#!/usr/bin/env python3
"""Build and audit actual Lean terms; distinguish partial progress from completion."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
FORBIDDEN = {
    "sorry", "admit", "axiom", "unsafe", "native_decide", "ofReduceBool",
    "skipKernelTC", "implemented_by", "extern",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(source: str) -> str:
    """Strip nested Lean block comments, line comments, and string literals.

    This is an additional hygiene screen. The transitive kernel axiom audit is
    authoritative; static scanning alone is never treated as verification.
    """
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if source[i] == "\n":
                    out.append("\n")
                i += 1
        elif in_string:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                in_string = False
                i += 1
            else:
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    if depth or in_string:
        raise ValueError("unterminated comment or string")
    return "".join(out)


def run(command: list[str], output: Path, timeout: int) -> dict:
    start = time.monotonic()
    try:
        with output.open("w") as log:
            proc = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                  timeout=timeout, check=False)
        result = {"command": command, "returncode": proc.returncode}
    except (OSError, subprocess.TimeoutExpired) as exc:
        with output.open("a") as log:
            log.write(f"\n{type(exc).__name__}: {exc}\n")
        result = {"command": command, "returncode": None, "error": str(exc)}
    result["seconds"] = round(time.monotonic() - start, 3)
    result["log"] = str(output.relative_to(ROOT))
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--mode", choices=["partial", "full"], default="full")
    parser.add_argument("--lake", default=os.environ.get("CK_LAKE", "lake"))
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--output", default="verification/latest")
    args = parser.parse_args()
    output = (ROOT / args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    result: dict = {
        "timestamp_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "mode": args.mode,
        "status": "NOT_VERIFIED",
        "latest_main_theorem_verified": False,
        "all_paper_results_verified": False,
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "steps": {},
    }
    report = output / "result.json"
    initial_snapshot: dict[str, str] | None = None
    paper_files: list[str] = []
    trusted_files: list[str] = []

    def source_files() -> list[Path]:
        return sorted((ROOT / "CK").rglob("*.lean")) + [ROOT / "CKLatest.lean"]

    def snapshot() -> dict[str, str]:
        files = set(source_files())
        files.update(ROOT / name for name in trusted_files)
        files.update(REPO / name for name in paper_files)
        files.update([ROOT / "paper-manifest.json", ROOT / "specification-manifest.json",
                      ROOT / "lake-manifest.json", Path(__file__).resolve()])
        return {str(path.relative_to(REPO)): sha256(path) for path in sorted(files)}

    def write_report() -> None:
        temporary = report.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(result, indent=2) + "\n")
        temporary.replace(report)

    def save(status: str, code: int) -> int:
        if initial_snapshot is not None:
            try:
                final_snapshot = snapshot()
                result["input_hashes_after"] = final_snapshot
                changed = sorted(name for name in set(initial_snapshot) | set(final_snapshot)
                                 if initial_snapshot.get(name) != final_snapshot.get(name))
                result["inputs_changed_during_run"] = changed
                if changed:
                    status, code = "INPUT_CHANGED_DURING_RUN", 1
                    result["latest_main_theorem_verified"] = False
            except (OSError, ValueError) as exc:
                result["final_snapshot_error"] = str(exc)
                status, code = "INPUT_CHANGED_DURING_RUN", 1
                result["latest_main_theorem_verified"] = False
        result["status"] = status
        write_report()
        print(json.dumps({"status": status, "report": str(report),
                          "latest_main_theorem_verified": result["latest_main_theorem_verified"],
                          "all_paper_results_verified": result["all_paper_results_verified"]}))
        return code

    # Invalidate any earlier result immediately, even if parsing an input fails.
    result["status"] = "RUNNING_NOT_VERIFIED"
    write_report()
    paper = json.loads((ROOT / "paper-manifest.json").read_text())
    paper_files = [entry["path"] for entry in paper["files"]]
    mismatches = [entry["path"] for entry in paper["files"]
                  if sha256(REPO / entry["path"]) != entry["sha256"]]
    result["paper_commit"] = paper["repository_commit"]
    result["paper_hash_mismatches"] = mismatches
    spec = json.loads((ROOT / "specification-manifest.json").read_text())
    trusted_files = list(spec["sha256"])
    trusted_mismatches = [name for name, digest in spec["sha256"].items()
                          if sha256(ROOT / name) != digest]
    result["specification_hash_mismatches"] = trusted_mismatches
    if mismatches or trusted_mismatches:
        return save("INPUT_HASH_MISMATCH", 1)

    sources = source_files()
    initial_snapshot = snapshot()
    result["input_hashes_before"] = initial_snapshot
    violations = []
    for source in sources:
        code = code_only(source.read_text())
        tokens = set(re.findall(r"[A-Za-z_][A-Za-z_0-9']*", code))
        for token in sorted(tokens & FORBIDDEN):
            violations.append({"path": str(source.relative_to(ROOT)), "token": token})
    result["source_hashes"] = {str(p.relative_to(ROOT)): sha256(p) for p in sources}
    result["forbidden_tokens"] = violations
    if violations:
        return save("FORBIDDEN_PROOF_CONSTRUCT", 1)

    try:
        mathlib_rev = subprocess.check_output(
            ["git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD"],
            text=True, stderr=subprocess.STDOUT).strip()
    except subprocess.CalledProcessError as exc:
        result["mathlib_error"] = exc.output
        return save("MATHLIB_REVISION_UNAVAILABLE", 1)
    result["mathlib_commit"] = mathlib_rev
    if mathlib_rev != paper["mathlib_commit"]:
        return save("MATHLIB_REVISION_MISMATCH", 1)

    result["steps"]["lean_version"] = run(
        [args.lake, "env", "lean", "--version"], output / "lean-version.log", args.timeout)
    if result["steps"]["lean_version"]["returncode"] != 0:
        return save("LEAN_RUNTIME_FAILED", 1)
    if "Lean (version 4.19.0," not in (output / "lean-version.log").read_text():
        return save("LEAN_VERSION_MISMATCH", 1)

    result["steps"]["build"] = run(
        [args.lake, "build", "CKLatest"], output / "build.log", args.timeout)
    if result["steps"]["build"]["returncode"] != 0:
        return save("BUILD_FAILED", 1)

    result["steps"]["axioms"] = run(
        [args.lake, "env", "lean", "scripts/AxiomAudit.lean"], output / "axioms.log", args.timeout)
    if result["steps"]["axioms"]["returncode"] != 0:
        return save("AXIOM_AUDIT_FAILED", 1)
    audit_text = (output / "axioms.log").read_text()
    imported_modules = set(re.findall(r"CK_AUDITED_MODULE (\S+)", audit_text))
    expected_modules = {str(p.relative_to(ROOT).with_suffix("")).replace(os.sep, ".")
                        for p in sources}
    result["audited_modules"] = sorted(imported_modules)
    result["unaudited_source_modules"] = sorted(expected_modules - imported_modules)
    if expected_modules != imported_modules:
        return save("AXIOM_AUDIT_MODULE_COVERAGE_MISMATCH", 1)
    counts = re.findall(r"CK_AUDIT_THEOREMS (\d+)", audit_text)
    if len(counts) != 1 or int(counts[0]) == 0:
        return save("AXIOM_AUDIT_INCOMPLETE", 1)
    result["audited_theorem_count"] = int(counts[0])
    audited_names = re.findall(r"CK_THEOREM (\S+) TRANSITIVE_AXIOMS_SUBSET_OF", audit_text)
    if len(audited_names) != int(counts[0]) or len(set(audited_names)) != len(audited_names):
        return save("AXIOM_AUDIT_INCOMPLETE", 1)
    for marker, key in [("CK_AUDIT_DECLARATIONS", "audited_safe_declaration_count"),
                        ("CK_AUDIT_UNSAFE_COMPILER_ARTIFACTS", "excluded_unsafe_compiler_artifact_count")]:
        values = re.findall(rf"{marker} (\d+)", audit_text)
        if len(values) != 1:
            return save("AXIOM_AUDIT_INCOMPLETE", 1)
        result[key] = int(values[0])
    if audit_text.count("CK_AUDIT_TRANSITIVE_AXIOM_UNION") != 1:
        return save("AXIOM_AUDIT_INCOMPLETE", 1)

    # Always attempt the exact target, even during a partial progress run.
    result["steps"]["completion"] = run(
        [args.lake, "env", "lean", "scripts/CompletionGate.lean"],
        output / "completion.log", args.timeout)
    if result["steps"]["completion"]["returncode"] == 0:
        result["latest_main_theorem_verified"] = True
        return save("LATEST_MAIN_THEOREM_KERNEL_CHECKED", 0)
    return save("PARTIAL_KERNEL_CHECKED_FULL_TARGET_OPEN", 0 if args.mode == "partial" else 2)


if __name__ == "__main__":
    sys.exit(main())
