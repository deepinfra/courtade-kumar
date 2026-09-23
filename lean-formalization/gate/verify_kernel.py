#!/usr/bin/env python3
"""Run Lean, audit actual axiom output, and distinguish partial from full CK.

This is orchestration, NOT a theorem prover or a security sandbox. No solver
output, static scan, archived log, or mocked process is accepted as a Lean build.
The supplied sources are still uncompiled. Full mode is expected to fail until
an unconditional CK.courtadeKumar_proved is implemented.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
ALLOW = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
PINNED_LEAN = '4.19.0'

class AuditError(RuntimeError):
    pass


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def uncomment(src: str) -> str:
    """Discard nested Lean comments; leave strings intact. Static hygiene only."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(src):
        if depth:
            if src.startswith('/-', i): depth += 1; i += 2
            elif src.startswith('-/', i): depth -= 1; i += 2
            else:
                out.append('\n' if src[i] == '\n' else ' '); i += 1
        elif quoted:
            out.append(src[i])
            if src[i] == '\\' and i + 1 < len(src):
                i += 1; out.append(src[i])
            elif src[i] == '"': quoted = False
            i += 1
        elif src.startswith('/-', i): depth = 1; i += 2
        elif src.startswith('--', i):
            end = src.find('\n', i)
            i = len(src) if end == -1 else end
        else:
            out.append(src[i])
            if src[i] == '"': quoted = True
            i += 1
    if depth or quoted:
        raise AuditError('Unterminated comment or string: requires source inspection')
    return ''.join(out)


def check_hygiene(project: Path) -> list[str]:
    files = [project / 'CK.lean', project / 'CKF2.lean']
    files += sorted((project / 'CK').rglob('*.lean'))
    files += sorted((project / 'CKF2').rglob('*.lean'))
    bad = re.compile(r'\b(sorry|admit|axiom|native_decide|ofReduceBool)\b|debug\.skipKernelTC')
    for p in files:
        if not p.is_file(): raise AuditError(f'Missing source: {p}')
        if bad.search(uncomment(p.read_text())):
            raise AuditError(f'Prohibited local proof shortcut found: {p}')
    return [str(p.relative_to(project)) for p in files]


def parse_axioms(text: str, expected: list[str]) -> dict[str, list[str]]:
    """Fail closed on absent, duplicate, extra, or nonallowlisted axiom records."""
    if re.search(r'(^|\s)(error|warning):', text, re.I):
        raise AuditError('Lean printed an error or warning during the axiom audit')
    found: dict[str, list[str]] = {}
    pat = re.compile(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.S)
    for m in pat.finditer(text):
        name = m.group(1)
        if name in found: raise AuditError(f'Duplicate axiom report: {name}')
        axes = [] if m.group(2) is None else [x.strip() for x in m.group(2).split(',') if x.strip()]
        extras = set(axes) - ALLOW
        if extras: raise AuditError(f'Unapproved axiom dependencies for {name}: {sorted(extras)}')
        found[name] = axes
    if set(found) != set(expected):
        raise AuditError(f'Axiom-report mismatch: missing={sorted(set(expected)-set(found))}, extra={sorted(set(found)-set(expected))}')
    return found


def command(cmd: list[str], project: Path, out: Path, phase: str, timeout: int) -> str:
    started = time.monotonic()
    try:
        proc = subprocess.run(cmd, cwd=project, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=timeout, check=False)
    except subprocess.TimeoutExpired as exc:
        raw = exc.stdout or ''
        text = raw.decode(errors='replace') if isinstance(raw, bytes) else raw
        (out / f'{phase}.log').write_text(text)
        (out / f'{phase}.json').write_text(json.dumps({'command': cmd, 'status': 'TIMEOUT', 'seconds': timeout}, indent=2)+'\n')
        raise AuditError(f'{phase}: timeout (not success)') from exc
    text = proc.stdout
    (out / f'{phase}.log').write_text(text)
    (out / f'{phase}.json').write_text(json.dumps({'command': cmd, 'returncode': proc.returncode,
        'seconds': round(time.monotonic()-started, 3)}, indent=2)+'\n')
    if proc.returncode != 0:
        raise AuditError(f'{phase}: nonzero exit {proc.returncode}; inspect {phase}.log')
    if re.search(r'(^|\s)(error|warning):', text, re.I):
        raise AuditError(f'{phase}: warning/error output must be resolved; not accepted')
    return text


def run(mode: str, dest: Path, timeout: int) -> dict:
    dest = dest.resolve()
    dest.mkdir(parents=True, exist_ok=False)
    project = ROOT / 'lean'
    result = {'mode': mode, 'status': 'STARTED', 'lean_executed': False,
        'compiled_declarations': [], 'full_ck_target_accepted': False,
        'independent_kernel_replay': 'NOT_RUN', 'manuscript_changed': False,
        'note': 'This result describes the actual run, not source-draft intentions.'}
    try:
        # Pin the separately spelled-out target and the no-extra-premise gate.
        trusted = json.loads((ROOT/'TRUSTED_INPUT_HASHES.json').read_text())
        for rel, digest in trusted.items():
            if sha(ROOT/rel) != digest:
                raise AuditError(f'Trusted challenge input changed: {rel}')
        audited = check_hygiene(project)
        result['static_hygiene_only'] = audited
        result['source_hashes'] = {str(p.relative_to(project)):sha(p) for p in project.rglob('*.lean') if '.lake' not in p.parts}
        if shutil.which('lake') is None:
            result['status'] = 'BLOCKED_NO_LAKE'
            raise AuditError('Lake is unavailable. No Lean source was compiled and no CK proof was verified.')
        ver = command(['lake','env','lean','--version'],project,dest,'lean_version',min(timeout,120))
        result['lean_executed'] = True
        if not re.search(r'\bversion\s+'+re.escape(PINNED_LEAN)+r'\b',ver):
            raise AuditError(f'Toolchain differs from inherited F1 pin {PINNED_LEAN}; review compatibility explicitly')
        command(['lake','build','CK','CKF2'],project,dest,'build',timeout)
        names = json.loads((ROOT/'DECLARATIONS.json').read_text())
        audit = project/'F2AxiomAudit.lean'
        audit.write_text('import CK\nimport CKF2.Spec\n\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
        text = command(['lake','env','lean',audit.name],project,dest,'axioms',timeout)
        result['axioms'] = parse_axioms(text,names)
        result['compiled_declarations'] = names
        result['status'] = 'PARTIAL_MODULE_BUILD_AND_AXIOM_AUDIT_PASSED'
        if mode == 'full':
            gate = project/'F2CompletionGate.lean'
            gate.write_bytes((ROOT/'CompletionGate.lean.template').read_bytes())
            olean = project/'.lake/build/lib/lean/F2CompletionGate.olean'
            olean.parent.mkdir(parents=True, exist_ok=True)
            text = command(['lake','env','lean','-o',str(olean),gate.name],project,dest,'full_ck_gate',timeout)
            result['full_target_axioms'] = parse_axioms(text,['CKF2.exactTargetAccepted'])
            if not olean.is_file(): raise AuditError('Full target compiled without the requested proof artifact')
            result['full_ck_target_accepted'] = True
            result['proof_artifact_sha256'] = sha(olean)
            result['status'] = 'EXACT_CK_TARGET_ACCEPTED_BY_LEAN_AXIOMS_AUDITED'
        manifest = project/'lake-manifest.json'
        if manifest.exists():
            shutil.copyfile(manifest,dest/'lake-manifest.json')
            result['lake_manifest_sha256'] = sha(manifest)
    except (AuditError, OSError, ValueError) as exc:
        result['failure'] = str(exc)
        if result['status'] != 'BLOCKED_NO_LAKE': result['status'] = 'FAILED_NOT_ACCEPTED'
        result['full_ck_target_accepted'] = False
    finally:
        (dest/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode',choices=['partial','full'],default='partial')
    parser.add_argument('--output',type=Path,required=True,help='New directory; archived results are never reused')
    parser.add_argument('--timeout',type=int,default=1800)
    args = parser.parse_args()
    if args.timeout <= 0: parser.error('--timeout must be positive')
    try: result = run(args.mode,args.output,args.timeout)
    except FileExistsError:
        parser.error('Output directory already exists; choose a fresh directory')
    print(json.dumps(result,indent=2))
    return 0 if result['status'] in {'PARTIAL_MODULE_BUILD_AND_AXIOM_AUDIT_PASSED','EXACT_CK_TARGET_ACCEPTED_BY_LEAN_AXIOMS_AUDITED'} else 2

if __name__ == '__main__':
    sys.exit(main())
