# Formalization contract

Target the manuscript pinned in `paper-manifest.json`. The November 20
progressive-entropy theorem is stronger than the classical Courtade–Kumar bound.
Keep these claims separate, including when reusing the earlier Fourier proof.

`CK/Spec.lean` spells out the target independently of proof modules. Do not weaken
its hypotheses, conclusion, domain, definitions, or entropy normalization to make
a proof pass. Any mathematically necessary specification correction must be
documented explicitly, with its manuscript correspondence and updated hash.

Only a fresh Lean build and transitive axiom audit count as checked progress.
No placeholders, new proof axioms, untrusted decision procedures, or declarations
that assert the desired result as a premise are allowed in the proved library.
Conditional lemmas are useful, but their unproved analytic hypotheses must be
listed in the obligation ledger. Never report them as a completed main theorem.

Keep source, machine-readable obligations, statement correspondence, and actual
verification logs together. A successful partial build is not a complete proof.
The full gate must require an inhabiting term of `Spec.LatestPaperTarget` and
reject undeclared axioms. Conjectures in the paper are not proof obligations.

Preserve the manuscript and slides. Add formalization changes on the working
branch; do not merge into `main` as part of the formalization work.
