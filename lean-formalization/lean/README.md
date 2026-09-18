# Lean project — kernel-checked (session 8, 18 Sept 2026)

Build: `lake exe cache get && lake build CK CKF2` (Lean 4.19.0, mathlib pinned in `lake-manifest.json`).

- `CK/Definitions.lean` — finite Bool cube, exact BSC kernel, entropy and information definitions, the target
  proposition `CK.CourtadeKumar`, and the assembly `assemble_conditional`. Trusted input; hash-pinned by the gate.
- `CKF2/Spec.lean` — independently spelled-out target `CKF2.Spec.Target` with `matches_f1_target : Target = CK.CourtadeKumar := rfl`. Trusted input.
- `CK/AnalyticTargets.lean` — goal statements (curvature, product centering, log enclosure, entropy comparison, strict anchor).
- Proof modules, in dependency order: Algebra, Induction, Semantics, Sections, Relabel, SmallGap, AvgLemmas,
  ProfileInduction, EntropyBounds, Pinsker, LogEnclosure, Constants, EtaDeriv, Curvature, ProductCentering,
  Transfer, GainBounds, KappaSeries, Bridge, InteriorEstimate, EndpointCommon, Anchor, Comparison, Fourier,
  SignSum, EndpointSmall, EndpointLarge, LargeCoordScalar, Deficit, NoiseOperator, FourierCap, ScalarMixing,
  InfoContraction, LargeBias, LargeCoordinate, MiddleHigh, Complementary.
- `CK/Complementary.lean` ends with `theorem courtadeKumar_proved : CourtadeKumar`.
- `F2CompletionGate.lean` — the gate's frozen challenge (`CKF2.exactTargetAccepted : CKF2.Spec.Target`), as compiled.
- `ExtendedAxiomAudit.lean` — `#print axioms` for every declaration; log in `../verification/extended_axioms.log`.

No `sorry`, `admit`, custom `axiom`, `native_decide` or kernel bypass anywhere; every declaration depends only on
`propext`, `Classical.choice`, `Quot.sound` (or fewer).
