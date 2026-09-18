import Lake
open Lake DSL

package ckFormalDraft

-- Compatibility pin for this UNCOMPILED draft, not an assertion that a build ran.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.19.0"

@[default_target]
lean_lib CK

-- F2 execution scaffolding; does not assert the CK theorem.
lean_lib CKF2
