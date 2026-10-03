import ConjugacyDiametersPORC.Basic

/-!
# Theorem 1: eventual affine PORC of conjugacy-class diameters

This file records the proof target only. The explicit `sorry` is intentional;
a successful build checks the statement's types, not the truth of the theorem.
-/

namespace ConjugacyDiametersPORC

/-- **Theorem 1.** For every fixed nontrivial cycle type `λ`, the diameters `D_n`
are eventually affine PORC with a common positive slope.

Unfolding `EventuallyAffinePORC` gives positive `P`, `q`, and `N` with
`D lam (n + P) = D lam n + q` for all `n ≥ N` (viewed in `ℤ`). The type `λ` is
chosen before these witnesses, so they may depend on `λ` but not on `n`.
-/
theorem diameter_eventuallyAffinePORC (lam : CycleType) :
    EventuallyAffinePORC (fun n => (D lam n : ℤ)) := by
  sorry

end ConjugacyDiametersPORC
