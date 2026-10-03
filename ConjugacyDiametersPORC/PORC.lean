import Mathlib.Data.Int.Basic

/-!
# Eventual affine PORC

An integer sequence is eventually affine PORC when a fixed positive shift of
the index eventually increases its value by a fixed positive amount.
-/

namespace ConjugacyDiametersPORC

/-- An integer sequence is eventually affine PORC with a common positive slope
if there are positive integers `P`, `q`, and `N` such that
`a (n + P) = a n + q` for every `n ≥ N`.

The witnesses are natural numbers with strict positivity conditions, equivalent
to positive integer witnesses. The common rational slope is `q / P`.
The equivalent formula using rational residue constants is future API, not an
additional assumption in this definition.
-/
def EventuallyAffinePORC (a : ℕ → ℤ) : Prop :=
  ∃ P q N : ℕ, 0 < P ∧ 0 < q ∧ 0 < N ∧
    ∀ n : ℕ, N ≤ n → a (n + P) = a n + (q : ℤ)

end ConjugacyDiametersPORC
