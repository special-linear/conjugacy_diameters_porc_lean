import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Fixed nontrivial cycle types

Cycle types record the nontrivial cycle lengths of a generating permutation.
Fixed points are omitted from the multiset, as in `Equiv.Perm.cycleType`.
-/

namespace ConjugacyDiametersPORC

/-- A nonempty multiset of cycle lengths, each at least two.

The ambient degree is not part of this data: a single `λ` is fixed while `n` varies.
Cycle lengths are natural numbers subject to `λᵢ ≥ 2`.
-/
structure CycleType where
  /-- The multiset `λ` of nontrivial cycle lengths. -/
  parts : Multiset ℕ
  /-- The identity cycle type is excluded. -/
  nonempty : parts ≠ 0
  /-- Fixed points and zero lengths are excluded. -/
  two_le : ∀ ℓ ∈ parts, 2 ≤ ℓ

namespace CycleType

/-- `m_ℓ`, the multiplicity of the length `ℓ` in `λ`. -/
def m (lam : CycleType) (ℓ : ℕ) : ℕ := lam.parts.count ℓ

/-- `J`, the finite set of nontrivial cycle lengths occurring in `λ`. -/
def J (lam : CycleType) : Finset ℕ := lam.parts.toFinset

/-- `b`, the support size of a generator. -/
def b (lam : CycleType) : ℕ := lam.parts.sum

/-- `h`, the number of nontrivial cycles in a generator. -/
def h (lam : CycleType) : ℕ := lam.parts.card

/-- `d = b - h`, the transposition length of a generator.

The conditions on `parts` ensure that this natural subtraction does not truncate.
The corresponding identities and positivity will be proved in the foundational API.
-/
def d (lam : CycleType) : ℕ := lam.b - lam.h

end CycleType

end ConjugacyDiametersPORC
