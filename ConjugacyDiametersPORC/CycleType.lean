import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Lean.Elab.Tactic.Omega

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
The inventory identities and positivity are established below.
-/
def d (lam : CycleType) : ℕ := lam.b - lam.h

@[simp]
theorem mem_J (lam : CycleType) (ℓ : ℕ) : ℓ ∈ lam.J ↔ ℓ ∈ lam.parts := by
  simp [J]

@[simp]
theorem m_pos_iff (lam : CycleType) (ℓ : ℕ) : 0 < lam.m ℓ ↔ ℓ ∈ lam.J := by
  simp [m, J, Multiset.count_pos]

theorem two_le_of_mem_J (lam : CycleType) {ℓ : ℕ} (hℓ : ℓ ∈ lam.J) : 2 ≤ ℓ :=
  lam.two_le ℓ ((lam.mem_J ℓ).mp hℓ)

theorem h_pos (lam : CycleType) : 0 < lam.h :=
  Multiset.card_pos.mpr lam.nonempty

theorem two_mul_h_le_b (lam : CycleType) : 2 * lam.h ≤ lam.b := by
  simpa [h, b, nsmul_eq_mul, mul_comm] using
    (Multiset.card_nsmul_le_sum lam.two_le)

theorem h_le_b (lam : CycleType) : lam.h ≤ lam.b := by
  have := lam.two_mul_h_le_b
  omega

theorem b_pos (lam : CycleType) : 0 < lam.b :=
  lt_of_lt_of_le lam.h_pos lam.h_le_b

theorem d_pos (lam : CycleType) : 0 < lam.d := by
  have := lam.h_pos
  have := lam.two_mul_h_le_b
  unfold d
  omega

theorem h_add_d (lam : CycleType) : lam.h + lam.d = lam.b := by
  exact Nat.add_sub_of_le lam.h_le_b

theorem h_eq_sum_m (lam : CycleType) : lam.h = ∑ ℓ ∈ lam.J, lam.m ℓ := by
  exact (Multiset.toFinset_sum_count_eq lam.parts).symm

theorem b_eq_sum_m (lam : CycleType) : lam.b = ∑ ℓ ∈ lam.J, ℓ * lam.m ℓ := by
  simpa [b, J, m, nsmul_eq_mul, mul_comm] using
    (Finset.sum_multiset_map_count lam.parts (fun ℓ => ℓ))

theorem d_eq_sum_m (lam : CycleType) :
    lam.d = ∑ ℓ ∈ lam.J, (ℓ - 1) * lam.m ℓ := by
  have hsum : lam.b = lam.h + ∑ ℓ ∈ lam.J, (ℓ - 1) * lam.m ℓ := by
    rw [lam.b_eq_sum_m, lam.h_eq_sum_m, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    have := lam.two_le_of_mem_J hℓ
    have hℓ' : ℓ = 1 + (ℓ - 1) := by omega
    calc
      ℓ * lam.m ℓ = (1 + (ℓ - 1)) * lam.m ℓ := congrArg (· * lam.m ℓ) hℓ'
      _ = lam.m ℓ + (ℓ - 1) * lam.m ℓ := by rw [add_mul, one_mul]
  unfold d
  omega

end CycleType

end ConjugacyDiametersPORC
