import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Clearing finitely many nonnegative rational denominators
-/

namespace ConjugacyDiametersPORC

theorem exists_nat_multiple {ι : Type*} [Finite ι] (y : ι → ℚ) (hy : ∀ i, 0 ≤ y i) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ z : ι → ℕ, ∀ i, (z i : ℚ) = Q * y i := by
  classical
  let _ := Fintype.ofFinite ι
  let Q := ∏ i, (y i).den
  have hQ : 0 < Q := Finset.prod_pos (fun i _ => (y i).den_pos)
  have hdiv (i : ι) : (y i).den ∣ Q :=
    Finset.dvd_prod_of_mem (fun j => (y j).den) (Finset.mem_univ i)
  choose k hk using hdiv
  refine ⟨Q, hQ, fun i => (y i).num.toNat * k i, ?_⟩
  intro i
  have hnum : ((y i).num.toNat : ℚ) = (y i).num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hy i))
  have hd : ((y i).den : ℚ) ≠ 0 := by exact_mod_cast (y i).den_ne_zero
  have he : ((y i).num : ℚ) = y i * (y i).den :=
    (div_eq_iff hd).mp (y i).num_div_den
  rw [Nat.cast_mul, hnum, hk i, Nat.cast_mul, he]
  ring

end ConjugacyDiametersPORC
