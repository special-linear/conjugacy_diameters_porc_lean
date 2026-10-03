import ConjugacyDiametersPORC.Basic
import ConjugacyDiametersPORC.UpperRecurrence
import ConjugacyDiametersPORC.LowerBound
import ConjugacyDiametersPORC.Stabilization
import ConjugacyDiametersPORC.UnionUpperRecurrence
import ConjugacyDiametersPORC.UnionLowerBound

/-!
# Theorem 1: eventual affine PORC of conjugacy-class diameters

The uniform lower bound and the matching eventual upper recurrence force each
integer residue-class defect to stabilize. The resulting common slope is `α_λ`.
-/

namespace ConjugacyDiametersPORC

/-- **Theorem 1 and Remark 3.** The eventual recurrence has common slope `α_λ`. -/
theorem diameter_eventual_recurrence_with_slope (lam : CycleType) :
    ∃ P q N : ℕ, 0 < P ∧ 0 < q ∧ 0 < N ∧
      (∀ n, N ≤ n → D lam (n + P) = D lam n + q) ∧
        (q : ℝ) / (P : ℝ) = α lam := by
  obtain ⟨P, q, N, hP, hq, _, hrate, hupper⟩ := exists_upper_recurrence lam
  obtain ⟨a, c, ha, _, _, hlower⟩ := exists_rational_lowerBound lam
  have hrateQ : a * (P : ℚ) = (q : ℚ) := by
    have he : (a : ℝ) * (P : ℝ) = (q : ℝ) := by rw [ha, hrate]
    exact_mod_cast he
  obtain ⟨N', hN', hrec⟩ := eventual_recurrence_of_bounds (D lam) P q
    (max N (lam.b + 1)) hP a c hrateQ
      (fun n hn => hupper n ((le_max_left _ _).trans hn))
      (fun n hn => hlower n ((le_max_right _ _).trans hn))
  refine ⟨P, q, N', hP, hq, hN', hrec, ?_⟩
  have hPR : (P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hP
  rw [hrate, mul_div_cancel_right₀ _ hPR]

/-- **Theorem 1.** For every fixed nontrivial cycle type `λ`, the diameters `D_n`
are eventually affine PORC with a common positive slope.

Unfolding `EventuallyAffinePORC` gives positive `P`, `q`, and `N` with
`D lam (n + P) = D lam n + q` for all `n ≥ N` (viewed in `ℤ`). The type `λ` is
chosen before these witnesses, so they may depend on `λ` but not on `n`.
-/
theorem diameter_eventuallyAffinePORC (lam : CycleType) :
    EventuallyAffinePORC (fun n => (D lam n : ℤ)) := by
  obtain ⟨P, q, N, hP, hq, hN, hrec, _⟩ := diameter_eventual_recurrence_with_slope lam
  refine ⟨P, q, N, hP, hq, hN, fun n hn => ?_⟩
  change (D lam (n + P) : ℤ) = (D lam n : ℤ) + (q : ℤ)
  exact_mod_cast hrec n hn

/-- The finite-union recurrence has the slope from the mixed inventory program. -/
theorem finiteUnion_diameter_eventual_recurrence_with_slope (F : CycleFamily) :
    ∃ P q N : ℕ, 0 < P ∧ 0 < q ∧ 0 < N ∧
      (∀ n, N ≤ n → FiniteUnion.D F (n + P) = FiniteUnion.D F n + q) ∧
        (q : ℝ) / (P : ℝ) = FiniteUnion.α F := by
  obtain ⟨P, q, N, hP, hq, _, hrate, hupper⟩ := FiniteUnion.exists_upper_recurrence F
  obtain ⟨a, c, ha, _, _, hlower⟩ := FiniteUnion.exists_rational_lowerBound F
  have hrateQ : a * (P : ℚ) = (q : ℚ) := by
    have he : (a : ℝ) * (P : ℝ) = (q : ℝ) := by rw [ha, hrate]
    exact_mod_cast he
  obtain ⟨N', hN', hrec⟩ := eventual_recurrence_of_bounds (FiniteUnion.D F) P q
    (max N (F.b + 1)) hP a c hrateQ
      (fun n hn => hupper n ((le_max_left _ _).trans hn))
      (fun n hn => hlower n ((le_max_right _ _).trans hn))
  refine ⟨P, q, N', hP, hq, hN', hrec, ?_⟩
  have hPR : (P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hP
  rw [hrate, mul_div_cancel_right₀ _ hPR]

/-- **Corollary (finite unions).** A fixed nonempty finite family of nontrivial
cycle types generates Cayley graphs whose diameters are eventually affine PORC.

`FiniteUnion.C F n` is the union of the full `S_n` conjugacy classes, and
`FiniteUnion.D F n` is the diameter of its generated subgroup with each generator
of every type costing one. The family is fixed independently of `n`.
-/
theorem finiteUnion_diameter_eventuallyAffinePORC (F : CycleFamily) :
    EventuallyAffinePORC (fun n => (FiniteUnion.D F n : ℤ)) := by
  obtain ⟨P, q, N, hP, hq, hN, hrec, _⟩ := finiteUnion_diameter_eventual_recurrence_with_slope F
  refine ⟨P, q, N, hP, hq, hN, fun n hn => ?_⟩
  change (FiniteUnion.D F (n + P) : ℤ) = (FiniteUnion.D F n : ℤ) + (q : ℤ)
  exact_mod_cast hrec n hn

end ConjugacyDiametersPORC
