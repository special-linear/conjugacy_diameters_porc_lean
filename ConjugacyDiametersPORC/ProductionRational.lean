import ConjugacyDiametersPORC.ProductionOptimum
import ConjugacyDiametersPORC.FinitePerturbation
import ConjugacyDiametersPORC.RationalLinearSystem
import Mathlib.Analysis.Convex.KreinMilman

/-!
# Rational attainment of the production rate

Choose an extreme point of the compact optimizer set. The resource equations
and its zero-coordinate equations form an injective rational system, since
otherwise two feasible perturbations would contradict extremality.
-/

namespace ConjugacyDiametersPORC

def ProductionOptimizers (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    Set (DictionaryEntry lam r hr → ℝ) :=
  {x | ProductionFeasible lam r hr x ∧ production lam r hr x = Γ lam r hr}

theorem productionOptimizers_isCompact (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    IsCompact (ProductionOptimizers lam r hr) :=
  (productionFeasible_isCompact lam r hr).inter_right
    (isClosed_eq (continuous_production lam r hr) continuous_const)

theorem exists_extreme_optimizer (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    ∃ x, x ∈ (ProductionOptimizers lam r hr).extremePoints ℝ := by
  obtain ⟨x, hx, he⟩ := exists_production_maximum lam r hr
  exact (productionOptimizers_isCompact lam r hr).extremePoints_nonempty ⟨x, hx, he⟩

theorem production_add_direction {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (x v : DictionaryEntry lam r hr → ℝ) (t : ℝ) :
    production lam r hr (x + t • v) =
      production lam r hr x + t * production lam r hr v := by
  simp only [production, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  ring

theorem feasible_add_direction {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (x v : DictionaryEntry lam r hr → ℝ) (hx : ProductionFeasible lam r hr x)
    (hv : ∀ ℓ : lam.J, ∑ A, (A.val.c ℓ : ℝ) * v A = 0) (t : ℝ)
    (hpos : ∀ A, 0 ≤ x A + t * v A) : ProductionFeasible lam r hr (x + t • v) := by
  refine ⟨hpos, fun ℓ => ?_⟩
  change (∑ A, (A.val.c ℓ : ℝ) * (x A + t * v A)) = _
  calc
    _ = (∑ A, (A.val.c ℓ : ℝ) * x A) + t * ∑ A, (A.val.c ℓ : ℝ) * v A := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ = _ := by rw [hx.2 ℓ, hv ℓ]; ring

theorem extreme_optimizer_direction_zero {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (x : DictionaryEntry lam r hr → ℝ)
    (hx : x ∈ (ProductionOptimizers lam r hr).extremePoints ℝ)
    (v : DictionaryEntry lam r hr → ℝ)
    (hv0 : ∀ A, x A = 0 → v A = 0)
    (hvc : ∀ ℓ : lam.J, ∑ A, (A.val.c ℓ : ℝ) * v A = 0) : v = 0 := by
  have hxF := hx.1.1
  have hxG := hx.1.2
  obtain ⟨ε, hε, hbound⟩ := exists_two_sided_perturbation x v hxF.1 hv0
  have hplus : ProductionFeasible lam r hr (x + ε • v) := by
    apply feasible_add_direction x v hxF hvc ε
    intro A
    have hab := neg_abs_le (v A)
    have hb := hbound A
    nlinarith
  have hminus : ProductionFeasible lam r hr (x - ε • v) := by
    have hf : ProductionFeasible lam r hr (x + (-ε) • v) := by
      apply feasible_add_direction x v hxF hvc (-ε)
      intro A
      have hab := le_abs_self (v A)
      have hb := hbound A
      nlinarith
    simpa only [neg_smul, sub_eq_add_neg] using hf
  have hp := production_le_Gamma lam r hr (x + ε • v) hplus
  have hm := production_le_Gamma lam r hr (x - ε • v) hminus
  rw [production_add_direction, hxG] at hp
  have heminus : production lam r hr (x - ε • v) =
      production lam r hr x - ε * production lam r hr v := by
    simpa only [neg_smul, sub_eq_add_neg, neg_mul] using production_add_direction x v (-ε)
  rw [heminus, hxG] at hm
  have hvp : production lam r hr v = 0 := by nlinarith
  have hyp : x + ε • v ∈ ProductionOptimizers lam r hr := by
    refine ⟨hplus, ?_⟩
    rw [production_add_direction, hvp, hxG, mul_zero, add_zero]
  have hym : x - ε • v ∈ ProductionOptimizers lam r hr := by
    refine ⟨hminus, ?_⟩
    rw [heminus, hvp, hxG, mul_zero, sub_zero]
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have he := hx.2 hyp hym (mem_openSegment_add_sub x (ε • v))
  funext A
  have ha := congrFun he A
  change x A + ε * v A = x A at ha
  change v A = 0
  nlinarith

open scoped Classical in
/-- Resource equations augmented by equations for the optimizer's zero coordinates. -/
noncomputable def optimizerMatrix {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (x : DictionaryEntry lam r hr → ℝ) :
    Matrix (lam.J ⊕ DictionaryEntry lam r hr) (DictionaryEntry lam r hr) ℚ
  | Sum.inl ℓ, A => A.val.c ℓ
  | Sum.inr B, A => if x B = 0 ∧ A = B then 1 else 0

def optimizerRightHandSide (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    lam.J ⊕ DictionaryEntry lam r hr → ℚ
  | Sum.inl ℓ => lam.m ℓ
  | Sum.inr _ => 0

theorem optimizerMatrix_solution {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (x : DictionaryEntry lam r hr → ℝ) (hx : ProductionFeasible lam r hr x) :
    ((optimizerMatrix x).map (Rat.castHom ℝ)).mulVec x =
      fun i => (optimizerRightHandSide lam r hr i : ℝ) := by
  classical
  funext i
  cases i with
  | inl ℓ => simpa [optimizerMatrix, optimizerRightHandSide, Matrix.mulVec, dotProduct] using hx.2 ℓ
  | inr B =>
    by_cases hB : x B = 0 <;>
      simp [optimizerMatrix, optimizerRightHandSide, Matrix.mulVec, dotProduct, hB,
        apply_ite, ite_mul]

theorem optimizerMatrix_injective {lam : CycleType} {r : ℕ} {hr : 2 ≤ r}
    (x : DictionaryEntry lam r hr → ℝ)
    (hx : x ∈ (ProductionOptimizers lam r hr).extremePoints ℝ) :
    Function.Injective ((optimizerMatrix x).map (Rat.castHom ℝ)).mulVec := by
  classical
  suffices hker : ∀ v, ((optimizerMatrix x).map (Rat.castHom ℝ)).mulVec v = 0 → v = 0 by
    intro u v huv
    have hz : ((optimizerMatrix x).map (Rat.castHom ℝ)).mulVec (u - v) = 0 := by
      rw [Matrix.mulVec_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) hz)
  intro v hv
  apply extreme_optimizer_direction_zero x hx v
  · intro B hB
    have h := congrFun hv (Sum.inr B)
    simpa [optimizerMatrix, Matrix.mulVec, dotProduct, hB, apply_ite, ite_mul] using h
  · intro ℓ
    have h := congrFun hv (Sum.inl ℓ)
    simpa [optimizerMatrix, Matrix.mulVec, dotProduct] using h

/-- **Remark 1.** The real maximum has a nonnegative rational optimizer. -/
theorem exists_rational_optimizer (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    ∃ y : DictionaryEntry lam r hr → ℚ,
      ProductionFeasible lam r hr (fun A => (y A : ℝ)) ∧
        production lam r hr (fun A => (y A : ℝ)) = Γ lam r hr := by
  obtain ⟨x, hx⟩ := exists_extreme_optimizer lam r hr
  obtain ⟨y, hy⟩ := rational_solution_of_injective (optimizerMatrix x)
    (optimizerRightHandSide lam r hr) x (optimizerMatrix_injective x hx)
      (optimizerMatrix_solution x hx.1.1)
  exact ⟨y, hy ▸ hx.1.1, hy ▸ hx.1.2⟩

theorem Gamma_rational (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    ∃ γ : ℚ, (γ : ℝ) = Γ lam r hr := by
  obtain ⟨y, _, he⟩ := exists_rational_optimizer lam r hr
  refine ⟨∑ A, (A.val.s : ℚ) * y A, ?_⟩
  simpa [production] using he

end ConjugacyDiametersPORC
