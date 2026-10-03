import ConjugacyDiametersPORC.RationalLinearSystem
import ConjugacyDiametersPORC.FinitePerturbation
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Topology.Order.Compact

/-! # Rational optimizers for compact finite rational programs -/

namespace ConjugacyDiametersPORC.RationalProgram

variable {ι κ : Type*} [Fintype ι]

def Feasible (M : Matrix κ ι ℚ) (b : κ → ℚ) (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∀ k, ∑ i, (M k i : ℝ) * x i = (b k : ℝ)

noncomputable def objective (c : ι → ℚ) (x : ι → ℝ) : ℝ := ∑ i, (c i : ℝ) * x i

theorem feasible_isClosed (M : Matrix κ ι ℚ) (b : κ → ℚ) :
    IsClosed {x | Feasible M b x} := by
  change IsClosed ({x : ι → ℝ | ∀ i, 0 ≤ x i} ∩
    {x | ∀ k, ∑ i, (M k i : ℝ) * x i = (b k : ℝ)})
  apply IsClosed.inter
  · rw [← Set.iInter_ofPred]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  · rw [← Set.iInter_ofPred]
    exact isClosed_iInter (fun k => isClosed_eq (continuous_finsetSum _
      (fun i _ => continuous_const.mul (continuous_apply i))) continuous_const)

theorem continuous_objective (c : ι → ℚ) : Continuous (objective c) :=
  continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))

theorem objective_add (c : ι → ℚ) (x v : ι → ℝ) (t : ℝ) :
    objective c (x + t • v) = objective c x + t * objective c v := by
  simp only [objective, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem feasible_add (M : Matrix κ ι ℚ) (b : κ → ℚ) (x v : ι → ℝ)
    (hx : Feasible M b x) (hv : ∀ k, ∑ i, (M k i : ℝ) * v i = 0)
    (t : ℝ) (hp : ∀ i, 0 ≤ x i + t * v i) : Feasible M b (x + t • v) := by
  refine ⟨hp, fun k => ?_⟩
  change (∑ i, (M k i : ℝ) * (x i + t * v i)) = _
  calc
    _ = (∑ i, (M k i : ℝ) * x i) + t * ∑ i, (M k i : ℝ) * v i := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hx.2 k, hv k]; ring

def Optimizers (M : Matrix κ ι ℚ) (b : κ → ℚ) (c : ι → ℚ) (z : ι → ℝ) : Set (ι → ℝ) :=
  {x | Feasible M b x ∧ objective c x = objective c z}

theorem direction_zero (M : Matrix κ ι ℚ) (b : κ → ℚ) (c : ι → ℚ) (z x : ι → ℝ)
    (hmax : ∀ y, Feasible M b y → objective c y ≤ objective c z)
    (hx : x ∈ (Optimizers M b c z).extremePoints ℝ) (v : ι → ℝ)
    (hv0 : ∀ i, x i = 0 → v i = 0)
    (hvM : ∀ k, ∑ i, (M k i : ℝ) * v i = 0) : v = 0 := by
  obtain ⟨ε, hε, hbound⟩ := exists_two_sided_perturbation x v hx.1.1.1 hv0
  have hp : Feasible M b (x + ε • v) := by
    apply feasible_add M b x v hx.1.1 hvM ε
    intro i
    have := neg_abs_le (v i)
    have := hbound i
    nlinarith
  have hm : Feasible M b (x - ε • v) := by
    have h := feasible_add M b x v hx.1.1 hvM (-ε) (by
      intro i
      have := le_abs_self (v i)
      have := hbound i
      nlinarith)
    simpa only [neg_smul, sub_eq_add_neg] using h
  have hpmax := hmax _ hp
  have hmmax := hmax _ hm
  have heminus : objective c (x - ε • v) = objective c x - ε * objective c v := by
    simpa only [neg_smul, sub_eq_add_neg, neg_mul] using objective_add c x v (-ε)
  rw [objective_add, hx.1.2] at hpmax
  rw [heminus, hx.1.2] at hmmax
  have hz : objective c v = 0 := by nlinarith
  have hyp : x + ε • v ∈ Optimizers M b c z := by
    refine ⟨hp, ?_⟩
    rw [objective_add, hz, hx.1.2, mul_zero, add_zero]
  have hym : x - ε • v ∈ Optimizers M b c z := by
    refine ⟨hm, ?_⟩
    rw [heminus, hz, hx.1.2, mul_zero, sub_zero]
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have he := hx.2 hyp hym (mem_openSegment_add_sub x (ε • v))
  funext i
  have hi := congrFun he i
  change x i + ε * v i = x i at hi
  change v i = 0
  nlinarith

open scoped Classical in
noncomputable def augmented (M : Matrix κ ι ℚ) (x : ι → ℝ) : Matrix (κ ⊕ ι) ι ℚ
  | Sum.inl k, i => M k i
  | Sum.inr j, i => if x j = 0 ∧ i = j then 1 else 0

def augmentedRhs (b : κ → ℚ) : κ ⊕ ι → ℚ
  | Sum.inl k => b k
  | Sum.inr _ => 0

theorem exists_rational_maximum (M : Matrix κ ι ℚ) (b : κ → ℚ) (c : ι → ℚ)
    [Finite κ]
    (hcompact : IsCompact {x | Feasible M b x}) (hne : ∃ x, Feasible M b x) :
    ∃ y : ι → ℚ, Feasible M b (fun i => (y i : ℝ)) ∧
      ∀ x, Feasible M b x → objective c x ≤ objective c (fun i => (y i : ℝ)) := by
  classical
  let _ := Fintype.ofFinite κ
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn hne (continuous_objective c).continuousOn
  have hc : IsCompact (Optimizers M b c z) := hcompact.inter_right
    (isClosed_eq (continuous_objective c) continuous_const)
  obtain ⟨x, hx⟩ := hc.extremePoints_nonempty (by exact ⟨z, hz, rfl⟩)
  have hsol : ((augmented M x).map (Rat.castHom ℝ)).mulVec x =
      fun k => (augmentedRhs b k : ℝ) := by
    funext k
    cases k with
    | inl k => simpa [augmented, augmentedRhs, Matrix.mulVec, dotProduct] using hx.1.1.2 k
    | inr i =>
      by_cases hi : x i = 0 <;>
        simp [augmented, augmentedRhs, Matrix.mulVec, dotProduct, hi, apply_ite, ite_mul]
  have hinj : Function.Injective ((augmented M x).map (Rat.castHom ℝ)).mulVec := by
    suffices hker : ∀ v, ((augmented M x).map (Rat.castHom ℝ)).mulVec v = 0 → v = 0 by
      intro u v huv
      exact sub_eq_zero.mp (hker (u - v) (by rw [Matrix.mulVec_sub, huv, sub_self]))
    intro v hv
    apply direction_zero M b c z x (fun y hy => hmax hy) hx v
    · intro i hi
      have h := congrFun hv (Sum.inr i)
      simpa [augmented, Matrix.mulVec, dotProduct, hi, apply_ite, ite_mul] using h
    · intro k
      have h := congrFun hv (Sum.inl k)
      simpa [augmented, Matrix.mulVec, dotProduct] using h
  obtain ⟨y, hy⟩ := rational_solution_of_injective (augmented M x) (augmentedRhs b) x hinj hsol
  refine ⟨y, hy ▸ hx.1.1, ?_⟩
  intro w hw
  rw [← hy, hx.1.2]
  exact hmax hw

end ConjugacyDiametersPORC.RationalProgram
