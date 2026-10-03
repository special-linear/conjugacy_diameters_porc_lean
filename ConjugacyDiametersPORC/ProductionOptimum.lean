import ConjugacyDiametersPORC.ProductionRate
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Attainment of the real production optimum

The feasible set is a closed subset of the finite box `0 ≤ x_A ≤ h`.
The continuous production objective therefore attains its supremum.
-/

namespace ConjugacyDiametersPORC

theorem continuous_production (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    Continuous (production lam r hr) := by
  unfold production
  exact continuous_finsetSum _ (fun A _ => continuous_const.mul (continuous_apply A))

theorem productionFeasible_isClosed (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    IsClosed {x : DictionaryEntry lam r hr → ℝ | ProductionFeasible lam r hr x} := by
  change IsClosed ({x : DictionaryEntry lam r hr → ℝ | ∀ A, 0 ≤ x A} ∩
    {x | ∀ ℓ : lam.J, ∑ A, (A.val.c ℓ : ℝ) * x A = lam.m ℓ})
  apply IsClosed.inter
  · rw [← Set.iInter_ofPred]
    apply isClosed_iInter
    intro A
    exact isClosed_le continuous_const (continuous_apply A)
  · rw [← Set.iInter_ofPred]
    apply isClosed_iInter
    intro ℓ
    exact isClosed_eq (continuous_finsetSum _
      (fun A _ => continuous_const.mul (continuous_apply A))) continuous_const

theorem productionFeasible_isCompact (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    IsCompact {x : DictionaryEntry lam r hr → ℝ | ProductionFeasible lam r hr x} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : DictionaryEntry lam r hr → ℝ)
    (fun _ => (lam.h : ℝ)))).of_isClosed_subset (productionFeasible_isClosed lam r hr)
  intro x hx
  constructor
  · exact hx.1
  · intro A
    exact (Finset.single_le_sum (fun B _ => hx.1 B) (Finset.mem_univ A)).trans
      (feasible_weight_bound lam r hr x hx)

theorem exists_production_maximum (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) :
    ∃ x : DictionaryEntry lam r hr → ℝ,
      ProductionFeasible lam r hr x ∧ production lam r hr x = Γ lam r hr := by
  obtain ⟨z, hz, _⟩ := exists_baseline_feasible lam r hr
  obtain ⟨x, hx, hmax⟩ := (productionFeasible_isCompact lam r hr).exists_isMaxOn
    ⟨z, hz⟩ (continuous_production lam r hr).continuousOn
  refine ⟨x, hx, le_antisymm (production_le_Gamma lam r hr x hx) ?_⟩
  apply csSup_le (productionValues_nonempty lam r hr)
  rintro t ⟨y, hy, rfl⟩
  exact hmax hy

end ConjugacyDiametersPORC
