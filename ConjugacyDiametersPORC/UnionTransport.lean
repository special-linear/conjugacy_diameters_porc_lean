import ConjugacyDiametersPORC.WordEmbedding
import ConjugacyDiametersPORC.UnionDiameter

/-!
# Transporting generator factorizations

Embedding into a larger degree and conjugating preserve the generating class
and the number of factors. Equal full cycle types therefore have equal costs
for any particular transported factorization.
-/

namespace ConjugacyDiametersPORC
namespace FiniteUnion

open Equiv Equiv.Perm

theorem IsFactorization.viaEmbedding {lam : CycleFamily} {n m : ℕ}
    {g : SymmetricGroup n} {w : List (SymmetricGroup n)}
    (hw : IsFactorization lam g w) (e : Fin n ↪ Fin m) :
    IsFactorization lam (g.viaEmbedding e) (w.map (viaEmbeddingHom e)) := by
  constructor
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, hj⟩ := hw.1 b hb
    refine ⟨j, ?_⟩
    rwa [ConjugacyDiametersPORC.mem_C, viaEmbeddingHom_apply, viaEmbedding_cycleType]
  · rw [← map_list_prod (viaEmbeddingHom e), hw.2]
    rfl

theorem IsFactorization.conjugate {lam : CycleFamily} {n : ℕ}
    {g : SymmetricGroup n} {w : List (SymmetricGroup n)}
    (hw : IsFactorization lam g w) (τ : SymmetricGroup n) :
    IsFactorization lam (τ * g * τ⁻¹) (w.map (MulAut.conj τ)) := by
  constructor
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, hj⟩ := hw.1 b hb
    exact ⟨j, ConjugacyDiametersPORC.conj_mem_C (lam.type j) hj τ⟩
  · calc
      _ = (MulAut.conj τ) w.prod := (map_list_prod (MulAut.conj τ).toMonoidHom w).symm
      _ = _ := by rw [hw.2]; rfl

theorem factorization_of_cycleType_eq {lam : CycleFamily} {n : ℕ}
    {g h : SymmetricGroup n} {w : List (SymmetricGroup n)}
    (hw : IsFactorization lam g w) (ht : g.cycleType = h.cycleType) :
    ∃ l, IsFactorization lam h l ∧ l.length = w.length := by
  obtain ⟨τ, hτ⟩ := isConj_iff.mp (isConj_of_cycleType_eq ht)
  exact ⟨w.map (MulAut.conj τ), hτ ▸ hw.conjugate τ, List.length_map _⟩

theorem factorization_prod_of_uniform_length (lam : CycleFamily) {n : ℕ}
    (l : List (SymmetricGroup n)) (t : ℕ)
    (h : ∀ g ∈ l, ∃ w, IsFactorization lam g w ∧ w.length = t) :
    ∃ w, IsFactorization lam l.prod w ∧ w.length = l.length * t := by
  induction l with
  | nil => exact ⟨[], isFactorization_nil lam n, by simp⟩
  | cons g l ih =>
    obtain ⟨v, hv, hvl⟩ := h g List.mem_cons_self
    obtain ⟨w, hw, hwl⟩ := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    exact ⟨v ++ w, hv.append hw, by simp [hvl, hwl, Nat.add_mul, Nat.add_comm]⟩

end FiniteUnion
end ConjugacyDiametersPORC
