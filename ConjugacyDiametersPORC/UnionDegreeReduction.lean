import ConjugacyDiametersPORC.UnionTransport

/-!
# Passing to a smaller degree after creating fixed labels

Realize the remaining cycle type in the smaller symmetric group. Generator
parity puts that realization in its generated subgroup once the smaller degree
is at least `b+1`. Embed and conjugate a shortest factorization back.
-/

namespace ConjugacyDiametersPORC
namespace FiniteUnion

open Equiv Equiv.Perm

theorem IsFactorization.mem_G {lam : CycleFamily} {n : ℕ}
    {g : SymmetricGroup n} {w : List (SymmetricGroup n)}
    (hw : IsFactorization lam g w) : g ∈ G lam n := by
  rw [← hw.2]
  apply (G lam n).list_prod_mem
  intro a ha
  exact Subgroup.subset_closure (hw.1 a ha)

theorem small_support_factorization (lam : CycleFamily) {n m : ℕ}
    (hm : lam.b + 1 ≤ m) (hmn : m ≤ n) (g : G lam n)
    (hs : (g : SymmetricGroup n).support.card ≤ m) :
    ∃ w : List (SymmetricGroup n), IsFactorization lam (g : SymmetricGroup n) w ∧
      w.length ≤ D lam m := by
  have hex : ∃ h : SymmetricGroup m, h.cycleType = (g : SymmetricGroup n).cycleType := by
    rw [exists_with_cycleType_iff]
    exact ⟨by simpa [sum_cycleType] using hs,
      by intro t ht; exact two_le_of_mem_cycleType ht⟩
  obtain ⟨h, ht⟩ := hex
  have hh : h ∈ G lam m := by
    classical
    by_cases hd : AllEven lam
    · rw [G_eq_alternatingGroup lam hm hd, mem_alternatingGroup, sign_of_cycleType, ht,
        ← sign_of_cycleType]
      exact mem_alternatingGroup.mp
        ((G_eq_alternatingGroup lam (hm.trans hmn) hd).le g.property)
    · rw [G_eq_symmetricGroup lam hm hd]
      trivial
  obtain ⟨l, hl, hlen⟩ := exists_shortest_factorization lam ⟨h, hh⟩
  let e : Fin m ↪ Fin n :=
    ⟨Fin.castLE hmn, fun _ _ he => Fin.ext (congrArg (fun x : Fin n => x.val) he)⟩
  obtain ⟨w, hw, hwlen⟩ := factorization_of_cycleType_eq (h := (g : SymmetricGroup n))
    (hl.viaEmbedding e) (by rw [viaEmbedding_cycleType, ht])
  refine ⟨w, hw, ?_⟩
  rw [hwlen, List.length_map, hlen]
  exact L_le_D lam ⟨h, hh⟩

/-- A bounded correction creating `P` fixed labels gives the desired length bound. -/
theorem length_le_of_correction (lam : CycleFamily) {n P q : ℕ}
    (hn : lam.b + 1 ≤ n - P) (g : G lam n)
    (f : SymmetricGroup n) (w : List (SymmetricGroup n))
    (hw : IsFactorization lam f w) (hlen : w.length ≤ q)
    (hs : ((g : SymmetricGroup n) * f⁻¹).support.card ≤ n - P) :
    L lam g ≤ D lam (n - P) + q := by
  have hrest : (g : SymmetricGroup n) * f⁻¹ ∈ G lam n :=
    (G lam n).mul_mem g.property ((G lam n).inv_mem hw.mem_G)
  obtain ⟨l, hl, hll⟩ := small_support_factorization lam hn (Nat.sub_le n P)
    ⟨(g : SymmetricGroup n) * f⁻¹, hrest⟩ hs
  have hprod : ((g : SymmetricGroup n) * f⁻¹) * f = g := by simp [mul_assoc]
  have hf := hl.append hw
  rw [hprod] at hf
  have he := L_le_length (g := g) hf
  rw [List.length_append] at he
  omega

end FiniteUnion
end ConjugacyDiametersPORC
