import ConjugacyDiametersPORC.ConstituentWord
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Relabeling and disjoint unions of words

Embedding a word in a larger finite set retains its resource vector and target.
Disjoint unions add the resource vectors and target-cycle counts.
-/

namespace ConjugacyDiametersPORC

open Equiv Equiv.Perm

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem viaEmbedding_cycleType (g : Perm α) (e : α ↪ β) :
    (g.viaEmbedding e).cycleType = g.cycleType := by
  classical
  let _ : DecidablePred (fun x => x ∈ Set.range e.1) := fun _ => Classical.propDecidable _
  simpa only [viaEmbedding] using
    (cycleType_extendDomain (g := g) (Equiv.ofInjective e.1 e.2))

theorem viaEmbedding_support_card (g : Perm α) (e : α ↪ β) :
    (g.viaEmbedding e).support.card = g.support.card := by
  classical
  let _ : DecidablePred (fun x => x ∈ Set.range e.1) := fun _ => Classical.propDecidable _
  simpa only [viaEmbedding] using
    (card_support_extend_domain (g := g) (Equiv.ofInjective e.1 e.2))

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem viaEmbedding_isCycle (g : Perm α) (e : α ↪ β) (hg : g.IsCycle) :
    (g.viaEmbedding e).IsCycle := by
  classical
  exact hg.extendDomain (Equiv.ofInjective e.1 e.2)

omit [Fintype α] [DecidableEq α] in
theorem viaEmbedding_support_subset (g : Perm α) (e : α ↪ β) :
    (↑(g.viaEmbedding e).support : Set β) ⊆ Set.range e := by
  intro x hx
  by_contra hn
  exact (mem_support.mp hx) (viaEmbedding_apply_of_notMem g e x hn)

theorem viaEmbedding_mem_support (g : Perm α) (e : α ↪ β) (x : α) :
    e x ∈ (g.viaEmbedding e).support ↔ x ∈ g.support := by
  simp only [mem_support, viaEmbedding_apply, ne_eq, e.injective.eq_iff]

namespace ConstituentWord

variable {lam : CycleType}

noncomputable def embed (w : ConstituentWord lam α) (e : α ↪ β) : ConstituentWord lam β where
  factors := w.factors.map (viaEmbeddingHom e)
  isCycle := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact viaEmbedding_isCycle b e (w.isCycle b hb)
  length_mem_J := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [viaEmbeddingHom_apply, viaEmbedding_support_card]
    exact w.length_mem_J b hb

theorem embed_value (w : ConstituentWord lam α) (e : α ↪ β) :
    (w.embed e).value = w.value.viaEmbedding e := by
  exact (map_list_prod (viaEmbeddingHom e) w.factors).symm

theorem embed_c (w : ConstituentWord lam α) (e : α ↪ β) : (w.embed e).c = w.c := by
  funext ℓ
  simp [c, embed, List.map_map, Function.comp_def,
    viaEmbeddingHom_apply, viaEmbedding_support_card]

theorem embed_hasTarget (w : ConstituentWord lam α) (e : α ↪ β) {r s : ℕ}
    (ht : w.HasTarget r s) : (w.embed e).HasTarget r s := by
  unfold HasTarget
  rw [embed_value, viaEmbedding_cycleType]
  exact ht

theorem embed_value_support (w : ConstituentWord lam α) (e : α ↪ β) :
    (↑(w.embed e).value.support : Set β) ⊆ Set.range e := by
  rw [embed_value]
  exact viaEmbedding_support_subset w.value e

theorem embed_mem_support (w : ConstituentWord lam α) (e : α ↪ β) (x : α) :
    e x ∈ (w.embed e).support ↔ x ∈ w.support := by
  rw [mem_support, mem_support]
  constructor
  · rintro ⟨a, ha, hx⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact ⟨b, hb, (viaEmbedding_mem_support b e x).mp hx⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨viaEmbeddingHom e a, List.mem_map.mpr ⟨a, ha, rfl⟩,
      (viaEmbedding_mem_support a e x).mpr hx⟩

theorem embed_support (w : ConstituentWord lam α) (e : α ↪ β) (y : β) :
    y ∈ (w.embed e).support ↔ ∃ x ∈ w.support, e x = y := by
  constructor
  · intro hy
    obtain ⟨a, ha, hy⟩ := ((w.embed e).mem_support y).mp hy
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨x, rfl⟩ := viaEmbedding_support_subset b e hy
    exact ⟨x, (w.embed_mem_support e x).mp
      (((w.embed e).mem_support (e x)).mpr ⟨viaEmbeddingHom e b,
        List.mem_map.mpr ⟨b, by assumption, rfl⟩, hy⟩), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (w.embed_mem_support e x).mpr hx

theorem embed_connected (w : ConstituentWord lam α) (e : α ↪ β)
    (hw : w.supportGraph.Connected) : (w.embed e).supportGraph.Connected := by
  let f : w.supportGraph →g (w.embed e).supportGraph :=
    { toFun := fun x => ⟨e x.val, (w.embed_mem_support e x.val).mpr x.property⟩
      map_rel' := by
        rintro x y ⟨hne, a, ha, hx, hy⟩
        refine ⟨?_, viaEmbeddingHom e a, List.mem_map.mpr ⟨a, ha, rfl⟩,
          (viaEmbedding_mem_support a e x.val).mpr hx,
          (viaEmbedding_mem_support a e y.val).mpr hy⟩
        intro he
        exact hne (Subtype.ext (e.injective (congrArg Subtype.val he))) }
  apply hw.map f
  intro y
  obtain ⟨x, hx, hxy⟩ := (w.embed_support e y.val).mp y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

noncomputable def disjointUnion (w : ConstituentWord lam α) (v : ConstituentWord lam β) :
    ConstituentWord lam (α ⊕ β) :=
  (w.embed ⟨Sum.inl, Sum.inl_injective⟩).append (v.embed ⟨Sum.inr, Sum.inr_injective⟩)

theorem disjointUnion_c (w : ConstituentWord lam α) (v : ConstituentWord lam β) :
    (w.disjointUnion v).c = w.c + v.c := by
  rw [disjointUnion, c_append, embed_c, embed_c]

theorem disjointUnion_hasTarget (w : ConstituentWord lam α) (v : ConstituentWord lam β)
    {r s t : ℕ} (hw : w.HasTarget r s) (hv : v.HasTarget r t) :
    (w.disjointUnion v).HasTarget r (s + t) := by
  let e : α ↪ α ⊕ β := ⟨Sum.inl, Sum.inl_injective⟩
  let f : β ↪ α ⊕ β := ⟨Sum.inr, Sum.inr_injective⟩
  have hd : Disjoint (w.embed e).value (v.embed f).value := by
    rw [disjoint_iff_disjoint_support]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha⟩ := w.embed_value_support e hx
    obtain ⟨b, hb⟩ := v.embed_value_support f hy
    exact Sum.inl_ne_inr (ha.trans hb.symm)
  change ((w.embed e).append (v.embed f)).value.cycleType = _
  rw [value_append, hd.cycleType_mul, w.embed_hasTarget e hw, v.embed_hasTarget f hv,
    Multiset.replicate_add]

end ConstituentWord

end ConjugacyDiametersPORC
