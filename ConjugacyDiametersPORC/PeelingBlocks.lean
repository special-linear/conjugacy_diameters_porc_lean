import ConjugacyDiametersPORC.CycleProducts

/-!
# Consecutive-block cancellation in a long cycle

Removing the cycle on each consecutive block retains its first label. The
surviving cycle reads those first labels, followed by the untouched suffix.
Singleton survivors are represented by their one-label lists.
-/

namespace ConjugacyDiametersPORC

open Equiv

theorem formPerm_append_comm {β : Type*} [DecidableEq β] (l₁ l₂ : List β)
    (h : (l₁ ++ l₂).Nodup) : (l₁ ++ l₂).formPerm = (l₂ ++ l₁).formPerm := by
  simpa only [List.rotate_append_length_eq] using
    (List.formPerm_rotate (l₁ ++ l₂) h l₁.length).symm

/-- Cancel one initial block, leaving its first label in the surviving cycle. -/
theorem formPerm_peel_head {β : Type*} [DecidableEq β] (x : β) (l t : List β)
    (h : ((x :: l) ++ t).Nodup) :
    ((x :: l) ++ t).formPerm = (x :: t).formPerm * (x :: l).formPerm := by
  have hres : (x :: t).Nodup := h.sublist ((List.sublist_append_right l t).cons_cons x)
  calc
    _ = (t ++ x :: l).formPerm := formPerm_append_comm _ _ h
    _ = (t ++ [x]).formPerm * (x :: l).formPerm := (formPerm_append_overlap t l x).symm
    _ = _ := by rw [← formPerm_append_comm [x] t hres]; rfl

namespace Peeling

variable {β : Type*} [DecidableEq β]

/-- A block, represented by its first label and its remaining labels. -/
abbrev Block (β : Type*) := β × List β

def blockList (b : Block β) : List β := b.1 :: b.2
def labels (bs : List (Block β)) : List β := bs.flatMap blockList
def heads (bs : List (Block β)) : List β := bs.map Prod.fst
def factors (bs : List (Block β)) : List (Perm β) := bs.map (fun b => (blockList b).formPerm)

omit [DecidableEq β] in
theorem block_mem_labels {bs : List (Block β)} {b : Block β} (hb : b ∈ bs)
    {x : β} (hx : x ∈ blockList b) : x ∈ labels bs := List.mem_flatMap.mpr ⟨b, hb, hx⟩

omit [DecidableEq β] in
theorem block_sublist_labels {bs : List (Block β)} {b : Block β} (hb : b ∈ bs) :
    (blockList b).Sublist (labels bs) := by
  induction bs with
  | nil => simp at hb
  | cons c cs ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact List.sublist_append_left _ _
    · exact (ih hb).trans (List.sublist_append_right _ _)

omit [DecidableEq β] in
theorem heads_sublist (bs : List (Block β)) : (heads bs).Sublist (labels bs) := by
  induction bs with
  | nil => simp [heads, labels]
  | cons b bs ih =>
    simpa [heads, labels, blockList] using
      (ih.trans (List.sublist_append_right b.2 (labels bs))).cons_cons b.1

omit [DecidableEq β] in
theorem labels_length (bs : List (Block β)) :
    (labels bs).length = (bs.map (fun b => (blockList b).length)).sum := by
  simp [labels, List.length_flatMap]

omit [DecidableEq β] in
theorem exists_blocks (ks : List ℕ) (hk : ∀ k ∈ ks, 0 < k) (l : List β)
    (hlen : ks.sum ≤ l.length) :
    ∃ bs : List (Block β), ∃ t : List β, labels bs ++ t = l ∧
      bs.map (fun b => (blockList b).length) = ks ∧ t.length = l.length - ks.sum := by
  induction ks generalizing l with
  | nil => exact ⟨[], l, rfl, rfl, by simp⟩
  | cons k ks ih =>
    have hk₀ : 0 < k := hk k List.mem_cons_self
    have hkl : k ≤ l.length := by
      have he : k + ks.sum ≤ l.length := hlen
      omega
    have htake : (l.take k).length = k := by simp [List.length_take, Nat.min_eq_left hkl]
    have hnonempty : l.take k ≠ [] := by intro he; simp [he] at htake; omega
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hnonempty
    have hrem : ks.sum ≤ (l.drop k).length := by
      simp only [List.length_drop]
      have he : k + ks.sum ≤ l.length := hlen
      omega
    obtain ⟨bs, t, hbs, hbsk, ht⟩ := ih (fun j hj => hk j (List.mem_cons_of_mem k hj))
      (l.drop k) hrem
    refine ⟨(x, xs) :: bs, t, ?_, ?_, ?_⟩
    · simp only [labels, List.flatMap_cons, blockList, List.append_assoc]
      change (x :: xs) ++ (labels bs ++ t) = l
      rw [hbs, ← hx, List.take_append_drop]
    · simp only [List.map_cons, blockList]
      change (x :: xs).length :: bs.map (fun b => (blockList b).length) = k :: ks
      rw [← hx, htake, hbsk]
    · simpa only [List.length_drop, List.sum_cons, Nat.sub_sub] using ht

theorem factors_pairwise (bs : List (Block β)) (h : (labels bs).Nodup) :
    (factors bs).Pairwise Equiv.Perm.Disjoint := by
  induction bs with
  | nil => simp [factors]
  | cons b bs ih =>
    have hn : (blockList b ++ labels bs).Nodup := by simpa [labels] using h
    simp only [factors, List.map_cons, List.pairwise_cons]
    constructor
    · intro f hf
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
      apply formPerm_disjoint_of_lists
      intro x hx hy
      exact (List.nodup_append.mp hn).2.2 x hx x (block_mem_labels hc hy) rfl
    · exact ih (List.nodup_append.mp hn).2.1

/-- The product identity for all consecutive blocks at once. -/
theorem formPerm_blocks (bs : List (Block β)) (t : List β) (h : (labels bs ++ t).Nodup) :
    (labels bs ++ t).formPerm = (heads bs ++ t).formPerm * (factors bs).prod := by
  induction bs generalizing t with
  | nil => simp [labels, heads, factors]
  | cons b bs ih =>
    let L := labels bs ++ t
    have hfull : (blockList b ++ L).Nodup := by simpa [labels, L] using h
    have hres : (b.1 :: L).Nodup := hfull.sublist
      ((List.sublist_append_right b.2 L).cons_cons b.1)
    have hrot : (labels bs ++ (t ++ [b.1])).Nodup := by
      have he := (List.perm_append_comm (l₁ := [b.1]) (l₂ := L)).nodup_iff.mp hres
      simpa only [L, List.append_assoc] using he
    have hc : Commute (blockList b).formPerm (factors bs).prod := by
      apply Commute.list_prod_right
      intro f hf
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
      apply Equiv.Perm.Disjoint.commute
      apply formPerm_disjoint_of_lists
      intro x hx hy
      have hm : x ∈ L := List.mem_append_left t (block_mem_labels hc hy)
      exact (List.nodup_append.mp hfull).2.2 x hx x hm rfl
    have hsurv : (b.1 :: (heads bs ++ t)).Nodup := by
      exact hres.sublist (((heads_sublist bs).append_right t).cons_cons b.1)
    simp only [labels, List.flatMap_cons, List.append_assoc, heads, List.map_cons,
      List.cons_append, factors, List.prod_cons]
    change (blockList b ++ L).formPerm =
      (b.1 :: (heads bs ++ t)).formPerm * ((blockList b).formPerm * (factors bs).prod)
    have he : (blockList b ++ L).formPerm = (b.1 :: L).formPerm * (blockList b).formPerm :=
      formPerm_peel_head b.1 b.2 L hfull
    have hr₁ : (b.1 :: L).formPerm = (L ++ [b.1]).formPerm :=
      formPerm_append_comm [b.1] L hres
    have hr₂ : (b.1 :: (heads bs ++ t)).formPerm = ((heads bs ++ t) ++ [b.1]).formPerm :=
      formPerm_append_comm [b.1] (heads bs ++ t) hsurv
    rw [he, hr₁]
    simp only [L, List.append_assoc]
    change (labels bs ++ (t ++ [b.1])).formPerm * (blockList b).formPerm = _
    rw [ih _ hrot]
    rw [← List.append_assoc, ← hr₂]
    rw [mul_assoc, ← hc.eq]

end Peeling

end ConjugacyDiametersPORC
