import ConjugacyDiametersPORC.Dictionary
import ConjugacyDiametersPORC.WordEmbedding
import ConjugacyDiametersPORC.WordComponents

/-!
# Realizing unions of dictionary words

Each finite collection is realized on disjoint label sets and then relabeled by
`Fin n`. Its inventory and target-cycle count are the sums of those of its entries.
-/

namespace ConjugacyDiametersPORC

namespace TargetWord

variable {lam : CycleType} {r : ℕ}

noncomputable def ofWord {α : Type*} [Fintype α] [DecidableEq α]
    (w : ConstituentWord lam α) (s : ℕ) (ht : w.HasTarget r s) : TargetWord lam r where
  n := Fintype.card α
  word := w.embed (Fintype.equivFin α).toEmbedding
  s := s
  target := w.embed_hasTarget _ ht

theorem ofWord_c {α : Type*} [Fintype α] [DecidableEq α]
    (w : ConstituentWord lam α) (s : ℕ) (ht : w.HasTarget r s) : (ofWord w s ht).c = w.c :=
  w.embed_c _

theorem ofWord_connected {α : Type*} [Fintype α] [DecidableEq α]
    (w : ConstituentWord lam α) (s : ℕ) (ht : w.HasTarget r s)
    (hconn : w.supportGraph.Connected) (hc : w.c ≠ 0) : (ofWord w s ht).Connected := by
  exact ⟨w.embed_connected _ hconn, by simpa only [ofWord_c] using hc⟩

noncomputable def union (A B : TargetWord lam r) : TargetWord lam r :=
  ofWord (A.word.disjointUnion B.word) (A.s + B.s)
    (A.word.disjointUnion_hasTarget B.word A.target B.target)

theorem union_c (A B : TargetWord lam r) : (A.union B).c = A.c + B.c := by
  rw [union, ofWord_c, ConstituentWord.disjointUnion_c]
  rfl

theorem union_s (A B : TargetWord lam r) : (A.union B).s = A.s + B.s := rfl

def empty (lam : CycleType) (r : ℕ) : TargetWord lam r where
  n := 0
  word := ConstituentWord.nil
  s := 0
  target := by simp [ConstituentWord.HasTarget]

@[simp]
theorem empty_c : (empty lam r).c = 0 := ConstituentWord.c_nil

@[simp]
theorem empty_s : (empty lam r).s = 0 := rfl

noncomputable def unionList (lam : CycleType) (r : ℕ) : List (TargetWord lam r) → TargetWord lam r
  | [] => empty lam r
  | A :: l => A.union (unionList lam r l)

theorem unionList_c (l : List (TargetWord lam r)) :
    (unionList lam r l).c = (l.map c).sum := by
  induction l with
  | nil => simp [unionList]
  | cons A l ih => simp [unionList, union_c, ih]

theorem unionList_s (l : List (TargetWord lam r)) :
    (unionList lam r l).s = (l.map s).sum := by
  induction l with
  | nil => simp [unionList]
  | cons A l ih => simp [unionList, union_s, ih]

end TargetWord

/-- All baseline copies required by a resource vector of multiplicities. -/
noncomputable def baselineCopies (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (k : ResourceVector lam) :
    List (TargetWord lam r) :=
  Finset.univ.toList.flatMap (fun ℓ => List.replicate (k ℓ) (baselineTargetWord lam r hr ℓ))

theorem baselineCopies_mem (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (k : ResourceVector lam)
    (A : TargetWord lam r) (hA : A ∈ baselineCopies lam r hr k) : A ∈ 𝒜 lam r hr := by
  obtain ⟨ℓ, _, hA⟩ := List.mem_flatMap.mp hA
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp hA
  exact baseline_mem_dictionary lam r hr ℓ

private theorem sum_flatMap {ι M : Type*} [AddMonoid M] (l : List ι) (f : ι → List M) :
    (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

private theorem sum_apply {ι M : Type*} [AddMonoid M] (l : List (ι → M)) (x : ι) :
    l.sum x = (l.map (fun f => f x)).sum := by
  induction l with
  | nil => rfl
  | cons f l ih => simp [ih]

theorem baselineCopies_c (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (k : ResourceVector lam) :
    ((baselineCopies lam r hr k).map TargetWord.c).sum = (r + 1) • k := by
  funext t
  simp [baselineCopies, List.map_flatMap, sum_flatMap, sum_apply, List.sum_replicate,
    TargetWord.c, baselineTargetWord, baselineWord_c, unitResource,
    mul_comm]

theorem baselineCopies_s (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (k : ResourceVector lam) :
    ((baselineCopies lam r hr k).map TargetWord.s).sum = δ lam k := by
  simp [baselineCopies, List.map_flatMap, sum_flatMap, List.sum_replicate,
    baselineTargetWord, δ, mul_comm]

/-- Copies of a finite indexed family of realized target words, with multiplicity. -/
noncomputable def wordCopies {lam : CycleType} {r : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → TargetWord lam r) (z : ι → ℕ) : List (TargetWord lam r) :=
  Finset.univ.toList.flatMap (fun i => List.replicate (z i) (A i))

theorem wordCopies_c {lam : CycleType} {r : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → TargetWord lam r) (z : ι → ℕ) :
    ((wordCopies A z).map TargetWord.c).sum = ∑ i, z i • (A i).c := by
  simp [wordCopies, List.map_flatMap, sum_flatMap, List.sum_replicate]

theorem wordCopies_s {lam : CycleType} {r : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → TargetWord lam r) (z : ι → ℕ) :
    ((wordCopies A z).map TargetWord.s).sum = ∑ i, z i * (A i).s := by
  simp [wordCopies, List.map_flatMap, sum_flatMap, List.sum_replicate]

/-- Realized baseline completion of a nonempty connected target word. -/
theorem connected_dictionary_union (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (T : TargetWord lam r) (hT : T.Connected) :
    ∃ l : List (TargetWord lam r), (∀ A ∈ l, A ∈ 𝒜 lam r hr) ∧
      (TargetWord.unionList lam r l).c = T.c ∧ T.s ≤ (TargetWord.unionList lam r l).s := by
  obtain ⟨A, hA, k, hc, hs⟩ := connected_dictionary_completion lam r hr T hT
  refine ⟨A :: baselineCopies lam r hr k, ?_, ?_, ?_⟩
  · intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hA
    · exact baselineCopies_mem lam r hr k B hB
  · rw [TargetWord.unionList_c, List.map_cons, List.sum_cons, baselineCopies_c]
    exact hc
  · rw [TargetWord.unionList_s, List.map_cons, List.sum_cons, baselineCopies_s]
    exact hs

theorem component_dictionary_collection {lam : CycleType} {α : Type*}
    [Fintype α] [DecidableEq α] (w : ConstituentWord lam α)
    (C : w.ambientGraph.ConnectedComponent) (r : ℕ) (hr : 2 ≤ r) {s : ℕ}
    (ht : w.HasTarget r s) :
    ∃ l : List (TargetWord lam r), (∀ A ∈ l, A ∈ 𝒜 lam r hr) ∧
      (l.map TargetWord.c).sum = (w.component C).c ∧
        (w.component C).value.cycleType.card ≤ (l.map TargetWord.s).sum := by
  by_cases hnil : (w.component C).factors = []
  · refine ⟨[], by simp, ?_, ?_⟩
    · funext ℓ
      simp [ConstituentWord.c, hnil]
    · simp [ConstituentWord.value, hnil]
  · let u := w.component C
    let T := TargetWord.ofWord u u.value.cycleType.card (w.component_hasTarget C ht)
    have hT : T.Connected := TargetWord.ofWord_connected _ _ _
      (w.component_connected C hnil) (u.c_ne_zero_iff.mpr hnil)
    obtain ⟨l, hl, hc, hs⟩ := connected_dictionary_union lam r hr T hT
    rw [TargetWord.unionList_c, TargetWord.ofWord_c] at hc
    rw [TargetWord.unionList_s] at hs
    exact ⟨l, hl, hc, hs⟩

/-- **Lemma 4.** A disjoint union of dictionary words restores the exact inventory
and produces at least the original number of target cycles, allowing extra labels. -/
theorem lemma4 {lam : CycleType} {α : Type*} [Fintype α] [DecidableEq α]
    (w : ConstituentWord lam α) (r : ℕ) (hr : 2 ≤ r) (s : ℕ) (ht : w.HasTarget r s) :
    ∃ l : List (TargetWord lam r), (∀ A ∈ l, A ∈ 𝒜 lam r hr) ∧
      (TargetWord.unionList lam r l).c = w.c ∧ s ≤ (TargetWord.unionList lam r l).s := by
  classical
  have hC := fun C => component_dictionary_collection w C r hr ht
  choose f hf using hC
  let l := Finset.univ.toList.flatMap f
  refine ⟨l, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨C, _, hA⟩ := List.mem_flatMap.mp hA
    exact (hf C).1 A hA
  · rw [TargetWord.unionList_c]
    change ((Finset.univ.toList.flatMap f).map TargetWord.c).sum = w.c
    rw [List.map_flatMap, sum_flatMap]
    simp_rw [(hf _).2.1]
    simpa using w.component_inventory_sum
  · rw [TargetWord.unionList_s]
    change s ≤ ((Finset.univ.toList.flatMap f).map TargetWord.s).sum
    rw [List.map_flatMap, sum_flatMap]
    have hsum : (∑ C : w.ambientGraph.ConnectedComponent, (w.component C).value.cycleType.card) ≤
        ∑ C : w.ambientGraph.ConnectedComponent, ((f C).map TargetWord.s).sum :=
      Finset.sum_le_sum (fun C _ => (hf C).2.2)
    rw [w.component_target_count_sum ht] at hsum
    simpa using hsum

end ConjugacyDiametersPORC
