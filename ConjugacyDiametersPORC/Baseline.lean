import ConjugacyDiametersPORC.ConstituentWord
import ConjugacyDiametersPORC.CycleProducts
import Mathlib.Data.List.OfFn

/-!
# Explicit baseline factors

For `u = ℓ - 1`, the baseline acts on `r u + 1` labels. In zero-based labels,
`B_j = (ju, ju+1, …, (j+1)u)` and `T = (0, r, …, ur)`.
The factor order is `T⁻¹ B₀ ⋯ B_{r-1}`.
-/

namespace ConjugacyDiametersPORC

namespace Baseline

def blockLetter {r u : ℕ} (j : Fin r) (i : Fin (u + 1)) : Fin (r * u + 1) :=
  ⟨j.val * u + i.val, by
    have hi : i.val ≤ u := by omega
    have hj : (j.val + 1) * u ≤ r * u := Nat.mul_le_mul_right u (by omega)
    have hle : j.val * u + i.val ≤ r * u := by
      calc
        j.val * u + i.val ≤ j.val * u + u := Nat.add_le_add_left hi _
        _ ≤ r * u := by simpa [Nat.add_mul] using hj
    omega⟩

def transverseLetter (r u : ℕ) (i : Fin (u + 1)) : Fin (r * u + 1) :=
  ⟨i.val * r, by
    have hi : i.val ≤ u := by omega
    have hle := Nat.mul_le_mul_right r hi
    rw [Nat.mul_comm u r] at hle
    omega⟩

def blockList {r u : ℕ} (j : Fin r) : List (Fin (r * u + 1)) :=
  List.ofFn (blockLetter (u := u) j)

def transverseList (r u : ℕ) : List (Fin (r * u + 1)) :=
  List.ofFn (transverseLetter r u)

def B {r u : ℕ} (j : Fin r) : Equiv.Perm (Fin (r * u + 1)) :=
  (blockList (u := u) j).formPerm

def T (r u : ℕ) : Equiv.Perm (Fin (r * u + 1)) :=
  (transverseList r u).formPerm

theorem blockList_nodup {r u : ℕ} (j : Fin r) : (blockList (u := u) j).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i₁ i₂ he
  apply Fin.ext
  have hval := congrArg Fin.val he
  dsimp [blockLetter] at hval
  omega

theorem transverseList_nodup {r u : ℕ} (hr : 0 < r) : (transverseList r u).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i₁ i₂ he
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_right hr (congrArg Fin.val he)

theorem B_isCycle {r u : ℕ} (j : Fin r) (hu : 0 < u) : (B (u := u) j).IsCycle := by
  apply List.isCycle_formPerm (blockList_nodup j)
  simpa [blockList] using (show 2 ≤ u + 1 by omega)

theorem T_isCycle {r u : ℕ} (hr : 0 < r) (hu : 0 < u) : (T r u).IsCycle := by
  apply List.isCycle_formPerm (transverseList_nodup hr)
  simpa [transverseList] using (show 2 ≤ u + 1 by omega)

theorem B_support_card {r u : ℕ} (j : Fin r) (hu : 0 < u) :
    (B (u := u) j).support.card = u + 1 := by
  rw [B, support_card_formPerm _ (blockList_nodup j)]
  · simp [blockList]
  · simp [blockList]
    omega

theorem T_support_card {r u : ℕ} (hr : 0 < r) (hu : 0 < u) :
    (T r u).support.card = u + 1 := by
  rw [T, support_card_formPerm _ (transverseList_nodup hr)]
  · simp [transverseList]
  · simp [transverseList]
    omega

def factors (r u : ℕ) : List (Equiv.Perm (Fin (r * u + 1))) :=
  (T r u)⁻¹ :: List.ofFn (B (r := r) (u := u))

theorem factors_length (r u : ℕ) : (factors r u).length = r + 1 := by
  simp [factors]

theorem factors_isCycle {r u : ℕ} (hr : 0 < r) (hu : 0 < u)
    {a : Equiv.Perm (Fin (r * u + 1))} (ha : a ∈ factors r u) : a.IsCycle := by
  rcases List.mem_cons.mp ha with rfl | ha
  · exact (T_isCycle hr hu).inv
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact B_isCycle j hu

theorem factors_support_card {r u : ℕ} (hr : 0 < r) (hu : 0 < u)
    {a : Equiv.Perm (Fin (r * u + 1))} (ha : a ∈ factors r u) :
    a.support.card = u + 1 := by
  rcases List.mem_cons.mp ha with rfl | ha
  · simpa using T_support_card hr hu
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact B_support_card j hu

/-- The overlapping block cycles multiply to the full displayed cycle. -/
theorem blocks_prod (r u : ℕ) :
    (List.ofFn (B (r := r) (u := u))).prod =
      (List.ofFn (fun i : Fin (r * u + 1) => i)).formPerm := by
  let φ (i : ℕ) : Fin (r * u + 1) :=
    ⟨i % (r * u + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hb (j : Fin r) :
      List.ofFn (fun i : Fin (u + 1) => φ (j.val * u + i.val)) =
        blockList (u := u) j := by
    apply congrArg List.ofFn
    funext i
    apply Fin.ext
    exact Nat.mod_eq_of_lt (blockLetter j i).isLt
  have hl : List.ofFn (fun i : Fin (r * u + 1) => φ i.val) =
      List.ofFn (fun i : Fin (r * u + 1) => i) := by
    apply congrArg List.ofFn
    funext i
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  change (List.ofFn (fun j : Fin r => (blockList (u := u) j).formPerm)).prod = _
  simpa only [hb, hl] using formPerm_blocks_prod φ r u

def rowLetter {r u : ℕ} (k : Fin u) (j : Fin r) : Fin (r * u + 1) :=
  ⟨k.val * r + j.val, by
    have hj := Nat.add_lt_add_left j.isLt (k.val * r)
    have hk := Nat.mul_le_mul_right r (Nat.succ_le_of_lt k.isLt)
    rw [Nat.succ_mul, Nat.mul_comm u r] at hk
    omega⟩

def rowList {r u : ℕ} (k : Fin u) : List (Fin (r * u + 1)) :=
  List.ofFn (rowLetter (r := r) k)

/-- The target cycles on consecutive rows of `r` labels. -/
def R {r u : ℕ} (k : Fin u) : Equiv.Perm (Fin (r * u + 1)) :=
  (rowList (r := r) k).formPerm

theorem rowLetter_div {r u : ℕ} (k : Fin u) (j : Fin r) :
    (rowLetter k j).val / r = k.val := by
  apply Nat.div_eq_of_lt_le (by simp [rowLetter])
  simp [rowLetter, Nat.add_mul]

theorem rowList_nodup {r u : ℕ} (k : Fin u) : (rowList (r := r) k).Nodup := by
  apply List.nodup_ofFn.mpr
  intro j₁ j₂ he
  apply Fin.ext
  have := congrArg Fin.val he
  dsimp [rowLetter] at this
  omega

theorem R_isCycle {r u : ℕ} (hr : 2 ≤ r) (k : Fin u) :
    (R (r := r) k).IsCycle := by
  apply List.isCycle_formPerm (rowList_nodup k)
  simpa [rowList] using hr

theorem R_support_card {r u : ℕ} (hr : 2 ≤ r) (k : Fin u) :
    (R (r := r) k).support.card = r := by
  rw [R, support_card_formPerm _ (rowList_nodup k)]
  · simp [rowList]
  · simpa [rowList] using hr

theorem R_disjoint {r u : ℕ} (hr : 2 ≤ r) (k k' : Fin u) (hk : k ≠ k') :
    Equiv.Perm.Disjoint (R (r := r) k) (R (r := r) k') := by
  apply (List.formPerm_disjoint_iff (rowList_nodup k) (rowList_nodup k')
    (by simpa [rowList] using hr) (by simpa [rowList] using hr)).mpr
  intro x hx hx'
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  obtain ⟨j', he⟩ := List.mem_ofFn.mp hx'
  have hdiv := congrArg (fun x : Fin (r * u + 1) => x.val / r) he
  rw [rowLetter_div, rowLetter_div] at hdiv
  exact hk (Fin.ext hdiv.symm)

theorem rows_pairwise_disjoint {r u : ℕ} (hr : 2 ≤ r) :
    (List.ofFn (R (r := r) (u := u))).Pairwise Equiv.Perm.Disjoint := by
  apply List.pairwise_ofFn.mpr
  intro k k' hk
  exact R_disjoint hr k k' (ne_of_lt hk)

theorem rowLetter_mem_support {r u : ℕ} (hr : 2 ≤ r) (k : Fin u) (j : Fin r) :
    rowLetter k j ∈ (R (r := r) k).support := by
  rw [R, List.support_formPerm_of_nodup _ (rowList_nodup k)]
  · exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · intro x he
    have he' := congrArg List.length he
    simp [rowList] at he'
    omega

theorem rows_prod_apply {r u : ℕ} (hr : 2 ≤ r) (k : Fin u) (j : Fin r) :
    (List.ofFn (R (r := r) (u := u))).prod (rowLetter k j) =
      rowLetter k ⟨(j.val + 1) % r, Nat.mod_lt _ (by omega)⟩ := by
  rw [← Equiv.Perm.eq_on_support_mem_disjoint (List.mem_ofFn.mpr ⟨k, rfl⟩)
    (rows_pairwise_disjoint hr) _ (rowLetter_mem_support hr k j)]
  exact formPerm_ofFn_apply (rowLetter k)
    (List.nodup_ofFn.mp (rowList_nodup k)) j

theorem T_apply_transverse {r u : ℕ} (hr : 0 < r) (i : Fin (u + 1)) :
    T r u (transverseLetter r u i) =
      transverseLetter r u
        ⟨(i.val + 1) % (u + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ :=
  formPerm_ofFn_apply (transverseLetter r u)
    (List.nodup_ofFn.mp (transverseList_nodup hr)) i

theorem T_fix_row_interior {r u : ℕ} (k : Fin u)
    (j : Fin r) (hj : 0 < j.val) : T r u (rowLetter k j) = rowLetter k j := by
  apply List.formPerm_apply_of_notMem
  intro hx
  obtain ⟨i, he⟩ := List.mem_ofFn.mp hx
  have hm := congrArg (fun x : Fin (r * u + 1) => x.val % r) he
  have hz : (i.val * r) % r = 0 := by simp
  have hrow : (k.val * r + j.val) % r = j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  change (i.val * r) % r = (k.val * r + j.val) % r at hm
  rw [hz, hrow] at hm
  omega

theorem rowLetter_lt {r u : ℕ} (k : Fin u) (j : Fin r) :
    (rowLetter k j).val < r * u := by
  have hj := Nat.add_lt_add_left j.isLt (k.val * r)
  have hk := Nat.mul_le_mul_right r (Nat.succ_le_of_lt k.isLt)
  rw [Nat.succ_mul, Nat.mul_comm u r] at hk
  exact lt_of_lt_of_le hj hk

theorem rows_fix_last (r u : ℕ) :
    (List.ofFn (R (r := r) (u := u))).prod (Fin.last (r * u)) = Fin.last (r * u) := by
  apply Equiv.Perm.notMem_support.mp
  intro hx
  obtain ⟨a, ha, hx⟩ := Equiv.Perm.exists_mem_support_of_mem_support_prod hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
  have hm := List.mem_toFinset.mp (List.support_formPerm_le (rowList k) hx)
  obtain ⟨j, he⟩ := List.mem_ofFn.mp hm
  have ht := rowLetter_lt k j
  rw [he] at ht
  simp at ht

/-- The transverse cycle joins the consecutive target rows into a full cycle. -/
theorem T_mul_rows {r u : ℕ} (hr : 2 ≤ r) :
    T r u * (List.ofFn (R (r := r) (u := u))).prod =
      (List.ofFn (fun i : Fin (r * u + 1) => i)).formPerm := by
  have hrow (k : Fin u) (j : Fin r) :
      (T r u * (List.ofFn (R (r := r) (u := u))).prod) (rowLetter k j) =
        (List.ofFn (fun i : Fin (r * u + 1) => i)).formPerm (rowLetter k j) := by
    rw [Equiv.Perm.mul_apply, rows_prod_apply hr,
      formPerm_ofFn_apply (fun i : Fin (r * u + 1) => i) Function.injective_id]
    have hv : (rowLetter k j).val + 1 < r * u + 1 := by
      have := rowLetter_lt k j
      omega
    change k.val * r + j.val + 1 < r * u + 1 at hv
    by_cases hj : j.val + 1 < r
    · have hnext : (j.val + 1) % r = j.val + 1 := Nat.mod_eq_of_lt hj
      have hfix := T_fix_row_interior k (⟨j.val + 1, hj⟩ : Fin r)
        (by simp)
      simp only [hnext]
      rw [hfix]
      apply Fin.ext
      change k.val * r + (j.val + 1) = (k.val * r + j.val + 1) % (r * u + 1)
      rw [Nat.mod_eq_of_lt hv, Nat.add_assoc]
    · have he : j.val + 1 = r := by omega
      have hz : (j.val + 1) % r = 0 := by rw [he, Nat.mod_self]
      have hin : rowLetter k ⟨(j.val + 1) % r, Nat.mod_lt _ (by omega)⟩ =
          transverseLetter r u ⟨k.val, by omega⟩ := by
        apply Fin.ext
        simp [rowLetter, transverseLetter, hz]
      rw [hin, T_apply_transverse (by omega)]
      apply Fin.ext
      have hk : k.val + 1 < u + 1 := by omega
      change ((k.val + 1) % (u + 1)) * r =
        (k.val * r + j.val + 1) % (r * u + 1)
      rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hv, Nat.add_mul, Nat.one_mul]
      omega
  apply Equiv.ext
  intro x
  by_cases hx : x.val < r * u
  · let k : Fin u := ⟨x.val / r, Nat.div_lt_of_lt_mul hx⟩
    let j : Fin r := ⟨x.val % r, Nat.mod_lt _ (by omega)⟩
    have he : rowLetter k j = x := by
      apply Fin.ext
      simpa [rowLetter, k, j, Nat.mul_comm] using Nat.div_add_mod x.val r
    rw [← he]
    exact hrow k j
  · have he : x = Fin.last (r * u) := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [he, Equiv.Perm.mul_apply, rows_fix_last]
    have ht := T_apply_transverse (r := r) (u := u) (by omega)
      (⟨u, Nat.lt_succ_self u⟩ : Fin (u + 1))
    have hin : transverseLetter r u ⟨u, Nat.lt_succ_self u⟩ = Fin.last (r * u) := by
      apply Fin.ext
      simp [transverseLetter, Nat.mul_comm]
    rw [hin] at ht
    rw [ht, formPerm_ofFn_apply (fun i : Fin (r * u + 1) => i) Function.injective_id]
    apply Fin.ext
    simp [transverseLetter]

theorem factors_prod {r u : ℕ} (hr : 2 ≤ r) :
    (factors r u).prod = (List.ofFn (R (r := r) (u := u))).prod := by
  rw [factors, List.prod_cons, blocks_prod, ← T_mul_rows hr, inv_mul_cancel_left]

theorem factors_cycleType {r u : ℕ} (hr : 2 ≤ r) :
    (factors r u).prod.cycleType = Multiset.replicate u r := by
  rw [factors_prod hr, Equiv.Perm.cycleType_eq _ rfl]
  · simp [List.map_ofFn, Function.comp_def, R_support_card hr, Multiset.coe_replicate]
  · intro a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    exact R_isCycle hr k
  · exact rows_pairwise_disjoint hr

end Baseline

/-- The explicit baseline constituent word. -/
def baselineWord (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (ℓ : lam.J) :
    ConstituentWord lam (Fin (r * ((ℓ : ℕ) - 1) + 1)) where
  factors := Baseline.factors r ((ℓ : ℕ) - 1)
  isCycle := fun _ ha => Baseline.factors_isCycle (by omega)
    (by have := lam.two_le_of_mem_J ℓ.property; omega) ha
  length_mem_J := by
    intro a ha
    rw [Baseline.factors_support_card (by omega)
      (by have := lam.two_le_of_mem_J ℓ.property; omega) ha]
    have he : (ℓ : ℕ) - 1 + 1 = ℓ := by
      have := lam.two_le_of_mem_J ℓ.property
      omega
    rw [he]
    exact ℓ.property

theorem baselineWord_length (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (ℓ : lam.J) :
    (baselineWord lam r hr ℓ).factors.length = r + 1 :=
  Baseline.factors_length r ((ℓ : ℕ) - 1)

/-- The baseline uses exactly `r + 1` constituents of the chosen length. -/
theorem baselineWord_c (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (ℓ : lam.J) :
    (baselineWord lam r hr ℓ).c = (r + 1) • unitResource lam ℓ := by
  have hmap : (baselineWord lam r hr ℓ).factors.map (fun a => a.support.card) =
      List.replicate (r + 1) (ℓ : ℕ) := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp [baselineWord_length], ?_⟩
    intro t ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    change a ∈ Baseline.factors r ((ℓ : ℕ) - 1) at ha
    rw [Baseline.factors_support_card (by omega)
      (by have := lam.two_le_of_mem_J ℓ.property; omega) ha]
    have := lam.two_le_of_mem_J ℓ.property
    omega
  funext t
  change (List.count (t : ℕ) _) = _
  rw [hmap]
  by_cases ht : t = ℓ
  · subst t
    simp [unitResource]
  · have hval : (t : ℕ) ≠ (ℓ : ℕ) := fun he => ht (Subtype.ext he)
    simp [unitResource, ht, List.count_replicate, Ne.symm hval]

theorem baselineWord_delta (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (ℓ : lam.J) :
    δ lam (baselineWord lam r hr ℓ).c = (r + 1) * ((ℓ : ℕ) - 1) := by
  rw [baselineWord_c, delta_smul, delta_unitResource]

theorem baselineWord_hasTarget (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (ℓ : lam.J) :
    (baselineWord lam r hr ℓ).HasTarget r ((ℓ : ℕ) - 1) :=
  Baseline.factors_cycleType hr

theorem baselineWord_E (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (ℓ : lam.J) :
    (baselineWord lam r hr ℓ).E r ((ℓ : ℕ) - 1) = 2 := by
  rw [ConstituentWord.E, baselineWord_delta]
  push_cast
  ring

/-- **Lemma 1.** The baseline has inventory `M e_ℓ` and exactly `ℓ - 1`
target cycles of length `r`, where `M = r + 1`. -/
theorem lemma1 (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (ℓ : lam.J) :
    (baselineWord lam r hr ℓ).c = (r + 1) • unitResource lam ℓ ∧
      (baselineWord lam r hr ℓ).HasTarget r ((ℓ : ℕ) - 1) :=
  ⟨baselineWord_c lam r hr ℓ, baselineWord_hasTarget lam r hr ℓ⟩

end ConjugacyDiametersPORC
