import ConjugacyDiametersPORC.Baseline
import ConjugacyDiametersPORC.ConnectedDefect
import ConjugacyDiametersPORC.Dickson

/-!
# The finite dictionary

For each resource residue modulo `M = r + 1`, choose a word realizing every
coordinatewise minimal resource-defect tuple. Adjoin the explicit baseline
words. Every dictionary entry is an actual finite word with its target verified.
-/

namespace ConjugacyDiametersPORC

/-- A realized target word, with its finite ambient degree retained. -/
structure TargetWord (lam : CycleType) (r : ℕ) where
  n : ℕ
  word : ConstituentWord lam (Fin n)
  s : ℕ
  target : word.HasTarget r s

/-- Resource residues `ρ ∈ (ℤ/Mℤ)^J`, represented by their least residues. -/
abbrev ResourceResidue (lam : CycleType) (r : ℕ) := lam.J → Fin (r + 1)

/-- The resource coordinates, together with the natural defect coordinate. -/
abbrev ResourceDefectTuple (lam : CycleType) := Option lam.J → ℕ

namespace TargetWord

variable {lam : CycleType} {r : ℕ}

def c (A : TargetWord lam r) : ResourceVector lam := A.word.c

def E (A : TargetWord lam r) : ℤ := A.word.E r A.s

def Connected (A : TargetWord lam r) : Prop := A.word.supportGraph.Connected ∧ A.c ≠ 0

def residue (A : TargetWord lam r) : ResourceResidue lam r :=
  fun ℓ => ⟨A.c ℓ % (r + 1), Nat.mod_lt _ (Nat.succ_pos r)⟩

def coordinates (A : TargetWord lam r) : ResourceDefectTuple lam
  | none => A.E.toNat
  | some ℓ => A.c ℓ

theorem defect_nonneg (A : TargetWord lam r) (hr : 2 ≤ r) (hA : A.Connected) : 0 ≤ A.E :=
  connected_defect_nonneg A.word r A.s hr hA.1 hA.2 A.target

end TargetWord

/-- The realized resource-defect tuples in residue class `ρ`. -/
def X (lam : CycleType) (r : ℕ) (ρ : ResourceResidue lam r) : Set (ResourceDefectTuple lam) :=
  {v | ∃ A : TargetWord lam r, A.Connected ∧ A.residue = ρ ∧ A.coordinates = v}

def minimalTuples (lam : CycleType) (r : ℕ) (ρ : ResourceResidue lam r) :
    Set (ResourceDefectTuple lam) := {v | Minimal (· ∈ X lam r ρ) v}

theorem minimalTuples_finite (lam : CycleType) (r : ℕ) (ρ : ResourceResidue lam r) :
    (minimalTuples lam r ρ).Finite := (lemma3 (X lam r ρ)).1

/-- Choose a realizing word for each minimal tuple. -/
noncomputable def selectedWord (lam : CycleType) (r : ℕ) (ρ : ResourceResidue lam r)
    (v : minimalTuples lam r ρ) : TargetWord lam r := Classical.choose v.property.prop

theorem selectedWord_spec (lam : CycleType) (r : ℕ) (ρ : ResourceResidue lam r)
    (v : minimalTuples lam r ρ) :
    (selectedWord lam r ρ v).Connected ∧ (selectedWord lam r ρ v).residue = ρ ∧
      (selectedWord lam r ρ v).coordinates = v.val := Classical.choose_spec v.property.prop

def baselineTargetWord (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (ℓ : lam.J) : TargetWord lam r where
  n := r * ((ℓ : ℕ) - 1) + 1
  word := baselineWord lam r hr ℓ
  s := (ℓ : ℕ) - 1
  target := baselineWord_hasTarget lam r hr ℓ

/-- `𝒜_r`, consisting of the selected realized words and the baselines. -/
def 𝒜 (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) : Set (TargetWord lam r) :=
  (⋃ ρ, Set.range (selectedWord lam r ρ)) ∪ Set.range (baselineTargetWord lam r hr)

theorem selectedWord_mem_dictionary (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (ρ : ResourceResidue lam r) (v : minimalTuples lam r ρ) :
    selectedWord lam r ρ v ∈ 𝒜 lam r hr :=
  Or.inl (Set.mem_iUnion.mpr ⟨ρ, Set.mem_range_self v⟩)

theorem baseline_mem_dictionary (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (ℓ : lam.J) :
    baselineTargetWord lam r hr ℓ ∈ 𝒜 lam r hr := Or.inr (Set.mem_range_self ℓ)

theorem dictionary_finite (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) : (𝒜 lam r hr).Finite := by
  apply Set.Finite.union _ (Set.finite_range _)
  apply Set.finite_iUnion
  intro ρ
  let _ := (minimalTuples_finite lam r ρ).to_subtype
  exact Set.finite_range _

theorem baselineTargetWord_c_ne_zero (lam : CycleType) (r : ℕ) (hr : 2 ≤ r) (ℓ : lam.J) :
    (baselineTargetWord lam r hr ℓ).c ≠ 0 := by
  apply (baselineWord lam r hr ℓ).c_ne_zero_iff.mpr
  intro he
  have hl := baselineWord_length lam r hr ℓ
  rw [he] at hl
  simp at hl

theorem dictionary_c_ne_zero (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (A : TargetWord lam r) (hA : A ∈ 𝒜 lam r hr) : A.c ≠ 0 := by
  rcases hA with hA | hA
  · obtain ⟨ρ, hA⟩ := Set.mem_iUnion.mp hA
    obtain ⟨v, rfl⟩ := hA
    exact (selectedWord_spec lam r ρ v).1.2
  · obtain ⟨ℓ, rfl⟩ := hA
    exact baselineTargetWord_c_ne_zero lam r hr ℓ

/-- Select a realized minimal pair in the same resource residue class. -/
theorem exists_dictionary_word_le (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (T : TargetWord lam r) (hT : T.Connected) :
    ∃ A ∈ 𝒜 lam r hr, A.c ≤ T.c ∧ A.E ≤ T.E ∧ A.residue = T.residue := by
  have hmem : T.coordinates ∈ X lam r T.residue := ⟨T, hT, rfl, rfl⟩
  obtain ⟨v, hv, hmin⟩ := (lemma3 (X lam r T.residue)).2 T.coordinates hmem
  let u : minimalTuples lam r T.residue := ⟨v, hmin⟩
  let A := selectedWord lam r T.residue u
  have hA := selectedWord_spec lam r T.residue u
  have hcoords : A.coordinates = v := hA.2.2
  have hc : A.c ≤ T.c := by
    intro ℓ
    have h := hv (some ℓ)
    rw [← hcoords] at h
    exact h
  have hE : A.E ≤ T.E := by
    have h := hv none
    rw [← hcoords] at h
    have hnat : A.E.toNat ≤ T.E.toNat := h
    have hz : (A.E.toNat : ℤ) ≤ (T.E.toNat : ℤ) := by exact_mod_cast hnat
    rwa [Int.toNat_of_nonneg (A.defect_nonneg hr hA.1),
      Int.toNat_of_nonneg (T.defect_nonneg hr hT)] at hz
  exact ⟨A, selectedWord_mem_dictionary lam r hr T.residue u, hc, hE, hA.2.1⟩

/-- The number of baselines needed in each coordinate to complete a minimal word. -/
def baselineMultiplicity {lam : CycleType} {r : ℕ} (A T : TargetWord lam r) :
    ResourceVector lam := fun ℓ => T.c ℓ / (r + 1) - A.c ℓ / (r + 1)

theorem baselineMultiplicity_inventory {lam : CycleType} {r : ℕ} (A T : TargetWord lam r)
    (hc : A.c ≤ T.c) (hres : A.residue = T.residue) :
    A.c + (r + 1) • baselineMultiplicity A T = T.c := by
  funext ℓ
  have hquot := Nat.div_le_div_right (c := r + 1) (hc ℓ)
  have hmod : A.c ℓ % (r + 1) = T.c ℓ % (r + 1) :=
    congrArg Fin.val (congrFun hres ℓ)
  have hA := Nat.mod_add_div (A.c ℓ) (r + 1)
  have hT := Nat.mod_add_div (T.c ℓ) (r + 1)
  have hk := Nat.sub_add_cancel hquot
  change A.c ℓ + (r + 1) * (T.c ℓ / (r + 1) - A.c ℓ / (r + 1)) = T.c ℓ
  nlinarith

theorem baselineMultiplicity_target_bound {lam : CycleType} {r : ℕ}
    (A T : TargetWord lam r) (hc : A.c ≤ T.c) (hE : A.E ≤ T.E)
    (hres : A.residue = T.residue) : T.s ≤ A.s + δ lam (baselineMultiplicity A T) := by
  have hd : δ lam T.c = δ lam A.c + (r + 1) * δ lam (baselineMultiplicity A T) := by
    rw [← baselineMultiplicity_inventory A T hc hres, delta_add, delta_smul]
  have hdz : (δ lam T.c : ℤ) = (δ lam A.c : ℤ) +
      ((r : ℤ) + 1) * (δ lam (baselineMultiplicity A T) : ℤ) := by
    exact_mod_cast hd
  change (δ lam A.c : ℤ) - ((r : ℤ) + 1) * (A.s : ℤ) + 2 ≤
    (δ lam T.c : ℤ) - ((r : ℤ) + 1) * (T.s : ℤ) + 2 at hE
  have hr : (0 : ℤ) < (r : ℤ) + 1 := by omega
  have hs : (T.s : ℤ) ≤ (A.s : ℤ) + δ lam (baselineMultiplicity A T) := by
    nlinarith
  exact_mod_cast hs

/-- Baseline completion for a connected word, at the level of exact resources and counts. -/
theorem connected_dictionary_completion (lam : CycleType) (r : ℕ) (hr : 2 ≤ r)
    (T : TargetWord lam r) (hT : T.Connected) :
    ∃ A ∈ 𝒜 lam r hr, ∃ k : ResourceVector lam,
      A.c + (r + 1) • k = T.c ∧ T.s ≤ A.s + δ lam k := by
  obtain ⟨A, hA, hc, hE, hres⟩ := exists_dictionary_word_le lam r hr T hT
  exact ⟨A, hA, baselineMultiplicity A T,
    baselineMultiplicity_inventory A T hc hres,
    baselineMultiplicity_target_bound A T hc hE hres⟩

end ConjugacyDiametersPORC
