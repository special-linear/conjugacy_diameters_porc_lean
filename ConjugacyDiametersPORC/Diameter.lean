import ConjugacyDiametersPORC.CycleType
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

/-!
# Generating classes, word lengths, and diameters

The class `C_{λ,n}` generates the subgroup `G_n`. Word length `L_n` counts
generators in a shortest factorization, and the diameter `D_n` is its maximum.

These definitions use the actual generated subgroup, without assuming its eventual
identification with the symmetric or alternating group. They are defined for every
natural degree, including degrees too small to realize `λ`.
-/

namespace ConjugacyDiametersPORC

/-- `S_n`, acting on `Fin n`. Multiplication applies the right factor first. -/
abbrev SymmetricGroup (n : ℕ) := Equiv.Perm (Fin n)

/-- `C_{λ,n}`, the full symmetric-group conjugacy class of nontrivial cycle type `λ`.

`cycleType` omits fixed points, so the remaining `n - lam.b` labels are implicit.
If `n < lam.b`, this set is empty.
-/
def C (lam : CycleType) (n : ℕ) : Set (SymmetricGroup n) :=
  {g | g.cycleType = lam.parts}

/-- `G_n = ⟨C_{λ,n}⟩`, as a subgroup of `S_n`. -/
def G (lam : CycleType) (n : ℕ) : Subgroup (SymmetricGroup n) :=
  Subgroup.closure (C lam n)

/-- A word in elements of `C_{λ,n}` whose product is `g`.

The empty list represents the identity. No separate inverse letters are added:
inversion preserves cycle type, so the class itself is closed under inverses.
`List.prod` evaluates the ordered product `a₁ ⋯ a_K`.
-/
def IsFactorization (lam : CycleType) {n : ℕ} (g : SymmetricGroup n)
    (w : List (SymmetricGroup n)) : Prop :=
  (∀ a ∈ w, a ∈ C lam n) ∧ w.prod = g

/-- The lengths of all words in `C_{λ,n}` representing `g`. -/
def factorizationLengths (lam : CycleType) {n : ℕ} (g : SymmetricGroup n) : Set ℕ :=
  {k | ∃ w, IsFactorization lam g w ∧ w.length = k}

/-- `L_n(g)`, the minimum number of generators needed to represent `g ∈ G_n`.

This is the infimum of a set of natural numbers. Its nonemptiness follows from
subgroup membership and inverse closure of `C_{λ,n}`.
In particular, the empty-set default of `sInf : Set ℕ → ℕ` is never needed here.
-/
noncomputable def L (lam : CycleType) {n : ℕ} (g : G lam n) : ℕ :=
  sInf (factorizationLengths lam (g : SymmetricGroup n))

/-- `D_n = max_{g ∈ G_n} L_n(g)`, the Cayley-graph diameter.

The range is finite and nonempty because `G_n` is a finite group. Thus its natural
supremum is a maximum. Translation invariance identifies this maximum distance
from the identity with the diameter.
-/
noncomputable def D (lam : CycleType) (n : ℕ) : ℕ :=
  sSup (Set.range (L lam (n := n)))

@[simp]
theorem mem_C (lam : CycleType) {n : ℕ} (g : SymmetricGroup n) :
    g ∈ C lam n ↔ g.cycleType = lam.parts := Iff.rfl

@[simp]
theorem inv_mem_C_iff (lam : CycleType) {n : ℕ} (g : SymmetricGroup n) :
    g⁻¹ ∈ C lam n ↔ g ∈ C lam n := by
  simp only [mem_C, Equiv.Perm.cycleType_inv]

theorem C_nonempty_iff (lam : CycleType) (n : ℕ) :
    (C lam n).Nonempty ↔ lam.b ≤ n := by
  change (∃ g : SymmetricGroup n, g.cycleType = lam.parts) ↔ lam.b ≤ n
  rw [Equiv.Perm.exists_with_cycleType_iff]
  constructor
  · intro hg
    simpa [CycleType.b] using hg.1
  · intro hn
    exact ⟨by simpa [CycleType.b] using hn, lam.two_le⟩

@[simp]
theorem isFactorization_nil (lam : CycleType) (n : ℕ) :
    IsFactorization lam (1 : SymmetricGroup n) [] := by
  simp [IsFactorization]

theorem isFactorization_singleton (lam : CycleType) {n : ℕ} {g : SymmetricGroup n}
    (hg : g ∈ C lam n) : IsFactorization lam g [g] := by
  simpa [IsFactorization] using hg

theorem IsFactorization.append {lam : CycleType} {n : ℕ}
    {g₁ g₂ : SymmetricGroup n} {w₁ w₂ : List (SymmetricGroup n)}
    (h₁ : IsFactorization lam g₁ w₁) (h₂ : IsFactorization lam g₂ w₂) :
    IsFactorization lam (g₁ * g₂) (w₁ ++ w₂) := by
  constructor
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h₁.1 a ha
    · exact h₂.1 a ha
  · rw [List.prod_append, h₁.2, h₂.2]

theorem IsFactorization.inverse {lam : CycleType} {n : ℕ}
    {g : SymmetricGroup n} {w : List (SymmetricGroup n)}
    (hw : IsFactorization lam g w) :
    IsFactorization lam g⁻¹ ((w.map (fun a => a⁻¹)).reverse) := by
  constructor
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
    exact (inv_mem_C_iff lam b).mpr (hw.1 b hb)
  · rw [← List.prod_inv_reverse, hw.2]

theorem exists_factorization_of_mem (lam : CycleType) {n : ℕ} {g : SymmetricGroup n}
    (hg : g ∈ G lam n) : ∃ w, IsFactorization lam g w := by
  change g ∈ Subgroup.closure (C lam n) at hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx => exact ⟨[x], isFactorization_singleton lam hx⟩
  | inv_mem x hx =>
    exact ⟨[x⁻¹], isFactorization_singleton lam ((inv_mem_C_iff lam x).mpr hx)⟩
  | one => exact ⟨[], isFactorization_nil lam n⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w₁, hw₁⟩ := hx
    obtain ⟨w₂, hw₂⟩ := hy
    exact ⟨w₁ ++ w₂, hw₁.append hw₂⟩

theorem exists_factorization (lam : CycleType) {n : ℕ} (g : G lam n) :
    ∃ w, IsFactorization lam (g : SymmetricGroup n) w :=
  exists_factorization_of_mem lam g.property

theorem factorizationLengths_nonempty (lam : CycleType) {n : ℕ} (g : G lam n) :
    (factorizationLengths lam (g : SymmetricGroup n)).Nonempty := by
  obtain ⟨w, hw⟩ := exists_factorization lam g
  exact ⟨w.length, w, hw, rfl⟩

theorem exists_shortest_factorization (lam : CycleType) {n : ℕ} (g : G lam n) :
    ∃ w, IsFactorization lam (g : SymmetricGroup n) w ∧ w.length = L lam g :=
  Nat.sInf_mem (factorizationLengths_nonempty lam g)

theorem L_le_length {lam : CycleType} {n : ℕ} {g : G lam n}
    {w : List (SymmetricGroup n)} (hw : IsFactorization lam (g : SymmetricGroup n) w) :
    L lam g ≤ w.length :=
  Nat.sInf_le ⟨w, hw, rfl⟩

theorem L_le_iff (lam : CycleType) {n : ℕ} (g : G lam n) (k : ℕ) :
    L lam g ≤ k ↔ ∃ w, IsFactorization lam (g : SymmetricGroup n) w ∧ w.length ≤ k := by
  constructor
  · intro hk
    obtain ⟨w, hw, hlen⟩ := exists_shortest_factorization lam g
    exact ⟨w, hw, hlen ▸ hk⟩
  · rintro ⟨w, hw, hlen⟩
    exact (L_le_length hw).trans hlen

@[simp]
theorem L_eq_zero_iff (lam : CycleType) {n : ℕ} (g : G lam n) :
    L lam g = 0 ↔ g = 1 := by
  constructor
  · intro hg
    obtain ⟨w, hw, hlen⟩ := exists_shortest_factorization lam g
    have hw0 : w = [] := List.length_eq_zero_iff.mp (hlen.trans hg)
    apply Subtype.ext
    simpa [hw0] using hw.2.symm
  · rintro rfl
    exact Nat.eq_zero_of_le_zero
      (L_le_length (g := (1 : G lam n)) (w := []) (isFactorization_nil lam n))

@[simp]
theorem L_one (lam : CycleType) (n : ℕ) : L lam (1 : G lam n) = 0 :=
  (L_eq_zero_iff lam 1).mpr rfl

theorem L_mul_le (lam : CycleType) {n : ℕ} (g₁ g₂ : G lam n) :
    L lam (g₁ * g₂) ≤ L lam g₁ + L lam g₂ := by
  obtain ⟨w₁, hw₁, hlen₁⟩ := exists_shortest_factorization lam g₁
  obtain ⟨w₂, hw₂, hlen₂⟩ := exists_shortest_factorization lam g₂
  simpa [List.length_append, hlen₁, hlen₂] using
    L_le_length (g := g₁ * g₂) (hw₁.append hw₂)

theorem L_inv_le (lam : CycleType) {n : ℕ} (g : G lam n) : L lam g⁻¹ ≤ L lam g := by
  obtain ⟨w, hw, hlen⟩ := exists_shortest_factorization lam g
  simpa [hlen] using L_le_length (g := g⁻¹) hw.inverse

@[simp]
theorem L_inv (lam : CycleType) {n : ℕ} (g : G lam n) : L lam g⁻¹ = L lam g := by
  apply le_antisymm (L_inv_le lam g)
  simpa using L_inv_le lam g⁻¹

theorem L_le_D (lam : CycleType) {n : ℕ} (g : G lam n) : L lam g ≤ D lam n := by
  apply le_csSup (Set.finite_range (L lam (n := n))).bddAbove
  exact Set.mem_range_self g

theorem exists_length_eq_D (lam : CycleType) (n : ℕ) :
    ∃ g : G lam n, L lam g = D lam n :=
  (Set.range_nonempty (L lam (n := n))).csSup_mem (Set.finite_range _)

theorem D_le_iff (lam : CycleType) (n k : ℕ) :
    D lam n ≤ k ↔ ∀ g : G lam n, L lam g ≤ k := by
  constructor
  · intro hk g
    exact (L_le_D lam g).trans hk
  · intro hk
    obtain ⟨g, hg⟩ := exists_length_eq_D lam n
    exact hg ▸ hk g

end ConjugacyDiametersPORC
