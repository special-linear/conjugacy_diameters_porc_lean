import ConjugacyDiametersPORC.CycleType
import Mathlib.Order.Lattice.Nat

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
subgroup membership and inverse closure of `C_{λ,n}`; that API is future proof work.
In particular, the empty-set default of `sInf : Set ℕ → ℕ` is never needed here.
-/
noncomputable def L (lam : CycleType) {n : ℕ} (g : G lam n) : ℕ :=
  sInf (factorizationLengths lam (g : SymmetricGroup n))

/-- `D_n = max_{g ∈ G_n} L_n(g)`, the Cayley-graph diameter.

The range is finite and nonempty because `G_n` is a finite group. Thus its natural
supremum is a maximum. Translation invariance identifies this maximum distance
from the identity with the diameter; those correctness lemmas remain to be proved.
-/
noncomputable def D (lam : CycleType) (n : ℕ) : ℕ :=
  sSup (Set.range (L lam (n := n)))

end ConjugacyDiametersPORC
