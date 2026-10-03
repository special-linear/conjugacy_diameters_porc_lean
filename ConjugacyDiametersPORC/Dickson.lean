import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Minimal

/-!
# Lemma 3: Dickson's lemma

The order on a finite tuple of natural numbers is coordinatewise. Every subset
has finitely many minimal elements, and each member dominates a minimal member.
-/

namespace ConjugacyDiametersPORC

/-- **Lemma 3.** Finiteness and domination of the coordinatewise minimal elements. -/
theorem lemma3 {ι : Type*} [Finite ι] (X : Set (ι → ℕ)) :
    {x | Minimal (· ∈ X) x}.Finite ∧
      ∀ x ∈ X, ∃ y ≤ x, Minimal (· ∈ X) y := by
  constructor
  · exact WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  · exact fun x hx => exists_minimal_le_of_wellFoundedLT (· ∈ X) x hx

end ConjugacyDiametersPORC
