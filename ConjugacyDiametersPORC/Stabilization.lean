import ConjugacyDiametersPORC.PORC
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Stabilization of the integer diameter defects

A bounded nonincreasing integer sequence stabilizes. Applying this fact on each
of the finitely many residue classes turns an upper recurrence into equality.
-/

namespace ConjugacyDiametersPORC

theorem bounded_antitone_int_stabilizes (F : ℕ → ℤ) (hF : Antitone F)
    (b : ℤ) (hb : ∀ k, b ≤ F k) : ∃ K, ∀ k, K ≤ k → F k = F K := by
  let H : ℕ → ℕ := fun k => (F k - b).toNat
  have hH : Antitone H := by
    intro i j hij
    exact Int.toNat_le_toNat (sub_le_sub_right (hF hij) b)
  obtain ⟨K, hK⟩ := WellFoundedLT.antitone_chain_condition hH
  refine ⟨K, fun k hk => ?_⟩
  have h := hK k hk
  have hi : 0 ≤ F k - b := sub_nonneg.mpr (hb k)
  have hj : 0 ≤ F K - b := sub_nonneg.mpr (hb K)
  have he : F K - b = F k - b := by
    simpa only [H, Int.toNat_of_nonneg hj, Int.toNat_of_nonneg hi] using
      congrArg (fun n : ℕ => (n : ℤ)) h
  omega

theorem eventually_nonincreasing_int_stabilizes (F : ℕ → ℤ) (N : ℕ)
    (hstep : ∀ k, N ≤ k → F (k + 1) ≤ F k)
    (b : ℤ) (hb : ∀ k, N ≤ k → b ≤ F k) :
    ∃ K, N ≤ K ∧ ∀ k, K ≤ k → F (k + 1) = F k := by
  have hmono : Antitone (fun k => F (k + N)) := by
    apply antitone_nat_of_succ_le
    intro k
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep (k + N) (by omega)
  obtain ⟨K, hK⟩ := bounded_antitone_int_stabilizes (fun k => F (k + N)) hmono b
    (fun k => hb (k + N) (by omega))
  refine ⟨K + N, by omega, fun k hk => ?_⟩
  have h₁ := hK (k - N) (by omega)
  have h₂ := hK (k - N + 1) (by omega)
  have hkN : N ≤ k := by omega
  have he₁ : k - N + N = k := Nat.sub_add_cancel hkN
  have he₂ : k - N + 1 + N = k + 1 := by omega
  rw [he₁] at h₁
  rw [he₂] at h₂
  exact h₂.trans h₁.symm

/-- Residue-class stabilization used to assemble eventual affine PORC.

The lower-bound hypothesis is expressed directly for the integer defects
`a (u + kP) - kq`; the diameter lower certificate supplies these bounds.
-/
theorem eventual_recurrence_of_bounded_defects (a : ℕ → ℤ) (P q N : ℕ)
    (hP : 0 < P)
    (hstep : ∀ n, N ≤ n → a (n + P) ≤ a n + (q : ℤ))
    (hbound : ∀ u : Fin P, ∃ b : ℤ, ∀ k, N ≤ k →
      b ≤ a (u.val + k * P) - (k : ℤ) * (q : ℤ)) :
    ∃ N' : ℕ, 0 < N' ∧ ∀ n, N' ≤ n → a (n + P) = a n + (q : ℤ) := by
  classical
  let F (u : Fin P) (k : ℕ) : ℤ := a (u.val + k * P) - (k : ℤ) * (q : ℤ)
  have hres : ∀ u : Fin P, ∃ K, ∀ k, K ≤ k → F u (k + 1) = F u k := by
    intro u
    obtain ⟨b, hb⟩ := hbound u
    have hF : ∀ k, N ≤ k → F u (k + 1) ≤ F u k := by
      intro k hk
      have hn : N ≤ u.val + k * P :=
        hk.trans ((Nat.le_mul_of_pos_right k hP).trans (Nat.le_add_left _ _))
      have h := hstep (u.val + k * P) hn
      dsimp [F]
      rw [Nat.add_mul, Nat.one_mul]
      simp only [add_mul, one_mul, ← Nat.add_assoc]
      omega
    obtain ⟨K, _, hK⟩ := eventually_nonincreasing_int_stabilizes (F u) N hF b hb
    exact ⟨K, hK⟩
  choose K hK using hres
  let Kmax := Finset.univ.sup K
  let N' := (Kmax + 1) * P
  refine ⟨N', Nat.mul_pos (Nat.succ_pos _) hP, ?_⟩
  intro n hn
  let u : Fin P := ⟨n % P, Nat.mod_lt n hP⟩
  let k := n / P
  have hlarge : Kmax + 1 ≤ k := (Nat.le_div_iff_mul_le hP).mpr hn
  have hKu : K u ≤ k := (Finset.le_sup (Finset.mem_univ u)).trans (by omega)
  have he := hK u k hKu
  have hn₀ : u.val + k * P = n := by
    simpa only [u, k, Nat.mul_comm] using Nat.mod_add_div n P
  have hn₁ : u.val + (k + 1) * P = n + P := by
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, hn₀]
  change a (u.val + (k + 1) * P) - ((k + 1 : ℕ) : ℤ) * (q : ℤ) =
    a (u.val + k * P) - (k : ℤ) * (q : ℤ) at he
  rw [hn₁, hn₀] at he
  simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at he
  omega

/-- Existential affine PORC from stabilization with the specified period. -/
theorem eventuallyAffinePORC_of_bounded_defects (a : ℕ → ℤ) (P q N : ℕ)
    (hP : 0 < P) (hq : 0 < q)
    (hstep : ∀ n, N ≤ n → a (n + P) ≤ a n + (q : ℤ))
    (hbound : ∀ u : Fin P, ∃ b : ℤ, ∀ k, N ≤ k →
      b ≤ a (u.val + k * P) - (k : ℤ) * (q : ℤ)) :
    EventuallyAffinePORC a := by
  obtain ⟨N', hN', he⟩ := eventual_recurrence_of_bounded_defects a P q N hP hstep hbound
  exact ⟨P, q, N', hP, hq, hN', he⟩

/-- A linear lower certificate and a matching upper recurrence imply stabilization.

The rational slope satisfies `α P = q`, so subtracting `kq` leaves a uniform
lower bound in each residue class.
-/
theorem eventual_recurrence_of_bounds (a : ℕ → ℕ) (P q N : ℕ)
    (hP : 0 < P) (α γ : ℚ) (hα : α * (P : ℚ) = (q : ℚ))
    (hstep : ∀ n, N ≤ n → a (n + P) ≤ a n + q)
    (hlower : ∀ n, N ≤ n → α * (n : ℚ) - γ ≤ (a n : ℚ)) :
    ∃ N' : ℕ, 0 < N' ∧ ∀ n, N' ≤ n → a (n + P) = a n + q := by
  have hex : ∃ N' : ℕ, 0 < N' ∧ ∀ n, N' ≤ n →
      (a (n + P) : ℤ) = (a n : ℤ) + (q : ℤ) := by
    apply eventual_recurrence_of_bounded_defects (fun n => (a n : ℤ)) P q N hP
    · intro n hn
      exact_mod_cast hstep n hn
    · intro u
      refine ⟨⌊α * (u.val : ℚ) - γ⌋, fun k hk => ?_⟩
      have hn : N ≤ u.val + k * P :=
        hk.trans ((Nat.le_mul_of_pos_right k hP).trans (Nat.le_add_left _ _))
      have h := hlower (u.val + k * P) hn
      have he : α * ((u.val + k * P : ℕ) : ℚ) - γ =
          α * (u.val : ℚ) - γ + (k : ℚ) * (q : ℚ) := by
        rw [Nat.cast_add, Nat.cast_mul, ← hα]
        ring
      rw [he] at h
      have hb : α * (u.val : ℚ) - γ ≤
          (a (u.val + k * P) : ℚ) - (k : ℚ) * (q : ℚ) := by linarith
      have hf := (Int.floor_le (α * (u.val : ℚ) - γ)).trans hb
      exact_mod_cast hf
  obtain ⟨N', hN', he⟩ := hex
  refine ⟨N', hN', fun n hn => ?_⟩
  exact_mod_cast he n hn

theorem eventuallyAffinePORC_of_bounds (a : ℕ → ℕ) (P q N : ℕ)
    (hP : 0 < P) (hq : 0 < q) (α γ : ℚ) (hα : α * (P : ℚ) = (q : ℚ))
    (hstep : ∀ n, N ≤ n → a (n + P) ≤ a n + q)
    (hlower : ∀ n, N ≤ n → α * (n : ℚ) - γ ≤ (a n : ℚ)) :
    EventuallyAffinePORC (fun n => (a n : ℤ)) := by
  obtain ⟨N', hN', he⟩ := eventual_recurrence_of_bounds a P q N hP α γ hα hstep hlower
  refine ⟨P, q, N', hP, hq, hN', fun n hn => ?_⟩
  change (a (n + P) : ℤ) = (a n : ℤ) + (q : ℤ)
  exact_mod_cast he n hn

end ConjugacyDiametersPORC
