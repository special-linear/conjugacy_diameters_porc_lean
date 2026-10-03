import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Basic.Real.Basic

/-!
# Rationality of a uniquely determined solution

An injective rational matrix has a rational left inverse. Thus a real solution
to that matrix with rational right-hand side has rational coordinates.
-/

namespace ConjugacyDiametersPORC

open Matrix

theorem rational_solution_of_injective {m n : Type*} [Finite m] [Fintype n]
    (A : Matrix m n ℚ) (b : m → ℚ) (x : n → ℝ)
    (hA : Function.Injective (A.map (Rat.castHom ℝ)).mulVec)
    (hx : (A.map (Rat.castHom ℝ)).mulVec x = fun i => (b i : ℝ)) :
    ∃ q : n → ℚ, x = fun j => (q j : ℝ) := by
  classical
  let _ := Fintype.ofFinite m
  let f : ℚ →+* ℝ := Rat.castHom ℝ
  have hQ : Function.Injective A.mulVec := by
    intro u v huv
    have hR : (A.map f).mulVec (f ∘ u) = (A.map f).mulVec (f ∘ v) := by
      ext i
      rw [← RingHom.map_mulVec, ← RingHom.map_mulVec, huv]
    have he := hA hR
    funext j
    exact Rat.cast_injective (congrFun he j)
  obtain ⟨g, hg⟩ := A.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hQ)
  let B : Matrix n m ℚ := LinearMap.toMatrix' g
  have hBA : B * A = 1 := by
    have he := congrArg LinearMap.toMatrix' hg
    have hMA : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'_toLin' A
    rw [LinearMap.toMatrix'_comp, hMA, LinearMap.toMatrix'_id] at he
    exact he
  have hBAR : B.map f * A.map f = 1 := by
    rw [← Matrix.map_mul, hBA]
    exact Matrix.map_one f (map_zero f) (map_one f)
  have hleft : (B.map f).mulVec (fun i => (b i : ℝ)) = x := by
    rw [← hx, Matrix.mulVec_mulVec, hBAR, Matrix.one_mulVec]
  refine ⟨B.mulVec b, ?_⟩
  rw [← hleft]
  ext j
  exact (RingHom.map_mulVec f B b j).symm

end ConjugacyDiametersPORC
