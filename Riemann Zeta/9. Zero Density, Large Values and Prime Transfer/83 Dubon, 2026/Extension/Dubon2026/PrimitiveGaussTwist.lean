import Dubon2026.CuspSelfTwists
import Mathlib.Analysis.Fourier.ZMod

/-! # Primitive Gauss sums for actual coefficient twists -/

namespace Dubon2026

open Finset

noncomputable section

/-- The actual standard Gauss sum of a primitive Dirichlet character cannot vanish. -/
theorem primitive_character_gaussSum_ne_zero {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro hz
  have hfourier : ZMod.dft (fun a => χ a) = (0 : ZMod D → ℂ) := by
    ext a
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, hz, mul_zero]
    rfl
  have hzero : (fun a => χ a) = (0 : ZMod D → ℂ) := ZMod.dft.injective (by simpa using hfourier)
  have hone := congrFun hzero 1
  simp only [map_one, Pi.zero_apply, one_ne_zero] at hone

/-- A primitive quadratic character is its normalized positive-sign finite Fourier sum. -/
theorem primitive_quadratic_gauss_inversion {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (n : ZMod D) :
    (gaussSum χ ZMod.stdAddChar)⁻¹ *
      (∑ a : ZMod D, χ a * ZMod.stdAddChar (n * a)) = χ n := by
  have hg := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ n
  rw [hq.inv] at hg
  change (∑ a : ZMod D, χ a * ZMod.stdAddChar (n * a)) =
    χ n * gaussSum χ ZMod.stdAddChar at hg
  rw [hg]
  field_simp [primitive_character_gaussSum_ne_zero χ hχ]

end
end Dubon2026
