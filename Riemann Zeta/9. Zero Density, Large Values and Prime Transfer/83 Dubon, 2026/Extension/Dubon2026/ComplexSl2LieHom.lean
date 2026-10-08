import Dubon2026.ComplexSl2Basis
import Mathlib.Algebra.Lie.OfAssociative

/-! # Faithful extension of three actual infinitesimals to the genuine complex matrix Lie algebra -/

namespace Dubon2026

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The actual three matrix coordinates give the linear extension of the three original generators. -/
def complexSl2LinearMap (A U F : R) : ComplexSl2 →ₗ[ℂ] R where
  toFun x := (2 * x.val 0 0) • A + x.val 0 1 • U + x.val 1 0 • F
  map_add' x y := by
    change (2 * (x.val 0 0 + y.val 0 0)) • A + (x.val 0 1 + y.val 0 1) • U +
      (x.val 1 0 + y.val 1 0) • F =
      ((2 * x.val 0 0) • A + x.val 0 1 • U + x.val 1 0 • F) +
      ((2 * y.val 0 0) • A + y.val 0 1 • U + y.val 1 0 • F)
    simp only [mul_add, add_smul]
    abel
  map_smul' c x := by
    change (2 * (c * x.val 0 0)) • A + (c * x.val 0 1) • U + (c * x.val 1 0) • F =
      c • ((2 * x.val 0 0) • A + x.val 0 1 • U + x.val 1 0 • F)
    module

/-- The exact linear extension recovers the actual half-diagonal generator. -/
theorem complexSl2LinearMap_A (A U F : R) : complexSl2LinearMap A U F complexSl2A = A := by
  norm_num [complexSl2LinearMap, complexSl2A]

/-- The exact linear extension recovers the actual upper generator. -/
theorem complexSl2LinearMap_U (A U F : R) : complexSl2LinearMap A U F complexSl2U = U := by
  norm_num [complexSl2LinearMap, complexSl2U]

/-- The exact linear extension recovers the actual lower generator. -/
theorem complexSl2LinearMap_F (A U F : R) : complexSl2LinearMap A U F complexSl2F = F := by
  norm_num [complexSl2LinearMap, complexSl2F]

/-- Proved original three-generator commutators force preservation of every actual matrix Lie bracket. -/
theorem complexSl2LinearMap_lie (A U F : R)
    (hAU : A * U - U * A = U) (hAF : A * F - F * A = -F)
    (hUF : U * F - F * U = A + A) (x y : ComplexSl2) :
    complexSl2LinearMap A U F ⁅x, y⁆ = ⁅complexSl2LinearMap A U F x, complexSl2LinearMap A U F y⁆ := by
  have hAU' : ⁅A, U⁆ = U := hAU
  have hAF' : ⁅A, F⁆ = -F := hAF
  have hUF' : ⁅U, F⁆ = A + A := hUF
  have hB (a b c d e f : ℂ) :
      complexSl2LinearMap A U F ⁅a • complexSl2A + b • complexSl2U + c • complexSl2F,
        d • complexSl2A + e • complexSl2U + f • complexSl2F⁆ =
      ⁅complexSl2LinearMap A U F (a • complexSl2A + b • complexSl2U + c • complexSl2F),
        complexSl2LinearMap A U F (d • complexSl2A + e • complexSl2U + f • complexSl2F)⁆ := by
    simp only [map_add, map_smul, add_lie, lie_add, smul_lie, lie_smul, lie_self,
      complexSl2_bracket_A_U, complexSl2_bracket_A_F, complexSl2_bracket_U_F,
      ← lie_skew complexSl2U complexSl2A, ← lie_skew complexSl2F complexSl2A,
      ← lie_skew complexSl2F complexSl2U, map_neg, map_zero,
      complexSl2LinearMap_A, complexSl2LinearMap_U, complexSl2LinearMap_F,
      hAU', hAF', hUF', ← lie_skew U A, ← lie_skew F A, ← lie_skew F U, smul_zero]
  simpa only [← complexSl2_decomposition x, ← complexSl2_decomposition y] using
    hB (2 * x.val 0 0) (x.val 0 1) (x.val 1 0) (2 * y.val 0 0) (y.val 0 1) (y.val 1 0)

/-- The original three operators with proved commutators define a genuine homomorphism out of actual traceless complex matrices. -/
def complexSl2LieHom (A U F : R)
    (hAU : A * U - U * A = U) (hAF : A * F - F * A = -F)
    (hUF : U * F - F * U = A + A) : ComplexSl2 →ₗ⁅ℂ⁆ R :=
  { complexSl2LinearMap A U F with
    map_lie' := fun {x y} => complexSl2LinearMap_lie A U F hAU hAF hUF x y }

/-- The genuine real matrix tangent is sent to precisely its three infinitesimal coordinate contributions. -/
theorem complexSl2LinearMap_real_tangent (A U F : R) (a b d : ℝ) :
    complexSl2LinearMap A U F (complexSl2OfRealTangent a b d) =
      (b : ℂ) • F + ((2 * a : ℝ) : ℂ) • A + (d : ℂ) • U := by
  change (2 * (a : ℂ)) • A + (d : ℂ) • U + (b : ℂ) • F =
    (b : ℂ) • F + ((2 * a : ℝ) : ℂ) • A + (d : ℂ) • U
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  abel

end
end Dubon2026
