import Dubon2026.CompactSl2Basis
import Mathlib.Algebra.Lie.OfAssociative

/-! # Exact Lie extension from the original compact matrix basis -/

namespace Dubon2026

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℂ R]

/-- The genuine compact matrix coordinates extend three original operators complex linearly. -/
def compactSl2LinearMap (H E F : R) : ComplexSl2 →ₗ[ℂ] R where
  toFun x := (Complex.I / 2 * (x.val 0 1 - x.val 1 0)) • H +
    (x.val 0 0 - Complex.I / 2 * (x.val 0 1 + x.val 1 0)) • E +
    (x.val 0 0 + Complex.I / 2 * (x.val 0 1 + x.val 1 0)) • F
  map_add' x y := by
    change (Complex.I / 2 * ((x.val 0 1 + y.val 0 1) - (x.val 1 0 + y.val 1 0))) • H +
      ((x.val 0 0 + y.val 0 0) - Complex.I / 2 * ((x.val 0 1 + y.val 0 1) + (x.val 1 0 + y.val 1 0))) • E +
      ((x.val 0 0 + y.val 0 0) + Complex.I / 2 * ((x.val 0 1 + y.val 0 1) + (x.val 1 0 + y.val 1 0))) • F = _
    module
  map_smul' c x := by
    change (Complex.I / 2 * (c * x.val 0 1 - c * x.val 1 0)) • H +
      (c * x.val 0 0 - Complex.I / 2 * (c * x.val 0 1 + c * x.val 1 0)) • E +
      (c * x.val 0 0 + Complex.I / 2 * (c * x.val 0 1 + c * x.val 1 0)) • F =
        c • ((Complex.I / 2 * (x.val 0 1 - x.val 1 0)) • H +
          (x.val 0 0 - Complex.I / 2 * (x.val 0 1 + x.val 1 0)) • E +
          (x.val 0 0 + Complex.I / 2 * (x.val 0 1 + x.val 1 0)) • F)
    module

/-- The extension retains the original compact Cartan operator. -/
theorem compactSl2LinearMap_H (H E F : R) : compactSl2LinearMap H E F compactSl2H = H := by
  norm_num [compactSl2LinearMap, compactSl2H, complexSl2U, complexSl2F]
  ring_nf
  norm_num [Complex.I_sq]

/-- The extension retains the original compact raising operator. -/
theorem compactSl2LinearMap_E (H E F : R) : compactSl2LinearMap H E F compactSl2E = E := by
  norm_num [compactSl2LinearMap, compactSl2E, complexSl2A, complexSl2U, complexSl2F]
  ring_nf
  norm_num [Complex.I_sq]

/-- The extension retains the original compact lowering operator. -/
theorem compactSl2LinearMap_F (H E F : R) : compactSl2LinearMap H E F compactSl2F = F := by
  norm_num [compactSl2LinearMap, compactSl2F, complexSl2A, complexSl2U, complexSl2F]
  ring_nf
  norm_num [Complex.I_sq]

/-- Original compact sl2 commutators ensure preservation of every original matrix Lie bracket. -/
theorem compactSl2LinearMap_lie (H E F : R)
    (hEF : E * F - F * E = H) (hHE : H * E - E * H = (2 : ℂ) • E)
    (hHF : H * F - F * H = -((2 : ℂ) • F)) (x y : ComplexSl2) :
    compactSl2LinearMap H E F ⁅x, y⁆ = ⁅compactSl2LinearMap H E F x, compactSl2LinearMap H E F y⁆ := by
  have hEF' : ⁅E, F⁆ = H := hEF
  have hHE' : ⁅H, E⁆ = (2 : ℂ) • E := hHE
  have hHF' : ⁅H, F⁆ = -((2 : ℂ) • F) := hHF
  have hB (a b c d e f : ℂ) :
      compactSl2LinearMap H E F ⁅a • compactSl2H + b • compactSl2E + c • compactSl2F,
        d • compactSl2H + e • compactSl2E + f • compactSl2F⁆ =
      ⁅compactSl2LinearMap H E F (a • compactSl2H + b • compactSl2E + c • compactSl2F),
        compactSl2LinearMap H E F (d • compactSl2H + e • compactSl2E + f • compactSl2F)⁆ := by
    simp only [map_add, map_smul, add_lie, lie_add, smul_lie, lie_smul, lie_self,
      compactSl2_bracket_H_E, compactSl2_bracket_H_F, compactSl2_bracket_E_F,
      ← lie_skew compactSl2E compactSl2H, ← lie_skew compactSl2F compactSl2H,
      ← lie_skew compactSl2F compactSl2E, map_neg, map_zero,
      compactSl2LinearMap_H, compactSl2LinearMap_E, compactSl2LinearMap_F,
      hEF', hHE', hHF', ← lie_skew E H, ← lie_skew F H, ← lie_skew F E, smul_zero]
  simpa only [← compactSl2_decomposition x, ← compactSl2_decomposition y] using
    hB (Complex.I / 2 * (x.val 0 1 - x.val 1 0))
      (x.val 0 0 - Complex.I / 2 * (x.val 0 1 + x.val 1 0))
      (x.val 0 0 + Complex.I / 2 * (x.val 0 1 + x.val 1 0))
      (Complex.I / 2 * (y.val 0 1 - y.val 1 0))
      (y.val 0 0 - Complex.I / 2 * (y.val 0 1 + y.val 1 0))
      (y.val 0 0 + Complex.I / 2 * (y.val 0 1 + y.val 1 0))

/-- The exact compact matrix basis and proved original commutators give a genuine matrix Lie homomorphism. -/
def compactSl2LieHom (H E F : R)
    (hEF : E * F - F * E = H) (hHE : H * E - E * H = (2 : ℂ) • E)
    (hHF : H * F - F * H = -((2 : ℂ) • F)) : ComplexSl2 →ₗ⁅ℂ⁆ R :=
  { compactSl2LinearMap H E F with
    map_lie' := fun {x y} => compactSl2LinearMap_lie H E F hEF hHE hHF x y }

end
end Dubon2026
