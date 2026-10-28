import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
namespace P2MW.S_AlgebraicCurve_separableAlong_of_charZero

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁] [CharZero F] (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral) : SeparableAlong K φ := by
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  exact Algebra.IsSeparable.of_integral F F₁
