import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') [HasPrincipalDivisors K F'] [HasPrincipalDivisors K F''] (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F) : Divisor.pullbackAlong χ hχ (Divisor.pullbackAlong φ hφ D) = Divisor.pullbackAlong (χ.comp φ) hχφ D := by
  ext W
  rw [Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply,
    AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ,
    AlgebraicCurve.Place.ramificationIndexAlong_comp φ χ hφ hχ hχφ]
  push_cast
  ring
