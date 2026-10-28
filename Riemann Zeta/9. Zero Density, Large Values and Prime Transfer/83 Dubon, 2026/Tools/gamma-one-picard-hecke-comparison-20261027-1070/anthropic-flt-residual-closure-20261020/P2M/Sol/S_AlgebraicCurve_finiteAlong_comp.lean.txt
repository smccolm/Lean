import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
namespace P2MW.S_AlgebraicCurve_finiteAlong_comp

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : FiniteAlong K φ) (hχ : FiniteAlong K χ) : FiniteAlong K (χ.comp φ) := by
  letI := algebraAlong φ
  letI := algebraAlong χ
  letI := algebraAlong (χ.comp φ)
  haveI : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite F F' := hφ
  haveI : Module.Finite F' F'' := hχ
  exact Module.Finite.trans F' F''
