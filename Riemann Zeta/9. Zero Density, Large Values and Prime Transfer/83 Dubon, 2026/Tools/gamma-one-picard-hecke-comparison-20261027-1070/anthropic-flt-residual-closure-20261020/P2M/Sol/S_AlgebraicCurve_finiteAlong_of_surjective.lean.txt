import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
namespace P2MW.S_AlgebraicCurve_finiteAlong_of_surjective

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : Function.Surjective φ) : FiniteAlong K φ := by
  letI := algebraAlong φ
  exact Module.Finite.of_surjective (Algebra.linearMap F F') hφ
