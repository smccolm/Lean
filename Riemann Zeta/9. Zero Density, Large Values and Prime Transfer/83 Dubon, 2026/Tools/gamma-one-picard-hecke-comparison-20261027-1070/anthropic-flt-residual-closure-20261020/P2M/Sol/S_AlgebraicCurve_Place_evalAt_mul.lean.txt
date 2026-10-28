import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_evalAt_mul

open IsLocalRing AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) : v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl
