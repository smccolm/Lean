import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance
import P2M.Util
namespace P2MW.S_AlgebraicCurve_hasCanonicalLocalResidueK

open AlgebraicCurve

theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F] :
    AlgebraicCurve.HasCanonicalLocalResidueK K F :=
  inferInstance
