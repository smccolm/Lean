import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_support_pullback_subset

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [DecidableEq (Place K F')] (E : Divisor K F) : (Divisor.pullback F' E).support ⊆ E.support.biUnion (fun v => v.fiber F') := by
  classical
  intro w hw
  exact Finset.mem_biUnion.mpr ⟨w.restrict F,
    restrict_mem_support_of_mem_support_pullback hw, w.restrict_mem_fiber⟩
