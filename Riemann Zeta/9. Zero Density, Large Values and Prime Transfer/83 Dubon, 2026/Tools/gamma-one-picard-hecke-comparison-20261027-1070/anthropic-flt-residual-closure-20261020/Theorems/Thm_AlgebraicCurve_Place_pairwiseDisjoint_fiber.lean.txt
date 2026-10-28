import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_pairwiseDisjoint_fiber

open AlgebraicCurve
theorem AlgebraicCurve.Place.pairwiseDisjoint_fiber {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] (s : Finset (Place K F)) : Set.PairwiseDisjoint (s : Set (Place K F)) (fun v : Place K F => v.fiber F') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_pairwiseDisjoint_fiber.solution
