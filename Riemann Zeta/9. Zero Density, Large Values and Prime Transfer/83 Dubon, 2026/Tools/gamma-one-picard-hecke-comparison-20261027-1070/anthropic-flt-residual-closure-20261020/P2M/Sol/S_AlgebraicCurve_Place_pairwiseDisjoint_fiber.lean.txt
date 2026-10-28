import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_pairwiseDisjoint_fiber

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] (s : Finset (Place K F)) : Set.PairwiseDisjoint (s : Set (Place K F)) (fun v : Place K F => v.fiber F') := by
  intro v₁ _ v₂ _ hne
  refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => ?_
  exact hne ((Place.mem_fiber.mp hw₁).symm.trans (Place.mem_fiber.mp hw₂))
