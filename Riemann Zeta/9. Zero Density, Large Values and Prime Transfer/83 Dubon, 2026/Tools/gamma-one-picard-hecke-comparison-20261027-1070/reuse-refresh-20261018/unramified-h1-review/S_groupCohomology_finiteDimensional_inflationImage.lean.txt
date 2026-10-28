import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Theorems.Thm_groupCohomology_finiteDimensional_H1_of_finite
import P2M.Util
namespace P2MW.S_groupCohomology_finiteDimensional_inflationImage

open CategoryTheory Module groupCohomology

universe u

theorem solution {k : Type u} [Field k] {G : Type u} [Group G] (M : Rep k G) (S : Subgroup G) [S.Normal]
    [S.FiniteIndex] [FiniteDimensional k M] :
    FiniteDimensional k (inflationImage M S) := by
  haveI : FiniteDimensional k (M.quotientToInvariants S) :=
    inferInstanceAs (FiniteDimensional k (Representation.invariants (M.ρ.comp S.subtype)))
  haveI : FiniteDimensional k (H1 (M.quotientToInvariants S)) := finiteDimensional_H1_of_finite _
  exact inferInstanceAs (FiniteDimensional k (LinearMap.range (inflation M S).hom))
