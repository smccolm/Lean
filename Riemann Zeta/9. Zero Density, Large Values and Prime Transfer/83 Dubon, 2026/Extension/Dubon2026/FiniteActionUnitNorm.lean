import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Topology.Algebra.Group.Basic

/-! # The original finite action norm and its topology -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable (G U : Type) [Group G] [Fintype G] [CommGroup U] [MulDistribMulAction G U]

/-- The literal product of every original action translate. -/
def finiteActionUnitNorm : U →* U where
  toFun u := ∏ g : G, g • u
  map_one' := by simp
  map_mul' u v := by simp only [smul_mul', Finset.prod_mul_distrib]

/-- The original action norm is invariant by reindexing its actual finite
product under original left multiplication. -/
theorem finiteActionUnitNorm_invariant (h : G) (u : U) :
    h • finiteActionUnitNorm G U u = finiteActionUnitNorm G U u := by
  change (MulDistribMulAction.toMonoidHom U h) (∏ g : G, g • u) = _
  rw [map_prod]
  change (∏ g : G, h • (g • u)) = ∏ g : G, g • u
  simp only [← mul_smul]
  exact Equiv.prod_comp (Equiv.mulLeft h) (fun g : G => g • u)

/-- Every original invariant subgroup is preserved by the actual action norm. -/
theorem finiteActionUnitNorm_mem (S : Subgroup U)
    (hS : ∀ (g : G) (u : U), u ∈ S → g • u ∈ S) {u : U} (hu : u ∈ S) :
    finiteActionUnitNorm G U u ∈ S := by
  classical
  exact S.prod_mem (fun g _ => hS g u hu)

/-- Continuity of each original action translate gives continuity of the
literal finite product norm in the original unit topology. -/
theorem finiteActionUnitNorm_continuous [TopologicalSpace U] [IsTopologicalGroup U]
    (hcont : ∀ g : G, Continuous (fun u : U => g • u)) :
    Continuous (finiteActionUnitNorm G U) := by
  classical
  exact continuous_finsetProd _ (fun g _ => hcont g)

end
end Dubon2026
