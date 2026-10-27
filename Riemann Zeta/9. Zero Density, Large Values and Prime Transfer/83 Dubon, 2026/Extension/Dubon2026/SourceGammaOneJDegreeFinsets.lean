import Dubon2026.SourceGammaOneCuspPoleDegree

/-! DUB-17/18 -> actual Gamma1 real period surjectivity -> genus lower
bound. Reindex the existing actual j-fiber and j-pole degree sums over
finite sets, as required by the canonical-divisor contribution bound. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve IntermediateField
open scoped MatrixGroups IntermediateField
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
include hT

theorem sum_j_fiber_orders_finset (c : ℂ)
    (S : Finset (Place ℂ (functionFieldOver Γ ℂ)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c)) :
    (∑ v ∈ S, v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c)) =
      (Module.finrank ℂ⟮jCoordinateOver Γ ℂ⟯ (functionFieldOver Γ ℂ) : ℤ) := by
  have h := sum_j_fiber_orders_eq_finrank hT c
  have he : {v : Place ℂ (functionFieldOver Γ ℂ) |
      0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c)} = (S : Set _) :=
    Set.ext fun v => (hS v).symm
  have h' := (finsum_set_coe_eq_finsum_mem (f := fun v : Place ℂ (functionFieldOver Γ ℂ) =>
    v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c))
    {v | 0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c)}).symm.trans h
  rw [he, finsum_mem_coe_finset] at h'
  exact h'

theorem sum_j_pole_orders_finset
    (S : Finset (Place ℂ (functionFieldOver Γ ℂ)))
    (hS : ∀ v, v ∈ S ↔ v.ord (jCoordinateOver Γ ℂ) < 0) :
    (∑ v ∈ S, -v.ord (jCoordinateOver Γ ℂ)) = (Module.finrank ℂ⟮jCoordinateOver Γ ℂ⟯ (functionFieldOver Γ ℂ) : ℤ) := by
  have h := sum_j_pole_orders_eq_finrank hT
  have he : {v : Place ℂ (functionFieldOver Γ ℂ) | v.ord (jCoordinateOver Γ ℂ) < 0} = (S : Set _) :=
    Set.ext fun v => (hS v).symm
  have h' := (finsum_set_coe_eq_finsum_mem (f := fun v : Place ℂ (functionFieldOver Γ ℂ) =>
    -v.ord (jCoordinateOver Γ ℂ)) {v | v.ord (jCoordinateOver Γ ℂ) < 0}).symm.trans h
  rw [he, finsum_mem_coe_finset] at h'
  exact h'

end
end Dubon2026.SourceFunctionField.GammaOne
