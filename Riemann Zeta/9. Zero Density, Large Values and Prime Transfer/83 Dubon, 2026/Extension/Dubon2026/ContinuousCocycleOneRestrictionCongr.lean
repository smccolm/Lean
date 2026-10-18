import Dubon2026.ContinuousRepresentationRestriction
import Dubon2026.ContinuousCohomologyCoefficientCongr

/-! Restriction followed by a proved equality of the actual coefficient
actions. The literal value formula is used for DUB-17's original local
Cartier cocycle without unfolding the arithmetic coefficient construction. -/
namespace Dubon2026
noncomputable section

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (j : H →* G) (hj : Continuous j) (σ : Representation R H A) (hσ : A.ρ.comp j = σ)

/-- Restrict an original continuous cocycle and identify its coefficient action. -/
def continuousCocycleOneRestrictionCongr :
    continuousRepresentationCocyclesOne A →ₗ[R]
      continuousRepresentationCocyclesOne (Rep.of σ) where
  toFun c := ⟨⟨fun g => c.val (j g), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    change c.val (j (g * h)) = σ g (c.val (j h)) + c.val (j g)
    rw [← hσ, j.map_mul]
    exact (groupCohomology.mem_cocycles₁_iff _).mp c.val.property (j g) (j h)⟩,
      c.property.comp hj⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The combined restriction and action identification retains the original value. -/
theorem continuousCocycleOneRestrictionCongr_apply
    (c : continuousRepresentationCocyclesOne A) (g : H) :
    (continuousCocycleOneRestrictionCongr A j hj σ hσ c).val g = c.val (j g) := rfl

end
end Dubon2026
