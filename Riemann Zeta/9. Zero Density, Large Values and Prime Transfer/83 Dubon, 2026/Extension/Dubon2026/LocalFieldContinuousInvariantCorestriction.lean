import Dubon2026.LocalFieldContinuousRestrictionSurjective
import Dubon2026.GaloisUnitContinuousCorestriction

/-! # The actual local invariant commutes with genuine continuous corestriction -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]

/-- Corestriction defined by the genuine finite coset trace preserves
the original rational invariant for every finite separable local extension.
The proof uses the proved restriction degree formula and an explicit
continuous restriction-corestriction homotopy on the actual cocycles. -/
theorem localFieldContinuousH2InvariantEquiv_corestriction :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    ∀ y : GaloisUnitContinuousH2 (K := E) (Ω := Ω),
      localFieldContinuousH2InvariantEquiv K Ω (galoisUnitContinuousCorestriction K Ω E y) =
        localFieldContinuousH2InvariantEquiv E Ω y := by
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  intro y
  obtain ⟨x, rfl⟩ := localFieldContinuousH2_restriction_surjective K Ω E y
  rw [galoisUnitContinuousCorestriction_restriction, map_nsmul,
    localFieldContinuousH2InvariantEquiv_finite_restriction]

/-- The actual coset-sum corestriction is bijective on the original
continuous local H2 groups, as proved through their arithmetic invariants. -/
theorem localFieldContinuousH2_corestriction_bijective :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    Function.Bijective (galoisUnitContinuousCorestriction K Ω E) := by
  haveI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  constructor
  · intro x y hxy
    apply (localFieldContinuousH2InvariantEquiv E Ω).injective
    rw [← localFieldContinuousH2InvariantEquiv_corestriction K Ω E x,
      ← localFieldContinuousH2InvariantEquiv_corestriction K Ω E y, hxy]
  · intro x
    obtain ⟨y, hy⟩ := (localFieldContinuousH2InvariantEquiv E Ω).surjective
      (localFieldContinuousH2InvariantEquiv K Ω x)
    refine ⟨y, (localFieldContinuousH2InvariantEquiv K Ω).injective ?_⟩
    exact (localFieldContinuousH2InvariantEquiv_corestriction K Ω E y).trans hy

end
end Dubon2026
