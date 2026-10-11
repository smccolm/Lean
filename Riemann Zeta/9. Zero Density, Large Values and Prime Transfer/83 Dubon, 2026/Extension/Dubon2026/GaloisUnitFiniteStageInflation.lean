import Dubon2026.ContinuousKummerH2Maps
import Dubon2026.ContinuousCohomologyRestriction

/-! # Original finite-stage Galois unit coefficients and actual H2 inflation -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)

/-- The original finite-field unit inclusion is a morphism from the actual
restricted finite Galois action to the original extension-field unit action. -/
def galoisUnitFiniteStageInclusion :
    restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K F)
      (AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K)) ⟶
      Rep.ofAlgebraAutOnUnits K Ω :=
  Rep.ofHom {
    toLinearMap := (Units.map F.toIntermediateField.val.toMonoidHom).toAdditive.toIntLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      change Units.map F.toIntermediateField.val.toMonoidHom
          (AlgEquiv.restrictNormalHom F g • (Additive.toMul (Rep.toAdditive x) : Fˣ)) =
        g • Units.map F.toIntermediateField.val.toMonoidHom
          (Additive.toMul (Rep.toAdditive x) : Fˣ)
      apply Units.ext
      exact AlgEquiv.restrictNormal_commutes g F
        (Additive.toMul (Rep.toAdditive x) : Fˣ).val }

omit [IsGalois K Ω] in
/-- The original coefficient morphism sends each actual finite-stage unit to
its literal image under the original field inclusion. -/
theorem galoisUnitFiniteStageInclusion_apply (u : Fˣ) :
    (galoisUnitFiniteStageInclusion F).hom
      (Rep.toAdditive.symm (Additive.ofMul u) : Rep.ofAlgebraAutOnUnits K F) =
      Rep.toAdditive.symm (Additive.ofMul (Units.map F.toIntermediateField.val.toMonoidHom u)) := by
  rfl

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits K F)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K F)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Actual restriction precomposition followed by the original unit inclusion
defines finite-stage inflation on the existing continuous H2 quotients. -/
def galoisUnitFiniteStageH2Inflation :
    GaloisUnitContinuousH2 (K := K) (Ω := F) →ₗ[ℤ]
      GaloisUnitContinuousH2 (K := K) (Ω := Ω) := by
  let j : Gal(Ω/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hj : Continuous j := InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField
  let φ := (galoisUnitFiniteStageInclusion F).hom.toLinearMap
  let hF := discreteGaloisUnitAction_continuous (K := K) (Ω := F)
  let hΩ := discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)
  exact (continuousCoefficientH2Map
    (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K F) j)
    (Rep.ofAlgebraAutOnUnits K Ω) φ continuous_of_discreteTopology
    (Rep.hom_comm_apply (galoisUnitFiniteStageInclusion F))
    (restrictedCoefficientAction_continuous (Rep.ofAlgebraAutOnUnits K F) j hj hF) hΩ).comp
      (continuousRepresentationH2Restriction (Rep.ofAlgebraAutOnUnits K F) hF j hj)

/-- Inflation on an original finite-stage cocycle uses actual restriction in
both original variables and the literal original coefficient inclusion. -/
theorem galoisUnitFiniteStageH2Inflation_mk
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K F)) :
    galoisUnitFiniteStageH2Inflation F (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCoefficientCocycleTwoMap
        (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K F)
          (AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K)))
        (Rep.ofAlgebraAutOnUnits K Ω) (galoisUnitFiniteStageInclusion F).hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply (galoisUnitFiniteStageInclusion F))
        (continuousRepresentationCocycleTwoRestriction (Rep.ofAlgebraAutOnUnits K F)
          (AlgEquiv.restrictNormalHom F : Gal(Ω/K) →* Gal(F/K))
          (InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField) c)) := by
  rfl

end
end Dubon2026
