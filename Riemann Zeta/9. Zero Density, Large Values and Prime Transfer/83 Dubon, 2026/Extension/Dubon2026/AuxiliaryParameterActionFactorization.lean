import Dubon2026.AuxiliaryComparisonConvergingAction
import Dubon2026.AuxiliaryFixedParameterContinuity

/-! The constructed auxiliary group-algebra action factors the exact
original arithmetic parameter action. Polynomial density and the same
original character values establish equality; no compatibility square
is supplied as an arithmetic assumption. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped MvPowerSeries.WithPiTopology

/-- The converging auxiliary parameter action composes to the original
deformation-ring action, with continuity derived from the original
residue comparison and compact coefficient topologies. -/
theorem auxiliaryComparisonConvergingParameterAction_factorization
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    {R A ι m G η : Type} [CommRing R] [IsLocalRing R] [Algebra O R]
    [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    [CommRing A] [Algebra O A] [Fintype ι] [DecidableEq ι] [Fintype η]
    [Fintype m] [DecidableEq m]
    (Q : Finset Nat.Primes) (q level : ℕ) [Fact q.Prime] [CharP (ResidueField O) q]
    (τ : G → GeneralLinearGroup m R) (τ₀ : G → GeneralLinearGroup m A)
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η)
    (hmod : ∀ p : Q, p.val.val ≡ 1 [MOD q ^ level])
    (eR : ResidueField R ≃ₐ[O] ResidueField O) :
    (auxiliaryFamilyGroupAlgebra O d.comparison.augmentation.characters).comp
      (auxiliaryComparisonConvergingParameterAction O Q q level τ τ₀ d hmod).val =
        auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d := by
  classical
  let D := ∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q
  letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
  let fR := auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d
  have hR : Continuous fR := auxiliaryFixedPowerSeriesParameterMap_continuous Q q τ τ₀ d eR
  have hO : Continuous (algebraMap O R) := by
    have hC := hR.comp MvPowerSeries.WithPiTopology.continuous_C
    have he : (fun x : O => fR (MvPowerSeries.C x)) = algebraMap O R :=
      funext (fun x => fR.commutes x)
    exact he ▸ hC
  letI : ContinuousSMul O R := ⟨by
    simpa only [Algebra.smul_def] using (hO.comp continuous_fst).mul continuous_snd⟩
  let θ := auxiliaryFamilyGroupAlgebra O d.comparison.augmentation.characters
  have hθ : Continuous θ := IsModuleTopology.continuous_of_linearMap θ.toLinearMap
  let c := auxiliaryComparisonConvergingParameterAction O Q q level τ τ₀ d hmod
  apply continuousPowerSeriesAlgHom_ext
  · exact hθ.comp c.property.2.2.1
  · exact hR
  · intro j
    change θ (c.val (MvPowerSeries.X j)) = fR (MvPowerSeries.X j)
    rw [c.property.1]
    let t : D := Pi.mulSingle (d.index j).1
      (Pi.mulSingle (d.index j).2 (d.comparison.parameters.generators (d.index j).1))
    change θ.toRingHom (MonoidAlgebra.of O D t - 1) = fR (MvPowerSeries.X j)
    rw [map_sub θ.toRingHom (MonoidAlgebra.of O D t) 1, map_one θ.toRingHom]
    have ht : θ.toRingHom (MonoidAlgebra.of O D t) =
        (d.comparison.augmentation.characters (d.index j).1
          (d.comparison.parameters.generators (d.index j).1)).val (d.index j).2 :=
      auxiliaryFamilyGroupAlgebra_of_single O d.comparison.augmentation.characters
        (d.index j).1 (d.index j).2 (d.comparison.parameters.generators (d.index j).1)
    rw [ht]
    exact (auxiliaryPowerSeriesFixedParameterMap_X O Q q τ τ₀ d.comparison d.index j).symm


/-- An arithmetic comparison and its compatible auxiliary action, with all
topological and quantitative properties proved by the constructor below. -/
structure AuxiliaryCompatibleConvergingParameterData
    (O : Type) [CommRing O] [IsLocalRing O] [TopologicalSpace O]
    {R A ι m G η : Type} [CommRing R] [IsLocalRing R] [Algebra O R]
    [CommRing A] [Algebra O A] [Fintype ι] [DecidableEq ι] [Fintype η]
    [Fintype m] [DecidableEq m]
    (Q : Finset Nat.Primes) (q level : ℕ) [Fact q.Prime]
    (τ : G → GeneralLinearGroup m R) (τ₀ : G → GeneralLinearGroup m A) where
  /-- The original fixed-index arithmetic comparison and its character generators. -/
  comparison : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η
  /-- The constructed coefficient action on the genuine auxiliary group algebra. -/
  action : MvPowerSeries η O →ₐ[O]
    MonoidAlgebra O (∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q)
  variableValue : ∀ j, action (MvPowerSeries.X j) = MonoidAlgebra.of O _
    (Pi.mulSingle (comparison.index j).1 (Pi.mulSingle (comparison.index j).2
      (comparison.comparison.parameters.generators (comparison.index j).1))) - 1
  isLocal : IsLocalHom action.toRingHom
  continuous :
    letI : TopologicalSpace (MonoidAlgebra O
      (∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q)) := moduleTopology O _
    Continuous action
  kernel_le : ∀ n ≤ level, RingHom.ker action.toRingHom ≤ maximalIdeal (MvPowerSeries η O) ^ n
  factorization :
    (auxiliaryFamilyGroupAlgebra O comparison.comparison.augmentation.characters).comp action =
      auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ comparison

/-- The constructed action retains both quantitative kernel convergence and
its proved factorization to the original deformation parameter action. -/
def auxiliaryComparisonCompatibleConvergingParameterAction
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    {R A ι m G η : Type} [CommRing R] [IsLocalRing R] [Algebra O R]
    [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    [CommRing A] [Algebra O A] [Fintype ι] [DecidableEq ι] [Fintype η]
    [Fintype m] [DecidableEq m]
    (Q : Finset Nat.Primes) (q level : ℕ) [Fact q.Prime] [CharP (ResidueField O) q]
    (τ : G → GeneralLinearGroup m R) (τ₀ : G → GeneralLinearGroup m A)
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η)
    (hmod : ∀ p : Q, p.val.val ≡ 1 [MOD q ^ level])
    (eR : ResidueField R ≃ₐ[O] ResidueField O) :
    AuxiliaryCompatibleConvergingParameterData O (ι := ι) (η := η) Q q level τ τ₀ := by
  let c := auxiliaryComparisonConvergingParameterAction O Q q level τ τ₀ d hmod
  exact ⟨d, c.val, c.property.1, c.property.2.1, c.property.2.2.1, c.property.2.2.2,
    auxiliaryComparisonConvergingParameterAction_factorization O Q q level τ τ₀ d hmod eR⟩

end
end Dubon2026
