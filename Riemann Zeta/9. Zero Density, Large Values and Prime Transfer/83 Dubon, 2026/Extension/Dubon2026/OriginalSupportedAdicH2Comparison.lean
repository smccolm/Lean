import Dubon2026.OriginalIdeleH2PointDetection
import Dubon2026.OriginalGlobalAdicH2

/-! # Actual finite-prime localization agrees with supported point detection

The original prime decomposition group and its literal field-completion
cocycle map supply the finite-place input to the proved global detection
theorem. The comparison is on actual H2 classes, not an equality inferred
from cardinalities. This removes the finite-support indexing obstacle
before DUB-17's normalized-invariant and cyclotomic-killing comparison.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The supported finite-place stabilizer maps to the same original prime decomposition group. -/
def originalSupportedFiniteStabilizerHom (w : {v : HeightOneSpectrum (𝓞 L) // v ∈ S}) :
    letI := sUnitLogPlaceAction K L S hS
    MulAction.stabilizer Gal(L/K) (Sum.inr w : SUnitLogPlace L S) →*
      OriginalFiniteDecompositionGroup K L w.val := by
  letI := sUnitLogPlaceAction K L S hS
  exact {
    toFun := fun σ => ⟨σ.val, congrArg Subtype.val (Sum.inr.inj σ.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }

/-- The actual finite completion coefficient is the supported point coefficient on the same values. -/
def originalSupportedAdicCoefficientHom (w : {v : HeightOneSpectrum (𝓞 L) // v ∈ S}) :
    letI := sUnitLogPlaceAction K L S hS
    Rep.res (originalSupportedFiniteStabilizerHom K L S hS w) (originalAdicUnitRep K L w.val) ⟶
      transportedStabilizerRep ℤ Gal(L/K) (SUnitLogPlace L S)
        (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
        (supportedUnrestrictedUnitTransport_one K L S hS)
        (supportedUnrestrictedUnitTransport_mul K L S hS) (Sum.inr w) := by
  letI := sUnitLogPlaceAction K L S hS
  exact Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- On every original global H2 class, actual finite-prime localization equals the finite supported-place detection map after literal stabilizer restriction. -/
theorem originalSupportedAdicH2_comparison
    (w : {v : HeightOneSpectrum (𝓞 L) // v ∈ S})
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    letI := sUnitLogPlaceAction K L S hS
    groupCohomology.map (originalSupportedFiniteStabilizerHom K L S hS w)
      (originalSupportedAdicCoefficientHom K L S hS w) 2 (originalGlobalAdicH2 K L w.val x) =
        originalIdelePointH2Map K L S hS (Sum.inr w)
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) := by
  letI := sUnitLogPlaceAction K L S hS
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)) =
      groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c))
    simp only [groupCohomology.H2π_comp_map_apply]
    rfl

/-- Actual original finite-prime H2 vanishing supplies exactly the supported finite-place vanishing needed by global detection. -/
theorem originalIdelePointH2Map_principal_finite_zero
    (w : {v : HeightOneSpectrum (𝓞 L) // v ∈ S})
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : originalGlobalAdicH2 K L w.val x = 0) :
    letI := sUnitLogPlaceAction K L S hS
    originalIdelePointH2Map K L S hS (Sum.inr w)
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) = 0 := by
  letI := sUnitLogPlaceAction K L S hS
  rw [← originalSupportedAdicH2_comparison, hx, map_zero]

end
end Dubon2026
