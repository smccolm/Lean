import Dubon2026.OriginalIdeleH2PointDetection
import Dubon2026.OriginalGlobalInfiniteH2

/-! # Actual infinite-place localization agrees with supported point detection

The original infinite decomposition group and its literal field-completion
cocycle map supply the infinite-place input to the proved global detection
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

/-- The supported infinite-place stabilizer maps to the same original infinite decomposition group. -/
def originalSupportedInfiniteStabilizerHom (w : InfinitePlace L) :
    letI := sUnitLogPlaceAction K L S hS
    MulAction.stabilizer Gal(L/K) (Sum.inl w : SUnitLogPlace L S) →*
      OriginalInfiniteDecompositionGroup K L w := by
  letI := sUnitLogPlaceAction K L S hS
  exact {
    toFun := fun σ => ⟨σ.val, Sum.inl.inj σ.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }

/-- The actual infinite completion coefficient is the supported point coefficient on the same values. -/
def originalSupportedInfiniteCoefficientHom (w : InfinitePlace L) :
    letI := sUnitLogPlaceAction K L S hS
    Rep.res (originalSupportedInfiniteStabilizerHom K L S hS w) (originalInfiniteUnitRep K L w) ⟶
      transportedStabilizerRep ℤ Gal(L/K) (SUnitLogPlace L S)
        (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
        (supportedUnrestrictedUnitTransport_one K L S hS)
        (supportedUnrestrictedUnitTransport_mul K L S hS) (Sum.inl w) := by
  letI := sUnitLogPlaceAction K L S hS
  exact Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- On every original global H2 class, actual infinite-place localization equals the infinite supported-place detection map after literal stabilizer restriction. -/
theorem originalSupportedInfiniteH2_comparison
    (w : InfinitePlace L)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    letI := sUnitLogPlaceAction K L S hS
    groupCohomology.map (originalSupportedInfiniteStabilizerHom K L S hS w)
      (originalSupportedInfiniteCoefficientHom K L S hS w) 2 (originalGlobalInfiniteH2 K L w x) =
        originalIdelePointH2Map K L S hS (Sum.inl w)
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) := by
  letI := sUnitLogPlaceAction K L S hS
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)) =
      groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c))
    simp only [groupCohomology.H2π_comp_map_apply]
    rfl

/-- Actual original infinite-place H2 vanishing supplies exactly the supported infinite-place vanishing needed by global detection. -/
theorem originalIdelePointH2Map_principal_infinite_zero
    (w : InfinitePlace L)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : originalGlobalInfiniteH2 K L w x = 0) :
    letI := sUnitLogPlaceAction K L S hS
    originalIdelePointH2Map K L S hS (Sum.inl w)
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) = 0 := by
  letI := sUnitLogPlaceAction K L S hS
  rw [← originalSupportedInfiniteH2_comparison, hx, map_zero]

end
end Dubon2026
