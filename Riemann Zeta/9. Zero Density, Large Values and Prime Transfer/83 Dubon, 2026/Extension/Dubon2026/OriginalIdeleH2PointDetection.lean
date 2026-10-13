import Dubon2026.OriginalIdeleH2LocalDetection
import Dubon2026.OriginalTransportedPointH2Detection

/-! # Original global H2 detection through actual place stabilizers

The already proved finite-support detection now uses literal original
places rather than subtypes of chosen orbits. This connects DUB-17's
required local vanishing to the original finite and infinite completion
maps, retaining both kinds of places and deriving support internally.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
/-- Actual subgroup restriction and original completion evaluation at a finite-support place. -/
def originalIdelePointH2Map
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) :
    letI := sUnitLogPlaceAction K L S hS
    ∀ p : SUnitLogPlace L S,
      groupCohomology (originalFullIdeleRep K L) 2 ⟶
        groupCohomology (transportedStabilizerRep ℤ Gal(L/K) (SUnitLogPlace L S)
          (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
          (supportedUnrestrictedUnitTransport_one K L S hS)
          (supportedUnrestrictedUnitTransport_mul K L S hS) p) 2 := by
  letI := sUnitLogPlaceAction K L S hS
  intro p
  exact groupCohomology.map
    (MulAction.stabilizer Gal(L/K) p).subtype
    ((Rep.resFunctor
      (MulAction.stabilizer Gal(L/K) p).subtype).map
        (originalFullUnrestrictedRepHom K L S hS) ≫
      transportedStabilizerEvaluation ℤ Gal(L/K) (SUnitLogPlace L S)
        (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
        (supportedUnrestrictedUnitTransport_one K L S hS)
        (supportedUnrestrictedUnitTransport_mul K L S hS) p) 2

/-- Vanishing of the literal original local restriction/evaluation maps kills an original full idele H2 class. -/
theorem originalIdeleH2_zero_of_points
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : ∀ (S : Finset (HeightOneSpectrum (𝓞 L)))
      (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S),
      letI := sUnitLogPlaceAction K L S hS
      ∀ p : SUnitLogPlace L S,
        originalIdelePointH2Map K L S hS p x = 0) : x = 0 := by
  apply originalIdeleH2_zero_of_unrestricted K L x
  intro S hS
  letI := sUnitLogPlaceAction K L S hS
  apply originalTransportedH2_zero_of_points ℤ Gal(L/K) (SUnitLogPlace L S)
    (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
    (supportedUnrestrictedUnitTransport_one K L S hS)
    (supportedUnrestrictedUnitTransport_mul K L S hS)
  intro p
  let H := MulAction.stabilizer Gal(L/K) p
  let q := transportedStabilizerEvaluation ℤ Gal(L/K) (SUnitLogPlace L S)
    (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
    (supportedUnrestrictedUnitTransport_one K L S hS)
    (supportedUnrestrictedUnitTransport_mul K L S hS) p
  have hc := groupCohomology.map_comp (A := originalFullIdeleRep K L)
    (B := supportedUnrestrictedUnitRep K L S hS) (MonoidHom.id Gal(L/K)) H.subtype
    (originalFullUnrestrictedRepHom K L S hS) q 2
  have h := hx S hS p
  change (groupCohomology.map ((MonoidHom.id Gal(L/K)).comp H.subtype)
    ((Rep.resFunctor H.subtype).map (originalFullUnrestrictedRepHom K L S hS) ≫ q) 2) x = 0 at h
  rw [hc] at h
  exact h

/-- The proved original class H1 vanishing makes literal local restriction/evaluation detect original global field-unit H2. -/
theorem originalGlobalUnitH2_zero_of_points
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : ∀ (S : Finset (HeightOneSpectrum (𝓞 L)))
      (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S),
      letI := sUnitLogPlaceAction K L S hS
      ∀ p : SUnitLogPlace L S,
        originalIdelePointH2Map K L S hS p
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) = 0) :
    x = 0 := by
  apply originalFullPrincipalH2_injective K L
  exact (originalIdeleH2_zero_of_points K L _ hx).trans
    (map_zero ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L)).hom).symm

end
end Dubon2026
