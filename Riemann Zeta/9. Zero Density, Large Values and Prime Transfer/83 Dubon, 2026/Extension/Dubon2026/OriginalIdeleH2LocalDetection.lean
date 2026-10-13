import Dubon2026.OriginalIdeleUnrestrictedCoordinates
import Dubon2026.OriginalTransportedH2LocalDetection
import Dubon2026.OriginalGlobalH2IdeleInjection

/-! # Local detection of actual original idele and global field-unit H2

Every original idele class lifts to a finite stable support. Its H2 is
detected by the unrestricted local factor, and literal stabilizer
restriction with coordinate evaluation detects that factor. Class H1
vanishing then gives local detection of original field-unit H2. These
are the maps required for cyclic cyclotomic killing on DUB-17's route to
arithmetic invariant sum-zero; local invariant comparison and the
cyclotomic extension construction remain separate obligations.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Original full idele H2 is detected by its actual unrestricted-coordinate maps over finite stable supports. -/
theorem originalIdeleH2_zero_of_unrestricted
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : ∀ (S : Finset (HeightOneSpectrum (𝓞 L)))
      (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S),
      (groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullUnrestrictedRepHom K L S hS) x = 0) :
    x = 0 := by
  obtain ⟨S, hS, hu, y, hy⟩ := originalIdeleH2_exists_supported_lift K L x
  have hproj : (groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalSupportedUnrestrictedProjection K L S hS) y = 0 := by
    rw [← originalSupportedFull_unrestricted_composition, Functor.map_comp]
    change (groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullUnrestrictedRepHom K L S hS)
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSupportedFullIdeleInclusion K L S hS) y) = 0
    rw [hy]
    exact hx S hS
  have hy0 : y = 0 := originalSupportedUnrestrictedH2_injective K L S hS hu
    (hproj.trans (map_zero _).symm)
  rw [← hy, hy0]
  exact map_zero ((groupCohomology.functor ℤ Gal(L/K) 2).map
    (originalSupportedFullIdeleInclusion K L S hS)).hom

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
/-- Actual subgroup restriction and original completion evaluation at a finite-support place orbit. -/
def originalIdeleLocalH2Map
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) :
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      groupCohomology (originalFullIdeleRep K L) 2 ⟶
        groupCohomology (transportedOrbitPointRep ℤ Gal(L/K) (SUnitLogPlace L S)
          (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
          (supportedUnrestrictedUnitTransport_one K L S hS)
          (supportedUnrestrictedUnitTransport_mul K L S hS) ω
          (originalOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)) 2 := by
  letI := sUnitLogPlaceAction K L S hS
  intro ω
  exact groupCohomology.map
    (MulAction.stabilizer Gal(L/K) (originalOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)).subtype
    ((Rep.resFunctor
      (MulAction.stabilizer Gal(L/K) (originalOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)).subtype).map
        (originalFullUnrestrictedRepHom K L S hS) ≫
      originalTransportedOrbitEvaluation ℤ Gal(L/K) (SUnitLogPlace L S)
        (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
        (supportedUnrestrictedUnitTransport_one K L S hS)
        (supportedUnrestrictedUnitTransport_mul K L S hS) ω) 2

/-- Vanishing of the literal original local restriction/evaluation maps kills an original full idele H2 class. -/
theorem originalIdeleH2_zero_of_local
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : ∀ (S : Finset (HeightOneSpectrum (𝓞 L)))
      (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S),
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        originalIdeleLocalH2Map K L S hS ω x = 0) : x = 0 := by
  apply originalIdeleH2_zero_of_unrestricted K L x
  intro S hS
  letI := sUnitLogPlaceAction K L S hS
  apply originalTransportedH2_zero_of_local ℤ Gal(L/K) (SUnitLogPlace L S)
    (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
    (supportedUnrestrictedUnitTransport_one K L S hS)
    (supportedUnrestrictedUnitTransport_mul K L S hS)
  intro ω
  let H := MulAction.stabilizer Gal(L/K) (originalOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)
  let q := originalTransportedOrbitEvaluation ℤ Gal(L/K) (SUnitLogPlace L S)
    (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
    (supportedUnrestrictedUnitTransport_one K L S hS)
    (supportedUnrestrictedUnitTransport_mul K L S hS) ω
  have hc := groupCohomology.map_comp (A := originalFullIdeleRep K L)
    (B := supportedUnrestrictedUnitRep K L S hS) (MonoidHom.id Gal(L/K)) H.subtype
    (originalFullUnrestrictedRepHom K L S hS) q 2
  have h := hx S hS ω
  change (groupCohomology.map ((MonoidHom.id Gal(L/K)).comp H.subtype)
    ((Rep.resFunctor H.subtype).map (originalFullUnrestrictedRepHom K L S hS) ≫ q) 2) x = 0 at h
  rw [hc] at h
  exact h

/-- The proved original class H1 vanishing makes literal local restriction/evaluation detect original global field-unit H2. -/
theorem originalGlobalUnitH2_zero_of_local
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : ∀ (S : Finset (HeightOneSpectrum (𝓞 L)))
      (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S),
      letI := sUnitLogPlaceAction K L S hS
      ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        originalIdeleLocalH2Map K L S hS ω
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) = 0) :
    x = 0 := by
  apply originalFullPrincipalH2_injective K L
  exact (originalIdeleH2_zero_of_local K L _ hx).trans
    (map_zero ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L)).hom).symm

end
end Dubon2026
