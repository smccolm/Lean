import Dubon2026.OriginalSupportedOutsideH2
import Dubon2026.SupportedIdeleLocalFactorRepresentation

/-! # Original supported H2 is detected by its unrestricted local factor

The actual outside-support H2 vanishes for every finite Galois number-field
extension with unramified complement. The literal unrestricted projection
therefore detects the original supported class. This is the coefficient
step needed for global H2 local detection on DUB-17's invariant sum-zero chain.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical

private def binaryFst {R G : Type} [CommRing R] [Group G] (A B : Rep R G) :
    Rep.of (A.ρ.prod B.ρ) ⟶ A :=
  Rep.ofHom ⟨LinearMap.fst R A B, by intro g; rfl⟩

private theorem binaryH2Fst_injective {R G : Type} [CommRing R] [Group G]
    (A B : Rep R G) (hz : Limits.IsZero (groupCohomology B 2)) :
    Function.Injective ((groupCohomology.functor R G 2).map (binaryFst A B)) := by
  let C := Rep.of (A.ρ.prod B.ρ)
  let snd : C ⟶ B := Rep.ofHom ⟨LinearMap.snd R A B, by intro g; rfl⟩
  have hzero (x : groupCohomology C 2)
      (hx : (groupCohomology.functor R G 2).map (binaryFst A B) x = 0) : x = 0 := by
    induction x using groupCohomology.H2_induction_on with
    | h c =>
      change groupCohomology.map (MonoidHom.id G) (binaryFst A B) 2
        (groupCohomology.H2π C c) = 0 at hx
      rw [groupCohomology.H2π_comp_map_apply] at hx
      obtain ⟨a, ha⟩ := (groupCohomology.H2π_eq_zero_iff _).mp hx
      have hb : groupCohomology.H2π B
          (groupCohomology.mapCocycles₂ (MonoidHom.id G) snd c) = 0 :=
        (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _
      obtain ⟨b, hb⟩ := (groupCohomology.H2π_eq_zero_iff _).mp hb
      apply (groupCohomology.H2π_eq_zero_iff c).mpr
      refine ⟨fun g => (a g, b g), ?_⟩
      funext g
      exact Prod.ext (congrFun ha g) (congrFun hb g)
  intro x y h
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, h, sub_self]

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual unrestricted-coordinate projection of the original supported-idele coefficient. -/
def originalSupportedUnrestrictedProjection :
    originalSupportedIdeleRep K L S hS ⟶ supportedUnrestrictedUnitRep K L S hS :=
  (supportedIdeleLocalFactorRepIso K L S hS).hom ≫
    binaryFst (supportedUnrestrictedUnitRep K L S hS) (supportedOutsideUnitRep K L S hS)

/-- The actual unrestricted-coordinate projection is injective on original supported H2 when its complement is unramified. -/
theorem originalSupportedUnrestrictedH2_injective
    [NumberField K] [FiniteDimensional K L] [IsGalois K L]
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Function.Injective ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalSupportedUnrestrictedProjection K L S hS)) := by
  let A := supportedUnrestrictedUnitRep K L S hS
  let B := supportedOutsideUnitRep K L S hS
  let e := supportedIdeleLocalFactorRepIso K L S hS
  have hi := binaryH2Fst_injective A B (originalOutsideUnit_second_zero_of_unramified K L S hS hu)
  have he : (groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalSupportedUnrestrictedProjection K L S hS) =
      (groupCohomology.functor ℤ Gal(L/K) 2).map e.hom ≫
        (groupCohomology.functor ℤ Gal(L/K) 2).map (binaryFst A B) :=
    (groupCohomology.functor ℤ Gal(L/K) 2).map_comp e.hom (binaryFst A B)
  intro x y h
  rw [he] at h
  apply ((groupCohomology.functor ℤ Gal(L/K) 2).mapIso e).toLinearEquiv.injective
  exact hi h

end
end Dubon2026
