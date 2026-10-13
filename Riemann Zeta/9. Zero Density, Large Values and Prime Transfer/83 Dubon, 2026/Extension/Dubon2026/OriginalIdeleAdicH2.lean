import Dubon2026.OriginalGlobalAdicH2
import Dubon2026.OriginalIdeleH2SupportedLift
import Dubon2026.OriginalSupportedOutsideH2
import Dubon2026.SupportedIdeleLocalFactorRepresentation

/-! # Original idele localization outside a finite unramified support

The original completion coordinate factors through the actual outside
integer-unit coefficient. Its proved H2 vanishing therefore kills the
localized supported class. These literal coefficient maps provide finite
support for the original global class before DUB-17's cyclotomic killing.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- Evaluation of an actual full idele at the original finite prime, with its actual decomposition action. -/
def originalFullIdeleAdicRepHom (w : HeightOneSpectrum (𝓞 L)) :
    Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalFullIdeleRep K L) ⟶
      originalAdicUnitRep K L w :=
  Rep.ofHom ⟨(numberFieldIdeleFiniteComponent L w).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro a
    apply congrArg Additive.ofMul
    apply Units.ext
    exact numberFieldFiniteAdeleGaloisMap_apply K L σ.val a.toMul.val.2 w w σ.property⟩

/-- The actual original finite-prime localization of full idele H2. -/
def originalFullIdeleAdicH2 (w : HeightOneSpectrum (𝓞 L)) :
    groupCohomology (originalFullIdeleRep K L) 2 ⟶
      groupCohomology (originalAdicUnitRep K L w) 2 :=
  groupCohomology.map (OriginalFiniteDecompositionGroup K L w).subtype
    (originalFullIdeleAdicRepHom K L w) 2

/-- Original principal inclusion followed by idele localization is the literal original global-unit localization. -/
theorem originalFullIdeleAdicH2_principal
    (w : HeightOneSpectrum (𝓞 L)) (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    originalFullIdeleAdicH2 K L w
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) x) =
      originalGlobalAdicH2 K L w x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)) =
      groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)
    simp only [groupCohomology.H2π_comp_map_apply]
    rfl

variable (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- Projection onto the original outside-support integer-unit product. -/
def originalSupportedOutsideProjection :
    originalSupportedIdeleRep K L S hS ⟶ supportedOutsideUnitRep K L S hS :=
  (supportedIdeleLocalFactorRepIso K L S hS).hom ≫
    Rep.ofHom ⟨LinearMap.snd ℤ (supportedUnrestrictedUnitRep K L S hS)
      (supportedOutsideUnitRep K L S hS), by intro σ; rfl⟩

/-- The actual outside-support integer coordinate embedded in the same original completion units. -/
def originalOutsideAdicRepHom (w : {v : HeightOneSpectrum (𝓞 L) // v ∉ S}) :
    Rep.res (OriginalFiniteDecompositionGroup K L w.val).subtype
      (supportedOutsideUnitRep K L S hS) ⟶ originalAdicUnitRep K L w.val := by
  letI := supportedOutsidePlaceAction K L S hS
  refine Rep.ofHom ⟨((Units.map (w.val.adicCompletionIntegers L).subtype.toMonoidHom).toAdditive.toIntLinearMap).comp
    (LinearMap.proj w), ?_⟩
  intro σ
  apply LinearMap.ext
  intro a
  apply congrArg Additive.ofMul
  apply Units.ext
  change (((transportedPiMap ℤ Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S}
    (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
    (supportedOutsideUnitTransport K L S hS) σ.val a w).toMul.val : w.val.adicCompletion L)) =
      numberFieldGaloisLocalTransport K L σ.val w.val w.val σ.property (a w).toMul.val.val
  rw [transportedPiMap_apply ℤ Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S}
    (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
    (supportedOutsideUnitTransport K L S hS) σ.val a w w (Subtype.ext σ.property)]
  rfl

/-- Outside the actual support, original idele localization factors through the same original integer-unit product. -/
theorem originalFullIdeleAdicH2_supported_outside
    (w : {v : HeightOneSpectrum (𝓞 L) // v ∉ S})
    (x : groupCohomology (originalSupportedIdeleRep K L S hS) 2) :
    originalFullIdeleAdicH2 K L w.val
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSupportedFullIdeleInclusion K L S hS) x) =
      groupCohomology.map (OriginalFiniteDecompositionGroup K L w.val).subtype
        (originalOutsideAdicRepHom K L S hS w) 2
        ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSupportedOutsideProjection K L S hS) x) := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)) =
      groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c))
    simp only [groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    apply congrArg Additive.ofMul
    apply Units.ext
    rfl

/-- A supported original idele class has zero localization at every unramified outside-support prime. -/
theorem originalFullIdeleAdicH2_supported_outside_zero
    [NumberField K] [FiniteDimensional K L] [IsGalois K L]
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (w : {v : HeightOneSpectrum (𝓞 L) // v ∉ S})
    (x : groupCohomology (originalSupportedIdeleRep K L S hS) 2) :
    originalFullIdeleAdicH2 K L w.val
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSupportedFullIdeleInclusion K L S hS) x) = 0 := by
  rw [originalFullIdeleAdicH2_supported_outside]
  have hz : (groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalSupportedOutsideProjection K L S hS) x = 0 :=
    (ModuleCat.isZero_iff_subsingleton.mp
      (originalOutsideUnit_second_zero_of_unramified K L S hS hu)).elim _ _
  rw [hz]
  exact map_zero (groupCohomology.map (OriginalFiniteDecompositionGroup K L w.val).subtype
    (originalOutsideAdicRepHom K L S hS w) 2).hom

end
end Dubon2026
