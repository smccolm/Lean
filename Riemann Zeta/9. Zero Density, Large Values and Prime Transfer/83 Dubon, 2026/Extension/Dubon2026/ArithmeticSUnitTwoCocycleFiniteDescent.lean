import Dubon2026.ArithmeticSUnitFiniteFieldCoefficients
import Dubon2026.ArithmeticSUnitCocycleFiniteField
import Dubon2026.GaloisUnitTwoCocycleFiniteDescent

/-! # Exact finite descent of the original S-unit two-cocycle

The existing field-unit cocycle descent is reused. Integrality and inverse
integrality put its actual finite-field values in the source S-unit group,
with the original Galois action and exact original restriction map.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
open IsDedekindDomain
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))

local instance : NumberField F := NumberField.of_module_finite K F
local instance : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  originalUnramifiedGaloisUnion_isGalois a

variable (c : groupCohomology.cocycles₂ (originalArithmeticSUnitRepresentation K Ω a ha))
  (hvalues : ∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
    (c (g, h)).toMul.val.val ∈ F.toIntermediateField)
  (hperiod : ∀ g h u v : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
    AlgEquiv.restrictNormalHom F u = 1 → AlgEquiv.restrictNormalHom F v = 1 →
      c (g * u, h * v) = c (g, h))

include hvalues hperiod in
/-- Actual finite-field descent retains the original S-unit cocycle, its nontrivial Galois action and every original value. -/
theorem originalArithmeticSUnitTwoCocycle_exists_finite_descent :
    let S := originalExceptionalIntegerSupport F (algebraMap (𝓞 K) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha)
    let hS := originalExceptionalIntegerSupport_galoisStable F K a ha
    letI := numberFieldSUnitGaloisAction K F S hS
    ∃ f : Gal(F/K) × Gal(F/K) → (S : Set (HeightOneSpectrum (𝓞 F))).unit F,
      groupCohomology.IsMulCocycle₂ f ∧
      ∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
        Units.map F.toIntermediateField.val.toMonoidHom
          (f (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)).val =
            Units.map (OriginalArithmeticSUnitRing K Ω a ha).val.toMonoidHom (c (g, h)).toMul := by
  let Γ := originalUnramifiedGaloisUnion (Ω := Ω) a
  let S := originalExceptionalIntegerSupport F (algebraMap (𝓞 K) (𝓞 F) a)
    (originalIntegerMap_ne_zero (L := F) a ha)
  let hS := originalExceptionalIntegerSupport_galoisStable F K a ha
  letI := numberFieldSUnitGaloisAction K F S hS
  let d := groupCohomology.mapCocycles₂ (MonoidHom.id Gal(Γ/K))
    (originalArithmeticSUnitInclusion K Ω a ha) c
  have hdvalues : ∀ g h : Gal(Γ/K),
      ((Additive.toMul (Rep.toAdditive (d (g, h))) : Γˣ) : Γ) ∈ F.toIntermediateField := hvalues
  have hdperiod : ∀ g h u v : Gal(Γ/K), AlgEquiv.restrictNormalHom F u = 1 →
      AlgEquiv.restrictNormalHom F v = 1 → d (g * u, h * v) = d (g, h) := by
    intro g h u v hu hv
    exact congrArg (originalArithmeticSUnitInclusion K Ω a ha).hom (hperiod g h u v hu hv)
  obtain ⟨f, hf, hfactor⟩ :=
    galoisUnitTwoCocycle_exists_finite_descent F d hdvalues hdperiod
  have hj : Function.Surjective (AlgEquiv.restrictNormalHom F : Gal(Γ/K) →* Gal(F/K)) :=
    AlgEquiv.restrictNormalHom_surjective Γ
  have hmem (z : Gal(F/K) × Gal(F/K)) : f z ∈ (S : Set (HeightOneSpectrum (𝓞 F))).unit F := by
    obtain ⟨g, hg⟩ := hj z.1
    obtain ⟨h, hh⟩ := hj z.2
    obtain ⟨v, hv⟩ := originalArithmeticSUnit_supportedPreimage_at_finiteField
      K Ω a ha F (c (g, h)).toMul (hvalues g h)
    have he : v.val = f z := by
      apply Units.map_injective F.toIntermediateField.val.injective
      apply Units.ext
      have hfg := congrArg Units.val (hfactor g h)
      rw [hg, hh] at hfg
      exact hv.trans hfg.symm
    exact he ▸ v.property
  refine ⟨fun z => ⟨f z, hmem z⟩, ?_, ?_⟩
  · intro g h t
    exact Subtype.ext (hf g h t)
  · exact hfactor

local instance
    [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
    [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)] :
    @ContinuousSMul ℤ (originalArithmeticSUnitRepresentation K Ω a ha)
      (originalArithmeticSUnitRepresentation K Ω a ha).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- Every actual continuous arithmetic S-unit two-cocycle descends to a constructed finite Galois S-unit cocycle, with no finite-stage or period premise. -/
theorem originalArithmeticSUnitContinuousTwoCocycle_exists_finite_descent
    [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
    [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]
    (c : continuousRepresentationCocyclesTwo (originalArithmeticSUnitRepresentation K Ω a ha)) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      letI : NumberField F := NumberField.of_module_finite K F
      let S := originalExceptionalIntegerSupport F (algebraMap (𝓞 K) (𝓞 F) a)
        (originalIntegerMap_ne_zero (L := F) a ha)
      let hS := originalExceptionalIntegerSupport_galoisStable F K a ha
      letI := numberFieldSUnitGaloisAction K F S hS
      ∃ f : Gal(F/K) × Gal(F/K) → (S : Set (HeightOneSpectrum (𝓞 F))).unit F,
        groupCohomology.IsMulCocycle₂ f ∧
        ∀ g h : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
          Units.map F.toIntermediateField.val.toMonoidHom
            (f (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)).val =
              Units.map (OriginalArithmeticSUnitRing K Ω a ha).val.toMonoidHom
                (c.val (g, h)).toMul := by
  obtain ⟨F, hvalues, hperiod⟩ := originalArithmeticSUnitTwoCocycle_exists_finiteField K Ω a ha c
  exact ⟨F, originalArithmeticSUnitTwoCocycle_exists_finite_descent K Ω a ha F c.val hvalues hperiod⟩

end
end Dubon2026
