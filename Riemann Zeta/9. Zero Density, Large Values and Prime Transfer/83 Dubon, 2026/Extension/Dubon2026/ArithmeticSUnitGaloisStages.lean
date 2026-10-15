import Dubon2026.ArithmeticSUnitValuationStages
import Dubon2026.ArithmeticExceptionalSUnitSupport
import Dubon2026.OriginalSPlaceIdeleSequence

/-! # Actual S-unit descent to the original finite Galois stages

The source Ext comparison uses finite Galois stages in the unramified union.
Normal closure and the literal localized coefficient maps supply those stages
without changing the exceptional integer or assuming a colimit presentation.
-/

namespace Dubon2026
noncomputable section
open IntermediateField IsDedekindDomain
open scoped NumberField

section Tower
variable (K E F : Type) [Field K] [Field E] [Field F]
  [NumberField K] [NumberField E] [NumberField F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- The original localized rings over the same exceptional integer map along the actual field tower. -/
def originalLocalizedIntegerTowerMap :
    originalLocalizedIntegers E (algebraMap (𝓞 K) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha) →+*
    originalLocalizedIntegers F (algebraMap (𝓞 K) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha) :=
  ((algebraMap E F).comp
    (originalLocalizedIntegers E (algebraMap (𝓞 K) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha)).val.toRingHom).codRestrict _ (by
    intro x
    have h := originalLocalizedIntegers_map_mem (L := F)
      (algebraMap (𝓞 K) (𝓞 E) a) (originalIntegerMap_ne_zero (L := E) a ha) x
    simpa only [← IsScalarTower.algebraMap_apply] using h)

omit [NumberField K] in
/-- The localized tower map retains the literal original field embedding. -/
theorem originalLocalizedIntegerTowerMap_coe
    (x : originalLocalizedIntegers E (algebraMap (𝓞 K) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha)) :
    (originalLocalizedIntegerTowerMap K E F a ha x).val = algebraMap E F x.val := rfl

end Tower

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)

/-- Every actual arithmetic S-unit is represented in an original finite Galois stage of the same unramified union. -/
theorem originalArithmeticSUnit_exists_finiteGaloisStage
    (u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      letI : NumberField F := NumberField.of_module_finite K F
      ∃ v : (originalLocalizedIntegers F (algebraMap (𝓞 K) (𝓞 F) a)
          (originalIntegerMap_ne_zero (L := F) a ha))ˣ,
        F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
          algebraMap F Ω v.val.val = u.val.val.val := by
  obtain ⟨E, hfin, h⟩ := originalArithmeticSUnit_exists_finiteStage K Ω a ha u
  letI := hfin
  letI : NumberField E := NumberField.of_module_finite K E
  obtain ⟨v, hE, hv⟩ := h
  let Γ := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : IsGalois K Γ := originalUnramifiedGaloisUnion_isGalois a
  let F : FiniteGaloisIntermediateField K Ω := ⟨normalClosure K E Ω⟩
  letI : NumberField F := NumberField.of_module_finite K F
  have hF : F.toIntermediateField ≤ Γ := by
    change normalClosure K E Ω ≤ Γ
    rw [← normalClosure_of_normal Γ]
    exact normalClosure_mono E Γ hE
  let w := Units.map (originalLocalizedIntegerTowerMap K E F a ha).toMonoidHom v
  refine ⟨F, w, hF, ?_⟩
  change algebraMap F Ω (algebraMap E F v.val.val) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact hv

/-- The original finite Galois stages exhaust the actual arithmetic S-units through the already constructed valuation-stage maps. -/
theorem originalArithmeticSUnit_mem_finiteGaloisStage_range
    (u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      letI : NumberField F := NumberField.of_module_finite K F
      ∃ hF : F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a,
        u ∈ (originalValuationStageSUnitMap K Ω a ha F.toIntermediateField hF).range := by
  obtain ⟨F, h⟩ := originalArithmeticSUnit_exists_finiteGaloisStage K Ω a ha u
  letI : NumberField F := NumberField.of_module_finite K F
  obtain ⟨v, hF, hv⟩ := h
  let e := originalLocalizedUnitsEquivSUnits F (algebraMap (𝓞 K) (𝓞 F) a)
    (originalIntegerMap_ne_zero (L := F) a ha)
  refine ⟨F, hF, e v, ?_⟩
  apply Units.ext
  apply Subtype.ext
  apply Subtype.ext
  exact (originalValuationStageSUnitMap_coe K Ω a ha F.toIntermediateField hF (e v)).trans
    ((congrArg (algebraMap F Ω)
      (originalLocalizedUnitsEquivSUnits_coe F (algebraMap (𝓞 K) (𝓞 F) a)
        (originalIntegerMap_ne_zero (L := F) a ha) v)).trans hv)

/-- Every original arithmetic S-unit enters the source short exact idele sequence at an actual finite Galois stage with exactly the original exceptional support. -/
theorem originalArithmeticSUnit_exists_sourceIdeleStage
    (u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      letI : NumberField F := NumberField.of_module_finite K F
      let S := originalExceptionalIntegerSupport F (algebraMap (𝓞 K) (𝓞 F) a)
        (originalIntegerMap_ne_zero (L := F) a ha)
      let hS := originalExceptionalIntegerSupport_galoisStable F K a ha
      ∃ v : (S : Set (HeightOneSpectrum (𝓞 F))).unit F,
        F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
          algebraMap F Ω v.val.val = u.val.val.val ∧
          (originalSPlaceIdeleShortComplex K F S hS).ShortExact := by
  obtain ⟨F, h⟩ := originalArithmeticSUnit_exists_finiteGaloisStage K Ω a ha u
  letI : NumberField F := NumberField.of_module_finite K F
  obtain ⟨v, hF, hv⟩ := h
  let S := originalExceptionalIntegerSupport F (algebraMap (𝓞 K) (𝓞 F) a)
    (originalIntegerMap_ne_zero (L := F) a ha)
  let hS := originalExceptionalIntegerSupport_galoisStable F K a ha
  refine ⟨F, originalLocalizedUnitsEquivSupportedSUnits F (algebraMap (𝓞 K) (𝓞 F) a)
    (originalIntegerMap_ne_zero (L := F) a ha) v, hF, ?_,
    originalSPlaceIdeleShortComplex_shortExact K F S hS⟩
  exact (congrArg (algebraMap F Ω)
    (originalLocalizedUnitsEquivSupportedSUnits_coe F (algebraMap (𝓞 K) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha) v)).trans hv

end
end Dubon2026
