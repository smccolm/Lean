import Dubon2026.LocalizedIntegerSUnitComparison
import Dubon2026.ArithmeticSUnitDivisibility

/-! # Actual arithmetic S-units at the original valuation-defined finite stages

This connects the constructed global S-unit coefficient with the same S-unit
groups used by the existing supported-idele sequence. The finite-stage field
values are retained; no idele exactness or cohomology comparison is assumed.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- Every original arithmetic S-unit descends to an original valuation-defined S-unit at a finite field. -/
theorem originalArithmeticSUnit_exists_valuationStage
    [IsAlgClosure K Ω]
    (u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ) :
    ∃ (E : IntermediateField K Ω) (hfin : FiniteDimensional K E),
      letI := hfin
      letI : NumberField E := NumberField.of_module_finite K E
      ∃ v : ({w : HeightOneSpectrum (𝓞 E) |
          algebraMap (𝓞 K) (𝓞 E) a ∈ w.asIdeal} : Set _).unit E,
        E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ∧
          algebraMap E Ω v.val.val = u.val.val.val := by
  obtain ⟨E, hfin, h⟩ := originalArithmeticSUnit_exists_finiteStage K Ω a ha u
  letI := hfin
  letI : NumberField E := NumberField.of_module_finite K E
  obtain ⟨v, hE, hv⟩ := h
  let aE := algebraMap (𝓞 K) (𝓞 E) a
  have haE : aE ≠ 0 := originalIntegerMap_ne_zero (L := E) a ha
  refine ⟨E, hfin, originalLocalizedUnitsEquivSUnits E aE haE v, hE, ?_⟩
  exact (congrArg (algebraMap E Ω) (originalLocalizedUnitsEquivSUnits_coe E aE haE v)).trans hv

variable (E : IntermediateField K Ω) [FiniteDimensional K E]
  (hE : E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)

local instance stageNumberField : NumberField E := NumberField.of_module_finite K E

/-- The actual finite-stage localized integers embed into the original arithmetic integral closure. -/
def originalLocalizedStageToArithmeticSIntegers :
    originalLocalizedIntegers E (algebraMap (𝓞 K) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha) →+* OriginalArithmeticSUnitRing K Ω a ha := by
  let R := originalLocalizedIntegers K a ha
  let S := originalLocalizedIntegers E (algebraMap (𝓞 K) (𝓞 E) a)
    (originalIntegerMap_ne_zero (L := E) a ha)
  let Γ := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : Algebra R S := (originalLocalizedIntegersMap (L := E) a ha).toRingHom.toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsIntegralClosure S R E := (canonicalLocalizedIntegerAlgebra_data (L := E) a ha).2.1
  let j : E →ₐ[R] Γ := {
    (IntermediateField.inclusion hE).toRingHom with commutes' := fun _ => rfl }
  exact (j.toRingHom.comp S.val.toRingHom).codRestrict _ (fun x =>
    ((IsIntegralClosure.isIntegral R E x).map (IsScalarTower.toAlgHom R S E)).map j)

/-- The original finite-stage map retains its literal value in the ambient field. -/
theorem originalLocalizedStageToArithmeticSIntegers_coe
    (x : originalLocalizedIntegers E (algebraMap (𝓞 K) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha)) :
    (originalLocalizedStageToArithmeticSIntegers K Ω a ha E hE x).val.val =
      algebraMap E Ω x.val := rfl

/-- The original valuation-defined finite-stage S-units map into the actual arithmetic S-units. -/
def originalValuationStageSUnitMap :
    ({w : HeightOneSpectrum (𝓞 E) | algebraMap (𝓞 K) (𝓞 E) a ∈ w.asIdeal} : Set _).unit E →*
      (OriginalArithmeticSUnitRing K Ω a ha)ˣ :=
  (Units.map (originalLocalizedStageToArithmeticSIntegers K Ω a ha E hE).toMonoidHom).comp
    (originalLocalizedUnitsEquivSUnits E (algebraMap (𝓞 K) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha)).symm.toMonoidHom

/-- The original valuation-stage inclusion is exactly the original ambient field embedding. -/
theorem originalValuationStageSUnitMap_coe
    (v : ({w : HeightOneSpectrum (𝓞 E) |
      algebraMap (𝓞 K) (𝓞 E) a ∈ w.asIdeal} : Set _).unit E) :
    (originalValuationStageSUnitMap K Ω a ha E hE v).val.val.val =
      algebraMap E Ω v.val.val := by
  let e := originalLocalizedUnitsEquivSUnits E (algebraMap (𝓞 K) (𝓞 E) a)
    (originalIntegerMap_ne_zero (L := E) a ha)
  have he := originalLocalizedUnitsEquivSUnits_coe E (algebraMap (𝓞 K) (𝓞 E) a)
    (originalIntegerMap_ne_zero (L := E) a ha) (e.symm v)
  have hev : (e.symm v).val.val = v.val.val := by
    rw [show originalLocalizedUnitsEquivSUnits E (algebraMap (𝓞 K) (𝓞 E) a)
      (originalIntegerMap_ne_zero (L := E) a ha) (e.symm v) = v from e.apply_symm_apply v] at he
    exact he.symm
  exact congrArg (algebraMap E Ω) hev

/-- Every actual arithmetic S-unit lies in the constructed image of an original valuation-defined finite stage. -/
theorem originalArithmeticSUnit_mem_valuationStage_range [IsAlgClosure K Ω]
    (u : (OriginalArithmeticSUnitRing K Ω a ha)ˣ) :
    ∃ (E : IntermediateField K Ω) (hfin : FiniteDimensional K E),
      letI := hfin
      letI : NumberField E := NumberField.of_module_finite K E
      ∃ hE : E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a,
        u ∈ (originalValuationStageSUnitMap K Ω a ha E hE).range := by
  obtain ⟨E, hfin, h⟩ := originalArithmeticSUnit_exists_valuationStage K Ω a ha u
  letI := hfin
  letI : NumberField E := NumberField.of_module_finite K E
  obtain ⟨v, hE, hv⟩ := h
  refine ⟨E, hfin, hE, v, ?_⟩
  apply Units.ext
  apply Subtype.ext
  apply Subtype.ext
  exact (originalValuationStageSUnitMap_coe K Ω a ha E hE v).trans hv

end
end Dubon2026
