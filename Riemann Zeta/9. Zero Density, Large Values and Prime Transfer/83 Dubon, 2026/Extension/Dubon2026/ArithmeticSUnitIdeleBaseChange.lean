import Dubon2026.ArithmeticExceptionalSUnitSupport
import Dubon2026.OriginalIdeleBaseChange

/-! # Original S-unit and supported-idele transition maps

The original exceptional supports pull back along the actual prime contraction.
The existing full-idele base change therefore restricts to supported ideles,
and the same principal map gives compatible S-unit transition maps. These are
the finite-stage maps needed by the source arithmetic coefficient colimits.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The original exceptional support in the upper field is exactly the inverse image under original prime contraction. -/
theorem originalExceptionalIntegerSupport_baseChange
    (a : 𝓞 K) (ha : a ≠ 0) (w : HeightOneSpectrum (𝓞 L)) :
    w ∈ originalExceptionalIntegerSupport L (algebraMap (𝓞 K) (𝓞 L) a)
      (originalIntegerMap_ne_zero (L := L) a ha) ↔
        originalFinitePrimeBelow K L w ∈ originalExceptionalIntegerSupport K a ha := by
  rw [mem_originalExceptionalIntegerSupport, mem_originalExceptionalIntegerSupport]
  rfl

variable (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 L)))
  (hST : ∀ w, w ∉ T → originalFinitePrimeBelow K L w ∉ S)

include hST in
/-- Original idele base change preserves the actual supported groups whenever the original supports pull back. -/
theorem originalIdeleBaseChangeMap_mem_supported
    (x : (AdeleRing (𝓞 K) K)ˣ) (hx : x ∈ numberFieldSupportedIdeles K S) :
    originalIdeleBaseChangeMap K L x ∈ numberFieldSupportedIdeles L T := by
  simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at hx ⊢
  intro w hw
  let v := originalFinitePrimeBelow K L w
  letI := originalFinitePrimeBelow_liesOver K L w
  have hv := hx v (hST w hw)
  change Valued.v (originalAdicBaseChangeMap K L v w
    (numberFieldIdeleFiniteComponent K v x).val) = 1
  rw [originalAdicBaseChangeMap_valuation, hv, one_pow]

/-- The actual full-idele base-change map restricted to the original supported groups. -/
def originalSupportedIdeleBaseChangeMap :
    numberFieldSupportedIdeles K S →* numberFieldSupportedIdeles L T :=
  ((originalIdeleBaseChangeMap K L).comp (numberFieldSupportedIdeles K S).subtype).codRestrict _
    (fun x => originalIdeleBaseChangeMap_mem_supported K L S T hST x.val x.property)

/-- The actual supported transition retains the original full idele. -/
theorem originalSupportedIdeleBaseChangeMap_coe (x : numberFieldSupportedIdeles K S) :
    (originalSupportedIdeleBaseChangeMap K L S T hST x).val =
      originalIdeleBaseChangeMap K L x.val := rfl

/-- The actual original supported-idele transition map is injective. -/
theorem originalSupportedIdeleBaseChangeMap_injective :
    Function.Injective (originalSupportedIdeleBaseChangeMap K L S T hST) := by
  intro x y h
  apply Subtype.ext
  exact originalIdeleBaseChangeMap_injective K L (congrArg Subtype.val h)

include hST in
/-- The actual field-unit embedding preserves the original S-unit groups. -/
theorem originalFieldUnitBaseChange_mem_SUnit (x : S.unit K) :
    Units.map (algebraMap K L).toMonoidHom x.val ∈ T.unit L := by
  apply (numberFieldPrincipalIdele_mem_supported_iff L T _).mp
  rw [← originalIdeleBaseChangeMap_principal]
  exact originalIdeleBaseChangeMap_mem_supported K L S T hST _
    ((numberFieldPrincipalIdele_mem_supported_iff K S x.val).mpr x.property)

/-- The original S-unit transition is the literal original field-unit map. -/
def originalValuationSUnitBaseChangeMap : S.unit K →* T.unit L :=
  ((Units.map (algebraMap K L).toMonoidHom).comp (S.unit K).subtype).codRestrict _
    (originalFieldUnitBaseChange_mem_SUnit K L S T hST)

/-- The S-unit transition retains the literal original field embedding. -/
theorem originalValuationSUnitBaseChangeMap_coe (x : S.unit K) :
    (originalValuationSUnitBaseChangeMap K L S T hST x).val.val =
      algebraMap K L x.val.val := rfl

/-- The original supported-idele and S-unit transition maps commute with the same principal inclusion. -/
theorem originalSupportedIdeleBaseChangeMap_principal (x : S.unit K) :
    originalSupportedIdeleBaseChangeMap K L S T hST (numberFieldSupportedPrincipalIdele K S x) =
      numberFieldSupportedPrincipalIdele L T (originalValuationSUnitBaseChangeMap K L S T hST x) := by
  apply Subtype.ext
  exact originalIdeleBaseChangeMap_principal K L x.val

/-- The exact original exceptional support supplies the supported-idele transition without a support premise. -/
def originalExceptionalSupportedIdeleBaseChange (a : 𝓞 K) (ha : a ≠ 0) :
    numberFieldSupportedIdeles K (originalExceptionalIntegerSupport K a ha) →*
      numberFieldSupportedIdeles L
        (originalExceptionalIntegerSupport L (algebraMap (𝓞 K) (𝓞 L) a)
          (originalIntegerMap_ne_zero (L := L) a ha)) :=
  originalSupportedIdeleBaseChangeMap K L _ _
    (fun w hw hv => hw ((originalExceptionalIntegerSupport_baseChange K L a ha w).mpr hv))

/-- The exact original exceptional support supplies the S-unit transition without a support premise. -/
def originalExceptionalSUnitBaseChange (a : 𝓞 K) (ha : a ≠ 0) :
    (↑(originalExceptionalIntegerSupport K a ha) : Set (HeightOneSpectrum (𝓞 K))).unit K →*
      (↑(originalExceptionalIntegerSupport L (algebraMap (𝓞 K) (𝓞 L) a)
        (originalIntegerMap_ne_zero (L := L) a ha)) : Set (HeightOneSpectrum (𝓞 L))).unit L :=
  originalValuationSUnitBaseChangeMap K L _ _
    (fun w hw hv => hw ((originalExceptionalIntegerSupport_baseChange K L a ha w).mpr hv))

/-- At the actual exceptional supports, the original principal square commutes with no support hypothesis. -/
theorem originalExceptionalSupportedIdeleBaseChange_principal
    (a : 𝓞 K) (ha : a ≠ 0)
    (x : (↑(originalExceptionalIntegerSupport K a ha) : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    originalExceptionalSupportedIdeleBaseChange K L a ha
      (numberFieldSupportedPrincipalIdele K _ x) =
        numberFieldSupportedPrincipalIdele L _ (originalExceptionalSUnitBaseChange K L a ha x) :=
  originalSupportedIdeleBaseChangeMap_principal K L _ _ _ x

/-- The original localized-unit map and the actual valuation-unit transition agree on the same field element. -/
theorem originalExceptionalSUnitBaseChange_localized
    (a : 𝓞 K) (ha : a ≠ 0) (u : (originalLocalizedIntegers K a ha)ˣ) :
    originalExceptionalSUnitBaseChange K L a ha
      (originalLocalizedUnitsEquivSupportedSUnits K a ha u) =
        originalLocalizedUnitsEquivSupportedSUnits L (algebraMap (𝓞 K) (𝓞 L) a)
          (originalIntegerMap_ne_zero (L := L) a ha)
          (Units.map (originalLocalizedIntegersMap (L := L) a ha).toMonoidHom u) := by
  apply Subtype.ext
  apply Units.ext
  change algebraMap K L (originalLocalizedUnitsEquivSupportedSUnits K a ha u).val.val = _
  rw [originalLocalizedUnitsEquivSupportedSUnits_coe,
    originalLocalizedUnitsEquivSupportedSUnits_coe]
  rfl

end
end Dubon2026
