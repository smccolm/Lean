import Dubon2026.NumberFieldPrimePowerValuations
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Independent original S-unit valuation coordinates

This constructs actual S-units from the class-number generators, with
exact coordinates in the existing valuation map. The range-rank calculation
then supplies the S-unit power-index input to global reciprocity for DUB-17.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

/-- The existing original S-unit valuations, written as an integer linear map. -/
def sUnitValuationLinearMap {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (HeightOneSpectrum R)) : Additive (S.unit K) →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x v => (sUnitValuations S x.toMul v).toAdd
      map_zero' := by
        funext v
        exact congrArg Multiplicative.toAdd (congrFun (map_one (sUnitValuations S)) v)
      map_add' := fun x y => by
        funext v
        exact congrArg Multiplicative.toAdd
          (congrFun (map_mul (sUnitValuations S) x.toMul y.toMul) v) }

/-- The actual nonzero prime-power generator as a unit in the original number field. -/
def numberFieldPrimePowerUnit (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K (numberFieldPrimePowerGenerator K v))
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr
      (numberFieldPrimePowerGenerator_ne_zero K v))

open Classical in
/-- The actual valuation coordinates of the prime-power field unit. -/
theorem numberFieldPrimePowerUnit_valuation (K : Type*) [Field K] [NumberField K]
    (v w : HeightOneSpectrum (𝓞 K)) :
    w.valuationOfNeZero (numberFieldPrimePowerUnit K v) =
      Multiplicative.ofAdd (if w = v then -(NumberField.classNumber K : ℤ) else 0) := by
  apply WithZero.coe_injective
  rw [HeightOneSpectrum.valuationOfNeZero_eq]
  change w.valuation K (algebraMap (𝓞 K) K (numberFieldPrimePowerGenerator K v)) = _
  rw [HeightOneSpectrum.valuation_of_algebraMap, numberFieldPrimePowerGenerator_intValuation]
  rfl

/-- The original prime-power generator is an S-unit whenever its prime belongs to S. -/
def numberFieldPrimePowerSUnit (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (v : S) : S.unit K :=
  ⟨numberFieldPrimePowerUnit K v.val, fun w hw => by
    have hne : w ≠ v.val := fun h => hw (h ▸ v.property)
    have h := numberFieldPrimePowerUnit_valuation K v.val w
    rw [if_neg hne] at h
    have h' := congrArg (fun z : Multiplicative ℤ => (z : WithZero (Multiplicative ℤ))) h
    simpa only [HeightOneSpectrum.valuationOfNeZero_eq] using h'⟩

open Classical in
/-- An actual original S-unit realizes the nonzero class-number multiple of a single coordinate. -/
theorem numberFieldPrimePowerSUnit_coordinate (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (v w : S) :
    sUnitValuationLinearMap S (Additive.ofMul (numberFieldPrimePowerSUnit K S v)) w =
      if w = v then -(NumberField.classNumber K : ℤ) else 0 := by
  change (w.val.valuationOfNeZero (numberFieldPrimePowerUnit K v.val)).toAdd = _
  rw [numberFieldPrimePowerUnit_valuation]
  simp only [Subtype.val_inj]
  rfl

end
end Dubon2026
