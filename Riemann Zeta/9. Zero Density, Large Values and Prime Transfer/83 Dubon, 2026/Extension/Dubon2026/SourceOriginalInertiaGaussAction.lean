import Dubon2026.SourceOriginalInertiaIntegralFunctions
import Dubon2026.SourceModularGaussResidueHom
import Dubon2026.SourceModularReductionCoordinate

/-! DUB-17/18 -> original Tate/Picard inertia -> actual modular reduction
equivariance. Transport the original arithmetic automorphism through the
already proved equality of the two literal modular fields. Its inertia
action preserves the actual Gauss ring and fixes the actual residue homomorphism.
The existing fraction witnesses and their proved choice independence suffice;
no new valuation, residue field or arithmetic action is postulated. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ

theorem coeffMap_mem_coefficient_field (N : ℕ) (τ : Qbar ≃ₐ[ℚ] Qbar)
    {f : LaurentSeries Qbar} (hf : f ∈ modularFunctionFieldCoeff N Qbar) :
    coeffMap (τ : Qbar →+* Qbar) f ∈ modularFunctionFieldCoeff N Qbar := by
  rw [← original_field_eq_coefficient_field] at hf ⊢
  exact coeffMap_mem_original N τ hf

/-- The original arithmetic automorphism on the equal coefficient field. -/
def coefficientArithmeticRingAut (N : ℕ) (τ : Qbar ≃ₐ[ℚ] Qbar) :
    modularFunctionFieldCoeff N Qbar ≃+* modularFunctionFieldCoeff N Qbar where
  toFun f := ⟨(originalArithmeticRingAut N τ
    ⟨f.val, by rw [original_field_eq_coefficient_field]; exact f.property⟩).val,
    coeffMap_mem_coefficient_field N τ f.property⟩
  invFun f := ⟨coeffMap (τ.symm : Qbar →+* Qbar) f.val,
    coeffMap_mem_coefficient_field N τ.symm f.property⟩
  left_inv f := by
    apply Subtype.ext
    ext n
    exact τ.symm_apply_apply (f.val.coeff n)
  right_inv f := by
    apply Subtype.ext
    ext n
    exact τ.apply_symm_apply (f.val.coeff n)
  map_mul' f g := Subtype.ext (map_mul (coeffMap (τ : Qbar →+* Qbar)) f.val g.val)
  map_add' f g := Subtype.ext (map_add (coeffMap (τ : Qbar →+* Qbar)) f.val g.val)

theorem coefficientArithmeticRingAut_coe (N : ℕ) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (f : modularFunctionFieldCoeff N Qbar) :
    (coefficientArithmeticRingAut N τ f : LaurentSeries Qbar) =
      coeffMap (τ : Qbar →+* Qbar) (f : LaurentSeries Qbar) := rfl

variable (A : ValuationSubring Qbar)

theorem isInt_coeffMap_inertia (d : A.decompositionSubgroup ℚ)
    (hd : d ∈ A.inertiaSubgroup ℚ) {f : LaurentSeries Qbar} (hf : IsInt A f) :
    IsInt A (coeffMap (d.val : Qbar →+* Qbar) f) := by
  obtain ⟨x, y, hy, h⟩ := hf
  let σA := MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d
  refine ⟨coeffMap σA x, coeffMap σA y, ?_, ?_⟩
  · exact (coeffMap_residue_inertia A d hd y).trans_ne hy
  · change coeffMap (d.val : Qbar →+* Qbar) f * coeffMap A.subtype (coeffMap σA y) =
      coeffMap A.subtype (coeffMap σA x)
    rw [coeffMap_subtype_decomposition, coeffMap_subtype_decomposition, ← map_mul]
    exact congrArg (coeffMap (d.val : Qbar →+* Qbar)) h

/-- Restriction of the original arithmetic inertia action to the actual Gauss ring. -/
def inertiaGaussHom (N : ℕ) (d : A.decompositionSubgroup ℚ)
    (hd : d ∈ A.inertiaSubgroup ℚ) : gaussRing A N →+* gaussRing A N where
  toFun f := ⟨coefficientArithmeticRingAut N d.val f.val, by
    rw [mem_gaussRing_iff, coefficientArithmeticRingAut_coe]
    exact isInt_coeffMap_inertia A d hd f.property⟩
  map_one' := Subtype.ext (map_one (coefficientArithmeticRingAut N d.val))
  map_mul' f g := Subtype.ext (map_mul (coefficientArithmeticRingAut N d.val) f.val g.val)
  map_zero' := Subtype.ext (map_zero (coefficientArithmeticRingAut N d.val))
  map_add' f g := Subtype.ext (map_add (coefficientArithmeticRingAut N d.val) f.val g.val)

theorem inertiaGaussHom_resHom (N : ℕ) (d : A.decompositionSubgroup ℚ)
    (hd : d ∈ A.inertiaSubgroup ℚ) (f : gaussRing A N) :
    resHom A N (inertiaGaussHom A N d hd f) = resHom A N f := by
  obtain ⟨hy, h⟩ := wit_spec A N f
  let σA := MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d
  have hy' : ϖ A (coeffMap σA (wit A N f).2) ≠ 0 :=
    (coeffMap_residue_inertia A d hd _).trans_ne hy
  have h' : ((inertiaGaussHom A N d hd f : modularFunctionFieldCoeff N Qbar) : LaurentSeries Qbar) *
      ι A (coeffMap σA (wit A N f).2) = ι A (coeffMap σA (wit A N f).1) := by
    change coeffMap (d.val : Qbar →+* Qbar) (f.val : LaurentSeries Qbar) *
      coeffMap A.subtype (coeffMap σA (wit A N f).2) =
        coeffMap A.subtype (coeffMap σA (wit A N f).1)
    rw [coeffMap_subtype_decomposition, coeffMap_subtype_decomposition, ← map_mul]
    exact congrArg (coeffMap (d.val : Qbar →+* Qbar)) h
  rw [resHom_eq A N hy' h', resHom_eq A N hy h]
  rw [show ϖ A (coeffMap σA (wit A N f).1) = ϖ A (wit A N f).1 from
    coeffMap_residue_inertia A d hd _,
    show ϖ A (coeffMap σA (wit A N f).2) = ϖ A (wit A N f).2 from
    coeffMap_residue_inertia A d hd _]

theorem inertiaGaussHom_modularResidue (N : ℕ) [NeZero N]
    (hNk : (N : IsLocalRing.ResidueField A) ≠ 0)
    (d : A.decompositionSubgroup ℚ) (hd : d ∈ A.inertiaSubgroup ℚ) (f : gaussRing A N) :
    modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk (inertiaGaussHom A N d hd f) =
      modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f :=
  Subtype.ext (inertiaGaussHom_resHom A N d hd f)

end
end Dubon2026.SourceFunctionField.GaussReduction
