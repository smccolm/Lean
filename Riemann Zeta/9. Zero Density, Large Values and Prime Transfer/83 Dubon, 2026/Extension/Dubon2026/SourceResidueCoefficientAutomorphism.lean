import Dubon2026.SourceResidueIntegralSpecialization

/-! DUB-17/18 -> original Frobenius comparison -> arithmetic Frobenius
on the actual residue modular field. The literal divisor generators are
fixed by every coefficient homomorphism. Native intermediate-field
induction therefore restricts the coefficient automorphism to this field.
This is needed for the residue arithmetic action; no general semilinear
automorphism framework or divisor-rigidity package is introduced.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_reductionModL_smul_of_isFrobeniusAt, coefficient section. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
variable (N : ℕ) (K : Type*) [Field K]
local notation "FF" => modularFunctionFieldCoeff N K

theorem coefficientMap_mem_divisor_field (φ : K →+* K) {f : LaurentSeries K}
    (hf : f ∈ modularFunctionFieldCoeff N K) :
    coeffMap φ f ∈ modularFunctionFieldCoeff N K := by
  induction hf using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hd, hdN, rfl⟩ := hy
    letI := hd
    rw [coefficientMap_j_expansion]
    exact jqd_mem_coeff_field N K hdN
  | algebraMap a =>
    simpa only [SourceDifferential.algebraMap_laurentSeries_apply_alt, coeffMap_single] using
      (modularFunctionFieldCoeff N K).algebraMap_mem (φ a)
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- The coefficient action on the actual modular field in residue characteristic. -/
def residueCoefficientRingAut (e : K ≃+* K) : FF ≃+* FF where
  toFun f := ⟨coeffMap e.toRingHom f.val, coefficientMap_mem_divisor_field N K _ f.property⟩
  invFun f := ⟨coeffMap e.symm.toRingHom f.val, coefficientMap_mem_divisor_field N K _ f.property⟩
  left_inv f := by
    apply Subtype.ext
    ext n
    exact e.symm_apply_apply (f.val.coeff n)
  right_inv f := by
    apply Subtype.ext
    ext n
    exact e.apply_symm_apply (f.val.coeff n)
  map_mul' f g := Subtype.ext (map_mul (coeffMap e.toRingHom) f.val g.val)
  map_add' f g := Subtype.ext (map_add (coeffMap e.toRingHom) f.val g.val)

theorem residueCoefficientRingAut_coe (e : K ≃+* K) (f : FF) :
    (residueCoefficientRingAut N K e f : LaurentSeries K) = coeffMap e.toRingHom f.val := rfl

theorem residueCoefficientRingAut_constants (e : K ≃+* K) (a : K) :
    residueCoefficientRingAut N K e (algebraMap K FF a) = algebraMap K FF (e a) := by
  apply Subtype.ext
  change coeffMap e.toRingHom (algebraMap K (LaurentSeries K) a) =
    algebraMap K (LaurentSeries K) (e a)
  simpa only [SourceDifferential.algebraMap_laurentSeries_apply_alt] using
    coeffMap_single e.toRingHom 0 a

theorem residueCoefficientRingAut_j (e : K ≃+* K) :
    residueCoefficientRingAut N K e (jCoeff N K) = jCoeff N K :=
  Subtype.ext (map_jqModC e.toRingHom)

end
end Dubon2026.SourceFunctionField
