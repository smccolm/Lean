import Dubon2026.MatrixRepresentationRelationIdeals
import Dubon2026.MatrixRepresentationConjugation

/-! The actual inertia matrix relation ideal is invariant under change
of basis. This allows the constructed local embedding conjugacy to be
used in the original universal ring, without replacing its coefficients
or its unramified quotient in the Dubon Theorem 2.6 dependency chain. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A B : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B]

/-- Changing the whole original basis preserves the exact relation
kernel after any coefficient map. -/
theorem matrixRepresentationConjugate_kernel_iff
    (ρ : G →* GeneralLinearGroup ι A) (U : GeneralLinearGroup ι A)
    (I : Subgroup G) (f : A →+* B) :
    I ≤ ((GeneralLinearGroup.map f).comp (matrixRepresentationConjugate ρ U)).ker ↔
      I ≤ ((GeneralLinearGroup.map f).comp ρ).ker := by
  constructor
  · intro h g hg
    have hz := h hg
    change GeneralLinearGroup.map f (U * ρ g * U⁻¹) = 1 at hz
    change GeneralLinearGroup.map f (ρ g) = 1
    apply (MulAut.conj (GeneralLinearGroup.map f U)).injective
    simpa only [MulAut.conj_apply, map_mul, map_inv, map_one, mul_one, mul_inv_cancel] using hz
  · intro h g hg
    have hz : GeneralLinearGroup.map f (ρ g) = 1 := h hg
    change GeneralLinearGroup.map f (U * ρ g * U⁻¹) = 1
    simp only [map_mul, map_inv, hz, mul_one, mul_inv_cancel]

/-- The original coefficient ideal imposing all inertia relations is
unchanged by an actual invertible basis change. -/
theorem matrixRepresentationRelationIdeal_conjugate
    (ρ : G →* GeneralLinearGroup ι A) (U : GeneralLinearGroup ι A) (I : Subgroup G) :
    matrixRepresentationRelationIdeal (matrixRepresentationConjugate ρ U) I =
      matrixRepresentationRelationIdeal ρ I := by
  let J := matrixRepresentationRelationIdeal (matrixRepresentationConjugate ρ U) I
  let K := matrixRepresentationRelationIdeal ρ I
  apply le_antisymm
  · have hk := matrixRepresentationRelationIdeal_quotient_kills ρ I
    have hc := (matrixRepresentationConjugate_kernel_iff ρ U I (Ideal.Quotient.mk K)).mpr hk
    have hj := (matrixRepresentationRelationIdeal_le_kernel_iff
      (matrixRepresentationConjugate ρ U) I (Ideal.Quotient.mk K)).mpr hc
    simpa only [Ideal.mk_ker] using hj
  · have hj := matrixRepresentationRelationIdeal_quotient_kills (matrixRepresentationConjugate ρ U) I
    have hc := (matrixRepresentationConjugate_kernel_iff ρ U I (Ideal.Quotient.mk J)).mp hj
    have hk := (matrixRepresentationRelationIdeal_le_kernel_iff ρ I (Ideal.Quotient.mk J)).mpr hc
    simpa only [Ideal.mk_ker] using hk

end
end Dubon2026
