import Dubon2026.FaithfulFieldUnitHilbert90
import Mathlib.Data.Real.Hom

/-! # Actual real-completion actions have trivial stabilizer

Every real field automorphism is identity. A faithful action on a field
identified with the original real completion is therefore trivial, so its
positive original unit cohomology vanishes. This supplies the real branch
of DUB-17's unrestricted archimedean local factor.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance] Units.mulDistribMulActionRight
variable (G F : Type) [Group G] [Field F] [MulSemiringAction G F] [FaithfulSMul G F]

/-- A faithful action on the original real field has only the identity element. -/
theorem faithfulRealField_subsingleton (e : F ≃+* ℝ) : Subsingleton G := by
  refine ⟨fun g h => ?_⟩
  apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
  intro x
  apply e.injective
  have hg := Real.ringHom_apply
    (e.toRingHom.comp ((MulSemiringAction.toRingHom G F g).comp e.symm.toRingHom)) (e x)
  have hh := Real.ringHom_apply
    (e.toRingHom.comp ((MulSemiringAction.toRingHom G F h).comp e.symm.toRingHom)) (e x)
  change e (g • e.symm (e x)) = e x at hg
  change e (h • e.symm (e x)) = e x at hh
  rw [e.symm_apply_apply] at hg hh
  exact hg.trans hh.symm

/-- Original H2 on a real-completion unit coefficient is finite of its actual stabilizer order. -/
theorem faithfulRealField_second_cohomology_order (e : F ≃+* ℝ) :
    Finite (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) = Nat.card G := by
  haveI := faithfulRealField_subsingleton G F e
  have hz := isZero_groupCohomology_succ_of_subsingleton
    (Rep.ofMulDistribMulAction G Fˣ) 1
  haveI := ModuleCat.isZero_iff_subsingleton.mp hz
  exact ⟨Finite.of_subsingleton, (Nat.card_unique (α := groupCohomology
    (Rep.ofMulDistribMulAction G Fˣ) 2)).trans (Nat.card_unique (α := G)).symm⟩

end
end Dubon2026
