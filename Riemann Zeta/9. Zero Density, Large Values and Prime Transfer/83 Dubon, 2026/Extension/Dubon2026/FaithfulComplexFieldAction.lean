import Dubon2026.FaithfulRealFieldCohomology
import Dubon2026.OriginalRealComplexSecondCohomology
import Mathlib.Analysis.Complex.Basic

/-! # The original continuous complex action as a real Galois action

Conjugating the actual field action by the original completion equivalence
gives continuous complex automorphisms. The pinned classification shows
that they fix the reals. Faithfulness is retained, supplying the exact
group comparison for DUB-17's archimedean H2 input.
-/

namespace Dubon2026
noncomputable section
variable (G F : Type) [Group G] [Field F] [MulSemiringAction G F]
  (e : F ≃+* ℂ)
  (hc : ∀ g : G, Continuous (fun z : ℂ => e (g • e.symm z)))

/-- The original field action transported to a continuous real-algebra automorphism of the complex field. -/
def faithfulComplexActionAut (g : G) : Gal(ℂ/ℝ) := {
  __ := (e.symm.trans (MulSemiringAction.toRingEquiv G F g)).trans e
  commutes' r := by
    let f := ((e.symm.trans (MulSemiringAction.toRingEquiv G F g)).trans e).toRingHom
    have hf : Continuous f := hc g
    change f (r : ℂ) = (r : ℂ)
    rcases Complex.ringHom_eq_id_or_conj_of_continuous hf with h | h
    · rw [h]; rfl
    · rw [h]; simp }

/-- Transport preserves multiplication of the actual acting group. -/
def faithfulComplexActionHom : G →* Gal(ℂ/ℝ) where
  toFun := faithfulComplexActionAut G F e hc
  map_one' := by ext z; simp [faithfulComplexActionAut]
  map_mul' g h := by ext z; simp [faithfulComplexActionAut, mul_smul]

variable [FaithfulSMul G F]

/-- Faithfulness on the original field gives injectivity into the actual real/complex Galois group. -/
theorem faithfulComplexActionHom_injective :
    Function.Injective (faithfulComplexActionHom G F e hc) := by
  intro g h hgh
  apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
  intro x
  apply e.injective
  have he := congrArg (fun f : Gal(ℂ/ℝ) => f (e x)) hgh
  change e (g • e.symm (e x)) = e (h • e.symm (e x)) at he
  simpa only [e.symm_apply_apply] using he

end
end Dubon2026
