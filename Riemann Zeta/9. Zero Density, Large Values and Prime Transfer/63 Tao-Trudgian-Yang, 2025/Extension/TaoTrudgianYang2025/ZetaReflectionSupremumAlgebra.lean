import TaoTrudgianYang2025.ZetaReflectionMassEnvelope
import Mathlib.Data.EReal.Inv

/-! Positive finite affine maps commute with arbitrary extended-real suprema. -/

noncomputable section
open Set
namespace TaoTrudgianYang2025

theorem ereal_iSup_add_real {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨆ i, f i)+(a : EReal) = ⨆ i, f i+(a : EReal) := by
  apply le_antisymm
  · apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))).mp
    apply iSup_le
    intro i
    apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))).mpr
    exact le_iSup (fun i => f i+(a : EReal)) i
  · apply iSup_le
    intro i
    exact add_le_add (le_iSup f i) le_rfl

theorem ereal_pos_mul_iSup {ι : Sort*} (f : ι → EReal) {c : ℝ} (hc : 0 < c) :
    (c : EReal)*(⨆ i, f i) = ⨆ i, (c : EReal)*f i := by
  have hce : (0 : EReal) < c := EReal.coe_pos.mpr hc
  apply le_antisymm
  · have h : (⨆ i, f i) ≤ (⨆ i, (c : EReal)*f i)/(c : EReal) := by
      apply iSup_le
      intro i
      apply (EReal.le_div_iff_mul_le hce (EReal.coe_ne_top c)).mpr
      simpa only [EReal.mul_comm] using le_iSup (fun i => (c : EReal)*f i) i
    have h' := (EReal.le_div_iff_mul_le hce (EReal.coe_ne_top c)).mp h
    simpa only [EReal.mul_comm] using h'
  · apply iSup_le
    intro i
    exact mul_le_mul_of_nonneg_left (le_iSup f i) hce.le

theorem ereal_pos_affine_iSup {ι : Sort*} (f : ι → EReal) {c : ℝ}
    (hc : 0 < c) (a : ℝ) :
    (c : EReal)*(⨆ i, f i)+(a : EReal) =
      ⨆ i, (c : EReal)*f i+(a : EReal) := by
  rw [ereal_pos_mul_iSup f hc,ereal_iSup_add_real]

theorem ereal_pos_affine_comp (x : EReal) {c : ℝ} (hc : 0 < c) (d a b : ℝ) :
    (c : EReal)*((d : EReal)*x+(b : EReal))+(a : EReal) =
      ((c*d : ℝ) : EReal)*x+((c*b+a : ℝ) : EReal) := by
  calc
    _ = ((c : EReal)*((d : EReal)*x)+(c : EReal)*(b : EReal))+(a : EReal) := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc.le)
        (EReal.coe_ne_top c)]
    _ = ((c : EReal)*(d : EReal))*x+((c : EReal)*(b : EReal)+(a : EReal)) := by
      simp only [mul_assoc,add_assoc]
    _ = _ := by rw [← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add]

end TaoTrudgianYang2025
