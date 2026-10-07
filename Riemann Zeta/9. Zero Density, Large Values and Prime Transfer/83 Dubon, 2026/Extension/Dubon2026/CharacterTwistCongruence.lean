import Dubon2026.PrincipalUpperDescent
import Dubon2026.PrincipalCharacterTwist

/-! # Integral translation cosets for genuine quadratic twists -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The diagonal entries of an upper congruence matrix are inverse modulo every divisor of its level. -/
theorem GammaUpper_diagonal_mul {N D : ℕ} (hD : D ∣ N)
    (γ : SL(2, ℤ)) (hγ : γ ∈ GammaUpper N) :
    (γ 0 0 : ZMod D) * (γ 1 1 : ZMod D) = 1 := by
  have hb : (D : ℤ) ∣ γ 0 1 := (Int.natCast_dvd_natCast.mpr hD).trans
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ)
  have hb0 : (γ 0 1 : ZMod D) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb
  have he := congrArg (fun z : ℤ => (z : ZMod D))
    ((Matrix.det_fin_two γ.val).symm.trans γ.property)
  push_cast at he
  simpa only [hb0, zero_mul, sub_zero] using he

/-- Translation by jN/D permutes upper congruence cosets by multiplication by the lower diagonal square. -/
theorem characterTwist_translation_conjugate {D H : ℕ} (hDH : D ∣ H)
    (γ : SL(2, ℤ)) (hγ : γ ∈ GammaUpper (D * H)) (a b : ℤ)
    (hab : (b : ZMod D) = (γ 1 1 : ZMod D) ^ 2 * (a : ZMod D)) :
    ModularGroup.T ^ (a * H) * γ * (ModularGroup.T ^ (b * H))⁻¹ ∈ GammaUpper (D * H) := by
  have hd := GammaUpper_diagonal_mul (dvd_mul_right D H) γ hγ
  have hbase : (D : ℤ) ∣ a * γ 1 1 - γ 0 0 * b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [hab]
    calc
      _ = (a : ZMod D) * (γ 1 1 : ZMod D) *
          (1 - (γ 0 0 : ZMod D) * (γ 1 1 : ZMod D)) := by ring
      _ = 0 := by rw [hd, sub_self, mul_zero]
  have hb : ((D * H : ℕ) : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  obtain ⟨v, hv⟩ := hb
  obtain ⟨u, hu⟩ := hbase
  obtain ⟨t, ht⟩ := Int.natCast_dvd_natCast.mpr hDH
  change (((ModularGroup.T ^ (a * H) * γ * (ModularGroup.T ^ (b * H))⁻¹) 0 1 : ℤ) : ZMod (D * H)) = 0
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  refine ⟨v + u - a * b * t * γ 1 0, ?_⟩
  rw [← _root_.zpow_neg]
  simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T_zpow]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_mul]
  push_cast at hv ⊢
  linear_combination hv + (H : ℤ) * hu - a * b * γ 1 0 * H * ht

end
end Dubon2026
