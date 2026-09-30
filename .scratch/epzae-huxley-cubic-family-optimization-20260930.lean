import Mathlib.Tactic
namespace HuxleyCubicFamilyScratch

private theorem long_short_cubic_balance {A a b D Gamma : ℝ}
    (hb : 0 < b) (hGamma : 0 < Gamma) :
    let length := (max 1 D/(Gamma*b))^((3:ℝ)⁻¹)
    0 < length ∧
      Gamma*max A (a+b*length)+D/length^2 ≤
        Gamma*max A a+2*Gamma*b*length := by
  intro length
  have hE : 0 < max 1 D := zero_lt_one.trans_le (le_max_left _ _)
  have hgb : 0 < Gamma*b := mul_pos hGamma hb
  have hratio : 0 < max 1 D/(Gamma*b) := div_pos hE hgb
  have hlength : 0 < length := Real.rpow_pos_of_pos hratio _
  have hcube : length^3=max 1 D/(Gamma*b) :=
    Real.rpow_inv_natCast_pow hratio.le (by norm_num : (3:ℕ) ≠ 0)
  have hDc : D ≤ Gamma*b*length^3 := by
    have he := (eq_div_iff hgb.ne').mp hcube
    calc
      D ≤ max 1 D := le_max_right _ _
      _ = Gamma*b*length^3 := by nlinarith only [he]
  have htail : D/length^2 ≤ Gamma*b*length := by
    apply (div_le_iff₀ (sq_pos_of_pos hlength)).mpr
    nlinarith only [hDc]
  have hshort : max A (a+b*length) ≤ max A a+b*length := by
    apply max_le
    · exact (le_max_left A a).trans (le_add_of_nonneg_right (mul_pos hb hlength).le)
    · exact add_le_add (le_max_right A a) le_rfl
  refine ⟨hlength,?_⟩
  calc
    Gamma*max A (a+b*length)+D/length^2 ≤ Gamma*(max A a+b*length)+Gamma*b*length :=
      add_le_add (mul_le_mul_of_nonneg_left hshort hGamma.le) htail
    _ = Gamma*max A a+2*Gamma*b*length := by ring

#print axioms long_short_cubic_balance
end HuxleyCubicFamilyScratch
