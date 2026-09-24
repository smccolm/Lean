import TaoTrudgianYang2025.ClassicalReflectedNormalizedSource
import TaoTrudgianYang2025.ClassicalReflectedColorTransfer

/-!
# Uniform physical conditions for the actual reflected source

The lower and upper logarithmic scale bounds imply the length, size and
near-two hypotheses required by compact zeta estimates. A separate eventual
bound fits the actual Fourier displacement inside the four positive slabs.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem eventually_classicalReflected_compact_scale_conditions
    (C U delta d : ℝ) (hU : 0 < U) (hdelta : 0 < delta)
    (hd : 0 ≤ d) (hdHalf : d ≤ 1/2) (hdWindow : d ≤ delta/8) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ N : ℕ, 1 < N →
      1/(1/2+d) ≤ typeILogarithmicScale T N →
      typeILogarithmicScale T N ≤ U →
      (N : ℝ) ≤ T ∧ C ≤ (N : ℝ) ∧ 4 ≤ (N : ℝ)^(delta/2) ∧
      2-delta/2 ≤ typeILogarithmicScale T N ∧
      typeILogarithmicScale T N ≤ U+delta/2 := by
  have hCevent := (tendsto_rpow_atTop (by positivity : 0 < 1/U)).eventually
    (Filter.eventually_ge_atTop C)
  have hPowerEvent := (tendsto_rpow_atTop (by positivity : 0 < delta/(2*U))).eventually
    (Filter.eventually_ge_atTop (4 : ℝ))
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),hCevent,hPowerEvent] with
    T hT hC hPower
  intro N hN hLower hUpper
  have hNreal : 1 < (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  let tau := typeILogarithmicScale T N
  have hScale : (N : ℝ)^tau = T := rpow_typeILogarithmicScale_eq hT hN
  have hden : 0 < (1/2+d : ℝ) := by linarith
  have hOne : 1 ≤ 1/(1/2+d) := (le_div_iff₀ hden).mpr (by linarith)
  have hNear : 2-4*d ≤ 1/(1/2+d) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [sq_nonneg d]
  have hNUpper : (N : ℝ) ≤ T := by
    rw [← hScale]
    exact Real.self_le_rpow_of_one_le hNreal.le (hOne.trans hLower)
  have hCLower : C ≤ (N : ℝ) := by
    calc
      C ≤ T^(1/U) := hC
      _ = (N : ℝ)^(tau*(1/U)) := by rw [← hScale, ← Real.rpow_mul hNpos.le]
      _ ≤ (N : ℝ)^1 := Real.rpow_le_rpow_of_exponent_le hNreal.le (by
        apply (mul_le_mul_of_nonneg_right hUpper (by positivity : 0 ≤ 1/U)).trans
        exact le_of_eq (by field_simp))
      _ = N := Real.rpow_one _
  have hPLower : 4 ≤ (N : ℝ)^(delta/2) := by
    calc
      4 ≤ T^(delta/(2*U)) := hPower
      _ = (N : ℝ)^(tau*(delta/(2*U))) := by rw [← hScale, ← Real.rpow_mul hNpos.le]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNreal.le (by
        apply (mul_le_mul_of_nonneg_right hUpper (by positivity : 0 ≤ delta/(2*U))).trans
        exact le_of_eq (by field_simp))
  exact ⟨hNUpper,hCLower,hPLower,by linarith [hNear.trans hLower],by linarith⟩

theorem eventually_classicalReflected_fourier_displacement_fits
    (d : ℝ) (hd : d < 1) :
    ∀ᶠ T : ℝ in Filter.atTop, 2*Real.pi*T^d ≤ T/4 := by
  have hconst := (tendsto_rpow_atTop (sub_pos.mpr hd)).eventually
    (Filter.eventually_ge_atTop (8*Real.pi))
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),hconst] with T hT hc
  have hm := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hT.le d)
  have heq : T^(1-d)*T^d = T := by
    rw [← Real.rpow_add hT, sub_add_cancel, Real.rpow_one]
  rw [heq] at hm
  linarith

end TaoTrudgianYang2025

