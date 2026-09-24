import TaoTrudgianYang2025.ClassicalReflectedThreshold

/-!
# Uniform absorption of the reflected source threshold loss

All constants and the physical height threshold are chosen before the
actual dyadic length. The logarithmic scale is linked to N and T.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem eventually_classicalReflected_threshold_absorbed
    (sigma loss delta U C : ℝ) (hloss : 0 ≤ loss)
    (hdelta : 0 < delta) (hU : 0 < U) (hC : 0 < C)
    (hLoss : U*loss ≤ delta/2) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (N : ℕ) (L : ℝ),
      1 < N → typeILogarithmicScale T N ≤ U →
      (N : ℝ)^sigma*T^(-loss)/C ≤ L →
      (N : ℝ)^(sigma-delta) ≤ L/(4*classicalTypeIFourierL1 (-sigma)) := by
  let mass := classicalTypeIFourierL1 (-sigma)
  have hmass : 0 < mass := classicalTypeIFourierL1_pos (-sigma)
  let K := 4*mass*C
  have hK : 0 < K := by dsimp [K]; positivity
  have hexponent : 0 < delta/(2*U) := by positivity
  have hconstant := (tendsto_rpow_atTop hexponent).eventually
    (Filter.eventually_ge_atTop K)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),hconstant] with T hT hTK
  intro N L hN hScaleUpper hL
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hNreal : 1 < (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNreal
  let tau := typeILogarithmicScale T N
  have hScale : (N : ℝ)^tau = T := rpow_typeILogarithmicScale_eq hTpos hN
  have hdeltaScale : tau*(delta/(2*U)) ≤ delta/2 := by
    apply (mul_le_mul_of_nonneg_right hScaleUpper hexponent.le).trans
    exact le_of_eq (by field_simp)
  have hKBound : K ≤ (N : ℝ)^(delta/2) := by
    calc
      K ≤ T^(delta/(2*U)) := hTK
      _ = (N : ℝ)^(tau*(delta/(2*U))) := by rw [← hScale, ← Real.rpow_mul hNpos.le]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNreal.le hdeltaScale
  have hTBound : T^loss ≤ (N : ℝ)^(delta/2) := by
    calc
      T^loss = (N : ℝ)^(tau*loss) := by rw [← hScale, ← Real.rpow_mul hNpos.le]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hNreal.le
        ((mul_le_mul_of_nonneg_right hScaleUpper hloss).trans hLoss)
  have hProduct : K*T^loss ≤ (N : ℝ)^delta := by
    calc
      K*T^loss ≤ (N : ℝ)^(delta/2)*(N : ℝ)^(delta/2) :=
        mul_le_mul hKBound hTBound (Real.rpow_nonneg hTpos.le _) (by positivity)
      _ = (N : ℝ)^delta := by rw [← Real.rpow_add hNpos]; congr 1; ring
  calc
    (N : ℝ)^(sigma-delta) = (N : ℝ)^sigma/(N : ℝ)^delta :=
      Real.rpow_sub hNpos _ _
    _ ≤ (N : ℝ)^sigma/(K*T^loss) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hNpos.le _)
        (mul_pos hK (Real.rpow_pos_of_pos hTpos _)) hProduct
    _ = ((N : ℝ)^sigma*T^(-loss)/C)/(4*mass) := by
      rw [Real.rpow_neg hTpos.le]
      dsimp [K]
      field_simp
    _ ≤ L/(4*mass) := div_le_div_of_nonneg_right hL (by positivity)

end TaoTrudgianYang2025

