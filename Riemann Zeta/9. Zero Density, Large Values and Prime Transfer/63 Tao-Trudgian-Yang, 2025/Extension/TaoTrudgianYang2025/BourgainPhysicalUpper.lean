import TaoTrudgianYang2025.BourgainMixedUpper

/-!
# The mixed upper bound at the original physical height

For N <= L <= P.T and a small shift exponent, the actual integer slice
lies in an interval of length at most 8 P.T. The constant-factor height
enlargement is paid uniformly, before the pattern is chosen.
-/

open Finset MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_shift_window_le_scale {N ε : ℝ} (hN : 1 ≤ N) (hε : ε ≤ 8) :
    N^(ε/8) ≤ N := by
  calc
    _ ≤ N^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = N := Real.rpow_one N

theorem bourgain_slice_height_le_original (P : LargeValuePattern)
    {L ε : ℝ} (hNL : P.N ≤ L) (hLT : L ≤ P.T) (hε : ε ≤ 8) :
    2*((L+P.N^(ε/8)+1)+P.N^(ε/8)) ≤ 8*P.T := by
  have hH := bourgain_shift_window_le_scale P.one_lt_N.le hε
  linarith [P.one_lt_N]

theorem bourgainSecondBudget_eight_height {N T R : ℝ}
    (hN : 0 ≤ N) (hR : 0 ≤ R) :
    bourgainSecondBudget N (8*T) R ≤ 3*bourgainSecondBudget N T R := by
  have he : (8*T)^(1/2 : ℝ) ≤ 3*T^(1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    exact mul_le_mul_of_nonneg_right
      (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩ : Real.sqrt (8 : ℝ) ≤ 3)
      (Real.sqrt_nonneg T)
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hR (5/4))) hN
  unfold bourgainSecondBudget
  nlinarith [mul_nonneg (sq_nonneg R) hN, mul_nonneg hR (sq_nonneg N)]

/-- The actual mixed integral is bounded at P.T itself, with all geometric
and height-enlargement hypotheses discharged from the source subdivision. -/
theorem bourgain_physical_mixed_upper {θ : ℝ} (hθ : 0 < θ) :
    ∃ D E₀ : ℝ, 0 < D ∧ 1 ≤ E₀ ∧
      ∀ (P : LargeValuePattern) (S : Finset ℝ), S ⊆ P.ordinates →
      ∀ (L ε V u r : ℝ), E₀ ≤ P.N → P.N ≤ L → L ≤ P.T → ε ≤ 8 →
        u ∈ Icc (-(P.N^(ε/8))) (P.N^(ε/8)) → 0 ≤ r →
        (∫ v in -r..r, ∑ t ∈ S,
          ∑ ℓ ∈ bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1) V u,
            ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) ≤
          2*r*D*P.T^θ*
            (Real.sqrt (bourgainSecondBudget P.N P.T (S.card : ℝ))*
              Real.sqrt (bourgainSecondBudget P.N P.T
                ((bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1) V u).card : ℝ))) := by
  obtain ⟨C, E₀, hC, hE₀, hupper⟩ := bourgain_actual_mixed_upper hθ
  refine ⟨3*C*(8 : ℝ)^θ, E₀, by positivity, hE₀, ?_⟩
  intro P S hsub L ε V u r hEN hNL hLT hε hu hr
  have hN : 0 ≤ P.N := (zero_lt_one.trans P.one_lt_N).le
  have hT : 0 ≤ P.T := P.T_pos.le
  have hTE : P.T ≤ 8*P.T := by linarith
  have hE : E₀ ≤ 8*P.T := hEN.trans (hNL.trans (hLT.trans hTE))
  have hb := hupper P S hsub (P.N^(ε/8)) (L+P.N^(ε/8)+1) V u r (8*P.T)
    hu hr hE hTE (bourgain_slice_height_le_original P hNL hLT hε)
  let K := ((bourgainIntegerSlice (P.N^(ε/8)) (L+P.N^(ε/8)+1) V u).card : ℝ)
  have hS := bourgainSecondBudget_eight_height (T := P.T) hN (Nat.cast_nonneg S.card)
  have hK := bourgainSecondBudget_eight_height (T := P.T) hN (show 0 ≤ K from Nat.cast_nonneg _)
  have hprod := mul_le_mul (Real.sqrt_le_sqrt hS) (Real.sqrt_le_sqrt hK)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [bourgain_sqrt_common_factor (by norm_num : (0 : ℝ) ≤ 3)] at hprod
  have hfin := hb.trans (mul_le_mul_of_nonneg_left hprod
    (by positivity : 0 ≤ 2*r*C*(8*P.T)^θ))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hT] at hfin
  convert hfin using 1
  ring

/-- The constant-factor height enlargement is absorbed in a uniform scalar
coefficient, with both cardinalities still arbitrary. -/
theorem bourgain_mixed_budget_eight_height {N T R K D r θ : ℝ}
    (hN : 0 ≤ N) (hT : 0 ≤ T) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hD : 0 ≤ D) (hr : 0 ≤ r) :
    2*r*D*(8*T)^θ*
        (Real.sqrt (bourgainSecondBudget N (8*T) R)*
          Real.sqrt (bourgainSecondBudget N (8*T) K)) ≤
      2*r*(3*D*(8 : ℝ)^θ)*T^θ*
        (Real.sqrt (bourgainSecondBudget N T R)*
          Real.sqrt (bourgainSecondBudget N T K)) := by
  have h₁ := bourgainSecondBudget_eight_height (T := T) hN hR
  have h₂ := bourgainSecondBudget_eight_height (T := T) hN hK
  have hprod := mul_le_mul (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt h₂)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [bourgain_sqrt_common_factor (by norm_num : (0 : ℝ) ≤ 3)] at hprod
  have hfin := mul_le_mul_of_nonneg_left hprod
    (by positivity : 0 ≤ 2*r*D*(8*T)^θ)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hT] at hfin ⊢
  convert hfin using 1
  ring

end TaoTrudgianYang2025
