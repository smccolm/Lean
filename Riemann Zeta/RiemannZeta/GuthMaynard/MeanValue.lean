import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.PolynomialPowers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Complex Finset

namespace RiemannZeta.GuthMaynard

/--
F-10.1: Core Montgomery Mean Value Theorem
* Points are 1-separated (IsSeparated 1 W).
* The line is \Re(s) = 0, evaluated at `t * I`.
* Support convention: the polynomial is supported in `(M1, M2]`.
* The bound is `T + M`, where `M = M2 - M1`.
* Coefficients are arbitrary `a : ℕ → ℂ`.
* Applied to one dyadic block of D^k.
* Constant dependencies: there exists a constant `C > 0`.
-/
def MontgomeryMeanValue : Prop :=
  ∃ C > (0 : ℝ), ∀ (M1 M2 : ℕ) (T0 T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
    1 ≤ T →
    M1 ≤ M2 →
    IsSeparated 1 W →
    (∀ x ∈ W, x ∈ Set.Icc T0 (T0 + T)) →
    ∑ t ∈ W, ‖∑ m ∈ Ioc M1 M2, a m * (m : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2 ≤
      C * (T + (M2 - M1 : ℝ)) * ∑ m ∈ Ioc M1 M2, ‖a m‖ ^ 2

/-- F-10: Mean-value bound hypothesis for powers of the Dirichlet polynomial.
    This is the exact specific variant consumed by the zero density transfer. -/
def MeanValueHypothesis (detector : ZeroDetectorModel) (powerModel : ∀ k, PolynomialPowerModel detector k) : Prop :=
  ∃ (C : ℝ), ∀ (N : ℕ) (k : ℕ) (V T : ℝ) (W : Finset ℝ),
    0 < N → 1 ≤ T → 0 < V →
    IsSeparated 1 W →
    InTargetInterval T W →
    (∀ t ∈ W, V^k ≤ ‖(powerModel k).powPoly N (t * I)‖) →
    (W.card : ℝ) ≤ C * (T + ((2 * N)^k - N^k : ℝ)) * V^(-2 * (k : ℝ)) * ∑ m ∈ Ioc (N^k) ((2*N)^k), ‖(powerModel k).powCoeff N m‖^2

lemma mean_value_reduction (detector : ZeroDetectorModel) (powerModel : ∀ k, PolynomialPowerModel detector k)
    (h_mont : MontgomeryMeanValue) : MeanValueHypothesis detector powerModel := by
  rcases h_mont with ⟨C, hC_pos, h_mont_bound⟩
  use C
  intro N k V T W hN hT hV hSep hTarget h_lower
  
  let M1 := N^k
  let M2 := (2*N)^k
  have hM1_le_M2 : M1 ≤ M2 := by
    apply Nat.pow_le_pow_left
    omega
  
  let a := (powerModel k).powCoeff N
  have h_base : ∀ x ∈ W, x ∈ Set.Icc T (T + T) := by
    intro x hx
    have hx_tgt := hTarget x hx
    rw [Set.mem_Icc] at hx_tgt ⊢
    constructor
    · exact hx_tgt.1
    · linarith [hx_tgt.2]

  have h_bound := h_mont_bound M1 M2 T T W a hT hM1_le_M2 hSep h_base
  
  have h_sum_lower : (W.card : ℝ) * (V^k)^2 ≤ ∑ t ∈ W, ‖∑ m ∈ Ioc M1 M2, a m * (m : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2 := by
    calc (W.card : ℝ) * (V^k)^2 = ∑ t ∈ W, (V^k)^2 := by simp
      _ ≤ ∑ t ∈ W, ‖∑ m ∈ Ioc M1 M2, a m * (m : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2 := by
        apply sum_le_sum
        intro t ht
        have hl := h_lower t ht
        -- unfold powPoly to match the sum
        change V^k ≤ ‖∑ m ∈ Ioc M1 M2, a m * (m : ℂ) ^ (-(t : ℂ) * I)‖ at hl
        have hp : 0 ≤ V^k := by positivity
        nlinarith [hl]

  have hl2 : (W.card : ℝ) * (V^k)^2 ≤ C * (T + (M2 - M1 : ℝ)) * ∑ m ∈ Ioc M1 M2, ‖a m‖ ^ 2 := by
    linarith [h_sum_lower, h_bound]
    
  have hpV : 0 < (V^k)^2 := by positivity
  
  have hpV2 : (V^k)^2 = V ^ (2 * (k : ℝ)) := by
    have h1 : (V^k)^2 = V ^ (2 * k) := by ring
    have h2 : V ^ (2 * k) = V ^ (2 * (k : ℝ)) := by
      rw [Real.rpow_natCast]
      push_cast
      rfl
    exact h1.trans h2

  rw [hpV2] at hl2
  have h_div : (W.card : ℝ) ≤ C * (T + (M2 - M1 : ℝ)) * ∑ m ∈ Ioc M1 M2, ‖a m‖ ^ 2 / V ^ (2 * (k : ℝ)) := by
    -- We can divide by V^(2k) because it's positive.
    have hpV3 : 0 < V ^ (2 * (k : ℝ)) := by rw [←hpV2]; exact hpV
    exact (le_div_iff₀ hpV3).mpr hl2
    
  have h_div2 : C * (T + (M2 - M1 : ℝ)) * ∑ m ∈ Ioc M1 M2, ‖a m‖ ^ 2 / V ^ (2 * (k : ℝ)) = C * (T + (M2 - M1 : ℝ)) * V ^ (-2 * (k : ℝ)) * ∑ m ∈ Ioc M1 M2, ‖a m‖ ^ 2 := by
    -- 1 / x = x⁻¹ and x⁻¹ = x^(-1) for rpow.
    have h_inv : 1 / V ^ (2 * (k : ℝ)) = V ^ (-2 * (k : ℝ)) := by
      rw [one_div, ←Real.rpow_neg (le_of_lt hV)]
    calc C * (T + (M2 - M1 : ℝ)) * ∑ m ∈ Ioc M1 M2, ‖a m‖ ^ 2 / V ^ (2 * (k : ℝ))
      _ = C * (T + (M2 - M1 : ℝ)) * ∑ m ∈ Ioc M1 M2, ‖a m‖ ^ 2 * (1 / V ^ (2 * (k : ℝ))) := by ring
      _ = C * (T + (M2 - M1 : ℝ)) * ∑ m ∈ Ioc M1 M2, ‖a m‖ ^ 2 * V ^ (-2 * (k : ℝ)) := by rw [h_inv]
      _ = C * (T + (M2 - M1 : ℝ)) * V ^ (-2 * (k : ℝ)) * ∑ m ∈ Ioc M1 M2, ‖a m‖ ^ 2 := by ring
  
  rw [h_div2] at h_div
  
  have hM2M1 : (M2 - M1 : ℝ) = (2 * N)^k - N^k := by
    have h1 : (M2 : ℝ) = ((2 * N)^k : ℝ) := rfl
    have h2 : (M1 : ℝ) = (N^k : ℝ) := rfl
    rw [h1, h2]
    exact Nat.cast_sub hM1_le_M2

  rw [hM2M1] at h_div
  exact h_div

end RiemannZeta.GuthMaynard
