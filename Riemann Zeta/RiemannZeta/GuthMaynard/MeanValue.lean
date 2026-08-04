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
    ∑ t ∈ W, ‖∑ m ∈ Icc M1 M2, a m * (m : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2 ≤
      C * (T + (M2 - M1 : ℝ)) * ∑ m ∈ Icc M1 M2, ‖a m‖ ^ 2

/-- F-10: Mean-value bound hypothesis for powers of the Dirichlet polynomial.
    This is the exact specific variant consumed by the zero density transfer. -/
def MeanValueHypothesis : Prop :=
  ∃ (C : ℝ), ∀ (N : ℕ) (k : ℕ) (V T : ℝ) (W : Finset ℝ),
    0 < N → 1 ≤ T → 0 < V →
    IsSeparated 1 W →
    InTargetInterval T W →
    (∀ t ∈ W, V^k ≤ ‖powPoly N k (t * I)‖) →
    (W.card : ℝ) ≤ C * (T + ((2 * N)^k - N^k : ℝ)) * V^(-2 * (k : ℝ)) * ∑ m ∈ Icc (N^k) ((2*N)^k), ‖powCoeff N k m‖^2

lemma mean_value_reduction
    (h_mont : MontgomeryMeanValue) : MeanValueHypothesis := by
  rcases h_mont with ⟨C, hC_pos, h_mont_bound⟩
  use C
  intro N k V T W hN hT hV hSep hTarget h_lower
  
  let M1 := N^k
  let M2 := (2*N)^k
  have hM1_le_M2 : M1 ≤ M2 := by
    apply Nat.pow_le_pow_left
    omega
  
  let a := powCoeff N k
  have h_base : ∀ x ∈ W, x ∈ Set.Icc T (T + T) := by
    intro x hx
    have hx_tgt := hTarget x hx
    rw [Set.mem_Icc] at hx_tgt ⊢
    constructor
    · exact hx_tgt.1
    · linarith [hx_tgt.2]

  have h_bound := h_mont_bound M1 M2 T T W a hT hM1_le_M2 hSep h_base
  
  have h_sum_lower : (W.card : ℝ) * (V^k)^2 ≤ ∑ t ∈ W, ‖∑ m ∈ Icc M1 M2, a m * (m : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2 := by
    calc (W.card : ℝ) * (V^k)^2 = ∑ t ∈ W, (V^k)^2 := by simp
      _ ≤ ∑ t ∈ W, ‖∑ m ∈ Icc M1 M2, a m * (m : ℂ) ^ (-(t : ℂ) * I)‖ ^ 2 := by
        apply sum_le_sum
        intro t ht
        have hl := h_lower t ht
        have h_neg : -(t : ℂ) * I = -((t : ℂ) * I) := by ring
        have h_eq : powPoly N k (t * I) = ∑ m ∈ Icc M1 M2, a m * (m : ℂ) ^ (-(t : ℂ) * I) := by
          dsimp [powPoly, a, M1, M2]
          apply Finset.sum_congr rfl
          intro m hm
          rw [h_neg]
        rw [←h_eq]
        have hp : 0 ≤ V^k := by positivity
        nlinarith [hl]

  have hl2 : (W.card : ℝ) * (V^k)^2 ≤ C * (T + (M2 - M1 : ℝ)) * ∑ m ∈ Icc M1 M2, ‖a m‖ ^ 2 := by
    linarith [h_sum_lower, h_bound]
    
  have hpV : 0 < (V^k)^2 := by positivity
  
  have hpV2 : (V^k)^2 = V ^ (2 * (k : ℝ)) := by
    have h1 : (V^k)^2 = V ^ (2 * k) := by ring
    have h2 : V ^ (2 * k) = V ^ (2 * (k : ℝ)) := by
      have h3 : V ^ (2 * k) = V ^ ((2 * k : ℕ) : ℝ) := Real.rpow_natCast V (2 * k) |>.symm
      have h4 : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; rfl
      rw [h4] at h3
      exact h3
    rw [h1, h2]

  rw [hpV2] at hl2
  have h_div : (W.card : ℝ) ≤ C * (T + (M2 - M1 : ℝ)) * (∑ m ∈ Icc M1 M2, ‖a m‖ ^ 2) / V ^ (2 * (k : ℝ)) := by
    have hpV3 : 0 < V ^ (2 * (k : ℝ)) := by rw [←hpV2]; exact hpV
    exact (le_div_iff₀ hpV3).mpr hl2
    
  have h_div2 : C * (T + (M2 - M1 : ℝ)) * (∑ m ∈ Icc M1 M2, ‖a m‖ ^ 2) / V ^ (2 * (k : ℝ)) = C * (T + (M2 - M1 : ℝ)) * V ^ (-2 * (k : ℝ)) * (∑ m ∈ Icc M1 M2, ‖a m‖ ^ 2) := by
    have h_inv : 1 / V ^ (2 * (k : ℝ)) = V ^ (-(2 * (k : ℝ))) := by
      rw [one_div, ←Real.rpow_neg (le_of_lt hV)]
    have h_neg : -(2 * (k : ℝ)) = -2 * (k : ℝ) := by ring
    rw [h_neg] at h_inv
    calc C * (T + (M2 - M1 : ℝ)) * (∑ m ∈ Icc M1 M2, ‖a m‖ ^ 2) / V ^ (2 * (k : ℝ))
      _ = C * (T + (M2 - M1 : ℝ)) * (∑ m ∈ Icc M1 M2, ‖a m‖ ^ 2) * (1 / V ^ (2 * (k : ℝ))) := by ring
      _ = C * (T + (M2 - M1 : ℝ)) * (∑ m ∈ Icc M1 M2, ‖a m‖ ^ 2) * V ^ (-2 * (k : ℝ)) := by rw [h_inv]
      _ = C * (T + (M2 - M1 : ℝ)) * V ^ (-2 * (k : ℝ)) * (∑ m ∈ Icc M1 M2, ‖a m‖ ^ 2) := by ring
  
  rw [h_div2] at h_div
  
  have hM2M1 : (M2 - M1 : ℝ) = ((2 * N)^k - N^k : ℝ) := by
    exact_mod_cast rfl

  rw [hM2M1] at h_div
  exact h_div

end RiemannZeta.GuthMaynard
