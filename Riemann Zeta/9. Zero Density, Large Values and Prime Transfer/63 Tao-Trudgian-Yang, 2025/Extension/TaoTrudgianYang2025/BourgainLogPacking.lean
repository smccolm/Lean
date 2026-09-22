import TaoTrudgianYang2025.BourgainComparisonLogarithm

/-!
# The original cardinality after finite selection, in logarithmic form

The three small-component powers become exactly the first frozen Bourgain
maximum. The retained-set loss stays visible in the original-count bound.
-/

noncomputable section

namespace TaoTrudgianYang2025

def bourgainSmallExponent (σ τ α χ : ℝ) : ℝ :=
  max (max (χ+2-2*σ) (-χ+2*τ+4-8*σ)) (-2*α+τ+12-16*σ)

theorem bourgain_small_component_power {N C σ τ α χ ε : ℝ}
    (hN : 1 ≤ N) (hC : 0 ≤ C) :
    2*N^χ*(C*(N^(2-2*σ+ε)+N^(2*(τ-χ)+4-8*σ+ε)+
      N^(-2*α+(τ-χ)+12-16*σ+ε))) ≤
      6*C*N^(bourgainSmallExponent σ τ α χ+ε) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hp₁ : N^(χ+(2-2*σ+ε)) ≤ N^(bourgainSmallExponent σ τ α χ+ε) :=
    Real.rpow_le_rpow_of_exponent_le hN (by
      have h : χ+2-2*σ ≤ bourgainSmallExponent σ τ α χ :=
        (le_max_left _ _).trans (le_max_left _ _)
      linarith)
  have hp₂ : N^(χ+(2*(τ-χ)+4-8*σ+ε)) ≤ N^(bourgainSmallExponent σ τ α χ+ε) :=
    Real.rpow_le_rpow_of_exponent_le hN (by
      have h : -χ+2*τ+4-8*σ ≤ bourgainSmallExponent σ τ α χ :=
        (le_max_right _ _).trans (le_max_left _ _)
      linarith)
  have hp₃ : N^(χ+(-2*α+(τ-χ)+12-16*σ+ε)) ≤ N^(bourgainSmallExponent σ τ α χ+ε) :=
    Real.rpow_le_rpow_of_exponent_le hN (by
      have h : -2*α+τ+12-16*σ ≤ bourgainSmallExponent σ τ α χ := le_max_right _ _
      linarith)
  have hsum := add_le_add (add_le_add hp₁ hp₂) hp₃
  have hscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*C by positivity)
  simp only [Real.rpow_add hNp] at hscaled ⊢
  nlinarith

theorem bourgain_logb_two_power_sum {N A B : ℝ}
    (hN : 1 < N) (hA : 0 < A) (hB : 0 < B) (p q : ℝ) :
    Real.logb N (A*N^p+B*N^q) ≤ Real.logb N (A+B)+max p q := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hp : N^p ≤ N^(max p q) :=
    Real.rpow_le_rpow_of_exponent_le hN.le (le_max_left _ _)
  have hq : N^q ≤ N^(max p q) :=
    Real.rpow_le_rpow_of_exponent_le hN.le (le_max_right _ _)
  have hbound : A*N^p+B*N^q ≤ (A+B)*N^(max p q) := by
    nlinarith [mul_le_mul_of_nonneg_left hp hA.le, mul_le_mul_of_nonneg_left hq hB.le]
  have hlog := Real.logb_le_logb_of_le hN (by positivity) hbound
  rwa [Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hNp _).ne',
    Real.logb_rpow hNp hN.ne'] at hlog

/-- The finite original-count selection estimate gives the exact logarithmic
max bound; R remains the actual retained cardinality when consumed downstream. -/
theorem bourgain_original_count_log_bound {N Q R C H σ τ α χ ε κ : ℝ}
    (hN : 1 < N) (hQ : 0 < Q) (hR : 0 < R) (hC : 0 < C) (hH : 0 < H)
    (hpack : Q ≤ 2*N^χ*(C*(N^(2-2*σ+ε)+N^(2*(τ-χ)+4-8*σ+ε)+
      N^(-2*α+(τ-χ)+12-16*σ+ε)))+C*H*N^(ε+κ)*R) :
    Real.logb N Q ≤ Real.logb N (6*C+C*H)+
      max (bourgainSmallExponent σ τ α χ+ε) (ε+κ+Real.logb N R) := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hs := bourgain_small_component_power (σ := σ) (τ := τ)
    (α := α) (χ := χ) (ε := ε) hN.le hC.le
  have heq : C*H*N^(ε+κ)*R = C*H*N^(ε+κ+Real.logb N R) := by
    rw [Real.rpow_add hNp (ε+κ) (Real.logb N R), Real.rpow_logb hNp hN.ne' hR]
    ring
  have hbound : Q ≤ 6*C*N^(bourgainSmallExponent σ τ α χ+ε)+
      C*H*N^(ε+κ+Real.logb N R) := by
    calc
      _ ≤ 6*C*N^(bourgainSmallExponent σ τ α χ+ε)+C*H*N^(ε+κ)*R :=
        hpack.trans (add_le_add hs le_rfl)
      _ = _ := by rw [heq]
  exact (Real.logb_le_logb_of_le hN hQ hbound).trans
    (bourgain_logb_two_power_sum hN (by positivity) (by positivity) _ _)

theorem bourgain_small_original_log_bound {N Q C σ τ α χ ε : ℝ}
    (hN : 1 < N) (hQ : 0 < Q) (hC : 0 < C)
    (hsmall : Q ≤ 2*N^χ*(C*(N^(2-2*σ+ε)+N^(2*(τ-χ)+4-8*σ+ε)+
      N^(-2*α+(τ-χ)+12-16*σ+ε)))) :
    Real.logb N Q ≤ bourgainSmallExponent σ τ α χ+ε+Real.logb N (6*C) := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hbound := hsmall.trans (bourgain_small_component_power hN.le hC.le)
  have hlog := Real.logb_le_logb_of_le hN hQ hbound
  rw [Real.logb_mul (by positivity) (Real.rpow_pos_of_pos hNp _).ne',
    Real.logb_rpow hNp hN.ne'] at hlog
  linarith

end TaoTrudgianYang2025
