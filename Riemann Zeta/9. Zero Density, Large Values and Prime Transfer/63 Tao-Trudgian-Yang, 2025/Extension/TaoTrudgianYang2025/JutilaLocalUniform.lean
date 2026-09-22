import TaoTrudgianYang2025.JutilaLocalAlgebra

/-!
# The local Jutila cardinality estimate with a single epsilon loss

The uniform estimate consumes the actual source-pattern recurrence.
The high-value absorption condition remains explicit in physical N,T,V.
-/

open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Uniform local Jutila estimate on actual patterns. The displayed
physical threshold is derived from the recurrence's absorption term.
No large-values estimate is accepted as a premise. -/
theorem jutila_local_cardinality_uniform (cutoff : GMSmoothCutoff)
    (k : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 1 ≤ C ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        C*P.T^ε*P.N^(3*k) ≤ (P.V-1)^(4*k) →
        (P.ordinates.card : ℝ) ≤ C*P.T^ε*
          (P.N^2/(P.V-1)^2 +
            P.T^k*P.N^(2*k)/(P.V-1)^(4*k) +
            P.T*P.N^(6*k)/(P.V-1)^(8*k)) := by
  let ν := ε/3
  have hν : 0 < ν := by dsimp [ν]; positivity
  obtain ⟨B, T₀, hB, hT₀, hp⟩ := jutila_local_pattern_cardinality cutoff k hk hν
  let S : ℝ := 2*B*(4 : ℝ)^(2*k)*(2 : ℝ)^k*(3 : ℝ)^(4*k)
  let C₁ : ℝ := 72*B
  let C₂ : ℝ := 4*B^2*(4 : ℝ)^(2*k)*(3 : ℝ)^(4*k)
  let C₃ : ℝ := 4*B^3*(4 : ℝ)^(4*k)*(2 : ℝ)^(2*k)*(3 : ℝ)^(8*k)
  let C : ℝ := 1+S+C₁+C₂+C₃
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hC₃ : 0 ≤ C₃ := by dsimp [C₃]; positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hSC : S ≤ C := by dsimp [C]; linarith
  have h1C : C₁ ≤ C := by dsimp [C]; linarith
  have h2C : C₂ ≤ C := by dsimp [C]; linarith
  have h3C : C₃ ≤ C := by dsimp [C]; linarith
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro P hN hV hT hNT hvalue
  have hTp : 0 < P.T := P.T_pos
  have hT1 : 1 ≤ P.T := by linarith [hT₀.trans hT]
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hv : 0 < P.V-1 := by linarith
  have hnue : ν ≤ ε := by dsimp [ν]; linarith
  have h2nue : 2*ν ≤ ε := by dsimp [ν]; linarith
  have h3nue : 3*ν = ε := by dsimp [ν]; ring
  have ht1 := Real.rpow_le_rpow_of_exponent_le hT1 hnue
  have ht2 := Real.rpow_le_rpow_of_exponent_le hT1 h2nue
  have ha : 2*(B*P.T^ν*(4*P.N)^(2*k))*(2*P.N)^k ≤ ((P.V-1)/3)^(4*k) := by
    rw [div_pow]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 3^(4*k))).mpr
    rw [jutila_local_absorption_identity]
    change S*P.T^ν*P.N^(3*k) ≤ _
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul hSC ht1 (by positivity) (zero_le_one.trans hC)) (by positivity)).trans hvalue
  have hc := hp P hN hV hT hNT ha
  have hpow := jutila_local_smoothing_powers (B := B) (ν := ν) hTp
  let X := P.N^2/(P.V-1)^2
  let Y := P.T^k*P.N^(2*k)/(P.V-1)^(4*k)
  let Z := P.T*P.N^(6*k)/(P.V-1)^(8*k)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hform : jutilaLocalCardinalityBound k P.N P.T P.V (B*P.T^ν) =
      C₁*P.T^ν*X+C₂*P.T^(2*ν)*Y+C₃*P.T^(3*ν)*Z := by
    rw [jutila_local_cardinality_expand k P.N P.T P.V (B*P.T^ν) hV,
      hpow.1, hpow.2]
    dsimp [C₁, C₂, C₃, X, Y, Z]
    ring
  have h1 : C₁*P.T^ν ≤ C*P.T^ε :=
    mul_le_mul h1C ht1 (by positivity) (zero_le_one.trans hC)
  have h2 : C₂*P.T^(2*ν) ≤ C*P.T^ε :=
    mul_le_mul h2C ht2 (by positivity) (zero_le_one.trans hC)
  have h3 : C₃*P.T^(3*ν) ≤ C*P.T^ε := by
    rw [h3nue]
    exact mul_le_mul_of_nonneg_right h3C (by positivity)
  calc
    _ ≤ jutilaLocalCardinalityBound k P.N P.T P.V (B*P.T^ν) := hc
    _ = C₁*P.T^ν*X+C₂*P.T^(2*ν)*Y+C₃*P.T^(3*ν)*Z := hform
    _ ≤ C*P.T^ε*X+C*P.T^ε*Y+C*P.T^ε*Z := by gcongr
    _ = _ := by dsimp [X, Y, Z]; ring

end TaoTrudgianYang2025
