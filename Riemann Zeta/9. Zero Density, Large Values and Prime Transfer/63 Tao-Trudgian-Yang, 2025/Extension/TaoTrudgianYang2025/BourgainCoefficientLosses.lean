import TaoTrudgianYang2025.BourgainCoefficientIdentity
import TaoTrudgianYang2025.BourgainComparisonLogLoss
import TaoTrudgianYang2025.BourgainPhysicalUpper

/-!
# Uniform power losses for the actual level-free coefficients

Both lower bounds follow from the literal finite denominators. The loss
records the window, height slack, fourth-moment exponent and logarithms.
-/

noncomputable section

namespace TaoTrudgianYang2025

def bourgainComparisonLoss (τ ε δ η : ℝ) : ℝ :=
  ε/4+η+δ+(τ+δ)*ε

theorem bourgain_window_ceiling_product {N ε : ℝ}
    (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    N^(ε/8)*((2*Nat.ceil (N^(ε/8))+1 : ℕ) : ℝ) ≤ 5*N^(ε/4) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hh : 1 ≤ N^(ε/8) := Real.one_le_rpow hN (by positivity)
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (ε/8))
  have hk : ((2*Nat.ceil (N^(ε/8))+1 : ℕ) : ℝ) ≤ 5*N^(ε/8) := by
    push_cast
    linarith
  calc
    _ ≤ N^(ε/8)*(5*N^(ε/8)) := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = 5*N^(ε/8+ε/8) := by rw [Real.rpow_add hNp]; ring
    _ = 5*N^(ε/4) := by congr 2; ring

theorem bourgain_local_height_power {N L τ ε δ : ℝ}
    (hN : 1 ≤ N) (hNL : N ≤ L) (hε : 0 ≤ ε) (hε₈ : ε ≤ 8)
    (hL : L ≤ N^(τ+δ)) :
    (L+N^(ε/8)+1)^(1+ε) ≤ (3 : ℝ)^(1+ε)*N^((τ+δ)*(1+ε)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hh := bourgain_shift_window_le_scale hN hε₈
  have hU : 0 ≤ L+N^(ε/8)+1 := by have hLp := hNp.trans_le hNL; positivity
  have hcap : L+N^(ε/8)+1 ≤ 3*N^(τ+δ) := by linarith
  calc
    _ ≤ (3*N^(τ+δ))^(1+ε) := Real.rpow_le_rpow hU hcap (by positivity)
    _ = (3 : ℝ)^(1+ε)*N^((τ+δ)*(1+ε)) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNp.le _),
        ← Real.rpow_mul hNp.le]

/-- Constants are uniform in the actual scale, local height and height slack.
The exact two coefficients are estimated together, not supplied as premises. -/
theorem bourgain_comparison_coefficients_uniform_power {B C α τ ε η : ℝ}
    (hB : 0 < B) (hC : 0 < C) (hε : 0 ≤ ε) (hε₈ : ε ≤ 8) (hη : 0 < η) :
    ∃ G N₀ : ℝ, 0 < G ∧ 2 ≤ N₀ ∧ ∀ N L δ : ℝ,
      N₀ ≤ N → N ≤ L → δ ≤ 1 → L ≤ N^(τ+δ) →
      N^(-2*α-bourgainComparisonLoss τ ε δ η)/G ≤
        bourgainEliminatedCardCoefficient N L B C τ α ε ∧
      N^(-α-bourgainComparisonLoss τ ε δ η/2)/Real.sqrt G ≤
        bourgainSliceSqrtCoefficient N L B C τ α ε 1 := by
  obtain ⟨D, N₀, hD, hN₀, hlogs⟩ :=
    bourgain_comparison_logs_uniform_power (B := B) (α := α) (τ := τ)
      hB hε (half_pos hη)
  let G := 163840*D^2*C*(3 : ℝ)^(1+ε)
  have hG : 0 < G := by dsimp only [G]; positivity
  refine ⟨G, N₀, hG, hN₀, ?_⟩
  intro N L δ hN hNL hδ hL
  have hN1 : 1 ≤ N := (by norm_num : (1 : ℝ) ≤ 2).trans (hN₀.trans hN)
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have hLp : 0 < L := hNp.trans_le hNL
  let Z := bourgainDifferenceLogLoss N τ
  let J := (bourgainZetaBandCount B (L+N^(ε/8)+1)
    (N^(-bourgainSharedFloorExponent α τ ε)) : ℝ)
  let K := ((2*Nat.ceil (N^(ε/8))+1 : ℕ) : ℝ)
  let U := L+N^(ε/8)+1
  have hZ : 0 < Z := bourgainDifferenceLogLoss_pos hN1 τ
  have hJ : 0 < J := by
    dsimp only [J]
    exact_mod_cast bourgainZetaBandCount_pos B U (N^(-bourgainSharedFloorExponent α τ ε))
  have hK : 0 < K := by dsimp only [K]; positivity
  have hU : 0 < U := by dsimp only [U]; positivity
  have hzj : Z^2*J^2 ≤ D^2*N^η := by
    calc
      _ = (Z*J)^2 := by ring
      _ ≤ (D*N^(η/2))^2 := pow_le_pow_left₀ (by positivity)
        (hlogs N L δ hN hLp.le hδ hL) 2
      _ = D^2*N^η := by
        rw [mul_pow, ← Real.rpow_mul_natCast hNp.le]
        congr 2
        norm_num
  have hwin : N^(ε/8)*K ≤ 5*N^(ε/4) := bourgain_window_ceiling_product hN1 hε
  have hheight : U^(1+ε) ≤ (3 : ℝ)^(1+ε)*N^((τ+δ)*(1+ε)) :=
    bourgain_local_height_power hN1 hNL hε hε₈ hL
  have hden : 0 < 32768*N^(ε/8)*K*Z^2*J^2*C*U^(1+ε) := by positivity
  have hbound : 32768*N^(ε/8)*K*Z^2*J^2*C*U^(1+ε) ≤
      G*N^(τ+bourgainComparisonLoss τ ε δ η) := by
    calc
      _ = 32768*(N^(ε/8)*K)*(Z^2*J^2)*C*U^(1+ε) := by ring
      _ ≤ 32768*(5*N^(ε/4))*(D^2*N^η)*C*
          ((3 : ℝ)^(1+ε)*N^((τ+δ)*(1+ε))) := by gcongr
      _ = G*N^(ε/4+η+(τ+δ)*(1+ε)) := by
        rw [Real.rpow_add hNp, Real.rpow_add hNp]
        dsimp only [G]
        ring
      _ = G*N^(τ+bourgainComparisonLoss τ ε δ η) := by
        congr 2
        unfold bourgainComparisonLoss
        ring
  have hcard : N^(-2*α-bourgainComparisonLoss τ ε δ η)/G ≤
      bourgainEliminatedCardCoefficient N L B C τ α ε := by
    change _ ≤ N^(-2*α)*N^τ/(32768*N^(ε/8)*K*Z^2*J^2*C*U^(1+ε))
    calc
      _ = N^(-2*α)*N^τ/(G*N^(τ+bourgainComparisonLoss τ ε δ η)) := by
        rw [Real.rpow_sub hNp, Real.rpow_add hNp]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden hbound
  refine ⟨hcard, ?_⟩
  rw [bourgain_slice_sqrt_coefficient_eq_sqrt hN1 hLp hC.le]
  have hs : Real.sqrt (N^(-2*α-bourgainComparisonLoss τ ε δ η)) =
      N^(-α-bourgainComparisonLoss τ ε δ η/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNp.le]
    congr 1
    ring
  calc
    _ = Real.sqrt (N^(-2*α-bourgainComparisonLoss τ ε δ η)/G) := by
      rw [Real.sqrt_div (Real.rpow_nonneg hNp.le _), hs]
    _ ≤ _ := Real.sqrt_le_sqrt hcard

end TaoTrudgianYang2025
