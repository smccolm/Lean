import TaoTrudgianYang2025.AtkinsonPairGramRows
import TaoTrudgianYang2025.AtkinsonPhysicalBudget

/-! Exact nominal powers for the general-pair Atkinson packet budget. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem atkinson_pair_epsilon_loss {H M L k l ε : ℝ}
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hMH : M ≤ H)
    (hL : 0 < L) (hLH : L ≤ H) (hε : 0 ≤ ε) :
    (L/Real.sqrt (H*M))^(k+ε)*M^(l+ε) ≤
      H^(2*ε)*((L/Real.sqrt (H*M))^k*M^l) := by
  have hH0 : 0 < H := by linarith
  have hM0 : 0 < M := by linarith
  have hs : 1 ≤ Real.sqrt (H*M) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith
  have hx : 0 < L/Real.sqrt (H*M) := by positivity
  have hxH : L/Real.sqrt (H*M) ≤ H :=
    (div_le_iff₀ (by positivity)).2 (by nlinarith)
  have he := mul_le_mul
    (Real.rpow_le_rpow hx.le hxH hε)
    (Real.rpow_le_rpow hM0.le hMH hε) (by positivity) (by positivity)
  have hpow : H^ε*H^ε = H^(2*ε) := by
    rw [← Real.rpow_add hH0]; congr 1; ring
  rw [hpow] at he
  rw [Real.rpow_add hx,Real.rpow_add hM0]
  calc
    _ = ((L/Real.sqrt (H*M))^ε*M^ε)*
        ((L/Real.sqrt (H*M))^k*M^l) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he (by positivity)

theorem atkinson_weighted_pair_power {H M : ℝ}
    (hH : 0 < H) (hM : 0 < M) {L : ℝ} (hL : 0 ≤ L) (k l : ℝ) :
    M^(1/2:ℝ)*((L/Real.sqrt (H*M))^k*M^l) =
      L^k*H^(-k/2)*M^(l+1/2-k/2) := by
  rw [Real.div_rpow hL (by positivity),Real.sqrt_eq_rpow,
    Real.mul_rpow hH.le hM.le,Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hH.le,← Real.rpow_mul hM.le]
  have hh : (H^((1/2:ℝ)*k))⁻¹ = H^(-k/2) := by
    rw [← Real.rpow_neg hH.le]; congr 1; ring
  have hm : M^(1/2:ℝ)*M^l/M^((1/2:ℝ)*k) =
      M^(l+1/2-k/2) := by
    rw [← Real.rpow_add hM,← Real.rpow_sub hM]
    congr 1
    ring
  calc
    _ = L^k*(H^((1/2:ℝ)*k))⁻¹*
        (M^(1/2:ℝ)*M^l/M^((1/2:ℝ)*k)) := by ring
    _ = _ := by rw [hh,hm]

def atkinsonPairPowerTerm (C k l H G L : ℝ) (N R : ℕ) : ℝ :=
  (R : ℝ)*(N : ℝ)^(3/2:ℝ)+
    C*(R : ℝ)^2*L^k*H^(-k/2)*(N : ℝ)^(l+1/2-k/2)+
    (2*C*(R : ℝ)*Real.sqrt H/G)*(N : ℝ)*
      (harmonic (Nat.ceil (L/G)) : ℝ)

def atkinsonPairPowerBudget (C k l H G L : ℝ) (N R : ℕ) : ℝ :=
  (Nat.clog 2 N : ℝ)^2*atkinsonPairPowerTerm C k l H G L N R

theorem atkinson_pair_power_term_eq {H : ℝ} {M : ℕ}
    (hH : 0 < H) (hM : 0 < M) {L : ℝ} (hL : 0 ≤ L)
    (C k l G : ℝ) (R : ℕ) :
    (M : ℝ)^(1/2:ℝ)*
      ((R : ℝ)*(M : ℝ)+C*(R : ℝ)^2*
        ((L/Real.sqrt (H*(M : ℝ)))^k*(M : ℝ)^l)+
        (2*C*Real.sqrt (H*(M : ℝ))/G)*(R : ℝ)*
          (harmonic (Nat.ceil (L/G)) : ℝ)) =
      atkinsonPairPowerTerm C k l H G L M R := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hd := atkinson_weighted_diagonal_power hM0 0
  have hn := atkinson_weighted_near_power hH hM0 0
  simp only [add_zero,Real.rpow_one] at hd hn
  have hf := atkinson_weighted_pair_power hH hM0 hL k l
  calc
    _ = (R : ℝ)*((M : ℝ)^(1/2:ℝ)*(M : ℝ))+
        C*(R : ℝ)^2*((M : ℝ)^(1/2:ℝ)*
          ((L/Real.sqrt (H*(M : ℝ)))^k*(M : ℝ)^l))+
        (2*C*(R : ℝ)/G)*((M : ℝ)^(1/2:ℝ)*Real.sqrt (H*(M : ℝ)))*
          (harmonic (Nat.ceil (L/G)) : ℝ) := by ring
    _ = _ := by rw [hd,hn,hf]; unfold atkinsonPairPowerTerm; ring

theorem atkinsonPairPowerTerm_nonneg {C H G L : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (k l : ℝ) (N R : ℕ) :
    0 ≤ atkinsonPairPowerTerm C k l H G L N R := by
  unfold atkinsonPairPowerTerm
  have hh : (0 : ℝ) ≤ (harmonic (Nat.ceil (L/G)) : ℝ) := by
    simpa only [harmonic_zero,Rat.cast_zero] using
      atkinson_harmonic_mono (Nat.zero_le (Nat.ceil (L/G)))
  positivity

theorem atkinsonPairPowerTerm_mono_index {C H G L k l : ℝ} {M N : ℕ}
    (R : ℕ) (hC : 0 ≤ C) (hH : 0 ≤ H) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hp : 0 ≤ l+1/2-k/2) (hMN : M ≤ N) :
    atkinsonPairPowerTerm C k l H G L M R ≤
      atkinsonPairPowerTerm C k l H G L N R := by
  have hMN0 : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hh : (0 : ℝ) ≤ (harmonic (Nat.ceil (L/G)) : ℝ) := by
    simpa only [harmonic_zero,Rat.cast_zero] using
      atkinson_harmonic_mono (Nat.zero_le (Nat.ceil (L/G)))
  unfold atkinsonPairPowerTerm
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg M) hMN0 (by norm_num))
        (Nat.cast_nonneg R)
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg M) hMN0 hp) (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMN0 (by positivity)) hh

theorem atkinsonPairPowerBudget_zero_card (C k l H G L : ℝ) (N : ℕ) :
    atkinsonPairPowerBudget C k l H G L N 0 = 0 := by
  simp [atkinsonPairPowerBudget,atkinsonPairPowerTerm]

end TaoTrudgianYang2025
