import TaoTrudgianYang2025.SargosQuarticBoundedMoment

/-! Localization of the actual full sixth moment, without a maximal-completion loss. -/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

def sargosSixthInitialMoment (N : ℕ) (A : ℝ) : ℝ :=
  ∫ α in Icc (0 : ℝ) A, ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
    ‖sargosQuarticSum N (fun _ => 1) α γ‖^6

theorem sargosSixthInitialMoment_nonneg (N : ℕ) (A : ℝ) :
    0 ≤ sargosSixthInitialMoment N A :=
  integral_nonneg (fun _α => integral_nonneg (fun _γ => pow_nonneg (norm_nonneg _) 6))

theorem sargosSixthInitialMoment_small {N : ℕ} (hN : 1 ≤ N) :
    sargosSixthInitialMoment N (1/Real.sqrt N) ≤
      44845498368*(1+Real.log N)^5 :=
  (sargosQuartic_fixed_power_le_maximal N 6 (fun _ => 1)
    0 (1/Real.sqrt N) _ _).trans (sargosQuartic_small_sixth_moment hN)

theorem sargosSixthBaseMoment_localize {N : ℕ} (hN : 1 ≤ N)
    {A : ℝ} (hA : 0 < A) (hA₁ : A ≤ 1/2) :
    sargosSixthBaseMoment N ≤ (1024/A)*sargosSixthInitialMoment N A := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let B : ℝ := 1/(N:ℝ)^3
  have hB : 0 < B := by dsimp [B]; positivity
  have hcount := sargosQuartic_even_moment_window_le_count hN 3 (fun _ => 1)
    (by intro n hn; simp) (by norm_num : (0:ℝ) < 1)
    (by positivity : 0 < 2*B) 0 (-B)
  have hcentral := sargosMomentNearCount_window_le_central hN 3
    (by positivity : 0 < 2*A) (by positivity : 0 < 2*B)
    (by linarith only [hA₁] : 2*A ≤ 1) (le_refl (2*B))
  have heB : -B+2*B = B := by ring
  have heA : 2*A/2 = A := by ring
  have heB₂ : 2*B/2 = B := by ring
  simp only [zero_add,heB,Nat.reduceMul] at hcount
  simp only [heA,heB₂,Nat.reduceMul] at hcentral
  have hsym := sargosQuartic_central_power_le_positive N 6 hA.le hB.le
  calc
    sargosSixthBaseMoment N ≤ (16*1*(2*B))*
        (sargosMomentNearCount N 3 (1/(1*(N:ℝ)^2)) (1/((2*B)*(N:ℝ)^4)):ℝ) := hcount
    _ ≤ (16*1*(2*B))*((64/((2*A)*(2*B)))*
        (2*sargosSixthInitialMoment N A)) := by
      have hc := hcentral.trans (mul_le_mul_of_nonneg_left hsym (by positivity))
      change _ ≤ (64/((2*A)*(2*B)))*(2*sargosSixthInitialMoment N A) at hc
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc
        (by positivity : 0 ≤ 16*1*(2*B))
    _ = _ := by field_simp; ring

end TaoTrudgianYang2025
