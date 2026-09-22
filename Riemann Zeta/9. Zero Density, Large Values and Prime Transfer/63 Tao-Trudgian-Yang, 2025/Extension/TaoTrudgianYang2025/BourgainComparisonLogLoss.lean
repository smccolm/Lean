import TaoTrudgianYang2025.BourgainLevelElimination

/-!
# Uniform bounds for the actual comparison's logarithmic factors

Constants precede the scale and physical local height. Alpha is fixed before
these constants, as required by the later fixed-exponent application.
-/

open Filter RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgainDifferenceLogLoss_uniform_power {τ η : ℝ} (hη : 0 < η) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      bourgainDifferenceLogLoss N τ ≤ D*N^η := by
  obtain ⟨Nlog, hlog⟩ := eventually_atTop.mp (heathBrown_eventually_log_le_rpow η hη)
  let D := 3+(|τ|+1)/Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc₀ : 0 ≤ (|τ|+1)/Real.log 2 := by positivity
  have hD : 1 ≤ D := by dsimp only [D]; linarith
  refine ⟨D, max 2 Nlog, hD, le_max_left _ _, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (by norm_num : (1 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hN)
  have hp : 1 ≤ N^η := Real.one_le_rpow hN1 hη.le
  have hl := hlog N ((le_max_right _ _).trans hN)
  have hc : 0 ≤ (|τ|+1)/Real.log 2 := by positivity
  unfold bourgainDifferenceLogLoss
  calc
    _ = 3+((|τ|+1)/Real.log 2)*Real.log N := by ring
    _ ≤ 3*N^η+((|τ|+1)/Real.log 2)*N^η :=
      add_le_add (by linarith) (mul_le_mul_of_nonneg_left hl hc)
    _ = D*N^η := by dsimp only [D]; ring

/-- Joint control of the exact difference-log and amplitude-grid factors.
The height and exponent slack remain universally quantified. -/
theorem bourgain_comparison_logs_uniform_power {B α τ ε η : ℝ}
    (hB : 0 < B) (hε : 0 ≤ ε) (hη : 0 < η) :
    ∃ D N₀ : ℝ, 1 ≤ D ∧ 2 ≤ N₀ ∧ ∀ N L δ : ℝ,
      N₀ ≤ N → 0 ≤ L → δ ≤ 1 → L ≤ N^(τ+δ) →
      bourgainDifferenceLogLoss N τ*
        (bourgainZetaBandCount B (L+N^(ε/8)+1)
          (N^(-bourgainSharedFloorExponent α τ ε)) : ℝ) ≤ D*N^η := by
  obtain ⟨D₁, N₁, hD₁, hN₁, hz⟩ :=
    bourgainDifferenceLogLoss_uniform_power (τ := τ) (half_pos hη)
  obtain ⟨D₂, N₂, hD₂, hN₂, hj⟩ :=
    bourgainZetaBandCount_uniform_power (B := B)
      (A := bourgainSharedFloorExponent α τ ε) (u := |τ|+ε+1)
      hB (bourgainSharedFloorExponent_pos α τ hε).le (by positivity) (half_pos hη)
  refine ⟨D₁*D₂, max N₁ N₂, by nlinarith, hN₁.trans (le_max_left _ _), ?_⟩
  intro N L δ hN hL hδ hT
  have hN1 : 1 ≤ N := (by norm_num : (1 : ℝ) ≤ 2).trans
    (hN₁.trans ((le_max_left _ _).trans hN))
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have ht : L ≤ N^(|τ|+ε+1) := hT.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_abs_self τ]))
  have hh : N^(ε/8) ≤ N^(|τ|+ε+1) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [abs_nonneg τ])
  have hone : 1 ≤ N^(|τ|+ε+1) := Real.one_le_rpow hN1 (by positivity)
  have hU : 0 ≤ L+N^(ε/8)+1 := by positivity
  have hcap : L+N^(ε/8)+1 ≤ 3*N^(|τ|+ε+1) := by linarith
  have hJ := hj N (L+N^(ε/8)+1) ((le_max_right _ _).trans hN) hU hcap
  calc
    _ ≤ (D₁*N^(η/2))*(D₂*N^(η/2)) := mul_le_mul
      (hz N ((le_max_left _ _).trans hN)) hJ (Nat.cast_nonneg _)
      (by positivity)
    _ = D₁*D₂*N^(η/2+η/2) := by rw [Real.rpow_add hNp]; ring
    _ = D₁*D₂*N^η := by congr 2; ring

end TaoTrudgianYang2025
