import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds

open Asymptotics Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

theorem hughesYoungMollifierWeightedGCDMass_nonneg (T : ℝ) :
    0 ≤ hughesYoungMollifierWeightedGCDMass T := by
  unfold hughesYoungMollifierWeightedGCDMass
  positivity

theorem hughesYoungMollifierWeightedGCDMass_epsilonPowerBound :
    EpsilonPowerBound hughesYoungMollifierWeightedGCDMass (fun _ => 1) := by
  intro ε hε
  let δ : ℝ := ε / 10
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨A, D, hA, hD, hmass⟩ :=
    exists_hughesYoungMollifierWeightedGCDMass_le δ hδ
  let C : ℝ := A ^ 2 * D * (1 + δ⁻¹) ^ 2 * (2 : ℝ) ^ (2 * δ)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  apply IsBigO.of_bound C
  filter_upwards [eventually_detectorCutoff_sq_le_rpow,
      eventually_ge_atTop (1 : ℝ)] with T hcut hT
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  let L : ℕ := (detectorCutoff T) ^ 2
  have hL : (L : ℝ) ≤ T := by
    calc
      (L : ℝ) ≤ T ^ (1 / 22 : ℝ) := by
        simpa only [L, Nat.cast_pow] using hcut
      _ ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      _ = T := Real.rpow_one T
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hLone : (1 : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hLsucc : ((L + 1 : ℕ) : ℝ) ≤ 2 * T := by
    push_cast
    linarith
  have hpowL : (L : ℝ) ^ δ ≤ T ^ δ :=
    Real.rpow_le_rpow hL0 hL hδ.le
  have hpowSucc : ((L + 1 : ℕ) : ℝ) ^ δ ≤ (2 * T) ^ δ :=
    Real.rpow_le_rpow (by positivity) hLsucc hδ.le
  have hH := harmonic_le_epsilon_rpow hδ (L + 1)
  have hmax : max 1 (((L + 1 : ℕ) : ℝ) ^ δ) =
      ((L + 1 : ℕ) : ℝ) ^ δ := max_eq_right <|
        Real.one_le_rpow hLone hδ.le
  rw [hmax] at hH
  have hHbound : (((harmonic (L + 1) : ℚ) : ℝ)) ≤
      (1 + δ⁻¹) * (2 * T) ^ δ :=
    hH.trans (mul_le_mul_of_nonneg_left hpowSucc (by positivity))
  have hmass' := hmass (T := T)
  change hughesYoungMollifierWeightedGCDMass T ≤
      (A * (L : ℝ) ^ δ) ^ 2 * (D * (L : ℝ) ^ δ) *
        (((harmonic (L + 1) : ℚ) : ℝ)) ^ 2 at hmass'
  have hH0 : 0 ≤ (((harmonic (L + 1) : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hraw : hughesYoungMollifierWeightedGCDMass T ≤
      (A * T ^ δ) ^ 2 * (D * T ^ δ) *
        (((1 + δ⁻¹) * (2 * T) ^ δ)) ^ 2 := by
    calc
      _ ≤ (A * (L : ℝ) ^ δ) ^ 2 * (D * (L : ℝ) ^ δ) *
          (((harmonic (L + 1) : ℚ) : ℝ)) ^ 2 := hmass'
      _ ≤ (A * T ^ δ) ^ 2 * (D * T ^ δ) *
          (((harmonic (L + 1) : ℚ) : ℝ)) ^ 2 := by
        gcongr
      _ ≤ (A * T ^ δ) ^ 2 * (D * T ^ δ) *
          (((1 + δ⁻¹) * (2 * T) ^ δ)) ^ 2 := by
        gcongr
  have hpowTwo : (2 * T) ^ δ = (2 : ℝ) ^ δ * T ^ δ := by
    rw [Real.mul_rpow (by norm_num) hT0.le]
  have hcombine :
      (A * T ^ δ) ^ 2 * (D * T ^ δ) *
          (((1 + δ⁻¹) * (2 * T) ^ δ)) ^ 2 =
        C * T ^ (5 * δ) := by
    rw [hpowTwo]
    have hp : (T ^ δ) ^ 2 = T ^ (2 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
      ring_nf
    have hp2 : ((2 : ℝ) ^ δ) ^ 2 = (2 : ℝ) ^ (2 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
    rw [mul_pow, mul_pow, mul_pow, hp, hp2]
    dsimp only [C]
    rw [show T ^ (5 * δ) = T ^ (2 * δ) * T ^ δ * T ^ (2 * δ) by
      rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
      congr 1
      ring]
    ring
  have hexp : 5 * δ = ε / 2 := by dsimp only [δ]; ring
  have hpowFinal : T ^ (5 * δ) ≤ T ^ ε := by
    rw [hexp]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  simp only [Real.norm_eq_abs, abs_abs, abs_one, mul_one]
  rw [abs_of_nonneg (hughesYoungMollifierWeightedGCDMass_nonneg T),
    abs_of_nonneg (Real.rpow_nonneg hT0.le ε)]
  exact hraw.trans_eq hcombine |>.trans (mul_le_mul_of_nonneg_left hpowFinal hC)

end RiemannZeta.GuthMaynard
