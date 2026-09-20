import TaoTrudgianYang2025.ZetaMellinDerivative

/-!
# Uniform Mellin bounds in the actual polynomial scale

The constants depend only on the fixed transition, derivative order, and
real line, never on the interval endpoints, physical scale, or ordinate.
-/

noncomputable section

open Complex MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def zetaCutoffMellinConstant (j : ℕ) (σ : ℝ) : ℝ :=
  1 + 3 ^ j * 3 ^ (σ + j - 1) * zetaCutoffDerivativeMass j

theorem zetaCutoffMellinConstant_pos (j : ℕ) (σ : ℝ) : 0 < zetaCutoffMellinConstant j σ := by
  unfold zetaCutoffMellinConstant
  have := zetaCutoffDerivativeMass_nonneg j
  positivity

theorem ZetaLargeValuePattern.cutoff_mellin_weighted_bound (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {σ : ℝ} (hσ : 1 / 2 ≤ σ) {j : ℕ} (hj : 1 ≤ j) (u : ℝ) :
    (1 + |u|) ^ j *
        ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      zetaCutoffMellinConstant j σ * P.N ^ (σ + j - 1) := by
  let g : ℝ → ℂ := fun x => (zetaIntervalCutoff a b x : ℂ)
  let hg := zetaIntervalCutoffTest a b (P.active_left_pos hactive)
  let hd := mellinIteratedDerivativeTest hg j
  obtain ⟨hab, ha, hb⟩ := P.active_interval_bounds hactive hne
  have hjreal : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hexp : 0 ≤ σ + j - 1 := by linarith
  have hupper : hd.upper ≤ 3 * P.N := by
    change max (a : ℝ) b + 1 / 2 ≤ 3 * P.N
    rw [max_eq_right (by exact_mod_cast hab)]
    linarith [P.one_lt_N]
  have hmass := integral_norm_complex_cutoff_deriv_le hab (Nat.lt_of_lt_of_le Nat.zero_lt_one hj)
  have hweighted := mellin_weighted_norm_le_derivative hg hσ u j
  have hnorm := norm_mellin_le_upper_mass hd
    (s := ((σ : ℂ) + (u : ℂ) * I) + (j : ℂ)) (by simpa using (show 1 ≤ σ + j by linarith))
  have hreal : (((σ : ℂ) + (u : ℂ) * I) + (j : ℂ)).re - 1 = σ + j - 1 := by simp
  rw [hreal] at hnorm
  have hpow : hd.upper ^ (σ + j - 1) ≤ (3 * P.N) ^ (σ + j - 1) :=
    Real.rpow_le_rpow (hd.lower_pos.le.trans hd.lower_le_upper) hupper hexp
  have hN : 0 ≤ P.N := P.one_lt_N.le.trans' (by norm_num)
  change (1 + |u|) ^ j * ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ _
  calc
    _ ≤ 3 ^ j * ‖mellin (iteratedDeriv j g) (((σ : ℂ) + (u : ℂ) * I) + j)‖ := hweighted
    _ ≤ 3 ^ j * ((3 * P.N) ^ (σ + j - 1) * zetaCutoffDerivativeMass j) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hnorm.trans (mul_le_mul hpow hmass
        (integral_nonneg fun x => norm_nonneg _) (Real.rpow_nonneg (by positivity) _))
    _ ≤ zetaCutoffMellinConstant j σ * P.N ^ (σ + j - 1) := by
      rw [Real.mul_rpow (by norm_num) hN]
      unfold zetaCutoffMellinConstant
      nlinarith [Real.rpow_nonneg hN (σ + j - 1)]

theorem ZetaLargeValuePattern.cutoff_mellin_bound (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {σ : ℝ} (hσ : 1 / 2 ≤ σ) {j : ℕ} (hj : 1 ≤ j) (u : ℝ) :
    ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      zetaCutoffMellinConstant j σ * P.N ^ (σ + j - 1) / (1 + |u|) ^ j := by
  apply (le_div_iff₀ (by positivity : 0 < (1 + |u|) ^ j)).2
  simpa only [mul_comm] using P.cutoff_mellin_weighted_bound hactive hne hσ hj u

theorem ZetaLargeValuePattern.cutoff_critical_mellin_kernel (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty) (u : ℝ) :
    ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
      zetaCutoffMellinConstant 1 (1 / 2) * Real.sqrt P.N / (1 + |u|) := by
  have h := P.cutoff_mellin_bound hactive hne (σ := 1 / 2) le_rfl (j := 1) le_rfl u
  norm_num only [Nat.cast_one, pow_one, show (1 / 2 : ℝ) + 1 - 1 = 1 / 2 by norm_num] at h
  simpa only [Real.sqrt_eq_rpow] using h

theorem ZetaLargeValuePattern.cutoff_mellin_residue_bound (P : ZetaLargeValuePattern)
    {a b : ℕ} (hactive : P.active = Finset.Icc a b) (hne : P.active.Nonempty)
    {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    ‖mellin (fun x => (zetaIntervalCutoff a b x : ℂ)) (1 - (t : ℂ) * I)‖ ≤
      zetaCutoffMellinConstant j 1 * P.N ^ j / (1 + |t|) ^ j := by
  have h := P.cutoff_mellin_bound hactive hne (σ := 1) (by norm_num) hj (-t)
  simpa only [ofReal_one, ofReal_neg, neg_mul, ← sub_eq_add_neg, abs_neg,
    add_sub_cancel_left, Real.rpow_natCast] using h

end TaoTrudgianYang2025
