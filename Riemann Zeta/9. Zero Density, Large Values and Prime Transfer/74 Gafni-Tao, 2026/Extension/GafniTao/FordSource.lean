import GafniTao.VinogradovKorobov

/-!
# Ford source statements and normalization bridges

Ford's 2002 theorem has an explicit zeta-growth constant.  The
Halász--Turán/Montgomery consumer is customarily written with an implied
multiplicative constant.  Gafni--Tao only needs some logarithmic power, so
this file proves the exact operation which absorbs that coefficient into one
additional logarithm without introducing a `T^epsilon` loss.
-/

namespace GafniTao

/-- Literal real-valued form of Ford's 2002 Theorem 1 for the Riemann zeta
function.  Decimal constants in Lean are exact rationals. -/
def FordZetaGrowthBound : Prop :=
  ∀ ⦃sigma t : ℝ⦄, 1 / 2 ≤ sigma → sigma ≤ 1 → 3 ≤ |t| →
    ‖riemannZeta (sigma + Complex.I * t)‖ ≤
      76.2 * |t| ^ (4.45 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log |t| ^ (2 / 3 : ℝ)

/-- The explicit coefficient-bearing near-one density estimate obtained by
the Halász--Turán/Montgomery detector from Ford's zeta-growth theorem. -/
def FordNearOneDensityEstimate (K T₀ : ℝ) : Prop :=
  ∀ ⦃eta T : ℝ⦄, 0 < eta → eta ≤ 1 / 2 → T₀ ≤ T →
    (zeroCount (1 - eta) T : ℝ) ≤
      K * T ^ (58.05 * eta ^ (3 / 2 : ℝ)) *
        Real.log T ^ (15 : ℝ)

/-- The exact asymptotic zero-free conclusion used from Ford: some positive
Vinogradov--Korobov width holds pointwise above a fixed height. -/
def FordAsymptoticZeroFree : Prop :=
  ∃ c H : ℝ, 0 < c ∧ Real.exp (Real.exp 1) ≤ H ∧
    VinogradovKorobovPointwiseZeroFree c H

/-- Absorb Ford's fixed implied coefficient into one extra logarithm.  No
power of `T` is spent in this conversion. -/
theorem nearOneLogDensityBound_of_fordNearOneDensityEstimate
    {K T₀ : ℝ} (hFord : FordNearOneDensityEstimate K T₀) :
    NearOneLogDensityBound 58.05 16
      (max T₀ (Real.exp (max K 1))) := by
  intro eta T hetaPos hetaHalf hT
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hExp : Real.exp (max K 1) ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := (Real.exp_pos _).trans_le hExp
  have hLogLower : max K 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hTPos hExp
  have hKLog : K ≤ Real.log T := (le_max_left _ _).trans hLogLower
  have hOneLog : 1 ≤ Real.log T := (le_max_right _ _).trans hLogLower
  have hLogNonneg : 0 ≤ Real.log T := zero_le_one.trans hOneLog
  have hFordBound := hFord hetaPos hetaHalf hT₀
  calc
    (zeroCount (1 - eta) T : ℝ) ≤
        K * T ^ (58.05 * eta ^ (3 / 2 : ℝ)) *
          Real.log T ^ (15 : ℝ) := hFordBound
    _ ≤ T ^ (58.05 * eta ^ (3 / 2 : ℝ)) *
          (Real.log T * Real.log T ^ (15 : ℝ)) := by
      have hPower : 0 ≤ T ^ (58.05 * eta ^ (3 / 2 : ℝ)) :=
        Real.rpow_nonneg hTPos.le _
      have hLogPower : 0 ≤ Real.log T ^ (15 : ℝ) :=
        Real.rpow_nonneg hLogNonneg _
      calc
        K * T ^ (58.05 * eta ^ (3 / 2 : ℝ)) *
            Real.log T ^ (15 : ℝ) ≤
            Real.log T * T ^ (58.05 * eta ^ (3 / 2 : ℝ)) *
              Real.log T ^ (15 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hKLog hPower) hLogPower
        _ = _ := by ring
    _ = T ^ (58.05 * eta ^ (3 / 2 : ℝ)) *
          Real.log T ^ (16 : ℝ) := by
      rw [show (16 : ℝ) = 1 + 15 by norm_num,
        Real.rpow_add (zero_lt_one.trans_le hOneLog), Real.rpow_one]

/-- The two genuine Ford outputs, once proved, supply the exact pair of
right-edge inputs consumed by Gafni--Tao. -/
theorem exists_nearOne_inputs_of_ford_outputs
    (hZeroFree : FordAsymptoticZeroFree)
    {K T₀ : ℝ} (hDensity : FordNearOneDensityEstimate K T₀) :
    ∃ c T₁ T₂ : ℝ,
      0 < c ∧
      VinogradovKorobovCountVanishing c T₁ ∧
      NearOneLogDensityBound 58.05 16 T₂ := by
  obtain ⟨c, H, hc, hH, hPointwise⟩ := hZeroFree
  obtain ⟨c', hc', _hc'Le, hRectangle⟩ :=
    exists_vinogradovKorobovRectangleZeroFree_of_pointwise hc hH hPointwise
  refine ⟨c', H, max T₀ (Real.exp (max K 1)), hc', ?_, ?_⟩
  · exact vinogradovKorobovCountVanishing_of_rectangleZeroFree hRectangle
  · exact nearOneLogDensityBound_of_fordNearOneDensityEstimate hDensity

end GafniTao
