import GafniTao.HeathBrownAtkinsonLemma71Assembly

/-!
# Exact fractional scales in Ivić equation (7.25)

The source writes quarter- and eighth-powers.  These definitions use nested
nonnegative square roots, so all identities are literal over `ℝ` and no
branch convention is implicit.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The positive eighth-root scale obtained by square-rooting the Atkinson
quarter scale. -/
def heathBrownAtkinsonEighthScale (u : ℝ) (K : ℕ) : ℝ :=
  Real.sqrt (heathBrownAtkinsonQuarterScale u K)

theorem heathBrownAtkinsonEighthScale_nonneg (u : ℝ) (K : ℕ) :
    0 ≤ heathBrownAtkinsonEighthScale u K := by
  unfold heathBrownAtkinsonEighthScale
  positivity

theorem heathBrownAtkinsonEighthScale_pos
    {u : ℝ} {K : ℕ} (hu : 0 < u) :
    0 < heathBrownAtkinsonEighthScale u K := by
  unfold heathBrownAtkinsonEighthScale
  exact Real.sqrt_pos.2 (heathBrownAtkinsonQuarterScale_pos hu)

/-- The eighth power is exactly the physical ratio `u/(K+1)`. -/
theorem heathBrownAtkinsonEighthScale_pow_eight
    {u : ℝ} {K : ℕ} (hu : 0 ≤ u) :
    heathBrownAtkinsonEighthScale u K ^ (8 : ℕ) =
      u / ((K + 1 : ℕ) : ℝ) := by
  have hq : 0 ≤ heathBrownAtkinsonQuarterScale u K := by
    unfold heathBrownAtkinsonQuarterScale
    positivity
  unfold heathBrownAtkinsonEighthScale
  calc
    Real.sqrt (heathBrownAtkinsonQuarterScale u K) ^ (8 : ℕ) =
        (Real.sqrt (heathBrownAtkinsonQuarterScale u K) ^ (2 : ℕ)) ^
          (4 : ℕ) := by ring
    _ = heathBrownAtkinsonQuarterScale u K ^ (4 : ℕ) := by
      rw [Real.sq_sqrt hq]
    _ = u / ((K + 1 : ℕ) : ℝ) :=
      heathBrownAtkinsonQuarterScale_pow_four hu

/-- The fourth power of the literal `J` quarter-root is exactly `J`. -/
theorem sqrt_sqrt_pow_four {J : ℝ} (hJ : 0 ≤ J) :
    Real.sqrt (Real.sqrt J) ^ (4 : ℕ) = J := by
  have hs : 0 ≤ Real.sqrt J := Real.sqrt_nonneg J
  calc
    Real.sqrt (Real.sqrt J) ^ (4 : ℕ) =
        (Real.sqrt (Real.sqrt J) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
    _ = Real.sqrt J ^ (2 : ℕ) := by rw [Real.sq_sqrt hs]
    _ = J := Real.sq_sqrt hJ

theorem sqrt_heathBrownAtkinsonSourceFirstCoefficient_eighthScale
    {T J : ℝ} {K : ℕ} (hT : 0 < T) :
    Real.sqrt (heathBrownAtkinsonSourceFirstCoefficient T J K) =
      30 * Real.sqrt (Real.sqrt J) /
        heathBrownAtkinsonEighthScale (T / 2) K := by
  simpa only [heathBrownAtkinsonEighthScale] using
    sqrt_heathBrownAtkinsonSourceFirstCoefficient
      (T := T) (J := J) (K := K) hT


end

end GafniTao
