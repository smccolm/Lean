import GafniTao.HeathBrownAtkinsonEquation719High

/-!
# Ivić equation (7.19) for the terminal Atkinson block

The two frequency regimes are assembled here.  The first theorem retains the
exact terminal curvature scale.  The second removes that scale without losing
the endpoint shift `K + 1`; its right-hand side is the source-shaped
square-root term plus the reciprocal-gap term.
-/

namespace GafniTao

noncomputable section

/-- The ordered two-term Gram bound obtained by joining the Kusmin--Landau
and B-process alternatives. -/
theorem norm_heathBrownAtkinsonGram_le_equation719_terminal
    {K : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      900 * (K : ℝ) * Real.sqrt
          ((t - u) / heathBrownAtkinsonTerminalScale u K) +
        28 * Real.sqrt (u * (K + 1 : ℕ)) / (t - u) := by
  by_cases hsmall :
      heathBrownAtkinsonFirstDerivativeUpper u t (K + 1) (2 * K + 1) ≤
        Real.pi
  · have h := norm_heathBrownAtkinsonGram_le_physical_firstDerivative_of_small
      hu htu hK hblock htUpper hsmall
    have hmain : 0 ≤ 900 * (K : ℝ) * Real.sqrt
        ((t - u) / heathBrownAtkinsonTerminalScale u K) := by positivity
    linarith
  · have h := norm_heathBrownAtkinsonGram_le_raw_high
      hu htu hK hblock htUpper hsmall
    have hrecip : 0 ≤
        28 * Real.sqrt (u * (K + 1 : ℕ)) / (t - u) := by positivity
    linarith

/-- The positive fourth-root scale appearing when the literal terminal
curvature denominator is square-rooted. -/
def heathBrownAtkinsonQuarterScale (u : ℝ) (K : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (u / ((K + 1 : ℕ) : ℝ)))

theorem heathBrownAtkinsonQuarterScale_pos
    {u : ℝ} {K : ℕ} (hu : 0 < u) :
    0 < heathBrownAtkinsonQuarterScale u K := by
  unfold heathBrownAtkinsonQuarterScale
  positivity

/-- Exact square root of the terminal curvature scale. -/
theorem sqrt_heathBrownAtkinsonTerminalScale
    {u : ℝ} {K : ℕ} :
    Real.sqrt (heathBrownAtkinsonTerminalScale u K) =
      ((K + 1 : ℕ) : ℝ) * heathBrownAtkinsonQuarterScale u K := by
  have hA : 0 ≤ ((K + 1 : ℕ) : ℝ) := by positivity
  have hs : 0 ≤ Real.sqrt (u / ((K + 1 : ℕ) : ℝ)) :=
    Real.sqrt_nonneg _
  unfold heathBrownAtkinsonTerminalScale heathBrownAtkinsonQuarterScale
  rw [Real.sqrt_mul (sq_nonneg (((K + 1 : ℕ) : ℝ))),
    Real.sqrt_sq hA]

/-- The literal B-process scale is bounded by the source fourth-root scale.
The factor `K/(K+1)` is discarded only through the proved inequality
`K ≤ K+1`. -/
theorem K_mul_sqrt_div_terminal_le_quarterScale
    {u d : ℝ} {K : ℕ} (hu : 0 < u) (hd : 0 < d) :
    (K : ℝ) * Real.sqrt (d / heathBrownAtkinsonTerminalScale u K) ≤
      Real.sqrt d / heathBrownAtkinsonQuarterScale u K := by
  let A : ℝ := ((K + 1 : ℕ) : ℝ)
  let r : ℝ := heathBrownAtkinsonQuarterScale u K
  have hA : 0 < A := by dsimp only [A]; positivity
  have hr : 0 < r := by
    dsimp only [r]
    exact heathBrownAtkinsonQuarterScale_pos hu
  have hKA : (K : ℝ) ≤ A := by
    dsimp only [A]
    exact_mod_cast (show K ≤ K + 1 by omega)
  rw [Real.sqrt_div hd.le,
    sqrt_heathBrownAtkinsonTerminalScale]
  change (K : ℝ) * (Real.sqrt d / (A * r)) ≤ Real.sqrt d / r
  rw [le_div_iff₀ hr]
  have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hden : A ≠ 0 := hA.ne'
  calc
    (K : ℝ) * (Real.sqrt d / (A * r)) * r =
        ((K : ℝ) / A) * Real.sqrt d := by field_simp
    _ ≤ 1 * Real.sqrt d := by
      gcongr
      exact (div_le_one hA).2 hKA
    _ = Real.sqrt d := one_mul _

/-- Ordered source-shaped form of Ivić (7.19), retaining exact constants and
the harmless `K+1` terminal convention. -/
theorem norm_heathBrownAtkinsonGram_le_equation719
    {K : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      900 * Real.sqrt (t - u) / heathBrownAtkinsonQuarterScale u K +
        28 * Real.sqrt (u * (K + 1 : ℕ)) / (t - u) := by
  have hterminal := norm_heathBrownAtkinsonGram_le_equation719_terminal
    hu htu hK hblock htUpper
  have hscale := K_mul_sqrt_div_terminal_le_quarterScale (K := K)
    hu (sub_pos.mpr htu)
  calc
    ‖heathBrownAtkinsonGram K t u‖ ≤
        900 * (K : ℝ) * Real.sqrt
            ((t - u) / heathBrownAtkinsonTerminalScale u K) +
          28 * Real.sqrt (u * (K + 1 : ℕ)) / (t - u) := hterminal
    _ = 900 * ((K : ℝ) * Real.sqrt
          ((t - u) / heathBrownAtkinsonTerminalScale u K)) +
          28 * Real.sqrt (u * (K + 1 : ℕ)) / (t - u) := by ring
    _ ≤ 900 * (Real.sqrt (t - u) /
          heathBrownAtkinsonQuarterScale u K) +
          28 * Real.sqrt (u * (K + 1 : ℕ)) / (t - u) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 900))
        le_rfl
    _ = 900 * Real.sqrt (t - u) /
          heathBrownAtkinsonQuarterScale u K +
          28 * Real.sqrt (u * (K + 1 : ℕ)) / (t - u) := by ring


end

end GafniTao
