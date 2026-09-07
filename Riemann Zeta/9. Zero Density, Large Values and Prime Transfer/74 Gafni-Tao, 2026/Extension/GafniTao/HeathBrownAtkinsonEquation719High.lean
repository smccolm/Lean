import GafniTao.HeathBrownAtkinsonEquation719Raw

/-!
# High-frequency half of Ivić (7.19)

Failure of the first-derivative half-period condition forces the height gap
past the geometric-mean threshold.  At that point the secondary square-root
term in the B-process is absorbed by its principal term.
-/

namespace GafniTao

noncomputable section

/-- The lower radical at any endpoint `B <= 2A` dominates the normalized
square-root scale at `A`. -/
theorem sqrt_div_le_heathBrownAtkinsonSlopeLower
    {u A B : ℝ} (hu : 0 < u) (hA : 0 < A)
    (hB : 0 < B) (hBtwo : B ≤ 2 * A) :
    Real.sqrt (u / A) ≤ heathBrownAtkinsonSlopeLower u B := by
  exact (sqrt_le_heathBrownAtkinsonSlopeLower_two_mul hu hA).trans
    (heathBrownAtkinsonSlopeLower_anti hu hB hBtwo)

/-- The complement of the small-frequency branch forces the terminal
curvature scale below twice `K` times the height gap. -/
theorem heathBrownAtkinsonTerminalScale_le_two_K_gap_of_not_small
    {K : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hnotSmall : ¬
      heathBrownAtkinsonFirstDerivativeUpper u t (K + 1) (2 * K + 1) ≤
        Real.pi) :
    heathBrownAtkinsonTerminalScale u K ≤
      2 * (K : ℝ) * (t - u) := by
  let A : ℝ := (K : ℝ) + 1
  let B : ℝ := 2 * (K : ℝ) + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBtwo : B ≤ 2 * A := by
    dsimp only [A, B]
    linarith
  have hslow := sqrt_div_le_heathBrownAtkinsonSlopeLower hu hA hB hBtwo
  have hslowPos := heathBrownAtkinsonSlopeLower_pos hu hB
  have hden : 0 < A * heathBrownAtkinsonSlopeLower u B :=
    mul_pos hA hslowPos
  have hlarge : Real.pi <
      Real.pi * (t - u) /
        (A * heathBrownAtkinsonSlopeLower u B) := by
    have hnot : ¬ Real.pi * (t - u) /
        (A * heathBrownAtkinsonSlopeLower u B) ≤ Real.pi := by
      simpa only [heathBrownAtkinsonFirstDerivativeUpper, Nat.cast_add,
        Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, A, B] using hnotSmall
    exact lt_of_not_ge hnot
  have hcross := (lt_div_iff₀ hden).mp hlarge
  have hthreshold : A * Real.sqrt (u / A) < t - u := by
    have hmul := mul_le_mul_of_nonneg_left hslow hA.le
    nlinarith [Real.pi_pos]
  have hAupper : A ≤ 2 * (K : ℝ) := by
    dsimp only [A]
    exact_mod_cast (show K + 1 ≤ 2 * K by omega)
  have hgap : 0 < t - u := sub_pos.mpr htu
  have hscaleEq : heathBrownAtkinsonTerminalScale u K =
      A * (A * Real.sqrt (u / A)) := by
    unfold heathBrownAtkinsonTerminalScale
    simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, A]
    ring
  rw [hscaleEq]
  calc
    A * (A * Real.sqrt (u / A)) ≤ A * (t - u) :=
      mul_le_mul_of_nonneg_left hthreshold.le hA.le
    _ ≤ 2 * (K : ℝ) * (t - u) :=
      mul_le_mul_of_nonneg_right hAupper hgap.le

/-- Reciprocal square-root absorption from the high-frequency scale
inequality. -/
theorem inv_sqrt_ratio_le_two_K_sqrt_ratio
    {K : ℕ} {d Q : ℝ} (hd : 0 < d) (hQ : 0 < Q)
    (hscale : Q ≤ 2 * (K : ℝ) * d) :
    1 / Real.sqrt (d / Q) ≤
      2 * (K : ℝ) * Real.sqrt (d / Q) := by
  have hx : 0 < d / Q := div_pos hd hQ
  have hs : 0 < Real.sqrt (d / Q) := Real.sqrt_pos.2 hx
  have hone : 1 ≤ 2 * (K : ℝ) * (d / Q) := by
    calc
      1 = Q / Q := (div_self hQ.ne').symm
      _ ≤ (2 * (K : ℝ) * d) / Q :=
        div_le_div_of_nonneg_right hscale hQ.le
      _ = 2 * (K : ℝ) * (d / Q) := by ring
  rw [div_le_iff₀ hs]
  rw [show (2 * (K : ℝ) * Real.sqrt (d / Q)) *
      Real.sqrt (d / Q) =
      2 * (K : ℝ) * (Real.sqrt (d / Q) ^ (2 : ℕ)) by ring,
    Real.sq_sqrt hx.le]
  exact hone

/-- High-frequency Atkinson Gram estimate after absorbing the secondary
B-process term. -/
theorem norm_heathBrownAtkinsonGram_le_raw_high
    {K : ℕ} {t u : ℝ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u)
    (hnotSmall : ¬
      heathBrownAtkinsonFirstDerivativeUpper u t (K + 1) (2 * K + 1) ≤
        Real.pi) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      900 * (K : ℝ) * Real.sqrt
        ((t - u) / heathBrownAtkinsonTerminalScale u K) := by
  let x := (t - u) / heathBrownAtkinsonTerminalScale u K
  have hQ := heathBrownAtkinsonTerminalScale_pos (K := K) hu
  have hgap : 0 < t - u := sub_pos.mpr htu
  have hx : 0 < x := by dsimp only [x]; positivity
  have hinv : 1 / Real.sqrt x ≤ 2 * (K : ℝ) * Real.sqrt x := by
    simpa only [x] using inv_sqrt_ratio_le_two_K_sqrt_ratio hgap hQ
      (heathBrownAtkinsonTerminalScale_le_two_K_gap_of_not_small
        hu htu hK hnotSmall)
  have hmain : 0 ≤ (K : ℝ) * Real.sqrt x := by positivity
  have hraw := norm_heathBrownAtkinsonGram_le_raw_B
    hu htu hK hblock htUpper
  change ‖heathBrownAtkinsonGram K t u‖ ≤
      900 * (K : ℝ) * Real.sqrt x
  calc
    ‖heathBrownAtkinsonGram K t u‖ ≤
        300 * ((K : ℝ) * Real.sqrt x + 1 / Real.sqrt x) := by
      simpa only [x] using hraw
    _ ≤ 300 * ((K : ℝ) * Real.sqrt x +
        2 * (K : ℝ) * Real.sqrt x) := by gcongr
    _ = 900 * (K : ℝ) * Real.sqrt x := by ring


end

end GafniTao
