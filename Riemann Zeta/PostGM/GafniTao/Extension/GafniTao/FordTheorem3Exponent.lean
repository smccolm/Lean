import GafniTao.FordMomentInterpolation

/-!
# Ford Theorem 3: the interpolated exponent

This file assembles Lemma 3.6 at two adjacent multiples of `k`, the literal
Hölder interpolation, and the elementary exponential remainder which changes
`1.69 / k` into the source exponent `1.7 / k`.  Coefficients remain finite
existential constants; the exponent is exact.
-/

namespace GafniTao

noncomputable section

/-- Increasing the permissible exponent preserves a global moment bound. -/
theorem FordVinogradovMomentBound.mono_delta
    {s k : ℕ} {C delta delta' : ℝ}
    (h : FordVinogradovMomentBound s k C delta) (hdelta : delta ≤ delta') :
    FordVinogradovMomentBound s k C delta' := by
  intro Q hQ
  have hsource := h Q hQ
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hexponent : fordLambda34 s k delta ≤ fordLambda34 s k delta' := by
    unfold fordLambda34
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hQone hexponent
  exact hsource.trans (mul_le_mul_of_nonneg_left hpow
    ((h.one_le_coefficient).trans' zero_le_one))

/-- A second-order bound sufficient for Ford's interpolation remainder. -/
theorem ford_exp_neg_le_one_sub_add_sq {y : ℝ}
    (hy : 0 ≤ y) (hyOne : y ≤ 1) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 := by
  have habs : |(-y : ℝ)| ≤ 1 := by simpa [abs_of_nonneg hy] using hyOne
  have h := Real.abs_exp_sub_one_sub_id_le habs
  have hupper : Real.exp (-y) - 1 - (-y) ≤ y ^ 2 := by
    calc
      Real.exp (-y) - 1 - (-y) ≤ |Real.exp (-y) - 1 - (-y)| := le_abs_self _
      _ ≤ (-y) ^ 2 := h
      _ = y ^ 2 := by ring
  linarith

/-- Ford's bracket after interpolating adjacent exponents.  The slightly
coarser quadratic Taylor remainder is harmless for `k ≥ 1000` and still
lands exactly inside the printed `1.7 / k`. -/
theorem ford_theorem3_interpolation_bracket
    {k u : ℕ} (hk : 1000 ≤ k) (hu : u ≤ k) :
    (1 - (u : ℝ) / (k : ℝ)) +
        (u : ℝ) / (k : ℝ) * Real.exp (-2 / (k : ℝ)) ≤
      Real.exp (-2 * (u : ℝ) / (k : ℝ) ^ 2 +
        4 * (u : ℝ) / (k : ℝ) ^ 3) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  have huR : (u : ℝ) ≤ k := by exact_mod_cast hu
  have hu0 : (0 : ℝ) ≤ u := by positivity
  have hy0 : (0 : ℝ) ≤ 2 / (k : ℝ) := by positivity
  have hyOne : 2 / (k : ℝ) ≤ 1 := by
    rw [div_le_one hk0]
    linarith
  have hexp := ford_exp_neg_le_one_sub_add_sq hy0 hyOne
  have hscaled := mul_le_mul_of_nonneg_left hexp
    (div_nonneg hu0 hk0.le)
  have hscaled' :
      (u : ℝ) / (k : ℝ) * Real.exp (-2 / (k : ℝ)) ≤
        (u : ℝ) / (k : ℝ) *
          (1 - 2 / (k : ℝ) + (2 / (k : ℝ)) ^ 2) := by
    simpa only [neg_div] using hscaled
  have hlinear :
      (1 - (u : ℝ) / (k : ℝ)) +
          (u : ℝ) / (k : ℝ) * Real.exp (-2 / (k : ℝ)) ≤
        1 + (-2 * (u : ℝ) / (k : ℝ) ^ 2 +
          4 * (u : ℝ) / (k : ℝ) ^ 3) := by
    calc
      (1 - (u : ℝ) / (k : ℝ)) +
          (u : ℝ) / (k : ℝ) * Real.exp (-2 / (k : ℝ)) ≤
        (1 - (u : ℝ) / (k : ℝ)) +
          (u : ℝ) / (k : ℝ) *
            (1 - 2 / (k : ℝ) + (2 / (k : ℝ)) ^ 2) := by linarith
      _ = 1 + (-2 * (u : ℝ) / (k : ℝ) ^ 2 +
          4 * (u : ℝ) / (k : ℝ) ^ 3) := by field_simp; ring
  exact hlinear.trans (by
    simpa [add_comm] using Real.add_one_le_exp
      (-2 * (u : ℝ) / (k : ℝ) ^ 2 +
        4 * (u : ℝ) / (k : ℝ) ^ 3))

/-- The weighted Lemma 3.6 upper bounds are at most Ford's printed
`Delta_s = 3/8 k² exp(1/2 - 2s/k² + 1.7/k)`. -/
theorem ford_theorem3_weighted_delta_le
    {n k u : ℕ} (hk : 1000 ≤ k) (hu : u ≤ k) :
    (((k : ℝ) - u) / (k : ℝ)) *
        ((3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
          (1 / 2 - 2 * (n : ℝ) / (k : ℝ) + 169 / (100 * (k : ℝ)))) +
      ((u : ℝ) / (k : ℝ)) *
        ((3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
          (1 / 2 - 2 * ((n + 1 : ℕ) : ℝ) / (k : ℝ) +
            169 / (100 * (k : ℝ)))) ≤
      (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 2 * ((n * k + u : ℕ) : ℝ) / (k : ℝ) ^ 2 +
          17 / (10 * (k : ℝ))) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  have huR : (u : ℝ) ≤ k := by exact_mod_cast hu
  have hu0 : (0 : ℝ) ≤ u := by positivity
  let A : ℝ := (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
    (1 / 2 - 2 * (n : ℝ) / (k : ℝ) + 169 / (100 * (k : ℝ)))
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hnext :
      (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
          (1 / 2 - 2 * ((n + 1 : ℕ) : ℝ) / (k : ℝ) +
            169 / (100 * (k : ℝ))) =
        A * Real.exp (-2 / (k : ℝ)) := by
    dsimp [A]
    have heq :
        1 / 2 - 2 * ((n + 1 : ℕ) : ℝ) / (k : ℝ) +
            169 / (100 * (k : ℝ)) =
          (1 / 2 - 2 * (n : ℝ) / (k : ℝ) +
            169 / (100 * (k : ℝ))) + (-2 / (k : ℝ)) := by
      push_cast
      ring
    rw [heq, Real.exp_add]
    ring
  have hbracket := ford_theorem3_interpolation_bracket hk hu
  have hmain := mul_le_mul_of_nonneg_left hbracket hA0
  have hcorrection :
      169 / (100 * (k : ℝ)) + 4 * (u : ℝ) / (k : ℝ) ^ 3 ≤
        17 / (10 * (k : ℝ)) := by
    field_simp [ne_of_gt hk0]
    nlinarith
  have hexponent :
      (1 / 2 - 2 * (n : ℝ) / (k : ℝ) + 169 / (100 * (k : ℝ))) +
          (-2 * (u : ℝ) / (k : ℝ) ^ 2 +
            4 * (u : ℝ) / (k : ℝ) ^ 3) ≤
        1 / 2 - 2 * ((n * k + u : ℕ) : ℝ) / (k : ℝ) ^ 2 +
          17 / (10 * (k : ℝ)) := by
    push_cast
    field_simp at hcorrection ⊢
    nlinarith
  calc
    (((k : ℝ) - u) / (k : ℝ)) * A +
        ((u : ℝ) / (k : ℝ)) *
          ((3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
            (1 / 2 - 2 * ((n + 1 : ℕ) : ℝ) / (k : ℝ) +
              169 / (100 * (k : ℝ)))) =
        A * ((1 - (u : ℝ) / (k : ℝ)) +
          (u : ℝ) / (k : ℝ) * Real.exp (-2 / (k : ℝ))) := by
      rw [hnext]
      field_simp
    _ ≤ A * Real.exp (-2 * (u : ℝ) / (k : ℝ) ^ 2 +
          4 * (u : ℝ) / (k : ℝ) ^ 3) := hmain
    _ = (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
          ((1 / 2 - 2 * (n : ℝ) / (k : ℝ) + 169 / (100 * (k : ℝ))) +
            (-2 * (u : ℝ) / (k : ℝ) ^ 2 +
              4 * (u : ℝ) / (k : ℝ) ^ 3)) := by
      dsimp [A]
      calc
        (3 / 8 : ℝ) * (k : ℝ) ^ 2 *
            Real.exp (1 / 2 - 2 * (n : ℝ) / (k : ℝ) +
              169 / (100 * (k : ℝ))) *
            Real.exp (-2 * (u : ℝ) / (k : ℝ) ^ 2 +
              4 * (u : ℝ) / (k : ℝ) ^ 3) =
          (3 / 8 : ℝ) * (k : ℝ) ^ 2 *
            (Real.exp (1 / 2 - 2 * (n : ℝ) / (k : ℝ) +
              169 / (100 * (k : ℝ))) *
             Real.exp (-2 * (u : ℝ) / (k : ℝ) ^ 2 +
              4 * (u : ℝ) / (k : ℝ) ^ 3)) := by ring
        _ = _ := by rw [← Real.exp_add]
    _ ≤ (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 2 * ((n * k + u : ℕ) : ℝ) / (k : ℝ) ^ 2 +
          17 / (10 * (k : ℝ))) := by
      gcongr

#print axioms FordVinogradovMomentBound.mono_delta
#print axioms ford_exp_neg_le_one_sub_add_sq
#print axioms ford_theorem3_interpolation_bracket
#print axioms ford_theorem3_weighted_delta_le

end

end GafniTao
