import GafniTao.Pintz2023CorollaryTwo

/-!
# Pintz (2023), Corollary 3

The critical length is kept literally as
`T^(1 / (r * (1 - (r-1)xi - 6r epsilon)))`.  Positivity of its denominator
is explicit, rather than being hidden in the source phrase that `epsilon` is
sufficiently small.
-/

namespace GafniTao

noncomputable section

noncomputable def pintz2023CriticalScaleExponent
    (r : ℕ) (xi epsilon : ℝ) : ℝ :=
  1 / ((r : ℝ) *
    (1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon))

noncomputable def pintz2023CriticalScale
    (r : ℕ) (xi epsilon T : ℝ) : ℝ :=
  T ^ pintz2023CriticalScaleExponent r xi epsilon

/-- Raising the critical-scale inequality to the exact complementary power
produces the height factor needed in Corollary 3. -/
theorem pintz2023_height_power_le_of_critical_scale
    {r N : ℕ} {xi epsilon T : ℝ}
    (hr : 3 ≤ r) (hT : 1 ≤ T)
    (hden : 0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon)
    (hscale : pintz2023CriticalScale r xi epsilon T ≤ (N : ℝ)) :
    T ^ pintz2023HBAlpha r ≤
      (N : ℝ) ^
        ((1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon) /
          ((r : ℝ) - 1)) := by
  have hrReal : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrPos : (0 : ℝ) < r := by linarith
  have hrSubPos : 0 < (r : ℝ) - 1 := by linarith
  let d : ℝ := 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon
  let p : ℝ := 1 / ((r : ℝ) * d)
  let q : ℝ := d / ((r : ℝ) - 1)
  have hdPos : 0 < d := by simpa only [d] using hden
  have hpPos : 0 < p := by
    dsimp only [p]
    exact one_div_pos.mpr (mul_pos hrPos hdPos)
  have hqPos : 0 < q := by
    dsimp only [q]
    exact div_pos hdPos hrSubPos
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hcritical : T ^ p ≤ (N : ℝ) := by
    simpa only [pintz2023CriticalScale, pintz2023CriticalScaleExponent, p, d]
      using hscale
  have hraised := Real.rpow_le_rpow (Real.rpow_nonneg hTPos.le p)
    hcritical hqPos.le
  have hpq : p * q = pintz2023HBAlpha r := by
    dsimp only [p, q, d]
    unfold pintz2023HBAlpha
    field_simp [hden.ne']
    apply div_self
    nlinarith
  rw [← Real.rpow_mul hTPos.le, hpq] at hraised
  simpa only [q, d] using hraised

/-- The first monomial of Corollary 2 is at most `N^(-3 epsilon)` beyond
the source critical scale. -/
theorem pintz2023_first_term_le_of_critical_scale
    {r N : ℕ} {xi epsilon t T : ℝ}
    (hr : 3 ≤ r) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (ht : 0 < t) (htT : t ≤ T) (hT : 1 ≤ T)
    (hden : 0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon)
    (hscale : pintz2023CriticalScale r xi epsilon T ≤ (N : ℝ)) :
    (N : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
        t ^ pintz2023HBAlpha r ≤
      (N : ℝ) ^ (-3 * epsilon) := by
  have hrReal : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrSubPos : 0 < (r : ℝ) - 1 := by linarith
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have haPos := pintz2023HBAlpha_pos (show 2 ≤ r by omega)
  have htPower : t ^ pintz2023HBAlpha r ≤ T ^ pintz2023HBAlpha r :=
    Real.rpow_le_rpow ht.le htT haPos.le
  have hTPower :=
    pintz2023_height_power_le_of_critical_scale hr hT hden hscale
  let q : ℝ :=
    (1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon) /
      ((r : ℝ) - 1)
  have hheight : t ^ pintz2023HBAlpha r ≤ (N : ℝ) ^ q :=
    htPower.trans (by simpa only [q] using hTPower)
  have hExp :
      xi - 1 / ((r : ℝ) - 1) + 3 * epsilon + q ≤
        -3 * epsilon := by
    dsimp only [q]
    have hInvPos : 0 < 1 / ((r : ℝ) - 1) := one_div_pos.mpr hrSubPos
    field_simp
    nlinarith
  calc
    _ ≤ (N : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
        (N : ℝ) ^ q :=
      mul_le_mul_of_nonneg_left hheight (Real.rpow_nonneg (by positivity) _)
    _ = (N : ℝ) ^
        (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon + q) := by
      rw [← Real.rpow_add (show (0 : ℝ) < N by positivity)]
    _ ≤ (N : ℝ) ^ (-3 * epsilon) :=
      Real.rpow_le_rpow_of_exponent_le hNReal hExp

/-- Pintz (2023), Corollary 3, equation (3.3), with the constant in
`N \ll |t|^(2/r)` explicit. -/
theorem pintz2023_corollary_three_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (xi : ℝ) (N R : ℕ) (t T : ℝ),
      xi ≤ pintz2023HBAlpha r - 6 * epsilon →
      0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon →
      0 < N → N < R → R ≤ 2 * N →
      0 < t → t ≤ T → 1 ≤ T →
      pintz2023CriticalScale r xi epsilon T ≤ (N : ℝ) →
      (N : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
      ‖pintz2023WeightedBlock xi N R t‖ ≤ C * (N : ℝ) ^ (-3 * epsilon) := by
  obtain ⟨C₀, hC₀, hcorTwo⟩ :=
    pintz2023_corollary_two_native r epsilon B hr hepsilon hB
  refine ⟨2 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro xi N R t T hxi hden hN hNR hR ht htT hT hcritical hscale
  have hfirst := pintz2023_first_term_le_of_critical_scale
    hr hepsilon hN ht htT hT hden hcritical
  have htwo := hcorTwo xi N R t hxi hN hNR hR ht hscale
  unfold pintz2023CorollaryTwoMajorant at htwo
  calc
    ‖pintz2023WeightedBlock xi N R t‖ ≤
        C₀ * ((N : ℝ) ^
            (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
              t ^ pintz2023HBAlpha r +
          (N : ℝ) ^ (-3 * epsilon)) := htwo
    _ ≤ C₀ * (2 * (N : ℝ) ^ (-3 * epsilon)) := by
      apply mul_le_mul_of_nonneg_left _ hC₀.le
      linarith
    _ = (2 * C₀) * (N : ℝ) ^ (-3 * epsilon) := by ring

#print axioms pintz2023_height_power_le_of_critical_scale
#print axioms pintz2023_first_term_le_of_critical_scale
#print axioms pintz2023_corollary_three_native

end

end GafniTao
