import DhimanKadiriQuesadaHerrera2026.GeneralBSmall

namespace DhimanKadiriQuesadaHerrera2026

/-- The positive cubic tail starting at two is uniformly at most one quarter. -/
theorem cubic_series_two_le {α : ℝ} (hα : 0 ≤ α) :
    (∑' n : ℕ, 1 / ((n : ℝ) + (2 + α)) ^ 3) ≤ 1 / 4 := by
  have hs := (reciprocal_cube_series_bounds (by positivity : 0 < 2 + α)).1
  have hs2 := reciprocal_cube_series_bounds (by norm_num : (0 : ℝ) < 2)
  have hm := hs.tsum_le_tsum (fun n : ℕ => one_div_le_one_div_of_le
    (pow_pos (by positivity : 0 < (n : ℝ) + 2) 3)
    (pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) + 2) (by linarith : (n : ℝ) + 2 ≤ (n : ℝ) + (2 + α)) 3)) hs2.1
  apply hm.trans
  convert hs2.2.2 using 1
  norm_num

/-- Exact cancellation in the literal source constant-weight square/cube coefficient. -/
theorem printed_constant_coefficient_expansion {β : ℝ} (hβ : 0 < β) :
    let d := (⌊β⌋₊ : ℝ) + 1 - β
    printedPartIIE1 β / β + partIICubeCoefficient β =
      1 / d ^ 3 + 1 / (d + 1) ^ 3 + 1 / (2 * (d + 1) ^ 2) +
        1 / (β * (d + 1) ^ 2) + 1 / (2 * ((⌊β⌋₊ : ℝ) + 1) * β ^ 2) -
          1 / (2 * (1 + β) ^ 2) := by
  let d := (⌊β⌋₊ : ℝ) + 1 - β
  have hd : 0 < d := by dsimp [d]; linarith [Nat.lt_floor_add_one β]
  have he : printedPartIIE1 β / β + partIICubeCoefficient β =
      1 / d ^ 3 + 1 / (d + 1) ^ 3 + 1 / (2 * (d + 1) ^ 2) +
        1 / (β * (d + 1) ^ 2) + 1 / (2 * ((⌊β⌋₊ : ℝ) + 1) * β ^ 2) -
          1 / (2 * (1 + β) ^ 2) := by
    unfold printedPartIIE1 partIICubeCoefficient
    rw [show 1 - (β - (⌊β⌋₊ : ℝ)) = d by dsimp [d]; ring]
    dsimp only
    have h1 : 1 + β ≠ 0 := by positivity
    have h2 : d + 1 ≠ 0 := by positivity
    have h3 : (⌊β⌋₊ : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  exact he

/-- After both far cubic tails the printed coefficient retains a uniform fraction of its singular gap allowance. -/
theorem printed_coefficient_after_cubic {α β : ℝ} (hα : 0 ≤ α) (hβ : 2 ≤ β) :
    let d := (⌊β⌋₊ : ℝ) + 1 - β
    (∑' n : ℕ, 1 / ((n : ℝ) + (d + 1)) ^ 3) +
      (∑' n : ℕ, 1 / ((n : ℝ) + (2 + α)) ^ 3) + 25 / (36 * d ^ 3) ≤
        printedPartIIE1 β / β + partIICubeCoefficient β := by
  dsimp only
  let d := (⌊β⌋₊ : ℝ) + 1 - β
  have hβp : 0 < β := by linarith
  have hd : 0 < d := by dsimp [d]; linarith [Nat.lt_floor_add_one β]
  have hd1 : d ≤ 1 := by dsimp [d]; linarith [Nat.floor_le hβp.le]
  have hi : 1 ≤ 1 / d ^ 3 := by
    apply (le_div_iff₀ (pow_pos hd 3)).mpr
    simpa using pow_le_one₀ (n := 3) hd.le hd1
  have hn := (reciprocal_cube_series_bounds (by positivity : 0 < d + 1)).2.2
  have hp := cubic_series_two_le hα
  have hsmall : 1 / (2 * (1 + β) ^ 2) ≤ 1 / 18 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (1 + β) ^ 2) (by norm_num : (0 : ℝ) < 18)).mpr
    nlinarith
  have hplus : 0 ≤ 1 / (β * (d + 1) ^ 2) + 1 / (2 * ((⌊β⌋₊ : ℝ) + 1) * β ^ 2) := by positivity
  have he := printed_constant_coefficient_expansion hβp
  change printedPartIIE1 β / β + partIICubeCoefficient β =
    1 / d ^ 3 + 1 / (d + 1) ^ 3 + 1 / (2 * (d + 1) ^ 2) +
      1 / (β * (d + 1) ^ 2) + 1 / (2 * ((⌊β⌋₊ : ℝ) + 1) * β ^ 2) - 1 / (2 * (1 + β) ^ 2) at he
  change _ + _ + 25 / (36 * d ^ 3) ≤ _
  rw [he]
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hn hp hi hsmall hplus ⊢
  nlinarith only [hn, hp, hi, hsmall, hplus]

/-- The unused stationary curvature coefficient absorbs half the reciprocal gap after the far tails. -/
theorem cubic_half_gap_budget {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    1 / (2 * Real.pi * d) ≤ 0.1585 / x + 25 * x ^ 2 / (72 * Real.pi ^ 2 * d ^ 3) := by
  have hπ : 3 ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hπ2 : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hleft : 1 / (2 * Real.pi * d) ≤ 1 / (6 * d) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hcurve : x ^ 2 / (32 * d ^ 3) ≤ 25 * x ^ 2 / (72 * Real.pi ^ 2 * d ^ 3) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 32 * d ^ 3) (by positivity : 0 < 72 * Real.pi ^ 2 * d ^ 3)).mpr
    nlinarith [mul_nonneg (sq_nonneg x) (pow_nonneg hd.le 3),
      mul_le_mul_of_nonneg_right hπ2 (mul_nonneg (sq_nonneg x) (pow_nonneg hd.le 3))]
  have hpoly := mul_nonneg (sq_nonneg (x - 4 * d / 3)) (by positivity : 0 ≤ x + 8 * d / 3)
  have hstep : 1 / (6 * d) ≤ 0.1585 / x + x ^ 2 / (32 * d ^ 3) := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 96 * x * d ^ 3)).mp
    field_simp
    nlinarith [pow_pos hd 3]
  exact hleft.trans (hstep.trans (add_le_add le_rfl hcurve))


/-- The actual source curvature bounds pay for both far tails and half the near gap. -/
theorem cubic_curvature_gap_budget {α β κ ℓ : ℝ} (hα : 0 ≤ α) (hβ : 2 ≤ β)
    (hℓ : 0 < ℓ) (hκ : ℓ ≤ κ) :
    let d := (⌊β⌋₊ : ℝ) + 1 - β
    κ / (2 * Real.pi ^ 2) * ((∑' n : ℕ, 1 / ((n : ℝ) + (d + 1)) ^ 3) +
      (∑' n : ℕ, 1 / ((n : ℝ) + (2 + α)) ^ 3)) + 1 / (2 * Real.pi * d) ≤
      0.1585 / Real.sqrt ℓ + κ / (2 * Real.pi ^ 2) *
        (printedPartIIE1 β / β + partIICubeCoefficient β) := by
  dsimp only
  let d := (⌊β⌋₊ : ℝ) + 1 - β
  have hd : 0 < d := by dsimp [d]; linarith [Nat.lt_floor_add_one β]
  have hκn : 0 ≤ κ := hℓ.le.trans hκ
  have hb := cubic_half_gap_budget (Real.sqrt_pos.mpr hℓ) hd
  rw [Real.sq_sqrt hℓ.le] at hb
  have hc := mul_le_mul_of_nonneg_left (printed_coefficient_after_cubic hα hβ)
    (by positivity : 0 ≤ κ / (2 * Real.pi ^ 2))
  have hm := mul_le_mul_of_nonneg_left hκ (by positivity : 0 ≤ 25 / (72 * Real.pi ^ 2 * d ^ 3))
  change κ / (2 * Real.pi ^ 2) * (_ + _ + 25 / (36 * d ^ 3)) ≤ _ at hc
  change κ / (2 * Real.pi ^ 2) * (_ + _) + 1 / (2 * Real.pi * d) ≤ _
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hb hc hm ⊢
  nlinarith only [hb, hc, hm]

/-- The two far cubic tails have a uniform seven-quarter bound for all positive gaps. -/
theorem cubic_series_uniform {α d : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d) :
    (∑' n : ℕ, 1 / ((n : ℝ) + (d + 1)) ^ 3) +
      (∑' n : ℕ, 1 / ((n : ℝ) + (2 + α)) ^ 3) ≤ 7 / 4 := by
  have hs := reciprocal_cube_series_bounds (by positivity : 0 < d + 1)
  have hb3 : 1 / (d + 1) ^ 3 ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact one_le_pow₀ (by linarith : 1 ≤ d + 1)
  have hb2 : 1 / (2 * (d + 1) ^ 2) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (d + 1) ^ 2) (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith
  have hp := cubic_series_two_le hα
  linarith [hs.2.2]

/-- For third-derivative bound at most one, six hundredths of the stationary nonlinear coefficient covers the full length error. -/
theorem cubic_small_D_budget {D L h₂ S : ℝ} (hD : 0 ≤ D) (hD1 : D ≤ 1)
    (hL : 0 ≤ L) (hh₂ : 1 ≤ h₂) (hS : S ≤ 7 / 4) :
    D * L / (4 * Real.pi ^ 2) * S ≤
      (0.06 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * L := by
  have hroot : D ≤ D ^ (1 / 3 : ℝ) := Real.self_le_rpow_of_le_one hD hD1 (by norm_num)
  have hratio : (9 / 10 : ℝ) ≤ (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ) := by
    have hp : 3 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_d2])
    have hr := Real.self_le_rpow_of_le_one (by positivity : 0 ≤ 3 / Real.pi) hp (by norm_num : (2 / 3 : ℝ) ≤ 1)
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3) Real.pi_pos.le] at hr
    have ht : (9 / 10 : ℝ) ≤ 3 / Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_d2])
    exact ht.trans hr
  have hpi : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
  have hc : 1 / (4 * Real.pi ^ 2) ≤ 1 / 36 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 36)
    linarith
  have hleft := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ D * L / (4 * Real.pi ^ 2))
  have hleft' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ D * L * (7 / 4 : ℝ))
  have hright := mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ 0.06 * h₂ * D ^ (1 / 3 : ℝ) * L)
  have hrootL := mul_le_mul_of_nonneg_right hroot hL
  have hhL := mul_le_mul_of_nonneg_right hh₂ (by positivity : 0 ≤ D ^ (1 / 3 : ℝ) * L)
  norm_num only [div_eq_mul_inv] at hleft hleft' hright ⊢
  nlinarith only [hleft, hleft', hright, hrootL, hhL, mul_nonneg hD hL]

/-- The literal non-curvature remainder pays the finite head, both endpoint constants, the stationary harmonic constant and an extra reciprocal pi. -/
theorem cubic_constant_budget {α β : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (M : ℕ) :
    1 / 2 + (Real.log 2 + 1 / ((M : ℝ) + 1) + 4.5) / Real.pi ≤
      (α * halfSecondEndpointBound M α + β * halfSecondEndpointBound M β) / (2 * Real.pi) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi) := by
  rw [printed_half_remainder_expand hα hβ M]
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have ha : (3 / 8 : ℝ) ≤ 0.75 / (α + 1) := by
    apply (le_div_iff₀ (by positivity : 0 < α + 1)).mpr
    linarith
  have hb : 0 ≤ 0.75 / (β + 1) + 0.5 / β := by positivity
  have hmain : (1 / 2 : ℝ) * Real.pi + (Real.log 2 + 1 / ((M : ℝ) + 1) + 4.5) ≤
      1.751 * Real.pi + (1 / ((M : ℝ) + 1) + 1.5 * Real.log 2 +
        0.75 / (α + 1) + 0.75 / (β + 1) + 0.5 / β) := by
    nlinarith [Real.pi_gt_d2]
  apply (mul_le_mul_iff_left₀ Real.pi_pos).mp
  simpa only [add_mul, div_mul_cancel₀ _ Real.pi_ne_zero] using hmain

end DhimanKadiriQuesadaHerrera2026

