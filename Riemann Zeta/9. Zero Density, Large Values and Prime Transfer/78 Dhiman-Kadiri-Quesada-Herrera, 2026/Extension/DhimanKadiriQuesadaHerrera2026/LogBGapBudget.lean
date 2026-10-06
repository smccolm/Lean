import DhimanKadiriQuesadaHerrera2026.LogBZeroFull
import DhimanKadiriQuesadaHerrera2026.PoissonCutoff

namespace DhimanKadiriQuesadaHerrera2026

/-- A rational cubic certificate for the remaining many-frequency curvature margin. -/
theorem many_gap_cubic_budget {q x δ : ℝ} (hq : 79 / 50 ≤ q) (hx : 0 < x) (hd : 0 < δ) :
    0.237 * q / δ ≤ 0.1585 * q ^ 2 * x + 1 / (2 * Real.pi ^ 2 * x ^ 2 * δ ^ 3) := by
  have hqp : 0 < q := by linarith
  have hp : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hpoly : 0 ≤ 3.17 * (x * δ * q) ^ 3 - 4.74 * (x * δ * q) ^ 2 + 1.58 := by
    have h := mul_nonneg (sq_nonneg (x * δ * q - 316 / 317))
      (by positivity : 0 ≤ x * δ * q + 158 / 317)
    nlinarith only [h]
  have hstep : 0.237 * q / δ - 0.1585 * q ^ 2 * x ≤ 1 / (20 * x ^ 2 * δ ^ 3) := by
    apply (le_div_iff₀ (by positivity : 0 < 20 * x ^ 2 * δ ^ 3)).mpr
    have he : ((0.237 * q / δ - 0.1585 * q ^ 2 * x) * (20 * x ^ 2 * δ ^ 3)) * q =
        4.74 * (x * δ * q) ^ 2 - 3.17 * (x * δ * q) ^ 3 := by field_simp; ring
    have hmul : ((0.237 * q / δ - 0.1585 * q ^ 2 * x) * (20 * x ^ 2 * δ ^ 3)) * q ≤ 1 * q := by
      rw [he]
      linarith
    exact (mul_le_mul_iff_left₀ hqp).mp hmul
  have hr : 0.237 * q / δ ≤ 0.1585 * q ^ 2 * x + 1 / (20 * x ^ 2 * δ ^ 3) := by linarith
  apply hr.trans
  apply add_le_add le_rfl
  exact one_div_le_one_div_of_le (by positivity)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : 2 * Real.pi ^ 2 ≤ 20)
      (sq_nonneg x)) (by positivity))

/-- A global square-root logarithm bound on the remaining many-frequency range. -/
theorem log_beta_add_two_le {β : ℝ} (hβ : 5 / 2 ≤ β) :
    Real.log (β + 2) ≤ 0.74 * Real.sqrt β + 0.35 := by
  have hβp : 0 < β := by linarith
  have hlog : Real.log (9 / 2 : ℝ) ≤ 1.51 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 9 / 2)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.51) 8
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hd (u : ℝ) : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + 2)) (2 * u / (u ^ 2 + 2)) u := by
    convert (((hasDerivAt_id u).pow 2).add_const 2).log (by positivity : u ^ 2 + 2 ≠ 0) using 1
    norm_num
  have hdle (u : ℝ) : 2 * u / (u ^ 2 + 2) ≤ 0.74 := by
    apply (div_le_iff₀ (by positivity : 0 < u ^ 2 + 2)).mpr
    nlinarith [sq_nonneg (u - 50 / 37)]
  have hxy := Real.sqrt_le_sqrt hβ
  have hv := (convex_Icc (Real.sqrt (5 / 2)) (Real.sqrt β)).image_sub_le_mul_sub_of_deriv_le
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
    (fun u _ => by rw [(hd u).deriv]; exact hdle u)
    (Real.sqrt (5 / 2)) (Set.left_mem_Icc.mpr hxy) (Real.sqrt β) (Set.right_mem_Icc.mpr hxy) hxy
  rw [Real.sq_sqrt hβp.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 2)] at hv
  norm_num only [show (5 / 2 : ℝ) + 2 = 9 / 2 by norm_num] at hv
  have hlo : (1.58 : ℝ) ≤ Real.sqrt (5 / 2) := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 2)
    have hn := Real.sqrt_nonneg (5 / 2)
    nlinarith
  linarith

/-- The unused stationary margin and cubic singularity cover the full logarithmic excess when the gap is at most one half. -/
theorem many_gap_log_budget {β x δ : ℝ} (hβ : 5 / 2 ≤ β) (hx : 0 < x)
    (hd : 0 < δ) (hdh : δ ≤ 1 / 2) :
    (2 * Real.log (β + 2) + 21 / 8) / Real.pi + 1 / 72 - 1.751 + 1 / (Real.pi * δ) ≤
      0.1585 * β * x + 1 / (2 * Real.pi ^ 2 * x ^ 2 * δ ^ 3) := by
  have hβp : 0 < β := by linarith
  have hq : (79 / 50 : ℝ) ≤ Real.sqrt β := by
    have hs := Real.sq_sqrt hβp.le
    have hn := Real.sqrt_nonneg β
    nlinarith
  have hc := many_gap_cubic_budget hq hx hd
  rw [Real.sq_sqrt hβp.le] at hc
  apply le_trans _ hc
  have hp : 157 / 50 ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hip : 1 / Real.pi ≤ 50 / 157 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 157 / 50) hp
    norm_num at h
    simpa only [one_div] using h
  have hlog := log_beta_add_two_le hβ
  have hleft : (2 * Real.log (β + 2) + 21 / 8) / Real.pi ≤
      (1.48 * Real.sqrt β + 3.325) * (50 / 157) := by
    have h := div_le_div_of_nonneg_right (by linarith : 2 * Real.log (β + 2) + 21 / 8 ≤
      1.48 * Real.sqrt β + 3.325) Real.pi_pos.le
    have hh := mul_le_mul_of_nonneg_left hip (by positivity : 0 ≤ 1.48 * Real.sqrt β + 3.325)
    exact h.trans (by simpa only [div_eq_mul_inv, one_mul] using hh)
  have hdinv : (2 : ℝ) ≤ 1 / δ := by
    have h := one_div_le_one_div_of_le hd hdh
    norm_num at h
    simpa only [one_div] using h
  have hn : 0 ≤ 0.237 * Real.sqrt β - 1 / Real.pi := by linarith
  have hgap := mul_le_mul_of_nonneg_left hdinv hn
  have he : (0.237 * Real.sqrt β - 1 / Real.pi) * (1 / δ) =
      0.237 * Real.sqrt β / δ - 1 / (Real.pi * δ) := by ring
  rw [he] at hgap
  nlinarith only [hleft, hgap, hip, Real.sqrt_nonneg β]

/-- The two printed constant-weight coefficients retain their leading cubic singularity at every upper frequency. -/
theorem printed_constant_coefficient_lower {β : ℝ} (hβ : 0 < β) :
    1 / ((⌊β⌋₊ : ℝ) + 1 - β) ^ 3 - 1 / (2 * (1 + β) ^ 2) ≤
      printedPartIIE1 β / β + partIICubeCoefficient β := by
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
  rw [he]
  change 1 / d ^ 3 - _ ≤ _
  have hp : 0 ≤ 1 / (d + 1) ^ 3 + 1 / (2 * (d + 1) ^ 2) +
      1 / (β * (d + 1) ^ 2) + 1 / (2 * ((⌊β⌋₊ : ℝ) + 1) * β ^ 2) := by positivity
  linarith

/-- The harmless negative rational correction costs at most one seventy-second at the logarithmic endpoint scale. -/
theorem printed_constant_tail_lower {β κ : ℝ} (hβ : 0 < β) (hκ : 0 ≤ κ) (hκβ : κ ≤ 2 * β) :
    κ / (2 * Real.pi ^ 2 * ((⌊β⌋₊ : ℝ) + 1 - β) ^ 3) - 1 / 72 ≤
      κ / (2 * Real.pi ^ 2) * (printedPartIIE1 β / β + partIICubeCoefficient β) := by
  have h := mul_le_mul_of_nonneg_left (printed_constant_coefficient_lower hβ)
    (by positivity : 0 ≤ κ / (2 * Real.pi ^ 2))
  have hloss : κ / (4 * Real.pi ^ 2 * (1 + β) ^ 2) ≤ 1 / 72 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.pi ^ 2 * (1 + β) ^ 2)).mpr
    have hp : 9 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hm := mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (1 + β))
    nlinarith [sq_nonneg (β - 1)]
  have he : κ / (2 * Real.pi ^ 2) *
      (1 / ((⌊β⌋₊ : ℝ) + 1 - β) ^ 3 - 1 / (2 * (1 + β) ^ 2)) =
      κ / (2 * Real.pi ^ 2 * ((⌊β⌋₊ : ℝ) + 1 - β) ^ 3) -
        κ / (4 * Real.pi ^ 2 * (1 + β) ^ 2) := by field_simp; ring
  rw [he] at h
  linarith

/-- The complete shifted-cutoff excess is absorbed by the literal printed error in the many-frequency small-gap range. -/
theorem many_gap_printed_budget {α β κ x : ℝ} (hαp : 0 < α) (hα : α < 1) (hβ : 5 / 2 ≤ β)
    (hx : 0 < x) (hscale : κ * x ^ 2 = 1) (hκβ : κ ≤ 2 * β)
    (hdh : (⌊β⌋₊ : ℝ) + 1 - β ≤ 1 / 2) :
    2 / Real.pi + 1 / (Real.pi * ((⌊β⌋₊ : ℝ) + 1 - β)) +
      (1 / Real.pi) * (Real.log ((⌊β⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊β⌋₊ : ℝ) + 2)) -
          (Complex.digamma ((⌊β⌋₊ : ℝ) + 2 - β : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + β) - 1 / (2 * (1 + β)) +
          Real.log 2 + 1 / ((⌊β⌋₊ : ℝ) + 1)) ≤
      0.1585 * β * x + ((α * halfSecondEndpointBound ⌊β⌋₊ α +
          β * halfSecondEndpointBound ⌊β⌋₊ β) / (2 * Real.pi) +
        κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  have hβp : 0 < β := by linarith
  have hκeq : κ = 1 / x ^ 2 := (eq_div_iff (pow_ne_zero 2 hx.ne')).mpr hscale
  have hκ : 0 ≤ κ := by rw [hκeq]; positivity
  let d := (⌊β⌋₊ : ℝ) + 1 - β
  have hd : 0 < d := by dsimp [d]; linarith [Nat.lt_floor_add_one β]
  have hc := many_gap_log_budget hβ hx hd hdh
  have ht := printed_constant_tail_lower hβp hκ hκβ
  have hcube : 1 / (2 * Real.pi ^ 2 * x ^ 2 * d ^ 3) = κ / (2 * Real.pi ^ 2 * d ^ 3) := by
    rw [hκeq]
    field_simp
  rw [hcube] at hc
  have hcoef : κ / (2 * Real.pi ^ 2) * (printedPartIIE1 β / β + partIICubeCoefficient β) =
      κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) := by ring
  rw [hcoef] at ht
  let L := Real.log ((⌊β⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊β⌋₊ : ℝ) + 2)) -
      (Complex.digamma ((⌊β⌋₊ : ℝ) + 2 - β : ℝ)).re +
      Real.eulerMascheroniConstant + Real.log (1 + β) - 1 / (2 * (1 + β)) +
      Real.log 2 + 1 / ((⌊β⌋₊ : ℝ) + 1)
  let H := ((α * halfSecondEndpointBound ⌊β⌋₊ α + β * halfSecondEndpointBound ⌊β⌋₊ β) / (2 * Real.pi) +
      1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi))
  let Q := 1 / ((⌊β⌋₊ : ℝ) + 1) + 1.5 * Real.log 2 + 0.75 / (α + 1) + 0.75 / (β + 1) + 0.5 / β
  have hH : H = 1.751 + Q / Real.pi := by
    dsimp [H, Q, halfSecondEndpointBound]
    field_simp
    ring
  have hψ := real_digamma_monotone (by norm_num : (0 : ℝ) < 1)
    (show 1 ≤ (⌊β⌋₊ : ℝ) + 2 - β by dsimp [d] at hd; linarith)
  simp only [Complex.ofReal_one, real_digamma_one] at hψ
  have hlM := Real.log_le_log (by positivity : 0 < (⌊β⌋₊ : ℝ) + 2)
    (add_le_add (Nat.floor_le hβp.le) le_rfl)
  have hlβ := Real.log_le_log (by positivity : 0 < 1 + β) (show 1 + β ≤ β + 2 by linarith)
  have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hαq : (3 / 8 : ℝ) ≤ 0.75 / (α + 1) := by
    apply (le_div_iff₀ (by positivity : 0 < α + 1)).mpr
    linarith
  have hQ : 2 + L - Q ≤ 2 * Real.log (β + 2) + 21 / 8 := by
    dsimp [L, Q]
    have h1 : 0 ≤ 1 / (2 * ((⌊β⌋₊ : ℝ) + 2)) := by positivity
    have h2 : 0 ≤ 1 / (2 * (1 + β)) := by positivity
    have h3 : 0 ≤ 0.75 / (β + 1) := by positivity
    have h4 : 0 ≤ 0.5 / β := by positivity
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hhead : 2 / Real.pi + (1 / Real.pi) * L - H ≤
      (2 * Real.log (β + 2) + 21 / 8) / Real.pi - 1.751 := by
    rw [hH]
    have h := div_le_div_of_nonneg_right hQ Real.pi_pos.le
    norm_num only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  change 2 / Real.pi + 1 / (Real.pi * d) + (1 / Real.pi) * L ≤ _
  have he : ((α * halfSecondEndpointBound ⌊β⌋₊ α + β * halfSecondEndpointBound ⌊β⌋₊ β) / (2 * Real.pi) +
        κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi)) =
      H + (κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2)) := by
    dsimp [H]
    ring
  rw [he]
  change κ / (2 * Real.pi ^ 2 * d ^ 3) - 1 / 72 ≤ _ at ht
  linarith

/-- The literal logarithmic source remainder holds for many frequencies with a small endpoint gap. -/
theorem logarithmic_b_process_printed_small_gap {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1) (hM : 2 ≤ ⌊c / a⌋₊)
    (hδ : (⌊c / a⌋₊ : ℝ) + 1 - c / a ≤ 1 / 2)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  have hb := ha.trans hab
  have hβp : 0 < c / a := div_pos hc ha
  have hβ25 : 5 / 2 ≤ c / a := by
    have hMR : (2 : ℝ) ≤ ⌊c / a⌋₊ := by exact_mod_cast hM
    linarith
  have hup (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hscl := afePhase_b_process_scales hc ha hab.le
  have hr := afePhase_constant_secondOrderRegularity hc ha hab
  have hβeq := (afePhase_hasDerivAt c ha).deriv
  have hγ := (afePhase_hasDerivAt c hb).deriv
  have hanti := (afePhase_strictAnti hc).mono (fun u (hu : u ∈ Set.Icc a b) => hup u hu)
  obtain ⟨ξ, hξ, ht⟩ := exists_b_process_next_cutoff (D := 2 * c / a ^ 3) (ℓ := c / b ^ 2)
    (h₂ := b ^ 2 / a ^ 2) hab (by positivity) (by rw [hγ]; positivity)
    (by rw [hγ]; exact hα) (by rw [hβeq]; exact hM) hah hbh hr.f_differentiable hr.f_deriv_differentiable
    (fun u hu => (afePhase_second_hasDerivAt c (hup u hu)).differentiableAt)
    hanti hscl.1 hscl.2.1 hscl.2.2
  rw [hβeq] at hξ ht
  rw [hγ] at ht
  have hmain : (∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊,
      Complex.exp (2 * Real.pi * Complex.I * ((afePhase c (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv (afePhase c)) (ξ ν)| : ℂ)) =
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro ν hν
    have hxp := hξ ν hν
    exact afePhase_stationary_term hc (hup (ξ ν) hxp.1)
      (by exact_mod_cast (show 0 < ν by have h := (Finset.mem_Icc.mp hν).1; omega)) hxp.2
  rw [hmain] at ht
  simp only [afePhase] at ht
  have haHalf : (1 / 2 : ℝ) ≤ a := by
    obtain ⟨k, hk⟩ := hah
    have hk0 : (0 : ℤ) ≤ k := by
      by_contra hn
      have hn' : k ≤ -1 := by omega
      have hr : (k : ℝ) ≤ -1 := by exact_mod_cast hn'
      linarith
    have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk0
    linarith
  have hκβ : c / a ^ 2 ≤ 2 * (c / a) := by
    have hd := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) haHalf
    have hm := mul_le_mul_of_nonneg_left hd hβp.le
    norm_num at hm
    convert hm using 1 <;> ring
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hscale : (c / a ^ 2) * (a / Real.sqrt c) ^ 2 = 1 := by
    field_simp
    rw [Real.sq_sqrt hc.le]
  have hbudget := many_gap_printed_budget (div_pos hc hb) hα hβ25 (div_pos ha hsq) hscale hκβ hδ
  have hmargin : (c / a) * (a / Real.sqrt c) ≤ 1 / Real.sqrt (c / b ^ 2) := by
    have hcb : c ≤ b := ((div_lt_one hb).mp hα).le
    have he1 : (c / a) * (a / Real.sqrt c) = c / Real.sqrt c := by field_simp
    have he2 : 1 / Real.sqrt (c / b ^ 2) = b / Real.sqrt c := by
      rw [Real.sqrt_div hc.le, Real.sqrt_sq_eq_abs, abs_of_pos hb]
      field_simp
    rw [he1, he2]
    exact div_le_div_of_nonneg_right hcb hsq.le
  have hmargin' := mul_le_mul_of_nonneg_left hmargin (by norm_num : (0 : ℝ) ≤ 0.1585)
  have hcap := min_le_right (0.6715 / Real.sqrt (c / b ^ 2))
    (1 / (Real.pi * ((⌊c / a⌋₊ : ℝ) + 1 - c / a)))
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hbudget hmargin' hcap ht ⊢
  nlinarith only [ht, hbudget, hmargin', hcap]

/-- The literal logarithmic B-process holds for every endpoint gap when there are at least two stationary frequencies. -/
theorem logarithmic_b_process_printed_many_full {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1) (hβ : 2 ≤ c / a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊c / a⌋₊, ((Real.sqrt c / (ν : ℝ) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (c / (ν : ℝ)) - c - 1 / 8 : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt (c / b ^ 2) +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * (b ^ 2 / a ^ 2) *
          (2 * c / a ^ 3) ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (c / a - c / b) +
      (((c / b) * halfSecondEndpointBound ⌊c / a⌋₊ (c / b) +
          (c / a) * halfSecondEndpointBound ⌊c / a⌋₊ (c / a)) / (2 * Real.pi) +
        (c / a ^ 2) * printedPartIIE1 (c / a) / (2 * Real.pi ^ 2 * (c / a)) +
        (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * (c / a)) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  by_cases hd : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a
  · exact logarithmic_b_process_printed hc ha hab hα hβ hd hah hbh
  · have hM : 2 ≤ ⌊c / a⌋₊ := by
      exact (Nat.le_floor_iff (by positivity : 0 ≤ c / a)).mpr (by exact_mod_cast hβ)
    exact logarithmic_b_process_printed_small_gap hc ha hab hα hM (le_of_not_ge hd) hah hbh

end DhimanKadiriQuesadaHerrera2026
