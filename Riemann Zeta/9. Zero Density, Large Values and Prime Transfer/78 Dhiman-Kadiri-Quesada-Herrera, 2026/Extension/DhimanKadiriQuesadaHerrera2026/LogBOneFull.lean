import DhimanKadiriQuesadaHerrera2026.LogBGapBudget

namespace DhimanKadiriQuesadaHerrera2026

/-- A single stationary frequency with upper derivative at least three halves leaves a larger curvature margin. -/
theorem stationary_one_left_far {f : ℝ → ℝ} {a b c ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hβ : 3 / 2 ≤ deriv f a) (hc : c ∈ Set.Icc a b) (hstat : deriv f c = 1)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc (0 : ℕ) 1, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      1.5995 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) + 2 / Real.pi := by
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hs := stationary_error_drop_right hℓ hc.1 hc.2 hstat hf hf' hf'' hcurv hD
  have hz := kershner_zero_frequency hab hℓ hf hf' hf'' hanti hαpos hlower
  have hg : 1 / 2 ≤ deriv f a - 1 := by linarith
  have hcap : stationaryEndpointCap ℓ (deriv f a - 1) ≤ 2 / Real.pi := by
    have h := stationaryEndpointCap_le_recip ℓ (by linarith : deriv f a - 1 ≠ 0)
    rw [abs_of_pos (by linarith : 0 < deriv f a - 1)] at h
    have hi := one_div_le_one_div_of_le (by positivity : 0 < Real.pi * (1 / 2))
      (mul_le_mul_of_nonneg_left hg Real.pi_pos.le)
    have he : 1 / (Real.pi * (1 / 2)) = 2 / Real.pi := by ring
    exact h.trans (by simpa only [he] using hi)
  have hw := derivative_range_le_curvature hab.le hf' hupper
  have hcount : 1 / 2 ≤ h₂ * ℓ * (b - a) := by linarith
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a (Set.left_mem_Icc.mpr hab.le))
  let C := 2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)
  have hdiv : 1 / (2 * ℓ) ≤ h₂ * (b - a) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * ℓ)).mpr
    nlinarith
  have hnonlin : (C * D ^ (1 / 3 : ℝ) / ℓ) / 2 ≤ C * h₂ * D ^ (1 / 3 : ℝ) * (b - a) := by
    have h := mul_le_mul_of_nonneg_left hdiv (by dsimp [C]; positivity : 0 ≤ C * D ^ (1 / 3 : ℝ))
    convert h using 1 <;> ring
  have he : Finset.Icc (0 : ℕ) 1 = {0, 1} := by decide
  rw [he, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
  simp only [Nat.cast_zero, zero_mul, sub_zero, Nat.cast_one, one_mul]
  rw [add_sub_assoc]
  have ht := (norm_add_le _ _).trans (add_le_add hz hs)
  simp only [one_mul] at ht
  change (C * D ^ (1 / 3 : ℝ) / ℓ) / 2 ≤ _ at hnonlin
  dsimp [C] at hnonlin
  norm_num only [div_eq_mul_inv] at hnonlin ht hcap ⊢
  nlinarith only [ht, hcap, hnonlin]

/-- A rational logarithm enclosure for the single-frequency cutoff. -/
theorem log_three_le_eleven_tenths : Real.log 3 ≤ 11 / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 10) 8
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The single-frequency small-gap shifted-cutoff error fits the literal printed remainder. -/
theorem one_gap_printed_budget {α β κ x : ℝ} (hαp : 0 < α) (hα : α < 1)
    (hβ : 3 / 2 ≤ β) (hβ2 : β < 2) (hx : 0 < x) (hscale : κ * x ^ 2 = 1) (hκβ : κ ≤ 2 * β) :
    2 / Real.pi + 1 / (Real.pi * (2 - β)) +
      (1 / Real.pi) * (Real.log 3 - 1 / (2 * 3) - (Complex.digamma ((3 - β : ℝ) : ℂ)).re +
        Real.eulerMascheroniConstant + Real.log (1 + β) - 1 / (2 * (1 + β)) + Real.log 2 + 1 / 2) ≤
      1.0865 * β * x + 2 / Real.pi * Real.log (β - α) +
      ((α * halfSecondEndpointBound 1 α + β * halfSecondEndpointBound 1 β) / (2 * Real.pi) +
        κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  have hβp : 0 < β := by linarith
  have hf : ⌊β⌋₊ = 1 := Nat.floor_eq_iff hβp.le |>.mpr ⟨by norm_num; linarith, by norm_num; exact hβ2⟩
  have hd : 0 < 2 - β := by linarith
  have hdh : 2 - β ≤ 1 / 2 := by linarith
  have hκeq : κ = 1 / x ^ 2 := (eq_div_iff (pow_ne_zero 2 hx.ne')).mpr hscale
  have hκ : 0 ≤ κ := by rw [hκeq]; positivity
  have hc := many_gap_cubic_budget (q := 16 / 5) (by norm_num) hx hd
  have hcube : 1 / (2 * Real.pi ^ 2 * x ^ 2 * (2 - β) ^ 3) = κ / (2 * Real.pi ^ 2 * (2 - β) ^ 3) := by
    rw [hκeq]
    field_simp
  rw [hcube] at hc
  have hmargin : (10144 / 6250 : ℝ) * x ≤ 1.0865 * β * x := by nlinarith
  have hgap : 0.7584 / (2 - β) ≤ 1.0865 * β * x + κ / (2 * Real.pi ^ 2 * (2 - β) ^ 3) := by
    norm_num only [div_eq_mul_inv] at hc ⊢
    nlinarith only [hc, hmargin]
  have hp : Real.pi ≤ 10 / 3 := by linarith [Real.pi_lt_d2]
  have hip : 1 / Real.pi ≤ (1 / 3 : ℝ) := one_div_le_one_div_of_le (by norm_num) Real.pi_gt_three.le
  have hsmall : 33 / 40 + 1 / (Real.pi * (2 - β)) ≤ 0.7584 / (2 - β) := by
    apply (le_div_iff₀ hd).mpr
    have he : (33 / 40 + 1 / (Real.pi * (2 - β))) * (2 - β) = 33 / 40 * (2 - β) + 1 / Real.pi := by field_simp
    rw [he]
    linarith
  let L := Real.log 3 - 1 / (2 * 3) - (Complex.digamma ((3 - β : ℝ) : ℂ)).re +
    Real.eulerMascheroniConstant + Real.log (1 + β) - 1 / (2 * (1 + β)) + Real.log 2 + 1 / 2
  have hψ := real_digamma_monotone (by norm_num : (0 : ℝ) < 1) (show 1 ≤ 3 - β by linarith)
  simp only [Complex.ofReal_one, real_digamma_one] at hψ
  have hL : L ≤ 71 / 15 := by
    have hl := Real.log_le_log (by positivity : 0 < 1 + β) (show 1 + β ≤ 3 by linarith)
    have hn : 0 ≤ 1 / (2 * (1 + β)) := by positivity
    dsimp [L]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds, log_three_le_eleven_tenths, log_two_le_seven_tenths]
  have hconst : 2 / Real.pi + (1 / Real.pi) * L ≤ 101 / 45 := by
    have h := div_le_div_of_nonneg_right (by linarith : 2 + L ≤ 101 / 15) Real.pi_pos.le
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 101 / 15) (by norm_num : (0 : ℝ) < 3) Real.pi_gt_three.le
    norm_num only [div_eq_mul_inv] at h hh ⊢
    nlinarith only [h, hh]
  have hlogloss : -(7 / 15 : ℝ) ≤ 2 / Real.pi * Real.log (β - α) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) (show 1 / 2 ≤ β - α by linarith)
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub] at hl
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 / Real.pi)
    have hi := mul_le_mul_of_nonneg_left hip (by norm_num : (0 : ℝ) ≤ 2)
    have hn := mul_nonneg (by positivity : 0 ≤ 2 / Real.pi) (show 0 ≤ 7 / 10 - Real.log 2 by linarith [log_two_le_seven_tenths])
    norm_num only [div_eq_mul_inv] at hh hi hn ⊢
    nlinarith only [hh, hi, hn]
  let H := (α * halfSecondEndpointBound 1 α + β * halfSecondEndpointBound 1 β) / (2 * Real.pi) +
    1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi)
  have hHeq : H = 1.751 + Real.log 2 / (2 * Real.pi) + 1 / (2 * Real.pi * β) +
      (1 + 2 * Real.log 2 + 1.5 / (α + 1) + 1.5 / (β + 1)) / (2 * Real.pi) := by
    dsimp [H, halfSecondEndpointBound]
    norm_num only [Nat.cast_one]
    field_simp
    ring
  have hH : 1.9 ≤ H := by
    have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hl : (1 / 10 : ℝ) ≤ Real.log 2 / (2 * Real.pi) :=
      (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr (by linarith)
    have hr : (3 / 40 : ℝ) ≤ 1 / (2 * Real.pi * β) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi * β)).mpr
      have hh := mul_le_mul_of_nonneg_left hβ2.le Real.pi_pos.le
      nlinarith
    have hn : 0 ≤ (1 + 2 * Real.log 2 + 1.5 / (α + 1) + 1.5 / (β + 1)) / (2 * Real.pi) := by positivity
    rw [hHeq]
    linarith
  have ht := printed_constant_tail_lower hβp hκ hκβ
  simp only [hf, Nat.cast_one] at ht
  norm_num only [show (1 : ℝ) + 1 = 2 by norm_num] at ht
  have he : κ / (2 * Real.pi ^ 2) * (printedPartIIE1 β / β + partIICubeCoefficient β) =
      κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) := by ring
  rw [he] at ht
  change 2 / Real.pi + 1 / (Real.pi * (2 - β)) + (1 / Real.pi) * L ≤ _
  have hHsplit : ((α * halfSecondEndpointBound 1 α + β * halfSecondEndpointBound 1 β) / (2 * Real.pi) +
        κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi)) =
      H + (κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2)) := by dsimp [H]; ring
  rw [hHsplit]
  linarith only [hconst, hsmall, hgap, hlogloss, hH, ht]

/-- The remaining single-frequency logarithmic small-gap source theorem. -/
theorem logarithmic_b_process_printed_one_gap {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1) (hone : ⌊c / a⌋₊ = 1)
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
  have hβ15 : 3 / 2 ≤ c / a := by
    have hd := hδ
    simp only [hone, Nat.cast_one] at hd
    linarith
  have hβ2 : c / a < 2 := by
    have h := Nat.lt_floor_add_one (c / a)
    simpa only [hone, Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num] using h
  have hup (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hscl := afePhase_b_process_scales hc ha hab.le
  have hr := afePhase_constant_secondOrderRegularity hc ha hab
  have hβeq := (afePhase_hasDerivAt c ha).deriv
  have hγ := (afePhase_hasDerivAt c hb).deriv
  have hanti := (afePhase_strictAnti hc).mono (fun u (hu : u ∈ Set.Icc a b) => hup u hu)
  have hα' : deriv (afePhase c) b < 1 := by rw [hγ]; exact hα
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hr.f_deriv_continuous hanti hα'
  rw [hβeq] at hξ
  have hxp := hξ 1 (by simp [hone])
  simp only [Nat.cast_one] at hxp
  have hs := stationary_one_left_far (D := 2 * c / a ^ 3) (ℓ := c / b ^ 2) (h₂ := b ^ 2 / a ^ 2)
    hab (by positivity) (by rw [hγ]; positivity) hα' (by rw [hβeq]; exact hβ15) hxp.1 hxp.2
    hr.f_differentiable hr.f_deriv_differentiable
    (fun u hu => (afePhase_second_hasDerivAt c (hup u hu)).differentiableAt)
    hanti hscl.1 hscl.2.1 hscl.2.2
  have r := constant_weight_partIRegularity hab hr.f_differentiable hr.f_deriv_continuous
    hr.f_deriv_pos hanti.antitoneOn
  have hcurv := stationary_curvature_of_antitone hab hr.f_deriv_differentiable hanti.antitoneOn hscl.1
  have hp := poisson_next_cutoff_bound (M := 1) r (by positivity : 0 < c / b ^ 2)
    (by rw [hβeq]; norm_num; exact hβ2) hr.f_deriv_differentiable
    (fun u hu => (afePhase_second_hasDerivAt c (hup u hu)).continuousAt.continuousWithinAt) hcurv hah hbh
  have ht := (norm_add_le _ _).trans (add_le_add hp hs)
  simp only [sub_add_sub_cancel] at ht
  rw [hβeq] at ht
  have hm := afePhase_stationary_term hc (hup (ξ 1) hxp.1) (by norm_num : (0 : ℝ) < 1) hxp.2
  simp only [one_mul] at hm
  rw [hm] at ht
  simp only [afePhase, Nat.cast_one, div_one] at ht
  norm_num only [show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) + 2 = 3 by norm_num] at ht
  simp only [hone, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one]
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
  have hbudget := one_gap_printed_budget (div_pos hc hb) hα hβ15 hβ2 (div_pos ha hsq) hscale hκβ
  have hmargin : (c / a) * (a / Real.sqrt c) ≤ 1 / Real.sqrt (c / b ^ 2) := by
    have hcb : c ≤ b := ((div_lt_one hb).mp hα).le
    have he1 : (c / a) * (a / Real.sqrt c) = c / Real.sqrt c := by field_simp
    have he2 : 1 / Real.sqrt (c / b ^ 2) = b / Real.sqrt c := by
      rw [Real.sqrt_div hc.le, Real.sqrt_sq_eq_abs, abs_of_pos hb]
      field_simp
    rw [he1, he2]
    exact div_le_div_of_nonneg_right hcb hsq.le
  have hmargin' := mul_le_mul_of_nonneg_left hmargin (by norm_num : (0 : ℝ) ≤ 1.0865)
  have hcap := min_le_right (0.6715 / Real.sqrt (c / b ^ 2)) (1 / (Real.pi * (2 - c / a)))
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hbudget hmargin' hcap ht ⊢
  nlinarith only [ht, hbudget, hmargin', hcap]

/-- The logarithmic specialization of the literal B-process, for all frequency counts and every endpoint gap. -/
theorem logarithmic_b_process_printed_full {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1)
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
  by_cases hz : ⌊c / a⌋₊ = 0
  · exact logarithmic_b_process_printed_zero_full hc ha hab hz hah hbh
  by_cases ho : ⌊c / a⌋₊ = 1
  · by_cases hd : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a
    · exact logarithmic_b_process_printed_one hc ha hab hα ho hd hah hbh
    · exact logarithmic_b_process_printed_one_gap hc ha hab hα ho (le_of_not_ge hd) hah hbh
  · have hM : 2 ≤ ⌊c / a⌋₊ := by omega
    have hMR : (2 : ℝ) ≤ ⌊c / a⌋₊ := by exact_mod_cast hM
    have hfloor := Nat.floor_le (div_nonneg hc.le ha.le)
    exact logarithmic_b_process_printed_many_full hc ha hab hα (by linarith) hah hbh

end DhimanKadiriQuesadaHerrera2026
