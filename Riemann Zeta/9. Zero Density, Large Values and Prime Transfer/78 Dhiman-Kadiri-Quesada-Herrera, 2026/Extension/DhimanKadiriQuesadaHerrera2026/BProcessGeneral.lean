import DhimanKadiriQuesadaHerrera2026.LargeDBudget

namespace DhimanKadiriQuesadaHerrera2026

/-- The exact source exponential has unit norm. -/
theorem norm_source_exponential (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
  have he : 2 * Real.pi * Complex.I * (t : ℂ) = (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  rw [he]
  exact Complex.norm_exp_ofReal_mul_I _

/-- A source half-integer sum contains exactly the interval length in unit-norm terms. -/
theorem norm_source_discrete_le_length {a b : ℝ} (f : ℝ → ℝ) (hab : a ≤ b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))‖ ≤ b - a := by
  have hh := norm_sum_le (Finset.Ioc ⌊a⌋ ⌊b⌋) (fun n : ℤ => Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ)))
  simp only [norm_source_exponential, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
  have hc := Int.card_Ioc_of_le ⌊a⌋ ⌊b⌋ (Int.floor_mono hab)
  have hc' : ((Finset.Ioc ⌊a⌋ ⌊b⌋).card : ℝ) = (⌊b⌋ : ℝ) - (⌊a⌋ : ℝ) := by exact_mod_cast hc
  rw [hc'] at hh
  obtain ⟨j, rfl⟩ := hah
  obtain ⟨k, rfl⟩ := hbh
  norm_num [Int.floor_intCast_add] at hh ⊢
  exact hh

/-- The actual stationary sum is bounded by its frequency count and the lower curvature. -/
theorem norm_source_stationary_le {f : ℝ → ℝ} {a b ℓ : ℝ} {M : ℕ} (ξ : ℕ → ℝ) (hℓ : 0 < ℓ)
    (hξ : ∀ ν ∈ Finset.Icc 1 M, ξ ν ∈ Set.Icc a b)
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|) :
    ‖∑ ν ∈ Finset.Icc 1 M,
      Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤ (M : ℝ) / Real.sqrt ℓ := by
  apply (norm_sum_le _ _).trans
  have ht : (∑ ν ∈ Finset.Icc 1 M,
      ‖Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖) ≤ ∑ _ν ∈ Finset.Icc 1 M, 1 / Real.sqrt ℓ := by
    apply Finset.sum_le_sum
    intro ν hν
    rw [norm_div, norm_source_exponential, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hℓ) (Real.sqrt_le_sqrt (hlower _ (hξ ν hν)))
  apply ht.trans_eq
  simp [Nat.card_Icc, div_eq_mul_inv]

/-- The literal remainder supplies at least its full constant 1.751. -/
theorem printed_half_remainder_full_lower {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hκ : 0 ≤ κ) :
    (1.751 : ℝ) ≤
      (α * halfSecondEndpointBound ⌊β⌋₊ α + β * halfSecondEndpointBound ⌊β⌋₊ β) / (2 * Real.pi) +
        κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi) := by
  have hc := mul_nonneg (by positivity : 0 ≤ κ / (2 * Real.pi ^ 2)) (printed_constant_coefficient_nonneg hβ)
  have he : κ / (2 * Real.pi ^ 2) * (printedPartIIE1 β / β + partIICubeCoefficient β) =
      κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) := by ring
  rw [he] at hc
  have hh := printed_half_remainder_expand hα hβ ⌊β⌋₊
  have hp : 0 ≤ (1 / ((⌊β⌋₊ : ℝ) + 1) + 1.5 * Real.log 2 +
      0.75 / (α + 1) + 0.75 / (β + 1) + 0.5 / β) / Real.pi := by positivity
  linarith

set_option maxHeartbeats 800000 in
/-- The literal B-process for third-derivative scale at least four and upper slope at most 26. -/
theorem exists_b_process_large_D_small_beta {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hβ : 2 ≤ deriv f a) (hβ26 : deriv f a ≤ 26) (hD4 : 4 ≤ D)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  have haa := Set.left_mem_Icc.mpr hab.le
  have hL : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hκ : ℓ ≤ h₂ * ℓ := (hlower a haa).trans (hupper a haa)
  have hh₂ : 1 ≤ h₂ := by nlinarith
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
  have hdisc := norm_source_discrete_le_length f hab.le hah hbh
  have hdual := norm_source_stationary_le ξ hℓ (fun ν hν => (hξ ν hν).1) hlower
  have ht := (norm_sub_le _ _).trans (add_le_add hdisc hdual)
  have hfloor := div_le_div_of_nonneg_right (Nat.floor_le (by linarith : 0 ≤ deriv f a)) (Real.sqrt_nonneg ℓ)
  have hwidth := derivative_range_le_curvature hab.le hf' hupper
  have hroot := Real.sqrt_pos.mpr hℓ
  have hrootsq := Real.sq_sqrt hℓ.le
  let x := 1 / Real.sqrt ℓ
  have hx : 0 < x := by dsimp [x]; positivity
  have hxℓ : ℓ * x ^ 2 = 1 := by dsimp [x]; field_simp; nlinarith only [hrootsq]
  have hK : (deriv f a - 1) * x ^ 2 ≤ h₂ * (b - a) := by
    have hm := mul_le_mul_of_nonneg_right (show deriv f a - 1 ≤ h₂ * ℓ * (b - a) by linarith) (sq_nonneg x)
    have he : h₂ * ℓ * (b - a) * x ^ 2 = h₂ * (b - a) := by calc
      _ = h₂ * (b - a) * (ℓ * x ^ 2) := by ring
      _ = _ := by rw [hxℓ]; ring
    rwa [he] at hm
  have hcoef := large_D_nonlinear_lower hD4
  have hlarge : 3 ≤ (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) := by
    norm_num only [div_eq_mul_inv] at hcoef ⊢
    nlinarith only [hcoef]
  have hnl := mul_le_mul_of_nonneg_right hlarge (by positivity : 0 ≤ h₂ * (b - a))
  have hlen := mul_le_mul_of_nonneg_right hh₂ hL
  have hrem := printed_half_remainder_full_lower hαpos (by linarith : 0 < deriv f a) (by positivity : 0 ≤ h₂ * ℓ)
  have hlog0 : 0 ≤ 2 / Real.pi * Real.log (deriv f a - deriv f b) := by
    apply mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  refine ⟨ξ, hξ, ?_⟩
  apply ht.trans
  by_cases hsmall : deriv f a ≤ 18
  · have hq := large_D_small_quadratic (x := x) hβ hsmall
    dsimp only [x] at hq hK
    norm_num only [div_eq_mul_inv] at hq hK hnl hfloor hrem hlog0 ⊢
    nlinarith only [hq, hK, hnl, hfloor, hlen, hrem, hlog0]
  · have hq := large_D_middle_quadratic (x := x) (le_of_not_ge hsmall) hβ26
    have hlog1 : 1 ≤ 2 / Real.pi * Real.log (deriv f a - deriv f b) := by
      have hlo : 2 ≤ Real.log (deriv f a - deriv f b) := by
        have hl' := Real.log_le_log (by norm_num : (0 : ℝ) < 16) (by linarith : 16 ≤ deriv f a - deriv f b)
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at hl'
        norm_num at hl'
        linarith [Real.log_two_gt_d9]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ Real.pi_pos).mpr
      nlinarith [Real.pi_lt_d2]
    dsimp only [x] at hq hK
    norm_num only [div_eq_mul_inv] at hq hK hnl hfloor hrem hlog1 ⊢
    nlinarith only [hq, hK, hnl, hfloor, hlen, hrem, hlog1]


set_option maxHeartbeats 800000 in
/-- The literal general B-process for the remaining large-derivative, large-frequency range. -/
theorem exists_b_process_large_D_large_beta {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hβ : 26 ≤ deriv f a) (hD4 : 4 ≤ D)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  have haa := Set.left_mem_Icc.mpr hab.le
  have hL : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hκ : ℓ ≤ h₂ * ℓ := (hlower a haa).trans (hupper a haa)
  have hh₂ : 1 ≤ h₂ := by nlinarith
  have hM : 2 ≤ ⌊deriv f a⌋₊ := Nat.le_floor (show (2 : ℝ) ≤ deriv f a by linarith)
  obtain ⟨ξ, hξ, ht⟩ := exists_b_process_next_tight hab hℓ hαpos hα hM hah hbh hf hf' hf'' hanti hlower hupper hD
  have hwidth := derivative_range_le_curvature hab.le hf' hupper
  have hroot := Real.sqrt_pos.mpr hℓ
  have hrootsq := Real.sq_sqrt hℓ.le
  let x := 1 / Real.sqrt ℓ
  let d := (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a
  have hd : 0 < d := by dsimp [d]; linarith [Nat.lt_floor_add_one (deriv f a)]
  have hd1 : d ≤ 1 := by dsimp [d]; linarith [Nat.floor_le (by linarith : 0 ≤ deriv f a)]
  have hxℓ : ℓ * x ^ 2 = 1 := by dsimp [x]; field_simp; nlinarith only [hrootsq]
  have hK : (deriv f a - 1) * x ^ 2 ≤ h₂ * (b - a) := by
    have hm := mul_le_mul_of_nonneg_right (show deriv f a - 1 ≤ h₂ * ℓ * (b - a) by linarith) (sq_nonneg x)
    have he : h₂ * ℓ * (b - a) * x ^ 2 = h₂ * (b - a) := by calc
      _ = h₂ * (b - a) * (ℓ * x ^ 2) := by ring
      _ = _ := by rw [hxℓ]; ring
    rwa [he] at hm
  have hprod : deriv f a - 1 ≤ (h₂ * (b - a)) * (h₂ * ℓ) := by
    have hm := mul_le_mul_of_nonneg_right hh₂ (by positivity : 0 ≤ h₂ * ℓ * (b - a))
    nlinarith only [hm, hwidth, hα]
  have hp := large_D_poisson_excess hαpos hα hβ
  have hn := large_D_near_budget (x := x) (w := deriv f a - 1) (d := d) (by linarith)
  have hg := large_D_log_gap_budget hβ hd hd1
  have hc := large_D_curvature_length hβ (by positivity : 0 ≤ h₂ * (b - a)) (by positivity : 0 ≤ h₂ * ℓ) hprod
  have hnl := mul_le_mul_of_nonneg_right (large_D_nonlinear_lower hD4) (by positivity : 0 ≤ h₂ * (b - a))
  refine ⟨ξ, hξ, ht.trans ?_⟩
  dsimp only at hp
  dsimp only [x, d] at hn hg hK
  norm_num only [div_eq_mul_inv, mul_inv_rev, one_mul, mul_one] at hp hn hg hc hnl hK ⊢
  nlinarith only [hp, hn, hg, hc, hnl, hK]

/-- The complete literal Corollary 0.2: every source phase, frequency count and positive endpoint gap. -/
theorem exists_b_process_printed_full {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  by_cases hD4 : D ≤ 4
  · exact exists_b_process_four_D hab hℓ hαpos hα hD4 hah hbh hf hf' hf'' hanti hlower hupper hD
  · by_cases hβ2 : deriv f a < 2
    · exact exists_b_process_printed_small hab hℓ hαpos hα hβ2 hah hbh hf hf' hf'' hanti hlower hupper hD
    · by_cases hβ26 : deriv f a ≤ 26
      · exact exists_b_process_large_D_small_beta hab hℓ hαpos hα (le_of_not_gt hβ2) hβ26
          (le_of_not_ge hD4) hah hbh hf' hanti hlower hupper
      · exact exists_b_process_large_D_large_beta hab hℓ hαpos hα (le_of_not_ge hβ26)
          (le_of_not_ge hD4) hah hbh hf hf' hf'' hanti hlower hupper hD

/-- The source third-derivative scales are retained in the complete literal general B-process. -/
theorem exists_source_b_process_printed_full {f : ℝ → ℝ} {a b ℓ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  obtain ⟨ξ, hξ, h⟩ := exists_b_process_printed_full hab hℓ hαpos hα hah hbh hf hf' hf'' hanti hlower hupper hD
  refine ⟨ξ, hξ, ?_⟩
  apply h.trans_eq
  rw [Real.mul_rpow hh₃ hℓ₃]
  ring

/-- The literal source corollary holds for any supplied family of its unique stationary points. -/
theorem source_b_process_printed {f : ℝ → ℝ} {a b ℓ ℓ₃ h₂ h₃ : ℝ}
    (ξ : ℕ → ℝ)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hab : a < b) (hℓ : 0 < ℓ) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  obtain ⟨η, hη, hb⟩ := exists_source_b_process_printed_full hab hℓ hℓ₃ hh₃ hαpos hα hah hbh hf hf' hf'' hanti hlower hupper hD
  have hpoint (ν : ℕ) (hν : ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊) : η ν = ξ ν :=
    hanti.injOn (hη ν hν).1 (hξ ν hν).1 ((hη ν hν).2.trans (hξ ν hν).2.symm)
  have he : (∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      Complex.exp (2 * Real.pi * Complex.I * ((f (η ν) - (ν : ℝ) * η ν - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) (η ν)| : ℂ)) =
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ) := by
    apply Finset.sum_congr rfl
    intro ν hν
    rw [hpoint ν hν]
  rwa [he] at hb

end DhimanKadiriQuesadaHerrera2026
