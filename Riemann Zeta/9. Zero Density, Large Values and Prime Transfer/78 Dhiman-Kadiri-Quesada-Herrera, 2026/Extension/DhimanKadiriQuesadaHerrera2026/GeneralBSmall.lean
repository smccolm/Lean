import DhimanKadiriQuesadaHerrera2026.LogBOneFull

namespace DhimanKadiriQuesadaHerrera2026

/-- The combined literal square/cube coefficient is positive on the entire positive derivative range. -/
theorem printed_constant_coefficient_nonneg {β : ℝ} (hβ : 0 < β) :
    0 ≤ printedPartIIE1 β / β + partIICubeCoefficient β := by
  let d := (⌊β⌋₊ : ℝ) + 1 - β
  have hd : 0 < d := by dsimp [d]; linarith [Nat.lt_floor_add_one β]
  have hd1 : d ≤ 1 := by dsimp [d]; linarith [Nat.floor_le hβ.le]
  have hp : d ^ 3 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sq_nonneg d)]
  have hi : 1 ≤ 1 / d ^ 3 := (le_div_iff₀ (pow_pos hd 3)).mpr (by simpa)
  have hn : 1 / (2 * (1 + β) ^ 2) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (1 + β) ^ 2) (by norm_num : (0 : ℝ) < 2)).mpr
    nlinarith
  have h := printed_constant_coefficient_lower hβ
  change 1 / d ^ 3 - 1 / (2 * (1 + β) ^ 2) ≤ _ at h
  linarith

/-- The non-curvature part of the literal half-integer remainder keeps its exact endpoint expansion. -/
theorem printed_half_remainder_expand {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (M : ℕ) :
    (α * halfSecondEndpointBound M α + β * halfSecondEndpointBound M β) / (2 * Real.pi) +
      1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi) =
      1.751 + (1 / ((M : ℝ) + 1) + 1.5 * Real.log 2 +
        0.75 / (α + 1) + 0.75 / (β + 1) + 0.5 / β) / Real.pi := by
  unfold halfSecondEndpointBound
  field_simp
  ring

/-- The literal remainder alone is greater than three halves for all positive endpoint slopes. -/
theorem printed_half_remainder_lower {α β κ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hκ : 0 ≤ κ) :
    (3 / 2 : ℝ) ≤
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

/-- Raising the Poisson cutoff to one has a bounded error below derivative one. -/
theorem poisson_cutoff_one_small {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    (1 / Real.pi) * (Real.log 2 - 1 / (2 * 2) - (Complex.digamma ((2 - β : ℝ) : ℂ)).re +
      Real.eulerMascheroniConstant + Real.log (1 + β) - 1 / (2 * (1 + β)) + Real.log 2 + 1) ≤ 3 / 2 := by
  have hψ := real_digamma_monotone (by norm_num : (0 : ℝ) < 1) (by linarith : 1 ≤ 2 - β)
  simp only [Complex.ofReal_one, real_digamma_one] at hψ
  have hl := Real.log_le_log (by positivity : 0 < 1 + β) (by linarith : 1 + β ≤ 2)
  have hl2 : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
  have hg := Real.eulerMascheroniConstant_lt_two_thirds
  have hi : 0 ≤ 1 / (2 * (1 + β)) := by positivity
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_gt_three]

/-- The literal B-process bound holds for arbitrary source phases with no stationary frequency. -/
theorem b_process_printed_zero {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hzero : ⌊deriv f a⌋₊ = 0)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
  have hβp : 0 < deriv f a := hαpos.trans_le (hanti.antitoneOn haa hbb hab.le)
  have hβ1 : deriv f a < 1 := Nat.floor_eq_zero.mp hzero
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hcc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) := fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  have hr := constant_weight_partIRegularity hab hf hfc
    (fun u hu => hαpos.trans_le (hanti.antitoneOn hu hbb hu.2)) hanti.antitoneOn
  have hp := constant_partI_cutoff (M := 1) hr (by norm_num) (by norm_num; linarith : deriv f a < (1 : ℕ) + 1) hah hbh
  norm_num only [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num, div_one] at hp
  have hbnd := poisson_cutoff_one_small hβp hβ1
  norm_num only [show (2 : ℝ) * 2 = 4 by norm_num] at hbnd
  have hP := hp.trans hbnd
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hI0 := kershner_zero_frequency hab hℓ hf hf' hf'' hanti hαpos.le hlower
  have hI1 := kershner_monotone_bound hab.le hℓ hf hf' hcc hcurv 1
    (Or.inr (fun u hu => (hanti.antitoneOn haa hu hu.1).trans hβ1.le))
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  have hi0 : ‖I 0‖ ≤ 0.6715 / Real.sqrt ℓ := by simpa only [I, Nat.cast_zero, zero_mul, sub_zero] using hI0
  have hi1 : ‖I 1‖ ≤ 0.6715 / Real.sqrt ℓ := by simpa only [I, Nat.cast_one] using hI1
  have hset : Finset.Icc (0 : ℕ) 1 = {0, 1} := by decide
  have hi : ‖∑ ν ∈ Finset.Icc (0 : ℕ) 1, I ν‖ ≤ 1.343 / Real.sqrt ℓ := by
    rw [hset, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
    exact (norm_add_le _ _).trans ((add_le_add hi0 hi1).trans_eq (by ring))
  have ht := (norm_add_le _ _).trans (add_le_add hP hi)
  dsimp only [I] at ht
  simp only [sub_add_cancel] at ht
  have hlen := half_integer_length_ge_one hab hah hbh
  have hdrop := stationary_derivative_drop hf' hcurv haa hbb hab.le
  have hw : ℓ ≤ deriv f a - deriv f b := by nlinarith
  have hs := stationary_zero_budget hℓ hw
  have hh₂ : 0 ≤ h₂ := by have h := (hlower a haa).trans (hupper a haa); nlinarith
  have hκ : 0 ≤ h₂ * ℓ := mul_nonneg hh₂ hℓ.le
  have hrem := printed_half_remainder_lower hαpos hβp hκ
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a haa)
  have hn : 0 ≤ (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) := by positivity
  have hgap : 1.343 / Real.sqrt ℓ ≤ 2 / Real.sqrt ℓ := div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg ℓ)
  change ‖_‖ ≤ _ at ht
  linarith

/-- The literal remainder has a larger uniform reserve when exactly one stationary frequency is present. -/
theorem printed_half_one_lower {α β κ : ℝ} (hαp : 0 < α) (hα : α < 1)
    (hβp : 0 < β) (hβ : β < 2) (hκ : 0 ≤ κ) :
    (5 / 2 : ℝ) ≤
      (α * halfSecondEndpointBound 1 α + β * halfSecondEndpointBound 1 β) / (2 * Real.pi) +
        κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * β) + 1.251 + Real.log 2 / (2 * Real.pi) := by
  have hc := mul_nonneg (by positivity : 0 ≤ κ / (2 * Real.pi ^ 2)) (printed_constant_coefficient_nonneg hβp)
  have he : κ / (2 * Real.pi ^ 2) * (printedPartIIE1 β / β + partIICubeCoefficient β) =
      κ * printedPartIIE1 β / (2 * Real.pi ^ 2 * β) + κ * partIICubeCoefficient β / (2 * Real.pi ^ 2) := by ring
  rw [he] at hc
  have hh := printed_half_remainder_expand hαp hβp 1
  norm_num only [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num] at hh
  have h1 : 3 / 8 ≤ 0.75 / (α + 1) := (le_div_iff₀ (by positivity : 0 < α + 1)).mpr (by linarith)
  have h2 : 1 / 4 ≤ 0.75 / (β + 1) := (le_div_iff₀ (by positivity : 0 < β + 1)).mpr (by linarith)
  have h3 : 1 / 4 ≤ 0.5 / β := (le_div_iff₀ hβp).mpr (by linarith)
  have hlog : 2 / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hq : 3 / 4 ≤ (1 / 2 + 1.5 * Real.log 2 + 0.75 / (α + 1) + 0.75 / (β + 1) + 0.5 / β) / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_d2]
  linarith

/-- The enlarged upper cutoff at two is uniformly bounded throughout the single-frequency range. -/
theorem poisson_cutoff_two_small {β : ℝ} (hβ : 0 < β) (hβ2 : β < 2) :
    (1 / Real.pi) * (Real.log 3 - 1 / (2 * 3) - (Complex.digamma ((3 - β : ℝ) : ℂ)).re +
      Real.eulerMascheroniConstant + Real.log (1 + β) - 1 / (2 * (1 + β)) + Real.log 2 + 1 / 2) ≤ 3 / 2 := by
  have hψ := real_digamma_monotone (by norm_num : (0 : ℝ) < 1) (by linarith : 1 ≤ 3 - β)
  simp only [Complex.ofReal_one, real_digamma_one] at hψ
  have hl := Real.log_le_log (by positivity : 0 < 1 + β) (by linarith : 1 + β ≤ 3)
  have hi : 1 / 6 ≤ 1 / (2 * (1 + β)) := (le_div_iff₀ (by positivity : 0 < 2 * (1 + β))).mpr (by linarith)
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ Real.pi_pos).mpr
  linarith [Real.pi_gt_three, Real.eulerMascheroniConstant_lt_two_thirds, log_three_le_eleven_tenths, log_two_le_seven_tenths]

/-- At gap at least one half the original single-frequency Poisson cutoff costs at most 1.9. -/
theorem poisson_cutoff_one_half {β : ℝ} (hβ : 0 < β) (hβh : β ≤ 3 / 2) :
    (1 / Real.pi) * (Real.log 2 - 1 / (2 * 2) - (Complex.digamma ((2 - β : ℝ) : ℂ)).re +
      Real.eulerMascheroniConstant + Real.log (1 + β) - 1 / (2 * (1 + β)) + Real.log 2 + 1) ≤ 1.9 := by
  have hψ := real_digamma_monotone (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 1 / 2 ≤ 2 - β)
  rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by norm_num, real_digamma_half] at hψ
  have hl := Real.log_le_log (by positivity : 0 < 1 + β) (by linarith : 1 + β ≤ 3)
  have hi : 1 / 5 ≤ 1 / (2 * (1 + β)) := (le_div_iff₀ (by positivity : 0 < 2 * (1 + β))).mpr (by linarith)
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ Real.pi_pos).mpr
  linarith [Real.pi_gt_d2, Real.eulerMascheroniConstant_lt_two_thirds, log_three_le_eleven_tenths, log_two_le_seven_tenths]

/-- The curvature margin absorbs the finite cutoff cost and the short-width logarithm. -/
theorem stationary_one_cutoff_absorb {ℓ w : ℝ} (hℓ : 0 < ℓ) (hℓw : ℓ ≤ w) (hw : 1 / 2 ≤ w) (hw2 : w ≤ 2) :
    1.5995 / Real.sqrt ℓ + 0.6715 / Real.sqrt ℓ + 2 / Real.pi + 3 / 2 ≤
      2.686 / Real.sqrt ℓ + 2 / Real.pi * Real.log w + 5 / 2 := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hw
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub] at hlog
  have hl : -(7 / 10 : ℝ) ≤ Real.log w := by linarith [log_two_le_seven_tenths]
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 / Real.pi)
  have hp : (2 / Real.pi : ℝ) ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_three.le
  have hs : Real.sqrt ℓ ≤ 2 := by nlinarith [Real.sq_sqrt hℓ.le, Real.sqrt_nonneg ℓ]
  have hi : 1 / 2 ≤ 1 / Real.sqrt ℓ := (le_div_iff₀ (Real.sqrt_pos.mpr hℓ)).mpr (by linarith)
  norm_num only [div_eq_mul_inv] at hm hp hi ⊢
  nlinarith

set_option maxHeartbeats 800000 in
/-- Every gap is covered by the literal B-process error for an arbitrary phase with one stationary frequency. -/
theorem exists_b_process_printed_one {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hone : ⌊deriv f a⌋₊ = 1)
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
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
  have hβp : 0 < deriv f a := hαpos.trans_le (hanti.antitoneOn haa hbb hab.le)
  have hβ2 : deriv f a < 2 := by have h := Nat.lt_floor_add_one (deriv f a); rw [hone] at h; norm_num at h; exact h
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hcc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) := fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  have hr := constant_weight_partIRegularity hab hf hfc
    (fun u hu => hαpos.trans_le (hanti.antitoneOn hu hbb hu.2)) hanti.antitoneOn
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hlen := half_integer_length_ge_one hab hah hbh
  have hdrop := stationary_derivative_drop hf' hcurv haa hbb hab.le
  have hw : ℓ ≤ deriv f a - deriv f b := by nlinarith
  have hh₂ : 0 ≤ h₂ := by have h := (hlower a haa).trans (hupper a haa); nlinarith
  have hκ : 0 ≤ h₂ * ℓ := mul_nonneg hh₂ hℓ.le
  have hrem := printed_half_one_lower hαpos hα hβp hβ2 hκ
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
  refine ⟨ξ, hξ, ?_⟩
  let S := ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  let P := ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
    Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
      (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)
  let NL := (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a)
  let R := (deriv f b * halfSecondEndpointBound 1 (deriv f b) + deriv f a * halfSecondEndpointBound 1 (deriv f a)) / (2 * Real.pi) +
    (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
    (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
    1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)
  change ‖S - P‖ ≤ _
  rw [hone]
  change ‖S - P‖ ≤ 2.686 / Real.sqrt ℓ + NL + 2 / Real.pi * Real.log (deriv f a - deriv f b) + R
  change 5 / 2 ≤ R at hrem
  by_cases hβh : deriv f a ≤ 3 / 2
  · have hs0 := stationary_full_sum_one_budget ξ hab hℓ hαpos.le hlen hone hξ hf hf' hf'' hanti hlower hupper hD
    change ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, I ν) - P‖ + 2 / 3 ≤ 2.686 / Real.sqrt ℓ + NL + _ + 1.251 at hs0
    rw [hone] at hs0
    have hs := le_sub_iff_add_le.mpr hs0
    have hp := constant_partI_cutoff (M := 1) hr (by norm_num) (by norm_num; linarith : deriv f a < (1 : ℕ) + 1) hah hbh
    have hbnd := poisson_cutoff_one_half hβp hβh
    norm_num only [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num, div_one, show (2 : ℝ) * 2 = 4 by norm_num] at hp hbnd
    have hp' : ‖S - ∑ ν ∈ Finset.Icc 0 1, I ν‖ ≤ 19 / 10 := hp.trans hbnd
    have ht := (norm_add_le _ _).trans (add_le_add hp' hs)
    simp only [sub_add_sub_cancel] at ht
    linarith only [ht, hrem]
  · have hx := hξ 1 (by simp [hone])
    simp only [Nat.cast_one] at hx
    have hs0 := stationary_one_left_far hab hℓ hαpos.le hα (by linarith : 3 / 2 ≤ deriv f a)
      hx.1 hx.2 hf hf' hf'' hanti hlower hupper hD
    have hPeq : P = Complex.exp (2 * Real.pi * Complex.I * ((f (ξ 1) - ξ 1 - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) (ξ 1)| : ℂ) := by
      simp only [P, hone, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_mul]
    have hs : ‖(∑ ν ∈ Finset.Icc 0 1, I ν) - P‖ ≤ 1.5995 / Real.sqrt ℓ + NL + 2 / Real.pi := by
      rw [hPeq]
      exact hs0
    have hI2 : ‖I 2‖ ≤ 0.6715 / Real.sqrt ℓ := by
      have h := kershner_monotone_bound hab.le hℓ hf hf' hcc hcurv 2
        (Or.inr (fun u hu => (hanti.antitoneOn haa hu hu.1).trans hβ2.le))
      simpa only [I, Nat.cast_ofNat] using h
    have hp := constant_partI_cutoff (M := 2) hr (by norm_num) (by norm_num; linarith : deriv f a < (2 : ℕ) + 1) hah hbh
    have hbnd := poisson_cutoff_two_small hβp hβ2
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℝ) * 3 = 6 by norm_num] at hp hbnd
    have hp' : ‖S - ∑ ν ∈ Finset.Icc 0 2, I ν‖ ≤ 3 / 2 := hp.trans hbnd
    have hmid : ‖(∑ ν ∈ Finset.Icc 0 2, I ν) - P‖ ≤
        (1.5995 / Real.sqrt ℓ + NL + 2 / Real.pi) + 0.6715 / Real.sqrt ℓ := by
      change ‖(∑ ν ∈ Finset.Icc 0 (1 + 1), I ν) - P‖ ≤ _
      rw [Finset.sum_Icc_succ_top (by norm_num), add_sub_right_comm]
      exact (norm_add_le _ _).trans (add_le_add hs hI2)
    have ht := (norm_add_le _ _).trans (add_le_add hp' hmid)
    simp only [sub_add_sub_cancel] at ht
    have hbudget := stationary_one_cutoff_absorb hℓ hw (by linarith : 1 / 2 ≤ deriv f a - deriv f b)
      (by linarith : deriv f a - deriv f b ≤ 2)
    linarith only [ht, hbudget, hrem]

/-- The literal general-phase B-process is proved throughout the full upper-derivative range below two. -/
theorem exists_b_process_printed_small {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hβsmall : deriv f a < 2)
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
  have hβp : 0 < deriv f a := hαpos.trans_le (hanti.antitoneOn (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab.le)
  by_cases hz : ⌊deriv f a⌋₊ = 0
  · have hfc : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
    refine ⟨ξ, hξ, ?_⟩
    have h := b_process_printed_zero hab hℓ hαpos hz hah hbh hf hf' hf'' hanti hlower hupper hD
    simpa only [hz, Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty, sub_zero] using h
  · have hcast : (⌊deriv f a⌋₊ : ℝ) < 2 := (Nat.floor_le hβp.le).trans_lt hβsmall
    have hn : ⌊deriv f a⌋₊ < 2 := by exact_mod_cast hcast
    exact exists_b_process_printed_one hab hℓ hαpos hα (by omega) hah hbh hf hf' hf'' hanti hlower hupper hD

/-- The source third-derivative factorization is retained in the literal small-frequency corollary. -/
theorem exists_source_b_process_small {f : ℝ → ℝ} {a b ℓ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hβsmall : deriv f a < 2)
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
  obtain ⟨ξ, hξ, h⟩ := exists_b_process_printed_small hab hℓ hαpos hα hβsmall hah hbh hf hf' hf'' hanti hlower hupper hD
  refine ⟨ξ, hξ, ?_⟩
  apply h.trans_eq
  rw [Real.mul_rpow hh₃ hℓ₃]
  ring

end DhimanKadiriQuesadaHerrera2026
