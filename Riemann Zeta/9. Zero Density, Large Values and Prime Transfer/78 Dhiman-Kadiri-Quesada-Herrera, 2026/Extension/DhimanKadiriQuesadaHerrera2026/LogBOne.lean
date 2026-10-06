import DhimanKadiriQuesadaHerrera2026.LogBSource
import DhimanKadiriQuesadaHerrera2026.AFECoarseConstants

namespace DhimanKadiriQuesadaHerrera2026

/-- The printed Poisson discrepancies have a uniform two-thirds budget above derivative one. -/
theorem printed_poisson_gap_one {β κ : ℝ} (hβ : 1 ≤ β) (hκ : 0 ≤ κ) (hκβ : κ ≤ 2 * β) :
    (Real.log 2 + 1 / β) / (2 * Real.pi) +
      κ / (2 * Real.pi ^ 2) * (partIISquareTailEnvelope β / β - printedPartIIE1 β / β) ≤ 2 / 3 := by
  have hβp : 0 < β := by linarith
  have hp := Real.pi_gt_three
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hinv : 1 / β ≤ (1 : ℝ) := by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hβ
  have hhead : (Real.log 2 + 1 / β) / (2 * Real.pi) ≤ 1 / 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    linarith
  let L := Real.log (β + 1) + Real.eulerMascheroniConstant - (1 + 2 * β) / (2 * (1 + β))
  have hL : L ≤ (3 / 2) * β := by
    have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < β + 1)
    have hg := Real.eulerMascheroniConstant_lt_two_thirds
    have hq : (1 / 2 : ℝ) ≤ (1 + 2 * β) / (2 * (1 + β)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (1 + β))).mpr
      linarith
    dsimp [L]
    linarith
  have hLd : L / β ≤ 3 / 2 := (div_le_iff₀ hβp).mpr (by linarith)
  have hκd : κ / β ≤ 2 := (div_le_iff₀ hβp).mpr hκβ
  have hprod : (κ / β) * (L / β) ≤ 3 := by
    calc
      _ ≤ (κ / β) * (3 / 2) := mul_le_mul_of_nonneg_left hLd (div_nonneg hκ hβp.le)
      _ ≤ 2 * (3 / 2) := mul_le_mul_of_nonneg_right hκd (by norm_num)
      _ = _ := by norm_num
  have hpi2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have hgap : (κ / β) * (L / β) / Real.pi ^ 2 ≤ 1 / 3 := by
    apply (div_le_div_of_nonneg_right hprod (sq_nonneg Real.pi)).trans
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) < 9) hpi2
    norm_num at h
    exact h
  have he : κ / (2 * Real.pi ^ 2) * (partIISquareTailEnvelope β / β - printedPartIIE1 β / β) =
      (κ / β) * (L / β) / Real.pi ^ 2 := by
    rw [← sub_div, partIISquareTailEnvelope_sub_printed]
    dsimp [L]
    ring
  rw [he]
  linarith

/-- The large-width single-frequency estimate leaves room for the full Poisson discrepancy. -/
theorem stationary_one_large_absorb {ℓ w : ℝ} (hw : 1 / 2 ≤ w) :
    2.5275 / Real.sqrt ℓ + 2 / 3 ≤ 2.686 / Real.sqrt ℓ + 2 / Real.pi * Real.log w + 1.251 := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hw
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub] at hlog
  have hl : -(7 / 10 : ℝ) ≤ Real.log w := by linarith [log_two_le_seven_tenths]
  have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 / Real.pi)
  have hp : (2 / Real.pi : ℝ) ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_three.le
  have hconst := div_le_div_of_nonneg_right (by norm_num : (2.5275 : ℝ) ≤ 2.686) (Real.sqrt_nonneg ℓ)
  nlinarith

/-- The short-width single-frequency estimate also retains the complete Poisson margin. -/
theorem stationary_one_small_absorb {ℓ w : ℝ} (hℓ : 0 < ℓ) (hℓw : ℓ ≤ w) (hw : w ≤ 1) :
    1.856 / Real.sqrt ℓ + 2 / Real.pi + 2 / 3 ≤
      2.686 / Real.sqrt ℓ + 2 / Real.pi * Real.log w + 1.251 := by
  have hwpos := hℓ.trans_le hℓw
  have hinv := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hℓ) (Real.sqrt_le_sqrt hℓw)
  have hlog := neg_inv_sqrt_le_log hwpos
  have hp : (2 / Real.pi : ℝ) ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_three.le
  have hs : Real.sqrt ℓ ≤ 1 := (Real.sqrt_le_one).mpr (hℓw.trans hw)
  have hv : (1 : ℝ) ≤ 1 / Real.sqrt ℓ := (le_div_iff₀ (Real.sqrt_pos.mpr hℓ)).mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / Real.pi)
  have hmul' := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 2 / Real.pi)
  have hprod := mul_nonneg (show 0 ≤ (0.83 : ℝ) - 2 / Real.pi by linarith) (sub_nonneg.mpr hv)
  simp only [div_eq_mul_inv] at hmul hmul' hp hprod ⊢
  nlinarith

/-- A single stationary frequency leaves a uniform two-thirds margin for the remaining Poisson terms. -/
theorem stationary_full_sum_one_budget {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b)
    (hlen : 1 ≤ b - a) (hone : ⌊deriv f a⌋₊ = 1)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ + 2 / 3 ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 := by
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hfcc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) :=
    fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  have hw : ℓ ≤ deriv f a - deriv f b := by
    have h := stationary_derivative_drop hf' hcurv haa hbb hab.le
    nlinarith
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a haa)
  have hh₂ : 0 ≤ h₂ := by
    have hh := (hlower a haa).trans (hupper a haa)
    nlinarith
  have hnonlin : 0 ≤ (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) *
      h₂ * D ^ (1 / 3 : ℝ) * (b - a) := by positivity
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  let P : ℕ → ℂ := fun ν => Complex.exp (2 * Real.pi * Complex.I *
    ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) / (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)
  have hz : ‖I 0‖ ≤ 0.6715 / Real.sqrt ℓ := by
    simpa only [I, Nat.cast_zero, zero_mul, sub_zero] using
      kershner_zero_frequency hab hℓ hf hf' hf'' hanti hαpos hlower
  change ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, I ν) -
    (∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, P ν)‖ + 2 / 3 ≤ _
  have hx := hξ 1 (by simp [hone])
  have hstation : ‖I 1 - P 1‖ ≤ 1.856 / Real.sqrt ℓ :=
    stationary_uniform_bound hℓ hx.1.1 hx.1.2 hx.2 hf hf' hfcc hcurv
  have hs : Finset.Icc 0 1 = {0, 1} := by decide
  simp only [hone, hs, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), Finset.Icc_self,
    Finset.sum_singleton]
  rw [add_sub_assoc]
  have hnorm := (norm_add_le (I 0) (I 1 - P 1)).trans (add_le_add le_rfl hstation)
  by_cases hwide : 1 / 2 ≤ deriv f a - deriv f b
  · have hwider := stationary_one_large_absorb (ℓ := ℓ) hwide
    have he : 0.6715 / Real.sqrt ℓ + 1.856 / Real.sqrt ℓ = 2.5275 / Real.sqrt ℓ := by ring
    linarith
  · have hβ : 1 ≤ deriv f a := Nat.floor_pos.mp (by omega)
    have hαhalf : 1 / 2 < deriv f b := by linarith
    have hz' : ‖I 0‖ ≤ 2 / Real.pi := by
      have h := norm_shifted_integral_positive (ν := 0) hab.le hf hfc hanti.antitoneOn
        (by linarith : 0 < deriv f b)
      simp only [sub_zero, zero_mul] at h
      have hp := one_div_le_one_div_of_le (by positivity : 0 < Real.pi * (1 / 2))
        (mul_le_mul_of_nonneg_left hαhalf.le Real.pi_pos.le)
      have he : 1 / (Real.pi * (1 / 2)) = 2 / Real.pi := by ring
      simpa only [I, Nat.cast_zero, zero_mul, sub_zero, he] using h.trans hp
    have hsmall := stationary_one_small_absorb hℓ hw (by linarith : deriv f a - deriv f b ≤ 1)
    linarith

/-- The literal B-process error also holds for the single-frequency logarithmic case when δ≥1/2. -/
theorem logarithmic_b_process_printed_one {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1) (hone : ⌊c / a⌋₊ = 1)
    (hδ : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a)
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
  have hβ : 1 ≤ c / a := Nat.floor_pos.mp (by rw [hone]; norm_num)
  have hb := ha.trans hab
  have hup (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hscl := afePhase_b_process_scales hc ha hab.le
  have hr := afePhase_constant_secondOrderRegularity hc ha hab
  have hβeq := (afePhase_hasDerivAt c ha).deriv
  have hγ := (afePhase_hasDerivAt c hb).deriv
  have hanti := (afePhase_strictAnti hc).mono (fun u (hu : u ∈ Set.Icc a b) => hup u hu)
  have hα' : deriv (afePhase c) b < 1 := by rw [hγ]; exact hα
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hr.f_deriv_continuous hanti hα'
  have hs0 := stationary_full_sum_one_budget (D := 2 * c / a ^ 3) (ℓ := c / b ^ 2)
    (h₂ := b ^ 2 / a ^ 2) ξ hab (by positivity)
    (by rw [hγ]; positivity) (half_integer_length_ge_one hab hah hbh)
    (by rw [hβeq]; exact hone) hξ hr.f_differentiable hr.f_deriv_differentiable
    (fun u hu => (afePhase_second_hasDerivAt c (hup u hu)).differentiableAt)
    hanti hscl.1 hscl.2.1 hscl.2.2
  have hs := le_sub_iff_add_le.mpr hs0
  have hp := constant_second_poisson_half hr hah hbh (by rw [hβeq]; exact hδ)
  dsimp only at hp
  have ht := (norm_add_le _ _).trans (add_le_add hp hs)
  simp only [sub_add_sub_cancel] at ht
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
  rw [hmain, (afePhase_deriv_hasDerivAt c ha).deriv, abs_div, abs_neg, abs_of_pos hc,
    abs_of_nonneg (sq_nonneg a)] at ht
  have hβp : 0 < c / a := div_pos hc ha
  rw [squareBounds_eq_proposed_envelope hβp, cubeBounds_eq_source_coefficient hβp] at ht
  have hcube : (c / a) * (c / a ^ 2) / (2 * Real.pi ^ 2) *
      (partIICubeCoefficient (c / a) / (c / a)) =
      (c / a ^ 2) * partIICubeCoefficient (c / a) / (2 * Real.pi ^ 2) := by
    field_simp
  rw [hcube] at ht
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
  have hgap := printed_poisson_gap_one hβ (by positivity : 0 ≤ c / a ^ 2) hκβ
  apply ht.trans
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hgap ⊢
  nlinarith only [hgap]

end DhimanKadiriQuesadaHerrera2026
