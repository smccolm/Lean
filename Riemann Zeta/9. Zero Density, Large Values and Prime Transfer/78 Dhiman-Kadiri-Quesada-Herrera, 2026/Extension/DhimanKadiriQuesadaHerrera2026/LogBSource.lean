import DhimanKadiriQuesadaHerrera2026.LogBProcess
import DhimanKadiriQuesadaHerrera2026.StationarySharpSum

namespace DhimanKadiriQuesadaHerrera2026

/-- The unused harmonic margin absorbs the printed finite-head and E₁ discrepancies when the endpoint curvature is at most twice the upper derivative. -/
theorem printed_poisson_gap_absorb {β κ : ℝ} (hβ : 2 ≤ β) (hκ : 0 ≤ κ) (hκβ : κ ≤ 2 * β) :
    2 / Real.pi + (Real.log 2 + 1 / β) / (2 * Real.pi) +
      κ / (2 * Real.pi ^ 2) * (partIISquareTailEnvelope β / β - printedPartIIE1 β / β) ≤ 1.251 := by
  have hβp : 0 < β := by linarith
  have hp := Real.pi_gt_three
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hinv : 1 / β ≤ (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hβ
  have hhead : (Real.log 2 + 1 / β) / (2 * Real.pi) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    linarith
  let L := Real.log (β + 1) + Real.eulerMascheroniConstant - (1 + 2 * β) / (2 * (1 + β))
  have hL : L ≤ (5 / 4) * β := by
    have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < β + 1)
    have hg := Real.eulerMascheroniConstant_lt_two_thirds
    have hq : (1 / 2 : ℝ) ≤ (1 + 2 * β) / (2 * (1 + β)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (1 + β))).mpr
      linarith
    dsimp [L]
    linarith
  have hLd : L / β ≤ 5 / 4 := (div_le_iff₀ hβp).mpr (by linarith)
  have hκd : κ / β ≤ 2 := (div_le_iff₀ hβp).mpr hκβ
  have hprod : (κ / β) * (L / β) ≤ 5 / 2 := by
    calc
      _ ≤ (κ / β) * (5 / 4) := mul_le_mul_of_nonneg_left hLd (div_nonneg hκ hβp.le)
      _ ≤ 2 * (5 / 4) := mul_le_mul_of_nonneg_right hκd (by norm_num)
      _ = _ := by norm_num
  have hpi2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have hgap : (κ / β) * (L / β) / Real.pi ^ 2 ≤ 5 / 18 := by
    apply (div_le_div_of_nonneg_right hprod (sq_nonneg Real.pi)).trans
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 5 / 2) (by norm_num : (0 : ℝ) < 9) hpi2
    norm_num at h
    exact h
  have he : κ / (2 * Real.pi ^ 2) * (partIISquareTailEnvelope β / β - printedPartIIE1 β / β) =
      (κ / β) * (L / β) / Real.pi ^ 2 := by
    rw [← sub_div, partIISquareTailEnvelope_sub_printed]
    dsimp [L]
    ring
  rw [he]
  have hpi : 2 / Real.pi ≤ (2 / 3 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  linarith

/-- On the explicit many-frequency half-offset subdomain, the logarithmic phase satisfies the smaller literal B-process error, with its printed E₁ and all printed constants. -/
theorem logarithmic_b_process_printed {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hα : c / b < 1) (hβ : 2 ≤ c / a)
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
  have hb := ha.trans hab
  have hup (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hscl := afePhase_b_process_scales hc ha hab.le
  have hr := afePhase_constant_secondOrderRegularity hc ha hab
  have hβeq := (afePhase_hasDerivAt c ha).deriv
  have hγ := (afePhase_hasDerivAt c hb).deriv
  have hanti := (afePhase_strictAnti hc).mono (fun u (hu : u ∈ Set.Icc a b) => hup u hu)
  have hα' : deriv (afePhase c) b < 1 := by rw [hγ]; exact hα
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hr.f_deriv_continuous hanti hα'
  have hs := stationary_full_sum_sharp (D := 2 * c / a ^ 3) (ℓ := c / b ^ 2)
    (h₂ := b ^ 2 / a ^ 2) ξ hab (by positivity)
    (by rw [hγ]; positivity) hα' (by rw [hβeq]; exact Nat.le_floor hβ) hξ
    hr.f_differentiable hr.f_deriv_differentiable
    (fun u hu => (afePhase_second_hasDerivAt c (hup u hu)).differentiableAt)
    hanti hscl.1 hscl.2.1 hscl.2.2
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
  have hgap := printed_poisson_gap_absorb hβ (by positivity : 0 ≤ c / a ^ 2) hκβ
  have hconst : 2.5275 / Real.sqrt (c / b ^ 2) ≤ 2.686 / Real.sqrt (c / b ^ 2) :=
    div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
  apply ht.trans
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hgap hconst ⊢
  nlinarith only [hgap, hconst]

end DhimanKadiriQuesadaHerrera2026
