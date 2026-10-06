import DhimanKadiriQuesadaHerrera2026.CubicPoisson
import DhimanKadiriQuesadaHerrera2026.CubicPositive
import DhimanKadiriQuesadaHerrera2026.TightStationary
import DhimanKadiriQuesadaHerrera2026.ExteriorPhase

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory

set_option maxHeartbeats 800000 in
/-- Actual half-integer Poisson summation with cubic tails, using only the source curvature and third-derivative bounds. -/
theorem constant_poisson_cubic_split {f : ℝ → ℝ} {a b κ D : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hkneg : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ 0)
    (hkb : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ κ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D)
    (hM : 1 ≤ M) (hδ : 1 / 2 ≤ (M : ℝ) + 1 - deriv f a)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, exp (2 * Real.pi * I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        exp (2 * Real.pi * I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / (M : ℝ)) / Real.pi + 1 / 2 + 3 / (2 * Real.pi) +
      (2 * κ + D * (b - a)) / (4 * Real.pi ^ 2) *
        ((∑' n : ℕ, 1 / ((n : ℝ) + ((M : ℝ) + 1 - deriv f a)) ^ 3) +
          ∑' n : ℕ, 1 / ((n : ℝ) + (2 + deriv f b)) ^ 3) := by
  have ha := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  have hb := h.f_deriv_pos b (Set.right_mem_Icc.mpr h.lt.le)
  have hba := h.f_deriv_antitone (Set.left_mem_Icc.mpr h.lt.le) (Set.right_mem_Icc.mpr h.lt.le) h.lt.le
  have hδb : 1 / 2 ≤ (M : ℝ) + 1 - deriv f b := by linarith
  have hmpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hn := negative_tail_cubic h hf' hf'' hkneg hkb hD (by linarith : deriv f a < (M : ℝ) + 1)
  have hp := positive_tail_cubic_split h hf' hf'' hkneg hkb hD hah hbh
  have hea := norm_poissonHeadBoundary_half_integer_le (f := f) (g := fun _ => 1) hah (by norm_num) hmpos
  have heb := norm_poissonHeadBoundary_half_integer_le (f := f) (g := fun _ => 1) hbh (by norm_num) hmpos
  simp only [Nat.floor_natCast] at hea heb
  have hea' : deriv f a / (2 * Real.pi) * ‖negativeTail M a (deriv f a)‖ ≤ 1 / 4 := by
    obtain ⟨k, hk⟩ := hah
    have hh := mul_le_mul_of_nonneg_left (show ‖negativeTail M a (deriv f a)‖ ≤ (Real.pi / 2) / deriv f a by simpa only [← hk] using norm_negativeTail_half_integer_sharp k ha hδ)
      (div_nonneg ha.le Real.two_pi_pos.le)
    convert hh using 1
    field_simp
    norm_num
  have heb' : deriv f b / (2 * Real.pi) * ‖negativeTail M b (deriv f b)‖ ≤ 1 / 4 := by
    obtain ⟨k, hk⟩ := hbh
    have hh := mul_le_mul_of_nonneg_left (show ‖negativeTail M b (deriv f b)‖ ≤ (Real.pi / 2) / deriv f b by simpa only [← hk] using norm_negativeTail_half_integer_sharp k hb hδb)
      (div_nonneg hb.le Real.two_pi_pos.le)
    convert hh using 1
    field_simp
    norm_num
  have hzero : poissonBoundary f (fun _ => 1) a b = 0 := by
    obtain ⟨k, rfl⟩ := hah
    obtain ⟨l, rfl⟩ := hbh
    exact poissonBoundary_half_integer f (fun _ => 1) k l
  have htri (A B T P : ℂ) : ‖A - B + T - P‖ ≤ ‖A‖ + ‖B‖ + ‖T‖ + ‖P‖ := by
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  have ht := htri (poissonHeadBoundary f (fun _ => 1) b M) (poissonHeadBoundary f (fun _ => 1) a M)
    (∑' n : ℕ, negativeCoefficient f (fun _ => 1) a b (n + M + 1))
    (∑' n : ℕ, positiveCoefficient f (fun _ => 1) a b n)
  rw [← add_zero (_ - _ + _ - _), ← hzero, ← weighted_sum_eq_poissonMain_add_remainder h,
    poissonMain_eq_source] at ht
  simp only [weightedWave, Complex.ofReal_one, one_mul] at ht
  apply ht.trans
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hea heb hea' heb' hn hp ⊢
  nlinarith only [hea, heb, hea', heb', hn, hp, mul_inv_cancel₀ Real.pi_ne_zero]

set_option maxHeartbeats 800000 in
/-- The full enlarged stationary sum has a uniform half-gap loss and coefficient 1.94, for all source gaps. -/
theorem stationary_sum_next_hybrid {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 (⌊deriv f a⌋₊ + 1), ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        (1.94 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
        1 / Real.pi +
        1 / (2 * Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a)) := by
  let M := ⌊deriv f a⌋₊
  let r := ((3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hMn : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a (Set.left_mem_Icc.mpr hab.le))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hL : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hh₂ : 0 ≤ h₂ := by
    have hlo := hlower a (Set.left_mem_Icc.mpr hab.le)
    have hup := hupper a (Set.left_mem_Icc.mpr hab.le)
    nlinarith
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  let P := ∑ ν ∈ Finset.Icc 1 M,
    Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
      (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)
  change ‖(∑ ν ∈ Finset.Icc 0 (M + 1), I ν) - P‖ ≤ _
  rw [Finset.sum_Icc_succ_top (by omega), add_sub_right_comm]
  by_cases hδ : (M : ℝ) + 1 - deriv f a ≤ 1 / 2
  · have hs := stationary_full_sum_counted_tight ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hD
    have he := exterior_integral_half_recip hℓ hab.le (Nat.lt_floor_add_one (deriv f a)) hf hf' hf'' hcurv hD
    have hcap : stationaryEndpointCap ℓ (deriv f b - ((M : ℝ) + 1)) ≤ 1 / Real.pi := by
      have hn : deriv f b - ((M : ℝ) + 1) < 0 := by linarith
      apply (stationaryEndpointCap_le_recip ℓ hn.ne).trans
      rw [abs_of_neg hn]
      exact one_div_le_one_div_of_le Real.pi_pos (by nlinarith [Real.pi_pos])
    have hcount : 1.89 * ((M - 1 : ℕ) : ℝ) + 1 ≤ 1.94 * (deriv f a - deriv f b) := by
      rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
      linarith
    have hw := derivative_range_le_curvature hab.le hf' hupper
    have hscale : (1.89 * ((M - 1 : ℕ) : ℝ) + 1) * r ≤
        (1.94 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) := by
      apply (mul_le_mul_of_nonneg_right (hcount.trans (mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 1.94))) hr).trans_eq
      dsimp [r]
      field_simp
    have he' : ‖I (M + 1)‖ ≤ r + 1 / Real.pi +
        1 / (2 * Real.pi * ((M : ℝ) + 1 - deriv f a)) := by
      have ht := he.trans (add_le_add (add_le_add le_rfl hcap) le_rfl)
      convert ht using 1
      · simp only [I, M, Nat.cast_add, Nat.cast_one]
      · dsimp [r]
        ring
    have ht := (norm_add_le ((∑ ν ∈ Finset.Icc 0 M, I ν) - P) (I (M + 1))).trans (add_le_add hs he')
    apply ht.trans
    dsimp only [M, r] at hscale ⊢
    norm_num only [div_eq_mul_inv] at hscale ⊢
    nlinarith only [hscale]
  · have hs := stationary_full_sum_sharp_tight ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hupper hD
    have hfc : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
    have he := norm_shifted_integral_negative hab.le hf hfc hanti.antitoneOn (Nat.lt_floor_add_one (deriv f a))
    have he' : ‖I (M + 1)‖ ≤ 1 / Real.pi + 1 / (2 * Real.pi * ((M : ℝ) + 1 - deriv f a)) := by
      have hrp : 1 / (2 * Real.pi * ((M : ℝ) + 1 - deriv f a)) ≤ 1 / Real.pi :=
        one_div_le_one_div_of_le Real.pi_pos (by nlinarith [Real.pi_pos])
      have hi : ‖I (M + 1)‖ ≤ 1 / (Real.pi * ((M : ℝ) + 1 - deriv f a)) := by
        simpa only [I, M, Nat.cast_add, Nat.cast_one] using he
      have hid : 1 / (Real.pi * ((M : ℝ) + 1 - deriv f a)) =
          2 * (1 / (2 * Real.pi * ((M : ℝ) + 1 - deriv f a))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [hid] at hi
      linarith
    have ht := (norm_add_le ((∑ ν ∈ Finset.Icc 0 M, I ν) - P) (I (M + 1))).trans (add_le_add hs he')
    apply ht.trans
    have hnon : 0 ≤ ((3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) := by positivity
    dsimp only [M]
    norm_num only [div_eq_mul_inv] at hnon ⊢
    nlinarith only [hnon]

end DhimanKadiriQuesadaHerrera2026
