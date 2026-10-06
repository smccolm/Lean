import DhimanKadiriQuesadaHerrera2026.CubicBudget
import DhimanKadiriQuesadaHerrera2026.CubicHybrid

namespace DhimanKadiriQuesadaHerrera2026

/-- A rational root comparison on the larger bounded-third-derivative interval. -/
theorem third_root_four_budget {D : ℝ} (hD : 0 ≤ D) (hD4 : D ≤ 4) :
    D ≤ (13 / 5 : ℝ) * D ^ (1 / 3 : ℝ) := by
  let r := D ^ (1 / 3 : ℝ)
  have hr : 0 ≤ r := Real.rpow_nonneg hD _
  have hr3 : r ^ 3 = D := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD]
    norm_num
  have hrmax : r ≤ 8 / 5 := by
    by_contra hn
    have hfactor := mul_nonneg (by linarith : 0 ≤ r - 8 / 5)
      (by positivity : 0 ≤ r ^ 2 + r * (8 / 5) + (8 / 5 : ℝ) ^ 2)
    nlinarith
  have hr2 : r ^ 2 ≤ 64 / 25 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hr2 hr
  change D ≤ (13 / 5 : ℝ) * r
  nlinarith

/-- Keeping the first upper cubic term improves the uniform two-tail constant to three halves. -/
theorem cubic_series_uniform_sharp {α d : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d) :
    (∑' n : ℕ, 1 / ((n : ℝ) + (d + 1)) ^ 3) +
      (∑' n : ℕ, 1 / ((n : ℝ) + (2 + α)) ^ 3) ≤ 3 / 2 := by
  have hs := (reciprocal_cube_series_bounds (by positivity : 0 < d + 1)).1
  have hs1 := (reciprocal_cube_series_bounds (by norm_num : (0 : ℝ) < 1)).1
  have hh := hs.tsum_le_tsum (fun n : ℕ => one_div_le_one_div_of_le
    (pow_pos (by positivity : 0 < (n : ℝ) + 1) 3)
    (pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) + 1) (by linarith : (n : ℝ) + 1 ≤ (n : ℝ) + (d + 1)) 3)) hs1
  have ht := (reciprocal_cube_series_sharp (by norm_num : (0 : ℝ) < 1)).2
  norm_num at ht
  have hp := cubic_series_two_le hα
  simp only [one_div] at hh hp ⊢
  linarith

/-- Above gap nine twentieths the same two tails have a smaller uniform rational bound. -/
theorem cubic_series_gap_nine_twentieths {α d : ℝ} (hα : 0 ≤ α) (hd : 9 / 20 ≤ d) :
    (∑' n : ℕ, 1 / ((n : ℝ) + (d + 1)) ^ 3) +
      (∑' n : ℕ, 1 / ((n : ℝ) + (2 + α)) ^ 3) ≤ 102 / 125 := by
  have hs := reciprocal_cube_series_bounds (by linarith : 0 < d + 1)
  have hb3 : 1 / (d + 1) ^ 3 ≤ 1 / (29 / 20 : ℝ) ^ 3 :=
    one_div_le_one_div_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 29 / 20) (by linarith) 3)
  have hb2 : 1 / (2 * (d + 1) ^ 2) ≤ 1 / (2 * (29 / 20 : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by norm_num) (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 29 / 20) (by linarith : 29 / 20 ≤ d + 1) 2) (by norm_num))
  have hp := cubic_series_two_le hα
  norm_num at hb3 hb2
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hs hp ⊢
  linarith [hs.2.2]

/-- The complete length error for D≤4 fits the nonlinear allowance on the smaller gap range. -/
theorem cubic_four_length_small_gap {D L h₂ S : ℝ} (hD : 0 ≤ D) (hD4 : D ≤ 4)
    (hL : 0 ≤ L) (hh₂ : 1 ≤ h₂) (hS : S ≤ 3 / 2) :
    D * L / (4 * Real.pi ^ 2) * S ≤
      (0.11 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * L := by
  have hroot := third_root_four_budget hD hD4
  have hratio : (9 / 10 : ℝ) ≤ (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ) := by
    have hp : 3 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_d2])
    have hr := Real.self_le_rpow_of_le_one (by positivity : 0 ≤ 3 / Real.pi) hp (by norm_num : (2 / 3 : ℝ) ≤ 1)
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3) Real.pi_pos.le] at hr
    have ht : (9 / 10 : ℝ) ≤ 3 / Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_d2])
    exact ht.trans hr
  have hpi : (197 / 20 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
  have hc : 1 / (4 * Real.pi ^ 2) ≤ 5 / 197 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * Real.pi ^ 2) (by norm_num : (0 : ℝ) < 197)).mpr
    linarith
  have hleft := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ D * L / (4 * Real.pi ^ 2))
  have hleft' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ D * L * (3 / 2 : ℝ))
  have hright := mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ 0.11 * h₂ * D ^ (1 / 3 : ℝ) * L)
  have hrootL := mul_le_mul_of_nonneg_right hroot hL
  have hhL := mul_le_mul_of_nonneg_right hh₂ (by positivity : 0 ≤ D ^ (1 / 3 : ℝ) * L)
  norm_num only [div_eq_mul_inv] at hleft hleft' hright ⊢
  nlinarith only [hleft, hleft', hright, hrootL, hhL, mul_nonneg hD hL]

/-- The smaller far-tail constant covers D≤4 on the complementary gap range. -/
theorem cubic_four_length_large_gap {D L h₂ S : ℝ} (hD : 0 ≤ D) (hD4 : D ≤ 4)
    (hL : 0 ≤ L) (hh₂ : 1 ≤ h₂) (hS : S ≤ 102 / 125) :
    D * L / (4 * Real.pi ^ 2) * S ≤
      (0.06 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * L := by
  have hroot := third_root_four_budget hD hD4
  have hratio : (9 / 10 : ℝ) ≤ (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ) := by
    have hp : 3 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_d2])
    have hr := Real.self_le_rpow_of_le_one (by positivity : 0 ≤ 3 / Real.pi) hp (by norm_num : (2 / 3 : ℝ) ≤ 1)
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 3) Real.pi_pos.le] at hr
    have ht : (9 / 10 : ℝ) ≤ 3 / Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_d2])
    exact ht.trans hr
  have hpi : (197 / 20 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
  have hc : 1 / (4 * Real.pi ^ 2) ≤ 5 / 197 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * Real.pi ^ 2) (by norm_num : (0 : ℝ) < 197)).mpr
    linarith
  have hleft := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ D * L / (4 * Real.pi ^ 2))
  have hleft' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ D * L * (102 / 125 : ℝ))
  have hright := mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ 0.06 * h₂ * D ^ (1 / 3 : ℝ) * L)
  have hrootL := mul_le_mul_of_nonneg_right hroot hL
  have hhL := mul_le_mul_of_nonneg_right hh₂ (by positivity : 0 ≤ D ^ (1 / 3 : ℝ) * L)
  norm_num only [div_eq_mul_inv] at hleft hleft' hright ⊢
  nlinarith only [hleft, hleft', hright, hrootL, hhL, mul_nonneg hD hL]

set_option maxHeartbeats 800000 in
/-- The smaller endpoint gap preserves the full 1.89 nonlinear coefficient in the enlarged Fourier sum. -/
theorem stationary_sum_next_small_gap {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊) (hδ : (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a ≤ 9 / 20)
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
        (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
        1 / Real.pi +
        1 / (2 * Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a)) := by
  let M := ⌊deriv f a⌋₊
  let r := ((3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hMn : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a (Set.left_mem_Icc.mpr hab.le))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  let P := ∑ ν ∈ Finset.Icc 1 M,
    Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
      (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)
  change ‖(∑ ν ∈ Finset.Icc 0 (M + 1), I ν) - P‖ ≤ _
  rw [Finset.sum_Icc_succ_top (by omega), add_sub_right_comm]
  change (M : ℝ) + 1 - deriv f a ≤ 9 / 20 at hδ
  have hs := stationary_full_sum_counted_tight ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hD
  have he := exterior_integral_half_recip hℓ hab.le (Nat.lt_floor_add_one (deriv f a)) hf hf' hf'' hcurv hD
  have hcap : stationaryEndpointCap ℓ (deriv f b - ((M : ℝ) + 1)) ≤ 1 / Real.pi := by
    have hn : deriv f b - ((M : ℝ) + 1) < 0 := by linarith
    apply (stationaryEndpointCap_le_recip ℓ hn.ne).trans
    rw [abs_of_neg hn]
    exact one_div_le_one_div_of_le Real.pi_pos (by nlinarith [Real.pi_pos])
  have hcount : 1.89 * ((M - 1 : ℕ) : ℝ) + 1 ≤ 1.89 * (deriv f a - deriv f b) := by
    rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
    linarith
  have hw := derivative_range_le_curvature hab.le hf' hupper
  have hscale : (1.89 * ((M - 1 : ℕ) : ℝ) + 1) * r ≤
      (1.89 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) := by
    apply (mul_le_mul_of_nonneg_right (hcount.trans (mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 1.89))) hr).trans_eq
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


set_option maxHeartbeats 800000 in
/-- The literal many-frequency B-process holds for arbitrary source phases with third-derivative bound at most four. -/
theorem exists_b_process_cubic_four_D {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊) (hD4 : D ≤ 4)
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
  have hbb := Set.right_mem_Icc.mpr hab.le
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a haa)
  have hκ : ℓ ≤ h₂ * ℓ := (hlower a haa).trans (hupper a haa)
  have hh₂ : 1 ≤ h₂ := by nlinarith
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hr := constant_weight_partIRegularity hab hf hfc
    (fun u hu => hαpos.trans_le (hanti.antitoneOn hu hbb hu.2)) hanti.antitoneOn
  have hβp := hr.f_deriv_pos a haa
  have hβ : 2 ≤ deriv f a := by
    have hh : (2 : ℝ) ≤ (⌊deriv f a⌋₊ : ℝ) := by exact_mod_cast hM
    exact hh.trans (Nat.floor_le hβp.le)
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
  have hgap : (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a + 1 = (⌊deriv f a⌋₊ : ℝ) + 2 - deriv f a := by ring
  have hn : (⌊deriv f a⌋₊ : ℝ) + 1 + 1 = (⌊deriv f a⌋₊ : ℝ) + 2 := by ring
  have hδ : 0 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a := by linarith [Nat.lt_floor_add_one (deriv f a)]
  have hp := constant_poisson_cubic_split (M := ⌊deriv f a⌋₊ + 1) hr hf' hf''
    (fun u hu => (hcurv u hu).trans (by linarith)) hupper hD (by omega)
    (by push_cast; linarith [Nat.lt_floor_add_one (deriv f a)] : 1 / 2 ≤ ((⌊deriv f a⌋₊ + 1 : ℕ) : ℝ) + 1 - deriv f a) hah hbh
  simp only [Nat.cast_add, Nat.cast_one, hn] at hp
  have hcb := cubic_curvature_gap_budget hαpos.le hβ hℓ hκ
  dsimp only at hcb
  rw [hgap] at hcb
  have hconst := cubic_constant_budget hαpos hα.le hβp ⌊deriv f a⌋₊
  refine ⟨ξ, hξ, ?_⟩
  by_cases hδsmall : (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a ≤ 9 / 20
  · have hs := stationary_sum_next_small_gap ξ hab hℓ hαpos.le hα hM hδsmall hξ hf hf' hf'' hanti hlower hupper hD
    have hS := cubic_series_uniform_sharp hαpos.le hδ
    rw [hgap] at hS
    have hlen := cubic_four_length_small_gap hDn hD4 (sub_nonneg.mpr hab.le) hh₂ hS
    have ht := (norm_add_le _ _).trans (add_le_add hp hs)
    simp only [sub_add_sub_cancel] at ht
    apply ht.trans
    norm_num only [div_eq_mul_inv, mul_inv_rev] at hcb hlen hconst ⊢
    nlinarith only [hcb, hlen, hconst]
  · have hs := stationary_sum_next_hybrid ξ hab hℓ hαpos.le hα hM hξ hf hf' hf'' hanti hlower hupper hD
    have hS := cubic_series_gap_nine_twentieths hαpos.le (le_of_not_ge hδsmall)
    rw [hgap] at hS
    have hlen := cubic_four_length_large_gap hDn hD4 (sub_nonneg.mpr hab.le) hh₂ hS
    have ht := (norm_add_le _ _).trans (add_le_add hp hs)
    simp only [sub_add_sub_cancel] at ht
    apply ht.trans
    norm_num only [div_eq_mul_inv, mul_inv_rev] at hcb hlen hconst ⊢
    nlinarith only [hcb, hlen, hconst]

/-- The literal B-process for every frequency count when the third-derivative bound is at most four. -/
theorem exists_b_process_four_D {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hD4 : D ≤ 4)
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
  by_cases hsmall : deriv f a < 2
  · exact exists_b_process_printed_small hab hℓ hαpos hα hsmall hah hbh hf hf' hf'' hanti hlower hupper hD
  · have hM : 2 ≤ ⌊deriv f a⌋₊ := Nat.le_floor (show (2 : ℝ) ≤ deriv f a from le_of_not_gt hsmall)
    exact exists_b_process_cubic_four_D hab hℓ hαpos hα hM hD4 hah hbh hf hf' hf'' hanti hlower hupper hD

/-- The source third-derivative scales are retained in the full bounded-third-derivative corollary. -/
theorem exists_source_b_process_four_D {f : ℝ → ℝ} {a b ℓ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hD4 : h₃ * ℓ₃ ≤ 4)
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
  obtain ⟨ξ, hξ, h⟩ := exists_b_process_four_D hab hℓ hαpos hα hD4 hah hbh hf hf' hf'' hanti hlower hupper hD
  refine ⟨ξ, hξ, ?_⟩
  apply h.trans_eq
  rw [Real.mul_rpow hh₃ hℓ₃]
  ring

end DhimanKadiriQuesadaHerrera2026
