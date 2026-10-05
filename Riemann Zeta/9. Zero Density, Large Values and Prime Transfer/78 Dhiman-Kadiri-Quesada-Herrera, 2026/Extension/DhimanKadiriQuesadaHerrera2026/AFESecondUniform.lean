import DhimanKadiriQuesadaHerrera2026.AFESecondBounds

/-! # Uniform proof-consistent Theorem-10 branches

The full A₀, B₀ and C₀ formulas bound the actual remainder in both cutoff regions,
including both height signs and closed sigma endpoints. The formula agrees with the
source proof and ancillary code. Equation (5.2) reverses the E₀ assignments; adopting
this corrected public contract remains an explicit owner scope decision.
-/

namespace DhimanKadiriQuesadaHerrera2026

/-- The literal source A₀, retaining x₀=max(h,sqrt(t₀/(2π))) and all thirteen terms. -/
noncomputable def afeSourceA0 (σ h t₀ : ℝ) : ℝ :=
  let x₀ := max h (Real.sqrt (t₀ / (2 * Real.pi)))
  1 / 4 + (Real.eulerMascheroniConstant + (7 / 2) * Real.log 2 - 3 / 2) / Real.pi +
    115 / (27 * Real.pi ^ 2) +
    7 / (4 * Real.pi * h) + 3 / (4 * Real.pi * (h + 1)) + 7 / (8 * Real.pi * h ^ 2) +
    (23 * (σ + 1)) / (9 * Real.pi ^ 2 * x₀) + (115 * σ) / (54 * Real.pi ^ 3 * x₀ ^ 2) +
    σ / (4 * t₀) + σ / (2 * Real.pi * h ^ 2 * t₀) +
    (σ * Real.log 2) / (2 * Real.pi * t₀) + (3 * σ) / (4 * Real.pi * (h + 1) * t₀) +
    (23 * σ * (σ + 1)) / (9 * Real.pi ^ 2 * x₀ * t₀)

/-- The literal source B₀ at a positive height threshold. -/
noncomputable def afeSourceB0 (σ t₀ : ℝ) : ℝ :=
  ((1 / 2) * Real.sqrt (t₀ / (2 * Real.pi)) * Real.log (t₀ / (2 * Real.pi)) +
    (t₀ / (2 * Real.pi)) ^ ((1 - σ) / 2)) * Real.exp (-Real.pi * t₀) /
      (1 - Real.exp (-Real.pi * t₀))

/-- The larger cutoff lies above the source x₀, as a consequence of the physical scale. -/
theorem afe_large_cutoff_ge_x0 {t t₀ x y h : ℝ} (hx : 0 < x) (hyx : y ≤ x)
    (hhx : h ≤ x) (htt : t₀ ≤ t) (hscale : 2 * Real.pi * x * y = t) :
    max h (Real.sqrt (t₀ / (2 * Real.pi))) ≤ x := by
  apply max_le hhx
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hx.le, (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr ?_⟩
  have hp := mul_le_mul_of_nonneg_left hyx (show 0 ≤ 2 * Real.pi * x by positivity)
  rw [hscale] at hp
  nlinarith only [hp, htt]

/-- The A coefficient is bounded uniformly by the exact source A₀ when x is the larger cutoff. -/
theorem afeSourceA_le_A0 {σ t t₀ x y h : ℝ} (hσ : 0 ≤ σ) (ht₀ : 0 < t₀)
    (hh : 0 < h) (hx : h ≤ x) (hy : h ≤ y) (hyx : y ≤ x)
    (htt : t₀ ≤ t) (hscale : 2 * Real.pi * x * y = t) :
    afeSourceA σ t x y ≤ afeSourceA0 σ h t₀ := by
  have hxpos := hh.trans_le hx
  have hypos := hh.trans_le hy
  have htpos := ht₀.trans_le htt
  have hx0 := afe_large_cutoff_ge_x0 hxpos hyx hx htt hscale
  have hx0pos : 0 < max h (Real.sqrt (t₀ / (2 * Real.pi))) := hh.trans_le (le_max_left _ _)
  have htx : t / x ^ 2 ≤ 2 * Real.pi := by
    apply (div_le_iff₀ (sq_pos_of_pos hxpos)).mpr
    have hp := mul_le_mul_of_nonneg_left hyx (show 0 ≤ 2 * Real.pi * x by positivity)
    rw [hscale] at hp
    nlinarith only [hp]
  have hmain := mul_le_mul_of_nonneg_left htx (show 0 ≤ 115 / (54 * Real.pi ^ 3) by positivity)
  have he : (115 / (54 * Real.pi ^ 3)) * (2 * Real.pi) = 115 / (27 * Real.pi ^ 2) := by field_simp; norm_num
  rw [he] at hmain
  dsimp only [afeSourceA, afeSourceA0]
  gcongr


/-- The normalized numerator of B₀, with its exact logarithmic and power contributions. -/
noncomputable def afeBKernel (α L z : ℝ) : ℝ :=
  (Real.sqrt z / 2 * Real.log z + z ^ α) * Real.exp (-L * z)

/-- Differentiation of the complete normalized B numerator. -/
theorem afeBKernel_hasDerivAt (α L : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (afeBKernel α L)
      (((1 / (2 * Real.sqrt z) / 2 * Real.log z + Real.sqrt z / 2 * (1 / z) + α * z ^ (α - 1)) -
        L * (Real.sqrt z / 2 * Real.log z + z ^ α)) * Real.exp (-L * z)) z := by
  have hd := (((Real.hasDerivAt_sqrt hz.ne').div_const 2).mul (Real.hasDerivAt_log hz.ne')).add
    (Real.hasDerivAt_rpow_const (p := α) (Or.inl hz.ne'))
  have he := (((hasDerivAt_id z).const_mul (-L)).exp)
  convert hd.mul he using 1
  dsimp only [afeBKernel, id_eq, Pi.mul_apply, Pi.add_apply]
  ring_nf

/-- The derivative's logarithmic and power terms are dominated by the original numerator on z≥1. -/
theorem afeBKernel_deriv_nonpos {α L z : ℝ} (hα : α ∈ Set.Icc 0 (1 / 2))
    (hL : 1 ≤ L) (hz : 1 ≤ z) : deriv (afeBKernel α L) z ≤ 0 := by
  have hzpos : 0 < z := by linarith
  have hspos := Real.sqrt_pos.mpr hzpos
  have hs : 1 ≤ Real.sqrt z := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hz
  have hsq := Real.sq_sqrt hzpos.le
  have hpow := Real.one_le_rpow hz hα.1
  have hlog := Real.log_nonneg hz
  have h1a : 1 / (2 * Real.sqrt z) / 2 ≤ Real.sqrt z / 2 := by
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt z)).mpr
    nlinarith only [hsq, hz]
  have h1 := mul_le_mul_of_nonneg_right h1a hlog
  have h2a : Real.sqrt z / 2 * (1 / z) ≤ (1 / 2 : ℝ) := by
    rw [mul_one_div]
    apply (div_le_iff₀ hzpos).mpr
    nlinarith only [hsq, hs, sq_nonneg (Real.sqrt z - 1)]
  have h2 : Real.sqrt z / 2 * (1 / z) ≤ (1 / 2) * z ^ α := by linarith
  have h3a : z ^ (α - 1) ≤ z ^ α := Real.rpow_le_rpow_of_exponent_le hz (by linarith)
  have h3 : α * z ^ (α - 1) ≤ (1 / 2) * z ^ α :=
    mul_le_mul hα.2 h3a (Real.rpow_nonneg hzpos.le _) (by norm_num)
  have hφ : 0 ≤ Real.sqrt z / 2 * Real.log z + z ^ α := by positivity
  have hLφ := mul_le_mul_of_nonneg_right hL hφ
  rw [(afeBKernel_hasDerivAt α L hzpos).deriv]
  apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
  nlinarith only [h1, h2, h3, hLφ]

/-- The complete normalized B numerator decreases on the entire interval needed for t₀≥2π. -/
theorem afeBKernel_antitone {α L : ℝ} (hα : α ∈ Set.Icc 0 (1 / 2)) (hL : 1 ≤ L) :
    AntitoneOn (afeBKernel α L) (Set.Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · intro z hz
    exact (afeBKernel_hasDerivAt α L (by have := hz; change 1 ≤ z at this; linarith)).continuousAt.continuousWithinAt
  · intro z hz
    have hz' : 1 ≤ z := interior_subset hz
    exact (afeBKernel_hasDerivAt α L (by linarith)).differentiableAt.differentiableWithinAt
  · intro z hz
    exact afeBKernel_deriv_nonpos hα hL (interior_subset hz)


/-- The smaller cutoff lies below sqrt(t/(2π)) by the physical scale. -/
theorem afe_small_cutoff_le_sqrt {t x y : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hscale : 2 * Real.pi * x * y = t) : y ≤ Real.sqrt (t / (2 * Real.pi)) := by
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  have hp := mul_le_mul_of_nonneg_right hyx (show 0 ≤ 2 * Real.pi * y by positivity)
  rw [← hscale]
  nlinarith only [hp]

/-- The exponential B coefficient is uniformly bounded by the exact B₀ for the full σ interval. -/
theorem afeSourceB_le_B0 {σ t t₀ x y : ℝ} (hσ : σ ∈ Set.Icc 0 1)
    (ht₀ : 2 * Real.pi ≤ t₀) (hy : 1 ≤ y) (hyx : y ≤ x)
    (htt : t₀ ≤ t) (hscale : 2 * Real.pi * x * y = t) :
    afeSourceB σ t y t₀ ≤ afeSourceB0 σ t₀ := by
  have hp : 0 < 2 * Real.pi := by positivity
  have ht₀pos := hp.trans_le ht₀
  have htpos := ht₀pos.trans_le htt
  have hypos : 0 < y := by linarith
  have hz : 1 ≤ t / (2 * Real.pi) := (le_div_iff₀ hp).mpr (by linarith)
  have hz₀ : 1 ≤ t₀ / (2 * Real.pi) := (le_div_iff₀ hp).mpr (by linarith)
  have hzz : t₀ / (2 * Real.pi) ≤ t / (2 * Real.pi) := div_le_div_of_nonneg_right htt hp.le
  have hu : 0 < t / (2 * Real.pi) := div_pos htpos hp
  have hys := afe_small_cutoff_le_sqrt hypos hyx hscale
  have hlog := Real.log_le_log hypos hys
  rw [Real.log_sqrt hu.le] at hlog
  have hyl : y * Real.log y ≤ Real.sqrt (t / (2 * Real.pi)) / 2 * Real.log (t / (2 * Real.pi)) := by
    have hh := mul_le_mul hys hlog (Real.log_nonneg hy) (Real.sqrt_nonneg _)
    nlinarith only [hh]
  have hyp : y ^ (1 - σ) ≤ (t / (2 * Real.pi)) ^ ((1 - σ) / 2) := by
    have hh := Real.rpow_le_rpow hypos.le hys (by linarith [hσ.2] : 0 ≤ 1 - σ)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le] at hh
    convert hh using 1
    congr 1
    ring
  have hnum := mul_le_mul_of_nonneg_right (add_le_add hyl hyp) (Real.exp_pos (-Real.pi * t)).le
  have hα : (1 - σ) / 2 ∈ Set.Icc (0 : ℝ) (1 / 2) := by constructor <;> linarith [hσ.1, hσ.2]
  have hL : 1 ≤ 2 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hK := afeBKernel_antitone hα hL hz₀ hz hzz
  have he (u : ℝ) : -(2 * Real.pi ^ 2) * (u / (2 * Real.pi)) = -Real.pi * u := by
    field_simp
  dsimp only [afeBKernel] at hK
  rw [he t, he t₀] at hK
  have hden : 0 ≤ 1 - Real.exp (-Real.pi * t₀) := by
    have hh : Real.exp (-Real.pi * t₀) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  unfold afeSourceB afeSourceB0
  apply div_le_div_of_nonneg_right _ hden
  convert hnum.trans hK using 1
  ring


/-- The source A₀ coefficient is nonnegative throughout the required parameter domain. -/
theorem afeSourceA0_nonneg {σ h t₀ : ℝ} (hσ : 0 ≤ σ) (hh : 0 < h) (ht₀ : 0 < t₀) :
    0 ≤ afeSourceA0 σ h t₀ := by
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hc : 0 ≤ Real.eulerMascheroniConstant + (7 / 2) * Real.log 2 - 3 / 2 := by
    norm_num at hl
    linarith
  have hx0 : 0 < max h (Real.sqrt (t₀ / (2 * Real.pi))) := hh.trans_le (le_max_left _ _)
  dsimp only [afeSourceA0]
  positivity

/-- The source B₀ coefficient is nonnegative at every threshold t₀≥2π. -/
theorem afeSourceB0_nonneg (σ : ℝ) {t₀ : ℝ} (ht₀ : 2 * Real.pi ≤ t₀) :
    0 ≤ afeSourceB0 σ t₀ := by
  have hp : 0 < 2 * Real.pi := by positivity
  have htpos := hp.trans_le ht₀
  have hu : 1 ≤ t₀ / (2 * Real.pi) := (le_div_iff₀ hp).mpr (by linarith)
  have hlog := Real.log_nonneg hu
  have hden : 0 ≤ 1 - Real.exp (-Real.pi * t₀) := by
    have he : Real.exp (-Real.pi * t₀) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  unfold afeSourceB0
  positivity

/-- The physical-scale power equals the direct weight times an explicit square-root ratio. -/
theorem afe_scale_power_identity (σ : ℝ) {T x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hscale : 2 * Real.pi * x * y = T) :
    (T / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) =
      x ^ (-σ) * (x ^ (1 / 2 : ℝ) / y ^ (1 / 2 : ℝ)) := by
  have he : T / (2 * Real.pi) = x * y := by rw [← hscale]; field_simp
  rw [he, Real.mul_rpow hx.le hy.le, mul_assoc, ← Real.rpow_add hy,
    show 1 / 2 - σ + (σ - 1) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hy.le]
  have hp : x ^ (1 / 2 - σ) = x ^ (-σ) * x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [hp]
  ring

/-- Source Lemma 6 expressed in the positive physical-scale power used in AFE2. -/
theorem norm_chi_le_source_scale {σ t t₀ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1)
    (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|) :
    ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      chiC0 σ t₀ * (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) := by
  have hp : 1 / Real.pi ≤ 2 * Real.pi := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  have hb := norm_chi_le_chiC0 hσ (hp.trans ht₀) ht
  have he : 2 * Real.pi / |t| = (|t| / (2 * Real.pi))⁻¹ := by rw [inv_div]
  rw [he, ← Real.rpow_neg_eq_inv_rpow, show -(σ - 1 / 2) = 1 / 2 - σ by ring] at hb
  exact hb

/-- The direct uniform Theorem-10 estimate derived from the proof's A₀/B₀ branch, including the diagonal. -/
theorem afe_second_uniform_direct {σ t t₀ x y h : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hh : 3 / 2 ≤ h) (hx : h ≤ x) (hy : h ≤ y) (hyx : y ≤ x)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      (Real.log y / Real.pi + afeSourceA0 σ h t₀ + chiC0 σ t₀ * afeSourceB0 σ t₀) *
        (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  have hs : σ ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hσ.1, hσ.2]
  have htpos : 0 < t₀ := (by positivity : 0 < 2 * Real.pi).trans_le ht₀
  have hhpos : 0 < h := by linarith
  have hxpos := hhpos.trans_le hx
  have hypos := hhpos.trans_le hy
  have ha := afeSourceA_le_A0 hs.1 htpos hhpos hx hy hyx ht hscale
  have hb := afeSourceB_le_B0 hs ht₀ (by linarith) hyx ht hscale
  have hz := afe_second_source_AB hs (hh.trans hx) (hh.trans hy) hxhalf hyhalf hscale htpos ht
  have hm : ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      (Real.log y / Real.pi + afeSourceA0 σ h t₀) * x ^ (-σ) +
        ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * afeSourceB0 σ t₀ * y ^ (σ - 1) := by
    apply hz.trans
    gcongr
  have hr : 1 ≤ x ^ (1 / 2 : ℝ) / y ^ (1 / 2 : ℝ) := by
    apply (one_le_div (Real.rpow_pos_of_pos hypos _)).mpr
    exact Real.rpow_le_rpow hypos.le hyx (by norm_num)
  have hpower : x ^ (-σ) ≤ (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
    rw [afe_scale_power_identity σ hxpos hypos hscale]
    have hh' := mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hxpos.le (-σ))
    simpa only [mul_one] using hh'
  have hcoef : 0 ≤ Real.log y / Real.pi + afeSourceA0 σ h t₀ :=
    add_nonneg (div_nonneg (Real.log_nonneg (by linarith)) Real.pi_pos.le)
      (afeSourceA0_nonneg hs.1 hhpos htpos)
  have hfirst := mul_le_mul_of_nonneg_left hpower hcoef
  have hchi := mul_le_mul_of_nonneg_right (norm_chi_le_source_scale hσ ht₀ ht)
    (mul_nonneg (afeSourceB0_nonneg σ ht₀) (Real.rpow_nonneg hypos.le (σ - 1)))
  nlinarith only [hm, hfirst, hchi]


/-- The reflected uniform Theorem-10 estimate uses the dual A₀/B₀ branch and the source logarithmic coefficient. -/
theorem afe_second_uniform_reflected {σ t t₀ x y h : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hh : 3 / 2 ≤ h) (hx : h ≤ x) (hy : h ≤ y) (hxy : x ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      (chiC0 σ t₀ / Real.pi * Real.log x + afeSourceA0 (1 - σ) h t₀ * chiC0 σ t₀ +
        afeSourceB0 (1 - σ) t₀) * x ^ (-σ) := by
  have hs : σ ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hσ.1, hσ.2]
  have hd : 1 - σ ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hσ.1, hσ.2]
  have htpos : 0 < t₀ := (by positivity : 0 < 2 * Real.pi).trans_le ht₀
  have hhpos : 0 < h := by linarith
  have hxpos := hhpos.trans_le hx
  have hypos := hhpos.trans_le hy
  have hscale' : 2 * Real.pi * y * x = |t| := by rw [← hscale]; ring
  have ha := afeSourceA_le_A0 hd.1 htpos hhpos hy hx hxy ht hscale'
  have hb := afeSourceB_le_B0 hd ht₀ (by linarith) hxy ht hscale'
  have hz := afe_second_source_AB_reflected hs (hh.trans hx) (hh.trans hy) hxhalf hyhalf hscale htpos ht
  have hm : ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        (Real.log x / Real.pi + afeSourceA0 (1 - σ) h t₀) * y ^ (σ - 1) +
          afeSourceB0 (1 - σ) t₀ * x ^ (-σ) := by
    apply hz.trans
    gcongr
  have hr : x ^ (1 / 2 : ℝ) / y ^ (1 / 2 : ℝ) ≤ 1 := by
    apply (div_le_one (Real.rpow_pos_of_pos hypos _)).mpr
    exact Real.rpow_le_rpow hxpos.le hxy (by norm_num)
  have hpower : (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) ≤ x ^ (-σ) := by
    rw [afe_scale_power_identity σ hxpos hypos hscale]
    have hh' := mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hxpos.le (-σ))
    simpa only [mul_one] using hh'
  have hcoef : 0 ≤ Real.log x / Real.pi + afeSourceA0 (1 - σ) h t₀ :=
    add_nonneg (div_nonneg (Real.log_nonneg (by linarith)) Real.pi_pos.le)
      (afeSourceA0_nonneg hd.1 hhpos htpos)
  have hchi := mul_le_mul_of_nonneg_right (norm_chi_le_source_scale hσ ht₀ ht)
    (mul_nonneg hcoef (Real.rpow_nonneg hypos.le (σ - 1)))
  have hfirst := mul_le_mul_of_nonneg_left hpower (mul_nonneg (chiC0_pos hσ htpos).le hcoef)
  simp only [div_eq_mul_inv] at hm hchi hfirst ⊢
  nlinarith only [hm, hchi, hfirst]

/-- The actual AFE satisfies the proof-consistent two-region formula, with the diagonal in the direct branch. -/
theorem afe_second_uniform_branches {σ t t₀ x y h : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hh : 3 / 2 ≤ h) (hx : h ≤ x) (hy : h ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      if y ≤ x then
        (Real.log y / Real.pi + afeSourceA0 σ h t₀ + chiC0 σ t₀ * afeSourceB0 σ t₀) *
          (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1)
      else (chiC0 σ t₀ / Real.pi * Real.log x + afeSourceA0 (1 - σ) h t₀ * chiC0 σ t₀ +
        afeSourceB0 (1 - σ) t₀) * x ^ (-σ) := by
  split_ifs with hxy
  · exact afe_second_uniform_direct hσ ht₀ ht hh hx hy hxy hxhalf hyhalf hscale
  · exact afe_second_uniform_reflected hσ ht₀ ht hh hx hy (le_of_not_ge hxy) hxhalf hyhalf hscale

end DhimanKadiriQuesadaHerrera2026
