import DhimanKadiriQuesadaHerrera2026.AFESecondUniform
import Mathlib.Topology.Order.Compact

namespace DhimanKadiriQuesadaHerrera2026

/-- The proof-consistent direct error coefficient. -/
noncomputable def afeDirectE0 (σ h t₀ : ℝ) : ℝ :=
  afeSourceA0 σ h t₀ + chiC0 σ t₀ * afeSourceB0 σ t₀

/-- The proof-consistent reflected error coefficient, with the actual dual exponent. -/
noncomputable def afeReflectedE0 (σ h t₀ : ℝ) : ℝ :=
  afeSourceA0 (1 - σ) h t₀ * chiC0 σ t₀ + afeSourceB0 (1 - σ) t₀

/-- The source sigma interval, including both endpoints. -/
def afeSigmaStrip : Set ℝ := Set.Icc (1 / 2) 1

/-- The exact uniform direct constant, defined over the entire closed source interval. -/
noncomputable def afeDirectMaximum (h t₀ : ℝ) : ℝ :=
  sSup ((fun σ => afeDirectE0 σ h t₀) '' afeSigmaStrip)

/-- The exact uniform reflected constant over the entire closed source interval. -/
noncomputable def afeReflectedMaximum (h t₀ : ℝ) : ℝ :=
  sSup ((fun σ => afeReflectedE0 σ h t₀) '' afeSigmaStrip)

/-- The exact excess chi constant in Corollary 0.4. -/
noncomputable def afeDelta0 (t₀ : ℝ) : ℝ :=
  sSup ((fun σ => chiC0 σ t₀) '' afeSigmaStrip) - 1

/-- Every term of the source A₀ is continuous in sigma. -/
theorem continuous_afeSourceA0 (h t₀ : ℝ) : Continuous (fun σ => afeSourceA0 σ h t₀) := by
  unfold afeSourceA0
  fun_prop

/-- The source B₀ is continuous in sigma throughout the real line at positive threshold. -/
theorem continuous_afeSourceB0 {t₀ : ℝ} (ht : 0 < t₀) : Continuous (fun σ => afeSourceB0 σ t₀) := by
  have hb : 0 < t₀ / (2 * Real.pi) := by positivity
  unfold afeSourceB0
  simp_rw [Real.rpow_def_of_pos hb]
  fun_prop

/-- The literal chi coefficient is continuous in sigma. -/
theorem continuous_chiC0_sigma (t₀ : ℝ) : Continuous (fun σ => chiC0 σ t₀) := by
  unfold chiC0 chiC1
  fun_prop

/-- Both proof-consistent branch coefficients are continuous on the complete real sigma line. -/
theorem continuous_afeE0 {h t₀ : ℝ} (ht : 0 < t₀) :
    Continuous (fun σ => afeDirectE0 σ h t₀) ∧ Continuous (fun σ => afeReflectedE0 σ h t₀) := by
  have ha := continuous_afeSourceA0 h t₀
  have hb := continuous_afeSourceB0 ht
  have hc := continuous_chiC0_sigma t₀
  exact ⟨ha.add (hc.mul hb), (ha.comp (continuous_const.sub continuous_id)).mul hc |>.add
    (hb.comp (continuous_const.sub continuous_id))⟩

/-- Each of the exact source maxima is attained, with global coverage and both endpoints included. -/
theorem afe_source_maxima_attained {h t₀ : ℝ} (ht : 0 < t₀) :
    (∃ σ ∈ afeSigmaStrip, afeDirectMaximum h t₀ = afeDirectE0 σ h t₀) ∧
    (∃ σ ∈ afeSigmaStrip, afeReflectedMaximum h t₀ = afeReflectedE0 σ h t₀) ∧
    (∃ σ ∈ afeSigmaStrip, afeDelta0 t₀ + 1 = chiC0 σ t₀) := by
  have hn : afeSigmaStrip.Nonempty := ⟨1, by norm_num [afeSigmaStrip]⟩
  have hc : IsCompact afeSigmaStrip := isCompact_Icc
  have he := continuous_afeE0 (h := h) ht
  refine ⟨hc.exists_sSup_image_eq hn he.1.continuousOn,
    hc.exists_sSup_image_eq hn he.2.continuousOn, ?_⟩
  obtain ⟨σ, hσ, heq⟩ := hc.exists_sSup_image_eq hn (continuous_chiC0_sigma t₀).continuousOn
  refine ⟨σ, hσ, ?_⟩
  simpa only [afeDelta0, sub_add_cancel] using heq

/-- All source sigma values are bounded by the exact attained maxima. -/
theorem afe_source_le_maxima {σ h t₀ : ℝ} (ht : 0 < t₀) (hσ : σ ∈ afeSigmaStrip) :
    afeDirectE0 σ h t₀ ≤ afeDirectMaximum h t₀ ∧
    afeReflectedE0 σ h t₀ ≤ afeReflectedMaximum h t₀ ∧
    chiC0 σ t₀ ≤ 1 + afeDelta0 t₀ := by
  have hc : IsCompact afeSigmaStrip := isCompact_Icc
  have he := continuous_afeE0 (h := h) ht
  refine ⟨le_csSup (hc.image_of_continuousOn he.1.continuousOn).bddAbove ⟨σ, hσ, rfl⟩,
    le_csSup (hc.image_of_continuousOn he.2.continuousOn).bddAbove ⟨σ, hσ, rfl⟩, ?_⟩
  have h := le_csSup (hc.image_of_continuousOn (continuous_chiC0_sigma t₀).continuousOn).bddAbove
    (Set.mem_image_of_mem (fun σ => chiC0 σ t₀) hσ)
  dsimp only [afeDelta0]
  linarith

/-- Corollary 0.4's direct logarithmic bound follows from the actual AFE and the exact global maximum. -/
theorem afe_uniform_max_direct {σ t t₀ x y h : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hh : 3 / 2 ≤ h) (hx : h ≤ x) (hy : h ≤ y) (hyx : y ≤ x)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      (Real.log y / Real.pi + afeDirectMaximum h t₀) *
        (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  have htpos : 0 < t₀ := lt_of_lt_of_le (by positivity : 0 < 2 * Real.pi) ht₀
  have hT : 0 < |t| := htpos.trans_le ht
  have hypos : 0 < y := by linarith
  have hb := (afe_source_le_maxima (h := h) htpos hσ).1
  have hs := afe_second_uniform_direct hσ ht₀ ht hh hx hy hyx hxhalf hyhalf hscale
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hypos.le (σ - 1))
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (div_nonneg hT.le (by positivity)) (1 / 2 - σ))
  dsimp only [afeDirectE0] at hb
  linarith

/-- Corollary 0.4's reflected logarithmic bound follows from the actual reflected remainder and both global maxima. -/
theorem afe_uniform_max_reflected {σ t t₀ x y h : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hh : 3 / 2 ≤ h) (hx : h ≤ x) (hy : h ≤ y) (hxy : x ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      ((1 + afeDelta0 t₀) / Real.pi * Real.log x + afeReflectedMaximum h t₀) * x ^ (-σ) := by
  have htpos : 0 < t₀ := lt_of_lt_of_le (by positivity : 0 < 2 * Real.pi) ht₀
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hb := afe_source_le_maxima (h := h) htpos hσ
  have hs := afe_second_uniform_reflected hσ ht₀ ht hh hx hy hxy hxhalf hyhalf hscale
  apply hs.trans
  have hm := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb.2.2 Real.pi_pos.le) hlog
  have ha := add_le_add hm hb.2.1
  dsimp only [afeReflectedE0] at ha
  simpa only [← add_assoc] using mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hxpos.le _)


/-- The literal chi majorant is at least one on the complete source strip. -/
theorem one_le_chiC0 {σ t₀ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht : 0 < t₀) :
    1 ≤ chiC0 σ t₀ := by
  rw [chiC0_eq ht]
  have h₂ : 1 ≤ chiC2 t₀ := by
    unfold chiC2
    exact Real.one_le_exp_iff.mpr (by positivity)
  have h₃ : 1 ≤ 1 + Real.exp (-Real.pi * t₀) := by linarith [Real.exp_pos (-Real.pi * t₀)]
  have h₁ : 1 ≤ 1 + chiC1 σ t₀ / t₀ := by
    have hh := div_nonneg (chiC1_nonneg hσ ht) ht.le
    linarith
  have hp : 1 ≤ chiC2 t₀ * (1 + Real.exp (-Real.pi * t₀)) := by
    nlinarith only [h₂, h₃, mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₃)]
  nlinarith only [hp, h₁, mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr h₁)]

/-- The global excess chi constant is nonnegative, with no optimizer or sampled certificate. -/
theorem afeDelta0_nonneg {t₀ : ℝ} (ht : 0 < t₀) : 0 ≤ afeDelta0 t₀ := by
  have hσ : (1 : ℝ) ∈ afeSigmaStrip := by norm_num [afeSigmaStrip]
  have h := (afe_source_le_maxima (h := 1) ht hσ).2.2
  have hc := one_le_chiC0 (show (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 by norm_num) ht
  linarith

/-- The exact lower endpoint hₖ in Corollary 0.5. -/
noncomputable def afeBandLower (k : ℕ) : ℝ := (⌊Real.exp ((k : ℝ) - 1)⌋₊ : ℝ) + 1 / 2

/-- Every allowed band lower endpoint satisfies the source minimum cutoff. -/
theorem afeBandLower_ge {k : ℕ} (hk : 1 ≤ k) : 3 / 2 ≤ afeBandLower k := by
  have hr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he : (1 : ℝ) ≤ Real.exp ((k : ℝ) - 1) := Real.one_le_exp_iff.mpr (by linarith)
  have hf : (1 : ℕ) ≤ ⌊Real.exp ((k : ℝ) - 1)⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using he)
  have hf' : (1 : ℝ) ≤ (⌊Real.exp ((k : ℝ) - 1)⌋₊ : ℝ) := by exact_mod_cast hf
  unfold afeBandLower
  linarith

/-- The direct Corollary-0.5 band bound follows on every integer band, hence also on k=1,...,50. -/
theorem afe_band_direct {σ t t₀ x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hk : 1 ≤ k) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hyx : y ≤ x)
    (hband : y ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      ((k : ℝ) / Real.pi + afeDirectMaximum (afeBandLower k) t₀) *
        (|t| / (2 * Real.pi)) ^ (1 / 2 - σ) * y ^ (σ - 1) := by
  have hh := afeBandLower_ge hk
  have hypos : 0 < y := by linarith
  have hs := afe_uniform_max_direct hσ ht₀ ht hh hx hy hyx hxhalf hyhalf hscale
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hypos.le (σ - 1))
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (by positivity)) (1 / 2 - σ))
  have hlog := (Real.log_le_iff_le_exp hypos).mpr hband
  have hd := div_le_div_of_nonneg_right hlog Real.pi_pos.le
  linarith

/-- The reflected Corollary-0.5 band bound retains k(1+δ₀)/π throughout every allowed integer band. -/
theorem afe_band_reflected {σ t t₀ x y : ℝ} {k : ℕ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (ht₀ : 2 * Real.pi ≤ t₀) (ht : t₀ ≤ |t|)
    (hk : 1 ≤ k) (hx : afeBandLower k ≤ x) (hy : afeBandLower k ≤ y) (hxy : x ≤ y)
    (hband : x ≤ Real.exp (k : ℝ))
    (hxhalf : ∃ j : ℤ, x = (j : ℝ) + 1 / 2)
    (hyhalf : ∃ j : ℤ, y = (j : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      ((k : ℝ) * (1 + afeDelta0 t₀) / Real.pi + afeReflectedMaximum (afeBandLower k) t₀) * x ^ (-σ) := by
  have hh := afeBandLower_ge hk
  have hxpos : 0 < x := by linarith
  have htpos : 0 < t₀ := lt_of_lt_of_le (by positivity : 0 < 2 * Real.pi) ht₀
  have hs := afe_uniform_max_reflected hσ ht₀ ht hh hx hy hxy hxhalf hyhalf hscale
  apply hs.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxpos.le (-σ))
  have hlog := (Real.log_le_iff_le_exp hxpos).mpr hband
  have hm := mul_le_mul_of_nonneg_left hlog
    (div_nonneg (show 0 ≤ 1 + afeDelta0 t₀ by linarith [afeDelta0_nonneg htpos]) Real.pi_pos.le)
  have he : (1 + afeDelta0 t₀) / Real.pi * (k : ℝ) = (k : ℝ) * (1 + afeDelta0 t₀) / Real.pi := by ring
  rw [he] at hm
  linarith

end DhimanKadiriQuesadaHerrera2026
