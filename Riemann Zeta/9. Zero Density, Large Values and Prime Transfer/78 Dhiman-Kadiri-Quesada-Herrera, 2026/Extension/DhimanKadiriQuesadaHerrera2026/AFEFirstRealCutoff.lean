import DhimanKadiriQuesadaHerrera2026.AFEFirstMonotonicity

/-! # Transfer of the actual AFE1 sum to a real cutoff -/

namespace DhimanKadiriQuesadaHerrera2026

/-- The half-integer in the same integer cell as a real cutoff. -/
noncomputable def afeHalfCutoff (t : ℝ) : ℝ := (⌊t⌋₊ : ℝ) + 1 / 2

/-- The scale linking a real cutoff to the half-integer in its cell. -/
noncomputable def afeCutoffScale (t : ℝ) : ℝ := afeHalfCutoff t / t

/-- The exact three-way maximum c₀ in the source's real-cutoff corollary. -/
noncomputable def afeFirstRealConstant (t₀ : ℝ) : ℝ :=
  let N : ℝ := (⌊t₀⌋₊ : ℝ)
  max (max (afeFirstConstant ((N + 1 / 2) / t₀) t₀)
    (afeFirstConstant ((N + 3 / 2) / (N + 1)) t₀))
    (afeFirstConstant (1 - 1 / (2 * (N + 1))) t₀ / (1 - 1 / (2 * (N + 1))))

/-- Moving to the half-integer in the same cell leaves every sharp Dirichlet term unchanged. -/
theorem sharpZetaSum_afeHalfCutoff (s : ℂ) (t : ℝ) :
    sharpZetaSum s (afeHalfCutoff t) = sharpZetaSum s t := by
  have hf : ⌊afeHalfCutoff t⌋₊ = ⌊t⌋₊ := by
    unfold afeHalfCutoff
    rw [add_comm, Nat.floor_add_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  simp only [sharpZetaSum, hf]

/-- The chosen scale always lies strictly above the first-frequency threshold for t≥1. -/
theorem afeCutoffScale_gt_threshold {t : ℝ} (ht : 1 ≤ t) :
    1 / (2 * Real.pi) < afeCutoffScale t := by
  have htpos : 0 < t := by linarith
  have hf := Nat.lt_floor_add_one t
  have hn : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have hn' : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hn
  have hscale : (1 / 2 : ℝ) < afeCutoffScale t := by
    unfold afeCutoffScale afeHalfCutoff
    apply (lt_div_iff₀ htpos).mpr
    linarith
  have hπ : 1 / (2 * Real.pi) < (1 / 2 : ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith [Real.pi_gt_three]
  exact hπ.trans hscale

/-- The actual real-cutoff sum satisfies the half-integer theorem with its derived scale. -/
theorem afe_first_kind_real_cutoff_scaled {sigma t t₀ : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) (ht1 : 1 ≤ t) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      sharpZetaSum ((sigma : ℂ) + (t : ℂ) * Complex.I) t‖ ≤
      (afeFirstConstant (afeCutoffScale t) t₀ * (afeCutoffScale t) ^ (-sigma)) * t ^ (-sigma) := by
  have htpos : 0 < t := ht₀.trans_le ht
  have hx : 0 < afeHalfCutoff t := by unfold afeHalfCutoff; positivity
  have hc : 0 < afeCutoffScale t := div_pos hx htpos
  have hct : afeCutoffScale t * t = afeHalfCutoff t := by
    unfold afeCutoffScale
    exact div_mul_cancel₀ _ htpos.ne'
  have hhalf : ∃ k : ℤ, afeCutoffScale t * t = (k : ℝ) + 1 / 2 := by
    refine ⟨(⌊t⌋₊ : ℤ), ?_⟩
    rw [hct, afeHalfCutoff, Int.cast_natCast]
  have he := afe_first_kind hsigma ht₀ ht (afeCutoffScale_gt_threshold ht1) hhalf
  rw [hct, sharpZetaSum_afeHalfCutoff] at he
  have hr : (afeHalfCutoff t) ^ (-sigma) =
      (afeCutoffScale t) ^ (-sigma) * t ^ (-sigma) := by
    rw [← hct, Real.mul_rpow hc.le htpos.le]
  rw [hr] at he
  simpa only [mul_assoc] using he

/-- The derived cutoff scale is bounded by the source's exact three-way maximum. -/
theorem afe_cutoff_coefficient_le_real_constant {sigma t t₀ : ℝ}
    (hsigma : sigma ∈ Set.Ioc 0 1) (ht₀ : 14 ≤ t₀) (ht : t₀ ≤ t) :
    afeFirstConstant (afeCutoffScale t) t₀ * (afeCutoffScale t) ^ (-sigma) ≤
      afeFirstRealConstant t₀ := by
  have htpos : 0 < t := by linarith
  have ht₀pos : 0 < t₀ := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hM : 14 ≤ ⌊t₀⌋₊ := Nat.le_floor (by exact_mod_cast ht₀)
  have hMN : ⌊t₀⌋₊ ≤ ⌊t⌋₊ := Nat.floor_mono ht
  have hMr : (14 : ℝ) ≤ (⌊t₀⌋₊ : ℝ) := by exact_mod_cast hM
  have hMNr : (⌊t₀⌋₊ : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hMN
  have hNpos : 0 < (⌊t⌋₊ : ℝ) := by linarith
  have hM1 : 0 < (⌊t₀⌋₊ : ℝ) + 1 := by positivity
  have hNt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le htpos.le
  have htN : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hc := afeCutoffScale_gt_threshold ht1
  unfold afeFirstRealConstant
  dsimp only
  by_cases hcase : 1 ≤ afeCutoffScale t
  · have hw := afeFirstConstant_mul_rpow_le_self ht₀pos hcase hsigma.1.le
    by_cases heq : ⌊t⌋₊ = ⌊t₀⌋₊
    · have hscale : afeCutoffScale t ≤ ((⌊t₀⌋₊ : ℝ) + 1 / 2) / t₀ := by
        unfold afeCutoffScale afeHalfCutoff
        rw [heq]
        exact div_le_div_of_nonneg_left (by positivity) ht₀pos ht
      have hm := afeFirstConstant_monotone (by linarith : 1 ≤ t₀) hcase hscale
      exact le_max_of_le_left (le_max_of_le_left (hw.trans hm))
    · have hsucc : (⌊t₀⌋₊ : ℝ) + 1 ≤ (⌊t⌋₊ : ℝ) := by
        exact_mod_cast (show ⌊t₀⌋₊ + 1 ≤ ⌊t⌋₊ by omega)
      have hscale : afeCutoffScale t ≤
          ((⌊t₀⌋₊ : ℝ) + 3 / 2) / ((⌊t₀⌋₊ : ℝ) + 1) := by
        unfold afeCutoffScale afeHalfCutoff
        calc
          _ ≤ ((⌊t⌋₊ : ℝ) + 1 / 2) / (⌊t⌋₊ : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hNpos hNt
          _ ≤ _ := by
            apply (div_le_div_iff₀ hNpos hM1).mpr
            nlinarith
      have hm := afeFirstConstant_monotone (by linarith : 1 ≤ t₀) hcase hscale
      exact le_max_of_le_left (le_max_of_le_right (hw.trans hm))
  · have hc1 : afeCutoffScale t ≤ 1 := le_of_lt (lt_of_not_ge hcase)
    have hden : 0 < 2 * ((⌊t₀⌋₊ : ℝ) + 1) := by positivity
    have hrec : 1 / (2 * ((⌊t₀⌋₊ : ℝ) + 1)) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    have hc2 : 1 / (2 * Real.pi) < 1 - 1 / (2 * ((⌊t₀⌋₊ : ℝ) + 1)) := by
      have hpi : 1 / (2 * Real.pi) < (1 / 2 : ℝ) := by
        apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
        linarith [Real.pi_gt_three]
      linarith
    have hscale : 1 - 1 / (2 * ((⌊t₀⌋₊ : ℝ) + 1)) ≤ afeCutoffScale t := by
      unfold afeCutoffScale afeHalfCutoff
      calc
        _ ≤ ((⌊t⌋₊ : ℝ) + 1 / 2) / ((⌊t⌋₊ : ℝ) + 1) := by
          have he : 1 - 1 / (2 * ((⌊t₀⌋₊ : ℝ) + 1)) =
              ((⌊t₀⌋₊ : ℝ) + 1 / 2) / ((⌊t₀⌋₊ : ℝ) + 1) := by field_simp; ring
          rw [he]
          apply (div_le_div_iff₀ hM1 (by positivity)).mpr
          nlinarith
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) htpos htN.le
    have hw := afeFirstConstant_mul_rpow_le_div ht₀pos hc hc1 hsigma.2
    have hm := afeFirstConstant_div_antitone ht₀pos hc2 hscale
    exact le_max_of_le_right (hw.trans hm)

/-- Corollary 0.3 with its exact analytic c₀, for every real t≥t₀≥14.
The separate decimal claims require rigorous numerical certification. -/
theorem afe_first_kind_real_cutoff {sigma t t₀ : ℝ} (hsigma : sigma ∈ Set.Ioc 0 1)
    (ht₀ : 14 ≤ t₀) (ht : t₀ ≤ t) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      sharpZetaSum ((sigma : ℂ) + (t : ℂ) * Complex.I) t‖ ≤
      afeFirstRealConstant t₀ * t ^ (-sigma) := by
  have he := afe_first_kind_real_cutoff_scaled hsigma (by linarith : 0 < t₀) ht
    (by linarith : 1 ≤ t)
  exact he.trans (mul_le_mul_of_nonneg_right (afe_cutoff_coefficient_le_real_constant hsigma ht₀ ht)
    (Real.rpow_nonneg (by linarith) _))

/-- Every argument in c₀ lies in the valid Gamma domain, and c₀ is the literal source maximum. -/
theorem afeFirstRealConstant_eq_source {t₀ : ℝ} (ht₀ : 14 ≤ t₀) :
    let N : ℝ := (⌊t₀⌋₊ : ℝ)
    let m : ℝ → ℝ := fun c => c + (1 / Real.pi) * (1 / t₀ + 1) *
      (Real.log (1 + 1 / (2 * Real.pi * c)) + Real.eulerMascheroniConstant -
        deriv Real.Gamma (1 - 1 / (2 * Real.pi * c)) /
          Real.Gamma (1 - 1 / (2 * Real.pi * c)) -
        1 / (2 * (1 + 1 / (2 * Real.pi * c))) - 1 / 2)
    afeFirstRealConstant t₀ = max (max (m ((N + 1 / 2) / t₀))
      (m ((N + 3 / 2) / (N + 1)))) (m (1 - 1 / (2 * (N + 1))) / (1 - 1 / (2 * (N + 1)))) := by
  dsimp only
  have hc3 : 1 / (2 * Real.pi) < ((⌊t₀⌋₊ : ℝ) + 1 / 2) / t₀ :=
    afeCutoffScale_gt_threshold (by linarith)
  have hπhalf : 1 / (2 * Real.pi) < (1 / 2 : ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith [Real.pi_gt_three]
  have hc4 : 1 / (2 * Real.pi) < ((⌊t₀⌋₊ : ℝ) + 3 / 2) / ((⌊t₀⌋₊ : ℝ) + 1) := by
    apply hπhalf.trans
    apply (lt_div_iff₀ (by positivity)).mpr
    have hn := Nat.cast_nonneg (α := ℝ) ⌊t₀⌋₊
    linarith
  have hrec : 1 / (2 * ((⌊t₀⌋₊ : ℝ) + 1)) ≤ (1 / 2 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    have hn := Nat.cast_nonneg (α := ℝ) ⌊t₀⌋₊
    linarith
  have hc2 : 1 / (2 * Real.pi) < 1 - 1 / (2 * ((⌊t₀⌋₊ : ℝ) + 1)) := by linarith
  unfold afeFirstRealConstant
  dsimp only
  rw [afeFirstConstant_eq_source hc3, afeFirstConstant_eq_source hc4, afeFirstConstant_eq_source hc2]

end DhimanKadiriQuesadaHerrera2026
