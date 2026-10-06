import DhimanKadiriQuesadaHerrera2026.FresnelNumeric

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- Positive curvature and nonnegative slope give the exact phase-energy inequality. -/
theorem curvature_energy_lower {f : ℝ → ℝ} {a b x ℓ : ℝ}
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 ≤ deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u)
    (hx : x ∈ Set.Icc a b) :
    (deriv f a) ^ 2 + 2 * ℓ * (f x - f a) ≤ (deriv f x) ^ 2 := by
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (fun v => (deriv f v) ^ 2 - 2 * ℓ * f v)
        (2 * deriv f u * (deriv (deriv f) u - ℓ)) u := by
    convert ((hf' u hu).hasDerivAt.pow 2).sub ((hf u hu).hasDerivAt.const_mul (2 * ℓ)) using 1
    dsimp only [id_eq]
    ring
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u (interior_subset hu)).hasDerivWithinAt)
    (fun u hu => mul_nonneg (mul_nonneg (by norm_num) (hpos u (interior_subset hu)))
      (sub_nonneg.mpr (hcurv u (interior_subset hu))))
  have h := hm (Set.left_mem_Icc.mpr (hx.1.trans hx.2)) hx hx.1
  dsimp only at h
  linarith

/-- The same assumptions force quadratic growth away from the left endpoint. -/
theorem curvature_phase_lower {f : ℝ → ℝ} {a b x ℓ : ℝ}
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (ha : 0 ≤ deriv f a)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u)
    (hx : x ∈ Set.Icc a b) : ℓ * (x - a) ^ 2 / 2 ≤ f x - f a := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hg (u : ℝ) (hu : u ∈ Set.Icc a b) : ℓ * (u - a) ≤ deriv f u := by
    have h := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      (fun v hv => (hf' v hv).continuousAt.continuousWithinAt)
      (fun v hv => (hf' v (interior_subset hv)).differentiableWithinAt)
      (fun v hv => hcurv v (interior_subset hv))
      a (Set.left_mem_Icc.mpr hab) u hu hu.1
    linarith
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (fun v => f v - ℓ * (v - a) ^ 2 / 2)
        (deriv f u - ℓ * (u - a)) u := by
    convert (hf u hu).hasDerivAt.sub ((((hasDerivAt_id u).sub_const a).pow 2).const_mul ℓ |>.div_const 2) using 1
    dsimp only [id_eq]
    ring
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u (interior_subset hu)).hasDerivWithinAt)
    (fun u hu => sub_nonneg.mpr (hg u (interior_subset hu)))
  have h := hm (Set.left_mem_Icc.mpr hab) hx hx.1
  dsimp only at h
  nlinarith

/-- After a sine maximum, an increasing positive derivative makes every remaining cosine tail nonpositive. -/
theorem cosine_tail_nonpos {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 < deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, 0 ≤ deriv (deriv f) u)
    (ha : Real.sin (f a) = 1) : (∫ u in a..b, Real.cos (f u)) ≤ 0 := by
  let g : ℝ → ℝ := fun u => (Real.sin (f u) - 1) / deriv f u
  let gp : ℝ → ℝ := fun u =>
    (Real.cos (f u) * deriv f u * deriv f u - (Real.sin (f u) - 1) * deriv (deriv f) u) /
      (deriv f u) ^ 2
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) : HasDerivAt g (gp u) u := by
    exact ((hf u hu).hasDerivAt.sin.sub_const 1).div (hf' u hu).hasDerivAt (hpos u hu).ne'
  have hle (u : ℝ) (hu : u ∈ Set.Icc a b) : Real.cos (f u) ≤ gp u := by
    dsimp [gp]
    apply (le_div_iff₀ (sq_pos_of_pos (hpos u hu))).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr (Real.sin_le_one (f u))) (hcurv u hu)]
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u (Set.Ioo_subset_Icc_self hu)).hasDerivWithinAt)
    (show IntegrableOn (fun u => Real.cos (f u)) (Set.Icc a b) from
      (show ContinuousOn (fun u => Real.cos (f u)) (Set.Icc a b) from
        fun u hu => (Real.continuous_cos.continuousAt.comp (hf u hu).continuousAt).continuousWithinAt).integrableOn_Icc)
    (fun u hu => hle u (Set.Ioo_subset_Icc_self hu))
  have hb : g b ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (Real.sin_le_one _)) (hpos b (Set.right_mem_Icc.mpr hab)).le
  have hga : g a = 0 := by simp [g, ha]
  rw [hga, sub_zero] at h
  exact h.trans hb

/-- On a nonnegative cosine lobe, positive curvature compares the actual integral with a genuine quadratic prefix. -/
theorem cosine_positive_lobe_bound {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 ≤ deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u)
    (hcos : ∀ u ∈ Set.Icc a b, 0 ≤ Real.cos (f u)) :
    (∫ u in a..b, Real.cos (f u)) ≤ 119 / (100 * Real.sqrt (ℓ / 2)) := by
  let q : ℝ → ℝ := fun u => 2 * (f u - f a) / ℓ
  let J : ℝ → ℝ := fun y => ∫ v in (0 : ℝ)..y, Real.cos (f a + ℓ / 2 * v ^ 2)
  let g : ℝ → ℝ := fun u => J (Real.sqrt (q u))
  let gp : ℝ → ℝ := fun u => Real.cos (f u) * (deriv f u / (ℓ * Real.sqrt (q u)))
  have hφ : Continuous (fun v : ℝ => Real.cos (f a + ℓ / 2 * v ^ 2)) := by fun_prop
  have hJ (y : ℝ) : HasDerivAt J (Real.cos (f a + ℓ / 2 * y ^ 2)) y :=
    intervalIntegral.integral_hasDerivAt_right (hφ.intervalIntegrable 0 y)
      hφ.aestronglyMeasurable.stronglyMeasurableAtFilter hφ.continuousAt
  have hfc : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.Icc a b) := by
    have hJc : Continuous J := continuous_iff_continuousAt.mpr (fun y => (hJ y).continuousAt)
    exact hJc.comp_continuousOn (((hfc.sub continuousOn_const).const_mul 2).div_const ℓ).sqrt
  have hq (u : ℝ) (hu : u ∈ Set.Ioo a b) : 0 < q u := by
    have hl := curvature_phase_lower hf hf' (hpos a (Set.left_mem_Icc.mpr hab)) hcurv
      (Set.Ioo_subset_Icc_self hu)
    have hgap : 0 < f u - f a := by nlinarith [mul_pos hℓ (sq_pos_of_pos (sub_pos.mpr hu.1))]
    exact div_pos (mul_pos (by norm_num) hgap) hℓ
  have hd (u : ℝ) (hu : u ∈ Set.Ioo a b) : HasDerivAt g (gp u) u := by
    have hdu := ((((hf u (Set.Ioo_subset_Icc_self hu)).hasDerivAt.sub_const (f a)).const_mul 2).div_const ℓ).sqrt (hq u hu).ne'
    have hh := (hJ (Real.sqrt (q u))).comp u hdu
    change HasDerivAt g _ u at hh
    have he : f a + ℓ / 2 * (Real.sqrt (q u)) ^ 2 = f u := by
      rw [Real.sq_sqrt (hq u hu).le]
      dsimp [q]
      field_simp
      ring
    rw [he] at hh
    convert hh using 1
    dsimp [gp, q]
    field_simp
  have hle (u : ℝ) (hu : u ∈ Set.Ioo a b) : Real.cos (f u) ≤ gp u := by
    have he := curvature_energy_lower hf hf' hpos hcurv (Set.Ioo_subset_Icc_self hu)
    have hs : 0 < Real.sqrt (q u) := Real.sqrt_pos.mpr (hq u hu)
    have hsq : (ℓ * Real.sqrt (q u)) ^ 2 = 2 * ℓ * (f u - f a) := by
      rw [mul_pow, Real.sq_sqrt (hq u hu).le]
      dsimp [q]
      field_simp
    have hfn := hpos u (Set.Ioo_subset_Icc_self hu)
    have hden : 0 < ℓ * Real.sqrt (q u) := mul_pos hℓ hs
    have hlow : ℓ * Real.sqrt (q u) ≤ deriv f u := by nlinarith [sq_nonneg (deriv f a)]
    have hr : 1 ≤ deriv f u / (ℓ * Real.sqrt (q u)) := (le_div_iff₀ hden).mpr (by simpa using hlow)
    dsimp [gp]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr (hcos u (Set.Ioo_subset_Icc_self hu))
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hgc
    (fun u hu => (hd u hu).hasDerivWithinAt) (Real.continuous_cos.comp_continuousOn hfc).integrableOn_Icc hle
  have hga : g a = 0 := by simp [g, q, J]
  rw [hga, sub_zero] at h
  exact h.trans (quadratic_cos_prefix_le (f a) (Real.sqrt (q b)) (by positivity))

/-- The curvature lower bound makes the nonnegative initial slope strictly positive to its right. -/
theorem curvature_slope_lower {f : ℝ → ℝ} {a b x ℓ : ℝ}
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (ha : 0 ≤ deriv f a) (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u)
    (hx : x ∈ Set.Icc a b) : ℓ * (x - a) ≤ deriv f x := by
  have h := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    (fun v hv => (hf' v hv).continuousAt.continuousWithinAt)
    (fun v hv => (hf' v (interior_subset hv)).differentiableWithinAt)
    (fun v hv => hcurv v (interior_subset hv))
    a (Set.left_mem_Icc.mpr (hx.1.trans hx.2)) x hx hx.1
  linarith

/-- A phase starting in a positive cosine lobe is controlled through all subsequent oscillations. -/
theorem cosine_initial_positive_bound {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 ≤ deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u)
    (ha₁ : -(Real.pi / 2) ≤ f a) (ha₂ : f a < Real.pi / 2) :
    (∫ u in a..b, Real.cos (f u)) ≤ 119 / (100 * Real.sqrt (ℓ / 2)) := by
  have hfc : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc a b) hfc
    (fun u hu => (hf u (interior_subset hu)).differentiableWithinAt)
    (fun u hu => hpos u (interior_subset hu))
  by_cases hfb : f b ≤ Real.pi / 2
  · apply cosine_positive_lobe_bound hab hℓ hf hf' hpos hcurv
    intro u hu
    apply Real.cos_nonneg_of_mem_Icc
    exact ⟨ha₁.trans (hm (Set.left_mem_Icc.mpr hab) hu hu.1),
      (hm hu (Set.right_mem_Icc.mpr hab) hu.2).trans hfb⟩
  · obtain ⟨c, hcc, hv⟩ := intermediate_value_Icc hab hfc ⟨ha₂.le, le_of_not_ge hfb⟩
    have hac : a < c := lt_of_le_of_ne hcc.1 (by intro he; rw [← he] at hv; linarith)
    have hleftset : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hcc.2
    have hrightset : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc hcc.1 le_rfl
    have hleft := cosine_positive_lobe_bound hcc.1 hℓ
      (fun u hu => hf u (hleftset hu)) (fun u hu => hf' u (hleftset hu))
      (fun u hu => hpos u (hleftset hu)) (fun u hu => hcurv u (hleftset hu))
      (fun u hu => Real.cos_nonneg_of_mem_Icc
        ⟨ha₁.trans (hm (Set.left_mem_Icc.mpr hab) (hleftset hu) hu.1),
          (hm (hleftset hu) hcc hu.2).trans_eq hv⟩)
    have hright := cosine_tail_nonpos hcc.2
      (fun u hu => hf u (hrightset hu)) (fun u hu => hf' u (hrightset hu))
      (fun u hu => by
        have hl := curvature_slope_lower hf' (hpos a (Set.left_mem_Icc.mpr hab)) hcurv (hrightset hu)
        have hup : 0 < u - a := by linarith [hu.1]
        exact (mul_pos hℓ hup).trans_le hl)
      (fun u hu => hℓ.le.trans (hcurv u (hrightset hu)))
      (by rw [hv, Real.sin_pi_div_two])
    have hc : ContinuousOn (fun u => Real.cos (f u)) (Set.Icc a b) := Real.continuous_cos.comp_continuousOn hfc
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hc.mono hleftset).intervalIntegrable_of_Icc (μ := volume) hcc.1)
      ((hc.mono hrightset).intervalIntegrable_of_Icc (μ := volume) hcc.2)]
    linarith

/-- A negative initial cosine lobe can be discarded before applying the positive-lobe comparison. -/
theorem cosine_initial_negative_bound {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 ≤ deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u)
    (ha₁ : Real.pi / 2 ≤ f a) (ha₂ : f a ≤ Real.pi + Real.pi / 2) :
    (∫ u in a..b, Real.cos (f u)) ≤ 119 / (100 * Real.sqrt (ℓ / 2)) := by
  have hfc : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc a b) hfc
    (fun u hu => (hf u (interior_subset hu)).differentiableWithinAt)
    (fun u hu => hpos u (interior_subset hu))
  have hnonpos {c : ℝ} (hcc : c ∈ Set.Icc a b) (hc : f c ≤ Real.pi + Real.pi / 2) :
      (∫ u in a..c, Real.cos (f u)) ≤ 0 := by
    have hh : 0 ≤ ∫ u in a..c, -Real.cos (f u) := intervalIntegral.integral_nonneg hcc.1
      (fun u hu => neg_nonneg.mpr (Real.cos_nonpos_of_pi_div_two_le_of_le
        (ha₁.trans (hm (Set.left_mem_Icc.mpr hab) ⟨hu.1, hu.2.trans hcc.2⟩ hu.1))
        ((hm ⟨hu.1, hu.2.trans hcc.2⟩ hcc hu.2).trans hc)))
    simpa only [intervalIntegral.integral_neg, neg_nonneg] using hh
  by_cases hfb : f b ≤ Real.pi + Real.pi / 2
  · exact (hnonpos (Set.right_mem_Icc.mpr hab) hfb).trans (by positivity)
  · obtain ⟨c, hcc, hv⟩ := intermediate_value_Icc hab hfc ⟨ha₂, le_of_not_ge hfb⟩
    have hleftset : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hcc.2
    have hrightset : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc hcc.1 le_rfl
    let g : ℝ → ℝ := fun u => f u - 2 * Real.pi
    have hg : deriv g = deriv f := deriv_sub_const_fun _
    have hright := cosine_initial_positive_bound (f := g) hcc.2 hℓ
      (fun u hu => (hf u (hrightset hu)).sub_const _)
      (fun u hu => by rw [hg]; exact hf' u (hrightset hu))
      (fun u hu => by rw [hg]; exact hpos u (hrightset hu))
      (fun u hu => by rw [hg]; exact hcurv u (hrightset hu))
      (by dsimp [g]; rw [hv]; linarith)
      (by dsimp [g]; rw [hv]; linarith [Real.pi_pos])
    simp only [g, Real.cos_sub_two_pi] at hright
    have hc : ContinuousOn (fun u => Real.cos (f u)) (Set.Icc a b) := Real.continuous_cos.comp_continuousOn hfc
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hc.mono hleftset).intervalIntegrable_of_Icc (μ := volume) hcc.1)
      ((hc.mono hrightset).intervalIntegrable_of_Icc (μ := volume) hcc.2)]
    linarith [hnonpos hcc hv.le]

/-- Reducing the initial phase modulo two pi removes the lobe-placement restriction. -/
theorem cosine_curvature_bound {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 ≤ deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u) :
    (∫ u in a..b, Real.cos (f u)) ≤ 119 / (100 * Real.sqrt (ℓ / 2)) := by
  let k : ℤ := ⌊(f a + Real.pi / 2) / (2 * Real.pi)⌋
  let g : ℝ → ℝ := fun u => f u - (k : ℝ) * (2 * Real.pi)
  have hg : deriv g = deriv f := deriv_sub_const_fun _
  have hlo : (k : ℝ) * (2 * Real.pi) ≤ f a + Real.pi / 2 :=
    (le_div_iff₀ Real.two_pi_pos).mp (Int.floor_le _)
  have hhi : f a + Real.pi / 2 < ((k : ℝ) + 1) * (2 * Real.pi) :=
    (div_lt_iff₀ Real.two_pi_pos).mp (Int.lt_floor_add_one _)
  have ha₁ : -(Real.pi / 2) ≤ g a := by dsimp [g]; linarith
  have ha₂ : g a ≤ Real.pi + Real.pi / 2 := by dsimp [g]; nlinarith
  have hgd (u : ℝ) (hu : u ∈ Set.Icc a b) : DifferentiableAt ℝ g u := (hf u hu).sub_const _
  have hgd' (u : ℝ) (hu : u ∈ Set.Icc a b) : DifferentiableAt ℝ (deriv g) u := by rw [hg]; exact hf' u hu
  have hgp (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 ≤ deriv g u := by rw [hg]; exact hpos u hu
  have hgc (u : ℝ) (hu : u ∈ Set.Icc a b) : ℓ ≤ deriv (deriv g) u := by rw [hg]; exact hcurv u hu
  have h : (∫ u in a..b, Real.cos (g u)) ≤ 119 / (100 * Real.sqrt (ℓ / 2)) := by
    by_cases hga : g a < Real.pi / 2
    · exact cosine_initial_positive_bound hab hℓ hgd hgd' hgp hgc ha₁ hga
    · exact cosine_initial_negative_bound hab hℓ hgd hgd' hgp hgc (le_of_not_gt hga) ha₂
  simpa only [g, Real.cos_sub_int_mul_two_pi] using h

/-- Rotating to the actual integral's argument turns the real projection bound into a complex norm bound. -/
theorem norm_curvature_positive_slope {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hpos : ∀ u ∈ Set.Icc a b, 0 ≤ deriv f u)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u) :
    ‖∫ u in a..b, Complex.exp ((f u : ℂ) * Complex.I)‖ ≤ 119 / (100 * Real.sqrt (ℓ / 2)) := by
  let z : ℂ := ∫ u in a..b, Complex.exp ((f u : ℂ) * Complex.I)
  let θ : ℝ := -Complex.arg z
  let g : ℝ → ℝ := fun u => f u + θ
  have hg : deriv g = deriv f := deriv_add_const' _
  have hgd (u : ℝ) (hu : u ∈ Set.Icc a b) : DifferentiableAt ℝ g u := (hf u hu).add_const _
  have h := cosine_curvature_bound (f := g) hab hℓ hgd
    (fun u hu => by rw [hg]; exact hf' u hu)
    (fun u hu => by rw [hg]; exact hpos u hu)
    (fun u hu => by rw [hg]; exact hcurv u hu)
  have hkc : ContinuousOn (fun u => Complex.exp ((g u : ℂ) * Complex.I)) (Set.Icc a b) := by
    have hgc : ContinuousOn g (Set.Icc a b) := fun u hu => (hgd u hu).continuousAt.continuousWithinAt
    fun_prop
  have hr := intervalIntegral.intervalIntegral_re (hkc.intervalIntegrable_of_Icc (μ := volume) hab)
  simp only [RCLike.re_eq_complex_re, Complex.exp_ofReal_mul_I_re] at hr
  have he (u : ℝ) : Complex.exp ((g u : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((f u : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [g]
    push_cast
    ring
  have hi : (∫ u in a..b, Complex.exp ((g u : ℂ) * Complex.I)) =
      Complex.exp ((θ : ℂ) * Complex.I) * z := by
    simp_rw [he, intervalIntegral.integral_const_mul]
    rfl
  have ht : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    simp [θ]
  have hz : Complex.exp ((θ : ℂ) * Complex.I) * z = (‖z‖ : ℂ) := by
    calc
      _ = Complex.exp ((θ : ℂ) * Complex.I) *
          ((‖z‖ : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I)) := by
        rw [Complex.norm_mul_exp_arg_mul_I]
      _ = (‖z‖ : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) *
          Complex.exp ((Complex.arg z : ℂ) * Complex.I)) := by ring
      _ = _ := by rw [ht, mul_one]
  rw [hr, hi, hz, Complex.ofReal_re] at h
  exact h

/-- Reflection gives the same half bound when the slope is nonpositive. -/
theorem norm_curvature_negative_slope {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hneg : ∀ u ∈ Set.Icc a b, deriv f u ≤ 0)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u) :
    ‖∫ u in a..b, Complex.exp ((f u : ℂ) * Complex.I)‖ ≤ 119 / (100 * Real.sqrt (ℓ / 2)) := by
  let g : ℝ → ℝ := fun u => f (-u)
  have hmap {u : ℝ} (hu : u ∈ Set.Icc (-b) (-a)) : -u ∈ Set.Icc a b := by
    constructor <;> linarith [hu.1, hu.2]
  have hg : deriv g = fun u => -deriv f (-u) := funext (fun u => deriv_comp_neg f u)
  have hgd (u : ℝ) (hu : u ∈ Set.Icc (-b) (-a)) : DifferentiableAt ℝ g u :=
    (hf (-u) (hmap hu)).comp u (hasDerivAt_neg u).differentiableAt
  have hdg (u : ℝ) (hu : u ∈ Set.Icc (-b) (-a)) :
      HasDerivAt (deriv g) (deriv (deriv f) (-u)) u := by
    rw [hg]
    convert ((hf' (-u) (hmap hu)).hasDerivAt.comp u (hasDerivAt_neg u)).neg using 1
    ring
  have h := norm_curvature_positive_slope (f := g) (by linarith : -b ≤ -a) hℓ hgd
    (fun u hu => (hdg u hu).differentiableAt)
    (fun u hu => by rw [hg]; exact neg_nonneg.mpr (hneg (-u) (hmap hu)))
    (fun u hu => by rw [(hdg u hu).deriv]; exact hcurv (-u) (hmap hu))
  change ‖∫ u in (-b)..(-a), Complex.exp ((f (-u) : ℂ) * Complex.I)‖ ≤ _ at h
  rw [intervalIntegral.integral_comp_neg (fun u => Complex.exp ((f u : ℂ) * Complex.I)), neg_neg, neg_neg] at h
  exact h

/-- Splitting at the actual critical point proves the general positive-curvature integral bound. -/
theorem norm_positive_curvature_integral {f : ℝ → ℝ} {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hcurv : ∀ u ∈ Set.Icc a b, ℓ ≤ deriv (deriv f) u) :
    ‖∫ u in a..b, Complex.exp ((f u : ℂ) * Complex.I)‖ ≤ 119 / (50 * Real.sqrt (ℓ / 2)) := by
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc a b) hfc
    (fun u hu => (hf' u (interior_subset hu)).differentiableWithinAt)
    (fun u hu => hℓ.le.trans (hcurv u (interior_subset hu)))
  have hB : 0 ≤ 119 / (100 * Real.sqrt (ℓ / 2)) := by positivity
  have hBB : 119 / (50 * Real.sqrt (ℓ / 2)) =
      2 * (119 / (100 * Real.sqrt (ℓ / 2))) := by ring
  rw [hBB]
  by_cases ha : 0 ≤ deriv f a
  · have h := norm_curvature_positive_slope hab hℓ hf hf'
      (fun u hu => ha.trans (hm (Set.left_mem_Icc.mpr hab) hu hu.1)) hcurv
    linarith
  by_cases hb : deriv f b ≤ 0
  · have h := norm_curvature_negative_slope hab hℓ hf hf'
      (fun u hu => (hm hu (Set.right_mem_Icc.mpr hab) hu.2).trans hb) hcurv
    linarith
  obtain ⟨c, hcc, hv⟩ := intermediate_value_Icc hab hfc ⟨le_of_not_ge ha, le_of_not_ge hb⟩
  have hleftset : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hcc.2
  have hrightset : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc hcc.1 le_rfl
  have hleft := norm_curvature_negative_slope hcc.1 hℓ
    (fun u hu => hf u (hleftset hu)) (fun u hu => hf' u (hleftset hu))
    (fun u hu => (hm (hleftset hu) hcc hu.2).trans_eq hv)
    (fun u hu => hcurv u (hleftset hu))
  have hright := norm_curvature_positive_slope hcc.2 hℓ
    (fun u hu => hf u (hrightset hu)) (fun u hu => hf' u (hrightset hu))
    (fun u hu => hv ▸ hm hcc (hrightset hu) hu.1)
    (fun u hu => hcurv u (hrightset hu))
  have hkc : ContinuousOn (fun u => Complex.exp ((f u : ℂ) * Complex.I)) (Set.Icc a b) := by
    have hc : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hkc.mono hleftset).intervalIntegrable_of_Icc (μ := volume) hcc.1)
    ((hkc.mono hrightset).intervalIntegrable_of_Icc (μ := volume) hcc.2)]
  exact (norm_add_le _ _).trans (by linarith)

end DhimanKadiriQuesadaHerrera2026
