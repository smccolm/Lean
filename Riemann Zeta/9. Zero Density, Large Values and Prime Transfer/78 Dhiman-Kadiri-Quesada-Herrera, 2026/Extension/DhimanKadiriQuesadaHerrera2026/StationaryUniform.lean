import DhimanKadiriQuesadaHerrera2026.AngularGeometry

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- A right-hand source interval controls the actual half stationary term, without a third-derivative error. -/
theorem stationary_right_uniform_global {f : ℝ → ℝ} {a b ℓ ν A : ℝ}
    (hab : a ≤ b) (hℓ : 0 < ℓ) (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) (hslope : deriv f a ≤ ν)
    (hA : 0 ≤ A) (hAmax : A ≤ 1 / (2 * Real.sqrt ℓ)) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      (A : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ))‖ ≤
      0.928 / Real.sqrt ℓ := by
  let g : ℝ → ℝ := fun u => 2 * Real.pi * ((f a - ν * a) - (f u - ν * u))
  have hgd (u : ℝ) : HasDerivAt g (-2 * Real.pi * (deriv f u - ν)) u := by
    convert (((hf u).hasDerivAt.sub ((hasDerivAt_id u).const_mul ν)).const_sub (f a - ν * a)).const_mul (2 * Real.pi) using 1
    simp
    ring
  have hg : deriv g = fun u => -2 * Real.pi * (deriv f u - ν) := funext fun u => (hgd u).deriv
  have hgd' (u : ℝ) : HasDerivAt (deriv g) (-2 * Real.pi * deriv (deriv f) u) u := by
    rw [hg]
    exact ((hf' u).hasDerivAt.sub_const ν).const_mul _
  have hm : AntitoneOn (deriv f) (Set.Icc a b) := antitoneOn_of_deriv_nonpos (convex_Icc a b)
    hf'.continuous.continuousOn (fun u _ => (hf' u).differentiableWithinAt)
    (fun u hu => (hcurv u (interior_subset hu)).trans (neg_nonpos.mpr hℓ.le))
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 ≤ deriv g u := by
    rw [(hgd u).deriv]
    have hh := (hm (Set.left_mem_Icc.mpr hab) hu hu.1).trans hslope
    nlinarith [Real.pi_pos]
  have hh := norm_positive_half_sub_main hab hℓ (fun u _ => (hgd u).differentiableAt)
    (fun u _ => (hgd' u).differentiableAt) hp
    (fun u hu => by rw [(hgd' u).deriv]; nlinarith [hcurv u hu, Real.pi_pos])
    (by dsimp [g]; ring : g a = 0) hA hAmax
  let P : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a : ℝ) : ℂ))
  have he (u : ℝ) : Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ)) =
      P * (starRingEnd ℂ) (Complex.exp ((g u : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    dsimp [P, g]
    rw [← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hi : (∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) =
      P * (starRingEnd ℂ) (∫ u in a..b, Complex.exp ((g u : ℂ) * Complex.I)) := by
    simp_rw [he, intervalIntegral.integral_const_mul]
    congr 1
    simp only [intervalIntegral, integral_conj, map_sub]
  have hmain : Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ)) =
      P * (starRingEnd ℂ) (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    dsimp [P]
    rw [← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hPn : ‖P‖ = 1 := by
    dsimp [P]
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re, Complex.mul_im]
  rw [hi, hmain]
  have hfactor : P * (starRingEnd ℂ) (∫ u in a..b, Complex.exp ((g u : ℂ) * Complex.I)) -
      (A : ℂ) * (P * (starRingEnd ℂ) (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))) =
      P * (starRingEnd ℂ) ((∫ u in a..b, Complex.exp ((g u : ℂ) * Complex.I)) -
        (A : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)) := by
    simp only [map_sub, map_mul, Complex.conj_ofReal]
    ring
  rw [hfactor, norm_mul, hPn, one_mul, Complex.norm_conj]
  exact hh

/-- The right-hand bound applies to the original closed-interval phase by the explicit curvature extension. -/
theorem stationary_right_uniform {f : ℝ → ℝ} {a b ℓ ν A : ℝ}
    (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) (hslope : deriv f a ≤ ν)
    (hA : 0 ≤ A) (hAmax : A ≤ 1 / (2 * Real.sqrt ℓ)) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      (A : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ))‖ ≤
      0.928 / Real.sqrt ℓ := by
  let F := extendedPhase f a b hab a
  have hFd : Differentiable ℝ F := fun u => (extendedPhase_hasDerivAt hab hfc a u).differentiableAt
  have hF : deriv F = extendedSlope f a b hab a := funext fun u => (extendedPhase_hasDerivAt hab hfc a u).deriv
  have hFd' : Differentiable ℝ (deriv F) := by
    rw [hF]
    exact fun u => (extendedSlope_hasDerivAt hab hfc a u).differentiableAt
  have hFe (u : ℝ) (hu : u ∈ Set.Icc a b) : F u = f u :=
    extendedPhase_eq hab (Set.left_mem_Icc.mpr hab) hu hf hf' hfc
  have h := stationary_right_uniform_global (ν := ν) hab hℓ hFd hFd'
    (fun u hu => by
      rw [extendedPhase_second_deriv hab hfc a u, extendedCurvature_eq hab hu]
      exact hcurv u hu) (by
        rw [hF, extendedSlope_eq hab (Set.left_mem_Icc.mpr hab) (Set.left_mem_Icc.mpr hab) hf' hfc]
        exact hslope) hA hAmax
  have he : (∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((F u - ν * u : ℝ) : ℂ))) =
      ∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact congrArg (fun v : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((v - ν * u : ℝ) : ℂ))) (hFe u hu)
  rw [he, hFe a (Set.left_mem_Icc.mpr hab)] at h
  exact h

/-- Reflection gives the same uniform half stationary error on the left of the critical point. -/
theorem stationary_left_uniform {f : ℝ → ℝ} {a b ℓ ν A : ℝ}
    (hab : a ≤ b) (hℓ : 0 < ℓ)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) (hslope : ν ≤ deriv f b)
    (hA : 0 ≤ A) (hAmax : A ≤ 1 / (2 * Real.sqrt ℓ)) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      (A : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((f b - ν * b - 1 / 8 : ℝ) : ℂ))‖ ≤
      0.928 / Real.sqrt ℓ := by
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
  have hgc : ContinuousOn (deriv (deriv g)) (Set.Icc (-b) (-a)) := by
    have h := hfc.comp continuous_neg.continuousOn (fun u hu => hmap hu)
    exact h.congr (fun u hu => (hdg u hu).deriv)
  have h := stationary_right_uniform (ν := -ν) (by linarith : -b ≤ -a) hℓ hgd
    (fun u hu => (hdg u hu).differentiableAt) hgc
    (fun u hu => by rw [(hdg u hu).deriv]; exact hcurv (-u) (hmap hu))
    (by rw [hg]; dsimp only; rw [neg_neg]; linarith) hA hAmax
  have he (u : ℝ) : g u - (-ν) * u = f (-u) - ν * (-u) := by dsimp [g]; ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_comp_neg
    (fun u => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))), neg_neg] at h
  simpa only [neg_neg] using h

/-- Both sides of an actual stationary point give the uniform 1.856 replacement error without any third-derivative premise. -/
theorem stationary_uniform_bound {f : ℝ → ℝ} {a b c ℓ ν : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤ 1.856 / Real.sqrt ℓ := by
  have hcc : c ∈ Set.Icc a b := ⟨ha, hb⟩
  have hk : ℓ ≤ |deriv (deriv f) c| := by
    have hh := hcurv c hcc
    rw [abs_of_neg (hh.trans_lt (neg_neg_of_pos hℓ))]
    linarith
  let A := 1 / (2 * Real.sqrt |deriv (deriv f) c|)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAmax : A ≤ 1 / (2 * Real.sqrt ℓ) := by
    apply one_div_le_one_div_of_le (by positivity : 0 < 2 * Real.sqrt ℓ)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hk) (by norm_num)
  have hleft : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hb
  have hright : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc ha le_rfl
  have hl := stationary_left_uniform (ν := ν) ha hℓ (fun u hu => hf u (hleft hu))
    (fun u hu => hf' u (hleft hu)) (hfc.mono hleft) (fun u hu => hcurv u (hleft hu)) hc.ge hA hAmax
  have hr := stationary_right_uniform (ν := ν) hb hℓ (fun u hu => hf u (hright hu))
    (fun u hu => hf' u (hright hu)) (hfc.mono hright) (fun u hu => hcurv u (hright hu)) hc.le hA hAmax
  let K : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))
  let P : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ))
  have hK : ContinuousOn K (Set.Icc a b) := by
    have hcont : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
    dsimp [K]
    fun_prop
  have hi := intervalIntegral.integral_add_adjacent_intervals
    ((hK.mono hleft).intervalIntegrable_of_Icc (μ := volume) ha)
    ((hK.mono hright).intervalIntegrable_of_Icc (μ := volume) hb)
  have he : (∫ u in a..b, K u) - P / (Real.sqrt |deriv (deriv f) c| : ℂ) =
      ((∫ u in a..c, K u) - (A : ℂ) * P) + ((∫ u in c..b, K u) - (A : ℂ) * P) := by
    rw [← hi]
    dsimp [A]
    push_cast
    ring
  change ‖(∫ u in a..b, K u) - P / (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hl hr).trans_eq (by ring))

end DhimanKadiriQuesadaHerrera2026
