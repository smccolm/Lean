import DhimanKadiriQuesadaHerrera2026.HalfStationary

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- The clamped curvature is exactly the left endpoint curvature before the source interval. -/
theorem extendedCurvature_left {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) :
    extendedCurvature f a b hab x = deriv (deriv f) a := by
  simp only [extendedCurvature, Set.projIcc_of_le_left hab hx]

/-- The slope extension is affine on the left exterior interval. -/
theorem extendedSlope_left {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) :
    extendedSlope f a b hab a x = deriv f a + deriv (deriv f) a * (x - a) := by
  unfold extendedSlope
  have hi : (∫ u in a..x, extendedCurvature f a b hab u) = ∫ _ in a..x, deriv (deriv f) a := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_ge hx] at hu
    exact extendedCurvature_left hab hu.2
  rw [hi, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- The actual phase extension is quadratic to the left of its source interval. -/
theorem extendedPhase_left {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) :
    extendedPhase f a b hab a x =
      f a + deriv f a * (x - a) + deriv (deriv f) a * (x - a) ^ 2 / 2 := by
  unfold extendedPhase
  have hi : (∫ u in a..x, extendedSlope f a b hab a u) =
      ∫ u in a..x, deriv f a + deriv (deriv f) a * (u - a) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_ge hx] at hu
    exact extendedSlope_left hab hu.2
  rw [hi]
  have hd (u : ℝ) : HasDerivAt
      (fun v : ℝ => deriv f a * (v - a) + deriv (deriv f) a * (v - a) ^ 2 / 2)
      (deriv f a + deriv (deriv f) a * (u - a)) u := by
    convert (((hasDerivAt_id u).sub_const a).const_mul (deriv f a)).add
      ((((hasDerivAt_id u).sub_const a).pow 2).const_mul (deriv (deriv f) a) |>.div_const 2) using 1
    simp only [id_eq]
    ring
  have hint : IntervalIntegrable (fun u : ℝ => deriv f a + deriv (deriv f) a * (u - a)) volume a x :=
    (by fun_prop : Continuous (fun u : ℝ => deriv f a + deriv (deriv f) a * (u - a))).intervalIntegrable a x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hint]
  ring

/-- A virtual stationary point in the quadratic extension halves the near-endpoint reciprocal loss. -/
theorem exterior_integral_half_recip {f : ℝ → ℝ} {a b ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (hν : deriv f a < ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        stationaryEndpointCap ℓ (deriv f b - ν) + 1 / (2 * Real.pi * (ν - deriv f a)) := by
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a haa)
  have hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) :=
    fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  let F := extendedPhase f a b hab a
  let κ := -deriv (deriv f) a
  let η := (ν - deriv f a) / κ
  let c := a - η
  have hκ : 0 < κ := by dsimp [κ]; linarith [hcurv a haa]
  have hη : 0 < η := div_pos (sub_pos.mpr hν) hκ
  have hca : c ≤ a := by dsimp [c]; linarith
  have hce : c + η = a := by dsimp [c]; ring
  have hFd (u : ℝ) : HasDerivAt F (extendedSlope f a b hab a u) u := extendedPhase_hasDerivAt hab hfc a u
  have hFd_eq : deriv F = extendedSlope f a b hab a := funext fun u => (hFd u).deriv
  have hFdd (u : ℝ) : DifferentiableAt ℝ (deriv F) u := by
    rw [hFd_eq]
    exact (extendedSlope_hasDerivAt hab hfc a u).differentiableAt
  have hF2 (u : ℝ) : deriv (deriv F) u = extendedCurvature f a b hab u :=
    extendedPhase_second_deriv hab hfc a u
  have hFκ : deriv (deriv F) c = -κ := by
    rw [hF2, extendedCurvature_left hab hca]
    simp only [κ, neg_neg]
  have hstat : deriv F c = ν := by
    rw [(hFd c).deriv, extendedSlope_left hab hca]
    rw [show deriv (deriv f) a = -κ by simp only [κ, neg_neg]]
    dsimp only [c, η]
    field_simp
    ring
  have hFL (u : ℝ) : deriv (deriv F) u ≤ -ℓ := by
    rw [hF2]
    exact hcurv _ (Set.projIcc a b hab u).property
  have hLip (u : ℝ) : |deriv (deriv F) u - deriv (deriv F) c| ≤ D * |u - c| := by
    rw [hF2, hF2]
    exact extendedCurvature_lipschitz hab hf'' hD u c
  have hmain := stationary_right_lipschitz_global hDn hℓ (hca.trans hab) hstat
    (fun u => (hFd u).differentiableAt) hFdd hFL hLip
  have hflat (u : ℝ) (hu : u ∈ Set.Icc (c - η) (c + η)) :
      |deriv (deriv F) u - deriv (deriv F) c| ≤ (0 : ℝ) * |u - c| := by
    have hua : u ≤ a := by linarith [hu.2]
    rw [hF2, hF2, extendedCurvature_left hab hua, extendedCurvature_left hab hca]
    simp only [sub_self, abs_zero, zero_mul, le_refl]
  have hnear := stationary_half_fresnel_lipschitz hη (by rw [hFκ]; linarith : deriv (deriv F) c < 0)
    hstat (fun u _ => (hFd u).differentiableAt) (fun u _ => hFdd u) hflat
  rw [hce, hFκ, abs_neg, abs_of_pos hκ] at hnear
  norm_num only [zero_mul, zero_div, zero_add] at hnear
  have hden : κ * η = ν - deriv f a := by dsimp [η]; field_simp
  have hrecip : 1 / (2 * Real.pi * κ * η) = 1 / (2 * Real.pi * (ν - deriv f a)) := by
    rw [mul_assoc, hden]
  rw [hrecip] at hnear
  have hFderiv : deriv F b = deriv f b := by
    rw [(hFd b).deriv]
    exact extendedSlope_eq hab haa hbb hf' hfc
  rw [hFderiv, hFκ, abs_neg, abs_of_pos hκ] at hmain
  let K : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((F u - ν * u : ℝ) : ℂ))
  let P := Complex.exp (2 * Real.pi * Complex.I * ((F c - ν * c - 1 / 8 : ℝ) : ℂ)) / (Real.sqrt κ : ℂ) / 2
  have hK : Continuous K := by
    have hFc : Continuous F := (show Differentiable ℝ F from fun u => (hFd u).differentiableAt).continuous
    dsimp [K]
    fun_prop
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hK.intervalIntegrable (μ := volume) c a) (hK.intervalIntegrable a b)
  have he : (∫ u in a..b, K u) = ((∫ u in c..b, K u) - P) - ((∫ u in c..a, K u) - P) := by rw [← hi]; ring
  have hsum := (norm_sub_le ((∫ u in c..b, K u) - P) ((∫ u in c..a, K u) - P)).trans (add_le_add hmain hnear)
  rw [← he] at hsum
  have hFe (u : ℝ) (hu : u ∈ Set.Icc a b) : F u = f u := extendedPhase_eq hab haa hu hf hf' hfc
  have heq : (∫ u in a..b, K u) =
      ∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    dsimp [K]
    rw [hFe u hu]
  rw [heq] at hsum
  exact hsum

end DhimanKadiriQuesadaHerrera2026
