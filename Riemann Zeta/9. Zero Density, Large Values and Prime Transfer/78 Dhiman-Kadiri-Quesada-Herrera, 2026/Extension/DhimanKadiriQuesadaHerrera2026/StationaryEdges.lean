import DhimanKadiriQuesadaHerrera2026.HalfStationary
import DhimanKadiriQuesadaHerrera2026.StationaryUniform

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- The uniform one-sided estimate consumes the actual half stationary amplitude. -/
theorem stationary_right_half_uniform {f : ℝ → ℝ} {a b ν ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (hcritical : deriv f a = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) a| : ℂ) / 2‖ ≤ 0.928 / Real.sqrt ℓ := by
  have hk : ℓ ≤ |deriv (deriv f) a| := by
    have hh := hcurv a (Set.left_mem_Icc.mpr hab)
    rw [abs_of_neg (hh.trans_lt (neg_neg_of_pos hℓ))]
    linarith
  let A := 1 / (2 * Real.sqrt |deriv (deriv f) a|)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAmax : A ≤ 1 / (2 * Real.sqrt ℓ) := by
    apply one_div_le_one_div_of_le (by positivity : 0 < 2 * Real.sqrt ℓ)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hk) (by norm_num)
  have h := stationary_right_uniform hab hℓ hf hf' hfc hcurv hcritical.le hA hAmax
  have he : (A : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((f a - ν * a - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) a| : ℂ) / 2 := by dsimp [A]; push_cast; ring
  rw [he] at h
  exact h

/-- The uniform one-sided estimate consumes the actual half stationary amplitude. -/
theorem stationary_left_half_uniform {f : ℝ → ℝ} {a b ν ℓ : ℝ}
    (hℓ : 0 < ℓ) (hab : a ≤ b) (hcritical : deriv f b = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f b - ν * b - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) b| : ℂ) / 2‖ ≤ 0.928 / Real.sqrt ℓ := by
  have hk : ℓ ≤ |deriv (deriv f) b| := by
    have hh := hcurv b (Set.right_mem_Icc.mpr hab)
    rw [abs_of_neg (hh.trans_lt (neg_neg_of_pos hℓ))]
    linarith
  let A := 1 / (2 * Real.sqrt |deriv (deriv f) b|)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAmax : A ≤ 1 / (2 * Real.sqrt ℓ) := by
    apply one_div_le_one_div_of_le (by positivity : 0 < 2 * Real.sqrt ℓ)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hk) (by norm_num)
  have h := stationary_left_uniform hab hℓ hf hf' hfc hcurv hcritical.ge hA hAmax
  have he : (A : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((f b - ν * b - 1 / 8 : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((f b - ν * b - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) b| : ℂ) / 2 := by dsimp [A]; push_cast; ring
  rw [he] at h
  exact h

/-- One uniform half error replaces the near-endpoint gap while the other half keeps its exact nonlinear coefficient. -/
theorem stationary_error_drop_left {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        0.928 / Real.sqrt ℓ + stationaryEndpointCap ℓ (deriv f b - ν) := by
  have hleft : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hb
  have hright : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc ha le_rfl
  have hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) :=
    fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  have hl := stationary_left_half_uniform hℓ ha hc (fun u hu => hf u (hleft hu))
    (fun u hu => hf' u (hleft hu)) (hfc.mono hleft) (fun u hu => hcurv u (hleft hu))
  have hr := stationary_right_phase_bound hℓ hb hc (fun u hu => hf u (hright hu))
    (fun u hu => hf' u (hright hu)) (fun u hu => hf'' u (hright hu))
    (fun u hu => hcurv u (hright hu)) (fun u hu => hD u (hright hu))
  let K : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))
  let P : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
    (Real.sqrt |deriv (deriv f) c| : ℂ)
  have hK : ContinuousOn K (Set.Icc a b) := by
    have hcont : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
    dsimp [K]
    fun_prop
  have hi := intervalIntegral.integral_add_adjacent_intervals
    ((hK.mono hleft).intervalIntegrable_of_Icc (μ := volume) ha)
    ((hK.mono hright).intervalIntegrable_of_Icc (μ := volume) hb)
  have he : (∫ u in a..b, K u) - P =
      ((∫ u in a..c, K u) - P / 2) + ((∫ u in c..b, K u) - P / 2) := by rw [← hi]; ring
  change ‖(∫ u in a..b, K u) - P‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hl hr).trans_eq (by ring))

/-- One uniform half error replaces the near-endpoint gap while the other half keeps its exact nonlinear coefficient. -/
theorem stationary_error_drop_right {f : ℝ → ℝ} {a b c ν D ℓ : ℝ}
    (hℓ : 0 < ℓ) (ha : a ≤ c) (hb : c ≤ b) (hc : deriv f c = ν)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∫ u in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))) -
      Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
        (Real.sqrt |deriv (deriv f) c| : ℂ)‖ ≤
      ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) / 2 +
        0.928 / Real.sqrt ℓ + stationaryEndpointCap ℓ (deriv f a - ν) := by
  have hleft : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hb
  have hright : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc ha le_rfl
  have hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) :=
    fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  have hl := stationary_left_phase_bound hℓ ha hc (fun u hu => hf u (hleft hu))
    (fun u hu => hf' u (hleft hu)) (fun u hu => hf'' u (hleft hu))
    (fun u hu => hcurv u (hleft hu)) (fun u hu => hD u (hleft hu))
  have hr := stationary_right_half_uniform hℓ hb hc (fun u hu => hf u (hright hu))
    (fun u hu => hf' u (hright hu)) (hfc.mono hright) (fun u hu => hcurv u (hright hu))
  let K : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((f u - ν * u : ℝ) : ℂ))
  let P : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((f c - ν * c - 1 / 8 : ℝ) : ℂ)) /
    (Real.sqrt |deriv (deriv f) c| : ℂ)
  have hK : ContinuousOn K (Set.Icc a b) := by
    have hcont : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
    dsimp [K]
    fun_prop
  have hi := intervalIntegral.integral_add_adjacent_intervals
    ((hK.mono hleft).intervalIntegrable_of_Icc (μ := volume) ha)
    ((hK.mono hright).intervalIntegrable_of_Icc (μ := volume) hb)
  have he : (∫ u in a..b, K u) - P =
      ((∫ u in a..c, K u) - P / 2) + ((∫ u in c..b, K u) - P / 2) := by rw [← hi]; ring
  change ‖(∫ u in a..b, K u) - P‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hl hr).trans_eq (by ring))

end DhimanKadiriQuesadaHerrera2026
