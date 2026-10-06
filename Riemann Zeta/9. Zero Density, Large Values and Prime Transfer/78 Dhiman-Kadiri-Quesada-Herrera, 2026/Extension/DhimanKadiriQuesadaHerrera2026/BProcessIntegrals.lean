import DhimanKadiriQuesadaHerrera2026.StationaryLogCaps

namespace DhimanKadiriQuesadaHerrera2026

/-- For at least two positive frequencies, the actual full stationary transform satisfies all three printed stationary-error constants. -/
theorem stationary_full_sum_large {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
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
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 := by
  let M := ⌊deriv f a⌋₊
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  let P : ℕ → ℂ := fun ν => Complex.exp (2 * Real.pi * Complex.I *
    ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) / (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)
  let E : ℕ → ℂ := fun ν => I ν - P ν
  let A : ℕ → ℝ := fun ν => stationaryEndpointCap ℓ (deriv f a - (ν : ℝ))
  let B : ℕ → ℝ := fun ν => stationaryEndpointCap ℓ (deriv f b - (ν : ℝ))
  let r := (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ
  change 2 ≤ M at hM
  change ∀ ν ∈ Finset.Icc 1 M, _ at hξ
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hx1 := hξ 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hxM := hξ M (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have h1 : ‖E 1‖ ≤ r / 2 + 0.928 / Real.sqrt ℓ + A 1 :=
    stationary_error_drop_right hℓ hx1.1.1 hx1.1.2 hx1.2 hf hf' hf'' hcurv hD
  have hlast : ‖E M‖ ≤ r / 2 + 0.928 / Real.sqrt ℓ + B M :=
    stationary_error_drop_left hℓ hxM.1.1 hxM.1.2 hxM.2 hf hf' hf'' hcurv hD
  have hmid (ν : ℕ) (hν : ν ∈ Finset.Icc 2 (M - 1)) : ‖E ν‖ ≤ r + A ν + B ν := by
    have hn := Finset.mem_Icc.mp hν
    have hx := hξ ν (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    exact stationary_phase_gap_bound hℓ hx.1.1 hx.1.2 hx.2 hf hf' hf'' hcurv hD
  have hsum := norm_sum_stationary_edges hM E A B r (0.928 / Real.sqrt ℓ) h1 hlast hmid
  have hz : ‖I 0‖ ≤ 0.6715 / Real.sqrt ℓ := by
    simpa only [I, Nat.cast_zero, zero_mul, sub_zero] using
      kershner_zero_frequency hab hℓ hf hf' hf'' hanti hαpos hlower
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
  have hβα : deriv f b ≤ deriv f a := hanti.antitoneOn haa hbb hab.le
  have hβ : 0 ≤ deriv f a := hαpos.trans hβα
  have hfar := stationary_far_caps_log (ℓ := ℓ) hM hα (Nat.floor_le hβ)
  have hcount := interior_frequency_card_le hα hβα
  have hcard : (Finset.Icc 1 (M - 1)).card = M - 1 := by rw [Nat.card_Icc]; omega
  change ((Finset.Icc 1 (M - 1)).card : ℝ) ≤ _ at hcount
  rw [hcard] at hcount
  have hw := derivative_range_le_curvature hab.le hf' hupper
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a haa)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hscale : ((M - 1 : ℕ) : ℝ) * r ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) := by
    apply (mul_le_mul_of_nonneg_right (hcount.trans hw) hr).trans_eq
    dsimp [r]
    field_simp
  have hs : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have he : (∑ ν ∈ Finset.Icc 0 M, I ν) - (∑ ν ∈ Finset.Icc 1 M, P ν) =
      I 0 + ∑ ν ∈ Finset.Icc 1 M, E ν := by
    dsimp [E]
    rw [hs, Finset.sum_insert (by simp), Finset.sum_sub_distrib]
    ring
  change ‖(∑ ν ∈ Finset.Icc 0 M, I ν) - (∑ ν ∈ Finset.Icc 1 M, P ν)‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans ((add_le_add hz hsum).trans ?_)
  have hconstant : 0.6715 / Real.sqrt ℓ + 2 * (0.928 / Real.sqrt ℓ) ≤ 2.686 / Real.sqrt ℓ := by
    calc
      _ = 2.5275 / Real.sqrt ℓ := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg ℓ)
  change (∑ ν ∈ Finset.Icc 1 (M - 1), A ν) + (∑ ν ∈ Finset.Icc 2 M, B ν) ≤ _ at hfar
  linarith

/-- The actual stationary Fourier transform obeys the printed error constants in every frequency-count case. -/
theorem stationary_full_sum_bound {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hlen : 1 ≤ b - a)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 := by
  by_cases hM : 2 ≤ ⌊deriv f a⌋₊
  · exact stationary_full_sum_large ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hupper hD
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hfcc : ContinuousOn (deriv (deriv f)) (Set.Icc a b) :=
    fun u hu => (hf'' u hu).continuousAt.continuousWithinAt
  have hw : ℓ ≤ deriv f a - deriv f b := by
    have h := stationary_derivative_drop hf' hcurv haa hbb hab.le
    nlinarith
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a haa)
  have hh₂ : 0 ≤ h₂ := by
    have hh := (hlower a haa).trans (hupper a haa)
    nlinarith
  have hnonlin : 0 ≤ (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) *
      h₂ * D ^ (1 / 3 : ℝ) * (b - a) := by positivity
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  let P : ℕ → ℂ := fun ν => Complex.exp (2 * Real.pi * Complex.I *
    ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) / (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)
  have hz : ‖I 0‖ ≤ 0.6715 / Real.sqrt ℓ := by
    simpa only [I, Nat.cast_zero, zero_mul, sub_zero] using
      kershner_zero_frequency hab hℓ hf hf' hf'' hanti hαpos hlower
  change ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, I ν) -
    (∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, P ν)‖ ≤ _
  by_cases hzero : ⌊deriv f a⌋₊ = 0
  · simp only [hzero, Finset.Icc_self, Finset.sum_singleton, show Finset.Icc 1 0 = ∅ by decide,
      Finset.sum_empty, sub_zero]
    have hsmall := stationary_small_width_absorb hℓ hw
    have hpre : 0.6715 / Real.sqrt ℓ ≤ 1.856 / Real.sqrt ℓ + 2 / Real.pi := by
      have hh := div_le_div_of_nonneg_right (by norm_num : (0.6715 : ℝ) ≤ 1.856) (Real.sqrt_nonneg ℓ)
      have hp : 0 ≤ 2 / Real.pi := by positivity
      linarith
    linarith
  · have hone : ⌊deriv f a⌋₊ = 1 := by omega
    have hx := hξ 1 (by simp [hone])
    have hstation : ‖I 1 - P 1‖ ≤ 1.856 / Real.sqrt ℓ :=
      stationary_uniform_bound hℓ hx.1.1 hx.1.2 hx.2 hf hf' hfcc hcurv
    have hs : Finset.Icc 0 1 = {0, 1} := by decide
    simp only [hone, hs, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), Finset.Icc_self,
      Finset.sum_singleton]
    rw [add_sub_assoc]
    have hnorm := (norm_add_le (I 0) (I 1 - P 1)).trans (add_le_add le_rfl hstation)
    by_cases hwide : 1 / 2 ≤ deriv f a - deriv f b
    · have hwider := stationary_large_width_absorb (ℓ := ℓ) hwide
      have he : 0.6715 / Real.sqrt ℓ + 1.856 / Real.sqrt ℓ = 2.5275 / Real.sqrt ℓ := by ring
      linarith
    · have hβ : 1 ≤ deriv f a := Nat.floor_pos.mp (by omega)
      have hαhalf : 1 / 2 < deriv f b := by linarith
      have hz' : ‖I 0‖ ≤ 2 / Real.pi := by
        have h := norm_shifted_integral_positive (ν := 0) hab.le hf hfc hanti.antitoneOn
          (by linarith : 0 < deriv f b)
        simp only [sub_zero, zero_mul] at h
        have hp := one_div_le_one_div_of_le (by positivity : 0 < Real.pi * (1 / 2))
          (mul_le_mul_of_nonneg_left hαhalf.le Real.pi_pos.le)
        have he : 1 / (Real.pi * (1 / 2)) = 2 / Real.pi := by ring
        simpa only [I, Nat.cast_zero, zero_mul, sub_zero, he] using h.trans hp
      have hsmall := stationary_small_width_absorb hℓ hw
      linarith

/-- The derivative hypotheses construct every actual stationary point and the complete Fourier-to-stationary estimate. -/
theorem exists_full_stationary_transform {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hlen : 1 ≤ b - a)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 := by
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
  exact ⟨ξ, hξ, stationary_full_sum_bound ξ hab hℓ hαpos hα hlen hξ hf hf' hf'' hanti hlower hupper hD⟩

/-- Distinct increasing half-integer endpoints have interval length at least one. -/
theorem half_integer_length_ge_one {a b : ℝ} (hab : a < b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    1 ≤ b - a := by
  obtain ⟨j, rfl⟩ := hah
  obtain ⟨k, rfl⟩ := hbh
  have hjk : (j : ℝ) < k := by linarith
  have hn : j + 1 ≤ k := by exact Int.add_one_le_iff.mpr (by exact_mod_cast hjk)
  have hr : (j : ℝ) + 1 ≤ k := by exact_mod_cast hn
  linarith

/-- The half-integer source geometry and scales give the exact full stationary error, before discrete Poisson transfer. -/
theorem exists_source_stationary_transform {f : ℝ → ℝ} {a b ℓ₂ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ₂ : 0 < ℓ₂) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ₂ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ₂)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ₂ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 := by
  obtain ⟨ξ, hξ, hbound⟩ := exists_full_stationary_transform hab hℓ₂ hαpos.le hα
    (half_integer_length_ge_one hab hah hbh) hf hf' hf'' hanti hlower hupper hD
  refine ⟨ξ, hξ, hbound.trans_eq ?_⟩
  rw [Real.mul_rpow hh₃ hℓ₃]
  ring

end DhimanKadiriQuesadaHerrera2026
