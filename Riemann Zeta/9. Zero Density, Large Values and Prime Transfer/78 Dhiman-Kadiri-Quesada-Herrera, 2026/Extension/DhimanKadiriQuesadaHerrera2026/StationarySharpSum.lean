import DhimanKadiriQuesadaHerrera2026.BProcessIntegrals

namespace DhimanKadiriQuesadaHerrera2026

/-- The far-end cap sum retains the exact harmonic constant 2/pi. -/
theorem stationary_far_caps_sharp {α β ℓ : ℝ} {M : ℕ} (hM : 2 ≤ M)
    (hα : α < 1) (hβ : (M : ℝ) ≤ β) :
    (∑ ν ∈ Finset.Icc 1 (M - 1), stationaryEndpointCap ℓ (β - (ν : ℝ))) +
      (∑ ν ∈ Finset.Icc 2 M, stationaryEndpointCap ℓ (α - (ν : ℝ))) ≤
        2 / Real.pi * (1 + Real.log (β - α)) := by
  have hM1 : 1 ≤ M := by omega
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub hM1, Nat.cast_one]
  have hleft : (∑ ν ∈ Finset.Icc 1 (M - 1), stationaryEndpointCap ℓ (β - (ν : ℝ))) ≤
      1 / Real.pi * ∑ ν ∈ Finset.Icc 1 (M - 1), 1 / (ν : ℝ) := by
    have he : (∑ ν ∈ Finset.Icc 1 (M - 1), 1 / ((M : ℝ) - (ν : ℝ))) =
        ∑ ν ∈ Finset.Icc 1 (M - 1), 1 / (ν : ℝ) := by
      have h := reciprocal_integer_reflect (M - 1)
      rw [hcast] at h
      simpa only [sub_add_cancel] using h
    rw [← he, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ν hν
    have hn : (ν : ℝ) ≤ (M : ℝ) - 1 := by exact_mod_cast (Finset.mem_Icc.mp hν).2
    have hp : 0 < β - (ν : ℝ) := by linarith
    apply (stationaryEndpointCap_le_recip ℓ hp.ne').trans
    rw [abs_of_pos hp]
    have hi := one_div_le_one_div_of_le (by linarith : 0 < (M : ℝ) - (ν : ℝ))
      (by linarith : (M : ℝ) - (ν : ℝ) ≤ β - (ν : ℝ))
    simpa only [one_div, mul_inv_rev, mul_comm] using
      mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 / Real.pi)
  have hright : (∑ ν ∈ Finset.Icc 2 M, stationaryEndpointCap ℓ (α - (ν : ℝ))) ≤
      1 / Real.pi * ∑ ν ∈ Finset.Icc 1 (M - 1), 1 / (ν : ℝ) := by
    rw [← reciprocal_lower_shift M, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ν hν
    have hn : (2 : ℝ) ≤ ν := by exact_mod_cast (Finset.mem_Icc.mp hν).1
    have hp : α - (ν : ℝ) < 0 := by linarith
    apply (stationaryEndpointCap_le_recip ℓ hp.ne).trans
    rw [abs_of_neg hp, neg_sub]
    have hi := one_div_le_one_div_of_le (by linarith : 0 < (ν : ℝ) - 1)
      (by linarith : (ν : ℝ) - 1 ≤ (ν : ℝ) - α)
    simpa only [one_div, mul_inv_rev, mul_comm] using
      mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 / Real.pi)
  have hlog : Real.log (M - 1 : ℕ) ≤ Real.log (β - α) := by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < M - 1))
    rw [hcast]
    linarith
  have hh := (real_harmonic_sum_le (M - 1)).trans (add_le_add le_rfl hlog)
  have hs := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 / Real.pi)
  simp only [div_eq_mul_inv] at hleft hright hs ⊢
  nlinarith

/-- The full stationary sum keeps the exact count of nonlinear errors before conversion to interval length. -/
theorem stationary_full_sum_counted {f : ℝ → ℝ} {a b D ℓ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
    (hξ : ∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊, ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ))
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) :
    ‖(∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.5275 / Real.sqrt ℓ +
        ((⌊deriv f a⌋₊ - 1 : ℕ) : ℝ) *
          ((2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi := by
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
  have hfar := stationary_far_caps_sharp (ℓ := ℓ) hM hα (Nat.floor_le hβ)
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
  have hconstant : 0.6715 / Real.sqrt ℓ + 2 * (0.928 / Real.sqrt ℓ) = 2.5275 / Real.sqrt ℓ := by ring
  change (∑ ν ∈ Finset.Icc 1 (M - 1), A ν) + (∑ ν ∈ Finset.Icc 2 M, B ν) ≤ _ at hfar
  linarith

/-- The many-frequency stationary estimate retains its unused numerical margin. -/
theorem stationary_full_sum_sharp {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
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
      2.5275 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi := by
  have hs := stationary_full_sum_counted ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hD
  let M := ⌊deriv f a⌋₊
  let r := (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ
  have haa : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  have hbb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab.le
  have hβα : deriv f b ≤ deriv f a := hanti.antitoneOn haa hbb hab.le
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
  exact hs.trans (add_le_add (add_le_add (add_le_add le_rfl hscale) le_rfl) le_rfl)

end DhimanKadiriQuesadaHerrera2026
