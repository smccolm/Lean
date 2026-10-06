import DhimanKadiriQuesadaHerrera2026.ExteriorPhase
import DhimanKadiriQuesadaHerrera2026.PoissonCutoff

namespace DhimanKadiriQuesadaHerrera2026

/-- The enlarged Fourier sum spends only the available half nonlinear error on the exterior frequency. -/
theorem stationary_sum_next_half_gap {f : ℝ → ℝ} {a b D ℓ h₂ : ℝ} (ξ : ℕ → ℝ)
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 ≤ deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊) (hδ : (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a ≤ 1 / 2)
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
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
        1 / (Real.pi * (⌊deriv f a⌋₊ : ℝ)) +
        1 / (2 * Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a)) := by
  let M := ⌊deriv f a⌋₊
  let r := (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * D ^ (1 / 3 : ℝ) / ℓ
  have hs := stationary_full_sum_counted ξ hab hℓ hαpos hα hM hξ hf hf' hf'' hanti hlower hD
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  have he := exterior_integral_half_recip hℓ hab.le (Nat.lt_floor_add_one (deriv f a)) hf hf' hf'' hcurv hD
  have hMn : (0 : ℝ) < M := by exact_mod_cast (show 0 < M from lt_of_lt_of_le (by norm_num) hM)
  have hcap : stationaryEndpointCap ℓ (deriv f b - ((M : ℝ) + 1)) ≤ 1 / (Real.pi * (M : ℝ)) := by
    have hn : deriv f b - ((M : ℝ) + 1) < 0 := by linarith
    apply (stationaryEndpointCap_le_recip ℓ hn.ne).trans
    rw [abs_of_neg hn]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [Real.pi_pos])
  have hcount : ((M - 1 : ℕ) : ℝ) + 1 / 2 ≤ deriv f a - deriv f b := by
    rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
    change (M : ℝ) + 1 - deriv f a ≤ 1 / 2 at hδ
    linarith
  have hw := derivative_range_le_curvature hab.le hf' hupper
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a (Set.left_mem_Icc.mpr hab.le))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hscale : (((M - 1 : ℕ) : ℝ) + 1 / 2) * r ≤
      (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) := by
    apply (mul_le_mul_of_nonneg_right (hcount.trans hw) hr).trans_eq
    dsimp [r]
    field_simp
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  let P := ∑ ν ∈ Finset.Icc 1 M,
    Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
      (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)
  have he' : ‖I (M + 1)‖ ≤ r / 2 + 1 / (Real.pi * (M : ℝ)) +
      1 / (2 * Real.pi * ((M : ℝ) + 1 - deriv f a)) := by
    simp only [I, Nat.cast_add, Nat.cast_one]
    exact he.trans (add_le_add (add_le_add le_rfl hcap) le_rfl)
  have ht := (norm_add_le ((∑ ν ∈ Finset.Icc 0 M, I ν) - P) (I (M + 1))).trans (add_le_add hs he')
  change ‖(∑ ν ∈ Finset.Icc 0 (M + 1), I ν) - P‖ ≤ _
  rw [Finset.sum_Icc_succ_top (by omega), add_sub_right_comm]
  apply ht.trans
  change 2.5275 / Real.sqrt ℓ + ((M - 1 : ℕ) : ℝ) * r + _ + _ + (r / 2 + _ + _) ≤ _
  nlinarith only [hscale]

/-- An actual general-phase discrete B-process uses the half reciprocal endpoint loss with no extra curvature monotonicity premise. -/
theorem exists_b_process_half_gap {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊) (hδ : (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a ≤ 1 / 2)
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
      2.5275 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 2 / Real.pi +
        1 / (Real.pi * (⌊deriv f a⌋₊ : ℝ)) +
        1 / (2 * Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a)) +
      (1 / Real.pi) * (Real.log ((⌊deriv f a⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊deriv f a⌋₊ : ℝ) + 2)) -
          (Complex.digamma ((⌊deriv f a⌋₊ : ℝ) + 2 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a)) +
          Real.log 2 + 1 / ((⌊deriv f a⌋₊ : ℝ) + 1)) := by
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hr := constant_weight_partIRegularity hab hf hfc
    (fun u hu => hαpos.trans_le (hanti.antitoneOn hu (Set.right_mem_Icc.mpr hab.le) hu.2))
    hanti.antitoneOn
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
  have hs := stationary_sum_next_half_gap ξ hab hℓ hαpos.le hα hM hδ hξ hf hf' hf'' hanti hlower hupper hD
  have hp := constant_partI_cutoff (M := ⌊deriv f a⌋₊ + 1) hr (by omega)
    (by push_cast; linarith [Nat.lt_floor_add_one (deriv f a)] : deriv f a < ((⌊deriv f a⌋₊ + 1 : ℕ) : ℝ) + 1) hah hbh
  have hn : (⌊deriv f a⌋₊ : ℝ) + 1 + 1 = (⌊deriv f a⌋₊ : ℝ) + 2 := by ring
  simp only [Nat.cast_add, Nat.cast_one, hn] at hp
  refine ⟨ξ, hξ, ?_⟩
  have ht := (norm_add_le _ _).trans (add_le_add hp hs)
  simp only [sub_add_sub_cancel] at ht
  exact ht.trans_eq (add_comm _ _)

end DhimanKadiriQuesadaHerrera2026
