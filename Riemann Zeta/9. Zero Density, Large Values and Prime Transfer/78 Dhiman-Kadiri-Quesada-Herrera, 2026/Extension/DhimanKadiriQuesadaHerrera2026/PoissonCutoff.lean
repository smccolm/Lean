import DhimanKadiriQuesadaHerrera2026.BProcessPoisson
import DhimanKadiriQuesadaHerrera2026.StationarySharpSum

namespace DhimanKadiriQuesadaHerrera2026

/-- The accepted weighted Poisson estimate permits any positive upper cutoff above the derivative. -/
theorem partI_half_arbitrary_cutoff {f g : ℝ → ℝ} {a b : ℝ} {M : ℕ}
    (h : PartIRegularity f g a b) (hM : 1 ≤ M) (hβ : deriv f a < (M : ℝ) + 1)
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M‖ ≤
      (partICoefficient f g a / deriv f a) *
        (Real.log ((M : ℝ) + 1) - 1 / (2 * ((M : ℝ) + 1)) -
          (Complex.digamma ((M : ℝ) + 1 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a))) +
        (g a + g b) / (2 * Real.pi) * (Real.log 2 + 1 / (M : ℝ)) := by
  rw [weighted_sum_eq_poissonMain_add_remainder h]
  have ht := norm_negativeCoefficient_tail_le_source h hβ
  have hp := norm_positiveCoefficient_sum_le_source h
  have hmpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hea := norm_poissonHeadBoundary_half_integer_le (f := f) ha
    (h.g_nonneg a (Set.left_mem_Icc.mpr h.lt.le)) hmpos
  have heb := norm_poissonHeadBoundary_half_integer_le (f := f) hb
    (h.g_nonneg b (Set.right_mem_Icc.mpr h.lt.le)) hmpos
  simp only [Nat.floor_natCast] at hea heb
  have he : poissonBoundary f g a b = 0 := by
    obtain ⟨k, rfl⟩ := ha
    obtain ⟨l, rfl⟩ := hb
    exact poissonBoundary_half_integer f g k l
  rw [he, add_zero]
  have htri (A B T P : ℂ) : ‖A - B + T - P‖ ≤ ‖A‖ + ‖B‖ + ‖T‖ + ‖P‖ := by
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  apply (htri _ _ _ _).trans
  have hsum := add_le_add (add_le_add (add_le_add heb hea) ht) hp
  convert hsum using 1
  ring

/-- Constant-weight Poisson with an arbitrary positive upper Fourier cutoff. -/
theorem constant_partI_cutoff {f : ℝ → ℝ} {a b : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b) (hM : 1 ≤ M) (hβ : deriv f a < (M : ℝ) + 1)
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (1 / Real.pi) * (Real.log ((M : ℝ) + 1) - 1 / (2 * ((M : ℝ) + 1)) -
          (Complex.digamma ((M : ℝ) + 1 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a)) +
          Real.log 2 + 1 / (M : ℝ)) := by
  have hp := partI_half_arbitrary_cutoff h hM hβ ha hb
  simp only [weightedWave, poissonMain_eq_source, Complex.ofReal_one, one_mul] at hp
  have hy := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  have he : partICoefficient f (fun _ => 1) a / deriv f a = 1 / Real.pi := by
    unfold partICoefficient
    simp only [deriv_const, abs_zero, zero_add, mul_one]
    field_simp
  rw [he] at hp
  apply hp.trans_eq
  ring

/-- Moving the cutoff one frequency upward bounds the nearby omitted integral by its actual curvature/gap minimum. -/
theorem poisson_next_cutoff_bound {f : ℝ → ℝ} {a b ℓ : ℝ} {M : ℕ}
    (h : PartIRegularity f (fun _ => 1) a b) (hℓ : 0 < ℓ)
    (hβ : deriv f a < (M : ℝ) + 1)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b))
    (hcurv : ∀ u ∈ Set.Icc a b, deriv (deriv f) u ≤ -ℓ)
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * ((M : ℝ) + 1 - deriv f a))) +
      (1 / Real.pi) * (Real.log ((M : ℝ) + 2) - 1 / (2 * ((M : ℝ) + 2)) -
          (Complex.digamma ((M : ℝ) + 2 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a)) +
          Real.log 2 + 1 / ((M : ℝ) + 1)) := by
  have hp := constant_partI_cutoff (M := M + 1) h (by omega)
    (by push_cast; linarith : deriv f a < ((M + 1 : ℕ) : ℝ) + 1) ha hb
  have hn : (M : ℝ) + 1 + 1 = (M : ℝ) + 2 := by ring
  simp only [Nat.cast_add, Nat.cast_one, hn] at hp
  let I : ℕ → ℂ := fun ν => ∫ u in a..b,
    Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))
  have hi : ‖I (M + 1)‖ ≤
      min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * ((M : ℝ) + 1 - deriv f a))) := by
    apply le_min
    · have hh := kershner_monotone_bound h.lt.le hℓ h.f_differentiable hf' hfc hcurv
        ((M : ℝ) + 1) (Or.inr (fun u hu =>
          (h.f_deriv_antitone (Set.left_mem_Icc.mpr h.lt.le) hu hu.1).trans hβ.le))
      simpa only [I, Nat.cast_add, Nat.cast_one] using hh
    · have hh := norm_shifted_integral_negative h.lt.le h.f_differentiable
        h.f_deriv_continuous h.f_deriv_antitone hβ
      simpa only [I, Nat.cast_add, Nat.cast_one] using hh
  change ‖_ - ∑ ν ∈ Finset.Icc 0 (M + 1), I ν‖ ≤ _ at hp
  rw [Finset.sum_Icc_succ_top (by omega)] at hp
  have ht := (norm_add_le _ _).trans (add_le_add hp hi)
  have he (S P Z : ℂ) : S - (P + Z) + Z = S - P := by ring
  simp only [he] at ht
  exact ht.trans_eq (add_comm _ _)

/-- A general-phase B-process with the nearby upper frequency separated; its shifted digamma argument stays above one. -/
theorem exists_b_process_next_cutoff {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊)
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
      min (0.6715 / Real.sqrt ℓ) (1 / (Real.pi * ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a))) +
      (1 / Real.pi) * (Real.log ((⌊deriv f a⌋₊ : ℝ) + 2) - 1 / (2 * ((⌊deriv f a⌋₊ : ℝ) + 2)) -
          (Complex.digamma ((⌊deriv f a⌋₊ : ℝ) + 2 - deriv f a : ℝ)).re +
          Real.eulerMascheroniConstant + Real.log (1 + deriv f a) - 1 / (2 * (1 + deriv f a)) +
          Real.log 2 + 1 / ((⌊deriv f a⌋₊ : ℝ) + 1)) := by
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hr := constant_weight_partIRegularity hab hf hfc
    (fun u hu => hαpos.trans_le (hanti.antitoneOn hu (Set.right_mem_Icc.mpr hab.le) hu.2))
    hanti.antitoneOn
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
  have hs := stationary_full_sum_sharp ξ hab hℓ hαpos.le hα hM hξ hf hf' hf'' hanti hlower hupper hD
  have hp := poisson_next_cutoff_bound hr hℓ (Nat.lt_floor_add_one (deriv f a)) hf'
    (fun u hu => (hf'' u hu).continuousAt.continuousWithinAt) hcurv hah hbh
  refine ⟨ξ, hξ, ?_⟩
  have ht := (norm_add_le _ _).trans (add_le_add hp hs)
  simp only [sub_add_sub_cancel] at ht
  apply ht.trans_eq
  ring

end DhimanKadiriQuesadaHerrera2026
