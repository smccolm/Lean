import DhimanKadiriQuesadaHerrera2026.BProcessIntegrals
import DhimanKadiriQuesadaHerrera2026.PartIIConstant
import DhimanKadiriQuesadaHerrera2026.BProcessReview

namespace DhimanKadiriQuesadaHerrera2026

/-- The actual discrete B-process follows under the source phase assumptions with the accepted Part-I Poisson error. This is not the smaller printed Part-II error. -/
theorem exists_b_process_partI {f : ℝ → ℝ} {a b ℓ₂ ℓ₃ h₂ h₃ : ℝ}
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
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ₂ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 +
      (1 / Real.pi) *
        (Real.log (1 + deriv f a) + Real.log (1 + (⌊deriv f a⌋₊ : ℝ)) +
          Real.eulerMascheroniConstant - 1 / (2 * (1 + (⌊deriv f a⌋₊ : ℝ))) -
            1 / (2 * (1 + deriv f a)) -
              (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re +
                Real.log 2 + 1 / deriv f a) := by
  obtain ⟨ξ, hξ, hs⟩ := exists_source_stationary_transform hab hℓ₂ hℓ₃ hh₃ hαpos hα hah hbh
    hf hf' hf'' hanti hlower hupper hD
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) :=
    fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hp := corollary_zero_one_partI hab hf hfc hαpos hanti hah hbh
  refine ⟨ξ, hξ, ?_⟩
  have ht := (norm_add_le _ _).trans (add_le_add hp hs)
  simpa only [sub_add_sub_cancel, add_comm] using ht

/-- The actual discrete B-process with the proved second-order coefficients, conditional on the explicit repaired analytic regularity and half-offset condition. -/
theorem exists_b_process_partII {f : ℝ → ℝ} {a b ℓ₂ ℓ₃ h₂ h₃ : ℝ}
    (r : SecondOrderRegularity f (fun _ => 1) a b)
    (hδ : 1 / 2 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a)
    (hℓ₂ : 0 < ℓ₂) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hα : deriv f b < 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ₂ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ₂)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ₂ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) + 1.251 +
      ((Real.log 2 + 1 / (deriv f a)) / Real.pi +
      (deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) + (deriv f a) * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) * (minusSquareBound ⌊deriv f a⌋₊ (deriv f a) + plusSquareBound (deriv f a)) +
      (deriv f a * |deriv (deriv f) a| / (2 * Real.pi ^ 2)) * (minusCubeBound ⌊deriv f a⌋₊ (deriv f a) + plusCubeBound (deriv f a))) := by
  have hab := r.lt
  have hf := r.f_differentiable
  have hf' := r.f_deriv_differentiable
  have hαpos := r.f_deriv_pos b (Set.right_mem_Icc.mpr hab.le)
  obtain ⟨ξ, hξ, hs⟩ := exists_source_stationary_transform hab hℓ₂ hℓ₃ hh₃ hαpos hα hah hbh
    hf hf' hf'' hanti hlower hupper hD
  have hp := constant_second_poisson_half r hah hbh hδ
  dsimp only at hp
  refine ⟨ξ, hξ, ?_⟩
  have ht := (norm_add_le _ _).trans (add_le_add hp hs)
  simpa only [sub_add_sub_cancel, add_comm] using ht

/-- The smooth quadratic review phase satisfies the B-process phase conditions but fails the extra second-order quotient input. -/
theorem BProcessReview.phase_not_secondOrderRegularity :
    ¬ SecondOrderRegularity phase (fun _ => 1) (1 / 2) (3 / 2) := by
  intro r
  have hq := r.positive_deriv_quotient (fun u => 1 * deriv phase u) (Or.inr rfl) 0
  simp only [one_mul, Nat.cast_zero, zero_add] at hq
  have h := hq (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2) (3 / 2))
    (by norm_num : (3 / 2 : ℝ) ∈ Set.Icc (1 / 2) (3 / 2)) (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)
  norm_num [phase_deriv, phase_second_deriv] at h

end DhimanKadiriQuesadaHerrera2026
