import DhimanKadiriQuesadaHerrera2026.CubicBudget
import DhimanKadiriQuesadaHerrera2026.CubicHybrid

namespace DhimanKadiriQuesadaHerrera2026

set_option maxHeartbeats 800000 in
/-- The literal many-frequency B-process holds for arbitrary source phases with third-derivative bound at most one. -/
theorem exists_b_process_cubic_small_D {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hM : 2 ≤ ⌊deriv f a⌋₊) (hD1 : D ≤ 1)
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
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  have haa := Set.left_mem_Icc.mpr hab.le
  have hbb := Set.right_mem_Icc.mpr hab.le
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a haa)
  have hκ : ℓ ≤ h₂ * ℓ := (hlower a haa).trans (hupper a haa)
  have hh₂ : 1 ≤ h₂ := by nlinarith
  have hfc : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hr := constant_weight_partIRegularity hab hf hfc
    (fun u hu => hαpos.trans_le (hanti.antitoneOn hu hbb hu.2)) hanti.antitoneOn
  have hβp := hr.f_deriv_pos a haa
  have hβ : 2 ≤ deriv f a := by
    have hh : (2 : ℝ) ≤ (⌊deriv f a⌋₊ : ℝ) := by exact_mod_cast hM
    exact hh.trans (Nat.floor_le hβp.le)
  have hcurv := stationary_curvature_of_antitone hab hf' hanti.antitoneOn hlower
  obtain ⟨ξ, hξ⟩ := exists_stationary_family hab.le hfc hanti hα
  have hs := stationary_sum_next_hybrid ξ hab hℓ hαpos.le hα hM hξ hf hf' hf'' hanti hlower hupper hD
  have hgap : (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a + 1 = (⌊deriv f a⌋₊ : ℝ) + 2 - deriv f a := by ring
  have hn : (⌊deriv f a⌋₊ : ℝ) + 1 + 1 = (⌊deriv f a⌋₊ : ℝ) + 2 := by ring
  have hδ : 0 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a := by linarith [Nat.lt_floor_add_one (deriv f a)]
  have hp := constant_poisson_cubic_split (M := ⌊deriv f a⌋₊ + 1) hr hf' hf''
    (fun u hu => (hcurv u hu).trans (by linarith)) hupper hD (by omega)
    (by push_cast; linarith [Nat.lt_floor_add_one (deriv f a)] : 1 / 2 ≤ ((⌊deriv f a⌋₊ + 1 : ℕ) : ℝ) + 1 - deriv f a) hah hbh
  simp only [Nat.cast_add, Nat.cast_one, hn] at hp
  have hcb := cubic_curvature_gap_budget hαpos.le hβ hℓ hκ
  dsimp only at hcb
  rw [hgap] at hcb
  have hS := cubic_series_uniform hαpos.le hδ
  rw [hgap] at hS
  have hlen := cubic_small_D_budget hDn hD1 (sub_nonneg.mpr hab.le) hh₂ hS
  have hconst := cubic_constant_budget hαpos hα.le hβp ⌊deriv f a⌋₊
  refine ⟨ξ, hξ, ?_⟩
  have ht := (norm_add_le _ _).trans (add_le_add hp hs)
  simp only [sub_add_sub_cancel] at ht
  apply ht.trans
  norm_num only [div_eq_mul_inv, mul_inv_rev] at hcb hlen hconst ⊢
  nlinarith only [hcb, hlen, hconst]

/-- The literal B-process for every frequency count when the third-derivative bound is at most one. -/
theorem exists_b_process_small_D {f : ℝ → ℝ} {a b ℓ D h₂ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hD1 : D ≤ 1)
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
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * D ^ (1 / 3 : ℝ) * (b - a) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  by_cases hsmall : deriv f a < 2
  · exact exists_b_process_printed_small hab hℓ hαpos hα hsmall hah hbh hf hf' hf'' hanti hlower hupper hD
  · have hM : 2 ≤ ⌊deriv f a⌋₊ := Nat.le_floor (show (2 : ℝ) ≤ deriv f a from le_of_not_gt hsmall)
    exact exists_b_process_cubic_small_D hab hℓ hαpos hα hM hD1 hah hbh hf hf' hf'' hanti hlower hupper hD

/-- The source third-derivative scales are retained in the full bounded-third-derivative corollary. -/
theorem exists_source_b_process_small_D {f : ℝ → ℝ} {a b ℓ ℓ₃ h₂ h₃ : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hℓ₃ : 0 ≤ ℓ₃) (hh₃ : 0 ≤ h₃) (hαpos : 0 < deriv f b) (hα : deriv f b < 1)
    (hD1 : h₃ * ℓ₃ ≤ 1)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hanti : StrictAntiOn (deriv f) (Set.Icc a b))
    (hlower : ∀ u ∈ Set.Icc a b, ℓ ≤ |deriv (deriv f) u|)
    (hupper : ∀ u ∈ Set.Icc a b, |deriv (deriv f) u| ≤ h₂ * ℓ)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ h₃ * ℓ₃) :
    ∃ ξ : ℕ → ℝ, (∀ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
      ξ ν ∈ Set.Icc a b ∧ deriv f (ξ ν) = (ν : ℝ)) ∧
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 1 ⌊deriv f a⌋₊,
        Complex.exp (2 * Real.pi * Complex.I * ((f (ξ ν) - (ν : ℝ) * ξ ν - 1 / 8 : ℝ) : ℂ)) /
          (Real.sqrt |deriv (deriv f) (ξ ν)| : ℂ)‖ ≤
      2.686 / Real.sqrt ℓ +
        (2 * (3 : ℝ) ^ (2 / 3 : ℝ) / Real.pi ^ (2 / 3 : ℝ)) * h₂ * h₃ ^ (1 / 3 : ℝ) * (b - a) * ℓ₃ ^ (1 / 3 : ℝ) +
        2 / Real.pi * Real.log (deriv f a - deriv f b) +
      ((deriv f b * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f b) +
          deriv f a * halfSecondEndpointBound ⌊deriv f a⌋₊ (deriv f a)) / (2 * Real.pi) +
        (h₂ * ℓ) * printedPartIIE1 (deriv f a) / (2 * Real.pi ^ 2 * deriv f a) +
        (h₂ * ℓ) * partIICubeCoefficient (deriv f a) / (2 * Real.pi ^ 2) +
        1 / (2 * Real.pi * deriv f a) + 1.251 + Real.log 2 / (2 * Real.pi)) := by
  obtain ⟨ξ, hξ, h⟩ := exists_b_process_small_D hab hℓ hαpos hα hD1 hah hbh hf hf' hf'' hanti hlower hupper hD
  refine ⟨ξ, hξ, ?_⟩
  apply h.trans_eq
  rw [Real.mul_rpow hh₃ hℓ₃]
  ring

end DhimanKadiriQuesadaHerrera2026
