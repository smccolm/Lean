import Dubon2026.SourceIntegralTraceTranslates

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. The finite translation sum
is periodic of width one and has the required holomorphic, bounded and
Fourier properties. Reuse the native period-power identity, avoiding the
upstream bespoke function wrapper. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace.Translates
noncomputable section
open UpperHalfPlane Filter Function Complex Function.Complex
open scoped Real Topology Manifold
variable {f : ℍ → ℂ} {h₀ : ℕ}

private theorem qParam_vadd (x : ℝ) (τ : ℍ) :
    Periodic.qParam (h₀ : ℝ) (((x +ᵥ τ : ℍ)) : ℂ) =
      cexp (2 * π * Complex.I * x / h₀) * Periodic.qParam (h₀ : ℝ) τ := by
  simp only [Periodic.qParam, coe_vadd, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem sum_exp_eq (hh₀ : 0 < h₀) (n : ℕ) :
    ∑ j ∈ Finset.range h₀, cexp (2 * π * Complex.I * ((j : ℕ) : ℝ) / h₀) ^ n =
      if h₀ ∣ n then (h₀ : ℂ) else 0 := by
  have hh₀' : (h₀ : ℂ) ≠ 0 := by exact_mod_cast hh₀.ne'

  set ζ : ℂ := cexp (2 * π * Complex.I * n / h₀) with hζ
  have hterm : ∀ j : ℕ, cexp (2 * π * Complex.I * ((j : ℕ) : ℝ) / h₀) ^ n = ζ ^ j := by
    intro j
    rw [hζ, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    exact congrArg cexp (by push_cast; ring)
  simp only [hterm]
  have hζpow : ζ ^ h₀ = 1 := by
    rw [hζ, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨n, ?_⟩
    push_cast
    field_simp
  split_ifs with hdiv
  · obtain ⟨k, rfl⟩ := hdiv
    have hζ1 : ζ = 1 := by
      rw [hζ, Complex.exp_eq_one_iff]
      refine ⟨k, ?_⟩
      push_cast; field_simp
    simp [hζ1]
  · have hζ1 : ζ ≠ 1 := by
      intro h1
      rw [hζ, Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      apply hdiv
      have h2 : (n : ℂ) = k * h₀ := by
        field_simp at hk
        linear_combination hk
      have h3 : (n : ℤ) = k * h₀ := by exact_mod_cast h2
      exact Int.natCast_dvd_natCast.mp ⟨k, by rw [h3]; ring⟩
    rw [geom_sum_eq hζ1, hζpow, sub_self, zero_div]

theorem coeff_translation_sum (hh₀ : 0 < h₀) (hper : Periodic (f ∘ ofComplex) (h₀ : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : IsBoundedAtImInfty f) (m : ℕ) :
    PowerSeries.coeff m (qExpansion 1 (trSum f h₀)) =
      (h₀ : ℂ) * PowerSeries.coeff (h₀ * m) (qExpansion (h₀ : ℝ) f) := by
  have hh₀r : 0 < (h₀ : ℝ) := by exact_mod_cast hh₀
  let a : ℕ → ℂ := fun n => PowerSeries.coeff n (qExpansion (h₀ : ℝ) f)
  let b : ℕ → ℂ := fun m => (h₀ : ℂ) * a (h₀ * m)
  have hinj : Injective (fun m : ℕ => h₀ * m) := mul_right_injective₀ hh₀.ne'
  have hnot : ∀ i : ℕ, ¬ h₀ ∣ i → ¬ ∃ m, (fun m : ℕ => h₀ * m) m = i :=
    fun i hdiv ⟨m, hm⟩ => hdiv ⟨m, hm.symm⟩

  have hsum1 : ∀ τ : ℍ, HasSum (fun n => ((if h₀ ∣ n then (h₀ : ℂ) else 0) * a n) •
      Periodic.qParam (h₀ : ℝ) τ ^ n) (trSum f h₀ τ) := by
    intro τ
    have hj : ∀ j ∈ Finset.range h₀, HasSum (fun n => a n • Periodic.qParam (h₀ : ℝ)
        ((((((j : ℕ) : ℝ)) +ᵥ τ : ℍ)) : ℂ) ^ n) (f (((j : ℕ) : ℝ) +ᵥ τ)) :=
      fun j _ => hasSum_qExpansion hh₀r hper hhol hbdd _
    have := hasSum_sum hj
    refine this.congr_fun fun n => ?_
    simp only [qParam_vadd, mul_pow, smul_eq_mul]
    rw [← sum_exp_eq hh₀ n, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hsum2 : ∀ τ : ℍ, HasSum (fun m => b m • Periodic.qParam 1 τ ^ m) (trSum f h₀ τ) := by
    intro τ
    have heq : (fun n => ((if h₀ ∣ n then (h₀ : ℂ) else 0) * a n) • Periodic.qParam (h₀ : ℝ) τ ^ n) =
        extend (fun m : ℕ => h₀ * m) (fun m => b m • Periodic.qParam 1 τ ^ m) 0 := by
      funext n
      split_ifs with hdiv
      · obtain ⟨m, rfl⟩ := hdiv
        rw [hinj.extend_apply, pow_mul, ← SourceFricke.qParam_one_eq_pow hh₀.ne']
      · rw [extend_apply' _ _ _ (hnot n hdiv), Pi.zero_apply, zero_mul, zero_smul]
    have := hsum1 τ
    rwa [heq, hasSum_extend_zero hinj] at this

  let F : C(ℍ, ℂ) := ⟨trSum f h₀, (mdifferentiable_trSum hhol).continuous⟩
  have hFsum : ∀ τ : ℍ, HasSum (fun m => b m • Periodic.qParam 1 τ ^ m) (F τ) := hsum2
  have huniq := qExpansion_coeff_unique F one_pos
    (analyticAt_cuspFunction_zero one_pos (periodic_trSum hper) (mdifferentiable_trSum hhol)
      (isBoundedAtImInfty_trSum hbdd)) hFsum m
  change b m = PowerSeries.coeff m (qExpansion 1 (trSum f h₀)) at huniq
  rw [← huniq]

end
end Dubon2026.SourceFunctionField.IntegralTrace.Translates
