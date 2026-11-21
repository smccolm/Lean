import Dubon2026.RankinBoundaryNonvanishing

namespace Dubon2026
open Filter Set
open scoped Topology
noncomputable section

/-- Both outer roots use the three-fifths bound; the middle root equals one. -/
theorem primitive_second_spectral_growth {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : Nat.Primes) (i : Fin 3) :
    ‖primitiveSymmetricSpectralRoots f 2 p i‖ ≤ ((p : ℕ) : ℝ) ^ (3/5 : ℝ) := by
  by_cases h : (p : ℕ) ∣ Q
  · simp only [primitiveSymmetricSpectralRoots, if_pos h, norm_zero]
    positivity
  obtain ⟨h1, h2⟩ := primitiveSatake_norm_sq_le_three_fifths f hk p.property h
  fin_cases i
  · simpa [primitiveSymmetricSpectralRoots, h, norm_pow] using h2
  · simp only [primitiveSymmetricSpectralRoots, if_neg h]
    norm_num
    rw [← norm_mul, (primitiveSatake_trace_det f p).2, norm_one]
    exact Real.one_le_rpow (by exact_mod_cast p.property.one_le) (by norm_num)
  · simpa [primitiveSymmetricSpectralRoots, h, norm_pow] using h1

private theorem spectral_coordinate_growth (p : Nat.Primes) {w s : ℂ}
    (hw : ‖w‖ ≤ ((p : ℕ) : ℝ)^(3/5 : ℝ)) (hs : 9/10 ≤ s.re) :
    ‖w * ((p : ℕ) : ℂ)^(-s)‖ ≤ ((p : ℕ) : ℝ)^(-(3/10 : ℝ)) := by
  have h1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.one_le
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
  calc
    _ ≤ ((p : ℕ) : ℝ)^(3/5 : ℝ) * ((p : ℕ) : ℝ)^(-(9/10 : ℝ)) :=
      mul_le_mul hw (Real.rpow_le_rpow_of_exponent_le h1 (neg_le_neg hs)) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by linarith : (0 : ℝ) < (p : ℕ))]; norm_num

private theorem weighted_spectral_tail_bound (p : Nat.Primes) {w s : ℂ}
    (hw : ‖w‖ ≤ ((p : ℕ) : ℝ)^(3/5 : ℝ)) (hs : 9/10 ≤ s.re) :
    Real.log (p : ℕ) * ‖spectralEulerTail w (((p : ℕ) : ℂ)^(-s))‖ ≤
      (10 / (1 - (2 : ℝ)^(-(3/10 : ℝ)))) * (‖w‖ * ((p : ℕ) : ℝ)^(-(11/10 : ℝ))) := by
  let x : ℝ := (p : ℕ)
  let z := ((p : ℕ) : ℂ)^(-s)
  let ρ : ℝ := 2^(-(3/10 : ℝ))
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast p.property.one_le
  have hx0 : 0 < x := by linarith
  have hρ : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hcz : ‖w*z‖ ≤ x^(-(3/10 : ℝ)) := spectral_coordinate_growth p hw hs
  have hcz' : ‖w*z‖ ≤ ρ := hcz.trans (Real.rpow_le_rpow_of_nonpos (by norm_num)
    (by dsimp [x]; exact_mod_cast p.property.two_le : 2 ≤ x) (by norm_num))
  have hd : 1 - ρ ≤ ‖1-w*z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (w*z)
    rw [norm_one] at this
    linarith
  have hz : ‖z‖ ≤ x^(-(9/10 : ℝ)) := by
    rw [show ‖z‖ = x^(-s.re) by simp [z,x,Complex.norm_natCast_cpow_of_pos p.property.pos]]
    exact Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hs)
  have hsquare : ‖w*z‖^2 ≤ ‖w‖ * (x^(-(9/10 : ℝ)) * x^(-(3/10 : ℝ))) := by
    rw [sq, ← mul_assoc]
    exact mul_le_mul (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hz (norm_nonneg _))
      hcz (norm_nonneg _) (by positivity)
  have hl := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1/10)
  change Real.log x * (‖(w*z)^2 / (1-w*z)‖) ≤ (10 / (1-ρ)) * (‖w‖ * x^(-(11/10 : ℝ)))
  rw [norm_div, norm_pow]
  calc
    _ ≤ (x^(1/10 : ℝ) / (1/10)) * ((‖w‖ * (x^(-(9/10 : ℝ)) * x^(-(3/10 : ℝ)))) / (1-ρ)) :=
      mul_le_mul hl (div_le_div₀ (by positivity) hsquare (by linarith) hd) (by positivity) (by positivity)
    _ = _ := by
      have he : x^(1/10 : ℝ) * (x^(-(9/10 : ℝ)) * x^(-(3/10 : ℝ))) = x^(-(11/10 : ℝ)) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
      rw [← he]
      ring

/-- The untempered square roots still give a holomorphic prime-power remainder
strictly to the left of one. One root factor is paid for by the Rankin mean. -/
theorem primitive_second_tail_analytic {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    AnalyticOnNhd ℂ (primeSpectralTail (primitiveSymmetricSpectralRoots f 2))
      {s : ℂ | 9/10 < s.re} := by
  let w := primitiveSymmetricSpectralRoots f 2
  let c : ℝ := 10 / (1 - (2 : ℝ)^(-(3/10 : ℝ)))
  let M := fun p : Nat.Primes => c * ∑ i, ‖w p i‖ * ((p : ℕ) : ℝ)^(-(11/10 : ℝ))
  have hnorm := summable_norm_primitive_second_spectral f (by omega : 0 ≤ k)
    (s := ((11/10 : ℝ) : ℂ)) (by norm_num)
  have hpow (p : Nat.Primes) := Complex.norm_natCast_cpow_of_pos p.property.pos
  simp only [norm_neg, norm_mul, hpow,
    Complex.neg_re, Complex.ofReal_re] at hnorm
  have hm : Summable M := by
    have hh := ((summable_prod_of_nonneg (fun v : Nat.Primes × Fin 3 =>
      show 0 ≤ ‖w v.1 v.2‖ * ((v.1 : ℕ) : ℝ)^(-(11/10 : ℝ)) by positivity)).mp hnorm).2
    simpa only [M, tsum_fintype] using hh.mul_left c
  have hU : IsOpen {s : ℂ | 9/10 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hU
  refine Complex.differentiableOn_tsum_of_summable_norm hm ?_ hU ?_
  · intro p t ht
    apply DifferentiableWithinAt.const_mul
    apply DifferentiableWithinAt.fun_sum
    intro i _
    have hg := spectral_coordinate_growth p (primitive_second_spectral_growth f hk p i) ht.le
    have hlt : ‖w p i * ((p : ℕ) : ℂ)^(-t)‖ < 1 := hg.trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by norm_num))
    have hne : 1 - w p i * ((p : ℕ) : ℂ)^(-t) ≠ 0 := by
      intro he
      rw [← sub_eq_zero.mp he, norm_one] at hlt
      exact (lt_irrefl _ hlt)
    have hdiff := ((primeDirichletCoordinate_differentiable p).const_mul (w p i)).differentiableAt (x := t)
    exact ((hdiff.pow 2).div (hdiff.const_sub 1) hne).differentiableWithinAt
  · intro p t ht
    simp only [primeSpectralTailTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast p.property.one_le : (1 : ℝ) ≤ (p : ℕ)))]
    calc
      _ ≤ Real.log (p : ℕ) * ∑ i, ‖spectralEulerTail (w p i) (((p : ℕ) : ℂ)^(-t))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.log_nonneg (by exact_mod_cast p.property.one_le))
      _ ≤ M p := by
        dsimp only [M]
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => weighted_spectral_tail_bound p (primitive_second_spectral_growth f hk p i) ht.le

end
end Dubon2026
