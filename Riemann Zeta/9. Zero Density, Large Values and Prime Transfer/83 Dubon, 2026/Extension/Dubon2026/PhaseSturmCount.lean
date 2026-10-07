import Dubon2026.SturmRootCount

/-! # The Sturm computation counts the actual zeros on a vertical segment -/

namespace Dubon2026

open Polynomial Complex

noncomputable section

theorem phase_real_root_count_eq_twice_vertical_count (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u T H σ : ℝ}
    (hl : l < σ) (hu : σ < u) (hH : H ≤ T) (x : PrimeCoordinate N → ℝ) :
    realPolynomialRootCount (phaseVerticalRealPolynomial a N hN ha l u T σ x) (-H) H =
      2 * ∑ s ∈ (zerosInOpenRectangleFinset
        (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N hN
        (by rwa [twistedCoefficients_one]) l u H).filter (fun s => s.re = σ),
          zeroMultiplicity (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N s := by
  classical
  rw [realPolynomialRootCount_eq_sum, Finset.mul_sum]
  apply Finset.sum_bij (fun (t : ℝ) _ => (σ : ℂ) + I * (t : ℂ))
  · intro t ht
    obtain ⟨hr, hlt, htu⟩ := Finset.mem_filter.mp ht
    have hab : |t| < H := abs_lt.mpr ⟨hlt, htu⟩
    have hz : dirichletSum (twistedCoefficients a N (fun p => (x p : UnitAddCircle)))
        N ((σ : ℂ) + I * t) = 0 :=
      (phaseVerticalRealPolynomial_eval_zero_iff a N hN ha hl hu (hab.trans_le hH) x).mp
        ((Polynomial.mem_roots (phaseVerticalRealPolynomial_ne_zero a N hN ha l u T σ x)).mp
          (Multiset.mem_toFinset.mp hr))
    rw [Finset.mem_filter, mem_zerosInOpenRectangleFinset]
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero,
      Complex.add_im, Complex.mul_im, one_mul, zero_add] using
      And.intro (And.intro hl (And.intro hu (And.intro hab hz))) (rfl : σ = σ)
  · intro t _ v _ hv
    have he := congrArg Complex.im hv
    simpa using he
  · intro s hs
    obtain ⟨hs, hσ⟩ := Finset.mem_filter.mp hs
    obtain ⟨_, _, hab, hz⟩ := (mem_zerosInOpenRectangleFinset _ _ _ _ _ _ _ _).mp hs
    have he : (σ : ℂ) + I * s.im = s := by
      apply Complex.ext <;> simp [hσ]
    refine ⟨s.im, ?_, he⟩
    rw [Finset.mem_filter, Multiset.mem_toFinset,
      Polynomial.mem_roots (phaseVerticalRealPolynomial_ne_zero a N hN ha l u T σ x)]
    constructor
    · apply (phaseVerticalRealPolynomial_eval_zero_iff a N hN ha hl hu (hab.trans_le hH) x).mpr
      rw [he]
      exact hz
    · exact abs_lt.mp hab
  · intro t ht
    have hab : |t| < H := abs_lt.mpr (Finset.mem_filter.mp ht).2
    exact phaseVerticalRealPolynomial_rootMultiplicity_interior a N hN ha hl hu
      (hab.trans_le hH) x

theorem phase_sturm_count_eq_twice_vertical_count (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u T H σ : ℝ}
    (hl : l < σ) (hu : σ < u) (hH : H ≤ T) (x : PrimeCoordinate N → ℝ) :
    sturmMultiplicityCount (phaseVerticalRealPolynomial a N hN ha l u T σ x) (-H) H =
      2 * ∑ s ∈ (zerosInOpenRectangleFinset
        (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N hN
        (by rwa [twistedCoefficients_one]) l u H).filter (fun s => s.re = σ),
          zeroMultiplicity (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N s := by
  rw [sturmMultiplicityCount_eq_root_count
    (phaseVerticalRealPolynomial_ne_zero a N hN ha l u T σ x)]
  exact phase_real_root_count_eq_twice_vertical_count a N hN ha hl hu hH x

end

end Dubon2026
