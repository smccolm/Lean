import GafniTao.SharpPerron

/-!
# The finite sharp-Perron kernel

This file starts the proof of `SharpPsiTruncationBound` at the genuine
finite-height Perron integral.  In particular, none of the declarations below
assumes an explicit formula, a zero sum, or a Chebyshev estimate.
-/

open scoped BigOperators Interval

namespace GafniTao

/-- The sharp finite-height Perron kernel attached to the Dirichlet monomial
`x^s / n^s`, on the vertical line `Re s = c`. -/
noncomputable def sharpPerronKernel (c T x : ℝ) (n : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t in (-T)..T,
      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
          ((c : ℂ) + (t : ℂ) * Complex.I)

/-- A finite von Mangoldt Dirichlet polynomial, using exactly the coefficients
of `-ζ'/ζ`. -/
noncomputable def finiteMangoldtDirichlet (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ s

private theorem intervalIntegrable_sharpPerronMonomial
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hx : 0 < x) (hn : 1 ≤ n) :
    IntervalIntegrable
      (fun t : ℝ =>
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
          (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
            ((c : ℂ) + (t : ℂ) * Complex.I))
      MeasureTheory.volume (-T) T := by
  have hs : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hxpow : Continuous
      (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    exact Continuous.cpow continuous_const hs
      (fun _ => Complex.ofReal_mem_slitPlane.mpr hx)
  have hnpow : Continuous
      (fun t : ℝ => (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    exact Continuous.cpow continuous_const hs
      (fun _ => Complex.natCast_mem_slitPlane.mpr (Nat.ne_zero_of_lt hn))
  have hnpow_ne : ∀ t : ℝ,
      (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t
    rw [Complex.cpow_ne_zero_iff]
    left
    exact_mod_cast Nat.ne_zero_of_lt hn
  have hs_ne : ∀ t : ℝ, (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, Complex.zero_re] at hre
    linarith
  exact ((hxpow.div hnpow hnpow_ne).div hs hs_ne).intervalIntegrable _ _

/-- Finite linearity of the sharp Perron integral.  This is the exact entry
identity before taking the (absolutely convergent) von Mangoldt Dirichlet
series limit. -/
theorem finiteMangoldt_sharpPerron_identity
    {c T x : ℝ} {N : ℕ} (hc : 0 < c) (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℂ) *
        ∫ t in (-T)..T,
          finiteMangoldtDirichlet N
              ((c : ℂ) + (t : ℂ) * Complex.I) *
            (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
              ((c : ℂ) + (t : ℂ) * Complex.I) =
      ∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronKernel c T x n := by
  simp only [finiteMangoldtDirichlet]
  have hInt : ∀ n ∈ Finset.Icc 1 N,
      IntervalIntegrable
        (fun t : ℝ =>
          (ArithmeticFunction.vonMangoldt n : ℂ) /
              (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) *
            (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
              ((c : ℂ) + (t : ℂ) * Complex.I))
        MeasureTheory.volume (-T) T := by
    intro n hn
    have hnOne : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hmono := intervalIntegrable_sharpPerronMonomial
      (T := T) hc hx hnOne
    exact IntervalIntegrable.congr (fun t _ht => by ring)
      (hmono.const_mul (ArithmeticFunction.vonMangoldt n : ℂ))
  calc
    (1 / (2 * Real.pi) : ℂ) *
        ∫ t in (-T)..T,
          (∑ n ∈ Finset.Icc 1 N,
              (ArithmeticFunction.vonMangoldt n : ℂ) /
                (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)) *
            (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
              ((c : ℂ) + (t : ℂ) * Complex.I)
        = (1 / (2 * Real.pi) : ℂ) *
            ∫ t in (-T)..T,
              ∑ n ∈ Finset.Icc 1 N,
                (ArithmeticFunction.vonMangoldt n : ℂ) /
                    (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) *
                  (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                    ((c : ℂ) + (t : ℂ) * Complex.I) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro t _ht
          dsimp only
          rw [Finset.sum_mul, Finset.sum_div]
    _ = (1 / (2 * Real.pi) : ℂ) *
          ∑ n ∈ Finset.Icc 1 N,
            ∫ t in (-T)..T,
              (ArithmeticFunction.vonMangoldt n : ℂ) /
                    (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) *
                  (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                    ((c : ℂ) + (t : ℂ) * Complex.I) := by
          rw [intervalIntegral.integral_finsetSum hInt]
    _ = ∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            sharpPerronKernel c T x n := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          have hnOne : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          rw [sharpPerronKernel]
          calc
            (1 / (2 * Real.pi) : ℂ) *
                ∫ t in (-T)..T,
                  (ArithmeticFunction.vonMangoldt n : ℂ) /
                      (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) *
                    (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                      ((c : ℂ) + (t : ℂ) * Complex.I)
                = (1 / (2 * Real.pi) : ℂ) *
                    ∫ t in (-T)..T,
                      (ArithmeticFunction.vonMangoldt n : ℂ) *
                        ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                          (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                            ((c : ℂ) + (t : ℂ) * Complex.I)) := by
                      congr 1
                      apply intervalIntegral.integral_congr
                      intro t _ht
                      ring
            _ = (1 / (2 * Real.pi) : ℂ) *
                  ((ArithmeticFunction.vonMangoldt n : ℂ) *
                    ∫ t in (-T)..T,
                      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                        (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                          ((c : ℂ) + (t : ℂ) * Complex.I)) := by
                    rw [intervalIntegral.integral_const_mul]
            _ = (ArithmeticFunction.vonMangoldt n : ℂ) *
                  ((1 / (2 * Real.pi) : ℂ) *
                    ∫ t in (-T)..T,
                      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                        (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                          ((c : ℂ) + (t : ℂ) * Complex.I)) := by ring

end GafniTao
