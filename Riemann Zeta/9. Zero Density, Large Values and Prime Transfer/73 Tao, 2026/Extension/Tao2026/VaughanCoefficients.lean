import Tao2026.VaughanIdentity

/-!
# Coefficients in the source-oriented Vaughan decomposition

This module reassociates the exact Vaughan identity into the Type I/Type II
coefficient pairs used in the pinned proof of Singmaster Proposition 1.12.  It
then proves, from the definitions of the Möbius and von Mangoldt functions,
the source's logarithmic coefficient envelope and the cutoff/tail support
conditions.  The shorter-than-dyadic family count and all analytic
cancellation estimates remain separate statements.
-/

open ArithmeticFunction
open scoped Moebius zeta

namespace Tao2026

/-- The Möbius coefficient in the first Type I term. -/
noncomputable def vaughanTypeICoefficient (U : ℕ) : ArithmeticFunction ℝ :=
  arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U

/-- The convolved coefficient in the second Type I term. -/
noncomputable def vaughanTypeIPrimeCoefficient (U V : ℕ) :
    ArithmeticFunction ℝ :=
  arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U *
    arithmeticFunctionCutoff Λ V

/-- The Möbius tail coefficient in the Type II term. -/
noncomputable def vaughanTypeIIBetaCoefficient (U : ℕ) :
    ArithmeticFunction ℝ :=
  arithmeticFunctionTail (μ : ArithmeticFunction ℝ) U

/-- The von-Mangoldt-tail divisor sum in the Type II term. -/
noncomputable def vaughanTypeIIGammaCoefficient (V : ℕ) :
    ArithmeticFunction ℝ :=
  arithmeticFunctionTail Λ V * (ζ : ArithmeticFunction ℝ)

/-- The exact Vaughan identity, reassociated into the coefficient pairs used
by the source's Type I and Type II sums. -/
theorem vaughanIdentity_sourceCoefficients (U V : ℕ) :
    Λ =
      arithmeticFunctionCutoff Λ V +
        vaughanTypeICoefficient U * log -
        vaughanTypeIPrimeCoefficient U V * (ζ : ArithmeticFunction ℝ) +
        vaughanTypeIIBetaCoefficient U * vaughanTypeIIGammaCoefficient V := by
  simpa only [vaughanTypeICoefficient, vaughanTypeIPrimeCoefficient,
    vaughanTypeIIBetaCoefficient, vaughanTypeIIGammaCoefficient, mul_assoc]
    using vaughanIdentity U V

/-- The source-oriented identity after multiplication by an arbitrary complex
weight and summation over a finite set. -/
theorem weightedVaughanIdentity_sourceCoefficients
    (S : Finset ℕ) (w : ℕ → ℂ) (U V : ℕ) :
    weightedRealArithmeticSum S w Λ =
      weightedRealArithmeticSum S w (arithmeticFunctionCutoff Λ V) +
        weightedRealArithmeticSum S w
          ((vaughanTypeICoefficient U * log) : ArithmeticFunction ℝ) -
        weightedRealArithmeticSum S w
          ((vaughanTypeIPrimeCoefficient U V *
            (ζ : ArithmeticFunction ℝ)) : ArithmeticFunction ℝ) +
        weightedRealArithmeticSum S w
          ((vaughanTypeIIBetaCoefficient U *
            vaughanTypeIIGammaCoefficient V) : ArithmeticFunction ℝ) := by
  unfold weightedRealArithmeticSum
  calc
    (∑ n ∈ S, (Λ n : ℂ) * w n) =
        ∑ n ∈ S,
          ((arithmeticFunctionCutoff Λ V n +
              (vaughanTypeICoefficient U * log) n -
              (vaughanTypeIPrimeCoefficient U V *
                (ζ : ArithmeticFunction ℝ)) n +
              (vaughanTypeIIBetaCoefficient U *
                vaughanTypeIIGammaCoefficient V) n : ℝ) : ℂ) * w n := by
      apply Finset.sum_congr rfl
      intro n _hn
      have hpoint := congrArg (fun f : ArithmeticFunction ℝ => f n)
        (vaughanIdentity_sourceCoefficients U V)
      change Λ n = arithmeticFunctionCutoff Λ V n +
        (vaughanTypeICoefficient U * log) n -
        (vaughanTypeIPrimeCoefficient U V *
          (ζ : ArithmeticFunction ℝ)) n +
        (vaughanTypeIIBetaCoefficient U *
          vaughanTypeIIGammaCoefficient V) n at hpoint
      exact congrArg (fun x : ℝ => (x : ℂ) * w n) hpoint
    _ = _ := by
      simp only [Complex.ofReal_add, Complex.ofReal_sub, add_mul, sub_mul,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- A tail is literally the original coefficient above the cutoff and zero
at or below it. -/
theorem arithmeticFunctionTail_apply {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) (X n : ℕ) :
    arithmeticFunctionTail f X n = if X < n then f n else 0 := by
  by_cases h : n ≤ X
  · rw [arithmeticFunctionTail_apply_of_le f h]
    simp [Nat.not_lt.mpr h]
  · have hlt : X < n := Nat.lt_of_not_ge h
    rw [arithmeticFunctionTail_apply_of_lt f hlt]
    simp [hlt]

theorem arithmeticFunctionTail_vonMangoldt_nonneg (V n : ℕ) :
    0 ≤ arithmeticFunctionTail Λ V n := by
  rw [arithmeticFunctionTail_apply]
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_rfl

theorem arithmeticFunctionTail_vonMangoldt_le (V n : ℕ) :
    arithmeticFunctionTail Λ V n ≤ Λ n := by
  rw [arithmeticFunctionTail_apply]
  split_ifs
  · exact le_rfl
  · exact vonMangoldt_nonneg

theorem abs_arithmeticFunctionCutoff_moebius_le_one (U n : ℕ) :
    |arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U n| ≤ 1 := by
  by_cases h : n ≤ U
  · rw [arithmeticFunctionCutoff_apply, if_pos h]
    calc
      |((μ n : ℤ) : ℝ)| = ((|μ n| : ℤ) : ℝ) := Int.cast_abs.symm
      _ ≤ (1 : ℝ) := by exact_mod_cast (abs_moebius_le_one (n := n))
  · simp [arithmeticFunctionCutoff_apply, h]

theorem arithmeticFunctionCutoff_vonMangoldt_nonneg (V n : ℕ) :
    0 ≤ arithmeticFunctionCutoff Λ V n := by
  rw [arithmeticFunctionCutoff_apply]
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_rfl

theorem arithmeticFunctionCutoff_vonMangoldt_le (V n : ℕ) :
    arithmeticFunctionCutoff Λ V n ≤ Λ n := by
  rw [arithmeticFunctionCutoff_apply]
  split_ifs
  · exact le_rfl
  · exact vonMangoldt_nonneg

/-- The convolved Type I coefficient is bounded by the full Mangoldt divisor
sum, hence by `log n`.  This is the exact estimate behind the source's phrase
"since `1 * Λ = log`". -/
theorem abs_vaughanTypeIPrimeCoefficient_le_log (U V n : ℕ) :
    |vaughanTypeIPrimeCoefficient U V n| ≤ Real.log n := by
  rw [vaughanTypeIPrimeCoefficient, mul_apply]
  calc
    |∑ x ∈ n.divisorsAntidiagonal,
        arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U x.1 *
          arithmeticFunctionCutoff Λ V x.2| ≤
        ∑ x ∈ n.divisorsAntidiagonal,
          |arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U x.1 *
            arithmeticFunctionCutoff Λ V x.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ n.divisorsAntidiagonal, Λ x.2 := by
      apply Finset.sum_le_sum
      intro x _hx
      rw [abs_mul, abs_of_nonneg
        (arithmeticFunctionCutoff_vonMangoldt_nonneg V x.2)]
      calc
        |arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U x.1| *
            arithmeticFunctionCutoff Λ V x.2 ≤
            1 * arithmeticFunctionCutoff Λ V x.2 := by
          exact mul_le_mul_of_nonneg_right
            (abs_arithmeticFunctionCutoff_moebius_le_one U x.1)
            (arithmeticFunctionCutoff_vonMangoldt_nonneg V x.2)
        _ ≤ Λ x.2 := by
          simpa using arithmeticFunctionCutoff_vonMangoldt_le V x.2
    _ = ∑ i ∈ n.divisors, Λ i := by
      exact Nat.sum_divisorsAntidiagonal' (fun _ y => Λ y)
    _ = Real.log n := vonMangoldt_sum

theorem vaughanTypeIIGammaCoefficient_nonneg (V n : ℕ) :
    0 ≤ vaughanTypeIIGammaCoefficient V n := by
  rw [vaughanTypeIIGammaCoefficient, coe_mul_zeta_apply]
  exact Finset.sum_nonneg fun i _hi =>
    arithmeticFunctionTail_vonMangoldt_nonneg V i

theorem vaughanTypeIIGammaCoefficient_le_log (V n : ℕ) :
    vaughanTypeIIGammaCoefficient V n ≤ Real.log n := by
  rw [vaughanTypeIIGammaCoefficient, coe_mul_zeta_apply, ← vonMangoldt_sum]
  exact Finset.sum_le_sum fun i _hi => arithmeticFunctionTail_vonMangoldt_le V i

/-- Monotonicity of the real logarithm on positive natural arguments, in the
form used to replace `log n` by the ambient scale `log P`. -/
theorem log_natCast_mono {n P : ℕ} (hn : 1 ≤ n) (hP : n ≤ P) :
    Real.log n ≤ Real.log P := by
  exact Real.strictMonoOn_log.monotoneOn
    (show (0 : ℝ) < (n : ℝ) by exact_mod_cast (Nat.zero_lt_of_lt hn))
    (show (0 : ℝ) < (P : ℝ) by
      exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_of_lt hn) hP))
    (by exact_mod_cast hP)

/-- The first Type I coefficient has absolute value at most one. -/
theorem abs_vaughanTypeICoefficient_le_one (U n : ℕ) :
    |vaughanTypeICoefficient U n| ≤ 1 := by
  exact abs_arithmeticFunctionCutoff_moebius_le_one U n

/-- The second Type I coefficient has the source's `log P` envelope on
positive arguments at most `P`. -/
theorem abs_vaughanTypeIPrimeCoefficient_le_log_scale
    (U V n P : ℕ) (hn : 1 ≤ n) (hP : n ≤ P) :
    |vaughanTypeIPrimeCoefficient U V n| ≤ Real.log P :=
  (abs_vaughanTypeIPrimeCoefficient_le_log U V n).trans
    (log_natCast_mono hn hP)

/-- The Type II Möbius coefficient has absolute value at most one. -/
theorem abs_vaughanTypeIIBetaCoefficient_le_one (U n : ℕ) :
    |vaughanTypeIIBetaCoefficient U n| ≤ 1 := by
  rw [vaughanTypeIIBetaCoefficient, arithmeticFunctionTail_apply]
  split_ifs
  · calc
      |((μ n : ℤ) : ℝ)| = ((|μ n| : ℤ) : ℝ) := Int.cast_abs.symm
      _ ≤ (1 : ℝ) := by exact_mod_cast (abs_moebius_le_one (n := n))
  · simp

/-- The Type II divisor-sum coefficient has the source's `log P` envelope on
positive arguments at most `P`. -/
theorem abs_vaughanTypeIIGammaCoefficient_le_log_scale
    (V n P : ℕ) (hn : 1 ≤ n) (hP : n ≤ P) :
    |vaughanTypeIIGammaCoefficient V n| ≤ Real.log P := by
  rw [abs_of_nonneg (vaughanTypeIIGammaCoefficient_nonneg V n)]
  exact (vaughanTypeIIGammaCoefficient_le_log V n).trans
    (log_natCast_mono hn hP)

theorem vaughanTypeICoefficient_eq_zero_of_lt
    (U n : ℕ) (hn : U < n) :
    vaughanTypeICoefficient U n = 0 := by
  simp [vaughanTypeICoefficient, arithmeticFunctionCutoff_apply,
    Nat.not_le_of_lt hn]

/-- The second Type I coefficient is supported at products at most `U*V`. -/
theorem vaughanTypeIPrimeCoefficient_eq_zero_of_mul_lt
    (U V n : ℕ) (hn : U * V < n) :
    vaughanTypeIPrimeCoefficient U V n = 0 := by
  rw [vaughanTypeIPrimeCoefficient, mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rcases Nat.mem_divisorsAntidiagonal.mp hx with ⟨hprod, _hn0⟩
  by_cases hU : x.1 ≤ U
  · have hnotV : ¬x.2 ≤ V := by
      intro hV
      exact (Nat.not_le_of_lt hn) (hprod ▸ Nat.mul_le_mul hU hV)
    simp [arithmeticFunctionCutoff_apply, hnotV]
  · simp [arithmeticFunctionCutoff_apply, hU]

theorem vaughanTypeIIBetaCoefficient_eq_zero_of_le
    (U n : ℕ) (hn : n ≤ U) :
    vaughanTypeIIBetaCoefficient U n = 0 := by
  exact arithmeticFunctionTail_apply_of_le _ hn

/-- The Type II divisor-sum coefficient vanishes at and below the Mangoldt
cutoff. -/
theorem vaughanTypeIIGammaCoefficient_eq_zero_of_le
    (V n : ℕ) (hn : n ≤ V) :
    vaughanTypeIIGammaCoefficient V n = 0 := by
  rw [vaughanTypeIIGammaCoefficient, coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  apply arithmeticFunctionTail_apply_of_le
  rcases Nat.mem_divisors.mp hd with ⟨hdvd, hn0⟩
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd).trans hn

end Tao2026
