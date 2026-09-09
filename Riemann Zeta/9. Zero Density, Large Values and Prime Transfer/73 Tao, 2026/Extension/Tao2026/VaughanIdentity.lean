import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Tao2026.VinogradovPhase

/-!
# Vaughan's identity

This module proves the exact arithmetic-function decomposition used in the
proof of Proposition 1.12 of the pinned Singmaster paper.  No estimate is
asserted here: the result is the algebraic identity which separates the later
prime exponential sum into its short, Type I, and Type II pieces.
-/

namespace Tao2026

open ArithmeticFunction
open scoped Moebius zeta

/-- Restrict an arithmetic function to arguments at most `X`. -/
def arithmeticFunctionCutoff {R : Type*} [Zero R]
    (f : ArithmeticFunction R) (X : ℕ) : ArithmeticFunction R :=
  ⟨fun n => if n ≤ X then f n else 0, by simp⟩

@[simp]
theorem arithmeticFunctionCutoff_apply {R : Type*} [Zero R]
    (f : ArithmeticFunction R) (X n : ℕ) :
    arithmeticFunctionCutoff f X n = if n ≤ X then f n else 0 :=
  rfl

/-- The complementary tail of an arithmetic function above `X`. -/
def arithmeticFunctionTail {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) (X : ℕ) : ArithmeticFunction R :=
  f - arithmeticFunctionCutoff f X

theorem arithmeticFunctionCutoff_add_tail {R : Type*} [AddCommGroup R]
    (f : ArithmeticFunction R) (X : ℕ) :
    arithmeticFunctionCutoff f X + arithmeticFunctionTail f X = f := by
  ext n
  simp [arithmeticFunctionTail, sub_eq_add_neg]

@[simp]
theorem arithmeticFunctionTail_apply_of_le {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) {X n : ℕ} (hn : n ≤ X) :
    arithmeticFunctionTail f X n = 0 := by
  simp [arithmeticFunctionTail, sub_eq_add_neg, hn]

@[simp]
theorem arithmeticFunctionTail_apply_of_lt {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) {X n : ℕ} (hn : X < n) :
    arithmeticFunctionTail f X n = f n := by
  simp [arithmeticFunctionTail, sub_eq_add_neg, Nat.not_le_of_lt hn]

/-- The finite divisor-pair sum underlying one Dirichlet convolution. -/
def dirichletPairSum {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) (n : ℕ) : R :=
  ∑ xy ∈ n.divisorsAntidiagonal, f xy.1 * g xy.2

/-- The finite nested divisor sum underlying a threefold Dirichlet
convolution, associated as `(f * g) * h`. -/
def dirichletTripleSum {R : Type*} [Semiring R]
    (f g h : ArithmeticFunction R) (n : ℕ) : R :=
  ∑ xy ∈ n.divisorsAntidiagonal,
    (∑ ab ∈ xy.1.divisorsAntidiagonal, f ab.1 * g ab.2) * h xy.2

theorem dirichletConvolution_apply_eq_pairSum {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) (n : ℕ) :
    (f * g) n = dirichletPairSum f g n :=
  rfl

theorem dirichletTripleConvolution_apply_eq_tripleSum
    {R : Type*} [Semiring R]
    (f g h : ArithmeticFunction R) (n : ℕ) :
    (f * g * h) n = dirichletTripleSum f g h n :=
  rfl

/-- Vaughan's identity, with `1` in the analytic-number-theory notation
represented by the zeta arithmetic function.  Thus every multiplication in
the formula is Dirichlet convolution.

This is the precise algebraic decomposition invoked in Proposition 1.12 of
the pinned source before its Type I/II estimates. -/
theorem vaughanIdentity (U V : ℕ) :
    Λ =
      arithmeticFunctionCutoff Λ V +
        arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U * log -
        arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U *
          arithmeticFunctionCutoff Λ V * (ζ : ArithmeticFunction ℝ) +
        arithmeticFunctionTail (μ : ArithmeticFunction ℝ) U *
          arithmeticFunctionTail Λ V * (ζ : ArithmeticFunction ℝ) := by
  let μ₀ := arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U
  let μ₁ := arithmeticFunctionTail (μ : ArithmeticFunction ℝ) U
  let Λ₀ := arithmeticFunctionCutoff Λ V
  let Λ₁ := arithmeticFunctionTail Λ V
  have hμ : μ₀ + μ₁ = (μ : ArithmeticFunction ℝ) :=
    arithmeticFunctionCutoff_add_tail _ _
  have hΛ : Λ₀ + Λ₁ = Λ :=
    arithmeticFunctionCutoff_add_tail _ _
  change Λ = Λ₀ + μ₀ * log - μ₀ * Λ₀ * ζ + μ₁ * Λ₁ * ζ
  calc
    Λ = Λ₀ + Λ₁ := hΛ.symm
    _ = Λ₀ + ((μ : ArithmeticFunction ℝ) * ζ) * Λ₁ := by
      rw [show (μ : ArithmeticFunction ℝ) * ζ = 1 from
        coe_moebius_mul_coe_zeta]
      simp
    _ = Λ₀ + (μ₀ + μ₁) * ζ * Λ₁ := by rw [hμ]
    _ = Λ₀ + μ₀ * ((Λ₀ + Λ₁) * ζ) - μ₀ * Λ₀ * ζ + μ₁ * Λ₁ * ζ := by
      ring
    _ = Λ₀ + μ₀ * log - μ₀ * Λ₀ * ζ + μ₁ * Λ₁ * ζ := by
      rw [hΛ, show Λ * ζ = log from vonMangoldt_mul_zeta]

/-- The exact finite-divisor-sum expansion of Vaughan's identity.  This is
the pointwise form to which the subsequent Type I and Type II estimates are
applied. -/
theorem vaughanIdentity_apply (U V n : ℕ) :
    Λ n =
      arithmeticFunctionCutoff Λ V n +
        dirichletPairSum (arithmeticFunctionCutoff
          (μ : ArithmeticFunction ℝ) U) log n -
        dirichletTripleSum (arithmeticFunctionCutoff
          (μ : ArithmeticFunction ℝ) U)
          (arithmeticFunctionCutoff Λ V) (ζ : ArithmeticFunction ℝ) n +
        dirichletTripleSum (arithmeticFunctionTail
          (μ : ArithmeticFunction ℝ) U)
          (arithmeticFunctionTail Λ V) (ζ : ArithmeticFunction ℝ) n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (vaughanIdentity U V)
  simpa [sub_eq_add_neg, dirichletPairSum, dirichletTripleSum] using h

/-- A finite complex-weighted sum of a real arithmetic sequence. -/
noncomputable def weightedRealArithmeticSum (S : Finset ℕ) (w : ℕ → ℂ)
    (f : ℕ → ℝ) : ℂ :=
  ∑ n ∈ S, (f n : ℂ) * w n

/-- Vaughan's identity after multiplication by an arbitrary complex weight
and summation over an arbitrary finite set.  This is the exact decomposition
used before estimating the source's reciprocal-phase exponential sums. -/
theorem weightedVaughanIdentity (S : Finset ℕ) (w : ℕ → ℂ) (U V : ℕ) :
    weightedRealArithmeticSum S w Λ =
      weightedRealArithmeticSum S w (arithmeticFunctionCutoff Λ V) +
        weightedRealArithmeticSum S w
          (dirichletPairSum (arithmeticFunctionCutoff
            (μ : ArithmeticFunction ℝ) U) log) -
        weightedRealArithmeticSum S w
          (dirichletTripleSum (arithmeticFunctionCutoff
            (μ : ArithmeticFunction ℝ) U)
            (arithmeticFunctionCutoff Λ V) (ζ : ArithmeticFunction ℝ)) +
        weightedRealArithmeticSum S w
          (dirichletTripleSum (arithmeticFunctionTail
            (μ : ArithmeticFunction ℝ) U)
            (arithmeticFunctionTail Λ V) (ζ : ArithmeticFunction ℝ)) := by
  unfold weightedRealArithmeticSum
  calc
    (∑ n ∈ S, (Λ n : ℂ) * w n) =
        ∑ n ∈ S,
          ((arithmeticFunctionCutoff Λ V n +
              dirichletPairSum (arithmeticFunctionCutoff
                (μ : ArithmeticFunction ℝ) U) log n -
              dirichletTripleSum (arithmeticFunctionCutoff
                (μ : ArithmeticFunction ℝ) U)
                (arithmeticFunctionCutoff Λ V)
                (ζ : ArithmeticFunction ℝ) n +
              dirichletTripleSum (arithmeticFunctionTail
                (μ : ArithmeticFunction ℝ) U)
                (arithmeticFunctionTail Λ V)
                (ζ : ArithmeticFunction ℝ) n : ℝ) : ℂ) * w n := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [vaughanIdentity_apply U V n]
    _ = _ := by
      simp only [Complex.ofReal_add, Complex.ofReal_sub, add_mul, sub_mul,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The von Mangoldt weighted reciprocal-phase sum on `[a,b)`. -/
noncomputable def mangoldtReciprocalPhaseSum
    (N M : ℝ) (j a b : ℕ) : ℂ :=
  weightedRealArithmeticSum (Finset.Ico a b)
    (fun n => standardAdditiveCharacter (reciprocalPhase N M j n)) Λ

/-- The exact Vaughan decomposition specialized to the reciprocal phase and
half-open interval used by the integer and prime exponential-sum arguments. -/
theorem mangoldtReciprocalPhaseSum_vaughan
    (N M : ℝ) (j a b U V : ℕ) :
    mangoldtReciprocalPhaseSum N M j a b =
      weightedRealArithmeticSum (Finset.Ico a b)
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (arithmeticFunctionCutoff Λ V) +
      weightedRealArithmeticSum (Finset.Ico a b)
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (dirichletPairSum (arithmeticFunctionCutoff
          (μ : ArithmeticFunction ℝ) U) log) -
      weightedRealArithmeticSum (Finset.Ico a b)
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (dirichletTripleSum (arithmeticFunctionCutoff
          (μ : ArithmeticFunction ℝ) U)
          (arithmeticFunctionCutoff Λ V) (ζ : ArithmeticFunction ℝ)) +
      weightedRealArithmeticSum (Finset.Ico a b)
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (dirichletTripleSum (arithmeticFunctionTail
          (μ : ArithmeticFunction ℝ) U)
          (arithmeticFunctionTail Λ V) (ζ : ArithmeticFunction ℝ)) := by
  exact weightedVaughanIdentity (Finset.Ico a b)
    (fun n => standardAdditiveCharacter (reciprocalPhase N M j n)) U V

end Tao2026
