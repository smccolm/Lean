import Tao2026.VaughanCoefficients
import Tao2026.ShortIntervalDecomposition

/-!
# Finite convolution rearrangement

This module connects the divisor-antidiagonal form of Dirichlet convolution
used by `VaughanIdentity` to the product-restricted double sums used by the
Type I and Type II reductions.  The results are exact finite identities; no
analytic estimate is assumed.
-/

open Finset
open ArithmeticFunction
open scoped BigOperators
open scoped Moebius zeta

namespace Tao2026

/-- Product-box form of a weighted convolution sum. -/
noncomputable def weightedConvolutionProductSum
    (S : Finset ℕ) (B : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) : ℂ :=
  ∑ mn ∈ ((Finset.Ioc 0 B ×ˢ Finset.Ioc 0 B).filter
      (fun mn => mn.1 * mn.2 ∈ S)),
    ((f mn.1 : ℂ) * (g mn.2 : ℂ)) * w (mn.1 * mn.2)

/-- One quotient-block restriction of the outer coefficient in a bounded
product-restricted convolution sum. -/
noncomputable def weightedConvolutionProductBlockSum
    (S : Finset ℕ) (B q k : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) : ℂ :=
  ∑ mn ∈ ((Finset.Ioc 0 B ×ˢ Finset.Ioc 0 B).filter
      (fun mn => mn.1 * mn.2 ∈ S)),
    shortIntervalCoefficient (fun m => (f m : ℂ)) 1 (B + 1) q k mn.1 *
      (g mn.2 : ℂ) * w (mn.1 * mn.2)

/-- Exact shorter-than-dyadic decomposition of the outer coefficient in the
literal product-restricted convolution sum.  Membership in the product box
itself supplies the support interval `[1,B+1)`. -/
theorem weightedConvolutionProductSum_eq_sum_outerBlocks
    (S : Finset ℕ) (B q : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) (hq : 0 < q) :
    weightedConvolutionProductSum S B w f g =
      ∑ k ∈ Finset.range (shortIntervalBlockCount 1 (B + 1) q),
        weightedConvolutionProductBlockSum S B q k w f g := by
  classical
  unfold weightedConvolutionProductSum weightedConvolutionProductBlockSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mn hmn
  have hm : mn.1 ∈ Finset.Ico 1 (B + 1) := by
    have hmBox := (Finset.mem_product.mp (Finset.mem_filter.mp hmn).1).1
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ioc.mp hmBox).1,
      Nat.lt_succ_of_le (Finset.mem_Ioc.mp hmBox).2⟩
  calc
    (f mn.1 : ℂ) * (g mn.2 : ℂ) * w (mn.1 * mn.2) =
        (∑ k ∈ Finset.range (shortIntervalBlockCount 1 (B + 1) q),
          shortIntervalCoefficient (fun m => (f m : ℂ))
            1 (B + 1) q k mn.1) *
          (g mn.2 : ℂ) * w (mn.1 * mn.2) := by
      rw [sum_shortIntervalCoefficient (fun m => (f m : ℂ)) hq]
      simp [hm]
    _ = ∑ k ∈ Finset.range (shortIntervalBlockCount 1 (B + 1) q),
          shortIntervalCoefficient (fun m => (f m : ℂ))
            1 (B + 1) q k mn.1 *
          (g mn.2 : ℂ) * w (mn.1 * mn.2) := by
      simp_rw [Finset.sum_mul]

/-- One pair of quotient-block restrictions on the two coefficients in a
bounded product-restricted convolution sum. -/
noncomputable def weightedConvolutionProductDoubleBlockSum
    (S : Finset ℕ) (B q k l : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) : ℂ :=
  ∑ mn ∈ ((Finset.Ioc 0 B ×ˢ Finset.Ioc 0 B).filter
      (fun mn => mn.1 * mn.2 ∈ S)),
    shortIntervalCoefficient (fun m => (f m : ℂ)) 1 (B + 1) q k mn.1 *
      shortIntervalCoefficient (fun n => (g n : ℂ)) 1 (B + 1) q l mn.2 *
      w (mn.1 * mn.2)

/-- Exact inner-coefficient block decomposition of one outer block. -/
theorem weightedConvolutionProductBlockSum_eq_sum_innerBlocks
    (S : Finset ℕ) (B q k : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) (hq : 0 < q) :
    weightedConvolutionProductBlockSum S B q k w f g =
      ∑ l ∈ Finset.range (shortIntervalBlockCount 1 (B + 1) q),
        weightedConvolutionProductDoubleBlockSum S B q k l w f g := by
  classical
  unfold weightedConvolutionProductBlockSum
    weightedConvolutionProductDoubleBlockSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mn hmn
  have hn : mn.2 ∈ Finset.Ico 1 (B + 1) := by
    have hnBox := (Finset.mem_product.mp (Finset.mem_filter.mp hmn).1).2
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ioc.mp hnBox).1,
      Nat.lt_succ_of_le (Finset.mem_Ioc.mp hnBox).2⟩
  calc
    shortIntervalCoefficient (fun m => (f m : ℂ))
          1 (B + 1) q k mn.1 *
        (g mn.2 : ℂ) * w (mn.1 * mn.2) =
      shortIntervalCoefficient (fun m => (f m : ℂ))
          1 (B + 1) q k mn.1 *
        (∑ l ∈ Finset.range (shortIntervalBlockCount 1 (B + 1) q),
          shortIntervalCoefficient (fun n => (g n : ℂ))
            1 (B + 1) q l mn.2) * w (mn.1 * mn.2) := by
      rw [sum_shortIntervalCoefficient (fun n => (g n : ℂ)) hq]
      simp [hn]
    _ = ∑ l ∈ Finset.range (shortIntervalBlockCount 1 (B + 1) q),
        shortIntervalCoefficient (fun m => (f m : ℂ))
            1 (B + 1) q k mn.1 *
          shortIntervalCoefficient (fun n => (g n : ℂ))
            1 (B + 1) q l mn.2 * w (mn.1 * mn.2) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]

/-- Exact double shorter-than-dyadic decomposition of a bounded
product-restricted convolution sum. -/
theorem weightedConvolutionProductSum_eq_sum_doubleBlocks
    (S : Finset ℕ) (B q : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) (hq : 0 < q) :
    weightedConvolutionProductSum S B w f g =
      ∑ k ∈ Finset.range (shortIntervalBlockCount 1 (B + 1) q),
        ∑ l ∈ Finset.range (shortIntervalBlockCount 1 (B + 1) q),
          weightedConvolutionProductDoubleBlockSum S B q k l w f g := by
  rw [weightedConvolutionProductSum_eq_sum_outerBlocks S B q w f g hq]
  apply Finset.sum_congr rfl
  intro k _hk
  exact weightedConvolutionProductBlockSum_eq_sum_innerBlocks
    S B q k w f g hq

/-- One canonical polynomial-logarithmic Vaughan block restriction on the
outer coefficient of a product sum. -/
noncomputable def weightedConvolutionProductVaughanBlockSum
    (S : Finset ℕ) (B : ℕ) (sk : ℕ × ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) : ℂ :=
  ∑ mn ∈ ((Finset.Ioc 0 B ×ˢ Finset.Ioc 0 B).filter
      (fun mn => mn.1 * mn.2 ∈ S)),
    vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk mn.1 *
      (g mn.2 : ℂ) * w (mn.1 * mn.2)

/-- One pair of canonical polynomial-logarithmic Vaughan block restrictions
on a product sum. -/
noncomputable def weightedConvolutionProductVaughanDoubleBlockSum
    (S : Finset ℕ) (B : ℕ) (sk tl : ℕ × ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) : ℂ :=
  ∑ mn ∈ ((Finset.Ioc 0 B ×ˢ Finset.Ioc 0 B).filter
      (fun mn => mn.1 * mn.2 ∈ S)),
    vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk mn.1 *
      vaughanShortIntervalCoefficient (fun n => (g n : ℂ)) B tl mn.2 *
      w (mn.1 * mn.2)

/-- Exact decomposition of a product sum into the explicit family of
`(log₂ B+1)^102` outer Vaughan blocks. -/
theorem weightedConvolutionProductSum_eq_sum_vaughanOuterBlocks
    (S : Finset ℕ) (B : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) :
    weightedConvolutionProductSum S B w f g =
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        weightedConvolutionProductVaughanBlockSum S B sk w f g := by
  classical
  unfold weightedConvolutionProductSum
    weightedConvolutionProductVaughanBlockSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mn hmn
  have hmBox := (Finset.mem_product.mp (Finset.mem_filter.mp hmn).1).1
  have hm : 0 < mn.1 ∧ mn.1 ≤ B := Finset.mem_Ioc.mp hmBox
  calc
    (f mn.1 : ℂ) * (g mn.2 : ℂ) * w (mn.1 * mn.2) =
        (∑ sk ∈ vaughanShortIntervalIndexBox B,
          vaughanShortIntervalCoefficient (fun m => (f m : ℂ))
            B sk mn.1) * (g mn.2 : ℂ) * w (mn.1 * mn.2) := by
      rw [sum_vaughanShortIntervalCoefficient
        (fun m => (f m : ℂ)) hm.1 hm.2]
    _ = ∑ sk ∈ vaughanShortIntervalIndexBox B,
        vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk mn.1 *
          (g mn.2 : ℂ) * w (mn.1 * mn.2) := by
      simp_rw [Finset.sum_mul]

/-- Exact inner-family decomposition of one canonical Vaughan outer block. -/
theorem weightedConvolutionProductVaughanBlockSum_eq_sum_innerBlocks
    (S : Finset ℕ) (B : ℕ) (sk : ℕ × ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) :
    weightedConvolutionProductVaughanBlockSum S B sk w f g =
      ∑ tl ∈ vaughanShortIntervalIndexBox B,
        weightedConvolutionProductVaughanDoubleBlockSum
          S B sk tl w f g := by
  classical
  unfold weightedConvolutionProductVaughanBlockSum
    weightedConvolutionProductVaughanDoubleBlockSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mn hmn
  have hnBox := (Finset.mem_product.mp (Finset.mem_filter.mp hmn).1).2
  have hn : 0 < mn.2 ∧ mn.2 ≤ B := Finset.mem_Ioc.mp hnBox
  calc
    vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk mn.1 *
        (g mn.2 : ℂ) * w (mn.1 * mn.2) =
      vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk mn.1 *
        (∑ tl ∈ vaughanShortIntervalIndexBox B,
          vaughanShortIntervalCoefficient (fun n => (g n : ℂ))
            B tl mn.2) * w (mn.1 * mn.2) := by
      rw [sum_vaughanShortIntervalCoefficient
        (fun n => (g n : ℂ)) hn.1 hn.2]
    _ = ∑ tl ∈ vaughanShortIntervalIndexBox B,
        vaughanShortIntervalCoefficient (fun m => (f m : ℂ)) B sk mn.1 *
          vaughanShortIntervalCoefficient (fun n => (g n : ℂ)) B tl mn.2 *
          w (mn.1 * mn.2) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]

/-- Exact double decomposition into the two counted canonical Vaughan short
families, retaining the literal product restriction. -/
theorem weightedConvolutionProductSum_eq_sum_vaughanDoubleBlocks
    (S : Finset ℕ) (B : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) :
    weightedConvolutionProductSum S B w f g =
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ tl ∈ vaughanShortIntervalIndexBox B,
          weightedConvolutionProductVaughanDoubleBlockSum
            S B sk tl w f g := by
  rw [weightedConvolutionProductSum_eq_sum_vaughanOuterBlocks]
  apply Finset.sum_congr rfl
  intro sk _hsk
  exact weightedConvolutionProductVaughanBlockSum_eq_sum_innerBlocks
    S B sk w f g

/-- A weighted divisor-pair sum over a finite set of positive integers can be
reindexed as a product-box sum with the literal restriction `m * n ∈ S`.
The box bound is explicit, so no hidden finite-support convention is used. -/
theorem sum_divisorsAntidiagonal_eq_sum_product_filter
    {A : Type*} [CommSemiring A] (S : Finset ℕ) (B : ℕ)
    (f g w : ℕ → A)
    (hpos : ∀ x ∈ S, x ≠ 0) (hB : ∀ x ∈ S, x ≤ B) :
    ∑ x ∈ S, ∑ mn ∈ x.divisorsAntidiagonal,
        f mn.1 * g mn.2 * w x =
      ∑ mn ∈ ((Finset.Ioc 0 B ×ˢ Finset.Ioc 0 B).filter
          (fun mn => mn.1 * mn.2 ∈ S)),
        f mn.1 * g mn.2 * w (mn.1 * mn.2) := by
  classical
  let box : Finset (ℕ × ℕ) := Finset.Ioc 0 B ×ˢ Finset.Ioc 0 B
  calc
    ∑ x ∈ S, ∑ mn ∈ x.divisorsAntidiagonal,
        f mn.1 * g mn.2 * w x =
        ∑ x ∈ S, ∑ mn ∈ box,
          if mn.1 * mn.2 = x then f mn.1 * g mn.2 * w x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (hpos x hx) (hB x hx)]
      simp only [box, Finset.sum_filter]
    _ = ∑ mn ∈ box, ∑ x ∈ S,
          if mn.1 * mn.2 = x then f mn.1 * g mn.2 * w x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ mn ∈ box,
          if mn.1 * mn.2 ∈ S then
            f mn.1 * g mn.2 * w (mn.1 * mn.2) else 0 := by
      apply Finset.sum_congr rfl
      intro mn _hmn
      by_cases hmem : mn.1 * mn.2 ∈ S
      · simp [hmem]
      · simp [hmem]
    _ = ∑ mn ∈ (box.filter (fun mn => mn.1 * mn.2 ∈ S)),
          f mn.1 * g mn.2 * w (mn.1 * mn.2) := by
      simp only [Finset.sum_filter]
    _ = _ := rfl

/-- The preceding rearrangement specialized to the real arithmetic-function
coefficients and complex weights used by `weightedRealArithmeticSum`. -/
theorem weightedRealArithmeticSum_dirichletPairSum_eq_product_filter
    (S : Finset ℕ) (B : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ)
    (hpos : ∀ x ∈ S, x ≠ 0) (hB : ∀ x ∈ S, x ≤ B) :
    weightedRealArithmeticSum S w (dirichletPairSum f g) =
      ∑ mn ∈ ((Finset.Ioc 0 B ×ˢ Finset.Ioc 0 B).filter
          (fun mn => mn.1 * mn.2 ∈ S)),
        ((f mn.1 : ℂ) * (g mn.2 : ℂ)) * w (mn.1 * mn.2) := by
  simpa only [weightedRealArithmeticSum, dirichletPairSum,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul] using
    (sum_divisorsAntidiagonal_eq_sum_product_filter S B
      (fun n => (f n : ℂ)) (fun n => (g n : ℂ)) w hpos hB)

/-- Named product-sum version of the exact pair-convolution rearrangement. -/
theorem weightedRealArithmeticSum_dirichletPairSum_eq_productSum
    (S : Finset ℕ) (B : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ)
    (hpos : ∀ x ∈ S, x ≠ 0) (hB : ∀ x ∈ S, x ≤ B) :
    weightedRealArithmeticSum S w (dirichletPairSum f g) =
      weightedConvolutionProductSum S B w f g := by
  exact weightedRealArithmeticSum_dirichletPairSum_eq_product_filter
    S B w f g hpos hB

/-- Product-sum rearrangement stated directly for Dirichlet convolution. -/
theorem weightedRealArithmeticSum_dirichletConvolution_eq_productSum
    (S : Finset ℕ) (B : ℕ) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ)
    (hpos : ∀ x ∈ S, x ≠ 0) (hB : ∀ x ∈ S, x ≤ B) :
    weightedRealArithmeticSum S w ((f * g) : ArithmeticFunction ℝ) =
      weightedConvolutionProductSum S B w f g := by
  change weightedRealArithmeticSum S w (dirichletPairSum f g) = _
  exact weightedRealArithmeticSum_dirichletPairSum_eq_productSum
    S B w f g hpos hB

/-- The nested triple sum in Vaughan's identity is definitionally the pair
sum whose first coefficient is the convolution of the first two factors. -/
theorem dirichletTripleSum_eq_pairSum_convolution
    (f g h : ArithmeticFunction ℝ) (n : ℕ) :
    dirichletTripleSum f g h n = dirichletPairSum (f * g) h n :=
  rfl

/-- Interval form of the exact convolution rearrangement.  Positivity of the
left endpoint excludes the conventional empty antidiagonal at zero. -/
theorem weightedRealArithmeticSum_dirichletPairSum_Ico
    {a b : ℕ} (ha : 0 < a) (w : ℕ → ℂ)
    (f g : ArithmeticFunction ℝ) :
    weightedRealArithmeticSum (Finset.Ico a b) w (dirichletPairSum f g) =
      ∑ mn ∈ ((Finset.Ioc 0 b ×ˢ Finset.Ioc 0 b).filter
          (fun mn => mn.1 * mn.2 ∈ Finset.Ico a b)),
        ((f mn.1 : ℂ) * (g mn.2 : ℂ)) * w (mn.1 * mn.2) := by
  apply weightedRealArithmeticSum_dirichletPairSum_eq_product_filter
  · intro x hx
    rw [Finset.mem_Ico] at hx
    omega
  · intro x hx
    rw [Finset.mem_Ico] at hx
    omega

/-- Every threefold Vaughan term has the same literal two-variable product
restriction after associating its first two arithmetic coefficients. -/
theorem weightedRealArithmeticSum_dirichletTripleSum_Ico
    {a b : ℕ} (ha : 0 < a) (w : ℕ → ℂ)
    (f g h : ArithmeticFunction ℝ) :
    weightedRealArithmeticSum (Finset.Ico a b) w
        (dirichletTripleSum f g h) =
      weightedConvolutionProductSum (Finset.Ico a b) b w (f * g) h := by
  rw [show dirichletTripleSum f g h = dirichletPairSum (f * g) h from
    funext (dirichletTripleSum_eq_pairSum_convolution f g h)]
  exact weightedRealArithmeticSum_dirichletPairSum_eq_productSum
    (Finset.Ico a b) b w (f * g) h
      (by
        intro x hx
        rw [Finset.mem_Ico] at hx
        omega)
      (by
        intro x hx
        rw [Finset.mem_Ico] at hx
        omega)

/-- Vaughan's identity for the reciprocal phase, with all three convolution
terms expressed as literal product-restricted double sums.  This is the
finite algebraic interface expected by the Type I/II estimates. -/
theorem mangoldtReciprocalPhaseSum_vaughan_product_restricted
    (N M : ℝ) (j : ℕ) {a b : ℕ} (ha : 0 < a) (U V : ℕ) :
    mangoldtReciprocalPhaseSum N M j a b =
      weightedRealArithmeticSum (Finset.Ico a b)
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (arithmeticFunctionCutoff Λ V) +
      weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U) log -
      weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (arithmeticFunctionCutoff (μ : ArithmeticFunction ℝ) U *
          arithmeticFunctionCutoff Λ V) (ζ : ArithmeticFunction ℝ) +
      weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (arithmeticFunctionTail (μ : ArithmeticFunction ℝ) U *
          arithmeticFunctionTail Λ V) (ζ : ArithmeticFunction ℝ) := by
  rw [mangoldtReciprocalPhaseSum_vaughan N M j a b U V]
  rw [weightedRealArithmeticSum_dirichletPairSum_Ico ha]
  rw [weightedRealArithmeticSum_dirichletTripleSum_Ico ha]
  rw [weightedRealArithmeticSum_dirichletTripleSum_Ico ha]
  rfl

/-- The source-oriented Vaughan decomposition, with the actual Type I and
Type II coefficient pairs and the literal restriction `m*n ∈ [a,b)`. -/
theorem mangoldtReciprocalPhaseSum_vaughan_source_product_restricted
    (N M : ℝ) (j : ℕ) {a b : ℕ} (ha : 0 < a) (U V : ℕ) :
    mangoldtReciprocalPhaseSum N M j a b =
      weightedRealArithmeticSum (Finset.Ico a b)
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (arithmeticFunctionCutoff Λ V) +
      weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeICoefficient U) log -
      weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ) +
      weightedConvolutionProductSum (Finset.Ico a b) b
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIIBetaCoefficient U)
        (vaughanTypeIIGammaCoefficient V) := by
  unfold mangoldtReciprocalPhaseSum
  rw [weightedVaughanIdentity_sourceCoefficients]
  rw [weightedRealArithmeticSum_dirichletConvolution_eq_productSum]
  rw [weightedRealArithmeticSum_dirichletConvolution_eq_productSum]
  rw [weightedRealArithmeticSum_dirichletConvolution_eq_productSum]
  all_goals
    intro x hx
    rw [Finset.mem_Ico] at hx
    omega

/-- Proposition 1.12's complete finite Vaughan-family decomposition before
analytic estimation: both Type I terms use the explicit counted outer family,
the Type II term uses its square, and every summand retains `m*n∈[a,b)`. -/
theorem mangoldtReciprocalPhaseSum_vaughan_source_shortFamilies
    (N M : ℝ) (j : ℕ) {a b : ℕ} (ha : 0 < a) (U V : ℕ) :
    mangoldtReciprocalPhaseSum N M j a b =
      weightedRealArithmeticSum (Finset.Ico a b)
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (arithmeticFunctionCutoff Λ V) +
      (∑ sk ∈ vaughanShortIntervalIndexBox b,
        weightedConvolutionProductVaughanBlockSum (Finset.Ico a b) b sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeICoefficient U) log) -
      (∑ sk ∈ vaughanShortIntervalIndexBox b,
        weightedConvolutionProductVaughanBlockSum (Finset.Ico a b) b sk
          (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
          (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)) +
      ∑ sk ∈ vaughanShortIntervalIndexBox b,
        ∑ tl ∈ vaughanShortIntervalIndexBox b,
          weightedConvolutionProductVaughanDoubleBlockSum
            (Finset.Ico a b) b sk tl
            (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient V) := by
  rw [mangoldtReciprocalPhaseSum_vaughan_source_product_restricted
    N M j ha U V]
  rw [weightedConvolutionProductSum_eq_sum_vaughanOuterBlocks]
  rw [weightedConvolutionProductSum_eq_sum_vaughanOuterBlocks]
  rw [weightedConvolutionProductSum_eq_sum_vaughanDoubleBlocks]

end Tao2026
