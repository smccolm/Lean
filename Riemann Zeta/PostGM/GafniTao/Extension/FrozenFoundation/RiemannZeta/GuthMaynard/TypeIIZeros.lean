import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RiemannZeta.GuthMaynard.ZeroDetector

open Asymptotics Filter MeasureTheory
open Complex
open scoped BigOperators Interval
open Classical

namespace RiemannZeta.GuthMaynard

/-- The short Möbius polynomial `M(s)` in Maynard--Pratt Definition 22. -/
noncomputable def shortMobiusPolynomial (T : ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Ico 1 (detectorCutoff T),
    (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)

/-- The real-line parameterization of the vertical contour through `1/2 - Re ρ`. -/
noncomputable def typeIIContourShift (ρ : ℂ) (u : ℝ) : ℂ :=
  ((1 / 2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * I

/-- The integrand in the Maynard--Pratt Type II contour detector. -/
noncomputable def typeIIContourIntegrand (ρ : ℂ) (T u : ℝ) : ℂ :=
  let s := typeIIContourShift ρ u
  (T : ℂ) ^ (s / 2) * Complex.Gamma s *
    shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s)

/--
The vertical contour detector in Maynard--Pratt Definition 22, parameterized by
`s = 1/2 - Re ρ + iu`. The factor `1/(2π)` includes `ds = i du`.
-/
noncomputable def typeIIContourIntegral (ρ : ℂ) (T : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ u : ℝ, typeIIContourIntegrand ρ T u)

/-- The genuine contour-integral Type II condition from Maynard--Pratt Definition 22. -/
def IsContourTypeIIZero (ρ : ℂ) (T : ℝ) : Prop :=
  (1 / 3 : ℝ) ≤ ‖typeIIContourIntegral ρ T‖

/--
Source-level Type-I/Type-II coverage above a specified real-part threshold.
It is stated separately from the residual class `¬ IsTypeIZero`.
-/
def TypeIContourTypeIICoverOnProp (σ₀ : ℝ) : Prop :=
  ∃ T₀ : ℝ, 2 ≤ T₀ ∧
    ∀ (T : ℝ), T₀ ≤ T → ∀ (ρ : ℂ),
      ρ ∈ ZeroRectangle σ₀ 1 T (2 * T) → riemannZeta ρ = 0 →
        IsTypeIZero ρ T ∨ IsContourTypeIIZero ρ T

/--
The source-range Type-I/Type-II coverage needed by the Section 13.1 transfer.
The lower threshold `7/10` stays strictly inside the Appendix C range
`Re ρ ≥ 1/2 + 1 / log T` for all sufficiently large `T`.
-/
def TypeIContourTypeIICoverProp : Prop :=
  TypeIContourTypeIICoverOnProp (7 / 10)

/-- The fourth-moment integrand used in the proof of Maynard--Pratt Lemma 24. -/
noncomputable def twistedZetaMomentIntegrand (T t : ℝ) : ℝ :=
  ‖shortMobiusPolynomial T ((1 / 2 : ℂ) + (t : ℂ) * I) *
    riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 4

/-- The twisted fourth moment over the interval appearing in Appendix C. -/
noncomputable def twistedZetaFourthMoment (T : ℝ) : ℝ :=
  ∫ t in T / 2..3 * T, twistedZetaMomentIntegrand T t

/--
The source's twisted fourth-moment input, with logarithmic losses represented
by the project's epsilon-power convention.
-/
def TwistedZetaFourthMomentProp : Prop :=
  EpsilonPowerBound twistedZetaFourthMoment (fun T => T)

/-- A weighted finite count selected by a `T`-dependent predicate. -/
noncomputable def weightedCount {α : Type*} (Z : ℝ → ℝ → Finset α)
    (multiplicity : α → ℕ) (P : ℝ → α → Prop) (σ T : ℝ) : ℝ :=
  ∑ x ∈ (Z σ T).filter (P T), (multiplicity x : ℝ)

/-- The weighted residual count for the complement of a Type-I predicate. -/
noncomputable def weightedResidualCount {α : Type*} (Z : ℝ → ℝ → Finset α)
    (multiplicity : α → ℕ) (isTypeI : ℝ → α → Prop) (σ T : ℝ) : ℝ :=
  weightedCount Z multiplicity (fun U x => ¬ isTypeI U x) σ T

/--
Type-I/Type-II coverage on generic finite zero data in the source σ-range.
Coverage is eventual in the height parameter, matching the source theorem and
the eventual nature of `EpsilonPowerBound`.
-/
def FiniteTypeICoverProp {α : Type*} (Z : ℝ → ℝ → Finset α)
    (isTypeI isTypeII : ℝ → α → Prop) : Prop :=
  ∀ (σ : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    ∀ᶠ T : ℝ in atTop, ∀ x : α, x ∈ Z σ T →
      isTypeI T x ∨ isTypeII T x

/--
The Appendix C reduction from the genuine Type II count to the scaled twisted
fourth moment. Gamma decay, Hölder, separated extraction, and local multiplicity
control belong in a proof of this source-specific proposition.
-/
def TypeIIFourthMomentReductionProp {α : Type*} (Z : ℝ → ℝ → Finset α)
    (multiplicity : α → ℕ) (isTypeII : ℝ → α → Prop) : Prop :=
  ∀ (σ : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    EpsilonPowerBound
      (fun T => weightedCount Z multiplicity isTypeII σ T)
      (fun T => T ^ (1 - 2 * σ) * twistedZetaFourthMoment T)

/-- Generic residual-zero target corresponding to `ResidualZeroBoundProp`. -/
def FiniteResidualZeroBoundProp {α : Type*} (Z : ℝ → ℝ → Finset α)
    (multiplicity : α → ℕ) (isTypeI : ℝ → α → Prop) : Prop :=
  ∀ (σ : ℝ), 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    EpsilonPowerBound
      (fun T => weightedResidualCount Z multiplicity isTypeI σ T)
      (fun T => T ^ (2 - 2 * σ))

/-- A residual finite count is bounded by the genuine Type II count under coverage. -/
theorem weightedResidualCount_le_weightedCount_of_cover {α : Type*}
    (Z : ℝ → ℝ → Finset α) (multiplicity : α → ℕ)
    (isTypeI isTypeII : ℝ → α → Prop)
    (σ T : ℝ)
    (hCover : ∀ x : α, x ∈ Z σ T → isTypeI T x ∨ isTypeII T x) :
    weightedResidualCount Z multiplicity isTypeI σ T ≤
      weightedCount Z multiplicity isTypeII σ T := by
  unfold weightedResidualCount weightedCount
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, (hCover x hx.1).resolve_left hx.2⟩
  · intro x _ _
    positivity

/-- Coverage alone gives an epsilon-power comparison of residual and Type II counts. -/
theorem residual_epsilonPowerBound_of_cover {α : Type*}
    (Z : ℝ → ℝ → Finset α) (multiplicity : α → ℕ)
    (isTypeI isTypeII : ℝ → α → Prop)
    (hCover : FiniteTypeICoverProp Z isTypeI isTypeII)
    (σ : ℝ) (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5) :
    EpsilonPowerBound
      (fun T => weightedResidualCount Z multiplicity isTypeI σ T)
      (fun T => weightedCount Z multiplicity isTypeII σ T) := by
  intro ε hε
  apply IsBigO.of_bound 1
  filter_upwards [hCover σ hσLower hσUpper, eventually_ge_atTop (1 : ℝ)]
    with T hCoverT hT
  have hResidualNonneg : 0 ≤ weightedResidualCount Z multiplicity isTypeI σ T := by
    unfold weightedResidualCount weightedCount
    positivity
  have hTypeIINonneg : 0 ≤ weightedCount Z multiplicity isTypeII σ T := by
    unfold weightedCount
    positivity
  have hPow : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  rw [Real.norm_eq_abs, abs_abs]
  have hTargetNorm :
      ‖T ^ ε * |weightedCount Z multiplicity isTypeII σ T|‖ =
        T ^ ε * |weightedCount Z multiplicity isTypeII σ T| := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  rw [hTargetNorm, one_mul, abs_of_nonneg hResidualNonneg]
  calc
    weightedResidualCount Z multiplicity isTypeI σ T
        ≤ weightedCount Z multiplicity isTypeII σ T :=
      weightedResidualCount_le_weightedCount_of_cover
        Z multiplicity isTypeI isTypeII σ T hCoverT
    _ = 1 * |weightedCount Z multiplicity isTypeII σ T| := by
      rw [abs_of_nonneg hTypeIINonneg, one_mul]
    _ ≤ T ^ ε * |weightedCount Z multiplicity isTypeII σ T| :=
      mul_le_mul_of_nonneg_right hPow (abs_nonneg _)

/-- Multiplying both sides by a real power preserves an epsilon-power bound. -/
theorem EpsilonPowerBound.mul_left_rpow {f g : ℝ → ℝ}
    (h : EpsilonPowerBound f g) (a : ℝ) :
    EpsilonPowerBound (fun T => T ^ a * f T) (fun T => T ^ a * g T) := by
  intro ε hε
  have H := IsBigO.mul (isBigO_refl (fun T : ℝ => |T ^ a|) atTop) (h ε hε)
  convert H using 1
  · ext T
    rw [abs_mul]
  · ext T
    rw [abs_mul]
    ring

/-- The twisted fourth moment gives the correctly scaled `T^(2-2σ)` bound. -/
theorem scaled_twistedZetaFourthMoment_bound
    (hMoment : TwistedZetaFourthMomentProp) (σ : ℝ) :
    EpsilonPowerBound
      (fun T => T ^ (1 - 2 * σ) * twistedZetaFourthMoment T)
      (fun T => T ^ (2 - 2 * σ)) := by
  have hScaled := hMoment.mul_left_rpow (1 - 2 * σ)
  intro ε hε
  have H := hScaled ε hε
  apply H.congr'
  · exact Filter.Eventually.of_forall fun _ => rfl
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hpow : T ^ (1 - 2 * σ) * T = T ^ (2 - 2 * σ) := by
      calc
        T ^ (1 - 2 * σ) * T = T ^ (1 - 2 * σ) * T ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = T ^ ((1 - 2 * σ) + 1) := (Real.rpow_add hT _ _).symm
        _ = T ^ (2 - 2 * σ) := by ring_nf
    rw [hpow]

/--
The residual bound follows from finite coverage, the Appendix C reduction, and
the twisted fourth moment. None of the three inputs is equivalent to the result.
-/
theorem residual_zero_bound_of_cover_reduction_and_fourth_moment {α : Type*}
    (Z : ℝ → ℝ → Finset α) (multiplicity : α → ℕ)
    (isTypeI isTypeII : ℝ → α → Prop)
    (hCover : FiniteTypeICoverProp Z isTypeI isTypeII)
    (hReduction : TypeIIFourthMomentReductionProp Z multiplicity isTypeII)
    (hMoment : TwistedZetaFourthMomentProp) :
    FiniteResidualZeroBoundProp Z multiplicity isTypeI := by
  intro σ hσLower hσUpper
  exact (residual_epsilonPowerBound_of_cover
    Z multiplicity isTypeI isTypeII hCover σ hσLower hσUpper).trans <|
      (hReduction σ hσLower hσUpper).trans <|
        scaled_twistedZetaFourthMoment_bound hMoment σ

/-- The concrete finite family of zeta zeros in the dyadic height rectangle. -/
noncomputable def dyadicZetaZeros (σ T : ℝ) : Finset ℂ :=
  zerosInRect σ 1 T (2 * T)

/-- The project Type-I predicate with the height argument first. -/
def zetaIsTypeI (T : ℝ) (ρ : ℂ) : Prop :=
  IsTypeIZero ρ T

/-- The source-facing contour-Type-II predicate with the height argument first. -/
def zetaIsContourTypeII (T : ℝ) (ρ : ℂ) : Prop :=
  IsContourTypeIIZero ρ T

/-- Source-level contour coverage supplies the eventual finite coverage needed
    for the concrete dyadic zeta-zero family. -/
theorem finiteTypeICover_of_typeIContourTypeII
    (hCover : TypeIContourTypeIICoverProp) :
    FiniteTypeICoverProp dyadicZetaZeros zetaIsTypeI zetaIsContourTypeII := by
  rcases hCover with ⟨T₀, _hT₀, hCover⟩
  intro σ hσLower _hσUpper
  filter_upwards [eventually_ge_atTop T₀] with T hT
  intro ρ hρ
  apply hCover T hT ρ
  · rw [dyadicZetaZeros, zerosInRect, Set.Finite.mem_toFinset,
      Set.mem_inter_iff] at hρ
    rw [mem_ZeroRectangle] at hρ ⊢
    rcases hρ with ⟨⟨hρLower, hρUpper, hρTLower, hρTUpper⟩, _hρZero⟩
    constructor
    · exact hσLower.trans hρLower
    · exact ⟨hρUpper, hρTLower, hρTUpper⟩
  · rw [dyadicZetaZeros, zerosInRect, Set.Finite.mem_toFinset,
      Set.mem_inter_iff] at hρ
    exact hρ.2

/-- The generic weighted residual count agrees exactly with the project's
    concrete analytic-multiplicity count. -/
lemma weightedResidualCount_dyadicZetaZeros_eq (σ T : ℝ) :
    weightedResidualCount dyadicZetaZeros
        (analyticVanishingOrder riemannZeta) zetaIsTypeI σ T =
      (residualZeroCount σ T (2 * T) T : ℝ) := by
  unfold weightedResidualCount weightedCount dyadicZetaZeros residualZeroCount
    IsResidualZero zetaIsTypeI
  rw [Nat.cast_sum]
  apply Finset.sum_congr
  · ext ρ
    simp only [Finset.mem_filter]
    tauto
  · intro ρ _hρ
    rfl

/--
Concrete conditional form of the Maynard--Pratt Type II deduction for the
project's finite zeta-zero family. The three hypotheses are the source coverage,
the Appendix C reduction, and the twisted fourth-moment estimate.
-/
theorem residualZeroBound_of_contourTypeII_reduction_and_fourthMoment
    (hCover : TypeIContourTypeIICoverProp)
    (hReduction : TypeIIFourthMomentReductionProp dyadicZetaZeros
      (analyticVanishingOrder riemannZeta) zetaIsContourTypeII)
    (hMoment : TwistedZetaFourthMomentProp) :
    ResidualZeroBoundProp := by
  have hGeneric := residual_zero_bound_of_cover_reduction_and_fourth_moment
    dyadicZetaZeros (analyticVanishingOrder riemannZeta)
      zetaIsTypeI zetaIsContourTypeII
      (finiteTypeICover_of_typeIContourTypeII hCover) hReduction hMoment
  intro σ hσLower hσUpper
  simpa only [weightedResidualCount_dyadicZetaZeros_eq] using
    hGeneric σ hσLower hσUpper

end RiemannZeta.GuthMaynard
