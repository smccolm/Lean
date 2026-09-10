import Tao2026.Vinogradov
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities

/-!
# Vinogradov polynomial moments

This module begins the polynomial mean-value argument after the coefficient
selection in `Tao2026.Vinogradov`. It formalizes the first Hölder step and the
finite power-sum representation functions used to define Vinogradov's mean
value count.
-/

namespace Tao2026

open scoped BigOperators NNReal

/-- Finite power-mean inequality in the exact form used for the first Hölder
step of Vinogradov's bilinear argument. -/
theorem norm_sum_pow_le_card_pow_mul_sum_norm_pow
    {ι : Type*} (s : Finset ι) (f : ι → ℂ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ‖∑ i ∈ s, f i‖ ^ ℓ ≤
      (s.card : ℝ) ^ (ℓ - 1) * ∑ i ∈ s, ‖f i‖ ^ ℓ := by
  have hnorm : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  calc
    ‖∑ i ∈ s, f i‖ ^ ℓ ≤ (∑ i ∈ s, ‖f i‖) ^ ℓ :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm ℓ
    _ ≤ (s.card : ℝ) ^ (ℓ - 1) * ∑ i ∈ s, ‖f i‖ ^ ℓ := by
      have h := pow_sum_le_card_mul_sum_pow
        (s := s) (f := fun i => ‖f i‖) (fun _ _ => norm_nonneg _) (ℓ - 1)
      simpa only [Nat.sub_add_cancel hℓ] using h

/-- The inner `y`-sum of the generic diagonal bilinear polynomial sum. -/
noncomputable def vinogradovBilinearPolynomialInnerSum
    (c : ℕ → ℝ) (R V x : ℕ) : ℂ :=
  ∑ y ∈ Finset.Icc 1 V, standardAdditiveCharacter
    (∑ r ∈ Finset.range R, c (r + 1) * x ^ (r + 1) * y ^ (r + 1))

/-- The generic bilinear sum is the outer sum of its polynomial inner sums. -/
theorem vinogradovBilinearPolynomialSum_eq_sum_inner
    (c : ℕ → ℝ) (R V : ℕ) :
    vinogradovBilinearPolynomialSum c R V =
      ∑ x ∈ Finset.Icc 1 V, vinogradovBilinearPolynomialInnerSum c R V x := by
  rfl

/-- First Hölder step for the unnormalized bilinear polynomial sum. -/
theorem norm_vinogradovBilinearPolynomialSum_pow_le_firstMoment
    (c : ℕ → ℝ) (R V ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ ℓ ≤
      (V : ℝ) ^ (ℓ - 1) *
        ∑ x ∈ Finset.Icc 1 V,
          ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ := by
  rw [vinogradovBilinearPolynomialSum_eq_sum_inner]
  have h := norm_sum_pow_le_card_pow_mul_sum_norm_pow
    (Finset.Icc 1 V) (vinogradovBilinearPolynomialInnerSum c R V) hℓ
  simpa using h

/-- The vector `(x,x²,…,xᴿ)` on the integer polynomial moment curve. -/
def vinogradovPolynomialCurve (R : ℕ) (x : ℕ) : Fin R → ℤ :=
  fun j => (x : ℤ) ^ (j.1 + 1)

/-- Sum of `ℓ` polynomial-curve vectors associated to an `ℓ`-tuple from
`{1,…,V}` (represented internally by `Fin V`). -/
def vinogradovTuplePowerSum {ℓ V : ℕ} (R : ℕ)
    (x : Fin ℓ → Fin V) : Fin R → ℤ :=
  fun j => ∑ i, (((x i).1 + 1 : ℕ) : ℤ) ^ (j.1 + 1)

/-- Finite set of power-sum vectors represented by `ℓ`-tuples. -/
def vinogradovPowerSumSupport (ℓ R V : ℕ) : Finset (Fin R → ℤ) :=
  Finset.univ.image (vinogradovTuplePowerSum (ℓ := ℓ) (V := V) R)

/-- Multiplicity of a power-sum vector among `ℓ`-tuples. -/
def vinogradovRepresentationCount (ℓ R V : ℕ) (u : Fin R → ℤ) : ℕ :=
  (Finset.univ.filter fun x : Fin ℓ → Fin V =>
    vinogradovTuplePowerSum R x = u).card

/-- Vinogradov's mean-value count, expressed directly as the number of pairs
of `ℓ`-tuples having the same first `R` power sums. -/
def vinogradovMeanValueCount (ℓ R V : ℕ) : ℕ :=
  ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
    (vinogradovRepresentationCount ℓ R V u) ^ 2

@[simp]
theorem mem_vinogradovPowerSumSupport {ℓ R V : ℕ} {u : Fin R → ℤ} :
    u ∈ vinogradovPowerSumSupport ℓ R V ↔
      ∃ x : Fin ℓ → Fin V, vinogradovTuplePowerSum R x = u := by
  classical
  simp [vinogradovPowerSumSupport]

/-- Summing all representation multiplicities recovers the number `V^ℓ` of
source tuples. This is equation (14) of the moment argument. -/
theorem sum_vinogradovRepresentationCount (ℓ R V : ℕ) :
    ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
      vinogradovRepresentationCount ℓ R V u = V ^ ℓ := by
  classical
  unfold vinogradovPowerSumSupport vinogradovRepresentationCount
  rw [← Finset.card_eq_sum_card_image]
  simp

/-- Equation (15): the second moment of the representation function is the
Vinogradov mean-value count. -/
theorem sum_sq_vinogradovRepresentationCount (ℓ R V : ℕ) :
    ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
      (vinogradovRepresentationCount ℓ R V u) ^ 2 =
        vinogradovMeanValueCount ℓ R V := by
  rfl

/-- Finite solution set for the Vinogradov system of equal power sums. -/
def vinogradovMeanValueSolutions (ℓ R V : ℕ) :
    Finset ((Fin ℓ → Fin V) × (Fin ℓ → Fin V)) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p =>
    vinogradovTuplePowerSum R p.1 = vinogradovTuplePowerSum R p.2

/-- The representation-function second moment equals the number of solutions
to the system of equal power sums. This is equation (17). -/
theorem card_vinogradovMeanValueSolutions_eq_meanValueCount (ℓ R V : ℕ) :
    (vinogradovMeanValueSolutions ℓ R V).card =
      vinogradovMeanValueCount ℓ R V := by
  classical
  unfold vinogradovMeanValueSolutions
  rw [Finset.card_filter, Finset.sum_product]
  have hinner : ∀ x : Fin ℓ → Fin V,
      (∑ y : Fin ℓ → Fin V,
        if vinogradovTuplePowerSum R x = vinogradovTuplePowerSum R y
        then 1 else 0) =
      vinogradovRepresentationCount ℓ R V (vinogradovTuplePowerSum R x) := by
    intro x
    unfold vinogradovRepresentationCount
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : vinogradovTuplePowerSum R y = vinogradovTuplePowerSum R x
    · rw [if_pos h.symm, if_pos h]
    · have h' : ¬vinogradovTuplePowerSum R x = vinogradovTuplePowerSum R y :=
        fun h' => h h'.symm
      rw [if_neg h', if_neg h]
  simp_rw [hinner]
  unfold vinogradovMeanValueCount vinogradovPowerSumSupport
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin ℓ → Fin V)))
    (t := Finset.univ.image (vinogradovTuplePowerSum R))
    (g := vinogradovTuplePowerSum R)
    (fun x hx => Finset.mem_image_of_mem _ hx)
    (fun x => vinogradovRepresentationCount ℓ R V
      (vinogradovTuplePowerSum R x))]
  apply Finset.sum_congr rfl
  intro u hu
  have hconst : ∀ x ∈ (Finset.univ.filter fun x : Fin ℓ → Fin V =>
      vinogradovTuplePowerSum R x = u),
      vinogradovRepresentationCount ℓ R V (vinogradovTuplePowerSum R x) =
        vinogradovRepresentationCount ℓ R V u := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [hx.2]
  rw [Finset.sum_const_nat hconst]
  change vinogradovRepresentationCount ℓ R V u *
      vinogradovRepresentationCount ℓ R V u =
    vinogradovRepresentationCount ℓ R V u ^ 2
  rw [pow_two]

/-- Difference of the power-sum vectors associated to two `ℓ`-tuples. -/
def vinogradovTuplePowerDifference {ℓ V : ℕ} (R : ℕ)
    (p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V)) : Fin R → ℤ :=
  fun j => vinogradovTuplePowerSum R p.1 j - vinogradovTuplePowerSum R p.2 j

/-- Finite support of the difference representation function appearing when
the linearized `2ℓ`-moment is expanded. -/
def vinogradovPowerDifferenceSupport (ℓ R V : ℕ) : Finset (Fin R → ℤ) :=
  ((Finset.univ : Finset (Fin ℓ → Fin V)) ×ˢ
    (Finset.univ : Finset (Fin ℓ → Fin V))).image
      (vinogradovTuplePowerDifference R)

/-- Number of pairs of `ℓ`-tuples representing a given power-sum
difference. -/
def vinogradovDifferenceRepresentationCount
    (ℓ R V : ℕ) (d : Fin R → ℤ) : ℕ :=
  (((Finset.univ : Finset (Fin ℓ → Fin V)) ×ˢ
      (Finset.univ : Finset (Fin ℓ → Fin V))).filter fun p :
      (Fin ℓ → Fin V) × (Fin ℓ → Fin V) =>
    vinogradovTuplePowerDifference R p = d).card

@[simp]
theorem mem_vinogradovPowerDifferenceSupport {ℓ R V : ℕ} {d : Fin R → ℤ} :
    d ∈ vinogradovPowerDifferenceSupport ℓ R V ↔
      ∃ p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V),
        vinogradovTuplePowerDifference R p = d := by
  classical
  simp [vinogradovPowerDifferenceSupport]

/-- The total multiplicity of all power-sum differences is the number of
ordered pairs of source tuples. -/
theorem sum_vinogradovDifferenceRepresentationCount (ℓ R V : ℕ) :
    ∑ d ∈ vinogradovPowerDifferenceSupport ℓ R V,
      vinogradovDifferenceRepresentationCount ℓ R V d = (V ^ ℓ) ^ 2 := by
  classical
  unfold vinogradovPowerDifferenceSupport vinogradovDifferenceRepresentationCount
  rw [← Finset.card_eq_sum_card_image]
  simp [pow_two]

theorem vinogradovTuplePowerSum_nonneg {ℓ R V : ℕ}
    (x : Fin ℓ → Fin V) (j : Fin R) :
    0 ≤ vinogradovTuplePowerSum R x j := by
  unfold vinogradovTuplePowerSum
  exact Finset.sum_nonneg fun _ _ => by positivity

/-- Each coordinate of an `ℓ`-fold curve sum lies below its natural box
side length. -/
theorem vinogradovTuplePowerSum_le {ℓ R V : ℕ}
    (x : Fin ℓ → Fin V) (j : Fin R) :
    vinogradovTuplePowerSum R x j ≤ (ℓ * V ^ (j.1 + 1) : ℕ) := by
  unfold vinogradovTuplePowerSum
  calc
    (∑ i, (((x i).1 + 1 : ℕ) : ℤ) ^ (j.1 + 1)) ≤
        ∑ _i : Fin ℓ, (V : ℤ) ^ (j.1 + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact_mod_cast Nat.pow_le_pow_left (show (x i).1 + 1 ≤ V by omega) _
    _ = (ℓ * V ^ (j.1 + 1) : ℕ) := by simp

/-- The difference support is contained in Tao's symmetric box
`|d_j| ≤ ℓ V^(j+1)`. -/
theorem abs_vinogradovTuplePowerDifference_le {ℓ R V : ℕ}
    (p : (Fin ℓ → Fin V) × (Fin ℓ → Fin V)) (j : Fin R) :
    |vinogradovTuplePowerDifference R p j| ≤
      (ℓ * V ^ (j.1 + 1) : ℕ) := by
  have h₁ := vinogradovTuplePowerSum_nonneg p.1 j
  have h₂ := vinogradovTuplePowerSum_nonneg p.2 j
  have h₁' := vinogradovTuplePowerSum_le p.1 j
  have h₂' := vinogradovTuplePowerSum_le p.2 j
  unfold vinogradovTuplePowerDifference
  rw [abs_le]
  constructor <;> omega

theorem abs_le_of_mem_vinogradovPowerDifferenceSupport {ℓ R V : ℕ}
    {d : Fin R → ℤ} (hd : d ∈ vinogradovPowerDifferenceSupport ℓ R V)
    (j : Fin R) :
    |d j| ≤ (ℓ * V ^ (j.1 + 1) : ℕ) := by
  rw [mem_vinogradovPowerDifferenceSupport] at hd
  obtain ⟨p, rfl⟩ := hd
  exact abs_vinogradovTuplePowerDifference_le p j

/-- Re-index a sum over `{1,…,V}` by the finite type `Fin V`. -/
theorem sum_Icc_one_eq_sum_fin {E : Type*} [AddCommMonoid E]
    (V : ℕ) (f : ℕ → E) :
    ∑ x ∈ Finset.Icc 1 V, f x = ∑ x : Fin V, f (x.1 + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun x => f (x + 1))]
  have hset : Finset.Icc 1 V =
      (Finset.range V).image (fun x => x + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx
      refine ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩
      omega
  rw [hset, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.add_right_cancel hxy

/-- Diagonal bilinear form associated to the coefficient vector `c`. -/
def vinogradovCoefficientBilinearForm
    (c : ℕ → ℝ) (R : ℕ) (u v : Fin R → ℤ) : ℝ :=
  ∑ j, c (j.1 + 1) * (u j : ℝ) * (v j : ℝ)

/-- The original polynomial phase is the coefficient bilinear form evaluated
on two points of the polynomial moment curve. -/
theorem vinogradovCoefficientBilinearForm_curve_curve
    (c : ℕ → ℝ) (R x y : ℕ) :
    vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R x) (vinogradovPolynomialCurve R y) =
      ∑ r ∈ Finset.range R,
        c (r + 1) * x ^ (r + 1) * y ^ (r + 1) := by
  unfold vinogradovCoefficientBilinearForm vinogradovPolynomialCurve
  rw [Fin.sum_univ_eq_sum_range (fun r =>
    c (r + 1) * (((x : ℤ) ^ (r + 1) : ℤ) : ℝ) *
      (((y : ℤ) ^ (r + 1) : ℤ) : ℝ))]
  apply Finset.sum_congr rfl
  intro r hr
  norm_num

/-- The inner polynomial sum, re-indexed by points of the finite moment
curve. -/
theorem vinogradovBilinearPolynomialInnerSum_eq_sum_curve
    (c : ℕ → ℝ) (R V x : ℕ) :
    vinogradovBilinearPolynomialInnerSum c R V x =
      ∑ y : Fin V, standardAdditiveCharacter
        (vinogradovCoefficientBilinearForm c R
          (vinogradovPolynomialCurve R x)
          (vinogradovPolynomialCurve R (y.1 + 1))) := by
  unfold vinogradovBilinearPolynomialInnerSum
  rw [sum_Icc_one_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro y hy
  rw [vinogradovCoefficientBilinearForm_curve_curve]

/-- Bilinearity in the tuple power-sum variable. -/
theorem vinogradovCoefficientBilinearForm_curve_tuplePowerSum
    (c : ℕ → ℝ) (R x : ℕ) {ℓ V : ℕ} (y : Fin ℓ → Fin V) :
    vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R x) (vinogradovTuplePowerSum R y) =
      ∑ i, vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R x)
        (vinogradovPolynomialCurve R ((y i).1 + 1)) := by
  unfold vinogradovCoefficientBilinearForm vinogradovPolynomialCurve
    vinogradovTuplePowerSum
  simp_rw [Int.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]

/-- An additive character maps a finite real sum to the corresponding complex
product. -/
theorem standardAdditiveCharacter_sum {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) :
    standardAdditiveCharacter (∑ i ∈ s, f i) =
      ∏ i ∈ s, standardAdditiveCharacter (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [standardAdditiveCharacter]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha,
        standardAdditiveCharacter_add, ih]

/-- Product of the phases associated with an `ℓ`-tuple depends only on its
power-sum vector. -/
theorem prod_standardAdditiveCharacter_bilinear_curve_eq_tuplePowerSum
    (c : ℕ → ℝ) (R x : ℕ) {ℓ V : ℕ} (y : Fin ℓ → Fin V) :
    (∏ i, standardAdditiveCharacter
      (vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R x)
        (vinogradovPolynomialCurve R ((y i).1 + 1)))) =
      standardAdditiveCharacter
        (vinogradovCoefficientBilinearForm c R
          (vinogradovPolynomialCurve R x)
          (vinogradovTuplePowerSum R y)) := by
  rw [vinogradovCoefficientBilinearForm_curve_tuplePowerSum]
  exact (standardAdditiveCharacter_sum Finset.univ _).symm

/-- Expanding the `ℓ`-th power of an inner polynomial sum produces one phase
for each tuple, indexed only by its power-sum vector. -/
theorem vinogradovBilinearPolynomialInnerSum_pow_eq_sum_tuplePowerSum
    (c : ℕ → ℝ) (R V x ℓ : ℕ) :
    (vinogradovBilinearPolynomialInnerSum c R V x) ^ ℓ =
      ∑ y : Fin ℓ → Fin V, standardAdditiveCharacter
        (vinogradovCoefficientBilinearForm c R
          (vinogradovPolynomialCurve R x)
          (vinogradovTuplePowerSum R y)) := by
  rw [vinogradovBilinearPolynomialInnerSum_eq_sum_curve, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro y hy
  exact prod_standardAdditiveCharacter_bilinear_curve_eq_tuplePowerSum c R x y

/-- Group the tuple expansion by power-sum vector, with the exact
representation multiplicity `ν`. -/
theorem vinogradovBilinearPolynomialInnerSum_pow_eq_sum_representationCount
    (c : ℕ → ℝ) (R V x ℓ : ℕ) :
    (vinogradovBilinearPolynomialInnerSum c R V x) ^ ℓ =
      ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u) •
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovPolynomialCurve R x) u) := by
  rw [vinogradovBilinearPolynomialInnerSum_pow_eq_sum_tuplePowerSum]
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin ℓ → Fin V)))
    (t := vinogradovPowerSumSupport ℓ R V)
    (g := vinogradovTuplePowerSum R)
    (fun y hy => by
      rw [mem_vinogradovPowerSumSupport]
      exact ⟨y, rfl⟩)
    (fun y => standardAdditiveCharacter
      (vinogradovCoefficientBilinearForm c R
        (vinogradovPolynomialCurve R x)
        (vinogradovTuplePowerSum R y)))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_eq_card_nsmul]
  · rfl
  · intro y hy
    rw [Finset.mem_filter] at hy
    rw [hy.2]

/-- Unit-norm multiplier rotating a complex number to its nonnegative real
norm. -/
noncomputable def complexNormPhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else (‖z‖ : ℂ) / z

theorem complexNormPhase_mul (z : ℂ) :
    complexNormPhase z * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [complexNormPhase, hz]
  · simp [complexNormPhase, hz]

@[simp]
theorem norm_complexNormPhase (z : ℂ) :
    ‖complexNormPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [complexNormPhase, hz]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    simp [complexNormPhase, hz, hn.ne']

/-- Raising the rotation identity to a natural power. -/
theorem complex_norm_pow_eq_phase_mul_pow (z : ℂ) (ℓ : ℕ) :
    ((‖z‖ ^ ℓ : ℝ) : ℂ) = (complexNormPhase z) ^ ℓ * z ^ ℓ := by
  rw [← mul_pow, complexNormPhase_mul]
  norm_num

/-- Unit coefficient used to remove the absolute value from the first Hölder
moment. -/
noncomputable def vinogradovOuterPhaseCoefficient
    (c : ℕ → ℝ) (R V ℓ x : ℕ) : ℂ :=
  (complexNormPhase (vinogradovBilinearPolynomialInnerSum c R V x)) ^ ℓ

@[simp]
theorem norm_vinogradovOuterPhaseCoefficient
    (c : ℕ → ℝ) (R V ℓ x : ℕ) :
    ‖vinogradovOuterPhaseCoefficient c R V ℓ x‖ = 1 := by
  simp [vinogradovOuterPhaseCoefficient, norm_pow]

/-- Pointwise removal of the absolute value followed by grouping the tuple
expansion according to its representation count. -/
theorem coe_norm_inner_pow_eq_phase_mul_representationCount
    (c : ℕ → ℝ) (R V x ℓ : ℕ) :
    ((‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) : ℂ) =
      vinogradovOuterPhaseCoefficient c R V ℓ x *
        ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
          (vinogradovRepresentationCount ℓ R V u) •
            standardAdditiveCharacter
              (vinogradovCoefficientBilinearForm c R
                (vinogradovPolynomialCurve R x) u) := by
  rw [complex_norm_pow_eq_phase_mul_pow]
  unfold vinogradovOuterPhaseCoefficient
  rw [vinogradovBilinearPolynomialInnerSum_pow_eq_sum_representationCount]

/-- Equation (13)--(14) after the first Hölder step: the sum of absolute
moments is an exact representation-weighted linearized bilinear sum. -/
theorem coe_sum_norm_inner_pow_eq_sum_representationCount_mul_linearized
    (c : ℕ → ℝ) (R V ℓ : ℕ) :
    (∑ x ∈ Finset.Icc 1 V,
        ((‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) : ℂ)) =
      ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u) •
          (∑ x ∈ Finset.Icc 1 V,
            vinogradovOuterPhaseCoefficient c R V ℓ x *
              standardAdditiveCharacter
                (vinogradovCoefficientBilinearForm c R
                  (vinogradovPolynomialCurve R x) u)) := by
  simp_rw [coe_norm_inner_pow_eq_phase_mul_representationCount]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [nsmul_eq_mul]
  ring

/-- The norm of a complex sum of nonnegative real numbers is the original
real sum. -/
theorem norm_sum_coe_eq_sum_of_nonneg {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ‖∑ i ∈ s, (f i : ℂ)‖ = ∑ i ∈ s, f i := by
  rw [← Complex.ofReal_sum, Complex.norm_real]
  exact Real.norm_of_nonneg (Finset.sum_nonneg hf)

/-- Triangle inequality after the exact representation-weighted
linearization of the first Hölder moment. -/
theorem sum_norm_inner_pow_le_representationCount_mul_norm_linearized
    (c : ℕ → ℝ) (R V ℓ : ℕ) :
    (∑ x ∈ Finset.Icc 1 V,
        ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) ≤
      ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ) *
          ‖∑ x ∈ Finset.Icc 1 V,
            vinogradovOuterPhaseCoefficient c R V ℓ x *
              standardAdditiveCharacter
                (vinogradovCoefficientBilinearForm c R
                  (vinogradovPolynomialCurve R x) u)‖ := by
  let lhs : ℝ := ∑ x ∈ Finset.Icc 1 V,
    ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ
  let rhs : ℂ := ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
    (vinogradovRepresentationCount ℓ R V u) •
      (∑ x ∈ Finset.Icc 1 V,
        vinogradovOuterPhaseCoefficient c R V ℓ x *
          standardAdditiveCharacter
            (vinogradovCoefficientBilinearForm c R
              (vinogradovPolynomialCurve R x) u))
  have heq : (∑ x ∈ Finset.Icc 1 V,
      ((‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) : ℂ)) = rhs :=
    coe_sum_norm_inner_pow_eq_sum_representationCount_mul_linearized c R V ℓ
  have hlhs : ‖∑ x ∈ Finset.Icc 1 V,
      ((‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) : ℂ)‖ = lhs := by
    apply norm_sum_coe_eq_sum_of_nonneg
    intro x hx
    positivity
  calc
    (∑ x ∈ Finset.Icc 1 V,
        ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) = lhs := rfl
    _ = ‖rhs‖ := by rw [← hlhs, heq]
    _ ≤ ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        ‖(vinogradovRepresentationCount ℓ R V u) •
          (∑ x ∈ Finset.Icc 1 V,
            vinogradovOuterPhaseCoefficient c R V ℓ x *
              standardAdditiveCharacter
                (vinogradovCoefficientBilinearForm c R
                  (vinogradovPolynomialCurve R x) u))‖ := norm_sum_le _ _
    _ = ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ) *
          ‖∑ x ∈ Finset.Icc 1 V,
            vinogradovOuterPhaseCoefficient c R V ℓ x *
              standardAdditiveCharacter
                (vinogradovCoefficientBilinearForm c R
                  (vinogradovPolynomialCurve R x) u)‖ := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [nsmul_eq_mul]

/-- The three-factor Hölder interpolation used in the second moment step.
The exponent `L` is kept real here so that the two nested Hölder inequalities
can use their natural conjugate exponents. -/
theorem nnreal_sum_mul_rpow_le_interpolation
    {ι : Type*} (s : Finset ι) (ν A : ι → ℝ≥0) (L : ℝ) (hL : 2 < L) :
    (∑ i ∈ s, ν i * A i) ^ L ≤
      (∑ i ∈ s, ν i) ^ (L - 2) *
        (∑ i ∈ s, ν i ^ (2 : ℝ)) *
          (∑ i ∈ s, A i ^ L) := by
  let p : ℝ := L / (L - 1)
  let q₁ : ℝ := (L - 1) / (L - 2)
  let q₂ : ℝ := L - 1
  have hpL : p.HolderConjugate L := by
    rw [Real.holderConjugate_iff]
    constructor
    · dsimp [p]
      rw [one_lt_div₀ (by linarith)]
      linarith
    · dsimp [p]
      field_simp [ne_of_gt (show 0 < L - 1 by linarith)]
      ring
  have hq : q₁.HolderConjugate q₂ := by
    rw [Real.holderConjugate_iff]
    constructor
    · dsimp [q₁]
      rw [one_lt_div₀ (by linarith)]
      linarith
    · dsimp [q₁, q₂]
      field_simp [ne_of_gt (show 0 < L - 2 by linarith),
        ne_of_gt (show 0 < L - 1 by linarith)]
      ring
  have houter := NNReal.inner_le_Lp_mul_Lq s ν A hpL
  have hinter := NNReal.inner_le_Lp_mul_Lq s
    (fun i => ν i ^ ((L - 2) / (L - 1)))
    (fun i => ν i ^ (2 / (L - 1))) hq
  dsimp [p] at houter
  dsimp [q₁, q₂] at hinter
  have hinter' :
      (∑ i ∈ s, ν i ^ (L / (L - 1))) ≤
        (∑ i ∈ s, ν i) ^ ((L - 2) / (L - 1)) *
          (∑ i ∈ s, ν i ^ (2 : ℝ)) ^ (1 / (L - 1)) := by
    convert hinter using 1
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hν : ν i = 0
      · have h₀ : 0 < L / (L - 1) := div_pos (by linarith) (by linarith)
        have h₁ : 0 < (L - 2) / (L - 1) := div_pos (by linarith) (by linarith)
        have h₂ : 0 < 2 / (L - 1) := div_pos (by norm_num) (by linarith)
        simp [hν, NNReal.zero_rpow, h₀.ne', h₁.ne', h₂.ne']
      · rw [← NNReal.rpow_add hν]
        congr 1
        field_simp [ne_of_gt (show 0 < L - 1 by linarith)]
        ring
    · congr 1
      · congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          rw [← NNReal.rpow_mul]
          field_simp [ne_of_gt (show 0 < L - 2 by linarith),
            ne_of_gt (show 0 < L - 1 by linarith)]
          simp
        · field_simp [ne_of_gt (show 0 < L - 2 by linarith),
            ne_of_gt (show 0 < L - 1 by linarith)]
      · congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [← NNReal.rpow_mul]
        congr 1
        field_simp [ne_of_gt (show 0 < L - 1 by linarith)]
  have hraw :
      (∑ i ∈ s, ν i * A i) ≤
        ((∑ i ∈ s, ν i) ^ ((L - 2) / (L - 1)) *
          (∑ i ∈ s, ν i ^ (2 : ℝ)) ^ (1 / (L - 1))) ^
            (1 / (L / (L - 1))) *
          (∑ i ∈ s, A i ^ L) ^ (1 / L) :=
    houter.trans (mul_le_mul_left
      (NNReal.rpow_le_rpow hinter'
        (show 0 ≤ 1 / (L / (L - 1)) by
          exact le_of_lt (one_div_pos.mpr (div_pos (by linarith) (by linarith))))) _)
  have hmain :
      (∑ i ∈ s, ν i * A i) ≤
        (∑ i ∈ s, ν i) ^ ((L - 2) / L) *
          (∑ i ∈ s, ν i ^ (2 : ℝ)) ^ (1 / L) *
            (∑ i ∈ s, A i ^ L) ^ (1 / L) := by
    convert hraw using 1
    rw [NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul]
    congr 2
    · field_simp [ne_of_gt (show 0 < L - 1 by linarith),
        ne_of_gt (show 0 < L by linarith)]
    · field_simp [ne_of_gt (show 0 < L - 1 by linarith),
        ne_of_gt (show 0 < L by linarith)]
  have hpow := NNReal.rpow_le_rpow hmain (show 0 ≤ L by linarith)
  convert hpow using 1
  rw [NNReal.mul_rpow, NNReal.mul_rpow, ← NNReal.rpow_mul,
    ← NNReal.rpow_mul, ← NNReal.rpow_mul]
  have hinv : 1 / L * L = 1 := by
    field_simp [ne_of_gt (show 0 < L by linarith)]
  rw [hinv]
  simp only [NNReal.rpow_one]
  congr 2
  field_simp [ne_of_gt (show 0 < L by linarith)]

/-- Integer-power form of the second Hölder interpolation. The endpoint
`ℓ = 1` is exactly Cauchy--Schwarz; larger exponents follow from the real
interpolation lemma. -/
theorem nnreal_sum_mul_pow_le_interpolation
    {ι : Type*} (s : Finset ι) (ν A : ι → ℝ≥0) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∑ i ∈ s, ν i * A i) ^ (2 * ℓ) ≤
      (∑ i ∈ s, ν i) ^ (2 * ℓ - 2) *
        (∑ i ∈ s, ν i ^ 2) *
          (∑ i ∈ s, A i ^ (2 * ℓ)) := by
  rcases hℓ.eq_or_lt with rfl | hℓ
  · simpa using Finset.sum_mul_sq_le_sq_mul_sq s ν A
  · have h := nnreal_sum_mul_rpow_le_interpolation s ν A (2 * ℓ : ℝ)
      (by exact_mod_cast (show 2 < 2 * ℓ by omega))
    have hmul : (2 : ℝ) * ℓ = ((2 * ℓ : ℕ) : ℝ) := by norm_num
    have hsub : ((2 * ℓ - 2 : ℕ) : ℝ) = ((2 * ℓ : ℕ) : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hmul, ← hsub] at h
    have htwo (x : ℝ≥0) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, NNReal.rpow_natCast]
    simp_rw [htwo] at h
    simpa only [NNReal.rpow_natCast] using h

/-- Real-valued nonnegative form of the second Hölder interpolation. -/
theorem sum_mul_pow_le_interpolation_of_nonneg
    {ι : Type*} (s : Finset ι) (ν A : ι → ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (hν : ∀ i, 0 ≤ ν i) (hA : ∀ i, 0 ≤ A i) :
    (∑ i ∈ s, ν i * A i) ^ (2 * ℓ) ≤
      (∑ i ∈ s, ν i) ^ (2 * ℓ - 2) *
        (∑ i ∈ s, ν i ^ 2) *
          (∑ i ∈ s, A i ^ (2 * ℓ)) := by
  lift ν to ι → ℝ≥0 using hν
  lift A to ι → ℝ≥0 using hA
  beta_reduce at *
  norm_cast at *
  exact nnreal_sum_mul_pow_le_interpolation s ν A ℓ hℓ

/-- Norm of the linearized outer sum attached to a power-sum vector. -/
noncomputable def vinogradovLinearizedSumNorm
    (c : ℕ → ℝ) (R V ℓ : ℕ) (u : Fin R → ℤ) : ℝ :=
  ‖∑ x ∈ Finset.Icc 1 V,
      vinogradovOuterPhaseCoefficient c R V ℓ x *
        standardAdditiveCharacter
          (vinogradovCoefficientBilinearForm c R
            (vinogradovPolynomialCurve R x) u)‖

theorem vinogradovLinearizedSumNorm_nonneg
    (c : ℕ → ℝ) (R V ℓ : ℕ) (u : Fin R → ℤ) :
    0 ≤ vinogradovLinearizedSumNorm c R V ℓ u := by
  exact norm_nonneg _

/-- The exact second Hölder estimate for the representation-weighted
linearized sum. This is the finite combinatorial inequality underlying
equation (16) in the Vinogradov argument. -/
theorem representationCount_linearized_pow_le_meanValue
    (c : ℕ → ℝ) (R V ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ) *
          vinogradovLinearizedSumNorm c R V ℓ u) ^ (2 * ℓ) ≤
      ((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
        (vinogradovMeanValueCount ℓ R V : ℝ) *
          ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) := by
  have h := sum_mul_pow_le_interpolation_of_nonneg
    (vinogradovPowerSumSupport ℓ R V)
    (fun u => (vinogradovRepresentationCount ℓ R V u : ℝ))
    (vinogradovLinearizedSumNorm c R V ℓ) ℓ hℓ
    (fun _ => Nat.cast_nonneg _) (vinogradovLinearizedSumNorm_nonneg c R V ℓ)
  have hsum :
      (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ)) =
          ((V ^ ℓ : ℕ) : ℝ) := by
    exact_mod_cast sum_vinogradovRepresentationCount ℓ R V
  have hsq :
      (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ) ^ 2) =
          (vinogradovMeanValueCount ℓ R V : ℝ) := by
    exact_mod_cast sum_sq_vinogradovRepresentationCount ℓ R V
  rw [hsum, hsq] at h
  exact h

/-- Equation (16) after both Hölder steps: the first inner-sum moment is
controlled by the representation count, its quadratic mean value, and the
`2ℓ`-moment of the linearized outer sums. -/
theorem sum_norm_inner_pow_pow_le_meanValue
    (c : ℕ → ℝ) (R V ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∑ x ∈ Finset.Icc 1 V,
        ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ) ^ (2 * ℓ) ≤
      ((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
        (vinogradovMeanValueCount ℓ R V : ℝ) *
          ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) := by
  have hfirst :=
    sum_norm_inner_pow_le_representationCount_mul_norm_linearized c R V ℓ
  have hfirst' :
      (∑ x ∈ Finset.Icc 1 V,
          ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ : ℝ) ≤
        ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
          (vinogradovRepresentationCount ℓ R V u : ℝ) *
            vinogradovLinearizedSumNorm c R V ℓ u := by
    simpa only [vinogradovLinearizedSumNorm] using hfirst
  calc
    (∑ x ∈ Finset.Icc 1 V,
        ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ) ^ (2 * ℓ) ≤
      (∑ u ∈ vinogradovPowerSumSupport ℓ R V,
        (vinogradovRepresentationCount ℓ R V u : ℝ) *
          vinogradovLinearizedSumNorm c R V ℓ u) ^ (2 * ℓ) :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hfirst' _
    _ ≤ ((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
        (vinogradovMeanValueCount ℓ R V : ℝ) *
          ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
            vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ) :=
      representationCount_linearized_pow_le_meanValue c R V ℓ hℓ

/-- Both Hölder steps combined with the original bilinear polynomial sum.
The remaining analytic input is now isolated in the mean-value count and the
linearized outer `2ℓ`-moment. -/
theorem norm_bilinearPolynomialSum_pow_le_meanValue
    (c : ℕ → ℝ) (R V ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ℓ * (2 * ℓ)) ≤
      (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
        (((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
          (vinogradovMeanValueCount ℓ R V : ℝ) *
            ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
              vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) := by
  have hfirst :=
    norm_vinogradovBilinearPolynomialSum_pow_le_firstMoment c R V ℓ hℓ
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤
      ‖vinogradovBilinearPolynomialSum c R V‖ ^ ℓ) hfirst (2 * ℓ)
  have hpow' :
      ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ℓ * (2 * ℓ)) ≤
        (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
          (∑ x ∈ Finset.Icc 1 V,
            ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ) ^
              (2 * ℓ) := by
    simpa only [pow_mul, mul_pow] using hpow
  calc
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ℓ * (2 * ℓ)) ≤
        (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
          (∑ x ∈ Finset.Icc 1 V,
            ‖vinogradovBilinearPolynomialInnerSum c R V x‖ ^ ℓ) ^
              (2 * ℓ) := hpow'
    _ ≤ (V : ℝ) ^ ((ℓ - 1) * (2 * ℓ)) *
        (((V ^ ℓ : ℕ) : ℝ) ^ (2 * ℓ - 2) *
          (vinogradovMeanValueCount ℓ R V : ℝ) *
            ∑ u ∈ vinogradovPowerSumSupport ℓ R V,
              vinogradovLinearizedSumNorm c R V ℓ u ^ (2 * ℓ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_norm_inner_pow_pow_le_meanValue c R V ℓ hℓ) (by positivity)

end Tao2026
