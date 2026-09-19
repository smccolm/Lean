import TaoTrudgianYang2025.RationalCertificates

/-!
# Exact piecewise-envelope certificates

The results here reduce interval coverage, affine comparisons, rational
comparisons, crossovers, and two-branch maxima/minima to kernel-checked real
arithmetic. Later paper-specific tables instantiate this layer with rational
data.
-/

namespace TaoTrudgianYang2025

/-- A closed interval with exact rational endpoints. -/
structure RationalClosedInterval where
  lower : ℚ
  upper : ℚ
  ordered : lower ≤ upper

namespace RationalClosedInterval

/-- Real membership in an exact rational closed interval. -/
def Contains (interval : RationalClosedInterval) (x : ℝ) : Prop :=
  (interval.lower : ℝ) ≤ x ∧ x ≤ (interval.upper : ℝ)

end RationalClosedInterval

/-- An affine function with exact rational coefficients. -/
structure RationalAffine where
  slope : ℚ
  constant : ℚ
deriving DecidableEq

namespace RationalAffine

/-- Evaluate a rational affine function over the reals. -/
def eval (f : RationalAffine) (x : ℝ) : ℝ :=
  (f.slope : ℝ) * x + f.constant

/-- An affine comparison on a closed interval is certified by its two
endpoints. -/
theorem eval_le_eval_of_endpoints
    (f g : RationalAffine) {lower upper x : ℝ}
    (_hLowerUpper : lower ≤ upper)
    (hxLower : lower ≤ x) (hxUpper : x ≤ upper)
    (hLower : f.eval lower ≤ g.eval lower)
    (hUpper : f.eval upper ≤ g.eval upper) :
    f.eval x ≤ g.eval x := by
  by_cases hSlope : (f.slope : ℝ) ≤ g.slope
  · have hProduct :
        0 ≤ ((g.slope : ℝ) - f.slope) * (x - lower) :=
      mul_nonneg (sub_nonneg.mpr hSlope) (sub_nonneg.mpr hxLower)
    dsimp [eval] at hLower ⊢
    nlinarith
  · have hSlope' : (g.slope : ℝ) ≤ f.slope := le_of_not_ge hSlope
    have hProduct :
        0 ≤ ((f.slope : ℝ) - g.slope) * (upper - x) :=
      mul_nonneg (sub_nonneg.mpr hSlope') (sub_nonneg.mpr hxUpper)
    dsimp [eval] at hUpper ⊢
    nlinarith

/-- A supplied exact crossover equation certifies equality of two affine
functions at that point. -/
theorem eval_eq_eval_of_crossover
    (f g : RationalAffine) {x : ℝ}
    (hCross : ((f.slope : ℝ) - g.slope) * x =
      (g.constant : ℝ) - f.constant) :
    f.eval x = g.eval x := by
  dsimp [eval]
  linarith

end RationalAffine

/-- Splitting an interval at an interior point covers the original interval
without duplicating its left endpoint. -/
theorem Ioc_union_Ioc {lower middle upper : ℝ}
    (hLowerMiddle : lower ≤ middle) (hMiddleUpper : middle ≤ upper) :
    Set.Ioc lower middle ∪ Set.Ioc middle upper = Set.Ioc lower upper := by
  ext x
  simp only [Set.mem_union, Set.mem_Ioc]
  constructor
  · rintro (hx | hx) <;> constructor <;> linarith
  · intro hx
    by_cases hxm : x ≤ middle
    · exact Or.inl ⟨hx.1, hxm⟩
    · exact Or.inr ⟨lt_of_not_ge hxm, hx.2⟩

/-- Positive denominators turn a cross-multiplied certificate into the
corresponding rational-function comparison. -/
theorem div_le_div_of_crossMultiply
    {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hCross : a * d ≤ c * b) :
    a / b ≤ c / d := by
  rw [div_le_div_iff₀ hb hd]
  exact hCross

/-- Specification that a function is the upper envelope of finitely many
exact affine functions on a domain. -/
def IsUpperEnvelope (pieces : Finset RationalAffine)
    (envelope : ℝ → ℝ) (domain : Set ℝ) : Prop :=
  ∀ x ∈ domain,
    (∀ f ∈ pieces, f.eval x ≤ envelope x) ∧
      ∃ f ∈ pieces, envelope x = f.eval x

/-- The pointwise maximum of two affine functions is their certified upper
envelope. -/
theorem max_two_isUpperEnvelope (f g : RationalAffine) (domain : Set ℝ) :
    IsUpperEnvelope {f, g} (fun x ↦ max (f.eval x) (g.eval x)) domain := by
  intro x hx
  constructor
  · intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  · by_cases hfg : f.eval x ≤ g.eval x
    · refine ⟨g, by simp, max_eq_right hfg⟩
    · have hgf : g.eval x ≤ f.eval x := le_of_not_ge hfg
      refine ⟨f, by simp, max_eq_left hgf⟩

/-- Specification that a function is the lower envelope of finitely many
exact affine functions on a domain. -/
def IsLowerEnvelope (pieces : Finset RationalAffine)
    (envelope : ℝ → ℝ) (domain : Set ℝ) : Prop :=
  ∀ x ∈ domain,
    (∀ f ∈ pieces, envelope x ≤ f.eval x) ∧
      ∃ f ∈ pieces, envelope x = f.eval x

/-- The pointwise minimum of two affine functions is their certified lower
envelope. -/
theorem min_two_isLowerEnvelope (f g : RationalAffine) (domain : Set ℝ) :
    IsLowerEnvelope {f, g} (fun x ↦ min (f.eval x) (g.eval x)) domain := by
  intro x hx
  constructor
  · intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _
  · by_cases hfg : f.eval x ≤ g.eval x
    · refine ⟨f, by simp, min_eq_left hfg⟩
    · have hgf : g.eval x ≤ f.eval x := le_of_not_ge hfg
      refine ⟨g, by simp, min_eq_right hgf⟩

end TaoTrudgianYang2025
