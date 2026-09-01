import GafniTao.FordFiniteHolder

/-!
# Ford Lemma 5.1: the first Hölder step

The source polynomial sum `U` is defined using the literal `γ_j`
normalization.  The Taylor double sum from equation (5.2) is identified with
`U`, and the first line of (5.3) is proved with its exact `|B|^(r-1)` factor.
-/

open Finset

namespace GafniTao

noncomputable section

def fordLemma51InnerSum
    (k M₁ : ℕ) (t z : ℝ) (b : ℕ) : ℂ :=
  ∑ a ∈ Finset.Icc 1 M₁,
    fordAdditiveCharacter
      (fordTaylorPolynomialPhase k t z ((a * b : ℕ) : ℝ))

def fordLemma51U
    (k M₁ : ℕ) (B : Finset ℕ) (t z : ℝ) : ℂ :=
  ∑ b ∈ B, fordLemma51InnerSum k M₁ t z b

/-- The polynomial double sum in (5.2) is exactly Ford's `U`. -/
theorem fordTaylorDoubleSum_eq_fordLemma51U
    {k M₁ : ℕ} {B : Finset ℕ} {t z : ℝ} (hz : z ≠ 0) :
    (∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
      fordTaylorOscillation k t (((a * b : ℕ) : ℝ) / z)) =
        fordLemma51U k M₁ B t z := by
  unfold fordLemma51U fordLemma51InnerSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  exact fordTaylorOscillation_eq_additiveCharacter hz

/-- Ford's first Hölder inequality in (5.3). -/
theorem fordLemma51U_pow_le
    {k M₁ r : ℕ} {B : Finset ℕ} {t z : ℝ} (hr : 1 ≤ r) :
    ‖fordLemma51U k M₁ B t z‖ ^ r ≤
      (B.card : ℝ) ^ (r - 1) *
        ∑ b ∈ B, ‖fordLemma51InnerSum k M₁ t z b‖ ^ r := by
  unfold fordLemma51U
  exact ford_finite_holder_power B (fordLemma51InnerSum k M₁ t z) hr

/-- Ford's unit-modulus phase selecting the absolute value of a complex
power. -/
def fordUnitNormalizer (w : ℂ) : ℂ :=
  if w = 0 then 1 else star w / (‖w‖ : ℂ)

theorem norm_fordUnitNormalizer (w : ℂ) : ‖fordUnitNormalizer w‖ = 1 := by
  by_cases hw : w = 0
  · simp [fordUnitNormalizer, hw]
  · simp [fordUnitNormalizer, hw, norm_ne_zero_iff.mpr hw]

theorem fordUnitNormalizer_mul (w : ℂ) :
    fordUnitNormalizer w * w = (‖w‖ : ℂ) := by
  by_cases hw : w = 0
  · simp [fordUnitNormalizer, hw]
  · rw [fordUnitNormalizer, if_neg hw, div_mul_eq_mul_div]
    rw [Complex.star_def]
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    norm_cast
    field_simp [norm_ne_zero_iff.mpr hw]

theorem fordUnitNormalizer_mul_pow (w : ℂ) (r : ℕ) :
    fordUnitNormalizer (w ^ r) * w ^ r = (‖w‖ ^ r : ℝ) := by
  rw [fordUnitNormalizer_mul, norm_pow]

/-- The source coefficient `ε_b`, with `|ε_b|=1`. -/
def fordLemma51Epsilon
    (k M₁ r : ℕ) (t z : ℝ) (b : ℕ) : ℂ :=
  fordUnitNormalizer (fordLemma51InnerSum k M₁ t z b ^ r)

theorem norm_fordLemma51Epsilon
    (k M₁ r : ℕ) (t z : ℝ) (b : ℕ) :
    ‖fordLemma51Epsilon k M₁ r t z b‖ = 1 :=
  norm_fordUnitNormalizer _

theorem fordLemma51Epsilon_mul_pow
    (k M₁ r : ℕ) (t z : ℝ) (b : ℕ) :
    fordLemma51Epsilon k M₁ r t z b *
        fordLemma51InnerSum k M₁ t z b ^ r =
      (‖fordLemma51InnerSum k M₁ t z b‖ ^ r : ℝ) :=
  fordUnitNormalizer_mul_pow _ _

theorem fordLemma51_norm_power_sum_eq_epsilon_sum
    (k M₁ r : ℕ) (B : Finset ℕ) (t z : ℝ) :
    ((∑ b ∈ B, ‖fordLemma51InnerSum k M₁ t z b‖ ^ r : ℝ) : ℂ) =
      ∑ b ∈ B, fordLemma51Epsilon k M₁ r t z b *
        fordLemma51InnerSum k M₁ t z b ^ r := by
  push_cast
  apply Finset.sum_congr rfl
  intro b hb
  simpa using (fordLemma51Epsilon_mul_pow k M₁ r t z b).symm

#print axioms fordTaylorDoubleSum_eq_fordLemma51U
#print axioms fordLemma51U_pow_le
#print axioms fordUnitNormalizer_mul_pow
#print axioms fordLemma51_norm_power_sum_eq_epsilon_sum

end

end GafniTao
