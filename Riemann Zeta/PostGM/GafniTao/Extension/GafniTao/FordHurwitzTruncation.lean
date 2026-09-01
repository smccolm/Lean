import GafniTao.FordFiniteZetaEndpoint
import Mathlib.NumberTheory.LSeries.HurwitzZeta

/-!
# Ford Lemma 7.2: exact source statement and finite-sum consumer

The proposition `FordHurwitzTruncationBound` is the literal missing analytic
claim of Ford's Lemma 7.2.  It is a named target, not an assumption exported
as a completed source theorem.  This file also proves the exact algebraic
consumer needed by Lemma 7.3, so that the remaining work is isolated to the
Euler--Maclaurin/Fourier remainder itself.
-/

open Complex HurwitzZeta

namespace GafniTao

noncomputable section

def fordComplexHeight (sigma t : ℝ) : ℂ :=
  (sigma : ℂ) + (t : ℂ) * I

def fordHurwitzHead (sigma u t : ℝ) : ℂ :=
  (u : ℂ) ^ (-fordComplexHeight sigma t)

def fordHurwitzFiniteApproximation (sigma u t : ℝ) : ℂ :=
  fordHurwitzHead sigma u t +
    fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) u t

def fordHurwitzRemainder (sigma u t : ℝ) : ℂ :=
  hurwitzZeta (u : UnitAddCircle) (fordComplexHeight sigma t) -
    fordHurwitzFiniteApproximation sigma u t

def fordTinyRemainder : ℝ := (10 : ℝ)⁻¹ ^ 80

/-- The exact statement of Ford's Lemma 7.2 in the Mathlib Hurwitz-zeta
normalization. -/
def FordHurwitzTruncationBound : Prop :=
  ∀ ⦃sigma u t : ℝ⦄,
    15 / 16 ≤ sigma → sigma ≤ 1 → (10 : ℝ) ^ 100 ≤ t →
    0 < u → u ≤ 1 →
    ‖fordHurwitzRemainder sigma u t‖ ≤ fordTinyRemainder

theorem fordHurwitz_sub_head_eq_finite_add_remainder
    (sigma u t : ℝ) :
    hurwitzZeta (u : UnitAddCircle) (fordComplexHeight sigma t) -
        fordHurwitzHead sigma u t =
      fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) u t +
        fordHurwitzRemainder sigma u t := by
  unfold fordHurwitzRemainder fordHurwitzFiniteApproximation
  ring

theorem norm_fordHurwitz_sub_head_le_expanded
    (hFord : FordTheorem2) (hTrunc : FordHurwitzTruncationBound)
    {sigma u t : ℝ}
    (hsigmaLower : 15 / 16 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : (10 : ℝ) ^ 100 ≤ t) (hu : 0 < u) (huOne : u ≤ 1) :
    ‖hurwitzZeta (u : UnitAddCircle) (fordComplexHeight sigma t) -
        fordHurwitzHead sigma u t‖ ≤
      (9.463 + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) +
        (1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) := by
  have htOne : 1 < t := by
    have hten : (1 : ℝ) < 10 := by norm_num
    have hpow : (1 : ℝ) < 10 ^ (100 : ℕ) := one_lt_pow₀ hten (by omega)
    exact hpow.trans_le ht
  have hsigmaNonneg : 0 ≤ sigma := by linarith
  have hfinite := norm_fordFiniteHurwitzSum_floor_le_source hFord
    hsigmaNonneg hsigmaUpper hu huOne htOne
  have hrem := hTrunc hsigmaLower hsigmaUpper ht hu huOne
  have hpeakNonneg :
      0 ≤ fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ) := by
    unfold fordSourceB
    positivity
  have hpower :
      1 ≤ t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.one_le_rpow htOne.le hpeakNonneg
  rw [fordHurwitz_sub_head_eq_finite_add_remainder]
  calc
    ‖fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) u t +
        fordHurwitzRemainder sigma u t‖ ≤
        ‖fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) u t‖ +
          ‖fordHurwitzRemainder sigma u t‖ := norm_add_le _ _
    _ ≤
        (1 + 9.463 *
          (t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            (1 + 1.569 * 133.66 ^ ((1 : ℝ) / 3) *
              Real.log t ^ ((2 : ℝ) / 3)))) + fordTinyRemainder :=
      add_le_add hfinite hrem
    _ ≤
      (9.463 + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) +
        (1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) := by
      have htiny : 0 ≤ fordTinyRemainder := by
        unfold fordTinyRemainder
        positivity
      nlinarith [mul_nonneg (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) htiny)
        (sub_nonneg.mpr hpower)]

/-- Ford Lemma 7.3 in its literal factored source layout, specialized to
the constants of Theorem 2. -/
theorem norm_fordHurwitz_sub_head_le_lemma73
    (hFord : FordTheorem2) (hTrunc : FordHurwitzTruncationBound)
    {sigma u t : ℝ}
    (hsigmaLower : 15 / 16 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : (10 : ℝ) ^ 100 ≤ t) (hu : 0 < u) (huOne : u ≤ 1) :
    ‖hurwitzZeta (u : UnitAddCircle) (fordComplexHeight sigma t) -
        fordHurwitzHead sigma u t‖ ≤
      ((9.463 + 1 + fordTinyRemainder) /
          Real.log t ^ ((2 : ℝ) / 3) +
        1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
        t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ ((2 : ℝ) / 3) := by
  have hraw := norm_fordHurwitz_sub_head_le_expanded hFord hTrunc
    hsigmaLower hsigmaUpper ht hu huOne
  have htOne : 1 < t := by
    have hten : (1 : ℝ) < 10 := by norm_num
    have hpow : (1 : ℝ) < 10 ^ (100 : ℕ) := one_lt_pow₀ hten (by omega)
    exact hpow.trans_le ht
  have hlog : 0 < Real.log t := Real.log_pos htOne
  have hlogPow : 0 < Real.log t ^ ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hlog _
  calc
    ‖hurwitzZeta (u : UnitAddCircle) (fordComplexHeight sigma t) -
        fordHurwitzHead sigma u t‖ ≤
      (9.463 + 1 + fordTinyRemainder) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) +
        (1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
          t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log t ^ ((2 : ℝ) / 3) := hraw
    _ = ((9.463 + 1 + fordTinyRemainder) /
          Real.log t ^ ((2 : ℝ) / 3) +
        1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3)) *
        t ^ (fordSourceB 133.66 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        Real.log t ^ ((2 : ℝ) / 3) := by
      field_simp [hlogPow.ne']

#print axioms fordHurwitz_sub_head_eq_finite_add_remainder
#print axioms norm_fordHurwitz_sub_head_le_expanded
#print axioms norm_fordHurwitz_sub_head_le_lemma73

end

end GafniTao
