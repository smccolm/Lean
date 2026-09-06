import GafniTao.Pintz2023PowerMargins
import GafniTao.Pintz2023LocalGram

/-!
# Pintz (2023), equation (4.20): strict exponent arithmetic

The paper suppresses the small perturbation in the displayed exponent.
Here it is retained.  The lemma below gives a strict reserve large enough
both for that perturbation and for the final `T^(-epsilon/k)` loss.
-/

namespace GafniTao

noncomputable section

private theorem sqrt_six_mul_eta_lt_five_halves_div
    {eta : ℝ} {ell : ℕ}
    (heta : 0 < eta) (hell : 3 ≤ ell)
    (hcellUpper : 2 * eta * (ell : ℝ) * ((ell : ℝ) - 1) < 1) :
    Real.sqrt (6 * eta) < (5 / 2 : ℝ) / (ell : ℝ) := by
  have hellReal : (3 : ℝ) ≤ ell := by exact_mod_cast hell
  have hellPos : (0 : ℝ) < ell := by positivity
  have hetaEllSq : eta * (ell : ℝ) ^ 2 < 1 := by
    have hcompare : (ell : ℝ) ≤ 2 * ((ell : ℝ) - 1) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcompare
      (mul_nonneg heta.le (by positivity : (0 : ℝ) ≤ ell))
    nlinarith
  have hsqrtNonneg : 0 ≤ Real.sqrt (6 * eta) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (6 * eta)) ^ 2 = 6 * eta := by
    rw [Real.sq_sqrt]
    positivity
  have hrightPos : 0 < (5 / 2 : ℝ) / (ell : ℝ) := by positivity
  have hsquare :
      (Real.sqrt (6 * eta)) ^ 2 <
        ((5 / 2 : ℝ) / (ell : ℝ)) ^ 2 := by
    rw [hsqrtSq]
    rw [div_pow]
    apply (lt_div_iff₀ (sq_pos_of_pos hellPos)).2
    nlinarith
  nlinarith

/-- Strict numerical reserve behind Pintz (4.20).  The first term is the
Heath-Brown zeta exponent after converting the branch power
`1.9/ell = 19/(10 ell)`; the second term reserves the advertised
`T^(-epsilon/k)` saving. -/
theorem pintz2023_equation420_exponent_margin
    {eta epsilon : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (hepsilonSmall : epsilon ≤ eta / (100 * (ell : ℝ))) :
    (10 * (ell : ℝ) / 19) *
          ((1 / 2 : ℝ) * (6 * eta) ^ (3 / 2 : ℝ) + epsilon) +
        (ell : ℝ) * epsilon / (k : ℝ) < 4 * eta := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hk : 4 ≤ k := hcell.1
  have hell : 3 ≤ ell := hcell.2.1
  have hkReal : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hellReal : (3 : ℝ) ≤ ell := by exact_mod_cast hell
  have hkPos : (0 : ℝ) < k := by positivity
  have hellPos : (0 : ℝ) < ell := by positivity
  have hcellUpper :
      2 * eta * (ell : ℝ) * ((ell : ℝ) - 1) < 1 := by
    simpa using hcell.2.2.2.2.1
  have hsqrt := sqrt_six_mul_eta_lt_five_halves_div
    heta hell hcellUpper
  have hrpow :
      (6 * eta) ^ (3 / 2 : ℝ) =
        (6 * eta) * Real.sqrt (6 * eta) :=
    eta_three_halves_eq_eta_mul_sqrt (by positivity)
  have hrpowBound :
      (6 * eta) ^ (3 / 2 : ℝ) < 15 * eta / (ell : ℝ) := by
    rw [hrpow]
    have hmul := mul_lt_mul_of_pos_left hsqrt (by positivity : 0 < 6 * eta)
    calc
      (6 * eta) * Real.sqrt (6 * eta) <
          (6 * eta) * ((5 / 2 : ℝ) / (ell : ℝ)) := hmul
      _ = 15 * eta / (ell : ℝ) := by ring
  have hepsilonScaled :
      (10 * (ell : ℝ) / 19) * epsilon ≤ eta / 190 := by
    have hmul := mul_le_mul_of_nonneg_left hepsilonSmall
      (by positivity : 0 ≤ 10 * (ell : ℝ) / 19)
    calc
      (10 * (ell : ℝ) / 19) * epsilon ≤
          (10 * (ell : ℝ) / 19) *
            (eta / (100 * (ell : ℝ))) := hmul
      _ = eta / 190 := by field_simp; ring
  have hepsilonK :
      (ell : ℝ) * epsilon / (k : ℝ) ≤ eta / 400 := by
    have hEllEps : (ell : ℝ) * epsilon ≤ eta / 100 := by
      have hmul := mul_le_mul_of_nonneg_left hepsilonSmall
        (show (0 : ℝ) ≤ ell by positivity)
      calc
        (ell : ℝ) * epsilon ≤
            (ell : ℝ) * (eta / (100 * (ell : ℝ))) := hmul
        _ = eta / 100 := by field_simp
    rw [div_le_iff₀ hkPos]
    have hmul := mul_le_mul_of_nonneg_right hkReal
      (show 0 ≤ eta / 400 by positivity)
    nlinarith
  have hmain :
      (10 * (ell : ℝ) / 19) *
          ((1 / 2 : ℝ) * (6 * eta) ^ (3 / 2 : ℝ)) <
        75 * eta / 19 := by
    have hmul := mul_lt_mul_of_pos_left hrpowBound
      (show (0 : ℝ) < 5 * (ell : ℝ) / 19 by positivity)
    calc
      (10 * (ell : ℝ) / 19) *
          ((1 / 2 : ℝ) * (6 * eta) ^ (3 / 2 : ℝ)) =
        (5 * (ell : ℝ) / 19) *
          (6 * eta) ^ (3 / 2 : ℝ) := by ring
      _ < (5 * (ell : ℝ) / 19) *
          (15 * eta / (ell : ℝ)) := hmul
      _ = 75 * eta / 19 := by field_simp; ring
  nlinarith

#print axioms pintz2023_equation420_exponent_margin

end

end GafniTao
