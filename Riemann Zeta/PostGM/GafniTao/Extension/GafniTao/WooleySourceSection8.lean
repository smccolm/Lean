import GafniTao.WooleySourceSections68

/-!
# Wooley Section 8 on source sequences

This module completes the unnormalised source-sequence form of Lemma 8.1.
The multiplier supplied by Lemma 7.1 is kept as an arbitrary nonnegative
quantity.  This is important later: constants and powers of `p` are then
normalised only once, in the exact equation-(3.24) quotient.
-/

namespace GafniTao

noncomputable section

/-- The source-sequence version of the endpoint estimate
`K^0_{a,b} \le U^{B,b}` used in (8.2). -/
theorem wooleySourcePolynomialMixedMean_zero_le_conditioned
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (hnua : nu ≤ a) (hnub : nu ≤ b)
    (gamma : WooleySourceSequence) :
    wooleySourcePolynomialMixedMean
        phi (wooleyTriangular k) 0 p B a b nu gamma ≤
      wooleySourcePolynomialConditionedMean
        (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma := by
  let phiBox := wooleyBoxedPolynomialSystem phi gamma
  let gammaBox := wooleySourceBoxCoefficients gamma
  have hfinite := wooleyPolynomialMixedGridMean_zero_le_conditioned
    (Q := wooleySourceBoxLength gamma) (p := p) (B := B) (k := k)
    (phi := phiBox) (gamma := gammaBox) (s := wooleyTriangular k)
    (a := a) (b := b) (nu := nu)
  simpa only [phiBox, gammaBox,
    wooleySourcePolynomialMixedMean_eq_boxed
      phi (wooleyTriangular k) 0 p B a b nu hnua hnub gamma,
    wooleySourcePolynomialConditionedMean_eq_boxed] using hfinite

/-- Equation (8.1) with the exact multiplier delivered by Lemma 7.1.
No implicit Vinogradov constant is introduced. -/
theorem wooleySourcePolynomial_equation_8_1_of_section7_mul
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B r a b bPrime nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (hr : 2 ≤ r) (hrk : r < k)
    (hnub : nu ≤ b) (hnuPrime : nu ≤ bPrime)
    (gamma : WooleySourceSequence) (D : ℝ) (hD : 0 ≤ D)
    (hsection7 :
      wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) r p B a b nu gamma ≤
        D * wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) r p B bPrime b nu gamma) :
    wooleySourcePolynomialMixedMean
        phi (wooleyTriangular k) r p B a b nu gamma ≤
      D *
        ((wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) (k - r) p B b bPrime nu gamma) ^
          (1 / ((k - r + 1 : ℕ) : ℝ)) *
        (wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) (r - 1) p B bPrime b nu gamma) ^
          (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ))) := by
  exact hsection7.trans (mul_le_mul_of_nonneg_left
    (wooleySourcePolynomial_equation_8_3
      phi p B r bPrime b nu (by omega) hrk hnuPrime hnub gamma) hD)

/-- Equation (8.2) with the exact multiplier delivered by Lemma 7.1.
The separated `K^0` term is bounded by the literal conditioned mean rather
than silently identified with it. -/
theorem wooleySourcePolynomial_equation_8_2_of_section7_mul
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (hk : 2 ≤ k) (hnub : nu ≤ b) (hnukb : nu ≤ k * b)
    (gamma : WooleySourceSequence) (D : ℝ) (hD : 0 ≤ D)
    (hsection7 :
      wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) 1 p B a b nu gamma ≤
        D * wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) 1 p B (k * b) b nu gamma) :
    wooleySourcePolynomialMixedMean
        phi (wooleyTriangular k) 1 p B a b nu gamma ≤
      D *
        ((wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) (k - 1) p B b (k * b) nu gamma) ^
          (1 / (k : ℝ)) *
        (wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma) ^
          (1 - 1 / (k : ℝ))) := by
  have hk1 : 1 < k := by omega
  have h83 := wooleySourcePolynomial_equation_8_3
    phi p B 1 (k * b) b nu (by omega) hk1 hnukb hnub gamma
  have hdenNat : k - 1 + 1 = k := by omega
  have hkRealNe : (k : ℝ) ≠ 0 := by positivity
  have hfrac :
      ((k - 1 : ℕ) : ℝ) / ((k - 1 + 1 : ℕ) : ℝ) =
        1 - 1 / (k : ℝ) := by
    rw [hdenNat, Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
    field_simp [hkRealNe]
  have hfrac' :
      ((k - 1 : ℕ) : ℝ) / (k : ℝ) = 1 - 1 / (k : ℝ) := by
    simpa only [hdenNat] using hfrac
  have h83' :
      wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) 1 p B (k * b) b nu gamma ≤
        (wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) (k - 1) p B b (k * b) nu gamma) ^
          (1 / (k : ℝ)) *
        (wooleySourcePolynomialMixedMean
            phi (wooleyTriangular k) 0 p B (k * b) b nu gamma) ^
          (1 - 1 / (k : ℝ)) := by
    simpa only [Nat.sub_self, hdenNat, hfrac'] using h83
  have hzero := wooleySourcePolynomialMixedMean_zero_le_conditioned
    phi p B (k * b) b nu hnukb hnub gamma
  have hv0 : (0 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
    have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hkPos : (0 : ℝ) < k := by positivity
    rw [sub_nonneg, div_le_iff₀ hkPos]
    simpa only [one_mul] using hkReal.trans' (by norm_num)
  have hzeroPow := Real.rpow_le_rpow
    (wooleySourcePolynomialMixedMean_nonneg
      phi (wooleyTriangular k) 0 p B (k * b) b nu gamma) hzero hv0
  have hfirstNonneg :
      0 ≤ (wooleySourcePolynomialMixedMean
        phi (wooleyTriangular k) (k - 1) p B b (k * b) nu gamma) ^
          (1 / (k : ℝ)) := Real.rpow_nonneg
            (wooleySourcePolynomialMixedMean_nonneg
              phi (wooleyTriangular k) (k - 1) p B b (k * b) nu gamma) _
  have hinside := h83'.trans
    (mul_le_mul_of_nonneg_left hzeroPow hfirstNonneg)
  exact hsection7.trans (mul_le_mul_of_nonneg_left hinside hD)

#print axioms wooleySourcePolynomialMixedMean_zero_le_conditioned
#print axioms wooleySourcePolynomial_equation_8_1_of_section7_mul
#print axioms wooleySourcePolynomial_equation_8_2_of_section7_mul

end

end GafniTao
