import GafniTao.WooleySection8Normalized

/-!
# Wooley equation (8.5): the conditioned-mean ratio

This file carries out the cancellation in the last paragraph of the proof of
Lemma 8.2.  In particular, the factor `U^{B,H}` is not cancelled unless the
literal normalization scale is positive, and the loss
`epsilon * (H - b)` is compared explicitly with `s * nu`.
-/

namespace GafniTao

noncomputable section

/-- The exact ratio estimate used between Wooley (8.7) and (8.5). -/
theorem wooleySourcePolynomial_equation_8_7_ratio
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B H b s nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (Lambda epsilon : ℝ) (gamma : WooleySourceSequence)
    (hp : 2 ≤ p) (hbH : b ≤ H)
    (hscale : 0 < wooleySourceNormalizationScale
      phi p B H s Lambda gamma)
    (hupper :
      wooleySourcePolynomialConditionedMean
          s (p ^ B) (p ^ b) phi gamma ≤
        (p : ℝ) ^ (((H - b : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            s (p ^ B) (p ^ H) phi gamma)
    (hloss : epsilon * ((H - b : ℕ) : ℝ) ≤ (s : ℝ) * (nu : ℝ)) :
    wooleySourcePolynomialConditionedMean
          s (p ^ B) (p ^ b) phi gamma /
        wooleySourceNormalizationScale phi p B H s Lambda gamma ≤
      (p : ℝ) ^ ((s : ℝ) * (nu : ℝ) - Lambda * (b : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hUH : 0 ≤ wooleySourcePolynomialConditionedMean
      s (p ^ B) (p ^ H) phi gamma :=
    wooleySourcePolynomialConditionedMean_nonneg phi s (p ^ B) (p ^ H) gamma
  have hexp :
      ((H - b : ℕ) : ℝ) * (Lambda + epsilon) ≤
        ((s : ℝ) * (nu : ℝ) - Lambda * (b : ℝ)) +
          Lambda * (H : ℝ) := by
    rw [Nat.cast_sub hbH] at hloss ⊢
    nlinarith
  have hpow :
      (p : ℝ) ^ (((H - b : ℕ) : ℝ) * (Lambda + epsilon)) ≤
        (p : ℝ) ^
          (((s : ℝ) * (nu : ℝ) - Lambda * (b : ℝ)) +
            Lambda * (H : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ p by omega)) hexp
  rw [div_le_iff₀ hscale]
  unfold wooleySourceNormalizationScale
  calc
    wooleySourcePolynomialConditionedMean
        s (p ^ B) (p ^ b) phi gamma ≤
      (p : ℝ) ^ (((H - b : ℕ) : ℝ) * (Lambda + epsilon)) *
        wooleySourcePolynomialConditionedMean
          s (p ^ B) (p ^ H) phi gamma := hupper
    _ ≤ (p : ℝ) ^
          (((s : ℝ) * (nu : ℝ) - Lambda * (b : ℝ)) +
            Lambda * (H : ℝ)) *
        wooleySourcePolynomialConditionedMean
          s (p ^ B) (p ^ H) phi gamma :=
      mul_le_mul_of_nonneg_right hpow hUH
    _ = (p : ℝ) ^ ((s : ℝ) * (nu : ℝ) - Lambda * (b : ℝ)) *
        ((p : ℝ) ^ (Lambda * (H : ℝ)) *
          wooleySourcePolynomialConditionedMean
            s (p ^ B) (p ^ H) phi gamma) := by
      rw [Real.rpow_add hpR]
      ring

/-- Wooley equation (8.5), with the source-(6.4) estimate and its complete
epsilon-loss comparison consumed in the same theorem.  The exact multiplier
`D` from Lemma 7.1 remains visible for the later uniform-constant ledger. -/
theorem wooleySourcePolynomial_equation_8_5
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B H a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (Lambda epsilon D : ℝ) (hk : 2 ≤ k) (hp : 2 ≤ p)
    (hbH : b ≤ H) (hnub : nu ≤ b) (hnukb : nu ≤ k * b)
    (gamma : WooleySourceSequence)
    (hscale : 0 < wooleySourceNormalizationScale
      phi p B H (wooleyTriangular k) Lambda gamma)
    (hD : 0 ≤ D)
    (hsection7 :
      wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) 1 p B a b nu gamma ≤
        D * wooleySourcePolynomialMixedMean
          phi (wooleyTriangular k) 1 p B (k * b) b nu gamma)
    (hupper :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma ≤
        (p : ℝ) ^ (((H - b : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma)
    (hloss : epsilon * ((H - b : ℕ) : ℝ) ≤
      (wooleyTriangular k : ℝ) * (nu : ℝ)) :
    wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) 1 a b nu Lambda gamma ≤
      D *
        (wooleySourceNormalizedMixedMean
          phi p B H (wooleyTriangular k) (k - 1) b (k * b) nu Lambda gamma) ^
            (1 / (k : ℝ)) *
        ((p : ℝ) ^
          ((wooleyTriangular k : ℝ) * (nu : ℝ) -
            Lambda * (b : ℝ))) ^ (1 - 1 / (k : ℝ)) := by
  apply wooleySourcePolynomial_equation_8_5_of_ratio
    (E := (p : ℝ) ^
      ((wooleyTriangular k : ℝ) * (nu : ℝ) -
        Lambda * (b : ℝ)))
    phi p B H a b nu Lambda D hk hnub hnukb gamma hscale hD hsection7
  exact wooleySourcePolynomial_equation_8_7_ratio
    phi p B H b (wooleyTriangular k) nu Lambda epsilon gamma
      hp hbH hscale hupper hloss

#print axioms wooleySourcePolynomial_equation_8_7_ratio
#print axioms wooleySourcePolynomial_equation_8_5

end

end GafniTao
