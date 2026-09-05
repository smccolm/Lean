import GafniTao.WooleyExponent
import GafniTao.WooleySourceSections68

/-!
# The initial normalized lower bound in Wooley Section 10

This file converts an actual counterexample below the critical exponent into
the lower bound for the first normalized mixed mean.  The positivity of the
normalizing conditioned mean is derived from source equation (3.10); it is
not imposed as an extra hypothesis.
-/

namespace GafniTao

noncomputable section

/-- The exact real-power rearrangement used between (6.3), Lemma 6.3, and
the initial inequality in (10.6). -/
theorem wooley_initial_normalization_algebra
    {p H theta s : ℕ} {Lambda epsilon C U K Z : ℝ}
    (hp : 1 ≤ p) (hC : 0 < C) (hZ : 0 < Z)
    (hlower :
      (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) * Z ≤ U)
    (hupper : U ≤ C * (p ^ theta : ℝ) ^ s * K) :
    C⁻¹ * (p : ℝ) ^ (-((H : ℝ) * epsilon) - (s : ℝ) * theta) ≤
      K / ((p : ℝ) ^ (Lambda * (H : ℝ)) * Z) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hden : 0 < (p : ℝ) ^ (Lambda * (H : ℝ)) * Z :=
    mul_pos (Real.rpow_pos_of_pos hpR _) hZ
  rw [le_div_iff₀ hden]
  have hscale : 0 < C * (p ^ theta : ℝ) ^ s := by positivity
  have hpowTheta : (p ^ theta : ℝ) ^ s =
      (p : ℝ) ^ ((s : ℝ) * theta) := by
    calc
      (p ^ theta : ℝ) ^ s = ((p : ℝ) ^ theta) ^ s := by norm_num
      _ = (p : ℝ) ^ (theta * s) := by rw [pow_mul]
      _ = (p : ℝ) ^ (((theta * s : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
      _ = (p : ℝ) ^ ((s : ℝ) * theta) := by
        congr 1
        push_cast
        ring
  have hrearrange :
      C⁻¹ * (p : ℝ) ^
          (-((H : ℝ) * epsilon) - (s : ℝ) * theta) *
          ((p : ℝ) ^ (Lambda * (H : ℝ)) * Z) =
        (C * (p ^ theta : ℝ) ^ s)⁻¹ *
          ((p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) * Z) := by
    rw [hpowTheta, mul_inv, ← Real.rpow_neg hpR.le]
    have hpowers :
        (p : ℝ) ^ (-((H : ℝ) * epsilon) - (s : ℝ) * theta) *
            (p : ℝ) ^ (Lambda * (H : ℝ)) =
          (p : ℝ) ^ (-((s : ℝ) * theta)) *
            (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) := by
      rw [← Real.rpow_add hpR, ← Real.rpow_add hpR]
      congr 1
      ring
    calc
      C⁻¹ * (p : ℝ) ^
            (-((H : ℝ) * epsilon) - (s : ℝ) * theta) *
            ((p : ℝ) ^ (Lambda * (H : ℝ)) * Z) =
          C⁻¹ *
            ((p : ℝ) ^
              (-((H : ℝ) * epsilon) - (s : ℝ) * theta) *
             (p : ℝ) ^ (Lambda * (H : ℝ))) * Z := by ring
      _ = C⁻¹ *
            ((p : ℝ) ^ (-((s : ℝ) * theta)) *
             (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon))) * Z := by
          rw [hpowers]
      _ = C⁻¹ * (p : ℝ) ^ (-((s : ℝ) * theta)) *
            ((p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) * Z) := by
          ring
  rw [hrearrange]
  calc
    (C * (p ^ theta : ℝ) ^ s)⁻¹ *
        ((p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) * Z) ≤
      (C * (p ^ theta : ℝ) ^ s)⁻¹ * U :=
        mul_le_mul_of_nonneg_left hlower (inv_nonneg.mpr hscale.le)
    _ ≤ (C * (p ^ theta : ℝ) ^ s)⁻¹ *
        (C * (p ^ theta : ℝ) ^ s * K) :=
          mul_le_mul_of_nonneg_left hupper (inv_nonneg.mpr hscale.le)
    _ = K := by field_simp

/-- An actual below-critical counterexample, combined with source Lemma 6.3,
gives the first normalized mixed-mean lower bound used in Section 10. -/
theorem wooleySourceNormalizedMixedMean_initial
    {k p B nu theta : ℕ} [NeZero p]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    {epsilon Lambda : ℝ}
    (hp : 2 ≤ p) (hk : 2 ≤ k)
    (hepsilon : 0 < epsilon) (hLambda : 0 < Lambda)
    (hnuH : nu ≤ B ⌈/⌉ k) (hnuTheta : nu ≤ theta)
    (hnu : 4 * epsilon * (B ⌈/⌉ k : ℕ) / Lambda ≤ (nu : ℝ))
    (hupper :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ nu) phi gamma ≤
        (p : ℝ) ^ ((((B ⌈/⌉ k) - nu : ℕ) : ℝ) *
            (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma)
    (hlarge : 2 * 2 ^ (wooleyTriangular k - 1) *
      (p : ℝ) ^ (-2 * epsilon * (B ⌈/⌉ k : ℕ)) ≤ 1)
    (hcounter :
      (p : ℝ) ^ (((B ⌈/⌉ k : ℕ) : ℝ) * (Lambda - epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma <
        wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B) phi gamma) :
    (2 * 2 ^ (wooleyTriangular k - 1) : ℝ)⁻¹ *
        (p : ℝ) ^
          (-(((B ⌈/⌉ k : ℕ) : ℝ) * epsilon) -
            (wooleyTriangular k : ℝ) * theta) ≤
      wooleySourceNormalizedMixedMean phi p B (B ⌈/⌉ k)
        (wooleyTriangular k) 1 theta theta nu Lambda gamma := by
  let H := B ⌈/⌉ k
  let s := wooleyTriangular k
  let U := wooleySourcePolynomialMean s (p ^ B) phi gamma
  let Z := wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ H) phi gamma
  let K := wooleySourcePolynomialMixedMean phi s 1 p B theta theta nu gamma
  let C : ℝ := 2 * 2 ^ (s - 1)
  have hs : 2 ≤ s := by
    exact (show 2 ≤ wooleyTriangular 2 by norm_num [wooleyTriangular]).trans
      (wooleyTriangular_mono hk)
  have hpPow : NeZero (p ^ B) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  have hpNu : NeZero (p ^ nu) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  have h310 := wooleySourcePolynomial_equation_3_10
    (k := k) (p := p) (B := B) phi gamma (by omega)
  have hleft0 : 0 ≤
      (p : ℝ) ^ ((H : ℝ) * (Lambda - epsilon)) * Z := by
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (wooleySourcePolynomialConditionedMean_nonneg phi s (p ^ B)
        (p ^ H) gamma)
  have hUpos : 0 < U := by
    exact lt_of_le_of_lt hleft0 (by simpa only [H, s, U, Z] using hcounter)
  have hZpos : 0 < Z := by
    have h310' : U ≤ ((p ^ H : ℕ) : ℝ) ^ s * Z := by
      simpa only [H, s, U, Z] using h310
    have hZ0 := wooleySourcePolynomialConditionedMean_nonneg
      phi s (p ^ B) (p ^ H) gamma
    exact lt_of_le_of_ne hZ0 (fun hz => by
      rw [← hz, mul_zero] at h310'
      linarith)
  have h63 := wooleySourcePolynomial_lemma_6_3
    phi p B nu theta H s gamma hp hs hepsilon hLambda
      (by simpa only [H] using hnuH) hnuTheta
      (by simpa only [H] using hnu)
      (by simpa only [H, s, U, Z] using hcounter.le)
      (by simpa only [H, s, Z] using hupper)
      (by simpa only [H, s] using hlarge)
  have halgebra := wooley_initial_normalization_algebra
    (p := p) (H := H) (theta := theta) (s := s)
    (Lambda := Lambda) (epsilon := epsilon) (C := C)
    (U := U) (K := K) (Z := Z) (by omega) (by dsimp [C]; positivity)
    hZpos (by simpa only [H, s, U, Z] using hcounter.le)
    (by simpa only [C, H, s, U, K] using h63)
  rw [wooleySourceNormalizedMixedMean, wooleyNormalizationExponent_one hk]
  simp only [Real.rpow_one]
  simpa only [C, H, s, K, Z, wooleySourceNormalizationScale,
    mul_comm (Lambda : ℝ) (H : ℝ)] using halgebra

#print axioms wooley_initial_normalization_algebra
#print axioms wooleySourceNormalizedMixedMean_initial

end

end GafniTao
