import GafniTao.WooleySection4Holder
import GafniTao.WooleyNormalization

/-!
# Wooley Lemma 4.2

This file performs the complete normalization following equation (4.15).
The two restricted-mean estimates are kept as explicit inputs here; the
source Lemma 4.1 module supplies them from the defining exponent.  No
Vinogradov constant is discarded in this exact, eventual-bound form.
-/

namespace GafniTao

noncomputable section

/-- The source Lemma 4.2 calculation after the two instances of Lemma 4.1
have been supplied.  This is the precise terminal estimate used in Section
10, with normalization parameter `Delta = 0`. -/
theorem wooleySourcePolynomial_lemma_4_2_of_conditioned_bounds
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B H a b nu r : ℕ) [NeZero p] [NeZero (p ^ B)]
    (Lambda epsilon : ℝ) (gamma : WooleySourceSequence)
    (hp : 2 ≤ p) (hr : 1 ≤ r) (hrk : r < k)
    (haH : a ≤ H) (hbH : b ≤ H)
    (hLambdaEpsilon : 0 ≤ Lambda + epsilon)
    (hUH : 0 < wooleySourcePolynomialConditionedMean
      (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma)
    (hupperA :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ a) phi gamma ≤
        (p : ℝ) ^ (((H - a : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma)
    (hupperB :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma ≤
        (p : ℝ) ^ (((H - b : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma) :
    wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) r a b nu 0 gamma ≤
      (p : ℝ) ^ ((H : ℝ) * (Lambda + epsilon)) := by
  let s := wooleyTriangular k
  let R := wooleyTriangular r
  let u : ℝ := (R : ℝ) / (s : ℝ)
  let e := wooleyNormalizationExponent k r
  let K := wooleySourcePolynomialMixedMean phi s r p B a b nu gamma
  let X := wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ a) phi gamma
  let Y := wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ b) phi gamma
  let Z := wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ H) phi gamma
  have hk : 2 ≤ k := by omega
  have hs : 1 ≤ s := by
    dsimp [s]
    unfold wooleyTriangular
    have hkpos : 0 < k := by omega
    have htwo : 2 ≤ k * (k + 1) := by nlinarith
    omega
  have hRle : R ≤ s := by
    dsimp [R, s]
    exact wooleyTriangular_mono hrk.le
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by exact_mod_cast (show 0 < s by omega))]
    exact_mod_cast hRle
  have he0 : 0 ≤ e :=
    (wooleyNormalizationExponent_pos hr hrk).le
  have he1 : e ≤ 1 :=
    wooleyNormalizationExponent_le_one hr hrk
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact wooleySourcePolynomialMixedMean_nonneg
      phi s r p B a b nu gamma
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact wooleySourcePolynomialConditionedMean_nonneg
      phi s (p ^ B) (p ^ a) gamma
  have hY0 : 0 ≤ Y := by
    dsimp [Y]
    exact wooleySourcePolynomialConditionedMean_nonneg
      phi s (p ^ B) (p ^ b) gamma
  have hZ : 0 < Z := by simpa only [Z, s] using hUH
  have hKholder : K ≤ X ^ u * Y ^ (1 - u) := by
    simpa only [K, X, Y, u, R, s] using
      wooleySourcePolynomial_equation_4_15
        phi p B a b nu r (by omega) hrk.le gamma
  have hnormalized :
      (K / Z) ^ e ≤
        (X / Z) ^ (u * e) * (Y / Z) ^ ((1 - u) * e) := by
    have h := wooley_normalized_two_factor
      hK0 hX0 hY0 hZ (show 0 ≤ (1 : ℝ) by norm_num) he0
      (show u + (1 - u) = 1 by ring)
      (show K ≤ 1 * (X ^ u * Y ^ (1 - u)) by simpa using hKholder)
    simpa using h
  let A : ℝ := ((H - a : ℕ) : ℝ) * (Lambda + epsilon)
  let D : ℝ := ((H - b : ℕ) : ℝ) * (Lambda + epsilon)
  have hratioA : X / Z ≤ (p : ℝ) ^ A := by
    rw [div_le_iff₀ hZ]
    simpa only [X, Z, A, s] using hupperA
  have hratioB : Y / Z ≤ (p : ℝ) ^ D := by
    rw [div_le_iff₀ hZ]
    simpa only [Y, Z, D, s] using hupperB
  have hratioA0 : 0 ≤ X / Z := div_nonneg hX0 hZ.le
  have hratioB0 : 0 ≤ Y / Z := div_nonneg hY0 hZ.le
  have hue0 : 0 ≤ u * e := mul_nonneg hu0 he0
  have hve0 : 0 ≤ (1 - u) * e :=
    mul_nonneg (sub_nonneg.mpr hu1) he0
  have hpowA :
      (X / Z) ^ (u * e) ≤ ((p : ℝ) ^ A) ^ (u * e) :=
    Real.rpow_le_rpow hratioA0 hratioA hue0
  have hpowB :
      (Y / Z) ^ ((1 - u) * e) ≤
        ((p : ℝ) ^ D) ^ ((1 - u) * e) :=
    Real.rpow_le_rpow hratioB0 hratioB hve0
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hA0 : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) hLambdaEpsilon
  have hD0 : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hLambdaEpsilon
  have hweighted0 : 0 ≤ A * u + D * (1 - u) := by positivity
  have hAle : A ≤ (H : ℝ) * (Lambda + epsilon) := by
    dsimp [A]
    rw [Nat.cast_sub haH]
    nlinarith
  have hDle : D ≤ (H : ℝ) * (Lambda + epsilon) := by
    dsimp [D]
    rw [Nat.cast_sub hbH]
    nlinarith
  have hweighted :
      (A * u + D * (1 - u)) * e ≤
        (H : ℝ) * (Lambda + epsilon) := by
    have hblend :
        A * u + D * (1 - u) ≤ (H : ℝ) * (Lambda + epsilon) := by
      nlinarith
    have htarget0 : 0 ≤ (H : ℝ) * (Lambda + epsilon) :=
      mul_nonneg (Nat.cast_nonneg _) hLambdaEpsilon
    nlinarith
  have hrearrange :
      ((p : ℝ) ^ A) ^ (u * e) *
          ((p : ℝ) ^ D) ^ ((1 - u) * e) =
        (p : ℝ) ^ ((A * u + D * (1 - u)) * e) := by
    rw [← Real.rpow_mul hpR.le, ← Real.rpow_mul hpR.le,
      ← Real.rpow_add hpR]
    congr 1
    ring
  have hfinalPow :
      (p : ℝ) ^ ((A * u + D * (1 - u)) * e) ≤
        (p : ℝ) ^ ((H : ℝ) * (Lambda + epsilon)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ p by omega))
      hweighted
  have hscaleZero :
      wooleySourceNormalizationScale phi p B H s 0 gamma = Z := by
    simp [wooleySourceNormalizationScale, Z]
  calc
    wooleySourceNormalizedMixedMean phi p B H s r a b nu 0 gamma =
        (K / Z) ^ e := by
          simp only [wooleySourceNormalizedMixedMean, K, e, hscaleZero]
    _ ≤ (X / Z) ^ (u * e) * (Y / Z) ^ ((1 - u) * e) := hnormalized
    _ ≤ ((p : ℝ) ^ A) ^ (u * e) *
          ((p : ℝ) ^ D) ^ ((1 - u) * e) :=
      mul_le_mul hpowA hpowB (Real.rpow_nonneg hratioB0 _) (by positivity)
    _ = (p : ℝ) ^ ((A * u + D * (1 - u)) * e) := hrearrange
    _ ≤ (p : ℝ) ^ ((H : ℝ) * (Lambda + epsilon)) := hfinalPow

#print axioms wooleySourcePolynomial_lemma_4_2_of_conditioned_bounds

end

end GafniTao
