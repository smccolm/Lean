import GafniTao.WooleySection4Lemma42
import GafniTao.WooleySection10Bound

/-!
# The terminal normalized estimate in Wooley Section 10

Lemma 4.2 is needed at its sharper pre-relaxation exponent.  This file
performs the exact change from normalization parameter `0` to `Lambda` and
keeps the exponent `(k-1)/(r(k-r))` visible throughout.
-/

namespace GafniTao

noncomputable section

/-- The sharp Lemma-4.2 estimate at normalization zero implies the terminal
`p^(H epsilon)` estimate used after (10.9). -/
theorem wooleySourceNormalizedMixedMean_terminal
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B H r a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (Lambda epsilon D : ℝ) (gamma : WooleySourceSequence)
    (hp : 2 ≤ p) (hr : 1 ≤ r) (hrk : r < k)
    (hepsilon : 0 ≤ epsilon) (hD : 0 ≤ D)
    (hzeroBound :
      wooleySourceNormalizedMixedMean phi p B H (wooleyTriangular k)
          r a b nu 0 gamma ≤
        D * (p : ℝ) ^
          (((H : ℝ) * (Lambda + epsilon)) *
            wooleyNormalizationExponent k r)) :
    wooleySourceNormalizedMixedMean phi p B H (wooleyTriangular k)
        r a b nu Lambda gamma ≤
      D * (p : ℝ) ^ ((H : ℝ) * epsilon) := by
  let s := wooleyTriangular k
  let e := wooleyNormalizationExponent k r
  let K := wooleySourcePolynomialMixedMean phi s r p B a b nu gamma
  let Z := wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ H) phi gamma
  have he0 : 0 ≤ e := (wooleyNormalizationExponent_pos hr hrk).le
  have he1 : e ≤ 1 := wooleyNormalizationExponent_le_one hr hrk
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact wooleySourcePolynomialMixedMean_nonneg phi s r p B a b nu gamma
  have hZ0 : 0 ≤ Z := by
    dsimp [Z]
    exact wooleySourcePolynomialConditionedMean_nonneg phi s (p ^ B)
      (p ^ H) gamma
  by_cases hZzero : Z = 0
  · unfold wooleySourceNormalizedMixedMean wooleySourceNormalizationScale
    simp only [show wooleySourcePolynomialConditionedMean
        (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma = 0 by
          simpa only [Z, s] using hZzero,
      mul_zero, div_zero, Real.zero_rpow
        (ne_of_gt (wooleyNormalizationExponent_pos hr hrk))]
    exact mul_nonneg hD (Real.rpow_nonneg (by positivity) _)
  have hZpos : 0 < Z := lt_of_le_of_ne hZ0 (Ne.symm hZzero)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  let P : ℝ := (p : ℝ) ^ (Lambda * (H : ℝ))
  have hPpos : 0 < P := Real.rpow_pos_of_pos hpR _
  have hbase : K / (P * Z) = (K / Z) / P := by
    field_simp
  have hscaleLambda :
      wooleySourceNormalizationScale phi p B H s Lambda gamma = P * Z := by
    simp only [wooleySourceNormalizationScale, P, Z, s]
  have hscaleZero :
      wooleySourceNormalizationScale phi p B H s 0 gamma = Z := by
    simp [wooleySourceNormalizationScale, Z]
  have hchange :
      wooleySourceNormalizedMixedMean phi p B H s r a b nu Lambda gamma =
        wooleySourceNormalizedMixedMean phi p B H s r a b nu 0 gamma /
          (p : ℝ) ^ ((Lambda * (H : ℝ)) * e) := by
    unfold wooleySourceNormalizedMixedMean
    rw [hscaleLambda, hscaleZero, hbase,
      Real.div_rpow (div_nonneg hK0 hZpos.le) hPpos.le,
      ← Real.rpow_mul hpR.le]
  have hdenPos : 0 < (p : ℝ) ^ ((Lambda * (H : ℝ)) * e) :=
    Real.rpow_pos_of_pos hpR _
  rw [hchange]
  apply (div_le_div_of_nonneg_right hzeroBound hdenPos.le).trans
  have hexact :
      D * (p : ℝ) ^ (((H : ℝ) * (Lambda + epsilon)) * e) /
          (p : ℝ) ^ ((Lambda * (H : ℝ)) * e) =
        D * (p : ℝ) ^ (((H : ℝ) * epsilon) * e) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hpR.le]
    calc
      D * (p : ℝ) ^ ((H : ℝ) * (Lambda + epsilon) * e) *
          (p : ℝ) ^ (-(Lambda * (H : ℝ) * e)) =
        D * ((p : ℝ) ^ ((H : ℝ) * (Lambda + epsilon) * e) *
          (p : ℝ) ^ (-(Lambda * (H : ℝ) * e))) := by ring_nf
      _ = D * (p : ℝ) ^ (((H : ℝ) * epsilon) * e) := by
        rw [← Real.rpow_add hpR]
        congr 1
        ring_nf
  rw [hexact]
  have hHepsilon : 0 ≤ (H : ℝ) * epsilon :=
    mul_nonneg (Nat.cast_nonneg _) hepsilon
  have hexponent : ((H : ℝ) * epsilon) * e ≤ (H : ℝ) * epsilon :=
    mul_le_of_le_one_right hHepsilon he1
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ p by omega)) hexponent) hD

#print axioms wooleySourceNormalizedMixedMean_terminal

end

end GafniTao
