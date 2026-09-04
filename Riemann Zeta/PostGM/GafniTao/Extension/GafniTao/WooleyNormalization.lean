import GafniTao.WooleySourceSection8

/-!
# Wooley equation (3.24)

This file defines the literal order-of-magnitude normalization used in
Sections 8--10.  The denominator and the exponent are exposed separately so
that every later cancellation has a named, auditable hypothesis.
-/

namespace GafniTao

noncomputable section

/-- The exponent `(k-1)/(r(k-r))` in Wooley (3.24). -/
def wooleyNormalizationExponent (k r : ℕ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) /
    (((r : ℕ) : ℝ) * ((k - r : ℕ) : ℝ))

/-- The common denominator `p^(Delta H) U^{B,H}` in Wooley (3.24). -/
def wooleySourceNormalizationScale {k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B H s : ℕ)
    [NeZero p] [NeZero (p ^ B)] (Delta : ℝ)
    (gamma : WooleySourceSequence) : ℝ :=
  (p : ℝ) ^ (Delta * (H : ℝ)) *
    wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ H) phi gamma

/-- The literal normalized mixed mean in Wooley equation (3.24). -/
def wooleySourceNormalizedMixedMean {k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B H s r a b nu : ℕ)
    [NeZero p] [NeZero (p ^ B)] (Delta : ℝ)
    (gamma : WooleySourceSequence) : ℝ :=
  (wooleySourcePolynomialMixedMean phi s r p B a b nu gamma /
      wooleySourceNormalizationScale phi p B H s Delta gamma) ^
    wooleyNormalizationExponent k r

theorem wooleyNormalizationExponent_pos
    {k r : ℕ} (hr : 1 ≤ r) (hrk : r < k) :
    0 < wooleyNormalizationExponent k r := by
  unfold wooleyNormalizationExponent
  have hk : 1 < k := lt_of_le_of_lt hr hrk
  have hkr : 0 < k - r := Nat.sub_pos_of_lt hrk
  have hnum : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hk
  have hden : (0 : ℝ) < (r : ℝ) * (k - r : ℕ) := by
    positivity
  exact div_pos hnum hden

theorem wooleyNormalizationExponent_le_one
    {k r : ℕ} (hr : 1 ≤ r) (hrk : r < k) :
    wooleyNormalizationExponent k r ≤ 1 := by
  unfold wooleyNormalizationExponent
  have hkr : 1 ≤ k - r := Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.sub_pos_of_lt hrk))
  have hden : (0 : ℝ) < (r : ℝ) * (k - r : ℕ) := by positivity
  rw [div_le_one hden]
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hkrR : (1 : ℝ) ≤ (k - r : ℕ) := by exact_mod_cast hkr
  have hsplit : (k : ℝ) = (r : ℝ) + (k - r : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le hrk.le).symm
  have hprod := mul_nonneg (sub_nonneg.mpr hrR) (sub_nonneg.mpr hkrR)
  rw [Nat.cast_sub (show 1 ≤ k by omega)]
  have hid :
      (r : ℝ) * (k - r : ℕ) - ((k : ℝ) - 1) =
        ((r : ℝ) - 1) * ((k - r : ℕ) - 1) := by
    rw [hsplit]
    ring
  norm_num only [Nat.cast_one] at *
  nlinarith [hprod]

theorem wooleyNormalizationExponent_symm
    {k r : ℕ} (hrk : r ≤ k) :
    wooleyNormalizationExponent k (k - r) =
      wooleyNormalizationExponent k r := by
  unfold wooleyNormalizationExponent
  rw [Nat.sub_sub_self hrk]
  ring

theorem wooleyNormalizationExponent_one
    {k : ℕ} (hk : 2 ≤ k) :
    wooleyNormalizationExponent k 1 = 1 := by
  unfold wooleyNormalizationExponent
  rw [Nat.cast_one, one_mul]
  have hk1 : 1 ≤ k := by omega
  rw [Nat.cast_sub hk1]
  norm_num
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  intro hzero
  linarith

theorem wooleyNormalizationExponent_pred
    {k : ℕ} (hk : 2 ≤ k) :
    wooleyNormalizationExponent k (k - 1) = 1 := by
  rw [wooleyNormalizationExponent_symm (show 1 ≤ k by omega)]
  exact wooleyNormalizationExponent_one hk

/-- The exponent conversion for the `r-1` factor in Wooley (8.4). -/
theorem wooley_normalization_pred_exponent
    {k r : ℕ} (hr : 2 ≤ r) (hrk : r < k) :
    (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) *
        wooleyNormalizationExponent k r =
      (1 - 1 / (r : ℝ)) * wooleyNormalizationExponent k (r - 1) := by
  have hsub : k - (r - 1) = k - r + 1 := by omega
  simp only [wooleyNormalizationExponent, hsub,
    Nat.cast_sub hrk.le, Nat.cast_sub (show 1 ≤ r by omega),
    Nat.cast_add, Nat.cast_one]
  have hkR : (r : ℝ) < k := by exact_mod_cast hrk
  have hrR : (1 : ℝ) < r := by exact_mod_cast hr
  have hkr0 : (k : ℝ) - r ≠ 0 := by linarith
  have hkr10 : (k : ℝ) - r + 1 ≠ 0 := by linarith
  have hr0 : (r : ℝ) ≠ 0 := by linarith
  have hr10 : (r : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hkr0, hkr10, hr0, hr10]

/-- The complementary exponent in (8.3) is `1-1/(k-r+1)`. -/
theorem wooley_section8_raw_complement
    {k r : ℕ} (hrk : r < k) :
    (((k - r : ℕ) : ℝ) / ((k - r + 1 : ℕ) : ℝ)) =
      1 - 1 / ((k - r + 1 : ℕ) : ℝ) := by
  symm
  exact wooley_section8_weight_complement hrk

theorem wooleySourceNormalizationScale_nonneg
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B H s : ℕ) [NeZero p] [NeZero (p ^ B)]
    (Delta : ℝ) (gamma : WooleySourceSequence) :
    0 ≤ wooleySourceNormalizationScale phi p B H s Delta gamma := by
  unfold wooleySourceNormalizationScale
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (by
      unfold wooleySourcePolynomialConditionedMean
      split_ifs with hmass
      · exact le_rfl
      · apply mul_nonneg (inv_nonneg.mpr (wooleySourceMassSq_nonneg gamma))
        exact Finset.sum_nonneg fun xi hxi => mul_nonneg
          (wooleySourceResidueMassSq_nonneg gamma _ xi)
          (mul_nonneg (inv_nonneg.mpr (by positivity))
            (Finset.sum_nonneg fun alpha halpha => pow_nonneg (norm_nonneg _) _)))

theorem wooleySourcePolynomialConditionedMean_nonneg
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (s q qH : ℕ) [NeZero q] [NeZero qH]
    (gamma : WooleySourceSequence) :
    0 ≤ wooleySourcePolynomialConditionedMean s q qH phi gamma := by
  unfold wooleySourcePolynomialConditionedMean
  split_ifs
  · exact le_rfl
  · apply mul_nonneg (inv_nonneg.mpr (wooleySourceMassSq_nonneg gamma))
    exact Finset.sum_nonneg fun xi hxi => mul_nonneg
      (wooleySourceResidueMassSq_nonneg gamma _ xi)
      (mul_nonneg (inv_nonneg.mpr (by positivity))
        (Finset.sum_nonneg fun alpha halpha => pow_nonneg (norm_nonneg _) _))

theorem wooleySourceNormalizedMixedMean_nonneg
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B H s r a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (Delta : ℝ) (gamma : WooleySourceSequence) :
    0 ≤ wooleySourceNormalizedMixedMean
      phi p B H s r a b nu Delta gamma := by
  unfold wooleySourceNormalizedMixedMean
  exact Real.rpow_nonneg (div_nonneg
    (wooleySourcePolynomialMixedMean_nonneg
      phi s r p B a b nu gamma)
    (wooleySourceNormalizationScale_nonneg phi p B H s Delta gamma)) _

/-- Quotient-normalized two-factor interpolation.  This is the abstract
algebra behind the passage from Lemma 8.1 to Lemma 8.2. -/
theorem wooley_normalized_two_factor
    {A X Y Z D u v e : ℝ}
    (hA : 0 ≤ A) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hZ : 0 < Z) (hD : 0 ≤ D)
    (he : 0 ≤ e) (huv : u + v = 1)
    (hmain : A ≤ D * (X ^ u * Y ^ v)) :
    (A / Z) ^ e ≤
      D ^ e * (X / Z) ^ (u * e) * (Y / Z) ^ (v * e) := by
  have hAZ : 0 ≤ A / Z := div_nonneg hA hZ.le
  have hright : 0 ≤ D * (X ^ u * Y ^ v) / Z := by positivity
  have hdiv : A / Z ≤ D * (X ^ u * Y ^ v) / Z :=
    div_le_div_of_nonneg_right hmain hZ.le
  have hpow := Real.rpow_le_rpow hAZ hdiv he
  have hZne : Z ≠ 0 := ne_of_gt hZ
  have hrewrite :
      D * (X ^ u * Y ^ v) / Z =
        D * ((X / Z) ^ u * (Y / Z) ^ v) := by
    rw [Real.div_rpow hX hZ.le, Real.div_rpow hY hZ.le]
    have hzpow : Z ^ u * Z ^ v = Z := by
      rw [← Real.rpow_add hZ, huv, Real.rpow_one]
    have hzInv : (Z ^ u)⁻¹ * (Z ^ v)⁻¹ = Z⁻¹ := by
      rw [← mul_inv, hzpow]
    simp only [div_eq_mul_inv]
    calc
      D * (X ^ u * Y ^ v) * Z⁻¹ =
          D * (X ^ u * Y ^ v) * ((Z ^ u)⁻¹ * (Z ^ v)⁻¹) := by
        rw [hzInv]
      _ = D * (X ^ u * (Z ^ u)⁻¹ * (Y ^ v * (Z ^ v)⁻¹)) := by
        ring
  calc
    (A / Z) ^ e ≤ (D * (X ^ u * Y ^ v) / Z) ^ e := hpow
    _ = (D * ((X / Z) ^ u * (Y / Z) ^ v)) ^ e := by rw [hrewrite]
    _ = D ^ e * ((X / Z) ^ u * (Y / Z) ^ v) ^ e := by
      rw [Real.mul_rpow hD
        (mul_nonneg (Real.rpow_nonneg (div_nonneg hX hZ.le) u)
          (Real.rpow_nonneg (div_nonneg hY hZ.le) v))]
    _ = D ^ e *
        ((X / Z) ^ u) ^ e * ((Y / Z) ^ v) ^ e := by
      rw [Real.mul_rpow
        (Real.rpow_nonneg (div_nonneg hX hZ.le) u)
        (Real.rpow_nonneg (div_nonneg hY hZ.le) v)]
      ring
    _ = D ^ e * (X / Z) ^ (u * e) * (Y / Z) ^ (v * e) := by
      rw [Real.rpow_mul (div_nonneg hX hZ.le),
        Real.rpow_mul (div_nonneg hY hZ.le)]

#print axioms wooleyNormalizationExponent_pos
#print axioms wooleyNormalizationExponent_le_one
#print axioms wooleyNormalizationExponent_symm
#print axioms wooleyNormalizationExponent_one
#print axioms wooleyNormalizationExponent_pred
#print axioms wooley_normalization_pred_exponent
#print axioms wooley_section8_raw_complement
#print axioms wooleySourceNormalizationScale_nonneg
#print axioms wooleySourcePolynomialConditionedMean_nonneg
#print axioms wooleySourceNormalizedMixedMean_nonneg
#print axioms wooley_normalized_two_factor

end

end GafniTao
