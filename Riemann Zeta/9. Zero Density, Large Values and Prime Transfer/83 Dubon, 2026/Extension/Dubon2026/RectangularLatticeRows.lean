import Dubon2026.LatticeEpsteinPrimitive

/-! # Exact reindexing and scaling of rectangular Eisenstein sublattices -/

namespace Dubon2026

open UpperHalfPlane

noncomputable section

/-- The literal rectangular integer sublattice, with independent coordinate divisibilities. -/
def rectangularLatticeRows (a b : ℕ) : Set (Fin 2 → ℤ) :=
  {v | (a : ℤ) ∣ v 0 ∧ (b : ℤ) ∣ v 1}

/-- Multiplication of the two actual integer coordinates parametrizes a positive rectangular lattice. -/
def rectangularLatticeEquiv (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (Fin 2 → ℤ) ≃ rectangularLatticeRows a b where
  toFun v := ⟨![(a : ℤ) * v 0, (b : ℤ) * v 1],
    ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩⟩
  invFun v := ![v.val 0 / (a : ℤ), v.val 1 / (b : ℤ)]
  left_inv v := by
    funext i
    fin_cases i <;> simp [Nat.ne_of_gt ha, Nat.ne_of_gt hb]
  right_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact Int.mul_ediv_cancel' v.property.1
    · exact Int.mul_ediv_cancel' v.property.2

/-- The actual point (a/b)z, using the positive-real action already defined by Mathlib. -/
def rectangularLatticePoint (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (z : ℍ) : ℍ :=
  (⟨(a : ℝ) / b, div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb)⟩ : {x : ℝ // 0 < x}) • z

/-- The rectangular rescaling has the literal complex coordinate (a/b)z. -/
theorem coe_rectangularLatticePoint (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (z : ℍ) :
    (rectangularLatticePoint a b ha hb z : ℂ) = ((a : ℂ) / b) * z := by
  simp [rectangularLatticePoint, coe_pos_real_smul, Complex.real_smul]

/-- The imaginary part is scaled by the same actual positive ratio. -/
theorem im_rectangularLatticePoint (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (z : ℍ) :
    (rectangularLatticePoint a b ha hb z).im = ((a : ℝ) / b) * z.im := by
  exact pos_real_im _ _

/-- The exact rectangular height factor is 1/(ab), including the zero row. -/
theorem eisensteinRowHeight_rectangular (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (v : Fin 2 → ℤ) (z : ℍ) :
    eisensteinRowHeight ![(a : ℤ) * v 0, (b : ℤ) * v 1] z =
      ((a : ℝ) * b)⁻¹ * eisensteinRowHeight v (rectangularLatticePoint a b ha hb z) := by
  have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)
  have hbC : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)
  have he : (((a : ℤ) * v 0 : ℤ) : ℂ) * z + ((b : ℤ) * v 1 : ℤ) =
      (b : ℂ) * ((v 0 : ℂ) * (rectangularLatticePoint a b ha hb z : ℂ) + v 1) := by
    rw [coe_rectangularLatticePoint]
    push_cast
    field_simp
  simp only [eisensteinRowHeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, he, norm_mul, Complex.norm_natCast, mul_pow,
    im_rectangularLatticePoint, div_eq_mul_inv, mul_inv_rev]
  have hc : z.im * ((b : ℝ) ^ 2)⁻¹ =
      (b : ℝ)⁻¹ * (a : ℝ)⁻¹ * ((a : ℝ) * (b : ℝ)⁻¹ * z.im) := by
    field_simp
  linear_combination hc * (‖(v 0 : ℂ) * (rectangularLatticePoint a b ha hb z : ℂ) + v 1‖ ^ 2)⁻¹

/-- The genuine complex Eisenstein kernel has the exact factor (ab)^(-s) on a rectangular sublattice. -/
theorem nonholomorphicEisensteinTerm_rectangular (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (v : Fin 2 → ℤ) (z : ℍ) (s : ℂ) :
    nonholomorphicEisensteinTerm s ![(a : ℤ) * v 0, (b : ℤ) * v 1] z =
      ((a : ℂ) * b) ^ (-s) *
        nonholomorphicEisensteinTerm s v (rectangularLatticePoint a b ha hb z) := by
  rw [nonholomorphicEisensteinTerm, eisensteinRowHeight_rectangular a b ha hb,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity)
      (eisensteinRowHeight_nonneg _ _), Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ (by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
  rfl

/-- The actual half-sum on a positive rectangular lattice is a rescaled full Epstein series. -/
theorem rectangularLatticeSeries_eq_epstein (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    (1 / 2 : ℂ) * (∑' v : rectangularLatticeRows a b, nonholomorphicEisensteinTerm s v.val z) =
      ((a : ℂ) * b) ^ (-s) * latticeEpsteinSeries (rectangularLatticePoint a b ha hb z) s := by
  rw [← (rectangularLatticeEquiv a b ha hb).tsum_eq]
  change (1 / 2 : ℂ) * (∑' v : Fin 2 → ℤ,
    nonholomorphicEisensteinTerm s ![(a : ℤ) * v 0, (b : ℤ) * v 1] z) = _
  simp_rw [nonholomorphicEisensteinTerm_rectangular a b ha hb]
  rw [tsum_mul_left, latticeEpstein_full_sum _ hs]
  ring

end
end Dubon2026
