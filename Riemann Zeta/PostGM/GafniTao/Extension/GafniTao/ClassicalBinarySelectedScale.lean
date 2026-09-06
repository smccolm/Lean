import GafniTao.ClassicalBinarySelectedFamily
import RiemannZeta.GuthMaynard.ClassicalEndpointSlab

/-!
# Physical scale of the selected classical binary family

The branch-independent family still remembers whether its scale came from
the Type-I or Type-II side of the exact classical detector.  This file
extracts the corresponding physical inequalities and proves that a genuinely
positive Type-I threshold forces the selected block to begin before the
sharp zeta cutoff.  The latter argument is performed for both source signs.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Every selected binary block begins at or beyond the smaller detector
cutoff `X`, provided `X <= Y`. -/
theorem le_classicalBinarySelectedN
    {Y X kI kII : Nat} (hXY : X <= Y)
    (q : Fin (kI * 2 + kII * 2)) :
    X <= classicalBinarySelectedN Y X kI kII q := by
  unfold classicalBinarySelectedN
  cases hq : binaryScaleLabel q with
  | inl r =>
      simp only [Sum.elim_inl, classicalTypeIShellScaleN]
      exact hXY.trans (Nat.le_mul_of_pos_left Y (pow_pos (by omega) _))
  | inr r =>
      simp only [Sum.elim_inr, classicalTypeIIShellScaleN]
      exact Nat.le_mul_of_pos_left X (pow_pos (by omega) _)

/-- A selected Type-I block begins at or beyond the Type-I cutoff `Y`. -/
theorem le_classicalBinarySelectedN_of_typeI
    {Y X kI kII : Nat}
    (q : Fin (kI * 2 + kII * 2))
    (r : Fin (kI * 2)) (hq : binaryScaleLabel q = Sum.inl r) :
    Y <= classicalBinarySelectedN Y X kI kII q := by
  unfold classicalBinarySelectedN
  simp only [hq, Sum.elim_inl, classicalTypeIShellScaleN]
  exact Nat.le_mul_of_pos_left Y (pow_pos (by omega) _)

/-- A selected Type-II block lies in the exact half-open physical range
`[X,Y*X)` supplied by the dyadic detector. -/
theorem classicalBinarySelectedN_typeII_range
    {Y X kI kII : Nat} (hX : 0 < X)
    (hkII : kII <= Nat.clog 2 Y)
    (q : Fin (kI * 2 + kII * 2))
    (r : Fin (kII * 2)) (hq : binaryScaleLabel q = Sum.inr r) :
    X <= classicalBinarySelectedN Y X kI kII q /\
      classicalBinarySelectedN Y X kI kII q < Y * X := by
  unfold classicalBinarySelectedN
  simp only [hq, Sum.elim_inr, classicalTypeIIShellScaleN]
  have hr : (classicalTypeIIShellScalePair r).1.val < kII :=
    (classicalTypeIIShellScalePair r).1.isLt
  constructor
  · exact Nat.le_mul_of_pos_left X (pow_pos (by omega) _)
  · have hPow : 2 ^ (classicalTypeIIShellScalePair r).1.val < Y := by
      exact Nat.pow_lt_of_lt_clog (hr.trans_le hkII)
    exact Nat.mul_lt_mul_of_pos_right hPow hX

/-- A positive literal Type-I detector threshold forces the selected block
to start before the sharp zeta cutoff.  This is the signed-shell analogue of
`typeI_start_lt_cutoff_of_positive_large_value`; no support condition is
assumed separately. -/
theorem classicalBinarySelectedN_lt_cutoff_of_typeI_large
    {A Y X kI kII : Nat} {sigma q0 t : Real}
    (hq0 : 0 < q0) (hkI : 0 < kI)
    (q : Fin (kI * 2 + kII * 2))
    (r : Fin (kI * 2)) (hq : binaryScaleLabel q = Sum.inl r)
    (hLarge : Sum.elim
      (ClassicalTypeIShellScaleLarge A Y kI sigma q0)
      (ClassicalTypeIIShellScaleLarge Y X kII sigma)
      (binaryScaleLabel q) t) :
    classicalBinarySelectedN Y X kI kII q < A := by
  have hThreshold : 0 < ((3 / 4 : Real) * (q0 / 2)) / (kI : Real) := by
    positivity
  have hRaw : ((3 / 4 : Real) * (q0 / 2)) / (kI : Real) <=
      ‖sourceDirichletPoly (classicalTypeIShellScaleN Y r)
        (classicalTypeIShellScaleCoeff A sigma r) t‖ := by
    simpa only [hq, Sum.elim_inl] using hLarge
  have hNA : classicalTypeIShellScaleN Y r < A := by
    by_cases hsign : (classicalTypeIShellScalePair r).2 = 0
    · have hCoeff : classicalTypeIShellScaleCoeff A sigma r =
          conjugateCoeffs (classicalZetaLongLineCoeff A sigma) := by
        funext n
        simp [classicalTypeIShellScaleCoeff, signedClassicalLongCoeff, hsign]
      rw [hCoeff, norm_sourceDirichletPoly_conjugateCoeffs] at hRaw
      exact typeI_start_lt_cutoff_of_positive_large_value A
        (classicalTypeIShellScaleN Y r) sigma t
        (((3 / 4 : Real) * (q0 / 2)) / (kI : Real)) hThreshold
        hRaw
    · have hsignOne : (classicalTypeIShellScalePair r).2 = 1 := by
        apply Fin.eq_of_val_eq
        have hlt := (classicalTypeIShellScalePair r).2.isLt
        have hne : (classicalTypeIShellScalePair r).2.val ≠ 0 := by
          intro hz
          apply hsign
          apply Fin.eq_of_val_eq
          simpa using hz
        omega
      have hCoeff : classicalTypeIShellScaleCoeff A sigma r =
          classicalZetaLongLineCoeff A sigma := by
        funext n
        simp [classicalTypeIShellScaleCoeff, signedClassicalLongCoeff,
          hsignOne]
      rw [hCoeff] at hRaw
      exact typeI_start_lt_cutoff_of_positive_large_value A
        (classicalTypeIShellScaleN Y r) sigma (-t)
        (((3 / 4 : Real) * (q0 / 2)) / (kI : Real)) hThreshold
        (by simpa only [dirichletPoly_neg_eq_sourceDirichletPoly] using hRaw)
  simpa [classicalBinarySelectedN, hq] using hNA

#print axioms le_classicalBinarySelectedN
#print axioms le_classicalBinarySelectedN_of_typeI
#print axioms classicalBinarySelectedN_typeII_range
#print axioms classicalBinarySelectedN_lt_cutoff_of_typeI_large

end

end GafniTao
