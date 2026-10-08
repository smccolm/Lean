import Dubon2026.AdelicUnipotentAverages
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Genuine unipotent cuspidality of the original function on the entire canonical adelic GL2 group -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

/-- The original rational reflection maps to the literal reflection over every actual scalar ring. -/
theorem rationalGL2Reflection_map {R : Type*} [CommRing R] (f : ℚ →+* R) :
    Matrix.GeneralLinearGroup.map f rationalGL2Reflection = gl2UnitFirstDiagonal (-1 : Rˣ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalGL2Reflection, gl2UnitFirstDiagonal, Matrix.GeneralLinearGroup.map]

/-- Actual reflection conjugation negates the original upper unipotent parameter. -/
theorem gl2Reflection_upperRightHom {R : Type*} [CommRing R] (x : R) :
    gl2UnitFirstDiagonal (-1 : Rˣ) * upperRightHom x =
      upperRightHom (-x) * gl2UnitFirstDiagonal (-1 : Rˣ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl2UnitFirstDiagonal, upperRightHom, Matrix.mul_apply, Fin.sum_univ_two]

/-- Rational invariance identifies reflection of the original full adelic cusp function with negation on its genuine additive unipotent quotient. -/
theorem adelicUnipotentQuotientFunction_reflection (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) (z : RationalAdelicAdditiveQuotient) :
    adelicUnipotentQuotientFunction N f g z =
      adelicUnipotentQuotientFunction N f
        (Matrix.GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) rationalGL2Reflection * g) (-z) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  change canonicalAdelicGL2CuspLift N k f (upperRightHom x * g) =
    canonicalAdelicGL2CuspLift N k f (upperRightHom (-x) *
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) rationalGL2Reflection * g))
  rw [← canonicalAdelicGL2CuspLift_rational_invariant N f rationalGL2Reflection
    (upperRightHom x * g)]
  congr 1
  rw [rationalGL2Reflection_map, ← mul_assoc, gl2Reflection_upperRightHom, mul_assoc]

/-- The original unipotent Haar integral is unchanged by the actual rational reflection of the adelic group point. -/
theorem adelicUnipotentQuotientFunction_integral_reflection (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) :
    (∫ z, adelicUnipotentQuotientFunction N f g z ∂rationalAdelicAdditiveHaar) =
      ∫ z, adelicUnipotentQuotientFunction N f
        (Matrix.GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) rationalGL2Reflection * g) z
          ∂rationalAdelicAdditiveHaar := by
  simp_rw [adelicUnipotentQuotientFunction_reflection N f g]
  exact integral_neg_eq_self _ rationalAdelicAdditiveHaar

/-- The actual original classical cusp form has zero unipotent Haar integral at every point of canonical full adelic GL2. -/
theorem canonicalAdelicGL2CuspLift_unipotent_cuspidal (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (g : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ)) :
    (∫ z : RationalAdelicAdditiveQuotient,
      adelicUnipotentQuotientFunction N f g z ∂rationalAdelicAdditiveHaar) = 0 := by
  have hpos (b : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing ℤ ℚ))
      (hb : 0 < (Matrix.GeneralLinearGroup.det (rationalAdelicGL2RealFiniteEquiv b).1).val) :
      (∫ z, adelicUnipotentQuotientFunction N f b z ∂rationalAdelicAdditiveHaar) = 0 := by
    let r : GL(2, ℝ)⁺ := ⟨(rationalAdelicGL2RealFiniteEquiv b).1, hb⟩
    have hz := adelicUnipotentQuotientFunction_integral_zero_positive N f r
      (rationalAdelicGL2RealFiniteEquiv b).2
    simpa only [r, Prod.mk.eta, MulEquiv.symm_apply_apply] using hz
  by_cases hp : 0 < (Matrix.GeneralLinearGroup.det (rationalAdelicGL2RealFiniteEquiv g).1).val
  · exact hpos g hp
  · rw [adelicUnipotentQuotientFunction_integral_reflection N f g]
    apply hpos
    rw [map_mul, rationalAdelicGL2RealFiniteEquiv_rational]
    change 0 < (Matrix.GeneralLinearGroup.det
      (rationalGL2ToReal rationalGL2Reflection * (rationalAdelicGL2RealFiniteEquiv g).1)).val
    rw [map_mul, Units.val_mul, rationalGL2Reflection_real_det, neg_one_mul]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp)
      (Units.ne_zero (Matrix.GeneralLinearGroup.det (rationalAdelicGL2RealFiniteEquiv g).1)))

end
end Dubon2026
