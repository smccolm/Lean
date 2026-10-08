import Dubon2026.AdelicReflectionPairing

/-! # The original full adelic cyclic action preserves its genuine quotient L2 inner product -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open MeasureTheory
open scoped MatrixGroups

/-- An original full adelic matrix with positive real determinant preserves the actual L2 inner product. -/
theorem adelicLiftCyclic_inner_of_positive (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule) (h : RationalAdelicGL2)
    (hh : (rationalAdelicGL2RealFiniteEquiv h).1 ∈ GLPos (Fin 2) ℝ) :
    inner ℂ (adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation h v))
      (adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation h w)) =
      inner ℂ (adelicProjectiveCyclicToL2 N f v) (adelicProjectiveCyclicToL2 N f w) := by
  let a : GL(2, ℝ)⁺ × GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) :=
    (⟨(rationalAdelicGL2RealFiniteEquiv h).1, hh⟩, (rationalAdelicGL2RealFiniteEquiv h).2)
  have he : positiveAdelicGL2Embedding a = h := rationalAdelicGL2RealFiniteEquiv.symm_apply_apply h
  rw [← he]
  exact adelicLiftCyclic_positive_inner N f v w a

/-- Every actual original full adelic right translation, including the negative real component, preserves the faithful L2 inner product. -/
theorem adelicLiftCyclic_inner (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v w : (adelicLiftCyclicRepresentation N k f).toSubmodule) (h : RationalAdelicGL2) :
    inner ℂ (adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation h v))
      (adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation h w)) =
      inner ℂ (adelicProjectiveCyclicToL2 N f v) (adelicProjectiveCyclicToL2 N f w) := by
  by_cases hh : (rationalAdelicGL2RealFiniteEquiv h).1 ∈ GLPos (Fin 2) ℝ
  · exact adelicLiftCyclic_inner_of_positive N f v w h hh
  · have hp : (rationalAdelicGL2RealFiniteEquiv (canonicalAdelicGL2Reflection * h)).1 ∈
        GLPos (Fin 2) ℝ := by
      rw [map_mul, canonicalAdelicGL2Reflection, rationalAdelicGL2RealFiniteEquiv_rational]
      change 0 < (GeneralLinearGroup.det (rationalGL2ToReal rationalGL2Reflection *
        (rationalAdelicGL2RealFiniteEquiv h).1)).val
      rw [map_mul, Units.val_mul, rationalGL2Reflection_real_det, neg_one_mul]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hh) (Units.ne_zero _))
    have ht (x : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
        (adelicLiftCyclicRepresentation N k f).toRepresentation h x =
        (adelicLiftCyclicRepresentation N k f).toRepresentation canonicalAdelicGL2Reflection
          ((adelicLiftCyclicRepresentation N k f).toRepresentation (canonicalAdelicGL2Reflection * h) x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc,
        canonicalAdelicGL2Reflection_mul_self, one_mul]
    rw [ht v, ht w, adelicLiftCyclic_reflection_inner]
    exact adelicLiftCyclic_inner_of_positive N f v w _ hp

/-- Every genuine full adelic matrix preserves exactly the original quotient L2 norm. -/
theorem adelicLiftCyclic_norm (N : ℕ) [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) (h : RationalAdelicGL2) :
    ‖adelicProjectiveCyclicToL2 N f ((adelicLiftCyclicRepresentation N k f).toRepresentation h v)‖ =
      ‖adelicProjectiveCyclicToL2 N f v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), adelicLiftCyclic_inner]

end
end Dubon2026
