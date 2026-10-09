import Dubon2026.AdelicClassicalReconstruction

/-! # Exact classical slash restriction of the original rational finite-adelic translate -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- Multiplying an original rational finite translate by its principal rational diagonal leaves exactly the genuine positive real matrix. -/
theorem adelicRationalTranslate_real_factor (r : GL(2, ℚ)⁺) (g : SL(2, ℝ)) :
    GeneralLinearGroup.map (algebraMap ℚ (AdeleRing ℤ ℚ)) r.val *
      (adelicRealSL2Embedding g * rationalAdelicFiniteGL2Embedding (rationalPositiveGL2ToFinite r)⁻¹) =
      adelicRealGL2Embedding ((rationalPositiveGL2ToReal r).val * toGL g) := by
  apply rationalAdelicGL2RealFiniteEquiv.injective
  rw [map_mul, map_mul, rationalAdelicGL2RealFiniteEquiv_rational,
    ← adelicRealGL2Embedding_toGL, adelicRealGL2Embedding_coordinates,
    rationalAdelicFiniteGL2Embedding_coordinates, adelicRealGL2Embedding_coordinates]
  change (rationalGL2ToReal r.val * (toGL g * 1),
    rationalPositiveGL2ToFinite r * (1 * (rationalPositiveGL2ToFinite r)⁻¹)) = _
  simp only [mul_one, one_mul, mul_inv_cancel]
  rfl

/-- The original rational finite-adelic inverse translate has exactly the true rational slash function with the pinned determinant-root correction. -/
theorem canonicalAdelic_rational_translate_real {N : ℕ} [NeZero N] {k : ℤ}
    (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (r : GL(2, ℚ)⁺) (g : SL(2, ℝ)) :
    canonicalAdelicGL2CuspLift N k F
      (adelicRealSL2Embedding g * rationalAdelicFiniteGL2Embedding (rationalPositiveGL2ToFinite r)⁻¹) =
        (realPositiveDetRoot (rationalPositiveGL2ToReal r) : ℂ) ^ (2 - k) *
          realWeightLift k ((F : ℍ → ℂ) ∣[k] (rationalPositiveGL2ToReal r).val) g := by
  have hr := canonicalAdelicGL2CuspLift_rational_invariant N F r.val
    (adelicRealSL2Embedding g * rationalAdelicFiniteGL2Embedding (rationalPositiveGL2ToFinite r)⁻¹)
  rw [adelicRationalTranslate_real_factor] at hr
  rw [← hr]
  change canonicalAdelicGL2CuspLift N k F
    (rationalAdelicGL2RealFiniteEquiv.symm (((rationalPositiveGL2ToReal r * toGLPos g).val), 1)) = _
  rw [canonicalAdelicGL2CuspLift_real_restriction, realPositiveUnitaryLift_left_slash]

end
end Dubon2026
