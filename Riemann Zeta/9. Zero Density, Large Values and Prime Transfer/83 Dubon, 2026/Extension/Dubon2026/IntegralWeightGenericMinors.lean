import Dubon2026.GeneralLinearIntegralTorsion
import Mathlib.RingTheory.Localization.FractionRing

/-! Nonvanishing of the actual generic inverse's principal minors.
Evaluation at the identity certifies these minors in the original regular
coordinate domain. Its fraction-field embedding then supplies the open-cell
hypotheses needed for highest-line uniqueness, without a density assumption.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] [IsDomain R] (n : ℕ)

/-- Every leading principal minor of the actual generic inverse is nonzero in the original coordinate domain. -/
theorem integralWeightGenericInverse_leading_ne_zero (k : ℕ) (hk : k ≤ n) :
    (((generalLinearRegularGeneric R n)⁻¹).val.submatrix
      (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  let e := generalLinearRegularEval (R := R) (1 : GeneralLinearGroup (Fin n) R)
  have he : GeneralLinearGroup.map e.toRingHom ((generalLinearRegularGeneric R n)⁻¹) = 1 := by
    rw [map_inv, generalLinearRegularGeneric_eval, inv_one]
  have hm : (((generalLinearRegularGeneric R n)⁻¹).val.submatrix
      (Fin.castLE hk) (Fin.castLE hk)).map e = 1 := by
    ext i j
    have h := congrArg (fun g : GeneralLinearGroup (Fin n) R =>
      g.val (Fin.castLE hk i) (Fin.castLE hk j)) he
    change e (((generalLinearRegularGeneric R n)⁻¹).val
      (Fin.castLE hk i) (Fin.castLE hk j)) =
        (1 : Matrix (Fin n) (Fin n) R) (Fin.castLE hk i) (Fin.castLE hk j) at h
    simpa only [Matrix.map_apply, Matrix.submatrix_apply,
      Matrix.one_apply, Fin.castLE_inj] using h
  intro hzero
  have h := congrArg e hzero
  rw [map_zero, AlgHom.map_det, AlgHom.mapMatrix_apply, hm, Matrix.det_one] at h
  exact one_ne_zero h

/-- The actual generic inverse retains its nonzero leading minors in the fraction field of the original coordinate domain. -/
theorem integralWeightGenericInverse_fraction_leading_ne_zero (k : ℕ) (hk : k ≤ n) :
    ((GeneralLinearGroup.map
      (algebraMap (GeneralLinearRegularFunctions R n)
        (FractionRing (GeneralLinearRegularFunctions R n)))
      ((generalLinearRegularGeneric R n)⁻¹)).val.submatrix
        (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
  let f := algebraMap (GeneralLinearRegularFunctions R n)
    (FractionRing (GeneralLinearRegularFunctions R n))
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  change (((((generalLinearRegularGeneric R n)⁻¹).val).map f).submatrix
    (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0
  change ((((generalLinearRegularGeneric R n)⁻¹).val.submatrix
    (Fin.castLE hk) (Fin.castLE hk)).map f).det ≠ 0
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact fun h => integralWeightGenericInverse_leading_ne_zero R n k hk
    (hinj (h.trans f.map_zero.symm))

end
end Dubon2026
