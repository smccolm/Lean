import Dubon2026.LocalCoefficientMatrixLifting
import Mathlib.Algebra.Group.Pi.Units

/-! Lift a Frobenius matrix with its prescribed determinant. The original
local coefficient lifting theorem supplies an invertible lift; one diagonal
unit corrects its determinant without changing its reduction. This discharges
the matrix-existence input to DUB-17's unramified local deformation lifting. -/

namespace Dubon2026
noncomputable section
open Matrix

/-- Every invertible matrix lifts along a surjective local coefficient
map with any compatible prescribed determinant. -/
theorem generalLinearGroup_fixedDeterminant_lift
    {ι A B : Type} [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]
    (i₀ : ι) (f : A →+* B) (hf : Function.Surjective f) [IsLocalHom f]
    (U : GeneralLinearGroup ι B) (d : Aˣ)
    (hd : Units.map f.toMonoidHom d = GeneralLinearGroup.det U) :
    ∃ V : GeneralLinearGroup ι A, GeneralLinearGroup.map f V = U ∧
      GeneralLinearGroup.det V = d := by
  obtain ⟨W, hW⟩ := generalLinearGroup_map_surjective f hf U
  let u : Aˣ := d * (GeneralLinearGroup.det W)⁻¹
  have hdetmap : Units.map f.toMonoidHom (GeneralLinearGroup.det W) =
      GeneralLinearGroup.det U :=
    (GeneralLinearGroup.map_det f W).symm.trans (congrArg GeneralLinearGroup.det hW)
  have hu : Units.map f.toMonoidHom u = 1 := by
    change Units.map f.toMonoidHom (d * (GeneralLinearGroup.det W)⁻¹) = 1
    rw [map_mul, map_inv, hd, hdetmap, mul_inv_cancel]
  have huval : f (u : A) = 1 := congrArg Units.val hu
  let v : ι → Aˣ := Pi.mulSingle i₀ u
  let D : GeneralLinearGroup ι A := Units.map (diagonalRingHom ι A).toMonoidHom
    ((MulEquiv.piUnits (M := fun _ : ι => A)).symm v)
  have hDdet : GeneralLinearGroup.det D = u := by
    apply Units.ext
    change Matrix.det (diagonal (fun i => (v i : A))) = (u : A)
    rw [det_diagonal]
    simp only [v, Pi.mulSingle_apply]
    simp_rw [apply_ite Units.val]
    simp
  have hDmap : GeneralLinearGroup.map f D = 1 := by
    apply Units.ext
    ext i j
    change f (diagonal (fun k => (v k : A)) i j) =
      (1 : Matrix ι ι B) i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = i₀
      · subst i
        simp [v, huval]
      · simp [v, Pi.mulSingle_apply, hi]
    · simp [Matrix.diagonal, hij]
  refine ⟨D * W, ?_, ?_⟩
  · rw [map_mul, hDmap, hW, one_mul]
  · rw [map_mul, hDdet]
    exact inv_mul_cancel_right d (GeneralLinearGroup.det W)

end
end Dubon2026
