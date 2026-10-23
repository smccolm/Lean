import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Basic

/-! Transpose in fixed complex coordinates, used only to transport the
actual cusp Hecke operators to the original period space. Proving its
evaluation and faithfulness abstractly avoids unfolding the concrete
modular-function field while checking the coordinate equivalence.
-/
namespace Dubon2026
noncomputable section
variable {M P : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup P] [Module ℂ P]
variable (e : P ≃ₗ[ℂ] Module.Dual ℂ M)

/-- Transpose expressed through a given complex coordinate equivalence to the dual space. -/
def dualCoordinateTranspose : Module.End ℂ M →ₗ[ℂ] Module.End ℂ P :=
  (e.symm.conjAlgEquiv ℂ).toLinearMap.comp (Module.Dual.transpose (R := ℂ))

theorem dualCoordinateTranspose_apply (T : Module.End ℂ M) (v : P) :
    e (dualCoordinateTranspose e T v) = T.dualMap (e v) := e.apply_symm_apply _

theorem dualCoordinateTranspose_injective : Function.Injective (dualCoordinateTranspose e) := by
  intro T U h
  apply LinearMap.ext
  intro f
  have hdu (φ : Module.Dual ℂ M) : T.dualMap φ = U.dualMap φ := by
    have he := (dualCoordinateTranspose_apply e T (e.symm φ)).symm.trans
      ((congrArg e (LinearMap.congr_fun h (e.symm φ))).trans
        (dualCoordinateTranspose_apply e U (e.symm φ)))
    simpa only [LinearEquiv.apply_symm_apply] using he
  have hz : ∀ φ : Module.Dual ℂ M, φ (T f - U f) = 0 := by
    intro φ
    rw [map_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun (hdu φ) f)
  exact sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp hz)

end
end Dubon2026
