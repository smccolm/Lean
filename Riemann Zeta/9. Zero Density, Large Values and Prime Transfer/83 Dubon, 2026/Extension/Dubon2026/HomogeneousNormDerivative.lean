import Dubon2026.HomogeneousNormedSpace
import Dubon2026.FiniteSeparatingDerivative
import Dubon2026.MatrixPolynomialOrbitDerivative
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Actual norm derivatives of the original finite-dimensional matrix representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- Every original matrix direction has a genuine norm derivative equal to its exact original homogeneous infinitesimal. -/
theorem homogeneousMatrixOrbit_hasDerivAt (n : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (p : homogeneousSubmodule (Fin 2) ℂ n) :
    HasDerivAt (fun t : ℂ => homogeneousMatrixAction n (1 + t • a) p)
      (homogeneousMatrixLieAction n a p) 0 := by
  let L : (Fin 2 → ℂ) → homogeneousSubmodule (Fin 2) ℂ n →ₗ[ℂ] ℂ :=
    fun x => (MvPolynomial.aeval x).toLinearMap.comp (homogeneousSubmodule (Fin 2) ℂ n).subtype
  apply finiteSeparatingFamily_hasDerivAt L
  · intro v hv
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    exact (hv x).trans (map_zero (MvPolynomial.eval x)).symm
  · intro x
    simpa only [L, LinearMap.comp_apply, Submodule.subtype_apply,
      homogeneousMatrixAction_apply, homogeneousMatrixLieAction_apply,
      AlgHom.toLinearMap_apply, MvPolynomial.coe_aeval_eq_eval] using
      matrixPolynomialOrbit_hasDerivAt a p.val x

end
end Dubon2026
