import Dubon2026.HomogeneousRaisingBasis
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The coefficient norm on the original finite-dimensional homogeneous space -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- The genuine homogeneous space carries the coefficient norm of its proved original raising basis. -/
instance homogeneousNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (homogeneousSubmodule (Fin 2) ℂ n) :=
  NormedAddCommGroup.induced _ _ (homogeneousRaisingBasis n).equivFun.toAddMonoidHom
    (homogeneousRaisingBasis n).equivFun.injective

/-- Use the actual coefficient-norm topology explicitly, including when ambient polynomial topologies are also imported. -/
instance homogeneousTopologicalSpace (n : ℕ) :
    TopologicalSpace (homogeneousSubmodule (Fin 2) ℂ n) :=
  (homogeneousNormedAddCommGroup n).toUniformSpace.toTopologicalSpace

/-- The original complex scalar multiplication is compatible with the actual raising-coordinate norm. -/
instance homogeneousNormedSpace (n : ℕ) : NormedSpace ℂ (homogeneousSubmodule (Fin 2) ℂ n) :=
  NormedSpace.induced ℂ _ _ (homogeneousRaisingBasis n).equivFun

/-- The original vector norm is exactly the genuine norm of its original raising coordinates. -/
theorem homogeneous_norm_eq_coordinates (n : ℕ) (p : homogeneousSubmodule (Fin 2) ℂ n) :
    ‖p‖ = ‖(homogeneousRaisingBasis n).equivFun p‖ := rfl

end
end Dubon2026
