import Dubon2026.CMHermitianPositiveMatrix

/-! # Original Hermitian unit from the source positivity hypothesis

The already proved matrix Hermitian property applies to the specified
invertible form. This removes a redundant self-adjointness input when
assembling DUB-17's actual unitary auxiliary module.
-/

namespace Dubon2026
noncomputable section
open NumberField
open scoped ComplexOrder

/-- The specified original positive invertible CM matrix is self-adjoint as an original matrix unit. -/
theorem cmHermitianPositiveUnit_star
    (K : Type*) [Field K] [NumberField K] [IsCMField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : (Matrix ι ι K)ˣ)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H.val).PosDef) : star H = H :=
  Units.ext (cmHermitianPositiveMatrix_isHermitian K H.val hH)

end
end Dubon2026
