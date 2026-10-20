import Dubon2026.PolarizedAdjointRepresentation

/-! The original scalar matrices transform by a minus sign on the
nonidentity component. Together with the native absolute-irreducibility
Schur theorem this removes the full-adjoint H0 term for the actual CM
symmetric power in DUB-17's source Selmer dimension comparison. -/

namespace Dubon2026
open Matrix

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Every original disconnected polarized point negates the scalar matrix line in its full adjoint. -/
theorem polarizedAdjoint_scalar_nonidentity (g : PolarizedGaloisGroup ι R)
    (hg : polarizedComponent g = Multiplicative.ofAdd (1 : ZMod 2)) (d : R) :
    polarizedAdjointRepresentation g (d • (1 : Matrix ι ι R)) = -(d • (1 : Matrix ι ι R)) := by
  rw [polarizedAdjointRepresentation_apply]
  change g.left.1.val * polarizedAdjointRepresentation
    (SemidirectProduct.inr (polarizedComponent g)) (d • (1 : Matrix ι ι R)) * g.left.1.inv = _
  rw [hg]
  change g.left.1.val * polarizedAdjointRepresentation polarizedComplexConjugation
    (d • (1 : Matrix ι ι R)) * g.left.1.inv = _
  rw [polarizedAdjointRepresentation_j]
  simp only [transpose_smul, transpose_one, mul_neg, neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, mul_one, Units.val_inv]

end Dubon2026
