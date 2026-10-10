import Dubon2026.AlgebraIdempotentMatrixAction
import Dubon2026.ResidualMatrixColumnIndependence

/-! # The genuine original column matrix intertwines the whole left-ideal representation -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {G ι O R : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [Algebra O R]

/-- Evaluation of the actual original left-ideal basis on a standard vector intertwines every original algebra-valued group element with its constructed coefficient-basis matrix. -/
theorem matrixIdempotentBasis_intertwines (S : Subalgebra O R)
    (A : Subalgebra S (Matrix ι ι R)) (σ : G →* A) (e : A)
    (b : Basis ι S (algebraIdempotentLeftIdeal (S := S) e)) (i₀ : ι) (g : G) :
    (σ g).val * residualColumnMatrix (fun i => (b i).val.val) i₀ =
      residualColumnMatrix (fun i => (b i).val.val) i₀ *
        (RingHom.mapMatrix S.val.toRingHom) (algebraIdempotentMatrixRepresentation σ e b g).val := by
  let M := algebraIdempotentLeftIdeal (S := S) e
  let F : M →ₗ[S] Matrix ι ι R := A.val.toLinearMap.comp M.subtype
  ext i j
  let x := algebraIdempotentLeftAction e (σ g) (b j)
  have hsum : (∑ k, (b.repr x k : R) • (b k).val.val) = (σ g).val * (b j).val.val := by
    have h := congrArg F (b.sum_repr x)
    simp only [map_sum, map_smul] at h
    exact h
  have hcoord := congrArg (fun X : Matrix ι ι R => X i i₀) hsum
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at hcoord
  change (∑ k, (σ g).val i k * (b j).val.val k i₀) =
    ∑ k, (b k).val.val i i₀ *
      ((algebraIdempotentMatrixRepresentation σ e b g).val k j : R)
  simp only [algebraIdempotentMatrixRepresentation_apply]
  simpa only [mul_comm] using hcoord.symm

end
end Dubon2026
