import Dubon2026.FirstOrderDeformationEquiv

/-! # Genuine first-order triviality and original adjoint cocycle vanishing -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- At an original group element where the residual matrix is the identity, the actual first-order lift is the identity exactly when its original adjoint cocycle vanishes. -/
theorem matrixFirstOrderLift_eq_one_iff
    (ρ : G →* GeneralLinearGroup ι R) (τ : MatrixFirstOrderLift ρ)
    (g : G) (hg : ρ g = 1) :
    τ.val g = 1 ↔ matrixFirstOrderCocycle ρ τ g = 0 := by
  constructor
  · intro h
    simp [matrixFirstOrderCocycle_apply, h, dualMatrixInfinitesimal, dualMatrixSnd]
    ext i j
    change TrivSqZeroExt.snd ((1 : Matrix ι ι (DualNumber R)) i j) = (0 : R)
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · intro hc
    have ht := congrArg (fun υ : MatrixFirstOrderLift ρ => υ.val g)
      (firstOrderLiftFromCocycle_cocycle ρ τ)
    change (firstOrderLiftFromCocycle ρ (matrixFirstOrderCocycle ρ τ)).val g = τ.val g at ht
    rw [← ht]
    apply Units.ext
    apply Matrix.dualNumberEquiv.injective
    change Matrix.dualNumberEquiv (Matrix.dualNumberEquiv.symm
      ⟨(ρ g).val, matrixFirstOrderCocycle ρ τ g * (ρ g).val⟩) =
        Matrix.dualNumberEquiv 1
    rw [AlgEquiv.apply_symm_apply, map_one]
    apply TrivSqZeroExt.ext <;> simp [hg, hc]

/-- Killing every element of an original residually trivial subgroup is equivalent to vanishing of the original first-order cocycle on that same entire subgroup. -/
theorem matrixFirstOrderLift_subgroup_kernel_iff
    (ρ : G →* GeneralLinearGroup ι R) (τ : MatrixFirstOrderLift ρ)
    (N : Subgroup G) (hN : N ≤ ρ.ker) :
    N ≤ τ.val.ker ↔ ∀ g ∈ N, matrixFirstOrderCocycle ρ τ g = 0 := by
  constructor
  · intro h g hg
    exact (matrixFirstOrderLift_eq_one_iff ρ τ g (hN hg)).mp (h hg)
  · intro h g hg
    exact (matrixFirstOrderLift_eq_one_iff ρ τ g (hN hg)).mpr (h g hg)

end
end Dubon2026
