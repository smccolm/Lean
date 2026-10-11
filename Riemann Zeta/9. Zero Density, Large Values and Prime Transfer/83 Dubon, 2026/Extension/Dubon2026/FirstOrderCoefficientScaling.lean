import Dubon2026.DualNumberCoefficientOperations
import Dubon2026.ContinuousFirstOrderDeformation

/-! # Genuine epsilon scaling and constant first-order lifts -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing k]

/-- Change original first-order coefficients by the actual epsilon-scaling map. -/
def matrixFirstOrderScale (ρ : G →* GeneralLinearGroup ι k)
    (c : k) (τ : MatrixFirstOrderLift ρ) : MatrixFirstOrderLift ρ := by
  refine ⟨(GeneralLinearGroup.map (dualNumberEpsilonScale k c)).comp τ.val, ?_⟩
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  change (dualNumberEpsilonScale k c ((τ.val g).val i j)).fst = (ρ g).val i j
  rw [(dualNumberEpsilonScale_components k c ((τ.val g).val i j)).1]
  exact congrArg (fun U : GeneralLinearGroup ι k => U.val i j)
    (DFunLike.congr_fun τ.property g)

/-- The genuine coefficient scaling gives precisely scalar multiplication of the
same original adjoint cocycle, including its right-logarithmic matrix convention. -/
theorem matrixFirstOrderScale_cocycle (ρ : G →* GeneralLinearGroup ι k)
    (c : k) (τ : MatrixFirstOrderLift ρ) :
    matrixFirstOrderCocycle ρ (matrixFirstOrderScale ρ c τ) =
      c • matrixFirstOrderCocycle ρ τ := by
  apply groupCohomology.cocycles₁_ext
  intro g
  have hτ : dualMatrixReduction (τ.val g) = ρ g := DFunLike.congr_fun τ.property g
  have hscale : dualMatrixReduction ((matrixFirstOrderScale ρ c τ).val g) = ρ g :=
    DFunLike.congr_fun (matrixFirstOrderScale ρ c τ).property g
  have hs : dualMatrixSnd ((matrixFirstOrderScale ρ c τ).val g).val =
      c • dualMatrixSnd (τ.val g).val := by
    ext i j
    exact (dualNumberEpsilonScale_components k c ((τ.val g).val i j)).2
  change dualMatrixInfinitesimal ((matrixFirstOrderScale ρ c τ).val g) =
    c • dualMatrixInfinitesimal (τ.val g)
  simp only [dualMatrixInfinitesimal, hscale, hτ, hs, smul_mul_assoc]

/-- The lift of the zero original cocycle is the whole original representation
changed through the constant coefficient inclusion. -/
theorem firstOrderLiftFromZero_constant (ρ : G →* GeneralLinearGroup ι k) :
    (firstOrderLiftFromCocycle ρ 0).val =
      (GeneralLinearGroup.map (algebraMap k (DualNumber k))).comp ρ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.dualNumberEquiv.injective
  change Matrix.dualNumberEquiv
      (Matrix.dualNumberEquiv.symm ⟨(ρ g).val, (0 : Matrix ι ι k) * (ρ g).val⟩) = _
  rw [AlgEquiv.apply_symm_apply]
  apply TrivSqZeroExt.ext
  · rfl
  · change (0 : Matrix ι ι k) * (ρ g).val = 0
    exact zero_mul _

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace k] [IsTopologicalRing k]

/-- Actual first-order epsilon scaling preserves continuity of the whole lift by
its original continuous cocycle and the existing reconstruction theorem. -/
theorem matrixFirstOrderScale_continuous (ρ : G →* GeneralLinearGroup ι k)
    (hρ : Continuous ρ) (c : k) (τ : MatrixFirstOrderLift ρ)
    (hτ : Continuous τ.val) : Continuous (matrixFirstOrderScale ρ c τ).val := by
  apply (matrixFirstOrderLift_continuous_iff ρ hρ _).mpr
  rw [matrixFirstOrderScale_cocycle]
  exact (matrixFirstOrderCocycle_continuous ρ hρ τ hτ).const_smul c

end
end Dubon2026
