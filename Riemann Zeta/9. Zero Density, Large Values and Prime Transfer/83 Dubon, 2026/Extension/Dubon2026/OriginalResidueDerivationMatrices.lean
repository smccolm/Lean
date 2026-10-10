import Dubon2026.RelativeDualNumberDerivations
import Dubon2026.MatrixAdjointCocycles

/-! # Actual matrix values of original relative residue derivations -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- The genuine original relative residue derivations carry scalar multiplication by the original residue field on their actual epsilon coefficients. -/
instance originalResidueDerivationsModule
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) :
    Module (IsLocalRing.ResidueField O) (OriginalResidueDerivations eR) := by
  let K := IsLocalRing.ResidueField O
  letI := (originalResidueConstantDualLift eR).toRingHom.toAlgebra
  letI : SMulCommClass K R (TrivSqZeroExt.kerIdeal K K) := by
    refine ⟨?_⟩
    intro k r x
    apply Subtype.ext
    simp only [Submodule.coe_smul_of_tower, Algebra.smul_def]
    exact mul_left_comm _ _ _
  exact inferInstanceAs (Module K (Derivation O R (TrivSqZeroExt.kerIdeal K K)))

/-- The actual epsilon entries of an original residue derivation on the same original representation matrices. -/
def originalResidueDerivationMatrix
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) (d : OriginalResidueDerivations eR)
    (g : G) : Matrix ι ι (IsLocalRing.ResidueField O) :=
  fun i j => (d ((ρ g).val i j)).val.snd

/-- Actual epsilon matrix values add under addition of the original relative derivations. -/
theorem originalResidueDerivationMatrix_add
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) (d e : OriginalResidueDerivations eR) (g : G) :
    originalResidueDerivationMatrix eR ρ (d + e) g =
      originalResidueDerivationMatrix eR ρ d g + originalResidueDerivationMatrix eR ρ e g := rfl

/-- Actual epsilon matrix values respect the original residue-field scalar multiplication. -/
theorem originalResidueDerivationMatrix_smul
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R) (a : IsLocalRing.ResidueField O)
    (d : OriginalResidueDerivations eR) (g : G) :
    originalResidueDerivationMatrix eR ρ (a • d) g =
      a • originalResidueDerivationMatrix eR ρ d g := rfl

/-- An original relative residue derivation evaluates the same original representation to a genuine first-order lift of its actual residual representation. -/
def originalResidueDerivationFirstOrderLift
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (d : OriginalResidueDerivations eR) : MatrixFirstOrderLift σ := by
  let f := originalResidueDerivationEquiv eR d
  refine ⟨(GeneralLinearGroup.map (n := ι) f.val.toRingHom).comp ρ, ?_⟩
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact (DFunLike.congr_fun f.property ((ρ g).val i j)).trans
    (congrArg (fun v : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => v.val i j)
      (DFunLike.congr_fun hres g))

/-- The original relative derivation gives its genuine first-order adjoint cocycle by the same right logarithmic matrix formula. -/
theorem originalResidueDerivationFirstOrderLift_cocycle
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ)
    (d : OriginalResidueDerivations eR) (g : G) :
    matrixFirstOrderCocycle σ (originalResidueDerivationFirstOrderLift eR ρ σ hres d) g =
      originalResidueDerivationMatrix eR ρ d g * ((σ g)⁻¹).val := by
  let τ := originalResidueDerivationFirstOrderLift eR ρ σ hres d
  have hr : dualMatrixReduction (τ.val g) = σ g := DFunLike.congr_fun τ.property g
  have hs : dualMatrixSnd (τ.val g).val = originalResidueDerivationMatrix eR ρ d g := by
    apply Matrix.ext
    intro i j
    change ((originalResidueDerivationEquiv eR d).val ((ρ g).val i j)).snd =
      (d ((ρ g).val i j)).val.snd
    rw [originalResidueDerivationEquiv_apply]
    simp [originalResidueConstantDualLift]
  change dualMatrixInfinitesimal (τ.val g) = _
  rw [dualMatrixInfinitesimal, hs, hr]

/-- Actual original relative residue derivations determine genuine adjoint cocycles by an original residue-field-linear map. -/
def originalResidueDerivationCocycleLinearMap
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hres : (GeneralLinearGroup.map (n := ι) (localCoefficientReduction eR).toRingHom).comp ρ = σ) :
    OriginalResidueDerivations eR →ₗ[IsLocalRing.ResidueField O]
      groupCohomology.cocycles₁ (matrixAdjointRep σ) where
  toFun d := matrixFirstOrderCocycle σ (originalResidueDerivationFirstOrderLift eR ρ σ hres d)
  map_add' d e := by
    apply groupCohomology.cocycles₁_ext
    intro g
    change matrixFirstOrderCocycle σ (originalResidueDerivationFirstOrderLift eR ρ σ hres (d + e)) g =
      matrixFirstOrderCocycle σ (originalResidueDerivationFirstOrderLift eR ρ σ hres d) g +
        matrixFirstOrderCocycle σ (originalResidueDerivationFirstOrderLift eR ρ σ hres e) g
    rw [originalResidueDerivationFirstOrderLift_cocycle, originalResidueDerivationFirstOrderLift_cocycle,
      originalResidueDerivationFirstOrderLift_cocycle, originalResidueDerivationMatrix_add, add_mul]
  map_smul' a d := by
    apply groupCohomology.cocycles₁_ext
    intro g
    change matrixFirstOrderCocycle σ (originalResidueDerivationFirstOrderLift eR ρ σ hres (a • d)) g =
      a • matrixFirstOrderCocycle σ (originalResidueDerivationFirstOrderLift eR ρ σ hres d) g
    rw [originalResidueDerivationFirstOrderLift_cocycle, originalResidueDerivationFirstOrderLift_cocycle,
      originalResidueDerivationMatrix_smul]
    exact smul_mul_assoc a _ _

end
end Dubon2026
