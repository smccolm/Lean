import Dubon2026.SourcePeriodBinaryHecke
import Dubon2026.SourceOriginalBinaryCohomology
import Dubon2026.SourcePrimitiveHeckeCohomology

/-! The actual Hecke correspondence in column-binary H1.
DUB-17/18 -> residual modular Galois association -> the original binary H1
eigensystem. The proved coefficient isomorphism transports the full native
correspondence; its literal cocycle formula uses the original Gamma0 cosets
and column substitution by diag(p,1).
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup CategoryTheory
open scoped MatrixGroups

/-- Native coefficient naturality on every original dual-period cocycle. -/
theorem sourcePeriodH1BinaryEquiv_cocycle (Γ : Subgroup SL(2, ℤ)) (w : ℕ)
    (c : groupCohomology.cocycles₁ (sourcePeriodDualRep Γ w)) :
    sourcePeriodH1BinaryEquiv Γ w (groupCohomology.H1π _ c) =
      groupCohomology.H1π (sourcePeriodColumnRep Γ w)
        (groupCohomology.mapCocycles₁ (MonoidHom.id Γ) (sourcePeriodCoefficientIso Γ w).hom c) := by
  change (groupCohomology.map (A := sourcePeriodDualRep Γ w)
    (B := sourcePeriodColumnRep Γ w) (MonoidHom.id Γ) (sourcePeriodCoefficientIso Γ w).hom 1)
      (groupCohomology.H1π _ c) = _
  exact groupCohomology.H1π_comp_map_apply
    (A := sourcePeriodDualRep Γ w) (B := sourcePeriodColumnRep Γ w) (MonoidHom.id Γ)
    (sourcePeriodCoefficientIso Γ w).hom c

/-- Native coefficient naturality on every original column-binary cocycle in the inverse direction. -/
theorem sourcePeriodH1BinaryEquiv_symm_cocycle (Γ : Subgroup SL(2, ℤ)) (w : ℕ)
    (c : groupCohomology.cocycles₁ (sourcePeriodColumnRep Γ w)) :
    (sourcePeriodH1BinaryEquiv Γ w).symm (groupCohomology.H1π _ c) =
      groupCohomology.H1π (sourcePeriodDualRep Γ w)
        (groupCohomology.mapCocycles₁ (MonoidHom.id Γ) (sourcePeriodCoefficientIso Γ w).inv c) := by
  change (groupCohomology.map (A := sourcePeriodColumnRep Γ w)
    (B := sourcePeriodDualRep Γ w) (MonoidHom.id Γ) (sourcePeriodCoefficientIso Γ w).inv 1)
      (groupCohomology.H1π _ c) = _
  exact groupCohomology.H1π_comp_map_apply
    (A := sourcePeriodColumnRep Γ w) (B := sourcePeriodDualRep Γ w) (MonoidHom.id Γ)
    (sourcePeriodCoefficientIso Γ w).inv c

variable {p Q : ℕ} [NeZero p]

private def coefficientCocycleMap {G : Type} [Group G] {A B : Rep ℂ G} (φ : A ⟶ B) :
    groupCohomology.cocycles₁ A →ₗ[ℂ] groupCohomology.cocycles₁ B :=
  (groupCohomology.mapCocycles₁ (MonoidHom.id G) φ).hom

private theorem coefficientCocycleMap_apply {G : Type} [Group G] {A B : Rep ℂ G}
    (φ : A ⟶ B) (c : groupCohomology.cocycles₁ A) (g : G) :
    coefficientCocycleMap φ c g = φ.hom (c g) := rfl

private theorem coefficientIso_diagonal (Γ : Subgroup SL(2, ℤ)) (w p : ℕ)
    (x : sourcePeriodDualRep Γ w) :
    (sourcePeriodCoefficientIso Γ w).hom.hom (sourceHeckeDualDiagonal w p x) =
      homogeneousMatrixAction w (Matrix.diagonal ![(p : ℂ), 1])
        ((sourcePeriodCoefficientIso Γ w).hom.hom x) := by
  change (sourcePeriodBinaryEquiv w _).toLinearMap (sourceHeckeDualDiagonal w p x) =
    homogeneousMatrixAction w (Matrix.diagonal ![(p : ℂ), 1])
      ((sourcePeriodBinaryEquiv w _).toLinearMap x)
  have h := LinearMap.congr_fun
    (sourcePeriodBinaryEquiv_heckeDiagonal w p
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero w))) x
  simpa only [LinearMap.comp_apply] using h

private local instance sourceHeckeBinaryCohomologyFintype :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q p) :=
  sourceHeckeUpperFintype Q p

/-- The actual full Hecke cocycle operator in the original column-binary coefficients. -/
def sourceHeckeBinaryCocycle (hp : Nat.Prime p) (w : ℕ) :
    Module.End ℂ (groupCohomology.cocycles₁ (sourcePeriodColumnRep (Gamma0 Q) w)) :=
  coefficientCocycleMap (sourcePeriodCoefficientIso (Gamma0 Q) w).hom ∘ₗ
    sourceHeckeCocycle hp w ∘ₗ
      coefficientCocycleMap (sourcePeriodCoefficientIso (Gamma0 Q) w).inv

/-- The full native column-binary H1 Hecke operator obtained by the proved coefficient isomorphism. -/
def sourceHeckeBinaryH1 (hp : Nat.Prime p) (w : ℕ) :
    Module.End ℂ (groupCohomology.H1 (sourcePeriodColumnRep (Gamma0 Q) w)) :=
  (sourcePeriodH1BinaryEquiv (Gamma0 Q) w).toLinearMap ∘ₗ sourceHeckeH1 hp w ∘ₗ
    (sourcePeriodH1BinaryEquiv (Gamma0 Q) w).symm.toLinearMap

/-- On every column cocycle, the full H1 operator has the transported actual cocycle representative. -/
theorem sourceHeckeBinaryH1_cocycle (hp : Nat.Prime p) (w : ℕ)
    (c : groupCohomology.cocycles₁ (sourcePeriodColumnRep (Gamma0 Q) w)) :
    sourceHeckeBinaryH1 hp w (groupCohomology.H1π _ c) =
      groupCohomology.H1π _ (sourceHeckeBinaryCocycle hp w c) := by
  change sourcePeriodH1BinaryEquiv (Gamma0 Q) w
    (sourceHeckeH1 hp w ((sourcePeriodH1BinaryEquiv (Gamma0 Q) w).symm
      (groupCohomology.H1π _ c))) = _
  rw [sourcePeriodH1BinaryEquiv_symm_cocycle, sourceHeckeH1_cocycle,
    sourcePeriodH1BinaryEquiv_cocycle]
  dsimp only [sourceHeckeBinaryCocycle, LinearMap.comp_apply, coefficientCocycleMap]

/-- The original column-binary Hecke operator uses the literal full coset formula and adjugate diagonal. -/
theorem sourceHeckeBinaryCocycle_apply (hp : Nat.Prime p) (w : ℕ)
    (c : groupCohomology.cocycles₁ (sourcePeriodColumnRep (Gamma0 Q) w)) (γ : Gamma0 Q) :
    sourceHeckeBinaryCocycle hp w c γ =
      ∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q p,
        (sourcePeriodColumnRep (Gamma0 Q) w).ρ (γ • q).out
          (homogeneousMatrixAction w (Matrix.diagonal ![(p : ℂ), 1])
             (c (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) γ q)))) := by
  change coefficientCocycleMap (sourcePeriodCoefficientIso (Gamma0 Q) w).hom
    (sourceHeckeCocycle hp w
      (coefficientCocycleMap (sourcePeriodCoefficientIso (Gamma0 Q) w).inv c)) γ = _
  rw [coefficientCocycleMap_apply, sourceHeckeCocycle_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Representation.IntertwiningMap.isIntertwining, coefficientIso_diagonal,
    coefficientCocycleMap_apply, Rep.hom_inv_apply]

end
end Dubon2026
