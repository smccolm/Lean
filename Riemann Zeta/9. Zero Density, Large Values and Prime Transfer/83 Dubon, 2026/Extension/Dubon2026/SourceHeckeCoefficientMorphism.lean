import Dubon2026.SourceHeckeSubgroupConjugation
import Dubon2026.SourcePeriodCocycle
import Dubon2026.SourceIntegralHeckeAction
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Original coefficient transport in the Hecke correspondence.
DUB-17/18 -> residual modular Galois association -> original H1 Hecke
eigensystem. The actual integral diagonal and existing row substitution
give the coefficient morphism between the two genuine subgroup actions.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup SourceModularSymbols
open MvPolynomial MulOpposite CategoryTheory
open scoped MatrixGroups

variable {p Q : ℕ} [NeZero p]

/-- The original Hecke conjugation satisfies its rational and integral equations. -/
theorem sourceHeckeConjugation_integral (hp : Nat.Prime p)
    (γ : heckeUpperSubgroup Q p) :
    heckeTriangularRat 1 p 0 * mapGL ℚ γ.val.val =
        mapGL ℚ (sourceHeckeConjugation hp γ).val * heckeTriangularRat 1 p 0 ∧
      integralTriangularMatrix 1 p 0 * (γ.val.val : Matrix (Fin 2) (Fin 2) ℤ) =
        ((sourceHeckeConjugation hp γ).val : Matrix (Fin 2) (Fin 2) ℤ) *
          integralTriangularMatrix 1 p 0 :=
  integralTriangular_factor 0 0 _ _ (sourceHeckeConjugation_matrix hp γ)

/-- The actual adjugate diagonal reverses the original conjugation equation. -/
theorem sourceHeckeConjugation_adjugate (hp : Nat.Prime p)
    (γ : heckeUpperSubgroup Q p) :
    (integralTriangularMatrix 1 p 0).adjugate *
        ((sourceHeckeConjugation hp γ).val : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ.val.val : Matrix (Fin 2) (Fin 2) ℤ) *
        (integralTriangularMatrix 1 p 0).adjugate := by
  have h := congrArg Matrix.adjugate (sourceHeckeConjugation_integral hp γ⁻¹).2
  simp only [map_inv] at h
  change (integralTriangularMatrix 1 p 0 *
      ((γ.val.val⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).adjugate =
    (((((sourceHeckeConjugation hp γ).val)⁻¹ : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) * integralTriangularMatrix 1 p 0).adjugate at h
  have hi (g : SL(2, ℤ)) :
      ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).adjugate =
        (g : Matrix (Fin 2) (Fin 2) ℤ) := by
    have e := Matrix.SpecialLinearGroup.coe_inv (g⁻¹)
    rw [inv_inv] at e
    exact e.symm
  rw [adjugate_mul_distrib, adjugate_mul_distrib, hi, hi] at h
  exact h.symm

/-- The genuine adjugate diagonal acts on the original dual period coefficients. -/
def sourceHeckeDualDiagonal (w p : ℕ) :
    Module.End ℂ (Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ w)) :=
  Module.Dual.transpose
    (sourceModularBinaryFormAdjugateRep ℂ w (integralTriangularMatrix 1 p 0))

/-- The actual adjugate dual action intertwines the two original subgroup actions. -/
theorem sourceHeckeDualDiagonal_intertwine (hp : Nat.Prime p) (w : ℕ)
    (γ : heckeUpperSubgroup Q p) :
    (sourceHeckeDualDiagonal w p).comp
        ((sourcePeriodDualRep (Gamma0 Q) w).ρ (sourceHeckeConjugation hp γ)) =
      ((sourcePeriodDualRep (Gamma0 Q) w).ρ γ.val).comp
        (sourceHeckeDualDiagonal w p) := by
  apply LinearMap.ext
  intro L
  apply LinearMap.ext
  intro P
  change ((sourcePeriodDualRep (Gamma0 Q) w).ρ (sourceHeckeConjugation hp γ) L)
      (sourceModularBinaryFormAdjugateRep ℂ w (integralTriangularMatrix 1 p 0) P) =
    ((sourcePeriodDualRep (Gamma0 Q) w).ρ γ.val (sourceHeckeDualDiagonal w p L)) P
  rw [sourcePeriodDualRep_apply, sourcePeriodDualRep_apply]
  change L (sourceModularBinaryFormRep ℂ w (op _) (sourceModularBinaryFormRep ℂ w (op _) P)) =
    L (sourceModularBinaryFormRep ℂ w (op _) (sourceModularBinaryFormRep ℂ w (op _) P))
  rw [← sourceModularBinaryFormRep_mul, ← sourceModularBinaryFormRep_mul,
    sourceHeckeConjugation_adjugate]

/-- The original Hecke coefficient morphism, with equivariance proved for the actual level. -/
def sourceHeckeDualMorphism (hp : Nat.Prime p) (w : ℕ) :
    Rep.res (sourceHeckeConjugation (Q := Q) hp) (sourcePeriodDualRep (Gamma0 Q) w) ⟶
      Rep.res (heckeUpperSubgroup Q p).subtype (sourcePeriodDualRep (Gamma0 Q) w) :=
  Rep.ofHom {
    toLinearMap := sourceHeckeDualDiagonal w p
    isIntertwining' := sourceHeckeDualDiagonal_intertwine hp w }

end
end Dubon2026
