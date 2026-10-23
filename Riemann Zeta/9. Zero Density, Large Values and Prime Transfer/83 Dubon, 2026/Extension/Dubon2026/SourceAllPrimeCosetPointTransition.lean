import Dubon2026.SourceOriginalHeckeAllPrimePrimitiveTrace
import Dubon2026.SourceHeckePeriodCosets

/-! DUB-17/18 -> rational rank-two Hecke descent -> the all-prime
character trace. This is the exact transition identity of the actual
analytic inverse-dilation coset points. Reuse the original integral
conjugation matrix equation, valid also at primes dividing the level.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable (N p : ℕ) [NeZero p]

theorem originalHeckeCosetPoint_transition (hp : Nat.Prime p)
    (γ : Gamma0 N) (q : Gamma0 N ⧸ heckeUpperSubgroup N p) (τ : ℍ) :
    originalHeckeCosetPoint N p (γ.val • τ) (γ • q) =
      (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup N p) γ q)).val •
        originalHeckeCosetPoint N p τ q := by
  have ht : (γ • q).out⁻¹ * γ =
      (cosetTransition (heckeUpperSubgroup N p) γ q).val * q.out⁻¹ := by
    change _ = ((γ • q).out⁻¹ * (γ * q.out)) * q.out⁻¹
    group
  have hm := congrArg (fun g : Gamma0 N => mapGL ℝ g.val) ht
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul] at hm
  have he : (heckeTriangularMatrix 1 p 0 * mapGL ℝ (γ • q).out.val⁻¹) * mapGL ℝ γ.val =
      mapGL ℝ (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup N p) γ q)).val *
        (heckeTriangularMatrix 1 p 0 * mapGL ℝ q.out.val⁻¹) := by
    rw [mul_assoc, hm, ← mul_assoc, sourceHeckeConjugation_matrix hp, mul_assoc]
  rw [originalHeckeCosetPoint_eq_triangular, originalHeckeCosetPoint_eq_triangular]
  change (heckeTriangularMatrix 1 p 0 * mapGL ℝ (γ • q).out.val⁻¹) • (mapGL ℝ γ.val • τ) =
    mapGL ℝ (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup N p) γ q)).val •
      ((heckeTriangularMatrix 1 p 0 * mapGL ℝ q.out.val⁻¹) • τ)
  rw [← mul_smul, he, mul_smul]

end
end Dubon2026.SourceFunctionField
