import Dubon2026.SourceIntegralHeckeConjugation
import Dubon2026.SourceBinaryHeckeMorphism

/-! The product-level diagonal correspondence on the original integral group.
DUB-17/18 -> residual modular Galois association -> original residual H1
eigensystem -> full integral H1 Hecke commutativity -> comparison with the
actual correspondence at the product of the two primes.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup CategoryTheory

variable {Q n : ℕ} [NeZero n]

/-- The literal integral diagonal conjugation is a group homomorphism at product level. -/
def sourceIntegralHeckeHom : heckeUpperSubgroup Q n →* Gamma0 Q where
  toFun := sourceIntegralHeckeConjugate
  map_one' := by
    apply Subtype.ext
    apply mapGL_injective (S := ℝ)
    apply mul_right_cancel (b := heckeTriangularMatrix 1 n 0)
    rw [← sourceIntegralHeckeConjugate_matrix]
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply mapGL_injective (S := ℝ)
    apply mul_right_cancel (b := heckeTriangularMatrix 1 n 0)
    rw [← sourceIntegralHeckeConjugate_matrix]
    simp only [Subgroup.coe_mul, map_mul]
    change heckeTriangularMatrix 1 n 0 * (mapGL ℝ g.val.val * mapGL ℝ h.val.val) =
      (mapGL ℝ (sourceIntegralHeckeConjugate g).val *
        mapGL ℝ (sourceIntegralHeckeConjugate h).val) * heckeTriangularMatrix 1 n 0
    rw [← mul_assoc, sourceIntegralHeckeConjugate_matrix, mul_assoc,
      sourceIntegralHeckeConjugate_matrix, mul_assoc]

/-- The product-level homomorphism specializes to the original prime correspondence. -/
theorem sourceIntegralHeckeHom_eq_prime (hn : n.Prime) :
    sourceIntegralHeckeHom (Q := Q) = sourceHeckeConjugation hn := by
  apply MonoidHom.ext
  intro g
  exact sourceIntegralHeckeConjugate_eq_prime hn g

/-- The actual diagonal coefficient action intertwines the product-level conjugation. -/
theorem sourceIntegralHeckeDiagonal_intertwine (R : Type) [CommRing R] (w : ℕ)
    (g : heckeUpperSubgroup Q n) :
    (homogeneousMatrixAction w (Matrix.diagonal ![(n : R), 1])).comp
        ((sourceBinaryCoefficientRep R Q w).ρ (sourceIntegralHeckeHom g)) =
      ((sourceBinaryCoefficientRep R Q w).ρ g.val).comp
        (homogeneousMatrixAction w (Matrix.diagonal ![(n : R), 1])) := by
  have hb : (g.val.val 0 1 / (n : ℤ)) * (n : ℤ) = g.val.val 0 1 :=
    Int.ediv_mul_cancel ((ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp g.property)
  have hm : Matrix.diagonal ![(n : ℤ), 1] *
      ((sourceIntegralHeckeConjugate g).val : Matrix (Fin 2) (Fin 2) ℤ) =
      (g.val.val : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal ![(n : ℤ), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceIntegralHeckeConjugate, Matrix.mul_apply, Fin.sum_univ_two]
    · exact mul_comm _ _
    · exact (mul_comm _ _).trans hb
  have hr := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ =>
    M.map (Int.castRingHom R)) hm
  have hd : (Matrix.diagonal ![(n : ℤ), 1]).map (Int.castRingHom R) =
      Matrix.diagonal ![(n : R), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  simp only [Matrix.map_mul, hd] at hr
  have h := congrArg (homogeneousMatrixRepresentation (R := R) w) hr
  simpa only [map_mul] using h

/-- The product-level coefficient morphism uses the same actual binary polynomial action. -/
def sourceIntegralHeckeMorphism (R : Type) [CommRing R] (w : ℕ) :
    Rep.res (sourceIntegralHeckeHom (Q := Q) (n := n)) (sourceBinaryCoefficientRep R Q w) ⟶
      Rep.res (heckeUpperSubgroup Q n).subtype (sourceBinaryCoefficientRep R Q w) :=
  Rep.ofHom {
    toLinearMap := homogeneousMatrixAction w (Matrix.diagonal ![(n : R), 1])
    isIntertwining' := sourceIntegralHeckeDiagonal_intertwine R w }

end
end Dubon2026
