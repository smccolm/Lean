import Dubon2026.SourceHeckeSubgroupConjugation

/-! Integral diagonal conjugation at the product level required for Hecke commutativity.
DUB-17/18 -> residual modular Galois association -> original residual H1
eigensystem -> commutativity of actual integral H1 good-prime operators
-> composition through the subgroup at the product of two distinct primes.
The actual prime conjugation is compared with the explicit integral matrix;
the auxiliary product-level construction does not alter that operator.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private theorem upper_entry_dvd {Q n : ℕ} (g : heckeUpperSubgroup Q n) :
    (n : ℤ) ∣ g.val.val 0 1 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp g.property

/-- The literal integral conjugate by diag(1,n), available also at the product of good primes. -/
def sourceIntegralHeckeConjugate {Q n : ℕ} (g : heckeUpperSubgroup Q n) : Gamma0 Q := by
  let A := g.val.val.val
  let B : Matrix (Fin 2) (Fin 2) ℤ :=
    !![A 0 0, A 0 1 / (n : ℤ); A 1 0 * (n : ℤ), A 1 1]
  have hb : (A 0 1 / (n : ℤ)) * (n : ℤ) = A 0 1 :=
    Int.ediv_mul_cancel (upper_entry_dvd g)
  have hdet : B.det = 1 := by
    calc
      B.det = A 0 0 * A 1 1 - (A 0 1 / (n : ℤ) * (n : ℤ)) * A 1 0 := by
        rw [Matrix.det_fin_two]
        change A 0 0 * A 1 1 - (A 0 1 / (n : ℤ)) * (A 1 0 * (n : ℤ)) = _
        ring
      _ = 1 := by rw [hb, ← Matrix.det_fin_two]; exact g.val.val.property
  refine ⟨⟨B, hdet⟩, ?_⟩
  rw [Gamma0_mem]
  change (((A 1 0 * (n : ℤ)) : ℤ) : ZMod Q) = 0
  have hg : ((A 1 0 : ℤ) : ZMod Q) = 0 := Gamma0_mem.mp g.val.property
  rw [Int.cast_mul, hg, zero_mul]

/-- The literal conjugate satisfies the exact original diagonal equation. -/
theorem sourceIntegralHeckeConjugate_matrix {Q n : ℕ} [NeZero n]
    (g : heckeUpperSubgroup Q n) :
    heckeTriangularMatrix 1 n 0 * mapGL ℝ g.val.val =
      mapGL ℝ (sourceIntegralHeckeConjugate g).val * heckeTriangularMatrix 1 n 0 := by
  apply Units.ext
  have hb : (g.val.val 0 1 / (n : ℤ)) * (n : ℤ) = g.val.val 0 1 :=
    Int.ediv_mul_cancel (upper_entry_dvd g)
  have hbr : ((g.val.val 0 1 / (n : ℤ) : ℤ) : ℝ) * (n : ℝ) =
      (g.val.val 0 1 : ℝ) := by exact_mod_cast hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceIntegralHeckeConjugate, heckeTriangularMatrix_val, mapGL_coe_matrix,
      Matrix.mul_apply, Fin.sum_univ_two, hbr, mul_comm]

/-- At an original prime, explicit integral diagonal conjugation is exactly the existing source homomorphism. -/
theorem sourceIntegralHeckeConjugate_eq_prime {Q p : ℕ} [NeZero p] (hp : p.Prime)
    (g : heckeUpperSubgroup Q p) :
    sourceIntegralHeckeConjugate g = sourceHeckeConjugation hp g := by
  apply Subtype.ext
  apply mapGL_injective (S := ℝ)
  apply mul_right_cancel (b := heckeTriangularMatrix 1 p 0)
  exact (sourceIntegralHeckeConjugate_matrix g).symm.trans (sourceHeckeConjugation_matrix hp g)

end
end Dubon2026
