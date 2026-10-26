import Dubon2026.SourceGammaOneDiagonalHom
import Dubon2026.SourceGammaOneHeckeSubgroup
import Dubon2026.SourceHeckeProductConjugation

/-! DUB-17/18 -> all-weight adic association -> Gamma1 geometric realization
-> cover-transfer Hecke compatibility. Prove the actual commutative square
of integral subgroup maps using their existing diagonal matrix equations.
This precedes, and does not assume, cohomology-transfer compatibility. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup

/-- The actual diagonal cover carries the genuine Gamma1 Hecke subgroup
into the original Gamma0 Hecke subgroup. -/
theorem sourceGammaOneDiagonalHom_mem_heckeUpper (Q N n : ℕ) [NeZero N]
    (g : sourceGammaOneHeckeUpper (Q * N ^ 2) n) :
    sourceGammaOneDiagonalHom Q N g.val ∈ heckeUpperSubgroup Q n := by
  rw [sourceHeckeUpper_mem_iff]
  have hg : (n : ℤ) ∣ g.val.val 0 1 :=
    (sourceHeckeUpper_mem_iff (Q * N ^ 2) n _).mp g.property
  change (n : ℤ) ∣ (N : ℤ) * g.val.val 0 1
  exact dvd_mul_of_dvd_right hg _

/-- The actual cover map restricted to the two genuine upper subgroups. -/
def sourceGammaOneCoverHeckeUpperHom (Q N n : ℕ) [NeZero N] :
    sourceGammaOneHeckeUpper (Q * N ^ 2) n →* heckeUpperSubgroup Q n :=
  ((sourceGammaOneDiagonalHom Q N).comp
    (sourceGammaOneHeckeUpper (Q * N ^ 2) n).subtype).codRestrict _
      (sourceGammaOneDiagonalHom_mem_heckeUpper Q N n)

/-- The cover's actual diagonal commutes with the Hecke diagonal. -/
theorem sourceGammaOne_cover_hecke_diagonals_commute (N n : ℕ) [NeZero N] [NeZero n] :
    heckeTriangularMatrix N 1 0 * heckeTriangularMatrix 1 n 0 =
      heckeTriangularMatrix 1 n 0 * heckeTriangularMatrix N 1 0 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeTriangularMatrix_val, Matrix.mul_apply, Fin.sum_univ_two]

/-- Literal integral conjugation commutes with the original Gamma1 cover
map. Both sides are the existing concrete homomorphisms. -/
theorem sourceGammaOneCoverHecke_square (Q N n : ℕ) [NeZero N] [NeZero n]
    (g : sourceGammaOneHeckeUpper (Q * N ^ 2) n) :
    sourceGammaOneDiagonalHom Q N (sourceGammaOneHeckeConjugation (Q * N ^ 2) n g) =
      sourceIntegralHeckeHom (sourceGammaOneCoverHeckeUpperHom Q N n g) := by
  apply Subtype.ext
  apply mapGL_injective (S := ℝ)
  apply mul_right_cancel (b := heckeTriangularMatrix N 1 0 * heckeTriangularMatrix 1 n 0)
  calc
    _ = heckeTriangularMatrix N 1 0 *
        (mapGL ℝ (sourceGammaOneHeckeConjugation (Q * N ^ 2) n g).val *
          heckeTriangularMatrix 1 n 0) := by
      rw [← mul_assoc, sourceGammaOneDiagonalHom_matrix, mul_assoc]
    _ = heckeTriangularMatrix N 1 0 *
        (heckeTriangularMatrix 1 n 0 * mapGL ℝ g.val.val) := by
      rw [← sourceGammaOneHeckeConjugation_matrix]
    _ = heckeTriangularMatrix 1 n 0 *
        (heckeTriangularMatrix N 1 0 * mapGL ℝ g.val.val) := by
      rw [← mul_assoc, sourceGammaOne_cover_hecke_diagonals_commute, mul_assoc]
    _ = heckeTriangularMatrix 1 n 0 *
        (mapGL ℝ (sourceGammaOneDiagonalHom Q N g.val).val *
          heckeTriangularMatrix N 1 0) := by
      rw [← sourceGammaOneDiagonalHom_matrix]
    _ = mapGL ℝ (sourceIntegralHeckeHom (sourceGammaOneCoverHeckeUpperHom Q N n g)).val *
        (heckeTriangularMatrix 1 n 0 * heckeTriangularMatrix N 1 0) := by
      rw [← mul_assoc]
      change (heckeTriangularMatrix 1 n 0 *
        mapGL ℝ (sourceGammaOneCoverHeckeUpperHom Q N n g).val.val) *
          heckeTriangularMatrix N 1 0 = _
      rw [sourceIntegralHeckeConjugate_matrix, mul_assoc]
      rfl
    _ = _ := by rw [sourceGammaOne_cover_hecke_diagonals_commute]

end
end Dubon2026
