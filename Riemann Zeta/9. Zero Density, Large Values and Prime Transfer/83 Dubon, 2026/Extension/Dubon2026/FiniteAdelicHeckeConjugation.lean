import Dubon2026.FiniteAdelicHeckeUpperCosets
import Dubon2026.RealGL2Sign

/-! # The original finite-adelic Hecke upper subgroup stabilizes the genuine diagonal translate -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The literal finite-adelic image of the original rational upper Hecke diagonal. -/
def finiteAdelicHeckeDiagonal (p : ℕ) [NeZero p] : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) :=
  rationalGL2ToFinite (heckeTriangularRat 1 p 0)

/-- The genuine Hecke diagonal has exactly its original entries in the finite adele ring. -/
theorem finiteAdelicHeckeDiagonal_val (p : ℕ) [NeZero p] :
    (finiteAdelicHeckeDiagonal p).val = !![1, 0; 0, (p : FiniteAdeleRing ℤ ℚ)] := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteAdelicHeckeDiagonal, rationalGL2ToFinite, heckeTriangularRat,
      GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero]

/-- The original rational inverse of p cancels its genuine finite-adelic integer image. -/
theorem finiteAdele_nat_rational_inverse (p : ℕ) [NeZero p] :
    (p : FiniteAdeleRing ℤ ℚ) * algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((p : ℚ)⁻¹) = 1 := by
  rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) p, ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne p)), map_one]

/-- The genuine inverse Hecke diagonal has its literal rational inverse entry. -/
theorem finiteAdelicHeckeDiagonal_inv_val (p : ℕ) [NeZero p] :
    ((finiteAdelicHeckeDiagonal p)⁻¹).val =
      !![1, 0; 0, algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((p : ℚ)⁻¹)] := by
  let B : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) :=
    !![1, 0; 0, algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((p : ℚ)⁻¹)]
  have hb : B * (finiteAdelicHeckeDiagonal p).val = 1 := by
    rw [finiteAdelicHeckeDiagonal_val]
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, finiteAdele_nat_rational_inverse]
  calc
    _ = (B * (finiteAdelicHeckeDiagonal p).val) * ((finiteAdelicHeckeDiagonal p)⁻¹).val := by
      rw [hb, one_mul]
    _ = B := by
      have he : (finiteAdelicHeckeDiagonal p).val * ((finiteAdelicHeckeDiagonal p)⁻¹).val = 1 :=
        congrArg Units.val (mul_inv_cancel (finiteAdelicHeckeDiagonal p))
      rw [mul_assoc, he, mul_one]

/-- Actual conjugation by the original Hecke diagonal divides the upper entry and multiplies the lower entry by exactly p. -/
theorem finiteAdelicHeckeDiagonal_conjugate_val (p : ℕ) [NeZero p]
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    (finiteAdelicHeckeDiagonal p * g * (finiteAdelicHeckeDiagonal p)⁻¹).val =
      !![g.val 0 0, algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((p : ℚ)⁻¹) * g.val 0 1;
        (p : FiniteAdeleRing ℤ ℚ) * g.val 1 0, g.val 1 1] := by
  rw [Units.val_mul, Units.val_mul, finiteAdelicHeckeDiagonal_val, finiteAdelicHeckeDiagonal_inv_val]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm, mul_assoc]
  rw [mul_left_comm, finiteAdele_nat_rational_inverse, mul_one]

/-- Membership in the genuine upper Hecke subgroup is precisely original finite-adelic divisibility of its upper entry. -/
theorem finiteAdelicHeckeUpper_mem_iff (N p : ℕ) [NeZero p] [Fact p.Prime]
    (g : finiteAdeleGL2Gamma0 N) : g ∈ finiteAdelicHeckeUpper N p ↔
      finiteAdeleLevelMultiple p (g.val.val 0 1) :=
  finiteAdeleResidue_eq_zero_iff p ⟨g.val.val 0 1, g.property.1.1 0 1⟩

private theorem heckeConjugate_level_matrix (N p : ℕ) [NeZero p]
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (hg : finiteAdeleLevelMatrix N g.val) (hu : finiteAdeleLevelMultiple p (g.val 0 1)) :
    finiteAdeleLevelMatrix N (finiteAdelicHeckeDiagonal p * g * (finiteAdelicHeckeDiagonal p)⁻¹).val := by
  rw [finiteAdelicHeckeDiagonal_conjugate_val]
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hg.1 0 0
    · exact (finiteAdeleLevelMultiple_iff p _).mp hu
    · exact finiteAdeleIntegerSubring.mul_mem (by simp) (hg.1 1 0)
    · exact hg.1 1 1
  · exact finiteAdeleLevelMultiple_mul_left N (by simp) hg.2

/-- Every original finite-adelic upper Hecke element conjugates back into the genuine original level group. -/
theorem finiteAdelicHeckeUpper_conjugate_mem (N p : ℕ) [NeZero p] [Fact p.Prime]
    (g : finiteAdeleGL2Gamma0 N) (hg : g ∈ finiteAdelicHeckeUpper N p) :
    finiteAdelicHeckeDiagonal p * g.val * (finiteAdelicHeckeDiagonal p)⁻¹ ∈ finiteAdeleGL2Gamma0 N := by
  constructor
  · exact heckeConjugate_level_matrix N p g.val g.property.1
      ((finiteAdelicHeckeUpper_mem_iff N p g).mp hg)
  · have hi := heckeConjugate_level_matrix N p g.val⁻¹ g.property.2
      ((finiteAdelicHeckeUpper_mem_iff N p g⁻¹).mp ((finiteAdelicHeckeUpper N p).inv_mem hg))
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc] using hi

end
end Dubon2026
