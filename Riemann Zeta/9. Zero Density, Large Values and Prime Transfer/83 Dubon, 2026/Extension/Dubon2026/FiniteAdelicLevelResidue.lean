import Dubon2026.FiniteAdeleResidueRing
import Dubon2026.FiniteAdelicGL2Level

/-! # Actual finite-level invertible matrices and their genuine finite residue matrices -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- A genuine adelic level matrix and its actual inverse form an invertible matrix over the original integral finite-adele subring. -/
def finiteAdelicLevelIntegralMatrix (N : ℕ) (g : finiteAdeleGL2Gamma0 N) :
    GeneralLinearGroup (Fin 2) finiteAdeleIntegerSubring where
  val i j := ⟨g.val.val i j, g.property.1.1 i j⟩
  inv i j := ⟨(g.val⁻¹).val i j, g.property.2.1 i j⟩
  val_inv := by
    funext i j
    apply Subtype.ext
    by_cases h : i = j <;> simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, h] using
      congrArg (fun m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) => m i j) g.val.val_inv
  inv_val := by
    funext i j
    apply Subtype.ext
    by_cases h : i = j <;> simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, h] using
      congrArg (fun m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) => m i j) g.val.inv_val

/-- Extending the actual integral matrix back to finite adeles recovers the original level matrix literally. -/
theorem finiteAdelicLevelIntegralMatrix_map (N : ℕ) (g : finiteAdeleGL2Gamma0 N) :
    GeneralLinearGroup.map finiteAdeleIntegerSubring.subtype (finiteAdelicLevelIntegralMatrix N g) = g.val := by
  apply Units.ext
  rfl

private theorem integralGL2_map_injective :
    Function.Injective (GeneralLinearGroup.map (n := Fin 2) finiteAdeleIntegerSubring.subtype) := by
  intro a b h
  apply Units.ext
  funext i j
  apply Subtype.ext
  exact congrArg (fun g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) => g.val i j) h

/-- The actual integral matrix lift preserves the original level-group multiplication. -/
def finiteAdelicLevelIntegralHom (N : ℕ) :
    finiteAdeleGL2Gamma0 N →* GeneralLinearGroup (Fin 2) finiteAdeleIntegerSubring where
  toFun := finiteAdelicLevelIntegralMatrix N
  map_one' := by
    apply integralGL2_map_injective
    rw [finiteAdelicLevelIntegralMatrix_map, map_one]
    rfl
  map_mul' a b := by
    apply integralGL2_map_injective
    rw [finiteAdelicLevelIntegralMatrix_map, map_mul,
      finiteAdelicLevelIntegralMatrix_map, finiteAdelicLevelIntegralMatrix_map]
    rfl

/-- The residue matrix of the original adelic level element is genuinely invertible over the ordinary finite residue ring. -/
def finiteAdelicLevelResidue (N m : ℕ) [NeZero m] (g : finiteAdeleGL2Gamma0 N) :
    GeneralLinearGroup (Fin 2) (ZMod m) :=
  GeneralLinearGroup.map (finiteAdeleResidue m) (finiteAdelicLevelIntegralMatrix N g)

/-- Reduction of the original adelic level matrices is a genuine homomorphism to the finite general-linear group. -/
def finiteAdelicLevelResidueHom (N m : ℕ) [NeZero m] :
    finiteAdeleGL2Gamma0 N →* GeneralLinearGroup (Fin 2) (ZMod m) :=
  (GeneralLinearGroup.map (finiteAdeleResidue m)).comp (finiteAdelicLevelIntegralHom N)

/-- The actual residue homomorphism has exactly the already defined original matrix entries. -/
theorem finiteAdelicLevelResidueHom_apply (N m : ℕ) [NeZero m] (g : finiteAdeleGL2Gamma0 N) :
    finiteAdelicLevelResidueHom N m g = finiteAdelicLevelResidue N m g := rfl

/-- At the original level, the lower-left entry of the actual residue matrix vanishes. -/
theorem finiteAdelicLevelResidue_lower_zero (N : ℕ) [NeZero N] (g : finiteAdeleGL2Gamma0 N) :
    (finiteAdelicLevelResidue N N g).val 1 0 = 0 :=
  (finiteAdeleResidue_eq_zero_iff N ⟨g.val.val 1 0, g.property.1.1 1 0⟩).mpr g.property.1.2

end
end Dubon2026
