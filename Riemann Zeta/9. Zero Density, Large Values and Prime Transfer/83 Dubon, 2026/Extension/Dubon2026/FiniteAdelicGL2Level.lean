import Dubon2026.GeneralLinearUnitDiagonal
import Dubon2026.FiniteAdeleLevelSubgroup

/-! # Actual finite adelic general-linear level matrices -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix
open scoped MatrixGroups

/-- The genuine integral matrix order whose lower-left entry is divisible by the level. -/
def finiteAdeleLevelMatrix (N : ℕ) (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)) : Prop :=
  (∀ i j, g i j ∈ finiteAdeleIntegerSubring) ∧ finiteAdeleLevelMultiple N (g 1 0)

/-- The actual identity matrix belongs to the integral level order. -/
theorem finiteAdeleLevelMatrix_one (N : ℕ) : finiteAdeleLevelMatrix N 1 := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp
  · exact ⟨0, finiteAdeleIntegerSubring.zero_mem, by simp⟩

/-- The original integral level matrix conditions are preserved under genuine matrix multiplication. -/
theorem finiteAdeleLevelMatrix_mul (N : ℕ)
    {g h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)}
    (hg : finiteAdeleLevelMatrix N g) (hh : finiteAdeleLevelMatrix N h) :
    finiteAdeleLevelMatrix N (g * h) := by
  rcases hg with ⟨hg, a, ha, hga⟩
  rcases hh with ⟨hh, b, hb, hhb⟩
  constructor
  · intro i j
    change ∑ k : Fin 2, g i k * h k j ∈ finiteAdeleIntegerSubring
    exact finiteAdeleIntegerSubring.sum_mem fun k _ =>
      finiteAdeleIntegerSubring.mul_mem (hg i k) (hh k j)
  · refine ⟨a * h 0 0 + g 1 1 * b,
      finiteAdeleIntegerSubring.add_mem
        (finiteAdeleIntegerSubring.mul_mem ha (hh 0 0))
        (finiteAdeleIntegerSubring.mul_mem (hg 1 1) hb), ?_⟩
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hga, hhb]
    ring

/-- The genuine GL2 level group consists of matrices and inverse matrices in the integral level order. -/
def finiteAdeleGL2Gamma0 (N : ℕ) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) where
  carrier := {g | finiteAdeleLevelMatrix N g.val ∧ finiteAdeleLevelMatrix N (g⁻¹).val}
  one_mem' := ⟨finiteAdeleLevelMatrix_one N, finiteAdeleLevelMatrix_one N⟩
  mul_mem' := by
    intro g h hg hh
    constructor
    · exact finiteAdeleLevelMatrix_mul N hg.1 hh.1
    · simpa only [_root_.mul_inv_rev, Units.val_mul] using
        finiteAdeleLevelMatrix_mul N hh.2 hg.2
  inv_mem' := by
    intro g hg
    simpa only [inv_inv] using hg.symm

/-- The actual determinant-one level subgroup embeds in the genuine general-linear level subgroup. -/
theorem finiteAdeleGamma0_toGL_mem (N : ℕ) (g : SL(2, FiniteAdeleRing ℤ ℚ))
    (hg : g ∈ finiteAdeleGamma0 N) :
    Matrix.SpecialLinearGroup.toGL g ∈ finiteAdeleGL2Gamma0 N := by
  change g ∈ finiteAdeleGamma0 N ∧ g⁻¹ ∈ finiteAdeleGamma0 N
  exact ⟨hg, (finiteAdeleGamma0 N).inv_mem hg⟩

/-- A genuine everywhere-integral determinant unit supplies an actual level diagonal matrix. -/
theorem finiteAdele_integral_unit_diagonal_mem (N : ℕ) (u : finiteAdeleIntegerSubringˣ) :
    gl2UnitFirstDiagonal (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u) ∈ finiteAdeleGL2Gamma0 N := by
  have hdiag (v : finiteAdeleIntegerSubringˣ) :
      finiteAdeleLevelMatrix N (gl2UnitFirstDiagonal
        (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom v)).val := by
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [gl2UnitFirstDiagonal]
    · exact ⟨0, finiteAdeleIntegerSubring.zero_mem, by simp [gl2UnitFirstDiagonal]⟩
  constructor
  · exact hdiag u
  · rw [gl2UnitFirstDiagonal_inv, ← map_inv]
    exact hdiag u⁻¹

/-- The actual nonzero-level integral matrix order is open in the canonical finite adelic matrix space. -/
theorem finiteAdeleLevelMatrix_isOpen (N : ℕ) [NeZero N] :
    IsOpen {g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) | finiteAdeleLevelMatrix N g} := by
  have hc (i j : Fin 2) : Continuous
      (fun g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) => g i j) :=
    (_root_.continuous_apply j).comp (_root_.continuous_apply i)
  change IsOpen {g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ) |
    (∀ i j, g i j ∈ finiteAdeleIntegerSubring) ∧ finiteAdeleLevelMultiple N (g 1 0)}
  apply IsOpen.inter
  · convert (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      finiteAdeleIntegerSubring_isOpen.preimage (hc i j)) using 1
    ext g
    simp
    rfl
  · exact (finiteAdeleLevelMultiple_isOpen N).preimage (hc 1 0)

/-- The actual general-linear level group is open in the canonical finite adelic GL2 topology. -/
theorem finiteAdeleGL2Gamma0_isOpen (N : ℕ) [NeZero N] :
    IsOpen (finiteAdeleGL2Gamma0 N :
      Set (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))) :=
  ((finiteAdeleLevelMatrix_isOpen N).preimage Units.continuous_val).inter
    ((finiteAdeleLevelMatrix_isOpen N).preimage (Units.continuous_val.comp continuous_inv))

end
end Dubon2026
