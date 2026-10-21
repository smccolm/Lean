import Dubon2026.SourceCuspBoundaryValues
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> period-pair injectivity -> cusp limits of the reflected primitive.
The actual integral conjugation carries every original cusp to another
original cusp and intertwines the pinned upper-half-plane J action.
-/
namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane Complex
open scoped MatrixGroups ComplexConjugate

/-- Integral special-linear conjugation by the sign matrix underlying J. -/
def sourceJConjugateSL (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    rw [Matrix.det_fin_two]
    change γ 0 0 * γ 1 1 - (-γ 0 1) * (-γ 1 0) = 1
    simpa only [Matrix.det_fin_two, neg_mul_neg] using γ.det_coe⟩

/-- Reflection of the original modular action is the literal integral
conjugated action, so no separate cusp embedding is introduced. -/
theorem sourceJ_smul_SL (γ : SL(2, ℤ)) (τ : ℍ) :
    J • (γ • τ) = sourceJConjugateSL γ • (J • τ) := by
  apply UpperHalfPlane.ext
  rw [coe_J_smul, UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply, coe_J_smul]
  dsimp only [sourceJConjugateSL, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [map_neg, Complex.ofReal_neg,
    map_div₀, map_add, map_mul, Complex.conj_ofReal]
  ring

/-- Integral reflection is an involution on the original special linear group. -/
theorem sourceJConjugateSL_involutive :
    Function.Involutive sourceJConjugateSL := by
  intro γ
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceJConjugateSL]

/-- Reflection preserves the original level condition. -/
theorem sourceJConjugateSL_mem_Gamma0 {N : ℕ} {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    sourceJConjugateSL γ ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  simpa [sourceJConjugateSL] using congrArg Neg.neg hγ

/-- The actual reflection on the level group, with no change of arithmetic subgroup. -/
def sourceJConjugateGamma0 (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) :
    CongruenceSubgroup.Gamma0 N :=
  ⟨sourceJConjugateSL γ.val, sourceJConjugateSL_mem_Gamma0 γ.property⟩

/-- The reflected original level element returns to itself after two reflections. -/
theorem sourceJConjugateGamma0_involutive (N : ℕ) :
    Function.Involutive (sourceJConjugateGamma0 N) := by
  intro γ
  exact Subtype.ext (sourceJConjugateSL_involutive γ.val)

/-- Reflection preserves integral matrix multiplication. -/
theorem sourceJConjugateSL_mul (γ δ : SL(2, ℤ)) :
    sourceJConjugateSL (γ * δ) = sourceJConjugateSL γ * sourceJConjugateSL δ := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceJConjugateSL, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Reflection fixes the identity integral matrix. -/
theorem sourceJConjugateSL_one : sourceJConjugateSL 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sourceJConjugateSL]

/-- Reflection is an actual endomorphism of the original arithmetic subgroup. -/
def sourceJConjugateGamma0Hom (N : ℕ) :
    CongruenceSubgroup.Gamma0 N →* CongruenceSubgroup.Gamma0 N where
  toFun := sourceJConjugateGamma0 N
  map_one' := Subtype.ext sourceJConjugateSL_one
  map_mul' γ δ := Subtype.ext (sourceJConjugateSL_mul γ.val δ.val)

end
end Dubon2026
