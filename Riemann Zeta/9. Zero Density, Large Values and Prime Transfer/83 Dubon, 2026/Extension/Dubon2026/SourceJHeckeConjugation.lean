import Dubon2026.SourceWeightTwoScalarHecke

/-! DUB-17/18 -> actual parabolic Hecke eigensystem realization ->
reflection compatibility of the original period pair. The literal integral
reflection preserves the genuine upper Hecke subgroup and commutes with
the already constructed diagonal conjugation. The latter is proved from
its existing matrix equation, avoiding a second divided-entry definition.
-/
namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup SourceModularSymbols
open scoped MatrixGroups

theorem sourceJConjugate_mem_heckeUpper {N p : ℕ} {γ : Gamma0 N}
    (hγ : γ ∈ heckeUpperSubgroup N p) : sourceJConjugateGamma0 N γ ∈ heckeUpperSubgroup N p := by
  change (((-γ.val 0 1 : ℤ) : ZMod p)) = 0
  rw [Int.cast_neg]
  change -((γ.val 0 1 : ℤ) : ZMod p) = 0
  rw [show ((γ.val 0 1 : ℤ) : ZMod p) = 0 from hγ, neg_zero]

/-- Restrict the actual reflection to the original upper Hecke subgroup. -/
def sourceJHeckeUpper (N p : ℕ) : heckeUpperSubgroup N p →* heckeUpperSubgroup N p where
  toFun γ := ⟨sourceJConjugateGamma0 N γ.val, sourceJConjugate_mem_heckeUpper γ.property⟩
  map_one' := Subtype.ext (sourceJConjugateGamma0Hom N).map_one
  map_mul' γ δ := Subtype.ext ((sourceJConjugateGamma0Hom N).map_mul γ.val δ.val)

theorem sourceHeckeConjugation_reflection {N p : ℕ} [NeZero p] (hp : p.Prime)
    (γ : heckeUpperSubgroup N p) :
    sourceHeckeConjugation hp (sourceJHeckeUpper N p γ) =
      sourceJConjugateGamma0 N (sourceHeckeConjugation hp γ) := by
  have he := (sourceHeckeConjugation_integral hp γ).2
  have he' := (sourceHeckeConjugation_integral hp (sourceJHeckeUpper N p γ)).2
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne p)
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases j
  · have h0 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A i 0) he
    have h1 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A i 0) he'
    fin_cases i <;>
      simp [integralTriangularMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        sourceJHeckeUpper, sourceJConjugateGamma0, sourceJConjugateSL] at h0 h1 ⊢ <;> linarith
  · apply mul_right_cancel₀ hp0
    have h0 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A i 1) he
    have h1 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A i 1) he'
    fin_cases i <;>
      simp [integralTriangularMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        sourceJHeckeUpper, sourceJConjugateGamma0, sourceJConjugateSL] at h0 h1 ⊢
    · linarith
    · exact Or.inl (mul_right_cancel₀ hp0 (h1.symm.trans h0))

end
end Dubon2026
