import Dubon2026.FrickeMatrices

/-! # The exact integral transition behind the Fricke transform of a level-one twist -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

/-- The integral determinant-one matrix associated to ab ≡ -1 modulo D. -/
def twistFrickeTransition (D a b : ℕ) (h : (D : ℤ) ∣ (a : ℤ) * b + 1) : SL(2, ℤ) :=
  ⟨!![(a : ℤ), -(((a : ℤ) * b + 1) / D); D, -(b : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination Int.ediv_mul_cancel h⟩

/-- The actual equal-diagonal Hecke representatives give the exact Fricke transition, including its scalar matrix. -/
theorem twistFrickeTransition_identity (D : ℕ) [NeZero D] (a b : ℕ)
    (h : (D : ℤ) ∣ (a : ℤ) * b + 1) :
    heckeTriangularMatrix D D a * frickeMatrix (D * D) =
      mapGL ℝ (twistFrickeTransition D a b h) *
        heckeTriangularMatrix D D b * heckeTriangularMatrix D D 0 := by
  have hr := congrArg (fun z : ℤ => (z : ℝ)) (Int.ediv_mul_cancel h)
  push_cast at hr
  ext i j
  simp only [GeneralLinearGroup.coe_mul, heckeTriangularMatrix_val, frickeMatrix_val,
    mapGL_coe_matrix, twistFrickeTransition, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [NeZero.ne D] <;>
    nlinarith [congrArg (fun x : ℝ => (D : ℝ) * x) hr]

/-- Every unit residue and its negative inverse satisfy the exact divisibility used in the integral transition. -/
theorem twistFrickeTransition_unit_divisibility (D : ℕ) [NeZero D] (u : (ZMod D)ˣ) :
    (D : ℤ) ∣ ((u : ZMod D).val : ℤ) * ((-↑u⁻¹ : ZMod D).val : ℤ) + 1 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one, ZMod.natCast_zmod_val,
    mul_neg, Units.mul_inv, neg_add_cancel]

/-- Every genuine level-one cusp form is invariant under the transition's actual integral slash action. -/
theorem levelOne_slash_integral {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    (f : UpperHalfPlane → ℂ) ∣[k] mapGL ℝ γ = f := by
  apply f.slash_action_eq'
  refine ⟨γ, ?_, rfl⟩
  change γ ∈ Gamma0 1
  rw [Gamma0_mem]
  exact Subsingleton.elim _ _

/-- The Fricke transform of a genuine level-one slash translate is another translate with the exact D^(k-2) scalar. -/
theorem levelOne_translate_fricke (D : ℕ) [NeZero D] (a b : ℕ)
    (h : (D : ℤ) ∣ (a : ℤ) * b + 1) {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) :
    ((f : UpperHalfPlane → ℂ) ∣[k] heckeTriangularMatrix D D a) ∣[k] frickeMatrix (D * D) =
      (D : ℂ) ^ (k - 2) • ((f : UpperHalfPlane → ℂ) ∣[k] heckeTriangularMatrix D D b) := by
  rw [← SlashAction.slash_mul, twistFrickeTransition_identity D a b h,
    SlashAction.slash_mul, SlashAction.slash_mul, levelOne_slash_integral,
    scalarMatrix_slash]

end
end Dubon2026
