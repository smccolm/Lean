import Dubon2026.SourceBinaryFlagHecke

/-! The actual one-dimensional representation on a residual coefficient-flag quotient.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> descent from the original binary representation to its diagonal character
pieces. The character is computed from the actual congruence-group matrices;
the quotient map is the original coefficient extraction.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable (F : Type) [Field F] (p Q : ℕ) [CharP F p] (hpQ : p ∣ Q) (n j : ℕ)

/-- The exact diagonal character on the j-th original residual coefficient quotient. -/
def sourceBinaryFlagCharacter : Gamma0 Q →* F where
  toFun g := ((g.val 0 0 : ℤ) : F) ^ j * ((g.val 1 1 : ℤ) : F) ^ (n - j)
  map_one' := by simp
  map_mul' g h := by
    have h00 : (((g * h).val 0 0 : ℤ) : F) =
        ((g.val 0 0 : ℤ) : F) * ((h.val 0 0 : ℤ) : F) := by
      change (((g.val.val * h.val.val) 0 0 : ℤ) : F) = _
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul,
        sourceBinaryFlag_lower_zero F p Q hpQ h, mul_zero, add_zero]
    have h11 : (((g * h).val 1 1 : ℤ) : F) =
        ((g.val 1 1 : ℤ) : F) * ((h.val 1 1 : ℤ) : F) := by
      change (((g.val.val * h.val.val) 1 1 : ℤ) : F) = _
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul,
        sourceBinaryFlag_lower_zero F p Q hpQ g, zero_mul, zero_add]
    rw [h00, h11, mul_pow, mul_pow]
    ring

/-- The native one-dimensional representation with the original computed quotient character. -/
def sourceBinaryFlagQuotientRep : Rep F (Gamma0 Q) :=
  Rep.of ((Algebra.lsmul F F F).toMonoidHom.comp (sourceBinaryFlagCharacter F p Q hpQ n j))

/-- The original coefficient extraction is an equivariant map onto the actual quotient character. -/
def sourceBinaryFlagQuotientMap :
    sourceBinaryFlagRep F p Q hpQ n j ⟶ sourceBinaryFlagQuotientRep F p Q hpQ n j :=
  Rep.ofHom {
    toLinearMap := sourceBinaryFlagGraded F n j
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro P
      exact sourceBinaryFlag_group_graded F p Q hpQ n j g P.val P.property }

/-- The original quotient morphism is surjective at every nonterminal flag step. -/
theorem sourceBinaryFlagQuotientMap_surjective (hj : j ≤ n) :
    Function.Surjective (sourceBinaryFlagQuotientMap F p Q hpQ n j) :=
  sourceBinaryFlagGraded_surjective F n j hj

/-- Inclusion of the next actual coefficient step is a native representation morphism. -/
def sourceBinaryFlagInclusion :
    sourceBinaryFlagRep F p Q hpQ n (j + 1) ⟶ sourceBinaryFlagRep F p Q hpQ n j :=
  Rep.ofHom {
    toLinearMap := Submodule.inclusion
      (sourceBinaryCoefficientFlag_antitone F n (Nat.le_succ j))
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro P
      rfl }

/-- The next-step inclusion is injective on the actual coefficient space. -/
theorem sourceBinaryFlagInclusion_injective :
    Function.Injective (sourceBinaryFlagInclusion F p Q hpQ n j) :=
  Submodule.inclusion_injective (sourceBinaryCoefficientFlag_antitone F n (Nat.le_succ j))

/-- The original coefficient sequence is exact: the image of the next flag
step is the kernel of the computed one-dimensional quotient map. -/
theorem sourceBinaryFlagCoefficient_exact :
    LinearMap.range (sourceBinaryFlagInclusion F p Q hpQ n j).hom.toLinearMap =
      LinearMap.ker (sourceBinaryFlagQuotientMap F p Q hpQ n j).hom.toLinearMap := by
  ext P
  constructor
  · rintro ⟨P', rfl⟩
    exact (sourceBinaryFlagGraded_eq_zero_iff F n j _).mpr P'.property
  · intro hP
    have h := (sourceBinaryFlagGraded_eq_zero_iff F n j P).mp hP
    exact ⟨⟨P.val, h⟩, rfl⟩

end
end Dubon2026
