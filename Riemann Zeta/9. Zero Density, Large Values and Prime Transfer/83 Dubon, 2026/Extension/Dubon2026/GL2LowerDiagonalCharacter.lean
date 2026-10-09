import Dubon2026.GeneralLinearUpperZero
import Dubon2026.FinitePlaceUnramifiedCharacter

/-! # Genuine diagonal characters on the original lower-triangular local group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original diagonal entry of a lower-triangular invertible matrix is a genuine unit and is multiplicative on the actual lower Borel. -/
def gl2LowerDiagonalHom {F : Type*} [Field F] (i : Fin 2) :
    gl2UpperZeroSubgroup F →* Fˣ where
  toFun b :=
    { val := b.val.val i i
      inv := (b.val⁻¹).val i i
      val_inv := by
        have hb : b.val.val 0 1 = 0 := b.property
        have hi : (b.val.val)⁻¹ 0 1 = 0 := by
          simpa only [GeneralLinearGroup.coe_inv] using gl2_upper_zero_inv b.val hb
        have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m i i) b.val.val_inv
        fin_cases i <;> simpa [Matrix.mul_apply, Fin.sum_univ_two, hb, hi] using he
      inv_val := by
        have hb : b.val.val 0 1 = 0 := b.property
        have hi : (b.val.val)⁻¹ 0 1 = 0 := by
          simpa only [GeneralLinearGroup.coe_inv] using gl2_upper_zero_inv b.val hb
        have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) F => m i i) b.val.inv_val
        fin_cases i <;> simpa [Matrix.mul_apply, Fin.sum_univ_two, hb, hi] using he }
  map_one' := by
    apply Units.ext
    change (1 : Matrix (Fin 2) (Fin 2) F) i i = 1
    simp
  map_mul' a b := by
    apply Units.ext
    change (a.val.val * b.val.val) i i = a.val.val i i * b.val.val i i
    have ha : a.val.val 0 1 = 0 := a.property
    have hb : b.val.val 0 1 = 0 := b.property
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]

/-- The genuine diagonal homomorphism keeps the literal original matrix entry. -/
theorem gl2LowerDiagonalHom_val {F : Type*} [Field F] (i : Fin 2)
    (b : gl2UpperZeroSubgroup F) : (gl2LowerDiagonalHom i b).val = b.val.val i i := rfl

/-- The original integral Borel has actual integral diagonal units, including their original inverses. -/
theorem gl2LowerDiagonalHom_integral (v : HeightOneSpectrum ℤ) (i : Fin 2)
    (b : gl2UpperZeroSubgroup (v.adicCompletion ℚ)) (hb : b.val ∈ finitePlaceGL2Gamma0 1 v) :
    (gl2LowerDiagonalHom i b).val ∈ v.adicCompletionIntegers ℚ ∧
      (gl2LowerDiagonalHom i b).inv ∈ v.adicCompletionIntegers ℚ := by
  exact ⟨(finitePlaceLevelMatrix_one_iff_integral v _).mp hb.1 i i,
    (finitePlaceLevelMatrix_one_iff_integral v _).mp hb.2 i i⟩

/-- The product of the two genuine unramified diagonal characters on the original local lower Borel. -/
def finitePlaceLowerCharacter (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ) :
    gl2UpperZeroSubgroup (v.adicCompletion ℚ) →* ℂ :=
  (Units.coeHom ℂ).comp (((finitePlaceUnramifiedCharacter v z₁).comp (gl2LowerDiagonalHom 0)) *
    ((finitePlaceUnramifiedCharacter v z₂).comp (gl2LowerDiagonalHom 1)))

/-- The actual inducing character is trivial on the genuine intersection of the Borel and integral local group. -/
theorem finitePlaceLowerCharacter_integral (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (b : gl2UpperZeroSubgroup (v.adicCompletion ℚ)) (hb : b.val ∈ finitePlaceGL2Gamma0 1 v) :
    finitePlaceLowerCharacter v z₁ z₂ b = 1 := by
  have h₀ := gl2LowerDiagonalHom_integral v 0 b hb
  have h₁ := gl2LowerDiagonalHom_integral v 1 b hb
  change ((finitePlaceUnramifiedCharacter v z₁ (gl2LowerDiagonalHom 0 b) *
    finitePlaceUnramifiedCharacter v z₂ (gl2LowerDiagonalHom 1 b) : ℂˣ) : ℂ) = 1
  rw [finitePlaceUnramifiedCharacter_integral v z₁ _ h₀.1 h₀.2,
    finitePlaceUnramifiedCharacter_integral v z₂ _ h₁.1 h₁.2, one_mul, Units.val_one]

end
end Dubon2026
