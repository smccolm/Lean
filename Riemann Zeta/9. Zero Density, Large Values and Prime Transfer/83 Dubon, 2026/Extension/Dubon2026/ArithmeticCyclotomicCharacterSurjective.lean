import Dubon2026.RationalArithmeticCyclotomicCharacter
import Dubon2026.ArithmeticCyclotomicRealSignAction
import Dubon2026.ArithmeticCyclotomicCoefficientCharacter
import Dubon2026.OriginalCyclotomicPrimeStage

/-! The actual rational arithmetic cyclotomic character is surjective.
DUB-17's twisted dual-class detection uses a scalar different from one;
this constructs its character value from the original root action. -/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- Every cyclotomic power occurs in the actual rational normal extension
containing the specified primitive root. -/
theorem rationalPrimitiveRoot_autToPow_surjective
    {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    (m : ℕ) [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) :
    Function.Surjective (hζ.autToPow ℚ) := by
  let F := originalPrimitiveRootStage ℚ Ω hζ
  letI : Algebra ℚ F := F.algebra'
  let ζF : F := originalPrimitiveRootStageRoot ℚ Ω hζ
  have hζF : IsPrimitiveRoot ζF m := originalPrimitiveRootStageRoot_isPrimitive ℚ Ω hζ
  intro u
  let e := IsCyclotomicExtension.autEquivPow F
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos m))
  let σF := e.symm u
  have hpower : hζF.autToPow ℚ σF = u := by
    rw [hζF.autToPow_eq_modularCyclotomicCharacter m ℚ,
      ← (IsCyclotomicExtension.zeta_spec m ℚ F).autToPow_eq_modularCyclotomicCharacter m ℚ]
    exact e.apply_symm_apply u
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective Ω σF
  refine ⟨σ, ?_⟩
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [hζ.autToPow_spec ℚ]
  have he : (AlgEquiv.restrictNormalHom F σ) ζF = ζF ^ (u : ZMod m).val := by
    rw [hσ, ← hpower]
    exact (hζF.autToPow_spec ℚ σF).symm
  have he' := congrArg (fun x : F => (x : Ω)) he
  simpa only [AlgEquiv.restrictNormalHom_apply, map_pow] using he'

/-- Surjectivity holds for the native arithmetic character, independently
of the primitive root chosen in its definition. -/
theorem rationalArithmeticCyclotomicCharacter_surjective
    (a : 𝓞 ℚ) (q : ℕ) [NeZero q] (hqa : (q : 𝓞 ℚ) ∣ a) :
    Function.Surjective (rationalArithmeticCyclotomicCharacter a q hqa) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  letI : IsGalois ℚ U := originalUnramifiedGaloisUnion_isGalois a
  obtain ⟨ζ, hζ⟩ := originalQUnramifiedUnion_exists_primitiveRoot
    (Ω := AlgebraicClosure ℚ) a q hqa
  intro u
  obtain ⟨g, hg⟩ := rationalPrimitiveRoot_autToPow_surjective q hζ u
  refine ⟨g, ?_⟩
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← rationalArithmeticCyclotomicCharacter_apply_root a q hqa g hζ,
    ← hg, hζ.autToPow_spec ℚ]

/-- At characteristic different from two and three, the actual arithmetic
coefficient character has a value whose square differs from one. -/
theorem rationalArithmeticCyclotomicCoefficient_exists_square_ne_one
    (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
    [NeZero (2 : ZMod q)] [NeZero (3 : ZMod q)]
    (hqa : (q : 𝓞 ℚ) ∣ a) :
    ∃ g : rationalArithmeticGaloisGroup a,
      rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q) g ^ 2 ≠ 1 := by
  obtain ⟨g, hg⟩ := rationalArithmeticCyclotomicCharacter_surjective a q hqa
    (Units.mk0 2 (NeZero.ne _))
  refine ⟨g, ?_⟩
  have he : rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q) g = 2 := by
    change ZMod.castHom (dvd_refl q) (ZMod q)
      (rationalArithmeticCyclotomicCharacter a q hqa g : ZMod q) = 2
    rw [hg]
    simp
  rw [he]
  intro h
  have hz : (3 : ZMod q) = 0 := by linear_combination h
  exact NeZero.ne (3 : ZMod q) hz

end
end Dubon2026
