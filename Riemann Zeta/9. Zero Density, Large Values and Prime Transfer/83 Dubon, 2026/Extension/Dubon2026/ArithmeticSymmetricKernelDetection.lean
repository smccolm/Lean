import Dubon2026.SymmetricTwistedKernelDetection
import Dubon2026.ArithmeticCyclotomicCharacterSurjective
import Dubon2026.HomogeneousSymmetricContinuity

/-! Nonzero native arithmetic twisted H1 classes give nonzero original
cocycle values on the residual kernel fixing any required cyclotomic
power root. This is DUB-17's kernel-value input to the commuting trace
test and regular auxiliary-prime construction. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

/-- The actual original root-fixing residual kernel detects every nonzero
continuous cyclotomic-adjoint class of the genuine symmetric power.
The original rank-two full-SL2 image remains explicit; neither a scalar
witness nor finite-image H1 vanishing is an assumption. -/
theorem rationalArithmetic_symmetricH1_exists_nonzero_root_kernel
    (a : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime]
    [NeZero (2 : ZMod q)] [NeZero (3 : ZMod q)]
    (hqa : (q : 𝓞 ℚ) ∣ a)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) (ZMod q))
    (hρ : Continuous ρ)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod q)).range ≤ ρ.range)
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep
      ((homogeneousSymmetricGL degree).comp ρ)
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom))
    (hc : (Submodule.Quotient.mk c : ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL degree).comp ρ)
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous ((homogeneousSymmetricGL degree).comp ρ)
        ((homogeneousSymmetricGL_continuous degree).comp hρ)
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) ≠ 0) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    ∀ ζ : U, IsPrimitiveRoot ζ (q ^ (level + 1)) →
      ∃ τ : Gal(U/ℚ), τ ζ = ζ ∧ ρ τ = 1 ∧ c.val τ ≠ 0 := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  dsimp only
  intro ζ hζ
  let χq := (rationalArithmeticCyclotomicCharacter a q hqa).toMonoidHom
  let χ := (hζ.autToPow ℚ).prod χq
  let ω := (finiteCyclotomicCoefficientMap q (ZMod q)).toMonoidHom.comp
    (MonoidHom.snd (ZMod (q ^ (level + 1)))ˣ (ZMod q)ˣ)
  let R := (homogeneousSymmetricGL degree).comp ρ
  let ξ := (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
  let hA := matrixTraceZeroCharacterAction_continuous R
    ((homogeneousSymmetricGL_continuous degree).comp hρ) ξ
    (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous
  obtain ⟨g, hg⟩ := rationalArithmeticCyclotomicCoefficient_exists_square_ne_one a q hqa
  have hdetect := symmetricTwistedH1_exists_nonzero_joint_kernel degree ρ χ ω
    himage g hg hA c hc
  obtain ⟨τ, hρτ, hχτ, hne⟩ := hdetect
  refine ⟨τ, ?_, hρτ, hne⟩
  have hr : hζ.autToPow ℚ τ = 1 := congrArg Prod.fst hχτ
  have he : hζ.autToPow ℚ τ = hζ.autToPow ℚ 1 := hr.trans (map_one _).symm
  rw [← hζ.autToPow_spec ℚ τ, he, hζ.autToPow_spec ℚ 1]
  rfl

end
end Dubon2026
