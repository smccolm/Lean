import Dubon2026.SourceOriginalArithmeticTwistedDetection

/-! DUB-17/18 -> automorphy -> regular auxiliary primes -> a nonzero
original cocycle value on the residual kernel fixing the required higher
cyclotomic root. Reuse the proved finite-subfield central-scalar detection
with the product of the actual root action and arithmetic cyclotomic action.
The original residue field is retained; it need not be the prime field. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix
open scoped NumberField

/-- Actual finite linear subfield bounds detect each nonzero original twisted
class on the residual kernel fixing any prescribed higher cyclotomic root.
The actual arithmetic cyclotomic character is also trivial there. -/
theorem original_arithmetic_symmetricH1_exists_nonzero_root_kernel
    (a : 𝓞 ℚ) (p degree level : ℕ) [Fact p.Prime]
    (hpa : (p : 𝓞 ℚ) ∣ a)
    {F : Type} [Field F] [CharP F p] [TopologicalSpace F] [IsTopologicalRing F]
    (j : F →+* K p)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) F)
    (hp3 : 3 < p) (h : HasFiniteLinearSubfieldBounds p j ρ)
    (hA : Continuous (fun z : rationalArithmeticGaloisGroup a ×
        matrixTraceZeroSubmodule (Fin (degree + 1)) F =>
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL degree).comp ρ)
        (rationalArithmeticCyclotomicCoefficientCharacter a p hpa F).toMonoidHom).ρ
          z.1 z.2))
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep
      ((homogeneousSymmetricGL degree).comp ρ)
      (rationalArithmeticCyclotomicCoefficientCharacter a p hpa F).toMonoidHom))
    (hc : (Submodule.Quotient.mk c : ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL degree).comp ρ)
        (rationalArithmeticCyclotomicCoefficientCharacter a p hpa F).toMonoidHom) hA) ≠ 0) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    ∀ ζ : U, IsPrimitiveRoot ζ (p ^ (level + 1)) →
      ∃ τ : Gal(U/ℚ), τ ζ = ζ ∧ ρ τ = 1 ∧
        rationalArithmeticCyclotomicCharacter a p hpa τ = 1 ∧ c.val τ ≠ 0 := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  dsimp only
  intro ζ hζ
  let χp := (rationalArithmeticCyclotomicCharacter a p hpa).toMonoidHom
  let χ := (hζ.autToPow ℚ).prod χp
  let ω := (finiteCyclotomicCoefficientMap p F).toMonoidHom.comp
    (MonoidHom.snd (ZMod (p ^ (level + 1)))ˣ (ZMod p)ˣ)
  obtain ⟨g, hg⟩ := originalArithmeticCyclotomicCoefficient_exists_square_ne_one
    a p hpa F hp3
  obtain ⟨τ, hρτ, hχτ, hne⟩ :=
    finite_linear_bounds_symmetricTwistedH1_exists_nonzero_joint_kernel
      p degree j ρ χ ω hp3 h g hg hA c hc
  refine ⟨τ, ?_, hρτ, congrArg Prod.snd hχτ, hne⟩
  have hr : hζ.autToPow ℚ τ = 1 := congrArg Prod.fst hχτ
  have he : hζ.autToPow ℚ τ = hζ.autToPow ℚ 1 := hr.trans (map_one _).symm
  rw [← hζ.autToPow_spec ℚ τ, he, hζ.autToPow_spec ℚ 1]
  rfl

end
end Dubon2026.SourceDickson
