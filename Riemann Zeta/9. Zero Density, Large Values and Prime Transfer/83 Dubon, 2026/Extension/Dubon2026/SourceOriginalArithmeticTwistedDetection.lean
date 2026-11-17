import Dubon2026.SourceOriginalTwistedTopology
import Dubon2026.SourceArithmeticCyclotomicSquare

/-! DUB-17/18 -> actual regular auxiliary-prime detection -> nonzero original
cocycle value on the actual arithmetic residual/cyclotomic kernel. The native
cyclotomic root action supplies the nontrivial scalar; no character witness is
assumed. The original field and its specified topology are retained. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix
open scoped NumberField

/-- Detection on the joint kernel of the original arithmetic residual action
and the actual arithmetic cyclotomic character, in every symmetric degree. -/
def HasOriginalArithmeticSymmetricTwistedKernelDetection
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a)
    {F : Type} [Field F] [CharP F p] [TopologicalSpace F]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) F) : Prop :=
  ∀ (_ : IsTopologicalRing F) (n : ℕ),
    let ξ := rationalArithmeticCyclotomicCoefficientCharacter a p hpa F
    ∀ hA : Continuous (fun z : rationalArithmeticGaloisGroup a ×
        matrixTraceZeroSubmodule (Fin (n + 1)) F =>
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL n).comp ρ) ξ.toMonoidHom).ρ z.1 z.2),
    ∀ c : continuousRepresentationCocyclesOne
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL n).comp ρ) ξ.toMonoidHom),
    (Submodule.Quotient.mk c : ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL n).comp ρ) ξ.toMonoidHom) hA) ≠ 0 →
    ∃ τ, ρ τ = 1 ∧ rationalArithmeticCyclotomicCharacter a p hpa τ = 1 ∧ c.val τ ≠ 0

/-- Native arithmetic cyclotomic surjectivity supplies the scalar witness
required by the proved original twisted-kernel detection property. -/
theorem original_arithmetic_symmetric_twisted_detection_of_original
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a)
    {F : Type} [Field F] [CharP F p] [TopologicalSpace F]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) F)
    (hp3 : 3 < p) (h : HasOriginalSymmetricTwistedKernelDetectionAtTopology ρ) :
    HasOriginalArithmeticSymmetricTwistedKernelDetection a p hpa ρ := by
  intro hRing n
  dsimp only
  intro hA c hc
  obtain ⟨g, hg⟩ := originalArithmeticCyclotomicCoefficient_exists_square_ne_one a p hpa F hp3
  exact h hRing (ZMod p)ˣ inferInstance
    (rationalArithmeticCyclotomicCharacter a p hpa).toMonoidHom
    (finiteCyclotomicCoefficientMap p F).toMonoidHom g hg n hA c hc

end
end Dubon2026.SourceDickson
