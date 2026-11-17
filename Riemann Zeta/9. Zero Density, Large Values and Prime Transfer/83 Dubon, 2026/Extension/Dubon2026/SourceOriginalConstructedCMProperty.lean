import Dubon2026.SourceOriginalRationalCMPolarizationProperty
import Dubon2026.SourceOriginalRationalCMProperty
import Dubon2026.ArithmeticSupportRestriction

/-! DUB-17/18 -> actual polarized residual input. This predicate records
an actual CM field in support 4a and polarized symmetric powers of the literal
pullback of the original representation. Its large-image consequence remains
explicitly conditional until the arithmetic small-image alternatives are excluded. -/
namespace Dubon2026.SourceDickson
noncomputable section
open NumberField Algebra Matrix
open scoped NumberField

/-- Preserve the original rational scalar structure. -/
private local instance originalConstructedCMUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

/-- The rational bottom field in the enlarged extension is totally real. -/
private local instance originalConstructedCMBottomReal (a : 𝓞 ℚ) :
    IsTotallyReal (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) :=
  IsTotallyReal.ofRingEquiv (IntermediateField.botEquiv ℚ (rationalUnramifiedExtension a)).symm.toRingEquiv

/-- A genuine CM field, polarized symmetric representations with exact
original kernel matrices and odd multiplier, and the original finite-image
consequences on its actual component kernel. The support enlargement is the
literal existing restriction; the original coefficient field is retained.
CM disjointness, local deformation conditions and automorphy are not asserted. -/
def HasOriginalConstructedCMResidual
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime]
    {L : Type} [Field L] [TopologicalSpace L]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) L) : Prop :=
  ∀ (_ : DiscreteTopology L) (hρ : Continuous ρ),
    ∃ C : IntermediateField (⊥ : IntermediateField ℚ (rationalUnramifiedExtension (4 * a)))
        (rationalUnramifiedExtension (4 * a)),
    ∃ hC : IsQuadraticExtension (⊥ : IntermediateField ℚ (rationalUnramifiedExtension (4 * a))) C,
    ∃ hComplex : IsTotallyComplex C,
    letI := hC
    letI := hComplex
    let ρs : rationalArithmeticGaloisGroup (4 * a) →ₜ* GeneralLinearGroup (Fin 2) L :=
      (show rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin 2) L from ⟨ρ, hρ⟩).comp
        (rationalArithmeticSupportRestriction a (4 * a) (dvd_mul_left a 4))
    let ρb := ρs.comp (originalRationalBottomRestriction (4 * a))
    (∀ j : L →+* K p, HasFiniteLinearSubfieldBounds p j ρ →
      HasOriginalSymmetricKernelConsequences p
        (ρb.toMonoidHom.comp (finiteBaseQuadraticComponent (4 * a) ⊥ C).toMonoidHom.ker.subtype)) ∧
    ∀ n : ℕ, n < p →
    ∃ R : finiteBaseArithmeticGaloisGroup (4 * a)
        (⊥ : IntermediateField ℚ (rationalUnramifiedExtension (4 * a))) →ₜ*
        PolarizedGaloisGroup (Fin (n + 1)) L,
      (∀ g : FiniteBaseCMKernel (4 * a) ⊥ C,
        R g.val = polarizedIdentityComponent
          (homogeneousSymmetricGL n (ρb g.val), (GeneralLinearGroup.det (ρb g.val)) ^ n)) ∧
      (∀ g, polarizedComponent (R g) = finiteBaseQuadraticComponent (4 * a) ⊥ C g) ∧
      polarizedSimilitude (R (finiteBaseRealConjugation (4 * a) ⊥)) = -1

end
end Dubon2026.SourceDickson
