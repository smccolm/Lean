import Dubon2026.SourceOriginalRationalBottomOdd
import Dubon2026.FiniteBaseCMSymmetricRepresentation
import Dubon2026.FiniteSymmetricIrreducible

/-! DUB-17/18 -> polarized residual automorphy inputs. The original
cyclotomic determinant gives the native real sign. Existing symmetric duality
then constructs the actual polarized representation, with exact kernel matrices,
CM component and odd similitude, over the same original coefficient field. -/
namespace Dubon2026.SourceDickson
noncomputable section
open NumberField Algebra Matrix
open scoped NumberField

/-- Keep the original rational scalar structure. -/
private local instance originalCMPolarizedUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

/-- The actual rational bottom field is totally real. -/
private local instance originalCMPolarizedBottomReal (a : 𝓞 ℚ) :
    IsTotallyReal (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) :=
  IsTotallyReal.ofRingEquiv (IntermediateField.botEquiv ℚ (rationalUnramifiedExtension a)).symm.toRingEquiv

/-- The actual native polarized symmetric representation is constructed
from the original odd cyclotomic determinant and a genuine CM subfield.
Its original matrices, component character and odd multiplier are retained. -/
theorem original_rational_cm_exists_polarized_symmetric
    (a : 𝓞 ℚ) (p w n : ℕ) [Fact p.Prime] (hpa : (p : 𝓞 ℚ) ∣ a)
    (hw : Odd w) (hn : n < p)
    {L : Type} [Field L] [Finite L] [CharP L p]
    [TopologicalSpace L] [DiscreteTopology L]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) L)
    (hρ : Continuous ρ)
    (hdet : GeneralLinearGroup.det.comp ρ =
      (sourceArithmeticCyclotomicUnitCharacter (F := L) p a hpa).toMonoidHom ^ w)
    (C : IntermediateField (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))
      (rationalUnramifiedExtension a))
    [IsQuadraticExtension (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) C]
    [IsTotallyComplex C] :
    let ρb : finiteBaseArithmeticGaloisGroup a
        (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) →ₜ*
        GeneralLinearGroup (Fin 2) L :=
      (show rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin 2) L from ⟨ρ, hρ⟩).comp
        (originalRationalBottomRestriction a)
    ∃ R : finiteBaseArithmeticGaloisGroup a
        (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) →ₜ*
        PolarizedGaloisGroup (Fin (n + 1)) L,
      (∀ g : FiniteBaseCMKernel a ⊥ C,
        R g.val = polarizedIdentityComponent
          (homogeneousSymmetricGL n (ρb g.val), (GeneralLinearGroup.det (ρb g.val)) ^ n)) ∧
      (∀ g, polarizedComponent (R g) = finiteBaseQuadraticComponent a ⊥ C g) ∧
      polarizedSimilitude (R (finiteBaseRealConjugation a ⊥)) = -1 := by
  let ρb : finiteBaseArithmeticGaloisGroup a
      (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) →ₜ*
      GeneralLinearGroup (Fin 2) L :=
    (show rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin 2) L from ⟨ρ, hρ⟩).comp
      (originalRationalBottomRestriction a)
  have hodd : (ρb (finiteBaseRealConjugation a ⊥)).val.det = -1 :=
    original_rational_bottom_odd_of_cyclotomic a p w hpa hw ρ hρ hdet
  have hfactorial : (n.factorial : L) ≠ 0 := factorial_cast_ne_zero_of_lt_char p n hn
  refine ⟨finiteBaseCMSymmetricPolarizedRepresentation a ⊥ C n ρb hfactorial hodd, ?_, ?_, ?_⟩
  · exact finiteBaseCMSymmetricPolarizedRepresentation_kernel a ⊥ C n ρb hfactorial hodd
  · exact finiteBaseCMSymmetricPolarizedRepresentation_component a ⊥ C n ρb hfactorial hodd
  · exact finiteBaseCMSymmetricPolarizedRepresentation_odd a ⊥ C n ρb hfactorial hodd

end
end Dubon2026.SourceDickson
