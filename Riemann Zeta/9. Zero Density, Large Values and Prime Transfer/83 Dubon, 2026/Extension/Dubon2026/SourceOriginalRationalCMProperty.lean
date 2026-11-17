import Dubon2026.SourceOriginalCMKernelConsequences
import Dubon2026.SourceOriginalRationalBottomRestriction

/-! DUB-17/18 -> original polarized CM deformation inputs. Native
bottom-field restriction retains the actual rational representation and its
finite image bounds. The original CM-kernel conclusions therefore hold for
all genuine quadratic subfields to which the CM construction applies. -/
namespace Dubon2026.SourceDickson
noncomputable section
open NumberField Algebra Matrix
open scoped NumberField

/-- Keep the actual rational scalar structure in the original union. -/
private local instance originalCMPropertyUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

/-- Original-field spanning, absolute irreducibility and adjoint vanishing
on actual quadratic component kernels, with the native symmetric matrices.
This states consequences for genuine fields; it does not postulate or construct
a CM field or its required arithmetic disjointness properties. -/
def HasOriginalRationalCMConsequences
    (a : 𝓞 ℚ) (p : ℕ) {L : Type} [Field L] [TopologicalSpace L]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) L) : Prop :=
  ∀ (_ : DiscreteTopology L) (hρ : Continuous ρ)
    (C : IntermediateField (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))
      (rationalUnramifiedExtension a))
    (hC : IsQuadraticExtension (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) C),
    letI := hC
    let ρb : finiteBaseArithmeticGaloisGroup a
        (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) →ₜ*
        GeneralLinearGroup (Fin 2) L :=
      (show rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin 2) L from ⟨ρ, hρ⟩).comp
        (originalRationalBottomRestriction a)
    HasOriginalSymmetricKernelConsequences p
      (ρb.toMonoidHom.comp (finiteBaseQuadraticComponent a ⊥ C).toMonoidHom.ker.subtype) ∧
    ∀ n : ℕ, 2 * n < p - 1 →
      Submodule.span L (Set.range (fun g : FiniteBaseCMKernel a ⊥ C =>
        ((finiteBaseCMSymmetricMatrices a ⊥ C n ρb g).1).val)) = ⊤ ∧
      ∀ (E : Type) (_ : Field E) (_ : Algebra L E),
        Representation.IsIrreducible (matrixStandardRepresentation
          (matrixCoefficientExtension (L := E)
            ((MonoidHom.fst _ _).comp (finiteBaseCMSymmetricMatrices a ⊥ C n ρb).toMonoidHom)))

/-- The same original rational finite linear bounds derive the actual CM
matrix consequences; no independent restricted image hypothesis remains. -/
theorem finite_linear_bounds_original_rational_cm_consequences
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime] {L : Type} [Field L] [CharP L p]
    [TopologicalSpace L] (j : L →+* K p)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) L)
    (hp3 : 3 < p) (h : HasFiniteLinearSubfieldBounds p j ρ) :
    HasOriginalRationalCMConsequences a p ρ := by
  intro hDiscrete hρ C hC
  letI := hC
  let ρb : finiteBaseArithmeticGaloisGroup a
      (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) →ₜ*
      GeneralLinearGroup (Fin 2) L :=
    (show rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin 2) L from ⟨ρ, hρ⟩).comp
      (originalRationalBottomRestriction a)
  have hb : HasFiniteLinearSubfieldBounds p j ρb.toMonoidHom :=
    original_finite_linear_bounds_rational_bottom a p j ρ h
  refine ⟨finite_linear_bounds_original_cm_kernel_consequences a ⊥ C p j ρb hp3 hb, ?_⟩
  intro n hn
  refine ⟨finite_linear_bounds_original_cm_matrix_span a ⊥ C p n j ρb hp3 hb hn, ?_⟩
  intro E hE hAlg
  exact finite_linear_bounds_original_cm_absolute_irreducible a ⊥ C p n j ρb hp3 hb hn

end
end Dubon2026.SourceDickson
