import Dubon2026.FiniteBaseCMSymmetricRepresentation
import Dubon2026.PolarizedRealInvariantDimension
import Dubon2026.CyclicMatrixTraceInvariants

/-! The actual real conjugation of the original CM symmetric-power
representation has the source full-adjoint invariant dimension. This is
the infinite-place term needed on the DUB-17 polarized Selmer chain. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the polarized symmetric-power consumer. -/
local instance finiteBaseCMSymmetricRealInvariantUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  {L : Type} [Field L] [Finite L] [TopologicalSpace L] [DiscreteTopology L]
  (n : ℕ) (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) L)
  (hn : (n.factorial : L) ≠ 0) (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1)

/-- The actual original real conjugation evaluates to the constructed symmetric polarization element. -/
theorem finiteBaseCMSymmetricPolarizedRepresentation_real_place :
    finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd (finiteBaseRealConjugation a F) =
      polarizedInvolution (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F))) := by
  unfold finiteBaseCMSymmetricPolarizedRepresentation
  exact finiteBaseCMPolarizedExtension_real_place a F K _ _ _ _

/-- The original conjugation subgroup has the exact source odd full-adjoint invariant dimension. -/
theorem finiteBaseCMSymmetricRealInvariants_finrank (h2 : (2 : L) ≠ 0) :
    Module.finrank L (Representation.invariants
      ((polarizedAdjointRepresentation.comp
        (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd).toMonoidHom).comp
        (Subgroup.zpowers (finiteBaseRealConjugation a F)).subtype)) = (n + 1) * n / 2 := by
  let c := finiteBaseRealConjugation a F
  let S := Subgroup.zpowers c
  let γ : S := ⟨c, Subgroup.mem_zpowers c⟩
  rw [representation_comp_invariants_eq_generator_ker
    (polarizedAdjointRepresentation.comp
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd).toMonoidHom)
    S.subtype γ (fun g => g.property)]
  change Module.finrank L (LinearMap.ker
    (polarizedAdjointRepresentation
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd (finiteBaseRealConjugation a F)) - 1)) = _
  have he : LinearMap.ker (polarizedAdjointRepresentation
      (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd (finiteBaseRealConjugation a F)) - 1) =
      polarizedRealInvariants (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F))) := by
    rw [finiteBaseCMSymmetricPolarizedRepresentation_real_place]
    rfl
  apply (LinearEquiv.ofEq _ _ he).finrank_eq.trans
  simpa only [Nat.add_sub_cancel] using
    polarizedRealInvariants_finrank (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F)))
      (finiteBaseCMSymmetricPolarization_symmetric a F n ρ hn hodd) h2

end
end Dubon2026

