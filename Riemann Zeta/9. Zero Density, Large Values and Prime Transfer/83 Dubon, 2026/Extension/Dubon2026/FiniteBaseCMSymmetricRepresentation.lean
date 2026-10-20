import Dubon2026.FiniteBaseCMSymmetricMatrices

/-! The original continuous odd rank-two arithmetic representation now
constructs its genuine polarized symmetric power. The duality matrix,
its invertibility, symmetry and conjugate-duality equation are derived,
not inputs. The modular-form realization of the rank-two representation
remains the source arithmetic obligation in DUB-17. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the polarized symmetric-power consumer. -/
local instance finiteBaseCMSymmetricRepresentationUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  {L : Type*} [Field L] [Finite L] [TopologicalSpace L] [DiscreteTopology L]
  (n : ℕ) (ρ : finiteBaseArithmeticGaloisGroup a F →ₜ* GeneralLinearGroup (Fin 2) L)
  (hn : (n.factorial : L) ≠ 0) (hodd : (ρ (finiteBaseRealConjugation a F)).val.det = -1)

/-- The original odd rank-two representation produces the actual continuous polarized symmetric power. -/
@[irreducible] def finiteBaseCMSymmetricPolarizedRepresentation :
    finiteBaseArithmeticGaloisGroup a F →ₜ* PolarizedGaloisGroup (Fin (n + 1)) L :=
  finiteBaseCMPolarizedExtension a F K (finiteBaseCMSymmetricMatrices a F K n ρ)
    (symmetricRealPolarization n hn (ρ (finiteBaseRealConjugation a F)))
    (finiteBaseCMSymmetricPolarization_symmetric a F n ρ hn hodd)
    (finiteBaseCMSymmetricMatrices_polarization a F K n ρ hn)

/-- The constructed CM restriction retains the literal original symmetric-power matrices and determinant multiplier. -/
theorem finiteBaseCMSymmetricPolarizedRepresentation_kernel (g : FiniteBaseCMKernel a F K) :
    finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd g.val =
      polarizedIdentityComponent (homogeneousSymmetricGL n (ρ g.val), (GeneralLinearGroup.det (ρ g.val)) ^ n) := by
  unfold finiteBaseCMSymmetricPolarizedRepresentation
  exact finiteBaseCMPolarizedExtension_kernel a F K _ _ _ _ g

/-- The constructed symmetric power has the actual CM quadratic component character. -/
theorem finiteBaseCMSymmetricPolarizedRepresentation_component (g : finiteBaseArithmeticGaloisGroup a F) :
    polarizedComponent (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd g) =
      finiteBaseQuadraticComponent a F K g := by
  unfold finiteBaseCMSymmetricPolarizedRepresentation
  exact finiteBaseCMPolarizedExtension_component a F K _ _ _ _ g

/-- The original real-place involution has the source odd similitude in the constructed polarized symmetric power. -/
theorem finiteBaseCMSymmetricPolarizedRepresentation_odd :
    polarizedSimilitude (finiteBaseCMSymmetricPolarizedRepresentation a F K n ρ hn hodd
      (finiteBaseRealConjugation a F)) = -1 := by
  unfold finiteBaseCMSymmetricPolarizedRepresentation
  exact finiteBaseCMPolarizedExtension_odd a F K _ _ _ _

end
end Dubon2026
