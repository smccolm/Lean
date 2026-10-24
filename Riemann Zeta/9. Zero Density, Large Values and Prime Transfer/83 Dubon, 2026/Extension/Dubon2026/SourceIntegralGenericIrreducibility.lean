import Dubon2026.SourceIntegralAllLevelGenericRoots

/-! The existing exact minimal polynomial is irreducible over the generic
rational j-field. Native rational-function equivalence identifies the
coordinate specialization as a field isomorphism. This supplies the
Galois-transitivity input to the all-level cyclic-root bijection needed by
the DUB-17/18 inertia census, without a new irreducibility proof. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial IntermediateField CoefficientPresentation
open scoped IntermediateField
noncomputable section
variable (N : ℕ) (K : Type*) [Field K]

/-- At the rational indeterminate the actual coordinate specialization is the native field isomorphism. -/
theorem coordinateSpecialization_ratFunc :
    coordinateSpecialization N K (RatFunc.transcendental_X (K := K)) =
      (RatFunc.algEquivOfTranscendental (jCoeff N K) (transcendental_jCoeff N K)).symm.toAlgHom := by
  apply coordinate_algHom_ext N K
  change coordinateSpecialization N K (RatFunc.transcendental_X (K := K))
      (AdjoinSimple.gen K (jCoeff N K)) =
    (RatFunc.algEquivOfTranscendental (jCoeff N K) (transcendental_jCoeff N K)).symm
      (AdjoinSimple.gen K (jCoeff N K))
  rw [coordinateSpecialization_gen, RatFunc.algEquivOfTranscendental_symm_gen]

variable [NeZero N] [IsAlgClosed K]

/-- The original integral modular polynomial is irreducible over the generic rational j-field. -/
theorem modularPolynomial_irreducible_ratFunc (hNK : (N : K) ≠ 0) :
    Irreducible (relationAtSeed (modularPolynomial N) (RatFunc.X : RatFunc K)) := by
  rw [← specialized_minpoly_eq_modularPolynomial N K hNK RatFunc.transcendental_X,
    coordinateSpecialization_ratFunc]
  exact (minpoly.irreducible (level_isIntegral N K)).map
    (Polynomial.mapEquiv
      (RatFunc.algEquivOfTranscendental (jCoeff N K) (transcendental_jCoeff N K)).symm.toRingEquiv)

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
