import Dubon2026.SourceModularCoefficientModularRoots
import Dubon2026.SourceModularCoefficientSeparability

/-! Reuse the original coefficient field's proved separability and exact
minimal-polynomial identification at every level. Specialization at a
transcendental j preserves separability and gives exactly psi(N) distinct
roots. These are the generic root-count inputs to the actual cyclic quotient
bijection on the DUB-17/18 inertia-census chain; the bijection is still required. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial IntermediateField CoefficientPresentation
open scoped IntermediateField
noncomputable section

/-- The exact integral modular polynomial is separable at every transcendental j and invertible level. -/
theorem modularPolynomial_separable_transcendental
    {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0) (j : L) (hj : Transcendental K j) :
    (relationAtSeed (modularPolynomial N) j).Separable := by
  letI := isSeparable_coeff_field N K
  rw [← specialized_minpoly_eq_modularPolynomial N K hNK hj]
  have hs : (minpoly K⟮jCoeff N K⟯ (jN N K)).Separable :=
    Algebra.IsSeparable.isSeparable K⟮jCoeff N K⟯ (jN N K)
  exact hs.map

/-- The generic modular fiber has exactly psi(N) distinct roots, with separability derived from the actual field. -/
theorem modularPolynomial_root_card_transcendental
    {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [IsAlgClosed L] [Algebra K L]
    (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0) (j : L) (hj : Transcendental K j) :
    Nat.card {x : L // (relationAtSeed (modularPolynomial N) j).IsRoot x} =
      SourceLevelProjective.dedekindPsi N := by
  classical
  let P := relationAtSeed (modularPolynomial N) j
  have hm : P.Monic := (modularPolynomial_monic N).map _
  have he : {x : L | P.IsRoot x} = P.rootSet L := by
    ext x
    simp [hm.mem_rootSet, Polynomial.aeval_def, Algebra.algebraMap_self, IsRoot.def]
  change Nat.card {x : L // x ∈ {x : L | P.IsRoot x}} = _
  rw [he, Nat.card_eq_fintype_card]
  rw [card_rootSet_eq_natDegree (modularPolynomial_separable_transcendental N hNK j hj)
    (IsAlgClosed.splits _)]
  exact (modularPolynomial_monic N).natDegree_map _ |>.trans (modularPolynomial_natDegree N)

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
