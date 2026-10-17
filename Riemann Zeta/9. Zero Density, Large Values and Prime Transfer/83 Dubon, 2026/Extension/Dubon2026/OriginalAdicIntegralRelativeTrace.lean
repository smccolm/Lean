import Dubon2026.OriginalInvariantAbelianTrace
import Dubon2026.OriginalAdicUnitCohomology

/-! # Integral units remain integral under the actual relative trace

All original completed Galois transports preserve valuation. Their
finite quotient product therefore preserves integral units. This keeps
the norm-adjusted inertia representatives inside the local unit image
required by DUB-17's prescribed-support norm-field argument.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField BigOperators
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))
  [Fintype (OriginalFiniteDecompositionGroup K L w)]
  (S : Subgroup (OriginalFiniteDecompositionGroup K L w))
  [S.Normal] [Fintype S] [Fintype (OriginalFiniteDecompositionGroup K L w ⧸ S)]

omit [Fintype (OriginalFiniteDecompositionGroup K L w)] [Fintype S] in
/-- The actual relative trace of an invariant integral unit is an
integral unit in the same original completion. -/
theorem originalAdicUnit_relativeTrace_integral
    (x : (originalAdicUnitRep K L w).quotientToInvariants S)
    (hx : x.val.toMul ∈ (w.adicCompletionIntegers L).units) :
    (originalInvariantRelativeTrace (originalAdicUnitRep K L w) S x).val.toMul ∈
      (w.adicCompletionIntegers L).units := by
  have hv := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hx
  apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
  have ht : (originalInvariantRelativeTrace (originalAdicUnitRep K L w) S x).val =
      ∑ q : OriginalFiniteDecompositionGroup K L w ⧸ S,
        (originalAdicUnitRep K L w).ρ q.out x.val := by
    simp only [originalInvariantRelativeTrace, Representation.norm, LinearMap.sum_apply,
      Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro q _
    exact originalQuotientInvariant_action_out (originalAdicUnitRep K L w) S q x
  rw [ht]
  change Valued.v ((∏ q : OriginalFiniteDecompositionGroup K L w ⧸ S,
    (show (w.adicCompletion L)ˣ from
      ((originalAdicUnitRep K L w).ρ q.out x.val).toMul)).val) = 1
  rw [Units.coe_prod, map_prod]
  apply Finset.prod_eq_one
  intro q _
  exact (numberFieldGaloisLocalTransport_valuation K L q.out.val w w
    q.out.property x.val.toMul.val).trans hv

end
end Dubon2026
