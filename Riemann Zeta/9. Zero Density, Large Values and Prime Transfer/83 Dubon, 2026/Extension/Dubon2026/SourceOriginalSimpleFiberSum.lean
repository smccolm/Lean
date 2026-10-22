import Dubon2026.SourceOriginalSimpleFiberResidues
import Dubon2026.SourceOriginalPlaceEvaluation
import Dubon2026.SourceOriginalGlobalResidues

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> local constancy along fibers. The sum of the coefficient
of an original regular differential over any simple fiber is zero.
The existing original global residue theorem and the proved simple-zero
residue identity discharge the algebraic input to the analytic fiber sum.
No global residue theorem, rational-residue identification or local
simple-zero calculation is supplied as an assumption.
Adapted from S_AlgebraicCurve_sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]

theorem original_trace_residue_eq_eval
    (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (h : modularFunctionFieldOver N ℂ) (hh : h ∈ v.toValuationSubring) :
    Algebra.trace ℂ v.ResidueField (IsLocalRing.residue v.toValuationSubring ⟨h, hh⟩) =
      originalPlaceEval N ℂ v h := by
  have he : algebraMap ℂ v.ResidueField (originalPlaceEval N ℂ v h) =
      IsLocalRing.residue v.toValuationSubring ⟨h, hh⟩ := by
    rw [originalPlaceEval_of_mem N ℂ v hh]
    exact (originalPlaceResidueEquiv N ℂ v).apply_symm_apply _
  rw [← he, Algebra.trace_algebraMap,
    Module.finrank_of_bijective_algebraMap (original_place_residue_algebraMap_bijective N ℂ v), one_smul]

theorem original_sum_simple_fiber_eq_zero
    (f h : modularFunctionFieldOver N ℂ)
    (hω : h • D ℂ (modularFunctionFieldOver N ℂ) f ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) (t : ℂ)
    (hsimple : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ),
      0 < v.ord (f - algebraMap ℂ (modularFunctionFieldOver N ℂ) t) →
        v.ord (f - algebraMap ℂ (modularFunctionFieldOver N ℂ) t) = 1)
    (Z : Finset (Place ℂ (modularFunctionFieldOver N ℂ)))
    (hZ : ∀ v, v ∈ Z ↔ 0 < v.ord (f - algebraMap ℂ (modularFunctionFieldOver N ℂ) t)) :
    ∑ v ∈ Z, originalPlaceEval N ℂ v h = 0 := by
  classical
  let g := f - algebraMap ℂ (modularFunctionFieldOver N ℂ) t
  have hDg : D ℂ (modularFunctionFieldOver N ℂ) g = D ℂ (modularFunctionFieldOver N ℂ) f := by
    simp only [g, map_sub, Derivation.map_algebraMap, sub_zero]
  let T : Place ℂ (modularFunctionFieldOver N ℂ) → ℂ := fun v =>
    Algebra.trace ℂ v.ResidueField ((originalCanonicalLocalResidueData N ℂ v).res
      (g⁻¹ * v.differentialCoeff (h • D ℂ (modularFunctionFieldOver N ℂ) f)))
  have hsum : ∑ᶠ v, T v = 0 :=
    original_global_residue_sum_zero N ℂ (h • D ℂ (modularFunctionFieldOver N ℂ) f) g⁻¹
  have hout : ∀ v, v ∉ Z → T v = 0 := by
    intro v hv
    have hord : v.ord g ≤ 0 := le_of_not_gt (fun hp => hv ((hZ v).mpr hp))
    have hmem : g⁻¹ * v.differentialCoeff (h • D ℂ (modularFunctionFieldOver N ℂ) f) ∈
        v.toValuationSubring :=
      mul_mem (v.mem_of_ord_nonneg (by rw [v.ord_inv]; omega))
        ((mem_original_regularDifferentials_iff N ℂ _).mp hω v)
    simp only [T, (originalCanonicalLocalResidueData N ℂ v).res_of_mem _ hmem, map_zero]
  have hin : ∀ v ∈ Z, T v = originalPlaceEval N ℂ v h := by
    intro v hv
    obtain ⟨hh, hr⟩ := original_simple_zero_residue N v g h (hsimple v ((hZ v).mp hv))
      (by rw [hDg]; exact hω)
    rw [hDg] at hr
    change Algebra.trace ℂ v.ResidueField
      ((originalCanonicalLocalResidueData N ℂ v).res
        (g⁻¹ * v.differentialCoeff (h • D ℂ (modularFunctionFieldOver N ℂ) f))) = _
    rw [hr, original_trace_residue_eq_eval N v h hh]
  have hsupp : Function.support T ⊆ (Z : Set (Place ℂ (modularFunctionFieldOver N ℂ))) := by
    intro v hv
    by_contra hn
    exact hv (hout v hn)
  rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum
  exact (Finset.sum_congr rfl fun v hv => (hin v hv).symm).trans hsum

end
end Dubon2026.SourceFunctionField
