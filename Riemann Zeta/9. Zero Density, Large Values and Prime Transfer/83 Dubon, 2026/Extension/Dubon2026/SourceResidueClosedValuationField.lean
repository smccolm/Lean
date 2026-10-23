import Dubon2026.SourceResidueIntegralRelationTransfer
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.Polynomial.Lifts

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> actual
coefficient specialization. The residue field of a valuation ring in the
algebraically closed arithmetic constants is algebraically closed. Lift a monic
polynomial, take a root in the constants, and use native integral closedness
to put that root in the valuation ring. This discharges the closed-residue-field
input required by the already proved all-level degree theorem.
Adapted from the two corresponding ValuationSubring proofs in the archived
anthropics/fermats-last-theorem commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache-2.0. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem valuation_monic_root_integral {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) (f : Polynomial A) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    ∃ x : A, Polynomial.aeval (x : K) f = 0 := by
  have hdeg : (f.map (algebraMap A K)).degree ≠ 0 := by
    rw [hf.degree_map]
    intro h
    exact hd (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h.le)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap A K)) hdeg
  have hint : IsIntegral A x := by
    refine ⟨f, hf, ?_⟩
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  have hyx : (y : K) = x := hy
  rw [Polynomial.aeval_def, hyx]
  rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx

theorem valuation_residue_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) : IsAlgClosed (IsLocalRing.ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro p hmonic hirr
  have hlift : p ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => IsLocalRing.residue_surjective _
  obtain ⟨f, hmap, hdeg, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  have hd : f.natDegree ≠ 0 := by
    rw [Polynomial.natDegree_eq_of_degree_eq hdeg]
    exact hirr.natDegree_pos.ne'
  obtain ⟨x, hx⟩ := valuation_monic_root_integral A f hf hd
  refine ⟨IsLocalRing.residue A x, ?_⟩
  have hx0 : f.eval x = 0 := by
    have h1 : (algebraMap A K) (f.eval x) = 0 := by
      rw [← hx, Polynomial.aeval_def]
      exact (Polynomial.eval₂_at_apply (algebraMap A K) x).symm
    exact Subtype.coe_injective (by simpa using h1)
  rw [← hmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hx0, map_zero]

end
end Dubon2026.SourceFunctionField
