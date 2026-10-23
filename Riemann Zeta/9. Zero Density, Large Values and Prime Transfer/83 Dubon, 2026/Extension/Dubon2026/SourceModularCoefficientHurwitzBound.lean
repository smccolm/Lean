import Dubon2026.SourceModularCoefficientHurwitzDivisor

/-! The actual coefficient-field Hurwitz inequalities used by the finite
and wild exceptional-fiber arguments for DUB-17/18. Effectivity and degree
are proved on the literal divisor of dj corrected by twice its pole divisor.
The only finite-set hypotheses identify regular points and poles; no genus
inequality or exceptional-fiber assertion is assumed. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- Finite differential orders and selected poles obey the actual Hurwitz bound. -/
theorem coeff_hurwitz_differential_bound
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS : ∀ v ∈ S, 0 ≤ v.ord (jCoeff N K))
    (P : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hP : ∀ v ∈ P, v.ord (jCoeff N K) < 0) :
    (∑ v ∈ S, v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K))) +
      (∑ v ∈ P, (-v.ord (jCoeff N K) - 1)) ≤
        2 * (genusFF K (modularFunctionFieldCoeff N K) : ℤ) - 2 +
          2 * (Module.finrank (IntermediateField.adjoin K {jCoeff N K})
            (modularFunctionFieldCoeff N K) : ℤ) := by
  classical
  have hdis : Disjoint S P := Finset.disjoint_left.mpr fun v hv hv' =>
    (not_lt_of_ge (hS v hv)) (hP v hv')
  have hs : ∀ v ∈ S,
      v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) ≤
        coeffHurwitzDivisor N K v := by
    intro v hv
    rw [coeffHurwitzDivisor_apply, max_eq_right (neg_nonpos.mpr (hS v hv)),
      mul_zero, add_zero]
  have hp : ∀ v ∈ P, -v.ord (jCoeff N K) - 1 ≤ coeffHurwitzDivisor N K v := by
    intro v hv
    rw [coeffHurwitzDivisor_apply, max_eq_left (neg_nonneg.mpr (hP v hv).le)]
    have hd := coeff_place_ord_j_sub_one_le_D_j N K v
    omega
  calc
    _ ≤ (∑ v ∈ S, coeffHurwitzDivisor N K v) +
        ∑ v ∈ P, coeffHurwitzDivisor N K v :=
      add_le_add (Finset.sum_le_sum hs) (Finset.sum_le_sum hp)
    _ = ∑ v ∈ S ∪ P, coeffHurwitzDivisor N K v := (Finset.sum_union hdis).symm
    _ ≤ Divisor.degree (coeffHurwitzDivisor N K) :=
      Divisor.sum_le_degree_of_nonneg _ (coeffHurwitzDivisor_nonneg N K)
        (fun v => Module.finrank_of_bijective_algebraMap
          (coeff_place_residue_algebraMap_bijective N K v)) _
    _ = _ := degree_coeffHurwitzDivisor N K

/-- Selected finite ramification orders and poles obey the same actual Hurwitz bound. -/
theorem coeff_hurwitz_ramification_bound
    (S : Finset (Place K (modularFunctionFieldCoeff N K)))
    (a : Place K (modularFunctionFieldCoeff N K) → K)
    (hS : ∀ v ∈ S, 0 < v.ord
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) (a v)))
    (P : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hP : ∀ v ∈ P, v.ord (jCoeff N K) < 0) :
    (∑ v ∈ S, (v.ord
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) (a v)) - 1)) +
      (∑ v ∈ P, (-v.ord (jCoeff N K) - 1)) ≤
        2 * (genusFF K (modularFunctionFieldCoeff N K) : ℤ) - 2 +
          2 * (Module.finrank (IntermediateField.adjoin K {jCoeff N K})
            (modularFunctionFieldCoeff N K) : ℤ) := by
  have hs : ∀ v ∈ S, 0 ≤ v.ord (jCoeff N K) := by
    intro v hv
    apply v.ord_nonneg_of_mem
    have hm := add_mem (v.mem_of_ord_nonneg (hS v hv).le) (v.algebraMap_mem' (a v))
    simpa only [sub_add_cancel] using hm
  refine le_trans ?_ (coeff_hurwitz_differential_bound N K S hs P hP)
  refine add_le_add ?_ le_rfl
  exact Finset.sum_le_sum fun v _ => coeff_place_ord_sub_one_le_D_j N K v (a v)

end Dubon2026.SourceFunctionField
