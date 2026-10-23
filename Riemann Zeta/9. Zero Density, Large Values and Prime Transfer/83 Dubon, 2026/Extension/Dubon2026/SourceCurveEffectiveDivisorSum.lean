import Dubon2026.SourceCurveDivisorDegree

/-! The finite contribution of rational places to an effective divisor
is bounded by its actual degree. This is the finite-sum step for the
modular Hurwitz bound on the DUB-17/18 reverse-genus path. -/

noncomputable section

namespace Dubon2026.SourceCurve.Divisor

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Every finite sum of coefficients of an effective rational-place divisor is bounded by degree. -/
theorem sum_le_degree_of_nonneg (D : Divisor K F) (hD : ∀ v, 0 ≤ D v)
    (hres : ∀ v : Place K F, Module.finrank K v.ResidueField = 1)
    (S : Finset (Place K F)) : ∑ v ∈ S, D v ≤ degree D := by
  classical
  rw [degree_eq_sum_support]
  simp only [hres, Nat.cast_one, mul_one]
  calc
    _ ≤ ∑ v ∈ S ∪ D.support, D v :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun v _ _ => hD v)
    _ = ∑ v ∈ D.support, D v := by
      symm
      exact Finset.sum_subset Finset.subset_union_right
        (fun v _ hv => Finsupp.notMem_support_iff.mp hv)

end Dubon2026.SourceCurve.Divisor
