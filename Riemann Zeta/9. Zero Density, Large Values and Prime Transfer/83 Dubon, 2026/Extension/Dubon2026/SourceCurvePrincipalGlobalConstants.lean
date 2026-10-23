import Dubon2026.SourceCurveWeilRankOne
import Dubon2026.SourceCurveLSpaceFiniteStep
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> actual modular good reduction -> genus comparison.
Global regular functions are constants over closed constants in every
characteristic. Reuse the existing negative-degree vanishing and single-place
dimension increment, rather than extending the characteristic-zero coordinate
argument to inseparable coordinates. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasPrincipalDivisors K F]
variable [∀ v : Place K F, Module.Finite K v.ResidueField]

theorem finite_lSpace_zero_of_place (P : Place K F) :
    Module.Finite K (LSpace (0 : Divisor K F)) := by
  have hdeg : Divisor.degree (0 - Finsupp.single P 1) < 0 := by
    rw [zero_sub, map_neg, Divisor.degree_single, one_mul]
    exact neg_neg_of_pos (by exact_mod_cast (Module.finrank_pos (R := K) (M := P.ResidueField)))
  haveI : Module.Finite K (LSpace (0 - Finsupp.single P 1)) := by
    rw [lSpace_eq_bot_of_degree_neg hdeg]
    infer_instance
  exact finite_lSpace_of_sub_single 0 P

theorem lSpace_zero_eq_range_of_principalDivisors [IsAlgClosed K] (P : Place K F) :
    LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := by
  classical
  haveI := finite_lSpace_zero_of_place P
  have hres : Module.finrank K P.ResidueField = 1 := by
    exact (LinearEquiv.finrank_eq (AlgEquiv.ofBijective (Algebra.ofId K P.ResidueField)
      IsAlgClosed.algebraMap_bijective_of_isIntegral).toLinearEquiv).symm.trans
        (Module.finrank_self K)
  have hdeg : Divisor.degree (-Finsupp.single P 1) = -1 := by
    rw [map_neg, Divisor.degree_single, one_mul, hres, Nat.cast_one]
  have hle : (-Finsupp.single P 1 : Divisor K F) ≤ 0 := by
    intro v
    simp only [Finsupp.neg_apply, Finsupp.zero_apply, neg_nonpos]
    exact Finsupp.single_nonneg.mpr (by omega) v
  have hdim := ell_sub_ell_le_degree_sub_degree hle
  rw [ell_eq_zero_of_degree_neg (D := -Finsupp.single P 1)
    (by rw [hdeg]; omega), map_zero, hdeg] at hdim
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_le
  · rintro f ⟨c, rfl⟩
    exact algebraMap_mem_lSpace_zero c
  · rw [LinearMap.finrank_range_of_inj (f := Algebra.linearMap K F)
      (algebraMap K F).injective, Module.finrank_self]
    change ell (0 : Divisor K F) ≤ 1
    omega

theorem finrank_lSpace_zero_of_principalDivisors [IsAlgClosed K] (P : Place K F) :
    Module.finrank K (LSpace (0 : Divisor K F)) = 1 := by
  rw [lSpace_zero_eq_range_of_principalDivisors P,
    LinearMap.finrank_range_of_inj (f := Algebra.linearMap K F)
      (algebraMap K F).injective, Module.finrank_self]

end
end Dubon2026.SourceCurve
