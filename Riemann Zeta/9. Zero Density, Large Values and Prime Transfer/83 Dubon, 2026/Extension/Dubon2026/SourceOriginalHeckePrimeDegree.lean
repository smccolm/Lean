import Dubon2026.SourceOriginalAllLevelDegree
import Dubon2026.SourceOriginalHeckeFinite
import Dubon2026.SourceCurvePicardCorrespondence

/-! DUB-17/18 -> actual Hecke norm -> complete embedding census.
Relative-degree multiplicativity and the already proved all-level j-map
degrees give the inclusion degree p+1. No new modular-polynomial degree
or Atkin-Lehner assumption is required for this count. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField SourceLevelProjective
variable (L : Type*) [Field L] [Algebra ℚ L]
variable (N p : ℕ) [NeZero N] [hp : Fact p.Prime]

theorem original_over_prime_relfinrank (hpN : ¬ p ∣ N) :
    relfinrank (modularFunctionFieldOver N L) (modularFunctionFieldOver (N * p) L) = p + 1 := by
  have hj : IntermediateField.adjoin L ({coeffEmb L jq} : Set (LaurentSeries L)) ≤
      modularFunctionFieldOver N L :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (coeffEmb_mem_laurentBaseChange L (jq_mem_full N)))
  have h := relfinrank_mul_relfinrank hj (original_over_mono_of_dvd L (dvd_mul_right N p))
  rw [← original_coordinate_finrank_eq_relfinrank,
    ← original_coordinate_finrank_eq_relfinrank,
    finrank_original_over_j_eq_psi, finrank_original_over_j_eq_psi,
    dedekindPsi_mul_prime_not_dvd hp.out hpN] at h
  exact Nat.eq_of_mul_eq_mul_left (dedekindPsi_pos (NeZero.ne N)) h

theorem originalHeckeAlpha_finrank (hpN : ¬ p ∣ N) :
    letI := SourceCurve.algebraAlong (originalHeckeAlpha L N p)
    Module.finrank (modularFunctionFieldOver N L) (modularFunctionFieldOver (N * p) L) = p + 1 := by
  letI := SourceCurve.algebraAlong (originalHeckeAlpha L N p)
  have h := original_over_prime_relfinrank L N p hpN
  rw [relfinrank_eq_finrank_of_le (original_over_mono_of_dvd L (dvd_mul_right N p))] at h
  exact h

end
end Dubon2026.SourceFunctionField
