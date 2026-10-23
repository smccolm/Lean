import Dubon2026.SourceCurveCompletionNorm

/-! Original integral elements represent every residue class after
completion. This is the bridge allowing the original modular local residue
calculation to use the proved completed integral basis. The proof reuses
native completion density, with no compactness or number-field hypothesis. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open IsDedekindDomain
open scoped Valued

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Every completed integral element is congruent modulo the maximal ideal to an original one. -/
theorem completion_integer_approximation (x : v.adicCompletionIntegers) :
    ∃ a : v.toValuationSubring,
      Valued.v ((x : v.adicCompletion) - algebraMap v.toValuationSubring v.adicCompletion a) < 1 := by
  letI := v.completionRankOne
  obtain ⟨y, hy⟩ := (v.heightOneSpectrum.denseRange_algebraMap F).exists_dist_lt
    (x : v.adicCompletion) zero_lt_one
  have hxy : Valued.v ((x : v.adicCompletion) - algebraMap F v.adicCompletion y) < 1 := by
    rw [← Valued.toNormedField.norm_lt_one_iff]
    simpa only [dist_eq_norm] using hy
  have hyint : algebraMap F v.adicCompletion y ∈ v.adicCompletionIntegers := by
    change Valued.v (algebraMap F v.adicCompletion y) ≤ 1
    rw [show algebraMap F v.adicCompletion y = (x : v.adicCompletion) -
      ((x : v.adicCompletion) - algebraMap F v.adicCompletion y) by ring]
    exact Valued.v.map_sub_le x.2 hxy.le
  exact ⟨⟨y, (v.completion_integer_iff y).mp hyint⟩, hxy⟩

/-- A difference of valuation less than one gives equal residues in the actual completion. -/
theorem completion_residue_eq_of_sub_lt_one (x y : v.adicCompletionIntegers)
    (h : Valued.v ((x : v.adicCompletion) - (y : v.adicCompletion)) < 1) :
    IsLocalRing.residue v.adicCompletionIntegers x = IsLocalRing.residue v.adicCompletionIntegers y := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit (x - y)
  intro hu
  exact h.ne ((HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    (v := v.heightOneSpectrum) (K := F) (a := x - y)).mp hu)

/-- The original integral ring surjects onto the residue field of its actual completion. -/
theorem completion_integral_residue_surjective : Function.Surjective
    ((IsLocalRing.residue v.adicCompletionIntegers).comp
      (algebraMap v.toValuationSubring v.adicCompletionIntegers)) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers) z
  obtain ⟨a, ha⟩ := v.completion_integer_approximation x
  exact ⟨a, (v.completion_residue_eq_of_sub_lt_one x
    (algebraMap v.toValuationSubring v.adicCompletionIntegers a) ha).symm⟩

end Dubon2026.SourceCurve.Place
