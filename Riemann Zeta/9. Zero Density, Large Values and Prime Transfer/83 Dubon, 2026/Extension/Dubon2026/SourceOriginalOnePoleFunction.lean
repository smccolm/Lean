import Dubon2026.SourceOriginalGlobalIndex
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> original torsion cardinality -> connected complex curve.
The proved original index formula gives a nonconstant function regular
away from any specified original place. Only the inequality ell(D) >= 2
is needed, so no new Riemann-Roch or canonical-divisor construction is used.
This is the algebraic input to the compact maximum-modulus argument.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]

theorem exists_original_nonconstant_regular_away
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ f : modularFunctionFieldOver N ℂ,
      f ∉ Set.range (algebraMap ℂ (modularFunctionFieldOver N ℂ)) ∧
      ∀ w : Place ℂ (modularFunctionFieldOver N ℂ), w ≠ v → f ∈ w.toValuationSubring := by
  classical
  let g := indexOfSpecialty (0 : Divisor ℂ (modularFunctionFieldOver N ℂ))
  let D : Divisor ℂ (modularFunctionFieldOver N ℂ) := Finsupp.single v ((g : ℤ) + 1)
  have hdeg : Divisor.degree D = (g : ℤ) + 1 := by
    have hr := Module.finrank_of_bijective_algebraMap
      (original_place_residue_algebraMap_bijective N ℂ v)
    rw [Divisor.degree_single, hr, Nat.cast_one, mul_one]
  have hell : (2 : ℤ) ≤ ell D := by
    have h := original_index_formula N ℂ D
    rw [hdeg] at h
    change (ell D : ℤ) - indexOfSpecialty D = (g : ℤ) + 1 + 1 - g at h
    omega
  have hnot : ¬((LSpace D : Set (modularFunctionFieldOver N ℂ)) ⊆
      Set.range (algebraMap ℂ (modularFunctionFieldOver N ℂ))) := by
    intro hle
    have hle' : LSpace D ≤ LinearMap.range (Algebra.linearMap ℂ (modularFunctionFieldOver N ℂ)) := by
      intro f hf
      obtain ⟨c, hc⟩ := hle hf
      exact ⟨c, hc⟩
    haveI := Module.Finite.range (Algebra.linearMap ℂ (modularFunctionFieldOver N ℂ))
    have h1 := Submodule.finrank_mono hle'
    have h2 : Module.finrank ℂ (LinearMap.range (Algebra.linearMap ℂ (modularFunctionFieldOver N ℂ))) ≤ 1 := by
      simpa using LinearMap.finrank_range_le (Algebra.linearMap ℂ (modularFunctionFieldOver N ℂ))
    have h3 : ell D ≤ 1 := h1.trans h2
    omega
  obtain ⟨f, hf, hfc⟩ := Set.not_subset.mp hnot
  refine ⟨f, hfc, fun w hw => ?_⟩
  have hf0 : f ≠ 0 := fun h => hfc ⟨0, by simpa only [map_zero] using h.symm⟩
  have ho := (mem_lSpace_iff_ord.mp hf).resolve_left hf0 w
  have hDw : D w = 0 := by
    change Finsupp.single v ((g : ℤ) + 1) w = 0
    rw [Finsupp.single_apply, if_neg (Ne.symm hw)]
  apply w.mem_of_ord_nonneg
  simpa only [hDw, neg_zero] using ho

end
end Dubon2026.SourceFunctionField
