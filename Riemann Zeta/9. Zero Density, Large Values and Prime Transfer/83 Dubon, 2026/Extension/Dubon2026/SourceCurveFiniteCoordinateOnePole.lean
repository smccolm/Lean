import Dubon2026.SourceCurveFiniteCoordinateGenusMaximum
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> auxiliary connectedness -> a function with one possible pole.
Reuse the finite-coordinate degree-dimension maximum directly: its bound
already gives a divisor space of dimension at least two. No new global
index formula is needed. The dimension-versus-constants argument adapts
SourceOriginalOnePoleFunction, originally adapted from the Apache-2.0 FLT
source at commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
variable {K F : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F]

theorem exists_nonconstant_regular_away_of_finite_coordinate
    (ht : Transcendental K t) (v : Place K F) :
    ∃ a : F, a ∉ Set.range (algebraMap K F) ∧
      ∀ w : Place K F, w ≠ v → a ∈ w.toValuationSubring := by
  classical
  obtain ⟨γ, D₀, hmax⟩ := finite_coordinate_degree_dimension_maximum t ht
  let D : Divisor K F := Finsupp.single v (γ + 1)
  have hdeg : Divisor.degree D = γ + 1 := by
    have hr := Module.finrank_of_bijective_algebraMap
      (place_residue_bijective_of_finite_coordinate t v)
    rw [Divisor.degree_single, hr, Nat.cast_one, mul_one]
  have hell : (2 : ℤ) ≤ ell D := by
    have h := hmax.isMax D
    rw [hdeg] at h
    omega
  have hnot : ¬((LSpace D : Set F) ⊆ Set.range (algebraMap K F)) := by
    intro hle
    have hle' : LSpace D ≤ LinearMap.range (Algebra.linearMap K F) := by
      intro a ha
      obtain ⟨c, hc⟩ := hle ha
      exact ⟨c, hc⟩
    haveI := Module.Finite.range (Algebra.linearMap K F)
    have h1 := Submodule.finrank_mono hle'
    have h2 : Module.finrank K (LinearMap.range (Algebra.linearMap K F)) ≤ 1 := by
      simpa using LinearMap.finrank_range_le (Algebra.linearMap K F)
    have h3 : ell D ≤ 1 := h1.trans h2
    omega
  obtain ⟨a, ha, hac⟩ := Set.not_subset.mp hnot
  refine ⟨a, hac, fun w hw => ?_⟩
  have ha0 : a ≠ 0 := fun h => hac ⟨0, by simpa only [map_zero] using h.symm⟩
  have ho := (mem_lSpace_iff_ord.mp ha).resolve_left ha0 w
  have hDw : D w = 0 := by
    change Finsupp.single v (γ + 1) w = 0
    rw [Finsupp.single_apply, if_neg (Ne.symm hw)]
  apply w.mem_of_ord_nonneg
  simpa only [hDw, neg_zero] using ho

end
end Dubon2026.SourceCurve
