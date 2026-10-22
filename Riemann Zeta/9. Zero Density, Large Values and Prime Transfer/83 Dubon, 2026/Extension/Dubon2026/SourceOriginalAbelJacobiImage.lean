import Dubon2026.SourceOriginalLocalAbelJacobi
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> Jacobi inversion.
The actual image of degree-zero original divisors modulo actual loop
periods is an additive subgroup. Sums of local chart primitives belong
to that subgroup, represented by explicit differences of original places.
This is the algebraic image used by the local inverse-function argument.
Adapted from S_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Metric KaehlerDifferential
variable (N : ℕ) [NeZero N]

/-- Vectors represented by actual degree-zero divisors up to actual loop periods. -/
def abelJacobiImage {n : ℕ} (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) : AddSubgroup (Fin n → ℂ) where
  carrier := {x | ∃ D : Divisor ℂ (modularFunctionFieldOver N ℂ),
    Divisor.degree D = 0 ∧ abelJacobiDiv N b P₀ D - x ∈ pathPeriodLattice N b}
  zero_mem' := ⟨0, map_zero _, by simp⟩
  add_mem' := by
    rintro x y ⟨D₁, hD₁, hx⟩ ⟨D₂, hD₂, hy⟩
    refine ⟨D₁ + D₂, by rw [map_add, hD₁, hD₂, add_zero], ?_⟩
    rw [map_add]
    convert (pathPeriodLattice N b).add_mem hx hy using 1
    abel
  neg_mem' := by
    rintro x ⟨D, hD, hx⟩
    refine ⟨-D, by rw [map_neg, hD, neg_zero], ?_⟩
    rw [map_neg]
    convert (pathPeriodLattice N b).neg_mem hx using 1
    abel

theorem local_primitive_sum_mem_abelJacobiImage {n : ℕ}
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    {κ : Type*} [Fintype κ] (a : κ → Place ℂ (modularFunctionFieldOver N ℂ))
    (Φ : κ → Fin n → ℂ → ℂ)
    (hΦ : ∀ k i, ∀ z ∈ ball (0 : ℂ) (placeRadius N (a k)),
      HasDerivAt (Φ k i) (readDifferential N (a k) (b i) z) z)
    (w : κ → ℂ) (hw : ∀ k, w k ∈ ball 0 (placeRadius N (a k))) :
    (∑ k, fun i => Φ k i (w k) - Φ k i 0) ∈ abelJacobiImage N b P₀ := by
  classical
  have hr : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), Module.finrank ℂ v.ResidueField = 1 :=
    fun v => Module.finrank_of_bijective_algebraMap (original_place_residue_algebraMap_bijective N ℂ v)
  refine ⟨∑ k, (Finsupp.single (placeFamily N (a k) (w k)) 1 - Finsupp.single (a k) 1), ?_, ?_⟩
  · simp [map_sum, map_sub, Divisor.degree_single, hr]
  · have hAJ : abelJacobiDiv N b P₀
        (∑ k, (Finsupp.single (placeFamily N (a k) (w k)) 1 - Finsupp.single (a k) 1)) =
        ∑ k, (abelJacobiVec N b P₀ (placeFamily N (a k) (w k)) - abelJacobiVec N b P₀ (a k)) := by
      simp [map_sum, map_sub, abelJacobiDiv_single]
    rw [hAJ, ← Finset.sum_sub_distrib]
    exact (pathPeriodLattice N b).sum_mem fun k _ =>
      abelJacobiVec_chart_primitive N b hb P₀ (a k) (Φ k) (hΦ k) (hw k)

end
end Dubon2026.SourceFunctionField.OriginalChart
