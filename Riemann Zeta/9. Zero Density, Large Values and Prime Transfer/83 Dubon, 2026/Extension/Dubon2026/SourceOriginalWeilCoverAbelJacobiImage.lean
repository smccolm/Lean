import Dubon2026.SourceOriginalWeilCoverLocalAbelJacobi
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> auxiliary point division -> cover Jacobi inversion.
Adapt the native original-curve evaluation and inverse-function arguments
to the literal Kummer cover, using actual residue readings and Abel vectors.
Finite coordinate support replaces any numerical genus assumption.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Metric KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

/-- Vectors represented by actual degree-zero divisors up to actual loop periods. -/
def abelJacobiImage {kDim : ℕ} (b : Fin kDim → Ω[EE⁄ℂ])
    (P₀ : Place ℂ (EE)) : AddSubgroup (Fin kDim → ℂ) where
  carrier := {x | ∃ D : Divisor ℂ (EE),
    Divisor.degree D = 0 ∧ abelJacobiDiv N n r A hr hrA b P₀ D - x ∈ pathPeriodLattice N n r A hr hrA b}
  zero_mem' := ⟨0, map_zero _, by simp⟩
  add_mem' := by
    rintro x y ⟨D₁, hD₁, hx⟩ ⟨D₂, hD₂, hy⟩
    refine ⟨D₁ + D₂, by rw [map_add, hD₁, hD₂, add_zero], ?_⟩
    rw [map_add]
    convert (pathPeriodLattice N n r A hr hrA b).add_mem hx hy using 1
    abel
  neg_mem' := by
    rintro x ⟨D, hD, hx⟩
    refine ⟨-D, by rw [map_neg, hD, neg_zero], ?_⟩
    rw [map_neg]
    convert (pathPeriodLattice N n r A hr hrA b).neg_mem hx using 1
    abel

theorem local_primitive_sum_mem_abelJacobiImage {kDim : ℕ}
    (b : Fin kDim → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (EE))
    (P₀ : Place ℂ (EE))
    {κ : Type*} [Fintype κ] (a : κ → Place ℂ (EE))
    (Φ : κ → Fin kDim → ℂ → ℂ)
    (hΦ : ∀ k i, ∀ z ∈ ball (0 : ℂ) (placeRadius N n r A hr hrA (a k)),
      HasDerivAt (Φ k i) (readDifferential N n r A hr hrA (a k) (b i) z) z)
    (w : κ → ℂ) (hw : ∀ k, w k ∈ ball 0 (placeRadius N n r A hr hrA (a k))) :
    (∑ k, fun i => Φ k i (w k) - Φ k i 0) ∈ abelJacobiImage N n r A hr hrA b P₀ := by
  classical
  have hres : ∀ v : Place ℂ (EE), Module.finrank ℂ v.ResidueField = 1 :=
    fun v => Module.finrank_of_bijective_algebraMap (originalWeilKummerCover_residue_bijective N ℂ n r v)
  refine ⟨∑ k, (Finsupp.single (placeFamily N n r A hr hrA (a k) (w k)) 1 - Finsupp.single (a k) 1), ?_, ?_⟩
  · simp [map_sum, map_sub, Divisor.degree_single, hres]
  · have hAJ : abelJacobiDiv N n r A hr hrA b P₀
        (∑ k, (Finsupp.single (placeFamily N n r A hr hrA (a k) (w k)) 1 - Finsupp.single (a k) 1)) =
        ∑ k, (abelJacobiVec N n r A hr hrA b P₀ (placeFamily N n r A hr hrA (a k) (w k)) - abelJacobiVec N n r A hr hrA b P₀ (a k)) := by
      simp [map_sum, map_sub, abelJacobiDiv_single]
    rw [hAJ, ← Finset.sum_sub_distrib]
    exact (pathPeriodLattice N n r A hr hrA b).sum_mem fun k _ =>
      abelJacobiVec_chart_primitive N n r A hr hrA b hb P₀ (a k) (Φ k) (hΦ k) (hw k)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
