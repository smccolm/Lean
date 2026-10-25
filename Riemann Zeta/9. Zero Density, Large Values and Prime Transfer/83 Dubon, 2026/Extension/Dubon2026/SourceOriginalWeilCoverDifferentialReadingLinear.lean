import Dubon2026.SourceOriginalWeilCoverLocalAbelJacobi

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
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

omit [NeZero n] A hr hrA in
theorem cover_differentialCoeff_sum_smul {kDim : ℕ}
    (v : Place ℂ (EE)) (c : Fin kDim → ℂ)
    (b : Fin kDim → Ω[EE⁄ℂ]) :
    v.differentialCoeff (∑ i, c i • b i) =
      ∑ i, algebraMap ℂ (EE) (c i) * v.differentialCoeff (b i) := by
  haveI := cover_place_dCoordGenerates N n r v
  haveI : Nontrivial Ω[EE⁄ℂ] :=
    cover_differentials_nontrivial N n r
  apply v.differentialCoeff_unique
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul, v.differentialCoeff_smul_dCoord, IsScalarTower.algebraMap_smul]

omit [NeZero n] A hr hrA in
theorem cover_eval_sum_mul_of_mem {kDim : ℕ}
    (w : Place ℂ (EE)) (c : Fin kDim → ℂ)
    (f : Fin kDim → EE) (hf : ∀ i, f i ∈ w.toValuationSubring) :
    w.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r w) (∑ i, algebraMap ℂ (EE) (c i) * f i) =
      ∑ i, c i * w.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n r w) (f i) := by
  let h : Fin kDim → w.toValuationSubring := fun i =>
    algebraMap ℂ w.toValuationSubring (c i) * ⟨f i, hf i⟩
  have he : ((∑ i, h i : w.toValuationSubring) : EE) =
      ∑ i, algebraMap ℂ (EE) (c i) * f i := by
    simp [h, w.coe_algebraMap]
  rw [← he, w.rationalEval_of_mem (originalWeilKummerCover_residue_bijective N ℂ n r w) (SetLike.coe_mem (∑ i, h i))]
  change w.rationalRegularEval (originalWeilKummerCover_residue_bijective N ℂ n r w) (∑ i, h i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [h]
  rw [map_mul, Place.rationalRegularEval_algebraMap,
    w.rationalEval_of_mem (originalWeilKummerCover_residue_bijective N ℂ n r w) (hf i)]

theorem readDifferential_sum_smul {kDim : ℕ}
    (v : Place ℂ (EE)) (c : Fin kDim → ℂ)
    (b : Fin kDim → Ω[EE⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (EE))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N n r A hr hrA v)) :
    readDifferential N n r A hr hrA v (∑ i, c i • b i) z = ∑ i, c i * readDifferential N n r A hr hrA v (b i) z := by
  simp only [readDifferential_eq_coefficient N n r A hr hrA v _ hz, chartRead,
    cover_differentialCoeff_sum_smul]
  exact cover_eval_sum_mul_of_mem N n r (placeFamily N n r A hr hrA v z) c
    (fun i => v.differentialCoeff (b i)) (fun i => chart_differentialCoeff_regular N n r A hr hrA v (b i) (hb i) hz)


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
