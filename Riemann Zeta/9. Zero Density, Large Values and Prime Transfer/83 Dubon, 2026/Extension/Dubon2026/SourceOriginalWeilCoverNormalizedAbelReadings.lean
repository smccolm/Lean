import Dubon2026.SourceOriginalWeilCoverPathPrimitiveJumps
import Dubon2026.SourceOriginalWeilCoverAbelJacobiPeriods
import Dubon2026.SourceOriginalWeilCoverRegularPathPrimitives

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse ->
third-kind reciprocity. Reuse the actual path-to-jump theorem and native
integer-span extraction. The chosen Abel paths give one common integer
period correction, and skew symmetry converts the weighted residue identity
to the exact Abel-divisor relation. No path comparison is assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders

open MeasureTheory

open scoped Real

open RadialDissectionPeriods
variable {kDim : ℕ}

theorem cover_abel_vector_eq_reading_add_periods :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀  (D : RadialCellDissection (Place ℂ EE))
    (η : Fin kDim → Ω[EE⁄ℂ]) (V : D.ιC → Set ℂ) (Ψ : Fin kDim → D.ιC → ℂ → ℂ)
    (J : D.ιE → Fin kDim → ℂ) (_ : CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ) (_ : IsJump D Ψ J)
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (_ : AddSubgroup.closure (range J) ≤ AddSubgroup.closure
      ((fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) '' ((T ∪ Ts)ᶜ : Finset D.ιE)))
    (P₀ : Place ℂ EE) (_ : gvec D Ψ P₀ (cellOf D P₀) = 0) (v : Place ℂ EE),
    ∃ a : D.ιE → ℤ, ∀ i,
      abelJacobiVec N n radicand baseDivisor hRadicand hOrders η P₀ v i = gvec D Ψ v (cellOf D v) i +
        ∑ l ∈ (T ∪ Ts)ᶜ, (a l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ T Ts γ hcl P₀ hzero v
  choose g hg using fun i => exists_isPrimitiveAlong_of_coeff_mem N n radicand baseDivisor hRadicand hOrders (η i) (coverPath N n radicand baseDivisor hRadicand hOrders P₀ v)
    (fun t => (mem_cover_regularDifferentials_iff N n radicand (η i)).mp (hP.2.2.2.2 i)
      (coverPath N n radicand baseDivisor hRadicand hOrders P₀ v t))
  have hm := hcl (cover_path_sub_mem_closure_jumps N n radicand baseDivisor hRadicand hOrders D η V Ψ J hP hJ (coverPath N n radicand baseDivisor hRadicand hOrders P₀ v) g hg)
  rw [hzero, sub_zero, ← Submodule.span_int_eq_addSubgroupClosure,
    Submodule.mem_toAddSubgroup, Submodule.mem_span_image_finset_iff_exists_fun'] at hm
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, fun i => ?_⟩
  have hi := congrFun ha i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply] at hi
  simp only [zsmul_eq_mul] at hi
  rw [abelJacobiVec, pathIntegral_eq_of_isPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (hg i)]
  linear_combination -hi


theorem cover_weighted_readings_eq_abel_add_periods :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀  (D : RadialCellDissection (Place ℂ EE))
    (η : Fin kDim → Ω[EE⁄ℂ]) (V : D.ιC → Set ℂ) (Ψ : Fin kDim → D.ιC → ℂ → ℂ)
    (J : D.ιE → Fin kDim → ℂ) (_ : CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ) (_ : IsJump D Ψ J)
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (_ : AddSubgroup.closure (range J) ≤ AddSubgroup.closure
      ((fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) '' ((T ∪ Ts)ᶜ : Finset D.ιE)))
    (P₀ : Place ℂ EE) (_ : gvec D Ψ P₀ (cellOf D P₀) = 0)
    (S : Finset (Place ℂ EE)) (E : Divisor ℂ EE) (_ : E.support ⊆ S),
    ∃ c : D.ιE → ℤ, ∀ i,
      (∑ v ∈ S, (E v : ℂ) * gvec D Ψ v (cellOf D v) i) =
        abelJacobiDiv N n radicand baseDivisor hRadicand hOrders η P₀ E i +
          ∑ l ∈ (T ∪ Ts)ᶜ, (c l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ T Ts γ hcl P₀ hzero S E hE
  classical
  choose a ha using cover_abel_vector_eq_reading_add_periods N n radicand baseDivisor hRadicand hOrders D η V Ψ J hP hJ T Ts γ hcl P₀ hzero
  refine ⟨fun l => -∑ v ∈ S, E v * a v l, fun i => ?_⟩
  have hAJ : abelJacobiDiv N n radicand baseDivisor hRadicand hOrders η P₀ E i = ∑ v ∈ S, (E v : ℂ) * abelJacobiVec N n radicand baseDivisor hRadicand hOrders η P₀ v i := by
    rw [abelJacobiDiv, Finsupp.liftAddHom_apply]
    simp only [zmultiplesHom_apply, Finsupp.sum, Finset.sum_apply]
    rw [Finset.sum_subset hE (f := fun v => (E v • abelJacobiVec N n radicand baseDivisor hRadicand hOrders η P₀ v) i)
      (fun v _ hv => by simp only [Finsupp.notMem_support_iff.1 hv, zero_smul, Pi.zero_apply])]
    apply Finset.sum_congr rfl
    intro v _
    simp only [Pi.smul_apply, zsmul_eq_mul]
  have hcor : (∑ l ∈ (T ∪ Ts)ᶜ, ((-∑ v ∈ S, E v * a v l : ℤ) : ℂ) *
      pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) =
      -(∑ v ∈ S, (E v : ℂ) * ∑ l ∈ (T ∪ Ts)ᶜ, (a v l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) := by
    simp only [Int.cast_neg, Int.cast_sum, Int.cast_mul]
    simp_rw [Finset.mul_sum, neg_mul, Finset.sum_mul]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    simp only [mul_assoc]
  rw [hAJ, hcor]
  simp_rw [ha, mul_add]
  rw [Finset.sum_add_distrib]
  ring

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
