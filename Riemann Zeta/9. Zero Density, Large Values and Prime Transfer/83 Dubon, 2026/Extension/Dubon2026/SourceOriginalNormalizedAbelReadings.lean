import Dubon2026.SourceOriginalRegularLoopJumpClosure
import Dubon2026.SourceOriginalAbelJacobiPeriods

/-! DUB-17/18 -> original Abel-Jacobi -> raw residue reciprocity.
Use the original chosen Abel path in the proved path-to-jump theorem. After
normalization at the base point, native integer-span extraction compares the
actual Abel vector and the same cell readings used by weighted reciprocity.
No new path existence or Abel-map compatibility assumption is introduced.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem abel_vector_eq_reading_add_periods {n : ℕ} (D : CellDissection N)
    (η : Fin n → Ω[F⁄ℂ]) (V : D.ιC → Set ℂ) (Ψ : Fin n → D.ιC → ℂ → ℂ)
    (J : D.ιE → Fin n → ℂ) (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J)
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hcl : AddSubgroup.closure (range J) ≤ AddSubgroup.closure
      ((fun l i => pathIntegral N (η i) (γ l)) '' ((T ∪ Ts)ᶜ : Finset D.ιE)))
    (P₀ : Place ℂ F) (hzero : gvec D Ψ P₀ (cellOf D P₀) = 0) (v : Place ℂ F) :
    ∃ a : D.ιE → ℤ, ∀ i,
      abelJacobiVec N η P₀ v i = gvec D Ψ v (cellOf D v) i +
        ∑ l ∈ (T ∪ Ts)ᶜ, (a l : ℂ) * pathIntegral N (η i) (γ l) := by
  choose g hg using fun i => exists_isPrimitiveAlong_of_coeff_mem N (η i) (originalPath N P₀ v)
    (fun t => (originalPath N P₀ v t).mem_of_ord_nonneg (hP.hη i _))
  have hm := hcl (path_sub_mem_closure_jumps D η V Ψ J hP hJ (originalPath N P₀ v) g hg)
  rw [hzero, sub_zero, ← Submodule.span_int_eq_addSubgroupClosure,
    Submodule.mem_toAddSubgroup, Submodule.mem_span_image_finset_iff_exists_fun'] at hm
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, fun i => ?_⟩
  have hi := congrFun ha i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply] at hi
  simp only [zsmul_eq_mul] at hi
  rw [abelJacobiVec, pathIntegral_eq_of_isPrimitiveAlong N (hg i)]
  linear_combination -hi

theorem weighted_readings_eq_abel_add_periods {n : ℕ} (D : CellDissection N)
    (η : Fin n → Ω[F⁄ℂ]) (V : D.ιC → Set ℂ) (Ψ : Fin n → D.ιC → ℂ → ℂ)
    (J : D.ιE → Fin n → ℂ) (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J)
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hcl : AddSubgroup.closure (range J) ≤ AddSubgroup.closure
      ((fun l i => pathIntegral N (η i) (γ l)) '' ((T ∪ Ts)ᶜ : Finset D.ιE)))
    (P₀ : Place ℂ F) (hzero : gvec D Ψ P₀ (cellOf D P₀) = 0)
    (S : Finset (Place ℂ F)) (E : Divisor ℂ F) (hE : E.support ⊆ S) :
    ∃ c : D.ιE → ℤ, ∀ i,
      (∑ v ∈ S, (E v : ℂ) * gvec D Ψ v (cellOf D v) i) =
        abelJacobiDiv N η P₀ E i +
          ∑ l ∈ (T ∪ Ts)ᶜ, (c l : ℂ) * pathIntegral N (η i) (γ l) := by
  classical
  choose a ha using abel_vector_eq_reading_add_periods D η V Ψ J hP hJ T Ts γ hcl P₀ hzero
  refine ⟨fun l => -∑ v ∈ S, E v * a v l, fun i => ?_⟩
  have hAJ : abelJacobiDiv N η P₀ E i = ∑ v ∈ S, (E v : ℂ) * abelJacobiVec N η P₀ v i := by
    rw [abelJacobiDiv_apply, Finsupp.sum, Finset.sum_apply]
    rw [Finset.sum_subset hE (f := fun v => (E v • abelJacobiVec N η P₀ v) i)
      (fun v _ hv => by simp only [Finsupp.notMem_support_iff.1 hv, zero_smul, Pi.zero_apply])]
    apply Finset.sum_congr rfl
    intro v _
    simp only [Pi.smul_apply, zsmul_eq_mul]
  have hcor : (∑ l ∈ (T ∪ Ts)ᶜ, ((-∑ v ∈ S, E v * a v l : ℤ) : ℂ) *
      pathIntegral N (η i) (γ l)) =
      -(∑ v ∈ S, (E v : ℂ) * ∑ l ∈ (T ∪ Ts)ᶜ, (a v l : ℂ) * pathIntegral N (η i) (γ l)) := by
    simp only [Int.cast_neg, Int.cast_sum, Int.cast_mul]
    simp_rw [Finset.mul_sum, neg_mul, Finset.sum_mul]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    simp only [mul_assoc]
  rw [hAJ, hcor]
  simp_rw [ha, mul_add]
  rw [Finset.sum_add_distrib]
  ring

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
