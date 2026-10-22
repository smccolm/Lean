import Dubon2026.SourceOriginalPathPrimitiveJumps
import Dubon2026.SourceOriginalCyclePeriodPolygonData
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! DUB-17/18 -> original Abel-Jacobi -> actual regular loop generators.
For a loop the two endpoint cell readings coincide. The proved path-to-jump
bridge therefore places its actual integral vector in the jump subgroup.
The proved word matrix then places it in the subgroup of the 2g constructed
loop periods. Native integer-span membership gives exact integer coefficients.
No topological generation or period-reduction premise is introduced.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*} [Finite κ]
local notation "F" => modularFunctionFieldOver N ℂ

theorem loop_period_mem_jumps (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J)
    (P : Place ℂ F) (δ : Path P P) :
    (fun i => pathIntegral N (η i) δ) ∈ AddSubgroup.closure (range J) := by
  choose g hg using fun i => exists_isPrimitiveAlong_of_coeff_mem N (η i) δ
    (fun t => (δ t).mem_of_ord_nonneg (hP.hη i (δ t)))
  have hm := path_sub_mem_closure_jumps D η V Ψ J hP hJ δ g hg
  simp only [sub_self, sub_zero] at hm
  have he : (fun i => pathIntegral N (η i) δ) = fun i => g i 1 - g i 0 := by
    funext i
    exact pathIntegral_eq_of_isPrimitiveAlong N (hg i)
  rw [he]
  exact hm

/-- Every actual regular loop period has common integer coefficients in the same complementary cycles. -/
def RegularCycleGeneration (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)) : Prop :=
  ∀ (P : Place ℂ F) (δ : Path P P), ∃ a : D.ιE → ℤ, ∀ i,
    pathIntegral N (η i) δ =
      ∑ l ∈ (T ∪ Ts)ᶜ, (a l : ℂ) * pathIntegral N (η i) (γ l)

theorem regular_cycle_generation_of_word (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (hP : PrimData D η V Ψ) (hJ : IsJump D Ψ J) (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hW : CyclePeriodPolygonConclusion D η T Ts J γ) :
    RegularCycleGeneration D η T Ts γ := by
  obtain ⟨_, _, _, _, _, _, hcl⟩ := hW
  intro P δ
  have hm := hcl (loop_period_mem_jumps D η V Ψ J hP hJ P δ)
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hm
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, fun i => ?_⟩
  have hi := congrFun ha i
  simpa only [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul] using hi.symm

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
