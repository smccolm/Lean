import TaoTrudgianYang2025.FiniteSignSamples
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Actual coefficient control and linear evaluation of finite sign samples. -/

namespace TaoTrudgianYang2025

theorem finiteSignSamples_norm_le {E : Type*} [NormedAddCommGroup E]
    (v : List E) {a : E} (ha : a ∈ finiteSignSamples v) :
    ‖a‖ ≤ (v.map norm).sum := by
  induction v generalizing a with
  | nil =>
    have he : a = 0 := by simpa only [finiteSignSamples,List.mem_singleton] using ha
    simp only [he,norm_zero,List.map_nil,List.sum_nil,le_refl]
  | cons z v ih =>
    simp only [finiteSignSamples,List.mem_append,List.mem_map] at ha
    rcases ha with ⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩
    · simp only [List.map_cons,List.sum_cons]
      have h := ih hw
      linarith [norm_add_le w z]
    · simp only [List.map_cons,List.sum_cons]
      have h := ih hw
      linarith [norm_sub_le w z]

theorem finiteSignSamples_apply_norm_le {ι : Type*}
    (v : List (ι → ℂ)) {a : ι → ℂ} (ha : a ∈ finiteSignSamples v) (i : ι) :
    ‖a i‖ ≤ (v.map (fun b => ‖b i‖)).sum := by
  let f : (ι → ℂ) →+ ℂ :=
    { toFun := fun b => b i
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hm : f a ∈ finiteSignSamples (v.map f) := by
    rw [← finiteSignSamples_map]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
  simpa only [List.map_map,Function.comp_def] using finiteSignSamples_norm_le (v.map f) hm

end TaoTrudgianYang2025
