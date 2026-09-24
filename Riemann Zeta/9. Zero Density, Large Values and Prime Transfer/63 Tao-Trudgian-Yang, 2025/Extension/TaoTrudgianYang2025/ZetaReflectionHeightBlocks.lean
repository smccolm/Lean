import TaoTrudgianYang2025.ZetaReflectionFiniteCover

/-! Three literal positive dyadic height windows for the reflected family. -/

noncomputable section
open Complex MeasureTheory Set
open scoped Classical BigOperators
namespace TaoTrudgianYang2025

def reflectionHeightScale (T : ℝ) (i : Fin 3) : ℝ := T/2*(2 : ℝ)^i.val

theorem reflectionHeightScale_pos {T : ℝ} (hT : 0 < T) (i : Fin 3) :
    0 < reflectionHeightScale T i := by
  unfold reflectionHeightScale
  positivity

theorem reflectionHeightScale_bounds {T : ℝ} (hT : 0 < T) (i : Fin 3) :
    T/2 ≤ reflectionHeightScale T i ∧ reflectionHeightScale T i ≤ 2*T := by
  constructor <;> fin_cases i <;> norm_num [reflectionHeightScale] <;> linarith

theorem reflectionHeightScale_cover {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc (T/2) (3*T)) :
    ∃ i : Fin 3, t ∈ Icc (reflectionHeightScale T i) (2*reflectionHeightScale T i) := by
  by_cases hlow : t ≤ T
  · refine ⟨0,?_⟩
    norm_num [reflectionHeightScale]
    exact ⟨ht.1,by linarith⟩
  · by_cases hmid : t ≤ 2*T
    · refine ⟨1,?_⟩
      norm_num [reflectionHeightScale]
      constructor <;> linarith
    · refine ⟨2,?_⟩
      norm_num [reflectionHeightScale]
      constructor <;> linarith [ht.2]

theorem exists_reflection_height_family {T : ℝ} (hT : 0 < T)
    (W : Finset ℝ) (hW : W.Nonempty) (hheight : ∀ t ∈ W, t ∈ Icc (T/2) (3*T)) :
    ∃ i : Fin 3, ∃ U : Finset ℝ, U.Nonempty ∧ U ⊆ W ∧
      (W.card : ℝ)/3 ≤ (U.card : ℝ) ∧
      ∀ t ∈ U, t ∈ Icc (reflectionHeightScale T i) (2*reflectionHeightScale T i) := by
  exact exists_reflection_three_cover W hW
    (fun i t => t ∈ Icc (reflectionHeightScale T i) (2*reflectionHeightScale T i))
    (fun t ht => reflectionHeightScale_cover hT (hheight t ht))

end TaoTrudgianYang2025
