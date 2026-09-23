import TaoTrudgianYang2025.SargosSextupleRadiusJets

/-! Local affine derivative scaling without any exterior smoothness assumption. -/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem sargos_iteratedDeriv_comp_affine_local {f : ℝ → ℝ} {l r c d x : ℝ}
    (hf : ∀ y ∈ Ioo l r, ContDiffAt ℝ ∞ f (c*y+d))
    (hx : x ∈ Ioo l r) (n : ℕ) :
    iteratedDeriv n (fun y => f (c*y+d)) x =
      c^n*iteratedDeriv n f (c*x+d) := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero,pow_zero,one_mul]
  | succ n ih =>
      have he : iteratedDeriv n (fun y => f (c*y+d)) =ᶠ[𝓝 x]
          (fun y => c^n*iteratedDeriv n f (c*y+d)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact ih hy
      have hd := (contDiffAt_iteratedDeriv_infty (hf x hx) n).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
      have hh := (hd.hasDerivAt.comp x
        (((hasDerivAt_id x).const_mul c).add_const d)).const_mul (c^n)
      dsimp only [Function.comp_def,id_eq] at hh
      rw [iteratedDeriv_succ,he.deriv_eq,hh.deriv,iteratedDeriv_succ,pow_succ]
      ring

end TaoTrudgianYang2025
