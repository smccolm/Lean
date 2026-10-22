import Dubon2026.SourceOriginalCyclePeriodPolygonData

/-! DUB-17/18 -> original Abel-Jacobi -> jump-to-loop-period generation.
Assemble the proved polygon word, integer-cycle decomposition and actual loop
integrals on an abstractly named original dissection. This keeps the final
constructed-dissection application small without changing any proof limits.
All inputs are explicit prior mathematical obligations, not matrix rows.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
universe u
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart OriginalEdgePaths
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem period_matrix_of_primitive_word (D : CellDissection N) (η : κ → Ω[F⁄ℂ])
    (hη : ∀ i, η i ∈ regularDifferentials ℂ F) (T Ts : Finset D.ιE)
    (Z : D.ιE → D.ιE → ℤ) (J : D.ιE → κ → ℂ)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (hdec : ∀ f : D.ιE → ULift.{u} ℤ,
      (∀ w, (∑ e with (D.ends e).2 = w, f e) = ∑ e with (D.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j)
    (hγi : ∀ j (θ : Ω[F⁄ℂ]), RegOnSkeleton D θ →
      (∃ g, IsPrimitiveAlong N θ (γ j) g) ∧
        pathIntegral N θ (γ j) = ∑ e, (Z j e : ℂ) * D.edgeInt θ e)
    (hgen : AddSubgroup.closure (range J) ≤ AddSubgroup.closure (J '' ((T ∪ Ts)ᶜ : Finset D.ιE)))
    (hW : PrimitivePolygonConclusion D η Ts J) : CyclePeriodPolygonConclusion D η T Ts J γ := by
  obtain ⟨hm, wd, hw₁, hw₃, hwjump⟩ := hW
  letI := hm
  have hZd := integer_decomposition_of_lift D (T := T) (Z := Z) hdec
  have hJF := jump_formula_of_word T Ts Z (Ivec D η) J
    hZd wd hw₃ hwjump
  have hzv : ∀ l, zv Z (Ivec D η) l =
      fun i => pathIntegral N (η i) (γ l) := by
    intro l
    funext i
    have hi := (hγi l (η i) (fun Q _ => Q.ord_nonneg_of_mem
      ((mem_original_regularDifferentials_iff N ℂ (η i)).mp (hη i) Q))).2
    simpa only [zv, Ivec, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using hi.symm
  have hrow : ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ,
      (wordMatrix wd j l : ℂ) • (fun i => pathIntegral N (η i) (γ l)) := by
    intro j hj
    rw [hJF j hj]
    simp_rw [hzv]
  have hcl := closure_generated_jumps_le_periods D T Ts J
    (fun l i => pathIntegral N (η i) (γ l)) (wordMatrix wd) hgen hrow
  unfold CyclePeriodPolygonConclusion
  intro Cside startV endV L m
  exact ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
