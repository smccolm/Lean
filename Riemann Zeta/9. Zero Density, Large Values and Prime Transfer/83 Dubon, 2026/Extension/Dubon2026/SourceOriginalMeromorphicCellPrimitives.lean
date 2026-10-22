import Dubon2026.SourceOriginalMeromorphicRegularizedCoefficient

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Subtract the actual simple-pole residue term in each marked original cell.
The original coefficient expansion makes the remainder analytic on a common
open neighborhood; the already proved radial primitive theorem integrates it.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
All original coordinate, simple-pole and primitive calculus is reused.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Topology Manifold
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

variable {𝒟 : CellDissection N} (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])

/-- Analytic primitives of the residue-subtracted coefficients on cell neighborhoods. -/
structure RegPrimData {𝒟 : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ]) (V : 𝒟.ιC → Set ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ) : Prop where
  hVo : ∀ C, IsOpen (V C)
  hVstar : ∀ C, StarConvex ℝ (𝒟.cell C).R.q (V C)
  hKV : ∀ C, (𝒟.cell C).R.K ⊆ V C
  hVgood : ∀ C, V C ⊆ goodSet (S := S) C
  hΨ : ∀ r C, ∀ w ∈ V C, HasDerivAt (Ψ r C) (regCoeff S θ r C w) w

theorem exists_regPrimData {𝒟 : CellDissection N} (S : Finset (Place ℂ F))
    (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r))) (hS : PolePos 𝒟 S) :
    ∃ (V : 𝒟.ιC → Set ℂ) (Ψ : R → 𝒟.ιC → ℂ → ℂ), RegPrimData S θ V Ψ := by
  have hcell : ∀ C : 𝒟.ιC, ∃ (V : Set ℂ) (Ψ : R → ℂ → ℂ), IsOpen V ∧
      StarConvex ℝ (𝒟.cell C).R.q V ∧ (𝒟.cell C).R.K ⊆ V ∧ V ⊆ goodSet (S := S) C ∧
      ∀ r, ∀ w ∈ V, HasDerivAt (Ψ r) (regCoeff S θ r C w) w := by
    intro C
    obtain ⟨W, hWo, _, hWstar, hKW, hsub⟩ :=
      (𝒟.cell C).R.exists_open_starConvex_neighborhood _ (isOpen_goodSet C) (K_subset_goodSet hS C)
    have hdiff : ∀ r, DifferentiableOn ℂ (regCoeff S θ r C) W :=
      fun r w hw => (analyticAt_regCoeff S θ hθ hS r C (hsub hw)).differentiableAt
        |>.differentiableWithinAt
    have hprim := fun r => exists_radial_primitive hWo hWstar (hdiff r)
    choose Ψ _ hΨ using hprim
    exact ⟨W, Ψ, hWo, hWstar, hKW, hsub, hΨ⟩
  choose V Ψ hVo hVs hKV hVg hΨ using hcell
  exact ⟨V, fun r C => Ψ C r, ⟨hVo, hVs, hKV, hVg, fun r C => hΨ C r⟩⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
