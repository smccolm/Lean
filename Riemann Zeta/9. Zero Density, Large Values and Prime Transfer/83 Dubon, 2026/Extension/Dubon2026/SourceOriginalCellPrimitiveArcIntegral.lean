import Dubon2026.SourceOriginalArcPathIntegral
import Dubon2026.SourceOriginalWeightedArcReversal

/-! DUB-17/18 -> original Abel-Jacobi -> polygon-word jump formula.
Primitive endpoint differences equal the actual arc integrals. The existing
weighted reversal theorem, specialized to weight one, supplies the negative
edge sign. These are the analytic inputs to telescoping the polygon word.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem Cell.primitive_arc_integral (C : Cell N) (k : Fin C.R.N) {θ : Ω[F⁄ℂ]}
    {V : Set ℂ} (hKV : C.R.K ⊆ V) {Ψ : ℂ → ℂ}
    (hΨ : ∀ w ∈ V, HasDerivAt Ψ (coeffIn C.ζ θ w) w)
    (hθ : ∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) :
    (∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), C.bdryIntegrand θ s) =
      Ψ (C.R.loop (C.R.φs k.succ)) - Ψ (C.R.loop (C.R.φs k.castSucc)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (C.R.hmono Fin.castSucc_lt_succ).le
    (f := fun s => Ψ (C.R.loop s))
  · intro s _
    exact ((hΨ _ (hKV (C.R.loop_mem_K s))).continuousAt.comp
      C.R.continuous_loop.continuousAt).continuousWithinAt
  · intro s hs
    exact (hΨ _ (hKV (C.R.loop_mem_K s))).comp s (C.R.hasDerivAt_loop k hs)
  · exact C.arc_integrable k θ hθ

theorem CellDissection.negative_arc_integral (D : CellDissection N) (e : D.ιE) {θ : Ω[F⁄ℂ]}
    (hθ : ∀ s ∈ (D.cell (D.arcOf (e, true)).1).R.arcIcc (D.arcOf (e, true)).2,
      0 ≤ ((D.cell (D.arcOf (e, true)).1).bdry s).ordDifferential θ) :
    (∫ s in ((D.cell (D.arcOf (e, false)).1).R.φs (D.arcOf (e, false)).2.castSucc)..
        ((D.cell (D.arcOf (e, false)).1).R.φs (D.arcOf (e, false)).2.succ),
      (D.cell (D.arcOf (e, false)).1).bdryIntegrand θ s) = -D.edgeInt θ e := by
  let p := D.arcOf (e, true)
  let n := D.arcOf (e, false)
  have hp : D.side p.1 p.2 = (e, true) := D.side_arcOf _
  have hn : D.side n.1 n.2 = (e, false) := D.side_arcOf _
  obtain ⟨ψ, hanti, hc, ha, hb, hbd⟩ := D.arc_rev p.1 p.2 n.1 n.2
    (by rw [hp, hn]) (by rw [hp]) (by rw [hn])
  have h := (D.cell p.1).weighted_reversed_arc_integral (D.cell n.1) p.2 n.2
    ψ hanti hc ha hb hbd θ hθ (fun _ => 1) (fun _ _ => continuousAt_const)
  simpa only [one_mul] using h

end
end Dubon2026.SourceFunctionField.CellGeometry
