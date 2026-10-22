import Dubon2026.SourceOriginalWeightedArcIntegral
import Dubon2026.SourceOriginalReversedArcIntegrand
import Dubon2026.SourceOriginalPairedArcOverlap

/-! DUB-17/18 -> raw reciprocity -> paired weighted boundary integrals.
The source C1 reversed-arc parameterization and the proved coefficient transport
give the exact sign change of the actual weighted differential integral.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set MeasureTheory KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem Cell.weighted_reversed_arc_integral (C C' : Cell N) (k : Fin C.R.N) (k' : Fin C'.R.N)
    (ψ : ℝ → ℝ) (hanti : StrictAntiOn ψ (C'.R.arcIcc k'))
    (hc : ContDiffOn ℝ 1 ψ (C'.R.arcIcc k'))
    (ha : ψ (C'.R.φs k'.castSucc) = C.R.φs k.succ)
    (hb : ψ (C'.R.φs k'.succ) = C.R.φs k.castSucc)
    (hbd : ∀ t ∈ C'.R.arcIcc k', C'.bdry t = C.bdry (ψ t))
    (θ : Ω[F⁄ℂ]) (hθ : ∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ)
    (Ψ' : ℂ → ℂ) (hΨ' : ∀ w ∈ C'.R.K, ContinuousAt Ψ' w) :
    (∫ t in (C'.R.φs k'.castSucc)..(C'.R.φs k'.succ), Ψ' (C'.R.loop t) * C'.bdryIntegrand θ t) =
      -∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ),
        Ψ' (C'.ζ (C.bdry s)) * C.bdryIntegrand θ s := by
  let a := C.R.φs k.castSucc
  let b := C.R.φs k.succ
  let a' := C'.R.φs k'.castSucc
  let b' := C'.R.φs k'.succ
  have hab' : a' < b' := C'.R.hmono Fin.castSucc_lt_succ
  have hm : MapsTo ψ (Icc a' b') (Icc a b) := by
    intro t ht
    have hh := hanti.antitoneOn.image_Icc_subset ⟨t, ht, rfl⟩
    rwa [ha, hb] at hh
  have hover := C.reversed_arc_overlap C' k k' ψ hc.continuousOn ha hb hbd
  let W : ℝ → ℂ := fun s => Ψ' (C'.ζ (C.bdry s))
  have hW : ContinuousOn W (Icc a b) := by
    intro s hs
    exact (((hΨ' _ (hover s hs).2).comp (C'.ζ.continuousAt (hover s hs).1)).comp
      C.continuous_bdry.continuousAt).continuousWithinAt
  let G : ℝ → ℂ := fun s => W s * (coeffIn C.ζ θ (C.R.loop s) * C.R.loopDerivOnArc k s)
  have hG : ContinuousOn G (Icc a b) :=
    hW.mul ((C.continuousOn_boundary_coefficient k θ hθ).mul
      (C.R.continuous_loopDerivOnArc k).continuousOn)
  let d : ℝ → ℝ := derivWithin ψ (Icc a' b')
  have hd : ContinuousOn d (Icc a' b') := hc.continuousOn_derivWithin (uniqueDiffOn_Icc hab') le_rfl
  have hdAt : ∀ t ∈ Ioo a' b', HasDerivAt ψ (d t) t := by
    intro t ht
    have hdt := (hc.differentiableOn one_ne_zero).differentiableAt (Icc_mem_nhds ht.1 ht.2)
    rw [show d t = deriv ψ t from hdt.derivWithin (uniqueDiffOn_Icc hab' t ⟨ht.1.le, ht.2.le⟩)]
    exact hdt.hasDerivAt
  have hH : ContinuousOn (fun t => d t • (G ∘ ψ) t) (Icc a' b') :=
    hd.smul (hG.comp hc.continuousOn hm)
  have he : EqOn (fun t => Ψ' (C'.R.loop t) * C'.bdryIntegrand θ t)
      (fun t => d t • (G ∘ ψ) t) (Ioo a' b') := by
    intro t ht
    have htI : t ∈ C'.R.arcIcc k' := ⟨ht.1.le, ht.2.le⟩
    have hψt : ψ t ∈ Ioo (C.R.φs k.castSucc) (C.R.φs k.succ) := by
      constructor
      · rw [← hb]
        exact hanti htI (right_mem_Icc.mpr hab'.le) ht.2
      · rw [← ha]
        exact hanti (left_mem_Icc.mpr hab'.le) htI ht.1
    change Ψ' (C'.R.loop t) * C'.bdryIntegrand θ t = d t • (G ∘ ψ) t
    rw [C.reversed_arc_integrand C' k k' ψ hanti ha hb hbd θ ht (hdAt t ht)]
    have hw : Ψ' (C'.R.loop t) = W (ψ t) := by
      dsimp only [W]
      rw [← hbd t htI, (C'.bdry_coordinates t).2]
    rw [hw]
    change W (ψ t) * ((coeffIn C.ζ θ (C.R.loop (ψ t)) * C.R.loop' (ψ t)) * d t) = _
    rw [C.R.loop'_eq_loopDerivOnArc k hψt]
    simp only [G, Function.comp_apply, Complex.real_smul]
    ring
  have hneg := (arc_integral_eq_of_continuous_extension hab'.le hH he).2
  have hpos := (C.weighted_arc_integral_extension k θ hθ W hW).2
  change (∫ t in a'..b', Ψ' (C'.R.loop t) * C'.bdryIntegrand θ t) =
    -∫ s in a..b, W s * C.bdryIntegrand θ s
  rw [hneg, hpos]
  exact integral_reversed_contDiff_arc hab' hc hm ha hb hG

end
end Dubon2026.SourceFunctionField.CellGeometry
