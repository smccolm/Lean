import Dubon2026.SourceOriginalWeilCoverWeightedArcIntegral
import Dubon2026.SourceOriginalWeilCoverReversedArcIntegrand

/-! DUB-17/18 -> cover Abel converse -> weighted residue reciprocity.
Use the existing C1 reversed-arc substitution on the actual coefficient.
The actual dissection supplies the overlap and geometry; its constructed
primitive derivatives and constant jumps give the weighted cancellation. -/
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

local notation "BI" => coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders

open MeasureTheory

theorem cover_weighted_reversed_arc_integral :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C C' : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      (∀ P ∈ C'.ζ.source, AnalyticAt ℂ (C'.ζ ∘ PF P) 0 ∧ deriv (C'.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (k : Fin C.R.N) (k' : Fin C'.R.N) (ψ : ℝ → ℝ),
      StrictAntiOn ψ (C'.R.arcIcc k') → ContDiffOn ℝ 1 ψ (C'.R.arcIcc k') →
      ψ (C'.R.φs k'.castSucc) = C.R.φs k.succ →
      ψ (C'.R.φs k'.succ) = C.R.φs k.castSucc →
      (∀ u ∈ C'.R.arcIcc k', C'.bdry u = C.bdry (ψ u)) →
      (∀ s ∈ C.R.arcIcc k, C.bdry s ∈ C'.ζ.source ∧ C'.ζ (C.bdry s) ∈ C'.R.K) →
      ∀ (θ : Ω[EE⁄ℂ]), (∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) →
      ∀ (Ψ' : ℂ → ℂ), (∀ w ∈ C'.R.K, ContinuousAt Ψ' w) →
      (∫ t in (C'.R.φs k'.castSucc)..(C'.R.φs k'.succ), Ψ' (C'.R.loop t) * BI C' θ t) =
        -∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), Ψ' (C'.ζ (C.bdry s)) * BI C θ s := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C C' hC hC' k k' ψ hanti hc ha hb hbd hover θ hθ Ψ' hΨ'
  let a := C.R.φs k.castSucc
  let b := C.R.φs k.succ
  let a' := C'.R.φs k'.castSucc
  let b' := C'.R.φs k'.succ
  have hab' : a' < b' := C'.R.hmono Fin.castSucc_lt_succ
  have hm : MapsTo ψ (Icc a' b') (Icc a b) := by
    intro t ht
    have hh := hanti.antitoneOn.image_Icc_subset ⟨t, ht, rfl⟩
    rwa [ha, hb] at hh
  let W : ℝ → ℂ := fun s => Ψ' (C'.ζ (C.bdry s))
  have hW : ContinuousOn W (Icc a b) := by
    intro s hs
    exact (((hΨ' _ (hover s hs).2).comp (C'.ζ.continuousAt (hover s hs).1)).comp
      C.continuous_bdry.continuousAt).continuousWithinAt
  let G : ℝ → ℂ := fun s => W s * (CF C.ζ θ (C.R.loop s) * C.R.loopDerivOnArc k s)
  have hG : ContinuousOn G (Icc a b) :=
    hW.mul ((cover_continuousOn_boundary_coefficient N n radicand baseDivisor hRadicand hOrders C hC k θ hθ).mul
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
  have he : EqOn (fun t => Ψ' (C'.R.loop t) * BI C' θ t)
      (fun t => d t • (G ∘ ψ) t) (Ioo a' b') := by
    intro t ht
    have htI : t ∈ C'.R.arcIcc k' := ⟨ht.1.le, ht.2.le⟩
    have hψt : ψ t ∈ Ioo (C.R.φs k.castSucc) (C.R.φs k.succ) := by
      constructor
      · rw [← hb]
        exact hanti htI (right_mem_Icc.mpr hab'.le) ht.2
      · rw [← ha]
        exact hanti (left_mem_Icc.mpr hab'.le) htI ht.1
    change Ψ' (C'.R.loop t) * BI C' θ t = d t • (G ∘ ψ) t
    rw [cover_reversed_arc_integrand N n radicand baseDivisor hRadicand hOrders C C' hC hC' k k' ψ hanti ha hb hbd θ ht (hdAt t ht)]
    have hw : Ψ' (C'.R.loop t) = W (ψ t) := by
      dsimp only [W]
      rw [← hbd t htI, (C'.bdry_coordinates t).2]
    rw [hw]
    change W (ψ t) * ((CF C.ζ θ (C.R.loop (ψ t)) * C.R.loop' (ψ t)) * d t) = _
    rw [C.R.loop'_eq_loopDerivOnArc k hψt]
    simp only [G, Function.comp_apply, Complex.real_smul]
    ring
  have hneg := (arc_integral_eq_of_continuous_extension hab'.le hH he).2
  have hpos := (cover_weighted_arc_integral_extension N n radicand baseDivisor hRadicand hOrders C hC k θ hθ W hW).2
  change (∫ t in a'..b', Ψ' (C'.R.loop t) * BI C' θ t) =
    -∫ s in a..b, W s * BI C θ s
  rw [hneg, hpos]
  exact integral_reversed_contDiff_arc hab' hc hm ha hb hG

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
