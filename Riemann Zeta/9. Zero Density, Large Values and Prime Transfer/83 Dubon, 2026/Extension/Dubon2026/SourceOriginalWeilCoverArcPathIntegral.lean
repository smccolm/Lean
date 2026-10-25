import Dubon2026.SourceOriginalWeilCoverBoundaryCoefficient
import Dubon2026.SourceOriginalWeilCoverPathPrimitiveDerivative
import Dubon2026.SourceOriginalWeilCoverRegularPathPrimitives
import Dubon2026.SourceRadialAffinePrimitiveIntegral

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
The actual cover path integral equals its coordinate boundary integral.
Local analytic primitives, the proved inverse-coordinate chain rule and native
interval FTC discharge the comparison; regularity is needed only on the arc. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open OriginalEdgePaths (arcParam arcParam_mem arcParam_mem_Ioo hasDerivAt_arcParam)
open scoped Topology Interval
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

theorem cover_pathIntegral_arcPath :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (C : RadialCell (Place ℂ EE)),
      (∀ P ∈ C.ζ.source, AnalyticAt ℂ (C.ζ ∘ PF P) 0 ∧ deriv (C.ζ ∘ PF P) 0 ≠ 0) →
      ∀ (k : Fin C.R.N) (θ : Ω[EE⁄ℂ]),
      (∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) →
      (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ (C.arcPath k) g) ∧
      pathIntegral N n radicand baseDivisor hRadicand hOrders θ (C.arcPath k) =
        ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ),
          coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders C θ s := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro C hC k θ hθ
  have hab : C.R.φs k.castSucc < C.R.φs k.succ := C.R.hmono Fin.castSucc_lt_succ
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong_of_coeff_mem N n radicand baseDivisor hRadicand hOrders θ (C.arcPath k)
    (fun t => ((C.arcPath k) t).mem_of_ord_nonneg (hθ _ (arcParam_mem C.R k t)))
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [pathIntegral_eq_of_isPrimitiveAlong N n radicand baseDivisor hRadicand hOrders hg]
  let gd : ℝ → ℂ := fun s => CF C.ζ θ (C.R.loop s) * C.R.loopDerivOnArc k s
  have hgd : ContinuousOn gd (C.R.arcIcc k) :=
    (cover_continuousOn_boundary_coefficient N n radicand baseDivisor hRadicand hOrders C hC k θ hθ).mul
      (C.R.continuous_loopDerivOnArc k).continuousOn
  have heq : EqOn (coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders C θ) gd
      (Ioo (C.R.φs k.castSucc) (C.R.φs k.succ)) := by
    intro s hs
    change CF C.ζ θ (C.R.loop s) * C.R.loop' s = _
    rw [C.R.loop'_eq_loopDerivOnArc k hs]
  set G : ℝ → ℂ := fun t => g (projIcc 0 1 zero_le_one t) with hG
  have hGc : ContinuousOn G (Icc 0 1) :=
    ((hg.continuous N n radicand baseDivisor hRadicand hOrders).comp continuous_projIcc).continuousOn
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt G
      (gd (arcParam C.R k t) * ((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ)) t := by
    intro t ht
    let tI : unitInterval := ⟨t, ht.1.le, ht.2.le⟩
    have hs : arcParam C.R k t ∈ Ioo (C.R.φs k.castSucc) (C.R.φs k.succ) :=
      arcParam_mem_Ioo C.R k ht
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg tI
    obtain ⟨hQs, hζQ⟩ := C.bdry_coordinates (arcParam C.R k t)
    have hz : HasDerivAt (fun u : ℝ => C.R.loop (arcParam C.R k u))
        (C.R.loop' (arcParam C.R k t) * ((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ)) t := by
      refine ((C.R.hasDerivAt_loop k hs).scomp t (hasDerivAt_arcParam C.R k t)).congr_deriv ?_
      rw [Complex.real_smul, mul_comm]
    have hΦ' : HasDerivAt Φ (RD (C.bdry (arcParam C.R k t)) θ 0) 0 := by
      have h := hΦ.self_of_nhds
      rw [placeChart_self] at h
      exact h
    have hcomp := cover_hasDerivAt_path_primitive N n radicand baseDivisor hRadicand hOrders C.ζ hQs
      (hC _ hQs).1 (hC _ hQs).2
      ((C.bdry (arcParam C.R k t)).mem_of_ord_nonneg (hθ _ (arcParam_mem C.R k tI)))
      hΦ' hz hζQ.symm
    have hproj : Tendsto (fun u : ℝ => projIcc 0 1 zero_le_one u) (𝓝 t) (𝓝 tI) := by
      have hh := continuous_projIcc (h := zero_le_one (α := ℝ)) |>.continuousAt (x := t)
      rwa [ContinuousAt, projIcc_of_mem zero_le_one ⟨ht.1.le, ht.2.le⟩] at hh
    have hnear : ∀ᶠ u in 𝓝 t, G u =
        (Φ ∘ PC (C.bdry (arcParam C.R k t)) ∘ C.ζ.symm ∘
          fun u : ℝ => C.R.loop (arcParam C.R k u)) u := by
      filter_upwards [hproj.eventually hgΦ, Ioo_mem_nhds ht.1 ht.2] with u hu huI
      have hu' : g (projIcc 0 1 zero_le_one u) = Φ (PC ((C.arcPath k) tI)
          (C.arcPath k (projIcc 0 1 zero_le_one u))) := hu
      rw [hG]
      show g (projIcc 0 1 zero_le_one u) = _
      rw [hu', projIcc_of_mem zero_le_one ⟨huI.1.le, huI.2.le⟩]
      rfl
    refine (hcomp.congr_of_eventuallyEq hnear).congr_deriv ?_
    change CF C.ζ θ (C.R.loop (arcParam C.R k t)) * (_ * _) =
      (CF C.ζ θ (C.R.loop (arcParam C.R k t)) * _) * _
    rw [C.R.loop'_eq_loopDerivOnArc k hs, mul_assoc]
  have hftc := OriginalEdgePaths.arc_integral_eq_primitive_sub C.R k hgd hGc hderiv
  have hG0 : G 0 = g 0 := by
    simp only [hG, projIcc_of_mem zero_le_one (left_mem_Icc.2 zero_le_one)]; rfl
  have hG1 : G 1 = g 1 := by
    simp only [hG, projIcc_of_mem zero_le_one (right_mem_Icc.2 zero_le_one)]; rfl
  rw [hG0, hG1] at hftc
  exact hftc.symm.trans (arc_integral_eq_of_continuous_extension hab.le hgd heq).2.symm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
