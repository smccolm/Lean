import Dubon2026.SourceOriginalCellPathPrimitiveDerivative
import Dubon2026.SourceOriginalRegularPathPrimitives
import Dubon2026.SourceCellArcIntegralExtension

/-! DUB-17/18 -> original Abel-Jacobi -> actual cycle periods.
The original path integral equals the actual cell boundary integral. Existing
local primitives and inverse-coordinate derivatives supply the chain rule;
the native fundamental theorem and affine substitution finish the identity.
Adapted from the edge-integral argument of the verified Apache-2.0 source
anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
noncomputable section
open SourceCurve Set Filter KaehlerDifferential OriginalChart
open scoped Manifold Topology Interval
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem pathIntegral_arcPath (C : Cell N) (k : Fin C.R.N) {θ : Ω[F⁄ℂ]}
    (hθ : ∀ s ∈ C.R.arcIcc k, 0 ≤ (C.bdry s).ordDifferential θ) :
    (∃ g, IsPrimitiveAlong N θ (arcPath C k) g) ∧
      pathIntegral N θ (arcPath C k) =
        ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), C.bdryIntegrand θ s := by
  have hab : C.R.φs k.castSucc < C.R.φs k.succ := C.R.hmono Fin.castSucc_lt_succ
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong_of_coeff_mem N θ (arcPath C k)
    (fun t => ((arcPath C k) t).mem_of_ord_nonneg (hθ _ (arcParam_mem C.R k t)))
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [pathIntegral_eq_of_isPrimitiveAlong N hg]
  let gd : ℝ → ℂ := fun s => coeffIn C.ζ θ (C.R.loop s) * C.R.loopDerivOnArc k s
  have hgd : ContinuousOn gd (C.R.arcIcc k) :=
    (C.continuousOn_boundary_coefficient k θ hθ).mul
      (C.R.continuous_loopDerivOnArc k).continuousOn
  have heq : EqOn (C.bdryIntegrand θ) gd
      (Ioo (C.R.φs k.castSucc) (C.R.φs k.succ)) := by
    intro s hs
    change coeffIn C.ζ θ (C.R.loop s) * C.R.loop' s = _
    rw [C.R.loop'_eq_loopDerivOnArc k hs]
  set G : ℝ → ℂ := fun t => g (projIcc 0 1 zero_le_one t) with hG
  have hGc : ContinuousOn G (Icc 0 1) :=
    ((hg.continuous N).comp continuous_projIcc).continuousOn
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt G
      (gd (arcParam C.R k t) * ((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ)) t := by
    intro t ht
    let tI : unitInterval := ⟨t, ht.1.le, ht.2.le⟩
    have hs : arcParam C.R k t ∈ Ioo (C.R.φs k.castSucc) (C.R.φs k.succ) :=
      arcParam_mem_Ioo C.R k ht
    obtain ⟨Φ, hΦ, hgΦ⟩ := hg tI
    have hQt : (arcPath C k) tI = C.bdry (arcParam C.R k t) := rfl
    obtain ⟨hQs, hζQ⟩ := C.bdry_coordinates (arcParam C.R k t)
    have hz : HasDerivAt (fun u : ℝ => C.R.loop (arcParam C.R k u))
        (C.R.loop' (arcParam C.R k t) * ((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ)) t := by
      refine ((C.R.hasDerivAt_loop k hs).scomp t (hasDerivAt_arcParam C.R k t)).congr_deriv ?_
      rw [Complex.real_smul, mul_comm]
    have hΦ' : HasDerivAt Φ
        (readDifferential N (C.bdry (arcParam C.R k t)) θ
          (extChartAt 𝓘(ℂ, ℂ) (C.bdry (arcParam C.R k t)) (C.bdry (arcParam C.R k t))))
        (extChartAt 𝓘(ℂ, ℂ) (C.bdry (arcParam C.R k t)) (C.bdry (arcParam C.R k t))) :=
      hΦ.self_of_nhds
    have hcomp := C.toAnalyticCoord.hasDerivAt_path_primitive hQs
      ((C.bdry (arcParam C.R k t)).mem_of_ord_nonneg (hθ _ (arcParam_mem C.R k tI)))
      hΦ' hz hζQ.symm
    have hproj : Tendsto (fun u : ℝ => projIcc 0 1 zero_le_one u) (𝓝 t) (𝓝 tI) := by
      have hh := continuous_projIcc (h := zero_le_one (α := ℝ)) |>.continuousAt (x := t)
      rwa [ContinuousAt, projIcc_of_mem zero_le_one ⟨ht.1.le, ht.2.le⟩] at hh
    have hnear : ∀ᶠ u in 𝓝 t, G u =
        (Φ ∘ extChartAt 𝓘(ℂ, ℂ) (C.bdry (arcParam C.R k t)) ∘ C.ζ.symm ∘
          fun u : ℝ => C.R.loop (arcParam C.R k u)) u := by
      filter_upwards [hproj.eventually hgΦ, Ioo_mem_nhds ht.1 ht.2] with u hu huI
      have hu' : g (projIcc 0 1 zero_le_one u) = Φ (extChartAt 𝓘(ℂ, ℂ) ((arcPath C k) tI)
          (arcPath C k (projIcc 0 1 zero_le_one u))) := hu
      rw [hG]
      show g (projIcc 0 1 zero_le_one u) = _
      rw [hu', projIcc_of_mem zero_le_one ⟨huI.1.le, huI.2.le⟩]
      rfl
    refine (hcomp.congr_of_eventuallyEq hnear).congr_deriv ?_
    change coeffIn C.ζ θ (C.R.loop (arcParam C.R k t)) * (_ * _) =
      (coeffIn C.ζ θ (C.R.loop (arcParam C.R k t)) * _) * _
    rw [C.R.loop'_eq_loopDerivOnArc k hs, mul_assoc]
  have hcont : ContinuousOn (fun t => gd (arcParam C.R k t) *
      ((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ)) (Icc 0 1) := by
    refine (hgd.comp (by unfold arcParam; fun_prop) fun t ht => ?_).mul continuousOn_const
    exact arcParam_mem C.R k ⟨t, ht⟩
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hGc hderiv
    ((hcont.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable)
  have hG0 : G 0 = g 0 := by
    simp only [hG, projIcc_of_mem zero_le_one (left_mem_Icc.2 zero_le_one)]; rfl
  have hG1 : G 1 = g 1 := by
    simp only [hG, projIcc_of_mem zero_le_one (right_mem_Icc.2 zero_le_one)]; rfl
  rw [← hG0, ← hG1, ← hftc]
  have hsub : (∫ t in (0 : ℝ)..1, gd (arcParam C.R k t) *
      ((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ)) =
      ∫ s in (C.R.φs k.castSucc)..(C.R.φs k.succ), gd s := by
    have h1 : (∫ t in (0 : ℝ)..1, gd (arcParam C.R k t) *
        ((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ)) =
        ((C.R.φs k.succ - C.R.φs k.castSucc : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1,
          gd ((C.R.φs k.succ - C.R.φs k.castSucc) * t + C.R.φs k.castSucc) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [arcParam]
      ring_nf
    rw [h1, intervalIntegral.integral_comp_mul_add gd (sub_ne_zero.2 hab.ne')]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel, Complex.real_smul, Complex.ofReal_inv]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast sub_ne_zero.2 hab.ne'), one_mul]
  rw [hsub]
  exact (arc_integral_eq_of_continuous_extension hab.le hgd heq).2.symm

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
