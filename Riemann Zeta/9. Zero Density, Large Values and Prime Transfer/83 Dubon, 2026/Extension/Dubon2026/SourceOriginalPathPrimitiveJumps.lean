import Dubon2026.SourcePathAtlasJumpClosure
import Dubon2026.SourceOriginalCellPrimitiveLocalDifference
import Dubon2026.SourceOriginalCellCarrierNeighborhoods
import Dubon2026.SourceOriginalCellJumpDifferences

/-! DUB-17/18 -> original Abel-Jacobi -> regular loop-period generation.
This is a necessary step in converting arbitrary actual path integrals into
the subgroup of the constructed primitive jumps. Adapted from
S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Reuse original cell compactness, coefficient pullback and primitive uniqueness;
no new ambient curve, manifold, compactness or primitive existence is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellDissection OriginalChart
open scoped Topology Manifold
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

/-- A local primitive chart corrected by the chosen cell readings at its center. -/
def Gchart (𝒟 : CellDissection N) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) (x y : Place ℂ F) : κ → ℂ :=
  gvec 𝒟 Ψ y (cellOf 𝒟 y) - gvec 𝒟 Ψ x (cellOf 𝒟 y) + gvec 𝒟 Ψ x (cellOf 𝒟 x)

theorem path_sub_mem_closure_jumps [Finite κ] (𝒟 : CellDissection N)
    (η : κ → Ω[F⁄ℂ]) (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ)
    (J : 𝒟.ιE → κ → ℂ) (hP : PrimData 𝒟 η V Ψ) (hJ : IsJump 𝒟 Ψ J)
    {P P' : Place ℂ F} (δ : Path P P') (g : κ → unitInterval → ℂ)
    (hg : ∀ i, IsPrimitiveAlong N (η i) δ (g i)) :
    (fun i => g i 1 - g i 0) - (gvec 𝒟 Ψ P' (cellOf 𝒟 P') - gvec 𝒟 Ψ P (cellOf 𝒟 P)) ∈
      AddSubgroup.closure (Set.range J) := by
  set Λ := AddSubgroup.closure (Set.range J) with hΛ
  have key := sub_sub_mem_of_atlas Λ (fun x : Place ℂ F => (badCarrierSet 𝒟 x)ᶜ) (Gchart 𝒟 Ψ)
    ?_ δ.continuous (fun t i => g i t) ?_ (j₀ := P) (j₁ := P')
    (by rw [δ.source]; exact not_mem_badCarrierSet_self 𝒟 P)
    (by rw [δ.target]; exact not_mem_badCarrierSet_self 𝒟 P')
  · have h0 : Gchart 𝒟 Ψ P (δ 0) = gvec 𝒟 Ψ P (cellOf 𝒟 P) := by
      rw [δ.source]; simp only [Gchart]; abel
    have h1 : Gchart 𝒟 Ψ P' (δ 1) = gvec 𝒟 Ψ P' (cellOf 𝒟 P') := by
      rw [δ.target]; simp only [Gchart]; abel
    rw [h0, h1] at key
    exact key
  ·
    rintro x x' y ⟨hy, hy'⟩
    have hcy : x ∈ (𝒟.cell (cellOf 𝒟 y)).carrier :=
      mem_carrier_of_not_mem_badCarrierSet 𝒟 hy (mem_cellOf 𝒟 y)
    have hcy' : x' ∈ (𝒟.cell (cellOf 𝒟 y)).carrier :=
      mem_carrier_of_not_mem_badCarrierSet 𝒟 hy' (mem_cellOf 𝒟 y)
    have h1 := gvec_sub_mem hJ (mem_cellOf 𝒟 x) hcy
    have h2 := gvec_sub_mem hJ hcy' (mem_cellOf 𝒟 x')
    have : Gchart 𝒟 Ψ x y - Gchart 𝒟 Ψ x' y =
        (gvec 𝒟 Ψ x (cellOf 𝒟 x) - gvec 𝒟 Ψ x (cellOf 𝒟 y)) +
          (gvec 𝒟 Ψ x' (cellOf 𝒟 y) - gvec 𝒟 Ψ x' (cellOf 𝒟 x')) := by
      simp only [Gchart]; abel
    rw [this]
    exact add_mem h1 h2
  ·
    intro t₀
    refine ⟨δ t₀, (isClosed_badCarrierSet 𝒟 (δ t₀)).isOpen_compl, not_mem_badCarrierSet_self 𝒟 (δ t₀), ?_⟩

    have hev1 : ∀ᶠ t in 𝓝 t₀, δ t ∈ (badCarrierSet 𝒟 (δ t₀))ᶜ :=
      δ.continuous.continuousAt.preimage_mem_nhds
        ((isClosed_badCarrierSet 𝒟 (δ t₀)).isOpen_compl.mem_nhds (not_mem_badCarrierSet_self 𝒟 (δ t₀)))
    have hev2 : ∀ᶠ t in 𝓝 t₀, ∀ E : 𝒟.ιC, (δ t₀) ∈ (𝒟.cell E).carrier →
        gvec 𝒟 Ψ (δ t) E - gvec 𝒟 Ψ (δ t) (cellOf 𝒟 (δ t₀)) = gvec 𝒟 Ψ (δ t₀) E - gvec 𝒟 Ψ (δ t₀) (cellOf 𝒟 (δ t₀)) := by
      haveI : Fintype 𝒟.ιC := 𝒟.fintypeC
      refine Filter.eventually_all.2 fun E => ?_
      by_cases hE : (δ t₀) ∈ (𝒟.cell E).carrier
      · have := eventually_gvec_sub 𝒟 η V Ψ hP hE (mem_cellOf 𝒟 (δ t₀))
        have h' := δ.continuous.continuousAt (x := t₀) |>.eventually this
        filter_upwards [h'] with t ht _
        exact ht
      · exact Filter.Eventually.of_forall fun t h => absurd h hE
    have hG : ∀ᶠ t in 𝓝 t₀, Gchart 𝒟 Ψ (δ t₀) (δ t) = gvec 𝒟 Ψ (δ t) (cellOf 𝒟 (δ t₀)) := by
      filter_upwards [hev1, hev2] with t ht1 ht2
      have hE : (δ t₀) ∈ (𝒟.cell (cellOf 𝒟 (δ t))).carrier :=
        mem_carrier_of_not_mem_badCarrierSet 𝒟 ht1 (mem_cellOf 𝒟 (δ t))
      have := ht2 _ hE
      simp only [Gchart]
      linear_combination this

    have hsrc : (δ t₀) ∈ (𝒟.cell (cellOf 𝒟 (δ t₀))).ζ.source ∧
        (𝒟.cell (cellOf 𝒟 (δ t₀))).ζ (δ t₀) ∈ V (cellOf 𝒟 (δ t₀)) := by
      have hgen : ∀ (E : 𝒟.ιC) (y : Place ℂ F), y ∈ (𝒟.cell E).carrier →
          y ∈ (𝒟.cell E).ζ.source ∧ (𝒟.cell E).ζ y ∈ V E := by
        rintro E y ⟨z, hz, rfl⟩
        have ht := (𝒟.cell E).hKt hz
        exact ⟨(𝒟.cell E).ζ.map_target ht, by rw [(𝒟.cell E).ζ.right_inv ht]; exact hP.hKV E hz⟩
      exact hgen _ _ (mem_cellOf 𝒟 (δ t₀))
    have hcomp : ∀ i, ∃ c : ℂ, ∀ᶠ t in 𝓝 t₀, g i t = Ψ i (cellOf 𝒟 (δ t₀)) ((𝒟.cell (cellOf 𝒟 (δ t₀))).ζ (δ t)) + c := by
      intro i
      obtain ⟨Φ₁, hΦ₁, hgΦ⟩ := hg i t₀
      have hΦ := hasDerivAt_coordPrimitive (𝒟.cell (cellOf 𝒟 (δ t₀))).toAnalyticCoord hsrc.1 (hP.hVo (cellOf 𝒟 (δ t₀))) hsrc.2
        (hP.hΨ i (cellOf 𝒟 (δ t₀))) (hP.hη i (δ t₀))
      have hdiff := eventually_coordPrimitive_sub_eq hΦ₁ hΦ
      refine ⟨Φ₁ (extChartAt 𝓘(ℂ, ℂ) (δ t₀) (δ t₀)) -
        Ψ i (cellOf 𝒟 (δ t₀)) ((𝒟.cell (cellOf 𝒟 (δ t₀))).ζ (δ t₀)), ?_⟩
      have h1 := δ.continuous.continuousAt (x := t₀) |>.eventually hdiff
      have h2 : ∀ᶠ t in 𝓝 t₀, δ t ∈ (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).source :=
        δ.continuous.continuousAt.preimage_mem_nhds
          (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (δ t₀))
      filter_upwards [h1, h2, hgΦ] with t ht hts hgt
      rw [hgt]
      change Φ₁ (extChartAt 𝓘(ℂ, ℂ) (δ t₀) (δ t)) = _
      simp only [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).left_inv hts,
        (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).left_inv (mem_extChartAt_source (δ t₀))] at ht
      linear_combination ht
    choose c hc using hcomp
    refine ⟨c, ?_⟩
    filter_upwards [hG, Filter.eventually_all.2 hc] with t htG htc
    rw [htG]
    funext i
    exact htc i
end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
