import Dubon2026.SourceOriginalMeromorphicLocalAtlas
import Dubon2026.SourceOriginalMeromorphicCellDifferences
import Dubon2026.SourcePathAtlasJumpClosure

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The existing connected-path atlas theorem converts local logarithmic primitive
comparisons into the exact endpoint correction modulo jumps and residue periods.
The carrier neighborhoods remove only marked poles; no unused ball conditions
are introduced. Pole avoidance and the endpoint formula retain their full scope.
Adapted from S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_eq_sum_periods_add_sum_residues,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
noncomputable section
open SourceCurve Set Filter Complex KaehlerDifferential DissectionPeriods
open scoped Real Topology Manifold
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem path_sub_mem_G2 [Finite R] {𝒟 : CellDissection N}
    (S : Finset (Place ℂ F)) (θ : R → Ω[F⁄ℂ])
    (hθ : ∀ r v, -1 ≤ v.ordDifferential (θ r) ∧ (v ∉ S → 0 ≤ v.ordDifferential (θ r)))
    (hS : PolePos 𝒟 S) {V : 𝒟.ιC → Set ℂ} {Ψ : R → 𝒟.ιC → ℂ → ℂ}
    (hP : RegPrimData S θ V Ψ) {J : 𝒟.ιE → R → ℂ} (hJ : IsJumpH 𝒟 (hfun S θ Ψ) J)
    {P P' : Place ℂ F} (δ : Path P P') (hδ : ∀ t, δ t ∉ S) (g : R → unitInterval → ℂ)
    (hg : ∀ r, OriginalChart.IsPrimitiveAlong N (θ r) δ (g r)) :
    (fun r => g r 1 - g r 0) - (pval S θ Ψ (cellOf 𝒟 P') P' - pval S θ Ψ (cellOf 𝒟 P) P) ∈
      ΛJ 𝒟 S θ J := by
  have hP0 : P ∉ S := by rw [← δ.source]; exact hδ 0
  have hP1 : P' ∉ S := by rw [← δ.target]; exact hδ 1
  have key := sub_sub_mem_of_atlas (ΛJ 𝒟 S θ J) (Uset 𝒟 S) (Gθ S θ Ψ)
    ?_ δ.continuous (fun t r => g r t) ?_ (j₀ := P) (j₁ := P')
    (by rw [δ.source]; exact mem_Uset_self 𝒟 S hP0)
    (by rw [δ.target]; exact mem_Uset_self 𝒟 S hP1)
  · rw [δ.source, δ.target, Gθ_self, Gθ_self] at key
    exact key
  ·
    rintro x x' y ⟨hy, hy'⟩
    obtain ⟨hxS, hyb, hyS⟩ := mem_Uset hy
    obtain ⟨hxS', hyb', -⟩ := mem_Uset hy'
    set D := cellOf 𝒟 y with hDdef
    have hxD : x ∈ (𝒟.cell D).carrier := mem_carrier_of_not_mem_badCarrierSet 𝒟 hyb (mem_cellOf 𝒟 y)
    have hxD' : x' ∈ (𝒟.cell D).carrier := mem_carrier_of_not_mem_badCarrierSet 𝒟 hyb' (mem_cellOf 𝒟 y)

    have hlog : Φloc S θ Ψ D x y - Φloc S θ Ψ D x' y ∈ ΛJ 𝒟 S θ J := by
      by_cases hρ : ρ 𝒟 S θ D = 0
      · have : Φloc S θ Ψ D x y - Φloc S θ Ψ D x' y = 0 := by
          funext r
          simp only [Φloc, Pi.sub_apply, Pi.zero_apply, hρ]
          ring
        rw [this]; exact zero_mem _
      · have hc := ζ_ne_q S θ hS hxS hxD hρ
        have hc' := ζ_ne_q S θ hS hxS' hxD' hρ
        have hw := ζ_ne_q S θ hS hyS (mem_cellOf 𝒟 y) hρ
        obtain ⟨n, hn⟩ := Lg_sub_Lg (q := (𝒟.cell D).R.q) hc hc' hw
        have : Φloc S θ Ψ D x y - Φloc S θ Ψ D x' y =
            fun r => ρ 𝒟 S θ D r * (n * (2 * π * I)) := by
          funext r
          simp only [Φloc, Pi.sub_apply]
          rw [← hn]
          ring
        rw [this]
        exact AddSubgroup.mem_sup_right (zsmul_ρ_mem_Λres S θ D n)
    have h1 := pval_sub_mem S θ hJ hxD (mem_cellOf 𝒟 x)
    have h2 := pval_sub_mem S θ hJ hxD' (mem_cellOf 𝒟 x')
    have : Gθ S θ Ψ x y - Gθ S θ Ψ x' y =
        (Φloc S θ Ψ D x y - Φloc S θ Ψ D x' y) -
          (pval S θ Ψ D x - pval S θ Ψ (cellOf 𝒟 x) x) +
          (pval S θ Ψ D x' - pval S θ Ψ (cellOf 𝒟 x') x') := by
      simp only [Gθ, hDdef]; abel
    rw [this]
    exact add_mem (sub_mem hlog h1) h2
  ·
    intro t₀
    have hy₀ : δ t₀ ∉ S := hδ t₀
    refine ⟨δ t₀, isOpen_Uset 𝒟 S (δ t₀), mem_Uset_self 𝒟 S hy₀, ?_⟩
    have hev1 : ∀ᶠ t in 𝓝 t₀, δ t ∈ Uset 𝒟 S (δ t₀) :=
      δ.continuous.continuousAt.preimage_mem_nhds
        ((isOpen_Uset 𝒟 S (δ t₀)).mem_nhds (mem_Uset_self 𝒟 S hy₀))
    have hev2 : ∀ᶠ t in 𝓝 t₀, ∀ E : 𝒟.ιC, δ t₀ ∈ (𝒟.cell E).carrier →
        Φloc S θ Ψ E (δ t₀) (δ t) - Φloc S θ Ψ (cellOf 𝒟 (δ t₀)) (δ t₀) (δ t) =
          Φloc S θ Ψ E (δ t₀) (δ t₀) -
            Φloc S θ Ψ (cellOf 𝒟 (δ t₀)) (δ t₀) (δ t₀) := by
      haveI : Fintype 𝒟.ιC := 𝒟.fintypeC
      refine Filter.eventually_all.2 fun E => ?_
      by_cases hE : δ t₀ ∈ (𝒟.cell E).carrier
      · have := eventually_Φloc_sub S θ hθ hS hP hy₀ hE (mem_cellOf 𝒟 (δ t₀))
        have h' := δ.continuous.continuousAt (x := t₀) |>.eventually this
        filter_upwards [h'] with t ht _
        exact ht
      · exact Filter.Eventually.of_forall fun t h => absurd h hE

    have hG : ∀ᶠ t in 𝓝 t₀, Gθ S θ Ψ (δ t₀) (δ t) =
        Φloc S θ Ψ (cellOf 𝒟 (δ t₀)) (δ t₀) (δ t) -
          pval S θ Ψ (cellOf 𝒟 (δ t₀)) (δ t₀) + pval S θ Ψ (cellOf 𝒟 (δ t₀)) (δ t₀) := by
      filter_upwards [hev1, hev2] with t ht1 ht2
      obtain ⟨-, hb, -⟩ := mem_Uset ht1
      have hE : δ t₀ ∈ (𝒟.cell (cellOf 𝒟 (δ t))).carrier :=
        mem_carrier_of_not_mem_badCarrierSet 𝒟 hb (mem_cellOf 𝒟 (δ t))
      have := ht2 _ hE
      rw [Φloc_self, Φloc_self] at this
      simp only [Gθ]
      rw [sub_eq_iff_eq_add] at this
      rw [this]
      abel

    set E₀ := cellOf 𝒟 (δ t₀) with hE₀
    have hsrc : δ t₀ ∈ (𝒟.cell E₀).ζ.source ∧ (𝒟.cell E₀).ζ (δ t₀) ∈ V E₀ := by
      obtain ⟨z, hz, hyz⟩ := mem_cellOf 𝒟 (δ t₀)
      have ht := (𝒟.cell E₀).hKt hz
      rw [← hyz]
      exact ⟨(𝒟.cell E₀).ζ.map_target ht,
        by rw [(𝒟.cell E₀).ζ.right_inv ht]; exact hP.hKV E₀ hz⟩
    have hcomp : ∀ r, ∃ c : ℂ, ∀ᶠ t in 𝓝 t₀,
        g r t = Φloc S θ Ψ E₀ (δ t₀) (δ t) r + c := by
      intro r
      obtain ⟨Φ₁, hΦ₁, hgΦ⟩ := hg r t₀
      obtain ⟨W, hWo, hcW, hW⟩ := exists_logPrimitive S θ hθ hS hP r E₀ hsrc.2
        (fun hρ => ζ_ne_q S θ hS hy₀ (mem_cellOf 𝒟 _) (fun h => hρ (by rw [h]; rfl)))
      have hΦ := hasDerivAt_coordPrimitive (𝒟.cell E₀).toAnalyticCoord hsrc.1 hWo hcW hW
        ((hθ r _).2 hy₀)
      have hdiff := eventually_coordPrimitive_sub_eq hΦ₁ hΦ
      refine ⟨Φ₁ (extChartAt 𝓘(ℂ, ℂ) (δ t₀) (δ t₀)) - Φloc S θ Ψ E₀ (δ t₀) (δ t₀) r, ?_⟩
      have h1 := δ.continuous.continuousAt (x := t₀) |>.eventually hdiff
      have h2 : ∀ᶠ t in 𝓝 t₀, δ t ∈ (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).source :=
        δ.continuous.continuousAt.preimage_mem_nhds
          (extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) (δ t₀))
      filter_upwards [h1, h2, hgΦ] with t ht hts hgt
      rw [hgt]
      change Φ₁ (extChartAt 𝓘(ℂ, ℂ) (δ t₀) (δ t)) = _
      simp only [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).left_inv hts,
        (extChartAt 𝓘(ℂ, ℂ) (δ t₀)).left_inv (mem_extChartAt_source (δ t₀))] at ht
      simp only [Φloc]
      linear_combination ht
    choose c hc using hcomp
    refine ⟨fun r => c r - pval S θ Ψ E₀ (δ t₀) r + pval S θ Ψ E₀ (δ t₀) r, ?_⟩
    filter_upwards [hG, Filter.eventually_all.2 hc] with t htG htc
    rw [htG]
    funext r
    simp only [Pi.add_apply, Pi.sub_apply, htc r]
    ring

end
end Dubon2026.SourceFunctionField.CellGeometry.MeromorphicPeriods
