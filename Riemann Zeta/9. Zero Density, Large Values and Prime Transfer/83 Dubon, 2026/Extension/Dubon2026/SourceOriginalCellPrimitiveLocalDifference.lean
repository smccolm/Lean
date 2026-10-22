import Dubon2026.SourceOriginalCoordinatePrimitiveComparison
import Dubon2026.SourceOriginalPolygonPrimitiveData

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

theorem eventually_gvec_sub [Finite κ] (𝒟 : CellDissection N)
    (η : κ → Ω[F⁄ℂ]) (V : 𝒟.ιC → Set ℂ) (Ψ : κ → 𝒟.ιC → ℂ → ℂ) (hP : PrimData 𝒟 η V Ψ) {y : Place ℂ F} {D D' : 𝒟.ιC}
    (hD : y ∈ (𝒟.cell D).carrier) (hD' : y ∈ (𝒟.cell D').carrier) :
    ∀ᶠ x in 𝓝 y, gvec 𝒟 Ψ x D - gvec 𝒟 Ψ x D' = gvec 𝒟 Ψ y D - gvec 𝒟 Ψ y D' := by

  have key : ∀ i, ∀ᶠ x in 𝓝 y, Ψ i D ((𝒟.cell D).ζ x) - Ψ i D' ((𝒟.cell D').ζ x) =
      Ψ i D ((𝒟.cell D).ζ y) - Ψ i D' ((𝒟.cell D').ζ y) := by
    intro i
    have hsrc : ∀ {E : 𝒟.ιC}, y ∈ (𝒟.cell E).carrier →
        y ∈ (𝒟.cell E).ζ.source ∧ (𝒟.cell E).ζ y ∈ V E := by
      rintro E ⟨z, hz, rfl⟩
      have ht := (𝒟.cell E).hKt hz
      exact ⟨(𝒟.cell E).ζ.map_target ht, by rw [(𝒟.cell E).ζ.right_inv ht]; exact hP.hKV E hz⟩
    have h1 := hasDerivAt_coordPrimitive (𝒟.cell D).toAnalyticCoord (hsrc hD).1 (hP.hVo D)
      (hsrc hD).2 (hP.hΨ i D) (hP.hη i y)
    have h2 := hasDerivAt_coordPrimitive (𝒟.cell D').toAnalyticCoord (hsrc hD').1 (hP.hVo D')
      (hsrc hD').2 (hP.hΨ i D') (hP.hη i y)
    have h3 := eventually_coordPrimitive_sub_eq h1 h2

    have hin : ∀ᶠ x in 𝓝 y, x ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := extChartAt_source_mem_nhds y
    filter_upwards [h3, hin] with x hx hxs
    simp only [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) y).left_inv hxs,
      (extChartAt 𝓘(ℂ, ℂ) y).left_inv (mem_extChartAt_source y)] at hx
    exact hx
  filter_upwards [Filter.eventually_all.2 key] with x hx
  funext i
  exact hx i
end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
