import Dubon2026.SourceEllipticPeriodScalarMap
import Dubon2026.SourceEllipticPeriodLocalCoordinates

/-! One holomorphic affine germ suffices to identify an actual surjective
period-curve homomorphism with a scalar. Translation by the group law moves
that germ to every source point. This avoids a countable exceptional-set
development for the odd quotient map. Its rational formulas need only be
checked near one preimage of a target point with nonzero y-coordinate.
This is the DUB-17/18 odd-prime quotient-product compatibility obligation. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set WeierstrassCurve WeierstrassCurve.Affine
open scoped Topology

theorem local_lifts_of_one (L M : PeriodPair)
    [(periodCurve L).IsElliptic] [(periodCurve M).IsElliptic]
    (ψ : (periodCurve L).toAffine.Point →+ (periodCurve M).toAffine.Point)
    (z₁ : ℂ) {U : Set ℂ} (hU : U ∈ 𝓝 z₁) (G : ℂ → ℂ)
    (hGd : DifferentiableOn ℂ G U)
    (hGint : ∀ z ∈ U, periodHom M (G z) = ψ (periodHom L z)) :
    ∀ z₀ : ℂ, ∃ V ∈ 𝓝 z₀, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H V ∧
      ∀ z ∈ V, periodHom M (H z) = ψ (periodHom L z) := by
  intro z₀
  let w := z₁ - z₀
  have hw : z₀ + w = z₁ := by dsimp [w]; ring
  obtain ⟨cw, hcw⟩ := periodHom_surjective M (ψ (periodHom L w))
  refine ⟨(· + w) ⁻¹' U,
    (continuous_add_const w).continuousAt.preimage_mem_nhds (by rwa [hw]),
    fun z => G (z + w) - cw,
    (hGd.comp (differentiable_id.add_const w).differentiableOn
      (Set.mapsTo_preimage _ _)).sub_const cw, fun z hz => ?_⟩
  rw [map_sub, hcw, hGint (z + w) hz, ← map_sub ψ, ← map_sub (periodHom L),
    add_sub_cancel_right]

theorem scalar_map_of_affine_germ (L M : PeriodPair)
    [(periodCurve L).IsElliptic] [(periodCurve M).IsElliptic]
    (ψ : (periodCurve L).toAffine.Point →+ (periodCurve M).toAffine.Point)
    (hψ : Function.Surjective ψ)
    (z₀ : ℂ) {U : Set ℂ} (hU : U ∈ 𝓝 z₀) (X Y : ℂ → ℂ)
    (hXd : DifferentiableOn ℂ X U) (hYd : DifferentiableOn ℂ Y U)
    (hcoord : ∀ z ∈ U, Y z ≠ 0 ∧
      ∃ h, ψ (periodHom L z) = Point.some (X z) (Y z) h) :
    ∃ α : ℂˣ, (∀ l ∈ L.lattice, (α : ℂ) * l ∈ M.lattice) ∧
      ∀ z, periodHom M ((α : ℂ) * z) = ψ (periodHom L z) := by
  obtain ⟨V, hV, G, hGd, hGint⟩ := local_lift_of_affine_coordinates M
    (fun z => ψ (periodHom L z)) z₀ hU X Y hXd hYd hcoord
  exact scalar_map_of_local_lifts L M ψ hψ (local_lifts_of_one L M ψ z₀ hV G hGd hGint)

end Dubon2026.SourceEllipticPeriod
