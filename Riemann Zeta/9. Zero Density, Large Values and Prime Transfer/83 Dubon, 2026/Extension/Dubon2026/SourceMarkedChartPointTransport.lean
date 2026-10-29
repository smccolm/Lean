import Dubon2026.SourceMarkedChartInvariantSeparation

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> original marked
chart -> stabilizer comparison. The two original coordinate invariants
detect transport of the actual point up to sign in every characteristic.
The diamond consumer supplies both invariant transport equalities. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve

theorem point_map_eq_or_neg_of_invariant_values
    {K k Ω : Type*} [Field K] [Field k] [Field Ω] [DecidableEq Ω]
    [Algebra K k] [Algebra K Ω] [Algebra k Ω] [IsScalarTower K k Ω]
    (E : WeierstrassCurve k) [E.IsElliptic] (hE : Transcendental K E.j)
    (a b a' b' : Ω) (h : (E.baseChange Ω).toAffine.Nonsingular a b)
    (h' : (E.baseChange Ω).toAffine.Nonsingular a' b') (σ : Ω ≃ₐ[k] Ω)
    (h1 : σ ((E.baseChange Ω).c₄ * (12 * a + (E.baseChange Ω).b₂) /
      (E.baseChange Ω).c₆) =
      (E.baseChange Ω).c₄ * (12 * a' + (E.baseChange Ω).b₂) / (E.baseChange Ω).c₆)
    (h2 : σ ((6 * a ^ 2 + (E.baseChange Ω).b₂ * a + (E.baseChange Ω).b₄) /
      (E.baseChange Ω).c₄) =
      (6 * a' ^ 2 + (E.baseChange Ω).b₂ * a' + (E.baseChange Ω).b₄) / (E.baseChange Ω).c₄) :
    Affine.Point.map (W' := E) σ.toAlgHom (Affine.Point.some a b h) = Affine.Point.some a' b' h' ∨
      Affine.Point.map (W' := E) σ.toAlgHom (Affine.Point.some a b h) = -Affine.Point.some a' b' h' := by
  have hc4 : (E.baseChange Ω).c₄ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄]
    exact (map_ne_zero (algebraMap k Ω)).mpr (c4_ne_zero_of_transcendental_j E hE)
  have hc6 : (E.baseChange Ω).c₆ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆]
    exact (map_ne_zero (algebraMap k Ω)).mpr (c6_ne_zero_of_transcendental_j E hE)
  have hv1 : (E.baseChange Ω).c₄ * (12 * σ a + (E.baseChange Ω).b₂) / (E.baseChange Ω).c₆ =
      (E.baseChange Ω).c₄ * (12 * a' + (E.baseChange Ω).b₂) / (E.baseChange Ω).c₆ := by
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆,
      WeierstrassCurve.map_b₂, map_div₀, map_mul, map_add, map_ofNat, σ.commutes] using h1
  have hv2 : (6 * (σ a) ^ 2 + (E.baseChange Ω).b₂ * σ a + (E.baseChange Ω).b₄) /
      (E.baseChange Ω).c₄ = (6 * a' ^ 2 + (E.baseChange Ω).b₂ * a' + (E.baseChange Ω).b₄) /
      (E.baseChange Ω).c₄ := by
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, WeierstrassCurve.map_b₂,
      WeierstrassCurve.map_b₄, map_div₀, map_mul, map_add, map_pow, map_ofNat, σ.commutes] using h2
  exact Affine.Point.X_eq_iff.mp (abscissa_eq_of_invariant_pair (E.baseChange Ω) hc4 hc6 hv1 hv2)

end
end Dubon2026.SourceFunctionField.MarkedChart
