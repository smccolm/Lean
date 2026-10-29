import Dubon2026.SourceMarkedChartInvariantSeparation

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> original-field
marked-point stabilizer. An automorphism fixing the actual field embedding
fixes both invariant values. Their proved separation, including in residue
characteristics two and three, forces the actual marked point to be fixed
up to sign. This proves one stabilizer inclusion; equality still requires
the original signed-index/orbit comparison. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve

theorem point_fixed_up_to_sign_of_embedding_fixed
    {K k Ω F : Type*} [Field K] [Field k] [Field Ω] [Field F] [DecidableEq Ω]
    [Algebra K k] [Algebra K Ω] [Algebra k Ω] [IsScalarTower K k Ω] [Algebra K F]
    (E : WeierstrassCurve k) [E.IsElliptic] (hE : Transcendental K E.j)
    (ψ : F →ₐ[K] Ω) (f1 f2 : F) (a b : Ω) (h : (E.baseChange Ω).toAffine.Nonsingular a b)
    (hw1 : ψ f1 = (E.baseChange Ω).c₄ * (12 * a + (E.baseChange Ω).b₂) /
      (E.baseChange Ω).c₆)
    (hw2 : ψ f2 = (6 * a ^ 2 + (E.baseChange Ω).b₂ * a + (E.baseChange Ω).b₄) /
      (E.baseChange Ω).c₄)
    (σ : Ω ≃ₐ[k] Ω) (hσ : (σ.toAlgHom.restrictScalars K).comp ψ = ψ) :
    Affine.Point.map (W' := E) σ.toAlgHom (Affine.Point.some a b h) = Affine.Point.some a b h ∨
      Affine.Point.map (W' := E) σ.toAlgHom (Affine.Point.some a b h) = -Affine.Point.some a b h := by
  have hc4 : (E.baseChange Ω).c₄ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄]
    exact (map_ne_zero (algebraMap k Ω)).mpr (c4_ne_zero_of_transcendental_j E hE)
  have hc6 : (E.baseChange Ω).c₆ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆]
    exact (map_ne_zero (algebraMap k Ω)).mpr (c6_ne_zero_of_transcendental_j E hE)
  have hs1 : σ (ψ f1) = ψ f1 := AlgHom.congr_fun hσ f1
  have hs2 : σ (ψ f2) = ψ f2 := AlgHom.congr_fun hσ f2
  rw [hw1] at hs1
  rw [hw2] at hs2
  have h1 : (E.baseChange Ω).c₄ * (12 * σ a + (E.baseChange Ω).b₂) / (E.baseChange Ω).c₆ =
      (E.baseChange Ω).c₄ * (12 * a + (E.baseChange Ω).b₂) / (E.baseChange Ω).c₆ := by
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆,
      WeierstrassCurve.map_b₂, map_div₀, map_mul, map_add, map_ofNat, σ.commutes] using hs1
  have h2 : (6 * (σ a) ^ 2 + (E.baseChange Ω).b₂ * σ a + (E.baseChange Ω).b₄) /
      (E.baseChange Ω).c₄ = (6 * a ^ 2 + (E.baseChange Ω).b₂ * a + (E.baseChange Ω).b₄) /
      (E.baseChange Ω).c₄ := by
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, WeierstrassCurve.map_b₂,
      WeierstrassCurve.map_b₄, map_div₀, map_mul, map_add, map_pow, map_ofNat, σ.commutes] using hs2
  exact Affine.Point.X_eq_iff.mp (abscissa_eq_of_invariant_pair (E.baseChange Ω) hc4 hc6 h1 h2)

end
end Dubon2026.SourceFunctionField.MarkedChart
