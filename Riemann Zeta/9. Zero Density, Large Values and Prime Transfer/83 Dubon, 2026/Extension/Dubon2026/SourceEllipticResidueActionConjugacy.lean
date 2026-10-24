import Dubon2026.SourceEllipticResidueCurvePointEquiv
import Dubon2026.SourceEllipticInverseCoordinateNaturality

/-! Transport the actual residue-curve stabilizer action through the
equivalence with the base field and displayed coordinate change. Exact
coordinate identities, including the point at infinity, prove conjugacy.
This identifies the faithful inertia action with the prescribed elliptic
curve action needed for the DUB-17/18 exceptional-fiber census. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
noncomputable section
variable {k K : Type*} [Field k] [Field K] [DecidableEq k] [DecidableEq K]

private theorem zero_heq_curve {R : Type*} [Field R] [DecidableEq R]
    {V W : WeierstrassCurve R} (h : V = W) :
    HEq (0 : V.toAffine.Point) (0 : W.toAffine.Point) := by subst W; rfl

private theorem some_heq_curve {R : Type*} [Field R] {V W : WeierstrassCurve R}
    (h : V = W) {x y x' y' : R} (hx : x = x') (hy : y = y')
    {hP : V.toAffine.Nonsingular x y} {hQ : W.toAffine.Nonsingular x' y'} :
    HEq (Point.some x y hP) (Point.some x' y' hQ) := by
  subst W
  subst x'
  subst y'
  rfl

omit [DecidableEq k] [DecidableEq K] in
theorem residueConjugate_stabilizes (e : k ≃+* K) (V : WeierstrassCurve k)
    (E₀ : WeierstrassCurve K) (γ : VariableChange K)
    (hγ : γ • V.map e.toRingHom = E₀) (g : VariableChange k) (hg : g • V = V) :
    (γ * g.map e.toRingHom * γ⁻¹) • E₀ = E₀ := by
  rw [mul_smul, mul_smul, ← hγ, inv_smul_smul, map_variableChange, hg]

theorem residueCurvePointEquiv_equivariant (e : k ≃+* K) (V : WeierstrassCurve k)
    (E₀ : WeierstrassCurve K) (γ : VariableChange K)
    (hγ : γ • V.map e.toRingHom = E₀) (g : VariableChange k) (hg : g • V = V)
    (P Q : V.toAffine.Point) (hPQ : HEq (vcInvFun g V.toAffine P) Q) :
    HEq (vcInvFun (γ * g.map e.toRingHom * γ⁻¹) E₀.toAffine
        (residueCurvePointEquiv e V E₀ γ hγ P))
      (residueCurvePointEquiv e V E₀ γ hγ Q) := by
  have hfix := residueConjugate_stabilizes e V E₀ γ hγ g hg
  have hx1 (x : K) : vcXInv (1 : VariableChange K) x = x := by
    simp [vcXInv, VariableChange.one_def]
  have hy1 (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
    simp [vcYInv, VariableChange.one_def]
  have hmx (x : k) : e (vcXInv g x) = vcXInv (g.map e.toRingHom) (e x) :=
    map_vcXInv e.toRingHom g x
  have hmy (x y : k) : e (vcYInv g x y) = vcYInv (g.map e.toRingHom) (e x) (e y) :=
    map_vcYInv e.toRingHom g x y
  rcases P with _ | ⟨x, y, h⟩
  · have hQ : Q = 0 := eq_of_heq (hPQ.symm.trans (zero_heq_curve hg))
    change HEq (vcInvFun _ E₀.toAffine (residueCurvePointEquiv e V E₀ γ hγ 0)) _
    rw [hQ, map_zero, vcInvFun_zero]
    exact zero_heq_curve hfix
  · have hns : V.toAffine.Nonsingular (vcXInv g x) (vcYInv g x y) := by
      rw [← hg]
      exact (nonsingular_variableChange_iff _ _).mpr (by rw [vcX_vcXInv, vcY_vcYInv]; exact h)
    have hQ : Q = Point.some (vcXInv g x) (vcYInv g x y) hns :=
      eq_of_heq (hPQ.symm.trans (some_heq_curve hg rfl rfl))
    obtain ⟨hP', hP'Eq⟩ := residueCurvePointEquiv_some_coordinates e V E₀ γ hγ h
    obtain ⟨hQ', hQ'Eq⟩ := residueCurvePointEquiv_some_coordinates e V E₀ γ hγ hns
    rw [hQ, hP'Eq, hQ'Eq]
    apply some_heq_curve hfix
    · rw [vcXInv_mul, vcXInv_mul, ← vcXInv_mul γ⁻¹ γ, inv_mul_cancel, hx1,
        hmx]
    · rw [vcYInv_mul, vcYInv_mul, ← vcYInv_mul γ⁻¹ γ, ← vcXInv_mul γ⁻¹ γ,
        inv_mul_cancel, hx1, hy1, hmx, hmy]

end
end Dubon2026.SourceEllipticReduction
