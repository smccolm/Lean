import Dubon2026.SourceEllipticModelTorsionEquivariance

/-! Identity residue action fixes actual prime-to-characteristic torsion.
This discharges the torsion-fixing assumption in the finite Legendre model
and division-field faithfulness arguments. The required chain is
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2, good reduction, reverse genus,
exceptional-fiber census, and faithful finite Galois specialization.
Only the already proved injective torsion reduction is used; full reduction
additivity on arbitrary nonintegral points is unnecessary. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing SourceEllipticVariableChange
noncomputable section

private theorem zero_heq_of_curve_eq {K : Type*} [Field K]
    {V W : WeierstrassCurve.Affine K} (h : V = W) :
    HEq (Affine.Point.zero : V.Point) (Affine.Point.zero : W.Point) := by
  subst W
  rfl

private theorem some_heq_of_curve_eq {K : Type*} [Field K]
    {V W : WeierstrassCurve.Affine K} (h : V = W) {x y x' y' : K}
    (hx : x = x') (hy : y = y') {hP : V.Nonsingular x y} {hQ : W.Nonsingular x' y'} :
    HEq (Affine.Point.some x y hP) (Affine.Point.some x' y' hQ) := by
  subst W
  subst x'
  subst y'
  rfl

theorem vcInvFun_one_heq {K : Type*} [Field K]
    (W : WeierstrassCurve.Affine K) (P : W.Point) :
    HEq (vcInvFun (1 : VariableChange K) W P) P := by
  cases P with
  | zero => exact zero_heq_of_curve_eq (one_smul _ W)
  | some x y h =>
    apply some_heq_of_curve_eq (one_smul _ W)
    · simp [vcXInv, VariableChange.one_def]
    · simp [vcYInv, VariableChange.one_def]

theorem galois_fixes_torsion_of_residue_cocycle_one
    {F M : Type*} [Field F] [Field M] [Algebra F M] [DecidableEq M]
    {A : ValuationSubring M} [DecidableEq (ResidueField A)]
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype)
    (hΔ : (W.map (residue A)).Δ ≠ 0) {N : ℕ} (hN : IsUnit (N : A))
    (g : VariableChange A) (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F)
    (hg : g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹)
    (hg1 : g.map (residue A) = 1)
    (P : (E.baseChange M).toAffine.Point) (hP : N • P = 0) :
    Affine.Point.map (σ : M →ₐ[F] M) P = P := by
  let Q : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) :=
    ⟨P, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hP⟩
  have hfix : g.map (residue A) • W.map (residue A) = W.map (residue A) := by
    rw [hg1, one_smul]
  have he := modelTorsionReduction_inertia E W κ hκ hΔ hN g σ hσ hσI hg hfix Q
  rw [hg1] at he
  have heq := (vcInvFun_one_heq _ _).symm.trans he
  have hQ := modelTorsionReduction_injective E W κ hκ hΔ hN (eq_of_heq heq)
  exact (congrArg Subtype.val hQ).symm

end
end Dubon2026.SourceEllipticReduction
