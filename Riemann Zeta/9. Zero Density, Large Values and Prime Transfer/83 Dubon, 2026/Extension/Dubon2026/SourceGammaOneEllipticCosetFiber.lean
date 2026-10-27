import Dubon2026.SourceGammaOneCuspCosetPlaces
import Dubon2026.SourceGammaOneJFiberOrbits

/-! DUB-17/18 -> actual Gamma1 real period surjectivity -> genus lower
bound -> elliptic fiber cardinalities. Actual signed cosets map onto the
literal finite j fiber. A cyclic subgroup fixing the analytic point acts
inside each fiber, so only a surjection from cyclic orbits is needed.
This adapts the existing SourceOriginalCosetFiber construction, retaining
the original Gamma1 field and avoiding a second injectivity proof. -/
namespace Dubon2026.SourceFunctionField.GammaOne.EllipticCounting
noncomputable section
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup SourceCurve
open scoped MatrixGroups GammaOne
variable (N : ℕ) (hT : ModularGroup.T ∈ Gamma1 N) (τ : ℍ)

/-- The actual finite j-fiber point represented by an inverse integral translate. -/
def point (g : SL(2, ℤ)) : AnalyticFiberOrbits.Fiber N τ :=
  ⟨analyticPlace hT (g⁻¹ • τ), by
    have h := analyticPlace_j_sub_pos hT (g⁻¹ • τ)
    rwa [JMultiplicity.jf_smul] at h⟩

theorem point_eq_of_leftRel (a b : SL(2, ℤ))
    (hab : QuotientGroup.leftRel (plusMinus (Gamma1 N)) a b) :
    point N hT τ a = point N hT τ b := by
  have hm := QuotientGroup.leftRel_apply.mp hab
  have he : b⁻¹ • τ = (a⁻¹ * b)⁻¹ • (a⁻¹ • τ) := by
    rw [← mul_smul]
    congr 1
    group
  apply Subtype.ext
  change analyticPlace hT (a⁻¹ • τ) = analyticPlace hT (b⁻¹ • τ)
  rw [he, analyticPlace_smul_plusMinus hT (inv_mem hm)]

/-- Map actual signed integral cosets onto the original finite j fiber. -/
def cosetToFiber : CuspCounting.Cosets (Gamma1 N) → AnalyticFiberOrbits.Fiber N τ :=
  Quotient.lift (point N hT τ) (point_eq_of_leftRel N hT τ)

theorem cosetToFiber_mk (g : SL(2, ℤ)) :
    cosetToFiber N hT τ (g : CuspCounting.Cosets (Gamma1 N)) = point N hT τ g := rfl

theorem cosetToFiber_surjective [NeZero N] : Function.Surjective (cosetToFiber N hT τ) := by
  intro P
  obtain ⟨q, hq⟩ := AnalyticFiberOrbits.toFiber_surjective N hT τ P
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp
    (q.out : MulAction.orbit SL(2, ℤ) τ).property
  refine ⟨(g⁻¹ : SL(2, ℤ)), ?_⟩
  apply Subtype.ext
  change analyticPlace hT ((g⁻¹)⁻¹ • τ) = P.val
  rw [inv_inv, hg]
  exact congrArg Subtype.val hq

theorem cosetToFiber_stabilizer_smul (k : MulAction.stabilizer SL(2, ℤ) τ)
    (x : CuspCounting.Cosets (Gamma1 N)) :
    cosetToFiber N hT τ ((k : SL(2, ℤ)) • x) = cosetToFiber N hT τ x := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    apply Subtype.ext
    change analyticPlace hT (((k : SL(2, ℤ)) * g)⁻¹ • τ) =
      analyticPlace hT (g⁻¹ • τ)
    have hk : (k : SL(2, ℤ))⁻¹ • τ = τ := inv_smul_eq_iff.mpr k.2.symm
    rw [mul_inv_rev, mul_smul, hk]

/-- Descend the actual finite-fiber map through a cyclic action fixing its analytic value. -/
def cyclicToFiber (g : SL(2, ℤ)) (hg : g • τ = τ) :
    SourceManin.Orb (MulAction.toPermHom SL(2, ℤ) (CuspCounting.Cosets (Gamma1 N)) g) →
      AnalyticFiberOrbits.Fiber N τ :=
  Quotient.lift (cosetToFiber N hT τ) (by
    intro x y hxy
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hxy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp k.2
    change (k.val : Equiv.Perm (CuspCounting.Cosets (Gamma1 N))) y = x at hk
    rw [← hn, ← map_zpow] at hk
    change (g ^ n) • y = x at hk
    rw [← hk]
    exact cosetToFiber_stabilizer_smul N hT τ
      ⟨g ^ n, Subgroup.zpow_mem _ (show g ∈ MulAction.stabilizer SL(2, ℤ) τ from hg) n⟩ y)

theorem cyclicToFiber_surjective [NeZero N] (g : SL(2, ℤ)) (hg : g • τ = τ) :
    Function.Surjective (cyclicToFiber N hT τ g hg) := by
  intro P
  obtain ⟨x, hx⟩ := cosetToFiber_surjective N hT τ P
  exact ⟨SourceManin.orbQ _ x, hx⟩

include hT in
theorem card_fiber_le_cyclic_orbits [NeZero N] (g : SL(2, ℤ)) (hg : g • τ = τ) :
    Nat.card (AnalyticFiberOrbits.Fiber N τ) ≤
      Nat.card (SourceManin.Orb
        (MulAction.toPermHom SL(2, ℤ) (CuspCounting.Cosets (Gamma1 N)) g)) :=
  Nat.card_le_card_of_surjective _ (cyclicToFiber_surjective N hT τ g hg)

end
end Dubon2026.SourceFunctionField.GammaOne.EllipticCounting
