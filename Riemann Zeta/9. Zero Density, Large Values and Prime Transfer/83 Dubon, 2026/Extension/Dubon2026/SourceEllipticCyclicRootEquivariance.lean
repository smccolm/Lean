import Dubon2026.SourceEllipticCyclicRootBaseChange

/-! DUB-17/18 -> original inertia -> good reduction -> cyclic orbit census.
Specialize the proved field-map naturality to automorphisms fixing the actual
curve coefficients. For a curve over the base field this equality is derived
from native base-change compatibility, so equivariance is not a certificate. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve SourceEllipticVelu.OddDiscriminant
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

/-- The literal image subgroup after identifying the coefficient-fixed curve. -/
def fixedCurveCyclicKernelMap (f : K →+* K) (W : WeierstrassCurve K)
    (hW : W.map f = W) (p : ℕ)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p} :=
  hW ▸ primeCyclicKernelMap f W p H

/-- Coefficient-fixed field maps commute with the actual cyclic-root value. -/
theorem primeCyclicRootMap_fixedCurve [IsAlgClosed K]
    (f : K →+* K) (W : WeierstrassCurve K) [W.IsElliptic]
    (hW : W.map f = W) (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    (primeCyclicRootMap W p hp (fixedCurveCyclicKernelMap f W hW p H)).1 =
      f (primeCyclicRootMap W p hp H).1 := by
  have hc : ∀ (V : WeierstrassCurve K) (hV : W.map f = V) (he : V.IsElliptic),
      (@primeCyclicRootMap K _ _ _ V he p _ hp
        (hV ▸ primeCyclicKernelMap f W p H)).1 =
        f (primeCyclicRootMap W p hp H).1 := by
    rintro V rfl he
    exact primeCyclicRootMap_map f W p hp hp H
  exact hc W hW inferInstance

/-- Every base-field automorphism, and hence every inertia element, acts equivariantly on the original prime root map. -/
theorem primeCyclicRootMap_galois
    {F : Type*} [Field F] [Algebra F K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic] (σ : K ≃ₐ[F] K)
    (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0)
    (H : {H : AddSubgroup (W.baseChange K).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = p}) :
    (primeCyclicRootMap (W.baseChange K) p hp
      (fixedCurveCyclicKernelMap σ.toRingHom (W.baseChange K)
        (W.map_baseChange σ.toAlgHom) p H)).1 =
      σ (primeCyclicRootMap (W.baseChange K) p hp H).1 :=
  primeCyclicRootMap_fixedCurve σ.toRingHom (W.baseChange K)
    (W.map_baseChange σ.toAlgHom) p hp H

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
