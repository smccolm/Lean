import Dubon2026.SourceEllipticCompositeQuotientJ
import Dubon2026.SourceEllipticCyclicRootEquivariance

/-! The literal all-level quotient value commutes with coefficient-fixed
field maps and with base-field automorphisms of the original elliptic curve.
This uses the already proved recursive quotient compatibility; no new
coordinate or isogeny construction is required. The DUB-17/18 inertia census
needs this compatibility for composite as well as prime levels. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]

/-- The actual composite quotient value commutes with a coefficient-fixed field map. -/
theorem cyclicQuotientJ_fixedCurve
    (f : L →+* L) (W : WeierstrassCurve L) [W.IsElliptic]
    (hW : W.map f = W) (N : ℕ) (hN : (N : L) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    cyclicQuotientJ W N hN (fixedCurveCyclicKernelMap f W hW N H) =
      f (cyclicQuotientJ W N hN H) := by
  have hc : ∀ (V : WeierstrassCurve L) (hV : W.map f = V) (he : V.IsElliptic),
      @cyclicQuotientJ L _ _ _ V he N hN (hV ▸ primeCyclicKernelMap f W N H) =
        f (cyclicQuotientJ W N hN H) := by
    rintro V rfl he
    exact cyclicQuotientJ_map f W N hN H
  exact hc W hW inferInstance

/-- Every base-field automorphism acts equivariantly on the original all-level cyclic quotient values. -/
theorem cyclicQuotientJ_galois
    {F : Type*} [Field F] [Algebra F L]
    (W : WeierstrassCurve F) [W.IsElliptic] (σ : L ≃ₐ[F] L)
    (N : ℕ) (hN : (N : L) ≠ 0)
    (H : {H : AddSubgroup (W.baseChange L).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N}) :
    cyclicQuotientJ (W.baseChange L) N hN
      (fixedCurveCyclicKernelMap σ.toRingHom (W.baseChange L)
        (W.map_baseChange σ.toAlgHom) N H) =
      σ (cyclicQuotientJ (W.baseChange L) N hN H) :=
  cyclicQuotientJ_fixedCurve σ.toRingHom (W.baseChange L)
    (W.map_baseChange σ.toAlgHom) N hN H

end
end Dubon2026.SourceEllipticVelu
