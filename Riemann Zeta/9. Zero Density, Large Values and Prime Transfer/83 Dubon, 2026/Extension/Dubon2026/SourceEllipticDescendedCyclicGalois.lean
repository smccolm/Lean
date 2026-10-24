import Dubon2026.SourceEllipticCyclicRootLiftNaturality
import Mathlib.FieldTheory.Normal.Basic

/-! The descended literal quotient value is equivariant for the original
field automorphism. Native normal-extension lifting supplies the ambient
automorphism; the proved point and cyclic-quotient diagrams then descend
through the injective field inclusion. This is the remaining equivariance
input in the DUB-17/18 finite-field root-orbit comparison. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve WeierstrassCurve.Affine SourceFunctionField.IntegralJCoordinate
noncomputable section

theorem descended_cyclic_value_galois
    {B M L : Type*} [Field B] [Field M] [Field L] [DecidableEq M] [DecidableEq L]
    [Algebra B M] [Algebra M L] [Algebra B L] [IsScalarTower B M L]
    [IsAlgClosed L] [Normal B L]
    (E : WeierstrassCurve B) [E.IsElliptic] (N : ℕ) (hNL : (N : L) ≠ 0)
    (q : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} → M)
    (hq : ∀ S, algebraMap M L (q S) =
      cyclicQuotientJ ((E.baseChange M).baseChange L) N hNL
        (primeCyclicKernelMap (algebraMap M L) (E.baseChange M) N S))
    (σ : M ≃ₐ[B] M)
    (S T : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N})
    (hT : T.val = S.val.map (Point.map (W' := E) σ.toAlgHom)) : q T = σ (q S) := by
  let τ := σ.liftNormal L
  have hcomm (x : M) : τ (algebraMap M L x) = algebraMap M L (σ x) :=
    σ.liftNormal_commutes L x
  have hfixed : T = fixedCurveCyclicKernelMap σ.toRingHom (E.baseChange M)
      (E.map_baseChange σ.toAlgHom) N S := by
    apply Subtype.ext
    rw [fixedCurveCyclicKernelMap_coe, fixedCurvePointMap_galois]
    exact hT
  apply (algebraMap M L).injective
  calc
    algebraMap M L (q T) =
        cyclicQuotientJ ((E.baseChange M).baseChange L) N hNL
          (primeCyclicKernelMap (algebraMap M L) (E.baseChange M) N
            (fixedCurveCyclicKernelMap σ.toRingHom (E.baseChange M)
              (E.map_baseChange σ.toAlgHom) N S)) := by rw [hfixed, hq]
    _ = τ (cyclicQuotientJ ((E.baseChange M).baseChange L) N hNL
        (primeCyclicKernelMap (algebraMap M L) (E.baseChange M) N S)) :=
      cyclicQuotientJ_lift_naturality (algebraMap M L) (E.baseChange M)
        σ.toRingHom (E.map_baseChange σ.toAlgHom) τ.toRingHom hcomm N hNL S
    _ = τ (algebraMap M L (q S)) := by rw [hq]
    _ = algebraMap M L (σ (q S)) := hcomm _

end
end Dubon2026.SourceEllipticVelu
