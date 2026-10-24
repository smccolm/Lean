import Dubon2026.SourceEllipticFixedCurvePointMap
import Dubon2026.SourceEllipticAllLevelCyclicEquivariance

/-! Cyclic kernels defined over the original field give actual quotient
values fixed by its algebraic-closure automorphisms. Native point-map
base-change compatibility proves the subgroup invariance. This is the
fixed-root input to finite-field descent in the DUB-17/18 orbit route. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve WeierstrassCurve.Affine OddDiscriminant
open SourceFunctionField.IntegralJCoordinate
noncomputable section

theorem cyclicQuotientJ_baseChange_fixed
    {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    [Algebra F L] [IsAlgClosed L]
    (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) (hN : (N : L) ≠ 0)
    (S : {S : AddSubgroup W.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N})
    (σ : L ≃ₐ[F] L) :
    σ (cyclicQuotientJ (W.baseChange L) N hN
      (primeCyclicKernelMap (algebraMap F L) W N S)) =
      cyclicQuotientJ (W.baseChange L) N hN
        (primeCyclicKernelMap (algebraMap F L) W N S) := by
  let H := primeCyclicKernelMap (algebraMap F L) W N S
  have hH : fixedCurveCyclicKernelMap σ.toRingHom (W.baseChange L)
      (W.map_baseChange σ.toAlgHom) N H = H := by
    apply Subtype.ext
    rw [fixedCurveCyclicKernelMap_coe, fixedCurvePointMap_galois]
    change (S.val.map (pointMapHom (algebraMap F L) W)).map (Point.map (W' := W) σ.toAlgHom) =
      S.val.map (pointMapHom (algebraMap F L) W)
    have hf (P : W.toAffine.Point) :
        Point.map (W' := W) σ.toAlgHom (pointMapHom (algebraMap F L) W P) =
          pointMapHom (algebraMap F L) W P :=
      Point.map_baseChange (W' := W) (F := F) σ.toAlgHom P
    ext Q
    constructor
    · rintro ⟨_, ⟨P, hP, rfl⟩, rfl⟩
      exact ⟨P, hP, (hf P).symm⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨_, ⟨P, hP, rfl⟩, hf P⟩
  have h := cyclicQuotientJ_galois W σ N hN H
  rw [hH] at h
  exact h.symm

end
end Dubon2026.SourceEllipticVelu
