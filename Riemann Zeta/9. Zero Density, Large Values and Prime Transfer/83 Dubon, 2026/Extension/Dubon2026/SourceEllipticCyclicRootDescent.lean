import Dubon2026.SourceSeparableFixedRootDescent
import Dubon2026.SourceEllipticCyclicRootFixed
import Dubon2026.SourceEllipticAllLevelCyclicRootBijection

/-! Descend the actual cyclic quotient value to the original coefficient
field. The proved generic modular polynomial is separable; native point
base change makes the literal quotient value fixed. Thus no rationality
certificate for quotient values is needed in the DUB-17/18 finite-field
modular-root and place-fiber comparison. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial SourceFunctionField SourceFunctionField.IntegralJCoordinate
noncomputable section

theorem exists_cyclicQuotientJ_descent
    {K F L : Type*} [Field K] [IsAlgClosed K] [Field F] [Field L]
    [DecidableEq F] [DecidableEq L] [Algebra K F] [Algebra F L] [Algebra K L]
    [IsScalarTower K F L] [IsAlgClosed L] [IsAlgClosure F L]
    (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (W : WeierstrassCurve F) [W.IsElliptic] (hj : Transcendental K W.j)
    (S : {S : AddSubgroup W.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
    let hNL : (N : L) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap K L)).mpr hNK
    ∃ y : F, (relationAtSeed (modularPolynomial N) W.j).IsRoot y ∧
      algebraMap F L y = cyclicQuotientJ (W.baseChange L) N hNL
        (primeCyclicKernelMap (algebraMap F L) W N S) := by
  intro hNL
  let p := relationAtSeed (modularPolynomial N) W.j
  have hjL : Transcendental K (W.baseChange L).j := by
    change Transcendental K (W.map (algebraMap F L)).j
    rw [map_j]
    exact (transcendental_algebraMap_iff (algebraMap F L).injective).mpr hj
  have he : relationAtSeed (modularPolynomial N) (W.baseChange L).j =
      p.map (algebraMap F L) := by
    change relationAtSeed (modularPolynomial N) (W.map (algebraMap F L)).j = _
    rw [map_j, relationAtSeed_map]
  let q := cyclicQuotientJ (W.baseChange L) N hNL
    (primeCyclicKernelMap (algebraMap F L) W N S)
  have hroot : (p.map (algebraMap F L)).IsRoot q := by
    rw [← he]
    exact (cyclicQuotientJ_bijOn_transcendental N hNK (W.baseChange L) hjL).mapsTo (Set.mem_univ _)
  obtain ⟨y, hy⟩ := separable_root_mem_range_of_fixed q p
    (modularPolynomial_separable_transcendental N hNK W.j hj) hroot
    (cyclicQuotientJ_baseChange_fixed W N hNL S)
  refine ⟨y, ?_, hy⟩
  rw [← hy, IsRoot.def, eval_map, eval₂_hom,
    map_eq_zero_iff _ (algebraMap F L).injective] at hroot
  exact hroot

end
end Dubon2026.SourceEllipticVelu
