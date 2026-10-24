import Dubon2026.SourceEllipticFullTorsionKernelMap
import Dubon2026.SourceEllipticCyclicRootDescent

/-! Exact modular roots over the actual full-torsion coefficient field
are in bijection with its actual cyclic subgroups. This removes the ambient
algebraically closed field assumption from the required DUB-17/18 root
correspondence. The displayed algebraic-closure image is the existing
literal cyclic quotient value, not an arbitrary enumeration of roots. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial SourceFunctionField SourceFunctionField.IntegralJCoordinate
noncomputable section

theorem exists_cyclicRootEquiv_of_full_torsion
    {K F L : Type*} [Field K] [IsAlgClosed K] [Field F] [Field L]
    [DecidableEq F] [DecidableEq L] [Algebra K F] [Algebra F L] [Algebra K L]
    [IsScalarTower K F L] [IsAlgClosed L] [IsAlgClosure F L]
    (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (W : WeierstrassCurve F) [W.IsElliptic] (hj : Transcendental K W.j)
    (hcard : Nat.card {P : W.toAffine.Point // N • P = 0} = N ^ 2) :
    let hNL : (N : L) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap K L)).mpr hNK
    ∃ Θ : {S : AddSubgroup W.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
      {y : F // (relationAtSeed (modularPolynomial N) W.j).IsRoot y},
      ∀ S, algebraMap F L (Θ S).val = cyclicQuotientJ (W.baseChange L) N hNL
        (primeCyclicKernelMap (algebraMap F L) W N S) := by
  intro hNL
  have hd := exists_cyclicQuotientJ_descent (L := L) N hNK W hj
  let f : {S : AddSubgroup W.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} →
      {y : F // (relationAtSeed (modularPolynomial N) W.j).IsRoot y} :=
    fun S => ⟨(hd S).choose, (hd S).choose_spec.1⟩
  have hf (S) : algebraMap F L (f S).val = cyclicQuotientJ (W.baseChange L) N hNL
      (primeCyclicKernelMap (algebraMap F L) W N S) := (hd S).choose_spec.2
  have hjL : Transcendental K (W.baseChange L).j := by
    change Transcendental K (W.map (algebraMap F L)).j
    rw [map_j]
    exact (transcendental_algebraMap_iff (algebraMap F L).injective).mpr hj
  have hb := cyclicQuotientJ_bijOn_transcendental N hNK (W.baseChange L) hjL
  have hNF : (N : F) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap K F)).mpr hNK
  have hk := cyclicKernelMap_bijective_of_full_torsion (algebraMap F L) W N hNF hcard
  have hinj : Function.Injective f := by
    intro S T h
    have hc := congrArg (fun y => algebraMap F L y.val) h
    change algebraMap F L (f S).val = algebraMap F L (f T).val at hc
    rw [hf, hf] at hc
    exact hk.1 (hb.injOn (Set.mem_univ _) (Set.mem_univ _) hc)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hyL : (relationAtSeed (modularPolynomial N) (W.baseChange L).j).IsRoot
        (algebraMap F L y) := by
      change (relationAtSeed (modularPolynomial N) (W.map (algebraMap F L)).j).IsRoot _
      rw [map_j, ← relationAtSeed_map, IsRoot.def, eval_map, eval₂_hom,
        hy.eq_zero, map_zero]
    obtain ⟨T, _, hT⟩ := hb.surjOn hyL
    obtain ⟨S, rfl⟩ := hk.2 T
    refine ⟨S, Subtype.ext ((algebraMap F L).injective ?_)⟩
    exact (hf S).trans hT
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end
end Dubon2026.SourceEllipticVelu
