import Dubon2026.SourceEllipticFullTorsionKernelMap

/-! The existing full-torsion cyclic-kernel bijection and positive Dedekind
psi count supply an actual cyclic subgroup. This gives an original modular
embedding into the DUB-17/18 auxiliary normal fixed field without assuming
that such an embedding exists. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section

theorem nonempty_cyclic_subgroups_of_full_torsion
    {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    [IsAlgClosed L] [Algebra F L] (W : WeierstrassCurve F) [W.IsElliptic]
    (N : ℕ) (hN : (N : F) ≠ 0)
    (hcard : Nat.card {P : W.toAffine.Point // N • P = 0} = N ^ 2) :
    Nonempty {S : AddSubgroup W.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} := by
  have hNL : (N : L) ≠ 0 := by
    simpa only [map_natCast] using (_root_.map_ne_zero (algebraMap F L)).mpr hN
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  have hpos : 0 < Nat.card
      {S : AddSubgroup (W.baseChange L).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} := by
    rw [SourceEllipticCyclicCount.actual_cyclic_subgroup_cardinality W hNL]
    exact SourceLevelProjective.dedekindPsi_pos hN0
  obtain ⟨T⟩ := (Nat.card_pos_iff.mp hpos).1
  obtain ⟨S, _⟩ := (cyclicKernelMap_bijective_of_full_torsion (algebraMap F L) W N hN hcard).2 T
  exact ⟨S⟩

end
end Dubon2026.SourceEllipticVelu
