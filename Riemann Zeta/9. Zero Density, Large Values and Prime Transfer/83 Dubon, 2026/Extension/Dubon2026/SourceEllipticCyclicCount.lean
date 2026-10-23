import Dubon2026.SourceCyclicTorsionTransport

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction
-> reverse genus -> finite exceptional fibers -> elliptic cyclic-subgroup
inertia -> actual number of cyclic subgroups. Reuse the already proved
projective-line cardinality and Dedekind psi function without redefining
either. Primitive pairs use native IsCoprime. The actual torsion structure
transports these subgroups into the original elliptic point group.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean and
S_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy.lean. -/
namespace Dubon2026.SourceEllipticCyclicCount
open AddSubgroup Dubon2026.SourceLevelProjective
noncomputable section
/-- The actual elliptic point group has exactly psi(n) cyclic subgroups of order n. -/
theorem actual_cyclic_subgroup_cardinality {F K : Type*} [Field F] [Field K] [Algebra F K]
    [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card {H : AddSubgroup (W.baseChange K).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = n} = dedekindPsi n := by
  haveI : NeZero n := ⟨by rintro rfl; exact hn Nat.cast_zero⟩
  obtain ⟨e⟩ := Dubon2026.SourceEllipticTorsionStructure.actual_torsion_structure W hn
  exact natCard_cyclicSubgroups_of_torsion_equiv n e

end
end Dubon2026.SourceEllipticCyclicCount
