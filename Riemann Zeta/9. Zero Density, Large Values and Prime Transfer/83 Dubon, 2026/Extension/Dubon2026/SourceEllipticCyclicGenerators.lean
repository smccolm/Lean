import Dubon2026.SourceEllipticCyclicCount

/-! Enumerate the actual prime-order cyclic subgroups of an elliptic curve
by generators, using the proved torsion structure and Dedekind-psi count.
This supplies the indexing family for the odd-prime quotient product, whose
cyclic-root correspondence is needed for the inertia census and good reduction
on DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2. No polynomial-root claim is assumed.
-/

namespace Dubon2026.SourceEllipticCyclicCount
open WeierstrassCurve
noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic]

/-- Every prime-order cyclic subgroup appears exactly once in this generator family. -/
theorem exists_prime_cyclic_generators (p : ℕ) [hp : Fact p.Prime]
    (hpK : (p : K) ≠ 0) :
    ∃ Q : Fin (p + 1) → (W.baseChange K).toAffine.Point,
      (∀ i, addOrderOf (Q i) = p) ∧
      Function.Injective (fun i => AddSubgroup.zmultiples (Q i)) ∧
      ∀ H : AddSubgroup (W.baseChange K).toAffine.Point,
        IsAddCyclic H → Nat.card H = p → ∃ i, AddSubgroup.zmultiples (Q i) = H := by
  classical
  let C := {H : AddSubgroup (W.baseChange K).toAffine.Point //
    IsAddCyclic H ∧ Nat.card H = p}
  have hcard : Nat.card C = p + 1 := by
    rw [actual_cyclic_subgroup_cardinality W hpK]
    simpa using SourceLevelProjective.dedekindPsi_prime_pow p 1 hp.out (by decide)
  let e : C ≃ Fin (p + 1) :=
    (Nat.equivFinOfCardPos (by rw [hcard]; omega)).trans (finCongr hcard)
  have hg : ∀ H : C, ∃ g : (W.baseChange K).toAffine.Point,
      AddSubgroup.zmultiples g = H.1 := fun H =>
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H.1).mp H.2.1
  choose g hg using hg
  refine ⟨fun i => g (e.symm i), ?_, ?_, ?_⟩
  · intro i
    have h := Nat.card_zmultiples (g (e.symm i))
    rw [hg, (e.symm i).2.2] at h
    exact h.symm
  · intro i j h
    simp only [hg] at h
    exact e.symm.injective (Subtype.ext h)
  · intro H hc hn
    refine ⟨e ⟨H, hc, hn⟩, ?_⟩
    simpa only [e.symm_apply_apply] using hg (⟨H, hc, hn⟩ : C)

end
end Dubon2026.SourceEllipticCyclicCount
