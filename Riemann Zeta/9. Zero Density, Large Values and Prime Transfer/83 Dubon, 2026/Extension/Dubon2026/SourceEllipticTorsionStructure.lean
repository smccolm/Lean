import Dubon2026.SourceTorsionDivisorStructure

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction
-> reverse genus -> finite exceptional fibers -> elliptic cyclic-subgroup
inertia -> actual torsion structure. The proved native torsion cardinality
at divisors of n supplies this structure; no torsion basis is assumed.
The pinned native finite-field basis, multiplication homomorphism, quotient
group and Chinese remainder APIs are reused. The archived two-generator
lifting proof avoids a separate development of invariant-factor classification.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq.lean
and S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean. -/
namespace Dubon2026.SourceEllipticTorsionStructure
noncomputable section
theorem actual_torsion_structure
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ (W.baseChange K).toAffine.Point n) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  refine torsion_structure_of_divisor_cardinality hn0 ?_
  intro d hd
  have hdK : (d : K) ≠ 0 := by
    obtain ⟨c, rfl⟩ := hd
    intro h; apply hn; push_cast; rw [h, zero_mul]
  exact Dubon2026.SourceEllipticTorsion.actual_torsion_cardinality W hdK

end
end Dubon2026.SourceEllipticTorsionStructure
