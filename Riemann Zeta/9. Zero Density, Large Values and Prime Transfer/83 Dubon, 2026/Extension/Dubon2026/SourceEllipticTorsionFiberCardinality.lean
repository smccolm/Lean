import Dubon2026.SourceEllipticDoubleFiberCount

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular good reduction
-> reverse genus -> finite exceptional fibers -> elliptic cyclic-subgroup
inertia -> actual n-torsion cardinality. The native division-polynomial
degrees and the proved point multiplication formula control actual point
fibers. Native perfect-field separability replaces the archive's generic
squarefree helpers, and one general surjectivity proof replaces its two
duplicated odd/general proofs. The torsion group is the native multiplication
homomorphism kernel. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean. -/
namespace Dubon2026.SourceEllipticTorsion
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open Dubon2026.SourceEllipticPointFormula
noncomputable section
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)
variable [IsAlgClosed K]

/-- Two disjoint generic fibers give the count for every multiplier prime to the characteristic. -/
theorem card_nTorsion [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (nTorsion W (K := K) n) = n ^ 2 := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨Q, hQQ, hQ⟩ := exists_double_fiber_card W hn
  have hdisj : Disjoint (fun P : (W.baseChange K).toAffine.Point => n • P = Q)
      (fun P : (W.baseChange K).toAffine.Point => n • P = -Q) := by
    rw [Pi.disjoint_iff]
    intro P
    rw [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩
    exact hQQ (h1 ▸ h2)
  have e := subtypeOrEquiv (fun P : (W.baseChange K).toAffine.Point => n • P = Q)
    (fun P : (W.baseChange K).toAffine.Point => n • P = -Q) hdisj
  rw [Nat.card_congr e] at hQ
  haveI hfinsum : Finite ({P : (W.baseChange K).toAffine.Point // n • P = Q} ⊕
      {P : (W.baseChange K).toAffine.Point // n • P = -Q}) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hQ]
    exact mul_ne_zero two_ne_zero (pow_ne_zero 2 hn0)
  haveI : Finite {P : (W.baseChange K).toAffine.Point // n • P = Q} :=
    Finite.of_injective
      (Sum.inl : {P : (W.baseChange K).toAffine.Point // n • P = Q} →
        {P : (W.baseChange K).toAffine.Point // n • P = Q} ⊕ {P : (W.baseChange K).toAffine.Point // n • P = -Q})
      Sum.inl_injective
  haveI : Finite {P : (W.baseChange K).toAffine.Point // n • P = -Q} :=
    Finite.of_injective
      (Sum.inr : {P : (W.baseChange K).toAffine.Point // n • P = -Q} →
        {P : (W.baseChange K).toAffine.Point // n • P = Q} ⊕ {P : (W.baseChange K).toAffine.Point // n • P = -Q})
      Sum.inr_injective
  rw [Nat.card_sum, card_smul_fiber_all W hn Q, card_smul_fiber_all W hn (-Q),
    ← two_mul] at hQ
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hQ

end
end Dubon2026.SourceEllipticTorsion
