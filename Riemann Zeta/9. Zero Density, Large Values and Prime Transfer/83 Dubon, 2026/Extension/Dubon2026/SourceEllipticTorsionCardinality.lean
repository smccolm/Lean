import Dubon2026.SourceEllipticTorsionFiberCardinality

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
theorem actual_torsion_cardinality {F K : Type*} [Field F] [Field K] [Algebra F K]
    [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W.baseChange K).toAffine.Point n) = n ^ 2 := by
  rw [← card_nTorsion W (K := K) hn]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun P => ?_)
  change P ∈ Submodule.torsionBy ℤ (W.baseChange K).toAffine.Point (n : ℤ) ↔
    P ∈ nTorsion W (K := K) n
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  rfl

end Dubon2026.SourceEllipticTorsion
