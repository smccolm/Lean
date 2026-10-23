import Dubon2026.SourceEllipticSequencePermutation

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction ->
reverse genus -> finite exceptional-fiber census -> elliptic cyclic-subgroup
inertia orbits -> actual n-torsion structure -> n-torsion cardinality ->
division-polynomial multiplication formula -> elliptic-sequence identities.
Selected from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_WeierstrassCurve_EDSEngine.lean. The pinned native
IsEllSequence is exactly the reference compatibility predicate. These
identities supply the required multiplication proof; the actual torsion
cardinality and finite-fiber census are not yet proved. -/
namespace Dubon2026.SourceEllipticSequence

variable {R : Type*} [CommRing R] {W : ℤ → R}
open Int
open scoped nonZeroDivisors





variable (ell : IsEllSequence W)

include ell in
theorem ell_oddRec (m : ℤ) : OddRec W m := (rel₃_iff_oddRec W m).mp (ell _ _ _)
include ell in
theorem ell_evenRec (m : ℤ) : EvenRec W m := (rel₃_iff_evenRec W m).mp (ell _ _ _)

include ell in

theorem ell_zero (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have := ell m m (2 * m)
  rw [add_comm, sub_self, sub_self, ← two_mul, mul_comm (W _)] at this
  exact (mem_nonZeroDivisors_iff.mp mem).2 _
    ((mem_nonZeroDivisors_iff.mp (pow_mem mem 2)).2 _ this)
include ell in
theorem ell_sub_add_neg_sub_mul_eq_zero (m n r : ℤ) :
    (W (m - n) + W (-(m - n))) * W (m + n) * W r ^ 2 = 0 := by
  have := congr($(ell m n r) + $(ell n m r))
  rw [add_comm n, ← right_distrib, ← left_distrib, mul_comm (W _)] at this
  convert this using 4 <;> ring_nf

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)

include ell one two in

theorem ell_neg (m : ℤ) : W (-m) = - W m := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨m, rfl|rfl⟩ := m.even_or_odd'
  on_goal 1 => apply (mem_nonZeroDivisors_iff.mp two).2
  on_goal 2 => apply (mem_nonZeroDivisors_iff.mp one).2
  all_goals apply (mem_nonZeroDivisors_iff.mp (pow_mem one 2)).2
  · convert ell_sub_add_neg_sub_mul_eq_zero ell (1 - m) (m + 1) 1 using 2; ring_nf
  · convert ell_sub_add_neg_sub_mul_eq_zero ell (-m) (m + 1) 1 using 2; ring_nf
include ell one two in
theorem ell_rel₄ {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : rel₄ W a b c d = 0 :=
  rel₄_of_oddRec_evenRec ((ell_neg ell) one two) ((ell_zero ell) 1 two) one two
    (fun _ _ ↦ (ell_oddRec ell) _) (fun _ _ ↦ (ell_evenRec ell) _) same
include ell one two in
theorem ell_net (p q r s : ℤ) : net W p q r s = 0 := by
  rw [net_eq_rel₄]
  refine (ell_rel₄ ell) one two ?_
  simp_rw [HaveSameParity₄, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, true_and]

end Dubon2026.SourceEllipticSequence
