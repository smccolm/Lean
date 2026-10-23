import Dubon2026.SourceEllipticTorsionCardinality
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Factorization.Induction

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
theorem nonempty_zmodSqAddEquiv_of_card_eq_sq {p : ℕ} (hp : p.Prime)
    (M : Type*) [AddCommGroup M] [Module (ZMod p) M]
    (hcard : Nat.card M = p ^ 2) :
    Nonempty ((ZMod p × ZMod p) ≃+ M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite M :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod p) M = 2 := by
    have hcard2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := M)
    rw [hcard, Nat.card_zmod] at hcard2
    exact (Nat.pow_right_injective hp.two_le hcard2).symm
  exact ⟨((Module.finBasisOfFinrankEq (ZMod p) M hfr).equivFun.trans
    (LinearEquiv.finTwoArrow (R := ZMod p) (M := ZMod p))).symm.toAddEquiv⟩

theorem forall_exists_zsmul_pair_of_step {M : Type*} [AddCommGroup M] {p k : ℕ} {x y : M}
    (hexp : ∀ t : M, p ^ k • t = 0)
    (hstep : ∀ t : M, ∃ (a b : ℤ) (s : M), t = a • x + b • y + (p : ℤ) • s) :
    ∀ t : M, ∃ a b : ℤ, t = a • x + b • y := by
  have hiter : ∀ (j : ℕ) (t : M), ∃ (a b : ℤ) (s : M),
      t = a • x + b • y + ((p : ℤ)) ^ j • s := by
    intro j
    induction j with
    | zero =>
      intro t
      exact ⟨0, 0, t, by simp⟩
    | succ j ih =>
      intro t
      obtain ⟨a, b, s, hs⟩ := ih t
      obtain ⟨a', b', s', hs'⟩ := hstep s
      refine ⟨a + (p : ℤ) ^ j * a', b + (p : ℤ) ^ j * b', s', ?_⟩
      calc t = a • x + b • y + (p : ℤ) ^ j • s := hs
        _ = a • x + b • y + (p : ℤ) ^ j • (a' • x + b' • y + (p : ℤ) • s') := by rw [← hs']
        _ = a • x + b • y + (((p : ℤ) ^ j * a') • x + ((p : ℤ) ^ j * b') • y
              + ((p : ℤ) ^ j * (p : ℤ)) • s') := by
            rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
        _ = (a + (p : ℤ) ^ j * a') • x + (b + (p : ℤ) ^ j * b') • y
              + (p : ℤ) ^ (j + 1) • s' := by
            rw [add_smul, add_smul, pow_succ]
            abel
  intro t
  obtain ⟨a, b, s, hs⟩ := hiter k t
  refine ⟨a, b, ?_⟩
  have hzero : ((p : ℤ)) ^ k • s = 0 := by
    have hcast : ((p : ℤ)) ^ k • s = (p ^ k : ℕ) • s := by
      rw [← Nat.cast_pow, natCast_zsmul]
    rw [hcast]
    exact hexp s
  rw [hs, hzero, add_zero]

theorem nonempty_zmodPowSqAddEquiv_of_span_pair {n : ℕ} (hn : n ≠ 0)
    (M : Type*) [AddCommGroup M] [Module (ZMod n) M]
    (hcard : Nat.card M = n ^ 2) (x y : M)
    (hgen : ∀ t : M, ∃ a b : ℤ, t = a • x + b • y) :
    Nonempty ((ZMod n × ZMod n) ≃+ M) := by
  haveI : NeZero n := ⟨hn⟩
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hn)
  let f : (ZMod n × ZMod n) →+ M := AddMonoidHom.mk' (fun c => c.1 • x + c.2 • y) (by
    intro c d
    show (c.1 + d.1) • x + (c.2 + d.2) • y = (c.1 • x + c.2 • y) + (d.1 • x + d.2 • y)
    rw [add_smul, add_smul]
    abel)
  have hfsurj : Function.Surjective f := by
    intro t
    obtain ⟨a, b, ht⟩ := hgen t
    refine ⟨((a : ZMod n), (b : ZMod n)), ?_⟩
    show ((a : ℤ) : ZMod n) • x + ((b : ℤ) : ZMod n) • y = t
    rw [Int.cast_smul_eq_zsmul (ZMod n) a x, Int.cast_smul_eq_zsmul (ZMod n) b y, ht]
  have hcards : Nat.card (ZMod n × ZMod n) = Nat.card M := by
    rw [Nat.card_prod, Nat.card_zmod, hcard]
    ring
  exact ⟨AddEquiv.ofBijective f
    ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hfsurj, hcards⟩)⟩


end
end Dubon2026.SourceEllipticTorsionStructure
