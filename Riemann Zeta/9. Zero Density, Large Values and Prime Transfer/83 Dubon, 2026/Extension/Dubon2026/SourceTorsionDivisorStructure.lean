import Dubon2026.SourceTorsionCoprimeStructure

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
theorem nonempty_zmodSqAddEquiv_torsionBy_one {A : Type*} [AddCommGroup A] :
    Nonempty ((ZMod 1 × ZMod 1) ≃+ Submodule.torsionBy ℤ A ((1 : ℕ) : ℤ)) := by
  haveI : Subsingleton (Submodule.torsionBy ℤ A ((1 : ℕ) : ℤ)) := by
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx := x.2; have hy := y.2
    rw [Submodule.mem_torsionBy_iff] at hx hy
    simp only [Nat.cast_one, one_smul] at hx hy
    rw [hx, hy]
  refine ⟨AddEquiv.ofBijective (0 : ZMod 1 × ZMod 1 →+ Submodule.torsionBy ℤ A ((1 : ℕ) : ℤ)) ⟨?_, ?_⟩⟩
  · intro a b _; exact Subsingleton.elim a b
  · intro y; exact ⟨0, Subsingleton.elim _ _⟩

theorem torsion_structure_of_divisor_cardinality
    {A : Type*} [AddCommGroup A] {n : ℕ} (hn : n ≠ 0)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ 2) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      have hc : Nat.card (Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) = p ^ (2 * k) := by
        rw [hcard (p ^ k) dvd_rfl, ← pow_mul, Nat.mul_comm]
      have hcp : Nat.card (Submodule.torsionBy ℤ A (p : ℤ)) = p ^ 2 :=
        hcard p (dvd_pow_self p hk.ne')
      exact nonempty_zmodPowSqAddEquiv_torsionBy_of_card_pow hp hk.ne' hc hcp
  | zero => exact absurd rfl hn
  | one => exact nonempty_zmodSqAddEquiv_torsionBy_one
  | coprime a b _ _ hab iha ihb =>
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hn
      have hb0 : b ≠ 0 := right_ne_zero_of_mul hn
      exact nonempty_zmodSqAddEquiv_torsionBy_mul_of_coprime hab
        (iha ha0 fun d hd => hcard d (hd.mul_right b))
        (ihb hb0 fun d hd => hcard d (hd.mul_left a))

end
end Dubon2026.SourceEllipticTorsionStructure
