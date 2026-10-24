import Dubon2026.SourceCyclicPrimeTorsionCriterion
import Dubon2026.SourceLevelGenusNumerics
import Mathlib.Tactic

/-! DUB-17/18 -> reverse genus -> exceptional j-fiber census ->
cyclic-subgroup fixed points of the order-two/order-three automorphisms.
The literal quadratic eigenkernels in the existing rank-two torsion
coordinates are used. The quadratic identity and non-scalar action on
prime torsion remain explicit upstream inputs until proved for the
specific elliptic automorphisms. No exceptional-fiber count is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo.lean. -/
namespace Dubon2026.SourceQuadraticCyclicCount
noncomputable section
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem nsmul_self_eq_zero (v : (ZMod n × ZMod n)) : n • v = 0 := by
  ext <;> simp [nsmul_eq_mul]

theorem map_zmod_smul (τ : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) (c : ZMod n) (v : (ZMod n × ZMod n)) : τ (c • v) = c • τ v := by
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem eq_zero_of_smul_eq_zero {v : (ZMod n × ZMod n)} (hv : addOrderOf v = n) {c : ZMod n} (hc : c • v = 0) : c = 0 := by
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul] at hc
  have hdvd : addOrderOf v ∣ c.val := addOrderOf_dvd_of_nsmul_eq_zero hc
  rw [hv] at hdvd
  have hval : c.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt c)
  exact (ZMod.val_eq_zero c).mp hval

/-- The actual additive subgroup on which the given torsion map acts by the scalar k. -/
def eig (τ : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) (k : ZMod n) : AddSubgroup (ZMod n × ZMod n) where
  carrier := {v | τ v = k • v}
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, smul_zero]
  add_mem' ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [map_add, ha, hb, smul_add]
  neg_mem' ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [map_neg, ha, smul_neg]

omit [NeZero n] in
theorem mem_eig (τ : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) (k : ZMod n) (v : (ZMod n × ZMod n)) : v ∈ eig τ k ↔ τ v = k • v := Iff.rfl

/-- The difference between the actual torsion endomorphism and scalar multiplication by k. -/
def shift (τ : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) (k : ZMod n) : (ZMod n × ZMod n) →+ (ZMod n × ZMod n) where
  toFun v := τ v - k • v
  map_zero' := by simp only [map_zero, smul_zero, sub_zero]
  map_add' v w := by simp only [map_add, smul_add]; abel

omit [NeZero n] in
theorem shift_apply (τ : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) (k : ZMod n) (v : (ZMod n × ZMod n)) : shift τ k v = τ v - k • v := rfl

omit [NeZero n] in
theorem ker_shift (τ : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) (k : ZMod n) : (shift τ k).ker = eig τ k := by
  ext v
  rw [AddMonoidHom.mem_ker, shift_apply, sub_eq_zero, mem_eig]

section Quadratic

variable (τ : (ZMod n × ZMod n) →+ (ZMod n × ZMod n)) (s : ZMod n) (hτ : ∀ v, τ (τ v) = s • τ v - v)
include hτ

omit [NeZero n] in
theorem τ_injective : Function.Injective τ := fun a b h => by
  have ha : a = s • τ a - τ (τ a) := by rw [hτ]; abel
  have hb : b = s • τ b - τ (τ b) := by rw [hτ]; abel
  rw [ha, hb, h]

theorem root_of_eigen {v : (ZMod n × ZMod n)} (hv : addOrderOf v = n) {k : ZMod n} (hk : τ v = k • v) :
    k * k = s * k - 1 := by
  have h1 : τ (τ v) = (k * k) • v := by rw [hk, map_zmod_smul, hk, smul_smul]
  have h2 : τ (τ v) = (s * k - 1) • v := by rw [hτ, hk, smul_smul, sub_smul, one_smul]
  have h3 : (k * k - (s * k - 1)) • v = 0 := by rw [sub_smul, ← h1, ← h2, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_smul_eq_zero hv h3)

theorem range_shift_le {k : ZMod n} (hk : k * k = s * k - 1) :
    (shift τ k).range ≤ eig τ (s - k) := by
  rintro w ⟨v, rfl⟩
  rw [mem_eig, shift_apply, map_sub, map_zmod_smul, hτ, smul_sub, smul_smul,
    show (s - k) * k = 1 by rw [sub_mul, hk]; ring, one_smul, sub_smul]
  abel

theorem sq_le_card_mul_card {k : ZMod n} (hk : k * k = s * k - 1) :
    n ^ 2 ≤ Nat.card (eig τ k) * Nat.card (eig τ (s - k)) := by
  have hN2 : Nat.card (ZMod n × ZMod n) = n ^ 2 := by rw [Nat.card_prod, Nat.card_zmod, sq]
  have hfirst : Nat.card (ZMod n × ZMod n) = Nat.card (shift τ k).ker * Nat.card (shift τ k).range := by
    rw [mul_comm, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (shift τ k)).toEquiv,
      ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
  rw [← hN2, hfirst, ker_shift]
  exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective
    (AddSubgroup.inclusion (range_shift_le τ s hτ hk)) (AddSubgroup.inclusion_injective _))

theorem map_eig_eq (k : ZMod n) : (eig τ k).map τ = eig τ k := by
  haveI : Finite (eig τ k) := inferInstance
  have hle : (eig τ k).map τ ≤ eig τ k := by
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_eig] at hv
    rw [mem_eig, hv, map_zmod_smul, hv]
  exact AddSubgroup.eq_of_le_of_card_ge hle
    (Nat.card_congr ((eig τ k).equivMapOfInjective τ (τ_injective τ s hτ)).toEquiv).le

end Quadratic

omit [NeZero n] in
theorem card_pTorsion_le {p : ℕ} (hp : p.Prime) :
    Nat.card {v : (ZMod n × ZMod n) // p • v = 0} ≤ p ^ 2 := by
  have key : Nat.card {x : ZMod n // p • x = 0} ≤ p := by
    let S : AddSubgroup (ZMod n) :=
      { carrier := {x | p • x = 0}, zero_mem' := by simp,
        add_mem' := fun {a b} ha hb =>
          show p • (a + b) = 0 by rw [nsmul_add, ha, hb, add_zero],
        neg_mem' := fun {a} ha =>
          show p • (-a) = 0 by rw [smul_neg, ha, neg_zero] }
    haveI : IsAddCyclic S := AddSubgroup.isAddCyclic S
    have hexp : AddMonoid.exponent S ∣ p :=
      AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero (fun g => Subtype.ext g.2)
    calc Nat.card {x : ZMod n // p • x = 0} = Nat.card S := rfl
      _ = AddMonoid.exponent S := IsAddCyclic.exponent_eq_card.symm
      _ ≤ p := Nat.le_of_dvd hp.pos hexp
  have e : {v : (ZMod n × ZMod n) // p • v = 0} ≃ {x : ZMod n // p • x = 0} × {y : ZMod n // p • y = 0} := by
    refine ⟨fun v => (⟨v.1.1, (Prod.mk_inj.mp v.2).1⟩, ⟨v.1.2, (Prod.mk_inj.mp v.2).2⟩),
      fun z => ⟨(z.1.1, z.2.1), Prod.ext z.1.2 z.2.2⟩, ?_, ?_⟩
    · intro v; exact Subtype.ext rfl
    · intro z; exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  rw [Nat.card_congr e, Nat.card_prod, sq]
  exact Nat.mul_le_mul key key

end
end Dubon2026.SourceQuadraticCyclicCount
