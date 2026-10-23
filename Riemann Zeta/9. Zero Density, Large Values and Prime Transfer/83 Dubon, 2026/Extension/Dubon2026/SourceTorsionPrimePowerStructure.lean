import Dubon2026.SourceTorsionPrimeLinearAlgebra

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
variable {A : Type*} [AddCommGroup A]

private def pSmulHomKerEquivTorsionBy (M : Type*) [AddCommGroup M] (p : ℕ) :
    (nsmulAddMonoidHom p : M →+ M).ker ≃ Submodule.torsionBy ℤ M (p : ℤ) :=
  Equiv.subtypeEquivRight fun t => by
    change p • t = 0 ↔ (p : ℤ) • t = 0
    rw [natCast_zsmul]

theorem nonempty_zmodPowSqAddEquiv_of_card_pow {p : ℕ} (hp : p.Prime) (k : ℕ)
    (M : Type*) [AddCommGroup M]
    (hexp : ∀ t : M, p ^ k • t = 0)
    (hcard : Nat.card M = p ^ (2 * k))
    (hcardp : Nat.card (Submodule.torsionBy ℤ M (p : ℤ)) = p ^ 2) :
    Nonempty ((ZMod (p ^ k) × ZMod (p ^ k)) ≃+ M) := by
  haveI : Finite M :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  ·

    exfalso
    have h1 : Nat.card M = 1 := by simpa using hcard
    have hle : Nat.card (Submodule.torsionBy ℤ M (p : ℤ)) ≤ Nat.card M :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    rw [hcardp, h1] at hle
    exact absurd (le_trans (Nat.pow_le_pow_left hp.two_le 2) hle) (by norm_num)
  ·
    set K : AddSubgroup M := ((nsmulAddMonoidHom p : M →+ M)).ker with hKdef
    set R : AddSubgroup M := ((nsmulAddMonoidHom p : M →+ M)).range with hRdef
    haveI : Nonempty R := ⟨0⟩

    have hKcard : Nat.card K = p ^ 2 := by
      rw [hKdef, Nat.card_congr (pSmulHomKerEquivTorsionBy M p)]
      exact hcardp

    have hMK : Nat.card K * K.index = Nat.card M := AddSubgroup.card_mul_index K
    have hKR : K.index = Nat.card R := by
      rw [hKdef, hRdef]
      exact AddSubgroup.index_ker ((nsmulAddMonoidHom p : M →+ M))
    have hMR : Nat.card R * R.index = Nat.card M := AddSubgroup.card_mul_index R
    have hRQ : R.index = Nat.card (M ⧸ R) := AddSubgroup.index_eq_card R
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have hQcard : Nat.card (M ⧸ R) = p ^ 2 := by
      have h1 : Nat.card K * Nat.card R = Nat.card M := by rw [← hKR]; exact hMK
      have h2 : Nat.card R * Nat.card (M ⧸ R) = Nat.card M := by rw [← hRQ]; exact hMR
      have h3 : Nat.card R * Nat.card (M ⧸ R) = Nat.card R * Nat.card K := by
        rw [h2, ← h1, mul_comm]
      rw [Nat.eq_of_mul_eq_mul_left hRpos h3, hKcard]

    have hQkill : ∀ q : M ⧸ R, p • q = 0 := by
      intro q
      obtain ⟨t, rfl⟩ := QuotientAddGroup.mk'_surjective R q
      rw [← map_nsmul]
      have hmem : p • t ∈ R := by
        rw [hRdef]
        exact AddMonoidHom.mem_range.mpr ⟨t, nsmulAddMonoidHom_apply p t⟩
      rwa [← QuotientAddGroup.ker_mk' R, AddMonoidHom.mem_ker] at hmem

    obtain ⟨E⟩ : Nonempty ((ZMod p × ZMod p) ≃+ (M ⧸ R)) := by
      letI : Module (ZMod p) (M ⧸ R) := AddCommGroup.zmodModule hQkill
      exact nonempty_zmodSqAddEquiv_of_card_eq_sq hp (M ⧸ R) hQcard

    obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective R (E ((1 : ZMod p), (0 : ZMod p)))
    obtain ⟨y, hy⟩ := QuotientAddGroup.mk'_surjective R (E ((0 : ZMod p), (1 : ZMod p)))

    have hstep : ∀ t : M, ∃ (a b : ℤ) (s : M), t = a • x + b • y + (p : ℤ) • s := by
      intro t
      obtain ⟨a, ha⟩ := ZMod.intCast_surjective ((E.symm ((QuotientAddGroup.mk' R) t)).1)
      obtain ⟨b, hb⟩ := ZMod.intCast_surjective ((E.symm ((QuotientAddGroup.mk' R) t)).2)
      have hxy : (QuotientAddGroup.mk' R) (a • x + b • y) = (QuotientAddGroup.mk' R) t := by
        rw [map_add, map_zsmul, map_zsmul, hx, hy, ← map_zsmul E, ← map_zsmul E, ← map_add E]
        have hpair : a • ((1 : ZMod p), (0 : ZMod p)) + b • ((0 : ZMod p), (1 : ZMod p))
            = E.symm ((QuotientAddGroup.mk' R) t) := by
          apply Prod.ext
          · simpa [Int.smul_one_eq_cast] using ha
          · simpa [Int.smul_one_eq_cast] using hb
        rw [hpair, AddEquiv.apply_symm_apply]
      have h0 : (QuotientAddGroup.mk' R) (t - (a • x + b • y)) = 0 := by
        rw [map_sub, hxy, sub_self]
      have hmem : t - (a • x + b • y) ∈ R := by
        rwa [← QuotientAddGroup.ker_mk' R, AddMonoidHom.mem_ker]
      rw [hRdef] at hmem
      obtain ⟨s, hs⟩ := AddMonoidHom.mem_range.mp hmem
      rw [nsmulAddMonoidHom_apply] at hs
      refine ⟨a, b, s, ?_⟩
      rw [natCast_zsmul, hs]
      abel

    have hgen : ∀ t : M, ∃ a b : ℤ, t = a • x + b • y :=
      forall_exists_zsmul_pair_of_step hexp hstep
    letI : Module (ZMod (p ^ k)) M := AddCommGroup.zmodModule hexp
    exact nonempty_zmodPowSqAddEquiv_of_span_pair (pow_ne_zero k hp.ne_zero) M
      (by rw [hcard, show 2 * k = k * 2 from Nat.mul_comm 2 k, pow_mul]) x y hgen

/-- The p-torsion inside the actual p-power torsion is the ambient p-torsion. -/
def torsionByPowPTorsionEquiv (p k : ℕ) (hk : k ≠ 0) :
    (Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) (p : ℤ)) ≃
      (Submodule.torsionBy ℤ A (p : ℤ)) where
  toFun T := ⟨((T : Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) : A), by
    have hT := T.2
    rw [Submodule.mem_torsionBy_iff] at hT
    rw [Submodule.mem_torsionBy_iff]
    exact congrArg Subtype.val hT⟩
  invFun T := ⟨⟨(T : A), by
      rw [Submodule.mem_torsionBy_iff]
      have hT : (p : ℤ) • (T : A) = 0 := by
        have := T.2
        rwa [Submodule.mem_torsionBy_iff] at this
      have hkk : ((p ^ k : ℕ) : ℤ) = ((p ^ (k - 1) : ℕ) : ℤ) * (p : ℤ) := by
        push_cast
        rw [← pow_succ]
        congr 1
        omega
      rw [hkk, mul_smul, hT, smul_zero]⟩, by
    rw [Submodule.mem_torsionBy_iff]
    apply Subtype.ext
    have hT : (p : ℤ) • (T : A) = 0 := by
      have := T.2
      rwa [Submodule.mem_torsionBy_iff] at this
    exact hT⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem nonempty_zmodPowSqAddEquiv_torsionBy_of_card_pow {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : k ≠ 0)
    (hcard : Nat.card (Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) = p ^ (2 * k))
    (hcardp : Nat.card (Submodule.torsionBy ℤ A (p : ℤ)) = p ^ 2) :
    Nonempty ((ZMod (p ^ k) × ZMod (p ^ k)) ≃+ Submodule.torsionBy ℤ A ((p ^ k : ℕ) : ℤ)) := by
  refine nonempty_zmodPowSqAddEquiv_of_card_pow hp k _ ?_ hcard ?_
  · intro t
    rw [← Nat.cast_smul_eq_nsmul ℤ (p ^ k) t]
    exact Submodule.smul_torsionBy _ t
  · rw [← hcardp]
    exact Nat.card_congr (torsionByPowPTorsionEquiv p k hk)


end
end Dubon2026.SourceEllipticTorsionStructure
