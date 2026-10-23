import Dubon2026.SourceTorsionPrimePowerStructure

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

/-- Bezout coefficients split the actual torsion for a product of coprime multipliers. -/
def torsionByMulCoprimeSplitAddEquiv (M N : ℕ) (a b : ℤ)
    (hab : (M : ℤ) * a + (N : ℤ) * b = 1) :
    Submodule.torsionBy ℤ A ((M * N : ℕ) : ℤ) ≃+
      Submodule.torsionBy ℤ A (M : ℤ) × Submodule.torsionBy ℤ A (N : ℤ) where
  toFun t :=
    (⟨((N : ℤ) * b) • (t : A), by
        have ht : ((M * N : ℕ) : ℤ) • (t : A) = 0 := by
          have h2 := t.2
          rwa [Submodule.mem_torsionBy_iff] at h2
        rw [Submodule.mem_torsionBy_iff, smul_smul,
          show (M : ℤ) * ((N : ℤ) * b) = b * ((M * N : ℕ) : ℤ) by push_cast; ring,
          ← smul_smul, ht, smul_zero]⟩,
     ⟨((M : ℤ) * a) • (t : A), by
        have ht : ((M * N : ℕ) : ℤ) • (t : A) = 0 := by
          have h2 := t.2
          rwa [Submodule.mem_torsionBy_iff] at h2
        rw [Submodule.mem_torsionBy_iff, smul_smul,
          show (N : ℤ) * ((M : ℤ) * a) = a * ((M * N : ℕ) : ℤ) by push_cast; ring,
          ← smul_smul, ht, smul_zero]⟩)
  invFun uv := ⟨(uv.1 : A) + (uv.2 : A), by
    have hu : (M : ℤ) • (uv.1 : A) = 0 := by
      have h2 := uv.1.2
      rwa [Submodule.mem_torsionBy_iff] at h2
    have hv : (N : ℤ) • (uv.2 : A) = 0 := by
      have h2 := uv.2.2
      rwa [Submodule.mem_torsionBy_iff] at h2
    rw [Submodule.mem_torsionBy_iff, smul_add,
      show ((M * N : ℕ) : ℤ) • (uv.1 : A) = 0 by
        rw [show ((M * N : ℕ) : ℤ) = (N : ℤ) * (M : ℤ) by push_cast; ring, ← smul_smul, hu,
          smul_zero],
      show ((M * N : ℕ) : ℤ) • (uv.2 : A) = 0 by
        rw [show ((M * N : ℕ) : ℤ) = (M : ℤ) * (N : ℤ) by push_cast; ring, ← smul_smul, hv,
          smul_zero],
      add_zero]⟩
  left_inv t := by
    apply Subtype.ext
    show ((N : ℤ) * b) • (t : A) + ((M : ℤ) * a) • (t : A) = (t : A)
    rw [← add_smul, show (N : ℤ) * b + (M : ℤ) * a = 1 by linarith [hab], one_smul]
  right_inv uv := by
    have hu : (M : ℤ) • (uv.1 : A) = 0 := by
      have h2 := uv.1.2
      rwa [Submodule.mem_torsionBy_iff] at h2
    have hv : (N : ℤ) • (uv.2 : A) = 0 := by
      have h2 := uv.2.2
      rwa [Submodule.mem_torsionBy_iff] at h2
    apply Prod.ext
    · apply Subtype.ext
      show ((N : ℤ) * b) • ((uv.1 : A) + (uv.2 : A)) = (uv.1 : A)
      rw [smul_add,
        show ((N : ℤ) * b) • (uv.2 : A) = 0 by
          rw [show (N : ℤ) * b = b * (N : ℤ) by ring, ← smul_smul, hv, smul_zero],
        show ((N : ℤ) * b) • (uv.1 : A) = (uv.1 : A) by
          rw [show (N : ℤ) * b = 1 - (M : ℤ) * a by linarith [hab], sub_smul, one_smul,
            show (M : ℤ) * a = a * (M : ℤ) by ring, ← smul_smul, hu, smul_zero, sub_zero],
        add_zero]
    · apply Subtype.ext
      show ((M : ℤ) * a) • ((uv.1 : A) + (uv.2 : A)) = (uv.2 : A)
      rw [smul_add,
        show ((M : ℤ) * a) • (uv.1 : A) = 0 by
          rw [show (M : ℤ) * a = a * (M : ℤ) by ring, ← smul_smul, hu, smul_zero],
        show ((M : ℤ) * a) • (uv.2 : A) = (uv.2 : A) by
          rw [show (M : ℤ) * a = 1 - (N : ℤ) * b by linarith [hab], sub_smul, one_smul,
            show (N : ℤ) * b = b * (N : ℤ) by ring, ← smul_smul, hv, smul_zero, sub_zero],
        zero_add]
  map_add' t s := by
    apply Prod.ext
    · apply Subtype.ext
      show ((N : ℤ) * b) • ((t : A) + (s : A))
        = ((N : ℤ) * b) • (t : A) + ((N : ℤ) * b) • (s : A)
      rw [smul_add]
    · apply Subtype.ext
      show ((M : ℤ) * a) • ((t : A) + (s : A))
        = ((M : ℤ) * a) • (t : A) + ((M : ℤ) * a) • (s : A)
      rw [smul_add]

theorem nonempty_torsionByMulAddEquiv_prod_of_coprime {M N : ℕ} (hcop : Nat.Coprime M N) :
    Nonempty (Submodule.torsionBy ℤ A ((M * N : ℕ) : ℤ) ≃+
      Submodule.torsionBy ℤ A (M : ℤ) × Submodule.torsionBy ℤ A (N : ℤ)) := by
  have hbez : (M : ℤ) * Nat.gcdA M N + (N : ℤ) * Nat.gcdB M N = 1 := by
    have h := Nat.gcd_eq_gcd_ab M N
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact_mod_cast h.symm
  exact ⟨torsionByMulCoprimeSplitAddEquiv M N (Nat.gcdA M N) (Nat.gcdB M N) hbez⟩

/-- Native Chinese remainders, reordered into the two rank-two factors. -/
def zmodSqCrtAddEquiv {M N : ℕ} (hcop : Nat.Coprime M N) :
    (ZMod (M * N) × ZMod (M * N)) ≃+ (ZMod M × ZMod M) × (ZMod N × ZMod N) :=
  (AddEquiv.prodCongr (ZMod.chineseRemainder hcop).toAddEquiv
    (ZMod.chineseRemainder hcop).toAddEquiv).trans
    (AddEquiv.prodProdProdComm (ZMod M) (ZMod N) (ZMod M) (ZMod N))

theorem nonempty_zmodSqAddEquiv_torsionBy_mul_of_coprime {M N : ℕ} (hcop : Nat.Coprime M N)
    (hM : Nonempty ((ZMod M × ZMod M) ≃+ Submodule.torsionBy ℤ A (M : ℤ)))
    (hN : Nonempty ((ZMod N × ZMod N) ≃+ Submodule.torsionBy ℤ A (N : ℤ))) :
    Nonempty ((ZMod (M * N) × ZMod (M * N)) ≃+ Submodule.torsionBy ℤ A ((M * N : ℕ) : ℤ)) := by
  obtain ⟨eM⟩ := hM
  obtain ⟨eN⟩ := hN
  obtain ⟨eT⟩ := nonempty_torsionByMulAddEquiv_prod_of_coprime (A := A) hcop
  exact ⟨((zmodSqCrtAddEquiv hcop).trans (AddEquiv.prodCongr eM eN)).trans eT.symm⟩


end
end Dubon2026.SourceEllipticTorsionStructure
