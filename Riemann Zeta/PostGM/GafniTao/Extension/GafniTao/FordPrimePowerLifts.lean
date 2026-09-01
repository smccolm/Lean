import GafniTao.FordSourcePrimePowerSystem
import Mathlib.GroupTheory.Coset.Basic

/-!
# Ford Section 3: exact prime-power lift counts

Ford's `B*` argument repeatedly lifts a residue modulo `p^e` to one modulo
`p^r`.  This file proves the exact fiber cardinal `p^(r-e)` from the
surjective additive homomorphism, rather than inserting a coarse bound.
-/

namespace GafniTao

noncomputable section

def fordPrimePowerCastHom (p r e : ℕ) (her : e ≤ r) :
    ZMod (p ^ r) →+ ZMod (p ^ e) :=
  (ZMod.castHom (pow_dvd_pow p her) (ZMod (p ^ e))).toAddMonoidHom

def FordPrimePowerLiftFiber (p r e : ℕ) (her : e ≤ r)
    (a : ZMod (p ^ e)) :=
  {b : ZMod (p ^ r) // fordPrimePowerCastHom p r e her b = a}

def fordTypeEquivSigmaFiber {A B : Type*} (f : A → B) :
    A ≃ Σ b : B, {a : A // f a = b} where
  toFun a := ⟨f a, a, rfl⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨b, a, ha⟩
    subst b
    rfl

def fordPrimePowerLiftFiberEquiv
    {p r e : ℕ} {her : e ≤ r} (a b : ZMod (p ^ e)) :
    FordPrimePowerLiftFiber p r e her a ≃
      FordPrimePowerLiftFiber p r e her b := by
  let hsurj : Function.Surjective (fordPrimePowerCastHom p r e her) :=
    ZMod.castHom_surjective (pow_dvd_pow p her)
  exact AddMonoidHom.fiberEquivOfSurjective hsurj a b

theorem fordPrimePowerLiftFiber_card
    {p r e : ℕ} (hp : Nat.Prime p) (he : 0 < e) (her : e ≤ r)
    (a : ZMod (p ^ e)) :
    Nat.card (FordPrimePowerLiftFiber p r e her a) = p ^ (r - e) := by
  letI : Fact (1 < p ^ e) := ⟨one_lt_pow₀ hp.one_lt he.ne'⟩
  letI : Fact (1 < p ^ r) :=
    ⟨one_lt_pow₀ hp.one_lt (he.trans_le her).ne'⟩
  letI (b : ZMod (p ^ e)) : Finite (FordPrimePowerLiftFiber p r e her b) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have htotal : p ^ r = p ^ e *
      Nat.card (FordPrimePowerLiftFiber p r e her a) := by
    calc
      p ^ r = Nat.card (ZMod (p ^ r)) := by simp
      _ = Nat.card (Σ b : ZMod (p ^ e),
          FordPrimePowerLiftFiber p r e her b) :=
        Nat.card_congr (fordTypeEquivSigmaFiber
          (fordPrimePowerCastHom p r e her))
      _ = ∑ b : ZMod (p ^ e),
          Nat.card (FordPrimePowerLiftFiber p r e her b) := Nat.card_sigma
      _ = ∑ _b : ZMod (p ^ e),
          Nat.card (FordPrimePowerLiftFiber p r e her a) := by
        apply Finset.sum_congr rfl
        intro b _
        exact Nat.card_congr (fordPrimePowerLiftFiberEquiv b a)
      _ = p ^ e * Nat.card (FordPrimePowerLiftFiber p r e her a) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp
  have hpow : p ^ r = p ^ e * p ^ (r - e) := by
    rw [← pow_add, Nat.add_sub_of_le her]
  rw [hpow] at htotal
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos e) htotal.symm

#print axioms fordTypeEquivSigmaFiber
#print axioms fordPrimePowerLiftFiberEquiv
#print axioms fordPrimePowerLiftFiber_card

end

end GafniTao
