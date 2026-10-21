import Dubon2026.SourceHeckeConjugationLower

/-! A lower-subgroup transversal for the second actual prime correspondence.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> full H1 Hecke commutativity -> product-coset parametrization.
Reuse the original upper translations and Bezout representative at level Q*p.
This replaces the external proof's separate modular-arithmetic factorization.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private def productBezout (Q p q : ℕ) (hq : Nat.Coprime q (Q * p)) : Gamma0 Q :=
  ⟨(heckeBezoutRepresentative q (Q * p) hq).val, by
    rw [Gamma0_mem]
    change (((Q * p : ℕ) : ℤ) : ZMod Q) = 0
    simp⟩

private def productRepresentative (Q p q : ℕ) (hq : Nat.Coprime q (Q * p)) :
    Option (ZMod q) → Gamma0 Q
  | some x => (heckeUpperTranslation Q x.val)⁻¹
  | none => (productBezout Q p q hq)⁻¹

private theorem productRepresentative_lower (Q p q : ℕ) (hq : Nat.Coprime q (Q * p))
    (i : Option (ZMod q)) :
    productRepresentative Q p q hq i ∈ heckeLowerSubgroup Q p := by
  change (((productRepresentative Q p q hq i).val 1 0 : ℤ) : ZMod p) = 0
  cases i <;> simp [productRepresentative, productBezout, heckeBezoutRepresentative,
    heckeUpperTranslation, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

private theorem productRepresentative_coset (Q p q : ℕ) [NeZero q]
    (hq : Nat.Coprime q (Q * p)) (hqQ : Nat.Coprime q Q) (i : Option (ZMod q)) :
    (productRepresentative Q p q hq i : Gamma0 Q ⧸ heckeUpperSubgroup Q q) =
      heckeUpperCoset q Q hqQ i := by
  cases i with
  | some i => rfl
  | none =>
    apply QuotientGroup.eq.mpr
    change ((productBezout Q p q hq)⁻¹)⁻¹ *
      (heckeBezoutRepresentative q Q hqQ)⁻¹ ∈ heckeUpperSubgroup Q q
    rw [inv_inv]
    change (((((productBezout Q p q hq).val) *
      (heckeBezoutRepresentative q Q hqQ).val⁻¹) 0 1 : ℤ) : ZMod q) = 0
    simp [productBezout, heckeBezoutRepresentative, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- For distinct good primes, every actual second-prime coset has a representative
in the image of the original first-prime conjugation. All factorization and section
conditions are derived from the existing integral Hecke transversals. -/
theorem sourceHeckeProduct_exists_section {Q p q : ℕ} [NeZero p] [NeZero q]
    (hp : p.Prime) (hq : q.Prime) (hpQ : Nat.Coprime p Q)
    (hqQ : Nat.Coprime q Q) (hpq : Nat.Coprime p q) :
    ∃ σ : Gamma0 Q ⧸ heckeUpperSubgroup Q q → heckeUpperSubgroup Q p,
      ∀ x, (sourceHeckeConjugation hp (σ x) :
        Gamma0 Q ⧸ heckeUpperSubgroup Q q) = x := by
  have hqQp : Nat.Coprime q (Q * p) := hqQ.mul_right hpq.symm
  have h (x : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
      ∃ u : heckeUpperSubgroup Q p,
        (sourceHeckeConjugation hp u : Gamma0 Q ⧸ heckeUpperSubgroup Q q) = x := by
    obtain ⟨i, hi⟩ := heckeUpperCoset_surjective hq hqQ x
    obtain ⟨u, hu⟩ := sourceHeckeConjugation_exists_lower hp hpQ
      (productRepresentative Q p q hqQp i) (productRepresentative_lower Q p q hqQp i)
    refine ⟨u, ?_⟩
    rw [hu, productRepresentative_coset Q p q hqQp hqQ, hi]
  choose σ hσ using h
  exact ⟨σ, hσ⟩

end
end Dubon2026
