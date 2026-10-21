import Dubon2026.SourceFiniteOrderHeckeConjugation
import Dubon2026.SourceCosetTransfer
import Dubon2026.HeckeUpperCosets

/-! DUB-17/18 -> residual Galois association -> finite-order weight-two
branch -> exact Hecke scalar. The pinned transfer orbit formula and the
proved original finite-order diagonal conjugacy identify the full coset
sum with index times the original homomorphism. No Hecke summand is omitted.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (Q ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓQ : Nat.Coprime ℓ Q)

private local instance upperIndex : (heckeUpperSubgroup Q ℓ).FiniteIndex :=
  sourceHeckeUpper_finiteIndex
private local instance upperFinite : Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ℓ) :=
  sourceHeckeUpperFintype Q ℓ

include hℓQ in
/-- The original full Hecke transition sum at a finite-order congruence
element is exactly ell+1 times its original homomorphism value. -/
theorem sourceFiniteOrderHecke_sum
    {A : Type} [AddCommGroup A] (φ : Additive (Gamma0 Q) →+ A)
    (γ : Gamma0 Q) (hγ : IsOfFinOrder γ) :
    (∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q ℓ,
      φ (Additive.ofMul (sourceHeckeConjugation hℓ
        (cosetTransition (heckeUpperSubgroup Q ℓ) γ q)))) =
      (ℓ + 1) • φ (Additive.ofMul γ) := by
  classical
  let K := heckeUpperSubgroup Q ℓ
  let ψ : Gamma0 Q →* Multiplicative A := AddMonoidHom.toMultiplicativeRight φ
  letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers γ) (Gamma0 Q ⧸ K))) :=
    Fintype.ofFinite _
  have he : MonoidHom.transfer (ψ.comp (sourceHeckeConjugation hℓ)) γ =
      MonoidHom.transfer (ψ.comp K.subtype) γ := by
    rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
      MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
    apply Finset.prod_congr rfl
    intro q _
    change Multiplicative.ofAdd (φ (Additive.ofMul (sourceHeckeConjugation hℓ _))) =
      Multiplicative.ofAdd (φ (Additive.ofMul _))
    apply congrArg Multiplicative.ofAdd
    apply SourceFiniteOrder.hom_conjugation_eq_of_finiteOrder hℓ
    obtain ⟨n, hn, hγn⟩ := hγ.exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    change (q.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * q.out.out) ^ n = 1
    have hc := conj_pow (a := q.out.out⁻¹)
      (b := γ ^ Function.minimalPeriod (γ • ·) q.out) (i := n)
    simpa only [inv_inv, pow_right_comm, hγn, one_pow, mul_one, inv_mul_cancel] using hc
  have hindex : K.index = ℓ + 1 := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card,
      ← Fintype.card_congr (heckeUpperCosetEquiv hℓ hℓQ), Fintype.card_option, ZMod.card]
  rw [sourceTransfer_restriction_eq_pow K ψ γ, hindex,
    sourceTransfer_eq_coset_product] at he
  have ha := congrArg Multiplicative.toAdd he
  rw [toAdd_prod, toAdd_pow] at ha
  exact ha

end
end Dubon2026
