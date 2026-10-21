import Dubon2026.SourceHeckeProductTransitions
import Dubon2026.SourceIntegralHeckeHom
import Dubon2026.SourceCorrespondenceOne

/-! The literal double prime trace reindexed as the original product trace.
DUB-17/18 -> residual modular Galois association -> original residual H1
eigensystem -> full integral H1 Hecke commutativity -> product-trace comparison.

The finite reindexing adapts the product-correspondence argument in
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.lean
(Apache-2.0; retained LICENSE and NOTICE). Native cocycles and coboundaries
replace the external coefficient-cohomology presentation.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable {R : Type} [CommRing R] {Q p q : ℕ} [NeZero p] [NeZero q]
    (hp : p.Prime) (hq : q.Prime) (A : Rep R (Gamma0 Q))
    (b d : Module.End R A)
    (σ : Gamma0 Q ⧸ heckeUpperSubgroup Q q → heckeUpperSubgroup Q p)
    (hσ : ∀ x, (sourceHeckeConjugation hp (σ x) :
      Gamma0 Q ⧸ heckeUpperSubgroup Q q) = x)

private local instance primeTraceFinite (n : ℕ) [NeZero n] :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q n) := sourceHeckeUpperFintype Q n

/-- The second original Hecke trace using the proved inner representatives. -/
def sourceHeckeInnerTrace (c : Gamma0 Q → A) (g : Gamma0 Q) : A :=
  ∑ y : Gamma0 Q ⧸ heckeUpperSubgroup Q q,
    A.ρ (sourceHeckeInnerRepresentative hp σ (g • y))
      (d (c (sourceHeckeConjugation hq (sourceHeckeInnerTransition hp σ hσ g y))))

/-- The original product-level trace using the actual product representatives. -/
def sourceHeckeProductTrace (c : Gamma0 Q → A) (g : Gamma0 Q) : A :=
  ∑ z : Gamma0 Q ⧸ heckeUpperSubgroup Q (p * q),
    A.ρ (sourceHeckeProductRepresentative hp σ hσ (g • z))
      ((b.comp d) (c (sourceIntegralHeckeHom (sourceHeckeProductTransition hp σ hσ g z))))

/-- The coefficient intertwining identity reindexes the entire double trace
as the actual product trace, before taking any quotient. -/
theorem sourceHeckePrime_innerTrace_eq_product
    (hb : ∀ u : heckeUpperSubgroup Q p,
      b.comp (A.ρ (sourceHeckeConjugation hp u)) = (A.ρ u.val).comp b)
    (c : Gamma0 Q → A) :
    sourceCorrespondenceOne A (heckeUpperSubgroup Q p) (sourceHeckeConjugation hp) b
      (sourceHeckeInnerTrace hp hq A d σ hσ c) =
        sourceHeckeProductTrace hp A b d σ hσ c := by
  funext g
  rw [sourceCorrespondenceOne_apply]
  change (∑ x : Gamma0 Q ⧸ heckeUpperSubgroup Q p,
    A.ρ (g • x).out (b (sourceHeckeInnerTrace hp hq A d σ hσ c _))) =
      ∑ z : Gamma0 Q ⧸ heckeUpperSubgroup Q (p * q),
        A.ρ (sourceHeckeProductRepresentative hp σ hσ (g • z))
          ((b.comp d) (c (sourceIntegralHeckeHom (sourceHeckeProductTransition hp σ hσ g z))))
  rw [← Fintype.sum_equiv (sourceHeckeProductCosetEquiv hp σ hσ)
    (fun xy => A.ρ (sourceHeckeProductRepresentative hp σ hσ
      (g • sourceHeckeProductCosetEquiv hp σ hσ xy))
      ((b.comp d) (c (sourceIntegralHeckeHom (sourceHeckeProductTransition hp σ hσ g
        (sourceHeckeProductCosetEquiv hp σ hσ xy))))))
    (fun z => A.ρ (sourceHeckeProductRepresentative hp σ hσ (g • z))
      ((b.comp d) (c (sourceIntegralHeckeHom (sourceHeckeProductTransition hp σ hσ g z)))))
    (fun _ => rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp only [sourceHeckeInnerTrace, map_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hpush (v : A) (z : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
      b (A.ρ (sourceHeckeInnerRepresentative hp σ z) v) = A.ρ (σ z).val (b v) :=
    LinearMap.congr_fun (hb (σ z)) v
  rw [hpush, sourceHeckeProductCosetEquiv_smul, sourceHeckeProductRepresentative_pair]
  change A.ρ _ (A.ρ _ (b (d (c _)))) =
    A.ρ _ ((b.comp d) (c (sourceIntegralHeckeConjugate _)))
  rw [sourceHeckeProductTransition_conjugate hp σ hσ hq, map_mul,
    Module.End.mul_apply, LinearMap.comp_apply]

/-- The product of the two genuine coefficient intertwiners intertwines the
actual product-level conjugation. -/
theorem sourceHeckeProduct_intertwine
    (hb : ∀ u : heckeUpperSubgroup Q p,
      b.comp (A.ρ (sourceHeckeConjugation hp u)) = (A.ρ u.val).comp b)
    (hd : ∀ u : heckeUpperSubgroup Q q,
      d.comp (A.ρ (sourceHeckeConjugation hq u)) = (A.ρ u.val).comp d)
    (u : heckeUpperSubgroup Q (p * q)) :
    (b.comp d).comp (A.ρ (sourceIntegralHeckeHom u)) =
      (A.ρ u.val).comp (b.comp d) := by
  change (b.comp d).comp (A.ρ (sourceIntegralHeckeConjugate u)) = _
  rw [sourceHeckeConjugate_product, sourceIntegralHeckeConjugate_eq_prime hq,
    LinearMap.comp_assoc, hd, ← LinearMap.comp_assoc]
  change (b.comp (A.ρ (sourceIntegralHeckeConjugate (sourceHeckeProductToLeft Q p q u)))).comp d = _
  rw [sourceIntegralHeckeConjugate_eq_prime hp, hb, LinearMap.comp_assoc]
  rfl

/-- The chosen product trace differs from the original product trace by a native coboundary. -/
theorem sourceHeckeProductTrace_sub
    (hb : ∀ u : heckeUpperSubgroup Q p,
      b.comp (A.ρ (sourceHeckeConjugation hp u)) = (A.ρ u.val).comp b)
    (hd : ∀ u : heckeUpperSubgroup Q q,
      d.comp (A.ρ (sourceHeckeConjugation hq u)) = (A.ρ u.val).comp d)
    (c : groupCohomology.cocycles₁ A) :
    sourceHeckeProductTrace hp A b d σ hσ c -
      sourceCorrespondenceOne A (heckeUpperSubgroup Q (p * q)) sourceIntegralHeckeHom (b.comp d) c ∈
        groupCohomology.coboundaries₁ A :=
  sourceCorrespondenceOne_chosen_sub A _ _ _ (sourceHeckeProduct_intertwine hp hq A b d hb hd)
    (sourceHeckeProductRepresentative hp σ hσ)
    (sourceHeckeProductRepresentative_coset hp σ hσ) c

/-- The chosen inner trace differs from the original second prime trace by a native coboundary. -/
theorem sourceHeckeInnerTrace_sub
    (hd : ∀ u : heckeUpperSubgroup Q q,
      d.comp (A.ρ (sourceHeckeConjugation hq u)) = (A.ρ u.val).comp d)
    (c : groupCohomology.cocycles₁ A) :
    sourceHeckeInnerTrace hp hq A d σ hσ c -
      sourceCorrespondenceOne A (heckeUpperSubgroup Q q) (sourceHeckeConjugation hq) d c ∈
        groupCohomology.coboundaries₁ A :=
  sourceCorrespondenceOne_chosen_sub A _ _ _ hd
    (sourceHeckeInnerRepresentative hp σ)
    (sourceHeckeInnerRepresentative_coset hp σ hσ) c

end
end Dubon2026
