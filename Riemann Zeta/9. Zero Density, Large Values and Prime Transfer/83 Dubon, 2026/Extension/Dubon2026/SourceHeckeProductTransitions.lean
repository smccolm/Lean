import Dubon2026.SourceHeckeProductCosets
import Dubon2026.SourceChosenCosetTraceOne

/-! Literal transitions for the composed original prime correspondences.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> original integral H1 Hecke commutativity -> equality of the composed
trace with the product trace modulo an explicitly proved coboundary.

The transition argument adapts the product-coset proof in
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.lean
(Apache-2.0; retained LICENSE and NOTICE), using the original native
conjugations, transitions, and the shorter local transversal construction.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable {Q p q : ℕ} [NeZero p] (hp : p.Prime)
    (σ : Gamma0 Q ⧸ heckeUpperSubgroup Q q → heckeUpperSubgroup Q p)
    (hσ : ∀ x, (sourceHeckeConjugation hp (σ x) :
      Gamma0 Q ⧸ heckeUpperSubgroup Q q) = x)

/-- The second correspondence represented by actual first-conjugated section elements. -/
def sourceHeckeInnerRepresentative (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) : Gamma0 Q :=
  sourceHeckeConjugation hp (σ y)

include hσ in
/-- The inner chosen representative has its required original coset. -/
theorem sourceHeckeInnerRepresentative_coset (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
    (sourceHeckeInnerRepresentative hp σ y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) = y :=
  hσ y

/-- The actual inner transition of the composed trace. -/
def sourceHeckeInnerTransition (g : Gamma0 Q) (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
    heckeUpperSubgroup Q q :=
  sourceChosenCosetTransition _ (sourceHeckeInnerRepresentative hp σ)
    (sourceHeckeInnerRepresentative_coset hp σ hσ) g y

private def productTransitionLeft (g : Gamma0 Q) (x : Gamma0 Q ⧸ heckeUpperSubgroup Q p)
    (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) : heckeUpperSubgroup Q p :=
  (σ (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) g x) • y))⁻¹ *
    cosetTransition (heckeUpperSubgroup Q p) g x * σ y

private theorem productTransitionLeft_conjugate (g : Gamma0 Q)
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q p) (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
    sourceHeckeConjugation hp (productTransitionLeft hp σ g x y) =
      (sourceHeckeInnerTransition hp σ hσ
        (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) g x)) y).val := by
  simp only [productTransitionLeft, map_mul, map_inv, sourceHeckeInnerTransition,
    sourceChosenCosetTransition, sourceHeckeInnerRepresentative, mul_assoc]

include hσ in
private theorem productTransitionLeft_mem (g : Gamma0 Q)
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q p) (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
    (productTransitionLeft hp σ g x y).val ∈ heckeUpperSubgroup Q (p * q) := by
  apply (sourceHeckeUpper_product_mem_iff Q p q _).mpr
  rw [sourceIntegralHeckeConjugate_eq_prime hp, productTransitionLeft_conjugate hp σ hσ]
  exact (sourceHeckeInnerTransition hp σ hσ _ y).property

/-- The original group action on the product cosets is the exact iterated prime action. -/
theorem sourceHeckeProductCosetEquiv_smul (g : Gamma0 Q)
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q p) (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
    g • sourceHeckeProductCosetEquiv hp σ hσ (x, y) =
      sourceHeckeProductCosetEquiv hp σ hσ
        (g • x, sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) g x) • y) := by
  rw [sourceHeckeProductCosetEquiv_apply, sourceHeckeProductCosetEquiv_apply]
  change ((g * (x.out * (σ y).val) : Gamma0 Q) :
    Gamma0 Q ⧸ heckeUpperSubgroup Q (p * q)) = _
  apply QuotientGroup.eq.mpr
  have key : ((g • x).out *
      (σ (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) g x) • y)).val)⁻¹ *
      (g * (x.out * (σ y).val)) = (productTransitionLeft hp σ g x y).val := by
    change _ = _⁻¹ * ((g • x).out⁻¹ * (g * x.out)) * (σ y).val
    group
  have hm := (heckeUpperSubgroup Q (p * q)).inv_mem
    (productTransitionLeft_mem hp σ hσ g x y)
  rw [← key, mul_inv_rev, inv_inv] at hm
  exact hm

/-- The product correspondence uses the literal product of the two original representatives. -/
def sourceHeckeProductRepresentative (z : Gamma0 Q ⧸ heckeUpperSubgroup Q (p * q)) : Gamma0 Q :=
  ((sourceHeckeProductCosetEquiv hp σ hσ).symm z).1.out *
    (σ ((sourceHeckeProductCosetEquiv hp σ hσ).symm z).2).val

/-- Evaluating the product representative at its original pair gives their literal product. -/
theorem sourceHeckeProductRepresentative_pair
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q p) (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
    sourceHeckeProductRepresentative hp σ hσ (sourceHeckeProductCosetEquiv hp σ hσ (x, y)) =
      x.out * (σ y).val := by
  rw [sourceHeckeProductRepresentative, Equiv.symm_apply_apply]

/-- The product representative has exactly its stated product-level coset. -/
theorem sourceHeckeProductRepresentative_coset (z : Gamma0 Q ⧸ heckeUpperSubgroup Q (p * q)) :
    (sourceHeckeProductRepresentative hp σ hσ z : Gamma0 Q ⧸ heckeUpperSubgroup Q (p * q)) = z := by
  exact (sourceHeckeProductCosetEquiv hp σ hσ).apply_symm_apply z

/-- The actual chosen product-level transition. -/
def sourceHeckeProductTransition (g : Gamma0 Q) (z : Gamma0 Q ⧸ heckeUpperSubgroup Q (p * q)) :
    heckeUpperSubgroup Q (p * q) :=
  sourceChosenCosetTransition _ (sourceHeckeProductRepresentative hp σ hσ)
    (sourceHeckeProductRepresentative_coset hp σ hσ) g z

private theorem productTransition_pair (g : Gamma0 Q)
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q p) (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
    (sourceHeckeProductTransition hp σ hσ g (sourceHeckeProductCosetEquiv hp σ hσ (x, y))).val =
      (productTransitionLeft hp σ g x y).val := by
  change (sourceHeckeProductRepresentative hp σ hσ
      (g • sourceHeckeProductCosetEquiv hp σ hσ (x, y)))⁻¹ *
      (g * sourceHeckeProductRepresentative hp σ hσ (sourceHeckeProductCosetEquiv hp σ hσ (x, y))) = _
  rw [sourceHeckeProductCosetEquiv_smul, sourceHeckeProductRepresentative_pair,
    sourceHeckeProductRepresentative_pair]
  change _ = _⁻¹ * ((g • x).out⁻¹ * (g * x.out)) * (σ y).val
  group

/-- The product-level conjugated transition is exactly the successive original transitions. -/
theorem sourceHeckeProductTransition_conjugate [NeZero q] (hq : q.Prime)
    (g : Gamma0 Q) (x : Gamma0 Q ⧸ heckeUpperSubgroup Q p)
    (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
    sourceIntegralHeckeConjugate
      (sourceHeckeProductTransition hp σ hσ g (sourceHeckeProductCosetEquiv hp σ hσ (x, y))) =
      sourceHeckeConjugation hq
        (sourceHeckeInnerTransition hp σ hσ
          (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) g x)) y) := by
  rw [sourceHeckeConjugate_product, sourceIntegralHeckeConjugate_eq_prime hq]
  congr 1
  apply Subtype.ext
  change sourceIntegralHeckeConjugate
    (sourceHeckeProductToLeft Q p q _) = _
  rw [sourceIntegralHeckeConjugate_eq_prime hp]
  have he : sourceHeckeProductToLeft Q p q
      (sourceHeckeProductTransition hp σ hσ g (sourceHeckeProductCosetEquiv hp σ hσ (x, y))) =
      productTransitionLeft hp σ g x y := Subtype.ext (productTransition_pair hp σ hσ g x y)
  rw [he, productTransitionLeft_conjugate hp σ hσ]

end
end Dubon2026
