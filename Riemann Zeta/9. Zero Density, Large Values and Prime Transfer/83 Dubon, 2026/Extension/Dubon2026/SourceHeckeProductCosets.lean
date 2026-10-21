import Dubon2026.SourceHeckeProductSection

/-! Exact product cosets for the original two prime correspondences.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> original integral H1 Hecke commutativity -> reindexing the composed trace.

The quotient argument adapts PsiFun_injective and PsiFun_surjective from
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries.lean
(Apache-2.0; retained LICENSE and NOTICE). The subgroup, conjugation and
section are the original local ones.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable {Q p q : ℕ} [NeZero p] (hp : p.Prime)
    (σ : Gamma0 Q ⧸ heckeUpperSubgroup Q q → heckeUpperSubgroup Q p)
    (hσ : ∀ x, (sourceHeckeConjugation hp (σ x) :
      Gamma0 Q ⧸ heckeUpperSubgroup Q q) = x)

private theorem product_mem (u : heckeUpperSubgroup Q p) :
    u.val ∈ heckeUpperSubgroup Q (p * q) ↔
      sourceHeckeConjugation hp u ∈ heckeUpperSubgroup Q q := by
  rw [← sourceIntegralHeckeConjugate_eq_prime hp u]
  exact sourceHeckeUpper_product_mem_iff Q p q u

/-- The literal pair-of-cosets map used to reindex the original composed Hecke trace. -/
def sourceHeckeProductCosetMap
    (x : (Gamma0 Q ⧸ heckeUpperSubgroup Q p) × (Gamma0 Q ⧸ heckeUpperSubgroup Q q)) :
    Gamma0 Q ⧸ heckeUpperSubgroup Q (p * q) :=
  (x.1.out * (σ x.2).val : Gamma0 Q)

include hp hσ in
private theorem productCosetMap_injective :
    Function.Injective (sourceHeckeProductCosetMap σ) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  have hW : (x₁.out * (σ y₁).val)⁻¹ * (x₂.out * (σ y₂).val) ∈
      heckeUpperSubgroup Q (p * q) := QuotientGroup.eq.mp h
  have hU : x₁.out⁻¹ * x₂.out ∈ heckeUpperSubgroup Q p := by
    have h1 := sourceHeckeUpper_product_le Q p q hW
    rw [mul_inv_rev, mul_assoc, ← mul_assoc (x₁.out⁻¹)] at h1
    have h2 := (Subgroup.mul_mem_cancel_left _ ((heckeUpperSubgroup Q p).inv_mem (σ y₁).property)).mp h1
    exact (Subgroup.mul_mem_cancel_right _ (σ y₂).property).mp h2
  have hx : x₁ = x₂ := by
    rw [← QuotientGroup.out_eq' x₁, ← QuotientGroup.out_eq' x₂]
    exact QuotientGroup.eq.mpr hU
  subst hx
  have hW' : ((σ y₁)⁻¹ * σ y₂).val ∈ heckeUpperSubgroup Q (p * q) := by
    have he : (x₁.out * (σ y₁).val)⁻¹ * (x₁.out * (σ y₂).val) =
        ((σ y₁)⁻¹ * σ y₂).val := by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [← he]
    exact hW
  have hU' := (product_mem hp ((σ y₁)⁻¹ * σ y₂)).mp hW'
  rw [map_mul, map_inv] at hU'
  have hy : (sourceHeckeConjugation hp (σ y₁) : Gamma0 Q ⧸ heckeUpperSubgroup Q q) =
      (sourceHeckeConjugation hp (σ y₂) : Gamma0 Q) := QuotientGroup.eq.mpr hU'
  rw [hσ, hσ] at hy
  rw [hy]

include hp hσ in
private theorem productCosetMap_surjective :
    Function.Surjective (sourceHeckeProductCosetMap σ) := by
  intro z
  induction z using QuotientGroup.induction_on with
  | H g =>
    let x : Gamma0 Q ⧸ heckeUpperSubgroup Q p := g
    have hu : x.out⁻¹ * g ∈ heckeUpperSubgroup Q p :=
      QuotientGroup.eq.mp (by rw [QuotientGroup.out_eq'])
    let u : heckeUpperSubgroup Q p := ⟨x.out⁻¹ * g, hu⟩
    let y : Gamma0 Q ⧸ heckeUpperSubgroup Q q := sourceHeckeConjugation hp u
    refine ⟨(x, y), QuotientGroup.eq.mpr ?_⟩
    have hm : ((σ y)⁻¹ * u).val ∈ heckeUpperSubgroup Q (p * q) := by
      apply (product_mem hp _).mpr
      rw [map_mul, map_inv]
      exact QuotientGroup.eq.mp (hσ y)
    have he : (x.out * (σ y).val)⁻¹ * g = ((σ y)⁻¹ * u).val := by
      simp only [u, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [he]
    exact hm

/-- The exact bijection from pairs of original prime cosets to the product-level cosets. -/
def sourceHeckeProductCosetEquiv :
    (Gamma0 Q ⧸ heckeUpperSubgroup Q p) × (Gamma0 Q ⧸ heckeUpperSubgroup Q q) ≃
      Gamma0 Q ⧸ heckeUpperSubgroup Q (p * q) :=
  Equiv.ofBijective (sourceHeckeProductCosetMap σ)
    ⟨productCosetMap_injective hp σ hσ, productCosetMap_surjective hp σ hσ⟩

/-- The product-coset equivalence retains its literal original representative. -/
theorem sourceHeckeProductCosetEquiv_apply
    (x : Gamma0 Q ⧸ heckeUpperSubgroup Q p) (y : Gamma0 Q ⧸ heckeUpperSubgroup Q q) :
    sourceHeckeProductCosetEquiv hp σ hσ (x, y) =
      (x.out * (σ y).val : Gamma0 Q) := rfl

end
end Dubon2026
