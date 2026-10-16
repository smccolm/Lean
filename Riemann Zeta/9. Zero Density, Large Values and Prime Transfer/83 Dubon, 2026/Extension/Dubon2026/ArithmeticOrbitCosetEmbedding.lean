import Dubon2026.ArithmeticOrbitFieldEmbedding

/-! # Original arithmetic coset equality detected on the literal embedded field

This is the group-coordinate input for DUB-17's identification of local
Mackey orbits with original finite primes. It uses the actual arithmetic
restriction, original fixing subgroup and coset-twisted embedding.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (c c' : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  (d : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))

/-- The actual local action carries one coset to another precisely when it identifies their original field embeddings. -/
theorem rationalArithmeticOrbitCoset_smul_iff :
    rationalPrimeArithmeticRestriction a p hp d • c = c' ↔
      ∀ x : F, d (rationalArithmeticOrbitEmbedding a p hp F c (x : rationalUnramifiedExtension a)) =
        rationalArithmeticOrbitEmbedding a p hp F c' (x : rationalUnramifiedExtension a) := by
  let σ := rationalArithmeticOrbitRepresentative a F c
  let σ' := rationalArithmeticOrbitRepresentative a F c'
  let τ : Gal(rationalUnramifiedExtension a / ℚ) := rationalPrimeArithmeticRestriction a p hp d
  have hq : rationalPrimeArithmeticRestriction a p hp d • c = c' ↔
      σ'⁻¹ * (τ * σ) ∈ F.fixingSubgroup := by
    rw [← MulAction.Quotient.mk_smul_out (rationalArithmeticOrbitFixingSubgroup a F)
      (rationalPrimeArithmeticRestriction a p hp d) c, ← Quotient.out_eq' c']
    exact eq_comm.trans QuotientGroup.eq
  rw [hq, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x
    have he := congrArg σ' (h x x.property)
    change σ' (σ'.symm (τ (σ x))) = σ' x at he
    rw [σ'.apply_symm_apply] at he
    exact (rationalPrimeArithmeticRestriction_commutes a p hp d (σ x)).symm.trans
      (congrArg (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a) he)
  · intro h x hx
    have he := (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a).injective
      ((rationalPrimeArithmeticRestriction_commutes a p hp d (σ x)).trans (h ⟨x, hx⟩))
    change τ (σ x) = σ' x at he
    change σ'.symm (τ (σ x)) = x
    rw [he, σ'.symm_apply_apply]

end
end Dubon2026
