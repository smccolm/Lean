import Dubon2026.ArithmeticOrbitFieldEmbedding

/-! # The original quotient representative preserves the literal finite-field embedding

This identifies the chosen representative with any specified representative
on the actual finite field. It supplies the explicit global automorphism
coordinates in DUB-17's prime-surjectivity proof.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))

/-- Any specified coset representative has the same literal action on the original fixed field. -/
theorem rationalArithmeticOrbitRepresentative_mk
    (τ : rationalArithmeticGaloisGroup a) (x : F) :
    rationalArithmeticOrbitRepresentative a F (QuotientGroup.mk τ)
      (x : rationalUnramifiedExtension a) =
        (show Gal(rationalUnramifiedExtension a / ℚ) from τ) (x : rationalUnramifiedExtension a) := by
  let c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F := QuotientGroup.mk τ
  let σ := rationalArithmeticOrbitRepresentative a F c
  have h := QuotientGroup.eq.mp (Quotient.out_eq' c)
  change σ⁻¹ * (show Gal(rationalUnramifiedExtension a / ℚ) from τ) ∈ F.fixingSubgroup at h
  rw [IntermediateField.mem_fixingSubgroup_iff] at h
  have he := congrArg σ (h x x.property)
  change σ (σ.symm ((show Gal(rationalUnramifiedExtension a / ℚ) from τ) x)) = σ x at he
  rw [σ.apply_symm_apply] at he
  exact he.symm

/-- The coset-twisted local embedding agrees with its explicitly specified arithmetic representative. -/
theorem rationalArithmeticOrbitEmbedding_mk
    (τ : rationalArithmeticGaloisGroup a) (x : F) :
    rationalArithmeticOrbitEmbedding a p hp F (QuotientGroup.mk τ) (x : rationalUnramifiedExtension a) =
      rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a
        ((show Gal(rationalUnramifiedExtension a / ℚ) from τ) (x : rationalUnramifiedExtension a)) :=
  congrArg (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a)
    (rationalArithmeticOrbitRepresentative_mk a F τ x)

end
end Dubon2026
