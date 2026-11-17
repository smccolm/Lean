import Dubon2026.SourceTraceRadicalQuotient

/-! DUB-17/18 -> original rank-two realization -> genuine trace algebra.
The proved dimension-two trace identity forces the polarized quadratic
identity in the actual radical quotient. This removes an algebraic
reconstruction premise without assuming matrices or finite dimension. -/
namespace Dubon2026
noncomputable section
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The polarized quadratic relation belongs to the actual trace radical. -/
theorem sourceTraceRadical_polarized
    (τ : A →ₗ[R] R) (hCyc : ∀ x y, τ (x * y) = τ (y * x))
    (hTri : ∀ x y z, τ (x * y * z) + τ (x * z * y) =
      τ x * τ (y * z) + τ y * τ (x * z) + τ z * τ (x * y) - τ x * τ y * τ z)
    (x y : A) :
    x * y + y * x - τ x • y - τ y • x + (τ x * τ y - τ (x * y)) • (1 : A) ∈
      sourceTraceRadical τ hCyc := by
  intro z
  have h := hTri x y z
  have hcycle : τ (y * x * z) = τ (x * z * y) := by
    rw [mul_assoc, hCyc]
  simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, map_add, map_sub, map_smul,
    smul_eq_mul, hcycle]
  linear_combination h

/-- The actual radical quotient satisfies the polarized quadratic identity
with its own original descended trace. -/
theorem sourceTraceQuotient_polarized
    (τ : A →ₗ[R] R) (hCyc : ∀ x y, τ (x * y) = τ (y * x))
    (hTri : ∀ x y z, τ (x * y * z) + τ (x * z * y) =
      τ x * τ (y * z) + τ y * τ (x * z) + τ z * τ (x * y) - τ x * τ y * τ z)
    (x y : A ⧸ sourceTraceRadical τ hCyc) :
    x * y + y * x - sourceTraceQuotientLinear τ hCyc x • y -
      sourceTraceQuotientLinear τ hCyc y • x +
      (sourceTraceQuotientLinear τ hCyc x * sourceTraceQuotientLinear τ hCyc y -
        sourceTraceQuotientLinear τ hCyc (x * y)) • (1 : A ⧸ sourceTraceRadical τ hCyc) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (sourceTraceRadical_polarized τ hCyc hTri a b)
  change Ideal.Quotient.mkₐ R (sourceTraceRadical τ hCyc) _ = 0 at h
  simpa only [map_add, map_sub, map_mul, map_smul, map_one,
    Ideal.Quotient.mkₐ_eq_mk, sourceTraceQuotientLinear_mk] using h

end
end Dubon2026
