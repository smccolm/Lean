import Dubon2026.SourceOriginalTranslationOrbits
import Dubon2026.SourceOriginalFixedReducedDivisor

/-! DUB-17/18 -> arithmetic torsion surjectivity -> divisor support descent.
A finite original complex divisor fixed by a common nonzero power of every
Qbar-linear complex automorphism is supported on lifted arithmetic places.
Otherwise a translation of its nonarithmetic j-value gives infinitely many
distinct places in the same finite support.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
attribute [local instance] complexAlgebra
variable (N : ℕ) [NeZero N]
local notation "FC" => modularFunctionFieldOver N ℂ

theorem original_invariant_support_lifts (A : Divisor ℂ FC) (M : ℕ) (hM : M ≠ 0)
    (hA : ∀ ρ : ℂ ≃ₐ[Qbar] ℂ, originalArithmeticDivisorEquiv N (complexAutRestrict ρ ^ M) A = A) :
    ∀ W ∈ A.support, ∃ P, W = liftPlace N P := by
  classical
  intro W hW
  by_contra hoff
  push Not at hoff
  obtain ⟨t, ht, hval⟩ := off_image_exists_nonarithmetic_j_value N W hoff
  obtain ⟨ρ, hρ, _, _⟩ := exists_original_complex_translation N ht (M : Qbar)⁻¹
  let τ : ℂ ≃ₐ[ℚ] ℂ := complexAutRestrict ρ ^ M
  have hτ (k : ℕ) : (τ ^ k) t = t + k := by
    dsimp only [τ]
    rw [← pow_mul, ← map_pow]
    change (ρ ^ (M * k)) t = t + k
    rw [complex_translation_pow ρ (M : Qbar)⁻¹ hρ]
    have hm : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
    rw [map_inv₀, map_natCast]
    push_cast
    field_simp
  have hinj := original_translation_orbit_injective N τ W t hval hτ
  have hmem (k : ℕ) : originalArithmeticPlace N (τ ^ k) W ∈ (A.support : Set (Place ℂ FC)) := by
    have hk := original_divisor_pow_fixed N τ A (hA ρ) k
    have hv := originalArithmeticDivisorEquiv_apply N (τ ^ k) A W
    rw [hk] at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hv]
    exact Finsupp.mem_support_iff.mp hW
  exact Set.infinite_of_injective_forall_mem hinj hmem A.support.finite_toSet

end
end Dubon2026.SourceFunctionField.OriginalConstantField
