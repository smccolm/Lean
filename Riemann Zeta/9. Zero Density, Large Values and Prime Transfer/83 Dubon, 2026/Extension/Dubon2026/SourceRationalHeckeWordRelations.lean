import Dubon2026.SourceHeckeWordParabolicRelations

/-! DUB-17/18 -> rational Hecke descent -> rational coordinates of
actual complex operator relations. Rational character values allow a
Q-coordinate projection on each scalar coefficient. The rational span
theorem and faithful original period map then return a cusp-operator
relation. Adapted from the coordinate argument in
S_CuspForm_linearIndependent_complex_of_linearIndependent_int,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup SourceCuspBoundary
variable (N : ℕ) [NeZero N]
local notation "bC" => Module.Basis.ofVectorSpace ℚ ℂ

theorem sourceHeckeWord_relation_rational_character {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (a : ι → FreeAlgebra ℤ Nat.Primes)
    (hc : ∑ j ∈ s, c j • sourceWeightTwoCuspHeckeWord N (a j) = 0)
    (β : Module.Basis.ofVectorSpaceIndex ℚ ℂ)
    (φ : Additive (Gamma0 N) →+ ℚ) (hφ : φ ∈ sourceRationalParabolicHoms N) :
    (∑ j ∈ s, ((bC).repr (c j) β : ℂ) • sourceAllPrimeCharacterHeckeWord N ℂ (a j))
      (sourceRationalCharacterComplex N φ) = 0 := by
  let y : ι → ℚ := fun j => (bC).repr (c j) β
  let ψ : ι → (Additive (Gamma0 N) →+ ℚ) := fun j => sourceAllPrimeCharacterHeckeWord N ℚ (a j) φ
  have h0 := sourceHeckeWord_relation_parabolic N s c a hc
    (sourceRationalCharacterComplex N φ) (sourceRationalCharacterComplex_parabolic N φ hφ)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, sourceAllPrimeCharacterHeckeWord_rational] at h0 ⊢
  apply AddMonoidHom.ext
  intro γ
  have h1 := congrArg (fun χ : Additive (Gamma0 N) →+ ℂ => (bC).repr (χ γ) β) h0
  simp only [AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply,
    sourceRationalCharacterComplex_apply, smul_eq_mul, map_sum, AddMonoidHom.zero_apply,
    map_zero, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
  have h2 (j : ι) : (bC).repr (c j * (ψ j γ : ℂ)) β = ψ j γ * y j := by
    rw [mul_comm, ← Rat.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  change (∑ j ∈ s, (bC).repr (c j * (ψ j γ : ℂ)) β) = 0 at h1
  simp only [h2] at h1
  rw [AddMonoidHom.finsetSum_apply, AddMonoidHom.zero_apply]
  simp only [AddMonoidHom.smul_apply, sourceRationalCharacterComplex_apply, smul_eq_mul]
  change (∑ j ∈ s, (y j : ℂ) * (ψ j γ : ℂ)) = 0
  have h3 : (∑ j ∈ s, (y j : ℂ) * (ψ j γ : ℂ)) = ((∑ j ∈ s, ψ j γ * y j : ℚ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h3, h1, Rat.cast_zero]

theorem sourceHeckeWord_relation_coordinate {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (a : ι → FreeAlgebra ℤ Nat.Primes)
    (hc : ∑ j ∈ s, c j • sourceWeightTwoCuspHeckeWord N (a j) = 0)
    (β : Module.Basis.ofVectorSpaceIndex ℚ ℂ) :
    ∑ j ∈ s, ((bC).repr (c j) β : ℂ) • sourceWeightTwoCuspHeckeWord N (a j) = 0 := by
  let y : ι → ℚ := fun j => (bC).repr (c j) β
  let D := ∑ j ∈ s, (y j : ℂ) • sourceAllPrimeCharacterHeckeWord N ℂ (a j)
  have hle : Submodule.span ℂ (sourceRationalCharacterComplex N ''
      (sourceRationalParabolicHoms N : Set (Additive (Gamma0 N) →+ ℚ))) ≤ LinearMap.ker D := by
    rw [Submodule.span_le]
    rintro _ ⟨φ, hφ, rfl⟩
    exact sourceHeckeWord_relation_rational_character N s c a hc β φ hφ
  apply LinearMap.ext
  intro f
  apply sourceWeightTwoPeriodHom_injective N
  rw [sourceHeckeWord_relation_period, LinearMap.zero_apply, map_zero]
  exact hle (sourceParabolicCharacter_mem_rational_span N _ (sourceWeightTwoPeriodHom_parabolic N f))

end
end Dubon2026
