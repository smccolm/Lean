import Dubon2026.SourceGammaOneNormRelation

/-! DUB-17/18 -> arithmetic Gamma1 realization -> finite Gamma1 function field.
The actual modular norm relation gives a nonzero polynomial relation of degree
at most the subgroup index, with coefficients polynomial in the original j.
Only cancellation by proved nonzero discriminant and denominator series is used.
Rational descent and the field-wide finite-dimension consequence remain next. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Polynomial ModularNormPolynomial
open scoped MatrixGroups

private theorem cancel_homogeneous_relation {F : Type*} [Field F] {c m : ℕ}
    (a b : Fin (c + 1) → F) (x y d : F) (hy : y ≠ 0) (hd : d ≠ 0)
    (hab : ∀ i, a i = b i * d ^ m)
    (hsum : ∑ i, a i * x ^ (i : ℕ) * y ^ (c - (i : ℕ)) = 0) :
    ∑ i, b i * (x / y) ^ (i : ℕ) = 0 := by
  have hid : (∑ i, b i * (x / y) ^ (i : ℕ)) * (d ^ m * y ^ c) = 0 := by
    rw [Finset.sum_mul]
    calc
      _ = ∑ i, a i * x ^ (i : ℕ) * y ^ (c - (i : ℕ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hab, pow_sub₀ _ hy (Nat.lt_succ_iff.mp i.2), div_pow]
        field_simp
      _ = 0 := hsum
  exact (mul_eq_zero.mp hid).resolve_right
    (mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ hy))

theorem exists_complex_j_relation
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne] {K : ℕ}
    (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods)
    (f g : ModularForm 𝒢 (12 * (K : ℤ))) (hg : g ≠ 0) :
    ∃ P : Fin (Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) + 1) → Polynomial ℂ,
      (∀ i, (P i).natDegree ≤ K * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)) ∧
      P ⟨Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ), Nat.lt_succ_self _⟩ ≠ 0 ∧
      ∑ i, Polynomial.aeval (jqModC ℂ) (P i) *
        ((qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) /
          (qExpansion 1 (g : ℍ → ℂ) : LaurentSeries ℂ)) ^ (i : ℕ) = 0 := by
  classical
  let c := Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)
  let Φ : PowerSeries ℂ →+* LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ
  have hΦ : Function.Injective Φ := HahnSeries.ofPowerSeries_injective
  have hy : Φ (qExpansion 1 (g : ℍ → ℂ)) ≠ 0 := by
    intro hz
    have hq : qExpansion 1 (g : ℍ → ℂ) = 0 := hΦ (by rw [map_zero]; exact hz)
    exact hg ((ModularForm.qExpansion_eq_zero_iff one_pos h1 g).mp hq)
  choose P hPdeg hP using fun i : Fin (c + 1) =>
    norm_coefficient_j_polynomial f g (i : ℕ)
  refine ⟨P, hPdeg, ?_, ?_⟩
  · intro hz
    have ht := hP ⟨c, Nat.lt_succ_self c⟩
    rw [hz, map_zero, zero_mul] at ht
    apply qExpansion_Aform_top_ne_zero f g hg
    exact hΦ (by rw [map_zero]; exact ht)
  · have hs := congrArg Φ (norm_qExpansion_relation h1 f g)
    rw [map_sum, map_zero] at hs
    have hs' : ∑ i : Fin (c + 1),
        Φ (qExpansion 1 (Aform f g (i : ℕ) : ℍ → ℂ)) *
          Φ (qExpansion 1 (f : ℍ → ℂ)) ^ (i : ℕ) *
          Φ (qExpansion 1 (g : ℍ → ℂ)) ^ (c - (i : ℕ)) = 0 := by
      rw [← hs]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_mul, map_pow, map_pow]
    exact cancel_homogeneous_relation
      (fun i => Φ (qExpansion 1 (Aform f g (i : ℕ) : ℍ → ℂ)))
      (fun i => Polynomial.aeval (jqModC ℂ) (P i))
      (Φ (qExpansion 1 (f : ℍ → ℂ))) (Φ (qExpansion 1 (g : ℍ → ℂ)))
      (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ)
      hy discriminant_expansion_ne_zero hP hs'

end
end Dubon2026.SourceFunctionField.GammaOne
