import Dubon2026.SourceAllPrimeCharacterWords

/-! DUB-17/18 -> rational Hecke operator descent -> faithful period
relations. An actual complex relation on cusp operators annihilates both
parts of the original period pair, since the genuine character operators
commute with reflection. Its proved surjectivity then annihilates every
actual parabolic character. No faithfulness or spanning input is assumed.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup SourceCuspBoundary
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Gamma0 N) 2

theorem sourceWeightTwoPeriodHom_injective :
    Function.Injective (sourceWeightTwoPeriodHom (Gamma0 N)) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply sourceWeightTwo_period_relation_zero N f 0
  intro γ
  have h := congrArg (fun ψ : Additive (Gamma0 N) →+ ℂ => ψ (Additive.ofMul γ)) hf
  change sourceWeightTwoPeriodValue (Gamma0 N) f γ = 0 at h
  simpa only [map_zero, Pi.zero_apply] using h

theorem sourceHeckeWord_relation_period {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (a : ι → FreeAlgebra ℤ Nat.Primes) (f : S) :
    sourceWeightTwoPeriodHom (Gamma0 N) ((∑ j ∈ s, c j • sourceWeightTwoCuspHeckeWord N (a j)) f) =
      (∑ j ∈ s, c j • sourceAllPrimeCharacterHeckeWord N ℂ (a j))
        (sourceWeightTwoPeriodHom (Gamma0 N) f) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    sourceAllPrimeCharacterHeckeWord_period]

theorem sourceHeckeWord_relation_parabolic {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (a : ι → FreeAlgebra ℤ Nat.Primes)
    (hc : ∑ j ∈ s, c j • sourceWeightTwoCuspHeckeWord N (a j) = 0)
    (φ : Additive (Gamma0 N) →+ ℂ) (hφ : φ ∈ parabolicHoms N) :
    (∑ j ∈ s, c j • sourceAllPrimeCharacterHeckeWord N ℂ (a j)) φ = 0 := by
  let D := ∑ j ∈ s, c j • sourceAllPrimeCharacterHeckeWord N ℂ (a j)
  have hD (f : S) : D (sourceWeightTwoPeriodHom (Gamma0 N) f) = 0 := by
    rw [← sourceHeckeWord_relation_period, hc, LinearMap.zero_apply, map_zero]
  have hDJ (ψ : Additive (Gamma0 N) →+ ℂ) :
      D (sourceWeightTwoPeriodReflection N ψ) = sourceWeightTwoPeriodReflection N (D ψ) := by
    simp only [D, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      sourceAllPrimeCharacterHeckeWord_reflection]
  obtain ⟨⟨f, g⟩, hfg⟩ := sourceWeightTwoParabolicPeriodPair_surjective N ⟨φ, hφ⟩
  have he : sourceWeightTwoPeriodPair N (f, g) = φ := congrArg Subtype.val hfg
  rw [← he]
  change D (sourceWeightTwoPeriodHom (Gamma0 N) f +
    sourceWeightTwoPeriodReflection N (sourceWeightTwoPeriodHom (Gamma0 N) f) +
    sourceWeightTwoPeriodHom (Gamma0 N) g -
    sourceWeightTwoPeriodReflection N (sourceWeightTwoPeriodHom (Gamma0 N) g)) = 0
  rw [map_sub, map_add, map_add, hDJ, hDJ, hD, hD, map_zero, zero_add, add_zero, sub_zero]

end
end Dubon2026
