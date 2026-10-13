/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the retained upstream LICENSE.
The norm-approximation contradiction is adapted to original objects and
prime degree from ClassFieldTheory dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/GlobalClassFieldTheory/Cohomology/CyclicPrimePowerFullDecomposition.lean.
-/
import Dubon2026.OriginalPrincipalPowerApproximation
import Dubon2026.OriginalIdeleNormLocalGlobal
import Dubon2026.OriginalLocalNormSplitPrime
import Dubon2026.OriginalIdeleClassNorm

/-! # Original class norms when almost all finite places split

Mixed approximation places every exceptional finite and every infinite local
ratio in the degree-power subgroup, already proved to lie in the actual norm
image. Split places supply all remaining local preimages. The original idele
norm-image theorem then proves class norm surjectivity. Together with the
proved degree lower bound, this forces nonsplit primes for DUB-17's Kummer
prime-selection and global norm-index argument.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- If every finite place outside the actual support splits, one actual principal
correction puts all original local components in their actual local norm images. -/
theorem originalIdele_principal_norm_correction
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSplit : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      OriginalFiniteDecompositionGroup K L w = ⊥)
    (a : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ x : Kˣ,
      (∀ w : HeightOneSpectrum (𝓞 L),
        numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w)
          (a * (numberFieldPrincipalIdele K x)⁻¹) ∈ (originalFiniteLocalNorm K L w).range) ∧
      (∀ w : InfinitePlace L,
        numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L))
          (a * (numberFieldPrincipalIdele K x)⁻¹) ∈ (originalInfiniteLocalNorm K L w).range) := by
  let A : ∀ i, (OriginalApproximationCompletion K S i)ˣ
    | Sum.inl v => numberFieldIdeleFiniteComponent K v.1 a
    | Sum.inr w => numberFieldIdeleInfiniteComponent K w a
  obtain ⟨x, hx⟩ := original_principalUnit_power_approximation K S
    (Module.finrank K L) Module.finrank_pos A
  refine ⟨x, ?_, ?_⟩
  · intro w
    by_cases hw : originalFinitePrimeBelow K L w ∈ S
    · obtain ⟨u, hu⟩ := hx (Sum.inl ⟨originalFinitePrimeBelow K L w, hw⟩)
      have he :
          numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w)
            (a * (numberFieldPrincipalIdele K x)⁻¹) = u ^ Module.finrank K L := by
        rw [map_mul, map_inv]
        exact hu.symm
      rw [he]
      exact originalFiniteLocalNorm_degreePower K L w u
    · exact originalFiniteLocalNorm_surjective_of_split K L w (hSplit w hw) _
  · intro w
    obtain ⟨u, hu⟩ := hx (Sum.inr (w.comap (algebraMap K L)))
    have he :
        numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L))
          (a * (numberFieldPrincipalIdele K x)⁻¹) = u ^ Module.finrank K L := by
      rw [map_mul, map_inv]
      exact hu.symm
    rw [he]
    exact originalInfiniteLocalNorm_degreePower K L w u

/-- Splitting at every original finite place outside a finite set would make
the actual original idele-class norm surjective. -/
theorem originalIdeleClassNorm_surjective_of_split_outside
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSplit : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      OriginalFiniteDecompositionGroup K L w = ⊥) :
    Function.Surjective (originalIdeleClassNorm K L) := by
  intro c
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (numberFieldPrincipalIdele K).range c
  obtain ⟨x, hFin, hInf⟩ := originalIdele_principal_norm_correction K L S hSplit a
  obtain ⟨b, hb⟩ := originalIdeleNorm_exists_of_local K L
    (a * (numberFieldPrincipalIdele K x)⁻¹) hFin hInf
  refine ⟨QuotientGroup.mk' (numberFieldPrincipalIdele L).range b, ?_⟩
  rw [originalIdeleClassNorm_mk, hb, map_mul, map_inv]
  have hp : QuotientGroup.mk' (numberFieldPrincipalIdele K).range
      (numberFieldPrincipalIdele K x) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  rw [hp, inv_one]
  exact mul_one (QuotientGroup.mk' (numberFieldPrincipalIdele K).range a)

end
end Dubon2026
