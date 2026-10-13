/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the retained upstream LICENSE.
The norm-approximation contradiction is adapted to original objects and
prime degree from ClassFieldTheory dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/GlobalClassFieldTheory/Cohomology/CyclicPrimePowerFullDecomposition.lean.
-/
import Dubon2026.OriginalSplitOutsideNorm
import Dubon2026.OriginalIdeleClassNativeNormQuotient

/-! # Actual full-decomposition primes in prime-degree extensions

If only finitely many original primes had full decomposition group, every
remaining decomposition group would be trivial. The proved original norm
correction would make the class norm surjective, contradicting its already
proved degree lower bound. This supplies the prime-degree avoidance result
needed to select actual Kummer coordinates for DUB-17's norm-index upper bound;
no prime-power generalization or analytic distribution theorem is used.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Splitting outside finite support would force the actual cyclic class norm
quotient to have order one. -/
theorem originalIdeleClassNormQuotient_card_one_of_split_outside
    [IsCyclic Gal(L/K)]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSplit : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      OriginalFiniteDecompositionGroup K L w = ⊥) :
    Nat.card (OriginalIdeleClassNormQuotient K L) = 1 := by
  have hsurj := originalIdeleClassNorm_surjective_of_split_outside K L S hSplit
  have hr : (originalIdeleClassNormLinear K L).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro c
    obtain ⟨b, hb⟩ := hsurj c.toMul
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  change Nat.card (Additive (OriginalNumberFieldIdeleClassGroup K) ⧸
    (originalIdeleClassNormLinear K L).range) = 1
  rw [hr]
  exact Nat.card_unique

/-- An actual prime with full decomposition group exists above a base prime
outside any prescribed finite set in every prime-degree Galois extension. -/
theorem original_primeDegree_exists_fullDecomposition_outside
    (hp : (Module.finrank K L).Prime)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∧
      OriginalFiniteDecompositionGroup K L w = ⊤ := by
  have hcard : Nat.card Gal(L/K) = Module.finrank K L := by
    exact IsGalois.card_aut_eq_finrank K L
  letI : Fact (Nat.card Gal(L/K)).Prime := ⟨hcard.symm ▸ hp⟩
  letI : IsCyclic Gal(L/K) := isCyclic_of_prime_card (rfl : Nat.card Gal(L/K) = Nat.card Gal(L/K))
  by_contra h
  have hSplit : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S →
      OriginalFiniteDecompositionGroup K L w = ⊥ := by
    intro w hw
    rcases (OriginalFiniteDecompositionGroup K L w).eq_bot_or_eq_top_of_prime_card with hb | ht
    · exact hb
    · exact False.elim (h ⟨w, hw, ht⟩)
  have hOne := originalIdeleClassNormQuotient_card_one_of_split_outside K L S hSplit
  have hLower := (originalIdeleClassNormQuotient_degree_lower K L).2
  rw [hOne] at hLower
  exact (not_le_of_gt hp.one_lt) hLower

/-- Infinitely many actual base primes support full original decomposition
groups in every prime-degree Galois extension. -/
theorem original_primeDegree_fullDecomposition_infinite
    (hp : (Module.finrank K L).Prime) :
    Set.Infinite {v : HeightOneSpectrum (𝓞 K) | ∃ w : HeightOneSpectrum (𝓞 L),
      originalFinitePrimeBelow K L w = v ∧ OriginalFiniteDecompositionGroup K L w = ⊤} := by
  intro h
  obtain ⟨w, hw, hFull⟩ := original_primeDegree_exists_fullDecomposition_outside K L hp h.toFinset
  apply hw
  exact h.mem_toFinset.mpr ⟨w, rfl, hFull⟩

end
end Dubon2026
