/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the retained upstream LICENSE.
The finite Hall selection argument is adapted from ClassFieldTheory
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/SUnitKummerPrimeSelection/BasePlaceSelection.lean.
-/
import Dubon2026.OriginalPrimeTowerSelection
import Mathlib.Combinatorics.Hall.Finite

/-! # Distinct original base primes for the actual Kummer coordinates

Each actual order-p coordinate supplies infinitely many base-prime candidates
by original finite-fiber contraction and the proved norm-index contradiction.
Finite Hall selection chooses distinct original base primes simultaneously.
This discharges the distinctness and coordinate-place selection input to
DUB-17's required selected-prime cardinality. Splitting in the prescribed
subextension and the original S-unit localization equality remain to prove.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Actual coordinate primes can be chosen with distinct original base primes,
outside any prescribed finite support, with full coordinate decomposition groups. -/
theorem original_primeCoordinate_primes_distinct
    (p : ℕ) (hp : p.Prime) (r : ℕ) (H : Subgroup Gal(L/K))
    (e : H ≃* (Fin r → Multiplicative (ZMod p)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ w : Fin r → HeightOneSpectrum (𝓞 L),
      Function.Injective (fun i => originalFinitePrimeBelow K L (w i)) ∧
      ∀ i, originalFinitePrimeBelow K L (w i) ∉ S ∧
        OriginalFiniteDecompositionGroup
          (IntermediateField.fixedField (Subgroup.zpowers (primeCoordinateGenerator e i).val)) L (w i) = ⊤ := by
  let A (i : Fin r) : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | v ∉ S ∧ ∃ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w = v ∧
      OriginalFiniteDecompositionGroup
        (IntermediateField.fixedField (Subgroup.zpowers (primeCoordinateGenerator e i).val)) L w = ⊤}
  have hOrder (i : Fin r) : orderOf (primeCoordinateGenerator e i).val = p := by
    rw [Subgroup.orderOf_coe, primeCoordinateGenerator_order]
  have hA (i : Fin r) : (A i).Infinite := by
    intro hFinite
    obtain ⟨w, hw, hFull⟩ := original_primeOrder_fixedField_exists_fullDecomposition
      K L p hp (primeCoordinateGenerator e i).val (hOrder i) (S ∪ hFinite.toFinset)
    have hAvoid : originalFinitePrimeBelow K L w ∉ S := fun h => hw (Finset.mem_union_left _ h)
    have hMem : originalFinitePrimeBelow K L w ∈ hFinite.toFinset :=
      hFinite.mem_toFinset.mpr ⟨hAvoid, w, rfl, hFull⟩
    exact hw (Finset.mem_union_right _ hMem)
  choose B hSub hCard using fun i => (hA i).exists_subset_card_eq r
  have hHall : ∀ t : Finset (Fin r), t.card ≤ (t.biUnion B).card := by
    intro t
    by_cases ht : t.Nonempty
    · obtain ⟨i, hi⟩ := ht
      calc
        t.card ≤ r := by simpa using t.card_le_univ
        _ = (B i).card := (hCard i).symm
        _ ≤ (t.biUnion B).card := Finset.card_le_card (Finset.subset_biUnion_of_mem B hi)
    · simp [Finset.not_nonempty_iff_eq_empty.mp ht]
  obtain ⟨v, hv, hvB⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' B).mp hHall
  have hSpec (i : Fin r) : v i ∈ A i := hSub i (hvB i)
  choose w hBelow hFull using fun i => (hSpec i).2
  refine ⟨w, ?_, ?_⟩
  · intro i j hij
    apply hv
    rw [← hBelow i, ← hBelow j]
    exact hij
  · intro i
    refine ⟨?_, hFull i⟩
    rw [hBelow i]
    exact (hSpec i).1

end
end Dubon2026
