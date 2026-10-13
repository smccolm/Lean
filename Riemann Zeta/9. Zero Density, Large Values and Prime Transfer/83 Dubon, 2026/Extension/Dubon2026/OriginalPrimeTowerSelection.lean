import Dubon2026.OriginalPrimeDegreeFullDecomposition
import Dubon2026.PrimeCoordinateGenerators

/-! # Prime-degree coordinate places avoiding original base primes

The prime-existence theorem must avoid primes of the original base field,
even when applied over a coordinate fixed field. Actual contraction in a
tower and its proved finite fibers give exactly that strengthened avoidance.
For an order-p automorphism, its genuine fixed field has top extension degree
p. These are the coordinate-place inputs to DUB-17's selected-prime set.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- Actual original prime contraction is transitive along the original field tower. -/
theorem originalFinitePrimeBelow_tower
    (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] (w : HeightOneSpectrum (𝓞 L)) :
    originalFinitePrimeBelow K E (originalFinitePrimeBelow E L w) =
      originalFinitePrimeBelow K L w := by
  apply HeightOneSpectrum.ext
  exact Ideal.under_under w.asIdeal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A prime-degree top extension supplies full-decomposition places avoiding
any prescribed finite set of primes of the actual original base field. -/
theorem original_primeDegree_tower_exists_fullDecomposition
    (F : IntermediateField K L) (hp : (Module.finrank F L).Prime)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∧
      OriginalFiniteDecompositionGroup F L w = ⊤ := by
  letI : NumberField F := NumberField.of_module_finite K F
  let hFinite := originalFinitePrimeBelow_preimage_finite K F (S : Set _) S.finite_toSet
  obtain ⟨w, hw, hFull⟩ := original_primeDegree_exists_fullDecomposition_outside F L hp hFinite.toFinset
  refine ⟨w, ?_, hFull⟩
  intro hS
  apply hw
  apply hFinite.mem_toFinset.mpr
  change originalFinitePrimeBelow K F (originalFinitePrimeBelow F L w) ∈ S
  rw [originalFinitePrimeBelow_tower]
  exact hS

/-- The genuine fixed field of an original order-p automorphism gives the
required coordinate extension and primes avoiding every finite base support. -/
theorem original_primeOrder_fixedField_exists_fullDecomposition
    (p : ℕ) (hp : p.Prime) (g : Gal(L/K)) (hg : orderOf g = p)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∧
      OriginalFiniteDecompositionGroup (IntermediateField.fixedField (Subgroup.zpowers g)) L w = ⊤ := by
  apply original_primeDegree_tower_exists_fullDecomposition K L
  have hDegree : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers g)) L = p := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hg]
  exact hDegree.symm ▸ hp

end
end Dubon2026
