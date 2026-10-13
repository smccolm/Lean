import Dubon2026.OriginalUnramifiedDecompositionCyclic
import Dubon2026.OriginalPrimeTowerSelection
import Dubon2026.FiniteCyclicSubgroupContainment

/-! # Original decomposition groups over coordinate fixed fields

The full relative decomposition group over a coordinate fixed field forces
the original coordinate subgroup into the original base decomposition group.
At an unramified place, cyclicity and the Kummer exponent then identify the
whole original stabilizer with that prescribed coordinate subgroup. This
discharges the stabilizer identification needed by DUB-17's S-unit selection.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- Restriction of scalar structure does not change the actual permutation of original primes. -/
theorem originalFinitePlace_restrictScalars
    (K F L : Type) [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    (σ : Gal(L/F)) (w : HeightOneSpectrum (𝓞 L)) :
    numberFieldGaloisPlaceEquiv K L (σ.restrictScalars K) w =
      numberFieldGaloisPlaceEquiv F L σ w := rfl

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- Full decomposition over the actual fixed field puts the original fixing subgroup
inside the original base-field decomposition group. -/
theorem originalFiniteDecomposition_contains_of_relative_top
    (H : Subgroup Gal(L/K)) (w : HeightOneSpectrum (𝓞 L))
    (hFull : OriginalFiniteDecompositionGroup (IntermediateField.fixedField H) L w = ⊤) :
    H ≤ OriginalFiniteDecompositionGroup K L w := by
  intro g hg
  let σ := IntermediateField.subgroupEquivAlgEquiv H ⟨g, hg⟩
  have hσ : σ ∈ OriginalFiniteDecompositionGroup (IntermediateField.fixedField H) L w := by
    rw [hFull]
    exact Subgroup.mem_top σ
  change numberFieldGaloisPlaceEquiv (IntermediateField.fixedField H) L σ w = w at hσ
  change numberFieldGaloisPlaceEquiv K L g w = w
  exact hσ

/-- At an absolutely unramified place in an exponent-p extension, full relative
decomposition over an order-p coordinate fixed field identifies the entire
original base-field decomposition group with that coordinate subgroup. -/
theorem originalFiniteDecomposition_eq_zpowers_of_relative_top
    (p : ℕ) (hp : 0 < p) (hPower : ∀ σ : Gal(L/K), σ ^ p = 1)
    (g : Gal(L/K)) (hg : orderOf g = p) (w : HeightOneSpectrum (𝓞 L))
    (hw : Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (hFull : OriginalFiniteDecompositionGroup
      (IntermediateField.fixedField (Subgroup.zpowers g)) L w = ⊤) :
    OriginalFiniteDecompositionGroup K L w = Subgroup.zpowers g := by
  let D := OriginalFiniteDecompositionGroup K L w
  letI : IsCyclic D := originalFiniteDecomposition_isCyclic_of_unramified K L w hw
  have hle : Subgroup.zpowers g ≤ D :=
    originalFiniteDecomposition_contains_of_relative_top K L (Subgroup.zpowers g) w hFull
  apply (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, hg]
  apply Nat.le_of_dvd hp
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro σ
  apply Subtype.ext
  exact hPower σ.val

end
end Dubon2026
