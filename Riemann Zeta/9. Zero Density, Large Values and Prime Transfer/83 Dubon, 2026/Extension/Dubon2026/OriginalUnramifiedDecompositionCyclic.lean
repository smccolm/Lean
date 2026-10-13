import Dubon2026.OriginalAdicDecompositionAction
import Dubon2026.OriginalFinitePrimeOrbits
import Dubon2026.NumberFieldInertiaRamification
import Dubon2026.NumberFieldRamificationUnramified
import Mathlib.RingTheory.Unramified.Locus

/-! # Cyclicity of the actual original unramified decomposition group

The existing original inertia calculation makes the residue action faithful
at an unramified prime. The actual residue field is finite, so its Galois
group is cyclic. This identifies the group-theoretic constraint at the
selected coordinate primes for DUB-17's required S-unit localization chain.
It reuses the original integer-ring action without a new local-field model.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Pointwise
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The actual original prime stabilizer acts through the same original ideal stabilizer. -/
def originalFiniteDecompositionIdealMap (w : HeightOneSpectrum (𝓞 L)) :
    OriginalFiniteDecompositionGroup K L w →* MulAction.stabilizer Gal(L/K) w.asIdeal where
  toFun σ := ⟨σ.val, by
    have h := congrArg HeightOneSpectrum.asIdeal σ.property
    change (numberFieldGaloisPlaceEquiv K L σ.val w).asIdeal = w.asIdeal at h
    rw [numberFieldGaloisPlaceEquiv_asIdeal] at h
    change σ.val • w.asIdeal = w.asIdeal
    rw [Ideal.pointwise_smul_def]
    have he : MulSemiringAction.toRingHom Gal(L/K) (𝓞 L) σ.val =
        (NumberField.RingOfIntegers.mapAlgEquiv σ.val).toRingHom := by
      ext a
      rfl
    rw [he]
    exact h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- Passing from an original prime stabilizer to its original ideal action is injective. -/
theorem originalFiniteDecompositionIdealMap_injective (w : HeightOneSpectrum (𝓞 L)) :
    Function.Injective (originalFiniteDecompositionIdealMap K L w) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : MulAction.stabilizer Gal(L/K) w.asIdeal => z.val) h

/-- The actual original decomposition group is cyclic at every absolutely unramified prime. -/
theorem originalFiniteDecomposition_isCyclic_of_unramified
    (w : HeightOneSpectrum (𝓞 L)) (hw : Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    IsCyclic (OriginalFiniteDecompositionGroup K L w) := by
  let v := originalFinitePrimeBelow K L w
  letI : w.asIdeal.LiesOver v.asIdeal := originalFinitePrimeBelow_liesOver K L w
  letI : Algebra.IsUnramifiedAt ℤ w.asIdeal := hw
  letI : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := Algebra.IsUnramifiedAt.of_restrictScalars ℤ w.asIdeal
  have hIndex : v.asIdeal.ramificationIdx w.asIdeal = 1 :=
    (numberField_isUnramifiedAt_iff_ramificationIdx_one v w).mp inferInstance
  have hInertia := numberField_inertia_eq_bot_of_ramificationIdx_one v w hIndex
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  let f := Ideal.Quotient.stabilizerHom w.asIdeal v.asIdeal Gal(L/K)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [Ideal.Quotient.ker_stabilizerHom, hInertia]
    exact Subgroup.bot_subgroupOf _
  letI : IsCyclic (MulAction.stabilizer Gal(L/K) w.asIdeal) := isCyclic_of_injective f hf
  exact isCyclic_of_injective (originalFiniteDecompositionIdealMap K L w)
    (originalFiniteDecompositionIdealMap_injective K L w)

end
end Dubon2026
