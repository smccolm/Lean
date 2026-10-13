import Dubon2026.OriginalSelectedCorrectionNorm
import Dubon2026.OriginalNormSurjectiveDescent
import Dubon2026.OriginalGeneratedKummerSplit
import Dubon2026.OriginalGeneratedKummerUnramified
import Dubon2026.OriginalPrimeKummerWitness
import Dubon2026.OriginalSUnitPowerLocalQuotient
import Dubon2026.SUnitPowerSaturation

/-! # The original principal S-union-T localization equality

For an actual principal local-power element, failure of a global prime
power constructs an actual simple cyclic Kummer extension. Its generating
root proves splitting at S and infinity; original inertia and the unit
conditions prove outside unramifiedness. The actual S-unit corrections
make its original class norm surjective. The proved degree lower bound
then descends the root to the base field, contradicting failure of a global
power. Existing S-unit power saturation gives the literal subgroup
equality required by DUB-17's principal/class index calculation.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type) [Field K] [NumberField K]

/-- The actual principal local-power subgroup is exactly the actual global
power subgroup, with local corrections and support conditions explicit. -/
theorem originalSUnitPowerLocalSubgroup_eq_powers
    (p : ℕ) (hp : p.Prime) (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hClasses : Function.Surjective (numberFieldSupportedIdeleClassMap K S))
    (hSurj : Function.Surjective (originalSUnitLocalPowerMap K p S T hST))
    (hBase : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Algebra.IsUnramifiedAt ℤ v.asIdeal)
    (hAway : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (p : 𝓞 K) ∉ v.asIdeal) :
    originalSUnitPowerLocalSubgroup K p S T =
      (powMonoidHom p : ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K) →*
        ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))).unit K)).range := by
  ext x
  constructor
  · intro hx
    apply (sUnit_mem_power_range_iff (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) p hp.ne_zero x).mpr
    by_contra hNot
    have hroot : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
    obtain ⟨hFinite, hGalois, hCyclic, hDegree, β, hβ, hGen⟩ :=
      originalPrimeKummerField_data K p hp hroot x.val hNot
    let L := OriginalSimpleKummerField K p x.val
    letI : FiniteDimensional K L := hFinite
    letI : IsGalois K L := hGalois
    letI : IsCyclic Gal(L/K) := hCyclic
    letI : NumberField L := NumberField.of_module_finite K L
    have hData := (originalSUnitPowerLocalSubgroup_mem_iff K p S T x).mp hx
    have hNorm : Function.Surjective (originalIdeleClassNorm K L) := by
      apply originalIdeleClassNorm_surjective_of_selected_corrections K L p
        hDegree.dvd S T hST hClasses hSurj
      · intro w hw
        exact originalGeneratedKummer_finite_split K L w p hp.pos ζ hζ x.val β hβ hGen
          (hData.2 (originalFinitePrimeBelow K L w) hw)
      · intro w
        apply originalInfiniteLocalNorm_surjective_of_split K L w
        exact originalGeneratedKummer_infinite_split K L w p hp.pos ζ hζ x.val β hβ hGen
          (hData.1 (w.comap (algebraMap K L)))
      · intro w hw
        let v := originalFinitePrimeBelow K L w
        letI : w.asIdeal.LiesOver v.asIdeal := originalFinitePrimeBelow_liesOver K L w
        have hvS : v ∉ S := fun h => hw (Finset.mem_union_left _ h)
        exact originalGeneratedKummer_unramified_of_base_units K L v w
          (hBase v hvS) p hp.pos (hAway v hvS) x.val (x.property v hw) β hβ hGen
    exact hNot (originalCyclicNormSurjective_power_descent K L hNorm p x.val β hβ)
  · rintro ⟨y, rfl⟩
    apply (originalSUnitPowerLocalSubgroup_mem_iff K p S T _).mpr
    constructor
    · intro w
      refine ⟨numberFieldIdeleInfiniteComponent K w (numberFieldPrincipalIdele K y.val), ?_⟩
      exact (map_pow ((numberFieldIdeleInfiniteComponent K w).comp (numberFieldPrincipalIdele K)) y.val p).symm
    · intro v _
      refine ⟨numberFieldIdeleFiniteComponent K v (numberFieldPrincipalIdele K y.val), ?_⟩
      exact (map_pow ((numberFieldIdeleFiniteComponent K v).comp (numberFieldPrincipalIdele K)) y.val p).symm

end
end Dubon2026
