import Dubon2026.NumberFieldSelmerFinite
import Dubon2026.UnramifiedRadicalSelmer
import Dubon2026.GaloisRadicalClassIndependence
import Dubon2026.PrimeRootUnitCharacters

/-! # Actual continuous Galois character finiteness from genuine unramified subextensions -/

namespace Dubon2026

open scoped NumberField

noncomputable section
open IsDedekindDomain

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Every actual finite Galois subextension of an extension of the original number field is itself a number field. -/
instance finiteGaloisIntermediateFieldNumberField (F : FiniteGaloisIntermediateField K Ω) :
    NumberField F := NumberField.of_module_finite K F

variable [IsGalois K Ω] [TopologicalSpace Kˣ] [DiscreteTopology Kˣ]

/-- If the actual finite Galois subextensions are unramified at genuine primes outside S, the original continuous character's actual Kummer class lies in the original number-field Selmer group. -/
theorem unramified_continuousGaloisKummerClass_mem_selmer
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (hunram : ∀ F : FiniteGaloisIntermediateField K Ω,
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
          v.asIdeal.ramificationIdx w.asIdeal = 1)
    (n : ℕ) (χ : ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) n) :
    continuousGaloisKummerClass n χ ∈
      IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := S) (n := n) := by
  obtain ⟨F, ψ, hfactor⟩ := continuous_galois_finite_factor χ.val
  have hψ : ∀ g : Gal(F/K), ψ g ^ n = 1 := by
    intro g
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω g
    rw [hfactor, χ.property]
  obtain ⟨a, β, hpower, hratio⟩ := finiteGaloisCharacter_exists_radical ψ n hψ
  have hselmer := unramified_radical_mem_selmer
    (R := 𝓞 K) (S := 𝓞 F) (K := K) (L := F) S (hunram F) n a β hpower
  let i := F.toIntermediateField.val
  let βΩ := Units.map i.toMonoidHom β
  have hpowerΩ : βΩ ^ n = Units.map (algebraMap K Ω).toMonoidHom a := by
    apply Units.ext
    change i β.val ^ n = algebraMap K Ω a.val
    have hval : β.val ^ n = algebraMap K F a.val := congrArg Units.val hpower
    rw [← map_pow, hval, i.commutes]
  have hratioΩ : ∀ g : Gal(Ω/K), g • βΩ / βΩ =
      Units.map (algebraMap K Ω).toMonoidHom (χ.val g) := by
    intro g
    apply Units.ext
    simp only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
      MonoidHom.coe_coe, βΩ]
    change g (i β.val) / i β.val = algebraMap K Ω (χ.val g).val
    have hval := congrArg Units.val (hratio (AlgEquiv.restrictNormalHom F g))
    simp only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
      MonoidHom.coe_coe] at hval
    change (AlgEquiv.restrictNormalHom F g) β.val / β.val =
      algebraMap K F (ψ (AlgEquiv.restrictNormalHom F g)).val at hval
    have hcompat : i ((AlgEquiv.restrictNormalHom F g) β.val) = g (i β.val) :=
      AlgEquiv.restrictNormal_commutes g F β.val
    have h := congrArg i hval
    simpa only [map_div₀, hcompat,
      AlgHom.commutes, hfactor] using h
  rw [continuousGaloisKummerClass_eq_of_radical n χ a βΩ hpowerΩ hratioΩ]
  exact hselmer

/-- Genuine unramified finite-subextension hypotheses give a finite original continuous exponent-character set by the actual injective map into the proved finite original Selmer group. -/
theorem unramified_continuous_exponent_characters_finite
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (hunram : ∀ F : FiniteGaloisIntermediateField K Ω,
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
          v.asIdeal.ramificationIdx w.asIdeal = 1)
    (n : ℕ) (hn : n ≠ 0) (hζ : (primitiveRoots n K).Nonempty) :
    Finite (ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) n) := by
  letI : NeZero n := ⟨hn⟩
  letI := numberField_selmer_finite K S hS n hn
  let f : ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) n →
      IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := S) (n := n) :=
    fun χ => ⟨continuousGaloisKummerClass n χ,
      unramified_continuousGaloisKummerClass_mem_selmer S hunram n χ⟩
  apply Finite.of_injective f
  intro χ ψ h
  exact continuousGaloisKummerClass_injective n hζ (congrArg Subtype.val h)

/-- For an original number field containing the required roots of unity, genuine unramified finite-subextension hypotheses imply finiteness of its exact original continuous prime-order Galois characters. -/
theorem unramified_continuous_prime_characters_finite
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (hunram : ∀ F : FiniteGaloisIntermediateField K Ω,
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
          v.asIdeal.ramificationIdx w.asIdeal = 1)
    (p : ℕ) (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Finite (Gal(Ω/K) →ₜ* Multiplicative (ZMod p)) := by
  have hroots : (primitiveRoots p K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  letI := unramified_continuous_exponent_characters_finite S hS hunram p hp.ne_zero hroots
  exact prime_characters_finite_of_unit_exponent_characters p hp hζ

end
end Dubon2026
