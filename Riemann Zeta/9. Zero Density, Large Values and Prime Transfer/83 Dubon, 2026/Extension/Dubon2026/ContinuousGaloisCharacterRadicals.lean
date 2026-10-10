import Dubon2026.ContinuousGaloisFiniteFactors
import Dubon2026.FiniteGaloisCharacterRadicals

/-! # Actual radicals for original continuous characters of infinite Galois groups -/

namespace Dubon2026

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- An original open-kernel Galois character killed by n has an actual radical in the original extension with the exact original character ratios. -/
theorem open_kernel_galois_character_exists_radical
    (χ : Gal(Ω/K) →* Kˣ) (hopen : IsOpen (χ.ker : Set Gal(Ω/K)))
    (n : ℕ) (hχ : ∀ g : Gal(Ω/K), χ g ^ n = 1) :
    ∃ (a : Kˣ) (β : Ωˣ),
      β ^ n = Units.map (algebraMap K Ω).toMonoidHom a ∧
      ∀ g : Gal(Ω/K), g • β / β = Units.map (algebraMap K Ω).toMonoidHom (χ g) := by
  obtain ⟨F, ψ, hfactor⟩ := galois_open_kernel_finite_factor χ hopen
  have hψ : ∀ g : Gal(F/K), ψ g ^ n = 1 := by
    intro g
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω g
    rw [hfactor, hχ]
  obtain ⟨a, β, hpower, hratio⟩ := finiteGaloisCharacter_exists_radical ψ n hψ
  let i := F.toIntermediateField.val
  let βΩ := Units.map i.toMonoidHom β
  refine ⟨a, βΩ, ?_, ?_⟩
  · apply Units.ext
    change i β.val ^ n = algebraMap K Ω a.val
    have hval : β.val ^ n = algebraMap K F a.val := congrArg Units.val hpower
    rw [← map_pow, hval, i.commutes]
  · intro g
    apply Units.ext
    simp only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
      MonoidHom.coe_coe, βΩ]
    change g (i β.val) / i β.val = algebraMap K Ω (χ g).val
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

/-- Original continuous characters into discrete base-field units have an actual Hilbert-90 radical realization in the original infinite Galois extension. -/
theorem continuous_galois_character_exists_radical
    [TopologicalSpace Kˣ] [DiscreteTopology Kˣ]
    (χ : Gal(Ω/K) →ₜ* Kˣ) (n : ℕ) (hχ : ∀ g : Gal(Ω/K), χ g ^ n = 1) :
    ∃ (a : Kˣ) (β : Ωˣ),
      β ^ n = Units.map (algebraMap K Ω).toMonoidHom a ∧
      ∀ g : Gal(Ω/K), g • β / β = Units.map (algebraMap K Ω).toMonoidHom (χ g) := by
  apply open_kernel_galois_character_exists_radical χ.toMonoidHom _ n hχ
  exact (isOpen_discrete ({1} : Set Kˣ)).preimage χ.continuous

end
end Dubon2026
