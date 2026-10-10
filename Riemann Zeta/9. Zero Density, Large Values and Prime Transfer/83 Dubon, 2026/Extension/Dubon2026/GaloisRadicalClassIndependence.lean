import Dubon2026.ContinuousGaloisKummerClasses

/-! # Original Galois character ratios determine the actual radical power class -/

namespace Dubon2026

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Any two original radicals with the same original Galois ratios have equal actual base-field classes modulo nth powers. -/
theorem galois_radical_power_class_eq_of_ratios (n : ℕ) (a b : Kˣ) (β γ : Ωˣ)
    (hβ : β ^ n = Units.map (algebraMap K Ω).toMonoidHom a)
    (hγ : γ ^ n = Units.map (algebraMap K Ω).toMonoidHom b)
    (hratios : ∀ g : Gal(Ω/K), g • β / β = g • γ / γ) :
    QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a =
      QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range b := by
  have hfixed : ∀ g : Gal(Ω/K), g ((β / γ : Ωˣ).val) = (β / γ : Ωˣ).val := by
    intro g
    have h := div_eq_div_iff_div_eq_div.mp (hratios g)
    have hunit : g • (β / γ) = β / γ := by
      simpa only [smul_div'] using h
    exact congrArg Units.val hunit
  obtain ⟨u, hu⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
    (β / γ : Ωˣ).val).mpr hfixed
  have hu0 : u ≠ 0 := by
    intro hzero
    exact (β / γ).ne_zero (by simpa only [hzero, map_zero] using hu.symm)
  let u₀ := Units.mk0 u hu0
  have humap : Units.map (algebraMap K Ω).toMonoidHom u₀ = β / γ := Units.ext hu
  have hp := congrArg (fun x : Ωˣ => x ^ n) humap
  dsimp only at hp
  rw [← map_pow, div_pow, hβ, hγ, ← map_div] at hp
  have hbase : u₀ ^ n = a / b :=
    Units.map_injective (algebraMap K Ω).injective hp
  apply QuotientGroup.eq_iff_div_mem.mpr
  exact ⟨u₀, hbase⟩

/-- Every actual radical realization of an original continuous character gives its same original Kummer class. -/
theorem continuousGaloisKummerClass_eq_of_radical
    [TopologicalSpace Kˣ] [DiscreteTopology Kˣ] (n : ℕ)
    (χ : ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) n)
    (a : Kˣ) (β : Ωˣ)
    (hβ : β ^ n = Units.map (algebraMap K Ω).toMonoidHom a)
    (hχ : ∀ g : Gal(Ω/K), g • β / β =
      Units.map (algebraMap K Ω).toMonoidHom (χ.val g)) :
    continuousGaloisKummerClass n χ =
      QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a := by
  obtain ⟨γ, hγ, hψ⟩ := continuousGaloisKummerRepresentative_exists_radical n χ
  apply galois_radical_power_class_eq_of_ratios n
    (continuousGaloisKummerRepresentative n χ) a γ β hγ hβ
  intro g
  rw [hψ, hχ]

end
end Dubon2026
