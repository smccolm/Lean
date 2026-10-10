import Dubon2026.FiniteGaloisCharacterRadicals
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Original Galois character ratios are determined by actual Kummer classes -/

namespace Dubon2026

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- When the original base field contains a primitive nth root, every actual extension-field nth root of unity is fixed by the original Galois group. -/
theorem galois_rootOfUnity_fixed (n : ℕ) [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) (δ : Lˣ) (hδ : δ ^ n = 1)
    (g : Gal(L/K)) : g • δ = δ := by
  let e : rootsOfUnity n K ≃* rootsOfUnity n L :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective hζ
  let ε : rootsOfUnity n L := ⟨δ, hδ⟩
  have hmap : Units.map (algebraMap K L).toMonoidHom (e.symm ε).val = δ := by
    apply Units.ext
    exact rootsOfUnityEquivOfPrimitiveRoots_symm_apply
      (algebraMap K L).injective hζ ε
  rw [← hmap]
  exact galois_base_unit_fixed g (e.symm ε).val

/-- Original radicals whose actual base-field power classes agree have exactly the same original Galois ratios. -/
theorem galois_radical_ratios_eq_of_power_class (n : ℕ) [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) (a b : Kˣ) (β γ : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (hγ : γ ^ n = Units.map (algebraMap K L).toMonoidHom b)
    (hab : QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a =
      QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range b)
    (g : Gal(L/K)) : g • β / β = g • γ / γ := by
  have hmem : a / b ∈ (powMonoidHom n : Kˣ →* Kˣ).range :=
    QuotientGroup.eq_iff_div_mem.mp hab
  obtain ⟨u, hu⟩ := hmem
  change u ^ n = a / b at hu
  let v := Units.map (algebraMap K L).toMonoidHom u
  let δ := β / γ / v
  have hδ : δ ^ n = 1 := by
    dsimp [δ, v]
    rw [div_pow, div_pow, hβ, hγ, ← map_pow, hu, map_div]
    exact div_self' _
  have hfixed := galois_rootOfUnity_fixed n hζ δ hδ g
  have hratio : (g • β / g • γ) / v = (β / γ) / v := by
    simpa only [δ, v, smul_div', galois_base_unit_fixed] using hfixed
  have hratio' : g • β / g • γ = β / γ := div_left_inj.mp hratio
  exact div_eq_div_iff_div_eq_div.mp hratio'

/-- The actual nth-power class of an original radical determines its original base-unit-valued Galois character. -/
theorem galois_characters_eq_of_radical_power_class (n : ℕ) [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) (χ ψ : Gal(L/K) →* Kˣ)
    (a b : Kˣ) (β γ : Lˣ)
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (hγ : γ ^ n = Units.map (algebraMap K L).toMonoidHom b)
    (hχ : ∀ g : Gal(L/K), g • β / β = Units.map (algebraMap K L).toMonoidHom (χ g))
    (hψ : ∀ g : Gal(L/K), g • γ / γ = Units.map (algebraMap K L).toMonoidHom (ψ g))
    (hab : QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a =
      QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range b) : χ = ψ := by
  apply MonoidHom.ext
  intro g
  apply Units.map_injective (algebraMap K L).injective
  rw [← hχ g, ← hψ g]
  exact galois_radical_ratios_eq_of_power_class n hζ a b β γ hβ hγ hab g

end
end Dubon2026
