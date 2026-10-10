import Dubon2026.ContinuousGaloisCharacterRadicals
import Dubon2026.GaloisCharacterKummerInjectivity

/-! # An actual injective Kummer-class map for original continuous Galois characters -/

namespace Dubon2026

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace Kˣ] [DiscreteTopology Kˣ]

/-- The actual continuous original Galois characters killed by the original exponent. -/
def ContinuousGaloisExponentCharacters (n : ℕ) :=
  {χ : Gal(Ω/K) →ₜ* Kˣ // ∀ g : Gal(Ω/K), χ g ^ n = 1}

/-- The original base-field unit supplied by the actual Hilbert-90 radical construction. -/
def continuousGaloisKummerRepresentative (n : ℕ)
    (χ : ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) n) : Kˣ :=
  (continuous_galois_character_exists_radical χ.val n χ.property).choose

/-- The actual class modulo nth powers of the original base-field radical coefficient. -/
def continuousGaloisKummerClass (n : ℕ)
    (χ : ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) n) :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range :=
  QuotientGroup.mk' _ (continuousGaloisKummerRepresentative n χ)

/-- The chosen original representative has a genuine radical in the original Galois extension with the exact original ratios. -/
theorem continuousGaloisKummerRepresentative_exists_radical (n : ℕ)
    (χ : ContinuousGaloisExponentCharacters (K := K) (Ω := Ω) n) :
    ∃ β : Ωˣ,
      β ^ n = Units.map (algebraMap K Ω).toMonoidHom
        (continuousGaloisKummerRepresentative n χ) ∧
      ∀ g : Gal(Ω/K), g • β / β =
        Units.map (algebraMap K Ω).toMonoidHom (χ.val g) :=
  (continuous_galois_character_exists_radical χ.val n χ.property).choose_spec

/-- Equality of the actual chosen original power classes implies equality of the original continuous characters. -/
theorem continuousGaloisKummerClass_injective (n : ℕ) [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) :
    Function.Injective (continuousGaloisKummerClass (K := K) (Ω := Ω) n) := by
  intro χ ψ hclass
  obtain ⟨β, hβ, hχ⟩ := continuousGaloisKummerRepresentative_exists_radical n χ
  obtain ⟨γ, hγ, hψ⟩ := continuousGaloisKummerRepresentative_exists_radical n ψ
  have heq := galois_characters_eq_of_radical_power_class n hζ
    χ.val.toMonoidHom ψ.val.toMonoidHom
    (continuousGaloisKummerRepresentative n χ) (continuousGaloisKummerRepresentative n ψ)
    β γ hβ hγ hχ hψ hclass
  apply Subtype.ext
  apply DFunLike.ext
  intro g
  exact DFunLike.congr_fun heq g

end
end Dubon2026
