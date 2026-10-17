import Dubon2026.OriginalGeneratedKummerUnramified

/-! # Original inertia fixes every valuation-unit radical

Reuse the unit-ratio argument of the original generating-root theorem
without its generation premise. The full S-unit Kummer field has many
roots, so this individual fixedness statement is the required input to
its outside-support unramifiedness in DUB-17's norm-field construction.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L]
  [Algebra K L]

/-- Each actual inertia automorphism fixes a valuation-unit radical
whose exponent is a valuation unit. -/
theorem originalInertia_fixes_unit_radical
    (w : HeightOneSpectrum (𝓞 L)) (n : ℕ) (hn : w.valuation L (n : L) = 1)
    (a : Kˣ) (β : Lˣ) (hβ : (β : L) ^ n = algebraMap K L (a : K))
    (hUnit : w.valuation L (β : L) = 1)
    (σ : Gal(L/K)) (hσ : σ ∈ w.asIdeal.inertia Gal(L/K)) : σ (β : L) = β := by
  have hVal : w.valuation L (σ (β : L)) = w.valuation L (β : L) := by
    have h := numberFieldGaloisPlace_valuation K L σ w (β : L)
    rw [originalInertia_fixes_prime K L w σ hσ] at h
    exact h
  have hRatioUnit : w.valuation L (σ (β : L) / (β : L)) = 1 := by
    rw [map_div₀, hVal, hUnit, div_one]
  have hClose : w.valuation L (σ (β : L) / (β : L) - 1) < 1 := by
    rw [div_sub_one β.ne_zero, map_div₀, hUnit, div_one]
    exact originalInertia_valuation_sub_lt_one K L w σ hσ (β : L) hUnit.le
  have hPower : (σ (β : L) / (β : L)) ^ n = 1 := by
    rw [div_pow, ← map_pow, hβ, σ.commutes, div_self]
    exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero
  exact (div_eq_one_iff_eq β.ne_zero).mp (valuation_unitExponent_root_eq_one
    (w.valuation L) n hn _ hRatioUnit hClose hPower)

end
end Dubon2026
