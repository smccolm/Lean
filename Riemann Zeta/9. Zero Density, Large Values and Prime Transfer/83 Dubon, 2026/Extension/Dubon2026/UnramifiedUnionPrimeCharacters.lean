import Dubon2026.UnramifiedUnionFiniteRamification
import Dubon2026.FiniteExceptionalIntegerPrimes

/-! # Prime-order characters of the actual constructed arithmetic Galois union -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- If the original number field contains the required primitive prime root, the actual constructed arithmetic union has only finitely many original continuous prime-order characters. Its finite-subextension ramification condition is derived. -/
theorem originalUnramifiedUnion_prime_characters_finite
    (a : 𝓞 K) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Finite (Gal((originalUnramifiedGaloisUnion (Ω := Ω) a)/K) →ₜ*
      Multiplicative (ZMod p)) := by
  letI : TopologicalSpace Kˣ := ⊥
  letI : DiscreteTopology Kˣ := ⟨rfl⟩
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    originalUnramifiedGaloisUnion_isGalois a
  exact unramified_continuous_prime_characters_finite
    {v : HeightOneSpectrum (𝓞 K) | a ∈ v.asIdeal}
    (heightOnePrimes_containing_nonzero_finite a ha)
    (fun F v hv => originalUnramifiedUnion_finiteGalois_unramified a ha F v hv)
    p hp hζ

end
end Dubon2026
