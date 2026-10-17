import Dubon2026.ArithmeticCyclotomicContainingSignedProduct
import Dubon2026.RationalNormalizedResidualAwayOrder

/-! # The containing-field factors retain the original rational input

The same normalized residual has the original sign and every away-prime
order. The proved character formulas therefore identify its actual factors
with those of the original rational unit. DUB-17 needs this step before
the containing-field principal product can compare the original local
reciprocity values at every place.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain HeightOneSpectrum
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (p : ℕ) (hp : p.Prime) (m : ℕ)
    [IsCyclotomicExtension {p ^ (m + 1)} ℚ F]

/-- Removing the normalized conductor-prime power does not change an
actual containing-field away-prime reciprocity factor. -/
theorem arithmeticCyclotomicContainingAwayAut_normalizedResidual
    (v : HeightOneSpectrum ℤ)
    (haway : ¬Rat.HeightOneSpectrum.natGenerator v ∣ p ^ (m + 1)) (q : ℚˣ) :
    letI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    arithmeticCyclotomicContainingAwayAut a F (Rat.HeightOneSpectrum.natGenerator v)
      (Rat.HeightOneSpectrum.prime_natGenerator v) (p ^ (m + 1)) haway
      (rationalPrimeNormalizedResidual p hp q) =
    arithmeticCyclotomicContainingAwayAut a F (Rat.HeightOneSpectrum.natGenerator v)
      (Rat.HeightOneSpectrum.prime_natGenerator v) (p ^ (m + 1)) haway q := by
  letI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hvp : Rat.HeightOneSpectrum.natGenerator v ≠ p := by
    intro heq
    apply haway
    rw [heq]
    exact dvd_pow_self p (Nat.succ_ne_zero m)
  let hζ := IsCyclotomicExtension.zeta_spec (p ^ (m + 1)) ℚ F
  apply IsPrimitiveRoot.autToPow_injective ℚ hζ
  rw [arithmeticCyclotomicContainingAwayAut_autToPow a F
      (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v)
      (p ^ (m + 1)) haway _ hζ,
    arithmeticCyclotomicContainingAwayAut_autToPow a F
      (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v)
      (p ^ (m + 1)) haway _ hζ,
    rationalPrimeNormalizedResidual_away_order p hp v hvp q]

/-- The sign-selected original conjugation is unchanged by division by
the positive normalized conductor-prime power. -/
theorem rationalCyclotomicRealSignAut_normalizedResidual (q : ℚˣ) :
    letI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rationalCyclotomicRealSignAut (p ^ (m + 1)) F (rationalPrimeNormalizedResidual p hp q) =
      rationalCyclotomicRealSignAut (p ^ (m + 1)) F q := by
  letI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  simp only [rationalCyclotomicRealSignAut, rationalPrimeNormalizedResidual_positive_iff]

/-- The full signed product of actual away-prime factors has the same
value for the normalized residual and the original rational unit. -/
theorem arithmeticCyclotomicContainingSignedAwayProduct_normalizedResidual
    (S : Finset (HeightOneSpectrum ℤ))
    (hS : ∀ w ∈ S, ¬Rat.HeightOneSpectrum.natGenerator w ∣ p ^ (m + 1)) (q : ℚˣ) :
    letI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    arithmeticCyclotomicContainingSignedAwayProduct a F (p ^ (m + 1)) S hS
      (rationalPrimeNormalizedResidual p hp q) =
      arithmeticCyclotomicContainingSignedAwayProduct a F (p ^ (m + 1)) S hS q := by
  letI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : CommGroup Gal(F/ℚ) := rationalCyclotomicGalCommGroup (p ^ (m + 1)) F
  rw [arithmeticCyclotomicContainingSignedAwayProduct,
    arithmeticCyclotomicContainingSignedAwayProduct,
    rationalCyclotomicRealSignAut_normalizedResidual a F p hp m q]
  congr 1
  apply Finset.prod_congr rfl
  intro w _hw
  exact arithmeticCyclotomicContainingAwayAut_normalizedResidual a F p hp m w.1 (hS w.1 w.2) q

end
end Dubon2026
