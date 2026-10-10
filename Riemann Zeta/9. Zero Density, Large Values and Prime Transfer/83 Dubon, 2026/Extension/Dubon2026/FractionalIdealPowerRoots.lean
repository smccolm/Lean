import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # Genuine fractional-ideal power roots from original prime multiplicities -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Original prime multiplicities separate nonzero fractional ideals. -/
theorem fractionalIdeal_eq_of_counts {I J : FractionalIdeal R⁰ K}
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I =
      FractionalIdeal.count K v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  apply finprod_congr
  intro v
  rw [h v]

/-- Positive powers are injective on the original nonzero fractional ideals. -/
theorem fractionalIdeal_eq_of_pow_eq {I J : FractionalIdeal R⁰ K}
    (hI : I ≠ 0) (hJ : J ≠ 0) (n : ℕ) (hn : n ≠ 0) (h : I ^ n = J ^ n) :
    I = J := by
  apply fractionalIdeal_eq_of_counts hI hJ
  intro v
  have hc := congrArg (FractionalIdeal.count K v) h
  rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at hc
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) hc

/-- The literal product obtained by dividing every original prime multiplicity by n. -/
def fractionalIdealCountRoot (n : ℕ) (I : FractionalIdeal R⁰ K) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
    (FractionalIdeal.count K v I / (n : ℤ))

/-- The original multiplicity-root product is a nonzero fractional ideal. -/
theorem fractionalIdealCountRoot_ne_zero (n : ℕ) (I : FractionalIdeal R⁰ K) :
    fractionalIdealCountRoot n I ≠ 0 := by
  apply finprod_ne_zero
  intro v
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- Every original prime multiplicity of the actual root product is the divided multiplicity. -/
theorem fractionalIdealCountRoot_count (n : ℕ) (I : FractionalIdeal R⁰ K)
    (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (fractionalIdealCountRoot n I) =
      FractionalIdeal.count K v I / (n : ℤ) := by
  apply FractionalIdeal.count_finprod
  filter_upwards [FractionalIdeal.finite_factors I] with w hw
  rw [hw, Int.zero_ediv]

/-- Divisibility of every original prime multiplicity gives an actual nth root of the original fractional ideal. -/
theorem fractionalIdealCountRoot_pow (n : ℕ) (I : FractionalIdeal R⁰ K)
    (hI : I ≠ 0)
    (hdiv : ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ FractionalIdeal.count K v I) :
    fractionalIdealCountRoot n I ^ n = I := by
  apply fractionalIdeal_eq_of_counts (pow_ne_zero n (fractionalIdealCountRoot_ne_zero n I)) hI
  intro v
  rw [FractionalIdeal.count_pow, fractionalIdealCountRoot_count]
  simpa only [mul_comm] using Int.ediv_mul_cancel (hdiv v)

/-- The actual power-root product, bundled as an invertible original fractional ideal. -/
def fractionalIdealCountRootUnit (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ) :
    (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (fractionalIdealCountRoot n I.val) (fractionalIdealCountRoot_ne_zero n I.val)

/-- The bundled original fractional-ideal root retains the exact nth-power identity. -/
theorem fractionalIdealCountRootUnit_pow (n : ℕ) (I : (FractionalIdeal R⁰ K)ˣ)
    (hdiv : ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ FractionalIdeal.count K v I.val) :
    fractionalIdealCountRootUnit n I ^ n = I := by
  apply Units.ext
  exact fractionalIdealCountRoot_pow n I.val I.ne_zero hdiv

end
end Dubon2026
