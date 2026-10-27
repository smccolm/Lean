import Dubon2026.SourceLaurentIntegralDescent
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded rational Fourier denominators. Native
localization of integer power series at X makes integer Laurent series
normal. Working directly with the original Laurent germ avoids choosing
new pole-clearing exponents for every coefficient of a monic relation.
Both the monic and fraction premises remain essential and explicit. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem isIntegrallyClosed_integerLaurentSeries : IsIntegrallyClosed (LaurentSeries ℤ) :=
  isIntegrallyClosed_of_isLocalization (LaurentSeries ℤ)
    (Submonoid.powers (PowerSeries.X : PowerSeries ℤ))
    (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero)

theorem rationalLaurentSeries_mem_integer_image_of_monic_of_fraction
    (g : LaurentSeries ℚ) (P : Polynomial (LaurentSeries ℤ)) (hP : P.Monic)
    (hroot : Polynomial.eval₂ (coeffMap (algebraMap ℤ ℚ)) g P = 0)
    (h : LaurentSeries ℤ) (h0 : h ≠ 0)
    (hmul : coeffMap (algebraMap ℤ ℚ) h * g ∈ (coeffMap (algebraMap ℤ ℚ)).range) :
    g ∈ (coeffMap (algebraMap ℤ ℚ)).range := by
  letI := isIntegrallyClosed_integerLaurentSeries
  let ι : LaurentSeries ℤ →+* LaurentSeries ℚ := coeffMap (algebraMap ℤ ℚ)
  let F := FractionRing (LaurentSeries ℤ)
  have hi : Function.Injective ι := by
    intro a b he
    ext n
    have hc := congrArg (fun x : LaurentSeries ℚ => x.coeff n) he
    simp only [ι, coeffMap_coeff] at hc
    exact (IsFractionRing.injective ℤ ℚ) hc
  let θ : F →+* LaurentSeries ℚ := IsFractionRing.lift (A := LaurentSeries ℤ) (K := F) hi
  have ht (a : LaurentSeries ℤ) : θ (algebraMap (LaurentSeries ℤ) F a) = ι a :=
    IsFractionRing.lift_algebraMap hi a
  have htc : θ.comp (algebraMap (LaurentSeries ℤ) F) = ι := RingHom.ext ht
  obtain ⟨u, hu⟩ := hmul
  let x : F := algebraMap (LaurentSeries ℤ) F u / algebraMap (LaurentSeries ℤ) F h
  have hih : ι h ≠ 0 := fun hz => h0 (hi (hz.trans (map_zero ι).symm))
  have htx : θ x = g := by
    rw [show x = algebraMap (LaurentSeries ℤ) F u / algebraMap (LaurentSeries ℤ) F h from rfl,
      map_div₀, ht, ht, div_eq_iff hih, mul_comm, ← hu]
  have hint : IsIntegral (LaurentSeries ℤ) x := by
    refine ⟨P, hP, ?_⟩
    apply θ.injective
    rw [Polynomial.hom_eval₂, htc, htx, map_zero]
    exact hroot
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨p, by rw [← ht, hp, htx]⟩

end
end Dubon2026.SourceFunctionField
