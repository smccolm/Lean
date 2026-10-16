import Dubon2026.ArithmeticOriginalPrimeInvariant

/-! # Finite sums over genuine original-prime fibers

Reuse the native finite-filter and fiberwise sum lemmas for the actual
prime contraction. This is the finite reindexing needed to turn the
rational corestriction sum into DUB-17's original number-field prime sum.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitUpperGalois
  arithmeticOrbitGlobalCosetsFinite arithmeticOrbitGlobalCosetsFintype
  arithmeticOrbitIndexFinite arithmeticOrbitIndexFintype

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]

/-- Enumerate the actual primes above p using the proved exact Mackey-orbit equivalence. -/
local instance arithmeticOriginalPrimeFiberFintype (p : Nat.Primes) :
    Fintype {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
      originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property} :=
  Fintype.ofEquiv (cosetOrbitIndex (rationalPrimeArithmeticRestriction a p.val p.property).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F)) (rationalArithmeticOrbitPrimeEquiv a p.val p.property F)

/-- The actual integral-prime fiber is exactly the fiber of the canonical rational-prime index. -/
theorem rationalArithmeticOriginalPrimeBase_eq_iff
    (p : Nat.Primes) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    rationalArithmeticOriginalPrimeBase a F w = p ↔
      originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property := by
  constructor
  · intro h
    subst p
    exact rationalArithmeticOriginalPrimeBase_below a F w
  · exact rationalArithmeticOriginalPrimeBase_eq a F p w

/-- A finite support permits replacing the whole genuine prime fiber by its filtered support. -/
theorem rationalArithmeticOriginalPrimeFiber_sum_support
    (f : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AddCircle (1 : ℚ))
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hT : ∀ w ∉ T, f w = 0)
    (p : Nat.Primes) :
    (∑ w : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
        originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property}, f w.val) =
      ∑ w ∈ T with rationalArithmeticOriginalPrimeBase a F w = p, f w := by
  classical
  have hs : (∑ w ∈ T.subtype (fun w => originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property),
      f w.val) = ∑ w : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
        originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property}, f w.val := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w _ hw
    exact hT w.val (by simpa only [Finset.mem_subtype] using hw)
  rw [← hs, Finset.sum_subtype_eq_sum_filter]
  congr 1
  ext w
  simp only [Finset.mem_filter, rationalArithmeticOriginalPrimeBase_eq_iff]

/-- Summing all genuine prime fibers above the rational support gives the original finite prime sum once each. -/
theorem rationalArithmeticOriginalPrimeFiber_sum
    (f : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AddCircle (1 : ℚ))
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hT : ∀ w ∉ T, f w = 0) :
    (∑ p ∈ T.image (rationalArithmeticOriginalPrimeBase a F),
      ∑ w : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
        originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property}, f w.val) =
      ∑ w ∈ T, f w := by
  classical
  calc
    _ = ∑ p ∈ T.image (rationalArithmeticOriginalPrimeBase a F),
        ∑ w ∈ T with rationalArithmeticOriginalPrimeBase a F w = p, f w :=
      Finset.sum_congr rfl (fun p _ => rationalArithmeticOriginalPrimeFiber_sum_support a F f T hT p)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem _ hw) f

end
end Dubon2026
