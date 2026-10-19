import Dubon2026.LocalQuotientCardinalityBound
import Dubon2026.AuxiliaryFixedPowerSeriesComparison

/-! Uniform finite-quotient bounds from the actual augmentation map.
The original base ring's generators and the common parameter index are
fixed, so the bound is independent of the auxiliary arithmetic level. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped BigOperators

/-- Choose generators of the original base maximal ideal once. -/
def localMaximalGenerators (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    Finset A :=
  Classical.choose (IsNoetherian.noetherian (maximalIdeal A))

/-- The chosen fixed base-ring generators span its actual maximal ideal. -/
theorem localMaximalGenerators_span (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    Ideal.span (localMaximalGenerators A : Set A) = maximalIdeal A :=
  Classical.choose_spec (IsNoetherian.noetherian (maximalIdeal A))

/-- The actual auxiliary ring's finite maximal-adic quotients have a
bound depending only on the original base ring and fixed parameter index. -/
theorem auxiliaryFixedPowerSeries_cardinality_pow_le
    (O : Type*) {R A ι n G η : Type*}
    [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    [CommRing R] [IsLocalRing R] [Algebra O R]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A]
    [Fintype ι] [Fintype n] [DecidableEq n] [Fintype η]
    (Q : Finset Nat.Primes) (q : ℕ)
    (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A)
    (d : AuxiliaryFixedPowerSeriesComparison O (ι := ι) Q q τ τ₀ η)
    (eR : ResidueField R ≃ₐ[O] ResidueField O) (k : ℕ) :
    Nat.card (R ⧸ maximalIdeal R ^ k) ≤
      Nat.card (ResidueField O) ^
        (∑ i ∈ Finset.range k, (Fintype.card η + (localMaximalGenerators A).card) ^ i) := by
  classical
  let e := auxiliaryFixedPowerSeriesParameterMap O Q q τ τ₀ d
  let J := Ideal.map e.toRingHom
    (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η))))
  let c := auxiliaryFixedPowerSeriesQuotientEquiv O Q q τ τ₀ d
  let f : R →+* A := c.toAlgHom.toRingHom.comp (Ideal.Quotient.mk J)
  have hf : Function.Surjective f := c.surjective.comp Ideal.Quotient.mk_surjective
  let v : η → R := fun i => e (MvPowerSeries.X i)
  have hker : RingHom.ker f = Ideal.span (Set.range v) := by
    have hJ : RingHom.ker f = J := by
      ext x
      change c (Ideal.Quotient.mk J x) = 0 ↔ x ∈ J
      rw [← map_zero c, c.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]
    rw [hJ]
    change Ideal.map e.toRingHom (Ideal.span (Set.range MvPowerSeries.X)) = _
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  letI : Finite (ResidueField R) := Finite.of_equiv (ResidueField O) eR.symm.toEquiv
  have h := localQuotient_cardinality_pow_le f hf v hker
    (localMaximalGenerators A) (localMaximalGenerators_span A) k
  rw [Nat.card_congr eR.toEquiv] at h
  exact h

end
end Dubon2026
