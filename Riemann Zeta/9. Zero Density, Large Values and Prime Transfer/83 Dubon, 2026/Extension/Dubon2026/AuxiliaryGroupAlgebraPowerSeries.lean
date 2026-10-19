import Dubon2026.FinitePrimaryGroupAlgebraPowerSeries
import Dubon2026.RationalPrimeTameCoefficientQuotient

/-! The actual product of selected tame coefficient groups is a finite
primary group. Consequently its literal group algebra has the local
continuous parameter action with the same selected generators and fixed
index used by the arithmetic ring comparison. -/

namespace Dubon2026
noncomputable section
open IsLocalRing
open scoped BigOperators MvPowerSeries.WithPiTopology

/-- The exact auxiliary product has coefficient-prime-power order. -/
theorem rationalPrimeAuxiliaryProduct_isPGroup
    {ι : Type*} [Finite ι] (Q : Finset Nat.Primes) (q : ℕ) [Fact q.Prime] :
    IsPGroup q (∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q) := by
  letI (p : Q) : Fact p.val.val.Prime := ⟨p.val.property⟩
  apply IsPGroup.of_card (n := ∑ p : Q, (p.val.val - 1).factorization q * Nat.card ι)
  simp only [Nat.card_pi, Nat.card_fun, rationalPrimeTameCoefficientQuotient_card,
    ← pow_mul, Finset.prod_pow_eq_pow_sum]

/-- Construct the power-series action on the same actual auxiliary
group algebra, with its original generator directions and finite-module
topology. No group-algebra locality or completeness hypothesis is supplied. -/
theorem auxiliaryGroupAlgebra_exists_powerSeriesMap
    (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    {η ι : Type} [Fintype η] [Fintype ι] [DecidableEq ι]
    (Q : Finset Nat.Primes) (q : ℕ) [Fact q.Prime] [CharP (ResidueField O) q]
    (e : η ≃ Q × ι)
    (g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q) :
    let D := ∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q
    letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
    letI := finitePrimaryGroupAlgebra_isLocal O D q (Fact.out : q.Prime)
      (rationalPrimeAuxiliaryProduct_isPGroup (ι := ι) Q q)
    ∃ f : MvPowerSeries η O →ₐ[O] MonoidAlgebra O D,
      (∀ j, f (MvPowerSeries.X j) = MonoidAlgebra.of O D
        (Pi.mulSingle (e j).1 (Pi.mulSingle (e j).2 (g (e j).1))) - 1) ∧
      IsLocalHom f.toRingHom ∧ Continuous f := by
  classical
  exact finitePrimaryGroupAlgebra_exists_powerSeriesMap O
    (∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q) q (Fact.out : q.Prime)
    (rationalPrimeAuxiliaryProduct_isPGroup (ι := ι) Q q)
    (fun j => Pi.mulSingle (e j).1 (Pi.mulSingle (e j).2 (g (e j).1)))

end
end Dubon2026
