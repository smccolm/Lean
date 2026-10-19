import Dubon2026.RationalPrimeParameterQuotient
import Dubon2026.AuxiliaryFamilyGroupAlgebra
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-! The actual finite auxiliary group algebra maps to each sufficiently
shallow quotient of the common parameter algebra. The map retains the
original selected cyclic generators and fixed direction index. This
supplies the finite factorization in the DUB-17 annihilator-convergence
chain; genuine Hecke-module freeness is a separate obligation. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- The coefficient residue characteristic belongs to the maximal
ideal of the same common parameter algebra. -/
theorem parameterRing_prime_mem_maximalIdeal
    {O η : Type*} [CommRing O] [IsLocalRing O]
    (q : ℕ) [CharP (ResidueField O) q] :
    (q : MvPowerSeries η O) ∈ maximalIdeal (MvPowerSeries η O) := by
  have hq : (q : O) ∈ maximalIdeal O := by
    apply (residue_eq_zero_iff _).mp
    rw [map_natCast, CharP.cast_eq_zero]
  intro hu
  apply hq
  simpa only [map_natCast] using MvPowerSeries.isUnit_iff_constantCoeff.mp hu

/-- Every actual parameter direction is residue zero. -/
theorem parameterRing_X_mem_maximalIdeal
    {O η : Type*} [CommRing O] [IsLocalRing O] (i : η) :
    (MvPowerSeries.X i : MvPowerSeries η O) ∈ maximalIdeal (MvPowerSeries η O) := by
  intro hu
  have hc := MvPowerSeries.isUnit_iff_constantCoeff.mp hu
  simp only [MvPowerSeries.constantCoeff_X, isUnit_zero_iff, zero_ne_one] at hc

/-- Construct the original coordinate characters in a maximal-adic
parameter quotient from the selected congruences alone. -/
def auxiliaryFiniteParameterCharacters
    {O η ι : Type*} [CommRing O] [IsLocalRing O]
    (Q : Finset Nat.Primes) (q level n : ℕ) [Fact q.Prime]
    [CharP (ResidueField O) q]
    (e : η ≃ Q × ι) (hlevel : n ≤ level)
    (hmod : ∀ p : Q, p.val.val ≡ 1 [MOD q ^ level])
    (g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q)
    (hg : ∀ p d, ∃ j : ℕ, g p ^ j = d) :
    ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q →*
      (ι → (MvPowerSeries η O ⧸ maximalIdeal (MvPowerSeries η O) ^ n))ˣ := by
  intro p
  letI : Fact p.val.val.Prime := ⟨p.val.property⟩
  exact MulEquiv.piUnits.symm.toMonoidHom.comp (Pi.monoidHom fun i =>
    rationalPrimeParameterQuotientCharacter (maximalIdeal (MvPowerSeries η O))
      p.val.val q level n (parameterRing_prime_mem_maximalIdeal q) hlevel (hmod p)
      (g p) (hg p) (1 + MvPowerSeries.X (e.symm (p, i)))
      (by simpa only [add_sub_cancel_left] using
        parameterRing_X_mem_maximalIdeal (O := O) (e.symm (p, i))))

/-- The original coordinate generator evaluates to one plus its
fixed variable in the literal parameter quotient. -/
theorem auxiliaryFiniteParameterCharacters_generator
    {O η ι : Type*} [CommRing O] [IsLocalRing O]
    (Q : Finset Nat.Primes) (q level n : ℕ) [Fact q.Prime]
    [CharP (ResidueField O) q]
    (e : η ≃ Q × ι) (hlevel : n ≤ level)
    (hmod : ∀ p : Q, p.val.val ≡ 1 [MOD q ^ level])
    (g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q)
    (hg : ∀ p d, ∃ j : ℕ, g p ^ j = d) (p : Q) (i : ι) :
    ((auxiliaryFiniteParameterCharacters (O := O) Q q level n e hlevel hmod g hg p
      (g p)).val i) = Ideal.Quotient.mk (maximalIdeal (MvPowerSeries η O) ^ n)
        (1 + MvPowerSeries.X (e.symm (p, i))) := by
  letI : Fact p.val.val.Prime := ⟨p.val.property⟩
  unfold auxiliaryFiniteParameterCharacters
  exact rationalPrimeParameterQuotientCharacter_generator
    (maximalIdeal (MvPowerSeries η O)) p.val.val q level n
    (parameterRing_prime_mem_maximalIdeal q) hlevel (hmod p) (g p) (hg p)
    (1 + MvPowerSeries.X (e.symm (p, i)))
    (by simpa only [add_sub_cancel_left] using
      parameterRing_X_mem_maximalIdeal (O := O) (e.symm (p, i)))

/-- The actual auxiliary group algebra has the constructed map to
each parameter quotient below its congruence level. -/
def auxiliaryFiniteParameterGroupAlgebra
    (O : Type*) [CommRing O] [IsLocalRing O] {η ι : Type*} [Fintype ι]
    (Q : Finset Nat.Primes) (q level n : ℕ) [Fact q.Prime]
    [CharP (ResidueField O) q]
    (e : η ≃ Q × ι) (hlevel : n ≤ level)
    (hmod : ∀ p : Q, p.val.val ≡ 1 [MOD q ^ level])
    (g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q)
    (hg : ∀ p d, ∃ j : ℕ, g p ^ j = d) :
    MonoidAlgebra O (∀ p : Q, ι → RationalPrimeTameCoefficientQuotient p.val.val q) →ₐ[O]
      (MvPowerSeries η O ⧸ maximalIdeal (MvPowerSeries η O) ^ n) :=
  auxiliaryFamilyGroupAlgebra O (auxiliaryFiniteParameterCharacters Q q level n e hlevel hmod g hg)

/-- Group-basis evaluation retains precisely the original selected
generator and its fixed common parameter direction. -/
theorem auxiliaryFiniteParameterGroupAlgebra_generator
    (O : Type*) [CommRing O] [IsLocalRing O] {η ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Finset Nat.Primes) (q level n : ℕ) [Fact q.Prime]
    [CharP (ResidueField O) q]
    (e : η ≃ Q × ι) (hlevel : n ≤ level)
    (hmod : ∀ p : Q, p.val.val ≡ 1 [MOD q ^ level])
    (g : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q)
    (hg : ∀ p d, ∃ j : ℕ, g p ^ j = d) (p : Q) (i : ι) :
    auxiliaryFiniteParameterGroupAlgebra O Q q level n e hlevel hmod g hg
      (MonoidAlgebra.of O _ (Pi.mulSingle p (Pi.mulSingle i (g p)))) =
        Ideal.Quotient.mk (maximalIdeal (MvPowerSeries η O) ^ n)
          (1 + MvPowerSeries.X (e.symm (p, i))) := by
  classical
  rw [auxiliaryFiniteParameterGroupAlgebra, auxiliaryFamilyGroupAlgebra_of_single]
  exact auxiliaryFiniteParameterCharacters_generator ..

end
end Dubon2026
