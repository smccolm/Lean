import Dubon2026.RationalPrimeOriginalResidueCard
import Dubon2026.LocalFieldUniformizerOrder

/-! # The prime is an original rational local uniformizer

The actual integer-ring equivalence proves irreducibility of p in the
original valuation ring. The existing normalized uniformizer theorem gives
its positive order one. This fixes the valuation normalization needed to
assemble the rational cyclotomic principal product for DUB-17's arithmetic
invariant sum-zero and global-duality dependency.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance 1100] Ring.toIntAlgebra

/-- The rational prime p is irreducible in the original p-adic valuation integer ring. -/
theorem rationalPrimeValuationInteger_irreducible_prime (p : ℕ) (hp : p.Prime) :
    Irreducible (p : 𝒪[rationalPrimeLocalField p hp]) := by
  let v := rationalPrimePlace p hp
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let e₁ : 𝒪[rationalPrimeLocalField p hp] ≃+* rationalPrimeLocalIntegerRing p hp :=
    RingEquiv.subringCongr (rationalPrimeLocalInteger_subring_eq p hp)
  let e₂ := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  let e := e₁.trans e₂
  apply (MulEquiv.irreducible_iff e).mp
  rw [map_natCast]
  have he : (p : ℤ_[Rat.HeightOneSpectrum.primesEquiv v]) =
      (Rat.HeightOneSpectrum.primesEquiv v : ℕ) :=
    congrArg (fun k : ℕ => (k : ℤ_[Rat.HeightOneSpectrum.primesEquiv v]))
      (rationalPrimePlace_natGenerator p hp).symm
  rw [he]
  exact PadicInt.irreducible_p

/-- The original normalized order of the rational local prime is positive one. -/
theorem rationalPrimeLocalField_prime_order (p : ℕ) (hp : p.Prime) :
    localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul (Units.mk0 (p : rationalPrimeLocalField p hp)
        (by
          intro h
          exact (rationalPrimeValuationInteger_irreducible_prime p hp).ne_zero
            (Subtype.ext h)))) = 1 := by
  exact localFieldUnitOrder_irreducible (rationalPrimeLocalField p hp)
    (p : 𝒪[rationalPrimeLocalField p hp])
    (rationalPrimeValuationInteger_irreducible_prime p hp)

end
end Dubon2026
