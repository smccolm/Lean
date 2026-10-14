import Dubon2026.RationalPrimeWittCoefficient
import Dubon2026.PrimeWittCoefficientEquation

/-! # Higher coefficient equations for the original rational prime units

The actual original integer-unit map is inserted into the proved Witt
coefficient solver. All coefficient solutions needed for the semilinear
changed-uniformizer construction are therefore produced from the original
unit. The subsequent power-series equation, auxiliary finite field, norm
and Frobenius comparison still serve DUB-17's ramified cyclotomic formula.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance] rationalPrimeWittPrime

/-- Higher semilinear coefficient equations have unique solutions for the actual image of every original rational local integer unit. -/
theorem rationalPrimeIntegerWittMap_existsUnique_higher_coefficient
    (p : ℕ) (hp : p.Prime) (u : 𝒪[rationalPrimeLocalField p hp]ˣ)
    (m : ℕ) (hm : 2 ≤ m)
    (b : WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
      (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))))) :
    ∃! a : WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
        (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)))),
      a = b + rationalPrimeIntegerWittMap p hp u.inv *
        (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp) :
          WittVector (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))
            (AlgebraicClosure (ZMod (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp))))) ^
          (m - 1) * WittVector.frobenius a := by
  exact primeWitt_existsUnique_higher_coefficient _
    (Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u) m hm b

end
end Dubon2026
