import Dubon2026.RationalPrimeWittCoefficient
import Dubon2026.PrimeWittIntertwinerFrobenius
import Dubon2026.PrimeWittIntertwinerInverse

/-! # The constructed semilinear series for original rational integer units

For each actual natural number prime to the original rational prime, the
original valuation-integer unit and the full semilinear power series are
constructed. Its functional equation, actual Frobenius action and both
inverse identities are proved; none is an input. This is the precise
formal-series input to the auxiliary finite extension for DUB-17 ramified
cyclotomic reciprocity. Evaluation, primitive torsion and the normed
uniformizer remain to be constructed before the local formula follows.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
attribute [local instance] rationalPrimeWittPrime

/-- Every actual natural unit away from p supplies the original integer unit, the genuine semilinear series, its Frobenius identity and its two-sided formal inverse. -/
theorem rationalPrimeNaturalWittIntertwiner_exists
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    let W := WittVector q (AlgebraicClosure (ZMod q))
    ∃ u : 𝒪[rationalPrimeLocalField p hp]ˣ,
      u.val = a ∧ ∃ H : PowerSeries W,
        PowerSeries.constantCoeff H = 0 ∧ IsUnit (PowerSeries.coeff 1 H) ∧
        PowerSeries.subst H
            (primeWittChangedSeries q (Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u)) =
          PowerSeries.subst (primeWittMultiplicativeSeries q) (PowerSeries.map WittVector.frobenius H) ∧
        PowerSeries.map WittVector.frobenius H = PowerSeries.subst (primeWittNaturalSeries q a) H ∧
        ∃ J : PowerSeries W, PowerSeries.constantCoeff J = 0 ∧
          PowerSeries.subst J H = PowerSeries.X ∧ PowerSeries.subst H J = PowerSeries.X := by
  dsimp only
  have haUnit : IsUnit (a : 𝒪[rationalPrimeLocalField p hp]) := by
    simpa only [Int.cast_natCast] using
      rationalPrimeValuationInteger_isUnit_int p hp (a : ℤ) (by exact_mod_cast ha)
  obtain ⟨u, hu⟩ := haUnit
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let v := Units.map (rationalPrimeIntegerWittMap p hp).toMonoidHom u
  have hv : (v : WittVector q (AlgebraicClosure (ZMod q))) = a := by
    change rationalPrimeIntegerWittMap p hp u.val = a
    rw [hu, map_natCast]
  refine ⟨u, hu, primeWittIntertwiner q v,
    primeWittIntertwiner_constantCoeff q v, primeWittIntertwiner_linear_isUnit q v,
    primeWittIntertwiner_functionalEquation q v,
    primeWittIntertwiner_frobenius_nat q v a hv, primeWittIntertwinerInverse q v,
    primeWittIntertwinerInverse_constantCoeff q v, primeWittIntertwinerInverse_right q v,
    primeWittIntertwinerInverse_left q v⟩

end
end Dubon2026
