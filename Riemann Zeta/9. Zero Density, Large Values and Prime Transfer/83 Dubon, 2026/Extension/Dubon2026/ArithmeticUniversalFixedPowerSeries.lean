import Dubon2026.ArithmeticUniversalSupportPowerSeries
import Dubon2026.AuxiliaryFixedPowerSeriesComparison

/-! The actual enlarged-support universal coefficient ring receives
an action of the power-series algebra indexed by Fin g × Fin degree.
The same fixed variable ideal recovers the original universal ring.
Exact-size arithmetic selection supplies the cardinality input below. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- Reuse the actual arithmetic power-series comparison and index its
genuine auxiliary character directions by one fixed finite type. -/
def arithmeticUniversalOriginalSupportFixedPowerSeriesComparison
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (b : 𝓞 ℚ) (hb : b ≠ 0) (hab : a ∣ b)
    (q degree level : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (hlevel : 0 < level) (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (Q : Finset Nat.Primes) (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ))
    (hgood : ∀ p : Q, RationalArithmeticTorusAuxiliaryPrime a q degree level
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val)
    (g : ℕ) (hcard : Q.card = g) :=
  let π := rationalArithmeticSupportRestriction a b hab
  let σb := σ.comp π.toMonoidHom
  let hσb : Continuous σb := hσ.comp π.continuous
  let δb := δ.comp π.toMonoidHom
  let hδb : ∀ g, GeneralLinearGroup.det (σb g) =
      Units.map (algebraMap O (ResidueField O)) (δb g) := fun g => hδ (π g)
  let hqb := dvd_trans hqa hab
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
  letI := (arithmeticFixedDeterminantRing_localData
    b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb).2.1
  let d := arithmeticUniversalOriginalSupportPowerSeriesComparison
    a ha b hb hab q degree level hqa hlevel eO σ hσ δ hδ Q hba hgood
  auxiliaryFixedPowerSeriesComparisonOfCard O
    (R := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σb hσb δb)
    (A := ArithmeticFixedDeterminantRing a ha q (Fact.out : q.Prime) hqa σ hσ δ)
    Q q
    (arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σb hσb δb)
    (fun x => arithmeticFixedDeterminantRepresentation a ha q (Fact.out : q.Prime) hqa σ hσ δ (π x))
    degree g d hcard

end
end Dubon2026
