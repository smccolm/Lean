import Dubon2026.ArithmeticUniversalOriginalSupportAugmentation
import Dubon2026.AuxiliaryPowerSeriesAugmentation

/-! The actual arithmetic universal ring and its constructed auxiliary
characters carry a power-series parameter map with exactly the original
augmentation image, retaining the same base-ring and universal-matrix comparison. This consumes the original-support comparison on
the DUB-17 arithmetic patching dependency chain. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- Construct power-series parameters for the actual original-support
auxiliary universal ring. Completeness and residue-one characters are
derived from the native ring and comparison; no character family or
parameter map is supplied. The output retains the same character family in its ring comparison and parameter data. -/
def arithmeticUniversalOriginalSupportPowerSeriesComparison
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
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val) :=
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
  let c := arithmeticUniversalOriginalSupportAugmentationComparison
    a ha b hb hab q degree level hqa hlevel eO σ hσ δ hδ Q hba hgood
  completeLocalAuxiliaryPowerSeriesAugmentationComparison O
    (R := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σb hσb δb)
    (A := ArithmeticFixedDeterminantRing a ha q (Fact.out : q.Prime) hqa σ hσ δ)
    (ι := Fin degree) Q q
    (arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σb hσb δb)
    (fun g => arithmeticFixedDeterminantRepresentation a ha q (Fact.out : q.Prime) hqa σ hσ δ (π g)) c

end
end Dubon2026
