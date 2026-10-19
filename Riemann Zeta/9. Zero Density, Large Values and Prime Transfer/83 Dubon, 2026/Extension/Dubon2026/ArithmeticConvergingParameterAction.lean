import Dubon2026.ArithmeticFixedDeterminantConvergingAction
import Dubon2026.ArithmeticUniversalFixedPowerSeries
import Dubon2026.ArithmeticFixedDeterminantCompactness

/-! The actual enlarged-support arithmetic comparison supplies its own
cyclic generators and fixed index to the continuous auxiliary algebra action
and its quantitative kernel convergence.
The selected torus property supplies the congruence and the original
residue identification supplies the coefficient characteristic. This is
the coefficient-ideal convergence dependency of DUB-17's arithmetic patching, not a construction of arithmetic Hecke modules. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- Construct the actual arithmetic comparison together with the local continuous action
on its genuine auxiliary group algebra, retaining its original generators
and proved kernel containment in every maximal-adic power up to its level.
The action factors the original arithmetic parameter map. -/
def arithmeticUniversalOriginalSupportConvergingParameterAction
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
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
    (g : ℕ) (hcard : Q.card = g) :
    let π := rationalArithmeticSupportRestriction a b hab
    let σb := σ.comp π.toMonoidHom
    let hσb : Continuous σb := hσ.comp π.continuous
    let δb := δ.comp π.toMonoidHom
    let hδb : ∀ x, GeneralLinearGroup.det (σb x) =
      Units.map (algebraMap O (ResidueField O)) (δb x) := fun x => hδ (π x)
    let hqb := dvd_trans hqa hab
    letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
    AuxiliaryCompatibleConvergingParameterData O (ι := Fin degree) (η := Fin g × Fin degree)
      Q q level
      (arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σb hσb δb)
      (fun x => arithmeticFixedDeterminantRepresentation a ha q (Fact.out : q.Prime) hqa σ hσ δ (π x)) :=
  letI : CharP (ResidueField O) q :=
    charP_of_injective_ringHom (f := eO.symm.toRingHom) eO.symm.injective q
  let π := rationalArithmeticSupportRestriction a b hab
  let σb := σ.comp π.toMonoidHom
  let hσb : Continuous σb := hσ.comp π.continuous
  let δb := δ.comp π.toMonoidHom
  let hδb : ∀ x, GeneralLinearGroup.det (σb x) =
      Units.map (algebraMap O (ResidueField O)) (δb x) := fun x => hδ (π x)
  let hqb := dvd_trans hqa hab
  letI := arithmeticFixedDeterminantRing_isLocal b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb
  let d := arithmeticUniversalOriginalSupportFixedPowerSeriesComparison
    a ha b hb hab q degree level hqa hlevel eO σ hσ δ hδ Q hba hgood g hcard
  arithmeticFixedDeterminantConvergingParameterData b hb q degree level hqb σb hσb δb hδb
    (ι := Fin degree) (η := Fin g × Fin degree) Q
    (fun x => arithmeticFixedDeterminantRepresentation a ha q (Fact.out : q.Prime) hqa σ hσ δ (π x))
    d (fun p => (hgood p).2.1)

end
end Dubon2026
