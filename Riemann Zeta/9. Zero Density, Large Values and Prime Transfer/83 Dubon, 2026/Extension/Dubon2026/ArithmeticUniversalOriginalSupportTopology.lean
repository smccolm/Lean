import Dubon2026.ArithmeticUniversalOriginalSupportRingComparison
import Dubon2026.ArithmeticFixedDeterminantCoefficientTopology

/-! Both directions of the actual original-support ring comparison
are continuous for their original quotient topologies. This supplies
the topological compatibility needed by the DUB-17 deformation chain. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- The actual original-support comparison preserves both original
coefficient topologies. No continuity premise is supplied. -/
def arithmeticUniversalOriginalSupportContinuousAlgEquiv
    {ι O : Type} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    [CharP (ResidueField O) q]
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (b : 𝓞 ℚ) (hb : b ≠ 0) (Q : Finset Nat.Primes)
    (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ))
    (hab : a ∣ b) (haway : ∀ p : Q, ¬(p.val.val : 𝓞 ℚ) ∣ a) :=
  let π := rationalArithmeticSupportRestriction a b hab
  let σb := σ.comp π.toMonoidHom
  let hσb : Continuous σb := hσ.comp π.continuous
  let δb := δ.comp π.toMonoidHom
  let hqb := dvd_trans hqa hab
  let hδb : ∀ g, GeneralLinearGroup.det (σb g) =
      Units.map (algebraMap O (ResidueField O)) (δb g) := fun g => hδ (π g)
  let hIb : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      σb (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1 :=
    fun p g hg => rationalArithmeticSupportCharacter_inertia_eq_one a b hab σ
      p.val.val p.val.property (haway p) g hg
  letI := arithmeticFixedDeterminantRing_isLocal a ha q hq hqa σ hσ δ hδ
  letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σb hσb δb hδb Q hIb
  let c := arithmeticUniversalOriginalSupportRingComparison a ha q hq hqa σ hσ δ hδ b hb Q hba hab haway
  arithmeticFixedDeterminantCoefficientContinuousAlgEquiv (O := O)
    (S := ArithmeticAuxiliaryUniversalRing b hb q hq hqb σb hσb δb Q)
    (arithmeticAuxiliaryUniversalRing_localData b hb q hq hqb σb hσb δb hδb Q hIb).2.2
    (arithmeticAuxiliaryUniversalResidueEquiv b hb q hq hqb σb hσb δb hδb Q hIb)
    a ha q hq hqa σ hσ δ hδ c.equiv c.residue

end
end Dubon2026
