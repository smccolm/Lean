import Dubon2026.ArithmeticUniversalOriginalSupportRingComparison
import Dubon2026.ArithmeticSupportRepresentationLocalConjugacy

/-! The constructed original-support isomorphism identifies the actual
local universal representations up to a constructed conjugating matrix.
This is the precise comparison required to transport local conditions. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- At every prime, the actual original local embeddings give
conjugate universal matrices under the constructed ring isomorphism. -/
def arithmeticUniversalOriginalSupportLocalConjugator
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
    (hab : a ∣ b) (haway : ∀ p : Q, ¬(p.val.val : 𝓞 ℚ) ∣ a)
    (p : ℕ) (hp : p.Prime) :=
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
  Classical.indefiniteDescription _ (arithmeticSupportRepresentation_local_conjugacy a b hab
    (arithmeticFixedDeterminantRepresentation a ha q hq hqa σ hσ δ).toMonoidHom
    (arithmeticAuxiliaryUniversalRepresentation b hb q hq hqb σb hσb δb Q).toMonoidHom
    c.equiv.toAlgHom.toRingHom c.evaluation p hp)

end
end Dubon2026
