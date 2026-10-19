import Dubon2026.ArithmeticUniversalPatchingRing
import Dubon2026.AuxiliaryBoundedTopologicalPatchingRing
import Dubon2026.ArithmeticFixedDeterminantCompactness

/-! The actual enlarged-support universal coefficient ring receives
an action of the power-series algebra indexed by Fin g × Fin degree.
The same fixed variable ideal recovers the original universal ring as an algebra over that common parameter ring.
Exact-size arithmetic selection supplies the cardinality input below. Original arithmetic ring topology and residue data derive the local continuous action and all compact Noetherian adic parameter-ring properties and finite-quotient bounds independent of the auxiliary level from the displayed coefficient assumptions. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField BigOperators

/-- Reuse the actual arithmetic power-series comparison and index its
genuine auxiliary character directions by one fixed finite type, retaining the constructed scalar-compatible quotient comparison. -/
def arithmeticUniversalOriginalSupportBoundedPatchingRingComparison
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
  letI := (arithmeticFixedDeterminantRing_localData
    b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb).1
  letI := arithmeticFixedDeterminantRing_compactSpace
    b hb q (Fact.out : q.Prime) hqb σb hσb δb
  letI := arithmeticFixedDeterminantRing_t2Space
    b hb q (Fact.out : q.Prime) hqb σb hσb δb
  let d := arithmeticUniversalOriginalSupportPatchingRingComparison
    a ha b hb hab q degree level hqa hlevel eO σ hσ δ hδ Q hba hgood g hcard
  letI := arithmeticFixedDeterminantRing_isLocal a ha q (Fact.out : q.Prime) hqa σ hσ δ hδ
  letI := (arithmeticFixedDeterminantRing_localData
    a ha q (Fact.out : q.Prime) hqa σ hσ δ hδ).1
  auxiliaryBoundedTopologicalPatchingRingComparison O
    (R := ArithmeticFixedDeterminantRing b hb q (Fact.out : q.Prime) hqb σb hσb δb)
    (A := ArithmeticFixedDeterminantRing a ha q (Fact.out : q.Prime) hqa σ hσ δ)
    (ι := Fin degree) (η := Fin g × Fin degree) Q q
    (arithmeticFixedDeterminantRepresentation b hb q (Fact.out : q.Prime) hqb σb hσb δb)
    (fun x => arithmeticFixedDeterminantRepresentation a ha q (Fact.out : q.Prime) hqa σ hσ δ (π x))
    d (arithmeticFixedDeterminantResidueEquiv b hb q (Fact.out : q.Prime) hqb σb hσb δb hδb)

end
end Dubon2026
