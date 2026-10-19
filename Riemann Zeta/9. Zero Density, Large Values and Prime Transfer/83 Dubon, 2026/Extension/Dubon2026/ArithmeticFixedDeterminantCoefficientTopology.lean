import Dubon2026.ArithmeticFixedDeterminantRing
import Dubon2026.OriginalCoefficientEquivContinuity
import Mathlib.Topology.Algebra.Algebra.Equiv

/-! Upgrade coefficient comparisons with the genuine original-support
ring to continuous algebra equivalences using its proved original adic
topology. The actual auxiliary topology is supplied by its native theorem. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

/-- Residue compatibility with the actual original-support ring
constructs an algebra equivalence continuous in both directions. -/
def arithmeticFixedDeterminantCoefficientContinuousAlgEquiv
    {ι O S : Type} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    [CommRing S] [IsLocalRing S] [Algebra O S] [TopologicalSpace S]
    (hS : (inferInstance : TopologicalSpace S) = (maximalIdeal S).adicTopology)
    (eS : ResidueField S ≃ₐ[O] ResidueField O)
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g)) :
    (letI := arithmeticFixedDeterminantRing_isLocal a ha q hq hqa σ hσ δ hδ
     (e : S ≃ₐ[O] ArithmeticFixedDeterminantRing a ha q hq hqa σ hσ δ) →
     (localCoefficientReduction (arithmeticFixedDeterminantResidueEquiv a ha q hq hqa σ hσ δ hδ)).comp
       e.toAlgHom = localCoefficientReduction eS →
     S ≃A[O] ArithmeticFixedDeterminantRing a ha q hq hqa σ hσ δ) := by
  letI := arithmeticFixedDeterminantRing_isLocal a ha q hq hqa σ hσ δ hδ
  intro e hres
  have h := originalCoefficientEquiv_continuous_both
    (arithmeticFixedDeterminantRing_localData a ha q hq hqa σ hσ δ hδ).2.2 hS
    (arithmeticFixedDeterminantResidueEquiv a ha q hq hqa σ hσ δ hδ) eS e hres
  exact ContinuousAlgEquiv.mk e h.1 h.2

end
end Dubon2026
