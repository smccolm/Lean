import Dubon2026.ArithmeticUniversalAuxiliaryQuotient
import Dubon2026.ArithmeticFixedDeterminantCompactness

/-! The actual universal auxiliary quotient is a complete Noetherian
local coefficient ring with its original maximal-adic topology. These
properties allow its own universal framed fiber to be used in the two
directions of the original-support ring identification. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

/-- The simultaneous actual auxiliary quotient has all original
complete local coefficient properties required by the universal
classification. The existing compact local quotient results discharge
the topology and completion conditions. -/
theorem arithmeticAuxiliaryUniversalRing_localData
    {ι O : Type} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (b : 𝓞 ℚ) (hb : b ≠ 0) (q : ℕ) (hq : q.Prime) (hqb : (q : 𝓞 ℚ) ∣ b)
    (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup b →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (Q : Finset Nat.Primes)
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      σ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1) :
    (letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σ hσ δ hδ Q hI
     IsNoetherianRing (ArithmeticAuxiliaryUniversalRing b hb q hq hqb σ hσ δ Q) ∧
       IsAdicComplete (maximalIdeal (ArithmeticAuxiliaryUniversalRing b hb q hq hqb σ hσ δ Q))
         (ArithmeticAuxiliaryUniversalRing b hb q hq hqb σ hσ δ Q) ∧
       (inferInstance : TopologicalSpace (ArithmeticAuxiliaryUniversalRing b hb q hq hqb σ hσ δ Q)) =
         (maximalIdeal (ArithmeticAuxiliaryUniversalRing b hb q hq hqb σ hσ δ Q)).adicTopology) := by
  let R := ArithmeticFixedDeterminantRing b hb q hq hqb σ hσ δ
  letI := arithmeticFixedDeterminantRing_isLocal b hb q hq hqb σ hσ δ hδ
  letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σ hσ δ hδ Q hI
  have hR := arithmeticFixedDeterminantRing_localData b hb q hq hqb σ hσ δ hδ
  letI : IsNoetherianRing R := hR.1
  letI : CompactSpace R := arithmeticFixedDeterminantRing_compactSpace b hb q hq hqb σ hσ δ
  letI : T2Space R := arithmeticFixedDeterminantRing_t2Space b hb q hq hqb σ hσ δ
  let J := arithmeticAuxiliaryInertiaRelationIdeal b Q
    (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom
  refine ⟨isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, ?_, ?_⟩
  · exact compactLocalAdicQuotient_maximal_complete J hR.2.2
  · exact localQuotient_maximal_adicTopology J hR.2.2

end
end Dubon2026
