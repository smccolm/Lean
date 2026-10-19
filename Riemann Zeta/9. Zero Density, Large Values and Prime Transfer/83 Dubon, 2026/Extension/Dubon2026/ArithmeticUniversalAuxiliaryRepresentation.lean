import Dubon2026.ArithmeticUniversalAuxiliaryQuotient
import Dubon2026.ArithmeticUnramifiedRepresentation
import Dubon2026.OriginalCoefficientQuotientRepresentation

/-! The actual continuous universal matrices on the simultaneous
auxiliary quotient. These retain the original determinant and residue
and kill every original auxiliary inertia group; they are the concrete
matrix values used to identify inverse coefficient maps. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

variable {ι O : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
  (b : 𝓞 ℚ) (hb : b ≠ 0) (q : ℕ) (hq : q.Prime) (hqb : (q : 𝓞 ℚ) ∣ b)
  (σ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup ι (ResidueField O))
  (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup b →* Oˣ) (Q : Finset Nat.Primes)

/-- The original universal matrices reduced through the literal
simultaneous auxiliary inertia ideal, with their quotient topology. -/
def arithmeticAuxiliaryUniversalRepresentation :
    rationalArithmeticGaloisGroup b →ₜ*
      GeneralLinearGroup ι (ArithmeticAuxiliaryUniversalRing b hb q hq hqb σ hσ δ Q) :=
  continuousCoefficientQuotientRepresentation
    (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ)
    (arithmeticAuxiliaryInertiaRelationIdeal b Q
      (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom)

/-- Every original auxiliary inertia element is killed by the same
actual universal quotient representation. -/
theorem arithmeticAuxiliaryUniversalRepresentation_inertia
    (p : Q) (g) (hg : g ∈ rationalPrimeNormInertia p.val.val p.val.property) :
    arithmeticAuxiliaryUniversalRepresentation b hb q hq hqb σ hσ δ Q
      (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1 := by
  let τ := (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom
  let J := arithmeticAuxiliaryInertiaRelationIdeal b Q τ
  have hJ : J ≤ RingHom.ker (Ideal.Quotient.mk J) := by
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  exact (arithmeticAuxiliaryInertiaRelationIdeal_le_kernel_iff b Q τ (Ideal.Quotient.mk J)).mp hJ p g hg

/-- The entire actual quotient representation has the original
specified determinant after the genuine coefficient quotient. -/
theorem arithmeticAuxiliaryUniversalRepresentation_det (g : rationalArithmeticGaloisGroup b) :
    GeneralLinearGroup.det (arithmeticAuxiliaryUniversalRepresentation b hb q hq hqb σ hσ δ Q g) =
      Units.map (algebraMap O (ArithmeticAuxiliaryUniversalRing b hb q hq hqb σ hσ δ Q)).toMonoidHom (δ g) := by
  let τ := arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ
  let J := arithmeticAuxiliaryInertiaRelationIdeal b Q τ.toMonoidHom
  exact (GeneralLinearGroup.map_det (Ideal.Quotient.mk J) (τ g)).trans
    (congrArg (Units.map (Ideal.Quotient.mk J).toMonoidHom)
      (arithmeticFixedDeterminantRepresentation_det b hb q hq hqb σ hσ δ g))

/-- The entire actual quotient representation has the original
residual matrices through its true residue-field identification. -/
theorem arithmeticAuxiliaryUniversalRepresentation_residue
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (hI : ∀ (p : Q) g, g ∈ rationalPrimeNormInertia p.val.val p.val.property →
      σ (rationalPrimeArithmeticRestriction b p.val.val p.val.property g) = 1) :
    (letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σ hσ δ hδ Q hI
     (GeneralLinearGroup.map
       (localCoefficientReduction (arithmeticAuxiliaryUniversalResidueEquiv b hb q hq hqb σ hσ δ hδ Q hI)).toRingHom).comp
       (arithmeticAuxiliaryUniversalRepresentation b hb q hq hqb σ hσ δ Q).toMonoidHom = σ) := by
  letI := arithmeticFixedDeterminantRing_isLocal b hb q hq hqb σ hσ δ hδ
  letI := arithmeticAuxiliaryUniversalRing_isLocal b hb q hq hqb σ hσ δ hδ Q hI
  exact originalCoefficientQuotientRepresentation_residue
    (arithmeticFixedDeterminantResidueEquiv b hb q hq hqb σ hσ δ hδ)
    (rationalArithmeticGaloisGroup b) σ (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ)
    (arithmeticFixedDeterminantRepresentation_residue b hb q hq hqb σ hσ δ hδ)
    (arithmeticAuxiliaryInertiaRelationIdeal b Q
      (arithmeticFixedDeterminantRepresentation b hb q hq hqb σ hσ δ).toMonoidHom)

end
end Dubon2026
