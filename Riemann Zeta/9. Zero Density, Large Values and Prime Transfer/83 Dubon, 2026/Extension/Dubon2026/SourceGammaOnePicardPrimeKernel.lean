import Dubon2026.SourceGammaOneKummerPowerLifting
import Dubon2026.SourceCurveReductionPrimeKernel
import Dubon2026.SourceCurveReductionPicardR2

/-! DUB-17/18 -> original Gamma1 Frobenius/inertia -> Picard torsion
specialization. The actual residue curve has only constant global regular
functions. The derived original-field Kummer power lifting then kills the
prime-order specialization kernel. Coordinate-degree and genus equality
remain explicit narrower inputs; the kernel assertion is proved from them. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve IntermediateField
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M : ℕ) [NeZero M]
local notation "Δ" => CongruenceSubgroup.Gamma1 M
local notation "FF" => functionFieldOver Δ Qbar
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Δ

theorem gammaOne_residue_lSpace_zero_eq_range :
    LSpace (0 : Divisor kk Fb) = LinearMap.range (Algebra.linearMap kk Fb) := by
  haveI := valuation_residue_isAlgClosed A
  have hT : ModularGroup.T ∈ Δ := by simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T]
  letI hcurve : IsCurveOver kk Fb := residueImage_isCurveOver A Δ hT
  haveI : ∀ v : Place kk Fb, Module.Finite kk v.ResidueField :=
    fun v => @IsCurveOver.finiteResidue kk Fb inferInstance inferInstance
      (specializationResidueAlgebra A Δ) hcurve v
  obtain ⟨P⟩ := @nonempty_place_of_separating_coordinate kk Fb inferInstance inferInstance
    (specializationResidueAlgebra A Δ) (residueJCoordinate A Δ)
    (transcendental_residueJCoordinate A Δ) (finite_residueCoordinate_and_degree_le A Δ hT).1
    (isSeparable_residueCoordinate A Δ hT)
  exact lSpace_zero_eq_range_of_principalDivisors P

theorem gammaOne_pic0_eq_zero_of_prime_torsion_of_degree_genus_eq
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Δ Qbar⟯ FF =
      Module.finrank kk⟮residueJCoordinate A Δ⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar FF)
    (R : ConstantReduction A FF Fb)
    (hR : R.toRegularProlongation = regularProlongation A Δ)
    {q : ℕ} [hqp : Fact q.Prime] (hq : (q : kk) ≠ 0)
    (z : Pic0 Qbar FF) (hqz : q • z = 0) (hz : R.pic0Map z = 0) : z = 0 := by
  haveI := valuation_residue_isAlgClosed A
  apply R.pic0_eq_zero_of_power_lifting (gammaOne_residue_lSpace_zero_eq_range A M)
    q hqp.out.pos _ z hqz hz
  change ∀ f : R.toRegularProlongation.integers,
    (∀ P : Place Qbar FF, (q : ℤ) ∣ P.ord (f : FF)) →
      ∀ {w : Fb}, w ≠ 0 → w ^ q = R.toRegularProlongation.residue f →
        ∃ g : FF, g ^ q = (f : FF)
  rw [hR]
  exact fun f hdvd _ hw0 hw =>
    gammaOne_exists_power_of_residue_power_of_degree_genus_eq A M hdeg hgen hq f hdvd hw0 hw

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
