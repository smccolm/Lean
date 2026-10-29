import Dubon2026.SourceGammaOneKummerResidueGenus
import Dubon2026.SourceGammaOneKummerGenus

/-! DUB-17/18 -> original Gamma1 arithmetic association -> Picard/Tate
specialization -> prime-to-residue torsion injectivity. The actual
Kummer cover's proved genus identity contradicts its proved residue genus
inequality if a prime root is missing. Only actual coordinate-degree and
genus preservation remain explicit. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve Polynomial IntermediateField
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M : ℕ) [NeZero M]
local notation "Δ" => CongruenceSubgroup.Gamma1 M
local notation "FF" => functionFieldOver Δ Qbar
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Δ

/-- The actual original coefficient algebra for its splitting field. -/
@[reducible] local instance gammaOnePowerLiftOriginalAlgebra : Algebra Qbar FF :=
  (functionFieldOver Δ Qbar).toSubalgebra.algebra

theorem gammaOne_exists_power_of_residue_power_of_degree_genus_eq
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Δ Qbar⟯ FF =
      Module.finrank kk⟮residueJCoordinate A Δ⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar FF)
    {q : ℕ} [hqp : Fact q.Prime] (hq : (q : kk) ≠ 0)
    (f : coefficientGaussRing Δ A)
    (hdvd : ∀ P : Place Qbar FF, (q : ℤ) ∣ P.ord (f : FF))
    {w : Fb} (hw0 : w ≠ 0) (hw : w ^ q = residueToImage A Δ f) :
    ∃ g : FF, g ^ q = (f : FF) := by
  classical
  by_contra hnone
  have hf : ∀ g : FF, g ^ q ≠ (f : FF) := fun g hg => hnone ⟨g, hg⟩
  let E := (X ^ q - C (f : FF)).SplittingField
  have hineq := gammaOne_kummer_residue_genus_inequality_of_degree_eq A M hdeg hq f hf hdvd hw0 hw E
  rw [hgen] at hineq
  have hineqZ : (q : ℤ) * (genusFF Qbar FF : ℤ) ≤ (genusFF Qbar E : ℤ) := by
    exact_mod_cast hineq
  have hidentity : (genusFF Qbar E : ℤ) - 1 =
      (q : ℤ) * ((genusFF Qbar FF : ℤ) - 1) := gammaOne_kummer_genus_sub_one M hf hdvd E
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hqp.out.two_le
  nlinarith only [hineqZ, hidentity, hq2]

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
