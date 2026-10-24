import Dubon2026.SourceModularKummerJointGenusInequality
import Dubon2026.SourceModularKummerGenus

/-! DUB-17/18 -> prime-to-characteristic Picard torsion injectivity.
The proved unramified genus identity and total residue-genus inequality
force a q-th root in the original modular field when the original and
residue genera agree. Only that narrower genus equality remains explicit;
the next actual tame consumer derives it. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual residue coefficient algebra for power lifting. -/
local instance powerLiftResidueAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

/-- The original coefficient algebra, avoiding an unrelated Laurent-series tower search. -/
local instance powerLiftOriginalAlgebra : Algebra Qbar FF :=
  (modularFunctionFieldCoeff N Qbar).toSubalgebra.algebra

theorem modular_exists_power_of_residue_power_of_genus_eq
    (hNk : (N : kk) ≠ 0) {q : ℕ} [hqp : Fact q.Prime] (hq : (q : kk) ≠ 0)
    (hgen : genusFF kk Fbar = genusFF Qbar FF)
    (f : gaussRing A N) (hdvd : ∀ P : Place Qbar FF, (q : ℤ) ∣ P.ord (f : FF))
    {w : Fbar} (hw0 : w ≠ 0)
    (hw : w ^ q = modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f) :
    ∃ g : FF, g ^ q = (f : FF) := by
  classical
  by_contra hnone
  have hf : ∀ g : FF, g ^ q ≠ (f : FF) := fun g hg => hnone ⟨g, hg⟩
  let E := (X ^ q - C (f : FF)).SplittingField
  have hineq := modular_kummer_joint_genus_inequality A N hNk hq f hf hw0 hw E
  rw [hgen] at hineq
  have hineqZ : (q : ℤ) * (genusFF Qbar FF : ℤ) ≤ (genusFF Qbar E : ℤ) := by
    exact_mod_cast hineq
  have hidentity : (genusFF Qbar E : ℤ) - 1 =
      (q : ℤ) * ((genusFF Qbar FF : ℤ) - 1) := modular_kummer_genus_sub_one N hf hdvd E
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hqp.out.two_le
  nlinarith only [hineqZ, hidentity, hq2]

end
end Dubon2026.SourceFunctionField.GaussReduction
