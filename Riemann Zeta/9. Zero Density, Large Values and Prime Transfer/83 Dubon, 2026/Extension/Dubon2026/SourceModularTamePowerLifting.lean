import Dubon2026.SourceModularKummerPowerLifting
import Dubon2026.SourceModularTameResidueGenus

/-! DUB-17/18 -> prime-to-characteristic Picard torsion injectivity.
The actual tame modular genus equality removes the last geometric premise
from Kummer power lifting in residue characteristic at least five.
The wild characteristics two and three remain part of the full goal. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fbar" => modularFunctionFieldCoeff N kk

/-- The actual residue coefficient algebra for the tame consumer. -/
local instance tamePowerLiftResidueAlgebra : Algebra kk Fbar :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

/-- The actual original coefficient algebra for the tame consumer. -/
local instance tamePowerLiftOriginalAlgebra : Algebra Qbar FF :=
  (modularFunctionFieldCoeff N Qbar).toSubalgebra.algebra

theorem modular_exists_power_of_residue_power_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0)
    {q : ℕ} [Fact q.Prime] (hq : (q : kk) ≠ 0)
    (f : gaussRing A N) (hdvd : ∀ P : Place Qbar FF, (q : ℤ) ∣ P.ord (f : FF))
    {w : Fbar} (hw0 : w ≠ 0)
    (hw : w ^ q = modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f) :
    ∃ g : FF, g ^ q = (f : FF) := by
  have hgen : genusFF kk Fbar = genusFF Qbar FF :=
    (modular_residue_genusFF_eq_originalGenus_of_five_le A N p hp hNk).trans
      (coefficient_genusFF_eq_originalGenus N).symm
  exact modular_exists_power_of_residue_power_of_genus_eq A N hNk hq hgen f hdvd hw0 hw

end
end Dubon2026.SourceFunctionField.GaussReduction
