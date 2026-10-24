import Dubon2026.SourceModularGenusTorsionInjectivity
import Dubon2026.SourceModularCharThreeResidueGenus

/-! The actual modular characteristic-three constant reduction preserves
genus and has a Picard map injective on every torsion subgroup whose order
is invertible in the residue field. All geometric, place, principal-divisor
and Kummer power inputs are derived. This discharges the characteristic-
three good-reduction and torsion premises in the DUB-17/18 dependency chain;
characteristic two and original arithmetic-action comparison remain required. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_picard_torsion_injective_of_char_three
    [CharP kk 3] (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧
      genusFF kk Fb = genusFF Qbar FF ∧
      ∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m)) := by
  have hgen : genusFF kk Fb = genusFF Qbar FF :=
    (modular_residue_genusFF_eq_originalGenus_of_char_three A N hNk).trans
      (coefficient_genusFF_eq_originalGenus N).symm
  exact exists_modular_picard_torsion_injective_of_genus_eq A N hNk hgen

end
end Dubon2026.SourceFunctionField.GaussReduction
