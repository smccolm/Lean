import Dubon2026.SourceModularCharTwoPicardInjectivity
import Dubon2026.SourceModularCharThreePicardInjectivity
import Dubon2026.SourceModularTameResidueGenus

/-! DUB-17/18 -> original arithmetic Frobenius/inertia comparison. Combine
the proved tame and both wild cases into the exact prime-characteristic
good-reduction input. Genus equality and torsion injectivity now require only
the original level-invertibility condition, with no genus certificate. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem modular_residue_genusFF_eq_originalGenus_of_prime
    (p : ℕ) [CharP kk p] (hp : p.Prime) (hNk : (N : kk) ≠ 0) :
    genusFF kk Fb = originalGenus N Qbar := by
  by_cases h2 : p = 2
  · subst p
    exact modular_residue_genusFF_eq_originalGenus_of_char_two A N hNk
  by_cases h3 : p = 3
  · subst p
    exact modular_residue_genusFF_eq_originalGenus_of_char_three A N hNk
  have h4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  exact modular_residue_genusFF_eq_originalGenus_of_five_le A N p hp5 hNk

theorem exists_modular_picard_torsion_injective_of_prime
    (p : ℕ) [CharP kk p] (hp : p.Prime) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧
      genusFF kk Fb = genusFF Qbar FF ∧
      ∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m)) := by
  have hgen : genusFF kk Fb = genusFF Qbar FF :=
    (modular_residue_genusFF_eq_originalGenus_of_prime A N p hp hNk).trans
      (coefficient_genusFF_eq_originalGenus N).symm
  exact exists_modular_picard_torsion_injective_of_genus_eq A N hNk hgen

end
end Dubon2026.SourceFunctionField.GaussReduction
