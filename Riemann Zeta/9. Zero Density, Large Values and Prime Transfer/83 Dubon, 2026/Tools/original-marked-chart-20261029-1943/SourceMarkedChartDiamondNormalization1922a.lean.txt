import Dubon2026.SourceGammaOneToricCoordinateDiamond
import Dubon2026.SourceOriginalResidueDiamondFixedField
import Dubon2026.SL2Reduction

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> marked-chart
stabilizers. The actual residue diamond action preserves j normalization,
and native integral SL2 reduction realizes every residue unit by Gamma0.
These facts feed normalized-embedding conjugacy and generator transport. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open CongruenceSubgroup GammaOne GammaOne.ToricCoordinates IntegralDiamond
open scoped MatrixGroups

theorem gamma0Unit_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (gamma0Unit N) := by
  intro u
  let B : SL(2, ZMod N) := ⟨!![(↑u⁻¹ : ZMod N), 0; 0, (↑u : ZMod N)], by
    rw [Matrix.det_fin_two_of]
    simp only [mul_zero, sub_zero, Units.inv_mul]⟩
  obtain ⟨g, hg⟩ := SL2Reduction.SL2_reduction_surjective N B
  have hc : (g.val 1 0 : ZMod N) = 0 :=
    congrArg (fun C : SL(2, ZMod N) => C.val 1 0) hg
  let γ : Gamma0 N := ⟨g, Gamma0_mem.mpr hc⟩
  refine ⟨γ, Units.ext ?_⟩
  exact congrArg (fun C : SL(2, ZMod N) => C.val 1 1) hg

theorem originalResidueDiamond_fixes_j
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    [CharP (IsLocalRing.ResidueField A) ℓ] (hℓN : ¬ ℓ ∣ N)
    (x : qExpFunctionFieldC (IsLocalRing.ResidueField A) (Gamma1 N))
    (hx : (x : LaurentSeries (IsLocalRing.ResidueField A)) = jqModC (IsLocalRing.ResidueField A))
    (γ : Gamma0 N) : originalResidueDiamondAction A N ℓ hℓN γ x = x := by
  letI : Algebra (ZMod ℓ) (IsLocalRing.ResidueField A) :=
    (ZMod.castHom (dvd_refl ℓ) (IsLocalRing.ResidueField A)).toAlgebra
  apply reducedFieldActionOver_fixes_fullBase (IsLocalRing.ResidueField A) N ℓ hℓN γ x
  rw [hx]
  exact jq_mem_coeff_field N (IsLocalRing.ResidueField A)

end
end Dubon2026.SourceFunctionField.MarkedChart
