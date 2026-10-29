import Dubon2026.SourceGammaOneHeckeFieldInclusion
import Dubon2026.SourceGammaOneIntegralJRatio
import Dubon2026.SourceModularFunctionFieldCoefficients

/-! DUB-17/18 -> original Gamma1 degree/genus -> signed-index lower bound
-> the actual full modular base field is fixed by the reduced diamond action.
Reuse the proved j integral-ratio membership and the existing degeneracy
field inclusion at level one. This places every divisor j expansion in
the original Gamma0 ratio field without rebuilding an explicit j ratio
or a separate modular-form stretching construction. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open CongruenceSubgroup GammaOne IntermediateField
open scoped MatrixGroups

theorem divisor_j_mem_gammaZeroField (K : Type*) [Field K] (N d : ℕ) [NeZero d]
    (hd : d ∣ N) : qExpand K d (jqModC K) ∈ qExpFunctionFieldC K (Gamma0 N) := by
  have hj : jqModC K ∈ x1FunctionFieldC K 1 := jqModC_mem_integralRatioField K (Gamma1 1)
  have hm : qExpand K d (jqModC K) ∈ (x1FunctionFieldC K 1).map (qExpandAlgHom K d) :=
    ⟨jqModC K, hj, rfl⟩
  have hsub : Gamma0 N ≤ Gamma1 1 ⊓ Gamma0 (d * 1) := by
    intro γ hγ
    constructor
    · change γ ∈ Gamma1 1
      rw [Gamma1_mem]
      exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    · change γ ∈ Gamma0 (d * 1)
      rw [Gamma0_mem] at hγ ⊢
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      simpa only [Nat.mul_one] using (Int.natCast_dvd_natCast.mpr hd).trans
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ)
  exact qExpFunctionFieldC_mono K hsub ((gamma1_degeneracy_map_le K 1 d) hm)

theorem fullBase_le_gammaZeroField (K : Type*) [Field K] (N : ℕ) :
    modularFunctionFieldCoeff N K ≤ qExpFunctionFieldC K (Gamma0 N) := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨d, hd0, hd, rfl⟩
  letI := hd0
  exact divisor_j_mem_gammaZeroField K N d hd

end
end Dubon2026.SourceFunctionField.IntegralDiamond
