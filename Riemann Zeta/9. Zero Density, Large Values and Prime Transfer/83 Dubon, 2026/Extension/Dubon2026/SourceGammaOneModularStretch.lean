import Dubon2026.ModularDegeneracy
import Dubon2026.SourceModularNormPolynomial

/-! DUB-17/18 -> all-weight adic association -> arithmetic finite Gamma1
realization -> genuine geometric Hecke correspondences -> the second field map.
Reuse the original level-raising matrix, conjugate and slash evaluation.
Only Gamma1 membership and the actual translated modular form are added.
The boundedness and holomorphy are supplied by native ModularForm.translate. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

theorem levelRaiseConj_mem_Gamma1 (M d : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma1 M ⊓ Gamma0 (d * M)) :
    levelRaiseConjOfDvd d γ (Gamma0_dmul_lower_left_dvd d M γ hγ.2) ∈ Gamma1 M := by
  have ha : γ ∈ Gamma1 M := hγ.1
  rw [Gamma1_mem] at ha
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · exact ha.1
  · exact ha.2.1
  · exact Gamma0_mem.mp (levelRaiseConjOfDvd_mem_Gamma0 d M γ hγ.2)

theorem gamma1_hecke_le_conj (M d : ℕ) [NeZero d] :
    (Gamma1 M ⊓ Gamma0 (d * M)).map (mapGL ℝ) ≤
      ConjAct.toConjAct (levelRaiseMatrix d)⁻¹ • (Gamma1 M).map (mapGL ℝ) := by
  intro g hg
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (levelRaiseConjOfDvd d γ (Gamma0_dmul_lower_left_dvd d M γ hγ.2)),
    Subgroup.mem_map.mpr ⟨_, levelRaiseConj_mem_Gamma1 M d γ hγ, rfl⟩, ?_⟩
  rw [ConjAct.toConjAct_smul, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact levelRaiseMatrix_mul_mapGL d γ (Gamma0_dmul_lower_left_dvd d M γ hγ.2)

/-- The literal modular form f(d*z) on the actual Gamma1 Hecke subgroup. -/
def modularStretch (M d : ℕ) [NeZero d] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ModularForm ((Gamma1 M ⊓ Gamma0 (d * M)).map (mapGL ℝ)) k :=
  ((d : ℂ) ^ (1 - k)) • ModularNormPolynomial.restrict (gamma1_hecke_le_conj M d)
    (ModularForm.translate f (levelRaiseMatrix d))

theorem modularStretch_apply (M d : ℕ) [NeZero d] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (τ : ℍ) :
    modularStretch M d f τ = f (levelRaiseMatrix d • τ) := by
  change levelRaiseFun d k (f : ℍ → ℂ) τ = _
  exact levelRaiseFun_apply d k f τ

end
end Dubon2026.SourceFunctionField.GammaOne
