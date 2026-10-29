import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularForm_exists_basis_gamma1_qCoeff_mem_range_ratCast
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import P2M.Util
namespace P2MW.S_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1

set_option autoImplicit false

open scoped MatrixGroups ModularForm in
theorem solution
    (N : ℕ) [NeZero N] {k : ℤ}
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by
  classical
  obtain ⟨n, b, hb⟩ := ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast N k
  have hrat : ∀ (i : Fin n) (m : ℕ), ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 (⇑(b i) : UpperHalfPlane → ℂ)).coeff m = (r : ℂ) := by
    intro i m
    obtain ⟨r, hr⟩ := hb i m
    exact ⟨r, hr.symm⟩
  choose D r hD hint using fun i => ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion N (b i) (hrat i)
  refine ⟨n, fun i => b.repr F i / (D i : ℂ), fun i => ((D i : ℂ)) • b i, r, fun i => ?_, ?_⟩
  · rw [ModularForm.IsGLPos.coe_smul]; exact hint i
  · have hsum := b.sum_repr F
    have hcoe : (⇑F : UpperHalfPlane → ℂ) = ∑ i, b.repr F i • (⇑(b i) : UpperHalfPlane → ℂ) := by
      conv_lhs => rw [← hsum]
      rw [show (⇑(∑ i, b.repr F i • b i) : UpperHalfPlane → ℂ) = FunLike.coeAddMonoidHom (ModularForm _ k) UpperHalfPlane ℂ (∑ i, b.repr F i • b i) from rfl, map_sum]
      rfl
    rw [hcoe]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ModularForm.IsGLPos.coe_smul, smul_smul, div_mul_cancel₀ _ (Int.cast_ne_zero.mpr (hD i))]
