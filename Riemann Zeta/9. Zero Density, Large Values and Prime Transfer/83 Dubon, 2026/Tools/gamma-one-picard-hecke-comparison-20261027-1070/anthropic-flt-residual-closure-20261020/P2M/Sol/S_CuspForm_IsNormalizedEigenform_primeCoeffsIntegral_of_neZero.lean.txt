import Mathlib
import Definitions.Def_CuspForm_EigenformCoefficientRing
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import P2M.Util
namespace P2MW.S_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero
attribute [-simp] PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU

open scoped CongruenceSubgroup

theorem solution {M : ℕ} [NeZero M]
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform) :
    g.PrimeCoeffsIntegral := by
  intro ℓ
  haveI : Module.Finite ℤ (CuspForm.heckeAlgebra M 2 (∅ : Set ℕ)) :=
    CuspForm.moduleFinite_heckeAlgebra_two M ∅
  haveI hint : Algebra.IsIntegral ℤ (CuspForm.heckeAlgebra M 2 (∅ : Set ℕ)) :=
    Algebra.IsIntegral.of_finite ℤ _
  obtain ⟨χ, -, hT, hU⟩ := hg.exists_ringHom_heckeAlgebra (∅ : Set ℕ)
  by_cases hℓM : (ℓ : ℕ) ∣ M
  · refine ⟨⟨ModularFormClass.qCoeff g ℓ, ?_⟩, rfl⟩
    rw [← hU ℓ ℓ.2 hℓM (Set.notMem_empty _)]
    exact (hint.isIntegral _).map χ.toIntAlgHom
  · refine ⟨⟨ModularFormClass.qCoeff g ℓ, ?_⟩, rfl⟩
    rw [← hT ℓ ℓ.2 hℓM (Set.notMem_empty _)]
    exact (hint.isIntegral _).map χ.toIntAlgHom
