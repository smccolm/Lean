import Dubon2026.CuspCoprimeOldspace
import Dubon2026.HeckeCommutativity

/-! # Actual newform multiplicity one for the good Hecke eigensystem -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- A genuine Hecke eigenvector equation determines the indexed coefficient from the first one. -/
theorem cuspHeckeLinear_eigen_coefficient {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) {n : ℕ} (hn : n ≠ 0) (a : ℂ)
    (hf : cuspHeckeLinear N k n f = a • f) :
    cuspCoefficients f n = a * cuspCoefficients f 1 := by
  have hc := congrArg (cuspCoefficientLinear N k 1) hf
  change cuspCoefficients (cuspHecke n f) 1 = cuspCoefficientLinear N k 1 (a • f) at hc
  rw [cuspHecke_coeff, classicalHeckeCoefficient_one N k hn, map_smul] at hc
  exact hc

/-- A nonzero actual newspace good eigenform has nonzero first Fourier coefficient. -/
theorem cusp_new_good_eigen_coefficient_one_ne_zero (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hnew : f ∈ cuspNewspace N k)
    (he : IsCuspHeckeEigenform f) (hf : f ≠ 0) : cuspCoefficients f 1 ≠ 0 := by
  intro hz
  apply hf
  apply cusp_new_coprime_eq_zero N k f hnew
  intro n hnN
  by_cases hn : n = 0
  · subst n
    exact cuspCoefficients_zero f
  · obtain ⟨a, ha⟩ := he n (Nat.pos_of_ne_zero hn) hnN.symm
    have hc := cusp_hecke_eigenfunction_coefficients f n a ha 1
    rwa [classicalHeckeCoefficient_one N k hn, hz, mul_zero] at hc

/-- Every actual newspace vector with a primitive form's good eigenvalues is its first-coefficient multiple. -/
theorem primitiveCuspForm_same_eigensystem_scalar {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspNewspace N k)
    (he : ∀ n, 0 < n → n.Coprime N →
      cuspHeckeLinear N k n g = cuspCoefficients f.toCuspForm n • g) :
    g = cuspCoefficients g 1 • f.toCuspForm := by
  apply cusp_new_eq_of_coprime_coefficients N k g _ hg
    ((cuspNewspace N k).smul_mem _ f.isNew)
  intro n hnN
  by_cases hn : n = 0
  · subst n
    rw [cuspCoefficients_zero, cuspCoefficients_zero]
  · change cuspCoefficients g n = cuspCoefficientLinear N k n (cuspCoefficients g 1 • f.toCuspForm)
    rw [map_smul, cuspHeckeLinear_eigen_coefficient g hn _ (he n (Nat.pos_of_ne_zero hn) hnN.symm)]
    exact mul_comm _ _

/-- A true newspace-preserving endomorphism commuting with all good Hecke operators acts scalarly
on every primitive form. The preservation and commutation premises remain explicit. -/
theorem primitiveCuspForm_commuting_endomorphism_scalar {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k)
    (A : Module.End ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k))
    (hA : ∀ g ∈ cuspNewspace N k, A g ∈ cuspNewspace N k)
    (hcomm : ∀ n, 0 < n → n.Coprime N → Commute A (cuspHeckeLinear N k n)) :
    A f.toCuspForm = cuspCoefficients (A f.toCuspForm) 1 • f.toCuspForm := by
  apply primitiveCuspForm_same_eigensystem_scalar f (A f.toCuspForm) (hA _ f.isNew)
  intro n hn hnN
  calc
    cuspHeckeLinear N k n (A f.toCuspForm) = A (cuspHeckeLinear N k n f.toCuspForm) :=
      (LinearMap.congr_fun (hcomm n hn hnN).eq f.toCuspForm).symm
    _ = cuspCoefficients f.toCuspForm n • A f.toCuspForm := by
      rw [primitiveCuspForm_eigenvector f hn hnN, map_smul]

end
end Dubon2026
