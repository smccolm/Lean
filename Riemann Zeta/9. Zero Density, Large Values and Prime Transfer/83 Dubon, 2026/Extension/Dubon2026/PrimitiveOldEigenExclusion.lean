import Dubon2026.PrimitiveMultiplicityOne
import Dubon2026.HeckeAllOldStability

/-! # No oldspace vector shares an actual primitive form's complete good eigenvalue system -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Any oldspace vector with the good eigenvalues of a primitive form has first coefficient zero. -/
theorem primitiveCuspForm_old_eigen_first_zero {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspOldspace N k)
    (he : ∀ n, 0 < n → n.Coprime N →
      cuspHeckeLinear N k n g = cuspCoefficients f.toCuspForm n • g) :
    cuspCoefficients g 1 = 0 := by
  by_contra hc
  have hdiff : f.toCuspForm - (cuspCoefficients g 1)⁻¹ • g ∈ cuspOldspace N k := by
    apply cusp_coprime_support_old N k
    intro n hnN
    by_cases hn : n = 0
    · subst n
      exact cuspCoefficients_zero _
    · change cuspCoefficientLinear N k n (f.toCuspForm - (cuspCoefficients g 1)⁻¹ • g) = 0
      rw [map_sub, map_smul]
      change cuspCoefficients f.toCuspForm n -
        (cuspCoefficients g 1)⁻¹ * cuspCoefficients g n = 0
      rw [cuspHeckeLinear_eigen_coefficient g hn _ (he n (Nat.pos_of_ne_zero hn) hnN.symm)]
      field_simp
      ring1
  have hfold : f.toCuspForm ∈ cuspOldspace N k := by
    have hh := (cuspOldspace N k).add_mem hdiff ((cuspOldspace N k).smul_mem (cuspCoefficients g 1)⁻¹ hg)
    simpa only [sub_add_cancel] using hh
  exact primitiveCuspForm_ne_zero f
    (Submodule.disjoint_def.mp (cuspOldspace_disjoint_newspace N k) f.toCuspForm hfold f.isNew)

/-- The oldspace contains no nonzero vector with the complete good eigensystem of a genuine primitive form. -/
theorem primitiveCuspForm_old_eigen_eq_zero {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspOldspace N k)
    (he : ∀ n, 0 < n → n.Coprime N →
      cuspHeckeLinear N k n g = cuspCoefficients f.toCuspForm n • g) : g = 0 := by
  apply cuspCoefficients_injective N k
  funext m
  change cuspCoefficients g m = cuspCoefficientLinear N k m 0
  rw [map_zero]
  by_cases hm : m = 0
  · subst m
    exact cuspCoefficients_zero g
  · have hh := primitiveCuspForm_old_eigen_first_zero f (cuspHeckeLinear N k m g)
      (cuspOldspace_hecke_all N k m g hg) (by
        intro n hn hnN
        calc
          cuspHeckeLinear N k n (cuspHeckeLinear N k m g) =
              cuspHeckeLinear N k m (cuspHeckeLinear N k n g) :=
            LinearMap.congr_fun (cuspHeckeLinear_commute N k n m).eq g
          _ = cuspCoefficients f.toCuspForm n • cuspHeckeLinear N k m g := by
            rw [he n hn hnN, map_smul])
    change cuspCoefficients (cuspHecke m g) 1 = 0 at hh
    rwa [cuspHecke_coeff, classicalHeckeCoefficient_one N k hm] at hh

end
end Dubon2026
