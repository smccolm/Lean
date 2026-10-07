import Dubon2026.PrimitiveOldEigenExclusion
import Dubon2026.CuspOldNewProjection

/-! # All-index Hecke eigenbehavior derived for actual primitive cusp forms -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Every actual Hecke image of a primitive form remains in the true newspace, including bad indices. -/
theorem primitiveCuspForm_hecke_mem_newspace {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (m : ℕ) : cuspHeckeLinear N k m f.toCuspForm ∈ cuspNewspace N k := by
  apply (cuspOldProjection_eq_zero_iff N k _).mp
  apply primitiveCuspForm_old_eigen_eq_zero f _ (cuspOldProjection_mem N k _)
  intro n hn hnN
  calc
    cuspHeckeLinear N k n (cuspOldProjection N k (cuspHeckeLinear N k m f.toCuspForm)) =
        cuspOldProjection N k (cuspHeckeLinear N k n (cuspHeckeLinear N k m f.toCuspForm)) :=
      (LinearMap.congr_fun (cuspOldProjection_good_commute N k n hnN).eq _).symm
    _ = cuspOldProjection N k (cuspHeckeLinear N k m (cuspHeckeLinear N k n f.toCuspForm)) :=
      congrArg (cuspOldProjection N k) (LinearMap.congr_fun (cuspHeckeLinear_commute N k n m).eq _)
    _ = cuspCoefficients f.toCuspForm n •
        cuspOldProjection N k (cuspHeckeLinear N k m f.toCuspForm) := by
      rw [primitiveCuspForm_eigenvector f hn hnN, map_smul, map_smul]

/-- A genuine normalized primitive form is an eigenvector of every positive classical Hecke operator. -/
theorem primitiveCuspForm_eigenvector_all {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) {m : ℕ} (hm : 0 < m) :
    cuspHeckeLinear N k m f.toCuspForm = cuspCoefficients f.toCuspForm m • f.toCuspForm := by
  have he := primitiveCuspForm_same_eigensystem_scalar f (cuspHeckeLinear N k m f.toCuspForm)
    (primitiveCuspForm_hecke_mem_newspace f m) (by
      intro n hn hnN
      calc
        cuspHeckeLinear N k n (cuspHeckeLinear N k m f.toCuspForm) =
            cuspHeckeLinear N k m (cuspHeckeLinear N k n f.toCuspForm) :=
          LinearMap.congr_fun (cuspHeckeLinear_commute N k n m).eq _
        _ = cuspCoefficients f.toCuspForm n • cuspHeckeLinear N k m f.toCuspForm := by
          rw [primitiveCuspForm_eigenvector f hn hnN, map_smul])
  change cuspHeckeLinear N k m f.toCuspForm = cuspCoefficients (cuspHecke m f.toCuspForm) 1 • f.toCuspForm at he
  rwa [cuspHecke_coeff, classicalHeckeCoefficient_one N k hm.ne'] at he

/-- Actual primitive forms satisfy the full literal analytic Hecke eigenform definition. -/
theorem primitiveCuspForm_isFullEigenform {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) : IsFullCuspHeckeEigenform f.toCuspForm := by
  intro n hn
  refine ⟨cuspCoefficients f.toCuspForm n, fun τ => ?_⟩
  have he := DFunLike.congr_fun (primitiveCuspForm_eigenvector_all f hn) τ
  change cuspHecke n f.toCuspForm τ = cuspCoefficients f.toCuspForm n * f.toCuspForm τ at he
  rwa [cuspHecke_apply] at he

end
end Dubon2026
