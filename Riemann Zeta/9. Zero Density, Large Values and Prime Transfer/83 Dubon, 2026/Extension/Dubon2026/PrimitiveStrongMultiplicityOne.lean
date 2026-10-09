import Dubon2026.PrimitiveFullEigen

/-! # The entire original-level good Hecke eigenspace of an actual primitive form -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The original Petersson old projection and proved old-eigensystem exclusion force every original-level vector with a primitive good eigensystem into the actual newspace. -/
theorem primitiveCuspForm_good_eigen_mem_newspace {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (he : ∀ n, 0 < n → n.Coprime N →
      cuspHeckeLinear N k n g = cuspCoefficients f.toCuspForm n • g) :
    g ∈ cuspNewspace N k := by
  apply (cuspOldProjection_eq_zero_iff N k g).mp
  apply primitiveCuspForm_old_eigen_eq_zero f _ (cuspOldProjection_mem N k g)
  intro n hn hnN
  calc
    cuspHeckeLinear N k n (cuspOldProjection N k g) =
        cuspOldProjection N k (cuspHeckeLinear N k n g) :=
      (LinearMap.congr_fun (cuspOldProjection_good_commute N k n hnN).eq g).symm
    _ = cuspCoefficients f.toCuspForm n • cuspOldProjection N k g := by
      rw [he n hn hnN, map_smul]

/-- A primitive form's entire good Hecke eigenspace at its original level is its actual line; newspace membership is derived from the original old/new decomposition. -/
theorem primitiveCuspForm_good_eigensystem_scalar {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (g : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (he : ∀ n, 0 < n → n.Coprime N →
      cuspHeckeLinear N k n g = cuspCoefficients f.toCuspForm n • g) :
    g = cuspCoefficients g 1 • f.toCuspForm :=
  primitiveCuspForm_same_eigensystem_scalar f g
    (primitiveCuspForm_good_eigen_mem_newspace f g he) he

end
end Dubon2026
