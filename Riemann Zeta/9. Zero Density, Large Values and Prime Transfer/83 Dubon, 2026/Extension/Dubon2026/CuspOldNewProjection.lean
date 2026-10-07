import Dubon2026.ModularFiniteDimension
import Dubon2026.CuspPeterssonCore
import Dubon2026.HeckeOldNewStability
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Actual Petersson old/new decomposition and the genuine oldspace projection -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Finite dimensionality and the actual positive Petersson pairing make the full old and new spaces complementary. -/
theorem cuspOldspace_isCompl_newspace (N : ℕ) [NeZero N] (k : ℤ) :
    IsCompl (cuspOldspace N k) (cuspNewspace N k) := by
  letI : FiniteDimensional ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
    ModularDimension.cuspForm_finiteDimensional (Gamma0 N) k
  letI := cuspPeterssonCore N k
  letI := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
  letI := InnerProductSpace.ofCore (cuspPeterssonCore N k).toCore
  have he : cuspNewspace N k = (cuspOldspace N k).orthogonal := by
    ext f
    exact (Submodule.mem_orthogonal' (cuspOldspace N k) f).symm
  rw [he]
  exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection

/-- The actual oldspace projection along the Petersson-orthogonal full newspace. -/
def cuspOldProjection (N : ℕ) [NeZero N] (k : ℤ) :
    Module.End ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  (cuspOldspace N k).projection (cuspNewspace N k) (cuspOldspace_isCompl_newspace N k)

/-- The actual projection always lies in the full classical oldspace. -/
theorem cuspOldProjection_mem (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : cuspOldProjection N k f ∈ cuspOldspace N k :=
  Submodule.projection_apply_mem (cuspOldspace_isCompl_newspace N k) f

/-- The actual projection fixes each full oldspace vector. -/
theorem cuspOldProjection_eq_self (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ∈ cuspOldspace N k) :
    cuspOldProjection N k f = f :=
  (Submodule.projection_eq_self_iff (cuspOldspace_isCompl_newspace N k) f).mpr hf

/-- The projection vanishes precisely on the genuine Petersson newspace. -/
theorem cuspOldProjection_eq_zero_iff (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    cuspOldProjection N k f = 0 ↔ f ∈ cuspNewspace N k :=
  Submodule.projection_apply_eq_zero_iff (cuspOldspace_isCompl_newspace N k)

/-- Subtracting the actual old projection leaves a genuine newspace form. -/
theorem cusp_sub_oldProjection_new (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    f - cuspOldProjection N k f ∈ cuspNewspace N k :=
  Submodule.sub_projection_mem (cuspOldspace_isCompl_newspace N k) f

/-- The actual Petersson old projection commutes with every good Hecke operator. -/
theorem cuspOldProjection_good_commute (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ)
    (hnN : n.Coprime N) : Commute (cuspOldProjection N k) (cuspHeckeLinear N k n) := by
  apply LinearMap.ext
  intro f
  change cuspOldProjection N k (cuspHeckeLinear N k n f) =
    cuspHeckeLinear N k n (cuspOldProjection N k f)
  have he : cuspHeckeLinear N k n f =
      cuspHeckeLinear N k n (cuspOldProjection N k f) +
      cuspHeckeLinear N k n (f - cuspOldProjection N k f) := by
    rw [← map_add, add_sub_cancel]
  rw [he, map_add, cuspOldProjection_eq_self N k _
    (cuspOldspace_hecke_coprime N k n hnN _ (cuspOldProjection_mem N k f)),
    (cuspOldProjection_eq_zero_iff N k _).mpr
      (cuspNewspace_hecke_coprime n hnN _ (cusp_sub_oldProjection_new N k f)), add_zero]

end
end Dubon2026
