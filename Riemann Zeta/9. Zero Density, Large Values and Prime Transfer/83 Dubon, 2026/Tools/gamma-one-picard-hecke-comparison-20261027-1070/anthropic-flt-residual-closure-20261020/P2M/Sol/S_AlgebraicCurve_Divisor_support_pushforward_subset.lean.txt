import Definitions.Def_AlgebraicCurve_DivisorPushPull
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_support_pushforward_subset

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [DecidableEq (Place K F)] (D : Divisor K F') : (Divisor.pushforward F D).support ⊆ D.support.image (fun w => w.restrict F) := by
  classical
  intro v hv
  rw [Finsupp.mem_support_iff, pushforward_apply] at hv
  obtain ⟨w, hw, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
  by_contra h
  exact hne (if_neg h)
