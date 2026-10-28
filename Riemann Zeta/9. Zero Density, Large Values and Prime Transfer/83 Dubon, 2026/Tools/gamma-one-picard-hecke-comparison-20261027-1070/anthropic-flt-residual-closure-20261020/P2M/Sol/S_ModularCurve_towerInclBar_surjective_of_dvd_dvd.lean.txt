import Definitions.Def_ModularCurve_DegeneracyTower
import P2M.Util
namespace P2MW.S_ModularCurve_towerInclBar_surjective_of_dvd_dvd

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L] [Algebra ℚ L] {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) (h' : M ∣ N) : Function.Surjective (towerInclBar L h) := by
  intro y
  refine ⟨towerInclBar L h' y, ?_⟩
  have e := congrArg (fun f => f y) (towerInclBar_comp_towerInclBar L h' h (dvd_refl M))
  simpa only [AlgHom.comp_apply, towerInclBar_self] using e
