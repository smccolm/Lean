import Mathlib
import Definitions.Def_ModularCurve_FibrePoly
import P2M.Util
namespace P2MW.S_ModularCurve_monic_fibrePoly

open Polynomial ModularCurve

theorem solution {K : Type*} [Field K] {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic)
    (a : K) : (fibrePoly Φ a).Monic := by
  exact hΦ.map _
