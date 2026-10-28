import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_le_dedekindPsi
import P2M.Util
namespace P2MW.S_ModularCurve_dedekindPsi_pos

open ModularCurve

theorem solution (N : ℕ) (hN : N ≠ 0) : 0 < dedekindPsi N :=
  lt_of_lt_of_le (Nat.pos_of_ne_zero hN) (ModularCurve.le_dedekindPsi N hN)
