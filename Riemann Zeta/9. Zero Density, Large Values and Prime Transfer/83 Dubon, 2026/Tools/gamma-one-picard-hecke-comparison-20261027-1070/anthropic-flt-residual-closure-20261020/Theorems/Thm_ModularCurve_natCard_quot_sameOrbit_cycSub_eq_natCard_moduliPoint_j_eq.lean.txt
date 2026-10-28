import Mathlib
import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_natCard_quot_sameOrbit_cycSub_eq_natCard_moduliPoint_j_eq

theorem ModularCurve.natCard_quot_sameOrbit_cycSub_eq_natCard_moduliPoint_j_eq (N : ℕ) [NeZero N]
    (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) [E₀.IsElliptic] :
    Nat.card (Quot (fun H H' : ModularCurve.CycSub E₀ N => ModularCurve.SameOrbit E₀ H.1 H'.1))
      = Nat.card {x : ModularCurve.ModuliPoint N (AlgebraicClosure ℚ) // ModularCurve.ModuliPoint.j x = E₀.j} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_natCard_quot_sameOrbit_cycSub_eq_natCard_moduliPoint_j_eq.solution
