import Mathlib
import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_natCard_quot_samePlace_eq_natCard_quot_sameOrbit_of_EMD

theorem ModularCurve.exists_natCard_quot_samePlace_eq_natCard_quot_sameOrbit_of_EMD (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) (hEMD : ModularCurve.EMD N j₀) :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      Nat.card (Quot (fun ψ ψ' : ModularCurve.Emb N j₀ => ModularCurve.SamePlace ψ.1 ψ'.1))
        = Nat.card (Quot (fun H H' : ModularCurve.CycSub E₀ N => ModularCurve.SameOrbit E₀ H.1 H'.1)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_natCard_quot_samePlace_eq_natCard_quot_sameOrbit_of_EMD.solution
