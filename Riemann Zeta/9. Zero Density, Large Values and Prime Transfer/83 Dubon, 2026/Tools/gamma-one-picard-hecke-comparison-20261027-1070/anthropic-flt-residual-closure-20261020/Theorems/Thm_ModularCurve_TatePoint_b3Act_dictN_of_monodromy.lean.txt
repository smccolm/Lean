import Definitions.Def_ModularCurve_CycSubRootBridgeN
import Definitions.Def_ModularCurve_SpecialisationBridge
import P2M.Util
import P2M.Sol.S_ModularCurve_TatePoint_b3Act_dictN_of_monodromy

open scoped Classical
theorem ModularCurve.TatePoint.b3Act_dictN_of_monodromy (N : ℕ) [NeZero N] (j₀ : Qbar)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N) :
    ∀ (data : ModularPolynomialData N) (m : HahnSeries.monodromy Qbar)
      (r r' : RootsAt data (nearCurve j₀).j),
      r'.1 = (↑m : H ≃ₐ[Qbar] H) r.1 →
        B3.b3Act j₀ m (dictN N data j₀ hW1 hW2 hW3 r).1 =
          (dictN N data j₀ hW1 hW2 hW3 r').1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TatePoint_b3Act_dictN_of_monodromy.solution
