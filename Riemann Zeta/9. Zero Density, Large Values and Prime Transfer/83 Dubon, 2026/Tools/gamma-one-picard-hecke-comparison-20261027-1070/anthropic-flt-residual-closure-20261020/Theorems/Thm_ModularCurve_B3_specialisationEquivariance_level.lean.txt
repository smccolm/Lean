import Definitions.Def_ModularCurve_SpecialisationBridge
import P2M.Util
import P2M.Sol.S_ModularCurve_B3_specialisationEquivariance_level

open ModularCurve ModularCurve.TatePoint ModularCurve.B3
theorem ModularCurve.B3.specialisationEquivariance_level (N : ℕ) [NeZero N] (j₀ : Qbar) :
    ∃ β : CycSubH (nearCurve j₀) N ≃ CycSub (WeierstrassCurve.ofJ j₀) N,
      ∀ G G' : CycSubH (nearCurve j₀) N,
        (∃ m : HahnSeries.monodromy Qbar, b3Act j₀ m G.1 = G'.1) ↔
          SameOrbit (WeierstrassCurve.ofJ j₀) (β G).1 (β G').1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_B3_specialisationEquivariance_level.solution
