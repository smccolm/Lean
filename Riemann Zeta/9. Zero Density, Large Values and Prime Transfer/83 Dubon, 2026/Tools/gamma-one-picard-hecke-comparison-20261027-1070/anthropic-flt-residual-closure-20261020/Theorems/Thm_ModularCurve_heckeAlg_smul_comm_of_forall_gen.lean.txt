import Definitions.Def_HeckeGalois_EichlerShimura
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeAlg_smul_comm_of_forall_gen

theorem ModularCurve.heckeAlg_smul_comm_of_forall_gen {J J' : Type*} [AddCommGroup J] [AddCommGroup J'] [Module ModularCurve.HeckeAlg J] [Module ModularCurve.HeckeAlg J'] (sp : J →+ J') (hgen : ∀ (q : Nat.Primes) (x : J), sp (ModularCurve.heckeGen q • x) = ModularCurve.heckeGen q • sp x) (T : ModularCurve.HeckeAlg) (x : J) : sp (T • x) = T • sp x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeAlg_smul_comm_of_forall_gen.solution
