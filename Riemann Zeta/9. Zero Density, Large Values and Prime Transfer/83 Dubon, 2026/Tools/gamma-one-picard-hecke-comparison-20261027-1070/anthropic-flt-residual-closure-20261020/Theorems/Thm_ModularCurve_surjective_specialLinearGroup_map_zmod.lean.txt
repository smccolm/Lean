import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_surjective_specialLinearGroup_map_zmod

theorem ModularCurve.surjective_specialLinearGroup_map_zmod (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_surjective_specialLinearGroup_map_zmod.solution
