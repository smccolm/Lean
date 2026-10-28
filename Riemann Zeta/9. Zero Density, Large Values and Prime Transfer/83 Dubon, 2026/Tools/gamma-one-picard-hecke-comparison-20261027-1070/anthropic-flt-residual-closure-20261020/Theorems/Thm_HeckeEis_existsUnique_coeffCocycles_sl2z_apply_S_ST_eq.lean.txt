import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq

theorem HeckeEis.existsUnique_coeffCocycles_sl2z_apply_S_ST_eq
    (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V]
    (ρ : Representation K (Matrix.SpecialLinearGroup (Fin 2) ℤ) V) (x y : V)
    (hx : x + ρ ModularGroup.S x = 0)
    (hy : y + ρ (ModularGroup.S * ModularGroup.T) y
        + ρ (ModularGroup.S * ModularGroup.T) (ρ (ModularGroup.S * ModularGroup.T) y) = 0) :
    ∃! z : ↥(HeckeEis.coeffCocycles ρ),
      (z : Matrix.SpecialLinearGroup (Fin 2) ℤ → V) ModularGroup.S = x
        ∧ (z : Matrix.SpecialLinearGroup (Fin 2) ℤ → V) (ModularGroup.S * ModularGroup.T) = y := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq.solution
