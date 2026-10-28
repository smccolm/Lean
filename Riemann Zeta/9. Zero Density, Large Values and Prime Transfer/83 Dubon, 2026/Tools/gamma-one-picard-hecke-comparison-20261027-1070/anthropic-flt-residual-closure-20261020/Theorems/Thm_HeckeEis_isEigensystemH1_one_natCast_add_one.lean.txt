import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_isEigensystemH1_one_natCast_add_one

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isEigensystemH1_one_natCast_add_one (M : ℕ) (hM : 2 ≤ M) (κ : Type) [Field κ]
    (S₀ : Set ℕ) :
    HeckeEis.IsEigensystemH1 M (1 : Representation κ (CongruenceSubgroup.Gamma0 M) κ)
      (fun _ => LinearMap.id) S₀ (fun ℓ => (ℓ : κ) + 1) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_one_natCast_add_one.solution
