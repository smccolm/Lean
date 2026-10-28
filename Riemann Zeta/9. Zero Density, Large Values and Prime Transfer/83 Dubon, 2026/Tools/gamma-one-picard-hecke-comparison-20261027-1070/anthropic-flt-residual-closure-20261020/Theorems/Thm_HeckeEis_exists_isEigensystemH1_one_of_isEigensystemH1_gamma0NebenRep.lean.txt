import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_Gamma0NebenRep
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (S₀ : Set ℕ) (e t : ℕ)
    (het : (p - 1) ∣ e + 2 * t)
    (κ : Type) [Field κ] [CharP κ p] (nu : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 M (HeckeEis.gamma0NebenRep p M hpM κ e)
      (fun _ => LinearMap.id) S₀ nu) :
    ∃ (M' : ℕ) (mu : ℕ → κ), M ∣ M' ∧ M' ∣ M * p ∧
      HeckeEis.IsEigensystemH1 M' (1 : Representation κ (CongruenceSubgroup.Gamma0 M') κ)
        (fun _ => LinearMap.id) (insert p S₀) mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ p → ℓ ∉ S₀ → mu ℓ = (ℓ : κ) ^ t * nu ℓ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.solution
