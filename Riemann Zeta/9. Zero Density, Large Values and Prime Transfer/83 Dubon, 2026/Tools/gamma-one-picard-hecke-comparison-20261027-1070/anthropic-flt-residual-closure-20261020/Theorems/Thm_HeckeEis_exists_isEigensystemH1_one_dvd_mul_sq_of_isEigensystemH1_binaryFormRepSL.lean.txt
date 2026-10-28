import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL
attribute [-simp] HeckeEis.gamma0NebenRep_apply

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ) (n : ℕ)
    (κ : Type) [Field κ] [CharP κ p] (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    ∃ (M : ℕ) (mu : ℕ → κ), M ∣ N * p ^ 2 ∧
      HeckeEis.IsEigensystemH1 M (1 : Representation κ (CongruenceSubgroup.Gamma0 M) κ)
        (fun _ => LinearMap.id) (insert p S₀) mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ℓ ∉ S₀ → lam ℓ = (ℓ : κ) ^ (n / 2) * mu ℓ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL.solution
