import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ) (n : ℕ)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    ∃ mu : ℕ → κ,
      HeckeEis.IsEigensystemH1 N
        ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) ∅ mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → mu ℓ = lam ℓ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom.solution
