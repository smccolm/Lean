import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1
    (N : ℕ) [NeZero N] (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (κ : Type) [Field κ] (hq1 : ((q + 1 : ℕ) : κ) ≠ 0) (S₀ : Set ℕ) (n : ℕ) (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    HeckeEis.IsEigensystemH1 (N * q)
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 (N * q)).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) (insert q S₀) lam := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1.solution
