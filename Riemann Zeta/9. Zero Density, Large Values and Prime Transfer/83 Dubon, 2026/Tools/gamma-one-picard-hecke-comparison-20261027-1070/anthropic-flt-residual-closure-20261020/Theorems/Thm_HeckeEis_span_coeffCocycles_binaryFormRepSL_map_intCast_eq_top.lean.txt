import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import P2M.Util
import P2M.Sol.S_HeckeEis_span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top (K : Type) [Field K] [CharZero K]
    (n N : ℕ) [NeZero N] :
    Submodule.span K
      {w : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype)) |
        ∃ z : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          ∀ g : CongruenceSubgroup.Gamma0 N,
            ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm K n)) g : MvPolynomial (Fin 2) K) =
              MvPolynomial.map (Int.castRingHom K)
                (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top.solution
