import Mathlib
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par
attribute [-simp] HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coeffCoboundaryMap_apply

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd
    (M : ℕ) (h3M : 3 ∣ M) (κ : Type) [CommRing κ] [CharP κ 3]
    (x : Additive ↥(CongruenceSubgroup.Gamma0 M) →+ κ) :
    ∃ H : ↥(CongruenceSubgroup.Gamma0 M) → κ,
      ∀ γ γ' : ↥(CongruenceSubgroup.Gamma0 M),
        H (γ * γ') = H γ + H γ' +
          ((((γ : SL(2, ℤ)) 0 1) * ((γ : SL(2, ℤ)) 1 1) : ℤ) : κ) * x (Additive.ofMul γ') := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd.solution
