import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_injective_baseChange_coeffH1_binaryFormRepSL

set_option autoImplicit false

open scoped MatrixGroups TensorProduct

theorem HeckeEis.exists_injective_baseChange_coeffH1_binaryFormRepSL (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [CharP F p] (n N : ℕ) :
    ∃ Φ : F ⊗[ℤ] HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[F]
        HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      Function.Injective Φ ∧
      ∀ (c : F)
        (z : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype))),
        ∃ w : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          (∀ g : CongruenceSubgroup.Gamma0 N,
              ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm F n)) g : MvPolynomial (Fin 2) F) =
                c • MvPolynomial.map (Int.castRingHom F)
                  (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))) ∧
            Φ (c ⊗ₜ[ℤ] HeckeEis.coeffH1Mk _ z) = HeckeEis.coeffH1Mk _ w := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_injective_baseChange_coeffH1_binaryFormRepSL.solution
