import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_eigenform

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.exists_coeffH1par_int_modp_eigenclass_of_eigenform (N : ℕ) [NeZero N] (n : ℕ) (S : Set ℕ) (p : ℕ) [Fact p.Prime]
    (Q : ℕ → Prop) (a : ℕ → ℤ)
    (𝔪' : Ideal (integralClosure ℤ ℂ)) (h𝔪' : 𝔪'.IsPrime) (hp𝔪' : (p : integralClosure ℤ ℂ) ∈ 𝔪')
    (α : ℕ → integralClosure ℤ ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) (hf : f ≠ 0)
    (heigen : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N), Q ℓ →
      CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f = ((α ℓ : integralClosure ℤ ℂ) : ℂ) • f)
    (hcong : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N → Q ℓ → α ℓ - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪') :
    ∃ y : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      (¬ ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), y = (p : ℤ) • y') ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N → Q ℓ →
        ∀ T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
              (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n))
                  = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℤ n ℓ) z ∧
                T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) →
          ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), T y - (a ℓ : ℤ) • y = (p : ℤ) • y' := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_eigenform.solution
