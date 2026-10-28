import Definitions.Def_CohCarrier_Level
import Definitions.Def_Gamma0HeckeOperatorHom
import Theorems.Thm_HeckeEis_coresHom_eq_transfer
import P2M.Util
namespace P2MW.S_CohCarrier_heckeT_top_apply_eq_heckeOperatorHom

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace ESBridge

variable {A : Type*} [AddCommGroup A]

noncomputable def genOp (Γ : Subgroup SL(2, ℤ)) (K : Subgroup ↥Γ) [K.FiniteIndex]
    (c : ↥K →* ↥Γ) (φ : Additive ↥Γ →+ A) : Additive ↥Γ →+ A :=
  MonoidHom.toAdditiveLeft
    (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp c))

theorem genOp_transport {Γ Γ' : Subgroup SL(2, ℤ)} (h : Γ = Γ')
    (K : Subgroup ↥Γ) (K' : Subgroup ↥Γ') [K.FiniteIndex] [K'.FiniteIndex]
    (c : ↥K →* ↥Γ) (c' : ↥K' →* ↥Γ')
    (φ : Additive ↥Γ →+ A) (ψ : Additive ↥Γ' →+ A)
    (hK : ∀ γ : ↥Γ, γ ∈ K ↔ (⟨(γ : SL(2, ℤ)), h ▸ γ.2⟩ : ↥Γ') ∈ K')
    (hc : ∀ (γ : ↥Γ) (hγ : γ ∈ K),
      ((c ⟨γ, hγ⟩ : ↥Γ) : SL(2, ℤ)) =
        ((c' ⟨⟨(γ : SL(2, ℤ)), h ▸ γ.2⟩, (hK γ).mp hγ⟩ : ↥Γ') : SL(2, ℤ)))
    (hφψ : ∀ γ : ↥Γ, φ (Additive.ofMul γ) = ψ (Additive.ofMul ⟨(γ : SL(2, ℤ)), h ▸ γ.2⟩))
    (γ : ↥Γ) :
    genOp Γ K c φ (Additive.ofMul γ) =
      genOp Γ' K' c' ψ (Additive.ofMul ⟨(γ : SL(2, ℤ)), h ▸ γ.2⟩) := by
  subst h
  have hKK' : K = K' := by
    ext γ
    exact hK γ
  subst hKK'
  have hcc' : c = c' := by
    refine MonoidHom.ext fun x => Subtype.ext ?_
    exact hc x.1 x.2
  subst hcc'
  have hφψ' : φ = ψ := by
    refine AddMonoidHom.ext fun x => ?_
    exact hφψ (Additive.toMul x)
  subst hφψ'
  rfl

theorem heckeT_eq_genOp (N ℓ : ℕ) [NeZero ℓ] (φ : CohCarrier.H1 N ⊤ A) :
    CohCarrier.heckeT N ⊤ ℓ A φ =
      genOp (CohCarrier.GammaH N ⊤) (CohCarrier.GammaHUpper N ⊤ ℓ) (CohCarrier.conjL N ⊤ ℓ) φ :=
  rfl

theorem heckeOperatorHom_eq_genOp (N ℓ : ℕ) [NeZero ℓ] (ψ : Additive ↥(Gamma0 N) →+ A) :
    HeckeEis.heckeOperatorHom N ℓ A ψ =
      genOp (Gamma0 N) (HeckeEis.heckeUpper N ℓ) (HeckeEis.heckeConj N ℓ) ψ := by
  show HeckeEis.coresHom (HeckeEis.heckeUpper N ℓ)
      (HeckeEis.pullbackHom (HeckeEis.heckeConj N ℓ) ψ) = _
  rw [HeckeEis.coresHom_eq_transfer]
  rfl

end ESBridge

open ESBridge in
theorem solution (N ℓ : ℕ) [NeZero ℓ]
    (A : Type*) [AddCommGroup A]
    (φ : CohCarrier.H1 N ⊤ A) (ψ : Additive ↥(CongruenceSubgroup.Gamma0 N) →+ A)
    (hφψ : ∀ γ : ↥(CohCarrier.GammaH N ⊤),
      φ (Additive.ofMul γ) =
        ψ (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩))
    (γ : ↥(CohCarrier.GammaH N ⊤)) :
    CohCarrier.heckeT N ⊤ ℓ A φ (Additive.ofMul γ) =
      HeckeEis.heckeOperatorHom N ℓ A ψ
        (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) := by
  rw [heckeT_eq_genOp, heckeOperatorHom_eq_genOp]
  refine genOp_transport CohCarrier.GammaH_top _ _ _ _ φ ψ ?_ ?_ hφψ γ
  · intro δ
    rw [Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper, HeckeEis.mem_heckeUpper,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  · intro δ hδ
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
