import Definitions.Def_Gamma0HeckeOperatorHom
import Mathlib.GroupTheory.Transfer
import P2M.Util
namespace P2MW.S_HeckeEis_coresHom_eq_transfer

set_option autoImplicit false

namespace INH
namespace SolB0

open Subgroup Subgroup.leftTransversals

variable {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
variable {A : Type*} [AddCommGroup A]

omit [H.FiniteIndex] in

theorem default_leftQuotientEquiv_apply (q : G ⧸ H) :
    ((default : H.LeftTransversal).2.leftQuotientEquiv q : G) = q.out :=
  IsComplement.leftQuotientEquiv_apply Quotient.out_eq' q

omit [H.FiniteIndex] in

theorem smul_default_leftQuotientEquiv_apply (g : G) (q : G ⧸ H) :
    ((g • (default : H.LeftTransversal)).2.leftQuotientEquiv q : G) = g * (g⁻¹ • q).out := by
  rw [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  congr 1
  exact default_leftQuotientEquiv_apply H (g⁻¹ • q)

theorem solution_aux (φ : Additive ↥H →+ A) :
    HeckeEis.coresHom (H := H) φ
      = MonoidHom.toAdditiveLeft
          (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)) := by
  letI := H.fintypeQuotientOfFiniteIndex
  ext g
  set g' := Additive.toMul g

  show (∑ q : G ⧸ H, φ (Additive.ofMul (HeckeEis.transferAux H g' q)))
    = Multiplicative.toAdd
        (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ) g')

  rw [MonoidHom.transfer_def (AddMonoidHom.toMultiplicativeRight φ) (g'⁻¹ • default),
    smul_inv_smul]
  unfold Subgroup.leftTransversals.diff
  simp only [toAdd_prod, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  refine Finset.sum_congr rfl (fun q _ => congr_arg φ (congr_arg Additive.ofMul (Subtype.ext ?_)))
  simp only [HeckeEis.coe_transferAux, default_leftQuotientEquiv_apply,
    smul_default_leftQuotientEquiv_apply, inv_inv, mul_inv_rev, mul_assoc]

end INH.SolB0

theorem solution {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    {A : Type*} [AddCommGroup A] (φ : Additive ↥H →+ A) :
    HeckeEis.coresHom (H := H) φ
      = MonoidHom.toAdditiveLeft
          (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)) :=
  INH.SolB0.solution_aux H φ

#print axioms solution
