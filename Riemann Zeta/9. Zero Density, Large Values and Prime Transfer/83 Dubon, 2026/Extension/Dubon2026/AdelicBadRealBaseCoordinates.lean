import Dubon2026.AdelicBadPlaceFamily
import Dubon2026.AdelicRealFinitePlaceCoordinates
import Dubon2026.AdelicGoodLevelBaseDecomposition

/-! # The actual fixed base is exactly the original real group times the original bad local groups -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable (N : ℕ) [NeZero N]

/-- The genuine finite tuple of all original bad local general-linear groups. -/
abbrev AdelicBadLocalTuple :=
  ∀ i : Fin (Fintype.card (AdelicBadPlace N)), GeneralLinearGroup (Fin 2) ((adelicBadPlaceFamily N i).adicCompletion ℚ)

/-- The actual product of the genuine bad local tuple and the original real group in the original adelic group. -/
def adelicBadRealJointHom : (AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ) →* RationalAdelicGL2 :=
  adelicFiniteRealJointHom (adelicBadPlaceFamily N) (adelicBadPlaceFamily_injective N)

/-- The original bad/real joint action has exactly the prescribed genuine real coordinate. -/
theorem adelicBadRealJointHom_real (a : AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ) :
    (rationalAdelicGL2RealFiniteEquiv (adelicBadRealJointHom N a)).1 = a.2 := by
  change (rationalAdelicGL2RealFiniteEquiv
    (adelicFinitePlaceProduct (adelicBadPlaceFamily N) (adelicBadPlaceFamily_injective N) a.1 *
      adelicRealGL2Embedding a.2)).1 = a.2
  rw [map_mul, Prod.fst_mul, adelicFinitePlaceProduct_real, adelicRealGL2Embedding_coordinates, one_mul]

/-- The original bad/real joint action has exactly the supplied genuine bad local coordinates. -/
theorem adelicBadRealJointHom_place (a : AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ)
    (i : Fin (Fintype.card (AdelicBadPlace N))) :
    adelicPlaceGL2Hom (adelicBadPlaceFamily N i) (adelicBadRealJointHom N a) = a.1 i := by
  change adelicPlaceGL2Hom (adelicBadPlaceFamily N i)
    (adelicFinitePlaceProduct (adelicBadPlaceFamily N) (adelicBadPlaceFamily_injective N) a.1 *
      adelicRealGL2Embedding a.2) = a.1 i
  rw [map_mul, adelicPlaceGL2Hom_finitePlaceProduct, adelicPlaceGL2Hom_real, mul_one]

/-- Every genuine bad/real product lies in the literal original fixed base because all its good coordinates are identity. -/
theorem adelicBadRealJointHom_mem_base (a : AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ) :
    adelicBadRealJointHom N a ∈ adelicRestrictedBaseGroup N := by
  apply (adelicRestrictedBaseGroup_mem_iff N _).mpr
  intro w hw
  change adelicPlaceGL2Hom w
    (adelicFinitePlaceProduct (adelicBadPlaceFamily N) (adelicBadPlaceFamily_injective N) a.1 *
      adelicRealGL2Embedding a.2) = 1
  rw [map_mul, adelicPlaceGL2Hom_real, mul_one]
  exact adelicPlaceGL2Hom_finitePlaceProduct_ne (adelicBadPlaceFamily N) (adelicBadPlaceFamily_injective N)
    w (goodAdelicPlace_ne_badFamily N w hw) a.1

/-- Removing all actual bad coordinates from an original fixed-base matrix leaves precisely its original real embedding. -/
theorem adelicBadRemoval_base_eq_real (b : adelicRestrictedBaseGroup N) :
    adelicFinitePlaceRemoval (adelicBadPlaceFamily N) (adelicBadPlaceFamily_injective N) b.val =
      adelicRealGL2Embedding (rationalAdelicGL2RealFiniteEquiv b.val).1 := by
  apply adelicRealFiniteCoordinates_ext
  · rw [adelicFinitePlaceRemoval_real, adelicRealGL2Embedding_coordinates]
  · intro w
    rw [adelicPlaceGL2Hom_real]
    by_cases hw : IsGoodAdelicPlace N w
    · rw [adelicFinitePlaceRemoval_ne _ _ w (goodAdelicPlace_ne_badFamily N w hw)]
      exact adelicRestrictedBaseGroup_place b w hw
    · obtain ⟨i, rfl⟩ := adelicBadPlaceFamily_surjective_bad N w hw
      exact adelicFinitePlaceRemoval_same (adelicBadPlaceFamily N) (adelicBadPlaceFamily_injective N) i b.val

/-- The genuine bad/real coordinate product reconstructs each original fixed-base matrix exactly. -/
theorem adelicBadRealJointHom_reconstruct (b : adelicRestrictedBaseGroup N) :
    adelicBadRealJointHom N
      (adelicFinitePlaceEvaluation (adelicBadPlaceFamily N) b.val, (rationalAdelicGL2RealFiniteEquiv b.val).1) = b.val := by
  have he := adelicFinitePlaceProduct_mul_removal (adelicBadPlaceFamily N) (adelicBadPlaceFamily_injective N) b.val
  rw [adelicBadRemoval_base_eq_real N b] at he
  exact he

/-- The original joint bad/real group homomorphism with its genuinely proved fixed-base codomain. -/
def adelicBadRealBaseHom :
    (AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ) →* adelicRestrictedBaseGroup N :=
  (adelicBadRealJointHom N).codRestrict (adelicRestrictedBaseGroup N) (adelicBadRealJointHom_mem_base N)

/-- The actual fixed-base group is isomorphic to its genuine finite bad local tuple times its original full real group. -/
def adelicBadRealBaseEquiv :
    (AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ) ≃* adelicRestrictedBaseGroup N where
  toFun := adelicBadRealBaseHom N
  invFun b := (adelicFinitePlaceEvaluation (adelicBadPlaceFamily N) b.val, (rationalAdelicGL2RealFiniteEquiv b.val).1)
  left_inv a := by
    apply Prod.ext
    · funext i
      exact adelicBadRealJointHom_place N a i
    · exact adelicBadRealJointHom_real N a
  right_inv b := Subtype.ext (adelicBadRealJointHom_reconstruct N b)
  map_mul' := map_mul (adelicBadRealBaseHom N)

/-- The genuine fixed-base coordinate equivalence retains the literal original bad/real adelic product. -/
theorem adelicBadRealBaseEquiv_val (a : AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ) :
    (adelicBadRealBaseEquiv N a).val = adelicBadRealJointHom N a := rfl

end
end Dubon2026
