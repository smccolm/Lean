import Mathlib
import P2M.Util
namespace P2MW.S_Subalgebra_isIntegrallyClosed_adjoin_singleton_of_transcendental

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial

theorem solution
    {L : Type*} [Field L] {F : Type*} [CommRing F] [IsDomain F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) :
    IsIntegrallyClosed (Algebra.adjoin L ({x} : Set F)) := by
  classical

  have hinj : Function.Injective (Polynomial.aeval (R := L) x) :=
    transcendental_iff_injective.mp hxL
  have hrange : (Polynomial.aeval (R := L) x).range = Algebra.adjoin L ({x} : Set F) :=
    (Algebra.adjoin_singleton_eq_range_aeval L x).symm
  let e : Polynomial L ≃ₐ[L] Algebra.adjoin L ({x} : Set F) :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := L) x) hinj).trans
      (Subalgebra.equivOfEq _ _ hrange)

  haveI : IsPrincipalIdealRing (Algebra.adjoin L ({x} : Set F)) := by
    constructor
    intro I

    obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal (I.comap e.toRingHom)
    refine ⟨e a, ?_⟩
    show I = Ideal.span {e a}
    rw [← Ideal.map_comap_of_surjective e.toRingHom e.surjective I,
      show Ideal.comap e.toRingHom I = Ideal.span {a} from ha,
      Ideal.map_span, Set.image_singleton]
    rfl

  infer_instance
