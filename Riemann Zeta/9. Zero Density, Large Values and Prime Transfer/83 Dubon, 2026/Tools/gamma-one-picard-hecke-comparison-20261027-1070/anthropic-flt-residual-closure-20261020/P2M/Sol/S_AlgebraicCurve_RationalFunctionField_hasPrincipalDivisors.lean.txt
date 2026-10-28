import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
import P2M.Util
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) :=
  ⟨fun f hf =>
    ⟨Finsupp.ofSupportFinite (fun v : Place K (RatFunc K) => v.ord f)
        (AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero hf),
      fun _ => rfl,
      AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord _ fun _ => rfl⟩⟩
