import Dubon2026.SourceEllipticClassLocalRegular
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Actual elliptic coordinate-ring normality for the odd quotient map.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The direct local-principal-ideal
argument meets the algebraically closed source contract in all characteristics.
Reuse the actual point-ideal classification; defer arbitrary-field normality.
This discharges the coordinate-ring input to the norm-induced odd quotient map,
needed by cyclic modular-polynomial roots, inertia census, reverse genus and
good reduction on the DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 chain. -/
namespace Dubon2026.SourceEllipticClassGroup
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing IsLocalRing
open scoped Polynomial.Bivariate
noncomputable section
variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F}
theorem exists_eq_XYIdeal_of_isMaximal [IsAlgClosed F]
    (I : Ideal W.CoordinateRing) [I.IsMaximal] :
    ∃ x y : F, W.Equation x y ∧ I = XYIdeal W x (C y) := by
  letI := Ideal.Quotient.field I
  have : Module.Finite F (W.CoordinateRing ⧸ I) :=
    finite_of_finite_type_of_isJacobsonRing F _
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F)
    (K := W.CoordinateRing ⧸ I)
  exact finrank_quotient_eq_one_iff.mp
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr hbij)

theorem isDiscreteValuationRing_localization_XYIdeal' {x y : F} (h : W.Nonsingular x y)
    [(XYIdeal W x (C y)).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (XYIdeal W x (C y))) := by
  have hnf := IsLocalization.AtPrime.not_isField W.CoordinateRing (XYIdeal_ne_bot x (C y))
    (Localization.AtPrime (XYIdeal W x (C y)))
  haveI : IsNoetherianRing (Localization.AtPrime (XYIdeal W x (C y))) :=
    IsLocalization.isNoetherianRing (XYIdeal W x (C y)).primeCompl _ inferInstance
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 4).mpr
    (isPrincipal_maximalIdeal_localization h)


theorem isMaximal_of_isPrime_of_ne_bot (P : Ideal W.CoordinateRing) [P.IsPrime] (hP : P ≠ ⊥) :
    P.IsMaximal :=
by
  letI : Module.Finite F[X] W.CoordinateRing := Module.Finite.of_basis (CoordinateRing.basis W)
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := F[X]) P <|
    IsPrime.to_maximal_ideal (Ideal.under_ne_bot F[X] hP)

theorem isDedekindDomain_of_isAlgClosed' [IsAlgClosed F] [W.IsElliptic] :
    IsDedekindDomain W.CoordinateRing := by
  have : IsDedekindDomainDvr W.CoordinateRing := by
    refine ⟨fun P hP hPp => ?_⟩
    haveI : P.IsMaximal := isMaximal_of_isPrime_of_ne_bot P hP
    obtain ⟨x, y, hxy, rfl⟩ := exists_eq_XYIdeal_of_isMaximal P
    exact isDiscreteValuationRing_localization_XYIdeal' (equation_iff_nonsingular.mp hxy)
  infer_instance


end
end Dubon2026.SourceEllipticClassGroup
