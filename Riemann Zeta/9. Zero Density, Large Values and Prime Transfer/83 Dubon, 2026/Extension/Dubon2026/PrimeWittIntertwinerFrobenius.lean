/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted from the uniqueness argument in
Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerIntertwiner/ScalarCompatibility.lean
at dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. Apache 2.0 license retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt. General scalar
endomorphisms are replaced by the explicit natural scalar polynomial.
-/
import Dubon2026.PrimeWittNaturalSeries

/-! # Frobenius on the actual intertwiner for natural units

The explicit natural scalar polynomial commutes with the multiplicative
prime polynomial. Uniqueness of the constructed semilinear series then
identifies its actual Frobenius twist. This is the series-level action
needed for DUB-17's auxiliary normed uniformizer and ramified reciprocity.
-/
noncomputable section
namespace Dubon2026

/-- Witt-vector Frobenius on the coefficients of the changed-uniformizer
intertwiner is substitution by the multiplicative endomorphism attached to
the unit changing the uniformizer. -/
theorem primeWittIntertwiner_frobenius_nat
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    PowerSeries.map WittVector.frobenius
        (primeWittIntertwiner p u) =
      PowerSeries.subst
        (primeWittNaturalSeries p a)
        (primeWittIntertwiner p u) := by
  let H := primeWittIntertwiner p u
  let U :=
    primeWittNaturalSeries p a
  let E := primeWittMultiplicativeSeries p
  let Ebar := primeWittChangedSeries p u
  let Phi := PowerSeries.map WittVector.frobenius H
  let Phi2 := PowerSeries.map WittVector.frobenius Phi
  let epsilon : WittVector p (AlgebraicClosure (ZMod p)) :=
    (primeWittLinearCoefficient p u :
      WittVector p (AlgebraicClosure (ZMod p)))
  let alpha : WittVector p (AlgebraicClosure (ZMod p)) :=
    (u :
      WittVector p (AlgebraicClosure (ZMod p)))
  let A := PowerSeries.subst U H
  have hHconstant : PowerSeries.constantCoeff H = 0 := by
    simpa only [H] using
      primeWittIntertwiner_constantCoeff p u
  have hHsubst : PowerSeries.HasSubst H := primeWittIntertwiner_hasSubst p u
  have hUconstant : PowerSeries.constantCoeff U = 0 :=
    primeWittNaturalSeries_constantCoeff p a
  have hUsubst : PowerSeries.HasSubst U :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hUconstant
  have hEsubst : PowerSeries.HasSubst E :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      simpa only [E] using
        primeWittMultiplicativeSeries_constantCoeff p)
  have hHfunctional :
      PowerSeries.subst H Ebar =
        PowerSeries.subst E Phi := by
    simpa only [H, Ebar, E, Phi,
      primeWittChangedSeries,
      primeWittMultiplicativeSeries] using
      primeWittIntertwiner_functionalEquation p u
  have hUcommutes :
      PowerSeries.subst U E =
        PowerSeries.subst E U := by
    exact primeWittNaturalSeries_commutes p a
  have hmapA :
      PowerSeries.map WittVector.frobenius A =
        PowerSeries.subst U Phi := by
    simp only [A, Phi]
    change MvPowerSeries.map _ _ = _
    rw [PowerSeries.map_subst hUsubst]
    change
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) = _
    rw [primeWittNaturalSeries_frobenius]
  have hPhiFunctional :
      PowerSeries.subst Phi Ebar =
        PowerSeries.subst E Phi2 := by
    have h :=
      congrArg (PowerSeries.map WittVector.frobenius) hHfunctional
    change MvPowerSeries.map _ _ = MvPowerSeries.map _ _ at h
    rw [PowerSeries.map_subst hHsubst,
      PowerSeries.map_subst hEsubst] at h
    change
      PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) =
        PowerSeries.subst (PowerSeries.map _ _) (PowerSeries.map _ _) at h
    rw [
      primeWittChangedSeries_frobenius_nat p u a hu,
      show PowerSeries.map WittVector.frobenius E = E from primeWittNaturalSeries_frobenius p p] at h
    simpa only [Phi, Phi2] using h
  have hAfunctional :
      PowerSeries.subst A Ebar =
        PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius A) := by
    calc
      PowerSeries.subst A Ebar =
          PowerSeries.subst U
            (PowerSeries.subst H Ebar) := by
        simpa only [A] using
          (PowerSeries.subst_comp_subst_apply
            hHsubst hUsubst Ebar).symm
      _ = PowerSeries.subst U
            (PowerSeries.subst E Phi) := by
        rw [hHfunctional]
      _ = PowerSeries.subst
            (PowerSeries.subst U E) Phi :=
        PowerSeries.subst_comp_subst_apply
          hEsubst hUsubst Phi
      _ = PowerSeries.subst
            (PowerSeries.subst E U) Phi := by
        rw [hUcommutes]
      _ = PowerSeries.subst E
            (PowerSeries.subst U Phi) :=
        (PowerSeries.subst_comp_subst_apply
          hUsubst hEsubst Phi).symm
      _ = PowerSeries.subst E
            (PowerSeries.map WittVector.frobenius A) := by
        rw [hmapA]
  have hAconstant : PowerSeries.constantCoeff A = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hUconstant H hHconstant
  have hAlinear : PowerSeries.coeff 1 A = epsilon * alpha := by
    rw [powerSeries_coeff_one_subst hHconstant hUconstant]
    rw [show PowerSeries.coeff 1 H = epsilon from primeWittIntertwiner_coeff_one p u,
      show PowerSeries.coeff 1 U = (a : WittVector p (AlgebraicClosure (ZMod p))) from
        primeWittNaturalSeries_coeff_one p a]
    rw [show alpha = (a : WittVector p (AlgebraicClosure (ZMod p))) from hu]
  have hPhiConstant : PowerSeries.constantCoeff Phi = 0 := by
    change PowerSeries.constantCoeff (PowerSeries.map WittVector.frobenius H) = 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hHconstant, map_zero]
  have hPhiLinear :
      PowerSeries.coeff 1 Phi = epsilon * alpha := by
    change
      WittVector.frobenius
          (PowerSeries.coeff 1 H) =
        epsilon * alpha
    rw [show PowerSeries.coeff 1 H = epsilon by
      simpa only [H, epsilon] using
        primeWittIntertwiner_coeff_one p u]
    simpa only [epsilon, alpha] using
      primeWittLinearCoefficient_frobenius p u
  have hPhiFunctional' :
      PowerSeries.subst Phi Ebar =
        PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius Phi) := by
    simpa only [Phi2] using hPhiFunctional
  have hAfunctional' :
      PowerSeries.subst A Ebar =
        PowerSeries.subst E
          (PowerSeries.map WittVector.frobenius A) :=
    hAfunctional
  exact
    primeWittIntertwiner_unique p u
      hPhiConstant
      hAconstant
      (hPhiLinear.trans hAlinear.symm)
      hPhiFunctional' hAfunctional'

end Dubon2026

end
