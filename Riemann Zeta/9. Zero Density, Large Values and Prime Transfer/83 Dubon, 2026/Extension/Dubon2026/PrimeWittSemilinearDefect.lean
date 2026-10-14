/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted for the explicit Dubon Witt series from
Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerIntertwiner/DefectCorrection.lean
at dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. The Apache 2.0 license is retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/

import Dubon2026.PrimeWittUniformizerSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.WittVector.Complete

/-! # The actual semilinear Witt defect is divisible by the prime

Residue Frobenius and formal substitution show that every coefficient of
H^Frob((1+X)^p-1) - (upH+H^p) is divisible by p when H has zero constant.
This supplies the integral normalized defect for the higher-coefficient
solver, then the changed-uniformizer series and auxiliary field required
by DUB-17's ramified cyclotomic formula and arithmetic invariant sum-zero.
-/
namespace Dubon2026
noncomputable section

/-- The defect of a candidate changed-uniformizer intertwiner: the difference
between its Frobenius-twisted multiplicative substitution and its
changed-standard substitution. -/
noncomputable def primeWittSemilinearDefect
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p)))) :
    PowerSeries (WittVector p (AlgebraicClosure (ZMod p))) :=
  PowerSeries.subst
      (primeWittMultiplicativeSeries p)
      (PowerSeries.map WittVector.frobenius H) -
    PowerSeries.subst H
      (primeWittChangedSeries p u)

/-- Reduction modulo `p` commutes with coefficientwise Witt-vector Frobenius
through residue-field Frobenius. -/
theorem primeWittFrobenius_residue
    (p : ℕ) [Fact p.Prime]
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p)))) :
    PowerSeries.map WittVector.constantCoeff
        (PowerSeries.map WittVector.frobenius H) =
      PowerSeries.map
        (frobenius (AlgebraicClosure (ZMod p)) p)
        (PowerSeries.map WittVector.constantCoeff H) := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_map, WittVector.constantCoeff_apply,
    WittVector.coeff_frobenius_charP, frobenius_def]

/-- The changed-uniformizer defect vanishes after coefficientwise reduction
modulo `p`. -/
theorem primeWittSemilinearDefect_map_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0) :
    PowerSeries.map WittVector.constantCoeff
        (primeWittSemilinearDefect p u H) = 0 := by
  have hM :
      PowerSeries.HasSubst (primeWittMultiplicativeSeries p) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (primeWittMultiplicativeSeries_constantCoeff p)
  have hHsubst : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hH
  have hHbar :
      PowerSeries.HasSubst
        (PowerSeries.map WittVector.constantCoeff H) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      change WittVector.constantCoeff
          (PowerSeries.constantCoeff H) = 0
      rw [hH, map_zero])
  rw [primeWittSemilinearDefect, map_sub]
  change
    MvPowerSeries.map WittVector.constantCoeff
          (PowerSeries.subst (primeWittMultiplicativeSeries p)
            (PowerSeries.map WittVector.frobenius H)) -
        MvPowerSeries.map WittVector.constantCoeff
          (PowerSeries.subst H
            (primeWittChangedSeries p u)) =
      0
  rw [PowerSeries.map_subst hM,
    PowerSeries.map_subst hHsubst]
  change
    PowerSeries.subst
          (PowerSeries.map WittVector.constantCoeff
            (primeWittMultiplicativeSeries p))
          (PowerSeries.map WittVector.constantCoeff
            (PowerSeries.map WittVector.frobenius H)) -
        PowerSeries.subst
          (PowerSeries.map WittVector.constantCoeff H)
          (PowerSeries.map WittVector.constantCoeff
            (primeWittChangedSeries p u)) =
      0
  rw [primeWittMultiplicativeSeries_residue,
    primeWittChangedSeries_residue,
    primeWittFrobenius_residue]
  rw [← PowerSeries.expand_apply, ← PowerSeries.map_expand]
  change
    MvPowerSeries.map
          (frobenius (AlgebraicClosure (ZMod p)) p)
          (MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero
            (PowerSeries.map WittVector.constantCoeff H)) -
        PowerSeries.subst
          (PowerSeries.map WittVector.constantCoeff H)
          (PowerSeries.X ^ p) =
      0
  rw [MvPowerSeries.map_frobenius_expand p
    (Fact.out : p.Prime).ne_zero]
  rw [PowerSeries.subst_pow hHbar,
    PowerSeries.subst_X hHbar]
  exact sub_self _

/-- Every coefficient of the changed-uniformizer defect is divisible by
`p` in the completed unramified Witt ring. -/
theorem primeWittSemilinearDefect_coeff_mem_span_p
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) :
    PowerSeries.coeff m (primeWittSemilinearDefect p u H) ∈
      Ideal.span ({(p : WittVector p (AlgebraicClosure (ZMod p)))} : Set _) := by
  rw [← WittVector.ker_constantCoeff]
  change
    WittVector.constantCoeff
      (PowerSeries.coeff m
        (primeWittSemilinearDefect p u H)) = 0
  rw [← PowerSeries.coeff_map,
    primeWittSemilinearDefect_map_constantCoeff p u H hH,
    map_zero]


end
end Dubon2026
