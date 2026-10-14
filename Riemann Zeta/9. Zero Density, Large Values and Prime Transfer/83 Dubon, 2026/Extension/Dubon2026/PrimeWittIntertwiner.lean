/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted for explicit Dubon Witt series from
Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerIntertwiner/IntertwinerConstruction.lean
at dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. Apache 2.0 license retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/

import Dubon2026.PrimeWittDefectCorrection

/-!
# Changed-uniformizer intertwiner construction

This module builds compatible finite-degree approximations, assembles the changed-uniformizer
intertwiner, proves its functional equation, and establishes uniqueness.
This is the exact series needed to construct the auxiliary extension and
Frobenius comparison for DUB-17 ramified cyclotomic reciprocity, then the
principal product, arithmetic invariant sum-zero and global duality.
It does not yet provide the finite extension or its norm calculation.
-/



noncomputable section

namespace Dubon2026



/-- The actual unit coefficient produced by Witt Frobenius rotation. -/
noncomputable def primeWittLinearCoefficient
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    (WittVector p (AlgebraicClosure (ZMod p)))ˣ :=
  (primeWitt_exists_frobenius_unit_rotation p u).choose

/-- Its defining equation is proved by the actual rotation construction. -/
theorem primeWittLinearCoefficient_frobenius
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    WittVector.frobenius (primeWittLinearCoefficient p u : WittVector p (AlgebraicClosure (ZMod p))) =
      (primeWittLinearCoefficient p u : WittVector p (AlgebraicClosure (ZMod p))) * u :=
  (primeWitt_exists_frobenius_unit_rotation p u).choose_spec

private structure PrimeWittApproximation
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) where
  series : PowerSeries (WittVector p (AlgebraicClosure (ZMod p)))
  constantCoeff_eq_zero :
    PowerSeries.constantCoeff series = 0
  coeff_one_eq :
    PowerSeries.coeff 1 series =
      (primeWittLinearCoefficient p u :
        WittVector p (AlgebraicClosure (ZMod p)))

private noncomputable def primeWittApproximation
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    ℕ → PrimeWittApproximation p u
  | 0 =>
      { series :=
          PowerSeries.monomial 1
            (primeWittLinearCoefficient p u :
              WittVector p (AlgebraicClosure (ZMod p)))
        constantCoeff_eq_zero := by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff,
            PowerSeries.coeff_monomial]
          simp
        coeff_one_eq := by simp }
  | n + 1 =>
      let A := primeWittApproximation p u n
      let m := n + 2
      let c :=
        primeWittCorrectionCoefficient
          p u A.series A.constantCoeff_eq_zero m (by omega)
      { series := A.series + PowerSeries.monomial m c
        constantCoeff_eq_zero := by
          rw [map_add, A.constantCoeff_eq_zero,
            ← PowerSeries.coeff_zero_eq_constantCoeff,
            PowerSeries.coeff_monomial]
          simp [m]
        coeff_one_eq := by
          rw [map_add, A.coeff_one_eq,
            PowerSeries.coeff_monomial]
          simp [m] }

private theorem primeWittApproximation_succ
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (n : ℕ) :
    (primeWittApproximation p u (n + 1)).series =
      (primeWittApproximation p u n).series +
        PowerSeries.monomial (n + 2)
          (primeWittCorrectionCoefficient p u
            (primeWittApproximation p u n).series
            (primeWittApproximation p u n).constantCoeff_eq_zero
            (n + 2) (by omega)) :=
  rfl

private theorem
    primeWittApproximation_coeff_succ_eq_of_lt
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (n q : ℕ) (hq : q < n + 2) :
    PowerSeries.coeff q
        (primeWittApproximation p u (n + 1)).series =
      PowerSeries.coeff q
        (primeWittApproximation p u n).series := by
  rw [primeWittApproximation_succ, map_add,
    PowerSeries.coeff_monomial, if_neg (Nat.ne_of_lt hq)]
  exact add_zero _

private theorem primeWittApproximation_coeff_eq_of_le
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (q : ℕ) {a b : ℕ} (hab : a ≤ b)
    (hq : q < a + 2) :
    PowerSeries.coeff q
        (primeWittApproximation p u b).series =
      PowerSeries.coeff q
        (primeWittApproximation p u a).series := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      rw [primeWittApproximation_coeff_succ_eq_of_lt
        p u b q (by omega)]
      exact ih

private theorem
    primeWittApproximation_succ_defect_coeff
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (n : ℕ) :
    PowerSeries.coeff (n + 2)
        (primeWittSemilinearDefect p u
          (primeWittApproximation p u (n + 1)).series) =
      0 := by
  rw [primeWittApproximation_succ]
  exact
    primeWittCorrectionCoefficient_kills_defect
      p u
      (primeWittApproximation p u n).series
      (primeWittApproximation p u n).constantCoeff_eq_zero
      (n + 2) (by omega)

/-- The actual semilinear changed-uniformizer series over the completed
unramified Witt ring. -/
noncomputable def primeWittIntertwiner
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries (WittVector p (AlgebraicClosure (ZMod p))) :=
  PowerSeries.mk fun m =>
    PowerSeries.coeff m
      (primeWittApproximation p u m).series

private theorem primeWittIntertwiner_coeff
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (m : ℕ) :
    PowerSeries.coeff m
        (primeWittIntertwiner p u) =
      PowerSeries.coeff m
        (primeWittApproximation p u m).series := by
  simp [primeWittIntertwiner]

theorem primeWittIntertwiner_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.constantCoeff
        (primeWittIntertwiner p u) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff,
    primeWittIntertwiner_coeff]
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
    (primeWittApproximation p u 0).constantCoeff_eq_zero

@[simp]
theorem primeWittIntertwiner_coeff_one
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.coeff 1
        (primeWittIntertwiner p u) =
      (primeWittLinearCoefficient p u :
        WittVector p (AlgebraicClosure (ZMod p))) := by
  rw [primeWittIntertwiner_coeff]
  exact
    (primeWittApproximation p u 1).coeff_one_eq

theorem primeWittIntertwiner_hasSubst
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.HasSubst
      (primeWittIntertwiner p u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (primeWittIntertwiner_constantCoeff p u)

private theorem primeWittIntertwiner_coeff_eq_approximation
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (q a : ℕ) (hq : q < a + 2) :
    PowerSeries.coeff q
        (primeWittIntertwiner p u) =
      PowerSeries.coeff q
        (primeWittApproximation p u a).series := by
  rw [primeWittIntertwiner_coeff]
  by_cases hqa : q ≤ a
  · exact
      (primeWittApproximation_coeff_eq_of_le
        p u q (a := q) (b := a) hqa (by omega)).symm
  · have haq : a + 1 = q := by omega
    subst q
    rw [primeWittApproximation_coeff_succ_eq_of_lt
      p u a (a + 1) (by omega)]

private theorem primeWittSemilinearDefect_coeff_zero
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.coeff 0
        (primeWittSemilinearDefect p u
          (primeWittIntertwiner p u)) = 0 := by
  let H := primeWittIntertwiner p u
  have hH := primeWittIntertwiner_constantCoeff p u
  have hM := primeWittMultiplicativeSeries_constantCoeff p
  have hE := primeWittChangedSeries_constantCoeff p u
  have hΦ :
      PowerSeries.constantCoeff
          (PowerSeries.map WittVector.frobenius H) = 0 :=
    by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hH, map_zero]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    primeWittSemilinearDefect, map_sub]
  change
    MvPowerSeries.constantCoeff
        (PowerSeries.subst
          (primeWittMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius H)) -
      MvPowerSeries.constantCoeff
        (PowerSeries.subst H
          (primeWittChangedSeries p u)) = 0
  rw [PowerSeries.constantCoeff_subst_eq_zero hM
      (PowerSeries.map WittVector.frobenius H) hΦ,
    PowerSeries.constantCoeff_subst_eq_zero hH
      (primeWittChangedSeries p u) hE,
    sub_zero]

private theorem primeWittSemilinearDefect_coeff_one
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.coeff 1
        (primeWittSemilinearDefect p u
          (primeWittIntertwiner p u)) = 0 := by
  let ε : WittVector p (AlgebraicClosure (ZMod p)) :=
    (primeWittLinearCoefficient p u :
      WittVector p (AlgebraicClosure (ZMod p)))
  let V : (WittVector p (AlgebraicClosure (ZMod p)))ˣ :=
    u
  let H := primeWittIntertwiner p u
  have hH := primeWittIntertwiner_constantCoeff p u
  have hcoeff :=
    primeWittIntertwiner_coeff_one p u
  have hlinear :=
    primeWittLinearCoefficient_frobenius p u
  have hcongr :
      PowerSeries.coeff 1
          (primeWittSemilinearDefect p u H) =
        PowerSeries.coeff 1
          (primeWittSemilinearDefect p u
            (PowerSeries.monomial 1 ε)) := by
    apply primeWittSemilinearDefect_coeff_eq_of_coeff_eq_le
      p u hH
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_monomial]
      simp
    · intro q hq
      interval_cases q
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hH,
          PowerSeries.coeff_monomial]
        simp
      · rw [PowerSeries.coeff_monomial, if_pos rfl]
        exact hcoeff
  let P : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))) :=
    PowerSeries.monomial 1 ε
  have hPconstant : PowerSeries.constantCoeff P = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_monomial]
    simp
  have hPsubst : PowerSeries.HasSubst P :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hPconstant
  have hΦP :
      PowerSeries.map WittVector.frobenius P =
        PowerSeries.monomial 1 (WittVector.frobenius ε) := by
    apply PowerSeries.ext
    intro q
    rw [PowerSeries.coeff_map]
    change
      WittVector.frobenius
          (PowerSeries.coeff q (PowerSeries.monomial 1 ε)) =
        PowerSeries.coeff q
          (PowerSeries.monomial 1 (WittVector.frobenius ε))
    rw [PowerSeries.coeff_monomial, PowerSeries.coeff_monomial]
    by_cases hq : q = 1
    · simp [hq]
    · simp [hq]
  have hright :
      PowerSeries.coeff 1
          (PowerSeries.subst (primeWittMultiplicativeSeries p)
            (PowerSeries.map WittVector.frobenius P)) =
        WittVector.frobenius ε * (p : WittVector p (AlgebraicClosure (ZMod p))) := by
    rw [hΦP, primeWitt_subst_monomial,
      PowerSeries.coeff_C_mul,
      primeWittMultiplicativeSeries_coeff_pow_self]
    simp
  have hleft :
      PowerSeries.coeff 1
          (PowerSeries.subst P
            (primeWittChangedSeries p u)) =
        ((V : WittVector p (AlgebraicClosure (ZMod p))) * (p : WittVector p (AlgebraicClosure (ZMod p)))) * ε := by
    rw [primeWittChangedSeries,
      PowerSeries.subst_add hPsubst,
      PowerSeries.subst_mul hPsubst,
      PowerSeries.subst_C,
      PowerSeries.subst_X hPsubst,
      PowerSeries.subst_pow hPsubst,
      PowerSeries.subst_X hPsubst,
      map_add]
    change
      PowerSeries.coeff 1
          (PowerSeries.C
              ((V : WittVector p (AlgebraicClosure (ZMod p))) *
                (p : WittVector p (AlgebraicClosure (ZMod p)))) * P) +
        PowerSeries.coeff 1 (P ^ p) =
      (V : WittVector p (AlgebraicClosure (ZMod p))) * (p : WittVector p (AlgebraicClosure (ZMod p))) * ε
    rw [PowerSeries.coeff_C_mul]
    have hpOne : 1 ≠ p := (Fact.out : p.Prime).one_lt.ne
    have hpOneMul : 1 ≠ p * 1 := by
      simpa only [mul_one] using hpOne
    rw [show P = PowerSeries.monomial 1 ε from rfl,
      PowerSeries.coeff_monomial, if_pos rfl,
      PowerSeries.monomial_pow, PowerSeries.coeff_monomial,
      if_neg hpOneMul]
    ring
  rw [hcongr, primeWittSemilinearDefect, map_sub,
    hright, hleft]
  change WittVector.frobenius ε * (p : WittVector p (AlgebraicClosure (ZMod p))) -
      ((V : WittVector p (AlgebraicClosure (ZMod p))) * (p : WittVector p (AlgebraicClosure (ZMod p)))) * ε = 0
  change WittVector.frobenius ε = ε * (V : WittVector p (AlgebraicClosure (ZMod p))) at hlinear
  rw [hlinear]
  ring

private theorem primeWittSemilinearDefect_coeff_succ_succ
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (n : ℕ) :
    PowerSeries.coeff (n + 2)
        (primeWittSemilinearDefect p u
          (primeWittIntertwiner p u)) = 0 := by
  let H := primeWittIntertwiner p u
  let A := primeWittApproximation p u (n + 1)
  calc
    PowerSeries.coeff (n + 2)
        (primeWittSemilinearDefect p u H) =
        PowerSeries.coeff (n + 2)
          (primeWittSemilinearDefect p u A.series) := by
      apply primeWittSemilinearDefect_coeff_eq_of_coeff_eq_le
        p u
        (primeWittIntertwiner_constantCoeff p u)
        A.constantCoeff_eq_zero
      intro q hq
      exact
        primeWittIntertwiner_coeff_eq_approximation
          p u q (n + 1) (by omega)
    _ = 0 :=
      primeWittApproximation_succ_defect_coeff p u n

/-- The completed changed standard series after the actual intertwiner is
the Frobenius transform of the intertwiner after the multiplicative
series. This is the first changed-uniformizer identity. -/
theorem primeWittIntertwiner_functionalEquation
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.subst (primeWittIntertwiner p u) (primeWittChangedSeries p u) =
      PowerSeries.subst (primeWittMultiplicativeSeries p)
        (PowerSeries.map WittVector.frobenius (primeWittIntertwiner p u)) := by
  rw [← sub_eq_zero]
  apply PowerSeries.ext
  intro m
  rw [map_sub, map_zero]
  have hrewrite :
      PowerSeries.coeff m
            (PowerSeries.subst
              (primeWittIntertwiner p u)
              (primeWittChangedSeries p u)) -
          PowerSeries.coeff m
            (PowerSeries.subst
              (primeWittMultiplicativeSeries p)
              (PowerSeries.map WittVector.frobenius
                (primeWittIntertwiner p u))) =
        -PowerSeries.coeff m
          (primeWittSemilinearDefect p u
            (primeWittIntertwiner p u)) := by
    unfold primeWittSemilinearDefect
    rw [map_sub]
    ring
  rw [hrewrite]
  cases m with
  | zero =>
      rw [primeWittSemilinearDefect_coeff_zero, neg_zero]
  | succ m =>
      cases m with
      | zero =>
          rw [primeWittSemilinearDefect_coeff_one, neg_zero]
      | succ n =>
          rw [show n + 1 + 1 = n + 2 by omega,
            primeWittSemilinearDefect_coeff_succ_succ, neg_zero]

/-- A zero-constant-coefficient solution of the changed-uniformizer
functional equation is determined by its linear coefficient. -/
theorem primeWittIntertwiner_unique
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    {H H' : PowerSeries (WittVector p (AlgebraicClosure (ZMod p)))}
    (hHconstant : PowerSeries.constantCoeff H = 0)
    (hH'constant : PowerSeries.constantCoeff H' = 0)
    (hlinear :
      PowerSeries.coeff 1 H = PowerSeries.coeff 1 H')
    (hH :
      PowerSeries.subst H
          (primeWittChangedSeries p u) =
        PowerSeries.subst
          (primeWittMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius H))
    (hH' :
      PowerSeries.subst H'
          (primeWittChangedSeries p u) =
        PowerSeries.subst
          (primeWittMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius H')) :
    H = H' := by
  have hHdefect :
      primeWittSemilinearDefect p u H = 0 := by
    rw [primeWittSemilinearDefect, hH, sub_self]
  have hH'defect :
      primeWittSemilinearDefect p u H' = 0 := by
    rw [primeWittSemilinearDefect, hH', sub_self]
  apply PowerSeries.ext
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
          hHconstant, hH'constant]
      by_cases hm1 : m = 1
      · subst m
        exact hlinear
      have hm : 2 ≤ m := by omega
      let c : WittVector p (AlgebraicClosure (ZMod p)) :=
        PowerSeries.coeff m H - PowerSeries.coeff m H'
      let A : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))) :=
        H' + PowerSeries.monomial m c
      have hAconstant : PowerSeries.constantCoeff A = 0 := by
        change PowerSeries.constantCoeff H' +
            PowerSeries.constantCoeff (PowerSeries.monomial m c) = 0
        rw [hH'constant,
          ← PowerSeries.coeff_zero_eq_constantCoeff,
          PowerSeries.coeff_monomial, if_neg (Ne.symm hm0),
          zero_add]
      have hcoeff :
          ∀ q : ℕ, q ≤ m →
            PowerSeries.coeff q H = PowerSeries.coeff q A := by
        intro q hqm
        by_cases hq : q = m
        · subst q
          change PowerSeries.coeff m H =
            PowerSeries.coeff m H' +
              PowerSeries.coeff m (PowerSeries.monomial m c)
          rw [PowerSeries.coeff_monomial, if_pos rfl]
          dsimp only [c]
          ring
        · have hqLt : q < m := lt_of_le_of_ne hqm hq
          change PowerSeries.coeff q H =
            PowerSeries.coeff q H' +
              PowerSeries.coeff q (PowerSeries.monomial m c)
          rw [PowerSeries.coeff_monomial, if_neg hq]
          simp only [add_zero]
          exact ih q hqLt
      have hdefectA :
          PowerSeries.coeff m
              (primeWittSemilinearDefect p u A) =
            0 := by
        calc
          PowerSeries.coeff m
              (primeWittSemilinearDefect p u A) =
              PowerSeries.coeff m
                (primeWittSemilinearDefect p u H) := by
            symm
            exact
              primeWittSemilinearDefect_coeff_eq_of_coeff_eq_le
                p u hHconstant hAconstant m hcoeff
          _ = 0 := by rw [hHdefect, map_zero]
      have hcHomogeneous :
          (p : WittVector p (AlgebraicClosure (ZMod p))) ^ m *
                WittVector.frobenius c -
              ((u) :
                  WittVector p (AlgebraicClosure (ZMod p))) *
                (p : WittVector p (AlgebraicClosure (ZMod p))) * c =
            0 := by
        have hformula :=
          primeWittSemilinearDefect_coeff_add_monomial
            p u H' hH'constant m hm c
        change
          PowerSeries.coeff m
              (primeWittSemilinearDefect p u A) =
            PowerSeries.coeff m
                (primeWittSemilinearDefect p u H') +
              (p : WittVector p (AlgebraicClosure (ZMod p))) ^ m *
                WittVector.frobenius c -
              ((u) :
                  WittVector p (AlgebraicClosure (ZMod p))) *
                (p : WittVector p (AlgebraicClosure (ZMod p))) * c at hformula
        rw [hdefectA, hH'defect, map_zero,
          zero_add] at hformula
        exact hformula.symm
      let V : (WittVector p (AlgebraicClosure (ZMod p)))ˣ :=
        u
      have hpne : (p : WittVector p (AlgebraicClosure (ZMod p))) ≠ 0 :=
        WittVector.p_nonzero p (AlgebraicClosure (ZMod p))
      have hpow :
          (p : WittVector p (AlgebraicClosure (ZMod p))) ^ m =
            (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
              (p : WittVector p (AlgebraicClosure (ZMod p))) := by
        calc
          (p : WittVector p (AlgebraicClosure (ZMod p))) ^ m =
              (p : WittVector p (AlgebraicClosure (ZMod p))) ^ ((m - 1) + 1) := by
            congr 1
            omega
          _ = (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
              (p : WittVector p (AlgebraicClosure (ZMod p))) := by
            rw [pow_succ]
      have hpCancel :
          (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
                WittVector.frobenius c =
            (V : WittVector p (AlgebraicClosure (ZMod p))) * c := by
        apply mul_left_cancel₀ hpne
        have heq := sub_eq_zero.mp hcHomogeneous
        change
          (p : WittVector p (AlgebraicClosure (ZMod p))) *
              ((p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
                WittVector.frobenius c) =
            (p : WittVector p (AlgebraicClosure (ZMod p))) *
              ((V : WittVector p (AlgebraicClosure (ZMod p))) * c)
        calc
          (p : WittVector p (AlgebraicClosure (ZMod p))) *
                ((p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
                  WittVector.frobenius c) =
              (p : WittVector p (AlgebraicClosure (ZMod p))) ^ m *
                WittVector.frobenius c := by
            rw [hpow]
            ring
          _ =
              (V : WittVector p (AlgebraicClosure (ZMod p))) *
                (p : WittVector p (AlgebraicClosure (ZMod p))) * c :=
            heq
          _ =
              (p : WittVector p (AlgebraicClosure (ZMod p))) *
                ((V : WittVector p (AlgebraicClosure (ZMod p))) * c) := by
            ring
      have hcFixed :
          c =
            ((V⁻¹ : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
                WittVector p (AlgebraicClosure (ZMod p))) *
              (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
              WittVector.frobenius c := by
        calc
          c =
              ((V⁻¹ : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
                  WittVector p (AlgebraicClosure (ZMod p))) *
                ((V : WittVector p (AlgebraicClosure (ZMod p))) * c) := by
            simp
          _ =
              ((V⁻¹ : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
                  WittVector p (AlgebraicClosure (ZMod p))) *
                ((p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
                  WittVector.frobenius c) := by
            rw [← hpCancel]
          _ =
              ((V⁻¹ : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
                  WittVector p (AlgebraicClosure (ZMod p))) *
                (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
                WittVector.frobenius c := by
            ring
      have hunique :=
        primeWitt_existsUnique_higher_coefficient p u m hm 0
      have hcSolution :
          c =
            0 +
              ((V⁻¹ : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
                  WittVector p (AlgebraicClosure (ZMod p))) *
                (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
                WittVector.frobenius c := by
        simpa only [zero_add] using hcFixed
      have hzeroSolution :
          (0 : WittVector p (AlgebraicClosure (ZMod p))) =
            0 +
              ((V⁻¹ : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
                  WittVector p (AlgebraicClosure (ZMod p))) *
                (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
                WittVector.frobenius 0 := by
        simp
      have hcZero : c = 0 :=
        hunique.unique hcSolution hzeroSolution
      exact sub_eq_zero.mp (by simpa only [c] using hcZero)

end Dubon2026

end
