/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted for the explicit Dubon Witt series from
Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerIntertwiner/DefectCorrection.lean
at dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. The Apache 2.0 license is retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/

import Dubon2026.PrimeWittSemilinearDefect
import Dubon2026.PrimeWittCoefficientEquation
import Mathlib.RingTheory.PowerSeries.Order
import Dubon2026.PowerSeriesFiniteCoefficientSubstitution

/-! # Actual degreewise correction of the semilinear Witt defect

The proved prime divisibility supplies the integral normalized defect. The
existing unique higher-coefficient solution then determines the monomial
correction that kills its current degree. Its effect is computed on the
actual two substitution expressions, and the pinned one-variable substitution coefficient formula proves that no
unrelated coefficients enter. These are the recursion obligations for the
changed-uniformizer series, then DUB-17's actual auxiliary field and ramified
cyclotomic reciprocity formula on the arithmetic sum-zero route.
-/
namespace Dubon2026
noncomputable section

private theorem exists_primeWittNormalizedDefect
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) :
    ∃ b : WittVector p (AlgebraicClosure (ZMod p)),
      (p : WittVector p (AlgebraicClosure (ZMod p))) * b =
        PowerSeries.coeff m
          (primeWittSemilinearDefect p u H) := by
  have hmem :=
    primeWittSemilinearDefect_coeff_mem_span_p p u H hH m
  rw [Ideal.mem_span_singleton] at hmem
  rcases hmem with ⟨b, hb⟩
  exact ⟨b, hb.symm⟩

private noncomputable def primeWittNormalizedDefect
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) :
    WittVector p (AlgebraicClosure (ZMod p)) :=
  Classical.choose
    (exists_primeWittNormalizedDefect p u H hH m)

private theorem primeWittNormalizedDefect_spec
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) :
    (p : WittVector p (AlgebraicClosure (ZMod p))) *
        primeWittNormalizedDefect p u H hH m =
      PowerSeries.coeff m
        (primeWittSemilinearDefect p u H) :=
  Classical.choose_spec
    (exists_primeWittNormalizedDefect p u H hH m)

/-- The completed multiplicative Lubin--Tate series has order one. -/
theorem primeWittMultiplicativeSeries_order
    (p : ℕ) [Fact p.Prime] :
    (primeWittMultiplicativeSeries p).order = 1 := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · rw [primeWittMultiplicativeSeries_coeff_one]
    exact
      WittVector.p_nonzero p (AlgebraicClosure (ZMod p))
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      primeWittMultiplicativeSeries_constantCoeff p

/-- The degree-`m` coefficient of the `m`-th power of the completed
multiplicative series is `p ^ m`. -/
theorem primeWittMultiplicativeSeries_coeff_pow_self
    (p : ℕ) [Fact p.Prime] (m : ℕ) :
    PowerSeries.coeff m
        ((primeWittMultiplicativeSeries p) ^ m) =
      (p : WittVector p (AlgebraicClosure (ZMod p))) ^ m := by
  let M := primeWittMultiplicativeSeries p
  have hMorder : M.order = 1 :=
    primeWittMultiplicativeSeries_order p
  calc
    PowerSeries.coeff m (M ^ m) =
        PowerSeries.constantCoeff
          (PowerSeries.divXPowOrder (M ^ m)) := by
      rw [PowerSeries.constantCoeff_divXPowOrder,
        PowerSeries.order_pow, hMorder]
      simp
    _ =
        PowerSeries.constantCoeff
          ((PowerSeries.divXPowOrder M) ^ m) := by
      rw [PowerSeries.divXPowOrder_pow]
    _ =
        (PowerSeries.constantCoeff
          (PowerSeries.divXPowOrder M)) ^ m := by
      exact map_pow PowerSeries.constantCoeff _ _
    _ = (PowerSeries.coeff 1 M) ^ m := by
      rw [PowerSeries.constantCoeff_divXPowOrder, hMorder]
      rfl
    _ = (p : WittVector p (AlgebraicClosure (ZMod p))) ^ m := by
      rw [primeWittMultiplicativeSeries_coeff_one]

private theorem primeWitt_coeff_pow_add_monomial
    (p : ℕ) [Fact p.Prime]
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m)
    (c : WittVector p (AlgebraicClosure (ZMod p))) :
    PowerSeries.coeff m
        ((H + PowerSeries.monomial m c) ^ p) =
      PowerSeries.coeff m (H ^ p) := by
  let N := PowerSeries.monomial m c
  let A := H + N
  have hm0 : m ≠ 0 := by omega
  have hNconstant : PowerSeries.constantCoeff N = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_monomial, if_neg (Ne.symm hm0)]
  have hAconstant : PowerSeries.constantCoeff A = 0 := by
    simp [A, hH, hNconstant]
  let Q :=
    ∑ i ∈ Finset.range p, A ^ i * H ^ (p - 1 - i)
  have hQ :
      ((p - 1 : ℕ) : ℕ∞) ≤ Q.order := by
    classical
    have hterm : ∀ i ∈ Finset.range p,
        ((p - 1 : ℕ) : ℕ∞) ≤
          (A ^ i * H ^ (p - 1 - i)).order := by
      intro i hi
      have hi' : i < p := Finset.mem_range.mp hi
      calc
        ((p - 1 : ℕ) : ℕ∞) =
            (i : ℕ∞) + ((p - 1 - i : ℕ) : ℕ∞) := by
          norm_cast
          omega
        _ ≤ (A ^ i).order + (H ^ (p - 1 - i)).order :=
          add_le_add
            (PowerSeries.le_order_pow_of_constantCoeff_eq_zero
              i hAconstant)
            (PowerSeries.le_order_pow_of_constantCoeff_eq_zero
              (p - 1 - i) hH)
        _ ≤ (A ^ i * H ^ (p - 1 - i)).order :=
          PowerSeries.le_order_mul _ _
    have hsum (s : Finset ℕ)
        (hs : ∀ i ∈ s,
          ((p - 1 : ℕ) : ℕ∞) ≤
            (A ^ i * H ^ (p - 1 - i)).order) :
        ((p - 1 : ℕ) : ℕ∞) ≤
          (∑ i ∈ s, A ^ i * H ^ (p - 1 - i)).order := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.sum_insert hi]
          exact
            (le_min
              (hs i (Finset.mem_insert_self i s))
              (ih fun j hj =>
                hs j (Finset.mem_insert_of_mem hj))).trans
            (PowerSeries.min_order_le_order_add _ _)
    simpa only [Q] using hsum (Finset.range p) hterm
  have hNorder : (m : ℕ∞) ≤ N.order := by
    apply PowerSeries.nat_le_order
    intro i hi
    rw [PowerSeries.coeff_monomial, if_neg]
    exact Nat.ne_of_lt hi
  have hfactor :
      (A - H) * Q = A ^ p - H ^ p := by
    exact (Commute.all A H).mul_geom_sum₂ p
  have horder :
      ((m + (p - 1) : ℕ) : ℕ∞) ≤
        (A ^ p - H ^ p).order := by
    calc
      ((m + (p - 1) : ℕ) : ℕ∞) =
          (m : ℕ∞) + ((p - 1 : ℕ) : ℕ∞) := by
        norm_cast
      _ ≤ (A - H).order + Q.order := by
        apply add_le_add
        · simpa [A, N] using hNorder
        · exact hQ
      _ ≤ ((A - H) * Q).order :=
        PowerSeries.le_order_mul _ _
      _ = (A ^ p - H ^ p).order := by
        rw [hfactor]
  have hpTwo : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hltNat : m < m + (p - 1) := by omega
  have hlt :
      (m : ℕ∞) < (A ^ p - H ^ p).order := by
    have hcast :
        (m : ℕ∞) < ((m + (p - 1) : ℕ) : ℕ∞) := by
      exact_mod_cast hltNat
    exact hcast.trans_le horder
  have hcoeff :=
    PowerSeries.coeff_of_lt_order m hlt
  rw [map_sub, sub_eq_zero] at hcoeff
  exact hcoeff

/-- Substituting the completed multiplicative series into a monomial scales
its `m`-th power by the monomial coefficient. -/
theorem primeWitt_subst_monomial
    (p : ℕ) [Fact p.Prime]
    (m : ℕ) (c : WittVector p (AlgebraicClosure (ZMod p))) :
    PowerSeries.subst
        (primeWittMultiplicativeSeries p)
        (PowerSeries.monomial m c) =
      PowerSeries.C c *
        (primeWittMultiplicativeSeries p) ^ m := by
  have hM :
      PowerSeries.HasSubst (primeWittMultiplicativeSeries p) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (primeWittMultiplicativeSeries_constantCoeff p)
  rw [PowerSeries.monomial_eq_C_mul_X_pow,
    PowerSeries.subst_mul hM,
    PowerSeries.subst_C,
    PowerSeries.subst_pow hM,
    PowerSeries.subst_X hM]
  rfl

private theorem
    primeWittFrobenius_add_monomial
    (p : ℕ) [Fact p.Prime]
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (m : ℕ) (c : WittVector p (AlgebraicClosure (ZMod p))) :
    PowerSeries.map WittVector.frobenius
        (H + PowerSeries.monomial m c) =
      PowerSeries.map WittVector.frobenius H +
        PowerSeries.monomial m (WittVector.frobenius c) := by
  apply PowerSeries.ext
  intro i
  by_cases hi : i = m
  · subst i
    simp [PowerSeries.coeff_map]
  · simp [PowerSeries.coeff_map, PowerSeries.coeff_monomial, hi]

private theorem primeWitt_coeff_subst_frobenius_add_monomial
    (p : ℕ) [Fact p.Prime]
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (m : ℕ) (c : WittVector p (AlgebraicClosure (ZMod p))) :
    PowerSeries.coeff m
        (PowerSeries.subst
          (primeWittMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius
            (H + PowerSeries.monomial m c))) =
      PowerSeries.coeff m
          (PowerSeries.subst
            (primeWittMultiplicativeSeries p)
            (PowerSeries.map WittVector.frobenius H)) +
        (p : WittVector p (AlgebraicClosure (ZMod p))) ^ m *
          WittVector.frobenius c := by
  have hM :
      PowerSeries.HasSubst (primeWittMultiplicativeSeries p) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (primeWittMultiplicativeSeries_constantCoeff p)
  rw [primeWittFrobenius_add_monomial,
    PowerSeries.subst_add hM, map_add,
    primeWitt_subst_monomial,
    PowerSeries.coeff_C_mul,
    primeWittMultiplicativeSeries_coeff_pow_self]
  ring

private theorem primeWitt_coeff_subst_changed_add_monomial
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m)
    (c : WittVector p (AlgebraicClosure (ZMod p))) :
    PowerSeries.coeff m
        (PowerSeries.subst
          (H + PowerSeries.monomial m c)
          (primeWittChangedSeries p u)) =
      PowerSeries.coeff m
          (PowerSeries.subst H
            (primeWittChangedSeries p u)) +
        ((u) :
            WittVector p (AlgebraicClosure (ZMod p))) *
          (p : WittVector p (AlgebraicClosure (ZMod p))) * c := by
  let a : WittVector p (AlgebraicClosure (ZMod p)) :=
    (u :
      WittVector p (AlgebraicClosure (ZMod p))) * (p : WittVector p (AlgebraicClosure (ZMod p)))
  let N := PowerSeries.monomial m c
  let A := H + N
  have hHsubst : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hH
  have hm0 : m ≠ 0 := by omega
  have hNconstant : PowerSeries.constantCoeff N = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_monomial, if_neg (Ne.symm hm0)]
  have hAsubst : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      change PowerSeries.constantCoeff H +
          PowerSeries.constantCoeff N = 0
      rw [hH, hNconstant, zero_add])
  rw [primeWittChangedSeries,
    PowerSeries.subst_add hAsubst,
    PowerSeries.subst_mul hAsubst,
    PowerSeries.subst_C,
    PowerSeries.subst_X hAsubst,
    PowerSeries.subst_pow hAsubst,
    PowerSeries.subst_X hAsubst,
    PowerSeries.subst_add hHsubst,
    PowerSeries.subst_mul hHsubst,
    PowerSeries.subst_C,
    PowerSeries.subst_X hHsubst,
    PowerSeries.subst_pow hHsubst,
    PowerSeries.subst_X hHsubst]
  change
    PowerSeries.coeff m (PowerSeries.C a * A + A ^ p) =
      PowerSeries.coeff m (PowerSeries.C a * H + H ^ p) + a * c
  rw [map_add, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul]
  change
    a * PowerSeries.coeff m A + PowerSeries.coeff m (A ^ p) =
      a * PowerSeries.coeff m H + PowerSeries.coeff m (H ^ p) +
        a * c
  rw [show PowerSeries.coeff m A =
      PowerSeries.coeff m H + c by
    simp [A, N],
    primeWitt_coeff_pow_add_monomial p H hH m hm c]
  ring

/-- Adding a monomial in degree `m` changes the degree-`m` defect by the
explicit Frobenius-linear correction term. -/
theorem primeWittSemilinearDefect_coeff_add_monomial
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m)
    (c : WittVector p (AlgebraicClosure (ZMod p))) :
    PowerSeries.coeff m
        (primeWittSemilinearDefect p u
          (H + PowerSeries.monomial m c)) =
      PowerSeries.coeff m
          (primeWittSemilinearDefect p u H) +
        (p : WittVector p (AlgebraicClosure (ZMod p))) ^ m *
          WittVector.frobenius c -
        ((u) :
            WittVector p (AlgebraicClosure (ZMod p))) *
          (p : WittVector p (AlgebraicClosure (ZMod p))) * c := by
  rw [primeWittSemilinearDefect, map_sub,
    primeWitt_coeff_subst_frobenius_add_monomial,
    primeWitt_coeff_subst_changed_add_monomial
      p u H hH m hm c]
  rw [primeWittSemilinearDefect, map_sub]
  ring

/-- The unique coefficient that corrects the changed-uniformizer defect in
degree `m`. -/
noncomputable def primeWittCorrectionCoefficient
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m) :
    WittVector p (AlgebraicClosure (ZMod p)) :=
  Classical.choose
    (primeWitt_existsUnique_higher_coefficient p u m hm
      ((↑((u)⁻¹) :
          WittVector p (AlgebraicClosure (ZMod p))) *
        primeWittNormalizedDefect p u H hH m))

/-- The correction coefficient satisfies its defining Frobenius fixed-point
equation. -/
theorem primeWittCorrectionCoefficient_spec
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m) :
    primeWittCorrectionCoefficient p u H hH m hm =
      (↑((u)⁻¹) :
          WittVector p (AlgebraicClosure (ZMod p))) *
        primeWittNormalizedDefect p u H hH m +
      (↑((u)⁻¹) :
          WittVector p (AlgebraicClosure (ZMod p))) *
        (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
        WittVector.frobenius
          (primeWittCorrectionCoefficient
            p u H hH m hm) :=
  (Classical.choose_spec
    (primeWitt_existsUnique_higher_coefficient p u m hm
      ((↑((u)⁻¹) :
          WittVector p (AlgebraicClosure (ZMod p))) *
        primeWittNormalizedDefect p u H hH m))).1

/-- Adding the correction coefficient in degree `m` kills the degree-`m`
defect. -/
theorem primeWittCorrectionCoefficient_kills_defect
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (H : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m) :
    PowerSeries.coeff m
        (primeWittSemilinearDefect p u
          (H + PowerSeries.monomial m
            (primeWittCorrectionCoefficient
              p u H hH m hm))) = 0 := by
  let V : (WittVector p (AlgebraicClosure (ZMod p)))ˣ :=
    u
  let b :=
    primeWittNormalizedDefect p u H hH m
  let c :=
    primeWittCorrectionCoefficient p u H hH m hm
  rw [primeWittSemilinearDefect_coeff_add_monomial
    p u H hH m hm c,
    ← primeWittNormalizedDefect_spec p u H hH m]
  have hc :=
    primeWittCorrectionCoefficient_spec
      p u H hH m hm
  change c =
      (↑(V⁻¹) : WittVector p (AlgebraicClosure (ZMod p))) * b +
        (↑(V⁻¹) : WittVector p (AlgebraicClosure (ZMod p))) *
          (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
          WittVector.frobenius c at hc
  have hc' :
      (V : WittVector p (AlgebraicClosure (ZMod p))) * c =
        b + (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
          WittVector.frobenius c := by
    calc
      (V : WittVector p (AlgebraicClosure (ZMod p))) * c =
          (V : WittVector p (AlgebraicClosure (ZMod p))) *
            ((↑(V⁻¹) : WittVector p (AlgebraicClosure (ZMod p))) * b +
                (↑(V⁻¹) : WittVector p (AlgebraicClosure (ZMod p))) *
                (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
                WittVector.frobenius c) :=
        congrArg (fun z : WittVector p (AlgebraicClosure (ZMod p)) =>
          (V : WittVector p (AlgebraicClosure (ZMod p))) * z) hc
      _ = b + (p : WittVector p (AlgebraicClosure (ZMod p))) ^ (m - 1) *
          WittVector.frobenius c := by
        simp [mul_add, mul_assoc]
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
  rw [show
      (V : WittVector p (AlgebraicClosure (ZMod p))) *
          (p : WittVector p (AlgebraicClosure (ZMod p))) * c =
        (p : WittVector p (AlgebraicClosure (ZMod p))) *
          ((V : WittVector p (AlgebraicClosure (ZMod p))) * c) by ring,
    hc', hpow]
  ring

/-- The degree-`m` defect depends only on coefficients through degree `m`. -/
theorem primeWittSemilinearDefect_coeff_eq_of_coeff_eq_le
    (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    {H H' : PowerSeries (WittVector p (AlgebraicClosure (ZMod p)))}
    (hH : PowerSeries.constantCoeff H = 0)
    (hH' : PowerSeries.constantCoeff H' = 0)
    (m : ℕ)
    (hcoeff : ∀ q : ℕ, q ≤ m →
      PowerSeries.coeff q H = PowerSeries.coeff q H') :
    PowerSeries.coeff m
        (primeWittSemilinearDefect p u H) =
      PowerSeries.coeff m
        (primeWittSemilinearDefect p u H') := by
  unfold primeWittSemilinearDefect
  rw [map_sub, map_sub]
  apply congrArg₂ (fun (a b : WittVector p (AlgebraicClosure (ZMod p))) => a - b)
  · apply powerSeries_coeff_subst_eq_of_coeff_eq_le
      (primeWittMultiplicativeSeries_constantCoeff p)
      (primeWittMultiplicativeSeries_constantCoeff p) m
    · intro q hq
      simp only [PowerSeries.coeff_map, hcoeff q hq]
    · intro q _
      rfl
  · exact powerSeries_coeff_subst_eq_of_coeff_eq_le hH hH' m (fun _ _ => rfl) hcoeff

end
end Dubon2026
