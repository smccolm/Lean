import RiemannZeta.GuthMaynard.KloostermanExtensionSum
import Mathlib.Algebra.Polynomial.OfFn

open Polynomial
open Classical
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

noncomputable def monicPolynomialOfCoeffs
    (p d : ℕ) [Fact p.Prime] (v : Fin d → ZMod p) : (ZMod p)[X] :=
  X ^ d + ofFn d v

theorem natDegree_monicPolynomialOfCoeffs
    (p d : ℕ) [Fact p.Prime] (v : Fin d → ZMod p) :
    (monicPolynomialOfCoeffs p d v).natDegree = d := by
  unfold monicPolynomialOfCoeffs
  have h : (ofFn d v).degree < (X ^ d : (ZMod p)[X]).degree := by
    simpa using ofFn_degree_lt v
  rw [natDegree_add_eq_left_of_degree_lt h, natDegree_X_pow]

theorem coeff_monicPolynomialOfCoeffs_of_lt
    (p d i : ℕ) [Fact p.Prime] (v : Fin d → ZMod p) (hi : i < d) :
    (monicPolynomialOfCoeffs p d v).coeff i = v ⟨i, hi⟩ := by
  simp [monicPolynomialOfCoeffs, coeff_X_pow, hi.ne,
    ofFn_coeff_eq_val_of_lt v hi]

theorem coeff_monicPolynomialOfCoeffs_self
    (p d : ℕ) [Fact p.Prime] (v : Fin d → ZMod p) :
    (monicPolynomialOfCoeffs p d v).coeff d = 1 := by
  simp [monicPolynomialOfCoeffs, ofFn_coeff_eq_zero_of_ge]

noncomputable def harcosEtaPolynomial
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (k : (ZMod p)[X]) : ℂ :=
  if k.natDegree = 0 then 1
  else if k.coeff 0 = 0 then 0
  else ZMod.stdAddChar
    (-a * (k.coeff (k.natDegree - 1) / k.leadingCoeff) -
      b * (k.coeff 1 / k.coeff 0))

theorem harcosEta_monic_degree_zero
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (v : Fin 0 → ZMod p) :
    harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p 0 v) = 1 := by
  simp [harcosEtaPolynomial, natDegree_monicPolynomialOfCoeffs]

theorem harcosEta_monic_degree_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (v : Fin 1 → ZMod p) :
    harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p 1 v) =
      if v 0 = 0 then 0 else ZMod.stdAddChar (-a * v 0 - b / v 0) := by
  rw [harcosEtaPolynomial]
  rw [natDegree_monicPolynomialOfCoeffs]
  simp only [Nat.one_ne_zero, ↓reduceIte]
  rw [coeff_monicPolynomialOfCoeffs_of_lt p 1 0 v (by omega)]
  change (if v 0 = 0 then 0 else
    ZMod.stdAddChar
      (-a * (v 0 / (monicPolynomialOfCoeffs p 1 v).leadingCoeff) -
        b * ((monicPolynomialOfCoeffs p 1 v).coeff 1 / v 0))) = _
  have hl : (monicPolynomialOfCoeffs p 1 v).leadingCoeff = 1 := by
    rw [leadingCoeff, natDegree_monicPolynomialOfCoeffs,
      coeff_monicPolynomialOfCoeffs_self]
  rw [hl, coeff_monicPolynomialOfCoeffs_self]
  simp [div_eq_mul_inv]

noncomputable def harcosEtaDegreeSum
    (p d : ℕ) [NeZero p] [Fact p.Prime] (a b : ZMod p) : ℂ :=
  ∑ v : Fin d → ZMod p,
    harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p d v)

theorem harcosEtaDegreeSum_one_eq_neg_frequencies
    (p : ℕ) [NeZero p] [Fact p.Prime] (a b : ZMod p) :
    harcosEtaDegreeSum p 1 a b = kloostermanSumZMod p (-a) (-b) := by
  unfold harcosEtaDegreeSum
  calc
    (∑ v : Fin 1 → ZMod p,
        harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p 1 v)) =
        ∑ c : ZMod p, harcosEtaPolynomial p a b
          (monicPolynomialOfCoeffs p 1 (fun _ => c)) := by
      apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod p))
      intro v
      congr 2
      funext i
      exact congrArg v (Subsingleton.elim i default)
    _ = kloostermanSumZMod p (-a) (-b) := by
      simp_rw [harcosEta_monic_degree_one]
      rw [Fintype.sum_eq_add_sum_subtype_ne _ (0 : ZMod p)]
      simp only [if_pos, zero_add]
      unfold kloostermanSumZMod
      apply Fintype.sum_equiv unitsEquivNeZero.symm
      intro c
      rw [if_neg c.2]
      apply congrArg ZMod.stdAddChar
      have hval : ((unitsEquivNeZero.symm c : (ZMod p)ˣ) : ZMod p) = c := rfl
      rw [hval]
      simp [div_eq_mul_inv]
      ring

theorem kloostermanSumZMod_neg_neg (p : ℕ) [NeZero p]
    (A B : ZMod p) :
    kloostermanSumZMod p (-A) (-B) = kloostermanSumZMod p A B := by
  unfold kloostermanSumZMod
  let e : (ZMod p)ˣ ≃ (ZMod p)ˣ := Equiv.mulLeft (-1)
  apply Fintype.sum_equiv e
  intro d
  apply congrArg ZMod.stdAddChar
  dsimp [e]
  simp

theorem harcosEtaDegreeSum_one
    (p : ℕ) [NeZero p] [Fact p.Prime] (a b : ZMod p) :
    harcosEtaDegreeSum p 1 a b = kloostermanSumZMod p a b := by
  rw [harcosEtaDegreeSum_one_eq_neg_frequencies,
    kloostermanSumZMod_neg_neg]

theorem harcosEta_monic_degree_two
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (v : Fin 2 → ZMod p) :
    harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p 2 v) =
      if v 0 = 0 then 0 else
        ZMod.stdAddChar (-a * v 1 - b * (v 1 / v 0)) := by
  rw [harcosEtaPolynomial]
  rw [natDegree_monicPolynomialOfCoeffs]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rw [coeff_monicPolynomialOfCoeffs_of_lt p 2 0 v (by omega)]
  change (if v 0 = 0 then 0 else
    ZMod.stdAddChar
      (-a * ((monicPolynomialOfCoeffs p 2 v).coeff 1 /
          (monicPolynomialOfCoeffs p 2 v).leadingCoeff) -
        b * ((monicPolynomialOfCoeffs p 2 v).coeff 1 / v 0))) = _
  have hl : (monicPolynomialOfCoeffs p 2 v).leadingCoeff = 1 := by
    rw [leadingCoeff, natDegree_monicPolynomialOfCoeffs,
      coeff_monicPolynomialOfCoeffs_self]
  rw [hl, coeff_monicPolynomialOfCoeffs_of_lt p 2 1 v (by omega)]
  simp

theorem harcosEtaDegreeSum_two
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosEtaDegreeSum p 2 a b = (p : ℂ) := by
  unfold harcosEtaDegreeSum
  calc
    (∑ v : Fin 2 → ZMod p,
        harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p 2 v)) =
        ∑ z : ZMod p × ZMod p,
          if z.1 = 0 then 0 else
            ZMod.stdAddChar (-a * z.2 - b * (z.2 / z.1)) := by
      apply Fintype.sum_equiv (finTwoArrowEquiv (ZMod p))
      intro v
      rw [harcosEta_monic_degree_two]
      rfl
    _ = ∑ c₀ : ZMod p,
        if c₀ = 0 then 0 else
          ∑ c₁ : ZMod p, ZMod.stdAddChar (c₁ * (-a - b / c₀)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c₀ _hc₀
      split_ifs with hc₀
      · simp
      · congr 1
        funext c₁
        apply congrArg ZMod.stdAddChar
        field_simp
    _ = ∑ c₀ : ZMod p,
        if c₀ = 0 then 0 else
          if -a - b / c₀ = 0 then (p : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro c₀ _hc₀
      by_cases hc₀ : c₀ = 0
      · simp [hc₀]
      · simp only [if_neg hc₀]
        exact sum_stdAddChar_mul p (-a - b / c₀)
    _ = (p : ℂ) := by
      let root : ZMod p := -b / a
      have hroot : root ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
      rw [Fintype.sum_eq_add_sum_subtype_ne _ root]
      have hcoeff : -a - b / root = 0 := by
        dsimp [root]
        field_simp
        ring
      rw [if_neg hroot, if_pos hcoeff]
      suffices hrest :
          (∑ c₀ : {c₀ : ZMod p // c₀ ≠ root},
            if (c₀ : ZMod p) = 0 then 0 else
              if -a - b / (c₀ : ZMod p) = 0 then (p : ℂ) else 0) = 0 by
        rw [hrest, add_zero]
      apply Finset.sum_eq_zero
      intro c₀ _hc₀
      by_cases hczero : (c₀ : ZMod p) = 0
      · rw [if_pos hczero]
      · rw [if_neg hczero]
        rw [if_neg]
        intro hcoeff₀
        apply c₀.2
        apply (mul_left_inj' ha).mp
        dsimp [root]
        field_simp at hcoeff₀ ⊢
        linear_combination -hcoeff₀

theorem harcosEta_monic_degree_ge_three
    (p d : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (v : Fin d → ZMod p) (hd : 3 ≤ d) :
    harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p d v) =
      if v ⟨0, by omega⟩ = 0 then 0 else
        ZMod.stdAddChar
          (-a * v ⟨d - 1, by omega⟩ -
            b * (v ⟨1, by omega⟩ / v ⟨0, by omega⟩)) := by
  rw [harcosEtaPolynomial]
  rw [natDegree_monicPolynomialOfCoeffs]
  simp only [show d ≠ 0 by omega, ↓reduceIte]
  rw [coeff_monicPolynomialOfCoeffs_of_lt p d 0 v (by omega)]
  change (if v ⟨0, by omega⟩ = 0 then 0 else
    ZMod.stdAddChar
      (-a * ((monicPolynomialOfCoeffs p d v).coeff (d - 1) /
          (monicPolynomialOfCoeffs p d v).leadingCoeff) -
        b * ((monicPolynomialOfCoeffs p d v).coeff 1 /
          v ⟨0, by omega⟩))) = _
  have hl : (monicPolynomialOfCoeffs p d v).leadingCoeff = 1 := by
    rw [leadingCoeff, natDegree_monicPolynomialOfCoeffs,
      coeff_monicPolynomialOfCoeffs_self]
  rw [hl,
    coeff_monicPolynomialOfCoeffs_of_lt p d (d - 1) v (by omega),
    coeff_monicPolynomialOfCoeffs_of_lt p d 1 v (by omega)]
  simp

noncomputable def addOneAt (p d : ℕ) [Fact p.Prime] (j : Fin d) :
    (Fin d → ZMod p) ≃ (Fin d → ZMod p) where
  toFun v i := if i = j then v i + 1 else v i
  invFun v i := if i = j then v i - 1 else v i
  left_inv v := by
    funext i
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi]
  right_inv v := by
    funext i
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi]

theorem harcosEta_addOneAt_last
    (p d : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (v : Fin d → ZMod p) (hd : 3 ≤ d) :
    harcosEtaPolynomial p a b
        (monicPolynomialOfCoeffs p d
          (addOneAt p d ⟨d - 1, by omega⟩ v)) =
      ZMod.stdAddChar (-a) *
        harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p d v) := by
  rw [harcosEta_monic_degree_ge_three p d a b _ hd,
    harcosEta_monic_degree_ge_three p d a b v hd]
  have hlast :
      addOneAt p d ⟨d - 1, by omega⟩ v ⟨d - 1, by omega⟩ =
        v ⟨d - 1, by omega⟩ + 1 := by
    simp [addOneAt]
  have hzero :
      addOneAt p d ⟨d - 1, by omega⟩ v ⟨0, by omega⟩ =
        v ⟨0, by omega⟩ := by
    simp [addOneAt, show (0 : ℕ) ≠ d - 1 by omega]
  have hone :
      addOneAt p d ⟨d - 1, by omega⟩ v ⟨1, by omega⟩ =
        v ⟨1, by omega⟩ := by
    simp [addOneAt, show (1 : ℕ) ≠ d - 1 by omega]
  rw [hlast, hzero, hone]
  split_ifs with hv₀
  · simp
  · rw [← AddChar.map_add_eq_mul]
    apply congrArg ZMod.stdAddChar
    ring

theorem harcosEtaDegreeSum_ge_three
    (p d : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hd : 3 ≤ d) :
    harcosEtaDegreeSum p d a b = 0 := by
  let e := addOneAt p d ⟨d - 1, by omega⟩
  have hperm : harcosEtaDegreeSum p d a b =
      ∑ v : Fin d → ZMod p,
        harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p d (e v)) := by
    symm
    unfold harcosEtaDegreeSum
    apply Fintype.sum_equiv e
    intro v
    rfl
  have heqsum : harcosEtaDegreeSum p d a b =
      ZMod.stdAddChar (-a) * harcosEtaDegreeSum p d a b := by
    calc
      harcosEtaDegreeSum p d a b =
          ∑ v : Fin d → ZMod p,
            harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p d (e v)) := hperm
      _ = ZMod.stdAddChar (-a) * harcosEtaDegreeSum p d a b := by
        dsimp [e]
        simp_rw [harcosEta_addOneAt_last p d a b _ hd]
        rw [← Finset.mul_sum]
        rfl
  have hchar : ZMod.stdAddChar (-a) ≠ (1 : ℂ) := by
    intro h
    have hzero := (ZMod.stdAddChar : AddChar (ZMod p) ℂ).map_zero_eq_one
    have heq : (-a : ZMod p) = 0 :=
      ZMod.injective_stdAddChar (h.trans hzero.symm)
    exact ha (neg_eq_zero.mp heq)
  have hmul : (1 - ZMod.stdAddChar (-a)) *
      harcosEtaDegreeSum p d a b = 0 := by
    calc
      (1 - ZMod.stdAddChar (-a)) * harcosEtaDegreeSum p d a b =
          harcosEtaDegreeSum p d a b -
            ZMod.stdAddChar (-a) * harcosEtaDegreeSum p d a b := by ring
      _ = 0 := sub_eq_zero.mpr heqsum
  exact (mul_eq_zero.mp hmul).resolve_left
    (sub_ne_zero.mpr (Ne.symm hchar))

theorem harcosEtaDegreeSum_zero
    (p : ℕ) [NeZero p] [Fact p.Prime] (a b : ZMod p) :
    harcosEtaDegreeSum p 0 a b = 1 := by
  unfold harcosEtaDegreeSum
  rw [Fintype.sum_unique]
  exact harcosEta_monic_degree_zero p a b default

theorem harcosEtaDegreeSum_eq
    (p d : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosEtaDegreeSum p d a b =
      if d = 0 then 1
      else if d = 1 then kloostermanSumZMod p a b
      else if d = 2 then (p : ℂ)
      else 0 := by
  rcases d with _ | _ | _ | d
  · rw [harcosEtaDegreeSum_zero]
    simp
  · rw [harcosEtaDegreeSum_one]
    simp
  · rw [harcosEtaDegreeSum_two p a b ha hb]
    simp
  · rw [harcosEtaDegreeSum_ge_three p (d + 3) a b ha (by omega)]
    simp

noncomputable def harcosLPolynomial
    (p : ℕ) [NeZero p] (a b : ZMod p) : ℂ[X] :=
  1 + C (kloostermanSumZMod p a b) * X + C (p : ℂ) * X ^ 2

theorem coeff_harcosLPolynomial
    (p d : ℕ) [NeZero p] (a b : ZMod p) :
    (harcosLPolynomial p a b).coeff d =
      if d = 0 then 1
      else if d = 1 then kloostermanSumZMod p a b
      else if d = 2 then (p : ℂ)
      else 0 := by
  rcases d with _ | _ | _ | d <;>
    simp [harcosLPolynomial, coeff_one]

theorem harcosLPolynomial_coeff_eq_etaDegreeSum
    (p d : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    (harcosLPolynomial p a b).coeff d = harcosEtaDegreeSum p d a b := by
  rw [coeff_harcosLPolynomial, harcosEtaDegreeSum_eq p d a b ha hb]

theorem harcosEtaPolynomial_eq_of_monic_pos
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (k : (ZMod p)[X])
    (hk : k.Monic) (hdegree : k.natDegree ≠ 0)
    (hconstant : k.coeff 0 ≠ 0) :
    harcosEtaPolynomial p a b k =
      ZMod.stdAddChar
        (-a * k.nextCoeff - b * (k.coeff 1 / k.coeff 0)) := by
  simp [harcosEtaPolynomial, hdegree, hconstant, Polynomial.nextCoeff,
    hk.leadingCoeff]

theorem coeffOne_div_coeffZero_mul
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (k l : (ZMod p)[X]) (hk0 : k.coeff 0 ≠ 0) (hl0 : l.coeff 0 ≠ 0) :
    (k * l).coeff 1 / (k * l).coeff 0 =
      k.coeff 1 / k.coeff 0 + l.coeff 1 / l.coeff 0 := by
  rw [Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero]
  field_simp
  ring

theorem harcosEtaPolynomial_mul_of_monic
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (k l : (ZMod p)[X])
    (hk : k.Monic) (hl : l.Monic) :
    harcosEtaPolynomial p a b (k * l) =
      harcosEtaPolynomial p a b k * harcosEtaPolynomial p a b l := by
  by_cases hkdeg : k.natDegree = 0
  · have hkone : k = 1 := Polynomial.eq_one_of_monic_natDegree_zero hk hkdeg
    subst k
    simp [harcosEtaPolynomial]
  by_cases hldeg : l.natDegree = 0
  · have hlone : l = 1 := Polynomial.eq_one_of_monic_natDegree_zero hl hldeg
    subst l
    simp [harcosEtaPolynomial]
  have hpdeg : (k * l).natDegree ≠ 0 := by
    rw [hk.natDegree_mul hl]
    omega
  by_cases hk0 : k.coeff 0 = 0
  · simp [harcosEtaPolynomial, hkdeg, hpdeg, hk0,
      Polynomial.mul_coeff_zero]
  by_cases hl0 : l.coeff 0 = 0
  · simp [harcosEtaPolynomial, hldeg, hpdeg, hk0, hl0,
      Polynomial.mul_coeff_zero]
  have hp0 : (k * l).coeff 0 ≠ 0 := by
    rw [Polynomial.mul_coeff_zero]
    exact mul_ne_zero hk0 hl0
  rw [harcosEtaPolynomial_eq_of_monic_pos p a b (k * l) (hk.mul hl) hpdeg hp0,
    harcosEtaPolynomial_eq_of_monic_pos p a b k hk hkdeg hk0,
    harcosEtaPolynomial_eq_of_monic_pos p a b l hl hldeg hl0,
    ← AddChar.map_add_eq_mul]
  apply congrArg ZMod.stdAddChar
  rw [hk.nextCoeff_mul hl, coeffOne_div_coeffZero_mul p k l hk0 hl0]
  ring

end RiemannZeta.GuthMaynard
