import RiemannZeta.GuthMaynard.KloostermanPrime
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

open Complex Finset
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-!
# DFI equation (26): the Ramanujan main frequency

This file proves the exact formula

`S(h,0;q) = ∑ v ∣ gcd(h,q), v * μ(q/v)`

from the project's complete additive-character sum.  The proof includes the
Möbius coprimality indicator, the exact parametrization of residue multiples,
additive-character orthogonality on the reduced modulus, and the divisor
involution appearing in the printed equation.
-/

theorem sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg
    (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  change ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n =
    (1 : ArithmeticFunction ℤ) n at h
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply] using h

theorem stdAddChar_progression
    (q h d : ℕ) [NeZero q] [NeZero (q / d)] (hd : d ∣ q) (hd0 : 0 < d)
    (y : ZMod (q / d)) :
    ZMod.stdAddChar ((h * d * y.val : ℕ) : ZMod q) =
      ZMod.stdAddChar ((h : ZMod (q / d)) * y) := by
  have hq : q = d * (q / d) := (Nat.mul_div_cancel' hd).symm
  have hr : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hd) hd0
  rw [show (h : ZMod (q / d)) * y =
      ((h * y.val : ℕ) : ZMod (q / d)) by
        calc
          (h : ZMod (q / d)) * y =
              (h : ZMod (q / d)) * (y.val : ZMod (q / d)) :=
            congrArg ((h : ZMod (q / d)) * ·)
              (ZMod.natCast_zmod_val y).symm
          _ = ((h * y.val : ℕ) : ZMod (q / d)) := by push_cast; rfl]
  rw [show ((h * d * y.val : ℕ) : ZMod q) =
      (((h * d * y.val : ℕ) : ℤ) : ZMod q) by norm_cast]
  rw [show ((h * y.val : ℕ) : ZMod (q / d)) =
      (((h * y.val : ℕ) : ℤ) : ZMod (q / d)) by norm_cast]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  apply congrArg Complex.exp
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hrC : ((q / d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  rw [show (q : ℂ) = (d : ℂ) * ((q / d : ℕ) : ℂ) by exact_mod_cast hq]
  field_simp

theorem sum_stdAddChar_progression
    (q h d : ℕ) [NeZero q] [NeZero (q / d)] (hd : d ∣ q) (hd0 : 0 < d) :
    (∑ y : ZMod (q / d),
        ZMod.stdAddChar ((h * d * y.val : ℕ) : ZMod q)) =
      if q / d ∣ h then ((q / d : ℕ) : ℂ) else 0 := by
  calc
    (∑ y : ZMod (q / d),
        ZMod.stdAddChar ((h * d * y.val : ℕ) : ZMod q)) =
        ∑ y : ZMod (q / d), ZMod.stdAddChar ((h : ZMod (q / d)) * y) := by
      apply Finset.sum_congr rfl
      intro y _hy
      exact stdAddChar_progression q h d hd hd0 y
    _ = if q / d ∣ h then ((q / d : ℕ) : ℂ) else 0 := by
      by_cases hdiv : q / d ∣ h
      · rw [if_pos hdiv]
        have hh : (h : ZMod (q / d)) = 0 :=
          (ZMod.natCast_eq_zero_iff h (q / d)).2 hdiv
        simp [hh, ZMod.card]
      · rw [if_neg hdiv]
        exact AddChar.sum_eq_zero_of_ne_one
          (ZMod.isPrimitive_stdAddChar (q / d)
            ((ZMod.natCast_eq_zero_iff h (q / d)).not.mpr hdiv))

theorem sum_moebius_gcd_indicator (x q : ℕ) :
    (∑ d ∈ (Nat.gcd x q).divisors, ArithmeticFunction.moebius d) =
      if Nat.Coprime x q then 1 else 0 := by
  rw [sum_moebius_divisors]

theorem sum_moebius_gcd_indicator_complex (x q : ℕ) :
    (∑ d ∈ (Nat.gcd x q).divisors,
        (ArithmeticFunction.moebius d : ℂ)) =
      if Nat.Coprime x q then 1 else 0 := by
  exact_mod_cast sum_moebius_gcd_indicator x q

noncomputable def zmodMultiplesEquiv
    (q d : ℕ) [NeZero q] [NeZero (q / d)] (hd : d ∣ q) (hd0 : 0 < d) :
    ZMod (q / d) ≃ {x : ZMod q // d ∣ x.val} where
  toFun y := by
    have hq : q = d * (q / d) := (Nat.mul_div_cancel' hd).symm
    have hlt : d * y.val < q := by
      calc
        d * y.val < d * (q / d) := (Nat.mul_lt_mul_left hd0).2 y.val_lt
        _ = q := Nat.mul_div_cancel' hd
    exact ⟨(d * y.val : ℕ), by
      rw [ZMod.val_natCast_of_lt hlt]
      exact dvd_mul_right d y.val⟩
  invFun := fun x : {x : ZMod q // d ∣ x.val} =>
    ((x.1.val / d : ℕ) : ZMod (q / d))
  left_inv y := by
    apply ZMod.val_injective
    have hr : 0 < q / d := Nat.div_pos
      (Nat.le_of_dvd (NeZero.pos q) hd) hd0
    have hq : q = d * (q / d) := (Nat.mul_div_cancel' hd).symm
    have hlt : d * y.val < q := by
      calc
        d * y.val < d * (q / d) := (Nat.mul_lt_mul_left hd0).2 y.val_lt
        _ = q := Nat.mul_div_cancel' hd
    dsimp
    rw [ZMod.val_natCast_of_lt hlt, ZMod.val_natCast,
      Nat.mul_comm d y.val, Nat.mul_div_left _ hd0,
      Nat.mod_eq_of_lt y.val_lt]
  right_inv x := by
    apply Subtype.ext
    have hr : 0 < q / d := Nat.div_pos
      (Nat.le_of_dvd (NeZero.pos q) hd) hd0
    have hquot : x.1.val / d < q / d := by
      rw [Nat.div_lt_iff_lt_mul hd0]
      calc
        x.1.val < q := x.1.val_lt
        _ = (q / d) * d := by rw [Nat.mul_comm, Nat.mul_div_cancel' hd]
    dsimp
    rw [ZMod.val_natCast_of_lt hquot, Nat.mul_div_cancel' x.property,
      ZMod.natCast_zmod_val]

theorem zmodMultiplesEquiv_symm_val
    (q d : ℕ) [NeZero q] [NeZero (q / d)] (hd : d ∣ q) (hd0 : 0 < d)
    (x : {x : ZMod q // d ∣ x.val}) :
    ((zmodMultiplesEquiv q d hd hd0).symm x).val = x.1.val / d := by
  have hr : 0 < q / d := Nat.div_pos
    (Nat.le_of_dvd (NeZero.pos q) hd) hd0
  have hquot : x.1.val / d < q / d := by
    rw [Nat.div_lt_iff_lt_mul hd0]
    calc
      x.1.val < q := x.1.val_lt
      _ = (q / d) * d := by rw [Nat.mul_comm, Nat.mul_div_cancel' hd]
  exact ZMod.val_natCast_of_lt hquot

theorem ramanujanSum_eq_coprime_residues (q h : ℕ) [NeZero q] :
    ramanujanSum q h =
      ∑ x : ZMod q,
        if Nat.Coprime x.val q then ZMod.stdAddChar ((h : ZMod q) * x) else 0 := by
  unfold ramanujanSum kloostermanSum
  simp only [Nat.cast_zero, zero_mul, add_zero]
  calc
    (∑ d : (ZMod q)ˣ, ZMod.stdAddChar ((h : ZMod q) * (d : ZMod q))) =
        ∑ x : {x : ZMod q // Nat.Coprime x.val q},
          ZMod.stdAddChar ((h : ZMod q) * x.1) := by
      apply Fintype.sum_equiv ZMod.unitsEquivCoprime
      intro d
      rfl
    _ = _ := by
      rw [← Finset.sum_filter]
      symm
      exact Finset.sum_subtype
        (Finset.univ.filter fun x : ZMod q => Nat.Coprime x.val q)
        (fun x => by simp)
        (fun x => ZMod.stdAddChar ((h : ZMod q) * x))

theorem filter_divisors_dvd_eq_gcd_divisors (x q : ℕ) (hq : 0 < q) :
    q.divisors.filter (fun d => d ∣ x) = (Nat.gcd x q).divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, hq.ne', ne_eq]
  constructor
  · rintro ⟨⟨hdq, _hq0⟩, hdx⟩
    exact ⟨Nat.dvd_gcd hdx hdq, (Nat.gcd_pos_of_pos_right x hq).ne'⟩
  · rintro ⟨hdg, _hg0⟩
    exact ⟨⟨dvd_trans hdg (Nat.gcd_dvd_right x q), by simp⟩,
      dvd_trans hdg (Nat.gcd_dvd_left x q)⟩

theorem sum_divisors_dvd_moebius (x q : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors,
        if d ∣ x then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime x q then 1 else 0 := by
  rw [← Finset.sum_filter]
  rw [filter_divisors_dvd_eq_gcd_divisors x q hq]
  exact sum_moebius_gcd_indicator_complex x q

theorem ramanujanSum_eq_moebius_progressions (q h : ℕ) [NeZero q] :
    ramanujanSum q h =
      ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ x : ZMod q,
          if d ∣ x.val then ZMod.stdAddChar ((h : ZMod q) * x) else 0 := by
  rw [show ramanujanSum q h =
      ∑ x : ZMod q,
        if Nat.Coprime x.val q then
          ZMod.stdAddChar ((h : ZMod q) * x) else 0 by
    unfold ramanujanSum kloostermanSum
    simp only [Nat.cast_zero, zero_mul, add_zero]
    calc
      (∑ d : (ZMod q)ˣ, ZMod.stdAddChar ((h : ZMod q) * (d : ZMod q))) =
          ∑ x : {x : ZMod q // Nat.Coprime x.val q},
            ZMod.stdAddChar ((h : ZMod q) * x.1) := by
        apply Fintype.sum_equiv ZMod.unitsEquivCoprime
        intro d
        rfl
      _ = _ := by
        rw [← Finset.sum_filter]
        symm
        exact Finset.sum_subtype
          (Finset.univ.filter fun x : ZMod q => Nat.Coprime x.val q)
          (fun x => by simp)
          (fun x => ZMod.stdAddChar ((h : ZMod q) * x))]
  calc
    (∑ x : ZMod q,
        if Nat.Coprime x.val q then
          ZMod.stdAddChar ((h : ZMod q) * x) else 0) =
        ∑ x : ZMod q,
          (∑ d ∈ q.divisors,
            if d ∣ x.val then (ArithmeticFunction.moebius d : ℂ) else 0) *
              ZMod.stdAddChar ((h : ZMod q) * x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [sum_divisors_dvd_moebius x.val q (NeZero.pos q)]
      by_cases hc : Nat.Coprime x.val q <;> simp [hc]
    _ = ∑ x : ZMod q, ∑ d ∈ q.divisors,
          (ArithmeticFunction.moebius d : ℂ) *
            (if d ∣ x.val then ZMod.stdAddChar ((h : ZMod q) * x) else 0) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hdx : d ∣ x.val <;> simp [hdx]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.mul_sum]

theorem sum_zmod_dvd_stdAddChar
    (q h d : ℕ) [NeZero q] (hdmem : d ∈ q.divisors) :
    (∑ x : ZMod q,
        if d ∣ x.val then ZMod.stdAddChar ((h : ZMod q) * x) else 0) =
      if q / d ∣ h then ((q / d : ℕ) : ℂ) else 0 := by
  have hdq : d ∣ q := (Nat.mem_divisors.mp hdmem).1
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq (NeZero.pos q)
  have hr : 0 < q / d := Nat.div_pos
    (Nat.le_of_dvd (NeZero.pos q) hdq) hd0
  letI : NeZero (q / d) := ⟨hr.ne'⟩
  rw [← Finset.sum_filter]
  calc
    (∑ x ∈ Finset.univ.filter (fun x : ZMod q => d ∣ x.val),
        ZMod.stdAddChar ((h : ZMod q) * x)) =
        ∑ x : {x : ZMod q // d ∣ x.val},
          ZMod.stdAddChar ((h : ZMod q) * x.1) :=
      Finset.sum_subtype
        (Finset.univ.filter fun x : ZMod q => d ∣ x.val)
        (fun x => by simp)
        (fun x => ZMod.stdAddChar ((h : ZMod q) * x))
    _ = ∑ y : ZMod (q / d),
          ZMod.stdAddChar ((h * d * y.val : ℕ) : ZMod q) := by
      apply Fintype.sum_equiv (zmodMultiplesEquiv q d hdq hd0).symm
      intro x
      rw [zmodMultiplesEquiv_symm_val q d hdq hd0 x]
      have hmul : d * (x.1.val / d) = x.1.val := Nat.mul_div_cancel' x.2
      rw [show ((h * d * (x.1.val / d) : ℕ) : ZMod q) =
          (h : ZMod q) * (x.1.val : ZMod q) by
            push_cast
            have hmulZ := congrArg (fun n : ℕ => (n : ZMod q)) hmul
            push_cast at hmulZ
            calc
              (h : ZMod q) * d * (x.1.val / d : ℕ) =
                  (h : ZMod q) * ((d : ZMod q) * (x.1.val / d : ℕ)) := by ring
              _ = (h : ZMod q) * (x.1.val : ZMod q) := by rw [hmulZ]]
      rw [ZMod.natCast_zmod_val]
    _ = _ := sum_stdAddChar_progression q h d hdq hd0

theorem ramanujanSum_eq_moebius_divisor (q h : ℕ) [NeZero q] :
    ramanujanSum q h =
      ∑ d ∈ q.divisors,
        if q / d ∣ h then
          (ArithmeticFunction.moebius d : ℂ) * (q / d : ℕ)
        else 0 := by
  rw [ramanujanSum_eq_moebius_progressions]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_zmod_dvd_stdAddChar q h d hd]
  by_cases hdiv : q / d ∣ h <;> simp [hdiv]

theorem divisor_involution_ramanujan (q h : ℕ) :
    (∑ d ∈ q.divisors,
        if q / d ∣ h then
          (ArithmeticFunction.moebius d : ℂ) * (q / d : ℕ)
        else 0) =
      ∑ v ∈ q.divisors,
        if v ∣ h then
          (v : ℂ) * ArithmeticFunction.moebius (q / v)
        else 0 := by
  let f : ℕ → ℕ → ℂ := fun v d =>
    if v ∣ h then (v : ℂ) * ArithmeticFunction.moebius d else 0
  calc
    (∑ d ∈ q.divisors,
        if q / d ∣ h then
          (ArithmeticFunction.moebius d : ℂ) * (q / d : ℕ)
        else 0) =
        ∑ d ∈ q.divisors, f (q / d) d := by
      apply Finset.sum_congr rfl
      intro d _hd
      dsimp [f]
      by_cases hv : q / d ∣ h <;> simp [hv, mul_comm]
    _ = ∑ p ∈ q.divisorsAntidiagonal, f p.1 p.2 := by
      rw [Nat.sum_divisorsAntidiagonal']
    _ = ∑ v ∈ q.divisors, f v (q / v) := by
      rw [Nat.sum_divisorsAntidiagonal]
    _ = _ := by rfl

theorem ramanujanSum_eq_dfi26 (q h : ℕ) [NeZero q] :
    ramanujanSum q h =
      ∑ v ∈ (Nat.gcd h q).divisors,
        (v : ℂ) * ArithmeticFunction.moebius (q / v) := by
  rw [ramanujanSum_eq_moebius_divisor]
  rw [divisor_involution_ramanujan q h]
  rw [← Finset.sum_filter]
  rw [filter_divisors_dvd_eq_gcd_divisors h q (NeZero.pos q)]

/-- Ramanujan sums at natural frequencies are real. -/
theorem star_ramanujanSum (q h : ℕ) [NeZero q] :
    star (ramanujanSum q h) = ramanujanSum q h := by
  rw [ramanujanSum_eq_dfi26]
  simp

/-- The divisor-loss form of the estimate following DFI equation (26).  This
is the form used under the paper's ubiquitous epsilon-power convention. -/
theorem norm_ramanujanSum_le_gcd_mul_divisors (q h : ℕ) [NeZero q] :
    ‖ramanujanSum q h‖ ≤
      (Nat.gcd h q : ℝ) * ((Nat.gcd h q).divisors.card : ℝ) := by
  rw [ramanujanSum_eq_dfi26]
  calc
    ‖∑ v ∈ (Nat.gcd h q).divisors,
        (v : ℂ) * ArithmeticFunction.moebius (q / v)‖ ≤
        ∑ v ∈ (Nat.gcd h q).divisors,
          ‖(v : ℂ) * ArithmeticFunction.moebius (q / v)‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ (Nat.gcd h q).divisors, (Nat.gcd h q : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_mul, Complex.norm_natCast, Complex.norm_intCast]
      have hvle : (v : ℝ) ≤ Nat.gcd h q := by
        exact_mod_cast Nat.divisor_le hv
      have hμ : (|ArithmeticFunction.moebius (q / v)| : ℝ) ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      nlinarith [(Nat.cast_nonneg v : (0 : ℝ) ≤ v)]
    _ = (Nat.gcd h q : ℝ) * ((Nat.gcd h q).divisors.card : ℝ) := by
      simp [mul_comm]

end RiemannZeta.GuthMaynard
