import RiemannZeta.GuthMaynard.KloostermanPrimePower
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Composite-modulus Weil--Estermann bound

This module assembles the prime-power estimates through the exact CRT
factorization of complete Kloosterman sums.  It supplies the square-root
estimate used in DFI equation (25).
-/

namespace RiemannZeta.GuthMaynard

open Complex
open scoped BigOperators
open Classical

theorem nat_dvd_of_dvd_mod_of_dvd
    {d q n : ℕ} (hdq : d ∣ q) (hdmod : d ∣ n % q) : d ∣ n := by
  have hmul : d ∣ n / q * q := dvd_mul_of_dvd_right hdq (n / q)
  have hadd : d ∣ n / q * q + n % q := dvd_add hmul hdmod
  simpa only [Nat.div_add_mod'] using hadd

/-- The Bezout coefficient multiplying the first CRT component is a unit. -/
theorem isUnit_gcdB_cast_left
    (a b : ℕ) [NeZero a] [NeZero b] (h : a.Coprime b) :
    IsUnit (Nat.gcdB a b : ZMod a) := by
  have hbez : (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b = 1 := by
    simpa [h] using (Nat.gcd_eq_gcd_ab a b).symm
  have hcast := congrArg (fun z : ℤ => (z : ZMod a)) hbez
  push_cast at hcast
  have hmul : (Nat.gcdB a b : ZMod a) * (b : ZMod a) = 1 := by
    simpa [mul_comm] using hcast
  exact IsUnit.of_mul_eq_one (b : ZMod a) hmul

/-- The Bezout coefficient multiplying the second CRT component is a unit. -/
theorem isUnit_gcdA_cast_right
    (a b : ℕ) [NeZero a] [NeZero b] (h : a.Coprime b) :
    IsUnit (Nat.gcdA a b : ZMod b) := by
  have hbez : (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b = 1 := by
    simpa [h] using (Nat.gcd_eq_gcd_ab a b).symm
  have hcast := congrArg (fun z : ℤ => (z : ZMod b)) hbez
  push_cast at hcast
  have hmul : (Nat.gcdA a b : ZMod b) * (a : ZMod b) = 1 := by
    simpa [mul_comm] using hcast
  exact IsUnit.of_mul_eq_one (a : ZMod b) hmul

/-- Divisibility by a divisor of the modulus is unchanged when a residue is
multiplied by a unit. -/
theorem dvd_val_of_dvd_val_mul_isUnit
    (q d : ℕ) [NeZero q] (hdq : d ∣ q) (u x : ZMod q) (hu : IsUnit u)
    (hd : d ∣ (u * x).val) : d ∣ x.val := by
  let U : (ZMod q)ˣ := hu.unit
  have hU : (U : ZMod q) = u := hu.unit_spec
  have hd' : d ∣ ((U : ZMod q) * x).val := by simpa [hU] using hd
  have hprod : d ∣ (U : ZMod q).val * x.val := by
    rw [ZMod.val_mul] at hd'
    exact nat_dvd_of_dvd_mod_of_dvd hdq hd'
  have hcop : Nat.Coprime d (U : ZMod q).val :=
    ((ZMod.val_coe_unit_coprime U).of_dvd_right hdq).symm
  exact hcop.dvd_of_dvd_mul_left hprod

theorem chineseRemainder_natCast_fst
    (a b A : ℕ) [NeZero a] [NeZero b] (h : a.Coprime b) :
    (ZMod.chineseRemainder h (A : ZMod (a * b))).1 = (A : ZMod a) := by
  rw [chineseRemainder_fst_eq_val a b h]
  apply ZMod.val_injective
  simp only [ZMod.val_natCast]
  exact Nat.mod_mod_of_dvd A (dvd_mul_right a b)

theorem chineseRemainder_natCast_snd
    (a b A : ℕ) [NeZero a] [NeZero b] (h : a.Coprime b) :
    (ZMod.chineseRemainder h (A : ZMod (a * b))).2 = (A : ZMod b) := by
  rw [chineseRemainder_snd_eq_val a b h]
  apply ZMod.val_injective
  simp only [ZMod.val_natCast]
  exact Nat.mod_mod_of_dvd A (dvd_mul_left b a)

/-- The common divisor appearing in the first local Weil bound divides the
global common divisor. -/
theorem crt_left_local_gcd_dvd_global
    (a b A B : ℕ) [NeZero a] [NeZero b] (h : a.Coprime b) :
    Nat.gcd
        (Nat.gcd
          (((Nat.gcdB a b : ZMod a) * (A : ZMod a)).val)
          (((Nat.gcdB a b : ZMod a) * (B : ZMod a)).val)) a ∣
      Nat.gcd (Nat.gcd A B) (a * b) := by
  let g := Nat.gcd
    (Nat.gcd
      (((Nat.gcdB a b : ZMod a) * (A : ZMod a)).val)
      (((Nat.gcdB a b : ZMod a) * (B : ZMod a)).val)) a
  have hga : g ∣ a := Nat.gcd_dvd_right _ _
  have hgAprod : g ∣ ((Nat.gcdB a b : ZMod a) * (A : ZMod a)).val :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgBprod : g ∣ ((Nat.gcdB a b : ZMod a) * (B : ZMod a)).val :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgAmod : g ∣ (A : ZMod a).val :=
    dvd_val_of_dvd_val_mul_isUnit a g hga _ _
      (isUnit_gcdB_cast_left a b h) hgAprod
  have hgBmod : g ∣ (B : ZMod a).val :=
    dvd_val_of_dvd_val_mul_isUnit a g hga _ _
      (isUnit_gcdB_cast_left a b h) hgBprod
  have hgA : g ∣ A := by
    rw [ZMod.val_natCast] at hgAmod
    exact nat_dvd_of_dvd_mod_of_dvd hga hgAmod
  have hgB : g ∣ B := by
    rw [ZMod.val_natCast] at hgBmod
    exact nat_dvd_of_dvd_mod_of_dvd hga hgBmod
  exact Nat.dvd_gcd (Nat.dvd_gcd hgA hgB) (hga.trans (dvd_mul_right a b))

/-- The common divisor appearing in the second local Weil bound divides the
global common divisor. -/
theorem crt_right_local_gcd_dvd_global
    (a b A B : ℕ) [NeZero a] [NeZero b] (h : a.Coprime b) :
    Nat.gcd
        (Nat.gcd
          (((Nat.gcdA a b : ZMod b) * (A : ZMod b)).val)
          (((Nat.gcdA a b : ZMod b) * (B : ZMod b)).val)) b ∣
      Nat.gcd (Nat.gcd A B) (a * b) := by
  let g := Nat.gcd
    (Nat.gcd
      (((Nat.gcdA a b : ZMod b) * (A : ZMod b)).val)
      (((Nat.gcdA a b : ZMod b) * (B : ZMod b)).val)) b
  have hgb : g ∣ b := Nat.gcd_dvd_right _ _
  have hgAprod : g ∣ ((Nat.gcdA a b : ZMod b) * (A : ZMod b)).val :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgBprod : g ∣ ((Nat.gcdA a b : ZMod b) * (B : ZMod b)).val :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgAmod : g ∣ (A : ZMod b).val :=
    dvd_val_of_dvd_val_mul_isUnit b g hgb _ _
      (isUnit_gcdA_cast_right a b h) hgAprod
  have hgBmod : g ∣ (B : ZMod b).val :=
    dvd_val_of_dvd_val_mul_isUnit b g hgb _ _
      (isUnit_gcdA_cast_right a b h) hgBprod
  have hgA : g ∣ A := by
    rw [ZMod.val_natCast] at hgAmod
    exact nat_dvd_of_dvd_mod_of_dvd hgb hgAmod
  have hgB : g ∣ B := by
    rw [ZMod.val_natCast] at hgBmod
    exact nat_dvd_of_dvd_mod_of_dvd hgb hgBmod
  exact Nat.dvd_gcd (Nat.dvd_gcd hgA hgB) (hgb.trans (dvd_mul_left b a))

/-- The Weil--Estermann estimate at one fixed modulus. -/
def KloostermanWeilAt (q : ℕ) : Prop :=
  ∀ (hq : q ≠ 0) (A B : ℕ),
    ‖@kloostermanSum q A B ⟨hq⟩‖ ≤
      Real.sqrt (Nat.gcd (Nat.gcd A B) q) * Real.sqrt q *
        (q.divisors.card : ℝ)

/-- CRT preserves the Weil--Estermann estimate under multiplication of
positive coprime moduli. -/
theorem kloostermanWeilAt_mul_coprime
    (a b : ℕ) (haPos : 1 < a) (hbPos : 1 < b) (h : a.Coprime b)
    (ha : KloostermanWeilAt a) (hb : KloostermanWeilAt b) :
    KloostermanWeilAt (a * b) := by
  intro habNe A B
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  letI : NeZero (a * b) := ⟨habNe⟩
  let A₁ : ZMod a := (Nat.gcdB a b : ZMod a) * (A : ZMod a)
  let B₁ : ZMod a := (Nat.gcdB a b : ZMod a) * (B : ZMod a)
  let A₂ : ZMod b := (Nat.gcdA a b : ZMod b) * (A : ZMod b)
  let B₂ : ZMod b := (Nat.gcdA a b : ZMod b) * (B : ZMod b)
  let g₁ := Nat.gcd (Nat.gcd A₁.val B₁.val) a
  let g₂ := Nat.gcd (Nat.gcd A₂.val B₂.val) b
  let G := Nat.gcd (Nat.gcd A B) (a * b)
  have hfactor :
      ‖kloostermanSum (a * b) A B‖ =
        ‖kloostermanSum a A₁.val B₁.val‖ *
          ‖kloostermanSum b A₂.val B₂.val‖ := by
    rw [kloostermanSum_eq_kloostermanSumZMod,
      kloostermanSum_eq_kloostermanSumZMod,
      kloostermanSum_eq_kloostermanSumZMod]
    rw [norm_kloostermanSumZMod_mul_coprime a b h]
    rw [chineseRemainder_natCast_fst a b A h,
      chineseRemainder_natCast_fst a b B h,
      chineseRemainder_natCast_snd a b A h,
      chineseRemainder_natCast_snd a b B h]
    simp only [A₁, B₁, A₂, B₂, ZMod.natCast_zmod_val]
  have hleft := ha (by omega) A₁.val B₁.val
  have hright := hb (by omega) A₂.val B₂.val
  have hg₁a : g₁ ∣ a := Nat.gcd_dvd_right _ _
  have hg₂b : g₂ ∣ b := Nat.gcd_dvd_right _ _
  have hg₁G : g₁ ∣ G := by
    exact crt_left_local_gcd_dvd_global a b A B h
  have hg₂G : g₂ ∣ G := by
    exact crt_right_local_gcd_dvd_global a b A B h
  have hgCoprime : g₁.Coprime g₂ := h.of_dvd hg₁a hg₂b
  have hgMulDvd : g₁ * g₂ ∣ G :=
    hgCoprime.mul_dvd_of_dvd_of_dvd hg₁G hg₂G
  have hGPos : 0 < G := by
    exact Nat.gcd_pos_of_pos_right _ (mul_pos (by omega) (by omega))
  have hgMulLe : g₁ * g₂ ≤ G := Nat.le_of_dvd hGPos hgMulDvd
  have hsqrtG :
      Real.sqrt ((g₁ * g₂ : ℕ) : ℝ) =
        Real.sqrt (g₁ : ℝ) * Real.sqrt (g₂ : ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg g₁)]
  have hsqrtAB :
      Real.sqrt (((a * b : ℕ) : ℝ)) =
        Real.sqrt (a : ℝ) * Real.sqrt (b : ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg a)]
  have hcard : (a * b).divisors.card = a.divisors.card * b.divisors.card :=
    h.card_divisors_mul
  rw [hfactor]
  calc
    ‖kloostermanSum a A₁.val B₁.val‖ *
          ‖kloostermanSum b A₂.val B₂.val‖ ≤
        (Real.sqrt g₁ * Real.sqrt a * (a.divisors.card : ℝ)) *
          (Real.sqrt g₂ * Real.sqrt b * (b.divisors.card : ℝ)) := by
      gcongr
    _ = Real.sqrt ((g₁ * g₂ : ℕ) : ℝ) *
          Real.sqrt (((a * b : ℕ) : ℝ)) *
            (((a * b).divisors.card : ℕ) : ℝ) := by
      rw [hsqrtG, hsqrtAB, hcard]
      push_cast
      ring
    _ ≤ Real.sqrt G * Real.sqrt ((a * b : ℕ) : ℝ) *
          (((a * b).divisors.card : ℕ) : ℝ) := by
      gcongr

theorem kloostermanWeilAt_zero : KloostermanWeilAt 0 := by
  intro hzero
  exact (hzero rfl).elim

theorem kloostermanWeilAt_primePow
    (p k : ℕ) (hp : p.Prime) : KloostermanWeilAt (p ^ k) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hpowNe A B
  letI : NeZero (p ^ k) := ⟨hpowNe⟩
  rw [kloostermanSum_eq_kloostermanSumZMod]
  have hlocal := norm_kloostermanSumZMod_primePow_le p k A B
  have hcard : (p ^ k).divisors.card = k + 1 := by
    rw [Nat.divisors_prime_pow hp]
    simp
  simpa only [hcard, Nat.cast_pow] using hlocal

theorem kloostermanWeilAt_one : KloostermanWeilAt 1 := by
  simpa using kloostermanWeilAt_primePow 2 0 Nat.prime_two

/-- DFI equation (25): the complete Weil--Estermann estimate for every
positive modulus, including the common-frequency gcd and divisor factors. -/
theorem kloostermanWeilBound_native : KloostermanWeilBoundProp := by
  intro q inst A B
  have hq : KloostermanWeilAt q :=
    Nat.recOnPosPrimePosCoprime
      (fun p k hp _hk => kloostermanWeilAt_primePow p k hp)
      kloostermanWeilAt_zero
      kloostermanWeilAt_one
      (fun a b ha hb hcop hA hB =>
        kloostermanWeilAt_mul_coprime a b ha hb hcop hA hB)
      q
  exact hq inst.out A B

/-- ZMod-frequency form of equation (25), with the common divisor weakened
to the first source frequency.  This is the uniform form used when the
second frequency ranges over the dual Voronoi variables in DFI (24). -/
theorem norm_kloostermanSumZMod_le_first_gcd
    (q : ℕ) [NeZero q] (A B : ZMod q) :
    ‖kloostermanSumZMod q A B‖ ≤
      Real.sqrt (Nat.gcd A.val q) * Real.sqrt q *
        (q.divisors.card : ℝ) := by
  have hweil := kloostermanWeilBound_native q A.val B.val
  have hgcd : Nat.gcd (Nat.gcd A.val B.val) q ≤ Nat.gcd A.val q := by
    apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (NeZero.pos q))
    exact Nat.dvd_gcd
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
      (Nat.gcd_dvd_right _ _)
  rw [kloostermanSum_eq_kloostermanSumZMod] at hweil
  simpa only [ZMod.natCast_zmod_val] using hweil.trans (by
    gcongr)

end RiemannZeta.GuthMaynard
