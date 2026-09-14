import Tao2026.ExceptionalCharacterFamilies
import RiemannZeta.GuthMaynard.DFIDivisorEpsilon
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Exact Burgess interface for Tao's exceptional-character sieve

`ExceptionalCharacterFamilies` intentionally exposed a convenient uniform
prefix predicate.  The proof of Lemma 5.1 only needs the sieve prefixes
`floor ((2Z-1)/d)`.  This file records that weaker exact interface and proves
how a source-shaped explicit Burgess estimate supplies it once the elementary
large-prefix and period-range inequalities are available.

No Burgess estimate is asserted here.  `TaoExplicitCubefreeBurgessBound` is a
proposition-valued target for the remaining analytic proof.
-/

namespace Tao2026

open Finset Complex
open scoped BigOperators ComplexConjugate ArithmeticFunction

noncomputable section

/-- Exactly the character prefixes produced after expanding Tao's sieve
weight. -/
def TaoCubefreeSievePrefixBound (R Z : ℕ) (E : ℝ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
    Squarefree q →
    (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent →
    χ ≠ 1 →
    ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      ‖∑ n ∈ Finset.Ioc 0 ((2 * Z - 1) / d), χ (n : ZMod q)‖ ≤ E

/-- The stronger all-prefix interface implies the exact sieve-prefix one. -/
theorem TaoCubefreeCharacterPrefixBound.toSievePrefixBound
    {R Z : ℕ} {E : ℝ}
    (h : TaoCubefreeCharacterPrefixBound Z E) :
    TaoCubefreeSievePrefixBound R Z E := by
  intro q χ hq hqZ hχ d hd hdR
  exact h q χ ((2 * Z - 1) / d) hq hqZ hχ
    ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))

/-- Source-shaped explicit specialization of the cubefree Burgess theorem.
The constant and lower cutoff are explicit parameters; the exponent is
Tao's `1-0.0163`, and the period range is `q ≤ H^3.1`. -/
def TaoExplicitCubefreeBurgessBound (C : ℝ) (H₀ : ℕ) : Prop :=
  ∀ (H q : ℕ) (χ : DirichletCharacter ℂ q),
    H₀ ≤ H →
    Squarefree q →
    (q : ℝ) ≤ (H : ℝ) ^ (31 / 10 : ℝ) →
    χ ≠ 1 →
    ‖∑ n ∈ Finset.Ioc 0 H, χ (n : ZMod q)‖ ≤
      C * (H : ℝ) ^ (1 - taoBurgessSavingExponent)

/-- The small positive exponent used to specialize the published Burgess
estimate at `r = 7`.  It is chosen well inside the numerical margin between
the raw `r = 7`, `q ≤ H^3.1` exponent and Tao's decimal `1 - 0.0163`. -/
def taoBurgessRSevenEpsilon : ℝ := 1 / 2000000

/-- A natural number is cube-free when no prime cube divides it.  This is the
literal modulus condition in Tao's cited Burgess theorem. -/
def TaoCubefree (q : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q

/-- The squarefree periods produced by Tao's exceptional-character family are
in particular cube-free. -/
theorem taoCubefree_of_squarefree {q : ℕ} (hq : Squarefree q) :
    TaoCubefree q := by
  intro p hp hpCube
  apply Nat.squarefree_iff_prime_squarefree.mp hq p hp
  simpa only [pow_two] using
    (pow_dvd_pow p (by omega : 2 ≤ 3)).trans hpCube

/-- A cube-free natural-number modulus is nonzero. -/
theorem TaoCubefree.ne_zero {q : ℕ} (hq : TaoCubefree q) : q ≠ 0 := by
  intro hq0
  exact hq 2 Nat.prime_two (by simp [hq0])

/-- Every divisor of a cube-free modulus is cube-free. -/
theorem TaoCubefree.of_dvd {d q : ℕ} (hq : TaoCubefree q)
    (hd : d ∣ q) : TaoCubefree d := by
  intro p hp hpd
  exact hq p hp (hpd.trans hd)

/-- Evaluation of a changed-level character at a natural number.  The
coprimality indicator is the only difference from the original-level
character. -/
theorem changeLevel_apply_natCast_eq_ite_coprime
    {d q n : ℕ} (χ : DirichletCharacter ℂ d) (hd : d ∣ q) :
    (DirichletCharacter.changeLevel hd χ) (n : ZMod q) =
      if Nat.Coprime n q then χ (n : ZMod d) else 0 := by
  split_ifs with hn
  · have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hd
      (ZMod.unitOfCoprime n hn)
    simp only [ZMod.coe_unitOfCoprime] at h
    rw [ZMod.cast_natCast hd n] at h
    exact h
  · exact MulChar.map_nonunit _
      ((ZMod.isUnit_iff_coprime n q).not.mpr hn)

/-- The divisor sum of the Möbius function is the singleton indicator. -/
theorem sum_moebius_divisors_eq_indicator (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) =
      if n = 1 then 1 else 0 := by
  calc
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) =
        ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
      simp only [ArithmeticFunction.intCoe_apply]
    _ = (1 : ArithmeticFunction ℂ) n := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = if n = 1 then 1 else 0 := ArithmeticFunction.one_apply

/-- Exact Möbius expansion of the coprimality indicator against a fixed
nonzero modulus. -/
theorem coprimeIndicator_eq_sum_moebius_divisors
    (q n : ℕ) (hq : q ≠ 0) :
    (if Nat.Coprime n q then (1 : ℂ) else 0) =
      ∑ d ∈ q.divisors,
        if d ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0 := by
  rw [← Finset.sum_filter]
  have hfilter :
      q.divisors.filter (fun d ↦ d ∣ n) =
        q.divisors.filter (fun d ↦ d ∣ Nat.gcd n q) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hdq, hdn⟩
      exact ⟨hdq, Nat.dvd_gcd hdn (Nat.dvd_of_mem_divisors hdq)⟩
    · rintro ⟨hdq, hdg⟩
      exact ⟨hdq, hdg.trans (Nat.gcd_dvd_left n q)⟩
  rw [hfilter]
  rw [Nat.divisors_filter_dvd_of_dvd hq (Nat.gcd_dvd_right n q)]
  rw [sum_moebius_divisors_eq_indicator (Nat.gcd n q)]

/-- Exact primitive-to-imprimitive prefix identity.  Changing level from
`f` to `q` is expanded by Möbius inversion; after reindexing the multiples
of each divisor `d`, every inner sum is a primitive-level prefix of length
`H/d`. -/
theorem sum_changeLevel_prefix_eq_moebius
    {f q H : ℕ} (χ : DirichletCharacter ℂ f) (hfq : f ∣ q)
    (hq : q ≠ 0) :
    (∑ n ∈ Finset.Ioc 0 H,
        (DirichletCharacter.changeLevel hfq χ) (n : ZMod q)) =
      ∑ d ∈ q.divisors,
        (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod f) *
          (∑ m ∈ Finset.Ioc 0 (H / d), χ (m : ZMod f)) := by
  calc
    (∑ n ∈ Finset.Ioc 0 H,
        (DirichletCharacter.changeLevel hfq χ) (n : ZMod q)) =
        ∑ n ∈ Finset.Ioc 0 H,
          ∑ d ∈ q.divisors,
            if d ∣ n then
              (ArithmeticFunction.moebius d : ℂ) * χ (n : ZMod f)
            else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [changeLevel_apply_natCast_eq_ite_coprime χ hfq]
      calc
        (if Nat.Coprime n q then χ (n : ZMod f) else 0) =
            (if Nat.Coprime n q then (1 : ℂ) else 0) *
              χ (n : ZMod f) := by split_ifs <;> simp
        _ = (∑ d ∈ q.divisors,
              if d ∣ n then
                (ArithmeticFunction.moebius d : ℂ)
              else 0) * χ (n : ZMod f) := by
          rw [← coprimeIndicator_eq_sum_moebius_divisors q n hq]
        _ = ∑ d ∈ q.divisors,
              if d ∣ n then
                (ArithmeticFunction.moebius d : ℂ) * χ (n : ZMod f)
              else 0 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro d hd
          split_ifs <;> simp
    _ = ∑ d ∈ q.divisors,
          ∑ n ∈ Finset.Ioc 0 H,
            if d ∣ n then
              (ArithmeticFunction.moebius d : ℂ) * χ (n : ZMod f)
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ q.divisors,
        (ArithmeticFunction.moebius d : ℂ) * χ (d : ZMod f) *
          (∑ m ∈ Finset.Ioc 0 (H / d), χ (m : ZMod f)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 :=
        ne_zero_of_dvd_ne_zero hq (Nat.dvd_of_mem_divisors hd)
      rw [sum_Ioc_ite_dvd_eq_sum_mul d H hd0
        (fun n ↦ (ArithmeticFunction.moebius d : ℂ) *
          χ (n : ZMod f))]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Nat.cast_mul, map_mul]
      ring

/-- A nonprincipal Dirichlet character sums to zero on the standard
representatives `0, ..., q - 1` of its nonzero modulus. -/
theorem sum_range_dirichletCharacter_eq_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (χne : χ ≠ 1) :
    (∑ n ∈ Finset.range q, χ (n : ZMod q)) = 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
      calc
        (∑ i : Fin (q + 1), χ ((i : ℕ) : ZMod (q + 1))) =
            ∑ a : ZMod (q + 1), χ a := by
          refine Fintype.sum_equiv (ZMod.finEquiv (q + 1)).toEquiv _ _ ?_
          intro i
          congr 1
          calc
            ((i.val : ℕ) : ZMod (q + 1)) =
                (((ZMod.finEquiv (q + 1)) i).val : ZMod (q + 1)) := by
              congr 1
            _ = (ZMod.finEquiv (q + 1)) i :=
              ZMod.natCast_zmod_val _
        _ = 0 := MulChar.sum_eq_zero_of_ne_one χne

/-- Reindex the positive natural interval `1, ..., H` as the shifted range
`0, ..., H - 1`. -/
theorem sum_Ioc_zero_eq_sum_range_succ
    {M : Type*} [AddCommMonoid M] (H : ℕ) (f : ℕ → M) :
    (∑ n ∈ Finset.Ioc 0 H, f n) =
      ∑ n ∈ Finset.range H, f (n + 1) := by
  refine Finset.sum_bij (fun n _ ↦ n - 1) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_range]
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Ioc] at ha hb
    change a - 1 = b - 1 at hab
    omega
  · intro n hn
    simp only [Finset.mem_range] at hn
    refine ⟨n + 1, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · change (n + 1) - 1 = n
      omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    change f n = f ((n - 1) + 1)
    rw [Nat.sub_add_cancel hn.1]

/-- The shifted complete period `1, ..., q` of a nonprincipal Dirichlet
character also sums to zero. -/
theorem sum_shifted_range_dirichletCharacter_eq_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (χne : χ ≠ 1) :
    (∑ n ∈ Finset.range q, χ ((n + 1 : ℕ) : ZMod q)) = 0 := by
  have hendpoint : χ ((q : ℕ) : ZMod q) = χ ((0 : ℕ) : ZMod q) := by
    simp
  have hshift :
      (∑ n ∈ Finset.range q, χ ((n + 1 : ℕ) : ZMod q)) =
        ∑ n ∈ Finset.range q, χ (n : ZMod q) := by
    calc
      (∑ n ∈ Finset.range q, χ ((n + 1 : ℕ) : ZMod q)) =
          (∑ n ∈ Finset.range (q + 1), χ (n : ZMod q)) -
            χ ((0 : ℕ) : ZMod q) := by
        rw [Finset.sum_range_succ']
        abel
      _ = ∑ n ∈ Finset.range q, χ (n : ZMod q) := by
        rw [Finset.sum_range_succ, hendpoint]
        abel
  rw [hshift]
  exact sum_range_dirichletCharacter_eq_zero χ χne

/-- One complete positive period of a nonprincipal Dirichlet character sums
to zero. -/
theorem sum_dirichletCharacter_period_eq_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (χne : χ ≠ 1) :
    (∑ n ∈ Finset.Ioc 0 q, χ (n : ZMod q)) = 0 := by
  rw [sum_Ioc_zero_eq_sum_range_succ]
  exact sum_shifted_range_dirichletCharacter_eq_zero χ χne

/-- Adding a multiple of the level does not change a Dirichlet-character
value at a natural number. -/
theorem dirichletCharacter_shift_mul_level
    {q a k : ℕ} (χ : DirichletCharacter ℂ q) :
    χ ((k * q + a : ℕ) : ZMod q) = χ (a : ZMod q) := by
  congr 1
  push_cast
  simp

/-- Any natural number of complete shifted periods of a nonprincipal
Dirichlet character has sum zero. -/
theorem sum_dirichletCharacter_blocks_eq_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (χne : χ ≠ 1) :
    ∀ k : ℕ,
      (∑ n ∈ Finset.range (k * q), χ ((n + 1 : ℕ) : ZMod q)) = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add]
      calc
        (∑ x ∈ Finset.range q,
            χ ((k * q + x + 1 : ℕ) : ZMod q)) =
            ∑ x ∈ Finset.range q,
              χ ((x + 1 : ℕ) : ZMod q) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Nat.add_assoc, dirichletCharacter_shift_mul_level]
        _ = 0 := sum_shifted_range_dirichletCharacter_eq_zero χ χne

/-- Exact periodic reduction of every positive Dirichlet-character prefix:
all complete periods cancel, leaving the prefix of length `H % q`. -/
theorem sum_dirichletCharacter_prefix_eq_mod
    {q H : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (χne : χ ≠ 1) :
    (∑ n ∈ Finset.Ioc 0 H, χ (n : ZMod q)) =
      ∑ n ∈ Finset.Ioc 0 (H % q), χ (n : ZMod q) := by
  rw [sum_Ioc_zero_eq_sum_range_succ,
    sum_Ioc_zero_eq_sum_range_succ]
  conv_lhs =>
    rw [show H = (H / q) * q + H % q by
      simpa [Nat.mul_comm] using (Nat.div_add_mod H q).symm]
  rw [Finset.sum_range_add,
    sum_dirichletCharacter_blocks_eq_zero χ χne, zero_add]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Nat.add_assoc, dirichletCharacter_shift_mul_level]

/-- The triangle inequality and `|χ(n)| ≤ 1` give the exact trivial
bound by the number of terms in a positive prefix. -/
theorem norm_dirichletCharacter_prefix_le_length
    {q H : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖∑ n ∈ Finset.Ioc 0 H, χ (n : ZMod q)‖ ≤ (H : ℝ) := by
  calc
    ‖∑ n ∈ Finset.Ioc 0 H, χ (n : ZMod q)‖ ≤
        ∑ n ∈ Finset.Ioc 0 H, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc 0 H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact DirichletCharacter.norm_le_one χ _
    _ = (H : ℝ) := by simp [Nat.card_Ioc]

/-- The exact `r = 7` form of the published cubefree Burgess estimate used by
Tao: `H^(6/7) q^(2/49+ε)`.  Unlike the downstream decimal contract, this
retains the two factors appearing in the cited theorem. -/
def TaoCubefreeBurgessRSevenBound (A ε : ℝ) (H₀ : ℕ) : Prop :=
  ∀ (H q : ℕ) (χ : DirichletCharacter ℂ q),
    H₀ ≤ H →
    TaoCubefree q →
    χ ≠ 1 →
    ‖∑ n ∈ Finset.Ioc 0 H, χ (n : ZMod q)‖ ≤
      A * (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ (2 / 49 + ε)

/-- The source-shaped `r = 7` Burgess target restricted to primitive
characters.  There is no large-`H` cutoff: this is the uniform published
estimate before Tao imposes `q ≤ H^3.1`. -/
def TaoPrimitiveCubefreeBurgessRSevenBound (A ε : ℝ) : Prop :=
  ∀ (H q : ℕ) (χ : DirichletCharacter ℂ q),
    TaoCubefree q →
    DirichletCharacter.IsPrimitive χ →
    χ ≠ 1 →
    ‖∑ n ∈ Finset.Ioc 0 H, χ (n : ZMod q)‖ ≤
      A * (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ (2 / 49 + ε)

/-- The genuinely nontrivial range of the primitive `r = 7` Burgess
estimate.  Periodicity removes `H ≥ q`; the strict lower condition is exactly
the range in which the trivial estimate `|S(H)| ≤ H` does not already imply
the desired two-factor bound with constant at least one. -/
def TaoPrimitiveCubefreeBurgessRSevenCoreBound (A ε : ℝ) : Prop :=
  ∀ (H q : ℕ) (χ : DirichletCharacter ℂ q),
    TaoCubefree q →
    DirichletCharacter.IsPrimitive χ →
    χ ≠ 1 →
    H < q →
    (q : ℝ) ^ (2 / 49 + ε) < (H : ℝ) ^ (1 / 7 : ℝ) →
    ‖∑ n ∈ Finset.Ioc 0 H, χ (n : ZMod q)‖ ≤
      A * (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ (2 / 49 + ε)

/-- The factor-shaped lower condition in the core Burgess interface is
equivalent to the familiar range `q^(2/7 + 7ε) < H`. -/
theorem taoBurgess_core_lower_iff (q H : ℕ) (ε : ℝ) :
    (q : ℝ) ^ (2 / 49 + ε) < (H : ℝ) ^ (1 / 7 : ℝ) ↔
      (q : ℝ) ^ (2 / 7 + 7 * ε) < (H : ℝ) := by
  constructor
  · intro h
    have h' := Real.rpow_lt_rpow
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ q) _) h
      (by norm_num : (0 : ℝ) < 7)
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ q),
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ H)] at h'
    have hqexp : (2 / 49 + ε) * (7 : ℝ) = 2 / 7 + 7 * ε := by ring
    have hHexp : (1 / 7 : ℝ) * 7 = 1 := by norm_num
    rw [hqexp, hHexp, Real.rpow_one] at h'
    exact h'
  · intro h
    have h' := Real.rpow_lt_rpow
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ q) _) h
      (by norm_num : (0 : ℝ) < 1 / 7)
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ q)] at h'
    have hqexp : (2 / 7 + 7 * ε) * (1 / 7 : ℝ) = 2 / 49 + ε := by ring
    rw [hqexp] at h'
    exact h'

/-- Periodicity and the trivial character bound extend the core primitive
estimate to every prefix, without increasing a constant `A ≥ 1`. -/
theorem TaoPrimitiveCubefreeBurgessRSevenCoreBound.toAllPrefixes
    {A ε : ℝ} (hA : 1 ≤ A)
    (hcore : TaoPrimitiveCubefreeBurgessRSevenCoreBound A ε) :
    TaoPrimitiveCubefreeBurgessRSevenBound A ε := by
  intro H q χ hq hprimitive hχ
  have hq0 : q ≠ 0 := hq.ne_zero
  letI : NeZero q := ⟨hq0⟩
  rw [sum_dirichletCharacter_prefix_eq_mod χ hχ]
  have hmod_le : H % q ≤ H := Nat.mod_le H q
  have hqpow_nonneg :
      0 ≤ (q : ℝ) ^ (2 / 49 + ε) := Real.rpow_nonneg (by positivity) _
  by_cases hmod0 : H % q = 0
  · simp [hmod0]
    positivity
  have hmod_pos : (0 : ℝ) < ((H % q : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hmod0
  have hmod_lt : H % q < q := Nat.mod_lt H (Nat.pos_of_ne_zero hq0)
  have hmodpow_le_Hpow :
      ((H % q : ℕ) : ℝ) ^ (6 / 7 : ℝ) ≤
        (H : ℝ) ^ (6 / 7 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmod_le) (by norm_num)
  by_cases hnontrivial :
      (q : ℝ) ^ (2 / 49 + ε) <
        ((H % q : ℕ) : ℝ) ^ (1 / 7 : ℝ)
  · have hbound := hcore (H % q) q χ hq hprimitive hχ
        hmod_lt hnontrivial
    calc
      ‖∑ n ∈ Finset.Ioc 0 (H % q), χ (n : ZMod q)‖ ≤
          A * ((H % q : ℕ) : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ (2 / 49 + ε) := hbound
      _ ≤ A * (H : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ (2 / 49 + ε) := by
        gcongr
  · have hsmall :
        ((H % q : ℕ) : ℝ) ^ (1 / 7 : ℝ) ≤
          (q : ℝ) ^ (2 / 49 + ε) := le_of_not_gt hnontrivial
    have hsplit :
        ((H % q : ℕ) : ℝ) =
          ((H % q : ℕ) : ℝ) ^ (6 / 7 : ℝ) *
            ((H % q : ℕ) : ℝ) ^ (1 / 7 : ℝ) := by
      calc
        ((H % q : ℕ) : ℝ) =
            ((H % q : ℕ) : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = ((H % q : ℕ) : ℝ) ^
              ((6 / 7 : ℝ) + (1 / 7 : ℝ)) := by norm_num
        _ = ((H % q : ℕ) : ℝ) ^ (6 / 7 : ℝ) *
              ((H % q : ℕ) : ℝ) ^ (1 / 7 : ℝ) :=
            Real.rpow_add hmod_pos _ _
    calc
      ‖∑ n ∈ Finset.Ioc 0 (H % q), χ (n : ZMod q)‖ ≤
          ((H % q : ℕ) : ℝ) :=
        norm_dirichletCharacter_prefix_le_length χ
      _ = ((H % q : ℕ) : ℝ) ^ (6 / 7 : ℝ) *
            ((H % q : ℕ) : ℝ) ^ (1 / 7 : ℝ) := hsplit
      _ ≤ ((H % q : ℕ) : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ (2 / 49 + ε) := by
        exact mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg (by positivity) _)
      _ ≤ (H : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ (2 / 49 + ε) := by
        exact mul_le_mul_of_nonneg_right hmodpow_le_Hpow hqpow_nonneg
      _ ≤ A * (H : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ (2 / 49 + ε) := by
        apply mul_le_mul_of_nonneg_right _ hqpow_nonneg
        calc
          (H : ℝ) ^ (6 / 7 : ℝ) =
              1 * (H : ℝ) ^ (6 / 7 : ℝ) := by ring
          _ ≤ A * (H : ℝ) ^ (6 / 7 : ℝ) := by
            exact mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (by positivity) _)

/-- A primitive-character Burgess estimate at half the requested epsilon
implies the all-character estimate.  Möbius inversion costs at most the
divisor count of the ambient modulus, which is absorbed into its other half
by the proved pointwise divisor-epsilon bound. -/
theorem TaoPrimitiveCubefreeBurgessRSevenBound.toAllCharacters
    {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε)
    (hburgess : TaoPrimitiveCubefreeBurgessRSevenBound A (ε / 2)) :
    TaoCubefreeBurgessRSevenBound
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant (ε / 2) * A)
      ε 0 := by
  intro H q χ hH hq hχ
  have hq0 : q ≠ 0 := hq.ne_zero
  letI : NeZero q := ⟨hq0⟩
  let ψ := χ.primitiveCharacter
  have hψPrimitive : DirichletCharacter.IsPrimitive ψ :=
    χ.primitiveCharacter_isPrimitive
  have hψNonprincipal : ψ ≠ 1 := by
    intro hψ
    have hψ' : χ.primitiveCharacter = 1 := by simpa [ψ] using hψ
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, hψ',
      DirichletCharacter.changeLevel_one]
  have hconductorCubefree : TaoCubefree χ.conductor :=
    hq.of_dvd χ.conductor_dvd_level
  have hexact := sum_changeLevel_prefix_eq_moebius
    χ.primitiveCharacter χ.conductor_dvd_level (H := H) hq0
  rw [χ.changeLevel_primitiveCharacter] at hexact
  rw [hexact]
  calc
    ‖∑ d ∈ q.divisors,
        (ArithmeticFunction.moebius d : ℂ) *
          ψ (d : ZMod χ.conductor) *
          (∑ m ∈ Finset.Ioc 0 (H / d),
            ψ (m : ZMod χ.conductor))‖ ≤
        ∑ d ∈ q.divisors,
          ‖(ArithmeticFunction.moebius d : ℂ) *
            ψ (d : ZMod χ.conductor) *
            (∑ m ∈ Finset.Ioc 0 (H / d),
              ψ (m : ZMod χ.conductor))‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ q.divisors,
          A * (H : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ (2 / 49 + ε / 2) := by
      apply Finset.sum_le_sum
      intro d hd
      have hprefix := hburgess (H / d) χ.conductor ψ
        hconductorCubefree hψPrimitive hψNonprincipal
      have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast, ← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hψ : ‖ψ (d : ZMod χ.conductor)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one ψ _
      have hHd : ((H / d : ℕ) : ℝ) ^ (6 / 7 : ℝ) ≤
          (H : ℝ) ^ (6 / 7 : ℝ) := by
        exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast Nat.div_le_self H d) (by norm_num)
      have hcondq :
          (χ.conductor : ℝ) ^ (2 / 49 + ε / 2) ≤
            (q : ℝ) ^ (2 / 49 + ε / 2) := by
        apply Real.rpow_le_rpow (by positivity)
        · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq0)
            χ.conductor_dvd_level
        · positivity
      rw [norm_mul, norm_mul]
      calc
        ‖(ArithmeticFunction.moebius d : ℂ)‖ *
            ‖ψ (d : ZMod χ.conductor)‖ *
            ‖∑ m ∈ Finset.Ioc 0 (H / d),
              ψ (m : ZMod χ.conductor)‖ ≤
            1 * 1 *
              (A * ((H / d : ℕ) : ℝ) ^ (6 / 7 : ℝ) *
                (χ.conductor : ℝ) ^ (2 / 49 + ε / 2)) := by
          gcongr
        _ ≤ A * (H : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ (2 / 49 + ε / 2) := by
          simp only [one_mul]
          gcongr
    _ = (q.divisors.card : ℝ) *
          (A * (H : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ (2 / 49 + ε / 2)) := by simp
    _ ≤ (RiemannZeta.GuthMaynard.divisorEpsilonConstant (ε / 2) *
          (q : ℝ) ^ (ε / 2)) *
          (A * (H : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ (2 / 49 + ε / 2)) := by
      gcongr
      exact RiemannZeta.GuthMaynard.card_divisors_le_const_mul_rpow
        (by linarith) hq0
    _ = (RiemannZeta.GuthMaynard.divisorEpsilonConstant (ε / 2) * A) *
          (H : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ (2 / 49 + ε) := by
      have hqPos : (0 : ℝ) < q := by
        exact_mod_cast Nat.pos_of_ne_zero hq0
      have hpow :
          (q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (2 / 49 + ε / 2) =
            (q : ℝ) ^ (2 / 49 + ε) := by
        rw [← Real.rpow_add hqPos]
        congr 1
        ring
      calc
        (RiemannZeta.GuthMaynard.divisorEpsilonConstant (ε / 2) *
            (q : ℝ) ^ (ε / 2)) *
            (A * (H : ℝ) ^ (6 / 7 : ℝ) *
              (q : ℝ) ^ (2 / 49 + ε / 2)) =
            (RiemannZeta.GuthMaynard.divisorEpsilonConstant (ε / 2) * A) *
              (H : ℝ) ^ (6 / 7 : ℝ) *
                ((q : ℝ) ^ (ε / 2) *
                  (q : ℝ) ^ (2 / 49 + ε / 2)) := by ring
        _ = _ := by rw [hpow]

/-- At `r = 7`, the exponents in the published formula are exactly `6/7`
and `2/49`. -/
theorem taoBurgess_rSeven_source_exponents :
    (1 - 1 / (7 : ℝ) = 6 / 7) ∧
      (((7 : ℝ) + 1) / (4 * (7 : ℝ) ^ 2) = 2 / 49) := by
  norm_num

/-- Exact arithmetic behind Tao's sentence "take `r = 7` and `ε'`
sufficiently small". -/
theorem taoBurgess_rSeven_exponent_le :
    (6 / 7 : ℝ) + (31 / 10 : ℝ) *
        (2 / 49 + taoBurgessRSevenEpsilon) ≤
      1 - taoBurgessSavingExponent := by
  norm_num [taoBurgessRSevenEpsilon, taoBurgessSavingExponent]

/-- The cited `r = 7` Burgess estimate at the fixed positive epsilon implies
the exact decimal theorem used everywhere downstream.  Thus the remaining
analytic task is the published two-factor character-sum estimate itself, not
any unverified exponent conversion. -/
theorem TaoCubefreeBurgessRSevenBound.toExplicit
    {A : ℝ} {H₀ : ℕ} (hA : 0 ≤ A)
    (hburgess : TaoCubefreeBurgessRSevenBound
      A taoBurgessRSevenEpsilon H₀) :
    TaoExplicitCubefreeBurgessBound A (max H₀ 1) := by
  intro H q χ hH hq hqH hχ
  have hHNat : 1 ≤ H := (Nat.le_max_right H₀ 1).trans hH
  have hHOne : (1 : ℝ) ≤ H := by exact_mod_cast hHNat
  have hHPos : (0 : ℝ) < H := zero_lt_one.trans_le hHOne
  have hqNonneg : (0 : ℝ) ≤ q := by positivity
  have hqExponentNonneg :
      (0 : ℝ) ≤ 2 / 49 + taoBurgessRSevenEpsilon := by
    norm_num [taoBurgessRSevenEpsilon]
  have hqPower :
      (q : ℝ) ^ (2 / 49 + taoBurgessRSevenEpsilon) ≤
        ((H : ℝ) ^ (31 / 10 : ℝ)) ^
          (2 / 49 + taoBurgessRSevenEpsilon) :=
    Real.rpow_le_rpow hqNonneg hqH hqExponentNonneg
  have hmain := hburgess H q χ
    ((Nat.le_max_left H₀ 1).trans hH) (taoCubefree_of_squarefree hq) hχ
  calc
    ‖∑ n ∈ Finset.Ioc 0 H, χ (n : ZMod q)‖ ≤
        A * (H : ℝ) ^ (6 / 7 : ℝ) *
          (q : ℝ) ^ (2 / 49 + taoBurgessRSevenEpsilon) := hmain
    _ ≤ A * (H : ℝ) ^ (6 / 7 : ℝ) *
          (((H : ℝ) ^ (31 / 10 : ℝ)) ^
            (2 / 49 + taoBurgessRSevenEpsilon)) := by
      exact mul_le_mul_of_nonneg_left hqPower
        (mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg H) _))
    _ = A * (H : ℝ) ^
          ((6 / 7 : ℝ) + (31 / 10 : ℝ) *
            (2 / 49 + taoBurgessRSevenEpsilon)) := by
      rw [← Real.rpow_mul hHPos.le, mul_assoc, ← Real.rpow_add hHPos]
    _ ≤ A * (H : ℝ) ^ (1 - taoBurgessSavingExponent) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hHOne
          taoBurgess_rSeven_exponent_le) hA

/-- A primitive-character proof of the cited Burgess estimate, with half of
the fixed epsilon reserved for the imprimitive reduction, supplies Tao's
decimal all-character contract directly. -/
theorem TaoPrimitiveCubefreeBurgessRSevenBound.toExplicit
    {A : ℝ} (hA : 0 ≤ A)
    (hburgess : TaoPrimitiveCubefreeBurgessRSevenBound A
      (taoBurgessRSevenEpsilon / 2)) :
    TaoExplicitCubefreeBurgessBound
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant
        (taoBurgessRSevenEpsilon / 2) * A) 1 := by
  have hε : 0 < taoBurgessRSevenEpsilon := by
    norm_num [taoBurgessRSevenEpsilon]
  have hall := hburgess.toAllCharacters hA hε
  have hconstant :
      0 ≤ RiemannZeta.GuthMaynard.divisorEpsilonConstant
          (taoBurgessRSevenEpsilon / 2) * A :=
    mul_nonneg
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos _).le hA
  simpa using hall.toExplicit hconstant

/-- An explicit Burgess bound yields all sieve prefixes once their lengths
are beyond its cutoff and the `Z^3.09` period envelope lies in their
`H^3.1` range. -/
theorem TaoExplicitCubefreeBurgessBound.toSievePrefixBound
    {C : ℝ} {H₀ R Z : ℕ}
    (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hlarge : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      H₀ ≤ (2 * Z - 1) / d)
    (hrange : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      (Z : ℝ) ^ taoBurgessPeriodExponent ≤
        (((2 * Z - 1) / d : ℕ) : ℝ) ^ (31 / 10 : ℝ)) :
    TaoCubefreeSievePrefixBound R Z
      (C * (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent)) := by
  intro q χ hq hqZ hχ d hd hdR
  have hprefix := hburgess ((2 * Z - 1) / d) q χ
    (hlarge d hd hdR) hq (hqZ.trans (hrange d hd hdR)) hχ
  refine hprefix.trans ?_
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow
  · exact_mod_cast Nat.zero_le ((2 * Z - 1) / d)
  · exact_mod_cast (Nat.div_le_self (2 * Z - 1) d).trans
      (Nat.sub_le (2 * Z) 1)
  · norm_num [taoBurgessSavingExponent]

/-- Complete finite Lemma 5.1 reduction using only the exact sieve-prefix
Burgess interface. -/
theorem sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily_of_sieveBurgess
    {q₁ R Z : ℕ} (hR : 1 < R) (hRZ : R < Z)
    (hq₁ : Squarefree q₁)
    (W : Finset (TaoExceptionalCharacterDatum q₁ Z)) (E : ℝ)
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hE : 0 ≤ E)
    (hsep : IsSeparatedTaoExceptionalFamily W)
    (hburgess : TaoCubefreeSievePrefixBound R Z E) :
    ∑ a ∈ W,
        ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤
      ((((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
          (R : ℝ) * (1 + Real.log R) ^ 3) +
        ((W.card - 1 : ℕ) : ℝ) *
          (((R : ℝ) * (1 + Real.log R) ^ 3) * E)) /
        (taoDyadicPrimeBand Z).card := by
  apply sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily
    hR hRZ W E hZ hE
  intro a ha b hb hba d hd hdR
  exact hburgess (taoExceptionalPairPeriod a b)
    (taoExceptionalPairCharacter a b)
    (taoExceptionalPairPeriod_squarefree a b hq₁)
    (taoExceptionalPairPeriod_cast_le_rpow a b
      (Nat.pos_of_ne_zero hq₁.ne_zero))
    (taoExceptionalPairCharacter_ne_one_of_changeLevel_ne a b
      (hsep a ha b hb hba)) d hd hdR

/-- Source-shaped explicit Burgess theorem plus the two elementary prefix
side conditions imply the complete finite exceptional-family estimate. -/
theorem sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily_of_explicitBurgess
    {C : ℝ} {H₀ q₁ R Z : ℕ}
    (hC : 0 ≤ C)
    (hR : 1 < R) (hRZ : R < Z)
    (hq₁ : Squarefree q₁)
    (W : Finset (TaoExceptionalCharacterDatum q₁ Z))
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hsep : IsSeparatedTaoExceptionalFamily W)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (hlarge : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      H₀ ≤ (2 * Z - 1) / d)
    (hrange : ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
      (Z : ℝ) ^ taoBurgessPeriodExponent ≤
        (((2 * Z - 1) / d : ℕ) : ℝ) ^ (31 / 10 : ℝ)) :
    ∑ a ∈ W,
        ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤
      ((((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
          (R : ℝ) * (1 + Real.log R) ^ 3) +
        ((W.card - 1 : ℕ) : ℝ) *
          (((R : ℝ) * (1 + Real.log R) ^ 3) *
            (C * (2 * Z : ℝ) ^
              (1 - taoBurgessSavingExponent)))) /
        (taoDyadicPrimeBand Z).card := by
  apply sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily_of_sieveBurgess
    hR hRZ hq₁ W
      (C * (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent)) hZ
  · positivity
  · exact hsep
  · exact hburgess.toSievePrefixBound hC hlarge hrange

end

end Tao2026
