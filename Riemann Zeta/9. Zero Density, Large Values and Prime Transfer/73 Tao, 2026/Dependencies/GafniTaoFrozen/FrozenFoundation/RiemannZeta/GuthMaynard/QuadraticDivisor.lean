import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Totient
import RiemannZeta.GuthMaynard.SmoothZetaAFE

open Complex Finset
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-!
# The finite entry layer for the DFI quadratic-divisor theorem

Hughes--Young reduce the off-diagonal part of their twisted fourth moment to
shifted sums

`sum_{a*m - b*n = r} d(m) d(n) f(a*m, b*n)`.

This file fixes that source object in Lean and proves the exact finite
shift decomposition used before the analytic Duke--Friedlander--Iwaniec
estimate.  It also defines the complete Kloosterman and Ramanujan sums that
occur after applying the divisor Voronoi formula.  The elementary estimates
below are deliberately labelled as trivial bounds; the square-root Weil bound
and the divisor Voronoi formula are separate analytic obligations and are not
postulated here.
-/

/-- The integer shift `a*m - b*n` in the quadratic-divisor problem. -/
def quadraticDivisorShift (a b m n : ℕ) : ℤ :=
  ((a * m : ℕ) : ℤ) - ((b * n : ℕ) : ℤ)

theorem quadraticDivisorShift_eq_zero_iff (a b m n : ℕ) :
    quadraticDivisorShift a b m n = 0 ↔ a * m = b * n := by
  unfold quadraticDivisorShift
  rw [sub_eq_zero]
  exact_mod_cast Iff.rfl

/-- The divisor weight in the DFI shifted convolution. -/
noncomputable def divisorWeight (n : ℕ) : ℂ :=
  (n.divisors.card : ℂ)

/-- A finite, source-shaped DFI shifted divisor sum.  The variables `m,n`
are positive, `a*m-b*n=r`, and the test function is evaluated at the scaled
arguments `(a*m,b*n)`. -/
noncomputable def finiteQuadraticDivisorSum
    (a b M N : ℕ) (r : ℤ) (f : ℕ → ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
    if quadraticDivisorShift a b m n = r then
      divisorWeight m * divisorWeight n * f (a * m) (b * n)
    else 0

/-- The complete finite off-diagonal contribution before estimating any
shifted convolution. -/
noncomputable def finiteQuadraticDivisorOffDiagonal
    (a b M N : ℕ) (f : ℕ → ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
    if quadraticDivisorShift a b m n = 0 then 0
    else divisorWeight m * divisorWeight n * f (a * m) (b * n)

lemma quadraticDivisorShift_mem_interval
    {a b M N m n : ℕ} (hm : m ∈ Finset.Icc 1 M)
    (hn : n ∈ Finset.Icc 1 N) :
    quadraticDivisorShift a b m n ∈
      Finset.Icc (-(b * N : ℤ)) (a * M : ℤ) := by
  rw [Finset.mem_Icc]
  have hmUpper : a * m ≤ a * M :=
    Nat.mul_le_mul_left a (Finset.mem_Icc.mp hm).2
  have hnUpper : b * n ≤ b * N :=
    Nat.mul_le_mul_left b (Finset.mem_Icc.mp hn).2
  have hmUpperZ : ((a * m : ℕ) : ℤ) ≤ ((a * M : ℕ) : ℤ) := by
    exact_mod_cast hmUpper
  have hnUpperZ : ((b * n : ℕ) : ℤ) ≤ ((b * N : ℕ) : ℤ) := by
    exact_mod_cast hnUpper
  constructor
  · dsimp [quadraticDivisorShift]
    omega
  · dsimp [quadraticDivisorShift]
    omega

/-- Exact partition of the finite off-diagonal into its nonzero determinant
shifts.  This is the finite combinatorial bridge from the AFE expansion to
the family of DFI shifted sums. -/
theorem finiteQuadraticDivisorOffDiagonal_eq_sum_shifts
    (a b M N : ℕ) (f : ℕ → ℕ → ℂ) :
    finiteQuadraticDivisorOffDiagonal a b M N f =
      ∑ r ∈ Finset.Icc (-(b * N : ℤ)) (a * M : ℤ),
        if r = 0 then 0 else finiteQuadraticDivisorSum a b M N r f := by
  let pairs := Finset.Icc 1 M ×ˢ Finset.Icc 1 N
  let shifts := Finset.Icc (-(b * N : ℤ)) (a * M : ℤ)
  let term : ℕ × ℕ → ℂ := fun p =>
    if quadraticDivisorShift a b p.1 p.2 = 0 then 0
    else divisorWeight p.1 * divisorWeight p.2 * f (a * p.1) (b * p.2)
  have hMaps : ∀ p ∈ pairs, quadraticDivisorShift a b p.1 p.2 ∈ shifts := by
    intro p hp
    exact quadraticDivisorShift_mem_interval
      (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2
  have hFiber := Finset.sum_fiberwise_of_maps_to hMaps term
  have hLeft : finiteQuadraticDivisorOffDiagonal a b M N f =
      ∑ p ∈ pairs, term p := by
    unfold finiteQuadraticDivisorOffDiagonal
    simp only [pairs, term, Finset.sum_product]
  rw [hLeft, ← hFiber]
  change (∑ r ∈ shifts,
      ∑ p ∈ pairs with quadraticDivisorShift a b p.1 p.2 = r, term p) =
    ∑ r ∈ shifts, if r = 0 then 0 else finiteQuadraticDivisorSum a b M N r f
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp only [if_true]
    apply Finset.sum_eq_zero
    intro p hp
    have hShift := (Finset.mem_filter.mp hp).2
    simp [term, hShift]
  · simp only [hr0, if_false]
    unfold finiteQuadraticDivisorSum
    rw [Finset.sum_filter]
    simp only [pairs, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hShift : quadraticDivisorShift a b m n = r
    · simp [hShift, hr0, term]
    · simp [hShift]

/-- The complete Kloosterman sum
`S(m,n;q) = sum_{d mod q}^* e((m*d+n*d⁻¹)/q)` in Mathlib's standard
`ZMod q` additive-character normalization. -/
noncomputable def kloostermanSum (q m n : ℕ) [NeZero q] : ℂ :=
  ∑ d : (ZMod q)ˣ,
    ZMod.stdAddChar
      ((m : ZMod q) * (d : ZMod q) + (n : ZMod q) * (↑(d⁻¹) : ZMod q))

/-- The same complete Kloosterman sum with both frequencies represented
directly in `ZMod q`.  This is the convenient form for finite Fourier
orthogonality in the first frequency. -/
noncomputable def kloostermanSumZMod (q : ℕ) [NeZero q]
    (m n : ZMod q) : ℂ :=
  ∑ d : (ZMod q)ˣ,
    ZMod.stdAddChar
      (m * (d : ZMod q) + n * (↑(d⁻¹) : ZMod q))

theorem kloostermanSum_eq_kloostermanSumZMod (q m n : ℕ) [NeZero q] :
    kloostermanSum q m n =
      kloostermanSumZMod q (m : ZMod q) (n : ZMod q) := rfl

/-- The Ramanujan sum is the zero second-frequency specialization of the
complete Kloosterman sum. -/
noncomputable def ramanujanSum (q h : ℕ) [NeZero q] : ℂ :=
  kloostermanSum q h 0

theorem kloostermanSum_zero_right (q h : ℕ) [NeZero q] :
    kloostermanSum q h 0 = ramanujanSum q h := rfl

/-- Inversion of the unit variable exchanges the two Kloosterman
frequencies. -/
theorem kloostermanSum_comm (q m n : ℕ) [NeZero q] :
    kloostermanSum q m n = kloostermanSum q n m := by
  unfold kloostermanSum
  refine Fintype.sum_equiv (Equiv.inv (ZMod q)ˣ) _ _ (fun d => ?_)
  simp only [Equiv.inv_apply]
  rw [inv_inv]
  apply congrArg ZMod.stdAddChar
  ring

private lemma zmod_stdAddChar_star (q : ℕ) [NeZero q] (y : ZMod q) :
    star (ZMod.stdAddChar y : ℂ) =
      (ZMod.stdAddChar (-y) : ℂ) := by
  have hq : 0 < ringChar (ZMod q) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne q)
  calc
    star (ZMod.stdAddChar y : ℂ) =
        starRingEnd ℂ (ZMod.stdAddChar y) := rfl
    _ = (ZMod.stdAddChar⁻¹) y := AddChar.starComp_apply hq y
    _ = (ZMod.stdAddChar (-y) : ℂ) := AddChar.inv_apply _ _

private lemma zmod_stdAddChar_orthogonality
    (q : ℕ) [NeZero q] (a b : ZMod q) :
    (∑ x : ZMod q,
      star (ZMod.stdAddChar (-(a * x)) : ℂ) *
        (ZMod.stdAddChar (-(b * x)) : ℂ)) =
      if a = b then (q : ℂ) else 0 := by
  simp_rw [zmod_stdAddChar_star]
  simp only [neg_neg, ← ZMod.stdAddChar.map_add_eq_mul]
  have hsum (t : ZMod q) :
      (∑ x : ZMod q, (ZMod.stdAddChar (t * x) : ℂ)) =
        if t = 0 then (q : ℂ) else 0 := by
    split_ifs with ht
    · subst t
      simp [ZMod.card]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)
  calc
    (∑ x : ZMod q,
        ZMod.stdAddChar (a * x + -(b * x))) =
        ∑ x : ZMod q, ZMod.stdAddChar ((a - b) * x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      congr 1
      ring
    _ = if a - b = 0 then (q : ℂ) else 0 := hsum (a - b)
    _ = if a = b then (q : ℂ) else 0 := by
      by_cases h : a = b
      · subst b
        simp
      · have hab : a - b ≠ 0 := sub_ne_zero.mpr h
        simp [h, hab]

private lemma zmod_stdAddChar_mul_orthogonality
    (q : ℕ) [NeZero q] (a b : ZMod q) :
    (∑ x : ZMod q,
      star (ZMod.stdAddChar (a * x) : ℂ) *
        (ZMod.stdAddChar (b * x) : ℂ)) =
      if a = b then (q : ℂ) else 0 := by
  simpa only [neg_mul, neg_neg, neg_inj] using
    zmod_stdAddChar_orthogonality q (-a) (-b)

private lemma zmod_stdAddChar_mul_orthogonality_right
    (q : ℕ) [NeZero q] (a b : ZMod q) :
    (∑ x : ZMod q,
      star (ZMod.stdAddChar (x * a) : ℂ) *
        (ZMod.stdAddChar (x * b) : ℂ)) =
      if a = b then (q : ℂ) else 0 := by
  simpa only [mul_comm] using zmod_stdAddChar_mul_orthogonality q a b

/-- Exact Parseval identity for Mathlib's unnormalised discrete Fourier
transform on `ZMod q`.  This gives average square-root cancellation for
complete exponential sums.  It is not the pointwise Weil bound required by
the DFI argument. -/
theorem zmod_dft_parseval (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) :
    (∑ k : ZMod q, star (ZMod.dft Φ k) * ZMod.dft Φ k) =
      (q : ℂ) * ∑ j : ZMod q, star (Φ j) * Φ j := by
  simp only [ZMod.dft_apply]
  simp_rw [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum]
  simp only [smul_eq_mul]
  calc
    (∑ x, ∑ j, ∑ i,
        star (ZMod.stdAddChar (-(j * x))) * star (Φ j) *
          (ZMod.stdAddChar (-(i * x)) * Φ i)) =
        ∑ j, ∑ i, ∑ x,
          star (ZMod.stdAddChar (-(j * x))) * star (Φ j) *
            (ZMod.stdAddChar (-(i * x)) * Φ i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, (star (Φ j) * Φ i) *
          ∑ x, star (ZMod.stdAddChar (-(j * x))) *
            ZMod.stdAddChar (-(i * x)) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ j, ∑ i, (star (Φ j) * Φ i) *
          (if j = i then (q : ℂ) else 0) := by
      simp_rw [zmod_stdAddChar_orthogonality]
    _ = ∑ j, (star (Φ j) * Φ j) * (q : ℂ) := by
      simp [mul_ite]
    _ = ∑ j, (q : ℂ) * (star (Φ j) * Φ j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      ring

/-- Exact first-frequency mean square for complete Kloosterman sums.  It
realizes the average square-root cancellation supplied by finite Fourier
orthogonality:

`sum_m |S(m,n;q)|² = q * φ(q)`.

The DFI theorem needs a pointwise estimate at each specified frequency, so
this identity is a genuine but insufficient substitute for Weil's bound. -/
theorem kloostermanSumZMod_mean_square (q : ℕ) [NeZero q] (n : ZMod q) :
    (∑ m : ZMod q,
      star (kloostermanSumZMod q m n) * kloostermanSumZMod q m n) =
      (q : ℂ) * (Nat.totient q : ℂ) := by
  unfold kloostermanSumZMod
  simp_rw [star_sum, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ m : ZMod q, ∑ d : (ZMod q)ˣ, ∑ e : (ZMod q)ˣ,
        star (ZMod.stdAddChar
          (m * (d : ZMod q) + n * (↑(d⁻¹) : ZMod q)) : ℂ) *
          ZMod.stdAddChar
            (m * (e : ZMod q) + n * (↑(e⁻¹) : ZMod q))) =
        ∑ d : (ZMod q)ˣ, ∑ e : (ZMod q)ˣ, ∑ m : ZMod q,
          star (ZMod.stdAddChar
            (m * (d : ZMod q) + n * (↑(d⁻¹) : ZMod q)) : ℂ) *
            ZMod.stdAddChar
              (m * (e : ZMod q) + n * (↑(e⁻¹) : ZMod q)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_comm]
    _ = ∑ d : (ZMod q)ˣ, ∑ e : (ZMod q)ˣ,
          (star (ZMod.stdAddChar
              (n * (↑(d⁻¹) : ZMod q)) : ℂ) *
            ZMod.stdAddChar (n * (↑(e⁻¹) : ZMod q))) *
          ∑ m : ZMod q,
            star (ZMod.stdAddChar (m * (d : ZMod q)) : ℂ) *
              ZMod.stdAddChar (m * (e : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [ZMod.stdAddChar.map_add_eq_mul, ZMod.stdAddChar.map_add_eq_mul,
        star_mul]
      ring

    _ = ∑ d : (ZMod q)ˣ, ∑ e : (ZMod q)ˣ,
          (star (ZMod.stdAddChar
              (n * (↑(d⁻¹) : ZMod q)) : ℂ) *
            ZMod.stdAddChar (n * (↑(e⁻¹) : ZMod q))) *
          (if (d : ZMod q) = (e : ZMod q) then (q : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      rw [zmod_stdAddChar_mul_orthogonality_right]
    _ = ∑ d : (ZMod q)ˣ, (q : ℂ) := by
      apply Finset.sum_congr rfl
      intro d _hd
      calc
        (∑ e : (ZMod q)ˣ,
            (star (ZMod.stdAddChar
                (n * (↑(d⁻¹) : ZMod q)) : ℂ) *
              ZMod.stdAddChar (n * (↑(e⁻¹) : ZMod q))) *
            (if (d : ZMod q) = (e : ZMod q) then (q : ℂ) else 0)) =
            (star (ZMod.stdAddChar
                (n * (↑(d⁻¹) : ZMod q)) : ℂ) *
              ZMod.stdAddChar (n * (↑(d⁻¹) : ZMod q))) * (q : ℂ) := by
          simp [Units.val_inj]
        _ = (q : ℂ) := by
          rw [zmod_stdAddChar_star, ← ZMod.stdAddChar.map_add_eq_mul]
          simp
    _ = (q : ℂ) * (Nat.totient q : ℂ) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        ZMod.card_units_eq_totient]
      ring

/-- Exact square-root cancellation on average along an invertible affine
frequency progression.  This is the form of finite Fourier cancellation
needed when the DFI transformed variables are summed before absolute values
are taken: multiplication by a unit and translation merely permute the
frequencies modulo `q`. -/
theorem kloostermanSumZMod_affine_mean_square (q : ℕ) [NeZero q]
    (h : ZMod q) (a : (ZMod q)ˣ) (b : ZMod q) :
    (∑ x : ZMod q,
      star (kloostermanSumZMod q ((a : ZMod q) * x + b) h) *
        kloostermanSumZMod q ((a : ZMod q) * x + b) h) =
      (q : ℂ) * (Nat.totient q : ℂ) := by
  let e : ZMod q ≃ ZMod q := a.mulLeft.trans (Equiv.addRight b)
  calc
    (∑ x : ZMod q,
        star (kloostermanSumZMod q ((a : ZMod q) * x + b) h) *
          kloostermanSumZMod q ((a : ZMod q) * x + b) h) =
        ∑ y : ZMod q,
          star (kloostermanSumZMod q y h) * kloostermanSumZMod q y h := by
      refine Fintype.sum_equiv e _ _ (fun x => ?_)
      rfl
    _ = (q : ℂ) * (Nat.totient q : ℂ) :=
      kloostermanSumZMod_mean_square q h

/-- Real norm-square form of the affine Kloosterman Parseval identity. -/
theorem sum_norm_kloostermanSumZMod_affine_sq (q : ℕ) [NeZero q]
    (h : ZMod q) (a : (ZMod q)ˣ) (b : ZMod q) :
    (∑ x : ZMod q, ‖kloostermanSumZMod q ((a : ZMod q) * x + b) h‖ ^ 2) =
      (q : ℝ) * (Nat.totient q : ℝ) := by
  have hParseval := congrArg Complex.re
    (kloostermanSumZMod_affine_mean_square q h a b)
  simpa [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self] using hParseval

/-- At most `L / q + 1` natural numbers below `L` occupy any prescribed
residue class modulo a nonzero modulus `q`. -/
theorem range_zmod_fiber_card_le (q L : ℕ) [NeZero q] (r : ZMod q) :
    ((Finset.range L).filter (fun n : ℕ => (n : ZMod q) = r)).card ≤ L / q + 1 := by
  let fiber : Finset ℕ :=
    (Finset.range L).filter (fun n : ℕ => (n : ZMod q) = r)
  have hCard : fiber.card ≤ (Finset.range (L / q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun n : ℕ => n / q)
    · intro n hn
      have hnL : n < L := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
      have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      have hdiv : n / q ≤ L / q := Nat.div_le_div_right hnL.le
      have hlt : n / q < L / q + 1 := by omega
      simpa using (Finset.mem_range.mpr hlt)
    · intro m hm n hn hmn
      have hmod : m % q = n % q := by
        rw [← ZMod.natCast_eq_natCast_iff']
        exact (Finset.mem_filter.mp hm).2.trans (Finset.mem_filter.mp hn).2.symm
      change m / q = n / q at hmn
      calc
        m = m % q + q * (m / q) := (Nat.mod_add_div m q).symm
        _ = n % q + q * (n / q) := by rw [hmod, hmn]
        _ = n := Nat.mod_add_div n q
  simpa [fiber] using hCard

/-- A finite interval of an invertible affine progression retains the
square-root average cancellation of a complete Kloosterman family, with only
the unavoidable number of complete residue blocks. -/
theorem sum_range_norm_kloostermanSumZMod_affine_sq_le
    (q L : ℕ) [NeZero q] (h : ZMod q) (a : (ZMod q)ˣ) (b : ZMod q) :
    ∑ n ∈ Finset.range L,
        ‖kloostermanSumZMod q ((a : ZMod q) * (n : ZMod q) + b) h‖ ^ 2 ≤
      ((L / q + 1 : ℕ) : ℝ) * ((q : ℝ) * (Nat.totient q : ℝ)) := by
  let energy : ZMod q → ℝ := fun r =>
    ‖kloostermanSumZMod q ((a : ZMod q) * r + b) h‖ ^ 2
  have hFiber : ∀ r : ZMod q,
      (((Finset.range L).filter (fun n : ℕ => (n : ZMod q) = r)).card : ℝ) ≤
        ((L / q + 1 : ℕ) : ℝ) := by
    intro r
    exact_mod_cast (range_zmod_fiber_card_le q L r)
  change ∑ n ∈ Finset.range L, energy (n : ZMod q) ≤ _
  calc
    ∑ n ∈ Finset.range L, energy (n : ZMod q) =
        ∑ r : ZMod q,
          ∑ n ∈ (Finset.range L).filter (fun n : ℕ => (n : ZMod q) = r),
            energy (n : ZMod q) := by
      exact (Finset.sum_fiberwise_of_maps_to
        (s := Finset.range L) (t := Finset.univ)
        (g := fun n : ℕ => (n : ZMod q)) (by simp)
        (fun n : ℕ => energy (n : ZMod q))).symm
    _ =
        ∑ r : ZMod q,
          (((Finset.range L).filter (fun n : ℕ => (n : ZMod q) = r)).card : ℝ) *
            energy r := by
      apply Finset.sum_congr rfl
      intro r _hr
      calc
        ∑ n ∈ (Finset.range L).filter (fun n : ℕ => (n : ZMod q) = r),
            energy (n : ZMod q) =
            ∑ _n ∈ (Finset.range L).filter (fun n : ℕ => (n : ZMod q) = r),
              energy r := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [(Finset.mem_filter.mp hn).2]
        _ = _ := by simp
    _ ≤ ∑ r : ZMod q, ((L / q + 1 : ℕ) : ℝ) * energy r := by
      apply Finset.sum_le_sum
      intro r _hr
      exact mul_le_mul_of_nonneg_right (hFiber r) (sq_nonneg _)
    _ = ((L / q + 1 : ℕ) : ℝ) * ((q : ℝ) * (Nat.totient q : ℝ)) := by
      rw [← Finset.mul_sum, sum_norm_kloostermanSumZMod_affine_sq]

/-- Cauchy--Schwarz form of the finite transformed-frequency estimate.  It
retains the exact `ℓ2` norm of the Voronoi/Bessel weights and pays only the
complete-block Kloosterman energy. -/
theorem norm_sum_range_mul_kloostermanSumZMod_affine_le
    (q L : ℕ) [NeZero q] (h : ZMod q) (a : (ZMod q)ˣ) (b : ZMod q)
    (w : ℕ → ℂ) :
    ‖∑ n ∈ Finset.range L,
        w n * kloostermanSumZMod q ((a : ZMod q) * (n : ZMod q) + b) h‖ ≤
      Real.sqrt (∑ n ∈ Finset.range L, ‖w n‖ ^ 2) *
        Real.sqrt (((L / q + 1 : ℕ) : ℝ) *
          ((q : ℝ) * (Nat.totient q : ℝ))) := by
  calc
    ‖∑ n ∈ Finset.range L,
        w n * kloostermanSumZMod q ((a : ZMod q) * (n : ZMod q) + b) h‖ ≤
        ∑ n ∈ Finset.range L,
          ‖w n‖ * ‖kloostermanSumZMod q
            ((a : ZMod q) * (n : ZMod q) + b) h‖ := by
      calc
        ‖∑ n ∈ Finset.range L,
            w n * kloostermanSumZMod q ((a : ZMod q) * (n : ZMod q) + b) h‖ ≤
            ∑ n ∈ Finset.range L,
              ‖w n * kloostermanSumZMod q
                ((a : ZMod q) * (n : ZMod q) + b) h‖ := norm_sum_le _ _
        _ = _ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ n ∈ Finset.range L, ‖w n‖ ^ 2) *
        Real.sqrt (∑ n ∈ Finset.range L,
          ‖kloostermanSumZMod q
            ((a : ZMod q) * (n : ZMod q) + b) h‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt (Finset.range L) (‖w ·‖)
        (fun n => ‖kloostermanSumZMod q
          ((a : ZMod q) * (n : ZMod q) + b) h‖)
    _ ≤ Real.sqrt (∑ n ∈ Finset.range L, ‖w n‖ ^ 2) *
        Real.sqrt (((L / q + 1 : ℕ) : ℝ) *
          ((q : ℝ) * (Nat.totient q : ℝ))) := by
      gcongr
      exact sum_range_norm_kloostermanSumZMod_affine_sq_le q L h a b

/-- Two-frequency version of the complete-block Kloosterman energy bound.
For each second frequency, an invertible first coefficient makes the first
frequency run through complete residue blocks.  This is the exact geometry
of the `S(h, ām-b̄n;q)` term in DFI equation (24). -/
theorem sum_range_range_norm_kloostermanSumZMod_affine_sq_le
    (q L₁ L₂ : ℕ) [NeZero q] (h : ZMod q) (a : (ZMod q)ˣ)
    (b c : ZMod q) :
    ∑ m ∈ Finset.range L₁, ∑ n ∈ Finset.range L₂,
        ‖kloostermanSumZMod q
          ((a : ZMod q) * (m : ZMod q) + b * (n : ZMod q) + c) h‖ ^ 2 ≤
      (L₂ : ℝ) * (((L₁ / q + 1 : ℕ) : ℝ) *
        ((q : ℝ) * (Nat.totient q : ℝ))) := by
  calc
    ∑ m ∈ Finset.range L₁, ∑ n ∈ Finset.range L₂,
        ‖kloostermanSumZMod q
          ((a : ZMod q) * (m : ZMod q) + b * (n : ZMod q) + c) h‖ ^ 2 =
        ∑ n ∈ Finset.range L₂, ∑ m ∈ Finset.range L₁,
          ‖kloostermanSumZMod q
            ((a : ZMod q) * (m : ZMod q) +
              (b * (n : ZMod q) + c)) h‖ ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro m _hm
      congr 3
      ring
    _ ≤ ∑ _n ∈ Finset.range L₂,
        (((L₁ / q + 1 : ℕ) : ℝ) *
          ((q : ℝ) * (Nat.totient q : ℝ))) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact sum_range_norm_kloostermanSumZMod_affine_sq_le
        q L₁ h a (b * (n : ZMod q) + c)
    _ = (L₂ : ℝ) * (((L₁ / q + 1 : ℕ) : ℝ) *
        ((q : ℝ) * (Nat.totient q : ℝ))) := by simp

/-- Weighted two-frequency Cauchy--Schwarz estimate for the double-dual
Voronoi term.  Unlike a pointwise triangle bound, this retains the exact
`ℓ2` norm of the Bessel/Mellin transform weights and obtains square-root
cancellation from finite Fourier orthogonality. -/
theorem norm_sum_range_range_mul_kloostermanSumZMod_affine_le
    (q L₁ L₂ : ℕ) [NeZero q] (h : ZMod q) (a : (ZMod q)ˣ)
    (b c : ZMod q) (w : ℕ → ℕ → ℂ) :
    ‖∑ m ∈ Finset.range L₁, ∑ n ∈ Finset.range L₂,
        w m n * kloostermanSumZMod q
          ((a : ZMod q) * (m : ZMod q) + b * (n : ZMod q) + c) h‖ ≤
      Real.sqrt
          (∑ m ∈ Finset.range L₁, ∑ n ∈ Finset.range L₂,
            ‖w m n‖ ^ 2) *
        Real.sqrt ((L₂ : ℝ) * (((L₁ / q + 1 : ℕ) : ℝ) *
          ((q : ℝ) * (Nat.totient q : ℝ)))) := by
  let P := Finset.range L₁ ×ˢ Finset.range L₂
  let K : ℕ × ℕ → ℂ := fun p =>
    kloostermanSumZMod q
      ((a : ZMod q) * (p.1 : ZMod q) + b * (p.2 : ZMod q) + c) h
  calc
    ‖∑ m ∈ Finset.range L₁, ∑ n ∈ Finset.range L₂,
        w m n * kloostermanSumZMod q
          ((a : ZMod q) * (m : ZMod q) + b * (n : ZMod q) + c) h‖ =
        ‖∑ p ∈ P, w p.1 p.2 * K p‖ := by
      simp [P, K, Finset.sum_product]
    _ ≤ ∑ p ∈ P, ‖w p.1 p.2‖ * ‖K p‖ := by
      calc
        ‖∑ p ∈ P, w p.1 p.2 * K p‖ ≤
            ∑ p ∈ P, ‖w p.1 p.2 * K p‖ := norm_sum_le _ _
        _ = _ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ p ∈ P, ‖w p.1 p.2‖ ^ 2) *
        Real.sqrt (∑ p ∈ P, ‖K p‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt P (fun p => ‖w p.1 p.2‖) (‖K ·‖)
    _ ≤ Real.sqrt
          (∑ m ∈ Finset.range L₁, ∑ n ∈ Finset.range L₂,
            ‖w m n‖ ^ 2) *
        Real.sqrt ((L₂ : ℝ) * (((L₁ / q + 1 : ℕ) : ℝ) *
          ((q : ℝ) * (Nat.totient q : ℝ)))) := by
      simp only [P, K, Finset.sum_product]
      gcongr
      exact sum_range_range_norm_kloostermanSumZMod_affine_sq_le
        q L₁ L₂ h a b c

/-- The elementary cardinality bound for a complete Kloosterman sum.  This is
not the Weil bound: it saves no square root and therefore does not close the
DFI error term. -/
theorem norm_kloostermanSum_le_totient (q m n : ℕ) [NeZero q] :
    ‖kloostermanSum q m n‖ ≤ (Nat.totient q : ℝ) := by
  unfold kloostermanSum
  calc
    ‖∑ d : (ZMod q)ˣ,
        ZMod.stdAddChar
          ((m : ZMod q) * (d : ZMod q) +
            (n : ZMod q) * (↑(d⁻¹) : ZMod q))‖
        ≤ ∑ _d : (ZMod q)ˣ, (1 : ℝ) := by
          apply norm_sum_le_of_le
          intro d hd
          simp
    _ = (Fintype.card (ZMod q)ˣ : ℝ) := by simp
    _ = (Nat.totient q : ℝ) := by
      rw [ZMod.card_units_eq_totient]

/-- The corresponding elementary Ramanujan-sum bound. -/
theorem norm_ramanujanSum_le_totient (q h : ℕ) [NeZero q] :
    ‖ramanujanSum q h‖ ≤ (Nat.totient q : ℝ) := by
  exact norm_kloostermanSum_le_totient q h 0

/-- The square-root Kloosterman estimate used in DFI, recorded as an explicit
unproved source proposition.  A theorem of this type must be derived before
the DFI node can be complete; `norm_kloostermanSum_le_totient` is strictly
weaker. -/
def KloostermanWeilBoundProp : Prop :=
  ∀ (q : ℕ) [NeZero q] (m n : ℕ),
    ‖kloostermanSum q m n‖ ≤
      Real.sqrt (Nat.gcd (Nat.gcd m n) q) * Real.sqrt q * (q.divisors.card : ℝ)

/-- A coefficientwise norm bound for one finite shifted divisor sum.  It is a
faithful triangle-inequality baseline, not the DFI power-saving estimate. -/
theorem norm_finiteQuadraticDivisorSum_le
    (a b M N : ℕ) (r : ℤ) (f : ℕ → ℕ → ℂ) :
    ‖finiteQuadraticDivisorSum a b M N r f‖ ≤
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        if quadraticDivisorShift a b m n = r then
          (m.divisors.card : ℝ) * (n.divisors.card : ℝ) * ‖f (a * m) (b * n)‖
        else 0 := by
  unfold finiteQuadraticDivisorSum divisorWeight
  calc
    ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        if quadraticDivisorShift a b m n = r then
          (m.divisors.card : ℂ) * (n.divisors.card : ℂ) * f (a * m) (b * n)
        else 0‖
        ≤ ∑ m ∈ Finset.Icc 1 M,
            ‖∑ n ∈ Finset.Icc 1 N,
              if quadraticDivisorShift a b m n = r then
                (m.divisors.card : ℂ) * (n.divisors.card : ℂ) *
                  f (a * m) (b * n)
              else 0‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          if quadraticDivisorShift a b m n = r then
            (m.divisors.card : ℝ) * (n.divisors.card : ℝ) * ‖f (a * m) (b * n)‖
          else 0 := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        ‖∑ n ∈ Finset.Icc 1 N,
            if quadraticDivisorShift a b m n = r then
              (m.divisors.card : ℂ) * (n.divisors.card : ℂ) *
                f (a * m) (b * n)
            else 0‖
            ≤ ∑ n ∈ Finset.Icc 1 N,
                ‖if quadraticDivisorShift a b m n = r then
                  (m.divisors.card : ℂ) * (n.divisors.card : ℂ) *
                    f (a * m) (b * n)
                else 0‖ := norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hShift : quadraticDivisorShift a b m n = r
          · simp [hShift]
          · simp [hShift]

end RiemannZeta.GuthMaynard
