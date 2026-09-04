import GafniTao.WooleySection7Translated

/-!
# The integral Section 7 change of equations

This file constructs the polynomial quotients that occur before the matrix
change in Wooley's passage from (7.10) to (7.11).  The power of the source
prime is divided out by an exact polynomial identity; the coprime part of the
translation parameter is left visible for the later modular matrix inverse.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- After writing `h = omega*p^gamma`, the translated variable
`p^a X+h` is `p^gamma` times this integral affine polynomial. -/
def wooleySection7AffineCore
    (p a gamma : ℕ) (omega : ℤ) : Polynomial ℤ :=
  C ((p : ℤ) ^ (a - gamma)) * X + C omega

theorem wooleySection7_primePower_mul_affineCore
    {p a gamma : ℕ} (hgamma : gamma ≤ a) (omega h : ℤ)
    (hsep : h = omega * (p : ℤ) ^ gamma) :
    C ((p : ℤ) ^ gamma) * wooleySection7AffineCore p a gamma omega =
      C ((p : ℤ) ^ a) * X + C h := by
  subst h
  unfold wooleySection7AffineCore
  rw [mul_add, ← mul_assoc, ← C_mul, ← C_mul]
  rw [← pow_add, Nat.add_sub_of_le hgamma]
  ring_nf

/-- The exact quotient after removing the column factor
`p^(gamma*(k-r+l))` from the translated top equation. -/
def wooleySection7ColumnNormalizedPolynomial
    (k r p c a gamma : ℕ) (omega h : ℤ)
    (psi : Fin r → Polynomial ℤ) (l : Fin r) : Polynomial ℤ :=
  let j := wooleySection7Node k r l + 1
  let g := wooleySection7AffineCore p a gamma omega
  (g ^ j - C (omega ^ j)) +
    C ((p : ℤ) ^ (c + gamma * (k + 1) - gamma * j)) *
      (g ^ (k + 1) * (psi l).comp (C ((p : ℤ) ^ gamma) * g) -
        C (omega ^ (k + 1) * (psi l).eval h))

theorem wooleySection7_column_exponent_add
    {k r c gamma : ℕ} (hrk : r ≤ k) (l : Fin r) :
    gamma * (wooleySection7Node k r l + 1) +
        (c + gamma * (k + 1) -
          gamma * (wooleySection7Node k r l + 1)) =
      c + gamma * (k + 1) := by
  have hj : wooleySection7Node k r l + 1 ≤ k + 1 := by
    exact (wooleySection7Node_succ_le hrk l).trans (Nat.le_succ k)
  have hmul :
      gamma * (wooleySection7Node k r l + 1) ≤
        c + gamma * (k + 1) :=
    (Nat.mul_le_mul_left gamma hj).trans (Nat.le_add_left _ _)
  exact Nat.add_sub_of_le hmul

/-- Exact column divisibility in (7.10).  This is an equality of integral
polynomials, so no division by a zero divisor is hidden in the notation. -/
theorem wooleySection7TranslatedTop_eq_columnFactor_mul
    {k r p c a gamma : ℕ} (hrk : r ≤ k) (hgamma : gamma ≤ a)
    (omega h : ℤ) (hsep : h = omega * (p : ℤ) ^ gamma)
    (psi : Fin r → Polynomial ℤ) (l : Fin r) :
    wooleySection7TranslatedDilatedPolynomial p a h
        (wooleySection7TopSystem k r p c psi l) =
      C ((p : ℤ) ^ (gamma * (wooleySection7Node k r l + 1))) *
        wooleySection7ColumnNormalizedPolynomial
          k r p c a gamma omega h psi l := by
  let j := wooleySection7Node k r l + 1
  let g := wooleySection7AffineCore p a gamma omega
  have hjk : j ≤ k := wooleySection7Node_succ_le hrk l
  have haffine :
      C ((p : ℤ) ^ gamma) * g = C ((p : ℤ) ^ a) * X + C h := by
    exact wooleySection7_primePower_mul_affineCore hgamma omega h hsep
  have hhpow : h = (p : ℤ) ^ gamma * omega := by
    rw [hsep, mul_comm]
  have hexp :
      gamma * j + (c + gamma * (k + 1) - gamma * j) =
        c + gamma * (k + 1) := by
    exact wooleySection7_column_exponent_add (c := c) hrk l
  have hpower :
      (p : ℤ) ^ c * (p : ℤ) ^ (gamma * (k + 1)) =
        (p : ℤ) ^ (gamma * j) *
          (p : ℤ) ^ (c + gamma * (k + 1) - gamma * j) := by
    rw [← pow_add, ← pow_add, hexp]
  have hpolyterm :
      C ((p : ℤ) ^ c) *
            (C ((p : ℤ) ^ (gamma * (k + 1))) * g ^ (k + 1)) *
          (psi l).comp (C ((p : ℤ) ^ gamma) * g) =
        C ((p : ℤ) ^ (gamma * j)) *
            (C ((p : ℤ) ^ (c + gamma * (k + 1) - gamma * j)) *
              g ^ (k + 1)) *
          (psi l).comp (C ((p : ℤ) ^ gamma) * g) := by
    rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, hpower]
  have hintterm :
      (p : ℤ) ^ c *
            ((p : ℤ) ^ (gamma * (k + 1)) * omega ^ (k + 1)) *
          (psi l).eval ((p : ℤ) ^ gamma * omega) =
        (p : ℤ) ^ (gamma * j) *
            ((p : ℤ) ^ (c + gamma * (k + 1) - gamma * j) *
              omega ^ (k + 1)) *
          (psi l).eval ((p : ℤ) ^ gamma * omega) := by
    rw [← mul_assoc, ← mul_assoc, hpower]
  rw [wooleySection7TranslatedDilatedPolynomial_eq_comp]
  unfold wooleyTaylorDifference wooleySection7TopSystem
  rw [taylor_apply, sub_comp, comp_assoc]
  simp only [add_comp, X_comp, C_comp, mul_comp, pow_comp, eval_add,
    eval_mul, eval_pow, eval_X]
  rw [← haffine]
  simp only [mul_pow, ← C_pow]
  rw [hhpow]
  simp only [mul_pow]
  unfold wooleySection7ColumnNormalizedPolynomial
  dsimp only [j, g]
  simp only [← pow_mul]
  simp only [eval_C]
  rw [hpolyterm, hintterm]
  dsimp only [j, g]
  simp only [Nat.mul_add, Nat.mul_one]
  simp only [map_add, map_mul]
  ring_nf

/-- Low coefficient of the normalized column, with the coprime powers kept
on the two sides.  This integral identity is the denominator-free form of
the Laurent coefficient display following (7.10). -/
theorem wooleySection7ColumnNormalizedPolynomial_coeff
    {k r p c a gamma : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (omega h : ℤ) (homega : omega ≠ 0)
    (hsep : h = omega * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) (i l : Fin r) :
    omega ^ ((i : ℕ) + 1) *
        (wooleySection7ColumnNormalizedPolynomial
          k r p c a gamma omega h psi l).coeff ((i : ℕ) + 1) =
      omega ^ (wooleySection7Node k r l + 1) *
        wooleySection7OmegaMatrix (p := p) (c := c) hrk h
            hh psi i l *
        (p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1)) := by
  let j := wooleySection7Node k r l + 1
  let d := (i : ℕ) + 1
  have hfactor := congrArg (fun f : Polynomial ℤ => f.coeff d)
    (wooleySection7TranslatedTop_eq_columnFactor_mul
      (p := p) (c := c) (a := a) (gamma := gamma)
      hrk hgamma omega h hsep psi l)
  have hfactor' :
      (p : ℤ) ^ (gamma * j) *
          (wooleySection7ColumnNormalizedPolynomial
            k r p c a gamma omega h psi l).coeff d =
        (wooleySection7TranslatedDilatedPolynomial p a h
          (wooleySection7TopSystem k r p c psi l)).coeff d := by
    simpa only [coeff_C_mul] using hfactor.symm
  have htop := wooleySection7TranslatedTop_coeff_rat
    (p := p) (c := c) (a := a) hrk h hh psi i l
  have hmain :
      ((p : ℚ) ^ (gamma * j)) *
          ((wooleySection7ColumnNormalizedPolynomial
            k r p c a gamma omega h psi l).coeff d : ℚ) =
        (h : ℚ) ^ ((j : ℤ) - (d : ℤ)) *
          (wooleySection7OmegaMatrix (p := p) (c := c)
            hrk h hh psi i l : ℚ) *
          (p : ℚ) ^ (a * d) := by
    rw [← htop]
    exact_mod_cast hfactor'
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have homegaq : (omega : ℚ) ≠ 0 := by exact_mod_cast homega
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  have hhqeq : (h : ℚ) = (omega : ℚ) * (p : ℚ) ^ gamma := by
    exact_mod_cast hsep
  rw [zpow_sub₀ hhq, zpow_natCast, zpow_natCast, hhqeq] at hmain
  simp only [mul_pow] at hmain
  simp only [← pow_mul] at hmain
  have hapow :
      (p : ℚ) ^ (a * d) =
        (p : ℚ) ^ (gamma * d) * (p : ℚ) ^ ((a - gamma) * d) := by
    rw [← pow_add]
    congr 1
    rw [← Nat.add_mul, Nat.add_sub_of_le hgamma]
  rw [hapow] at hmain
  apply Int.cast_injective (α := ℚ)
  push_cast
  field_simp at hmain
  nlinarith

/-- The normalized column has zero constant term. -/
theorem wooleySection7ColumnNormalizedPolynomial_coeff_zero
    {k r p c a gamma : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (omega h : ℤ)
    (hsep : h = omega * (p : ℤ) ^ gamma)
    (psi : Fin r → Polynomial ℤ) (l : Fin r) :
    (wooleySection7ColumnNormalizedPolynomial
      k r p c a gamma omega h psi l).coeff 0 = 0 := by
  have hfactor := congrArg (fun f : Polynomial ℤ => f.coeff 0)
    (wooleySection7TranslatedTop_eq_columnFactor_mul
      (p := p) (c := c) (a := a) (gamma := gamma)
      hrk hgamma omega h hsep psi l)
  change
    (wooleySection7TranslatedDilatedPolynomial p a h
      (wooleySection7TopSystem k r p c psi l)).coeff 0 =
      (C ((p : ℤ) ^ (gamma * (wooleySection7Node k r l + 1))) *
        wooleySection7ColumnNormalizedPolynomial
          k r p c a gamma omega h psi l).coeff 0 at hfactor
  rw [wooleySection7TranslatedDilatedPolynomial_coeff_zero] at hfactor
  simp only [coeff_C_mul] at hfactor
  exact (mul_eq_zero.mp hfactor.symm).resolve_left
    (pow_ne_zero _ (by exact_mod_cast hp))

/-- Every coefficient above the first `r` degrees retains the full tail
valuation after the column factor has been removed. -/
theorem wooleySection7ColumnNormalizedPolynomial_high_coeff_dvd
    {k r p c a gamma : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (hgammaK : gamma * k ≤ a)
    (omega h : ℤ) (hsep : h = omega * (p : ℤ) ^ gamma)
    (psi : Fin r → Polynomial ℤ) (l : Fin r) (n : ℕ)
    (hn : r + 1 ≤ n) :
    (p : ℤ) ^
        (a * (r + 1) - gamma * (wooleySection7Node k r l + 1)) ∣
      (wooleySection7ColumnNormalizedPolynomial
        k r p c a gamma omega h psi l).coeff n := by
  let j := wooleySection7Node k r l + 1
  have hjk : j ≤ k := wooleySection7Node_succ_le hrk l
  have hcol : gamma * j ≤ a * (r + 1) := by
    calc
      gamma * j ≤ gamma * k := Nat.mul_le_mul_left gamma hjk
      _ ≤ a := hgammaK
      _ ≤ a * (r + 1) := by
        exact Nat.le_mul_of_pos_right a (Nat.zero_lt_succ r)
  have hnpos : 0 < n := (Nat.zero_lt_succ r).trans_le hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  have hfactor := congrArg (fun f : Polynomial ℤ => f.coeff (m + 1))
    (wooleySection7TranslatedTop_eq_columnFactor_mul
      (p := p) (c := c) (a := a) (gamma := gamma)
      hrk hgamma omega h hsep psi l)
  have hfactor' :
      (p : ℤ) ^ (gamma * j) *
          (wooleySection7ColumnNormalizedPolynomial
            k r p c a gamma omega h psi l).coeff (m + 1) =
        (wooleySection7TranslatedDilatedPolynomial p a h
          (wooleySection7TopSystem k r p c psi l)).coeff (m + 1) := by
    simpa only [coeff_C_mul] using hfactor.symm
  rw [wooleySection7TranslatedDilatedPolynomial_coeff_succ] at hfactor'
  have hdegree : a * (r + 1) ≤ a * (m + 1) :=
    Nat.mul_le_mul_left a hn
  have htailDiv :
      (p : ℤ) ^ (a * (r + 1)) ∣
        (taylor h (wooleySection7TopSystem k r p c psi l)).coeff (m + 1) *
          (p : ℤ) ^ (a * (m + 1)) := by
    exact dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) hdegree) _
  rw [← hfactor'] at htailDiv
  have hexp :
      gamma * j + (a * (r + 1) - gamma * j) = a * (r + 1) :=
    Nat.add_sub_of_le hcol
  rw [← hexp, pow_add, Int.mul_dvd_mul_iff_left
    (pow_ne_zero _ (by exact_mod_cast hp))] at htailDiv
  exact htailDiv

/-- A polynomial whose constant coefficient vanishes and whose coefficients
above degree `r` share a scalar factor has an exact positive-low-part plus
scalar-tail decomposition. -/
theorem wooleyPolynomial_exists_positiveLow_add_scalarTail
    (r : ℕ) (f : Polynomial ℤ) (z : ℤ)
    (hzero : f.coeff 0 = 0)
    (hhigh : ∀ n, r + 1 ≤ n → z ∣ f.coeff n) :
    ∃ Xi : Polynomial ℤ,
      f = (∑ i : Fin r, C (f.coeff ((i : ℕ) + 1)) *
              X ^ ((i : ℕ) + 1)) + C z * Xi := by
  let low : Polynomial ℤ :=
    ∑ i : Fin r, C (f.coeff ((i : ℕ) + 1)) * X ^ ((i : ℕ) + 1)
  have hlowCoeff (n : ℕ) :
      low.coeff n =
        ∑ i : Fin r,
          (C (f.coeff ((i : ℕ) + 1)) * X ^ ((i : ℕ) + 1)).coeff n := by
    dsimp [low]
    rw [← lcoeff_apply, map_sum]
    simp only [lcoeff_apply]
  have hdiv : C z ∣ f - low := by
    rw [C_dvd_iff_dvd_coeff]
    intro n
    rw [coeff_sub]
    by_cases hn0 : n = 0
    · subst n
      rw [hlowCoeff]
      simp [hzero]
    by_cases hnr : n ≤ r
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      let i : Fin r := ⟨n - 1, by omega⟩
      have hi : (i : ℕ) + 1 = n := by
        dsimp [i]
        omega
      have hsum : low.coeff n = f.coeff n := by
        rw [hlowCoeff]
        simp only [coeff_C_mul, coeff_X_pow]
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro b hb hbi
          have hne : (b : ℕ) + 1 ≠ n := by
            intro heq
            apply hbi
            apply Fin.ext
            omega
          simp [Ne.symm hne]
        · simp
      rw [hsum, sub_self]
      exact dvd_zero z
    · have hlt : r < n := Nat.lt_of_not_ge hnr
      have hsum : low.coeff n = 0 := by
        rw [hlowCoeff]
        simp only [coeff_C_mul, coeff_X_pow]
        apply Finset.sum_eq_zero
        intro i hi
        have hne : (i : ℕ) + 1 ≠ n := by
          omega
        simp [Ne.symm hne]
      rw [hsum, sub_zero]
      exact hhigh n (by omega)
  obtain ⟨Xi, hXi⟩ := hdiv
  refine ⟨Xi, ?_⟩
  dsimp [low] at hXi ⊢
  rw [← hXi]
  ring

/-- All normalized columns may use the weakest, common high-degree
valuation `a(r+1)-gamma*k`. -/
theorem wooleySection7ColumnNormalizedPolynomial_exists_commonTail
    {k r p c a gamma : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (hgammaK : gamma * k ≤ a)
    (omega h : ℤ) (hsep : h = omega * (p : ℤ) ^ gamma)
    (psi : Fin r → Polynomial ℤ) (l : Fin r) :
    ∃ Theta : Polynomial ℤ,
      wooleySection7ColumnNormalizedPolynomial
          k r p c a gamma omega h psi l =
        (∑ i : Fin r,
          C ((wooleySection7ColumnNormalizedPolynomial
            k r p c a gamma omega h psi l).coeff ((i : ℕ) + 1)) *
              X ^ ((i : ℕ) + 1)) +
          C ((p : ℤ) ^ (a * (r + 1) - gamma * k)) * Theta := by
  apply wooleyPolynomial_exists_positiveLow_add_scalarTail
  · exact wooleySection7ColumnNormalizedPolynomial_coeff_zero
      hp hrk hgamma omega h hsep psi l
  · intro n hn
    have hjk : wooleySection7Node k r l + 1 ≤ k :=
      wooleySection7Node_succ_le hrk l
    have hle :
        a * (r + 1) - gamma * k ≤
          a * (r + 1) -
            gamma * (wooleySection7Node k r l + 1) :=
      Nat.sub_le_sub_left (Nat.mul_le_mul_left gamma hjk) _
    exact dvd_trans (pow_dvd_pow (p : ℤ) hle)
      (wooleySection7ColumnNormalizedPolynomial_high_coeff_dvd
        hp hrk hgamma hgammaK omega h hsep psi l n hn)

/-- Integral representative of a matrix over a residue ring. -/
def wooleyZModMatrixIntLift {r q : ℕ}
    (G : Matrix (Fin r) (Fin r) (ZMod q)) : Matrix (Fin r) (Fin r) ℤ :=
  fun i j => Classical.choose (ZMod.intCast_surjective (G i j))

theorem wooleyZModMatrixIntLift_cast {r q : ℕ}
    (G : Matrix (Fin r) (Fin r) (ZMod q)) (i j : Fin r) :
    (wooleyZModMatrixIntLift G i j : ZMod q) = G i j :=
  Classical.choose_spec (ZMod.intCast_surjective (G i j))

/-- A source unit has an integral inverse representative modulo every prime
power. -/
theorem wooleySection7_exists_int_unit_inverse
    {p L : ℕ} {omega : ℤ} (hcop : Nat.Coprime p omega.natAbs) :
    ∃ omegaInv : ℤ,
      (omegaInv : ZMod (p ^ L)) * (omega : ZMod (p ^ L)) = 1 := by
  have hunit : IsUnit (omega : ZMod (p ^ L)) :=
    wooleySection7_unit_isUnit_primePower hcop
  obtain ⟨u, hu⟩ := hunit
  obtain ⟨omegaInv, hInv⟩ :=
    ZMod.intCast_surjective (↑u⁻¹ : ZMod (p ^ L))
  refine ⟨omegaInv, ?_⟩
  rw [hInv, ← hu]
  exact Units.inv_mul u

/-- Moving unequal powers of a unit across an equality. -/
theorem wooley_unit_power_transport
    {R : Type*} [CommRing R] (u v x y : R) (d j : ℕ)
    (huv : v * u = 1) (hxy : u ^ d * x = u ^ j * y) :
    v ^ j * x = v ^ d * y := by
  have hpow (n : ℕ) : v ^ n * u ^ n = 1 := by
    rw [← mul_pow, huv, one_pow]
  calc
    v ^ j * x = (v ^ d * u ^ d) * (v ^ j * x) := by
      rw [hpow]
      ring
    _ = v ^ d * v ^ j * (u ^ d * x) := by ring
    _ = v ^ d * v ^ j * (u ^ j * y) := by rw [hxy]
    _ = v ^ d * ((v ^ j * u ^ j) * y) := by ring
    _ = v ^ d * y := by rw [hpow]; ring

/-- The inverse Omega matrix and the inverse unit turn the first `r`
coefficients into the diagonal row factors `p^((a-gamma)i)`. -/
theorem wooleySection7_inverse_combination_low_coefficient
    {k r p c a gamma L : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (omega h omegaInv : ℤ)
    (homega : omega ≠ 0) (hsep : h = omega * (p : ℤ) ^ gamma)
    (hh : h ≠ 0) (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L)))
    (hG : G * Matrix.transpose
        (wooleyIntMatrixMod
          (wooleySection7OmegaMatrix (p := p) (c := c)
            hrk h hh psi) (p ^ L)) = 1)
    (hInv : (omegaInv : ZMod (p ^ L)) *
      (omega : ZMod (p ^ L)) = 1)
    (i d : Fin r) :
    (omega : ZMod (p ^ L)) ^ ((i : ℕ) + 1) *
        (∑ l : Fin r,
          (wooleyZModMatrixIntLift G i l : ZMod (p ^ L)) *
            (omegaInv : ZMod (p ^ L)) ^
              (wooleySection7Node k r l + 1) *
            ((wooleySection7ColumnNormalizedPolynomial
              k r p c a gamma omega h psi l).coeff ((d : ℕ) + 1) :
                ZMod (p ^ L))) =
      if i = d then
        (p : ZMod (p ^ L)) ^ ((a - gamma) * ((d : ℕ) + 1))
      else 0 := by
  let Omega := wooleySection7OmegaMatrix (p := p) (c := c)
    hrk h hh psi
  have hentry := congrArg
    (fun M : Matrix (Fin r) (Fin r) (ZMod (p ^ L)) => M i d) hG
  have hmatrix :
      (∑ l : Fin r, G i l * (Omega d l : ZMod (p ^ L))) =
        if i = d then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply,
      wooleyIntMatrixMod, Matrix.one_apply] using hentry
  have hterm (l : Fin r) :
      (omegaInv : ZMod (p ^ L)) ^
            (wooleySection7Node k r l + 1) *
          ((wooleySection7ColumnNormalizedPolynomial
            k r p c a gamma omega h psi l).coeff ((d : ℕ) + 1) :
              ZMod (p ^ L)) =
        (omegaInv : ZMod (p ^ L)) ^ ((d : ℕ) + 1) *
          (Omega d l : ZMod (p ^ L)) *
          (p : ZMod (p ^ L)) ^ ((a - gamma) * ((d : ℕ) + 1)) := by
    have hcoeffInt := wooleySection7ColumnNormalizedPolynomial_coeff
      (c := c) hp hrk hgamma omega h homega hsep hh psi d l
    have hcoeffMod := congrArg
      (fun z : ℤ => (z : ZMod (p ^ L))) hcoeffInt
    have ht := wooley_unit_power_transport
      (u := (omega : ZMod (p ^ L)))
      (v := (omegaInv : ZMod (p ^ L)))
      (x := ((wooleySection7ColumnNormalizedPolynomial
        k r p c a gamma omega h psi l).coeff ((d : ℕ) + 1) :
          ZMod (p ^ L)))
      (y := (Omega d l : ZMod (p ^ L)) *
        (p : ZMod (p ^ L)) ^ ((a - gamma) * ((d : ℕ) + 1)))
      (d := (d : ℕ) + 1)
      (j := wooleySection7Node k r l + 1)
      hInv (by
        dsimp only [Omega]
        simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
          mul_assoc] using hcoeffMod)
    simpa only [mul_assoc] using ht
  simp_rw [wooleyZModMatrixIntLift_cast (G := G)]
  simp_rw [mul_assoc]
  simp_rw [hterm]
  rw [show
    (∑ l : Fin r,
      G i l * ((omegaInv : ZMod (p ^ L)) ^ ((d : ℕ) + 1) *
        (Omega d l : ZMod (p ^ L)) *
        (p : ZMod (p ^ L)) ^ ((a - gamma) * ((d : ℕ) + 1)))) =
      (omegaInv : ZMod (p ^ L)) ^ ((d : ℕ) + 1) *
        (∑ l : Fin r, G i l * (Omega d l : ZMod (p ^ L))) *
        (p : ZMod (p ^ L)) ^ ((a - gamma) * ((d : ℕ) + 1)) by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      ring]
  rw [hmatrix]
  by_cases hid : i = d
  · subst d
    have hunitPow :
      (omega : ZMod (p ^ L)) ^ ((i : ℕ) + 1) *
          (omegaInv : ZMod (p ^ L)) ^ ((i : ℕ) + 1) = 1 := by
      rw [← mul_pow, mul_comm, hInv, one_pow]
    simp only [ite_true]
    calc
      (omega : ZMod (p ^ L)) ^ ((i : ℕ) + 1) *
            (((omegaInv : ZMod (p ^ L)) ^ ((i : ℕ) + 1) * 1) *
              (p : ZMod (p ^ L)) ^ ((a - gamma) * ((i : ℕ) + 1))) =
          ((omega : ZMod (p ^ L)) ^ ((i : ℕ) + 1) *
            (omegaInv : ZMod (p ^ L)) ^ ((i : ℕ) + 1)) *
              (p : ZMod (p ^ L)) ^ ((a - gamma) * ((i : ℕ) + 1)) := by
            ring
      _ = (p : ZMod (p ^ L)) ^ ((a - gamma) * ((i : ℕ) + 1)) := by
        rw [hunitPow, one_mul]
  · simp [hid]

/-- The integral polynomial obtained by applying the inverse Omega row and
the inverse powers of the unit part of the residue separation.  Its first
`r` coefficients are diagonal modulo the working prime power. -/
def wooleySection7TransformedPolynomial
    (k r p c a gamma L : ℕ) (omega h omegaInv : ℤ)
    (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L)))
    (i : Fin r) : Polynomial ℤ :=
  C (omega ^ ((i : ℕ) + 1)) *
    ∑ l : Fin r,
      C (wooleyZModMatrixIntLift G i l *
        omegaInv ^ (wooleySection7Node k r l + 1)) *
        wooleySection7ColumnNormalizedPolynomial
          k r p c a gamma omega h psi l

theorem wooleySection7TransformedPolynomial_coeff_low
    {k r p c a gamma L : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (omega h omegaInv : ℤ)
    (homega : omega ≠ 0) (hsep : h = omega * (p : ℤ) ^ gamma)
    (hh : h ≠ 0) (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L)))
    (hG : G * Matrix.transpose
        (wooleyIntMatrixMod
          (wooleySection7OmegaMatrix (p := p) (c := c)
            hrk h hh psi) (p ^ L)) = 1)
    (hInv : (omegaInv : ZMod (p ^ L)) *
      (omega : ZMod (p ^ L)) = 1)
    (i d : Fin r) :
    ((wooleySection7TransformedPolynomial
        k r p c a gamma L omega h omegaInv psi G i).coeff
          ((d : ℕ) + 1) : ZMod (p ^ L)) =
      if i = d then
        (p : ZMod (p ^ L)) ^ ((a - gamma) * ((d : ℕ) + 1))
      else 0 := by
  unfold wooleySection7TransformedPolynomial
  rw [coeff_C_mul]
  rw [← lcoeff_apply, map_sum]
  simp only [lcoeff_apply]
  simp only [coeff_C_mul, Int.cast_mul, Int.cast_pow]
  push_cast
  exact wooleySection7_inverse_combination_low_coefficient
    hp hrk hgamma omega h omegaInv homega hsep hh psi G hG hInv i d

theorem wooleySection7TransformedPolynomial_coeff_zero
    {k r p c a gamma L : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (omega h omegaInv : ℤ)
    (hsep : h = omega * (p : ℤ) ^ gamma)
    (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L))) (i : Fin r) :
    (wooleySection7TransformedPolynomial
      k r p c a gamma L omega h omegaInv psi G i).coeff 0 = 0 := by
  unfold wooleySection7TransformedPolynomial
  rw [coeff_C_mul]
  apply mul_eq_zero_of_right
  rw [← lcoeff_apply, map_sum]
  simp only [lcoeff_apply]
  apply Finset.sum_eq_zero
  intro l hl
  simp only [coeff_C_mul]
  simp [wooleySection7ColumnNormalizedPolynomial_coeff_zero
    hp hrk hgamma omega h hsep psi l]

theorem wooleySection7TransformedPolynomial_high_coeff_dvd
    {k r p c a gamma L : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (hgammaK : gamma * k ≤ a)
    (omega h omegaInv : ℤ) (hsep : h = omega * (p : ℤ) ^ gamma)
    (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L))) (i : Fin r)
    (n : ℕ) (hn : r + 1 ≤ n) :
    (p : ℤ) ^ (a * (r + 1) - gamma * k) ∣
      (wooleySection7TransformedPolynomial
        k r p c a gamma L omega h omegaInv psi G i).coeff n := by
  unfold wooleySection7TransformedPolynomial
  rw [coeff_C_mul]
  apply dvd_mul_of_dvd_right
  rw [← lcoeff_apply, map_sum]
  simp only [lcoeff_apply]
  apply dvd_sum
  intro l hl
  simp only [coeff_C_mul]
  have hjk : wooleySection7Node k r l + 1 ≤ k :=
    wooleySection7Node_succ_le hrk l
  have hle :
      a * (r + 1) - gamma * k ≤
        a * (r + 1) - gamma * (wooleySection7Node k r l + 1) :=
    Nat.sub_le_sub_left (Nat.mul_le_mul_left gamma hjk) _
  have hdiv := wooleySection7ColumnNormalizedPolynomial_high_coeff_dvd
    (c := c) hp hrk hgamma hgammaK omega h hsep psi l n hn
  exact dvd_mul_of_dvd_right
    (dvd_trans (pow_dvd_pow (p : ℤ) hle) hdiv) _

theorem wooleySection7TransformedPolynomial_exists_commonTail
    {k r p c a gamma L : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (hgammaK : gamma * k ≤ a)
    (omega h omegaInv : ℤ) (hsep : h = omega * (p : ℤ) ^ gamma)
    (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L))) (i : Fin r) :
    ∃ Theta : Polynomial ℤ,
      wooleySection7TransformedPolynomial
          k r p c a gamma L omega h omegaInv psi G i =
        (∑ d : Fin r,
          C ((wooleySection7TransformedPolynomial
            k r p c a gamma L omega h omegaInv psi G i).coeff
              ((d : ℕ) + 1)) * X ^ ((d : ℕ) + 1)) +
          C ((p : ℤ) ^ (a * (r + 1) - gamma * k)) * Theta := by
  apply wooleyPolynomial_exists_positiveLow_add_scalarTail
  · exact wooleySection7TransformedPolynomial_coeff_zero
      hp hrk hgamma omega h omegaInv hsep psi G i
  · exact wooleySection7TransformedPolynomial_high_coeff_dvd
      hp hrk hgamma hgammaK omega h omegaInv hsep psi G i

/-- The positive-degree truncation used to separate the modular inverse
errors from the genuinely high-degree tail. -/
def wooleySection7TransformedLow
    (k r p c a gamma L : ℕ) (omega h omegaInv : ℤ)
    (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L)))
    (i : Fin r) : Polynomial ℤ :=
  ∑ d : Fin r,
    C ((wooleySection7TransformedPolynomial
      k r p c a gamma L omega h omegaInv psi G i).coeff
        ((d : ℕ) + 1)) * X ^ ((d : ℕ) + 1)

/-- Modulo the working prime power the low part is exactly one monomial.
This is the polynomial form of the inverse-matrix coefficient calculation. -/
theorem wooleySection7TransformedLow_map_eq_monomial
    {k r p c a gamma L : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (omega h omegaInv : ℤ)
    (homega : omega ≠ 0) (hsep : h = omega * (p : ℤ) ^ gamma)
    (hh : h ≠ 0) (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L)))
    (hG : G * Matrix.transpose
        (wooleyIntMatrixMod
          (wooleySection7OmegaMatrix (p := p) (c := c)
            hrk h hh psi) (p ^ L)) = 1)
    (hInv : (omegaInv : ZMod (p ^ L)) *
      (omega : ZMod (p ^ L)) = 1)
    (i : Fin r) :
    Polynomial.map (Int.castRingHom (ZMod (p ^ L)))
        (wooleySection7TransformedLow
          k r p c a gamma L omega h omegaInv psi G i) =
      C ((p : ZMod (p ^ L)) ^
          ((a - gamma) * ((i : ℕ) + 1))) *
        X ^ ((i : ℕ) + 1) := by
  calc
    Polynomial.map (Int.castRingHom (ZMod (p ^ L)))
        (wooleySection7TransformedLow
          k r p c a gamma L omega h omegaInv psi G i) =
      ∑ d : Fin r,
        C (((wooleySection7TransformedPolynomial
          k r p c a gamma L omega h omegaInv psi G i).coeff
            ((d : ℕ) + 1) : ℤ) : ZMod (p ^ L)) *
          X ^ ((d : ℕ) + 1) := by
      unfold wooleySection7TransformedLow
      simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X]
      apply Finset.sum_congr rfl
      intro d hd
      rfl
    _ = ∑ d : Fin r,
        C (if i = d then
          (p : ZMod (p ^ L)) ^ ((a - gamma) * ((d : ℕ) + 1))
          else 0) * X ^ ((d : ℕ) + 1) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [wooleySection7TransformedPolynomial_coeff_low
        hp hrk hgamma omega h omegaInv homega hsep hh psi G hG hInv]
    _ = C ((p : ZMod (p ^ L)) ^
          ((a - gamma) * ((i : ℕ) + 1))) *
        X ^ ((i : ℕ) + 1) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro d hd hdi
        simp [Ne.symm hdi]
      · simp

/-- A polynomial vanishing after reduction modulo `p^L` is coefficientwise
divisible by the corresponding integral prime power. -/
theorem wooleyPolynomial_C_primePower_dvd_of_map_eq_zero
    {p L : ℕ} (f : Polynomial ℤ)
    (hmap : Polynomial.map (Int.castRingHom (ZMod (p ^ L))) f = 0) :
    C ((p : ℤ) ^ L) ∣ f := by
  rw [C_dvd_iff_dvd_coeff]
  intro n
  have hcoeff := congrArg (fun g : Polynomial (ZMod (p ^ L)) => g.coeff n) hmap
  simp only [coeff_map, coeff_zero] at hcoeff
  change (f.coeff n : ZMod (p ^ L)) = 0 at hcoeff
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcoeff
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hcoeff ⊢
  exact hcoeff

/-- The low-coefficient error made by choosing integral representatives of
the modular inverse is an exact multiple of `p^L`. -/
theorem wooleySection7TransformedLow_exists_modulus_error
    {k r p c a gamma L : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (omega h omegaInv : ℤ)
    (homega : omega ≠ 0) (hsep : h = omega * (p : ℤ) ^ gamma)
    (hh : h ≠ 0) (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L)))
    (hG : G * Matrix.transpose
        (wooleyIntMatrixMod
          (wooleySection7OmegaMatrix (p := p) (c := c)
            hrk h hh psi) (p ^ L)) = 1)
    (hInv : (omegaInv : ZMod (p ^ L)) *
      (omega : ZMod (p ^ L)) = 1)
    (i : Fin r) :
    ∃ Error : Polynomial ℤ,
      wooleySection7TransformedLow
          k r p c a gamma L omega h omegaInv psi G i =
        C ((p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1))) *
            X ^ ((i : ℕ) + 1) +
          C ((p : ℤ) ^ L) * Error := by
  let low := wooleySection7TransformedLow
    k r p c a gamma L omega h omegaInv psi G i
  let mono : Polynomial ℤ :=
    C ((p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1))) *
      X ^ ((i : ℕ) + 1)
  have hmapLow := wooleySection7TransformedLow_map_eq_monomial
    hp hrk hgamma omega h omegaInv homega hsep hh psi G hG hInv i
  have hmapSub : Polynomial.map (Int.castRingHom (ZMod (p ^ L)))
      (low - mono) = 0 := by
    dsimp only [low, mono]
    rw [Polynomial.map_sub, hmapLow]
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X]
    have hpcast :
        (Int.castRingHom (ZMod (p ^ L)))
            ((p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1))) =
          (p : ZMod (p ^ L)) ^ ((a - gamma) * ((i : ℕ) + 1)) := by
      change (((p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1)) : ℤ) :
          ZMod (p ^ L)) = _
      norm_cast
    rw [hpcast]
    exact sub_self _
  obtain ⟨Error, hError⟩ :=
    wooleyPolynomial_C_primePower_dvd_of_map_eq_zero (low - mono) hmapSub
  refine ⟨Error, ?_⟩
  dsimp only [low, mono] at hError ⊢
  rw [← hError]
  ring

/-- Exact exponent ledger behind (7.11).  The common high-degree valuation
splits into the row valuation, the advertised spacing, and a nonnegative
row-dependent surplus. -/
theorem wooleySection7_tail_exponent_eq
    {k r a gamma : ℕ} (hrk : r ≤ k) (hgamma : gamma ≤ a)
    (hgammaK : gamma * k ≤ a) (i : Fin r) :
    a * (r + 1) - gamma * k =
      (a - gamma) * ((i : ℕ) + 1) +
        (a - (k - r) * gamma) +
        (r - ((i : ℕ) + 1)) * (a - gamma) := by
  have hi : (i : ℕ) + 1 ≤ r := i.isLt
  have hkr : k - r + r = k := Nat.sub_add_cancel hrk
  have hkgamma : (k - r) * gamma ≤ a := by
    have : (k - r) * gamma ≤ k * gamma :=
      Nat.mul_le_mul_right gamma (Nat.sub_le k r)
    exact this.trans (by simpa [Nat.mul_comm] using hgammaK)
  have hA : gamma + (a - gamma) = a := Nat.add_sub_of_le hgamma
  have hS : (k - r) * gamma + (a - (k - r) * gamma) = a :=
    Nat.add_sub_of_le hkgamma
  have hS' : gamma * (k - r) + (a - (k - r) * gamma) = a := by
    simpa [Nat.mul_comm] using hS
  have hD : gamma * k + (a * (r + 1) - gamma * k) = a * (r + 1) := by
    apply Nat.add_sub_of_le
    exact hgammaK.trans (by
      have hrPos : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hrPos)
  have hsplitK : gamma * k = gamma * (k - r) + gamma * r := by
    calc
      gamma * k = gamma * ((k - r) + r) := by rw [hkr]
      _ = _ := Nat.mul_add _ _ _
  have hsplitR :
      (a - gamma) * r =
        (a - gamma) * ((i : ℕ) + 1) +
          (r - ((i : ℕ) + 1)) * (a - gamma) := by
    have hir : (i : ℕ) + 1 + (r - ((i : ℕ) + 1)) = r :=
      Nat.add_sub_of_le hi
    calc
      (a - gamma) * r =
          (a - gamma) * (((i : ℕ) + 1) +
            (r - ((i : ℕ) + 1))) := by rw [hir]
      _ = (a - gamma) * ((i : ℕ) + 1) +
          (a - gamma) * (r - ((i : ℕ) + 1)) := by
            rw [Nat.mul_add]
      _ = _ := by rw [Nat.mul_comm (a - gamma)
        (r - ((i : ℕ) + 1))]
  have hAR : a * (r + 1) = a * r + a := by ring
  have hpair : gamma * r + (a - gamma) * r = a * r := by
    rw [← Nat.add_mul, hA]
  have htotal :
      gamma * k +
          ((a - gamma) * ((i : ℕ) + 1) +
            (a - (k - r) * gamma) +
            (r - ((i : ℕ) + 1)) * (a - gamma)) =
        a * (r + 1) := by
    calc
      gamma * k +
          ((a - gamma) * ((i : ℕ) + 1) +
            (a - (k - r) * gamma) +
            (r - ((i : ℕ) + 1)) * (a - gamma)) =
        (gamma * (k - r) + (a - (k - r) * gamma)) +
          (gamma * r +
            ((a - gamma) * ((i : ℕ) + 1) +
              (r - ((i : ℕ) + 1)) * (a - gamma))) := by
          rw [hsplitK]
          ring
      _ = a + (gamma * r + (a - gamma) * r) := by
        rw [hsplitR, hS']
      _ = a + a * r := by rw [hpair]
      _ = a * (r + 1) := by ring
  exact Nat.add_left_cancel (hD.trans htotal.symm)

/-- The transformed row is a row factor times a genuinely spaced lower
equation, up to the explicit `p^L` error caused by choosing integral lifts of
the modular inverse.  This is the exact algebraic content of (7.11). -/
theorem wooleySection7TransformedPolynomial_exists_lower_equation
    {k r p c a gamma L : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (hgammaK : gamma * k ≤ a)
    (omega h omegaInv : ℤ) (homega : omega ≠ 0)
    (hsep : h = omega * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ)
    (G : Matrix (Fin r) (Fin r) (ZMod (p ^ L)))
    (hG : G * Matrix.transpose
        (wooleyIntMatrixMod
          (wooleySection7OmegaMatrix (p := p) (c := c)
            hrk h hh psi) (p ^ L)) = 1)
    (hInv : (omegaInv : ZMod (p ^ L)) *
      (omega : ZMod (p ^ L)) = 1)
    (i : Fin r) :
    ∃ Xi Error : Polynomial ℤ,
      wooleySection7TransformedPolynomial
          k r p c a gamma L omega h omegaInv psi G i =
        C ((p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1))) *
          (X ^ ((i : ℕ) + 1) +
            C ((p : ℤ) ^ (a - (k - r) * gamma)) * Xi) +
          C ((p : ℤ) ^ L) * Error := by
  obtain ⟨Theta, hTheta⟩ :=
    wooleySection7TransformedPolynomial_exists_commonTail
      hp hrk hgamma hgammaK omega h omegaInv hsep psi G i
  obtain ⟨Error, hError⟩ :=
    wooleySection7TransformedLow_exists_modulus_error
      hp hrk hgamma omega h omegaInv homega hsep hh psi G hG hInv i
  let surplus := r - ((i : ℕ) + 1)
  let Xi := C ((p : ℤ) ^ (surplus * (a - gamma))) * Theta
  refine ⟨Xi, Error, ?_⟩
  rw [hTheta]
  change
    wooleySection7TransformedLow
        k r p c a gamma L omega h omegaInv psi G i +
      C ((p : ℤ) ^ (a * (r + 1) - gamma * k)) * Theta = _
  rw [hError]
  have hexp := wooleySection7_tail_exponent_eq hrk hgamma hgammaK i
  have hfactorC :
      C ((p : ℤ) ^ (a * (r + 1) - gamma * k)) =
        C ((p : ℤ) ^ ((a - gamma) * ((i : ℕ) + 1))) *
          C ((p : ℤ) ^ (a - (k - r) * gamma)) *
          C ((p : ℤ) ^
            ((r - ((i : ℕ) + 1)) * (a - gamma))) := by
    rw [hexp, pow_add, pow_add, C_mul, C_mul]
  rw [hfactorC]
  dsimp only [Xi, surplus]
  ring

#print axioms wooleySection7_primePower_mul_affineCore
#print axioms wooleySection7_column_exponent_add
#print axioms wooleySection7TranslatedTop_eq_columnFactor_mul
#print axioms wooleySection7ColumnNormalizedPolynomial_coeff
#print axioms wooleySection7ColumnNormalizedPolynomial_coeff_zero
#print axioms wooleySection7ColumnNormalizedPolynomial_high_coeff_dvd
#print axioms wooleyPolynomial_exists_positiveLow_add_scalarTail
#print axioms wooleySection7ColumnNormalizedPolynomial_exists_commonTail
#print axioms wooleyZModMatrixIntLift_cast
#print axioms wooleySection7_exists_int_unit_inverse
#print axioms wooley_unit_power_transport
#print axioms wooleySection7_inverse_combination_low_coefficient
#print axioms wooleySection7TransformedPolynomial_coeff_low
#print axioms wooleySection7TransformedPolynomial_coeff_zero
#print axioms wooleySection7TransformedPolynomial_high_coeff_dvd
#print axioms wooleySection7TransformedPolynomial_exists_commonTail
#print axioms wooleySection7TransformedLow_map_eq_monomial
#print axioms wooleyPolynomial_C_primePower_dvd_of_map_eq_zero
#print axioms wooleySection7TransformedLow_exists_modulus_error
#print axioms wooleySection7_tail_exponent_eq
#print axioms wooleySection7TransformedPolynomial_exists_lower_equation

end

end GafniTao
