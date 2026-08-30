import RiemannZeta.GuthMaynard.DFIEquation23Main

/-!
# Reduced moduli in DFI equation (23)

DFI explicitly requires `a/q` and `b/q` to be reduced before applying the
divisor Voronoi formula.  This file formalizes that source convention and the
exact equality of the original and reduced additive characters.
-/

open Complex

namespace RiemannZeta.GuthMaynard

/-- The reduced denominator `q / gcd(a,q)`, totalized at `q = 0` so it can
be used under finite sums before positivity of the summation index is opened. -/
def dfiReducedDenominator (a q : ℕ) : ℕ := q / a.gcd q

/-- The reduced numerator and denominator of `a/q`. -/
structure DFIReducedModulus (a q : ℕ) [NeZero q] where
  /-- The `gcd` component of `DFIReducedModulus`. -/
  gcd : ℕ := a.gcd q
  /-- The `numerator` component of `DFIReducedModulus`. -/
  numerator : ℕ := a / a.gcd q
  /-- The `denominator` component of `DFIReducedModulus`. -/
  denominator : ℕ := q / a.gcd q
  gcd_pos : 0 < gcd
  denominator_pos : 0 < denominator
  numerator_reconstruct : gcd * numerator = a
  denominator_reconstruct : gcd * denominator = q
  coprime : numerator.Coprime denominator

/-- The `dfiReducedModulus` definition used by the source-facing construction in `DFIReducedModulus`. -/
noncomputable def dfiReducedModulus (a q : ℕ) [NeZero q] :
    DFIReducedModulus a q where
  gcd := a.gcd q
  numerator := a / a.gcd q
  denominator := q / a.gcd q
  gcd_pos := Nat.gcd_pos_of_pos_right a (NeZero.pos q)
  denominator_pos := Nat.div_pos (Nat.gcd_le_right a (NeZero.pos q))
    (Nat.gcd_pos_of_pos_right a (NeZero.pos q))
  numerator_reconstruct := Nat.mul_div_cancel' (Nat.gcd_dvd_left a q)
  denominator_reconstruct := Nat.mul_div_cancel' (Nat.gcd_dvd_right a q)
  coprime := Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_right a (NeZero.pos q))

instance (a q : ℕ) [NeZero q] : NeZero (dfiReducedModulus a q).denominator :=
  ⟨(dfiReducedModulus a q).denominator_pos.ne'⟩

theorem dfiReducedModulus_denominator_eq (a q : ℕ) [NeZero q] :
    (dfiReducedModulus a q).denominator = dfiReducedDenominator a q := rfl

/-- Reduction of `a/q` can only decrease its denominator.  DFI uses this
elementary fact when the dual transition `r²/S` is enlarged to the original
delta-method modulus `q²/S`. -/
theorem dfiReducedModulus_denominator_le (a q : ℕ) [NeZero q] :
    (dfiReducedModulus a q).denominator ≤ q := by
  change q / a.gcd q ≤ q
  exact Nat.div_le_self q (a.gcd q)

/-- If the source coefficients are coprime, the two gcd factors created by
reducing `a/q` and `b/q` have product dividing `q`.  This is the arithmetic
cancellation used in DFI equation (29); bounding the two gcds separately would
introduce a spurious dependence on `a` and `b`. -/
theorem gcd_mul_gcd_dvd_right_of_coprime
    (a b q : ℕ) (hab : a.Coprime b) :
    Nat.gcd a q * Nat.gcd b q ∣ q := by
  simpa [Nat.gcd_comm] using
    (hab.gcd_both q q).mul_dvd_of_dvd_of_dvd
      (Nat.gcd_dvd_left q a) (Nat.gcd_dvd_left q b)

/-- Exact inverse-square-root normalization of the reduced denominator.
Unlike the convenient one-variable majorant below, this identity retains the
gcd factor needed for the coprime two-variable cancellation in DFI. -/
theorem dfiReducedModulus_denominator_rpow_neg_half_eq
    (a q : ℕ) [NeZero q] :
    ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) =
      Real.sqrt (Nat.gcd a q) / Real.sqrt q := by
  let R := dfiReducedModulus a q
  have hdenR : (0 : ℝ) < R.denominator := by exact_mod_cast R.denominator_pos
  have hEq : Real.sqrt q = Real.sqrt R.gcd * Real.sqrt R.denominator := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg R.gcd)]
    congr 1
    exact_mod_cast R.denominator_reconstruct.symm
  rw [Real.rpow_neg (Nat.cast_nonneg R.denominator), ← Real.sqrt_eq_rpow]
  change (Real.sqrt R.denominator)⁻¹ = Real.sqrt R.gcd / Real.sqrt q
  rw [hEq]
  have hg : 0 < Real.sqrt R.gcd := Real.sqrt_pos.2 (by exact_mod_cast R.gcd_pos)
  have hd : 0 < Real.sqrt R.denominator := Real.sqrt_pos.2 hdenR
  field_simp

/-- The inverse square root of a reduced denominator retains only the
harmless numerator gcd.  This is the exact normalization used when the
DFI equation-(29) transform bounds are combined with Weil's estimate. -/
theorem dfiReducedModulus_denominator_rpow_neg_half_le
    (a q : ℕ) [NeZero q] (ha : 0 < a) :
    ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      Real.sqrt a / Real.sqrt q := by
  let R := dfiReducedModulus a q
  have hq : 0 < q := NeZero.pos q
  have hden : 0 < R.denominator := R.denominator_pos
  have hg : R.gcd ≤ a := Nat.gcd_le_left q ha
  have hrec : R.gcd * R.denominator = q := R.denominator_reconstruct
  have hdenR : (0 : ℝ) < R.denominator := by exact_mod_cast hden
  have hEq : Real.sqrt q = Real.sqrt R.gcd * Real.sqrt R.denominator := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg R.gcd)]
    congr 1
    exact_mod_cast hrec.symm
  rw [Real.rpow_neg (Nat.cast_nonneg R.denominator), ← Real.sqrt_eq_rpow]
  have hsqrtg : Real.sqrt R.gcd ≤ Real.sqrt a := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hg)
  have hsqrtDen : 0 < Real.sqrt R.denominator := Real.sqrt_pos.2 hdenR
  calc
    (Real.sqrt R.denominator)⁻¹ =
        Real.sqrt R.gcd / (Real.sqrt R.gcd * Real.sqrt R.denominator) := by
      by_cases hg0 : R.gcd = 0
      · have : q = 0 := by simpa [hg0] using hrec.symm
        exact (NeZero.ne q this).elim
      field_simp
    _ ≤ Real.sqrt a / (Real.sqrt R.gcd * Real.sqrt R.denominator) := by
      gcongr
    _ = Real.sqrt a / Real.sqrt q := by rw [← hEq]

/-- First-power companion to
`dfiReducedModulus_denominator_rpow_neg_half_le`. -/
theorem dfiReducedModulus_denominator_inv_le
    (a q : ℕ) [NeZero q] (ha : 0 < a) :
    (((dfiReducedModulus a q).denominator : ℝ)⁻¹) ≤ (a : ℝ) / q := by
  let R := dfiReducedModulus a q
  have hq : 0 < q := NeZero.pos q
  have hg : R.gcd ≤ a := Nat.gcd_le_left q ha
  have hrec : R.gcd * R.denominator = q := R.denominator_reconstruct
  have hgR : (0 : ℝ) < R.gcd := by exact_mod_cast R.gcd_pos
  have hEq : (q : ℝ) = R.gcd * R.denominator := by exact_mod_cast hrec.symm
  calc
    ((R.denominator : ℝ))⁻¹ = (R.gcd : ℝ) / q := by
      rw [hEq]
      field_simp
    _ ≤ (a : ℝ) / q := by
      gcongr

/-- Exact first-power normalization, retained separately from the one-variable
majorant so the product of the two source gcds remains available. -/
theorem dfiReducedModulus_denominator_inv_eq
    (a q : ℕ) [NeZero q] :
    (((dfiReducedModulus a q).denominator : ℝ)⁻¹) =
      (Nat.gcd a q : ℝ) / q := by
  let R := dfiReducedModulus a q
  have hEq : (q : ℝ) = R.gcd * R.denominator := by
    exact_mod_cast R.denominator_reconstruct.symm
  change ((R.denominator : ℝ))⁻¹ = (R.gcd : ℝ) / q
  rw [hEq]
  have hg : (R.gcd : ℝ) ≠ 0 := by exact_mod_cast R.gcd_pos.ne'
  have hd : (R.denominator : ℝ) ≠ 0 := by exact_mod_cast R.denominator_pos.ne'
  field_simp

/-- The logarithm of a reduced denominator is uniformly bounded by the
logarithm of the original positive modulus.  This is the exact uniformity
needed when the two reduced Voronoi moduli occur in DFI equation (27). -/
theorem abs_log_dfiReducedModulus_denominator_le (a q : ℕ) [NeZero q] :
    |Real.log ((dfiReducedModulus a q).denominator : ℝ)| ≤
      Real.log (q : ℝ) := by
  have hdenPos : (0 : ℝ) < (dfiReducedModulus a q).denominator := by
    exact_mod_cast (dfiReducedModulus a q).denominator_pos
  have hdenOne : (1 : ℝ) ≤ (dfiReducedModulus a q).denominator := by
    exact_mod_cast (dfiReducedModulus a q).denominator_pos
  have hdenLe : ((dfiReducedModulus a q).denominator : ℝ) ≤ q := by
    exact_mod_cast dfiReducedModulus_denominator_le a q
  rw [abs_of_nonneg (Real.log_nonneg hdenOne)]
  exact Real.log_le_log hdenPos hdenLe

theorem abs_log_dfiReducedDenominator_le
    (a q : ℕ) (hq : 0 < q) :
    |Real.log (dfiReducedDenominator a q : ℝ)| ≤ Real.log (q : ℝ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  simpa only [dfiReducedModulus_denominator_eq] using
    abs_log_dfiReducedModulus_denominator_le a q

theorem dfiReducedModulus_numerator_isUnit (a q : ℕ) [NeZero q] :
    IsUnit ((dfiReducedModulus a q).numerator :
      ZMod (dfiReducedModulus a q).denominator) := by
  rw [ZMod.isUnit_iff_coprime]
  exact (dfiReducedModulus a q).coprime

/-- Multiplying a frequency by `a` modulo `q` gives exactly the same complex
additive character as multiplying it by the reduced numerator modulo the
reduced denominator. -/
theorem stdAddChar_mul_eq_reduced (a q d n : ℕ) [NeZero q] :
    ZMod.stdAddChar ((a * d * n : ℕ) : ZMod q) =
      ZMod.stdAddChar
        (((dfiReducedModulus a q).numerator * d * n : ℕ) :
          ZMod (dfiReducedModulus a q).denominator) := by
  let R := dfiReducedModulus a q
  have hleft := ZMod.stdAddChar_coe (N := q) ((a * d * n : ℕ) : ℤ)
  have hright := ZMod.stdAddChar_coe (N := R.denominator)
    ((R.numerator * d * n : ℕ) : ℤ)
  simp only [Int.cast_natCast] at hleft hright
  rw [hleft, hright]
  apply congrArg Complex.exp
  have hg : (R.gcd : ℂ) ≠ 0 := by exact_mod_cast R.gcd_pos.ne'
  have hratio : (a : ℂ) / (q : ℂ) =
      (R.numerator : ℂ) / (R.denominator : ℂ) := by
    have haC : (R.gcd : ℂ) * (R.numerator : ℂ) = (a : ℂ) := by
      exact_mod_cast R.numerator_reconstruct
    have hqC : (R.gcd : ℂ) * (R.denominator : ℂ) = (q : ℂ) := by
      exact_mod_cast R.denominator_reconstruct
    rw [← haC, ← hqC]
    field_simp
  calc
    2 * (Real.pi : ℂ) * I * (((a * d * n : ℕ) : ℂ)) / q =
        (2 * (Real.pi : ℂ) * I * d * n) * ((a : ℂ) / q) := by
          push_cast
          ring
    _ = (2 * (Real.pi : ℂ) * I * d * n) *
        ((R.numerator : ℂ) / (R.denominator : ℂ)) := by rw [hratio]
    _ = 2 * (Real.pi : ℂ) * I * (((R.numerator * d * n : ℕ) : ℂ)) /
        (R.denominator : ℂ) := by
          push_cast
          ring

theorem stdAddChar_neg_mul_eq_reduced (a q d n : ℕ) [NeZero q] :
    ZMod.stdAddChar (-((a * d * n : ℕ) : ZMod q)) =
      ZMod.stdAddChar
        (-(((dfiReducedModulus a q).numerator * d * n : ℕ) :
          ZMod (dfiReducedModulus a q).denominator)) := by
  rw [AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv,
    stdAddChar_mul_eq_reduced]

/-- If `q = g * q'`, multiplying a representative modulo `q'` by `g`
lifts its standard additive character exactly to modulus `q`.  This is the
cross-modulus identity needed to put the reduced inverse frequencies in DFI
equation (23) back into one modulus in equation (24). -/
theorem stdAddChar_gcd_mul_val_lift
    (q g q' : ℕ) [NeZero q] [NeZero q'] (hq : g * q' = q)
    (z : ZMod q') :
    ZMod.stdAddChar (((g * z.val : ℕ) : ZMod q)) = ZMod.stdAddChar z := by
  have hqC : (q : ℂ) = (g : ℂ) * (q' : ℂ) := by
    exact_mod_cast hq.symm
  have hq'ne : (q' : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne q'
  have hgneNat : g ≠ 0 := by
    intro hg
    rw [hg, zero_mul] at hq
    exact NeZero.ne q hq.symm
  have hgne : (g : ℂ) ≠ 0 := by exact_mod_cast hgneNat
  calc
    ZMod.stdAddChar (((g * z.val : ℕ) : ZMod q)) =
        Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * ((g * z.val : ℕ) : ℂ) / q) := by
      simpa only [Int.cast_natCast] using
        ZMod.stdAddChar_coe (N := q) ((g * z.val : ℕ) : ℤ)
    _ = Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (z.val : ℂ) / q') := by
      apply congrArg Complex.exp
      rw [hqC]
      push_cast
      field_simp
    _ = ZMod.stdAddChar ((z.val : ℕ) : ZMod q') := by
      simpa only [Int.cast_natCast] using
        (ZMod.stdAddChar_coe (N := q') (z.val : ℤ)).symm
    _ = ZMod.stdAddChar z := by rw [ZMod.natCast_zmod_val]

/-- Natural-frequency form of the same character lift.  Unlike the
representative form above, this version can be applied before reducing a
product modulo `q'`, which is exactly what the inverse-frequency terms of
equation (24) require. -/
theorem stdAddChar_gcd_mul_nat_lift
    (q g q' x : ℕ) [NeZero q] [NeZero q'] (hq : g * q' = q) :
    ZMod.stdAddChar (((g * x : ℕ) : ZMod q)) =
      ZMod.stdAddChar ((x : ℕ) : ZMod q') := by
  have hqC : (q : ℂ) = (g : ℂ) * (q' : ℂ) := by
    exact_mod_cast hq.symm
  have hgneNat : g ≠ 0 := by
    intro hg
    rw [hg, zero_mul] at hq
    exact NeZero.ne q hq.symm
  have hgne : (g : ℂ) ≠ 0 := by exact_mod_cast hgneNat
  have hq'ne : (q' : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q'
  calc
    ZMod.stdAddChar (((g * x : ℕ) : ZMod q)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((g * x : ℕ) : ℂ) / q) := by
      simpa only [Int.cast_natCast] using
        ZMod.stdAddChar_coe (N := q) ((g * x : ℕ) : ℤ)
    _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) / q') := by
      apply congrArg Complex.exp
      rw [hqC]
      push_cast
      field_simp
    _ = ZMod.stdAddChar ((x : ℕ) : ZMod q') := by
      simpa only [Int.cast_natCast] using
        (ZMod.stdAddChar_coe (N := q') (x : ℤ)).symm

/-- Modular inversion commutes with passage from modulus `q` to a divisor
`q'` when the residue is a unit modulo `q`.  The left side is written using
the canonical natural representative because that is what the character
lift in `stdAddChar_gcd_mul_val_lift` consumes. -/
theorem zmod_inv_val_cast_of_dvd
    (q q' d : ℕ) [NeZero q] [NeZero q'] (hq' : q' ∣ q)
    (hd : d.Coprime q) :
    ((((d : ZMod q)⁻¹).val : ℕ) : ZMod q') = (d : ZMod q')⁻¹ := by
  have hdUnit : IsUnit (d : ZMod q) := (ZMod.isUnit_iff_coprime d q).2 hd
  have hmul : (d : ZMod q)⁻¹ * (d : ZMod q) = 1 :=
    ZMod.inv_mul_of_unit _ hdUnit
  have hcast := congrArg (ZMod.castHom hq' (ZMod q')) hmul
  have hcastMul :
      ((((d : ZMod q)⁻¹).val : ℕ) : ZMod q') * (d : ZMod q') = 1 := by
    simpa only [map_mul, map_one, map_natCast, ZMod.castHom_apply,
      ZMod.cast_eq_val] using hcast
  exact (ZMod.inv_eq_of_mul_eq_one q' (d : ZMod q')
    ((((d : ZMod q)⁻¹).val : ℕ) : ZMod q') (by simpa [mul_comm] using hcastMul)).symm

/-- In a `ZMod` ring the inverse of a product of units is the product of
their inverses.  `ZMod` is totalized rather than a division ring, so the
unit hypotheses are essential and kept explicit. -/
theorem zmod_mul_inv_of_isUnit
    (q : ℕ) (x y : ZMod q) (hx : IsUnit x) (hy : IsUnit y) :
    (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  apply ZMod.inv_eq_of_mul_eq_one q
  calc
    (x * y) * (x⁻¹ * y⁻¹) = (x * x⁻¹) * (y * y⁻¹) := by ring
    _ = 1 := by rw [ZMod.mul_inv_of_unit x hx, ZMod.mul_inv_of_unit y hy, one_mul]

/-- The fixed modulus-`q` frequency corresponding to the inverse additive
phase at the reduced denominator of `a/q`. -/
noncomputable def dfiLiftedInverseFrequency
    (a q n : ℕ) [NeZero q] : ZMod q :=
  let R := dfiReducedModulus a q
  ((R.gcd * ((R.numerator : ZMod R.denominator)⁻¹ *
    (n : ZMod R.denominator)).val : ℕ) : ZMod q)

/-- Exact inverse-phase lift used in DFI equation (24).  After reducing
`a/q`, the phase `(a' d)⁻¹ n / q'` equals a fixed lifted frequency times
`d⁻¹ / q` at the original modulus. -/
theorem stdAddChar_reduced_inverse_eq_lifted
    (a q d n : ℕ) [NeZero q] (hd : d.Coprime q) :
    ZMod.stdAddChar
        (((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator)⁻¹) *
          (n : ZMod (dfiReducedModulus a q).denominator)) =
      ZMod.stdAddChar
        (dfiLiftedInverseFrequency a q n * (d : ZMod q)⁻¹) := by
  let R := dfiReducedModulus a q
  have hdenDvd : R.denominator ∣ q := by
    exact ⟨R.gcd, by rw [mul_comm, R.denominator_reconstruct]⟩
  have hnumUnit : IsUnit (R.numerator : ZMod R.denominator) :=
    dfiReducedModulus_numerator_isUnit a q
  have hdUnitQ : IsUnit (d : ZMod q) := (ZMod.isUnit_iff_coprime d q).2 hd
  have hdUnitR : IsUnit (d : ZMod R.denominator) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hd.of_dvd_right hdenDvd
  have hInvCast := zmod_inv_val_cast_of_dvd q R.denominator d hdenDvd hd
  have hLift := stdAddChar_gcd_mul_nat_lift q R.gcd R.denominator
    (((R.numerator : ZMod R.denominator)⁻¹ *
      (n : ZMod R.denominator)).val * ((d : ZMod q)⁻¹).val)
    R.denominator_reconstruct
  rw [dfiLiftedInverseFrequency]
  change ZMod.stdAddChar ((((R.numerator * d : ℕ) : ZMod R.denominator)⁻¹) *
      (n : ZMod R.denominator)) = _
  rw [show dfiReducedModulus a q = R from rfl]
  rw [Nat.cast_mul]
  rw [zmod_mul_inv_of_isUnit R.denominator
    (R.numerator : ZMod R.denominator) (d : ZMod R.denominator)
    hnumUnit hdUnitR]
  rw [← hInvCast]
  calc
    ZMod.stdAddChar
        ((R.numerator : ZMod R.denominator)⁻¹ *
          ((((d : ZMod q)⁻¹).val : ℕ) : ZMod R.denominator) *
          (n : ZMod R.denominator)) =
        ZMod.stdAddChar
          (((((R.numerator : ZMod R.denominator)⁻¹ *
            (n : ZMod R.denominator)).val * ((d : ZMod q)⁻¹).val : ℕ) :
              ZMod R.denominator)) := by
      congr 1
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      ring
    _ = ZMod.stdAddChar
          (((R.gcd * (((R.numerator : ZMod R.denominator)⁻¹ *
            (n : ZMod R.denominator)).val * ((d : ZMod q)⁻¹).val) : ℕ) :
              ZMod q)) := hLift.symm
    _ = ZMod.stdAddChar
          (((R.gcd * ((R.numerator : ZMod R.denominator)⁻¹ *
            (n : ZMod R.denominator)).val : ℕ) : ZMod q) *
              (d : ZMod q)⁻¹) := by
      congr 1
      rw [Nat.cast_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
      push_cast
      ring

theorem dfiReducedModulus_frequency_isUnit
    (a q d : ℕ) [NeZero q] (hd : d.Coprime q) :
    IsUnit ((((dfiReducedModulus a q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus a q).denominator)) := by
  rw [ZMod.isUnit_iff_coprime]
  let R := dfiReducedModulus a q
  have hden : R.denominator ∣ q := by
    refine ⟨R.gcd, ?_⟩
    simpa [mul_comm] using R.denominator_reconstruct.symm
  exact R.coprime.mul_left (hd.of_dvd_right hden)

theorem dfiReducedModulus_neg_frequency_isUnit
    (a q d : ℕ) [NeZero q] (hd : d.Coprime q) :
    IsUnit (-((((dfiReducedModulus a q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus a q).denominator))) :=
  (dfiReducedModulus_frequency_isUnit a q d hd).neg

theorem periodicDivisorCoeff_source_eq_reduced
    (a q d n : ℕ) [NeZero q] :
    periodicDivisorCoeff q
        (dfiVoronoiCharacter q (((a * d : ℕ) : ZMod q))) n =
      periodicDivisorCoeff (dfiReducedModulus a q).denominator
        (dfiVoronoiCharacter (dfiReducedModulus a q).denominator
          ((((dfiReducedModulus a q).numerator * d : ℕ) :
            ZMod (dfiReducedModulus a q).denominator))) n := by
  rw [periodicDivisorCoeff_voronoiCharacter,
    periodicDivisorCoeff_voronoiCharacter]
  congr 1
  simpa only [Nat.cast_mul] using stdAddChar_mul_eq_reduced a q d n

theorem periodicDivisorCoeff_neg_source_eq_reduced
    (a q d n : ℕ) [NeZero q] :
    periodicDivisorCoeff q
        (dfiVoronoiCharacter q (-(((a * d : ℕ) : ZMod q)))) n =
      periodicDivisorCoeff (dfiReducedModulus a q).denominator
        (dfiVoronoiCharacter (dfiReducedModulus a q).denominator
          (-((((dfiReducedModulus a q).numerator * d : ℕ) :
            ZMod (dfiReducedModulus a q).denominator)))) n := by
  rw [periodicDivisorCoeff_voronoiCharacter,
    periodicDivisorCoeff_voronoiCharacter]
  congr 1
  simpa only [neg_mul, Nat.cast_mul] using stdAddChar_neg_mul_eq_reduced a q d n

/-- Equation (23) with the two independently reduced Voronoi moduli. -/
noncomputable def dfiEquation23ReducedLeft
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ) (E : ℝ → ℝ → ℂ) : ℂ :=
  periodicDivisorWeightedSum qₓ (dfiVoronoiCharacter qₓ dₓ)
    (fun x => periodicDivisorWeightedSum qᵧ
      (dfiVoronoiCharacter qᵧ dᵧ) (E x))

/-- The double divisor series carrying the two additive phases in DFI (22),
before reducing `a/q` and `b/q` as required immediately before equation (23). -/
noncomputable def dfiEquation23SourceLeft
    (q a b d : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℂ :=
  periodicDivisorWeightedSum q
    (dfiVoronoiCharacter q (((a * d : ℕ) : ZMod q)))
    (fun x => periodicDivisorWeightedSum q
      (dfiVoronoiCharacter q (-(((b * d : ℕ) : ZMod q)))) (E x))

/-- Exact source-entry reduction of both phases in DFI equation (23). -/
theorem dfiEquation23SourceLeft_eq_reduced
    (q a b d : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) :
    dfiEquation23SourceLeft q a b d E =
      dfiEquation23ReducedLeft
        (dfiReducedModulus a q).denominator
        (dfiReducedModulus b q).denominator
        ((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator))
        (-((((dfiReducedModulus b q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus b q).denominator))) E := by
  unfold dfiEquation23SourceLeft dfiEquation23ReducedLeft
  unfold periodicDivisorWeightedSum
  apply tsum_congr
  intro m
  rw [periodicDivisorCoeff_source_eq_reduced]
  congr 1
  apply tsum_congr
  intro n
  rw [periodicDivisorCoeff_neg_source_eq_reduced]

/-- The `dfiEquation23ReducedGroupedRight` definition used by the source-facing construction in `DFIReducedModulus`. -/
noncomputable def dfiEquation23ReducedGroupedRight
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ) (E : ℝ → ℝ → ℂ) : ℂ :=
  (∑ bx : DFIVoronoiBranch,
      dfiVoronoiBranchValue qₓ dₓ bx
        (fun x => dfiVoronoiBranchValue qᵧ dᵧ .mainTerm (E x))) +
    ∑ bx : DFIVoronoiBranch,
      dfiVoronoiBranchValue qₓ dₓ bx
        (fun x => dfiVoronoiRemainderValue qᵧ dᵧ (E x))

/-- The literal nine-branch expansion with independently reduced moduli. -/
noncomputable def dfiEquation23ReducedRight
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ) (E : ℝ → ℝ → ℂ) : ℂ :=
  ∑ byBranch : DFIVoronoiBranch, ∑ bxBranch : DFIVoronoiBranch,
    dfiVoronoiBranchValue qₓ dₓ bxBranch
      (fun x => dfiVoronoiBranchValue qᵧ dᵧ byBranch (E x))

/-- The `DFIEquation23ReducedFullAdmissible` definition used by the source-facing construction in `DFIReducedModulus`. -/
structure DFIEquation23ReducedFullAdmissible
    (qᵧ : ℕ) [NeZero qᵧ] (dᵧ : ZMod qᵧ) (E : ℝ → ℝ → ℂ) where
  /-- The `ySlice` component of `DFIEquation23ReducedFullAdmissible`. -/
  ySlice : ∀ x : ℝ, DFIVoronoiTestFunction (E x)
  /-- The `xAfterYBranch` component of `DFIEquation23ReducedFullAdmissible`. -/
  xAfterYBranch : ∀ branch : DFIVoronoiBranch,
    DFIVoronoiTestFunction
      (fun x => dfiVoronoiBranchValue qᵧ dᵧ branch (E x))

theorem dfiEquation23_reduced_of_fullAdmissible
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ)
    (hdₓ : IsUnit dₓ) (hdᵧ : IsUnit dᵧ)
    (E : ℝ → ℝ → ℂ)
    (hE : DFIEquation23ReducedFullAdmissible qᵧ dᵧ E) :
    dfiEquation23ReducedLeft qₓ qᵧ dₓ dᵧ E =
      dfiEquation23ReducedRight qₓ qᵧ dₓ dᵧ E := by
  unfold dfiEquation23ReducedLeft dfiEquation23ReducedRight
  have hinner : ∀ x : ℝ,
      periodicDivisorWeightedSum qᵧ (dfiVoronoiCharacter qᵧ dᵧ) (E x) =
        ∑ branch : DFIVoronoiBranch,
          dfiVoronoiBranchValue qᵧ dᵧ branch (E x) := fun x =>
    (hE.ySlice x).dfiProposition1_native_branch_sum qᵧ dᵧ hdᵧ
  simp_rw [hinner]
  have hsummable : ∀ branch : DFIVoronoiBranch,
      Summable (fun n : ℕ =>
        periodicDivisorCoeff qₓ (dfiVoronoiCharacter qₓ dₓ) n *
          dfiVoronoiBranchValue qᵧ dᵧ branch (E n)) := fun branch =>
    (hE.xAfterYBranch branch).summable_periodicDivisorWeighted qₓ
      (dfiVoronoiCharacter qₓ dₓ)
  unfold periodicDivisorWeightedSum
  simp_rw [Finset.mul_sum]
  change (∑' n : ℕ, ∑ branch : DFIVoronoiBranch,
      periodicDivisorCoeff qₓ (dfiVoronoiCharacter qₓ dₓ) n *
        dfiVoronoiBranchValue qᵧ dᵧ branch (E n)) = _
  rw [Summable.tsum_finsetSum (s := Finset.univ)
    (fun branch _ => hsummable branch)]
  apply Finset.sum_congr rfl
  intro branch _hbranch
  change periodicDivisorWeightedSum qₓ (dfiVoronoiCharacter qₓ dₓ)
      (fun x => dfiVoronoiBranchValue qᵧ dᵧ branch (E x)) = _
  exact DFIVoronoiTestFunction.dfiProposition1_native_branch_sum
    (hE.xAfterYBranch branch) qₓ dₓ hdₓ

/-- The `DFIEquation23ReducedAdmissible` definition used by the source-facing construction in `DFIReducedModulus`. -/
structure DFIEquation23ReducedAdmissible
    (qᵧ : ℕ) [NeZero qᵧ] (dᵧ : ZMod qᵧ) (E : ℝ → ℝ → ℂ) where
  /-- The `ySlice` component of `DFIEquation23ReducedAdmissible`. -/
  ySlice : ∀ x : ℝ, DFIVoronoiTestFunction (E x)
  /-- The `xMain` component of `DFIEquation23ReducedAdmissible`. -/
  xMain : DFIVoronoiTestFunction
    (fun x => dfiVoronoiBranchValue qᵧ dᵧ .mainTerm (E x))
  /-- The `xRemainder` component of `DFIEquation23ReducedAdmissible`. -/
  xRemainder : DFIVoronoiTestFunction
    (fun x => dfiVoronoiRemainderValue qᵧ dᵧ (E x))

theorem dfiEquation23_reduced_grouped_of_admissible
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ)
    (hdₓ : IsUnit dₓ) (hdᵧ : IsUnit dᵧ)
    (E : ℝ → ℝ → ℂ) (hE : DFIEquation23ReducedAdmissible qᵧ dᵧ E) :
    dfiEquation23ReducedLeft qₓ qᵧ dₓ dᵧ E =
      dfiEquation23ReducedGroupedRight qₓ qᵧ dₓ dᵧ E := by
  unfold dfiEquation23ReducedLeft dfiEquation23ReducedGroupedRight
  have hinner : ∀ x : ℝ,
      periodicDivisorWeightedSum qᵧ (dfiVoronoiCharacter qᵧ dᵧ) (E x) =
        dfiVoronoiBranchValue qᵧ dᵧ .mainTerm (E x) +
          dfiVoronoiRemainderValue qᵧ dᵧ (E x) := by
    intro x
    rw [(hE.ySlice x).dfiProposition1_native_branch_sum qᵧ dᵧ hdᵧ,
      sum_dfiVoronoiBranchValue_eq_main_add_remainder]
  simp_rw [hinner]
  have hsMain := hE.xMain.summable_periodicDivisorWeighted qₓ
    (dfiVoronoiCharacter qₓ dₓ)
  have hsRem := hE.xRemainder.summable_periodicDivisorWeighted qₓ
    (dfiVoronoiCharacter qₓ dₓ)
  unfold periodicDivisorWeightedSum
  simp_rw [mul_add]
  rw [Summable.tsum_add hsMain hsRem]
  congr 1
  · exact hE.xMain.dfiProposition1_native_branch_sum qₓ dₓ hdₓ
  · exact hE.xRemainder.dfiProposition1_native_branch_sum qₓ dₓ hdₓ

/-- The concrete equation-(21) weight is admissible for two independently
reduced moduli. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def dfiEquation23Weight_reducedAdmissible
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (qᵧ : ℕ) [NeZero qᵧ] (dᵧ : ZMod qᵧ) (hdᵧ : IsUnit dᵧ) :
    DFIEquation23ReducedAdmissible qᵧ dᵧ
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀) where
  ySlice := dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q₀ hq₀
  xMain := dfiEquation23Weight_mainBranch
    w hf hbox hφ a b ha hb h q₀ hq₀ qᵧ dᵧ
  xRemainder := dfiEquation23Weight_remainderBranch
    w hf hbox hφ a b ha hb h q₀ hq₀ qᵧ dᵧ hdᵧ

/-- The `dfiEquation23Weight_reducedFullAdmissible` definition used by the source-facing construction in `DFIReducedModulus`. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def dfiEquation23Weight_reducedFullAdmissible
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (qᵧ : ℕ) [NeZero qᵧ] (dᵧ : ZMod qᵧ) :
    DFIEquation23ReducedFullAdmissible qᵧ dᵧ
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀) where
  ySlice := dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q₀ hq₀
  xAfterYBranch := by
    intro branch
    cases branch with
    | mainTerm =>
        exact dfiEquation23Weight_mainBranch
          w hf hbox hφ a b ha hb h q₀ hq₀ qᵧ dᵧ
    | minusTerm =>
        exact dfiEquation23Weight_dualBranch
          w hf hbox hφ a b ha hb h q₀ hq₀ qᵧ dᵧ .minusTerm
    | plusTerm =>
        exact dfiEquation23Weight_dualBranch
          w hf hbox hφ a b ha hb h q₀ hq₀ qᵧ dᵧ .plusTerm

theorem dfiEquation23Weight_reduced_ungrouped
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ)
    (hdₓ : IsUnit dₓ) (hdᵧ : IsUnit dᵧ) :
    dfiEquation23ReducedLeft qₓ qᵧ dₓ dᵧ
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀) =
    dfiEquation23ReducedRight qₓ qᵧ dₓ dᵧ
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀) := by
  exact dfiEquation23_reduced_of_fullAdmissible
    qₓ qᵧ dₓ dᵧ hdₓ hdᵧ _
    (dfiEquation23Weight_reducedFullAdmissible
      w hf hbox hφ a b ha hb h q₀ hq₀ qᵧ dᵧ)

theorem dfiEquation23Weight_reduced_grouped
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q₀ : ℕ) (hq₀ : 0 < q₀)
    (qₓ qᵧ : ℕ) [NeZero qₓ] [NeZero qᵧ]
    (dₓ : ZMod qₓ) (dᵧ : ZMod qᵧ)
    (hdₓ : IsUnit dₓ) (hdᵧ : IsUnit dᵧ) :
    dfiEquation23ReducedLeft qₓ qᵧ dₓ dᵧ
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀) =
    dfiEquation23ReducedGroupedRight qₓ qᵧ dₓ dᵧ
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q₀) := by
  exact dfiEquation23_reduced_grouped_of_admissible qₓ qᵧ dₓ dᵧ hdₓ hdᵧ _
    (dfiEquation23Weight_reducedAdmissible
      w hf hbox hφ a b ha hb h q₀ hq₀ qᵧ dᵧ hdᵧ)

/-- DFI equation (23) at its source entry: the two phases from equation (22)
are reduced to their correct, generally different, Voronoi moduli and both
Voronoi formulas are then applied. -/
theorem dfiEquation23Weight_source_grouped
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) (d : ℕ) (hd : d.Coprime q) :
    dfiEquation23SourceLeft q a b d
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) =
      dfiEquation23ReducedGroupedRight
        (dfiReducedModulus a q).denominator
        (dfiReducedModulus b q).denominator
        ((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator))
        (-((((dfiReducedModulus b q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus b q).denominator)))
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) := by
  rw [dfiEquation23SourceLeft_eq_reduced]
  exact dfiEquation23Weight_reduced_grouped
    w hf hbox hφ a b ha hb h q hq
    (dfiReducedModulus a q).denominator
    (dfiReducedModulus b q).denominator
    ((((dfiReducedModulus a q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus a q).denominator))
    (-((((dfiReducedModulus b q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus b q).denominator)))
    (dfiReducedModulus_frequency_isUnit a q d hd)
    (dfiReducedModulus_neg_frequency_isUnit b q d hd)

/-- Source-entry equation (23) in the literal ungrouped nine-branch form. -/
theorem dfiEquation23Weight_source_ungrouped
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) (d : ℕ) (hd : d.Coprime q) :
    dfiEquation23SourceLeft q a b d
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) =
      dfiEquation23ReducedRight
        (dfiReducedModulus a q).denominator
        (dfiReducedModulus b q).denominator
        ((((dfiReducedModulus a q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus a q).denominator))
        (-((((dfiReducedModulus b q).numerator * d : ℕ) :
          ZMod (dfiReducedModulus b q).denominator)))
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) := by
  rw [dfiEquation23SourceLeft_eq_reduced]
  exact dfiEquation23Weight_reduced_ungrouped
    w hf hbox hφ a b ha hb h q hq
    (dfiReducedModulus a q).denominator
    (dfiReducedModulus b q).denominator
    ((((dfiReducedModulus a q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus a q).denominator))
    (-((((dfiReducedModulus b q).numerator * d : ℕ) :
      ZMod (dfiReducedModulus b q).denominator)))
    (dfiReducedModulus_frequency_isUnit a q d hd)
    (dfiReducedModulus_neg_frequency_isUnit b q d hd)

end RiemannZeta.GuthMaynard
