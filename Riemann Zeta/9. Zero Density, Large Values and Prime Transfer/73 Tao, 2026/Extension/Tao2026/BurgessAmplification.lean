import Tao2026.BurgessMoment

/-!
# Exact finite reindexing for Burgess amplification

This file starts the missing passage from the complete fourteenth moment to
the primitive prefix estimate.  It isolates the elementary part of Burgess
amplification: interval sums, their exact additive shift difference, and the
affine change of variables associated to a unit modulo the conductor.
-/

namespace Tao2026

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-- A Dirichlet-character sum on the positive interval `(N, N + H]`. -/
def burgessIntervalCharacterSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N H : ℕ) : ℂ :=
  ∑ i ∈ Finset.range H, χ ((N + i + 1 : ℕ) : ZMod q)

/-- The interval starting at zero is exactly the positive prefix convention
used by the downstream Burgess interface. -/
theorem burgessIntervalCharacterSum_zero {q H : ℕ}
    (χ : DirichletCharacter ℂ q) :
    burgessIntervalCharacterSum χ 0 H =
      ∑ n ∈ Finset.Ioc 0 H, χ (n : ZMod q) := by
  rw [sum_Ioc_zero_eq_sum_range_succ]
  simp only [burgessIntervalCharacterSum, zero_add]

/-- Splitting an interval after its first `K` terms. -/
theorem burgessIntervalCharacterSum_split {q N H K : ℕ}
    (χ : DirichletCharacter ℂ q) (hKH : K ≤ H) :
    burgessIntervalCharacterSum χ N H =
      burgessIntervalCharacterSum χ N K +
        burgessIntervalCharacterSum χ (N + K) (H - K) := by
  unfold burgessIntervalCharacterSum
  conv_lhs =>
    rw [← Nat.add_sub_of_le hKH, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  omega

/-- Splitting an interval before its last `K` terms. -/
theorem burgessIntervalCharacterSum_split_last {q N H K : ℕ}
    (χ : DirichletCharacter ℂ q) (hKH : K ≤ H) :
    burgessIntervalCharacterSum χ N H =
      burgessIntervalCharacterSum χ N (H - K) +
        burgessIntervalCharacterSum χ (N + H - K) K := by
  have hsum : H - K + K = H := Nat.sub_add_cancel hKH
  unfold burgessIntervalCharacterSum
  conv_lhs =>
    rw [← hsum, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  omega

/-- Exact two-boundary-term identity for an additive shift by `K`. -/
theorem burgessIntervalCharacterSum_sub_shift {q N H K : ℕ}
    (χ : DirichletCharacter ℂ q) (hKH : K ≤ H) :
    burgessIntervalCharacterSum χ N H -
        burgessIntervalCharacterSum χ (N + K) H =
      burgessIntervalCharacterSum χ N K -
        burgessIntervalCharacterSum χ (N + H) K := by
  rw [burgessIntervalCharacterSum_split (N := N) χ hKH]
  rw [burgessIntervalCharacterSum_split_last (N := N + K) χ hKH]
  have hstart : N + K + H - K = N + H := by omega
  rw [hstart]
  ring

/-- The trivial interval estimate, with the exact number of summands. -/
theorem norm_burgessIntervalCharacterSum_le {q N H : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ‖burgessIntervalCharacterSum χ N H‖ ≤ (H : ℝ) := by
  unfold burgessIntervalCharacterSum
  calc
    ‖∑ i ∈ Finset.range H, χ ((N + i + 1 : ℕ) : ZMod q)‖ ≤
        ∑ i ∈ Finset.range H, ‖χ ((N + i + 1 : ℕ) : ZMod q)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact DirichletCharacter.norm_le_one χ _
    _ = (H : ℝ) := by simp

/-- Moving an interval by at most `K` changes its sum by at most `2K`. -/
theorem norm_burgessIntervalCharacterSum_sub_shift_le {q N H K : ℕ}
    (χ : DirichletCharacter ℂ q) (hKH : K ≤ H) :
    ‖burgessIntervalCharacterSum χ N H -
        burgessIntervalCharacterSum χ (N + K) H‖ ≤ 2 * (K : ℝ) := by
  rw [burgessIntervalCharacterSum_sub_shift χ hKH]
  calc
    ‖burgessIntervalCharacterSum χ N K -
        burgessIntervalCharacterSum χ (N + H) K‖ ≤
        ‖burgessIntervalCharacterSum χ N K‖ +
          ‖burgessIntervalCharacterSum χ (N + H) K‖ := norm_sub_le _ _
    _ ≤ (K : ℝ) + (K : ℝ) := add_le_add
      (norm_burgessIntervalCharacterSum_le χ)
      (norm_burgessIntervalCharacterSum_le χ)
    _ = 2 * (K : ℝ) := by ring

/-- The affine line sum used when Burgess averages over a multiplier `a` and
an additive shift `b`. -/
def burgessAffineShiftSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N H a b : ℕ) : ℂ :=
  ∑ i ∈ Finset.range H,
    χ (((N + i + 1 : ℕ) : ZMod q) * ((a : ℕ) : ZMod q)⁻¹ +
      ((b : ℕ) : ZMod q))

/-- Pointwise affine reindexing after multiplication by a residue prime to
the conductor. -/
theorem dirichletCharacter_mul_affine_inv {q a b x : ℕ}
    (χ : DirichletCharacter ℂ q) (ha : Nat.Coprime a q) :
    χ (a : ZMod q) *
        χ ((x : ZMod q) * (a : ZMod q)⁻¹ + (b : ZMod q)) =
      χ ((x + a * b : ℕ) : ZMod q) := by
  rw [← map_mul]
  congr 1
  have haUnit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  push_cast
  rw [mul_add]
  calc
    (a : ZMod q) * ((x : ZMod q) * (a : ZMod q)⁻¹) +
        (a : ZMod q) * (b : ZMod q) =
        (x : ZMod q) * ((a : ZMod q) * (a : ZMod q)⁻¹) +
          (a : ZMod q) * (b : ZMod q) := by ring
    _ = (x : ZMod q) + (a : ZMod q) * (b : ZMod q) := by
      rw [ZMod.mul_inv_of_unit _ haUnit, mul_one]

/-- Exact affine reindexing of a whole interval. -/
theorem mul_burgessAffineShiftSum {q N H a b : ℕ}
    (χ : DirichletCharacter ℂ q) (ha : Nat.Coprime a q) :
    χ (a : ZMod q) * burgessAffineShiftSum χ N H a b =
      burgessIntervalCharacterSum χ (N + a * b) H := by
  simp only [burgessAffineShiftSum, burgessIntervalCharacterSum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dirichletCharacter_mul_affine_inv χ ha]
  congr 2
  omega

/-- A Dirichlet character has norm one on every unit of its source. -/
theorem norm_dirichletCharacter_natCast_eq_one {q a : ℕ}
    (χ : DirichletCharacter ℂ q) (ha : Nat.Coprime a q) :
    ‖χ (a : ZMod q)‖ = 1 := by
  have haUnit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  have hprod : χ (a : ZMod q) * χ ((a : ZMod q)⁻¹) = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit _ haUnit, map_one]
  have hnormprod : ‖χ (a : ZMod q)‖ * ‖χ ((a : ZMod q)⁻¹)‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  have haNorm := DirichletCharacter.norm_le_one χ (a : ZMod q)
  have haInvNorm := DirichletCharacter.norm_le_one χ ((a : ZMod q)⁻¹)
  nlinarith [norm_nonneg (χ (a : ZMod q)),
    norm_nonneg (χ ((a : ZMod q)⁻¹))]

/-- Consequently affine reindexing preserves the norm of the character sum. -/
theorem norm_burgessAffineShiftSum {q N H a b : ℕ}
    (χ : DirichletCharacter ℂ q) (ha : Nat.Coprime a q) :
    ‖burgessAffineShiftSum χ N H a b‖ =
      ‖burgessIntervalCharacterSum χ (N + a * b) H‖ := by
  have h := congrArg norm
    (mul_burgessAffineShiftSum (N := N) (H := H) (b := b) χ ha)
  simpa [norm_mul, norm_dirichletCharacter_natCast_eq_one χ ha] using h

/-- One shifted interval is controlled by the original interval together
with the two boundary pieces created by the shift `a*b`. -/
theorem norm_burgessIntervalCharacterSum_le_affine_add_boundary
    {q N H a b : ℕ} (χ : DirichletCharacter ℂ q)
    (ha : Nat.Coprime a q) (hab : a * b ≤ H) :
    ‖burgessIntervalCharacterSum χ N H‖ ≤
      ‖burgessAffineShiftSum χ N H a b‖ + 2 * (a * b : ℝ) := by
  have hshift := norm_burgessIntervalCharacterSum_sub_shift_le
    (N := N) χ hab
  have haff := norm_burgessAffineShiftSum
    (N := N) (H := H) (b := b) χ ha
  calc
    ‖burgessIntervalCharacterSum χ N H‖ =
        ‖(burgessIntervalCharacterSum χ N H -
            burgessIntervalCharacterSum χ (N + a * b) H) +
          burgessIntervalCharacterSum χ (N + a * b) H‖ := by ring_nf
    _ ≤ ‖burgessIntervalCharacterSum χ N H -
            burgessIntervalCharacterSum χ (N + a * b) H‖ +
          ‖burgessIntervalCharacterSum χ (N + a * b) H‖ := norm_add_le _ _
    _ ≤ 2 * (a * b : ℝ) +
          ‖burgessIntervalCharacterSum χ (N + a * b) H‖ :=
      by
        simpa [Nat.cast_mul, add_comm] using
          (add_le_add_right hshift
            ‖burgessIntervalCharacterSum χ (N + a * b) H‖)
    _ = ‖burgessAffineShiftSum χ N H a b‖ + 2 * (a * b : ℝ) := by
      rw [haff]
      ring

/-- Summing the affine interval over `1 ≤ b ≤ B` and exchanging the two
finite sums produces exactly the complete-moment inner sum
`burgessShiftSum B χ` along the residues `(N+n)/a`. -/
theorem sum_burgessAffineShiftSum_eq_sum_burgessShiftSum
    {q N H a B : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b) =
      ∑ i ∈ Finset.range H,
        burgessShiftSum B χ
          (((N + i + 1 : ℕ) : ZMod q) * ((a : ℕ) : ZMod q)⁻¹) := by
  rw [sum_Ioc_zero_eq_sum_range_succ]
  unfold burgessAffineShiftSum burgessShiftSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact (Fin.sum_univ_eq_sum_range
    (fun b : ℕ => χ
      (((N + i + 1 : ℕ) : ZMod q) * ((a : ℕ) : ZMod q)⁻¹ +
        ((b + 1 : ℕ) : ZMod q))) B).symm

/-- Pairs of a positive coprime multiplier `a ≤ A` and an interval index
`n < H`. -/
def burgessCoprimeMultiplierPairs (q A H : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ioc 0 A).filter fun a => Nat.Coprime a q).product (Finset.range H)

/-- The residue `(N+n+1)/a` produced by a Burgess multiplier pair. -/
def burgessMultiplierResidue (q N : ℕ) (an : ℕ × ℕ) : ZMod q :=
  ((N + an.2 + 1 : ℕ) : ZMod q) * ((an.1 : ℕ) : ZMod q)⁻¹

/-- Multiplicity with which a residue occurs in the Burgess multiplier map. -/
def burgessResidueMultiplicity (q N H A : ℕ) (x : ZMod q) : ℕ :=
  ((burgessCoprimeMultiplierPairs q A H).filter fun an =>
    burgessMultiplierResidue q N an = x).card

/-- The multiplier-pair set has the expected product cardinality. -/
theorem card_burgessCoprimeMultiplierPairs (q A H : ℕ) :
    (burgessCoprimeMultiplierPairs q A H).card =
      ((Finset.Ioc 0 A).filter fun a => Nat.Coprime a q).card * H := by
  simp [burgessCoprimeMultiplierPairs]

/-- The first moment of the residue multiplicity is exactly the number of
multiplier pairs. -/
theorem sum_burgessResidueMultiplicity (q N H A : ℕ) [NeZero q] :
    ∑ x : ZMod q, burgessResidueMultiplicity q N H A x =
      (burgessCoprimeMultiplierPairs q A H).card := by
  symm
  simpa only [burgessResidueMultiplicity] using
    (Finset.card_eq_sum_card_fiberwise
      (s := burgessCoprimeMultiplierPairs q A H)
      (t := (Finset.univ : Finset (ZMod q)))
      (f := burgessMultiplierResidue q N)
      (fun _ _ => Finset.mem_univ _))

/-- Exact weighted regrouping by the residue multiplicity. -/
theorem sum_burgessResidueMultiplicity_mul
    {q N H A : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℂ) * f x) =
      ∑ an ∈ burgessCoprimeMultiplierPairs q A H,
        f (burgessMultiplierResidue q N an) := by
  let s := burgessCoprimeMultiplierPairs q A H
  let g := burgessMultiplierResidue q N
  calc
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℂ) * f x) =
        ∑ x ∈ (Finset.univ : Finset (ZMod q)),
          ∑ an ∈ s with g an = x, f (g an) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (burgessResidueMultiplicity q N H A x : ℂ) * f x =
            ∑ _an ∈ s with g _an = x, f x := by
          simp [burgessResidueMultiplicity, s, g]
        _ = ∑ an ∈ s with g an = x, f (g an) := by
          apply Finset.sum_congr rfl
          intro an han
          rw [(Finset.mem_filter.mp han).2]
    _ = ∑ an ∈ s with g an ∈ (Finset.univ : Finset (ZMod q)),
          f (g an) :=
      Finset.sum_fiberwise_eq_sum_filter s Finset.univ g (fun an => f (g an))
    _ = ∑ an ∈ burgessCoprimeMultiplierPairs q A H,
          f (burgessMultiplierResidue q N an) := by
      simp [s, g]

/-- The complete affine Burgess average is the multiplicity-weighted sum of
the same shifted-character function controlled by `BurgessMoment`. -/
theorem sum_coprime_burgessAffineShiftSum_eq_multiplicity_sum
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∑ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
        ∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b) =
      ∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℂ) *
        burgessShiftSum B χ x := by
  calc
    (∑ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
        ∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b) =
        ∑ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
          ∑ i ∈ Finset.range H,
            burgessShiftSum B χ
              (((N + i + 1 : ℕ) : ZMod q) * ((a : ℕ) : ZMod q)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact sum_burgessAffineShiftSum_eq_sum_burgessShiftSum χ
    _ = ∑ an ∈ burgessCoprimeMultiplierPairs q A H,
          burgessShiftSum B χ (burgessMultiplierResidue q N an) := by
      unfold burgessCoprimeMultiplierPairs burgessMultiplierResidue
      exact (Finset.sum_product
        ((Finset.Ioc 0 A).filter fun a => Nat.Coprime a q)
        (Finset.range H)
        (fun an : ℕ × ℕ => burgessShiftSum B χ
          (((N + an.2 + 1 : ℕ) : ZMod q) *
            ((an.1 : ℕ) : ZMod q)⁻¹))).symm
    _ = ∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℂ) *
          burgessShiftSum B χ x :=
      (sum_burgessResidueMultiplicity_mul (N := N) (H := H) (A := A)
        (fun x => burgessShiftSum B χ x)).symm

/-- Ordered collisions of two multiplier pairs having the same residue. -/
def burgessResidueCollisionPairs (q N H A : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((burgessCoprimeMultiplierPairs q A H).product
    (burgessCoprimeMultiplierPairs q A H)).filter fun uv =>
      burgessMultiplierResidue q N uv.1 =
        burgessMultiplierResidue q N uv.2

/-- The second moment of the multiplicity is exactly the number of ordered
residue collisions.  This is the combinatorial quantity in the source's
`v_A` square-sum estimate. -/
theorem sum_sq_burgessResidueMultiplicity_eq_card_collisions
    (q N H A : ℕ) [NeZero q] :
    ∑ x : ZMod q, (burgessResidueMultiplicity q N H A x) ^ 2 =
      (burgessResidueCollisionPairs q N H A).card := by
  symm
  calc
    (burgessResidueCollisionPairs q N H A).card =
        ∑ x ∈ (Finset.univ : Finset (ZMod q)),
          ((burgessResidueCollisionPairs q N H A).filter fun uv =>
            burgessMultiplierResidue q N uv.1 = x).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro uv huv
      exact Finset.mem_univ _
    _ = ∑ x : ZMod q,
          (burgessResidueMultiplicity q N H A x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [pow_two]
      unfold burgessResidueMultiplicity
      rw [← Finset.card_product
        ((burgessCoprimeMultiplierPairs q A H).filter fun an =>
          burgessMultiplierResidue q N an = x)
        ((burgessCoprimeMultiplierPairs q A H).filter fun an =>
          burgessMultiplierResidue q N an = x)]
      congr 1
      ext uv
      simp [burgessResidueCollisionPairs]
      constructor
      · rintro ⟨⟨⟨hu, hv⟩, huv⟩, hux⟩
        exact ⟨⟨hu, hux⟩, hv, huv ▸ hux⟩
      · rintro ⟨⟨hu, hux⟩, hv, hvx⟩
        exact ⟨⟨⟨hu, hv⟩, hux.trans hvx.symm⟩, hux⟩

/-- Equality of two multiplier residues is equivalent to the usual
cross-multiplied congruence once both multipliers are units modulo `q`. -/
theorem burgessMultiplierResidue_eq_iff_cross_mul
    {q N a c n m : ℕ} (ha : Nat.Coprime a q) (hc : Nat.Coprime c q) :
    burgessMultiplierResidue q N (a, n) =
        burgessMultiplierResidue q N (c, m) ↔
      (c : ZMod q) * ((N + n + 1 : ℕ) : ZMod q) =
        (a : ZMod q) * ((N + m + 1 : ℕ) : ZMod q) := by
  have haUnit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  have hcUnit : IsUnit (c : ZMod q) :=
    (ZMod.isUnit_iff_coprime c q).2 hc
  have haInv : (a : ZMod q) * (a : ZMod q)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ haUnit
  have hcInv : (c : ZMod q) * (c : ZMod q)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hcUnit
  have hcancelA (z : ZMod q) :
      (a : ZMod q) * (z * (a : ZMod q)⁻¹) = z := by
    calc
      _ = ((a : ZMod q) * (a : ZMod q)⁻¹) * z := by ac_rfl
      _ = z := by rw [haInv, one_mul]
  have hcancelC (z : ZMod q) :
      (z * (c : ZMod q)⁻¹) * (c : ZMod q) = z := by
    calc
      _ = z * ((c : ZMod q) * (c : ZMod q)⁻¹) := by ac_rfl
      _ = z := by rw [hcInv, mul_one]
  have hcancelCOuter (z : ZMod q) :
      (c : ZMod q) * z * (c : ZMod q)⁻¹ = z := by
    calc
      _ = z * ((c : ZMod q) * (c : ZMod q)⁻¹) := by ac_rfl
      _ = z := by rw [hcInv, mul_one]
  have hcancelAOuter (z : ZMod q) :
      (a : ZMod q)⁻¹ * ((a : ZMod q) * z) = z := by
    calc
      _ = ((a : ZMod q) * (a : ZMod q)⁻¹) * z := by ac_rfl
      _ = z := by rw [haInv, one_mul]
  unfold burgessMultiplierResidue
  constructor
  · intro h
    have hmul := congrArg
      (fun z : ZMod q => (a : ZMod q) * z * (c : ZMod q)) h
    calc
      (c : ZMod q) * ((N + n + 1 : ℕ) : ZMod q) =
          (a : ZMod q) *
            (((N + n + 1 : ℕ) : ZMod q) * (a : ZMod q)⁻¹) *
              (c : ZMod q) := by
        rw [hcancelA]
        ring
      _ = (a : ZMod q) *
            (((N + m + 1 : ℕ) : ZMod q) * (c : ZMod q)⁻¹) *
              (c : ZMod q) := hmul
      _ = (a : ZMod q) * ((N + m + 1 : ℕ) : ZMod q) := by
        rw [mul_assoc, hcancelC]
  · intro h
    have hmul := congrArg
      (fun z : ZMod q => (a : ZMod q)⁻¹ * z * (c : ZMod q)⁻¹) h
    calc
      ((N + n + 1 : ℕ) : ZMod q) * (a : ZMod q)⁻¹ =
          (a : ZMod q)⁻¹ *
            ((c : ZMod q) * ((N + n + 1 : ℕ) : ZMod q)) *
              (c : ZMod q)⁻¹ := by
        symm
        calc
          _ = (a : ZMod q)⁻¹ *
              (((c : ZMod q) * ((N + n + 1 : ℕ) : ZMod q)) *
                (c : ZMod q)⁻¹) := by rw [mul_assoc]
          _ = (a : ZMod q)⁻¹ * ((N + n + 1 : ℕ) : ZMod q) := by
            rw [hcancelCOuter]
          _ = _ := by ring
      _ = (a : ZMod q)⁻¹ *
            ((a : ZMod q) * ((N + m + 1 : ℕ) : ZMod q)) *
              (c : ZMod q)⁻¹ := hmul
      _ = ((N + m + 1 : ℕ) : ZMod q) * (c : ZMod q)⁻¹ := by
        rw [hcancelAOuter]

/-- Integer determinant whose divisibility by `q` expresses a fixed-
multiplier residue collision. -/
def burgessCollisionDeterminant (N a c n m : ℕ) : ℤ :=
  (a : ℤ) * (N + m + 1 : ℕ) - (c : ℤ) * (N + n + 1 : ℕ)

/-- The cross-multiplied congruence is exactly divisibility of the integer
collision determinant by the modulus. -/
theorem burgess_cross_mul_eq_iff_dvd_collisionDeterminant
    (q N a c n m : ℕ) :
    (c : ZMod q) * ((N + n + 1 : ℕ) : ZMod q) =
        (a : ZMod q) * ((N + m + 1 : ℕ) : ZMod q) ↔
      (q : ℤ) ∣ burgessCollisionDeterminant N a c n m := by
  unfold burgessCollisionDeterminant
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub
    ((c : ℤ) * (N + n + 1 : ℕ))
    ((a : ℤ) * (N + m + 1 : ℕ)) q]
  norm_cast

/-- Collision fiber for two fixed multipliers. -/
def burgessMultiplierCollisionFiber (q N H a c : ℕ) :
    Finset (ℕ × ℕ) :=
  ((Finset.range H).product (Finset.range H)).filter fun nm =>
    burgessMultiplierResidue q N (a, nm.1) =
      burgessMultiplierResidue q N (c, nm.2)

/-- Membership in a fixed-multiplier collision fiber, expressed using the
source's cross-multiplied congruence. -/
theorem mem_burgessMultiplierCollisionFiber_iff
    {q N H a c n m : ℕ} (ha : Nat.Coprime a q) (hc : Nat.Coprime c q) :
    (n, m) ∈ burgessMultiplierCollisionFiber q N H a c ↔
      n < H ∧ m < H ∧
        (c : ZMod q) * ((N + n + 1 : ℕ) : ZMod q) =
          (a : ZMod q) * ((N + m + 1 : ℕ) : ZMod q) := by
  simp [burgessMultiplierCollisionFiber, and_assoc,
    burgessMultiplierResidue_eq_iff_cross_mul ha hc]

/-- Integer-divisibility form of fixed-multiplier collision-fiber
membership. -/
theorem mem_burgessMultiplierCollisionFiber_iff_dvd
    {q N H a c n m : ℕ} (ha : Nat.Coprime a q) (hc : Nat.Coprime c q) :
    (n, m) ∈ burgessMultiplierCollisionFiber q N H a c ↔
      n < H ∧ m < H ∧
        (q : ℤ) ∣ burgessCollisionDeterminant N a c n m := by
  rw [mem_burgessMultiplierCollisionFiber_iff ha hc,
    burgess_cross_mul_eq_iff_dvd_collisionDeterminant]

/-- Subtracting two collision determinants cancels the interval base point. -/
theorem burgessCollisionDeterminant_sub
    (N a c n₁ m₁ n₂ m₂ : ℕ) :
    burgessCollisionDeterminant N a c n₁ m₁ -
        burgessCollisionDeterminant N a c n₂ m₂ =
      (a : ℤ) * ((m₁ : ℤ) - m₂) -
        (c : ℤ) * ((n₁ : ℤ) - n₂) := by
  simp only [burgessCollisionDeterminant]
  push_cast
  ring

/-- Two collisions force the modulus to divide their base-point-free linear
difference. -/
theorem dvd_burgessCollisionDifference
    {q N a c n₁ m₁ n₂ m₂ : ℕ}
    (h₁ : (q : ℤ) ∣ burgessCollisionDeterminant N a c n₁ m₁)
    (h₂ : (q : ℤ) ∣ burgessCollisionDeterminant N a c n₂ m₂) :
    (q : ℤ) ∣ (a : ℤ) * ((m₁ : ℤ) - m₂) -
      (c : ℤ) * ((n₁ : ℤ) - n₂) := by
  rw [← burgessCollisionDeterminant_sub]
  exact dvd_sub h₁ h₂

/-- In the no-wrap range, the congruence between two collisions is an exact
integer linear equation. -/
theorem burgessCollisionDifference_eq_zero_of_abs_lt_modulus
    {q N a c n₁ m₁ n₂ m₂ : ℕ}
    (h₁ : (q : ℤ) ∣ burgessCollisionDeterminant N a c n₁ m₁)
    (h₂ : (q : ℤ) ∣ burgessCollisionDeterminant N a c n₂ m₂)
    (hsmall :
      |(a : ℤ) * ((m₁ : ℤ) - m₂) -
        (c : ℤ) * ((n₁ : ℤ) - n₂)| < (q : ℤ)) :
    (a : ℤ) * ((m₁ : ℤ) - m₂) =
      (c : ℤ) * ((n₁ : ℤ) - n₂) := by
  apply sub_eq_zero.mp
  exact Int.eq_zero_of_abs_lt_dvd
    (dvd_burgessCollisionDifference h₁ h₂) hsmall

/-- Uniform no-wrap estimate for the difference of two collision
determinants when both multipliers are at most `A` and both interval indices
are below `H`. -/
theorem abs_burgessCollisionDifference_lt_two_mul
    {A H a c n₁ m₁ n₂ m₂ : ℕ}
    (ha0 : 0 < a) (hc0 : 0 < c) (haA : a ≤ A) (hcA : c ≤ A)
    (hn₁ : n₁ < H) (hm₁ : m₁ < H) (hn₂ : n₂ < H) (hm₂ : m₂ < H) :
    |(a : ℤ) * ((m₁ : ℤ) - m₂) -
        (c : ℤ) * ((n₁ : ℤ) - n₂)| < (2 * A * H : ℕ) := by
  have hmNat : Int.natAbs ((m₁ : ℤ) - m₂) < H :=
    Int.natAbs_coe_sub_coe_lt_of_lt hm₁ hm₂
  have hnNat : Int.natAbs ((n₁ : ℤ) - n₂) < H :=
    Int.natAbs_coe_sub_coe_lt_of_lt hn₁ hn₂
  have hmCast : ((Int.natAbs ((m₁ : ℤ) - m₂) : ℕ) : ℤ) < H := by
    exact_mod_cast hmNat
  have hnCast : ((Int.natAbs ((n₁ : ℤ) - n₂) : ℕ) : ℤ) < H := by
    exact_mod_cast hnNat
  have hm : |(m₁ : ℤ) - m₂| < (H : ℤ) := by
    simpa only [Int.natCast_natAbs] using hmCast
  have hn : |(n₁ : ℤ) - n₂| < (H : ℤ) := by
    simpa only [Int.natCast_natAbs] using hnCast
  have haInt : (a : ℤ) ≤ A := by exact_mod_cast haA
  have hcInt : (c : ℤ) ≤ A := by exact_mod_cast hcA
  have hma : |(a : ℤ) * ((m₁ : ℤ) - m₂)| < (A : ℤ) * H := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg a)]
    exact (mul_lt_mul_of_pos_left hm (by exact_mod_cast ha0)).trans_le
      (mul_le_mul_of_nonneg_right haInt (Int.natCast_nonneg H))
  have hnc : |(c : ℤ) * ((n₁ : ℤ) - n₂)| < (A : ℤ) * H := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg c)]
    exact (mul_lt_mul_of_pos_left hn (by exact_mod_cast hc0)).trans_le
      (mul_le_mul_of_nonneg_right hcInt (Int.natCast_nonneg H))
  calc
    |(a : ℤ) * ((m₁ : ℤ) - m₂) -
        (c : ℤ) * ((n₁ : ℤ) - n₂)| ≤
        |(a : ℤ) * ((m₁ : ℤ) - m₂)| +
          |(c : ℤ) * ((n₁ : ℤ) - n₂)| := abs_sub _ _
    _ < (A : ℤ) * H + (A : ℤ) * H := add_lt_add hma hnc
    _ = (2 * A * H : ℕ) := by push_cast; ring

/-- Under the standard Burgess no-wrap condition `2*A*H ≤ q`, any two
members of one fixed-multiplier collision fiber satisfy an exact integer
linear equation after subtraction. -/
theorem burgessCollisionFiber_sub_eq_of_two_mul_le_modulus
    {q N H A a c n₁ m₁ n₂ m₂ : ℕ}
    (ha : Nat.Coprime a q) (hc : Nat.Coprime c q)
    (ha0 : 0 < a) (hc0 : 0 < c) (haA : a ≤ A) (hcA : c ≤ A)
    (hAHq : 2 * A * H ≤ q)
    (h₁ : (n₁, m₁) ∈ burgessMultiplierCollisionFiber q N H a c)
    (h₂ : (n₂, m₂) ∈ burgessMultiplierCollisionFiber q N H a c) :
    (a : ℤ) * ((m₁ : ℤ) - m₂) =
      (c : ℤ) * ((n₁ : ℤ) - n₂) := by
  have hmem₁ := (mem_burgessMultiplierCollisionFiber_iff_dvd ha hc).1 h₁
  have hmem₂ := (mem_burgessMultiplierCollisionFiber_iff_dvd ha hc).1 h₂
  apply burgessCollisionDifference_eq_zero_of_abs_lt_modulus hmem₁.2.2 hmem₂.2.2
  exact (abs_burgessCollisionDifference_lt_two_mul ha0 hc0 haA hcA
    hmem₁.1 hmem₁.2.1 hmem₂.1 hmem₂.2.1).trans_le (by exact_mod_cast hAHq)

/-- In an exact collision-difference equation, the reduced first multiplier
divides the distance between the two first interval indices. -/
theorem burgess_reduced_left_dvd_dist_of_sub_eq
    {a c n₁ m₁ n₂ m₂ : ℕ} (ha0 : 0 < a)
    (hEq : (a : ℤ) * ((m₁ : ℤ) - m₂) =
      (c : ℤ) * ((n₁ : ℤ) - n₂)) :
    a / Nat.gcd a c ∣ Nat.dist n₁ n₂ := by
  have habs := congrArg Int.natAbs hEq
  have hnat : a * Nat.dist m₁ m₂ = c * Nat.dist n₁ n₂ := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast,
      burgess_natAbs_int_sub_eq_dist] using habs
  have hgpos : 0 < Nat.gcd a c := Nat.gcd_pos_of_pos_left c ha0
  have hred :
      (a / Nat.gcd a c) * Nat.dist m₁ m₂ =
        (c / Nat.gcd a c) * Nat.dist n₁ n₂ := by
    apply Nat.mul_left_cancel hgpos
    calc
      Nat.gcd a c * ((a / Nat.gcd a c) * Nat.dist m₁ m₂) =
          a * Nat.dist m₁ m₂ := by
        rw [← Nat.mul_assoc, Nat.mul_comm (Nat.gcd a c),
          Nat.div_mul_cancel (Nat.gcd_dvd_left a c)]
      _ = c * Nat.dist n₁ n₂ := hnat
      _ = Nat.gcd a c *
          ((c / Nat.gcd a c) * Nat.dist n₁ n₂) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (Nat.gcd a c),
          Nat.div_mul_cancel (Nat.gcd_dvd_right a c)]
  have hcop : Nat.Coprime (a / Nat.gcd a c) (c / Nat.gcd a c) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  apply (hcop.dvd_mul_right).mp
  refine ⟨Nat.dist m₁ m₂, ?_⟩
  calc
    Nat.dist n₁ n₂ * (c / Nat.gcd a c) =
        (c / Nat.gcd a c) * Nat.dist n₁ n₂ := by ring
    _ =
        (a / Nat.gcd a c) * Nat.dist m₁ m₂ := hred.symm

/-- Symmetric reduced-multiplier spacing for the second interval index. -/
theorem burgess_reduced_right_dvd_dist_of_sub_eq
    {a c n₁ m₁ n₂ m₂ : ℕ} (hc0 : 0 < c)
    (hEq : (a : ℤ) * ((m₁ : ℤ) - m₂) =
      (c : ℤ) * ((n₁ : ℤ) - n₂)) :
    c / Nat.gcd a c ∣ Nat.dist m₁ m₂ := by
  simpa only [Nat.gcd_comm] using
    (burgess_reduced_left_dvd_dist_of_sub_eq
      (a := c) (c := a) (n₁ := m₁) (m₁ := n₁)
      (n₂ := m₂) (m₂ := n₂) hc0 hEq.symm)

/-- The two coordinate spacings forced on any pair of elements of one
collision fiber in the standard no-wrap range. -/
theorem burgessCollisionFiber_reduced_dvd_dists
    {q N H A a c n₁ m₁ n₂ m₂ : ℕ}
    (ha : Nat.Coprime a q) (hc : Nat.Coprime c q)
    (ha0 : 0 < a) (hc0 : 0 < c) (haA : a ≤ A) (hcA : c ≤ A)
    (hAHq : 2 * A * H ≤ q)
    (h₁ : (n₁, m₁) ∈ burgessMultiplierCollisionFiber q N H a c)
    (h₂ : (n₂, m₂) ∈ burgessMultiplierCollisionFiber q N H a c) :
    a / Nat.gcd a c ∣ Nat.dist n₁ n₂ ∧
      c / Nat.gcd a c ∣ Nat.dist m₁ m₂ := by
  have hEq := burgessCollisionFiber_sub_eq_of_two_mul_le_modulus
    ha hc ha0 hc0 haA hcA hAHq h₁ h₂
  exact ⟨burgess_reduced_left_dvd_dist_of_sub_eq ha0 hEq,
    burgess_reduced_right_dvd_dist_of_sub_eq hc0 hEq⟩

/-- A quotient block contains at most one member of a fixed congruence class
modulo its block length. -/
theorem eq_of_div_eq_div_of_dvd_dist
    {d n₁ n₂ : ℕ} (hdiv : d ∣ Nat.dist n₁ n₂)
    (hquot : n₁ / d = n₂ / d) : n₁ = n₂ := by
  have hmod : n₁ ≡ n₂ [MOD d] := by
    rw [Nat.modEq_iff_dvd, ← Int.dvd_natAbs,
      Int.natCast_dvd_natCast]
    simpa only [burgess_natAbs_int_sub_eq_dist, Nat.dist_comm] using hdiv
  change n₁ % d = n₂ % d at hmod
  calc
    n₁ = n₁ % d + d * (n₁ / d) := (Nat.mod_add_div n₁ d).symm
    _ = n₂ % d + d * (n₂ / d) := by rw [hmod, hquot]
    _ = n₂ := Nat.mod_add_div n₂ d

/-- Fixed-fiber count using the spacing of the first interval coordinate. -/
theorem card_burgessMultiplierCollisionFiber_le_left
    {q N H A a c : ℕ}
    (ha : Nat.Coprime a q) (hc : Nat.Coprime c q)
    (ha0 : 0 < a) (hc0 : 0 < c) (haA : a ≤ A) (hcA : c ≤ A)
    (hAHq : 2 * A * H ≤ q) :
    (burgessMultiplierCollisionFiber q N H a c).card ≤
      H / (a / Nat.gcd a c) + 1 := by
  let d := a / Nat.gcd a c
  have hcard := Finset.card_le_card_of_injOn
    (s := burgessMultiplierCollisionFiber q N H a c)
    (t := Finset.range (H / d + 1))
    (fun nm : ℕ × ℕ => nm.1 / d)
    (by
      intro nm hnm
      have hn : nm.1 < H := by
        have h := (mem_burgessMultiplierCollisionFiber_iff ha hc).1 hnm
        exact h.1
      simpa using
        (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hn))))
    (by
      intro u hu v hv huv
      have hspaced := burgessCollisionFiber_reduced_dvd_dists
        ha hc ha0 hc0 haA hcA hAHq hu hv
      have hun : u.1 = v.1 :=
        eq_of_div_eq_div_of_dvd_dist hspaced.1 huv
      have hlinear := burgessCollisionFiber_sub_eq_of_two_mul_le_modulus
        ha hc ha0 hc0 haA hcA hAHq hu hv
      have haz : (a : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt ha0)
      have hmzero : (a : ℤ) * ((u.2 : ℤ) - v.2) = 0 := by
        simpa only [hun, sub_self, mul_zero] using hlinear
      have hmInt : (u.2 : ℤ) = v.2 :=
        sub_eq_zero.mp ((mul_eq_zero.mp hmzero).resolve_left haz)
      have hum : u.2 = v.2 := by exact_mod_cast hmInt
      exact Prod.ext hun hum)
  simpa only [Finset.card_range] using hcard

/-- Symmetric fixed-fiber count using the spacing of the second interval
coordinate. -/
theorem card_burgessMultiplierCollisionFiber_le_right
    {q N H A a c : ℕ}
    (ha : Nat.Coprime a q) (hc : Nat.Coprime c q)
    (ha0 : 0 < a) (hc0 : 0 < c) (haA : a ≤ A) (hcA : c ≤ A)
    (hAHq : 2 * A * H ≤ q) :
    (burgessMultiplierCollisionFiber q N H a c).card ≤
      H / (c / Nat.gcd a c) + 1 := by
  let d := c / Nat.gcd a c
  have hcard := Finset.card_le_card_of_injOn
    (s := burgessMultiplierCollisionFiber q N H a c)
    (t := Finset.range (H / d + 1))
    (fun nm : ℕ × ℕ => nm.2 / d)
    (by
      intro nm hnm
      have hm : nm.2 < H := by
        have h := (mem_burgessMultiplierCollisionFiber_iff ha hc).1 hnm
        exact h.2.1
      simpa using
        (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt hm))))
    (by
      intro u hu v hv huv
      have hspaced := burgessCollisionFiber_reduced_dvd_dists
        ha hc ha0 hc0 haA hcA hAHq hu hv
      have hum : u.2 = v.2 :=
        eq_of_div_eq_div_of_dvd_dist hspaced.2 huv
      have hlinear := burgessCollisionFiber_sub_eq_of_two_mul_le_modulus
        ha hc ha0 hc0 haA hcA hAHq hu hv
      have hcz : (c : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hc0)
      have hnzero : (c : ℤ) * ((u.1 : ℤ) - v.1) = 0 := by
        simpa only [hum, sub_self, mul_zero] using hlinear.symm
      have hnInt : (u.1 : ℤ) = v.1 :=
        sub_eq_zero.mp ((mul_eq_zero.mp hnzero).resolve_left hcz)
      have hun : u.1 = v.1 := by exact_mod_cast hnInt
      exact Prod.ext hun hum)
  simpa only [Finset.card_range] using hcard

/-- Source-shaped fixed-fiber collision bound, with the larger reduced
multiplier supplying the spacing. -/
theorem card_burgessMultiplierCollisionFiber_le_max
    {q N H A a c : ℕ}
    (ha : Nat.Coprime a q) (hc : Nat.Coprime c q)
    (ha0 : 0 < a) (hc0 : 0 < c) (haA : a ≤ A) (hcA : c ≤ A)
    (hAHq : 2 * A * H ≤ q) :
    (burgessMultiplierCollisionFiber q N H a c).card ≤
      H / (Nat.max a c / Nat.gcd a c) + 1 := by
  rcases le_total a c with hac | hca
  · simpa only [Nat.max_eq_right hac] using
      card_burgessMultiplierCollisionFiber_le_right
        ha hc ha0 hc0 haA hcA hAHq
  · simpa only [Nat.max_eq_left hca] using
      card_burgessMultiplierCollisionFiber_le_left
        ha hc ha0 hc0 haA hcA hAHq

/-- The part of the global collision family with a prescribed ordered pair
of multipliers. -/
def burgessGlobalMultiplierCollisionFiber (q N H A : ℕ)
    (ac : ℕ × ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (burgessResidueCollisionPairs q N H A).filter fun uv =>
    (uv.1.1, uv.2.1) = ac

/-- The global collision count is exactly the sum of its multiplier-pair
fibers. -/
theorem card_burgessResidueCollisionPairs_eq_sum_globalFibers
    (q N H A : ℕ) :
    (burgessResidueCollisionPairs q N H A).card =
      ∑ ac ∈
        (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).product
          ((Finset.Ioc 0 A).filter (fun c => Nat.Coprime c q))),
        (burgessGlobalMultiplierCollisionFiber q N H A ac).card := by
  simpa only [burgessGlobalMultiplierCollisionFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := burgessResidueCollisionPairs q N H A)
      (t := ((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).product
        ((Finset.Ioc 0 A).filter (fun c => Nat.Coprime c q)))
      (f := fun uv => (uv.1.1, uv.2.1))
      (by
        intro uv huv
        have hpairs := (Finset.mem_filter.mp huv).1
        have hleft := (Finset.mem_product.mp hpairs).1
        have hright := (Finset.mem_product.mp hpairs).2
        exact Finset.mem_product.mpr
          ⟨(Finset.mem_product.mp hleft).1,
            (Finset.mem_product.mp hright).1⟩))

/-- Forgetting the already fixed multipliers injects a global multiplier
fiber into the corresponding interval-index collision fiber. -/
theorem card_burgessGlobalMultiplierCollisionFiber_le_local
    (q N H A a c : ℕ) :
    (burgessGlobalMultiplierCollisionFiber q N H A (a, c)).card ≤
      (burgessMultiplierCollisionFiber q N H a c).card := by
  apply Finset.card_le_card_of_injOn
    (fun uv : (ℕ × ℕ) × (ℕ × ℕ) => (uv.1.2, uv.2.2))
  · intro uv huv
    have hglobal := (Finset.mem_filter.mp huv)
    have hac : (uv.1.1, uv.2.1) = (a, c) := hglobal.2
    have haeq : uv.1.1 = a := congrArg Prod.fst hac
    have hceq : uv.2.1 = c := congrArg Prod.snd hac
    have hcollision := (Finset.mem_filter.mp hglobal.1).2
    have hpairs := (Finset.mem_filter.mp hglobal.1).1
    have hn := (Finset.mem_product.mp
      (Finset.mem_product.mp hpairs).1).2
    have hm := (Finset.mem_product.mp
      (Finset.mem_product.mp hpairs).2).2
    have hleftPair : uv.1 = (a, uv.1.2) := Prod.ext haeq rfl
    have hrightPair : uv.2 = (c, uv.2.2) := Prod.ext hceq rfl
    rw [hleftPair, hrightPair] at hcollision
    change (uv.1.2, uv.2.2) ∈
      ((Finset.range H).product (Finset.range H)).filter (fun nm =>
        burgessMultiplierResidue q N (a, nm.1) =
          burgessMultiplierResidue q N (c, nm.2))
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hn, hm⟩, hcollision⟩
  · intro u hu v hv huv
    have huac := (Finset.mem_filter.mp hu).2
    have hvac := (Finset.mem_filter.mp hv).2
    have huLeft : u.1.1 = a := congrArg Prod.fst huac
    have huRight : u.2.1 = c := congrArg Prod.snd huac
    have hvLeft : v.1.1 = a := congrArg Prod.fst hvac
    have hvRight : v.2.1 = c := congrArg Prod.snd hvac
    injection huv with hn hm
    apply Prod.ext
    · exact Prod.ext (huLeft.trans hvLeft.symm) hn
    · exact Prod.ext (huRight.trans hvRight.symm) hm

/-- The source-shaped finite upper bound for the complete residue-collision
count, before estimating the remaining elementary gcd sum. -/
theorem card_burgessResidueCollisionPairs_le_sum_max_gcd
    {q N H A : ℕ} (hAHq : 2 * A * H ≤ q) :
    (burgessResidueCollisionPairs q N H A).card ≤
      ∑ ac ∈
        (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).product
          ((Finset.Ioc 0 A).filter (fun c => Nat.Coprime c q))),
        (H / (Nat.max ac.1 ac.2 / Nat.gcd ac.1 ac.2) + 1) := by
  rw [card_burgessResidueCollisionPairs_eq_sum_globalFibers]
  apply Finset.sum_le_sum
  intro ac hac
  have haMem := (Finset.mem_product.mp hac).1
  have hcMem := (Finset.mem_product.mp hac).2
  have haData := Finset.mem_filter.mp haMem
  have hcData := Finset.mem_filter.mp hcMem
  have haRange := Finset.mem_Ioc.mp haData.1
  have hcRange := Finset.mem_Ioc.mp hcData.1
  exact (card_burgessGlobalMultiplierCollisionFiber_le_local
    q N H A ac.1 ac.2).trans
      (card_burgessMultiplierCollisionFiber_le_max
        haData.2 hcData.2 haRange.1 hcRange.1 haRange.2 hcRange.2 hAHq)

/-- For a fixed larger multiplier `c`, the sum of the natural collision
quotients is bounded by `H` times the divisor count of `c`. -/
theorem sum_Ioc_burgessGcdQuotient_le (c H : ℕ) (hc : 0 < c) :
    (∑ a ∈ Finset.Ioc 0 c, H / (c / Nat.gcd a c)) ≤
      H * c.divisors.card := by
  calc
    (∑ a ∈ Finset.Ioc 0 c, H / (c / Nat.gcd a c)) ≤
        ∑ a ∈ Finset.Ioc 0 c,
          ∑ d ∈ c.divisors, if d ∣ a then H / (c / d) else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      have hgMem : Nat.gcd a c ∈ c.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right a c, hc.ne'⟩
      have hsingle := Finset.single_le_sum
        (s := c.divisors)
        (f := fun d => if d ∣ a then H / (c / d) else 0)
        (fun d hd => by omega) hgMem
      simpa [Nat.gcd_dvd_left] using hsingle
    _ = ∑ d ∈ c.divisors,
          ∑ a ∈ Finset.Ioc 0 c, if d ∣ a then H / (c / d) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ c.divisors, (c / d) * (H / (c / d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (∑ a ∈ Finset.Ioc 0 c, if d ∣ a then H / (c / d) else 0) =
            ∑ a ∈ (Finset.Ioc 0 c).filter (fun a => d ∣ a), H / (c / d) := by
          rw [Finset.sum_filter]
        _ = ((Finset.Ioc 0 c).filter (fun a => d ∣ a)).card *
              (H / (c / d)) := by simp
        _ = (c / d) * (H / (c / d)) := by
          rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ _d ∈ c.divisors, H := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.mul_div_le H (c / d)
    _ = H * c.divisors.card := by simp [Nat.mul_comm]

/-- Double-counting divisor incidences below `A`: the summatory divisor
function is exactly the sum of the quotients `A / d`. -/
theorem sum_Ioc_card_divisors_eq_sum_div (A : ℕ) :
    (∑ c ∈ Finset.Ioc 0 A, c.divisors.card) =
      ∑ d ∈ Finset.Ioc 0 A, A / d := by
  calc
    (∑ c ∈ Finset.Ioc 0 A, c.divisors.card) =
        ∑ c ∈ Finset.Ioc 0 A,
          ∑ d ∈ Finset.Ioc 0 A, if d ∣ c then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcData := Finset.mem_Ioc.mp hc
      rw [← Finset.card_filter]
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
      constructor
      · intro hd
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 hcData.1,
          (Nat.le_of_dvd hcData.1 hd.1).trans hcData.2⟩,
          hd.1⟩
      · intro hd
        exact ⟨hd.2, hcData.1.ne'⟩
    _ = ∑ d ∈ Finset.Ioc 0 A,
          ∑ c ∈ Finset.Ioc 0 A, if d ∣ c then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Ioc 0 A, A / d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      exact Nat.Ioc_filter_dvd_card_eq_div A d

/-- The summatory divisor function below `A` is at most `A` times the
`A`-th harmonic number. -/
theorem sum_Ioc_card_divisors_cast_le_harmonic (A : ℕ) :
    (∑ c ∈ Finset.Ioc 0 A, (c.divisors.card : ℝ)) ≤
      (A : ℝ) * (((harmonic A : ℚ) : ℝ)) := by
  rw [show (∑ c ∈ Finset.Ioc 0 A, (c.divisors.card : ℝ)) =
      ((∑ c ∈ Finset.Ioc 0 A, c.divisors.card : ℕ) : ℝ) by norm_cast]
  rw [sum_Ioc_card_divisors_eq_sum_div]
  rw [show ((∑ d ∈ Finset.Ioc 0 A, A / d : ℕ) : ℝ) =
      ∑ d ∈ Finset.Ioc 0 A, ((A / d : ℕ) : ℝ) by norm_cast]
  calc
    (∑ d ∈ Finset.Ioc 0 A, ((A / d : ℕ) : ℝ)) ≤
        ∑ d ∈ Finset.Ioc 0 A, (A : ℝ) / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.cast_div_le
    _ = (A : ℝ) * ∑ d ∈ Finset.Ioc 0 A, (d : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [div_eq_mul_inv]
    _ = (A : ℝ) * (((harmonic A : ℚ) : ℝ)) := by
      have hsets : Finset.Ioc 0 A = Finset.Icc 1 A := by
        ext d
        simp
        omega
      rw [hsets]
      congr 1
      rw [harmonic_eq_sum_Icc]
      push_cast
      apply Finset.sum_congr rfl
      intro d hd
      simp

/-- The upper-triangular part of the multiplier gcd quotient sum. -/
def burgessOrientedGcdQuotientSum (A H : ℕ) : ℕ :=
  ∑ c ∈ Finset.Ioc 0 A,
    ∑ a ∈ Finset.Ioc 0 c, H / (c / Nat.gcd a c)

theorem burgessOrientedGcdQuotientSum_le (A H : ℕ) :
    burgessOrientedGcdQuotientSum A H ≤
      H * ∑ c ∈ Finset.Ioc 0 A, c.divisors.card := by
  unfold burgessOrientedGcdQuotientSum
  calc
    (∑ c ∈ Finset.Ioc 0 A,
        ∑ a ∈ Finset.Ioc 0 c, H / (c / Nat.gcd a c)) ≤
        ∑ c ∈ Finset.Ioc 0 A, H * c.divisors.card := by
      apply Finset.sum_le_sum
      intro c hc
      exact sum_Ioc_burgessGcdQuotient_le c H (Finset.mem_Ioc.mp hc).1
    _ = H * ∑ c ∈ Finset.Ioc 0 A, c.divisors.card := by
      rw [Finset.mul_sum]

/-- Symmetry bounds the complete square of multiplier gcd quotients by twice
its upper-triangular part. -/
theorem sum_burgessGcdQuotient_le (A H : ℕ) :
    (∑ ac ∈ (Finset.Ioc 0 A).product (Finset.Ioc 0 A),
        H / (Nat.max ac.1 ac.2 / Nat.gcd ac.1 ac.2)) ≤
      2 * burgessOrientedGcdQuotientSum A H := by
  let S := Finset.Ioc 0 A
  have hfirst :
      (∑ ac ∈ S.product S,
          if ac.1 ≤ ac.2 then H / (ac.2 / Nat.gcd ac.1 ac.2) else 0) =
        burgessOrientedGcdQuotientSum A H := by
    calc
      (∑ ac ∈ S.product S,
          if ac.1 ≤ ac.2 then H / (ac.2 / Nat.gcd ac.1 ac.2) else 0) =
          ∑ c ∈ S, ∑ a ∈ S,
            if a ≤ c then H / (c / Nat.gcd a c) else 0 :=
        Finset.sum_product_right S S _
      _ = burgessOrientedGcdQuotientSum A H := by
        unfold burgessOrientedGcdQuotientSum
        apply Finset.sum_congr rfl
        intro c hc
        rw [← Finset.sum_filter]
        have hfilter : S.filter (fun a => a ≤ c) = Finset.Ioc 0 c := by
          ext a
          simp only [S, Finset.mem_filter, Finset.mem_Ioc]
          have hcA := (Finset.mem_Ioc.mp hc).2
          omega
        rw [hfilter]
  have hsecond :
      (∑ ac ∈ S.product S,
          if ac.2 ≤ ac.1 then H / (ac.1 / Nat.gcd ac.2 ac.1) else 0) =
        burgessOrientedGcdQuotientSum A H := by
    calc
      (∑ ac ∈ S.product S,
          if ac.2 ≤ ac.1 then H / (ac.1 / Nat.gcd ac.2 ac.1) else 0) =
          ∑ a ∈ S, ∑ c ∈ S,
            if c ≤ a then H / (a / Nat.gcd c a) else 0 :=
        Finset.sum_product S S _
      _ = burgessOrientedGcdQuotientSum A H := by
        unfold burgessOrientedGcdQuotientSum
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.sum_filter]
        have hfilter : S.filter (fun c => c ≤ a) = Finset.Ioc 0 a := by
          ext c
          simp only [S, Finset.mem_filter, Finset.mem_Ioc]
          have haA := (Finset.mem_Ioc.mp ha).2
          omega
        rw [hfilter]
  calc
    (∑ ac ∈ S.product S,
        H / (Nat.max ac.1 ac.2 / Nat.gcd ac.1 ac.2)) ≤
        ∑ ac ∈ S.product S,
          ((if ac.1 ≤ ac.2 then
              H / (ac.2 / Nat.gcd ac.1 ac.2) else 0) +
            (if ac.2 ≤ ac.1 then
              H / (ac.1 / Nat.gcd ac.2 ac.1) else 0)) := by
      apply Finset.sum_le_sum
      intro ac hac
      rcases le_total ac.1 ac.2 with hle | hle
      · simp only [if_pos hle]
        have hmax : ac.1.max ac.2 = ac.2 := max_eq_right hle
        rw [hmax]
        omega
      · simp only [if_pos hle]
        have hmax : ac.1.max ac.2 = ac.1 := max_eq_left hle
        rw [hmax]
        rw [Nat.gcd_comm ac.2 ac.1]
        omega
    _ = (∑ ac ∈ S.product S,
          if ac.1 ≤ ac.2 then H / (ac.2 / Nat.gcd ac.1 ac.2) else 0) +
        ∑ ac ∈ S.product S,
          if ac.2 ≤ ac.1 then H / (ac.1 / Nat.gcd ac.2 ac.1) else 0 := by
      rw [Finset.sum_add_distrib]
    _ = 2 * burgessOrientedGcdQuotientSum A H := by
      rw [hfirst, hsecond]
      omega

/-- The complete collision cardinality is bounded by a diagonal multiplier
term plus the elementary summatory divisor function. -/
theorem card_burgessResidueCollisionPairs_le_divisor_sum
    {q N H A : ℕ} (hAHq : 2 * A * H ≤ q) :
    (burgessResidueCollisionPairs q N H A).card ≤
      (burgessCoprimeMultiplierPairs q A 1).card ^ 2 +
        2 * H * ∑ c ∈ Finset.Ioc 0 A, c.divisors.card := by
  let P := (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)
  let T := Finset.Ioc 0 A
  have hbase := card_burgessResidueCollisionPairs_le_sum_max_gcd
    (q := q) (N := N) (H := H) (A := A) hAHq
  have hsubset : P.product P ⊆ T.product T := by
    intro ac hac
    have hp := Finset.mem_product.mp hac
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hp.1).1, (Finset.mem_filter.mp hp.2).1⟩
  have hquotient :
      (∑ ac ∈ P.product P,
          H / (Nat.max ac.1 ac.2 / Nat.gcd ac.1 ac.2)) ≤
        ∑ ac ∈ T.product T,
          H / (Nat.max ac.1 ac.2 / Nat.gcd ac.1 ac.2) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  have hpairCard : (P.product P).card = P.card ^ 2 := by simp [pow_two]
  calc
    (burgessResidueCollisionPairs q N H A).card ≤
        ∑ ac ∈ P.product P,
          (H / (Nat.max ac.1 ac.2 / Nat.gcd ac.1 ac.2) + 1) := by
      simpa only [P] using hbase
    _ = (∑ ac ∈ P.product P,
          H / (Nat.max ac.1 ac.2 / Nat.gcd ac.1 ac.2)) + P.card ^ 2 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hpairCard]
    _ ≤ (∑ ac ∈ T.product T,
          H / (Nat.max ac.1 ac.2 / Nat.gcd ac.1 ac.2)) + P.card ^ 2 := by
      omega
    _ ≤ 2 * burgessOrientedGcdQuotientSum A H + P.card ^ 2 := by
      have h := sum_burgessGcdQuotient_le A H
      simpa only [T] using Nat.add_le_add_right h (P.card ^ 2)
    _ ≤ 2 * (H * ∑ c ∈ Finset.Ioc 0 A, c.divisors.card) + P.card ^ 2 := by
      have h := burgessOrientedGcdQuotientSum_le A H
      omega
    _ = (burgessCoprimeMultiplierPairs q A 1).card ^ 2 +
          2 * H * ∑ c ∈ Finset.Ioc 0 A, c.divisors.card := by
      have hP : P.card = (burgessCoprimeMultiplierPairs q A 1).card := by
        simp [P, burgessCoprimeMultiplierPairs]
      rw [hP]
      ring

/-- Real source-facing form: the multiplier collision count costs only one
harmonic factor beyond `A*H`, in addition to the diagonal multiplier term. -/
theorem card_burgessResidueCollisionPairs_cast_le_harmonic
    {q N H A : ℕ} (hAHq : 2 * A * H ≤ q) :
    ((burgessResidueCollisionPairs q N H A).card : ℝ) ≤
      ((burgessCoprimeMultiplierPairs q A 1).card : ℝ) ^ 2 +
        2 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ)) := by
  have hnat := card_burgessResidueCollisionPairs_le_divisor_sum
    (q := q) (N := N) (H := H) (A := A) hAHq
  have hcast :
      ((burgessResidueCollisionPairs q N H A).card : ℝ) ≤
        ((burgessCoprimeMultiplierPairs q A 1).card : ℝ) ^ 2 +
          2 * (H : ℝ) *
            (∑ c ∈ Finset.Ioc 0 A, (c.divisors.card : ℝ)) := by
    exact_mod_cast hnat
  calc
    ((burgessResidueCollisionPairs q N H A).card : ℝ) ≤
        ((burgessCoprimeMultiplierPairs q A 1).card : ℝ) ^ 2 +
          2 * (H : ℝ) *
            (∑ c ∈ Finset.Ioc 0 A, (c.divisors.card : ℝ)) := hcast
    _ ≤ ((burgessCoprimeMultiplierPairs q A 1).card : ℝ) ^ 2 +
          2 * (H : ℝ) *
            ((A : ℝ) * (((harmonic A : ℚ) : ℝ))) := by
      gcongr
      exact sum_Ioc_card_divisors_cast_le_harmonic A
    _ = ((burgessCoprimeMultiplierPairs q A 1).card : ℝ) ^ 2 +
          2 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ)) := by ring

/-- Real-valued weighted regrouping by the residue multiplicity. -/
theorem sum_burgessResidueMultiplicity_mul_real
    {q N H A : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) * f x) =
      ∑ an ∈ burgessCoprimeMultiplierPairs q A H,
        f (burgessMultiplierResidue q N an) := by
  let s := burgessCoprimeMultiplierPairs q A H
  let g := burgessMultiplierResidue q N
  calc
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) * f x) =
        ∑ x ∈ (Finset.univ : Finset (ZMod q)),
          ∑ an ∈ s with g an = x, f (g an) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (burgessResidueMultiplicity q N H A x : ℝ) * f x =
            ∑ _an ∈ s with g _an = x, f x := by
          simp [burgessResidueMultiplicity, s, g]
        _ = ∑ an ∈ s with g an = x, f (g an) := by
          apply Finset.sum_congr rfl
          intro an han
          rw [(Finset.mem_filter.mp han).2]
    _ = ∑ an ∈ s with g an ∈ (Finset.univ : Finset (ZMod q)),
          f (g an) :=
      Finset.sum_fiberwise_eq_sum_filter s Finset.univ g (fun an => f (g an))
    _ = ∑ an ∈ burgessCoprimeMultiplierPairs q A H,
          f (burgessMultiplierResidue q N an) := by
      simp [s, g]

/-- Summing the norms of the affine `b`-averages over coprime multipliers is
bounded by the source multiplicity-weighted shifted-character sum. -/
theorem sum_norm_coprime_burgessAffineShiftSum_le_multiplicity
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∑ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
        ‖∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b‖) ≤
      ∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖ := by
  calc
    (∑ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
        ‖∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b‖) ≤
        ∑ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
          ∑ i ∈ Finset.range H,
            ‖burgessShiftSum B χ
              (((N + i + 1 : ℕ) : ZMod q) * ((a : ℕ) : ZMod q)⁻¹)‖ := by
      apply Finset.sum_le_sum
      intro a ha
      rw [sum_burgessAffineShiftSum_eq_sum_burgessShiftSum χ]
      exact norm_sum_le _ _
    _ = ∑ an ∈ burgessCoprimeMultiplierPairs q A H,
          ‖burgessShiftSum B χ (burgessMultiplierResidue q N an)‖ := by
      unfold burgessCoprimeMultiplierPairs burgessMultiplierResidue
      exact (Finset.sum_product
        ((Finset.Ioc 0 A).filter fun a => Nat.Coprime a q)
        (Finset.range H)
        (fun an : ℕ × ℕ =>
          ‖burgessShiftSum B χ
            (((N + an.2 + 1 : ℕ) : ZMod q) *
              ((an.1 : ℕ) : ZMod q)⁻¹)‖)).symm
    _ = ∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
          ‖burgessShiftSum B χ x‖ :=
      (sum_burgessResidueMultiplicity_mul_real
        (N := N) (H := H) (A := A)
        (fun x => ‖burgessShiftSum B χ x‖)).symm

/-- An arbitrary majorant for the two shorter boundary intervals controls the
difference between an interval and its additive translate. -/
theorem norm_burgessIntervalCharacterSum_sub_shift_le_of_majorants
    {q N H K : ℕ} (χ : DirichletCharacter ℂ q) (hK : K ≤ H)
    {E : ℝ}
    (hleft : ‖burgessIntervalCharacterSum χ N K‖ ≤ E)
    (hright : ‖burgessIntervalCharacterSum χ (N + H) K‖ ≤ E) :
    ‖burgessIntervalCharacterSum χ N H -
        burgessIntervalCharacterSum χ (N + K) H‖ ≤ 2 * E := by
  rw [burgessIntervalCharacterSum_sub_shift χ hK]
  exact (norm_sub_le _ _).trans (by linarith)

/-- For one coprime multiplier, averaging the shifted interval over `b`
costs precisely the sum of the two shorter-interval majorants. -/
theorem fixedMultiplier_burgessAffineAverage_le
    {q N H a B : ℕ} (χ : DirichletCharacter ℂ q)
    (ha : Nat.Coprime a q) (haB : a * B ≤ H)
    (E : ℕ → ℝ)
    (hleft : ∀ b ∈ Finset.Ioc 0 B,
      ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤ E (a * b))
    (hright : ∀ b ∈ Finset.Ioc 0 B,
      ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤ E (a * b)) :
    (B : ℝ) * ‖burgessIntervalCharacterSum χ N H‖ ≤
      ‖∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b‖ +
        2 * ∑ b ∈ Finset.Ioc 0 B, E (a * b) := by
  let S := burgessIntervalCharacterSum χ N H
  let X := χ (a : ZMod q) *
    ∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b
  have hab : ∀ b ∈ Finset.Ioc 0 B, a * b ≤ H := by
    intro b hb
    exact (Nat.mul_le_mul_left a (Finset.mem_Ioc.mp hb).2).trans haB
  have hterm : ∀ b ∈ Finset.Ioc 0 B,
      ‖S - χ (a : ZMod q) * burgessAffineShiftSum χ N H a b‖ ≤
        2 * E (a * b) := by
    intro b hb
    rw [mul_burgessAffineShiftSum χ ha]
    exact norm_burgessIntervalCharacterSum_sub_shift_le_of_majorants
      χ (hab b hb) (hleft b hb) (hright b hb)
  have hidentity :
      ((B : ℂ) * S - X) =
        ∑ b ∈ Finset.Ioc 0 B,
          (S - χ (a : ZMod q) * burgessAffineShiftSum χ N H a b) := by
    simp [S, X, Finset.sum_sub_distrib, Finset.mul_sum]
  have hdiff : ‖(B : ℂ) * S - X‖ ≤
      2 * ∑ b ∈ Finset.Ioc 0 B, E (a * b) := by
    rw [hidentity]
    calc
      ‖∑ b ∈ Finset.Ioc 0 B,
          (S - χ (a : ZMod q) * burgessAffineShiftSum χ N H a b)‖ ≤
          ∑ b ∈ Finset.Ioc 0 B,
            ‖S - χ (a : ZMod q) * burgessAffineShiftSum χ N H a b‖ :=
        norm_sum_le _ _
      _ ≤ ∑ b ∈ Finset.Ioc 0 B, 2 * E (a * b) := by
        exact Finset.sum_le_sum (fun b hb => hterm b hb)
      _ = 2 * ∑ b ∈ Finset.Ioc 0 B, E (a * b) := by
        rw [Finset.mul_sum]
  calc
    (B : ℝ) * ‖burgessIntervalCharacterSum χ N H‖ =
        ‖(B : ℂ) * S‖ := by simp [S]
    _ = ‖((B : ℂ) * S - X) + X‖ := by ring_nf
    _ ≤ ‖(B : ℂ) * S - X‖ + ‖X‖ := norm_add_le _ _
    _ ≤ 2 * ∑ b ∈ Finset.Ioc 0 B, E (a * b) + ‖X‖ :=
      add_le_add_left hdiff _
    _ = ‖∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b‖ +
          2 * ∑ b ∈ Finset.Ioc 0 B, E (a * b) := by
      rw [show ‖X‖ =
          ‖∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b‖ by
        simp [X, norm_dirichletCharacter_natCast_eq_one χ ha]]
      ring

/-- The exact pre-Hölder Burgess recursion inequality. It is equation (28)
of the pinned explicit source with the shorter-interval bound left as an
arbitrary function `E`. -/
theorem burgessAffineAverage_recursion_le
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hAB : A * B ≤ H) (E : ℕ → ℝ)
    (hleft : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤ E (a * b))
    (hright : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤ E (a * b)) :
    (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℝ) *
        (B : ℝ) * ‖burgessIntervalCharacterSum χ N H‖ ≤
      (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) +
        2 * ∑ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
          ∑ b ∈ Finset.Ioc 0 B, E (a * b) := by
  let P := (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)
  have hsum :
      ∑ a ∈ P, (B : ℝ) * ‖burgessIntervalCharacterSum χ N H‖ ≤
        ∑ a ∈ P,
          (‖∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b‖ +
            2 * ∑ b ∈ Finset.Ioc 0 B, E (a * b)) := by
    apply Finset.sum_le_sum
    intro a ha
    have ha' : a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q) := by
      simpa only [P] using ha
    have haData := Finset.mem_filter.mp ha'
    have haA := (Finset.mem_Ioc.mp haData.1).2
    exact fixedMultiplier_burgessAffineAverage_le χ haData.2
      ((Nat.mul_le_mul_right B haA).trans hAB) E
      (hleft a ha') (hright a ha')
  calc
    (P.card : ℝ) * (B : ℝ) * ‖burgessIntervalCharacterSum χ N H‖ =
        ∑ a ∈ P, (B : ℝ) * ‖burgessIntervalCharacterSum χ N H‖ := by
      simp
      ring
    _ ≤ ∑ a ∈ P,
          (‖∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b‖ +
            2 * ∑ b ∈ Finset.Ioc 0 B, E (a * b)) := hsum
    _ = (∑ a ∈ P,
          ‖∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b‖) +
        2 * ∑ a ∈ P, ∑ b ∈ Finset.Ioc 0 B, E (a * b) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
          ‖burgessShiftSum B χ x‖) +
        2 * ∑ a ∈ P, ∑ b ∈ Finset.Ioc 0 B, E (a * b) := by
      simpa only [P] using
        add_le_add_left
          (sum_norm_coprime_burgessAffineShiftSum_le_multiplicity
            (N := N) (H := H) (A := A) (B := B) χ)
          (2 * ∑ a ∈ P, ∑ b ∈ Finset.Ioc 0 B, E (a * b))

/-- Monotonicity of a shorter-interval majorant removes the multiplier from
the boundary sum, exactly as in the source proof. -/
theorem sum_coprime_burgessBoundaryMajorant_le
    {q A B : ℕ} (E : ℕ → ℝ) (hE : Monotone E) :
    (∑ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
        ∑ b ∈ Finset.Ioc 0 B, E (a * b)) ≤
      (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℝ) *
        ∑ b ∈ Finset.Ioc 0 B, E (A * b) := by
  calc
    (∑ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
        ∑ b ∈ Finset.Ioc 0 B, E (a * b)) ≤
        ∑ _a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
          ∑ b ∈ Finset.Ioc 0 B, E (A * b) := by
      apply Finset.sum_le_sum
      intro a ha
      have haA := (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).2
      apply Finset.sum_le_sum
      intro b hb
      exact hE (Nat.mul_le_mul_right b haA)
    _ = (((Finset.Ioc 0 A).filter
          (fun a => Nat.Coprime a q)).card : ℝ) *
        ∑ b ∈ Finset.Ioc 0 B, E (A * b) := by simp

/-- Source form of the pre-Hölder recurrence after replacing every multiplier
in the boundary term by its common upper bound `A`. -/
theorem burgessAffineAverage_recursion_monotone_le
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hAB : A * B ≤ H) (E : ℕ → ℝ) (hE : Monotone E)
    (hleft : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤ E (a * b))
    (hright : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤ E (a * b)) :
    (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℝ) *
        (B : ℝ) * ‖burgessIntervalCharacterSum χ N H‖ ≤
      (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) +
        2 * (((Finset.Ioc 0 A).filter
          (fun a => Nat.Coprime a q)).card : ℝ) *
          ∑ b ∈ Finset.Ioc 0 B, E (A * b) := by
  have hrec := burgessAffineAverage_recursion_le χ hAB E hleft hright
  have hbound := sum_coprime_burgessBoundaryMajorant_le
    (q := q) (A := A) (B := B) E hE
  simpa only [mul_assoc] using hrec.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2))
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
      ‖burgessShiftSum B χ x‖))

/-- A nonnegative power majorant on `(0,B]` is bounded by `B` copies of its
endpoint value. -/
theorem sum_Ioc_burgessPowerBoundary_le
    {A B : ℕ} {C Q α : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hα : 0 ≤ α) :
    (∑ b ∈ Finset.Ioc 0 B, C * (A * b : ℝ) ^ α * Q) ≤
      (B : ℝ) * C * (A * B : ℝ) ^ α * Q := by
  calc
    (∑ b ∈ Finset.Ioc 0 B, C * (A * b : ℝ) ^ α * Q) ≤
        ∑ _b ∈ Finset.Ioc 0 B, C * (A * B : ℝ) ^ α * Q := by
      apply Finset.sum_le_sum
      intro b hb
      have hbB := (Finset.mem_Ioc.mp hb).2
      have hbase : (A * b : ℝ) ≤ (A * B : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left A hbB
      gcongr
    _ = (B : ℝ) * C * (A * B : ℝ) ^ α * Q := by
      simp
      ring

/-- Pre-Hölder recursion with a concrete nonnegative power majorant for the
shorter intervals. -/
theorem burgessAffineAverage_recursion_rpow_le
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hAB : A * B ≤ H) {C Q α : ℝ}
    (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hα : 0 ≤ α)
    (hleft : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤
          C * (a * b : ℝ) ^ α * Q)
    (hright : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤
          C * (a * b : ℝ) ^ α * Q) :
    (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℝ) *
        (B : ℝ) * ‖burgessIntervalCharacterSum χ N H‖ ≤
      (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) +
        2 * (((Finset.Ioc 0 A).filter
          (fun a => Nat.Coprime a q)).card : ℝ) *
          (B : ℝ) * C * (A * B : ℝ) ^ α * Q := by
  let E : ℕ → ℝ := fun K => C * (K : ℝ) ^ α * Q
  have hE : Monotone E := by
    intro K L hKL
    dsimp [E]
    have hbase : (K : ℝ) ≤ (L : ℝ) := by exact_mod_cast hKL
    gcongr
  have hleftE : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤ E (a * b) := by
    simpa only [E, Nat.cast_mul] using hleft
  have hrightE : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤ E (a * b) := by
    simpa only [E, Nat.cast_mul] using hright
  have hrec := burgessAffineAverage_recursion_monotone_le
    (N := N) χ hAB E hE hleftE hrightE
  have hsum := sum_Ioc_burgessPowerBoundary_le
    (A := A) (B := B) hC hQ hα
  simp only [E, Nat.cast_mul] at hrec
  calc
    (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℝ) *
        (B : ℝ) * ‖burgessIntervalCharacterSum χ N H‖ ≤
      (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) +
        2 * (((Finset.Ioc 0 A).filter
          (fun a => Nat.Coprime a q)).card : ℝ) *
          ∑ b ∈ Finset.Ioc 0 B, C * (A * b : ℝ) ^ α * Q := hrec
    _ ≤ (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
          ‖burgessShiftSum B χ x‖) +
        2 * (((Finset.Ioc 0 A).filter
          (fun a => Nat.Coprime a q)).card : ℝ) *
          ((B : ℝ) * C * (A * B : ℝ) ^ α * Q) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hsum
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
            (Nat.cast_nonneg _))) _
    _ = (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
          ‖burgessShiftSum B χ x‖) +
        2 * (((Finset.Ioc 0 A).filter
          (fun a => Nat.Coprime a q)).card : ℝ) *
          (B : ℝ) * C * (A * B : ℝ) ^ α * Q := by ring

/-- Normalized power-majorant recursion. Positivity of `A` and `B` makes the
averaging denominator nonzero. -/
theorem norm_burgessIntervalCharacterSum_le_holderTerm_add_rpowBoundary
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hAB : A * B ≤ H)
    {C Q α : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hα : 0 ≤ α)
    (hleft : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤
          C * (a * b : ℝ) ^ α * Q)
    (hright : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤
          C * (a * b : ℝ) ^ α * Q) :
    ‖burgessIntervalCharacterSum χ N H‖ ≤
      (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) /
          ((((Finset.Ioc 0 A).filter
            (fun a => Nat.Coprime a q)).card : ℝ) * (B : ℝ)) +
        2 * C * (A * B : ℝ) ^ α * Q := by
  let P := (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)
  let M := ∑ x : ZMod q,
    (burgessResidueMultiplicity q N H A x : ℝ) * ‖burgessShiftSum B χ x‖
  have hOne : 1 ∈ P := by
    simp [P, hA]
  have hPPosNat : 0 < P.card := Finset.card_pos.mpr ⟨1, hOne⟩
  have hPPos : (0 : ℝ) < P.card := by exact_mod_cast hPPosNat
  have hBPos : (0 : ℝ) < B := by exact_mod_cast hB
  have hDPos : (0 : ℝ) < (P.card : ℝ) * (B : ℝ) := mul_pos hPPos hBPos
  have hrec := burgessAffineAverage_recursion_rpow_le
    χ hAB hC hQ hα hleft hright
  calc
    ‖burgessIntervalCharacterSum χ N H‖ ≤
        (M + ((P.card : ℝ) * (B : ℝ)) *
          (2 * C * (A * B : ℝ) ^ α * Q)) /
            ((P.card : ℝ) * (B : ℝ)) := by
      apply (le_div_iff₀ hDPos).2
      simpa only [P, M, mul_assoc, mul_left_comm, mul_comm] using hrec
    _ = M / ((P.card : ℝ) * (B : ℝ)) +
          2 * C * (A * B : ℝ) ^ α * Q := by
      field_simp

/-- The normalized recursion is monotone in any supplied upper bound for its
multiplicity-weighted Hölder main term. -/
theorem norm_burgessIntervalCharacterSum_le_of_holderBound_add_rpowBoundary
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hAB : A * B ≤ H)
    {C Q α V : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hα : 0 ≤ α)
    (hleft : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤
          C * (a * b : ℝ) ^ α * Q)
    (hright : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤
          C * (a * b : ℝ) ^ α * Q)
    (hV : (∑ x : ZMod q,
      (burgessResidueMultiplicity q N H A x : ℝ) * ‖burgessShiftSum B χ x‖) ≤ V) :
    ‖burgessIntervalCharacterSum χ N H‖ ≤
      V / ((((Finset.Ioc 0 A).filter
        (fun a => Nat.Coprime a q)).card : ℝ) * (B : ℝ)) +
        2 * C * (A * B : ℝ) ^ α * Q := by
  refine (norm_burgessIntervalCharacterSum_le_holderTerm_add_rpowBoundary
    χ hA hB hAB hC hQ hα hleft hright).trans ?_
  gcongr

/-- Hölder's inequality in the exact multiplicity/moment form required by
the Burgess argument.  The right side has already been rewritten using the
proved first-moment and collision identities. -/
theorem burgessResidueMultiplicity_holder_pow
    {q N H A B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hr : 1 ≤ r) :
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) ^ (2 * r) ≤
      ((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ (2 * r - 2) *
        ((burgessResidueCollisionPairs q N H A).card : ℝ) *
          ∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) := by
  have h := sum_mul_pow_le_interpolation_of_nonneg
    (Finset.univ : Finset (ZMod q))
    (fun x => (burgessResidueMultiplicity q N H A x : ℝ))
    (fun x => ‖burgessShiftSum B χ x‖) r hr
    (fun _ => by positivity) (fun _ => norm_nonneg _)
  have hfirst :
      (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ)) =
        ((burgessCoprimeMultiplierPairs q A H).card : ℝ) := by
    exact_mod_cast sum_burgessResidueMultiplicity q N H A
  have hsecond :
      (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) ^ 2) =
        ((burgessResidueCollisionPairs q N H A).card : ℝ) := by
    exact_mod_cast
      sum_sq_burgessResidueMultiplicity_eq_card_collisions q N H A
  simpa only [hfirst, hsecond] using h

/-- Root form of the Burgess Hölder estimate. The exponent is the reciprocal
of the positive real number `2*r`, so this statement can be substituted
directly into the normalized amplification recurrence. -/
theorem burgessResidueMultiplicity_holder
    {q N H A B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hr : 1 ≤ r) :
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) ≤
      (((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ (2 * r - 2) *
        ((burgessResidueCollisionPairs q N H A).card : ℝ) *
          ∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r)) ^
            (((2 * r : ℕ) : ℝ)⁻¹) := by
  let M : ℝ := ∑ x : ZMod q,
    (burgessResidueMultiplicity q N H A x : ℝ) * ‖burgessShiftSum B χ x‖
  let R : ℝ :=
    ((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ (2 * r - 2) *
      ((burgessResidueCollisionPairs q N H A).card : ℝ) *
        ∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have htwoR : (0 : ℝ) < ((2 * r : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * r)
  apply (Real.le_rpow_inv_iff_of_pos hM0 hR0 htwoR).2
  rw [Real.rpow_natCast]
  exact burgessResidueMultiplicity_holder_pow χ hr

/-- Monotone root-form Hölder estimate with abstract upper bounds for the
collision factor and the complete moment. -/
theorem burgessResidueMultiplicity_holder_le_of_bounds
    {q N H A B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hr : 1 ≤ r) {V₂ V₂r : ℝ}
    (hV₂ : ((burgessResidueCollisionPairs q N H A).card : ℝ) ≤ V₂)
    (hV₂r : (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ) ≤ V₂r) :
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) ≤
      (((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ (2 * r - 2) *
        V₂ * V₂r) ^ (((2 * r : ℕ) : ℝ)⁻¹) := by
  have hbase :
      ((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ (2 * r - 2) *
          ((burgessResidueCollisionPairs q N H A).card : ℝ) *
            ∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) ≤
        ((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ (2 * r - 2) *
          V₂ * V₂r := by
    have hV₂0 : 0 ≤ V₂ := (Nat.cast_nonneg _).trans hV₂
    gcongr
  exact (burgessResidueMultiplicity_holder χ hr).trans
    (Real.rpow_le_rpow (by positivity) hbase (by positivity))

/-- The `r = 7` Hölder main term after insertion of the proved harmonic
collision estimate and an arbitrary fourteenth-moment majorant. -/
theorem burgessResidueMultiplicity_holder_fourteenth_le_of_moment
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hAHq : 2 * A * H ≤ q) {V : ℝ}
    (hV : (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤ V) :
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) ≤
      (((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ 12 *
        (((burgessCoprimeMultiplierPairs q A 1).card : ℝ) ^ 2 +
          2 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) * V) ^
            (14 : ℝ)⁻¹ := by
  simpa using burgessResidueMultiplicity_holder_le_of_bounds
    χ (r := 7) (by norm_num)
      (card_burgessResidueCollisionPairs_cast_le_harmonic hAHq) hV

/-- The explicit `r = 7` main-term estimate obtained by combining Hölder,
the harmonic collision bound, and the complete cubefree Weil moment. -/
theorem exists_burgessResidueMultiplicity_holder_fourteenth_le_of_completeWeil_rpow
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
        TaoCubefree q → DirichletCharacter.IsPrimitive χ →
        2 * A * H ≤ q →
        (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
            ‖burgessShiftSum B χ x‖) ≤
          (((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ 12 *
            (((burgessCoprimeMultiplierPairs q A 1).card : ℝ) ^ 2 +
              2 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) *
            (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
              C * (B : ℝ) ^ 14 *
                (q : ℝ) ^ ((1 / 2 : ℝ) + ε))) ^ (14 : ℝ)⁻¹ := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_burgess_shift_fourteenth_moment_le_of_completeWeil_rpow hweil hε
  refine ⟨C, hC, ?_⟩
  intro q N H A B _ χ hq hχ hAHq
  exact burgessResidueMultiplicity_holder_fourteenth_le_of_moment χ hAHq
    (hmoment χ hq hχ)

/-- Full normalized `r = 7` Burgess recurrence after the powered boundary,
Hölder, harmonic collision, and complete-moment estimates have all been
inserted. Only scalar parameter estimates remain in this amplification step. -/
theorem exists_norm_burgessIntervalCharacterSum_le_fourteenthMain_add_rpowBoundary
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
        TaoCubefree q → DirichletCharacter.IsPrimitive χ →
        1 ≤ A → 1 ≤ B → A * B ≤ H → 2 * A * H ≤ q →
        ∀ {C₂ Q α : ℝ}, 0 ≤ C₂ → 0 ≤ Q → 0 ≤ α →
        (∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
          ∀ b ∈ Finset.Ioc 0 B,
            ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤
              C₂ * (a * b : ℝ) ^ α * Q) →
        (∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
          ∀ b ∈ Finset.Ioc 0 B,
            ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤
              C₂ * (a * b : ℝ) ^ α * Q) →
        ‖burgessIntervalCharacterSum χ N H‖ ≤
          ((((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ 12 *
            (((burgessCoprimeMultiplierPairs q A 1).card : ℝ) ^ 2 +
              2 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) *
            (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
              C₁ * (B : ℝ) ^ 14 *
                (q : ℝ) ^ ((1 / 2 : ℝ) + ε))) ^ (14 : ℝ)⁻¹) /
              ((((Finset.Ioc 0 A).filter
                (fun a => Nat.Coprime a q)).card : ℝ) * (B : ℝ)) +
            2 * C₂ * (A * B : ℝ) ^ α * Q := by
  obtain ⟨C₁, hC₁, hmain⟩ :=
    exists_burgessResidueMultiplicity_holder_fourteenth_le_of_completeWeil_rpow
      hweil hε
  refine ⟨C₁, hC₁, ?_⟩
  intro q N H A B _ χ hq hχ hA hB hAB hAHq C₂ Q α hC₂ hQ hα hleft hright
  exact norm_burgessIntervalCharacterSum_le_of_holderBound_add_rpowBoundary
    χ hA hB hAB hC₂ hQ hα hleft hright (hmain χ hq hχ hAHq)

/-- Complex-valued version of the preceding Hölder estimate, ready to consume
the exact affine-average identity. -/
theorem norm_burgessMultiplicityWeightedShiftSum_pow_le
    {q N H A B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hr : 1 ≤ r) :
    ‖∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℂ) *
        burgessShiftSum B χ x‖ ^ (2 * r) ≤
      ((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ (2 * r - 2) *
        ((burgessResidueCollisionPairs q N H A).card : ℝ) *
          ∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) := by
  have hnorm :
      ‖∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℂ) *
          burgessShiftSum B χ x‖ ≤
        ∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
          ‖burgessShiftSum B χ x‖ := by
    calc
      ‖∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℂ) *
          burgessShiftSum B χ x‖ ≤
          ∑ x : ZMod q,
            ‖(burgessResidueMultiplicity q N H A x : ℂ) *
              burgessShiftSum B χ x‖ := norm_sum_le _ _
      _ = ∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
            ‖burgessShiftSum B χ x‖ := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [norm_mul, norm_natCast]
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm (2 * r)).trans
    (burgessResidueMultiplicity_holder_pow χ hr)

/-- Source-facing Hölder estimate for the complete coprime affine average. -/
theorem norm_sum_coprime_burgessAffineShiftSum_pow_le
    {q N H A B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hr : 1 ≤ r) :
    ‖∑ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
        ∑ b ∈ Finset.Ioc 0 B, burgessAffineShiftSum χ N H a b‖ ^ (2 * r) ≤
      ((burgessCoprimeMultiplierPairs q A H).card : ℝ) ^ (2 * r - 2) *
        ((burgessResidueCollisionPairs q N H A).card : ℝ) *
          ∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) := by
  rw [sum_coprime_burgessAffineShiftSum_eq_multiplicity_sum χ]
  exact norm_burgessMultiplicityWeightedShiftSum_pow_le χ hr

/-!
The collision-counting layer is complete through its harmonic summation.
The exact pre-Hölder recursion is complete through specialization to a
nonnegative power majorant, endpoint summation, and normalization by the
positive affine-average denominator. The powered Hölder estimate has now been
rooted, and the harmonic collision and complete fourteenth-moment estimates
are inserted into one normalized recurrence. The remaining amplification
step is scalar parameter estimation and optimization.
-/

end

end Tao2026
