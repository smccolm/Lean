import GafniTao.WooleySection9Selection

/-!
# Product algebra for Wooley Lemma 9.1

This file isolates the exponent calculation that turns one application of
(8.4), followed by the induction hypothesis at grade `r-1`, into the
equal-weight product in (9.2).  Constants are not hidden: `A` is the common
Section-7 loss base and the deliberately loose power `A^(r+1)` is retained.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The literal product on the right side of Wooley (9.2). -/
def wooleyMonogradeProduct (k r : ℕ) (X : ℕ → ℝ) : ℝ :=
  ∏ j ∈ wooleyGradeRange r,
    (X j) ^ (wooleyRho k j / (r : ℝ))

theorem wooleyMonogradeProduct_nonneg
    {k r : ℕ} {X : ℕ → ℝ}
    (hX : ∀ j ∈ wooleyGradeRange r, 0 ≤ X j) :
    0 ≤ wooleyMonogradeProduct k r X := by
  exact Finset.prod_nonneg fun j hj => Real.rpow_nonneg (hX j hj) _

theorem wooleyMonogradeProduct_one
    {k : ℕ} (X : ℕ → ℝ) :
    wooleyMonogradeProduct k 1 X = (X 1) ^ wooleyRho k 1 := by
  simp [wooleyMonogradeProduct, wooleyGradeRange]

/-- Removing the terminal grade rewrites the source product recursively. -/
theorem wooleyMonogradeProduct_step
    {k r : ℕ} (hr : 2 ≤ r) (X : ℕ → ℝ)
    (hX : ∀ j ∈ wooleyGradeRange r, 0 ≤ X j) :
    wooleyMonogradeProduct k r X =
      (X r) ^ (wooleyRho k r / (r : ℝ)) *
        (wooleyMonogradeProduct k (r - 1) X) ^
          (1 - 1 / (r : ℝ)) := by
  have hrOne : 1 ≤ r := by omega
  have hrPred : 1 ≤ r - 1 := by omega
  have hrR : (0 : ℝ) < r := by positivity
  have hrPredR : (0 : ℝ) < (r - 1 : ℕ) := by
    exact_mod_cast (show 0 < r - 1 by omega)
  have hRange :
      wooleyGradeRange r = insert r (wooleyGradeRange (r - 1)) := by
    unfold wooleyGradeRange
    symm
    exact Finset.insert_Icc_sub_one_right_eq_Icc hrOne
  have hrNotMem : r ∉ wooleyGradeRange (r - 1) := by
    simp [wooleyGradeRange]
    omega
  have hsubset : wooleyGradeRange (r - 1) ⊆ wooleyGradeRange r := by
    intro j hj
    simp only [wooleyGradeRange, mem_Icc] at hj ⊢
    omega
  rw [wooleyMonogradeProduct, hRange, Finset.prod_insert hrNotMem]
  congr 1
  rw [wooleyMonogradeProduct]
  have hprodNonneg :
      ∀ j ∈ wooleyGradeRange (r - 1), 0 ≤ X j :=
    fun j hj => hX j (hsubset hj)
  rw [← Real.finsetProd_rpow
    (wooleyGradeRange (r - 1))
    (fun j => (X j) ^ (wooleyRho k j / ((r - 1 : ℕ) : ℝ)))
    (fun j hj => Real.rpow_nonneg (hprodNonneg j hj) _)
    (1 - 1 / (r : ℝ))]
  apply Finset.prod_congr rfl
  intro j hj
  have hXj := hprodNonneg j hj
  rw [← Real.rpow_mul hXj]
  congr 1
  have hrCast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
  have hrMinus : (0 : ℝ) < (r : ℝ) - 1 := by
    have hrTwo : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  rw [hrCast]
  field_simp [ne_of_gt hrMinus]

/-- The exact one-step envelope calculation behind the induction in Lemma
9.1.  The right side leaves one harmless extra factor of `A`, matching the
source's loose exponent `(r+1)k^2 nu`. -/
theorem wooley_monograde_envelope_step
    {r : ℕ} {A q X P c : ℝ}
    (hr : 2 ≤ r) (hA : 1 ≤ A) (hq : 0 < q)
    (hX : 0 ≤ X) (hP : 0 ≤ P) :
    A * X ^ (1 / (r : ℝ)) *
        (A ^ (r : ℝ) * q ^ (-c / ((r - 1 : ℕ) : ℝ)) * P) ^
          (1 - 1 / (r : ℝ)) ≤
      A ^ ((r + 1 : ℕ) : ℝ) * q ^ (-c / (r : ℝ)) *
        (X ^ (1 / (r : ℝ)) *
          P ^ (1 - 1 / (r : ℝ))) := by
  have hA0 : 0 ≤ A := hA.trans' (by norm_num)
  have hq0 : 0 ≤ q := hq.le
  have hrR : (0 : ℝ) < r := by positivity
  have hrPredR : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < r - 1 by omega)
  let v : ℝ := 1 - 1 / (r : ℝ)
  have hv : 0 ≤ v := by
    dsimp [v]
    have hrTwo : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have : 1 / (r : ℝ) ≤ 1 := by
      rw [div_le_one hrR]
      linarith
    linarith
  have hvId : v = ((r - 1 : ℕ) : ℝ) / (r : ℝ) := by
    dsimp [v]
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
    field_simp
  have hAexp :
      1 + (r : ℝ) * v ≤ ((r + 1 : ℕ) : ℝ) := by
    have hrCast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r)]
      norm_num
    rw [hvId, hrCast, Nat.cast_add, Nat.cast_one]
    field_simp
    linarith
  have hApow : A * (A ^ (r : ℝ)) ^ v ≤ A ^ ((r + 1 : ℕ) : ℝ) := by
    have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
    calc
      A * (A ^ (r : ℝ)) ^ v =
          A ^ (1 : ℝ) * A ^ ((r : ℝ) * v) := by
        rw [Real.rpow_one, Real.rpow_mul hA0]
      _ = A ^ (1 + (r : ℝ) * v) :=
        (Real.rpow_add hApos _ _).symm
      _ ≤ A ^ ((r + 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hA hAexp
  have hqexp :
      (-c / ((r - 1 : ℕ) : ℝ)) * v = -c / (r : ℝ) := by
    rw [hvId]
    field_simp
  have hinside :
      (A ^ (r : ℝ) * q ^ (-c / ((r - 1 : ℕ) : ℝ)) * P) ^ v =
        (A ^ (r : ℝ)) ^ v * q ^ (-c / (r : ℝ)) * P ^ v := by
    rw [Real.mul_rpow
      (mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hq0 _)) hP,
      Real.mul_rpow (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hq0 _),
      ← Real.rpow_mul hq0, hqexp]
  rw [hinside]
  have hrest :
      0 ≤ X ^ (1 / (r : ℝ)) * q ^ (-c / (r : ℝ)) * P ^ v := by
    positivity
  calc
    A * X ^ (1 / (r : ℝ)) *
        ((A ^ (r : ℝ)) ^ v * q ^ (-c / (r : ℝ)) * P ^ v) =
      (A * (A ^ (r : ℝ)) ^ v) *
        (X ^ (1 / (r : ℝ)) * q ^ (-c / (r : ℝ)) * P ^ v) := by ring
    _ ≤ A ^ ((r + 1 : ℕ) : ℝ) *
        (X ^ (1 / (r : ℝ)) * q ^ (-c / (r : ℝ)) * P ^ v) :=
      mul_le_mul_of_nonneg_right hApow hrest
    _ = A ^ ((r + 1 : ℕ) : ℝ) * q ^ (-c / (r : ℝ)) *
        (X ^ (1 / (r : ℝ)) * P ^ v) := by ring

/-- Abstract induction underlying Wooley Lemma 9.1.  The second argument of
`K` records the first congruence scale; in the recursive term it is replaced
by the exact ceiling `b_r`. -/
theorem wooley_multigrade_to_monograde
    {k b : ℕ} {A q c : ℝ} (X : ℕ → ℝ) (K : ℕ → ℕ → ℝ)
    (Valid : ℕ → ℕ → Prop)
    (hA : 1 ≤ A) (hq : 0 < q)
    (hX : ∀ j, 1 ≤ j → j < k → 0 ≤ X j)
    (hK : ∀ r a, 0 ≤ K r a)
    (hbase : ∀ a, Valid 1 a →
      K 1 a ≤ A ^ (2 : ℝ) * q ^ (-c) * (X 1) ^ wooleyRho k 1)
    (hstep : ∀ {r a : ℕ}, 2 ≤ r → r < k →
      Valid r a →
      K r a ≤
        A * (X r) ^ (wooleyRho k r / (r : ℝ)) *
          (K (r - 1) (wooleyNextB k r b)) ^
            (1 - 1 / (r : ℝ)))
    (hvalidPred : ∀ {r a : ℕ}, 2 ≤ r → r < k → Valid r a →
      Valid (r - 1) (wooleyNextB k r b)) :
    ∀ {r a : ℕ}, 1 ≤ r → r < k →
      Valid r a →
      K r a ≤
        A ^ ((r + 1 : ℕ) : ℝ) * q ^ (-c / (r : ℝ)) *
          wooleyMonogradeProduct k r X := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro a hr hrk hvalid
      by_cases hrOne : r = 1
      · subst r
        simpa [wooleyMonogradeProduct_one] using hbase a hvalid
      · have hrTwo : 2 ≤ r := by omega
        let v : ℝ := 1 - 1 / (r : ℝ)
        let P : ℝ := wooleyMonogradeProduct k (r - 1) X
        have hrPred : 1 ≤ r - 1 := by omega
        have hrPredK : r - 1 < k := by omega
        have hih := ih (r - 1) (by omega)
          (a := wooleyNextB k r b) hrPred hrPredK
            (hvalidPred hrTwo hrk hvalid)
        have hv : 0 ≤ v := by
          dsimp [v]
          have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hrTwo
          have hrPos : (0 : ℝ) < r := by positivity
          rw [sub_nonneg, div_le_one hrPos]
          linarith
        have hpow :
            (K (r - 1) (wooleyNextB k r b)) ^ v ≤
              (A ^ ((r - 1 + 1 : ℕ) : ℝ) *
                  q ^ (-c / ((r - 1 : ℕ) : ℝ)) * P) ^ v :=
          Real.rpow_le_rpow
            (hK (r - 1) (wooleyNextB k r b)) hih hv
        have hXr : 0 ≤ X r := hX r hr hrk
        have hlead :
            0 ≤ A * (X r) ^ (wooleyRho k r / (r : ℝ)) :=
          mul_nonneg (hA.trans' (by norm_num)) (Real.rpow_nonneg hXr _)
        have hrec := hstep hrTwo hrk hvalid (a := a)
        have hsub : r - 1 + 1 = r := by omega
        have hbound :
            K r a ≤
              A * (X r) ^ (wooleyRho k r / (r : ℝ)) *
                (A ^ (r : ℝ) * q ^ (-c / ((r - 1 : ℕ) : ℝ)) * P) ^ v := by
          calc
            K r a ≤ A * (X r) ^ (wooleyRho k r / (r : ℝ)) *
                (K (r - 1) (wooleyNextB k r b)) ^ v := hrec
            _ ≤ A * (X r) ^ (wooleyRho k r / (r : ℝ)) *
                (A ^ ((r - 1 + 1 : ℕ) : ℝ) *
                    q ^ (-c / ((r - 1 : ℕ) : ℝ)) * P) ^ v :=
              mul_le_mul_of_nonneg_left hpow hlead
            _ = A * (X r) ^ (wooleyRho k r / (r : ℝ)) *
                (A ^ (r : ℝ) * q ^ (-c / ((r - 1 : ℕ) : ℝ)) * P) ^ v := by
              rw [hsub]
        have hterm :
            ((X r) ^ wooleyRho k r) ^ (1 / (r : ℝ)) =
              (X r) ^ (wooleyRho k r / (r : ℝ)) := by
          rw [← Real.rpow_mul hXr]
          congr 1
          ring
        have henv := wooley_monograde_envelope_step
          (r := r) (A := A) (q := q) (X := (X r) ^ wooleyRho k r)
          (P := P) (c := c) hrTwo hA hq (Real.rpow_nonneg hXr _) 
            (wooleyMonogradeProduct_nonneg
              (fun j hj => by
                have hjBounds : 1 ≤ j ∧ j ≤ r - 1 := by
                  simpa only [wooleyGradeRange, mem_Icc] using hj
                exact hX j hjBounds.1 (by omega)))
        rw [hterm] at henv
        change _ ≤ A ^ ((r + 1 : ℕ) : ℝ) * q ^ (-c / (r : ℝ)) *
          ((X r) ^ (wooleyRho k r / (r : ℝ)) * P ^ v) at henv
        have hprod := wooleyMonogradeProduct_step (k := k) hrTwo X
          (fun j hj => by
            have hjBounds : 1 ≤ j ∧ j ≤ r := by
              simpa only [wooleyGradeRange, mem_Icc] using hj
            exact hX j hjBounds.1 (by omega))
        exact hbound.trans (by simpa only [P, v, hprod] using henv)

#print axioms wooleyMonogradeProduct_nonneg
#print axioms wooleyMonogradeProduct_one
#print axioms wooleyMonogradeProduct_step
#print axioms wooley_monograde_envelope_step
#print axioms wooley_multigrade_to_monograde

end

end GafniTao
