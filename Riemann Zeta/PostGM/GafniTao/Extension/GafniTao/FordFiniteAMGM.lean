import GafniTao.FordPowerResidueFiber
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities

/-!
# The finite Cauchy--AM--GM step in Ford equation (3.4)

Ford's proof first applies Cauchy to each residue power-sum fibre and then
AM--GM to the squared absolute values of the `s` residue-class Weyl sums.
The factor `1 / s` in AM--GM is essential: after summing over all residue
tuples it cancels the choice of a coordinate, leaving a single `d!` and the
source power `p^(2s-d)`.  These lemmas keep that cancellation explicit.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

instance fordBResidueClassFinite (p d s : ℕ) [NeZero p]
    (v : Fin d → ZMod p) :
    Finite (FordBResidueClass p d s v) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance fordBResidueClassFintype
    (p d s : ℕ) [NeZero p] (v : Fin d → ZMod p) :
    Fintype (FordBResidueClass p d s v) := Fintype.ofFinite _

/-- Division-free, equal-weight AM--GM in the form used by Ford:
`s * prod_i a_i <= sum_i a_i^s`. -/
theorem ford_fin_prod_amgm
    {s : ℕ} (hs : 0 < s) (a : Fin s → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (s : ℝ) * ∏ i, a i ≤ ∑ i, (a i) ^ s := by
  let w : Fin s → ℝ := fun _ => ((s : ℝ)⁻¹)
  let z : Fin s → ℝ := fun i => (a i) ^ s
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin s)), 0 ≤ w i := by
    intro i hi
    exact inv_nonneg.mpr (Nat.cast_nonneg s)
  have hwsum : ∑ i ∈ (Finset.univ : Finset (Fin s)), w i = 1 := by
    simp [w, hsR]
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin s)), 0 ≤ z i := by
    intro i hi
    exact pow_nonneg (ha i) _
  have h := Real.geom_mean_le_arith_mean_weighted
    (Finset.univ : Finset (Fin s)) w z hw hwsum hz
  have hleft :
      ∏ i ∈ (Finset.univ : Finset (Fin s)), z i ^ w i = ∏ i, a i := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [z, w]
    exact Real.pow_rpow_inv_natCast (ha i) hs.ne'
  rw [hleft] at h
  have hright :
      ∑ i ∈ (Finset.univ : Finset (Fin s)), w i * z i =
        (s : ℝ)⁻¹ * ∑ i, (a i) ^ s := by
    simp [w, z, Finset.mul_sum]
  rw [hright] at h
  calc
    (s : ℝ) * ∏ i, a i ≤
        (s : ℝ) * ((s : ℝ)⁻¹ * ∑ i, (a i) ^ s) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg s)
    _ = ∑ i, (a i) ^ s := by field_simp

/-- Cauchy's inequality for a finite complex sum, in the exact squared-norm
form used for `U(alpha;w)`. -/
theorem ford_norm_sum_sq_le_card_mul_sum_norm_sq
    {α : Type*} (B : Finset α) (V : α → ℂ) :
    ‖∑ b ∈ B, V b‖ ^ 2 ≤
      (B.card : ℝ) * ∑ b ∈ B, ‖V b‖ ^ 2 := by
  have htri : ‖∑ b ∈ B, V b‖ ≤ ∑ b ∈ B, ‖V b‖ := norm_sum_le B V
  calc
    ‖∑ b ∈ B, V b‖ ^ 2 ≤ (∑ b ∈ B, ‖V b‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ (B.card : ℝ) * ∑ b ∈ B, ‖V b‖ ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := B) (f := fun b => ‖V b‖))

/-- Join the `d` Newton-controlled coordinates and the remaining `s-d`
coordinates of a residue tuple. -/
def fordBJoin {p d s : ℕ} (hds : d ≤ s)
    (c : (Fin d → ZMod p) × (Fin (s - d) → ZMod p)) :
    Fin s → ZMod p :=
  fun i => Sum.elim c.1 c.2
    ((finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hds))).symm i)

/-- The source Cauchy--AM--GM estimate for one residue power-sum fibre,
before summing over the moment vector `w`.  Its coefficient is exactly
`d! p^(s-d)` and not its square. -/
theorem ford_residue_fiber_cauchy_amgm
    {p d s : ℕ} [NeZero p] (hs : 0 < s) (hds : d ≤ s)
    (hp : Nat.Prime p) (hdp : d < p)
    (v : Fin d → ZMod p) (g : ZMod p → ℂ) :
    (s : ℝ) *
        ‖∑ c : FordBResidueClass p d s v,
          ∏ i, g (fordBJoin hds c.1 i)‖ ^ 2 ≤
      ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) *
        ∑ c : FordBResidueClass p d s v,
          ∑ i : Fin s, ‖g (fordBJoin hds c.1 i)‖ ^ (2 * s) := by
  classical
  let B := (Finset.univ : Finset (FordBResidueClass p d s v))
  let V : FordBResidueClass p d s v → ℂ :=
    fun c => ∏ i, g (fordBJoin hds c.1 i)
  have hCauchy := ford_norm_sum_sq_le_card_mul_sum_norm_sq B V
  have hcardNat : B.card ≤ Nat.factorial d * p ^ (s - d) := by
    simpa [B, Nat.card_eq_fintype_card] using
      (fordBResidueClass_card_le (s := s) hp hdp v)
  have hcardReal : (B.card : ℝ) ≤
      ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hterm (c : FordBResidueClass p d s v) :
      (s : ℝ) * ‖V c‖ ^ 2 ≤
        ∑ i : Fin s, ‖g (fordBJoin hds c.1 i)‖ ^ (2 * s) := by
    have hamgm := ford_fin_prod_amgm hs
      (fun i : Fin s => ‖g (fordBJoin hds c.1 i)‖ ^ 2)
      (fun i => sq_nonneg ‖g (fordBJoin hds c.1 i)‖)
    have hnorm : ‖V c‖ ^ 2 =
        ∏ i : Fin s, ‖g (fordBJoin hds c.1 i)‖ ^ 2 := by
      simp only [V, norm_prod, Finset.prod_pow]
    rw [hnorm]
    simpa only [pow_mul] using hamgm
  calc
    (s : ℝ) *
          ‖∑ c : FordBResidueClass p d s v,
            ∏ i, g (fordBJoin hds c.1 i)‖ ^ 2 =
        (s : ℝ) * ‖∑ c ∈ B, V c‖ ^ 2 := by simp [B, V]
    _ ≤ (s : ℝ) *
          ((B.card : ℝ) * ∑ c ∈ B, ‖V c‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hCauchy (Nat.cast_nonneg s)
    _ = (B.card : ℝ) *
          ((s : ℝ) * ∑ c ∈ B, ‖V c‖ ^ 2) := by ring
    _ = (B.card : ℝ) *
          ∑ c ∈ B, (s : ℝ) * ‖V c‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (B.card : ℝ) *
          ∑ c ∈ B,
            ∑ i : Fin s, ‖g (fordBJoin hds c.1 i)‖ ^ (2 * s) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun c hc => hterm c
      · exact Nat.cast_nonneg B.card
    _ ≤ ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) *
          ∑ c ∈ B,
            ∑ i : Fin s, ‖g (fordBJoin hds c.1 i)‖ ^ (2 * s) := by
      apply mul_le_mul_of_nonneg_right hcardReal
      exact Finset.sum_nonneg fun c hc => Finset.sum_nonneg fun i hi =>
        pow_nonneg (norm_nonneg _) _
    _ = ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) *
        ∑ c : FordBResidueClass p d s v,
          ∑ i : Fin s, ‖g (fordBJoin hds c.1 i)‖ ^ (2 * s) := by simp [B]

#print axioms ford_fin_prod_amgm
#print axioms ford_norm_sum_sq_le_card_mul_sum_norm_sq
#print axioms ford_residue_fiber_cauchy_amgm

end

end GafniTao
