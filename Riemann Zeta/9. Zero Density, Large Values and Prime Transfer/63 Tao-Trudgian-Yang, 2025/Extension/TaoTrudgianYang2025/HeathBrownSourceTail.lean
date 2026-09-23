import TaoTrudgianYang2025.HeathBrownPhysicalPhase
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Exact source tails and the fixed derivative sign

The closed source sum loses only its first term on translation to the
positive-index Heath--Brown sum. A negative derivative sign is handled
by exact complex conjugation of that same finite sum.
-/

noncomputable section

open Expdb
open scoped FourierTransform BigOperators

namespace TaoTrudgianYang2025

def heathBrownCharacterSum (L : ℕ) (f : ℝ → ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 L, (𝐞 (f n) : ℂ)

def heathBrownSourceTail (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 L, oscillatory F T N ((a : ℝ)+n)

theorem exponentialSumAt_first_add_heathBrownTail
    (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) :
    exponentialSumAt F T N a (a+L) =
      oscillatory F T N a + heathBrownSourceTail F T N a L := by
  induction L with
  | zero => simp [exponentialSumAt,heathBrownSourceTail]
  | succ L ih =>
    have hsum := Finset.sum_Icc_succ_top (a := a) (b := a+L)
      (by omega) (fun n : ℕ => oscillatory F T N n)
    have htail := Finset.sum_Icc_succ_top (a := 1) (b := L)
      (by omega) (fun n : ℕ => oscillatory F T N ((a : ℝ)+n))
    change exponentialSumAt F T N a ((a+L)+1) =
      oscillatory F T N a + heathBrownSourceTail F T N a (L+1)
    change exponentialSumAt F T N a ((a+L)+1) =
      exponentialSumAt F T N a (a+L)+oscillatory F T N (((a+L)+1 : ℕ) : ℝ) at hsum
    change heathBrownSourceTail F T N a (L+1) =
      heathBrownSourceTail F T N a L+oscillatory F T N ((a : ℝ)+(L+1 : ℕ)) at htail
    rw [hsum,htail,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_assoc]

theorem norm_exponentialSumAt_le_one_add_heathBrownTail
    (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) :
    ‖exponentialSumAt F T N a (a+L)‖ ≤ 1+‖heathBrownSourceTail F T N a L‖ := by
  rw [exponentialSumAt_first_add_heathBrownTail]
  exact (norm_add_le _ _).trans_eq (by rw [norm_oscillatory])

theorem heathBrownCharacterSum_neg (L : ℕ) (f : ℝ → ℝ) :
    heathBrownCharacterSum L (fun x => -f x) =
      starRingEnd ℂ (heathBrownCharacterSum L f) := by
  unfold heathBrownCharacterSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]

theorem norm_heathBrownSourceTail_eq_signed_characterSum
    (F : ℝ → ℝ) (T N σ : ℝ) (a L p : ℕ) :
    ‖heathBrownSourceTail F T N a L‖ =
      ‖heathBrownCharacterSum L
        (heathBrownPhysicalPhase F T N a (modelPhaseJetSign σ p))‖ := by
  unfold modelPhaseJetSign
  split
  · simp only [heathBrownPhysicalPhase,one_mul,heathBrownCharacterSum,
      heathBrownSourceTail,oscillatory]
  · have he : heathBrownPhysicalPhase F T N a (-1) =
        (fun x => -(T*F (((a : ℝ)+x)/N))) := by
      funext x
      unfold heathBrownPhysicalPhase
      ring
    rw [he,heathBrownCharacterSum_neg,Complex.norm_conj]
    rfl

end TaoTrudgianYang2025
