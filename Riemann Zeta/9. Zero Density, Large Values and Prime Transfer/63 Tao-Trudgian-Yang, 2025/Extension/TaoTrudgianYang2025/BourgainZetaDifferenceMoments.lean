import TaoTrudgianYang2025.BourgainDifferenceLevels
import TaoTrudgianYang2025.BourgainIntegerWindows
import TaoTrudgianYang2025.JutilaReflectionIntegrals
import TaoTrudgianYang2025.ZetaMomentTransfer

/-!
# Bourgain's weighted local zeta-square moment

The multiplicities and moving zeta integrals are the actual source objects.
Finite Cauchy--Schwarz, interval Hölder and integer-window overlap give
an explicit fourth-moment bound. The retained-zeta source entry (4.7) and
the large-branch zeta-superlevel selection remain separate obligations.
-/

open Finset MeasureTheory
open scoped Interval
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The actual critical-line zeta-square integral around an integer. -/
def bourgainLocalZetaSquare (H : ℝ) (ℓ : ℤ) : ℝ :=
  ∫ u in -H..H, zetaMomentCriticalNorm ((ℓ : ℝ) + u) ^ 2

/-- The retained local zeta moment, weighted by genuine ordered-pair counts. -/
def bourgainZetaDifferenceMoment (W : Finset ℝ) (H : ℝ) : ℝ :=
  ∑ ℓ ∈ bourgainDifferenceSupport W,
    (bourgainDifferenceCount W ℓ : ℝ) * bourgainLocalZetaSquare H ℓ

/-- The local square moment is nonnegative, including a zero-radius window. -/
theorem bourgainLocalZetaSquare_nonneg {H : ℝ} (hH : 0 ≤ H) (ℓ : ℤ) :
    0 ≤ bourgainLocalZetaSquare H ℓ := by
  exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)

/-- Exact translation of the actual local zeta-square integral. -/
theorem bourgainLocalZetaSquare_eq (H : ℝ) (ℓ : ℤ) :
    bourgainLocalZetaSquare H ℓ =
      ∫ t in (ℓ : ℝ)-H..(ℓ : ℝ)+H, zetaMomentCriticalNorm t ^ 2 := by
  unfold bourgainLocalZetaSquare
  convert intervalIntegral.integral_comp_add_left
    (fun t => zetaMomentCriticalNorm t ^ 2) (ℓ : ℝ) using 1

/-- Interval Hölder with the exact local window length. -/
theorem bourgainLocalZetaSquare_sq_le {H : ℝ} (hH : 0 ≤ H) (ℓ : ℤ) :
    bourgainLocalZetaSquare H ℓ ^ 2 ≤
      2 * H * ∫ t in (ℓ : ℝ)-H..(ℓ : ℝ)+H, zetaMomentCriticalNorm t ^ 4 := by
  have h := jutila_intervalIntegral_pow_le
    (fun u => zetaMomentCriticalNorm ((ℓ : ℝ)+u)^2) H hH
    (by norm_num : 0 < (2 : ℕ))
    ((continuous_zetaMomentCriticalNorm.comp (continuous_const.add continuous_id)).pow 2)
    (fun _ => sq_nonneg _)
  have hshift :
      (∫ u in -H..H, zetaMomentCriticalNorm ((ℓ : ℝ)+u)^4) =
        ∫ t in (ℓ : ℝ)-H..(ℓ : ℝ)+H, zetaMomentCriticalNorm t^4 := by
    convert intervalIntegral.integral_comp_add_left
      (fun t => zetaMomentCriticalNorm t^4) (ℓ : ℝ) using 1
  norm_num only [Nat.reduceSub, pow_one, ← pow_mul, Nat.reduceMul] at h
  rw [hshift] at h
  exact h

/-- The sum of squared local zeta moments costs only a polynomial window
factor, independently of the number of integer centres. -/
theorem bourgainLocalZetaSquare_sum_sq_le (D : Finset ℤ)
    (H a b : ℝ) (hH : 0 ≤ H) (hab : a ≤ b)
    (hrange : ∀ ℓ ∈ D, a ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ b) :
    (∑ ℓ ∈ D, bourgainLocalZetaSquare H ℓ ^ 2) ≤
      2 * H * (2 * Nat.ceil H + 1 : ℕ) *
        ∫ t in a-H..b+H, zetaMomentCriticalNorm t ^ 4 := by
  calc
    _ ≤ ∑ ℓ ∈ D, 2 * H *
        ∫ t in (ℓ : ℝ)-H..(ℓ : ℝ)+H, zetaMomentCriticalNorm t^4 :=
      Finset.sum_le_sum fun ℓ _ => bourgainLocalZetaSquare_sq_le hH ℓ
    _ = 2 * H * ∑ ℓ ∈ D,
        ∫ t in (ℓ : ℝ)-H..(ℓ : ℝ)+H, zetaMomentCriticalNorm t^4 := by
      rw [Finset.mul_sum]
    _ ≤ 2 * H * ((2 * Nat.ceil H + 1 : ℕ) *
        ∫ t in a-H..b+H, zetaMomentCriticalNorm t^4) :=
      mul_le_mul_of_nonneg_left
        (bourgain_sum_integer_window_integral_le D
          (fun t => zetaMomentCriticalNorm t^4) (continuous_zetaMomentCriticalNorm.pow 4)
          (fun _ => by positivity) H a b hH hab hrange) (by positivity)
    _ = _ := by ring

/-- The actual weighted zeta-square moment satisfies Bourgain's
Cauchy--Schwarz reduction to a global fourth moment. No local-moment
bound, multiplicity cap, or support range is supplied independently. -/
theorem bourgainZetaDifferenceMoment_sq_le {W : Finset ℝ} {T H : ℝ}
    (hsep : IsSeparated 2 W) (hbase : InBaseInterval T W)
    (hT : 0 ≤ T) (hH : 0 ≤ H) :
    bourgainZetaDifferenceMoment W H ^ 2 ≤
      4 * H * (2 * Nat.ceil H + 1 : ℕ) * (W.card : ℝ) ^ 3 *
        ∫ t in -(T+H+1)..T+H+1, zetaMomentCriticalNorm t ^ 4 := by
  have hCS := bourgainDifferenceCount_weighted_sq_le hsep
    (bourgainDifferenceSupport W) (bourgainLocalZetaSquare H)
  have hlocal := bourgainLocalZetaSquare_sum_sq_le
    (bourgainDifferenceSupport W) H (-T-1) (T+1) hH (by linarith)
    (fun _ hℓ => bourgainDifferenceSupport_bounds hbase hℓ)
  have hbound := hCS.trans (mul_le_mul_of_nonneg_left hlocal
    (by positivity : 0 ≤ 2 * (W.card : ℝ)^3))
  have hlo : -T-1-H = -(T+H+1) := by ring
  have hhi : T+1+H = T+H+1 := by ring
  rw [hlo, hhi] at hbound
  convert hbound using 1
  ring

/-- Positive mass in the source zeta integral selects a genuine nonempty
dyadic difference level with its exact cardinality and moment losses. -/
theorem bourgainZetaDifferenceMoment_select_level {W : Finset ℝ} {H : ℝ}
    (hsep : IsSeparated 2 W) (hH : 0 ≤ H)
    (hmass : 0 < bourgainZetaDifferenceMoment W H) :
    ∃ j ∈ Finset.range (Nat.log 2 W.card + 1),
      (bourgainDifferenceLevel W j).Nonempty ∧
      2 ^ j ≤ W.card ∧
      2 ^ j * (bourgainDifferenceLevel W j).card ≤ 2 * W.card ^ 2 ∧
      bourgainZetaDifferenceMoment W H ≤
        (Nat.log 2 W.card + 1 : ℕ) * (2 : ℝ) ^ (j+1) *
          ∑ ℓ ∈ bourgainDifferenceLevel W j, bourgainLocalZetaSquare H ℓ :=
  bourgainDifferenceLevel_select hsep (bourgainLocalZetaSquare H)
    (fun ℓ _ => bourgainLocalZetaSquare_nonneg hH ℓ) hmass

/-- The original real pair differences enter the retained integer zeta
moment, with the necessary unit enlargement made explicit. -/
theorem bourgain_pair_zeta_square_integral_le (W : Finset ℝ) {H : ℝ}
    (hH : 0 ≤ H) :
    (∑ t ∈ W, ∑ v ∈ W,
      ∫ u in -H..H, zetaMomentCriticalNorm (t-v+u)^2) ≤
        bourgainZetaDifferenceMoment W (H+1) := by
  have h := bourgain_difference_window_integral_le W
    (fun x => zetaMomentCriticalNorm x^2) (continuous_zetaMomentCriticalNorm.pow 2)
    (fun _ => sq_nonneg _) H hH
  simpa only [Finset.sum_product, bourgainZetaDifferenceMoment,
    bourgainLocalZetaSquare] using h

end TaoTrudgianYang2025
