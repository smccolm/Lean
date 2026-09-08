import RiemannZeta.GuthMaynard.HughesYoungReducedIntegratedConsumer
import RiemannZeta.GuthMaynard.HughesYoungShiftRanges

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The exact Hughes--Young near-shift DFI estimate
-/

/-- DFI Theorem 1, its signed central terms, gcd reduction, Fubini, and the
small-contour ordinate integral assembled on Hughes--Young's literal near
shift family. -/
theorem exists_uniform_norm_hughesYoungNearShiftSource_full_dfi
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T H X Y P U Q : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 0 ≤ H →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k → 1 ≤ P →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤ 2 * X →
      ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤ 2 * Y →
      ‖∑ r ∈ hughesYoungNearShifts T P X Y
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
          dfiDyadicShiftedDivisorSum
            (hughesYoungGCDReducedIntegratedBoxWeight T
              (hughesYoungSmallContour T) H X Y h k)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            M N r‖ ≤
        (T * (Real.log T * Real.exp (4 * Cγ) *
          ((hughesYoungReducedLeft h k : ℝ) / X) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
          ((hughesYoungReducedRight h k : ℝ) / Y) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
          hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungNearShifts T P X Y
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              M N)) * L := by
  obtain ⟨Cγ, C, L, hCγ, hC, hL, hnear⟩ :=
    exists_uniform_norm_sum_hughesYoungSmallContourGCDReduced_full_dfi
      ε hε0 hε4
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T H X Y P U Q h k M N hT hH hX hY hh hk hP hscale hQ hU
    hQsq hM hN haX hbY
  apply hnear hT hH hX hY hh hk hP hscale hQ hU hQsq hM hN haX hbY
  exact hughesYoungNearShifts_dfi_conditions

end RiemannZeta.GuthMaynard
