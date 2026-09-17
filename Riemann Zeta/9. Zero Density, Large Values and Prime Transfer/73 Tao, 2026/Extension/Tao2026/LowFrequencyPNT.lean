import Tao2026.LowFrequencyIntegral

/-!
# Quantitative PNT interface for low frequencies

Tao's low-frequency argument uses the classical prime number theorem with an
arbitrary logarithmic saving.  The frozen dependency currently exposes only
the qualitative `WeakPNT`, so this module records the missing global prefix
estimate as a proposition and proves all dyadic consequences conditionally.
No quantitative PNT theorem is postulated as an axiom.
-/

open Complex Finset Filter Set
open scoped BigOperators Topology

namespace Tao2026

noncomputable section

/-- Source-faithful quantitative PNT contract: the global Mangoldt prefix
discrepancy has every fixed integral logarithmic saving. -/
def ClassicalMangoldtDiscrepancyLogSaving : Prop :=
  ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ k : ℕ in atTop,
      ‖mangoldtDiscrepancyPartialSum 0 k‖ ≤
        C * k / (Real.log k) ^ A

/-- A global logarithmic-saving PNT estimate is uniform on every subinterval
of a dyadic block. -/
theorem ClassicalMangoldtDiscrepancyLogSaving.uniform_dyadic
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop, ∀ a k : ℕ,
      P ≤ a → a ≤ k → k ≤ 2 * P →
        ‖mangoldtDiscrepancyPartialSum a k‖ ≤
          4 * C * P / (Real.log P) ^ A := by
  obtain ⟨C, hC, hglobal⟩ := hPNT A
  refine ⟨C, hC, ?_⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 hglobal
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop (2 : ℕ)] with P hPK hP2
  intro a k hPa hak hkP
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (show 0 < P by omega)
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hprefix : ∀ x : ℕ, P ≤ x → x ≤ 2 * P →
      ‖mangoldtDiscrepancyPartialSum 0 x‖ ≤
        2 * C * P / (Real.log P) ^ A := by
    intro x hPx hxP
    have hxK : K ≤ x := hPK.trans hPx
    have hxpos : 0 < (x : ℝ) := hPpos.trans_le (by exact_mod_cast hPx)
    have hlogx : 0 < Real.log (x : ℝ) :=
      Real.log_pos ((by exact_mod_cast (show 1 < P by omega) : (1 : ℝ) < P).trans_le
        (by exact_mod_cast hPx))
    have hlogle : Real.log (P : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log hPpos (by exact_mod_cast hPx)
    have hpowle : (Real.log (P : ℝ)) ^ A ≤
        (Real.log (x : ℝ)) ^ A :=
      pow_le_pow_left₀ hlogP.le hlogle A
    calc
      ‖mangoldtDiscrepancyPartialSum 0 x‖ ≤
          C * x / (Real.log x) ^ A := hK x hxK
      _ ≤ C * (2 * P) / (Real.log x) ^ A := by
        apply div_le_div_of_nonneg_right
        · have hxP' : (x : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hxP
          nlinarith
        · positivity
      _ ≤ C * (2 * P) / (Real.log P) ^ A := by
        exact div_le_div_of_nonneg_left (by positivity) (pow_pos hlogP A) hpowle
      _ = 2 * C * P / (Real.log P) ^ A := by ring
  rw [mangoldtDiscrepancyPartialSum_eq_sub hak]
  calc
    ‖mangoldtDiscrepancyPartialSum 0 k -
        mangoldtDiscrepancyPartialSum 0 a‖ ≤
        ‖mangoldtDiscrepancyPartialSum 0 k‖ +
          ‖mangoldtDiscrepancyPartialSum 0 a‖ := norm_sub_le _ _
    _ ≤ 2 * C * P / (Real.log P) ^ A +
        2 * C * P / (Real.log P) ^ A :=
      add_le_add (hprefix k (hPa.trans hak) hkP)
        (hprefix a hPa (hak.trans hkP))
    _ = 4 * C * P / (Real.log P) ^ A := by ring

/-- Exact dyadic Mangoldt/log-to-integral consequence of the quantitative PNT
contract.  This theorem performs the full Abel and discrete-to-continuous
assembly while leaving the classical PNT contract explicit. -/
theorem ClassicalMangoldtDiscrepancyLogSaving.eventually_mangoldtLogWeighted_sub_integral_le
    (hPNT : ClassicalMangoldtDiscrepancyLogSaving)
    {j : ℕ} (hj : 1 ≤ j) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ P : ℕ in atTop, ∀ (N M : ℝ) (a b : ℕ),
      P ≤ a → a < b → b ≤ 2 * P →
      ‖mangoldtLogWeightedReciprocalPhaseSum N M j a b -
          ∫ t in (a : ℝ)..(b : ℝ),
            standardAdditiveCharacter (reciprocalPhase N M j t) / Real.log t‖ ≤
        (1 / Real.log P +
          (2 * Real.pi *
              ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
              Real.log P +
            1 / (Real.log P) ^ 2)) *
            (4 * C * P / (Real.log P) ^ A) +
          (2 * Real.pi *
              ((j + 1 : ℕ) * reciprocalPhaseScale N M j P) /
              Real.log P +
            1 / (Real.log P) ^ 2) := by
  obtain ⟨C, hC, huniform⟩ := hPNT.uniform_dyadic A
  refine ⟨C, hC, ?_⟩
  filter_upwards [huniform, eventually_ge_atTop (2 : ℕ)] with P hpartial hP2
  intro N M a b hPa hab hbP
  have hPreal : 2 ≤ (P : ℝ) := by exact_mod_cast hP2
  have halow : (P : ℝ) ≤ (a : ℝ) := by exact_mod_cast hPa
  have hbhigh : (b : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hbP
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hB : 0 ≤ 4 * C * P / (Real.log P) ^ A := by positivity
  apply norm_mangoldtLogWeightedReciprocalPhaseSum_sub_integral_le
    N M hj hPreal hab halow hbhigh hB
  intro k hak hkb
  exact hpartial a k hPa hak.le (hkb.trans hbP)

end

end Tao2026
