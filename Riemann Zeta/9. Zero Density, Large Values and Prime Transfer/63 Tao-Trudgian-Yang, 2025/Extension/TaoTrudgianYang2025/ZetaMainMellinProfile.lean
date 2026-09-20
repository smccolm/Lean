import TaoTrudgianYang2025.ZetaMainElementaryWeights

/-!
# Fixed Mellin profile of the actual main source

After x is divided by T, the complex logarithmic argument lies in
one fixed positive compact interval. Holomorphy of the actual contour
weight gives uniform bounds for the profile and its derivative.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def zetaMainMellinProfile (u : ℝ) : ℂ :=
  zetaDivisorWeight ((Real.log u + Real.log (2 * Real.pi) : ℝ) +
    (Real.pi / 2 : ℝ) * I)

theorem contDiffAt_zetaMainMellinProfile {u : ℝ} (hu : 0 < u) :
    ContDiffAt ℝ 1 zetaMainMellinProfile u := by
  have hl : ContDiffAt ℝ 1 Real.log u := Real.contDiffAt_log.mpr hu.ne'
  have hc : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hw : ContDiff ℝ 1 zetaDivisorWeight := contDiff_zetaDivisorWeight.of_le (by simp)
  unfold zetaMainMellinProfile
  fun_prop

theorem zetaDivisorWeight_source_eq_profile {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    zetaDivisorWeight ((Real.log x : ℂ) - zetaGammaLeadingLog T) =
      zetaMainMellinProfile (x / T) := by
  unfold zetaMainMellinProfile zetaGammaLeadingLog
  rw [Real.log_div hx.ne' hT.ne', Real.log_div hT.ne' (by positivity : 2 * Real.pi ≠ 0)]
  congr 1
  push_cast
  ring

theorem exists_intervalC1Bound_zetaMainMellinProfile :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      IntervalC1Bound (fun x => zetaMainMellinProfile (x / T)) (T / 16) T C :=
  exists_intervalC1Bound_rescaled (fun _ hu => contDiffAt_zetaMainMellinProfile hu)

end TaoTrudgianYang2025

