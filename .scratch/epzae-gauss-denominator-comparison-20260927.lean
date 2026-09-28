import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

example (C X μ : ℝ) (N q : ℕ) (hC : 1 ≤ C) (hN : 1 ≤ N)
    (hqN : q ≤ N)
    (hbound : X ≤ C*(Real.sqrt q*Real.log (2*(N:ℝ))+1/(μ*(N:ℝ)^2)+
      1/(Real.sqrt (μ*(N:ℝ))*Real.sqrt q))) :
    X ≤ C*(Real.sqrt N*Real.log (2*(N:ℝ))+1/(μ*(N:ℝ)^2)+
      1/(Real.sqrt (μ*(N:ℝ))*Real.sqrt q)) := by
  apply hbound.trans
  have hlog : 0 ≤ Real.log (2*(N : ℝ)) := by
    apply Real.log_nonneg
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hn]
  have hsq : Real.sqrt (q : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hqN)
  gcongr
