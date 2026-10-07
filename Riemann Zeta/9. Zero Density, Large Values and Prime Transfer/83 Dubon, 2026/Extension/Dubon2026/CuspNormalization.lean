import Dubon2026.CuspCoefficients
import Dubon2026.ZeroCountShift
import Dubon2026.JessenShift

/-! # Actual cusp coefficient normalization translates zeros, potentials, and measures -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups CongruenceSubgroup

theorem cusp_jessenFunction_classical {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (N : ℕ) (σ : ℝ) :
    jessenFunction (cuspCoefficients f) N σ =
      jessenFunction (normalizedCuspCoefficients f) N (σ - ((k : ℝ) - 1) / 2) := by
  rw [normalizedCuspCoefficients, jessenFunction_shiftedCoefficients]
  congr 1
  ring

theorem cusp_zeroMultiplicity_classical {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) (N : ℕ) (s : ℂ) :
    zeroMultiplicity (cuspCoefficients f) N s =
      zeroMultiplicity (normalizedCuspCoefficients f) N (s - ((k : ℂ) - 1) / 2) := by
  rw [normalizedCuspCoefficients, zeroMultiplicity_shiftedCoefficients]
  congr 1
  push_cast
  ring

theorem cusp_verticalZeroCount_classical {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : cuspCoefficients f 1 ≠ 0) {N : ℕ} (hN : 1 ≤ N) (l u T : ℝ) :
    verticalZeroCount (cuspCoefficients f) N hN hf
      (l + ((k : ℝ) - 1) / 2) (u + ((k : ℝ) - 1) / 2) T =
        verticalZeroCount (normalizedCuspCoefficients f) N hN
          (by simpa only [normalizedCuspCoefficients, shiftedCoefficients_one] using hf) l u T := by
  have hh := verticalZeroCount_shiftedCoefficients hN hf (-((k : ℝ) - 1) / 2)
    (l + ((k : ℝ) - 1) / 2) (u + ((k : ℝ) - 1) / 2) T
  have hl : l + ((k : ℝ) - 1) / 2 + -((k : ℝ) - 1) / 2 = l := by ring
  have hu : u + ((k : ℝ) - 1) / 2 + -((k : ℝ) - 1) / 2 = u := by ring
  rw [hl, hu] at hh
  exact hh.symm

theorem cusp_jessenMeasure_classical {Q : ℕ} {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : cuspCoefficients f 1 ≠ 0) {N : ℕ} (hN : 1 ≤ N) :
    jessenMeasure (a := cuspCoefficients f) hN hf =
      Measure.map (fun x : ℝ => x + ((k : ℝ) - 1) / 2)
        (jessenMeasure (a := normalizedCuspCoefficients f) hN
          (by simpa only [normalizedCuspCoefficients, shiftedCoefficients_one] using hf)) := by
  dsimp only [normalizedCuspCoefficients]
  rw [jessenMeasure_shiftedCoefficients hN hf]
  have hp : Measurable (fun x : ℝ => x + ((k : ℝ) - 1) / 2) := measurable_id.add_const _
  have hn : Measurable (fun x : ℝ => x + -((k : ℝ) - 1) / 2) := measurable_id.add_const _
  rw [Measure.map_map hp hn]
  have he : (fun x : ℝ => x + ((k : ℝ) - 1) / 2) ∘
      (fun x : ℝ => x + -((k : ℝ) - 1) / 2) = id := by
    funext x
    dsimp
    ring
  rw [he, Measure.map_id]

end Dubon2026
