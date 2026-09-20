import TaoTrudgianYang2025.ZetaSmoothDivisorTest
import GuthMaynard.DFIProposition1Native

/-!
# Native Voronoi applied to the actual smooth source

The local native theorem is specialized to modulus one. Both canonical
Mellin--Barnes transforms and the full logarithmic main term are kept.
This identity makes no unproved assertion about classical Bessel
representations or subsequent uniform stationary-phase estimates.
-/

noncomputable section

open Complex MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem ordinaryDivisorVoronoi_native {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    (∑' n : ℕ, divisorWeight n * g n) =
      (∫ x : ℝ in Ioi 0, ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) * g x) +
        (∑' n : ℕ, divisorWeight n * dfiVoronoiMinusTransform 1 (mellin g) n) +
        ∑' n : ℕ, divisorWeight n * dfiVoronoiPlusTransform 1 (mellin g) n := by
  have h := hg.dfiProposition1_native 1 1 isUnit_one
  have hchar (x : ZMod 1) : ZMod.stdAddChar x = (1 : ℂ) := by
    rw [Subsingleton.elim x 0]
    exact AddChar.map_zero_eq_one _
  simpa only [periodicDivisorWeightedSum, periodicDivisorCoeff_voronoiCharacter,
    hchar, mul_one, dfiVoronoiMainTerm, Nat.cast_one, inv_one, Complex.log_one,
    mul_zero, sub_zero, one_mul] using h

def zetaDivisorVoronoiMain (T G L : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 0, ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) *
    zetaSmoothDivisorTest T G L x

def zetaDivisorVoronoiMinus (T G L : ℝ) : ℂ :=
  ∑' n : ℕ, divisorWeight n * dfiVoronoiMinusTransform 1 (mellin (zetaSmoothDivisorTest T G L)) n

def zetaDivisorVoronoiPlus (T G L : ℝ) : ℂ :=
  ∑' n : ℕ, divisorWeight n * dfiVoronoiPlusTransform 1 (mellin (zetaSmoothDivisorTest T G L)) n

/-- The input is the constructed source test, not a separately assumed
smoothness, support, contour-shift or Voronoi hypothesis. -/
theorem zetaSmoothDivisorSum_eq_voronoi {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) :
    zetaSmoothDivisorSum T G L =
      zetaDivisorVoronoiMain T G L + zetaDivisorVoronoiMinus T G L +
        zetaDivisorVoronoiPlus T G L :=
  ordinaryDivisorVoronoi_native (zetaSmoothDivisorVoronoiTest hT hG hL)

end TaoTrudgianYang2025
