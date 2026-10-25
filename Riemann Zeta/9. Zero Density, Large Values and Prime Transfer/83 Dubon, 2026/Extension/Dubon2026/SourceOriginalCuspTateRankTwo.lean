import Dubon2026.SourceOriginalCuspRationalTateHecke
import Dubon2026.SourceOriginalCuspPadicHeckeMap
import Dubon2026.SourceOriginalExplicitHeckeRankTwo
import Dubon2026.SourceRankTwoSurjectiveDescent

/-! DUB-17/18 -> primitive determinant -> the actual primitive Tate image.
Reuse the already proved all-word rank-two coordinates and the surjective
integral cusp presentation to retain every integral operator at once. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b
open scoped IsMulCommutative

theorem originalCuspTate_rankTwo {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    ∃ e : originalRationalTateModule N p ≃ₗ[ℚ_[p]]
        (Fin 2 → SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p),
      ∀ (t : sourceOriginalIntegralHeckeAlgebra N 2) (x : originalRationalTateModule N p),
        e (originalCuspRationalTateHecke N p b P₀ lb t x) =
          (fun i => originalCuspPadicHeckeMap N p b lb t * e x i) := by
  exact rankTwo_surjective_descent
    (sourceIntegralCuspHeckeWord N) (sourceIntegralCuspHeckeWord_surjective N)
    (originalRationalTateHeckeWord N p) (originalCuspRationalTateHecke N p b P₀ lb)
    (fun a => SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
      (originalFullLatticeHeckeWord N b a))
    (originalCuspPadicHeckeMap N p b lb)
    (originalCuspRationalTateHecke_word N p b P₀ lb)
    (originalCuspPadicHeckeMap_word N p b lb)
    (originalRationalTate_explicit_word_rankTwo N p b P₀ lb)

end
end Dubon2026.SourceFunctionField.OriginalChart
