import Dubon2026.RealSmoothSemidirectBracket
import Dubon2026.RealInfinitesimalGroupRelations
import Dubon2026.AdelicSmoothInfinitesimalOperators

/-! # Genuine geodesic brackets on the original adelic smooth-vector space -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

private theorem complex_neg_one_smul {W : Type*} [AddCommGroup W] [Module ℂ W] (w : W) :
    ((-1 : ℝ) : ℂ) • w = -w := by simp

/-- An actual exponential real subgroup relation gives the corresponding original adelic infinitesimal endomorphism bracket. -/
theorem adelicSmoothInfinitesimal_semidirect {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (a b : ℝ → SL(2, ℝ))
    (ha : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => a t i j))
    (hb : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => b t i j)) (ha0 : a 0 = 1)
    (r : ℝ) (hab : ∀ s t, a s * b t = b (Real.exp (r * s) * t) * a s) :
    adelicSmoothInfinitesimal f a ha * adelicSmoothInfinitesimal f b hb -
      adelicSmoothInfinitesimal f b hb * adelicSmoothInfinitesimal f a ha =
      (r : ℂ) • adelicSmoothInfinitesimal f b hb := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothInfinitesimal_semidirect (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl) a b ha hb ha0 r hab

/-- The actual original smooth-space geodesic and upper-unipotent infinitesimal actions satisfy [A,U]=U. -/
theorem adelicSmoothInfinitesimal_geodesic_upper {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff *
        adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff -
      adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff *
        adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff =
      adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff := by
  have he := adelicSmoothInfinitesimal_semidirect f realGeodesicCurve realUpperUnipotent
    realGeodesicCurve_entries_contDiff realUpperUnipotent_entries_contDiff realGeodesicCurve_zero 1
    (fun s t => by simpa only [one_mul] using realGeodesicCurve_mul_upper s t)
  simpa only [Complex.ofReal_one, one_smul] using he

/-- The actual original smooth-space geodesic and lower-unipotent infinitesimal actions satisfy [A,F]=-F. -/
theorem adelicSmoothInfinitesimal_geodesic_lower {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff *
        adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff -
      adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff *
        adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff =
      -adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff := by
  have he := adelicSmoothInfinitesimal_semidirect f realGeodesicCurve realLowerUnipotent
    realGeodesicCurve_entries_contDiff realLowerUnipotent_entries_contDiff realGeodesicCurve_zero (-1)
    (fun s t => by simpa only [neg_one_mul] using realGeodesicCurve_mul_lower s t)
  exact he.trans (complex_neg_one_smul
    (adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff))

end
end Dubon2026
