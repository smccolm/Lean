import Dubon2026.DescendedTraceCoefficientGeneration
import Dubon2026.MatrixStrictConjugacyCoefficientChange

/-! Equality of trace coefficients gives strict conjugacy after a genuine
whole trace descent. This uses the existing descent and coefficient-change
theorems on the route to DUB-17's CM polarization descent. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {G ι O R A k : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [CommRing R] [CommRing A] [CommRing k]
  [Algebra O R] [Algebra O A]
  [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace A] [T2Space A]

/-- Two coefficient specializations of an actual whole representation with
equal traces are strictly conjugate whenever that representation has a
genuine strict descent to its own closed trace algebra. -/
theorem matrixStrictlyConjugate_of_trace_specializations
    (rR : R →+* k) (rA : A →+* k) (ρ : G →* GeneralLinearGroup ι R)
    (τ : G →* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ))
    (hτ : MatrixStrictlyConjugate rR
      ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ).val.toRingHom).comp τ) ρ)
    (f g : R →ₐ[O] A) (hf : Continuous f) (hg : Continuous g)
    (hrf : rA.comp f.toRingHom = rR) (hrg : rA.comp g.toRingHom = rR)
    (htrace : ∀ x, f (Matrix.trace (ρ x).val) = g (Matrix.trace (ρ x).val)) :
    MatrixStrictlyConjugate rA
      ((GeneralLinearGroup.map f.toRingHom).comp ρ)
      ((GeneralLinearGroup.map g.toRingHom).comp ρ) := by
  let T := closedMatrixTraceAlgebra (O := O) ρ
  have heq := eqOn_closedMatrixTraceAlgebra ρ f g hf hg htrace
  have he : (GeneralLinearGroup.map f.toRingHom).comp
      ((GeneralLinearGroup.map T.val.toRingHom).comp τ) =
      (GeneralLinearGroup.map g.toRingHom).comp
        ((GeneralLinearGroup.map T.val.toRingHom).comp τ) := by
    apply MonoidHom.ext
    intro x
    apply Units.ext
    ext i j
    exact heq ((τ x).val i j).property
  have hcf := matrixStrictlyConjugate_map rR rA f.toRingHom hrf _ _ hτ
  have hcg := matrixStrictlyConjugate_map rR rA g.toRingHom hrg _ _ hτ
  rw [← he] at hcg
  exact matrixStrictlyConjugate_trans _ _ _ _
    (matrixStrictlyConjugate_symm _ _ _ hcf) hcg

end
end Dubon2026
