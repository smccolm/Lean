import Dubon2026.MatrixCombinationDeterminant
import Dubon2026.GroupDeterminantLaw
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-! # Direct continuity of all multivariable coefficients of the original determinant law -/

namespace Dubon2026

noncomputable section
open Matrix

variable {σ ι R : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original determinant coefficient, viewed as a universal polynomial in all original tuple entries. -/
def determinantMulticoefficientPolynomial (d : σ →₀ ℕ) : MvPolynomial (σ × ι × ι) R :=
  MvPolynomial.coeff d (matrixCombinationDeterminant
    (fun t i j => (MvPolynomial.X (t, i, j) : MvPolynomial (σ × ι × ι) R)))

/-- Every actual multivariable determinant coefficient is evaluation of the literal universal coefficient polynomial. -/
theorem determinantMulticoefficientPolynomial_eval (d : σ →₀ ℕ)
    (A : σ → Matrix ι ι R) :
    MvPolynomial.eval (fun tij : σ × ι × ι => A tij.1 tij.2.1 tij.2.2)
      (determinantMulticoefficientPolynomial d) =
        MvPolynomial.coeff d (matrixCombinationDeterminant A) := by
  let φ := MvPolynomial.eval (fun tij : σ × ι × ι => A tij.1 tij.2.1 tij.2.2)
  let U : σ → Matrix ι ι (MvPolynomial (σ × ι × ι) R) := fun t i j => MvPolynomial.X (t, i, j)
  have he := matrixCombinationDeterminant_map φ U
  have hm : (fun t => (U t).map φ) = A := by
    funext t i j
    exact MvPolynomial.eval_X (t, i, j)
  rw [hm] at he
  have hc := congrArg (MvPolynomial.coeff d) he
  simpa only [MvPolynomial.coeff_map] using hc

/-- All actual tuple-determinant coefficients vary continuously over every topological coefficient ring. -/
theorem determinantMulticoefficient_continuous [TopologicalSpace R] [IsTopologicalRing R]
    (d : σ →₀ ℕ) :
    Continuous (fun A : σ → Matrix ι ι R => MvPolynomial.coeff d (matrixCombinationDeterminant A)) := by
  simp_rw [← determinantMulticoefficientPolynomial_eval]
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro tij
  exact (continuous_apply tij.2.2).comp
    ((continuous_apply tij.2.1).comp (continuous_apply tij.1))

/-- The determinant law constructed from a continuous representation has continuous original multivariable coefficients on every finite tuple of group elements. -/
theorem matrixGroupDeterminantLaw_multicoefficient_continuous
    {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalSpace R] [IsTopologicalRing R]
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) (d : σ →₀ ℕ) :
    Continuous (fun g : σ → G => MvPolynomial.coeff d
      ((matrixGroupDeterminantLaw ρ).eval (MvPolynomial σ R) MvPolynomial.C
        (∑ t, MonoidAlgebra.single (g t) (MvPolynomial.X t)))) := by
  simp_rw [matrixGroupDeterminantLaw_eval, matrixCombinationDeterminant_groupAlgebra]
  apply (determinantMulticoefficient_continuous d).comp
  apply continuous_pi
  intro t
  exact (Units.continuous_val (M := Matrix ι ι R)).comp (hρ.comp (continuous_apply t))

end
end Dubon2026
