import Dubon2026.SourceOriginalPeriodHeckeWords
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! DUB-17/18 -> original rank-two Tate descent -> exact integral and
real matrices of the same original lattice action. The native ZLattice
coordinate formula proves equality of matrices after coefficient change;
the original all-prime word and lattice compatibility are consumed here.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

/-- Integer matrices of the genuine full original lattice Hecke algebra. -/
def originalLatticeHeckeMatrix {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    originalFullLatticeHeckeAlgebra N b →+* Matrix ι ι ℤ :=
  (LinearMap.toMatrixAlgEquiv lb).toRingHom.comp
    (originalFullLatticeHeckeAlgebra N b).val.toRingHom

/-- Real matrices of actual complex-linear period operators in the original lattice basis. -/
def originalPeriodRealMatrix {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (T : Module.End ℂ (Fin n → ℂ)) : Matrix ι ι ℝ :=
  LinearMap.toMatrix (originalPeriodRealBasis N b lb) (originalPeriodRealBasis N b lb)
    (T.restrictScalars ℝ)

theorem originalPeriodRealMatrix_integral {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (T : Module.End ℂ (Fin n → ℂ))
    (u : Module.End ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (hu : ∀ x, (u x).val = T x.val) :
    originalPeriodRealMatrix N b lb T =
      (LinearMap.toMatrix lb lb u).map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [originalPeriodRealMatrix, LinearMap.toMatrix_apply,
    LinearMap.restrictScalars_apply, Matrix.map_apply]
  calc
    _ = (originalPeriodRealBasis N b lb).repr (T (lb j).val) i :=
      congrArg (fun x => (originalPeriodRealBasis N b lb).repr (T x) i)
        (originalPeriodRealBasis_apply N b lb j)
    _ = (originalPeriodRealBasis N b lb).repr (u (lb j)).val i :=
      congrArg (fun x => (originalPeriodRealBasis N b lb).repr x i) (hu (lb j)).symm
    _ = _ := originalPeriodRealBasis_repr N b lb (u (lb j)) i

theorem originalPeriodRealMatrix_heckeWord {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a : FreeAlgebra ℤ Nat.Primes) :
    originalPeriodRealMatrix N b lb (originalPeriodHeckeWord N b a) =
      (LinearMap.toMatrix lb lb (originalLatticeHeckeWord N b a)).map (Int.cast : ℤ → ℝ) :=
  originalPeriodRealMatrix_integral N b lb _ _ (originalPeriodHeckeWord_lattice N b a)

end
end Dubon2026.SourceFunctionField.OriginalChart
