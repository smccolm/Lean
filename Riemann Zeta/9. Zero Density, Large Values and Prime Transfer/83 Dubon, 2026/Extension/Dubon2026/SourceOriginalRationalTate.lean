import Dubon2026.SourceOriginalTateHeckeMatrices
import Dubon2026.SourceOriginalFullHeckeMatrixRange

/-! DUB-17/18 -> rank-two original rational Tate realization -> rational
coordinates of the literal arithmetic Tate module. Native scalar extension
keeps the exact integral Hecke matrices, so no independent representation
or comparison witness is substituted for the original Picard action. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Matrix
open scoped TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

/-- The rational Tate module of the literal original arithmetic Picard group. -/
abbrev originalRationalTateModule := ℚ_[p] ⊗[ℤ_[p]] TateModule p (originalJZero N)

/-- The original integral Hecke words acting by scalar extension on the rational Tate module. -/
def originalRationalTateHeckeWord :
    FreeAlgebra ℤ Nat.Primes →ₐ[ℤ] Module.End ℚ_[p] (originalRationalTateModule N p) :=
  ((Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p (originalJZero N))).restrictScalars ℤ).comp
    (originalTateHeckeWord N p)

/-- The original rational Tate basis, retaining the integral period indices. -/
def originalRationalTateBasis {n m : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Module.Basis (Fin m) ℚ_[p] (originalRationalTateModule N p) :=
  Algebra.TensorProduct.basis ℚ_[p] (originalTateLatticeBasis N p b P₀ lb)

theorem originalRationalTateBasis_heckeWord {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a : FreeAlgebra ℤ Nat.Primes) :
    LinearMap.toMatrix (originalRationalTateBasis N p b P₀ lb)
        (originalRationalTateBasis N p b P₀ lb) (originalRationalTateHeckeWord N p a) =
      (LinearMap.toMatrix lb lb (originalLatticeHeckeWord N b a)).map
        (Int.cast : ℤ → ℚ_[p]) := by
  change LinearMap.toMatrix
    (Algebra.TensorProduct.basis ℚ_[p] (originalTateLatticeBasis N p b P₀ lb))
    (Algebra.TensorProduct.basis ℚ_[p] (originalTateLatticeBasis N p b P₀ lb))
    ((originalTateHeckeWord N p a).baseChange ℚ_[p]) = _
  have h₁ := LinearMap.toMatrix_baseChange ℚ_[p] (originalTateHeckeWord N p a)
    (originalTateLatticeBasis N p b P₀ lb) (originalTateLatticeBasis N p b P₀ lb)
  have h₂ := congrArg (fun A : Matrix (Fin m) (Fin m) ℤ_[p] =>
    A.map (algebraMap ℤ_[p] ℚ_[p])) (originalTateLatticeBasis_heckeWord N p b P₀ lb a)
  have h₃ : ((LinearMap.toMatrix lb lb (originalLatticeHeckeWord N b a)).map
      (Int.cast : ℤ → ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p]) =
      (LinearMap.toMatrix lb lb (originalLatticeHeckeWord N b a)).map
        (Int.cast : ℤ → ℚ_[p]) := by
    ext i j
    exact map_intCast (algebraMap ℤ_[p] ℚ_[p]) _
  with_reducible exact h₁.trans (h₂.trans h₃)

theorem originalRationalTateBasis_word_coordinates {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a : FreeAlgebra ℤ Nat.Primes) (x : originalRationalTateModule N p) :
    (originalRationalTateBasis N p b P₀ lb).equivFun (originalRationalTateHeckeWord N p a x) =
      (originalLatticeHeckeMatrix N b lb (originalFullLatticeHeckeWord N b a)).map
        (Int.cast : ℤ → ℚ_[p]) *ᵥ (originalRationalTateBasis N p b P₀ lb).equivFun x := by
  have h := (LinearMap.toMatrix_mulVec_repr (originalRationalTateBasis N p b P₀ lb)
    (originalRationalTateBasis N p b P₀ lb) (originalRationalTateHeckeWord N p a) x).symm
  rw [originalRationalTateBasis_heckeWord] at h
  exact h

end
end Dubon2026.SourceFunctionField.OriginalChart
