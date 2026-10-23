import Dubon2026.SourceOriginalTateHeckeWords
import Dubon2026.SourceTateBasisConjugation

/-! DUB-17/18 -> rank-two original rational Tate realization -> actual
integral Tate matrices. Transporting the original lattice basis through
the proved period equivalence retains every integral Hecke word exactly. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
open scoped TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

/-- The genuine arithmetic Tate basis obtained from the original integral period basis. -/
def originalTateLatticeBasis {n m : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Module.Basis (Fin m) ℤ_[p] (TateModule p (originalJZero N)) :=
  (Algebra.TensorProduct.basis ℤ_[p] lb).map
    (originalTatePeriodTensorEquiv N p b P₀ lb).symm

theorem originalTateLatticeBasis_eq {n m : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    originalTateLatticeBasis N p b P₀ lb =
      (Algebra.TensorProduct.basis ℤ_[p] lb).map
        (originalTatePeriodTensorEquiv N p b P₀ lb).symm := rfl

theorem originalTateLatticeBasis_heckeWord {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a : FreeAlgebra ℤ Nat.Primes) :
    LinearMap.toMatrix (originalTateLatticeBasis N p b P₀ lb)
        (originalTateLatticeBasis N p b P₀ lb) (originalTateHeckeWord N p a) =
      (LinearMap.toMatrix lb lb (originalLatticeHeckeWord N b a)).map
        (Int.cast : ℤ → ℤ_[p]) := by
  unfold originalTateLatticeBasis
  have h := tate_matrix_transport p (M := originalJZero N)
    (L := pathPeriodLattice N (fun i => (b i).val))
    (originalTatePeriodTensorEquiv N p b P₀ lb) lb
    (originalTateHeckeWord N p a) (originalLatticeHeckeWord N b a)
    (originalTatePeriodTensorEquiv_heckeWord N p b P₀ lb a)
  with_reducible exact h

end
end Dubon2026.SourceFunctionField.OriginalChart
