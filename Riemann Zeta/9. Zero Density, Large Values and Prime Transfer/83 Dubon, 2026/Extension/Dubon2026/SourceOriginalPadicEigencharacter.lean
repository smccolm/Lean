import Dubon2026.SourceOriginalLatticeEigencharacter
import Dubon2026.SourceMatrixAlgebraSpecialization
import Dubon2026.SourceHeckeMatrixPadicAlgebra

/-! DUB-17/18 -> modular Galois association -> specialize the actual
p-adic Hecke algebra to the prescribed primitive coefficient embedding.
Its integral matrix action is faithful by the actual lattice basis. The
native tensor presentation therefore extends the constructed integral
eigencharacter, with the original prime Fourier values. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

theorem originalLatticeHeckeMatrix_injective {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Function.Injective (originalLatticeHeckeMatrix N b lb) := by
  intro a c h
  apply Subtype.ext
  exact (LinearMap.toMatrixAlgEquiv lb).injective h

private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b

open scoped IsMulCommutative

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [CommRing E] [Algebra ℚ_[p] E]

/-- The prescribed primitive eigencharacter on the actual generated p-adic matrix algebra. -/
def originalPadicHeckeEigencharacter {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E) :
    SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p →ₐ[ℚ_[p]] E :=
  integralMatrixSpecialization (originalLatticeHeckeMatrix N b lb) ℚ_[p]
    (originalLatticeHeckeMatrix_injective N b lb)
    (τ.comp (originalLatticeEigencharacter N b f))

theorem originalPadicHeckeEigencharacter_integral {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (t : originalFullLatticeHeckeAlgebra N b) :
    originalPadicHeckeEigencharacter N p b lb f τ
      (SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p t) =
        τ (originalLatticeEigencharacter N b f t) :=
  integralMatrixSpecialization_generator (originalLatticeHeckeMatrix N b lb) ℚ_[p]
    (originalLatticeHeckeMatrix_injective N b lb)
    (τ.comp (originalLatticeEigencharacter N b f)) t

theorem originalPadicHeckeEigencharacter_prime {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (ell : Nat.Primes) :
    originalPadicHeckeEigencharacter N p b lb f τ
      (SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
        (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell))) =
          τ (sourcePrimitiveFieldCoefficient f ell.val) :=
  (originalPadicHeckeEigencharacter_integral N p b lb f τ _).trans
    (congrArg τ (originalLatticeEigencharacter_prime N b f ell))

end
end Dubon2026.SourceFunctionField.OriginalChart
