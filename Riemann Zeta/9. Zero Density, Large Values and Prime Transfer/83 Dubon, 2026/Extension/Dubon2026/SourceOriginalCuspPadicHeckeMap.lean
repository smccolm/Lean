import Dubon2026.SourceOriginalPadicEigencharacter
import Dubon2026.SourceExplicitHeckeMatrixDescent
import Dubon2026.SourcePrimitiveTensorOperators

/-! DUB-17/18 -> nonzero rank-two primitive Tate image. The same integral
cusp Hecke algebra maps into the original generated p-adic matrix algebra,
and its prescribed character retains every original integral eigenvalue. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b
open scoped IsMulCommutative

/-- The original integral cusp operators in the actual generated p-adic Hecke algebra. -/
def originalCuspPadicHeckeMap {n m : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    sourceOriginalIntegralHeckeAlgebra N 2 →+*
      SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p :=
  (SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p).comp
    (originalLatticeCuspHeckeEquiv N b).symm.toRingHom

theorem originalCuspPadicHeckeMap_word {n m : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (a : FreeAlgebra ℤ Nat.Primes) :
    originalCuspPadicHeckeMap N p b lb (sourceIntegralCuspHeckeWord N a) =
      SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
        (originalFullLatticeHeckeWord N b a) := by
  exact congrArg (SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p)
    ((originalLatticeCuspHeckeEquiv N b).symm_apply_eq.mpr
      (originalLatticeCuspHeckeEquiv_word N b a).symm)

theorem originalCuspPadicHeckeMap_prime {n m : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) (ell : Nat.Primes) :
    originalCuspPadicHeckeMap N p b lb
      (primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩) =
      SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
        (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell)) := by
  have h : primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩ =
      sourceIntegralCuspHeckeWord N (FreeAlgebra.ι ℤ ell) :=
    Subtype.ext (sourceIntegralCuspHeckeWord_prime N ell).symm
  exact (congrArg (originalCuspPadicHeckeMap N p b lb) h).trans
    (originalCuspPadicHeckeMap_word N p b lb (FreeAlgebra.ι ℤ ell))

theorem originalCuspPadicHeckeMap_character {E : Type*} [CommRing E] [Algebra ℚ_[p] E]
    {n m : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (t : sourceOriginalIntegralHeckeAlgebra N 2) :
    originalPadicHeckeEigencharacter N p b lb f τ (originalCuspPadicHeckeMap N p b lb t) =
      τ (sourcePrimitiveFieldHeckeCharacter f t) := by
  change originalPadicHeckeEigencharacter N p b lb f τ
    (SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
      ((originalLatticeCuspHeckeEquiv N b).symm t)) = _
  rw [originalPadicHeckeEigencharacter_integral]
  change τ (sourcePrimitiveFieldHeckeCharacter f
    (originalLatticeCuspHeckeEquiv N b ((originalLatticeCuspHeckeEquiv N b).symm t))) = _
  rw [RingEquiv.apply_symm_apply]

theorem originalCuspPadicHeckeMap_generates {n m : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Algebra.adjoin ℚ_[p] (Set.range fun ell : Nat.Primes =>
      originalCuspPadicHeckeMap N p b lb
        (primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩)) = ⊤ := by
  have h := funext (originalCuspPadicHeckeMap_prime N p b lb)
  exact (congrArg (fun g : Nat.Primes →
    SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p =>
      Algebra.adjoin ℚ_[p] (Set.range g)) h).trans
    (SourceHeckeMatrixDescent.explicit_descent_prime_generators
      (originalLatticeHeckeMatrix N b lb) p (originalFullLatticeHeckeWord N b)
      (originalFullLatticeHeckeWord_surjective N b))

end
end Dubon2026.SourceFunctionField.OriginalChart
