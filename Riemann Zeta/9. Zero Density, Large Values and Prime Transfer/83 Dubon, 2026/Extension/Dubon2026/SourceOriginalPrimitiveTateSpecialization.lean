import Dubon2026.SourceOriginalExplicitHeckeGalois
import Dubon2026.SourceOriginalFinitePadicSpecialization
import Dubon2026.SourcePrimitiveCoefficientGaloisConsumer

/-! DUB-17/18 -> modular residual association -> specialize the actual
rank-two Tate representation at the prescribed primitive eigenform. The
constructed coefficient map carries every literal Hecke operator to the
original Fourier eigenvalue and intertwines the actual arithmetic action.
Its image spans the two-dimensional coefficient space. Frobenius identities,
inertia and the residual association remain separate obligations. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Matrix
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "Qbar" => AlgebraicClosure ℚ

private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b
private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

open scoped IsMulCommutative

theorem originalPrimitiveTate_specialization_of_basis {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) :
    letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
    let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[p]
    letI : TopologicalSpace E := moduleTopology ℚ_[p] E
    ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
      (π : originalRationalTateModule N p →ₗ[ℚ_[p]] (Fin 2 → E))
      (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E),
      Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
      (∀ (ell : Nat.Primes) (x : originalRationalTateModule N p),
        π ((TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange ℚ_[p] x) =
          (fun i => τ (sourcePrimitiveFieldCoefficient f ell.val) * π x i)) ∧
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N p),
        (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N p σ x) := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[p]
  let T := SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p
  letI : IsMulCommutative T :=
    SourceHeckeMatrixDescent.Tp_commutative (originalLatticeHeckeMatrix N b lb) p
  letI : CommRing T := inferInstance
  letI : TopologicalSpace T := moduleTopology ℚ_[p] T
  letI : TopologicalSpace E := moduleTopology ℚ_[p] E
  exact specialize_continuous_rankTwo_hecke (K := ℚ_[p]) (T := T) (E := E)
    (fun ell : Nat.Primes => SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
      (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell)))
    (fun ell : Nat.Primes => sourcePrimitiveFieldCoefficient f ell.val)
    (fun ell : Nat.Primes =>
      (TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange ℚ_[p])
    (originalRationalTateGaloisRep N p)
    (originalRationalTate_explicit_continuous_galois N p b P₀ lb)
    (originalPadicHecke_finite_specialization N p b lb f).2

end
end Dubon2026.SourceFunctionField.OriginalChart
