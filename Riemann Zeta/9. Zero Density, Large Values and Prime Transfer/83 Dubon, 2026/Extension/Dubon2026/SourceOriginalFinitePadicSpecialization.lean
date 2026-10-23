import Dubon2026.SourceOriginalPadicEigencharacter
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! DUB-17/18 -> modular residual association -> primitive specialization
of the original Tate Hecke action. The existing common coefficient field
constructs a finite extension of the actual p-adic field and an embedding
of the literal Fourier field. The proved operator character is continuous
in canonical module topologies and retains every original prime value. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b

open scoped IsMulCommutative

theorem originalPadicHecke_finite_specialization (p : ℕ) [Fact p.Prime] {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) :
    letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
    let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[p]
    let T := SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p
    letI : TopologicalSpace T := moduleTopology ℚ_[p] T
    letI : TopologicalSpace E := moduleTopology ℚ_[p] E
    FiniteDimensional ℚ_[p] E ∧
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) (χ : T →ₐ[ℚ_[p]] E),
        Continuous χ ∧ ∀ ell : Nat.Primes,
          χ (SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
            (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell))) =
              τ (sourcePrimitiveFieldCoefficient f ell.val) := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[p]
  let T := SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p
  letI : TopologicalSpace T := moduleTopology ℚ_[p] T
  letI : TopologicalSpace E := moduleTopology ℚ_[p] E
  letI := IsModuleTopology.toContinuousAdd ℚ_[p] E
  let σ : sourcePrimitiveCoefficientField f →ₐ[ℚ] AlgebraicClosure ℚ_[p] := IsAlgClosed.lift
  let τ := commonCoefficientEmbedding (sourcePrimitiveCoefficientField f) ℚ_[p] σ
  let χ := originalPadicHeckeEigencharacter N p b lb f τ.toRingHom
  refine ⟨inferInstance, τ, χ, ?_, ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap χ.toLinearMap
  · exact originalPadicHeckeEigencharacter_prime N p b lb f τ.toRingHom

end
end Dubon2026.SourceFunctionField.OriginalChart
