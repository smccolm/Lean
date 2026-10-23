import Dubon2026.SourceOriginalPeriodHeckeCoordinates
import Dubon2026.SourceOriginalPeriodLatticeEquality

/-! DUB-17/18 -> original Jacobian Tate Hecke realization -> period
quotient Hecke action. The existing scalar Hecke-character formula sends
each modular period generator to a finite integer sum of such generators.
The proved equality of the two genuine lattices then discharges stability
of the original path-period lattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup KaehlerDifferential
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]

private local instance {N : ℕ} (ell : sourceBinaryHeckePrime N) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

theorem originalPeriodHecke_cusp_generator_mem (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    (γ : Gamma0 N) :
    originalPeriodHecke N ell b
        (fun i => sourceWeightTwoPeriodValue (Gamma0 N) (originalRegularCuspEquiv N (b i)) γ) ∈
      originalCuspPeriodLattice N b := by
  letI := sourceHeckeUpperFintype N ell.val
  let V := fun g : Gamma0 N =>
    fun i => sourceWeightTwoPeriodValue (Gamma0 N) (originalRegularCuspEquiv N (b i)) g
  have hV : ∀ g, V g ∈ originalCuspPeriodLattice N b :=
    fun g => Submodule.subset_span ⟨g, rfl⟩
  have he : originalPeriodHecke N ell b (V γ) =
      ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
        V (sourceHeckeConjugation ell.property.1
          (cosetTransition (heckeUpperSubgroup N ell.val) γ q)) := by
    rw [originalPeriodHecke_cusp_period]
    funext i
    rw [sourceWeightTwoPeriodValue_hecke, sourceWeightTwoHeckeHom_apply]
    simp only [Finset.sum_apply]
    rfl
  change originalPeriodHecke N ell b (V γ) ∈ _
  rw [he]
  exact (originalCuspPeriodLattice N b).sum_mem fun q _ => hV _

theorem originalPeriodHecke_preserves_cusp_lattice (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    {v : Fin n → ℂ} (hv : v ∈ originalCuspPeriodLattice N b) :
    originalPeriodHecke N ell b v ∈ originalCuspPeriodLattice N b := by
  have hle : originalCuspPeriodLattice N b ≤
      (originalCuspPeriodLattice N b).comap ((originalPeriodHecke N ell b).restrictScalars ℤ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨γ, rfl⟩
    exact originalPeriodHecke_cusp_generator_mem N ell b γ
  exact hle hv

theorem originalPeriodHecke_preserves_path_lattice (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    {v : Fin n → ℂ} (hv : v ∈ pathPeriodLattice N (fun i => (b i).val)) :
    originalPeriodHecke N ell b v ∈ pathPeriodLattice N (fun i => (b i).val) := by
  rw [← originalCuspPeriodLattice_eq_pathPeriodLattice] at hv ⊢
  exact originalPeriodHecke_preserves_cusp_lattice N ell b hv

/-- Hecke endomorphism of the actual original path-period quotient. -/
def originalPeriodQuotientHecke (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ))) :
    Module.End ℤ ((Fin n → ℂ) ⧸ pathPeriodLattice N (fun i => (b i).val)) :=
  (pathPeriodLattice N (fun i => (b i).val)).mapQ
    (pathPeriodLattice N (fun i => (b i).val))
    ((originalPeriodHecke N ell b).restrictScalars ℤ)
    (fun _ hv => originalPeriodHecke_preserves_path_lattice N ell b hv)

theorem originalPeriodQuotientHecke_mk (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    (v : Fin n → ℂ) :
    originalPeriodQuotientHecke N ell b ((pathPeriodLattice N (fun i => (b i).val)).mkQ v) =
      (pathPeriodLattice N (fun i => (b i).val)).mkQ (originalPeriodHecke N ell b v) := rfl

end
end Dubon2026.SourceFunctionField.OriginalChart
