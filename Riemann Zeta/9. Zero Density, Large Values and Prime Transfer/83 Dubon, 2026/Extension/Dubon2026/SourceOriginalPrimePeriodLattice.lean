import Dubon2026.SourceOriginalPrimePeriodCoordinates
import Dubon2026.SourceOriginalPeriodLatticeEquality

/-! DUB-17/18 -> full rank-two Hecke algebra realization -> all-prime
period lattice stability. A Gamma translate represents the same actual
place. Apply the proved all-prime Abel comparison to this zero point
divisor: the transformed modular period is zero in the original quotient.
The exact lattice equality then handles every original loop period. This
avoids a separate bad-prime cohomology or scalar-character development.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup KaehlerDifferential
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalPrimePeriodHecke_cusp_generator_mem (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (γ : Gamma0 N) :
    originalPrimePeriodHecke N ell b
        (fun i => sourceWeightTwoPeriodValue (Gamma0 N) (originalRegularCuspEquiv N (b i)) γ) ∈
      pathPeriodLattice N (fun i => (b i).val) := by
  letI : Fact ell.val.Prime := ⟨ell.property⟩
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have he : (fun i => sourceWeightTwoPeriodValue (Gamma0 N) (originalRegularCuspEquiv N (b i)) γ) =
      fun i => sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) (γ.val • I) -
        sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) I := by
    funext i
    rw [original_cusp_primitive_period N]
    ring
  rw [he, originalPrimePeriodHecke_primitive_difference]
  have hp := originalHecke_abel_analytic_difference_all N ell.val b
    (originalAnalyticPlace N I) I (γ.val • I)
  rw [originalAnalyticPlace_smul N γ I, sub_self, map_zero, map_zero, map_zero] at hp
  exact hp.symm

theorem originalPrimePeriodHecke_preserves_path_lattice (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    {v : Fin n → ℂ} (hv : v ∈ pathPeriodLattice N (fun i => (b i).val)) :
    originalPrimePeriodHecke N ell b v ∈ pathPeriodLattice N (fun i => (b i).val) := by
  have hle : originalCuspPeriodLattice N b ≤
      (pathPeriodLattice N (fun i => (b i).val)).comap
        ((originalPrimePeriodHecke N ell b).restrictScalars ℤ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨γ, rfl⟩
    exact originalPrimePeriodHecke_cusp_generator_mem N ell b γ
  apply hle
  rwa [originalCuspPeriodLattice_eq_pathPeriodLattice]

/-- The genuine prime Hecke action on the original path quotient, including bad primes. -/
def originalPrimePeriodQuotientHecke (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) :
    Module.End ℤ ((Fin n → ℂ) ⧸ pathPeriodLattice N (fun i => (b i).val)) :=
  (pathPeriodLattice N (fun i => (b i).val)).mapQ
    (pathPeriodLattice N (fun i => (b i).val))
    ((originalPrimePeriodHecke N ell b).restrictScalars ℤ)
    (fun _ hv => originalPrimePeriodHecke_preserves_path_lattice N ell b hv)

theorem originalPrimePeriodQuotientHecke_mk (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (v : Fin n → ℂ) :
    originalPrimePeriodQuotientHecke N ell b
        ((pathPeriodLattice N (fun i => (b i).val)).mkQ v) =
      (pathPeriodLattice N (fun i => (b i).val)).mkQ (originalPrimePeriodHecke N ell b v) := rfl

end
end Dubon2026.SourceFunctionField.OriginalChart
