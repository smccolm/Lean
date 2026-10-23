import Dubon2026.SourceOriginalPrimePicardCommute
import Dubon2026.SourceOriginalTateRank
import Mathlib.Algebra.FreeAlgebra

/-! DUB-17/18 -> rank-two original Hecke realization -> the genuine
finite integral period-lattice algebra. The original lattice is already
finite free; every prime correspondence preserves it and the restrictions
commute. Integral words therefore give actual operators with no finite
generation, commutativity or lattice-stability premise.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

/-- The integral algebra of all actual prime operators on the original period lattice. -/
def originalFullLatticeHeckeAlgebra {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    Subalgebra ℤ (Module.End ℤ (pathPeriodLattice N (fun i => (b i).val))) :=
  Algebra.adjoin ℤ (Set.range fun ell : Nat.Primes => originalPrimePeriodLatticeHecke N ell b)

theorem originalFullLatticeHeckeAlgebra_commutative {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ell, rfl⟩ _ ⟨q, rfl⟩
    exact (originalPrimePeriodLatticeHecke_commute N ell q b).eq)

private theorem finite_integral_operator_algebra (M : Type*) [AddCommGroup M]
    [Module ℤ M] [Module.Finite ℤ M] (A : Subalgebra ℤ (Module.End ℤ M)) :
    Module.Finite ℤ A := by
  letI : IsNoetherian ℤ M := isNoetherian_of_isNoetherianRing_of_finite ℤ M
  letI : IsNoetherian ℤ (Module.End ℤ M) := by
    convert isNoetherian_linearMap ℤ M M using 1
    exact Subsingleton.elim _ _
  exact Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective

theorem originalFullLatticeHeckeAlgebra_finite {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    Module.Finite ℤ (originalFullLatticeHeckeAlgebra N b) := by
  letI := (original_period_lattice_free_finite_rank N b).2.1
  exact finite_integral_operator_algebra _ (originalFullLatticeHeckeAlgebra N b)

/-- Evaluate an integral prime word on the same actual original path lattice. -/
def originalLatticeHeckeWord {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    FreeAlgebra ℤ Nat.Primes →ₐ[ℤ]
      Module.End ℤ (pathPeriodLattice N (fun i => (b i).val)) :=
  FreeAlgebra.lift ℤ (fun ell => originalPrimePeriodLatticeHecke N ell b)

theorem originalLatticeHeckeWord_generator {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (ell : Nat.Primes) :
    originalLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell) = originalPrimePeriodLatticeHecke N ell b :=
  FreeAlgebra.lift_ι_apply _ ell

theorem originalLatticeHeckeWord_range {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    (originalLatticeHeckeWord N b).range = originalFullLatticeHeckeAlgebra N b :=
  (Algebra.adjoin_range_eq_range_freeAlgebra_lift ℤ (X := Nat.Primes)
    (fun ell : Nat.Primes => originalPrimePeriodLatticeHecke N ell b)).symm

end
end Dubon2026.SourceFunctionField.OriginalChart
