import Dubon2026.SourceOriginalPeriodRealBasis
import Dubon2026.SourceIntegralWordAdditiveNaturality

/-! DUB-17/18 -> actual rank-two Tate descent -> the full integral
word action on the original real period space. The already proved
prime lattice restrictions extend to all integral words by additive
naturality, preserving the actual original path lattice throughout.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

/-- Integral prime words acting on the original complex period coordinates. -/
def originalPeriodHeckeWord {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    FreeAlgebra ℤ Nat.Primes →ₐ[ℤ] Module.End ℂ (Fin n → ℂ) :=
  FreeAlgebra.lift ℤ (fun ell => originalPrimePeriodHecke N ell b)

theorem originalPeriodHeckeWord_generator {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (ell : Nat.Primes) :
    originalPeriodHeckeWord N b (FreeAlgebra.ι ℤ ell) = originalPrimePeriodHecke N ell b :=
  FreeAlgebra.lift_ι_apply _ ell

theorem originalPeriodHeckeWord_lattice {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (a : FreeAlgebra ℤ Nat.Primes) (x : pathPeriodLattice N (fun i => (b i).val)) :
    (originalLatticeHeckeWord N b a x).val = originalPeriodHeckeWord N b a x.val :=
  sourceHeckeWord_intertwine_addHom
    (fun ell => originalPrimePeriodLatticeHecke N ell b)
    (fun ell => originalPrimePeriodHecke N ell b)
    (pathPeriodLattice N (fun i => (b i).val)).subtype.toAddMonoidHom
    (fun ell y => originalPrimePeriodLatticeHecke_coe N ell b y) a x

theorem originalPeriodHeckeWord_preserves_lattice {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (a : FreeAlgebra ℤ Nat.Primes) {x : Fin n → ℂ}
    (hx : x ∈ pathPeriodLattice N (fun i => (b i).val)) :
    originalPeriodHeckeWord N b a x ∈ pathPeriodLattice N (fun i => (b i).val) := by
  rw [← originalPeriodHeckeWord_lattice N b a ⟨x, hx⟩]
  exact (originalLatticeHeckeWord N b a ⟨x, hx⟩).property

end
end Dubon2026.SourceFunctionField.OriginalChart
