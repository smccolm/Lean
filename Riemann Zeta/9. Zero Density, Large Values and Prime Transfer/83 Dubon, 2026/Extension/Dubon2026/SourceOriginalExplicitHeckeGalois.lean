import Dubon2026.SourceOriginalExplicitHeckeRankTwo
import Dubon2026.SourceOriginalContinuousRankTwoGalois
import Dubon2026.SourceContinuousHeckeCoordinateConsumer

/-! DUB-17/18 -> prescribed primitive Galois specialization -> retain
the actual generated p-adic algebra through the continuous rank-two
arithmetic action. Existing prime commutation proves coefficient linearity;
the already proved integral Tate continuity supplies the topology. -/
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

theorem originalRationalTate_explicit_continuous_galois {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    let T := SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p
    let χ := fun ell : Nat.Primes =>
      SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
        (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell))
    ∃ (e : originalRationalTateModule N p ≃ₗ[ℚ_[p]] (Fin 2 → T))
      (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) T),
      (∀ (ell : Nat.Primes) (x : originalRationalTateModule N p),
        e ((TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange ℚ_[p] x) =
          (fun i => χ ell * e x i)) ∧
      (letI : TopologicalSpace T := moduleTopology ℚ_[p] T
       Continuous ρ) ∧
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N p),
        (ρ σ).val *ᵥ e x = e (originalRationalTateGaloisRep N p σ x) := by
  let T := SourceHeckeMatrixDescent.Tp (originalLatticeHeckeMatrix N b lb) p
  letI : IsMulCommutative T :=
    SourceHeckeMatrixDescent.Tp_commutative (originalLatticeHeckeMatrix N b lb) p
  letI : CommRing T := inferInstance
  let χ := fun ell : Nat.Primes =>
    SourceHeckeMatrixDescent.φ (originalLatticeHeckeMatrix N b lb) p
      (originalFullLatticeHeckeWord N b (FreeAlgebra.ι ℤ ell))
  have h := originalRationalTate_explicit_prime_rankTwo N p b P₀ lb
  let u : Nat.Primes → Module.End ℚ_[p] (originalRationalTateModule N p) := fun ell =>
    (TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange ℚ_[p]
  letI : Module.Finite ℚ_[p] (originalRationalTateModule N p) := originalRationalTate_finite N p
  letI : TopologicalSpace (originalRationalTateModule N p) :=
    moduleTopology ℚ_[p] (originalRationalTateModule N p)
  letI : TopologicalSpace T := moduleTopology ℚ_[p] T
  exact exists_continuous_hecke_coordinate_rep χ h.1 u h.2
    (originalRationalTateGaloisRep N p) (originalRationalTateGaloisRep_prime_commute N p)
    (originalRationalTateGalois_all_continuous_apply N p)

end
end Dubon2026.SourceFunctionField.OriginalChart
