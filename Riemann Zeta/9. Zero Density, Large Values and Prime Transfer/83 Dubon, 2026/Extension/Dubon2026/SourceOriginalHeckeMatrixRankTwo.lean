import Dubon2026.SourceOriginalHeckeMatrixRank
import Dubon2026.SourceOriginalCuspRealCoordinates
import Dubon2026.SourceHeckeMatrixPadicRankTwo

/-! DUB-17/18 -> original rational Tate rank-two realization -> close
the actual integral matrix descent. All inputs of the determinant
argument are now proved for the original lattice Hecke algebra: its
real matrix action, two real generators and exact twice-rank identity.
The original rational Tate coordinate comparison remains the next step.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Matrix
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b

open scoped IsMulCommutative in
theorem originalFullHecke_matrix_rankTwo (p : ℕ) [Fact p.Prime] {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra ℚ_[p] T)
      (φ : originalFullLatticeHeckeAlgebra N b →+* T)
      (e : (Fin m → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 → T)),
      Algebra.adjoin ℚ_[p] (Set.range φ) = ⊤ ∧
      ∀ (t : originalFullLatticeHeckeAlgebra N b) (v : Fin m → ℚ_[p]),
        e ((originalLatticeHeckeMatrix N b lb t).map (Int.cast : ℤ → ℚ_[p]) *ᵥ v) =
          φ t • e v :=
  SourceHeckeMatrixDescent.descent (originalLatticeHeckeMatrix N b lb) p
    (originalFullHecke_matrix_rank_twice N b lb)
    (originalFullHecke_real_matrix_two_generators N b lb)

end
end Dubon2026.SourceFunctionField.OriginalChart
