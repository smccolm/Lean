import Dubon2026.SourceOriginalRationalTate
import Dubon2026.SourceOriginalHeckeMatrixRankTwo

/-! DUB-17/18 -> modular residual association -> the original rational
Tate rank-two Hecke realization. Compose the actual integral Tate basis
comparison with the already proved matrix descent, retaining every prime
word and its literal Picard action. The bases here are genuine original
bases; the next prime consumer constructs them from the proved finiteness. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b

open scoped IsMulCommutative in
theorem originalRationalTate_heckeWord_rankTwo {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra ℚ_[p] T)
      (φ : originalFullLatticeHeckeAlgebra N b →+* T)
      (e : originalRationalTateModule N p ≃ₗ[ℚ_[p]] (Fin 2 → T)),
      Algebra.adjoin ℚ_[p] (Set.range φ) = ⊤ ∧
      ∀ (a : FreeAlgebra ℤ Nat.Primes) (x : originalRationalTateModule N p),
        e (originalRationalTateHeckeWord N p a x) =
          φ (originalFullLatticeHeckeWord N b a) • e x := by
  exact rankTwo_transfer_coordinates
    (fun t : originalFullLatticeHeckeAlgebra N b =>
      (originalLatticeHeckeMatrix N b lb t).map (Int.cast : ℤ → ℚ_[p]))
    (originalFullLatticeHeckeWord N b) (originalRationalTateHeckeWord N p)
    (originalRationalTateBasis N p b P₀ lb).equivFun
    (originalRationalTateBasis_word_coordinates N p b P₀ lb)
    (originalFullHecke_matrix_rankTwo N p b lb)

end
end Dubon2026.SourceFunctionField.OriginalChart
