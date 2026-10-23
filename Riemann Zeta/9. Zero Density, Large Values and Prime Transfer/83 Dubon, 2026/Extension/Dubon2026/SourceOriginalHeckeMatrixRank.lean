import Dubon2026.SourceOriginalCuspRealHeckeMatrix
import Dubon2026.SourceWeightTwoRealHeckeRank
import Dubon2026.SourceHeckeMatrixRealRank

/-! DUB-17/18 -> original rank-two matrix descent -> its exact rank
hypothesis. The faithful cusp-to-period matrix map identifies the full
real operator span with the actual integral lattice matrix span. Rational
and real matrix rank agree, while the original lattice rank is twice the
cusp dimension. These are proved for the actual original operators.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "S" => CuspForm (Gamma0 N) 2

theorem originalFullHecke_real_matrix_finrank {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range
      (fun t : originalFullLatticeHeckeAlgebra N b =>
        (originalLatticeHeckeMatrix N b lb t).map (Int.cast : ℤ → ℝ)))) =
      Module.finrank ℂ S := by
  let Ψ := originalCuspRealHeckeMatrix N b lb
  let P := Submodule.span ℝ
    (sourceOriginalIntegralHeckeAlgebra N 2 : Set (Module.End ℂ S))
  have hspan : Submodule.span ℝ (Set.range
      (fun t : sourceOriginalIntegralHeckeAlgebra N 2 => Ψ t.val)) = P.map Ψ := by
    rw [Submodule.map_span, Set.image_eq_range]
    rfl
  rw [← originalCuspRealHeckeMatrix_range N b lb, hspan]
  exact (Submodule.equivMapOfInjective Ψ (originalCuspRealHeckeMatrix_injective N b lb)
    P).finrank_eq.symm.trans (sourceWeightTwoRealHecke_finrank N)

private local instance {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    IsMulCommutative (originalFullLatticeHeckeAlgebra N b) :=
  originalFullLatticeHeckeAlgebra_commutative N b

open scoped IsMulCommutative in
theorem originalFullHecke_rational_matrix_finrank {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    SourceHeckeMatrixDescent.g (originalLatticeHeckeMatrix N b lb) = Module.finrank ℂ S := by
  change Module.finrank ℚ (Submodule.span ℚ (Set.range
    (SourceHeckeMatrixDescent.MK (originalLatticeHeckeMatrix N b lb) ℚ))) = _
  rw [← SourceHeckeMatrixDescent.finrank_real_span_eq
    (SourceHeckeMatrixDescent.MK (originalLatticeHeckeMatrix N b lb) ℚ)]
  exact originalFullHecke_real_matrix_finrank N b lb

open scoped IsMulCommutative in
theorem originalFullHecke_matrix_rank_twice {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V)
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    2 * SourceHeckeMatrixDescent.g (originalLatticeHeckeMatrix N b lb) = m := by
  rw [originalFullHecke_rational_matrix_finrank N b lb]
  have hc : Module.finrank ℂ S = n :=
    (Module.finrank_eq_card_basis (b.map (originalRegularCuspEquiv N))).trans
      (Fintype.card_fin n)
  have hl : Module.finrank ℤ (pathPeriodLattice N (fun i => (b i).val)) = m :=
    (Module.finrank_eq_card_basis lb).trans (Fintype.card_fin m)
  have hr := (original_period_lattice_free_finite_rank N b).2.2
  rw [hc]
  exact hr.symm.trans hl

end
end Dubon2026.SourceFunctionField.OriginalChart
