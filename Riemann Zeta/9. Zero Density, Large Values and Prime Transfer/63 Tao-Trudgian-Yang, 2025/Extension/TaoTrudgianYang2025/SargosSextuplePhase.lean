import TaoTrudgianYang2025.SargosSextupleRemainder

/-! Exact cancellation of the quadratic term in an actual square-diagonal sextuple phase. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosSymmetricTuplePhase {H : ℕ} (f : ℝ → ℝ)
    (t : SargosInitialMomentTuple H 3) (m : ℝ) : ℝ :=
  ∑ i, (f (m+((t i:ℤ):ℝ))+f (m-((t i:ℤ):ℝ)))

theorem sargosSymmetricTuplePhase_taylor {H : ℕ} (f : ℝ → ℝ)
    (t : SargosInitialMomentTuple H 3) (m : ℝ) :
    sargosSymmetricTuplePhase f t m =
      6*f m+iteratedDeriv 2 f m*(sargosInitialTuplePower 2 t:ℝ)+
        (iteratedDeriv 4 f m/12)*(sargosInitialTuplePower 4 t:ℝ)+
        sargosTupleRemainder f t m := by
  have hi (i : Fin 3) := sargos_symmetric_taylor_identity f m ((t i:ℤ):ℝ)
  unfold sargosSymmetricTuplePhase
  simp_rw [hi]
  simp only [Finset.sum_add_distrib,sargosTupleRemainder,sargosInitialTuplePower,
    Int.cast_sum,Int.cast_pow]
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_div]
  simp
  ring

theorem sargos_square_diagonal_phase {H : ℕ} (f : ℝ → ℝ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hq : q ∈ sargosSquareDiagonal H) (m : ℝ) :
    sargosSymmetricTuplePhase f q.1 m-sargosSymmetricTuplePhase f q.2 m =
      (((sargosInitialTuplePower 4 q.1-sargosInitialTuplePower 4 q.2:ℤ):ℝ)/12)*
        iteratedDeriv 4 f m+sargosSextupleRemainder f q m := by
  have he := (Finset.mem_filter.mp hq).2
  rw [sargosSymmetricTuplePhase_taylor,sargosSymmetricTuplePhase_taylor,he]
  simp only [Int.cast_sub,sargosSextupleRemainder]
  ring

end TaoTrudgianYang2025
