import TaoTrudgianYang2025.SargosPositiveSextupleModel

/-! Orient a genuine sextuple by swapping its triples, retaining the exact source sum norm. -/

noncomputable section

open GafniTao
open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargosSextupleRadius_swap {H : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    sargosSextupleRadius q.swap = sargosSextupleRadius q := by
  exact max_comm _ _

theorem sargosSextupleInterior_swap {H : ℕ} (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    sargosSextupleInterior M q.swap = sargosSextupleInterior M q := by
  simp only [sargosSextupleInterior,sargosSextupleRadius_swap]

theorem sargosQuarticDifference_swap {H : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    sargosQuarticDifference q.swap = -sargosQuarticDifference q := by
  dsimp [sargosQuarticDifference]
  ring

theorem sargosSextuplePhase_swap {H : ℕ} (f : ℝ → ℝ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (m : ℝ) :
    sargosSextuplePhase f q.swap m = -sargosSextuplePhase f q m := by
  dsimp [sargosSextuplePhase,sargosSextupleRemainder]
  push_cast
  ring

theorem sargos_sextuple_sum_norm_swap {H : ℕ} (f : ℝ → ℝ) (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    ‖∑ m ∈ sargosSextupleInterior M q.swap,
      fordAdditiveCharacter (sargosSextuplePhase f q.swap m)‖ =
      ‖∑ m ∈ sargosSextupleInterior M q,
        fordAdditiveCharacter (sargosSextuplePhase f q m)‖ := by
  rw [sargosSextupleInterior_swap]
  simp_rw [sargosSextuplePhase_swap,← conj_fordAdditiveCharacter]
  rw [← map_sum,Complex.norm_conj]

def sargosOrientedSextuple {H : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3 :=
  if 0 ≤ sargosQuarticDifference q then q else q.swap

theorem sargosQuarticDifference_oriented {H : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    sargosQuarticDifference (sargosOrientedSextuple q) = |sargosQuarticDifference q| := by
  unfold sargosOrientedSextuple
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · rw [sargosQuarticDifference_swap,abs_of_neg (lt_of_not_ge h)]

theorem sargosOrientedSextuple_mem_diagonal {H : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hq : q ∈ sargosSquareDiagonal H) :
    sargosOrientedSextuple q ∈ sargosSquareDiagonal H := by
  unfold sargosOrientedSextuple
  split_ifs
  · exact hq
  · simpa only [sargosSquareDiagonal,Finset.mem_filter,Finset.mem_univ,true_and,
      Prod.fst_swap,Prod.snd_swap,eq_comm] using hq

theorem sargosSextupleInterior_oriented {H : ℕ} (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    sargosSextupleInterior M (sargosOrientedSextuple q) = sargosSextupleInterior M q := by
  unfold sargosOrientedSextuple
  split_ifs
  · rfl
  · exact sargosSextupleInterior_swap M q

theorem sargos_sextuple_sum_norm_oriented {H : ℕ} (f : ℝ → ℝ) (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    ‖∑ m ∈ sargosSextupleInterior M (sargosOrientedSextuple q),
      fordAdditiveCharacter (sargosSextuplePhase f (sargosOrientedSextuple q) m)‖ =
      ‖∑ m ∈ sargosSextupleInterior M q,
        fordAdditiveCharacter (sargosSextuplePhase f q m)‖ := by
  unfold sargosOrientedSextuple
  split_ifs
  · rfl
  · exact sargos_sextuple_sum_norm_swap f M q

end TaoTrudgianYang2025
