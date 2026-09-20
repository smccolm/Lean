import TaoTrudgianYang2025.GeneratedCertificates

/-!
# Generated additive-energy certificates

This module consumes the nine exact clauses emitted from the frozen ANTEDB
blueprint. It checks that every interval is ordered and every generated
rational-function denominator is strictly positive throughout that interval.
These are finite certificate facts, not the analytic energy estimates.
-/

namespace TaoTrudgianYang2025

/-- Every rational function in a generated energy clause has a positive
denominator throughout the clause's closed interval. -/
def EnergyClauseDenominatorsPositive (clause : GeneratedEnergyClause) : Prop :=
  clause.lower ≤ clause.upper ∧
    ∀ bound ∈ clause.bounds, ∀ sigma : ℝ,
      (clause.lower : ℝ) ≤ sigma → sigma ≤ (clause.upper : ℝ) →
        0 < (bound.denominatorSlope : ℝ) * sigma +
          bound.denominatorConstant

theorem generatedEnergyClause1_denominatorsPositive :
    EnergyClauseDenominatorsPositive generatedEnergyClause1 := by
  constructor
  · norm_num [generatedEnergyClause1]
  · intro bound hbound sigma hLower hUpper
    simp only [generatedEnergyClause1, List.mem_cons, List.not_mem_nil, or_false] at hbound
    rcases hbound with rfl | rfl
    all_goals norm_num [generatedEnergyClause1] at hLower hUpper ⊢; nlinarith

theorem generatedEnergyClause2_denominatorsPositive :
    EnergyClauseDenominatorsPositive generatedEnergyClause2 := by
  constructor
  · norm_num [generatedEnergyClause2]
  · intro bound hbound sigma hLower hUpper
    simp only [generatedEnergyClause2, List.mem_cons, List.not_mem_nil, or_false] at hbound
    rcases hbound with rfl | rfl
    all_goals norm_num [generatedEnergyClause2] at hLower hUpper ⊢; nlinarith

theorem generatedEnergyClause3_denominatorsPositive :
    EnergyClauseDenominatorsPositive generatedEnergyClause3 := by
  constructor
  · norm_num [generatedEnergyClause3]
  · intro bound hbound sigma hLower hUpper
    simp only [generatedEnergyClause3, List.mem_cons, List.not_mem_nil, or_false] at hbound
    rcases hbound with rfl | rfl | rfl
    all_goals norm_num [generatedEnergyClause3] at hLower hUpper ⊢; nlinarith

theorem generatedEnergyClause4_denominatorsPositive :
    EnergyClauseDenominatorsPositive generatedEnergyClause4 := by
  constructor
  · norm_num [generatedEnergyClause4]
  · intro bound hbound sigma hLower hUpper
    simp only [generatedEnergyClause4, List.mem_cons, List.not_mem_nil, or_false] at hbound
    rcases hbound with rfl | rfl
    all_goals norm_num [generatedEnergyClause4] at hLower hUpper ⊢; nlinarith

theorem generatedEnergyClause5_denominatorsPositive :
    EnergyClauseDenominatorsPositive generatedEnergyClause5 := by
  constructor
  · norm_num [generatedEnergyClause5]
  · intro bound hbound sigma hLower hUpper
    simp only [generatedEnergyClause5, List.mem_cons, List.not_mem_nil, or_false] at hbound
    rcases hbound with rfl | rfl | rfl
    all_goals norm_num [generatedEnergyClause5] at hLower hUpper ⊢; nlinarith

theorem generatedEnergyClause6_denominatorsPositive :
    EnergyClauseDenominatorsPositive generatedEnergyClause6 := by
  constructor
  · norm_num [generatedEnergyClause6]
  · intro bound hbound sigma hLower hUpper
    simp only [generatedEnergyClause6, List.mem_cons, List.not_mem_nil, or_false] at hbound
    rcases hbound with rfl | rfl
    all_goals norm_num [generatedEnergyClause6] at hLower hUpper ⊢; nlinarith

theorem generatedEnergyClause7_denominatorsPositive :
    EnergyClauseDenominatorsPositive generatedEnergyClause7 := by
  constructor
  · norm_num [generatedEnergyClause7]
  · intro bound hbound sigma hLower hUpper
    simp only [generatedEnergyClause7, List.mem_cons, List.not_mem_nil, or_false] at hbound
    rcases hbound with rfl | rfl
    all_goals norm_num [generatedEnergyClause7] at hLower hUpper ⊢; nlinarith

theorem generatedEnergyClause8_denominatorsPositive :
    EnergyClauseDenominatorsPositive generatedEnergyClause8 := by
  constructor
  · norm_num [generatedEnergyClause8]
  · intro bound hbound sigma hLower hUpper
    simp only [generatedEnergyClause8, List.mem_cons, List.not_mem_nil, or_false] at hbound
    rcases hbound with rfl | rfl
    all_goals norm_num [generatedEnergyClause8] at hLower hUpper ⊢; nlinarith

theorem generatedEnergyClause9_denominatorsPositive :
    EnergyClauseDenominatorsPositive generatedEnergyClause9 := by
  constructor
  · norm_num [generatedEnergyClause9]
  · intro bound hbound sigma hLower hUpper
    simp only [generatedEnergyClause9, List.mem_cons, List.not_mem_nil, or_false] at hbound
    rcases hbound with rfl | rfl
    all_goals norm_num [generatedEnergyClause9] at hLower hUpper ⊢; nlinarith

/-- The complete generated nine-clause table passes the denominator-sign
certificate check. -/
theorem generatedEnergyClauses_denominatorsPositive :
    ∀ clause ∈ generatedEnergyClauses,
      EnergyClauseDenominatorsPositive clause := by
  intro clause hclause
  simp only [generatedEnergyClauses, List.mem_cons, List.not_mem_nil, or_false] at hclause
  rcases hclause with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact generatedEnergyClause1_denominatorsPositive
  · exact generatedEnergyClause2_denominatorsPositive
  · exact generatedEnergyClause3_denominatorsPositive
  · exact generatedEnergyClause4_denominatorsPositive
  · exact generatedEnergyClause5_denominatorsPositive
  · exact generatedEnergyClause6_denominatorsPositive
  · exact generatedEnergyClause7_denominatorsPositive
  · exact generatedEnergyClause8_denominatorsPositive
  · exact generatedEnergyClause9_denominatorsPositive

end TaoTrudgianYang2025
