import TaoTrudgianYang2025.SargosTupleSupport

/-! Exact source support and character phase for square-diagonal sextuple correlations. -/

noncomputable section

open GafniTao
open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

def sargosSextupleRadius {H : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : ℤ :=
  max (sargosTupleRadius q.1) (sargosTupleRadius q.2)

def sargosSextupleInterval {H : ℕ} (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : Finset ℤ :=
  Finset.Icc (sargosSextupleRadius q+1) ((M:ℤ)-sargosSextupleRadius q)

def sargosSextuplePhase {H : ℕ} (f : ℝ → ℝ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (m : ℝ) : ℝ :=
  (((sargosInitialTuplePower 4 q.1-sargosInitialTuplePower 4 q.2:ℤ):ℝ)/12)*
    iteratedDeriv 4 f m+sargosSextupleRemainder f q m

theorem mem_sargosSextupleInterval {H : ℕ} (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (m : ℤ) :
    m ∈ sargosSextupleInterval M q ↔
      m ∈ Finset.Icc (sargosTupleRadius q.1+1) ((M:ℤ)-sargosTupleRadius q.1) ∧
      m ∈ Finset.Icc (sargosTupleRadius q.2+1) ((M:ℤ)-sargosTupleRadius q.2) := by
  simp only [sargosSextupleInterval,sargosSextupleRadius,Finset.mem_Icc]
  omega

theorem sargosSextupleInterval_subset {H : ℕ} (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    sargosSextupleInterval M q ⊆ Finset.Ioc (0:ℤ) M := by
  intro m hm
  have h := (mem_sargosSextupleInterval M q m).mp hm
  have hx := Finset.mem_Icc.mp h.1
  have hr := (sargosTupleRadius_bounds q.1).1
  apply Finset.mem_Ioc.mpr
  constructor <;> omega

theorem sargos_source_sextuple_character {H : ℕ} (f : ℝ → ℝ) (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hq : q ∈ sargosSquareDiagonal H) (m : ℤ) :
    sargosSourceSymmetricTriple (fun n => fordAdditiveCharacter (f n)) M H m q.1*
      conj (sargosSourceSymmetricTriple (fun n => fordAdditiveCharacter (f n)) M H m q.2) =
      if m ∈ sargosSextupleInterval M q
      then fordAdditiveCharacter (sargosSextuplePhase f q m) else 0 := by
  rw [sargosSourceSymmetricTriple_character,sargosSourceSymmetricTriple_character]
  by_cases hm : m ∈ sargosSextupleInterval M q
  · obtain ⟨h1,h2⟩ := (mem_sargosSextupleInterval M q m).mp hm
    rw [if_pos h1,if_pos h2,if_pos hm,conj_fordAdditiveCharacter,← fordAdditiveCharacter_add]
    congr 1
    simpa only [sargosSextuplePhase,sub_eq_add_neg] using sargos_square_diagonal_phase f q hq m
  · have hnot := mt (mem_sargosSextupleInterval M q m).mpr hm
    by_cases h1 : m ∈ Finset.Icc (sargosTupleRadius q.1+1) ((M:ℤ)-sargosTupleRadius q.1)
    · have h2 : m ∉ Finset.Icc (sargosTupleRadius q.2+1) ((M:ℤ)-sargosTupleRadius q.2) :=
        fun h2 => hnot ⟨h1,h2⟩
      simp only [if_pos h1,if_neg h2,if_neg hm,map_zero,mul_zero]
    · simp only [if_neg h1,if_neg hm,zero_mul]

theorem sargos_source_sextuple_sum {H : ℕ} (f : ℝ → ℝ) (M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hq : q ∈ sargosSquareDiagonal H) :
    (∑ m ∈ Finset.Ioc (0:ℤ) M,
      sargosSourceSymmetricTriple (fun n => fordAdditiveCharacter (f n)) M H m q.1*
        conj (sargosSourceSymmetricTriple (fun n => fordAdditiveCharacter (f n)) M H m q.2)) =
      ∑ m ∈ sargosSextupleInterval M q, fordAdditiveCharacter (sargosSextuplePhase f q m) := by
  have he : (Finset.Ioc (0:ℤ) M).filter (fun m => m ∈ sargosSextupleInterval M q) =
      sargosSextupleInterval M q := by
    ext m
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨sargosSextupleInterval_subset M q h,h⟩⟩
  simp_rw [sargos_source_sextuple_character f M q hq]
  rw [← Finset.sum_filter,he]

theorem sargosSourceSextupleCorrelation_eq_phase (f : ℝ → ℝ) (M H : ℕ) :
    sargosSourceSextupleCorrelation (fun n => fordAdditiveCharacter (f n)) M H =
      ∑ q ∈ sargosSquareDiagonal H,
        ‖∑ m ∈ sargosSextupleInterval M q, fordAdditiveCharacter (sargosSextuplePhase f q m)‖ := by
  apply Finset.sum_congr rfl
  intro q hq
  rw [sargos_source_sextuple_sum f M q hq]

theorem sargos_character_sextuple_differencing (f : ℝ → ℝ) {M H : ℕ}
    (hH : 1 ≤ H) (hHM : H ≤ M) :
    ‖∑ m ∈ Finset.Ioc (0:ℤ) M, fordAdditiveCharacter (f m)‖^12 ≤
      1492992*((M:ℝ)/H)^6*(M:ℝ)^6+
      (382205952*(M:ℝ)^11/(H:ℝ)^4)*
        ∑ q ∈ sargosSquareDiagonal H,
          ‖∑ m ∈ sargosSextupleInterval M q, fordAdditiveCharacter (sargosSextuplePhase f q m)‖ := by
  have h := sargos_source_sextuple_differencing (fun n => fordAdditiveCharacter (f n)) hH hHM
  rw [sargosSourceSextupleCorrelation_eq_phase] at h
  simpa [sargos_character_norm] using h

end TaoTrudgianYang2025
