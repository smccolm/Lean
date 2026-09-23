import TaoTrudgianYang2025.SargosPhysicalRemainderExtension
import TaoTrudgianYang2025.SargosInteriorDifferencing

/-! The actual interior sums are unchanged by the constructed smooth remainder extension. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosExtendedSextuplePhase {H : ℕ} (f : ℝ → ℝ) (M Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (m : ℝ) : ℝ :=
  (((sargosInitialTuplePower 4 q.1-sargosInitialTuplePower 4 q.2:ℤ):ℝ)/12)*
    iteratedDeriv 4 f m+sargosPhysicalExtendedRemainder f M Q q m

def sargosExtendedSextupleCorrelation (f : ℝ → ℝ) (M H Q : ℕ) : ℝ :=
  ∑ q ∈ sargosSquareDiagonal H,
    ‖∑ m ∈ sargosSextupleInterior M q,
      fordAdditiveCharacter (sargosExtendedSextuplePhase f M Q q m)‖

theorem sargosExtendedSextuplePhase_agrees {H M : ℕ} (f : ℝ → ℝ)
    (hM : 1 ≤ M) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    {m : ℤ} (hm : m ∈ sargosSextupleInterior M q) :
    sargosExtendedSextuplePhase f M Q q m = sargosSextuplePhase f q m := by
  unfold sargosExtendedSextuplePhase sargosSextuplePhase
  rw [sargosPhysicalExtendedRemainder_agrees f hM Q q hm]

theorem sargos_extended_sextuple_sum {H M : ℕ} (f : ℝ → ℝ)
    (hM : 1 ≤ M) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    (∑ m ∈ sargosSextupleInterior M q,
      fordAdditiveCharacter (sargosExtendedSextuplePhase f M Q q m)) =
      ∑ m ∈ sargosSextupleInterior M q, fordAdditiveCharacter (sargosSextuplePhase f q m) := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [sargosExtendedSextuplePhase_agrees f hM Q q hm]

theorem sargosExtendedSextupleCorrelation_eq_interior (f : ℝ → ℝ)
    {M : ℕ} (hM : 1 ≤ M) (H Q : ℕ) :
    sargosExtendedSextupleCorrelation f M H Q = sargosInteriorSextupleCorrelation f M H := by
  apply Finset.sum_congr rfl
  intro q hq
  rw [sargos_extended_sextuple_sum f hM Q q]

theorem sargos_character_extended_differencing (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ H : ℕ, 1 ≤ H → ∀ M : ℕ, H ≤ M →
      ∀ (f : ℝ → ℝ) (Q : ℕ),
      ‖∑ m ∈ Finset.Ioc (0:ℤ) M, fordAdditiveCharacter (f m)‖^12 ≤
        1492992*((M:ℝ)/H)^6*(M:ℝ)^6+
        (382205952*(M:ℝ)^11/(H:ℝ)^4)*sargosExtendedSextupleCorrelation f M H Q+
        C*(M:ℝ)^11*(H:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := sargos_character_interior_differencing ε hε
  refine ⟨C,hC,?_⟩
  intro H hH M hHM f Q
  rw [sargosExtendedSextupleCorrelation_eq_interior f (hH.trans hHM)]
  exact hbound H hH M hHM f

end TaoTrudgianYang2025
