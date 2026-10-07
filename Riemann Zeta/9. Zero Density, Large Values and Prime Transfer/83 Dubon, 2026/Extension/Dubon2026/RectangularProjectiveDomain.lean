import Dubon2026.CongruenceTraceDomain
import Dubon2026.RectangularConjugation

/-! # Exact real projective transport of the rectangular subgroup domain -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups Pointwise

noncomputable section

/-- Mapping a genuine conjugate subgroup commutes exactly with a group homomorphism. -/
theorem map_conjAct_subgroup {G K : Type*} [Group G] [Group K]
    (φ : G →* K) (H : Subgroup G) (a : G) :
    (ConjAct.toConjAct a • H).map φ = ConjAct.toConjAct (φ a) • H.map φ := by
  ext g
  constructor
  · rintro ⟨u, hu, rfl⟩
    change u ∈ ConjAct.toConjAct a • H at hu
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hu ⊢
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨φ v, ⟨v, hv, rfl⟩, ?_⟩
    change φ a * φ v * (φ a)⁻¹ = φ (a * v * a⁻¹)
    simp
  · rw [Subgroup.mem_smul_pointwise_iff_exists]
    rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨a * v * a⁻¹, ?_, by simp [ConjAct.smul_def]⟩
    change a * v * a⁻¹ ∈ ConjAct.toConjAct a • H
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨v, hv, rfl⟩

/-- The exact mixed subgroup is the diagonal conjugate in the faithful real projective action. -/
theorem realProjective_rectangular_eq_conj (a b : ℕ) [NeZero a] :
    realProjectiveIntegralSubgroup (rectangularCongruenceSubgroup a b) =
      ConjAct.toConjAct (ProjGenLinGroup.mk (levelRaiseMatrix a)) • realProjectiveGamma0 (a * b) := by
  rw [realProjectiveIntegralSubgroup_eq_map, slToRealProjective, ← Subgroup.map_map,
    rectangularCongruence_map_eq_conj, map_conjAct_subgroup]
  congr 1
  change ((Gamma0 (a * b)).map (mapGL ℝ)).map ProjGenLinGroup.mk =
    realProjectiveIntegralSubgroup (Gamma0 (a * b))
  rw [realProjectiveIntegralSubgroup_eq_map, Subgroup.map_map]
  rfl

/-- Diagonal transport of the original Gamma0 domain gives a genuine domain for the mixed group. -/
theorem isFundamentalDomain_rectangular_translate (a b : ℕ) [NeZero a] [NeZero b] :
    IsFundamentalDomain (realProjectiveIntegralSubgroup (rectangularCongruenceSubgroup a b))
      (levelRaiseMatrix a • gamma0FundamentalDomain (a * b)) (volume : Measure ℍ) := by
  change IsFundamentalDomain _ (ProjGenLinGroup.mk (levelRaiseMatrix a) •
    gamma0FundamentalDomain (a * b)) (volume : Measure ℍ)
  exact fundamentalDomain_smul_of_eq_conjAct (isFundamentalDomain_realGamma0 (a * b))
    (realProjective_rectangular_eq_conj a b)

/-- The literal integral coset tiling is another genuine domain for the same mixed group. -/
theorem isFundamentalDomain_rectangular_coset (a b : ℕ) :
    IsFundamentalDomain (realProjectiveIntegralSubgroup (rectangularCongruenceSubgroup a b))
      (integralSubgroupDomain (rectangularCongruenceSubgroup a b)) (volume : Measure ℍ) :=
  isFundamentalDomain_realIntegralSubgroup _ (center_SL_le_rectangularCongruenceSubgroup a b)

end
end Dubon2026
