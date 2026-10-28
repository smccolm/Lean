import Dubon2026.SourceGammaOneAnalyticDivisorMoving
import Dubon2026.SourceGammaOneAnalyticPlaceOrbits
import Dubon2026.SourceGammaOneExactRamification
import Mathlib.Data.Set.Finite.Basic

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> finite orbit representatives and weighted order sum.
The actual degree-zero analytic divisor and exact signed stabilizer formula
give the required degree identity directly. A separate logarithmic residue
theorem for arbitrary automorphic functions is unnecessary for this source
contract. All original Gamma1 levels and elliptic multiplicities remain. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup
open scoped MatrixGroups Classical

theorem exists_analytic_support_representatives {Γ : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ) (c : ℍ →₀ ℤ) :
    ∃ S : Finset ℍ, (S : Set ℍ) ⊆ c.support ∧
      Set.InjOn (analyticPlace hT) S ∧
      S.image (analyticPlace hT) = (Finsupp.mapDomain (analyticPlace hT) c).support := by
  classical
  apply Finset.exists_subset_injOn_image_eq_of_surjOn
  intro P hP
  by_contra h
  exact (Finsupp.mem_support_iff.mp hP) (Finsupp.mapDomain_of_not_mem_image_support h)

theorem sum_on_analytic_representatives_eq_degree {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (D : Divisor ℂ (functionFieldOver Γ ℂ)) (S : Finset ℍ)
    (hinj : Set.InjOn (analyticPlace hT) S) (hS : S.image (analyticPlace hT) = D.support) :
    ∑ τ ∈ S, D (analyticPlace hT τ) = Divisor.degree D := by
  classical
  symm
  rw [Divisor.degree_eq_sum_support, ← hS, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro τ _
  have hr : Module.finrank ℂ (analyticPlace hT τ).ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (place_residue_bijective hT _)
  rw [hr, Nat.cast_one, mul_one]

theorem weighted_analytic_order_eq_half_coefficient (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (D : Divisor ℂ (functionFieldOver (Gamma1 N) ℂ))
    (τ : ℍ) :
    (((analyticRamification hT τ : ℤ) * D (analyticPlace hT τ) : ℤ) : ℂ) /
      (Nat.card (MulAction.stabilizer (plusMinus (Gamma1 N)) τ) : ℂ) =
        (D (analyticPlace hT τ) : ℂ) / 2 := by
  have he : (analyticRamification hT τ : ℂ) ≠ 0 := by
    exact_mod_cast (analyticRamification_pos hT τ).ne'
  rw [← two_mul_ramification_eq_stabilizer_card N hT τ]
  push_cast
  field_simp

theorem exists_degree_zero_reciprocity_data (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (c : ℍ →₀ ℤ) (hc : c.sum (fun _ n => n) = 0) :
    let D := Finsupp.mapDomain (analyticPlace hT) c
    ∃ S : Finset ℍ, (S : Set ℍ) ⊆ c.support ∧
      (∀ s ∈ S, ∀ t ∈ S, (∃ γ : Gamma1 N, γ.val • s = t) → s = t) ∧
      (∀ τ : ℍ, D (analyticPlace hT τ) ≠ 0 →
        ∃ s ∈ S, ∃ γ : Gamma1 N, γ.val • s = τ) ∧
      (∑ s ∈ S, (((analyticRamification hT s : ℤ) * D (analyticPlace hT s) : ℤ) : ℂ) /
        (Nat.card (MulAction.stabilizer (plusMinus (Gamma1 N)) s) : ℂ)) = 0 := by
  classical
  dsimp only
  let D := Finsupp.mapDomain (analyticPlace hT) c
  obtain ⟨S, hsub, hinj, hS⟩ := exists_analytic_support_representatives hT c
  refine ⟨S, hsub, ?_, ?_, ?_⟩
  · intro s hs t ht horbit
    exact hinj hs ht ((analyticPlace_eq_iff_gamma1_orbit N hT s t).mpr horbit)
  · intro τ hτ
    have hm : analyticPlace hT τ ∈ S.image (analyticPlace hT) := by
      rw [hS]
      exact Finsupp.mem_support_iff.mpr hτ
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hm
    exact ⟨s, hs, (analyticPlace_eq_iff_gamma1_orbit N hT s τ).mp he⟩
  · have hdeg : Divisor.degree D = 0 := by
      rw [degree_mapDomain_analyticPlace, hc]
    have hsum := (sum_on_analytic_representatives_eq_degree hT D S hinj hS).trans hdeg
    calc
      (∑ s ∈ S, (((analyticRamification hT s : ℤ) * D (analyticPlace hT s) : ℤ) : ℂ) /
          (Nat.card (MulAction.stabilizer (plusMinus (Gamma1 N)) s) : ℂ))
          = ∑ s ∈ S, (D (analyticPlace hT s) : ℂ) / 2 :=
        Finset.sum_congr rfl fun s _ => weighted_analytic_order_eq_half_coefficient N hT D s
      _ = 0 := by
        rw [← Finset.sum_div]
        have hz : (∑ s ∈ S, (D (analyticPlace hT s) : ℂ)) = 0 := by exact_mod_cast hsum
        rw [hz, zero_div]

end
end Dubon2026.SourceFunctionField.GammaOne
