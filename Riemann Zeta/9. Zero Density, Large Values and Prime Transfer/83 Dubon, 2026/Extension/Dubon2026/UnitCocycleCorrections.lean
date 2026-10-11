import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Actual multiplicative cocycle corrections at finite filtration precision -/

namespace Dubon2026

variable {G U : Type} [Group G] [CommGroup U] [MulDistribMulAction G U]

/-- The original unit coboundary respects multiplication of original correcting units. -/
theorem unit_coboundary_mul (g : G) (u v : U) :
    (g • (u * v)) / (u * v) = ((g • u) / u) * ((g • v) / v) := by
  rw [smul_mul', mul_div_mul_comm]

/-- Dividing an original multiplicative cocycle by an actual original unit
coboundary leaves a multiplicative cocycle for the same action. -/
theorem unit_cocycle_corrected_isCocycle (c : G → U)
    (hc : ∀ g h, c (g * h) = (g • c h) * c g) (u : U) :
    ∀ g h, c (g * h) / (((g * h) • u) / u) =
      (g • (c h / ((h • u) / u))) * (c g / ((g • u) / u)) := by
  intro g h
  rw [hc, mul_smul, smul_div', smul_div', ← mul_div_mul_comm, div_mul_div_cancel]

/-- Original one-step cocycle corrections at every level give genuine
original coboundary approximations to every finite precision. The cumulative
correcting unit remains in the original initial subgroup. -/
theorem unit_cocycle_filtered_approximations
    (S : ℕ → Subgroup U) (hmono : ∀ j, S (j + 1) ≤ S j)
    (hcorrect : ∀ j (c : G → U),
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S j) →
        ∃ u : U, u ∈ S j ∧ ∀ g, c g / ((g • u) / u) ∈ S (j + 1))
    (c : G → U) (hc : ∀ g h, c (g * h) = (g • c h) * c g)
    (hc0 : ∀ g, c g ∈ S 0) :
    ∀ j, ∃ u : U, u ∈ S 0 ∧ ∀ g, c g / ((g • u) / u) ∈ S j := by
  have hsub : ∀ j, S j ≤ S 0 := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (hmono j).trans ih
  intro j
  induction j with
  | zero => exact ⟨1, (S 0).one_mem, fun g => by simpa only [smul_one, div_one] using hc0 g⟩
  | succ j ih =>
    obtain ⟨u, hu, he⟩ := ih
    obtain ⟨v, hv, hnext⟩ := hcorrect j (fun g => c g / ((g • u) / u))
      (unit_cocycle_corrected_isCocycle c hc u) he
    refine ⟨u * v, (S 0).mul_mem hu (hsub j hv), fun g => ?_⟩
    rw [unit_coboundary_mul]
    simpa only [div_div] using hnext g

end Dubon2026
