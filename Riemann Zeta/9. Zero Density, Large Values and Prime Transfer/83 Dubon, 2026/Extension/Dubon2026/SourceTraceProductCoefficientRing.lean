import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Recover precisely the needed
coefficient of the original series from finitely many coefficients of its
product with the auxiliary series. The leading auxiliary coefficient has
its inverse in the prescribed subring; no coefficient of the target is
assumed directly. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem.lean. -/
namespace Dubon2026.SourceFunctionField.LevelOneCoefficientRing

theorem coeff_mem_of_product_initial_coeff_mem (R : Subring ℂ)
    (P U : PowerSeries ℂ) (m₀ L : ℕ)
    (hU₀ : ∀ n : ℕ, n < m₀ → PowerSeries.coeff n U = 0)
    (hU₁ : ∃ v ∈ R, v * PowerSeries.coeff m₀ U = 1)
    (hU : ∀ n : ℕ, PowerSeries.coeff n U ∈ R)
    (hPU : ∀ n : ℕ, n < L → PowerSeries.coeff n (P * U) ∈ R)
    (n : ℕ) (hn : n + m₀ < L) :
    PowerSeries.coeff n P ∈ R := by
  obtain ⟨v, hv, hvu⟩ := hU₁
  induction n using Nat.strong_induction_on with
  | _ n ih =>

    have hsum := PowerSeries.coeff_mul (n + m₀) P U

    have hmem : (n, m₀) ∈ Finset.HasAntidiagonal.antidiagonal (n + m₀) := by simp
    rw [← Finset.add_sum_erase _ _ hmem] at hsum

    have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n + m₀)).erase (n, m₀), PowerSeries.coeff x.1 P * PowerSeries.coeff x.2 U ∈ R := by
      refine Subring.sum_mem _ fun x hx => ?_
      obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rcases lt_trichotomy x.1 n with hlt | heq | hgt
      · exact Subring.mul_mem _ (ih x.1 hlt (by omega)) (hU x.2)
      · exfalso; apply hne
        have : x.2 = m₀ := by omega
        exact Prod.ext heq this
      · have : x.2 < m₀ := by omega
        rw [hU₀ x.2 this, mul_zero]
        exact Subring.zero_mem _

    have hkey : PowerSeries.coeff n P = v * (PowerSeries.coeff (n + m₀) (P * U) -
        ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n + m₀)).erase (n, m₀), PowerSeries.coeff x.1 P * PowerSeries.coeff x.2 U) := by
      rw [hsum, add_sub_cancel_right, mul_comm v, mul_assoc, mul_comm _ v, hvu, mul_one]
    rw [hkey]
    exact Subring.mul_mem _ hv (Subring.sub_mem _ (hPU _ hn) hrest)

end Dubon2026.SourceFunctionField.LevelOneCoefficientRing
