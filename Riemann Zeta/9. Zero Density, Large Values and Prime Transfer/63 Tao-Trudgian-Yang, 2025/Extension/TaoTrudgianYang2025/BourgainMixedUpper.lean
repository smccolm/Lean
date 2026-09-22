import TaoTrudgianYang2025.BourgainMixedShift

/-!
# Actual mixed upper estimate from Heath--Brown

The selected source set and the real image of the full integer slice satisfy
the required geometry. Both self moments use the same genuine source support.
The enclosing physical height and exact integration length remain explicit.
-/

open Finset MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_sqrt_common_factor {A B D : ℝ} (hA : 0 ≤ A) :
    Real.sqrt (A*B)*Real.sqrt (A*D) =
      A*(Real.sqrt B*Real.sqrt D) := by
  rw [Real.sqrt_mul hA, Real.sqrt_mul hA]
  calc
    _ = (Real.sqrt A)^2*(Real.sqrt B*Real.sqrt D) := by ring
    _ = _ := by rw [Real.sq_sqrt hA]

/-- A uniform bound for the actual shifted mixed local moment; neither
separation nor a Heath--Brown estimate for the auxiliary slice is assumed. -/
theorem bourgain_actual_mixed_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ C E₀ : ℝ, 0 < C ∧ 1 ≤ E₀ ∧
      ∀ (P : LargeValuePattern) (S : Finset ℝ), S ⊆ P.ordinates →
      ∀ (H T V u r E : ℝ), u ∈ Icc (-H) H → 0 ≤ r →
        E₀ ≤ E → P.T ≤ E → 2*(T+H) ≤ E →
        (∫ v in -r..r, ∑ t ∈ S, ∑ ℓ ∈ bourgainIntegerSlice H T V u,
          ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n (t-(ℓ : ℝ)+v)‖^2) ≤
          2*r*C*E^ε*
            (Real.sqrt (bourgainSecondBudget P.N E (S.card : ℝ))*
              Real.sqrt (bourgainSecondBudget P.N E
                ((bourgainIntegerSlice H T V u).card : ℝ))) := by
  obtain ⟨C, E₀, hC, hE₀, hHB⟩ := bourgain_separated_self_moment hε
  refine ⟨C, E₀, hC, hE₀, ?_⟩
  intro P S hsub H T V u r E hu hr hE hPE hZE
  have hsep : IsSeparated 1 S := by
    intro t ht w hw htw
    simpa only [Real.dist_eq] using
      P.ordinates_oneSeparated t (hsub ht) w (hsub hw) htw
  have hSloc : ∀ t ∈ S, P.intervalLeft ≤ t ∧ t ≤ P.intervalLeft+E := by
    intro t ht
    have hloc := P.ordinates_in_interval t (hsub ht)
    constructor
    · exact hloc.1
    · linarith [P.interval_length]
  have hZloc : ∀ x ∈ bourgainRealSlice H T V u,
      -(T+H) ≤ x ∧ x ≤ -(T+H)+E := by
    intro x hx
    have hh := bourgainRealSlice_bounds hu x hx
    constructor
    · exact hh.1
    · linarith
  have hS := hHB P S P.intervalLeft E hE hsep hSloc
  have hZ := hHB P (bourgainRealSlice H T V u) (-(T+H)) E hE
    (bourgainRealSlice_separated H T V u) hZloc
  rw [bourgainRealSlice_card] at hZ
  have hprod := mul_le_mul (Real.sqrt_le_sqrt hS) (Real.sqrt_le_sqrt hZ)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hEpos : 0 < E := zero_lt_one.trans_le (hE₀.trans hE)
  rw [bourgain_sqrt_common_factor (mul_nonneg hC.le (Real.rpow_nonneg hEpos.le ε))]
    at hprod
  have hfin := (bourgain_slice_mixed_integral_cauchySchwarz P S H T V u r hr).trans
    (mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) hr))
  convert hfin using 1
  ring

end TaoTrudgianYang2025
