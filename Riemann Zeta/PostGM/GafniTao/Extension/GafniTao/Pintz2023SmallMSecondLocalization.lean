import GafniTao.Pintz2023PowerMargins
import GafniTao.Pintz2023SmallMIntervalPower
import RiemannZeta.GuthMaynard.PolynomialPowers

/-!
# Pintz (2023), equation (4.16): second dyadic localization

The real parts of the displaced zeros vary with the ordinate.  Consequently
the line-normalized coefficient used for pigeonholing also varies.  The
underlying powered arithmetic coefficient remains common, exactly as required
by equations (4.17)--(4.18).
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintz2023SmallMPoweredLineCoeff
    (X : ℕ) (R : ℝ) (baseI : Finset ℕ) (h : ℕ)
    (beta : ℝ) (m : ℕ) : ℂ :=
  pintz2023SmallMIntervalPowerCoeff X R baseI h m *
    (m : ℂ) ^ (-(beta : ℂ))

/-- Exact wide-polynomial realization of the power of the surviving block. -/
theorem wideDirichletPoly_pintz2023SmallMPoweredLineCoeff
    (X U h : ℕ) (R beta t : ℝ) {baseI : Finset ℕ}
    (hbaseI : baseI ⊆ Finset.Ioc U (2 * U))
    (hU : 0 < U) (hh : 0 < h) :
    wideDirichletPoly (U ^ h) h
        (pintz2023SmallMPoweredLineCoeff X R baseI h beta) t =
      (pintz2023SplitIntervalBlock
        (fun n => pintz2023SmallMCoeff X n R) baseI
        ((beta : ℂ) + I * (t : ℂ))) ^ h := by
  rw [pintz2023_smallM_interval_power_identity_Ioc
    X R U h ((beta : ℂ) + I * (t : ℂ)) hbaseI hU hh]
  unfold wideDirichletPoly pintz2023SmallMPoweredLineCoeff
  have hUpper : 2 ^ h * U ^ h = (2 * U) ^ h := by
    rw [mul_pow]
  rw [hUpper]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := by
    exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hm).1
  have hmNe : (m : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
  rw [mul_assoc, ← Complex.cpow_add _ _ hmNe]
  congr 2
  ring

/-- Simultaneous second localization with varying real parts.  The block
index is common on the output subset; only the harmless line normalization
depends on the selected ordinate. -/
theorem exists_pintz2023_smallM_powered_block_and_subset
    {X U h : ℕ} {R V : ℝ} {baseI : Finset ℕ}
    {W : Finset ℝ} (betaAt gammaAt : ℝ → ℝ)
    (hbaseI : baseI ⊆ Finset.Ioc U (2 * U))
    (hU : 0 < U) (hh : 0 < h) (hV : 0 ≤ V)
    (hLarge : ∀ t ∈ W, V ≤
      ‖pintz2023SplitIntervalBlock
        (fun n => pintz2023SmallMCoeff X n R) baseI
        (((betaAt t : ℝ) : ℂ) + I * (gammaAt t : ℂ))‖) :
    ∃ q ∈ Finset.range h, ∃ W' ⊆ W,
      (W.card : ℝ) ≤ h * (W'.card : ℝ) ∧
      ∀ t ∈ W', V ^ h / h ≤
        ‖dirichletPoly (2 ^ q * U ^ h)
          (pintz2023SmallMPoweredLineCoeff
            X R baseI h (betaAt t)) (gammaAt t)‖ := by
  classical
  have hWide : ∀ t ∈ W, V ^ h ≤
      ‖wideDirichletPoly (U ^ h) h
        (pintz2023SmallMPoweredLineCoeff
          X R baseI h (betaAt t)) (gammaAt t)‖ := by
    intro t ht
    rw [wideDirichletPoly_pintz2023SmallMPoweredLineCoeff
      X U h R (betaAt t) (gammaAt t) hbaseI hU hh, norm_pow]
    exact pow_le_pow_left₀ hV (hLarge t ht) h
  have hEach : ∀ t ∈ W, ∃ q ∈ Finset.range h,
      V ^ h / h ≤
        ‖dirichletPoly (2 ^ q * U ^ h)
          (pintz2023SmallMPoweredLineCoeff
            X R baseI h (betaAt t)) (gammaAt t)‖ := by
    intro t ht
    exact exists_large_dyadic_block (U ^ h) h
      (pintz2023SmallMPoweredLineCoeff X R baseI h (betaAt t))
      (gammaAt t) (V ^ h) hh (hWide t ht)
  let index (t : ℝ) : ℕ :=
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hIndexMem : ∀ t ∈ W, index t ∈ Finset.range h := by
    intro t ht
    simp only [index, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).1
  have hIndexLarge : ∀ t ∈ W,
      V ^ h / h ≤
        ‖dirichletPoly (2 ^ index t * U ^ h)
          (pintz2023SmallMPoweredLineCoeff
            X R baseI h (betaAt t)) (gammaAt t)‖ := by
    intro t ht
    simp only [index, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).2
  have hCard : W.card = ∑ q ∈ Finset.range h,
      (W.filter fun t => index t = q).card :=
    Finset.card_eq_sum_card_fiberwise hIndexMem
  have hCardReal : (W.card : ℝ) = ∑ q ∈ Finset.range h,
      ((W.filter fun t => index t = q).card : ℝ) := by
    exact_mod_cast hCard
  obtain ⟨q, hq, hqLarge⟩ := pigeonhole_real_sum h
    (fun q => ((W.filter fun t => index t = q).card : ℝ))
    (W.card : ℝ) (by rw [hCardReal]) hh
  refine ⟨q, hq, W.filter fun t => index t = q,
    Finset.filter_subset _ _, ?_, ?_⟩
  · have hhReal : (0 : ℝ) < h := by exact_mod_cast hh
    calc
      (W.card : ℝ) = h * ((W.card : ℝ) / h) := by field_simp
      _ ≤ h * ((W.filter fun t => index t = q).card : ℝ) := by gcongr
  · intro t ht
    rw [Finset.mem_filter] at ht
    simpa [ht.2] using hIndexLarge t ht.1

#print axioms wideDirichletPoly_pintz2023SmallMPoweredLineCoeff
#print axioms exists_pintz2023_smallM_powered_block_and_subset

end

end GafniTao
