import GafniTao.EnergyDetectorSharpShellExtraction
import RiemannZeta.GuthMaynard.LargeValuesLanguage

/-!
# Translation of signed-shell large-value sets

The frozen Guth--Maynard large-values theorems use sets in `[0,T]`, whereas
the signed zero-shell detector naturally produces representatives in a
symmetric interval.  These lemmas give the exact translation, coefficient
phase twist, cardinality, separation, and energy identities needed to cross
that convention boundary.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Positive-sign Dirichlet polynomials transform under ordinate translation
by the opposite phase twist to the negative-sign convention. -/
theorem sourceDirichletPoly_translate
    (N : Nat) (a : Nat → Complex) (c t : Real) :
    sourceDirichletPoly N a (t + c) =
      sourceDirichletPoly N (phaseShiftCoeffs (-c) a) t := by
  unfold sourceDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    rw [dyadicInterval, Finset.mem_Ioc] at hn
    omega
  have hnNe : (n : Complex) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [phaseShiftCoeffs, if_neg hnPos.ne']
  rw [mul_assoc, ← Complex.cpow_add _ _ hnNe]
  congr 2
  push_cast
  ring

/-- Translating a finite real set preserves its cardinality. -/
theorem card_gmTranslate (c : Real) (W : Finset Real) :
    (gmTranslate c W).card = W.card := by
  unfold gmTranslate
  exact Finset.card_image_iff.mpr (fun x _ y _ hxy => by linarith)

/-- Translation preserves separation. -/
theorem isSeparated_gmTranslate
    (d c : Real) (W : Finset Real) (hW : IsSeparated d W) :
    IsSeparated d (gmTranslate c W) := by
  intro x hx y hy hxy
  rw [gmTranslate, Finset.mem_image] at hx hy
  obtain ⟨x0, hx0, rfl⟩ := hx
  obtain ⟨y0, hy0, rfl⟩ := hy
  have hne : x0 ≠ y0 := by
    intro h
    subst y0
    exact hxy rfl
  simpa [Real.dist_eq] using hW x0 hx0 y0 hy0 hne

/-- A symmetric interval translates exactly into the frozen base interval. -/
theorem inBaseInterval_gmTranslate_of_symmetric
    (B : Real) (W : Finset Real)
    (hW : ∀ t, t ∈ W → -B ≤ t ∧ t ≤ B) :
    InBaseInterval (2 * B) (gmTranslate B W) := by
  intro y hy
  rw [gmTranslate, Finset.mem_image] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  rw [Set.mem_Icc]
  obtain ⟨htLower, htUpper⟩ := hW t ht
  constructor <;> linarith

/-- A large value on a symmetric set becomes a large value on its translated
base-interval set after the exact unimodular coefficient twist. -/
theorem sourceDirichletPoly_large_on_gmTranslate
    (N : Nat) (a : Nat → Complex) (B V : Real) (W : Finset Real)
    (hLarge : ∀ t, t ∈ W → V ≤ ‖sourceDirichletPoly N a t‖) :
    ∀ y, y ∈ gmTranslate B W →
      V ≤ ‖sourceDirichletPoly N (phaseShiftCoeffs B a) y‖ := by
  intro y hy
  rw [gmTranslate, Finset.mem_image] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  have h := hLarge t ht
  calc
    V ≤ ‖sourceDirichletPoly N a t‖ := h
    _ = ‖sourceDirichletPoly N (phaseShiftCoeffs B a) (t + B)‖ := by
      congr 1
      simpa only [neg_neg, add_neg_cancel_right] using
        sourceDirichletPoly_translate N a (-B) (t + B)

/-- Unit coefficient bounds survive the translation twist. -/
theorem norm_phaseShiftCoeffs_le_one_on
    (N : Nat) (a : Nat → Complex) (B : Real)
    (ha : ∀ n, n ∈ dyadicInterval N → ‖a n‖ ≤ 1) :
    ∀ n, n ∈ dyadicInterval N → ‖phaseShiftCoeffs B a n‖ ≤ 1 := by
  intro n hn
  rw [norm_phaseShiftCoeffs]
  exact ha n hn

#print axioms sourceDirichletPoly_translate
#print axioms card_gmTranslate
#print axioms isSeparated_gmTranslate
#print axioms inBaseInterval_gmTranslate_of_symmetric
#print axioms sourceDirichletPoly_large_on_gmTranslate
#print axioms norm_phaseShiftCoeffs_le_one_on

end

end GafniTao
