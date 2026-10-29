import Dubon2026.SourceGammaOneEisensteinSum
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! DUB-17/18 -> all-weight association -> original Gamma1 degree
preservation -> integral Eisenstein coset separation. Summing over the
second residue class first reduces the Fourier calculation to Mathlib's
unrestricted integer Lipschitz sum. No additive-character expansion is
needed. These are the same lattice sums and original Gamma1 forms. -/
namespace Dubon2026.SourceFunctionField.GammaOne.IntegralEisenstein
noncomputable section
open scoped MatrixGroups CongruenceSubgroup ModularForm Topology Manifold Matrix
open UpperHalfPlane hiding I
open EisensteinSeries Complex

private def rowClassEquiv (N : ℕ) (c : ZMod N) :
    (Σ b : ZMod N, rows N ![c, b]) ≃ ({m : ℤ // (m : ZMod N) = c} × ℤ) where
  toFun p := (⟨p.2.1 0, congr_fun p.2.2 0⟩, p.2.1 1)
  invFun p := ⟨(p.2 : ZMod N), ⟨![p.1.1, p.2], by
    funext i
    fin_cases i
    · exact p.1.2
    · rfl⟩⟩
  left_inv p := by
    rcases p with ⟨b, v, hv⟩
    have hb : (v 1 : ZMod N) = b := congr_fun hv 1
    subst b
    have hv' : ![v 0, v 1] = v := by
      funext i
      fin_cases i <;> rfl
    dsimp only
    simp only [hv']
  right_inv p := by cases p; rfl

private theorem summable_class_rows (N : ℕ) (c : ZMod N) (z : ℍ) :
    Summable fun p : {m : ℤ // (m : ZMod N) = c} × ℤ =>
      eisSummand 4 ![p.1.1, p.2] z := by
  refine (summable_prod_eisSummand (k := 4) (by norm_num) z).comp_injective
    (i := fun p : {m : ℤ // (m : ZMod N) = c} × ℤ => (p.1.1, p.2)) ?_
  intro x y h
  have h1 : x.1.1 = y.1.1 := congrArg (fun q : ℤ × ℤ => q.1) h
  have h2 : x.2 = y.2 := congrArg (fun q : ℤ × ℤ => q.2) h
  exact Prod.ext (Subtype.ext h1) h2

theorem rowSum_eq_integer_lattice (N : ℕ) [NeZero N] (c : ZMod N) (z : ℍ) :
    rowSum N c z = ∑' m : {m : ℤ // (m : ZMod N) = c},
      ∑' d : ℤ, (((m.1 : ℂ) * z + d) ^ (4 : ℕ))⁻¹ := by
  have hs := summable_class_rows N c z
  have ht := (rowClassEquiv N c).summable_iff.mpr hs
  change Summable (fun p : (Σ b : ZMod N, rows N ![c, b]) =>
    eisSummand 4 ![p.2.1 0, p.2.1 1] z) at ht
  calc
    rowSum N c z = ∑' b : ZMod N, ∑' v : rows N ![c, b], eisSummand 4 v z := by
      simp only [rowSum, Finset.sum_apply, series, tsum_fintype]
    _ = ∑' p : (Σ b : ZMod N, rows N ![c, b]),
        eisSummand 4 ![p.2.1 0, p.2.1 1] z := by
      rw [ht.tsum_sigma]
      refine tsum_congr fun b => tsum_congr fun v => ?_
      congr 1
      funext i
      fin_cases i <;> rfl
    _ = ∑' p : {m : ℤ // (m : ZMod N) = c} × ℤ,
        eisSummand 4 ![p.1.1, p.2] z := (rowClassEquiv N c).tsum_eq
          (fun p : {m : ℤ // (m : ZMod N) = c} × ℤ => eisSummand 4 ![p.1.1, p.2] z)
    _ = _ := by
      rw [hs.tsum_prod]
      refine tsum_congr fun m => tsum_congr fun d => ?_
      simp only [eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one,
        zpow_neg, zpow_ofNat]

end
end Dubon2026.SourceFunctionField.GammaOne.IntegralEisenstein
