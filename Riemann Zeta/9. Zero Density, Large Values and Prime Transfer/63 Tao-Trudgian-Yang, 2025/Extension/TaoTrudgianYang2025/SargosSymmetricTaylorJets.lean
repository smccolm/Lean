import TaoTrudgianYang2025.SargosSymmetricTaylor

/-! Differentiated actual symmetric remainders with local, original-phase jet bounds. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargosSymmetricRemainder_contDiffAt {f : ℝ → ℝ} {m n : ℝ}
    (hp : ContDiffAt ℝ ∞ f (m+n)) (hm : ContDiffAt ℝ ∞ f (m-n))
    (hc : ContDiffAt ℝ ∞ f m) :
    ContDiffAt ℝ ∞ (sargosSymmetricRemainder f n) m := by
  have hp' := hp.comp m (contDiffAt_id.add contDiffAt_const)
  have hm' := hm.comp m (contDiffAt_id.sub contDiffAt_const)
  exact (((hp'.add hm').sub (contDiffAt_const.mul hc)).sub
    (contDiffAt_const.mul (contDiffAt_iteratedDeriv_infty hc 2))).sub
    (contDiffAt_const.mul (contDiffAt_iteratedDeriv_infty hc 4))

theorem iteratedDeriv_sargosSymmetricRemainder {f : ℝ → ℝ} {m n : ℝ}
    (hp : ContDiffAt ℝ ∞ f (m+n)) (hm : ContDiffAt ℝ ∞ f (m-n))
    (hc : ContDiffAt ℝ ∞ f m) (j : ℕ) :
    iteratedDeriv j (sargosSymmetricRemainder f n) m =
      sargosSymmetricRemainder (iteratedDeriv j f) n m := by
  have hp' : ContDiffAt ℝ ∞ (fun x => f (x+n)) m :=
    hp.comp m (contDiffAt_id.add contDiffAt_const)
  have hm' : ContDiffAt ℝ ∞ (fun x => f (x-n)) m :=
    hm.comp m (contDiffAt_id.sub contDiffAt_const)
  have htwo : ContDiffAt ℝ ∞ (fun x => 2*f x) m := contDiffAt_const.mul hc
  have hquad : ContDiffAt ℝ ∞ (fun x => n^2*iteratedDeriv 2 f x) m :=
    contDiffAt_const.mul (contDiffAt_iteratedDeriv_infty hc 2)
  have hfour : ContDiffAt ℝ ∞ (fun x => (n^4/12)*iteratedDeriv 4 f x) m :=
    contDiffAt_const.mul (contDiffAt_iteratedDeriv_infty hc 4)
  have hj : (j : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  unfold sargosSymmetricRemainder
  rw [iteratedDeriv_fun_sub (((hp'.add hm').sub htwo).sub hquad |>.of_le hj) (hfour.of_le hj),
    iteratedDeriv_fun_sub (((hp'.add hm').sub htwo).of_le hj) (hquad.of_le hj),
    iteratedDeriv_fun_sub ((hp'.add hm').of_le hj) (htwo.of_le hj),
    iteratedDeriv_fun_add (hp'.of_le hj) (hm'.of_le hj)]
  simp only [iteratedDeriv_comp_add_const,iteratedDeriv_comp_sub_const,
    iteratedDeriv_const_mul_field,iteratedDeriv_real_comp_order]
  rw [Nat.add_comm j 2,Nat.add_comm j 4]

theorem abs_iteratedDeriv_sargosSymmetricRemainder_le
    {f : ℝ → ℝ} {m n B : ℝ} (hn : 0 ≤ n)
    (hf : ∀ x ∈ Icc (m-n) (m+n), ContDiffAt ℝ ∞ f x)
    (j : ℕ)
    (hB : ∀ x ∈ Icc (m-n) (m+n), |iteratedDeriv (j+6) f x| ≤ B) :
    |iteratedDeriv j (sargosSymmetricRemainder f n) m| ≤ B*n^6/360 := by
  have hp : m+n ∈ Icc (m-n) (m+n) := ⟨by linarith,le_rfl⟩
  have hm : m-n ∈ Icc (m-n) (m+n) := ⟨le_rfl,by linarith⟩
  have hc : m ∈ Icc (m-n) (m+n) := ⟨by linarith,by linarith⟩
  rw [iteratedDeriv_sargosSymmetricRemainder (hf _ hp) (hf _ hm) (hf _ hc)]
  apply abs_sargosSymmetricRemainder_le hn
    (fun x hx => contDiffAt_iteratedDeriv_infty (hf x hx) j)
  intro x hx
  rw [iteratedDeriv_real_comp_order,Nat.add_comm 6 j]
  exact hB x hx

end TaoTrudgianYang2025
