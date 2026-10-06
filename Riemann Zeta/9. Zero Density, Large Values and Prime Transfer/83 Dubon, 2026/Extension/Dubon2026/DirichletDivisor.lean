import Dubon2026.DirichletZeros
import GuthMaynardExternal.PNT.RectangleArgumentPrinciple

/-! # Exact analytic-multiplicity adapter to the existing rectangle divisor API -/

namespace Dubon2026

open Set Complex

theorem meromorphicOrderAt_dirichletSum {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (s : ℂ) :
    meromorphicOrderAt (dirichletSum a N) s = (zeroMultiplicity a N s : ℤ) := by
  rw [(analyticAt_dirichletSum a N s).meromorphicOrderAt_eq, ← zeroMultiplicity_cast hN ha]
  simp

theorem meromorphicOrderAt_dirichletSum_ne_top {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (s : ℂ) :
    meromorphicOrderAt (dirichletSum a N) s ≠ ⊤ := by
  rw [meromorphicOrderAt_dirichletSum hN ha]
  exact WithTop.coe_ne_top

theorem dirichlet_divisor_apply {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {U : Set ℂ} {s : ℂ} (hs : s ∈ U) :
    MeromorphicOn.divisor (dirichletSum a N) U s = (zeroMultiplicity a N s : ℤ) := by
  have hf : MeromorphicOn (dirichletSum a N) U :=
    fun z _ => (analyticAt_dirichletSum a N z).meromorphicAt
  rw [hf.divisor_apply hs, meromorphicOrderAt_dirichletSum hN ha]
  rfl

theorem mem_dirichlet_divisor_support {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (U : Set ℂ) (s : ℂ) :
    s ∈ (MeromorphicOn.divisor (dirichletSum a N) U).support ↔
      s ∈ U ∧ dirichletSum a N s = 0 := by
  constructor
  · intro hs
    have hU := (MeromorphicOn.divisor (dirichletSum a N) U).supportWithinDomain hs
    refine ⟨hU, (zeroMultiplicity_pos_iff hN ha s).mp (Nat.pos_of_ne_zero ?_)⟩
    intro hz
    exact hs (by rw [dirichlet_divisor_apply hN ha hU, hz, Nat.cast_zero])
  · rintro ⟨hU, hz⟩
    change MeromorphicOn.divisor (dirichletSum a N) U s ≠ 0
    rw [dirichlet_divisor_apply hN ha hU]
    exact_mod_cast (zeroMultiplicity_pos_iff hN ha s).mpr hz |>.ne'

theorem dirichlet_rectangle_argument_principle {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hb : ∀ s ∈ RectangleBorder z w, dirichletSum a N s ≠ 0) :
    RectangleIntegral' (logDeriv (dirichletSum a N)) z w =
      ∑ s ∈ (divisor_support_rectangle_finite (dirichletSum a N) z w).toFinset,
        (zeroMultiplicity a N s : ℂ) := by
  have hf : MeromorphicOn (dirichletSum a N) (Rectangle z w) :=
    fun s _ => (analyticAt_dirichletSum a N s).meromorphicAt
  have hd : Disjoint (RectangleBorder z w)
      (MeromorphicOn.divisor (dirichletSum a N) (Rectangle z w)).support := by
    rw [Set.disjoint_left]
    intro s hs hsupport
    exact hb s hs ((mem_dirichlet_divisor_support hN ha _ s).mp hsupport).2
  rw [rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt hre him hf hf.logDeriv
    (fun s _ => meromorphicOrderAt_dirichletSum_ne_top hN ha s) hd]
  apply Finset.sum_congr rfl
  intro s hs
  have hU := ((mem_dirichlet_divisor_support hN ha _ s).mp
    ((divisor_support_rectangle_finite (dirichletSum a N) z w).mem_toFinset.mp hs)).1
  rw [dirichlet_divisor_apply hN ha hU, Int.cast_natCast]

end Dubon2026
