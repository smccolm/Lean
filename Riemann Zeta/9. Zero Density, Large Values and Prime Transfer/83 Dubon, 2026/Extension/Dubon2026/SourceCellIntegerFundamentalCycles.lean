import Dubon2026.SourceCellIntegerTreeCardinality

/-! DUB-17/18 -> original Abel-Jacobi -> period generation -> fundamental cycles.
A proved integer spanning tree supplies closed fundamental cycles on the
actual labeled edges. The decomposition is valid in every additive commutative
group, as required for both integer cycles and complex-valued period sums.
The already proved integer boundary algebra is reused; unused source
root-chain uniqueness and normalization detours are omitted.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
noncomputable section
open Finset

theorem exists_fundamental_cycles {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (hd tl : E → V) (T : Finset E)
    (hTpath : ∀ u v : V, ∃! c : E → ℤ, (∀ e ∉ T, c e = 0) ∧
      ∀ w, (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0)) :
    ∃ Z : E → E → ℤ,
      (∀ j, ∀ w, (∑ e with hd e = w, Z j e) = (∑ e with tl e = w, Z j e)) ∧
      (∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0) ∧
      (∀ j ∈ T, Z j = 0) ∧
      ∀ {A : Type*} [AddCommGroup A] (f : E → A),
        (∀ w, (∑ e with hd e = w, f e) = (∑ e with tl e = w, f e)) →
        ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j := by
  classical

  rcases isEmpty_or_nonempty V with hVe | hVne
  · haveI : IsEmpty E := ⟨fun e => hVe.elim (hd e)⟩
    exact ⟨fun _ _ => 0, fun _ _ => by simp, fun j _ => isEmptyElim j,
      fun j _ => isEmptyElim j, fun {A} _ f _ e => isEmptyElim e⟩
  obtain ⟨v₀⟩ := hVne

  set c : V → E → ℤ := fun v => (hTpath v₀ v).exists.choose
  have hcspec : ∀ v, (∀ e ∉ T, c v e = 0) ∧
      ∀ w, bd hd tl (c v) w = (if w = v then 1 else 0) - (if w = v₀ then 1 else 0) :=
    fun v => (hTpath v₀ v).exists.choose_spec
  have hcsub_T : ∀ e e', e' ∉ T → c (hd e) e' - c (tl e) e' = 0 := fun e e' he' => by
    rw [(hcspec (hd e)).1 e' he', (hcspec (tl e)).1 e' he']; ring
  have hcsub_bd : ∀ e w, bd hd tl (c (hd e) - c (tl e)) w =
      (if w = hd e then 1 else 0) - (if w = tl e then 1 else 0) := fun e w => by
    rw [bd_sub hd tl, (hcspec (hd e)).2 w, (hcspec (tl e)).2 w]; ring

  have hkey : ∀ e ∈ T, ∀ e', c (hd e) e' - c (tl e) e' = if e' = e then (1 : ℤ) else 0 := by
    intro e heT

    have heq := (hTpath (tl e) (hd e)).unique
      (y₁ := fun e' => if e' = e then (1 : ℤ) else 0)
      (y₂ := fun e' => c (hd e) e' - c (tl e) e')
      ⟨fun e' he' => if_neg (fun (h : e' = e) => he' (h ▸ heT)), bd_single hd tl e⟩
      ⟨fun e' he' => hcsub_T e e' he', fun w => hcsub_bd e w⟩
    intro e'; exact (congrFun heq e').symm

  refine ⟨fun j e' => if j ∈ T then 0 else
    (if e' = j then 1 else 0) - (c (hd j) e' - c (tl j) e'), ?_, ?_, ?_, ?_⟩
  ·
    intro j w
    by_cases hjT : j ∈ T
    · simp only [hjT, if_true, Finset.sum_const_zero]
    · simp only [hjT, if_false]
      have hbd : bd hd tl (fun e' => (if e' = j then (1:ℤ) else 0) -
          (c (hd j) e' - c (tl j) e')) w = 0 := by
        change bd hd tl ((fun e' => if e' = j then (1 : ℤ) else 0) - (c (hd j) - c (tl j))) w = 0
        rw [bd_sub hd tl, bd_single hd tl, hcsub_bd]; ring
      unfold bd at hbd; linarith [hbd]
  ·
    intro j hj j' hj'
    simp only [Finset.mem_compl] at hj hj'
    simp only [hj, if_false, hcsub_T j j' hj', sub_zero, eq_comm (a := j')]
  ·
    intro j hj; funext e'; simp only [hj, if_true]; rfl
  ·
    intro A _ f hf e

    have hZsum : ∀ e', (∑ j ∈ Tᶜ, (if j ∈ T then (0:ℤ) else
        (if e' = j then 1 else 0) - (c (hd j) e' - c (tl j) e')) • f j) =
        ∑ j ∈ Tᶜ, ((if e' = j then (1:ℤ) else 0) - (c (hd j) e' - c (tl j) e')) • f j := by
      intro e'; refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [Finset.mem_compl] at hj; simp only [hj, if_false]
    rw [hZsum e]

    set g : E → A := fun e' => f e' -
      ∑ j ∈ Tᶜ, ((if e' = j then (1:ℤ) else 0) - (c (hd j) e' - c (tl j) e')) • f j with hgdef
    suffices hge : g e = 0 by
      have := hge; rw [hgdef] at this; simp only at this
      exact sub_eq_zero.mp this

    have hgTc : ∀ e' ∈ Tᶜ, g e' = 0 := by
      intro e' he'
      simp only [Finset.mem_compl] at he'
      rw [hgdef]
      simp only
      rw [Finset.sum_eq_single e']
      · simp only [hcsub_T _ e' he', sub_zero, ite_true, one_smul, sub_self]
      · intro j hj hjne
        simp only [Finset.mem_compl] at hj
        rw [if_neg (Ne.symm hjne), hcsub_T j e' he']; simp
      · intro h; exact absurd (Finset.mem_compl.mpr he') h

    have hgK : ∀ w, (∑ e' with hd e' = w, g e') = (∑ e' with tl e' = w, g e') := by
      intro w
      simp only [hgdef, Finset.sum_sub_distrib]
      rw [hf w]
      congr 1

      rw [Finset.sum_comm (t := Tᶜ), Finset.sum_comm (s := univ.filter (tl · = w)) (t := Tᶜ)]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [← Finset.sum_smul]
      congr 1

      have hbdZ : bd hd tl (fun e' => (if e' = j then (1:ℤ) else 0) -
          (c (hd j) e' - c (tl j) e')) w = 0 := by
        change bd hd tl ((fun e' => if e' = j then (1 : ℤ) else 0) - (c (hd j) - c (tl j))) w = 0
        rw [bd_sub hd tl, bd_single hd tl, hcsub_bd]; ring
      unfold bd at hbdZ; linarith

    by_cases heT : e ∈ T
    ·

      have step1 : g e = ∑ e' ∈ T, (c (hd e') e - c (tl e') e) • g e' := by
        have hind : g e = ∑ e' ∈ T, (if e' = e then (1:ℤ) else 0) • g e' := by
          simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', heT, if_true]
        rw [hind]
        refine Finset.sum_congr rfl (fun e' he' => ?_)
        rw [hkey e' he' e]
        simp only [@eq_comm _ e e']
      have step2 : (∑ e' ∈ T, (c (hd e') e - c (tl e') e) • g e') =
          ∑ v : V, c v e • ((∑ e' ∈ T with hd e' = v, g e') - (∑ e' ∈ T with tl e' = v, g e')) := by
        simp only [sub_smul, Finset.sum_sub_distrib, smul_sub, Finset.smul_sum]
        congr 1
        ·
          rw [← Finset.sum_fiberwise T hd (fun e' => c (hd e') e • g e')]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          refine Finset.sum_congr rfl (fun e' he' => ?_)
          simp only [Finset.mem_filter] at he'; rw [he'.2]
        · rw [← Finset.sum_fiberwise T tl (fun e' => c (tl e') e • g e')]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          refine Finset.sum_congr rfl (fun e' he' => ?_)
          simp only [Finset.mem_filter] at he'; rw [he'.2]
      have step3 : ∀ v, (∑ e' ∈ T with hd e' = v, g e') - (∑ e' ∈ T with tl e' = v, g e') =
          (∑ e' with hd e' = v, g e') - (∑ e' with tl e' = v, g e') := by
        intro v
        have hset1 : univ.filter (fun x => hd x = v ∧ x ∈ T) = T.filter (fun x => hd x = v) := by
          ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
        have hset2 : univ.filter (fun x => tl x = v ∧ x ∈ T) = T.filter (fun x => tl x = v) := by
          ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
        have hext1 : (∑ e' with hd e' = v, g e') = (∑ e' ∈ T with hd e' = v, g e') := by
          rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (hd · = v)) (· ∈ T)]
          simp only [Finset.filter_filter]
          have h0 : (∑ e' ∈ univ with hd e' = v ∧ e' ∉ T, g e') = 0 :=
            Finset.sum_eq_zero (fun e' he' => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he'
              exact hgTc e' (Finset.mem_compl.mpr he'.2))
          rw [h0, add_zero, hset1]
        have hext2 : (∑ e' with tl e' = v, g e') = (∑ e' ∈ T with tl e' = v, g e') := by
          rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (tl · = v)) (· ∈ T)]
          simp only [Finset.filter_filter]
          have h0 : (∑ e' ∈ univ with tl e' = v ∧ e' ∉ T, g e') = 0 :=
            Finset.sum_eq_zero (fun e' he' => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he'
              exact hgTc e' (Finset.mem_compl.mpr he'.2))
          rw [h0, add_zero, hset2]
        rw [hext1, hext2]
      rw [step1, step2]
      simp only [step3]
      refine Finset.sum_eq_zero (fun v _ => ?_)
      rw [hgK v, sub_self, smul_zero]
    · exact hgTc e (Finset.mem_compl.mpr heT)

end
end Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
