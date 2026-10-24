import Dubon2026.SourceReductionTotalChartOrderEquality

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward.
For integral chart functions, total-order equality and the pointwise fiber
inequality force exact equality at every finite residue chart place, including
places outside the residue divisor support. The proof retains literal orders,
finite support and the exact integral-function reduction relation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors (ResidueField A) Fbar]

theorem sum_fiber_orders_eq_residue_order_of_integral_chart (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    [Algebra.IsSeparable
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar]
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (T : Finset (Place L F))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧ ChartDomain A P (x : F) ∧ ChartReducesTo A R (x : F) P Q)) :
    ∑ P ∈ T, D P = Q.ord (R.residue f) := by
  classical
  set k := IsLocalRing.ResidueField A

  obtain ⟨Dbar, hDbar, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) (R.residue f) hf

  have hE : ∀ P : Place L F, ChartDomain A P (x : F) → ∃! Q', ChartReducesTo A R (x : F) P Q' := fun P hP =>
    existsUnique_reduction_chart_place R x hx hfin hdeg hchart P hP
  let ρ : Place L F → Place k Fbar := fun P =>
    if h : ChartDomain A P (x : F) then (hE P h).exists.choose else Q
  have hρ : ∀ P, ChartDomain A P (x : F) → ChartReducesTo A R (x : F) P (ρ P) := fun P h => by
    simp only [ρ, dif_pos h]
    exact (hE P h).exists.choose_spec
  have hρeq : ∀ P Q', ChartDomain A P (x : F) → (ChartReducesTo A R (x : F) P Q' ↔ ρ P = Q') := fun P Q' h =>
    ⟨fun hred => (hE P h).unique (hρ P h) hred, fun he => he ▸ hρ P h⟩

  have hnonneg : ∀ P, ChartDomain A P (x : F) → 0 ≤ D P := fun P hP => by
    rw [hD]
    obtain ⟨a, ha⟩ := hP
    exact P.ord_nonneg_of_mem (P.mem_of_integral_adjoin
      (mem_of_sub_algebraMap_mem_nonunits P ha) hfi)

  let TP : Finset (Place L F) := D.support.filter fun P => ChartDomain A P (x : F)
  let TQ : Finset (Place k Fbar) := Dbar.support.filter fun Q' => R.residue x ∈ Q'.toValuationSubring
  have hTP : ∀ P, P ∈ TP ↔ (D P ≠ 0 ∧ ChartDomain A P (x : F)) := fun P => by
    simp only [TP, Finset.mem_filter, Finsupp.mem_support_iff]
  have hTQ : ∀ Q', Q' ∈ TQ ↔ (Dbar Q' ≠ 0 ∧ R.residue x ∈ Q'.toValuationSubring) := fun Q' => by
    simp only [TQ, Finset.mem_filter, Finsupp.mem_support_iff]

  have hfib : ∀ Q' P, P ∈ TP.filter (fun P => ρ P = Q') ↔
      (D P ≠ 0 ∧ ChartDomain A P (x : F) ∧ ChartReducesTo A R (x : F) P Q') := fun Q' P => by
    rw [Finset.mem_filter, hTP]
    constructor
    · rintro ⟨⟨h0, hd⟩, he⟩; exact ⟨h0, hd, (hρeq P Q' hd).mpr he⟩
    · rintro ⟨h0, hd, hred⟩; exact ⟨⟨h0, hd⟩, (hρeq P Q' hd).mp hred⟩

  have hMle : ∀ Q', R.residue x ∈ Q'.toValuationSubring →
      Dbar Q' ≤ ∑ P ∈ TP.filter (fun P => ρ P = Q'), D P := fun Q' hQ' => by
    rw [hDbar]
    exact residue_order_le_sum_fiber_orders A R x hx hfin hdeg
      hchart f hfi hf Q' hQ' D hD _ (hfib Q')

  have hG : ∑ P ∈ TP, D P = ∑ Q' ∈ TQ, Dbar Q' := by
    have he := chartOrderSum_eq_residue_chartOrderSum R x hx hfin hdeg hchart f hfi hf
    rw [chartOrderSum_eq_sum _ _ TP (fun P => by rw [hTP, hD]),
      chartOrderSum_eq_sum _ _ TQ (fun Q' => by rw [hTQ, hDbar])] at he
    simpa only [hD, hDbar] using he

  let TP' : Finset (Place L F) := TP.filter fun P => ρ P ∈ TQ
  have h12 : ∑ Q' ∈ TQ, Dbar Q' ≤ ∑ Q' ∈ TQ, ∑ P ∈ TP.filter (fun P => ρ P = Q'), D P :=
    Finset.sum_le_sum fun Q' hQ' => hMle Q' ((hTQ Q').mp hQ').2
  have h23 : ∑ Q' ∈ TQ, ∑ P ∈ TP.filter (fun P => ρ P = Q'), D P = ∑ P ∈ TP', D P := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := TP') (t := TQ) (g := ρ)
      (fun P hP => (Finset.mem_filter.mp hP).2)]
    refine Finset.sum_congr rfl fun Q' hQ' => Finset.sum_congr ?_ fun _ _ => rfl
    ext P
    simp only [TP', Finset.mem_filter]
    constructor
    · rintro ⟨hP, he⟩; exact ⟨⟨hP, he ▸ hQ'⟩, he⟩
    · rintro ⟨⟨hP, -⟩, he⟩; exact ⟨hP, he⟩
  have h34 : ∑ P ∈ TP', D P ≤ ∑ P ∈ TP, D P :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun P hP _ => hnonneg P ((hTP P).mp hP).2
  have h31 : ∑ P ∈ TP', D P = ∑ Q' ∈ TQ, Dbar Q' :=
    le_antisymm (h34.trans hG.le) (h12.trans h23.le)

  have hterm : ∀ Q' ∈ TQ, Dbar Q' = ∑ P ∈ TP.filter (fun P => ρ P = Q'), D P := by
    have heq : ∑ Q' ∈ TQ, Dbar Q' = ∑ Q' ∈ TQ, ∑ P ∈ TP.filter (fun P => ρ P = Q'), D P :=
      le_antisymm h12 (h23.trans_le h31.le)
    exact (Finset.sum_eq_sum_iff_of_le fun Q' hQ' => hMle Q' ((hTQ Q').mp hQ').2).mp heq

  have hall : ∀ P ∈ TP, ρ P ∈ TQ := by
    intro P hP
    by_contra hnot
    have hsplit := Finset.sum_filter_add_sum_filter_not TP (fun P => ρ P ∈ TQ) (fun P => D P)
    have hzero : ∑ P ∈ TP.filter (fun P => ρ P ∉ TQ), D P = 0 := by
      have := h31.trans hG.symm
      change ∑ P ∈ TP', D P + _ = _ at hsplit
      omega
    have hP' : P ∈ TP.filter (fun P => ρ P ∉ TQ) := Finset.mem_filter.mpr ⟨hP, hnot⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg fun P' hP' =>
      hnonneg P' ((hTP P').mp (Finset.mem_filter.mp hP').1).2).mp hzero P hP'
    exact ((hTP P).mp hP).1 this

  have hTeq : T = TP.filter (fun P => ρ P = Q) := by
    ext P; rw [hT, hfib]
  by_cases hQT : Q ∈ TQ
  · rw [hTeq, ← hterm Q hQT, hDbar]
  · have h0 : Dbar Q = 0 := by
      by_contra hne
      exact hQT ((hTQ Q).mpr ⟨hne, hQ⟩)
    have hTempty : T = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun P hP => hQT ?_
      rw [hTeq, Finset.mem_filter] at hP
      exact hP.2 ▸ hall P hP.1
    rw [hTempty, Finset.sum_empty, ← hDbar, h0]

end
end Dubon2026.SourceCurve.RegularProlongation
