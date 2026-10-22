import Dubon2026.SourceMeromorphicDegreeBase

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. Meromorphic functions with a fixed effective
pole bound satisfy a linear relation once their number exceeds its degree
plus one. Removing one leading coefficient reduces the allowed pole degree;
compact holomorphic constancy supplies degree zero. This is the analytic
dimension bound required to identify functions with original field elements.
Adapted from S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.MeromorphicCompact
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable [IsManifold 𝓘(ℂ, ℂ) ω M] [CompactSpace M] [ConnectedSpace M]



theorem bound (n : ℕ) : ∀ (D : M →₀ ℕ), degN D = n → ∀ {ι : Type*} [Fintype ι] (ψ : ι → M → ℂ),
    (∀ i, Bdd D (ψ i)) → n + 1 < Fintype.card ι →
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ x, rd (∑ i, c i • ψ i) x =ᶠ[𝓝[≠] (ctr x)] 0 := by
  classical
  induction n with
  | zero =>
    intro D hD ι _ ψ hψ hcard
    rw [degN_eq_zero_iff] at hD
    subst hD
    exact base ψ hψ hcard
  | succ n ih =>
    intro D hD ι _ ψ hψ hcard

    obtain ⟨x₀, hx₀⟩ : ∃ x₀, 1 ≤ D x₀ := by
      by_contra hcon
      push Not at hcon
      have : D = 0 := by ext x; have := hcon x; simpa using Nat.lt_one_iff.1 this
      rw [this] at hD; simp [degN] at hD
    have hdeg' : degN (D - Finsupp.single x₀ 1) = n := by
      have := degN_sub_single hx₀
      rw [hD] at this
      omega
    let lam : ι → ℂ := fun i => lead (D x₀) (rd (ψ i) x₀) (ctr x₀)
    by_cases hall : ∀ i, lam i = 0
    ·
      exact ih _ hdeg' ψ (fun i => (hψ i).of_lead_eq_zero hx₀ (hall i)) (by omega)
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall

      let ι' := {i : ι // i ≠ i₀}
      let ψ' : ι' → M → ℂ := fun i => ψ i - (lam i / lam i₀) • ψ i₀
      have hψ' : ∀ i : ι', Bdd (D - Finsupp.single x₀ 1) (ψ' i) := by
        intro i
        have hB : Bdd D (ψ' i) := (hψ i).sub ((hψ i₀).smul _)
        refine hB.of_lead_eq_zero hx₀ ?_
        set a : ℂ := -(lam i / lam i₀) with ha
        have hm : MeromorphicAt (a • rd (ψ i₀) x₀) (ctr x₀) := (((hψ i₀).smul a) x₀).1
        have ho : ((-(D x₀ : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (a • rd (ψ i₀) x₀) (ctr x₀) :=
          (((hψ i₀).smul a) x₀).2
        have e : rd (ψ' i) x₀ = rd (ψ i) x₀ + a • rd (ψ i₀) x₀ := by
          funext z; simp [ψ', rd, smul_eq_mul, ha]; ring
        rw [e, lead_add (hψ i x₀).1 (hψ i x₀).2 hm ho, lead_smul a (hψ i₀ x₀).1 (hψ i₀ x₀).2]
        show lam i + -(lam i / lam i₀) * lam i₀ = 0
        field_simp
        ring
      have hcard' : n + 1 < Fintype.card ι' := by
        have : Fintype.card ι' = Fintype.card ι - 1 := by
          simp [ι', Fintype.card_subtype_compl]
        omega
      obtain ⟨c', hc'0, hc'⟩ := ih _ hdeg' ψ' hψ' hcard'

      let c : ι → ℂ := fun i =>
        if h : i = i₀ then -(∑ j : ι', c' j * (lam j / lam i₀)) else c' ⟨i, h⟩
      have hsum : ∑ i, c i • ψ i = ∑ j : ι', c' j • ψ' j := by

        have hL : ∑ i, c i • ψ i = c i₀ • ψ i₀ + ∑ j : ι', c' j • ψ (j : ι) := by
          rw [← Finset.add_sum_erase Finset.univ (fun i => c i • ψ i) (Finset.mem_univ i₀)]
          congr 1
          rw [Finset.sum_subtype (Finset.univ.erase i₀) (p := fun i => i ≠ i₀)
            (fun i => by simp)]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [c, dif_neg j.2]
        have hR : ∑ j : ι', c' j • ψ' j =
            ∑ j : ι', c' j • ψ (j : ι) + (-(∑ j : ι', c' j * (lam j / lam i₀))) • ψ i₀ := by
          simp only [ψ', smul_sub, Finset.sum_sub_distrib, smul_smul, neg_smul, Finset.sum_smul]
          abel
        rw [hL, hR, add_comm]
        simp only [c, dif_pos rfl]
      refine ⟨c, ?_, fun x => by rw [hsum]; exact hc' x⟩
      intro hc0
      apply hc'0
      funext j
      have := congrFun hc0 (j : ι)
      simp only [c, dif_neg j.2, Pi.zero_apply] at this
      exact this


theorem exists_relation_of_degree_lt_card
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (D : M →₀ ℕ) {ι : Type*} [Fintype ι] (ψ : ι → M → ℂ)
    (hψ : ∀ i x, MeromorphicAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hord : ∀ i x, ((-(D x : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x))
    (hcard : (D.sum fun _ n => n) + 1 < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ x : M, (fun z : ℂ => ∑ i, c i * ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] 0 := by
  obtain ⟨c, hc0, hc⟩ := bound (degN D) D rfl ψ (fun i x => ⟨hψ i x, hord i x⟩) hcard
  refine ⟨c, hc0, fun x => ?_⟩
  have : (fun z : ℂ => ∑ i, c i * ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) = rd (∑ i, c i • ψ i) x := by
    funext z
    simp [rd, Finset.sum_apply, smul_eq_mul]
  rw [this]
  exact hc x


end
end Dubon2026.SourceFunctionField.MeromorphicCompact
