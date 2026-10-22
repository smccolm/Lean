import Dubon2026.SourceConstantFieldOrderResidues

/-! DUB-17/18 -> original Picard injectivity -> principal-divisor descent.
Independent constant coefficients prevent cancellation of the least local
order. Adapted from the ord_sum_le and coefficient-representation arguments
in S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing order/unit identities replace the external local foundations.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem ord_sum_le
    (P : Place K F) (P' : Place K' F')
    (hres : Function.Surjective (algebraMap K P.ResidueField))
    (hcomap : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (hord : ∀ f : F, P'.ord (algebraMap F F' f) = P.ord f)
    {ι : Type*} (s : Finset ι) (β : ι → K') (hβ : LinearIndependent K β) (u : ι → F)
    {i : ι} (hi : i ∈ s) (hui : u i ≠ 0) :
    P'.ord (∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (u j)) ≤ P.ord (u i) := by
  classical
  have hφmem : ∀ x : F, x ∈ P.toValuationSubring → algebraMap F F' x ∈ P'.toValuationSubring := by
    intro x hx
    rw [← hcomap] at hx
    exact hx

  set T := s.filter (fun j => u j ≠ 0) with hT
  have hiT : i ∈ T := Finset.mem_filter.2 ⟨hi, hui⟩
  have hTne : T.Nonempty := ⟨i, hiT⟩
  obtain ⟨i₀, hi₀T, hi₀⟩ := Finset.exists_mem_eq_inf' hTne (fun j => P.ord (u j))
  set m := T.inf' hTne (fun j => P.ord (u j)) with hm
  have hm_le : ∀ j ∈ T, m ≤ P.ord (u j) := fun j hj => Finset.inf'_le _ hj
  have hui₀ : u i₀ ≠ 0 := (Finset.mem_filter.1 hi₀T).2
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.1 hi₀T).1
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := irreducible_coe_ne_zero P hπ

  have ho_mem : ∀ j ∈ s, u j * (π : F) ^ (-m) ∈ P.toValuationSubring := by
    intro j hj
    by_cases huj : u j = 0
    · rw [huj, zero_mul]; exact zero_mem _
    apply P.mem_of_ord_nonneg
    rw [P.ord_mul huj (zpow_ne_zero _ hπ0), P.ord_zpow, P.ord_coe_irreducible hπ]
    have := hm_le j (Finset.mem_filter.2 ⟨hj, huj⟩)
    linarith

  have hdig : ∀ j ∈ s, ∃ a : K, ∃ r : P.toValuationSubring,
      r ∈ IsLocalRing.maximalIdeal P.toValuationSubring ∧
      u j * (π : F) ^ (-m) = algebraMap K F a + (r : F) := by
    intro j hj
    obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_maximalIdeal P hres ⟨_, ho_mem j hj⟩
    refine ⟨a, _, ha, ?_⟩
    simp only [AddSubgroupClass.coe_sub, Place.coe_algebraMap]
    ring
  choose! a r har hur using hdig

  have hai₀ : a i₀ ≠ 0 := by
    intro h0
    have hunit : IsUnit (⟨_, ho_mem i₀ hi₀s⟩ : P.toValuationSubring) := by
      apply isUnit_of_ord_eq_zero P
      · intro h
        apply hui₀
        have h' : u i₀ * (π : F) ^ (-m) = 0 := by
          simpa using congrArg Subtype.val h
        rcases mul_eq_zero.1 h' with h'' | h''
        · exact h''
        · exact absurd h'' (zpow_ne_zero _ hπ0)
      · show P.ord (u i₀ * (π : F) ^ (-m)) = 0
        rw [P.ord_mul hui₀ (zpow_ne_zero _ hπ0), P.ord_zpow, P.ord_coe_irreducible hπ, ← hi₀]
        ring
    have heq : (⟨_, ho_mem i₀ hi₀s⟩ : P.toValuationSubring) = r i₀ := by
      apply Subtype.ext
      show u i₀ * (π : F) ^ (-m) = r i₀
      rw [hur i₀ hi₀s, h0, map_zero, zero_add]
    rw [heq] at hunit
    exact (IsLocalRing.mem_maximalIdeal _).1 (har i₀ hi₀s) hunit

  set d : K' := ∑ j ∈ s, a j • β j with hd
  have hd0 : d ≠ 0 := by
    intro h0
    exact hai₀ (linearIndependent_iff'.1 hβ s a h0 i₀ hi₀s)

  have hrmem : ∀ j ∈ s, (⟨algebraMap F F' (r j), hφmem _ (r j).2⟩ : P'.toValuationSubring) ∈
      IsLocalRing.maximalIdeal P'.toValuationSubring := by
    intro j hj
    by_cases hr0 : r j = 0
    · have : (⟨algebraMap F F' (r j), hφmem _ (r j).2⟩ : P'.toValuationSubring) = 0 := by
        apply Subtype.ext
        simp [hr0]
      rw [this]
      exact Ideal.zero_mem _
    apply mem_maximalIdeal_of_ord_pos P'
    show 0 < P'.ord (algebraMap F F' (r j))
    rw [hord]
    exact ord_pos_of_mem_maximalIdeal P (har j hj) hr0
  set Dd : P'.toValuationSubring := ⟨algebraMap K' F' d, P'.algebraMap_mem' d⟩ with hDd
  set Tt : P'.toValuationSubring := ∑ j ∈ s,
    (⟨algebraMap K' F' (β j), P'.algebraMap_mem' (β j)⟩ : P'.toValuationSubring) *
      ⟨algebraMap F F' (r j), hφmem _ (r j).2⟩ with hTt
  have hDunit : IsUnit Dd := by
    apply isUnit_of_ord_eq_zero P'
    · intro h
      have : algebraMap K' F' d = 0 := by simpa [hDd] using congrArg Subtype.val h
      exact hd0 ((algebraMap K' F').injective (by rw [this, map_zero]))
    · exact P'.ord_algebraMap d
  have hTmem : Tt ∈ IsLocalRing.maximalIdeal P'.toValuationSubring :=
    Ideal.sum_mem _ fun j hj => Ideal.mul_mem_left _ _ (hrmem j hj)
  have hunit := isUnit_add_of_mem_maximalIdeal hDunit hTmem
  have hcoe : ((Dd + Tt : P'.toValuationSubring) : F') =
      algebraMap K' F' d + ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j) := by
    simp [hDd, hTt]
  have hne' : algebraMap K' F' d + ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j) ≠ 0 := by
    rw [← hcoe]
    exact_mod_cast hunit.ne_zero
  have hord0 : P'.ord (algebraMap K' F' d +
      ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j)) = 0 := by
    rw [← hcoe]
    exact ord_coe_isUnit P' hunit

  have hS : ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (u j) =
      algebraMap F F' (π : F) ^ m * (algebraMap K' F' d +
        ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j)) := by
    rw [hd, map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have huj : u j = (algebraMap K F (a j) + r j) * (π : F) ^ m := by
      rw [← hur j hj, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
    rw [huj, map_mul, map_add, map_zpow₀, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply K K' F', ← IsScalarTower.algebraMap_apply K F F']
    ring
  rw [hS, P'.ord_mul (zpow_ne_zero _ ((map_ne_zero _).2 hπ0)) hne', P'.ord_zpow, hord,
    P.ord_coe_irreducible hπ, hord0]
  simpa using hm_le i hiT

end
end Dubon2026.SourceCurve.ConstantField
