import Dubon2026.SourceValuationIntersectionCentersR2

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
actual extending residue fields. Finite valuation approximation supplies
independent residue vectors; the degree-q cover then forces each residue
extension to have degree one. Adapted from the frozen Apache-2.0 FLT
finite-valuation approximation proof (6e837e75355538c7f80bab5b956861e86c4eacc2).
No value-group coarsening or arbitrary-constant normalization is imported. -/
namespace Dubon2026.SourceCurve.ValuationApproximation
noncomputable section
open IsLocalRing ValuationSubring

variable {K : Type*} [Field K] {ι : Type*}

theorem exists_mem_inter_sub_lt [Fintype ι] {R : ι → ValuationSubring K}
    (hR : ∀ i j, R i ≤ R j → i = j) (i : ι) {a : K} (ha : a ∈ R i) :
    ∃ c ∈ inter R, (R i).valuation (c - a) < 1 := by
  classical
  obtain ⟨t, htB, htaB, htu⟩ := exists_mul_mem_forall R a
  have hti : (R i).valuation t = 1 := htu i ha
  let tB : inter R := ⟨t, mem_inter.mpr htB⟩
  let taB : inter R := ⟨t * a, mem_inter.mpr htaB⟩
  set J : Ideal (inter R) := centre R i ⊔ Ideal.span {tB} with hJ
  by_cases hJtop : J = ⊤
  · have h1 : (1 : inter R) ∈ J := hJtop ▸ Submodule.mem_top
    rw [hJ, Submodule.mem_sup] at h1
    obtain ⟨q, hq, r, hr, hqr⟩ := h1
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    refine ⟨(s : K) * (t * a), Subring.mul_mem _ s.2 (mem_inter.mpr htaB), ?_⟩
    have hq' : (q : K) + s * t = 1 := by
      have h := congrArg (fun b : inter R => (b : K)) hqr
      exact h
    have : (s : K) * (t * a) - a = -((q : K) * a) := by linear_combination a * hq'
    rw [this, Valuation.map_neg, map_mul]
    calc (R i).valuation (q : K) * (R i).valuation a
        ≤ (R i).valuation (q : K) * 1 := by
          gcongr
          exact ((R i).valuation_le_one_iff a).mpr ha
      _ < 1 := by rw [mul_one]; exact hq
  · obtain ⟨l, hl⟩ := exists_le_centre i hJtop
    have hli : R l ≤ R i := le_of_centre_le_centre (le_sup_left.trans hl)
    have := hR l i hli
    subst this
    have htJ : tB ∈ J := hJ ▸ Submodule.mem_sup_right (Ideal.mem_span_singleton_self tB)
    have := hl htJ
    rw [mem_centre] at this
    exact absurd hti this.ne

theorem exists_forall_mem_and_sub_mem_nonunits' [Finite ι] (R : ι → ValuationSubring K)
    (hR : ∀ i j, R i ≤ R j → i = j) (a : ι → K) (ha : ∀ i, a i ∈ R i) :
    ∃ z : K, ∀ i, z ∈ R i ∧ z - a i ∈ (R i).nonunits := by
  classical
  cases nonempty_fintype ι
  choose c hcB hc using fun i => exists_mem_inter_sub_lt hR i (ha i)
  have hcop : Pairwise (Function.onFun IsCoprime (centre R)) := fun i j hij => isCoprime_centre hR hij
  obtain ⟨z, hz⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun i => (⟨c i, hcB i⟩ : inter R))
  refine ⟨z, fun i => ⟨mem_inter.mp z.2 i, ?_⟩⟩
  rw [ValuationSubring.mem_nonunits_iff]
  have h1 : (R i).valuation ((z : K) - c i) < 1 := hz i
  have : (z : K) - a i = ((z : K) - c i) + (c i - a i) := by ring
  rw [this]
  exact Valuation.map_add_lt _ h1 (hc i)


end
end Dubon2026.SourceCurve.ValuationApproximation
