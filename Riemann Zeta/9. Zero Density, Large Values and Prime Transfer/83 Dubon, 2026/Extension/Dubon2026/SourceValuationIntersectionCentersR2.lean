import Dubon2026.SourceValuationSimultaneousDenominators

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

/-- The subring integral at every valuation in the finite family. -/
def inter (R : ι → ValuationSubring K) : Subring K := ⨅ j, (R j).toSubring

theorem mem_inter {R : ι → ValuationSubring K} {z : K} : z ∈ inter R ↔ ∀ j, z ∈ R j := by
  simp [inter, Subring.mem_iInf]

/-- The prime ideal cut out by one valuation on the common integral subring. -/
def centre (R : ι → ValuationSubring K) (j : ι) : Ideal (inter R) where
  carrier := {b | (R j).valuation (b : K) < 1}
  add_mem' {a b} ha hb := by
    show (R j).valuation ((a : K) + b) < 1
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by show (R j).valuation ((0 : inter R) : K) < 1; simp
  smul_mem' c b hb := by
    show (R j).valuation ((c : K) * b) < 1
    rw [map_mul]
    calc (R j).valuation (c : K) * (R j).valuation (b : K)
        ≤ 1 * (R j).valuation (b : K) := by
          gcongr
          exact ((R j).valuation_le_one_iff _).mpr (mem_inter.mp c.2 j)
      _ < 1 := by rwa [one_mul]

theorem mem_centre {R : ι → ValuationSubring K} {j : ι} {b : inter R} :
    b ∈ centre R j ↔ (R j).valuation (b : K) < 1 := Iff.rfl

theorem valuation_eq_one_of_not_mem_centre {R : ι → ValuationSubring K} {j : ι} {b : inter R}
    (hb : b ∉ centre R j) : (R j).valuation (b : K) = 1 :=
  le_antisymm (((R j).valuation_le_one_iff _).mpr (mem_inter.mp b.2 j)) (not_lt.mp hb)

theorem centre_isPrime (R : ι → ValuationSubring K) (j : ι) : (centre R j).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    show ¬ (R j).valuation ((1 : inter R) : K) < 1
    simp
  · intro a b hab
    by_contra h
    push Not at h
    have ha := valuation_eq_one_of_not_mem_centre h.1
    have hb := valuation_eq_one_of_not_mem_centre h.2
    have : (R j).valuation ((a * b : inter R) : K) = 1 := by
      show (R j).valuation ((a : K) * b) = 1
      rw [map_mul, ha, hb, one_mul]
    have hab' : (R j).valuation ((a * b : inter R) : K) < 1 := hab
    rw [this] at hab'
    exact lt_irrefl _ hab'

theorem isUnit_of_forall_not_mem_centre {R : ι → ValuationSubring K} (i : ι) {b : inter R}
    (hb : ∀ j, b ∉ centre R j) : IsUnit b := by
  have hv : ∀ j, (R j).valuation (b : K) = 1 := fun j => valuation_eq_one_of_not_mem_centre (hb j)
  have hb0 : (b : K) ≠ 0 := by
    intro h
    have := hv i
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hinv : (b : K)⁻¹ ∈ inter R := by
    refine mem_inter.mpr fun j => ?_
    rw [← (R j).valuation_le_one_iff, map_inv₀, hv j, inv_one]
  exact IsUnit.of_mul_eq_one ⟨(b : K)⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hb0))

theorem exists_le_centre [Fintype ι] {R : ι → ValuationSubring K} (i : ι) {J : Ideal (inter R)}
    (hJ : J ≠ ⊤) : ∃ j, J ≤ centre R j := by
  classical
  have hsub : (J : Set (inter R)) ⊆ ⋃ j ∈ (↑(Finset.univ : Finset ι) : Set ι), (centre R j : Set (inter R)) := by
    intro b hbJ
    by_contra hnot
    have hb : ∀ j, b ∉ centre R j := fun j hj => hnot (by
      simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe]
      exact ⟨j, hj⟩)
    exact hJ (Ideal.eq_top_of_isUnit_mem J hbJ (isUnit_of_forall_not_mem_centre i hb))
  obtain ⟨j, -, hj⟩ := (Ideal.subset_union_prime i i (fun j _ _ _ => centre_isPrime R j)).mp hsub
  exact ⟨j, hj⟩

theorem le_of_centre_le_centre [Fintype ι] {R : ι → ValuationSubring K} {i j : ι}
    (h : centre R i ≤ centre R j) : R j ≤ R i := by
  intro x hx
  obtain ⟨t, htB, htxB, htu⟩ := exists_mul_mem_forall R x
  have htj : (R j).valuation t = 1 := htu j hx
  have htni : (⟨t, mem_inter.mpr htB⟩ : inter R) ∉ centre R i := by
    intro hti
    have htj' := h hti
    rw [mem_centre] at htj'
    exact htj'.ne htj
  have hti : (R i).valuation t = 1 := valuation_eq_one_of_not_mem_centre htni
  have ht0 : t ≠ 0 := by intro h0; rw [h0, map_zero] at hti; exact zero_ne_one hti
  have htinv : t⁻¹ ∈ R i := by
    rw [← (R i).valuation_le_one_iff, map_inv₀, hti, inv_one]
  have : x = t⁻¹ * (t * x) := by field_simp
  rw [this]
  exact (R i).mul_mem _ _ htinv (htxB i)

theorem isCoprime_centre [Fintype ι] {R : ι → ValuationSubring K}
    (hR : ∀ i j, R i ≤ R j → i = j) {i j : ι} (hij : i ≠ j) :
    IsCoprime (centre R i) (centre R j) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨l, hl⟩ := exists_le_centre i hne
  have hil : R l ≤ R i := le_of_centre_le_centre (le_sup_left.trans hl)
  have hjl : R l ≤ R j := le_of_centre_le_centre (le_sup_right.trans hl)
  exact hij ((hR l i hil).symm.trans (hR l j hjl))


end
end Dubon2026.SourceCurve.ValuationApproximation
