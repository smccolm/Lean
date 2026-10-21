import Dubon2026.SourceLaurentDegreeTransportFields
import Dubon2026.SourceLaurentCoefficientIndependence

/-! DUB-17/18 -> numerical modular genus -> exact all-level j-map degree
-> transport from the rational original field to its geometric coefficient
extension. Literal Laurent coefficients preserve linear independence.
Polynomial denominator clearing and the existing finite original extension
then preserve the coordinate degree, allowing rational prime-power proofs
to serve the actual algebraically closed coefficient field.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_GeometricBaseChange.lean and
P2M/Sol/S_ModularCurve_relfinrank_laurentBaseChange.lean.
Only the finite degree-transport chain is selected; external global instance
changes, proof options and the infinite-dimensional generalization are omitted.
-/
namespace Dubon2026.SourceFunctionField.DegreeTransport
noncomputable section
open IntermediateField Polynomial

variable (L : Type*) [Field L] [Algebra ℚ L]
variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {t : LaurentSeries ℚ}

theorem linearIndependent_pow_mul (ht : t ∈ F₀) (htr : Transcendental ℚ t) {ι : Type*}
    {v : ι → E₀ F₀ t ht} (hv : LinearIndependent (K₀ t) v) :
    LinearIndependent ℚ fun p : ℕ × ι => t ^ p.1 * ((v p.2 : E₀ F₀ t ht) : LaurentSeries ℚ) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro S μ hS p hp
  let c : ι → LaurentSeries ℚ := fun i =>
    ∑ q ∈ S, if q.2 = i then algebraMap ℚ (LaurentSeries ℚ) (μ q) * t ^ q.1 else 0
  have hcmem : ∀ i, c i ∈ K₀ t := fun i => by
    refine sum_mem fun q _ => ?_
    split_ifs
    · exact mul_mem ((K₀ t).algebraMap_mem _) (pow_mem (mem_adjoin_simple_self ℚ t) _)
    · exact zero_mem _
  have hrel : ∑ i ∈ S.image Prod.snd, (⟨c i, hcmem i⟩ : K₀ t) • v i = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
    have h1 : ∀ i, ((((⟨c i, hcmem i⟩ : K₀ t) • v i : E₀ F₀ t ht)) : LaurentSeries ℚ)
        = ∑ q ∈ S, if q.2 = i then
            algebraMap ℚ (LaurentSeries ℚ) (μ q) * t ^ q.1 * ((v i : E₀ F₀ t ht) : LaurentSeries ℚ) else 0 := by
      intro i
      show c i * ((v i : E₀ F₀ t ht) : LaurentSeries ℚ) = _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun q _ => by by_cases h : q.2 = i <;> simp [h]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun q hq => ?_) hS
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem Prod.snd hq), ← HahnSeries.single_zero_mul_eq_smul,
      SourceDifferential.algebraMap_laurentSeries_apply_alt, mul_assoc]
  have hci : (⟨c p.2, hcmem p.2⟩ : K₀ t) = 0 := hv _ _ hrel p.2 (Finset.mem_image_of_mem Prod.snd hp)
  have hc0 : c p.2 = 0 := congrArg Subtype.val hci
  have hQ : aeval t (∑ q ∈ S, if q.2 = p.2 then monomial q.1 (μ q) else 0) = 0 := by
    rw [map_sum, ← hc0]
    exact Finset.sum_congr rfl fun q _ => by by_cases h : q.2 = p.2 <;> simp [h, aeval_monomial]
  have hQ0 : (∑ q ∈ S, if q.2 = p.2 then monomial q.1 (μ q) else 0 : ℚ[X]) = 0 :=
    transcendental_iff_injective.mp htr (by rw [map_zero]; exact hQ)
  have hco := congrArg (fun P : ℚ[X] => P.coeff p.1) hQ0
  beta_reduce at hco
  rw [finsetSum_coeff, coeff_zero, Finset.sum_eq_single p] at hco
  · simpa using hco
  · intro q _ hqp
    by_cases h2 : q.2 = p.2
    · rw [if_pos h2, coeff_monomial, if_neg]
      intro h1
      exact hqp (Prod.ext h1 h2)
    · rw [if_neg h2, coeff_zero]
  · intro hpS
    exact absurd hp hpS

theorem exists_common_denom {ι : Type*} (s : Finset ι) (g : ι → K L t) :
    ∃ d : L[X], aeval (coeffEmb L t) d ≠ 0 ∧
      ∀ i ∈ s, ∃ p : L[X], aeval (coeffEmb L t) d * (g i : LaurentSeries L) = aeval (coeffEmb L t) p := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a s has ih =>
    obtain ⟨d, hd, hs⟩ := ih
    obtain ⟨r, q, hrq⟩ := (mem_adjoin_simple_iff L _).mp (g a).2
    by_cases hq : aeval (coeffEmb L t) q = 0
    · refine ⟨d, hd, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨0, by rw [hrq, hq, div_zero, mul_zero, map_zero]⟩
      · exact hs i hi
    · refine ⟨d * q, by rw [map_mul]; exact mul_ne_zero hd hq, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · refine ⟨d * r, ?_⟩
        rw [hrq, map_mul, map_mul, mul_assoc, mul_div_cancel₀ _ hq]
      · obtain ⟨p, hp⟩ := hs i hi
        exact ⟨p * q, by rw [map_mul, map_mul, mul_right_comm, hp]⟩

theorem linearIndependent_ψ (ht : t ∈ F₀) (htr : Transcendental ℚ t) {ι : Type*} [Fintype ι]
    {v : ι → E₀ F₀ t ht} (hv : LinearIndependent (K₀ t) v) :
    LinearIndependent (K L t) fun i => ψ L ht (v i) := by
  classical
  have hw := linearIndependent_coeffEmb L (linearIndependent_pow_mul ht htr hv)
  rw [linearIndependent_iff'] at hw ⊢
  intro s g hg i hi
  obtain ⟨d, hd, hs⟩ := exists_common_denom L Finset.univ g
  choose! P hP using hs

  have hg' : ∑ j ∈ s, aeval (coeffEmb L t) (P j) * coeffEmb L ((v j : E₀ F₀ t ht) : LaurentSeries ℚ) = 0 := by
    have := congrArg (fun z : E L F₀ t ht => aeval (coeffEmb L t) d * (z : LaurentSeries L)) hg
    beta_reduce at this
    rw [ZeroMemClass.coe_zero, mul_zero, AddSubmonoidClass.coe_finsetSum, Finset.mul_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IntermediateField.coe_smul]
    show _ = aeval (coeffEmb L t) d * (((g j : K L t) : LaurentSeries L) * ((ψ L ht (v j) : E L F₀ t ht) : LaurentSeries L))
    rw [← mul_assoc, hP j (Finset.mem_univ j)]
    rfl

  let n : ℕ := (s.sup fun j => (P j).natDegree) + 1
  have hdeg : ∀ j ∈ s, (P j).natDegree < n := fun j hj =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (P j).natDegree) hj)
  have hrel : ∑ p ∈ (Finset.range n) ×ˢ s,
      (P p.2).coeff p.1 • coeffEmb L (t ^ p.1 * ((v p.2 : E₀ F₀ t ht) : LaurentSeries ℚ)) = 0 := by
    rw [Finset.sum_product_right, ← hg']
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [aeval_eq_sum_range' (hdeg j hj), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← HahnSeries.single_zero_mul_eq_smul, map_mul, map_pow, Algebra.smul_def,
      SourceDifferential.algebraMap_laurentSeries_apply_alt, mul_assoc]
  have hcoeff : ∀ j ∈ s, ∀ k ∈ Finset.range n, (P j).coeff k = 0 := fun j hj k hk =>
    hw ((Finset.range n) ×ˢ s) (fun p => (P p.2).coeff p.1) hrel (k, j) (Finset.mem_product.mpr ⟨hk, hj⟩)
  have hP0 : P i = 0 := by
    ext k
    by_cases hk : k < n
    · rw [hcoeff i hi k (Finset.mem_range.mpr hk), coeff_zero]
    · rw [coeff_zero, coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i hi) (not_lt.mp hk))]
  have h3 : aeval (coeffEmb L t) d * (g i : LaurentSeries L) = 0 := by
    rw [hP i (Finset.mem_univ i), hP0, map_zero]
  exact Subtype.ext ((mul_eq_zero.mp h3).resolve_left hd)

end
end Dubon2026.SourceFunctionField.DegreeTransport
