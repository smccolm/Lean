import Dubon2026.SourceReductionChartPoleCancellation
import Dubon2026.SourceCurveIntegralChartUniformizer
import Dubon2026.SourceCurveLocalJetDimension
import Dubon2026.SourceCurveUniformizerJets

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy and residual association -> original weight-two
Frobenius/inertia -> modular good reduction -> principal-divisor pushforward.
The order of a reduced integral function is bounded by the sum of the actual
original orders in its exact chart-reduction fiber. The argument consumes
proved integral uniformizers, local quotient dimensions, normalization and
pole cancellation. Only the narrower separating-coordinate and chart-lifting
inputs remain; both are already proved for the actual tame modular charts.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Place

private theorem exists_rescale_fun {L : Type*} [Field L] (A : ValuationSubring L) {m : ℕ}
    (c : Fin m → L) (hc : ∃ i, c i ≠ 0) :
    ∃ j, c j ≠ 0 ∧ ∃ d : Fin m → A, (∀ i, (d i : L) = (c j)⁻¹ * c i) ∧ d j = 1 := by
  classical
  obtain ⟨i, hi⟩ := hc
  obtain ⟨j, -, hj, hmem, -⟩ := exists_normalizer (A := A) Finset.univ c (Finset.mem_univ i) hi
  refine ⟨j, hj, fun k => ⟨(c j)⁻¹ * c k, hmem k (Finset.mem_univ k)⟩,
    fun _ => rfl, Subtype.ext ?_⟩
  exact inv_mul_cancel₀ hj

theorem residue_order_le_sum_fiber_orders
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
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
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧
      (∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) ∧
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits)) :
    Q.ord (R.residue f) ≤ ∑ P ∈ T, D P := by
  classical
  haveI : FiniteDimensional
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin

  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  have hresP : ∀ P : Place L F, Function.Surjective (algebraMap L P.ResidueField) :=
    fun P => (place_residue_bijective_of_finite_coordinate (x : F) P).surjective

  have hxT : ∀ P ∈ T, (x : F) ∈ P.toValuationSubring := by
    intro P hP
    obtain ⟨-, ⟨a, ha⟩, -⟩ := (hT P).mp hP
    have h1 := add_mem (P.toValuationSubring.nonunits_subset ha) (P.algebraMap_mem' (a : L))
    rwa [sub_add_cancel] at h1
  have hDnn : ∀ P ∈ T, 0 ≤ D P := fun P hP => by
    rw [hD]
    exact ord_nonneg_of_mem P (P.mem_of_integral_adjoin (hxT P hP) hfi)
  by_contra hlt
  rw [not_le] at hlt
  have hsum_nn : 0 ≤ ∑ P ∈ T, D P := Finset.sum_nonneg hDnn
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = Q.ord (R.residue f) :=
    ⟨_, Int.toNat_of_nonneg (by omega)⟩

  obtain ⟨tbar, htbar, htQ⟩ := Place.exists_integral_chart_uniformizer (R.residue x) hx Q hQ
  obtain ⟨t, ht, hrt⟩ := hchart tbar htbar
  have htP : ∀ P : ↥T, (t : F) ∈ P.1.toValuationSubring := fun P =>
    P.1.mem_of_integral_adjoin (hxT P.1 P.2) ht

  let r : ↥T → ℕ := fun P => (D P.1).toNat
  haveI hfin' : ∀ P : ↥T, Module.Finite L
      (P.1.toValuationSubring ⧸ (maximalIdeal P.1.toValuationSubring) ^ r P) :=
    fun P => (P.1.finite_quotient_maximalIdeal_pow (hresP P.1) (r P)).1
  let tO : ∀ P : ↥T, P.1.toValuationSubring := fun P => ⟨(t : F), htP P⟩
  let Ψ : (Fin m → L) →ₗ[L]
      (∀ P : ↥T, P.1.toValuationSubring ⧸ (maximalIdeal P.1.toValuationSubring) ^ r P) :=
    Fintype.linearCombination L fun (i : Fin m) (P : ↥T) =>
      Ideal.Quotient.mkₐ L ((maximalIdeal P.1.toValuationSubring) ^ r P) (tO P ^ (i : ℕ))

  have hrank : Module.finrank L
      (∀ P : ↥T, P.1.toValuationSubring ⧸ (maximalIdeal P.1.toValuationSubring) ^ r P) <
      Module.finrank L (Fin m → L) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun]
    have h1 : ((∑ P : ↥T, Module.finrank L
        (P.1.toValuationSubring ⧸ (maximalIdeal P.1.toValuationSubring) ^ r P) : ℕ) : ℤ) ≤
        ∑ P ∈ T, D P := by
      rw [Nat.cast_sum, ← Finset.sum_coe_sort T (fun P => D P)]
      refine Finset.sum_le_sum fun P _ => ?_
      have h3 := (P.1.finite_quotient_maximalIdeal_pow (hresP P.1) (r P)).2
      have h2 : ((r P : ℕ) : ℤ) = D P.1 := Int.toNat_of_nonneg (hDnn P.1 P.2)
      omega
    omega

  obtain ⟨c, hcker, hc0⟩ := (Submodule.ne_bot_iff _).mp (Ψ.ker_ne_bot_of_finrank_lt hrank)
  have hcker' : ∀ P : ↥T, (∑ i : Fin m, c i • tO P ^ (i : ℕ)) ∈
      (maximalIdeal P.1.toValuationSubring) ^ r P := by
    intro P
    have := congrFun (LinearMap.mem_ker.mp hcker) P
    simp only [Ψ, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      ← map_smul, ← map_sum] at this
    rw [Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

  obtain ⟨j, hcj, d, hd, hdj⟩ := exists_rescale_fun A c (Function.ne_iff.mp hc0)
  let h : R.integers := ∑ i : Fin m, constHom R (d i) * t ^ (i : ℕ)
  have hhF' : (h : F) = ∑ i : Fin m, (constHom R (d i) : F) * (t : F) ^ (i : ℕ) := by
    simp only [h, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have hhint : IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) := by
    rw [hhF']
    exact IsIntegral.sum _ fun i _ => ((isIntegral_algebraMap (R := L) (A := F) (x := (d i : L))).tower_top).mul (ht.pow _)
  have hhF : (h : F) = algebraMap L F (c j)⁻¹ *
      ∑ i : Fin m, algebraMap L F (c i) * (t : F) ^ (i : ℕ) := by
    rw [hhF', Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_constHom, hd i, map_mul, mul_assoc]

  have hvan : ∀ P : ↥T, (h : F) = 0 ∨ D P.1 ≤ P.1.ord (h : F) := by
    intro P
    have hy := P.1.le_ord_of_mem_maximalIdeal_pow (r P) _ (hcker' P)
    have hyF : ((∑ i : Fin m, c i • tO P ^ (i : ℕ) : P.1.toValuationSubring) : F) =
        ∑ i : Fin m, algebraMap L F (c i) * (t : F) ^ (i : ℕ) := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, MulMemClass.coe_mul, SubmonoidClass.coe_pow, Place.coe_algebraMap]
    rw [hhF]
    rcases eq_or_ne (∑ i : Fin m, algebraMap L F (c i) * (t : F) ^ (i : ℕ)) 0 with hs0 | hs0
    · left; rw [hs0, mul_zero]
    · right
      rcases hy with hy | hy
      · exact absurd (hyF.symm.trans hy) hs0
      · rw [P.1.ord_mul ((_root_.map_ne_zero _).mpr (inv_ne_zero hcj)) hs0, P.1.ord_algebraMap,
          zero_add, ← hyF]
        have h2 : ((r P : ℕ) : ℤ) = D P.1 := Int.toNat_of_nonneg (hDnn P.1 P.2)
        omega

  have hpk := chart_pole_cancellation R x hx hfin hdeg f hfi hf Q hQ D hD T hT h hhint
    (fun P hP => hvan ⟨P, hP⟩)

  have hres : R.residue h = ∑ i : Fin m,
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A (d i)) * tbar ^ (i : ℕ) := by
    simp only [h, map_sum, map_mul, map_pow, residue_constHom, hrt]
  have hzero := Q.coefficients_eq_zero_of_uniformizer_order htQ m (fun i => IsLocalRing.residue A (d i)) (by
    rw [← hres]
    rcases hpk with hpk | hpk
    · exact Or.inl hpk
    · right; omega)
  have h1 : IsLocalRing.residue A (d j) = 0 := hzero j
  rw [hdj, map_one] at h1
  exact one_ne_zero h1

end
end Dubon2026.SourceCurve.RegularProlongation
