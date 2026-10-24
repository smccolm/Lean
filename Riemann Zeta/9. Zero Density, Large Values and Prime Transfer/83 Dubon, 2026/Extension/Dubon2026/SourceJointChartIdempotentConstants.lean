import Dubon2026.SourceJointChartNonunitNormalization
import Dubon2026.SourceJointChartInverseClearing
import Dubon2026.SourceJointChartLocalizedIntersection
import Dubon2026.SourceJointChartOverlapTorsion
import Dubon2026.SourceJointChartIdempotentGluing
import Dubon2026.SourceJointChartNonunitPowers
import Dubon2026.SourceJointChartResidueAlgebras

/-! DUB-17/18 -> Kummer genus inequality -> common residue-chart constants.
This is the exact residue-idempotent step. Finite generation of the actual
overlap quotient remains an explicit upstream hypothesis; it is not a
completion claim. The original-chart equalizer, nonunit normalization,
Krull-dimension power divisibility and abstract gluing inputs are proved.
Adapted from Apache-2.0 FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)
  (f : F) (hf : ∀ i, f ∈ (R i).integers) (htrL : Transcendental L f)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
  [∀ i, FiniteDimensional (IntermediateField.adjoin (ResidueField A)
    ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
  (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) =
    Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)

include hR in
omit [Fintype ι] in

theorem subsingleton_of_maximalIdeal_eq_bot (hm : ∀ π ∈ maximalIdeal A, π = 0) (i j : ι) : i = j := by
  have hall : ∀ x : L, x ∈ A := fun x => by
    by_contra hx
    have hinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
    have hx0 : x ≠ 0 := by rintro rfl; exact hx A.zero_mem
    have h1 : 1 < A.valuation x := not_le.mp fun h => hx ((A.valuation_le_one_iff x).mp h)
    have h2 : A.valuation x⁻¹ < 1 := (Valuation.one_lt_val_iff _ hx0).mp h1
    have hmax : (⟨x⁻¹, hinv⟩ : A) ∈ maximalIdeal A := (A.valuation_lt_one_iff _).mpr h2
    have := congrArg Subtype.val (hm _ hmax)
    exact hx0 (inv_eq_zero.mp this)
  have htop : ∀ i (g : F), g ∈ (R i).integers := fun i g => by
    by_cases hg0 : g = 0
    · rw [hg0]; exact zero_mem _
    obtain ⟨c, hcg, hres⟩ := (R i).exists_smul_mem g hg0
    have hc0 : c ≠ 0 := by
      intro hc
      apply hres
      have hz : (⟨c • g, hcg⟩ : (R i).integers) = 0 :=
        Subtype.ext (by change c • g = 0; rw [hc, zero_smul])
      rw [hz, map_zero]
    have : g = algebraMap L F c⁻¹ * (c • g) := by
      rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
    rw [this]
    exact mul_mem (((R i).algebraMap_mem_iff _).mpr (hall _)) hcg
  apply hR
  show (R i).integers = (R j).integers
  ext g
  exact ⟨fun _ => htop j g, fun _ => htop i g⟩

include hR htrL htr heq in

theorem forall_eq_one_of_idempotent_of_finite_overlap [IsAlgClosed L] [CharZero L]
    [Ring.KrullDimLE 1 A] (hfi : ∀ i, f⁻¹ ∈ (R i).integers)
    [Module.Finite A (overlapQuotient R f hf hfi)]
    (e : ∀ i, Fb i) (he : e ∈ JointChartAssembly.ST R f) (he' : e ∈ JointChartAssembly.ST R f⁻¹) (h01 : ∀ i, e i = 0 ∨ e i = 1)
    {i₀ : ι} (hi₀ : e i₀ = 1) : ∀ i, e i = 1 := by
  classical
  by_cases hm : ∃ π ∈ maximalIdeal A, π ≠ 0
  swap
  · have hm' : ∀ π ∈ maximalIdeal A, π = 0 := fun π hπ => by_contra fun h => hm ⟨π, hπ, h⟩
    intro i
    rw [subsingleton_of_maximalIdeal_eq_bot R hR hm' i i₀]
    exact hi₀
  obtain ⟨π, hπ, hπ0⟩ := hm
  have hf0 : f ≠ 0 := JointChartAssembly.ne_zero_of_transcendental htrL
  have hf' : ∀ i, f⁻¹ ∈ (R i).integers := hfi
  have hS' : ∀ u ∈ Sg R f⁻¹, ∃ m : ℕ, u * f ^ m ∈ Sg R f := exists_mul_pow_mem_Sg R f hf htrL

  have hPle : Pg R f hf ≤ Ppp R f hf := Pg_le_Ppp R hf
  have hP'le : Pg R f⁻¹ hf' ≤ Ppp R f hf := Pinv_le_Ppp R hf hf' hf0 hS'
  set u : Pg R f hf →ₐ[A] Ppp R f hf := Subalgebra.inclusion hPle with hu_def
  set u' : Pg R f⁻¹ hf' →ₐ[A] Ppp R f hf := Subalgebra.inclusion hP'le with hu'_def

  obtain ⟨et, hetS, hetres⟩ := (mem_residue_chart_iff R f e).mp he
  obtain ⟨et', het'S, het'res⟩ := (mem_residue_chart_iff R f⁻¹ e).mp he'

  have hsqS : et * et - et ∈ Sg R f := sub_mem (mul_mem hetS hetS) hetS
  have hsq : ∀ i, (R i).residue ⟨et * et - et, hsqS.1 i⟩ = 0 := fun i => by
    have : (⟨et * et - et, hsqS.1 i⟩ : (R i).integers) = ⟨et, hetS.1 i⟩ * ⟨et, hetS.1 i⟩ - ⟨et, hetS.1 i⟩ :=
      rfl
    rw [this, map_sub, map_mul, hetres i]
    rcases h01 i with h | h <;> simp [h]
  obtain ⟨a₁, ha₁, w₁, hw₁S, hw₁⟩ := exists_nonunit_factor_in_chart A Fb R hR f hf htr heq f _ hsqS hsq
  have hsqS' : et' * et' - et' ∈ Sg R f⁻¹ := sub_mem (mul_mem het'S het'S) het'S
  have hsq' : ∀ i, (R i).residue ⟨et' * et' - et', hsqS'.1 i⟩ = 0 := fun i => by
    have : (⟨et' * et' - et', hsqS'.1 i⟩ : (R i).integers)
        = ⟨et', het'S.1 i⟩ * ⟨et', het'S.1 i⟩ - ⟨et', het'S.1 i⟩ := rfl
    rw [this, map_sub, map_mul, het'res i]
    rcases h01 i with h | h <;> simp [h]
  obtain ⟨a₁', ha₁', w₁', hw₁'S, hw₁'⟩ :=
    exists_nonunit_factor_in_chart A Fb R hR f hf htr heq f⁻¹ _ hsqS' hsq'

  obtain ⟨m, hm⟩ := hS' et' het'S
  have hdS : (et - et') * f ^ m ∈ Sg R f := by
    rw [sub_mul]
    exact sub_mem (mul_mem hetS (pow_mem (self_mem_Sg R hf) m)) hm
  have hdres : ∀ i, (R i).residue ⟨(et - et') * f ^ m, hdS.1 i⟩ = 0 := fun i => by
    have : (⟨(et - et') * f ^ m, hdS.1 i⟩ : (R i).integers)
        = (⟨et, hetS.1 i⟩ - ⟨et', het'S.1 i⟩) * ⟨f, hf i⟩ ^ m := by
      apply Subtype.ext
      simp
    rw [this, map_mul, map_sub, hetres i, het'res i, sub_self, zero_mul]
  obtain ⟨a₂, ha₂, w₂, hw₂S, hw₂⟩ := exists_nonunit_factor_in_chart A Fb R hR f hf htr heq f _ hdS hdres

  have h0 : ∀ (x : Pg R f hf) (x' : Pg R f⁻¹ hf'), u x = u' x' →
      ∃ r : A, x = algebraMap A (Pg R f hf) r ∧ x' = algebraMap A (Pg R f⁻¹ hf') r := by
    intro x x' hxx'
    have heqF : (x : F) = x' := by
      have := congrArg Subtype.val hxx'
      simpa [hu_def, hu'_def, Subalgebra.coe_inclusion] using this
    letI : Nonempty ι := ⟨i₀⟩
    obtain ⟨c, hc⟩ := constant_of_mem_localized_charts R f hf hf' htrL (x : F) x.2
      (by rw [heqF]; exact x'.2)
    exact ⟨c, Subtype.ext hc, Subtype.ext (heqF.symm.trans hc)⟩

  obtain ⟨a, ha0, hator⟩ := exists_chart_torsion_annihilator R f hf hf'
  have haπ0 : a * π ≠ 0 := mul_ne_zero ha0 hπ0
  have htor : ∀ y : Ppp R f hf,
      (∃ (p : Pg R f hf) (p' : Pg R f⁻¹ hf'), (a * π) • y = u p + u' p') →
      ∃ (p : Pg R f hf) (p' : Pg R f⁻¹ hf'), a • y = u p + u' p' := by
    rintro y ⟨p, p', hy⟩
    have h1 : (a * π) • (y : F) ∈ (Pg R f hf).toSubmodule ⊔ (Pg R f⁻¹ hf').toSubmodule := by
      have := congrArg Subtype.val hy
      simp only [Subalgebra.coe_smul, Subalgebra.coe_add, hu_def, hu'_def,
        Subalgebra.coe_inclusion] at this
      rw [this]
      exact add_mem (Submodule.mem_sup_left p.2) (Submodule.mem_sup_right p'.2)
    have h2 := hator y y.2 (a * π) haπ0 h1
    obtain ⟨q, hq, q', hq', hqq⟩ := Submodule.mem_sup.mp h2
    refine ⟨⟨q, hq⟩, ⟨q', hq'⟩, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_smul, Subalgebra.coe_add, hu_def, hu'_def, Subalgebra.coe_inclusion]
    exact hqq.symm

  have hnil : ∀ c ∈ maximalIdeal A, ∃ n : ℕ, a * π ∣ c ^ n := fun c hc =>
    exists_dvd_pow haπ0 hc

  set eP : Pg R f hf := ⟨et, Sg_le_Pg R hf hetS⟩ with heP_def
  set eP' : Pg R f⁻¹ hf' := ⟨et', Sg_le_Pg R hf' het'S⟩ with heP'_def
  have heP : eP * eP - eP ∈ (maximalIdeal A).map (algebraMap A (Pg R f hf)) := by
    have : eP * eP - eP = a₁ • (⟨w₁, Sg_le_Pg R hf hw₁S⟩ : Pg R f hf) :=
      Subtype.ext (by simp [heP_def] at hw₁ ⊢; exact hw₁)
    rw [this, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha₁)
  have heP' : eP' * eP' - eP' ∈ (maximalIdeal A).map (algebraMap A (Pg R f⁻¹ hf')) := by
    have : eP' * eP' - eP' = a₁' • (⟨w₁', Sg_le_Pg R hf' hw₁'S⟩ : Pg R f⁻¹ hf') :=
      Subtype.ext (by simp [heP'_def] at hw₁' ⊢; exact hw₁')
    rw [this, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha₁')
  have hwP'' : w₂ * (f ^ m)⁻¹ ∈ Ppp R f hf :=
    mem_Ppp_of_mul_mul_pow_mem R hf IsGoodAt.one m
      (by rw [map_one, mul_one, inv_mul_cancel_right₀ (pow_ne_zero m hf0)]; exact hw₂S)
  have hu : u eP - u' eP' ∈ (maximalIdeal A).map (algebraMap A (Ppp R f hf)) := by
    have : u eP - u' eP' = a₂ • (⟨w₂ * (f ^ m)⁻¹, hwP''⟩ : Ppp R f hf) := by
      apply Subtype.ext
      simp only [Subalgebra.coe_sub, Subalgebra.coe_smul, hu_def, hu'_def, Subalgebra.coe_inclusion,
        heP_def, heP'_def]
      show et - et' = (a₂ : L) • (w₂ * (f ^ m)⁻¹)
      rw [← smul_mul_assoc, ← hw₂, mul_inv_cancel_right₀ (pow_ne_zero m hf0)]
    rw [this, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha₂)

  obtain ⟨r, hr, -⟩ :=
    exists_common_constant_mod_maximalIdeal
      u u' h0 a π hπ hnil htor eP eP' heP heP' hu

  have hconst : ∀ i, e i = algebraMap (ResidueField A) (Fb i) (IsLocalRing.residue A r) := fun i => by
    have hlt : (R i).integers.valuation (et - algebraMap L F r) < 1 := by
      have := valuation_lt_of_mem_map R hf hr i
      simp [heP_def, Subalgebra.coe_algebraMap] at this
      exact this
    have hmemd : et - algebraMap L F r ∈ (R i).integers := (mem_iff_le _ _).mpr hlt.le
    have hres0 : (R i).residue ⟨et - algebraMap L F r, hmemd⟩ = 0 :=
      (residue_eq_zero_iff _ _).mpr hlt
    have hsplit : (⟨et, hetS.1 i⟩ : (R i).integers)
        = constHom (R i) r + ⟨et - algebraMap L F r, hmemd⟩ := by
      apply Subtype.ext
      simp
    rw [← hetres i, hsplit, map_add, hres0, add_zero, residue_constHom]
  have hr1 : IsLocalRing.residue A r = 1 :=
    (algebraMap (ResidueField A) (Fb i₀)).injective (by rw [← hconst i₀, hi₀, map_one])
  intro i
  rw [hconst i, hr1, map_one]

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
