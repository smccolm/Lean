import Dubon2026.SourceJointReductionLifts
import Dubon2026.SourceJointReductionPolynomialCover
import Dubon2026.SourceJointReductionSubspaceBasis

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
simultaneous residue dimension. The actual joint residue span preserves
finite-space dimension when the coordinate degrees sum to the original
degree. Existing constant normalizers, adapted bases, coordinate powers
and native fraction-ring independence are reused. Finite residue coordinate
degrees are explicit upstream inputs, supplied by the actual modular fields.
Adapted from frozen Apache-2.0 FLT source, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing

theorem finrank_joint_residue_span
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    [∀ i, FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) =
      Module.finrank L V := by
  classical
  set k := ResidueField A
  haveI : DecidableEq ι := Classical.decEq ι

  let d : ι → ℕ := fun i => Module.finrank
    (IntermediateField.adjoin k ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
  let yb : ∀ i, Fin (d i) → Fb i := fun i => (Module.finBasis _ (Fb i) : _)
  have hyb : ∀ i, LinearIndependent _ (yb i) := fun i => (Module.finBasis _ (Fb i)).linearIndependent
  choose z hzmem hzi hzl using fun τ : Σ i, Fin (d i) => exists_lift R hR τ.1 (yb τ.1 τ.2)
  have heq' : ∑ i, d i = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := heq

  have hrank_le : Module.rank k (Submodule.span k
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) ≤ Module.finrank L V := by

    have hSclosed : ∀ h ∈ Submodule.span k
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i},
        ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i := by
      intro h hh
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hh
      · exact fun x hx => hx
      · exact ⟨0, fun i => zero_mem _, zero_mem V, fun i => by
          simp only [Pi.zero_apply]; exact map_zero _⟩
      · rintro x y - - ⟨ux, hux, huxV, huxR⟩ ⟨uy, huy, huyV, huyR⟩
        refine ⟨ux + uy, fun i => add_mem (hux i) (huy i), add_mem huxV huyV, fun i => ?_⟩
        have e : (⟨ux + uy, _⟩ : (R i).integers) = ⟨ux, hux i⟩ + ⟨uy, huy i⟩ := Subtype.ext rfl
        rw [e, map_add, huxR i, huyR i]; rfl
      · rintro c x - ⟨ux, hux, huxV, huxR⟩
        obtain ⟨ĉ, hĉ⟩ := IsLocalRing.residue_surjective (R := A) c
        refine ⟨(ĉ : L) • ux, fun i => ?_, V.smul_mem _ huxV, fun i => ?_⟩
        · rw [Algebra.smul_def]
          exact mul_mem ((R i).algebraMap_mem_iff _ |>.mpr ĉ.2) (hux i)
        · have hmem' : (ĉ : L) • ux ∈ (R i).integers := by
            rw [Algebra.smul_def]; exact mul_mem ((R i).algebraMap_mem_iff _ |>.mpr ĉ.2) (hux i)
          have e : (⟨(ĉ : L) • ux, hmem'⟩ : (R i).integers) = constHom (R i) ĉ * ⟨ux, hux i⟩ := by
            refine Subtype.ext ?_; simp only [MulMemClass.coe_mul, coe_constHom]
            exact Algebra.smul_def (ĉ : L) ux
          rw [show (⟨(ĉ : L) • ux, _⟩ : (R i).integers) = ⟨(ĉ : L) • ux, hmem'⟩ from rfl,
            e, map_mul, residue_constHom, hĉ, huxR i, Pi.smul_apply]
          exact (Algebra.smul_def c (x i)).symm
    apply rank_le
    intro s hs

    choose u hu huV huRes using fun a : s => hSclosed a.1.1 a.1.2
    have hli := linearIndependent_coe_joint R (fun a : s => u a) (fun a => hu a)
      (by
        have heq : ∀ a i, jointRes R (fun a : s => u a) (fun a => hu a) a i = (a.1 : ∀ i, Fb i) i :=
          fun a i => huRes a i
        have heq' : jointRes R (fun a : s => u a) (fun a => hu a) =
            (Submodule.span k _).subtype ∘ (fun a : s => a.1) := funext fun a => funext fun i => heq a i
        rw [heq']
        exact hs.map' (Submodule.span k _).subtype (Submodule.ker_subtype _))
    have hmemV : ∀ a : s, u a ∈ V := huV
    have : LinearIndependent L (fun a : s => (⟨u a, hmemV a⟩ : V)) :=
      LinearIndependent.of_comp V.subtype hli
    simpa only [Fintype.card_coe] using this.fintype_card_le_finrank
  haveI : Module.Finite k (Submodule.span k
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hrank_le (Cardinal.natCast_lt_aleph0)
  apply le_antisymm (Module.finrank_le_of_rank_le hrank_le)

  obtain ⟨U, hUmem, hUres, T, hT⟩ :=
    exists_joint_unit_mul_mem_span R f hf htr yb hyb z hzmem hzi hzl heq' V
  have hUne : U ≠ 0 := by
    intro h0
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
    ·
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at heq
      exact absurd heq.symm Module.finrank_pos.ne'
    · exact hUres i (by rw [show (⟨U, hUmem i⟩ : (R i).integers) = 0 from Subtype.ext h0, map_zero])
  let μ : F →ₗ[L] F := LinearMap.mulLeft L U
  have hμinj : Function.Injective μ := mul_right_injective₀ hUne
  have hWfin : Module.finrank L (V.map μ) = Module.finrank L V :=
    (Submodule.equivMapOfInjective μ hμinj V).finrank_eq.symm
  let ET : T → F := fun p => f ^ p.1.1 * z p.1.2
  have hETmem : ∀ (p : T) i, ET p ∈ (R i).integers :=
    fun p i => mul_mem (pow_mem (hf i) _) (hzmem p.1.2 i)
  have hET : LinearIndependent k (jointRes R ET hETmem) :=
    (linearIndependent_jointRes_jointFrame R f hf htr yb hyb z hzmem hzi hzl).comp
      (fun p : T => p.1) Subtype.val_injective
  have hWle : V.map μ ≤ Submodule.span L (Set.range ET) := by
    rintro _ ⟨v, hv, rfl⟩; exact hT v hv
  obtain ⟨w, hwmem, hwW, hwLI⟩ :=
    exists_jointResidue_linearIndependent R ET hETmem hET (V.map μ) hWle hWfin

  have hUunit : ∀ i, IsUnit (⟨U, hUmem i⟩ : (R i).integers) :=
    fun i => (R i).isUnit_of_residue_ne_zero (hUres i)
  have hUinv_mem : ∀ i, U⁻¹ ∈ (R i).integers := fun i => by
    have hv : (R i).integers.valuation U = 1 :=
      ((R i).integers.valuation_eq_one_iff ⟨U, hUmem i⟩).mp (hUunit i)
    rw [← (R i).integers.valuation_le_one_iff, map_inv₀, hv, inv_one]
  have hw'mem : ∀ a i, U⁻¹ * w a ∈ (R i).integers := fun a i =>
    mul_mem (hUinv_mem i) (hwmem a i)
  have hw'V : ∀ a, U⁻¹ * w a ∈ V := by
    intro a; obtain ⟨v, hv, hμv⟩ := hwW a
    have : U⁻¹ * w a = v := by
      rw [← hμv]; simp only [μ, LinearMap.mulLeft_apply]
      rw [← mul_assoc, inv_mul_cancel₀ hUne, one_mul]
    rw [this]; exact hv
  have hw'LI : LinearIndependent k (fun a => jointRes R (fun a => U⁻¹ * w a) hw'mem a) := by

    rw [Fintype.linearIndependent_iff]
    intro κ hκ a'
    refine Fintype.linearIndependent_iff.mp hwLI κ ?_ a'
    funext i
    have h := congrFun hκ i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, jointRes] at h ⊢
    have hfact : ∀ a, (R i).residue ⟨U, hUmem i⟩ * (R i).residue ⟨U⁻¹ * w a, hw'mem a i⟩ =
        (R i).residue ⟨w a, hwmem a i⟩ := fun a => by
      rw [← map_mul]; congr 1
      exact Subtype.ext (by push_cast; rw [← mul_assoc, mul_inv_cancel₀ hUne, one_mul])
    calc ∑ a, κ a • (R i).residue ⟨w a, hwmem a i⟩
        = ∑ a, κ a • ((R i).residue ⟨U, hUmem i⟩ * (R i).residue ⟨U⁻¹ * w a, hw'mem a i⟩) := by
          simp_rw [← hfact]
      _ = (R i).residue ⟨U, hUmem i⟩ * ∑ a, κ a • (R i).residue ⟨U⁻¹ * w a, hw'mem a i⟩ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => (mul_smul_comm _ _ _).symm
      _ = 0 := by rw [h, mul_zero]
  have hmemS : ∀ a, jointRes R (fun a => U⁻¹ * w a) hw'mem a ∈ Submodule.span k
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        u ∈ V ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i} :=
    fun a => Submodule.subset_span ⟨U⁻¹ * w a, hw'mem a, hw'V a, fun i => rfl⟩
  have hind2 : LinearIndependent k (fun a => (⟨_, hmemS a⟩ : Submodule.span k _)) :=
    LinearIndependent.of_comp (Submodule.span k _).subtype hw'LI
  simpa using hind2.fintype_card_le_finrank

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
