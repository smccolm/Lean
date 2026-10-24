import Dubon2026.SourceJointReductionDimension

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
genus inequality -> the common residue chart consists of constants.
The needed common nonunit factor follows from the proved dimension equality
on the one-dimensional span of the function. No further general adapted
basis construction is required. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing

theorem exists_nonunit_smul_joint_integral
    {L F : Type*} [Field L] (A : ValuationSubring L) [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [∀ i, FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) =
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (V : Submodule L F) (u : F) (hu : ∀ i, u ∈ (R i).integers) (huV : u ∈ V)
    (hres : ∀ i, (R i).residue ⟨u, hu i⟩ = 0) :
    ∃ (a : A) (z : F), ¬ IsUnit a ∧ (∀ i, z ∈ (R i).integers) ∧ z ∈ V ∧
      u = (a : L) • z := by
  classical
  by_cases hu0 : u = 0
  · exact ⟨0, 0, not_isUnit_zero, fun _ => zero_mem _, V.zero_mem, by simp [hu0]⟩
  let U : Submodule L F := Submodule.span L {u}
  have hd := finrank_joint_residue_span A Fb R hR f hf htr heq U
  have hd1 : Module.finrank L U = 1 := finrank_span_singleton hu0
  have hex : ∃ (z : F) (hz : ∀ i, z ∈ (R i).integers), z ∈ U ∧
      ∃ i, (R i).residue ⟨z, hz i⟩ ≠ 0 := by
    by_contra hn
    push Not at hn
    have hs : Submodule.span (ResidueField A)
        {h : ∀ i, Fb i | ∃ z : F, ∃ hz : ∀ i, z ∈ (R i).integers,
          z ∈ U ∧ ∀ i, (R i).residue ⟨z, hz i⟩ = h i} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro h ⟨z, hz, hzU, hzres⟩
      funext i
      exact (hzres i).symm.trans (hn z hz hzU i)
    rw [hs, finrank_bot, hd1] at hd
    omega
  obtain ⟨z, hz, hzU, i, hzi⟩ := hex
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzU
  have hc0 : c ≠ 0 := by
    intro h0
    have hz0 : z = 0 := by rw [← hc, h0, zero_smul]
    exact hzi (by rw [show (⟨z, hz i⟩ : (R i).integers) = 0 from Subtype.ext hz0, map_zero])
  have hcA : c ∉ A := by
    intro hmem
    have he : (⟨z, hz i⟩ : (R i).integers) = constHom (R i) ⟨c, hmem⟩ * ⟨u, hu i⟩ := by
      apply Subtype.ext
      exact hc.symm.trans (Algebra.smul_def c u)
    apply hzi
    rw [he, map_mul, residue_constHom, hres i, mul_zero]
  have hci : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  let a : A := ⟨c⁻¹, hci⟩
  have ha : ¬ IsUnit a := by
    intro ha
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    have hb' : c⁻¹ * (b : L) = 1 := congrArg Subtype.val hb
    have hbc : (b : L) = c := by
      calc
        (b : L) = c * (c⁻¹ * (b : L)) := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
        _ = c := by rw [hb', mul_one]
    exact hcA (hbc ▸ b.2)
  refine ⟨a, z, ha, hz, ?_, ?_⟩
  · rw [← hc]
    exact V.smul_mem c huV
  · rw [← hc, smul_smul]
    change u = (c⁻¹ * c) • u
    rw [inv_mul_cancel₀ hc0, one_smul]

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
