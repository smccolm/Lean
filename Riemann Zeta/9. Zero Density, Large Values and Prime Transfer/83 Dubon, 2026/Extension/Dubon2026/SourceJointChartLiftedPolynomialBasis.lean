import Dubon2026.SourceJointChartPolynomialBasis
import Dubon2026.SourceJointChartPolynomialGenerators

/-! DUB-17/18 -> Kummer power lifting -> common residue constants -> finite
localized overlap. The actual joint residue chart has a finite polynomial
basis, and every basis vector lifts to the original integral chart. The
actual separating coordinate replaces the external general normalization
finiteness input. No freeness or lifting certificate is assumed. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing
open JointChartAssembly

variable {L F : Type*} [Field L] (A : ValuationSubring L) [Field F] [Algebra L F]
  {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
  (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)
  (f : F) (hf : ∀ i, f ∈ (R i).integers)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
  [∀ i, FiniteDimensional (IntermediateField.adjoin (ResidueField A)
    ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
  [∀ i, Algebra.IsSeparable (IntermediateField.adjoin (ResidueField A)
    ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)]
  (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) =
    Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)

include hR htr heq in
theorem exists_lifted_residue_polynomial_basis :
    ∃ (d : ℕ) (z : Fin d → F) (hz : ∀ σ i, z σ ∈ (R i).integers),
      (∀ σ, z σ ∈ originalChart (L := L) f) ∧
      (∀ q q' : Fin d → (ResidueField A)[X],
        ∑ σ, aeval (rv R f hf) (q σ) * rv R (z σ) (hz σ) =
          ∑ σ, aeval (rv R f hf) (q' σ) * rv R (z σ) (hz σ) → q = q') ∧
      (∀ h ∈ ST R f, ∃ q : Fin d → (ResidueField A)[X],
        h = ∑ σ, aeval (rv R f hf) (q σ) * rv R (z σ) (hz σ)) ∧
      (∀ (d' : ℕ) (zb' : Fin d' → ∀ i, Fb i), (∀ τ, zb' τ ∈ ST R f) →
        (∀ q q' : Fin d' → (ResidueField A)[X],
          ∑ τ, aeval (rv R f hf) (q τ) * zb' τ =
            ∑ τ, aeval (rv R f hf) (q' τ) * zb' τ → q = q') → d' ≤ d) := by
  classical
  letI (i : ι) : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({rv R f hf i} : Set (Fb i))) (Fb i) :=
    inferInstanceAs (FiniteDimensional (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i))
  letI (i : ι) : Algebra.IsSeparable
      (IntermediateField.adjoin (ResidueField A) ({rv R f hf i} : Set (Fb i))) (Fb i) :=
    inferInstanceAs (Algebra.IsSeparable (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i))
  obtain ⟨m, g, hg⟩ := exists_joint_integral_polynomial_generators Fb (rv R f hf) htr
  have hgen : ∀ h ∈ ST R f, ∃ q : Fin m → (ResidueField A)[X],
      h = ∑ c, aeval (rv R f hf) (q c) * g c :=
    fun h hh => hg h (residue_chart_isIntegral A Fb R hR f hf htr heq h hh)
  have hstable : ∀ h ∈ ST R f, rv R f hf * h ∈ ST R f := by
    intro h hh
    rw [← residueChartAlgebra_toSubmodule] at hh ⊢
    exact (residueChartAlgebra R f).mul_mem
      ⟨f, self_mem_Sg R hf, fun _ => rfl⟩ hh
  have htf : ∀ (q : (ResidueField A)[X]) (h : ∀ i, Fb i),
      aeval (rv R f hf) q * h = 0 → q = 0 ∨ h = 0 := by
    intro q h he
    by_cases hq : q = 0
    · exact Or.inl hq
    right
    funext i
    have hi := congrFun he i
    simp only [Pi.mul_apply, aeval_pi_apply₂, Pi.zero_apply] at hi
    apply (mul_eq_zero.mp hi).resolve_left
    intro hzero
    apply hq
    exact (transcendental_iff_injective.mp (htr i)) (hzero.trans (map_zero _).symm)
  obtain ⟨d, zb, hzb, huniq, hspan, hcard⟩ :=
    exists_polynomial_basis (rv R f hf) (ST R f) hstable htf g hgen
  choose z hz hr using fun σ => (mem_residue_chart_iff R f (zb σ)).mp (hzb σ)
  have hrv : ∀ σ, rv R (z σ) (hz σ).1 = zb σ := fun σ => funext (hr σ)
  refine ⟨d, z, fun σ => (hz σ).1, fun σ => (hz σ).2, ?_, ?_, hcard⟩
  · simpa only [hrv] using huniq
  · simpa only [hrv] using hspan

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
