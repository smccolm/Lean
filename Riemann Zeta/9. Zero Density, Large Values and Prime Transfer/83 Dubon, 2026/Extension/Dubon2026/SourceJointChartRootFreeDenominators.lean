import Dubon2026.SourceJointChartSmallRootCancellation

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap ->
controlled denominators. Repeated cancellation strictly lowers polynomial
degree and leaves a common denominator all of whose roots lie outside the
coefficient valuation ring. This uses only the proved residue-chart basis. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly

theorem exists_denominator_with_roots_outside
    {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
    {ι J : Type*} [Fintype J] {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers) (htrL : Transcendental L f)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (z : J → F) (hz : ∀ j i, z j ∈ (R i).integers)
    (hchart : ∀ j, z j ∈ originalChart L f)
    (huniq : ∀ q q' : J → (ResidueField A)[X],
      ∑ j, aeval (rv R f hf) (q j) * rv R (z j) (hz j) =
        ∑ j, aeval (rv R f hf) (q' j) * rv R (z j) (hz j) → q = q')
    (hgen : ∀ h ∈ ST R f, ∃ q : J → (ResidueField A)[X],
      h = ∑ j, aeval (rv R f hf) (q j) * rv R (z j) (hz j))
    (s : F) (hs : s ∈ originalChart L f) (w : J → F) (hsum : s = ∑ j, w j * z j)
    (D : L[X]) (P : J → L[X]) (hD0 : D ≠ 0)
    (hP : ∀ j, w j * aeval f D = aeval f (P j)) :
    ∃ (T : L[X]) (Q : J → L[X]), T ≠ 0 ∧
      (∀ a ∈ T.roots, 1 < A.valuation a) ∧
      ∀ j, w j * aeval f T = aeval f (Q j) := by
  classical
  suffices ∀ n : ℕ, ∀ D : L[X], ∀ P : J → L[X], D.natDegree = n → D ≠ 0 →
      (∀ j, w j * aeval f D = aeval f (P j)) →
      ∃ (T : L[X]) (Q : J → L[X]), T ≠ 0 ∧
        (∀ a ∈ T.roots, 1 < A.valuation a) ∧
        ∀ j, w j * aeval f T = aeval f (Q j) from this _ D P rfl hD0 hP
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D P hdegree hD hP
    by_cases hex : ∃ a : L, a ∈ A ∧ D.IsRoot a
    · obtain ⟨a, ha, hroot⟩ := hex
      obtain ⟨D₁, P₁, hD₁, hlt, hP₁⟩ := exists_cancel_small_denominator_root
        R f hf htrL htr z hz hchart huniq hgen s hs w hsum D P hD hP ⟨a, ha⟩ hroot
      exact ih D₁.natDegree (by rwa [← hdegree]) D₁ P₁ rfl hD₁ hP₁
    · refine ⟨D, P, hD, ?_, hP⟩
      intro a ha
      by_contra hle
      exact hex ⟨a, (A.valuation_le_one_iff _).mp (not_lt.mp hle), (mem_roots hD).mp ha⟩

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
