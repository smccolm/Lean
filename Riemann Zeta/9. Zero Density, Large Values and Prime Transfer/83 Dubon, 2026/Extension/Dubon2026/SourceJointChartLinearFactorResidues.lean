import Dubon2026.SourceJointChartFullBasis

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap ->
controlled denominators. Polynomial uniqueness in the residue chart
directly excludes a nonzero constant coefficient at a coordinate linear
factor. Reducing the identity and evaluating at the root replaces the
external small-numerator and primitive-polynomial contradiction. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly

theorem residue_coeff_zero_of_chart_linear_factor
    {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
    {ι J : Type*} [Fintype J] {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (z : J → F) (hz : ∀ j i, z j ∈ (R i).integers)
    (huniq : ∀ q q' : J → (ResidueField A)[X],
      ∑ j, aeval (rv R f hf) (q j) * rv R (z j) (hz j) =
        ∑ j, aeval (rv R f hf) (q' j) * rv R (z j) (hz j) → q = q')
    (hgen : ∀ h ∈ ST R f, ∃ q : J → (ResidueField A)[X],
      h = ∑ j, aeval (rv R f hf) (q j) * rv R (z j) (hz j))
    (a : A) (c : J → A) (y : F) (hy : y ∈ Sg R f)
    (he : ∑ j, (c j : L) • z j = (f - algebraMap L F a) * y) :
    ∀ j, IsLocalRing.residue A (c j) = 0 := by
  classical
  obtain ⟨p, hp⟩ := hgen (rv R y hy.1)
    ((mem_residue_chart_iff R f _).mpr ⟨y, hy, fun _ => rfl⟩)
  have hres (i : ι) :
      ∑ j, algebraMap (ResidueField A) (Fb i) (IsLocalRing.residue A (c j)) *
        (R i).residue ⟨z j, hz j i⟩ =
      ((R i).residue ⟨f, hf i⟩ - algebraMap (ResidueField A) (Fb i) (IsLocalRing.residue A a)) *
        (R i).residue ⟨y, hy.1 i⟩ := by
    have hsum := Joint.sum_smul_mem R z hz Finset.univ c i
    have hei : (⟨∑ j, (c j : L) • z j, hsum⟩ : (R i).integers) =
        (⟨f, hf i⟩ - constHom (R i) a) * ⟨y, hy.1 i⟩ := by
      apply Subtype.ext
      exact he
    have hh := congrArg (R i).residue hei
    rw [Joint.residue_sum_smul, map_mul, map_sub, residue_constHom] at hh
    simpa only [Algebra.smul_def, Joint.jointRes] using hh
  have hpoly := huniq (fun j => C (IsLocalRing.residue A (c j)))
    (fun j => (X - C (IsLocalRing.residue A a)) * p j) (by
      funext i
      simp only [Finset.sum_apply, Pi.mul_apply, aeval_pi_apply₂, map_mul, map_sub,
        aeval_X, aeval_C, mul_assoc, ← Finset.mul_sum]
      have hi := congrFun hp i
      simp only [Finset.sum_apply, Pi.mul_apply, aeval_pi_apply₂] at hi
      rw [← hi]
      exact hres i)
  intro j
  have hj := congrArg (Polynomial.eval (IsLocalRing.residue A a)) (congrFun hpoly j)
  simpa only [eval_C, eval_mul, eval_sub, eval_X, sub_self, zero_mul] using hj

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
