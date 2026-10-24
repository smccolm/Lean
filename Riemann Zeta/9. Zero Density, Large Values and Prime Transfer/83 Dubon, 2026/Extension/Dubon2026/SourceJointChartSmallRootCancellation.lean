import Dubon2026.SourceJointChartLinearFactorResidues

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap ->
controlled denominators. A denominator root in the coefficient valuation
ring cancels from every coordinate of an original chart element. The
polynomial residue basis gives the contradiction directly. The algebraic
division step adapts Apache-2.0 FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2; local normalization and residue
uniqueness replace its primitive-polynomial and small-remainder argument. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly

theorem exists_cancel_small_denominator_root
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
    (hP : ∀ j, w j * aeval f D = aeval f (P j))
    (a : A) (hroot : D.IsRoot (a : L)) :
    ∃ (D₁ : L[X]) (P₁ : J → L[X]), D₁ ≠ 0 ∧ D₁.natDegree < D.natDegree ∧
      ∀ j, w j * aeval f D₁ = aeval f (P₁ j) := by
  classical
  obtain ⟨D₁, hD⟩ := dvd_iff_isRoot.mpr hroot
  have hD₁0 : D₁ ≠ 0 := by
    rintro rfl
    exact hD0 (by rw [hD, mul_zero])
  have hdeg : D₁.natDegree < D.natDegree := by
    rw [hD, natDegree_mul (X_sub_C_ne_zero (a : L)) hD₁0, natDegree_X_sub_C]
    omega
  have hQex : ∀ j, ∃ Q : L[X], P j - C ((P j).eval (a : L)) = (X - C (a : L)) * Q :=
    fun _ => X_sub_C_dvd_sub_C_eval
  choose Q hQ using hQex
  let e : J → L := fun j => (P j).eval (a : L)
  have hfa : f - algebraMap L F a ≠ 0 := by
    have h := fun he => (X_sub_C_ne_zero (a : L)) (transcendental_iff.mp htrL _ he)
    simpa only [map_sub, aeval_X, aeval_C] using h
  let y : F := aeval f D₁ * s - ∑ j, aeval f (Q j) * z j
  have hy : y ∈ originalChart L f := sub_mem (mul_mem (aeval_mem_originalChart f D₁) hs)
    ((originalChart L f).sum_mem fun j _ => mul_mem (aeval_mem_originalChart f (Q j)) (hchart j))
  have hkey : ∑ j, algebraMap L F (e j) * z j = (f - algebraMap L F a) * y := by
    have h1 : ∀ j, aeval f (P j) = algebraMap L F (e j) +
        (f - algebraMap L F a) * aeval f (Q j) := by
      intro j
      have hh := congrArg (aeval f) (hQ j)
      simp only [map_sub, map_mul, aeval_C, aeval_X] at hh
      linear_combination hh
    have h2 : aeval f D = (f - algebraMap L F a) * aeval f D₁ := by
      rw [hD, map_mul, map_sub, aeval_X, aeval_C]
    have h3 : aeval f D * s = ∑ j, aeval f (P j) * z j := by
      rw [hsum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [← mul_assoc, mul_comm (aeval f D) (w j), hP j]
    dsimp only [y]
    rw [mul_sub, ← mul_assoc, ← h2, h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [h1 j]; ring
  have hall : ∀ j, e j = 0 := by
    by_contra hn
    obtain ⟨j₁, hj₁⟩ := not_forall.mp hn
    obtain ⟨j₀, _, hc, hm, _⟩ := exists_normalizer (A := A) Finset.univ e (Finset.mem_univ j₁) hj₁
    let c : J → A := fun j => ⟨(e j₀)⁻¹ * e j, hm j (Finset.mem_univ j)⟩
    have hc1 : c j₀ = 1 := Subtype.ext (inv_mul_cancel₀ hc)
    let y' : F := (e j₀)⁻¹ • y
    have hyc : y' ∈ originalChart L f := (originalChart L f).toSubmodule.smul_mem _ hy
    have hkey' : ∑ j, (c j : L) • z j = (f - algebraMap L F a) * y' := by
      have he' : ∑ j, (c j : L) • z j = (e j₀)⁻¹ • ∑ j, algebraMap L F (e j) * z j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by
          change ((e j₀)⁻¹ * e j) • z j = _
          rw [mul_smul, Algebra.smul_def (e j) (z j)]
      rw [he', hkey]
      exact (mul_smul_comm _ _ _).symm
    have hfm : ∀ i, f - algebraMap L F a ∈ (R i).integers :=
      fun i => sub_mem (hf i) (((R i).algebraMap_mem_iff _).mpr a.2)
    have hfr : ∀ i, (R i).residue ⟨f - algebraMap L F a, hfm i⟩ ≠ 0 := by
      intro i
      change (R i).residue (⟨f, hf i⟩ - constHom (R i) a) ≠ 0
      rw [map_sub, residue_constHom]
      intro heq
      apply htr i
      rw [sub_eq_zero.mp heq]
      exact isAlgebraic_algebraMap _
    have hyi : ∀ i, y' ∈ (R i).integers := by
      have heq : y' = (f - algebraMap L F a)⁻¹ * ∑ j, (c j : L) • z j := by
        rw [hkey', ← mul_assoc, inv_mul_cancel₀ hfa, one_mul]
      intro i
      rw [heq]
      exact mul_mem (inv_mem_integers hfr i) (Joint.sum_smul_mem R z hz Finset.univ c i)
    have hzero := residue_coeff_zero_of_chart_linear_factor R f hf z hz huniq hgen
      a c y' ⟨hyi, hyc⟩ hkey' j₀
    rw [hc1, map_one] at hzero
    exact one_ne_zero hzero
  refine ⟨D₁, Q, hD₁0, hdeg, fun j => ?_⟩
  have h1 : P j = (X - C (a : L)) * Q j := by
    have hh := hQ j
    rw [show (P j).eval (a : L) = e j from rfl, hall j, C_0, sub_zero] at hh
    exact hh
  have h2 := hP j
  rw [hD, h1, map_mul, map_mul, map_sub, aeval_X, aeval_C] at h2
  apply mul_left_cancel₀ hfa
  linear_combination h2

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
