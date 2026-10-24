import Dubon2026.SourceReductionIndependent

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera inequality ->
simultaneous residue dimension. A joint independent residue family has
independent lifts, and coefficients of integral linear combinations are
integral constants. Reuses the actual constant homomorphism and finite
valuation normalizer already proved in SourceReductionIndependent.
Adapted from the frozen Apache-2.0 FLT joint-residue argument at commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open IsLocalRing
variable {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
variable {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]


variable (R : ∀ i, RegularProlongation A F (Fb i))
  {J : Type*} (E : J → F) (hEmem : ∀ j i, E j ∈ (R i).integers)

/-- The vector of residues at all members of the reduction family. -/
def jointRes (j : J) : ∀ i, Fb i := fun i => (R i).residue ⟨E j, hEmem j i⟩

include hEmem in
theorem sum_smul_mem (t : Finset J) (a : J → A) (i : ι) :
    ∑ j ∈ t, (a j : L) • E j ∈ (R i).integers := by
  refine (R i).integers.toSubring.sum_mem fun j _ => ?_
  rw [Algebra.smul_def]
  exact (R i).integers.toSubring.mul_mem
    ((R i).algebraMap_mem_iff _ |>.mpr (a j).2) (hEmem j i)

theorem residue_sum_smul (t : Finset J) (a : J → A) (i : ι) :
    (R i).residue ⟨∑ j ∈ t, (a j : L) • E j, sum_smul_mem R E hEmem t a i⟩ =
      ∑ j ∈ t, IsLocalRing.residue A (a j) • jointRes R E hEmem j i := by
  have hXeq : (⟨∑ j ∈ t, (a j : L) • E j, sum_smul_mem R E hEmem t a i⟩ : (R i).integers) =
      ∑ j ∈ t, constHom (R i) (a j) * ⟨E j, hEmem j i⟩ := by
    refine Subtype.ext ?_
    push_cast
    exact Finset.sum_congr rfl fun j _ => by
      simp only [coe_constHom]; exact Algebra.smul_def _ _
  rw [hXeq, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, residue_constHom, Algebra.smul_def]
  rfl

variable (hE : LinearIndependent (ResidueField A) (jointRes R E hEmem))
include hE

theorem residue_coeff_eq_zero_joint (t : Finset J) (a : J → A)
    (h : ∀ i, (R i).residue ⟨∑ j ∈ t, (a j : L) • E j, sum_smul_mem R E hEmem t a i⟩ = 0) :
    ∀ j ∈ t, IsLocalRing.residue A (a j) = 0 := by
  have hsum : ∑ j ∈ t, IsLocalRing.residue A (a j) • jointRes R E hEmem j = 0 := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    rw [← residue_sum_smul R E hEmem t a i, h i]
  exact linearIndependent_iff'.mp hE t (fun j => IsLocalRing.residue A (a j)) hsum

theorem mem_of_sum_smul_mem_joint (t : Finset J) (g : J → L)
    (h : ∀ i, ∑ j ∈ t, g j • E j ∈ (R i).integers) : ∀ j ∈ t, g j ∈ A := by
  classical
  by_contra hne
  obtain ⟨j₀, hj₀t, hgj₀⟩ := not_forall₂.mp hne
  have hg0 : g j₀ ≠ 0 := by rintro h0; exact hgj₀ (h0 ▸ zero_mem A)
  obtain ⟨j₁, hj₁t, hg₁, hcA, hmax⟩ := exists_normalizer (A := A) t g hj₀t hg0
  set c : L := (g j₁)⁻¹
  have hv₁ : 1 < A.valuation (g j₁) := lt_of_lt_of_le
    (by rw [← not_le, A.valuation_le_one_iff]; exact hgj₀) (hmax j₀ hj₀t)
  have hcv : A.valuation c < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hv₁
  have hcmem : c ∈ A := (A.valuation_le_one_iff c).mp hcv.le
  have hcres : IsLocalRing.residue A ⟨c, hcmem⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]; exact hcv
  let a : J → A := fun j => if hj : j ∈ t then ⟨c * g j, hcA j hj⟩ else 0
  have ha : ∀ j ∈ t, (a j : L) = c * g j := fun j hj => by simp [a, dif_pos hj]
  have hsum_eq : ∑ j ∈ t, (a j : L) • E j = algebraMap L F c * ∑ j ∈ t, g j • E j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ha j hj, mul_smul, Algebra.smul_def]
  have hres0 : ∀ i, (R i).residue ⟨∑ j ∈ t, (a j : L) • E j, sum_smul_mem R E hEmem t a i⟩ = 0 := by
    intro i
    have heq : (⟨∑ j ∈ t, (a j : L) • E j, sum_smul_mem R E hEmem t a i⟩ : (R i).integers) =
        constHom (R i) ⟨c, hcmem⟩ * ⟨∑ j ∈ t, g j • E j, h i⟩ := by
      refine Subtype.ext ?_; push_cast; simp only [coe_constHom]; exact hsum_eq
    rw [heq, map_mul, residue_constHom, hcres, map_zero, zero_mul]
  have hall := residue_coeff_eq_zero_joint R E hEmem hE t a hres0 j₁ hj₁t
  have ha1 : a j₁ = 1 := Subtype.ext (by
    simp only [ha j₁ hj₁t, c, inv_mul_cancel₀ hg₁, OneMemClass.coe_one])
  rw [ha1, map_one] at hall; exact one_ne_zero hall

theorem linearIndependent_coe_joint : LinearIndependent L E := by
  classical
  rw [linearIndependent_iff']
  intro t g hsum j hj
  by_contra hgj
  have hsum' : ∑ j' ∈ t, ((g j)⁻¹ * g j') • E j' = 0 := by
    simp_rw [mul_smul, ← Finset.smul_sum, hsum, smul_zero]
  have hmem' : ∀ i, ∑ j' ∈ t, ((g j)⁻¹ * g j') • E j' ∈ (R i).integers :=
    fun i => hsum' ▸ zero_mem _
  have hA := mem_of_sum_smul_mem_joint R E hEmem hE t (fun j' => (g j)⁻¹ * g j') hmem'
  have h0' : ∀ i, (R i).residue ⟨_, hmem' i⟩ = 0 := fun i => by
    have : (⟨_, hmem' i⟩ : (R i).integers) = 0 := Subtype.ext hsum'; rw [this, map_zero]

  let a : J → A := fun j' => if hj' : j' ∈ t then ⟨(g j)⁻¹ * g j', hA j' hj'⟩ else 0
  have ha : ∀ j' ∈ t, (a j' : L) = (g j)⁻¹ * g j' := fun j' hj' => by simp [a, dif_pos hj']
  have heq : ∀ i, (⟨_, hmem' i⟩ : (R i).integers) =
      ⟨∑ j' ∈ t, (a j' : L) • E j', sum_smul_mem R E hEmem t a i⟩ := fun i => by
    apply Subtype.ext
    exact Finset.sum_congr rfl fun j' hj' => by rw [ha j' hj']
  have hres : ∀ i, (R i).residue ⟨∑ j' ∈ t, (a j' : L) • E j',
      sum_smul_mem R E hEmem t a i⟩ = 0 := fun i => (heq i ▸ h0' i :)
  have hall := residue_coeff_eq_zero_joint R E hEmem hE t a hres j hj
  have ha1 : a j = 1 := Subtype.ext (by simp only [ha j hj, inv_mul_cancel₀ hgj, OneMemClass.coe_one])
  rw [ha1, map_one] at hall; exact one_ne_zero hall


end
end Dubon2026.SourceCurve.RegularProlongation.Joint
