import Dubon2026.SourceCurveRegularProlongation
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> arithmetic automorphy and residual association -> original
weight-two Frobenius/inertia -> actual good reduction -> genus comparison ->
preservation of dimensions under coefficient reduction. These lemmas serve
that finite-space dimension theorem; no genus or good-reduction claim is made.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native polynomial monomial independence
replaces the external custom coefficient linear-combination equivalence. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

/-- The inclusion of integral constants into the prolongation valuation ring. -/
def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem residue_eq_zero_iff (R : RegularProlongation A F Fbar) (f : R.integers) :
    R.residue f = 0 ↔ f ∈ maximalIdeal R.integers := by
  change f ∈ RingHom.ker R.residue ↔ _
  rw [R.ker_residue]


theorem exists_normalizer {ι : Type*} (t : Finset ι) (g : ι → L) {i₀ : ι} (hi₀ : i₀ ∈ t)
    (hg : g i₀ ≠ 0) :
    ∃ i₁ ∈ t, g i₁ ≠ 0 ∧ (∀ i ∈ t, (g i₁)⁻¹ * g i ∈ A) ∧
      (∀ i ∈ t, A.valuation (g i) ≤ A.valuation (g i₁)) := by
  obtain ⟨i₁, hi₁t, hmax⟩ := t.exists_max_image (fun i => A.valuation (g i)) ⟨i₀, hi₀⟩
  have hg₁ : g i₁ ≠ 0 := by
    intro h0
    have h := hmax i₀ hi₀
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at h
    exact hg h
  have hv₁ : A.valuation (g i₁) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  refine ⟨i₁, hi₁t, hg₁, fun i hi => ?_, hmax⟩
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc (A.valuation (g i₁))⁻¹ * A.valuation (g i)
      ≤ (A.valuation (g i₁))⁻¹ * A.valuation (g i₁) := by gcongr; exact hmax i hi
    _ = 1 := inv_mul_cancel₀ hv₁

section resIndep

variable (R : RegularProlongation A F Fbar) {ι : Type*} (E : ι → R.integers)

theorem coe_sum_constHom_mul (t : Finset ι) (a : ι → A) :
    ((∑ i ∈ t, constHom R (a i) * E i : R.integers) : F) = ∑ i ∈ t, (a i : L) • (E i : F) := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_constHom, Algebra.smul_def]

theorem residue_sum_constHom_mul (t : Finset ι) (a : ι → A) :
    R.residue (∑ i ∈ t, constHom R (a i) * E i) =
      ∑ i ∈ t, IsLocalRing.residue A (a i) • R.residue (E i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, residue_constHom, Algebra.smul_def]

variable (hE : LinearIndependent (ResidueField A) (fun i => R.residue (E i)))
include hE

theorem residue_coeff_eq_zero (t : Finset ι) (a : ι → A)
    (h : R.residue (∑ i ∈ t, constHom R (a i) * E i) = 0) :
    ∀ i ∈ t, IsLocalRing.residue A (a i) = 0 := by
  rw [residue_sum_constHom_mul] at h
  exact linearIndependent_iff'.mp hE t (fun i => IsLocalRing.residue A (a i)) h

theorem mem_of_sum_smul_mem (t : Finset ι) (g : ι → L)
    (h : ∑ i ∈ t, g i • (E i : F) ∈ R.integers) : ∀ i ∈ t, g i ∈ A := by
  classical
  by_contra hne
  obtain ⟨i₀, hi₀t, hgi₀⟩ := not_forall₂.mp hne
  have hg0 : g i₀ ≠ 0 := by
    rintro h0
    exact hgi₀ (h0 ▸ zero_mem A)
  obtain ⟨i₁, hi₁t, hg₁, hcA, hmax⟩ := exists_normalizer (A := A) t g hi₀t hg0
  set c : L := (g i₁)⁻¹ with hc

  have hv₀ : 1 < A.valuation (g i₀) := by
    rw [← not_le, A.valuation_le_one_iff]; exact hgi₀
  have hv₁ : 1 < A.valuation (g i₁) := lt_of_lt_of_le hv₀ (hmax i₀ hi₀t)
  have hcv : A.valuation c < 1 := by
    rw [hc, map_inv₀]
    exact inv_lt_one_of_one_lt₀ hv₁
  have hcmem : c ∈ A := (A.valuation_le_one_iff c).mp hcv.le
  have hcres : IsLocalRing.residue A ⟨c, hcmem⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact hcv

  let a : ι → A := fun i => if hi : i ∈ t then ⟨c * g i, hcA i hi⟩ else 0
  have ha : ∀ i ∈ t, (a i : L) = c * g i := fun i hi => by simp [a, dif_pos hi]
  set X : R.integers := ∑ i ∈ t, constHom R (a i) * E i with hX
  have hXeq : X = constHom R ⟨c, hcmem⟩ * ⟨∑ i ∈ t, g i • (E i : F), h⟩ := by
    apply Subtype.ext
    rw [hX, coe_sum_constHom_mul]
    change _ = algebraMap L F c * ∑ i ∈ t, g i • (E i : F)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ha i hi, mul_smul, Algebra.smul_def]
  have hres : R.residue X = 0 := by
    rw [hXeq, map_mul, residue_constHom, hcres, map_zero, zero_mul]
  have hall := residue_coeff_eq_zero R E hE t a hres i₁ hi₁t
  have ha1 : a i₁ = 1 := Subtype.ext (by rw [ha i₁ hi₁t, hc, inv_mul_cancel₀ hg₁]; rfl)
  rw [ha1, map_one] at hall
  exact one_ne_zero hall

theorem valuation_lt_one_of_sum_smul_mem (t : Finset ι) (g : ι → L)
    (h : ∑ i ∈ t, g i • (E i : F) ∈ R.integers) (h0 : R.residue ⟨_, h⟩ = 0) :
    ∀ i ∈ t, A.valuation (g i) < 1 := by
  classical
  have hA := mem_of_sum_smul_mem R E hE t g h
  let a : ι → A := fun i => if hi : i ∈ t then ⟨g i, hA i hi⟩ else 0
  have ha : ∀ i ∈ t, (a i : L) = g i := fun i hi => by simp [a, dif_pos hi]
  set X : R.integers := ∑ i ∈ t, constHom R (a i) * E i with hX
  have hXeq : X = ⟨∑ i ∈ t, g i • (E i : F), h⟩ := by
    apply Subtype.ext
    rw [hX, coe_sum_constHom_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [ha i hi]
  have hres : R.residue X = 0 := by rw [hXeq]; exact h0
  intro i hi
  have hz := residue_coeff_eq_zero R E hE t a hres i hi
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at hz
  rwa [ha i hi] at hz

theorem linearIndependent_coe : LinearIndependent L (fun i => (E i : F)) := by
  rw [linearIndependent_iff']
  intro t g hsum i hi
  by_contra hgi

  have hsum' : ∑ j ∈ t, ((g i)⁻¹ * g j) • (E j : F) = 0 := by
    simp_rw [mul_smul, ← Finset.smul_sum, hsum, smul_zero]
  have hmem' : ∑ j ∈ t, ((g i)⁻¹ * g j) • (E j : F) ∈ R.integers := by
    rw [hsum']; exact zero_mem _
  have h0' : R.residue ⟨_, hmem'⟩ = 0 := by
    have : (⟨_, hmem'⟩ : R.integers) = 0 := Subtype.ext hsum'
    rw [this, map_zero]
  have hlt := valuation_lt_one_of_sum_smul_mem R E hE t (fun j => (g i)⁻¹ * g j) hmem' h0' i hi
  simp only [inv_mul_cancel₀ hgi, map_one, lt_self_iff_false] at hlt

end resIndep


end
end Dubon2026.SourceCurve.RegularProlongation
