import Dubon2026.SourceCuspCorrectionGenerators

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier lifting -> integral parabolic-character lifting -> actual cusp
value correction. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.
The native finite edge-chain construction supplies the named dependency.
No external compatibility shim or linter suppression is imported. -/
namespace Dubon2026.SourceCuspCorrection
noncomputable section
open Subgroup Monoid Monoid.CoprodI MulAction
section Cosets

variable (H : Subgroup Gp)

/-- The actual subgroup coset space. -/
abbrev X : Type := Gp ⧸ H

/-- Cyclic parabolic orbits in the actual coset space. -/
abbrev Cu : Type := orbitRel.Quotient (zpowers τ) (X H)

/-- The actual parabolic coset-orbit projection. -/
def cusp (x : X H) : Cu H := Quotient.mk (orbitRel (zpowers τ) (X H)) x

theorem cusp_surjective : Function.Surjective (cusp H) := Quotient.mk_surjective

theorem cusp_eq_iff {x y : X H} : cusp H x = cusp H y ↔ x ∈ orbit (zpowers τ) y := by
  unfold cusp; rw [Quotient.eq]; rfl

theorem cusp_smul (t : zpowers τ) (x : X H) : cusp H (t • x) = cusp H x :=
  (cusp_eq_iff H).mpr (mem_orbit x t)

@[scoped simp] theorem cusp_τ_smul (x : X H) : cusp H (τ • x) = cusp H x :=
  cusp_smul H ⟨τ, mem_zpowers τ⟩ x

@[scoped simp] theorem cusp_τ_zpow_smul (n : ℤ) (x : X H) : cusp H (τ ^ n • x) = cusp H x :=
  cusp_smul H ⟨τ ^ n, zpow_mem (mem_zpowers τ) n⟩ x

/-- The order-two generator action on cosets. -/
def flip (x : X H) : X H := (CoprodI.of sA : Gp) • x

@[scoped simp] theorem flip_mk (g : Gp) : flip H (g : X H) = ((CoprodI.of sA * g : Gp) : X H) := rfl

theorem flip_flip (x : X H) : flip H (flip H x) = x := by
  rw [flip, flip, ← mul_smul, of_sA_mul_of_sA, one_smul]

/-- The minimal period of the actual parabolic action on a coset. -/
def wd (x : X H) : ℕ := Function.minimalPeriod (fun y => τ • y) x

variable [H.FiniteIndex]

theorem wd_pos (x : X H) : 0 < wd H x :=
  Nat.pos_of_ne_zero (MulAction.minimalPeriod_pos τ x).ne

omit [H.FiniteIndex] in
theorem τ_pow_wd_smul (x : X H) : τ ^ wd H x • x = x :=
  (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl

omit [H.FiniteIndex] in
theorem τ_zpow_smul_eq_iff (x : X H) (n : ℤ) : τ ^ n • x = x ↔ (wd H x : ℤ) ∣ n :=
  MulAction.zpow_smul_eq_iff_minimalPeriod_dvd

omit [H.FiniteIndex] in
theorem gen_mem (g : Gp) : g⁻¹ * τ ^ wd H (g : X H) * g ∈ H := by
  have h1 : ((τ ^ wd H (g : X H) * g : Gp) : X H) = (g : X H) := τ_pow_wd_smul H (g : X H)
  rw [QuotientGroup.eq] at h1
  have h2 := H.inv_mem h1
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using h2

/-- The actual primitive parabolic generator associated with a coset. -/
def genAt (g : Gp) : H := ⟨g⁻¹ * τ ^ wd H (g : X H) * g, gen_mem H g⟩

omit [H.FiniteIndex] in
@[scoped simp] theorem genAt_coe (g : Gp) : (genAt H g : Gp) = g⁻¹ * τ ^ wd H (g : X H) * g := rfl

/-- The successive inverse parabolic translates of a coset. -/
def enum (g : Gp) (j : ℕ) : X H := (((τ ^ j)⁻¹ * g : Gp) : X H)

omit [H.FiniteIndex] in
theorem enum_eq_zpow_smul (g : Gp) (j : ℕ) : enum H g j = τ ^ (-(j : ℤ)) • (g : X H) := by
  rw [enum, zpow_neg, zpow_natCast]; rfl

omit [H.FiniteIndex] in
@[scoped simp] theorem cusp_enum (g : Gp) (j : ℕ) : cusp H (enum H g j) = cusp H (g : X H) := by
  rw [enum_eq_zpow_smul, cusp_τ_zpow_smul]

omit [H.FiniteIndex] in
theorem enum_zero (g : Gp) : enum H g 0 = (g : X H) := by
  rw [enum, pow_zero, inv_one, one_mul]

omit [H.FiniteIndex] in
theorem edgeChainHom_genAt_raw (g : Gp) :
    edgeChainHom H (Additive.ofMul (genAt H g))
      = ∑ j ∈ Finset.range (wd H (g : X H)),
          (Finsupp.single (flip H (enum H g j)) (1 : ℤ)
            - Finsupp.single (enum H g (j + 1)) 1) := by
  have hmem' : g⁻¹ * τ ^ wd H (g : X H) * g⁻¹⁻¹ ∈ H := by
    rw [inv_inv]; exact gen_mem H g
  have hconj := edgeChainHom_conj H g⁻¹ (τ ^ wd H (g : X H)) hmem'
  have hgen : genAt H g = ⟨_, hmem'⟩ :=
    Subtype.ext (show _ = _ * _ * g⁻¹⁻¹ by rw [inv_inv]; rfl)
  rw [hgen, hconj, edgeChain_τ_pow, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sub, map_sub, lTransl_single, lTransl_single, projChain_single, projChain_single,
    enum, enum, flip_mk]
  congr 2
  · rw [mul_inv_rev, mul_inv_rev, inv_inv, of_sA_inv, mul_assoc]
  · rw [mul_inv_rev, inv_inv]

theorem enum_injOn_range (g : Gp) :
    Set.InjOn (enum H g) (Finset.range (wd H (g : X H))) := by
  intro j hj k hk heq
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  rw [enum_eq_zpow_smul, enum_eq_zpow_smul] at heq
  have hstab : τ ^ ((k : ℤ) - j) • (g : X H) = (g : X H) := by
    have h2 : (τ ^ (-(k : ℤ)))⁻¹ • (τ ^ (-(j : ℤ)) • (g : X H)) = (g : X H) := by
      rw [heq, inv_smul_smul]
    rwa [← mul_smul, ← zpow_neg, neg_neg, ← zpow_add, ← sub_eq_add_neg] at h2
  have hdvd := (τ_zpow_smul_eq_iff H _ _).mp hstab
  have hw := wd_pos H (g : X H)
  rcases hdvd with ⟨m, hm⟩
  have hbound : |(k : ℤ) - j| < wd H (g : X H) := by
    rw [abs_sub_lt_iff]; constructor <;> omega
  rw [hm, abs_mul, Nat.abs_cast] at hbound
  have hm0 : m = 0 := by
    by_contra hm0
    have : (wd H (g : X H) : ℤ) * 1 ≤ (wd H (g : X H) : ℤ) * |m| :=
      mul_le_mul_of_nonneg_left (Int.one_le_abs hm0) (Nat.cast_nonneg _)
    omega
  rw [hm0, mul_zero, sub_eq_zero] at hm
  exact_mod_cast hm.symm

omit [H.FiniteIndex] in
theorem enum_width (g : Gp) : enum H g (wd H (g : X H)) = enum H g 0 := by
  rw [enum_eq_zpow_smul, enum_zero]
  exact (τ_zpow_smul_eq_iff H _ _).mpr (by simp)

omit [H.FiniteIndex] in
theorem sum_enum_succ {M : Type*} [AddCommGroup M] (g : Gp) (f : X H → M) :
    ∑ j ∈ Finset.range (wd H (g : X H)), f (enum H g (j + 1))
      = ∑ j ∈ Finset.range (wd H (g : X H)), f (enum H g j) := by
  have h1 := Finset.sum_range_succ (fun j => f (enum H g j)) (wd H (g : X H))
  have h2 := Finset.sum_range_succ' (fun j => f (enum H g j)) (wd H (g : X H))
  rw [enum_width] at h1
  exact (add_right_cancel (h1.symm.trans h2)).symm

theorem exists_enum_eq_of_cusp_eq (g : Gp) {y : X H} (hy : cusp H y = cusp H (g : X H)) :
    ∃ j ∈ Finset.range (wd H (g : X H)), enum H g j = y := by
  rw [cusp_eq_iff] at hy
  obtain ⟨⟨_, n, rfl⟩, rfl⟩ := hy
  set w : ℕ := wd H (g : X H) with hw
  have hwpos : (0 : ℤ) < w := by exact_mod_cast wd_pos H (g : X H)
  refine ⟨((-n) % (w : ℤ)).toNat, ?_, ?_⟩
  · rw [Finset.mem_range]
    have h0 : 0 ≤ (-n) % (w : ℤ) := Int.emod_nonneg _ hwpos.ne'
    have h1 : (-n) % (w : ℤ) < w := Int.emod_lt_of_pos _ hwpos
    omega
  · rw [enum_eq_zpow_smul]
    show τ ^ (-((((-n) % (w : ℤ)).toNat : ℕ) : ℤ)) • (g : X H) = τ ^ n • (g : X H)
    have h0 : 0 ≤ (-n) % (w : ℤ) := Int.emod_nonneg _ hwpos.ne'
    rw [Int.toNat_of_nonneg h0, ← MulAction.zpow_smul_mod_minimalPeriod τ (g : X H) n,
      ← MulAction.zpow_smul_mod_minimalPeriod τ (g : X H) (-((-n) % (w : ℤ)))]
    congr 2
    show -(-n % (w : ℤ)) % (w : ℤ) = n % (w : ℤ)
    exact (Int.mod_modEq (-n) (w : ℤ)).neg.trans (by rw [neg_neg])

end Cosets

end
end Dubon2026.SourceCuspCorrection
