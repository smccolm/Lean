import Dubon2026.SourceCuspUnipotent
import Dubon2026.SourceParabolicClassification
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! DUB-17/18 -> residual Galois association -> boundary eigensystems
of the constructed original complex weight-two class -> its actual cusp
values. Principal-congruence conjugacy makes those values depend only on
the reduced primitive column. Vanishing detects the precise parabolic
subspace, using the proved signed-translation classification.
-/
namespace Dubon2026.SourceCuspBoundary
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} {A : Type*} [AddCommGroup A]

private theorem gamma_le_gamma0 (N : ℕ) : Gamma N ≤ Gamma0 N := by
  intro g hg
  exact Gamma0_mem.mpr (Gamma_mem.mp hg).2.2.1

/-- The actual level-multiple translation at an integral cusp column. -/
def uOf (N : ℕ) (δ : SL(2, ℤ)) : Gamma0 N :=
  ⟨δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹, by
    rw [conj_T_zpow_eq_unipMat]
    exact gamma_le_gamma0 N (unipMat_mem_Gamma N _ _)⟩

/-- The original cusp element has its literal conjugated-translation matrix. -/
theorem coe_uOf (δ : SL(2, ℤ)) :
    (uOf N δ : SL(2, ℤ)) = δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ := rfl

/-- Evaluation of the actual original subgroup homomorphism at a cusp. -/
def B (φ : Additive (Gamma0 N) →+ A) (δ : SL(2, ℤ)) : A :=
  φ (Additive.ofMul (uOf N δ))

/-- Actual cusp evaluation preserves addition. -/
theorem B_add (φ ψ : Additive (Gamma0 N) →+ A) (δ : SL(2, ℤ)) :
    B (φ + ψ) δ = B φ δ + B ψ δ := rfl

/-- Actual cusp evaluation preserves coefficient scalars. -/
theorem B_smul {R : Type*} [Semiring R] [Module R A] (c : R)
    (φ : Additive (Gamma0 N) →+ A) (δ : SL(2, ℤ)) :
    B (c • φ) δ = c • B φ δ := rfl

private theorem apply_conj (φ : Additive (Gamma0 N) →+ A) (g x : Gamma0 N) :
    φ (Additive.ofMul (g * x * g⁻¹)) = φ (Additive.ofMul x) := by
  simp only [ofMul_mul, ofMul_inv, map_add, map_neg]
  abel

/-- Left translation by the original subgroup preserves actual cusp values. -/
theorem B_mul_left (φ : Additive (Gamma0 N) →+ A) (γ : Gamma0 N) (δ : SL(2, ℤ)) :
    B φ ((γ : SL(2, ℤ)) * δ) = B φ δ := by
  have h : uOf N ((γ : SL(2, ℤ)) * δ) = γ * uOf N δ * γ⁻¹ := by
    apply Subtype.ext
    simp only [coe_uOf, Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  unfold B
  rw [h, apply_conj]

/-- The reduced primitive column of an actual integral cusp representative. -/
def colRed (N : ℕ) (δ : SL(2, ℤ)) : ZMod N × ZMod N :=
  (((δ 0 0 : ℤ) : ZMod N), ((δ 1 0 : ℤ) : ZMod N))

/-- Equal reduced columns give equal values of the original homomorphism. -/
theorem B_congr (φ : Additive (Gamma0 N) →+ A) {δ δ' : SL(2, ℤ)}
    (h : colRed N δ = colRed N δ') : B φ δ = B φ δ' := by
  obtain ⟨g, hg, hconj⟩ := exists_conj_of_col_congr N δ δ'
    (congrArg Prod.fst h) (congrArg Prod.snd h)
  let g' : Gamma0 N := ⟨g, gamma_le_gamma0 N hg⟩
  have he : uOf N δ = g' * uOf N δ' * g'⁻¹ := by
    apply Subtype.ext
    exact hconj N
  unfold B
  rw [he, apply_conj]

/-- The exact action of an original subgroup element on reduced cusp columns. -/
theorem colRed_mul_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (X : SL(2, ℤ)) :
    colRed N (γ * X) = (((γ 0 0 : ℤ) : ZMod N) * ((X 0 0 : ℤ) : ZMod N) +
        ((γ 0 1 : ℤ) : ZMod N) * ((X 1 0 : ℤ) : ZMod N),
      ((γ 1 1 : ℤ) : ZMod N) * ((X 1 0 : ℤ) : ZMod N)) := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ
  have hmul : ∀ i j, (γ * X : SL(2, ℤ)) i j =
      γ i 0 * X 0 j + γ i 1 * X 1 j := fun i j => by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  unfold colRed
  rw [hmul, hmul]
  push_cast
  rw [hc, zero_mul, zero_add]

variable [NeZero N]

/-- The actual original subgroup lifts every required upper-triangular
matrix modulo the level, by the existing integral SL2 reduction theorem. -/
theorem exists_borel (h : (ZMod N)ˣ) (t : ZMod N) :
    ∃ γ : Gamma0 N, (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = (↑h⁻¹ : ZMod N) ∧
      (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod N) = t ∧
      (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = (h : ZMod N) := by
  let a : SL(2, ZMod N) :=
    ⟨!![↑h⁻¹, t; 0, ↑h], by
      rw [Matrix.det_fin_two_of, mul_zero, sub_zero, Units.inv_mul]⟩
  obtain ⟨σ, hσ⟩ := SL2Reduction.SL2_reduction_surjective N a
  have he (i j : Fin 2) : ((σ i j : ℤ) : ZMod N) = a i j :=
    congrArg (fun x : SL(2, ZMod N) => x i j) hσ
  exact ⟨⟨σ, Gamma0_mem.mpr (he 1 0)⟩, he 0 0, he 0 1, he 1 1⟩

/-- Actual cusp values are invariant under the original upper-triangular
action on their reduced columns. -/
theorem B_eq_of_borel (φ : Additive (Gamma0 N) →+ A) {σ σ' : SL(2, ℤ)}
    (h : (ZMod N)ˣ) (t : ZMod N)
    (h0 : (colRed N σ').1 = (↑h⁻¹ : ZMod N) * (colRed N σ).1 + t * (colRed N σ).2)
    (h1 : (colRed N σ').2 = (h : ZMod N) * (colRed N σ).2) : B φ σ' = B φ σ := by
  obtain ⟨γ, hγ0, hγ1, hγ2⟩ := exists_borel h t
  have hcol : colRed N σ' = colRed N ((γ : SL(2, ℤ)) * σ) := by
    rw [colRed_mul_of_mem_Gamma0 γ.property, hγ0, hγ1, hγ2]
    exact Prod.ext h0 h1
  rw [B_congr φ hcol, B_mul_left]

/-- The original parabolic subspace: homomorphisms vanishing on every
actual subgroup element of squared trace four. -/
def parabolicHoms (N : ℕ) : Submodule ℂ (Additive (Gamma0 N) →+ ℂ) where
  carrier := {φ | ∀ γ : Gamma0 N, (γ.val.val.trace) ^ 2 = 4 → φ (Additive.ofMul γ) = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by intro f g hf hg γ hγ; simp only [AddMonoidHom.add_apply, hf γ hγ, hg γ hγ, add_zero]
  smul_mem' := by intro c f hf γ hγ; simp only [AddMonoidHom.smul_apply, hf γ hγ, smul_zero]

/-- Vanishing of the actual cusp values implies membership in the precise
original parabolic subspace. No parabolic classification is assumed. -/
theorem mem_parabolicHoms_of_B_eq_zero (φ : Additive (Gamma0 N) →+ ℂ)
    (hB : ∀ δ : SL(2, ℤ), B φ δ = 0) : φ ∈ parabolicHoms N := by
  intro γ hγ
  obtain ⟨ε, δ, h, hε, hγeq⟩ := SourceParabolic.classification γ.val hγ
  have hcomm : Commute ε (δ * ModularGroup.T ^ h * δ⁻¹) := by
    rcases hε with rfl | rfl
    · exact Commute.one_left _
    · rw [Commute, SemiconjBy, neg_one_mul, mul_neg_one]
  have hε2 : ε ^ (2 * N) = 1 := by
    rcases hε with rfl | rfl
    · exact one_pow _
    · rw [pow_mul, sq, neg_mul_neg, one_mul, one_pow]
  have hpow : γ ^ (2 * N) = (uOf N δ) ^ (2 * h) := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_zpow, hγeq, coe_uOf, hcomm.mul_pow, hε2,
      one_mul, conj_pow, conj_zpow, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul,
      show h * ((2 * N : ℕ) : ℤ) = (N : ℤ) * (2 * h) by push_cast; ring]
  have h1 : φ (Additive.ofMul (γ ^ (2 * N))) = (2 * N) • φ (Additive.ofMul γ) := by
    rw [ofMul_pow, map_nsmul]
  have h2 : φ (Additive.ofMul ((uOf N δ) ^ (2 * h))) = (2 * h) • B φ δ := by
    rw [ofMul_zpow, map_zsmul]
    rfl
  rw [hpow, h2, hB, smul_zero] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left (mul_ne_zero two_ne_zero (NeZero.ne N))

end
end Dubon2026.SourceCuspBoundary
