import Dubon2026.RationalSL2FiniteAdeleDensity

/-! # The genuine integral level subgroup in finite adelic SL2 -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The subring of finite adeles integral at every canonical finite place. -/
def finiteAdeleIntegerSubring : Subring (FiniteAdeleRing ℤ ℚ) where
  carrier := {x | ∀ v, x v ∈ v.adicCompletionIntegers ℚ}
  zero_mem' := fun v => (v.adicCompletionIntegers ℚ).zero_mem
  one_mem' := fun v => (v.adicCompletionIntegers ℚ).one_mem
  add_mem' hx hy v := (v.adicCompletionIntegers ℚ).toSubring.add_mem (hx v) (hy v)
  mul_mem' hx hy v := (v.adicCompletionIntegers ℚ).toSubring.mul_mem (hx v) (hy v)
  neg_mem' hx v := (v.adicCompletionIntegers ℚ).toSubring.neg_mem (hx v)

/-- The canonical everywhere-integral subring is open in the actual finite adele ring. -/
theorem finiteAdeleIntegerSubring_isOpen :
    IsOpen (finiteAdeleIntegerSubring : Set (FiniteAdeleRing ℤ ℚ)) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

/-- The actual principal level ideal in the everywhere-integral subring, viewed in finite adeles. -/
def finiteAdeleLevelMultiple (N : ℕ) (x : FiniteAdeleRing ℤ ℚ) : Prop :=
  ∃ y ∈ finiteAdeleIntegerSubring, x = (N : FiniteAdeleRing ℤ ℚ) * y

/-- For nonzero level, the actual principal ideal is the inverse image of the integral subring. -/
theorem finiteAdeleLevelMultiple_iff (N : ℕ) [NeZero N] (x : FiniteAdeleRing ℤ ℚ) :
    finiteAdeleLevelMultiple N x ↔
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹) * x ∈ finiteAdeleIntegerSubring := by
  let d := algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹)
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hd : d * (N : FiniteAdeleRing ℤ ℚ) = 1 := by
    change algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹) * (N : FiniteAdeleRing ℤ ℚ) = 1
    rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) N, ← map_mul,
      inv_mul_cancel₀ hN, map_one]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change d * ((N : FiniteAdeleRing ℤ ℚ) * y) ∈ _
    rwa [← mul_assoc, hd, one_mul]
  · intro hx
    refine ⟨d * x, hx, ?_⟩
    rw [← mul_assoc, mul_comm (N : FiniteAdeleRing ℤ ℚ) d, hd, one_mul]

/-- The genuine nonzero-level principal ideal is open in finite adeles. -/
theorem finiteAdeleLevelMultiple_isOpen (N : ℕ) [NeZero N] :
    IsOpen {x : FiniteAdeleRing ℤ ℚ | finiteAdeleLevelMultiple N x} := by
  simp_rw [finiteAdeleLevelMultiple_iff]
  exact finiteAdeleIntegerSubring_isOpen.preimage (continuous_const.mul continuous_id)

/-- The actual K0(N) subgroup of determinant-one finite adelic matrices. -/
def finiteAdeleGamma0 (N : ℕ) : Subgroup SL(2, FiniteAdeleRing ℤ ℚ) where
  carrier := {g | (∀ i j, g i j ∈ finiteAdeleIntegerSubring) ∧ finiteAdeleLevelMultiple N (g 1 0)}
  one_mem' := by
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> simp
    · exact ⟨0, finiteAdeleIntegerSubring.zero_mem, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, a, ha, hga⟩ ⟨hh, b, hb, hhb⟩
    constructor
    · intro i j
      change ∑ k : Fin 2, g i k * h k j ∈ finiteAdeleIntegerSubring
      exact finiteAdeleIntegerSubring.sum_mem (fun k _ =>
        finiteAdeleIntegerSubring.mul_mem (hg i k) (hh k j))
    · refine ⟨a * h 0 0 + g 1 1 * b,
        finiteAdeleIntegerSubring.add_mem
          (finiteAdeleIntegerSubring.mul_mem ha (hh 0 0))
          (finiteAdeleIntegerSubring.mul_mem (hg 1 1) hb), ?_⟩
      simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hga, hhb]
      ring
  inv_mem' := by
    rintro g ⟨hg, a, ha, hga⟩
    constructor
    · intro i j
      fin_cases i <;> fin_cases j
      · simpa only [coe_inv, Matrix.adjugate_fin_two] using hg 1 1
      · simpa only [coe_inv, Matrix.adjugate_fin_two] using
          finiteAdeleIntegerSubring.neg_mem (hg 0 1)
      · simpa only [coe_inv, Matrix.adjugate_fin_two] using
          finiteAdeleIntegerSubring.neg_mem (hg 1 0)
      · simpa only [coe_inv, Matrix.adjugate_fin_two] using hg 0 0
    · refine ⟨-a, finiteAdeleIntegerSubring.neg_mem ha, ?_⟩
      simp [coe_inv, Matrix.adjugate_fin_two, hga]

/-- Every actual matrix entry is continuous for the canonical finite adelic group topology. -/
theorem finiteAdeleSL2_entry_continuous (i j : Fin 2) :
    Continuous (fun g : SL(2, FiniteAdeleRing ℤ ℚ) => g i j) :=
  (_root_.continuous_apply j).comp
    (Matrix.SpecialLinearGroup.continuous_apply _ continuous_id i)

/-- The actual K0(N) subgroup is open at every nonzero level. -/
theorem finiteAdeleGamma0_isOpen (N : ℕ) [NeZero N] :
    IsOpen (finiteAdeleGamma0 N : Set SL(2, FiniteAdeleRing ℤ ℚ)) := by
  change IsOpen {g : SL(2, FiniteAdeleRing ℤ ℚ) |
    (∀ i j, g i j ∈ finiteAdeleIntegerSubring) ∧ finiteAdeleLevelMultiple N (g 1 0)}
  apply IsOpen.inter
  · convert (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        finiteAdeleIntegerSubring_isOpen.preimage (finiteAdeleSL2_entry_continuous i j)) using 1
    ext g
    simp
    rfl
  · exact (finiteAdeleLevelMultiple_isOpen N).preimage (finiteAdeleSL2_entry_continuous 1 0)

/-- Strong approximation supplies an actual rational matrix and the genuine level subgroup factor. -/
theorem rationalSL2_finiteAdeles_gamma0_factorization (N : ℕ) [NeZero N]
    (g : SL(2, FiniteAdeleRing ℤ ℚ)) :
    ∃ γ : SL(2, ℚ), ∃ k : finiteAdeleGamma0 N,
      g = Matrix.SpecialLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) γ * k.val :=
  rationalSL2_finiteAdeles_open_subgroup_factorization _ (finiteAdeleGamma0_isOpen N) g

end
end Dubon2026
