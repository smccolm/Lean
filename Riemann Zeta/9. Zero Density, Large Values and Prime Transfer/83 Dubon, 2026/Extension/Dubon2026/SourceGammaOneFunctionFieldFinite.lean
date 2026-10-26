import Dubon2026.SourceGammaOneRationalRelation
import Mathlib.FieldTheory.PrimitiveElement

/-! DUB-17/18 -> arithmetic Gamma1 realization -> finite rational function field.
The proved field-wide rational norm relation bounds the minimal degree of every
element over the literal j coordinate. Native primitive-element theory for
finite separable subextensions then proves finite dimension. No finite-degree,
transcendence or field-generation hypothesis remains beyond finite index and T.
The final bounded-degree argument is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean.
Existing local j and Laurent independence replace the external alternatives. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField Polynomial

private theorem finiteDimensional_of_forall_aeval_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (D : ℕ)
    (h : ∀ y : F, ∃ p : K[X], p ≠ 0 ∧ p.natDegree ≤ D ∧ aeval y p = 0) :
    FiniteDimensional K F := by
  haveI : Algebra.IsAlgebraic K F := ⟨fun y => by
    obtain ⟨p, hp0, -, hpy⟩ := h y
    exact ⟨p, hp0, hpy⟩⟩
  haveI : Algebra.IsSeparable K F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  by_contra hinf
  obtain ⟨L, hLfd, hlt⟩ := IntermediateField.exists_lt_finrank_of_infinite_dimensional hinf D
  haveI := hLfd
  haveI : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L F
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hdeg : (minpoly K α).natDegree = Module.finrank K L :=
    (Field.primitive_element_iff_minpoly_natDegree_eq K α).mp hα
  obtain ⟨p, hp0, hpD, hpy⟩ := h (α : F)
  have hmin : minpoly K α = minpoly K (α : F) := IntermediateField.minpoly_eq α
  have hle : (minpoly K (α : F)).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd (minpoly.dvd K _ hpy) hp0
  have : Module.finrank K L ≤ D := by
    rw [← hdeg, hmin]
    exact hle.trans hpD
  exact absurd hlt (not_lt.mpr this)


open scoped MatrixGroups

theorem finiteDimensional_jCoordinate
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    letI : Algebra ℚ (qExpFunctionFieldC ℚ Γ) := (qExpFunctionFieldC ℚ Γ).toSubalgebra.algebra
    FiniteDimensional
      (IntermediateField.adjoin ℚ ({jCoordinate Γ} : Set (qExpFunctionFieldC ℚ Γ)))
      (qExpFunctionFieldC ℚ Γ) := by
  classical
  letI : Algebra ℚ (qExpFunctionFieldC ℚ Γ) := (qExpFunctionFieldC ℚ Γ).toSubalgebra.algebra
  let F := qExpFunctionFieldC ℚ Γ
  let X₀ : F := jCoordinate Γ
  let φ : F →+* LaurentSeries ℚ := F.subtype
  let K₀ := IntermediateField.adjoin ℚ ({X₀} : Set F)
  let Xk : K₀ := ⟨X₀, IntermediateField.mem_adjoin_simple_self ℚ X₀⟩
  have hrat : ∀ e : ℚ, (((algebraMap ℚ K₀ e : K₀) : F) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) e := by
    intro e
    have h := RingHom.congr_fun (Subsingleton.elim
      ((φ.comp (algebraMap K₀ F)).comp (algebraMap ℚ K₀)) (algebraMap ℚ (LaurentSeries ℚ))) e
    rw [← h]
    rfl
  haveI : PerfectField K₀ := PerfectField.ofCharZero
  refine finiteDimensional_of_forall_aeval_eq_zero (Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) ?_
  intro Y
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hY⟩ := (mem_qExpFunctionFieldC_iff hT).mp Y.2
  obtain ⟨m, d, ⟨ib₀, hib₀⟩, hd⟩ := exists_rational_j_relation hT f g hf hg hg0

  let coef : Fin (Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) + 1) → K₀ :=
    fun i => ∑ b : Fin (m + 1), algebraMap ℚ K₀ (d (i, b)) * Xk ^ (b : ℕ)
  have hcoef : ∀ i, (((coef i : K₀) : F) : LaurentSeries ℚ) =
      ∑ b : Fin (m + 1), algebraMap ℚ (LaurentSeries ℚ) (d (i, b)) * jq ^ (b : ℕ) := by
    intro i
    simp only [coef]
    rw [IntermediateField.coe_sum, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, hrat]
    rfl
  let p : K₀[X] := ∑ i : Fin (Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) + 1), Polynomial.monomial (i : ℕ) (coef i)
  have hcoeff : ∀ i : Fin (Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) + 1), p.coeff i = coef i := by
    intro i
    simp only [p, finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j _ hji
      rw [if_neg]
      exact fun h => hji (Fin.ext h)
  refine ⟨p, ?_, ?_, ?_⟩
  ·
    intro hp
    have h1 : coef ib₀.1 = 0 := by rw [← hcoeff, hp, Polynomial.coeff_zero]
    apply transcendental_jqModC ℚ
    let r : ℚ[X] := ∑ b : Fin (m + 1), Polynomial.monomial (b : ℕ) (d (ib₀.1, b))
    have hr0 : r ≠ 0 := by
      intro hr
      have := congrArg (fun q : ℚ[X] => q.coeff ib₀.2) hr
      simp only [r, finsetSum_coeff, coeff_monomial, Polynomial.coeff_zero] at this
      rw [Finset.sum_eq_single_of_mem ib₀.2 (Finset.mem_univ _)] at this
      · simp only [↓reduceIte] at this; exact hib₀ this
      · intro j _ hji; rw [if_neg]; exact fun h => hji (Fin.ext h)
    refine ⟨r, hr0, ?_⟩
    have h2 : (((coef ib₀.1 : K₀) : F) : LaurentSeries ℚ) = 0 := by rw [h1]; rfl
    rw [hcoef] at h2
    rw [← h2]
    simp only [r, map_sum, Polynomial.aeval_monomial, jqModC_rat]
  ·
    exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp i.2)
  ·
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero]
    have hd' : ∑ ib : Fin (Nat.card (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) + 1) × Fin (m + 1),
        algebraMap ℚ (LaurentSeries ℚ) (d ib) *
          (jq ^ (ib.2 : ℕ) * (intSeriesC ℚ pf / intSeriesC ℚ pg) ^ (ib.1 : ℕ)) = 0 := by
      rw [← hd]
      refine Finset.sum_congr rfl fun ib _ => ?_
      rw [← HahnSeries.C_mul_eq_smul, HahnSeries.C_eq_algebraMap]
      congr 1
      exact RingHom.congr_fun (Subsingleton.elim _ _) _
    rw [← hd']
    simp only [p, map_sum, Polynomial.aeval_monomial]
    rw [IntermediateField.coe_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, ← hY, IntermediateField.algebraMap_apply, hcoef,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end
end Dubon2026.SourceFunctionField.GammaOne
