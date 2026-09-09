import Tao2026.SquareRelations
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Units in the real quadratic maximal order

This file specializes Mathlib's Dirichlet unit theorem to the concrete
quadratic field used in the nonsquare-discriminant branch of Tao's Lemma 2.10.
The first step is to prove directly that every complex embedding is real.
-/

namespace Tao2026

open scoped ComplexConjugate NumberField

/-- A complex number whose square is a positive real number is real. -/
theorem complex_conj_eq_self_of_sq_eq_natCast
    {z : ℂ} {D : ℕ} (hD : 0 < D) (hz : z * z = (D : ℂ)) :
    conj z = z := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.mul_re, Complex.natCast_re, Complex.mul_im,
    Complex.natCast_im] at hre him
  have hzIm : z.im = 0 := by
    have hprod : z.re * z.im = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hzRe | hzIm
    · have hDReal : (0 : ℝ) < D := by exact_mod_cast hD
      rw [hzRe] at hre
      nlinarith [sq_nonneg z.im]
    · exact hzIm
  exact Complex.conj_eq_iff_im.mpr hzIm

/-- Every embedding of `ℚ(√D)` into `ℂ` is fixed by complex conjugation when
`D` is positive. -/
theorem quadraticField_embedding_isReal
    (D : ℕ) [Fact (¬ IsSquare D)] [hD : Fact (0 < D)]
    (φ : quadraticField D →+* ℂ) :
    NumberField.ComplexEmbedding.IsReal φ := by
  rw [NumberField.ComplexEmbedding.isReal_iff]
  apply AdjoinRoot.ringHom_ext
  · exact Subsingleton.elim _ _
  · change conj (φ (quadraticSqrt D)) = φ (quadraticSqrt D)
    apply complex_conj_eq_self_of_sq_eq_natCast hD.out
    simpa only [map_mul, map_natCast] using congrArg φ (quadraticSqrt_sq D)

/-- For positive nonsquare `D`, the concrete quadratic field is totally
real.  This supplies the archimedean signature needed by Dirichlet's unit
theorem. -/
noncomputable instance quadraticFieldIsTotallyReal
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    NumberField.IsTotallyReal (quadraticField D) where
  isReal w := NumberField.InfinitePlace.isReal_iff.mpr
    (quadraticField_embedding_isReal D
      (NumberField.InfinitePlace.embedding w))

/-- A positive real quadratic field has exactly two real places. -/
theorem quadraticField_nrRealPlaces_eq_two
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    NumberField.InfinitePlace.nrRealPlaces (quadraticField D) = 2 := by
  rw [← NumberField.IsTotallyReal.finrank]
  exact Algebra.IsQuadraticExtension.finrank_eq_two ℚ (quadraticField D)

/-- The concrete positive real quadratic field has two infinite places. -/
theorem quadraticField_card_infinitePlace_eq_two
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    Fintype.card (NumberField.InfinitePlace (quadraticField D)) = 2 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    quadraticField_nrRealPlaces_eq_two D,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]

/-- Dirichlet's unit rank for the concrete positive real quadratic field is
exactly one. -/
theorem quadraticField_unitRank_eq_one
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    NumberField.Units.rank (quadraticField D) = 1 := by
  simp [NumberField.Units.rank, quadraticField_card_infinitePlace_eq_two D]

/-- The only roots of unity in a positive real quadratic field are `1` and
`-1`.  The proof specializes Mathlib's order argument using the already
computed positive number of real places. -/
theorem quadraticField_torsion_eq_one_or_neg_one
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (x : NumberField.Units.torsion (quadraticField D)) :
    (x : (𝓞 (quadraticField D))ˣ) = 1 ∨
      (x : (𝓞 (quadraticField D))ˣ) = -1 := by
  let xu : (𝓞 (quadraticField D))ˣ := x
  by_cases! hc : 2 < orderOf xu
  · have horder : orderOf xu = orderOf (xu : quadraticField D) := by
      calc
        orderOf xu = orderOf (xu.val : 𝓞 (quadraticField D)) :=
          orderOf_units.symm
        _ = orderOf (algebraMap (𝓞 (quadraticField D))
            (quadraticField D) xu.val) :=
          (orderOf_injective (algebraMap (𝓞 (quadraticField D))
            (quadraticField D)).toMonoidHom
              NumberField.RingOfIntegers.coe_injective xu.val).symm
        _ = orderOf (xu : quadraticField D) := rfl
    have hcField : 2 < orderOf (xu : quadraticField D) := by
      rwa [horder] at hc
    linarith [NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hcField
        (IsPrimitiveRoot.orderOf (x.1 : quadraticField D)),
      quadraticField_nrRealPlaces_eq_two D]
  · interval_cases hi : orderOf xu
    · have hpos : 0 < orderOf xu := orderOf_pos_iff.mpr (by
        simpa only [xu] using ((CommGroup.mem_torsion _ x.1).mp x.2))
      omega
    · left
      change xu = 1
      exact orderOf_eq_one_iff.mp hi
    · right
      change xu = -1
      apply Units.val_injective
      rw [← orderOf_units] at hi
      exact (CharP.orderOf_eq_two_iff 0 (by decide)).mp hi

/-- Consequently the torsion subgroup of the concrete real quadratic unit
group has exactly two elements. -/
theorem quadraticField_torsionOrder_eq_two
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    NumberField.Units.torsionOrder (quadraticField D) = 2 := by
  classical
  refine (Finset.card_eq_two.mpr ⟨1,
    ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x => ⟨fun _ => ?_, fun _ =>
      Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton,
    ← Subtype.val_inj, ← Subtype.val_inj]
  exact quadraticField_torsion_eq_one_or_neg_one D x

/-- The unique index in Mathlib's fundamental system for the rank-one unit
group of the concrete real quadratic field. -/
noncomputable def quadraticUnitIndex
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    Fin (NumberField.Units.rank (quadraticField D)) :=
  ⟨0, by rw [quadraticField_unitRank_eq_one D]; omega⟩

noncomputable instance quadraticUnitIndexUnique
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    Unique (Fin (NumberField.Units.rank (quadraticField D))) := {
  default := quadraticUnitIndex D
  uniq i := by
    apply Fin.ext
    have hi : i.val < 1 := by
      simpa only [quadraticField_unitRank_eq_one D] using i.isLt
    simp [quadraticUnitIndex]
    omega }

/-- The single member of Mathlib's fundamental system for the rank-one unit
group of the concrete real quadratic field. -/
noncomputable def quadraticFundamentalUnit
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    (𝓞 (quadraticField D))ˣ :=
  NumberField.Units.fundSystem (quadraticField D) (quadraticUnitIndex D)

/-- Rank-one form of Dirichlet's unit theorem: every maximal-order unit is a
root of unity times one integral power of the distinguished fundamental
unit. -/
theorem exists_eq_torsion_mul_quadraticFundamentalUnit_zpow
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (x : (𝓞 (quadraticField D))ˣ) :
    ∃ ζ : NumberField.Units.torsion (quadraticField D), ∃ j : ℤ,
      x = ζ * quadraticFundamentalUnit D ^ j := by
  obtain ⟨⟨ζ, f⟩, hx, -⟩ :=
    NumberField.Units.exist_unique_eq_mul_prod (quadraticField D) x
  refine ⟨ζ, f (quadraticUnitIndex D), ?_⟩
  rw [hx, Fintype.prod_unique]
  congr 2

/-- The torsion factor and integer exponent in the rank-one Dirichlet
decomposition are jointly unique. -/
theorem existsUnique_eq_torsion_mul_quadraticFundamentalUnit_zpow
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (x : (𝓞 (quadraticField D))ˣ) :
    ∃! ζj : NumberField.Units.torsion (quadraticField D) × ℤ,
      x = ζj.1 * quadraticFundamentalUnit D ^ ζj.2 := by
  obtain ⟨ζ, j, hx⟩ :=
    exists_eq_torsion_mul_quadraticFundamentalUnit_zpow D x
  refine ⟨⟨ζ, j⟩, hx, ?_⟩
  rintro ⟨η, k⟩ hk
  let fj : Fin (NumberField.Units.rank (quadraticField D)) → ℤ := fun _ => j
  let fk : Fin (NumberField.Units.rank (quadraticField D)) → ℤ := fun _ => k
  have hxj : x = ζ * ∏ i, NumberField.Units.fundSystem
      (quadraticField D) i ^ fj i := by
    rw [Fintype.prod_unique]
    exact hx
  have hxk : x = η * ∏ i, NumberField.Units.fundSystem
      (quadraticField D) i ^ fk i := by
    rw [Fintype.prod_unique]
    exact hk
  have hfj := NumberField.Units.fun_eq_repr (quadraticField D) ζ.prop hxj
  have hfk := NumberField.Units.fun_eq_repr (quadraticField D) η.prop hxk
  have hjk : j = k := by
    have hfun : fj = fk := hfj.trans hfk.symm
    exact congrFun hfun (quadraticUnitIndex D)
  subst k
  apply Prod.ext
  · apply Subtype.ext
    exact mul_right_cancel (hx.symm.trans hk).symm
  · rfl

/-- Distinct integer exponents give distinct powers of the quadratic
fundamental unit. -/
theorem quadraticFundamentalUnit_zpow_injective
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    Function.Injective fun j : ℤ => quadraticFundamentalUnit D ^ j := by
  intro j k hjk
  change quadraticFundamentalUnit D ^ j =
    quadraticFundamentalUnit D ^ k at hjk
  obtain ⟨ζj, _, hunique⟩ :=
    existsUnique_eq_torsion_mul_quadraticFundamentalUnit_zpow D
      (quadraticFundamentalUnit D ^ j)
  have hj : quadraticFundamentalUnit D ^ j =
      (1 : NumberField.Units.torsion (quadraticField D)) *
        quadraticFundamentalUnit D ^ j := by simp
  have hk : quadraticFundamentalUnit D ^ j =
      (1 : NumberField.Units.torsion (quadraticField D)) *
        quadraticFundamentalUnit D ^ k := by
    simpa only [Subgroup.coe_one, one_mul] using hjk
  have heqj :
      ((1 : NumberField.Units.torsion (quadraticField D)), j) = ζj :=
    hunique ((1 : NumberField.Units.torsion (quadraticField D)), j) hj
  have heqk :
      ((1 : NumberField.Units.torsion (quadraticField D)), k) = ζj :=
    hunique ((1 : NumberField.Units.torsion (quadraticField D)), k) hk
  have hpair :
      ((1 : NumberField.Units.torsion (quadraticField D)), j) =
        ((1 : NumberField.Units.torsion (quadraticField D)), k) :=
    heqj.trans heqk.symm
  exact congrArg Prod.snd hpair

/-- The distinguished fundamental unit is genuinely nontorsion. -/
theorem quadraticFundamentalUnit_not_mem_torsion
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    quadraticFundamentalUnit D ∉
      NumberField.Units.torsion (quadraticField D) := by
  intro hmem
  obtain ⟨ζj, _, hunique⟩ :=
    existsUnique_eq_torsion_mul_quadraticFundamentalUnit_zpow D
      (quadraticFundamentalUnit D)
  let ζ : NumberField.Units.torsion (quadraticField D) :=
    ⟨quadraticFundamentalUnit D, hmem⟩
  have hzero : quadraticFundamentalUnit D =
      ζ * quadraticFundamentalUnit D ^ (0 : ℤ) := by simp [ζ]
  have hone : quadraticFundamentalUnit D =
      (1 : NumberField.Units.torsion (quadraticField D)) *
        quadraticFundamentalUnit D ^ (1 : ℤ) := by simp
  have hpairs : (ζ, (0 : ℤ)) =
      ((1 : NumberField.Units.torsion (quadraticField D)), (1 : ℤ)) :=
    (hunique _ hzero).trans (hunique _ hone).symm
  have := congrArg Prod.snd hpairs
  norm_num at this

/-- Some infinite place detects the nontorsion fundamental unit. -/
theorem exists_quadraticFundamentalUnit_place_ne_one
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    ∃ w : NumberField.InfinitePlace (quadraticField D),
      w (quadraticFundamentalUnit D : quadraticField D) ≠ 1 := by
  by_contra hExists
  apply quadraticFundamentalUnit_not_mem_torsion D
  apply (NumberField.Units.mem_torsion (quadraticField D)).mpr
  intro w
  by_contra hw
  exact hExists ⟨w, hw⟩

/-- A fixed infinite place at which the fundamental unit has nonunit
absolute value. -/
noncomputable def quadraticNontrivialUnitPlace
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    NumberField.InfinitePlace (quadraticField D) :=
  Classical.choose (exists_quadraticFundamentalUnit_place_ne_one D)

theorem quadraticNontrivialUnitPlace_ne_one
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    quadraticNontrivialUnitPlace D
        (quadraticFundamentalUnit D : quadraticField D) ≠ 1 :=
  Classical.choose_spec (exists_quadraticFundamentalUnit_place_ne_one D)

/-- Orient the rank-one generator so that its value at the selected real
place is greater than one. -/
noncomputable def quadraticExpandingUnit
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    (𝓞 (quadraticField D))ˣ :=
  if 1 < quadraticNontrivialUnitPlace D
      (quadraticFundamentalUnit D : quadraticField D) then
    quadraticFundamentalUnit D else (quadraticFundamentalUnit D)⁻¹

theorem one_lt_quadraticExpandingUnit_at_place
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    1 < quadraticNontrivialUnitPlace D
      (quadraticExpandingUnit D : quadraticField D) := by
  let w := quadraticNontrivialUnitPlace D
  let u := quadraticFundamentalUnit D
  have huPos : 0 < w (u : quadraticField D) :=
    NumberField.Units.pos_at_place u w
  have huNe : w (u : quadraticField D) ≠ 1 :=
    quadraticNontrivialUnitPlace_ne_one D
  by_cases hu : 1 < w (u : quadraticField D)
  · rw [quadraticExpandingUnit, if_pos hu]
    exact hu
  · have huLt : w (u : quadraticField D) < 1 :=
      lt_of_le_of_ne (le_of_not_gt hu) huNe
    rw [quadraticExpandingUnit, if_neg hu]
    have hcoeInv :
        ((u⁻¹ : (𝓞 (quadraticField D))ˣ) : quadraticField D) =
          (u : quadraticField D)⁻¹ := by
      simpa only [zpow_neg_one] using NumberField.Units.coe_zpow u (-1)
    rw [hcoeInv, map_inv₀]
    exact (one_lt_inv₀ huPos).mpr huLt

/-- Reorienting the fundamental unit does not change the rank-one
decomposition: every maximal-order unit remains torsion times one integer
power. -/
theorem exists_eq_torsion_mul_quadraticExpandingUnit_zpow
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (x : (𝓞 (quadraticField D))ˣ) :
    ∃ ζ : NumberField.Units.torsion (quadraticField D), ∃ j : ℤ,
      x = ζ * quadraticExpandingUnit D ^ j := by
  obtain ⟨ζ, j, hx⟩ :=
    exists_eq_torsion_mul_quadraticFundamentalUnit_zpow D x
  by_cases hu : 1 < quadraticNontrivialUnitPlace D
      (quadraticFundamentalUnit D : quadraticField D)
  · refine ⟨ζ, j, ?_⟩
    simpa only [quadraticExpandingUnit, if_pos hu] using hx
  · refine ⟨ζ, -j, ?_⟩
    have hpow : (quadraticFundamentalUnit D)⁻¹ ^ (-j) =
        quadraticFundamentalUnit D ^ j := by
      rw [inv_zpow, ← zpow_neg, neg_neg]
    rw [quadraticExpandingUnit, if_neg hu, hpow]
    exact hx

/-- Integer powers of the oriented expanding unit are injectively indexed. -/
theorem quadraticExpandingUnit_zpow_injective
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    Function.Injective fun j : ℤ => quadraticExpandingUnit D ^ j := by
  intro j k hjk
  by_cases hu : 1 < quadraticNontrivialUnitPlace D
      (quadraticFundamentalUnit D : quadraticField D)
  · apply quadraticFundamentalUnit_zpow_injective D
    simpa only [quadraticExpandingUnit, if_pos hu] using hjk
  · have hinv : (quadraticFundamentalUnit D ^ j)⁻¹ =
        (quadraticFundamentalUnit D ^ k)⁻¹ := by
      simpa only [quadraticExpandingUnit, if_neg hu, inv_zpow] using hjk
    exact quadraticFundamentalUnit_zpow_injective D (inv_injective hinv)

/-- The expansion factor of the oriented unit at the selected real place. -/
noncomputable def quadraticUnitGrowthBase
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] : ℝ :=
  quadraticNontrivialUnitPlace D
    (quadraticExpandingUnit D : quadraticField D)

theorem one_lt_quadraticUnitGrowthBase
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    1 < quadraticUnitGrowthBase D :=
  one_lt_quadraticExpandingUnit_at_place D

/-- Cayley--Hamilton in dimension two, expressed solely through field trace
and norm.  Keeping this generic makes the later uniform unit-gap argument
independent of the chosen presentation of the quadratic field. -/
theorem quadratic_element_sq_sub_trace_mul_add_norm
    {K : Type*} [Field K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K] (α : K) :
    α ^ 2 - algebraMap ℚ K (Algebra.trace ℚ K α) * α +
      algebraMap ℚ K (Algebra.norm ℚ α) = 0 := by
  have hc := Algebra.aeval_self_charpoly_lmul (R := ℚ) α
  rw [LinearMap.charpoly_def, Matrix.charpoly_of_card_eq_two] at hc
  · have ht := Algebra.trace_eq_matrix_trace
        (Module.Free.chooseBasis ℚ K) α
    have hn := Algebra.norm_eq_matrix_det
        (Module.Free.chooseBasis ℚ K) α
    change Algebra.trace ℚ K α =
      ((LinearMap.toMatrix (Module.Free.chooseBasis ℚ K)
        (Module.Free.chooseBasis ℚ K)) ((Algebra.lmul ℚ K) α)).trace at ht
    change Algebra.norm ℚ α =
      ((LinearMap.toMatrix (Module.Free.chooseBasis ℚ K)
        (Module.Free.chooseBasis ℚ K)) ((Algebra.lmul ℚ K) α)).det at hn
    rw [← ht, ← hn] at hc
    simpa using hc
  · rw [← Module.finrank_eq_card_chooseBasisIndex,
      Algebra.IsQuadraticExtension.finrank_eq_two]

/-- The signed real value underlying an infinite-place absolute value in the
concrete totally real quadratic field. -/
noncomputable def quadraticUnitSignedValue
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (v : NumberField.InfinitePlace (quadraticField D))
    (u : (𝓞 (quadraticField D))ˣ) : ℝ :=
  NumberField.InfinitePlace.embedding_of_isReal
    (NumberField.IsTotallyReal.isReal v) (u : quadraticField D)

theorem abs_quadraticUnitSignedValue
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (v : NumberField.InfinitePlace (quadraticField D))
    (u : (𝓞 (quadraticField D))ˣ) :
    |quadraticUnitSignedValue D v u| = v (u : quadraticField D) := by
  simpa only [quadraticUnitSignedValue, Real.norm_eq_abs] using
    (NumberField.InfinitePlace.norm_embedding_of_isReal
      (NumberField.IsTotallyReal.isReal v) (u : quadraticField D))

/-- The signed value of a quadratic algebraic unit satisfies a monic
quadratic equation with integral trace and constant coefficient `±1`. -/
theorem exists_integral_trace_norm_relation_quadraticUnit
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (v : NumberField.InfinitePlace (quadraticField D))
    (u : (𝓞 (quadraticField D))ˣ) :
    ∃ t n : ℤ, |n| = 1 ∧
      quadraticUnitSignedValue D v u ^ 2 -
        (t : ℝ) * quadraticUnitSignedValue D v u + (n : ℝ) = 0 := by
  let t : ℤ := Algebra.trace ℤ (𝓞 (quadraticField D))
    (u : 𝓞 (quadraticField D))
  let n : ℤ := Algebra.norm ℤ (u : 𝓞 (quadraticField D))
  refine ⟨t, n, ?_, ?_⟩
  · have hunitNorm := NumberField.Units.norm (quadraticField D) u
    have hnQ : (n : ℚ) = Algebra.norm ℚ (u : quadraticField D) :=
      Algebra.coe_norm_int (u : 𝓞 (quadraticField D))
    rw [← hnQ] at hunitNorm
    have hnCast : ((|n| : ℤ) : ℚ) = 1 := by simpa using hunitNorm
    exact_mod_cast hnCast
  · have hrel := quadratic_element_sq_sub_trace_mul_add_norm
      (u : quadraticField D)
    have hr := congrArg
      (NumberField.InfinitePlace.embedding_of_isReal
        (NumberField.IsTotallyReal.isReal v)) hrel
    have htQ : (t : ℚ) = Algebra.trace ℚ (quadraticField D)
        (u : quadraticField D) :=
      Algebra.coe_trace_int (u : 𝓞 (quadraticField D))
    have hnQ : (n : ℚ) = Algebra.norm ℚ (u : quadraticField D) :=
      Algebra.coe_norm_int (u : 𝓞 (quadraticField D))
    rw [← htQ, ← hnQ] at hr
    simpa [quadraticUnitSignedValue] using hr

/-- An integral quadratic unit cannot have real absolute value strictly
between `1` and `3/2`.  The proof is the elementary trace/norm argument:
the norm is `±1`, the trace is integral, and the handful of possible traces
in that interval contradict the quadratic equation. -/
theorem three_halves_le_abs_of_integral_quadratic_unit_relation
    (r : ℝ) (t n : ℤ) (hn : |n| = 1)
    (hr : r ^ 2 - (t : ℝ) * r + (n : ℝ) = 0)
    (hgt : 1 < |r|) : (3 : ℝ) / 2 ≤ |r| := by
  by_contra h
  have hlt : |r| < (3 : ℝ) / 2 := lt_of_not_ge h
  have hnCases : n = 1 ∨ n = -1 :=
    (abs_eq (zero_le_one' ℤ)).mp hn
  rcases hnCases with rfl | rfl
  · rcases le_total 0 r with hrNonneg | hrNonpos
    · rw [abs_of_nonneg hrNonneg] at hgt hlt
      have htLower : (0 : ℤ) ≤ t := by
        by_contra ht
        have ht' : (t : ℝ) ≤ -1 := by exact_mod_cast (show t ≤ -1 by omega)
        norm_num at hr
        nlinarith
      have htUpper : t ≤ 2 := by
        by_contra ht
        have ht' : (3 : ℝ) ≤ t := by exact_mod_cast (show 3 ≤ t by omega)
        norm_num at hr
        nlinarith
      interval_cases t <;> norm_num at hr <;> nlinarith
    · rw [abs_of_nonpos hrNonpos] at hgt hlt
      have htLower : (-2 : ℤ) ≤ t := by
        by_contra ht
        have ht' : (t : ℝ) ≤ -3 := by exact_mod_cast (show t ≤ -3 by omega)
        norm_num at hr
        nlinarith
      have htUpper : t ≤ 0 := by
        by_contra ht
        have ht' : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
        norm_num at hr
        nlinarith
      interval_cases t <;> norm_num at hr <;> nlinarith
  · rcases le_total 0 r with hrNonneg | hrNonpos
    · rw [abs_of_nonneg hrNonneg] at hgt hlt
      have htLower : (0 : ℤ) ≤ t := by
        by_contra ht
        have ht' : (t : ℝ) ≤ -1 := by exact_mod_cast (show t ≤ -1 by omega)
        norm_num at hr
        nlinarith
      have htUpper : t ≤ 1 := by
        by_contra ht
        have ht' : (2 : ℝ) ≤ t := by exact_mod_cast (show 2 ≤ t by omega)
        norm_num at hr
        nlinarith
      interval_cases t <;> norm_num at hr <;> nlinarith
    · rw [abs_of_nonpos hrNonpos] at hgt hlt
      have htLower : (-1 : ℤ) ≤ t := by
        by_contra ht
        have ht' : (t : ℝ) ≤ -2 := by exact_mod_cast (show t ≤ -2 by omega)
        norm_num at hr
        nlinarith
      have htUpper : t ≤ 0 := by
        by_contra ht
        have ht' : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
        norm_num at hr
        nlinarith
      interval_cases t <;> norm_num at hr <;> nlinarith

/-- Uniform regulator gap for every positive nonsquare discriminant in this
family: the oriented fundamental unit expands by at least `3/2`. -/
theorem three_halves_le_quadraticUnitGrowthBase
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    (3 : ℝ) / 2 ≤ quadraticUnitGrowthBase D := by
  let v := quadraticNontrivialUnitPlace D
  let u := quadraticExpandingUnit D
  obtain ⟨t, n, hn, hrelation⟩ :=
    exists_integral_trace_norm_relation_quadraticUnit D v u
  have hgt : 1 < |quadraticUnitSignedValue D v u| := by
    rw [abs_quadraticUnitSignedValue]
    exact one_lt_quadraticUnitGrowthBase D
  have hgap := three_halves_le_abs_of_integral_quadratic_unit_relation
    (quadraticUnitSignedValue D v u) t n hn hrelation hgt
  rw [abs_quadraticUnitSignedValue] at hgap
  exact hgap

theorem log_three_halves_le_log_quadraticUnitGrowthBase
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    Real.log ((3 : ℝ) / 2) ≤ Real.log (quadraticUnitGrowthBase D) :=
  (Real.log_le_log_iff (by norm_num) (zero_lt_one.trans
    (one_lt_quadraticUnitGrowthBase D))).2
      (three_halves_le_quadraticUnitGrowthBase D)

/-- A discriminant-independent natural exponent cutoff obtained by dividing
the box-height logarithm by the fixed positive gap `log(3/2)`. -/
noncomputable def quadraticUnitLogCutoff (E : ℝ) : ℕ :=
  ⌈Real.log (E ^ 2) / Real.log ((3 : ℝ) / 2)⌉₊

/-- The natural ceiling in the uniform unit cutoff costs less than one. -/
theorem quadraticUnitLogCutoff_cast_lt_log_div_add_one
    {E : ℝ} (hE : 1 ≤ E) :
    (quadraticUnitLogCutoff E : ℝ) <
      Real.log (E ^ 2) / Real.log ((3 : ℝ) / 2) + 1 := by
  apply Nat.ceil_lt_add_one
  apply div_nonneg
  · apply Real.log_nonneg
    nlinarith
  · exact (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)).le

/-- A convenient epsilon-power majorant for the logarithmic unit cutoff. -/
theorem quadraticUnitLogCutoff_cast_le_rpow
    {E δ : ℝ} (hE : 1 ≤ E) (hδ : 0 < δ) :
    (quadraticUnitLogCutoff E : ℝ) ≤
      (2 / (Real.log ((3 : ℝ) / 2) * δ)) * E ^ δ + 1 := by
  have hlogBase : 0 < Real.log ((3 : ℝ) / 2) :=
    Real.log_pos (by norm_num)
  have hlogE : Real.log E ≤ E ^ δ / δ :=
    Real.log_le_rpow_div (by positivity) hδ
  have hsq : Real.log (E ^ 2) = 2 * Real.log E := by
    rw [Real.log_pow]
    norm_num
  have hcut :=
    (quadraticUnitLogCutoff_cast_lt_log_div_add_one hE).le
  rw [hsq] at hcut
  calc
    (quadraticUnitLogCutoff E : ℝ) ≤
        2 * Real.log E / Real.log ((3 : ℝ) / 2) + 1 := hcut
    _ ≤ 2 * (E ^ δ / δ) / Real.log ((3 : ℝ) / 2) + 1 := by
      gcongr
    _ = (2 / (Real.log ((3 : ℝ) / 2) * δ)) * E ^ δ + 1 := by
      field_simp [hlogBase.ne', hδ.ne']

/-- Explicit constant used to absorb the logarithmic unit count into an
arbitrarily small positive power of the height envelope. -/
noncomputable def quadraticUnitEpsilonConstant (δ : ℝ) : ℝ :=
  8 / (Real.log ((3 : ℝ) / 2) * δ) + 6

theorem quadraticUnitEpsilonConstant_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < quadraticUnitEpsilonConstant δ := by
  unfold quadraticUnitEpsilonConstant
  have hlog : 0 < Real.log ((3 : ℝ) / 2) := Real.log_pos (by norm_num)
  positivity

/-- The complete `2(2B+1)` unit-family factor is `O(E^δ)` for every
positive `δ`, with a displayed constant independent of the discriminant. -/
theorem unitLogCutoffFactor_cast_le_const_mul_rpow
    {E δ : ℝ} (hE : 1 ≤ E) (hδ : 0 < δ) :
    ((2 * (2 * quadraticUnitLogCutoff E + 1) : ℕ) : ℝ) ≤
      quadraticUnitEpsilonConstant δ * E ^ δ := by
  have hcut := quadraticUnitLogCutoff_cast_le_rpow hE hδ
  have hpow : 1 ≤ E ^ δ := Real.one_le_rpow hE hδ.le
  let A : ℝ := 2 / (Real.log ((3 : ℝ) / 2) * δ)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hlog : 0 < Real.log ((3 : ℝ) / 2) :=
      Real.log_pos (by norm_num)
    positivity
  calc
    ((2 * (2 * quadraticUnitLogCutoff E + 1) : ℕ) : ℝ) =
        4 * (quadraticUnitLogCutoff E : ℝ) + 2 := by
      push_cast
      ring
    _ ≤ 4 * (A * E ^ δ + 1) + 2 := by
      gcongr
    _ = 4 * A * E ^ δ + 6 := by ring
    _ ≤ (4 * A + 6) * E ^ δ := by
      nlinarith [mul_nonneg (show 0 ≤ (6 : ℝ) by norm_num)
        (sub_nonneg.mpr hpow)]
    _ = quadraticUnitEpsilonConstant δ * E ^ δ := by
      unfold quadraticUnitEpsilonConstant
      dsimp [A]
      ring

/-- The cutoff dominates the required height in units of the actual
fundamental-unit logarithm, uniformly in the discriminant. -/
theorem log_sq_le_quadraticUnitLogCutoff_mul_log_growthBase
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] (E : ℝ) :
    Real.log (E ^ 2) ≤
      (quadraticUnitLogCutoff E : ℝ) *
        Real.log (quadraticUnitGrowthBase D) := by
  have hcPos : 0 < Real.log ((3 : ℝ) / 2) := Real.log_pos (by norm_num)
  have hceil : Real.log (E ^ 2) / Real.log ((3 : ℝ) / 2) ≤
      (quadraticUnitLogCutoff E : ℕ) := by
    exact Nat.le_ceil _
  have hfixed : Real.log (E ^ 2) ≤
      (quadraticUnitLogCutoff E : ℝ) * Real.log ((3 : ℝ) / 2) := by
    exact (div_le_iff₀ hcPos).mp hceil
  calc
    Real.log (E ^ 2) ≤
        (quadraticUnitLogCutoff E : ℝ) *
          Real.log ((3 : ℝ) / 2) := hfixed
    _ ≤ (quadraticUnitLogCutoff E : ℝ) *
        Real.log (quadraticUnitGrowthBase D) :=
      mul_le_mul_of_nonneg_left
        (log_three_halves_le_log_quadraticUnitGrowthBase D) (by positivity)

/-- Evaluation at the selected place commutes with all integer powers of
the oriented unit. -/
theorem quadraticExpandingUnit_zpow_at_place
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] (j : ℤ) :
    quadraticNontrivialUnitPlace D
        ((quadraticExpandingUnit D ^ j : (𝓞 (quadraticField D))ˣ) :
          quadraticField D) =
      quadraticUnitGrowthBase D ^ j := by
  rw [NumberField.Units.coe_zpow, map_zpow₀]
  rfl

/-- The logarithmic size of the `j`th unit power is exactly `|j|` times
the positive logarithm of the expansion factor. -/
theorem abs_log_quadraticExpandingUnit_zpow_at_place
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] (j : ℤ) :
    |Real.log (quadraticNontrivialUnitPlace D
        ((quadraticExpandingUnit D ^ j : (𝓞 (quadraticField D))ˣ) :
          quadraticField D))| =
      (j.natAbs : ℝ) * Real.log (quadraticUnitGrowthBase D) := by
  rw [quadraticExpandingUnit_zpow_at_place, Real.log_zpow, abs_mul]
  have hlog : 0 < Real.log (quadraticUnitGrowthBase D) :=
    Real.log_pos (one_lt_quadraticUnitGrowthBase D)
  rw [abs_of_pos hlog]
  have habs : |(j : ℝ)| = (j.natAbs : ℝ) := by
    calc
      |(j : ℝ)| = ((|j| : ℤ) : ℝ) := Int.cast_abs.symm
      _ = (((j.natAbs : ℤ)) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs j).symm
      _ = (j.natAbs : ℝ) := rfl
  rw [habs]

/-- A logarithmic place bound gives an explicit bound for the absolute
integer exponent. -/
theorem natAbs_exponent_le_of_abs_log_place_le
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)]
    {j : ℤ} {B : ℕ}
    (hbound : |Real.log (quadraticNontrivialUnitPlace D
        ((quadraticExpandingUnit D ^ j : (𝓞 (quadraticField D))ˣ) :
          quadraticField D))| ≤
      (B : ℝ) * Real.log (quadraticUnitGrowthBase D)) :
    j.natAbs ≤ B := by
  rw [abs_log_quadraticExpandingUnit_zpow_at_place] at hbound
  have hlog : 0 < Real.log (quadraticUnitGrowthBase D) :=
    Real.log_pos (one_lt_quadraticUnitGrowthBase D)
  have hcast : (j.natAbs : ℝ) ≤ B :=
    (mul_le_mul_iff_left₀ hlog).mp hbound
  exact_mod_cast hcast

/-- The symmetric integer interval of exponents allowed by a logarithmic
height cutoff. -/
noncomputable def integerExponentsUpTo (B : ℕ) : Finset ℤ :=
  Finset.Icc (-(B : ℤ)) (B : ℤ)

theorem mem_integerExponentsUpTo_iff {B : ℕ} {j : ℤ} :
    j ∈ integerExponentsUpTo B ↔ -(B : ℤ) ≤ j ∧ j ≤ (B : ℤ) := by
  simp [integerExponentsUpTo]

theorem card_integerExponentsUpTo (B : ℕ) :
    (integerExponentsUpTo B).card = 2 * B + 1 := by
  rw [integerExponentsUpTo, Int.card_Icc]
  simp
  omega

theorem mem_integerExponentsUpTo_of_abs_log_place_le
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)]
    {j : ℤ} {B : ℕ}
    (hbound : |Real.log (quadraticNontrivialUnitPlace D
        ((quadraticExpandingUnit D ^ j : (𝓞 (quadraticField D))ˣ) :
          quadraticField D))| ≤
      (B : ℝ) * Real.log (quadraticUnitGrowthBase D)) :
    j ∈ integerExponentsUpTo B := by
  rw [mem_integerExponentsUpTo_iff]
  have hj := natAbs_exponent_le_of_abs_log_place_le D hbound
  have habs : |j| ≤ (B : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hj
  exact abs_le.mp habs

/-- The explicit finite family of all torsion-times-power candidates under
the logarithmic cutoff `B * log(growthBase)`. -/
noncomputable def quadraticUnitsUpToLogBound
    (D B : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    Finset ((𝓞 (quadraticField D))ˣ) := by
  classical
  exact ((Finset.univ : Finset
      (NumberField.Units.torsion (quadraticField D))).product
        (integerExponentsUpTo B)).image fun ζj =>
    (ζj.1 : (𝓞 (quadraticField D))ˣ) *
      quadraticExpandingUnit D ^ ζj.2

/-- Every maximal-order unit satisfying the selected logarithmic place
bound belongs to the explicit torsion-times-power family. -/
theorem mem_quadraticUnitsUpToLogBound_of_abs_log_place_le
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)]
    {x : (𝓞 (quadraticField D))ˣ} {B : ℕ}
    (hbound : |Real.log (quadraticNontrivialUnitPlace D
        (x : quadraticField D))| ≤
      (B : ℝ) * Real.log (quadraticUnitGrowthBase D)) :
    x ∈ quadraticUnitsUpToLogBound D B := by
  classical
  obtain ⟨ζ, j, hx⟩ :=
    exists_eq_torsion_mul_quadraticExpandingUnit_zpow D x
  have hζ : quadraticNontrivialUnitPlace D
      ((ζ : (𝓞 (quadraticField D))ˣ) : quadraticField D) = 1 :=
    (NumberField.Units.mem_torsion (quadraticField D)).mp ζ.prop
      (quadraticNontrivialUnitPlace D)
  have hplace : quadraticNontrivialUnitPlace D
      (x : quadraticField D) =
      quadraticNontrivialUnitPlace D
        ((quadraticExpandingUnit D ^ j : (𝓞 (quadraticField D))ˣ) :
          quadraticField D) := by
    rw [hx, NumberField.Units.coe_mul, map_mul, hζ, one_mul]
  rw [quadraticUnitsUpToLogBound, Finset.mem_image]
  refine ⟨⟨ζ, j⟩, ?_, hx.symm⟩
  exact Finset.mk_mem_product (Finset.mem_univ ζ)
    (mem_integerExponentsUpTo_of_abs_log_place_le D (hplace ▸ hbound))

/-- Quantitative full-unit conclusion: at most `2(2B+1)` maximal-order
units can occur under the logarithmic cutoff.  The first factor `2` is the
exact torsion order and the second counts the possible integer exponents. -/
theorem card_quadraticUnitsUpToLogBound_le
    (D B : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    (quadraticUnitsUpToLogBound D B).card ≤ 2 * (2 * B + 1) := by
  classical
  calc
    (quadraticUnitsUpToLogBound D B).card ≤
        ((Finset.univ : Finset
          (NumberField.Units.torsion (quadraticField D))).product
            (integerExponentsUpTo B)).card := by
      exact Finset.card_image_le
    _ = (Finset.univ : Finset
          (NumberField.Units.torsion (quadraticField D))).card *
        (integerExponentsUpTo B).card := by
      exact Finset.card_product _ _
    _ = Fintype.card (NumberField.Units.torsion (quadraticField D)) *
        (integerExponentsUpTo B).card := by
      rw [Finset.card_univ]
    _ = 2 * (2 * B + 1) := by
      rw [← NumberField.Units.torsionOrder,
        quadraticField_torsionOrder_eq_two D,
        card_integerExponentsUpTo]

/-! ## Unit coordinates on a maximal-order ideal fiber -/

/-- The concrete quadratic-order embedding really is `r+s√D` after
coercion from the maximal order to the fraction field. -/
theorem coe_quadraticOrderToRingOfIntegers
    (D : ℕ) [Fact (¬ IsSquare D)] (z : ℤ√(D : ℤ)) :
    ((quadraticOrderToRingOfIntegers D z : 𝓞 (quadraticField D)) :
        quadraticField D) =
      (z.re : quadraticField D) +
        (z.im : quadraticField D) * quadraticSqrt D :=
  rfl

/-- Every complex embedding sends the distinguished square root to a number
whose squared complex norm is exactly `D`. -/
theorem norm_quadraticSqrt_embedding_sq
    (D : ℕ) [Fact (¬ IsSquare D)] (φ : quadraticField D →+* ℂ) :
    ‖φ (quadraticSqrt D)‖ ^ 2 = D := by
  rw [sq, ← norm_mul, ← map_mul, quadraticSqrt_sq]
  simp

/-- A deliberately elementary polynomial upper bound for the size of the
distinguished square root at every complex embedding.  This weaker-than-sharp
`D+1` bound is sufficient for Tao's subpolynomial orbit count. -/
theorem norm_quadraticSqrt_embedding_le
    (D : ℕ) [Fact (¬ IsSquare D)] (φ : quadraticField D →+* ℂ) :
    ‖φ (quadraticSqrt D)‖ ≤ (D : ℝ) + 1 := by
  have hs : ‖φ (quadraticSqrt D)‖ ^ 2 = (D : ℝ) :=
    norm_quadraticSqrt_embedding_sq D φ
  have hn : 0 ≤ ‖φ (quadraticSqrt D)‖ := norm_nonneg _
  nlinarith

/-- The explicit place envelope for an integral point `r+s√D`. -/
noncomputable def quadraticOrderPlaceEnvelope
    (D : ℕ) (z : ℤ√(D : ℤ)) : ℝ :=
  |(z.re : ℝ)| + |(z.im : ℝ)| * ((D : ℝ) + 1)

theorem quadraticOrderPlaceEnvelope_nonneg
    (D : ℕ) (z : ℤ√(D : ℤ)) :
    0 ≤ quadraticOrderPlaceEnvelope D z := by
  unfold quadraticOrderPlaceEnvelope
  positivity

/-- At every infinite place, an embedded quadratic-order point is bounded by
its explicit coefficient envelope. -/
theorem quadraticOrderPoint_at_place_le_envelope
    (D : ℕ) [Fact (¬ IsSquare D)]
    (z : ℤ√(D : ℤ)) (w : NumberField.InfinitePlace (quadraticField D)) :
    w (((quadraticOrderToRingOfIntegers D z : 𝓞 (quadraticField D)) :
        quadraticField D)) ≤ quadraticOrderPlaceEnvelope D z := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq,
    coe_quadraticOrderToRingOfIntegers, map_add, map_mul]
  calc
    ‖w.embedding (z.re : quadraticField D) +
        w.embedding (z.im : quadraticField D) *
          w.embedding (quadraticSqrt D)‖ ≤
        ‖w.embedding (z.re : quadraticField D)‖ +
          ‖w.embedding (z.im : quadraticField D) *
            w.embedding (quadraticSqrt D)‖ := norm_add_le _ _
    _ = |(z.re : ℝ)| + |(z.im : ℝ)| *
          ‖w.embedding (quadraticSqrt D)‖ := by
      rw [norm_mul]
      simp
    _ ≤ |(z.re : ℝ)| + |(z.im : ℝ)| * ((D : ℝ) + 1) := by
      apply add_le_add (le_refl _)
      exact mul_le_mul_of_nonneg_left
        (norm_quadraticSqrt_embedding_le D w.embedding) (abs_nonneg _)
    _ = quadraticOrderPlaceEnvelope D z := rfl

@[simp]
theorem quadraticOrderPlaceEnvelope_star
    (D : ℕ) (z : ℤ√(D : ℤ)) :
    quadraticOrderPlaceEnvelope D (star z) =
      quadraticOrderPlaceEnvelope D z := by
  simp [quadraticOrderPlaceEnvelope]

/-- The two conjugate factors at any fixed infinite place multiply to the
absolute value of the integral quadratic norm. -/
theorem quadraticOrderPoint_mul_conj_at_place
    (D : ℕ) [Fact (¬ IsSquare D)]
    (z : ℤ√(D : ℤ)) (w : NumberField.InfinitePlace (quadraticField D)) :
    w (((quadraticOrderToRingOfIntegers D z : 𝓞 (quadraticField D)) :
        quadraticField D)) *
      w (((quadraticOrderToRingOfIntegers D (star z) :
        𝓞 (quadraticField D)) : quadraticField D)) =
      |(z.norm : ℝ)| := by
  have h := congrArg
    (fun q : 𝓞 (quadraticField D) => w (q : quadraticField D))
    (quadraticOrderToRingOfIntegers_mul_conj D z)
  calc
    w (((quadraticOrderToRingOfIntegers D z : 𝓞 (quadraticField D)) :
        quadraticField D)) *
      w (((quadraticOrderToRingOfIntegers D (star z) :
        𝓞 (quadraticField D)) : quadraticField D)) =
        w (((z.norm : 𝓞 (quadraticField D)) : quadraticField D)) := by
      simpa only [map_mul] using h
    _ = |(z.norm : ℝ)| := by
      rw [← NumberField.InfinitePlace.norm_embedding_eq]
      simp

/-- Consequently the coefficient envelope also supplies the complementary
lower bound needed to divide two points in the same unit orbit. -/
theorem abs_norm_le_place_mul_envelope
    (D : ℕ) [Fact (¬ IsSquare D)]
    (z : ℤ√(D : ℤ)) (w : NumberField.InfinitePlace (quadraticField D)) :
    |(z.norm : ℝ)| ≤
      w (((quadraticOrderToRingOfIntegers D z : 𝓞 (quadraticField D)) :
        quadraticField D)) * quadraticOrderPlaceEnvelope D z := by
  calc
    |(z.norm : ℝ)| =
        w (((quadraticOrderToRingOfIntegers D z : 𝓞 (quadraticField D)) :
          quadraticField D)) *
        w (((quadraticOrderToRingOfIntegers D (star z) :
          𝓞 (quadraticField D)) : quadraticField D)) :=
      (quadraticOrderPoint_mul_conj_at_place D z w).symm
    _ ≤ w (((quadraticOrderToRingOfIntegers D z :
          𝓞 (quadraticField D)) : quadraticField D)) *
        quadraticOrderPlaceEnvelope D z := by
      exact mul_le_mul_of_nonneg_left
        (by simpa using quadraticOrderPoint_at_place_le_envelope D (star z) w)
        (w.1.nonneg _)

/-- The canonical (choice-defined) unit carrying one embedded norm point to
another when their principal ideals agree.  The existence of this unit is
exactly the association statement supplied by the ideal-divisor map. -/
noncomputable def maximalOrderNormFiberAssociatedUnit
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ}
    {z w : zsqrtdNormFiber (D : ℤ) N}
    (h : maximalOrderNormFiberIdealDivisor z =
      maximalOrderNormFiberIdealDivisor w) :
    (𝓞 (quadraticField D))ˣ :=
  Classical.choose
    (maximalOrderNormFiberIdealDivisor_eq_iff_associated.mp h)

/-- The chosen associated unit has its defining transport property. -/
theorem maximalOrderNormFiberAssociatedUnit_spec
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ}
    {z w : zsqrtdNormFiber (D : ℤ) N}
    (h : maximalOrderNormFiberIdealDivisor z =
      maximalOrderNormFiberIdealDivisor w) :
    quadraticOrderToRingOfIntegers D z.1 *
        maximalOrderNormFiberAssociatedUnit h =
      quadraticOrderToRingOfIntegers D w.1 :=
  Classical.choose_spec
    (maximalOrderNormFiberIdealDivisor_eq_iff_associated.mp h)

/-- Evaluation at any infinite place turns the defining unit transport into
the corresponding multiplicative equality of positive real absolute values. -/
theorem maximalOrderNormFiberAssociatedUnit_at_place
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ}
    {z w : zsqrtdNormFiber (D : ℤ) N}
    (h : maximalOrderNormFiberIdealDivisor z =
      maximalOrderNormFiberIdealDivisor w)
    (v : NumberField.InfinitePlace (quadraticField D)) :
    v (((quadraticOrderToRingOfIntegers D z.1 :
        𝓞 (quadraticField D)) : quadraticField D)) *
      v ((maximalOrderNormFiberAssociatedUnit h :
        (𝓞 (quadraticField D))ˣ) : quadraticField D) =
      v (((quadraticOrderToRingOfIntegers D w.1 :
        𝓞 (quadraticField D)) : quadraticField D)) := by
  have hs := congrArg
    (fun q : 𝓞 (quadraticField D) => v (q : quadraticField D))
    (maximalOrderNormFiberAssociatedUnit_spec h)
  simpa only [map_mul] using hs

/-- Upper ratio estimate for the unit joining two same-norm points in one
ideal-divisor fiber.  It is stated without division, so it remains robust at
the algebraic boundary; later `N ≠ 0` turns `|N|` into a factor at least one. -/
theorem associatedUnit_place_mul_abs_norm_le_envelopes
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ}
    {z w : zsqrtdNormFiber (D : ℤ) N}
    (h : maximalOrderNormFiberIdealDivisor z =
      maximalOrderNormFiberIdealDivisor w)
    (v : NumberField.InfinitePlace (quadraticField D)) :
    v ((maximalOrderNormFiberAssociatedUnit h :
        (𝓞 (quadraticField D))ˣ) : quadraticField D) * |(N : ℝ)| ≤
      quadraticOrderPlaceEnvelope D z.1 *
        quadraticOrderPlaceEnvelope D w.1 := by
  let A := v (((quadraticOrderToRingOfIntegers D z.1 :
    𝓞 (quadraticField D)) : quadraticField D))
  let U := v ((maximalOrderNormFiberAssociatedUnit h :
    (𝓞 (quadraticField D))ˣ) : quadraticField D)
  let B := v (((quadraticOrderToRingOfIntegers D w.1 :
    𝓞 (quadraticField D)) : quadraticField D))
  have htransport : A * U = B :=
    maximalOrderNormFiberAssociatedUnit_at_place h v
  have hzNorm : |(N : ℝ)| ≤ A * quadraticOrderPlaceEnvelope D z.1 := by
    simpa only [z.2] using abs_norm_le_place_mul_envelope D z.1 v
  have hwUpper : B ≤ quadraticOrderPlaceEnvelope D w.1 :=
    quadraticOrderPoint_at_place_le_envelope D w.1 v
  calc
    U * |(N : ℝ)| ≤ U *
        (A * quadraticOrderPlaceEnvelope D z.1) :=
      mul_le_mul_of_nonneg_left hzNorm (v.1.nonneg _)
    _ = B * quadraticOrderPlaceEnvelope D z.1 := by
      rw [← htransport]
      ring
    _ ≤ quadraticOrderPlaceEnvelope D w.1 *
        quadraticOrderPlaceEnvelope D z.1 :=
      mul_le_mul_of_nonneg_right hwUpper
        (quadraticOrderPlaceEnvelope_nonneg D z.1)
    _ = quadraticOrderPlaceEnvelope D z.1 *
        quadraticOrderPlaceEnvelope D w.1 := mul_comm _ _

/-- The reverse ratio estimate; together with the preceding theorem this
bounds both a unit and its inverse by the same envelope product. -/
theorem abs_norm_le_associatedUnit_place_mul_envelopes
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ}
    {z w : zsqrtdNormFiber (D : ℤ) N}
    (h : maximalOrderNormFiberIdealDivisor z =
      maximalOrderNormFiberIdealDivisor w)
    (v : NumberField.InfinitePlace (quadraticField D)) :
    |(N : ℝ)| ≤
      v ((maximalOrderNormFiberAssociatedUnit h :
        (𝓞 (quadraticField D))ˣ) : quadraticField D) *
      (quadraticOrderPlaceEnvelope D z.1 *
        quadraticOrderPlaceEnvelope D w.1) := by
  let A := v (((quadraticOrderToRingOfIntegers D z.1 :
    𝓞 (quadraticField D)) : quadraticField D))
  let U := v ((maximalOrderNormFiberAssociatedUnit h :
    (𝓞 (quadraticField D))ˣ) : quadraticField D)
  let B := v (((quadraticOrderToRingOfIntegers D w.1 :
    𝓞 (quadraticField D)) : quadraticField D))
  have htransport : A * U = B :=
    maximalOrderNormFiberAssociatedUnit_at_place h v
  have hwNorm : |(N : ℝ)| ≤ B * quadraticOrderPlaceEnvelope D w.1 := by
    simpa only [w.2] using abs_norm_le_place_mul_envelope D w.1 v
  have hzUpper : A ≤ quadraticOrderPlaceEnvelope D z.1 :=
    quadraticOrderPoint_at_place_le_envelope D z.1 v
  calc
    |(N : ℝ)| ≤ B * quadraticOrderPlaceEnvelope D w.1 := hwNorm
    _ = (A * U) * quadraticOrderPlaceEnvelope D w.1 := by rw [htransport]
    _ ≤ (quadraticOrderPlaceEnvelope D z.1 * U) *
        quadraticOrderPlaceEnvelope D w.1 := by
      gcongr
      exact quadraticOrderPlaceEnvelope_nonneg D w.1
    _ = U * (quadraticOrderPlaceEnvelope D z.1 *
        quadraticOrderPlaceEnvelope D w.1) := by ring

/-- For nonzero norm and envelopes at least one, the logarithmic size of the
unit coordinate is bounded by the logarithm of the product of the two
literal coefficient envelopes.  This is the promised boxed-point-to-height
bridge in the nonsquare branch of Lemma 2.10. -/
theorem abs_log_associatedUnit_at_place_le_log_envelopes
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ} (hN : N ≠ 0)
    {z w : zsqrtdNormFiber (D : ℤ) N}
    (h : maximalOrderNormFiberIdealDivisor z =
      maximalOrderNormFiberIdealDivisor w)
    (v : NumberField.InfinitePlace (quadraticField D))
    (hzOne : 1 ≤ quadraticOrderPlaceEnvelope D z.1)
    (hwOne : 1 ≤ quadraticOrderPlaceEnvelope D w.1) :
    |Real.log (v ((maximalOrderNormFiberAssociatedUnit h :
        (𝓞 (quadraticField D))ˣ) : quadraticField D))| ≤
      Real.log (quadraticOrderPlaceEnvelope D z.1 *
        quadraticOrderPlaceEnvelope D w.1) := by
  let U := v ((maximalOrderNormFiberAssociatedUnit h :
    (𝓞 (quadraticField D))ˣ) : quadraticField D)
  let Q := quadraticOrderPlaceEnvelope D z.1 *
    quadraticOrderPlaceEnvelope D w.1
  have huPos : 0 < U :=
    NumberField.Units.pos_at_place
      (maximalOrderNormFiberAssociatedUnit h) v
  have hqPos : 0 < Q := mul_pos (zero_lt_one.trans_le hzOne)
    (zero_lt_one.trans_le hwOne)
  have hNOneInt : (1 : ℤ) ≤ |N| := Int.one_le_abs hN
  have hNOne : (1 : ℝ) ≤ |(N : ℝ)| := by
    exact_mod_cast hNOneInt
  have huUpper : U ≤ Q := by
    calc
      U = U * 1 := by ring
      _ ≤ U * |(N : ℝ)| :=
        mul_le_mul_of_nonneg_left hNOne huPos.le
      _ ≤ Q := associatedUnit_place_mul_abs_norm_le_envelopes h v
  have hinvUpper : U⁻¹ ≤ Q := by
    apply (inv_le_iff_one_le_mul₀' huPos).2
    exact hNOne.trans
      (abs_norm_le_associatedUnit_place_mul_envelopes h v)
  rw [abs_le]
  constructor
  · have hlogInv : Real.log U⁻¹ ≤ Real.log Q :=
      (Real.log_le_log_iff (inv_pos.mpr huPos) hqPos).2 hinvUpper
    rw [Real.log_inv] at hlogInv
    linarith
  · exact (Real.log_le_log_iff huPos hqPos).2 huUpper

/-! ## Specialization to Tao's boxed square-relation points -/

@[simp]
theorem quadraticOrderPlaceEnvelope_squareRelationNormPoint
    (b c D n m : ℕ) :
    quadraticOrderPlaceEnvelope D
        (squareRelationNormPoint b c D n m) =
      (b * m : ℝ) + (c * n : ℝ) * ((D : ℝ) + 1) := by
  simp [quadraticOrderPlaceEnvelope, squareRelationNormPoint]

/-- One uniform coefficient envelope for all points arising from an
`n ≤ x`, `m ≤ y` solution box. -/
noncomputable def squareRelationBoxEnvelope
    (b c D x y : ℕ) : ℝ :=
  (b * y : ℝ) + (c * x : ℝ) * ((D : ℝ) + 1)

theorem squareRelationNormPoint_envelope_le_boxEnvelope
    {b c D n m x y : ℕ} (hn : n ≤ x) (hm : m ≤ y) :
    quadraticOrderPlaceEnvelope D
        (squareRelationNormPoint b c D n m) ≤
      squareRelationBoxEnvelope b c D x y := by
  rw [quadraticOrderPlaceEnvelope_squareRelationNormPoint]
  unfold squareRelationBoxEnvelope
  norm_cast
  gcongr

theorem one_le_squareRelationNormPoint_envelope
    {b c D n m : ℕ} (hb : 0 < b) (hm : 0 < m) :
    1 ≤ quadraticOrderPlaceEnvelope D
      (squareRelationNormPoint b c D n m) := by
  rw [quadraticOrderPlaceEnvelope_squareRelationNormPoint]
  have hbmNat : 1 ≤ b * m := Nat.mul_pos hb hm
  have hbm : (1 : ℝ) ≤ (b : ℝ) * (m : ℝ) := by
    exact_mod_cast hbmNat
  have hrest : 0 ≤ (c * n : ℝ) * ((D : ℝ) + 1) := by positivity
  linarith

/-- Two positive boxed solutions in one ideal-divisor fiber have a unit
coordinate whose logarithmic size is bounded by the square of the single
uniform box envelope. -/
theorem abs_log_squareRelationAssociatedUnit_le_boxEnvelope_sq
    {a b c D h n₁ m₁ n₂ m₂ x y : ℕ}
    [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2)
    (heq₁ : a * n₁ ^ 2 + h = b * m₁ ^ 2)
    (heq₂ : a * n₂ ^ 2 + h = b * m₂ ^ 2)
    (hb : 0 < b) (hh : 0 < h) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hn₁x : n₁ ≤ x) (hm₁y : m₁ ≤ y)
    (hn₂x : n₂ ≤ x) (hm₂y : m₂ ≤ y)
    (hideal : maximalOrderNormFiberIdealDivisor
        (squareRelationNormFiberPoint hdisc heq₁) =
      maximalOrderNormFiberIdealDivisor
        (squareRelationNormFiberPoint hdisc heq₂)) :
    |Real.log (quadraticNontrivialUnitPlace D
      ((maximalOrderNormFiberAssociatedUnit hideal :
        (𝓞 (quadraticField D))ˣ) : quadraticField D))| ≤
      Real.log ((squareRelationBoxEnvelope b c D x y) ^ 2) := by
  let z := squareRelationNormFiberPoint hdisc heq₁
  let w := squareRelationNormFiberPoint hdisc heq₂
  let E := squareRelationBoxEnvelope b c D x y
  have hN : ((b * h : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (Nat.ne_of_gt hb) (Nat.ne_of_gt hh)
  have hzOne : 1 ≤ quadraticOrderPlaceEnvelope D z.1 := by
    exact one_le_squareRelationNormPoint_envelope hb hm₁
  have hwOne : 1 ≤ quadraticOrderPlaceEnvelope D w.1 := by
    exact one_le_squareRelationNormPoint_envelope hb hm₂
  have hbase := abs_log_associatedUnit_at_place_le_log_envelopes
    hN hideal (quadraticNontrivialUnitPlace D) hzOne hwOne
  have hzE : quadraticOrderPlaceEnvelope D z.1 ≤ E :=
    squareRelationNormPoint_envelope_le_boxEnvelope hn₁x hm₁y
  have hwE : quadraticOrderPlaceEnvelope D w.1 ≤ E :=
    squareRelationNormPoint_envelope_le_boxEnvelope hn₂x hm₂y
  have hEPos : 0 < E := lt_of_lt_of_le (zero_lt_one.trans_le hzOne) hzE
  calc
    |Real.log (quadraticNontrivialUnitPlace D
      ((maximalOrderNormFiberAssociatedUnit hideal :
        (𝓞 (quadraticField D))ˣ) : quadraticField D))| ≤
        Real.log (quadraticOrderPlaceEnvelope D z.1 *
          quadraticOrderPlaceEnvelope D w.1) := hbase
    _ ≤ Real.log (E ^ 2) := by
      apply (Real.log_le_log_iff
        (mul_pos (zero_lt_one.trans_le hzOne) (zero_lt_one.trans_le hwOne))
        (sq_pos_of_pos hEPos)).2
      rw [pow_two]
      exact mul_le_mul hzE hwE
        (quadraticOrderPlaceEnvelope_nonneg D w.1) hEPos.le

/-- The associated unit of any two positive boxed solutions in the same
ideal-divisor fiber belongs to one explicit, discriminant-uniform finite
candidate set. -/
theorem squareRelationAssociatedUnit_mem_uniformCandidates
    {a b c D h n₁ m₁ n₂ m₂ x y : ℕ}
    [Fact (¬ IsSquare D)] [Fact (0 < D)]
    (hdisc : a * b = D * c ^ 2)
    (heq₁ : a * n₁ ^ 2 + h = b * m₁ ^ 2)
    (heq₂ : a * n₂ ^ 2 + h = b * m₂ ^ 2)
    (hb : 0 < b) (hh : 0 < h) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hn₁x : n₁ ≤ x) (hm₁y : m₁ ≤ y)
    (hn₂x : n₂ ≤ x) (hm₂y : m₂ ≤ y)
    (hideal : maximalOrderNormFiberIdealDivisor
        (squareRelationNormFiberPoint hdisc heq₁) =
      maximalOrderNormFiberIdealDivisor
        (squareRelationNormFiberPoint hdisc heq₂)) :
    maximalOrderNormFiberAssociatedUnit hideal ∈
      quadraticUnitsUpToLogBound D
        (quadraticUnitLogCutoff (squareRelationBoxEnvelope b c D x y)) := by
  apply mem_quadraticUnitsUpToLogBound_of_abs_log_place_le D
  exact (abs_log_squareRelationAssociatedUnit_le_boxEnvelope_sq
    hdisc heq₁ heq₂ hb hh hm₁ hm₂ hn₁x hm₁y hn₂x hm₂y hideal).trans
      (log_sq_le_quadraticUnitLogCutoff_mul_log_growthBase D _)

/-- On any ideal-divisor fiber, the unit coordinate relative to a fixed anchor
is injective.  Thus every such fiber can be counted by counting the
maximal-order units that its boxed points are able to realize. -/
theorem maximalOrderNormFiberAssociatedUnit_injective
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ}
    (z : zsqrtdNormFiber (D : ℤ) N) :
    Function.Injective fun
      w : {w : zsqrtdNormFiber (D : ℤ) N //
        maximalOrderNormFiberIdealDivisor z =
          maximalOrderNormFiberIdealDivisor w} =>
      maximalOrderNormFiberAssociatedUnit w.property := by
  intro w₁ w₂ hunit
  apply Subtype.ext
  apply Subtype.ext
  apply quadraticOrderToRingOfIntegers_injective D
  calc
    quadraticOrderToRingOfIntegers D w₁.1.1 =
        quadraticOrderToRingOfIntegers D z.1 *
          maximalOrderNormFiberAssociatedUnit w₁.property := by
      exact (maximalOrderNormFiberAssociatedUnit_spec w₁.property).symm
    _ = quadraticOrderToRingOfIntegers D z.1 *
          maximalOrderNormFiberAssociatedUnit w₂.property := by
      congr 1
      exact congrArg Units.val hunit
    _ = quadraticOrderToRingOfIntegers D w₂.1.1 :=
      maximalOrderNormFiberAssociatedUnit_spec w₂.property

end Tao2026
