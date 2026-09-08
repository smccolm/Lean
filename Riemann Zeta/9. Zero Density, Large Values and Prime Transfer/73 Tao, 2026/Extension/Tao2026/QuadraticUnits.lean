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
    rw [quadraticExpandingUnit, if_neg hu, inv_zpow]
    simpa only [neg_neg] using hx

/-- Integer powers of the oriented expanding unit are injectively indexed. -/
theorem quadraticExpandingUnit_zpow_injective
    (D : ℕ) [Fact (¬ IsSquare D)] [Fact (0 < D)] :
    Function.Injective fun j : ℤ => quadraticExpandingUnit D ^ j := by
  intro j k hjk
  by_cases hu : 1 < quadraticNontrivialUnitPlace D
      (quadraticFundamentalUnit D : quadraticField D)
  · apply quadraticFundamentalUnit_zpow_injective D
    simpa only [quadraticExpandingUnit, if_pos hu] using hjk
  · apply neg_injective
    apply quadraticFundamentalUnit_zpow_injective D
    simpa only [quadraticExpandingUnit, if_neg hu, inv_zpow] using hjk

end Tao2026
