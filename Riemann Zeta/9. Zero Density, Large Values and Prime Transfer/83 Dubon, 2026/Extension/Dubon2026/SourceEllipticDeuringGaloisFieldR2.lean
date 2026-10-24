import Dubon2026.SourceEllipticDeuringCubicRootsR2

/-! DUB-17/18 -> characteristic-two modular genus/Picard -> faithful inertia.
The actual finite Deuring generator field is adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero.
Existing local division-field and exact torsion-cardinality proofs are reused. -/
namespace Dubon2026.SourceEllipticDeuring
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open SourceEllipticDivisionField
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]

section FieldS

variable (E : WeierstrassCurve F) [E.IsElliptic] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]
  (h3 : (3 : F) ≠ 0)

include h3 in

theorem exists_S : ∃ L : IntermediateField F Ω, IsGalois F L ∧
    (∀ σ : L ≃ₐ[F] L, (∀ P : (E.baseChange L).toAffine.Point, (3 : ℕ) • P = 0 →
      Point.map (σ : L →ₐ[F] L) P = P) → σ = 1) ∧
    (∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      (3 : ℕ) • Point.some x y h = 0 → x ∈ L ∧ y ∈ L) ∧
    FiniteDimensional F (L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E) : IntermediateField F Ω) ∧
    IsGalois F (L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E) : IntermediateField F Ω) := by
  have h3Ω : (3 : Ω) ≠ 0 := natCast_ne_zero_of_ne_zero h3
  obtain ⟨L, hLfd, hLgal, hLcard, hLfaith⟩ :=
    exists_divisionField (Ω := Ω) E (n := 3) h3
  haveI := hLfd; haveI := hLgal

  let ι : (E.baseChange L).toAffine.Point →+ (E.baseChange Ω).toAffine.Point :=
    Point.map (IntermediateField.val L)
  have hι : Function.Injective ι := Point.map_injective _
  let g : {P : (E.baseChange L).toAffine.Point // (3 : ℕ) • P = 0} →
      {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0} :=
    fun P => ⟨ι P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg : Function.Injective g := fun P Q h => Subtype.ext (hι (congrArg Subtype.val h))
  haveI := finite_three_torsion (Ω := Ω) E h3
  have hgbij : Function.Bijective g :=
    hg.bijective_of_nat_card_le (by rw [card_three_torsion E h3, hLcard]; norm_num)
  have hcoords : ∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      (3 : ℕ) • Point.some x y h = 0 → x ∈ L ∧ y ∈ L := by
    intro x y h hP
    obtain ⟨⟨Q, hQ⟩, hQP⟩ := hgbij.2 ⟨Point.some x y h, hP⟩
    have hQP' : ι Q = Point.some x y h := congrArg Subtype.val hQP
    rcases Q with _ | ⟨x', y', h'⟩
    · exact absurd ((map_zero ι).symm.trans hQP') (Point.some_ne_zero _).symm
    · have := hQP'
      erw [Point.map_some] at this
      obtain ⟨hx, hy⟩ := Point.some.inj this
      exact ⟨hx ▸ x'.2, hy ▸ y'.2⟩

  have hsep3 : ∀ q ∈ cubeRoots (Ω := Ω) E, q ∈ separableClosure F Ω := by
    rintro q ⟨P, hP, hP0, hq⟩
    have hd : psi2 E P ∈ separableClosure F Ω ∧ psi2 E P ≠ 0 := by
      rcases P with _ | ⟨x, y, h⟩
      · exact absurd rfl hP0
      · obtain ⟨hx, hy⟩ := hcoords h hP
        haveI : Algebra.IsSeparable F L := IsGalois.to_isSeparable
        have hLsc : L ≤ separableClosure F Ω := le_separableClosure F Ω L
        refine ⟨?_, psi2_ne_zero E h hP⟩
        rw [psi2_some]
        exact add_mem (add_mem (mul_mem (by
          rw [show (2 : Ω) = algebraMap F Ω 2 from (map_ofNat _ 2).symm]
          exact IntermediateField.algebraMap_mem _ _) (hLsc hy))
          (mul_mem (IntermediateField.algebraMap_mem _ E.a₁) (hLsc hx)))
          (IntermediateField.algebraMap_mem _ E.a₃)
    obtain ⟨hdsc, hd0⟩ := hd
    let dS : separableClosure F Ω := ⟨psi2 E P, hdsc⟩
    let f : Polynomial (separableClosure F Ω) := X ^ 3 - Polynomial.C dS
    have hfmap : f.map (algebraMap (separableClosure F Ω) Ω) = X ^ 3 - Polynomial.C (psi2 E P) := by
      simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]; rfl
    have hfsep : (f.map (algebraMap (separableClosure F Ω) Ω)).Separable := by
      rw [hfmap]; exact separable_X_pow_sub_C _ h3Ω hd0
    rw [mem_separableClosure_iff]
    have hf' : f.Separable := (Polynomial.separable_map _).mp hfsep
    have haeval : aeval q f = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, hfmap, eval_sub, eval_pow, eval_X, eval_C, hq, sub_self]
    have hz : IsSeparable (separableClosure F Ω) q := hf'.of_dvd (minpoly.dvd _ q haeval)
    exact IsSeparable.of_algebra_isSeparable_of_isSeparable F hz

  haveI hfin : Finite (cubeRoots (Ω := Ω) E) := (finite_cubeRoots E h3).to_subtype
  have hCfd : FiniteDimensional F (IntermediateField.adjoin F (cubeRoots (Ω := Ω) E)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral
  have hCsep : Algebra.IsSeparable F (IntermediateField.adjoin F (cubeRoots (Ω := Ω) E)) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable F Ω).mpr fun x hx =>
      mem_separableClosure_iff.mp (hsep3 x hx)
  haveI : Normal F Ω :=
    normal_iff.mpr fun z => ⟨(Algebra.IsAlgebraic.isAlgebraic z).isIntegral, IsAlgClosed.splits _⟩
  have hCnormal : Normal F (IntermediateField.adjoin F (cubeRoots (Ω := Ω) E)) := by
    refine IntermediateField.normal_iff_forall_map_le.mpr fun σ => ?_
    rw [IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono F _ _ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact map_mem_cubeRoots E σ hz
  haveI := hCfd; haveI := hCsep; haveI := hCnormal
  haveI : IsGalois F (IntermediateField.adjoin F (cubeRoots (Ω := Ω) E)) := IsGalois.mk
  exact ⟨L, hLgal, hLfaith, hcoords, IntermediateField.finiteDimensional_sup _ _, inferInstance⟩

end FieldS

end
end Dubon2026.SourceEllipticDeuring
