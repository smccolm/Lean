import Dubon2026.SourceEllipticVeluTwoAdditivity

/-! Remaining coordinate and case analysis for the actual degree-two Velu
group homomorphism. The dependency is DUB-17 / DUB-18 -> continuation -> good
reduction -> reverse genus -> elliptic inertia census -> cyclic-quotient root
interpretation -> quotient homomorphisms with their actual cyclic kernels.
Compatibility predicates in intermediate lemmas describe explicit secant and
tangent coordinate obligations; the final consumer must derive them all.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2. All source option
changes and irrelevant logical anchors are omitted. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
theorem exists_addMonoidHom_coe_eq_veluPointMap2
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0) :
    ∃ φ : W.toAffine.Point →+ (veluQuotient2 W x₀ y₀).toAffine.Point,
      ⇑φ = veluPointMap2 hQ hgy hΔ := by
  have hQns : W.toAffine.Nonsingular x₀ y₀ := W.toAffine.equation_iff_nonsingular.mp hQ
  have hadd : KwVeluOrderTwoAddCompatAt W x₀ y₀ hQns.1 hgy hΔ :=
    velu2_addCompatAt_of_YAlign hgy hQns hΔ
      (fun _ _ hP hy hx hx2 hY => velu2_tanY_align hP hQns.1 hgy hy hx hx2 hY)
  exact ⟨AddMonoidHom.mk' (veluPointMap2 hQ hgy hΔ) hadd, rfl⟩

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
  [W.IsElliptic] {x₀ y₀ : F}

/-- The actual degree-two quotient homomorphism; quotient ellipticity is derived. -/
def veluTwoHom (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) :
    W.toAffine.Point →+ (veluQuotient2 W x₀ y₀).toAffine.Point :=
  Classical.choose (exists_addMonoidHom_coe_eq_veluPointMap2 W hQ hgy
    (veluQuotient2_Delta_ne_zero W.isUnit_Δ.ne_zero hQ hgy))

theorem veluTwoHom_coe (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) :
    ⇑(veluTwoHom hQ hgy) = veluPointMap2 hQ hgy
      (veluQuotient2_Delta_ne_zero W.isUnit_Δ.ne_zero hQ hgy) :=
  Classical.choose_spec (exists_addMonoidHom_coe_eq_veluPointMap2 W hQ hgy
    (veluQuotient2_Delta_ne_zero W.isUnit_Δ.ne_zero hQ hgy))

theorem veluTwoHom_ker (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0) :
    (veluTwoHom hQ hgy).ker = AddSubgroup.zmultiples
      (WeierstrassCurve.Affine.Point.some x₀ y₀ (W.toAffine.equation_iff_nonsingular.mp hQ)) := by
  ext P
  rw [AddMonoidHom.mem_ker, veluTwoHom_coe]
  exact veluPointMap2_eq_zero_iff_mem_zmultiples hQ hgy _ _ P

theorem veluTwoHom_kernel_cardinality (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) : Nat.card (veluTwoHom hQ hgy).ker = 2 := by
  rw [veluTwoHom_ker hQ hgy, Nat.card_zmultiples]
  exact addOrderOf_some_eq_two_of_veluGy_eq_zero hgy _

end
end Dubon2026.SourceEllipticVelu
