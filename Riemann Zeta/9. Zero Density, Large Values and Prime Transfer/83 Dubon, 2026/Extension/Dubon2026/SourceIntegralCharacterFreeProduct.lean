import Dubon2026.SourceIntegralCharacterShapiro

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier logarithms -> integral parabolic-character lifting. The actual
free-product universal property lifts a subgroup character that vanishes
on all conjugates of the finite factors. Adapted from the Apache-2.0
pinned primary integral-lift proof in scope 796, revision
6e837e75355538c7f80bab5b956861e86c4eacc2. Native cosetTransition
multiplication is used through the scalar Shapiro construction. Parabolic
vanishing is a separate correction obligation, not assumed proved here. -/
namespace Dubon2026.SourceIntegralCharacterLift
noncomputable section
section FreeProduct

variable {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]
variable {Ω : Type*} [MulAction (Monoid.CoprodI M) Ω] {A B : Type*} [AddCommGroup A] [AddCommGroup B]

open Monoid.CoprodI

theorem IsCrossed.ext_of {c c' : Monoid.CoprodI M → Ω → A} (hc : IsCrossed c) (hc' : IsCrossed c')
    (h : ∀ (i : ι) (m : M i), c (of m) = c' (of m)) : c = c' := by
  funext g
  induction g using Monoid.CoprodI.induction_on with
  | one => rw [hc.map_one, hc'.map_one]
  | of i m => exact h i m
  | mul x y hx hy => rw [hc, hc', hx, hy]

/-- The factor homomorphism with its actual coboundary component. -/
def genHom (F : ι → Ω → A) (i : ι) :
    M i →* (Multiplicative (Ω → A)) ⋊[trHom (Monoid.CoprodI M) Ω A] Monoid.CoprodI M where
  toFun m := ⟨Multiplicative.ofAdd (cob (F i) (of m)), of m⟩
  map_one' := by
    apply SemidirectProduct.ext
    · simp only [map_one, SemidirectProduct.one_left]
      rw [(isCrossed_cob (F i)).map_one]; rfl
    · simp
  map_mul' m m' := by
    apply SemidirectProduct.ext
    · simp only [map_mul, SemidirectProduct.mul_left]
      rw [(isCrossed_cob (F i))]
      show _ = Multiplicative.ofAdd (cob (F i) (of m))
        * trHom (Monoid.CoprodI M) Ω A (of m) (Multiplicative.ofAdd _)
      rw [trHom_apply, toAdd_ofAdd]
      rfl
    · simp

/-- The free-product homomorphism assembled from the factor coboundaries. -/
def totalHom (F : ι → Ω → A) :
    Monoid.CoprodI M →* (Multiplicative (Ω → A)) ⋊[trHom (Monoid.CoprodI M) Ω A] Monoid.CoprodI M :=
  Monoid.CoprodI.lift (genHom F)

theorem totalHom_right (F : ι → Ω → A) (g : Monoid.CoprodI M) : (totalHom F g).right = g := by
  have h : (SemidirectProduct.rightHom.comp (totalHom (M := M) (A := A) F)) = MonoidHom.id _ := by
    apply Monoid.CoprodI.ext_hom
    intro i
    ext m
    simp [totalHom, genHom, SemidirectProduct.rightHom]
  exact DFunLike.congr_fun h g

/-- The actual crossed cocycle obtained from the free-product semidirect lift. -/
def liftCrossed (F : ι → Ω → A) : Monoid.CoprodI M → Ω → A :=
  fun g => Multiplicative.toAdd (totalHom F g).left

theorem isCrossed_liftCrossed (F : ι → Ω → A) : IsCrossed (liftCrossed (M := M) F) := by
  intro g h
  simp only [liftCrossed, map_mul, SemidirectProduct.mul_left, totalHom_right, trHom_apply]
  rfl

theorem liftCrossed_of (F : ι → Ω → A) (i : ι) (m : M i) :
    liftCrossed (M := M) F (of m) = cob (F i) (of m) := by
  simp only [liftCrossed, totalHom, Monoid.CoprodI.lift_of, genHom, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd]

end FreeProduct

end
end Dubon2026.SourceIntegralCharacterLift
