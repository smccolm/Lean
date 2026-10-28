import Mathlib

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
section EdgeChain

variable {G : Fin 2 → Type*} [∀ i, Group (G i)]

/-- Left translation of actual finite integer chains on the free product. -/
def lTransl (g : CoprodI G) : (CoprodI G →₀ ℤ) →+ (CoprodI G →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (g * ·)

@[scoped simp] theorem lTransl_single (g x : CoprodI G) (n : ℤ) :
    lTransl g (Finsupp.single x n) = Finsupp.single (g * x) n :=
  Finsupp.mapDomain_single

@[scoped simp] theorem lTransl_one_apply (f : CoprodI G →₀ ℤ) : lTransl 1 f = f := by
  show Finsupp.mapDomain (1 * ·) f = f
  rw [show ((1 : CoprodI G) * ·) = id from funext fun x => one_mul x]
  exact Finsupp.mapDomain_id

theorem lTransl_mul_apply (g₁ g₂ : CoprodI G) (f : CoprodI G →₀ ℤ) :
    lTransl (g₁ * g₂) f = lTransl g₁ (lTransl g₂ f) := by
  show Finsupp.mapDomain (g₁ * g₂ * ·) f
      = Finsupp.mapDomain (g₁ * ·) (Finsupp.mapDomain (g₂ * ·) f)
  rw [← Finsupp.mapDomain_comp]
  simp only [Function.comp_def, mul_assoc]

/-- The additive automorphism induced by left translation of chains. -/
def lTranslAddAut (g : CoprodI G) : AddAut (CoprodI G →₀ ℤ) where
  toFun := lTransl g
  invFun := lTransl g⁻¹
  left_inv f := by rw [← lTransl_mul_apply, inv_mul_cancel, lTransl_one_apply]
  right_inv f := by rw [← lTransl_mul_apply, mul_inv_cancel, lTransl_one_apply]
  map_add' := (lTransl g).map_add

/-- Translation as a multiplicative action on the additive chain group. -/
def lTranslMulAut : CoprodI G →* MulAut (Multiplicative (CoprodI G →₀ ℤ)) where
  toFun g := AddEquiv.toMultiplicative (lTranslAddAut g)
  map_one' := MulEquiv.ext fun f => Multiplicative.toAdd.injective
    (lTransl_one_apply (Multiplicative.toAdd f))
  map_mul' g₁ g₂ := MulEquiv.ext fun f => Multiplicative.toAdd.injective
    (lTransl_mul_apply g₁ g₂ (Multiplicative.toAdd f))

@[scoped simp] theorem toAdd_lTranslMulAut (g : CoprodI G)
    (f : Multiplicative (CoprodI G →₀ ℤ)) :
    Multiplicative.toAdd (lTranslMulAut g f) = lTransl g (Multiplicative.toAdd f) := rfl

/-- The semidirect product carrying the actual edge-chain cocycle. -/
abbrev ChainCarrier (G : Fin 2 → Type*) [∀ i, Group (G i)] : Type _ :=
  SemidirectProduct (Multiplicative (CoprodI G →₀ ℤ)) (CoprodI G) lTranslMulAut

/-- The lifted second cyclic-factor homomorphism with its edge boundary. -/
def factorOneSect : G 1 →* ChainCarrier G where
  toFun a := ⟨Multiplicative.ofAdd
      (Finsupp.single 1 1 - Finsupp.single (CoprodI.of a) 1 : CoprodI G →₀ ℤ),
    CoprodI.of a⟩
  map_one' := by
    refine SemidirectProduct.ext ?_ ?_
    · show Multiplicative.ofAdd (Finsupp.single 1 1 - Finsupp.single (of (1 : G 1)) 1) = 1
      rw [map_one, sub_self]; rfl
    · exact map_one _
  map_mul' a b := by
    refine SemidirectProduct.ext ?_ (map_mul CoprodI.of a b)
    show Multiplicative.ofAdd
        (Finsupp.single 1 1 - Finsupp.single (of (a * b)) 1 : CoprodI G →₀ ℤ) =
      Multiplicative.ofAdd (Finsupp.single 1 1 - Finsupp.single (of a) 1) *
        lTranslMulAut (of a)
          (Multiplicative.ofAdd (Finsupp.single 1 1 - Finsupp.single (of b) 1))
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_lTranslMulAut, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd,
      map_sub, lTransl_single, lTransl_single, mul_one, map_mul,
      sub_add_sub_cancel]

/-- The free-product homomorphism defining the edge-chain cocycle. -/
def chainSect : CoprodI G →* ChainCarrier G :=
  CoprodI.lift fun i =>
    match i with
    | 0 => SemidirectProduct.inr.comp CoprodI.of
    | 1 => factorOneSect

@[scoped simp] theorem chainSect_right (g : CoprodI G) : (chainSect g).right = g := by
  have h : SemidirectProduct.rightHom.comp chainSect = MonoidHom.id (CoprodI G) := by
    refine CoprodI.ext_hom _ _ fun i => ?_
    match i with
    | 0 => ext a; rfl
    | 1 => ext a; rfl
  exact DFunLike.congr_fun h g

/-- The finite integer edge chain of a free-product word. -/
def edgeChain (g : CoprodI G) : CoprodI G →₀ ℤ :=
  Multiplicative.toAdd (chainSect g).left

@[scoped simp] theorem edgeChain_one : edgeChain (1 : CoprodI G) = 0 := by
  unfold edgeChain; rw [map_one]; rfl

theorem edgeChain_mul (g₁ g₂ : CoprodI G) :
    edgeChain (g₁ * g₂) = edgeChain g₁ + lTransl g₁ (edgeChain g₂) := by
  unfold edgeChain
  rw [map_mul, SemidirectProduct.mul_left, chainSect_right, toAdd_mul, toAdd_lTranslMulAut]

@[scoped simp] theorem edgeChain_of_zero (a : G 0) :
    edgeChain (CoprodI.of a : CoprodI G) = 0 := by
  unfold edgeChain chainSect
  rw [CoprodI.lift_of]
  rfl

@[scoped simp] theorem edgeChain_of_one (a : G 1) :
    edgeChain (CoprodI.of a : CoprodI G)
      = Finsupp.single 1 1 - Finsupp.single (CoprodI.of a) 1 := by
  unfold edgeChain chainSect
  rw [CoprodI.lift_of]
  rfl

theorem edgeChain_inv (g : CoprodI G) :
    edgeChain g⁻¹ = -lTransl g⁻¹ (edgeChain g) := by
  have h := edgeChain_mul g⁻¹ g
  rw [inv_mul_cancel, edgeChain_one, eq_comm, add_eq_zero_iff_eq_neg] at h
  exact h

theorem edgeChain_of_zero_mul_of_one (a : G 0) (b : G 1) :
    edgeChain (CoprodI.of a * CoprodI.of b : CoprodI G)
      = Finsupp.single (CoprodI.of a) 1 - Finsupp.single (CoprodI.of a * CoprodI.of b) 1 := by
  rw [edgeChain_mul, edgeChain_of_zero, edgeChain_of_one, zero_add, map_sub,
    lTransl_single, lTransl_single, mul_one]
end EdgeChain

end
end Dubon2026.SourceCuspCorrection
