import Mathlib.RepresentationTheory.Coinduced
import Mathlib.GroupTheory.GroupAction.Transitive

/-! # Representations on products of coherently transported local factors

Original completion maps have different source and target fields. Their
proved identity and composition laws give the dependent product action
and the stabilizer action on one original factor. These are the precise
inputs needed to apply Shapiro to DUB-17's actual idele coordinates.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)

/-- The coordinate linear map induced by the actual transport maps. -/
def transportedPiMap (g : G) : (∀ i, M i) →ₗ[R] (∀ i, M i) where
  toFun x j := T g (g⁻¹ • j) j (smul_inv_smul g j) (x (g⁻¹ • j))
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_smul _ _ _

/-- The product action uses the specified transport at any actual source and target coordinate. -/
theorem transportedPiMap_apply (g : G) (x : ∀ i, M i) (i j : ι) (h : g • i = j) :
    transportedPiMap R G ι M T g x j = T g i j h (x i) := by
  have he : g⁻¹ • j = i := by rw [← h, inv_smul_smul]
  dsimp only [transportedPiMap, LinearMap.coe_mk, AddHom.coe_mk]
  generalize_proofs hp
  cases he
  rfl

variable
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))

/-- The representation on the actual dependent product defined by the coherent transports. -/
def transportedPiRep : Rep R G := Rep.of {
  toFun := transportedPiMap R G ι M T
  map_one' := by
    apply LinearMap.ext
    intro x
    funext i
    rw [transportedPiMap_apply R G ι M T 1 x i i (one_smul G i)]
    exact T_one i (x i)
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro x
    funext k
    let j := g⁻¹ • k
    let i := h⁻¹ • j
    have hh : h • i = j := smul_inv_smul h j
    have hg : g • j = k := smul_inv_smul g k
    have hgh : (g * h) • i = k := by rw [mul_smul, hh, hg]
    change transportedPiMap R G ι M T (g * h) x k =
      transportedPiMap R G ι M T g (transportedPiMap R G ι M T h x) k
    rw [transportedPiMap_apply R G ι M T (g * h) x i k hgh,
      transportedPiMap_apply R G ι M T g _ j k hg,
      transportedPiMap_apply R G ι M T h x i j hh]
    exact T_mul g h i j k hh hg hgh (x i) }

/-- The original transport action of the actual point stabilizer on one actual factor. -/
def transportedStabilizerRep (i : ι) : Rep R (MulAction.stabilizer G i) := Rep.of {
  toFun := fun g => (T g.val i i g.property).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    exact T_one i x
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro x
    exact T_mul g.val h.val i i i h.property g.property (g * h).property x }

/-- Original coordinate evaluation intertwines restriction and the actual stabilizer action. -/
def transportedStabilizerEvaluation (i : ι) :
    Rep.res (MulAction.stabilizer G i).subtype (transportedPiRep R G ι M T T_one T_mul) ⟶
      transportedStabilizerRep R G ι M T T_one T_mul i :=
  Rep.ofHom ⟨LinearMap.proj i, by
    intro g
    apply LinearMap.ext
    intro x
    exact transportedPiMap_apply R G ι M T g.val x i i g.property⟩

/-- The existing restriction/coinduction adjunction applied to original coordinate evaluation. -/
def transportedCoindHom (i : ι) :
    transportedPiRep R G ι M T T_one T_mul ⟶
      Rep.coind (MulAction.stabilizer G i).subtype
        (transportedStabilizerRep R G ι M T T_one T_mul i) :=
  Rep.resCoindToHom (MulAction.stabilizer G i).subtype _ _
    (transportedStabilizerEvaluation R G ι M T T_one T_mul i)

/-- The coinduction morphism is the original transported evaluation at the inverse orbit coordinate. -/
theorem transportedCoindHom_apply (i : ι) (x : ∀ j, M j) (g : G) :
    ((transportedCoindHom R G ι M T T_one T_mul i).hom x).val g =
      T g (g⁻¹ • i) i (smul_inv_smul g i) (x (g⁻¹ • i)) := rfl

end
end Dubon2026
