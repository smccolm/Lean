import Dubon2026.GaloisRootOfUnityRepresentation
import Dubon2026.AlgebraicallyClosedUnitPowerSequence

/-! # The original equivariant root inclusion and unit power coefficient sequence -/

namespace Dubon2026
noncomputable section
open CategoryTheory

private def multiplicativeCoefficientMorphism {G M N : Type}
    [Monoid G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (f : M →* N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x) :
    Rep.ofMulDistribMulAction G M ⟶ Rep.ofMulDistribMulAction G N :=
  Rep.ofHom {
    toLinearMap := f.toAdditive.toIntLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      exact hf g x }

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)

/-- The original root-of-unity inclusion is a morphism of the actual Galois
representations, retaining the original integer module structures. -/
def galoisKummerInclusion :
    galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n ⟶ Rep.ofAlgebraAutOnUnits K Ω :=
  multiplicativeCoefficientMorphism (rootsOfUnity n Ω).subtype (fun _ _ => rfl)

/-- The actual unit nth-power map is an endomorphism of the original Galois
unit representation, through the original additive tag. -/
def galoisKummerPower : Rep.ofAlgebraAutOnUnits K Ω ⟶ Rep.ofAlgebraAutOnUnits K Ω :=
  multiplicativeCoefficientMorphism (powMonoidHom n : Ωˣ →* Ωˣ)
    (galoisUnitPower_equivariant (K := K) n)

/-- The representation inclusion sends the same actual root unit to the same
original extension-field unit. -/
theorem galoisKummerInclusion_apply (u : rootsOfUnity n Ω) :
    (galoisKummerInclusion (K := K) n).hom (Rep.toAdditive.symm (Additive.ofMul u)) =
      Rep.toAdditive.symm (Additive.ofMul (u : Ωˣ)) := by
  rfl

/-- The representation endomorphism is the literal nth power of the original unit. -/
theorem galoisKummerPower_apply (u : Ωˣ) :
    (galoisKummerPower (K := K) n).hom (Rep.toAdditive.symm (Additive.ofMul u)) =
      Rep.toAdditive.symm (Additive.ofMul (u ^ n)) := by
  rfl

/-- The original root representation inclusion is genuinely injective. -/
theorem galoisKummerInclusion_injective :
    Function.Injective (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap := by
  intro x y h
  change ((Additive.toMul (Rep.toAdditive x) : rootsOfUnity n Ω) : Ωˣ) =
    ((Additive.toMul (Rep.toAdditive y) : rootsOfUnity n Ω) : Ωˣ) at h
  exact Subtype.ext h

/-- Actual algebraic closedness makes the original Galois unit power morphism
surjective for positive n; its preimages are original extension-field units. -/
theorem galoisKummerPower_surjective [IsAlgClosed Ω] (hn : 0 < n) :
    Function.Surjective (galoisKummerPower (K := K) (Ω := Ω) n).hom.toLinearMap := by
  intro x
  obtain ⟨u, hu⟩ := algebraicallyClosedUnitPower_surjective n hn
    (Additive.toMul (Rep.toAdditive x))
  refine ⟨Rep.toAdditive.symm (Additive.ofMul u), ?_⟩
  exact hu

/-- The actual inclusion range is exactly the actual power-map kernel, with
the original root-of-unity group as coefficient object. -/
theorem galoisKummerCoefficient_exact :
    LinearMap.range (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap =
      LinearMap.ker (galoisKummerPower (K := K) (Ω := Ω) n).hom.toLinearMap := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    change ((Additive.toMul (Rep.toAdditive u) : rootsOfUnity n Ω) : Ωˣ) ^ n = 1
    exact (Additive.toMul (Rep.toAdditive u) : rootsOfUnity n Ω).property
  · intro hx
    change (Additive.toMul (Rep.toAdditive x) : Ωˣ) ^ n = 1 at hx
    refine ⟨Rep.toAdditive.symm (Additive.ofMul
      (⟨Additive.toMul (Rep.toAdditive x), hx⟩ : rootsOfUnity n Ω)), ?_⟩
    rfl

end
end Dubon2026
