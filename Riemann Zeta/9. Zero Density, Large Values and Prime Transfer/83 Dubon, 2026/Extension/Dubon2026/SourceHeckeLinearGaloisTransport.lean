import Dubon2026.SourceGeneratedHeckeLinearity
import Mathlib.Algebra.Algebra.Equiv

/-! DUB-17/18 -> original rank-two Galois realization -> transport the
actual commuting Galois action to the coefficient algebra constructed by
Hecke descent. Prime equivariance and algebra generation prove scalar
linearity; the original group law is preserved by conjugation. -/
namespace Dubon2026
noncomputable section
variable {K T V G I : Type*} [CommRing K] [CommRing T] [Algebra K T]
    [AddCommMonoid V] [Module K V] [Monoid G]
    (χ : I → T) (hχ : Algebra.adjoin K (Set.range χ) = ⊤)
    (u : I → Module.End K V) (e : V ≃ₗ[K] (Fin 2 → T))
    (he : ∀ i x, e (u i x) = χ i • e x)
    (ρ : G →* Module.End K V) (hc : ∀ g i, Commute (ρ g) (u i))

include hχ he hc in
theorem heckeConjugate_map_smul (g : G) (t : T) (y : Fin 2 → T) :
    e (ρ g (e.symm (t • y))) = t • e (ρ g (e.symm y)) := by
  apply map_smul_of_generating_hecke χ hχ (e.conjAlgEquiv K (ρ g)) ?_ t y
  intro i y
  obtain ⟨x, rfl⟩ := e.surjective y
  change e (ρ g (e.symm (χ i • e x))) = χ i • e (ρ g (e.symm (e x)))
  rw [← he i x, e.symm_apply_apply, e.symm_apply_apply]
  exact (congrArg e (LinearMap.congr_fun (hc g i).eq x)).trans (he i (ρ g x))

/-- The same conjugated Galois action, with coefficient-algebra linearity proved from its primes. -/
def heckeLinearGaloisRep : G →* Module.End T (Fin 2 → T) where
  toFun g :=
    { (e.conjAlgEquiv K (ρ g)).toAddMonoidHom with
      map_smul' t y := heckeConjugate_map_smul χ hχ u e he ρ hc g t y }
  map_one' := by
    apply LinearMap.ext
    intro y
    change e (ρ 1 (e.symm y)) = y
    rw [map_one]
    exact e.apply_symm_apply y
  map_mul' g h := by
    apply LinearMap.ext
    intro y
    change e (ρ (g * h) (e.symm y)) = e (ρ g (e.symm (e (ρ h (e.symm y)))))
    rw [map_mul, e.symm_apply_apply]
    rfl

theorem heckeLinearGaloisRep_equivariant (g : G) (x : V) :
    heckeLinearGaloisRep χ hχ u e he ρ hc g (e x) = e (ρ g x) := by
  change e (ρ g (e.symm (e x))) = e (ρ g x)
  rw [e.symm_apply_apply]

end
end Dubon2026
