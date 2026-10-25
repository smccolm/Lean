import Mathlib.LinearAlgebra.BilinearMap

/-! DUB-17/18 -> original primitive Tate projector. Injective coordinates
transport a proved operator relation, without unfolding geometric models. -/
namespace Dubon2026

theorem hecke_relation_of_injective_coordinates
    {R A C V W : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (l : A → C) (u : A → Module.End R V) (e : V → W) (he : Function.Injective e)
    (v : C → W → W) (hu : ∀ a x, e (u a x) = v (l a) (e x))
    (a c : A) (h : l a = l c) : u a = u c := by
  apply LinearMap.ext
  intro x
  apply he
  rw [hu, hu, h]

end Dubon2026
