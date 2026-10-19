import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The dimension identity used by the actual arithmetic Selmer consumer.
The only duality premise is the exact image-annihilator equality, which the
original arithmetic localization theorem proves. No Euler-characteristic
formula or deformation dimension is assumed or asserted here. -/
namespace Dubon2026
noncomputable section

variable {K U V D : Type} [Field K]
  [AddCommGroup U] [Module K U] [Module.Finite K U]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup D] [Module K D] [Module.Finite K D]

private theorem comap_finrank (f : U →ₗ[K] V) (L : Submodule K V) :
    Module.finrank K (L.comap f) = Module.finrank K (L ⊓ LinearMap.range f : Submodule K V) +
      Module.finrank K (LinearMap.ker f) := by
  have hk : LinearMap.ker f ≤ L.comap f := by
    intro x hx
    change f x ∈ L
    rw [show f x = 0 from hx]
    exact L.zero_mem
  have hdim := (f.domRestrict (L.comap f)).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, Submodule.map_comap_eq,
    LinearMap.ker_domRestrict] at hdim
  rw [(Submodule.comapSubtypeEquivOfLe hk).finrank_eq] at hdim
  rw [inf_comm (LinearMap.range f) L] at hdim
  exact hdim.symm

/-- Exact annihilator duality determines the balanced Selmer dimensions,
retaining the actual everywhere-zero dual kernel. -/
theorem selmer_finrank_of_range_eq_annihilator
    (f : U →ₗ[K] V) (g : D →ₗ[K] Module.Dual K V)
    (hfg : LinearMap.range g = (LinearMap.range f).dualAnnihilator)
    (L : Submodule K V) :
    Module.finrank K (L.comap f) + Module.finrank K V + Module.finrank K (LinearMap.ker g) =
      Module.finrank K U + Module.finrank K L + Module.finrank K (L.dualAnnihilator.comap g) := by
  have hp := comap_finrank f L
  have hd := comap_finrank g L.dualAnnihilator
  rw [hfg, ← Submodule.dualAnnihilator_sup_eq] at hd
  have hs := Submodule.finrank_sup_add_finrank_inf_eq L (LinearMap.range f)
  have ha := Subspace.finrank_add_finrank_dualAnnihilator_eq (L ⊔ LinearMap.range f)
  have hf := f.finrank_range_add_finrank_ker
  omega

end
end Dubon2026
