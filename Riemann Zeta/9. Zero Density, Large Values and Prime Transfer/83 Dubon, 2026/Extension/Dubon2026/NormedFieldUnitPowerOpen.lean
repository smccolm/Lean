import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Openness of actual field-unit powers from the inverse function theorem

This supplies the missing openness needed with the existing compact integer-unit
quotient and uniformizer decomposition to prove finiteness of local Kummer H1.
-/

namespace Dubon2026
noncomputable section

open Filter Topology

variable (K : Type) [NontriviallyNormedField K] [CompleteSpace K]

/-- If n is nonzero in the original complete normed field, its actual unit
nth-power subgroup is open. The strict derivative at one is the original n. -/
theorem normedField_unitPower_range_isOpen (n : ℕ) (hn : (n : K) ≠ 0) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  have hn0 : n ≠ 0 := by
    intro h
    exact hn (h ▸ Nat.cast_zero)
  have hf : HasStrictDerivAt (fun x : K => x ^ n) (n : K) 1 := by
    simpa only [id_eq, one_pow, mul_one] using (hasStrictDerivAt_id (1 : K)).pow n
  have hR : Set.range (fun x : K => x ^ n) ∈ 𝓝 (1 : K) := by
    have hm := hf.map_nhds_eq hn
    rw [one_pow] at hm
    rw [← hm]
    exact range_mem_map
  have hu : (fun u : Kˣ => (u : K)) ⁻¹' Set.range (fun x : K => x ^ n) ∈ 𝓝 (1 : Kˣ) :=
    Units.continuous_val.continuousAt.preimage_mem_nhds hR
  apply (powMonoidHom n : Kˣ →* Kˣ).range.isOpen_of_mem_nhds (g := (1 : Kˣ))
  apply mem_of_superset hu
  rintro u ⟨a, ha⟩
  change a ^ n = (u : K) at ha
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at ha
    exact u.ne_zero ha.symm
  exact ⟨Units.mk0 a ha0, Units.ext ha⟩

end
end Dubon2026
