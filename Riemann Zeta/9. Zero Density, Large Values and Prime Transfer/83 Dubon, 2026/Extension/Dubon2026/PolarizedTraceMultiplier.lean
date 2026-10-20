import Dubon2026.PolarizedPointTopology
import Mathlib.Topology.Algebra.Algebra

/-! The prescribed base multiplier is continuous over the actual trace
subalgebra because the original polarized lift realizes it. This avoids
adding a multiplier-continuity assumption in DUB-17's CM trace descent. -/

namespace Dubon2026
open Matrix

variable {O R ι G : Type*} [CommRing O] [CommRing R] [Algebra O R]
  [Fintype ι] [DecidableEq ι] [TopologicalSpace R] [IsTopologicalRing R]

omit [CommRing O] [Algebra O R] in
/-- The actual source similitude is continuous in the original coordinate topology. -/
theorem polarizedSimilitude_continuous :
    Continuous (polarizedSimilitude (R := R) (ι := ι)) :=
  (polarizedPointHomeomorph.continuous.fst.snd).mul
    (continuous_of_discreteTopology.comp polarizedPointHomeomorph.continuous.snd)

omit [Fintype ι] [DecidableEq ι] [IsTopologicalRing R] in
/-- Continuity of unit-valued functions into a coefficient subalgebra is
reflected by its original inclusion, for both unit and inverse coordinates. -/
theorem coefficientSubalgebra_units_continuous [TopologicalSpace G]
    (S : Subalgebra O R) (f : G → Sˣ)
    (hf : Continuous (fun x => Units.map S.val.toMonoidHom (f x))) : Continuous f := by
  apply Units.continuous_iff.mpr
  exact ⟨(Units.continuous_val.comp hf).subtype_mk _,
    (Units.continuous_coe_inv.comp hf).subtype_mk _⟩

/-- The original polarized representation forces continuity of its base
character over every original coefficient subalgebra, including its CM
trace algebra; no extra topological condition on the base character is used. -/
theorem polarizedBaseCharacter_subalgebra_continuous [Group G] [TopologicalSpace G]
    (ρ : G →ₜ* PolarizedGaloisGroup ι R) (ν : G →* Oˣ)
    (hν : ∀ x, polarizedSimilitude (ρ x) = Units.map (algebraMap O R).toMonoidHom (ν x))
    (S : Subalgebra O R) :
    Continuous ((Units.map (algebraMap O S).toMonoidHom).comp ν) := by
  apply coefficientSubalgebra_units_continuous S
  have he : (fun x => Units.map S.val.toMonoidHom
      (((Units.map (algebraMap O S).toMonoidHom).comp ν) x)) =
      (fun x => polarizedSimilitude (ρ x)) := by
    funext x
    exact (hν x).symm
  rw [he]
  exact polarizedSimilitude_continuous.comp ρ.continuous

end Dubon2026
