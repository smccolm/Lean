import Dubon2026.SourceOriginalBranchedCells
import Dubon2026.SourceOriginalCellArcGeometry
import Mathlib.Algebra.Polynomial.Roots

/-! DUB-17/18 -> original Abel-Jacobi -> branch/pole arc matching.
The e separated inverse arcs contain all e possible roots over a base-side
point. Native polynomial root cardinality discharges exhaustive arc coverage.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.PowPullback
noncomputable section
open Set

theorem exists_lap_of_pow_mem {R R' : RadialRegion} {e : ℕ} (he : e ≠ 0)
    {lap : Fin e → Fin R.N → Fin R'.N}
    (himg : ∀ (j : Fin e) (k : Fin R.N),
      (fun u : ℂ => R.q + u ^ e) '' R'.arcSet (lap j k) = R.arcSet k)
    (hsep : ∀ k : Fin R.N, ∃ U : Fin e → Set ℂ, (∀ j, IsOpen (U j)) ∧
      Pairwise (fun j j' => Disjoint (U j) (U j')) ∧ ∀ j, R'.arcSet (lap j k) ⊆ U j)
    {k : Fin R.N} {u : ℂ} (hu : R.q + u ^ e ∈ R.arcSet k) :
    ∃ j : Fin e, u ∈ R'.arcSet (lap j k) := by
  classical
  obtain ⟨U, -, hdisj, hUsub⟩ := hsep k
  have hroot : ∀ j : Fin e, ∃ v ∈ R'.arcSet (lap j k), R.q + v ^ e = R.q + u ^ e := by
    intro j
    have hu' : R.q + u ^ e ∈ (fun v : ℂ => R.q + v ^ e) '' R'.arcSet (lap j k) := by
      rw [himg j k]
      exact hu
    obtain ⟨v, hv, hveq⟩ := hu'
    exact ⟨v, hv, hveq⟩
  choose v hv hveq using hroot
  have hvinj : Function.Injective v := by
    intro j j' hjj'
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hUsub j (hv j)) (hjj' ▸ hUsub j' (hv j'))
  have hpow : ∀ j, v j ^ e = u ^ e := fun j => add_left_cancel (hveq j)
  have hepos : 0 < e := Nat.pos_of_ne_zero he
  have himage : Finset.univ.image v ⊆ (Polynomial.nthRoots e (u ^ e)).toFinset := by
    intro z hz
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hepos).mpr (hpow j))
  have hcard : (Polynomial.nthRoots e (u ^ e)).toFinset.card ≤ (Finset.univ.image v).card := by
    rw [Finset.card_image_of_injective _ hvinj, Finset.card_univ, Fintype.card_fin]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots e (u ^ e))
  have humem : u ∈ (Polynomial.nthRoots e (u ^ e)).toFinset :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hepos).mpr rfl)
  rw [← Finset.eq_of_subset_of_card_le himage hcard] at humem
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp humem
  exact ⟨j, hj ▸ hv j⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.PowPullback
