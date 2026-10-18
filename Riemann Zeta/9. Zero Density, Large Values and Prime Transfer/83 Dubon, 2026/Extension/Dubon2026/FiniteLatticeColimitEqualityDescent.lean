import Dubon2026.FiniteLatticeColimitHomDescent

/-! Preserve a relation equation when descending a finite free lattice.
Only its finitely many basis differences need direct-limit zero detection.
This supplies DUB-17's exact relation equality at the same finite stage
as its source-class extension, before the projective S-place lift. -/
namespace Dubon2026
noncomputable section

variable {R ι : Type} [CommRing R] [Preorder ι] [DecidableEq ι]
  [Nonempty ι] [IsDirectedOrder ι]
  (A : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  (f : ∀ i j, i ≤ j → A i →ₗ[R] A j) [DirectedSystem A (f · · ·)]
  (B : Type) [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Free R B]

/-- Two actual maps from a finite free lattice that agree in the direct
limit agree after one transition, on every lattice element. -/
theorem finiteLatticeColimitEquality_exists_stage (i : ι)
    (φ ψ : B →ₗ[R] A i)
    (he : (Module.DirectLimit.of R ι A f i).comp φ =
      (Module.DirectLimit.of R ι A f i).comp ψ) :
    ∃ j, ∃ hij : i ≤ j, (f i j hij).comp φ = (f i j hij).comp ψ := by
  classical
  let J := Module.Free.ChooseBasisIndex R B
  let β := Module.Free.chooseBasis R B
  let d : J → A i := fun e => φ (β e) - ψ (β e)
  have hd : (Set.range d).Finite := Set.finite_range d
  have hz (x : A i) (hx : x ∈ hd.toFinset) : Module.DirectLimit.of R ι A f i x = 0 := by
    obtain ⟨e, rfl⟩ := hd.mem_toFinset.mp hx
    change Module.DirectLimit.of R ι A f i (φ (β e) - ψ (β e)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun he (β e))
  obtain ⟨j, hij, hj⟩ := coefficientColimit_finite_zero_detected A f i hd.toFinset hz
  refine ⟨j, hij, ?_⟩
  apply β.ext
  intro e
  have h := hj (d e) (hd.mem_toFinset.mpr (Set.mem_range_self e))
  change f i j hij (φ (β e) - ψ (β e)) = 0 at h
  rw [map_sub] at h
  exact sub_eq_zero.mp h

end
end Dubon2026
