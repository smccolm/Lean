import Dubon2026.PolarizedBlockRepresentation

/-! Faithfulness of the source polarized matrix realization. The positive
dimension and nontrivial coefficient ring are explicit, as they are for
the actual CM deformation problem. This permits reuse of genuine framed
matrix deformations without collapsing the polarized target in DUB-17. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Equality of the original block diagonal matrix with one forces both blocks to be one. -/
theorem polarizedBlockDiagonal_eq_one (g h : GeneralLinearGroup ι R)
    (he : polarizedBlockDiagonal g h = 1) : g = 1 ∧ h = 1 := by
  constructor
  · apply Units.ext
    ext i j
    have hij := congrArg (fun u : GeneralLinearGroup (ι ⊕ ι) R =>
      u.val (Sum.inl i) (Sum.inl j)) he
    simpa [polarizedBlockDiagonal, Matrix.one_apply] using hij
  · apply Units.ext
    ext i j
    have hij := congrArg (fun u : GeneralLinearGroup (ι ⊕ ι) R =>
      u.val (Sum.inr i) (Sum.inr j)) he
    simpa [polarizedBlockDiagonal, Matrix.one_apply] using hij

/-- The identity-component realization retains the original multiplier. -/
theorem polarizedIdentityBlockRepresentation_injective [Nonempty ι] :
    Function.Injective (polarizedIdentityBlockRepresentation (R := R) (ι := ι)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  obtain ⟨hg, hs⟩ := polarizedBlockDiagonal_eq_one x.1 (polarizedSwitch x).1 hx
  have hu : x.2 = 1 := by
    have hscalar : GeneralLinearGroup.scalar ι x.2 = 1 := by
      change GeneralLinearGroup.scalar ι x.2 * polarizedContragredient x.1 = 1 at hs
      simpa only [hg, map_one, mul_one] using hs
    obtain ⟨i⟩ := ‹Nonempty ι›
    apply Units.ext
    have hii := congrArg (fun g : GeneralLinearGroup ι R => g.val i i) hscalar
    simpa [GeneralLinearGroup.scalar, Matrix.scalar_apply] using hii
  exact Prod.ext hg hu

/-- A matrix representing the nonidentity component cannot be the identity matrix. -/
theorem polarizedBlockRepresentation_ne_one_of_component [Nonempty ι] [Nontrivial R]
    (x : PolarizedGaloisGroup ι R) (hz : x.right.toAdd ≠ 0) :
    polarizedBlockRepresentation x ≠ 1 := by
  intro he
  rw [polarizedBlockRepresentation_apply, if_neg hz] at he
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hii := congrArg (fun g : GeneralLinearGroup (ι ⊕ ι) R =>
    g.val (Sum.inl i) (Sum.inl i)) he
  simp [polarizedBlockDiagonal, polarizedBlockSwap, fromBlocks_multiply] at hii

/-- The doubled matrix representation is faithful on the full source polarized group. -/
theorem polarizedBlockRepresentation_injective [Nonempty ι] [Nontrivial R] :
    Function.Injective (polarizedBlockRepresentation (R := R) (ι := ι)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hz : x.right.toAdd = 0 := by
    by_contra hn
    exact polarizedBlockRepresentation_ne_one_of_component x hn hx
  have hl : x.left = 1 := by
    apply polarizedIdentityBlockRepresentation_injective
    rw [map_one]
    rw [polarizedBlockRepresentation_apply, if_pos hz, mul_one] at hx
    exact hx
  exact SemidirectProduct.ext hl hz

end Dubon2026
