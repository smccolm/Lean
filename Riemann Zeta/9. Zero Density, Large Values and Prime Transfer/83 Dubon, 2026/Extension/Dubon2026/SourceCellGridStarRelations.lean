import Dubon2026.SourceCellGridStarSides

/-! DUB-17/18 -> original Abel-Jacobi -> actual paired cell dissection.
Use the exact six-arc square and refined-window outputs to identify the two
regions sharing each side, its orientation and C1 reversal, and the finite
intersection chains at every boundary point. These are the planar inputs
to pairing the constructed original-curve cells and to their Euler count.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The existing rectangle and outer-window constructors provide the geometric
data; no new radial-region existence hypothesis is introduced by consumers.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.StarProperty
noncomputable section
open scoped Real
open Set

open PlanarRegions
variable (M : GridData)

/-- A square or exterior region contains the given point. -/
def Contains : Option (ℤ × ℤ) → ℂ → Prop
  | some p, v => p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ v ∈ (M.base p).K
  | none, v => v ∉ M.winReg.Kint

/-- A square or exterior region has the given boundary side. -/
def Shares : Option (ℤ × ℤ) → Set ℂ → Prop
  | some p, Z => p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ ∃ k : Fin (M.base p).N, (M.base p).arcSet k = Z
  | none, Z => ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ = Z

/-- Two regions share a boundary side through the specified point. -/
def Adj (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)) : Prop := ∃ Z : Set ℂ, Shares M ρ Z ∧ Shares M ρ' Z ∧ v ∈ Z

theorem contains_some_iff (p : ℤ × ℤ) (v : ℂ) :
    Contains M (some p) v ↔ p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ v ∈ (M.base p).K :=
  Iff.rfl

theorem contains_none_iff (v : ℂ) : Contains M none v ↔ v ∉ M.winReg.Kint :=
  Iff.rfl

theorem shares_some_iff (p : ℤ × ℤ) (Z : Set ℂ) :
    Shares M (some p) Z ↔
      p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ ∃ k : Fin (M.base p).N, (M.base p).arcSet k = Z :=
  Iff.rfl

theorem shares_none_iff (Z : Set ℂ) : Shares M none Z ↔ ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ = Z :=
  Iff.rfl

theorem adj_symm {v : ℂ} {ρ ρ' : Option (ℤ × ℤ)} (h : Adj M v ρ ρ') : Adj M v ρ' ρ := by
  obtain ⟨Z, h1, h2, hv⟩ := h
  exact ⟨Z, h2, h1, hv⟩

theorem adj_of_arcs {v : ℂ} {ρ ρ' : Option (ℤ × ℤ)} {Z : Set ℂ} (h : Shares M ρ Z) (h' : Shares M ρ' Z)
    (hv : v ∈ Z) : Adj M v ρ ρ' :=
  ⟨Z, h, h', hv⟩

theorem two_of_square {j kk : ℤ} (a : Fin (M.base (j, kk)).N) (j' kk' : ℤ)
    (hw' : (j', kk') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hne : j' ≠ j ∨ kk' ≠ kk)
    (a' : Fin (M.base (j', kk')).N) (heq : (M.base (j, kk)).arcSet a = (M.base (j', kk')).arcSet a')
    (hper : ∀ k₀ : Fin M.winReg.N, (M.base (j, kk)).arcSet a ≠ M.winReg.arcSet k₀)
    (hsq : ∀ (j'' kk'' : ℤ), (j'', kk'') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
      ∀ a'' : Fin (M.base (j'', kk'')).N, (M.base (j'', kk'')).arcSet a'' = (M.base (j, kk)).arcSet a →
        (j'' = j ∧ kk'' = kk) ∨ (j'' = j' ∧ kk'' = kk')) :
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ some (j, kk) ∧ Shares M ρ' ((M.base (j, kk)).arcSet a) ∧
      ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' ((M.base (j, kk)).arcSet a) → ρ'' = some (j, kk) ∨ ρ'' = ρ' := by
  refine ⟨some (j', kk'), some_mk_ne hne, (shares_some_iff M _ _).2 ⟨hw', a', heq.symm⟩, ?_⟩
  intro ρ'' h''
  rcases ρ'' with _ | ⟨j'', kk''⟩
  · obtain ⟨k₀, hk₀⟩ := (shares_none_iff M _).1 h''
    exact absurd hk₀.symm (hper k₀)
  · obtain ⟨hw'', a'', ha''⟩ := (shares_some_iff M _ _).1 h''
    rcases hsq j'' kk'' hw'' a'' ha'' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl (some_mk_eq e1 e2)
    · exact Or.inr (some_mk_eq e1 e2)

theorem two_with_outside {j kk : ℤ} (a : Fin (M.base (j, kk)).N) (k₀ : Fin M.winReg.N)
    (heq : (M.base (j, kk)).arcSet a = M.winReg.arcSet k₀)
    (hsq : ∀ (j'' kk'' : ℤ), (j'', kk'') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
      ∀ a'' : Fin (M.base (j'', kk'')).N, (M.base (j'', kk'')).arcSet a'' = (M.base (j, kk)).arcSet a →
        j'' = j ∧ kk'' = kk) :
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ some (j, kk) ∧ Shares M ρ' ((M.base (j, kk)).arcSet a) ∧
      ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' ((M.base (j, kk)).arcSet a) → ρ'' = some (j, kk) ∨ ρ'' = ρ' := by
  refine ⟨none, (Option.some_ne_none _).symm, (shares_none_iff M _).2 ⟨k₀, heq.symm⟩, ?_⟩
  intro ρ'' h''
  rcases ρ'' with _ | ⟨j'', kk''⟩
  · exact Or.inr rfl
  · obtain ⟨hw'', a'', ha''⟩ := (shares_some_iff M _ _).1 h''
    obtain ⟨e1, e2⟩ := hsq j'' kk'' hw'' a'' ha''
    exact Or.inl (some_mk_eq e1 e2)

theorem uniq_of_none (k₀ : Fin M.winReg.N) (q1 q2 : ℤ)
    (hsq : ∀ (j'' kk'' : ℤ), (j'', kk'') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
      ∀ a'' : Fin (M.base (j'', kk'')).N, (M.base (j'', kk'')).arcSet a'' = M.winReg.arcSet k₀ →
        j'' = q1 ∧ kk'' = q2) :
    ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' (M.winReg.arcSet k₀) → ρ'' = none ∨ ρ'' = some (q1, q2) := by
  intro ρ'' h''
  rcases ρ'' with _ | ⟨j'', kk''⟩
  · exact Or.inl rfl
  · obtain ⟨hw'', a'', ha''⟩ := (shares_some_iff M _ _).1 h''
    obtain ⟨e1, e2⟩ := hsq j'' kk'' hw'' a'' ha''
    exact Or.inr (some_mk_eq e1 e2)


end
end Dubon2026.SourceFunctionField.CellGeometry.StarProperty
