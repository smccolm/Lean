import Dubon2026.SourceGammaOneCuspCyclicOrbit

/-! DUB-17/18 -> actual Gamma1 real period surjectivity -> exact cusp
widths. The finite original cosets modulo the central-sign enlargement
map to actual cusp places. Translation acts on these cosets, and the
place map is invariant under every integral power. The original function
field is retained throughout. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open Matrix.SpecialLinearGroup ModularGroup SourceCurve
open scoped MatrixGroups

theorem cuspPlace_mul_left_plusMinus
    {Γ : Subgroup SL(2, ℤ)} (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : T ∈ Γ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ plusMinus Γ) (δ : SL(2, ℤ)) :
    cuspPlace N hΓ hT (γ * δ) = cuspPlace N hΓ hT δ := by
  apply Place.ext
  apply SetLike.ext
  intro x
  rw [cuspPlace_mem_iff, cuspPlace_mem_iff]
  have he := meromorphicOrderAt_congr
    (cuspRealize_mul_left_plusMinus_eventuallyEq N hΓ hT x hγ δ)
  change (0 ≤ cuspOrder Γ N (γ * δ) x) ↔ 0 ≤ cuspOrder Γ N δ x
  rw [show cuspOrder Γ N (γ * δ) x = cuspOrder Γ N δ x from he]

namespace CuspCounting
variable (Γ : Subgroup SL(2, ℤ))

/-- Actual integral cosets modulo the subgroup and the central negative identity. -/
abbrev Cosets : Type := SL(2, ℤ) ⧸ plusMinus Γ

/-- The integral translation acting by left multiplication on actual cosets. -/
def translation : Equiv.Perm (Cosets Γ) := MulAction.toPerm (T : SL(2, ℤ))

theorem translation_zpow_apply (n : ℤ) (x : Cosets Γ) :
    (translation Γ ^ n) x = (T ^ n : SL(2, ℤ)) • x := by
  change ((MulAction.toPermHom SL(2, ℤ) (Cosets Γ)) T ^ n) x = _
  rw [← map_zpow]
  rfl

variable {Γ} (N : ℕ) [NeZero N]
  (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : T ∈ Γ)

/-- The actual cusp place attached to the inverse representative of an integral coset. -/
def cosetPlace : Cosets Γ → Place ℂ (functionFieldOver Γ ℂ) :=
  Quotient.lift (fun g => cuspPlace N hΓ hT g⁻¹) (by
    intro a b hab
    change cuspPlace N hΓ hT a⁻¹ = cuspPlace N hΓ hT b⁻¹
    have hm := QuotientGroup.leftRel_apply.mp hab
    have hb : b⁻¹ = (a⁻¹ * b)⁻¹ * a⁻¹ := by group
    rw [hb]
    exact (cuspPlace_mul_left_plusMinus N hΓ hT (inv_mem hm) a⁻¹).symm)

theorem cosetPlace_mk (g : SL(2, ℤ)) :
    cosetPlace N hΓ hT (g : Cosets Γ) = cuspPlace N hΓ hT g⁻¹ := rfl

theorem cosetPlace_j_neg (x : Cosets Γ) :
    (cosetPlace N hΓ hT x).ord (jCoordinateOver Γ ℂ) < 0 := by
  induction x using QuotientGroup.induction_on with
  | H g => exact cuspPlace_j_neg N hΓ hT g⁻¹

theorem cosetPlace_translation_zpow (n : ℤ) (x : Cosets Γ) :
    cosetPlace N hΓ hT ((translation Γ ^ n) x) = cosetPlace N hΓ hT x := by
  rw [translation_zpow_apply]
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, cosetPlace_mk,
      cosetPlace_mk, mul_inv_rev, ← zpow_neg, cuspPlace_mul_T_zpow N hΓ hT]

theorem exists_cosetPlace_of_j_pole
    (P : Place ℂ (functionFieldOver Γ ℂ)) (hP : P.ord (jCoordinateOver Γ ℂ) < 0) :
    ∃ x : Cosets Γ, cosetPlace N hΓ hT x = P := by
  obtain ⟨δ, rfl⟩ := exists_cusp_place_eq_of_j_pole N hΓ hT P hP
  exact ⟨(δ⁻¹ : SL(2, ℤ)), by rw [cosetPlace_mk, inv_inv]⟩

/-- The actual cyclic translation orbits on the original finite coset space. -/
abbrev Orbits := SourceManin.Orb (translation Γ)

/-- The actual cusp place attached to a cyclic translation orbit of cosets. -/
def orbitPlace : Orbits (Γ := Γ) → Place ℂ (functionFieldOver Γ ℂ) :=
  Quotient.lift (cosetPlace N hΓ hT) (by
    intro x y hxy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hxy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    change (g.val : Equiv.Perm (Cosets Γ)) y = x at hg
    rw [← hg, ← hn]
    exact cosetPlace_translation_zpow N hΓ hT n y)

theorem orbitPlace_mk (x : Cosets Γ) :
    orbitPlace N hΓ hT (SourceManin.orbQ (translation Γ) x) = cosetPlace N hΓ hT x := rfl

theorem orbitPlace_j_neg (q : Orbits (Γ := Γ)) :
    (orbitPlace N hΓ hT q).ord (jCoordinateOver Γ ℂ) < 0 := by
  induction q using Quotient.inductionOn with
  | h x => exact cosetPlace_j_neg N hΓ hT x

theorem exists_orbitPlace_of_j_pole
    (P : Place ℂ (functionFieldOver Γ ℂ)) (hP : P.ord (jCoordinateOver Γ ℂ) < 0) :
    ∃ q : Orbits (Γ := Γ), orbitPlace N hΓ hT q = P := by
  obtain ⟨x, hx⟩ := exists_cosetPlace_of_j_pole N hΓ hT P hP
  exact ⟨SourceManin.orbQ (translation Γ) x, hx⟩

end CuspCounting
end
end Dubon2026.SourceFunctionField.GammaOne
