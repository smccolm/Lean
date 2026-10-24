import Dubon2026.SourceEllipticFiniteTorsionField
import Dubon2026.SourceEllipticLegendreCoordinates

/-! The finite Galois Legendre good-model stage and its faithful inertia.
The generators are the actual two-torsion abscissae and square roots of
their nonzero differences. This realizes the model and action required by
the positive-characteristic exceptional-fiber census, reverse genus and
good reduction in DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, finite Legendre model proof.
Native valuation-ring inertia and the existing explicit good model are reused.
No characteristic-zero Hahn-series route is introduced. -/
namespace Dubon2026.SourceEllipticLegendreStage
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial
open Dubon2026.SourceEllipticLegendre
open scoped Pointwise
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
section Cubic

variable (E : WeierstrassCurve F)

lemma map_twoTorsionPolynomial {S : Type*} [CommRing S] (φ : F →+* S) :
    Cubic.map φ E.twoTorsionPolynomial = (E.map φ).twoTorsionPolynomial := by
  simp only [twoTorsionPolynomial, Cubic.map, map_b₂, map_b₄, map_b₆, map_ofNat, map_mul]

variable [E.IsElliptic] [IsAlgClosed Ω] (h2 : (2 : F) ≠ 0)

omit [E.IsElliptic] in
include h2 in
lemma four_ne_zero : E.twoTorsionPolynomial.a ≠ 0 := by
  show (4 : F) ≠ 0
  rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2

include h2 in

lemma exists_roots : ∃ e₁ e₂ e₃ : Ω,
    (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃} ∧
      e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ := by
  have ha := four_ne_zero E h2
  obtain ⟨e₁, e₂, e₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp
    (IsAlgClosed.splits (E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω)))
  have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
    E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) E.isUnit_Δ
  exact ⟨e₁, e₂, e₃, h3, (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc⟩

include h2 in

lemma separable_twoTorsion : (E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω)).Separable := by
  have ha := four_ne_zero E h2
  have hspl := IsAlgClosed.splits (E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω))
  have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
    E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) E.isUnit_Δ
  have hnodup := (Cubic.discr_ne_zero_iff_roots_nodup ha hspl).mp hdisc
  rw [Cubic.map_roots] at hnodup
  have hne : E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω) ≠ 0 :=
    Polynomial.map_ne_zero (Cubic.ne_zero_of_a_ne_zero ha)
  exact (nodup_roots_iff_of_splits hne hspl).mp hnodup

end Cubic

variable [DecidableEq Ω]
/-- Differences of distinct indexed two-torsion abscissae. -/
def diffs (e₁ e₂ e₃ : Ω) : Finset Ω := {e₂ - e₁, e₁ - e₂, e₃ - e₁, e₁ - e₃, e₃ - e₂, e₂ - e₃}

/-- All three abscissae and both square roots of each difference. -/
def gens (e₁ e₂ e₃ : Ω) : Finset Ω :=
  {e₁, e₂, e₃} ∪ (diffs e₁ e₂ e₃).biUnion fun d => (nthRoots 2 d).toFinset

lemma mem_gens_of_sq {e₁ e₂ e₃ q : Ω} (hq : q ^ 2 ∈ diffs e₁ e₂ e₃) : q ∈ gens e₁ e₂ e₃ := by
  rw [gens, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨q ^ 2, hq, by rw [Multiset.mem_toFinset, mem_nthRoots (by norm_num)]⟩

lemma mem_gens_cases {e₁ e₂ e₃ x : Ω} (hx : x ∈ gens e₁ e₂ e₃) :
    (x = e₁ ∨ x = e₂ ∨ x = e₃) ∨ x ^ 2 ∈ diffs e₁ e₂ e₃ := by
  rw [gens, Finset.mem_union, Finset.mem_biUnion] at hx
  rcases hx with h | ⟨d, hd, hq⟩
  · left; simpa using h
  · right; rw [Multiset.mem_toFinset, mem_nthRoots (by norm_num)] at hq; rwa [hq]

lemma mem_diffs_iff {e₁ e₂ e₃ d : Ω} : d ∈ diffs e₁ e₂ e₃ ↔
    d = e₂ - e₁ ∨ d = e₁ - e₂ ∨ d = e₃ - e₁ ∨ d = e₁ - e₃ ∨ d = e₃ - e₂ ∨ d = e₂ - e₃ := by
  simp [diffs]

lemma sub_mem_diffs {e₁ e₂ e₃ x y : Ω} (hx : x = e₁ ∨ x = e₂ ∨ x = e₃) (hy : y = e₁ ∨ y = e₂ ∨ y = e₃)
    (hxy : x ≠ y) : x - y ∈ diffs e₁ e₂ e₃ := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first | exact absurd rfl hxy | simp [diffs]

lemma exists_of_mem_diffs {e₁ e₂ e₃ d : Ω} (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (hd : d ∈ diffs e₁ e₂ e₃) :
    ∃ x y : Ω, (x = e₁ ∨ x = e₂ ∨ x = e₃) ∧ (y = e₁ ∨ y = e₂ ∨ y = e₃) ∧ x ≠ y ∧ d = x - y := by
  rcases mem_diffs_iff.mp hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨e₂, e₁, by tauto, by tauto, Ne.symm h12, rfl⟩
  · exact ⟨e₁, e₂, by tauto, by tauto, h12, rfl⟩
  · exact ⟨e₃, e₁, by tauto, by tauto, Ne.symm h13, rfl⟩
  · exact ⟨e₁, e₃, by tauto, by tauto, h13, rfl⟩
  · exact ⟨e₃, e₂, by tauto, by tauto, Ne.symm h23, rfl⟩
  · exact ⟨e₂, e₃, by tauto, by tauto, h23, rfl⟩


end
end Dubon2026.SourceEllipticLegendreStage
