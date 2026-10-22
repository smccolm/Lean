import Dubon2026.SourceCellSideRealization

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
namespace Dubon2026.SourceFunctionField.CellGeometry.GridVertices
noncomputable section
open scoped Real
open Set

theorem strip_ne_grid (o : ℝ) {hm : ℝ} (hhm : 0 < hm) {k m : ℤ} {y : ℝ} (h₀ : o + k * hm < y)
    (h₁ : y < o + (k + 1) * hm) (h : y = o + m * hm) : False := by
  subst h
  have h₂ := SideIdentity.int_lt_of_grid₀₀ o hhm k m h₀
  have h₃ := SideIdentity.int_lt_of_grid₀₁ o hhm m k h₁
  omega

theorem strip_eq_strip (o : ℝ) {hm : ℝ} (hhm : 0 < hm) {k k' : ℤ} {y y' : ℝ} (h₀ : o + k * hm < y)
    (h₁ : y < o + (k + 1) * hm) (h₀' : o + k' * hm < y') (h₁' : y' < o + (k' + 1) * hm) (h : y = y') :
    k = k' := by
  subst h
  have l₁ := h₀.trans h₁'
  have l₂ := h₀'.trans h₁
  have i₁ := SideIdentity.int_lt_of_grid₀₁ o hhm k k' l₁
  have i₂ := SideIdentity.int_lt_of_grid₀₁ o hhm k' k l₂
  omega

theorem complex_mk_eq {a b c d : ℝ} (h₁ : a = c) (h₂ : b = d) : (⟨a, b⟩ : ℂ) = ⟨c, d⟩ := by
  subst h₁
  subst h₂
  rfl

/-- Source left-side split, using its own center at the outer boundary. -/
def yL (jlo : ℤ) (ctr : ℤ × ℤ → ℂ) (p : ℤ × ℤ) : ℝ :=
  if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im


/-- One grid-line intersection. -/
def cornerPt (o hm : ℝ) (q : ℤ × ℤ) : ℂ := ⟨o + q.1 * hm, o + q.2 * hm⟩

/-- One right-side split vertex. -/
def rightPt (o hm : ℝ) (ctr : ℤ × ℤ → ℂ) (q : ℤ × ℤ) : ℂ := ⟨o + (q.1 + 1) * hm, (ctr q).im⟩

/-- One left-boundary split vertex. -/
def leftPt (o hm : ℝ) (jlo : ℤ) (ctr : ℤ × ℤ → ℂ) (k : ℤ) : ℂ := ⟨o + jlo * hm, (ctr (jlo, k)).im⟩

/-- All grid-line vertices in the window. -/
def corners (o hm : ℝ) (jlo jhi klo khi : ℤ) : Finset ℂ :=
  (Finset.Icc jlo (jhi + 1) ×ˢ Finset.Icc klo (khi + 1)).image (cornerPt o hm)

/-- All right-side split vertices in the window. -/
def rights (o hm : ℝ) (jlo jhi klo khi : ℤ) (ctr : ℤ × ℤ → ℂ) : Finset ℂ :=
  (Finset.Icc jlo jhi ×ˢ Finset.Icc klo khi).image (rightPt o hm ctr)

/-- All left-boundary split vertices. -/
def lefts (o hm : ℝ) (jlo klo khi : ℤ) (ctr : ℤ × ℤ → ℂ) : Finset ℂ :=
  (Finset.Icc klo khi).image (leftPt o hm jlo ctr)

/-- The complete finite set of planar boundary vertices. -/
def B₀ (o hm : ℝ) (jlo jhi klo khi : ℤ) (ctr : ℤ × ℤ → ℂ) : Finset ℂ :=
  corners o hm jlo jhi klo khi ∪ rights o hm jlo jhi klo khi ctr ∪ lefts o hm jlo klo khi ctr

variable {o hm : ℝ} {jlo jhi klo khi : ℤ} {ctr : ℤ × ℤ → ℂ}

theorem yL_of_eq {j : ℤ} (hj : j = jlo) (k : ℤ) : yL jlo ctr (j, k) = (ctr (j, k)).im := by
  simp [yL, hj]

theorem yL_of_ne {j : ℤ} (hj : j ≠ jlo) (k : ℤ) : yL jlo ctr (j, k) = (ctr (j - 1, k)).im := by
  simp [yL, hj]

theorem yL_left (k : ℤ) : yL jlo ctr (jlo, k) = (ctr (jlo, k)).im :=
  yL_of_eq rfl k

theorem mem_corners {v : ℂ} :
    v ∈ corners o hm jlo jhi klo khi ↔
      ∃ j k : ℤ, jlo ≤ j ∧ j ≤ jhi + 1 ∧ klo ≤ k ∧ k ≤ khi + 1 ∧ v = (⟨o + j * hm, o + k * hm⟩ : ℂ) := by
  unfold corners
  constructor
  · intro h
    obtain ⟨⟨j, k⟩, hq, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hj, hk⟩ := Finset.mem_product.mp hq
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    exact ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩
  · rintro ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩
    exact Finset.mem_image.mpr ⟨(j, k),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hj₁, hj₂⟩, Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩⟩, rfl⟩

theorem mem_rights {v : ℂ} :
    v ∈ rights o hm jlo jhi klo khi ctr ↔
      ∃ j k : ℤ, jlo ≤ j ∧ j ≤ jhi ∧ klo ≤ k ∧ k ≤ khi ∧
        v = (⟨o + (j + 1) * hm, (ctr (j, k)).im⟩ : ℂ) := by
  unfold rights
  constructor
  · intro h
    obtain ⟨⟨j, k⟩, hq, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hj, hk⟩ := Finset.mem_product.mp hq
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    exact ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩
  · rintro ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩
    exact Finset.mem_image.mpr ⟨(j, k),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hj₁, hj₂⟩, Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩⟩, rfl⟩

theorem mem_lefts {v : ℂ} :
    v ∈ lefts o hm jlo klo khi ctr ↔
      ∃ k : ℤ, klo ≤ k ∧ k ≤ khi ∧ v = (⟨o + jlo * hm, (ctr (jlo, k)).im⟩ : ℂ) := by
  unfold lefts
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    exact ⟨k, hk₁, hk₂, rfl⟩
  · rintro ⟨k, hk₁, hk₂, rfl⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩, rfl⟩

theorem mem_B₀ {v : ℂ} :
    v ∈ B₀ o hm jlo jhi klo khi ctr ↔
      v ∈ corners o hm jlo jhi klo khi ∨ v ∈ rights o hm jlo jhi klo khi ctr ∨
        v ∈ lefts o hm jlo klo khi ctr := by
  unfold B₀
  simp only [Finset.mem_union, or_assoc]

theorem corner_mem_B₀ (j k : ℤ) (hj₁ : jlo ≤ j) (hj₂ : j ≤ jhi + 1) (hk₁ : klo ≤ k) (hk₂ : k ≤ khi + 1)
    {a b : ℝ} (ha : a = o + j * hm) (hb : b = o + k * hm) :
    (⟨a, b⟩ : ℂ) ∈ B₀ o hm jlo jhi klo khi ctr := by
  subst ha
  subst hb
  refine mem_B₀.mpr (Or.inl ?_)
  exact mem_corners.mpr ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩

theorem right_mem_B₀ (j k : ℤ) (hj₁ : jlo ≤ j) (hj₂ : j ≤ jhi) (hk₁ : klo ≤ k) (hk₂ : k ≤ khi) :
    (⟨o + (j + 1) * hm, (ctr (j, k)).im⟩ : ℂ) ∈ B₀ o hm jlo jhi klo khi ctr := by
  refine mem_B₀.mpr (Or.inr (Or.inl ?_))
  exact mem_rights.mpr ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩

theorem right_mem_B₀_of_eq (j k : ℤ) (hj₁ : jlo ≤ j) (hj₂ : j ≤ jhi) (hk₁ : klo ≤ k) (hk₂ : k ≤ khi)
    {a : ℝ} (ha : a = o + (j + 1) * hm) : (⟨a, (ctr (j, k)).im⟩ : ℂ) ∈ B₀ o hm jlo jhi klo khi ctr := by
  subst ha
  exact right_mem_B₀ j k hj₁ hj₂ hk₁ hk₂

theorem left_mem_B₀ (k : ℤ) (hk₁ : klo ≤ k) (hk₂ : k ≤ khi) :
    (⟨o + jlo * hm, (ctr (jlo, k)).im⟩ : ℂ) ∈ B₀ o hm jlo jhi klo khi ctr := by
  refine mem_B₀.mpr (Or.inr (Or.inr ?_))
  exact mem_lefts.mpr ⟨k, hk₁, hk₂, rfl⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.GridVertices
