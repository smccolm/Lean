import Mathlib

/-!
# Modularity and Langlands extensions: representative target signatures

The mathematical roadmap is `README.md`. This file records definitions and theorem signatures
statable against the pinned Mathlib APIs and is not exhaustive. The definitions retain repeated
Hodge numbers, compare projective images using
one embedded finite field and one conjugation, and impose the orthogonal determinant constraint
before a central quotient. Weight functions are numerical data; attachment to an automorphic
representation is a separate comparison in the README.
-/

namespace TauCetiRoadmap.ModularityAndLanglandsExtensions

open scoped BigOperators MatrixGroups

/-! ## Layer 0: realization comparisons and the singular-weight Hodge prediction -/

namespace LanglandsRegister

/-- The four predicted Hodge numbers, as a list retaining repetitions. -/
def singularWeightHodgeList (k : ℕ) (r : ℤ) : List ℤ :=
  [0, r - 2, r + k - 1, k + 2 * r - 3]

/-- The prediction has four positions even when two values coincide. -/
theorem singularWeightHodgeList_length (k : ℕ) (r : ℤ) :
    (singularWeightHodgeList k r).length = 4 := sorry

/-- Nonnegativity of `k` makes the remaining pairwise difference `k + 1` nonzero. -/
theorem singularWeightHodgeList_nodup_iff (k : ℕ) (r : ℤ) :
    (singularWeightHodgeList k r).Nodup ↔
      r ≠ 2 ∧ (k : ℤ) + r ≠ 1 ∧ (k : ℤ) + 2 * r ≠ 3 := sorry

/-- At `r = 2` both pairs coincide. -/
theorem singularWeightHodgeList_r_two (k : ℕ) :
    singularWeightHodgeList k 2 = [0, 0, (k : ℤ) + 1, (k : ℤ) + 1] := sorry

example : singularWeightHodgeList 2 1 = [0, -1, 2, 1] ∧
    (singularWeightHodgeList 2 1).Nodup := by
  norm_num [singularWeightHodgeList]

example : singularWeightHodgeList 0 1 = [0, -1, 0, -1] ∧
    ¬ (singularWeightHodgeList 0 1).Nodup := by
  norm_num [singularWeightHodgeList]

example : singularWeightHodgeList 0 2 = [0, 0, 1, 1] ∧
    ¬ (singularWeightHodgeList 3 2).Nodup := by
  norm_num [singularWeightHodgeList]

/-- Use the existing polynomial API directly; the characteristic and Euler polynomials differ. -/
example : (Polynomial.X - 1 : Polynomial ℚ).reverse = 1 - Polynomial.X ∧
    (Polynomial.X - 1 : Polynomial ℚ).eval (1 / 2) ≠
      (1 - Polynomial.X : Polynomial ℚ).eval (1 / 2) := by
  constructor
  · have hx : (Polynomial.X : Polynomial ℚ).reverse = 1 := by
      simp [Polynomial.reverse]
    have hsub : (Polynomial.X - 1 : Polynomial ℚ) =
        Polynomial.X + Polynomial.C (-1) := by simp [sub_eq_add_neg]
    rw [hsub, Polynomial.reverse_add_C, hx]
    simp [sub_eq_add_neg]
  · norm_num

/-- The matrix API includes singular matrices and dimension zero. -/
example : Matrix.charpolyRev (0 : Matrix (Fin 0) (Fin 0) ℚ) = 1 ∧
    Matrix.charpolyRev (0 : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
  simp [Matrix.charpolyRev]

/-- In the basis `e², eē, ē²`, conjugation fixes the middle line of `Sym² H¹`. -/
example : Matrix.trace (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℤ) = 1 ∧
    Matrix.det (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℤ) = -1 := by
  norm_num [Matrix.trace, Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.cons_val']
  decide

end LanglandsRegister

/-! ## Layer 1: weight one, low-rank lifts and residual image conditions -/

namespace SymmetricPower

/-- The NT II finite-field image condition uses the same field and conjugation in both inclusions.
`n` is the rank of the symmetric power, whose degree is `n - 1`. -/
def ProjectiveImageSandwich {G k K : Type*} [Group G] [Field k] [Fintype k]
    [Field K] (p a n : ℕ) (ι : k →+* K)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) K) : Prop :=
  Nat.Prime p ∧ 1 ≤ a ∧ 1 ≤ n ∧ Fintype.card k = p ^ a ∧
  Fintype.card k > max 5 (2 * n - 1) ∧
  ∃ c : PGL(2, K),
    ((Matrix.ProjGenLinGroup.map ι).comp
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := k))).range ≤
        ((MulAut.conj c).toMonoidHom.comp (Matrix.ProjGenLinGroup.mk.comp ρ)).range ∧
    ((MulAut.conj c).toMonoidHom.comp (Matrix.ProjGenLinGroup.mk.comp ρ)).range ≤
      (Matrix.ProjGenLinGroup.map (n := Fin 2) ι).range

/-- The strict field-size bound excludes the exceptional small projective images. -/
theorem ProjectiveImageSandwich.bound {G k K : Type*} [Group G] [Field k]
    [Fintype k] [Field K] {p a n : ℕ} {ι : k →+* K}
    {ρ : G →* Matrix.GeneralLinearGroup (Fin 2) K}
    (h : ProjectiveImageSandwich p a n ι ρ) : p ^ a > max 5 (2 * n - 1) := sorry

/-- The same sandwich suffices at a smaller positive rank. -/
theorem ProjectiveImageSandwich.mono {G k K : Type*} [Group G] [Field k]
    [Fintype k] [Field K] {p a m n : ℕ} {ι : k →+* K}
    {ρ : G →* Matrix.GeneralLinearGroup (Fin 2) K}
    (h : ProjectiveImageSandwich p a n ι ρ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ProjectiveImageSandwich p a m ι ρ := sorry

/-- Change of basis preserves the projective image condition. -/
theorem ProjectiveImageSandwich.conjugation {G k K : Type*} [Group G] [Field k]
    [Fintype k] [Field K] {p a n : ℕ} {ι : k →+* K}
    {ρ : G →* Matrix.GeneralLinearGroup (Fin 2) K}
    (d : Matrix.GeneralLinearGroup (Fin 2) K) :
    ProjectiveImageSandwich p a n ι ((MulAut.conj d).toMonoidHom.comp ρ) ↔
      ProjectiveImageSandwich p a n ι ρ := sorry

section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The identity representation of `GL₂(𝔽₇)` meets the rank-three condition (README §1.7). -/
example : ProjectiveImageSandwich 7 1 3 (RingHom.id (ZMod 7))
    (MonoidHom.id (Matrix.GeneralLinearGroup (Fin 2) (ZMod 7))) := by
  refine ⟨by norm_num, le_rfl, by norm_num, by rw [ZMod.card]; norm_num,
    by rw [ZMod.card]; norm_num, 1, ?_, ?_⟩
  · rintro x -
    obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    exact ⟨g, by simp⟩
  · rintro x -
    exact ⟨x, by simp [Matrix.ProjGenLinGroup.map_id]⟩

/-- Over `𝔽₅` the strict bound `5 > max 5 3` fails for every representation (README §1.7). -/
example (ρ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 5) →*
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) :
    ¬ ProjectiveImageSandwich 5 1 2 (RingHom.id (ZMod 5)) ρ := by
  intro h
  have h1 := h.2.2.2.2.1
  rw [ZMod.card] at h1
  norm_num at h1

end

/-- A degree-zero finite-field parameter is excluded explicitly. -/
example {G k K : Type*} [Group G] [Field k] [Fintype k] [Field K]
    (p n : ℕ) (ι : k →+* K) (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) K) :
    ¬ ProjectiveImageSandwich p 0 n ι ρ := by
  intro h
  have := h.2.1
  omega

/-- Small characteristic is allowed by the bound; the prime need not exceed the rank. -/
example : (2 : ℕ) ^ 3 > max 5 (2 * 4 - 1) ∧ 2 ≤ 4 := by decide

end SymmetricPower

/-! ## Layer 2: controlled potential automorphy and compatible systems -/

/-! ## Layer 3: classical-group packets and symplectic descent -/

namespace Arthur

/-- The determinant-one condition on block signs, additively modulo two. -/
def orthogonalSignKernel {ι : Type*} [Fintype ι] (dim : ι → ℕ) :
    AddSubgroup (ι → ZMod 2) where
  carrier := {s | ∑ i, (dim i : ZMod 2) * s i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib] at *
    rw [ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [ha, neg_zero]

/-- Membership in the kernel is exactly the weighted parity equation. -/
theorem orthogonalSignKernel_mem_iff {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (s : ι → ZMod 2) :
    s ∈ orthogonalSignKernel dim ↔ ∑ i, (dim i : ZMod 2) * s i = 0 := sorry

/-- Even-dimensional blocks impose no determinant constraint. -/
theorem orthogonalSignKernel_even {ι : Type*} [Fintype ι]
    (dim : ι → ℕ) (h : ∀ i, Even (dim i)) : orthogonalSignKernel dim = ⊤ := sorry

/-- A single odd-dimensional block must have positive sign. -/
theorem orthogonalSignKernel_one_odd (d : ℕ) (h : Odd d) :
    orthogonalSignKernel (fun (_ : Fin 1) => d) = ⊥ := sorry

/-- One dimension-three block forces the trivial sign; the empty index set imposes nothing. -/
example : orthogonalSignKernel (fun (_ : Fin 1) => 3) = ⊥ ∧
    orthogonalSignKernel (fun (i : Fin 0) => i.elim0) = ⊤ := by
  have h3 : ((3 : ℕ) : ZMod 2) = 1 := by decide
  constructor
  · ext s
    simp only [orthogonalSignKernel, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, Fin.sum_univ_one, h3, one_mul,
      AddSubgroup.mem_bot]
    constructor
    · intro h
      funext i
      fin_cases i
      simpa using h
    · intro h
      simp [h]
  · ext s
    simp [orthogonalSignKernel]

/-- Two odd blocks: the signs must agree. -/
example (s : Fin 2 → ZMod 2) :
    s ∈ orthogonalSignKernel (fun (_ : Fin 2) => 1) ↔ s 0 = s 1 := by
  have key : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  simp [orthogonalSignKernel, Fin.sum_univ_two, key]

/-- An even block is free while the odd block must have positive sign. -/
example (s : Fin 2 → ZMod 2) :
    s ∈ orthogonalSignKernel ![1, 2] ↔ s 0 = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  simp [orthogonalSignKernel, Fin.sum_univ_two, h]

end Arthur

/-! ## Layer 4: symmetric powers, purity and equidistribution -/

namespace SymmetricPower

/-- A GL₂ weight function is parallel when the difference of its entries is independent of the
embedding. Attachment of this function to an automorphic representation is specified in README.md. -/
def IsParallelWeight {ι : Type*} (wt : ι → Fin 2 → ℤ) : Prop :=
  ∀ τ σ, wt τ 0 - wt τ 1 = wt σ 0 - wt σ 1

/-- The classical weight read from a numerical GL₂ weight at one embedding. -/
def parallelWeight {ι : Type*} (wt : ι → Fin 2 → ℤ) (τ : ι) : ℤ :=
  wt τ 0 - wt τ 1 + 2

/-- Adding a scalar to both entries at each embedding preserves parallel weight. -/
theorem IsParallelWeight.twist {ι : Type*} (wt : ι → Fin 2 → ℤ) (a : ι → ℤ) :
    IsParallelWeight (fun τ i => wt τ i + a τ) ↔ IsParallelWeight wt := sorry

/-- For a parallel weight the classical value is independent of the embedding. -/
theorem parallelWeight_independent {ι : Type*} {wt : ι → Fin 2 → ℤ}
    (h : IsParallelWeight wt) (τ σ : ι) : parallelWeight wt τ = parallelWeight wt σ := sorry

example : IsParallelWeight (fun (_ : Fin 2) (_ : Fin 2) => (0 : ℤ)) ∧
    parallelWeight (fun (_ : Fin 2) (_ : Fin 2) => (0 : ℤ)) 0 = 2 := by
  simp [IsParallelWeight, parallelWeight]

example : ¬ IsParallelWeight (fun (τ : Fin 2) (i : Fin 2) =>
    if i = 0 then if τ = 0 then (0 : ℤ) else 2 else 0) ∧
    parallelWeight (fun (τ : Fin 2) (i : Fin 2) =>
      if i = 0 then if τ = 0 then (0 : ℤ) else 2 else 0) 1 = 4 := by
  simp only [IsParallelWeight, parallelWeight]
  decide

example : IsParallelWeight (fun (τ : Fin 2) (i : Fin 2) =>
    if i = 0 then if τ = 0 then (2 : ℤ) else 3 else if τ = 0 then 0 else 1) ∧
    parallelWeight (fun (τ : Fin 2) (i : Fin 2) =>
      if i = 0 then if τ = 0 then (2 : ℤ) else 3 else if τ = 0 then 0 else 1) 0 = 4 ∧
    parallelWeight (fun (τ : Fin 2) (i : Fin 2) =>
      if i = 0 then if τ = 0 then (2 : ℤ) else 3 else if τ = 0 then 0 else 1) 1 = 4 := by
  simp only [IsParallelWeight, parallelWeight]
  decide

end SymmetricPower

/-! ## Layer 5: generic transfers and Langlands conjectures -/

/-! ## Numerical convention witnesses -/

/-- The symmetric Heisenberg cocycle becomes the polarized law under `z = t + xy/2`
(README §3.1); doubling the cocycle already fails on the two coordinate vectors. -/
example (x y x' y' t t' : ℚ) :
    (t + t' + (x * y' - x' * y) / 2) + (x + x') * (y + y') / 2 =
      (t + x * y / 2) + (t' + x' * y' / 2) + x * y' ∧
    (1 / 2 + (1 + 0) * (0 + 1) / 2 : ℚ) = 1 ∧
    (1 + (1 + 0) * (0 + 1) / 2 : ℚ) ≠ 1 := by
  constructor
  · ring
  · norm_num

/-- Halving the oscillator eigenvalue gives the even/odd lowest metaplectic weights
(README §3.1); the unhalved odd value is different. -/
example : ((2 * 0 + 1) / 2 : ℚ) = 1 / 2 ∧
    ((2 * 1 + 1) / 2 : ℚ) = 3 / 2 ∧
    ((2 * 1 + 1) / 2 : ℚ) ≠ 2 * 1 + 1 := by norm_num

/-- Ramification scaling preserves the rational rank-two nilpotence index (README §2.10). -/
example :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) ^ 2 = 0 ∧
    (2 • !![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) ^ 2 = 0 ∧
    (2 • !![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) ≠ 0 := by
  norm_num [pow_two, Matrix.mul_fin_two, Matrix.smul_cons, Matrix.smul_empty,
    Matrix.cons_eq_zero_iff]
  decide

/-- Maximal N and Nφ=pφN do not encode the consecutive-Hodge-list premise: the weakly admissible
`diag(5,25)` example of README §2.11 has `t_N = t_H = 3` and a stable line with `t_H < t_N`. -/
example :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![5, 0; 0, 25] =
      5 • (!![5, 0; 0, 25] * !![0, 1; 0, 0]) ∧
    (1 + 2 : ℤ) = 0 + 3 ∧ (0 : ℤ) < 1 := by
  norm_num [Matrix.mul_fin_two, Matrix.smul_cons, Matrix.smul_empty]
  decide

/-- Residue cardinality q, rather than coefficient prime p, fixes the unramified scale (README
Conventions and §3.7). -/
example : (Real.sqrt 9) ^ 3 = 27 ∧ (Real.sqrt 5) ^ 3 ≠ 27 := by
  constructor
  · norm_num
  · have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hn := Real.sqrt_nonneg (5 : ℝ)
    nlinarith [sq_nonneg (Real.sqrt 5 - 3)]

/-- The archimedean angular character remembers the value at the negative real unit (README
Conventions). -/
example : ((-1 : ℂ) / ‖(-1 : ℂ)‖) ^ 1 = -1 ∧
    (-1 : ℂ) / star (-1 : ℂ) = 1 := by norm_num

/-- The cohomological symmetric square has weights 0,1,2 and determinant exponent -3 (README
Conventions). -/
example : (List.range 3).map (fun i => (i : ℤ)) = [0, 1, 2] ∧
    -(∑ i ∈ Finset.range 3, (i : ℤ)) = -3 := by decide

/-- Rank n means symmetric-power degree n-1; distinct Satake roots may collide in degree two
(README Conventions and §1.1). -/
example : (1 : ℕ) - 1 = 0 ∧ (3 : ℕ) - 1 = 2 ∧
    [((1 : ℤ) ^ 2), 1 * (-1), (-1) ^ 2] = [1, -1, 1] := by decide

/-- The boundary chamber and its integral lattice impose different constraints (README §3.29). -/
example : (((1 - 3 : ℤ) : ZMod 2) = (2 : ZMod 2)) ∧
    (((1 - 3 : ℤ) : ZMod 2) ≠ (1 : ZMod 2)) ∧
    ((1 + 1 : ℤ), (0 + 2 : ℤ)) = (2, 2) := by decide

/-- The Adams–Johnson weak good range includes a zero root pairing and excludes `-1` (README §3.20). -/
example : (0 : ℤ) ≤ 0 ∧ ¬ (0 : ℤ) ≤ -1 := by decide

/-- Nonpositive pole orders summing to `-1` are `(-1, 0)` or `(0, -1)`: boundary nonvanishing rules
out cancellation of a higher pole by a zero (README §3.3). -/
example (a b : ℤ) (ha : a ≤ 0) (hb : b ≤ 0) (hab : a + b = -1) :
    (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = -1) := by omega

/-- The ordinary idempotent selects the unit-root coordinate in this mod-three model (README §2.3). -/
example : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 2 =
    !![1, 0; 0, 0] ∧
    Matrix.mulVec (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 3)) ![0, 1] = 0 := by
  norm_num [pow_two, Matrix.mul_fin_two, Matrix.cons_mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.cons_eq_zero_iff]
  decide

/-- Deligne–Lusztig cuspidal-type signs distinguish the two split block sizes (README §4.4). -/
example : (-1 : ℤ) ^ (2 - 1) = -1 ∧ (-1 : ℤ) ^ (5 - 1) = 1 := by decide

/-- The normalized Jacquet factor and the spectrum twist are different powers (README §4.3). -/
example : (Real.sqrt ((9 : ℝ)⁻¹))⁻¹ = 3 ∧ (((9 : ℝ)⁻¹)⁻¹) = 9 := by
  norm_num

/-!
The README also specifies the automorphic realization, accessible refinements,
Artin/functorial/symmetric-power predicates, integral Hecke and Dwork objects, ordinary flags,
Conjecture B, twisted modular curves and exceptional-curve certificates; oscillator/theta and
metaplectic descent, Arthur parameters/packets, Adams–Johnson induction, unitary eigenvarieties
and trianguline deformation families; Bianchi Fourier/cohomology and Sato–Tate data; general
functoriality/reciprocity, Bun_G/lisse categories, Weil-cocycle stacks, singular support and the
canonical spectral-action adjunction. Their carriers and comparisons remain mathematical targets
there.
-/

end TauCetiRoadmap.ModularityAndLanglandsExtensions
