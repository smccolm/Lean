import Dubon2026.SourceFiniteFunctionBasis

/-! The exact monomial filtration of the original finite-function representation.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the affine coefficient flag and its character quotients.
The flag calculations are adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean.txt
(Apache-2.0; retained LICENSE and NOTICE). The basis itself comes directly
from pinned native interpolation, replacing the external basis construction.
-/

namespace Dubon2026
noncomputable section
variable (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] in
/-- The exact finite binomial expansion of an affine prime-field function. -/
theorem sourceFiniteFunction_affine_pow (x y : F) (n : ℕ) :
    (fun u : ZMod p => (x * ZMod.castHom (dvd_refl p) F u + y) ^ n)
      = ∑ m ∈ Finset.range (n + 1), (x ^ m * y ^ (n - m) * (n.choose m : F)) • sourceFiniteFunctionMonomial F p m := by
  funext u
  rw [add_pow, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.smul_apply, sourceFiniteFunctionMonomial, smul_eq_mul, mul_pow]
  ring

/-- The actual subspace spanned by prime-field monomials of degrees at most k. -/
noncomputable def sourceFiniteFunctionFlag (k : ℕ) : Submodule F (ZMod p → F) :=
  Submodule.span F (sourceFiniteFunctionBasis F p '' {i : Fin p | i.val ≤ k})

/-- Flag membership is precisely the vanishing of all higher monomial coordinates. -/
theorem sourceFiniteFunctionFlag_mem_iff {k : ℕ} {f : ZMod p → F} :
    f ∈ sourceFiniteFunctionFlag F p k ↔ ∀ i : Fin p, (sourceFiniteFunctionBasis F p).repr f i ≠ 0 → i.val ≤ k := by
  rw [sourceFiniteFunctionFlag, Module.Basis.mem_span_image]
  constructor
  · intro h i hi
    exact h (Finsupp.mem_support_iff.mpr hi)
  · intro h i hi
    exact h i (Finsupp.mem_support_iff.mp hi)

/-- Every original basis vector below the degree cutoff lies in the actual flag. -/
theorem sourceFiniteFunctionBasis_mem_flag {k : ℕ} {i : Fin p} (hi : i.val ≤ k) : sourceFiniteFunctionBasis F p i ∈ sourceFiniteFunctionFlag F p k :=
  Submodule.subset_span ⟨i, hi, rfl⟩

/-- Every prime-field monomial below the cutoff lies in the actual flag. -/
theorem sourceFiniteFunctionMonomial_mem_flag {k m : ℕ} (hm : m ≤ k) (hmp : m < p) : sourceFiniteFunctionMonomial F p m ∈ sourceFiniteFunctionFlag F p k := by
  rw [← sourceFiniteFunctionBasis_apply F p ⟨m, hmp⟩]
  exact sourceFiniteFunctionBasis_mem_flag F p hm

/-- The actual finite-function flag is increasing. -/
theorem sourceFiniteFunctionFlag_mono {k k' : ℕ} (h : k ≤ k') : sourceFiniteFunctionFlag F p k ≤ sourceFiniteFunctionFlag F p k' :=
  Submodule.span_mono (Set.image_mono fun _ hi => le_trans hi h)

/-- The flag contains all original functions once the cutoff reaches p minus one. -/
theorem sourceFiniteFunctionFlag_eq_top {k : ℕ} (hk : p - 1 ≤ k) : sourceFiniteFunctionFlag F p k = ⊤ := by
  rw [sourceFiniteFunctionFlag, show {i : Fin p | i.val ≤ k} = Set.univ from
    Set.eq_univ_of_forall fun i => le_trans (Nat.le_sub_one_of_lt i.2) hk, Set.image_univ]
  exact (sourceFiniteFunctionBasis F p).span_eq

/-- A finite linear combination below the original degree cutoff belongs to the flag. -/
theorem sourceFiniteFunction_sum_mem_flag {k n : ℕ} (hn : n ≤ k) (hkp : k < p) (c : ℕ → F) :
    ∑ m ∈ Finset.range (n + 1), c m • sourceFiniteFunctionMonomial F p m ∈ sourceFiniteFunctionFlag F p k :=
  Submodule.sum_mem _ fun _ hm =>
    Submodule.smul_mem _ _ (sourceFiniteFunctionMonomial_mem_flag F p (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hn)
      (lt_of_le_of_lt (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hn) hkp))

/-- The actual monomial coordinate on the finite-function coefficient space. -/
noncomputable def sourceFiniteFunctionCoordinate (k : Fin p) : (ZMod p → F) →ₗ[F] F := (sourceFiniteFunctionBasis F p).coord k

/-- The coordinate is literally that of the proved interpolation basis. -/
theorem sourceFiniteFunctionCoordinate_apply (k : Fin p) (f : ZMod p → F) : sourceFiniteFunctionCoordinate F p k f = (sourceFiniteFunctionBasis F p).repr f k := rfl

/-- Coordinate extraction on actual prime-field monomials is the Kronecker delta. -/
theorem sourceFiniteFunctionCoordinate_monomial (k : Fin p) {m : ℕ} (hm : m < p) : sourceFiniteFunctionCoordinate F p k (sourceFiniteFunctionMonomial F p m) = if m = k.val then 1 else 0 := by
  rw [sourceFiniteFunctionCoordinate_apply, ← sourceFiniteFunctionBasis_apply F p ⟨m, hm⟩, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : m = k.val
  · rw [if_pos h, if_pos (Fin.ext h)]
  · rw [if_neg h, if_neg (fun h' => h (congrArg Fin.val h'))]

/-- All higher coordinates vanish on the original flag. -/
theorem sourceFiniteFunctionCoordinate_zero {j : ℕ} {k : Fin p} (hjk : j < k.val) {f : ZMod p → F} (hf : f ∈ sourceFiniteFunctionFlag F p j) :
    sourceFiniteFunctionCoordinate F p k f = 0 := by
  by_contra h
  exact absurd ((sourceFiniteFunctionFlag_mem_iff F p).mp hf k h) (not_le.mpr hjk)

/-- The leading coordinate of a bounded monomial sum is its exact last coefficient. -/
theorem sourceFiniteFunctionCoordinate_sum (k : Fin p) {n : ℕ} (hn : n ≤ k.val) (c : ℕ → F) :
    sourceFiniteFunctionCoordinate F p k (∑ m ∈ Finset.range (n + 1), c m • sourceFiniteFunctionMonomial F p m) = if n = k.val then c n else 0 := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hval : ∀ m ∈ Finset.range (n + 1), c m * sourceFiniteFunctionCoordinate F p k (sourceFiniteFunctionMonomial F p m) = if m = k.val then c m else 0 := by
    intro m hm
    have hmp : m < p := lt_of_le_of_lt (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hn) k.2
    rw [sourceFiniteFunctionCoordinate_monomial F p k hmp]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq']
  by_cases h : n = k.val
  · rw [if_pos h, if_pos (Finset.mem_range.mpr (by omega)), h]
  · rw [if_neg h, if_neg]
    intro hmem
    have := Finset.mem_range.mp hmem
    omega

end
end Dubon2026
