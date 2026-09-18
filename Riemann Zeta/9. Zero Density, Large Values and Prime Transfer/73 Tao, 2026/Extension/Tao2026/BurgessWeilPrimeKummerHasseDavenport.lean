import Tao2026.BurgessWeilPrimeKummerTwoRootTrace
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The Gauss-sum core of the two-root Hasse--Davenport leaf

This file separates the elementary Jacobi-sum degeneracies from the genuine
finite-field lifting theorem.  Additive characters are lifted by the field
trace, and the remaining nondegenerate Jacobi identity is reduced to the
corresponding three Gauss-sum lifting identities.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Pull an additive character back along the trace of a finite field
extension. -/
def finiteFieldTraceLiftAddChar
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (ψ : AddChar K ℂ) : AddChar L ℂ :=
  ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom

@[simp]
theorem finiteFieldTraceLiftAddChar_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (ψ : AddChar K ℂ) (x : L) :
    finiteFieldTraceLiftAddChar K L ψ x = ψ (Algebra.trace K L x) :=
  rfl

/-- Trace pullback preserves primitivity over a finite separable extension. -/
theorem finiteFieldTraceLiftAddChar_isPrimitive
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive) :
    (finiteFieldTraceLiftAddChar K L ψ).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  intro hlift
  have hψone : ψ = 1 := by
    apply AddChar.compAddMonoidHom_injective_left
      (Algebra.trace K L).toAddMonoidHom (Algebra.trace_surjective K L)
    simpa [finiteFieldTraceLiftAddChar] using hlift
  have hψne : ψ ≠ 1 := by
    intro h
    subst ψ
    exact hψ one_ne_zero (by simp)
  exact hψne hψone

/-- Norm pullback of multiplicative characters is transitive in a finite
field tower. -/
theorem finiteFieldNormLiftMulChar_tower
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Finite L] [Finite M] (χ : MulChar K ℂ) :
    finiteFieldNormLiftMulChar K M χ =
      finiteFieldNormLiftMulChar L M (finiteFieldNormLiftMulChar K L χ) := by
  apply MulChar.ext
  intro x
  change χ (Algebra.norm K (x : M)) =
    χ (Algebra.norm K (Algebra.norm L (x : M)))
  rw [Algebra.norm_norm]

/-- Trace pullback of additive characters is transitive in a finite field
tower. -/
theorem finiteFieldTraceLiftAddChar_tower
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (ψ : AddChar K ℂ) :
    finiteFieldTraceLiftAddChar K M ψ =
      finiteFieldTraceLiftAddChar L M (finiteFieldTraceLiftAddChar K L ψ) := by
  ext x
  change ψ (Algebra.trace K M x) =
    ψ (Algebra.trace K L (Algebra.trace L M x))
  rw [Algebra.trace_trace]

/-- The Hasse--Davenport Gauss identity for one specified finite field
extension and one pair of characters. -/
def FiniteFieldGaussLiftRelation
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) : Prop :=
  gaussSum (finiteFieldNormLiftMulChar K L χ)
      (finiteFieldTraceLiftAddChar K L ψ) =
    (-1 : ℂ) ^ (Module.finrank K L - 1) *
      gaussSum χ ψ ^ Module.finrank K L

/-- The signs and powers in Hasse--Davenport multiply correctly through two
positive extension degrees. -/
private theorem hasseDavenport_tower_power
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (z : ℂ) :
    (-1 : ℂ) ^ (n - 1) *
        (((-1 : ℂ) ^ (m - 1) * z ^ m) ^ n) =
      (-1 : ℂ) ^ (m * n - 1) * z ^ (m * n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hprod : (m + 1) * (n + 1) = (n + m * (n + 1)) + 1 := by
    ring
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, mul_pow]
  rw [← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add]
  rw [hprod, Nat.add_sub_cancel]

/-- Gauss lifting relations compose in a finite field tower. -/
theorem FiniteFieldGaussLiftRelation.tower
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Fintype K] [Fintype L] [Fintype M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (hKL : FiniteFieldGaussLiftRelation K L χ ψ)
    (hLM : FiniteFieldGaussLiftRelation L M
      (finiteFieldNormLiftMulChar K L χ)
      (finiteFieldTraceLiftAddChar K L ψ)) :
    FiniteFieldGaussLiftRelation K M χ ψ := by
  unfold FiniteFieldGaussLiftRelation at hKL hLM ⊢
  rw [finiteFieldNormLiftMulChar_tower K L M χ,
    finiteFieldTraceLiftAddChar_tower K L M ψ, hLM, hKL]
  rw [← Module.finrank_mul_finrank K L M]
  exact hasseDavenport_tower_power
    (Module.finrank K L) (Module.finrank L M)
    Module.finrank_pos Module.finrank_pos (gaussSum χ ψ)

/-- Norm/trace-lifted Gauss sums are invariant under an algebra equivalence
of the extension fields. -/
theorem gaussSum_normTraceLift_eq_of_algEquiv
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Fintype K] [Fintype L] [Fintype M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    (e : L ≃ₐ[K] M) (χ : MulChar K ℂ) (ψ : AddChar K ℂ) :
    gaussSum (finiteFieldNormLiftMulChar K L χ)
        (finiteFieldTraceLiftAddChar K L ψ) =
      gaussSum (finiteFieldNormLiftMulChar K M χ)
        (finiteFieldTraceLiftAddChar K M ψ) := by
  unfold gaussSum
  calc
    (∑ x : L, finiteFieldNormLiftMulChar K L χ x *
        finiteFieldTraceLiftAddChar K L ψ x) =
        ∑ x : L, finiteFieldNormLiftMulChar K M χ (e x) *
          finiteFieldTraceLiftAddChar K M ψ (e x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [finiteFieldNormLiftMulChar_apply,
        finiteFieldNormLiftMulChar_apply,
        finiteFieldTraceLiftAddChar_apply,
        finiteFieldTraceLiftAddChar_apply]
      have hn := Algebra.norm_eq_of_algEquiv e x
      have ht := Algebra.trace_eq_of_algEquiv e x
      exact congrArg₂ (fun a b => χ a * ψ b) hn.symm ht.symm
    _ = ∑ x : M, finiteFieldNormLiftMulChar K M χ x *
        finiteFieldTraceLiftAddChar K M ψ x := by
      exact e.toEquiv.sum_comp (fun x : M =>
        finiteFieldNormLiftMulChar K M χ x *
          finiteFieldTraceLiftAddChar K M ψ x)

/-- A local Gauss lifting relation is unchanged when its extension field is
replaced by an algebra-equivalent one. -/
theorem finiteFieldGaussLiftRelation_iff_of_algEquiv
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Fintype K] [Fintype L] [Fintype M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    (e : L ≃ₐ[K] M) (χ : MulChar K ℂ) (ψ : AddChar K ℂ) :
    FiniteFieldGaussLiftRelation K L χ ψ ↔
      FiniteFieldGaussLiftRelation K M χ ψ := by
  unfold FiniteFieldGaussLiftRelation
  have hsum := gaussSum_normTraceLift_eq_of_algEquiv K L M e χ ψ
  have hrank := e.toLinearEquiv.finrank_eq
  rw [hsum, hrank]

/-- The local relation for any finite extension is equivalent to the relation
for Mathlib's chosen extension of the same degree. -/
theorem finiteFieldGaussLiftRelation_iff_extension
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    (p d : ℕ) [Fact p.Prime] [CharP K p] [NeZero d]
    [Algebra K L] [FiniteDimensional K L]
    (hd : Module.finrank K L = d)
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) : by
      let E := FiniteField.Extension K p d
      letI : Fintype E := Fintype.ofFinite E
      exact FiniteFieldGaussLiftRelation K L χ ψ ↔
        FiniteFieldGaussLiftRelation K E χ ψ := by
  let E := FiniteField.Extension K p d
  letI : Fintype E := Fintype.ofFinite E
  exact finiteFieldGaussLiftRelation_iff_of_algEquiv K L E
    (FiniteField.algEquivExtension K p d L hd) χ ψ

/-- Trace lifting commutes with scalar shifts of additive characters. -/
theorem finiteFieldTraceLiftAddChar_mulShift
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (ψ : AddChar K ℂ) (a : K) :
    finiteFieldTraceLiftAddChar K L (ψ.mulShift a) =
      (finiteFieldTraceLiftAddChar K L ψ).mulShift (algebraMap K L a) := by
  ext x
  change ψ (a * Algebra.trace K L x) =
    ψ (Algebra.trace K L (algebraMap K L a * x))
  rw [← Algebra.smul_def, LinearMap.map_smul, Algebra.smul_def]
  simp

/-- Norm lifting on a base scalar raises the original character value to the
extension degree. -/
theorem finiteFieldNormLiftMulChar_algebraMap
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Finite L] (χ : MulChar K ℂ) (a : K) :
    finiteFieldNormLiftMulChar K L χ (algebraMap K L a) =
      χ a ^ Module.finrank K L := by
  rw [finiteFieldNormLiftMulChar_apply, Algebra.norm_algebraMap, map_pow]

/-- Shifting the base additive character scales the lifted Gauss sum by the
degree-th power of the usual base-field factor. -/
theorem gaussSum_normTraceLift_mulShift
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) (a : K) (ha : a ≠ 0) :
    gaussSum (finiteFieldNormLiftMulChar K L χ)
        (finiteFieldTraceLiftAddChar K L (ψ.mulShift a)) =
      χ⁻¹ a ^ Module.finrank K L *
        gaussSum (finiteFieldNormLiftMulChar K L χ)
          (finiteFieldTraceLiftAddChar K L ψ) := by
  let u : Kˣ := Units.mk0 a ha
  let uL : Lˣ := Units.map (algebraMap K L) u
  rw [finiteFieldTraceLiftAddChar_mulShift]
  change gaussSum (finiteFieldNormLiftMulChar K L χ)
      ((finiteFieldTraceLiftAddChar K L ψ).mulShift (uL : L)) = _
  rw [gaussSum_mulShift_eq (finiteFieldNormLiftMulChar K L χ)
    (finiteFieldTraceLiftAddChar K L ψ) uL]
  congr 1
  simp only [MulChar.inv_apply_eq_inv]
  change Ring.inverse (finiteFieldNormLiftMulChar K L χ
    (algebraMap K L a)) = Ring.inverse (χ a) ^ Module.finrank K L
  rw [finiteFieldNormLiftMulChar_algebraMap]
  exact (Ring.inverse_pow (χ a) (Module.finrank K L)).symm

/-- A Gauss lifting relation for one primitive additive character transfers
to every nonzero scalar shift of that character. -/
theorem FiniteFieldGaussLiftRelation.mulShift
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L]
    [Algebra K L] [FiniteDimensional K L]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (h : FiniteFieldGaussLiftRelation K L χ ψ)
    (a : K) (ha : a ≠ 0) :
    FiniteFieldGaussLiftRelation K L χ (ψ.mulShift a) := by
  let u : Kˣ := Units.mk0 a ha
  have hbase : gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
    simpa [u] using gaussSum_mulShift_eq χ ψ u
  unfold FiniteFieldGaussLiftRelation at h ⊢
  rw [gaussSum_normTraceLift_mulShift K L χ ψ a ha]
  rw [hbase, h, mul_pow]
  ring

/-- Scalar shifts of any primitive complex additive character exhaust all
complex additive characters of a finite field. -/
theorem exists_eq_mulShift_of_isPrimitive
    (K : Type*) [Field K] [Fintype K]
    (ψ₀ ψ : AddChar K ℂ) (hψ₀ : ψ₀.IsPrimitive) :
    ∃ a : K, ψ = ψ₀.mulShift a := by
  have hbij : Function.Bijective ψ₀.mulShift :=
    (Fintype.bijective_iff_injective_and_card ψ₀.mulShift).2
      ⟨AddChar.to_mulShift_inj_of_isPrimitive hψ₀, by simp⟩
  obtain ⟨a, ha⟩ := hbij.surjective ψ
  exact ⟨a, ha.symm⟩

/-- A primitive additive character is a nonzero scalar shift of any fixed
primitive additive character. -/
theorem exists_ne_zero_eq_mulShift_of_isPrimitive
    (K : Type*) [Field K] [Fintype K]
    (ψ₀ ψ : AddChar K ℂ) (hψ₀ : ψ₀.IsPrimitive)
    (hψ : ψ.IsPrimitive) :
    ∃ a : K, a ≠ 0 ∧ ψ = ψ₀.mulShift a := by
  obtain ⟨a, ha⟩ := exists_eq_mulShift_of_isPrimitive K ψ₀ ψ hψ₀
  refine ⟨a, ?_, ha⟩
  intro ha0
  subst a
  have hψne : ψ ≠ 1 := by
    simpa using hψ (a := (1 : K)) one_ne_zero
  exact hψne (by simpa using ha)

/-- The genuine Gauss-sum lifting statement needed for Jacobi
Hasse--Davenport.  The additive character upstairs is pulled back along the
field trace. -/
def TaoPrimeFieldGaussHasseDavenport : Prop :=
  ∀ (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ), χ ≠ 1 →
    let E := FiniteField.Extension (ZMod p) p d
    letI : Fintype E := Fintype.ofFinite E
    let ψ := AddChar.FiniteField.primitiveChar_to_Complex (ZMod p)
    gaussSum (finiteFieldNormLiftMulChar (ZMod p) E χ)
        (finiteFieldTraceLiftAddChar (ZMod p) E ψ) =
      (-1 : ℂ) ^ (d - 1) * gaussSum χ ψ ^ d

/-- In extension degree one over any finite field, norm/trace lifting
preserves every Gauss sum.  This is proved by transporting the sum through
finite-field uniqueness, not assumed as part of Hasse--Davenport. -/
theorem gaussSum_normTraceLift_extension_one_finiteField
    (K : Type*) [Field K] [Fintype K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ) : by
      let E := FiniteField.Extension K p 1
      letI : Fintype E := Fintype.ofFinite E
      exact gaussSum (finiteFieldNormLiftMulChar K E χ)
        (finiteFieldTraceLiftAddChar K E ψ) = gaussSum χ ψ := by
  let E := FiniteField.Extension K p 1
  letI : Fintype E := Fintype.ofFinite E
  let e : E ≃ₐ[K] K :=
    (FiniteField.algEquivExtension K p 1 K (by simp)).symm
  unfold gaussSum
  calc
    (∑ x : E, finiteFieldNormLiftMulChar K E χ x *
        finiteFieldTraceLiftAddChar K E ψ x) =
        ∑ x : E, χ (e x) * ψ (e x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [finiteFieldNormLiftMulChar_apply,
        finiteFieldTraceLiftAddChar_apply]
      have hn := Algebra.norm_eq_of_algEquiv e x
      have ht := Algebra.trace_eq_of_algEquiv e x
      simpa using congrArg₂ (fun a b => χ a * ψ b) hn.symm ht.symm
    _ = ∑ x : K, χ x * ψ x := by
      exact e.toEquiv.sum_comp (fun x : K => χ x * ψ x)

/-- The prime-field specialization of the general degree-one identity. -/
theorem gaussSum_normTraceLift_extension_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (ψ : AddChar (ZMod p) ℂ) : by
      let E := FiniteField.Extension (ZMod p) p 1
      letI : Fintype E := Fintype.ofFinite E
      exact gaussSum (finiteFieldNormLiftMulChar (ZMod p) E χ)
        (finiteFieldTraceLiftAddChar (ZMod p) E ψ) = gaussSum χ ψ := by
  let E := FiniteField.Extension (ZMod p) p 1
  letI : Fintype E := Fintype.ofFinite E
  let e : E ≃ₐ[ZMod p] ZMod p :=
    FiniteField.algEquivOfCardEq p (K := E) (K' := ZMod p) (by
      rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension]
      simp [ZMod.card])
  unfold gaussSum
  calc
    (∑ x : E, finiteFieldNormLiftMulChar (ZMod p) E χ x *
        finiteFieldTraceLiftAddChar (ZMod p) E ψ x) =
        ∑ x : E, χ (e x) * ψ (e x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [finiteFieldNormLiftMulChar_apply,
        finiteFieldTraceLiftAddChar_apply]
      have hn := Algebra.norm_eq_of_algEquiv e x
      have ht := Algebra.trace_eq_of_algEquiv e x
      simpa using congrArg₂ (fun a b => χ a * ψ b) hn.symm ht.symm
    _ = ∑ x : ZMod p, χ x * ψ x := by
      exact e.toEquiv.sum_comp (fun x : ZMod p => χ x * ψ x)

/-- Universal Hasse--Davenport restricted to extensions of prime degree.  The
base field and the primitive additive character are allowed to vary, which is
exactly what is needed to iterate the theorem in extension towers. -/
def TaoFiniteFieldGaussHasseDavenportPrimeDegree : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Fintype K] [Fintype L]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra K L] [FiniteDimensional K L]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ),
    (Module.finrank K L).Prime → χ ≠ 1 → ψ.IsPrimitive →
    FiniteFieldGaussLiftRelation K L χ ψ

/-- The prime-degree source restricted to Mathlib's one canonical primitive
complex additive character on each finite base field. -/
def TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Fintype K] [Fintype L]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra K L] [FiniteDimensional K L]
    (χ : MulChar K ℂ), (Module.finrank K L).Prime → χ ≠ 1 →
    FiniteFieldGaussLiftRelation K L χ
      (AddChar.FiniteField.primitiveChar_to_Complex K)

/-- Universal Hasse--Davenport for arbitrary finite-field extensions and
primitive additive characters. -/
def TaoFiniteFieldGaussHasseDavenport : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Fintype K] [Fintype L]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra K L] [FiniteDimensional K L]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ), χ ≠ 1 → ψ.IsPrimitive →
    FiniteFieldGaussLiftRelation K L χ ψ

/-- Prime-degree universal lifting implies the relation for every canonical
positive-degree extension.  Composite degrees are split into a two-step
tower and handled recursively. -/
theorem TaoFiniteFieldGaussHasseDavenportPrimeDegree.canonical
    (hprime : TaoFiniteFieldGaussHasseDavenportPrimeDegree)
    (K : Type) [Field K] [Fintype K]
    (p d : ℕ) [Fact p.Prime] [CharP K p]
    (χ : MulChar K ℂ) (ψ : AddChar K ℂ)
    (hd : 0 < d) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    letI : NeZero d := ⟨hd.ne'⟩
    let E := FiniteField.Extension K p d
    letI : Fintype E := Fintype.ofFinite E
    FiniteFieldGaussLiftRelation K E χ ψ := by
  induction d using Nat.prime_composite_induction generalizing K with
  | zero => omega
  | one =>
      unfold FiniteFieldGaussLiftRelation
      simpa [FiniteField.finrank_extension] using
        gaussSum_normTraceLift_extension_one_finiteField K p χ ψ
  | prime q hq =>
      letI : NeZero q := ⟨hq.ne_zero⟩
      letI : Fintype (FiniteField.Extension K p q) := Fintype.ofFinite _
      apply hprime K (FiniteField.Extension K p q) p χ ψ
      · simpa [FiniteField.finrank_extension] using hq
      · exact hχ
      · exact hψ
  | composite a ha hA b hb hB =>
      letI : NeZero a := ⟨by omega⟩
      letI : NeZero b := ⟨by omega⟩
      let L := FiniteField.Extension K p a
      letI : Fintype L := Fintype.ofFinite L
      letI : CharP L p := charP_of_injective_algebraMap' K p
      let M := FiniteField.Extension L p b
      letI : Fintype M := Fintype.ofFinite M
      letI : Algebra K M :=
        ((algebraMap L M).comp (algebraMap K L)).toAlgebra
      letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
      have hKL : FiniteFieldGaussLiftRelation K L χ ψ :=
        hA K χ ψ (by omega) hχ hψ
      have hχL : finiteFieldNormLiftMulChar K L χ ≠ 1 :=
        finiteFieldNormLiftMulChar_ne_one K L hχ
      have hψL : (finiteFieldTraceLiftAddChar K L ψ).IsPrimitive :=
        finiteFieldTraceLiftAddChar_isPrimitive K L hψ
      have hLM : FiniteFieldGaussLiftRelation L M
          (finiteFieldNormLiftMulChar K L χ)
          (finiteFieldTraceLiftAddChar K L ψ) :=
        hB L (finiteFieldNormLiftMulChar K L χ)
          (finiteFieldTraceLiftAddChar K L ψ) (by omega) hχL hψL
      have hKM : FiniteFieldGaussLiftRelation K M χ ψ :=
        FiniteFieldGaussLiftRelation.tower K L M χ ψ hKL hLM
      have hrank : Module.finrank K M = a * b := by
        rw [← Module.finrank_mul_finrank K L M,
          FiniteField.finrank_extension, FiniteField.finrank_extension]
      exact (finiteFieldGaussLiftRelation_iff_extension K M p (a * b)
        hrank χ ψ).mp hKM

/-- The universal prime-degree theorem implies universal
Hasse--Davenport in every positive extension degree. -/
theorem TaoFiniteFieldGaussHasseDavenportPrimeDegree.toFull
    (hprime : TaoFiniteFieldGaussHasseDavenportPrimeDegree) :
    TaoFiniteFieldGaussHasseDavenport := by
  intro K L _ _ _ _ p _ _ _ _ χ ψ hχ hψ
  let d := Module.finrank K L
  have hd : 0 < d := Module.finrank_pos
  letI : NeZero d := ⟨hd.ne'⟩
  have hcanonical := hprime.canonical K p d χ ψ hd hχ hψ
  exact (finiteFieldGaussLiftRelation_iff_extension K L p d rfl χ ψ).mpr
    hcanonical

/-- Universal finite-field Hasse--Davenport is exactly its prime-degree
fragment; degree one and all composite degrees are formal consequences. -/
theorem taoFiniteFieldGaussHasseDavenport_iff_primeDegree :
    TaoFiniteFieldGaussHasseDavenport ↔
      TaoFiniteFieldGaussHasseDavenportPrimeDegree := by
  constructor
  · intro h K L _ _ _ _ p _ _ _ _ χ ψ _hprime hχ hψ
    exact h K L p χ ψ hχ hψ
  · exact TaoFiniteFieldGaussHasseDavenportPrimeDegree.toFull

/-- Scalar-shift invariance and finite Pontryagin duality reduce the universal
prime-degree theorem to one canonical primitive additive character per base
field. -/
theorem taoFiniteFieldGaussHasseDavenportPrimeDegree_iff_canonicalAddChar :
    TaoFiniteFieldGaussHasseDavenportPrimeDegree ↔
      TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar := by
  constructor
  · intro h K L _ _ _ _ p _ _ _ _ χ hprime hχ
    exact h K L p χ (AddChar.FiniteField.primitiveChar_to_Complex K)
      hprime hχ
      (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive K)
  · intro h K L _ _ _ _ p _ _ _ _ χ ψ hprime hχ hψ
    let ψ₀ := AddChar.FiniteField.primitiveChar_to_Complex K
    have hψ₀ : ψ₀.IsPrimitive :=
      AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive K
    obtain ⟨a, ha, hψeq⟩ :=
      exists_ne_zero_eq_mulShift_of_isPrimitive K ψ₀ ψ hψ₀ hψ
    rw [hψeq]
    exact (h K L p χ hprime hχ).mulShift K L χ ψ₀ a ha

/-- The canonical-character prime-degree residual already implies universal
Hasse--Davenport in every positive degree. -/
theorem TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar.toFull
    (h : TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar) :
    TaoFiniteFieldGaussHasseDavenport :=
  TaoFiniteFieldGaussHasseDavenportPrimeDegree.toFull
    (taoFiniteFieldGaussHasseDavenportPrimeDegree_iff_canonicalAddChar.mpr h)

/-- The universal theorem specializes to the exact prime-field proposition
used by the two-root Kummer argument. -/
theorem TaoFiniteFieldGaussHasseDavenport.toPrimeField
    (h : TaoFiniteFieldGaussHasseDavenport) :
    TaoPrimeFieldGaussHasseDavenport := by
  intro p d _ _ _ χ hχ
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex (ZMod p)
  have hψ : ψ.IsPrimitive :=
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod p)
  have hrel : FiniteFieldGaussLiftRelation (ZMod p) E χ ψ :=
    h (ZMod p) E p χ ψ hχ hψ
  unfold FiniteFieldGaussLiftRelation at hrel
  have hrank : Module.finrank (ZMod p) E = d := by
    refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card (ZMod p)) ?_
    change Nat.card (ZMod p) ^ Module.finrank (ZMod p) E =
      Nat.card (ZMod p) ^ d
    rw [← Module.natCard_eq_pow_finrank]
    exact FiniteField.natCard_extension (ZMod p) p d
  rw [hrank] at hrel
  simpa [E, ψ] using hrel

/-- The canonical-character prime-degree residual specializes all the way to
the prime-field Hasse--Davenport proposition used by the Kummer argument. -/
theorem TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar.toPrimeField
    (h : TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar) :
    TaoPrimeFieldGaussHasseDavenport :=
  h.toFull.toPrimeField

/-- The only unresolved degrees in Gauss Hasse--Davenport are at least two. -/
def TaoPrimeFieldGaussHasseDavenportDegreeAtLeastTwo : Prop :=
  ∀ (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ), 2 ≤ d → χ ≠ 1 →
    let E := FiniteField.Extension (ZMod p) p d
    letI : Fintype E := Fintype.ofFinite E
    let ψ := AddChar.FiniteField.primitiveChar_to_Complex (ZMod p)
    gaussSum (finiteFieldNormLiftMulChar (ZMod p) E χ)
        (finiteFieldTraceLiftAddChar (ZMod p) E ψ) =
      (-1 : ℂ) ^ (d - 1) * gaussSum χ ψ ^ d

/-- Degree one is unconditional, so the full Gauss lifting theorem is exactly
its restriction to extension degrees at least two. -/
theorem taoPrimeFieldGaussHasseDavenport_iff_degreeAtLeastTwo :
    TaoPrimeFieldGaussHasseDavenport ↔
      TaoPrimeFieldGaussHasseDavenportDegreeAtLeastTwo := by
  constructor
  · intro h p d _ _ _ χ _hd hχ
    exact h p d χ hχ
  · intro h p d _ _ _ χ hχ
    by_cases hd : 2 ≤ d
    · exact h p d χ hd hχ
    have hd1 : d = 1 := by
      have hd0 : d ≠ 0 := NeZero.ne d
      omega
    subst d
    simpa using gaussSum_normTraceLift_extension_one p χ
      (AddChar.FiniteField.primitiveChar_to_Complex (ZMod p))

/-- The sign identity governing both degenerate Jacobi branches. -/
private theorem neg_one_eq_hasseDavenport_sign (d : ℕ) [NeZero d] :
    (-1 : ℂ) = (-1 : ℂ) ^ (d - 1) * (-1 : ℂ) ^ d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  simp [pow_succ, ← pow_add]

/-- The Gauss-sum lifting theorem implies the literal Jacobi-sum
Hasse--Davenport theorem, including the trivial-second-character and
inverse-product degeneracies. -/
theorem TaoPrimeFieldGaussHasseDavenport.toJacobi
    (hGauss : TaoPrimeFieldGaussHasseDavenport) :
    TaoPrimeFieldJacobiHasseDavenport := by
  intro p d _ _ _ χ φ hχ
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let lift := finiteFieldNormLiftMulChar (ZMod p) E
  let χE := lift χ
  let φE := lift φ
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex (ZMod p)
  let ψE := finiteFieldTraceLiftAddChar (ZMod p) E ψ
  let s : ℂ := (-1 : ℂ) ^ (d - 1)
  dsimp only
  have hχE : χE ≠ 1 := by
    exact finiteFieldNormLiftMulChar_ne_one (ZMod p) E hχ
  by_cases hφ : φ = 1
  · subst φ
    change jacobiSum χE (lift 1) = s * jacobiSum χ 1 ^ d
    rw [map_one]
    rw [jacobiSum_comm, jacobiSum_one_nontrivial hχE]
    rw [jacobiSum_comm, jacobiSum_one_nontrivial hχ]
    exact neg_one_eq_hasseDavenport_sign d
  by_cases hprod : χ * φ = 1
  · have hφeq : φ = χ⁻¹ := by
      have h := congrArg (fun η : MulChar (ZMod p) ℂ => χ⁻¹ * η) hprod
      simpa [mul_assoc] using h
    subst φ
    change jacobiSum χE (lift χ⁻¹) =
      s * jacobiSum χ χ⁻¹ ^ d
    rw [map_inv, jacobiSum_nontrivial_inv hχE,
      jacobiSum_nontrivial_inv hχ]
    have hminus := finiteFieldNormLiftMulChar_algebraMap_extension
      p d χ (-1)
    have hminus' : χE (-1) = χ (-1) ^ d := by
      simpa [χE, lift] using hminus
    rw [hminus', neg_pow, ← mul_assoc,
      ← neg_one_eq_hasseDavenport_sign d]
    ring
  have hφE : φE ≠ 1 := by
    exact finiteFieldNormLiftMulChar_ne_one (ZMod p) E hφ
  have hprodE : χE * φE ≠ 1 := by
    change lift χ * lift φ ≠ 1
    rw [← map_mul]
    exact finiteFieldNormLiftMulChar_ne_one (ZMod p) E hprod
  have hψ : ψ.IsPrimitive := by
    exact AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod p)
  have hψE : ψE.IsPrimitive := by
    exact finiteFieldTraceLiftAddChar_isPrimitive (ZMod p) E hψ
  have hcardE : (Fintype.card E : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hgprodE : gaussSum (χE * φE) ψE ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcardE hprodE hψE
  have hGχ : gaussSum χE ψE = s * gaussSum χ ψ ^ d := by
    simpa [χE, lift, ψE, ψ, s] using hGauss p d χ hχ
  have hGφ : gaussSum φE ψE = s * gaussSum φ ψ ^ d := by
    simpa [φE, lift, ψE, ψ, s] using hGauss p d φ hφ
  have hGprod : gaussSum (χE * φE) ψE =
      s * gaussSum (χ * φ) ψ ^ d := by
    simpa [χE, φE, lift, ψE, ψ, s] using hGauss p d (χ * φ) hprod
  apply mul_left_cancel₀ hgprodE
  rw [jacobiSum_mul_nontrivial hprodE ψE]
  rw [hGχ, hGφ, hGprod]
  have hbase := jacobiSum_mul_nontrivial hprod ψ
  calc
    (s * gaussSum χ ψ ^ d) * (s * gaussSum φ ψ ^ d) =
        s ^ 2 * (gaussSum χ ψ * gaussSum φ ψ) ^ d := by
      rw [mul_pow]
      ring
    _ = s ^ 2 *
        (gaussSum (χ * φ) ψ * jacobiSum χ φ) ^ d := by
      rw [hbase]
    _ = (s * gaussSum (χ * φ) ψ ^ d) *
        (s * jacobiSum χ φ ^ d) := by
      rw [mul_pow]
      ring

/-- Gauss Hasse--Davenport therefore constructs the exact two-root
all-extension Frobenius system. -/
theorem TaoPrimeFieldGaussHasseDavenport.toTwoRoots
    (hGauss : TaoPrimeFieldGaussHasseDavenport) :
    TaoPrimeKummerIsotypicFrobeniusSystemTwoRoots :=
  hGauss.toJacobi.toTwoRoots

/-- Combining Gauss Hasse--Davenport with the genuinely geometric
three-or-more-root system gives the full Kummer Frobenius source theorem. -/
theorem TaoPrimeFieldGaussHasseDavenport.toFull
    (hGauss : TaoPrimeFieldGaussHasseDavenport)
    (hthree : TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  taoPrimeKummerIsotypicFrobeniusSystem_of_twoRoots_and_threeRootsOrMore
    hGauss.toTwoRoots hthree

/-- The canonical-character prime-degree residual implies the literal Jacobi
Hasse--Davenport theorem. -/
theorem TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar.toJacobi
    (h : TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar) :
    TaoPrimeFieldJacobiHasseDavenport :=
  h.toPrimeField.toJacobi

/-- The canonical-character prime-degree residual constructs the exact
two-root all-extension Frobenius system. -/
theorem TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar.toTwoRoots
    (h : TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar) :
    TaoPrimeKummerIsotypicFrobeniusSystemTwoRoots :=
  h.toPrimeField.toTwoRoots

/-- Combining the canonical-character prime-degree residual with the genuine
three-or-more-root geometry constructs the full Kummer source system. -/
theorem TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar.toKummerSystem
    (h : TaoFiniteFieldGaussHasseDavenportPrimeDegreeCanonicalAddChar)
    (hthree : TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  h.toPrimeField.toFull hthree

end

end Tao2026
