module

/- Apache-2.0 source adapted for the frozen Dubon toolchain.
Source: https://raw.githubusercontent.com/CBirkbeck/aintlib/1e63feb21e2dd9e54908d14c9c07058eff3ff1d4/projects/Chebotarev/CebotarevDensity/Main.lean
Original license retained in Dependencies/AintlibChebotarevReuse/LICENSE.
DUB-17 dependency: prescribed Frobenius primes for arithmetic patching,
then automorphy lifting and higher symmetric-power continuation.
Adapted closure kernel-checked at the frozen pin; no arithmetic Taylor-Wiles system is asserted. -/

public import Dubon2026.Reuse.Chebotarev.Abelian
public import Dubon2026.Reuse.Chebotarev.FixedFieldDensity
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.RingTheory.Ideal.Over

/-!
# Chebotarev's density theorem

For a finite Galois extension `L/K` of number fields with Galois group
`G = Gal(L/K)` and a conjugacy class `C` of `G`, the Dirichlet density of
primes `𝔭` of `𝓞 K` (unramified in `L`) whose Frobenius conjugacy class is
`C` equals `|C| / |G|`.

The proof (Sharifi 7.2.2 Step 1; Stevenhagen–Lenstra Appendix paragraph 2)
reduces the conjugacy-class statement to the cyclic case via the
intermediate field `E = L^⟨σ⟩` for `σ ∈ C`:

- `L/E` is cyclic of degree `f = |⟨σ⟩|`, hence abelian, so the abelian case
  (`chebotarev_abelian`) gives density `1/f` for primes of `E` with
  Frobenius `σ`.
- A counting argument over the primes of `L` lying above a prime of `K`
  shows that, for the set `S` of primes `𝔭` of `K` whose Frobenius class is
  `C`, and `T_σ` the set of primes `P` of `E` with `σ_P = σ`,

      δ_K(S) = (f · |C| / |G|) · δ_E(T_σ).

  With `δ_E(T_σ) = 1/f` from the cyclic case, this gives `δ_K(S) = |C|/|G|`.

## Main results

* `Chebotarev.chebotarev_density` — Chebotarev's density
  theorem in conjugacy-class form.
* `Chebotarev.infinite_setOf_frobenius_class` gives the prime-existence
  input needed for arithmetic auxiliary-prime selection.

Only the density and infinitude endpoints are retained in this port. The
upstream arithmetic-progression corollary is not needed by this dependency chain.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (`docs/algnum.pdf`,
  pp. 142–144).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix
  (`docs/cheb.pdf`, p. 18).
-/

@[expose] public section

noncomputable section

open Filter NumberField Topology Set

open scoped ENNReal

namespace Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **Chebotarev's density theorem** (Sharifi 7.2.2; SL Appendix).

For a finite Galois extension `L/K` of number fields with Galois group `G`
and a conjugacy class `C ⊆ G`, the Dirichlet density of the set of primes
`𝔭` of `𝓞 K` (unramified in `L`) such that the Frobenius conjugacy class of
`𝔭` is `C` equals `|C| / |G|`. -/
theorem chebotarev_density
    [FiniteDimensional K L] (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := by
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  let e := IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)
  have : IsMulCommutative Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))) :=
    .of_comm fun a b ↦ by
      obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, rfl⟩ := e.surjective b
      rw [← map_mul e x y, ← map_mul e y x, mul_comm' x y]
  exact density_lift_through_fixedField σ
    (IntermediateField.fixedField (Subgroup.zpowers σ))
    (e ⟨σ, Subgroup.mem_zpowers σ⟩) rfl rfl
    (chebotarev_abelian _ L (e ⟨σ, Subgroup.mem_zpowers σ⟩))

/-- In a commutative finite monoid every conjugacy class is a singleton,
so `|C| = 1`. -/
theorem ConjClasses_carrier_card_eq_one_of_comm
    {G : Type*} [Monoid G] [IsMulCommutative G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier = 1 := by
  letI : CommMonoid G := IsMulCommutative.instCommMonoid
  have h : (ConjClasses.mk g).carrier = {g} := by
    ext a
    simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq]
  simp [h]

/-- **Chebotarev's density theorem, abelian case.** For an abelian Galois
extension `L/K`, the Dirichlet density of primes `𝔭` of `𝓞 K` unramified in
`L` whose Frobenius conjugacy class is `C` is `|C| / |Gal(L/K)|`. -/
theorem chebotarev_density_of_comm
    [FiniteDimensional K L] [IsMulCommutative Gal(L/K)] (C : ConjClasses Gal(L/K)) :
    HasDirichletDensity
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C}
      ((Nat.card C.carrier : ℝ) / Nat.card Gal(L/K)) := by
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C
  simpa [ConjClasses_carrier_card_eq_one_of_comm σ] using chebotarev_abelian K L σ

/-- A set of prime ideals with positive Dirichlet density is infinite. -/
theorem infinite_of_hasDirichletDensity_pos
    {S : Set (Ideal (𝓞 K))} {δ : ℝ} (h : HasDirichletDensity S δ) (hδ : 0 < δ) :
    S.Infinite :=
  fun hfin ↦ hδ.ne' (tendsto_nhds_unique h (hasDirichletDensity_of_finite K hfin))

/-- The carrier of a conjugacy class in a finite monoid has positive cardinality. -/
theorem ConjClasses_carrier_card_pos
    {G : Type*} [Monoid G] [Finite G] (C : ConjClasses G) :
    0 < Nat.card C.carrier := by
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C
  have : Nonempty (ConjClasses.mk a).carrier := ⟨⟨a, ConjClasses.mem_carrier_mk⟩⟩
  exact Nat.card_pos

/-- Existence of *infinitely many* primes with each Frobenius conjugacy class
— a qualitative corollary of `chebotarev_density`. -/
theorem infinite_setOf_frobenius_class
    (C : ConjClasses Gal(L/K)) :
    Set.Infinite
      {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ UnramifiedIn K L 𝔭 ∧
        frobeniusClass K L 𝔭 = C} := by
  refine infinite_of_hasDirichletDensity_pos (chebotarev_density C) ?_
  apply div_pos
  · exact_mod_cast ConjClasses_carrier_card_pos C
  · exact_mod_cast Nat.card_pos (α := Gal(L/K))

end Chebotarev
