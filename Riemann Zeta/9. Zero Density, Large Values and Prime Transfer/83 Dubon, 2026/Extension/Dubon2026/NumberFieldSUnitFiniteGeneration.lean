import Dubon2026.SUnitValuationKernel
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Finite generation of the original number-field S-unit group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

/-- A homomorphism to a finitely generated commutative group with finitely generated actual kernel has finitely generated source. -/
theorem commGroup_fg_of_kernel {G H : Type*} [CommGroup G] [CommGroup H]
    [Group.FG H] (f : G →* H) [Group.FG f.ker] : Group.FG G := by
  let l := f.toAdditive.toIntLinearMap
  letI : Module.Finite ℤ (Additive H) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  letI : Module.Finite ℤ l.ker := by
    apply Module.Finite.iff_addGroup_fg.mpr
    change AddGroup.FG (Additive f.ker)
    infer_instance
  let q := l.rangeRestrict
  letI : Module.Finite ℤ q.ker := by
    change Module.Finite ℤ l.rangeRestrict.ker
    rw [LinearMap.ker_rangeRestrict]
    infer_instance
  have hsurj : Function.Surjective q := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  letI : Module.Finite ℤ (Additive G) :=
    Module.Finite.of_exact q.exact_subtype_ker_map hsurj
  letI : AddGroup.FG (Additive G) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  exact (GroupFG.iff_add_fg (G := G)).mpr inferInstance

/-- Finitely many original places and finite generation of ordinary units imply finite generation of the actual S-units. -/
theorem sUnit_fg_of_baseUnits {R K : Type*} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Group.FG Rˣ]
    (S : Set (HeightOneSpectrum R)) (hS : S.Finite) : Group.FG (S.unit K) := by
  letI : Fintype S := hS.fintype
  letI : Group.FG (sUnitValuations (K := K) S).ker :=
    Group.fg_of_surjective
      (f := (sUnitValuationKernelBaseEquiv (K := K) S).symm.toMonoidHom)
      (sUnitValuationKernelBaseEquiv (K := K) S).symm.surjective
  exact commGroup_fg_of_kernel (sUnitValuations (K := K) S)

/-- The actual S-units of every number field are finitely generated for every finite set of original finite places. -/
theorem numberField_sUnit_fg (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) : Group.FG (S.unit K) := by
  letI : Group.FG (𝓞 K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  exact sUnit_fg_of_baseUnits S hS

/-- For every positive exponent, the actual original number-field S-units have a finite quotient by powers. -/
theorem numberField_sUnit_powerQuotient_finite (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) (n : ℕ) (hn : n ≠ 0) :
    Finite (S.unit K ⧸ (powMonoidHom (α := S.unit K) n).range) := by
  letI := numberField_sUnit_fg K S hS
  exact CommGroup.finite_of_fg_torsion _
    (CommGroup.isTorsion_quotient_range_powMonoidHom (S.unit K) hn)

end
end Dubon2026
