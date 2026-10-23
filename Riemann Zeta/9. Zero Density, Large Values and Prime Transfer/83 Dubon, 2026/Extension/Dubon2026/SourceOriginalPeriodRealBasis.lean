import Dubon2026.SourceOriginalTateHeckeWords

/-! DUB-17/18 -> original rank-two Tate Hecke comparison -> real
coordinates of the actual integral path lattice. The established
discreteness and full real span allow the native ZLattice basis theorem
to supply the real basis, with no new linear-independence assumption.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)

/-- A finite basis of the genuine original period lattice, with its proved rank. -/
def originalPeriodLatticeBasis {n : ℕ} (b : Module.Basis (Fin n) ℂ V) :
    Module.Basis (Fin (2 * n)) ℤ (pathPeriodLattice N (fun i => (b i).val)) := by
  obtain ⟨hf, hfin, hr⟩ := original_period_lattice_free_finite_rank N b
  letI := hf
  letI := hfin
  exact Module.finBasisOfFinrankEq ℤ _ hr

/-- The same integral lattice vectors form a basis of the actual real period space. -/
def originalPeriodRealBasis {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    Module.Basis ι ℝ (Fin n → ℂ) := by
  let L := pathPeriodLattice N (fun i => (b i).val)
  letI : DiscreteTopology L := original_discrete_period_lattice N b
  letI : IsZLattice ℝ L := ⟨span_real_pathPeriodLattice_eq_top N b⟩
  exact lb.ofZLatticeBasis ℝ L

theorem originalPeriodRealBasis_apply {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (i : ι) : originalPeriodRealBasis N b lb i = (lb i).val := by
  let L := pathPeriodLattice N (fun i => (b i).val)
  letI : DiscreteTopology L := original_discrete_period_lattice N b
  letI : IsZLattice ℝ L := ⟨span_real_pathPeriodLattice_eq_top N b⟩
  exact lb.ofZLatticeBasis_apply ℝ L i

theorem originalPeriodRealBasis_repr {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    {ι : Type*} (lb : Module.Basis ι ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (x : pathPeriodLattice N (fun i => (b i).val)) (i : ι) :
    (originalPeriodRealBasis N b lb).repr x.val i = (lb.repr x i : ℝ) := by
  let L := pathPeriodLattice N (fun i => (b i).val)
  letI : DiscreteTopology L := original_discrete_period_lattice N b
  letI : IsZLattice ℝ L := ⟨span_real_pathPeriodLattice_eq_top N b⟩
  exact lb.ofZLatticeBasis_repr_apply ℝ L x i

end
end Dubon2026.SourceFunctionField.OriginalChart
