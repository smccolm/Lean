import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
namespace P2MW.S_ModularCurve_coeffMap_injective

open ModularCurve IntermediateField HahnSeries

theorem solution {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) : Function.Injective (ModularCurve.coeffMap f) :=
  fun x y hxy => by
  ext k
  exact hf (by simpa using congrArg (fun z => HahnSeries.coeff z k) hxy)
