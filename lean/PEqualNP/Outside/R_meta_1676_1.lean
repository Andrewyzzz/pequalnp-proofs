import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1676_1
    (hnormalize : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = 15 ∧ D.output ≤ 24 ∧ (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24) ∧ (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (C.wires (List.ofFn x)).getD 9 false) ∧ PEqualNP.MetaComplexity.circuitFun 9 D = PEqualNP.MetaComplexity.circuitFun 9 C)
    (hfinite : ¬ ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = 15 ∧ D.output ≤ 24 ∧ (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 24) ∧ (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) ∧ PEqualNP.MetaComplexity.circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hok hfirst hfun
  by_contra hs
  have hsize : C.size ≤ 15 := by omega
  obtain ⟨D, hd, hsD, ho, hb, hw, he⟩ := hnormalize C hok hsize
  apply hfinite
  refine ⟨D, hd, hsD, ho, hb, ?_, he.trans hfun⟩
  intro x
  rw [hw, hfirst]
