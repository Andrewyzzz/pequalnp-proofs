import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2089_37
    (hOr : ∀ C : Circuit, (∀ g ∈ C.gates, g.op = GateOp.or) → ∀ a b : Nat,
    (∀ r ∈ ([8193, 16386] : List Nat), GateOp.and.eval
      [(C.wires (List.ofFn fun i : Fin 26 => r.testBit i.val)).getD a false,
       (C.wires (List.ofFn fun i : Fin 26 => r.testBit i.val)).getD b false] = true) →
    (∀ r ∈ ([67100672, 8191, 25018369] : List Nat), GateOp.and.eval
      [(C.wires (List.ofFn fun i : Fin 26 => r.testBit i.val)).getD a false,
       (C.wires (List.ofFn fun i : Fin 26 => r.testBit i.val)).getD b false] = false) → False)
    (hAnd : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∃ pre g post, x7.gates = pre ++ g :: post ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ q ∈ pre, q.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) → x7.size ≤ (62 : ℕ) → ∀ (x10 x11 : Fin ((26 : ℕ) + x7.size)), x10 ≠ x11 → (∀ (x13 x14 : Fin (13 : ℕ)), x2 x13 x14 → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x4 x13 x14), x6 x7 (↑x11) (x4 x13 x14)] = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), (∀ x15 ∉ x14, ∃ (x17 : Fin (13 : ℕ)), x3 x14 x17 ∧ x2 x15 x17) → ((∃ (x16 : Fin (13 : ℕ)), ∀ x17 ∈ x14, x2 x17 x16) ∨ ∃ (x16 : Fin (13 : ℕ)), ∀ (x17 : Fin (13 : ℕ)), x3 x14 x17 → x2 x16 x17) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x5 x14), x6 x7 (↑x11) (x5 x14)] = Bool.false) → False) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (62 : ℕ) → ∀ (x10 x11 : Fin ((26 : ℕ) + x7.size)), x10 ≠ x11 → (∀ (x13 x14 : Fin (13 : ℕ)), x2 x13 x14 → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x4 x13 x14), x6 x7 (↑x11) (x4 x13 x14)] = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), (∀ x15 ∉ x14, ∃ (x17 : Fin (13 : ℕ)), x3 x14 x17 ∧ x2 x15 x17) → ((∃ (x16 : Fin (13 : ℕ)), ∀ x17 ∈ x14, x2 x17 x16) ∨ ∃ (x16 : Fin (13 : ℕ)), ∀ (x17 : Fin (13 : ℕ)), x3 x14 x17 → x2 x16 x17) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x5 x14), x6 x7 (↑x11) (x5 x14)] = Bool.false) → False := by
  dsimp only at hAnd ⊢
  intro C hm hs a b hab hp hn
  by_cases hA : ∃ g ∈ C.gates, g.op = GateOp.and
  · have split (gs : List Gate) :
        (∀ g ∈ gs, g.op ≠ GateOp.and) ∨
        ∃ pre g post, gs = pre ++ g :: post ∧ g.op = GateOp.and ∧
          ∀ q ∈ pre, q.op ≠ GateOp.and := by
      induction gs with
      | nil => exact Or.inl (by simp)
      | cons g gs ih =>
        by_cases hg : g.op = GateOp.and
        · exact Or.inr ⟨[], g, gs, rfl, hg, by simp⟩
        rcases ih with hnone | ⟨pre, q, post, heq, hq, hpre⟩
        · apply Or.inl
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hg
          · exact hnone q hq
        · refine Or.inr ⟨g :: pre, q, post, by simp [heq], hq, ?_⟩
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hg
          · exact hpre r hr
    rcases split C.gates with hnone | hfirst
    · obtain ⟨g, hg, he⟩ := hA
      exact hnone g hg he
    · exact hAnd C hm hfirst hs a b hab hp hn
  · refine hOr C ?_ a.val b.val ?_ ?_
    · intro g hg
      have hop := (hm g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact hop.resolve_left (fun h => hA ⟨g, hg, h⟩)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have hrow : (fun i : Fin 26 => (8193 : Nat).testBit i.val) =
            (fun i => decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13))) := by decide
        simpa only [hrow] using hp 0 0 (by decide)
      · have hrow : (fun i : Fin 26 => (16386 : Nat).testBit i.val) =
            (fun i => decide (i = Fin.castAdd 13 (1 : Fin 13) ∨ i = Fin.natAdd 13 (1 : Fin 13))) := by decide
        simpa only [hrow] using hp 1 1 (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have hrow : (fun i : Fin 26 => (67100672 : Nat).testBit i.val) =
          (fun i : Fin 26 => decide ((∃ p ∈ (∅ : Finset (Fin 13)), i = Fin.castAdd 13 p) ∨
            ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ ∀ p ∈ (∅ : Finset (Fin 13)),
              ¬∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d)) := by decide
        simpa only [hrow] using hn (∅ : Finset (Fin 13)) (by decide) (by decide)
      · have hrow : (fun i : Fin 26 => (8191 : Nat).testBit i.val) =
          (fun i : Fin 26 => decide ((∃ p ∈ (Finset.univ : Finset (Fin 13)), i = Fin.castAdd 13 p) ∨
            ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ ∀ p ∈ (Finset.univ : Finset (Fin 13)),
              ¬∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d)) := by decide
        simpa only [hrow] using hn (Finset.univ : Finset (Fin 13)) (by decide) (by decide)
      · have hrow : (fun i : Fin 26 => (25018369 : Nat).testBit i.val) =
          (fun i : Fin 26 => decide ((∃ p ∈ ({0} : Finset (Fin 13)), i = Fin.castAdd 13 p) ∨
            ∃ l : Fin 13, i = Fin.natAdd 13 l ∧ ∀ p ∈ ({0} : Finset (Fin 13)),
              ¬∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d)) := by decide
        simpa only [hrow] using hn ({0} : Finset (Fin 13)) (by decide) (by decide)
