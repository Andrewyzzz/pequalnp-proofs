import Mathlib.Tactic
import PEqualNP.Defs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3291_37
    (hLow : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
 (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
 (∀ p r, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) → (∀ z : Fin (N+N) → Bool,
 Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 2 →
 (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
 PEqualNP.MetaComplexity.circuitFun (N+N) C z = false) → let E := Finset.univ.filter (fun e : Fin N × Fin N =>
 I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
 (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true);
 (((∀ p, (E.filter fun e => e.1 = p).card ≤ 131) ∧
   (∀ l, (E.filter fun e => e.2 = l).card ≤ 131)) ∨
   (∀ p, (E.filter fun e => e.1 = p).card ≤ 44) ∨
   (∀ l, (E.filter fun e => e.2 = l).card ≤ 44)) → E.card ≤ 44*C.size)
    (hHigh : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
 (C : PEqualNP.CircuitLowerBounds.Circuit), 131 ≤ q → N = q^2+q+1 →
 (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
 (∀ p r, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) → PEqualNP.TopForm.IsAO2 (N+N) C → (∀ z : Fin (N+N) → Bool,
 Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
 (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
 PEqualNP.MetaComplexity.circuitFun (N+N) C z = false) → let E := Finset.univ.filter (fun e : Fin N × Fin N =>
 I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
 (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true);
 (∃ p, 44 < (E.filter fun e => e.1 = p).card) →
 (∃ l, 44 < (E.filter fun e => e.2 = l).card) →
 ((∃ p, 131 < (E.filter fun e => e.1 = p).card) ∨
 (∃ l, 131 < (E.filter fun e => e.2 = l).card)) → E.card ≤ 44*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq hN hcol hu hAO hs
  let E := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
      (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true)
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hAO.1 g hg,
      by have h := hAO.2.2 g hg; omega⟩
  have hs2 : ∀ z : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 2 →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z = false := by
    intro z hz hn
    exact hs z (by omega) hn
  have hb : E.card ≤ 44*C.size := by
    by_cases hp44 : ∀ p, (E.filter fun e => e.1 = p).card ≤ 44
    · exact hLow N I C hm hu hs2 (Or.inr (Or.inl hp44))
    by_cases hl44 : ∀ l, (E.filter fun e => e.2 = l).card ≤ 44
    · exact hLow N I C hm hu hs2 (Or.inr (Or.inr hl44))
    obtain ⟨p44,hp44⟩ := not_forall.mp hp44
    obtain ⟨l44,hl44⟩ := not_forall.mp hl44
    have hp : ∃ p, 44 < (E.filter fun e => e.1 = p).card := ⟨p44,Nat.lt_of_not_ge hp44⟩
    have hl : ∃ l, 44 < (E.filter fun e => e.2 = l).card := ⟨l44,Nat.lt_of_not_ge hl44⟩
    by_cases hleft : ∀ p, (E.filter fun e => e.1 = p).card ≤ 131
    · by_cases hright : ∀ l, (E.filter fun e => e.2 = l).card ≤ 131
      · exact hLow N I C hm hu hs2 (Or.inl ⟨hleft,hright⟩)
      · obtain ⟨l,h⟩ := not_forall.mp hright
        exact hHigh q N I C hq hN hcol hu hAO hs hp hl (Or.inr ⟨l,Nat.lt_of_not_ge h⟩)
    · obtain ⟨p,h⟩ := not_forall.mp hleft
      exact hHigh q N I C hq hN hcol hu hAO hs hp hl (Or.inl ⟨p,Nat.lt_of_not_ge h⟩)
  simpa only [E, Fintype.card_subtype] using hb
