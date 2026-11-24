import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Defs

-- Branch counting adapts L-meta-614 / PR 6550.
-- The two single-read estimates are copied from checked L-meta-2970 and L-meta-2972.
-- New ingredients: port accounting, saturation ownership, single-read transfer, and the degree-132 count.

-- Branch counting adapted from the repository proof of L-meta-614.
namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted


-- Branch counting adapted from the repository proof of L-meta-614.
namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

theorem carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

theorem singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

theorem nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

theorem firstBranch_spec (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

theorem firstBranch_unique (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2,hc,hb⟩)

theorem no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted


-- Branch counting adapted from the repository proof of L-meta-614.
namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w, val C (point {v,w}) C.output = true ↔ G.Adj v w

theorem point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v,w}) C.output = true ↔ G.Adj v w := he v w

theorem point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]
  exact hn

theorem point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

theorem edge_at_output (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    n ≤ C.output ∧ C.output < n+C.gates.length := by
  have hp := (point_pair he v w).2 hvw
  constructor
  · by_contra! hl
    let i : Fin n := ⟨C.output,hl⟩
    have hv := point_single_quiet he i
    rw [show C.output = i.val from rfl,val_input] at hv
    simp [point] at hv
  · by_contra! hgt
    rw [val_beyond C _ hgt] at hp
    contradiction

theorem two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

theorem carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh
    contradiction
  rw [carries_iff hC,carries_iff hC]
  simp [h1,h0,hb]

theorem meeting_gate (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n}
    (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v,w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (point_pair he v w).2 hvw, point_single_quiet he v, point_single_quiet he w⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C (point {v,w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point,h] at hv
    · simp [point,h] at hw
  have hlt : j < n+C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht
    contradiction
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n+p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n+p) := ep ▸ hj.1
  have hs1 : val C (point {v,w}) (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n+p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n+p) (hm : i ∈ g.inputs) : LNext n C i (n+p) :=
    ⟨⟨hi,p,g,hg,rfl,hm⟩,hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i,hi,ht⟩ := hs1
    have hi' : i < n+p := by
      by_contra hh'
      simp [operand,hh'] at ht
    have ht' : val C (point {v,w}) i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v,w}) (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n+p) = false) :
      ∃ i ∈ g.inputs, operand C x (n+p) i = false := by
    by_contra! h
    have ht : val C x (n+p) = true := by
      rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
      intro i hi
      simpa using h i hi
    rw [hX] at ht
    contradiction
  obtain ⟨a,ha,hwa⟩ := hFalse _ hs3
  obtain ⟨b,hb,hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n+p := by
    by_contra hi
    have hX := hAll i h
    simp [operand,hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand,ite_eq_left ha'] at hwa
  rw [operand,ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,reads a ha' ha,reads b hb' hb,
    (carries_separate hC hva hwa).1,(carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1,(carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2⟩

theorem covers_edge (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (_ha₁ : a₀ ≠ w)
    (hb₀ : G.Adj w b₀) (_hb₁ : b₀ ≠ v) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs⟩ := meeting_gate hC he hvw
  have pathV : Trace n C (Carries C v) v.val (n+p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva,ha⟩
  have pathW : Trace n C (Carries C w) w.val (n+p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb,hb⟩
  have uniqueV : ∀ k j j', k < n+p → Carries C v k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n+p → Carries C w k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀,b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false :=
    point_pair_quiet he (hind.elim (fun e => e ▸ G.irrefl (v := a₀)) id)
  have hY : val C y C.output = true := by
    apply acts_mono hC (point_mono (s := {v,a₀}) (by simp [S])) C.output
    exact (he v a₀).2 ha₀

  have hZ : val C z C.output = true := by
    apply acts_mono hC (point_mono (s := {w,b₀}) (by simp [S])) C.output
    exact (he w b₀).2 hb₀

  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C y C.output from by rw [hzero,hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C z C.output from by rw [hzero,hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n+p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n+p) = true := by
    rw [hX] at hdiffV
    simpa using hdiffV.symm
  have hzj : val C z (n+p) = true := by
    rw [hX] at hdiffW
    simpa using hdiffW.symm
  have hAX : val C x a = val C z a := by
    by_contra h
    rcases influence pathW uniqueW (fun _ hi => (point_insert hi).symm) (live_before ha.1 ha.2) h with h' | h'
    · exact hwa h'.2
    · exact (Nat.not_le_of_gt ha.1.1) h'.1
  have hBX : val C x b = val C y b := by
    by_contra h
    rcases influence pathV uniqueV (fun _ hi => (point_insert hi).symm) (live_before hb.1 hb.2) h with h' | h'
    · exact hvb h'.2
    · exact (Nat.not_le_of_gt hb.1.1) h'.1
  have hYall : ∀ i ∈ g.inputs, operand C y (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n+p) → i ∈ g.inputs := by
    rintro ⟨⟨_,k,g',he',hk,hmem⟩,_⟩
    have e : k=p := by omega
    subst k
    rw [hg] at he'
    cases he'
    exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand,ite_eq_left ha.1.1,← hAX] at hxA
  rw [operand,ite_eq_left hb.1.1,← hBX] at hxB
  have hs' : val C x (n+p) = true := by
    rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply,operand,ha.1.1] using hxA
    · simpa [Function.comp_apply,operand,hb.1.1] using hxB
  rw [hX] at hs'
  contradiction

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted


-- Branch counting adapted from the repository proof of L-meta-614.
namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

theorem value_at_branch {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

theorem branch_injective (hC : Monotone2 C) (he : GraphEval C G)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    {v w : Fin n} (hv : Eligible C v) (hw : Eligible C w)
    (hdv : 2 ≤ (G.neighborSet v).ncard) (hdw : 2 ≤ (G.neighborSet w).ncard)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins v w hne hadj hdv hdw
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

theorem input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (point_pair he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

theorem readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

theorem branch_budget (hC : Monotone2 C) (he : GraphEval C G)
    (active : Finset (Fin n)) (hdegree : ∀ v ∈ active, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in active.card + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : active.image Fin.val ⊆ W \ S := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,hu⟩ := hdegree v hv
    exact Finset.mem_sdiff.mpr ⟨mem_living.2 ⟨by have := v.isLt; omega,input_live he hu⟩,
      fun h => (Finset.mem_filter.mp h).2 v.isLt⟩
  have hW : active.card + S.card ≤ W.card := by
    have h := Finset.card_le_card hSub
    rw [Finset.card_image_of_injective _ Fin.val_injective] at h
    have part := Finset.card_sdiff_add_card_eq_card (show S ⊆ W from Finset.filter_subset _ _)
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change active.card+B.card ≤ C.gates.length+1
  omega



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem coverBudget {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : Monotone2 C) (hE : GraphEval C G)
    (active : Finset (Fin n)) (hdegree : ∀ v ∈ active, ∃ u, G.Adj v u)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ u, ¬ (G.Adj v u ↔ G.Adj w u))
    (hadj : ∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ a b, G.Adj v a ∧ a ≠ w ∧
      G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b)) :
    ∃ S : Finset (Fin n),
      (∀ u v, G.Adj u v → 2 ≤ (G.neighborSet u).ncard →
          2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) ∧ active.card + S.card ≤ C.size+1 := by
  classical
  by_cases h : ∃ v u, G.Adj v u
  swap
  · have empty : active = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro v hv
      obtain ⟨w,hw⟩ := hdegree v hv
      exact h ⟨v,w,hw⟩)
    exact ⟨∅, fun u v e => (h ⟨u,v,e⟩).elim, by simp [empty]⟩
  obtain ⟨v,u,edge⟩ := h
  have ho := (edge_at_output hE edge).2
  have ho' : C.output ∈ living n C := mem_living.2 ⟨ho, Relation.ReflTransGen.refl⟩
  let S : Finset (Fin n) := Finset.univ.filter fun v =>
    2 ≤ (G.neighborSet v).ncard ∧ Eligible C v
  have hS (u : Fin n) : u ∈ S ↔ 2 ≤ (G.neighborSet u).ncard ∧ Eligible C u := by
    simp [S]
  have covers : ∀ a b, G.Adj a b → 2 ≤ (G.neighborSet a).ncard → 2 ≤ (G.neighborSet b).ncard → a ∈ S ∨ b ∈ S := by
    intro a b hab hda hdb
    obtain ⟨u,v,hu,hu',hv,hv',hind⟩ := hadj a b hab hda hdb
    rcases covers_edge hC hE hab hu hu' hv hv' hind with ha | hb
    · exact Or.inl ((hS a).2 ⟨hda,ha⟩)
    · exact Or.inr ((hS b).2 ⟨hdb,hb⟩)
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have hcap : S.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      obtain ⟨_,hs⟩ := (hS u).1 hu
      have hb := firstBranch_spec u hs
      have hlt := (next_le hb.1).trans_lt ho
      show f u ∈ B
      rw [hf u hs]
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hlt,hb.1⟩,hb.2.2⟩
    · intro u hu v hv huv
      obtain ⟨hdu,hsu⟩ := (hS u).1 hu
      obtain ⟨hdv,hsv⟩ := (hS v).1 hv
      rw [hf u hsu,hf v hsv] at huv
      exact branch_injective hC hE htwins hsu hsv hdu hdv huv
  have budget := branch_budget hC hE active hdegree ho'
  exact ⟨S,covers,(Nat.add_le_add_left hcap _).trans budget⟩

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Graph construction adapted from R_meta_2866_42.
theorem incidenceCover : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ p r, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      (∀ z : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 2 →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N+N) C z = false) →

      let E := Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
          (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true)
      let A := E.image Prod.fst
      let B := E.image Prod.snd
      ∃ U V : Finset (Fin N), (∀ e ∈ E, (∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2) →
          (∃ g ∈ E, g.2 = e.2 ∧ g.1 ≠ e.1) → e.1 ∈ U ∨ e.2 ∈ V) ∧
        A.card+B.card+U.card+V.card ≤ C.size+1 := by
  classical
  let L {N : ℕ} : Fin N → Fin (N+N) := Fin.castAdd N
  let R {N : ℕ} : Fin N → Fin (N+N) := Fin.natAdd N
  have sides {N : ℕ} (p l : Fin N) : L p ≠ R l := by
    intro equal
    have val := congrArg Fin.val equal
    change p.val = N + l.val at val
    have inRange := p.isLt
    omega
  have leftInjective {N : ℕ} : Function.Injective (@L N) := by
    intro a b eq
    have valuations : (L a).val = (L b).val := congrArg Fin.val eq
    exact Fin.ext valuations
  have rightInjective {N : ℕ} : Function.Injective (@R N) := by
    intro a b eq
    have val := congrArg Fin.val eq
    change N + a.val = N + b.val at val
    exact Fin.ext (by omega)
  let graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) :=
    SimpleGraph.fromRel (fun x y => ∃ p l, x = L p ∧ y = R l ∧ I p l)
  have adjEither {N : ℕ} (I : Fin N → Fin N → Prop) (x y : Fin (N+N)) :
      (graph I).Adj x y ↔
        (∃ p l, x = L p ∧ y = R l ∧ I p l) ∨ (∃ p l, y = L p ∧ x = R l ∧ I p l) := by
    unfold graph
    rw [SimpleGraph.fromRel_adj]
    constructor
    · exact And.right
    · intro ok
      refine ⟨?_,ok⟩
      rintro rfl
      rcases ok with ⟨p,l,atP,atL,_⟩ | ⟨p,l,atP,atL,_⟩
      · exact sides p l (atP.symm.trans atL)
      · exact sides p l (atP.symm.trans atL)
  have leftNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) (y : Fin (N+N)) :
      (graph I).Adj (L p) y ↔ ∃ l, y = R l ∧ I p l := by
    rw [adjEither]
    constructor
    · rintro (⟨p',l,atP,atL,inc⟩ | ⟨p',l,_,invalid,_⟩)
      · exact ⟨l, atL, (leftInjective atP).symm ▸ inc⟩
      · exact (sides p l invalid).elim
    · rintro ⟨l,eq,inc⟩
      exact Or.inl ⟨p,l,rfl,eq,inc⟩
  have rightNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) (y : Fin (N+N)) :
      (graph I).Adj (R l) y ↔ ∃ p, y = L p ∧ I p l := by
    rw [adjEither]
    constructor
    · rintro (⟨p,l',invalid,_,_⟩ | ⟨p,l',atP,atL,inc⟩)
      · exact (sides p l invalid.symm).elim
      · exact ⟨p,atP,(rightInjective atL).symm ▸ inc⟩
    · rintro ⟨p,eq,inc⟩
      exact Or.inr ⟨p,l,eq,rfl,inc⟩
  have leftRight {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
      (graph I).Adj (L p) (R l) ↔ I p l := by
    rw [leftNeighbors]
    constructor
    · rintro ⟨k,eq,inc⟩
      exact (rightInjective eq).symm ▸ inc
    · exact fun inc => ⟨l,rfl,inc⟩
  have noFour {N : ℕ} (I : Fin N → Fin N → Prop)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (u v a b : Fin (N+N)) (vertices : u ≠ v) (neighbors : a ≠ b)
      (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
      (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
    have crosses (p l : Fin N) (otherP otherL : Fin (N+N))
        (differentP : L p ≠ otherP) (differentL : R l ≠ otherL)
        (pl : I p l) (pOther : (graph I).Adj (L p) otherL)
        (otherL' : (graph I).Adj otherP (R l)) (pair : (graph I).Adj otherP otherL) : False := by
      obtain ⟨k, rfl, pk⟩ := (leftNeighbors I p otherL).mp pOther
      obtain ⟨r, rfl, rl⟩ := (rightNeighbors I l otherP).mp ((graph I).adj_symm otherL')
      have rk := (leftRight I r k).mp pair
      have distinct : p ≠ r := fun eq => differentP (congrArg L eq)
      have same := (unique p r distinct).unique ⟨pl,rl⟩ ⟨pk,rk⟩
      exact differentL (congrArg R same)
    rcases (adjEither I u a).mp ua with ⟨p,l,rfl,rfl,pl⟩ | ⟨p,l,rfl,rfl,pl⟩
    · exact crosses p l v b vertices neighbors pl ub va vb
    · exact crosses p l b v neighbors vertices pl ((graph I).adj_symm va) ((graph I).adj_symm ub) ((graph I).adj_symm vb)
  intro N I inst C mono uniq sound
  let pair (u v i : Fin (N+N)) := decide (i = u ∨ i = v)
  let J (p l : Fin N) := I p l ∧ circuitFun (N+N) C (pair (L p) (R l)) = true
  let E := Finset.univ.filter (fun e : Fin N × Fin N => J e.1 e.2)
  let G := graph J
  have subAdj {u v} (h : G.Adj u v) : (graph I).Adj u v := by
    rcases (adjEither J u v).mp h with ⟨p,l,rfl,rfl,j⟩ | ⟨p,l,rfl,rfl,j⟩
    · exact (leftRight I p l).mpr j.1
    · exact (graph I).adj_symm ((leftRight I p l).mpr j.1)
  have hE : GraphEval C G := by
    intro u v
    let x := pair u v
    have fx : point {u,v} = x := by funext i; simp [point,x,pair]
    rw [fx]
    change circuitFun (N+N) C x = true ↔ G.Adj u v
    constructor
    · intro recognized
      have small : Fintype.card {l : Fin N // x (R l) = true} ≤ 2 := by
        let emb (l : {l : Fin N // x (R l) = true}) : ↥({u,v} : Finset (Fin (N+N))) :=
          ⟨R l.val, by simpa [x,pair] using l.property⟩
        apply (Fintype.card_le_of_injective emb (by
          intro a b eq; exact Subtype.ext (rightInjective (congrArg Subtype.val eq)))).trans
        simpa only [Fintype.card_coe, Finset.card_singleton] using
          Finset.card_insert_le (a := u) (s := ({v} : Finset (Fin (N+N))))
      have existsInc : ∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true := by
        by_contra missing
        rw [sound x small missing] at recognized
        contradiction
      obtain ⟨p,l,inc,onP,onL⟩ := existsInc
      rcases of_decide_eq_true onP with hp | hp <;> rcases of_decide_eq_true onL with hl | hl
      · exact (sides p l (hp.trans hl.symm)).elim
      · subst u; subst v
        exact (leftRight J p l).mpr ⟨inc, recognized⟩
      · subst v; subst u
        apply G.adj_symm
        apply (leftRight J p l).mpr
        refine ⟨inc,?_⟩
        convert recognized using 1 <;> simp [x,pair,Bool.or_comm]
      · exact (sides p l (hp.trans hl.symm)).elim
    · intro hit
      rcases (adjEither J u v).mp hit with ⟨p,l,rfl,rfl,j⟩ | ⟨p,l,rfl,rfl,j⟩
      · exact j.2
      · have eq : x = pair (L p) (R l) := by funext i; simp [x,pair,Bool.or_comm]
        rw [eq]; exact j.2
  have neighbors (v : Fin (N+N)) (h : 2 ≤ (G.neighborSet v).ncard) :
      ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
    have finite : (G.neighborSet v).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card _ finite] at h
    obtain ⟨a,b,ha,hb,ne⟩ := Finset.one_lt_card_iff.mp h
    exact ⟨a,b,ne,finite.mem_toFinset.mp ha,finite.mem_toFinset.mp hb⟩
  have noTwins (v w : Fin (N+N)) (diff : v ≠ w) (_ : ¬ G.Adj v w)
      (hv : 2 ≤ (G.neighborSet v).ncard) (_ : 2 ≤ (G.neighborSet w).ncard) :
      ∃ a, ¬(G.Adj v a ↔ G.Adj w a) := by
    by_contra! same
    obtain ⟨a,b,distinct,va,vb⟩ := neighbors v hv
    exact noFour I uniq v w a b diff distinct (subAdj va) (subAdj vb)
      (subAdj ((same a).mp va)) (subAdj ((same b).mp vb))
  have other (v w : Fin (N+N)) (h : 2 ≤ (G.neighborSet v).ncard) : ∃ a, G.Adj v a ∧ a ≠ w := by
    obtain ⟨a,b,diff,ha,hb⟩ := neighbors v h
    by_cases eq : a = w
    · exact ⟨b,hb,fun h => diff (eq.trans h.symm)⟩
    · exact ⟨a,ha,eq⟩
  have adjacent (v w : Fin (N+N)) (edge : G.Adj v w)
      (hv : 2 ≤ (G.neighborSet v).ncard) (hw : 2 ≤ (G.neighborSet w).ncard) :
      ∃ a b, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a=b ∨ ¬ G.Adj a b) := by
    obtain ⟨a,va,aw⟩ := other v w hv
    obtain ⟨b,wb,bv⟩ := other w v hw
    exact ⟨a,b,va,aw,wb,bv,Or.inr (fun ab => noFour I uniq w a v b aw.symm bv.symm
      (subAdj (G.adj_symm edge)) (subAdj wb) (subAdj (G.adj_symm va)) (subAdj ab))⟩
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  let active := A.image L ∪ B.image R
  have degree (v) (hv : v ∈ active) : ∃ u, G.Adj v u := by
    rcases Finset.mem_union.mp hv with ha | hb
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨_,(leftRight J _ _).mpr (Finset.mem_filter.mp he).2⟩
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨_,G.adj_symm ((leftRight J _ _).mpr (Finset.mem_filter.mp he).2)⟩
  obtain ⟨S,covered,budget⟩ := coverBudget mono hE active degree noTwins adjacent
  let U := Finset.univ.filter fun p : Fin N => L p ∈ S
  let V := Finset.univ.filter fun l : Fin N => R l ∈ S
  refine ⟨U,V,?_,?_⟩
  · intro e he hl hr
    change e.1 ∈ U ∨ e.2 ∈ V
    have two {v a b : Fin (N+N)} (ha : G.Adj v a) (hb : G.Adj v b) (ne : a ≠ b) :
        2 ≤ (G.neighborSet v).ncard := by
      have finite : (G.neighborSet v).Finite := Set.toFinite _
      rw [Set.ncard_eq_toFinset_card _ finite]
      exact Finset.one_lt_card_iff.mpr ⟨a,b,finite.mem_toFinset.mpr ha,finite.mem_toFinset.mpr hb,ne⟩
    obtain ⟨f,hf,fe,off⟩ := hl
    obtain ⟨g,hg,ge,off'⟩ := hr
    have ee := (leftRight J _ _).mpr ((Finset.mem_filter.mp he).2 : J e.1 e.2)
    have ff := (leftRight J _ _).mpr ((Finset.mem_filter.mp hf).2 : J f.1 f.2)
    have gg := (leftRight J _ _).mpr ((Finset.mem_filter.mp hg).2 : J g.1 g.2)
    rw [fe] at ff
    rw [ge] at gg
    exact (covered _ _ ee (two ff ee (fun h => off (rightInjective h)))
      (two (G.adj_symm gg) (G.adj_symm ee) (fun h => off' (leftInjective h)))).imp
      (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  · have disjoint (X Y : Finset (Fin N)) : Disjoint (X.image L) (Y.image R) := by
      rw [Finset.disjoint_left]
      intro v h k
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨l,_,eq⟩ := Finset.mem_image.mp k
      exact sides p l eq.symm
    have activeCount : active.card = A.card+B.card := by
      rw [Finset.card_union_of_disjoint (disjoint A B), Finset.card_image_of_injective _ leftInjective,
        Finset.card_image_of_injective _ rightInjective]
    have less : U.image L ∪ V.image R ⊆ S := by
      intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h; exact (Finset.mem_filter.mp hp).2
      · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h; exact (Finset.mem_filter.mp hl).2
    have hc := Finset.card_le_card less
    rw [Finset.card_union_of_disjoint (disjoint U V), Finset.card_image_of_injective _ leftInjective,
      Finset.card_image_of_injective _ rightInjective] at hc
    change A.card+B.card+U.card+V.card ≤ C.size+1
    omega

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted

theorem side {α β : Type} [DecidableEq α] [DecidableEq β]
    (E X : Finset β) (f : β → α) (U : Finset α) (hX : X ⊆ E)
    (deg : ∀ u, (E.filter fun e => f e = u).card ≤ 131)
    (extra : ∀ e ∈ X, f e ∈ U ∨ (E.filter fun j => f j = f e).card ≤ 1) :
    E.card + X.card ≤ 131 * ((E.image f).card + U.card) := by
  classical
  let A := E.image f
  have hE := Finset.card_eq_sum_card_fiberwise (s := E) (t := A)
    (f := f) (fun e he => Finset.mem_image_of_mem f he)
  have hY := Finset.card_eq_sum_card_fiberwise (s := X) (t := A)
    (f := f) (fun e he => Finset.mem_image_of_mem f (hX he))
  rw [hE,hY,← Finset.sum_add_distrib]
  have each (u : α) :
      (E.filter fun e => f e = u).card + (X.filter fun e => f e = u).card ≤
        131 + (if u ∈ U then 131 else 0) := by
    have sub := Finset.card_le_card (Finset.filter_subset_filter (fun e => f e = u) hX)
    have main := deg u
    by_cases hu : u ∈ U
    · simp [hu]; omega
    · simp only [hu, ite_false, Nat.add_zero]
      by_cases h : (X.filter fun e => f e = u).Nonempty
      · obtain ⟨e,he⟩ := h
        obtain ⟨hx,rfl⟩ := Finset.mem_filter.mp he
        have small := (extra e hx).resolve_left hu
        omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp h]
        simpa using main
  calc
    _ ≤ ∑ u ∈ A, (131 + (if u ∈ U then 131 else 0) : ℕ) :=
      Finset.sum_le_sum (fun u _ => each u)
    _ = 131 * A.card + 131 * (A.filter (· ∈ U)).card := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      simp [Nat.mul_comm]
    _ ≤ _ := by
      have h := Finset.card_le_card (show A.filter (· ∈ U) ⊆ U from
        fun _ h => (Finset.mem_filter.mp h).2)
      change _ ≤ 131 * (A.card + U.card)
      omega



theorem cover {N : ℕ} (E : Finset (Fin N × Fin N))
    (U V : Finset (Fin N))
    (left : ∀ u, (E.filter fun e => e.1 = u).card ≤ 131)
    (right : ∀ u, (E.filter fun e => e.2 = u).card ≤ 131)
    (cover : ∀ e ∈ E, (∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2) →
          (∃ g ∈ E, g.2 = e.2 ∧ g.1 ≠ e.1) → e.1 ∈ U ∨ e.2 ∈ V) :
    3 * E.card ≤ 131*((E.image Prod.fst).card + (E.image Prod.snd).card + U.card + V.card) := by
  classical
  let L (e : Fin N × Fin N) := e.1 ∈ U ∨ (E.filter fun f => f.1 = e.1).card ≤ 1
  let X := E.filter L
  let Y := E.filter fun e => ¬ L e
  have l := PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted.side E X Prod.fst U (Finset.filter_subset _ _) left
    (fun _ he => (Finset.mem_filter.mp he).2)
  have r := PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted.side E Y Prod.snd V (Finset.filter_subset _ _) right (by
    intro e he
    obtain ⟨mem,neg⟩ := Finset.mem_filter.mp he
    change ¬ (_ ∨ _) at neg
    by_cases hv : e.2 ∈ V
    · exact Or.inl hv
    right
    have more : ∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2 := by
      by_contra! no
      apply neg
      right
      apply Finset.card_le_one_iff.mpr
      intro a b ha hb
      obtain ⟨am,ae⟩ := Finset.mem_filter.mp ha
      obtain ⟨bm,be⟩ := Finset.mem_filter.mp hb
      exact Prod.ext (ae.trans be.symm) ((no a am ae).trans (no b bm be).symm)
    apply Finset.card_le_one_iff.mpr
    have uniq (g) (m : g ∈ E) (eq : g.2 = e.2) : g.1 = e.1 := by
      by_contra off
      exact (cover e mem more ⟨g,m,eq,off⟩).elim (fun u => neg (Or.inl u)) hv
    intro a b ha hb
    obtain ⟨am,ae⟩ := Finset.mem_filter.mp ha
    obtain ⟨bm,be⟩ := Finset.mem_filter.mp hb
    exact Prod.ext ((uniq a am ae).trans (uniq b bm be).symm) (ae.trans be.symm))
  have total : X.card + Y.card = E.card := Finset.card_filter_add_card_filter_not (s := E) L
  omega

theorem finish (e p l t s : Nat)
    (weight : 3*e ≤ 131*(p+l+t))
    (gateCount : p + l + t ≤ s + 1)
    (productBound : e ≤ p * l) : e ≤ 44 * s := by
  by_cases large : 131 ≤ s
  · omega
  · by_cases smallP : p ≤ 44
    · by_cases empty : p = 0
      · simp_all
      · have h := Nat.mul_le_mul_right l smallP
        omega
    · by_cases smallL : l ≤ 44
      · have h := Nat.mul_le_mul_left p smallL
        by_cases empty : l = 0
        · simp_all
        · omega
      · have aux : p*l + p*l ≤ p*p + l*l := by
          rcases Nat.le_total p l with hpl | hlp
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpl
            simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm k p]
            omega
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlp
            simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm k l]
            omega
        have sq := Nat.mul_le_mul_left (p+l) (show p+l ≤ 131 by omega)
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm l p] at sq
        omega


theorem bounded_degree (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (unique : ∀ p r, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (sound : ∀ z : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 2 →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z = false) :
    let E := Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true)
    (∀ p, (E.filter fun e => e.1 = p).card ≤ 131) →
    (∀ l, (E.filter fun e => e.2 = l).card ≤ 131) → E.card ≤ 44*C.size := by
  classical
  dsimp only
  let E := Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true)
  intro left right
  obtain ⟨U,V,covered,budget⟩ := incidenceCover N I C mono unique sound
  have weight := cover E U V left right covered
  have contain : E ⊆ (E.image Prod.fst) ×ˢ (E.image Prod.snd) := fun e he =>
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩
  apply finish E.card _ _ (U.card+V.card) C.size
  · simpa only [Nat.add_assoc] using weight
  · simpa only [Nat.add_assoc] using budget
  · simpa only [Finset.card_product] using Finset.card_le_card contain

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted

lemma fiber_bound {α β : Type} [DecidableEq α] [DecidableEq β]
    (E : Finset β) (f : β → α) (d : Nat)
    (hd : ∀ a, (E.filter fun e => f e = a).card ≤ d) :
    E.card ≤ d * (E.image f).card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := E) (t := E.image f)
    (f := f) (fun e he => Finset.mem_image_of_mem f he)
  rw [h]
  calc
    _ ≤ ∑ a ∈ E.image f, d := Finset.sum_le_sum (fun a _ => hd a)
    _ = _ := by simp [Nat.mul_comm]

lemma one_sided_budget {N : Nat} (E : Finset (Fin N × Fin N)) (d s : Nat)
    (hbudget : (E.image Prod.fst).card + (E.image Prod.snd).card ≤ s + 1)
    (hd : (∀ p, (E.filter fun e => e.1 = p).card ≤ d) ∨
      (∀ l, (E.filter fun e => e.2 = l).card ≤ d)) : E.card ≤ d*s := by
  by_cases hz : E = ∅
  · simp [hz]
  obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr hz
  have ha : 0 < (E.image Prod.fst).card := Finset.card_pos.mpr ⟨e.1,Finset.mem_image_of_mem _ he⟩
  have hb : 0 < (E.image Prod.snd).card := Finset.card_pos.mpr ⟨e.2,Finset.mem_image_of_mem _ he⟩
  rcases hd with hd | hd
  · exact (fiber_bound E Prod.fst d hd).trans (Nat.mul_le_mul_left d (by omega))
  · exact (fiber_bound E Prod.snd d hd).trans (Nat.mul_le_mul_left d (by omega))

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted


namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted

theorem weighted_side (d : Nat) (hd : 2 ≤ d) {α β : Type} [DecidableEq α] [DecidableEq β]
    (E X : Finset β) (f : β → α) (U : Finset α) (hX : X ⊆ E)
    (deg : ∀ u, (E.filter fun e => f e = u).card ≤ d)
    (extra : ∀ e ∈ X, f e ∈ U ∨ (E.filter fun j => f j = f e).card ≤ 1) :
    E.card + X.card ≤ d * ((E.image f).card + U.card) := by
  classical
  let A := E.image f
  have hE := Finset.card_eq_sum_card_fiberwise (s := E) (t := A)
    (f := f) (fun e he => Finset.mem_image_of_mem f he)
  have hY := Finset.card_eq_sum_card_fiberwise (s := X) (t := A)
    (f := f) (fun e he => Finset.mem_image_of_mem f (hX he))
  rw [hE,hY,← Finset.sum_add_distrib]
  have each (u : α) :
      (E.filter fun e => f e = u).card + (X.filter fun e => f e = u).card ≤
        d + (if u ∈ U then d else 0) := by
    have sub := Finset.card_le_card (Finset.filter_subset_filter (fun e => f e = u) hX)
    have main := deg u
    by_cases hu : u ∈ U
    · simp [hu]; omega
    · simp only [hu, ite_false, Nat.add_zero]
      by_cases h : (X.filter fun e => f e = u).Nonempty
      · obtain ⟨e,he⟩ := h
        obtain ⟨hx,rfl⟩ := Finset.mem_filter.mp he
        have small := (extra e hx).resolve_left hu
        omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp h]
        simpa using main
  calc
    _ ≤ ∑ u ∈ A, (d + (if u ∈ U then d else 0) : ℕ) :=
      Finset.sum_le_sum (fun u _ => each u)
    _ = d * A.card + d * (A.filter (· ∈ U)).card := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      simp [Nat.mul_comm]
    _ ≤ _ := by
      have h := Finset.card_le_card (show A.filter (· ∈ U) ⊆ U from
        fun _ h => (Finset.mem_filter.mp h).2)
      change _ ≤ d * (A.card + U.card)
      rw [Nat.mul_add]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left d h) _


theorem weighted_cover (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) {N : ℕ} (E : Finset (Fin N × Fin N))
    (U V : Finset (Fin N))
    (left : ∀ u, (E.filter fun e => e.1 = u).card ≤ a)
    (right : ∀ u, (E.filter fun e => e.2 = u).card ≤ b)
    (cover : ∀ e ∈ E, (∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2) →
          (∃ g ∈ E, g.2 = e.2 ∧ g.1 ≠ e.1) → e.1 ∈ U ∨ e.2 ∈ V) :
    (a+b+min a b) * E.card ≤ (a*b)*((E.image Prod.fst).card + (E.image Prod.snd).card + U.card + V.card) := by
  classical
  let L (e : Fin N × Fin N) := e.1 ∈ U ∨ (E.filter fun f => f.1 = e.1).card ≤ 1
  let X := E.filter L
  let Y := E.filter fun e => ¬ L e
  have l := PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted.weighted_side a ha E X Prod.fst U (Finset.filter_subset _ _) left
    (fun _ he => (Finset.mem_filter.mp he).2)
  have r := PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted.weighted_side b hb E Y Prod.snd V (Finset.filter_subset _ _) right (by
    intro e he
    obtain ⟨mem,neg⟩ := Finset.mem_filter.mp he
    change ¬ (_ ∨ _) at neg
    by_cases hv : e.2 ∈ V
    · exact Or.inl hv
    right
    have more : ∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2 := by
      by_contra! no
      apply neg
      right
      apply Finset.card_le_one_iff.mpr
      intro a b ha hb
      obtain ⟨am,ae⟩ := Finset.mem_filter.mp ha
      obtain ⟨bm,be⟩ := Finset.mem_filter.mp hb
      exact Prod.ext (ae.trans be.symm) ((no a am ae).trans (no b bm be).symm)
    apply Finset.card_le_one_iff.mpr
    have uniq (g) (m : g ∈ E) (eq : g.2 = e.2) : g.1 = e.1 := by
      by_contra off
      exact (cover e mem more ⟨g,m,eq,off⟩).elim (fun u => neg (Or.inl u)) hv
    intro a b ha hb
    obtain ⟨am,ae⟩ := Finset.mem_filter.mp ha
    obtain ⟨bm,be⟩ := Finset.mem_filter.mp hb
    exact Prod.ext ((uniq a am ae).trans (uniq b bm be).symm) (ae.trans be.symm))
  have total : X.card + Y.card = E.card := Finset.card_filter_add_card_filter_not (s := E) L
  have hl := Nat.mul_le_mul_left b l
  have hr := Nat.mul_le_mul_left a r
  have hx := Nat.mul_le_mul_right X.card (min_le_right a b)
  have hy := Nat.mul_le_mul_right Y.card (min_le_left a b)
  have heq := congrArg (fun k => min a b * k) total
  nlinarith

lemma small_budget (e p l s : Nat) (hs : s ≤ 174)
    (hbudget : p+l ≤ s+1) (hprod : e ≤ p*l) : e ≤ 44*s := by
  by_cases hp : p = 0
  · simp_all
  by_cases hl : l = 0
  · simp_all
  have hpos : 1 ≤ s := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpos
  have hk : k ≤ 173 := by omega
  have hk2 := Nat.mul_le_mul_left k hk
  have bal : p*l+p*l ≤ p*p+l*l := by
    rcases Nat.le_total p l with h | h
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le h
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm j p]
      omega
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le h
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm j l]
      omega
  have square := Nat.mul_le_mul hbudget hbudget
  have bound : 4*e ≤ 176*(1+k)+1 := by nlinarith
  omega

lemma weighted_finish (e p l t s a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hweight : (a+b+min a b)*e ≤ a*b*(p+l+t))
    (hbudget : p+l+t ≤ s+1) (hprod : e ≤ p*l)
    (hratio : 4*(a*b) ≤ 175*(a+b+min a b)) : e ≤ 44*s := by
  by_cases hs : s ≤ 174
  · exact small_budget e p l s hs (by omega) hprod
  let T := a+b+min a b
  let W := a*b
  have hT : 0 < T := by dsimp [T]; omega
  have weighted : T*e ≤ W*(s+1) :=
    hweight.trans (Nat.mul_le_mul_left (a*b) hbudget)
  have ratio : 4*W ≤ 175*T := hratio
  have hscaled := Nat.mul_le_mul_right (s+1) ratio
  have hlarge := Nat.mul_le_mul_left T (show 175 ≤ s by omega)
  have final : T*e ≤ T*(44*s) := by nlinarith
  by_contra hn
  have hbad := Nat.mul_le_mul_left T (show 44*s+1 ≤ e by omega)
  nlinarith

lemma weighted_degree_bound (N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hu : ∀ p r, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hs : ∀ z : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 2 →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z = false)
    (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hratio : 4*(a*b) ≤ 175*(a+b+min a b)) :
    let E := Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true)
    (∀ p, (E.filter fun e => e.1 = p).card ≤ a) →
    (∀ l, (E.filter fun e => e.2 = l).card ≤ b) → E.card ≤ 44*C.size := by
  classical
  dsimp only
  let E := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
      (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true)
  intro hl hr
  obtain ⟨U,V,hcover,hbudget⟩ := incidenceCover N I C hm hu hs
  have hweight := weighted_cover a b ha hb E U V hl hr hcover
  have contain : E ⊆ (E.image Prod.fst) ×ˢ (E.image Prod.snd) := fun e he =>
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩
  apply weighted_finish E.card _ _ (U.card+V.card) C.size a b ha hb
  · simpa only [Nat.add_assoc] using hweight
  · simpa only [Nat.add_assoc] using hbudget
  · simpa only [Finset.card_product] using Finset.card_le_card contain
  · exact hratio

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted


namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Parts
open PEqualNP.CircuitLowerBounds

def duplicate (C : Circuit) (n : Nat) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [C.output, C.output]⟩], n + C.size⟩

lemma run_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (xs : List α) :
    (gs.foldl (fun w g => w ++ [step w g]) xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_append,
      List.length_cons, List.length_nil]; omega

lemma duplicate_size (C : Circuit) (n : Nat) : (duplicate C n).size = C.size + 1 := by
  simp [duplicate, Circuit.size]

lemma duplicate_preserves_value (C : Circuit) (x : List Bool) :
    (duplicate C x.length).eval x = C.eval x := by
  have hl : (C.wires x).length = x.length + C.size := run_length _ _ _
  simp only [duplicate, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  change (C.wires x ++ [GateOp.and.eval
    [(C.wires x).getD C.output false, (C.wires x).getD C.output false]]).getD
      (x.length + C.size) false = (C.wires x).getD C.output false
  rw [← hl, List.getD_append_right _ _ _ _ (by omega)]
  simp [GateOp.eval]

-- This recursion is the linearParts definition in the public ReadK definitions.
noncomputable def linearParts (C : Circuit) (isLine : Nat → Bool) (x : List Bool) : List (Bool × Bool) :=
  C.gates.foldl
    (fun w g =>
      let ins := g.inputs.map fun i => w.getD i (false, false)
      w ++ [GateOp.rec (motive := fun _ => Bool × Bool)
        (ins.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false))
        (ins.any (·.1), ins.any (·.2)) (false, false) (fun _ => (false, false)) (false, false) g.op])
    ((x.zipIdx).map fun bi => if isLine bi.2 then (false, bi.1) else (bi.1, false))

lemma linearParts_length (C : Circuit) (marked : Nat → Bool) (x : List Bool) :
    (linearParts C marked x).length = x.length + C.size := by
  unfold linearParts Circuit.size
  rw [run_length]
  simp

lemma duplicate_linear_part_one (C : Circuit) (marked : Nat → Bool) (x : List Bool)
    (hz : ((linearParts C marked x).getD C.output (false,false)).1 = false) :
    ((linearParts (duplicate C x.length) marked x).getD (x.length+C.size) (false,false)).2 = false := by
  have hl := linearParts_length C marked x
  simp only [duplicate, linearParts, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change ((linearParts C marked x ++ [List.foldl
    (fun (acc : Bool × Bool) p => (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1)))
    (true,false) [(linearParts C marked x).getD C.output (false,false),
      (linearParts C marked x).getD C.output (false,false)]]).getD
    (x.length+C.size) (false,false)).2 = false
  rw [← hl, List.getD_append_right _ _ _ _ (by omega)]
  simp only [Nat.sub_self, List.getD_cons_zero, List.foldl_cons, List.foldl_nil,
    Bool.true_and, Bool.false_and, Bool.and_false, Bool.or_false, hz]

lemma duplicate_preserves_model (C : Circuit) (n : Nat)
    (hm : PEqualNP.TopForm.IsAO2 n C) (ho : C.output < n+C.size) :
    PEqualNP.TopForm.IsAO2 n (duplicate C n) := by
  rcases hm with ⟨hop, hback, htwo⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [duplicate, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hop g hg
    · exact Or.inl rfl
  · intro j hj i hi
    by_cases h : j < C.gates.length
    · have he : PEqualNP.MetaComplexity.NestedCover.gateAt (duplicate C n) j =
          PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt duplicate
        exact List.getD_append _ _ _ _ h
      rw [he] at hi
      exact hback j h i hi
    · have hj' : j = C.gates.length := by
        simp only [duplicate, List.length_append, List.length_singleton] at hj
        omega
      subst j
      simp [duplicate, PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
      subst i
      exact ho
  · intro g hg
    simp only [duplicate, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact htwo g hg
    · rfl


noncomputable def partStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false,false)
  GateOp.rec (motive := fun _ => Bool × Bool)
    (ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true,false))
    (ins.any (·.1), ins.any (·.2)) (false,false) (fun _ => (false,false)) (false,false) g.op

def masked (x : List Bool) (marked : Nat → Bool) : List Bool :=
  x.zipIdx.map fun bi => if marked bi.2 then false else bi.1

lemma and_zero (xs : List (Bool × Bool)) (acc : Bool × Bool) :
    (xs.foldl (fun (a : Bool × Bool) p =>
      (a.1 && p.1, (a.1 && p.2) || (a.2 && p.1))) acc).1 = (acc.1 && xs.all (·.1)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons, ih, List.all_cons, Bool.and_assoc]

lemma partStep_zero (w : List (Bool × Bool)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (partStep w g).1 = g.op.eval (g.inputs.map fun i => (w.map Prod.fst).getD i false) := by
  have hg (i : Nat) : (w.map Prod.fst).getD i false = (w.getD i (false,false)).1 :=
    List.getD_map w (false,false) Prod.fst
  rcases hop with h | h
  · simp only [partStep, h, and_zero, Bool.true_and, GateOp.eval, hg, List.all_map, Function.comp_def, id_eq]
  · simp only [partStep, h, GateOp.eval, hg, List.any_map, Function.comp_def, id_eq]

lemma run_zero (gs : List Gate) (w : List (Bool × Bool))
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    (gs.foldl (fun w g => w ++ [partStep w g]) w).map Prod.fst =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map Prod.fst) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun j hj => hop j (List.mem_cons_of_mem _ hj))]
    rw [List.map_append, List.map_singleton, partStep_zero w g (hop g (by simp))]

lemma linearParts_zero (C : Circuit) (marked : Nat → Bool) (x : List Bool)
    (hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ((linearParts C marked x).getD C.output (false,false)).1 = C.eval (masked x marked) := by
  have h : (linearParts C marked x).map Prod.fst = C.wires (masked x marked) := by
    unfold linearParts
    change (C.gates.foldl (fun w g => w ++ [partStep w g]) _).map Prod.fst = _
    rw [run_zero _ _ hop]
    unfold Circuit.wires masked
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro bi _
    cases h : marked bi.2 <;> simp [h]
  calc
    _ = ((linearParts C marked x).map Prod.fst).getD C.output false :=
      (List.getD_map _ (false,false) Prod.fst).symm
    _ = _ := by rw [h]; rfl

lemma masked_ofFn {n : Nat} (x : Fin n → Bool) (marked : Nat → Bool) :
    masked (List.ofFn x) marked = List.ofFn (fun i => if marked i.val then false else x i) := by
  apply List.ext_getElem
  · simp [masked]
  · intro i hi hj
    simp [masked]

lemma duplicate_linear_part_of_masked_false (C : Circuit) (marked : Nat → Bool) (x : List Bool)
    (hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hs : C.eval (masked x marked) = false) :
    ((linearParts (duplicate C x.length) marked x).getD (x.length+C.size) (false,false)).2 = false := by
  apply duplicate_linear_part_one
  exact (linearParts_zero C marked x hop).trans hs


def pairInput {N : Nat} (p l : Fin N) (i : Fin (N+N)) : Bool :=
  decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

lemma pair_mask_lines {N : Nat} (p l : Fin N) :
    masked (List.ofFn (pairInput p l)) (fun i => decide (N ≤ i)) =
      List.ofFn (Fin.addCases (fun k => decide (k = p)) (fun _ : Fin N => false)) := by
  rw [masked_ofFn]
  apply congrArg List.ofFn
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    have h : ¬ N ≤ (Fin.castAdd N k).val := by exact Nat.not_le_of_gt k.isLt
    have off : Fin.castAdd N k ≠ Fin.natAdd N l := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    simp only [h, decide_false, Bool.false_eq_true, ite_false, Fin.addCases_left,
      pairInput, off, or_false, Fin.castAdd_inj]
  · intro k
    have h : N ≤ (Fin.natAdd N k).val := by simp
    simp only [h, decide_true, ite_true, Fin.addCases_right]

lemma pair_mask_points {N : Nat} (p l : Fin N) :
    masked (List.ofFn (pairInput p l)) (fun i => decide (i < N)) =
      List.ofFn (Fin.addCases (fun _ : Fin N => false) (fun k => decide (k = l))) := by
  rw [masked_ofFn]
  apply congrArg List.ofFn
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    have h : (Fin.castAdd N k).val < N := k.isLt
    simp only [h, decide_true, ite_true, Fin.addCases_left]
  · intro k
    have h : ¬ (Fin.natAdd N k).val < N := by simp
    have off : Fin.natAdd N k ≠ Fin.castAdd N p := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    simp only [h, decide_false, Bool.false_eq_true, ite_false,
      Fin.addCases_right, pairInput, off, false_or, Fin.natAdd_inj]

lemma pair_masks_false {q N : Nat} (hq : 1 ≤ q) (I : Fin N → Fin N → Prop)
    (C : Circuit)
    (hs : ∀ z : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z = false)
    (p l : Fin N) :
    C.eval (masked (List.ofFn (pairInput p l)) (fun i => decide (N ≤ i))) = false ∧
    C.eval (masked (List.ofFn (pairInput p l)) (fun i => decide (i < N))) = false := by
  classical
  constructor
  · rw [pair_mask_lines]
    apply hs
    · simp only [Fin.addCases_right]; simp
    · simp only [Fin.addCases_left, Fin.addCases_right]; simp
  · rw [pair_mask_points]
    apply hs
    · simp only [Fin.addCases_right]; simpa using hq
    · simp only [Fin.addCases_left, Fin.addCases_right]; simp

lemma duplicate_pair_reread {q N : Nat} (hq : 1 ≤ q) (I : Fin N → Fin N → Prop)
    (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hs : ∀ z : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z = false)
    (p l : Fin N) :
    ((linearParts (duplicate C (N+N)) (fun i => decide (N ≤ i))
       (List.ofFn (pairInput p l))).getD (N+N+C.size) (false,false)).2 = false ∧
    ((linearParts (duplicate C (N+N)) (fun i => decide (i < N))
       (List.ofFn (pairInput p l))).getD (N+N+C.size) (false,false)).2 = false := by
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg; exact hm.1 g hg
  obtain ⟨hL,hP⟩ := pair_masks_false hq I C hs p l
  constructor
  · simpa only [List.length_ofFn] using
      duplicate_linear_part_of_masked_false C (fun i => decide (N ≤ i)) _ hop hL
  · simpa only [List.length_ofFn] using
      duplicate_linear_part_of_masked_false C (fun i => decide (i < N)) _ hop hP

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Parts


namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.ReadK
open PEqualNP.CircuitLowerBounds
def linearParts (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) : List (Bool × Bool) :=
  C.gates.foldl
    (fun w g =>
      let ins := g.inputs.map fun i => w.getD i (false, false)
      w ++ [match g.op with
        | GateOp.or  => (ins.any (·.1), ins.any (·.2))
        | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
              (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
        | _ => (false, false)])
    ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false))

/-- Edge (p, l) is LINE-SINGLE in `C`: the output's part 1 is true at the input with only
`p` and `l` true. -/
def lineSingle (C : Circuit) (n : ℕ) (isLine : ℕ → Bool) (p l : ℕ) : Bool :=
  ((linearParts C isLine ((List.range n).map fun i => i == p || i == l)).getD C.output
    (false, false)).2


end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.ReadK

-- Adapted verbatim from checked L-meta-2970; only namespace and copied ReadK definitions changed.

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.LineBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

def pairList (N : ℕ) (p l : Fin N) : List Bool :=
  (List.range (N + N)).map fun i => i == p.val || i == N + l.val

def lpInit (N : ℕ) (p l : Fin N) : List (Bool × Bool) :=
  ((pairList N p l).zipIdx).map fun (b, i) => if decide (N ≤ i) then (false, b) else (b, false)

def lpList (C : Circuit) (N : ℕ) (p l : Fin N) : List (Bool × Bool) :=
  linearParts C (fun k => decide (N ≤ k)) (pairList N p l)

def lpAt (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) : Bool × Bool :=
  (lpList C N p l).getD w (false, false)

lemma lineSingle_eq_lpAt (C : Circuit) (N : ℕ) (p l : Fin N) :
    lineSingle C (N + N) (fun k => decide (N ≤ k)) p.val (N + l.val) = (lpAt C N p l C.output).2 := rfl

lemma lpInit_length (N : ℕ) (p l : Fin N) : (lpInit N p l).length = N + N := by
  simp [lpInit, pairList]

lemma lpInit_getD (N : ℕ) (p l : Fin N) (i : ℕ) (hi : i < N + N) :
    (lpInit N p l).getD i (false, false) =
      if i < N then (decide (i = p.val), false) else (false, decide (i = N + l.val)) := by
  have hl1 : (pairList N p l).length = N + N := by simp [pairList]
  have hl2 : ((pairList N p l).zipIdx).length = N + N := by simp [hl1]
  rw [lpInit, List.getD_eq_getElem _ _ (by simp [hl2, hi]), List.getElem_map]
  have hz : ((pairList N p l).zipIdx)[i]'(by omega) = ((pairList N p l)[i]'(by omega), i) := by
    simp [List.getElem_zipIdx]
  rw [hz]
  dsimp only
  unfold pairList
  rw [List.getElem_map, List.getElem_range]
  by_cases hlt : i < N
  · have hni : ¬ (N ≤ i) := by omega
    have hne : (i == N + l.val) = false := by
      simp
      omega
    simp only [hlt, hni, hne, Bool.or_false, decide_false, ite_true]
    by_cases hep : i = p.val <;> simp [hep]
  · have hle : N ≤ i := by omega
    have hne : (i == p.val) = false := by
      simp
      omega
    simp only [hlt, hle, hne, Bool.false_or, decide_true, ite_true, ite_false]
    by_cases hel : i = N + l.val <;> simp [hel]

def pointInput (N : ℕ) (p : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i.val = p.val)

def zInput {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : Fin (N + N) → Bool :=
  fun i => if h : i.val < N then decide (¬ I ⟨i.val, h⟩ l) else decide (i.val = N + l.val)

def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma getD_map_fst (ws : List (Bool × Bool)) (i : ℕ) :
    (ws.map (·.1)).getD i false = (ws.getD i (false, false)).1 := by
  by_cases hi : i < ws.length
  · simp [hi]
  · have hle : ws.length ≤ i := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hle)]

lemma boolStep_fst_linStep (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (ws : List (Bool × Bool)) :
    (linStep ws g).1 = boolStep (ws.map (·.1)) g := by
  rcases hg with hop | hop
  · simp only [linStep, boolStep, hop, GateOp.eval]
    have hfold : ∀ (l : List (Bool × Bool)) (b c : Bool),
        (l.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (b, c)).1 =
        (b && l.all (·.1)) := by
      intro l
      induction l with
      | nil => intro b c; simp
      | cons x xs ih =>
        intro b c
        simp only [List.foldl_cons, List.all_cons]
        rw [ih, Bool.and_assoc]
    rw [hfold, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi; rw [getD_map_fst]; exact h i hi
    · intro h i hi; rw [← getD_map_fst]; exact h i hi
  · simp only [linStep, boolStep, hop, GateOp.eval]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro ⟨i, hi, hit⟩; exact ⟨i, hi, by rw [getD_map_fst]; exact hit⟩
    · intro ⟨i, hi, hit⟩; exact ⟨i, hi, by rw [← getD_map_fst]; exact hit⟩

lemma scan_lin_fst (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ws : List (Bool × Bool)) :
    (scan linStep gs ws).map (·.1) = scan boolStep gs (ws.map (·.1)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    rw [scan_cons, scan_cons, ih hgs]
    simp [boolStep_fst_linStep g hg ws]

lemma lpInit_map_fst (N : ℕ) (p l : Fin N) :
    (lpInit N p l).map (·.1) = List.ofFn (pointInput N p) := by
  apply List.ext_getElem
  · simp [lpInit_length]
  · intro i h1 h2
    have hi : i < N + N := by simpa [lpInit_length] using h1
    rw [List.getElem_map, List.getElem_ofFn]
    have hg := lpInit_getD N p l i hi
    rw [List.getD_eq_getElem _ _ (by simp [lpInit_length, hi])] at hg
    rw [hg]
    by_cases hlt : i < N
    · simp [hlt, pointInput]
    · simp [hlt, pointInput]
      omega

lemma lpAt_fst (C : Circuit) (hAO : AndOrOnly C) (N : ℕ) (p l : Fin N) (w : ℕ) :
    (lpAt C N p l w).1 = wireVal (N + N) C w (pointInput N p) := by
  rw [lpAt, lpList, linearParts_eq_scan]
  change ((scan linStep C.gates (lpInit N p l)).getD w (false, false)).1 =
    (scan boolStep C.gates (List.ofFn (pointInput N p))).getD w false
  rw [← getD_map_fst, scan_lin_fst C.gates hAO, lpInit_map_fst]

lemma lpList_length (C : Circuit) (N : ℕ) (p l : Fin N) :
    (lpList C N p l).length = N + N + C.gates.length := by
  rw [lpList, linearParts_eq_scan, scan_length]
  change (lpInit N p l).length + C.gates.length = N + N + C.gates.length
  rw [lpInit_length]

lemma lpAt_ge (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    lpAt C N p l w = (false, false) := by
  rw [lpAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [lpList_length]; exact hw)]
  rfl

lemma lpAt_lt_len (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : w < N + N) :
    lpAt C N p l w = (lpInit N p l).getD w (false, false) := by
  rw [lpAt, lpList, linearParts_eq_scan]
  exact scan_prefix linStep C.gates (lpInit N p l) (false, false) w (by rw [lpInit_length]; exact hw)

lemma lpAt_snd_lt_N (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : w < N) :
    (lpAt C N p l w).2 = false := by
  rw [lpAt_lt_len C N p l w (by omega), lpInit_getD N p l w (by omega)]
  simp [hw]

lemma lpAt_snd_line (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (h1 : N ≤ w) (h2 : w < N + N) :
    (lpAt C N p l w).2 = decide (w = N + l.val) := by
  rw [lpAt_lt_len C N p l w h2, lpInit_getD N p l w h2]
  have hnot : ¬ (w < N) := by omega
  simp [hnot]

lemma lpAt_gate {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) :
    lpAt C N p l (N + N + j) = linStep (lpList C N p l) C.gates[j] := by
  rw [lpAt, lpList, linearParts_eq_scan]
  have hlen : (lpInit N p l).length = N + N := lpInit_length N p l
  conv_lhs => rw [← hlen]
  apply scan_gate linStep C.gates (lpInit N p l) (false, false) j hj
  intro q1 q2 hq
  simp only [linStep]
  have hrb := hAO2.2.1 j hj
  have hcongr : C.gates[j].inputs.map (fun i => q1.getD i (false, false)) =
      C.gates[j].inputs.map (fun i => q2.getD i (false, false)) := by
    apply List.map_congr_left
    intro i hi
    apply hq
    rw [hlen]
    exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
  rw [hcongr]

lemma lpAt_snd_or {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    (lpAt C N p l (N + N + j)).2 =
      ((lpAt C N p l (opnd C j 0)).2 || (lpAt C N p l (opnd C j 1)).2) := by
  rw [lpAt_gate hAO2 p l hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [linStep, hop, hin, lpAt]

lemma lpAt_snd_and {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    (lpAt C N p l (N + N + j)).2 =
      ((wireVal (N + N) C (opnd C j 0) (pointInput N p) && (lpAt C N p l (opnd C j 1)).2) ||
       ((lpAt C N p l (opnd C j 0)).2 && wireVal (N + N) C (opnd C j 1) (pointInput N p))) := by
  rw [lpAt_gate hAO2 p l hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp only [linStep, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Bool.true_and, Bool.false_and, Bool.or_false]
  rw [← lpAt_fst C hAO2.1 N p l (opnd C j 0), ← lpAt_fst C hAO2.1 N p l (opnd C j 1)]
  rfl

lemma wireVal_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_scan, scan_length, List.length_ofFn]

lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wireVal n C w x = false := by
  rw [wireVal, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wireVal_length]; exact hw)]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i x = x ⟨i, hi⟩ := by
  rw [wireVal, wires_eq_scan, scan_prefix boolStep C.gates (List.ofFn x) false i (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wireVal n C (n + j) x = boolStep (C.wires (List.ofFn x)) C.gates[j] := by
  rw [wireVal, wires_eq_scan]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h := scan_gate boolStep C.gates (List.ofFn x) false j hj (by
    intro q1 q2 hq
    simp only [boolStep]
    have hrb := hAO2.2.1 j hj
    have hcongr : C.gates[j].inputs.map (fun i => q1.getD i false) =
        C.gates[j].inputs.map (fun i => q2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hq
      rw [hlen]
      exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
    rw [hcongr])
  simpa only [hlen] using h

lemma wireVal_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma wireVal_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma scan_bool_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (lx ly : List Bool) (hlen : lx.length = ly.length)
    (hle : ∀ i, lx.getD i false = true → ly.getD i false = true) :
    (scan boolStep gs lx).length = (scan boolStep gs ly).length ∧
      ∀ w, (scan boolStep gs lx).getD w false = true → (scan boolStep gs ly).getD w false = true := by
  induction gs generalizing lx ly with
  | nil => exact ⟨hlen, hle⟩
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    have hstep : boolStep lx g = true → boolStep ly g = true := by
      intro h
      rcases hg with hop | hop
      · simp only [boolStep, hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply] at h ⊢
        intro i hi
        exact hle i (h i hi)
      · simp only [boolStep, hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply] at h ⊢
        rcases h with ⟨i, hi, hit⟩
        exact ⟨i, hi, hle i hit⟩
    have hlen' : (lx ++ [boolStep lx g]).length = (ly ++ [boolStep ly g]).length := by
      simp [hlen]
    have hle' : ∀ i, (lx ++ [boolStep lx g]).getD i false = true →
        (ly ++ [boolStep ly g]).getD i false = true := by
      intro i hi
      by_cases hil : i < lx.length
      · rw [List.getD_append _ _ _ _ hil] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle i hi
      · by_cases heq : i = lx.length
        · subst heq
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at hi
          rw [hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          exact hstep hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi
    exact ih hgs (lx ++ [boolStep lx g]) (ly ++ [boolStep ly g]) hlen' hle'

lemma wireVal_mono {n : ℕ} {C : Circuit} (hAO : AndOrOnly C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) (w : ℕ) :
    wireVal n C w x = true → wireVal n C w y = true := by
  have hle : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i hi
    by_cases hin : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [hin]), List.getElem_ofFn] at hi ⊢
      exact hxy ⟨i, hin⟩ hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
      simp at hi
  exact (scan_bool_mono C.gates hAO (List.ofFn x) (List.ofFn y) (by simp) hle).2 w

lemma eval_zInput_false {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hSound : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l' : Fin N // z (Fin.natAdd N l') = true } ≤ 1 →
      (¬ ∃ p l' : Fin N, I p l' ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l') = true) →
      circuitFun (N + N) C z = false)
    (l : Fin N) :
    wireVal (N + N) C C.output (zInput I l) = false := by
  have hcard : Fintype.card { l' : Fin N // zInput I l (Fin.natAdd N l') = true } ≤ 1 := by
    have hsub : Subsingleton { l' : Fin N // zInput I l (Fin.natAdd N l') = true } := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : a.1 = l := by
        have h1 : (Fin.natAdd N a.1).val = N + a.1.val := Fin.val_natAdd N a.1
        have h2 := a.2
        dsimp only [zInput] at h2
        split_ifs at h2 with hlt
        · omega
        · simp only [h1, decide_eq_true_eq] at h2
          exact Fin.ext (by omega)
      have hb : b.1 = l := by
        have h1 : (Fin.natAdd N b.1).val = N + b.1.val := Fin.val_natAdd N b.1
        have h2 := b.2
        dsimp only [zInput] at h2
        split_ifs at h2 with hlt
        · omega
        · simp only [h1, decide_eq_true_eq] at h2
          exact Fin.ext (by omega)
      exact ha.trans hb.symm
    exact Fintype.card_le_one_iff_subsingleton.mpr hsub
  have hno : ¬ ∃ p l' : Fin N, I p l' ∧ zInput I l (Fin.castAdd N p) = true ∧
      zInput I l (Fin.natAdd N l') = true := by
    rintro ⟨p, l', hI, hp, hl'⟩
    have hl'' : l' = l := by
      have h1 : (Fin.natAdd N l').val = N + l'.val := Fin.val_natAdd N l'
      dsimp only [zInput] at hl'
      split_ifs at hl' with hlt
      · omega
      · simp only [h1, decide_eq_true_eq] at hl'
        exact Fin.ext (by omega)
    subst hl''
    have hp' : ¬ I p l' := by
      have h1 : (Fin.castAdd N p).val = p.val := Fin.val_castAdd N p
      have h2 : (Fin.castAdd N p).val < N := p.isLt
      have hpe : (⟨(Fin.castAdd N p).val, h2⟩ : Fin N) = p := Fin.ext h1
      simp only [zInput, h2, dite_true, hpe, decide_eq_true_eq] at hp
      exact hp
    exact hp' hI
  exact hSound (zInput I l) hcard hno

lemma pointInput_le_zInput {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    {p l' : Fin N} (hnot : ¬ I p l') :
    ∀ i : Fin (N + N), pointInput N p i = true → zInput I l' i = true := by
  intro i hi
  simp only [pointInput, decide_eq_true_eq] at hi
  have hlt : i.val < N := by omega
  have hpi : (⟨i.val, hlt⟩ : Fin N) = p := Fin.ext hi
  simp [zInput, hlt, hpi, hnot]

def aSet (C : Circuit) (N w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun p => wireVal (N + N) C w (pointInput N p) = true

def zLineSet {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (w : ℕ) :
    Finset (Fin N) :=
  Finset.univ.filter fun l => wireVal (N + N) C w (zInput I l) = true

lemma mem_aSet {C : Circuit} {N w : ℕ} {p : Fin N} :
    p ∈ aSet C N w ↔ wireVal (N + N) C w (pointInput N p) = true := by
  simp [aSet]

lemma mem_zLineSet {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] {C : Circuit} {w : ℕ} {l : Fin N} :
    l ∈ zLineSet I C w ↔ wireVal (N + N) C w (zInput I l) = true := by
  simp [zLineSet]

lemma aSet_lt_N (C : Circuit) (N : ℕ) {w : ℕ} (hw : w < N) :
    aSet C N w = {⟨w, hw⟩} := by
  ext p
  rw [mem_aSet, wireVal_input (N + N) C (pointInput N p) w (by omega)]
  simp [pointInput, Fin.ext_iff, eq_comm]

lemma aSet_line (C : Circuit) (N : ℕ) {w : ℕ} (h1 : N ≤ w) (h2 : w < N + N) :
    aSet C N w = ∅ := by
  ext p
  rw [mem_aSet, wireVal_input (N + N) C (pointInput N p) w h2]
  simp [pointInput]
  omega

lemma aSet_ge (C : Circuit) (N : ℕ) {w : ℕ} (hw : N + N + C.gates.length ≤ w) :
    aSet C N w = ∅ := by
  ext p
  rw [mem_aSet, wireVal_ge (N + N) C (pointInput N p) w hw]
  simp

lemma zLineSet_line {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    {w : ℕ} (h1 : N ≤ w) (h2 : w < N + N) :
    zLineSet I C w = {⟨w - N, by omega⟩} := by
  ext l
  rw [mem_zLineSet, wireVal_input (N + N) C (zInput I l) w h2]
  have hnot : ¬ (w < N) := by omega
  simp [zInput, hnot, Fin.ext_iff]
  omega

lemma zLineSet_and {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C) {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    zLineSet I C (N + N + j) = zLineSet I C (opnd C j 0) ∩ zLineSet I C (opnd C j 1) := by
  ext l
  simp [mem_zLineSet, wireVal_and hAO2 (zInput I l) hj hop]

lemma aSet_subset_of_zInput_false {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    {C : Circuit} (hAO : AndOrOnly C) {w : ℕ} {l : Fin N}
    (hz : wireVal (N + N) C w (zInput I l) = false) :
    ∀ p' ∈ aSet C N w, I p' l := by
  intro p' hp'
  rw [mem_aSet] at hp'
  by_contra hnot
  have ht := wireVal_mono hAO (pointInput_le_zInput I hnot) w hp'
  rw [hz] at ht
  exact Bool.noConfusion ht

def bStep (C : Circuit) (N : ℕ) (p : Fin N) (w w' : ℕ) : Prop :=
  ∃ j < C.gates.length, w = (N + N) + j ∧
    (((gateAt C j).op = GateOp.or ∧ (w' = opnd C j 0 ∨ w' = opnd C j 1)) ∨
     ((gateAt C j).op = GateOp.and ∧
       ((w' = opnd C j 0 ∧ wireVal (N + N) C (opnd C j 1) (pointInput N p) = true) ∨
        (w' = opnd C j 1 ∧ wireVal (N + N) C (opnd C j 0) (pointInput N p) = true))))

def reachesOut (C : Circuit) (N : ℕ) (p : Fin N) (w : ℕ) : Prop :=
  Relation.ReflTransGen (bStep C N p) C.output w

lemma bStep_zInput {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C) {p l' : Fin N} (hnot : ¬ I p l') {w w' : ℕ}
    (hs : bStep C N p w w') (hw' : wireVal (N + N) C w' (zInput I l') = true) :
    wireVal (N + N) C w (zInput I l') = true := by
  rcases hs with ⟨j, hj, rfl, ⟨hop, rfl | rfl⟩ | ⟨hop, ⟨rfl, ha⟩ | ⟨rfl, ha⟩⟩⟩
  · rw [wireVal_or hAO2 _ hj hop, hw', Bool.true_or]
  · rw [wireVal_or hAO2 _ hj hop, hw', Bool.or_true]
  · have ha' := wireVal_mono hAO2.1 (pointInput_le_zInput I hnot) (opnd C j 1) ha
    rw [wireVal_and hAO2 _ hj hop, hw', ha', Bool.true_and]
  · have ha' := wireVal_mono hAO2.1 (pointInput_le_zInput I hnot) (opnd C j 0) ha
    rw [wireVal_and hAO2 _ hj hop, ha', hw', Bool.true_and]

lemma reachesOut_zInput_gen {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C) {p l' : Fin N} (hnot : ¬ I p l') {u v : ℕ}
    (hr : Relation.ReflTransGen (bStep C N p) u v)
    (hv : wireVal (N + N) C v (zInput I l') = true) :
    wireVal (N + N) C u (zInput I l') = true := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hs _ ih => exact bStep_zInput I hAO2 hnot hs ih

lemma reachesOut_zLineSet {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C)
    (hEval : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l' : Fin N // z (Fin.natAdd N l') = true } ≤ 1 →
      (¬ ∃ p l' : Fin N, I p l' ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l') = true) →
      circuitFun (N + N) C z = false)
    {p : Fin N} {w : ℕ} (hr : reachesOut C N p w) :
    ∀ l' ∈ zLineSet I C w, I p l' := by
  intro l' hl'
  rw [mem_zLineSet] at hl'
  by_contra hnot
  have hout := reachesOut_zInput_gen I hAO2 hnot hr hl'
  have hf := eval_zInput_false I C hEval l'
  rw [hf] at hout
  exact Bool.noConfusion hout

def R1 {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (kb : Fin C.size × Fin 2) (pl : Fin N × Fin N) : Prop :=
  I pl.1 pl.2 ∧ 2 ≤ (aSet C N (N + N + kb.1.val)).card ∧
    (∀ p' ∈ aSet C N (N + N + kb.1.val), I p' pl.2) ∧
    aSet C N (opnd C kb.1.val kb.2) = {pl.1}

def R2a {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (jb : Fin C.size × Fin 2) (pl : Fin N × Fin N) : Prop :=
  (gateAt C jb.1.val).op = GateOp.and ∧
    aSet C N (opnd C jb.1.val jb.2) = {pl.1} ∧
    zLineSet I C (opnd C jb.1.val (1 - jb.2)) = {pl.2}

def R2b {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (mb : Fin C.size × Fin 2) (pl : Fin N × Fin N) : Prop :=
  I pl.1 pl.2 ∧ (gateAt C mb.1.val).op = GateOp.or ∧
    2 ≤ (zLineSet I C (N + N + mb.1.val)).card ∧
    (∀ l' ∈ zLineSet I C (N + N + mb.1.val), I pl.1 l') ∧
    zLineSet I C (opnd C mb.1.val mb.2) = {pl.2}

lemma R1_uniq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hC4 : ∀ p1 p2 l1 l2 : Fin N, p1 ≠ p2 → l1 ≠ l2 → ¬(I p1 l1 ∧ I p2 l1 ∧ I p1 l2 ∧ I p2 l2))
    (C : Circuit) (kb : Fin C.size × Fin 2) (pl1 pl2 : Fin N × Fin N)
    (h1 : R1 I C kb pl1) (h2 : R1 I C kb pl2) : pl1 = pl2 := by
  have hp : pl1.1 = pl2.1 := Finset.singleton_injective (h1.2.2.2.symm.trans h2.2.2.2)
  have hl : pl1.2 = pl2.2 := by
    by_contra hneL
    have hlt : 1 < (aSet C N (N + N + kb.1.val)).card := Nat.lt_of_lt_of_le (by decide) h1.2.1
    obtain ⟨pa, hpa, pb, hpb, hne⟩ := Finset.one_lt_card.mp hlt
    exact hC4 pa pb pl1.2 pl2.2 hne hneL ⟨h1.2.2.1 pa hpa, h1.2.2.1 pb hpb, h2.2.2.1 pa hpa, h2.2.2.1 pb hpb⟩
  exact Prod.ext hp hl

lemma R2a_uniq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (jb : Fin C.size × Fin 2) (pl1 pl2 : Fin N × Fin N)
    (h1 : R2a I C jb pl1) (h2 : R2a I C jb pl2) : pl1 = pl2 := by
  have hp : pl1.1 = pl2.1 := Finset.singleton_injective (h1.2.1.symm.trans h2.2.1)
  have hl : pl1.2 = pl2.2 := Finset.singleton_injective (h1.2.2.symm.trans h2.2.2)
  exact Prod.ext hp hl

lemma R2b_uniq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hC4 : ∀ p1 p2 l1 l2 : Fin N, p1 ≠ p2 → l1 ≠ l2 → ¬(I p1 l1 ∧ I p2 l1 ∧ I p1 l2 ∧ I p2 l2))
    (C : Circuit) (mb : Fin C.size × Fin 2) (pl1 pl2 : Fin N × Fin N)
    (h1 : R2b I C mb pl1) (h2 : R2b I C mb pl2) : pl1 = pl2 := by
  have hl : pl1.2 = pl2.2 := Finset.singleton_injective (h1.2.2.2.2.symm.trans h2.2.2.2.2)
  have hp : pl1.1 = pl2.1 := by
    by_contra hne
    have hlt : 1 < (zLineSet I C (N + N + mb.1.val)).card := Nat.lt_of_lt_of_le (by decide) h1.2.2.1
    obtain ⟨la, hla, lb, hlb, hneL⟩ := Finset.one_lt_card.mp hlt
    have h1a := h1.2.2.2.1 la hla
    have h1b := h1.2.2.2.1 lb hlb
    have h2a := h2.2.2.2.1 la hla
    have h2b := h2.2.2.2.1 lb hlb
    exact hC4 pl1.1 pl2.1 la lb hne hneL ⟨h1a, h2a, h1b, h2b⟩
  exact Prod.ext hp hl

lemma card_le_of_rel {α β : Type} [Fintype α] [DecidableEq β]
    (S : Finset β) (R : α → β → Prop)
    (hEx : ∀ y ∈ S, ∃ x : α, R x y)
    (hUniq : ∀ x : α, ∀ y1 y2 : β, R x y1 → R x y2 → y1 = y2) :
    S.card ≤ Fintype.card α := by
  classical
  let f : { y : β // y ∈ S } → α := fun y => Classical.choose (hEx y.1 y.2)
  have hf : Function.Injective f := by
    intro y1 y2 heq
    have h1 : R (f y1) y1.1 := Classical.choose_spec (hEx y1.1 y1.2)
    have h2 : R (f y2) y2.1 := Classical.choose_spec (hEx y2.1 y2.2)
    rw [heq] at h1
    exact Subtype.ext (hUniq (f y2) y1.1 y2.1 h1 h2)
  simpa [Fintype.card_coe] using Fintype.card_le_of_injective f hf

lemma classify_pair {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C)
    (hEval : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l' : Fin N // z (Fin.natAdd N l') = true } ≤ 1 →
      (¬ ∃ p l' : Fin N, I p l' ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l') = true) →
      circuitFun (N + N) C z = false)
    (p l : Fin N) (hI : I p l) (hls : (lpAt C N p l C.output).2 = true) :
    (∃ kb, R1 I C kb (p, l)) ∨ (∃ jb, R2a I C jb (p, l)) ∨ (∃ mb, R2b I C mb (p, l)) := by
  classical
  let goodG : ℕ → Prop := fun w =>
    reachesOut C N p w ∧ (lpAt C N p l w).2 = true ∧ wireVal (N + N) C w (zInput I l) = false
  have hOut : goodG C.output :=
    ⟨Relation.ReflTransGen.refl, hls, eval_zInput_false I C hEval l⟩
  let gStar := Nat.find ⟨C.output, hOut⟩
  have hgStar : goodG gStar := Nat.find_spec ⟨C.output, hOut⟩
  have hgMin : ∀ w < gStar, ¬ goodG w := fun w hw => Nat.find_min ⟨C.output, hOut⟩ hw
  have hgLtLen : gStar < N + N + C.gates.length := by
    by_contra hge
    have hge' : N + N + C.gates.length ≤ gStar := by omega
    have hlp := lpAt_ge C N p l gStar hge'
    have hgs2 := hgStar.2.1
    rw [hlp] at hgs2
    exact Bool.noConfusion hgs2
  have hgGeN : N ≤ gStar := by
    by_contra hlt
    have hlp := lpAt_snd_lt_N C N p l gStar (by omega)
    have hgs2 := hgStar.2.1
    rw [hlp] at hgs2
    exact Bool.noConfusion hgs2
  have hgGeNN : N + N ≤ gStar := by
    by_contra hlt
    have hlp := lpAt_snd_line C N p l gStar hgGeN (by omega)
    have hgs2 := hgStar.2.1
    rw [hlp, decide_eq_true_eq] at hgs2
    have hzv : wireVal (N + N) C gStar (zInput I l) = true := by
      rw [wireVal_input (N + N) C (zInput I l) gStar (by omega)]
      have hnot : ¬ (gStar < N) := by omega
      simp [zInput, hgs2]
    have hgs3 := hgStar.2.2
    rw [hzv] at hgs3
    exact Bool.noConfusion hgs3
  let j := gStar - (N + N)
  have hj : j < C.gates.length := by omega
  have hgEq : gStar = N + N + j := by omega
  have ⟨hop, _, h0lt, h1lt⟩ := ao2_gate_props hAO2 hj
  have hNotOr : (gateAt C j).op ≠ GateOp.or := by
    intro hor
    have hlp := lpAt_snd_or hAO2 p l hj hor
    rw [← hgEq, hgStar.2.1] at hlp
    have hz := wireVal_or hAO2 (zInput I l) hj hor
    rw [← hgEq, hgStar.2.2] at hz
    obtain ⟨hz0, hz1⟩ := Bool.or_eq_false_iff.mp hz.symm
    rcases Bool.or_eq_true_iff.mp hlp.symm with h0 | h1
    · have hs : bStep C N p gStar (opnd C j 0) :=
        ⟨j, hj, hgEq, Or.inl ⟨hor, Or.inl rfl⟩⟩
      exact hgMin (opnd C j 0) (by omega)
        ⟨Relation.ReflTransGen.tail hgStar.1 hs, h0, hz0⟩
    · have hs : bStep C N p gStar (opnd C j 1) :=
        ⟨j, hj, hgEq, Or.inl ⟨hor, Or.inr rfl⟩⟩
      exact hgMin (opnd C j 1) (by omega)
        ⟨Relation.ReflTransGen.tail hgStar.1 hs, h1, hz1⟩
  have hAnd : (gateAt C j).op = GateOp.and := hop.resolve_right hNotOr
  have hlpAnd := lpAt_snd_and hAO2 p l hj hAnd
  rw [← hgEq, hgStar.2.1] at hlpAnd
  have hChoice : ∃ b : Fin 2,
      wireVal (N + N) C (opnd C j b) (pointInput N p) = true ∧
      (lpAt C N p l (opnd C j (1 - b))).2 = true := by
    rcases Bool.or_eq_true_iff.mp hlpAnd.symm with h01 | h10
    · rcases Bool.and_eq_true_iff.mp h01 with ⟨ha, hb⟩
      exact ⟨0, ha, by simpa using hb⟩
    · rcases Bool.and_eq_true_iff.mp h10 with ⟨hb, ha⟩
      exact ⟨1, ha, by simpa using hb⟩
  rcases hChoice with ⟨b, hua, hvb⟩
  let uStar := opnd C j b
  let vStar := opnd C j (1 - b)
  have hb01 : b = 0 ∨ b = 1 := by
    rcases b with ⟨_ | _ | _, hb⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  have huLt : uStar < gStar := by
    rcases hb01 with rfl | rfl <;> dsimp [uStar] <;> omega
  have hvLt : vStar < gStar := by
    rcases hb01 with rfl | rfl <;> dsimp [vStar] <;> omega
  have hStepV : bStep C N p gStar vStar := by
    rcases hb01 with rfl | rfl
    · exact ⟨j, hj, hgEq, Or.inr ⟨hAnd, Or.inr ⟨rfl, hua⟩⟩⟩
    · exact ⟨j, hj, hgEq, Or.inr ⟨hAnd, Or.inl ⟨rfl, hua⟩⟩⟩
  have hvReach : reachesOut C N p vStar := Relation.ReflTransGen.tail hgStar.1 hStepV
  have hvZ : wireVal (N + N) C vStar (zInput I l) = true := by
    have hng := hgMin vStar hvLt
    by_contra hne
    have hzf : wireVal (N + N) C vStar (zInput I l) = false := Bool.eq_false_iff.mpr hne
    exact hng ⟨hvReach, hvb, hzf⟩
  have huZ : wireVal (N + N) C uStar (zInput I l) = false := by
    have hz := wireVal_and hAO2 (zInput I l) hj hAnd
    rw [← hgEq, hgStar.2.2] at hz
    rcases hb01 with rfl | rfl
    · dsimp only [uStar]
      dsimp only [vStar] at hvZ
      rw [show (1 : Fin 2) - 0 = 1 from rfl] at hvZ
      rw [hvZ, Bool.and_true] at hz
      exact hz.symm
    · dsimp only [uStar]
      dsimp only [vStar] at hvZ
      rw [show (1 : Fin 2) - 1 = 0 from rfl] at hvZ
      rw [hvZ, Bool.true_and] at hz
      exact hz.symm
  have hpMemU : p ∈ aSet C N uStar := mem_aSet.mpr hua
  have hlMemV : l ∈ zLineSet I C vStar := mem_zLineSet.mpr hvZ
  by_cases hA2 : 2 ≤ (aSet C N uStar).card
  · left
    let hasA : ℕ → Prop := fun w =>
      wireVal (N + N) C w (pointInput N p) = true ∧ wireVal (N + N) C w (zInput I l) = false
    have hExA : ∃ w, hasA w ∧ 2 ≤ (aSet C N w).card := ⟨uStar, ⟨hua, huZ⟩, hA2⟩
    let wA := Nat.find hExA
    have hwA : hasA wA ∧ 2 ≤ (aSet C N wA).card := Nat.find_spec hExA
    have hwAMin : ∀ w < wA, ¬ (hasA w ∧ 2 ≤ (aSet C N w).card) := fun w hw => Nat.find_min hExA hw
    have hwALt : wA < N + N + C.gates.length := by
      by_contra hge
      have h0 : aSet C N wA = ∅ := aSet_ge C N (by omega)
      have hwAc := hwA.2
      rw [h0] at hwAc
      simp at hwAc
    have hwAGe : N + N ≤ wA := by
      by_contra hlt
      by_cases hltN : wA < N
      · have h1 := aSet_lt_N C N hltN
        have hwAc := hwA.2
        rw [h1] at hwAc
        simp at hwAc
      · have h0 := aSet_line C N (w := wA) (by omega) (by omega)
        have hwAc := hwA.2
        rw [h0] at hwAc
        simp at hwAc
    let k := wA - (N + N)
    have hk : k < C.gates.length := by omega
    have hwAEq : wA = N + N + k := by omega
    have ⟨hopk, _, hk0, hk1⟩ := ao2_gate_props hAO2 hk
    have hChildA : ∃ bA : Fin 2, hasA (opnd C k bA) := by
      rcases hopk with hand | hor
      · have ha := wireVal_and hAO2 (pointInput N p) hk hand
        have hz := wireVal_and hAO2 (zInput I l) hk hand
        rw [← hwAEq, hwA.1.1] at ha
        rw [← hwAEq, hwA.1.2] at hz
        obtain ⟨ha0, ha1⟩ := Bool.and_eq_true_iff.mp ha.symm
        rcases Bool.and_eq_false_iff.mp hz.symm with hz0 | hz1
        · exact ⟨0, ha0, hz0⟩
        · exact ⟨1, ha1, hz1⟩
      · have ha := wireVal_or hAO2 (pointInput N p) hk hor
        have hz := wireVal_or hAO2 (zInput I l) hk hor
        rw [← hwAEq, hwA.1.1] at ha
        rw [← hwAEq, hwA.1.2] at hz
        obtain ⟨hz0, hz1⟩ := Bool.or_eq_false_iff.mp hz.symm
        rcases Bool.or_eq_true_iff.mp ha.symm with ha0 | ha1
        · exact ⟨0, ha0, hz0⟩
        · exact ⟨1, ha1, hz1⟩
    rcases hChildA with ⟨bA, hbA⟩
    have hbA01 : bA = 0 ∨ bA = 1 := by
      rcases bA with ⟨_ | _ | _, hb⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
    have hcLt : opnd C k bA < wA := by
      rcases hbA01 with rfl | rfl <;> omega
    have hcCard : (aSet C N (opnd C k bA)).card < 2 := by
      by_contra hge2
      exact hwAMin (opnd C k bA) hcLt ⟨hbA, by omega⟩
    have hcMem : p ∈ aSet C N (opnd C k bA) := mem_aSet.mpr hbA.1
    have hcSing : aSet C N (opnd C k bA) = {p} := by
      have hpos : 0 < (aSet C N (opnd C k bA)).card := Finset.card_pos.mpr ⟨p, hcMem⟩
      have hcard1 : (aSet C N (opnd C k bA)).card = 1 := by omega
      obtain ⟨p', hp'⟩ := Finset.card_eq_one.mp hcard1
      rw [hp'] at hcMem ⊢
      simp at hcMem
      simp [hcMem]
    refine ⟨(⟨k, hk⟩, bA), hI, ?_, ?_, hcSing⟩
    · simpa [← hwAEq] using hwA.2
    · simpa [← hwAEq] using aSet_subset_of_zInput_false I hAO2.1 hwA.1.2
  · right
    have huMem : p ∈ aSet C N uStar := hpMemU
    have huSing : aSet C N uStar = {p} := by
      have hpos : 0 < (aSet C N uStar).card := Finset.card_pos.mpr ⟨p, huMem⟩
      have hcard1 : (aSet C N uStar).card = 1 := by omega
      obtain ⟨p', hp'⟩ := Finset.card_eq_one.mp hcard1
      rw [hp'] at huMem ⊢
      simp at huMem
      simp [huMem]
    by_cases hB2 : 2 ≤ (zLineSet I C vStar).card
    · right
      let hasB : ℕ → Prop := fun w =>
        reachesOut C N p w ∧ (lpAt C N p l w).2 = true ∧ l ∈ zLineSet I C w
      have hExB : ∃ w, hasB w ∧ 2 ≤ (zLineSet I C w).card :=
        ⟨vStar, ⟨hvReach, hvb, hlMemV⟩, hB2⟩
      let wB := Nat.find hExB
      have hwB : hasB wB ∧ 2 ≤ (zLineSet I C wB).card := Nat.find_spec hExB
      have hwBMin : ∀ w < wB, ¬ (hasB w ∧ 2 ≤ (zLineSet I C w).card) := fun w hw => Nat.find_min hExB hw
      have hwBLeV : wB ≤ vStar := Nat.find_min' hExB ⟨⟨hvReach, hvb, hlMemV⟩, hB2⟩
      have hwBLtG : wB < gStar := lt_of_le_of_lt hwBLeV hvLt
      have hwBLtLen : wB < N + N + C.gates.length := by
        by_contra hge
        have hlp := lpAt_ge C N p l wB (by omega)
        have hwb2 := hwB.1.2.1
        rw [hlp] at hwb2
        exact Bool.noConfusion hwb2
      have hwBGeN : N ≤ wB := by
        by_contra hlt
        have hlp := lpAt_snd_lt_N C N p l wB (by omega)
        have hwb2 := hwB.1.2.1
        rw [hlp] at hwb2
        exact Bool.noConfusion hwb2
      have hwBGeNN : N + N ≤ wB := by
        by_contra hlt
        have hzl := zLineSet_line I C hwBGeN (by omega)
        have hwBc := hwB.2
        rw [hzl] at hwBc
        simp at hwBc
      let m := wB - (N + N)
      have hm : m < C.gates.length := by omega
      have hwBEq : wB = N + N + m := by omega
      have ⟨hopm, _, hm0, hm1⟩ := ao2_gate_props hAO2 hm
      have hNotAnd : (gateAt C m).op ≠ GateOp.and := by
        intro hand
        have hlp := lpAt_snd_and hAO2 p l hm hand
        rw [← hwBEq, hwB.1.2.1] at hlp
        have hz := zLineSet_and I hAO2 hm hand
        rw [← hwBEq] at hz
        have hlZ := hwB.1.2.2
        rw [hz, Finset.mem_inter] at hlZ
        rcases Bool.or_eq_true_iff.mp hlp.symm with h01 | h10
        · rcases Bool.and_eq_true_iff.mp h01 with ⟨ha0, hb1⟩
          have hs : bStep C N p wB (opnd C m 1) :=
            ⟨m, hm, hwBEq, Or.inr ⟨hand, Or.inr ⟨rfl, ha0⟩⟩⟩
          have hsub : zLineSet I C wB ⊆ zLineSet I C (opnd C m 1) := by
            rw [hz]
            exact Finset.inter_subset_right
          have hcard : 2 ≤ (zLineSet I C (opnd C m 1)).card :=
            le_trans hwB.2 (Finset.card_le_card hsub)
          exact hwBMin (opnd C m 1) (by omega)
            ⟨⟨Relation.ReflTransGen.tail hwB.1.1 hs, hb1, hlZ.2⟩, hcard⟩
        · rcases Bool.and_eq_true_iff.mp h10 with ⟨hb0, ha1⟩
          have hs : bStep C N p wB (opnd C m 0) :=
            ⟨m, hm, hwBEq, Or.inr ⟨hand, Or.inl ⟨rfl, ha1⟩⟩⟩
          have hsub : zLineSet I C wB ⊆ zLineSet I C (opnd C m 0) := by
            rw [hz]
            exact Finset.inter_subset_left
          have hcard : 2 ≤ (zLineSet I C (opnd C m 0)).card :=
            le_trans hwB.2 (Finset.card_le_card hsub)
          exact hwBMin (opnd C m 0) (by omega)
            ⟨⟨Relation.ReflTransGen.tail hwB.1.1 hs, hb0, hlZ.1⟩, hcard⟩
      have hOr : (gateAt C m).op = GateOp.or := hopm.resolve_left hNotAnd
      have hlpOr := lpAt_snd_or hAO2 p l hm hOr
      rw [← hwBEq, hwB.1.2.1] at hlpOr
      have hChildB : ∃ bB : Fin 2, (lpAt C N p l (opnd C m bB)).2 = true := by
        rcases Bool.or_eq_true_iff.mp hlpOr.symm with h0 | h1
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
      rcases hChildB with ⟨bB, hbB⟩
      have hbB01 : bB = 0 ∨ bB = 1 := by
        rcases bB with ⟨_ | _ | _, hb⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      have hcLt : opnd C m bB < wB := by
        rcases hbB01 with rfl | rfl <;> omega
      have hStepB : bStep C N p wB (opnd C m bB) := by
        rcases hbB01 with rfl | rfl
        · exact ⟨m, hm, hwBEq, Or.inl ⟨hOr, Or.inl rfl⟩⟩
        · exact ⟨m, hm, hwBEq, Or.inl ⟨hOr, Or.inr rfl⟩⟩
      have hcReach : reachesOut C N p (opnd C m bB) :=
        Relation.ReflTransGen.tail hwB.1.1 hStepB
      have hcZ : l ∈ zLineSet I C (opnd C m bB) := by
        rw [mem_zLineSet]
        have hng := hgMin (opnd C m bB) (lt_trans hcLt hwBLtG)
        by_contra hne
        have hzf : wireVal (N + N) C (opnd C m bB) (zInput I l) = false :=
          Bool.eq_false_iff.mpr hne
        exact hng ⟨hcReach, hbB, hzf⟩
      have hcCard : (zLineSet I C (opnd C m bB)).card < 2 := by
        by_contra hge2
        exact hwBMin (opnd C m bB) hcLt ⟨⟨hcReach, hbB, hcZ⟩, by omega⟩
      have hcSing : zLineSet I C (opnd C m bB) = {l} := by
        have hpos : 0 < (zLineSet I C (opnd C m bB)).card := Finset.card_pos.mpr ⟨l, hcZ⟩
        have hcard1 : (zLineSet I C (opnd C m bB)).card = 1 := by omega
        obtain ⟨l', hl'⟩ := Finset.card_eq_one.mp hcard1
        rw [hl'] at hcZ ⊢
        simp at hcZ
        simp [hcZ]
      refine ⟨(⟨m, hm⟩, bB), hI, hOr, ?_, ?_, hcSing⟩
      · simpa [← hwBEq] using hwB.2
      · simpa [← hwBEq] using reachesOut_zLineSet I hAO2 hEval hwB.1.1
    · left
      have hvSing : zLineSet I C vStar = {l} := by
        have hpos : 0 < (zLineSet I C vStar).card := Finset.card_pos.mpr ⟨l, hlMemV⟩
        have hcard1 : (zLineSet I C vStar).card = 1 := by omega
        obtain ⟨l', hl'⟩ := Finset.card_eq_one.mp hcard1
        rw [hl'] at hlMemV ⊢
        simp at hlMemV
        simp [hlMemV]
      exact ⟨(⟨j, hj⟩, b), hAnd, huSing, hvSing⟩

lemma main (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hUnique : ∀ p1 p2 l1 l2 : Fin N, p1 ≠ p2 → l1 ≠ l2 → ¬(I p1 l1 ∧ I p2 l1 ∧ I p1 l2 ∧ I p2 l2))
    (hAO2 : IsAO2 (N + N) C)
    (hEval : ∀ z : Fin (N + N) → Bool,
      Fintype.card { l' : Fin N // z (Fin.natAdd N l') = true } ≤ 1 →
      (¬ ∃ p l' : Fin N, I p l' ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l') = true) →
      circuitFun (N + N) C z = false) :
    Fintype.card { pl : Fin N × Fin N // I pl.1 pl.2 ∧
      lineSingle C (N + N) (fun k => decide (N ≤ k)) pl.1.val (N + pl.2.val) = true } ≤ 10 * C.size := by
  classical
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun pl =>
    I pl.1 pl.2 ∧ lineSingle C (N + N) (fun k => decide (N ≤ k)) pl.1.val (N + pl.2.val) = true
  have hCardE : Fintype.card { pl : Fin N × Fin N // I pl.1 pl.2 ∧
      lineSingle C (N + N) (fun k => decide (N ≤ k)) pl.1.val (N + pl.2.val) = true } = E.card := by
    rw [Fintype.card_subtype]
  rw [hCardE]
  let E1 := E.filter fun pl => ∃ kb, R1 I C kb pl
  let E2a := E.filter fun pl => ∃ jb, R2a I C jb pl
  let E2b := E.filter fun pl => ∃ mb, R2b I C mb pl
  have hSub : E ⊆ E1 ∪ (E2a ∪ E2b) := by
    intro pl hpl
    have hmem := Finset.mem_filter.mp hpl
    rcases hmem.2 with ⟨hI, hls⟩
    rw [lineSingle_eq_lpAt] at hls
    rcases classify_pair I hAO2 hEval pl.1 pl.2 hI hls with h1 | h2a | h2b
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpl, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpl, h2a⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpl, h2b⟩))
  have hc1 : E1.card ≤ Fintype.card (Fin C.size × Fin 2) :=
    card_le_of_rel E1 (R1 I C) (fun y hy => (Finset.mem_filter.mp hy).2) (R1_uniq I hUnique C)
  have hc2a : E2a.card ≤ Fintype.card (Fin C.size × Fin 2) :=
    card_le_of_rel E2a (R2a I C) (fun y hy => (Finset.mem_filter.mp hy).2) (R2a_uniq I C)
  have hc2b : E2b.card ≤ Fintype.card (Fin C.size × Fin 2) :=
    card_le_of_rel E2b (R2b I C) (fun y hy => (Finset.mem_filter.mp hy).2) (R2b_uniq I hUnique C)
  have hFcard : Fintype.card (Fin C.size × Fin 2) = 2 * C.size := by
    simp [Fintype.card_prod, mul_comm]
  have hUnion : E.card ≤ E1.card + (E2a.card + E2b.card) :=
    le_trans (Finset.card_le_card hSub)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  omega

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.LineBound

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds
theorem LineBound : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬(x2 x5 x7 ∧ x2 x6 x7 ∧ x2 x5 x8 ∧ x2 x6 x8)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x7 : Fin (x1 + x1) → Bool), Fintype.card { x8 : Fin x1 // x7 (Fin.natAdd x1 x8) = Bool.true } ≤ (1 : ℕ) → (¬∃ (x9 : Fin x1) (x10 : Fin x1), x2 x9 x10 ∧ x7 (Fin.castAdd x1 x9) = Bool.true ∧ x7 (Fin.natAdd x1 x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x7 = Bool.false) → Fintype.card { x8 : Fin x1 × Fin x1 // x2 x8.1 x8.2 ∧ PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.ReadK.lineSingle x4 (x1 + x1) (fun (x9 : ℕ) => Decidable.decide (x1 ≤ x9)) (↑x8.1) (x1 + ↑x8.2) = Bool.true } ≤ (10 : ℕ) * x4.size := by
  intro x1 x2 _ x4 hC4 hAO2 hSound
  exact PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.LineBound.main x1 x2 x4 hC4 hAO2 hSound


end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds

-- Adapted verbatim from checked L-meta-2972; only namespace and copied ReadK definitions changed.

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound
open PEqualNP.CircuitLowerBounds

def run {α : Type} (F : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [F w g]) init

lemma run_cons {α : Type} (F : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    run F (g :: gs) init = run F gs (init ++ [F init g]) := rfl

lemma run_append {α : Type} (F : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    run F (gs ++ hs) init = run F hs (run F gs init) := by
  unfold run; rw [List.foldl_append]

lemma run_length {α : Type} (F : List α → Gate → α) (gs : List Gate) :
    ∀ init : List α, (run F gs init).length = init.length + gs.length := by
  induction gs with
  | nil => intro init; simp [run]
  | cons g gs ih => intro init; rw [run_cons, ih]; simp; omega

lemma run_getD_lt {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (init : List α) (i : ℕ), i < init.length → (run F gs init).getD i d = init.getD i d := by
  induction gs with
  | nil => intro init i _; rfl
  | cons g gs ih =>
    intro init i hi
    rw [run_cons, ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma run_getD_gate {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (init : List α) (j : ℕ) (g : Gate), gs[j]? = some g →
      (run F gs init).getD (init.length + j) d = F (run F (gs.take j) init) g := by
  induction gs with
  | nil => intro init j g h; simp at h
  | cons g0 gs ih =>
    intro init j g h
    cases j with
    | zero =>
      simp at h
      subst h
      rw [run_cons, run_getD_lt F d gs _ _ (by simp)]
      simp [run]
    | succ j =>
      simp at h
      rw [run_cons]
      have h1 := ih (init ++ [F init g0]) j g h
      simp only [List.length_append, List.length_singleton] at h1
      rw [show init.length + (j + 1) = init.length + 1 + j by omega, h1]
      simp [run_cons]

lemma run_take_getD {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) (init : List α)
    (j i : ℕ) (hj : j ≤ gs.length) (hi : i < init.length + j) :
    (run F (gs.take j) init).getD i d = (run F gs init).getD i d := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  rw [run_getD_lt F d (gs.drop j) (run F (gs.take j) init) i
    (by rw [run_length, List.length_take, Nat.min_eq_left hj]; exact hi)]

def lpF (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  match g.op with
  | GateOp.or => ((g.inputs.map fun i => w.getD i (false, false)).any (·.1),
      (g.inputs.map fun i => w.getD i (false, false)).any (·.2))
  | GateOp.and => (g.inputs.map fun i => w.getD i (false, false)).foldl
      (fun (acc : Bool × Bool) p => (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def lpInit (N : ℕ) (x : List Bool) : List (Bool × Bool) :=
  (x.zipIdx).map fun (b, i) => if (decide (i < N)) then (false, b) else (b, false)

lemma linearParts_eq (C : Circuit) (N : ℕ) (x : List Bool) :
    PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.ReadK.linearParts C (fun i => decide (i < N)) x = run lpF C.gates (lpInit N x) := rfl

def wvF (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = run wvF C.gates x := rfl

def xs (N : ℕ) (x : ℕ → Bool) : List Bool := (List.range (N + N)).map x

def pP (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool × Bool :=
  (PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.ReadK.linearParts C (fun i => decide (i < N)) (xs N x)).getD w (false, false)

def pA (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool := (pP C N x w).1

def pB (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool := (pP C N x w).2

def pV (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) : Bool := (C.wires (xs N x)).getD w false

lemma lpInit_length (N : ℕ) (x : List Bool) : (lpInit N x).length = x.length := by
  simp [lpInit]

lemma xs_length (N : ℕ) (x : ℕ → Bool) : (xs N x).length = N + N := by simp [xs]

lemma pP_input (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : w < N + N) :
    pP C N x w = if w < N then (false, x w) else (x w, false) := by
  unfold pP
  rw [linearParts_eq, run_getD_lt _ _ _ _ _ (by rw [lpInit_length, xs_length]; exact hw)]
  simp [lpInit, xs, List.getD_eq_getElem?_getD, hw]

lemma pV_input (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : w < N + N) :
    pV C N x w = x w := by
  unfold pV
  rw [wires_eq, run_getD_lt _ _ _ _ _ (by rw [xs_length]; exact hw)]
  simp [xs, List.getD_eq_getElem?_getD, hw]

lemma pP_out (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    pP C N x w = (false, false) := by
  unfold pP
  rw [linearParts_eq]
  apply List.getD_eq_default
  rw [run_length, lpInit_length, xs_length]; exact hw

lemma pV_out (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    pV C N x w = false := by
  unfold pV
  rw [wires_eq]
  apply List.getD_eq_default
  rw [run_length, xs_length]; exact hw

lemma pP_gate (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ) (op : GateOp)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pP C N x (N + N + j) = lpF [pP C N x a, pP C N x b] ⟨op, [0, 1]⟩ := by
  have hj : j ≤ C.gates.length := by
    have := (List.getElem?_eq_some_iff.mp hg).1; omega
  have hl : (lpInit N (xs N x)).length = N + N := by rw [lpInit_length, xs_length]
  unfold pP
  rw [linearParts_eq]
  have h1 := run_getD_gate lpF (false, false) C.gates (lpInit N (xs N x)) j _ hg
  rw [hl] at h1
  rw [h1]
  have ea := run_take_getD lpF (false, false) C.gates (lpInit N (xs N x)) j a hj (by rw [hl]; exact ha)
  have eb := run_take_getD lpF (false, false) C.gates (lpInit N (xs N x)) j b hj (by rw [hl]; exact hb)
  simp only [List.getD_eq_getElem?_getD] at ea eb
  cases op <;> simp [lpF, ea, eb]

lemma pV_gate (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ) (op : GateOp)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pV C N x (N + N + j) = op.eval [pV C N x a, pV C N x b] := by
  have hj : j ≤ C.gates.length := by
    have := (List.getElem?_eq_some_iff.mp hg).1; omega
  have hl : (xs N x).length = N + N := xs_length N x
  unfold pV
  rw [wires_eq]
  have h1 := run_getD_gate wvF false C.gates (xs N x) j _ hg
  rw [hl] at h1
  rw [h1]
  have ea := run_take_getD wvF false C.gates (xs N x) j a hj (by rw [hl]; exact ha)
  have eb := run_take_getD wvF false C.gates (xs N x) j b hj (by rw [hl]; exact hb)
  simp only [List.getD_eq_getElem?_getD] at ea eb
  simp [wvF, ea, eb]

def Good (C : Circuit) (N : ℕ) : Prop :=
  (∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) ∧
  (∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < N + N + j) ∧
  ∀ g ∈ C.gates, g.inputs.length = 2

lemma gate_view (C : Circuit) (N : ℕ) (hG : Good C N) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, a < N + N + j ∧ b < N + N + j ∧
      (C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ ∨ C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) := by
  obtain ⟨h1, h2, h3⟩ := hG
  have hm : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have e1 := h1 _ hm
  have e2 := h2 j hj
  have e3 := h3 _ hm
  rw [List.getD_eq_getElem _ _ hj] at e2
  rcases hgj : C.gates[j] with ⟨op, ins⟩
  rw [hgj] at e1 e2 e3
  simp only at e1 e2 e3
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp e3
  refine ⟨a, b, e2 a (by simp), e2 b (by simp), ?_⟩
  rw [List.getElem?_eq_getElem hj, hgj]
  rcases e1 with e1 | e1
  · right; rw [e1]
  · left; rw [e1]

lemma wire_kind (C : Circuit) (N : ℕ) (hG : Good C N) (w : ℕ) :
    w < N ∨ (N ≤ w ∧ w < N + N) ∨
    (∃ j a b, w = N + N + j ∧ a < N + N + j ∧ b < N + N + j ∧
      C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) ∨
    (∃ j a b, w = N + N + j ∧ a < N + N + j ∧ b < N + N + j ∧
      C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) ∨
    N + N + C.gates.length ≤ w := by
  by_cases h1 : w < N
  · exact Or.inl h1
  by_cases h2 : w < N + N
  · exact Or.inr (Or.inl ⟨by omega, h2⟩)
  by_cases h3 : N + N + C.gates.length ≤ w
  · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))
  obtain ⟨a, b, ha, hb, h⟩ := gate_view C N hG (w - (N + N)) (by omega)
  have e : w = N + N + (w - (N + N)) := by omega
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl ⟨_, a, b, e, ha, hb, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, a, b, e, ha, hb, h⟩)))

lemma ev_pt (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : w < N) :
    pA C N x w = false ∧ pB C N x w = x w ∧ pV C N x w = x w := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_input C N x w (by omega), hw]
  · simp [pB, pP_input C N x w (by omega), hw]
  · exact pV_input C N x w (by omega)

lemma ev_ln (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (h1 : N ≤ w) (h2 : w < N + N) :
    pA C N x w = x w ∧ pB C N x w = false ∧ pV C N x w = x w := by
  have h3 : ¬ w < N := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_input C N x w h2, h3]
  · simp [pB, pP_input C N x w h2, h3]
  · exact pV_input C N x w h2

lemma ev_out (C : Circuit) (N : ℕ) (x : ℕ → Bool) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    pA C N x w = false ∧ pB C N x w = false ∧ pV C N x w = false := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_out C N x w hw]
  · simp [pB, pP_out C N x w hw]
  · exact pV_out C N x w hw

lemma ev_or (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ)
    (hg : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pA C N x (N + N + j) = (pA C N x a || pA C N x b) ∧
    pB C N x (N + N + j) = (pB C N x a || pB C N x b) ∧
    pV C N x (N + N + j) = (pV C N x a || pV C N x b) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pB, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pV_gate C N x j a b _ hg ha hb, GateOp.eval]

lemma ev_and (C : Circuit) (N : ℕ) (x : ℕ → Bool) (j a b : ℕ)
    (hg : C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j) :
    pA C N x (N + N + j) = (pA C N x a && pA C N x b) ∧
    pB C N x (N + N + j) = ((pA C N x a && pB C N x b) || (pB C N x a && pA C N x b)) ∧
    pV C N x (N + N + j) = (pV C N x a && pV C N x b) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pA, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pA, pB, pP_gate C N x j a b _ hg ha hb, lpF]
  · simp [pV_gate C N x j a b _ hg ha hb, GateOp.eval]

lemma pA_mono (C : Circuit) (N : ℕ) (hG : Good C N) (x x' : ℕ → Bool)
    (hx : ∀ i, N ≤ i → x i = true → x' i = true) :
    ∀ w, pA C N x w = true → pA C N x' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb, hg⟩ |
      ⟨j, a, b, rfl, ha, hb, hg⟩ | h
    · rw [(ev_pt C N x w h).1]; simp
    · rw [(ev_ln C N x w h1 h2).1, (ev_ln C N x' w h1 h2).1]; exact hx w h1
    · rw [(ev_or C N x j a b hg ha hb).1, (ev_or C N x' j a b hg ha hb).1]
      simp only [Bool.or_eq_true]
      rintro (h | h)
      · exact Or.inl (ih a ha h)
      · exact Or.inr (ih b hb h)
    · rw [(ev_and C N x j a b hg ha hb).1, (ev_and C N x' j a b hg ha hb).1]
      simp only [Bool.and_eq_true]
      rintro ⟨h1, h2⟩
      exact ⟨ih a ha h1, ih b hb h2⟩
    · rw [(ev_out C N x w h).1]; simp

lemma parts_le_val (C : Circuit) (N : ℕ) (hG : Good C N) (x : ℕ → Bool) :
    ∀ w, (pA C N x w = true ∨ pB C N x w = true) → pV C N x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb, hg⟩ |
      ⟨j, a, b, rfl, ha, hb, hg⟩ | h
    · obtain ⟨e1, e2, e3⟩ := ev_pt C N x w h
      rw [e1, e2, e3]; simp
    · obtain ⟨e1, e2, e3⟩ := ev_ln C N x w h1 h2
      rw [e1, e2, e3]; simp
    · obtain ⟨e1, e2, e3⟩ := ev_or C N x j a b hg ha hb
      rw [e1, e2, e3]; simp only [Bool.or_eq_true]
      have iha := ih a ha
      have ihb := ih b hb
      tauto
    · obtain ⟨e1, e2, e3⟩ := ev_and C N x j a b hg ha hb
      rw [e1, e2, e3]; simp only [Bool.or_eq_true, Bool.and_eq_true]
      have iha := ih a ha
      have ihb := ih b hb
      tauto
    · obtain ⟨e1, e2, e3⟩ := ev_out C N x w h
      rw [e1, e2, e3]; simp

def inp (C : Circuit) (j : ℕ) (s : Bool) : ℕ :=
  (C.gates.getD j ⟨GateOp.or, []⟩).inputs.getD (if s then 1 else 0) 0

def sib (C : Circuit) (j : ℕ) (s : Bool) : ℕ :=
  (C.gates.getD j ⟨GateOp.or, []⟩).inputs.getD (if s then 0 else 1) 0

def isAnd (C : Circuit) (j : ℕ) : Prop := ∃ a b, C.gates[j]? = some ⟨GateOp.and, [a, b]⟩

def side (C : Circuit) (N : ℕ) (P : ℕ → Bool) (j : ℕ) (s : Bool) : Prop :=
  isAnd C j → pA C N P (sib C j s) = true

def ctx (C : Circuit) (N : ℕ) (P : ℕ → Bool) : ℕ → ℕ → Prop
  | 0, w => w = C.output
  | k + 1, w => ∃ j s, j < C.gates.length ∧ w = inp C j s ∧ ctx C N P k (N + N + j) ∧
      side C N P j s

def Ctx (C : Circuit) (N : ℕ) (P : ℕ → Bool) (w : ℕ) : Prop := ∃ k, ctx C N P k w

def term (C : Circuit) (N : ℕ) (P : ℕ → Bool) (j : ℕ) (s : Bool) : Prop :=
  j < C.gates.length ∧ Ctx C N P (N + N + j) ∧ side C N P j s

lemma inp_sib (C : Circuit) (j : ℕ) (op : GateOp) (a b : ℕ)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) :
    inp C j false = a ∧ inp C j true = b ∧ sib C j false = b ∧ sib C j true = a := by
  simp [inp, sib, List.getD_eq_getElem?_getD, hg]

lemma inp_lt (C : Circuit) (N : ℕ) (hG : Good C N) (j : ℕ) (s : Bool) (hj : j < C.gates.length) :
    inp C j s < N + N + j := by
  obtain ⟨a, b, ha, hb, hg⟩ := gate_view C N hG j hj
  rcases hg with hg | hg
  · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
    cases s
    · rw [e1]; exact ha
    · rw [e2]; exact hb
  · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
    cases s
    · rw [e1]; exact ha
    · rw [e2]; exact hb

lemma not_isAnd_of_or (C : Circuit) (j a b : ℕ) (hg : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) :
    ¬ isAnd C j := by
  rintro ⟨a', b', h'⟩
  rw [hg] at h'
  simp at h'

lemma Ctx_out (C : Circuit) (N : ℕ) (P : ℕ → Bool) : Ctx C N P C.output := ⟨0, by simp [ctx]⟩

lemma Ctx_cases (C : Circuit) (N : ℕ) (P : ℕ → Bool) (w : ℕ) (h : Ctx C N P w) :
    w = C.output ∨ ∃ j s, w = inp C j s ∧ term C N P j s := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero => left; simpa [ctx] using hk
  | succ k =>
    simp only [ctx] at hk
    obtain ⟨j, s, hj, hw, hc, hs⟩ := hk
    exact Or.inr ⟨j, s, hw, hj, ⟨k, hc⟩, hs⟩

lemma term_to_Ctx (C : Circuit) (N : ℕ) (P : ℕ → Bool) (j : ℕ) (s : Bool)
    (h : term C N P j s) : Ctx C N P (inp C j s) := by
  obtain ⟨hj, ⟨k, hk⟩, hs⟩ := h
  refine ⟨k + 1, ?_⟩
  simp only [ctx]
  exact ⟨j, s, hj, rfl, hk, hs⟩

lemma sib_inp (C : Circuit) (j : ℕ) (s : Bool) : sib C j s = inp C j (!s) := by
  cases s <;> rfl

lemma ctx_mono (C : Circuit) (N : ℕ) (hG : Good C N) (P P' : ℕ → Bool)
    (h : ∀ i, N ≤ i → P i = true → P' i = true) :
    ∀ k w, ctx C N P k w → ctx C N P' k w := by
  intro k
  induction k with
  | zero => intro w hw; simpa [ctx] using hw
  | succ k ih =>
    intro w hw
    simp only [ctx] at hw ⊢
    obtain ⟨j, s, hj, e, hc, hs⟩ := hw
    exact ⟨j, s, hj, e, ih _ hc, fun ha => pA_mono C N hG P P' h _ (hs ha)⟩

def xin (P : ℕ → Bool) (l : ℕ) : ℕ → Bool := fun i => P i || i == l

lemma ctx_B (C : Circuit) (N : ℕ) (hG : Good C N) (P : ℕ → Bool) (l : ℕ) :
    ∀ k w, ctx C N P k w → pB C N (xin P l) w = true → pB C N (xin P l) C.output = true := by
  intro k
  induction k with
  | zero =>
    intro w h hb
    simp only [ctx] at h
    rw [← h]; exact hb
  | succ k ih =>
    intro w h hb
    simp only [ctx] at h
    obtain ⟨j, s, hj, hw, hc, hs⟩ := h
    apply ih _ hc
    obtain ⟨a, b, ha, hb', hg⟩ := gate_view C N hG j hj
    rcases hg with hg | hg
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      rw [(ev_or C N (xin P l) j a b hg ha hb').2.1]
      cases s
      · rw [hw, e1] at hb; simp [hb]
      · rw [hw, e2] at hb; simp [hb]
    · obtain ⟨e1, e2, e3, e4⟩ := inp_sib C j _ a b hg
      have hs' := pA_mono C N hG P (xin P l) (by intro i _ h; simp [xin, h]) _ (hs ⟨a, b, hg⟩)
      rw [(ev_and C N (xin P l) j a b hg ha hb').2.1]
      cases s
      · rw [hw, e1] at hb; rw [e3] at hs'; simp [hb, hs']
      · rw [hw, e2] at hb; rw [e4] at hs'; simp [hb, hs']

lemma B_ctx (C : Circuit) (N : ℕ) (hG : Good C N) (P : ℕ → Bool)
    (hP : ∀ i, P i = true → N ≤ i) (p : ℕ) (hp : p < N) :
    ∀ w, Ctx C N P w → pB C N (xin P p) w = true → Ctx C N P p := by
  have hmono : ∀ c, pA C N (xin P p) c = true → pA C N P c = true := by
    intro c
    apply pA_mono C N hG (xin P p) P
    intro i hi h
    simp only [xin, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact h
    · omega
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hc hb
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb', hg⟩ |
      ⟨j, a, b, rfl, ha, hb', hg⟩ | h
    · rw [(ev_pt C N _ w h).2.1] at hb
      simp only [xin, Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with hb | hb
      · exact absurd (hP w hb) (by omega)
      · rw [← hb]; exact hc
    · rw [(ev_ln C N _ w h1 h2).2.1] at hb; simp at hb
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      have hns := not_isAnd_of_or C j a b hg
      rw [(ev_or C N _ j a b hg ha hb').2.1] at hb
      simp only [Bool.or_eq_true] at hb
      rcases hb with hb | hb
      · apply ih a ha _ hb
        rw [← e1]; exact term_to_Ctx C N P j false ⟨hj, hc, fun h => absurd h hns⟩
      · apply ih b hb' _ hb
        rw [← e2]; exact term_to_Ctx C N P j true ⟨hj, hc, fun h => absurd h hns⟩
    · obtain ⟨e1, e2, e3, e4⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      rw [(ev_and C N _ j a b hg ha hb').2.1] at hb
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hb
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · apply ih b hb' _ h2
        rw [← e2]
        exact term_to_Ctx C N P j true ⟨hj, hc, fun _ => by rw [e4]; exact hmono a h1⟩
      · apply ih a ha _ h1
        rw [← e1]
        exact term_to_Ctx C N P j false ⟨hj, hc, fun _ => by rw [e3]; exact hmono b h2⟩
    · rw [(ev_out C N _ w h).2.1] at hb; simp at hb

lemma ofFn_xs (N : ℕ) (x : ℕ → Bool) : List.ofFn (fun i : Fin (N + N) => x i) = xs N x := by
  apply List.ext_getElem <;> simp [xs]

def inL (N : ℕ) (L : Finset (Fin N)) : ℕ → Bool :=
  fun i => decide (∃ l ∈ L, i = N + (l : ℕ))

lemma inL_supp (N : ℕ) (L : Finset (Fin N)) (i : ℕ) (h : inL N L i = true) : N ≤ i := by
  simp only [inL, decide_eq_true_eq] at h
  obtain ⟨l, _, e⟩ := h
  omega

lemma inL_mono (N : ℕ) (L L' : Finset (Fin N)) (h : L ⊆ L') (i : ℕ)
    (hi : inL N L i = true) : inL N L' i = true := by
  simp only [inL, decide_eq_true_eq] at hi ⊢
  obtain ⟨l, hl, e⟩ := hi
  exact ⟨l, h hl, e⟩

lemma inL_mem (N : ℕ) (L : Finset (Fin N)) (a : Fin N) (h : inL N L (N + (a : ℕ)) = true) :
    a ∈ L := by
  simp only [inL, decide_eq_true_eq] at h
  obtain ⟨l, hl, e⟩ := h
  have e' : a = l := Fin.ext (by omega)
  rw [e']; exact hl

def AL (C : Circuit) (N : ℕ) (w : ℕ) : Finset (Fin N) → Prop :=
  fun L => pA C N (inL N L) w = true

def CL (C : Circuit) (N : ℕ) (w : ℕ) : Finset (Fin N) → Prop :=
  fun L => Ctx C N (inL N L) w

def TL (C : Circuit) (N : ℕ) (j : ℕ) (s : Bool) : Finset (Fin N) → Prop :=
  fun L => term C N (inL N L) j s

def MonoL (N : ℕ) (φ : Finset (Fin N) → Prop) : Prop :=
  ∀ L L' : Finset (Fin N), L ⊆ L' → φ L → φ L'

lemma mono_AL (C : Circuit) (N : ℕ) (hG : Good C N) (w : ℕ) : MonoL N (AL C N w) :=
  fun L L' h hf => pA_mono C N hG (inL N L) (inL N L')
    (fun i _ hi => inL_mono N L L' h i hi) w hf

lemma mono_CL (C : Circuit) (N : ℕ) (hG : Good C N) (w : ℕ) : MonoL N (CL C N w) :=
  fun L L' h hf => by
    obtain ⟨k, hk⟩ := hf
    exact ⟨k, ctx_mono C N hG (inL N L) (inL N L')
      (fun i _ hi => inL_mono N L L' h i hi) k w hk⟩

lemma ctx_sound (C : Circuit) (N q : ℕ) (hG : Good C N) (I : Fin N → Fin N → Prop)
    (hS : ∀ (x11 : Fin (N + N) → Bool),
      Fintype.card { x12 : Fin N // x11 (Fin.natAdd N x12) = Bool.true } ≤ q →
      (¬∃ (x13 : Fin N) (x14 : Fin N), I x13 x14 ∧ x11 (Fin.castAdd N x13) = Bool.true ∧
        x11 (Fin.natAdd N x14) = Bool.true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x11 = Bool.false)
    (p : Fin N) (L : Finset (Fin N)) (hc : L.card ≤ q) (h : CL C N p L) :
    ∃ l ∈ L, I p l := by
  have hB : pB C N (xin (inL N L) p) C.output = true := by
    obtain ⟨k, hk⟩ := h
    apply ctx_B C N hG (inL N L) p k p hk
    rw [(ev_pt C N _ p p.isLt).2.1]
    simp [xin]
  have hV := parts_le_val C N hG _ C.output (Or.inr hB)
  by_contra hne
  have hline : ∀ a : Fin N, xin (inL N L) p (N + (a : ℕ)) = true → a ∈ L := by
    intro a ha
    simp only [xin, Bool.or_eq_true, beq_iff_eq] at ha
    rcases ha with ha | ha
    · exact inL_mem N L a ha
    · have := p.isLt; omega
  have h0 := hS (fun i => xin (inL N L) p i) (by
      refine le_trans ?_ hc
      rw [← Fintype.card_coe L]
      apply Fintype.card_le_of_injective
        (fun x : { x12 : Fin N // xin (inL N L) p (Fin.natAdd N x12) = Bool.true } =>
          (⟨x.1, hline x.1 (by have h' := x.2; simpa only [Fin.val_natAdd] using h')⟩ :
            { a // a ∈ L }))
      intro x y e
      apply Subtype.ext
      exact congrArg (fun z : { a // a ∈ L } => z.1) e) (by
      rintro ⟨p', l', hinc, hp', hl'⟩
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hp' hl'
      have hl'L := hline l' hl'
      simp only [xin, Bool.or_eq_true, beq_iff_eq] at hp'
      rcases hp' with hp' | hp'
      · have h1 := inL_supp N L _ hp'
        have h2 := p'.isLt
        omega
      · have e : p' = p := Fin.ext hp'
        rw [e] at hinc
        exact hne ⟨l', hl'L, hinc⟩)
  have h1 : pV C N (xin (inL N L) p) C.output = false := by
    unfold pV
    rw [← ofFn_xs]
    exact h0
  rw [h1] at hV
  simp at hV

lemma ls_eq (C : Circuit) (N : ℕ) (p l : Fin N)
    (h : PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.ReadK.lineSingle C (N + N) (fun x13 => decide (x13 < N)) p (N + l) = true) :
    pB C N (xin (inL N {l}) p) C.output = true := by
  have hf : (fun i : ℕ => (i == (p : ℕ) || i == N + (l : ℕ))) = xin (inL N {l}) p := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp [xin, inL, or_comm]
  unfold PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.ReadK.lineSingle at h
  rw [hf] at h
  exact h

def Below1 (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N) : Prop :=
  ∀ L : Finset (Fin N), L.card ≤ 1 → φ L → ∃ l ∈ L, I p l

lemma below1_single (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N)
    (h : Below1 N I φ p) (l : Fin N) (hl : φ {l}) : I p l := by
  obtain ⟨l', h1, h2⟩ := h {l} (by simp) hl
  rw [Finset.mem_singleton] at h1
  rw [← h1]; exact h2

lemma owner_unique (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (φ : Finset (Fin N) → Prop) (p p' : Fin N) (h : Below1 N I φ p) (h' : Below1 N I φ p')
    (l1 l2 : Fin N) (hne : l1 ≠ l2) (h1 : φ {l1}) (h2 : φ {l2}) : p = p' := by
  by_contra hp
  obtain ⟨m, _, hm⟩ := hU p p' hp
  have e1 := hm l1 ⟨below1_single N I φ p h l1 h1, below1_single N I φ p' h' l1 h1⟩
  have e2 := hm l2 ⟨below1_single N I φ p h l2 h2, below1_single N I φ p' h' l2 h2⟩
  exact hne (e1.trans e2.symm)

noncomputable def wit (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop)
    (p : Fin N) : Finset (Fin N) := by
  classical
  exact if h : ∃ a, ¬ I p a ∧ φ {a} then {Classical.choose h} else ∅

lemma wit_card (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N) :
    (wit N I φ p).card ≤ 1 := by
  classical
  unfold wit
  split_ifs <;> simp

lemma wit_avoid (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N)
    (a : Fin N) (ha : a ∈ wit N I φ p) : ¬ I p a := by
  classical
  unfold wit at ha
  split_ifs at ha with h
  · rw [Finset.mem_singleton] at ha
    rw [ha]; exact (Classical.choose_spec h).1
  · simp at ha

lemma wit_accept (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N)
    (hm : MonoL N φ) (hb : ¬ Below1 N I φ p) (L' : Finset (Fin N))
    (hL : wit N I φ p ⊆ L') : φ L' := by
  classical
  unfold Below1 at hb
  rw [not_forall] at hb
  obtain ⟨L, hb⟩ := hb
  rw [Classical.not_imp] at hb
  obtain ⟨hc, hb⟩ := hb
  rw [Classical.not_imp] at hb
  obtain ⟨hφ, hno⟩ := hb
  rcases Nat.eq_zero_or_pos L.card with h0 | hpos
  · rw [Finset.card_eq_zero] at h0
    rw [h0] at hφ
    exact hm ∅ L' (Finset.empty_subset _) hφ
  · have h1 : L.card = 1 := by omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    have hex : ∃ a, ¬ I p a ∧ φ {a} :=
      ⟨a, fun hI => hno ⟨a, Finset.mem_singleton_self a, hI⟩, hφ⟩
    unfold wit at hL
    split_ifs at hL
    exact hm _ L' hL (Classical.choose_spec hex).2

def Owned (N : ℕ) (I : Fin N → Fin N → Prop) (φ : Finset (Fin N) → Prop) (p : Fin N) : Prop :=
  Below1 N I φ p ∧ ∃ l1 l2 : Fin N, l1 ≠ l2 ∧ φ {l1} ∧ φ {l2}

def Owns (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N)
    (τ : Fin C.gates.length × Bool) : Prop :=
  (τ.2 = true ∧ Owned N I (AL C N (N + N + (τ.1 : ℕ))) p) ∨
  (τ.2 = false ∧ Owned N I (CL C N (N + N + (τ.1 : ℕ))) p)

lemma owns_unique (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p p' : Fin N) (τ : Fin C.gates.length × Bool)
    (h : Owns C N I p τ) (h' : Owns C N I p' τ) : p = p' := by
  rcases h with ⟨e, hb, l1, l2, hne, h1, h2⟩ | ⟨e, hb, l1, l2, hne, h1, h2⟩
  · rcases h' with ⟨e', hb', _⟩ | ⟨e', _⟩
    · exact owner_unique N I hU _ p p' hb hb' l1 l2 hne h1 h2
    · rw [e] at e'; simp at e'
  · rcases h' with ⟨e', _⟩ | ⟨e', hb', _⟩
    · rw [e] at e'; simp at e'
    · exact owner_unique N I hU _ p p' hb hb' l1 l2 hne h1 h2

noncomputable def ownedSet (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) :
    Finset (Fin C.gates.length × Bool) := by
  classical
  exact Finset.univ.filter (fun τ => Owns C N I p τ)

lemma mem_ownedSet (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N)
    (τ : Fin C.gates.length × Bool) : τ ∈ ownedSet C N I p ↔ Owns C N I p τ := by
  classical
  unfold ownedSet
  simp

noncomputable def Lstar (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) :
    Finset (Fin N) :=
  (ownedSet C N I p).biUnion (fun τ =>
    wit N I (AL C N (inp C τ.1 false)) p ∪ wit N I (AL C N (inp C τ.1 true)) p)

lemma Lstar_card (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) :
    (Lstar C N I p).card ≤ 2 * (ownedSet C N I p).card := by
  unfold Lstar
  refine le_trans Finset.card_biUnion_le ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 2 ?_) ?_
  · intro τ _
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 := wit_card N I (AL C N (inp C τ.1 false)) p
    have h2 := wit_card N I (AL C N (inp C τ.1 true)) p
    omega
  · simp [mul_comm]

lemma Lstar_avoid (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) (a : Fin N)
    (ha : a ∈ Lstar C N I p) : ¬ I p a := by
  unfold Lstar at ha
  rw [Finset.mem_biUnion] at ha
  obtain ⟨τ, _, ha⟩ := ha
  rw [Finset.mem_union] at ha
  rcases ha with ha | ha
  · exact wit_avoid N I _ p a ha
  · exact wit_avoid N I _ p a ha

lemma Lstar_sub (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N)
    (τ : Fin C.gates.length × Bool) (h : Owns C N I p τ) (s : Bool) :
    wit N I (AL C N (inp C τ.1 s)) p ⊆ Lstar C N I p := by
  intro a ha
  unfold Lstar
  rw [Finset.mem_biUnion]
  refine ⟨τ, (mem_ownedSet C N I p τ).mpr h, ?_⟩
  rw [Finset.mem_union]
  cases s
  · exact Or.inl ha
  · exact Or.inr ha

def RA (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) (j : ℕ) (s : Bool) :
    Prop :=
  Below1 N I (AL C N (N + N + j)) p ∧ AL C N (N + N + j) {l} ∧
  (∃ l1, l1 ≠ l ∧ AL C N (N + N + j) {l1}) ∧
  AL C N (inp C j s) {l} ∧ ∀ l', AL C N (inp C j s) {l'} → l' = l

def RC (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) (j : ℕ) (s : Bool) :
    Prop :=
  Below1 N I (CL C N (inp C j s)) p ∧ CL C N (inp C j s) {l} ∧
  ((∃ l1, l1 ≠ l ∧ CL C N (inp C j s) {l1}) ∨ inp C j s = (p : ℕ)) ∧
  TL C N j s {l} ∧ ∀ l', TL C N j s {l'} → l' = l

lemma RA_unique (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p l p' l' : Fin N) (j : ℕ) (s : Bool)
    (h : RA C N I p l j s) (h' : RA C N I p' l' j s) : p = p' ∧ l = l' := by
  obtain ⟨b, a1, ⟨l1, hne, a2⟩, c1, u⟩ := h
  obtain ⟨b', a1', _, c1', u'⟩ := h'
  exact ⟨owner_unique N I hU _ p p' b b' l1 l hne a2 a1, u' l c1⟩

lemma RC_unique (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p l p' l' : Fin N) (j : ℕ) (s : Bool)
    (h : RC C N I p l j s) (h' : RC C N I p' l' j s) : p = p' ∧ l = l' := by
  obtain ⟨b, a1, d, c1, u⟩ := h
  obtain ⟨b', a1', d', c1', u'⟩ := h'
  refine ⟨?_, u' l c1⟩
  rcases d with ⟨l1, hne, a2⟩ | e
  · exact owner_unique N I hU _ p p' b b' l1 l hne a2 a1
  · rcases d' with ⟨l1, hne, a2⟩ | e'
    · exact owner_unique N I hU _ p p' b b' l1 l' hne a2 a1'
    · exact Fin.ext (e.symm.trans e')

lemma AL_or (C : Circuit) (N : ℕ) (j a b : ℕ)
    (hg : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j)
    (L : Finset (Fin N)) : AL C N (N + N + j) L ↔ (AL C N a L ∨ AL C N b L) := by
  unfold AL
  rw [(ev_or C N (inL N L) j a b hg ha hb).1]
  simp

lemma AL_and (C : Circuit) (N : ℕ) (j a b : ℕ)
    (hg : C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) (ha : a < N + N + j) (hb : b < N + N + j)
    (L : Finset (Fin N)) : AL C N (N + N + j) L ↔ (AL C N a L ∧ AL C N b L) := by
  unfold AL
  rw [(ev_and C N (inL N L) j a b hg ha hb).1]
  simp

lemma findA (C : Circuit) (N : ℕ) (hG : Good C N) (I : Fin N → Fin N → Prop) (p l : Fin N) :
    ∀ w, Below1 N I (AL C N w) p → AL C N w {l} → (∃ l1, l1 ≠ l ∧ AL C N w {l1}) →
      (∃ j s, j < C.gates.length ∧ RA C N I p l j s) ∨
      (∀ L', Lstar C N I p ⊆ L' → AL C N w L') := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hb hl hl1
    obtain ⟨l1, hne, hl1⟩ := hl1
    rcases wire_kind C N hG w with h | ⟨h1, h2⟩ | ⟨j, a, b, rfl, ha, hb', hg⟩ |
      ⟨j, a, b, rfl, ha, hb', hg⟩ | h
    · exfalso
      unfold AL at hl
      rw [(ev_pt C N _ w h).1] at hl
      simp at hl
    · exfalso
      unfold AL at hl hl1
      rw [(ev_ln C N _ w h1 h2).1] at hl hl1
      simp only [inL, Finset.mem_singleton, exists_eq_left, decide_eq_true_eq] at hl hl1
      exact hne (Fin.ext (by omega))
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      have hor := AL_or C N j a b hg ha hb'
      have key : ∀ (s : Bool) (c : ℕ), inp C j s = c → c < N + N + j →
          (∀ L, AL C N c L → AL C N (N + N + j) L) → AL C N c {l} →
          (∃ j s, j < C.gates.length ∧ RA C N I p l j s) ∨
          (∀ L', Lstar C N I p ⊆ L' → AL C N (N + N + j) L') := by
        intro s c hc hlt hle hcl
        have hbc : Below1 N I (AL C N c) p := fun L hL hf => hb L hL (hle L hf)
        by_cases hu : ∀ l', AL C N c {l'} → l' = l
        · left
          refine ⟨j, s, hj, hb, hl, ⟨l1, hne, hl1⟩, ?_, ?_⟩
          · rw [hc]; exact hcl
          · rw [hc]; exact hu
        · rw [not_forall] at hu
          obtain ⟨l2, hu⟩ := hu
          rw [Classical.not_imp] at hu
          rcases ih c hlt hbc hcl ⟨l2, hu.2, hu.1⟩ with h | h
          · exact Or.inl h
          · exact Or.inr (fun L' hL' => hle L' (h L' hL'))
      rcases (hor {l}).mp hl with hla | hlb
      · exact key false a e1 ha (fun L h => (hor L).mpr (Or.inl h)) hla
      · exact key true b e2 hb' (fun L h => (hor L).mpr (Or.inr h)) hlb
    · obtain ⟨e1, e2, _, _⟩ := inp_sib C j _ a b hg
      have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
      have hand := AL_and C N j a b hg ha hb'
      have hown : Owns C N I p (⟨j, hj⟩, true) :=
        Or.inl ⟨rfl, hb, l, l1, hne.symm, hl, hl1⟩
      have key : ∀ (s : Bool) (c : ℕ), inp C j s = c → c < N + N + j →
          AL C N c {l} → AL C N c {l1} →
          (∃ j s, j < C.gates.length ∧ RA C N I p l j s) ∨
          (∀ L', Lstar C N I p ⊆ L' → AL C N c L') := by
        intro s c hc hlt hcl hcl1
        by_cases hbc : Below1 N I (AL C N c) p
        · exact ih c hlt hbc hcl ⟨l1, hne, hcl1⟩
        · right
          intro L' hL'
          apply wit_accept N I (AL C N c) p (mono_AL C N hG c) hbc L'
          have hs := Lstar_sub C N I p (⟨j, hj⟩, true) hown s
          rw [← hc]
          exact Finset.Subset.trans hs hL'
      obtain ⟨hla, hlb⟩ := (hand {l}).mp hl
      obtain ⟨hl1a, hl1b⟩ := (hand {l1}).mp hl1
      rcases key false a e1 ha hla hl1a with h | h
      · exact Or.inl h
      · rcases key true b e2 hb' hlb hl1b with h' | h'
        · exact Or.inl h'
        · exact Or.inr (fun L' hL' => (hand L').mpr ⟨h L' hL', h' L' hL'⟩)
    · exfalso
      unfold AL at hl
      rw [(ev_out C N _ w h).1] at hl
      simp at hl

def Inv (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) (w : ℕ) : Prop :=
  Below1 N I (CL C N w) p ∧ CL C N w {l} ∧ ((∃ l1, l1 ≠ l ∧ CL C N w {l1}) ∨ w = (p : ℕ))

def Done (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) : Prop :=
  (∃ j s, j < C.gates.length ∧ RC C N I p l j s) ∨
  (∃ j s, j < C.gates.length ∧ RA C N I p l j s)

def Esc (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p : Fin N) (w : ℕ) : Prop :=
  ∃ E : Finset (Fin N), E.card ≤ 2 ∧ (∀ a ∈ E, ¬ I p a) ∧ CL C N w (Lstar C N I p ∪ E)

lemma walk_step (C : Circuit) (N : ℕ) (hG : Good C N) (I : Fin N → Fin N → Prop)
    (p l : Fin N) (w : ℕ)
    (ih : ∀ j, j < C.gates.length → w < N + N + j → Inv C N I p l (N + N + j) →
      Done C N I p l ∨ Esc C N I p (N + N + j)) :
    Inv C N I p l w → Done C N I p l ∨ Esc C N I p w := by
  rintro ⟨hb, hl, hd⟩
  rcases Ctx_cases C N _ w hl with ho | ⟨j, s, hw, ht⟩
  · exfalso
    obtain ⟨a, ha, _⟩ := hb ∅ (by simp)
      (by show Ctx C N (inL N ∅) w; rw [ho]; exact Ctx_out C N _)
    simp at ha
  · have hj := ht.1
    have hlt : inp C j s < N + N + j := inp_lt C N hG j s hj
    by_cases hu : ∀ l', TL C N j s {l'} → l' = l
    · left; left
      refine ⟨j, s, hj, ?_, ?_, ?_, ht, hu⟩
      · rw [← hw]; exact hb
      · rw [← hw]; exact hl
      · rw [← hw]; exact hd
    · rw [not_forall] at hu
      obtain ⟨l2, hu⟩ := hu
      rw [Classical.not_imp] at hu
      obtain ⟨ht2, hne2⟩ := hu
      have hside : Done C N I p l ∨ ∀ L', Lstar C N I p ∪ wit N I (AL C N (sib C j s)) p ⊆ L' →
          side C N (inL N L') j s := by
        by_cases hand : isAnd C j
        · have hcl : AL C N (sib C j s) {l} := ht.2.2 hand
          have hcl2 : AL C N (sib C j s) {l2} := ht2.2.2 hand
          by_cases hbc : Below1 N I (AL C N (sib C j s)) p
          · rcases findA C N hG I p l (sib C j s) hbc hcl ⟨l2, hne2, hcl2⟩ with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr (fun L' hL' _ =>
                h L' (Finset.Subset.trans Finset.subset_union_left hL'))
          · right
            intro L' hL' _
            exact wit_accept N I _ p (mono_AL C N hG _) hbc L'
              (Finset.Subset.trans Finset.subset_union_right hL')
        · exact Or.inr (fun L' _ ha => absurd ha hand)
      rcases hside with hdone | hside
      · exact Or.inl hdone
      by_cases hbg : Below1 N I (CL C N (N + N + j)) p
      · have hown : Owns C N I p (⟨j, hj⟩, false) :=
          Or.inr ⟨rfl, hbg, l, l2, Ne.symm hne2, ht.2.1, ht2.2.1⟩
        have hsub : wit N I (AL C N (sib C j s)) p ⊆ Lstar C N I p := by
          rw [sib_inp]
          exact Lstar_sub C N I p (⟨j, hj⟩, false) hown (!s)
        rcases ih j hj (by omega) ⟨hbg, ht.2.1, Or.inl ⟨l2, hne2, ht2.2.1⟩⟩ with
          h | ⟨E, hE1, hE2, hE3⟩
        · exact Or.inl h
        · right
          refine ⟨E, hE1, hE2, ?_⟩
          show Ctx C N (inL N (Lstar C N I p ∪ E)) w
          rw [hw]
          apply term_to_Ctx C N _ j s
          refine ⟨hj, hE3, hside _ ?_⟩
          exact Finset.union_subset Finset.subset_union_left
            (Finset.Subset.trans hsub Finset.subset_union_left)
      · right
        refine ⟨wit N I (CL C N (N + N + j)) p ∪ wit N I (AL C N (sib C j s)) p, ?_, ?_, ?_⟩
        · refine le_trans (Finset.card_union_le _ _) ?_
          have h1 := wit_card N I (CL C N (N + N + j)) p
          have h2 := wit_card N I (AL C N (sib C j s)) p
          omega
        · intro a ha
          rw [Finset.mem_union] at ha
          rcases ha with ha | ha
          · exact wit_avoid N I _ p a ha
          · exact wit_avoid N I _ p a ha
        · show Ctx C N (inL N _) w
          rw [hw]
          apply term_to_Ctx C N _ j s
          refine ⟨hj, ?_, hside _ ?_⟩
          · exact wit_accept N I _ p (mono_CL C N hG _) hbg _
              (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right)
          · exact Finset.union_subset_union (Finset.Subset.refl _) Finset.subset_union_right

lemma walk (C : Circuit) (N : ℕ) (hG : Good C N) (I : Fin N → Fin N → Prop) (p l : Fin N) :
    ∀ m w, N + N + C.gates.length ≤ w + m → Inv C N I p l w →
      Done C N I p l ∨ Esc C N I p w := by
  intro m
  induction m with
  | zero =>
    intro w hw
    apply walk_step C N hG I p l w
    intro j hj hlt
    omega
  | succ m ih =>
    intro w hw
    apply walk_step C N hG I p l w
    intro j hj hlt
    exact ih (N + N + j) (by omega)

lemma stuck_bound (C : Circuit) (N q : ℕ) (hG : Good C N) (I : Fin N → Fin N → Prop)
    (hsound : ∀ (p : Fin N) (L : Finset (Fin N)), L.card ≤ q → CL C N p L → ∃ l ∈ L, I p l)
    (hq : 1 ≤ q) (p l : Fin N) (hK : CL C N (p : ℕ) {l}) (hnd : ¬ Done C N I p l) :
    q + 1 ≤ 2 * (ownedSet C N I p).card + 2 := by
  have hinv : Inv C N I p l p :=
    ⟨fun L hL hf => hsound p L (le_trans hL hq) hf, hK, Or.inr rfl⟩
  rcases walk C N hG I p l (N + N + C.gates.length) p (by omega) hinv with
    h | ⟨E, hE1, hE2, hE3⟩
  · exact absurd h hnd
  · by_contra hlt
    have hcard : (Lstar C N I p ∪ E).card ≤ q := by
      have h1 := Finset.card_union_le (Lstar C N I p) E
      have h2 := Lstar_card C N I p
      omega
    obtain ⟨a, ha, hI⟩ := hsound p _ hcard hE3
    rw [Finset.mem_union] at ha
    rcases ha with ha | ha
    · exact Lstar_avoid C N I p a ha hI
    · exact hE2 a ha hI

lemma pencil_le (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 1 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hL : ∀ (x8 : Fin N), Fintype.card { x9 : Fin N // I x9 x8 } = q + 1)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p : Fin N) (Lp : Finset (Fin N)) (hLp : ∀ l ∈ Lp, I p l) : Lp.card ≤ q + 1 := by
  have hT : ∀ l ∈ Lp, ((Finset.univ.filter (fun r => I r l)).erase p).card = q := by
    intro l hl
    have hpl : I p l := hLp l hl
    rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl⟩)]
    have h1 : (Finset.univ.filter (fun r => I r l)).card = q + 1 := by
      rw [← hL l]
      exact (Fintype.card_of_subtype _ (fun x => by simp)).symm
    omega
  have hdisj : ∀ l ∈ Lp, ∀ l' ∈ Lp, l ≠ l' →
      Disjoint ((Finset.univ.filter (fun r => I r l)).erase p)
        ((Finset.univ.filter (fun r => I r l')).erase p) := by
    intro l hl l' hl' hne
    rw [Finset.disjoint_left]
    intro r hr hr'
    rw [Finset.mem_erase, Finset.mem_filter] at hr hr'
    obtain ⟨m, _, hm⟩ := hU p r (fun e => hr.1 e.symm)
    have e1 := hm l ⟨hLp l hl, hr.2.2⟩
    have e2 := hm l' ⟨hLp l' hl', hr'.2.2⟩
    exact hne (e1.trans e2.symm)
  have hcard : (Lp.biUnion (fun l => (Finset.univ.filter (fun r => I r l)).erase p)).card
      = Lp.card * q := by
    rw [Finset.card_biUnion hdisj, Finset.sum_const_nat hT]
  have hsub : Lp.biUnion (fun l => (Finset.univ.filter (fun r => I r l)).erase p)
      ⊆ Finset.univ.erase p := by
    intro r hr
    rw [Finset.mem_biUnion] at hr
    obtain ⟨l, _, hr⟩ := hr
    rw [Finset.mem_erase] at hr ⊢
    exact ⟨hr.1, Finset.mem_univ r⟩
  have h1 := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
    Fintype.card_fin] at h1
  have h3 : N - 1 = (q + 1) * q := by
    rw [hN]
    have h4 : q ^ 2 + q + 1 - 1 = q ^ 2 + q := by omega
    rw [h4]; ring
  rw [h3] at h1
  exact Nat.le_of_mul_le_mul_right h1 hq

def Rel (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) :
    (Fin C.gates.length × Bool) ⊕ (Fin C.gates.length × Bool) → Prop
  | Sum.inl (j, s) => RC C N I p l j s
  | Sum.inr (j, s) => RA C N I p l j s

lemma rel_unique (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (p l p' l' : Fin N) (σ : (Fin C.gates.length × Bool) ⊕ (Fin C.gates.length × Bool))
    (h : Rel C N I p l σ) (h' : Rel C N I p' l' σ) : p = p' ∧ l = l' := by
  rcases σ with ⟨j, s⟩ | ⟨j, s⟩
  · simp only [Rel] at h h'
    exact RC_unique C N I hU p l p' l' j s h h'
  · simp only [Rel] at h h'
    exact RA_unique C N I hU p l p' l' j s h h'

lemma done_rel (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N)
    (h : Done C N I p l) : ∃ σ, Rel C N I p l σ := by
  rcases h with ⟨j, s, hj, h⟩ | ⟨j, s, hj, h⟩
  · exact ⟨Sum.inl (⟨j, hj⟩, s), h⟩
  · exact ⟨Sum.inr (⟨j, hj⟩, s), h⟩

lemma count (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hG : Good C N)
    (hU : ∀ (x9 x10 : Fin N), x9 ≠ x10 → ∃! x12 : Fin N, I x9 x12 ∧ I x10 x12)
    (hsound : ∀ (p : Fin N) (L : Finset (Fin N)), L.card ≤ q → CL C N p L → ∃ l ∈ L, I p l)
    (hpen : ∀ (p : Fin N) (Lp : Finset (Fin N)), (∀ l ∈ Lp, I p l) → Lp.card ≤ q + 1)
    (hq : 2 ≤ q) {S : Type} [Fintype S] (π : S → Fin N × Fin N) (hπ : Function.Injective π)
    (hI : ∀ x, I (π x).1 (π x).2) (hK : ∀ x, CL C N ((π x).1 : ℕ) {(π x).2}) :
    Fintype.card S ≤ 10 * C.gates.length := by
  classical
  by_cases hq5 : 5 ≤ q
  · have hemb : ∀ p : Fin N, ∃ e : { l : Fin N // (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ } →
        (Fin C.gates.length × Bool) × Fin 3,
        Function.Injective e ∧ ∀ x, Owns C N I p (e x).1 := by
      intro p
      have hc : Fintype.card { l : Fin N // (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ } ≤
          Fintype.card ({ τ : Fin C.gates.length × Bool // Owns C N I p τ } × Fin 3) := by
        rw [Fintype.card_prod, Fintype.card_fin]
        have ho : Fintype.card { τ : Fin C.gates.length × Bool // Owns C N I p τ }
            = (ownedSet C N I p).card :=
          Fintype.card_of_subtype _ (fun τ => mem_ownedSet C N I p τ)
        rw [ho]
        by_cases hne : Nonempty { l : Fin N // (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ }
        · obtain ⟨⟨l0, h0⟩⟩ := hne
          have hb := stuck_bound C N q hG I hsound (by omega) p l0 h0.1.2
            (fun hd => h0.2 (done_rel C N I p l0 hd))
          have hp : Fintype.card { l : Fin N // (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ } ≤ q + 1 := by
            rw [Fintype.card_of_subtype
              (Finset.univ.filter (fun l : Fin N => (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ))
              (fun x => by
                rw [Finset.mem_filter]
                exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩)]
            exact hpen p _ (fun l hl => (Finset.mem_filter.mp hl).2.1.1)
          omega
        · rw [not_nonempty_iff] at hne
          rw [Fintype.card_eq_zero_iff.mpr hne]
          exact Nat.zero_le _
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
      refine ⟨fun x => ((e x).1.1, (e x).2), ?_, fun x => (e x).1.2⟩
      intro x y h
      dsimp only at h
      have h1 : (e x).1.1 = (e y).1.1 := (Prod.mk.inj h).1
      have h2 : (e x).2 = (e y).2 := (Prod.mk.inj h).2
      exact e.injective (Prod.ext (Subtype.ext h1) h2)
    choose E hEinj hEown using hemb
    have hEglob : ∀ (p p' l l' : Fin N) (h : (I p l ∧ CL C N (p : ℕ) {l}) ∧ ¬ ∃ σ, Rel C N I p l σ)
        (h' : (I p' l' ∧ CL C N (p' : ℕ) {l'}) ∧ ¬ ∃ σ, Rel C N I p' l' σ),
        E p ⟨l, h⟩ = E p' ⟨l', h'⟩ → p = p' ∧ l = l' := by
      intro p p' l l' h h' e
      have hp : p = p' := owns_unique C N I hU p p' _ (hEown p ⟨l, h⟩)
        (by rw [e]; exact hEown p' ⟨l', h'⟩)
      subst hp
      exact ⟨rfl, congrArg Subtype.val (hEinj p e)⟩
    have hcard := Fintype.card_le_of_injective
      (fun x : S => if h : ∃ σ, Rel C N I (π x).1 (π x).2 σ then
          (Sum.inl (Classical.choose h) :
            ((Fin C.gates.length × Bool) ⊕ (Fin C.gates.length × Bool)) ⊕
              ((Fin C.gates.length × Bool) × Fin 3))
        else Sum.inr (E (π x).1 ⟨(π x).2, ⟨⟨hI x, hK x⟩, h⟩⟩))
      (by
        intro x y hxy
        dsimp only at hxy
        by_cases hx : ∃ σ, Rel C N I (π x).1 (π x).2 σ
        · by_cases hy : ∃ σ, Rel C N I (π y).1 (π y).2 σ
          · rw [dite_eq_left_of_eq_true (eq_true hx), dite_eq_left_of_eq_true (eq_true hy)] at hxy
            have e := Sum.inl.inj hxy
            have h1 := Classical.choose_spec hx
            have h2 := Classical.choose_spec hy
            have h3 := rel_unique C N I hU _ _ _ _ (Classical.choose hx) h1
              (by rw [show Classical.choose hx = Classical.choose hy from e]; exact h2)
            exact hπ (Prod.ext h3.1 h3.2)
          · rw [dite_eq_left_of_eq_true (eq_true hx), dite_eq_right_of_eq_false (eq_false hy)] at hxy
            cases hxy
        · by_cases hy : ∃ σ, Rel C N I (π y).1 (π y).2 σ
          · rw [dite_eq_right_of_eq_false (eq_false hx), dite_eq_left_of_eq_true (eq_true hy)] at hxy
            cases hxy
          · rw [dite_eq_right_of_eq_false (eq_false hx), dite_eq_right_of_eq_false (eq_false hy)] at hxy
            have e := Sum.inr.inj hxy
            have h3 := hEglob _ _ _ _ _ _ e
            exact hπ (Prod.ext h3.1 h3.2))
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      at hcard
    omega
  · have hrd : ∀ x : S, ∃ σ : Fin C.gates.length × Bool,
        inp C σ.1 σ.2 = ((π x).1 : ℕ) := by
      intro x
      rcases Ctx_cases C N _ _ (hK x) with ho | ⟨j, s, hw, ht⟩
      · exfalso
        obtain ⟨a, ha, _⟩ := hsound (π x).1 ∅ (by simp)
          (by show Ctx C N (inL N ∅) ((π x).1 : ℕ); rw [ho]; exact Ctx_out C N _)
        simp at ha
      · exact ⟨(⟨j, ht.1⟩, s), hw.symm⟩
    have hemb5 : ∀ p : Fin N, ∃ e : { l : Fin N // I p l } → Fin 5, Function.Injective e := by
      intro p
      have hc : Fintype.card { l : Fin N // I p l } ≤ Fintype.card (Fin 5) := by
        rw [Fintype.card_fin, Fintype.card_of_subtype
          (Finset.univ.filter (fun l : Fin N => I p l))
          (fun x => by
            rw [Finset.mem_filter]
            exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩)]
        have h1 := hpen p (Finset.univ.filter (fun l : Fin N => I p l))
          (fun l hl => (Finset.mem_filter.mp hl).2)
        omega
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
      exact ⟨e, e.injective⟩
    choose E5 hE5 using hemb5
    have hE5glob : ∀ (p p' l l' : Fin N) (h : I p l) (h' : I p' l'), p = p' →
        E5 p ⟨l, h⟩ = E5 p' ⟨l', h'⟩ → l = l' := by
      intro p p' l l' h h' hp e
      subst hp
      exact congrArg Subtype.val (hE5 p e)
    have hcard := Fintype.card_le_of_injective
      (fun x : S => ((Classical.choose (hrd x), E5 (π x).1 ⟨(π x).2, hI x⟩) :
        (Fin C.gates.length × Bool) × Fin 5))
      (by
        intro x y hxy
        dsimp only at hxy
        have e1 : Classical.choose (hrd x) = Classical.choose (hrd y) := congrArg Prod.fst hxy
        have e2 : E5 (π x).1 ⟨(π x).2, hI x⟩ = E5 (π y).1 ⟨(π y).2, hI y⟩ :=
          congrArg Prod.snd hxy
        have s1 := Classical.choose_spec (hrd x)
        have s2 := Classical.choose_spec (hrd y)
        rw [e1] at s1
        have hp : (π x).1 = (π y).1 := Fin.ext (s1.symm.trans s2)
        have hl := hE5glob _ _ _ _ _ _ hp e2
        exact hπ (Prod.ext hp hl))
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hcard
    omega

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds
theorem PointBound : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.true } ≤ (10 : ℕ) * x5.size := by
  intro q N I inst C hq hN hL hU hAO hS
  have hG : PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound.Good C N := ⟨hAO.1, hAO.2.1, hAO.2.2⟩
  have hsound : ∀ (p : Fin N) (L : Finset (Fin N)), L.card ≤ q →
      PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound.CL C N p L → ∃ l ∈ L, I p l :=
    fun p L hc h => PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound.ctx_sound C N q hG I hS p L hc h
  have hpen : ∀ (p : Fin N) (Lp : Finset (Fin N)), (∀ l ∈ Lp, I p l) → Lp.card ≤ q + 1 :=
    fun p Lp h => PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound.pencil_le N q I (by omega) hN hL hU p Lp h
  exact PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound.count q N I C hG hU hsound hpen hq Subtype.val
    Subtype.val_injective (fun x => x.2.1) (fun x => by
      apply PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound.B_ctx C N hG _
        (fun i hi => PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound.inL_supp N _ i hi) x.1.1 x.1.1.isLt
        C.output (PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound.Ctx_out C N _)
      exact PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds.PointBound.ls_eq C N x.1.1 x.1.2 x.2.2)


end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds


namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Ownership
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open Relation

lemma dominated_input_output {n : Nat} (C : Circuit) (v : Fin n) (b : Nat) (P : Nat → Prop)
    (path : Trace n C P v.val b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j=j')
    (hb : Live n C b) (x y : Fin n → Bool)
    (same : ∀ i, i ≠ v → x i = y i) (sameGate : val C x b = val C y b) :
    val C x C.output = val C y C.output := by
  by_contra h
  rcases influence path unique same (Relation.ReflTransGen.refl) h with h | h
  · exact (Nat.not_lt_of_ge (next_le hb)) h.1
  · exact h.2 sameGate

lemma carrier_neighborhood_inclusion {n : Nat} (C : Circuit) (G : SimpleGraph (Fin n))
    (hm : Monotone2 C) (he : GraphEval C G) (v u : Fin n) (b : Nat) (P : Nat → Prop)
    (path : Trace n C P v.val b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j=j')
    (hb : Live n C b) (hu : Carries C u b) :
    ∀ w, G.Adj v w → G.Adj u w := by
  classical
  intro w hvw
  have ba : val C (point {u,w}) b = true :=
    acts_mono hm (point_mono (by simp)) b ((carries_iff hm).mp hu).1
  have bb : val C (point (insert v {u,w})) b = true :=
    acts_mono hm (point_mono (Finset.subset_insert _ _)) b ba
  have keep := dominated_input_output C v b P path unique hb
    (point {u,w}) (point (insert v {u,w}))
    (fun i hi => (point_insert hi).symm) (ba.trans bb.symm)
  have accepted : val C (point (insert v {u,w})) C.output = true := by
    apply acts_mono hm (point_mono ?_) C.output ((point_pair he v w).mpr hvw)
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢
    tauto
  exact (point_pair he u w).mp (keep.trans accepted)

lemma carrier_must_be_input {n : Nat} (C : Circuit) (G : SimpleGraph (Fin n))
    (hm : Monotone2 C) (he : GraphEval C G)
    (hno : ∀ u v a b, u ≠ v → a ≠ b → G.Adj u a → G.Adj u b → G.Adj v a → G.Adj v b → False)
    (v u : Fin n) (b : Nat) (P : Nat → Prop)
    (hd : 2 ≤ (G.neighborSet v).ncard)
    (path : Trace n C P v.val b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j=j')
    (hb : Live n C b) (hu : Carries C u b) : u=v := by
  classical
  by_contra hne
  have finite : (G.neighborSet v).Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ finite] at hd
  obtain ⟨a,c,ha,hc,hac⟩ := Finset.one_lt_card_iff.mp hd
  have hva : G.Adj v a := finite.mem_toFinset.mp ha
  have hvc : G.Adj v c := finite.mem_toFinset.mp hc
  have included := carrier_neighborhood_inclusion C G hm he v u b P path unique hb hu
  exact hno v u a c (fun h => hne h.symm) hac hva hvc (included a hva) (included c hvc)

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Ownership


namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open Relation

noncomputable def liveGates (n : Nat) (C : Circuit) : Finset Nat :=
  open Classical in (Finset.range C.gates.length).filter (fun j => Live n C (n+j))

noncomputable def ports (n : Nat) (C : Circuit) : Finset (Nat × Fin 2) :=
  liveGates n C ×ˢ Finset.univ

def portSource (C : Circuit) (t : Nat × Fin 2) : Nat :=
  (NestedCover.gateAt C t.1).inputs.getD t.2.val 0

noncomputable def portCount (n : Nat) (C : Circuit) (a : Nat) : Nat :=
  open Classical in ((ports n C).filter fun t => portSource C t = a).card

def PortBranch (n : Nat) (C : Circuit) (a : Nat) : Prop := 2 ≤ portCount n C a

lemma gate_mem {C : Circuit} {j : Nat} (hj : j < C.gates.length) :
    NestedCover.gateAt C j ∈ C.gates := by
  unfold NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma gate_inputs (n : Nat) (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (hj : j < C.gates.length) :
    (NestedCover.gateAt C j).inputs = [portSource C (j,0), portSource C (j,1)] := by
  have hl := hm.2.2 _ (gate_mem hj)
  obtain ⟨a,b,he⟩ := List.length_eq_two.mp hl
  simp [portSource,he]

lemma slot_mem (n : Nat) (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (j : Nat) (hj : j < C.gates.length) (k : Fin 2) :
    portSource C (j,k) ∈ (NestedCover.gateAt C j).inputs := by
  rw [gate_inputs n C hm j hj]
  fin_cases k <;> simp

lemma gate_lookup {C : Circuit} {j : Nat} (hj : j < C.gates.length) :
    C.gates[j]? = some (NestedCover.gateAt C j) := by
  unfold NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩

lemma port_next (n : Nat) (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (t : Nat × Fin 2) (ht : t ∈ ports n C) :
    LNext n C (portSource C t) (n+t.1) := by
  classical
  obtain ⟨hj,_⟩ := Finset.mem_product.mp ht
  obtain ⟨hj,hlive⟩ := Finset.mem_filter.mp hj
  have hj := Finset.mem_range.mp hj
  have hs := slot_mem n C hm t.1 hj t.2
  exact ⟨⟨hm.2.1 t.1 hj _ hs, t.1, _, gate_lookup hj, rfl, hs⟩,hlive⟩

lemma port_witness {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    {a b : Nat} (h : LNext n C a b) :
    ∃ t ∈ ports n C, portSource C t = a ∧ n+t.1=b := by
  classical
  obtain ⟨⟨_,j,g,hg,rfl,ha⟩,hb⟩ := h
  have hj := (List.getElem?_eq_some_iff.mp hg).1
  have he : NestedCover.gateAt C j = g := by
    have hlookup := gate_lookup hj
    rw [hg] at hlookup
    exact (Option.some.inj hlookup).symm
  rw [← he,gate_inputs n C hm j hj] at ha
  have hport (k : Fin 2) : (j,k) ∈ ports n C := by
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hb⟩,Finset.mem_univ _⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with h | h
  · exact ⟨(j,0),hport 0,h.symm,rfl⟩
  · exact ⟨(j,1),hport 1,h.symm,rfl⟩

lemma nonport_unique {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    {a b c : Nat} (hn : ¬ PortBranch n C a) (hb : LNext n C a b) (hc : LNext n C a c) : b=c := by
  classical
  obtain ⟨t,ht,hs,hb'⟩ := port_witness C hm hb
  obtain ⟨u,hu,hs',hc'⟩ := port_witness C hm hc
  have hcard : ((ports n C).filter fun t => portSource C t = a).card ≤ 1 := by
    unfold PortBranch portCount at hn
    omega
  have same := Finset.card_le_one_iff.mp hcard
    (Finset.mem_filter.mpr ⟨ht,hs⟩) (Finset.mem_filter.mpr ⟨hu,hs'⟩)
  exact hb'.symm.trans ((congrArg (fun t : Nat × Fin 2 => n+t.1) same).trans hc')

lemma source_live {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (t : Nat × Fin 2) (ht : t ∈ ports n C) : portSource C t ∈ living n C := by
  have hn := port_next n C hm t ht
  apply mem_living.mpr
  exact ⟨hn.1.1.trans (next_in_range hn.1), live_before hn.1 hn.2⟩

lemma sum_portCount {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C) :
    ∑ a ∈ living n C, portCount n C a = 2*(liveGates n C).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := ports n C) (t := living n C)
    (f := portSource C) (source_live C hm)
  unfold portCount
  rw [← h]
  simp [ports,Nat.mul_comm]

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port


namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open Relation Classical

lemma liveGates_card (n : Nat) (C : Circuit) :
    (liveGates n C).card = ((living n C).filter fun a => ¬a<n).card := by
  classical
  apply Finset.card_bij (fun j _ => n+j)
  · intro j hj
    obtain ⟨hj,hl⟩ := Finset.mem_filter.mp hj
    have hj := Finset.mem_range.mp hj
    exact Finset.mem_filter.mpr ⟨mem_living.mpr ⟨by omega,hl⟩,by omega⟩
  · intro a ha b hb hab
    omega
  · intro a ha
    obtain ⟨ha,hn⟩ := Finset.mem_filter.mp ha
    obtain ⟨hr,hl⟩ := mem_living.mp ha
    refine ⟨a-n,?_,by omega⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega),by simpa only [Nat.add_sub_of_le (by omega : n ≤ a)] using hl⟩

lemma port_branch_budget {n : Nat} (C : Circuit) (G : SimpleGraph (Fin n))
    (hm : PEqualNP.TopForm.IsAO2 n C) (he : GraphEval C G)
    (active : Finset (Fin n)) (hdegree : ∀ v ∈ active, ∃ u, G.Adj v u)
    (ho : C.output ∈ living n C) :
    active.card + ((living n C).filter (PortBranch n C)).card ≤ C.size+1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a<n)
  let B := W.filter (PortBranch n C)
  let R := W.erase C.output
  have hSub : active.image Fin.val ⊆ W \ S := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,hu⟩ := hdegree v hv
    exact Finset.mem_sdiff.mpr ⟨mem_living.mpr ⟨by have := v.isLt; omega,input_live he hu⟩,
      fun h => (Finset.mem_filter.mp h).2 v.isLt⟩
  have hW : active.card + S.card ≤ W.card := by
    have h := Finset.card_le_card hSub
    rw [Finset.card_image_of_injective _ Fin.val_injective] at h
    have part := Finset.card_sdiff_add_card_eq_card (show S ⊆ W from Finset.filter_subset _ _)
    omega
  have hR : R.card+1 = W.card := by
    exact Finset.card_erase_add_one ho
  have hS : S.card ≤ C.gates.length := by
    rw [← liveGates_card n C]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  have hoNone : ¬ PortBranch n C C.output := by
    intro hb
    have hpos : 0 < ((ports n C).filter fun t => portSource C t = C.output).card := by
      unfold PortBranch portCount at hb
      omega
    obtain ⟨t,ht⟩ := Finset.card_pos.mp hpos
    obtain ⟨ht,hs⟩ := Finset.mem_filter.mp ht
    have hn := port_next n C hm t ht
    rw [hs] at hn
    exact (Nat.not_lt_of_ge (next_le hn.2)) hn.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, portCount n C a := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : Nat)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : Nat) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if PortBranch n C a then 1 else 0 : Nat)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.mp ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : PortBranch n C a
      · have hb' : 2 ≤ portCount n C a := hb
        simpa [heq,hb] using hb'
      · have hp : 0 < portCount n C a := by
          obtain ⟨b,hb⟩ := live_readers_nonempty hl heq
          obtain ⟨t,ht,hs,_⟩ := port_witness C hm (mem_readers.mp hb)
          exact Finset.card_pos.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,hs⟩⟩
        simpa [heq,hb] using Nat.succ_le_of_lt hp
  have hsum : (∑ a ∈ W, portCount n C a) = 2*S.card := by
    rw [sum_portCount C hm,liveGates_card]
  change active.card+B.card ≤ C.gates.length+1
  omega

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Ownership
open Relation Classical

lemma reach_trace {n : Nat} {C : Circuit} {v b : Nat}
    (h : ReflTransGen (Next n C) v b) (hb : Live n C b) :
    Trace n C (fun a => ReflTransGen (Next n C) v a) v b := by
  revert hb
  induction h with
  | refl => intro _; exact .refl
  | tail h hn ih =>
    intro hb
    exact (ih (live_before hn hb)).tail ⟨h,hn,hb⟩

lemma no_reachable_branch_outside_carriers {n : Nat} (C : Circuit) (G : SimpleGraph (Fin n))
    (hm : PEqualNP.TopForm.IsAO2 n C) (hmono : Monotone2 C) (he : GraphEval C G)
    (hno : ∀ u v a b, u ≠ v → a ≠ b → G.Adj u a → G.Adj u b → G.Adj v a → G.Adj v b → False)
    (S : Finset (Fin n))
    (saturated : ∀ b, Live n C b → PortBranch n C b → ∃ u ∈ S, Carries C u b)
    (v : Fin n) (hv : v ∉ S) (hd : 2 ≤ (G.neighborSet v).ncard) :
    ∀ b, ReflTransGen (Next n C) v.val b → Live n C b → ¬ PortBranch n C b := by
  intro b hp hl hb
  have hex : ∃ a, ReflTransGen (Next n C) v.val a ∧ Live n C a ∧ PortBranch n C a :=
    ⟨b,hp,hl,hb⟩
  let first := Nat.find hex
  have hs : ReflTransGen (Next n C) v.val first ∧ Live n C first ∧ PortBranch n C first := Nat.find_spec hex
  have unique : ∀ a j j', a < first → ReflTransGen (Next n C) v.val a →
      LNext n C a j → LNext n C a j' → j=j' := by
    intro a j j' ha hreach hj hj'
    apply nonport_unique C hm _ hj hj'
    intro hbranch
    exact Nat.find_min hex ha ⟨hreach,live_before hj.1 hj.2,hbranch⟩
  obtain ⟨u,hu,hcarry⟩ := saturated first hs.2.1 hs.2.2
  have same := carrier_must_be_input C G hmono he hno v u first _ hd
    (reach_trace hs.1 hs.2.1) unique hs.2.1 hcarry
  exact hv (same ▸ hu)

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open Relation Classical

lemma branch_is_port_branch {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    {a : Nat} (hb : Branch n C a) : PortBranch n C a := by
  by_contra hn
  obtain ⟨b,c,hb,hc,hne⟩ := Finset.one_lt_card_iff.mp hb
  exact hne (nonport_unique C hm hn (mem_readers.mp hb) (mem_readers.mp hc))

theorem carrierCover {n : Nat} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hm : PEqualNP.TopForm.IsAO2 n C) (hC : Monotone2 C) (hE : GraphEval C G)
    (active : Finset (Fin n)) (hdegree : ∀ v ∈ active, ∃ u, G.Adj v u)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ u, ¬ (G.Adj v u ↔ G.Adj w u))
    (hadj : ∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ a b, G.Adj v a ∧ a ≠ w ∧
      G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b))
    (nonempty : ∃ v u, G.Adj v u) :
    ∃ S : Finset (Fin n),
      (∀ u v, G.Adj u v → 2 ≤ (G.neighborSet u).ncard →
          2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) ∧
      active.card + S.card ≤ C.size+1 ∧
      (active.card + S.card = C.size+1 →
        ∀ b, Live n C b → PortBranch n C b → ∃ u ∈ S, Carries C u b) := by
  obtain ⟨v,u,edge⟩ := nonempty
  have ho := (edge_at_output hE edge).2
  have ho' : C.output ∈ living n C := mem_living.2 ⟨ho, .refl⟩
  let S : Finset (Fin n) := Finset.univ.filter fun v =>
    2 ≤ (G.neighborSet v).ncard ∧ Eligible C v
  have hS (u : Fin n) : u ∈ S ↔ 2 ≤ (G.neighborSet u).ncard ∧ Eligible C u := by simp [S]
  have covers : ∀ a b, G.Adj a b → 2 ≤ (G.neighborSet a).ncard → 2 ≤ (G.neighborSet b).ncard → a ∈ S ∨ b ∈ S := by
    intro a b hab hda hdb
    obtain ⟨u,v,hu,hu',hv,hv',hind⟩ := hadj a b hab hda hdb
    rcases covers_edge hC hE hab hu hu' hv hv' hind with ha | hb
    · exact Or.inl ((hS a).2 ⟨hda,ha⟩)
    · exact Or.inr ((hS b).2 ⟨hdb,hb⟩)
  let B := (living n C).filter (PortBranch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have maps : ∀ u ∈ S, f u ∈ B := by
    intro u hu
    obtain ⟨_,hs⟩ := (hS u).1 hu
    have hb := firstBranch_spec u hs
    rw [hf u hs]
    exact Finset.mem_filter.2 ⟨mem_living.2 ⟨(next_le hb.1).trans_lt ho,hb.1⟩,
      branch_is_port_branch C hm hb.2.2⟩
  have inj : Set.InjOn f S := by
    intro u hu v hv huv
    obtain ⟨hdu,hsu⟩ := (hS u).1 hu
    obtain ⟨hdv,hsv⟩ := (hS v).1 hv
    rw [hf u hsu,hf v hsv] at huv
    exact branch_injective hC hE htwins hsu hsv hdu hdv huv
  have hcap : S.card ≤ B.card := Finset.card_le_card_of_injOn f maps inj
  have budget := port_branch_budget C G hm hE active hdegree ho'
  refine ⟨S,covers,(Nat.add_le_add_left hcap _).trans budget,?_⟩
  intro equality b hb hbranch
  have image_eq : S.image f = B := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact maps u hu
    · rw [Finset.card_image_iff.mpr inj]
      change active.card + B.card ≤ C.size+1 at budget
      omega
  have hbB : b ∈ B := Finset.mem_filter.mpr ⟨mem_living.mpr ⟨(next_le hb).trans_lt ho,hb⟩,hbranch⟩
  rw [← image_eq] at hbB
  obtain ⟨u,hu,hfu⟩ := Finset.mem_image.mp hbB
  have eligible := ((hS u).mp hu).2
  refine ⟨u,hu,?_⟩
  rw [hf u eligible] at hfu
  exact hfu ▸ (firstBranch_spec u eligible).2.1

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open Relation Classical

lemma trace_next {n : Nat} {C : Circuit} {P : Nat → Prop} {a b : Nat}
    (h : Trace n C P a b) : ReflTransGen (Next n C) a b := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail h.2.1

lemma incoming_sources_equal {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (v a b target : Nat)
    (none : ∀ w, ReflTransGen (Next n C) v w → Live n C w → ¬ PortBranch n C w)
    (pa : ReflTransGen (Next n C) v a) (pb : ReflTransGen (Next n C) v b)
    (ha : LNext n C a target) (hb : LNext n C b target) : a=b := by
  have ordered (a b : Nat) (pa : ReflTransGen (Next n C) v a)
      (pb : ReflTransGen (Next n C) v b) (ha : LNext n C a target)
      (hb : LNext n C b target) (hle : a ≤ b) : a=b := by
    have path := reach_trace pa (live_before ha.1 ha.2)
    have unique : ∀ w j j', w<a → ReflTransGen (Next n C) v w →
        LNext n C w j → LNext n C w j' → j=j' := by
      intro w j j' _ hw hj hj'
      exact nonport_unique C hm (none w hw (live_before hj.1 hj.2)) hj hj'
    rcases align path unique b (reach_trace pb (live_before hb.1 hb.2)) with h | h
    · omega
    rcases h.cases_head with h | ⟨j,hj,hrest⟩
    · exact h
    have same : target=j := nonport_unique C hm (none a pa (live_before ha.1 ha.2)) ha hj.2
    have hle := trace_le hrest
    have hlt := hb.1.1
    omega
  rcases le_total a b with h | h
  · exact ordered a b pa pb ha hb h
  · exact (ordered b a pb pa hb ha h).symm

lemma incoming_ports_unique {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (v : Nat)
    (none : ∀ w, ReflTransGen (Next n C) v w → Live n C w → ¬ PortBranch n C w)
    (t u : Nat × Fin 2) (ht : t ∈ ports n C) (hu : u ∈ ports n C)
    (sameGate : t.1=u.1)
    (pt : ReflTransGen (Next n C) v (portSource C t))
    (pu : ReflTransGen (Next n C) v (portSource C u)) : t=u := by
  have htn := port_next n C hm t ht
  have hun := port_next n C hm u hu
  have sameSource : portSource C t = portSource C u := by
    apply incoming_sources_equal C hm v _ _ (n+t.1) none pt pu htn
    simpa only [sameGate] using hun
  have hn := none _ pt (live_before htn.1 htn.2)
  have hcard : ((ports n C).filter fun p => portSource C p = portSource C t).card ≤ 1 := by
    unfold PortBranch portCount at hn
    omega
  exact Finset.card_le_one_iff.mp hcard
    (Finset.mem_filter.mpr ⟨ht,rfl⟩) (Finset.mem_filter.mpr ⟨hu,sameSource.symm⟩)

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Parts (linearParts partStep linearParts_zero)
open Relation Classical
-- Generic append-only evaluation lemmas adapted from checked L-meta-2972.
def run {α : Type} (F : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [F w g]) init

lemma run_cons {α : Type} (F : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    run F (g :: gs) init = run F gs (init ++ [F init g]) := rfl

lemma run_append {α : Type} (F : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    run F (gs ++ hs) init = run F hs (run F gs init) := by
  unfold run; rw [List.foldl_append]

lemma run_length {α : Type} (F : List α → Gate → α) (gs : List Gate) :
    ∀ init : List α, (run F gs init).length = init.length + gs.length := by
  induction gs with
  | nil => intro init; simp [run]
  | cons g gs ih => intro init; rw [run_cons, ih]; simp; omega

lemma run_getD_lt {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (init : List α) (i : ℕ), i < init.length → (run F gs init).getD i d = init.getD i d := by
  induction gs with
  | nil => intro init i _; rfl
  | cons g gs ih =>
    intro init i hi
    rw [run_cons, ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma run_getD_gate {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (init : List α) (j : ℕ) (g : Gate), gs[j]? = some g →
      (run F gs init).getD (init.length + j) d = F (run F (gs.take j) init) g := by
  induction gs with
  | nil => intro init j g h; simp at h
  | cons g0 gs ih =>
    intro init j g h
    cases j with
    | zero =>
      simp at h
      subst h
      rw [run_cons, run_getD_lt F d gs _ _ (by simp)]
      simp [run]
    | succ j =>
      simp at h
      rw [run_cons]
      have h1 := ih (init ++ [F init g0]) j g h
      simp only [List.length_append, List.length_singleton] at h1
      rw [show init.length + (j + 1) = init.length + 1 + j by omega, h1]
      simp [run_cons]

lemma run_take_getD {α : Type} (F : List α → Gate → α) (d : α) (gs : List Gate) (init : List α)
    (j i : ℕ) (hj : j ≤ gs.length) (hi : i < init.length + j) :
    (run F (gs.take j) init).getD i d = (run F gs init).getD i d := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  rw [run_getD_lt F d (gs.drop j) (run F (gs.take j) init) i
    (by rw [run_length, List.length_take, Nat.min_eq_left hj]; exact hi)]


noncomputable def parts {n : Nat} (C : Circuit) (marked : Nat → Bool) (x : Fin n → Bool) (w : Nat) : Bool × Bool :=
  (linearParts C marked (List.ofFn x)).getD w (false,false)

lemma parts_input {n : Nat} (C : Circuit) (marked : Nat → Bool) (x : Fin n → Bool) (i : Fin n) :
    parts C marked x i.val = if marked i.val then (false,x i) else (x i,false) := by
  unfold parts linearParts
  change (run partStep C.gates _).getD i.val (false,false) = _
  rw [run_getD_lt _ _ _ _ _ (by simpa using i.isLt)]
  simp

lemma parts_gate {n : Nat} (C : Circuit) (marked : Nat → Bool) (x : Fin n → Bool)
    (j : Nat) (g : Gate) (hg : C.gates[j]?=some g)
    (hback : ∀ i ∈ g.inputs, i < n+j) :
    parts C marked x (n+j) =
      partStep (linearParts C marked (List.ofFn x)) g := by
  let init := ((List.ofFn x).zipIdx).map fun bi =>
    if marked bi.2 then (false,bi.1) else (bi.1,false)
  have hi : init.length=n := by simp [init]
  change (run partStep C.gates init).getD (n+j) (false,false) = _
  rw [show n+j=init.length+j by rw [hi], run_getD_gate _ _ _ _ _ _ hg]
  have equal : g.inputs.map (fun i => (run partStep (C.gates.take j) init).getD i (false,false)) =
      g.inputs.map (fun i => (linearParts C marked (List.ofFn x)).getD i (false,false)) := by
    apply List.map_congr_left
    intro i hmem
    apply run_take_getD
    · exact Nat.le_of_lt (List.getElem?_eq_some_iff.mp hg).1
    · rw [hi]; exact hback i hmem
  simp only [partStep] at equal ⊢
  rw [equal]

lemma parts_two {n : Nat} (C : Circuit) (marked : Nat → Bool) (x : Fin n → Bool)
    (j a b : Nat) (op : GateOp) (hg : C.gates[j]?=some ⟨op,[a,b]⟩)
    (ha : a<n+j) (hb : b<n+j) :
    parts C marked x (n+j) =
    GateOp.rec (motive := fun _ => Bool × Bool)
      ((parts C marked x a).1 && (parts C marked x b).1,
        ((parts C marked x a).1 && (parts C marked x b).2) ||
        ((parts C marked x a).2 && (parts C marked x b).1))
      ((parts C marked x a).1 || (parts C marked x b).1,
       (parts C marked x a).2 || (parts C marked x b).2)
      (false,false) (fun _ => (false,false)) (false,false) op := by
  rw [parts_gate C marked x j _ hg (by simpa using And.intro ha hb)]
  cases op <;> simp [partStep,parts]

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open Relation Classical

lemma not_both_inputs_reachable {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (v j a b : Nat) (op : GateOp) (hg : C.gates[j]?=some ⟨op,[a,b]⟩)
    (hl : Live n C (n+j))
    (none : ∀ w, ReflTransGen (Next n C) v w → Live n C w → ¬ PortBranch n C w) :
    ¬ (ReflTransGen (Next n C) v a ∧ ReflTransGen (Next n C) v b) := by
  intro h
  have hj := (List.getElem?_eq_some_iff.mp hg).1
  have he : NestedCover.gateAt C j = ⟨op,[a,b]⟩ := by
    have hk := gate_lookup hj
    rw [hg] at hk
    exact (Option.some.inj hk).symm
  have mem (k : Fin 2) : (j,k) ∈ ports n C :=
    Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hl⟩,Finset.mem_univ _⟩
  have hzero : portSource C (j,0)=a := by simp [portSource,he]
  have hone : portSource C (j,1)=b := by simp [portSource,he]
  have eq := incoming_ports_unique C hm v none (j,0) (j,1) (mem 0) (mem 1) rfl
    (hzero ▸ h.1) (hone ▸ h.2)
  have : (0 : Fin 2)=1 := congrArg Prod.snd eq
  exact (by decide : (0 : Fin 2) ≠ 1) this

lemma parts_complete_without_branch {n : Nat} (C : Circuit) (hm : PEqualNP.TopForm.IsAO2 n C)
    (marked : Nat → Bool) (x : Fin n → Bool) (v : Nat)
    (only : ∀ i : Fin n, marked i.val=true → x i=true → i.val=v)
    (none : ∀ w, ReflTransGen (Next n C) v w → Live n C w → ¬ PortBranch n C w) :
    ∀ w, Live n C w →
      ((parts C marked x w).1 || (parts C marked x w).2) = val C x w ∧
      (¬ ReflTransGen (Next n C) v w → (parts C marked x w).2=false) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w<n
    · let i : Fin n := ⟨w,hin⟩
      have hparts := parts_input C marked x i
      have hval := val_input C x i
      change parts C marked x w = _ at hparts
      change val C x w = x i at hval
      rw [hparts,hval]
      constructor
      · cases marked i.val <;> cases x i <;> rfl
      · intro hnot
        by_cases hm : marked i.val=true
        · have hx : x i=false := by
            cases he : x i
            · rfl
            · have hiv := only i hm he
              exact False.elim (hnot (hiv ▸ ReflTransGen.refl))
          simp [hm,hx]
        · simp [Bool.eq_false_of_not_eq_true hm]
    by_cases hr : w<n+C.gates.length
    swap
    · have hbeyond : n+C.gates.length ≤ w := Nat.le_of_not_gt hr
      have hp : parts C marked x w = (false,false) := by
        unfold parts
        rw [List.getD_eq_default _ _ (by simpa only
          [PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Parts.linearParts_length,
            List.length_ofFn,Circuit.size] using hbeyond)]
      simp [hp,val_beyond C x hbeyond]
    obtain ⟨j,hj,rfl⟩ : ∃ j, j<C.gates.length ∧ w=n+j := ⟨w-n,by omega,by omega⟩
    let g := NestedCover.gateAt C j
    obtain ⟨a,b,hinputs⟩ := List.length_eq_two.mp (hm.2.2 g (gate_mem hj))
    have hg : C.gates[j]?=some ⟨g.op,[a,b]⟩ := by
      have he : g=⟨g.op,[a,b]⟩ := by
        exact congrArg (fun ins => ({op:=g.op,inputs:=ins} : Gate)) hinputs
      rw [← he]
      exact gate_lookup hj
    have ha : a<n+j := hm.2.1 j hj a (by change _ ∈ g.inputs; rw [hinputs]; simp)
    have hb : b<n+j := hm.2.1 j hj b (by change _ ∈ g.inputs; rw [hinputs]; simp)
    have na : Next n C a (n+j) := ⟨ha,j,_,hg,rfl,by simp⟩
    have nb : Next n C b (n+j) := ⟨hb,j,_,hg,rfl,by simp⟩
    obtain ⟨av,az⟩ := ih a ha (live_before na hw)
    obtain ⟨bv,bz⟩ := ih b hb (live_before nb hw)
    have nodouble := not_both_inputs_reachable C hm v j a b g.op hg hw none
    have vanish : (parts C marked x a).2=false ∨ (parts C marked x b).2=false := by
      by_cases hpa : ReflTransGen (Next n C) v a
      · exact Or.inr (bz (fun hpb => nodouble ⟨hpa,hpb⟩))
      · exact Or.inl (az hpa)
    have eval := val_gate C x hg
    have pair := parts_two C marked x j a b g.op hg ha hb
    have ops := hm.1 g (gate_mem hj)
    constructor
    · rcases ops with hop | hop
      · rw [pair,eval,hop]
        simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
          Bool.and_true,operand,if_pos ha,if_pos hb]
        rw [← av,← bv]
        rcases vanish with hz | hz <;> rw [hz] <;>
          cases (parts C marked x a).1 <;> cases (parts C marked x a).2 <;>
          cases (parts C marked x b).1 <;> cases (parts C marked x b).2 <;> rfl
      · rw [pair,eval,hop]
        simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,
          Bool.or_false,operand,if_pos ha,if_pos hb]
        rw [← av,← bv]
        cases (parts C marked x a).1 <;> cases (parts C marked x a).2 <;>
          cases (parts C marked x b).1 <;> cases (parts C marked x b).2 <;> rfl
    · intro hn
      have hna : ¬ ReflTransGen (Next n C) v a := fun h => hn (h.tail na)
      have hnb : ¬ ReflTransGen (Next n C) v b := fun h => hn (h.tail nb)
      rcases ops with hop | hop <;> rw [pair,hop] <;> simp [az hna,bz hnb]

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Parts (linearParts linearParts_zero masked_ofFn)
open Relation Classical

lemma single_part_at_pair {n : Nat} (C : Circuit) (G : SimpleGraph (Fin n))
    (hm : PEqualNP.TopForm.IsAO2 n C) (he : GraphEval C G)
    (v w : Fin n) (edge : G.Adj v w) (marked : Nat → Bool)
    (hv : marked v.val=true) (hw : marked w.val=false)
    (none : ∀ a, ReflTransGen (Next n C) v.val a → Live n C a → ¬ PortBranch n C a) :
    (parts C marked (point {v,w}) C.output).2=true := by
  have only : ∀ i : Fin n, marked i.val=true → point {v,w} i=true → i.val=v.val := by
    intro i hi hx
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rfl
    · rw [hw] at hi; contradiction
  have total := (parts_complete_without_branch C hm marked (point {v,w}) v.val only none C.output .refl).1
  have zero : (parts C marked (point {v,w}) C.output).1=false := by
    unfold parts
    rw [linearParts_zero C marked (List.ofFn (point {v,w})) (by
      intro g hg; exact hm.1 g hg),masked_ofFn]
    change val C (fun i => if marked i.val then false else point {v,w} i) C.output=false
    have mask : (fun i => if marked i.val then false else point {v,w} i) = point {w} := by
      funext i
      by_cases hi : i=v
      · subst i
        have hne : v ≠ w := G.ne_of_adj edge
        simp [hv,point,hne]
      · by_cases hj : i=w
        · subst i; simp [hw,point]
        · simp [point,hi,hj]
    rw [mask]
    exact point_single_quiet he w
  rw [zero, Bool.false_or, (point_pair he v w).mpr edge] at total
  exact total

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port

namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open Relation Classical
theorem incidenceCarrierCover : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.TopForm.IsAO2 (N+N) C →
      (∀ p r, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      (∀ z : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 2 →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N+N) C z = false) →

      let E := Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
          (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true)
      let A := E.image Prod.fst
      let B := E.image Prod.snd
      E.Nonempty → ∃ U V : Finset (Fin N), (∀ e ∈ E, (∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2) →
          (∃ g ∈ E, g.2 = e.2 ∧ g.1 ≠ e.1) → e.1 ∈ U ∨ e.2 ∈ V) ∧
        A.card+B.card+U.card+V.card ≤ C.size+1 ∧
        (A.card+B.card+U.card+V.card = C.size+1 → ∀ e ∈ E,
          (e.1 ∉ U → (∃ f ∈ E, f.1=e.1 ∧ f.2≠e.2) →
            (parts C (fun i => decide (i < N))
              (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) C.output).2=true) ∧
          (e.2 ∉ V → (∃ f ∈ E, f.2=e.2 ∧ f.1≠e.1) →
            (parts C (fun i => decide (N ≤ i))
              (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) C.output).2=true)) := by
  classical
  let L {N : ℕ} : Fin N → Fin (N+N) := Fin.castAdd N
  let R {N : ℕ} : Fin N → Fin (N+N) := Fin.natAdd N
  have sides {N : ℕ} (p l : Fin N) : L p ≠ R l := by
    intro equal
    have val := congrArg Fin.val equal
    change p.val = N + l.val at val
    have inRange := p.isLt
    omega
  have leftInjective {N : ℕ} : Function.Injective (@L N) := by
    intro a b eq
    have valuations : (L a).val = (L b).val := congrArg Fin.val eq
    exact Fin.ext valuations
  have rightInjective {N : ℕ} : Function.Injective (@R N) := by
    intro a b eq
    have val := congrArg Fin.val eq
    change N + a.val = N + b.val at val
    exact Fin.ext (by omega)
  let graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) :=
    SimpleGraph.fromRel (fun x y => ∃ p l, x = L p ∧ y = R l ∧ I p l)
  have adjEither {N : ℕ} (I : Fin N → Fin N → Prop) (x y : Fin (N+N)) :
      (graph I).Adj x y ↔
        (∃ p l, x = L p ∧ y = R l ∧ I p l) ∨ (∃ p l, y = L p ∧ x = R l ∧ I p l) := by
    unfold graph
    rw [SimpleGraph.fromRel_adj]
    constructor
    · exact And.right
    · intro ok
      refine ⟨?_,ok⟩
      rintro rfl
      rcases ok with ⟨p,l,atP,atL,_⟩ | ⟨p,l,atP,atL,_⟩
      · exact sides p l (atP.symm.trans atL)
      · exact sides p l (atP.symm.trans atL)
  have leftNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) (y : Fin (N+N)) :
      (graph I).Adj (L p) y ↔ ∃ l, y = R l ∧ I p l := by
    rw [adjEither]
    constructor
    · rintro (⟨p',l,atP,atL,inc⟩ | ⟨p',l,_,invalid,_⟩)
      · exact ⟨l, atL, (leftInjective atP).symm ▸ inc⟩
      · exact (sides p l invalid).elim
    · rintro ⟨l,eq,inc⟩
      exact Or.inl ⟨p,l,rfl,eq,inc⟩
  have rightNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) (y : Fin (N+N)) :
      (graph I).Adj (R l) y ↔ ∃ p, y = L p ∧ I p l := by
    rw [adjEither]
    constructor
    · rintro (⟨p,l',invalid,_,_⟩ | ⟨p,l',atP,atL,inc⟩)
      · exact (sides p l invalid.symm).elim
      · exact ⟨p,atP,(rightInjective atL).symm ▸ inc⟩
    · rintro ⟨p,eq,inc⟩
      exact Or.inr ⟨p,l,eq,rfl,inc⟩
  have leftRight {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
      (graph I).Adj (L p) (R l) ↔ I p l := by
    rw [leftNeighbors]
    constructor
    · rintro ⟨k,eq,inc⟩
      exact (rightInjective eq).symm ▸ inc
    · exact fun inc => ⟨l,rfl,inc⟩
  have noFour {N : ℕ} (I : Fin N → Fin N → Prop)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (u v a b : Fin (N+N)) (vertices : u ≠ v) (neighbors : a ≠ b)
      (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
      (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
    have crosses (p l : Fin N) (otherP otherL : Fin (N+N))
        (differentP : L p ≠ otherP) (differentL : R l ≠ otherL)
        (pl : I p l) (pOther : (graph I).Adj (L p) otherL)
        (otherL' : (graph I).Adj otherP (R l)) (pair : (graph I).Adj otherP otherL) : False := by
      obtain ⟨k, rfl, pk⟩ := (leftNeighbors I p otherL).mp pOther
      obtain ⟨r, rfl, rl⟩ := (rightNeighbors I l otherP).mp ((graph I).adj_symm otherL')
      have rk := (leftRight I r k).mp pair
      have distinct : p ≠ r := fun eq => differentP (congrArg L eq)
      have same := (unique p r distinct).unique ⟨pl,rl⟩ ⟨pk,rk⟩
      exact differentL (congrArg R same)
    rcases (adjEither I u a).mp ua with ⟨p,l,rfl,rfl,pl⟩ | ⟨p,l,rfl,rfl,pl⟩
    · exact crosses p l v b vertices neighbors pl ub va vb
    · exact crosses p l b v neighbors vertices pl ((graph I).adj_symm va) ((graph I).adj_symm ub) ((graph I).adj_symm vb)
  intro N I inst C mono ao uniq sound
  let pair (u v i : Fin (N+N)) := decide (i = u ∨ i = v)
  let J (p l : Fin N) := I p l ∧ circuitFun (N+N) C (pair (L p) (R l)) = true
  let E := Finset.univ.filter (fun e : Fin N × Fin N => J e.1 e.2)
  dsimp only
  intro nonempty
  let G := graph J
  have subAdj {u v} (h : G.Adj u v) : (graph I).Adj u v := by
    rcases (adjEither J u v).mp h with ⟨p,l,rfl,rfl,j⟩ | ⟨p,l,rfl,rfl,j⟩
    · exact (leftRight I p l).mpr j.1
    · exact (graph I).adj_symm ((leftRight I p l).mpr j.1)
  have hE : GraphEval C G := by
    intro u v
    let x := pair u v
    have fx : point {u,v} = x := by funext i; simp [point,x,pair]
    rw [fx]
    change circuitFun (N+N) C x = true ↔ G.Adj u v
    constructor
    · intro recognized
      have small : Fintype.card {l : Fin N // x (R l) = true} ≤ 2 := by
        let emb (l : {l : Fin N // x (R l) = true}) : ↥({u,v} : Finset (Fin (N+N))) :=
          ⟨R l.val, by simpa [x,pair] using l.property⟩
        apply (Fintype.card_le_of_injective emb (by
          intro a b eq; exact Subtype.ext (rightInjective (congrArg Subtype.val eq)))).trans
        simpa only [Fintype.card_coe, Finset.card_singleton] using
          Finset.card_insert_le (a := u) (s := ({v} : Finset (Fin (N+N))))
      have existsInc : ∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true := by
        by_contra missing
        rw [sound x small missing] at recognized
        contradiction
      obtain ⟨p,l,inc,onP,onL⟩ := existsInc
      rcases of_decide_eq_true onP with hp | hp <;> rcases of_decide_eq_true onL with hl | hl
      · exact (sides p l (hp.trans hl.symm)).elim
      · subst u; subst v
        exact (leftRight J p l).mpr ⟨inc, recognized⟩
      · subst v; subst u
        apply G.adj_symm
        apply (leftRight J p l).mpr
        refine ⟨inc,?_⟩
        convert recognized using 1 <;> simp [x,pair,Bool.or_comm]
      · exact (sides p l (hp.trans hl.symm)).elim
    · intro hit
      rcases (adjEither J u v).mp hit with ⟨p,l,rfl,rfl,j⟩ | ⟨p,l,rfl,rfl,j⟩
      · exact j.2
      · have eq : x = pair (L p) (R l) := by funext i; simp [x,pair,Bool.or_comm]
        rw [eq]; exact j.2
  have neighbors (v : Fin (N+N)) (h : 2 ≤ (G.neighborSet v).ncard) :
      ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
    have finite : (G.neighborSet v).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card _ finite] at h
    obtain ⟨a,b,ha,hb,ne⟩ := Finset.one_lt_card_iff.mp h
    exact ⟨a,b,ne,finite.mem_toFinset.mp ha,finite.mem_toFinset.mp hb⟩
  have noTwins (v w : Fin (N+N)) (diff : v ≠ w) (_ : ¬ G.Adj v w)
      (hv : 2 ≤ (G.neighborSet v).ncard) (_ : 2 ≤ (G.neighborSet w).ncard) :
      ∃ a, ¬(G.Adj v a ↔ G.Adj w a) := by
    by_contra! same
    obtain ⟨a,b,distinct,va,vb⟩ := neighbors v hv
    exact noFour I uniq v w a b diff distinct (subAdj va) (subAdj vb)
      (subAdj ((same a).mp va)) (subAdj ((same b).mp vb))
  have other (v w : Fin (N+N)) (h : 2 ≤ (G.neighborSet v).ncard) : ∃ a, G.Adj v a ∧ a ≠ w := by
    obtain ⟨a,b,diff,ha,hb⟩ := neighbors v h
    by_cases eq : a = w
    · exact ⟨b,hb,fun h => diff (eq.trans h.symm)⟩
    · exact ⟨a,ha,eq⟩
  have adjacent (v w : Fin (N+N)) (edge : G.Adj v w)
      (hv : 2 ≤ (G.neighborSet v).ncard) (hw : 2 ≤ (G.neighborSet w).ncard) :
      ∃ a b, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a=b ∨ ¬ G.Adj a b) := by
    obtain ⟨a,va,aw⟩ := other v w hv
    obtain ⟨b,wb,bv⟩ := other w v hw
    exact ⟨a,b,va,aw,wb,bv,Or.inr (fun ab => noFour I uniq w a v b aw.symm bv.symm
      (subAdj (G.adj_symm edge)) (subAdj wb) (subAdj (G.adj_symm va)) (subAdj ab))⟩
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  let active := A.image L ∪ B.image R
  have degree (v) (hv : v ∈ active) : ∃ u, G.Adj v u := by
    rcases Finset.mem_union.mp hv with ha | hb
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨_,(leftRight J _ _).mpr (Finset.mem_filter.mp he).2⟩
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨_,G.adj_symm ((leftRight J _ _).mpr (Finset.mem_filter.mp he).2)⟩
  have edgeExists : ∃ v u, G.Adj v u := by
    obtain ⟨e,he⟩ := nonempty
    exact ⟨L e.1,R e.2,(leftRight J _ _).mpr (Finset.mem_filter.mp he).2⟩
  obtain ⟨S,covered,budget,saturated⟩ := carrierCover ao mono hE active degree noTwins adjacent edgeExists
  let U := Finset.univ.filter fun p : Fin N => L p ∈ S
  let V := Finset.univ.filter fun l : Fin N => R l ∈ S
  refine ⟨U,V,?_,?_,?_⟩
  · intro e he hl hr
    change e.1 ∈ U ∨ e.2 ∈ V
    have two {v a b : Fin (N+N)} (ha : G.Adj v a) (hb : G.Adj v b) (ne : a ≠ b) :
        2 ≤ (G.neighborSet v).ncard := by
      have finite : (G.neighborSet v).Finite := Set.toFinite _
      rw [Set.ncard_eq_toFinset_card _ finite]
      exact Finset.one_lt_card_iff.mpr ⟨a,b,finite.mem_toFinset.mpr ha,finite.mem_toFinset.mpr hb,ne⟩
    obtain ⟨f,hf,fe,off⟩ := hl
    obtain ⟨g,hg,ge,off'⟩ := hr
    have ee := (leftRight J _ _).mpr ((Finset.mem_filter.mp he).2 : J e.1 e.2)
    have ff := (leftRight J _ _).mpr ((Finset.mem_filter.mp hf).2 : J f.1 f.2)
    have gg := (leftRight J _ _).mpr ((Finset.mem_filter.mp hg).2 : J g.1 g.2)
    rw [fe] at ff
    rw [ge] at gg
    exact (covered _ _ ee (two ff ee (fun h => off (rightInjective h)))
      (two (G.adj_symm gg) (G.adj_symm ee) (fun h => off' (leftInjective h)))).imp
      (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  · have disjoint (X Y : Finset (Fin N)) : Disjoint (X.image L) (Y.image R) := by
      rw [Finset.disjoint_left]
      intro v h k
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨l,_,eq⟩ := Finset.mem_image.mp k
      exact sides p l eq.symm
    have activeCount : active.card = A.card+B.card := by
      rw [Finset.card_union_of_disjoint (disjoint A B), Finset.card_image_of_injective _ leftInjective,
        Finset.card_image_of_injective _ rightInjective]
    have less : U.image L ∪ V.image R ⊆ S := by
      intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h; exact (Finset.mem_filter.mp hp).2
      · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h; exact (Finset.mem_filter.mp hl).2
    have hc := Finset.card_le_card less
    rw [Finset.card_union_of_disjoint (disjoint U V), Finset.card_image_of_injective _ leftInjective,
      Finset.card_image_of_injective _ rightInjective] at hc
    change A.card+B.card+U.card+V.card ≤ C.size+1
    omega

  · intro equality e he
    have disjoint (X Y : Finset (Fin N)) : Disjoint (X.image L) (Y.image R) := by
      rw [Finset.disjoint_left]
      intro v h k
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨l,_,eq⟩ := Finset.mem_image.mp k
      exact sides p l eq.symm
    have activeCount : active.card = A.card+B.card := by
      rw [Finset.card_union_of_disjoint (disjoint A B), Finset.card_image_of_injective _ leftInjective,
        Finset.card_image_of_injective _ rightInjective]
    have less : U.image L ∪ V.image R ⊆ S := by
      intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h; exact (Finset.mem_filter.mp hp).2
      · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h; exact (Finset.mem_filter.mp hl).2
    have hc := Finset.card_le_card less
    rw [Finset.card_union_of_disjoint (disjoint U V), Finset.card_image_of_injective _ leftInjective,
      Finset.card_image_of_injective _ rightInjective] at hc
    change A.card+B.card+U.card+V.card=C.size+1 at equality
    have satEq : active.card+S.card=C.size+1 := by omega
    have carrier := saturated satEq
    have hno : ∀ u v a b, u ≠ v → a ≠ b → G.Adj u a → G.Adj u b → G.Adj v a → G.Adj v b → False := by
      intro u v a b huv hab hua hub hva hvb
      exact noFour I uniq u v a b huv hab (subAdj hua) (subAdj hub) (subAdj hva) (subAdj hvb)
    have two {v a b : Fin (N+N)} (ha : G.Adj v a) (hb : G.Adj v b) (hne : a ≠ b) :
        2 ≤ (G.neighborSet v).ncard := by
      have finite : (G.neighborSet v).Finite := Set.toFinite _
      rw [Set.ncard_eq_toFinset_card _ finite]
      exact Finset.one_lt_card_iff.mpr ⟨a,b,finite.mem_toFinset.mpr ha,finite.mem_toFinset.mpr hb,hne⟩
    have ee := (leftRight J _ _).mpr ((Finset.mem_filter.mp he).2 : J e.1 e.2)
    constructor
    · intro hout ⟨f,hf,hfe,hne⟩
      have ff := (leftRight J _ _).mpr ((Finset.mem_filter.mp hf).2 : J f.1 f.2)
      rw [hfe] at ff
      have hd := two ff ee (fun h => hne (rightInjective h))
      have notS : L e.1 ∉ S := fun h => hout (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have none := no_reachable_branch_outside_carriers C G ao mono hE hno S carrier (L e.1) notS hd
      have result := single_part_at_pair C G ao hE (L e.1) (R e.2) ee (fun i => decide (i < N))
        (by simp [L]) (by simp [R]) none
      have inputEq : point {L e.1,R e.2} =
          (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) := by
        funext i; simp [point,L,R]
      rw [inputEq] at result
      exact result
    · intro hout ⟨f,hf,hfe,hne⟩
      have ff := (leftRight J _ _).mpr ((Finset.mem_filter.mp hf).2 : J f.1 f.2)
      rw [hfe] at ff
      have hd := two (G.adj_symm ff) (G.adj_symm ee) (fun h => hne (leftInjective h))
      have notS : R e.2 ∉ S := fun h => hout (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have none := no_reachable_branch_outside_carriers C G ao mono hE hno S carrier (R e.2) notS hd
      have result := single_part_at_pair C G ao hE (R e.2) (L e.1) (G.adj_symm ee) (fun i => decide (N ≤ i))
        (by simp [R]) (by simp [L]) none
      have inputEq : point {R e.2,L e.1} =
          (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) := by
        funext i; simp [point,L,R,or_comm]
      rw [inputEq] at result
      exact result

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port


namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Count
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted
open Classical

lemma low_fiber_card {α β : Type} [DecidableEq α] [DecidableEq β]
    (E : Finset β) (f : β → α) :
    (E.filter fun e => (E.filter fun z => f z=f e).card ≤ 1).card ≤ (E.image f).card := by
  let F := E.filter fun e => (E.filter fun z => f z=f e).card ≤ 1
  have bound : F.card ≤ 1*(F.image f).card := by
    apply fiber_bound
    intro a
    by_cases h : (F.filter fun e => f e=a).Nonempty
    · obtain ⟨e,he⟩ := h
      have heF : e ∈ F := (Finset.mem_filter.mp he).1
      have heq : f e=a := (Finset.mem_filter.mp he).2
      have hd : (E.filter fun z => f z=f e).card ≤ 1 := (Finset.mem_filter.mp heF).2
      have sub : (F.filter fun z => f z=a) ⊆ (E.filter fun z => f z=a) :=
        Finset.filter_subset_filter _ (Finset.filter_subset _ _)
      exact (Finset.card_le_card sub).trans (by simpa only [heq] using hd)
    · simp [Finset.not_nonempty_iff_eq_empty.mp h]
  have sub : F.image f ⊆ E.image f := Finset.image_subset_image (Finset.filter_subset _ _)
  have := Finset.card_le_card sub
  simpa only [Nat.one_mul] using bound.trans (by simpa using this)

lemma selected_fiber_card {α β : Type} [DecidableEq α] [DecidableEq β]
    (E : Finset β) (f : β → α) (U : Finset α) (d : Nat)
    (hd : ∀ a, (E.filter fun e => f e=a).card ≤ d) :
    (E.filter fun e => f e ∈ U).card ≤ d*U.card := by
  let X := E.filter fun e => f e ∈ U
  rw [Finset.card_eq_sum_card_fiberwise (s:=X) (t:=U) (f:=f)
    (fun e he => (Finset.mem_filter.mp he).2)]
  calc
    _ ≤ ∑ a ∈ U, d := Finset.sum_le_sum (fun a _ =>
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans (hd a))
    _ = _ := by simp [Nat.mul_comm]

lemma other_in_fiber {α β : Type} [DecidableEq α] [DecidableEq β]
    (E : Finset β) (f : β → α) (e : β) (h : 1 < (E.filter fun z => f z=f e).card) :
    ∃ z ∈ E, f z=f e ∧ z ≠ e := by
  obtain ⟨a,b,ha,hb,hab⟩ := Finset.one_lt_card_iff.mp h
  obtain ⟨ha,hfa⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb,hfb⟩ := Finset.mem_filter.mp hb
  by_cases he : a=e
  · exact ⟨b,hb,hfb,fun h => hab (he.trans h.symm)⟩
  · exact ⟨a,ha,hfa,he⟩

theorem finish132 {N : Nat} (E : Finset (Fin N × Fin N)) (U V : Finset (Fin N))
    (P L : Finset (Fin N × Fin N)) (s : Nat)
    (hdp : ∀ p, (E.filter fun e => e.1=p).card ≤ 132)
    (hdl : ∀ l, (E.filter fun e => e.2=l).card ≤ 132)
    (hcover : ∀ e ∈ E, (∃ f ∈ E, f.1=e.1 ∧ f.2≠e.2) →
      (∃ f ∈ E, f.2=e.2 ∧ f.1≠e.1) → e.1 ∈ U ∨ e.2 ∈ V)
    (hbudget : (E.image Prod.fst).card+(E.image Prod.snd).card+U.card+V.card ≤ s+1)
    (hp : P.card ≤ 10*s) (hl : L.card ≤ 10*s)
    (hsingle : (E.image Prod.fst).card+(E.image Prod.snd).card+U.card+V.card=s+1 →
      ∀ e ∈ E,
        (e.1 ∉ U → (∃ f ∈ E, f.1=e.1 ∧ f.2≠e.2) → e ∈ P) ∧
        (e.2 ∉ V → (∃ f ∈ E, f.2=e.2 ∧ f.1≠e.1) → e ∈ L)) : E.card ≤ 44*s := by
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  change A.card+B.card+U.card+V.card ≤ s+1 at hbudget
  have product : E.card ≤ A.card*B.card := by
    have sub : E ⊆ A ×ˢ B := fun e he =>
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he,Finset.mem_image_of_mem _ he⟩
    simpa only [Finset.card_product] using Finset.card_le_card sub
  by_cases hsmall : s ≤ 174
  · exact small_budget E.card A.card B.card s hsmall (by omega) product
  by_contra bad
  have hweight := weighted_cover 132 132 (by omega) (by omega) E U V hdp hdl hcover
  norm_num at hweight
  have equality : A.card+B.card+U.card+V.card=s+1 := by
    change 396*E.card ≤ 17424*(A.card+B.card+U.card+V.card) at hweight
    omega
  have singles := hsingle equality
  let Zp := E.filter fun e => (E.filter fun f => f.1=e.1).card ≤ 1
  let Zl := E.filter fun e => (E.filter fun f => f.2=e.2).card ≤ 1
  let Z := Zp ∪ Zl
  let X := E.filter fun e => e.1 ∈ U
  let Y := E.filter fun e => e.2 ∈ V
  let T := X ∩ Y
  have zbound : Z.card ≤ A.card+B.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add (low_fiber_card E Prod.fst) (low_fiber_card E Prod.snd))
  have xbound := selected_fiber_card E Prod.fst U 132 hdp
  have ybound := selected_fiber_card E Prod.snd V 132 hdl
  change X.card ≤ 132*U.card at xbound
  change Y.card ≤ 132*V.card at ybound
  have outside (e : Fin N × Fin N) (he : e ∈ E) (hz : e ∉ Z) :
      (∃ f ∈ E, f.1=e.1 ∧ f.2≠e.2) ∧ (∃ f ∈ E, f.2=e.2 ∧ f.1≠e.1) := by
    have hzp : ¬ (E.filter fun f => f.1=e.1).card ≤ 1 :=
      fun h => hz (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,h⟩))
    have hzl : ¬ (E.filter fun f => f.2=e.2).card ≤ 1 :=
      fun h => hz (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,h⟩))
    obtain ⟨a,ha,haf,hane⟩ := other_in_fiber E Prod.fst e (by omega)
    obtain ⟨b,hb,hbf,hbne⟩ := other_in_fiber E Prod.snd e (by omega)
    exact ⟨⟨a,ha,haf,fun h => hane (Prod.ext haf h)⟩,
      ⟨b,hb,hbf,fun h => hbne (Prod.ext h hbf)⟩⟩
  have coverXYZ : E ⊆ (X ∪ Y) ∪ Z := by
    intro e he
    by_cases hz : e ∈ Z
    · exact Finset.mem_union_right _ hz
    have other := outside e he hz
    rcases hcover e he other.1 other.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,h⟩))
  have cross : E.card+T.card ≤ X.card+Y.card+Z.card := by
    have le := (Finset.card_le_card coverXYZ).trans (Finset.card_union_le _ _)
    have eq := Finset.card_union_add_card_inter X Y
    change (X ∪ Y).card + T.card = X.card+Y.card at eq
    omega
  have incidenceP := fiber_bound E Prod.fst 132 hdp
  have incidenceL := fiber_bound E Prod.snd 132 hdl
  have triple : 3*E.card+T.card ≤ 132*(s+1)+Z.card := by
    change E.card ≤ 132*A.card at incidenceP
    change E.card ≤ 132*B.card at incidenceL
    omega
  have rest : E ⊆ ((P ∪ L) ∪ T) ∪ Z := by
    intro e he
    by_cases hz : e ∈ Z
    · exact Finset.mem_union_right _ hz
    have other := outside e he hz
    by_cases hpu : e.1 ∈ U
    · by_cases hlv : e.2 ∈ V
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨he,hpu⟩,Finset.mem_filter.mpr ⟨he,hlv⟩⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ((singles e he).2 hlv other.2)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ((singles e he).1 hpu other.1)))
  have total : E.card ≤ P.card+L.card+T.card+Z.card := by
    exact (Finset.card_le_card rest).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
  omega

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Count
namespace PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Final
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Port
open PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Bounds
open Classical

lemma public_parts_eq (C : Circuit) (marked : Nat → Bool) (x : List Bool) :
    ReadK.linearParts C marked x =
      PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Parts.linearParts C marked x := by
  unfold ReadK.linearParts PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Parts.linearParts
  congr 1
  funext w g
  cases g.op <;> rfl

lemma pair_input {N : Nat} (p l : Fin N) :
    List.ofFn (fun i : Fin (N+N) => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) =
      (List.range (N+N)).map (fun i => i == p.val || i == N+l.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    apply Bool.eq_iff_iff.mpr
    simp [Fin.ext_iff,Nat.add_comm]

lemma single_eq_parts {N : Nat} (C : Circuit) (marked : Nat → Bool) (p l : Fin N) :
    ReadK.lineSingle C (N+N) marked p.val (N+l.val) =
      (parts C marked (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) C.output).2 := by
  unfold ReadK.lineSingle parts
  rw [public_parts_eq,← pair_input]

theorem degree132 (q N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 2 ≤ q) (hN : N=q^2+q+1)
    (hcol : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hu : ∀ p r, p≠r → ∃! l : Fin N, I p l ∧ I r l)
    (hao : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hs : ∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l)=true} ≤ q →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) →
      circuitFun (N+N) C z=false) :
    let E := Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ circuitFun (N+N) C
        (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true)
    (∀ p, (E.filter fun e => e.1=p).card ≤ 132) →
    (∀ l, (E.filter fun e => e.2=l).card ≤ 132) → E.card ≤ 44*C.size := by
  classical
  dsimp only
  let E := Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ circuitFun (N+N) C
        (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true)
  change (∀ p, (E.filter fun e => e.1=p).card ≤ 132) →
    (∀ l, (E.filter fun e => e.2=l).card ≤ 132) → E.card ≤ 44*C.size
  intro hdp hdl
  by_cases empty : E=∅
  · simp [empty]
  have hm : Monotone2 C := by
    intro g hg
    exact ⟨hao.1 g hg, Nat.le_of_eq (hao.2.2 g hg)⟩
  have hs2 : ∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l)=true} ≤ 2 →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) →
      circuitFun (N+N) C z=false := fun z hz hn => hs z (hz.trans hq) hn
  obtain ⟨U,V,hcover,hbudget,hsingle⟩ := incidenceCarrierCover N I C hm hao hu hs2
    (Finset.nonempty_iff_ne_empty.mpr empty)
  let P := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ ReadK.lineSingle C (N+N) (fun i => decide (i<N)) e.1.val (N+e.2.val)=true)
  let L := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ ReadK.lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val)=true)
  have hp : P.card ≤ 10*C.size := by
    simpa only [P,Fintype.card_subtype] using PointBound q N I C hq hN hcol hu hao hs
  have hl : L.card ≤ 10*C.size := by
    have noFour : ∀ a b l k : Fin N, a≠b → l≠k → ¬ (I a l ∧ I b l ∧ I a k ∧ I b k) := by
      intro a b l k hab hlk h
      exact hlk ((hu a b hab).unique ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2⟩)
    have hs1 : ∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l)=true} ≤ 1 →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) →
      circuitFun (N+N) C z=false := fun z hz hn => hs2 z (by omega) hn
    simpa only [L,Fintype.card_subtype] using LineBound N I C noFour hao hs1
  apply PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Count.finish132 E U V P L C.size hdp hdl hcover hbudget hp hl
  intro equality e he
  have single := hsingle equality e he
  have inc := ((Finset.mem_filter.mp he).2).1
  constructor
  · intro hout hother
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,inc,(single_eq_parts C _ e.1 e.2).trans (single.1 hout hother)⟩
  · intro hout hother
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,inc,(single_eq_parts C _ e.1 e.2).trans (single.2 hout hother)⟩

end PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Final
theorem PEqualNP.Outside.L_meta_3291_expanded_degrees : ∀ (q N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hq : 2 ≤ q) (hN : N=q^2+q+1)
    (hcol : ∀ l, Fintype.card {p : Fin N // I p l}=q+1)
    (hu : ∀ p r, p≠r → ∃! l : Fin N, I p l ∧ I r l)
    (hao : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hs : ∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l)=true} ≤ q →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z=false),
    let E := Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
        (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true)
    (∃ a b : Nat, 2 ≤ a ∧ 2 ≤ b ∧
      (a ≤ 44 ∨ b ≤ 44 ∨ (a ≤ 132 ∧ b ≤ 132) ∨ 4*(a*b) ≤ 175*(a+b+min a b)) ∧
      (∀ p, (E.filter fun e => e.1=p).card ≤ a) ∧
      (∀ l, (E.filter fun e => e.2=l).card ≤ b)) → E.card ≤ 44*C.size := by
  intro q N I inst C hq hN hcol hu hao hs
  dsimp only
  intro hgood
  obtain ⟨a,b,ha,hb,hcase,hdp,hdl⟩ := hgood
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    exact ⟨hao.1 g hg,Nat.le_of_eq (hao.2.2 g hg)⟩
  have hs2 : ∀ z : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l)=true} ≤ 2 →
      (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p)=true ∧ z (Fin.natAdd N l)=true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z=false := fun z hz hn => hs z (hz.trans hq) hn
  let E := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
      (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2))=true)
  change E.card ≤ 44*C.size
  change ∀ p, (E.filter fun e => e.1=p).card ≤ a at hdp
  change ∀ l, (E.filter fun e => e.2=l).card ≤ b at hdl
  rcases hcase with hp44 | hl44 | h132 | hweight
  · obtain ⟨U,V,_,hbudget⟩ := PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted.incidenceCover N I C hm hu hs2
    change (E.image Prod.fst).card+(E.image Prod.snd).card+U.card+V.card ≤ C.size+1 at hbudget
    apply PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted.one_sided_budget E 44 C.size (by omega)
    exact Or.inl (fun p => (hdp p).trans hp44)
  · obtain ⟨U,V,_,hbudget⟩ := PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted.incidenceCover N I C hm hu hs2
    change (E.image Prod.fst).card+(E.image Prod.snd).card+U.card+V.card ≤ C.size+1 at hbudget
    apply PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted.one_sided_budget E 44 C.size (by omega)
    exact Or.inr (fun l => (hdl l).trans hl44)
  · exact PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Final.degree132 q N I C hq hN hcol hu hao hs
      (fun p => (hdp p).trans h132.1) (fun l => (hdl l).trans h132.2)
  · exact PEqualNP.Outside.L_meta_3291_expanded_degrees_aux.Weighted.weighted_degree_bound N I C hm hu hs2 a b ha hb hweight hdp hdl
