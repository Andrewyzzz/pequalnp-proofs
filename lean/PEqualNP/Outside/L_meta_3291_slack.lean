import Mathlib.Tactic
import PEqualNP.Outside.L_meta_3291_sharp_degrees
namespace PEqualNP.Outside.L_meta_3291_slack_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3291_sharp_degrees_aux.Weighted
open PEqualNP.Outside.L_meta_3291_sharp_degrees_aux.Port
open PEqualNP.Outside.L_meta_3291_sharp_degrees_aux.Ownership
open Relation Classical
theorem carrierCoverWithSlack {n : Nat} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hm : PEqualNP.TopForm.IsAO2 n C) (hC : Monotone2 C) (hE : GraphEval C G)
    (active : Finset (Fin n)) (hdegree : ∀ v ∈ active, ∃ u, G.Adj v u)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ u, ¬ (G.Adj v u ↔ G.Adj w u))
    (hadj : ∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ a b, G.Adj v a ∧ a ≠ w ∧
      G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b))
    (nonempty : ∃ v u, G.Adj v u) :
    ∃ (S : Finset (Fin n)) (X : Finset Nat),
      (∀ u v, G.Adj u v → 2 ≤ (G.neighborSet u).ncard →
          2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) ∧
      active.card + S.card + X.card ≤ C.size+1 ∧
      (∀ b ∈ X, Live n C b ∧ PortBranch n C b) ∧
      (∀ b, Live n C b → PortBranch n C b → b ∉ X → ∃ u ∈ S, Carries C u b) := by
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
  let X := B \ S.image f
  have sub : S.image f ⊆ B := by
    intro b hb
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hb
    exact maps u hu
  have cardpart := Finset.card_sdiff_add_card_eq_card sub
  rw [Finset.card_image_iff.mpr inj] at cardpart
  have fullbudget : active.card + S.card + X.card ≤ C.size+1 := by
    change active.card+B.card ≤ C.size+1 at budget
    change X.card+S.card=B.card at cardpart
    omega
  refine ⟨S,X,covers,fullbudget,?_,?_⟩
  · intro b hb
    have hB := (Finset.mem_sdiff.mp hb).1
    exact ⟨(mem_living.mp (Finset.mem_filter.mp hB).1).2,(Finset.mem_filter.mp hB).2⟩
  · intro b hb hbranch hX
    have hbB : b ∈ B := Finset.mem_filter.mpr ⟨mem_living.mpr ⟨(next_le hb).trans_lt ho,hb⟩,hbranch⟩
    have himage : b ∈ S.image f := by
      by_contra hn
      exact hX (Finset.mem_sdiff.mpr ⟨hbB,hn⟩)
    obtain ⟨u,hu,hfu⟩ := Finset.mem_image.mp himage
    have eligible := ((hS u).mp hu).2
    refine ⟨u,hu,?_⟩
    rw [hf u eligible] at hfu
    exact hfu ▸ (firstBranch_spec u eligible).2.1

lemma reachable_unowned_branch {n : Nat} (C : Circuit) (G : SimpleGraph (Fin n))
    (hm : PEqualNP.TopForm.IsAO2 n C) (hmono : Monotone2 C) (he : GraphEval C G)
    (hno : ∀ u v a b, u ≠ v → a ≠ b → G.Adj u a → G.Adj u b → G.Adj v a → G.Adj v b → False)
    (S : Finset (Fin n)) (X : Finset Nat)
    (covered : ∀ b, Live n C b → PortBranch n C b → b ∉ X → ∃ u ∈ S, Carries C u b)
    (v : Fin n) (hv : v ∉ S) (hd : 2 ≤ (G.neighborSet v).ncard)
    (existsBranch : ∃ b, ReflTransGen (Next n C) v.val b ∧ Live n C b ∧ PortBranch n C b) :
    ∃ b ∈ X, ReflTransGen (Next n C) v.val b ∧ Live n C b ∧ PortBranch n C b := by
  let first := Nat.find existsBranch
  have hs : ReflTransGen (Next n C) v.val first ∧ Live n C first ∧ PortBranch n C first := Nat.find_spec existsBranch
  have unique : ∀ a j j', a < first → ReflTransGen (Next n C) v.val a →
      LNext n C a j → LNext n C a j' → j=j' := by
    intro a j j' ha hreach hj hj'
    apply nonport_unique C hm _ hj hj'
    intro hbranch
    exact Nat.find_min existsBranch ha ⟨hreach,live_before hj.1 hj.2,hbranch⟩
  have inX : first ∈ X := by
    by_contra hn
    obtain ⟨u,hu,hcarry⟩ := covered first hs.2.1 hs.2.2 hn
    have same := carrier_must_be_input C G hmono he hno v u first _ hd
      (reach_trace hs.1 hs.2.1) unique hs.2.1 hcarry
    exact hv (same ▸ hu)
  exact ⟨first,inX,hs⟩

lemma nonsingle_reaches_unowned {n : Nat} (C : Circuit) (G : SimpleGraph (Fin n))
    (hm : PEqualNP.TopForm.IsAO2 n C) (hmono : Monotone2 C) (he : GraphEval C G)
    (hno : ∀ u v a b, u ≠ v → a ≠ b → G.Adj u a → G.Adj u b → G.Adj v a → G.Adj v b → False)
    (S : Finset (Fin n)) (X : Finset Nat)
    (covered : ∀ b, Live n C b → PortBranch n C b → b ∉ X → ∃ u ∈ S, Carries C u b)
    (v w : Fin n) (hv : v ∉ S) (hd : 2 ≤ (G.neighborSet v).ncard) (edge : G.Adj v w)
    (marked : Nat → Bool) (mv : marked v.val=true) (mw : marked w.val=false)
    (bad : (parts C marked (point {v,w}) C.output).2 ≠ true) :
    ∃ b ∈ X, ReflTransGen (Next n C) v.val b ∧ Live n C b ∧ PortBranch n C b := by
  apply reachable_unowned_branch C G hm hmono he hno S X covered v hv hd
  by_contra hn
  apply bad
  apply single_part_at_pair C G hm he v w edge marked mv mw
  intro b reach live branch
  exact hn ⟨b,reach,live,branch⟩


theorem incidenceCarrierCoverWithSlack : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
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
      E.Nonempty → ∃ (U V : Finset (Fin N)) (X : Finset Nat), (∀ e ∈ E, (∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2) →
          (∃ g ∈ E, g.2 = e.2 ∧ g.1 ≠ e.1) → e.1 ∈ U ∨ e.2 ∈ V) ∧
        A.card+B.card+U.card+V.card+X.card ≤ C.size+1 ∧
        (∀ b ∈ X, Live (N+N) C b ∧ PortBranch (N+N) C b) ∧
        (∀ e ∈ E,
          (e.1 ∉ U → (∃ f ∈ E, f.1=e.1 ∧ f.2≠e.2) →
            (parts C (fun i => decide (i < N))
              (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) C.output).2≠true →
            ∃ b ∈ X, ReflTransGen (Next (N+N) C) e.1.val b) ∧
          (e.2 ∉ V → (∃ f ∈ E, f.2=e.2 ∧ f.1≠e.1) →
            (parts C (fun i => decide (N ≤ i))
              (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) C.output).2≠true →
            ∃ b ∈ X, ReflTransGen (Next (N+N) C) (N+e.2.val) b)) := by
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
  obtain ⟨S,X,covered,budget,hX,carrier⟩ := carrierCoverWithSlack ao mono hE active degree noTwins adjacent edgeExists
  let U := Finset.univ.filter fun p : Fin N => L p ∈ S
  let V := Finset.univ.filter fun l : Fin N => R l ∈ S
  refine ⟨U,V,X,?_,?_,hX,?_⟩
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
    change A.card+B.card+U.card+V.card+X.card ≤ C.size+1
    omega

  · intro e he
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
    · intro hout ⟨f,hf,hfe,hne⟩ bad
      have ff := (leftRight J _ _).mpr ((Finset.mem_filter.mp hf).2 : J f.1 f.2)
      rw [hfe] at ff
      have hd := two ff ee (fun h => hne (rightInjective h))
      have notS : L e.1 ∉ S := fun h => hout (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have inputEq : point {L e.1,R e.2} =
          (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) := by
        funext i; simp [point,L,R]
      have hbad : (parts C (fun i => decide (i < N)) (point {L e.1,R e.2}) C.output).2≠true := by
        rw [inputEq]
        exact bad
      obtain ⟨b,hb,reach,_⟩ := nonsingle_reaches_unowned C G ao mono hE hno S X carrier
        (L e.1) (R e.2) notS hd ee (fun i => decide (i < N)) (by simp [L]) (by simp [R]) hbad
      exact ⟨b,hb,reach⟩
    · intro hout ⟨f,hf,hfe,hne⟩ bad
      have ff := (leftRight J _ _).mpr ((Finset.mem_filter.mp hf).2 : J f.1 f.2)
      rw [hfe] at ff
      have hd := two (G.adj_symm ff) (G.adj_symm ee) (fun h => hne (leftInjective h))
      have notS : R e.2 ∉ S := fun h => hout (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have inputEq : point {R e.2,L e.1} =
          (fun i => decide (i=Fin.castAdd N e.1 ∨ i=Fin.natAdd N e.2)) := by
        funext i; simp [point,L,R,or_comm]
      have hbad : (parts C (fun i => decide (N ≤ i)) (point {R e.2,L e.1}) C.output).2≠true := by
        rw [inputEq]
        exact bad
      obtain ⟨b,hb,reach,_⟩ := nonsingle_reaches_unowned C G ao mono hE hno S X carrier
        (R e.2) (L e.1) notS hd (G.adj_symm ee) (fun i => decide (N ≤ i)) (by simp [R]) (by simp [L]) hbad
      exact ⟨b,hb,reach⟩

end PEqualNP.Outside.L_meta_3291_slack_aux
