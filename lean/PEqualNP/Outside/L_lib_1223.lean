import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1223_aux

open scoped Classical

abbrev Word (n : Nat) := Fin n → Bool
abbrev Table (n : Nat) := Word n → Bool

/-! ### Part 0: Mod-2 arithmetic and counting helpers -/

lemma sum_mod_two {ι : Type*} (s : Finset ι) (f : ι → Nat) :
    (∑ i ∈ s, f i) % 2 = (∑ i ∈ s, f i % 2) % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.add_mod, ih]
    simp [Nat.add_mod]

lemma mul_mod_two (a b : Nat) : (a * b) % 2 = ((a % 2) * (b % 2)) % 2 := by
  rw [Nat.mul_mod]

lemma prod_mod_two {ι : Type*} (s : Finset ι) (f : ι → Nat) :
    (∏ i ∈ s, f i) % 2 = (∏ i ∈ s, f i % 2) % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.mul_mod, ih]
    simp [Nat.mul_mod]

lemma if_decide_mod_two (x : Nat) :
    (if decide (x % 2 = 1) then (1 : Nat) else 0) = x % 2 := by
  have h : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases h with h0 | h0 <;> simp [h0]

lemma ite_nat_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1 : Nat) else 0) = (if Q then 1 else 0) := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

/-! ### Part 1: Upper bound (2^n bits one-way communication) -/

def isCountFin {N : Nat} (G : Fin N → Finset (Fin N)) (live : Fin N → Bool) : Nat :=
  ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
    (∀ u ∈ I, live u = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card

def countBoolFn : (m : Nat) → ((Fin m → Bool) → Bool) → Nat
  | 0, P => if P Fin.elim0 then 1 else 0
  | m + 1, P =>
    countBoolFn m (fun f => P (Fin.cons false f)) +
    countBoolFn m (fun f => P (Fin.cons true f))

lemma countBoolFn_eq_card : ∀ (m : Nat) (P : (Fin m → Bool) → Bool),
    countBoolFn m P = ((Finset.univ : Finset (Fin m → Bool)).filter (fun f => P f = true)).card
  | 0, P => by
    have huniv : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      ext f
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim f Fin.elim0
    simp only [countBoolFn, huniv, Finset.filter_singleton]
    cases h : P Fin.elim0 <;> simp
  | m + 1, P => by
    simp only [countBoolFn]
    rw [countBoolFn_eq_card m (fun f => P (Fin.cons false f)),
        countBoolFn_eq_card m (fun f => P (Fin.cons true f))]
    let e : (Fin (m + 1) → Bool) ≃ Bool × (Fin m → Bool) :=
      { toFun := fun f => (f 0, fun i => f i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun f => by ext i; refine Fin.cases ?_ ?_ i <;> simp
        right_inv := fun ⟨b, f⟩ => by ext <;> simp }
    have hsplit :
        ((Finset.univ : Finset (Fin (m + 1) → Bool)).filter (fun f => P f = true)).card =
        ((Finset.univ : Finset (Bool × (Fin m → Bool))).filter (fun p => P (Fin.cons p.1 p.2) = true)).card := by
      refine Finset.card_bij (fun f _ => e f) ?_ ?_ ?_
      · intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
        have : Fin.cons (e f).1 (e f).2 = f := e.left_inv f
        rw [this]; exact hf
      · intro f1 _ f2 _ h; exact e.injective h
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        refine ⟨e.symm p, ?_, e.right_inv p⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hp
    rw [hsplit]
    have hpair :
        ((Finset.univ : Finset (Bool × (Fin m → Bool))).filter (fun p => P (Fin.cons p.1 p.2) = true)) =
        (((Finset.univ : Finset (Fin m → Bool)).filter (fun f => P (Fin.cons false f) = true)).image (Prod.mk false)) ∪
        (((Finset.univ : Finset (Fin m → Bool)).filter (fun f => P (Fin.cons true f) = true)).image (Prod.mk true)) := by
      ext ⟨b, f⟩
      cases b <;> simp
    rw [hpair, Finset.card_union_of_disjoint,
        Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
        Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_image] at hp1 hp2
    rcases hp1 with ⟨_, _, rfl⟩
    rcases hp2 with ⟨_, _, h⟩
    exact Bool.noConfusion (Prod.mk.inj h).1

structure Gadget (r s d : Nat) where
  edges : List (Fin (r + d) × Fin (r + d))
  shore : Fin (r + d) → Bool
  tagKind : Fin d → Option Bool

def gadgetNbrs {r s d : Nat} (g : Gadget r s d) (v : Fin (r + d)) : Finset (Fin (r + d)) :=
  Finset.univ.filter (fun w => g.edges.any (fun e => (e.1 == v && e.2 == w) || (e.1 == w && e.2 == v)))

lemma gadgetNbrs_symm {r s d : Nat} (g : Gadget r s d) (v w : Fin (r + d)) :
    w ∈ gadgetNbrs g v ↔ v ∈ gadgetNbrs g w := by
  simp only [gadgetNbrs, Finset.mem_filter, Finset.mem_univ, true_and, List.any_eq_true,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor <;> rintro ⟨e, he, h | h⟩
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩

structure ValidGadget {r s d : Nat} (g : Gadget r s d) : Prop where
  hs : s ≤ d
  no_loop : ∀ v, v ∉ gadgetNbrs g v
  no_in_edge : ∀ v w, w ∈ gadgetNbrs g v → ¬(v.val < r ∧ w.val < r)
  bip : ∀ v w, w ∈ gadgetNbrs g v → g.shore v ≠ g.shore w
  port_shore : ∀ v : Fin (r + d), v.val < r + s → g.shore v = false
  port_deg : ∀ v : Fin (r + d), v.val < r + s → (gadgetNbrs g v).card ≤ 1
  all_deg : ∀ v : Fin (r + d), (gadgetNbrs g v).card ≤ 3
  out_tag : ∀ k : Fin d, k.val < s → g.tagKind k = none

def gadgetAssign {r s d : Nat} (hs : s ≤ d)
    (inp : Fin r → Bool) (out : Fin s → Bool) (z : Fin (d - s) → Bool)
    (v : Fin (r + d)) : Bool :=
  if h1 : v.val < r then inp ⟨v.val, h1⟩
  else if h2 : v.val - r < s then out ⟨v.val - r, h2⟩
  else z ⟨v.val - r - s, by omega⟩

def gadgetValidB {r s d : Nat} (g : Gadget r s d) (hs : s ≤ d)
    (val : Bool) (inp : Fin r → Bool) (out : Fin s → Bool) (z : Fin (d - s) → Bool) : Bool :=
  let a := gadgetAssign hs inp out z
  let liveOk := (List.finRange d).all (fun k =>
    if a ⟨r + k.val, by omega⟩ then
      (g.tagKind k).elim true (fun b => decide (val = b))
    else true)
  let edgeOk := g.edges.all (fun e => !(a e.1 && a e.2))
  liveOk && edgeOk

def gadgetCnt {r s d : Nat} (g : Gadget r s d) (hs : s ≤ d)
    (val : Bool) (inp : Fin r → Bool) (out : Fin s → Bool) : Nat :=
  countBoolFn (d - s) (gadgetValidB g hs val inp out)

def gConst0 : Gadget 0 1 3 :=
  { edges := [(0, 1), (1, 2)]
    shore := ![false, true, false]
    tagKind := ![none, none, none] }

def gConst1 : Gadget 0 1 2 :=
  { edges := [(0, 1)]
    shore := ![false, true]
    tagKind := ![none, none] }

def gPin1 : Gadget 1 0 1 :=
  { edges := [(0, 1)]
    shore := ![false, true]
    tagKind := ![none] }

def gConstTag : Gadget 0 1 7 :=
  { edges := [(0, 1), (1, 2), (2, 3), (3, 4), (3, 5), (5, 6)]
    shore := ![false, true, false, true, false, false, true]
    tagKind := ![none, none, none, none, some true, none, some false] }

def gNot : Gadget 1 1 7 :=
  { edges := [(0, 4), (1, 3), (2, 6), (2, 7), (3, 5), (3, 7), (4, 5), (4, 6)]
    shore := ![false, false, true, true, true, false, false, false]
    tagKind := ![none, none, none, none, none, none, none] }

def gOr : Gadget 2 1 6 :=
  { edges := [(0, 3), (1, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 2)]
    shore := ![false, false, false, true, false, true, false, true]
    tagKind := ![none, none, none, none, none, none] }

def gAnd : Gadget 2 1 7 :=
  { edges := [(0, 3), (1, 4), (3, 5), (4, 5), (5, 6), (6, 7), (7, 8), (8, 2)]
    shore := ![false, false, false, true, true, false, true, false, true]
    tagKind := ![none, none, none, none, none, none, none] }

def gCopy : Gadget 1 2 9 :=
  { edges := [(0, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 1), (5, 8), (8, 9), (9, 2)]
    shore := ![false, false, false, true, false, true, false, true, false, true]
    tagKind := ![none, none, none, none, none, none, none, none, none] }

lemma valid_gConst0 : ValidGadget gConst0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma valid_gConst1 : ValidGadget gConst1 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma valid_gPin1 : ValidGadget gPin1 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma valid_gConstTag : ValidGadget gConstTag :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma valid_gNot : ValidGadget gNot :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma valid_gOr : ValidGadget gOr :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma valid_gAnd : ValidGadget gAnd :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma valid_gCopy : ValidGadget gCopy :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

lemma cnt_gConst0 : ∀ (val : Bool) (inp : Fin 0 → Bool) (out : Fin 1 → Bool),
    gadgetCnt gConst0 valid_gConst0.hs val inp out % 2 = if out 0 = false then 1 else 0 := by
  decide

lemma cnt_gConst1 : ∀ (val : Bool) (inp : Fin 0 → Bool) (out : Fin 1 → Bool),
    gadgetCnt gConst1 valid_gConst1.hs val inp out % 2 = if out 0 = true then 1 else 0 := by
  decide

lemma cnt_gPin1 : ∀ (val : Bool) (inp : Fin 1 → Bool) (out : Fin 0 → Bool),
    gadgetCnt gPin1 valid_gPin1.hs val inp out % 2 = if inp 0 = true then 1 else 0 := by
  decide

lemma cnt_gConstTag : ∀ (val : Bool) (inp : Fin 0 → Bool) (out : Fin 1 → Bool),
    gadgetCnt gConstTag valid_gConstTag.hs val inp out % 2 = if out 0 = val then 1 else 0 := by
  decide

lemma cnt_gNot : ∀ (val : Bool) (inp : Fin 1 → Bool) (out : Fin 1 → Bool),
    gadgetCnt gNot valid_gNot.hs val inp out % 2 = if out 0 = !inp 0 then 1 else 0 := by
  decide

lemma cnt_gOr : ∀ (val : Bool) (inp : Fin 2 → Bool) (out : Fin 1 → Bool),
    gadgetCnt gOr valid_gOr.hs val inp out % 2 = if out 0 = (inp 0 || inp 1) then 1 else 0 := by
  decide

lemma cnt_gAnd : ∀ (val : Bool) (inp : Fin 2 → Bool) (out : Fin 1 → Bool),
    gadgetCnt gAnd valid_gAnd.hs val inp out % 2 = if out 0 = (inp 0 && inp 1) then 1 else 0 := by
  decide

lemma cnt_gCopy : ∀ (val : Bool) (inp : Fin 1 → Bool) (out : Fin 2 → Bool),
    gadgetCnt gCopy valid_gCopy.hs val inp out % 2 =
      if out 0 = inp 0 ∧ out 1 = inp 0 then 1 else 0 := by
  decide

/-! ### Part 3: Incremental Nat-indexed graph state, bags, and Master Gluing Lemma -/

structure State (n : Nat) where
  nv : Nat
  adj : Nat → Finset Nat
  shore : Nat → Bool
  tag : Nat → Option (Word n × Bool)
  bags : List (Finset Nat)

def liveOf {n : Nat} (st : State n) (f : Table n) (u : Nat) : Bool :=
  (st.tag u).elim true (fun p => decide (f p.1 = p.2))

def isSets {n : Nat} (st : State n) (f : Table n) (A : Finset Nat) (σ : Nat → Bool) :
    Finset (Finset Nat) :=
  (Finset.range st.nv).powerset.filter (fun I =>
    (∀ u ∈ I, liveOf st f u = true) ∧
    (∀ u ∈ I, ∀ v ∈ st.adj u, v ∉ I) ∧
    (∀ u ∈ A, decide (u ∈ I) = σ u))

def cnt {n : Nat} (st : State n) (f : Table n) (A : Finset Nat) (σ : Nat → Bool) : Nat :=
  (isSets st f A σ).card

def BagsRI (bags : List (Finset Nat)) : Prop :=
  ∀ u i j k, i ≤ j → j ≤ k →
    (hi : i < bags.length) → (hj : j < bags.length) → (hk : k < bags.length) →
    u ∈ bags[i] → u ∈ bags[k] → u ∈ bags[j]

lemma bags_append_two (bags : List (Finset Nat)) (nv d W : Nat)
    (cur B1 B2 : Finset Nat)
    (hne : bags ≠ [])
    (hlast : bags.getLast hne = cur)
    (hsub : ∀ B ∈ bags, B ⊆ Finset.range nv)
    (hcard : ∀ B ∈ bags, B.card ≤ W)
    (hri : BagsRI bags)
    (hcurB1 : cur ⊆ B1)
    (hB1sub : B1 ⊆ cur ∪ (Finset.range (nv + d) \ Finset.range nv))
    (hB2B1 : B2 ⊆ B1)
    (hB1card : B1.card ≤ W) :
    let bags' := bags ++ [B1, B2]
    ∃ hne' : bags' ≠ [],
      bags'.head hne' = bags.head hne ∧
      bags'.getLast hne' = B2 ∧
      (∀ B ∈ bags', B ⊆ Finset.range (nv + d)) ∧
      (∀ B ∈ bags', B.card ≤ W) ∧
      BagsRI bags' := by
  intro bags'
  have hne' : bags' ≠ [] := by simp [bags']
  refine ⟨hne', ?_, ?_, ?_, ?_, ?_⟩
  · simp [bags', List.head_append_of_ne_nil hne]
  · simp [bags']
  · intro B hB
    simp only [bags', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hB
    have hcurSub : cur ⊆ Finset.range nv := by
      rw [← hlast]; exact hsub _ (List.getLast_mem hne)
    have hrg : Finset.range nv ⊆ Finset.range (nv + d) := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    rcases hB with hB | rfl | rfl
    · exact Finset.Subset.trans (hsub B hB) hrg
    · intro x hx
      rcases Finset.mem_union.mp (hB1sub hx) with hx1 | hx2
      · exact hrg (hcurSub hx1)
      · exact (Finset.mem_sdiff.mp hx2).1
    · intro x hx
      rcases Finset.mem_union.mp (hB1sub (hB2B1 hx)) with hx1 | hx2
      · exact hrg (hcurSub hx1)
      · exact (Finset.mem_sdiff.mp hx2).1
  · intro B hB
    simp only [bags', List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with hB | rfl | rfl
    · exact hcard B hB
    · exact hB1card
    · exact le_trans (Finset.card_le_card hB2B1) hB1card
  · intro u i j k hij hjk hi hj hk hui huk
    have hlen : bags'.length = bags.length + 2 := by simp [bags']
    have hLpos : 0 < bags.length := List.length_pos_of_ne_nil hne
    by_cases hkL : k < bags.length
    · have hiL : i < bags.length := by omega
      have hjL : j < bags.length := by omega
      have h1 : bags'[i] = bags[i] := List.getElem_append_left hiL
      have h2 : bags'[j] = bags[j] := List.getElem_append_left hjL
      have h3 : bags'[k] = bags[k] := List.getElem_append_left hkL
      rw [h1] at hui; rw [h3] at huk; rw [h2]
      exact hri u i j k hij hjk hiL hjL hkL hui huk
    · by_cases hiL : i < bags.length
      · have h1 : bags'[i] = bags[i] := List.getElem_append_left hiL
        rw [h1] at hui
        have hu_old : u ∈ Finset.range nv := hsub _ (List.getElem_mem hiL) hui
        have huB1 : u ∈ B1 := by
          have hkcases : k = bags.length ∨ k = bags.length + 1 := by omega
          rcases hkcases with rfl | rfl
          · have h3 : bags'[bags.length] = B1 := by simp [bags']
            rw [h3] at huk; exact huk
          · have h3 : bags'[bags.length + 1] = B2 := by simp [bags']
            rw [h3] at huk; exact hB2B1 huk
        have hu_cur : u ∈ cur := by
          rcases Finset.mem_union.mp (hB1sub huB1) with h | h
          · exact h
          · exact False.elim ((Finset.mem_sdiff.mp h).2 hu_old)
        by_cases hjL : j < bags.length
        · have h2 : bags'[j] = bags[j] := List.getElem_append_left hjL
          rw [h2]
          have hlast_eq : bags[bags.length - 1] = cur := by
            rw [← List.getLast_eq_getElem hne]; exact hlast
          refine hri u i j (bags.length - 1) hij (by omega) hiL hjL (by omega) hui ?_
          rw [hlast_eq]; exact hu_cur
        · have hjcases : j = bags.length ∨ j = bags.length + 1 := by omega
          rcases hjcases with rfl | rfl
          · have h2 : bags'[bags.length] = B1 := by simp [bags']
            rw [h2]; exact huB1
          · have hjk_eq : bags.length + 1 = k := by omega
            subst hjk_eq; exact huk
      · have hij_or : j = i ∨ j = k := by omega
        rcases hij_or with rfl | rfl
        · exact hui
        · exact huk

lemma bags_append_list (bags1 bags2 : List (Finset Nat)) (V1 V2 S : Finset Nat)
    (hne1 : bags1 ≠ []) (hne2 : bags2 ≠ [])
    (hlast1 : bags1.getLast hne1 = S) (hhead2 : bags2.head hne2 = S)
    (hsub1 : ∀ B ∈ bags1, B ⊆ V1) (hsub2 : ∀ B ∈ bags2, B ⊆ V2)
    (hinter : ∀ u, u ∈ V1 → u ∈ V2 → u ∈ S)
    (hri1 : BagsRI bags1) (hri2 : BagsRI bags2) :
    BagsRI (bags1 ++ bags2) := by
  intro u i j k hij hjk hi hj hk hui huk
  have hL1pos : 0 < bags1.length := List.length_pos_of_ne_nil hne1
  have hL2pos : 0 < bags2.length := List.length_pos_of_ne_nil hne2
  by_cases hk1 : k < bags1.length
  · have hi1 : i < bags1.length := by omega
    have hj1 : j < bags1.length := by omega
    rw [List.getElem_append_left hi1] at hui
    rw [List.getElem_append_left hk1] at huk
    rw [List.getElem_append_left hj1]
    exact hri1 u i j k hij hjk hi1 hj1 hk1 hui huk
  · by_cases hi1 : i < bags1.length
    · rw [List.getElem_append_left hi1] at hui
      have hk2 : k - bags1.length < bags2.length := by
        simp only [List.length_append] at hk; omega
      rw [List.getElem_append_right (by omega)] at huk
      have huV1 : u ∈ V1 := hsub1 _ (List.getElem_mem hi1) hui
      have huV2 : u ∈ V2 := hsub2 _ (List.getElem_mem hk2) huk
      have huS : u ∈ S := hinter u huV1 huV2
      by_cases hj1 : j < bags1.length
      · rw [List.getElem_append_left hj1]
        have hlast_eq : bags1[bags1.length - 1] = S := by
          rw [← List.getLast_eq_getElem hne1]; exact hlast1
        refine hri1 u i j (bags1.length - 1) hij (by omega) hi1 hj1 (by omega) hui ?_
        rw [hlast_eq]; exact huS
      · have hj2 : j - bags1.length < bags2.length := by
          simp only [List.length_append] at hj; omega
        rw [List.getElem_append_right (by omega)]
        have hhead_eq : bags2[0] = S := by
          rw [← List.head_eq_getElem hne2]; exact hhead2
        refine hri2 u 0 (j - bags1.length) (k - bags1.length) (Nat.zero_le _) (by omega)
          hL2pos hj2 hk2 ?_ huk
        rw [hhead_eq]; exact huS
    · have hi2 : i - bags1.length < bags2.length := by simp only [List.length_append] at hi; omega
      have hj2 : j - bags1.length < bags2.length := by simp only [List.length_append] at hj; omega
      have hk2 : k - bags1.length < bags2.length := by simp only [List.length_append] at hk; omega
      rw [List.getElem_append_right (by omega)] at hui huk
      rw [List.getElem_append_right (by omega)]
      exact hri2 u (i - bags1.length) (j - bags1.length) (k - bags1.length)
        (by omega) (by omega) hi2 hj2 hk2 hui huk

lemma bags_reverse_ri (bags : List (Finset Nat)) (hri : BagsRI bags) :
    BagsRI bags.reverse := by
  intro u i j k hij hjk hi hj hk hui huk
  simp only [List.length_reverse] at hi hj hk
  rw [List.getElem_reverse] at hui huk ⊢
  exact hri u (bags.length - 1 - k) (bags.length - 1 - j) (bags.length - 1 - i)
    (by omega) (by omega) (by omega) (by omega) (by omega) huk hui

structure WellFormed {n : Nat} (st : State n) (active : Finset Nat) (W : Nat) : Prop where
  n_le : n ≤ st.nv
  act_sub : active ⊆ Finset.range st.nv
  disj : Disjoint (Finset.range n) active
  adj_lt : ∀ u v, v ∈ st.adj u → u < st.nv ∧ v < st.nv
  no_loop : ∀ u, u ∉ st.adj u
  symm : ∀ u v, v ∈ st.adj u ↔ u ∈ st.adj v
  deg_le : ∀ u, (st.adj u).card ≤ 3
  act_deg : ∀ u ∈ active, (st.adj u).card ≤ 1
  in_deg : ∀ u < n, (st.adj u).card ≤ 1
  bip : ∀ u, ∀ v ∈ st.adj u, st.shore u ≠ st.shore v
  act_shore : ∀ u ∈ active, st.shore u = false
  in_shore : ∀ u < n, st.shore u = true
  act_tag : ∀ u ∈ active, st.tag u = none
  in_tag : ∀ u < n, st.tag u = none
  bags_ne : st.bags ≠ []
  bags_head : st.bags.head bags_ne = Finset.range n
  bags_last : st.bags.getLast bags_ne = active
  bags_sub : ∀ B ∈ st.bags, B ⊆ Finset.range st.nv
  bags_card : ∀ B ∈ st.bags, B.card ≤ W
  bags_covV : ∀ u < st.nv, ∃ B ∈ st.bags, u ∈ B
  bags_covE : ∀ u v, v ∈ st.adj u → ∃ B ∈ st.bags, u ∈ B ∧ v ∈ B
  bags_ri : BagsRI st.bags

def mapV {r d : Nat} (base : Nat) (ports : Fin r → Nat) (v : Fin (r + d)) : Nat :=
  if h : v.val < r then ports ⟨v.val, h⟩ else base + (v.val - r)

lemma mapV_injective {r d : Nat} (base : Nat) (ports : Fin r → Nat)
    (hinj : Function.Injective ports) (hlt : ∀ k, ports k < base) :
    Function.Injective (mapV (d := d) base ports) := by
  intro v1 v2 h
  simp only [mapV] at h
  by_cases h1 : v1.val < r <;> by_cases h2 : v2.val < r
  · simp only [dif_pos h1, dif_pos h2] at h
    have := hinj h
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · simp only [dif_pos h1, dif_neg h2] at h
    have := hlt ⟨v1.val, h1⟩; omega
  · simp only [dif_neg h1, dif_pos h2] at h
    have := hlt ⟨v2.val, h2⟩; omega
  · simp only [dif_neg h1, dif_neg h2] at h
    exact Fin.ext (by omega)

def freshFinset (base d : Nat) : Finset Nat :=
  Finset.range (base + d) \ Finset.range base

def outFinset (base s : Nat) : Finset Nat :=
  (Finset.range s).image (fun k => base + k)

def portsFinset {r : Nat} (ports : Fin r → Nat) : Finset Nat :=
  Finset.univ.image ports

def attach {n r s d : Nat} (st : State n) (active : Finset Nat)
    (g : Gadget r s d) (ports : Fin r → Nat) (y : Word n) : State n :=
  let base := st.nv
  let adj' : Nat → Finset Nat := fun u =>
    st.adj u ∪
    (Finset.univ.filter (fun v : Fin (r + d) => mapV base ports v = u)).biUnion
      (fun v => (gadgetNbrs g v).image (mapV base ports))
  let shore' : Nat → Bool := fun u =>
    if h : base ≤ u ∧ u < base + d then
      g.shore ⟨r + (u - base), by omega⟩
    else st.shore u
  let tag' : Nat → Option (Word n × Bool) := fun u =>
    if h : base ≤ u ∧ u < base + d then
      (g.tagKind ⟨u - base, by omega⟩).map (fun b => (y, b))
    else st.tag u
  let B1 := active ∪ freshFinset base d
  let B2 := (active \ portsFinset ports) ∪ outFinset base s
  { nv := base + d
    adj := adj'
    shore := shore'
    tag := tag'
    bags := st.bags ++ [B1, B2] }

lemma mem_attach_adj {n r s d : Nat} (st : State n) (active : Finset Nat)
    (g : Gadget r s d) (ports : Fin r → Nat) (y : Word n) (u w : Nat) :
    w ∈ (attach st active g ports y).adj u ↔
      w ∈ st.adj u ∨ ∃ v1 v2 : Fin (r + d),
        mapV st.nv ports v1 = u ∧ mapV st.nv ports v2 = w ∧ v2 ∈ gadgetNbrs g v1 := by
  simp only [attach, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · rintro (h | ⟨v1, hv1, v2, hv2, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v1, v2, hv1, hw, hv2⟩
  · rintro (h | ⟨v1, v2, hv1, hw, hv2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v1, hv1, v2, hv2, hw⟩

lemma attach_wellFormed {n r s d W : Nat} (st : State n) (active : Finset Nat)
    (g : Gadget r s d) (hg : ValidGadget g) (ports : Fin r → Nat) (y : Word n)
    (hwf : WellFormed st active W)
    (hinj : Function.Injective ports)
    (hports : ∀ k, ports k ∈ active)
    (hW : active.card + d ≤ W) :
    WellFormed (attach st active g ports y) ((active \ portsFinset ports) ∪ outFinset st.nv s) W := by
  let st' := attach st active g ports y
  let active' := (active \ portsFinset ports) ∪ outFinset st.nv s
  have hports_lt : ∀ k, ports k < st.nv := fun k => Finset.mem_range.mp (hwf.act_sub (hports k))
  have hmap_inj : Function.Injective (mapV (d := d) st.nv ports) :=
    mapV_injective st.nv ports hinj hports_lt
  have hmap_lt : ∀ v : Fin (r + d), mapV st.nv ports v < st.nv + d := by
    intro v; simp only [mapV]; split_ifs with h
    · have := hports_lt ⟨v.val, h⟩; omega
    · omega
  have hmap_shore : ∀ v : Fin (r + d), st'.shore (mapV st.nv ports v) = g.shore v := by
    intro v; simp only [st', attach, mapV]
    by_cases hv : v.val < r
    · simp only [dif_pos hv]
      have hlt : ports ⟨v.val, hv⟩ < st.nv := hports_lt ⟨v.val, hv⟩
      have hnot : ¬(st.nv ≤ ports ⟨v.val, hv⟩ ∧ ports ⟨v.val, hv⟩ < st.nv + d) := by omega
      rw [dif_neg hnot, hwf.act_shore _ (hports _), hg.port_shore v (by omega)]
    · simp only [dif_neg hv]
      have hcond : st.nv ≤ st.nv + (v.val - r) ∧ st.nv + (v.val - r) < st.nv + d := by
        have := v.isLt; omega
      rw [dif_pos hcond]
      congr 1; exact Fin.ext (by dsimp; omega)
  have hdeg_map : ∀ v0 : Fin (r + d),
      (st'.adj (mapV st.nv ports v0)) =
        st.adj (mapV st.nv ports v0) ∪ (gadgetNbrs g v0).image (mapV st.nv ports) := by
    intro v0
    ext w
    rw [mem_attach_adj, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (h | ⟨v1, v2, hv1, hv2, hnbr⟩)
      · exact Or.inl h
      · have heq : v1 = v0 := hmap_inj hv1
        subst heq; exact Or.inr ⟨v2, hnbr, hv2⟩
    · rintro (h | ⟨v2, hnbr, hv2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨v0, v2, rfl, hv2, hnbr⟩
  have hfresh_adj_old : ∀ u, st.nv ≤ u → st.adj u = ∅ := by
    intro u hu
    ext w; simp only [Finset.notMem_empty, iff_false]
    intro hw; have := (hwf.adj_lt u w hw).1; omega
  have hB1sub : active ∪ freshFinset st.nv d ⊆
      active ∪ (Finset.range (st.nv + d) \ Finset.range st.nv) := by
    exact Finset.Subset.refl _
  have hB2B1 : active' ⊆ active ∪ freshFinset st.nv d := by
    intro u hu
    rcases Finset.mem_union.mp hu with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp h1).1
    · simp only [outFinset, Finset.mem_image, Finset.mem_range] at h2
      rcases h2 with ⟨k, hk, rfl⟩
      refine Finset.mem_union_right _ ?_
      simp only [freshFinset, Finset.mem_sdiff, Finset.mem_range]
      have := hg.hs; omega
  have hB1card : (active ∪ freshFinset st.nv d).card ≤ W := by
    have hfr : (freshFinset st.nv d).card ≤ d := by
      have hsub : freshFinset st.nv d ⊆ (Finset.range d).image (fun k => st.nv + k) := by
        intro u hu
        simp only [freshFinset, Finset.mem_sdiff, Finset.mem_range] at hu
        simp only [Finset.mem_image, Finset.mem_range]
        exact ⟨u - st.nv, by omega, by omega⟩
      exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (by simp))
    exact le_trans (Finset.card_union_le _ _) (by omega)
  obtain ⟨hne', hhead', hlast', hsub', hcard', hri'⟩ :=
    bags_append_two st.bags st.nv d W active (active ∪ freshFinset st.nv d) active'
      hwf.bags_ne hwf.bags_last hwf.bags_sub hwf.bags_card hwf.bags_ri
      Finset.subset_union_left hB1sub hB2B1 hB1card
  refine
    { n_le := by simp only [attach]; have := hwf.n_le; omega
      act_sub := by
        intro u hu
        simp only [attach]
        rcases Finset.mem_union.mp hu with h1 | h2
        · have := Finset.mem_range.mp (hwf.act_sub (Finset.mem_sdiff.mp h1).1)
          exact Finset.mem_range.mpr (by omega)
        · simp only [outFinset, Finset.mem_image, Finset.mem_range] at h2
          rcases h2 with ⟨k, hk, rfl⟩
          have := hg.hs; exact Finset.mem_range.mpr (by omega)
      disj := by
        rw [Finset.disjoint_left]
        intro u hu hu'
        rcases Finset.mem_union.mp hu' with h1 | h2
        · exact Finset.disjoint_left.mp hwf.disj hu (Finset.mem_sdiff.mp h1).1
        · simp only [outFinset, Finset.mem_image, Finset.mem_range] at h2
          rcases h2 with ⟨k, hk, rfl⟩
          have := Finset.mem_range.mp hu; have := hwf.n_le; omega
      adj_lt := by
        intro u w hw
        simp only [attach]
        rcases (mem_attach_adj st active g ports y u w).mp hw with h | ⟨v1, v2, rfl, rfl, _⟩
        · have := hwf.adj_lt u w h; omega
        · exact ⟨hmap_lt v1, hmap_lt v2⟩
      no_loop := by
        intro u hu
        rcases (mem_attach_adj st active g ports y u u).mp hu with h | ⟨v1, v2, hv1, hv2, hnbr⟩
        · exact hwf.no_loop u h
        · have heq : v1 = v2 := hmap_inj (hv1.trans hv2.symm)
          subst heq; exact hg.no_loop v1 hnbr
      symm := by
        intro u w
        simp only [mem_attach_adj]
        constructor
        · rintro (h | ⟨v1, v2, hv1, hv2, hnbr⟩)
          · exact Or.inl ((hwf.symm u w).mp h)
          · exact Or.inr ⟨v2, v1, hv2, hv1, (gadgetNbrs_symm g v1 v2).mp hnbr⟩
        · rintro (h | ⟨v1, v2, hv1, hv2, hnbr⟩)
          · exact Or.inl ((hwf.symm u w).mpr h)
          · exact Or.inr ⟨v2, v1, hv2, hv1, (gadgetNbrs_symm g v1 v2).mp hnbr⟩
      deg_le := by
        intro u
        by_cases hm : ∃ v0 : Fin (r + d), mapV st.nv ports v0 = u
        · rcases hm with ⟨v0, rfl⟩
          rw [hdeg_map v0]
          by_cases hv0 : v0.val < r
          · have h1 : (st.adj (mapV st.nv ports v0)).card ≤ 1 := by
              simp only [mapV, dif_pos hv0]; exact hwf.act_deg _ (hports _)
            have h2 : ((gadgetNbrs g v0).image (mapV st.nv ports)).card ≤ 1 := by
              exact le_trans Finset.card_image_le (hg.port_deg v0 (by omega))
            exact le_trans (Finset.card_union_le _ _) (by omega)
          · have hge : st.nv ≤ mapV st.nv ports v0 := by simp only [mapV, dif_neg hv0]; omega
            rw [hfresh_adj_old _ hge, Finset.empty_union]
            exact le_trans Finset.card_image_le (hg.all_deg v0)
        · have hadj : st'.adj u = st.adj u := by
            ext w; rw [mem_attach_adj]
            constructor
            · rintro (h | ⟨v1, _, hv1, _, _⟩)
              · exact h
              · exact False.elim (hm ⟨v1, hv1⟩)
            · exact Or.inl
          rw [hadj]; exact hwf.deg_le u
      act_deg := by
        intro u hu
        rcases Finset.mem_union.mp hu with h1 | h2
        · have hu_act : u ∈ active := (Finset.mem_sdiff.mp h1).1
          have hu_notp : u ∉ portsFinset ports := (Finset.mem_sdiff.mp h1).2
          have hu_lt : u < st.nv := Finset.mem_range.mp (hwf.act_sub hu_act)
          have hadj : st'.adj u = st.adj u := by
            ext w; rw [mem_attach_adj]
            constructor
            · rintro (h | ⟨v1, _, hv1, _, _⟩)
              · exact h
              · simp only [mapV] at hv1
                split_ifs at hv1 with h
                · exact False.elim (hu_notp (Finset.mem_image.mpr ⟨⟨v1.val, h⟩, Finset.mem_univ _, hv1⟩))
                · omega
            · exact Or.inl
          rw [hadj]; exact hwf.act_deg u hu_act
        · simp only [outFinset, Finset.mem_image, Finset.mem_range] at h2
          rcases h2 with ⟨k, hk, rfl⟩
          have hs_le := hg.hs
          let v0 : Fin (r + d) := ⟨r + k, by omega⟩
          have hmv : mapV st.nv ports v0 = st.nv + k := by
            simp only [mapV, v0]; rw [dif_neg (by omega)]; omega
          rw [← hmv, hdeg_map v0, hmv, hfresh_adj_old _ (by omega), Finset.empty_union]
          exact le_trans Finset.card_image_le (hg.port_deg v0 (by simp [v0]; omega))
      in_deg := by
        intro u hu
        have hu_lt : u < st.nv := lt_of_lt_of_le hu hwf.n_le
        have hadj : st'.adj u = st.adj u := by
          ext w; rw [mem_attach_adj]
          constructor
          · rintro (h | ⟨v1, _, hv1, _, _⟩)
            · exact h
            · simp only [mapV] at hv1
              split_ifs at hv1 with h
              · have hp := hports ⟨v1.val, h⟩
                rw [hv1] at hp
                exact False.elim (Finset.disjoint_left.mp hwf.disj (Finset.mem_range.mpr hu) hp)
              · omega
          · exact Or.inl
        rw [hadj]; exact hwf.in_deg u hu
      bip := by
        intro u w hw
        rcases (mem_attach_adj st active g ports y u w).mp hw with h | ⟨v1, v2, rfl, rfl, hnbr⟩
        · have ⟨hu, hwl⟩ := hwf.adj_lt u w h
          simp only [st', attach]
          rw [dif_neg (by omega), dif_neg (by omega)]
          exact hwf.bip u w h
        · rw [hmap_shore v1, hmap_shore v2]
          exact hg.bip v1 v2 hnbr
      act_shore := by
        intro u hu
        rcases Finset.mem_union.mp hu with h1 | h2
        · have hu_act := (Finset.mem_sdiff.mp h1).1
          have hu_lt := Finset.mem_range.mp (hwf.act_sub hu_act)
          simp only [st', attach]; rw [dif_neg (by omega)]
          exact hwf.act_shore u hu_act
        · simp only [outFinset, Finset.mem_image, Finset.mem_range] at h2
          rcases h2 with ⟨k, hk, rfl⟩
          have hs_le := hg.hs
          simp only [st', attach]; rw [dif_pos (by omega)]
          exact hg.port_shore ⟨r + (st.nv + k - st.nv), by omega⟩ (by dsimp; omega)
      in_shore := by
        intro u hu
        have hu_lt : u < st.nv := lt_of_lt_of_le hu hwf.n_le
        simp only [st', attach]; rw [dif_neg (by omega)]
        exact hwf.in_shore u hu
      act_tag := by
        intro u hu
        rcases Finset.mem_union.mp hu with h1 | h2
        · have hu_act := (Finset.mem_sdiff.mp h1).1
          have hu_lt := Finset.mem_range.mp (hwf.act_sub hu_act)
          simp only [st', attach]; rw [dif_neg (by omega)]
          exact hwf.act_tag u hu_act
        · simp only [outFinset, Finset.mem_image, Finset.mem_range] at h2
          rcases h2 with ⟨k, hk, rfl⟩
          have hs_le := hg.hs
          simp only [st', attach]; rw [dif_pos (by omega)]
          have htk := hg.out_tag ⟨st.nv + k - st.nv, by omega⟩ (by dsimp; omega)
          simp only [Option.map_eq_none_iff]
          simpa [Nat.add_sub_cancel_left] using htk
      in_tag := by
        intro u hu
        have hu_lt : u < st.nv := lt_of_lt_of_le hu hwf.n_le
        simp only [st', attach]; rw [dif_neg (by omega)]
        exact hwf.in_tag u hu
      bags_ne := hne'
      bags_head := hhead'.trans hwf.bags_head
      bags_last := hlast'
      bags_sub := hsub'
      bags_card := hcard'
      bags_covV := by
        intro u hu
        simp only [attach] at hu
        by_cases hlt : u < st.nv
        · obtain ⟨B, hB, huB⟩ := hwf.bags_covV u hlt
          exact ⟨B, List.mem_append_left _ hB, huB⟩
        · refine ⟨active ∪ freshFinset st.nv d, by simp [st', attach], ?_⟩
          refine Finset.mem_union_right _ ?_
          simp only [freshFinset, Finset.mem_sdiff, Finset.mem_range]
          omega
      bags_covE := by
        intro u w hw
        rcases (mem_attach_adj st active g ports y u w).mp hw with h | ⟨v1, v2, rfl, rfl, _⟩
        · obtain ⟨B, hB, huB, hwB⟩ := hwf.bags_covE u w h
          exact ⟨B, List.mem_append_left _ hB, huB, hwB⟩
        · refine ⟨active ∪ freshFinset st.nv d, by simp [st', attach], ?_, ?_⟩
          · simp only [mapV]; split_ifs with h
            · exact Finset.mem_union_left _ (hports _)
            · refine Finset.mem_union_right _ ?_
              simp only [freshFinset, Finset.mem_sdiff, Finset.mem_range]; omega
          · simp only [mapV]; split_ifs with h
            · exact Finset.mem_union_left _ (hports _)
            · refine Finset.mem_union_right _ ?_
              simp only [freshFinset, Finset.mem_sdiff, Finset.mem_range]; omega
      bags_ri := hri' }

noncomputable def overridePorts {r : Nat} (σ : Nat → Bool) (ports : Fin r → Nat) (τ : Fin r → Bool) (u : Nat) : Bool :=
  if h : ∃ k : Fin r, ports k = u then τ (Classical.choose h) else σ u

lemma overridePorts_at {r : Nat} (σ : Nat → Bool) (ports : Fin r → Nat)
    (hinj : Function.Injective ports) (τ : Fin r → Bool) (k : Fin r) :
    overridePorts σ ports τ (ports k) = τ k := by
  have hex : ∃ k' : Fin r, ports k' = ports k := ⟨k, rfl⟩
  simp only [overridePorts, dif_pos hex]
  rw [hinj (Classical.choose_spec hex)]

lemma overridePorts_other {r : Nat} (σ : Nat → Bool) (ports : Fin r → Nat)
    (τ : Fin r → Bool) (u : Nat) (hu : u ∉ portsFinset ports) :
    overridePorts σ ports τ u = σ u := by
  have hnot : ¬∃ k : Fin r, ports k = u := by
    rintro ⟨k, hk⟩
    exact hu (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
  simp only [overridePorts, dif_neg hnot]

/-- Master Gluing Lemma: exact count identity when attaching a valid gadget. -/
lemma attach_cnt {n r s d W : Nat} (st : State n) (active : Finset Nat)
    (g : Gadget r s d) (hg : ValidGadget g) (ports : Fin r → Nat) (y : Word n)
    (hwf : WellFormed st active W)
    (hinj : Function.Injective ports)
    (hports : ∀ k, ports k ∈ active)
    (f : Table n) (σ : Nat → Bool) :
    let st' := attach st active g ports y
    let A_old := Finset.range n ∪ active
    let A_new := Finset.range n ∪ ((active \ portsFinset ports) ∪ outFinset st.nv s)
    cnt st' f A_new σ =
      ∑ τ : (Fin r → Bool),
        cnt st f A_old (overridePorts σ ports τ) *
        gadgetCnt g hg.hs (f y) τ (fun j => σ (st.nv + j.val)) := by
  intro st' A_old A_new
  have hports_lt : ∀ k, ports k < st.nv := fun k => Finset.mem_range.mp (hwf.act_sub (hports k))
  have hmap_inj : Function.Injective (mapV (d := d) st.nv ports) :=
    mapV_injective st.nv ports hinj hports_lt
  let gSet : (Fin r → Bool) → Finset (Fin (d - s) → Bool) := fun τ =>
    (Finset.univ : Finset (Fin (d - s) → Bool)).filter
      (fun z => gadgetValidB g hg.hs (f y) τ (fun j => σ (st.nv + j.val)) z = true)
  have hgSet_card : ∀ τ, (gSet τ).card = gadgetCnt g hg.hs (f y) τ (fun j => σ (st.nv + j.val)) := by
    intro τ; exact (countBoolFn_eq_card (d - s) _).symm
  let dom : Finset (Σ τ : (Fin r → Bool), Finset Nat × (Fin (d - s) → Bool)) :=
    Finset.univ.sigma (fun τ => isSets st f A_old (overridePorts σ ports τ) ×ˢ gSet τ)
  have hdom_card : dom.card =
      ∑ τ : (Fin r → Bool),
        cnt st f A_old (overridePorts σ ports τ) *
        gadgetCnt g hg.hs (f y) τ (fun j => σ (st.nv + j.val)) := by
    simp only [dom, Finset.card_sigma, Finset.card_product, cnt, hgSet_card]
  rw [← hdom_card]
  change (isSets st' f A_new σ).card = dom.card
  symm
  let freshSet : (Fin (d - s) → Bool) → Finset Nat := fun z =>
    ((Finset.univ : Finset (Fin d)).filter (fun k =>
      if h : k.val < s then σ (st.nv + k.val) = true
      else z ⟨k.val - s, by omega⟩ = true)).image (fun k => st.nv + k.val)
  have hmem_freshSet : ∀ z u, u ∈ freshSet z ↔
      ∃ (k : Nat) (hk : k < d), st.nv + k = u ∧
        (if h : k < s then σ (st.nv + k) else z ⟨k - s, by omega⟩) = true := by
    intro z u
    simp only [freshSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hval, rfl⟩
      refine ⟨k.val, k.isLt, rfl, ?_⟩
      split_ifs at hval ⊢ <;> exact hval
    · rintro ⟨k, hk, rfl, hval⟩
      refine ⟨⟨k, hk⟩, ?_, rfl⟩
      split_ifs at hval ⊢ <;> exact hval
  have hassign_eq : ∀ τ z I (hI : I ∈ isSets st f A_old (overridePorts σ ports τ))
      (v : Fin (r + d)),
      decide (mapV st.nv ports v ∈ I ∪ freshSet z) =
        gadgetAssign hg.hs τ (fun j => σ (st.nv + j.val)) z v := by
    intro τ z I hI v
    simp only [isSets, Finset.mem_filter, Finset.mem_powerset] at hI
    simp only [mapV, gadgetAssign]
    by_cases hv : v.val < r
    · simp only [dif_pos hv]
      have hplt : ports ⟨v.val, hv⟩ < st.nv := hports_lt ⟨v.val, hv⟩
      have hnotF : ports ⟨v.val, hv⟩ ∉ freshSet z := by
        rw [hmem_freshSet]; rintro ⟨k, _, heq, _⟩; omega
      have hmem : ports ⟨v.val, hv⟩ ∈ I ∪ freshSet z ↔ ports ⟨v.val, hv⟩ ∈ I := by
        simp [hnotF]
      have hA : ports ⟨v.val, hv⟩ ∈ A_old := Finset.mem_union_right _ (hports _)
      have hdec := hI.2.2.2 _ hA
      rw [overridePorts_at σ ports hinj τ ⟨v.val, hv⟩] at hdec
      rw [decide_eq_decide.mpr hmem, hdec]
    · simp only [dif_neg hv]
      have hnotI : st.nv + (v.val - r) ∉ I := by
        intro hmem; have := Finset.mem_range.mp (hI.1 hmem); omega
      have hdec_eq : decide (st.nv + (v.val - r) ∈ I ∪ freshSet z) =
          decide (st.nv + (v.val - r) ∈ freshSet z) := by
        simp [hnotI]
      rw [hdec_eq]
      by_cases h2 : v.val - r < s
      · simp only [dif_pos h2]
        have hiff : st.nv + (v.val - r) ∈ freshSet z ↔ σ (st.nv + (v.val - r)) = true := by
          rw [hmem_freshSet]
          constructor
          · rintro ⟨k, hk, heq, hval⟩
            have hkeq : k = v.val - r := by omega
            subst hkeq; simp [dif_pos h2] at hval; exact hval
          · intro hval
            exact ⟨v.val - r, by have := v.isLt; omega, rfl, by simp [dif_pos h2, hval]⟩
        simp [hiff]
      · simp only [dif_neg h2]
        have hiff : st.nv + (v.val - r) ∈ freshSet z ↔ z ⟨v.val - r - s, by omega⟩ = true := by
          rw [hmem_freshSet]
          constructor
          · rintro ⟨k, hk, heq, hval⟩
            have hkeq : k = v.val - r := by omega
            subst hkeq; simp [dif_neg h2] at hval; exact hval
          · intro hval
            exact ⟨v.val - r, by have := v.isLt; omega, rfl, by simp [dif_neg h2, hval]⟩
        simp [hiff]
  refine Finset.card_bij (fun p _ => p.2.1 ∪ freshSet p.2.2) ?_ ?_ ?_
  · intro ⟨τ, I, z⟩ hp
    simp only [dom, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product, gSet,
      Finset.mem_filter] at hp
    rcases hp with ⟨hI, hz⟩
    have hI' := hI
    simp only [isSets, Finset.mem_filter, Finset.mem_powerset] at hI'
    simp only [gadgetValidB, Bool.and_eq_true, List.all_eq_true] at hz
    rcases hz with ⟨hliveG, hedgeG⟩
    simp only [isSets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu
      simp only [st', attach]
      rcases Finset.mem_union.mp hu with huI | huF
      · have := Finset.mem_range.mp (hI'.1 huI); exact Finset.mem_range.mpr (by omega)
      · rw [hmem_freshSet] at huF
        rcases huF with ⟨k, hk, rfl, _⟩
        exact Finset.mem_range.mpr (by omega)
    · intro u hu
      rcases Finset.mem_union.mp hu with huI | huF
      · have hu_lt : u < st.nv := Finset.mem_range.mp (hI'.1 huI)
        simp only [liveOf, st', attach, dif_neg (show ¬(st.nv ≤ u ∧ u < st.nv + d) by omega)]
        exact hI'.2.1 u huI
      · rw [hmem_freshSet] at huF
        rcases huF with ⟨k, hk, rfl, hval⟩
        simp only [liveOf, st', attach, dif_pos (show st.nv ≤ st.nv + k ∧ st.nv + k < st.nv + d by omega)]
        have hksub : st.nv + k - st.nv = k := by omega
        have hlt := hliveG ⟨k, hk⟩ (List.mem_finRange _)
        have hassign_k : gadgetAssign hg.hs τ (fun j => σ (st.nv + j.val)) z ⟨r + k, by omega⟩ = true := by
          simp only [gadgetAssign, dif_neg (show ¬(r + k < r) by omega)]
          have hsub : r + k - r = k := by omega
          by_cases hks : k < s
          · rw [dif_pos (by omega)]
            simp only [dif_pos hks] at hval
            simpa [hsub] using hval
          · rw [dif_neg (by omega)]
            simp only [dif_neg hks] at hval
            have heq_idx : (⟨r + k - r - s, by omega⟩ : Fin (d - s)) = ⟨k - s, by omega⟩ :=
              Fin.ext (by dsimp; omega)
            rw [heq_idx]; exact hval
        simp only [hassign_k, ↓reduceIte] at hlt
        have hkeq : (⟨st.nv + k - st.nv, by omega⟩ : Fin d) = ⟨k, hk⟩ := Fin.ext (by dsimp; omega)
        rw [hkeq]
        cases htk : g.tagKind ⟨k, hk⟩ with
        | none => simp
        | some b => simp [htk] at hlt ⊢; exact hlt
    · intro u hu w hw hwmem
      rcases (mem_attach_adj st active g ports y u w).mp hw with hold | ⟨v1, v2, rfl, rfl, hnbr⟩
      · have ⟨hu_lt, hw_lt⟩ := hwf.adj_lt u w hold
        have huI : u ∈ I := by
          rcases Finset.mem_union.mp hu with h | h
          · exact h
          · rw [hmem_freshSet] at h; rcases h with ⟨k, _, heq, _⟩; omega
        have hwI : w ∈ I := by
          rcases Finset.mem_union.mp hwmem with h | h
          · exact h
          · rw [hmem_freshSet] at h; rcases h with ⟨k, _, heq, _⟩; omega
        exact hI'.2.2.1 u huI w hold hwI
      · have ha1 : gadgetAssign hg.hs τ (fun j => σ (st.nv + j.val)) z v1 = true := by
          rw [← hassign_eq τ z I hI v1]; exact decide_eq_true hu
        have ha2 : gadgetAssign hg.hs τ (fun j => σ (st.nv + j.val)) z v2 = true := by
          rw [← hassign_eq τ z I hI v2]; exact decide_eq_true hwmem
        simp only [gadgetNbrs, Finset.mem_filter, Finset.mem_univ, true_and,
          List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hnbr
        rcases hnbr with ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · have := hedgeG e he; simp [ha1, ha2] at this
        · have := hedgeG e he; simp [ha1, ha2] at this
    · intro u hu
      simp only [A_new, Finset.mem_union, Finset.mem_sdiff] at hu
      rcases hu with huN | ⟨huAct, huNotP⟩ | huOut
      · have hu_lt : u < st.nv := lt_of_lt_of_le (Finset.mem_range.mp huN) hwf.n_le
        have hnotF : u ∉ freshSet z := by
          rw [hmem_freshSet]; rintro ⟨k, _, heq, _⟩; omega
        have huNotP' : u ∉ portsFinset ports := by
          intro hp
          simp only [portsFinset, Finset.mem_image, Finset.mem_univ, true_and] at hp
          rcases hp with ⟨k, rfl⟩
          exact Finset.disjoint_left.mp hwf.disj huN (hports k)
        have hmem : u ∈ I ∪ freshSet z ↔ u ∈ I := by simp [hnotF]
        have hdec := hI'.2.2.2 u (Finset.mem_union_left _ huN)
        rw [overridePorts_other σ ports τ u huNotP'] at hdec
        simp [hmem, hdec]
      · have hu_lt : u < st.nv := Finset.mem_range.mp (hwf.act_sub huAct)
        have hnotF : u ∉ freshSet z := by
          rw [hmem_freshSet]; rintro ⟨k, _, heq, _⟩; omega
        have hmem : u ∈ I ∪ freshSet z ↔ u ∈ I := by simp [hnotF]
        have hdec := hI'.2.2.2 u (Finset.mem_union_right _ huAct)
        rw [overridePorts_other σ ports τ u huNotP] at hdec
        simp [hmem, hdec]
      · simp only [outFinset, Finset.mem_image, Finset.mem_range] at huOut
        rcases huOut with ⟨k, hk, rfl⟩
        have hnotI : st.nv + k ∉ I := by
          intro hmem; have := Finset.mem_range.mp (hI'.1 hmem); omega
        have hdec_eq : decide (st.nv + k ∈ I ∪ freshSet z) =
            decide (st.nv + k ∈ freshSet z) := by
          simp [hnotI]
        rw [hdec_eq]
        have hiff : st.nv + k ∈ freshSet z ↔ σ (st.nv + k) = true := by
          rw [hmem_freshSet]
          constructor
          · rintro ⟨k', _, heq, hval⟩
            have : k' = k := by omega
            subst this; simp [dif_pos hk] at hval; exact hval
          · intro hval
            have := hg.hs
            exact ⟨k, by omega, rfl, by simp [dif_pos hk, hval]⟩
        simp [hiff]
  · intro ⟨τ1, I1, z1⟩ hp1 ⟨τ2, I2, z2⟩ hp2 heq
    simp only [dom, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product, gSet,
      Finset.mem_filter] at hp1 hp2
    have hI1_sub : I1 ⊆ Finset.range st.nv := (Finset.mem_powerset.mp (Finset.mem_filter.mp hp1.1).1)
    have hI2_sub : I2 ⊆ Finset.range st.nv := (Finset.mem_powerset.mp (Finset.mem_filter.mp hp2.1).1)
    have hIeq : I1 = I2 := by
      ext u
      have h1 : u ∈ (I1 ∪ freshSet z1) ∩ Finset.range st.nv ↔ u ∈ I1 := by
        constructor
        · intro h
          rcases Finset.mem_union.mp (Finset.mem_inter.mp h).1 with hI | hF
          · exact hI
          · rw [hmem_freshSet] at hF; rcases hF with ⟨k, _, rfl, _⟩
            have := Finset.mem_range.mp (Finset.mem_inter.mp h).2; omega
        · intro h; exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h, hI1_sub h⟩
      have h2 : u ∈ (I2 ∪ freshSet z2) ∩ Finset.range st.nv ↔ u ∈ I2 := by
        constructor
        · intro h
          rcases Finset.mem_union.mp (Finset.mem_inter.mp h).1 with hI | hF
          · exact hI
          · rw [hmem_freshSet] at hF; rcases hF with ⟨k, _, rfl, _⟩
            have := Finset.mem_range.mp (Finset.mem_inter.mp h).2; omega
        · intro h; exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h, hI2_sub h⟩
      rw [← h1, ← h2, heq]
    have hτeq : τ1 = τ2 := by
      ext k
      have h1 := (Finset.mem_filter.mp hp1.1).2.2.2 (ports k) (Finset.mem_union_right _ (hports k))
      have h2 := (Finset.mem_filter.mp hp2.1).2.2.2 (ports k) (Finset.mem_union_right _ (hports k))
      rw [overridePorts_at σ ports hinj τ1 k] at h1
      rw [overridePorts_at σ ports hinj τ2 k] at h2
      rw [← h1, ← h2, hIeq]
    have hzeq : z1 = z2 := by
      ext i
      have hnotI1 : st.nv + (s + i.val) ∉ I1 := by
        intro h; have := Finset.mem_range.mp (hI1_sub h); omega
      have hnotI2 : st.nv + (s + i.val) ∉ I2 := by
        intro h; have := Finset.mem_range.mp (hI2_sub h); omega
      have h1 : st.nv + (s + i.val) ∈ I1 ∪ freshSet z1 ↔ z1 i = true := by
        simp only [Finset.mem_union, hnotI1, false_or, hmem_freshSet]
        constructor
        · rintro ⟨k, _, hkeq, hval⟩
          have : k = s + i.val := by omega
          subst this; simp [dif_neg (show ¬(s + i.val < s) by omega)] at hval
          have heqi : (⟨s + i.val - s, by omega⟩ : Fin (d - s)) = i := Fin.ext (by dsimp; omega)
          simpa [heqi] using hval
        · intro hval
          refine ⟨s + i.val, by have := hg.hs; have := i.isLt; omega, rfl, ?_⟩
          rw [dif_neg (show ¬(s + i.val < s) by omega)]
          have heqi : (⟨s + i.val - s, by omega⟩ : Fin (d - s)) = i := Fin.ext (by dsimp; omega)
          rw [heqi]; exact hval
      have h2 : st.nv + (s + i.val) ∈ I2 ∪ freshSet z2 ↔ z2 i = true := by
        simp only [Finset.mem_union, hnotI2, false_or, hmem_freshSet]
        constructor
        · rintro ⟨k, _, hkeq, hval⟩
          have : k = s + i.val := by omega
          subst this; simp [dif_neg (show ¬(s + i.val < s) by omega)] at hval
          have heqi : (⟨s + i.val - s, by omega⟩ : Fin (d - s)) = i := Fin.ext (by dsimp; omega)
          simpa [heqi] using hval
        · intro hval
          refine ⟨s + i.val, by have := hg.hs; have := i.isLt; omega, rfl, ?_⟩
          rw [dif_neg (show ¬(s + i.val < s) by omega)]
          have heqi : (⟨s + i.val - s, by omega⟩ : Fin (d - s)) = i := Fin.ext (by dsimp; omega)
          rw [heqi]; exact hval
      rw [heq] at h1
      cases h1v : z1 i <;> cases h2v : z2 i <;> simp_all
    subst hτeq; subst hIeq; subst hzeq; rfl
  · intro J hJ
    simp only [isSets, Finset.mem_filter, Finset.mem_powerset] at hJ
    rcases hJ with ⟨hJsub, hJlive, hJind, hJA⟩
    let I := J ∩ Finset.range st.nv
    let τ : Fin r → Bool := fun k => decide (ports k ∈ J)
    let z : Fin (d - s) → Bool := fun i => decide (st.nv + (s + i.val) ∈ J)
    have hIJ_eq : I ∪ freshSet z = J := by
      ext u
      simp only [Finset.mem_union, I, Finset.mem_inter, Finset.mem_range, hmem_freshSet]
      constructor
      · rintro (⟨huJ, _⟩ | ⟨k, hk, rfl, hval⟩)
        · exact huJ
        · by_cases hks : k < s
          · simp only [dif_pos hks] at hval
            have huA : st.nv + k ∈ A_new := by
              refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
              exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hks, rfl⟩
            have := hJA (st.nv + k) huA
            rw [hval] at this; exact of_decide_eq_true this
          · simp only [dif_neg hks, z] at hval
            have h1 := of_decide_eq_true hval
            have : st.nv + (s + (k - s)) = st.nv + k := by omega
            rw [this] at h1; exact h1
      · intro huJ
        have hult : u < st.nv + d := Finset.mem_range.mp (hJsub huJ)
        by_cases hlt : u < st.nv
        · exact Or.inl ⟨huJ, hlt⟩
        · refine Or.inr ⟨u - st.nv, by omega, by omega, ?_⟩
          by_cases hks : u - st.nv < s
          · rw [dif_pos hks]
            have huA : st.nv + (u - st.nv) ∈ A_new := by
              refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
              exact Finset.mem_image.mpr ⟨u - st.nv, Finset.mem_range.mpr hks, rfl⟩
            have := hJA (st.nv + (u - st.nv)) huA
            have heq : st.nv + (u - st.nv) = u := by omega
            rw [heq]; rw [heq] at this; rw [← this]; exact decide_eq_true huJ
          · rw [dif_neg hks]
            simp only [z]
            have heq : st.nv + (s + (u - st.nv - s)) = u := by omega
            rw [heq]; exact decide_eq_true huJ
    have hI_mem : I ∈ isSets st f A_old (overridePorts σ ports τ) := by
      simp only [isSets, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.inter_subset_right, ?_, ?_, ?_⟩
      · intro u hu
        have huJ := (Finset.mem_inter.mp hu).1
        have hult := Finset.mem_range.mp (Finset.mem_inter.mp hu).2
        have := hJlive u huJ
        simp only [liveOf, st', attach, dif_neg (show ¬(st.nv ≤ u ∧ u < st.nv + d) by omega)] at this
        exact this
      · intro u hu v hv hvmem
        have huJ := (Finset.mem_inter.mp hu).1
        have hvJ := (Finset.mem_inter.mp hvmem).1
        exact hJind u huJ v ((mem_attach_adj st active g ports y u v).mpr (Or.inl hv)) hvJ
      · intro u hu
        by_cases hp : u ∈ portsFinset ports
        · simp only [portsFinset, Finset.mem_image, Finset.mem_univ, true_and] at hp
          rcases hp with ⟨k, rfl⟩
          rw [overridePorts_at σ ports hinj τ k]
          simp only [I, Finset.mem_inter, Finset.mem_range, hports_lt k, and_true, τ]
        · rw [overridePorts_other σ ports τ u hp]
          have hu_lt : u < st.nv := by
            rcases Finset.mem_union.mp hu with h1 | h2
            · exact lt_of_lt_of_le (Finset.mem_range.mp h1) hwf.n_le
            · exact Finset.mem_range.mp (hwf.act_sub h2)
          have hu_new : u ∈ A_new := by
            rcases Finset.mem_union.mp hu with h1 | h2
            · exact Finset.mem_union_left _ h1
            · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h2, hp⟩))
          simp only [I, Finset.mem_inter, Finset.mem_range, hu_lt, and_true]
          exact hJA u hu_new
    refine ⟨⟨τ, (I, z)⟩, ?_, hIJ_eq⟩
    simp only [dom, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product, gSet,
      Finset.mem_filter]
    refine ⟨hI_mem, ?_⟩
    simp only [gadgetValidB, Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, ?_⟩
    · intro k _
      have hassign_k := hassign_eq τ z I hI_mem ⟨r + k.val, by omega⟩
      rw [hIJ_eq] at hassign_k
      have hmv : mapV (d := d) st.nv ports ⟨r + k.val, by have := k.isLt; omega⟩ = st.nv + k.val := by
        simp only [mapV, dif_neg (show ¬(r + k.val < r) by omega), Nat.add_sub_cancel_left]
      rw [hmv] at hassign_k
      by_cases hmem : st.nv + k.val ∈ J
      · rw [← hassign_k, decide_eq_true hmem, if_pos rfl]
        have hl := hJlive (st.nv + k.val) hmem
        simp only [liveOf, st', attach,
          dif_pos (show st.nv ≤ st.nv + k.val ∧ st.nv + k.val < st.nv + d by omega)] at hl
        have hkeq : (⟨st.nv + k.val - st.nv, by omega⟩ : Fin d) = k := Fin.ext (by dsimp; omega)
        rw [hkeq] at hl
        cases htk : g.tagKind k with
        | none => simp
        | some b => simp [htk] at hl ⊢; exact hl
      · rw [← hassign_k, decide_eq_false hmem]; simp
    · intro e he
      have h1 := hassign_eq τ z I hI_mem e.1
      have h2 := hassign_eq τ z I hI_mem e.2
      rw [hIJ_eq] at h1 h2
      rw [← h1, ← h2]
      by_cases hm1 : mapV st.nv ports e.1 ∈ J <;> by_cases hm2 : mapV st.nv ports e.2 ∈ J
      · have hnbr : e.2 ∈ gadgetNbrs g e.1 := by
          simp only [gadgetNbrs, Finset.mem_filter, Finset.mem_univ, true_and,
            List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
          exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
        have hadj := (mem_attach_adj st active g ports y (mapV st.nv ports e.1)
          (mapV st.nv ports e.2)).mpr (Or.inr ⟨e.1, e.2, rfl, rfl, hnbr⟩)
        exact False.elim (hJind _ hm1 _ hadj hm2)
      · simp [hm1, hm2]
      · simp [hm1, hm2]
      · simp [hm1, hm2]

/-- Mod-2 propagation lemma for a single functional/predicate gate step! -/
lemma attach_mod2 {n r s d W : Nat} (st : State n) (active : Finset Nat)
    (g : Gadget r s d) (hg : ValidGadget g) (ports : Fin r → Nat) (y : Word n)
    (hwf : WellFormed st active W)
    (hinj : Function.Injective ports)
    (hports : ∀ k, ports k ∈ active)
    (f : Table n)
    (val : Word n → Nat → Bool)
    (Pold : Word n → Prop) [∀ a, Decidable (Pold a)]
    (hinv : ∀ σ : Nat → Bool,
      cnt st f (Finset.range n ∪ active) σ % 2 =
        if Pold (fun j => σ j.val) ∧ (∀ w ∈ active, σ w = val (fun j => σ j.val) w) then 1 else 0)
    (gateP : Bool → (Fin r → Bool) → (Fin s → Bool) → Prop)
    [∀ v inp out, Decidable (gateP v inp out)]
    (hgate : ∀ (v : Bool) (inp : Fin r → Bool) (out : Fin s → Bool),
      gadgetCnt g hg.hs v inp out % 2 = if gateP v inp out then 1 else 0) :
    ∀ σ : Nat → Bool,
      cnt (attach st active g ports y) f
        (Finset.range n ∪ ((active \ portsFinset ports) ∪ outFinset st.nv s)) σ % 2 =
      if Pold (fun j => σ j.val) ∧
         (∀ w ∈ active \ portsFinset ports, σ w = val (fun j => σ j.val) w) ∧
         gateP (f y) (fun k => val (fun j => σ j.val) (ports k)) (fun j => σ (st.nv + j.val))
      then 1 else 0 := by
  intro σ
  rw [attach_cnt st active g hg ports y hwf hinj hports f σ]
  rw [sum_mod_two]
  have hword_eq : ∀ τ : Fin r → Bool,
      (fun j : Fin n => overridePorts σ ports τ j.val) = (fun j : Fin n => σ j.val) := by
    intro τ; ext j
    refine overridePorts_other σ ports τ j.val ?_
    intro hp
    simp only [portsFinset, Finset.mem_image, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨k, hk⟩
    have := hports k; rw [hk] at this
    exact Finset.disjoint_left.mp hwf.disj (Finset.mem_range.mpr j.isLt) this
  let a : Word n := fun j => σ j.val
  let τ0 : Fin r → Bool := fun k => val a (ports k)
  have hterm : ∀ τ : Fin r → Bool,
      (cnt st f (Finset.range n ∪ active) (overridePorts σ ports τ) *
        gadgetCnt g hg.hs (f y) τ (fun j => σ (st.nv + j.val))) % 2 =
      if τ = τ0 ∧ Pold a ∧ (∀ w ∈ active \ portsFinset ports, σ w = val a w) ∧
         gateP (f y) τ0 (fun j => σ (st.nv + j.val))
      then 1 else 0 := by
    intro τ
    rw [mul_mod_two, hinv (overridePorts σ ports τ), hword_eq τ, hgate]
    have hall_iff :
        (∀ w ∈ active, overridePorts σ ports τ w = val a w) ↔
        (τ = τ0 ∧ ∀ w ∈ active \ portsFinset ports, σ w = val a w) := by
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · ext k
          have := h (ports k) (hports k)
          rw [overridePorts_at σ ports hinj τ k] at this
          exact this
        · intro w hw
          have := h w (Finset.mem_sdiff.mp hw).1
          rw [overridePorts_other σ ports τ w (Finset.mem_sdiff.mp hw).2] at this
          exact this
      · rintro ⟨rfl, hrest⟩ w hw
        by_cases hp : w ∈ portsFinset ports
        · simp only [portsFinset, Finset.mem_image, Finset.mem_univ, true_and] at hp
          rcases hp with ⟨k, rfl⟩
          rw [overridePorts_at σ ports hinj τ0 k]
        · rw [overridePorts_other σ ports τ0 w hp]
          exact hrest w (Finset.mem_sdiff.mpr ⟨hw, hp⟩)
    have h1 : (if Pold a ∧ ∀ w ∈ active, overridePorts σ ports τ w = val a w then (1 : Nat) else 0) =
        if Pold a ∧ τ = τ0 ∧ ∀ w ∈ active \ portsFinset ports, σ w = val a w then 1 else 0 :=
      ite_nat_congr (by simp only [hall_iff])
    rw [h1]
    by_cases hτ : τ = τ0
    · subst hτ
      split_ifs <;> simp_all
    · simp [hτ]
  have hsum :
      (∑ τ : Fin r → Bool,
        (cnt st f (Finset.range n ∪ active) (overridePorts σ ports τ) *
          gadgetCnt g hg.hs (f y) τ (fun j => σ (st.nv + j.val))) % 2) =
      if Pold a ∧ (∀ w ∈ active \ portsFinset ports, σ w = val a w) ∧
         gateP (f y) τ0 (fun j => σ (st.nv + j.val))
      then 1 else 0 := by
    rw [Finset.sum_congr rfl (fun τ _ => hterm τ)]
    rw [Finset.sum_eq_single τ0]
    · simp
    · intro τ _ hne; simp [hne]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  rw [hsum]
  split_ifs <;> rfl

/-! ### Part 4: Building SideGraph(n) -/

/-- Exact mod-2 count for a 3-edge path `x - p - q - y`. -/
def eq3ValidB (x y : Bool) (z : Fin 2 → Bool) : Bool :=
  !(x && z 0) && !(z 0 && z 1) && !(z 1 && y)

def eq3Cnt (x y : Bool) : Nat := countBoolFn 2 (eq3ValidB x y)

lemma cnt_eq3 : ∀ x y : Bool, eq3Cnt x y % 2 = if y = x then 1 else 0 := by decide

/-- Initial state after wiring `k` input ports (`0 .. k-1`) via 3-edge paths. -/
def initBase (n : Nat) : State n :=
  { nv := n
    adj := fun _ => ∅
    shore := fun _ => true
    tag := fun _ => none
    bags := [Finset.range n] }

def addEq3 {n : Nat} (st : State n) (curBag : Finset Nat) (k : Nat) : State n :=
  let p := st.nv
  let q := st.nv + 1
  let w := st.nv + 2
  let adj' : Nat → Finset Nat := fun u =>
    if u = k then insert p (st.adj u)
    else if u = p then {k, q}
    else if u = q then {p, w}
    else if u = w then {q}
    else st.adj u
  let shore' : Nat → Bool := fun u =>
    if u = p then false
    else if u = q then true
    else if u = w then false
    else st.shore u
  let B1 := curBag ∪ {p, q, w}
  let B2 := (curBag \ {k}) ∪ {w}
  { nv := st.nv + 3
    adj := adj'
    shore := shore'
    tag := st.tag
    bags := st.bags ++ [B1, B2] }

def initBag (n k : Nat) : Finset Nat :=
  (Finset.range k).image (fun j => n + 3 * j + 2) ∪ Finset.Ico k n

def initLoop (n : Nat) : (k : Nat) → State n
  | 0 => initBase n
  | k + 1 => addEq3 (initLoop n k) (initBag n k) k

lemma initLoop_nv (n k : Nat) : (initLoop n k).nv = n + 3 * k := by
  induction k with
  | zero => simp [initLoop, initBase]
  | succ k ih => simp [initLoop, addEq3, ih]; omega

lemma initBag_card (n k : Nat) (hk : k ≤ n) : (initBag n k).card = n := by
  have hdisj : Disjoint ((Finset.range k).image (fun j => n + 3 * j + 2)) (Finset.Ico k n) := by
    rw [Finset.disjoint_left]
    intro u h1 h2
    simp only [Finset.mem_image, Finset.mem_range] at h1
    rcases h1 with ⟨j, _, rfl⟩
    have := (Finset.mem_Ico.mp h2).2; omega
  rw [initBag, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b h => by omega),
      Finset.card_range, Nat.card_Ico]
  omega

lemma initBag_step (n k : Nat) (hk : k < n) :
    (initBag n k \ {k}) ∪ {n + 3 * k + 2} = initBag n (k + 1) := by
  ext u
  simp only [initBag, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro (⟨⟨j, hj, rfl⟩ | ⟨hk1, hk2⟩, hne⟩ | rfl)
    · exact Or.inl ⟨j, by omega, rfl⟩
    · exact Or.inr ⟨by omega, hk2⟩
    · exact Or.inl ⟨k, by omega, rfl⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨hk1, hk2⟩)
    · by_cases hjk : j = k
      · subst hjk; exact Or.inr rfl
      · exact Or.inl ⟨Or.inl ⟨j, by omega, rfl⟩, by omega⟩
    · exact Or.inl ⟨Or.inr ⟨by omega, hk2⟩, by omega⟩

structure InitInv (n k : Nat) (st : State n) : Prop where
  nv_eq : st.nv = n + 3 * k
  adj_lt : ∀ u v, v ∈ st.adj u → u < st.nv ∧ v < st.nv
  no_loop : ∀ u, u ∉ st.adj u
  symm : ∀ u v, v ∈ st.adj u ↔ u ∈ st.adj v
  deg_le : ∀ u, (st.adj u).card ≤ 3
  in_deg_done : ∀ u < k, (st.adj u).card ≤ 1
  in_deg_todo : ∀ u, k ≤ u → u < n → st.adj u = ∅
  w_deg : ∀ j < k, (st.adj (n + 3 * j + 2)).card ≤ 1
  bip : ∀ u, ∀ v ∈ st.adj u, st.shore u ≠ st.shore v
  in_shore : ∀ u < n, st.shore u = true
  w_shore : ∀ j < k, st.shore (n + 3 * j + 2) = false
  tag_none : ∀ u, st.tag u = none
  bags_ne : st.bags ≠ []
  bags_head : st.bags.head bags_ne = Finset.range n
  bags_last : st.bags.getLast bags_ne = initBag n k
  bags_sub : ∀ B ∈ st.bags, B ⊆ Finset.range st.nv
  bags_card : ∀ B ∈ st.bags, B.card ≤ n + 3
  bags_covV : ∀ u < st.nv, ∃ B ∈ st.bags, u ∈ B
  bags_covE : ∀ u v, v ∈ st.adj u → ∃ B ∈ st.bags, u ∈ B ∧ v ∈ B
  bags_ri : BagsRI st.bags
  sem : ∀ (f : Table n) (σ : Nat → Bool),
    cnt st f (Finset.range n ∪ (Finset.range k).image (fun j => n + 3 * j + 2)) σ % 2 =
      if (∀ j < k, σ (n + 3 * j + 2) = σ j) then 1 else 0

lemma initLoop_inv (n k : Nat) (hk : k ≤ n) : InitInv n k (initLoop n k) := by
  induction k with
  | zero =>
    refine
      { nv_eq := by simp [initLoop, initBase]
        adj_lt := by intro u v h; simp [initLoop, initBase] at h
        no_loop := by intro u; simp [initLoop, initBase]
        symm := by intro u v; simp [initLoop, initBase]
        deg_le := by intro u; simp [initLoop, initBase]
        in_deg_done := by intro u hu; omega
        in_deg_todo := by intro u _ _; rfl
        w_deg := by intro j hj; omega
        bip := by intro u v h; simp [initLoop, initBase] at h
        in_shore := by intro u _; rfl
        w_shore := by intro j hj; omega
        tag_none := by intro u; rfl
        bags_ne := by simp [initLoop, initBase]
        bags_head := by simp [initLoop, initBase]
        bags_last := by
          ext u; simp [initLoop, initBase, initBag]
        bags_sub := by intro B hB; simp [initLoop, initBase] at hB; subst hB; exact Finset.Subset.refl _
        bags_card := by intro B hB; simp [initLoop, initBase] at hB; subst hB; simp
        bags_covV := by
          intro u hu; exact ⟨Finset.range n, by simp [initLoop, initBase], Finset.mem_range.mpr hu⟩
        bags_covE := by intro u v h; simp [initLoop, initBase] at h
        bags_ri := by
          intro u i j m hij hjm hi hj hm hui hum
          simp [initLoop, initBase] at hi hj hm
          have : i = 0 ∧ j = 0 ∧ m = 0 := by omega
          rcases this with ⟨rfl, rfl, rfl⟩; exact hui
        sem := by
          intro f σ
          have hcard : cnt (initBase n) f (Finset.range n ∪ ∅) σ = 1 := by
            let I0 : Finset Nat := (Finset.range n).filter (fun u => σ u = true)
            have hsing : isSets (initBase n) f (Finset.range n ∪ ∅) σ = {I0} := by
              ext I
              simp only [isSets, Finset.union_empty, Finset.mem_filter, Finset.mem_powerset,
                Finset.mem_singleton, liveOf, initBase, Option.elim_none, Finset.notMem_empty,
                false_implies, implies_true, true_and]
              constructor
              · rintro ⟨hsub, hdec⟩
                ext u
                simp only [I0, Finset.mem_filter]
                constructor
                · intro hu; exact ⟨hsub hu, by rw [← hdec u (hsub hu)]; exact decide_eq_true hu⟩
                · rintro ⟨hrg, hσ⟩
                  have := hdec u hrg; rw [hσ] at this; exact of_decide_eq_true this
              · rintro rfl
                refine ⟨Finset.filter_subset _ _, fun u hu => ?_⟩
                simp only [I0, Finset.mem_filter, hu, true_and]
                cases σ u <;> simp
            rw [cnt, hsing, Finset.card_singleton]
          simpa [initLoop] using congrArg (· % 2) hcard }
  | succ k ih =>
    have ihk := ih (by omega)
    let st := initLoop n k
    let st' := addEq3 st (initBag n k) k
    have hst_nv : (initLoop n k).nv = st.nv := rfl
    have hnv : st.nv = n + 3 * k := ihk.nv_eq
    have hkl : k < st.nv := by omega
    have hB1sub : initBag n k ∪ {st.nv, st.nv + 1, st.nv + 2} ⊆
        initBag n k ∪ (Finset.range (st.nv + 3) \ Finset.range st.nv) := by
      intro u hu
      rcases Finset.mem_union.mp hu with h1 | h2
      · exact Finset.mem_union_left _ h1
      · refine Finset.mem_union_right _ ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at h2
        simp only [Finset.mem_sdiff, Finset.mem_range]
        rcases h2 with rfl | rfl | rfl <;> omega
    have hB2B1 : (initBag n k \ {k}) ∪ {st.nv + 2} ⊆ initBag n k ∪ {st.nv, st.nv + 1, st.nv + 2} := by
      intro u hu
      rcases Finset.mem_union.mp hu with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp h1).1
      · simp only [Finset.mem_singleton] at h2; subst h2
        exact Finset.mem_union_right _ (by simp)
    have hB1card : (initBag n k ∪ {st.nv, st.nv + 1, st.nv + 2}).card ≤ n + 3 := by
      have h1 := initBag_card n k (by omega)
      have h2 : ({st.nv, st.nv + 1, st.nv + 2} : Finset Nat).card ≤ 3 := by
        exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
          (le_trans (Finset.card_insert_le _ _) (by simp)) 1)
      exact le_trans (Finset.card_union_le _ _) (by omega)
    obtain ⟨hne', hhead', hlast', hsub', hcard', hri'⟩ :=
      bags_append_two st.bags st.nv 3 (n + 3) (initBag n k)
        (initBag n k ∪ {st.nv, st.nv + 1, st.nv + 2}) ((initBag n k \ {k}) ∪ {st.nv + 2})
        ihk.bags_ne ihk.bags_last ihk.bags_sub (fun B hB => ihk.bags_card B hB) ihk.bags_ri
        Finset.subset_union_left hB1sub hB2B1 hB1card
    have hlast_eq : (initBag n k \ {k}) ∪ {st.nv + 2} = initBag n (k + 1) := by
      have hw : st.nv + 2 = n + 3 * k + 2 := by omega
      rw [hw]; exact initBag_step n k (by omega)
    have hkad : st.adj k = ∅ := ihk.in_deg_todo k (le_refl k) (by omega)
    have hmem_st' : ∀ a b, b ∈ st'.adj a ↔
        b ∈ st.adj a ∨ (a = k ∧ b = st.nv) ∨ (a = st.nv ∧ b = k) ∨
        (a = st.nv ∧ b = st.nv + 1) ∨ (a = st.nv + 1 ∧ b = st.nv) ∨
        (a = st.nv + 1 ∧ b = st.nv + 2) ∨ (a = st.nv + 2 ∧ b = st.nv + 1) := by
      intro a b
      simp only [st', addEq3]
      by_cases h1 : a = k
      · rw [if_pos h1]; simp only [Finset.mem_insert]
        constructor
        · rintro (rfl | h)
          · exact Or.inr (Or.inl ⟨h1, rfl⟩)
          · exact Or.inl h
        · rintro (h | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)
          · exact Or.inr h
          · exact Or.inl rfl
          all_goals omega
      · rw [if_neg h1]
        by_cases h2 : a = st.nv
        · rw [if_pos h2]; simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (rfl | rfl)
            · exact Or.inr (Or.inr (Or.inl ⟨h2, rfl⟩))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, rfl⟩)))
          · rintro (h | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)
            · have := (ihk.adj_lt a b h).1; omega
            · omega
            · exact Or.inl rfl
            · exact Or.inr rfl
            all_goals omega
        · rw [if_neg h2]
          by_cases h3 : a = st.nv + 1
          · rw [if_pos h3]; simp only [Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro (rfl | rfl)
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩)))))
            · rintro (h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨h, _⟩)
              · have := (ihk.adj_lt a b h).1; omega
              · omega
              · omega
              · omega
              · exact Or.inl rfl
              · exact Or.inr rfl
              · omega
          · rw [if_neg h3]
            by_cases h4 : a = st.nv + 2
            · rw [if_pos h4]; simp only [Finset.mem_singleton]
              constructor
              · rintro rfl; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h4, rfl⟩)))))
              · rintro (h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩)
                · have := (ihk.adj_lt a b h).1; omega
                all_goals first | rfl | omega
            · rw [if_neg h4]
              constructor
              · exact Or.inl
              · rintro (h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩)
                · exact h
                all_goals omega
    refine
      { nv_eq := initLoop_nv n (k + 1)
        adj_lt := by
          intro u v hv
          change u < st.nv + 3 ∧ v < st.nv + 3
          rcases (hmem_st' u v).mp hv with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · have := ihk.adj_lt u v h; omega
          all_goals omega
        no_loop := by
          intro u hu
          rcases (hmem_st' u u).mp hu with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ihk.no_loop u h
          all_goals omega
        symm := by
          intro u v
          change v ∈ st'.adj u ↔ u ∈ st'.adj v
          rw [hmem_st' u v, hmem_st' v u, ihk.symm u v]
          constructor
          · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
            · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
          · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
            · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
        deg_le := by
          intro u; change (st'.adj u).card ≤ 3
          simp only [st', addEq3]
          split_ifs with h1 h2 h3 h4
          · subst h1; rw [hkad]; simp
          · exact le_trans (Finset.card_insert_le _ _) (by simp)
          · exact le_trans (Finset.card_insert_le _ _) (by simp)
          · simp
          · exact ihk.deg_le u
        in_deg_done := by
          intro u hu; change (st'.adj u).card ≤ 1
          simp only [st', addEq3]
          split_ifs with h1 h2 h3 h4
          · subst h1; rw [hkad]; simp
          · omega
          · omega
          · omega
          · exact ihk.in_deg_done u (by omega)
        in_deg_todo := by
          intro u hu1 hu2; change st'.adj u = ∅
          simp only [st', addEq3]
          split_ifs with h1 h2 h3 h4
          all_goals try omega
          exact ihk.in_deg_todo u (by omega) hu2
        w_deg := by
          intro j hj; change (st'.adj (n + 3 * j + 2)).card ≤ 1
          simp only [st', addEq3]
          split_ifs with h1 h2 h3 h4
          · omega
          · omega
          · omega
          · simp
          · exact ihk.w_deg j (by omega)
        bip := by
          intro u v hv; change st'.shore u ≠ st'.shore v
          have hsh : ∀ x, st'.shore x =
              if x = st.nv then false
              else if x = st.nv + 1 then true
              else if x = st.nv + 2 then false
              else st.shore x := fun _ => rfl
          rcases (hmem_st' u v).mp hv with h | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
          · have ⟨hu, hvl⟩ := ihk.adj_lt u v h
            rw [hsh u, hsh v, if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            exact ihk.bip u v h
          · rw [hu, hv, hsh k, hsh st.nv, if_neg (by omega), if_neg (by omega), if_neg (by omega),
                if_pos rfl, ihk.in_shore k (by omega)]; decide
          · rw [hu, hv, hsh st.nv, hsh k, if_pos rfl, if_neg (by omega), if_neg (by omega),
                if_neg (by omega), ihk.in_shore k (by omega)]; decide
          · rw [hu, hv, hsh st.nv, hsh (st.nv + 1), if_pos rfl, if_neg (by omega), if_pos rfl]; decide
          · rw [hu, hv, hsh (st.nv + 1), hsh st.nv, if_neg (by omega), if_pos rfl, if_pos rfl]; decide
          · rw [hu, hv, hsh (st.nv + 1), hsh (st.nv + 2), if_neg (by omega), if_pos rfl,
                if_neg (by omega), if_neg (by omega), if_pos rfl]; decide
          · rw [hu, hv, hsh (st.nv + 2), hsh (st.nv + 1), if_neg (by omega), if_neg (by omega),
                if_pos rfl, if_neg (by omega), if_pos rfl]; decide
        in_shore := by
          intro u hu; change st'.shore u = true
          simp only [st', addEq3]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          exact ihk.in_shore u hu
        w_shore := by
          intro j hj; change st'.shore (n + 3 * j + 2) = false
          simp only [st', addEq3]
          by_cases hjk : j = k
          · subst hjk
            rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            exact ihk.w_shore j (by omega)
        tag_none := ihk.tag_none
        bags_ne := hne'
        bags_head := hhead'.trans ihk.bags_head
        bags_last := hlast'.trans hlast_eq
        bags_sub := hsub'
        bags_card := hcard'
        bags_covV := by
          intro u hu
          change u < st.nv + 3 at hu
          by_cases hlt : u < st.nv
          · obtain ⟨B, hB, huB⟩ := ihk.bags_covV u hlt
            exact ⟨B, List.mem_append_left _ hB, huB⟩
          · refine ⟨initBag n k ∪ {st.nv, st.nv + 1, st.nv + 2}, ?_, ?_⟩
            · change _ ∈ st.bags ++ [initBag n k ∪ {st.nv, st.nv + 1, st.nv + 2}, (initBag n k \ {k}) ∪ {st.nv + 2}]
              simp
            · refine Finset.mem_union_right _ ?_
              have : u = st.nv ∨ u = st.nv + 1 ∨ u = st.nv + 2 := by omega
              rcases this with rfl | rfl | rfl <;> simp
        bags_covE := by
          intro u v hv
          have hkmem : k ∈ initBag n k := by
            simp only [initBag, Finset.mem_union, Finset.mem_Ico]; exact Or.inr ⟨le_refl k, by omega⟩
          let B1 := initBag n k ∪ {st.nv, st.nv + 1, st.nv + 2}
          have hB1 : B1 ∈ st'.bags := by
            change B1 ∈ st.bags ++ [B1, (initBag n k \ {k}) ∪ {st.nv + 2}]; simp
          rcases (hmem_st' u v).mp hv with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · obtain ⟨B, hB, huB, hvB⟩ := ihk.bags_covE u v h
            exact ⟨B, List.mem_append_left _ hB, huB, hvB⟩
          · exact ⟨B1, hB1, Finset.mem_union_left _ hkmem, Finset.mem_union_right _ (by simp)⟩
          · exact ⟨B1, hB1, Finset.mem_union_right _ (by simp), Finset.mem_union_left _ hkmem⟩
          · exact ⟨B1, hB1, Finset.mem_union_right _ (by simp), Finset.mem_union_right _ (by simp)⟩
          · exact ⟨B1, hB1, Finset.mem_union_right _ (by simp), Finset.mem_union_right _ (by simp)⟩
          · exact ⟨B1, hB1, Finset.mem_union_right _ (by simp), Finset.mem_union_right _ (by simp)⟩
          · exact ⟨B1, hB1, Finset.mem_union_right _ (by simp), Finset.mem_union_right _ (by simp)⟩
        bags_ri := hri'
        sem := by
          intro f σ
          let A_k := Finset.range n ∪ (Finset.range k).image (fun j => n + 3 * j + 2)
          have hA_eq : Finset.range n ∪ (Finset.range (k + 1)).image (fun j => n + 3 * j + 2) =
              insert (st.nv + 2) A_k := by
            ext u
            simp only [A_k, Finset.mem_union, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
            constructor
            · rintro (h | ⟨j, hj, rfl⟩)
              · exact Or.inr (Or.inl h)
              · by_cases hjk : j = k
                · subst hjk; exact Or.inl (by omega)
                · exact Or.inr (Or.inr ⟨j, by omega, rfl⟩)
            · rintro (rfl | h | ⟨j, hj, rfl⟩)
              · exact Or.inr ⟨k, by omega, by omega⟩
              · exact Or.inl h
              · exact Or.inr ⟨j, by omega, rfl⟩
          rw [hA_eq]
          let eq3Set : Finset (Fin 2 → Bool) :=
            Finset.univ.filter (fun z => eq3ValidB (σ k) (σ (st.nv + 2)) z = true)
          have hcard_eq3 : eq3Set.card = eq3Cnt (σ k) (σ (st.nv + 2)) := (countBoolFn_eq_card 2 _).symm
          have hprod : cnt st' f (insert (st.nv + 2) A_k) σ = cnt st f A_k σ * eq3Cnt (σ k) (σ (st.nv + 2)) := by
            rw [← hcard_eq3, cnt, cnt, ← Finset.card_product]
            symm
            let mkF : (Fin 2 → Bool) → Finset Nat := fun z =>
              (if z 0 then {st.nv} else ∅) ∪ (if z 1 then {st.nv + 1} else ∅) ∪ (if σ (st.nv + 2) then {st.nv + 2} else ∅)
            have hmem_mkF : ∀ z x, x ∈ mkF z ↔
                (x = st.nv ∧ z 0 = true) ∨ (x = st.nv + 1 ∧ z 1 = true) ∨ (x = st.nv + 2 ∧ σ (st.nv + 2) = true) := by
              intro z x
              simp only [mkF, Finset.mem_union]
              constructor
              · rintro ((h1 | h2) | h3)
                · split_ifs at h1 with hz
                  · exact Or.inl ⟨Finset.mem_singleton.mp h1, hz⟩
                  · exact False.elim (Finset.notMem_empty _ h1)
                · split_ifs at h2 with hz
                  · exact Or.inr (Or.inl ⟨Finset.mem_singleton.mp h2, hz⟩)
                  · exact False.elim (Finset.notMem_empty _ h2)
                · split_ifs at h3 with hz
                  · exact Or.inr (Or.inr ⟨Finset.mem_singleton.mp h3, hz⟩)
                  · exact False.elim (Finset.notMem_empty _ h3)
              · rintro (⟨rfl, hz⟩ | ⟨rfl, hz⟩ | ⟨rfl, hz⟩)
                · exact Or.inl (Or.inl (by simp [hz]))
                · exact Or.inl (Or.inr (by simp [hz]))
                · exact Or.inr (by simp [hz])
            refine Finset.card_bij (fun pr _ => pr.1 ∪ mkF pr.2) ?_ ?_ ?_
            · intro ⟨I, z⟩ hpr
              simp only [Finset.mem_product, isSets, eq3Set, Finset.mem_filter, Finset.mem_powerset,
                Finset.mem_univ, true_and, eq3ValidB, Bool.and_eq_true, Bool.not_eq_true'] at hpr
              rcases hpr with ⟨⟨hIsub, hIlive, hIind, hIA⟩, ⟨hkp, hpq⟩, hqw⟩
              have hkdec : decide (k ∈ I) = σ k := hIA k (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega)))
              have hltI : ∀ x ∈ I, x < st.nv := fun x hx => Finset.mem_range.mp (hIsub hx)
              simp only [isSets, Finset.mem_filter, Finset.mem_powerset]
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro u hu
                refine Finset.mem_range.mpr ?_
                change u < st.nv + 3
                rcases Finset.mem_union.mp hu with huI | huF
                · have := hltI u huI; omega
                · rcases (hmem_mkF z u).mp huF with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
              · intro u _
                have htag : st'.tag u = none := ihk.tag_none u
                simp [liveOf, htag]
              · intro u hu v hv hvmem
                have hInU : u ∈ I ∨ (u = st.nv ∧ z 0 = true) ∨ (u = st.nv + 1 ∧ z 1 = true) ∨ (u = st.nv + 2 ∧ σ (st.nv + 2) = true) := by
                  rcases Finset.mem_union.mp hu with h | h
                  · exact Or.inl h
                  · exact Or.inr ((hmem_mkF z u).mp h)
                have hInV : v ∈ I ∨ (v = st.nv ∧ z 0 = true) ∨ (v = st.nv + 1 ∧ z 1 = true) ∨ (v = st.nv + 2 ∧ σ (st.nv + 2) = true) := by
                  rcases Finset.mem_union.mp hvmem with h | h
                  · exact Or.inl h
                  · exact Or.inr ((hmem_mkF z v).mp h)
                rcases (hmem_st' u v).mp hv with hold | ⟨hu', hv'⟩ | ⟨hu', hv'⟩ | ⟨hu', hv'⟩ | ⟨hu', hv'⟩ | ⟨hu', hv'⟩ | ⟨hu', hv'⟩
                · have ⟨hult, hvlt⟩ := ihk.adj_lt u v hold
                  have huI : u ∈ I := by rcases hInU with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩; exact h; all_goals omega
                  have hvI : v ∈ I := by rcases hInV with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩; exact h; all_goals omega
                  exact hIind u huI v hold hvI
                · rw [hu'] at hInU; rw [hv'] at hInV
                  have hkI : k ∈ I := by rcases hInU with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩; exact h; all_goals omega
                  have hz0 : z 0 = true := by rcases hInV with h | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩; have := hltI _ h; omega; exact h; all_goals omega
                  have hsk : σ k = true := by rw [← hkdec]; exact decide_eq_true hkI
                  simp [hsk, hz0] at hkp
                · rw [hu'] at hInU; rw [hv'] at hInV
                  have hz0 : z 0 = true := by rcases hInU with h | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩; have := hltI _ h; omega; exact h; all_goals omega
                  have hkI : k ∈ I := by rcases hInV with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩; exact h; all_goals omega
                  have hsk : σ k = true := by rw [← hkdec]; exact decide_eq_true hkI
                  simp [hsk, hz0] at hkp
                · rw [hu'] at hInU; rw [hv'] at hInV
                  have hz0 : z 0 = true := by rcases hInU with h | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩; have := hltI _ h; omega; exact h; all_goals omega
                  have hz1 : z 1 = true := by rcases hInV with h | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩; have := hltI _ h; omega; omega; exact h; omega
                  simp [hz0, hz1] at hpq
                · rw [hu'] at hInU; rw [hv'] at hInV
                  have hz1 : z 1 = true := by rcases hInU with h | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩; have := hltI _ h; omega; omega; exact h; omega
                  have hz0 : z 0 = true := by rcases hInV with h | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩; have := hltI _ h; omega; exact h; all_goals omega
                  simp [hz0, hz1] at hpq
                · rw [hu'] at hInU; rw [hv'] at hInV
                  have hz1 : z 1 = true := by rcases hInU with h | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩; have := hltI _ h; omega; omega; exact h; omega
                  have hsw : σ (st.nv + 2) = true := by rcases hInV with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩; have := hltI _ h; omega; omega; omega; exact h
                  simp [hz1, hsw] at hqw
                · rw [hu'] at hInU; rw [hv'] at hInV
                  have hsw : σ (st.nv + 2) = true := by rcases hInU with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩; have := hltI _ h; omega; omega; omega; exact h
                  have hz1 : z 1 = true := by rcases hInV with h | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩; have := hltI _ h; omega; omega; exact h; omega
                  simp [hz1, hsw] at hqw
              · intro u hu
                rcases Finset.mem_insert.mp hu with rfl | huA
                · have hnotI : st.nv + 2 ∉ I := fun h => by have := hltI _ h; omega
                  have hiff : st.nv + 2 ∈ I ∪ mkF z ↔ σ (st.nv + 2) = true := by
                    simp only [Finset.mem_union, hnotI, false_or, hmem_mkF]
                    constructor
                    · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩)
                      · omega
                      · omega
                      · exact h
                    · intro h; exact Or.inr (Or.inr ⟨trivial, h⟩)
                  simp [hiff]
                · have hult : u < st.nv := by
                    simp only [A_k, Finset.mem_union, Finset.mem_image, Finset.mem_range] at huA
                    rcases huA with h | ⟨j, hj, rfl⟩ <;> omega
                  have hnotF : u ∉ mkF z := by
                    rw [hmem_mkF]; rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> omega
                  have hiff : u ∈ I ∪ mkF z ↔ u ∈ I := by simp [hnotF]
                  simp [hiff, hIA u huA]
            · intro ⟨I1, z1⟩ h1 ⟨I2, z2⟩ h2 heq
              simp only [Finset.mem_product, isSets, Finset.mem_filter, Finset.mem_powerset] at h1 h2
              have hI : I1 = I2 := by
                ext u
                have hf1 : u ∈ (I1 ∪ mkF z1) ∩ Finset.range st.nv ↔ u ∈ I1 := by
                  constructor
                  · intro h
                    rcases Finset.mem_union.mp (Finset.mem_inter.mp h).1 with hI | hF
                    · exact hI
                    · have hlt := Finset.mem_range.mp (Finset.mem_inter.mp h).2
                      rcases (hmem_mkF z1 u).mp hF with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
                  · intro h; exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h, h1.1.1 h⟩
                have hf2 : u ∈ (I2 ∪ mkF z2) ∩ Finset.range st.nv ↔ u ∈ I2 := by
                  constructor
                  · intro h
                    rcases Finset.mem_union.mp (Finset.mem_inter.mp h).1 with hI | hF
                    · exact hI
                    · have hlt := Finset.mem_range.mp (Finset.mem_inter.mp h).2
                      rcases (hmem_mkF z2 u).mp hF with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
                  · intro h; exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h, h2.1.1 h⟩
                rw [← hf1, ← hf2, heq]
              have hz : z1 = z2 := by
                ext i; fin_cases i
                · have hp1 : st.nv ∈ I1 ∪ mkF z1 ↔ z1 0 = true := by
                    have hni : st.nv ∉ I1 := fun h => by have := Finset.mem_range.mp (h1.1.1 h); omega
                    simp only [Finset.mem_union, hni, false_or, hmem_mkF]
                    exact ⟨fun h => by rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩; exact h; omega; omega, fun h => Or.inl ⟨trivial, h⟩⟩
                  have hp2 : st.nv ∈ I2 ∪ mkF z2 ↔ z2 0 = true := by
                    have hni : st.nv ∉ I2 := fun h => by have := Finset.mem_range.mp (h2.1.1 h); omega
                    simp only [Finset.mem_union, hni, false_or, hmem_mkF]
                    exact ⟨fun h => by rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩; exact h; omega; omega, fun h => Or.inl ⟨trivial, h⟩⟩
                  rw [heq] at hp1
                  have heqv : z1 0 = true ↔ z2 0 = true := hp1.symm.trans hp2
                  cases hv1 : z1 0 <;> cases hv2 : z2 0 <;> simp [hv1, hv2] at heqv ⊢
                · have hq1 : st.nv + 1 ∈ I1 ∪ mkF z1 ↔ z1 1 = true := by
                    have hni : st.nv + 1 ∉ I1 := fun h => by have := Finset.mem_range.mp (h1.1.1 h); omega
                    simp only [Finset.mem_union, hni, false_or, hmem_mkF]
                    exact ⟨fun h => by rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩; omega; exact h; omega, fun h => Or.inr (Or.inl ⟨trivial, h⟩)⟩
                  have hq2 : st.nv + 1 ∈ I2 ∪ mkF z2 ↔ z2 1 = true := by
                    have hni : st.nv + 1 ∉ I2 := fun h => by have := Finset.mem_range.mp (h2.1.1 h); omega
                    simp only [Finset.mem_union, hni, false_or, hmem_mkF]
                    exact ⟨fun h => by rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩; omega; exact h; omega, fun h => Or.inr (Or.inl ⟨trivial, h⟩)⟩
                  rw [heq] at hq1
                  have heqv : z1 1 = true ↔ z2 1 = true := hq1.symm.trans hq2
                  cases hv1 : z1 1 <;> cases hv2 : z2 1 <;> simp [hv1, hv2] at heqv ⊢
              subst hI; subst hz; rfl
            · intro J hJ
              simp only [isSets, Finset.mem_filter, Finset.mem_powerset] at hJ
              rcases hJ with ⟨hJsub, _, hJind, hJA⟩
              let I := J ∩ Finset.range st.nv
              let z : Fin 2 → Bool := ![decide (st.nv ∈ J), decide (st.nv + 1 ∈ J)]
              refine ⟨(I, z), ?_, ?_⟩
              · simp only [Finset.mem_product, isSets, eq3Set, Finset.mem_filter, Finset.mem_powerset,
                  Finset.mem_univ, true_and, eq3ValidB, Bool.and_eq_true, Bool.not_eq_true']
                refine ⟨⟨Finset.inter_subset_right, fun u _ => by
                    have htag : st.tag u = none := ihk.tag_none u
                    simp [liveOf, htag], ?_, ?_⟩, ?_⟩
                · intro u hu v hv hvmem
                  have huJ := (Finset.mem_inter.mp hu).1
                  have hvJ := (Finset.mem_inter.mp hvmem).1
                  exact hJind u huJ v ((hmem_st' u v).mpr (Or.inl hv)) hvJ
                · intro u hu
                  have hult : u < st.nv := by
                    simp only [A_k, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hu
                    rcases hu with h | ⟨j, hj, rfl⟩ <;> omega
                  simp only [I, Finset.mem_inter, Finset.mem_range, hult, and_true]
                  exact hJA u (Finset.mem_insert_of_mem hu)
                · have hkJ : decide (k ∈ J) = σ k := hJA k (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))))
                  have hwJ : decide (st.nv + 2 ∈ J) = σ (st.nv + 2) := hJA (st.nv + 2) (Finset.mem_insert_self _ _)
                  have hkp_e : st.nv ∈ st'.adj k := (hmem_st' k st.nv).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                  have hpq_e : st.nv + 1 ∈ st'.adj st.nv := (hmem_st' st.nv (st.nv + 1)).mpr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
                  have hqw_e : st.nv + 2 ∈ st'.adj (st.nv + 1) := (hmem_st' (st.nv + 1) (st.nv + 2)).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
                  refine ⟨⟨?_, ?_⟩, ?_⟩
                  · rw [← hkJ]; simp only [z, Matrix.cons_val_zero]
                    by_cases h1 : k ∈ J <;> by_cases h2 : st.nv ∈ J
                    · exact False.elim (hJind k h1 st.nv hkp_e h2)
                    all_goals simp [h1, h2]
                  · simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
                    by_cases h1 : st.nv ∈ J <;> by_cases h2 : st.nv + 1 ∈ J
                    · exact False.elim (hJind st.nv h1 (st.nv + 1) hpq_e h2)
                    all_goals simp [h1, h2]
                  · rw [← hwJ]; simp only [z, Matrix.cons_val_one, Matrix.head_cons]
                    by_cases h1 : st.nv + 1 ∈ J <;> by_cases h2 : st.nv + 2 ∈ J
                    · exact False.elim (hJind (st.nv + 1) h1 (st.nv + 2) hqw_e h2)
                    all_goals simp [h1, h2]
              · ext u
                simp only [Finset.mem_union, I, Finset.mem_inter, Finset.mem_range, hmem_mkF, z,
                  Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, decide_eq_true_eq]
                have hwJ : decide (st.nv + 2 ∈ J) = σ (st.nv + 2) := hJA (st.nv + 2) (Finset.mem_insert_self _ _)
                rw [← hwJ, decide_eq_true_eq]
                constructor
                · rintro (⟨h, _⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) <;> exact h
                · intro huJ
                  have hult : u < st.nv + 3 := Finset.mem_range.mp (hJsub huJ)
                  by_cases hlt : u < st.nv
                  · exact Or.inl ⟨huJ, hlt⟩
                  · have hcases : u = st.nv ∨ u = st.nv + 1 ∨ u = st.nv + 2 := by omega
                    rcases hcases with rfl | rfl | rfl
                    · exact Or.inr (Or.inl ⟨rfl, huJ⟩)
                    · exact Or.inr (Or.inr (Or.inl ⟨rfl, huJ⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨rfl, huJ⟩))
          change cnt st' f (insert (st.nv + 2) A_k) σ % 2 = _
          rw [hprod, mul_mod_two, ihk.sem f σ, cnt_eq3]
          have hw_eq : st.nv + 2 = n + 3 * k + 2 := by omega
          rw [hw_eq]
          have hiff : ((∀ j < k, σ (n + 3 * j + 2) = σ j) ∧ σ (n + 3 * k + 2) = σ k) ↔
              (∀ j < k + 1, σ (n + 3 * j + 2) = σ j) := by
            constructor
            · rintro ⟨h1, h2⟩ j hj
              by_cases hjk : j = k
              · subst hjk; exact h2
              · exact h1 j (by omega)
            · intro h; exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
          have hmul_ite :
              ((if ∀ j < k, σ (n + 3 * j + 2) = σ j then (1 : Nat) else 0) *
               (if σ (n + 3 * k + 2) = σ k then 1 else 0)) % 2 =
              if (∀ j < k, σ (n + 3 * j + 2) = σ j) ∧ σ (n + 3 * k + 2) = σ k then 1 else 0 := by
            by_cases h1 : ∀ j < k, σ (n + 3 * j + 2) = σ j
            · by_cases h2 : σ (n + 3 * k + 2) = σ k
              · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
              · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]
            · rw [if_neg h1, Nat.zero_mul, Nat.zero_mod, if_neg (fun h => h1 h.1)]
          rw [hmul_ite]; exact ite_nat_congr hiff }

/-- Enumerate all `2^n` words of length `n`. -/
def allWords : (n : Nat) → List (Word n)
  | 0 => [Fin.elim0]
  | n + 1 =>
    (allWords n).map (Fin.cons false) ++ (allWords n).map (Fin.cons true)

lemma allWords_length : ∀ n : Nat, (allWords n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by
    simp only [allWords, List.length_append, List.length_map, allWords_length n, pow_succ]
    omega

lemma mem_allWords : ∀ (n : Nat) (y : Word n), y ∈ allWords n
  | 0, y => by
    simp only [allWords, List.mem_singleton]
    ext i; exact Fin.elim0 i
  | n + 1, y => by
    simp only [allWords, List.mem_append, List.mem_map]
    let tail : Word n := fun i => y i.succ
    have htail : tail ∈ allWords n := mem_allWords n tail
    cases hy0 : y 0
    · left; refine ⟨tail, htail, ?_⟩
      ext i; refine Fin.cases ?_ ?_ i
      · simp [hy0]
      · intro j; simp [tail]
    · right; refine ⟨tail, htail, ?_⟩
      ext i; refine Fin.cases ?_ ?_ i
      · simp [hy0]
      · intro j; simp [tail]

/-- A circuit bundle maintaining `n` bus wires + `1` accumulator wire. -/
structure BusState (n : Nat) where
  st : State n
  bus : Fin n → Nat
  acc : Nat

def busSet {n : Nat} (bus : Fin n → Nat) : Finset Nat :=
  Finset.univ.image bus

structure BusInv {n : Nat} (bs : BusState n) (accFn : Table n → Word n → Bool) : Prop where
  wf : WellFormed bs.st (insert bs.acc (busSet bs.bus)) (n + 15)
  bus_inj : Function.Injective bs.bus
  acc_not_bus : bs.acc ∉ busSet bs.bus
  sem : ∀ (f : Table n) (σ : Nat → Bool),
    cnt bs.st f (Finset.range n ∪ insert bs.acc (busSet bs.bus)) σ % 2 =
      if (∀ j : Fin n, σ (bs.bus j) = σ j.val) ∧ σ bs.acc = accFn f (fun j => σ j.val)
      then 1 else 0

lemma card_busSet {n : Nat} (bus : Fin n → Nat) : (busSet bus).card ≤ n := by
  exact le_trans Finset.card_image_le (by simp)

/-- Start BusState: `initLoop n n` + `CONST0` for `acc`. -/
def startBus (n : Nat) : BusState n :=
  let st1 := initLoop n n
  let bus1 : Fin n → Nat := fun j => n + 3 * j.val + 2
  let st2 := attach st1 (busSet bus1) gConst0 Fin.elim0 (fun _ => false)
  { st := st2
    bus := bus1
    acc := st1.nv }

lemma startBus_nv (n : Nat) : (startBus n).st.nv = 4 * n + 3 := by
  simp only [startBus, attach, initLoop_nv]; omega

lemma startBus_inv (n : Nat) : BusInv (startBus n) (fun _ _ => false) := by
  have hi := initLoop_inv n n (le_refl n)
  let st1 := initLoop n n
  let bus1 : Fin n → Nat := fun j => n + 3 * j.val + 2
  have hbus_eq : busSet bus1 = (Finset.range n).image (fun j => n + 3 * j + 2) := by
    ext u; simp only [busSet, bus1, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨fun ⟨j, hj⟩ => ⟨j.val, j.isLt, hj⟩, fun ⟨j, hj, h⟩ => ⟨⟨j, hj⟩, h⟩⟩
  have hinitBag : initBag n n = busSet bus1 := by
    rw [hbus_eq]; simp [initBag]
  have hwf1 : WellFormed st1 (busSet bus1) (n + 15) :=
    { n_le := by rw [hi.nv_eq]; omega
      act_sub := by
        rw [hbus_eq]; intro u hu
        simp only [Finset.mem_image, Finset.mem_range] at hu
        rcases hu with ⟨j, hj, rfl⟩
        exact Finset.mem_range.mpr (by rw [hi.nv_eq]; omega)
      disj := by
        rw [hbus_eq, Finset.disjoint_left]
        intro u h1 h2
        simp only [Finset.mem_range] at h1
        simp only [Finset.mem_image, Finset.mem_range] at h2
        rcases h2 with ⟨j, _, rfl⟩; omega
      adj_lt := hi.adj_lt
      no_loop := hi.no_loop
      symm := hi.symm
      deg_le := hi.deg_le
      act_deg := by
        rw [hbus_eq]; intro u hu
        simp only [Finset.mem_image, Finset.mem_range] at hu
        rcases hu with ⟨j, hj, rfl⟩; exact hi.w_deg j hj
      in_deg := hi.in_deg_done
      bip := hi.bip
      act_shore := by
        rw [hbus_eq]; intro u hu
        simp only [Finset.mem_image, Finset.mem_range] at hu
        rcases hu with ⟨j, hj, rfl⟩; exact hi.w_shore j hj
      in_shore := hi.in_shore
      act_tag := fun u _ => hi.tag_none u
      in_tag := fun u _ => hi.tag_none u
      bags_ne := hi.bags_ne
      bags_head := hi.bags_head
      bags_last := hi.bags_last.trans hinitBag
      bags_sub := hi.bags_sub
      bags_card := fun B hB => le_trans (hi.bags_card B hB) (by omega)
      bags_covV := hi.bags_covV
      bags_covE := hi.bags_covE
      bags_ri := hi.bags_ri }
  have hact_eq : (busSet bus1 \ portsFinset (Fin.elim0 : Fin 0 → Nat)) ∪ outFinset st1.nv 1 =
      insert st1.nv (busSet bus1) := by
    ext u
    simp only [portsFinset, outFinset, Finset.mem_union, Finset.mem_sdiff, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_insert, IsEmpty.exists_iff,
      not_false_eq_true, and_true]
    constructor
    · rintro (h | ⟨k, hk, rfl⟩)
      · exact Or.inr h
      · have : k = 0 := by omega
        subst this; exact Or.inl (by omega)
    · rintro (rfl | h)
      · exact Or.inr ⟨0, by omega, by omega⟩
      · exact Or.inl h
  have hwf2 := attach_wellFormed st1 (busSet bus1) gConst0 valid_gConst0 Fin.elim0 (fun _ => false)
    hwf1 (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
    (by have := card_busSet bus1; omega)
  rw [hact_eq] at hwf2
  refine
    { wf := hwf2
      bus_inj := fun a b h => Fin.ext (by simp [startBus, bus1] at h; omega)
      acc_not_bus := by
        intro h
        dsimp only [startBus] at h
        have := Finset.mem_range.mp (hwf1.act_sub h)
        dsimp only [st1] at this; omega
      sem := by
        intro f σ
        dsimp only [startBus]
        let val0 : Word n → Nat → Bool := fun a w =>
          if h : (w - n) / 3 < n then a ⟨(w - n) / 3, h⟩ else false
        have hval_inv2 : ∀ σ' : Nat → Bool,
            cnt st1 f (Finset.range n ∪ busSet bus1) σ' % 2 =
              if True ∧ (∀ w ∈ busSet bus1, σ' w = val0 (fun j => σ' j.val) w) then 1 else 0 := by
          intro σ'
          rw [hbus_eq, hi.sem f σ']
          refine ite_nat_congr ?_
          simp only [true_and, Finset.mem_image, Finset.mem_range, val0]
          constructor
          · rintro h _ ⟨j, hj, rfl⟩
            have hdiv : (n + 3 * j + 2 - n) / 3 = j := by omega
            simp [hdiv, hj, h j hj]
          · intro h j hj
            have := h (n + 3 * j + 2) ⟨j, hj, rfl⟩
            have hdiv : (n + 3 * j + 2 - n) / 3 = j := by omega
            simp [hdiv, hj] at this; exact this
        have hmod := attach_mod2 st1 (busSet bus1) gConst0 valid_gConst0 Fin.elim0 (fun _ => false)
          hwf1 (fun a => Fin.elim0 a) (fun a => Fin.elim0 a) f val0 (fun _ => True)
          hval_inv2 (fun _ _ out => out 0 = false) cnt_gConst0 σ
        rw [hact_eq] at hmod
        dsimp only at hmod
        change cnt (attach st1 (busSet bus1) gConst0 Fin.elim0 (fun _ => false)) f
          (Finset.range n ∪ insert st1.nv (busSet bus1)) σ % 2 = _
        rw [hmod]
        refine ite_nat_congr ?_
        simp only [true_and, Fin.val_zero, Nat.add_zero]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨fun j => ?_, h2⟩
          have hmem : bus1 j ∈ busSet bus1 \ portsFinset (Fin.elim0 : Fin 0 → Nat) := by
            refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
            simp [portsFinset]
          have := h1 (bus1 j) hmem
          have hdiv : (bus1 j - n) / 3 = j.val := by simp [bus1]; omega
          simp only [val0, hdiv, j.isLt, dite_true] at this
          exact this
        · rintro ⟨h1, h2⟩
          refine ⟨fun w hw => ?_, h2⟩
          have hmem := (Finset.mem_sdiff.mp hw).1
          simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hmem
          rcases hmem with ⟨j, rfl⟩
          have hdiv : (bus1 j - n) / 3 = j.val := by simp [bus1]; omega
          simp only [val0, hdiv, j.isLt, dite_true]
          exact h1 j }

/-- Inner bit-matching loop: maintains `bus`, `acc`, and running match wire `m`. -/
structure MatchState (n : Nat) where
  st : State n
  bus : Fin n → Nat
  acc : Nat
  m : Nat

structure MatchInv {n : Nat} (ms : MatchState n) (accFn mFn : Table n → Word n → Bool) : Prop where
  wf : WellFormed ms.st (insert ms.m (insert ms.acc (busSet ms.bus))) (n + 15)
  bus_inj : Function.Injective ms.bus
  acc_not_bus : ms.acc ∉ busSet ms.bus
  m_not_bus : ms.m ∉ busSet ms.bus
  m_ne_acc : ms.m ≠ ms.acc
  sem : ∀ (f : Table n) (σ : Nat → Bool),
    cnt ms.st f (Finset.range n ∪ insert ms.m (insert ms.acc (busSet ms.bus))) σ % 2 =
      if (∀ j : Fin n, σ (ms.bus j) = σ j.val) ∧
         σ ms.acc = accFn f (fun j => σ j.val) ∧
         σ ms.m = mFn f (fun j => σ j.val)
      then 1 else 0

/-- Helper: build a total valuation function on `active` from `bus`, `acc`, `m`, and optionally one extra wire. -/
noncomputable def valOfBus {n : Nat} (bus : Fin n → Nat) (acc : Nat) (accVal : Bool)
    (extra : List (Nat × Bool)) (a : Word n) (u : Nat) : Bool :=
  match extra.find? (fun p => p.1 == u) with
  | some p => p.2
  | none =>
    if u = acc then accVal
    else if h : ∃ j : Fin n, bus j = u then a (Classical.choose h)
    else false

lemma valOfBus_bus {n : Nat} (bus : Fin n → Nat) (hinj : Function.Injective bus)
    (acc : Nat) (hacc : acc ∉ busSet bus) (accVal : Bool)
    (extra : List (Nat × Bool)) (hex : ∀ p ∈ extra, p.1 ∉ busSet bus)
    (a : Word n) (j : Fin n) :
    valOfBus bus acc accVal extra a (bus j) = a j := by
  have hfind : extra.find? (fun p => p.1 == bus j) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp only [beq_iff_eq]
    intro heq
    exact hex p hp (heq ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hne : bus j ≠ acc := fun heq => hacc (heq ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hexj : ∃ j' : Fin n, bus j' = bus j := ⟨j, rfl⟩
  simp only [valOfBus, hfind, if_neg hne, dif_pos hexj]
  rw [hinj (Classical.choose_spec hexj)]

lemma valOfBus_acc {n : Nat} (bus : Fin n → Nat) (acc : Nat) (accVal : Bool)
    (extra : List (Nat × Bool)) (hex : ∀ p ∈ extra, p.1 ≠ acc) (a : Word n) :
    valOfBus bus acc accVal extra a acc = accVal := by
  have hfind : extra.find? (fun p => p.1 == acc) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp only [beq_iff_eq]
    exact hex p hp
  simp only [valOfBus, hfind, ↓reduceIte]

/-- Step one bit `j : Fin n` in the match loop: COPY `bus j`, optional NOT if `y j = false`, AND with `m`. -/
def bitStep {n : Nat} (ms : MatchState n) (y : Word n) (j : Fin n) : MatchState n :=
  let act0 := insert ms.m (insert ms.acc (busSet ms.bus))
  let st1 := attach ms.st act0 gCopy ![ms.bus j] y
  let bus1 : Fin n → Nat := Function.update ms.bus j ms.st.nv
  let copyW := ms.st.nv + 1
  let act1 := insert copyW (insert ms.m (insert ms.acc (busSet bus1)))
  let st2 := if y j then st1 else attach st1 act1 gNot ![copyW] y
  let litW := if y j then copyW else st1.nv
  let act2 := insert litW (insert ms.m (insert ms.acc (busSet bus1)))
  let st3 := attach st2 act2 gAnd ![ms.m, litW] y
  { st := st3
    bus := bus1
    acc := ms.acc
    m := st2.nv }

lemma bitStep_nv_le {n : Nat} (ms : MatchState n) (y : Word n) (j : Fin n) :
    (bitStep ms y j).st.nv ≤ ms.st.nv + 23 := by
  simp only [bitStep, attach]
  cases y j <;> simp <;> omega

lemma busSet_update {n : Nat} (bus : Fin n → Nat) (hinj : Function.Injective bus)
    (j : Fin n) (v : Nat) :
    busSet (Function.update bus j v) = insert v (busSet bus \ {bus j}) := by
  ext u
  simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hij : i = j
    · subst hij; simp
    · simp only [Function.update_of_ne hij]
      exact Or.inr ⟨⟨i, rfl⟩, fun h => hij (hinj h)⟩
  · rintro (rfl | ⟨⟨i, rfl⟩, hne⟩)
    · exact ⟨j, by simp⟩
    · refine ⟨i, ?_⟩
      have hij : i ≠ j := fun h => hne (by subst h; rfl)
      simp [hij]

lemma bitStep_inv {n : Nat} (ms : MatchState n) (y : Word n) (j : Fin n)
    (accFn mFn : Table n → Word n → Bool) (hinv : MatchInv ms accFn mFn) :
    MatchInv (bitStep ms y j) accFn
      (fun f a => mFn f a && decide (a j = y j)) := by
  let act0 := insert ms.m (insert ms.acc (busSet ms.bus))
  let bus1 : Fin n → Nat := Function.update ms.bus j ms.st.nv
  let copyW := ms.st.nv + 1
  let act1 := insert copyW (insert ms.m (insert ms.acc (busSet bus1)))
  have hlt_act0 : ∀ u ∈ act0, u < ms.st.nv := fun u hu => Finset.mem_range.mp (hinv.wf.act_sub hu)
  have hbus1_inj : Function.Injective bus1 := by
    intro a b h
    by_cases ha : a = j <;> by_cases hb : b = j
    · rw [ha, hb]
    · simp only [bus1, ha, Function.update_self, Function.update_of_ne hb] at h
      have := hlt_act0 (ms.bus b) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩)))
      omega
    · simp only [bus1, hb, Function.update_self, Function.update_of_ne ha] at h
      have := hlt_act0 (ms.bus a) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)))
      omega
    · simp only [bus1, Function.update_of_ne ha, Function.update_of_ne hb] at h
      exact hinv.bus_inj h
  have hacc_not1 : ms.acc ∉ busSet bus1 := by
    rw [busSet_update ms.bus hinv.bus_inj j ms.st.nv]
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    rintro (heq | ⟨h1, _⟩)
    · have := hlt_act0 ms.acc (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)); omega
    · exact hinv.acc_not_bus h1
  have hm_not1 : ms.m ∉ busSet bus1 := by
    rw [busSet_update ms.bus hinv.bus_inj j ms.st.nv]
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    rintro (heq | ⟨h1, _⟩)
    · have := hlt_act0 ms.m (Finset.mem_insert_self _ _); omega
    · exact hinv.m_not_bus h1
  have hcopy_not1 : copyW ∉ busSet bus1 := by
    rw [busSet_update ms.bus hinv.bus_inj j ms.st.nv]
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    rintro (heq | ⟨h1, _⟩)
    · omega
    · have := hlt_act0 copyW (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h1)); omega
  have hcopy_ne_acc : copyW ≠ ms.acc := by
    have := hlt_act0 ms.acc (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)); omega
  have hcopy_ne_m : copyW ≠ ms.m := by
    have := hlt_act0 ms.m (Finset.mem_insert_self _ _); omega
  -- Step 1: COPY (bus j) -> (st.nv, st.nv + 1)
  let st1 := attach ms.st act0 gCopy ![ms.bus j] y
  have hp1_inj : Function.Injective (![ms.bus j] : Fin 1 → Nat) := fun a b _ => Subsingleton.elim a b
  have hp1_mem : ∀ k : Fin 1, (![ms.bus j] : Fin 1 → Nat) k ∈ act0 := fun k => by
    fin_cases k
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  have hact1_eq : (act0 \ portsFinset ![ms.bus j]) ∪ outFinset ms.st.nv 2 = act1 := by
    have hp1 : portsFinset (![ms.bus j] : Fin 1 → Nat) = {ms.bus j} := by
      ext u; simp [portsFinset]
    have hout1 : outFinset ms.st.nv 2 = {ms.st.nv, copyW} := by
      ext u; simp only [outFinset, Finset.mem_image, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, copyW]
      constructor
      · rintro ⟨k, hk, rfl⟩; have : k = 0 ∨ k = 1 := by omega
        rcases this with rfl | rfl <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, by omega, by omega⟩
        · exact ⟨1, by omega, by omega⟩
    dsimp only [act1]; rw [hp1, hout1, busSet_update ms.bus hinv.bus_inj j ms.st.nv]
    have hm_ne_bj : ms.m ≠ ms.bus j := fun h => hinv.m_not_bus (h ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    have ha_ne_bj : ms.acc ≠ ms.bus j := fun h => hinv.acc_not_bus (h ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    ext u; simp only [act0, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨rfl | rfl | h, hne⟩ | rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hne⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inl rfl
    · rintro (rfl | rfl | rfl | rfl | ⟨h, hne⟩)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨Or.inl rfl, hm_ne_bj⟩
      · exact Or.inl ⟨Or.inr (Or.inl rfl), ha_ne_bj⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ⟨Or.inr (Or.inr h), hne⟩
  have hact0_card : act0.card ≤ n + 2 := by
    have := card_busSet ms.bus
    exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
      (le_trans (Finset.card_insert_le _ _) (by omega)) 1)
  have hwf1 := attach_wellFormed ms.st act0 gCopy valid_gCopy ![ms.bus j] y
    hinv.wf hp1_inj hp1_mem (by omega)
  rw [hact1_eq] at hwf1
  have hsem1 : ∀ (f : Table n) (σ : Nat → Bool),
      cnt st1 f (Finset.range n ∪ act1) σ % 2 =
        if (∀ i : Fin n, σ (bus1 i) = σ i.val) ∧
           σ ms.acc = accFn f (fun i => σ i.val) ∧
           σ ms.m = mFn f (fun i => σ i.val) ∧
           σ copyW = σ j.val
        then 1 else 0 := by
    intro f σ
    let val0 : Word n → Nat → Bool := fun a u =>
      valOfBus ms.bus ms.acc (accFn f a) [(ms.m, mFn f a)] a u
    have hinv0 : ∀ σ' : Nat → Bool,
        cnt ms.st f (Finset.range n ∪ act0) σ' % 2 =
          if True ∧ (∀ w ∈ act0, σ' w = val0 (fun i => σ' i.val) w) then 1 else 0 := by
      intro σ'
      rw [hinv.sem f σ']
      let a : Word n := fun i => σ' i.val
      have hiff : ((∀ i : Fin n, σ' (ms.bus i) = a i) ∧ σ' ms.acc = accFn f a ∧ σ' ms.m = mFn f a) ↔
          (True ∧ ∀ w ∈ act0, σ' w = val0 a w) := by
        simp only [true_and, act0, Finset.mem_insert]
        constructor
        · rintro ⟨hB, hA, hM⟩ w (rfl | rfl | hw)
          · simp [val0, valOfBus] ; exact hM
          · dsimp only [val0]; rw [valOfBus_acc ms.bus ms.acc (accFn f a) [(ms.m, mFn f a)] (by simp [hinv.m_ne_acc]) a]; exact hA
          · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
            rcases hw with ⟨i, rfl⟩
            dsimp only [val0]; rw [valOfBus_bus ms.bus hinv.bus_inj ms.acc hinv.acc_not_bus (accFn f a)
              [(ms.m, mFn f a)] (by simp [hinv.m_not_bus]) a i]
            exact hB i
        · intro h
          refine ⟨fun i => ?_, ?_, ?_⟩
          · have := h (ms.bus i) (Or.inr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
            dsimp only [val0] at this; rw [valOfBus_bus ms.bus hinv.bus_inj ms.acc hinv.acc_not_bus (accFn f a)
              [(ms.m, mFn f a)] (by simp [hinv.m_not_bus]) a i] at this
            exact this
          · have := h ms.acc (Or.inr (Or.inl rfl))
            dsimp only [val0] at this; rw [valOfBus_acc ms.bus ms.acc (accFn f a) [(ms.m, mFn f a)] (by simp [hinv.m_ne_acc]) a] at this
            exact this
          · have := h ms.m (Or.inl rfl)
            simp [val0, valOfBus] at this; exact this
      exact ite_nat_congr hiff
    have hmod := attach_mod2 ms.st act0 gCopy valid_gCopy ![ms.bus j] y hinv.wf hp1_inj hp1_mem f
      val0 (fun _ => True) hinv0 (fun _ inp out => out 0 = inp 0 ∧ out 1 = inp 0) cnt_gCopy σ
    rw [hact1_eq] at hmod
    change cnt st1 f (Finset.range n ∪ act1) σ % 2 = _
    dsimp only at hmod; rw [hmod]
    let a : Word n := fun i => σ i.val
    have hval_bj : val0 a (ms.bus j) = a j :=
      valOfBus_bus ms.bus hinv.bus_inj ms.acc hinv.acc_not_bus (accFn f a)
        [(ms.m, mFn f a)] (by simp [hinv.m_not_bus]) a j
    have hp1 : portsFinset (![ms.bus j] : Fin 1 → Nat) = {ms.bus j} := by ext u; simp [portsFinset]
    have hiff : (True ∧
        (∀ w ∈ act0 \ portsFinset ![ms.bus j], σ w = val0 a w) ∧
        (σ (ms.st.nv + (0 : Fin 2).val) = val0 a (ms.bus j) ∧
         σ (ms.st.nv + (1 : Fin 2).val) = val0 a (ms.bus j))) ↔
        ((∀ i : Fin n, σ (bus1 i) = a i) ∧ σ ms.acc = accFn f a ∧ σ ms.m = mFn f a ∧ σ copyW = a j) := by
      simp only [true_and, Fin.val_zero, Nat.add_zero, Fin.val_one, hval_bj, hp1]
      have hm_ne_bj : ms.m ≠ ms.bus j := fun h => hinv.m_not_bus (h ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      have ha_ne_bj : ms.acc ≠ ms.bus j := fun h => hinv.acc_not_bus (h ▸ Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      constructor
      · rintro ⟨hrest, hnv0, hcp⟩
        refine ⟨fun i => ?_, ?_, ?_, hcp⟩
        · by_cases hij : i = j
          · subst hij; simp [bus1, hnv0]
          · simp only [bus1, Function.update_of_ne hij]
            have hmem : ms.bus i ∈ act0 \ {ms.bus j} := by
              refine Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)), ?_⟩
              simp only [Finset.mem_singleton]
              exact fun h => hij (hinv.bus_inj h)
            have := hrest (ms.bus i) hmem
            dsimp only [val0] at this; rw [valOfBus_bus ms.bus hinv.bus_inj ms.acc hinv.acc_not_bus (accFn f a)
              [(ms.m, mFn f a)] (by simp [hinv.m_not_bus]) a i] at this
            exact this
        · have := hrest ms.acc (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), by simp [ha_ne_bj]⟩)
          dsimp only [val0] at this; rw [valOfBus_acc ms.bus ms.acc (accFn f a) [(ms.m, mFn f a)] (by simp [hinv.m_ne_acc]) a] at this
          exact this
        · have := hrest ms.m (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, by simp [hm_ne_bj]⟩)
          simp [val0, valOfBus] at this; exact this
      · rintro ⟨hB, hA, hM, hcp⟩
        refine ⟨fun w hw => ?_, ?_, hcp⟩
        · rcases Finset.mem_sdiff.mp hw with ⟨hw0, hne⟩
          simp only [Finset.mem_singleton] at hne
          simp only [act0, Finset.mem_insert] at hw0
          rcases hw0 with rfl | rfl | hwB
          · simp [val0, valOfBus]; exact hM
          · dsimp only [val0]; rw [valOfBus_acc ms.bus ms.acc (accFn f a) [(ms.m, mFn f a)] (by simp [hinv.m_ne_acc]) a]; exact hA
          · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hwB
            rcases hwB with ⟨i, rfl⟩
            have hij : i ≠ j := fun h => hne (by subst h; rfl)
            dsimp only [val0]; rw [valOfBus_bus ms.bus hinv.bus_inj ms.acc hinv.acc_not_bus (accFn f a)
              [(ms.m, mFn f a)] (by simp [hinv.m_not_bus]) a i]
            have := hB i; simp [bus1, hij] at this; exact this
        · have := hB j; simp [bus1] at this; exact this
    exact ite_nat_congr hiff
  -- Step 2: Optional NOT on copyW if y j = false
  let st2 := if y j then st1 else attach st1 act1 gNot ![copyW] y
  let litW := if y j then copyW else st1.nv
  let act2 := insert litW (insert ms.m (insert ms.acc (busSet bus1)))
  have hact1_card : act1.card ≤ n + 3 := by
    have := card_busSet bus1
    exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
      (le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
        (le_trans (Finset.card_insert_le _ _) (by omega)) 1)) 1)
  have hstep2 : WellFormed st2 act2 (n + 15) ∧
      litW ∉ busSet bus1 ∧ litW ≠ ms.acc ∧ litW ≠ ms.m ∧
      ∀ (f : Table n) (σ : Nat → Bool),
        cnt st2 f (Finset.range n ∪ act2) σ % 2 =
          if (∀ i : Fin n, σ (bus1 i) = σ i.val) ∧
             σ ms.acc = accFn f (fun i => σ i.val) ∧
             σ ms.m = mFn f (fun i => σ i.val) ∧
             σ litW = decide (σ j.val = y j)
          then 1 else 0 := by
    cases hyj : y j
    · -- y j = false: attach gNot
      simp only [st2, litW, act2, hyj, Bool.false_eq_true, ↓reduceIte]
      have hact2_eq : (act1 \ portsFinset ![copyW]) ∪ outFinset st1.nv 1 =
          insert st1.nv (insert ms.m (insert ms.acc (busSet bus1))) := by
        have hp : portsFinset (![copyW] : Fin 1 → Nat) = {copyW} := by ext u; simp [portsFinset]
        have hout : outFinset st1.nv 1 = {st1.nv} := by
          ext u; simp only [outFinset, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
          exact ⟨fun ⟨k, hk, h⟩ => by omega,
                 fun h => ⟨0, by omega, by omega⟩⟩
        rw [hp, hout]
        ext u; simp only [act1, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (⟨h1 | h2 | h3 | h4, hne⟩ | rfl)
          · exact False.elim (hne h1)
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr h4))
          · exact Or.inl rfl
        · rintro (rfl | rfl | rfl | h)
          · exact Or.inr rfl
          · exact Or.inl ⟨Or.inr (Or.inl rfl), hcopy_ne_m.symm⟩
          · exact Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), hcopy_ne_acc.symm⟩
          · exact Or.inl ⟨Or.inr (Or.inr (Or.inr h)), fun heq => hcopy_not1 (heq ▸ h)⟩
      have hwf2 := attach_wellFormed st1 act1 gNot valid_gNot ![copyW] y
        hwf1 (fun a b _ => Subsingleton.elim a b)
        (fun k => by fin_cases k; exact Finset.mem_insert_self _ _) (by omega)
      rw [hact2_eq] at hwf2
      have hlt_act1 : ∀ u ∈ act1, u < st1.nv := fun u hu => Finset.mem_range.mp (hwf1.act_sub hu)
      refine ⟨hwf2, ?_, ?_, ?_, ?_⟩
      · intro h; have := hlt_act1 st1.nv (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))); omega
      · have := hlt_act1 ms.acc (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))); omega
      · have := hlt_act1 ms.m (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)); omega
      · intro f σ
        let val1 : Word n → Nat → Bool := fun a u =>
          valOfBus bus1 ms.acc (accFn f a) [(copyW, a j), (ms.m, mFn f a)] a u
        have hinv1 : ∀ σ' : Nat → Bool,
            cnt st1 f (Finset.range n ∪ act1) σ' % 2 =
              if True ∧ (∀ w ∈ act1, σ' w = val1 (fun i => σ' i.val) w) then 1 else 0 := by
          intro σ'; rw [hsem1 f σ']
          let a : Word n := fun i => σ' i.val
          have hiff : ((∀ i : Fin n, σ' (bus1 i) = a i) ∧ σ' ms.acc = accFn f a ∧ σ' ms.m = mFn f a ∧ σ' copyW = a j) ↔
              (True ∧ ∀ w ∈ act1, σ' w = val1 a w) := by
            simp only [true_and, act1, Finset.mem_insert]
            constructor
            · rintro ⟨hB, hA, hM, hC⟩ w (rfl | rfl | rfl | hw)
              · simp [val1, valOfBus]; exact hC
              · simp [val1, valOfBus, hcopy_ne_m]; exact hM
              · dsimp only [val1]; rw [valOfBus_acc bus1 ms.acc (accFn f a) _ (by simp [hcopy_ne_acc, hinv.m_ne_acc]) a]; exact hA
              · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
                rcases hw with ⟨i, rfl⟩
                dsimp only [val1]; rw [valOfBus_bus bus1 hbus1_inj ms.acc hacc_not1 (accFn f a) _
                  (by simp [hcopy_not1, hm_not1]) a i]
                exact hB i
            · intro h
              refine ⟨fun i => ?_, ?_, ?_, ?_⟩
              · have := h (bus1 i) (Or.inr (Or.inr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))))
                dsimp only [val1] at this; rw [valOfBus_bus bus1 hbus1_inj ms.acc hacc_not1 (accFn f a) _
                  (by simp [hcopy_not1, hm_not1]) a i] at this; exact this
              · have := h ms.acc (Or.inr (Or.inr (Or.inl rfl)))
                dsimp only [val1] at this; rw [valOfBus_acc bus1 ms.acc (accFn f a) _ (by simp [hcopy_ne_acc, hinv.m_ne_acc]) a] at this; exact this
              · have := h ms.m (Or.inr (Or.inl rfl))
                simp [val1, valOfBus, hcopy_ne_m] at this; exact this
              · have := h copyW (Or.inl rfl)
                simp [val1, valOfBus] at this; exact this
          exact ite_nat_congr hiff
        have hmod := attach_mod2 st1 act1 gNot valid_gNot ![copyW] y hwf1
          (fun a b _ => Subsingleton.elim a b)
          (fun k => by fin_cases k; exact Finset.mem_insert_self _ _)
          f val1 (fun _ => True) hinv1 (fun _ inp out => out 0 = !inp 0) cnt_gNot σ
        rw [hact2_eq] at hmod; dsimp only at hmod; rw [hmod]
        let a : Word n := fun i => σ i.val
        have hvc : val1 a copyW = a j := by simp [val1, valOfBus]
        have hp : portsFinset (![copyW] : Fin 1 → Nat) = {copyW} := by ext u; simp [portsFinset]
        have hiff : (True ∧
            (∀ w ∈ act1 \ portsFinset ![copyW], σ w = val1 a w) ∧
            σ (st1.nv + (0 : Fin 1).val) = !val1 a copyW) ↔
            ((∀ i : Fin n, σ (bus1 i) = a i) ∧ σ ms.acc = accFn f a ∧ σ ms.m = mFn f a ∧
             σ st1.nv = decide (a j = false)) := by
          simp only [true_and, Fin.val_zero, Nat.add_zero, hvc, hp]
          have hdec : (!a j) = decide (a j = false) := by cases a j <;> rfl
          rw [hdec]
          constructor
          · rintro ⟨hrest, hlit⟩
            refine ⟨fun i => ?_, ?_, ?_, hlit⟩
            · have hmem : bus1 i ∈ act1 \ {copyW} := Finset.mem_sdiff.mpr
                ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                  (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))),
                 fun h => hcopy_not1 (Finset.mem_singleton.mp h ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
              have := hrest _ hmem
              dsimp only [val1] at this; rw [valOfBus_bus bus1 hbus1_inj ms.acc hacc_not1 (accFn f a) _
                (by simp [hcopy_not1, hm_not1]) a i] at this; exact this
            · have := hrest ms.acc (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), by simp [hcopy_ne_acc.symm]⟩)
              dsimp only [val1] at this; rw [valOfBus_acc bus1 ms.acc (accFn f a) _ (by simp [hcopy_ne_acc, hinv.m_ne_acc]) a] at this; exact this
            · have := hrest ms.m (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), by simp [hcopy_ne_m.symm]⟩)
              simp [val1, valOfBus, hcopy_ne_m] at this; exact this
          · rintro ⟨hB, hA, hM, hlit⟩
            refine ⟨fun w hw => ?_, hlit⟩
            rcases Finset.mem_sdiff.mp hw with ⟨hw1, hne⟩
            simp only [Finset.mem_singleton] at hne
            simp only [act1, Finset.mem_insert] at hw1
            rcases hw1 with rfl | rfl | rfl | hwB
            · exact False.elim (hne rfl)
            · simp [val1, valOfBus, hcopy_ne_m]; exact hM
            · dsimp only [val1]; rw [valOfBus_acc bus1 ms.acc (accFn f a) _ (by simp [hcopy_ne_acc, hinv.m_ne_acc]) a]; exact hA
            · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hwB
              rcases hwB with ⟨i, rfl⟩
              dsimp only [val1]; rw [valOfBus_bus bus1 hbus1_inj ms.acc hacc_not1 (accFn f a) _
                (by simp [hcopy_not1, hm_not1]) a i]; exact hB i
        exact ite_nat_congr hiff
    · -- y j = true: st2 = st1, litW = copyW
      simp only [st2, litW, act2, hyj, ↓reduceIte]
      refine ⟨hwf1, hcopy_not1, hcopy_ne_acc, hcopy_ne_m, fun f σ => ?_⟩
      refine (hsem1 f σ).trans (ite_nat_congr ?_)
      simp
  rcases hstep2 with ⟨hwf2, hlit_not1, hlit_ne_acc, hlit_ne_m, hsem2⟩
  -- Step 3: AND (m, litW) -> st2.nv
  let st3 := attach st2 act2 gAnd ![ms.m, litW] y
  have hact2_card : act2.card ≤ n + 3 := by
    have := card_busSet bus1
    exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
      (le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
        (le_trans (Finset.card_insert_le _ _) (by omega)) 1)) 1)
  have hp3_inj : Function.Injective (![ms.m, litW] : Fin 2 → Nat) := by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [hlit_ne_m.symm]
  have hp3_mem : ∀ k : Fin 2, (![ms.m, litW] : Fin 2 → Nat) k ∈ act2 := by
    intro k; fin_cases k
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_self _ _
  have hact3_eq : (act2 \ portsFinset ![ms.m, litW]) ∪ outFinset st2.nv 1 =
      insert st2.nv (insert ms.acc (busSet bus1)) := by
    have hp : portsFinset (![ms.m, litW] : Fin 2 → Nat) = {ms.m, litW} := by
      ext u; simp only [portsFinset, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨k, rfl⟩; fin_cases k <;> simp
      · rintro (rfl | rfl); exact ⟨0, rfl⟩; exact ⟨1, rfl⟩
    have hout : outFinset st2.nv 1 = {st2.nv} := by
      ext u; simp only [outFinset, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
      exact ⟨fun ⟨k, hk, h⟩ => by omega,
             fun h => ⟨0, by omega, by omega⟩⟩
    rw [hp, hout]
    ext u; simp only [act2, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h1 | h2 | h3 | h4, hne⟩ | rfl)
      · exact False.elim (hne (Or.inr h1))
      · exact False.elim (hne (Or.inl h2))
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr h4)
      · exact Or.inl rfl
    · rintro (rfl | rfl | h)
      · exact Or.inr rfl
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), by push_neg; exact ⟨hinv.m_ne_acc.symm, hlit_ne_acc.symm⟩⟩
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inr h)), by
          push_neg; exact ⟨fun heq => hm_not1 (heq ▸ h), fun heq => hlit_not1 (heq ▸ h)⟩⟩
  have hwf3 := attach_wellFormed st2 act2 gAnd valid_gAnd ![ms.m, litW] y hwf2 hp3_inj hp3_mem (by omega)
  rw [hact3_eq] at hwf3
  have hlt_act2 : ∀ u ∈ act2, u < st2.nv := fun u hu => Finset.mem_range.mp (hwf2.act_sub hu)
  refine
    { wf := hwf3
      bus_inj := hbus1_inj
      acc_not_bus := hacc_not1
      m_not_bus := fun h => by
        change st2.nv ∈ busSet bus1 at h
        have := hlt_act2 st2.nv (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
        omega
      m_ne_acc := by
        change st2.nv ≠ ms.acc
        have := hlt_act2 ms.acc (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        omega
      sem := by
        intro f σ
        let val2 : Word n → Nat → Bool := fun a u =>
          valOfBus bus1 ms.acc (accFn f a) [(litW, decide (a j = y j)), (ms.m, mFn f a)] a u
        have hinv2 : ∀ σ' : Nat → Bool,
            cnt st2 f (Finset.range n ∪ act2) σ' % 2 =
              if True ∧ (∀ w ∈ act2, σ' w = val2 (fun i => σ' i.val) w) then 1 else 0 := by
          intro σ'; rw [hsem2 f σ']
          let a : Word n := fun i => σ' i.val
          have hiff : ((∀ i : Fin n, σ' (bus1 i) = a i) ∧ σ' ms.acc = accFn f a ∧
              σ' ms.m = mFn f a ∧ σ' litW = decide (a j = y j)) ↔
              (True ∧ ∀ w ∈ act2, σ' w = val2 a w) := by
            simp only [true_and, act2, Finset.mem_insert]
            constructor
            · rintro ⟨hB, hA, hM, hL⟩ w (rfl | rfl | rfl | hw)
              · simp [val2, valOfBus]; exact hL
              · simp [val2, valOfBus, hlit_ne_m]; exact hM
              · dsimp only [val2]; rw [valOfBus_acc bus1 ms.acc (accFn f a) _ (by simp [hlit_ne_acc, hinv.m_ne_acc]) a]; exact hA
              · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
                rcases hw with ⟨i, rfl⟩
                dsimp only [val2]; rw [valOfBus_bus bus1 hbus1_inj ms.acc hacc_not1 (accFn f a) _
                  (by simp [hlit_not1, hm_not1]) a i]; exact hB i
            · intro h
              refine ⟨fun i => ?_, ?_, ?_, ?_⟩
              · have := h (bus1 i) (Or.inr (Or.inr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))))
                dsimp only [val2] at this; rw [valOfBus_bus bus1 hbus1_inj ms.acc hacc_not1 (accFn f a) _
                  (by simp [hlit_not1, hm_not1]) a i] at this; exact this
              · have := h ms.acc (Or.inr (Or.inr (Or.inl rfl)))
                dsimp only [val2] at this; rw [valOfBus_acc bus1 ms.acc (accFn f a) _ (by simp [hlit_ne_acc, hinv.m_ne_acc]) a] at this; exact this
              · have := h ms.m (Or.inr (Or.inl rfl))
                simp [val2, valOfBus, hlit_ne_m] at this; exact this
              · have := h litW (Or.inl rfl)
                simp [val2, valOfBus] at this; exact this
          exact ite_nat_congr hiff
        have hmod := attach_mod2 st2 act2 gAnd valid_gAnd ![ms.m, litW] y hwf2 hp3_inj hp3_mem f
          val2 (fun _ => True) hinv2 (fun _ inp out => out 0 = (inp 0 && inp 1)) cnt_gAnd σ
        rw [hact3_eq] at hmod
        change cnt st3 f (Finset.range n ∪ insert st2.nv (insert ms.acc (busSet bus1))) σ % 2 = _
        dsimp only at hmod; rw [hmod]
        let a : Word n := fun i => σ i.val
        have hvm : val2 a ms.m = mFn f a := by simp [val2, valOfBus, hlit_ne_m]
        have hvl : val2 a litW = decide (a j = y j) := by simp [val2, valOfBus]
        have hp : portsFinset (![ms.m, litW] : Fin 2 → Nat) = {ms.m, litW} := by
          ext u; simp only [portsFinset, Finset.mem_image, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun ⟨k, hk⟩ => by fin_cases k <;> simp [← hk],
                 fun h => by rcases h with rfl | rfl; exact ⟨0, rfl⟩; exact ⟨1, rfl⟩⟩
        have hiff : (True ∧
            (∀ w ∈ act2 \ portsFinset ![ms.m, litW], σ w = val2 a w) ∧
            σ (st2.nv + (0 : Fin 1).val) = (val2 a ((![ms.m, litW] : Fin 2 → Nat) 0) &&
              val2 a ((![ms.m, litW] : Fin 2 → Nat) 1))) ↔
            ((∀ i : Fin n, σ (bus1 i) = a i) ∧ σ ms.acc = accFn f a ∧
             σ st2.nv = (mFn f a && decide (a j = y j))) := by
          simp only [true_and, Fin.val_zero, Nat.add_zero, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, hvm, hvl, hp]
          constructor
          · rintro ⟨hrest, hm'⟩
            refine ⟨fun i => ?_, ?_, hm'⟩
            · have hmem : bus1 i ∈ act2 \ {ms.m, litW} := Finset.mem_sdiff.mpr
                ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                  (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))),
                 by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                    exact ⟨fun h => hm_not1 (h ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩),
                           fun h => hlit_not1 (h ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩⟩
              have := hrest _ hmem
              dsimp only [val2] at this; rw [valOfBus_bus bus1 hbus1_inj ms.acc hacc_not1 (accFn f a) _
                (by simp [hlit_not1, hm_not1]) a i] at this; exact this
            · have := hrest ms.acc (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
                by simp [hinv.m_ne_acc.symm, hlit_ne_acc.symm]⟩)
              dsimp only [val2] at this; rw [valOfBus_acc bus1 ms.acc (accFn f a) _ (by simp [hlit_ne_acc, hinv.m_ne_acc]) a] at this; exact this
          · rintro ⟨hB, hA, hm'⟩
            refine ⟨fun w hw => ?_, hm'⟩
            rcases Finset.mem_sdiff.mp hw with ⟨hw2, hne⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hne
            simp only [act2, Finset.mem_insert] at hw2
            rcases hw2 with rfl | rfl | rfl | hwB
            · exact False.elim (hne (Or.inr rfl))
            · exact False.elim (hne (Or.inl rfl))
            · dsimp only [val2]; rw [valOfBus_acc bus1 ms.acc (accFn f a) _ (by simp [hlit_ne_acc, hinv.m_ne_acc]) a]; exact hA
            · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hwB
              rcases hwB with ⟨i, rfl⟩
              dsimp only [val2]; rw [valOfBus_bus bus1 hbus1_inj ms.acc hacc_not1 (accFn f a) _
                (by simp [hlit_not1, hm_not1]) a i]; exact hB i
        exact ite_nat_congr hiff }

def matchBits {n : Nat} (ms : MatchState n) (y : Word n) : (k : Nat) → k ≤ n → MatchState n
  | 0, _ => ms
  | k + 1, hk => bitStep (matchBits ms y k (by omega)) y ⟨k, hk⟩

lemma matchBits_nv_le {n : Nat} (ms : MatchState n) (y : Word n) :
    ∀ (k : Nat) (hk : k ≤ n), (matchBits ms y k hk).st.nv ≤ ms.st.nv + 23 * k
  | 0, _ => by simp [matchBits]
  | k + 1, hk => by
    simp only [matchBits]
    have h1 := bitStep_nv_le (matchBits ms y k (by omega)) y ⟨k, hk⟩
    have h2 := matchBits_nv_le ms y k (by omega)
    omega

lemma matchBits_inv {n : Nat} (ms : MatchState n) (y : Word n) (accFn : Table n → Word n → Bool)
    (h0 : MatchInv ms accFn (fun _ _ => true)) :
    ∀ (k : Nat) (hk : k ≤ n),
      MatchInv (matchBits ms y k hk) accFn
        (fun _ a => decide (∀ i : Fin n, i.val < k → a i = y i))
  | 0, _ => by
    have : (fun (_ : Table n) (a : Word n) => decide (∀ i : Fin n, i.val < 0 → a i = y i)) =
        (fun _ _ => true) := by ext f a; simp
    rw [this]; exact h0
  | k + 1, hk => by
    have ih := matchBits_inv ms y accFn h0 k (by omega)
    have hstep := bitStep_inv (matchBits ms y k (by omega)) y ⟨k, hk⟩ accFn _ ih
    have hfn : (fun (f : Table n) (a : Word n) =>
        decide (∀ i : Fin n, i.val < k → a i = y i) && decide (a ⟨k, hk⟩ = y ⟨k, hk⟩)) =
        (fun _ a => decide (∀ i : Fin n, i.val < k + 1 → a i = y i)) := by
      ext f a
      rw [← Bool.decide_and]
      refine decide_eq_decide.mpr ?_
      constructor
      · rintro ⟨h1, h2⟩ i hi
        by_cases hik : i.val = k
        · have : i = ⟨k, hk⟩ := Fin.ext hik; subst this; exact h2
        · exact h1 i (by omega)
      · intro h; exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by dsimp; omega)⟩
    rw [hfn] at hstep; exact hstep

/-- Full word step for a single word `y : Word n`. -/
def wordStep {n : Nat} (bs : BusState n) (y : Word n) : BusState n :=
  let act0 := insert bs.acc (busSet bs.bus)
  -- 1. CONST1 for m = true
  let st1 := attach bs.st act0 gConst1 Fin.elim0 y
  let ms0 : MatchState n := { st := st1, bus := bs.bus, acc := bs.acc, m := bs.st.nv }
  -- 2. matchBits for all n bits
  let ms1 := matchBits ms0 y n (le_refl n)
  let act1 := insert ms1.m (insert ms1.acc (busSet ms1.bus))
  -- 3. CONST_TAG(y) -> fy = ms1.st.nv
  let st2 := attach ms1.st act1 gConstTag Fin.elim0 y
  let fy := ms1.st.nv
  let act2 := insert fy act1
  -- 4. AND(ms1.m, fy) -> term = st2.nv
  let st3 := attach st2 act2 gAnd ![ms1.m, fy] y
  let term := st2.nv
  let act3 := insert term (insert ms1.acc (busSet ms1.bus))
  -- 5. OR(ms1.acc, term) -> acc' = st3.nv
  let st4 := attach st3 act3 gOr ![ms1.acc, term] y
  { st := st4
    bus := ms1.bus
    acc := st3.nv }

lemma wordStep_nv_le {n : Nat} (bs : BusState n) (y : Word n) :
    (wordStep bs y).st.nv ≤ bs.st.nv + 23 * n + 22 := by
  simp only [wordStep, attach]
  have hmb := matchBits_nv_le
    { st := attach bs.st (insert bs.acc (busSet bs.bus)) gConst1 Fin.elim0 y
      bus := bs.bus, acc := bs.acc, m := bs.st.nv } y n (le_refl n)
  simp only [attach] at hmb
  omega

lemma wordStep_inv {n : Nat} (bs : BusState n) (y : Word n) (accFn : Table n → Word n → Bool)
    (hinv : BusInv bs accFn) :
    BusInv (wordStep bs y) (fun f a => accFn f a || (decide (a = y) && f y)) := by
  let act0 := insert bs.acc (busSet bs.bus)
  -- 1. CONST1 -> ms0
  let st1 := attach bs.st act0 gConst1 Fin.elim0 y
  let ms0 : MatchState n := { st := st1, bus := bs.bus, acc := bs.acc, m := bs.st.nv }
  have hact0_card : act0.card ≤ n + 1 := by
    have := card_busSet bs.bus; exact le_trans (Finset.card_insert_le _ _) (by omega)
  have hact1_eq : (act0 \ portsFinset (Fin.elim0 : Fin 0 → Nat)) ∪ outFinset bs.st.nv 1 =
      insert bs.st.nv act0 := by
    ext u; simp only [portsFinset, outFinset, Finset.mem_union, Finset.mem_sdiff, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_insert, IsEmpty.exists_iff,
      not_false_eq_true, and_true]
    exact ⟨fun h => by rcases h with h | ⟨k, hk, rfl⟩; exact Or.inr h; exact Or.inl (by omega),
           fun h => by rcases h with rfl | h; exact Or.inr ⟨0, by omega, by omega⟩; exact Or.inl h⟩
  have hwf1 := attach_wellFormed bs.st act0 gConst1 valid_gConst1 Fin.elim0 y hinv.wf
    (fun a => Fin.elim0 a) (fun a => Fin.elim0 a) (by omega)
  rw [hact1_eq] at hwf1
  have hlt0 : ∀ u ∈ act0, u < bs.st.nv := fun u hu => Finset.mem_range.mp (hinv.wf.act_sub hu)
  have hms0 : MatchInv ms0 accFn (fun _ _ => true) :=
    { wf := hwf1
      bus_inj := hinv.bus_inj
      acc_not_bus := hinv.acc_not_bus
      m_not_bus := fun h => by dsimp only [ms0] at h; have := hlt0 bs.st.nv (Finset.mem_insert_of_mem h); omega
      m_ne_acc := by dsimp only [ms0]; have := hlt0 bs.acc (Finset.mem_insert_self _ _); omega
      sem := by
        intro f σ
        let val0 : Word n → Nat → Bool := fun a u => valOfBus bs.bus bs.acc (accFn f a) [] a u
        have hinv0 : ∀ σ' : Nat → Bool,
            cnt bs.st f (Finset.range n ∪ act0) σ' % 2 =
              if True ∧ (∀ w ∈ act0, σ' w = val0 (fun i => σ' i.val) w) then 1 else 0 := by
          intro σ'; rw [hinv.sem f σ']
          let a : Word n := fun i => σ' i.val
          have hiff : ((∀ i : Fin n, σ' (bs.bus i) = a i) ∧ σ' bs.acc = accFn f a) ↔
              (True ∧ ∀ w ∈ act0, σ' w = val0 a w) := by
            simp only [true_and, act0, Finset.mem_insert]
            constructor
            · rintro ⟨hB, hA⟩ w (rfl | hw)
              · dsimp only [val0]; rw [valOfBus_acc bs.bus bs.acc (accFn f a) [] (by simp) a]; exact hA
              · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
                rcases hw with ⟨i, rfl⟩
                dsimp only [val0]; rw [valOfBus_bus bs.bus hinv.bus_inj bs.acc hinv.acc_not_bus (accFn f a) [] (by simp) a i]; exact hB i
            · intro h
              refine ⟨fun i => ?_, ?_⟩
              · have := h (bs.bus i) (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
                dsimp only [val0] at this; rw [valOfBus_bus bs.bus hinv.bus_inj bs.acc hinv.acc_not_bus (accFn f a) [] (by simp) a i] at this; exact this
              · have := h bs.acc (Or.inl rfl)
                dsimp only [val0] at this; rw [valOfBus_acc bs.bus bs.acc (accFn f a) [] (by simp) a] at this; exact this
          exact ite_nat_congr hiff
        have hmod := attach_mod2 bs.st act0 gConst1 valid_gConst1 Fin.elim0 y hinv.wf
          (fun a => Fin.elim0 a) (fun a => Fin.elim0 a) f val0 (fun _ => True) hinv0
          (fun _ _ out => out 0 = true) cnt_gConst1 σ
        rw [hact1_eq] at hmod
        change cnt st1 f (Finset.range n ∪ insert bs.st.nv act0) σ % 2 = _
        dsimp only at hmod; rw [hmod]
        let a : Word n := fun i => σ i.val
        have hiff : (True ∧
            (∀ w ∈ act0 \ portsFinset (Fin.elim0 : Fin 0 → Nat), σ w = val0 a w) ∧
            σ (bs.st.nv + (0 : Fin 1).val) = true) ↔
            ((∀ i : Fin n, σ (bs.bus i) = a i) ∧ σ bs.acc = accFn f a ∧ σ bs.st.nv = true) := by
          simp only [true_and, Fin.val_zero, Nat.add_zero]
          have hsdiff : act0 \ portsFinset (Fin.elim0 : Fin 0 → Nat) = act0 := by
            ext u; simp [portsFinset]
          rw [hsdiff]
          constructor
          · rintro ⟨hrest, hm⟩
            refine ⟨fun i => ?_, ?_, hm⟩
            · have := hrest (bs.bus i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
              dsimp only [val0] at this; rw [valOfBus_bus bs.bus hinv.bus_inj bs.acc hinv.acc_not_bus (accFn f a) [] (by simp) a i] at this; exact this
            · have := hrest bs.acc (Finset.mem_insert_self _ _)
              dsimp only [val0] at this; rw [valOfBus_acc bs.bus bs.acc (accFn f a) [] (by simp) a] at this; exact this
          · rintro ⟨hB, hA, hm⟩
            refine ⟨fun w hw => ?_, hm⟩
            rcases Finset.mem_insert.mp hw with rfl | hwB
            · dsimp only [val0]; rw [valOfBus_acc bs.bus bs.acc (accFn f a) [] (by simp) a]; exact hA
            · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hwB
              rcases hwB with ⟨i, rfl⟩
              dsimp only [val0]; rw [valOfBus_bus bs.bus hinv.bus_inj bs.acc hinv.acc_not_bus (accFn f a) [] (by simp) a i]; exact hB i
        exact ite_nat_congr hiff }
  -- 2. matchBits -> ms1
  let ms1 := matchBits ms0 y n (le_refl n)
  have hms1_raw : MatchInv ms1 accFn (fun _ a => decide (a = y)) := by
    have h0 := matchBits_inv ms0 y accFn hms0 n (le_refl n)
    have hfn_eq : (fun (_ : Table n) (a : Word n) => decide (∀ i : Fin n, i.val < n → a i = y i)) =
        (fun _ a => decide (a = y)) := by
      ext f a; refine decide_eq_decide.mpr ?_
      exact ⟨fun h => funext fun i => h i i.isLt, fun h i _ => congrFun h i⟩
    rw [hfn_eq] at h0; exact h0
  -- 3. CONST_TAG(y) -> fy = ms1.st.nv
  let act1 := insert ms1.m (insert ms1.acc (busSet ms1.bus))
  let st2 := attach ms1.st act1 gConstTag Fin.elim0 y
  let fy := ms1.st.nv
  let act2 := insert fy act1
  have hact1_card : act1.card ≤ n + 2 := by
    have := card_busSet ms1.bus
    exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
      (le_trans (Finset.card_insert_le _ _) (by omega)) 1)
  have hact2_eq : (act1 \ portsFinset (Fin.elim0 : Fin 0 → Nat)) ∪ outFinset fy 1 = act2 := by
    ext u; simp only [act2, portsFinset, outFinset, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_insert,
      IsEmpty.exists_iff, not_false_eq_true, and_true]
    exact ⟨fun h => by rcases h with h | ⟨k, hk, rfl⟩; exact Or.inr h; exact Or.inl (by omega),
           fun h => by rcases h with rfl | h; exact Or.inr ⟨0, by omega, by omega⟩; exact Or.inl h⟩
  have hwf2 := attach_wellFormed ms1.st act1 gConstTag valid_gConstTag Fin.elim0 y hms1_raw.wf
    (fun a => Fin.elim0 a) (fun a => Fin.elim0 a) (by omega)
  rw [hact2_eq] at hwf2
  have hlt1 : ∀ u ∈ act1, u < fy := fun u hu => Finset.mem_range.mp (hms1_raw.wf.act_sub hu)
  have hfy_not_bus : fy ∉ busSet ms1.bus := fun h => by
    have := hlt1 fy (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)); omega
  have hfy_ne_acc : fy ≠ ms1.acc := by
    have := hlt1 ms1.acc (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)); omega
  have hfy_ne_m : fy ≠ ms1.m := by
    have := hlt1 ms1.m (Finset.mem_insert_self _ _); omega
  have hsem2 : ∀ (f : Table n) (σ : Nat → Bool),
      cnt st2 f (Finset.range n ∪ act2) σ % 2 =
        if (∀ i : Fin n, σ (ms1.bus i) = σ i.val) ∧
           σ ms1.acc = accFn f (fun i => σ i.val) ∧
           σ ms1.m = decide ((fun i => σ i.val) = y) ∧
           σ fy = f y
        then 1 else 0 := by
    intro f σ
    let val1 : Word n → Nat → Bool := fun a u =>
      valOfBus ms1.bus ms1.acc (accFn f a) [(ms1.m, decide (a = y))] a u
    have hinv1 : ∀ σ' : Nat → Bool,
        cnt ms1.st f (Finset.range n ∪ act1) σ' % 2 =
          if True ∧ (∀ w ∈ act1, σ' w = val1 (fun i => σ' i.val) w) then 1 else 0 := by
      intro σ'; rw [hms1_raw.sem f σ']
      let a : Word n := fun i => σ' i.val
      have hiff : ((∀ i : Fin n, σ' (ms1.bus i) = a i) ∧ σ' ms1.acc = accFn f a ∧ σ' ms1.m = decide (a = y)) ↔
          (True ∧ ∀ w ∈ act1, σ' w = val1 a w) := by
        simp only [true_and, act1, Finset.mem_insert]
        constructor
        · rintro ⟨hB, hA, hM⟩ w (rfl | rfl | hw)
          · simp [val1, valOfBus]; exact hM
          · dsimp only [val1]; rw [valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hms1_raw.m_ne_acc]) a]; exact hA
          · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
            rcases hw with ⟨i, rfl⟩
            dsimp only [val1]; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
              (by simp [hms1_raw.m_not_bus]) a i]; exact hB i
        · intro h
          refine ⟨fun i => ?_, ?_, ?_⟩
          · have := h (ms1.bus i) (Or.inr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
            dsimp only [val1] at this; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
              (by simp [hms1_raw.m_not_bus]) a i] at this; exact this
          · have := h ms1.acc (Or.inr (Or.inl rfl))
            dsimp only [val1] at this; rw [valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hms1_raw.m_ne_acc]) a] at this; exact this
          · have := h ms1.m (Or.inl rfl); simp [val1, valOfBus] at this; exact this
      exact ite_nat_congr hiff
    have hmod := attach_mod2 ms1.st act1 gConstTag valid_gConstTag Fin.elim0 y hms1_raw.wf
      (fun a => Fin.elim0 a) (fun a => Fin.elim0 a) f val1 (fun _ => True) hinv1
      (fun v _ out => out 0 = v) cnt_gConstTag σ
    rw [hact2_eq] at hmod; dsimp only at hmod; rw [hmod]
    let a : Word n := fun i => σ i.val
    have hsdiff : act1 \ portsFinset (Fin.elim0 : Fin 0 → Nat) = act1 := by ext u; simp [portsFinset]
    have hiff : (True ∧ (∀ w ∈ act1 \ portsFinset (Fin.elim0 : Fin 0 → Nat), σ w = val1 a w) ∧
        σ (fy + (0 : Fin 1).val) = f y) ↔
        ((∀ i : Fin n, σ (ms1.bus i) = a i) ∧ σ ms1.acc = accFn f a ∧ σ ms1.m = decide (a = y) ∧ σ fy = f y) := by
      simp only [true_and, hsdiff, Fin.val_zero, Nat.add_zero]
      constructor
      · rintro ⟨hrest, hfy⟩
        refine ⟨fun i => ?_, ?_, ?_, hfy⟩
        · have := hrest (ms1.bus i) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
          dsimp only [val1] at this; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
            (by simp [hms1_raw.m_not_bus]) a i] at this; exact this
        · have := hrest ms1.acc (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          dsimp only [val1] at this; rw [valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hms1_raw.m_ne_acc]) a] at this; exact this
        · have := hrest ms1.m (Finset.mem_insert_self _ _)
          simp [val1, valOfBus] at this; exact this
      · rintro ⟨hB, hA, hM, hfy⟩
        refine ⟨fun w hw => ?_, hfy⟩
        simp only [act1, Finset.mem_insert] at hw
        rcases hw with rfl | rfl | hwB
        · simp [val1, valOfBus]; exact hM
        · dsimp only [val1]; rw [valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hms1_raw.m_ne_acc]) a]; exact hA
        · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hwB
          rcases hwB with ⟨i, rfl⟩
          dsimp only [val1]; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
            (by simp [hms1_raw.m_not_bus]) a i]; exact hB i
    exact ite_nat_congr hiff
  -- 4. AND(ms1.m, fy) -> term = st2.nv
  let st3 := attach st2 act2 gAnd ![ms1.m, fy] y
  let term := st2.nv
  let act3 := insert term (insert ms1.acc (busSet ms1.bus))
  have hact2_card : act2.card ≤ n + 3 := le_trans (Finset.card_insert_le _ _) (by omega)
  have hp3_inj : Function.Injective (![ms1.m, fy] : Fin 2 → Nat) := by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [hfy_ne_m.symm]
  have hp3_mem : ∀ k : Fin 2, (![ms1.m, fy] : Fin 2 → Nat) k ∈ act2 := by
    intro k; fin_cases k
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_self _ _
  have hact3_eq : (act2 \ portsFinset ![ms1.m, fy]) ∪ outFinset term 1 = act3 := by
    have hp : portsFinset (![ms1.m, fy] : Fin 2 → Nat) = {ms1.m, fy} := by
      ext u; simp only [portsFinset, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨k, hk⟩ => by fin_cases k <;> simp [← hk],
             fun h => by rcases h with rfl | rfl; exact ⟨0, rfl⟩; exact ⟨1, rfl⟩⟩
    have hout : outFinset term 1 = {term} := by
      ext u; simp only [outFinset, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
      exact ⟨fun ⟨k, hk, h⟩ => by omega,
             fun h => ⟨0, by omega, by omega⟩⟩
    rw [hp, hout]
    ext u; simp only [act3, act2, act1, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h1 | h2 | h3 | h4, hne⟩ | rfl)
      · exact False.elim (hne (Or.inr h1))
      · exact False.elim (hne (Or.inl h2))
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr h4)
      · exact Or.inl rfl
    · rintro (rfl | rfl | h)
      · exact Or.inr rfl
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), by push_neg; exact ⟨hms1_raw.m_ne_acc.symm, hfy_ne_acc.symm⟩⟩
      · exact Or.inl ⟨Or.inr (Or.inr (Or.inr h)), by
          push_neg; exact ⟨fun heq => hms1_raw.m_not_bus (heq ▸ h), fun heq => hfy_not_bus (heq ▸ h)⟩⟩
  have hwf3 := attach_wellFormed st2 act2 gAnd valid_gAnd ![ms1.m, fy] y hwf2 hp3_inj hp3_mem (by omega)
  rw [hact3_eq] at hwf3
  have hlt2 : ∀ u ∈ act2, u < term := fun u hu => Finset.mem_range.mp (hwf2.act_sub hu)
  have hterm_not_bus : term ∉ busSet ms1.bus := fun h => by
    have := hlt2 term (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))); omega
  have hterm_ne_acc : term ≠ ms1.acc := by
    have := hlt2 ms1.acc (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))); omega
  have hsem3 : ∀ (f : Table n) (σ : Nat → Bool),
      cnt st3 f (Finset.range n ∪ act3) σ % 2 =
        if (∀ i : Fin n, σ (ms1.bus i) = σ i.val) ∧
           σ ms1.acc = accFn f (fun i => σ i.val) ∧
           σ term = (decide ((fun i => σ i.val) = y) && f y)
        then 1 else 0 := by
    intro f σ
    let val2 : Word n → Nat → Bool := fun a u =>
      valOfBus ms1.bus ms1.acc (accFn f a) [(fy, f y), (ms1.m, decide (a = y))] a u
    have hinv2 : ∀ σ' : Nat → Bool,
        cnt st2 f (Finset.range n ∪ act2) σ' % 2 =
          if True ∧ (∀ w ∈ act2, σ' w = val2 (fun i => σ' i.val) w) then 1 else 0 := by
      intro σ'; rw [hsem2 f σ']
      let a : Word n := fun i => σ' i.val
      have hiff : ((∀ i : Fin n, σ' (ms1.bus i) = a i) ∧ σ' ms1.acc = accFn f a ∧
          σ' ms1.m = decide (a = y) ∧ σ' fy = f y) ↔
          (True ∧ ∀ w ∈ act2, σ' w = val2 a w) := by
        simp only [true_and, act2, act1, Finset.mem_insert]
        constructor
        · rintro ⟨hB, hA, hM, hF⟩ w (rfl | rfl | rfl | hw)
          · simp [val2, valOfBus]; exact hF
          · simp [val2, valOfBus, hfy_ne_m]; exact hM
          · dsimp only [val2]; rw [valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hfy_ne_acc, hms1_raw.m_ne_acc]) a]; exact hA
          · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
            rcases hw with ⟨i, rfl⟩
            dsimp only [val2]; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
              (by simp [hfy_not_bus, hms1_raw.m_not_bus]) a i]; exact hB i
        · intro h
          refine ⟨fun i => ?_, ?_, ?_, ?_⟩
          · have := h (ms1.bus i) (Or.inr (Or.inr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))))
            dsimp only [val2] at this; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
              (by simp [hfy_not_bus, hms1_raw.m_not_bus]) a i] at this; exact this
          · have := h ms1.acc (Or.inr (Or.inr (Or.inl rfl)))
            dsimp only [val2] at this; rw [valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hfy_ne_acc, hms1_raw.m_ne_acc]) a] at this; exact this
          · have := h ms1.m (Or.inr (Or.inl rfl)); simp [val2, valOfBus, hfy_ne_m] at this; exact this
          · have := h fy (Or.inl rfl); simp [val2, valOfBus] at this; exact this
      exact ite_nat_congr hiff
    have hmod := attach_mod2 st2 act2 gAnd valid_gAnd ![ms1.m, fy] y hwf2 hp3_inj hp3_mem f
      val2 (fun _ => True) hinv2 (fun _ inp out => out 0 = (inp 0 && inp 1)) cnt_gAnd σ
    rw [hact3_eq] at hmod; dsimp only at hmod; rw [hmod]
    let a : Word n := fun i => σ i.val
    have hvm : val2 a ms1.m = decide (a = y) := by simp [val2, valOfBus, hfy_ne_m]
    have hvf : val2 a fy = f y := by simp [val2, valOfBus]
    have hp : portsFinset (![ms1.m, fy] : Fin 2 → Nat) = {ms1.m, fy} := by
      ext u; simp only [portsFinset, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨k, hk⟩ => by fin_cases k <;> simp [← hk],
             fun h => by rcases h with rfl | rfl; exact ⟨0, rfl⟩; exact ⟨1, rfl⟩⟩
    have hiff : (True ∧
        (∀ w ∈ act2 \ portsFinset ![ms1.m, fy], σ w = val2 a w) ∧
        σ (term + (0 : Fin 1).val) = (val2 a ((![ms1.m, fy] : Fin 2 → Nat) 0) &&
          val2 a ((![ms1.m, fy] : Fin 2 → Nat) 1))) ↔
        ((∀ i : Fin n, σ (ms1.bus i) = a i) ∧ σ ms1.acc = accFn f a ∧
         σ term = (decide (a = y) && f y)) := by
      simp only [true_and, Fin.val_zero, Nat.add_zero, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, hvm, hvf, hp]
      constructor
      · rintro ⟨hrest, ht⟩
        refine ⟨fun i => ?_, ?_, ht⟩
        · have hmem : ms1.bus i ∈ act2 \ {ms1.m, fy} := Finset.mem_sdiff.mpr
            ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))),
             by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                exact ⟨fun h => hms1_raw.m_not_bus (h ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩),
                       fun h => hfy_not_bus (h ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩⟩
          have := hrest _ hmem
          dsimp only [val2] at this; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
            (by simp [hfy_not_bus, hms1_raw.m_not_bus]) a i] at this; exact this
        · have := hrest ms1.acc (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
            by simp [hms1_raw.m_ne_acc.symm, hfy_ne_acc.symm]⟩)
          dsimp only [val2] at this; rw [valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hfy_ne_acc, hms1_raw.m_ne_acc]) a] at this; exact this
      · rintro ⟨hB, hA, ht⟩
        refine ⟨fun w hw => ?_, ht⟩
        rcases Finset.mem_sdiff.mp hw with ⟨hw2, hne⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hne
        simp only [act2, act1, Finset.mem_insert] at hw2
        rcases hw2 with rfl | rfl | rfl | hwB
        · exact False.elim (hne (Or.inr rfl))
        · exact False.elim (hne (Or.inl rfl))
        · dsimp only [val2]; rw [valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hfy_ne_acc, hms1_raw.m_ne_acc]) a]; exact hA
        · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hwB
          rcases hwB with ⟨i, rfl⟩
          dsimp only [val2]; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
            (by simp [hfy_not_bus, hms1_raw.m_not_bus]) a i]; exact hB i
    exact ite_nat_congr hiff
  -- 5. OR(ms1.acc, term) -> acc' = st3.nv
  let st4 := attach st3 act3 gOr ![ms1.acc, term] y
  have hact3_card : act3.card ≤ n + 2 := by
    have := card_busSet ms1.bus
    exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
      (le_trans (Finset.card_insert_le _ _) (by omega)) 1)
  have hp4_inj : Function.Injective (![ms1.acc, term] : Fin 2 → Nat) := by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [hterm_ne_acc.symm]
  have hp4_mem : ∀ k : Fin 2, (![ms1.acc, term] : Fin 2 → Nat) k ∈ act3 := by
    intro k; fin_cases k
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_self _ _
  have hact4_eq : (act3 \ portsFinset ![ms1.acc, term]) ∪ outFinset st3.nv 1 =
      insert st3.nv (busSet ms1.bus) := by
    have hp : portsFinset (![ms1.acc, term] : Fin 2 → Nat) = {ms1.acc, term} := by
      ext u; simp only [portsFinset, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨k, hk⟩ => by fin_cases k <;> simp [← hk],
             fun h => by rcases h with rfl | rfl; exact ⟨0, rfl⟩; exact ⟨1, rfl⟩⟩
    have hout : outFinset st3.nv 1 = {st3.nv} := by
      ext u; simp only [outFinset, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
      exact ⟨fun ⟨k, hk, h⟩ => by omega,
             fun h => ⟨0, by omega, by omega⟩⟩
    rw [hp, hout]
    ext u; simp only [act3, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨h1 | h2 | h3, hne⟩ | rfl)
      · exact False.elim (hne (Or.inr h1))
      · exact False.elim (hne (Or.inl h2))
      · exact Or.inr h3
      · exact Or.inl rfl
    · rintro (rfl | h)
      · exact Or.inr rfl
      · exact Or.inl ⟨Or.inr (Or.inr h), by
          push_neg; exact ⟨fun heq => hms1_raw.acc_not_bus (heq ▸ h), fun heq => hterm_not_bus (heq ▸ h)⟩⟩
  have hwf4 := attach_wellFormed st3 act3 gOr valid_gOr ![ms1.acc, term] y hwf3 hp4_inj hp4_mem (by omega)
  rw [hact4_eq] at hwf4
  have hlt3 : ∀ u ∈ act3, u < st3.nv := fun u hu => Finset.mem_range.mp (hwf3.act_sub hu)
  refine
    { wf := hwf4
      bus_inj := hms1_raw.bus_inj
      acc_not_bus := fun h => by
        have := hlt3 st3.nv (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)); omega
      sem := by
        intro f σ
        let val3 : Word n → Nat → Bool := fun a u =>
          valOfBus ms1.bus ms1.acc (accFn f a) [(term, decide (a = y) && f y)] a u
        have hinv3 : ∀ σ' : Nat → Bool,
            cnt st3 f (Finset.range n ∪ act3) σ' % 2 =
              if True ∧ (∀ w ∈ act3, σ' w = val3 (fun i => σ' i.val) w) then 1 else 0 := by
          intro σ'; rw [hsem3 f σ']
          let a : Word n := fun i => σ' i.val
          have hiff : ((∀ i : Fin n, σ' (ms1.bus i) = a i) ∧ σ' ms1.acc = accFn f a ∧
              σ' term = (decide (a = y) && f y)) ↔
              (True ∧ ∀ w ∈ act3, σ' w = val3 a w) := by
            simp only [true_and, act3, Finset.mem_insert]
            constructor
            · rintro ⟨hB, hA, hT⟩ w (rfl | rfl | hw)
              · simp [val3, valOfBus]; exact hT
              · dsimp only [val3]; rw [valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hterm_ne_acc]) a]; exact hA
              · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
                rcases hw with ⟨i, rfl⟩
                dsimp only [val3]; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
                  (by simp [hterm_not_bus]) a i]; exact hB i
            · intro h
              refine ⟨fun i => ?_, ?_, ?_⟩
              · have := h (ms1.bus i) (Or.inr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)))
                dsimp only [val3] at this; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
                  (by simp [hterm_not_bus]) a i] at this; exact this
              · have := h ms1.acc (Or.inr (Or.inl rfl))
                dsimp only [val3] at this; rw [valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hterm_ne_acc]) a] at this; exact this
              · have := h term (Or.inl rfl); simp [val3, valOfBus] at this; exact this
          exact ite_nat_congr hiff
        have hmod := attach_mod2 st3 act3 gOr valid_gOr ![ms1.acc, term] y hwf3 hp4_inj hp4_mem f
          val3 (fun _ => True) hinv3 (fun _ inp out => out 0 = (inp 0 || inp 1)) cnt_gOr σ
        rw [hact4_eq] at hmod
        change cnt st4 f (Finset.range n ∪ insert st3.nv (busSet ms1.bus)) σ % 2 = _
        dsimp only at hmod; rw [hmod]
        let a : Word n := fun i => σ i.val
        have hva : val3 a ms1.acc = accFn f a :=
          valOfBus_acc ms1.bus ms1.acc (accFn f a) _ (by simp [hterm_ne_acc]) a
        have hvt : val3 a term = (decide (a = y) && f y) := by simp [val3, valOfBus]
        have hp : portsFinset (![ms1.acc, term] : Fin 2 → Nat) = {ms1.acc, term} := by
          ext u; simp only [portsFinset, Finset.mem_image, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun ⟨k, hk⟩ => by fin_cases k <;> simp [← hk],
                 fun h => by rcases h with rfl | rfl; exact ⟨0, rfl⟩; exact ⟨1, rfl⟩⟩
        have hiff : (True ∧
            (∀ w ∈ act3 \ portsFinset ![ms1.acc, term], σ w = val3 a w) ∧
            σ (st3.nv + (0 : Fin 1).val) = (val3 a ((![ms1.acc, term] : Fin 2 → Nat) 0) ||
              val3 a ((![ms1.acc, term] : Fin 2 → Nat) 1))) ↔
            ((∀ i : Fin n, σ (ms1.bus i) = a i) ∧
             σ st3.nv = (accFn f a || (decide (a = y) && f y))) := by
          simp only [true_and, Fin.val_zero, Nat.add_zero, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.head_cons, hva, hvt, hp]
          constructor
          · rintro ⟨hrest, ha'⟩
            refine ⟨fun i => ?_, ha'⟩
            have hmem : ms1.bus i ∈ act3 \ {ms1.acc, term} := Finset.mem_sdiff.mpr
              ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)),
               by simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg
                  exact ⟨fun h => hms1_raw.acc_not_bus (h ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩),
                         fun h => hterm_not_bus (h ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩⟩
            have := hrest _ hmem
            dsimp only [val3] at this; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
              (by simp [hterm_not_bus]) a i] at this; exact this
          · rintro ⟨hB, ha'⟩
            refine ⟨fun w hw => ?_, ha'⟩
            rcases Finset.mem_sdiff.mp hw with ⟨hw3, hne⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hne
            simp only [act3, Finset.mem_insert] at hw3
            rcases hw3 with rfl | rfl | hwB
            · exact False.elim (hne (Or.inr rfl))
            · exact False.elim (hne (Or.inl rfl))
            · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hwB
              rcases hwB with ⟨i, rfl⟩
              dsimp only [val3]; rw [valOfBus_bus ms1.bus hms1_raw.bus_inj ms1.acc hms1_raw.acc_not_bus (accFn f a) _
                (by simp [hterm_not_bus]) a i]; exact hB i
        exact ite_nat_congr hiff }

def foldWords {n : Nat} : List (Word n) → BusState n → BusState n
  | [], bs => bs
  | y :: ys, bs => foldWords ys (wordStep bs y)

lemma foldWords_nv_le {n : Nat} : ∀ (ys : List (Word n)) (bs : BusState n),
    (foldWords ys bs).st.nv ≤ bs.st.nv + ys.length * (23 * n + 22)
  | [], bs => by simp [foldWords]
  | y :: ys, bs => by
    simp only [foldWords, List.length_cons]
    have h1 := foldWords_nv_le ys (wordStep bs y)
    have h2 := wordStep_nv_le bs y
    have h3 : (ys.length + 1) * (23 * n + 22) = ys.length * (23 * n + 22) + (23 * n + 22) := by ring
    omega

lemma foldWords_inv {n : Nat} : ∀ (ys : List (Word n)) (bs : BusState n)
    (accFn : Table n → Word n → Bool),
    BusInv bs accFn →
    BusInv (foldWords ys bs) (fun f a => accFn f a || ys.any (fun y => decide (a = y) && f y))
  | [], bs, accFn, hinv => by
    simp only [foldWords, List.any_nil, Bool.or_false]
    exact hinv
  | y :: ys, bs, accFn, hinv => by
    simp only [foldWords, List.any_cons]
    have h1 := wordStep_inv bs y accFn hinv
    have h2 := foldWords_inv ys (wordStep bs y) _ h1
    have heq : (fun f a => (accFn f a || (decide (a = y) && f y)) || ys.any (fun z => decide (a = z) && f z)) =
        (fun f a => accFn f a || ((decide (a = y) && f y) || ys.any (fun z => decide (a = z) && f z))) := by
      ext f a; exact Bool.or_assoc _ _ _
    rw [heq] at h2; exact h2

/-- Final SideGraph(n): fold over `allWords n`, then attach `PIN1` to `acc`. -/
def sideGraph (n : Nat) : State n :=
  let bs := foldWords (allWords n) (startBus n)
  attach bs.st (insert bs.acc (busSet bs.bus)) gPin1 ![bs.acc] (fun _ => false)

lemma sideGraph_nv_le (n : Nat) : (sideGraph n).nv ≤ 27 * (n + 1) * 2 ^ n := by
  simp only [sideGraph, attach]
  have h1 := foldWords_nv_le (allWords n) (startBus n)
  rw [allWords_length, startBus_nv] at h1
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 4 * n + 4 ≤ 4 * (n + 1) * 2 ^ n := by
    calc 4 * n + 4 = 4 * (n + 1) * 1 := by ring
    _ ≤ 4 * (n + 1) * 2 ^ n := Nat.mul_le_mul_left _ hpow
  have h3 : 2 ^ n * (23 * n + 22) ≤ 23 * (n + 1) * 2 ^ n := by
    calc 2 ^ n * (23 * n + 22) = (23 * n + 22) * 2 ^ n := Nat.mul_comm _ _
    _ ≤ (23 * (n + 1)) * 2 ^ n := Nat.mul_le_mul_right _ (by omega)
  have h4 : 4 * (n + 1) * 2 ^ n + 23 * (n + 1) * 2 ^ n = 27 * (n + 1) * 2 ^ n := by ring
  omega

/-- Forgetting `busSet` from `cnt` sums over all `τ : Fin n → Bool`. -/
lemma cnt_forget_bus {n : Nat} (st : State n) (f : Table n)
    (bus : Fin n → Nat) (hinj : Function.Injective bus)
    (hdisj : Disjoint (Finset.range n) (busSet bus)) (σ : Nat → Bool) :
    cnt st f (Finset.range n) σ =
      ∑ τ : Word n, cnt st f (Finset.range n ∪ busSet bus) (overridePorts σ bus τ) := by
  let dom := Finset.univ.sigma (fun τ : Word n => isSets st f (Finset.range n ∪ busSet bus) (overridePorts σ bus τ))
  have hcard : dom.card = ∑ τ : Word n, cnt st f (Finset.range n ∪ busSet bus) (overridePorts σ bus τ) := by
    simp [dom, cnt, Finset.card_sigma]
  rw [← hcard]; change (isSets st f (Finset.range n) σ).card = dom.card
  symm
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro ⟨τ, I⟩ hp
    simp only [dom, Finset.mem_sigma, Finset.mem_univ, true_and, isSets, Finset.mem_filter,
      Finset.mem_powerset] at hp ⊢
    refine ⟨hp.1, hp.2.1, hp.2.2.1, fun u hu => ?_⟩
    have h1 := hp.2.2.2 u (Finset.mem_union_left _ hu)
    have hnot : u ∉ portsFinset bus := by
      intro hmem; exact Finset.disjoint_left.mp hdisj hu hmem
    rw [overridePorts_other σ bus τ u hnot] at h1
    exact h1
  · intro ⟨τ1, I1⟩ hp1 ⟨τ2, I2⟩ hp2 heq
    simp only at heq; subst heq
    simp only [dom, Finset.mem_sigma, Finset.mem_univ, true_and, isSets, Finset.mem_filter,
      Finset.mem_powerset] at hp1 hp2
    have hτ : τ1 = τ2 := by
      ext j
      have h1 := hp1.2.2.2 (bus j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
      have h2 := hp2.2.2.2 (bus j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
      rw [overridePorts_at σ bus hinj τ1 j] at h1
      rw [overridePorts_at σ bus hinj τ2 j] at h2
      rw [← h1, ← h2]
    subst hτ; rfl
  · intro I hI
    simp only [isSets, Finset.mem_filter, Finset.mem_powerset] at hI
    let τ : Word n := fun j => decide (bus j ∈ I)
    refine ⟨⟨τ, I⟩, ?_, rfl⟩
    simp only [dom, Finset.mem_sigma, Finset.mem_univ, true_and, isSets, Finset.mem_filter,
      Finset.mem_powerset]
    refine ⟨hI.1, hI.2.1, hI.2.2.1, fun u hu => ?_⟩
    rcases Finset.mem_union.mp hu with h1 | h2
    · have hnot : u ∉ portsFinset bus := fun hmem => Finset.disjoint_left.mp hdisj h1 hmem
      rw [overridePorts_other σ bus τ u hnot]; exact hI.2.2.2 u h1
    · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at h2
      rcases h2 with ⟨j, rfl⟩
      rw [overridePorts_at σ bus hinj τ j]

lemma sideGraph_props (n : Nat) :
    ∃ active : Finset Nat,
      WellFormed (sideGraph n) active (n + 15) ∧
      ∀ (f : Table n) (σ : Nat → Bool),
        cnt (sideGraph n) f (Finset.range n) σ % 2 =
          if f (fun j : Fin n => σ j.val) = true then 1 else 0 := by
  let bs := foldWords (allWords n) (startBus n)
  have hbs := foldWords_inv (allWords n) (startBus n) (fun _ _ => false) (startBus_inv n)
  have hacc_eq : (fun (f : Table n) (a : Word n) =>
      false || (allWords n).any (fun y => decide (a = y) && f y)) = (fun f a => f a) := by
    ext f a
    simp only [Bool.false_or]
    cases hfa : f a
    · rw [Bool.eq_false_iff]; intro h
      rw [List.any_eq_true] at h
      rcases h with ⟨y, _, hy⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hy
      rcases hy with ⟨rfl, h1⟩; rw [hfa] at h1; exact Bool.noConfusion h1
    · rw [List.any_eq_true]
      exact ⟨a, mem_allWords n a, by simp [hfa]⟩
  rw [hacc_eq] at hbs
  let act0 := insert bs.acc (busSet bs.bus)
  have hact0_card : act0.card ≤ n + 1 := by
    have := card_busSet bs.bus; exact le_trans (Finset.card_insert_le _ _) (by omega)
  have hact1_eq : (act0 \ portsFinset ![bs.acc]) ∪ outFinset bs.st.nv 0 = busSet bs.bus := by
    have hp : portsFinset (![bs.acc] : Fin 1 → Nat) = {bs.acc} := by ext u; simp [portsFinset]
    have hout : outFinset bs.st.nv 0 = ∅ := by simp [outFinset]
    rw [hp, hout, Finset.union_empty]
    ext u; simp only [act0, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | h, hne⟩; exact False.elim (hne rfl); exact h
    · intro h; exact ⟨Or.inr h, fun heq => hbs.acc_not_bus (heq ▸ h)⟩
  have hwf := attach_wellFormed bs.st act0 gPin1 valid_gPin1 ![bs.acc] (fun _ => false) hbs.wf
    (fun a b _ => Subsingleton.elim a b)
    (fun k => by fin_cases k; exact Finset.mem_insert_self _ _) (by omega)
  rw [hact1_eq] at hwf
  refine ⟨busSet bs.bus, hwf, fun f σ => ?_⟩
  let val0 : Word n → Nat → Bool := fun a u => valOfBus bs.bus bs.acc (f a) [] a u
  have hinv0 : ∀ σ' : Nat → Bool,
      cnt bs.st f (Finset.range n ∪ act0) σ' % 2 =
        if True ∧ (∀ w ∈ act0, σ' w = val0 (fun i => σ' i.val) w) then 1 else 0 := by
    intro σ'; rw [hbs.sem f σ']
    let a : Word n := fun i => σ' i.val
    have hiff : ((∀ i : Fin n, σ' (bs.bus i) = a i) ∧ σ' bs.acc = f a) ↔
        (True ∧ ∀ w ∈ act0, σ' w = val0 a w) := by
      simp only [true_and, act0, Finset.mem_insert]
      constructor
      · rintro ⟨hB, hA⟩ w (rfl | hw)
        · dsimp only [val0]; rw [valOfBus_acc bs.bus bs.acc (f a) [] (by simp) a]; exact hA
        · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hw
          rcases hw with ⟨i, rfl⟩
          dsimp only [val0]; rw [valOfBus_bus bs.bus hbs.bus_inj bs.acc hbs.acc_not_bus (f a) [] (by simp) a i]; exact hB i
      · intro h
        refine ⟨fun i => ?_, ?_⟩
        · have := h (bs.bus i) (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
          dsimp only [val0] at this; rw [valOfBus_bus bs.bus hbs.bus_inj bs.acc hbs.acc_not_bus (f a) [] (by simp) a i] at this; exact this
        · have := h bs.acc (Or.inl rfl)
          dsimp only [val0] at this; rw [valOfBus_acc bs.bus bs.acc (f a) [] (by simp) a] at this; exact this
    exact ite_nat_congr hiff
  have hpin : ∀ σ' : Nat → Bool,
      cnt (sideGraph n) f (Finset.range n ∪ busSet bs.bus) σ' % 2 =
        if (∀ i : Fin n, σ' (bs.bus i) = σ' i.val) ∧ f (fun i => σ' i.val) = true then 1 else 0 := by
    intro σ'
    have hmod := attach_mod2 bs.st act0 gPin1 valid_gPin1 ![bs.acc] (fun _ => false) hbs.wf
      (fun a b _ => Subsingleton.elim a b)
      (fun k => by fin_cases k; exact Finset.mem_insert_self _ _)
      f val0 (fun _ => True) hinv0 (fun _ inp _ => inp 0 = true) cnt_gPin1 σ'
    rw [hact1_eq] at hmod
    change cnt (attach bs.st act0 gPin1 ![bs.acc] (fun _ => false)) f
      (Finset.range n ∪ busSet bs.bus) σ' % 2 = _
    dsimp only at hmod; rw [hmod]
    let a : Word n := fun i => σ' i.val
    have hva : val0 a bs.acc = f a := valOfBus_acc bs.bus bs.acc (f a) [] (by simp) a
    have hp : portsFinset (![bs.acc] : Fin 1 → Nat) = {bs.acc} := by ext u; simp [portsFinset]
    have hiff : (True ∧ (∀ w ∈ act0 \ portsFinset ![bs.acc], σ' w = val0 a w) ∧
        val0 a ((![bs.acc] : Fin 1 → Nat) 0) = true) ↔
        ((∀ i : Fin n, σ' (bs.bus i) = a i) ∧ f a = true) := by
      simp only [true_and, Matrix.cons_val_zero, hva, hp]
      constructor
      · rintro ⟨hrest, hf⟩
        refine ⟨fun i => ?_, hf⟩
        have hmem : bs.bus i ∈ act0 \ {bs.acc} := Finset.mem_sdiff.mpr
          ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩),
           fun h => hbs.acc_not_bus (Finset.mem_singleton.mp h ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
        have := hrest _ hmem
        dsimp only [val0] at this; rw [valOfBus_bus bs.bus hbs.bus_inj bs.acc hbs.acc_not_bus (f a) [] (by simp) a i] at this; exact this
      · rintro ⟨hB, hf⟩
        refine ⟨fun w hw => ?_, hf⟩
        rcases Finset.mem_sdiff.mp hw with ⟨hw0, hne⟩
        simp only [Finset.mem_singleton] at hne
        rcases Finset.mem_insert.mp hw0 with rfl | hwB
        · exact False.elim (hne rfl)
        · simp only [busSet, Finset.mem_image, Finset.mem_univ, true_and] at hwB
          rcases hwB with ⟨i, rfl⟩
          dsimp only [val0]; rw [valOfBus_bus bs.bus hbs.bus_inj bs.acc hbs.acc_not_bus (f a) [] (by simp) a i]; exact hB i
    exact ite_nat_congr hiff
  rw [cnt_forget_bus (sideGraph n) f bs.bus hbs.bus_inj hwf.disj σ, sum_mod_two]
  let a : Word n := fun j => σ j.val
  have hword_eq : ∀ τ : Word n, (fun j : Fin n => overridePorts σ bs.bus τ j.val) = a := by
    intro τ; ext j
    refine overridePorts_other σ bs.bus τ j.val ?_
    intro hmem; exact Finset.disjoint_left.mp hwf.disj (Finset.mem_range.mpr j.isLt) hmem
  have hterm : ∀ τ : Word n,
      cnt (sideGraph n) f (Finset.range n ∪ busSet bs.bus) (overridePorts σ bs.bus τ) % 2 =
        if τ = a ∧ f a = true then 1 else 0 := by
    intro τ
    rw [hpin (overridePorts σ bs.bus τ), hword_eq τ]
    have hword_i : ∀ i : Fin n, overridePorts σ bs.bus τ i.val = a i := fun i => congrFun (hword_eq τ) i
    have hiff : ((∀ i : Fin n, overridePorts σ bs.bus τ (bs.bus i) = overridePorts σ bs.bus τ i.val) ∧ f a = true) ↔
        (τ = a ∧ f a = true) := by
      simp only [hword_i]
      constructor
      · rintro ⟨h1, h2⟩; refine ⟨funext fun i => ?_, h2⟩
        have := h1 i; rw [overridePorts_at σ bs.bus hbs.bus_inj τ i] at this; exact this
      · rintro ⟨rfl, h2⟩; exact ⟨fun i => overridePorts_at σ bs.bus hbs.bus_inj a i, h2⟩
    exact ite_nat_congr hiff
  rw [Finset.sum_congr rfl (fun τ _ => hterm τ), Finset.sum_eq_single a]
  · simp; split_ifs <;> rfl
  · intro τ _ hne; simp [hne]
  · intro h; exact False.elim (h (Finset.mem_univ _))

/-! ### Part 5: Full graph (Left + n-edge Bridge + Right), pathwidth, and IP identity -/

def bridgeBags (n M : Nat) : (k : Nat) → List (Finset Nat)
  | 0 => []
  | k + 1 =>
    let cur : Finset Nat := (Finset.range k).image (fun j => M + j) ∪ Finset.Ico k n
    let B1 : Finset Nat := cur ∪ {2 * M + k, 2 * M + n + k, M + k}
    let B2 : Finset Nat := (Finset.range (k + 1)).image (fun j => M + j) ∪ Finset.Ico (k + 1) n
    bridgeBags n M k ++ [B1, B2]

def bridgeCur (n M k : Nat) : Finset Nat :=
  (Finset.range k).image (fun j => M + j) ∪ Finset.Ico k n

lemma bridgeCur_card (n M k : Nat) (hM : n ≤ M) (hk : k ≤ n) :
    (bridgeCur n M k).card = n := by
  have hdisj : Disjoint ((Finset.range k).image (fun j => M + j)) (Finset.Ico k n) := by
    rw [Finset.disjoint_left]
    intro u h1 h2
    simp only [Finset.mem_image, Finset.mem_range] at h1
    rcases h1 with ⟨j, _, rfl⟩
    have := (Finset.mem_Ico.mp h2).2; omega
  rw [bridgeCur, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun a b h => by omega),
      Finset.card_range, Nat.card_Ico]
  omega

lemma bridgeCur_step (n M k : Nat) (hM : n ≤ M) (hk : k < n) :
    (bridgeCur n M k \ {k}) ∪ {M + k} = bridgeCur n M (k + 1) := by
  ext u
  simp only [bridgeCur, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro (⟨⟨j, hj, rfl⟩ | ⟨h1, h2⟩, hne⟩ | rfl)
    · exact Or.inl ⟨j, by omega, rfl⟩
    · exact Or.inr ⟨by omega, h2⟩
    · exact Or.inl ⟨k, by omega, rfl⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨h1, h2⟩)
    · by_cases hjk : j = k
      · subst hjk; exact Or.inr rfl
      · exact Or.inl ⟨Or.inl ⟨j, by omega, rfl⟩, by omega⟩
    · exact Or.inl ⟨Or.inr ⟨by omega, h2⟩, by omega⟩

lemma bridge_prefix_ri (n M W : Nat) (bagsL : List (Finset Nat)) (hM : n ≤ M) (hW : n + 3 ≤ W)
    (hneL : bagsL ≠ []) (hlastL : bagsL.getLast hneL = Finset.range n)
    (hsubL : ∀ B ∈ bagsL, B ⊆ Finset.range M)
    (hcardL : ∀ B ∈ bagsL, B.card ≤ W) (hriL : BagsRI bagsL) :
    ∀ k ≤ n,
      let pref := bagsL ++ bridgeBags n M k
      ∃ hne : pref ≠ [],
        pref.getLast hne = bridgeCur n M k ∧
        (∀ B ∈ pref, B ⊆ Finset.range M ∪ (Finset.range k).image (fun j => M + j) ∪
          (Finset.range k).image (fun j => 2 * M + j) ∪
          (Finset.range k).image (fun j => 2 * M + n + j)) ∧
        (∀ B ∈ pref, B.card ≤ W) ∧
        BagsRI pref := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨by simpa [bridgeBags] using hneL, ?_, ?_, ?_, ?_⟩
    · simp only [bridgeBags, List.append_nil]
      rw [hlastL]; ext u; simp [bridgeCur]
    · intro B hB; simp only [bridgeBags, List.append_nil] at hB
      intro u hu; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hsubL B hB hu)))
    · intro B hB; simp only [bridgeBags, List.append_nil] at hB; exact hcardL B hB
    · simpa [bridgeBags] using hriL
  | succ k ih =>
    obtain ⟨hneP, hlastP, hsubP, hcardP, hriP⟩ := ih (by omega)
    let pref := bagsL ++ bridgeBags n M k
    let B1 := bridgeCur n M k ∪ {2 * M + k, 2 * M + n + k, M + k}
    let B2 := bridgeCur n M (k + 1)
    have hpref' : bagsL ++ bridgeBags n M (k + 1) = pref ++ [B1, B2] := by
      simp [pref, bridgeBags, bridgeCur, B1, B2, List.append_assoc]
    rw [hpref']
    let V_k := Finset.range M ∪ (Finset.range k).image (fun j => M + j) ∪
      (Finset.range k).image (fun j => 2 * M + j) ∪
      (Finset.range k).image (fun j => 2 * M + n + j)
    let V_k1 := Finset.range M ∪ (Finset.range (k + 1)).image (fun j => M + j) ∪
      (Finset.range (k + 1)).image (fun j => 2 * M + j) ∪
      (Finset.range (k + 1)).image (fun j => 2 * M + n + j)
    have hVsub : V_k ⊆ V_k1 := by
      intro u hu
      simp only [V_k, V_k1, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hu ⊢
      rcases hu with ((h | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr ⟨j, by omega, rfl⟩))
      · exact Or.inl (Or.inr ⟨j, by omega, rfl⟩)
      · exact Or.inr ⟨j, by omega, rfl⟩
    have hnew_not_Vk : ∀ x ∈ ({2 * M + k, 2 * M + n + k, M + k} : Finset Nat), x ∉ V_k := by
      intro x hx hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [V_k, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hmem
      rcases hx with rfl | rfl | rfl <;>
        rcases hmem with ((h | ⟨j, hj, heq⟩) | ⟨j, hj, heq⟩) | ⟨j, hj, heq⟩ <;> omega
    have hB2_sub_B1 : B2 ⊆ B1 := by
      dsimp only [B2, B1]
      rw [← bridgeCur_step n M k hM (by omega)]
      intro u hu
      rcases Finset.mem_union.mp hu with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp h1).1
      · simp only [Finset.mem_singleton] at h2; subst h2
        exact Finset.mem_union_right _ (by simp)
    have hB1_card : B1.card ≤ W := by
      have h1 := bridgeCur_card n M k hM (by omega)
      have h2 : ({2 * M + k, 2 * M + n + k, M + k} : Finset Nat).card ≤ 3 :=
        le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
          (le_trans (Finset.card_insert_le _ _) (by simp)) 1)
      exact le_trans (Finset.card_union_le _ _) (by omega)
    have hB1_sub_Vk1 : B1 ⊆ V_k1 := by
      intro u hu
      rcases Finset.mem_union.mp hu with h1 | h2
      · have hcur : bridgeCur n M k ⊆ V_k := by
          rw [← hlastP]; exact hsubP _ (List.getLast_mem hneP)
        exact hVsub (hcur h1)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h2
        simp only [V_k1, Finset.mem_union, Finset.mem_image, Finset.mem_range]
        rcases h2 with rfl | rfl | rfl
        · exact Or.inl (Or.inr ⟨k, by omega, rfl⟩)
        · exact Or.inr ⟨k, by omega, rfl⟩
        · exact Or.inl (Or.inl (Or.inr ⟨k, by omega, rfl⟩))
    refine ⟨by simp, by simp [B2], ?_, ?_, ?_⟩
    · intro B hB
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with hB | rfl | rfl
      · exact Finset.Subset.trans (hsubP B hB) hVsub
      · exact hB1_sub_Vk1
      · exact Finset.Subset.trans hB2_sub_B1 hB1_sub_Vk1
    · intro B hB
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with hB | rfl | rfl
      · exact hcardP B hB
      · exact hB1_card
      · exact le_trans (Finset.card_le_card hB2_sub_B1) hB1_card
    · intro u i j m hij hjm hi hj hm hui hum
      have hlen : (pref ++ [B1, B2]).length = pref.length + 2 := by simp
      have hLpos : 0 < pref.length := List.length_pos_of_ne_nil hneP
      by_cases hmL : m < pref.length
      · have hiL : i < pref.length := by omega
        have hjL : j < pref.length := by omega
        rw [List.getElem_append_left hiL] at hui
        rw [List.getElem_append_left hmL] at hum
        rw [List.getElem_append_left hjL]
        exact hriP u i j m hij hjm hiL hjL hmL hui hum
      · by_cases hiL : i < pref.length
        · rw [List.getElem_append_left hiL] at hui
          have huVk : u ∈ V_k := hsubP _ (List.getElem_mem hiL) hui
          have huB1 : u ∈ B1 := by
            have hmcases : m = pref.length ∨ m = pref.length + 1 := by omega
            rcases hmcases with rfl | rfl
            · simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero] at hum
              exact hum
            · have h3 : (pref ++ [B1, B2])[pref.length + 1] = B2 := by simp
              rw [h3] at hum; exact hB2_sub_B1 hum
          have hucur : u ∈ bridgeCur n M k := by
            rcases Finset.mem_union.mp huB1 with h | h
            · exact h
            · exact False.elim (hnew_not_Vk u h huVk)
          by_cases hjL : j < pref.length
          · rw [List.getElem_append_left hjL]
            have hlast_eq : pref[pref.length - 1] = bridgeCur n M k := by
              rw [← List.getLast_eq_getElem hneP]; exact hlastP
            have hj_le : j ≤ pref.length - 1 := by omega
            have hpref_len : pref.length = (bagsL ++ bridgeBags n M k).length := rfl
            have hpl_lt : pref.length - 1 < (bagsL ++ bridgeBags n M k).length := by omega
            refine hriP u i j (pref.length - 1) hij hj_le (hpref_len ▸ hiL) (hpref_len ▸ hjL) hpl_lt hui ?_
            rw [hlast_eq]; exact hucur
          · have hjcases : j = pref.length ∨ j = pref.length + 1 := by omega
            rcases hjcases with rfl | rfl
            · simp [huB1]
            · have : pref.length + 1 = m := by omega
              subst this; exact hum
        · have : j = i ∨ j = m := by omega
          rcases this with rfl | rfl
          · exact hui
          · exact hum

set_option maxHeartbeats 800000 in
/-- Full construction for Part 2 of L-lib-1225! -/
lemma sharpness_part (n : Nat) :
    ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (shore side : Fin N → Bool)
      (tag : Fin N → Option (Word n × Bool)),
      N ≤ 225000 * (n + 1) * 2 ^ n ∧
      (∀ u, u ∉ G u ∧ (G u).card ≤ 3) ∧
      (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
      (∀ u, ∀ v ∈ G u, shore u ≠ shore v) ∧
      (∀ u, ((G u).filter (fun v => side v ≠ side u)).card ≤ 1) ∧
      ((Finset.univ : Finset (Fin N)).filter (fun u =>
        side u = false ∧ ∃ v ∈ G u, side v = true)).card ≤ n ∧
      (∃ (l : Nat) (bag : Fin l → Finset (Fin N)),
        (∀ t, (bag t).card ≤ n + 41) ∧ (∀ u, ∃ t, u ∈ bag t) ∧
        (∀ u v, v ∈ G u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
        ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t) ∧
      let result := fun (f g : Table n) => decide (isCountFin G (fun i =>
        (tag i).elim true (fun p => decide ((if side i then g else f) p.1 = p.2))) % 2 = 1)
      (∀ f g, result f g = decide (((Finset.univ : Finset (Word n)).filter
        (fun y => f y && g y)).card % 2 = 1)) ∧
      ∀ (k : Nat) (send : Table n → Fin k → Bool) (recv : (Fin k → Bool) → Table n → Bool),
        (∀ f g, recv (send f) g = result f g) → 2 ^ n ≤ k := by
  let S := sideGraph n
  obtain ⟨actS, hwfS, hsemS⟩ := sideGraph_props n
  let M := S.nv
  have hS_nv : (sideGraph n).nv = M := rfl
  have hM_def : M = S.nv := rfl
  have hM_ge : n ≤ M := hwfS.n_le
  have hM_le : M ≤ 27 * (n + 1) * 2 ^ n := sideGraph_nv_le n
  let N := 2 * M + 2 * n
  have hN_def : N = 2 * M + 2 * n := rfl
  -- Adjacency on Nat (within 0..N-1)
  let adjN : Nat → Finset Nat := fun u =>
    if u < M then
      if u < n then insert (2 * M + u) (S.adj u) else S.adj u
    else if u < 2 * M then
      let x := u - M
      if x < n then insert (2 * M + n + x) ((S.adj x).image (· + M))
      else (S.adj x).image (· + M)
    else if u < 2 * M + n then
      let j := u - 2 * M
      {j, 2 * M + n + j}
    else if u < 2 * M + 2 * n then
      let j := u - (2 * M + n)
      {2 * M + j, M + j}
    else ∅
  have hadjN_lt : ∀ u v, v ∈ adjN u → u < N ∧ v < N := by
    intro u v hv
    simp only [adjN] at hv
    split_ifs at hv with h1 h2 h3 h4 h5 h6
    · rcases Finset.mem_insert.mp hv with rfl | hv'
      · omega
      · have := hwfS.adj_lt u v hv'; omega
    · have := hwfS.adj_lt u v hv; omega
    · rcases Finset.mem_insert.mp hv with rfl | hv'
      · omega
      · simp only [Finset.mem_image] at hv'; rcases hv' with ⟨y, hy, rfl⟩
        have := hwfS.adj_lt (u - M) y hy; omega
    · simp only [Finset.mem_image] at hv; rcases hv with ⟨y, hy, rfl⟩
      have := hwfS.adj_lt (u - M) y hy; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> omega
    · simp at hv
  let shoreN : Nat → Bool := fun u =>
    if u < M then S.shore u
    else if u < 2 * M then !(S.shore (u - M))
    else if u < 2 * M + n then false
    else true
  let sideN : Nat → Bool := fun u =>
    if u < M then false
    else if u < 2 * M then true
    else if u < 2 * M + n then false
    else true
  let tagN : Nat → Option (Word n × Bool) := fun u =>
    if u < M then S.tag u
    else if u < 2 * M then S.tag (u - M)
    else none
  let G : Fin N → Finset (Fin N) := fun u =>
    Finset.univ.filter (fun v => v.val ∈ adjN u.val)
  have hmemG : ∀ u v : Fin N, v ∈ G u ↔ v.val ∈ adjN u.val := by
    intro u v; simp [G]
  have hcardG : ∀ u : Fin N, (G u).card = (adjN u.val).card := by
    intro u
    refine Finset.card_bij (fun v _ => v.val) ?_ ?_ ?_
    · intro v hv; exact (hmemG u v).mp hv
    · intro v1 _ v2 _ h; exact Fin.ext h
    · intro x hx
      have hlt := (hadjN_lt u.val x hx).2
      exact ⟨⟨x, hlt⟩, (hmemG u ⟨x, hlt⟩).mpr hx, rfl⟩
  let shore : Fin N → Bool := fun u => shoreN u.val
  let side : Fin N → Bool := fun u => sideN u.val
  let tag : Fin N → Option (Word n × Bool) := fun u => tagN u.val
  -- Helper characterization of adjN
  have hadjN_iff : ∀ u v, v ∈ adjN u ↔
      (u < M ∧ v < M ∧ v ∈ S.adj u) ∨
      (M ≤ u ∧ u < 2 * M ∧ M ≤ v ∧ v < 2 * M ∧ (v - M) ∈ S.adj (u - M)) ∨
      (∃ j < n, (u = j ∧ v = 2 * M + j) ∨ (u = 2 * M + j ∧ v = j) ∨
                (u = 2 * M + j ∧ v = 2 * M + n + j) ∨ (u = 2 * M + n + j ∧ v = 2 * M + j) ∨
                (u = 2 * M + n + j ∧ v = M + j) ∨ (u = M + j ∧ v = 2 * M + n + j)) := by
    intro u v
    simp only [adjN]
    split_ifs with h1 h2 h3 h4 h5 h6
    · simp only [Finset.mem_insert]; constructor
      · rintro (rfl | hv)
        · exact Or.inr (Or.inr ⟨u, h2, Or.inl ⟨rfl, rfl⟩⟩)
        · exact Or.inl ⟨h1, (hwfS.adj_lt u v hv).2, hv⟩
      · rintro (⟨_, _, hv⟩ | ⟨hge, _⟩ | ⟨j, hj, h⟩)
        · exact Or.inr hv
        · omega
        · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact Or.inl rfl
          all_goals omega
    · constructor
      · intro hv; exact Or.inl ⟨h1, (hwfS.adj_lt u v hv).2, hv⟩
      · rintro (⟨_, _, hv⟩ | ⟨hge, _⟩ | ⟨j, hj, h⟩)
        · exact hv
        · omega
        · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    · simp only [Finset.mem_insert, Finset.mem_image]; constructor
      · rintro (rfl | ⟨y, hy, rfl⟩)
        · exact Or.inr (Or.inr ⟨u - M, h4, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))))⟩)
        · have := hwfS.adj_lt (u - M) y hy
          exact Or.inr (Or.inl ⟨by omega, h3, by omega, by omega, by simpa [Nat.add_sub_cancel] using hy⟩)
      · rintro (⟨hlt, _⟩ | ⟨_, _, hv1, hv2, hv⟩ | ⟨j, hj, h⟩)
        · omega
        · exact Or.inr ⟨v - M, hv, by omega⟩
        · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨hu, hv⟩
          · omega
          · omega
          · omega
          · omega
          · omega
          · left; omega
    · simp only [Finset.mem_image]; constructor
      · rintro ⟨y, hy, rfl⟩
        have := hwfS.adj_lt (u - M) y hy
        exact Or.inr (Or.inl ⟨by omega, h3, by omega, by omega, by simpa [Nat.add_sub_cancel] using hy⟩)
      · rintro (⟨hlt, _⟩ | ⟨_, _, hv1, hv2, hv⟩ | ⟨j, hj, h⟩)
        · omega
        · exact ⟨v - M, hv, by omega⟩
        · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨hu, _⟩ <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
      · rintro (rfl | rfl)
        · exact Or.inr (Or.inr ⟨u - 2 * M, by omega, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩)
        · exact Or.inr (Or.inr ⟨u - 2 * M, by omega, Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))⟩)
      · rintro (⟨hlt, _⟩ | ⟨_, hlt, _⟩ | ⟨j, hj, h⟩)
        · omega
        · omega
        · rcases h with ⟨rfl, _⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩
          · omega
          · left; omega
          · right; omega
          all_goals omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
      · rintro (rfl | rfl)
        · exact Or.inr (Or.inr ⟨u - (2 * M + n), by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩)))⟩)
        · exact Or.inr (Or.inr ⟨u - (2 * M + n), by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))))⟩)
      · rintro (⟨hlt, _⟩ | ⟨_, hlt, _⟩ | ⟨j, hj, h⟩)
        · omega
        · omega
        · rcases h with ⟨rfl, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, _⟩
          · omega
          · omega
          · omega
          · left; omega
          · right; omega
          · omega
    · constructor
      · intro h; simp at h
      · rintro (⟨hlt, _⟩ | ⟨_, hlt, _⟩ | ⟨j, hj, h⟩)
        · omega
        · omega
        · rcases h with ⟨rfl, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ | ⟨hu, _⟩ <;> omega
  -- Semantic count identity for Full graph
  have hresult : ∀ f g : Table n,
      decide (isCountFin G (fun i =>
        (tag i).elim true (fun p => decide ((if side i then g else f) p.1 = p.2))) % 2 = 1) =
      decide (((Finset.univ : Finset (Word n)).filter (fun y => f y && g y)).card % 2 = 1) := by
    intro f g
    let liveF : Fin N → Bool := fun i =>
      (tag i).elim true (fun p => decide ((if side i then g else f) p.1 = p.2))
    let totalF : Finset (Finset (Fin N)) :=
      (Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
        (∀ u ∈ I, liveF u = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)
    let bridgeSet : Word n → Word n → Finset (Fin n → Fin 2 → Bool) := fun a b =>
      Finset.univ.filter (fun z => ∀ j : Fin n, eq3ValidB (a j) (b j) (z j) = true)
    have hbridge_card : ∀ a b : Word n, (bridgeSet a b).card = ∏ j : Fin n, eq3Cnt (a j) (b j) := by
      intro a b
      have heq : bridgeSet a b = Fintype.piFinset (fun j : Fin n =>
          (Finset.univ : Finset (Fin 2 → Bool)).filter (fun w => eq3ValidB (a j) (b j) w = true)) := by
        ext z; simp [bridgeSet, Fintype.mem_piFinset]
      rw [heq, Fintype.card_piFinset]
      refine Finset.prod_congr rfl fun j _ => (countBoolFn_eq_card 2 _).symm
    let wordSig : Word n → (Nat → Bool) := fun a u => if h : u < n then a ⟨u, h⟩ else false
    let dom :=
      (Finset.univ : Finset (Word n × Word n)).sigma (fun ab =>
        isSets S f (Finset.range n) (wordSig ab.1) ×ˢ
        isSets S g (Finset.range n) (wordSig ab.2) ×ˢ
        bridgeSet ab.1 ab.2)
    have hdom_card : dom.card =
        ∑ ab : Word n × Word n,
          cnt S f (Finset.range n) (wordSig ab.1) *
          (cnt S g (Finset.range n) (wordSig ab.2) * ∏ j : Fin n, eq3Cnt (ab.1 j) (ab.2 j)) := by
      simp only [dom, Finset.card_sigma, Finset.card_product, cnt, hbridge_card]
    have hbij : totalF.card = dom.card := by
      symm
      let toFin : Finset Nat → Finset Nat → (Fin n → Fin 2 → Bool) → Finset (Fin N) :=
        fun IL IR z =>
          Finset.univ.filter (fun u : Fin N =>
            if h0 : u.val < M then u.val ∈ IL
            else if h2 : u.val < 2 * M then u.val - M ∈ IR
            else if h1 : u.val < 2 * M + n then z ⟨u.val - 2 * M, by omega⟩ 0 = true
            else z ⟨u.val - (2 * M + n), by have := u.isLt; omega⟩ 1 = true)
      refine Finset.card_bij (fun p _ => toFin p.2.1 p.2.2.1 p.2.2.2) ?_ ?_ ?_
      · intro ⟨⟨a, b⟩, IL, IR, z⟩ hp
        simp only [dom, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product,
          isSets, bridgeSet, Finset.mem_filter, Finset.mem_powerset] at hp
        rcases hp with ⟨⟨hILsub, hILlive, hILind, hILA⟩, ⟨hIRsub, hIRlive, hIRind, hIRA⟩, hz⟩
        simp only [totalF, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · intro u hu
          simp only [toFin, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          simp only [liveF, tag, tagN, side, sideN]
          split_ifs at hu with h1 h2 h3
          · simp only [if_pos h1, Bool.false_eq_true, ↓reduceIte]; exact hILlive u.val hu
          · simp only [if_neg h1, if_pos h2, ↓reduceIte]; exact hIRlive (u.val - M) hu
          · simp only [if_neg h1, if_neg h2]; rfl
          · simp only [if_neg h1, if_neg h2]; rfl
        · intro u hu v hv hvmem
          have hadj := (hmemG u v).mp hv
          simp only [toFin, Finset.mem_filter, Finset.mem_univ, true_and] at hu hvmem
          rcases (hadjN_iff u.val v.val).mp hadj with
            ⟨hu1, hv1, huv⟩ | ⟨hu1, hu2, hv1, hv2, huv⟩ | ⟨j, hj, hcase⟩
          · rw [dif_pos hu1] at hu; rw [dif_pos hv1] at hvmem
            exact hILind u.val hu v.val huv hvmem
          · rw [dif_neg (by omega), dif_pos hu2] at hu
            rw [dif_neg (by omega), dif_pos hv2] at hvmem
            exact hIRind (u.val - M) hu (v.val - M) huv hvmem
          · have hzj := hz ⟨j, hj⟩
            simp only [eq3ValidB, Bool.and_eq_true, Bool.not_eq_true'] at hzj
            have ha_dec : decide (j ∈ IL) = a ⟨j, hj⟩ := by
              have := hILA j (Finset.mem_range.mpr hj)
              simp only [wordSig, dif_pos hj] at this; exact this
            have hb_dec : decide (j ∈ IR) = b ⟨j, hj⟩ := by
              have := hIRA j (Finset.mem_range.mpr hj)
              simp only [wordSig, dif_pos hj] at this; exact this
            rcases hcase with ⟨hu_eq, hv_eq⟩ | ⟨hu_eq, hv_eq⟩ | ⟨hu_eq, hv_eq⟩ |
              ⟨hu_eq, hv_eq⟩ | ⟨hu_eq, hv_eq⟩ | ⟨hu_eq, hv_eq⟩
            · rw [dif_pos (by omega)] at hu; rw [hu_eq] at hu
              rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)] at hvmem
              have hjeq : (⟨v.val - 2 * M, by omega⟩ : Fin n) = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
              rw [hjeq] at hvmem
              have ha1 : a ⟨j, hj⟩ = true := by rw [← ha_dec]; exact decide_eq_true hu
              simp [ha1, hvmem] at hzj
            · rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)] at hu
              rw [dif_pos (by omega)] at hvmem; rw [hv_eq] at hvmem
              have hjeq : (⟨u.val - 2 * M, by omega⟩ : Fin n) = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
              rw [hjeq] at hu
              have ha1 : a ⟨j, hj⟩ = true := by rw [← ha_dec]; exact decide_eq_true hvmem
              simp [ha1, hu] at hzj
            · rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)] at hu
              rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)] at hvmem
              have h1 : (⟨u.val - 2 * M, by omega⟩ : Fin n) = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
              have h2 : (⟨v.val - (2 * M + n), by omega⟩ : Fin n) = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
              rw [h1] at hu; rw [h2] at hvmem
              simp [hu, hvmem] at hzj
            · rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)] at hu
              rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)] at hvmem
              have h1 : (⟨u.val - (2 * M + n), by omega⟩ : Fin n) = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
              have h2 : (⟨v.val - 2 * M, by omega⟩ : Fin n) = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
              rw [h1] at hu; rw [h2] at hvmem
              simp [hu, hvmem] at hzj
            · rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)] at hu
              rw [dif_neg (by omega), dif_pos (by omega)] at hvmem
              have h1 : (⟨u.val - (2 * M + n), by omega⟩ : Fin n) = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
              rw [h1] at hu
              have hvj : v.val - M = j := by omega
              rw [hvj] at hvmem
              have hb1 : b ⟨j, hj⟩ = true := by rw [← hb_dec]; exact decide_eq_true hvmem
              simp [hu, hb1] at hzj
            · rw [dif_neg (by omega), dif_pos (by omega)] at hu
              rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)] at hvmem
              have h2 : (⟨v.val - (2 * M + n), by omega⟩ : Fin n) = ⟨j, hj⟩ := Fin.ext (by dsimp; omega)
              rw [h2] at hvmem
              have huj : u.val - M = j := by omega
              rw [huj] at hu
              have hb1 : b ⟨j, hj⟩ = true := by rw [← hb_dec]; exact decide_eq_true hu
              simp [hvmem, hb1] at hzj
      · intro ⟨⟨a1, b1⟩, IL1, IR1, z1⟩ hp1 ⟨⟨a2, b2⟩, IL2, IR2, z2⟩ hp2 heq
        simp only [dom, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product,
          isSets, Finset.mem_filter, Finset.mem_powerset] at hp1 hp2
        have hIL : IL1 = IL2 := by
          ext x
          by_cases hx : x < M
          · have h1 : (⟨x, by omega⟩ : Fin N) ∈ toFin IL1 IR1 z1 ↔ x ∈ IL1 := by
              simp [toFin, hx]
            have h2 : (⟨x, by omega⟩ : Fin N) ∈ toFin IL2 IR2 z2 ↔ x ∈ IL2 := by
              simp [toFin, hx]
            rw [← h1, ← h2, heq]
          · constructor
            · intro h; exact False.elim (hx (Finset.mem_range.mp (hp1.1.1 h)))
            · intro h; exact False.elim (hx (Finset.mem_range.mp (hp2.1.1 h)))
        have hIR : IR1 = IR2 := by
          ext x
          by_cases hx : x < M
          · have h1 : (⟨M + x, by omega⟩ : Fin N) ∈ toFin IL1 IR1 z1 ↔ x ∈ IR1 := by
              simp only [toFin, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [dif_neg (by omega), dif_pos (by omega)]; simp
            have h2 : (⟨M + x, by omega⟩ : Fin N) ∈ toFin IL2 IR2 z2 ↔ x ∈ IR2 := by
              simp only [toFin, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [dif_neg (by omega), dif_pos (by omega)]; simp
            rw [← h1, ← h2, heq]
          · constructor
            · intro h; exact False.elim (hx (Finset.mem_range.mp (hp1.2.1.1 h)))
            · intro h; exact False.elim (hx (Finset.mem_range.mp (hp2.2.1.1 h)))
        have hz : z1 = z2 := by
          ext j k; fin_cases k
          · have h1 : (⟨2 * M + j.val, by omega⟩ : Fin N) ∈ toFin IL1 IR1 z1 ↔ z1 j 0 = true := by
              simp only [toFin, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
              have hjeq : (⟨2 * M + j.val - 2 * M, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
              rw [hjeq]
            have h2 : (⟨2 * M + j.val, by omega⟩ : Fin N) ∈ toFin IL2 IR2 z2 ↔ z2 j 0 = true := by
              simp only [toFin, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
              have hjeq : (⟨2 * M + j.val - 2 * M, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
              rw [hjeq]
            rw [heq] at h1
            have heqv : z1 j 0 = true ↔ z2 j 0 = true := h1.symm.trans h2
            cases hv1 : z1 j 0 <;> cases hv2 : z2 j 0 <;> simp [hv1, hv2] at heqv ⊢
          · have h1 : (⟨2 * M + n + j.val, by omega⟩ : Fin N) ∈ toFin IL1 IR1 z1 ↔ z1 j 1 = true := by
              simp only [toFin, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
              have hjeq : (⟨2 * M + n + j.val - (2 * M + n), by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
              rw [hjeq]
            have h2 : (⟨2 * M + n + j.val, by omega⟩ : Fin N) ∈ toFin IL2 IR2 z2 ↔ z2 j 1 = true := by
              simp only [toFin, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
              have hjeq : (⟨2 * M + n + j.val - (2 * M + n), by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
              rw [hjeq]
            rw [heq] at h1
            have heqv : z1 j 1 = true ↔ z2 j 1 = true := h1.symm.trans h2
            cases hv1 : z1 j 1 <;> cases hv2 : z2 j 1 <;> simp [hv1, hv2] at heqv ⊢
        have ha : a1 = a2 := by
          ext j
          have h1 := hp1.1.2.2.2 j.val (Finset.mem_range.mpr j.isLt)
          have h2 := hp2.1.2.2.2 j.val (Finset.mem_range.mpr j.isLt)
          simp only [wordSig, dif_pos j.isLt] at h1 h2
          rw [← h1, ← h2, hIL]
        have hb : b1 = b2 := by
          ext j
          have h1 := hp1.2.1.2.2.2 j.val (Finset.mem_range.mpr j.isLt)
          have h2 := hp2.2.1.2.2.2 j.val (Finset.mem_range.mpr j.isLt)
          simp only [wordSig, dif_pos j.isLt] at h1 h2
          rw [← h1, ← h2, hIR]
        subst ha; subst hb; subst hIL; subst hIR; subst hz; rfl
      · intro I hI
        simp only [totalF, Finset.mem_filter, Finset.mem_univ, true_and] at hI
        let IL : Finset Nat := (Finset.range M).filter (fun x =>
          if h : x < N then ⟨x, h⟩ ∈ I else false)
        let IR : Finset Nat := (Finset.range M).filter (fun x =>
          if h : M + x < N then ⟨M + x, h⟩ ∈ I else false)
        let a : Word n := fun j => decide ((⟨j.val, by omega⟩ : Fin N) ∈ I)
        let b : Word n := fun j => decide ((⟨M + j.val, by omega⟩ : Fin N) ∈ I)
        let z : Fin n → Fin 2 → Bool := fun j =>
          ![decide ((⟨2 * M + j.val, by omega⟩ : Fin N) ∈ I),
            decide ((⟨2 * M + n + j.val, by omega⟩ : Fin N) ∈ I)]
        refine ⟨⟨(a, b), (IL, IR, z)⟩, ?_, ?_⟩
        · simp only [dom, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product,
            isSets, bridgeSet, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨⟨Finset.filter_subset _ _, ?_, ?_, ?_⟩,
                  ⟨Finset.filter_subset _ _, ?_, ?_, ?_⟩, ?_⟩
          · intro x hx
            simp only [IL, Finset.mem_filter, Finset.mem_range] at hx
            rcases hx with ⟨hxM, hxI⟩
            rw [dif_pos (by omega)] at hxI
            have hl := hI.1 ⟨x, by omega⟩ hxI
            simp only [liveF, tag, tagN, side, sideN, if_pos hxM] at hl
            exact hl
          · intro x hx y hy hyI
            simp only [IL, Finset.mem_filter, Finset.mem_range] at hx hyI
            rw [dif_pos (by omega)] at hx hyI
            have hadj : (⟨y, by omega⟩ : Fin N) ∈ G ⟨x, by omega⟩ :=
              (hmemG _ _).mpr ((hadjN_iff x y).mpr (Or.inl ⟨hx.1, hyI.1, hy⟩))
            exact hI.2 ⟨x, by omega⟩ hx.2 ⟨y, by omega⟩ hadj hyI.2
          · intro u hu
            have hult : u < n := Finset.mem_range.mp hu
            simp only [IL, wordSig, dif_pos hult, Finset.mem_filter, Finset.mem_range,
              show u < M by omega, true_and, dif_pos (show u < N by omega), a]
          · intro x hx
            simp only [IR, Finset.mem_filter, Finset.mem_range] at hx
            rcases hx with ⟨hxM, hxI⟩
            rw [dif_pos (by omega)] at hxI
            have hl := hI.1 ⟨M + x, by omega⟩ hxI
            simp only [liveF, tag, tagN, side, sideN,
              if_neg (show ¬(M + x < M) by omega), if_pos (show M + x < 2 * M by omega),
              Nat.add_sub_cancel_left] at hl
            exact hl
          · intro x hx y hy hyI
            simp only [IR, Finset.mem_filter, Finset.mem_range] at hx hyI
            rw [dif_pos (by omega)] at hx hyI
            have hadj : (⟨M + y, by omega⟩ : Fin N) ∈ G ⟨M + x, by omega⟩ :=
              (hmemG _ _).mpr ((hadjN_iff (M + x) (M + y)).mpr
                (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by simpa using hy⟩)))
            exact hI.2 ⟨M + x, by omega⟩ hx.2 ⟨M + y, by omega⟩ hadj hyI.2
          · intro u hu
            have hult : u < n := Finset.mem_range.mp hu
            simp only [IR, wordSig, dif_pos hult, Finset.mem_filter, Finset.mem_range,
              show u < M by omega, true_and, dif_pos (show M + u < N by omega), b]
          · intro j
            simp only [eq3ValidB, Bool.and_eq_true, Bool.not_eq_true', z, a, b,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
            have he1 : (⟨2 * M + j.val, by omega⟩ : Fin N) ∈ G ⟨j.val, by omega⟩ :=
              (hmemG _ _).mpr ((hadjN_iff _ _).mpr (Or.inr (Or.inr ⟨j.val, j.isLt, Or.inl ⟨rfl, rfl⟩⟩)))
            have he2 : (⟨2 * M + n + j.val, by omega⟩ : Fin N) ∈ G ⟨2 * M + j.val, by omega⟩ :=
              (hmemG _ _).mpr ((hadjN_iff _ _).mpr (Or.inr (Or.inr ⟨j.val, j.isLt, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩)))
            have he3 : (⟨M + j.val, by omega⟩ : Fin N) ∈ G ⟨2 * M + n + j.val, by omega⟩ :=
              (hmemG _ _).mpr ((hadjN_iff _ _).mpr (Or.inr (Or.inr ⟨j.val, j.isLt, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩)))
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · by_cases h1 : (⟨j.val, by omega⟩ : Fin N) ∈ I <;>
                by_cases h2 : (⟨2 * M + j.val, by omega⟩ : Fin N) ∈ I
              · exact False.elim (hI.2 _ h1 _ he1 h2)
              all_goals simp [h1, h2]
            · by_cases h1 : (⟨2 * M + j.val, by omega⟩ : Fin N) ∈ I <;>
                by_cases h2 : (⟨2 * M + n + j.val, by omega⟩ : Fin N) ∈ I
              · exact False.elim (hI.2 _ h1 _ he2 h2)
              all_goals simp [h1, h2]
            · by_cases h1 : (⟨2 * M + n + j.val, by omega⟩ : Fin N) ∈ I <;>
                by_cases h2 : (⟨M + j.val, by omega⟩ : Fin N) ∈ I
              · exact False.elim (hI.2 _ h1 _ he3 h2)
              all_goals simp [h1, h2]
        · ext u
          have hu_lt := u.isLt
          simp only [toFin, Finset.mem_filter, Finset.mem_univ, true_and]
          split_ifs with h1 h2 h3
          · simp only [IL, Finset.mem_filter, Finset.mem_range, h1, true_and, dif_pos hu_lt]
          · simp only [IR, Finset.mem_filter, Finset.mem_range, show u.val - M < M by omega,
              true_and, dif_pos (show M + (u.val - M) < N by omega)]
            have heq : (⟨M + (u.val - M), by omega⟩ : Fin N) = u := Fin.ext (by dsimp; omega)
            rw [heq]
          · simp only [z, Matrix.cons_val_zero, decide_eq_true_eq]
            have heq : (⟨2 * M + (u.val - 2 * M), by omega⟩ : Fin N) = u := Fin.ext (by dsimp; omega)
            rw [heq]
          · simp only [z, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, decide_eq_true_eq]
            have heq : (⟨2 * M + n + (u.val - (2 * M + n)), by omega⟩ : Fin N) = u := Fin.ext (by dsimp; omega)
            rw [heq]
    -- Reduce totalF.card % 2 to inner product mod 2
    have hmod : isCountFin G liveF % 2 =
        ((Finset.univ : Finset (Word n)).filter (fun y => f y && g y)).card % 2 := by
      change totalF.card % 2 = _
      rw [hbij, hdom_card, sum_mod_two]
      have hsemS' : ∀ (t : Table n) (σ : Nat → Bool),
          cnt S t (Finset.range n) σ % 2 =
            if t (fun j : Fin n => σ j.val) = true then 1 else 0 := hsemS
      have hterm : ∀ ab : Word n × Word n,
          (cnt S f (Finset.range n) (wordSig ab.1) *
            (cnt S g (Finset.range n) (wordSig ab.2) * ∏ j : Fin n, eq3Cnt (ab.1 j) (ab.2 j))) % 2 =
          if ab.1 = ab.2 ∧ (f ab.1 && g ab.1) = true then 1 else 0 := by
        intro ⟨a, b⟩
        rw [mul_mod_two, hsemS' f (wordSig a), mul_mod_two (cnt S g _ _), hsemS' g (wordSig b), prod_mod_two]
        have hwa : (fun j : Fin n => wordSig a j.val) = a := by
          ext j; simp [wordSig, j.isLt]
        have hwb : (fun j : Fin n => wordSig b j.val) = b := by
          ext j; simp [wordSig, j.isLt]
        rw [hwa, hwb]
        have hprod : (∏ j : Fin n, eq3Cnt (a j) (b j) % 2) = if a = b then 1 else 0 := by
          have h1 : (∏ j : Fin n, eq3Cnt (a j) (b j) % 2) =
              ∏ j : Fin n, (if b j = a j then (1 : Nat) else 0) :=
            Finset.prod_congr rfl fun j _ => cnt_eq3 (a j) (b j)
          rw [h1]
          by_cases hab : a = b
          · subst hab; simp
          · rw [if_neg hab]
            have hex : ∃ j : Fin n, b j ≠ a j := by
              by_contra hall; push_neg at hall
              exact hab (funext fun j => (hall j).symm)
            rcases hex with ⟨j0, hj0⟩
            exact Finset.prod_eq_zero (Finset.mem_univ j0) (by simp [hj0])
        rw [hprod]
        by_cases hab : a = b
        · subst hab
          cases hfa : f a <;> cases hga : g a <;> simp
        · simp [hab]
      rw [Finset.sum_congr rfl (fun ab _ => hterm ab)]
      have hsum_diag :
          (∑ ab : Word n × Word n, if ab.1 = ab.2 ∧ (f ab.1 && g ab.1) = true then (1 : Nat) else 0) =
          ((Finset.univ : Finset (Word n)).filter (fun y => f y && g y)).card := by
        rw [Fintype.sum_prod_type]
        have hinner : ∀ a : Word n,
            (∑ b : Word n, if a = b ∧ (f a && g a) = true then (1 : Nat) else 0) =
            if (f a && g a) = true then 1 else 0 := by
          intro a
          rw [Finset.sum_eq_single a]
          · simp
          · intro b _ hne; simp [hne.symm]
          · intro h; exact False.elim (h (Finset.mem_univ _))
        simp only [hinner, Finset.sum_boole, Nat.cast_id]
      rw [hsum_diag]
    exact congrArg (fun x => decide (x = 1)) hmod
  -- Assemble all conditions of sharpness_part
  refine ⟨N, G, shore, side, tag, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hresult, ?_⟩
  · -- N ≤ 225000 * (n + 1) * 2^n
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hn_le : 2 * n ≤ 2 * (n + 1) * 2 ^ n := by
      calc 2 * n ≤ 2 * (n + 1) * 1 := by omega
      _ ≤ 2 * (n + 1) * 2 ^ n := Nat.mul_le_mul_left _ hpow
    have hbig : 56 * (n + 1) * 2 ^ n ≤ 225000 * (n + 1) * 2 ^ n := by
      exact Nat.mul_le_mul_right _ (by omega)
    calc N = 2 * M + 2 * n := rfl
      _ ≤ 2 * (27 * (n + 1) * 2 ^ n) + 2 * (n + 1) * 2 ^ n := by omega
      _ = 56 * (n + 1) * 2 ^ n := by ring
      _ ≤ 225000 * (n + 1) * 2 ^ n := hbig
  · -- no loops and deg ≤ 3
    intro u
    refine ⟨?_, ?_⟩
    · rw [hmemG, hadjN_iff]
      rintro (⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨j, hj, h⟩)
      · exact hwfS.no_loop u.val h
      · exact hwfS.no_loop (u.val - M) h
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rw [hcardG u]
      simp only [adjN]
      split_ifs with h1 h2 h3 h4 h5 h6
      · exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right (hwfS.in_deg u.val h2) 1) |>.trans (by omega)
      · exact hwfS.deg_le u.val
      · have hdeg := hwfS.in_deg (u.val - M) h4
        exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right
          (le_trans Finset.card_image_le hdeg) 1) |>.trans (by omega)
      · exact le_trans Finset.card_image_le (hwfS.deg_le (u.val - M))
      · exact le_trans (Finset.card_insert_le _ _) (by simp)
      · exact le_trans (Finset.card_insert_le _ _) (by simp)
      · simp
  · -- symmetric
    intro u v
    rw [hmemG, hmemG, hadjN_iff, hadjN_iff]
    constructor
    · rintro (⟨h1, h2, h⟩ | ⟨h1, h2, h3, h4, h⟩ | ⟨j, hj, h⟩)
      · exact Or.inl ⟨h2, h1, (hwfS.symm u.val v.val).mp h⟩
      · exact Or.inr (Or.inl ⟨h3, h4, h1, h2, (hwfS.symm _ _).mp h⟩)
      · exact Or.inr (Or.inr ⟨j, hj, by tauto⟩)
    · rintro (⟨h1, h2, h⟩ | ⟨h1, h2, h3, h4, h⟩ | ⟨j, hj, h⟩)
      · exact Or.inl ⟨h2, h1, (hwfS.symm v.val u.val).mp h⟩
      · exact Or.inr (Or.inl ⟨h3, h4, h1, h2, (hwfS.symm _ _).mp h⟩)
      · exact Or.inr (Or.inr ⟨j, hj, by tauto⟩)
  · -- bipartite
    intro u v hv
    have hS_in_shore : ∀ j < n, S.shore j = true := hwfS.in_shore
    rcases (hadjN_iff u.val v.val).mp ((hmemG u v).mp hv) with
      ⟨h1, h2, h⟩ | ⟨h1, h2, h3, h4, h⟩ | ⟨j, hj, hcase⟩
    · simp only [shore, shoreN, if_pos h1, if_pos h2]; exact hwfS.bip u.val v.val h
    · simp only [shore, shoreN, if_neg (show ¬(u.val < M) by omega), if_pos h2,
        if_neg (show ¬(v.val < M) by omega), if_pos h4]
      intro heq; exact hwfS.bip (u.val - M) (v.val - M) h (Bool.not_inj heq)
    · rcases hcase with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
      · simp only [shore, shoreN, hu, hv, if_pos (show j < M by omega),
          if_neg (show ¬(2 * M + j < M) by omega), if_neg (show ¬(2 * M + j < 2 * M) by omega),
          if_pos (show 2 * M + j < 2 * M + n by omega), hS_in_shore j hj]; decide
      · simp only [shore, shoreN, hu, hv, if_pos (show j < M by omega),
          if_neg (show ¬(2 * M + j < M) by omega), if_neg (show ¬(2 * M + j < 2 * M) by omega),
          if_pos (show 2 * M + j < 2 * M + n by omega), hS_in_shore j hj]; decide
      · simp only [shore, shoreN, hu, hv,
          if_neg (show ¬(2 * M + j < M) by omega), if_neg (show ¬(2 * M + j < 2 * M) by omega),
          if_pos (show 2 * M + j < 2 * M + n by omega),
          if_neg (show ¬(2 * M + n + j < M) by omega), if_neg (show ¬(2 * M + n + j < 2 * M) by omega),
          if_neg (show ¬(2 * M + n + j < 2 * M + n) by omega)]; decide
      · simp only [shore, shoreN, hu, hv,
          if_neg (show ¬(2 * M + j < M) by omega), if_neg (show ¬(2 * M + j < 2 * M) by omega),
          if_pos (show 2 * M + j < 2 * M + n by omega),
          if_neg (show ¬(2 * M + n + j < M) by omega), if_neg (show ¬(2 * M + n + j < 2 * M) by omega),
          if_neg (show ¬(2 * M + n + j < 2 * M + n) by omega)]; decide
      · simp only [shore, shoreN, hu, hv,
          if_neg (show ¬(2 * M + n + j < M) by omega), if_neg (show ¬(2 * M + n + j < 2 * M) by omega),
          if_neg (show ¬(2 * M + n + j < 2 * M + n) by omega),
          if_neg (show ¬(M + j < M) by omega), if_pos (show M + j < 2 * M by omega),
          Nat.add_sub_cancel_left, hS_in_shore j hj]; decide
      · simp only [shore, shoreN, hu, hv,
          if_neg (show ¬(2 * M + n + j < M) by omega), if_neg (show ¬(2 * M + n + j < 2 * M) by omega),
          if_neg (show ¬(2 * M + n + j < 2 * M + n) by omega),
          if_neg (show ¬(M + j < M) by omega), if_pos (show M + j < 2 * M by omega),
          Nat.add_sub_cancel_left, hS_in_shore j hj]; decide
  · -- cut matching (each vertex has ≤ 1 cross-side neighbor)
    intro u
    have hcross : ∀ v : Fin N, v ∈ G u → side v ≠ side u →
        (∃ j < n, u.val = 2 * M + j ∧ v.val = 2 * M + n + j) ∨
        (∃ j < n, u.val = 2 * M + n + j ∧ v.val = 2 * M + j) := by
      intro v hv hne
      rcases (hadjN_iff u.val v.val).mp ((hmemG u v).mp hv) with
        ⟨h1, h2, _⟩ | ⟨h1, h2, h3, h4, _⟩ | ⟨j, hj, hcase⟩
      · simp only [side, sideN, if_pos h1, if_pos h2] at hne; exact False.elim (hne rfl)
      · simp only [side, sideN, if_neg (show ¬(u.val < M) by omega), if_pos h2,
          if_neg (show ¬(v.val < M) by omega), if_pos h4] at hne; exact False.elim (hne rfl)
      · rcases hcase with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩
        · simp only [side, sideN, hu, hv, if_pos (show j < M by omega),
            if_neg (show ¬(2 * M + j < M) by omega), if_neg (show ¬(2 * M + j < 2 * M) by omega),
            if_pos (show 2 * M + j < 2 * M + n by omega)] at hne; exact False.elim (hne rfl)
        · simp only [side, sideN, hu, hv, if_pos (show j < M by omega),
            if_neg (show ¬(2 * M + j < M) by omega), if_neg (show ¬(2 * M + j < 2 * M) by omega),
            if_pos (show 2 * M + j < 2 * M + n by omega)] at hne; exact False.elim (hne rfl)
        · exact Or.inl ⟨j, hj, hu, hv⟩
        · exact Or.inr ⟨j, hj, hu, hv⟩
        · simp only [side, sideN, hu, hv,
            if_neg (show ¬(2 * M + n + j < M) by omega), if_neg (show ¬(2 * M + n + j < 2 * M) by omega),
            if_neg (show ¬(2 * M + n + j < 2 * M + n) by omega),
            if_neg (show ¬(M + j < M) by omega), if_pos (show M + j < 2 * M by omega)] at hne
          exact False.elim (hne rfl)
        · simp only [side, sideN, hu, hv,
            if_neg (show ¬(2 * M + n + j < M) by omega), if_neg (show ¬(2 * M + n + j < 2 * M) by omega),
            if_neg (show ¬(2 * M + n + j < 2 * M + n) by omega),
            if_neg (show ¬(M + j < M) by omega), if_pos (show M + j < 2 * M by omega)] at hne
          exact False.elim (hne rfl)
    refine Finset.card_le_one.mpr ?_
    intro v1 hv1 v2 hv2
    simp only [Finset.mem_filter] at hv1 hv2
    rcases hcross v1 hv1.1 hv1.2 with ⟨j1, _, hu1, hv1'⟩ | ⟨j1, _, hu1, hv1'⟩ <;>
    rcases hcross v2 hv2.1 hv2.2 with ⟨j2, _, hu2, hv2'⟩ | ⟨j2, _, hu2, hv2'⟩
    · exact Fin.ext (by omega)
    · omega
    · omega
    · exact Fin.ext (by omega)
  · -- cut size ≤ n
    have hsub : ((Finset.univ : Finset (Fin N)).filter (fun u =>
        side u = false ∧ ∃ v ∈ G u, side v = true)) ⊆
        (Finset.univ : Finset (Fin n)).image (fun j => ⟨2 * M + j.val, by omega⟩) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rcases hu with ⟨hsu, v, hv, hsv⟩
      have hne : side v ≠ side u := by rw [hsu, hsv]; decide
      rcases (hadjN_iff u.val v.val).mp ((hmemG u v).mp hv) with
        ⟨h1, h2, _⟩ | ⟨h1, h2, h3, h4, _⟩ | ⟨j, hj, hcase⟩
      · simp only [side, sideN, if_pos h1, if_pos h2] at hne; exact False.elim (hne rfl)
      · simp only [side, sideN, if_neg (show ¬(u.val < M) by omega), if_pos h2,
          if_neg (show ¬(v.val < M) by omega), if_pos h4] at hne; exact False.elim (hne rfl)
      · rcases hcase with ⟨hu', hv'⟩ | ⟨hu', hv'⟩ | ⟨hu', hv'⟩ | ⟨hu', hv'⟩ | ⟨hu', hv'⟩ | ⟨hu', hv'⟩
        · simp only [side, sideN, hv', if_neg (show ¬(2 * M + j < M) by omega),
            if_neg (show ¬(2 * M + j < 2 * M) by omega),
            if_pos (show 2 * M + j < 2 * M + n by omega)] at hsv; exact False.elim (Bool.noConfusion hsv)
        · simp only [side, sideN, hv', if_pos (show j < M by omega)] at hsv; exact False.elim (Bool.noConfusion hsv)
        · exact Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, Fin.ext (by dsimp; omega)⟩
        · simp only [side, sideN, hu', if_neg (show ¬(2 * M + n + j < M) by omega),
            if_neg (show ¬(2 * M + n + j < 2 * M) by omega),
            if_neg (show ¬(2 * M + n + j < 2 * M + n) by omega)] at hsu; exact False.elim (Bool.noConfusion hsu)
        · simp only [side, sideN, hu', if_neg (show ¬(2 * M + n + j < M) by omega),
            if_neg (show ¬(2 * M + n + j < 2 * M) by omega),
            if_neg (show ¬(2 * M + n + j < 2 * M + n) by omega)] at hsu; exact False.elim (Bool.noConfusion hsu)
        · simp only [side, sideN, hu', if_neg (show ¬(M + j < M) by omega),
            if_pos (show M + j < 2 * M by omega)] at hsu; exact False.elim (Bool.noConfusion hsu)
    exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le (by simp))
  · -- Path decomposition of width ≤ n + 41
    let bagsL := S.bags.reverse
    let bagsR := S.bags.map (Finset.image (· + M))
    let pref := bagsL ++ bridgeBags n M n
    let allBags := pref ++ bagsR
    have hS_bne : S.bags ≠ [] := hwfS.bags_ne
    have hS_bhead : S.bags.head hS_bne = Finset.range n := hwfS.bags_head
    have hneL : bagsL ≠ [] := by simp [bagsL, hS_bne]
    have hlastL : bagsL.getLast hneL = Finset.range n := by
      simp only [bagsL, List.getLast_reverse]
      exact hS_bhead
    have hsubL : ∀ B ∈ bagsL, B ⊆ Finset.range M := by
      intro B hB; simp only [bagsL, List.mem_reverse] at hB; exact hwfS.bags_sub B hB
    have hcardL : ∀ B ∈ bagsL, B.card ≤ n + 15 := by
      intro B hB; simp only [bagsL, List.mem_reverse] at hB; exact hwfS.bags_card B hB
    have hriL : BagsRI bagsL := bags_reverse_ri S.bags hwfS.bags_ri
    obtain ⟨hneP, hlastP, hsubP, hcardP, hriP⟩ :=
      bridge_prefix_ri n M (n + 15) bagsL hM_ge (by omega) hneL hlastL hsubL hcardL hriL n (le_refl n)
    have hlastP' : pref.getLast hneP = (Finset.range n).image (· + M) := by
      rw [hlastP]; ext u; simp [bridgeCur, Nat.add_comm]
    have hneR : bagsR ≠ [] := by simp [bagsR, hS_bne]
    have hheadR : bagsR.head hneR = (Finset.range n).image (· + M) := by
      simp only [bagsR, List.head_map, hS_bhead]
    have hsubR : ∀ B ∈ bagsR, B ⊆ (Finset.range M).image (· + M) := by
      intro B hB
      simp only [bagsR, List.mem_map] at hB
      rcases hB with ⟨B0, hB0, rfl⟩
      exact Finset.image_subset_image (hwfS.bags_sub B0 hB0)
    have hcardR : ∀ B ∈ bagsR, B.card ≤ n + 15 := by
      intro B hB
      simp only [bagsR, List.mem_map] at hB
      rcases hB with ⟨B0, hB0, rfl⟩
      exact le_trans Finset.card_image_le (hwfS.bags_card B0 hB0)
    have hriR : BagsRI bagsR := by
      intro u i j k hij hjk hi hj hk hui huk
      simp only [bagsR, List.length_map] at hi hj hk
      simp only [bagsR, List.getElem_map, Finset.mem_image] at hui huk ⊢
      rcases hui with ⟨x1, hx1, hx1eq⟩
      rcases huk with ⟨x2, hx2, hx2eq⟩
      have hx : x1 = x2 := by omega
      subst hx
      exact ⟨x1, hwfS.bags_ri x1 i j k hij hjk hi hj hk hx1 hx2, hx1eq⟩
    let V1 := Finset.range M ∪ (Finset.range n).image (fun j => M + j) ∪
      (Finset.range n).image (fun j => 2 * M + j) ∪
      (Finset.range n).image (fun j => 2 * M + n + j)
    let V2 := (Finset.range M).image (· + M)
    have hinter : ∀ u, u ∈ V1 → u ∈ V2 → u ∈ (Finset.range n).image (· + M) := by
      intro u hu1 hu2
      simp only [V1, V2, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hu1 hu2 ⊢
      rcases hu2 with ⟨y, hy, rfl⟩
      rcases hu1 with ((h | ⟨j, hj, heq⟩) | ⟨j, hj, heq⟩) | ⟨j, hj, heq⟩
      · omega
      · exact ⟨j, hj, by omega⟩
      · omega
      · omega
    have hriAll : BagsRI allBags :=
      bags_append_list pref bagsR V1 V2 ((Finset.range n).image (· + M))
        hneP hneR hlastP' hheadR hsubP hsubR hinter hriP hriR
    have hallSub : ∀ B ∈ allBags, B ⊆ Finset.range N := by
      intro B hB
      rcases List.mem_append.mp hB with h1 | h2
      · intro u hu
        have := hsubP B h1 hu
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at this ⊢
        rcases this with ((h | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩ <;> omega
      · intro u hu
        have := hsubR B h2 hu
        simp only [Finset.mem_image, Finset.mem_range] at this ⊢
        rcases this with ⟨y, hy, rfl⟩; omega
    have hallCard : ∀ B ∈ allBags, B.card ≤ n + 41 := by
      intro B hB
      rcases List.mem_append.mp hB with h1 | h2
      · exact le_trans (hcardP B h1) (by omega)
      · exact le_trans (hcardR B h2) (by omega)
    have hmemBridgeB1 : ∀ j < n,
        let B1 := bridgeCur n M j ∪ {2 * M + j, 2 * M + n + j, M + j}
        B1 ∈ bridgeBags n M n := by
      have hgen : ∀ k ≤ n, ∀ j < k,
          (bridgeCur n M j ∪ {2 * M + j, 2 * M + n + j, M + j}) ∈ bridgeBags n M k := by
        intro k
        induction k with
        | zero => intro _ j hj; omega
        | succ k ih =>
          intro hk j hj
          simp only [bridgeBags, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          by_cases hjk : j = k
          · subst hjk; exact Or.inr (Or.inl rfl)
          · exact Or.inl (ih (by omega) j (by omega))
      exact hgen n (le_refl n)
    have hcovV : ∀ u < N, ∃ B ∈ allBags, u ∈ B := by
      intro u hu
      by_cases h1 : u < M
      · obtain ⟨B, hB, huB⟩ := hwfS.bags_covV u h1
        exact ⟨B, List.mem_append_left _ (List.mem_append_left _ (List.mem_reverse.mpr hB)), huB⟩
      · by_cases h2 : u < 2 * M
        · obtain ⟨B, hB, huB⟩ := hwfS.bags_covV (u - M) (by omega)
          refine ⟨B.image (· + M), List.mem_append_right _ (List.mem_map.mpr ⟨B, hB, rfl⟩), ?_⟩
          exact Finset.mem_image.mpr ⟨u - M, huB, by omega⟩
        · by_cases h3 : u < 2 * M + n
          · let j := u - 2 * M
            refine ⟨bridgeCur n M j ∪ {2 * M + j, 2 * M + n + j, M + j},
              List.mem_append_left _ (List.mem_append_right _ (hmemBridgeB1 j (by omega))), ?_⟩
            refine Finset.mem_union_right _ ?_; simp [j]; omega
          · let j := u - (2 * M + n)
            refine ⟨bridgeCur n M j ∪ {2 * M + j, 2 * M + n + j, M + j},
              List.mem_append_left _ (List.mem_append_right _ (hmemBridgeB1 j (by omega))), ?_⟩
            refine Finset.mem_union_right _ ?_; simp [j]; omega
    have hcovE : ∀ u v, v ∈ adjN u → ∃ B ∈ allBags, u ∈ B ∧ v ∈ B := by
      intro u v hv
      rcases (hadjN_iff u v).mp hv with
        ⟨_, _, h⟩ | ⟨h1, h2, h3, h4, h⟩ | ⟨j, hj, hcase⟩
      · obtain ⟨B, hB, huB, hvB⟩ := hwfS.bags_covE u v h
        exact ⟨B, List.mem_append_left _ (List.mem_append_left _ (List.mem_reverse.mpr hB)), huB, hvB⟩
      · obtain ⟨B, hB, huB, hvB⟩ := hwfS.bags_covE (u - M) (v - M) h
        refine ⟨B.image (· + M), List.mem_append_right _ (List.mem_map.mpr ⟨B, hB, rfl⟩), ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨u - M, huB, by omega⟩
        · exact Finset.mem_image.mpr ⟨v - M, hvB, by omega⟩
      · let B1 := bridgeCur n M j ∪ {2 * M + j, 2 * M + n + j, M + j}
        have hB1 : B1 ∈ allBags :=
          List.mem_append_left _ (List.mem_append_right _ (hmemBridgeB1 j hj))
        have hjB1 : j ∈ B1 :=
          Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_refl j, hj⟩))
        have huB1 : 2 * M + j ∈ B1 := Finset.mem_union_right _ (by simp)
        have hvB1 : 2 * M + n + j ∈ B1 := Finset.mem_union_right _ (by simp)
        have hmB1 : M + j ∈ B1 := Finset.mem_union_right _ (by simp)
        rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨B1, hB1, hjB1, huB1⟩
        · exact ⟨B1, hB1, huB1, hjB1⟩
        · exact ⟨B1, hB1, huB1, hvB1⟩
        · exact ⟨B1, hB1, hvB1, huB1⟩
        · exact ⟨B1, hB1, hvB1, hmB1⟩
        · exact ⟨B1, hB1, hmB1, hvB1⟩
    let bag : Fin allBags.length → Finset (Fin N) := fun t =>
      Finset.univ.filter (fun u : Fin N => u.val ∈ allBags[t.val])
    have hmem_bag : ∀ (t : Fin allBags.length) (u : Fin N), u ∈ bag t ↔ u.val ∈ allBags[t.val] := by
      intro t u; simp [bag]
    have hcard_bag : ∀ t : Fin allBags.length, (bag t).card ≤ (allBags[t.val]).card := by
      intro t
      have hinj : Function.Injective (fun u : Fin N => u.val) := fun a b h => Fin.ext h
      have hsub : (bag t).image (fun u : Fin N => u.val) ⊆ allBags[t.val] := by
        intro x hx
        simp only [Finset.mem_image] at hx
        rcases hx with ⟨u, hu, rfl⟩
        exact (hmem_bag t u).mp hu
      rw [← Finset.card_image_of_injective (bag t) hinj]
      exact Finset.card_le_card hsub
    refine ⟨allBags.length, bag, ?_, ?_, ?_, ?_⟩
    · intro t
      exact le_trans (hcard_bag t) (hallCard _ (List.getElem_mem t.isLt))
    · intro u
      obtain ⟨B, hB, huB⟩ := hcovV u.val u.isLt
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hB
      exact ⟨⟨i, hi⟩, (hmem_bag ⟨i, hi⟩ u).mpr huB⟩
    · intro u v hv
      obtain ⟨B, hB, huB, hvB⟩ := hcovE u.val v.val ((hmemG u v).mp hv)
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hB
      exact ⟨⟨i, hi⟩, (hmem_bag ⟨i, hi⟩ u).mpr huB, (hmem_bag ⟨i, hi⟩ v).mpr hvB⟩
    · intro v s t u hst htu hvs hvu
      rw [hmem_bag] at hvs hvu ⊢
      exact hriAll v.val s.val t.val u.val hst htu s.isLt t.isLt u.isLt hvs hvu
  · -- Communication lower bound: 2^n ≤ k
    intro k send recv hcorr
    have hinj : Function.Injective send := by
      intro f1 f2 hsend
      ext y
      let gy : Table n := fun z => decide (z = y)
      have h1 : decide (((Finset.univ : Finset (Word n)).filter (fun z => f1 z && gy z)).card % 2 = 1) = f1 y := by
        cases hfy : f1 y
        · have hempty : ((Finset.univ : Finset (Word n)).filter (fun z => f1 z && gy z)) = ∅ := by
            ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, Bool.and_eq_true, gy, decide_eq_true_eq]
            rintro ⟨h, rfl⟩; rw [hfy] at h; exact Bool.noConfusion h
          rw [hempty]; simp
        · have hsing : ((Finset.univ : Finset (Word n)).filter (fun z => f1 z && gy z)) = {y} := by
            ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
              Bool.and_eq_true, gy, decide_eq_true_eq]
            constructor
            · rintro ⟨_, rfl⟩; rfl
            · rintro rfl; exact ⟨hfy, rfl⟩
          rw [hsing]; simp
      have h2 : decide (((Finset.univ : Finset (Word n)).filter (fun z => f2 z && gy z)).card % 2 = 1) = f2 y := by
        cases hfy : f2 y
        · have hempty : ((Finset.univ : Finset (Word n)).filter (fun z => f2 z && gy z)) = ∅ := by
            ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, Bool.and_eq_true, gy, decide_eq_true_eq]
            rintro ⟨h, rfl⟩; rw [hfy] at h; exact Bool.noConfusion h
          rw [hempty]; simp
        · have hsing : ((Finset.univ : Finset (Word n)).filter (fun z => f2 z && gy z)) = {y} := by
            ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
              Bool.and_eq_true, gy, decide_eq_true_eq]
            constructor
            · rintro ⟨_, rfl⟩; rfl
            · rintro rfl; exact ⟨hfy, rfl⟩
          rw [hsing]; simp
      have eq1 : recv (send f1) gy = f1 y := by
        rw [hcorr f1 gy]; dsimp only; rw [hresult f1 gy, h1]
      have eq2 : recv (send f2) gy = f2 y := by
        rw [hcorr f2 gy]; dsimp only; rw [hresult f2 gy, h2]
      rw [← eq1, hsend, eq2]
    have hcard : Fintype.card (Table n) ≤ Fintype.card (Fin k → Bool) :=
      Fintype.card_le_of_injective send hinj
    simp only [Table, Word, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

/-! ### Part 6: Main theorem matching the exact target statement -/

lemma decide_eq_any {P Q : Prop} {d1 : Decidable P} {d2 : Decidable Q} (h : P ↔ Q) :
    @decide P d1 = @decide Q d2 := by
  have hpq : P = Q := propext h
  subst hpq
  exact congrArg (@decide P) (Subsingleton.elim d1 d2)

lemma card_filter_eq_any {α : Type*} (s : Finset α) (p q : α → Prop)
    {dp : DecidablePred p} {dq : DecidablePred q} (h : ∀ x, p x ↔ q x) :
    (@Finset.filter α p dp s).card = (@Finset.filter α q dq s).card := by
  have hpq : p = q := funext fun x => propext (h x)
  subst hpq
  exact congrArg (fun d => (@Finset.filter α p d s).card) (Subsingleton.elim dp dq)

lemma oddCount_eq_isCountFin {N : Nat} (G : Fin N → Finset (Fin N)) (live1 live2 : Fin N → Bool)
    (hlive : ∀ i, live1 i = live2 i)
    {dp1 : DecidablePred (fun I : Finset (Fin N) => (∀ u ∈ I, live1 u = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)}
    {d1 : Decidable ((@Finset.filter (Finset (Fin N))
      (fun I => (∀ u ∈ I, live1 u = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I) dp1 Finset.univ).card % 2 = 1)} :
    @decide ((@Finset.filter (Finset (Fin N))
      (fun I => (∀ u ∈ I, live1 u = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I) dp1 Finset.univ).card % 2 = 1) d1 =
    decide (isCountFin G live2 % 2 = 1) := by
  have hl : live1 = live2 := funext hlive
  subst hl
  dsimp only [isCountFin]
  exact decide_eq_any (iff_of_eq (congrArg (fun x => x % 2 = 1)
    (card_filter_eq_any Finset.univ _ _ (fun _ => Iff.rfl))))


/-! ### Part 7: Lindsey discrepancy bound for inner product mod 2 -/

lemma cauchy_schwarz_int {ι : Type*} (s : Finset ι) (a : ι → ℤ) :
    (∑ x ∈ s, a x) ^ 2 ≤ (s.card : ℤ) * ∑ x ∈ s, (a x) ^ 2 := by
  have h0 : (0 : ℤ) ≤ ∑ x ∈ s, ∑ y ∈ s, (a x - a y) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  have hexp : ∑ x ∈ s, ∑ y ∈ s, (a x - a y) ^ 2 =
      2 * (s.card : ℤ) * (∑ x ∈ s, (a x) ^ 2) - 2 * (∑ x ∈ s, a x) ^ 2 := by
    have h1 : ∀ x y : ι, (a x - a y) ^ 2 = a x ^ 2 + a y ^ 2 - (2 * a x) * a y := fun x y => by ring
    simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have t1 : ∑ x ∈ s, ∑ _y ∈ s, a x ^ 2 = (s.card : ℤ) * ∑ x ∈ s, a x ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    have t2 : ∑ _x ∈ s, ∑ y ∈ s, a y ^ 2 = (s.card : ℤ) * ∑ y ∈ s, a y ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have t3 : ∑ x ∈ s, ∑ y ∈ s, (2 * a x) * a y = 2 * (∑ x ∈ s, a x) ^ 2 := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    rw [t1, t2, t3]
    ring
  linarith

def sgnBool (b : Bool) : ℤ := if b then -1 else 1

lemma sgnBool_mul_self (b : Bool) : sgnBool b * sgnBool b = 1 := by
  cases b <;> rfl

lemma sgnBool_eq_iff (b c : Bool) :
    sgnBool b * sgnBool c = if b = c then 1 else -1 := by
  cases b <;> cases c <;> rfl

def ipBool {n : Nat} (f g : Table n) : Bool :=
  decide (((Finset.univ : Finset (Word n)).filter (fun y => f y && g y)).card % 2 = 1)

lemma neg_one_pow_eq_sgnBool (k : Nat) :
    (-1 : ℤ) ^ k = sgnBool (decide (k % 2 = 1)) := by
  rcases Nat.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · subst hr
    have h1 : (r + r) % 2 = 0 := by omega
    rw [h1]
    simp [sgnBool, ← two_mul, pow_mul]
  · subst hr
    have h1 : (2 * r + 1) % 2 = 1 := by omega
    rw [h1]
    simp [sgnBool, pow_succ, pow_mul]

lemma sgnBool_ipBool {n : Nat} (f g : Table n) :
    sgnBool (ipBool f g) = ∏ y : Word n, (if f y && g y then (-1 : ℤ) else 1) := by
  dsimp only [ipBool]
  rw [← neg_one_pow_eq_sgnBool]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

lemma ipMat_orth {n : Nat} (g1 g2 : Table n) :
    ∑ f : Table n, sgnBool (ipBool f g1) * sgnBool (ipBool f g2) =
      if g1 = g2 then ((2 ^ (2 ^ n) : Nat) : ℤ) else 0 := by
  have hterm : ∀ f : Table n,
      sgnBool (ipBool f g1) * sgnBool (ipBool f g2) =
        ∏ y : Word n, (if f y && (g1 y != g2 y) then (-1 : ℤ) else 1) := by
    intro f
    rw [sgnBool_ipBool, sgnBool_ipBool, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun y _ => ?_
    cases f y <;> cases g1 y <;> cases g2 y <;> rfl
  simp_rw [hterm]
  have hps : ∑ f : Word n → Bool, ∏ y : Word n, (if f y && (g1 y != g2 y) then (-1 : ℤ) else 1) =
      ∏ y : Word n, ∑ b : Bool, (if b && (g1 y != g2 y) then (-1 : ℤ) else 1) := by
    symm
    exact Fintype.prod_sum (fun y b => if b && (g1 y != g2 y) then (-1 : ℤ) else 1)
  rw [hps]
  by_cases heq : g1 = g2
  · subst heq
    rw [if_pos rfl]
    have h2 : ∀ y : Word n,
        ∑ b : Bool, (if b && (g1 y != g1 y) then (-1 : ℤ) else 1) = (2 : ℤ) := by
      intro y; cases g1 y <;> decide
    simp_rw [h2]
    rw [Finset.prod_const, Finset.card_univ]
    have hcw : Fintype.card (Word n) = 2 ^ n := by
      simp [Word]
    rw [hcw]
    push_cast
    rfl
  · rw [if_neg heq]
    have hne : ∃ y : Word n, g1 y ≠ g2 y := by
      by_contra hall
      push_neg at hall
      exact heq (funext hall)
    obtain ⟨y0, hy0⟩ := hne
    refine Finset.prod_eq_zero (Finset.mem_univ y0) ?_
    cases h1 : g1 y0 <;> cases h2 : g2 y0 <;> simp_all

lemma lindsey_bound (n K : Nat) (rows cols : Fin K → Finset (Table n))
    (guess : Fin K → Table n → Bool)
    (hpart : ∀ f g : Table n, ∃! i, f ∈ rows i ∧ g ∈ cols i) :
    let D := 2 ^ (2 ^ n)
    let correct := ((Finset.univ : Finset (Table n × Table n)).filter (fun p =>
      ∃ i, p.1 ∈ rows i ∧ p.2 ∈ cols i ∧ guess i p.2 = ipBool p.1 p.2)).card
    (2 * correct - D ^ 2) ^ 2 ≤ K * D ^ 3 := by
  intro D correct
  by_cases hle : 2 * correct ≤ D ^ 2
  · have hz : 2 * correct - D ^ 2 = 0 := Nat.sub_eq_zero_of_le hle
    rw [hz]; simp
  · push_neg at hle
    have hD_card : Fintype.card (Table n) = D := by
      simp [D, Table, Word]
    have hD2_card : Fintype.card (Table n × Table n) = D ^ 2 := by
      rw [Fintype.card_prod, hD_card, sq]
    let S : Fin K → ℤ := fun i =>
      ∑ f ∈ rows i, ∑ g ∈ cols i, sgnBool (guess i g) * sgnBool (ipBool f g)
    have hsum_S : 2 * (correct : ℤ) - (D : ℤ) ^ 2 = ∑ i : Fin K, S i := by
      have hpair : ∀ p : Table n × Table n,
          (if ∃ i, p.1 ∈ rows i ∧ p.2 ∈ cols i ∧ guess i p.2 = ipBool p.1 p.2
            then (1 : ℤ) else -1) =
          ∑ i : Fin K, (if p.1 ∈ rows i ∧ p.2 ∈ cols i
            then sgnBool (guess i p.2) * sgnBool (ipBool p.1 p.2) else 0) := by
        intro ⟨f, g⟩
        obtain ⟨i0, ⟨hfr, hgc⟩, huniq⟩ := hpart f g
        rw [Finset.sum_eq_single i0]
        · dsimp only []
          have hrhs : (if f ∈ rows i0 ∧ g ∈ cols i0
              then sgnBool (guess i0 g) * sgnBool (ipBool f g) else 0) =
              if guess i0 g = ipBool f g then (1 : ℤ) else -1 := by
            rw [if_pos ⟨hfr, hgc⟩, sgnBool_eq_iff]
          rw [hrhs]
          by_cases hge : guess i0 g = ipBool f g
          · rw [if_pos ⟨i0, hfr, hgc, hge⟩, if_pos hge]
          · have hne : ¬ ∃ i, f ∈ rows i ∧ g ∈ cols i ∧ guess i g = ipBool f g := by
              rintro ⟨j, hjr, hjc, hje⟩
              have hj : j = i0 := huniq j ⟨hjr, hjc⟩
              subst hj; exact hge hje
            rw [if_neg hne, if_neg hge]
        · intro j _ hjne
          rw [if_neg]
          rintro ⟨hjr, hjc⟩
          exact hjne (huniq j ⟨hjr, hjc⟩)
        · intro hmem; exact absurd (Finset.mem_univ i0) hmem
      have hsum_lhs : ∑ p : Table n × Table n,
          (if ∃ i, p.1 ∈ rows i ∧ p.2 ∈ cols i ∧ guess i p.2 = ipBool p.1 p.2
            then (1 : ℤ) else -1) = 2 * (correct : ℤ) - (D : ℤ) ^ 2 := by
        have hrew : ∀ p : Table n × Table n,
            (if ∃ i, p.1 ∈ rows i ∧ p.2 ∈ cols i ∧ guess i p.2 = ipBool p.1 p.2
              then (1 : ℤ) else -1) =
            2 * (if ∃ i, p.1 ∈ rows i ∧ p.2 ∈ cols i ∧ guess i p.2 = ipBool p.1 p.2
              then (1 : ℤ) else 0) - 1 := by
          intro p; split_ifs <;> ring
        simp_rw [hrew, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hD2_card]
        push_cast
        rfl
      have hsum_rhs : ∑ p : Table n × Table n, ∑ i : Fin K,
          (if p.1 ∈ rows i ∧ p.2 ∈ cols i
            then sgnBool (guess i p.2) * sgnBool (ipBool p.1 p.2) else 0) =
          ∑ i : Fin K, S i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [S]
        rw [Fintype.sum_prod_type]
        calc ∑ f : Table n, ∑ g : Table n,
              (if f ∈ rows i ∧ g ∈ cols i
                then sgnBool (guess i g) * sgnBool (ipBool f g) else 0)
            = ∑ f : Table n, if f ∈ rows i then
                ∑ g : Table n, if g ∈ cols i
                  then sgnBool (guess i g) * sgnBool (ipBool f g) else 0
              else 0 := by
              refine Finset.sum_congr rfl fun f _ => ?_
              by_cases hf : f ∈ rows i
              · simp [hf]
              · simp [hf]
          _ = ∑ f ∈ rows i, ∑ g ∈ cols i, sgnBool (guess i g) * sgnBool (ipBool f g) := by
              rw [← Finset.sum_subset (Finset.subset_univ (rows i))]
              · refine Finset.sum_congr rfl fun f hf => ?_
                rw [if_pos hf]
                rw [← Finset.sum_subset (Finset.subset_univ (cols i))]
                · refine Finset.sum_congr rfl fun g hg => if_pos hg
                · intro g _ hg; exact if_neg hg
              · intro f _ hf; exact if_neg hf
      rw [← hsum_lhs, ← hsum_rhs]
      exact Finset.sum_congr rfl fun p _ => hpair p
    have hrect : ∀ i : Fin K, (S i) ^ 2 ≤ (D : ℤ) * (((rows i).card : ℤ) * ((cols i).card : ℤ)) := by
      intro i
      let v : Table n → ℤ := fun f => ∑ g ∈ cols i, sgnBool (guess i g) * sgnBool (ipBool f g)
      have hcs1 : (S i) ^ 2 ≤ ((rows i).card : ℤ) * ∑ f ∈ rows i, (v f) ^ 2 :=
        cauchy_schwarz_int (rows i) v
      have hsub : ∑ f ∈ rows i, (v f) ^ 2 ≤ ∑ f : Table n, (v f) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (rows i))
          fun _ _ _ => sq_nonneg _
      have hnorm : ∑ f : Table n, (v f) ^ 2 = (D : ℤ) * ((cols i).card : ℤ) := by
        have hsq : ∀ f, (v f) ^ 2 =
            ∑ g1 ∈ cols i, ∑ g2 ∈ cols i,
              (sgnBool (guess i g1) * sgnBool (guess i g2)) *
                (sgnBool (ipBool f g1) * sgnBool (ipBool f g2)) := by
          intro f
          dsimp only [v]
          rw [sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun g1 _ => Finset.sum_congr rfl fun g2 _ => by ring
        simp_rw [hsq]
        rw [Finset.sum_comm]
        have hswap : ∀ g1 ∈ cols i,
            ∑ f : Table n, ∑ g2 ∈ cols i,
              (sgnBool (guess i g1) * sgnBool (guess i g2)) *
                (sgnBool (ipBool f g1) * sgnBool (ipBool f g2)) =
            ∑ g2 ∈ cols i, (sgnBool (guess i g1) * sgnBool (guess i g2)) *
              (∑ f : Table n, sgnBool (ipBool f g1) * sgnBool (ipBool f g2)) := by
          intro g1 _
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun g2 _ => by rw [← Finset.mul_sum]
        rw [Finset.sum_congr rfl hswap]
        have hdiag : ∀ g1 ∈ cols i,
            ∑ g2 ∈ cols i, (sgnBool (guess i g1) * sgnBool (guess i g2)) *
              (∑ f : Table n, sgnBool (ipBool f g1) * sgnBool (ipBool f g2)) = (D : ℤ) := by
          intro g1 hg1
          rw [Finset.sum_eq_single g1]
          · rw [ipMat_orth, if_pos rfl, sgnBool_mul_self, one_mul]
          · intro g2 _ hne
            rw [ipMat_orth, if_neg (Ne.symm hne), mul_zero]
          · intro hnot; exact absurd hg1 hnot
        rw [Finset.sum_congr rfl hdiag, Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hmul : ((rows i).card : ℤ) * ∑ f ∈ rows i, (v f) ^ 2 ≤
          ((rows i).card : ℤ) * ((D : ℤ) * ((cols i).card : ℤ)) := by
        rw [← hnorm]
        exact mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)
      linarith
    have harea : ∑ i : Fin K, ((rows i).card : ℤ) * ((cols i).card : ℤ) = (D : ℤ) ^ 2 := by
      have h1 : ∀ i : Fin K, ((rows i).card : ℤ) * ((cols i).card : ℤ) =
          ∑ p : Table n × Table n, (if p.1 ∈ rows i ∧ p.2 ∈ cols i then (1 : ℤ) else 0) := by
        intro i
        rw [Fintype.sum_prod_type]
        have hinner : ∀ f : Table n,
            ∑ g : Table n, (if f ∈ rows i ∧ g ∈ cols i then (1 : ℤ) else 0) =
              if f ∈ rows i then ((cols i).card : ℤ) else 0 := by
          intro f
          by_cases hf : f ∈ rows i
          · simp [hf]
          · simp [hf]
        simp_rw [hinner]
        rw [← Finset.sum_subset (Finset.subset_univ (rows i))]
        · rw [Finset.sum_congr rfl fun f hf => if_pos hf, Finset.sum_const, nsmul_eq_mul]
        · intro f _ hf; exact if_neg hf
      simp_rw [h1]
      rw [Finset.sum_comm]
      have hone : ∀ p : Table n × Table n,
          ∑ i : Fin K, (if p.1 ∈ rows i ∧ p.2 ∈ cols i then (1 : ℤ) else 0) = 1 := by
        intro ⟨f, g⟩
        obtain ⟨i0, ⟨hfr, hgc⟩, huniq⟩ := hpart f g
        rw [Finset.sum_eq_single i0]
        · exact if_pos ⟨hfr, hgc⟩
        · intro j _ hjne
          exact if_neg fun ⟨hjr, hjc⟩ => hjne (huniq j ⟨hjr, hjc⟩)
        · intro hnot; exact absurd (Finset.mem_univ i0) hnot
      simp_rw [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hD2_card]
      push_cast
      rfl
    have hcsK : (∑ i : Fin K, S i) ^ 2 ≤ (K : ℤ) * ∑ i : Fin K, (S i) ^ 2 := by
      simpa using cauchy_schwarz_int (Finset.univ : Finset (Fin K)) S
    have hsum_bound : ∑ i : Fin K, (S i) ^ 2 ≤ (D : ℤ) ^ 3 := by
      calc ∑ i : Fin K, (S i) ^ 2
          ≤ ∑ i : Fin K, (D : ℤ) * (((rows i).card : ℤ) * ((cols i).card : ℤ)) :=
            Finset.sum_le_sum fun i _ => hrect i
        _ = (D : ℤ) * ∑ i : Fin K, ((rows i).card : ℤ) * ((cols i).card : ℤ) := by
            rw [← Finset.mul_sum]
        _ = (D : ℤ) * (D : ℤ) ^ 2 := by rw [harea]
        _ = (D : ℤ) ^ 3 := by ring
    have hfinal : (2 * (correct : ℤ) - (D : ℤ) ^ 2) ^ 2 ≤ (K : ℤ) * (D : ℤ) ^ 3 := by
      rw [hsum_S]
      exact le_trans hcsK (mul_le_mul_of_nonneg_left hsum_bound (Nat.cast_nonneg K))
    by_cases hge : D ^ 2 ≤ 2 * correct
    · have hcast : ((2 * correct - D ^ 2 : Nat) : ℤ) = 2 * (correct : ℤ) - (D : ℤ) ^ 2 := by
        rw [Nat.cast_sub hge]
        push_cast
        rfl
      have hnat_int : (((2 * correct - D ^ 2) ^ 2 : Nat) : ℤ) ≤ ((K * D ^ 3 : Nat) : ℤ) := by
        rw [Nat.cast_pow, hcast, Nat.cast_mul, Nat.cast_pow]
        exact hfinal
      exact Nat.cast_le.mp hnat_int
    · have hzero : 2 * correct - D ^ 2 = 0 := Nat.sub_eq_zero_of_le (by omega)
      rw [hzero]
      exact Nat.zero_le _

lemma lindsey_bound_any (n K : Nat) (rows cols : Fin K → Finset (Table n))
    (guess : Fin K → Table n → Bool)
    (hpart : ∀ f g : Table n, ∃! i, f ∈ rows i ∧ g ∈ cols i)
    (c : Nat)
    (hc : c = ((Finset.univ : Finset (Table n × Table n)).filter (fun p =>
      ∃ i, p.1 ∈ rows i ∧ p.2 ∈ cols i ∧ guess i p.2 = ipBool p.1 p.2)).card) :
    (2 * c - (2 ^ (2 ^ n)) ^ 2) ^ 2 ≤ K * (2 ^ (2 ^ n)) ^ 3 := by
  subst hc
  exact lindsey_bound n K rows cols guess hpart

lemma card_filter_univ_eq {α : Type*} {ft1 ft2 : Fintype α} (p q : α → Prop)
    {dp : DecidablePred p} {dq : DecidablePred q} (h : ∀ x, p x ↔ q x) :
    (@Finset.filter α p dp (@Finset.univ α ft1)).card =
    (@Finset.filter α q dq (@Finset.univ α ft2)).card := by
  have hf : ft1 = ft2 := Subsingleton.elim ft1 ft2
  subst hf
  have hpq : p = q := funext fun x => propext (h x)
  subst hpq
  exact congrArg (fun d => (@Finset.filter α p d (@Finset.univ α ft1)).card) (Subsingleton.elim dp dq)

lemma decide_card_filter_eq {α : Type*} {ft1 ft2 : Fintype α} (p : α → Prop)
    {dp1 dp2 : DecidablePred p}
    {d1 : Decidable ((@Finset.filter α p dp1 (@Finset.univ α ft1)).card % 2 = 1)}
    {d2 : Decidable ((@Finset.filter α p dp2 (@Finset.univ α ft2)).card % 2 = 1)} :
    @decide ((@Finset.filter α p dp1 (@Finset.univ α ft1)).card % 2 = 1) d1 =
    @decide ((@Finset.filter α p dp2 (@Finset.univ α ft2)).card % 2 = 1) d2 := by
  have hf : ft1 = ft2 := Subsingleton.elim ft1 ft2
  subst hf
  have h : dp1 = dp2 := Subsingleton.elim dp1 dp2
  subst h
  exact congrArg (@decide _) (Subsingleton.elim d1 d2)

lemma main :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ n : Nat,
      let Word := Fin n → Bool
      let Table := Word → Bool
      let D := 2^(2^n)
      ∃ (N : Nat) (H : Fin N → Finset (Fin N)) (shore side : Fin N → Bool)
        (tag : Fin N → Option (Word × Bool)) (readBit : Nat → Bool),
        N ≤ 26*(15000*(n+1)*2^n+1)^2 ∧
        (∀ u, u ∉ H u ∧ (H u).card ≤ 3) ∧ (∀ u v, v ∈ H u ↔ u ∈ H v) ∧
        (∀ u, ∀ v ∈ H u, shore v ≠ shore u) ∧
        (∀ u, ((H u).filter (fun v => side v ≠ side u)).card ≤ 1) ∧
        ((Finset.univ : Finset (Fin N)).filter (fun u =>
          side u = false ∧ ∃ v ∈ H u, side v = true)).card ≤ n ∧
        (∃ (l : Nat) (bag : Fin l → Finset (Fin N)),
          (∀ t, (bag t).card ≤ n+43) ∧ (∀ v, ∃ t, v ∈ bag t) ∧
          (∀ u v, v ∈ H u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
          ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t) ∧
        let total := fun (f g : Table) =>
          let on := fun i => (tag i).elim true (fun p => decide ((if side i then g else f) p.1 = p.2))
          ((Finset.univ : Finset (Finset (Fin N))).filter
            (fun I => (∀ v ∈ I, on v = true) ∧ ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)).card
        (∀ f g, readBit (total f g) = decide (((Finset.univ : Finset Word).filter
          (fun y => f y && g y)).card % 2 = 1)) ∧
        ∀ (K : Nat) (rows cols : Fin K → Finset Table) (guess : Fin K → Table → Bool),
          (∀ f g : Table, ∃! i, f ∈ rows i ∧ g ∈ cols i) →
          let correct := ((Finset.univ : Finset (Table × Table)).filter (fun p =>
            ∃ i, p.1 ∈ rows i ∧ p.2 ∈ cols i ∧ guess i p.2 = readBit (total p.1 p.2))).card
          (2*correct - D^2)^2 ≤ K*D^3 := by
  intro n
  obtain ⟨N, H, shore, side, tag, hN, hdeg, hsym, hbip, hcm, hcs, ⟨l, bag, hcard, hcov, hedge, hconn⟩, hres, _hlb⟩ :=
    sharpness_part n
  refine ⟨N, H, shore, side, tag, fun t => decide (t % 2 = 1), ?_, hdeg, hsym, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hpos : 1 ≤ (n + 1) * 2 ^ n := Nat.mul_pos (Nat.succ_pos n) (Nat.two_pow_pos n)
    nlinarith
  · intro u v hv; exact Ne.symm (hbip u v hv)
  · intro u; convert hcm u using 2; ext v; simp
  · convert hcs using 2; ext u; simp
  · exact ⟨l, bag, fun t => le_trans (hcard t) (by omega), hcov, hedge, hconn⟩
  · intro f g
    refine Eq.trans (oddCount_eq_isCountFin H _ _ ?_) (Eq.trans (hres f g) ?_)
    · intro i
      cases tag i with
      | none => rfl
      | some p =>
        dsimp only [Option.elim_some]
        by_cases hs : side i = true
        · simp only [hs, ↓reduceIte] <;> exact decide_eq_any Iff.rfl
        · simp only [hs, Bool.false_eq_true, ↓reduceIte] <;> exact decide_eq_any Iff.rfl
    · exact decide_card_filter_eq (fun y : Word n => (f y && g y) = true)
  · intro K rows cols guess hpart
    dsimp only []
    refine lindsey_bound_any n K rows cols guess hpart _ ?_
    refine card_filter_univ_eq _ _ (fun p =>
      exists_congr fun i => and_congr_right fun _ => and_congr_right fun _ =>
        iff_of_eq (congrArg (Eq (guess i p.2)) ?_))
    refine Eq.trans (oddCount_eq_isCountFin H _ _ ?_) (hres p.1 p.2)
    intro j
    cases tag j with
    | none => rfl
    | some q =>
      dsimp only [Option.elim_some]
      by_cases hs : side j = true
      · simp only [hs, ↓reduceIte] <;> exact decide_eq_any Iff.rfl
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] <;> exact decide_eq_any Iff.rfl

end PEqualNP.Outside.L_lib_1223_aux

theorem PEqualNP.Outside.L_lib_1223 : letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ n : Nat,
  let Word := Fin n → Bool
  let Table := Word → Bool
  let D := 2^(2^n)
  ∃ (N : Nat) (H : Fin N → Finset (Fin N)) (shore side : Fin N → Bool)
    (tag : Fin N → Option (Word × Bool)) (readBit : Nat → Bool),
    N ≤ 26*(15000*(n+1)*2^n+1)^2 ∧
    (∀ u, u ∉ H u ∧ (H u).card ≤ 3) ∧ (∀ u v, v ∈ H u ↔ u ∈ H v) ∧
    (∀ u, ∀ v ∈ H u, shore v ≠ shore u) ∧
    (∀ u, ((H u).filter (fun v => side v ≠ side u)).card ≤ 1) ∧
    ((Finset.univ : Finset (Fin N)).filter (fun u =>
      side u = false ∧ ∃ v ∈ H u, side v = true)).card ≤ n ∧
    (∃ (l : Nat) (bag : Fin l → Finset (Fin N)),
      (∀ t, (bag t).card ≤ n+43) ∧ (∀ v, ∃ t, v ∈ bag t) ∧
      (∀ u v, v ∈ H u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
      ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t) ∧
    let total := fun (f g : Table) =>
      let on := fun i => (tag i).elim true (fun p => decide ((if side i then g else f) p.1 = p.2))
      ((Finset.univ : Finset (Finset (Fin N))).filter
        (fun I => (∀ v ∈ I, on v = true) ∧ ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)).card
    (∀ f g, readBit (total f g) = decide (((Finset.univ : Finset Word).filter
      (fun y => f y && g y)).card % 2 = 1)) ∧
    ∀ (K : Nat) (rows cols : Fin K → Finset Table) (guess : Fin K → Table → Bool),
      (∀ f g : Table, ∃! i, f ∈ rows i ∧ g ∈ cols i) →
      let correct := ((Finset.univ : Finset (Table × Table)).filter (fun p =>
        ∃ i, p.1 ∈ rows i ∧ p.2 ∈ cols i ∧ guess i p.2 = readBit (total p.1 p.2))).card
      (2*correct - D^2)^2 ≤ K*D^3 :=
  PEqualNP.Outside.L_lib_1223_aux.main
