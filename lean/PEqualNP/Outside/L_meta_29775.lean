import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29775

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

end PEqualNP.Outside.L_meta_29775

namespace PEqualNP.Outside.L_meta_29775

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

def trim (g : Gate) : Gate :=
  ⟨g.op, match g.op with | .not => g.inputs.take 1 | _ => g.inputs⟩

lemma trim_eval (g : Gate) (w : List Bool) :
    (trim g).op.eval ((trim g).inputs.map fun i => w.getD i false) =
    g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  cases op <;> cases ins <;> rfl

lemma trim_wires (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map trim) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change wiresFrom (gs.map trim)
      (w ++ [(trim g).op.eval ((trim g).inputs.map fun i => w.getD i false)]) = _
    rw [trim_eval]
    exact ih _

lemma cnt_step_cost (t : ℕ) (L : List (Finset (Fin n))) (g : Gate)
    (h : Cnt t L) : Cnt (t + (g.inputs.length-1)) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤
        (W.card-1) + g.inputs.length := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (List.toFinset_card_le _) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

def cost (gs : List Gate) : ℕ := (gs.map fun g => g.inputs.length-1).sum

lemma cnt_cost (gs : List Gate) (t : ℕ) (L : List (Finset (Fin n)))
    (h : Cnt t L) : Cnt (t+cost gs) (suppsFrom gs L) := by
  induction gs generalizing t L with
  | nil => simpa [cost, suppsFrom] using h
  | cons g gs ih =>
    have hh := ih (t+(g.inputs.length-1)) (L ++ [gateSupp L g]) (cnt_step_cost t L g h)
    simpa [cost, suppsFrom, List.foldl_cons, Nat.add_assoc] using hh

lemma support_agree (C : Circuit) (x y : Fin n → Bool)
    (h : ∀ i ∈ (suppsFrom C.gates (inputSupps n)).getD C.output ∅, x i = y i) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) :=
  (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 C.output h

lemma profile_support {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Fin n → Fin m → Bool) (hrow : Function.Injective A)
    (hcol : Function.Injective (fun j i => A i j)) (C : Circuit)
    (hrep : PEqualNP.Represents.Represents A C) :
    n+m-2 ≤ ((suppsFrom C.gates (inputSupps (n+m))).getD C.output ∅).card := by
  classical
  let S := (suppsFrom C.gates (inputSupps (n+m))).getD C.output ∅
  let x := fun (u : Fin n) (v : Fin m) =>
    Fin.append (fun i : Fin n => decide (i=u)) (fun j : Fin m => decide (j=v))
  have hx : ∀ u v, List.ofFn (x u v) = PEqualNP.Represents.oneEach u v := by
    intro u v
    exact List.ofFn_fin_append _ _
  have hr : ∀ u v : Fin n, u.castAdd m ∉ S → v.castAdd m ∉ S → u = v := by
    intro u v hu hv
    apply hrow
    funext j
    rw [← hrep u j, ← hrep v j, ← hx u j, ← hx v j]
    apply support_agree
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · intro hi
      have hau : a ≠ u := by intro he; subst a; exact hu hi
      have hav : a ≠ v := by intro he; subst a; exact hv hi
      simp [x, hau, hav]
    · intro _; simp [x]
  have hc : ∀ u v : Fin m, u.natAdd n ∉ S → v.natAdd n ∉ S → u = v := by
    intro u v hu hv
    apply hcol
    funext j
    change A j u = A j v
    rw [← hrep j u, ← hrep j v, ← hx j u, ← hx j v]
    apply support_agree
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · intro _; simp [x]
    · intro hi
      have hbu : b ≠ u := by intro he; subst b; exact hu hi
      have hbv : b ≠ v := by intro he; subst b; exact hv hi
      simp [x, hbu, hbv]
  have rows : ∃ r : Fin n, ∀ i, i ≠ r → i.castAdd m ∈ S := by
    by_cases hh : ∃ r : Fin n, r.castAdd m ∉ S
    · obtain ⟨r, hr0⟩ := hh
      exact ⟨r, fun i hir => by by_contra hi; exact hir (hr i r hi hr0)⟩
    · exact ⟨⟨0, hn⟩, fun i _ => by by_contra hi; exact hh ⟨i,hi⟩⟩
  have cols : ∃ c : Fin m, ∀ j, j ≠ c → j.natAdd n ∈ S := by
    by_cases hh : ∃ c : Fin m, c.natAdd n ∉ S
    · obtain ⟨c, hc0⟩ := hh
      exact ⟨c, fun j hjc => by by_contra hj; exact hjc (hc j c hj hc0)⟩
    · exact ⟨⟨0, hm⟩, fun j _ => by by_contra hj; exact hh ⟨j,hj⟩⟩
  obtain ⟨r, hR⟩ := rows
  obtain ⟨c, hC⟩ := cols
  have hne : r.castAdd m ≠ c.natAdd n := by
    intro he
    have hval := congrArg Fin.val he
    simp at hval
    omega
  have hS : ∀ i : Fin (n+m), i ≠ r.castAdd m → i ≠ c.natAdd n → i ∈ S := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · intro ha _
      exact hR a (fun he => ha (by rw [he]))
    · intro _ hb
      exact hC b (fun he => hb (by rw [he]))
  have hsubset : ((Finset.univ.erase (r.castAdd m)).erase (c.natAdd n)) ⊆ S := by
    intro i hi
    exact hS i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1 (Finset.mem_erase.mp hi).1
  have hcard : ((Finset.univ.erase (r.castAdd m)).erase (c.natAdd n)).card = n+m-2 := by
    rw [Finset.card_erase_of_mem (by simp [hne.symm]), Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
    omega
  rw [← hcard]
  exact Finset.card_le_card hsubset

def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false

def notNum : List Gate → ℕ
  | [] => 0
  | g :: gs => (if isNot g then 1 else 0)+notNum gs

lemma isNot_iff (g : Gate) : isNot g = true ↔ g.op = .not := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [isNot]

lemma cost_not_bound (gs : List Gate)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    cost (gs.map trim)+notNum gs ≤ gs.length := by
  induction gs with
  | nil => simp [cost, notNum]
  | cons g gs ih =>
    have htail := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    have hg := h g List.mem_cons_self
    have hc : (trim g).inputs.length-1+(if isNot g then 1 else 0) ≤ 1 := by
      rcases g with ⟨op, ins⟩
      cases op <;> simp [trim, isNot] at hg ⊢ <;> omega
    change (trim g).inputs.length-1+cost (gs.map trim) +
      ((if isNot g then 1 else 0)+notNum gs) ≤ gs.length+1
    omega

lemma notNum_pos {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : 1 ≤ notNum gs := by
  induction gs with
  | nil => simpa using h
  | cons g gs ih =>
    obtain ⟨a, ha, hop⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [notNum, (isNot_iff a).mpr hop]
    · have hh := ih ⟨a,ha,hop⟩
      simp only [notNum]
      omega

lemma notNum_eq_card (gs : List Gate) :
    notNum gs = (Finset.univ.filter (fun i : Fin gs.length => isNot (gs.get i))).card := by
  have hh : notNum gs = ∑ i : Fin gs.length, (if isNot (gs.get i) then 1 else 0) := by
    induction gs with
    | nil => simp [notNum]
    | cons g gs ih =>
      change notNum (g :: gs) = ∑ i : Fin (gs.length+1), (if isNot ((g :: gs).get i) then 1 else 0)
      rw [Fin.sum_univ_succ]
      simp only [notNum, List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
        List.getElem_cons_zero, List.getElem_cons_succ]
      exact congrArg (fun a => (if isNot g then 1 else 0)+a) ih
  rw [hh, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma unique_not {gs : List Gate} (h : notNum gs = 1) :
    ∃ t : Fin gs.length, ∀ k : Fin gs.length, (gs.get k).op = .not ↔ k = t := by
  classical
  rw [notNum_eq_card] at h
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h
  refine ⟨t, fun k => ?_⟩
  have hh : k ∈ Finset.univ.filter (fun i : Fin gs.length => isNot (gs.get i)) ↔ k = t := by
    rw [ht]; simp
  simpa [isNot_iff] using hh

lemma threshold {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (A : Fin n → Fin m → Bool) (hrow : Function.Injective A)
    (hcol : Function.Injective (fun j i => A i j)) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hrep : PEqualNP.Represents.Represents A C) (hsize : C.size+2 ≤ n+m)
    (hpos : ¬ PEqualNP.Represents.RepSizeAtMost A C.size) :
    C.size+2 = n+m ∧ notNum C.gates = 1 ∧ cost (C.gates.map trim)+1 = C.size ∧
    ∃ t : Fin C.size, ∀ k : Fin C.size,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k.val).op = .not ↔ k = t := by
  classical
  have hnot : ∃ g ∈ C.gates, g.op = .not := by
    by_contra hh
    apply hpos
    refine ⟨C, ?_, le_rfl, hrep⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hC g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with hop | hop | hop
    · exact ⟨Or.inl hop, hlen⟩
    · exact ⟨Or.inr hop, hlen⟩
    · exact False.elim (hh ⟨g,hg,hop⟩)
  let D : Circuit := ⟨C.gates.map trim, C.output⟩
  have hrepD : PEqualNP.Represents.Represents A D := by
    intro u v
    change (wiresFrom (C.gates.map trim) _).getD C.output false = _
    rw [trim_wires]
    exact hrep u v
  have hs := profile_support (by omega : 0 < n) (by omega : 0 < m) A hrow hcol D hrepD
  have hb := cnt_cost (C.gates.map trim) 0 (inputSupps (n+m)) cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hb
  have hnN := notNum_pos hnot
  have hbudget := cost_not_bound C.gates (fun g hg => (hC g hg).2)
  have hsize' : C.gates.length+2 ≤ n+m := hsize
  have heq : C.size+2 = n+m ∧ notNum C.gates = 1 := by
    dsimp [D] at hs
    change C.gates.length+2 = n+m ∧ notNum C.gates = 1
    omega
  have hcostEq : cost (C.gates.map trim)+1 = C.size := by
    dsimp [D] at hs
    change cost (C.gates.map trim)+1 = C.gates.length
    omega
  refine ⟨heq.1, heq.2, hcostEq, ?_⟩
  obtain ⟨t, ht⟩ := unique_not heq.2
  refine ⟨t, fun k => ?_⟩
  simp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
  rw [List.getD_eq_get _ _ k]
  exact ht k

inductive Expr (N : ℕ) where
  | var : Fin N → Expr N
  | zero : Expr N
  | val : ℕ → Bool → Expr N
  | conj : ℕ → Expr N → Expr N → Expr N
  | disj : ℕ → Expr N → Expr N → Expr N
  | neg : ℕ → Expr N → Expr N

def Expr.eval {N : ℕ} (override : ℕ → Option Bool) (x : Fin N → Bool) : Expr N → Bool
  | .var i => x i
  | .zero => false
  | .val j b => (override j).getD b
  | .conj _ a b => a.eval override x && b.eval override x
  | .disj _ a b => a.eval override x || b.eval override x
  | .neg j a => (override j).getD (!(a.eval override x))

def Expr.supp {N : ℕ} : Expr N → Finset (Fin N)
  | .var i => {i}
  | .zero => ∅
  | .val _ _ => ∅
  | .conj _ a b => a.supp ∪ b.supp
  | .disj _ a b => a.supp ∪ b.supp
  | .neg _ a => a.supp

def Expr.good {N : ℕ} : Expr N → Prop
  | .var _ => True
  | .zero => False
  | .val _ _ => False
  | .conj _ a b => a.good ∧ b.good ∧ Disjoint a.supp b.supp
  | .disj _ a b => a.good ∧ b.good ∧ Disjoint a.supp b.supp
  | .neg _ a => a.good

def Expr.bins {N : ℕ} : Expr N → ℕ
  | .var _ => 0
  | .zero => 0
  | .val _ _ => 0
  | .conj _ a b => a.bins+b.bins+1
  | .disj _ a b => a.bins+b.bins+1
  | .neg _ a => a.bins

def Expr.negs {N : ℕ} : Expr N → ℕ
  | .var _ => 0
  | .zero => 0
  | .val _ _ => 1
  | .conj _ a b => a.negs+b.negs
  | .disj _ a b => a.negs+b.negs
  | .neg _ a => a.negs+1

def Normal (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
  (g.op = .not ∧ g.inputs.length ≤ 1)

lemma normal_cases (g : Gate) (h : Normal g) :
    (∃ a b, g = ⟨.and, [a,b]⟩) ∨ (∃ a b, g = ⟨.or, [a,b]⟩) ∨
    g = ⟨.not, []⟩ ∨ (∃ a, g = ⟨.not, [a]⟩) := by
  rcases g with ⟨op, ins⟩
  rcases h with ⟨hop, hl⟩ | ⟨hop, hl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at hl
    have hr : rest = [] := by simpa using hl
    subst rest
    rcases hop with rfl | rfl
    · exact Or.inl ⟨a,b,rfl⟩
    · exact Or.inr (Or.inl ⟨a,b,rfl⟩)
  · change op = .not at hop
    change ins.length ≤ 1 at hl
    subst op
    cases ins with
    | nil => exact Or.inr (Or.inr (Or.inl rfl))
    | cons a rest =>
      have hr : rest = [] := by simpa using hl
      subst rest
      exact Or.inr (Or.inr (Or.inr ⟨a,rfl⟩))

def applyExpr {N : ℕ} (j : ℕ) (g : Gate) (L : List (Expr N)) : Expr N :=
  match g.op, g.inputs with
  | .and, a :: b :: _ => .conj j (L.getD a .zero) (L.getD b .zero)
  | .or, a :: b :: _ => .disj j (L.getD a .zero) (L.getD b .zero)
  | .not, [] => .val j true
  | .not, a :: _ => .neg j (L.getD a .zero)
  | _, _ => .zero

def exprStep {N : ℕ} (L : List (Expr N)) (g : Gate) : List (Expr N) :=
  L ++ [applyExpr (L.length-N) g L]

def exprs (N : ℕ) (gs : List Gate) : List (Expr N) :=
  gs.foldl exprStep (List.ofFn fun i : Fin N => Expr.var i)

lemma applyExpr_supp {N : ℕ} (j : ℕ) (g : Gate) (h : Normal g) (L : List (Expr N)) :
    (applyExpr j g L).supp = gateSupp (L.map Expr.supp) g := by
  have hd (a : ℕ) : (L.map Expr.supp).getD a ∅ = (L.getD a Expr.zero).supp := by
    change (L.map Expr.supp).getD a (Expr.supp (Expr.zero : Expr N)) = _
    exact List.getD_map L Expr.zero Expr.supp
  rcases normal_cases g h with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩ | rfl | ⟨a,rfl⟩ <;>
    simp only [applyExpr, Expr.supp, gateSupp, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, Finset.union_empty, hd]

lemma exprs_support {N : ℕ} (gs : List Gate) (h : ∀ g ∈ gs, Normal g) :
    (exprs N gs).map Expr.supp = suppsFrom gs (inputSupps N) := by
  have hh : ∀ L : List (Expr N),
      (gs.foldl exprStep L).map Expr.supp = suppsFrom gs (L.map Expr.supp) := by
    induction gs with
    | nil => intro L; rfl
    | cons g gs ih =>
      intro L
      have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) (exprStep L g)
      change (List.map Expr.supp (List.foldl exprStep L (g :: gs))) =
        suppsFrom gs ((L.map Expr.supp) ++ [gateSupp (L.map Expr.supp) g])
      rw [List.foldl_cons, ht]
      congr 1
      simp only [exprStep, List.map_append, List.map_cons, List.map_nil,
        applyExpr_supp _ g (h g List.mem_cons_self)]
  simpa [exprs, inputSupps, List.map_ofFn, Function.comp_def, Expr.supp] using
    hh (List.ofFn fun i : Fin N => Expr.var i)

lemma exprs_length (N : ℕ) (gs : List Gate) : (exprs N gs).length = N+gs.length := by
  have hh : ∀ L : List (Expr N), (gs.foldl exprStep L).length = L.length+gs.length := by
    induction gs with
    | nil => intro L; simp
    | cons g gs ih => intro L; simp [List.foldl_cons, ih, exprStep]; omega
  simpa [exprs] using hh (List.ofFn fun i : Fin N => Expr.var i)

lemma expr_getD_supp {N : ℕ} (L : List (Expr N)) (w : ℕ) :
    (L.map Expr.supp).getD w ∅ = (L.getD w Expr.zero).supp := by
  change (L.map Expr.supp).getD w (Expr.supp (Expr.zero : Expr N)) = _
  exact List.getD_map L Expr.zero Expr.supp

def joint {N : ℕ} (L : List (Expr N)) (W : Finset ℕ) : Finset (Fin N) :=
  W.biUnion (fun w => (L.getD w Expr.zero).supp)

lemma mem_applyExpr {N : ℕ} (j : ℕ) (g : Gate) (h : Normal g)
    (L : List (Expr N)) (i : Fin N) :
    i ∈ (applyExpr j g L).supp ↔ ∃ w ∈ g.inputs, i ∈ (L.getD w Expr.zero).supp := by
  rw [applyExpr_supp _ _ h, mem_gateSupp]
  simp_rw [expr_getD_supp]

lemma joint_bound {N : ℕ} (gs : List Gate) (h : ∀ g ∈ gs, Normal g) (W : Finset ℕ) :
    (joint (exprs N gs) W).card ≤ cost gs+W.card := by
  have hh := cnt_cost gs 0 (inputSupps N) cnt_inputs W
  have heq : joint (exprs N gs) W = W.biUnion
      (fun w => (suppsFrom gs (inputSupps N)).getD w ∅) := by
    apply Finset.biUnion_congr rfl
    intro w hw
    rw [← exprs_support gs h, expr_getD_supp]
  rw [heq]
  simpa using hh

lemma joint_snoc {N : ℕ} (L : List (Expr N)) (g : Gate) (h : Normal g)
    (W : Finset ℕ) (hw : L.length ∈ W) :
    joint (L ++ [applyExpr (L.length-N) g L]) W =
      joint L (W.erase L.length ∪ g.inputs.toFinset) := by
  classical
  ext i
  simp only [joint, Finset.mem_biUnion]
  constructor
  · rintro ⟨w, hwW, hi⟩
    by_cases hwl : w = L.length
    · subst w
      rw [getD_snoc_eq] at hi
      obtain ⟨a, ha, hia⟩ := (mem_applyExpr _ _ h _ _).mp hi
      exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.mpr ha), hia⟩
    · rw [getD_snoc_ne _ _ _ _ hwl] at hi
      exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwl,hwW⟩), hi⟩
  · rintro ⟨w, hwW, hi⟩
    rcases Finset.mem_union.mp hwW with hw0 | hwS
    · obtain ⟨hwl, hwW⟩ := Finset.mem_erase.mp hw0
      refine ⟨w, hwW, ?_⟩
      rw [getD_snoc_ne _ _ _ _ hwl]
      exact hi
    · refine ⟨L.length, hw, ?_⟩
      rw [getD_snoc_eq]
      exact (mem_applyExpr _ _ h _ _).mpr ⟨w,List.mem_toFinset.mp hwS,hi⟩

lemma joint_snoc_unused {N : ℕ} (L : List (Expr N)) (e : Expr N)
    (W : Finset ℕ) (hw : L.length ∉ W) : joint (L ++ [e]) W = joint L W := by
  apply Finset.biUnion_congr rfl
  intro w hwW
  rw [getD_snoc_ne _ _ _ _ (fun he => hw (he ▸ hwW))]

lemma notNum_append (gs hs : List Gate) : notNum (gs ++ hs) = notNum gs+notNum hs := by
  induction gs with
  | nil => simp [notNum]
  | cons g gs ih => simp [notNum, ih, Nat.add_assoc]

lemma cost_snoc (gs : List Gate) (g : Gate) :
    cost (gs ++ [g]) = cost gs+(g.inputs.length-1) := by
  simp [cost, List.map_append, List.sum_append]

lemma exprs_snoc (N : ℕ) (gs : List Gate) (g : Gate) :
    exprs N (gs ++ [g]) = exprs N gs ++ [applyExpr gs.length g (exprs N gs)] := by
  unfold exprs
  rw [List.foldl_append]
  change exprs N gs ++ [applyExpr ((exprs N gs).length-N) g (exprs N gs)] = _
  rw [exprs_length, Nat.add_sub_cancel_left]
  rfl

lemma saturated (gs : List Gate) (h : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (heq : cost (gs.map trim)+notNum gs = gs.length) :
    ∀ g ∈ gs, Normal (trim g) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have htail := cost_not_bound gs (fun g hg => (h g (List.mem_cons_of_mem _ hg)).2)
    obtain ⟨hop, hg⟩ := h g List.mem_cons_self
    have hc : (trim g).inputs.length-1+(if isNot g then 1 else 0) ≤ 1 := by
      rcases g with ⟨op, ins⟩
      cases op <;> simp [trim, isNot] at hg ⊢ <;> omega
    change (trim g).inputs.length-1+cost (gs.map trim)+
      ((if isNot g then 1 else 0)+notNum gs) = gs.length+1 at heq
    have heqT : cost (gs.map trim)+notNum gs = gs.length := by omega
    have heqG : (trim g).inputs.length-1+(if isNot g then 1 else 0) = 1 := by omega
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · rcases a with ⟨op, ins⟩
      cases op <;> simp [trim, isNot, Normal] at hop hg heqG ⊢ <;> omega
    · exact ih (fun g hg => h g (List.mem_cons_of_mem _ hg)) heqT a ha

lemma tight_step {N : ℕ} (gs : List Gate) (hgs : ∀ g ∈ gs, Normal g)
    (g : Gate) (hg : Normal g) (W : Finset ℕ) (hw : N+gs.length ∈ W)
    (hmax : (joint (exprs N (gs ++ [g])) W).card = cost (gs ++ [g])+W.card) :
    0 < g.inputs.length ∧ g.inputs.Nodup ∧
    Disjoint (W.erase (N+gs.length)) g.inputs.toFinset ∧
    (joint (exprs N gs) (W.erase (N+gs.length) ∪ g.inputs.toFinset)).card =
      cost gs+(W.erase (N+gs.length) ∪ g.inputs.toFinset).card := by
  classical
  have hstep := joint_snoc (exprs N gs) g hg W (by simpa [exprs_length] using hw)
  rw [exprs_length, Nat.add_sub_cancel_left] at hstep
  rw [exprs_snoc, cost_snoc, hstep] at hmax
  have hb := joint_bound (N := N) gs hgs (W.erase (N+gs.length) ∪ g.inputs.toFinset)
  have hWpos : 0 < W.card := Finset.card_pos.mpr ⟨_,hw⟩
  have he := Finset.card_erase_of_mem hw
  have hu := Finset.card_union_le (W.erase (N+gs.length)) g.inputs.toFinset
  have hs := List.toFinset_card_le g.inputs
  have hi := Finset.card_union_add_card_inter (W.erase (N+gs.length)) g.inputs.toFinset
  have hp : 0 < g.inputs.length := by omega
  have hcard : g.inputs.toFinset.card = g.inputs.length := by omega
  have hzero : ((W.erase (N+gs.length)) ∩ g.inputs.toFinset).card = 0 := by omega
  refine ⟨hp, ?_, Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero), ?_⟩
  · exact (Multiset.toFinset_card_eq_card_iff_nodup (m := (g.inputs : Multiset ℕ))).mp hcard
  · omega

lemma joint_erase {N : ℕ} (L : List (Expr N)) (W : Finset ℕ) (j : ℕ)
    (hz : (L.getD j Expr.zero).supp = ∅) : joint L (W.erase j) = joint L W := by
  classical
  ext i
  simp only [joint, Finset.mem_biUnion]
  constructor
  · rintro ⟨w, hw, hi⟩
    exact ⟨w, (Finset.mem_erase.mp hw).2, hi⟩
  · rintro ⟨w, hw, hi⟩
    have hne : w ≠ j := by intro he; subst w; rw [hz] at hi; simpa using hi
    exact ⟨w, Finset.mem_erase.mpr ⟨hne,hw⟩, hi⟩

lemma applyExpr_support_joint {N : ℕ} (j : ℕ) (g : Gate) (h : Normal g) (L : List (Expr N)) :
    (applyExpr j g L).supp = joint L g.inputs.toFinset := by
  classical
  ext i
  simp only [mem_applyExpr _ _ h, joint, Finset.mem_biUnion, List.mem_toFinset]

lemma applyExpr_bins {N : ℕ} (j : ℕ) (g : Gate) (h : Normal g)
    (hn : g.inputs.Nodup) (L : List (Expr N)) :
    (applyExpr j g L).bins = (g.inputs.length-1)+
      ∑ w ∈ g.inputs.toFinset, (L.getD w Expr.zero).bins := by
  classical
  rcases normal_cases g h with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩ | rfl | ⟨a,rfl⟩
  · have hab : a ≠ b := by simpa using hn
    simp [applyExpr, Expr.bins, hab]; omega
  · have hab : a ≠ b := by simpa using hn
    simp [applyExpr, Expr.bins, hab]; omega
  · simp [applyExpr, Expr.bins]
  · simp [applyExpr, Expr.bins]

lemma applyExpr_negs {N : ℕ} (j : ℕ) (g : Gate) (h : Normal g)
    (hn : g.inputs.Nodup) (L : List (Expr N)) :
    (applyExpr j g L).negs = (if isNot g then 1 else 0)+
      ∑ w ∈ g.inputs.toFinset, (L.getD w Expr.zero).negs := by
  classical
  rcases normal_cases g h with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩ | rfl | ⟨a,rfl⟩
  · have hab : a ≠ b := by simpa using hn
    simp [applyExpr, Expr.negs, isNot, hab]
  · have hab : a ≠ b := by simpa using hn
    simp [applyExpr, Expr.negs, isNot, hab]
  · simp [applyExpr, Expr.negs, isNot]
  · simp [applyExpr, Expr.negs, isNot]; omega

lemma applyExpr_good {N : ℕ} (j : ℕ) (g : Gate) (h : Normal g)
    (hn : g.inputs.Nodup) (hp : 0 < g.inputs.length) (L : List (Expr N))
    (hgood : ∀ w ∈ g.inputs.toFinset, (L.getD w Expr.zero).good)
    (hpair : (g.inputs.toFinset : Set ℕ).Pairwise (fun a b =>
      Disjoint (L.getD a Expr.zero).supp (L.getD b Expr.zero).supp)) :
    (applyExpr j g L).good := by
  classical
  rcases normal_cases g h with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩ | rfl | ⟨a,rfl⟩
  · have hab : a ≠ b := by simpa using hn
    exact ⟨hgood a (by simp),hgood b (by simp),hpair (by simp) (by simp) hab⟩
  · have hab : a ≠ b := by simpa using hn
    exact ⟨hgood a (by simp),hgood b (by simp),hpair (by simp) (by simp) hab⟩
  · simp at hp
  · exact hgood a (by simp)

def Forest {N : ℕ} (L : List (Expr N)) (W : Finset ℕ) (b u : ℕ) : Prop :=
  (∀ w ∈ W, (L.getD w Expr.zero).good) ∧
  (W : Set ℕ).Pairwise (fun a b =>
    Disjoint (L.getD a Expr.zero).supp (L.getD b Expr.zero).supp) ∧
  (∑ w ∈ W, (L.getD w Expr.zero).bins) = b ∧
  (∑ w ∈ W, (L.getD w Expr.zero).negs) ≤ u

lemma forest_transport {N : ℕ} (L K : List (Expr N)) (W : Finset ℕ) (b u v : ℕ)
    (heq : ∀ w ∈ W, K.getD w Expr.zero = L.getD w Expr.zero) (hu : u ≤ v)
    (h : Forest L W b u) : Forest K W b v := by
  obtain ⟨hg, hp, hb, hn⟩ := h
  refine ⟨fun w hw => ?_, ?_, ?_, ?_⟩
  · rw [heq w hw]; exact hg w hw
  · intro a ha b hb hab
    rw [heq a ha, heq b hb]
    exact hp ha hb hab
  · calc
      (∑ w ∈ W, (K.getD w Expr.zero).bins) = ∑ w ∈ W, (L.getD w Expr.zero).bins :=
        Finset.sum_congr rfl (fun w hw => by rw [heq w hw])
      _ = b := hb
  · calc
      (∑ w ∈ W, (K.getD w Expr.zero).negs) = ∑ w ∈ W, (L.getD w Expr.zero).negs :=
        Finset.sum_congr rfl (fun w hw => by rw [heq w hw])
      _ ≤ u := hn
      _ ≤ v := hu

lemma forest_active {N : ℕ} (L : List (Expr N)) (g : Gate) (hg : Normal g)
    (W : Finset ℕ) (hw : L.length ∈ W) (hnodup : g.inputs.Nodup)
    (hlen : 0 < g.inputs.length) (hd : Disjoint (W.erase L.length) g.inputs.toFinset)
    (b u : ℕ) (hf : Forest L (W.erase L.length ∪ g.inputs.toFinset) b u) :
    Forest (L ++ [applyExpr (L.length-N) g L]) W
      (b+(g.inputs.length-1)) (u+(if isNot g then 1 else 0)) := by
  classical
  obtain ⟨hgood, hpair, hbin, hneg⟩ := hf
  let e := applyExpr (L.length-N) g L
  have hold : ∀ w ∈ W.erase L.length,
      (L ++ [e]).getD w Expr.zero = L.getD w Expr.zero := by
    intro w hw0
    exact getD_snoc_ne _ _ _ _ (Finset.mem_erase.mp hw0).1
  have hegood : e.good := by
    apply applyExpr_good _ _ hg hnodup hlen
    · intro w hwS
      exact hgood w (Finset.mem_union_right _ hwS)
    · intro a ha b hb hab
      exact hpair (Finset.mem_union_right _ ha) (Finset.mem_union_right _ hb) hab
  have hedisj : ∀ w ∈ W.erase L.length,
      Disjoint e.supp (L.getD w Expr.zero).supp := by
    intro w hw0
    rw [applyExpr_support_joint _ _ hg]
    change Disjoint (g.inputs.toFinset.biUnion (fun a => (L.getD a Expr.zero).supp)) _
    rw [Finset.disjoint_biUnion_left]
    intro a ha
    have haw : a ≠ w := by
      intro he
      subst a
      exact Finset.disjoint_left.mp hd hw0 ha
    exact hpair (Finset.mem_union_right _ ha) (Finset.mem_union_left _ hw0) haw
  have hsum (f : Expr N → ℕ) :
      (∑ w ∈ W, f ((L ++ [e]).getD w Expr.zero)) =
        f e + ∑ w ∈ W.erase L.length, f (L.getD w Expr.zero) := by
    calc
      (∑ w ∈ W, f ((L ++ [e]).getD w Expr.zero)) =
          ∑ w ∈ insert L.length (W.erase L.length), f ((L ++ [e]).getD w Expr.zero) := by
        rw [Finset.insert_erase hw]
      _ = f e + ∑ w ∈ W.erase L.length, f (L.getD w Expr.zero) := by
        rw [Finset.sum_insert (by simp : L.length ∉ W.erase L.length), getD_snoc_eq]
        congr 1
        apply Finset.sum_congr rfl
        intro w hw0
        rw [hold w hw0]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hwW
    by_cases hwl : w = L.length
    · subst w
      rw [getD_snoc_eq]
      exact hegood
    · rw [getD_snoc_ne _ _ _ _ hwl]
      exact hgood w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwl,hwW⟩))
  · intro a ha b hb hab
    by_cases hal : a = L.length
    · subst a
      rw [getD_snoc_eq, getD_snoc_ne _ _ _ _ (Ne.symm hab)]
      exact hedisj b (Finset.mem_erase.mpr ⟨Ne.symm hab,hb⟩)
    · by_cases hbl : b = L.length
      · subst b
        rw [getD_snoc_eq, getD_snoc_ne _ _ _ _ hal]
        exact (hedisj a (Finset.mem_erase.mpr ⟨hal,ha⟩)).symm
      · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ hbl]
        exact hpair (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hal,ha⟩))
          (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hbl,hb⟩)) hab
  · have hs := hsum Expr.bins
    rw [applyExpr_bins _ _ hg hnodup] at hs
    rw [Finset.sum_union hd] at hbin
    dsimp [e] at hs
    omega
  · have hs := hsum Expr.negs
    rw [applyExpr_negs _ _ hg hnodup] at hs
    rw [Finset.sum_union hd] at hneg
    dsimp [e] at hs
    omega

lemma initial_expr (N w : ℕ) (hw : w < N) :
    (exprs N []).getD w Expr.zero = Expr.var ⟨w,hw⟩ := by
  simp [exprs, List.getD_eq_getElem?_getD, hw]

lemma forest_tight {N : ℕ} (gs : List Gate) (hgs : ∀ g ∈ gs, Normal g) :
    ∀ W : Finset ℕ, (joint (exprs N gs) W).card = cost gs+W.card →
      Forest (exprs N gs) W (cost gs) (notNum gs) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    intro W hmax
    have hv : ∀ w ∈ W, w < N := by
      intro w hw
      by_contra hbad
      have hzero : (exprs N []).getD w Expr.zero = Expr.zero := by
        rw [List.getD_eq_default _ _ (by simpa [exprs] using Nat.le_of_not_gt hbad)]
      have hWpos : 0 < W.card := Finset.card_pos.mpr ⟨w,hw⟩
      have he := joint_erase (exprs N []) W w (by rw [hzero]; rfl)
      have hb := joint_bound (N := N) [] (by simp) (W.erase w)
      rw [he, hmax, Finset.card_erase_of_mem hw] at hb
      simp only [cost, List.map_nil, List.sum_nil, zero_add] at hb
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro w hw
      rw [initial_expr N w (hv w hw)]
      trivial
    · intro a ha b hb hab
      rw [initial_expr N a (hv a ha), initial_expr N b (hv b hb)]
      simp only [Expr.supp, Finset.disjoint_singleton]
      exact fun he => hab (congrArg Fin.val he)
    · change (∑ w ∈ W, ((exprs N []).getD w Expr.zero).bins) = 0
      apply Finset.sum_eq_zero
      intro w hw
      rw [initial_expr N w (hv w hw)]
      rfl
    · change (∑ w ∈ W, ((exprs N []).getD w Expr.zero).negs) ≤ 0
      have hz : (∑ w ∈ W, ((exprs N []).getD w Expr.zero).negs) = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        rw [initial_expr N w (hv w hw)]
        rfl
      omega
  | append_singleton gs g ih =>
    intro W hmax
    have hp : ∀ a ∈ gs, Normal a := fun a ha => hgs a (List.mem_append_left _ ha)
    have hg : Normal g := hgs g (by simp)
    by_cases hw : N+gs.length ∈ W
    · obtain ⟨hlen, hnodup, hd, hnew⟩ := tight_step gs hp g hg W hw hmax
      have hf := ih hp (W.erase (N+gs.length) ∪ g.inputs.toFinset) hnew
      have hh := forest_active (exprs N gs) g hg W (by simpa [exprs_length] using hw)
        hnodup hlen (by simpa [exprs_length] using hd) (cost gs) (notNum gs)
        (by simpa [exprs_length] using hf)
      simpa only [exprs_snoc, exprs_length, Nat.add_sub_cancel_left, cost_snoc,
        notNum_append, notNum, Nat.add_zero] using hh
    · have hnot : (exprs N gs).length ∉ W := by simpa [exprs_length] using hw
      have hs := joint_snoc_unused (exprs N gs) (applyExpr gs.length g (exprs N gs)) W hnot
      rw [exprs_snoc, cost_snoc, hs] at hmax
      have hb := joint_bound (N := N) gs hp W
      have hcost : g.inputs.length-1 = 0 := by omega
      have hnew : (joint (exprs N gs) W).card = cost gs+W.card := by omega
      have hf := ih hp W hnew
      have hh := forest_transport (exprs N gs)
        (exprs N gs ++ [applyExpr gs.length g (exprs N gs)]) W (cost gs) (notNum gs)
        (notNum gs+(if isNot g then 1 else 0)) (fun w hwW =>
          getD_snoc_ne _ _ _ _ (fun he => hnot (he ▸ hwW))) (by omega) hf
      simpa only [exprs_snoc, cost_snoc, hcost, Nat.add_zero, notNum_append,
        notNum] using hh

def Expr.nodes {N : ℕ} : Expr N → ℕ
  | .var _ => 0
  | .zero => 1
  | .val _ _ => 1
  | .conj _ a b => a.nodes+b.nodes+1
  | .disj _ a b => a.nodes+b.nodes+1
  | .neg _ a => a.nodes+1

def Expr.occs {N : ℕ} (w : ℕ) : Expr N → ℕ
  | .var i => if i.val = w then 1 else 0
  | .zero => 0
  | .val _ _ => 0
  | .conj _ a b => a.occs w+b.occs w
  | .disj _ a b => a.occs w+b.occs w
  | .neg _ a => a.occs w

def Expr.compile {N : ℕ} : Expr N → ℕ → List Gate × ℕ
  | .var i, _ => ([],i.val)
  | .zero, s => ([⟨.or,[]⟩],s)
  | .val _ b, s => ([⟨if b then .and else .or,[]⟩],s)
  | .conj _ a b, s =>
    let ca := a.compile s
    let cb := b.compile (s+ca.1.length)
    (ca.1 ++ cb.1 ++ [⟨.and,[ca.2,cb.2]⟩],s+ca.1.length+cb.1.length)
  | .disj _ a b, s =>
    let ca := a.compile s
    let cb := b.compile (s+ca.1.length)
    (ca.1 ++ cb.1 ++ [⟨.or,[ca.2,cb.2]⟩],s+ca.1.length+cb.1.length)
  | .neg _ a, s =>
    let ca := a.compile s
    (ca.1 ++ [⟨.not,[ca.2]⟩],s+ca.1.length)

lemma Expr.compile_length {N : ℕ} (e : Expr N) (s : ℕ) :
    (e.compile s).1.length = e.nodes := by
  induction e generalizing s <;> simp [Expr.compile, Expr.nodes, Nat.add_assoc, *]

lemma Expr.good_nodes {N : ℕ} (e : Expr N) (h : e.good) : e.nodes = e.bins+e.negs := by
  induction e <;> simp_all [Expr.good, Expr.nodes, Expr.bins, Expr.negs] <;> omega

lemma Expr.compile_out_lt {N : ℕ} (e : Expr N) (s : ℕ) (hs : N ≤ s) :
    (e.compile s).2 < s+(e.compile s).1.length := by
  cases e with
  | var i => have hi := i.isLt; simpa [Expr.compile] using lt_of_lt_of_le hi hs
  | zero => simp [Expr.compile]
  | val j b => simp [Expr.compile]
  | conj j a b => simp [Expr.compile] <;> omega
  | disj j a b => simp [Expr.compile] <;> omega
  | neg j a => simp [Expr.compile] <;> omega

lemma Expr.compile_output {N : ℕ} (e : Expr N) (s : ℕ) :
    (e.compile s).2+1 = s+(e.compile s).1.length ∨
    ((e.compile s).1.length = 0 ∧ (e.compile s).2 < N) := by
  cases e with
  | var i => exact Or.inr ⟨rfl,i.isLt⟩
  | zero => exact Or.inl (by simp [Expr.compile])
  | val j b => exact Or.inl (by simp [Expr.compile])
  | conj j a b => exact Or.inl (by simp [Expr.compile] <;> omega)
  | disj j a b => exact Or.inl (by simp [Expr.compile] <;> omega)
  | neg j a => exact Or.inl (by simp [Expr.compile] <;> omega)

lemma Expr.occs_out {N : ℕ} (e : Expr N) (w : ℕ) (hw : N ≤ w) : e.occs w = 0 := by
  induction e with
  | var i => have hi := i.isLt; simp [Expr.occs, show i.val ≠ w by omega]
  | zero => rfl
  | val j b => rfl
  | conj j a b iha ihb => simp [Expr.occs, iha, ihb]
  | disj j a b iha ihb => simp [Expr.occs, iha, ihb]
  | neg j a iha => exact iha

lemma Expr.good_occs {N : ℕ} (e : Expr N) (h : e.good) (i : Fin N) :
    e.occs i.val = if i ∈ e.supp then 1 else 0 := by
  induction e with
  | var j => simp [Expr.occs, Expr.supp, Fin.ext_iff, eq_comm]
  | zero => exact False.elim h
  | val j b => exact False.elim h
  | conj j a b iha ihb =>
    obtain ⟨ha,hb,hd⟩ := h
    rw [Expr.occs, iha ha, ihb hb]
    have hh := Finset.disjoint_left.mp hd
    by_cases hai : i ∈ a.supp <;> by_cases hbi : i ∈ b.supp <;>
      simp_all [Expr.supp]
  | disj j a b iha ihb =>
    obtain ⟨ha,hb,hd⟩ := h
    rw [Expr.occs, iha ha, ihb hb]
    have hh := Finset.disjoint_left.mp hd
    by_cases hai : i ∈ a.supp <;> by_cases hbi : i ∈ b.supp <;>
      simp_all [Expr.supp]
  | neg j a iha => exact iha h

def mentions (gs : List Gate) (w : ℕ) : ℕ := (gs.map fun g => g.inputs.count w).sum

lemma mentions_append (gs hs : List Gate) (w : ℕ) :
    mentions (gs ++ hs) w = mentions gs w+mentions hs w := by
  simp [mentions, List.map_append, List.sum_append]

lemma mentions_range (gs : List Gate) (w : ℕ) :
    (∑ j ∈ Finset.range gs.length, (gs.getD j ⟨.or,[]⟩).inputs.count w) = mentions gs w := by
  induction gs using List.reverseRecOn with
  | nil => simp [mentions]
  | append_singleton gs g ih =>
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
    rw [Finset.sum_range_succ, getD_snoc_eq]
    have hh : (∑ j ∈ Finset.range gs.length, ((gs ++ [g]).getD j ⟨.or,[]⟩).inputs.count w) =
        ∑ j ∈ Finset.range gs.length, (gs.getD j ⟨.or,[]⟩).inputs.count w := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [getD_snoc_ne _ _ _ _ (by have := Finset.mem_range.mp hj; omega)]
    rw [hh, ih, mentions_append]
    rfl

lemma pair_count (a b w : ℕ) :
    [a,b].count w = (if a=w then 1 else 0)+(if b=w then 1 else 0) := by
  by_cases ha : a=w <;> by_cases hb : b=w <;> simp_all

lemma intervals (s a b w : ℕ) :
    (if s ≤ w ∧ w < s+a then 1 else 0)+
    (if s+a ≤ w ∧ w < s+a+b then 1 else 0)+
    (if s+a+b=w then 1 else 0) =
    (if s ≤ w ∧ w < s+a+b+1 then 1 else 0) := by
  split_ifs <;> omega

lemma mentions_singleton (g : Gate) (w : ℕ) : mentions [g] w = g.inputs.count w := by
  simp [mentions]

lemma one_interval (s w : ℕ) :
    (if s=w then 1 else 0) = (if s ≤ w ∧ w < s+1 then 1 else 0) := by
  split_ifs <;> omega

lemma join_usage (s : ℕ) (P Q : List Gate × ℕ) (op : GateOp) (w A B : ℕ)
    (ha : mentions P.1 w+(if P.2=w then 1 else 0) =
      A+(if s ≤ w ∧ w < s+P.1.length then 1 else 0))
    (hb : mentions Q.1 w+(if Q.2=w then 1 else 0) =
      B+(if s+P.1.length ≤ w ∧ w < s+P.1.length+Q.1.length then 1 else 0)) :
    mentions (P.1 ++ Q.1 ++ [⟨op,[P.2,Q.2]⟩]) w+
      (if s+P.1.length+Q.1.length=w then 1 else 0) =
    A+B+(if s ≤ w ∧ w < s+P.1.length+Q.1.length+1 then 1 else 0) := by
  rw [mentions_append, mentions_append, mentions_singleton]
  change mentions P.1 w+mentions Q.1 w+[P.2,Q.2].count w+_ = _
  rw [pair_count]
  have hi := intervals s P.1.length Q.1.length w
  omega

lemma extend_usage (s : ℕ) (P : List Gate × ℕ) (op : GateOp) (w A : ℕ)
    (ha : mentions P.1 w+(if P.2=w then 1 else 0) =
      A+(if s ≤ w ∧ w < s+P.1.length then 1 else 0)) :
    mentions (P.1 ++ [⟨op,[P.2]⟩]) w+
      (if s+P.1.length=w then 1 else 0) =
    A+(if s ≤ w ∧ w < s+P.1.length+1 then 1 else 0) := by
  rw [mentions_append, mentions_singleton]
  change mentions P.1 w+[P.2].count w+_ = _
  have hc : [P.2].count w = (if P.2=w then 1 else 0) := by
    by_cases hh : P.2=w <;> simp [hh]
  rw [hc]
  have hi := intervals s P.1.length 0 w
  simp only [Nat.add_zero] at hi
  have hz : (if s+P.1.length ≤ w ∧ w < s+P.1.length then 1 else 0 : ℕ) = 0 := by
    split_ifs <;> omega
  rw [hz] at hi
  omega

lemma Expr.compile_uses {N : ℕ} (e : Expr N) (s w : ℕ) (hs : N ≤ s) :
    mentions (e.compile s).1 w+(if (e.compile s).2=w then 1 else 0) =
      e.occs w+(if s ≤ w ∧ w < s+(e.compile s).1.length then 1 else 0) := by
  induction e generalizing s with
  | var i =>
    change 0+(if i.val=w then 1 else 0) =
      (if i.val=w then 1 else 0)+(if s ≤ w ∧ w < s then 1 else 0)
    rw [Nat.zero_add, if_neg (by omega : ¬ (s ≤ w ∧ w < s)), Nat.add_zero]
  | zero =>
    simp only [Expr.compile, mentions, Expr.occs, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.count_nil, List.length_cons, List.length_nil,
      Nat.add_zero, Nat.zero_add]
    exact one_interval s w
  | val j b =>
    simp only [Expr.compile, mentions, Expr.occs, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.count_nil, List.length_cons, List.length_nil,
      Nat.add_zero, Nat.zero_add]
    exact one_interval s w
  | conj j a b iha ihb =>
    have ha := iha s hs
    have hb := ihb (s+(a.compile s).1.length) (by omega)
    have hh := join_usage s (a.compile s) (b.compile (s+(a.compile s).1.length)) .and w
      (a.occs w) (b.occs w) ha hb
    simpa only [Expr.compile, Expr.occs, List.length_append, List.length_cons,
      List.length_nil, Nat.add_zero, Nat.add_assoc] using hh
  | disj j a b iha ihb =>
    have ha := iha s hs
    have hb := ihb (s+(a.compile s).1.length) (by omega)
    have hh := join_usage s (a.compile s) (b.compile (s+(a.compile s).1.length)) .or w
      (a.occs w) (b.occs w) ha hb
    simpa only [Expr.compile, Expr.occs, List.length_append, List.length_cons,
      List.length_nil, Nat.add_zero, Nat.add_assoc] using hh
  | neg j a iha =>
    have ha := iha s hs
    have hh := extend_usage s (a.compile s) .not w (a.occs w) ha
    simp only [Expr.compile, Expr.occs, List.length_append, List.length_cons,
      List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc]
    simp only [Nat.add_assoc, Nat.zero_add] at hh
    exact hh

def Valid (s : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ w ∈ (gs.getD j ⟨.or,[]⟩).inputs, w < s+j

lemma valid_append (s : ℕ) (gs hs : List Gate) (hp : Valid s gs)
    (hq : Valid (s+gs.length) hs) : Valid s (gs ++ hs) := by
  intro j hj w hw
  by_cases hjp : j < gs.length
  · rw [List.getD_append _ _ _ _ hjp] at hw
    exact hp j hjp w hw
  · have hjq : j-gs.length < hs.length := by simp only [List.length_append] at hj; omega
    rw [List.getD_append_right _ _ _ _ (by omega)] at hw
    have hh := hq (j-gs.length) hjq w hw
    omega

lemma valid_snoc (s : ℕ) (gs : List Gate) (g : Gate) (hp : Valid s gs)
    (hg : ∀ w ∈ g.inputs, w < s+gs.length) : Valid s (gs ++ [g]) := by
  intro j hj w hw
  by_cases hjp : j = gs.length
  · subst j
    rw [getD_snoc_eq] at hw
    exact hg w hw
  · have hjlt : j < gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    rw [getD_snoc_ne _ _ _ _ hjp] at hw
    exact hp j hjlt w hw

lemma valid_singleton (s : ℕ) (g : Gate) (hg : ∀ w ∈ g.inputs, w < s) : Valid s [g] := by
  intro j hj w hw
  have hj0 : j = 0 := by simpa using hj
  subst j
  exact hg w hw

lemma valid_join (s : ℕ) (P Q : List Gate × ℕ) (op : GateOp)
    (hp : Valid s P.1) (hq : Valid (s+P.1.length) Q.1)
    (ha : P.2 < s+P.1.length) (hb : Q.2 < s+P.1.length+Q.1.length) :
    Valid s (P.1 ++ Q.1 ++ [⟨op,[P.2,Q.2]⟩]) := by
  apply valid_snoc s (P.1 ++ Q.1) _ (valid_append _ _ _ hp hq)
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> simp only [List.length_append] <;> omega

lemma Expr.compile_valid {N : ℕ} (e : Expr N) (s : ℕ) (hs : N ≤ s) :
    Valid s (e.compile s).1 := by
  induction e generalizing s with
  | var i => intro j hj; simpa [Expr.compile] using hj
  | zero => apply valid_singleton; simp [Expr.compile]
  | val j b => apply valid_singleton; simp [Expr.compile]
  | conj j a b iha ihb =>
    exact valid_join s (a.compile s) (b.compile (s+(a.compile s).1.length)) .and
      (iha s hs) (ihb _ (by omega)) (a.compile_out_lt s hs)
      (by simpa [Nat.add_assoc] using b.compile_out_lt (s+(a.compile s).1.length) (by omega))
  | disj j a b iha ihb =>
    exact valid_join s (a.compile s) (b.compile (s+(a.compile s).1.length)) .or
      (iha s hs) (ihb _ (by omega)) (a.compile_out_lt s hs)
      (by simpa [Nat.add_assoc] using b.compile_out_lt (s+(a.compile s).1.length) (by omega))
  | neg j a iha =>
    apply valid_snoc s (a.compile s).1 _ (iha s hs)
    intro w hw
    have he : w = (a.compile s).2 := by simpa using hw
    subst w
    exact a.compile_out_lt s hs

lemma Expr.compile_binary {N : ℕ} (e : Expr N) : e.good → e.negs = 0 →
    ∀ s : ℕ, ∀ g ∈ (e.compile s).1,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  induction e with
  | var i => intro h hn s g hg; simp [Expr.compile] at hg
  | zero => intro h; exact False.elim h
  | val j b => intro h; exact False.elim h
  | conj j a b iha ihb =>
    intro h hn s g hg
    obtain ⟨ha,hb,hd⟩ := h
    have hna : a.negs = 0 := by change a.negs+b.negs = 0 at hn; omega
    have hnb : b.negs = 0 := by change a.negs+b.negs = 0 at hn; omega
    simp only [Expr.compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact iha ha hna s g hg
    · exact ihb hb hnb _ g hg
    · exact ⟨Or.inl rfl,rfl⟩
  | disj j a b iha ihb =>
    intro h hn s g hg
    obtain ⟨ha,hb,hd⟩ := h
    have hna : a.negs = 0 := by change a.negs+b.negs = 0 at hn; omega
    have hnb : b.negs = 0 := by change a.negs+b.negs = 0 at hn; omega
    simp only [Expr.compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact iha ha hna s g hg
    · exact ihb hb hnb _ g hg
    · exact ⟨Or.inr rfl,rfl⟩
  | neg j a iha => intro h hn; simp [Expr.negs] at hn

def compiled {N : ℕ} (e : Expr N) : Circuit := ⟨(e.compile N).1,(e.compile N).2⟩

def uses (C : Circuit) (w : ℕ) : ℕ :=
  PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w+
    (if C.output=w then 1 else 0)

def Tree (N : ℕ) (C : Circuit) : Prop :=
  (∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack N C ∧
  (C.output+1 = N+C.size ∨ (C.size = 0 ∧ C.output < N)) ∧
  (∀ w < N, uses C w ≤ 1) ∧ (∀ j < C.size, uses C (N+j) = 1)

lemma compiled_uses {N : ℕ} (e : Expr N) (w : ℕ) :
    uses (compiled e) w = e.occs w+
      (if N ≤ w ∧ w < N+(e.compile N).1.length then 1 else 0) := by
  change (∑ j ∈ Finset.range (e.compile N).1.length,
      ((e.compile N).1.getD j ⟨.or,[]⟩).inputs.count w)+
    (if (e.compile N).2=w then 1 else 0) = _
  rw [mentions_range]
  exact e.compile_uses N w le_rfl

lemma compiled_input_uses {N : ℕ} (e : Expr N) (hg : e.good) (i : Fin N) :
    uses (compiled e) i.val = if i ∈ e.supp then 1 else 0 := by
  rw [compiled_uses, e.good_occs hg i]
  have hi := i.isLt
  rw [if_neg (by omega : ¬ (N ≤ i.val ∧ i.val < N+(e.compile N).1.length)), Nat.add_zero]

lemma compiled_tree {N : ℕ} (e : Expr N) (hg : e.good) (hn : e.negs = 0) :
    Tree N (compiled e) := by
  refine ⟨e.compile_binary hg hn N, ?_, e.compile_output N, ?_, ?_⟩
  · exact e.compile_valid N le_rfl
  · intro w hw
    have hh := compiled_input_uses e hg (⟨w,hw⟩ : Fin N)
    rw [hh]
    split_ifs <;> omega
  · intro j hj
    rw [compiled_uses, e.occs_out (N+j) (by omega)]
    have hi : N ≤ N+j ∧ N+j < N+(e.compile N).1.length := by exact ⟨by omega,by exact Nat.add_lt_add_left hj N⟩
    rw [if_pos hi]

lemma snoc_value (gs : List Gate) (g : Gate) (w : List Bool) :
    (wiresFrom (gs ++ [g]) w).getD (w.length+gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresFrom gs w).getD i false) := by
  rw [wiresFrom_append]
  change ((wiresFrom gs w) ++ [g.op.eval (g.inputs.map fun i =>
    (wiresFrom gs w).getD i false)]).getD (w.length+gs.length) false = _
  rw [← length_wiresFrom gs w, getD_snoc_eq]

lemma join_value (s : ℕ) (P Q : List Gate × ℕ) (op : GateOp) (w : List Bool)
    (hw : w.length = s) (ha : P.2 < s+P.1.length) :
    (wiresFrom (P.1 ++ Q.1 ++ [⟨op,[P.2,Q.2]⟩]) w).getD
      (s+P.1.length+Q.1.length) false =
    op.eval [(wiresFrom P.1 w).getD P.2 false,
      (wiresFrom Q.1 (wiresFrom P.1 w)).getD Q.2 false] := by
  have hh := snoc_value (P.1 ++ Q.1) ⟨op,[P.2,Q.2]⟩ w
  have hp := wiresFrom_append P.1 Q.1 w
  rw [hp] at hh
  simp only [List.map_cons, List.map_nil] at hh
  rw [getD_wiresFrom Q.1 (wiresFrom P.1 w) P.2 (by rw [length_wiresFrom, hw]; exact ha)] at hh
  simpa only [hw, List.length_append, Nat.add_assoc] using hh

lemma unary_value (s : ℕ) (P : List Gate × ℕ) (op : GateOp) (w : List Bool)
    (hw : w.length = s) :
    (wiresFrom (P.1 ++ [⟨op,[P.2]⟩]) w).getD (s+P.1.length) false =
      op.eval [(wiresFrom P.1 w).getD P.2 false] := by
  have hh := snoc_value P.1 ⟨op,[P.2]⟩ w
  simpa only [hw, List.map_cons, List.map_nil] using hh

lemma input_values (N s : ℕ) (gs : List Gate) (w : List Bool)
    (hw : w.length = s) (hs : N ≤ s) :
    (fun i : Fin N => (wiresFrom gs w).getD i.val false) =
      (fun i : Fin N => w.getD i.val false) := by
  funext i
  exact getD_wiresFrom gs w i.val (by rw [hw]; have hi := i.isLt; omega)

lemma Expr.compile_eval {N : ℕ} (e : Expr N) (s : ℕ) (w : List Bool)
    (hw : w.length = s) (hs : N ≤ s) :
    (wiresFrom (e.compile s).1 w).getD (e.compile s).2 false =
      e.eval (fun _ => none) (fun i => w.getD i.val false) := by
  induction e generalizing s w with
  | var i => rfl
  | zero =>
    have hh := snoc_value [] ⟨.or,[]⟩ w
    simp only [List.nil_append, List.length_nil, Nat.add_zero, hw,
      List.map_nil, GateOp.eval, List.any_nil] at hh
    exact hh
  | val j b =>
    cases b
    · have hh := snoc_value [] ⟨.or,[]⟩ w
      simp only [List.nil_append, List.length_nil, Nat.add_zero, hw,
        List.map_nil, GateOp.eval, List.any_nil] at hh
      exact hh
    · have hh := snoc_value [] ⟨.and,[]⟩ w
      simp only [List.nil_append, List.length_nil, Nat.add_zero, hw,
        List.map_nil, GateOp.eval, List.all_nil] at hh
      exact hh
  | conj j a b iha ihb =>
    have ha := iha s w hw hs
    have hla : (wiresFrom (a.compile s).1 w).length = s+(a.compile s).1.length := by
      rw [length_wiresFrom,hw]
    have hb := ihb (s+(a.compile s).1.length) (wiresFrom (a.compile s).1 w) hla (by omega)
    rw [input_values N s (a.compile s).1 w hw hs] at hb
    change (wiresFrom ((a.compile s).1 ++ (b.compile (s+(a.compile s).1.length)).1 ++
      [⟨.and,[(a.compile s).2,(b.compile (s+(a.compile s).1.length)).2]⟩]) w).getD
      (s+(a.compile s).1.length+(b.compile (s+(a.compile s).1.length)).1.length) false =
      (a.eval (fun _ => none) (fun i => w.getD i.val false) &&
      b.eval (fun _ => none) (fun i => w.getD i.val false))
    rw [join_value s (a.compile s) (b.compile (s+(a.compile s).1.length)) .and w hw (a.compile_out_lt s hs)]
    simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [ha,hb]
  | disj j a b iha ihb =>
    have ha := iha s w hw hs
    have hla : (wiresFrom (a.compile s).1 w).length = s+(a.compile s).1.length := by
      rw [length_wiresFrom,hw]
    have hb := ihb (s+(a.compile s).1.length) (wiresFrom (a.compile s).1 w) hla (by omega)
    rw [input_values N s (a.compile s).1 w hw hs] at hb
    change (wiresFrom ((a.compile s).1 ++ (b.compile (s+(a.compile s).1.length)).1 ++
      [⟨.or,[(a.compile s).2,(b.compile (s+(a.compile s).1.length)).2]⟩]) w).getD
      (s+(a.compile s).1.length+(b.compile (s+(a.compile s).1.length)).1.length) false =
      (a.eval (fun _ => none) (fun i => w.getD i.val false) ||
      b.eval (fun _ => none) (fun i => w.getD i.val false))
    rw [join_value s (a.compile s) (b.compile (s+(a.compile s).1.length)) .or w hw (a.compile_out_lt s hs)]
    simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [ha,hb]
  | neg j a iha =>
    change (wiresFrom ((a.compile s).1 ++ [⟨.not,[(a.compile s).2]⟩]) w).getD
      (s+(a.compile s).1.length) false = !(a.eval (fun _ => none) (fun i => w.getD i.val false))
    rw [unary_value s (a.compile s) .not w hw]
    simp only [GateOp.eval, List.headD_cons]
    rw [iha s w hw hs]

lemma compiled_eval {N : ℕ} (e : Expr N) (x : Fin N → Bool) :
    (compiled e).eval (List.ofFn x) = e.eval (fun _ => none) x := by
  have hh := e.compile_eval N (List.ofFn x) (by simp) le_rfl
  have hx : (fun i : Fin N => (List.ofFn x).getD i.val false) = x := by
    funext i
    simp [List.getD_eq_getElem?_getD]
  rw [hx] at hh
  exact hh

def overrideEval (rho : ℕ → Option Bool) (j : ℕ) (g : Gate) (ys : List Bool) : Bool :=
  match g.op with
  | .not => (rho j).getD (g.op.eval (g.inputs.map fun w => ys.getD w false))
  | _ => g.op.eval (g.inputs.map fun w => ys.getD w false)

def forcedStep (N : ℕ) (rho : ℕ → Option Bool) (ys : List Bool) (g : Gate) : List Bool :=
  ys ++ [overrideEval rho (ys.length-N) g ys]

def forcedWires (N : ℕ) (rho : ℕ → Option Bool) (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (forcedStep N rho) xs

lemma applyExpr_eval {N : ℕ} (j : ℕ) (g : Gate) (hg : Normal g) (L : List (Expr N))
    (rho : ℕ → Option Bool) (x : Fin N → Bool) :
    (applyExpr j g L).eval rho x = overrideEval rho j g (L.map (Expr.eval rho x)) := by
  have hd (w : ℕ) : (L.map (Expr.eval rho x)).getD w false = (L.getD w Expr.zero).eval rho x := by
    change (L.map (Expr.eval rho x)).getD w (Expr.eval rho x (Expr.zero : Expr N)) = _
    exact List.getD_map L Expr.zero (Expr.eval rho x)
  rcases normal_cases g hg with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩ | rfl | ⟨a,rfl⟩ <;>
    simp only [applyExpr, Expr.eval, overrideEval, GateOp.eval, List.map_cons,
      List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
      List.headD_cons, List.headD_nil, id_eq, Bool.and_true, Bool.or_false,
      Bool.not_false, hd]

lemma exprs_override (N : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, Normal g)
    (rho : ℕ → Option Bool) (x : Fin N → Bool) :
    (exprs N gs).map (Expr.eval rho x) = forcedWires N rho gs (List.ofFn x) := by
  have hh : ∀ L : List (Expr N),
      (gs.foldl exprStep L).map (Expr.eval rho x) =
        forcedWires N rho gs (L.map (Expr.eval rho x)) := by
    induction gs with
    | nil => intro L; rfl
    | cons g gs ih =>
      intro L
      have ht := ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) (exprStep L g)
      change (List.foldl exprStep (exprStep L g) gs).map (Expr.eval rho x) =
        forcedWires N rho gs (forcedStep N rho (L.map (Expr.eval rho x)) g)
      rw [ht]
      congr 1
      simp only [exprStep, forcedStep, List.map_append, List.map_cons, List.map_nil,
        List.length_map, applyExpr_eval _ g (hgs g List.mem_cons_self)]
  have hi : (List.ofFn fun i : Fin N => Expr.var i).map (Expr.eval rho x) = List.ofFn x := by
    rw [List.map_ofFn]
    rfl
  exact (hh _).trans (congrArg (forcedWires N rho gs) hi)

lemma override_none (j : ℕ) (g : Gate) (ys : List Bool) :
    overrideEval (fun _ => none) j g ys = g.op.eval (g.inputs.map fun w => ys.getD w false) := by
  rcases g with ⟨op,ins⟩
  cases op <;> rfl

lemma forced_none (N : ℕ) (gs : List Gate) (xs : List Bool) :
    forcedWires N (fun _ => none) gs xs = wiresFrom gs xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change forcedWires N (fun _ => none) gs
      (xs ++ [overrideEval (fun _ => none) (xs.length-N) g xs]) = _
    rw [override_none]
    exact ih _

lemma override_trim (rho : ℕ → Option Bool) (j : ℕ) (g : Gate) (ys : List Bool) :
    overrideEval rho j (trim g) ys = overrideEval rho j g ys := by
  rcases g with ⟨op,ins⟩
  cases op <;> cases ins <;> rfl

lemma forced_trim (N : ℕ) (rho : ℕ → Option Bool) (gs : List Gate) (xs : List Bool) :
    forcedWires N rho (gs.map trim) xs = forcedWires N rho gs xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change forcedWires N rho (gs.map trim)
      (xs ++ [overrideEval rho (xs.length-N) (trim g) xs]) = _
    rw [override_trim]
    exact ih _

lemma exprs_eval (N : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, Normal g)
    (rho : ℕ → Option Bool) (x : Fin N → Bool) (w : ℕ) :
    ((exprs N gs).getD w Expr.zero).eval rho x =
      (forcedWires N rho gs (List.ofFn x)).getD w false := by
  have hh := congrArg (fun ys : List Bool => ys.getD w false) (exprs_override N gs hgs rho x)
  change ((exprs N gs).map (Expr.eval rho x)).getD w (Expr.eval rho x (Expr.zero : Expr N)) = _ at hh
  rw [List.getD_map] at hh
  exact hh

lemma notNum_trim (gs : List Gate) : notNum (gs.map trim) = notNum gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hh : isNot (trim g) = isNot g := by rcases g with ⟨op,ins⟩; cases op <;> rfl
    change (if isNot (trim g) then 1 else 0)+notNum (gs.map trim) =
      (if isNot g then 1 else 0)+notNum gs
    rw [hh,ih]

lemma threshold_good {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (A : Fin n → Fin m → Bool) (hrow : Function.Injective A)
    (hcol : Function.Injective (fun j i => A i j)) (C : Circuit)
    (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hrep : PEqualNP.Represents.Represents A C) (hsize : C.size+2 ≤ n+m)
    (hpos : ¬ PEqualNP.Represents.RepSizeAtMost A C.size) :
    let gs := C.gates.map trim
    let e := (exprs (n+m) gs).getD C.output Expr.zero
    (∀ g ∈ gs, Normal g) ∧ e.good ∧ e.bins+1 = C.size ∧ e.negs = 1 ∧
      ∀ rho x, e.eval rho x = (forcedWires (n+m) rho C.gates (List.ofFn x)).getD C.output false := by
  classical
  obtain ⟨hsizeEq,hnot,hcost,t,ht⟩ := threshold hn hm A hrow hcol C hC hrep hsize hpos
  let gs := C.gates.map trim
  let e := (exprs (n+m) gs).getD C.output Expr.zero
  have hsat : cost (C.gates.map trim)+notNum C.gates = C.gates.length := by
    rw [hnot]
    exact hcost
  have hng : ∀ g ∈ C.gates, Normal (trim g) := saturated C.gates hC hsat
  have hgs : ∀ g ∈ gs, Normal g := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact hng a ha
  let D : Circuit := ⟨gs,C.output⟩
  have hrepD : PEqualNP.Represents.Represents A D := by
    intro u v
    change (wiresFrom (C.gates.map trim) _).getD C.output false = _
    rw [trim_wires]
    exact hrep u v
  have hs := profile_support (by omega : 0 < n) (by omega : 0 < m) A hrow hcol D hrepD
  have hb := cnt_cost gs 0 (inputSupps (n+m)) cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hb
  have hcostN : cost gs+1 = n+m-2 := by
    calc
      cost gs+1 = C.size := hcost
      _ = n+m-2 := by omega
  have hcard : ((suppsFrom gs (inputSupps (n+m))).getD C.output ∅).card = cost gs+1 := by
    change n+m-2 ≤ ((suppsFrom gs (inputSupps (n+m))).getD C.output ∅).card at hs
    change ((suppsFrom gs (inputSupps (n+m))).getD C.output ∅).card ≤ cost gs+1 at hb
    exact Nat.le_antisymm hb (by rw [hcostN]; exact hs)
  have hmax : (joint (exprs (n+m) gs) {C.output}).card = cost gs+({C.output} : Finset ℕ).card := by
    simp only [joint, Finset.singleton_biUnion, Finset.card_singleton]
    rw [← expr_getD_supp, exprs_support gs hgs]
    exact hcard
  have hf := forest_tight gs hgs {C.output} hmax
  have heg : e.good := hf.1 C.output (by simp)
  have heb : e.bins = cost gs := by simpa only [Finset.sum_singleton] using hf.2.2.1
  have hen : e.negs ≤ 1 := by
    have hh := hf.2.2.2
    simpa only [Finset.sum_singleton, gs, notNum_trim, hnot] using hh
  have hecost : e.bins+1 = C.size := by rw [heb]; exact hcost
  have hev : ∀ rho x, e.eval rho x = (forcedWires (n+m) rho C.gates (List.ofFn x)).getD C.output false := by
    intro rho x
    change ((exprs (n+m) gs).getD C.output Expr.zero).eval rho x = _
    rw [exprs_eval (n+m) gs hgs, forced_trim]
  have hstd : ∀ x, e.eval (fun _ => none) x = C.eval (List.ofFn x) := by
    intro x
    rw [hev, forced_none]
    rfl
  have hne : e.negs ≠ 0 := by
    intro hzero
    apply hpos
    refine ⟨compiled e, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨hop,hlen⟩ := e.compile_binary heg hzero (n+m) g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, by omega⟩
    · change (e.compile (n+m)).1.length ≤ C.size
      rw [e.compile_length, e.good_nodes heg, hzero, Nat.add_zero]
      omega
    · intro u v
      let x := Fin.append (fun i : Fin n => decide (i=u)) (fun j : Fin m => decide (j=v))
      have hx : List.ofFn x = PEqualNP.Represents.oneEach u v := List.ofFn_fin_append _ _
      rw [← hx, compiled_eval, hstd, hx]
      exact hrep u v
  have hn1 : e.negs = 1 := Nat.le_antisymm hen (Nat.pos_of_ne_zero hne)
  exact ⟨hgs,heg,hecost,hn1,hev⟩

def Expr.up {N : ℕ} : Expr N → Expr (N+1)
  | .var i => .var i.castSucc
  | .zero => .zero
  | .val j b => .val j b
  | .conj j a b => .conj j a.up b.up
  | .disj j a b => .disj j a.up b.up
  | .neg j a => .neg j a.up

lemma Expr.up_bins {N : ℕ} (e : Expr N) : e.up.bins = e.bins := by
  induction e <;> simp [Expr.up, Expr.bins, *]

lemma Expr.up_negs {N : ℕ} (e : Expr N) : e.up.negs = e.negs := by
  induction e <;> simp [Expr.up, Expr.negs, *]

lemma Expr.up_supp {N : ℕ} (e : Expr N) : e.up.supp = e.supp.image Fin.castSucc := by
  induction e <;> simp [Expr.up, Expr.supp, Finset.image_union, *]

lemma Expr.up_eval {N : ℕ} (e : Expr N) (rho : ℕ → Option Bool) (x : Fin N → Bool) (a : Bool) :
    e.up.eval rho (Fin.snoc x a) = e.eval rho x := by
  induction e <;> simp [Expr.up, Expr.eval, Fin.snoc_castSucc, *]

def oldSupp {N : ℕ} (e : Expr (N+1)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => i.castSucc ∈ e.supp)

lemma mem_oldSupp {N : ℕ} (e : Expr (N+1)) (i : Fin N) :
    i ∈ oldSupp e ↔ i.castSucc ∈ e.supp := by simp [oldSupp]

lemma oldSupp_up {N : ℕ} (e : Expr N) : oldSupp e.up = e.supp := by
  classical
  ext i
  rw [mem_oldSupp, Expr.up_supp]
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
    have hjv : j = i := Fin.ext (congrArg (fun k : Fin (N+1) => k.val) he)
    subst j
    exact hj
  · intro hi
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩

lemma oldSupp_conj {N : ℕ} (j : ℕ) (a b : Expr (N+1)) :
    oldSupp (.conj j a b) = oldSupp a ∪ oldSupp b := by
  ext i
  simp [oldSupp, Expr.supp]

lemma oldSupp_disj {N : ℕ} (j : ℕ) (a b : Expr (N+1)) :
    oldSupp (.disj j a b) = oldSupp a ∪ oldSupp b := by
  ext i
  simp [oldSupp, Expr.supp]

lemma oldSupp_hole (N : ℕ) : oldSupp (Expr.var (Fin.last N)) = ∅ := by
  ext i
  simp [oldSupp, Expr.supp]

lemma Expr.eval_no_negs {N : ℕ} (e : Expr N) : e.negs = 0 →
    ∀ rho x, e.eval rho x = e.eval (fun _ => none) x := by
  induction e with
  | var i => intros; rfl
  | zero => intros; rfl
  | val j b => simp [Expr.negs]
  | conj j a b iha ihb =>
    intro hn rho x
    have ha : a.negs = 0 := by change a.negs+b.negs = 0 at hn; omega
    have hb : b.negs = 0 := by change a.negs+b.negs = 0 at hn; omega
    simp only [Expr.eval, iha ha, ihb hb]
  | disj j a b iha ihb =>
    intro hn rho x
    have ha : a.negs = 0 := by change a.negs+b.negs = 0 at hn; omega
    have hb : b.negs = 0 := by change a.negs+b.negs = 0 at hn; omega
    simp only [Expr.eval, iha ha, ihb hb]
  | neg j a iha => simp [Expr.negs]

def rhoAt (t : ℕ) (a : Bool) : ℕ → Option Bool := fun j => if j=t then some a else none

inductive CutAt {N : ℕ} (t : ℕ) (H : Expr N) : Expr N → Expr (N+1) → Prop
  | here (hn : H.negs = 0) : CutAt t H (.neg t H) (.var (Fin.last N))
  | conjL {j : ℕ} {a b : Expr N} {D : Expr (N+1)}
      (hc : CutAt t H a D) (hn : b.negs = 0) : CutAt t H (.conj j a b) (.conj j D b.up)
  | conjR {j : ℕ} {a b : Expr N} {D : Expr (N+1)}
      (hn : a.negs = 0) (hc : CutAt t H b D) : CutAt t H (.conj j a b) (.conj j a.up D)
  | disjL {j : ℕ} {a b : Expr N} {D : Expr (N+1)}
      (hc : CutAt t H a D) (hn : b.negs = 0) : CutAt t H (.disj j a b) (.disj j D b.up)
  | disjR {j : ℕ} {a b : Expr N} {D : Expr (N+1)}
      (hn : a.negs = 0) (hc : CutAt t H b D) : CutAt t H (.disj j a b) (.disj j a.up D)

lemma exists_cut {N : ℕ} (e : Expr N) : e.good → e.negs = 1 →
    ∃ t H D, CutAt t H e D := by
  induction e with
  | var i => intro h hn; simp [Expr.negs] at hn
  | zero => intro h; exact False.elim h
  | val j b => intro h; exact False.elim h
  | neg j a iha =>
    intro h hn
    have ha : a.negs = 0 := by change a.negs+1 = 1 at hn; omega
    exact ⟨j,a,.var (Fin.last N),CutAt.here ha⟩
  | conj j a b iha ihb =>
    intro h hn
    obtain ⟨ha,hb,hd⟩ := h
    change a.negs+b.negs = 1 at hn
    by_cases hna : a.negs = 1
    · have hnb : b.negs = 0 := by omega
      obtain ⟨t,H,D,hc⟩ := iha ha hna
      exact ⟨t,H,.conj j D b.up,CutAt.conjL hc hnb⟩
    · have hna0 : a.negs = 0 := by omega
      have hnb : b.negs = 1 := by omega
      obtain ⟨t,H,D,hc⟩ := ihb hb hnb
      exact ⟨t,H,.conj j a.up D,CutAt.conjR hna0 hc⟩
  | disj j a b iha ihb =>
    intro h hn
    obtain ⟨ha,hb,hd⟩ := h
    change a.negs+b.negs = 1 at hn
    by_cases hna : a.negs = 1
    · have hnb : b.negs = 0 := by omega
      obtain ⟨t,H,D,hc⟩ := iha ha hna
      exact ⟨t,H,.disj j D b.up,CutAt.disjL hc hnb⟩
    · have hna0 : a.negs = 0 := by omega
      have hnb : b.negs = 1 := by omega
      obtain ⟨t,H,D,hc⟩ := ihb hb hnb
      exact ⟨t,H,.disj j a.up D,CutAt.disjR hna0 hc⟩

lemma CutAt.counts {N t : ℕ} {H e : Expr N} {D : Expr (N+1)} (hc : CutAt t H e D) :
    H.negs = 0 ∧ D.negs = 0 ∧ H.bins+D.bins = e.bins := by
  induction hc <;> simp_all [Expr.negs, Expr.bins, Expr.up_bins, Expr.up_negs] <;> omega

lemma CutAt.hole {N t : ℕ} {H e : Expr N} {D : Expr (N+1)} (hc : CutAt t H e D) :
    Fin.last N ∈ D.supp := by
  induction hc <;> simp_all [Expr.supp]

lemma CutAt.eval {N t : ℕ} {H e : Expr N} {D : Expr (N+1)} (hc : CutAt t H e D)
    (x : Fin N → Bool) (a : Bool) :
    D.eval (fun _ => none) (Fin.snoc x a) = e.eval (rhoAt t a) x := by
  induction hc <;> simp_all [Expr.eval, Expr.up_eval, Expr.eval_no_negs, rhoAt, Fin.snoc_last]

lemma CutAt.standard_eval {N t : ℕ} {H e : Expr N} {D : Expr (N+1)} (hc : CutAt t H e D)
    (x : Fin N → Bool) :
    D.eval (fun _ => none) (Fin.snoc x (!(H.eval (fun _ => none) x))) = e.eval (fun _ => none) x := by
  induction hc <;> simp_all [Expr.eval, Expr.up_eval, Fin.snoc_last]

lemma cast_disjoint {N : ℕ} {A B : Finset (Fin N)} (h : Disjoint A B) :
    Disjoint (A.image Fin.castSucc) (B.image Fin.castSucc) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hj
  have hab : b = a := Fin.ext (congrArg (fun k : Fin (N+1) => k.val) he)
  subst b
  exact Finset.disjoint_left.mp h ha hb

lemma Expr.up_good {N : ℕ} (e : Expr N) (hg : e.good) : e.up.good := by
  induction e with
  | var i => trivial
  | zero => exact False.elim hg
  | val j b => exact False.elim hg
  | conj j a b iha ihb =>
    obtain ⟨ha,hb,hd⟩ := hg
    refine ⟨iha ha,ihb hb,?_⟩
    rw [Expr.up_supp,Expr.up_supp]
    exact cast_disjoint hd
  | disj j a b iha ihb =>
    obtain ⟨ha,hb,hd⟩ := hg
    refine ⟨iha ha,ihb hb,?_⟩
    rw [Expr.up_supp,Expr.up_supp]
    exact cast_disjoint hd
  | neg j a iha => exact iha hg

lemma attach_left {N : ℕ} (H a b : Expr N) (D : Expr (N+1))
    (ih : H.good ∧ D.good ∧ Disjoint H.supp (oldSupp D) ∧ a.supp = H.supp ∪ oldSupp D)
    (ha : a.good) (hb : b.good) (hd : Disjoint a.supp b.supp) :
    H.good ∧ (D.good ∧ b.up.good ∧ Disjoint D.supp b.up.supp) ∧
    Disjoint H.supp (oldSupp D ∪ b.supp) ∧
    a.supp ∪ b.supp = H.supp ∪ (oldSupp D ∪ b.supp) := by
  classical
  obtain ⟨hH,hD,hDis,hPart⟩ := ih
  have hHsub : H.supp ⊆ a.supp := by
    intro i hi
    rw [hPart]
    exact Finset.mem_union_left _ hi
  have hDsub : oldSupp D ⊆ a.supp := by
    intro i hi
    rw [hPart]
    exact Finset.mem_union_right _ hi
  have hNew : Disjoint D.supp b.up.supp := by
    apply Finset.disjoint_left.mpr
    intro i hiD hib
    rw [Expr.up_supp] at hib
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hib
    have hko : k ∈ oldSupp D := (mem_oldSupp D k).mpr hiD
    exact Finset.disjoint_left.mp hd (hDsub hko) hk
  refine ⟨hH,⟨hD,b.up_good hb,hNew⟩,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro i hiH hiNew
    rcases Finset.mem_union.mp hiNew with hiD | hib
    · exact Finset.disjoint_left.mp hDis hiH hiD
    · exact Finset.disjoint_left.mp hd (hHsub hiH) hib
  · rw [hPart, Finset.union_assoc]

lemma attach_right {N : ℕ} (H a b : Expr N) (D : Expr (N+1))
    (ih : H.good ∧ D.good ∧ Disjoint H.supp (oldSupp D) ∧ b.supp = H.supp ∪ oldSupp D)
    (ha : a.good) (hb : b.good) (hd : Disjoint a.supp b.supp) :
    H.good ∧ (a.up.good ∧ D.good ∧ Disjoint a.up.supp D.supp) ∧
    Disjoint H.supp (a.supp ∪ oldSupp D) ∧
    a.supp ∪ b.supp = H.supp ∪ (a.supp ∪ oldSupp D) := by
  obtain ⟨hH,⟨hD,hA,hDis⟩,hNo,hPart⟩ := attach_left H b a D ih hb ha hd.symm
  refine ⟨hH,⟨hA,hD,hDis.symm⟩,?_,?_⟩
  · simpa only [Finset.union_comm] using hNo
  · rw [Finset.union_comm a.supp b.supp, hPart]
    rw [Finset.union_comm (oldSupp D) a.supp]

lemma CutAt.good_support {N t : ℕ} {H e : Expr N} {D : Expr (N+1)} (hc : CutAt t H e D) :
    e.good → H.good ∧ D.good ∧ Disjoint H.supp (oldSupp D) ∧ e.supp = H.supp ∪ oldSupp D := by
  induction hc with
  | here hn => intro hg; simpa [Expr.good, Expr.supp, oldSupp_hole] using hg
  | @conjL j a b D hc hn ih =>
    intro hg
    obtain ⟨ha,hb,hd⟩ := hg
    simpa only [Expr.good, Expr.supp, oldSupp_conj, oldSupp_up] using attach_left H a b D (ih ha) ha hb hd
  | @conjR j a b D hn hc ih =>
    intro hg
    obtain ⟨ha,hb,hd⟩ := hg
    simpa only [Expr.good, Expr.supp, oldSupp_conj, oldSupp_up] using attach_right H a b D (ih hb) ha hb hd
  | @disjL j a b D hc hn ih =>
    intro hg
    obtain ⟨ha,hb,hd⟩ := hg
    simpa only [Expr.good, Expr.supp, oldSupp_disj, oldSupp_up] using attach_left H a b D (ih ha) ha hb hd
  | @disjR j a b D hn hc ih =>
    intro hg
    obtain ⟨ha,hb,hd⟩ := hg
    simpa only [Expr.good, Expr.supp, oldSupp_disj, oldSupp_up] using attach_right H a b D (ih hb) ha hb hd

def Expr.Shape {N : ℕ} (e : Expr N) (t : ℕ) (H : Expr N) : Prop :=
  match e with
  | .var _ => True
  | .zero => True
  | .val j _ => j=t
  | .conj _ a b => a.Shape t H ∧ b.Shape t H
  | .disj _ a b => a.Shape t H ∧ b.Shape t H
  | .neg j a => j=t ∧ a=H

lemma CutAt.shape {N j t : ℕ} {K H e : Expr N} {D : Expr (N+1)} (hc : CutAt j K e D) :
    e.Shape t H → j=t ∧ K=H := by
  induction hc <;> simp_all [Expr.Shape]

lemma expr_getD_property {N : ℕ} (P : Expr N → Prop) (hz : P Expr.zero)
    (L : List (Expr N)) (hL : ∀ e ∈ L, P e) (w : ℕ) : P (L.getD w Expr.zero) := by
  induction L generalizing w with
  | nil => exact hz
  | cons a L ih =>
    cases w with
    | zero => exact hL a (by simp)
    | succ w => exact ih (fun e he => hL e (List.mem_cons_of_mem _ he)) w

lemma shape_apply {N : ℕ} (t : ℕ) (H : Expr N) (j : ℕ) (g : Gate)
    (hg : Normal g) (hn : g.op ≠ .not) (L : List (Expr N))
    (hL : ∀ e ∈ L, e.Shape t H) : (applyExpr j g L).Shape t H := by
  have hh (w : ℕ) : (L.getD w Expr.zero).Shape t H :=
    expr_getD_property (fun e => e.Shape t H) True.intro L hL w
  rcases normal_cases g hg with ⟨a,b,rfl⟩ | ⟨a,b,rfl⟩ | rfl | ⟨a,rfl⟩
  · exact ⟨hh a,hh b⟩
  · exact ⟨hh a,hh b⟩
  · exact False.elim (hn rfl)
  · exact False.elim (hn rfl)

lemma shape_fold {N : ℕ} (t : ℕ) (H : Expr N) (gs : List Gate)
    (hgs : ∀ g ∈ gs, Normal g ∧ g.op ≠ .not) :
    ∀ L : List (Expr N), (∀ e ∈ L, e.Shape t H) →
      ∀ e ∈ gs.foldl exprStep L, e.Shape t H := by
  induction gs with
  | nil => intro L hL; exact hL
  | cons g gs ih =>
    intro L hL
    apply ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) (exprStep L g)
    intro e he
    simp only [exprStep, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hL e he
    · exact shape_apply t H _ g (hgs g List.mem_cons_self).1 (hgs g List.mem_cons_self).2 L hL

lemma shape_exprs_noNot (N t : ℕ) (H : Expr N) (gs : List Gate)
    (hgs : ∀ g ∈ gs, Normal g ∧ g.op ≠ .not) :
    ∀ e ∈ exprs N gs, e.Shape t H := by
  apply shape_fold t H gs hgs
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  trivial

lemma exprs_shape (N : ℕ) (pre post : List Gate) (ins : List ℕ) (df : ℕ)
    (hp : ∀ g ∈ pre, Normal g ∧ g.op ≠ .not)
    (hq : ∀ g ∈ post, Normal g ∧ g.op ≠ .not) :
    let H := (exprs N pre).getD (ins.headD df) Expr.zero
    ∀ e ∈ exprs N (pre ++ ⟨.not,ins⟩ :: post), e.Shape pre.length H := by
  dsimp only
  have hfold : exprs N (pre ++ ⟨.not,ins⟩ :: post) =
      post.foldl exprStep (exprStep (exprs N pre) ⟨.not,ins⟩) := by
    simp only [exprs, List.foldl_append, List.foldl_cons]
  rw [hfold]
  apply shape_fold pre.length _ post hq
  intro e he
  simp only [exprStep, List.mem_append, List.mem_singleton] at he
  rcases he with he | rfl
  · exact shape_exprs_noNot N pre.length _ pre hp e he
  · have hj : (exprs N pre).length-N = pre.length := by rw [exprs_length]; omega
    cases ins with
    | nil => simpa only [applyExpr, Expr.Shape, hj]
    | cons a rest => simp only [applyExpr, Expr.Shape, hj, List.headD_cons, and_self]

lemma trim_head (g : Gate) (df : ℕ) : (trim g).inputs.headD df = g.inputs.headD df := by
  rcases g with ⟨op,ins⟩
  cases op <;> cases ins <;> rfl

lemma split_at (gs : List Gate) (t : Fin gs.length) :
    gs = gs.take t.val ++ gs.get t :: gs.drop (t.val+1) := by
  calc
    gs = gs.take (t.val+1) ++ gs.drop (t.val+1) := by simp
    _ = (gs.take t.val ++ [gs.get t]) ++ gs.drop (t.val+1) := by
      rw [← List.take_concat_get' gs t.val t.isLt]
      rfl
    _ = gs.take t.val ++ gs.get t :: gs.drop (t.val+1) := by simp

lemma gateAt_get (C : Circuit) (t : Fin C.size) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C t.val = C.gates.get t :=
  List.getD_eq_get _ _ _

def notFactory (N : ℕ) (C : Circuit) (t : Fin C.size) : Expr N :=
  (exprs N ((C.gates.take t.val).map trim)).getD
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C t.val).inputs.headD (N+C.size)) Expr.zero

lemma source_shape (N : ℕ) (C : Circuit)
    (hN : ∀ g ∈ C.gates.map trim, Normal g) (hn : notNum C.gates = 1)
    (t : Fin C.size) (ht : (PEqualNP.MetaComplexity.NestedCover.gateAt C t.val).op = .not) :
    ((exprs N (C.gates.map trim)).getD C.output Expr.zero).Shape t.val (notFactory N C t) := by
  classical
  let pre := C.gates.take t.val
  let post := C.gates.drop (t.val+1)
  let g0 := C.gates.get t
  have hsplit : C.gates = pre ++ g0 :: post := split_at C.gates t
  have hop : g0.op = .not := by rw [gateAt_get] at ht; exact ht
  have hnum : notNum pre+1+notNum post = 1 := by
    rw [hsplit,notNum_append,notNum] at hn
    have hh := (isNot_iff g0).mpr hop
    simpa [hh,Nat.add_assoc] using hn
  have hpre0 : notNum pre = 0 := by omega
  have hpost0 : notNum post = 0 := by omega
  have hp : ∀ g ∈ pre.map trim, Normal g ∧ g.op ≠ .not := by
    intro g hg
    constructor
    · apply hN g
      rw [hsplit,List.map_append,List.map_cons]
      exact List.mem_append_left _ hg
    · intro he
      have hh := notNum_pos ⟨g,hg,he⟩
      rw [notNum_trim,hpre0] at hh
      omega
  have hq : ∀ g ∈ post.map trim, Normal g ∧ g.op ≠ .not := by
    intro g hg
    constructor
    · apply hN g
      rw [hsplit,List.map_append,List.map_cons]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg)
    · intro he
      have hh := notNum_pos ⟨g,hg,he⟩
      rw [notNum_trim,hpost0] at hh
      omega
  let ins := (trim g0).inputs
  have htrim : trim g0 = ⟨.not,ins⟩ := by
    change (⟨g0.op,ins⟩ : Gate) = ⟨.not,ins⟩
    rw [hop]
  have hgs : C.gates.map trim = pre.map trim ++ ⟨.not,ins⟩ :: post.map trim := by
    rw [hsplit,List.map_append,List.map_cons,htrim]
  let F := (exprs N (pre.map trim)).getD (ins.headD (N+C.size)) Expr.zero
  have hh := exprs_shape N (pre.map trim) (post.map trim) ins (N+C.size) hp hq
  have hr := expr_getD_property (fun e => e.Shape (pre.map trim).length F) True.intro _ hh C.output
  rw [← hgs] at hr
  have hlen : (pre.map trim).length = t.val := by
    have hlt : t.val < C.gates.length := t.isLt
    simp [pre,List.length_take,Nat.min_eq_left hlt.le]
  have hF : F = notFactory N C t := by
    change (exprs N (pre.map trim)).getD ((trim g0).inputs.headD (N+C.size)) Expr.zero = _
    rw [trim_head]
    unfold notFactory
    rw [gateAt_get]
  rw [hlen,hF] at hr
  exact hr

lemma notFactory_earlier (N : ℕ) (C : Circuit) (t : Fin C.size)
    (hF : (notFactory N C t).good) :
    (PEqualNP.MetaComplexity.NestedCover.gateAt C t.val).inputs.headD (N+C.size) < N+t.val := by
  have hlen : (exprs N ((C.gates.take t.val).map trim)).length = N+t.val := by
    have ht : t.val < C.gates.length := t.isLt
    simp [exprs_length,List.length_take,Nat.min_eq_left ht.le]
  by_contra hh
  have hz : notFactory N C t = Expr.zero := by
    unfold notFactory
    rw [List.getD_eq_default _ _ (by rw [hlen]; omega)]
  rw [hz] at hF
  exact hF

lemma notFactory_eval (N : ℕ) (C : Circuit) (t : Fin C.size)
    (hN : ∀ g ∈ C.gates.map trim, Normal g) (hF : (notFactory N C t).good)
    (x : Fin N → Bool) :
    (notFactory N C t).eval (fun _ => none) x =
      (C.wires (List.ofFn x)).getD
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C t.val).inputs.headD (N+C.size)) false := by
  let pre := C.gates.take t.val
  let post := C.gates.drop t.val
  let w := (PEqualNP.MetaComplexity.NestedCover.gateAt C t.val).inputs.headD (N+C.size)
  have hp : ∀ g ∈ pre.map trim, Normal g := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact hN _ (List.mem_map.mpr ⟨a,List.mem_of_mem_take ha,rfl⟩)
  have he := exprs_eval N (pre.map trim) hp (fun _ => none) x w
  rw [forced_none,trim_wires] at he
  have hFull : wiresFrom C.gates (List.ofFn x) =
      wiresFrom post (wiresFrom pre (List.ofFn x)) := by
    calc
      wiresFrom C.gates (List.ofFn x) = wiresFrom (pre ++ post) (List.ofFn x) := by
        apply congrArg (fun gs => wiresFrom gs (List.ofFn x))
        dsimp [pre,post]
        simp
      _ = wiresFrom post (wiresFrom pre (List.ofFn x)) := wiresFrom_append _ _ _
  have hEarly := notFactory_earlier N C t hF
  have hprelen : pre.length = t.val := by
    have ht : t.val < C.gates.length := t.isLt
    simp [pre,List.length_take,Nat.min_eq_left ht.le]
  change ((exprs N (pre.map trim)).getD w Expr.zero).eval (fun _ => none) x =
    (wiresFrom C.gates (List.ofFn x)).getD w false
  rw [he,hFull,getD_wiresFrom post (wiresFrom pre (List.ofFn x)) w
    (by rw [length_wiresFrom,List.length_ofFn,hprelen]; exact hEarly)]

lemma Expr.good_card {N : ℕ} (e : Expr N) : e.good → e.supp.card = e.bins+1 := by
  induction e with
  | var i => simp [Expr.good,Expr.supp,Expr.bins]
  | zero => simp [Expr.good]
  | val j b => simp [Expr.good]
  | neg j a ih => exact ih
  | conj j a b ia ib | disj j a b ia ib =>
    intro h
    obtain ⟨ha,hb,hd⟩ := h
    simp only [Expr.supp,Expr.bins,Finset.card_union_of_disjoint hd,ia ha,ib hb]
    omega

lemma Expr.agree {N : ℕ} (e : Expr N) (rho : ℕ → Option Bool) (x y : Fin N → Bool)
    (h : ∀ i ∈ e.supp, x i = y i) : e.eval rho x = e.eval rho y := by
  induction e with
  | var i => exact h i (by simp [Expr.supp])
  | zero | val j b => rfl
  | neg j a ih => simp only [Expr.eval,ih h]
  | conj j a b ia ib | disj j a b ia ib =>
    have ha := ia (fun i hi => h i (Finset.mem_union_left _ hi))
    have hb := ib (fun i hi => h i (Finset.mem_union_right _ hi))
    simp only [Expr.eval,ha,hb]

lemma Expr.mono {N : ℕ} (e : Expr N) (hn : e.negs = 0) (x y : Fin N → Bool)
    (h : ∀ i ∈ e.supp, x i = true → y i = true) :
    e.eval (fun _ => none) x = true → e.eval (fun _ => none) y = true := by
  induction e with
  | var i => exact h i (by simp [Expr.supp])
  | zero => simp [Expr.eval]
  | val j b => simp [Expr.negs] at hn
  | neg j a ih => simp [Expr.negs] at hn
  | conj j a b ia ib | disj j a b ia ib =>
    have ha : a.negs = 0 := by change a.negs+b.negs=0 at hn; omega
    have hb : b.negs = 0 := by change a.negs+b.negs=0 at hn; omega
    have hma := ia ha (fun i hi => h i (Finset.mem_union_left _ hi))
    have hmb := ib hb (fun i hi => h i (Finset.mem_union_right _ hi))
    simp only [Expr.eval,Bool.and_eq_true,Bool.or_eq_true]
    tauto

def forceAt (N t : ℕ) (a : Bool) (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun ys g => ys ++ [if ys.length=N+t then a else
    g.op.eval (g.inputs.map fun w => ys.getD w false)]) xs

lemma forced_one (N t k : ℕ) (a : Bool) (gs : List Gate) (xs : List Bool)
    (hlen : xs.length = N+k)
    (ht : ∀ j : Fin gs.length, k+j.val=t → (gs.get j).op=.not) :
    forcedWires N (rhoAt t a) gs xs = forceAt N t a gs xs := by
  induction gs generalizing k xs with
  | nil => rfl
  | cons g gs ih =>
    have hh : overrideEval (rhoAt t a) (xs.length-N) g xs =
        if xs.length=N+t then a else g.op.eval (g.inputs.map fun w => xs.getD w false) := by
      have hsub : xs.length-N=k := by omega
      rw [hsub]
      by_cases hk : k=t
      · have hop : g.op=.not := ht ⟨0,by simp⟩ (by simpa using hk)
        simp [overrideEval,rhoAt,hop,hk,hlen]
      · have hne : xs.length ≠ N+t := by omega
        cases hop : g.op <;> simp [overrideEval,rhoAt,hk,hne,hop]
    change forcedWires N (rhoAt t a) gs (xs ++ [overrideEval (rhoAt t a) (xs.length-N) g xs]) = _
    rw [hh]
    apply ih (k+1)
    · simp only [List.length_append,List.length_singleton]; omega
    · intro j hj
      exact ht ⟨j.val+1,by simpa using j.isLt⟩ (by change k+(j.val+1)=t; omega)

lemma omitted_profiles {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (A : Fin n → Fin m → Bool) (hrow : Function.Injective A)
    (hcol : Function.Injective (fun j i => A i j)) (e : Expr (n+m))
    (hrep : ∀ u v, e.eval (fun _ => none)
      (Fin.append (fun i : Fin n => decide (i=u)) (fun j : Fin m => decide (j=v))) = A u v)
    (hsmall : e.supp.card ≤ n+m-2) :
    ∃ r : Fin n, ∃ c : Fin m,
      r.castAdd m ∉ e.supp ∧ c.natAdd n ∉ e.supp ∧
      (∀ i, i ≠ r → i.castAdd m ∈ e.supp) ∧
      (∀ j, j ≠ c → j.natAdd n ∈ e.supp) ∧
      (∀ i, i.castAdd m ∈ e.supp ↔ i ≠ r) ∧
      (∀ j, j.natAdd n ∈ e.supp ↔ j ≠ c) := by
  classical
  let S := e.supp
  let x := fun (u : Fin n) (v : Fin m) =>
    Fin.append (fun i : Fin n => decide (i=u)) (fun j : Fin m => decide (j=v))
  have hx : ∀ u v, List.ofFn (x u v) = PEqualNP.Represents.oneEach u v := by
    intro u v
    exact List.ofFn_fin_append _ _
  have hr : ∀ u v : Fin n, u.castAdd m ∉ S → v.castAdd m ∉ S → u = v := by
    intro u v hu hv
    apply hrow
    funext j
    rw [← hrep u j, ← hrep v j]
    apply e.agree (fun _ => none)
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · intro hi
      have hau : a ≠ u := by intro he; subst a; exact hu hi
      have hav : a ≠ v := by intro he; subst a; exact hv hi
      simp [x, hau, hav]
    · intro _; simp [x]
  have hc : ∀ u v : Fin m, u.natAdd n ∉ S → v.natAdd n ∉ S → u = v := by
    intro u v hu hv
    apply hcol
    funext j
    change A j u = A j v
    rw [← hrep j u, ← hrep j v]
    apply e.agree (fun _ => none)
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · intro _; simp [x]
    · intro hi
      have hbu : b ≠ u := by intro he; subst b; exact hu hi
      have hbv : b ≠ v := by intro he; subst b; exact hv hi
      simp [x, hbu, hbv]
  have rows : ∃ r : Fin n, ∀ i, i ≠ r → i.castAdd m ∈ S := by
    by_cases hh : ∃ r : Fin n, r.castAdd m ∉ S
    · obtain ⟨r, hr0⟩ := hh
      exact ⟨r, fun i hir => by by_contra hi; exact hir (hr i r hi hr0)⟩
    · exact ⟨⟨0, hn⟩, fun i _ => by by_contra hi; exact hh ⟨i,hi⟩⟩
  have cols : ∃ c : Fin m, ∀ j, j ≠ c → j.natAdd n ∈ S := by
    by_cases hh : ∃ c : Fin m, c.natAdd n ∉ S
    · obtain ⟨c, hc0⟩ := hh
      exact ⟨c, fun j hjc => by by_contra hj; exact hjc (hc j c hj hc0)⟩
    · exact ⟨⟨0, hm⟩, fun j _ => by by_contra hj; exact hh ⟨j,hj⟩⟩
  obtain ⟨r, hR⟩ := rows
  obtain ⟨c, hC⟩ := cols
  have hne : r.castAdd m ≠ c.natAdd n := by
    intro he
    have hval := congrArg Fin.val he
    simp at hval
    omega
  have hS : ∀ i : Fin (n+m), i ≠ r.castAdd m → i ≠ c.natAdd n → i ∈ S := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · intro ha _
      exact hR a (fun he => ha (by rw [he]))
    · intro _ hb
      exact hC b (fun he => hb (by rw [he]))
  have hsubset : ((Finset.univ.erase (r.castAdd m)).erase (c.natAdd n)) ⊆ S := by
    intro i hi
    exact hS i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1 (Finset.mem_erase.mp hi).1
  have hcard : ((Finset.univ.erase (r.castAdd m)).erase (c.natAdd n)).card = n+m-2 := by
    rw [Finset.card_erase_of_mem (by simp [hne.symm]), Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
    omega
  have hEq : e.supp = (Finset.univ.erase (r.castAdd m)).erase (c.natAdd n) :=
    (Finset.eq_of_subset_of_card_le hsubset (by rw [hcard]; exact hsmall)).symm
  refine ⟨r,c,?_,?_,?_,?_,?_,?_⟩
  · rw [hEq]; simp
  · rw [hEq]; simp
  · exact hR
  · exact hC
  · intro i
    constructor
    · intro hi he; subst i
      rw [hEq] at hi; simpa using hi
    · exact hR i
  · intro j
    constructor
    · intro hj he; subst j
      rw [hEq] at hj; simpa using hj
    · exact hC j

def cutValue {N : ℕ} (H : Expr N) (D : Expr (N+1)) (x : Fin N → Bool) : Bool :=
  D.eval (fun _ => none) (Fin.snoc x (!(H.eval (fun _ => none) x)))

lemma cutValue_mono {N : ℕ} (H : Expr N) (D : Expr (N+1))
    (hH : H.negs=0) (hD : D.negs=0) (k : Fin N) (x y : Fin N → Bool)
    (hxy : ∀ i, x i=true → y i=true) (heq : ∀ i, i≠k → x i=y i) :
    (k ∉ H.supp → cutValue H D x=true → cutValue H D y=true) ∧
    (k ∉ oldSupp D → cutValue H D y=true → cutValue H D x=true) := by
  constructor
  · intro hk
    have hHeq : H.eval (fun _ => none) x = H.eval (fun _ => none) y :=
      H.agree _ x y (fun i hi => heq i (fun h => hk (h ▸ hi)))
    apply D.mono hD
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> intro hi
    · simpa only [Fin.snoc_last,hHeq] using (fun h => h)
    · simpa only [Fin.snoc_castSucc] using hxy j
  · intro hk
    have hHm := H.mono hH x y (fun i _ => hxy i)
    apply D.mono hD
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> intro hi
    · simp only [Fin.snoc_last]
      cases hx : H.eval (fun _ => none) x <;>
        cases hy : H.eval (fun _ => none) y <;> simp_all
    · have hjk : j ≠ k := by
        intro hj; subst j
        apply hk
        exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
      simpa only [Fin.snoc_castSucc,heq j hjk] using (fun h => h)

lemma profile_partition {N s q : ℕ} (A : Fin s → Fin q → Bool)
    (hinj : Function.Injective A) (p : Fin s → Fin N) (base : Fin q → Fin N → Bool)
    (pts : Fin s → Fin q → Fin N → Bool)
    (hpts : ∀ i j k, pts i j k = if k=p i then true else base j k)
    (e H : Expr N) (D : Expr (N+1)) (hH : H.negs=0) (hD : D.negs=0)
    (hdis : Disjoint H.supp (oldSupp D)) (hsupp : e.supp=H.supp∪oldSupp D)
    (heval : ∀ x, e.eval (fun _ => none) x = cutValue H D x)
    (hrep : ∀ i j, e.eval (fun _ => none) (pts i j)=A i j)
    (r : Fin s) (hr : p r ∉ e.supp) (hall : ∀ i, p i ∈ e.supp ↔ i≠r) :
    ∀ i, let le := fun i k => ∀ j, A i j=true → A k j=true
      (le i r ∨ le r i) ∧
      (p i ∈ H.supp ↔ i≠r ∧ le i r) ∧
      (p i ∈ oldSupp D ↔ i≠r ∧ le r i) := by
  classical
  let le := fun i k => ∀ j, A i j=true → A k j=true
  have hbase (j : Fin q) : e.eval (fun _ => none) (base j)=A r j := by
    rw [← hrep r j]
    apply e.agree
    intro k hk
    have hkr : k≠p r := by intro h; exact hr (h ▸ hk)
    simp [hpts,hkr]
  have hsign (i : Fin s) :
      (p i ∉ H.supp → le r i) ∧ (p i ∉ oldSupp D → le i r) := by
    constructor
    · intro hi j
      have hh := (cutValue_mono H D hH hD (p i) (base j) (pts i j)
        (fun k hk => by rw [hpts]; split_ifs <;> simp_all)
        (fun k hk => by simp [hpts,hk])).1 hi
      rw [← heval,← heval,hbase,hrep] at hh
      exact hh
    · intro hi j
      have hh := (cutValue_mono H D hH hD (p i) (base j) (pts i j)
        (fun k hk => by rw [hpts]; split_ifs <;> simp_all)
        (fun k hk => by simp [hpts,hk])).2 hi
      rw [← heval,← heval,hbase,hrep] at hh
      exact hh
  have antisymm (i : Fin s) (hi : le i r) (hi' : le r i) : i=r := by
    apply hinj
    funext j
    cases hai : A i j <;> cases har : A r j <;> simp_all [le]
  intro i
  change (le i r ∨ le r i) ∧ _
  have hnotboth : ¬ (p i ∈ H.supp ∧ p i ∈ oldSupp D) :=
    fun h => Finset.disjoint_left.mp hdis h.1 h.2
  have hHsign : p i ∈ H.supp → le i r := fun hi =>
    (hsign i).2 (fun hd => hnotboth ⟨hi,hd⟩)
  have hDsign : p i ∈ oldSupp D → le r i := fun hi =>
    (hsign i).1 (fun hh => hnotboth ⟨hh,hi⟩)
  refine ⟨?_,?_,?_⟩
  · by_cases hi : p i ∈ H.supp
    · exact Or.inl (hHsign hi)
    · exact Or.inr ((hsign i).1 hi)
  · constructor
    · intro hi
      exact ⟨(hall i).mp (by rw [hsupp]; exact Finset.mem_union_left _ hi),hHsign hi⟩
    · rintro ⟨hir,hle⟩
      by_contra hi
      exact hir (antisymm i hle ((hsign i).1 hi))
  · constructor
    · intro hi
      exact ⟨(hall i).mp (by rw [hsupp]; exact Finset.mem_union_right _ hi),hDsign hi⟩
    · rintro ⟨hir,hle⟩
      by_contra hi
      exact hir (antisymm i ((hsign i).2 hi) hle)

lemma ofFn_snoc {N : ℕ} (x : Fin N → Bool) (a : Bool) :
    List.ofFn (Fin.snoc x a) = List.ofFn x ++ [a] := by
  rw [List.ofFn_succ_last]
  simp

end PEqualNP.Outside.L_meta_29775

open PEqualNP.Outside.L_meta_29775

theorem PEqualNP.Outside.L_meta_29775 : (∀ (n m : Nat) (A : Fin n → Fin m → Bool),
  2 ≤ n → 2 ≤ m → Function.Injective A → Function.Injective (fun j i => A i j) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  C.size + 2 ≤ n+m → ¬ PEqualNP.Represents.RepSizeAtMost A C.size →
  let N := n+m
  let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
  let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
  let reads := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.NestedCover.readsIn G (Finset.range G.size)
  let use := fun (G : PEqualNP.CircuitLowerBounds.Circuit) (w : Nat) => reads G w + (if G.output = w then 1 else 0)
  let tree := fun (k : Nat) (G : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ G.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack k G ∧ (G.output+1 = k+G.size ∨ (G.size = 0 ∧ G.output < k)) ∧
    (∀ i < k, use G i ≤ 1) ∧ (∀ j < G.size, use G (k+j) = 1)
  ∃ (r : Fin n) (c : Fin m) (t : Fin C.size) (H D : PEqualNP.CircuitLowerBounds.Circuit),
    C.size + 2 = N ∧
    (∀ k : Fin C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C k.val).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ k = t) ∧
    tree N H ∧ tree (N+1) D ∧ H.size+D.size+1 = C.size ∧ use D N = 1 ∧
    (∀ i : Fin n, (rowLE i r ∨ rowLE r i) ∧
      use H i.val = (if i ≠ r ∧ rowLE i r then 1 else 0) ∧
      use D i.val = (if i ≠ r ∧ rowLE r i then 1 else 0)) ∧
    (∀ j : Fin m, (colLE j c ∨ colLE c j) ∧
      use H (n+j.val) = (if j ≠ c ∧ colLE j c then 1 else 0) ∧
      use D (n+j.val) = (if j ≠ c ∧ colLE c j then 1 else 0)) ∧
    ∀ (x : Fin N → Bool) (a : Bool),
      let xs := List.ofFn x
      let forced := C.gates.foldl (fun (ys : List Bool) g =>
        ys ++ [if ys.length = N+t.val then a else g.op.eval (g.inputs.map (fun w => ys.getD w false))]) xs
      H.eval xs = (C.wires xs).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C t.val).inputs.headD (N+C.size)) false ∧
      D.eval (xs++[a]) = forced.getD C.output false) := by
  classical
  intro n m A hn hm hrow hcol C hC hrep hsize hpos
  obtain ⟨hsizeEq,hnot,hcost,t,ht⟩ := threshold hn hm A hrow hcol C hC hrep hsize hpos
  let e := (exprs (n+m) (C.gates.map trim)).getD C.output Expr.zero
  obtain ⟨hN,heg,heb,hen,hev⟩ := threshold_good hn hm A hrow hcol C hC hrep hsize hpos
  change e.good at heg
  change e.bins+1=C.size at heb
  change e.negs=1 at hen
  change ∀ rho x, e.eval rho x = _ at hev
  obtain ⟨j,H,D,hcut⟩ := exists_cut e heg hen
  have htNot := (ht t).mpr rfl
  have hshape := source_shape (n+m) C hN hnot t htNot
  obtain ⟨hjt,hfactory⟩ := hcut.shape hshape
  subst j
  obtain ⟨hHg,hDg,hdis,hsupp⟩ := hcut.good_support heg
  obtain ⟨hHn,hDn,hbins⟩ := hcut.counts
  have hrepe (u : Fin n) (v : Fin m) :
      e.eval (fun _ => none) (Fin.append (fun i : Fin n => decide (i=u))
        (fun j : Fin m => decide (j=v)))=A u v := by
    rw [hev,forced_none,List.ofFn_fin_append]
    exact hrep u v
  have hsmall : e.supp.card ≤ n+m-2 := by
    have hh := e.good_card heg
    omega
  obtain ⟨r,c,hr,hc,_,_,hrows,hcols⟩ := omitted_profiles (by omega) (by omega)
    A hrow hcol e hrepe hsmall
  have heval (x : Fin (n+m) → Bool) : e.eval (fun _ => none) x = cutValue H D x :=
    (hcut.standard_eval x).symm
  have hrowpart := profile_partition A hrow (fun i : Fin n => i.castAdd m)
    (fun v : Fin m => Fin.append (fun _ : Fin n => false) (fun j : Fin m => decide (j=v)))
    (fun u : Fin n => fun v : Fin m => Fin.append (fun i : Fin n => decide (i=u))
      (fun j : Fin m => decide (j=v)))
    (by
      intro u v k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · simp
      · have hne : j.natAdd n ≠ u.castAdd m := by
          intro he
          have hh := congrArg (fun z : Fin (n+m) => z.val) he
          simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
          omega
        simp [hne])
    e H D hHn hDn hdis hsupp heval hrepe r hr hrows
  have hcolpart := profile_partition (fun v u => A u v) hcol (fun j : Fin m => j.natAdd n)
    (fun u : Fin n => Fin.append (fun i : Fin n => decide (i=u)) (fun _ : Fin m => false))
    (fun v : Fin m => fun u : Fin n => Fin.append (fun i : Fin n => decide (i=u))
      (fun j : Fin m => decide (j=v)))
    (by
      intro v u k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · have hne : i.castAdd m ≠ v.natAdd n := by
          intro he
          have hh := congrArg (fun z : Fin (n+m) => z.val) he
          simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
          omega
        simp [hne]
      · simp)
    e H D hHn hDn hdis hsupp heval (fun v u => hrepe u v) c hc hcols
  refine ⟨r,c,t,compiled H,compiled D,hsizeEq,ht,compiled_tree H hHg hHn,
    compiled_tree D hDg hDn,?_,?_,?_,?_,?_⟩
  · change (H.compile (n+m)).1.length+(D.compile (n+m+1)).1.length+1=C.size
    rw [H.compile_length,D.compile_length,H.good_nodes hHg,D.good_nodes hDg,hHn,hDn]
    omega
  · change uses (compiled D) (n+m)=1
    have hh := compiled_input_uses D hDg (Fin.last (n+m))
    simpa only [Fin.val_last,if_pos hcut.hole] using hh
  · intro i
    obtain ⟨hcompare,hleft,hright⟩ := hrowpart i
    refine ⟨hcompare,?_,?_⟩
    · change uses (compiled H) i.val=_
      simpa only [Fin.val_castAdd,hleft] using compiled_input_uses H hHg (i.castAdd m)
    · change uses (compiled D) i.val=_
      have hh : (i.castAdd m).castSucc ∈ D.supp ↔ i.castAdd m ∈ oldSupp D := by simp [oldSupp]
      simpa only [Fin.val_castSucc,Fin.val_castAdd,Fin.val_natAdd,hh,hright] using
        compiled_input_uses D hDg (i.castAdd m).castSucc
  · intro j
    obtain ⟨hcompare,hleft,hright⟩ := hcolpart j
    refine ⟨hcompare,?_,?_⟩
    · change uses (compiled H) (n+j.val)=_
      simpa only [Fin.val_natAdd,hleft] using compiled_input_uses H hHg (j.natAdd n)
    · change uses (compiled D) (n+j.val)=_
      have hh : (j.natAdd n).castSucc ∈ D.supp ↔ j.natAdd n ∈ oldSupp D := by simp [oldSupp]
      simpa only [Fin.val_castSucc,Fin.val_castAdd,Fin.val_natAdd,hh,hright] using
        compiled_input_uses D hDg (j.natAdd n).castSucc
  · intro x a
    constructor
    · rw [compiled_eval,hfactory]
      exact notFactory_eval (n+m) C t hN (hfactory ▸ hHg) x
    · change (compiled D).eval (List.ofFn x++[a]) = (forceAt (n+m) t.val a C.gates (List.ofFn x)).getD C.output false
      rw [← ofFn_snoc,compiled_eval,hcut.eval,hev]
      rw [forced_one (n+m) t.val 0 a C.gates (List.ofFn x) (by simp)]
      intro k hk
      have hkt : k=t := Fin.ext (by simpa using hk)
      subst k
      rw [← gateAt_get]
      exact htNot
