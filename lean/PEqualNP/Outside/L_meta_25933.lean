import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_25933_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

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

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
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
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
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

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

end PEqualNP.MetaComplexity.Helpers

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

theorem gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'

theorem two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

theorem drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

end PEqualNP.MetaComplexity.Helpers
namespace PEqualNP.MetaComplexity.Helpers.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end PEqualNP.MetaComplexity.Helpers.PermInputs
namespace PEqualNP.MetaComplexity.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b

def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))

def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)

def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)

def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q

structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

section LocalSection1

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

theorem Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega

theorem Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega
end LocalSection1
end PEqualNP.MetaComplexity.Helpers.Readers
namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs

theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b]) : a ≠ b := by
  rintro rfl
  have hcl := L.hcl p g hg
  have hlt : a < m + p := by
    rcases hcl with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, hj, hk, h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [vl_gate gs L.hcl u p g hg, hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]

theorem pq2f_ne_pair {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b] ∨ g.inputs = [b, a]) : a ≠ b := by
  rcases hin with h | h
  · exact pq2f_nodup L hnc hg hop h
  · exact (pq2f_nodup L hnc hg hop h).symm

end PEqualNP.MetaComplexity.Helpers.RunAsm
end PEqualNP.Outside.L_meta_25933_aux


namespace PEqualNP.Outside.L_meta_25933_aux
def pm (x : Fin 9 → Bool) : Bool := (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

structure Symmetry where
  run : Fin 9 → Fin 9
  preserves : ∀ x : Fin 9 → Bool, pm (x ∘ run) = pm x

private def sym0 : Symmetry where
  run := ![0, 1, 2, 3, 4, 5, 6, 7, 8]
  preserves := by
    intro x
    change ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym2 : Symmetry where
  run := ![0, 2, 1, 3, 5, 4, 6, 8, 7]
  preserves := by
    intro x
    change ((x 0 && x 5 && x 7) || (x 0 && x 4 && x 8) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym1 : Symmetry where
  run := ![0, 3, 6, 1, 4, 7, 2, 5, 8]
  preserves := by
    intro x
    change ((x 0 && x 4 && x 8) || (x 0 && x 7 && x 5) || (x 3 && x 1 && x 8) || (x 3 && x 7 && x 2) || (x 6 && x 1 && x 5) || (x 6 && x 4 && x 2)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym13 : Symmetry where
  run := ![0, 3, 6, 2, 5, 8, 1, 4, 7]
  preserves := by
    intro x
    change ((x 0 && x 5 && x 7) || (x 0 && x 8 && x 4) || (x 3 && x 2 && x 7) || (x 3 && x 8 && x 1) || (x 6 && x 2 && x 4) || (x 6 && x 5 && x 1)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym12 : Symmetry where
  run := ![0, 1, 2, 6, 7, 8, 3, 4, 5]
  preserves := by
    intro x
    change ((x 0 && x 7 && x 5) || (x 0 && x 8 && x 4) || (x 1 && x 6 && x 5) || (x 1 && x 8 && x 3) || (x 2 && x 6 && x 4) || (x 2 && x 7 && x 3)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym14 : Symmetry where
  run := ![0, 2, 1, 6, 8, 7, 3, 5, 4]
  preserves := by
    intro x
    change ((x 0 && x 8 && x 4) || (x 0 && x 7 && x 5) || (x 2 && x 6 && x 4) || (x 2 && x 7 && x 3) || (x 1 && x 6 && x 5) || (x 1 && x 8 && x 3)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym4 : Symmetry where
  run := ![1, 0, 2, 4, 3, 5, 7, 6, 8]
  preserves := by
    intro x
    change ((x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 2 && x 4 && x 6) || (x 2 && x 3 && x 7)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym8 : Symmetry where
  run := ![2, 0, 1, 5, 3, 4, 8, 6, 7]
  preserves := by
    intro x
    change ((x 2 && x 3 && x 7) || (x 2 && x 4 && x 6) || (x 0 && x 5 && x 7) || (x 0 && x 4 && x 8) || (x 1 && x 5 && x 6) || (x 1 && x 3 && x 8)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym5 : Symmetry where
  run := ![3, 0, 6, 4, 1, 7, 5, 2, 8]
  preserves := by
    intro x
    change ((x 3 && x 1 && x 8) || (x 3 && x 7 && x 2) || (x 0 && x 4 && x 8) || (x 0 && x 7 && x 5) || (x 6 && x 4 && x 2) || (x 6 && x 1 && x 5)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym16 : Symmetry where
  run := ![1, 0, 2, 7, 6, 8, 4, 3, 5]
  preserves := by
    intro x
    change ((x 1 && x 6 && x 5) || (x 1 && x 8 && x 3) || (x 0 && x 7 && x 5) || (x 0 && x 8 && x 4) || (x 2 && x 7 && x 3) || (x 2 && x 6 && x 4)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym17 : Symmetry where
  run := ![3, 0, 6, 5, 2, 8, 4, 1, 7]
  preserves := by
    intro x
    change ((x 3 && x 2 && x 7) || (x 3 && x 8 && x 1) || (x 0 && x 5 && x 7) || (x 0 && x 8 && x 4) || (x 6 && x 5 && x 1) || (x 6 && x 2 && x 4)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym20 : Symmetry where
  run := ![2, 0, 1, 8, 6, 7, 5, 3, 4]
  preserves := by
    intro x
    change ((x 2 && x 6 && x 4) || (x 2 && x 7 && x 3) || (x 0 && x 8 && x 4) || (x 0 && x 7 && x 5) || (x 1 && x 8 && x 3) || (x 1 && x 6 && x 5)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym6 : Symmetry where
  run := ![1, 2, 0, 4, 5, 3, 7, 8, 6]
  preserves := by
    intro x
    change ((x 1 && x 5 && x 6) || (x 1 && x 3 && x 8) || (x 2 && x 4 && x 6) || (x 2 && x 3 && x 7) || (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym10 : Symmetry where
  run := ![2, 1, 0, 5, 4, 3, 8, 7, 6]
  preserves := by
    intro x
    change ((x 2 && x 4 && x 6) || (x 2 && x 3 && x 7) || (x 1 && x 5 && x 6) || (x 1 && x 3 && x 8) || (x 0 && x 5 && x 7) || (x 0 && x 4 && x 8)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym7 : Symmetry where
  run := ![3, 6, 0, 4, 7, 1, 5, 8, 2]
  preserves := by
    intro x
    change ((x 3 && x 7 && x 2) || (x 3 && x 1 && x 8) || (x 6 && x 4 && x 2) || (x 6 && x 1 && x 5) || (x 0 && x 4 && x 8) || (x 0 && x 7 && x 5)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym18 : Symmetry where
  run := ![1, 2, 0, 7, 8, 6, 4, 5, 3]
  preserves := by
    intro x
    change ((x 1 && x 8 && x 3) || (x 1 && x 6 && x 5) || (x 2 && x 7 && x 3) || (x 2 && x 6 && x 4) || (x 0 && x 7 && x 5) || (x 0 && x 8 && x 4)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym22 : Symmetry where
  run := ![2, 1, 0, 8, 7, 6, 5, 4, 3]
  preserves := by
    intro x
    change ((x 2 && x 7 && x 3) || (x 2 && x 6 && x 4) || (x 1 && x 8 && x 3) || (x 1 && x 6 && x 5) || (x 0 && x 8 && x 4) || (x 0 && x 7 && x 5)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym19 : Symmetry where
  run := ![3, 6, 0, 5, 8, 2, 4, 7, 1]
  preserves := by
    intro x
    change ((x 3 && x 8 && x 1) || (x 3 && x 2 && x 7) || (x 6 && x 5 && x 1) || (x 6 && x 2 && x 4) || (x 0 && x 5 && x 7) || (x 0 && x 8 && x 4)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym25 : Symmetry where
  run := ![1, 4, 7, 0, 3, 6, 2, 5, 8]
  preserves := by
    intro x
    change ((x 1 && x 3 && x 8) || (x 1 && x 6 && x 5) || (x 4 && x 0 && x 8) || (x 4 && x 6 && x 2) || (x 7 && x 0 && x 5) || (x 7 && x 3 && x 2)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym24 : Symmetry where
  run := ![3, 4, 5, 0, 1, 2, 6, 7, 8]
  preserves := by
    intro x
    change ((x 3 && x 1 && x 8) || (x 3 && x 2 && x 7) || (x 4 && x 0 && x 8) || (x 4 && x 2 && x 6) || (x 5 && x 0 && x 7) || (x 5 && x 1 && x 6)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym26 : Symmetry where
  run := ![3, 5, 4, 0, 2, 1, 6, 8, 7]
  preserves := by
    intro x
    change ((x 3 && x 2 && x 7) || (x 3 && x 1 && x 8) || (x 5 && x 0 && x 7) || (x 5 && x 1 && x 6) || (x 4 && x 0 && x 8) || (x 4 && x 2 && x 6)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym49 : Symmetry where
  run := ![2, 5, 8, 0, 3, 6, 1, 4, 7]
  preserves := by
    intro x
    change ((x 2 && x 3 && x 7) || (x 2 && x 6 && x 4) || (x 5 && x 0 && x 7) || (x 5 && x 6 && x 1) || (x 8 && x 0 && x 4) || (x 8 && x 3 && x 1)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym48 : Symmetry where
  run := ![6, 7, 8, 0, 1, 2, 3, 4, 5]
  preserves := by
    intro x
    change ((x 6 && x 1 && x 5) || (x 6 && x 2 && x 4) || (x 7 && x 0 && x 5) || (x 7 && x 2 && x 3) || (x 8 && x 0 && x 4) || (x 8 && x 1 && x 3)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym50 : Symmetry where
  run := ![6, 8, 7, 0, 2, 1, 3, 5, 4]
  preserves := by
    intro x
    change ((x 6 && x 2 && x 4) || (x 6 && x 1 && x 5) || (x 8 && x 0 && x 4) || (x 8 && x 1 && x 3) || (x 7 && x 0 && x 5) || (x 7 && x 2 && x 3)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym28 : Symmetry where
  run := ![4, 3, 5, 1, 0, 2, 7, 6, 8]
  preserves := by
    intro x
    change ((x 4 && x 0 && x 8) || (x 4 && x 2 && x 6) || (x 3 && x 1 && x 8) || (x 3 && x 2 && x 7) || (x 5 && x 1 && x 6) || (x 5 && x 0 && x 7)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym29 : Symmetry where
  run := ![4, 1, 7, 3, 0, 6, 5, 2, 8]
  preserves := by
    intro x
    change ((x 4 && x 0 && x 8) || (x 4 && x 6 && x 2) || (x 1 && x 3 && x 8) || (x 1 && x 6 && x 5) || (x 7 && x 3 && x 2) || (x 7 && x 0 && x 5)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym32 : Symmetry where
  run := ![5, 3, 4, 2, 0, 1, 8, 6, 7]
  preserves := by
    intro x
    change ((x 5 && x 0 && x 7) || (x 5 && x 1 && x 6) || (x 3 && x 2 && x 7) || (x 3 && x 1 && x 8) || (x 4 && x 2 && x 6) || (x 4 && x 0 && x 8)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym52 : Symmetry where
  run := ![7, 6, 8, 1, 0, 2, 4, 3, 5]
  preserves := by
    intro x
    change ((x 7 && x 0 && x 5) || (x 7 && x 2 && x 3) || (x 6 && x 1 && x 5) || (x 6 && x 2 && x 4) || (x 8 && x 1 && x 3) || (x 8 && x 0 && x 4)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym53 : Symmetry where
  run := ![5, 2, 8, 3, 0, 6, 4, 1, 7]
  preserves := by
    intro x
    change ((x 5 && x 0 && x 7) || (x 5 && x 6 && x 1) || (x 2 && x 3 && x 7) || (x 2 && x 6 && x 4) || (x 8 && x 3 && x 1) || (x 8 && x 0 && x 4)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym56 : Symmetry where
  run := ![8, 6, 7, 2, 0, 1, 5, 3, 4]
  preserves := by
    intro x
    change ((x 8 && x 0 && x 4) || (x 8 && x 1 && x 3) || (x 6 && x 2 && x 4) || (x 6 && x 1 && x 5) || (x 7 && x 2 && x 3) || (x 7 && x 0 && x 5)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym30 : Symmetry where
  run := ![4, 5, 3, 1, 2, 0, 7, 8, 6]
  preserves := by
    intro x
    change ((x 4 && x 2 && x 6) || (x 4 && x 0 && x 8) || (x 5 && x 1 && x 6) || (x 5 && x 0 && x 7) || (x 3 && x 1 && x 8) || (x 3 && x 2 && x 7)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym34 : Symmetry where
  run := ![5, 4, 3, 2, 1, 0, 8, 7, 6]
  preserves := by
    intro x
    change ((x 5 && x 1 && x 6) || (x 5 && x 0 && x 7) || (x 4 && x 2 && x 6) || (x 4 && x 0 && x 8) || (x 3 && x 2 && x 7) || (x 3 && x 1 && x 8)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym31 : Symmetry where
  run := ![4, 7, 1, 3, 6, 0, 5, 8, 2]
  preserves := by
    intro x
    change ((x 4 && x 6 && x 2) || (x 4 && x 0 && x 8) || (x 7 && x 3 && x 2) || (x 7 && x 0 && x 5) || (x 1 && x 3 && x 8) || (x 1 && x 6 && x 5)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym54 : Symmetry where
  run := ![7, 8, 6, 1, 2, 0, 4, 5, 3]
  preserves := by
    intro x
    change ((x 7 && x 2 && x 3) || (x 7 && x 0 && x 5) || (x 8 && x 1 && x 3) || (x 8 && x 0 && x 4) || (x 6 && x 1 && x 5) || (x 6 && x 2 && x 4)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym58 : Symmetry where
  run := ![8, 7, 6, 2, 1, 0, 5, 4, 3]
  preserves := by
    intro x
    change ((x 8 && x 1 && x 3) || (x 8 && x 0 && x 4) || (x 7 && x 2 && x 3) || (x 7 && x 0 && x 5) || (x 6 && x 2 && x 4) || (x 6 && x 1 && x 5)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym55 : Symmetry where
  run := ![5, 8, 2, 3, 6, 0, 4, 7, 1]
  preserves := by
    intro x
    change ((x 5 && x 6 && x 1) || (x 5 && x 0 && x 7) || (x 8 && x 3 && x 1) || (x 8 && x 0 && x 4) || (x 2 && x 3 && x 7) || (x 2 && x 6 && x 4)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym37 : Symmetry where
  run := ![1, 4, 7, 2, 5, 8, 0, 3, 6]
  preserves := by
    intro x
    change ((x 1 && x 5 && x 6) || (x 1 && x 8 && x 3) || (x 4 && x 2 && x 6) || (x 4 && x 8 && x 0) || (x 7 && x 2 && x 3) || (x 7 && x 5 && x 0)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym36 : Symmetry where
  run := ![3, 4, 5, 6, 7, 8, 0, 1, 2]
  preserves := by
    intro x
    change ((x 3 && x 7 && x 2) || (x 3 && x 8 && x 1) || (x 4 && x 6 && x 2) || (x 4 && x 8 && x 0) || (x 5 && x 6 && x 1) || (x 5 && x 7 && x 0)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym38 : Symmetry where
  run := ![3, 5, 4, 6, 8, 7, 0, 2, 1]
  preserves := by
    intro x
    change ((x 3 && x 8 && x 1) || (x 3 && x 7 && x 2) || (x 5 && x 6 && x 1) || (x 5 && x 7 && x 0) || (x 4 && x 6 && x 2) || (x 4 && x 8 && x 0)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym61 : Symmetry where
  run := ![2, 5, 8, 1, 4, 7, 0, 3, 6]
  preserves := by
    intro x
    change ((x 2 && x 4 && x 6) || (x 2 && x 7 && x 3) || (x 5 && x 1 && x 6) || (x 5 && x 7 && x 0) || (x 8 && x 1 && x 3) || (x 8 && x 4 && x 0)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym60 : Symmetry where
  run := ![6, 7, 8, 3, 4, 5, 0, 1, 2]
  preserves := by
    intro x
    change ((x 6 && x 4 && x 2) || (x 6 && x 5 && x 1) || (x 7 && x 3 && x 2) || (x 7 && x 5 && x 0) || (x 8 && x 3 && x 1) || (x 8 && x 4 && x 0)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym62 : Symmetry where
  run := ![6, 8, 7, 3, 5, 4, 0, 2, 1]
  preserves := by
    intro x
    change ((x 6 && x 5 && x 1) || (x 6 && x 4 && x 2) || (x 8 && x 3 && x 1) || (x 8 && x 4 && x 0) || (x 7 && x 3 && x 2) || (x 7 && x 5 && x 0)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym40 : Symmetry where
  run := ![4, 3, 5, 7, 6, 8, 1, 0, 2]
  preserves := by
    intro x
    change ((x 4 && x 6 && x 2) || (x 4 && x 8 && x 0) || (x 3 && x 7 && x 2) || (x 3 && x 8 && x 1) || (x 5 && x 7 && x 0) || (x 5 && x 6 && x 1)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym41 : Symmetry where
  run := ![4, 1, 7, 5, 2, 8, 3, 0, 6]
  preserves := by
    intro x
    change ((x 4 && x 2 && x 6) || (x 4 && x 8 && x 0) || (x 1 && x 5 && x 6) || (x 1 && x 8 && x 3) || (x 7 && x 5 && x 0) || (x 7 && x 2 && x 3)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym44 : Symmetry where
  run := ![5, 3, 4, 8, 6, 7, 2, 0, 1]
  preserves := by
    intro x
    change ((x 5 && x 6 && x 1) || (x 5 && x 7 && x 0) || (x 3 && x 8 && x 1) || (x 3 && x 7 && x 2) || (x 4 && x 8 && x 0) || (x 4 && x 6 && x 2)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym64 : Symmetry where
  run := ![7, 6, 8, 4, 3, 5, 1, 0, 2]
  preserves := by
    intro x
    change ((x 7 && x 3 && x 2) || (x 7 && x 5 && x 0) || (x 6 && x 4 && x 2) || (x 6 && x 5 && x 1) || (x 8 && x 4 && x 0) || (x 8 && x 3 && x 1)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym65 : Symmetry where
  run := ![5, 2, 8, 4, 1, 7, 3, 0, 6]
  preserves := by
    intro x
    change ((x 5 && x 1 && x 6) || (x 5 && x 7 && x 0) || (x 2 && x 4 && x 6) || (x 2 && x 7 && x 3) || (x 8 && x 4 && x 0) || (x 8 && x 1 && x 3)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym68 : Symmetry where
  run := ![8, 6, 7, 5, 3, 4, 2, 0, 1]
  preserves := by
    intro x
    change ((x 8 && x 3 && x 1) || (x 8 && x 4 && x 0) || (x 6 && x 5 && x 1) || (x 6 && x 4 && x 2) || (x 7 && x 5 && x 0) || (x 7 && x 3 && x 2)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym42 : Symmetry where
  run := ![4, 5, 3, 7, 8, 6, 1, 2, 0]
  preserves := by
    intro x
    change ((x 4 && x 8 && x 0) || (x 4 && x 6 && x 2) || (x 5 && x 7 && x 0) || (x 5 && x 6 && x 1) || (x 3 && x 7 && x 2) || (x 3 && x 8 && x 1)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym46 : Symmetry where
  run := ![5, 4, 3, 8, 7, 6, 2, 1, 0]
  preserves := by
    intro x
    change ((x 5 && x 7 && x 0) || (x 5 && x 6 && x 1) || (x 4 && x 8 && x 0) || (x 4 && x 6 && x 2) || (x 3 && x 8 && x 1) || (x 3 && x 7 && x 2)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym43 : Symmetry where
  run := ![4, 7, 1, 5, 8, 2, 3, 6, 0]
  preserves := by
    intro x
    change ((x 4 && x 8 && x 0) || (x 4 && x 2 && x 6) || (x 7 && x 5 && x 0) || (x 7 && x 2 && x 3) || (x 1 && x 5 && x 6) || (x 1 && x 8 && x 3)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym66 : Symmetry where
  run := ![7, 8, 6, 4, 5, 3, 1, 2, 0]
  preserves := by
    intro x
    change ((x 7 && x 5 && x 0) || (x 7 && x 3 && x 2) || (x 8 && x 4 && x 0) || (x 8 && x 3 && x 1) || (x 6 && x 4 && x 2) || (x 6 && x 5 && x 1)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym70 : Symmetry where
  run := ![8, 7, 6, 5, 4, 3, 2, 1, 0]
  preserves := by
    intro x
    change ((x 8 && x 4 && x 0) || (x 8 && x 3 && x 1) || (x 7 && x 5 && x 0) || (x 7 && x 3 && x 2) || (x 6 && x 5 && x 1) || (x 6 && x 4 && x 2)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

private def sym67 : Symmetry where
  run := ![5, 8, 2, 4, 7, 1, 3, 6, 0]
  preserves := by
    intro x
    change ((x 5 && x 7 && x 0) || (x 5 && x 1 && x 6) || (x 8 && x 4 && x 0) || (x 8 && x 1 && x 3) || (x 2 && x 4 && x 6) || (x 2 && x 7 && x 3)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl

def selectSym : Fin 9 → Fin 9 → Symmetry := ![
  ![sym0, sym0, sym2, sym1, sym0, sym2, sym13, sym12, sym14],
  ![sym4, sym4, sym8, sym4, sym5, sym8, sym16, sym17, sym20],
  ![sym6, sym10, sym6, sym6, sym10, sym7, sym18, sym22, sym19],
  ![sym25, sym24, sym26, sym24, sym24, sym26, sym49, sym48, sym50],
  ![sym28, sym29, sym32, sym28, sym28, sym32, sym52, sym53, sym56],
  ![sym30, sym34, sym31, sym30, sym34, sym30, sym54, sym58, sym55],
  ![sym37, sym36, sym38, sym61, sym60, sym62, sym36, sym36, sym38],
  ![sym40, sym41, sym44, sym64, sym65, sym68, sym40, sym40, sym44],
  ![sym42, sym46, sym43, sym66, sym70, sym67, sym42, sym46, sym42]]

set_option maxRecDepth 20000 in
theorem sym_first : ∀ a b : Fin 9, (selectSym a b).run a = 0 := by decide

set_option maxRecDepth 20000 in
theorem sym_second : ∀ a b : Fin 9, a ≠ b → (selectSym a b).run b = 1 ∨ (selectSym a b).run b = 4 := by decide

theorem pm_nc : ∃ x y : Fin 9 → Bool, pm x ≠ pm y := ⟨fun _ => false, fun _ => true, by decide⟩

theorem pm_not_input : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, x i ≠ pm x := by
  intro i
  exact ⟨fun j => decide (j = i), (by fin_cases i <;> decide)⟩

end PEqualNP.Outside.L_meta_25933_aux


namespace PEqualNP.Outside.L_meta_25933_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Helpers.PermInputs

open scoped Classical

noncomputable def sortGate (g : Gate) : Gate :=
  match g.inputs with
  | [a,b] => if g.op = .and ∨ g.op = .or then ⟨g.op,[min a b,max a b]⟩ else g
  | _ => g

theorem sort_step (w : List Bool) (g : Gate) : step w (sortGate g) = step w g := by
  obtain ⟨op,ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,t⟩⟩⟩
  · rfl
  · rfl
  · by_cases ok : op=GateOp.and ∨ op=GateOp.or
    · rcases ok with rfl | rfl <;> rcases le_total a b with h | h <;>
        simp [sortGate,step,GateOp.eval,Nat.min_eq_left,Nat.max_eq_right,Nat.min_eq_right,
          Nat.max_eq_left,h,Bool.and_comm,Bool.or_comm]
    · simp [sortGate,ok]
  · rfl

theorem sort_run (gs : List Gate) (w : List Bool) :
    (gs.map sortGate).foldl step w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simpa only [List.map_cons,List.foldl_cons,sort_step] using ih (step w g)

def sortedAt (bound : Nat) (g : Gate) : Prop :=
    (g.op=.not ∧ ∃ a, a<bound ∧ g.inputs=[a]) ∨
    ((g.op=.and ∨ g.op=.or) ∧ ∃ a b, a≤b ∧ b<bound ∧ g.inputs=[a,b])

theorem sortedAt_clean {bound : Nat} {g : Gate} (h : sortedAt bound g) : CleanGate bound g := by
  rcases h with h | ⟨op,a,b,ab,hb,args⟩
  · exact Or.inl h
  · exact Or.inr ⟨op,a,b,lt_of_le_of_lt ab hb,hb,args⟩

noncomputable def fixed (s : Symmetry) (gs : List Gate) :=
  (gs.map (relGate 9 9 s.run)).map sortGate

theorem map_bound (s : Symmetry) {i j : Nat} (h : i<9+j) : wmap 9 9 s.run i<9+j := by
  unfold wmap
  split
  · have bound := (s.run ⟨i,by assumption⟩).isLt
    omega
  · omega

theorem fix_one (s : Symmetry) {j : Nat} {g : Gate} (h : CleanGate (9+j) g) :
    sortedAt (9+j) (sortGate (relGate 9 9 s.run g)) := by
  rcases h with ⟨op,a,ha,arg⟩ | ⟨op,a,b,ha,hb,arg⟩
  · left
    exact ⟨by simp [relGate,sortGate,arg,op],_,map_bound s ha,by simp [sortGate,relGate,arg]⟩
  · right
    have h₁:=map_bound s ha
    have h₂:=map_bound s hb
    let u:=wmap 9 9 s.run a
    let v:=wmap 9 9 s.run b
    have shape : sortGate (relGate 9 9 s.run g) = ⟨g.op,[min u v,max u v]⟩ := by
      rcases op with h | h <;> simp [sortGate,relGate,arg,h,u,v]
    rw [shape]
    exact ⟨op,min u v,max u v,min_le_max,(max_lt_iff.mpr ⟨h₁,h₂⟩),rfl⟩

theorem fixed_sorted (s : Symmetry) {gs : List Gate} (cl : CleanL 9 gs)
    {j : Nat} {g : Gate} (h : (fixed s gs)[j]?=some g) : sortedAt (9+j) g := by
  simp only [fixed,List.getElem?_map] at h
  cases q : gs[j]? with
  | none => simp [q] at h
  | some node =>
    simp [q] at h
    subst g
    exact fix_one s (cl j node q)

theorem least_fixed {gs : List Gate} {o : Nat} (L : Least 9 pm gs o) (s : Symmetry) (ho : 9≤o) :
    Least 9 pm (fixed s gs) o := by
  constructor
  · intro j g h
    exact sortedAt_clean (fixed_sorted s L.hcl h)
  · intro x
    have h := (rel_fold 9 9 s.run gs _ _ (rel_init 9 9 s.run x)).2.2 o
    have wo : wmap 9 9 s.run o = o := by simp [wmap,Nat.not_lt.mpr ho];omega
    rw [wo] at h
    change (((gs.map (relGate 9 9 s.run)).map sortGate).foldl step (List.ofFn x)).getD o false = pm x
    rw [sort_run,h]
    exact (L.hev (x ∘ s.run)).trans (s.preserves x)
  · intro gs' o' cl correct
    simpa [fixed] using L.hmin gs' o' cl correct

end PEqualNP.Outside.L_meta_25933_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_25933_aux
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs
open scoped Classical

def Normal (s : Nat) (C : Circuit) :=
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)

structure Permute where
  sym : Symmetry
  inv : Fin 9→Fin 9
  undo : ∀ i, inv (sym.run i)=i
  redo : ∀ i, sym.run (inv i)=i

theorem map_gateindex (f : Fin 9→Fin 9) (j : Nat) : wmap 9 9 f (9+j)=9+j := by simp [wmap,Nat.add_comm]
theorem undo_map (f g : Fin 9→Fin 9) (h : ∀i,f (g i)=i) (k : Nat) :
    wmap 9 9 f (wmap 9 9 g k)=k := by
  by_cases small : k<9
  · simp [wmap,small,(g ⟨k,small⟩).isLt,h]
  · have e : k-9+9=k := by omega
    simp [wmap,small,e]

theorem inverse_assignment (p : Permute) (x : Fin 9→Bool) : (x ∘ p.inv) ∘ p.sym.run=x := by
  funext i
  simp [Function.comp_def,p.undo]

theorem perm_wires (p : Permute) (gs : List Gate) (x : Fin 9→Bool) (i : Nat) :
    vl (fixed p.sym gs) x (wmap 9 9 p.sym.run i)=vl gs (x ∘ p.sym.run) i := by
  change (((gs.map (relGate 9 9 p.sym.run)).map sortGate).foldl step (List.ofFn x)).getD _ false=_
  rw [sort_run]
  exact (rel_fold 9 9 p.sym.run gs _ _ (rel_init 9 9 p.sym.run x)).2.2 i

def strictAt (bound : Nat) (g : Gate) : Prop :=
    (g.op=.not ∧ ∃ a,a<bound ∧ g.inputs=[a]) ∨
    ((g.op=.and ∨ g.op=.or) ∧ ∃ a b,a<b ∧ b<bound ∧ g.inputs=[a,b])

theorem fixed_strict (p : Permute) {j : Nat} {g : Gate} (h : strictAt (9+j) g) :
    strictAt (9+j) (sortGate (relGate 9 9 p.sym.run g)) := by
  rcases h with ⟨op,a,ha,arg⟩ | ⟨op,a,b,ab,hb,arg⟩
  · exact Or.inl ⟨by simp [sortGate,relGate,op,arg],_,map_bound p.sym ha,by simp [sortGate,relGate,arg]⟩
  · let u:=wmap 9 9 p.sym.run a
    let v:=wmap 9 9 p.sym.run b
    have ne : u≠v := by
      intro eq
      have e:=congrArg (wmap 9 9 p.inv) eq
      simp only [u,v,undo_map _ _ p.undo] at e
      omega
    have shape : sortGate (relGate 9 9 p.sym.run g) = ⟨g.op,[min u v,max u v]⟩ := by
      rcases op with h | h <;> simp [sortGate,relGate,arg,h,u,v]
    rw [shape]
    have smaller : min u v < max u v := by omega
    exact Or.inr ⟨op,_,_,smaller,max_lt_iff.mpr ⟨map_bound p.sym (ab.trans hb),map_bound p.sym hb⟩,rfl⟩

theorem reader_map (p : Permute) {g : Gate} {j w : Nat} (h : strictAt (9+j) g) (read : w∈g.inputs) :
    wmap 9 9 p.sym.run w ∈ (sortGate (relGate 9 9 p.sym.run g)).inputs := by
  rcases h with ⟨op,a,_,arg⟩ | ⟨op,a,b,_,_,arg⟩
  · simp [arg] at read
    subst w
    simp [sortGate,relGate,arg]
  · simp only [arg,List.mem_cons,List.not_mem_nil,or_false] at read
    rcases op with op | op <;>
      rcases read with rfl | rfl <;> simp [sortGate,relGate,arg,op] <;> omega

noncomputable def shiftC (p : Permute) (C : Circuit) : Circuit := ⟨fixed p.sym C.gates,C.output⟩

theorem normal_shift {s : Nat} {C : Circuit} (p : Permute) (norm : Normal s C) (out : 9≤C.output) :
    Normal s (shiftC p C) := by
  obtain ⟨fan,size,funct,last,shape,irred,live⟩:=norm
  have len : (shiftC p C).gates.length=C.gates.length := by simp [shiftC,fixed]
  let old (j : Fin (shiftC p C).gates.length) : Fin C.gates.length:=⟨j.val,by have :=j.isLt;omega⟩
  let new (j : Fin C.gates.length) : Fin (shiftC p C).gates.length:=⟨j.val,by have :=j.isLt;omega⟩
  have node (j : Fin (shiftC p C).gates.length) :
      (shiftC p C).gates.get j=sortGate (relGate 9 9 p.sym.run (C.gates.get (old j))) := by
    change ((C.gates.map (relGate 9 9 p.sym.run)).map sortGate)[j.val] = _
    simp [old,List.get_eq_getElem]
  have good (j : Fin (shiftC p C).gates.length) : strictAt (9+j.val) ((shiftC p C).gates.get j) := by
    rw [node]
    exact fixed_strict p (shape (old j))
  have orig (x : Fin 9→Bool) (i : Nat) :
      vl (fixed p.sym C.gates) (x ∘ p.inv) (wmap 9 9 p.sym.run i)=vl C.gates x i := by
    rw [perm_wires,inverse_assignment]
  refine ⟨?_,by simpa [shiftC,fixed,Circuit.size] using size,?_,by simpa [shiftC,fixed,Circuit.size] using last,good,?_,?_⟩
  · intro g hg
    obtain ⟨j,rfl⟩:=List.mem_iff_get.mp hg
    have condition:=good j
    change ((shiftC p C).gates.get j).op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ ((shiftC p C).gates.get j).inputs.length ≤ 2
    rcases condition with ⟨op,a,_,arg⟩ | ⟨op,a,b,_,_,arg⟩
    · rw [op,arg];simp
    · rcases op with h | h <;> rw [h,arg] <;> simp
  · intro x
    have eq:=perm_wires p C.gates x C.output
    have wo : wmap 9 9 p.sym.run C.output=C.output := by simp [wmap,Nat.not_lt.mpr out];omega
    rw [wo] at eq
    exact eq.trans ((funct (x ∘ p.sym.run)).trans (p.sym.preserves x))
  · intro j
    obtain ⟨non,distinct⟩:=irred (old j)
    constructor
    · obtain ⟨x,y,ne⟩:=non
      refine ⟨x ∘ p.inv,y ∘ p.inv,?_⟩
      have ex:=orig x (9+j.val)
      have ey:=orig y (9+j.val)
      rw [map_gateindex] at ex ey
      exact fun eq=>ne (ex.symm.trans (eq.trans ey))
    · intro k hk
      let k' := wmap 9 9 p.inv k
      have bound : k'<9+j.val := by
        dsimp [k',wmap]
        split
        · have hi:=(p.inv ⟨k,by assumption⟩).isLt;omega
        · omega
      obtain ⟨x,ne⟩:=distinct k' bound
      refine ⟨x ∘ p.inv,?_⟩
      have ex:=orig x (9+j.val)
      have ek:=orig x k'
      rw [map_gateindex] at ex
      rw [show wmap 9 9 p.sym.run k'=k from undo_map _ _ p.redo k] at ek
      exact fun eq=>ne (ex.symm.trans (eq.trans ek))
  · intro j before
    obtain ⟨t,after,mem⟩:=live (old j) (by dsimp [old];omega)
    refine ⟨new t,after,?_⟩
    rw [node]
    have read:=reader_map p (shape t) mem
    rw [map_gateindex] at read
    exact read

end PEqualNP.Outside.L_meta_25933_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_25933_aux
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.PermInputs
open scoped Classical

noncomputable def move (r : Permute) (g : Gate) := sortGate (relGate 9 9 r.sym.run g)
theorem move_and (r : Permute) (a b : Nat) : move r ⟨.and,[a,b]⟩ =
    ⟨.and,[min (wmap 9 9 r.sym.run a) (wmap 9 9 r.sym.run b),max (wmap 9 9 r.sym.run a) (wmap 9 9 r.sym.run b)]⟩ := by simp [move,sortGate,relGate]
theorem move_or (r : Permute) (a b : Nat) : move r ⟨.or,[a,b]⟩ =
    ⟨.or,[min (wmap 9 9 r.sym.run a) (wmap 9 9 r.sym.run b),max (wmap 9 9 r.sym.run a) (wmap 9 9 r.sym.run b)]⟩ := by simp [move,sortGate,relGate]
theorem move_not (r : Permute) (a : Nat) : move r ⟨.not,[a]⟩ =
    ⟨.not,[wmap 9 9 r.sym.run a]⟩ := by simp [move,sortGate,relGate]

def GateCase (f g : Gate) (menu : List Gate) : Prop :=
  (∃ p : Permute,move p f=f ∧ move p g∈menu) ∨
  (∃ k : Fin 10,∀ x : Fin 9→Bool,vl [f,g] x 10=vl [f,g] x k.val) ∨
  (∃ b : Bool,∀ x : Fin 9→Bool,vl [f,g] x 10=b)

theorem prefix_vl (pre rest : List Gate) (x : Fin 9→Bool) (k : Nat) (h : k<9+pre.length) :
    vl (pre++rest) x k=vl pre x k := by
  unfold vl
  rw [wiresFrom_append,getD_wiresFrom]
  simpa [length_wiresFrom] using h

theorem has_two {s : Nat} {C : Circuit} {f : Gate} (nrm : Normal s C) (head : C.gates.head?=some f)
    (onefails : ∃ x : Fin 9→Bool,vl [f] x 9≠pm x) :
    ∃ (g : Gate) (rest : List Gate), C.gates=f::g::rest := by
  obtain ⟨gs,o⟩:=C
  obtain ⟨_,_,computes,last,_,_,_⟩:=nrm
  change gs.head?=some f at head
  cases gs with
  | nil => simp at head
  | cons a tail =>
    have af : a=f:=Option.some.inj head
    subst a
    cases tail with
    | nil =>
      have out : o=9 := by change o+1=9+1 at last;omega
      subst o
      obtain ⟨x,ne⟩:=onefails
      exact False.elim (ne (computes x))
    | cons b rest => exact ⟨b,rest,rfl⟩

theorem choose_second {s : Nat} {C : Circuit} {f : Gate} {menu : List Gate}
    (nrm : Normal s C) (head : C.gates.head?=some f)
    (onefails : ∃ x : Fin 9→Bool,vl [f] x 9≠pm x)
    (classify : ∀ g : Gate,strictAt 10 g → GateCase f g menu) :
    ∃ D : Circuit,Normal s D ∧ D.gates.head?=some f ∧
      ∃ gate, D.gates.tail.head?=some gate ∧ gate∈menu := by
  obtain ⟨g,rest,gates⟩:=has_two nrm head onefails
  obtain ⟨fan,sz,eval,last,shape,irr,live⟩:=nrm
  let j : Fin C.gates.length:=⟨1,by simp [gates]⟩
  have q : C.gates.get j=g := by simp [j,List.get_eq_getElem,gates]
  have sg:=shape j
  rw [q] at sg
  have out : 9≤C.output := by change C.output+1=9+C.gates.length at last;rw [gates] at last;simp at last;omega
  have read (x : Fin 9→Bool) (k : Nat) (h : k<11) :
      (C.wires (List.ofFn x)).getD k false=vl [f,g] x k := by
    change vl C.gates x k=_
    rw [gates]
    exact prefix_vl [f,g] rest x k h
  rcases classify g sg with ⟨p,hf,hg⟩ | ⟨k,same⟩ | ⟨b,flat⟩
  · have full : (shiftC p C).gates=move p f::move p g::fixed p.sym rest := by simp [shiftC,fixed,move,gates]
    exact ⟨shiftC p C,normal_shift p ⟨fan,sz,eval,last,shape,irr,live⟩ out,
      by simp [full,hf],move p g,by simp [full],hg⟩
  · obtain ⟨x,ne⟩:=(irr j).2 k.val k.isLt
    change (C.wires (List.ofFn x)).getD 10 false ≠ (C.wires (List.ofFn x)).getD k.val false at ne
    rw [read x 10 (by decide),read x k.val (by omega)] at ne
    exact False.elim (ne (same x))
  · obtain ⟨x,y,ne⟩:=(irr j).1
    change (C.wires (List.ofFn x)).getD 10 false ≠ (C.wires (List.ofFn y)).getD 10 false at ne
    rw [read x 10 (by decide),read y 10 (by decide),flat x,flat y] at ne
    exact False.elim (ne rfl)

end PEqualNP.Outside.L_meta_25933_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_25933_aux
namespace PEqualNP.Outside.L_meta_25933_aux.Second25933
def firstGate : Gate := ⟨.or,[0,1]⟩
def menu : List Gate := [⟨.and,[0,1]⟩, ⟨.and,[0,2]⟩, ⟨.and,[0,3]⟩, ⟨.and,[0,4]⟩, ⟨.and,[0,5]⟩, ⟨.and,[2,3]⟩, ⟨.and,[2,5]⟩, ⟨.and,[2,9]⟩, ⟨.and,[3,4]⟩, ⟨.and,[3,5]⟩, ⟨.and,[3,6]⟩, ⟨.and,[3,7]⟩, ⟨.and,[3,8]⟩, ⟨.and,[3,9]⟩, ⟨.and,[5,8]⟩, ⟨.and,[5,9]⟩, ⟨.or,[0,2]⟩, ⟨.or,[0,3]⟩, ⟨.or,[0,4]⟩, ⟨.or,[0,5]⟩, ⟨.or,[2,3]⟩, ⟨.or,[2,5]⟩, ⟨.or,[2,9]⟩, ⟨.or,[3,4]⟩, ⟨.or,[3,5]⟩, ⟨.or,[3,6]⟩, ⟨.or,[3,7]⟩, ⟨.or,[3,8]⟩, ⟨.or,[3,9]⟩, ⟨.or,[5,8]⟩, ⟨.or,[5,9]⟩, ⟨.not,[0]⟩, ⟨.not,[2]⟩, ⟨.not,[3]⟩, ⟨.not,[5]⟩, ⟨.not,[9]⟩]
private def rot0 : Permute where
  sym := ⟨![0, 1, 2, 3, 4, 5, 6, 7, 8], by
    intro x
    change ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl⟩
  inv := ![0, 1, 2, 3, 4, 5, 6, 7, 8]
  undo := by decide
  redo := by decide
private def rot1 : Permute where
  sym := ⟨![1, 0, 2, 4, 3, 5, 7, 6, 8], by
    intro x
    change ((x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 2 && x 4 && x 6) || (x 2 && x 3 && x 7)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl⟩
  inv := ![1, 0, 2, 4, 3, 5, 7, 6, 8]
  undo := by decide
  redo := by decide
private def rot2 : Permute where
  sym := ⟨![0, 1, 2, 6, 7, 8, 3, 4, 5], by
    intro x
    change ((x 0 && x 7 && x 5) || (x 0 && x 8 && x 4) || (x 1 && x 6 && x 5) || (x 1 && x 8 && x 3) || (x 2 && x 6 && x 4) || (x 2 && x 7 && x 3)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl⟩
  inv := ![0, 1, 2, 6, 7, 8, 3, 4, 5]
  undo := by decide
  redo := by decide
private def rot3 : Permute where
  sym := ⟨![1, 0, 2, 7, 6, 8, 4, 3, 5], by
    intro x
    change ((x 1 && x 6 && x 5) || (x 1 && x 8 && x 3) || (x 0 && x 7 && x 5) || (x 0 && x 8 && x 4) || (x 2 && x 7 && x 3) || (x 2 && x 6 && x 4)) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))
    ac_rfl⟩
  inv := ![1, 0, 2, 7, 6, 8, 4, 3, 5]
  undo := by decide
  redo := by decide
private theorem unary : ∀ a : Fin 10, GateCase firstGate ⟨.not,[a.val]⟩ menu := by
  intro a
  fin_cases a
  · refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_not]
      exact List.mem_iff_get.mpr ⟨⟨31,by decide⟩,rfl⟩
  · refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_not]
      exact List.mem_iff_get.mpr ⟨⟨31,by decide⟩,rfl⟩
  · refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_not]
      exact List.mem_iff_get.mpr ⟨⟨32,by decide⟩,rfl⟩
  · refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_not]
      exact List.mem_iff_get.mpr ⟨⟨33,by decide⟩,rfl⟩
  · refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_not]
      exact List.mem_iff_get.mpr ⟨⟨33,by decide⟩,rfl⟩
  · refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_not]
      exact List.mem_iff_get.mpr ⟨⟨34,by decide⟩,rfl⟩
  · refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_not]
      exact List.mem_iff_get.mpr ⟨⟨33,by decide⟩,rfl⟩
  · refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_not]
      exact List.mem_iff_get.mpr ⟨⟨33,by decide⟩,rfl⟩
  · refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_not]
      exact List.mem_iff_get.mpr ⟨⟨34,by decide⟩,rfl⟩
  · refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_not]
      exact List.mem_iff_get.mpr ⟨⟨35,by decide⟩,rfl⟩
private theorem binary_and : ∀ a b : Fin 10, a<b → GateCase firstGate ⟨.and,[a.val,b.val]⟩ menu := by
  intro a b
  fin_cases a <;> fin_cases b
  · intro h; exact False.elim ((by decide : ¬((0 : Fin 10)<0)) h)
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨0,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨1,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨2,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨3,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨4,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨2,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨3,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨4,by decide⟩,rfl⟩
  · intro _
    refine Or.inr (Or.inl ⟨0,?_⟩)
    intro x
    have raw : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl
    unfold PEqualNP.MetaComplexity.Helpers.vl PEqualNP.MetaComplexity.Helpers.wiresFrom
    rw [raw]
    cases x 0 <;> cases x 1 <;> rfl
  · intro h; exact False.elim ((by decide : ¬((1 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((1 : Fin 10)<1)) h)
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨1,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨3,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨2,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨4,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨3,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨2,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨4,by decide⟩,rfl⟩
  · intro _
    refine Or.inr (Or.inl ⟨1,?_⟩)
    intro x
    have raw : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl
    unfold PEqualNP.MetaComplexity.Helpers.vl PEqualNP.MetaComplexity.Helpers.wiresFrom
    rw [raw]
    cases x 0 <;> cases x 1 <;> rfl
  · intro h; exact False.elim ((by decide : ¬((2 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((2 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((2 : Fin 10)<2)) h)
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨5,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨5,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨6,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨5,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨5,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨6,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨7,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((3 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((3 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((3 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((3 : Fin 10)<3)) h)
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨8,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨9,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨10,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨11,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨12,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨13,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((4 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((4 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((4 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((4 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((4 : Fin 10)<4)) h)
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨9,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨11,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨10,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨12,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨13,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<4)) h)
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<5)) h)
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨12,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨12,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨14,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨15,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<4)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<5)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<6)) h)
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨8,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨9,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨13,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<4)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<5)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<6)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<7)) h)
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨9,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨13,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<4)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<5)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<6)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<7)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<8)) h)
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_and]
      exact List.mem_iff_get.mpr ⟨⟨15,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<4)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<5)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<6)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<7)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<8)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<9)) h)
private theorem binary_or : ∀ a b : Fin 10, a<b → GateCase firstGate ⟨.or,[a.val,b.val]⟩ menu := by
  intro a b
  fin_cases a <;> fin_cases b
  · intro h; exact False.elim ((by decide : ¬((0 : Fin 10)<0)) h)
  · intro _
    refine Or.inr (Or.inl ⟨9,?_⟩)
    intro x
    have raw : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl
    unfold PEqualNP.MetaComplexity.Helpers.vl PEqualNP.MetaComplexity.Helpers.wiresFrom
    rw [raw]
    cases x 0 <;> cases x 1 <;> rfl
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨16,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨17,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨18,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨19,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨17,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨18,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨19,by decide⟩,rfl⟩
  · intro _
    refine Or.inr (Or.inl ⟨9,?_⟩)
    intro x
    have raw : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl
    unfold PEqualNP.MetaComplexity.Helpers.vl PEqualNP.MetaComplexity.Helpers.wiresFrom
    rw [raw]
    cases x 0 <;> cases x 1 <;> rfl
  · intro h; exact False.elim ((by decide : ¬((1 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((1 : Fin 10)<1)) h)
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨16,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨18,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨17,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨19,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨18,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨17,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨19,by decide⟩,rfl⟩
  · intro _
    refine Or.inr (Or.inl ⟨9,?_⟩)
    intro x
    have raw : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl
    unfold PEqualNP.MetaComplexity.Helpers.vl PEqualNP.MetaComplexity.Helpers.wiresFrom
    rw [raw]
    cases x 0 <;> cases x 1 <;> rfl
  · intro h; exact False.elim ((by decide : ¬((2 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((2 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((2 : Fin 10)<2)) h)
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨20,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨20,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨21,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨20,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨20,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨21,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨22,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((3 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((3 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((3 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((3 : Fin 10)<3)) h)
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨23,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨24,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨25,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨26,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨27,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨28,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((4 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((4 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((4 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((4 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((4 : Fin 10)<4)) h)
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨24,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨26,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨25,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨27,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot1,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨28,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<4)) h)
  · intro h; exact False.elim ((by decide : ¬((5 : Fin 10)<5)) h)
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨27,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨27,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨29,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot0,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨30,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<4)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<5)) h)
  · intro h; exact False.elim ((by decide : ¬((6 : Fin 10)<6)) h)
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨23,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨24,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨28,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<4)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<5)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<6)) h)
  · intro h; exact False.elim ((by decide : ¬((7 : Fin 10)<7)) h)
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨24,by decide⟩,rfl⟩
  · intro _
    refine Or.inl ⟨rot3,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨28,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<4)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<5)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<6)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<7)) h)
  · intro h; exact False.elim ((by decide : ¬((8 : Fin 10)<8)) h)
  · intro _
    refine Or.inl ⟨rot2,?_,?_⟩
    · simp only [firstGate,move_or] <;> rfl
    · rw [move_or]
      exact List.mem_iff_get.mpr ⟨⟨30,by decide⟩,rfl⟩
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<0)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<1)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<2)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<3)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<4)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<5)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<6)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<7)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<8)) h)
  · intro h; exact False.elim ((by decide : ¬((9 : Fin 10)<9)) h)
theorem classify (g : Gate) (shape : strictAt 10 g) : GateCase firstGate g menu := by
  obtain ⟨op,ins⟩:=g
  rcases shape with ⟨h,a,ha,arg⟩ | ⟨h,a,b,ab,hb,arg⟩
  · change op=GateOp.not at h
    change ins=[a] at arg
    subst op
    subst ins
    exact unary ⟨a,ha⟩
  · change ins=[a,b] at arg
    subst ins
    rcases h with h | h
    · change op=GateOp.and at h
      subst op
      exact binary_and ⟨a,ab.trans hb⟩ ⟨b,hb⟩ ab
    · change op=GateOp.or at h
      subst op
      exact binary_or ⟨a,ab.trans hb⟩ ⟨b,hb⟩ ab
theorem fails : ∃ x : Fin 9→Bool, PEqualNP.MetaComplexity.Helpers.vl [firstGate] x 9 ≠ pm x := by
  exact ⟨![true, true, false, false, false, false, false, false, false],by decide⟩
end PEqualNP.Outside.L_meta_25933_aux.Second25933
open PEqualNP.Outside.L_meta_25933_aux.Second25933
theorem PEqualNP.Outside.L_meta_25933 : ∀ s : ℕ,
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    (C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 8]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩) := by
  rintro s ⟨C,fan,sz,eval,last,nodes,values,live,head⟩
  obtain ⟨D,nrm,h,g,second,allowed⟩:=choose_second (f:=firstGate) (menu:=menu)
    (s:=s) (C:=C) ⟨fan,sz,eval,last,nodes,values,live⟩ head fails classify
  obtain ⟨fan,sz,eval,last,nodes,values,live⟩:=nrm
  refine ⟨D,fan,sz,eval,last,nodes,values,live,h,?_⟩
  rw [second]
  simpa [menu] using allowed
