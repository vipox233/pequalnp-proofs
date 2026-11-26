import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19493_aux
namespace Transfer
-- The argument and all lemmas before W0 are those of the checked proof of L-meta-19325 (same repository);
-- the sub-grid, its wire sets, the goal set and the search depth are those of this graph.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool


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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
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

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
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

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

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

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
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
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
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

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
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
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
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
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
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
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
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
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
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
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
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
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
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
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
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
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
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
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

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

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
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
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
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
theorem two_gates_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
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
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
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

def st (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)

def pick (b t f : Bool) : Bool := Bool.rec (motive := fun _ => Bool) f t b

theorem pick_eq (b t f : Bool) : pick b t f = if b then t else f := by cases b <;> rfl

def bitN (s c : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight s c) 1) 1

theorem bitN_eq (s c : ℕ) : bitN s c = s.testBit c := by
  have h1 : Nat.land (Nat.shiftRight s c) 1 = (s >>> c) % 2 := Nat.and_one_is_mod _
  have h2 : s.testBit c = decide ((s >>> c) % 2 = 1) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rw [h2]
  unfold bitN
  rw [h1]
  by_cases h : (s >>> c) % 2 = 1
  · rw [h]; rfl
  · rw [decide_eq_false h]
    exact Bool.eq_false_iff.2 fun hh => h (Nat.eq_of_beq_eq_true hh)

def ext1 (c s : ℕ) (L : List ℕ) (k : List ℕ → ℕ → Bool) : Bool :=
  pick (bitN s c) (k L s) (st (Nat.lor s (Nat.pow 2 c)) fun s' => k (c :: L) s')

def grow (z : ℕ) (ws : List ℕ) : ℕ → List ℕ → (List ℕ → ℕ → Bool) → Bool :=
  List.rec (motive := fun _ => ℕ → List ℕ → (List ℕ → ℕ → Bool) → Bool) (fun s L k => k L s)
    (fun b _ ih s L k => st (Nat.land z b) fun p => ext1 p s L fun L s =>
      st (Nat.lor z b) fun q => ext1 q s L fun L s => ih s L k) ws

def anyb (goal z : ℕ) (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun b _ ih => pick (Nat.beq (Nat.land z b) goal) true
      (pick (Nat.beq (Nat.lor z b) goal) true ih)) ws

def chk (M goal : ℕ) (ws L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun z _ ih => pick (Nat.beq z goal) true (pick (Nat.beq (Nat.xor z M) goal) true
      (pick (anyb goal z ws) true ih))) L

def loop (goal : ℕ) (f : ℕ → List ℕ → Bool) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun z post ih => pick (Nat.beq z goal) true (pick (f z post) true ih)) L

def srch (M goal : ℕ) (j : ℕ) : List ℕ → ℕ → List ℕ → Bool :=
  Nat.rec (motive := fun _ => List ℕ → ℕ → List ℕ → Bool) (fun ws _ L => chk M goal ws L)
    (fun _ ih ws s L => loop goal (fun z post => st (Nat.xor z M) fun q => ext1 q s post fun L s =>
      grow z ws s L fun L s => ih (z :: ws) s L) L) j

theorem ext1_spec (c s : ℕ) (L : List ℕ) : ∃ L' s', (∀ k, ext1 c s L k = k L' s') ∧
    (∀ d ∈ L, d ∈ L') ∧ (c ∈ L' ∨ s.testBit c = true) ∧
    (∀ d, s'.testBit d = true → s.testBit d = true ∨ d ∈ L') := by
  by_cases h : s.testBit c = true
  · refine ⟨L, s, fun k => ?_, fun d hd => hd, .inr h, fun d hd => .inl hd⟩
    unfold ext1
    rw [bitN_eq, h]; rfl
  · refine ⟨c :: L, s ||| 2 ^ c, fun k => ?_, fun d hd => List.mem_cons_of_mem _ hd,
      .inl List.mem_cons_self, fun d hd => ?_⟩
    · unfold ext1
      rw [bitN_eq, Bool.eq_false_iff.2 h]; rfl
    · rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at hd
      rcases hd with hd | hd
      · exact .inl hd
      · have : c = d := of_decide_eq_true hd
        exact .inr (this ▸ List.mem_cons_self)

theorem grow_spec (z : ℕ) : ∀ (ws : List ℕ) (s : ℕ) (L : List ℕ), ∃ L' s',
    (∀ k, grow z ws s L k = k L' s') ∧ (∀ d ∈ L, d ∈ L') ∧
    (∀ b ∈ ws, (z &&& b ∈ L' ∨ s.testBit (z &&& b) = true) ∧
      (z ||| b ∈ L' ∨ s.testBit (z ||| b) = true)) ∧
    (∀ d, s'.testBit d = true → s.testBit d = true ∨ d ∈ L') := by
  intro ws
  induction ws with
  | nil => intro s L; exact ⟨L, s, fun k => rfl, fun d hd => hd, by simp, fun d hd => .inl hd⟩
  | cons b ws ih =>
    intro s L
    obtain ⟨L1, s1, e1, m1, c1, t1⟩ := ext1_spec (z &&& b) s L
    obtain ⟨L2, s2, e2, m2, c2, t2⟩ := ext1_spec (z ||| b) s1 L1
    obtain ⟨L3, s3, e3, m3, c3, t3⟩ := ih s2 L2
    have back1 : ∀ d, s1.testBit d = true → d ∈ L3 ∨ s.testBit d = true := fun d hd =>
      (t1 d hd).elim .inr fun h => .inl (m3 d (m2 d h))
    have back2 : ∀ d, s2.testBit d = true → d ∈ L3 ∨ s.testBit d = true := fun d hd =>
      (t2 d hd).elim (back1 d) fun h => .inl (m3 d h)
    refine ⟨L3, s3, fun k => ?_, fun d hd => m3 d (m2 d (m1 d hd)), ?_, ?_⟩
    · change ext1 (z &&& b) s L (fun L s => ext1 (z ||| b) s L fun L s => grow z ws s L k) = _
      rw [e1, e2, e3]
    · intro b' hb'
      rcases List.mem_cons.1 hb' with rfl | hb'
      · refine ⟨c1.imp (fun h => m3 _ (m2 _ h)) id, ?_⟩
        rcases c2 with h | h
        · exact .inl (m3 _ h)
        · exact back1 _ h
      · obtain ⟨p, q⟩ := c3 b' hb'
        exact ⟨p.elim .inl (back2 _), q.elim .inl (back2 _)⟩
    · intro d hd
      rcases t3 d hd with h | h
      · exact (back2 d h).symm
      · exact .inr h

def Ob (M : ℕ) (ws : List ℕ) (d : ℕ) : Prop :=
  d = M ∨ (∃ a ∈ ws, d = a ^^^ M) ∨ ∃ a ∈ ws, ∃ b ∈ ws, d = a &&& b ∨ d = a ||| b

def Der (M : ℕ) : List ℕ → List ℕ → Prop
  | _, [] => True
  | ws, d :: D => (d ∈ 0 :: ws ∨ Ob M ws d) ∧ Der M (d :: ws) D

theorem Ob_mono {M : ℕ} {ws ws' : List ℕ} (h : ∀ x ∈ 0 :: ws, x ∈ 0 :: ws') {d : ℕ}
    (hd : d ∈ 0 :: ws ∨ Ob M ws d) : d ∈ 0 :: ws' ∨ Ob M ws' d := by
  have hz : ∀ x ∈ ws, x = 0 ∨ x ∈ ws' := fun x hx => List.mem_cons.1 (h x (List.mem_cons_of_mem _ hx))
  have m0 : (0 : ℕ) ∈ 0 :: ws' := List.mem_cons_self
  rcases hd with hd | rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl | rfl⟩
  · exact .inl (h d hd)
  · exact .inr (.inl rfl)
  · rcases hz a ha with rfl | ha
    · exact .inr (.inl (by simp))
    · exact .inr (.inr (.inl ⟨a, ha, rfl⟩))
  · rcases hz a ha with rfl | ha
    · exact .inl (by simp)
    · rcases hz b hb with rfl | hb
      · exact .inl (by simp)
      · exact .inr (.inr (.inr ⟨a, ha, b, hb, .inl rfl⟩))
  · rcases hz a ha with rfl | ha
    · exact .inl (by simpa using h b (List.mem_cons_of_mem _ hb))
    · rcases hz b hb with rfl | hb
      · exact .inl (by simpa using Or.inr ha)
      · exact .inr (.inr (.inr ⟨a, ha, b, hb, .inr rfl⟩))

theorem Der_mono (M : ℕ) : ∀ (D ws ws' : List ℕ), (∀ x ∈ 0 :: ws, x ∈ 0 :: ws') →
    Der M ws D → Der M ws' D := by
  intro D
  induction D with
  | nil => intro ws ws' _ _; trivial
  | cons d D ih =>
    intro ws ws' h hD
    refine ⟨Ob_mono h hD.1, ih _ _ ?_ hD.2⟩
    intro x hx
    simp only [List.mem_cons] at hx h ⊢
    rcases hx with hx | hx | hx
    · exact .inl hx
    · exact .inr (.inl hx)
    · rcases h x (.inr hx) with h | h
      · exact .inl h
      · exact .inr (.inr h)

theorem Der_filter (M z : ℕ) : ∀ (D ws ws' : List ℕ), (∀ x ∈ 0 :: ws, x ∈ 0 :: ws') → z ∈ ws' →
    Der M ws D → Der M ws' (D.filter fun x => decide (x ≠ z)) := by
  intro D
  induction D with
  | nil => intro ws ws' _ _ _; trivial
  | cons d D ih =>
    intro ws ws' h hz hD
    have hsub : ∀ ws'' : List ℕ, (∀ x ∈ 0 :: ws', x ∈ 0 :: ws'') → d ∈ 0 :: ws'' →
        ∀ x ∈ 0 :: d :: ws, x ∈ 0 :: ws'' := by
      intro ws'' h2 hd x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hd
        · exact h2 x (h x (List.mem_cons_of_mem _ hx))
    by_cases hdz : d = z
    · subst hdz
      rw [List.filter_cons_of_neg (by simp)]
      exact ih _ _ (hsub ws' (fun x hx => hx) (List.mem_cons_of_mem _ hz)) hz hD.2
    · rw [List.filter_cons_of_pos (by simpa using hdz)]
      refine ⟨Ob_mono h hD.1, ih _ _ (hsub (d :: ws') ?_ (by simp)) (List.mem_cons_of_mem _ hz) hD.2⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)

theorem Der_first (M goal : ℕ) (ws : List ℕ) (hg : goal ∉ 0 :: ws) : ∀ D : List ℕ, Der M ws D →
    goal ∈ D → ∃ d ∈ D, d ∉ 0 :: ws ∧ Ob M ws d := by
  intro D
  induction D with
  | nil => intro _ h; simp at h
  | cons d D ih =>
    intro hD hgD
    by_cases hd : d ∈ 0 :: ws
    · have hne : goal ≠ d := fun e => hg (e ▸ hd)
      have hD' : Der M ws D := Der_mono M D (d :: ws) ws (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hd
          · exact List.mem_cons_of_mem _ hx) hD.2
      obtain ⟨e, he, h⟩ := ih hD' ((List.mem_cons.1 hgD).resolve_left hne)
      exact ⟨e, List.mem_cons_of_mem _ he, h⟩
    · exact ⟨d, List.mem_cons_self, hd, hD.1.resolve_left hd⟩

theorem Ob_cons {M z d : ℕ} {ws : List ℕ} (h : Ob M (z :: ws) d) :
    Ob M ws d ∨ d = z ^^^ M ∨ (∃ b ∈ ws, d = z &&& b ∨ d = z ||| b) ∨ d ∈ 0 :: z :: ws := by
  rcases h with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, hd⟩
  · exact .inl (.inl rfl)
  · rcases List.mem_cons.1 ha with rfl | ha
    · exact .inr (.inl rfl)
    · exact .inl (.inr (.inl ⟨a, ha, rfl⟩))
  · rcases List.mem_cons.1 ha with ea | ha'
    · rcases List.mem_cons.1 hb with eb | hb'
      · refine .inr (.inr (.inr ?_))
        subst ea; subst eb
        rcases hd with rfl | rfl <;> simp
      · subst ea
        exact .inr (.inr (.inl ⟨b, hb', hd⟩))
    · rcases List.mem_cons.1 hb with eb | hb'
      · refine .inr (.inr (.inl ⟨a, ha', ?_⟩))
        subst eb
        rcases hd with rfl | rfl
        · exact .inl (Nat.and_comm _ _)
        · exact .inr (Nat.or_comm _ _)
      · exact .inl (.inr (.inr ⟨a, ha', b, hb', hd⟩))

theorem pick_true {b t f : Bool} (h : b = true ∧ t = true ∨ b = false ∧ f = true) :
    pick b t f = true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem pick_or {b f : Bool} (h : b = true ∨ f = true) : pick b true f = true := by
  cases b
  · exact (h.resolve_left (by simp))
  · rfl

theorem beq_self (a : ℕ) : Nat.beq a a = true := Nat.beq_refl a

theorem anyb_true (goal z : ℕ) (ws : List ℕ) (h : ∃ b ∈ ws, goal = z &&& b ∨ goal = z ||| b) :
    anyb goal z ws = true := by
  induction ws with
  | nil => simp at h
  | cons c ws ih =>
    change pick (Nat.beq (z &&& c) goal) true (pick (Nat.beq (z ||| c) goal) true (anyb goal z ws)) = true
    obtain ⟨b, hb, hd⟩ := h
    rcases List.mem_cons.1 hb with rfl | hb
    · rcases hd with rfl | rfl
      · exact pick_or (.inl (beq_self _))
      · exact pick_or (.inr (pick_or (.inl (beq_self _))))
    · exact pick_or (.inr (pick_or (.inr (ih ⟨b, hb, hd⟩))))

theorem chk_true (M goal : ℕ) (ws L : List ℕ)
    (h : ∃ z ∈ L, z = goal ∨ goal = z ^^^ M ∨ ∃ b ∈ ws, goal = z &&& b ∨ goal = z ||| b) :
    chk M goal ws L = true := by
  induction L with
  | nil => simp at h
  | cons c L ih =>
    change pick (Nat.beq c goal) true (pick (Nat.beq (c ^^^ M) goal) true
      (pick (anyb goal c ws) true (chk M goal ws L))) = true
    obtain ⟨z, hz, hd⟩ := h
    rcases List.mem_cons.1 hz with rfl | hz
    · rcases hd with rfl | rfl | hd
      · exact pick_or (.inl (beq_self _))
      · exact pick_or (.inr (pick_or (.inl (beq_self _))))
      · exact pick_or (.inr (pick_or (.inr (pick_or (.inl (anyb_true _ _ _ hd))))))
    · exact pick_or (.inr (pick_or (.inr (pick_or (.inr (ih ⟨z, hz, hd⟩))))))

theorem srch_sound (M goal : ℕ) : ∀ (j : ℕ) (ws : List ℕ) (s : ℕ) (L D : List ℕ),
    Der M ws D → D.length ≤ j + 2 → goal ∈ D → goal ∉ 0 :: ws →
    (∀ d ∈ D, d ∉ 0 :: ws → Ob M ws d → d ∈ L) →
    (∀ d ∈ D, d ∉ 0 :: ws → s.testBit d = true → d ∈ L) → srch M goal j ws s L = true := by
  intro j
  induction j with
  | zero =>
    intro ws s L D hD hlen hgD hg h1 _
    change chk M goal ws L = true
    obtain ⟨z, hz, hz0, hzo⟩ := Der_first M goal ws hg D hD hgD
    have hzL := h1 z hz hz0 hzo
    by_cases hgo : Ob M ws goal
    · exact chk_true _ _ _ _ ⟨goal, h1 goal hgD hg hgo, .inl rfl⟩
    · have hzg : z ≠ goal := fun e => hgo (e ▸ hzo)
      match D, hD, hlen, hgD, hz with
      | [], _, _, hgD, _ => simp at hgD
      | [a], _, _, hgD, hz =>
        exact (hzg ((List.mem_singleton.1 hz).trans (List.mem_singleton.1 hgD).symm)).elim
      | [a, b], hD, _, hgD, hz =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hgD hz
        rcases hgD with rfl | rfl
        · exact (hgo (hD.1.resolve_left hg)).elim
        · rcases hz with rfl | rfl
          · have hb := hD.2.1
            have hgz : goal ∉ 0 :: z :: ws := by
              intro hm
              simp only [List.mem_cons] at hm hg
              rcases hm with h | h | h
              · exact hg (.inl h)
              · exact hzg h.symm
              · exact hg (.inr h)
            rcases Ob_cons (hb.resolve_left hgz) with h | h | h | h
            · exact (hgo h).elim
            · exact chk_true _ _ _ _ ⟨z, hzL, .inr (.inl h)⟩
            · exact chk_true _ _ _ _ ⟨z, hzL, .inr (.inr h)⟩
            · exact (hgz h).elim
          · exact (hzg rfl).elim
      | _ :: _ :: _ :: _, _, hlen, _, _ => simp at hlen
  | succ j ih =>
    intro ws s L D hD hlen hgD hg h1 h2
    set f : ℕ → List ℕ → Bool := fun z post => st (Nat.xor z M) fun q => ext1 q s post fun L s =>
      grow z ws s L fun L s => srch M goal j (z :: ws) s L with hf
    change loop goal f L = true
    induction L with
    | nil =>
      obtain ⟨z, hz, hz0, hzo⟩ := Der_first M goal ws hg D hD hgD
      exact absurd (h1 z hz hz0 hzo) (by simp)
    | cons z post ihL =>
      change pick (Nat.beq z goal) true (pick (f z post) true (loop goal f post)) = true
      by_cases hzD : z ∈ D ∧ z ∉ 0 :: ws
      · obtain ⟨hzD, hz0⟩ := hzD
        by_cases hzg : z = goal
        · subst hzg; exact pick_or (.inl (beq_self _))
        · refine pick_or (.inr (pick_or (.inl ?_)))
          obtain ⟨L1, s1, e1, m1, c1, t1⟩ := ext1_spec (z ^^^ M) s post
          obtain ⟨L2, s2, e2, m2, c2, t2⟩ := grow_spec z ws s1 L1
          have hfz : f z post = srch M goal j (z :: ws) s2 L2 := by
            change ext1 (z ^^^ M) s post (fun L s => grow z ws s L fun L s => srch M goal j (z :: ws) s L) = _
            rw [e1, e2]
          rw [hfz]
          have hback : ∀ d ∈ D, d ∉ 0 :: z :: ws → d ∈ z :: post → d ∈ L2 := by
            intro d _ hd hm
            rcases List.mem_cons.1 hm with rfl | hm
            · exact (hd (by simp)).elim
            · exact m2 d (m1 d hm)
          have hd0 : ∀ d, d ∉ 0 :: z :: ws → d ∉ 0 :: ws := by
            intro d hd hm
            simp only [List.mem_cons] at hd hm
            exact hd (hm.elim .inl fun h => .inr (.inr h))
          have hs1 : ∀ d ∈ D, d ∉ 0 :: z :: ws → s1.testBit d = true → d ∈ L2 := by
            intro d hdD hd hb
            rcases t1 d hb with h | h
            · exact hback d hdD hd (h2 d hdD (hd0 d hd) h)
            · exact m2 d h
          have hmem : ∀ d ∈ D.filter (fun x => decide (x ≠ z)), d ∈ D := fun d hd =>
            (List.mem_filter.1 hd).1
          refine ih (z :: ws) s2 L2 (D.filter fun x => decide (x ≠ z)) ?_ ?_ ?_ ?_ ?_ ?_
          · exact Der_filter M z D ws (z :: ws) (fun x hx => by
              rcases List.mem_cons.1 hx with rfl | hx
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) List.mem_cons_self hD
          · have : (D.filter fun x => decide (x ≠ z)).length < D.length :=
              List.length_filter_lt_length_iff_exists.2 ⟨z, hzD, by simp⟩
            omega
          · exact List.mem_filter.2 ⟨hgD, by simpa using fun e => hzg e.symm⟩
          · intro hm
            simp only [List.mem_cons] at hm hg
            rcases hm with h | h | h
            · exact hg (.inl h)
            · exact hzg h.symm
            · exact hg (.inr h)
          · intro d hd hd1 hdo
            have hdD := hmem d hd
            rcases Ob_cons hdo with h | h | ⟨b, hb, h⟩ | h
            · exact hback d hdD hd1 (h1 d hdD (hd0 d hd1) h)
            · subst h
              rcases c1 with h | h
              · exact m2 _ h
              · exact hback _ hdD hd1 (h2 _ hdD (hd0 _ hd1) h)
            · rcases h with rfl | rfl
              · exact (c2 b hb).1.elim id (hs1 _ hdD hd1)
              · exact (c2 b hb).2.elim id (hs1 _ hdD hd1)
            · exact (hd1 h).elim
          · intro d hd hd1 hb
            have hdD := hmem d hd
            rcases t2 d hb with h | h
            · exact hs1 d hdD hd1 h
            · exact h
      · refine pick_or (.inr (pick_or (.inr (ihL ?_ ?_))))
        · intro d hd hd0 ho
          rcases List.mem_cons.1 (h1 d hd hd0 ho) with rfl | h
          · exact (hzD ⟨hd, hd0⟩).elim
          · exact h
        · intro d hd hd0 hb
          rcases List.mem_cons.1 (h2 d hd hd0 hb) with rfl | h
          · exact (hzD ⟨hd, hd0⟩).elim
          · exact h

def Cov (R : ℕ) (ws : List ℕ) (w : ℕ → List Bool) : Prop :=
  ∀ i, ∃ t ∈ 0 :: ws, ∀ r < R, (w r).getD i false = t.testBit r

theorem gate_cov (R M : ℕ) (hM : ∀ r < R, M.testBit r = true) (ws : List ℕ) (w : ℕ → List Bool)
    (hw : Cov R ws w) (g : Gate) (hg : Ok g) :
    ∃ z, (z ∈ 0 :: ws ∨ Ob M ws z) ∧ ∀ r < R,
      g.op.eval (g.inputs.map fun i => (w r).getD i false) = z.testBit r := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have notv : ∀ (a r : ℕ), r < R → (a ^^^ M).testBit r = !(a.testBit r) := by
    intro a r hr
    rw [Nat.testBit_xor, hM r hr]
    cases a.testBit r <;> rfl
  have z0 : (0 : ℕ) ∈ 0 :: ws := List.mem_cons_self
  have mNot : ∀ a ∈ 0 :: ws, a ^^^ M ∈ 0 :: ws ∨ Ob M ws (a ^^^ M) := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact .inr (.inl (by simp))
    · exact .inr (.inr (.inl ⟨a, ha, rfl⟩))
  have mAnd : ∀ a ∈ 0 :: ws, ∀ b ∈ 0 :: ws, a &&& b ∈ 0 :: ws ∨ Ob M ws (a &&& b) := by
    intro a ha b hb
    rcases List.mem_cons.1 ha with rfl | ha
    · simp
    · rcases List.mem_cons.1 hb with rfl | hb
      · simp
      · exact .inr (.inr (.inr ⟨a, ha, b, hb, .inl rfl⟩))
  have mOr : ∀ a ∈ 0 :: ws, ∀ b ∈ 0 :: ws, a ||| b ∈ 0 :: ws ∨ Ob M ws (a ||| b) := by
    intro a ha b hb
    rcases List.mem_cons.1 ha with rfl | ha
    · exact .inl (by simpa using hb)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact .inl (by simpa using Or.inr ha)
      · exact .inr (.inr (.inr ⟨a, ha, b, hb, .inr rfl⟩))
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨0 ^^^ M, mNot 0 z0, fun r hr => by rw [notv 0 r hr]; simp [GateOp.eval]⟩
    · exact ⟨0, .inl z0, fun r hr => by simp [GateOp.eval]⟩
    · exact ⟨0 ^^^ M, mNot 0 z0, fun r hr => by rw [notv 0 r hr]; simp [GateOp.eval]⟩
  | [i], _ =>
    obtain ⟨a, ha, hav⟩ := hw i
    rcases hop with rfl | rfl | rfl
    · exact ⟨a, .inl ha, fun r hr => by
        simp only [List.map_cons, List.map_nil, hav r hr]; simp [GateOp.eval]⟩
    · exact ⟨a, .inl ha, fun r hr => by
        simp only [List.map_cons, List.map_nil, hav r hr]; simp [GateOp.eval]⟩
    · exact ⟨a ^^^ M, mNot a ha, fun r hr => by
        rw [notv a r hr]; simp only [List.map_cons, List.map_nil, hav r hr]; simp [GateOp.eval]⟩
  | [i, j], _ =>
    obtain ⟨a, ha, hav⟩ := hw i
    obtain ⟨b, hb, hbv⟩ := hw j
    rcases hop with rfl | rfl | rfl
    · exact ⟨a &&& b, mAnd a ha b hb, fun r hr => by
        rw [Nat.testBit_and]; simp only [List.map_cons, List.map_nil, hav r hr, hbv r hr]; simp [GateOp.eval]⟩
    · exact ⟨a ||| b, mOr a ha b hb, fun r hr => by
        rw [Nat.testBit_or]; simp only [List.map_cons, List.map_nil, hav r hr, hbv r hr]; simp [GateOp.eval]⟩
    · exact ⟨a ^^^ M, mNot a ha, fun r hr => by
        rw [notv a r hr]; simp only [List.map_cons, List.map_nil, hav r hr]; simp [GateOp.eval]⟩
  | _ :: _ :: _ :: _, hlen => simp at hlen

theorem to_der (R M : ℕ) (hM : ∀ r < R, M.testBit r = true) (o : ℕ) : ∀ (gs : List Gate) (ws : List ℕ)
    (w : ℕ → List Bool) (m : ℕ), (∀ g ∈ gs, Ok g) → (∀ r < R, (w r).length = m) → Cov R ws w →
    ∃ D, Der M ws D ∧ D.length = gs.length ∧
      ∃ t, (t ∈ 0 :: ws ∨ t ∈ D) ∧ ∀ r < R, (wiresFrom gs (w r)).getD o false = t.testBit r := by
  intro gs
  induction gs with
  | nil =>
    intro ws w m _ _ hw
    obtain ⟨t, ht, htv⟩ := hw o
    exact ⟨[], trivial, rfl, t, .inl ht, htv⟩
  | cons g gs ih =>
    intro ws w m hok hlen hw
    obtain ⟨z, hz, hzv⟩ := gate_cov R M hM ws w hw g (hok g List.mem_cons_self)
    obtain ⟨D, hD, hDl, t, ht, htv⟩ := ih (z :: ws)
      (fun r => w r ++ [g.op.eval (g.inputs.map fun i => (w r).getD i false)]) (m + 1)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) (fun r hr => by simp [hlen r hr]) (by
        intro i
        by_cases hi : i = m
        · subst hi
          refine ⟨z, by simp, fun r hr => ?_⟩
          rw [← hzv r hr]
          exact getD_snoc_len _ _ _ _ (hlen r hr)
        · obtain ⟨t, ht, htv⟩ := hw i
          refine ⟨t, ?_, fun r hr => ?_⟩
          · rcases List.mem_cons.1 ht with rfl | ht
            · simp
            · simp [ht]
          · rw [getD_snoc_ne _ _ _ _ (by rw [hlen r hr]; exact hi)]
            exact htv r hr)
    refine ⟨z :: D, ⟨hz, hD⟩, by simp [hDl], t, ?_, htv⟩
    rcases ht with ht | ht
    · rcases List.mem_cons.1 ht with rfl | ht
      · simp
      · rcases List.mem_cons.1 ht with rfl | ht
        · simp
        · exact .inl (List.mem_cons_of_mem _ ht)
    · exact .inr (List.mem_cons_of_mem _ ht)

def W0 : List ℕ := [7, 56, 448, 73, 146, 292]

def L0 : List ℕ := [511, 504, 455, 63, 438, 365, 219, 1, 79, 2, 151, 4, 295, 8, 121, 16, 186, 32, 316, 64, 457, 128, 466, 256, 484]

def raw (M : ℕ) (ws : List ℕ) : List ℕ :=
  M :: (ws.map fun a => a ^^^ M) ++ ws.flatMap fun a => ws.flatMap fun b => [a &&& b, a ||| b]

theorem raw_mem {M : ℕ} {ws : List ℕ} {d : ℕ} (h : Ob M ws d) : d ∈ raw M ws := by
  unfold raw
  rcases h with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, h⟩
  · simp
  · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, ha, rfl⟩))
  · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, List.mem_flatMap.2 ⟨b, hb, ?_⟩⟩)
    rcases h with rfl | rfl <;> simp

theorem raw_L0 : ∀ d ∈ raw 511 W0, d ∈ 0 :: W0 ∨ d ∈ L0 := by decide +kernel

def maskOf (l : List ℕ) : ℕ := l.foldr (fun c m => m ||| 2 ^ c) 0

theorem maskOf_bit (l : List ℕ) (d : ℕ) (h : (maskOf l).testBit d = true) : d ∈ l := by
  induction l with
  | nil => simp [maskOf] at h
  | cons c l ih =>
    change (maskOf l ||| 2 ^ c).testBit d = true at h
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at h
    rcases h with h | h
    · exact List.mem_cons_of_mem _ (ih h)
    · have : c = d := of_decide_eq_true h
      exact this ▸ List.mem_cons_self

def seen0 : ℕ := 6756278264645804627077973060856148259526718073466519407968896533989437490412491062901373979313941092812702659559342377725348607425508021385093378222391703

theorem seen0_eq : seen0 = maskOf (0 :: W0 ++ L0) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem searchFailed : srch 511 94 3 W0 seen0 L0 = false := by decide +kernel

theorem lower : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6126 : ℕ).testBit (4 * u.val + v.val)) C := by
  rintro ⟨C, hfan, hsize, hrep⟩
  have hsz' : C.gates.length ≤ 5 := hsize
  let rows : Fin 3 → Fin 4 := ![0, 2, 3]
  let cols : Fin 3 → Fin 4 := ![0, 1, 3]
  let au : ℕ → Fin 3 := fun r => Fin.ofNat 3 (r / 3)
  let bv : ℕ → Fin 3 := fun r => Fin.ofNat 3 (r % 3)
  let w : ℕ → List Bool := fun r => PEqualNP.Represents.oneEach (rows (au r)) (cols (bv r))
  let raw : Fin 8 → ℕ := ![7, 0, 56, 448, 73, 146, 0, 292]
  have allowed : ∀ k : Fin 8, raw k ∈ 0 :: W0 := by decide +kernel
  have pins : ∀ k : Fin 8, ∀ j : Fin 9, (w j.val).getD k.val false = (raw k).testBit j.val := by decide +kernel
  have wlen : ∀ r, (w r).length = 8 := by intro r; simp [w, PEqualNP.Represents.oneEach]
  have hcov : Cov 9 W0 w := by
    intro k
    by_cases hi : k < 8
    · exact ⟨raw ⟨k,hi⟩, allowed ⟨k,hi⟩, fun j hj => pins ⟨k,hi⟩ ⟨j,hj⟩⟩
    · refine ⟨0, List.mem_cons_self, fun j hj => ?_⟩
      rw [List.getD_eq_default _ _ (by rw [wlen]; omega)]
      simp
  have hM : ∀ j < 9, (511 : ℕ).testBit j = true := by decide +kernel
  obtain ⟨D, hD, hDl, t, ht, htv⟩ := to_der 9 511 hM C.output C.gates W0 w 8 hfan
    (fun j _ => wlen j) hcov
  have bits : ∀ j : Fin 9, (fun u v : Fin 4 => (6126 : ℕ).testBit (4 * u.val + v.val)) (rows (au j.val)) (cols (bv j.val))
      = (94 : ℕ).testBit j.val := by decide +kernel
  have htg : ∀ j < 9, t.testBit j = (94 : ℕ).testBit j := by
    intro j hj
    rw [← htv j hj]
    exact (hrep (rows (au j)) (cols (bv j))).trans (bits ⟨j,hj⟩)
  have bound : ∀ (D ws : List ℕ), (∀ x ∈ ws, x < 512) → Der 511 ws D → ∀ x ∈ D, x < 512 := by
    intro D
    induction D with
    | nil => intro ws _ _ x hx; simp at hx
    | cons d D ih =>
      intro ws hws hD x hx
      have hd : d < 512 := by
        rcases hD.1 with hd | rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl | rfl⟩
        · rcases List.mem_cons.1 hd with rfl | hd
          · norm_num
          · exact hws d hd
        · norm_num
        · exact Nat.xor_lt_two_pow (n := 9) (hws a ha) (by norm_num)
        · exact Nat.and_lt_two_pow (n := 9) a (hws b hb)
        · exact Nat.or_lt_two_pow (n := 9) (hws a ha) (hws b hb)
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hd
      · exact ih (d :: ws) (fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hd
          · exact hws y hy) hD.2 x hx
  have hW : ∀ x ∈ 0 :: W0, x < 512 := by decide
  have ht512 : t < 2 ^ 9 := by
    rcases ht with ht | ht
    · exact hW t ht
    · exact bound D W0 (fun x hx => hW x (List.mem_cons_of_mem _ hx)) hD t ht
  have hteq : t = 94 := by
    apply Nat.eq_of_testBit_eq
    intro r
    by_cases hr : r < 9
    · exact htg r hr
    · have hp : 2 ^ 9 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ht512 hp),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num) hp)]
  subst hteq
  have hg0 : (94 : ℕ) ∉ 0 :: W0 := by decide
  have := srch_sound 511 94 3 W0 seen0 L0 D hD (by omega) (ht.resolve_left hg0) hg0
    (fun d _ hd ho => (raw_L0 d (raw_mem ho)).resolve_left hd)
    (fun d _ hd hb => by
      rw [seen0_eq] at hb
      rcases List.mem_append.1 (maskOf_bit _ _ hb) with h | h
      · exact (hd h).elim
      · exact h)
  rw [searchFailed] at this
  exact Bool.noConfusion this
end Transfer
end PEqualNP.Outside.L_meta_19493_aux
theorem PEqualNP.Outside.L_meta_19493 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6126 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact PEqualNP.Outside.L_meta_19493_aux.Transfer.lower
