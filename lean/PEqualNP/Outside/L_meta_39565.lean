import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39565

namespace Lift
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

end Lift

namespace Cofactor

def H : ℕ := 2 ^ 252 - 1
def FM : ℕ := 2 ^ 504 - 1

def X : List ℕ := [0x110844211084421108442110844211084421108442110844211084421108442fffc000fffc000fffc000fffffff0003ffffffffff0003fffffffffffffffff,
  0x225089422508942250894225089422508942250894225089422508942250894fffffff0000000fffffff0003ffffffc000ffffffffffc000fffffff0003fff,
  0x446111844611184461118446111844611184461118446111844611184461118ffffffffffffff00000000003ffffffffff0003ffffffffff0003ffffffc000,
  0x87821e087821e087821e087821e087821e087821e087821e087821e087821e0ffffffffffffffffffffffffc00000000000003fffffffffffffc0000000000,
  0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000]

def R0 : ℕ := 0x3bbd0003bbd0003bbd0000000eef40000000000eef4000000000000000000003bbd0003bbd0003bbd0000000eef40000000000eef400000000000000000
def R1 : ℕ := 0x87821e087821e087821e08780000000000000021e087821e08780000000000087821e087821e087821e08780000000000000021e087821e087800000000000
def R2 : ℕ := 0xf803e00f803e00f803e00f803e00f803e00f800000000000000000000000000f803e00f803e00f803e00f803e00f803e00f800000000000000000000000000

def neg (m w : ℕ) : ℕ := (m ^^^ w) &&& m

def opsW (m a b : ℕ) : List ℕ := [a &&& b, a ||| b, a &&& neg m b, neg m a &&& b]

def sep (g w : ℕ) : ℕ := (w ^^^ (w >>> 252)) &&& g

def cov (g : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: ws => sep g w ||| cov g ws

def degen (r a b z : ℕ) : Bool :=
  let zr := z &&& r
  let ar := a &&& r
  let br := b &&& r
  zr == 0 || zr == r || zr == ar || zr == neg r ar || zr == br || zr == neg r br

def newNeed (a b z : ℕ) : List ℕ → List ℕ → List ℕ
  | r :: rs, n :: ns => (if degen r a b z then n else n - 1) :: newNeed a b z rs ns
  | _, _ => []

def okNeed (k : ℕ) : List ℕ → Bool
  | [] => true
  | n :: ns => decide (n ≤ k) && okNeed k ns

def notIn (z : ℕ) : List ℕ → Bool
  | [] => true
  | w :: ws => z != w && notIn z ws

def onZ (m g k : ℕ) (rs need : List ℕ) (rec : List ℕ → List ℕ → Bool)
    (a b base n : ℕ) (r : List ℕ) (z : ℕ) : Bool :=
  let v := sep g z ||| base
  let c0 := decide (n ≤ k) && v == g
  let c1 := decide (n + 1 ≤ k) && v ||| sep g a == g
  let c2 := decide (n + 1 ≤ k) && v ||| sep g b == g
  let c3 := decide (n + 2 ≤ k)
  (c0 || c1 || c2 || c3) && z != 0 && z != m && notIn z (a :: b :: r) &&
    notIn (neg m z) (a :: b :: r) &&
    (let nd := newNeed a b z rs need
     okNeed k nd && ((c0 && rec nd (z :: r)) || (c1 && rec nd (z :: a :: r)) ||
       (c2 && rec nd (z :: b :: r)) || (c3 && rec nd (z :: a :: b :: r))))

def onPair (m g k : ℕ) (rs need : List ℕ) (rec : List ℕ → List ℕ → Bool)
    (a b : ℕ) (r : List ℕ) : Bool :=
  (opsW m a b).any (onZ m g k rs need rec a b (cov g r) r.length r)

def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (picks rest).map (fun p => (p.1, a :: p.2))

def pairsL {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (picks rest).map (fun p => (a, p.1, p.2)) ++
      (pairsL rest).map (fun p => (p.1, p.2.1, a :: p.2.2))

def go (m g : ℕ) (rs : List ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, ws, _ => ws == [g] || ws == [neg m g]
  | k + 1, ws, need => ws == [g] || ws == [neg m g] ||
      (pairsL ws).any fun p => onPair m g k rs need (fun nd l => go m g rs k l nd) p.1 p.2.1 p.2.2

theorem bit_in {m w : ℕ} (h : w &&& m = w) (i : ℕ) : w.testBit i = (w.testBit i && m.testBit i) := by
  have := congrArg (fun t => Nat.testBit t i) h
  simp only [Nat.testBit_land] at this
  exact this.symm

theorem testBit_neg (m w i : ℕ) : (neg m w).testBit i = (m.testBit i && !w.testBit i) := by
  simp only [neg, Nat.testBit_land, Nat.testBit_xor]
  cases m.testBit i <;> cases w.testBit i <;> rfl

theorem neg_in (m w : ℕ) : neg m w &&& m = neg m w := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land, testBit_neg]
  cases m.testBit i <;> cases w.testBit i <;> rfl

theorem neg_neg' {m w : ℕ} (h : w &&& m = w) : neg m (neg m w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  have hw := bit_in h i
  simp only [testBit_neg]
  revert hw
  cases m.testBit i <;> cases w.testBit i <;> decide

theorem neg_zero' (m : ℕ) : neg m 0 = m := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [testBit_neg, Nat.zero_testBit]
  cases m.testBit i <;> rfl

theorem neg_self' (m : ℕ) : neg m m = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [testBit_neg, Nat.zero_testBit]
  cases m.testBit i <;> rfl

theorem ops_in {m a b z : ℕ} (ha : a &&& m = a) (hb : b &&& m = b) (hz : z ∈ opsW m a b) :
    z &&& m = z := by
  simp only [opsW, List.mem_cons, List.not_mem_nil, or_false] at hz
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := bit_in ha i
  have h2 := bit_in hb i
  rcases hz with rfl | rfl | rfl | rfl <;>
  · simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    revert h1 h2
    cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide

theorem ops_comm' {m a b z : ℕ} (hz : z ∈ opsW m a b) : z ∈ opsW m b a := by
  simp only [opsW, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inl (Nat.land_comm _ _)
  · exact Or.inr (Or.inl (Nat.lor_comm _ _))
  · exact Or.inr (Or.inr (Or.inr (Nat.land_comm _ _)))
  · exact Or.inr (Or.inr (Or.inl (Nat.land_comm _ _)))

theorem ops_self {m a z : ℕ} (hz : z ∈ opsW m a a) : z = a ∨ z = 0 := by
  simp only [opsW, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inl (Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_land])
  · exact Or.inl (Nat.eq_of_testBit_eq fun i => by simp [Nat.testBit_lor])
  all_goals
    right
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land, testBit_neg, Nat.zero_testBit]
    cases m.testBit i <;> cases a.testBit i <;> rfl

theorem mem1 (m a b : ℕ) : a &&& b ∈ opsW m a b := by simp [opsW]
theorem mem2 (m a b : ℕ) : a ||| b ∈ opsW m a b := by simp [opsW]
theorem mem3 (m a b : ℕ) : a &&& neg m b ∈ opsW m a b := by simp [opsW]
theorem mem4 (m a b : ℕ) : neg m a &&& b ∈ opsW m a b := by simp [opsW]

theorem signs_nb {m a b z : ℕ} (ha : a &&& m = a) (hb : b &&& m = b) (hz : z ∈ opsW m a (neg m b)) :
    ∃ u ∈ opsW m a b, z = u ∨ z = neg m u := by
  simp only [opsW, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · refine ⟨_, mem3 m a b, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)
  · refine ⟨_, mem4 m a b, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)
  · refine ⟨_, mem1 m a b, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)
  · refine ⟨_, mem2 m a b, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)

theorem signs_na {m a b z : ℕ} (ha : a &&& m = a) (hb : b &&& m = b) (hz : z ∈ opsW m (neg m a) b) :
    ∃ u ∈ opsW m a b, z = u ∨ z = neg m u := by
  simp only [opsW, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · refine ⟨_, mem4 m a b, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)
  · refine ⟨_, mem3 m a b, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)
  · refine ⟨_, mem2 m a b, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)
  · refine ⟨_, mem1 m a b, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)

theorem signs_nn {m a b z : ℕ} (ha : a &&& m = a) (hb : b &&& m = b) (hz : z ∈ opsW m (neg m a) (neg m b)) :
    ∃ u ∈ opsW m a b, z = u ∨ z = neg m u := by
  simp only [opsW, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · refine ⟨_, mem2 m a b, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)
  · refine ⟨_, mem1 m a b, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)
  · refine ⟨_, mem4 m a b, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)
  · refine ⟨_, mem3 m a b, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in ha i
    have h2 := bit_in hb i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    try (revert h1 h2; cases m.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide)

theorem signs {m a b a' b' z : ℕ} (ha : a &&& m = a) (hb : b &&& m = b)
    (ha' : a' = a ∨ a' = neg m a) (hb' : b' = b ∨ b' = neg m b) (hz : z ∈ opsW m a' b') :
    ∃ u ∈ opsW m a b, z = u ∨ z = neg m u := by
  rcases ha' with h | h <;> rcases hb' with h' | h' <;> rw [h, h'] at hz
  · exact ⟨z, hz, Or.inl rfl⟩
  · exact signs_nb ha hb hz
  · exact signs_na ha hb hz
  · exact signs_nn ha hb hz

def Held (m : ℕ) (A : Finset ℕ) (w : ℕ) : Prop :=
  w = 0 ∨ w = m ∨ ∃ a ∈ A, w = a ∨ w = neg m a

theorem held_mono {m : ℕ} {A B : Finset ℕ} {w : ℕ} (h : Held m A w) (hs : A ⊆ B) : Held m B w := by
  rcases h with h | h | ⟨a, ha, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨a, hs ha, h⟩)

theorem held_neg {m : ℕ} {A : Finset ℕ} {w : ℕ} (hA : ∀ a ∈ A, a &&& m = a) (h : Held m A w) :
    Held m A (neg m w) := by
  rcases h with h | h | ⟨a, ha, h | h⟩
  · rw [h, neg_zero']; exact Or.inr (Or.inl rfl)
  · rw [h, neg_self']; exact Or.inl rfl
  · rw [h]; exact Or.inr (Or.inr ⟨a, ha, Or.inr rfl⟩)
  · rw [h, neg_neg' (hA a ha)]; exact Or.inr (Or.inr ⟨a, ha, Or.inl rfl⟩)

def Build (m gm : ℕ) : ℕ → Finset ℕ → Prop
  | 0, A => Held m A gm
  | n + 1, A => Build m gm n A ∨
      ∃ a ∈ A, ∃ b ∈ A, ∃ z ∈ opsW m a b, ¬ Held m A z ∧ Build m gm n (insert z A)

theorem build_up {m gm : ℕ} {n : ℕ} {A : Finset ℕ} (h : Build m gm n A) :
    ∀ j, Build m gm (n + j) A := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih => exact Or.inl ih

theorem build_le {m gm : ℕ} {n N : ℕ} {A : Finset ℕ} (h : Build m gm n A) (hn : n ≤ N) :
    Build m gm N A := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact build_up h j

def stepCount (a b z : ℕ) (e : ℕ → ℕ) (r : ℕ) : ℕ := e r + (if degen r a b z then 0 else 1)

def Live (m gm : ℕ) : ℕ → Finset ℕ → (ℕ → ℕ) → Prop
  | 0, s, e => (s = {gm} ∨ s = {neg m gm}) ∧ ∀ r, e r = 0
  | k + 1, s, e => Live m gm k s e ∨
      ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ opsW m a b, z ≠ 0 ∧ z ≠ m ∧ z ∉ s ∧ neg m z ∉ s ∧
        ∃ (rest : Finset ℕ) (e' : ℕ → ℕ), s = insert a (insert b rest) ∧
          (∀ r, e r = stepCount a b z e' r) ∧ Live m gm k (insert z rest) e'

theorem compress {m gm : ℕ} (hg0 : gm ≠ 0) (hgm : gm ≠ m) (hgi : gm &&& m = gm) :
    ∀ (n : ℕ) (A : Finset ℕ), (∀ a ∈ A, a &&& m = a) → Build m gm n A →
      ∃ s ⊆ A, ∃ e, Live m gm n s e := by
  intro n
  induction n with
  | zero =>
    intro A hA h
    rcases h with h | h | ⟨a, ha, h | h⟩
    · exact absurd h hg0
    · exact absurd h hgm
    · exact ⟨{gm}, by simp [h, ha], fun _ => 0, Or.inl rfl, fun _ => rfl⟩
    · refine ⟨{a}, by simp [ha], fun _ => 0, Or.inr ?_, fun _ => rfl⟩
      rw [h, neg_neg' (hA a ha)]
  | succ n ih =>
    intro A hA h
    rcases h with h | ⟨a, ha, b, hb, z, hz, hnew, h⟩
    · obtain ⟨s, hs, e, hl⟩ := ih A hA h
      exact ⟨s, hs, e, Or.inl hl⟩
    · have hzi : z &&& m = z := ops_in (hA a ha) (hA b hb) hz
      have hA' : ∀ x ∈ insert z A, x &&& m = x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hzi
        · exact hA x hx
      obtain ⟨t, ht, e', hl⟩ := ih (insert z A) hA' h
      by_cases sub : t ⊆ A
      · exact ⟨t, sub, e', Or.inl hl⟩
      · have hzt : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | hu'
          · exact absurd hu hn
          · exact hu'
        have hzA : z ∉ A := fun hm => hnew (Or.inr (Or.inr ⟨z, hm, Or.inl rfl⟩))
        have hnA : neg m z ∉ A := fun hm =>
          hnew (Or.inr (Or.inr ⟨neg m z, hm, Or.inr (neg_neg' hzi).symm⟩))
        have hab : a ≠ b := by
          rintro rfl
          rcases ops_self hz with h1 | h1
          · exact hnew (Or.inr (Or.inr ⟨a, ha, Or.inl h1⟩))
          · exact hnew (Or.inl h1)
        let rest := t.erase z
        have hrest : rest ⊆ A := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ A := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, stepCount a b z e', Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h0 => hnew (Or.inl h0), fun h1 => hnew (Or.inr (Or.inl h1)),
          fun h2 => hzA (hs h2), fun h3 => hnA (hs h3), rest, e', rfl, fun _ => rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzt] using hl

theorem first_live {m gm : ℕ} {k : ℕ} {s : Finset ℕ} {e : ℕ → ℕ} (h : Live m gm (k + 1) s e) :
    ((s = {gm} ∨ s = {neg m gm}) ∧ ∀ r, e r = 0) ∨
      ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ opsW m a b, z ≠ 0 ∧ z ≠ m ∧ z ∉ s ∧ neg m z ∉ s ∧
        ∃ (rest : Finset ℕ) (e' : ℕ → ℕ), s = insert a (insert b rest) ∧
          (∀ r, e r = stepCount a b z e' r) ∧ Live m gm k (insert z rest) e' := by
  induction k generalizing s e with
  | zero => exact h
  | succ k ih =>
    rcases h with h | h
    · rcases ih h with h | ⟨a, ha, b, hb, hab, z, hz, h0, h1, h2, h3, rest, e', hs, he, hl⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, ha, b, hb, hab, z, hz, h0, h1, h2, h3, rest, e', hs, he, Or.inl hl⟩
    · exact Or.inr h

theorem live_card {m gm : ℕ} : ∀ {k : ℕ} {s : Finset ℕ} {e : ℕ → ℕ}, Live m gm k s e → s.card ≤ k + 1
  | 0, s, e, h => by rcases h.1 with rfl | rfl <;> simp
  | k + 1, s, e, h => by
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, h0, h1, h2, h3, rest, e', rfl, he, hl⟩
    · exact (live_card h).trans (by omega)
    · have hzr : z ∉ rest := fun hm => h2 (by simp [hm])
      have ht := live_card hl
      rw [Finset.card_insert_of_notMem hzr] at ht
      have c1 := Finset.card_insert_le a (insert b rest)
      have c2 := Finset.card_insert_le b rest
      omega

theorem live_count {m gm : ℕ} : ∀ {k : ℕ} {s : Finset ℕ} {e : ℕ → ℕ}, Live m gm k s e → ∀ r, e r ≤ k
  | 0, s, e, h => by intro r; rw [h.2 r]
  | k + 1, s, e, h => by
    intro r
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, h0, h1, h2, h3, rest, e', hs, he, hl⟩
    · exact (live_count h r).trans (by omega)
    · rw [he r, stepCount]
      have := live_count hl r
      split <;> omega

def WorldOK (m gm : ℕ) : Prop := gm = H &&& m ∧ ∀ i < 252, m.testBit i = m.testBit (i + 252)

theorem testBit_H (i : ℕ) : H.testBit i = decide (i < 252) := by
  show (2 ^ 252 - 1).testBit i = decide (i < 252)
  exact Nat.testBit_two_pow_sub_one _ _

theorem ops_dif {m a b z i j : ℕ} (hi : m.testBit i = true) (hj : m.testBit j = true)
    (hz : z ∈ opsW m a b) (hd : z.testBit i ≠ z.testBit j) :
    a.testBit i ≠ a.testBit j ∨ b.testBit i ≠ b.testBit j := by
  simp only [opsW, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  apply hd
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg, hi, hj, h1, h2]

theorem live_sep {m gm i : ℕ} (hi : m.testBit i = true) (hj : m.testBit (i + 252) = true)
    (hg : gm.testBit i ≠ gm.testBit (i + 252))
    (hg' : (neg m gm).testBit i ≠ (neg m gm).testBit (i + 252)) :
    ∀ {k : ℕ} {s : Finset ℕ} {e : ℕ → ℕ}, Live m gm k s e →
      ∃ w ∈ s, w.testBit i ≠ w.testBit (i + 252)
  | 0, s, e, h => by
    rcases h.1 with rfl | rfl
    · exact ⟨gm, by simp, hg⟩
    · exact ⟨neg m gm, by simp, hg'⟩
  | k + 1, s, e, h => by
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, h0, h1, h2, h3, rest, e', hs, he, hl⟩
    · exact live_sep hi hj hg hg' h
    · obtain ⟨w, hw, hd⟩ := live_sep hi hj hg hg' hl
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases ops_dif hi hj hz hd with hd | hd
        · exact ⟨a, ha, hd⟩
        · exact ⟨b, hb, hd⟩
      · exact ⟨w, by rw [hs]; simp [hw], hd⟩

theorem testBit_sep (g w j : ℕ) :
    (sep g w).testBit j = ((w.testBit j ^^ w.testBit (252 + j)) && g.testBit j) := by
  simp [sep, Nat.testBit_land, Nat.testBit_xor, Nat.testBit_shiftRight]

theorem testBit_cov (g j : ℕ) : ∀ ws : List ℕ,
    (cov g ws).testBit j = true ↔ ∃ w ∈ ws, (sep g w).testBit j = true
  | [] => by simp [cov]
  | w :: ws => by
    simp only [cov, Nat.testBit_lor, Bool.or_eq_true, testBit_cov g j ws, List.mem_cons]
    constructor
    · rintro (h | ⟨u, hu, h⟩)
      · exact ⟨w, Or.inl rfl, h⟩
      · exact ⟨u, Or.inr hu, h⟩
    · rintro ⟨u, rfl | hu, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨u, hu, h⟩

theorem live_cut {m gm : ℕ} (W : WorldOK m gm) {k : ℕ} {ws : List ℕ} {e : ℕ → ℕ}
    (h : Live m gm k ws.toFinset e) : cov gm ws = gm := by
  obtain ⟨hg, hw⟩ := W
  apply Nat.eq_of_testBit_eq
  intro j
  cases hgj : gm.testBit j
  · cases hc : (cov gm ws).testBit j
    · rfl
    · obtain ⟨w, _, hs⟩ := (testBit_cov gm j ws).mp hc
      rw [testBit_sep, hgj, Bool.and_false] at hs
      exact absurd hs (by simp)
  · have hj : j < 252 ∧ m.testBit j = true := by
      rw [hg, Nat.testBit_land, testBit_H] at hgj
      simpa using hgj
    have hm2 : m.testBit (j + 252) = true := by rw [← hw j hj.1]; exact hj.2
    have hg2 : gm.testBit (j + 252) = false := by
      rw [hg, Nat.testBit_land, testBit_H]; simp
    have d1 : gm.testBit j ≠ gm.testBit (j + 252) := by rw [hgj, hg2]; simp
    have d2 : (neg m gm).testBit j ≠ (neg m gm).testBit (j + 252) := by
      rw [testBit_neg, testBit_neg, hgj, hg2, hj.2, hm2]; simp
    obtain ⟨w, hwm, hd⟩ := live_sep hj.2 hm2 d1 d2 h
    apply (testBit_cov gm j ws).mpr
    refine ⟨w, List.mem_toFinset.mp hwm, ?_⟩
    rw [testBit_sep, hgj, Nat.add_comm 252 j]
    revert hd
    cases w.testBit j <;> cases w.testBit (j + 252) <;> simp

theorem picks_mem {α : Type} {a : α} : ∀ {ws : List α}, a ∈ ws →
    ∃ r, (a, r) ∈ picks ws ∧ ws.Perm (a :: r)
  | [], h => by simp at h
  | x :: xs, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨xs, by simp [picks], List.Perm.refl _⟩
    · obtain ⟨r, hm, hp⟩ := picks_mem h
      refine ⟨x :: r, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (List.Perm.swap _ _ _)

theorem pairs_mem {α : Type} {a b : α} (hab : a ≠ b) : ∀ {ws : List α}, a ∈ ws → b ∈ ws →
    ∃ r, ((a, b, r) ∈ pairsL ws ∨ (b, a, r) ∈ pairsL ws) ∧ ws.Perm (a :: b :: r)
  | [], ha, _ => by simp at ha
  | x :: xs, ha, hb => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · have hb' : b ∈ xs := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
      obtain ⟨r, hm, hp⟩ := picks_mem hb'
      exact ⟨r, Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons _⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨r, hm, hp⟩ := picks_mem ha'
        exact ⟨r, Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons _).trans (List.Perm.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := pairs_mem hab ha' hb'
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans
          ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact Or.inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact Or.inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

theorem recover {ws r : List ℕ} {a b : ℕ} {rest : Finset ℕ} (hn : ws.Nodup)
    (hp : ws.Perm (a :: b :: r)) (hs : ws.toFinset = insert a (insert b rest)) :
    ∃ kept : List ℕ, (kept = r ∨ kept = a :: r ∨ kept = b :: r ∨ kept = a :: b :: r) ∧
      kept.Nodup ∧ kept.toFinset = rest := by
  have hn' := hp.nodup_iff.mp hn
  simp only [List.nodup_cons, List.mem_cons, not_or] at hn'
  obtain ⟨⟨hab, har⟩, hbr, hr⟩ := hn'
  have key : ∀ v, v ∈ r ↔ v ∈ rest ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have e1 : v ∈ ws.toFinset ↔ v ∈ insert a (insert b rest) := by rw [hs]
    simp only [List.mem_toFinset, hp.mem_iff, List.mem_cons, Finset.mem_insert] at e1
    constructor
    · intro hv
      have hva : v ≠ a := fun h => har (h ▸ hv)
      have hvb : v ≠ b := fun h => hbr (h ▸ hv)
      refine ⟨?_, hva, hvb⟩
      rcases e1.mp (Or.inr (Or.inr hv)) with h | h | h
      · exact absurd h hva
      · exact absurd h hvb
      · exact h
    · rintro ⟨hv, hva, hvb⟩
      rcases e1.mpr (Or.inr (Or.inr hv)) with h | h | h
      · exact absurd h hva
      · exact absurd h hvb
      · exact h
  by_cases ha : a ∈ rest <;> by_cases hb : b ∈ rest
  · refine ⟨a :: b :: r, Or.inr (Or.inr (Or.inr rfl)), ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, not_or]; exact ⟨⟨hab, har⟩, hbr, hr⟩
    · ext v; simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, key]
      constructor
      · rintro (rfl | rfl | ⟨h, -⟩) <;> assumption
      · intro hv; by_cases h1 : v = a
        · exact Or.inl h1
        · by_cases h2 : v = b
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr ⟨hv, h1, h2⟩)
  · refine ⟨a :: r, Or.inr (Or.inl rfl), ?_, ?_⟩
    · simp only [List.nodup_cons]; exact ⟨har, hr⟩
    · ext v; simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, key]
      constructor
      · rintro (rfl | ⟨h, -⟩) <;> assumption
      · intro hv; by_cases h1 : v = a
        · exact Or.inl h1
        · have h2 : v ≠ b := fun h => hb (h ▸ hv)
          exact Or.inr ⟨hv, h1, h2⟩
  · refine ⟨b :: r, Or.inr (Or.inr (Or.inl rfl)), ?_, ?_⟩
    · simp only [List.nodup_cons]; exact ⟨hbr, hr⟩
    · ext v; simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, key]
      constructor
      · rintro (rfl | ⟨h, -⟩) <;> assumption
      · intro hv; by_cases h2 : v = b
        · exact Or.inl h2
        · have h1 : v ≠ a := fun h => ha (h ▸ hv)
          exact Or.inr ⟨hv, h1, h2⟩
  · refine ⟨r, Or.inl rfl, hr, ?_⟩
    ext v; simp only [List.mem_toFinset, key]
    constructor
    · rintro ⟨h, -⟩; exact h
    · intro hv
      exact ⟨hv, fun h => ha (h ▸ hv), fun h => hb (h ▸ hv)⟩

theorem singleton_list {x : ℕ} {ws : List ℕ} (hn : ws.Nodup) (hs : ws.toFinset = {x}) : ws = [x] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  match ws, hc with
  | [y], _ => simpa using hs

def Cover : List ℕ → List ℕ → (ℕ → ℕ) → Prop
  | r :: rs, n :: ns, e => n ≤ e r ∧ Cover rs ns e
  | _, _, _ => True

theorem need_step (a b z k : ℕ) (e' : ℕ → ℕ) (he' : ∀ r, e' r ≤ k) :
    ∀ (rs need : List ℕ) (e : ℕ → ℕ), (∀ r, e r = stepCount a b z e' r) → Cover rs need e →
      Cover rs (newNeed a b z rs need) e' ∧ okNeed k (newNeed a b z rs need) = true
  | [], need, e, _, _ => by cases need <;> exact ⟨trivial, rfl⟩
  | r :: rs, [], e, _, _ => ⟨trivial, rfl⟩
  | r :: rs, n :: ns, e, he, hc => by
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨c, o⟩ := need_step a b z k e' he' rs ns e he h2
    have hr := he r
    have hk := he' r
    unfold stepCount at hr
    have key : (if degen r a b z = true then n else n - 1) ≤ e' r := by
      by_cases hd : degen r a b z = true
      · rw [if_pos hd]; rw [if_pos hd] at hr; omega
      · rw [if_neg hd]; rw [if_neg hd] at hr; omega
    refine ⟨?_, ?_⟩
    · simp only [newNeed, Cover]; exact ⟨key, c⟩
    · simp only [newNeed, okNeed, o, Bool.and_true, decide_eq_true_eq]
      omega

theorem notIn_iff (z : ℕ) : ∀ l : List ℕ, notIn z l = true ↔ z ∉ l
  | [] => by simp [notIn]
  | w :: ws => by simp [notIn, notIn_iff z ws]

theorem onZ_of {m g k : ℕ} {rs need : List ℕ} {rec : List ℕ → List ℕ → Bool} {a b z : ℕ}
    {r : List ℕ} (hz0 : z ≠ 0) (hzm : z ≠ m) (hf1 : z ∉ a :: b :: r) (hf2 : neg m z ∉ a :: b :: r)
    (hok : okNeed k (newNeed a b z rs need) = true)
    (hk : (r.length ≤ k ∧ sep g z ||| cov g r = g ∧ rec (newNeed a b z rs need) (z :: r) = true) ∨
      (r.length + 1 ≤ k ∧ sep g z ||| cov g r ||| sep g a = g ∧
        rec (newNeed a b z rs need) (z :: a :: r) = true) ∨
      (r.length + 1 ≤ k ∧ sep g z ||| cov g r ||| sep g b = g ∧
        rec (newNeed a b z rs need) (z :: b :: r) = true) ∨
      (r.length + 2 ≤ k ∧ rec (newNeed a b z rs need) (z :: a :: b :: r) = true)) :
    onZ m g k rs need rec a b (cov g r) r.length r z = true := by
  have e1 := (notIn_iff z (a :: b :: r)).mpr hf1
  have e2 := (notIn_iff (neg m z) (a :: b :: r)).mpr hf2
  unfold onZ
  rcases hk with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
  · have h1' : r.length + 2 ≤ k ∨ ¬ r.length + 2 ≤ k := Classical.em _
    simp [e1, e2, hok, h1, h2, h3, hz0, hzm]
  · have h1' : r.length ≤ k := by omega
    simp [e1, e2, hok, h1, h1', h2, h3, hz0, hzm]
  · have h1' : r.length ≤ k := by omega
    simp [e1, e2, hok, h1, h1', h2, h3, hz0, hzm]
  · have h1' : r.length ≤ k := by omega
    have h1'' : r.length + 1 ≤ k := by omega
    simp [e1, e2, hok, h1, h1', h1'', h3, hz0, hzm]

theorem degen_comm (r a b z : ℕ) : degen r a b z = degen r b a z := by
  simp only [degen]
  cases (z &&& r == a &&& r) <;> cases (z &&& r == neg r (a &&& r)) <;>
    cases (z &&& r == b &&& r) <;> cases (z &&& r == neg r (b &&& r)) <;> simp

theorem step_ok {m gm : ℕ} (W : WorldOK m gm) (rs : List ℕ) (k : ℕ)
    (ih : ∀ (ws need : List ℕ) (e : ℕ → ℕ), ws.Nodup → Live m gm k ws.toFinset e →
      Cover rs need e → go m gm rs k ws need = true)
    {ws need r : List ℕ} {e e' : ℕ → ℕ} {a b z : ℕ} {rest : Finset ℕ}
    (hn : ws.Nodup) (hp : ws.Perm (a :: b :: r)) (hc : Cover rs need e)
    (hz : z ∈ opsW m a b) (h0 : z ≠ 0) (h1 : z ≠ m) (h2 : z ∉ ws.toFinset)
    (h3 : neg m z ∉ ws.toFinset) (hs : ws.toFinset = insert a (insert b rest))
    (he : ∀ q, e q = stepCount a b z e' q) (hl : Live m gm k (insert z rest) e') :
    onPair m gm k rs need (fun nd l => go m gm rs k l nd) a b r = true := by
  obtain ⟨kept, hkc, hkn, hkf⟩ := recover hn hp hs
  have hzk : z ∉ kept := by
    intro hm
    apply h2
    rw [hs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hkf ▸ List.mem_toFinset.mpr hm))
  have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hzk, hkn⟩
  have hfin : (z :: kept).toFinset = insert z rest := by simp [hkf]
  have hl' : Live m gm k (z :: kept).toFinset e' := hfin ▸ hl
  have card := live_card hl'
  rw [List.toFinset_card_of_nodup hnd, List.length_cons] at card
  have cut := live_cut W hl'
  obtain ⟨hcov, hok⟩ := need_step a b z k e' (live_count hl) rs need e he hc
  have hrec := ih (z :: kept) _ e' hnd hl' hcov
  have hmem : ∀ v, v ∈ ws ↔ v ∈ a :: b :: r := fun v => hp.mem_iff
  have f1 : z ∉ a :: b :: r := fun hm => h2 (List.mem_toFinset.mpr ((hmem z).mpr hm))
  have f2 : neg m z ∉ a :: b :: r := fun hm => h3 (List.mem_toFinset.mpr ((hmem _).mpr hm))
  unfold onPair
  apply List.any_eq_true.mpr
  refine ⟨z, hz, onZ_of h0 h1 f1 f2 hok ?_⟩
  rcases hkc with rfl | rfl | rfl | rfl
  · left
    simp only [cov] at cut
    exact ⟨by simp at card; omega, cut, hrec⟩
  · right; left
    simp only [cov] at cut
    refine ⟨by simp at card; omega, ?_, hrec⟩
    rw [Nat.lor_assoc, Nat.lor_comm (cov gm r)]; exact cut
  · right; right; left
    simp only [cov] at cut
    refine ⟨by simp at card; omega, ?_, hrec⟩
    rw [Nat.lor_assoc, Nat.lor_comm (cov gm r)]; exact cut
  · right; right; right
    exact ⟨by simp at card; omega, hrec⟩

theorem go_complete {m gm : ℕ} (W : WorldOK m gm) (rs : List ℕ) :
    ∀ (k : ℕ) (ws need : List ℕ) (e : ℕ → ℕ), ws.Nodup → Live m gm k ws.toFinset e →
      Cover rs need e → go m gm rs k ws need = true
  | 0, ws, need, e, hn, hl, _ => by
    rcases hl.1 with h | h <;> simp [go, singleton_list hn h]
  | k + 1, ws, need, e, hn, hl, hc => by
    rcases first_live hl with ⟨h, _⟩ | ⟨a, ha, b, hb, hab, z, hz, h0, h1, h2, h3, rest, e', hs, he, htl⟩
    · rcases h with h | h <;> simp [go, singleton_list hn h]
    · have ih := go_complete W rs k
      obtain ⟨r, hm, hp⟩ := pairs_mem hab (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
      simp only [go, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with hm | hm
      · exact ⟨(a, b, r), hm, step_ok W rs k ih hn hp hc hz h0 h1 h2 h3 hs he htl⟩
      · refine ⟨(b, a, r), hm, step_ok W rs k ih hn (hp.trans (List.Perm.swap _ _ _)) hc
          (ops_comm' hz) h0 h1 h2 h3 (by rw [hs, Finset.insert_comm]) ?_ htl⟩
        intro q
        rw [he q, stepCount, stepCount, degen_comm]

theorem search_refutes {m gm : ℕ} (W : WorldOK m gm) (hg0 : gm ≠ 0) (hgm : gm ≠ m)
    (rs need inputs : List ℕ) (hnd : inputs.Nodup) (hin : ∀ a ∈ inputs, a &&& m = a) (N : ℕ)
    (hS : ∀ ws ∈ inputs.sublists, ws.length ≤ N + 1 → cov gm ws = gm → go m gm rs N ws need = false)
    (hC : ∀ s e, s ⊆ inputs.toFinset → Live m gm N s e → Cover rs need e)
    (hB : Build m gm N inputs.toFinset) : False := by
  classical
  have hgi : gm &&& m = gm := by
    rw [W.1]; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land]; cases H.testBit i <;> cases m.testBit i <;> rfl
  obtain ⟨s, hs, e, hl⟩ := compress hg0 hgm hgi N inputs.toFinset
    (fun a ha => hin a (List.mem_toFinset.mp ha)) hB
  let ws := inputs.filter (fun v => decide (v ∈ s))
  have hws : ws.toFinset = s := by
    ext v
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hv => List.mem_toFinset.mp (hs hv)
  have hn : ws.Nodup := hnd.filter _
  have hl' : Live m gm N ws.toFinset e := hws ▸ hl
  have card := live_card hl'
  rw [List.toFinset_card_of_nodup hn] at card
  have h := hS ws (List.mem_sublists.mpr List.filter_sublist) card (live_cut W hl')
  rw [go_complete W rs N ws need e hn hl' (hC s e hs hl)] at h
  exact Bool.noConfusion h

theorem land_in (a r : ℕ) : (a &&& r) &&& r = a &&& r := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_land]
  cases a.testBit i <;> cases r.testBit i <;> rfl

theorem const_cases {r a b z : ℕ} (ha : a &&& r = a) (hb : b &&& r = b) (hz : z ∈ opsW r a b)
    (hc : a = 0 ∨ a = r ∨ b = 0 ∨ b = r) :
    z = 0 ∨ z = r ∨ z = a ∨ z = neg r a ∨ z = b ∨ z = neg r b := by
  simp only [opsW, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hc with h | h | h | h <;> rw [h] at hz ⊢ <;> rcases hz with rfl | rfl | rfl | rfl
  all_goals first
    | (refine Or.inl ?_
       apply Nat.eq_of_testBit_eq; intro i
       have h1 := bit_in ha i
       have h2 := bit_in hb i
       simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg, Nat.zero_testBit]
       all_goals (revert h1 h2; cases r.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide))
    | (refine Or.inr (Or.inl ?_)
       apply Nat.eq_of_testBit_eq; intro i
       have h1 := bit_in ha i
       have h2 := bit_in hb i
       simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg, Nat.zero_testBit]
       all_goals (revert h1 h2; cases r.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide))
    | (refine Or.inr (Or.inr (Or.inl ?_))
       apply Nat.eq_of_testBit_eq; intro i
       have h1 := bit_in ha i
       have h2 := bit_in hb i
       simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg, Nat.zero_testBit]
       all_goals (revert h1 h2; cases r.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide))
    | (refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
       apply Nat.eq_of_testBit_eq; intro i
       have h1 := bit_in ha i
       have h2 := bit_in hb i
       simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg, Nat.zero_testBit]
       all_goals (revert h1 h2; cases r.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide))
    | (refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
       apply Nat.eq_of_testBit_eq; intro i
       have h1 := bit_in ha i
       have h2 := bit_in hb i
       simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg, Nat.zero_testBit]
       all_goals (revert h1 h2; cases r.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide))
    | (refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
       apply Nat.eq_of_testBit_eq; intro i
       have h1 := bit_in ha i
       have h2 := bit_in hb i
       simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg, Nat.zero_testBit]
       all_goals (revert h1 h2; cases r.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide))

theorem held_six {m : ℕ} {A : Finset ℕ} {a b z : ℕ} (hA : ∀ x ∈ A, x &&& m = x)
    (ha : Held m A a) (hb : Held m A b)
    (h : z = 0 ∨ z = m ∨ z = a ∨ z = neg m a ∨ z = b ∨ z = neg m b) : Held m A z := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact ha
  · exact held_neg hA ha
  · exact hb
  · exact held_neg hA hb

theorem proj_ops {r a b z : ℕ} (hr : r &&& FM = r) (hz : z ∈ opsW FM a b) :
    z &&& r ∈ opsW r (a &&& r) (b &&& r) := by
  simp only [opsW, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl
  · refine Or.inl ?_
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    cases r.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl
  · refine Or.inr (Or.inl ?_)
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    cases r.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl
  · refine Or.inr (Or.inr (Or.inl ?_))
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in hr i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    revert h1
    cases r.testBit i <;> cases FM.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide
  · refine Or.inr (Or.inr (Or.inr ?_))
    apply Nat.eq_of_testBit_eq; intro i
    have h1 := bit_in hr i
    simp only [Nat.testBit_land, Nat.testBit_lor, testBit_neg]
    revert h1
    cases r.testBit i <;> cases FM.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> decide

theorem proj_neg {r w : ℕ} (hr : r &&& FM = r) : neg FM w &&& r = neg r (w &&& r) := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := bit_in hr i
  simp only [Nat.testBit_land, testBit_neg]
  revert h1
  cases r.testBit i <;> cases FM.testBit i <;> cases w.testBit i <;> decide

theorem degen_six {r a b z : ℕ} (hd : degen r a b z = true) :
    z &&& r = 0 ∨ z &&& r = r ∨ z &&& r = a &&& r ∨ z &&& r = neg r (a &&& r) ∨
      z &&& r = b &&& r ∨ z &&& r = neg r (b &&& r) := by
  simp only [degen, Bool.or_eq_true, beq_iff_eq] at hd
  rcases hd with ((((h | h) | h) | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem degen_of_six {r a b z : ℕ}
    (h : z &&& r = 0 ∨ z &&& r = r ∨ z &&& r = a &&& r ∨ z &&& r = neg r (a &&& r) ∨
      z &&& r = b &&& r ∨ z &&& r = neg r (b &&& r)) : degen r a b z = true := by
  simp only [degen]
  rcases h with h | h | h | h | h | h <;> simp [h]

theorem project {r : ℕ} (hr : r &&& FM = r) :
    ∀ {k : ℕ} {s : Finset ℕ} {e : ℕ → ℕ} (A : Finset ℕ), Live FM H k s e →
      (∀ a ∈ A, a &&& r = a) → (∀ w ∈ s, Held r A (w &&& r)) → Build r (H &&& r) (e r) A
  | 0, s, e, A, h, hA, hs => by
    rw [h.2 r]
    show Held r A (H &&& r)
    rcases h.1 with h1 | h1
    · exact hs H (by simp [h1])
    · have := held_neg hA (hs (neg FM H) (by simp [h1]))
      rwa [proj_neg hr, neg_neg' (land_in H r)] at this
  | k + 1, s, e, A, h, hA, hs => by
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, h0, h1, h2, h3, rest, e', hsr, he, hl⟩
    · exact project hr A h hA hs
    · have hra : Held r A (a &&& r) := hs a (by rw [hsr]; simp)
      have hrb : Held r A (b &&& r) := hs b (by rw [hsr]; simp)
      have hrest : ∀ w ∈ rest, Held r A (w &&& r) := fun w hw => hs w (by rw [hsr]; simp [hw])
      have hz' := proj_ops hr hz
      rw [he r, stepCount]
      by_cases hd : degen r a b z = true
      · rw [if_pos hd, Nat.add_zero]
        have hzh : Held r A (z &&& r) := held_six hA hra hrb (degen_six hd)
        refine project hr A hl hA ?_
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hzh
        · exact hrest w hw
      · rw [if_neg hd]
        have nc : ¬ (a &&& r = 0 ∨ a &&& r = r ∨ b &&& r = 0 ∨ b &&& r = r) := by
          intro hc
          exact hd (degen_of_six (const_cases (land_in a r) (land_in b r) hz' hc))
        rcases hra with h4 | h4 | ⟨x, hx, hxa⟩
        · exact absurd (Or.inl h4) nc
        · exact absurd (Or.inr (Or.inl h4)) nc
        rcases hrb with h5 | h5 | ⟨y, hy, hyb⟩
        · exact absurd (Or.inr (Or.inr (Or.inl h5))) nc
        · exact absurd (Or.inr (Or.inr (Or.inr h5))) nc
        obtain ⟨u, hu, hzu⟩ := signs (hA x hx) (hA y hy) hxa hyb hz'
        by_cases hhu : Held r A u
        · have hzh : Held r A (z &&& r) := by
            rcases hzu with h6 | h6
            · rw [h6]; exact hhu
            · rw [h6]; exact held_neg hA hhu
          refine build_le (project hr A hl hA ?_) (Nat.le_succ _)
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hzh
          · exact hrest w hw
        · have hui : u &&& r = u := ops_in (hA x hx) (hA y hy) hu
          have hA' : ∀ v ∈ insert u A, v &&& r = v := by
            intro v hv
            rcases Finset.mem_insert.mp hv with rfl | hv
            · exact hui
            · exact hA v hv
          have tail := project hr (insert u A) hl hA' (by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · rcases hzu with h6 | h6
              · rw [h6]; exact Or.inr (Or.inr ⟨u, Finset.mem_insert_self _ _, Or.inl rfl⟩)
              · rw [h6]; exact Or.inr (Or.inr ⟨u, Finset.mem_insert_self _ _, Or.inr rfl⟩)
            · exact held_mono (hrest w hw) (Finset.subset_insert _ _))
          exact Or.inr ⟨x, hx, y, hy, u, hu, hhu, tail⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Legal (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def isBin (g : Gate) : Bool := match g.op with
  | GateOp.not => false
  | _ => true

def binCost (gs : List Gate) : ℕ := (gs.filter isBin).length

def rd (w : List ℕ) (i : ℕ) : ℕ := w.getD i 0

def gword (w : List ℕ) (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [] => FM
  | GateOp.and, [i] => rd w i
  | GateOp.and, i :: j :: _ => rd w i &&& rd w j
  | GateOp.or, [] => 0
  | GateOp.or, [i] => rd w i
  | GateOp.or, i :: j :: _ => rd w i ||| rd w j
  | GateOp.not, [] => FM
  | GateOp.not, i :: _ => neg FM (rd w i)
  | _, _ => 0

def wstep (w : List ℕ) (g : Gate) : List ℕ := w ++ [gword w g]

def bstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 10000 in
theorem testBit_FM (j : ℕ) : FM.testBit j = decide (j < 504) := by
  show (2 ^ 504 - 1).testBit j = decide (j < 504)
  exact Nat.testBit_two_pow_sub_one _ _

theorem read_bit (w : List ℕ) (i j : ℕ) :
    (w.map (fun v => v.testBit j)).getD i false = (rd w i).testBit j := by
  unfold rd
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

theorem gate_bit (w : List ℕ) (g : Gate) (hg : Legal g) (j : ℕ) (hj : j < 504) :
    (gword w g).testBit j = g.op.eval (g.inputs.map fun i => (w.map (fun v => v.testBit j)).getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only at hop hl
  have hF : FM.testBit j = true := by rw [testBit_FM]; simp [hj]
  match ins, hl with
  | [], _ =>
    rcases hop with rfl | rfl | rfl <;> simp only [gword, GateOp.eval, List.map_cons, List.map_nil, read_bit, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons, List.headD_nil, id_eq, Bool.and_true, Bool.or_false, testBit_neg, hF, Bool.true_and, Nat.testBit_land, Nat.testBit_lor, Nat.zero_testBit, Bool.not_false]
  | [i], _ =>
    rcases hop with rfl | rfl | rfl <;>
      simp only [gword, GateOp.eval, List.map_cons, List.map_nil, read_bit, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons, List.headD_nil, id_eq, Bool.and_true, Bool.or_false, testBit_neg, hF, Bool.true_and, Nat.testBit_land, Nat.testBit_lor, Nat.zero_testBit, Bool.not_false]
  | [i, k], _ =>
    rcases hop with rfl | rfl | rfl <;>
      simp only [gword, GateOp.eval, List.map_cons, List.map_nil, read_bit, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons, List.headD_nil, id_eq, Bool.and_true, Bool.or_false, testBit_neg, hF, Bool.true_and, Nat.testBit_land, Nat.testBit_lor, Nat.zero_testBit, Bool.not_false]

theorem fold_bit (j : ℕ) (hj : j < 504) : ∀ (gs : List Gate) (w : List ℕ), (∀ g ∈ gs, Legal g) →
    gs.foldl bstep (w.map (fun v => v.testBit j)) = (gs.foldl wstep w).map (fun v => v.testBit j)
  | [], w, _ => rfl
  | g :: gs, w, hg => by
    simp only [List.foldl_cons]
    have e : bstep (w.map (fun v => v.testBit j)) g = (wstep w g).map (fun v => v.testBit j) := by
      simp only [bstep, wstep, List.map_append, List.map_cons, List.map_nil]
      rw [gate_bit w g (hg g (by simp)) j hj]
    rw [e]
    exact fold_bit j hj gs _ (fun g' h' => hg g' (List.mem_cons_of_mem _ h'))

theorem rd_facts {w : List ℕ} {A : Finset ℕ} (hw : ∀ u ∈ w, u &&& FM = u ∧ Held FM A u) (i : ℕ) :
    rd w i &&& FM = rd w i ∧ Held FM A (rd w i) := by
  unfold rd
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hw _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
    exact ⟨by simp, Or.inl rfl⟩

theorem bin2 {A : Finset ℕ} {u v z : ℕ} (hA : ∀ a ∈ A, a &&& FM = a) (hu : u &&& FM = u)
    (hv : v &&& FM = v) (hu' : Held FM A u) (hv' : Held FM A v) (hz : z ∈ opsW FM u v) :
    Held FM A z ∨ ∃ x ∈ A, ∃ y ∈ A, ∃ t ∈ opsW FM x y, ¬ Held FM A t ∧ (z = t ∨ z = neg FM t) := by
  by_cases hc : u = 0 ∨ u = FM ∨ v = 0 ∨ v = FM
  · exact Or.inl (held_six hA hu' hv' (const_cases hu hv hz hc))
  · push_neg at hc
    obtain ⟨c1, c2, c3, c4⟩ := hc
    rcases hu' with h | h | ⟨x, hx, hxu⟩
    · exact absurd h c1
    · exact absurd h c2
    rcases hv' with h | h | ⟨y, hy, hyv⟩
    · exact absurd h c3
    · exact absurd h c4
    obtain ⟨t, ht, hzt⟩ := signs (hA x hx) (hA y hy) hxu hyv hz
    by_cases hh : Held FM A t
    · left
      rcases hzt with h | h
      · rw [h]; exact hh
      · rw [h]; exact held_neg hA hh
    · exact Or.inr ⟨x, hx, y, hy, t, ht, hh, hzt⟩

theorem gclass {w : List ℕ} {A : Finset ℕ} {g : Gate} (hg : Legal g)
    (hw : ∀ u ∈ w, u &&& FM = u ∧ Held FM A u) (hA : ∀ a ∈ A, a &&& FM = a) :
    gword w g &&& FM = gword w g ∧ (Held FM A (gword w g) ∨ (isBin g = true ∧
      ∃ x ∈ A, ∃ y ∈ A, ∃ t ∈ opsW FM x y, ¬ Held FM A t ∧
        (gword w g = t ∨ gword w g = neg FM t))) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only at hop hl
  have hFF : FM &&& FM = FM := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_land]
  match ins, hl with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨hFF, Or.inl (Or.inr (Or.inl rfl))⟩
    · exact ⟨by simp [gword], Or.inl (Or.inl rfl)⟩
    · exact ⟨hFF, Or.inl (Or.inr (Or.inl rfl))⟩
  | [i], _ =>
    obtain ⟨r1, r2⟩ := rd_facts hw i
    rcases hop with rfl | rfl | rfl
    · exact ⟨r1, Or.inl r2⟩
    · exact ⟨r1, Or.inl r2⟩
    · exact ⟨neg_in _ _, Or.inl (held_neg hA r2)⟩
  | [i, k], _ =>
    obtain ⟨r1, r2⟩ := rd_facts hw i
    obtain ⟨s1, s2⟩ := rd_facts hw k
    rcases hop with rfl | rfl | rfl
    · have hm := mem1 FM (rd w i) (rd w k)
      refine ⟨ops_in r1 s1 hm, ?_⟩
      rcases bin2 hA r1 s1 r2 s2 hm with h | h
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩
    · have hm := mem2 FM (rd w i) (rd w k)
      refine ⟨ops_in r1 s1 hm, ?_⟩
      rcases bin2 hA r1 s1 r2 s2 hm with h | h
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩
    · exact ⟨neg_in _ _, Or.inl (held_neg hA r2)⟩

theorem compile (o : ℕ) : ∀ (gs : List Gate) (w : List ℕ) (A : Finset ℕ), (∀ g ∈ gs, Legal g) →
    (∀ u ∈ w, u &&& FM = u ∧ Held FM A u) → (∀ a ∈ A, a &&& FM = a) →
    rd (gs.foldl wstep w) o = H → Build FM H (binCost gs) A
  | [], w, A, _, hw, _, hout => by
    show Held FM A H
    rw [← hout]
    exact (rd_facts hw o).2
  | g :: gs, w, A, hg, hw, hA, hout => by
    have hgl := hg g (by simp)
    have hgs : ∀ g' ∈ gs, Legal g' := fun g' h' => hg g' (List.mem_cons_of_mem _ h')
    obtain ⟨zin, hcls⟩ := gclass hgl hw hA
    have hcost : binCost (g :: gs) = binCost gs + (if isBin g = true then 1 else 0) := by
      unfold binCost
      rw [List.filter_cons]
      split <;> simp
    rcases hcls with hh | ⟨hbin, x, hx, y, hy, t, ht, hnt, hzt⟩
    · have tail := compile o gs (wstep w g) A hgs (by
        intro u hu
        simp only [wstep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact hw u hu
        · exact ⟨zin, hh⟩) hA hout
      exact build_le tail (by rw [hcost]; omega)
    · have hti : t &&& FM = t := ops_in (hA x hx) (hA y hy) ht
      have hA' : ∀ a ∈ insert t A, a &&& FM = a := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hti
        · exact hA a ha
      have tail := compile o gs (wstep w g) (insert t A) hgs (by
        intro u hu
        simp only [wstep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact ⟨(hw u hu).1, held_mono (hw u hu).2 (Finset.subset_insert _ _)⟩
        · refine ⟨zin, ?_⟩
          rcases hzt with h | h
          · rw [h]; exact Or.inr (Or.inr ⟨t, Finset.mem_insert_self _ _, Or.inl rfl⟩)
          · rw [h]; exact Or.inr (Or.inr ⟨t, Finset.mem_insert_self _ _, Or.inr rfl⟩)) hA' hout
      rw [hcost, if_pos hbin]
      exact Or.inr ⟨x, hx, y, hy, t, ht, hnt, tail⟩

set_option maxRecDepth 100000 in
theorem fold_in : ∀ (gs : List Gate) (w : List ℕ), (∀ u ∈ w, u &&& FM = u) →
    ∀ u ∈ gs.foldl wstep w, u &&& FM = u
  | [], w, hw => hw
  | g :: gs, w, hw => by
    apply fold_in gs (wstep w g)
    intro u hu
    simp only [wstep, List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hw u hu
    · have hr : ∀ i, rd w i &&& FM = rd w i := by
        intro i; unfold rd
        by_cases h : i < w.length
        · rw [List.getD_eq_getElem _ _ h]; exact hw _ (List.getElem_mem h)
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]; simp
      unfold gword
      split
      all_goals first
        | exact hr _
        | exact neg_in _ _
        | exact ops_in (hr _) (hr _) (mem1 _ _ _)
        | exact ops_in (hr _) (hr _) (mem2 _ _ _)
        | exact Nat.zero_and _
        | (apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_land])

def tbl (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 0xfee8e8a8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def upper : Circuit where
  gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [5, 8]⟩,
    ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [9, 13]⟩]
  output := 14

theorem upper_mono : Monotone2 upper := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_size : upper.size = 10 := rfl

theorem upper_eval : ∀ x : Fin 5 → Bool, upper.eval (List.ofFn x) = tbl x := by
  decide +kernel

def RS : List ℕ := [R0, R1, R2]
def NEED : List ℕ := [7, 7, 7]

def blk (i : ℕ) : Bool :=
  let p := (pairsL X).getD i (0, 0, [])
  onPair FM H 7 RS NEED (fun nd l => go FM H RS 7 l nd) p.1 p.2.1 p.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0 : blk 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b1 : blk 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b2 : blk 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : blk 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4 : blk 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b5 : blk 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b6 : blk 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b7 : blk 7 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b8 : blk 8 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b9 : blk 9 = false := by decide +kernel

theorem len10 : (pairsL X).length = 10 := by decide +kernel

theorem go_main : go FM H RS 8 X NEED = false := by
  rw [go.eq_2]
  have e1 : (X == [H]) = false := by decide +kernel
  have e2 : (X == [neg FM H]) = false := by decide +kernel
  rw [e1, e2, Bool.false_or, Bool.false_or]
  apply List.any_eq_false.mpr
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  have hb : blk i = false := by
    have hi' : i < 10 := len10 ▸ hi
    match i, hi' with
    | 0, _ => exact b0
    | 1, _ => exact b1
    | 2, _ => exact b2
    | 3, _ => exact b3
    | 4, _ => exact b4
    | 5, _ => exact b5
    | 6, _ => exact b6
    | 7, _ => exact b7
    | 8, _ => exact b8
    | 9, _ => exact b9
  have e3 : (pairsL X).getD i (0, 0, []) = (pairsL X)[i] := List.getD_eq_getElem _ _ hi
  simp only [blk, e3] at hb
  rw [hb]
  simp

theorem only_full : ∀ ws ∈ X.sublists, cov H ws = H → ws = X := by decide +kernel

theorem worldFM : WorldOK FM H := ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w0 : ∀ ws ∈ (X.map (· &&& R0)).sublists, ws.length ≤ 6 + 1 →
    cov (H &&& R0) ws = H &&& R0 → go R0 (H &&& R0) [] 6 ws [] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w1 : ∀ ws ∈ (X.map (· &&& R1)).sublists, ws.length ≤ 6 + 1 →
    cov (H &&& R1) ws = H &&& R1 → go R1 (H &&& R1) [] 6 ws [] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w2 : ∀ ws ∈ (X.map (· &&& R2)).sublists, ws.length ≤ 6 + 1 →
    cov (H &&& R2) ws = H &&& R2 → go R2 (H &&& R2) [] 6 ws [] = false := by decide +kernel

theorem sub_refute {r : ℕ} (W : WorldOK r (H &&& r)) (h0 : H &&& r ≠ 0) (h1 : H &&& r ≠ r)
    (hnd : (X.map (· &&& r)).Nodup)
    (hS : ∀ ws ∈ (X.map (· &&& r)).sublists, ws.length ≤ 6 + 1 →
      cov (H &&& r) ws = H &&& r → go r (H &&& r) [] 6 ws [] = false)
    {n : ℕ} (hn : n ≤ 6) (hB : Build r (H &&& r) n (X.map (· &&& r)).toFinset) : False :=
  search_refutes W h0 h1 [] [] (X.map (· &&& r)) hnd
    (by intro a ha; obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; exact land_in x r) 6 hS
    (fun _ _ _ _ => trivial) (build_le hB hn)

theorem seven {r : ℕ} (hr : r &&& FM = r) (W : WorldOK r (H &&& r)) (h0 : H &&& r ≠ 0)
    (h1 : H &&& r ≠ r) (hnd : (X.map (· &&& r)).Nodup)
    (hS : ∀ ws ∈ (X.map (· &&& r)).sublists, ws.length ≤ 6 + 1 →
      cov (H &&& r) ws = H &&& r → go r (H &&& r) [] 6 ws [] = false)
    {s : Finset ℕ} {e : ℕ → ℕ} (hs : s ⊆ X.toFinset) (hl : Live FM H 8 s e) : 7 ≤ e r := by
  by_contra hlt
  have hB := project hr (X.map (· &&& r)).toFinset hl
    (by intro a ha; obtain ⟨x, -, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha); exact land_in x r)
    (by
      intro w hw
      have hx : w ∈ X := List.mem_toFinset.mp (hs hw)
      exact Or.inr (Or.inr ⟨w &&& r, List.mem_toFinset.mpr (List.mem_map_of_mem hx), Or.inl rfl⟩))
  exact sub_refute W h0 h1 hnd hS (by omega) hB

theorem cover_main (s : Finset ℕ) (e : ℕ → ℕ) (hs : s ⊆ X.toFinset) (hl : Live FM H 8 s e) :
    Cover RS NEED e := by
  show 7 ≤ e R0 ∧ 7 ≤ e R1 ∧ 7 ≤ e R2 ∧ True
  refine ⟨?_, ?_, ?_, trivial⟩
  · exact seven (by decide +kernel) ⟨rfl, by decide +kernel⟩ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) w0 hs hl
  · exact seven (by decide +kernel) ⟨rfl, by decide +kernel⟩ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) w1 hs hl
  · exact seven (by decide +kernel) ⟨rfl, by decide +kernel⟩ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) w2 hs hl

theorem main_refute (hB : Build FM H 8 X.toFinset) : False :=
  search_refutes worldFM (by decide +kernel) (by decide +kernel) RS NEED X (by decide +kernel)
    (by decide +kernel) 8
    (by intro ws hws _ hcov; rw [only_full ws hws hcov]; exact go_main) cover_main hB

set_option maxRecDepth 10000 in
theorem sample : ∀ j < 504, tbl (fun i : Fin 5 => (X.getD i.val 0).testBit j) = H.testBit j := by
  decide +kernel

theorem ofFn_X (j : ℕ) :
    List.ofFn (fun i : Fin 5 => (X.getD i.val 0).testBit j) = X.map (fun v => v.testBit j) := by
  apply List.ext_getElem
  · simp [X]
  · intro n h1 h2
    have hn : n < X.length := by simpa using h2
    simp only [List.getElem_ofFn, List.getElem_map]
    rw [List.getD_eq_getElem _ _ hn]

theorem cost_lb (C : Circuit) (hf : FanInTwo C) (hev : ∀ x, C.eval (List.ofFn x) = tbl x) :
    9 ≤ binCost C.gates := by
  by_contra hlt
  have legal : ∀ g ∈ C.gates, Legal g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hf g hg
    refine ⟨?_, h2⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h1
  have hXin : ∀ u ∈ X, u &&& FM = u := by decide +kernel
  have hout : rd (C.gates.foldl wstep X) C.output = H := by
    apply Nat.eq_of_testBit_eq; intro j
    by_cases hj : j < 504
    · rw [← read_bit, ← fold_bit j hj C.gates X legal, ← sample j hj, ← hev, ofFn_X]
      rfl
    · have hin := fold_in C.gates X hXin
      have hr : rd (C.gates.foldl wstep X) C.output &&& FM = rd (C.gates.foldl wstep X) C.output := by
        unfold rd
        by_cases h : C.output < (C.gates.foldl wstep X).length
        · rw [List.getD_eq_getElem _ _ h]; exact hin _ (List.getElem_mem h)
        · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]; simp
      rw [bit_in hr j, testBit_FM, testBit_H]
      simp only [hj, decide_false, Bool.and_false]
      symm
      simp only [decide_eq_false_iff_not]
      omega
  have hb := compile C.output C.gates X X.toFinset legal
    (fun u hu => ⟨hXin u hu, Or.inr (Or.inr ⟨u, List.mem_toFinset.mpr hu, Or.inl rfl⟩)⟩)
    (fun a ha => hXin a (List.mem_toFinset.mp ha)) hout
  exact main_refute (build_le hb (by omega))

theorem solve (s : ℕ) (hs : HasCircuitSize 5 tbl s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = tbl x := by
  obtain ⟨C, hf, hsz, hev⟩ := hs
  by_cases hn : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hg, hop⟩ := hn
    have lt : binCost C.gates < C.gates.length := by
      unfold binCost
      exact List.length_filter_lt_length_iff_exists.mpr ⟨g, hg, by simp [isBin, hop]⟩
    have lb := cost_lb C hf hev
    refine ⟨upper, upper_mono, ?_, upper_eval⟩
    rw [upper_size]
    unfold Circuit.size at hsz
    omega
  · refine ⟨C, ?_, hsz, hev⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hf g hg
    refine ⟨?_, h2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g, hg, h⟩ hn

end Cofactor

theorem Cofactor : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xfee8e8a8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xfee8e8a8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  exact Cofactor.solve

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) := Nat.testBit (4294901482 * 2 ^ 32 + 4276809450) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def base (x : Fin 5 → Bool) := Nat.testBit 4276676776 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)
def rotation : Fin 6 → Fin 6 := ![5,0,1,2,3,4]
def rotated (x : Fin 6 → Bool) := target (x ∘ rotation)
def plusGate (C : Circuit) : Gate := ⟨.or,[0,C.output]⟩
def plus (C : Circuit) : Circuit := ⟨C.gates ++ [plusGate C],6+C.gates.length⟩
theorem plusMono (C : Circuit) (hc : Monotone2 C) : Monotone2 (plus C) := by
  intro g hg
  rcases List.mem_append.mp hg with old | newGate
  · exact hc g old
  · obtain rfl := List.mem_singleton.mp newGate
    simp [plusGate]
theorem plusEval (C : Circuit) (x : Fin 6 → Bool) :
    (plus C).eval (List.ofFn x) = (x 0 || C.eval (List.ofFn x)) := by
  change (Lift.wiresFrom (C.gates ++ [plusGate C]) (List.ofFn x)).getD (6+C.gates.length) false = _
  rw [Lift.wiresFrom_append]
  let w := Lift.wiresFrom C.gates (List.ofFn x)
  change (w ++ [GateOp.or.eval ([0,C.output].map (fun i => w.getD i false))]).getD (6+C.gates.length) false = _
  rw [Lift.getD_snoc_len _ _ _ _ (by simp [w,Lift.length_wiresFrom])]
  have first : w.getD 0 false = x 0 := by
    rw [show w = Lift.wiresFrom C.gates (List.ofFn x) from rfl,Lift.getD_wiresFrom _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  change _ = (x 0 || w.getD C.output false)
  simp only [List.map_cons,List.map_nil,first]
  simp [GateOp.eval]
theorem lifted
    (small : ∀ s : ℕ, HasCircuitSize 5 base s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = base x)
    (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  have signed := Lift.relabel_size (n := 6) (m := 6) rotation target s hs
  change HasCircuitSize 6 rotated s at signed
  have dep : ∃ x : Fin 6 → Bool, rotated (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ rotated x := by
    exact ⟨fun _ => false, by decide +kernel⟩
  have nc : ∃ y z : Fin 5 → Bool, rotated (Fin.snoc y false) ≠ rotated (Fin.snoc z false) := by
    exact ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨k,hk,sm⟩ := Lift.gate_elim_one 5 rotated false s dep nc signed
  have fixed : (fun y : Fin 5 → Bool => rotated (Fin.snoc y false)) = base := by
    funext y
    exact (by decide +kernel : ∀ a : Fin 5 → Bool, rotated (Fin.snoc a false) = base a) y
  rw [fixed] at sm
  obtain ⟨C,hm,hsize,eval⟩ := small k sm
  let D := Lift.relabel 5 6 Fin.succ C
  have mono : Monotone2 D := by
    intro q hq
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hq
    exact ⟨(hm o ho).1, by simpa [Lift.relGate] using (hm o ho).2⟩
  have sz : D.gates.length=C.gates.length := by simp [D,Lift.relabel]
  refine ⟨plus D, plusMono D mono, ?_, fun x => ?_⟩
  · change (D.gates ++ [plusGate D]).length ≤ s
    simp only [List.length_append,List.length_singleton,sz]
    change C.gates.length ≤ k at hsize
    omega
  · have agrees : D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ Fin.succ)) :=
      (Lift.rel_fold 5 6 Fin.succ C.gates _ _ (Lift.rel_init 5 6 Fin.succ x)).2.2 C.output
    rw [plusEval,agrees,eval]
    exact (by decide +kernel : ∀ y : Fin 6 → Bool, (y 0 || base (y ∘ Fin.succ))=target y) x

end PEqualNP.Outside.L_meta_39565

theorem PEqualNP.Outside.L_meta_39565 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901482 * 2 ^ 32 + 4276809450) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901482 * 2 ^ 32 + 4276809450) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) :=
  PEqualNP.Outside.L_meta_39565.lifted PEqualNP.Outside.L_meta_39565.Cofactor
