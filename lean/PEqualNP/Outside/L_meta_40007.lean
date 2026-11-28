import PEqualNP.Defs

-- The shared gate-elimination and certificate code follows L-meta-8646 and L-meta-12821.
-- The two five-input certificates come from L-meta-12821 and L-meta-8704.
-- The circuit duality lemma is from L-meta-12184.

namespace PEqualNP.Outside.L_meta_40007.Base


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! ## Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

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

/-! ## Section 2: Self-contained Run, Reach, NatRun, and barrier checker -/

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)


theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {m y a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun m y s ((if neg then a ^^^ m else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {m y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {m y a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun m y s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) :
    next (m) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {m y t ws} (h : NatRun m y t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun m y s ys → f t ys = true) →
      next (m) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])


theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

/-! ## NOT-free circuits give NOT-free Runs (a copy of run_live with the NOT branch removed) -/

theorem simplify_nonot (op : GateOp) (hop : op ≠ GateOp.not) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op ≠ GateOp.not := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp)
  · exact absurd rfl hop
  · simp at hg
  · simp at hg

theorem elim_nonot (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, g.op ≠ GateOp.not) → (∀ g ∈ acc.2, g.op ≠ GateOp.not) →
    ∀ g ∈ (elim n gs acc).2, g.op ≠ GateOp.not := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hg h
    apply ih (elimStep n acc g) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_nonot _ (hg g List.mem_cons_self) _ _ g' (by simpa using h1)

theorem exists_clean_m (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ gs o, CleanL n gs ∧ (∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hC, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, fun p g hp => elim_nonot n C.gates (initId n, []) hC (fun _ h => by simp at h) g (List.mem_of_getElem? hp), hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

open Classical in
theorem run_live_m (n : ℕ) (inv : BFn n → BFn n) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hm : ∀ (p : ℕ) (g : Gate), gs[p]? = some g → g.op ≠ GateOp.not) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run inv meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then inv (val gs n j) else val gs n j) →
          Run inv meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · exact absurd hop (hm p g hg)
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run_m {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : ∃ C : Circuit, FanInTwo C ∧ (∀ g ∈ C.gates, g.op ≠ GateOp.not) ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (fun a => a) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hm, hlen, ho, hev⟩ := exists_clean_m n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live_m n (fun a => a) gs o hcl hm ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun


/-! ## Family 1: a certified frontier search (Run states closed under the moves of `next`) -/

theorem run_nil {α inv meet join y t} (h : @Run α inv meet join y t []) : False := by
  have key : ∀ t ws, @Run α inv meet join y t ws → ws ≠ [] := by
    intro t ws h
    induction h using Run.fold with
    | done => simp
    | perm hp _ ih => exact fun he => ih (List.Perm.eq_nil (he ▸ hp))
    | one => simp
    | two => simp
  exact key t [] h rfl

def isort (l : List ℕ) : List ℕ := l.insertionSort (· ≤ ·)

inductive BT where
  | lf : BT
  | nd : BT → List ℕ → BT → BT

def leqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: s, b :: t => Nat.beq a b && leqL s t
  | _, _ => false

theorem leqL_eq : ∀ a b : List ℕ, leqL a b = true → a = b
  | [], [], _ => rfl
  | a :: s, b :: t, h => by
      simp only [leqL, Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, leqL_eq s t h.2]
  | [], _ :: _, h => by simp [leqL] at h
  | _ :: _, [], h => by simp [leqL] at h

theorem leqL_self : ∀ a : List ℕ, leqL a a = true
  | [] => rfl
  | a :: s => by simp [leqL, leqL_self s]

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => Nat.blt a b || (Nat.beq a b && ltL s t)

def BT.mem : BT → List ℕ → Bool
  | .lf, _ => false
  | .nd l k r, x => leqL x k || (if ltL x k then l.mem x else r.mem x)

def BT.toList : BT → List (List ℕ)
  | .lf => []
  | .nd l k r => l.toList ++ k :: r.toList

theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .lf, x, h => by simp [BT.mem] at h
  | .nd l k r, x, hm => by
      simp only [BT.mem, Bool.or_eq_true] at hm
      simp only [BT.toList, List.mem_append, List.mem_cons]
      rcases hm with he | hm
      · exact Or.inr (Or.inl (leqL_eq x k he))
      · split at hm
        · exact Or.inl (BT.mem_toList l x hm)
        · exact Or.inr (Or.inr (BT.mem_toList r x hm))

theorem all_app {α : Type} {p : α → Bool} {A B : List α} (ha : A.all p = true) (hb : B.all p = true) :
    (A ++ B).all p = true := by
  rw [List.all_append, ha, hb]; rfl

theorem cover {p : List ℕ → List (ℕ × ℕ) → Bool} (T : BT) (L : List (List ℕ × List (ℕ × ℕ)))
    (hK : T.toList = L.map Prod.fst) (hL : L.all (fun kh => p kh.1 kh.2) = true) :
    ∀ x, T.mem x = true → ∃ h, p x h = true := by
  intro x hx
  have h1 := BT.mem_toList T x hx
  rw [hK, List.mem_map] at h1
  obtain ⟨kh, hkh, rfl⟩ := h1
  exact ⟨kh.2, List.all_eq_true.1 hL kh hkh⟩

/-- bit `i` is set when some wire differs at points `i` and `d + i` -/
def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)

/-- the union of the wires that are false at point `q` -/
def accM (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => bif Nat.testBit w q then accM q t else Nat.lor w (accM q t)

theorem accD_of (d i : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit i ≠ w.testBit (d + i) →
    (accD d ws).testBit i = true
  | [], w, hw, _ => by simp at hw
  | u :: t, w, hw, hne => by
      have e : accD d (u :: t) = (u ^^^ (u >>> d)) ||| accD d t := rfl
      rw [e, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftRight, Bool.or_eq_true]
      rcases List.mem_cons.1 hw with rfl | hw'
      · left; cases h1 : w.testBit i <;> cases h2 : w.testBit (d + i) <;> simp_all
      · right; exact accD_of d i t w hw' hne

theorem accM_of (q p : ℕ) : ∀ (ws : List ℕ) (w : ℕ), w ∈ ws → w.testBit p = true →
    w.testBit q = false → (accM q ws).testBit p = true
  | [], w, hw, _, _ => by simp at hw
  | u :: t, w, hw, hp, hq => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · have e : accM q (w :: t) = w ||| accM q t := by simp [accM, hq]
        rw [e, Nat.testBit_or, hp, Bool.true_or]
      · have ih := accM_of q p t w hw' hp hq
        cases hu : Nat.testBit u q
        · have e : accM q (u :: t) = u ||| accM q t := by simp [accM, hu]
          rw [e, Nat.testBit_or, ih, Bool.or_true]
        · have e : accM q (u :: t) = accM q t := by simp [accM, hu]
          rw [e, ih]

theorem land_sub {R X i : ℕ} (h : Nat.beq (Nat.land R X) R = true) (hi : R.testBit i = true) :
    X.testBit i = true := by
  have he : (R &&& X) = R := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and] at h2
  exact h2

theorem land_of {R X : ℕ} (h : ∀ i, R.testBit i = true → X.testBit i = true) :
    Nat.beq (Nat.land R X) R = true := by
  have he : (R &&& X) = R := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : R.testBit i
    · rfl
    · rw [h i hi]; rfl
  exact Nat.beq_eq_true_eq _ _ ▸ he

def distOK (pD : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pD.all fun dr => Nat.beq (Nat.land dr.2 (accD dr.1 ws)) dr.2

def monoOK (pM : List (ℕ × ℕ)) (ws : List ℕ) : Bool :=
  pM.all fun qp => Nat.beq (Nat.land qp.2 (accM qp.1 ws)) qp.2

def via (y : ℕ) (pD pM : List (ℕ × ℕ)) (t : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble ws.length (t + 1) && (t != 0 || leqL ws [y]) && distOK pD ws &&
    (ws.length != t + 1 || monoOK pM ws)

/-- `pD` entries `(d, R)`: every bit `i` of `R` has `y i ≠ y (d + i)`, both inside the mask.
`pM` entries `(q, P)`: `y q` is false and every bit of `P` is a true point of `y`. -/
def prsOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) : Bool :=
  pD.all (fun dr => Nat.beq (Nat.land dr.2 (Nat.xor y (Nat.shiftRight y dr.1))) dr.2 &&
    Nat.beq (Nat.land dr.2 (Nat.xor m (Nat.shiftRight m dr.1))) 0) &&
  pM.all (fun qp => Nat.beq (Nat.land qp.2 y) qp.2 && !Nat.testBit y qp.1)

theorem land_zero {R X i : ℕ} (h : Nat.beq (Nat.land R X) 0 = true) (hi : R.testBit i = true) :
    X.testBit i = false := by
  have he : (R &&& X) = 0 := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun z => Nat.testBit z i) he
  simp only [Nat.testBit_and, hi, Bool.true_and, Nat.zero_testBit] at h2
  exact h2

theorem via_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} (hp : prsOK m y pD pM = true) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : via y pD pM t ws = true := by
  simp only [prsOK, Bool.and_eq_true, List.all_eq_true] at hp
  have hl := run_len h
  simp only [via, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨⟨by rw [Nat.ble_eq]; exact hl, ?_⟩, ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · right; rw [zero_done h rfl]; exact leqL_self _
    · left; simp only [bne_iff_ne, ne_eq]; omega
  · simp only [distOK, List.all_eq_true]
    intro dr hdr
    apply land_of
    intro i hi
    have h12 := hp.1 dr hdr
    have hy : (y ^^^ (y >>> dr.1)).testBit i = true := land_sub h12.1 hi
    have hmx : (m ^^^ (m >>> dr.1)).testBit i = false := land_zero h12.2 hi
    simp only [Nat.testBit_xor, Nat.testBit_shiftRight] at hy hmx
    have hmm : m.testBit i = m.testBit (dr.1 + i) := by
      cases h1 : m.testBit i <;> cases h2 : m.testBit (dr.1 + i) <;> simp_all
    by_contra hc
    have hall : ∀ w ∈ ws, w.testBit i = w.testBit (dr.1 + i) := by
      intro w hw
      by_contra hne
      exact hc (accD_of dr.1 i ws w hw hne)
    have := run_bits h i (dr.1 + i) hmm hall
    rw [this] at hy; simp at hy
  · by_cases hlen : ws.length = t + 1
    · right
      simp only [monoOK, List.all_eq_true]
      intro qp hqp
      have h1 := hp.2 qp hqp
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      apply land_of
      intro p hpP
      have hyp : y.testBit p = true := land_sub h1.1 hpP
      by_contra hc
      have hle : ∀ w ∈ ws, w.testBit p ≤ w.testBit qp.1 := by
        intro w hw
        cases h2 : w.testBit p
        · exact Bool.false_le _
        · cases h3 : w.testBit qp.1
          · exact absurd (accM_of qp.1 p ws w hw h2 h3) hc
          · exact le_refl _
      have := bits_le h hlen p qp.1 hle
      rw [hyp, h1.2] at this
      exact absurd this (by decide)
    · left; simpa using hlen

/-- a bit map of tables: bit `k` of `actL pi w` is bit `pi[k]` of `w` (a symmetry of the target) -/
def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

theorem run_act {m y : ℕ} (pi : List ℕ) (hm : actL pi m = m) (hy : actL pi y = y) {t : ℕ}
    {ws : List ℕ} (h : NatRun m y t ws) : NatRun m y t (ws.map (actL pi)) := by
  have h2 := Run.map (actL pi) (inv' := (· ^^^ m)) (meet' := (· &&& ·)) (join' := (· ||| ·))
    (fun a => by simp only [actL_xor, hm]) (fun a b => actL_and pi a b) (fun a b => actL_or pi a b) h
  rwa [hy] at h2

def symOK (m y : ℕ) (G : List (List ℕ)) : Bool :=
  G.all fun pi => Nat.beq (actL pi m) m && Nat.beq (actL pi y) y

theorem symOK_mem {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) {pi : List ℕ}
    (hpi : pi ∈ G) : actL pi m = m ∧ actL pi y = y := by
  have := List.all_eq_true.1 hG pi hpi
  simp only [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

/-- a successor not stored as it is may be stored up to the symmetry named by its hint -/
def hfind (G : List (List ℕ)) (T : BT) (t : ℕ) (h : List (ℕ × ℕ)) (tag : ℕ) (ys : List ℕ) : Bool :=
  match h.lookup tag with
  | some j =>
    match G[j]? with
    | some pi => T.mem (t :: isort (ys.map (actL pi)))
    | none => false
  | none => false

theorem hfind_false {m y : ℕ} {G : List (List ℕ)} (hG : symOK m y G = true) (T : BT) (t : ℕ)
    (ih : ∀ ws, NatRun m y t ws → T.mem (t :: isort ws) = false)
    (h : List (ℕ × ℕ)) (tag : ℕ) {ys : List ℕ} (hys : NatRun m y t ys) : hfind G T t h tag ys = false := by
  unfold hfind
  split
  · split
    · rename_i pi hpi
      have hmem : pi ∈ G := List.mem_of_getElem? hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hmem
      exact ih _ (run_act pi hm hy hys)
    · rfl
  · rfl

def stepOK (m y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) :
    List ℕ → List (ℕ × ℕ) → Bool
  | [], _ => false
  | 0 :: _, _ => false
  | (t + 1) :: es, h => !(next m (t + 2 - es.length) es
      (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys))

theorem closure_sound {m y : ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} (T : BT)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true) :
    ∀ t ws, NatRun m y t ws → T.mem (t :: isort ws) = false := by
  intro t
  induction t with
  | zero =>
    intro ws _
    cases hm : T.mem (0 :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp [stepOK] at hs
  | succ t ih =>
    intro ws hw
    cases hm : T.mem ((t + 1) :: isort ws)
    · rfl
    · obtain ⟨h, hs⟩ := hT _ hm
      simp only [stepOK, Bool.not_eq_true'] at hs
      have hperm : (isort ws).Perm ws := List.perm_insertionSort _ _
      have hr : NatRun m y (t + 1) (isort ws) := Run.perm hperm.symm hw
      have hn := next_complete hr t rfl (isort ws) (List.Perm.refl _)
        (fun tag ys => via y pD pM t ys && !T.mem (t :: isort ys) && !hfind G T t h tag ys)
        (fun tag ys hys => by simp [via_sound hp hys, ih ys hys, hfind_false hG T t ih h tag hys])
      rw [hn] at hs; cases hs

def rootOK (y : ℕ) (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap : ℕ) (zs : List ℕ) : Bool :=
  !via y pD pM cap zs || T.mem (cap :: isort zs) || G.any (fun pi => T.mem (cap :: isort (zs.map (actL pi))))

theorem cert_core {m y : ℕ} {xs : List ℕ} {pD pM : List (ℕ × ℕ)} {G : List (List ℕ)} {T : BT} {cap : ℕ}
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true)
    {s' : ℕ} (hs' : s' ≤ cap) {ws : List ℕ} (hsub : ws.Sublist xs) (hr : NatRun m y s' ws) : False := by
  have hmem := List.all_eq_true.1 hi _ (List.mem_sublists.2 hsub)
  revert hr hmem
  cases ws with
  | nil => intro hr _; exact run_nil hr
  | cons a r =>
    intro hr hmem
    have hcap : NatRun m y cap (a :: r) := extend_run hr hs'
    have hd := via_sound hp hcap
    have hc := closure_sound T hp hG hT cap (a :: r) hcap
    have hg : (G.any fun pi => T.mem (cap :: isort ((a :: r).map (actL pi)))) = false := by
      rw [List.any_eq_false]
      intro pi hpi
      obtain ⟨hm, hy⟩ := symOK_mem hG hpi
      rw [closure_sound T hp hG hT cap _ (run_act pi hm hy hcap)]
      simp
    unfold rootOK at hmem
    rw [hd, hc, hg] at hmem
    simp at hmem

theorem lb_cert {n : ℕ} (f : BFn n) (l : List ℕ) (m y : ℕ) (xs : List ℕ)
    (pD pM : List (ℕ × ℕ)) (G : List (List ℕ)) (T : BT) (cap lb : ℕ)
    (hlb : cap + 1 = lb)
    (hm : m = 2 ^ l.length - 1)
    (hy : encL f l = y)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map
      (fun a => encL a l) = xs)
    (hnc : ∃ a b : Fin n → Bool, f a ≠ f b)
    (hp : prsOK m y pD pM = true) (hG : symOK m y G = true)
    (hT : ∀ x, T.mem x = true → ∃ h, stepOK m y pD pM G T x h = true)
    (hi : xs.sublists.all (rootOK y pD pM G T cap) = true) :
    ∀ s, HasCircuitSize n f s → lb ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hr : NatRun m (encL f l) s' (ws.map fun a => encL a l) :=
    Run.map (fun a : BFn n => encL a l) (fun a => by rw [hm]; exact encL_inv a l)
      (fun a b => encL_and a b l) (fun a b => encL_or a b l) hrun
  rw [hy] at hr
  have hsub' : (ws.map fun a => encL a l).Sublist xs := by rw [← hxs]; exact hsub.map _
  exact cert_core hp hG hT hi (by omega) hsub' hr


/-- the table index, written out for five inputs -/
def idx5 (x : Fin 5 → Bool) : ℕ :=
  (if x 0 then 2 ^ 0 else 0) + (if x 1 then 2 ^ 1 else 0) + (if x 2 then 2 ^ 2 else 0) +
    (if x 3 then 2 ^ 3 else 0) + (if x 4 then 2 ^ 4 else 0)

theorem sum_eq (x : Fin 5 → Bool) : (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) = idx5 x := by
  rw [Fin.sum_univ_five]; rfl

/-- a function true at the all-false input needs a gate -/
theorem one_le {n : ℕ} (f : BFn n) (hf : f (fun _ => false) = true) :
    ∀ s, HasCircuitSize n f s → 1 ≤ s := by
  intro s hs
  obtain ⟨C, _, hle, hC⟩ := hs
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · exfalso
    have hg : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hle)
    have h1 := hC (fun _ => false)
    rw [hf] at h1
    have e : C.eval (List.ofFn fun _ : Fin n => false) = false := by
      unfold Circuit.eval Circuit.wires
      rw [hg, List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      split <;> rfl
    rw [e] at h1
    exact Bool.false_ne_true h1
  · exact hpos


namespace LowZero

def L_ : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def M_ : ℕ := 4294967295
def Y_ : ℕ := 3936921736
def XS_ : List ℕ := [2863311530,3435973836,4042322160,4278255360,4294901760]
def PD_ : List (ℕ × ℕ) := [(1,357848132),(2,268567074),(4,67240448),(8,4325408),(16,16928)]
def PM_ : List (ℕ × ℕ) := [(5,3936921736),(9,3936921736),(14,3936921736),(17,3936921736),(22,3936921736),(26,3936921736),(28,3936921736)]

def G_ : List (List ℕ) := [[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31],[0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31],[0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31],[0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31],[0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31]]

/-- the closed set of failing search states (1551 states, up to 5 symmetries) -/
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,2290649224,2694881440,3925928448,4294901760] BT.lf) [3,2829625512,3435973836,3925928448,4294901760] (BT.nd BT.lf [3,2863179944,3435973836,4026593280,4294901760] BT.lf)) [3,2863180456,3435973836,4026593280,4293918720] (BT.nd (BT.nd BT.lf [3,2863180456,3435973836,4026593280,4294705152] BT.lf) [3,2863180456,3435973836,4026593280,4294901760] BT.lf)) [3,2863180456,3435973836,4034982016,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,3221274624,4241292492,4293918720] BT.lf) [3,2863311530,3233857536,4244438220,4278190080] BT.lf) [3,2863311530,3233857728,4244438220,4278190080] (BT.nd (BT.nd BT.lf [3,2863311530,3364407432,4026593280,4293918720] BT.lf) [3,2863311530,3368601736,4042321920,4278190080] BT.lf))) [3,2863311530,3368601800,4026593280,4293918720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,3368601800,4042321920,4278190080] BT.lf) [3,2863311530,3435711688,4026593280,4293918720] BT.lf) [3,2863311530,3435973836,3758153728,4277141504] (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,3758153728,4293918720] BT.lf) [3,2863311530,3435973836,3772833792,4278190080] BT.lf)) [3,2863311530,3435973836,3772833984,4278190080] (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4026531840,4293980160] BT.lf) [3,2863311530,3435973836,4026572800,4293918720] BT.lf) [3,2863311530,3435973836,4026593280,4092592128] (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4026593280,4204789760] BT.lf) [3,2863311530,3435973836,4026593280,4210032640] BT.lf)))) [3,2863311530,3435973836,4026593280,4210556928] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4026593280,4277141504] BT.lf) [3,2863311530,3435973836,4026593280,4277927936] BT.lf) [3,2863311530,3435973836,4026593280,4293918720] (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4026593280,4293953664] BT.lf) [3,2863311530,3435973836,4026593280,4293959680] BT.lf)) [3,2863311530,3435973836,4026593280,4294246400] (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4026593280,4294443008] BT.lf) [3,2863311530,3435973836,4026593280,4294477960] BT.lf) [3,2863311530,3435973836,4026593280,4294705152] (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4034982016,4293918720] BT.lf) [3,2863311530,3435973836,4034982016,4294443008] BT.lf))) [3,2863311530,3435973836,4037079040,4288675840] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4037079040,4291559424] BT.lf) [3,2863311530,3435973836,4037079040,4293918720] BT.lf) [3,2863311530,3435973836,4042321920,4287137928] (BT.nd (BT.nd BT.lf [3,2863311530,3435973836,4042321920,4288716800] BT.lf) [3,2863311530,3435973836,4042322160,4288716800] BT.lf)) [3,2863311530,3772834016,4287168392,4294936712] (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,3907578088,4278255360,4294936712] BT.lf) [3,2863311530,3972852940,4026593280,4293918720] BT.lf) [3,2863311530,3972852940,4042260480,4278190080] (BT.nd (BT.nd BT.lf [3,2863311530,3972852940,4042322160,4288675840] BT.lf) [3,2863311530,3974950092,4042321920,4278190080] BT.lf))))) [3,2863311530,3974950092,4042322160,4278190080] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,255,2863311530,3435973836,4042321920,4278190080] BT.lf) [4,65535,2863311530,3435973836,4026593280,4293918720] BT.lf) [4,65535,2863311530,3435973836,4042260480,4278251520] (BT.nd (BT.nd BT.lf [4,1048575,2863311530,3435973836,4026593280] BT.lf) [4,1048575,2863311530,3435973836,4026593280,4293918720] BT.lf)) [4,16776960,2863311530,3435973836,4042322160] (BT.nd (BT.nd (BT.nd BT.lf [4,16776960,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,16777215,2863311530,3435973836,4042321920] BT.lf) [4,16777215,2863311530,3435973836,4042321920,4278190080] (BT.nd (BT.nd BT.lf [4,808464432,2863311530,3368601800,4278255360,4294901760] BT.lf) [4,808464432,2863311530,3435973836,4076925696,4294901760] BT.lf))) [4,808464432,2863311530,3435973836,4194368000,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,858796848,2863311530,3435973836,4026593280,4294901760] BT.lf) [4,858993459,2863311530,3435973836,4026593280,4293918720] BT.lf) [4,858993459,2863311530,4026593280,4293918720] (BT.nd (BT.nd BT.lf [4,859032780,2863311530,4042322160,4278255360] BT.lf) [4,1154272460,2863311530,4042322160,4278255360,4294901760] BT.lf)) [4,1357967600,2863311530,3435973836,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,1431655765,2863311530,3435973836,4026593280,4293918720] BT.lf) [4,1431655765,3435973836,4026593280,4293918720] BT.lf) [4,1431677610,3435973836,4042322160,4278255360] (BT.nd (BT.nd BT.lf [4,1717986918,4042322160,4278255360,4294901760] BT.lf) [4,1886417008,1996519168,2863311530,3435973836,4294901760] BT.lf)))) [4,1886417008,2863311530,3435973836,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1886417008,2863311530,3435973836,4278255360,4294936712] BT.lf) [4,1886449904,2863311530,3435973836,4278255360,4294901760] BT.lf) [4,2290649224,2694881440,3941264106,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2290649224,2862656160,3435973836,4026593280,4294901760] BT.lf) [4,2290649224,2863311530,3435973836,4026593280,4293918720] BT.lf)) [4,2290649224,2863311530,3768639648,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2290649224,2863311530,3772834016,3993038336,4294901760] BT.lf) [4,2290649224,2863311530,3772834016,4278255360,4294901760] BT.lf) [4,2290649224,2863311530,3772834016,4278255360,4294936712] (BT.nd (BT.nd BT.lf [4,2290649224,2863311530,3907578088,4278255360,4294901760] BT.lf) [4,2290649224,3772834016,3993038336,4294901760] BT.lf))) [4,2576980377,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2684395520,2863311530,3435973836,4026593280,4293918720] BT.lf) [4,2684395520,2863311530,3435973836,4042260480,4278190080] BT.lf) [4,2684395520,2863311530,3435973836,4042322160,4288675840] (BT.nd (BT.nd BT.lf [4,2694881280,2863311530,3435973836,4042321920,4278190080] BT.lf) [4,2694881280,2863311530,3435973836,4042322160,4278190080] BT.lf)) [4,2694881440,2861083272,3435973836,4026593280,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2694881440,2863311530,3364407432,4278255360,4294901760] BT.lf) [4,2694881440,2863311530,3368601800,4194368000,4294901760] BT.lf) [4,2694881440,2863311530,3368601800,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2694881440,2863311530,3435973836,3925928448,4294901760] BT.lf) [4,2694881440,2863311530,3435973836,4026593280,4288675840] BT.lf)))))) [4,2694881440,2863311530,3435973836,4026593280,4293918720] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2694881440,2863311530,3435973836,4042321920,4278190080] BT.lf) [4,2694881440,2863311530,3435973836,4076925696,4294901760] (BT.nd BT.lf [4,2694881440,2863311530,3435973836,4194347520,4294901760] BT.lf)) [4,2694881440,2863311530,3435973836,4194365440,4294901760] (BT.nd (BT.nd BT.lf [4,2694881440,2863311530,3435973836,4194368000,4210688000] BT.lf) [4,2694881440,2863311530,3435973836,4194368000,4294901760] BT.lf)) [4,2694881440,3368601800,4194368000,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2779096485,3435973836,4278255360,4294901760] BT.lf) [4,2829625512,2863311530,3368601800,4278255360,4294901760] BT.lf) [4,2829625512,2863311530,3435973836,4194368000,4294901760] (BT.nd (BT.nd BT.lf [4,2829625512,3435973836,3941264106,4278255360,4294901760] BT.lf) [4,2829625512,3435973836,4194368000,4294901760] BT.lf))) [4,2862653600,2863311530,3435973836,4026593280,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2862656160,2863311530,3435973836,4026593280,4293918720] BT.lf) [4,2862656160,2863311530,3435973836,4026593280,4294901760] BT.lf) [4,2863179944,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863180456,2863311530,3435973836,4026593280,4294901760] BT.lf) [4,2863180456,3435973836,4026593280,4042322160,4294901760] BT.lf)) [4,2863180456,3435973836,4026593280,4244438268,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863180456,3435973836,4026593280,4293984240,4294901760] BT.lf) [4,2863180456,3435973836,4026593280,4294770684,4294901760] BT.lf) [4,2863180456,3435973836,4026593280,4294901760] (BT.nd (BT.nd BT.lf [4,2863180456,3435973836,4039176384,4278255360,4294901760] BT.lf) [4,2863180456,3435973836,4042322160,4278255360,4293918720] BT.lf)))) [4,2863180456,3435973836,4042322160,4278255360,4294705152] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863180456,3435973836,4042322160,4278255360,4294901760] BT.lf) [4,2863180456,3435973836,4042322160,4287168392,4294901760] BT.lf) [4,2863311528,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,2863311530,3435973836,4026593280,4293918720] BT.lf) [4,2863311530,3221274624,3435973836,4026593280,4293918720] BT.lf)) [4,2863311530,3221274624,4241292492,4293984240,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3221274624,4244438268,4291624908,4294901760] BT.lf) [4,2863311530,3233857536,3435973836,4042321920,4278190080] BT.lf) [4,2863311530,3233857536,4244438220,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3233857728,3435973836,4026593280,4293918720] BT.lf) [4,2863311530,3233857728,3435973836,4042321920,4278190080] BT.lf))) [4,2863311530,3233857728,4042322160,4287168392,4294936712] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3233857728,4177066232,4278255360,4294936712] BT.lf) [4,2863311530,3233857728,4244438220,4278255360,4294901760] BT.lf) [4,2863311530,3233857728,4244438268,4278255360,4294936712] (BT.nd (BT.nd BT.lf [4,2863311530,3233860812,4244438268,4278255360,4294901760] BT.lf) [4,2863311530,3234647244,4042322160,4278255360,4294901760] BT.lf)) [4,2863311530,3237015792,3435973836,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3284386755,4278255360,4294901760] BT.lf) [4,2863311530,3364391048,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3364407432,4026593280,4293984240,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3364407432,4037079200,4278255360,4294901760] BT.lf) [4,2863311530,3364407432,4042322160,4205445120,4278255360] BT.lf))))) [4,2863311530,3364407432,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3364407432,4042322160,4287168392,4294901760] BT.lf) [4,2863311530,3364407432,4042322160,4291624908,4294901760] BT.lf) [4,2863311530,3368601736,4042321920,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3368601736,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3368601800,3772834016,4278255360,4294901760] BT.lf)) [4,2863311530,3368601800,3907578088,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3368601800,3925928448,4042322160,4294901760] BT.lf) [4,2863311530,3368601800,3974950124,4278255360,4294901760] BT.lf) [4,2863311530,3368601800,3993038336,4042322160,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3368601800,4026593280,4293984240,4294901760] BT.lf) [4,2863311530,3368601800,4037079200,4278255360,4294901760] BT.lf))) [4,2863311530,3368601800,4042321920,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3368601800,4042322160,4194368000,4210688000] BT.lf) [4,2863311530,3368601800,4042322160,4194368000,4294901760] BT.lf) [4,2863311530,3368601800,4042322160,4261477888,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3368601800,4042322160,4278190080,4294967040] BT.lf) [4,2863311530,3368601800,4042322160,4278233600,4294901760] BT.lf)) [4,2863311530,3368601800,4042322160,4278251520,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3368601800,4042322160,4278254080,4294901760] BT.lf) [4,2863311530,3368601800,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3368601800,4042322160,4278255360,4294903045] (BT.nd (BT.nd BT.lf [4,2863311530,3368601800,4042322160,4278255360,4294936712] BT.lf) [4,2863311530,3368601800,4126537205,4278255360,4294901760] BT.lf)))) [4,2863311530,3368601800,4176541936,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3368601800,4177066232,4194368000,4294901760] BT.lf) [4,2863311530,3368601800,4177066232,4278255360,4294901760] BT.lf) [4,2863311530,3368601800,4177066232,4278255360,4294936712] (BT.nd (BT.nd BT.lf [4,2863311530,3368601800,4194368000,4244438268,4294901760] BT.lf) [4,2863311530,3368601800,4243651824,4278255360,4294901760] BT.lf)) [4,2863311530,3368601800,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3368601800,4278255360,4293980400,4294901760] BT.lf) [4,2863311530,3368602828,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3435187392,3435973836,4026593280,4293918720] (BT.nd (BT.nd BT.lf [4,2863311530,3435710664,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3435711688,4026593280,4293984240,4294901760] BT.lf))) [4,2863311530,3435711688,4037079200,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435711688,4042322160,4210688000,4278255360] BT.lf) [4,2863311530,3435711688,4042322160,4278255360,4293918720] BT.lf) [4,2863311530,3435711688,4042322160,4278255360,4294574080] (BT.nd (BT.nd BT.lf [4,2863311530,3435711688,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3435711688,4042322160,4287168392,4294901760] BT.lf)) [4,2863311530,3435973832,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,3435973836,4026593280,4293918720] BT.lf) [4,2863311530,3435973836,3758153728,4277206768,4294901760] BT.lf) [4,2863311530,3435973836,3758153728,4293984240,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,3768623264,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,3768639648,3993038336,4294901760] BT.lf))))))) [4,2863311530,3435973836,3768639648,4004118528,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,3768639648,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,3768639648,4291624908,4294901760] (BT.nd BT.lf [4,2863311530,3435973836,3772833792,4278255360,4294901760] BT.lf)) [4,2863311530,3435973836,3772833952,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,3772833984,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,3772834016,3993038336,4008574976] BT.lf)) [4,2863311530,3435973836,3772834016,3993038336,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,3772834016,4194368000,4294901760] BT.lf) [4,2863311530,3435973836,3772834016,4261477888,4294901760] BT.lf) [4,2863311530,3435973836,3772834016,4278190080,4294967040] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,3772834016,4278233600,4294901760] BT.lf) [4,2863311530,3435973836,3772834016,4278247424,4294901760] BT.lf))) [4,2863311530,3435973836,3772834016,4278251008,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,3772834016,4278251520,4294901760] BT.lf) [4,2863311530,3435973836,3772834016,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,3772834016,4278255360,4294906129] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,3772834016,4278255360,4294936712] BT.lf) [4,2863311530,3435973836,3772838128,4278255360,4294901760] BT.lf)) [4,2863311530,3435973836,3907578088,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,3974950124,4194368000,4294901760] BT.lf) [4,2863311530,3435973836,4007718624,4026593280,4294901760] BT.lf) [4,2863311530,3435973836,4008505068,4026593280,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4008636142,4026593280,4293918720] BT.lf) [4,2863311530,3435973836,4026531840,4026593280,4293918720] BT.lf)))) [4,2863311530,3435973836,4026531840,4293980400,4294967040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026572800,4293982960,4294901760] BT.lf) [4,2863311530,3435973836,4026572800,4293984240,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4026593280,4293918720] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4042260480,4278190080] BT.lf) [4,2863311530,3435973836,4026593280,4042260480,4278242304] BT.lf)) [4,2863311530,3435973836,4026593280,4042260480,4278251520] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4042260480,4291611852] BT.lf) [4,2863311530,3435973836,4026593280,4042322160,4210032640] BT.lf) [4,2863311530,3435973836,4026593280,4042322160,4288675840] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4042322160,4293918720] BT.lf) [4,2863311530,3435973836,4026593280,4042322160,4294705152] BT.lf))) [4,2863311530,3435973836,4026593280,4092654576,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4204853920,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4205445120,4293984240] BT.lf) [4,2863311530,3435973836,4026593280,4205509290,4293918720] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4210032640] BT.lf) [4,2863311530,3435973836,4026593280,4210032640,4210096880] BT.lf)) [4,2863311530,3435973836,4026593280,4210032640,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4210076160,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4210094320,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4210096880,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4210621176,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4210688000,4293984240] BT.lf))))) [4,2863311530,3435973836,4026593280,4210752250,4293918720] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4241292492,4293918720] BT.lf) [4,2863311530,3435973836,4026593280,4244438268,4293918720] BT.lf) [4,2863311530,3435973836,4026593280,4244438268,4294705152] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4277206768,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4277993212,4294901760] BT.lf)) [4,2863311530,3435973836,4026593280,4293918720] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4293918720,4293918720] BT.lf) [4,2863311530,3435973836,4026593280,4293918720,4293980160] BT.lf) [4,2863311530,3435973836,4026593280,4293918720,4293980400] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4293918720,4293984240] BT.lf) [4,2863311530,3435973836,4026593280,4293918720,4294617770] BT.lf))) [4,2863311530,3435973836,4026593280,4293918720,4294639610] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4293918720,4294757580] BT.lf) [4,2863311530,3435973836,4026593280,4293918720,4294770684] BT.lf) [4,2863311530,3435973836,4026593280,4293918720,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4293918720,4294945450] BT.lf) [4,2863311530,3435973836,4026593280,4293918720,4294954188] BT.lf)) [4,2863311530,3435973836,4026593280,4293918720,4294963200] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4293918720,4294963440] BT.lf) [4,2863311530,3435973836,4026593280,4293918720,4294967280] BT.lf) [4,2863311530,3435973836,4026593280,4293962400,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4293971136,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4293980160,4294901760] BT.lf)))) [4,2863311530,3435973836,4026593280,4293980400,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4293982960,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4293983472,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4293984240,4294574080] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4293984240,4294705152] BT.lf) [4,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf)) [4,2863311530,3435973836,4026593280,4293984240,4294901775] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4293984240,4294936712] BT.lf) [4,2863311530,3435973836,4026593280,4293984240,4294942720] BT.lf) [4,2863311530,3435973836,4026593280,4293984255,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4294311925,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4294508536,4294901760] BT.lf))) [4,2863311530,3435973836,4026593280,4294705152] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4294705152,4294770684] BT.lf) [4,2863311530,3435973836,4026593280,4294705152,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4294757580,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4294766832,4294901760] BT.lf) [4,2863311530,3435973836,4026593280,4294769916,4294901760] BT.lf)) [4,2863311530,3435973836,4026593280,4294770672,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4026593280,4294770684,4294901760] BT.lf) [4,2863311530,3435973836,4027576335,4293984240,4294901760] BT.lf) [4,2863311530,3435973836,4027576335,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4028690464,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4029689904,4278255360,4294901760] BT.lf)))))) [4,2863311530,3435973836,4029739008,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4029739056,4278255360,4281532416] BT.lf) [4,2863311530,3435973836,4029739056,4278255360,4294901760] (BT.nd BT.lf [4,2863311530,3435973836,4029739056,4291624908,4294901760] BT.lf)) [4,2863311530,3435973836,4029739248,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4033933424,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4034982016,4293984240,4294901760] BT.lf)) [4,2863311530,3435973836,4034982016,4294508536,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4037058720,4278233600,4294901760] BT.lf) [4,2863311530,3435973836,4037058720,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4037058720,4278255360,4294954188] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4037075104,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4037079040,4278255360,4289331200] BT.lf))) [4,2863311530,3435973836,4037079040,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4037079040,4288741120,4294901760] BT.lf) [4,2863311530,3435973836,4037079040,4291624908,4294901760] BT.lf) [4,2863311530,3435973836,4037079040,4293984240,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4037079168,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4037079200,4194368000,4294901760] BT.lf)) [4,2863311530,3435973836,4037079200,4210688000,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4037079200,4278251520,4294901760] BT.lf) [4,2863311530,3435973836,4037079200,4278255360,4289331200] BT.lf) [4,2863311530,3435973836,4037079200,4278255360,4293787648] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4037079200,4278255360,4293918720] BT.lf) [4,2863311530,3435973836,4037079200,4278255360,4294574080] BT.lf)))) [4,2863311530,3435973836,4037079200,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4037079200,4278255360,4294901845] BT.lf) [4,2863311530,3435973836,4037079200,4278255360,4294936712] BT.lf) [4,2863311530,3435973836,4037079200,4283826005,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4037079200,4286644096,4294901760] BT.lf) [4,2863311530,3435973836,4037079200,4287168392,4294901760] BT.lf)) [4,2863311530,3435973836,4037079200,4288741120,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4037079200,4289331200,4291624908] BT.lf) [4,2863311530,3435973836,4037079200,4290838464,4294901760] BT.lf) [4,2863311530,3435973836,4037079200,4291624704,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4037079200,4291624908,4294901760] BT.lf) [4,2863311530,3435973836,4037079200,4293984000,4294901760] BT.lf))) [4,2863311530,3435973836,4037079280,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4038127792,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4039176384,4278255360,4293918720] BT.lf) [4,2863311530,3435973836,4039176384,4278255360,4294705152] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4039176384,4288741280,4294901760] BT.lf) [4,2863311530,3435973836,4041269472,4278255360,4294901760] BT.lf)) [4,2863311530,3435973836,4041273344,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4041273504,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4041273536,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4041273568,4278255360,4293787648] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4041273568,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4042321920,4278251520,4294901760] BT.lf))))) [4,2863311530,3435973836,4042321920,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042321920,4278255360,4294902015] BT.lf) [4,2863311530,3435973836,4042321920,4278255360,4294936712] BT.lf) [4,2863311530,3435973836,4042321920,4278255360,4294942720] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042321920,4278255360,4294942880] BT.lf) [4,2863311530,3435973836,4042321968,4278255360,4294901760] BT.lf)) [4,2863311530,3435973836,4042322000,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322048,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4042322048,4278255360,4294936712] BT.lf) [4,2863311530,3435973836,4042322080,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322112,4278255360,4294901760] BT.lf) [4,2863311530,3435973836,4042322144,4278255360,4294901760] BT.lf))) [4,2863311530,3435973836,4042322160,4203281032,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4293953664] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294477960] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901763] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901765] BT.lf)) [4,2863311530,3435973836,4042322160,4278255360,4294901770] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901772] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901775] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901777] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901828] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901840] BT.lf)))) [4,2863311530,3435973836,4042322160,4278255360,4294901845] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901855] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901896] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901952] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901964] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294903125] BT.lf)) [4,2863311530,3435973836,4042322160,4278255360,4294905036] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294905872] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294906129] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294906197] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294914048] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294934528] BT.lf))) [4,2863311530,3435973836,4042322160,4278255360,4294934656] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294936704] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294936780] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294942720] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294942848] BT.lf)) [4,2863311530,3435973836,4042322160,4278255360,4294944904] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278583045,4294903045] BT.lf) [4,2863311530,3435973836,4042322160,4279041804,4294904844] BT.lf) [4,2863311530,3435973836,4042322160,4279369489,4294906129] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4286644096,4294934656] BT.lf) [4,2863311530,3435973836,4042322160,4286644096,4294936712] BT.lf)))))))) [4,2863311530,3435973836,4042322160,4287137928,4294967040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4287168256,4294936712] BT.lf) [4,2863311530,3435973836,4042322160,4287168392,4294936712] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4288716960,4294967040] BT.lf)) [4,2863311530,3435973836,4042322160,4288741120,4294942880] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4177066232,4287168392,4294936712] BT.lf) [4,2863311530,3435973853,4042322160,4278255360,4294901760] BT.lf)) [4,2863311530,3435977948,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435978205,4042301600,4278255360,4294901760] BT.lf) [4,2863311530,3435978205,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3435978205,4042322160,4278255445,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435986124,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3435986943,4042322160,4278255360,4294936712] BT.lf))) [4,2863311530,3437092317,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3722304989,3772834016,4278255360,4294901760] BT.lf) [4,2863311530,3772834016,3972852940,4278255360,4294901760] BT.lf) [4,2863311530,3772834016,4241292492,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3772834016,4278255360,4291611852,4294901760] BT.lf) [4,2863311530,3972844748,4042322160,4278255360,4294901760] BT.lf)) [4,2863311530,3972852940,4026593280,4293984240,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3972852940,4042260480,4278255360,4294901760] BT.lf) [4,2863311530,3972852940,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3972852940,4042322160,4278255360,4294942720] (BT.nd (BT.nd BT.lf [4,2863311530,3972852940,4042322160,4288741280,4294901760] BT.lf) [4,2863311530,3974950092,4042321920,4278255360,4294901760] BT.lf)))) [4,2863311530,3974950092,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3974950124,4026593280,4291624908,4294901760] BT.lf) [4,2863311530,3974950124,4042322160,4278255360,4294936712] BT.lf) [4,2863311530,4008636142,4042322160,4287168392,4294936712] (BT.nd (BT.nd BT.lf [4,2863311547,3435973836,4042322160,4278255360,4294901760] BT.lf) [4,3435973836,3937053354,4042322160,4278255360,4294901760] BT.lf)) [5,0,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,15,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,51,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,85,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,170,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,204,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,240,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,255,2863311530,3435973836,4042321920,4278255360,4294901760] BT.lf) [5,255,2863311530,3435973836,4042322160,4278190080] BT.lf) [5,255,2863311530,3435973836,4042322160,4278190080,4294967040] (BT.nd (BT.nd BT.lf [5,255,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,255,2863311530,3435973836,4042322175,4278255360,4294901760] BT.lf)) [5,4095,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,4369,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,8738,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,12336,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,13107,2863311530,3435921408,4042322160,4278255360] BT.lf) [5,13107,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [5,13311,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,17476,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,20560,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,21845,2863267840,3435973836,4042322160,4278255360] (BT.nd (BT.nd BT.lf [5,21845,2863311530,3435956360,4042322160,4278255360,4294901760] BT.lf) [5,21845,2863311530,3435973836,4042301600,4278255360,4294901760] BT.lf)) [5,21845,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,21845,2863311530,3435973836,4042322160,4278255445,4294901760] BT.lf) [5,21845,2863311530,3435978205,4042322160,4278255360,4294901760] BT.lf) [5,22015,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,30583,2863311530,3435973836,4042322160,4278255360] BT.lf) [5,30583,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,30583,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,34952,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,41120,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,43690,2863267840,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,43690,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,43690,2863333375,3435973836,4042322160,4278255360] BT.lf)) [5,43690,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,49344,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,52428,2863311530,3435921408,4042322160,4278255360,4294901760] BT.lf) [5,52428,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,52428,2863311530,3435973836,4042322160,4278255564,4294901760] BT.lf) [5,52428,2863311530,3435986943,4042322160,4278255360] BT.lf)))) [5,52428,2863311530,3435986943,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,61166,2863311530,3435973836,4042322160,4278255360] BT.lf) [5,61166,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,61440,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,61680,2863311530,3435973836,4042260480,4278255360,4294901760] BT.lf) [5,61680,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,61680,2863311530,3435973836,4042326015,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [5,61680,2863311530,3435973836,4042326015,4278255360,4294901760] BT.lf) [5,64250,2863311530,3435973836,4042322160,4278255360] BT.lf) [5,64250,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,64764,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,65520,2863311530,3435973836,4042322160,4278255360] BT.lf))) [5,65520,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,65535,16711935,252645135,2863311530,3435973836] BT.lf) [5,65535,16711935,858993459,2863311530,4042322160] BT.lf) [5,65535,16711935,1431655765,3435973836,4042322160] (BT.nd (BT.nd BT.lf [5,65535,16711935,2863311530,3435973836,4042322160] BT.lf) [5,65535,858993459,1431655765,4042322160,4278255360] BT.lf)) [5,65535,858993459,2863311530,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [5,65535,1431655765,3435973836,4042322160,4278255360] BT.lf) [5,65535,2290649224,4008636142,4042322160,4278255360] BT.lf) [5,65535,2694881440,3435973836,4210752250,4278255360] (BT.nd (BT.nd BT.lf [5,65535,2863267840,3435973836,4042322160,4278255360,4294945450] BT.lf) [5,65535,2863311530,3233857728,4244438268,4278255360] BT.lf)))))) [5,65535,2863311530,3368601800,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,65535,2863311530,3368601800,4042322160,4278255360,4294901760] BT.lf) [5,65535,2863311530,3435921408,4042322160,4278255360,4294954188] (BT.nd BT.lf [5,65535,2863311530,3435956360,4042322160,4278255360] BT.lf)) [5,65535,2863311530,3435956360,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,3772834016,4278255360] BT.lf) [5,65535,2863311530,3435973836,3772834016,4278255360,4294901760] BT.lf)) [5,65535,2863311530,3435973836,4008574976,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4026593280,4293984240] BT.lf) [5,65535,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,65535,2863311530,3435973836,4037079200,4278255360] (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4037079200,4278255360,4294901760] BT.lf) [5,65535,2863311530,3435973836,4042260480,4278255360,4294963440] BT.lf))) [5,65535,2863311530,3435973836,4042301600,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4042301600,4278255360,4294901760] BT.lf) [5,65535,2863311530,3435973836,4042321920,4278255360] BT.lf) [5,65535,2863311530,3435973836,4042321920,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4210688000,4278255360] BT.lf) [5,65535,2863311530,3435973836,4042322160,4278255360] BT.lf)) [5,65535,2863311530,3435973836,4042322160,4278255360,4293918720] (BT.nd (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,65535,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf) [5,65535,2863311530,3435973836,4042322160,4278255564] (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4278255564,4294901760] BT.lf) [5,65535,2863311530,3435973836,4042322160,4287168392] BT.lf)))) [5,65535,2863311530,3435973836,4042322160,4287168392,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1048575,2863311530,3435973836,4042322160,4278255360] BT.lf) [5,1048575,2863311530,3435973836,4042322160,4278255360,4293918720] BT.lf) [5,1048575,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,3355443,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,3407871,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,5592405,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,5636095,2863311530,3435973836,4042322160,4278255360] BT.lf) [5,5636095,2863311530,3435973836,4042322160,4278255360,4289331200] BT.lf) [5,5636095,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,11184810,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,13421772,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,15790320,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,16777215,2863311530,3435973836,4042322160,4278190080,4294967040] BT.lf) [5,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,16777215,2863311530,3435973836,4042322160,4294967040] (BT.nd (BT.nd BT.lf [5,268435455,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,269488144,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,286331153,2290649224,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,286331153,2863311530,3435973836,3772834016,4278255360,4294901760] BT.lf) [5,286331153,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,286331153,2863311530,3435973836,4042322160,4278255360,4294906129] (BT.nd (BT.nd BT.lf [5,286339891,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,286348629,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [5,286392319,2863311530,3435973836,4008574976,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,286392319,2863311530,3435973836,4042322160,4278255360] BT.lf) [5,286392319,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,538976288,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,572662306,2290649224,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,572662306,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,572662306,3149642683,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,572662306,3149642683,4042322160,4278255360,4294901760] BT.lf) [5,572697258,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,805318656,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,808464432,2863311530,3233857728,3435973836,4278255360,4294901760] BT.lf) [5,808464432,2863311530,3435973836,4026593280,4278255360,4294901760] BT.lf))) [5,808464432,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,808464432,2863311530,3435973836,4092851187,4278255360,4294901760] BT.lf) [5,808464432,2863311530,3435973836,4210752250,4278255360,4294901760] BT.lf) [5,808464432,2863311530,4092851187,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,808513776,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,842150450,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,842150450,2863311530,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,858796848,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,858993459,1431655765,4042322160,4278255360,4294901760] BT.lf) [5,858993459,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,858993459,2694881440,4210752250,4278255360,4294901760] BT.lf) [5,858993459,2863311530,3368601800,4042322160,4278255360,4294901760] BT.lf)))) [5,858993459,2863311530,3435973836,3772834016,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,858993459,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,858993459,2863311530,3435973836,4029739056,4278255360,4294901760] BT.lf) [5,858993459,2863311530,3435973836,4037079200,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,858993459,2863311530,3435973836,4042321920,4278255360,4294901760] BT.lf) [5,858993459,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,858993459,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd (BT.nd BT.lf [5,858993459,2863311530,3772834016,4278255360,4294901760] BT.lf) [5,858993459,2863311530,4026593280,4293984240,4294901760] BT.lf) [5,858993459,2863311530,4029739056,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,858993459,2863311530,4037079200,4278255360,4294901760] BT.lf) [5,858993459,2863311530,4042321920,4278255360,4294901760] BT.lf))) [5,858993459,2863311530,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,858993459,2863311530,4042322160,4278255360,4294936712] BT.lf) [5,858993663,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,859010935,2863311530,3435956360,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,859010935,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,859010935,2863311530,4042322160,4278255360,4294901760] BT.lf)) [5,859045887,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,859045887,2863311530,4042322160,4278255360,4294954188] BT.lf) [5,872415231,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,1077952576,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,1145324612,2290649224,2863311530,4042322160,4278255360,4294901760] BT.lf) [5,1145324612,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))))) [5,1145324612,2863311530,3722304989,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1145324612,3722304989,4042322160,4278255360,4294901760] BT.lf) [5,1145359564,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,1342197760,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,1347440720,2694881440,2863311530,3435973836,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,1347440720,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,1347440720,2863311530,3435973836,4126537205,4278255360,4294901760] BT.lf)) [5,1347440720,2863311530,3435973836,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,1347440720,3435973836,4126537205,4278255360,4294901760] BT.lf) [5,1347481840,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,1414812756,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,1431328080,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,1431655765,2863311530,3368601800,4042322160,4278255360,4294901760] BT.lf))) [5,1431655765,2863311530,3435973836,3772834016,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1431655765,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,1431655765,2863311530,3435973836,4037079200,4278255360,4294901760] BT.lf) [5,1431655765,2863311530,3435973836,4042321920,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,1431655765,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf)) [5,1431655765,3233857728,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,1431655765,3368601800,4042322160,4278255360,4294901760] BT.lf) [5,1431655765,3435973836,3772834016,4278255360,4294901760] BT.lf) [5,1431655765,3435973836,4026593280,4293984240,4294901760] (BT.nd (BT.nd BT.lf [5,1431655765,3435973836,4037079200,4278255360,4294901760] BT.lf) [5,1431655765,3435973836,4042321920,4278255360,4294901760] BT.lf)))) [5,1431655765,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1431655765,3435973836,4042322160,4278255360,4294936712] BT.lf) [5,1431655935,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,1431664503,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,1431699455,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,1431699455,3435973836,4042322160,4278255360,4294945450] BT.lf)) [5,1442840575,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,1886417008,2004318071,2863311530,3435973836,4278255360,4294901760] BT.lf) [5,1886417008,2290649224,2863311530,3435973836,4278255360,4294901760] BT.lf) [5,1886417008,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,1886417008,2863311530,3435973836,4278255360,4294901760] BT.lf) [5,2004318071,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,2004318071,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2004318071,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2004353023,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2147516416,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf)) [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd (BT.nd BT.lf [5,2155905152,2863311530,3435973836,4177066232,4278255360,4294901760] BT.lf) [5,2290124928,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2694881440,2863311530,3233857728,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290649224,2862656160,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3221274624,4042322160,4278255360,4294901760] BT.lf))))) [5,2290649224,2863311530,3233857728,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3233857728,4042322160,4278255360,4294936712] BT.lf) [5,2290649224,2863311530,3233857728,4177066232,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3233857728,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3368601800,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3368601800,4177066232,4278255360,4294901760] BT.lf)) [5,2290649224,2863311530,3435187392,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3435973836,3772834016,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,2290649224,2863311530,3435973836,4037079200,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4042321920,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf) [5,2290649224,2863311530,3435973836,4042322160,4287168392,4294936712] BT.lf) [5,2290649224,2863311530,3435986943,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3772834016,4008636142,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3772834016,4042322160,4278255360,4294901760] BT.lf)) [5,2290649224,2863311530,3772834016,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3941264106,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3974950124,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,4008636142,4042322160,4278255360,4294936712] BT.lf) [5,2290649224,3772834016,4008636142,4278255360,4294901760] BT.lf)))) [5,2290649224,3941264106,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,4008636142,4042322160,4278255360,4294936712] BT.lf) [5,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290666700,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2290679807,2863311530,3435973836,4042322160,4278255360] BT.lf)) [5,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2684354560,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2684395520,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,2684395520,2863311530,3435973836,4042260480,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2684395520,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2684395520,2863311530,3435973836,4042322160,4278255360,4294942720] BT.lf))) [5,2684395520,2863311530,3435973836,4042322160,4288741280,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2684395520,2863311530,3972852940,4042322160,4278255360,4294901760] BT.lf) [5,2692784256,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2694881280,2863311530,3435973836,4042321920,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2694881280,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2694881440,2852170240,2863311530,3435973836,4026593280,4294901760] BT.lf)) [5,2694881440,2861083272,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3221274624,3435973836,4278255360,4294901760] BT.lf) [5,2694881440,2863311530,3233857728,3435973836,4278255360,4294901760] BT.lf) [5,2694881440,2863311530,3368601800,3435973836,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3368601800,4042322160,4278255360,4294901760] BT.lf) [5,2694881440,2863311530,3368601800,4210752250,4278255360,4294901760] BT.lf)))))) [5,2694881440,2863311530,3368601800,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3431517320,4042322160,4278255360,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,3772834016,4278255360,4294901760] (BT.nd BT.lf [5,2694881440,2863311530,3435973836,3941264106,4278255360,4294901760] BT.lf)) [5,2694881440,2863311530,3435973836,3993038336,4042322160,4294901760] (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3435973836,4026531840,4278255360,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,4026593280,4278190080,4294901760] BT.lf)) [5,2694881440,2863311530,3435973836,4026593280,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3435973836,4026593280,4288741280,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,4026593280,4291624908,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,4026593280,4293984240,4294901760] (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3435973836,4037079200,4278255360,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,4039176384,4278255360,4294901760] BT.lf))) [5,2694881440,2863311530,3435973836,4042321920,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3435973836,4042322160,4194368000,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,4042322160,4278190080,4294967040] BT.lf) [5,2694881440,2863311530,3435973836,4042322160,4278231040,4294901760] (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3435973836,4042322160,4278233600,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,4042322160,4278251520,4294901760] BT.lf)) [5,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf) [5,2694881440,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf) [5,2694881440,2863311530,3435973836,4042322160,4278255360,4294942720] (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3435973836,4042326015,4278255360,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,4092851187,4278255360,4294901760] BT.lf)))) [5,2694881440,2863311530,3435973836,4177066232,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3435973836,4194368000,4210752250,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,4194368000,4278255360,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,4194368000,4294901760] (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3435973836,4205509290,4278255360,4294901760] BT.lf) [5,2694881440,2863311530,3435973836,4210096880,4278255360,4294901760] BT.lf)) [5,2694881440,2863311530,3435973836,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2694881440,2863311530,3972852940,4042322160,4278255360,4294901760] BT.lf) [5,2694881440,3368601800,4210752250,4278255360,4294901760] BT.lf) [5,2694881440,3435973836,3941264106,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2694881440,3435973836,4194368000,4210752250,4294901760] BT.lf) [5,2694881440,3435973836,4205509290,4278255360,4294901760] BT.lf))) [5,2694881440,3435973836,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2694884010,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2694902000,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2694905855,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2728567458,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2827528328,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,2829101216,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2829625512,2863311530,3233857728,3435973836,4278255360,4294901760] BT.lf) [5,2829625512,2863311530,3233857728,4278255360,4294901760] BT.lf) [5,2829625512,2863311530,3435973836,4026593280,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2829625512,2863311530,3435973836,4177066232,4278255360,4294901760] BT.lf))))) [5,2829625512,2863311530,3435973836,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2829625512,3435973836,4210752250,4278255360,4294901760] BT.lf) [5,2862653600,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2862656160,2863311530,3435973836,4026593280,4042322160,4294901760] (BT.nd (BT.nd BT.lf [5,2862656160,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,2862656160,2863311530,3435973836,4026593280,4294901760] BT.lf)) [5,2862656160,2863311530,3435973836,4042322160,4278255360,4293918720] (BT.nd (BT.nd (BT.nd BT.lf [5,2862656160,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863180456,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863180456,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863180456,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf) [5,2863180456,3435973836,4042322160,4278255360,4294770684,4294901760] BT.lf))) [5,2863180456,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311520,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863311530,3368601800,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863311530,3435973836,3772834016,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,2863311530,2863311530,3435973836,4037079200,4278255360,4294901760] BT.lf)) [5,2863311530,2863311530,3435973836,4042321920,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf) [5,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,2863315899,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [5,2863311530,2863332090,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2964369584,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3014898611,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3132799674,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3149642683,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3149660159,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3221225472,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3221274624,3435973836,4026593280,4293984240,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3221274624,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3221274624,3435973836,4042322160,4290838464,4294901760] BT.lf))) [5,2863311530,3221274624,3435973836,4042322160,4291624908,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3221274624,4042322160,4241292492,4278255360,4294901760] BT.lf) [5,2863311530,3229663360,3431517320,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3229663360,3435973836,4037079200,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3229663360,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3233857536,3435973836,4042321920,4278255360,4294901760] BT.lf)) [5,2863311530,3233857536,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3368601800,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3233857728,3431517320,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3233857728,3435973836,3772834016,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3435973836,3925928448,4042322160,4294901760] BT.lf) [5,2863311530,3233857728,3435973836,3974950124,4278255360,4294901760] BT.lf))))))))) [5,2863311530,3233857728,3435973836,3993038336,4042322160,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,2863311530,3233857728,3435973836,4037079200,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4042321920,4278255360,4294901760] BT.lf)) [5,2863311530,3233857728,3435973836,4042322160,4194368000,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4042322160,4278190080,4294967040] BT.lf) [5,2863311530,3233857728,3435973836,4042322160,4278233600,4294901760] BT.lf)) [5,2863311530,3233857728,3435973836,4042322160,4278251520,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3233857728,3435973836,4042322160,4278255360,4294934656] BT.lf) [5,2863311530,3233857728,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4126537205,4278255360,4294901760] BT.lf) [5,2863311530,3233857728,3435973836,4177066232,4278255360,4294901760] BT.lf))) [5,2863311530,3233857728,3435973836,4243651824,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4244438268,4278255360,4294901760] BT.lf) [5,2863311530,3233857728,3435973836,4278255360,4293980400,4294901760] BT.lf) [5,2863311530,3233857728,3722304989,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3974950124,4278255360,4294901760] BT.lf) [5,2863311530,3233857728,4042322160,4241292492,4278255360,4294901760] BT.lf)) [5,2863311530,3233857728,4042322160,4278255360,4291611852,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,4177066232,4278255360,4294901760] BT.lf) [5,2863311530,3233857728,4244438268,4278255360,4291624908,4294901760] BT.lf) [5,2863311530,3233857728,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3233860812,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3233870064,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [5,2863311530,3233873919,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3301229764,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3364407432,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3364407432,4026593280,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3364407432,4042322160,4205509290,4278255360,4294901760] BT.lf) [5,2863311530,3364407432,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3368077504,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,3368601800,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,3435973836,4042322160,4194368000,4294901760] BT.lf) [5,2863311530,3368601800,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,3435973836,4177066232,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,3435973836,4244438268,4278255360,4294901760] BT.lf))) [5,2863311530,3368601800,3941264106,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,4026593280,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,4042322160,4177066232,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,4042322160,4194368000,4210752250,4294901760] BT.lf)) [5,2863311530,3368601800,4042322160,4194368000,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,4042322160,4194368000,4294901760] BT.lf) [5,2863311530,3368601800,4042322160,4210752250,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,4042322160,4278124286,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,4042322160,4278190080,4278255360,4294901760] BT.lf))))) [5,2863311530,3368601800,4042322160,4278255360,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,4042322160,4278255360,4289396650,4294901760] BT.lf) [5,2863311530,3368601800,4042322160,4278255360,4291362760,4294901760] BT.lf) [5,2863311530,3368601800,4042322160,4278255360,4291624908,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,4042322160,4278255360,4293984240,4294901760] BT.lf) [5,2863311530,3368601800,4042322160,4278255360,4294639610,4294901760] BT.lf)) [5,2863311530,3368601800,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,4042322160,4278255360,4294901760,4294967040] BT.lf) [5,2863311530,3368601800,4177066232,4210752250,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,4177066232,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,4210752250,4244438268,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,4244438268,4278255360,4294901760] BT.lf))) [5,2863311530,3435184320,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435187392,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,2863311530,3435187392,3435973836,4042322160,4278255360,4293918720] BT.lf) [5,2863311530,3435187392,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435711688,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435711688,4042322160,4210752250,4278255360,4294901760] BT.lf)) [5,2863311530,3435711688,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435711688,4042322160,4278255360,4294639610,4294901760] BT.lf) [5,2863311530,3435711688,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973824,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3435973836,3772834016,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3435973836,4026593280,4293984240,4294901760] BT.lf)))) [5,2863311530,3435973836,3435973836,4037079200,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3435973836,4042321920,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3435973887,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3435978205,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,3435982574,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3435986172,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3439329279,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3503345872,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3587560917,4042322160,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,3705461980,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3722313727,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3758153728,3772834016,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3758153728,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3768639648,4004179626,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,3768639648,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3768639648,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3770736832,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3772834016,3772834016,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3772834016,3941264106,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3772834016,3974950124,4278255360,4294901760] BT.lf)))))) [5,2863311530,3435973836,3772834016,3993038336,4008636142,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3772834016,3993038336,4042322160,4294901760] BT.lf) [5,2863311530,3435973836,3772834016,3993038336,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,3772834016,4008636142,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,3772834016,4026593280,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3772834016,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3772834016,4210752250,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,3772834016,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3772834016,4278124286,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3772834016,4278190080,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3772834016,4278255360,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3772834016,4278255360,4289396650,4294901760] BT.lf) [5,2863311530,3435973836,3772834016,4278255360,4291624908,4294901760] BT.lf))) [5,2863311530,3435973836,3772834016,4278255360,4292935648,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3772834016,4278255360,4293853166,4294901760] BT.lf) [5,2863311530,3435973836,3772834016,4278255360,4293984240,4294901760] BT.lf) [5,2863311530,3435973836,3772834016,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3772834016,4278255360,4294901760,4294967040] BT.lf) [5,2863311530,3435973836,3937069738,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,3938511552,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3941264106,4244438268,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3972852940,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3974950124,4026593280,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760] BT.lf)))) [5,2863311530,3435973836,3974950124,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4007718624,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4008373994,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4008505068,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4008636142,4026593280,4293984240,4294901760] BT.lf) [5,2863311530,3435973836,4008636142,4037079200,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4008636142,4041273568,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4008636142,4042321920,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294906129] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294936712] BT.lf) [5,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,4026531840,4026593280,4293984240,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026531840,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4026531840,4042322160,4278255360,4294954188] BT.lf) [5,2863311530,3435973836,4026531840,4042322160,4278255360,4294963200] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026572800,4042301600,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4026572800,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4026580992,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4026593280,4293984240,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4037079200,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042260480,4042322160,4278190080] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042260480,4278190080] BT.lf) [5,2863311530,3435973836,4026593280,4042260480,4278255360,4294901760] BT.lf))))) [5,2863311530,3435973836,4026593280,4042260480,4278255360,4294954188] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042260480,4278255360,4294963200] BT.lf) [5,2863311530,3435973836,4026593280,4042260480,4278255360,4294963440] BT.lf) [5,2863311530,3435973836,4026593280,4042301600,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042309824,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042321920,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4026593280,4042322160,4205445120,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042322160,4210096880,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4210688000,4278255360] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4278255360,4293918720] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4278255360,4294936712] BT.lf))) [5,2863311530,3435973836,4026593280,4042322160,4278255360,4294942720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042322160,4278255615,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4283826005,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4287168392,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042322160,4288741280,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4290838464,4294901760] BT.lf)) [5,2863311530,3435973836,4026593280,4042322160,4291559424,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042322160,4291611852,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4291624704,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4291624908,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042322160,4293918720] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4293918720,4293984240] BT.lf)))) [5,2863311530,3435973836,4026593280,4042322160,4293918720,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042322160,4293980400,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4293984000,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4042322160,4293984240,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4042322160,4294770684,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4205509290,4293984240,4294901760] BT.lf)) [5,2863311530,3435973836,4026593280,4210096880,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4210752250,4293984240,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4241292492,4293984240,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4244438268,4291624908,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4244438268,4293984240,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4244438268,4294770684,4294901760] BT.lf))) [5,2863311530,3435973836,4026593280,4293918720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4293918720,4293984240] BT.lf) [5,2863311530,3435973836,4026593280,4293918720,4293984240,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4293918720,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4293980400,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4293984240,4293984240,4294901760] BT.lf)) [5,2863311530,3435973836,4026593280,4293984240,4294639610,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4293984240,4294770684,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf) [5,2863311530,3435973836,4026593280,4293984240,4294901760,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4293984240,4294901760,4294945450] BT.lf) [5,2863311530,3435973836,4026593280,4293984240,4294901760,4294954188] BT.lf))))))) [5,2863311530,3435973836,4026593280,4293984240,4294901760,4294963200] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4293984240,4294901760,4294963440] BT.lf) [5,2863311530,3435973836,4026593280,4293984240,4294901760,4294967280] (BT.nd BT.lf [5,2863311530,3435973836,4026593280,4294770684,4294901760] BT.lf)) [5,2863311530,3435973836,4026593520,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4026597375,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4029739056,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4029739056,4278255360,4281597747,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4029739056,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4031836240,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4034982016,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4034982016,4042322160,4287168392,4294901760] BT.lf) [5,2863311530,3435973836,4037058720,4042322160,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,4037058720,4278255360,4289374890,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037058720,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4037079040,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4037079040,4278255360,4289396480,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037079040,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4037079200,4037079200,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4037079200,4042322160,4278255360,4289331200] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037079200,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4037079200,4042322160,4291624908,4294901760] BT.lf) [5,2863311530,3435973836,4037079200,4205509290,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037079200,4210752250,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4037079200,4243389676,4278255360,4294901760] BT.lf)))) [5,2863311530,3435973836,4037079200,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037079200,4278255360,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4037079200,4278255360,4288741280,4294901760] BT.lf) [5,2863311530,3435973836,4037079200,4278255360,4289331200] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037079200,4278255360,4289331200,4289396650] BT.lf) [5,2863311530,3435973836,4037079200,4278255360,4289396650,4294901760] BT.lf)) [5,2863311530,3435973836,4037079200,4278255360,4291624908,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037079200,4278255360,4293853166,4294901760] BT.lf) [5,2863311530,3435973836,4037079200,4278255360,4293984240,4294901760] BT.lf) [5,2863311530,3435973836,4037079200,4278255360,4294639610,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037079200,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4037079200,4278255360,4294901760,4294901760] BT.lf))) [5,2863311530,3435973836,4037079200,4278255360,4294901760,4294945450] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037079200,4278255360,4294901760,4294954188] BT.lf) [5,2863311530,3435973836,4037079200,4278255360,4294901760,4294963360] BT.lf) [5,2863311530,3435973836,4037079200,4278255360,4294901760,4294963440] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037079200,4278255360,4294901760,4294967040] BT.lf) [5,2863311530,3435973836,4037079200,4278255360,4294901760,4294967210] BT.lf)) [5,2863311530,3435973836,4037079200,4289396650,4291624908,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4037079200,4291624908,4294901760] BT.lf) [5,2863311530,3435973836,4039164096,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4039176192,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4039176384,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4039176384,4244438268,4278255360,4294901760] BT.lf))))) [5,2863311530,3435973836,4039176384,4278255360,4293984240,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4039176384,4278255360,4294770684,4294901760] BT.lf) [5,2863311530,3435973836,4041273568,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4041273568,4278255360,4289396650,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4041273568,4278255360,4291624908,4294901760] BT.lf) [5,2863311530,3435973836,4041273568,4278255360,4293853166,4294901760] BT.lf)) [5,2863311530,3435973836,4041273568,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042321920,4042321920,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042321920,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042321920,4210752170,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042321920,4210752250,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042321920,4244438220,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,4042321920,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042321920,4278255360,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042321920,4278255360,4289396650,4294901760] BT.lf) [5,2863311530,3435973836,4042321920,4278255360,4291624908,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042321920,4278255360,4293984000,4294901760] BT.lf) [5,2863311530,3435973836,4042321920,4278255360,4293984240,4294901760] BT.lf)) [5,2863311530,3435973836,4042321920,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042321920,4278255360,4294901760,4294967040] BT.lf) [5,2863311530,3435973836,4042321920,4278255360,4294901760,4294967210] BT.lf) [5,2863311530,3435973836,4042321920,4278255360,4294901760,4294967244] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042321920,4278255360,4294901760,4294967280] BT.lf) [5,2863311530,3435973836,4042322080,4042322160,4278255360,4294901760] BT.lf)))) [5,2863311530,3435973836,4042322080,4278255360,4289396650,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322080,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322080,4278255360,4294901760,4294967040] BT.lf) [5,2863311530,3435973836,4042322080,4278255360,4294901760,4294967210] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322112,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322112,4278255360,4291624908,4294901760] BT.lf)) [5,2863311530,3435973836,4042322112,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322112,4278255360,4294901760,4294967040] BT.lf) [5,2863311530,3435973836,4042322112,4278255360,4294901760,4294967244] BT.lf) [5,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4042322160,4278255360,4294936712] BT.lf) [5,2863311530,3435973836,4042322160,4042322175,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,4042322160,4042322931,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4042323445,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4042324730,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4042325244,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4042326000,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4042326015,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4043309055,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4059165169,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4076008178,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4080268083,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4092654576,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4092851187,4278255360,4294901760] BT.lf)))))) [5,2863311530,3435973836,4042322160,4092854271,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4109694196,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4116051285,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4126209520,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4126537205,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4126539775,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4160223223,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4169726088,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4176541936,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4177066232,4278255360,4294936712] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4205488810,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4205506560,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,4042322160,4205509290,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4205509290,4291624908,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4207475400,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4209703658,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4210094320,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4210096880,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4210621176,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4210752000,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4210752170,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4210752240,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4210752250,4278255360,4294903045] BT.lf)))) [5,2863311530,3435973836,4042322160,4210752250,4278255360,4294936712] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4210753535,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4227595259,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4241280204,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4241289216,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4243389676,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4243648752,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4243651824,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4244176120,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4244438016,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4244438220,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,4042322160,4244438256,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4244438268,4278255360,4294936712] BT.lf) [5,2863311530,3435973836,4042322160,4244439039,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4261281277,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4277075694,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4277206768,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4277862138,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4277993212,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4293980400,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4293982960,4294901760] BT.lf))))) [5,2863311530,3435973836,4042322160,4278255360,4293983472,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4293984240,4294901775] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4293984240,4294936712] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4293984255,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294180851,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4278255360,4294311925,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294508536,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294638330,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294639600,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294639610,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294769916,4294901760] BT.lf))) [5,2863311530,3435973836,4042322160,4278255360,4294770672,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901758,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967280] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967290] BT.lf)) [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967292] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901775] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901845] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294901964] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294902015,4294954188] BT.lf)))) [5,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294906129] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294914867,4294954188] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294923605,4294945450] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf)) [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294936712] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294945450] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294954188] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294965496] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294942720] BT.lf))) [5,2863311530,3435973836,4042322160,4278255360,4294942880,4294954188] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294942880,4294967040] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294945450,4294951104] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294945450,4294963200] BT.lf) [5,2863311530,3435973836,4042322160,4287168392,4294936712] BT.lf)) [5,2863311530,3435978205,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435978205,4042322160,4278255360,4294901760,4294945450] BT.lf) [5,2863311530,3435986943,4042322160,4278255360,4294901760,4294954188] BT.lf) [5,2863311530,3722304989,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3972852940,4026593280,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3972852940,4042322160,4278255360,4294901760] BT.lf)))))))) [5,2863311530,3974950124,4042322160,4278255360,4291624908,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,4008636142,4042322160,4241292492,4278255360,4294901760] BT.lf) [5,2863333375,3435973836,4042322160,4278255360,4294901760,4294945450] (BT.nd BT.lf [5,3149642683,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf)) [6,0,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd BT.lf [6,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,858993459,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,0,858993459,2863311530,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,0,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,255,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] BT.lf))) [6,13107,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,13107,2863311530,3435973836,4042322160,4278255360,4294901760,4294954188] BT.lf) [6,21845,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,21845,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450] (BT.nd (BT.nd BT.lf [6,43690,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,43690,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,43690,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,52428,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,52428,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,52428,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,61680,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,61680,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [6,61680,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,16711935,2863311530,3435973836,4042322160] (BT.nd (BT.nd BT.lf [6,65535,16711935,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,16711935,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,65535,858993459,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,858993459,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,858993459,2863311530,4042322160,4278255360] BT.lf) [6,65535,858993459,2863311530,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,65535,1431655765,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,65535,1431655765,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2290649224,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,65535,2694881440,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,65535,2863267840,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,65535,2863311530,2863333375,3435973836,4042322160,4278255360] BT.lf) [6,65535,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [6,65535,2863311530,3233857728,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435921408,3435973836,4042322160,4278255360] BT.lf) [6,65535,2863311530,3435921408,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,3435973836,4042322160,4278255360] BT.lf) [6,65535,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,65535,2863311530,3435973836,3435986943,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,4008636142,4042322160,4278255360] BT.lf) [6,65535,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4026593280,4042322160,4278255360] BT.lf) [6,65535,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf))) [6,65535,2863311530,3435973836,4042260480,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042260480,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,4042322160,4042322160,4278255360] BT.lf) [6,65535,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4042326015,4278255360] BT.lf) [6,65535,2863311530,3435973836,4042322160,4042326015,4278255360,4294901760] BT.lf)) [6,65535,2863311530,3435973836,4042322160,4210752250,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,4042322160,4244438268,4278255360] BT.lf) [6,65535,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4293984240] BT.lf)))) [6,65535,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450] (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294954188] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294963440] BT.lf)) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294945450] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294954188] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294963440] (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294967295] BT.lf) [6,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] BT.lf))) [6,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,286331153,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,286331153,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,572662306,858993459,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,572662306,858993459,2863311530,4042322160,4278255360,4294901760] BT.lf) [6,572662306,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,808464432,858993459,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,808464432,858993459,2863311530,4042322160,4278255360,4294901760] BT.lf) [6,808464432,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,858993459,858993459,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,858993459,858993459,2863311530,4042322160,4278255360,4294901760] BT.lf) [6,858993459,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))))) [6,858993459,1431655765,2863311530,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,858993459,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,858993459,1431655765,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,858993459,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,858993459,2290649224,2863311530,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,858993459,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,858993459,2694881440,2863311530,4042322160,4278255360,4294901760] BT.lf)) [6,858993459,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,858993459,2863311530,2863311530,4042322160,4278255360,4294901760] BT.lf) [6,858993459,2863311530,3149642683,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,858993459,2863311530,3149642683,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,858993459,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,858993459,2863311530,3233857728,4042322160,4278255360,4294901760] BT.lf))) [6,858993459,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,858993459,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,858993459,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf) [6,858993459,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,858993459,2863311530,3435973836,4042322160,4092851187,4278255360,4294901760] BT.lf) [6,858993459,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf)) [6,858993459,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,858993459,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,858993459,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,858993459,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd BT.lf [6,858993459,2863311530,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,858993459,2863311530,4026593280,4042322160,4278255360,4294901760] BT.lf)))) [6,858993459,2863311530,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,858993459,2863311530,4042322160,4092851187,4278255360,4294901760] BT.lf) [6,858993459,2863311530,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,858993459,2863311530,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,858993459,2863311530,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,858993459,2863311530,4042322160,4278255360,4294901760] BT.lf)) [6,858993459,2863311530,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd BT.lf [6,859045887,2863311530,3435921408,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,859045887,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1145324612,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,1145324612,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1145324612,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,1347440720,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1347440720,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1347440720,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,1431655765,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,1431655765,2290649224,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,1431655765,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,2694881440,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,1431655765,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [6,1431655765,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1431655765,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,1431655765,2863311530,3435973836,4042322160,4126537205,4278255360,4294901760] BT.lf) [6,1431655765,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf)) [6,1431655765,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,1431655765,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd BT.lf [6,1431655765,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,1431655765,3435973836,3722304989,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1431655765,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,3435973836,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,1431655765,3435973836,4042322160,4126537205,4278255360,4294901760] BT.lf) [6,1431655765,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf)) [6,1431655765,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,1431655765,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd BT.lf [6,1431699455,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431699455,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [6,2004318071,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2004318071,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2155905152,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2155905152,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2290649224,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3233857728,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,2290649224,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf)) [6,2290649224,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf) [6,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2290649224,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,4008636142,4042322160,4278255360,4294901760] BT.lf))))))) [6,2684395520,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2684395520,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf) [6,2684395520,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2694881440,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2694881440,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2694881440,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2694881440,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2694881440,2863311530,3233857728,3435973836,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2694881440,2863311530,3422604288,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2694881440,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2694881440,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2694881440,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2694881440,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf))) [6,2694881440,2863311530,3435973836,4026593280,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2694881440,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] BT.lf) [6,2694881440,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,2694881440,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2694881440,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] BT.lf) [6,2694881440,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760] BT.lf)) [6,2694881440,2863311530,3435973836,4042322160,4278255360,4288741280,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2694881440,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760] BT.lf) [6,2694881440,2863311530,3435973836,4042322160,4278255360,4291624908,4294901760] BT.lf) [6,2694881440,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd BT.lf [6,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] BT.lf)))) [6,2694881440,2863311530,3435973836,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2694881440,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,2694881440,3435973836,4210752250,4278255360,4294901760] BT.lf) [6,2829625512,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2862656160,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf)) [6,2862656160,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf))) [6,2863311530,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2863311530,3149642683,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3221274624,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3221274624,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3221274624,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3233857728,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3422604288,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [6,2863311530,3233857728,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3233857728,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3435973836,4026593280,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3233857728,3435973836,4042322160,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf)) [6,2863311530,3233857728,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3233857728,3435973836,4042322160,4278190080,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3435973836,4042322160,4278255360,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3435973836,4042322160,4278255360,4289396650,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3233857728,3435973836,4042322160,4278255360,4290838464,4294901760] BT.lf) [6,2863311530,3233857728,3435973836,4042322160,4278255360,4291624908,4294901760] BT.lf))) [6,2863311530,3233857728,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760,4294967040] BT.lf) [6,2863311530,3233857728,3435973836,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3233857728,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,4244438268,4278255360,4294901760] BT.lf)) [6,2863311530,3368601800,3435973836,4042322160,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3368601800,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3368601800,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,2863311530,3368601800,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435187392,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,2863311530,3435187392,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [6,2863311530,3435973836,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3435973836,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3772834016,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3772834016,4008636142,4278255360,4294901760] BT.lf))) [6,2863311530,3435973836,3772834016,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3772834016,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4008636142,4026593280,4042322160,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,4008636142,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4008636142,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf)))))) [6,2863311530,3435973836,4026531840,4026593280,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4026531840,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4026593280,4026593280,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,4026593280,4042260480,4042322160,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,4026593280,4042260480,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4026593280,4042322160,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4026593280,4042322160,4205509290,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,4026593280,4042322160,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4026593280,4042322160,4241292492,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4026593280,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4026593280,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760,4294901760] BT.lf))) [6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760,4294945450] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760,4294954188] BT.lf) [6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760,4294963200] BT.lf) [6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760,4294963440] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4026593280,4042322160,4291624908,4294901760] BT.lf) [6,2863311530,3435973836,4026593280,4042322160,4293984240,4294901760] BT.lf)) [6,2863311530,3435973836,4026593280,4293984240,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4037079200,4042322160,4278255360,4289396650,4294901760] BT.lf) [6,2863311530,3435973836,4037079200,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4037079200,4278255360,4289396650,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4037079200,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4039176384,4042322160,4278255360,4291624908,4294901760] BT.lf)))) [6,2863311530,3435973836,4039176384,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042321920,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042321920,4042322160,4278255360,4294901760,4294967040] BT.lf) [6,2863311530,3435973836,4042321920,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042321920,4278255360,4294901760,4294967040] BT.lf) [6,2863311530,3435973836,4042322160,4042322160,4042322160,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,4042322160,4042322160,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4042322160,4278255360,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4042322160,4278255360,4289396650,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4042322160,4278255360,4291624908,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4042322160,4278255360,4293984240,4294901760] BT.lf))) [6,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760,4294967040] BT.lf) [6,2863311530,3435973836,4042322160,4042326015,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4092851187,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4126537205,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,4042322160,4205509290,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4210096880,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4210752250,4210752250,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4210752250,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4210752250,4278124286,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4210752250,4278255360,4289396650,4294901760] BT.lf))))) [6,2863311530,3435973836,4042322160,4210752250,4278255360,4291624908,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4210752250,4278255360,4293984240,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4210752250,4278255360,4294639610,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760,4294967040] BT.lf) [6,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,4042322160,4243651824,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4244438268,4244438268,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4244438268,4278124286,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4244438268,4278255360,4291624908,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4244438268,4278255360,4293984240,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4244438268,4278255360,4294770684,4294901760] BT.lf))) [6,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760,4294967040] BT.lf) [6,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4293980400,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4293984240,4293984240,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4293984240,4294639610,4294901760] BT.lf)) [6,2863311530,3435973836,4042322160,4278255360,4293984240,4294770684,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760,4294963440] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760,4294967280] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4294639610,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760] BT.lf)))) [6,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967280] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188] BT.lf) [7,65535,2863311530,3435973836,4042322160,4278255360] BT.lf)) [7,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,858993459,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,858993459,2863311530,4042322160,4278255360,4294901760] BT.lf) [7,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [7,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [7,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [7,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [7,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] BT.lf)) [7,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf) [7,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [7,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd BT.lf [7,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [8,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([3,2290649224,2694881440,3925928448,4294901760],[]),([3,2829625512,3435973836,3925928448,4294901760],[]),([3,2863179944,3435973836,4026593280,4294901760],[]),([3,2863180456,3435973836,4026593280,4293918720],[]),([3,2863180456,3435973836,4026593280,4294705152],[]),([3,2863180456,3435973836,4026593280,4294901760],[]),([3,2863180456,3435973836,4034982016,4294901760],[]),([3,2863311530,3221274624,4241292492,4293918720],[]),([3,2863311530,3233857536,4244438220,4278190080],[]),([3,2863311530,3233857728,4244438220,4278190080],[]),([3,2863311530,3364407432,4026593280,4293918720],[]),([3,2863311530,3368601736,4042321920,4278190080],[]),([3,2863311530,3368601800,4026593280,4293918720],[]),([3,2863311530,3368601800,4042321920,4278190080],[]),([3,2863311530,3435711688,4026593280,4293918720],[]),([3,2863311530,3435973836,3758153728,4277141504],[]),([3,2863311530,3435973836,3758153728,4293918720],[]),([3,2863311530,3435973836,3772833792,4278190080],[]),([3,2863311530,3435973836,3772833984,4278190080],[]),([3,2863311530,3435973836,4026531840,4293980160],[]),([3,2863311530,3435973836,4026572800,4293918720],[]),([3,2863311530,3435973836,4026593280,4092592128],[]),([3,2863311530,3435973836,4026593280,4204789760],[]),([3,2863311530,3435973836,4026593280,4210032640],[]),([3,2863311530,3435973836,4026593280,4210556928],[]),([3,2863311530,3435973836,4026593280,4277141504],[]),([3,2863311530,3435973836,4026593280,4277927936],[]),([3,2863311530,3435973836,4026593280,4293918720],[]),([3,2863311530,3435973836,4026593280,4293953664],[]),([3,2863311530,3435973836,4026593280,4293959680],[]),([3,2863311530,3435973836,4026593280,4294246400],[]),([3,2863311530,3435973836,4026593280,4294443008],[]),([3,2863311530,3435973836,4026593280,4294477960],[]),([3,2863311530,3435973836,4026593280,4294705152],[]),([3,2863311530,3435973836,4034982016,4293918720],[]),([3,2863311530,3435973836,4034982016,4294443008],[]),([3,2863311530,3435973836,4037079040,4288675840],[]),([3,2863311530,3435973836,4037079040,4291559424],[]),([3,2863311530,3435973836,4037079040,4293918720],[]),([3,2863311530,3435973836,4042321920,4287137928],[]),([3,2863311530,3435973836,4042321920,4288716800],[]),([3,2863311530,3435973836,4042322160,4288716800],[]),([3,2863311530,3772834016,4287168392,4294936712],[]),([3,2863311530,3907578088,4278255360,4294936712],[]),([3,2863311530,3972852940,4026593280,4293918720],[]),([3,2863311530,3972852940,4042260480,4278190080],[]),([3,2863311530,3972852940,4042322160,4288675840],[]),([3,2863311530,3974950092,4042321920,4278190080],[]),([3,2863311530,3974950092,4042322160,4278190080],[]),([4,255,2863311530,3435973836,4042321920,4278190080],[]),([4,65535,2863311530,3435973836,4026593280,4293918720],[]),([4,65535,2863311530,3435973836,4042260480,4278251520],[]),([4,1048575,2863311530,3435973836,4026593280],[]),([4,1048575,2863311530,3435973836,4026593280,4293918720],[]),([4,16776960,2863311530,3435973836,4042322160],[]),([4,16776960,2863311530,3435973836,4042322160,4278190080],[]),([4,16777215,2863311530,3435973836,4042321920],[(2,2)]),([4,16777215,2863311530,3435973836,4042321920,4278190080],[]),([4,808464432,2863311530,3368601800,4278255360,4294901760],[]),([4,808464432,2863311530,3435973836,4076925696,4294901760],[]),([4,808464432,2863311530,3435973836,4194368000,4294901760],[]),([4,858796848,2863311530,3435973836,4026593280,4294901760],[]),([4,858993459,2863311530,3435973836,4026593280,4293918720],[]),([4,858993459,2863311530,4026593280,4293918720],[]),([4,859032780,2863311530,4042322160,4278255360],[]),([4,1154272460,2863311530,4042322160,4278255360,4294901760],[]),([4,1357967600,2863311530,3435973836,4278255360,4294901760],[]),([4,1431655765,2863311530,3435973836,4026593280,4293918720],[]),([4,1431655765,3435973836,4026593280,4293918720],[]),([4,1431677610,3435973836,4042322160,4278255360],[]),([4,1717986918,4042322160,4278255360,4294901760],[]),([4,1886417008,1996519168,2863311530,3435973836,4294901760],[]),([4,1886417008,2863311530,3435973836,4278255360,4294901760],[]),([4,1886417008,2863311530,3435973836,4278255360,4294936712],[]),([4,1886449904,2863311530,3435973836,4278255360,4294901760],[]),([4,2290649224,2694881440,3941264106,4278255360,4294901760],[(148,0)]),([4,2290649224,2862656160,3435973836,4026593280,4294901760],[]),([4,2290649224,2863311530,3435973836,4026593280,4293918720],[(96,3)]),([4,2290649224,2863311530,3768639648,4278255360,4294901760],[(108,1)]),([4,2290649224,2863311530,3772834016,3993038336,4294901760],[]),([4,2290649224,2863311530,3772834016,4278255360,4294901760],[]),([4,2290649224,2863311530,3772834016,4278255360,4294936712],[]),([4,2290649224,2863311530,3907578088,4278255360,4294901760],[(96,0)]),([4,2290649224,3772834016,3993038336,4294901760],[]),([4,2576980377,4042322160,4278255360,4294901760],[]),([4,2684395520,2863311530,3435973836,4026593280,4293918720],[]),([4,2684395520,2863311530,3435973836,4042260480,4278190080],[(96,4),(128,3)]),([4,2684395520,2863311530,3435973836,4042322160,4288675840],[]),([4,2694881280,2863311530,3435973836,4042321920,4278190080],[(56,2),(96,2)])]
noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([4,2694881280,2863311530,3435973836,4042322160,4278190080],[]),([4,2694881440,2861083272,3435973836,4026593280,4294901760],[]),([4,2694881440,2863311530,3364407432,4278255360,4294901760],[]),([4,2694881440,2863311530,3368601800,4194368000,4294901760],[]),([4,2694881440,2863311530,3368601800,4278255360,4294901760],[]),([4,2694881440,2863311530,3435973836,3925928448,4294901760],[]),([4,2694881440,2863311530,3435973836,4026593280,4288675840],[(56,1)]),([4,2694881440,2863311530,3435973836,4026593280,4293918720],[]),([4,2694881440,2863311530,3435973836,4042321920,4278190080],[(56,2)]),([4,2694881440,2863311530,3435973836,4076925696,4294901760],[]),([4,2694881440,2863311530,3435973836,4194347520,4294901760],[]),([4,2694881440,2863311530,3435973836,4194365440,4294901760],[]),([4,2694881440,2863311530,3435973836,4194368000,4210688000],[]),([4,2694881440,2863311530,3435973836,4194368000,4294901760],[]),([4,2694881440,3368601800,4194368000,4294901760],[]),([4,2779096485,3435973836,4278255360,4294901760],[]),([4,2829625512,2863311530,3368601800,4278255360,4294901760],[]),([4,2829625512,2863311530,3435973836,4194368000,4294901760],[]),([4,2829625512,3435973836,3941264106,4278255360,4294901760],[(148,0)]),([4,2829625512,3435973836,4194368000,4294901760],[]),([4,2862653600,2863311530,3435973836,4026593280,4294901760],[]),([4,2862656160,2863311530,3435973836,4026593280,4293918720],[]),([4,2862656160,2863311530,3435973836,4026593280,4294901760],[]),([4,2863179944,3435973836,4042322160,4278255360,4294901760],[(148,0)]),([4,2863180456,2863311530,3435973836,4026593280,4294901760],[]),([4,2863180456,3435973836,4026593280,4042322160,4294901760],[]),([4,2863180456,3435973836,4026593280,4244438268,4294901760],[]),([4,2863180456,3435973836,4026593280,4293984240,4294901760],[]),([4,2863180456,3435973836,4026593280,4294770684,4294901760],[]),([4,2863180456,3435973836,4026593280,4294901760],[]),([4,2863180456,3435973836,4039176384,4278255360,4294901760],[]),([4,2863180456,3435973836,4042322160,4278255360,4293918720],[]),([4,2863180456,3435973836,4042322160,4278255360,4294705152],[]),([4,2863180456,3435973836,4042322160,4278255360,4294901760],[]),([4,2863180456,3435973836,4042322160,4287168392,4294901760],[]),([4,2863311528,3435973836,4042322160,4278255360,4294901760],[]),([4,2863311530,2863311530,3435973836,4026593280,4293918720],[]),([4,2863311530,3221274624,3435973836,4026593280,4293918720],[]),([4,2863311530,3221274624,4241292492,4293984240,4294901760],[]),([4,2863311530,3221274624,4244438268,4291624908,4294901760],[]),([4,2863311530,3233857536,3435973836,4042321920,4278190080],[(80,2),(104,2)]),([4,2863311530,3233857536,4244438220,4278255360,4294901760],[]),([4,2863311530,3233857728,3435973836,4026593280,4293918720],[]),([4,2863311530,3233857728,3435973836,4042321920,4278190080],[(80,2),(104,2)]),([4,2863311530,3233857728,4042322160,4287168392,4294936712],[]),([4,2863311530,3233857728,4177066232,4278255360,4294936712],[]),([4,2863311530,3233857728,4244438220,4278255360,4294901760],[]),([4,2863311530,3233857728,4244438268,4278255360,4294936712],[]),([4,2863311530,3233860812,4244438268,4278255360,4294901760],[]),([4,2863311530,3234647244,4042322160,4278255360,4294901760],[]),([4,2863311530,3237015792,3435973836,4278255360,4294901760],[]),([4,2863311530,3284386755,4278255360,4294901760],[]),([4,2863311530,3364391048,4042322160,4278255360,4294901760],[]),([4,2863311530,3364407432,4026593280,4293984240,4294901760],[]),([4,2863311530,3364407432,4037079200,4278255360,4294901760],[]),([4,2863311530,3364407432,4042322160,4205445120,4278255360],[]),([4,2863311530,3364407432,4042322160,4278255360,4294901760],[]),([4,2863311530,3364407432,4042322160,4287168392,4294901760],[]),([4,2863311530,3364407432,4042322160,4291624908,4294901760],[]),([4,2863311530,3368601736,4042321920,4278255360,4294901760],[]),([4,2863311530,3368601736,4042322160,4278255360,4294901760],[]),([4,2863311530,3368601800,3772834016,4278255360,4294901760],[]),([4,2863311530,3368601800,3907578088,4278255360,4294901760],[]),([4,2863311530,3368601800,3925928448,4042322160,4294901760],[]),([4,2863311530,3368601800,3974950124,4278255360,4294901760],[]),([4,2863311530,3368601800,3993038336,4042322160,4294901760],[]),([4,2863311530,3368601800,4026593280,4293984240,4294901760],[]),([4,2863311530,3368601800,4037079200,4278255360,4294901760],[])]
noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([4,2863311530,3368601800,4042321920,4278255360,4294901760],[]),([4,2863311530,3368601800,4042322160,4194368000,4210688000],[]),([4,2863311530,3368601800,4042322160,4194368000,4294901760],[]),([4,2863311530,3368601800,4042322160,4261477888,4294901760],[]),([4,2863311530,3368601800,4042322160,4278190080,4294967040],[]),([4,2863311530,3368601800,4042322160,4278233600,4294901760],[]),([4,2863311530,3368601800,4042322160,4278251520,4294901760],[(148,0)]),([4,2863311530,3368601800,4042322160,4278254080,4294901760],[]),([4,2863311530,3368601800,4042322160,4278255360,4294901760],[]),([4,2863311530,3368601800,4042322160,4278255360,4294903045],[]),([4,2863311530,3368601800,4042322160,4278255360,4294936712],[]),([4,2863311530,3368601800,4126537205,4278255360,4294901760],[]),([4,2863311530,3368601800,4176541936,4278255360,4294901760],[]),([4,2863311530,3368601800,4177066232,4194368000,4294901760],[]),([4,2863311530,3368601800,4177066232,4278255360,4294901760],[]),([4,2863311530,3368601800,4177066232,4278255360,4294936712],[]),([4,2863311530,3368601800,4194368000,4244438268,4294901760],[]),([4,2863311530,3368601800,4243651824,4278255360,4294901760],[]),([4,2863311530,3368601800,4244438268,4278255360,4294901760],[]),([4,2863311530,3368601800,4278255360,4293980400,4294901760],[]),([4,2863311530,3368602828,4042322160,4278255360,4294901760],[]),([4,2863311530,3435187392,3435973836,4026593280,4293918720],[]),([4,2863311530,3435710664,4042322160,4278255360,4294901760],[]),([4,2863311530,3435711688,4026593280,4293984240,4294901760],[]),([4,2863311530,3435711688,4037079200,4278255360,4294901760],[]),([4,2863311530,3435711688,4042322160,4210688000,4278255360],[]),([4,2863311530,3435711688,4042322160,4278255360,4293918720],[]),([4,2863311530,3435711688,4042322160,4278255360,4294574080],[]),([4,2863311530,3435711688,4042322160,4278255360,4294901760],[]),([4,2863311530,3435711688,4042322160,4287168392,4294901760],[]),([4,2863311530,3435973832,4042322160,4278255360,4294901760],[]),([4,2863311530,3435973836,3435973836,4026593280,4293918720],[]),([4,2863311530,3435973836,3758153728,4277206768,4294901760],[]),([4,2863311530,3435973836,3758153728,4293984240,4294901760],[]),([4,2863311530,3435973836,3768623264,4278255360,4294901760],[]),([4,2863311530,3435973836,3768639648,3993038336,4294901760],[]),([4,2863311530,3435973836,3768639648,4004118528,4278255360],[]),([4,2863311530,3435973836,3768639648,4278255360,4294901760],[]),([4,2863311530,3435973836,3768639648,4291624908,4294901760],[(100,1)]),([4,2863311530,3435973836,3772833792,4278255360,4294901760],[]),([4,2863311530,3435973836,3772833952,4278255360,4294901760],[]),([4,2863311530,3435973836,3772833984,4278255360,4294901760],[]),([4,2863311530,3435973836,3772834016,3993038336,4008574976],[]),([4,2863311530,3435973836,3772834016,3993038336,4294901760],[]),([4,2863311530,3435973836,3772834016,4194368000,4294901760],[]),([4,2863311530,3435973836,3772834016,4261477888,4294901760],[]),([4,2863311530,3435973836,3772834016,4278190080,4294967040],[]),([4,2863311530,3435973836,3772834016,4278233600,4294901760],[]),([4,2863311530,3435973836,3772834016,4278247424,4294901760],[(148,3)]),([4,2863311530,3435973836,3772834016,4278251008,4294901760],[]),([4,2863311530,3435973836,3772834016,4278251520,4294901760],[(148,0)]),([4,2863311530,3435973836,3772834016,4278255360,4294901760],[]),([4,2863311530,3435973836,3772834016,4278255360,4294906129],[]),([4,2863311530,3435973836,3772834016,4278255360,4294936712],[]),([4,2863311530,3435973836,3772838128,4278255360,4294901760],[]),([4,2863311530,3435973836,3907578088,4278255360,4294901760],[]),([4,2863311530,3435973836,3974950124,4194368000,4294901760],[]),([4,2863311530,3435973836,4007718624,4026593280,4294901760],[(148,3)]),([4,2863311530,3435973836,4008505068,4026593280,4294901760],[(148,3)]),([4,2863311530,3435973836,4008636142,4026593280,4293918720],[(148,3)]),([4,2863311530,3435973836,4026531840,4026593280,4293918720],[]),([4,2863311530,3435973836,4026531840,4293980400,4294967040],[]),([4,2863311530,3435973836,4026572800,4293982960,4294901760],[]),([4,2863311530,3435973836,4026572800,4293984240,4294901760],[]),([4,2863311530,3435973836,4026593280,4026593280,4293918720],[]),([4,2863311530,3435973836,4026593280,4042260480,4278190080],[(112,2),(144,0)]),([4,2863311530,3435973836,4026593280,4042260480,4278242304],[(144,0)]),([4,2863311530,3435973836,4026593280,4042260480,4278251520],[(144,0)]),([4,2863311530,3435973836,4026593280,4042260480,4291611852],[]),([4,2863311530,3435973836,4026593280,4042322160,4210032640],[]),([4,2863311530,3435973836,4026593280,4042322160,4288675840],[(116,1)])]
noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([4,2863311530,3435973836,4026593280,4042322160,4293918720],[]),([4,2863311530,3435973836,4026593280,4042322160,4294705152],[]),([4,2863311530,3435973836,4026593280,4092654576,4294901760],[]),([4,2863311530,3435973836,4026593280,4204853920,4294901760],[]),([4,2863311530,3435973836,4026593280,4205445120,4293984240],[]),([4,2863311530,3435973836,4026593280,4205509290,4293918720],[]),([4,2863311530,3435973836,4026593280,4210032640],[]),([4,2863311530,3435973836,4026593280,4210032640,4210096880],[]),([4,2863311530,3435973836,4026593280,4210032640,4294901760],[]),([4,2863311530,3435973836,4026593280,4210076160,4294901760],[]),([4,2863311530,3435973836,4026593280,4210094320,4294901760],[]),([4,2863311530,3435973836,4026593280,4210096880,4294901760],[]),([4,2863311530,3435973836,4026593280,4210621176,4294901760],[]),([4,2863311530,3435973836,4026593280,4210688000,4293984240],[]),([4,2863311530,3435973836,4026593280,4210752250,4293918720],[]),([4,2863311530,3435973836,4026593280,4241292492,4293918720],[]),([4,2863311530,3435973836,4026593280,4244438268,4293918720],[]),([4,2863311530,3435973836,4026593280,4244438268,4294705152],[]),([4,2863311530,3435973836,4026593280,4277206768,4294901760],[]),([4,2863311530,3435973836,4026593280,4277993212,4294901760],[]),([4,2863311530,3435973836,4026593280,4293918720],[]),([4,2863311530,3435973836,4026593280,4293918720,4293918720],[]),([4,2863311530,3435973836,4026593280,4293918720,4293980160],[]),([4,2863311530,3435973836,4026593280,4293918720,4293980400],[]),([4,2863311530,3435973836,4026593280,4293918720,4293984240],[]),([4,2863311530,3435973836,4026593280,4293918720,4294617770],[(140,3)]),([4,2863311530,3435973836,4026593280,4293918720,4294639610],[]),([4,2863311530,3435973836,4026593280,4293918720,4294757580],[(108,3)]),([4,2863311530,3435973836,4026593280,4293918720,4294770684],[]),([4,2863311530,3435973836,4026593280,4293918720,4294901760],[]),([4,2863311530,3435973836,4026593280,4293918720,4294945450],[(140,3)]),([4,2863311530,3435973836,4026593280,4293918720,4294954188],[]),([4,2863311530,3435973836,4026593280,4293918720,4294963200],[]),([4,2863311530,3435973836,4026593280,4293918720,4294963440],[]),([4,2863311530,3435973836,4026593280,4293918720,4294967280],[]),([4,2863311530,3435973836,4026593280,4293962400,4294901760],[]),([4,2863311530,3435973836,4026593280,4293971136,4294901760],[]),([4,2863311530,3435973836,4026593280,4293980160,4294901760],[]),([4,2863311530,3435973836,4026593280,4293980400,4294901760],[]),([4,2863311530,3435973836,4026593280,4293982960,4294901760],[]),([4,2863311530,3435973836,4026593280,4293983472,4294901760],[]),([4,2863311530,3435973836,4026593280,4293984240,4294574080],[]),([4,2863311530,3435973836,4026593280,4293984240,4294705152],[]),([4,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([4,2863311530,3435973836,4026593280,4293984240,4294901775],[]),([4,2863311530,3435973836,4026593280,4293984240,4294936712],[]),([4,2863311530,3435973836,4026593280,4293984240,4294942720],[]),([4,2863311530,3435973836,4026593280,4293984255,4294901760],[]),([4,2863311530,3435973836,4026593280,4294311925,4294901760],[]),([4,2863311530,3435973836,4026593280,4294508536,4294901760],[]),([4,2863311530,3435973836,4026593280,4294705152],[]),([4,2863311530,3435973836,4026593280,4294705152,4294770684],[]),([4,2863311530,3435973836,4026593280,4294705152,4294901760],[]),([4,2863311530,3435973836,4026593280,4294757580,4294901760],[(140,3)]),([4,2863311530,3435973836,4026593280,4294766832,4294901760],[]),([4,2863311530,3435973836,4026593280,4294769916,4294901760],[]),([4,2863311530,3435973836,4026593280,4294770672,4294901760],[]),([4,2863311530,3435973836,4026593280,4294770684,4294901760],[]),([4,2863311530,3435973836,4027576335,4293984240,4294901760],[]),([4,2863311530,3435973836,4027576335,4294901760],[]),([4,2863311530,3435973836,4028690464,4278255360,4294901760],[]),([4,2863311530,3435973836,4029689904,4278255360,4294901760],[]),([4,2863311530,3435973836,4029739008,4278255360,4294901760],[(156,2)]),([4,2863311530,3435973836,4029739056,4278255360,4281532416],[]),([4,2863311530,3435973836,4029739056,4278255360,4294901760],[]),([4,2863311530,3435973836,4029739056,4291624908,4294901760],[]),([4,2863311530,3435973836,4029739248,4278255360,4294901760],[]),([4,2863311530,3435973836,4033933424,4278255360,4294901760],[])]
noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([4,2863311530,3435973836,4034982016,4293984240,4294901760],[]),([4,2863311530,3435973836,4034982016,4294508536,4294901760],[]),([4,2863311530,3435973836,4037058720,4278233600,4294901760],[]),([4,2863311530,3435973836,4037058720,4278255360,4294901760],[]),([4,2863311530,3435973836,4037058720,4278255360,4294954188],[]),([4,2863311530,3435973836,4037075104,4278255360,4294901760],[]),([4,2863311530,3435973836,4037079040,4278255360,4289331200],[(156,2)]),([4,2863311530,3435973836,4037079040,4278255360,4294901760],[(156,2)]),([4,2863311530,3435973836,4037079040,4288741120,4294901760],[]),([4,2863311530,3435973836,4037079040,4291624908,4294901760],[]),([4,2863311530,3435973836,4037079040,4293984240,4294901760],[]),([4,2863311530,3435973836,4037079168,4278255360,4294901760],[(156,2)]),([4,2863311530,3435973836,4037079200,4194368000,4294901760],[]),([4,2863311530,3435973836,4037079200,4210688000,4278255360],[]),([4,2863311530,3435973836,4037079200,4278251520,4294901760],[(148,0)]),([4,2863311530,3435973836,4037079200,4278255360,4289331200],[]),([4,2863311530,3435973836,4037079200,4278255360,4293787648],[]),([4,2863311530,3435973836,4037079200,4278255360,4293918720],[]),([4,2863311530,3435973836,4037079200,4278255360,4294574080],[]),([4,2863311530,3435973836,4037079200,4278255360,4294901760],[]),([4,2863311530,3435973836,4037079200,4278255360,4294901845],[]),([4,2863311530,3435973836,4037079200,4278255360,4294936712],[]),([4,2863311530,3435973836,4037079200,4283826005,4294901760],[]),([4,2863311530,3435973836,4037079200,4286644096,4294901760],[]),([4,2863311530,3435973836,4037079200,4287168392,4294901760],[]),([4,2863311530,3435973836,4037079200,4288741120,4294901760],[]),([4,2863311530,3435973836,4037079200,4289331200,4291624908],[]),([4,2863311530,3435973836,4037079200,4290838464,4294901760],[]),([4,2863311530,3435973836,4037079200,4291624704,4294901760],[]),([4,2863311530,3435973836,4037079200,4291624908,4294901760],[]),([4,2863311530,3435973836,4037079200,4293984000,4294901760],[]),([4,2863311530,3435973836,4037079280,4278255360,4294901760],[]),([4,2863311530,3435973836,4038127792,4278255360,4294901760],[]),([4,2863311530,3435973836,4039176384,4278255360,4293918720],[]),([4,2863311530,3435973836,4039176384,4278255360,4294705152],[]),([4,2863311530,3435973836,4039176384,4288741280,4294901760],[(156,4)]),([4,2863311530,3435973836,4041269472,4278255360,4294901760],[]),([4,2863311530,3435973836,4041273344,4278255360,4294901760],[(156,2)]),([4,2863311530,3435973836,4041273504,4278255360,4294901760],[]),([4,2863311530,3435973836,4041273536,4278255360,4294901760],[(156,2)]),([4,2863311530,3435973836,4041273568,4278255360,4293787648],[]),([4,2863311530,3435973836,4041273568,4278255360,4294901760],[]),([4,2863311530,3435973836,4042321920,4278251520,4294901760],[(148,0),(156,2)]),([4,2863311530,3435973836,4042321920,4278255360,4294901760],[(156,2)]),([4,2863311530,3435973836,4042321920,4278255360,4294902015],[(156,2)]),([4,2863311530,3435973836,4042321920,4278255360,4294936712],[(156,2)]),([4,2863311530,3435973836,4042321920,4278255360,4294942720],[(156,2)]),([4,2863311530,3435973836,4042321920,4278255360,4294942880],[(156,2)]),([4,2863311530,3435973836,4042321968,4278255360,4294901760],[]),([4,2863311530,3435973836,4042322000,4278255360,4294901760],[(156,2)]),([4,2863311530,3435973836,4042322048,4278255360,4294901760],[(156,2)]),([4,2863311530,3435973836,4042322048,4278255360,4294936712],[(156,2)]),([4,2863311530,3435973836,4042322080,4278255360,4294901760],[]),([4,2863311530,3435973836,4042322112,4278255360,4294901760],[(156,2)]),([4,2863311530,3435973836,4042322144,4278255360,4294901760],[]),([4,2863311530,3435973836,4042322160,4203281032,4294901760],[]),([4,2863311530,3435973836,4042322160,4278255360,4293953664],[]),([4,2863311530,3435973836,4042322160,4278255360,4294477960],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901763],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901765],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901770],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901772],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901775],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901777],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901828],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901840],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901845],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901855],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901896],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901952],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901964],[])]
noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([4,2863311530,3435973836,4042322160,4278255360,4294903125],[]),([4,2863311530,3435973836,4042322160,4278255360,4294905036],[]),([4,2863311530,3435973836,4042322160,4278255360,4294905872],[]),([4,2863311530,3435973836,4042322160,4278255360,4294906129],[]),([4,2863311530,3435973836,4042322160,4278255360,4294906197],[]),([4,2863311530,3435973836,4042322160,4278255360,4294914048],[]),([4,2863311530,3435973836,4042322160,4278255360,4294934528],[]),([4,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([4,2863311530,3435973836,4042322160,4278255360,4294936704],[]),([4,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([4,2863311530,3435973836,4042322160,4278255360,4294936780],[]),([4,2863311530,3435973836,4042322160,4278255360,4294942720],[]),([4,2863311530,3435973836,4042322160,4278255360,4294942848],[]),([4,2863311530,3435973836,4042322160,4278255360,4294944904],[]),([4,2863311530,3435973836,4042322160,4278583045,4294903045],[]),([4,2863311530,3435973836,4042322160,4279041804,4294904844],[]),([4,2863311530,3435973836,4042322160,4279369489,4294906129],[]),([4,2863311530,3435973836,4042322160,4286644096,4294934656],[]),([4,2863311530,3435973836,4042322160,4286644096,4294936712],[]),([4,2863311530,3435973836,4042322160,4287137928,4294967040],[]),([4,2863311530,3435973836,4042322160,4287168256,4294936712],[]),([4,2863311530,3435973836,4042322160,4287168392,4294936712],[]),([4,2863311530,3435973836,4042322160,4288716960,4294967040],[]),([4,2863311530,3435973836,4042322160,4288741120,4294942880],[]),([4,2863311530,3435973836,4177066232,4287168392,4294936712],[]),([4,2863311530,3435973853,4042322160,4278255360,4294901760],[]),([4,2863311530,3435977948,4042322160,4278255360,4294901760],[]),([4,2863311530,3435978205,4042301600,4278255360,4294901760],[]),([4,2863311530,3435978205,4042322160,4278255360,4294901760],[]),([4,2863311530,3435978205,4042322160,4278255445,4294901760],[]),([4,2863311530,3435986124,4042322160,4278255360,4294901760],[]),([4,2863311530,3435986943,4042322160,4278255360,4294936712],[]),([4,2863311530,3437092317,4042322160,4278255360,4294901760],[]),([4,2863311530,3722304989,3772834016,4278255360,4294901760],[]),([4,2863311530,3772834016,3972852940,4278255360,4294901760],[]),([4,2863311530,3772834016,4241292492,4278255360,4294901760],[]),([4,2863311530,3772834016,4278255360,4291611852,4294901760],[]),([4,2863311530,3972844748,4042322160,4278255360,4294901760],[]),([4,2863311530,3972852940,4026593280,4293984240,4294901760],[]),([4,2863311530,3972852940,4042260480,4278255360,4294901760],[]),([4,2863311530,3972852940,4042322160,4278255360,4294901760],[]),([4,2863311530,3972852940,4042322160,4278255360,4294942720],[]),([4,2863311530,3972852940,4042322160,4288741280,4294901760],[]),([4,2863311530,3974950092,4042321920,4278255360,4294901760],[]),([4,2863311530,3974950092,4042322160,4278255360,4294901760],[]),([4,2863311530,3974950124,4026593280,4291624908,4294901760],[]),([4,2863311530,3974950124,4042322160,4278255360,4294936712],[]),([4,2863311530,4008636142,4042322160,4287168392,4294936712],[(108,1),(140,3)]),([4,2863311547,3435973836,4042322160,4278255360,4294901760],[]),([4,3435973836,3937053354,4042322160,4278255360,4294901760],[]),([5,0,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,15,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,51,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2)]),([5,85,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,170,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2)]),([5,204,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,240,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,255,2863311530,3435973836,4042321920,4278255360,4294901760],[(96,2),(128,0)]),([5,255,2863311530,3435973836,4042322160,4278190080],[(2,2),(128,2)]),([5,255,2863311530,3435973836,4042322160,4278190080,4294967040],[(96,2),(128,2)]),([5,255,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2)])]
noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([5,255,2863311530,3435973836,4042322175,4278255360,4294901760],[(96,2)]),([5,4095,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,4369,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,8738,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,12336,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,13107,2863311530,3435921408,4042322160,4278255360],[(72,3)]),([5,13107,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,13311,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,17476,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,20560,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,21845,2863267840,3435973836,4042322160,4278255360],[(56,3)]),([5,21845,2863311530,3435956360,4042322160,4278255360,4294901760],[(96,4),(128,3),(168,3)]),([5,21845,2863311530,3435973836,4042301600,4278255360,4294901760],[(96,2),(128,0),(168,0)]),([5,21845,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,21845,2863311530,3435973836,4042322160,4278255445,4294901760],[(96,3),(128,0)]),([5,21845,2863311530,3435978205,4042322160,4278255360,4294901760],[(96,1)]),([5,22015,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2)]),([5,30583,2863311530,3435973836,4042322160,4278255360],[]),([5,30583,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,30583,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,34952,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,41120,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,43690,2863267840,3435973836,4042322160,4278255360,4294901760],[]),([5,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,43690,2863333375,3435973836,4042322160,4278255360],[]),([5,43690,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([5,49344,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,52428,2863311530,3435921408,4042322160,4278255360,4294901760],[]),([5,52428,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,52428,2863311530,3435973836,4042322160,4278255564,4294901760],[(72,0),(96,3),(128,0)]),([5,52428,2863311530,3435986943,4042322160,4278255360],[]),([5,52428,2863311530,3435986943,4042322160,4278255360,4294901760],[]),([5,61166,2863311530,3435973836,4042322160,4278255360],[]),([5,61166,2863311530,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([5,61440,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,61680,2863311530,3435973836,4042260480,4278255360,4294901760],[(168,0)]),([5,61680,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,61680,2863311530,3435973836,4042326015,4278255360],[]),([5,61680,2863311530,3435973836,4042326015,4278255360,4294901760],[]),([5,64250,2863311530,3435973836,4042322160,4278255360],[(2,1)]),([5,64250,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,64764,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2)]),([5,65520,2863311530,3435973836,4042322160,4278255360],[]),([5,65520,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,65535,16711935,252645135,2863311530,3435973836],[]),([5,65535,16711935,858993459,2863311530,4042322160],[]),([5,65535,16711935,1431655765,3435973836,4042322160],[]),([5,65535,16711935,2863311530,3435973836,4042322160],[]),([5,65535,858993459,1431655765,4042322160,4278255360],[]),([5,65535,858993459,2863311530,4042322160,4278255360],[]),([5,65535,1431655765,3435973836,4042322160,4278255360],[]),([5,65535,2290649224,4008636142,4042322160,4278255360],[]),([5,65535,2694881440,3435973836,4210752250,4278255360],[]),([5,65535,2863267840,3435973836,4042322160,4278255360,4294945450],[]),([5,65535,2863311530,3233857728,4244438268,4278255360],[]),([5,65535,2863311530,3368601800,4042322160,4278255360],[]),([5,65535,2863311530,3368601800,4042322160,4278255360,4294901760],[]),([5,65535,2863311530,3435921408,4042322160,4278255360,4294954188],[]),([5,65535,2863311530,3435956360,4042322160,4278255360],[(2,3)])]
noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([5,65535,2863311530,3435956360,4042322160,4278255360,4294901760],[]),([5,65535,2863311530,3435973836,3772834016,4278255360],[]),([5,65535,2863311530,3435973836,3772834016,4278255360,4294901760],[]),([5,65535,2863311530,3435973836,4008574976,4042322160,4278255360],[]),([5,65535,2863311530,3435973836,4026593280,4293984240],[]),([5,65535,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([5,65535,2863311530,3435973836,4037079200,4278255360],[]),([5,65535,2863311530,3435973836,4037079200,4278255360,4294901760],[]),([5,65535,2863311530,3435973836,4042260480,4278255360,4294963440],[]),([5,65535,2863311530,3435973836,4042301600,4278255360],[(2,0)]),([5,65535,2863311530,3435973836,4042301600,4278255360,4294901760],[]),([5,65535,2863311530,3435973836,4042321920,4278255360],[]),([5,65535,2863311530,3435973836,4042321920,4278255360,4294901760],[(128,0),(204,1)]),([5,65535,2863311530,3435973836,4042322160,4210688000,4278255360],[]),([5,65535,2863311530,3435973836,4042322160,4278255360],[]),([5,65535,2863311530,3435973836,4042322160,4278255360,4293918720],[]),([5,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,65535,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,65535,2863311530,3435973836,4042322160,4278255564],[(2,0)]),([5,65535,2863311530,3435973836,4042322160,4278255564,4294901760],[]),([5,65535,2863311530,3435973836,4042322160,4287168392],[(2,0)]),([5,65535,2863311530,3435973836,4042322160,4287168392,4294901760],[]),([5,1048575,2863311530,3435973836,4042322160,4278255360],[(2,3)]),([5,1048575,2863311530,3435973836,4042322160,4278255360,4293918720],[]),([5,1048575,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,3355443,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,3407871,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,5592405,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2)]),([5,5636095,2863311530,3435973836,4042322160,4278255360],[(2,4)]),([5,5636095,2863311530,3435973836,4042322160,4278255360,4289331200],[])]
noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([5,5636095,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,11184810,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,13421772,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2)]),([5,15790320,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,16777215,2863311530,3435973836,4042322160,4278190080,4294967040],[]),([5,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,16777215,2863311530,3435973836,4042322160,4294967040],[(2,2)]),([5,268435455,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,269488144,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,286331153,2290649224,4042322160,4278255360,4294901760],[]),([5,286331153,2863311530,3435973836,3772834016,4278255360,4294901760],[(96,2),(128,0)]),([5,286331153,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,286331153,2863311530,3435973836,4042322160,4278255360,4294906129],[(96,1)]),([5,286339891,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,286348629,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,286392319,2863311530,3435973836,4008574976,4042322160,4278255360],[]),([5,286392319,2863311530,3435973836,4042322160,4278255360],[(2,3)]),([5,286392319,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,538976288,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,572662306,2290649224,3435973836,4042322160,4278255360,4294901760],[]),([5,572662306,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,572662306,3149642683,3435973836,4042322160,4278255360,4294901760],[]),([5,572662306,3149642683,4042322160,4278255360,4294901760],[]),([5,572697258,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,805318656,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,808464432,2863311530,3233857728,3435973836,4278255360,4294901760],[]),([5,808464432,2863311530,3435973836,4026593280,4278255360,4294901760],[(128,1)]),([5,808464432,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,808464432,2863311530,3435973836,4092851187,4278255360,4294901760],[(196,0)]),([5,808464432,2863311530,3435973836,4210752250,4278255360,4294901760],[(196,0)]),([5,808464432,2863311530,4092851187,4278255360,4294901760],[]),([5,808513776,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,842150450,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,842150450,2863311530,4042322160,4278255360,4294901760],[(2,2)])]
noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([5,858796848,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,858993459,1431655765,4042322160,4278255360,4294901760],[]),([5,858993459,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,858993459,2694881440,4210752250,4278255360,4294901760],[]),([5,858993459,2863311530,3368601800,4042322160,4278255360,4294901760],[]),([5,858993459,2863311530,3435973836,3772834016,4278255360,4294901760],[]),([5,858993459,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([5,858993459,2863311530,3435973836,4029739056,4278255360,4294901760],[(132,1)]),([5,858993459,2863311530,3435973836,4037079200,4278255360,4294901760],[(132,1)]),([5,858993459,2863311530,3435973836,4042321920,4278255360,4294901760],[(204,2)]),([5,858993459,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,858993459,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,858993459,2863311530,3772834016,4278255360,4294901760],[]),([5,858993459,2863311530,4026593280,4293984240,4294901760],[]),([5,858993459,2863311530,4029739056,4278255360,4294901760],[]),([5,858993459,2863311530,4037079200,4278255360,4294901760],[]),([5,858993459,2863311530,4042321920,4278255360,4294901760],[(156,2)]),([5,858993459,2863311530,4042322160,4278255360,4294901760],[]),([5,858993459,2863311530,4042322160,4278255360,4294936712],[]),([5,858993663,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,859010935,2863311530,3435956360,4042322160,4278255360,4294901760],[(172,3)]),([5,859010935,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,859010935,2863311530,4042322160,4278255360,4294901760],[(2,3)]),([5,859045887,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,859045887,2863311530,4042322160,4278255360,4294954188],[]),([5,872415231,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1077952576,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1145324612,2290649224,2863311530,4042322160,4278255360,4294901760],[]),([5,1145324612,2863311530,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([5,1145324612,2863311530,3722304989,4042322160,4278255360,4294901760],[]),([5,1145324612,3722304989,4042322160,4278255360,4294901760],[]),([5,1145359564,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1342197760,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1347440720,2694881440,2863311530,3435973836,4278255360,4294901760],[]),([5,1347440720,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1347440720,2863311530,3435973836,4126537205,4278255360,4294901760],[]),([5,1347440720,2863311530,3435973836,4244438268,4278255360,4294901760],[]),([5,1347440720,3435973836,4126537205,4278255360,4294901760],[]),([5,1347481840,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1414812756,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1431328080,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1431655765,2863311530,3368601800,4042322160,4278255360,4294901760],[]),([5,1431655765,2863311530,3435973836,3772834016,4278255360,4294901760],[]),([5,1431655765,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([5,1431655765,2863311530,3435973836,4037079200,4278255360,4294901760],[]),([5,1431655765,2863311530,3435973836,4042321920,4278255360,4294901760],[(204,2)]),([5,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1431655765,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,1431655765,3233857728,4244438268,4278255360,4294901760],[]),([5,1431655765,3368601800,4042322160,4278255360,4294901760],[]),([5,1431655765,3435973836,3772834016,4278255360,4294901760],[]),([5,1431655765,3435973836,4026593280,4293984240,4294901760],[]),([5,1431655765,3435973836,4037079200,4278255360,4294901760],[]),([5,1431655765,3435973836,4042321920,4278255360,4294901760],[(156,2)]),([5,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([5,1431655765,3435973836,4042322160,4278255360,4294936712],[]),([5,1431655935,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1431664503,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1431699455,2863311530,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([5,1431699455,3435973836,4042322160,4278255360,4294945450],[]),([5,1442840575,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1886417008,2004318071,2863311530,3435973836,4278255360,4294901760],[(180,0)]),([5,1886417008,2290649224,2863311530,3435973836,4278255360,4294901760],[(56,2),(136,0)]),([5,1886417008,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1886417008,2863311530,3435973836,4278255360,4294901760],[]),([5,2004318071,2863311530,3435973836,4042322160,4278255360,4294901760],[(132,1),(172,3)]),([5,2004318071,2863311530,3435973836,4042322160,4278255360,4294936712],[(132,1),(172,3)]),([5,2004318071,4008636142,4042322160,4278255360,4294901760],[]),([5,2004353023,2863311530,3435973836,4042322160,4278255360,4294901760],[(132,1),(172,3)]),([5,2147516416,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,2155905152,2863311530,3435973836,4177066232,4278255360,4294901760],[(56,2),(72,2),(96,2),(128,4),(168,2)]),([5,2290124928,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,2290649224,2694881440,2863311530,3233857728,4278255360,4294901760],[]),([5,2290649224,2862656160,3435973836,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,3221274624,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,3233857728,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,3233857728,4042322160,4278255360,4294936712],[]),([5,2290649224,2863311530,3233857728,4177066232,4278255360,4294901760],[(128,0)]),([5,2290649224,2863311530,3233857728,4244438268,4278255360,4294901760],[(128,0)]),([5,2290649224,2863311530,3368601800,4042322160,4278255360,4294901760],[(128,0)]),([5,2290649224,2863311530,3368601800,4177066232,4278255360,4294901760],[(128,0)]),([5,2290649224,2863311530,3435187392,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,3435973836,3772834016,4278255360,4294901760],[(128,0)]),([5,2290649224,2863311530,3435973836,4026593280,4293984240,4294901760],[(96,3)]),([5,2290649224,2863311530,3435973836,4037079200,4278255360,4294901760],[(96,1)]),([5,2290649224,2863311530,3435973836,4042321920,4278255360,4294901760],[(96,2),(128,0),(204,2)]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656],[(96,2),(128,0)]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712],[(96,1)]),([5,2290649224,2863311530,3435973836,4042322160,4287168392,4294936712],[]),([5,2290649224,2863311530,3435986943,4042322160,4278255360,4294901760],[]),([5,2290649224,2863311530,3772834016,4008636142,4278255360,4294901760],[(196,0)]),([5,2290649224,2863311530,3772834016,4042322160,4278255360,4294901760],[])]
noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([5,2290649224,2863311530,3772834016,4278255360,4294901760],[(98,0)]),([5,2290649224,2863311530,3941264106,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([5,2290649224,2863311530,3974950124,4042322160,4278255360,4294901760],[(128,0)]),([5,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([5,2290649224,2863311530,4008636142,4042322160,4278255360,4294936712],[(96,1),(148,1),(188,3)]),([5,2290649224,3772834016,4008636142,4278255360,4294901760],[(148,0)]),([5,2290649224,3941264106,4042322160,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4278255360,4294936712],[]),([5,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290666700,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,2290679807,2863311530,3435973836,4042322160,4278255360],[(2,3)]),([5,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2684354560,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2684395520,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([5,2684395520,2863311530,3435973836,4042260480,4278255360,4294901760],[(96,0),(168,3)]),([5,2684395520,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2684395520,2863311530,3435973836,4042322160,4278255360,4294942720],[]),([5,2684395520,2863311530,3435973836,4042322160,4288741280,4294901760],[(168,0)]),([5,2684395520,2863311530,3972852940,4042322160,4278255360,4294901760],[]),([5,2692784256,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,2694881280,2863311530,3435973836,4042321920,4278255360,4294901760],[(128,0)]),([5,2694881280,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,2694881440,2852170240,2863311530,3435973836,4026593280,4294901760],[(128,1)]),([5,2694881440,2861083272,3435973836,4042322160,4278255360,4294901760],[]),([5,2694881440,2863311530,3221274624,3435973836,4278255360,4294901760],[]),([5,2694881440,2863311530,3233857728,3435973836,4278255360,4294901760],[]),([5,2694881440,2863311530,3368601800,3435973836,4278255360,4294901760],[]),([5,2694881440,2863311530,3368601800,4042322160,4278255360,4294901760],[]),([5,2694881440,2863311530,3368601800,4210752250,4278255360,4294901760],[(196,0)]),([5,2694881440,2863311530,3368601800,4278255360,4294901760],[]),([5,2694881440,2863311530,3431517320,4042322160,4278255360,4294901760],[(56,1),(96,1)]),([5,2694881440,2863311530,3435973836,3772834016,4278255360,4294901760],[])]
noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([5,2694881440,2863311530,3435973836,3941264106,4278255360,4294901760],[(196,0)]),([5,2694881440,2863311530,3435973836,3993038336,4042322160,4294901760],[(56,1),(128,1)]),([5,2694881440,2863311530,3435973836,4026531840,4278255360,4294901760],[]),([5,2694881440,2863311530,3435973836,4026593280,4278190080,4294901760],[(128,1),(172,0)]),([5,2694881440,2863311530,3435973836,4026593280,4278255360,4294901760],[(128,1)]),([5,2694881440,2863311530,3435973836,4026593280,4288741280,4294901760],[(56,1),(128,1)]),([5,2694881440,2863311530,3435973836,4026593280,4291624908,4294901760],[(128,1)]),([5,2694881440,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([5,2694881440,2863311530,3435973836,4037079200,4278255360,4294901760],[]),([5,2694881440,2863311530,3435973836,4039176384,4278255360,4294901760],[]),([5,2694881440,2863311530,3435973836,4042321920,4278255360,4294901760],[(128,0)]),([5,2694881440,2863311530,3435973836,4042322160,4194368000,4294901760],[(56,1),(96,1)]),([5,2694881440,2863311530,3435973836,4042322160,4278190080,4294967040],[(56,2),(96,2)]),([5,2694881440,2863311530,3435973836,4042322160,4278231040,4294901760],[(56,2),(96,2),(172,0),(196,0)]),([5,2694881440,2863311530,3435973836,4042322160,4278233600,4294901760],[(56,2),(96,2)]),([5,2694881440,2863311530,3435973836,4042322160,4278251520,4294901760],[(56,1),(96,1),(196,0)]),([5,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2694881440,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,2694881440,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,2694881440,2863311530,3435973836,4042322160,4278255360,4294942720],[(128,0)]),([5,2694881440,2863311530,3435973836,4042326015,4278255360,4294901760],[]),([5,2694881440,2863311530,3435973836,4092851187,4278255360,4294901760],[(196,0)]),([5,2694881440,2863311530,3435973836,4177066232,4278255360,4294901760],[(56,2),(96,2)]),([5,2694881440,2863311530,3435973836,4194368000,4210752250,4294901760],[]),([5,2694881440,2863311530,3435973836,4194368000,4278255360,4294901760],[]),([5,2694881440,2863311530,3435973836,4194368000,4294901760],[]),([5,2694881440,2863311530,3435973836,4205509290,4278255360,4294901760],[(196,0)]),([5,2694881440,2863311530,3435973836,4210096880,4278255360,4294901760],[(196,0)]),([5,2694881440,2863311530,3435973836,4210752250,4278255360,4294901760],[(196,0)]),([5,2694881440,2863311530,3972852940,4042322160,4278255360,4294901760],[]),([5,2694881440,3368601800,4210752250,4278255360,4294901760],[(148,0)]),([5,2694881440,3435973836,3941264106,4278255360,4294901760],[]),([5,2694881440,3435973836,4194368000,4210752250,4294901760],[]),([5,2694881440,3435973836,4205509290,4278255360,4294901760],[])]
noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([5,2694881440,3435973836,4210752250,4278255360,4294901760],[]),([5,2694884010,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2694902000,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2694905855,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2728567458,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2827528328,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,2829101216,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2)]),([5,2829625512,2863311530,3233857728,3435973836,4278255360,4294901760],[]),([5,2829625512,2863311530,3233857728,4278255360,4294901760],[]),([5,2829625512,2863311530,3435973836,4026593280,4278255360,4294901760],[(96,1),(128,1),(140,1)]),([5,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2)]),([5,2829625512,2863311530,3435973836,4177066232,4278255360,4294901760],[(56,2),(96,2)]),([5,2829625512,2863311530,3435973836,4210752250,4278255360,4294901760],[(196,0)]),([5,2829625512,3435973836,4210752250,4278255360,4294901760],[(148,0)]),([5,2862653600,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(196,0)]),([5,2862656160,2863311530,3435973836,4026593280,4042322160,4294901760],[]),([5,2862656160,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([5,2862656160,2863311530,3435973836,4026593280,4294901760],[(133,3)]),([5,2862656160,2863311530,3435973836,4042322160,4278255360,4293918720],[(56,3)]),([5,2862656160,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863180456,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863180456,3435973836,4042322160,4244438268,4278255360,4294901760],[(156,1)]),([5,2863180456,3435973836,4042322160,4278255360,4293984240,4294901760],[]),([5,2863180456,3435973836,4042322160,4278255360,4294770684,4294901760],[]),([5,2863180456,3435973836,4042322160,4278255360,4294901760],[(117,1)]),([5,2863311520,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863311530,3368601800,4042322160,4278255360,4294901760],[]),([5,2863311530,2863311530,3435973836,3772834016,4278255360,4294901760],[]),([5,2863311530,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([5,2863311530,2863311530,3435973836,4037079200,4278255360,4294901760],[(132,1)]),([5,2863311530,2863311530,3435973836,4042321920,4278255360,4294901760],[(204,2)]),([5,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,2863315899,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863332090,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2964369584,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3014898611,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3132799674,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3149642683,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3149660159,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3221225472,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3221274624,3435973836,4026593280,4293984240,4294901760],[]),([5,2863311530,3221274624,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3221274624,3435973836,4042322160,4290838464,4294901760],[]),([5,2863311530,3221274624,3435973836,4042322160,4291624908,4294901760],[]),([5,2863311530,3221274624,4042322160,4241292492,4278255360,4294901760],[]),([5,2863311530,3229663360,3431517320,4042322160,4278255360,4294901760],[(80,1),(104,1),(136,1)]),([5,2863311530,3229663360,3435973836,4037079200,4278255360,4294901760],[]),([5,2863311530,3229663360,3435973836,4042322160,4278255360,4294901760],[(136,0)]),([5,2863311530,3233857536,3435973836,4042321920,4278255360,4294901760],[]),([5,2863311530,3233857536,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3233857728,3368601800,4042322160,4278255360,4294901760],[]),([5,2863311530,3233857728,3431517320,4042322160,4278255360,4294901760],[(104,1),(136,1)]),([5,2863311530,3233857728,3435973836,3772834016,4278255360,4294901760],[]),([5,2863311530,3233857728,3435973836,3925928448,4042322160,4294901760],[(80,1),(136,1)]),([5,2863311530,3233857728,3435973836,3974950124,4278255360,4294901760],[]),([5,2863311530,3233857728,3435973836,3993038336,4042322160,4294901760],[(80,1),(136,1)]),([5,2863311530,3233857728,3435973836,4026593280,4293984240,4294901760],[]),([5,2863311530,3233857728,3435973836,4037079200,4278255360,4294901760],[]),([5,2863311530,3233857728,3435973836,4042321920,4278255360,4294901760],[]),([5,2863311530,3233857728,3435973836,4042322160,4194368000,4294901760],[(80,1),(104,1)]),([5,2863311530,3233857728,3435973836,4042322160,4278190080,4294967040],[(80,2),(104,2),(176,2)]),([5,2863311530,3233857728,3435973836,4042322160,4278233600,4294901760],[(80,2),(104,2),(176,2)]),([5,2863311530,3233857728,3435973836,4042322160,4278251520,4294901760],[(80,1),(104,1),(196,0)]),([5,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3233857728,3435973836,4042322160,4278255360,4294934656],[]),([5,2863311530,3233857728,3435973836,4042322160,4278255360,4294936712],[]),([5,2863311530,3233857728,3435973836,4126537205,4278255360,4294901760],[]),([5,2863311530,3233857728,3435973836,4177066232,4278255360,4294901760],[(80,2),(104,2)]),([5,2863311530,3233857728,3435973836,4243651824,4278255360,4294901760],[])]
noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3233857728,3435973836,4244438268,4278255360,4294901760],[]),([5,2863311530,3233857728,3435973836,4278255360,4293980400,4294901760],[]),([5,2863311530,3233857728,3722304989,4042322160,4278255360,4294901760],[]),([5,2863311530,3233857728,3974950124,4278255360,4294901760],[]),([5,2863311530,3233857728,4042322160,4241292492,4278255360,4294901760],[]),([5,2863311530,3233857728,4042322160,4278255360,4291611852,4294901760],[]),([5,2863311530,3233857728,4177066232,4278255360,4294901760],[]),([5,2863311530,3233857728,4244438268,4278255360,4291624908,4294901760],[]),([5,2863311530,3233857728,4244438268,4278255360,4294901760],[]),([5,2863311530,3233860812,3435973836,4042322160,4278255360,4294901760],[(104,2)]),([5,2863311530,3233870064,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3233873919,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3301229764,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3364407432,3435973836,4042322160,4278255360,4294901760],[(104,2),(136,0),(112,1)]),([5,2863311530,3364407432,4026593280,4042322160,4278255360,4294901760],[]),([5,2863311530,3364407432,4042322160,4205509290,4278255360,4294901760],[(156,1)]),([5,2863311530,3364407432,4042322160,4278255360,4294901760],[(102,1),(82,1)]),([5,2863311530,3368077504,3435973836,4042322160,4278255360,4294901760],[(104,2)]),([5,2863311530,3368601800,3368601800,4042322160,4278255360,4294901760],[]),([5,2863311530,3368601800,3435973836,4042322160,4194368000,4294901760],[(80,1),(104,1)]),([5,2863311530,3368601800,3435973836,4042322160,4278255360,4294901760],[(104,2)]),([5,2863311530,3368601800,3435973836,4177066232,4278255360,4294901760],[(80,2),(104,2)]),([5,2863311530,3368601800,3435973836,4244438268,4278255360,4294901760],[]),([5,2863311530,3368601800,3941264106,4042322160,4278255360,4294901760],[(188,0)]),([5,2863311530,3368601800,4008636142,4042322160,4278255360,4294901760],[(188,0)]),([5,2863311530,3368601800,4026593280,4042322160,4278255360,4294901760],[]),([5,2863311530,3368601800,4042322160,4042322160,4278255360,4294901760],[]),([5,2863311530,3368601800,4042322160,4177066232,4278255360,4294901760],[]),([5,2863311530,3368601800,4042322160,4194368000,4210752250,4294901760],[]),([5,2863311530,3368601800,4042322160,4194368000,4278255360,4294901760],[]),([5,2863311530,3368601800,4042322160,4194368000,4294901760],[]),([5,2863311530,3368601800,4042322160,4210752250,4278255360,4294901760],[(196,0)]),([5,2863311530,3368601800,4042322160,4244438268,4278255360,4294901760],[]),([5,2863311530,3368601800,4042322160,4278124286,4278255360,4294901760],[(196,0)]),([5,2863311530,3368601800,4042322160,4278190080,4278255360,4294901760],[])]
noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3368601800,4042322160,4278255360,4278255360,4294901760],[]),([5,2863311530,3368601800,4042322160,4278255360,4289396650,4294901760],[(204,0)]),([5,2863311530,3368601800,4042322160,4278255360,4291362760,4294901760],[]),([5,2863311530,3368601800,4042322160,4278255360,4291624908,4294901760],[]),([5,2863311530,3368601800,4042322160,4278255360,4293984240,4294901760],[(204,0)]),([5,2863311530,3368601800,4042322160,4278255360,4294639610,4294901760],[(204,0)]),([5,2863311530,3368601800,4042322160,4278255360,4294901760],[]),([5,2863311530,3368601800,4042322160,4278255360,4294901760,4294967040],[]),([5,2863311530,3368601800,4177066232,4210752250,4278255360,4294901760],[(196,0)]),([5,2863311530,3368601800,4177066232,4278255360,4294901760],[]),([5,2863311530,3368601800,4210752250,4244438268,4278255360,4294901760],[(188,0)]),([5,2863311530,3368601800,4244438268,4278255360,4294901760],[]),([5,2863311530,3435184320,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435187392,3435973836,4026593280,4293984240,4294901760],[]),([5,2863311530,3435187392,3435973836,4042322160,4278255360,4293918720],[(80,3)]),([5,2863311530,3435187392,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435711688,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435711688,4042322160,4210752250,4278255360,4294901760],[(156,1)]),([5,2863311530,3435711688,4042322160,4278255360,4293984240,4294901760],[]),([5,2863311530,3435711688,4042322160,4278255360,4294639610,4294901760],[]),([5,2863311530,3435711688,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973824,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435973836,3772834016,4278255360,4294901760],[]),([5,2863311530,3435973836,3435973836,4026593280,4293984240,4294901760],[]),([5,2863311530,3435973836,3435973836,4037079200,4278255360,4294901760],[]),([5,2863311530,3435973836,3435973836,4042321920,4278255360,4294901760],[(204,2)]),([5,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435973836,4042322160,4278255360,4294936712],[]),([5,2863311530,3435973836,3435973887,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435978205,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435982574,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435986172,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3439329279,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3503345872,4042322160,4278255360,4294901760],[])]
noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,3587560917,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3705461980,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3722313727,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3758153728,3772834016,4278255360,4294901760],[(152,1)]),([5,2863311530,3435973836,3758153728,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3768639648,4004179626,4278255360,4294901760],[(108,1)]),([5,2863311530,3435973836,3768639648,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3768639648,4278255360,4294901760],[(102,1)]),([5,2863311530,3435973836,3770736832,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3772834016,3772834016,4278255360,4294901760],[]),([5,2863311530,3435973836,3772834016,3941264106,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,3772834016,3974950124,4278255360,4294901760],[]),([5,2863311530,3435973836,3772834016,3993038336,4008636142,4294901760],[]),([5,2863311530,3435973836,3772834016,3993038336,4042322160,4294901760],[(144,1)]),([5,2863311530,3435973836,3772834016,3993038336,4294901760],[]),([5,2863311530,3435973836,3772834016,4008636142,4278255360,4294901760],[(196,0)]),([5,2863311530,3435973836,3772834016,4026593280,4278255360,4294901760],[(144,1)]),([5,2863311530,3435973836,3772834016,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3772834016,4210752250,4278255360,4294901760],[(196,0)]),([5,2863311530,3435973836,3772834016,4244438268,4278255360,4294901760],[]),([5,2863311530,3435973836,3772834016,4278124286,4278255360,4294901760],[(196,0)]),([5,2863311530,3435973836,3772834016,4278190080,4278255360,4294901760],[]),([5,2863311530,3435973836,3772834016,4278255360,4278255360,4294901760],[]),([5,2863311530,3435973836,3772834016,4278255360,4289396650,4294901760],[(140,1),(204,0)]),([5,2863311530,3435973836,3772834016,4278255360,4291624908,4294901760],[]),([5,2863311530,3435973836,3772834016,4278255360,4292935648,4294901760],[(116,1),(204,0)]),([5,2863311530,3435973836,3772834016,4278255360,4293853166,4294901760],[(204,0)]),([5,2863311530,3435973836,3772834016,4278255360,4293984240,4294901760],[(204,0)]),([5,2863311530,3435973836,3772834016,4278255360,4294901760],[]),([5,2863311530,3435973836,3772834016,4278255360,4294901760,4294967040],[]),([5,2863311530,3435973836,3937069738,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3435973836,3938511552,4042322160,4278255360,4294901760],[(148,1)]),([5,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3435973836,3941264106,4244438268,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3435973836,3972852940,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3974950124,4026593280,4278255360,4294901760],[(144,1)])]
noncomputable def K_20 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3974950124,4210752250,4278255360,4294901760],[(196,0)]),([5,2863311530,3435973836,4007718624,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3435973836,4008373994,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3435973836,4008505068,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3435973836,4008636142,4026593280,4293984240,4294901760],[(188,3)]),([5,2863311530,3435973836,4008636142,4037079200,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3435973836,4008636142,4041273568,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3435973836,4008636142,4042321920,4278255360,4294901760],[(148,1),(188,3),(204,2)]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294906129],[(148,1),(188,3)]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294936712],[(148,1),(188,3)]),([5,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3435973836,4026531840,4026593280,4293984240,4294901760],[(192,3)]),([5,2863311530,3435973836,4026531840,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4026531840,4042322160,4278255360,4294954188],[]),([5,2863311530,3435973836,4026531840,4042322160,4278255360,4294963200],[(152,3)]),([5,2863311530,3435973836,4026572800,4042301600,4278255360,4294901760],[(112,0),(144,0),(184,0),(152,1)]),([5,2863311530,3435973836,4026572800,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4026580992,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4026593280,4026593280,4293984240,4294901760],[]),([5,2863311530,3435973836,4026593280,4037079200,4278255360,4294901760],[(152,1)]),([5,2863311530,3435973836,4026593280,4042260480,4042322160,4278190080],[(112,2),(184,0)]),([5,2863311530,3435973836,4026593280,4042260480,4278190080],[(102,0),(134,2),(82,3),(106,1),(112,2),(114,1),(113,3),(144,0),(145,4),(154,0),(153,2)]),([5,2863311530,3435973836,4026593280,4042260480,4278255360,4294901760],[(184,3),(152,1)]),([5,2863311530,3435973836,4026593280,4042260480,4278255360,4294954188],[(184,3)]),([5,2863311530,3435973836,4026593280,4042260480,4278255360,4294963200],[(144,3),(184,3)]),([5,2863311530,3435973836,4026593280,4042260480,4278255360,4294963440],[(144,0),(184,0)]),([5,2863311530,3435973836,4026593280,4042301600,4278255360,4294901760],[(144,0),(184,0),(152,1)]),([5,2863311530,3435973836,4026593280,4042309824,4278255360,4294901760],[(152,1),(204,1)]),([5,2863311530,3435973836,4026593280,4042321920,4278255360,4294901760],[(152,1),(204,1)]),([5,2863311530,3435973836,4026593280,4042322160,4205445120,4278255360],[(112,3),(184,3)]),([5,2863311530,3435973836,4026593280,4042322160,4210096880,4294901760],[]),([5,2863311530,3435973836,4026593280,4042322160,4210688000,4278255360],[(112,3),(184,3)]),([5,2863311530,3435973836,4026593280,4042322160,4278255360,4293918720],[(112,3),(116,1),(144,3)]),([5,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4026593280,4042322160,4278255360,4294936712],[]),([5,2863311530,3435973836,4026593280,4042322160,4278255360,4294942720],[])]
noncomputable def K_21 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4026593280,4042322160,4278255615,4294901760],[]),([5,2863311530,3435973836,4026593280,4042322160,4283826005,4294901760],[]),([5,2863311530,3435973836,4026593280,4042322160,4287168392,4294901760],[(112,0),(144,0)]),([5,2863311530,3435973836,4026593280,4042322160,4288741280,4294901760],[(116,1)]),([5,2863311530,3435973836,4026593280,4042322160,4290838464,4294901760],[]),([5,2863311530,3435973836,4026593280,4042322160,4291559424,4294901760],[(196,0)]),([5,2863311530,3435973836,4026593280,4042322160,4291611852,4294901760],[]),([5,2863311530,3435973836,4026593280,4042322160,4291624704,4294901760],[]),([5,2863311530,3435973836,4026593280,4042322160,4291624908,4294901760],[]),([5,2863311530,3435973836,4026593280,4042322160,4293918720],[(14,2),(157,0)]),([5,2863311530,3435973836,4026593280,4042322160,4293918720,4293984240],[]),([5,2863311530,3435973836,4026593280,4042322160,4293918720,4294901760],[(196,0)]),([5,2863311530,3435973836,4026593280,4042322160,4293980400,4294901760],[]),([5,2863311530,3435973836,4026593280,4042322160,4293984000,4294901760],[(116,1)]),([5,2863311530,3435973836,4026593280,4042322160,4293984240,4294901760],[]),([5,2863311530,3435973836,4026593280,4042322160,4294770684,4294901760],[]),([5,2863311530,3435973836,4026593280,4205509290,4293984240,4294901760],[]),([5,2863311530,3435973836,4026593280,4210096880,4294901760],[]),([5,2863311530,3435973836,4026593280,4210752250,4293984240,4294901760],[]),([5,2863311530,3435973836,4026593280,4241292492,4293984240,4294901760],[]),([5,2863311530,3435973836,4026593280,4244438268,4291624908,4294901760],[]),([5,2863311530,3435973836,4026593280,4244438268,4293984240,4294901760],[]),([5,2863311530,3435973836,4026593280,4244438268,4294770684,4294901760],[]),([5,2863311530,3435973836,4026593280,4293918720],[(103,3),(111,3),(10,3),(11,3)]),([5,2863311530,3435973836,4026593280,4293918720,4293984240],[(18,3)]),([5,2863311530,3435973836,4026593280,4293918720,4293984240,4294901760],[]),([5,2863311530,3435973836,4026593280,4293918720,4294901760],[(102,3),(134,3),(142,3)]),([5,2863311530,3435973836,4026593280,4293980400,4294901760],[]),([5,2863311530,3435973836,4026593280,4293984240,4293984240,4294901760],[]),([5,2863311530,3435973836,4026593280,4293984240,4294639610,4294901760],[]),([5,2863311530,3435973836,4026593280,4293984240,4294770684,4294901760],[]),([5,2863311530,3435973836,4026593280,4293984240,4294901760],[]),([5,2863311530,3435973836,4026593280,4293984240,4294901760,4294901760],[])]
noncomputable def K_22 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4026593280,4293984240,4294901760,4294945450],[(180,3)]),([5,2863311530,3435973836,4026593280,4293984240,4294901760,4294954188],[]),([5,2863311530,3435973836,4026593280,4293984240,4294901760,4294963200],[(148,3)]),([5,2863311530,3435973836,4026593280,4293984240,4294901760,4294963440],[]),([5,2863311530,3435973836,4026593280,4293984240,4294901760,4294967280],[]),([5,2863311530,3435973836,4026593280,4294770684,4294901760],[]),([5,2863311530,3435973836,4026593520,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4026597375,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4029739056,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4029739056,4278255360,4281597747,4294901760],[]),([5,2863311530,3435973836,4029739056,4278255360,4294901760],[(102,1)]),([5,2863311530,3435973836,4031836240,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4034982016,4042322160,4278255360,4294901760],[(144,0)]),([5,2863311530,3435973836,4034982016,4042322160,4287168392,4294901760],[(112,0),(144,0)]),([5,2863311530,3435973836,4037058720,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4037058720,4278255360,4289374890,4294901760],[(140,2),(204,0)]),([5,2863311530,3435973836,4037058720,4278255360,4294901760],[(102,1),(134,3),(106,0)]),([5,2863311530,3435973836,4037079040,4042322160,4278255360,4294901760],[(144,0),(204,2)]),([5,2863311530,3435973836,4037079040,4278255360,4289396480,4294901760],[(196,2)]),([5,2863311530,3435973836,4037079040,4278255360,4294901760],[(102,1),(156,2),(158,2),(157,4)]),([5,2863311530,3435973836,4037079200,4037079200,4278255360,4294901760],[]),([5,2863311530,3435973836,4037079200,4042322160,4278255360,4289331200],[(112,4)]),([5,2863311530,3435973836,4037079200,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4037079200,4042322160,4291624908,4294901760],[]),([5,2863311530,3435973836,4037079200,4205509290,4278255360,4294901760],[(196,3)]),([5,2863311530,3435973836,4037079200,4210752250,4278255360,4294901760],[]),([5,2863311530,3435973836,4037079200,4243389676,4278255360,4294901760],[]),([5,2863311530,3435973836,4037079200,4244438268,4278255360,4294901760],[]),([5,2863311530,3435973836,4037079200,4278255360,4278255360,4294901760],[]),([5,2863311530,3435973836,4037079200,4278255360,4288741280,4294901760],[(116,1),(204,4)]),([5,2863311530,3435973836,4037079200,4278255360,4289331200],[(102,1)]),([5,2863311530,3435973836,4037079200,4278255360,4289331200,4289396650],[(180,1)]),([5,2863311530,3435973836,4037079200,4278255360,4289396650,4294901760],[(140,1)]),([5,2863311530,3435973836,4037079200,4278255360,4291624908,4294901760],[]),([5,2863311530,3435973836,4037079200,4278255360,4293853166,4294901760],[])]
noncomputable def K_23 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4037079200,4278255360,4293984240,4294901760],[]),([5,2863311530,3435973836,4037079200,4278255360,4294639610,4294901760],[]),([5,2863311530,3435973836,4037079200,4278255360,4294901760],[(102,1)]),([5,2863311530,3435973836,4037079200,4278255360,4294901760,4294901760],[]),([5,2863311530,3435973836,4037079200,4278255360,4294901760,4294945450],[(180,3),(196,2)]),([5,2863311530,3435973836,4037079200,4278255360,4294901760,4294954188],[]),([5,2863311530,3435973836,4037079200,4278255360,4294901760,4294963360],[(148,3)]),([5,2863311530,3435973836,4037079200,4278255360,4294901760,4294963440],[(148,0)]),([5,2863311530,3435973836,4037079200,4278255360,4294901760,4294967040],[(156,2)]),([5,2863311530,3435973836,4037079200,4278255360,4294901760,4294967210],[(180,2)]),([5,2863311530,3435973836,4037079200,4289396650,4291624908,4294901760],[(108,1)]),([5,2863311530,3435973836,4037079200,4291624908,4294901760],[(100,1),(102,1)]),([5,2863311530,3435973836,4039164096,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4039176192,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4039176384,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4039176384,4244438268,4278255360,4294901760],[]),([5,2863311530,3435973836,4039176384,4278255360,4293984240,4294901760],[]),([5,2863311530,3435973836,4039176384,4278255360,4294770684,4294901760],[]),([5,2863311530,3435973836,4041273568,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4041273568,4278255360,4289396650,4294901760],[(140,1),(204,4)]),([5,2863311530,3435973836,4041273568,4278255360,4291624908,4294901760],[]),([5,2863311530,3435973836,4041273568,4278255360,4293853166,4294901760],[]),([5,2863311530,3435973836,4041273568,4278255360,4294901760],[]),([5,2863311530,3435973836,4042321920,4042321920,4278255360,4294901760],[(204,2)]),([5,2863311530,3435973836,4042321920,4042322160,4278255360,4294901760],[(204,2)]),([5,2863311530,3435973836,4042321920,4210752170,4278255360,4294901760],[(156,1),(196,3),(204,2)]),([5,2863311530,3435973836,4042321920,4210752250,4278255360,4294901760],[(156,1),(196,3),(204,2)]),([5,2863311530,3435973836,4042321920,4244438220,4278255360,4294901760],[(204,2)]),([5,2863311530,3435973836,4042321920,4244438268,4278255360,4294901760],[(204,2)]),([5,2863311530,3435973836,4042321920,4278255360,4278255360,4294901760],[(196,2)]),([5,2863311530,3435973836,4042321920,4278255360,4289396650,4294901760],[(140,1),(196,2),(204,4)]),([5,2863311530,3435973836,4042321920,4278255360,4291624908,4294901760],[(196,2),(204,4)]),([5,2863311530,3435973836,4042321920,4278255360,4293984000,4294901760],[(116,1),(196,2),(204,0)]),([5,2863311530,3435973836,4042321920,4278255360,4293984240,4294901760],[(196,2),(204,0)]),([5,2863311530,3435973836,4042321920,4278255360,4294901760],[(156,2),(158,2),(157,4)]),([5,2863311530,3435973836,4042321920,4278255360,4294901760,4294967040],[(156,2)])]
noncomputable def K_24 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4042321920,4278255360,4294901760,4294967210],[(180,2),(156,2)]),([5,2863311530,3435973836,4042321920,4278255360,4294901760,4294967244],[(172,2),(156,2)]),([5,2863311530,3435973836,4042321920,4278255360,4294901760,4294967280],[(156,2)]),([5,2863311530,3435973836,4042322080,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322080,4278255360,4289396650,4294901760],[(140,1),(204,4)]),([5,2863311530,3435973836,4042322080,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322080,4278255360,4294901760,4294967040],[(156,2)]),([5,2863311530,3435973836,4042322080,4278255360,4294901760,4294967210],[(180,2)]),([5,2863311530,3435973836,4042322112,4042322160,4278255360,4294901760],[(204,2)]),([5,2863311530,3435973836,4042322112,4278255360,4291624908,4294901760],[(196,2),(204,4)]),([5,2863311530,3435973836,4042322112,4278255360,4294901760],[(156,2),(158,2),(157,4)]),([5,2863311530,3435973836,4042322112,4278255360,4294901760,4294967040],[(156,2)]),([5,2863311530,3435973836,4042322112,4278255360,4294901760,4294967244],[(172,2),(156,2)]),([5,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4042322160,4278255360,4294936712],[]),([5,2863311530,3435973836,4042322160,4042322175,4278255360,4294901760],[(112,2)]),([5,2863311530,3435973836,4042322160,4042322931,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4042323445,4278255360,4294901760],[(112,2)]),([5,2863311530,3435973836,4042322160,4042324730,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4042325244,4278255360,4294901760],[(112,2)]),([5,2863311530,3435973836,4042322160,4042326000,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4042326015,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4043309055,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4059165169,4278255360,4294901760],[(112,2)]),([5,2863311530,3435973836,4042322160,4076008178,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4080268083,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4092654576,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4092851187,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4092854271,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4109694196,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4116051285,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4126209520,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4126537205,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4126539775,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4160223223,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4169726088,4278255360,4294901760],[(112,2),(144,3),(152,0)]),([5,2863311530,3435973836,4042322160,4176541936,4278255360,4294901760],[(112,2)])]
noncomputable def K_25 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760],[(112,2)]),([5,2863311530,3435973836,4042322160,4177066232,4278255360,4294936712],[(112,1)]),([5,2863311530,3435973836,4042322160,4205488810,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4205506560,4278255360,4294901760],[(144,3),(188,0),(156,1),(196,3),(204,2)]),([5,2863311530,3435973836,4042322160,4205509290,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4205509290,4291624908,4294901760],[(196,3)]),([5,2863311530,3435973836,4042322160,4207475400,4278255360,4294901760],[(156,1)]),([5,2863311530,3435973836,4042322160,4209703658,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4210094320,4278255360,4294901760],[(112,2),(188,0),(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4210096880,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4210621176,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4210752000,4278255360,4294901760],[(156,1),(196,3),(204,2)]),([5,2863311530,3435973836,4042322160,4210752170,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4210752240,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4210752250,4278255360,4294903045],[(100,1),(116,1),(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4210752250,4278255360,4294936712],[(156,1),(196,0)]),([5,2863311530,3435973836,4042322160,4210753535,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4227595259,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4241280204,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4241289216,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4243389676,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4243648752,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4243651824,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4244176120,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4244438016,4278255360,4294901760],[(204,2)]),([5,2863311530,3435973836,4042322160,4244438220,4278255360,4294901760],[(204,2)]),([5,2863311530,3435973836,4042322160,4244438256,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4244438268,4278255360,4294936712],[]),([5,2863311530,3435973836,4042322160,4244439039,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4261281277,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4277075694,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4277206768,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4277862138,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4277993212,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(156,1),(196,3)]),([5,2863311530,3435973836,4042322160,4278255360,4293980400,4294901760],[(188,0),(156,1),(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4293982960,4294901760],[(156,1),(204,3)])]
noncomputable def K_26 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4042322160,4278255360,4293983472,4294901760],[(188,0),(156,1),(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4293984240,4294901775],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4293984240,4294936712],[]),([5,2863311530,3435973836,4042322160,4278255360,4293984255,4294901760],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294180851,4294901760],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294311925,4294901760],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294508536,4294901760],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294638330,4294901760],[(156,1),(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294639600,4294901760],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294639610,4294901760],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294769916,4294901760],[(188,0),(156,1),(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294770672,4294901760],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294901758,4294901760],[(204,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967280],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967290],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967292],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901775],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901845],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901964],[]),([5,2863311530,3435973836,4042322160,4278255360,4294902015,4294954188],[(140,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040],[(156,2)]),([5,2863311530,3435973836,4042322160,4278255360,4294906129],[]),([5,2863311530,3435973836,4042322160,4278255360,4294914867,4294954188],[(148,0),(156,2)]),([5,2863311530,3435973836,4042322160,4278255360,4294923605,4294945450],[(180,3),(188,0),(196,2)]),([5,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,2863311530,3435973836,4042322160,4278255360,4294936712],[(141,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294936712],[(140,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294945450],[(180,3),(188,0),(196,2)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294954188],[(140,3)])]
noncomputable def K_27 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440],[(148,0),(196,1)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294965496],[(172,0),(180,0),(148,0),(196,1)]),([5,2863311530,3435973836,4042322160,4278255360,4294942720],[(149,0),(157,2)]),([5,2863311530,3435973836,4042322160,4278255360,4294942880,4294954188],[(148,0),(188,0),(156,2)]),([5,2863311530,3435973836,4042322160,4278255360,4294942880,4294967040],[(156,2)]),([5,2863311530,3435973836,4042322160,4278255360,4294945450,4294951104],[(140,3),(148,0),(156,2)]),([5,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188],[(140,3),(148,0),(156,2)]),([5,2863311530,3435973836,4042322160,4278255360,4294945450,4294963200],[(140,3),(148,0),(156,2)]),([5,2863311530,3435973836,4042322160,4287168392,4294936712],[(109,1),(141,3)]),([5,2863311530,3435978205,4042322160,4278255360,4294901760],[]),([5,2863311530,3435978205,4042322160,4278255360,4294901760,4294945450],[(180,3),(196,1)]),([5,2863311530,3435986943,4042322160,4278255360,4294901760,4294954188],[]),([5,2863311530,3722304989,4008636142,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([5,2863311530,3972852940,4026593280,4042322160,4278255360,4294901760],[]),([5,2863311530,3972852940,4042322160,4278255360,4294901760],[(157,1)]),([5,2863311530,3974950124,4042322160,4278255360,4291624908,4294901760],[]),([5,2863311530,4008636142,4042322160,4241292492,4278255360,4294901760],[(140,1),(180,3)]),([5,2863333375,3435973836,4042322160,4278255360,4294901760,4294945450],[]),([5,3149642683,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,0,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,858993459,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,858993459,2863311530,4042322160,4278255360,4294901760],[]),([6,0,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,1431655765,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_28 : List (List ℕ × List (ℕ × ℕ)) := [([6,0,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,1),(169,3)]),([6,255,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,2),(96,2),(129,1),(169,3)]),([6,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[(96,2),(128,0)]),([6,13107,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(129,1),(133,1),(169,3)]),([6,13107,2863311530,3435973836,4042322160,4278255360,4294901760,4294954188],[]),([6,21845,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(96,2),(98,1),(128,0),(129,1),(133,1),(169,3)]),([6,21845,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450],[(96,4),(128,3),(252,1)]),([6,43690,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,43690,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(129,1),(133,1),(169,3)]),([6,52428,65535,2863311530,3435973836,4042322160,4278255360],[(128,1)]),([6,52428,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,1)]),([6,52428,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(96,2),(98,1),(128,0),(129,1),(133,1),(169,3)]),([6,61680,65535,2863311530,3435973836,4042322160,4278255360],[])]
noncomputable def K_29 : List (List ℕ × List (ℕ × ℕ)) := [([6,61680,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,61680,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,4),(129,1),(169,0)]),([6,65535,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,16711935,2863311530,3435973836,4042322160],[(2,0)]),([6,65535,16711935,2863311530,3435973836,4042322160,4278255360],[(2,0)]),([6,65535,16711935,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,858993459,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,858993459,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,858993459,2863311530,4042322160,4278255360],[(14,1)]),([6,65535,858993459,2863311530,4042322160,4278255360,4294901760],[]),([6,65535,1431655765,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,1431655765,3435973836,4042322160,4278255360],[(14,1)])]
noncomputable def K_30 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2290649224,2863311530,3435973836,4042322160,4278255360],[(136,1)]),([6,65535,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(136,1)]),([6,65535,2694881440,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863267840,2863311530,3435973836,4042322160,4278255360],[(2,3)]),([6,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,2863333375,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3233857728,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435921408,3435973836,4042322160,4278255360],[(2,3)]),([6,65535,2863311530,3435921408,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_31 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,2863311530,3435973836,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,3435986943,4042322160,4278255360],[]),([6,65535,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,4008636142,4042322160,4278255360],[(196,1)]),([6,65535,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(196,1)]),([6,65535,2863311530,3435973836,4026593280,4042322160,4278255360],[]),([6,65535,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(128,1)]),([6,65535,2863311530,3435973836,4042260480,4042322160,4278255360],[(2,0)]),([6,65535,2863311530,3435973836,4042260480,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,4042322160,4042322160,4278255360],[]),([6,65535,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,4042322160,4042326015,4278255360],[]),([6,65535,2863311530,3435973836,4042322160,4042326015,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,4042322160,4210752250,4278255360],[(204,1)])]
noncomputable def K_32 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(204,1)]),([6,65535,2863311530,3435973836,4042322160,4244438268,4278255360],[]),([6,65535,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(96,2)]),([6,65535,2863311530,3435973836,4042322160,4278255360],[(14,1)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4293984240],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(129,1),(133,1)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450],[(252,1)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294954188],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294963440],[(96,2),(252,1)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294945450],[(2,3),(204,1)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294954188],[(2,3)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294963440],[(2,0),(204,1)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294967295],[])]
noncomputable def K_33 : List (List ℕ × List (ℕ × ℕ)) := [([6,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(172,1),(220,3)]),([6,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,2),(133,1),(173,3)]),([6,286331153,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(128,2),(168,0),(196,1),(244,3)]),([6,286331153,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(98,2),(128,0),(130,0),(129,1),(133,1),(169,3),(173,3)]),([6,572662306,858993459,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,572662306,858993459,2863311530,4042322160,4278255360,4294901760],[]),([6,572662306,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,1),(133,1),(169,3),(173,3)]),([6,808464432,858993459,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,808464432,858993459,2863311530,4042322160,4278255360,4294901760],[]),([6,808464432,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,2),(129,1),(169,3),(173,0),(197,0)]),([6,858993459,858993459,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,858993459,858993459,2863311530,4042322160,4278255360,4294901760],[]),([6,858993459,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,858993459,1431655765,2863311530,4042322160,4278255360,4294901760],[])]
noncomputable def K_34 : List (List ℕ × List (ℕ × ℕ)) := [([6,858993459,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([6,858993459,1431655765,4042322160,4278255360,4294901760],[(10,2),(14,0)]),([6,858993459,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(136,2),(176,0)]),([6,858993459,2290649224,2863311530,4042322160,4278255360,4294901760],[(104,2),(136,0)]),([6,858993459,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,858993459,2694881440,2863311530,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,2863311530,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,3149642683,3435973836,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,3149642683,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,3233857728,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(196,1),(244,3)]),([6,858993459,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(172,1)]),([6,858993459,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,3435973836,4042322160,4092851187,4278255360,4294901760],[(204,1),(252,3)])]
noncomputable def K_35 : List (List ℕ × List (ℕ × ℕ)) := [([6,858993459,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(204,1),(252,3)]),([6,858993459,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(96,2)]),([6,858993459,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(260,3)]),([6,858993459,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,1),(133,1),(169,3),(173,3)]),([6,858993459,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,858993459,2863311530,4008636142,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([6,858993459,2863311530,4026593280,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,4042322160,4042322160,4278255360,4294901760],[]),([6,858993459,2863311530,4042322160,4092851187,4278255360,4294901760],[(156,1),(196,3)]),([6,858993459,2863311530,4042322160,4210752250,4278255360,4294901760],[(156,1),(196,3)]),([6,858993459,2863311530,4042322160,4244438268,4278255360,4294901760],[]),([6,858993459,2863311530,4042322160,4278255360,4293984240,4294901760],[(204,3)]),([6,858993459,2863311530,4042322160,4278255360,4294901760],[(10,2),(14,0)])]
noncomputable def K_36 : List (List ℕ × List (ℕ × ℕ)) := [([6,858993459,2863311530,4042322160,4278255360,4294901760,4294967295],[]),([6,859045887,2863311530,3435921408,3435973836,4042322160,4278255360,4294901760],[(220,3)]),([6,859045887,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(129,1),(133,1),(173,3)]),([6,1145324612,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,1145324612,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([6,1145324612,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,1),(133,1),(169,3),(173,3)]),([6,1347440720,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,1347440720,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([6,1347440720,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,2),(129,1),(169,3),(173,0)]),([6,1431655765,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(136,2),(176,0)]),([6,1431655765,2290649224,3435973836,4042322160,4278255360,4294901760],[(104,2),(136,0)]),([6,1431655765,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_37 : List (List ℕ × List (ℕ × ℕ)) := [([6,1431655765,2694881440,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760],[]),([6,1431655765,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(196,1),(244,3)]),([6,1431655765,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(128,1)]),([6,1431655765,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[]),([6,1431655765,2863311530,3435973836,4042322160,4126537205,4278255360,4294901760],[]),([6,1431655765,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(96,2),(204,1),(252,3)]),([6,1431655765,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[]),([6,1431655765,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(260,3)]),([6,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,1),(133,1),(169,3),(173,3)]),([6,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,1431655765,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,3435973836,3722304989,4042322160,4278255360,4294901760],[])]
noncomputable def K_38 : List (List ℕ × List (ℕ × ℕ)) := [([6,1431655765,3435973836,4008636142,4042322160,4278255360,4294901760],[(148,1),(188,3)]),([6,1431655765,3435973836,4026593280,4042322160,4278255360,4294901760],[]),([6,1431655765,3435973836,4042322160,4042322160,4278255360,4294901760],[]),([6,1431655765,3435973836,4042322160,4126537205,4278255360,4294901760],[]),([6,1431655765,3435973836,4042322160,4210752250,4278255360,4294901760],[(156,1),(196,3)]),([6,1431655765,3435973836,4042322160,4244438268,4278255360,4294901760],[]),([6,1431655765,3435973836,4042322160,4278255360,4293984240,4294901760],[(204,3)]),([6,1431655765,3435973836,4042322160,4278255360,4294901760],[(10,2),(14,0)]),([6,1431655765,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,1431699455,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760],[(220,3)]),([6,1431699455,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(129,1),(133,1),(173,3)]),([6,2004318071,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(172,1),(220,3),(136,2),(176,0)])]
noncomputable def K_39 : List (List ℕ × List (ℕ × ℕ)) := [([6,2004318071,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,1),(132,1),(134,1),(133,1),(169,3),(172,3),(174,3),(173,3)]),([6,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(168,0),(176,0)]),([6,2155905152,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[(168,0)]),([6,2155905152,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[(168,0)]),([6,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,2),(128,0),(130,0),(129,1),(169,3),(173,0)]),([6,2290649224,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,2),(168,0)]),([6,2290649224,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[(168,0)]),([6,2290649224,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,2),(168,0)]),([6,2290649224,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[(168,0)]),([6,2290649224,2863311530,3233857728,4042322160,4278255360,4294901760],[(130,0),(189,0)]),([6,2290649224,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(128,2),(168,0)]),([6,2290649224,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(128,2),(168,0),(196,1),(244,3)]),([6,2290649224,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(128,1)]),([6,2290649224,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[(168,0)]),([6,2290649224,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760],[(96,2),(168,0),(152,2)]),([6,2290649224,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(96,2),(168,0),(204,1),(252,3)]),([6,2290649224,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(96,2),(168,0)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(96,2),(128,0),(260,3)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(98,2),(128,0),(130,0),(129,1),(133,1),(169,3),(173,3),(149,1),(189,3)])]
noncomputable def K_40 : List (List ℕ × List (ℕ × ℕ)) := [([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712],[(96,1),(98,1),(129,1),(133,1),(149,1),(189,3)]),([6,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[(98,2),(130,0),(148,1),(150,1),(149,1),(188,3),(190,3),(189,3)]),([6,2290649224,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,2290649224,4008636142,4042322160,4278255360,4294901760],[(74,2),(98,0),(110,1),(142,3),(10,2),(14,0)]),([6,2684395520,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2684395520,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[]),([6,2684395520,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(129,1),(169,3),(205,1)]),([6,2694881440,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2694881440,2852170240,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,1),(128,1),(168,1)]),([6,2694881440,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2694881440,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,2694881440,2863311530,3233857728,3435973836,4278255360,4294901760],[(189,0)]),([6,2694881440,2863311530,3422604288,3435973836,4042322160,4278255360,4294901760],[(56,1),(72,1),(128,1)]),([6,2694881440,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,2694881440,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760],[]),([6,2694881440,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(244,0)]),([6,2694881440,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[])]
noncomputable def K_41 : List (List ℕ × List (ℕ × ℕ)) := [([6,2694881440,2863311530,3435973836,4026593280,4278255360,4294901760],[(128,1),(129,1),(173,0)]),([6,2694881440,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[]),([6,2694881440,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(252,0)]),([6,2694881440,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[]),([6,2694881440,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(56,2),(96,2),(128,2),(172,1),(220,3),(244,0)]),([6,2694881440,2863311530,3435973836,4042322160,4278255360,4278255360,4294901760],[(56,1),(96,1),(128,1)]),([6,2694881440,2863311530,3435973836,4042322160,4278255360,4288741280,4294901760],[(56,1),(96,1),(168,1),(260,0)]),([6,2694881440,2863311530,3435973836,4042322160,4278255360,4289396650,4294901760],[(56,1),(96,1),(168,1),(260,0)]),([6,2694881440,2863311530,3435973836,4042322160,4278255360,4291624908,4294901760],[(56,1),(96,1),(128,0),(168,1)]),([6,2694881440,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(260,0)]),([6,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,2),(129,1),(169,3),(173,0),(197,0)]),([6,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[(56,2),(96,2),(128,0),(216,2)]),([6,2694881440,2863311530,3435973836,4210752250,4278255360,4294901760],[(196,0),(198,0),(197,0)]),([6,2694881440,3435973836,4042322160,4210752250,4278255360,4294901760],[(10,2)]),([6,2694881440,3435973836,4210752250,4278255360,4294901760],[(2,2),(10,2),(150,0),(14,0)]),([6,2829625512,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(96,2)]),([6,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,2),(96,2),(129,1),(133,1),(169,3),(173,3),(141,1),(181,3),(197,0)]),([6,2862656160,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[])]
noncomputable def K_42 : List (List ℕ × List (ℕ × ℕ)) := [([6,2862656160,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(129,1),(133,1),(169,3),(173,3),(157,1)]),([6,2863311530,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(196,1),(244,3)]),([6,2863311530,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(172,1)]),([6,2863311530,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(204,1),(252,3)]),([6,2863311530,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(96,2)]),([6,2863311530,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(260,3)]),([6,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,1),(133,1),(169,3),(173,3)]),([6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[(6,3),(137,1),(141,1),(181,3)]),([6,2863311530,3149642683,3435973836,4042322160,4278255360,4294901760],[(137,1),(141,1),(177,3),(181,3)]),([6,2863311530,3221274624,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,3221274624,3435973836,4026593280,4042322160,4278255360,4294901760],[]),([6,2863311530,3221274624,3435973836,4042322160,4278255360,4294901760],[(134,1),(6,3),(137,1),(177,3),(114,1)]),([6,2863311530,3233857728,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,3233857728,3422604288,3435973836,4042322160,4278255360,4294901760],[(104,1),(136,1),(176,1)])]
noncomputable def K_43 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3233857728,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,3233857728,3435973836,3941264106,4042322160,4278255360,4294901760],[(244,0)]),([6,2863311530,3233857728,3435973836,4008636142,4042322160,4278255360,4294901760],[(244,0)]),([6,2863311530,3233857728,3435973836,4026593280,4042322160,4278255360,4294901760],[]),([6,2863311530,3233857728,3435973836,4042322160,4042322160,4278255360,4294901760],[]),([6,2863311530,3233857728,3435973836,4042322160,4210752250,4278255360,4294901760],[(252,0)]),([6,2863311530,3233857728,3435973836,4042322160,4244438268,4278255360,4294901760],[]),([6,2863311530,3233857728,3435973836,4042322160,4278190080,4278255360,4294901760],[(80,2),(104,2),(136,2),(176,4),(224,2)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4278255360,4294901760],[(80,1),(104,1),(136,1)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4289396650,4294901760],[(80,1),(104,1),(136,0),(176,1),(260,0)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4290838464,4294901760],[(80,1),(104,1),(176,1)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4291624908,4294901760],[(80,1),(104,1),(176,1)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4293984240,4294901760],[(260,0)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[(6,2),(137,1),(177,3),(181,0)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760,4294967040],[(80,2),(104,2),(224,2)]),([6,2863311530,3233857728,3435973836,4244438268,4278255360,4294901760],[(141,1),(181,3),(185,0)]),([6,2863311530,3233857728,4042322160,4244438268,4278255360,4294901760],[(10,2)]),([6,2863311530,3233857728,4244438268,4278255360,4294901760],[(6,2),(10,2),(14,0)]),([6,2863311530,3368601800,3435973836,4042322160,4210752250,4278255360,4294901760],[(104,2),(252,0)])]
noncomputable def K_44 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3368601800,3435973836,4042322160,4278255360,4294901760],[(6,2),(104,2),(137,1),(141,1),(177,3),(181,3),(149,1),(185,0),(189,3)]),([6,2863311530,3368601800,4042322160,4210752250,4278255360,4294901760],[(14,2),(193,0),(196,0),(198,0),(197,0)]),([6,2863311530,3368601800,4042322160,4278255360,4294901760],[(103,1),(131,0),(135,3),(6,2),(7,2),(111,1),(139,0),(143,3),(10,2),(11,2),(147,0),(151,0),(14,0),(15,0),(17,0)]),([6,2863311530,3435187392,3435973836,4042322160,4278255360,4293984240,4294901760],[]),([6,2863311530,3435187392,3435973836,4042322160,4278255360,4294901760],[(6,3),(137,1),(141,1),(177,3),(181,3)]),([6,2863311530,3435973836,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,3435973836,4008636142,4042322160,4278255360,4294901760],[(196,1),(244,3)]),([6,2863311530,3435973836,3435973836,4026593280,4042322160,4278255360,4294901760],[(136,1)]),([6,2863311530,3435973836,3435973836,4042322160,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,3435973836,4042322160,4210752250,4278255360,4294901760],[(104,2),(204,1),(252,3)]),([6,2863311530,3435973836,3435973836,4042322160,4244438268,4278255360,4294901760],[]),([6,2863311530,3435973836,3435973836,4042322160,4278255360,4293984240,4294901760],[(260,3)]),([6,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(137,1),(141,1),(177,3),(181,3)]),([6,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760],[(10,3),(145,1),(149,1),(189,3)]),([6,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760],[(141,1),(181,3),(145,1),(149,1),(185,3),(189,3)]),([6,2863311530,3435973836,3772834016,4008636142,4042322160,4278255360,4294901760],[(244,0)])]
noncomputable def K_45 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3435973836,3772834016,4008636142,4278255360,4294901760],[(157,1),(193,0),(196,0),(198,0),(197,3)]),([6,2863311530,3435973836,3772834016,4042322160,4278255360,4294901760],[(10,2),(145,1),(185,3),(189,0),(14,2),(193,0),(197,0)]),([6,2863311530,3435973836,3772834016,4278255360,4294901760],[(103,1),(131,0),(135,3),(111,1),(139,0),(143,3),(10,2),(11,2),(147,0),(151,0),(14,0),(15,0),(17,0)]),([6,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[(10,2),(145,1),(148,1),(150,1),(149,1),(185,3),(188,3),(190,3),(189,3)]),([6,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760],[(177,0),(10,2),(145,1),(149,1),(185,3),(189,3),(197,0)]),([6,2863311530,3435973836,4008636142,4008636142,4042322160,4278255360,4294901760],[(188,1),(236,3)]),([6,2863311530,3435973836,4008636142,4026593280,4042322160,4278255360,4294901760],[(188,1),(236,3)]),([6,2863311530,3435973836,4008636142,4042322160,4042322160,4278255360,4294901760],[(188,1),(236,3)]),([6,2863311530,3435973836,4008636142,4042322160,4210752250,4278255360,4294901760],[(188,1),(236,3),(204,1),(252,3)]),([6,2863311530,3435973836,4008636142,4042322160,4244438268,4278255360,4294901760],[(188,1),(236,3)]),([6,2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760],[(188,1),(236,3),(204,1),(252,3)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760],[(148,1),(236,3),(260,3)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(145,1),(148,1),(150,1),(149,1),(185,3),(188,3),(190,3),(189,3)]),([6,2863311530,3435973836,4026531840,4026593280,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,4026531840,4042322160,4278255360,4294901760],[(134,1),(174,3),(106,2),(138,0),(145,1),(185,3)]),([6,2863311530,3435973836,4026593280,4026593280,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,4026593280,4042260480,4042322160,4278255360,4294901760],[(144,0),(184,0),(232,0),(200,0)])]
noncomputable def K_46 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3435973836,4026593280,4042260480,4278255360,4294901760],[(102,0),(134,1),(174,3),(82,3),(106,1),(138,0),(113,0),(184,3),(185,3),(152,1),(154,0),(153,1),(206,1),(205,3)]),([6,2863311530,3435973836,4026593280,4042322160,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,4026593280,4042322160,4205509290,4278255360,4294901760],[(204,1)]),([6,2863311530,3435973836,4026593280,4042322160,4210752250,4278255360,4294901760],[(204,1)]),([6,2863311530,3435973836,4026593280,4042322160,4241292492,4278255360,4294901760],[(152,1)]),([6,2863311530,3435973836,4026593280,4042322160,4244438268,4278255360,4294901760],[(116,1),(152,1)]),([6,2863311530,3435973836,4026593280,4042322160,4278255360,4293984240,4294901760],[(116,1),(192,1)]),([6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(134,1),(106,1),(10,3),(145,1),(185,3),(153,1),(205,1)]),([6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760,4294901760],[(112,3),(144,3),(184,3),(204,1)]),([6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760,4294945450],[(228,3),(112,3),(144,3),(232,3),(252,1)]),([6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760,4294954188],[(112,3),(144,3),(232,3),(204,1),(252,1)]),([6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760,4294963200],[(112,3),(144,3),(232,3),(204,1),(252,1)]),([6,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760,4294963440],[(112,0),(144,0),(232,0),(252,1)]),([6,2863311530,3435973836,4026593280,4042322160,4291624908,4294901760],[(134,1),(189,0),(153,1),(197,0)]),([6,2863311530,3435973836,4026593280,4042322160,4293984240,4294901760],[(14,2),(197,0)]),([6,2863311530,3435973836,4026593280,4293984240,4294901760],[(135,3),(143,3),(10,3),(11,3),(14,3),(15,3)]),([6,2863311530,3435973836,4037079200,4042322160,4278255360,4289396650,4294901760],[(180,1),(112,1),(184,1)]),([6,2863311530,3435973836,4037079200,4042322160,4278255360,4294901760],[(134,1),(10,4),(145,1),(185,3),(189,0),(14,2),(197,0)])]
noncomputable def K_47 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3435973836,4037079200,4278255360,4289396650,4294901760],[(100,1),(102,1),(140,1),(142,1),(141,1),(18,0),(205,4)]),([6,2863311530,3435973836,4037079200,4278255360,4294901760],[(102,1),(103,1),(135,3),(111,1),(143,3),(10,4),(11,4),(151,0),(14,0),(15,0),(159,2)]),([6,2863311530,3435973836,4039176384,4042322160,4278255360,4291624908,4294901760],[(112,1),(184,1)]),([6,2863311530,3435973836,4039176384,4042322160,4278255360,4294901760],[(10,4),(145,1),(185,3),(189,0),(197,0),(205,4)]),([6,2863311530,3435973836,4042321920,4042322160,4278255360,4294901760],[(10,2),(145,1),(185,3),(189,0),(14,2),(193,0),(197,0),(204,2),(206,2),(205,4)]),([6,2863311530,3435973836,4042321920,4042322160,4278255360,4294901760,4294967040],[(112,2),(232,2),(204,2)]),([6,2863311530,3435973836,4042321920,4278255360,4294901760],[(103,1),(131,0),(135,3),(111,1),(139,0),(143,3),(10,2),(11,2),(147,0),(151,0),(14,0),(15,0),(156,2),(158,2),(157,4),(159,2),(17,0)]),([6,2863311530,3435973836,4042321920,4278255360,4294901760,4294967040],[(174,2),(182,2),(156,2),(158,2),(157,4),(206,0)]),([6,2863311530,3435973836,4042322160,4042322160,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,4042322160,4042322160,4210752250,4278255360,4294901760],[(204,1),(252,3)]),([6,2863311530,3435973836,4042322160,4042322160,4244438268,4278255360,4294901760],[]),([6,2863311530,3435973836,4042322160,4042322160,4278255360,4278255360,4294901760],[(88,1),(92,1)]),([6,2863311530,3435973836,4042322160,4042322160,4278255360,4289396650,4294901760],[(180,1),(88,1),(92,1),(260,4)]),([6,2863311530,3435973836,4042322160,4042322160,4278255360,4291624908,4294901760],[(88,1),(92,1)]),([6,2863311530,3435973836,4042322160,4042322160,4278255360,4293984240,4294901760],[(260,3)]),([6,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[(10,2),(185,0),(189,0)]),([6,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760,4294967040],[(88,2),(92,2),(204,2)])]
noncomputable def K_48 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3435973836,4042322160,4042326015,4278255360,4294901760],[(82,2),(149,1),(185,2),(14,4),(157,1),(197,0)]),([6,2863311530,3435973836,4042322160,4092851187,4278255360,4294901760],[(82,2),(14,2),(156,1),(158,1),(157,1),(193,0),(196,3),(198,3),(197,3)]),([6,2863311530,3435973836,4042322160,4126537205,4278255360,4294901760],[(74,2),(149,1),(189,3),(14,2),(157,1),(193,0),(197,3)]),([6,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760],[(74,2),(82,2),(10,2),(112,2),(113,2),(145,2),(149,1),(185,4),(189,3),(14,2),(157,1),(193,0),(197,3)]),([6,2863311530,3435973836,4042322160,4205509290,4278255360,4294901760],[(132,1),(134,1),(82,1),(14,3),(153,1),(156,1),(158,1),(157,1),(193,3),(196,3),(198,3),(197,3)]),([6,2863311530,3435973836,4042322160,4210096880,4278255360,4294901760],[(82,2),(149,1),(185,2),(14,4),(156,1),(158,1),(157,1),(193,0),(196,3),(198,3),(197,3)]),([6,2863311530,3435973836,4042322160,4210752250,4210752250,4278255360,4294901760],[(196,1),(244,3)]),([6,2863311530,3435973836,4042322160,4210752250,4244438268,4278255360,4294901760],[(112,2),(144,2),(196,1),(244,3)]),([6,2863311530,3435973836,4042322160,4210752250,4278124286,4278255360,4294901760],[(196,1),(244,3),(204,1),(252,3)]),([6,2863311530,3435973836,4042322160,4210752250,4278255360,4289396650,4294901760],[(100,1),(180,1),(116,1),(156,1),(244,3),(260,4)]),([6,2863311530,3435973836,4042322160,4210752250,4278255360,4291624908,4294901760],[(100,1),(116,1),(156,1),(244,3)]),([6,2863311530,3435973836,4042322160,4210752250,4278255360,4293984240,4294901760],[(156,1),(244,3),(260,3)]),([6,2863311530,3435973836,4042322160,4210752250,4278255360,4294639610,4294901760],[(156,1),(244,3),(260,3)]),([6,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(82,2),(14,2),(156,1),(158,1),(157,1),(193,0),(196,3),(198,3),(197,3)]),([6,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760,4294967040],[(100,2),(116,2),(156,1),(196,3),(204,2)])]
noncomputable def K_49 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760],[(141,1),(181,3),(189,3),(14,3),(153,1),(157,1),(193,3),(197,3),(205,4)]),([6,2863311530,3435973836,4042322160,4243651824,4278255360,4294901760],[(74,2),(149,1),(189,3),(14,4),(157,1),(193,0),(197,3)]),([6,2863311530,3435973836,4042322160,4244438268,4244438268,4278255360,4294901760],[]),([6,2863311530,3435973836,4042322160,4244438268,4278124286,4278255360,4294901760],[(204,1),(252,3)]),([6,2863311530,3435973836,4042322160,4244438268,4278255360,4291624908,4294901760],[(108,1),(140,1),(116,1),(156,1)]),([6,2863311530,3435973836,4042322160,4244438268,4278255360,4293984240,4294901760],[(156,1),(260,3)]),([6,2863311530,3435973836,4042322160,4244438268,4278255360,4294770684,4294901760],[(156,1),(260,3)]),([6,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(74,2),(149,1),(189,3),(14,2),(157,1),(193,0),(197,3)]),([6,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760,4294967040],[(108,2),(116,2),(204,2)]),([6,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(14,2),(156,1),(158,1),(157,1),(193,0),(196,3),(198,3),(197,3)]),([6,2863311530,3435973836,4042322160,4278255360,4293980400,4294901760],[(74,2),(117,1),(188,0),(190,0),(189,3),(156,1),(158,1),(157,1),(18,2),(201,0),(204,3),(206,3),(205,3)]),([6,2863311530,3435973836,4042322160,4278255360,4293984240,4293984240,4294901760],[(252,3)]),([6,2863311530,3435973836,4042322160,4278255360,4293984240,4294639610,4294901760],[(252,3),(260,3)]),([6,2863311530,3435973836,4042322160,4278255360,4293984240,4294770684,4294901760],[(252,3),(260,3)]),([6,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(117,1),(158,1),(18,3),(204,3),(206,3),(205,3)]),([6,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760,4294963440],[(148,0),(188,0),(156,0),(244,1),(204,3)]),([6,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760,4294967280],[(204,3)])]
noncomputable def K_50 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3435973836,4042322160,4278255360,4294639610,4294901760],[(158,1),(18,3),(204,3),(206,3),(205,3)]),([6,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760],[(117,1),(158,1),(18,3),(204,3),(206,3),(205,3)]),([6,2863311530,3435973836,4042322160,4278255360,4294901760],[(99,1),(103,1),(131,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(17,3)]),([6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967280],[(198,1),(206,3)]),([6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(198,1),(206,3)]),([6,2863311530,3435973836,4042322160,4278255360,4294936712],[(99,1),(103,1),(135,3),(107,1),(111,1),(141,3),(143,3),(10,2),(11,2),(151,0),(13,1),(14,0),(15,0),(155,1),(159,2)]),([6,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188],[(172,3),(174,3),(140,3),(142,3),(141,3),(148,0),(150,0),(149,0),(156,2),(158,2),(157,2)]),([7,65535,2863311530,3435973836,4042322160,4278255360],[(131,1),(135,1),(139,1),(143,1),(147,1),(151,1),(14,1),(15,1),(17,1)]),([7,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,3),(129,1),(131,1),(133,1),(135,1),(139,1),(143,1),(147,1),(151,1),(14,2),(15,1),(17,1),(18,0),(202,1),(203,1),(206,1),(207,1)]),([7,858993459,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,1),(131,1),(133,1),(135,1),(169,3),(171,3),(173,3),(175,3),(139,1),(143,1),(179,3),(183,3),(145,1),(147,1),(149,1),(151,1),(185,3),(187,3),(189,3),(191,3),(14,2),(15,2),(195,0),(199,0),(17,1),(18,0),(19,0),(203,2),(207,2),(21,3)]),([7,858993459,2863311530,4042322160,4278255360,4294901760],[(99,1),(103,1),(131,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(17,3)])]
noncomputable def K_51 : List (List ℕ × List (ℕ × ℕ)) := [([7,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,1),(131,1),(133,1),(135,1),(169,3),(171,3),(173,3),(175,3),(137,1),(139,1),(141,1),(143,1),(177,3),(179,3),(181,3),(183,3),(147,1),(151,1),(187,3),(191,3),(14,2),(15,2),(195,0),(199,0),(17,1),(18,0),(19,0),(203,2),(207,2),(21,3)]),([7,1431655765,3435973836,4042322160,4278255360,4294901760],[(99,1),(103,1),(131,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(17,3)]),([7,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(98,2),(128,0),(130,0),(129,1),(131,1),(133,1),(135,1),(169,3),(171,3),(173,3),(175,3),(139,1),(143,1),(179,3),(183,3),(147,1),(149,1),(151,1),(187,3),(189,3),(191,3),(14,2),(15,2),(195,0),(199,0),(17,1),(18,0),(19,0),(203,2),(207,2),(21,3)]),([7,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,2),(3,2),(129,1),(169,3),(171,0),(173,0),(175,0),(179,0),(183,0),(187,0),(191,0),(14,2),(15,2),(195,0),(197,0),(199,0),(18,0),(19,0),(21,0)]),([7,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(129,1),(131,1),(133,1),(135,1),(169,3),(171,3),(173,3),(175,3),(147,1),(151,1),(187,3),(191,3),(14,2),(15,2),(195,0),(199,0),(17,1),(18,0),(19,0),(203,2),(207,2),(21,3)]),([7,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[(135,1),(171,0),(175,3),(6,2),(7,2),(137,1),(177,3),(179,0),(181,0),(183,0),(187,0),(191,0),(14,2),(15,2),(195,0),(199,0),(18,0),(19,0),(21,0)]),([7,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(131,1),(135,1),(171,3),(175,3),(137,1),(139,1),(141,1),(143,1),(177,3),(179,3),(181,3),(183,3),(14,2),(15,2),(195,0),(199,0),(17,1),(18,0),(19,0),(203,2),(207,2),(21,3)]),([7,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(131,1),(135,1),(171,3),(175,3),(139,1),(143,1),(179,3),(183,3),(145,1),(147,1),(148,1),(150,1),(149,1),(151,1),(185,3),(187,3),(188,3),(190,3),(189,3),(191,3),(14,2),(15,2),(195,0),(199,0),(17,1),(18,0),(19,0),(203,2),(207,2),(21,3)])]
noncomputable def K_52 : List (List ℕ × List (ℕ × ℕ)) := [([7,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(131,1),(134,1),(135,1),(175,3),(106,1),(139,1),(143,1),(183,3),(10,3),(11,3),(145,1),(147,1),(185,3),(14,2),(15,2),(153,1),(17,1),(18,0),(19,0),(203,1),(205,1),(207,1)]),([7,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[(135,1),(171,0),(175,3),(143,1),(179,0),(183,3),(10,2),(11,2),(185,0),(187,0),(189,0),(191,0),(18,0),(19,0),(207,2),(21,0)]),([7,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(135,1),(171,0),(175,3),(82,2),(143,1),(179,0),(183,3),(10,2),(11,2),(187,0),(191,0),(14,2),(15,2),(156,1),(158,1),(157,1),(159,1),(193,0),(195,0),(196,3),(198,3),(197,3),(199,3),(17,1),(18,0),(19,0),(207,2),(21,3)]),([7,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(74,2),(131,1),(135,1),(171,3),(175,3),(143,1),(179,0),(183,3),(10,2),(11,2),(149,1),(187,0),(189,3),(191,0),(14,2),(15,2),(157,1),(159,1),(193,0),(195,0),(197,3),(199,3),(17,1),(18,0),(19,0),(207,2),(21,3)]),([7,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(99,1),(103,1),(171,3),(175,3),(107,1),(111,1),(179,3),(183,3),(10,2),(11,2),(117,1),(191,0),(13,1),(14,0),(15,0),(158,1),(159,1),(195,1),(199,2),(18,3),(19,3),(204,3),(206,3),(205,3),(207,3),(21,3)]),([7,2863311530,3435973836,4042322160,4278255360,4294901760],[(99,1),(103,1),(131,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(17,3)]),([8,2863311530,3435973836,4042322160,4278255360,4294901760],[(99,1),(103,1),(131,3),(135,3),(107,1),(111,1),(139,3),(143,3),(10,2),(11,2),(147,0),(151,0),(13,1),(14,0),(15,0),(155,2),(159,2),(17,3)])]
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_20 : K_20.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_21 : K_21.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_22 : K_22.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_23 : K_23.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_24 : K_24.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_25 : K_25.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_26 : K_26.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_27 : K_27.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_28 : K_28.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_29 : K_29.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_30 : K_30.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_31 : K_31.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_32 : K_32.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_33 : K_33.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_34 : K_34.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_35 : K_35.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_36 : K_36.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_37 : K_37.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_38 : K_38.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_39 : K_39.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_40 : K_40.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_41 : K_41.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_42 : K_42.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_43 : K_43.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_44 : K_44.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_45 : K_45.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_46 : K_46.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_47 : K_47.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_48 : K_48.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_49 : K_49.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_50 : K_50.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_51 : K_51.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_52 : K_52.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem hK_cert : T_cert.toList = (((((K_0 ++ (K_1 ++ K_2)) ++ (K_3 ++ (K_4 ++ K_5))) ++ ((K_6 ++ (K_7 ++ K_8)) ++ ((K_9 ++ K_10) ++ (K_11 ++ K_12)))) ++ (((K_13 ++ (K_14 ++ K_15)) ++ (K_16 ++ (K_17 ++ K_18))) ++ ((K_19 ++ (K_20 ++ K_21)) ++ ((K_22 ++ K_23) ++ (K_24 ++ K_25))))) ++ ((((K_26 ++ (K_27 ++ K_28)) ++ (K_29 ++ (K_30 ++ K_31))) ++ ((K_32 ++ (K_33 ++ K_34)) ++ ((K_35 ++ K_36) ++ (K_37 ++ K_38)))) ++ (((K_39 ++ (K_40 ++ K_41)) ++ ((K_42 ++ K_43) ++ (K_44 ++ K_45))) ++ ((K_46 ++ (K_47 ++ K_48)) ++ ((K_49 ++ K_50) ++ (K_51 ++ K_52)))))).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert ((all_app (all_app (all_app (all_app (all_app c_0 (all_app c_1 c_2)) (all_app c_3 (all_app c_4 c_5))) (all_app (all_app c_6 (all_app c_7 c_8)) (all_app (all_app c_9 c_10) (all_app c_11 c_12)))) (all_app (all_app (all_app c_13 (all_app c_14 c_15)) (all_app c_16 (all_app c_17 c_18))) (all_app (all_app c_19 (all_app c_20 c_21)) (all_app (all_app c_22 c_23) (all_app c_24 c_25))))) (all_app (all_app (all_app (all_app c_26 (all_app c_27 c_28)) (all_app c_29 (all_app c_30 c_31))) (all_app (all_app c_32 (all_app c_33 c_34)) (all_app (all_app c_35 c_36) (all_app c_37 c_38)))) (all_app (all_app (all_app c_39 (all_app c_40 c_41)) (all_app (all_app c_42 c_43) (all_app c_44 c_45))) (all_app (all_app c_46 (all_app c_47 c_48)) (all_app (all_app c_49 c_50) (all_app c_51 c_52)))))))

theorem lb : ∀ s : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeaa8a888 (idx5 x)) s → 9 ≤ s :=
  lb_cert _ L_ M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel)

end LowZero

namespace LowOne

def L_ : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def M_ : ℕ := 4294967295
def Y_ : ℕ := 4276808360
def XS_ : List ℕ := [2863311530,3435973836,4042322160,4278255360,4294901760]
def PD_ : List (ℕ × ℕ) := [(1,18158932),(2,17829890),(4,17040386),(8,1310786),(16,5186)]
def PM_ : List (ℕ × ℕ) := [(1,4276808360),(6,4276808360),(10,4276808360),(12,4276808360),(18,4276808360),(20,4276808360),(24,4276808360)]

def G_ : List (List ℕ) := [[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31],[0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31],[0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31],[0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31],[0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31],[0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31],[0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31],[0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15,16,17,20,21,24,25,28,29,18,19,22,23,26,27,30,31],[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31],[0,1,4,5,16,17,20,21,2,3,6,7,18,19,22,23,8,9,12,13,24,25,28,29,10,11,14,15,26,27,30,31],[0,1,4,5,16,17,20,21,8,9,12,13,24,25,28,29,2,3,6,7,18,19,22,23,10,11,14,15,26,27,30,31],[0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15,16,17,24,25,18,19,26,27,20,21,28,29,22,23,30,31],[0,1,8,9,2,3,10,11,16,17,24,25,18,19,26,27,4,5,12,13,6,7,14,15,20,21,28,29,22,23,30,31],[0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15,16,17,24,25,20,21,28,29,18,19,26,27,22,23,30,31],[0,1,8,9,4,5,12,13,16,17,24,25,20,21,28,29,2,3,10,11,6,7,14,15,18,19,26,27,22,23,30,31],[0,1,8,9,16,17,24,25,2,3,10,11,18,19,26,27,4,5,12,13,20,21,28,29,6,7,14,15,22,23,30,31],[0,1,8,9,16,17,24,25,4,5,12,13,20,21,28,29,2,3,10,11,18,19,26,27,6,7,14,15,22,23,30,31],[0,1,16,17,2,3,18,19,4,5,20,21,6,7,22,23,8,9,24,25,10,11,26,27,12,13,28,29,14,15,30,31],[0,1,16,17,2,3,18,19,8,9,24,25,10,11,26,27,4,5,20,21,6,7,22,23,12,13,28,29,14,15,30,31],[0,1,16,17,4,5,20,21,2,3,18,19,6,7,22,23,8,9,24,25,12,13,28,29,10,11,26,27,14,15,30,31],[0,1,16,17,4,5,20,21,8,9,24,25,12,13,28,29,2,3,18,19,6,7,22,23,10,11,26,27,14,15,30,31],[0,1,16,17,8,9,24,25,2,3,18,19,10,11,26,27,4,5,20,21,12,13,28,29,6,7,22,23,14,15,30,31],[0,1,16,17,8,9,24,25,4,5,20,21,12,13,28,29,2,3,18,19,10,11,26,27,6,7,22,23,14,15,30,31]]

/-- the closed set of failing search states (509 states, up to 23 symmetries) -/
noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,2863311530,4241280204,4293980400,4294967040] BT.lf) [3,2863311530,4241289216,4293984240,4294954188] (BT.nd BT.lf [3,3435973836,4007718624,4205509290,4294901760] BT.lf)) [3,3435973836,4042322160,4272597674,4294967040] (BT.nd (BT.nd BT.lf [3,3435973836,4205488810,4293980400,4294967040] BT.lf) [3,3435973836,4205509290,4293984240,4294945440] (BT.nd BT.lf [3,3435973836,4210752240,4289396650,4294945450] BT.lf))) [4,16776960,2863311530,3435973836,4042322160] (BT.nd (BT.nd (BT.nd BT.lf [4,16776960,2863311530,3435973836,4042322160,4278190080] BT.lf) [4,178956970,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [4,214748364,2863311530,4042322160,4278255360,4294901760] BT.lf)) [4,1077952576,2863311530,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,1145324612,2863311530,4042322160,4278255360,4294936712] BT.lf) [4,1145324748,2863311530,4042322160,4278255360,4294901760] (BT.nd BT.lf [4,1145359564,1347481840,2863311530,4278255360,4294901760] BT.lf)))) [4,1145359564,2863311530,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,1145359564,2863311530,4042322160,4289396480,4294901760] BT.lf) [4,1154272460,2863311530,4042322160,4278255360,4294901760] (BT.nd BT.lf [4,1431677610,3435973836,4042322160,4278255360] BT.lf)) [4,2576980377,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2829625512,3941264106,4244438268,4278255360,4294901760] BT.lf) [4,2829625512,4008636142,4210752250,4278255360,4294901760] (BT.nd BT.lf [4,2863311528,3435973836,4042322160,4278255360,4294901760] BT.lf))) [4,2863311530,3221274624,4241292492,4293984240,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3233857536,4244438268,4278255360,4294901760] BT.lf) [4,2863311530,3233857728,4227922944,4294770684,4294901760] (BT.nd BT.lf [4,2863311530,3233857728,4238933160,4278255360,4294901760] BT.lf)) [4,2863311530,3233857728,4243389676,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3233857728,4244438268,4261477888,4294901760] BT.lf) [4,2863311530,3233857728,4244438268,4278190080,4294967040] (BT.nd BT.lf [4,2863311530,3233857728,4244438268,4278255360,4294901760] BT.lf))))) [4,2863311530,3233857728,4244438268,4278255360,4294934656] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3233857728,4244438268,4278255360,4294936712] BT.lf) [4,2863311530,3233857728,4244438268,4278255360,4294944936] (BT.nd BT.lf [4,2863311530,3233857728,4244438268,4278255360,4294945280] BT.lf)) [4,2863311530,3233857728,4244438268,4278255360,4294950912] (BT.nd (BT.nd BT.lf [4,2863311530,3233857728,4277993212,4278255360,4294901760] BT.lf) [4,2863311530,3284386755,4244438268,4278255360,4294901760] (BT.nd BT.lf [4,2863311530,3284386755,4278255360,4294901760] BT.lf))) [4,2863311530,3301231820,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3368077504,4244438268,4278255360,4294901760] BT.lf) [4,2863311530,3368077504,4277993212,4278255360,4294901760] (BT.nd BT.lf [4,2863311530,3368601800,4042322160,4261477888,4294901760] BT.lf)) [4,2863311530,3368601800,4243651824,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3368601800,4244438268,4278255360,4294901760] BT.lf) [4,2863311530,3435184320,4244438268,4278255360,4294901760] (BT.nd BT.lf [4,2863311530,3435187392,4042322160,4278255360,4294936712] BT.lf)))) [4,2863311530,3435187392,4042322160,4287168392,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435187404,4042322160,4278255360,4294901760] BT.lf) [4,2863311530,3435710664,4042322160,4278255360,4294901760] (BT.nd BT.lf [4,2863311530,3435711688,4042322160,4278255360,4294574080] BT.lf)) [4,2863311530,3435711688,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,2863311530,3435711688,4042322160,4287168392,4294901760] BT.lf) [4,2863311530,3435973832,4042322160,4278255360,4294901760] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [4,2863311530,3435973836,4042322160,4278255360,4294901765] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294901772] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294901896] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294934528] BT.lf)) [4,2863311530,3435973836,4042322160,4278255360,4294934656] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294936704] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294944904] BT.lf)))))) [4,2863311530,3435973836,4042322160,4278255360,4294944936] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294945448] BT.lf) [4,2863311530,3435973836,4042322160,4278255360,4294950912] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4278255360,4294951040] BT.lf)) [4,2863311530,3435973836,4042322160,4278255360,4294953096] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4286644096,4294934656] BT.lf) [4,2863311530,3435973836,4042322160,4286644096,4294936712] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4287137928,4294967040] BT.lf))) [4,2863311530,3435973836,4042322160,4287168256,4294936712] (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4287168392,4294936712] BT.lf) [4,2863311530,3435973836,4042322160,4287168392,4294942880] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4287168392,4294945280] BT.lf)) [4,2863311530,3435973836,4042322160,4287168392,4294945416] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4289265576,4294944936] BT.lf) [4,2863311530,3435973836,4042322160,4289374720,4294967040] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4289374890,4294967040] BT.lf)))) [4,2863311530,3435973836,4042322160,4289396480,4294945280] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4289396480,4294945450] BT.lf) [4,2863311530,3435973836,4042322160,4289396616,4294945450] (BT.nd BT.lf [4,2863311530,3435973836,4042322160,4290822336,4294967040] BT.lf)) [4,2863311530,3435973836,4042322160,4290838272,4294951104] (BT.nd (BT.nd BT.lf [4,2863311530,3435973836,4177066232,4287168392,4294936712] BT.lf) [4,2863311530,3435973836,4210096880,4289396650,4294945280] (BT.nd BT.lf [4,3233857728,3937069738,4244438268,4278255360,4294901760] BT.lf))) [4,3435973836,3937053354,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [4,3435973836,3937069738,4042322160,4278255360,4294901760] BT.lf) [4,3435973836,3937069738,4042322160,4278255360,4294950912] (BT.nd BT.lf [4,3435973836,3937069738,4042322160,4290838464,4294901760] BT.lf)) [4,3435973836,3941264042,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [4,3435973836,4008636142,4042322160,4289374890,4294967040] BT.lf) [4,3435973836,4210096880,4289396650,4294945280] (BT.nd BT.lf [5,0,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [5,15,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,85,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,170,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,204,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,255,2863311530,3435973836,4042322160,4278190080] (BT.nd (BT.nd BT.lf [5,255,2863311530,3435973836,4042322160,4278190080,4294967040] BT.lf) [5,255,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,4095,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,17476,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,21845,2863267840,3435973836,4042322160,4278255360] BT.lf) [5,21845,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,22015,2863311530,3435973836,4042322160,4278255360] BT.lf)) [5,22015,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,22015,2863311530,3435973836,4042322160,4278255360,4294945280] BT.lf) [5,34952,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,43690,2863267840,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [5,43690,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,43690,2863333375,3435973836,4042322160,4278255360] BT.lf) [5,43690,2863333375,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,49344,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,52428,2863311530,3435921408,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,52428,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,52428,2863311530,3435986943,4042322160,4278255360] (BT.nd BT.lf [5,52428,2863311530,3435986943,4042322160,4278255360,4294901760] BT.lf))) [5,52428,2863311530,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,61166,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,64764,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,65535,16711935,252645135,2863311530,3435973836] BT.lf)) [5,65535,16711935,1431655765,3435973836,4042322160] (BT.nd (BT.nd BT.lf [5,65535,16711935,2863311530,3435973836,4042322160] BT.lf) [5,65535,1431655765,3435973836,4042322160,4278255360] (BT.nd BT.lf [5,65535,2290649224,4008636142,4042322160,4278255360] BT.lf))))))) [5,65535,2863267840,3435973836,4042322160,4278255360,4294945450] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,65535,2863311530,3233857728,4244438268,4278255360] BT.lf) [5,65535,2863311530,3233857728,4244438268,4278255360,4294901760] (BT.nd BT.lf [5,65535,2863311530,3435921408,4042322160,4278255360,4294954188] BT.lf)) [5,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,65535,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4287168392] BT.lf))) [5,65535,2863311530,3435973836,4042322160,4287168392,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,65535,2863311530,3435973836,4042322160,4289396480] BT.lf) [5,65535,2863311530,3435973836,4042322160,4289396480,4294901760] (BT.nd BT.lf [5,1048575,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,5592405,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,5636095,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,11184810,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,13421772,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [5,16777215,2863311530,3435973836,4042322160,4278190080,4294967040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,16777215,2863311530,3435973836,4042322160,4294967040] (BT.nd BT.lf [5,268435455,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,1077952576,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,1145324612,2290649224,2863311530,4042322160,4278255360,4294901760] BT.lf) [5,1145324612,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,1145324612,2863311530,3722304989,4042322160,4278255360,4294901760] BT.lf))) [5,1145324612,2863311530,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,1145324612,3722304989,4042322160,4278255360,4294901760] BT.lf) [5,1145359564,1431699455,2863311530,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,1145359564,2863267840,2863311530,4042322160,4278255360,4294901760] BT.lf)) [5,1145359564,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,1145359564,2863311530,4042322160,4278255360,4294901760] BT.lf) [5,1414812756,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,1431655765,2863311530,3233857728,4244438268,4278255360,4294901760] BT.lf))))) [5,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1431655765,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf) [5,1431655765,3233857728,4244438268,4278255360,4294901760] (BT.nd BT.lf [5,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,1431655765,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd BT.lf [5,1431655935,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,1431699455,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,1431699455,2863311530,3435973836,4042322160,4289396480,4294901760] BT.lf))) [5,1431699455,3435973836,4042322160,4278255360,4294945450] (BT.nd (BT.nd (BT.nd BT.lf [5,1442840575,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2147516416,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2155905152,2863311530,3233857728,4244438268,4278255360,4294901760] BT.lf)) [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf) [5,2155905152,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd BT.lf [5,2155905152,2863311530,3435973836,4177066232,4278255360,4294901760] BT.lf)))) [5,2290124928,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3233857728,4244438268,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,3435187392,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4026593280,4293984240,4294901760] BT.lf)) [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656] BT.lf) [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd BT.lf [5,2290649224,2863311530,3435973836,4042322160,4278255360,4294942880] BT.lf))) [5,2290649224,2863311530,3435973836,4042322160,4287168392,4294936712] (BT.nd (BT.nd (BT.nd BT.lf [5,2290649224,2863311530,3974950124,4042322160,4278255360,4294901760] BT.lf) [5,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290649224,2863311530,4008636142,4042322160,4278255360,4294936712] BT.lf)) [5,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2290649224,4008636142,4042322160,4278255360,4294936712] BT.lf) [5,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2290666700,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))))) [5,2290679807,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2827528328,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2829625512,2863311530,3233857728,4244438268,4278255360,4294901760] BT.lf)) [5,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2829625512,2863311530,3435973836,4042322160,4278255360,4294944936] BT.lf) [5,2829625512,2863311530,3435973836,4177066232,4278255360,4294901760] (BT.nd BT.lf [5,2829625512,2863311530,3435973836,4210752250,4278255360,4294901760] BT.lf))) [5,2829625512,3435973836,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863180456,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863311530,3233857728,4244438268,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,2863311530,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd BT.lf [5,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [5,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3221225472,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3221274624,3233857728,4244438268,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3221274624,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3221274624,3435973836,4042322160,4278255360,4294950912] (BT.nd (BT.nd BT.lf [5,2863311530,3221274624,3435973836,4042322160,4290838464,4294901760] BT.lf) [5,2863311530,3229663360,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3233857536,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,2863311530,3233857728,3233857728,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3422604288,4042322160,4291624908,4294901760] BT.lf) [5,2863311530,3233857728,3431517320,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4042322160,4278190080,4294967040] BT.lf)) [5,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4042322160,4278255360,4294934656] BT.lf) [5,2863311530,3233857728,3435973836,4042322160,4278255360,4294936712] (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4042322160,4278255360,4294945280] BT.lf))))) [5,2863311530,3233857728,3435973836,4042322160,4278255360,4294950912] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4177066232,4278255360,4294901760] BT.lf) [5,2863311530,3233857728,3435973836,4210096880,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3233857728,3435973836,4243651824,4278255360,4294901760] BT.lf)) [5,2863311530,3233857728,3435973836,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,3941264106,4244438268,4278255360,4294901760] BT.lf) [5,2863311530,3233857728,4008636142,4244438268,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3233857728,4227922944,4244438268,4278255360,4294901760] BT.lf))) [5,2863311530,3233857728,4244438268,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,4244438268,4278124286,4278255360,4294901760] BT.lf) [5,2863311530,3233857728,4244438268,4278255360,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3233857728,4244438268,4278255360,4289396650,4294901760] BT.lf)) [5,2863311530,3233857728,4244438268,4278255360,4290838464,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3233857728,4244438268,4278255360,4291624908,4294901760] BT.lf) [5,2863311530,3233857728,4244438268,4278255360,4294770684,4294901760] (BT.nd BT.lf [5,2863311530,3233857728,4244438268,4278255360,4294901760] BT.lf)))) [5,2863311530,3233857728,4244438268,4278255360,4294901760,4294967040] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3233860812,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3233873919,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3301229764,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3364407432,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3368077504,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3368077504,3435973836,4210096880,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3368601800,3435973836,4042322160,4278255360,4294901760] BT.lf))) [5,2863311530,3368601800,3435973836,4177066232,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,3435973836,4244438268,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3368601800,4042322160,4244438268,4278255360,4294901760] BT.lf)) [5,2863311530,3368601800,4042322160,4278124286,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3368601800,4210752250,4244438268,4278255360,4294901760] BT.lf) [5,2863311530,3368601800,4244438268,4278255360,4294901760] BT.lf))))))) [5,2863311530,3435184320,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435187392,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435187392,4042322160,4244438268,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435187392,4042322160,4278255360,4294770684,4294901760] BT.lf)) [5,2863311530,3435187392,4042322160,4278255360,4294901760,4294954188] (BT.nd (BT.nd BT.lf [5,2863311530,3435711688,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435711688,4042322160,4210752250,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435711688,4042322160,4278255360,4293984240,4294901760] BT.lf))) [5,2863311530,3435711688,4042322160,4278255360,4294639610,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435711688,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973824,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,3435973836,4042322160,4278255360,4294936712] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3435973836,4042322160,4278255360,4294942880] BT.lf) [5,2863311530,3435973836,3435973887,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,3435978205,4042322160,4278255360,4294901760] BT.lf)))) [5,2863311530,3435973836,3435982574,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3435986172,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,3439329279,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,3587560917,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3705461980,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,3722313727,4042322160,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,3937069738,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3938511552,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,3941264106,4244438268,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,3972852940,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,3974950124,4042322160,4278255360,4294942880] (BT.nd BT.lf [5,2863311530,3435973836,3974950124,4210752250,4278255360,4294901760] BT.lf))))) [5,2863311530,3435973836,4007718624,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4008373994,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4008505068,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294936712] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4008636142,4042322160,4278255360,4294942880] BT.lf) [5,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4241280204,4278255360,4294901760] BT.lf))) [5,2863311530,3435973836,4042322160,4241289216,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4243389676,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4244438016,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4244438220,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4244438268,4278255360,4294936712] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4244438268,4278255360,4294944936] BT.lf)))) [5,2863311530,3435973836,4042322160,4244438268,4278255360,4294945280] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4244439039,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4261281277,4278255360,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4277075694,4278255360,4294901760] BT.lf)) [5,2863311530,3435973836,4042322160,4277993212,4278255360,4294901760] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294769916,4294901760] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760] BT.lf))) [5,2863311530,3435973836,4042322160,4278255360,4294901758,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967292] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf)) [5,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294923605,4294945450] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294934656] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf)))))) [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294936712] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294945450] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294954188] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440] BT.lf)) [5,2863311530,3435973836,4042322160,4278255360,4294936712,4294965496] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294944936] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294945450,4294951104] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188] BT.lf))) [5,2863311530,3435973836,4042322160,4278255360,4294945450,4294966524] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4278255360,4294950912] BT.lf) [5,2863311530,3435973836,4042322160,4278255360,4294951104,4294967040] (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4287168392,4294936712] BT.lf)) [5,2863311530,3435973836,4042322160,4289374890,4294967040] (BT.nd (BT.nd BT.lf [5,2863311530,3435973836,4042322160,4289396480,4294945450] BT.lf) [5,2863311530,3435973836,4042322160,4289396650,4294945450,4294967040] (BT.nd BT.lf [5,2863333375,3435973836,4042322160,4278255360,4294901760,4294945450] BT.lf)))) [5,3221274624,3435973836,3937069738,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,3233857728,3435973836,3937069738,4042322160,4278255360,4294901760] BT.lf) [5,3435973836,3937069738,4042322160,4278255360,4294901760] (BT.nd BT.lf [5,3435973836,3941264106,4042322160,4278255360,4289396650,4294901760] BT.lf)) [6,0,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd BT.lf [6,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,0,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,0,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,0,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,255,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040] (BT.nd BT.lf [6,21845,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,21845,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450] (BT.nd (BT.nd BT.lf [6,43690,65535,2863311530,3435973836,4042322160,4278255360] BT.lf) [6,43690,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,43690,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [6,52428,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,52428,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,52428,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,65535,65535,2863311530,3435973836,4042322160,4278255360] BT.lf)) [6,65535,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,65535,16711935,2863311530,3435973836,4042322160] BT.lf) [6,65535,16711935,2863311530,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,65535,16711935,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,65535,1431655765,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,1431655765,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,65535,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,65535,2290649224,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd BT.lf [6,65535,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863267840,2863311530,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [6,65535,2863311530,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,2863333375,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,65535,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,65535,2863311530,3233857728,3435973836,4042322160,4278255360] (BT.nd (BT.nd BT.lf [6,65535,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435921408,3435973836,4042322160,4278255360] (BT.nd BT.lf [6,65535,2863311530,3435921408,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,65535,2863311530,3435973836,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,3435986943,4042322160,4278255360] (BT.nd BT.lf [6,65535,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760] BT.lf)) [6,65535,2863311530,3435973836,4008636142,4042322160,4278255360] (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,4042322160,4244438268,4278255360] (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf))))))) [6,65535,2863311530,3435973836,4042322160,4278255360] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760] (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450] BT.lf)) [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294954188] (BT.nd (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [6,65535,2863311530,3435973836,4042322160,4278255360,4294945450] (BT.nd BT.lf [6,65535,2863311530,3435973836,4042322160,4278255360,4294954188] BT.lf))) [6,65535,2863311530,3435973836,4042322160,4278255360,4294967295] (BT.nd (BT.nd (BT.nd BT.lf [6,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760] BT.lf) [6,16777215,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,1145324612,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,1145324612,1431655765,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,1145324612,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,1431655765,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [6,1431655765,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1431655765,2290649224,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,1431655765,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,1431655765,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,1431655765,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,1431655765,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf))) [6,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] BT.lf) [6,1431655765,3233857728,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,1431655765,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,1431655765,3435973836,3722304989,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,1431655765,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,1431655765,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd BT.lf [6,1431655765,3435973836,4042322160,4278255360,4294901760] BT.lf))))) [6,1431655765,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1431699455,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,1431699455,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2155905152,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [6,2290649224,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf)) [6,2290649224,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf)))) [6,2290649224,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf) [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf)) [6,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2290649224,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2290649224,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2829625512,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf))) [6,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2863311530,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760] BT.lf)))))) [6,2863311530,3221274624,3233857728,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3221274624,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3233857728,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3233857728,3422604288,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2863311530,3233857728,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3233857728,3435973836,3941264106,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3233857728,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf))) [6,2863311530,3233857728,3435973836,4042322160,4278190080,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3233857728,3435973836,4042322160,4278255360,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3435973836,4042322160,4278255360,4289396650,4294901760] (BT.nd BT.lf [6,2863311530,3233857728,3435973836,4042322160,4278255360,4290838464,4294901760] BT.lf)) [6,2863311530,3233857728,3435973836,4042322160,4278255360,4291624908,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760,4294967040] (BT.nd BT.lf [6,2863311530,3233857728,3435973836,4244438268,4278255360,4294901760] BT.lf)))) [6,2863311530,3233857728,4244438268,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3368601800,3435973836,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,2863311530,3368601800,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435187392,3435973836,4042322160,4278255360,4293984240,4294901760] BT.lf)) [6,2863311530,3435187392,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3435973836,4008636142,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,3435973836,4042322160,4042322160,4278255360,4294901760] BT.lf))) [6,2863311530,3435973836,3435973836,4042322160,4210752250,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3435973836,4042322160,4278255360,4293984240,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760] BT.lf))))) [6,2863311530,3435973836,4008636142,4008636142,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4042322160,4210752250,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4008636142,4042322160,4244438268,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4244438268,4244438268,4278255360,4294901760] BT.lf))) [6,2863311530,3435973836,4042322160,4244438268,4278124286,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4244438268,4278255360,4291624908,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4244438268,4278255360,4294770684,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] BT.lf)) [6,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760,4294967040] (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760] (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf)))) [6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,3435973836,4042322160,4278255360,4294936712] BT.lf) [6,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188] (BT.nd BT.lf [7,65535,2863311530,3435973836,4042322160,4278255360] BT.lf)) [7,65535,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd BT.lf [7,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,1431655765,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))) [7,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760] (BT.nd (BT.nd (BT.nd BT.lf [7,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760] BT.lf) [7,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760] (BT.nd BT.lf [7,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760] BT.lf)) [7,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760] (BT.nd (BT.nd BT.lf [7,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf) [8,2863311530,3435973836,4042322160,4278255360,4294901760] BT.lf))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([3,2863311530,4241280204,4293980400,4294967040],[]),([3,2863311530,4241289216,4293984240,4294954188],[]),([3,3435973836,4007718624,4205509290,4294901760],[]),([3,3435973836,4042322160,4272597674,4294967040],[]),([3,3435973836,4205488810,4293980400,4294967040],[]),([3,3435973836,4205509290,4293984240,4294945440],[]),([3,3435973836,4210752240,4289396650,4294945450],[]),([4,16776960,2863311530,3435973836,4042322160],[]),([4,16776960,2863311530,3435973836,4042322160,4278190080],[]),([4,178956970,3435973836,4042322160,4278255360,4294901760],[]),([4,214748364,2863311530,4042322160,4278255360,4294901760],[]),([4,1077952576,2863311530,4244438268,4278255360,4294901760],[]),([4,1145324612,2863311530,4042322160,4278255360,4294936712],[]),([4,1145324748,2863311530,4042322160,4278255360,4294901760],[]),([4,1145359564,1347481840,2863311530,4278255360,4294901760],[]),([4,1145359564,2863311530,4042322160,4278255360,4294901760],[]),([4,1145359564,2863311530,4042322160,4289396480,4294901760],[]),([4,1154272460,2863311530,4042322160,4278255360,4294901760],[]),([4,1431677610,3435973836,4042322160,4278255360],[]),([4,2576980377,4042322160,4278255360,4294901760],[]),([4,2829625512,3941264106,4244438268,4278255360,4294901760],[(96,17),(128,11)]),([4,2829625512,4008636142,4210752250,4278255360,4294901760],[(96,21),(128,15)]),([4,2863311528,3435973836,4042322160,4278255360,4294901760],[]),([4,2863311530,3221274624,4241292492,4293984240,4294901760],[(56,17),(136,17)]),([4,2863311530,3233857536,4244438268,4278255360,4294901760],[(56,15)]),([4,2863311530,3233857728,4227922944,4294770684,4294901760],[]),([4,2863311530,3233857728,4238933160,4278255360,4294901760],[(56,11)]),([4,2863311530,3233857728,4243389676,4278255360,4294901760],[]),([4,2863311530,3233857728,4244438268,4261477888,4294901760],[]),([4,2863311530,3233857728,4244438268,4278190080,4294967040],[(104,2)]),([4,2863311530,3233857728,4244438268,4278255360,4294901760],[]),([4,2863311530,3233857728,4244438268,4278255360,4294934656],[]),([4,2863311530,3233857728,4244438268,4278255360,4294936712],[]),([4,2863311530,3233857728,4244438268,4278255360,4294944936],[(56,11)]),([4,2863311530,3233857728,4244438268,4278255360,4294945280],[]),([4,2863311530,3233857728,4244438268,4278255360,4294950912],[(104,21)]),([4,2863311530,3233857728,4277993212,4278255360,4294901760],[]),([4,2863311530,3284386755,4244438268,4278255360,4294901760],[]),([4,2863311530,3284386755,4278255360,4294901760],[]),([4,2863311530,3301231820,4042322160,4278255360,4294901760],[]),([4,2863311530,3368077504,4244438268,4278255360,4294901760],[]),([4,2863311530,3368077504,4277993212,4278255360,4294901760],[]),([4,2863311530,3368601800,4042322160,4261477888,4294901760],[]),([4,2863311530,3368601800,4243651824,4278255360,4294901760],[]),([4,2863311530,3368601800,4244438268,4278255360,4294901760],[]),([4,2863311530,3435184320,4244438268,4278255360,4294901760],[]),([4,2863311530,3435187392,4042322160,4278255360,4294936712],[]),([4,2863311530,3435187392,4042322160,4287168392,4294901760],[]),([4,2863311530,3435187404,4042322160,4278255360,4294901760],[]),([4,2863311530,3435710664,4042322160,4278255360,4294901760],[]),([4,2863311530,3435711688,4042322160,4278255360,4294574080],[]),([4,2863311530,3435711688,4042322160,4278255360,4294901760],[]),([4,2863311530,3435711688,4042322160,4287168392,4294901760],[]),([4,2863311530,3435973832,4042322160,4278255360,4294901760],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901765],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901772],[]),([4,2863311530,3435973836,4042322160,4278255360,4294901896],[]),([4,2863311530,3435973836,4042322160,4278255360,4294934528],[]),([4,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([4,2863311530,3435973836,4042322160,4278255360,4294936704],[]),([4,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([4,2863311530,3435973836,4042322160,4278255360,4294944904],[]),([4,2863311530,3435973836,4042322160,4278255360,4294944936],[]),([4,2863311530,3435973836,4042322160,4278255360,4294945448],[]),([4,2863311530,3435973836,4042322160,4278255360,4294950912],[]),([4,2863311530,3435973836,4042322160,4278255360,4294951040],[]),([4,2863311530,3435973836,4042322160,4278255360,4294953096],[]),([4,2863311530,3435973836,4042322160,4286644096,4294934656],[]),([4,2863311530,3435973836,4042322160,4286644096,4294936712],[]),([4,2863311530,3435973836,4042322160,4287137928,4294967040],[]),([4,2863311530,3435973836,4042322160,4287168256,4294936712],[])]
noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([4,2863311530,3435973836,4042322160,4287168392,4294936712],[]),([4,2863311530,3435973836,4042322160,4287168392,4294942880],[]),([4,2863311530,3435973836,4042322160,4287168392,4294945280],[]),([4,2863311530,3435973836,4042322160,4287168392,4294945416],[]),([4,2863311530,3435973836,4042322160,4289265576,4294944936],[]),([4,2863311530,3435973836,4042322160,4289374720,4294967040],[]),([4,2863311530,3435973836,4042322160,4289374890,4294967040],[]),([4,2863311530,3435973836,4042322160,4289396480,4294945280],[]),([4,2863311530,3435973836,4042322160,4289396480,4294945450],[]),([4,2863311530,3435973836,4042322160,4289396616,4294945450],[(56,7)]),([4,2863311530,3435973836,4042322160,4290822336,4294967040],[(80,2)]),([4,2863311530,3435973836,4042322160,4290838272,4294951104],[(80,15)]),([4,2863311530,3435973836,4177066232,4287168392,4294936712],[]),([4,2863311530,3435973836,4210096880,4289396650,4294945280],[]),([4,3233857728,3937069738,4244438268,4278255360,4294901760],[(96,21)]),([4,3435973836,3937053354,4042322160,4278255360,4294901760],[]),([4,3435973836,3937069738,4042322160,4278255360,4294901760],[]),([4,3435973836,3937069738,4042322160,4278255360,4294950912],[]),([4,3435973836,3937069738,4042322160,4290838464,4294901760],[(72,21)]),([4,3435973836,3941264042,4042322160,4278255360,4294901760],[(72,15)]),([4,3435973836,4008636142,4042322160,4289374890,4294967040],[(140,2)]),([4,3435973836,4210096880,4289396650,4294945280],[]),([5,0,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,15,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,85,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,8),(96,2)]),([5,170,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,204,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2)]),([5,255,2863311530,3435973836,4042322160,4278190080],[(2,15),(128,15)]),([5,255,2863311530,3435973836,4042322160,4278190080,4294967040],[(128,15)]),([5,255,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,4095,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,17476,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,21845,2863267840,3435973836,4042322160,4278255360],[(56,17)]),([5,21845,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,22015,2863311530,3435973836,4042322160,4278255360],[(2,11)]),([5,22015,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,22015,2863311530,3435973836,4042322160,4278255360,4294945280],[]),([5,34952,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,43690,2863267840,3435973836,4042322160,4278255360,4294901760],[]),([5,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,43690,2863333375,3435973836,4042322160,4278255360],[]),([5,43690,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([5,49344,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,52428,2863311530,3435921408,4042322160,4278255360,4294901760],[(168,3)]),([5,52428,2863311530,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([5,52428,2863311530,3435986943,4042322160,4278255360],[]),([5,52428,2863311530,3435986943,4042322160,4278255360,4294901760],[]),([5,52428,2863311530,4008636142,4042322160,4278255360,4294901760],[]),([5,61166,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,64764,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,65535,16711935,252645135,2863311530,3435973836],[]),([5,65535,16711935,1431655765,3435973836,4042322160],[]),([5,65535,16711935,2863311530,3435973836,4042322160],[]),([5,65535,1431655765,3435973836,4042322160,4278255360],[]),([5,65535,2290649224,4008636142,4042322160,4278255360],[]),([5,65535,2863267840,3435973836,4042322160,4278255360,4294945450],[]),([5,65535,2863311530,3233857728,4244438268,4278255360],[]),([5,65535,2863311530,3233857728,4244438268,4278255360,4294901760],[]),([5,65535,2863311530,3435921408,4042322160,4278255360,4294954188],[]),([5,65535,2863311530,3435973836,4042322160,4278255360],[]),([5,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,65535,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,65535,2863311530,3435973836,4042322160,4287168392],[(2,0)]),([5,65535,2863311530,3435973836,4042322160,4287168392,4294901760],[]),([5,65535,2863311530,3435973836,4042322160,4289396480],[(2,17)]),([5,65535,2863311530,3435973836,4042322160,4289396480,4294901760],[]),([5,1048575,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,5592405,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,5636095,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,11184810,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,13421772,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,16777215,2863311530,3435973836,4042322160,4278190080,4294967040],[]),([5,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,16777215,2863311530,3435973836,4042322160,4294967040],[(2,15)])]
noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([5,268435455,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1077952576,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1145324612,2290649224,2863311530,4042322160,4278255360,4294901760],[(104,2),(136,0)]),([5,1145324612,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1145324612,2863311530,3722304989,4042322160,4278255360,4294901760],[]),([5,1145324612,2863311530,4042322160,4244438268,4278255360,4294901760],[]),([5,1145324612,3722304989,4042322160,4278255360,4294901760],[]),([5,1145359564,1431699455,2863311530,4042322160,4278255360,4294901760],[(140,1)]),([5,1145359564,2863267840,2863311530,4042322160,4278255360,4294901760],[(56,20),(104,1)]),([5,1145359564,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1145359564,2863311530,4042322160,4278255360,4294901760],[]),([5,1414812756,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1431655765,2863311530,3233857728,4244438268,4278255360,4294901760],[]),([5,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,1431655765,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,1431655765,3233857728,4244438268,4278255360,4294901760],[]),([5,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([5,1431655765,3435973836,4042322160,4278255360,4294936712],[]),([5,1431655935,2863311530,3435973836,4042322160,4278255360,4294901760],[(100,5)]),([5,1431699455,2863311530,3435973836,4042322160,4278255360,4294901760],[(100,5),(132,11)]),([5,1431699455,2863311530,3435973836,4042322160,4289396480,4294901760],[(100,5),(132,11),(172,17)]),([5,1431699455,3435973836,4042322160,4278255360,4294945450],[]),([5,1442840575,2863311530,3435973836,4042322160,4278255360,4294901760],[(100,5),(132,11),(172,17)]),([5,2147516416,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2155905152,2863311530,3233857728,4244438268,4278255360,4294901760],[(128,0)]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,0)]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,2155905152,2863311530,3435973836,4042322160,4278255360,4294936712],[]),([5,2155905152,2863311530,3435973836,4177066232,4278255360,4294901760],[(56,2),(72,2),(96,2),(128,4),(168,2)]),([5,2290124928,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)]),([5,2290649224,2863311530,3233857728,4244438268,4278255360,4294901760],[(128,0)]),([5,2290649224,2863311530,3435187392,4042322160,4278255360,4294901760],[(96,1)]),([5,2290649224,2863311530,3435973836,4026593280,4293984240,4294901760],[(56,7),(72,7),(96,3),(128,7),(168,7)]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(96,2),(128,0)])]
noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294934656],[(96,2),(128,0)]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712],[(96,1)]),([5,2290649224,2863311530,3435973836,4042322160,4278255360,4294942880],[(56,5),(72,5),(96,1)]),([5,2290649224,2863311530,3435973836,4042322160,4287168392,4294936712],[]),([5,2290649224,2863311530,3974950124,4042322160,4278255360,4294901760],[(56,8),(72,8),(96,15),(128,9),(168,7)]),([5,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[(96,16),(128,10),(168,8)]),([5,2290649224,2863311530,4008636142,4042322160,4278255360,4294936712],[(56,8),(72,8),(96,13),(128,7),(168,8)]),([5,2290649224,4008636142,4042322160,4278255360,4294901760],[]),([5,2290649224,4008636142,4042322160,4278255360,4294936712],[(72,13),(96,7)]),([5,2290657962,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290666700,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2290679807,2863311530,3435973836,4042322160,4278255360],[(2,20)]),([5,2290679807,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2827528328,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,8),(96,2),(128,0)]),([5,2829625512,2863311530,3233857728,4244438268,4278255360,4294901760],[(72,15),(128,0)]),([5,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,8),(96,2),(128,0)]),([5,2829625512,2863311530,3435973836,4042322160,4278255360,4294944936],[(72,7),(96,1)]),([5,2829625512,2863311530,3435973836,4177066232,4278255360,4294901760],[(56,2),(72,15),(96,2),(128,3),(168,1)]),([5,2829625512,2863311530,3435973836,4210752250,4278255360,4294901760],[(72,15),(128,4),(168,2)]),([5,2829625512,3435973836,4210752250,4278255360,4294901760],[]),([5,2863180456,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,8),(96,2),(128,0)]),([5,2863311530,2863311530,3233857728,4244438268,4278255360,4294901760],[(72,15)]),([5,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863311530,3435973836,4042322160,4278255360,4294936712],[(72,8)]),([5,2863311530,2863311615,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863329006,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,2868903935,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3221225472,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3221274624,3233857728,4244438268,4278255360,4294901760],[(144,11)]),([5,2863311530,3221274624,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3221274624,3435973836,4042322160,4278255360,4294950912],[]),([5,2863311530,3221274624,3435973836,4042322160,4290838464,4294901760],[(176,0),(112,11)]),([5,2863311530,3229663360,3435973836,4042322160,4278255360,4294901760],[(136,0)]),([5,2863311530,3233857536,3435973836,4042322160,4278255360,4294901760],[(136,0)])]
noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3233857728,3233857728,4244438268,4278255360,4294901760],[]),([5,2863311530,3233857728,3422604288,4042322160,4291624908,4294901760],[(104,1),(136,1)]),([5,2863311530,3233857728,3431517320,4042322160,4278255360,4294901760],[(136,1),(112,5)]),([5,2863311530,3233857728,3435973836,4042322160,4278190080,4294967040],[(80,15),(104,15)]),([5,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3233857728,3435973836,4042322160,4278255360,4294934656],[]),([5,2863311530,3233857728,3435973836,4042322160,4278255360,4294936712],[]),([5,2863311530,3233857728,3435973836,4042322160,4278255360,4294945280],[(80,11),(104,11)]),([5,2863311530,3233857728,3435973836,4042322160,4278255360,4294950912],[(136,0)]),([5,2863311530,3233857728,3435973836,4177066232,4278255360,4294901760],[(80,2),(104,2)]),([5,2863311530,3233857728,3435973836,4210096880,4278255360,4294901760],[(80,12),(104,12)]),([5,2863311530,3233857728,3435973836,4243651824,4278255360,4294901760],[]),([5,2863311530,3233857728,3435973836,4244438268,4278255360,4294901760],[]),([5,2863311530,3233857728,3941264106,4244438268,4278255360,4294901760],[(80,15),(104,15)]),([5,2863311530,3233857728,4008636142,4244438268,4278255360,4294901760],[]),([5,2863311530,3233857728,4227922944,4244438268,4278255360,4294901760],[]),([5,2863311530,3233857728,4244438268,4244438268,4278255360,4294901760],[]),([5,2863311530,3233857728,4244438268,4278124286,4278255360,4294901760],[(196,0)]),([5,2863311530,3233857728,4244438268,4278255360,4278255360,4294901760],[]),([5,2863311530,3233857728,4244438268,4278255360,4289396650,4294901760],[(56,15)]),([5,2863311530,3233857728,4244438268,4278255360,4290838464,4294901760],[(108,11)]),([5,2863311530,3233857728,4244438268,4278255360,4291624908,4294901760],[]),([5,2863311530,3233857728,4244438268,4278255360,4294770684,4294901760],[]),([5,2863311530,3233857728,4244438268,4278255360,4294901760],[(58,15)]),([5,2863311530,3233857728,4244438268,4278255360,4294901760,4294967040],[]),([5,2863311530,3233860812,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3233873919,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3301229764,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3364407432,3435973836,4042322160,4278255360,4294901760],[(104,2),(136,0)]),([5,2863311530,3368077504,3435973836,4042322160,4278255360,4294901760],[(104,2)]),([5,2863311530,3368077504,3435973836,4210096880,4278255360,4294901760],[(80,12),(104,12)]),([5,2863311530,3368601800,3435973836,4042322160,4278255360,4294901760],[(104,2)]),([5,2863311530,3368601800,3435973836,4177066232,4278255360,4294901760],[(80,2),(104,2)]),([5,2863311530,3368601800,3435973836,4244438268,4278255360,4294901760],[]),([5,2863311530,3368601800,4008636142,4042322160,4278255360,4294901760],[(104,16)]),([5,2863311530,3368601800,4042322160,4244438268,4278255360,4294901760],[]),([5,2863311530,3368601800,4042322160,4278124286,4278255360,4294901760],[(196,0)]),([5,2863311530,3368601800,4210752250,4244438268,4278255360,4294901760],[])]
noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3368601800,4244438268,4278255360,4294901760],[(58,15)]),([5,2863311530,3435184320,3435973836,4042322160,4278255360,4294901760],[(104,2)]),([5,2863311530,3435187392,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435187392,4042322160,4244438268,4278255360,4294901760],[]),([5,2863311530,3435187392,4042322160,4278255360,4294770684,4294901760],[(116,7)]),([5,2863311530,3435187392,4042322160,4278255360,4294901760,4294954188],[(140,3)]),([5,2863311530,3435711688,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435711688,4042322160,4210752250,4278255360,4294901760],[(156,13)]),([5,2863311530,3435711688,4042322160,4278255360,4293984240,4294901760],[(116,7)]),([5,2863311530,3435711688,4042322160,4278255360,4294639610,4294901760],[]),([5,2863311530,3435711688,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973824,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435973836,4042322160,4278255360,4294936712],[]),([5,2863311530,3435973836,3435973836,4042322160,4278255360,4294942880],[(64,5),(68,5)]),([5,2863311530,3435973836,3435973887,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435978205,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435982574,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435986172,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3439329279,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3587560917,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3705461980,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3722313727,4042322160,4278255360,4294901760],[(116,5),(148,11)]),([5,2863311530,3435973836,3937069738,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,3938511552,4042322160,4278255360,4294901760],[(80,14),(104,15),(112,12)]),([5,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[(104,15)]),([5,2863311530,3435973836,3941264106,4244438268,4278255360,4294901760],[(104,15)]),([5,2863311530,3435973836,3972852940,4042322160,4278255360,4294901760],[(80,8)]),([5,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760],[(80,8)]),([5,2863311530,3435973836,3974950124,4042322160,4278255360,4294942880],[(80,7),(84,5)]),([5,2863311530,3435973836,3974950124,4210752250,4278255360,4294901760],[(80,15)]),([5,2863311530,3435973836,4007718624,4042322160,4278255360,4294901760],[(80,8),(156,7)]),([5,2863311530,3435973836,4008373994,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4008505068,4042322160,4278255360,4294901760],[(80,8)]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[])]
noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294936712],[(80,8)]),([5,2863311530,3435973836,4008636142,4042322160,4278255360,4294942880],[(76,5),(84,5)]),([5,2863311530,3435973836,4008640511,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4241280204,4278255360,4294901760],[(104,8)]),([5,2863311530,3435973836,4042322160,4241289216,4278255360,4294901760],[(176,7),(144,3)]),([5,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4243389676,4278255360,4294901760],[(116,5)]),([5,2863311530,3435973836,4042322160,4244438016,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4244438220,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4244438268,4278255360,4294936712],[]),([5,2863311530,3435973836,4042322160,4244438268,4278255360,4294944936],[]),([5,2863311530,3435973836,4042322160,4244438268,4278255360,4294945280],[(108,11),(116,11),(156,11)]),([5,2863311530,3435973836,4042322160,4244439039,4278255360,4294901760],[(156,11)]),([5,2863311530,3435973836,4042322160,4261281277,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4277075694,4278255360,4294901760],[(116,5),(156,11),(196,17)]),([5,2863311530,3435973836,4042322160,4277993212,4278255360,4294901760],[(156,11)]),([5,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(156,11),(196,17)]),([5,2863311530,3435973836,4042322160,4278255360,4294769916,4294901760],[]),([5,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901758,4294901760],[(204,17)]),([5,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967292],[]),([5,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([5,2863311530,3435973836,4042322160,4278255360,4294902015,4294967040],[(156,15)]),([5,2863311530,3435973836,4042322160,4278255360,4294923605,4294945450],[]),([5,2863311530,3435973836,4042322160,4278255360,4294934656],[]),([5,2863311530,3435973836,4042322160,4278255360,4294936712],[(58,8)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294936712],[]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294945450],[]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294954188],[(140,3)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294963440],[(180,0),(148,9)]),([5,2863311530,3435973836,4042322160,4278255360,4294936712,4294965496],[(180,0),(148,9)]),([5,2863311530,3435973836,4042322160,4278255360,4294944936],[(58,8),(74,2)]),([5,2863311530,3435973836,4042322160,4278255360,4294945450,4294951104],[(140,3),(148,9)]),([5,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188],[(140,3)])]
noncomputable def K_8 : List (List ℕ × List (ℕ × ℕ)) := [([5,2863311530,3435973836,4042322160,4278255360,4294945450,4294966524],[]),([5,2863311530,3435973836,4042322160,4278255360,4294950912],[]),([5,2863311530,3435973836,4042322160,4278255360,4294951104,4294967040],[(156,15)]),([5,2863311530,3435973836,4042322160,4287168392,4294936712],[(56,7),(58,7)]),([5,2863311530,3435973836,4042322160,4289374890,4294967040],[(73,5),(133,15)]),([5,2863311530,3435973836,4042322160,4289396480,4294945450],[]),([5,2863311530,3435973836,4042322160,4289396650,4294945450,4294967040],[(172,15),(204,0)]),([5,2863333375,3435973836,4042322160,4278255360,4294901760,4294945450],[]),([5,3221274624,3435973836,3937069738,4042322160,4278255360,4294901760],[]),([5,3233857728,3435973836,3937069738,4042322160,4278255360,4294901760],[]),([5,3435973836,3937069738,4042322160,4278255360,4294901760],[]),([5,3435973836,3941264106,4042322160,4278255360,4289396650,4294901760],[(72,15)]),([6,0,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,0,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,0,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([6,0,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,5),(129,11),(169,17)]),([6,255,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,15),(97,5),(101,5),(129,11),(169,17)]),([6,255,2863311530,3435973836,4042322160,4278255360,4294901760,4294967040],[(128,0)]),([6,21845,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,17),(97,5),(101,5),(129,11),(133,11),(169,17)])]
noncomputable def K_9 : List (List ℕ × List (ℕ × ℕ)) := [([6,21845,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450],[]),([6,43690,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,43690,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,43690,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,17),(97,5),(101,5),(129,11),(133,11),(169,17)]),([6,52428,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,52428,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,52428,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,20),(97,5),(129,11),(133,1),(169,3)]),([6,65535,65535,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,16711935,2863311530,3435973836,4042322160],[(2,0),(14,5)]),([6,65535,16711935,2863311530,3435973836,4042322160,4278255360],[(2,0)]),([6,65535,16711935,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,1431655765,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,1431655765,3435973836,4042322160,4278255360],[(10,7),(14,1)])]
noncomputable def K_10 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2290649224,2863311530,3435973836,4042322160,4278255360],[(136,1)]),([6,65535,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(136,1)]),([6,65535,2863267840,2863311530,3435973836,4042322160,4278255360],[(2,17),(104,7),(136,1)]),([6,65535,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760],[(104,7),(136,1)]),([6,65535,2863311530,2863311530,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,2863333375,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3233857728,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435921408,3435973836,4042322160,4278255360],[(2,3)]),([6,65535,2863311530,3435921408,3435973836,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,3435973836,4042322160,4278255360],[]),([6,65535,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_11 : List (List ℕ × List (ℕ × ℕ)) := [([6,65535,2863311530,3435973836,3435986943,4042322160,4278255360],[]),([6,65535,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,4008636142,4042322160,4278255360],[]),([6,65535,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,4042322160,4244438268,4278255360],[]),([6,65535,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[]),([6,65535,2863311530,3435973836,4042322160,4278255360],[(10,7),(14,1)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,17),(97,5),(101,5),(129,11),(133,11)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294901760],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294945450],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294954188],[(72,8)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294945450],[(2,17)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294954188],[(2,3)]),([6,65535,2863311530,3435973836,4042322160,4278255360,4294967295],[]),([6,16777215,2863311530,3435973836,4042322160,4278190080,4278255360,4294901760],[(172,11),(220,17)])]
noncomputable def K_12 : List (List ℕ × List (ℕ × ℕ)) := [([6,16777215,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,15),(97,5),(101,5),(133,11),(173,17)]),([6,1145324612,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,1145324612,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([6,1145324612,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,8),(97,5),(129,11),(133,1),(169,17),(173,3),(145,1),(185,3)]),([6,1431655765,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,1431655765,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(136,2),(176,0)]),([6,1431655765,2290649224,3435973836,4042322160,4278255360,4294901760],[(104,2),(136,0)]),([6,1431655765,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760],[]),([6,1431655765,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(72,8)]),([6,1431655765,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(100,5)]),([6,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,5),(101,5),(129,11),(133,11),(169,17),(173,17)]),([6,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[])]
noncomputable def K_13 : List (List ℕ × List (ℕ × ℕ)) := [([6,1431655765,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,1431655765,3435973836,3722304989,4042322160,4278255360,4294901760],[]),([6,1431655765,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,1431655765,3435973836,4042322160,4244438268,4278255360,4294901760],[]),([6,1431655765,3435973836,4042322160,4278255360,4294901760],[(6,8),(10,2),(14,0)]),([6,1431655765,3435973836,4042322160,4278255360,4294901760,4294967295],[]),([6,1431699455,2863267840,2863311530,3435973836,4042322160,4278255360,4294901760],[(132,5),(172,11),(220,17),(104,7),(136,1)]),([6,1431699455,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,17),(97,5),(100,5),(102,5),(101,5),(129,11),(132,11),(134,11),(133,11),(173,17)]),([6,2155905152,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(168,0),(176,0)]),([6,2155905152,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[(168,0)]),([6,2155905152,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,15),(97,5),(128,0),(130,0),(129,11),(169,17),(173,0)]),([6,2290649224,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,2),(168,0)]),([6,2290649224,2694881440,2863311530,3435973836,4042322160,4278255360,4294901760],[(72,5),(96,5),(128,5),(168,6),(216,5),(176,0)])]
noncomputable def K_14 : List (List ℕ × List (ℕ × ℕ)) := [([6,2290649224,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(128,2),(168,0)]),([6,2290649224,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[(168,0)]),([6,2290649224,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(128,2),(168,0)]),([6,2290649224,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(128,2),(168,0)]),([6,2290649224,2863311530,3435973836,4026593280,4042322160,4278255360,4294901760],[(56,7),(72,7),(96,7),(128,13),(168,7),(216,7)]),([6,2290649224,2863311530,3435973836,4042322160,4042322160,4278255360,4294901760],[(56,5),(72,5),(96,5),(168,6),(216,5)]),([6,2290649224,2863311530,3435973836,4042322160,4177066232,4278255360,4294901760],[(56,5),(72,5),(96,2),(128,5),(168,6),(216,5),(152,2)]),([6,2290649224,2863311530,3435973836,4042322160,4210752250,4278255360,4294901760],[(56,5),(72,5),(96,2),(128,5),(168,6),(216,5)]),([6,2290649224,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(96,2),(168,0)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4293984240,4294901760],[(56,7),(72,7),(96,2),(128,0),(168,7),(216,7)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,8),(96,2),(98,2),(97,5),(128,0),(130,0),(129,11),(133,1),(169,17),(173,3)]),([6,2290649224,2863311530,3435973836,4042322160,4278255360,4294936712],[(2,8),(96,1),(98,1),(97,5),(129,11),(133,1)]),([6,2290649224,2863311530,4008636142,4042322160,4278255360,4294901760],[(96,16),(98,2),(97,5),(128,10),(130,0),(129,11),(168,8),(169,17)]),([6,2290649224,3435973836,4008636142,4042322160,4278255360,4294901760],[(6,8)]),([6,2290649224,4008636142,4042322160,4278255360,4294901760],[(2,8),(74,2),(98,0),(6,8),(10,2),(14,0)]),([6,2829625512,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(72,8),(96,2),(168,0)]),([6,2829625512,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,15),(72,8),(74,5),(96,2),(97,5),(101,5),(128,0),(130,0),(129,11),(133,11),(169,17),(173,17),(80,5),(82,5)]),([6,2863311530,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[])]
noncomputable def K_15 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,2863311530,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(72,8),(96,2)]),([6,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,5),(101,5),(129,11),(133,11),(169,17),(173,17)]),([6,2863311530,2863333375,3435973836,4042322160,4278255360,4294901760],[(6,17),(105,5),(109,5),(137,11),(141,11),(181,17)]),([6,2863311530,3221274624,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,3221274624,3435973836,4042322160,4278255360,4294901760],[(6,17),(105,5),(137,11),(177,17)]),([6,2863311530,3233857728,3233857728,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,3233857728,3422604288,3435973836,4042322160,4278255360,4294901760],[(104,1),(136,1),(176,1),(152,1)]),([6,2863311530,3233857728,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,3233857728,3435973836,3941264106,4042322160,4278255360,4294901760],[]),([6,2863311530,3233857728,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,2863311530,3233857728,3435973836,4042322160,4244438268,4278255360,4294901760],[(84,5),(144,5)]),([6,2863311530,3233857728,3435973836,4042322160,4278190080,4278255360,4294901760],[(80,15),(104,15),(136,2),(112,15)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4278255360,4294901760],[(80,11),(104,11),(136,11)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4289396650,4294901760],[(80,11),(104,11),(136,0),(176,11),(196,5)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4290838464,4294901760],[(80,11),(104,11),(176,11)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4291624908,4294901760],[(80,1),(104,1),(176,1)])]
noncomputable def K_16 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[(6,15),(105,5),(137,11),(177,17),(181,0),(113,5)]),([6,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760,4294967040],[(80,15),(104,15),(136,0),(224,15)]),([6,2863311530,3233857728,3435973836,4244438268,4278255360,4294901760],[(10,8),(149,1),(185,0),(189,3)]),([6,2863311530,3233857728,4244438268,4278255360,4294901760],[(58,15),(103,11),(131,0),(135,17),(6,15),(7,15),(139,0),(143,0),(10,15),(11,15),(147,0),(151,0),(14,0),(15,0),(159,15),(17,0)]),([6,2863311530,3368601800,3435973836,4042322160,4210752250,4278255360,4294901760],[(80,5),(104,2),(136,5)]),([6,2863311530,3368601800,3435973836,4042322160,4278255360,4294901760],[(6,16),(104,2),(105,5),(137,11),(141,1),(177,17),(181,3),(149,1),(189,3)]),([6,2863311530,3435187392,3435973836,4042322160,4278255360,4293984240,4294901760],[(80,7),(176,7),(156,7)]),([6,2863311530,3435187392,3435973836,4042322160,4278255360,4294901760],[(6,20),(105,5),(137,11),(141,1),(177,17),(181,3),(145,1)]),([6,2863311530,3435973836,3435973836,3435973836,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,3435973836,4008636142,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,3435973836,4042322160,4042322160,4278255360,4294901760],[(64,5),(68,5)]),([6,2863311530,3435973836,3435973836,4042322160,4210752250,4278255360,4294901760],[(64,5),(68,5),(104,2)]),([6,2863311530,3435973836,3435973836,4042322160,4244438268,4278255360,4294901760],[]),([6,2863311530,3435973836,3435973836,4042322160,4278255360,4293984240,4294901760],[(64,7),(68,7),(156,7)]),([6,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(6,8),(137,1),(141,1),(177,3),(181,3)]),([6,2863311530,3435973836,3435986943,4042322160,4278255360,4294901760],[(177,8),(10,20),(117,5),(145,1),(149,11),(189,3)])]
noncomputable def K_17 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3435973836,3722304989,4042322160,4278255360,4294901760],[(58,8),(10,8),(117,5),(145,1),(149,11),(185,3),(189,17)]),([6,2863311530,3435973836,3941264106,4042322160,4278255360,4294901760],[(169,0),(104,15),(105,5),(10,15),(113,5),(117,5),(145,11),(149,11),(185,17),(189,17)]),([6,2863311530,3435973836,3974950124,4042322160,4278255360,4294901760],[(58,8),(6,8),(80,8),(81,8),(105,8),(109,5),(137,8),(141,11),(177,10),(181,17),(10,16),(117,5),(145,1),(149,11),(185,3),(189,17)]),([6,2863311530,3435973836,4008636142,4008636142,4042322160,4278255360,4294901760],[]),([6,2863311530,3435973836,4008636142,4042322160,4210752250,4278255360,4294901760],[(76,5),(84,5),(104,15),(116,5)]),([6,2863311530,3435973836,4008636142,4042322160,4244438268,4278255360,4294901760],[(80,8),(136,8),(116,5)]),([6,2863311530,3435973836,4008636142,4042322160,4278124286,4278255360,4294901760],[(116,5),(204,11),(252,17)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4293984240,4294901760],[(76,7),(84,7),(176,8),(156,7)]),([6,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(105,8),(137,14),(177,20),(10,8),(117,5),(145,1),(149,11),(185,3),(189,17)]),([6,2863311530,3435973836,4042322160,4241292492,4278255360,4294901760],[(58,8),(85,5),(141,11),(177,8),(118,5),(14,20),(153,1),(157,11),(193,3),(197,17)]),([6,2863311530,3435973836,4042322160,4244438268,4244438268,4278255360,4294901760],[]),([6,2863311530,3435973836,4042322160,4244438268,4278124286,4278255360,4294901760],[(204,11),(252,17)]),([6,2863311530,3435973836,4042322160,4244438268,4278255360,4291624908,4294901760],[(108,1),(140,1),(116,1),(188,5),(156,11)]),([6,2863311530,3435973836,4042322160,4244438268,4278255360,4294770684,4294901760],[(156,11)]),([6,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(58,8),(74,2),(85,5),(118,5),(14,15),(157,11),(193,0),(197,17)]),([6,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760,4294967040],[(108,15),(228,2),(116,15),(236,8),(156,11),(196,17),(204,15)])]
noncomputable def K_18 : List (List ℕ × List (ℕ × ℕ)) := [([6,2863311530,3435973836,4042322160,4278124286,4278255360,4294901760],[(118,5),(14,15),(156,11),(158,11),(157,11),(193,0),(196,17),(198,17),(197,17)]),([6,2863311530,3435973836,4042322160,4278255360,4294770684,4294901760],[(58,8),(74,2),(98,0),(150,5),(158,11),(18,17),(205,17)]),([6,2863311530,3435973836,4042322160,4278255360,4294901760],[(75,5),(79,5),(99,11),(103,11),(131,17),(135,17),(6,8),(7,8),(107,1),(111,1),(139,3),(143,3),(9,5),(10,2),(11,2),(115,7),(119,7),(147,9),(151,9),(13,11),(14,0),(15,0),(155,15),(159,15),(17,17)]),([6,2863311530,3435973836,4042322160,4278255360,4294901760,4294967295],[(190,5),(198,11),(206,17)]),([6,2863311530,3435973836,4042322160,4278255360,4294936712],[(58,8),(75,5),(79,5),(99,11),(103,11),(135,3),(6,8),(7,8),(107,1),(111,1),(143,3),(9,5),(10,2),(11,2),(115,7),(119,7),(151,9),(13,11),(14,0),(15,0),(155,1),(159,15),(18,7),(19,7)]),([6,2863311530,3435973836,4042322160,4278255360,4294945450,4294954188],[(58,7),(172,3),(174,3),(140,3),(142,3),(141,3),(194,1)]),([7,65535,2863311530,3435973836,4042322160,4278255360],[(99,5),(103,5),(131,11),(135,11),(107,5),(111,5),(139,11),(143,11),(10,7),(11,7),(147,1),(151,1),(13,5),(14,1),(15,1),(155,7),(159,7),(17,11)]),([7,65535,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,17),(97,5),(99,5),(101,5),(103,5),(129,11),(131,11),(133,11),(135,11),(107,5),(111,5),(139,11),(143,11),(10,8),(11,7),(147,1),(151,1),(13,5),(14,2),(15,1),(155,7),(159,7),(194,5),(195,5),(198,5),(199,5),(17,11),(18,0),(202,11),(203,11),(206,11),(207,11)]),([7,1431655765,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,5),(99,5),(101,5),(103,5),(129,11),(131,11),(133,11),(135,11),(169,17),(171,17),(173,17),(175,17),(105,5),(107,5),(109,5),(111,5),(137,11),(139,11),(141,11),(143,11),(177,17),(179,17),(181,17),(183,17),(10,8),(11,8),(147,1),(151,1),(187,3),(191,3),(13,5),(14,2),(15,2),(155,7),(159,7),(195,9),(199,9),(17,11),(18,0),(19,0),(203,15),(207,15),(21,17)]),([7,1431655765,3435973836,4042322160,4278255360,4294901760],[(75,5),(79,5),(99,11),(103,11),(131,17),(135,17),(6,8),(7,8),(107,1),(111,1),(139,3),(143,3),(9,5),(10,2),(11,2),(115,7),(119,7),(147,9),(151,9),(13,11),(14,0),(15,0),(155,15),(159,15),(17,17)]),([7,2290649224,2863311530,3435973836,4042322160,4278255360,4294901760],[(2,8),(3,8),(96,2),(98,2),(97,5),(128,0),(130,0),(129,11),(131,1),(133,1),(135,1),(169,17),(171,3),(173,3),(175,3),(139,1),(143,1),(179,3),(183,3),(10,8),(11,8),(147,1),(151,1),(187,3),(191,3),(14,2),(15,2),(195,0),(199,0),(17,1),(18,0),(19,0),(203,2),(207,2),(21,3)])]
noncomputable def K_19 : List (List ℕ × List (ℕ × ℕ)) := [([7,2863311530,2863311530,3435973836,4042322160,4278255360,4294901760],[(97,5),(99,5),(101,5),(103,5),(129,11),(131,11),(133,11),(135,11),(169,17),(171,17),(173,17),(175,17),(10,8),(11,8),(147,1),(151,1),(187,3),(191,3),(13,5),(14,2),(15,2),(155,7),(159,7),(195,9),(199,9),(17,11),(18,0),(19,0),(203,15),(207,15),(21,17)]),([7,2863311530,3233857728,3435973836,4042322160,4278255360,4294901760],[(99,5),(103,5),(135,11),(171,0),(175,17),(6,15),(7,15),(105,5),(107,5),(137,11),(177,17),(179,0),(181,0),(183,0),(10,8),(11,8),(113,5),(187,0),(191,0),(13,5),(14,2),(15,2),(155,5),(159,5),(195,6),(199,6),(18,0),(19,0),(21,0)]),([7,2863311530,3435973836,3435973836,4042322160,4278255360,4294901760],[(103,5),(131,1),(135,11),(171,3),(175,17),(6,8),(7,8),(137,1),(139,1),(141,1),(143,1),(177,3),(179,3),(181,3),(183,3),(14,2),(15,2),(159,7),(195,0),(199,9),(17,1),(18,0),(19,0),(203,2),(207,15),(21,3)]),([7,2863311530,3435973836,4008636142,4042322160,4278255360,4294901760],[(103,5),(131,1),(135,11),(171,3),(175,17),(6,8),(7,8),(105,8),(137,14),(139,1),(143,1),(177,20),(179,3),(183,3),(10,8),(11,8),(117,5),(119,5),(145,1),(147,1),(149,11),(151,11),(185,3),(187,3),(189,17),(191,17),(13,5),(14,2),(15,2),(159,7),(195,0),(199,9),(17,11),(18,0),(19,0),(203,2),(207,15),(21,17)]),([7,2863311530,3435973836,4042322160,4244438268,4278255360,4294901760],[(58,8),(74,2),(75,5),(79,5),(131,11),(135,11),(171,17),(175,17),(6,8),(7,8),(85,5),(143,1),(179,0),(183,3),(9,5),(10,2),(11,2),(118,5),(119,5),(147,5),(151,7),(187,6),(191,9),(14,15),(15,15),(157,11),(159,11),(193,0),(195,0),(197,17),(199,17),(17,11),(18,0),(19,0),(207,15),(21,17)]),([7,2863311530,3435973836,4042322160,4278255360,4294901760],[(75,5),(79,5),(99,11),(103,11),(131,17),(135,17),(6,8),(7,8),(107,1),(111,1),(139,3),(143,3),(9,5),(10,2),(11,2),(115,7),(119,7),(147,9),(151,9),(13,11),(14,0),(15,0),(155,15),(159,15),(17,17)]),([8,2863311530,3435973836,4042322160,4278255360,4294901760],[(75,5),(79,5),(99,11),(103,11),(131,17),(135,17),(6,8),(7,8),(107,1),(111,1),(139,3),(143,3),(9,5),(10,2),(11,2),(115,7),(119,7),(147,9),(151,9),(13,11),(14,0),(15,0),(155,15),(159,15),(17,17)])]
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_8 : K_8.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_9 : K_9.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_10 : K_10.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_11 : K_11.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_12 : K_12.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_13 : K_13.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_14 : K_14.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_15 : K_15.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_16 : K_16.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_17 : K_17.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_18 : K_18.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
theorem c_19 : K_19.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem hK_cert : T_cert.toList = ((((K_0 ++ K_1) ++ (K_2 ++ (K_3 ++ K_4))) ++ ((K_5 ++ K_6) ++ (K_7 ++ (K_8 ++ K_9)))) ++ (((K_10 ++ K_11) ++ (K_12 ++ (K_13 ++ K_14))) ++ ((K_15 ++ K_16) ++ (K_17 ++ (K_18 ++ K_19))))).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert ((all_app (all_app (all_app (all_app c_0 c_1) (all_app c_2 (all_app c_3 c_4))) (all_app (all_app c_5 c_6) (all_app c_7 (all_app c_8 c_9)))) (all_app (all_app (all_app c_10 c_11) (all_app c_12 (all_app c_13 c_14))) (all_app (all_app c_15 c_16) (all_app c_17 (all_app c_18 c_19))))))

theorem lb : ∀ s : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xfeeaeaa8 (idx5 x)) s → 9 ≤ s :=
  lb_cert _ L_ M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel)

set_option maxRecDepth 100000 in
theorem main : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xfeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xfeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  simp only [sum_eq] at h ⊢
  exact ⟨⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [12, 10]⟩], 13⟩, by simp [PEqualNP.MetaComplexity.Monotone2], le_trans (by decide) (lb s h), by decide +kernel⟩

end LowOne

def dualGate (L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
      if g.inputs.all (fun i => decide (i < L)) then ⟨GateOp.or, g.inputs⟩ else ⟨GateOp.and, []⟩
  | GateOp.or =>
      ⟨GateOp.and, g.inputs.filter (fun i => decide (i < L))⟩
  | GateOp.not =>
      match g.inputs with
      | [] => ⟨GateOp.or, []⟩
      | i :: _ => if i < L then ⟨GateOp.not, [i]⟩ else ⟨GateOp.or, []⟩
  | op => ⟨op, g.inputs⟩

def dualGates (L : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => dualGate L g :: dualGates (L + 1) gs

theorem dualGates_length (L : ℕ) (gs : List Gate) : (dualGates L gs).length = gs.length := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih => simp [dualGates, ih]

theorem dualGate_ok (L : ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (dualGate L g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (dualGate L g).inputs.length ≤ 2 := by
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  rcases hop with h | h | h
  · unfold dualGate; rw [h]; dsimp only
    split
    · exact ⟨Or.inr (Or.inl rfl), hlen⟩
    · exact ⟨Or.inl rfl, by simp⟩
  · unfold dualGate; rw [h]; dsimp only
    exact ⟨Or.inl rfl, le_trans (List.length_filter_le _ _) hlen⟩
  · unfold dualGate; rw [h]; dsimp only
    cases hi : g.inputs with
    | nil => exact ⟨Or.inr (Or.inl rfl), by simp⟩
    | cons i rest =>
      dsimp only
      split
      · exact ⟨Or.inr (Or.inr rfl), by simp⟩
      · exact ⟨Or.inr (Or.inl rfl), by simp⟩

theorem dualGates_ok (L : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ dualGates L gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing L with
  | nil => intro g hg; cases hg
  | cons g gs ih =>
    intro g' hg'
    simp only [dualGates, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact dualGate_ok L g (hgs g (by simp))
    · exact ih (L + 1) (fun x hx => hgs x (by simp [hx])) g' hg'

theorem getD_map_not (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (w.map (!·)).getD i false = !(w.getD i false) := by
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getD_eq_getElem _ _ hi]
  simp

theorem dualGate_and_all (w : List Bool) (l : List ℕ)
    (hall : l.all (fun i => decide (i < w.length)) = true) :
    (l.map fun i => (w.map (!·)).getD i false).any id = !(l.map fun i => w.getD i false).all id := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
    simp only [List.map_cons, List.any_cons, List.all_cons, id_eq]
    rw [getD_map_not w i hall.1, ih hall.2]
    cases w.getD i false <;> cases (l.map fun k => w.getD k false).all id <;> rfl

theorem dualGate_and_oob (w : List Bool) (l : List ℕ)
    (hall : l.all (fun i => decide (i < w.length)) = false) :
    (l.map fun i => w.getD i false).all id = false := by
  induction l with
  | nil => simp at hall
  | cons i l ih =>
    simp only [List.map_cons, List.all_cons, id_eq]
    by_cases hlt : i < w.length
    · simp only [List.all_cons, decide_eq_true hlt, Bool.true_and] at hall
      rw [ih hall, Bool.and_false]
    · have hwi : w.getD i false = false := List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)
      rw [hwi, Bool.false_and]

theorem dualGate_or_aux (w : List Bool) (l : List ℕ) :
    ((l.filter (fun i => decide (i < w.length))).map fun i => (w.map (!·)).getD i false).all id =
      !(l.map fun i => w.getD i false).any id := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hlt : i < w.length
    · simp only [List.filter_cons, decide_eq_true hlt, ite_true, List.map_cons, List.all_cons, List.any_cons, id_eq]
      rw [getD_map_not w i hlt, ih]
      cases w.getD i false <;> cases (l.map fun k => w.getD k false).any id <;> rfl
    · have hwi : w.getD i false = false := List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)
      simp only [List.filter_cons, decide_eq_false hlt, ite_false, List.map_cons, List.any_cons, id_eq]
      rw [hwi, Bool.false_or]
      exact ih

theorem dualGate_eval (w : List Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (dualGate w.length g).op.eval ((dualGate w.length g).inputs.map fun i => (w.map (!·)).getD i false) =
      !(g.op.eval (g.inputs.map fun i => w.getD i false)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · unfold dualGate; rw [h]; dsimp only
    split
    · rename_i hall
      exact dualGate_and_all w g.inputs hall
    · rename_i hall
      have hfalse : g.inputs.all (fun i => decide (i < w.length)) = false :=
        Bool.eq_false_iff.mpr hall
      simp only [GateOp.eval, List.map_nil, List.all_nil, dualGate_and_oob w g.inputs hfalse, Bool.not_false]
  · unfold dualGate; rw [h]; dsimp only
    exact dualGate_or_aux w g.inputs
  · unfold dualGate; rw [h]; dsimp only
    cases hi : g.inputs with
    | nil => simp [GateOp.eval]
    | cons i rest =>
      dsimp only
      split
      · rename_i hlt
        simp only [GateOp.eval, List.map_cons, List.headD_cons, getD_map_not w i hlt, Bool.not_not]
      · rename_i hlt
        have hwi : w.getD i false = false := List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)
        simp only [GateOp.eval, List.map_cons, List.headD_cons]
        rw [hwi]; rfl

theorem dualGates_wires (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    ∀ w : List Bool,
      wiresFrom (dualGates w.length gs) (w.map (!·)) = (wiresFrom gs w).map (!·) := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have hg := hgs g (by simp)
    have hrest : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
      fun g' hx => hgs g' (by simp [hx])
    change wiresFrom (dualGates (w.length + 1) gs)
      (w.map (!·) ++ [(dualGate w.length g).op.eval
        ((dualGate w.length g).inputs.map fun i => (w.map (!·)).getD i false)]) =
      (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).map (!·)
    rw [dualGate_eval w g hg]
    have hstep : w.map (!·) ++ [!(g.op.eval (g.inputs.map fun i => w.getD i false))] =
        (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).map (!·) := by simp
    rw [hstep]
    have hlen : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by simp
    rw [← hlen]
    exact ih hrest _

theorem wiresFrom_length (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]; simp; omega

theorem dual_size {n : ℕ} (f : (Fin n → Bool) → Bool) (hf : ∃ x, f x = true) (s : ℕ)
    (h : HasCircuitSize n f s) : HasCircuitSize n (fun x => !(f (fun i => !x i))) s := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hout : C.output < n + C.gates.length := by
    by_contra hge
    obtain ⟨x0, hx0⟩ := hf
    have he := hev x0
    have hlen : (C.wires (List.ofFn x0)).length = n + C.gates.length := by
      change (wiresFrom C.gates (List.ofFn x0)).length = _
      rw [wiresFrom_length]; simp
    have hdef : C.eval (List.ofFn x0) = false :=
      List.getD_eq_default _ _ (by rw [hlen]; omega)
    rw [hdef] at he
    exact Bool.noConfusion (he.trans hx0)
  refine ⟨⟨dualGates n C.gates, C.output⟩, dualGates_ok n C.gates hfan, ?_, ?_⟩
  · simpa [Circuit.size, dualGates_length] using hsz
  · intro x
    let y : Fin n → Bool := fun i => !x i
    have hxy : List.ofFn x = (List.ofFn y).map (!·) := by
      rw [List.map_ofFn]
      congr 1; funext i; simp [y]
    have hw : (⟨dualGates n C.gates, C.output⟩ : Circuit).wires (List.ofFn x) =
        (C.wires (List.ofFn y)).map (!·) := by
      change wiresFrom (dualGates n C.gates) (List.ofFn x) = (wiresFrom C.gates (List.ofFn y)).map (!·)
      rw [hxy]
      have hdg : dualGates n C.gates = dualGates (List.ofFn y).length C.gates := by simp
      rw [hdg]
      exact dualGates_wires C.gates (fun g hg => (hfan g hg).1) (List.ofFn y)
    have hlen : (C.wires (List.ofFn y)).length = n + C.gates.length := by
      change (wiresFrom C.gates (List.ofFn y)).length = _
      rw [wiresFrom_length]; simp
    change ((⟨dualGates n C.gates, C.output⟩ : Circuit).wires (List.ofFn x)).getD C.output false = !(f y)
    rw [hw, getD_map_not _ _ (by rw [hlen]; exact hout)]
    exact congrArg (!·) (hev y)


end PEqualNP.Outside.L_meta_40007.Base

namespace PEqualNP.Outside.L_meta_40007

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808360 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def project : Fin 6 → Fin 5 := ![0,1,2,3,4,0]
def cut (v : Bool) (x : Fin 5 → Bool) : Bool :=
  target (Function.update (x ∘ project) 5 v)

set_option maxRecDepth 100000 in
theorem falseCut : (fun x : Fin 5 → Bool => !(cut false (fun i => !x i))) =
    (fun x : Fin 5 → Bool => Nat.testBit 0xeaa8a888 (Base.idx5 x)) := by
  funext x
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
theorem trueCut : cut true = (fun x : Fin 5 → Bool => Nat.testBit 0xfeeaeaa8 (Base.idx5 x)) := by
  funext x
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
theorem lower (s : ℕ) (h : HasCircuitSize 6 target s) : 11 ≤ s := by
  have dep : ∃ x : Fin 6 → Bool, target (Function.update x 5 (!x 5)) ≠ target x :=
    ⟨fun i => (28 : ℕ).testBit i.val, by decide +kernel⟩
  have nc : ∀ v : Bool, ∃ x y : Fin 6 → Bool,
      target (Function.update x 5 v) ≠ target (Function.update y 5 v) := by
    intro v
    exact ⟨fun _ => false, fun _ => true, by cases v <;> decide +kernel⟩
  obtain ⟨v,t,ht,hc⟩ := Base.gate_elim_at 5 target 5 s dep nc h
  have hr : HasCircuitSize 5 (cut v) t := Base.relabel_size project _ t hc
  cases v
  · have hd := Base.dual_size (cut false) ⟨fun _ => true, by decide +kernel⟩ t hr
    rw [falseCut] at hd
    have := Base.LowZero.lb t hd
    omega
  · rw [trueCut] at hr
    have := Base.LowOne.lb t hr
    omega

def circuit : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [9, 15]⟩], 16⟩

set_option maxRecDepth 100000 in
theorem correct : ∀ x, circuit.eval (List.ofFn x) = target x := by decide +kernel

theorem basis : Monotone2 circuit := by simp [circuit, Monotone2]

end PEqualNP.Outside.L_meta_40007

theorem PEqualNP.Outside.L_meta_40007 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  exact ⟨PEqualNP.Outside.L_meta_40007.circuit, PEqualNP.Outside.L_meta_40007.basis, PEqualNP.Outside.L_meta_40007.lower s h, PEqualNP.Outside.L_meta_40007.correct⟩
