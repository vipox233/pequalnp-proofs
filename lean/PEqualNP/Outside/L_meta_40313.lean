import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40313_aux.Signed
open PEqualNP.CircuitLowerBounds
def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

end PEqualNP.Outside.L_meta_40313_aux.Signed
namespace PEqualNP.Outside.L_meta_40313_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_40313_aux.Signed (legal isBinary binaryCost)

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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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

theorem simplify_legal (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1.toList, legal g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨Or.inl rfl, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨Or.inr (Or.inl rfl), by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg; exact ⟨Or.inr (Or.inr rfl), by simp⟩
  · simp at hg
  · simp at hg

theorem isBinary_and (l : List ℕ) : isBinary ⟨GateOp.and, l⟩ = true := rfl
theorem isBinary_or (l : List ℕ) : isBinary ⟨GateOp.or, l⟩ = true := rfl
theorem isBinary_not (l : List ℕ) : isBinary ⟨GateOp.not, l⟩ = false := rfl

theorem simplify_binCost_le (op : GateOp) (m : ℕ) (ins : List Stat) :
    binaryCost (simplify op m ins).1.toList ≤ if isBinary ⟨op, []⟩ then 1 else 0 := by
  have hlen : ∀ o : Option Gate, binaryCost o.toList ≤ 1 := by
    intro o
    cases o with
    | none => simp [binaryCost]
    | some g => exact (List.length_filter_le _ _).trans (by simp)
  cases op
  · exact hlen _
  · exact hlen _
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simplify, simpNot, binaryCost, isBinary_not]
  · simp [simplify, binaryCost]
  · simp [simplify, binaryCost]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem binaryCost_append (l1 l2 : List Gate) :
    binaryCost (l1 ++ l2) = binaryCost l1 + binaryCost l2 := by
  simp [binaryCost, List.filter_append]

theorem binaryCost_cons (g : Gate) (gs : List Gate) :
    binaryCost (g :: gs) = (if isBinary g then 1 else 0) + binaryCost gs := by
  simp only [binaryCost, List.filter_cons]
  cases isBinary g <;> simp [Nat.add_comm]

theorem elim_legal (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, legal g) → (∀ g ∈ (elim n gs acc).2, legal g) := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih
    intro g' hg'
    simp only [elimStep, List.mem_append] at hg'
    rcases hg' with hg' | hg'
    · exact h g' hg'
    · exact simplify_legal _ _ _ g' hg'

theorem elim_binCost_le (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    binaryCost (elim n gs acc).2 ≤ binaryCost acc.2 + binaryCost gs := by
  induction gs with
  | nil => intro acc; simp [elim, binaryCost]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + (if isBinary g then 1 else 0) := by
      simp only [elimStep, binaryCost_append]
      have hb := simplify_binCost_le g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      have heq : isBinary ⟨g.op, []⟩ = isBinary g := rfl
      rw [heq] at hb
      omega
    rw [elim_cons, binaryCost_cons]
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
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, legal g) → Inv n y w acc →
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

def AgreeNonConst (st : List Stat) (w1 w2 : List Bool) : Prop :=
  st.length = w1.length ∧ st.length = w2.length ∧
  ∀ i : ℕ, (∃ j : ℕ, st.getD i (Sum.inl false) = Sum.inr j) → w1.getD i false = w2.getD i false

theorem elim_agree_of_eq_binCost (n : ℕ) (gs : List Gate) :
    ∀ (w1 w2 : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, legal g) →
      AgreeNonConst acc.1 w1 w2 →
      binaryCost (elim n gs acc).2 = binaryCost acc.2 + binaryCost gs →
      AgreeNonConst (elim n gs acc).1 (wiresFrom gs w1) (wiresFrom gs w2) := by
  induction gs with
  | nil => intro w1 w2 acc _ hag _; exact hag
  | cons g gs ih =>
    intro w1 w2 acc hok hag heq
    have hstep_le : binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + (if isBinary g then 1 else 0) := by
      simp only [elimStep, binaryCost_append]
      have hb := simplify_binCost_le g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      have heq' : isBinary ⟨g.op, []⟩ = isBinary g := rfl
      rw [heq'] at hb; omega
    have htail_le := elim_binCost_le n gs (elimStep n acc g)
    rw [elim_cons, binaryCost_cons] at heq
    have hstep_eq : binaryCost (elimStep n acc g).2 = binaryCost acc.2 + (if isBinary g then 1 else 0) := by omega
    have htail_eq : binaryCost (elim n gs (elimStep n acc g)).2 = binaryCost (elimStep n acc g).2 + binaryCost gs := by omega
    apply ih (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
             (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])
             (elimStep n acc g)
             (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) _ htail_eq
    obtain ⟨hl1, hl2, hwi⟩ := hag
    refine ⟨by simp [elimStep, hl1], by simp [elimStep, hl2], ?_⟩
    intro i hi
    by_cases hil : i = acc.1.length
    · subst hil
      simp only [elimStep] at hi ⊢
      rw [getD_snoc_eq] at hi
      rw [hl1, getD_snoc_eq, ← hl1, hl2, getD_snoc_eq]
      have hgok := hok g List.mem_cons_self
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hlen⟩ := hgok
      dsimp only [elimStep] at hi hstep_eq
      rw [binaryCost_append] at hstep_eq
      rcases hop with rfl | rfl | rfl
      · rw [isBinary_and] at hstep_eq
        rcases args with _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, l⟩⟩⟩
        · simp [simplify, simpAnd, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpAnd, binaryCost] at hstep_eq
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpAnd, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b <;>
              (rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq;
               simp [simplify, simpAnd, binaryCost] at hstep_eq)
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b
            · rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq
              simp [simplify, simpAnd, binaryCost] at hstep_eq
            · have e1 := hwi k1 ⟨a, h1⟩
              have e2 := hwi k2 ⟨b, h2⟩
              simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 e2 ⊢
              rw [e1, e2]
        · simp at hlen
      · rw [isBinary_or] at hstep_eq
        rcases args with _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, l⟩⟩⟩
        · simp [simplify, simpOr, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpOr, binaryCost] at hstep_eq
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpOr, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b <;>
              (rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq;
               simp [simplify, simpOr, binaryCost] at hstep_eq)
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b
            · rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq
              simp [simplify, simpOr, binaryCost] at hstep_eq
            · have e1 := hwi k1 ⟨a, h1⟩
              have e2 := hwi k2 ⟨b, h2⟩
              simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 e2 ⊢
              rw [e1, e2]
        · simp at hlen
      · rcases args with _ | ⟨k1, l⟩
        · simp [simplify, simpNot] at hi
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, h1] at hi
            simp [simplify, simpNot] at hi
          · have e1 := hwi k1 ⟨a, h1⟩
            simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 ⊢
            rw [e1]
    · simp only [elimStep] at hi ⊢
      rw [getD_snoc_ne _ _ _ _ hil] at hi
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact hwi i hi

def insAt {α : Type} {n : ℕ} (idx : Fin (n + 1)) (v : α) (y : Fin n → α) (k : Fin (n + 1)) : α :=
  if h1 : k.val < idx.val then y ⟨k.val, by omega⟩
  else if h2 : k.val = idx.val then v
  else y ⟨k.val - 1, by omega⟩

end PEqualNP.Outside.L_meta_40313_aux
namespace PEqualNP.Outside.L_meta_40313_aux.TwoPin

abbrev V := Bool × Bool
abbrev P := V × V

def gate (isOr : Bool) (a b : V) : V :=
  if isOr then
    (a.1 || b.1, (a.2 && b.2) || (a.2 && a.1) || (b.2 && b.1))
  else
    (a.1 && b.1, (a.2 && b.2) || (a.2 && !a.1) || (b.2 && !b.1))

def gateP (isOr : Bool) (a b : P) : P :=
  (gate isOr a.1 b.1, gate isOr a.2 b.2)

def ok (spent : Bool) (w : P) : Bool :=
  (w.1.1 == w.2.1) || (if spent then w.1.2 || w.2.2 else w.1.2 && w.2.2)

def losses (a b : P) : Bool × Bool := (a.1.2 || b.1.2, a.2.2 || b.2.2)

theorem local_rule : ∀ (spent isOr : Bool) (a b : P),
    ok spent a → ok spent b →
    ¬ (spent && ((losses a b).1 || (losses a b).2)) →
    ok (spent || ((losses a b).1 && (losses a b).2)) (gateP isOr a b) := by
  decide +kernel

theorem ok_mono : ∀ (w : P), ok false w → ok true w := by decide +kernel

def notP (a : P) : P := ((!a.1.1, a.1.2), (!a.2.1, a.2.2))

theorem ok_not : ∀ (s : Bool) (w : P), ok s (notP w) = ok s w := by decide +kernel

open PEqualNP.CircuitLowerBounds

def view (op : GateOp) (l : List V) : V :=
  match op, l with
  | .not, a :: _ => (!a.1, a.2)
  | .not, [] => (true, true)
  | .and, [a,b] => gate false a b
  | .or, [a,b] => gate true a b
  | .and, [a] | .or, [a] => a
  | .and, [] => (true, true)
  | _, _ => (false, true)

def saved (op : GateOp) (l : List V) : Bool :=
  match op, l with
  | .not, _ => false
  | .and, [a,b] | .or, [a,b] => a.2 || b.2
  | _, _ => true

def switch (s a b : Bool) := s || (a && b)

theorem switch_ok (s a b : Bool) (p : P) (h : ok s p) : ok (switch s a b) p := by
  cases s <;> cases a <;> cases b <;> first | exact h | exact ok_mono p h

theorem view_ok (s : Bool) (op : GateOp) (l : List P)
    (hop : op = .and ∨ op = .or ∨ op = .not) (hl : l.length ≤ 2)
    (hk : ∀ p ∈ l, ok s p)
    (hlim : ¬ (s && (saved op (l.map Prod.fst) || saved op (l.map Prod.snd)))) :
    ok (switch s (saved op (l.map Prod.fst)) (saved op (l.map Prod.snd)))
      (view op (l.map Prod.fst), view op (l.map Prod.snd)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, ls⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> cases s <;> decide
  · have ha := hk a (by simp)
    rcases hop with rfl | rfl | rfl
    · exact switch_ok s true true a ha
    · exact switch_ok s true true a ha
    · change ok (s || (false && false)) (notP a)
      simpa [ok_not] using ha
  · have ha := hk a (by simp)
    have hb := hk b (by simp)
    rcases hop with rfl | rfl | rfl
    · exact local_rule s false a b ha hb hlim
    · exact local_rule s true a b ha hb hlim
    · change ok (s || (false && false)) (notP a)
      simpa [ok_not] using ha
  · simp at hl

end PEqualNP.Outside.L_meta_40313_aux.TwoPin

namespace PEqualNP.Outside.L_meta_40313_aux.TwoPin
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_40313_aux
open PEqualNP.Outside.L_meta_40313_aux.Signed (legal binaryCost isBinary)

def compatible (s : Stat) (v : Bool) : Prop :=
  match s with
  | .inl c => c = v
  | .inr _ => True

def pack (s : Stat) (v : Bool) : V := (v, s.isLeft)

def data (x : Stat × Bool) : V := pack x.1 x.2

theorem implements (op : GateOp) (m : ℕ) (args : List (Stat × Bool))
    (hop : op = .and ∨ op = .or ∨ op = .not) (hlen : args.length ≤ 2)
    (hcomp : ∀ a ∈ args, compatible a.1 a.2) :
    let out := simplify op m (args.map Prod.fst)
    let v := op.eval (args.map Prod.snd)
    compatible out.2 v ∧ pack out.2 v = view op (args.map data) ∧
    binaryCost out.1.toList + (saved op (args.map data)).toNat =
      (isBinary ⟨op, []⟩).toNat := by
  rcases args with _ | ⟨⟨a,x⟩, _ | ⟨⟨b,y⟩, _ | ⟨c, ls⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  · have ha := hcomp (a,x) (by simp)
    rcases hop with rfl | rfl | rfl <;> cases a with
    | inl u => cases u <;> cases x <;> simp_all +decide [compatible, pack, simplify, simpAnd,
        simpOr, simpNot, binaryCost, isBinary, data, view, saved, GateOp.eval]
    | inr j => cases x <;> simp_all +decide [compatible, pack, simplify, simpAnd,
        simpOr, simpNot, binaryCost, isBinary, data, view, saved, GateOp.eval]
  · have ha := hcomp (a,x) (by simp)
    have hb := hcomp (b,y) (by simp)
    rcases hop with rfl | rfl | rfl <;> cases a with
    | inl u => cases b with
      | inl v => cases u <;> cases v <;> cases x <;> cases y <;> simp_all +decide [compatible,
          pack, simplify, simpAnd, simpOr, simpNot, binaryCost, isBinary, data, view, gate, saved, GateOp.eval]
      | inr j => cases u <;> cases x <;> cases y <;> simp_all +decide [compatible,
          pack, simplify, simpAnd, simpOr, simpNot, binaryCost, isBinary, data, view, gate, saved, GateOp.eval]
    | inr k => cases b with
      | inl v => cases v <;> cases x <;> cases y <;> simp_all +decide [compatible,
          pack, simplify, simpAnd, simpOr, simpNot, binaryCost, isBinary, data, view, gate, saved, GateOp.eval]
      | inr j => cases x <;> cases y <;> simp_all +decide [compatible,
          pack, simplify, simpAnd, simpOr, simpNot, binaryCost, isBinary, data, view, gate, saved, GateOp.eval]
          <;> rfl
  · simp at hlen

structure Run where
  st : List Stat
  gs : List Gate
  bits : List Bool

def read (r : Run) (i : ℕ) : Stat × Bool :=
  (r.st.getD i (.inl false), r.bits.getD i false)

def inputs (r : Run) (g : Gate) := g.inputs.map fun i => data (read r i)

def step (n : ℕ) (r : Run) (g : Gate) : Run :=
  let a := elimStep n (r.st,r.gs) g
  ⟨a.1, a.2, r.bits ++ [g.op.eval (g.inputs.map fun i => r.bits.getD i false)]⟩

def valid (r : Run) := r.st.length = r.bits.length ∧ ∀ i, compatible (read r i).1 (read r i).2

theorem step_length (n : ℕ) (r : Run) (g : Gate) :
    (step n r g).st.length = r.st.length + 1 := by simp [step, elimStep]

theorem old_read (n : ℕ) (r : Run) (g : Gate) (v : valid r) (i : ℕ) (h : i ≠ r.st.length) :
    read (step n r g) i = read r i := by
  have h' : i ≠ r.bits.length := by rwa [← v.1]
  apply Prod.ext
  · exact getD_snoc_ne _ _ _ _ h
  · exact getD_snoc_ne _ _ _ _ h'

theorem new_read (n : ℕ) (r : Run) (g : Gate) (v : valid r) :
    read (step n r g) r.st.length =
      ((simplify g.op (n+r.gs.length) (g.inputs.map fun i => (read r i).1)).2,
       g.op.eval (g.inputs.map fun i => (read r i).2)) := by
  have hr := getD_snoc_eq r.bits (g.op.eval (g.inputs.map fun i => r.bits.getD i false)) false
  rw [← v.1] at hr
  exact Prod.ext (getD_snoc_eq _ _ _) hr

theorem step_spec (n : ℕ) (r : Run) (g : Gate) (v : valid r) (hg : legal g) :
    valid (step n r g) ∧
    data (read (step n r g) r.st.length) = view g.op (inputs r g) ∧
    binaryCost (step n r g).gs + (saved g.op (inputs r g)).toNat =
      binaryCost r.gs + (isBinary g).toNat := by
  have hc : ∀ a ∈ g.inputs.map (read r), compatible a.1 a.2 := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 ha
    exact v.2 i
  obtain ⟨hcompat,hview,hcost⟩ := implements g.op (n+r.gs.length) (g.inputs.map (read r))
    hg.1 (by simpa using hg.2) hc
  have hbits : isBinary ⟨g.op, []⟩ = isBinary g := rfl
  simp only [List.map_map, Function.comp_def] at hcompat hview hcost
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [step, elimStep] using v.1
  · intro i
    by_cases hi : i = r.st.length
    · subst i
      rw [new_read n r g v]
      exact hcompat
    · rw [old_read n r g v i hi]
      exact v.2 i
  · rw [new_read n r g v]
    exact hview
  · change binaryCost (r.gs ++ _) + _ = _
    rw [binaryCost_append, Nat.add_assoc]
    exact congrArg (binaryCost r.gs + ·) hcost

def pair (r q : Run) (i : ℕ) : P := (data (read r i), data (read q i))

def common (s : Bool) (r q : Run) : Prop :=
  r.st.length = q.st.length ∧ ∀ i, ok s (pair r q i)

theorem step_common (n : ℕ) (r q : Run) (g : Gate) (s : Bool)
    (v : valid r) (u : valid q) (hg : legal g) (hs : common s r q)
    (hlim : ¬ (s && (saved g.op (inputs r g) || saved g.op (inputs q g)))) :
    common (switch s (saved g.op (inputs r g)) (saved g.op (inputs q g)))
      (step n r g) (step n q g) := by
  refine ⟨by simpa only [step_length, Nat.add_right_cancel_iff] using hs.1, ?_⟩
  intro i
  by_cases hi : i = r.st.length
  · subst i
    have hr := (step_spec n r g v hg).2.1
    have hq := (step_spec n q g u hg).2.1
    rw [← hs.1] at hq
    change ok _ (data _, data _)
    rw [hr,hq]
    have h : ∀ p ∈ g.inputs.map (pair r q), ok s p := by
      intro p hp
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp
      exact hs.2 i
    have z := view_ok s g.op (g.inputs.map (pair r q)) hg.1 (by simpa using hg.2) h
    simp only [List.map_map, Function.comp_def, pair] at z
    exact z hlim
  · have hq : i ≠ q.st.length := by rwa [← hs.1]
    change ok _ (data _, data _)
    rw [old_read n r g v i hi,old_read n q g u i hq]
    exact switch_ok _ _ _ _ (hs.2 i)

def walk (n : ℕ) (gs : List Gate) (r : Run) := gs.foldl (step n) r

theorem walk_cost (n : ℕ) (gs : List Gate) (r : Run) :
    binaryCost (walk n gs r).gs ≤ binaryCost r.gs + binaryCost gs := by
  have he : ((walk n gs r).st, (walk n gs r).gs) = elim n gs (r.st,r.gs) := by
    induction gs generalizing r with
    | nil => rfl
    | cons g gs ih => exact ih (step n r g)
  have h := elim_binCost_le n gs (r.st,r.gs)
  rw [← he] at h
  exact h

theorem two_saved_or_agree (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, legal g)
    (r q : Run) (s : Bool) (budget : ℕ) (v : valid r) (u : valid q)
    (hs : common s r q) (hl : binaryCost r.gs + s.toNat ≤ budget)
    (hr : binaryCost q.gs + s.toNat ≤ budget) :
    binaryCost (walk n gs r).gs + 2 ≤ budget + binaryCost gs ∨
    binaryCost (walk n gs q).gs + 2 ≤ budget + binaryCost gs ∨
    common true (walk n gs r) (walk n gs q) := by
  induction gs generalizing r q s budget with
  | nil =>
    right; right
    refine ⟨hs.1, fun i => ?_⟩
    cases s
    · exact ok_mono _ (hs.2 i)
    · exact hs.2 i
  | cons g gs ih =>
    have hop := hg g (by simp)
    have hx := step_spec n r g v hop
    have hy := step_spec n q g u hop
    let a := saved g.op (inputs r g)
    let b := saved g.op (inputs q g)
    have hl' : binaryCost (step n r g).gs + a.toNat = binaryCost r.gs + (isBinary g).toNat := hx.2.2
    have hr' : binaryCost (step n q g).gs + b.toNat = binaryCost q.gs + (isBinary g).toNat := hy.2.2
    have hsum : binaryCost (g::gs) = (isBinary g).toNat + binaryCost gs := by
      rw [binaryCost_cons]; cases isBinary g <;> rfl
    change binaryCost (walk n gs (step n r g)).gs + 2 ≤ _ ∨
      binaryCost (walk n gs (step n q g)).gs + 2 ≤ _ ∨
      common true (walk n gs (step n r g)) (walk n gs (step n q g))
    rw [hsum]
    by_cases hbig : (s && (a || b)) = true
    · obtain ⟨hs',hab⟩ := Bool.and_eq_true_iff.mp hbig
      rw [hs'] at hl hr
      rcases Bool.or_eq_true_iff.mp hab with ha | hb
      · left
        have hw := walk_cost n gs (step n r g)
        rw [ha] at hl'
        simp only [Bool.toNat_true] at *
        omega
      · right; left
        have hw := walk_cost n gs (step n q g)
        rw [hb] at hr'
        simp only [Bool.toNat_true] at *
        omega
    · have hnext := step_common n r q g s v u hop hs hbig
      have small : ∀ s a b : Bool, (switch s a b).toNat ≤ s.toNat + a.toNat ∧
          (switch s a b).toNat ≤ s.toNat + b.toNat := by decide
      obtain ⟨smL,smR⟩ := small s a b
      have budgetL : binaryCost (step n r g).gs + (switch s a b).toNat ≤ budget + (isBinary g).toNat := by
        omega
      have budgetR : binaryCost (step n q g).gs + (switch s a b).toNat ≤ budget + (isBinary g).toNat := by
        omega
      have z := ih (fun g mem => hg g (List.mem_cons_of_mem _ mem)) (step n r g) (step n q g)
        (switch s a b) (budget + (isBinary g).toNat) hx.1 hy.1 hnext budgetL budgetR
      simpa [Nat.add_assoc] using z

def initialFn {n : ℕ} (i : Fin (n+1)) (b : Bool) : Fin (n+1) → Stat :=
  insAt i (.inl b) (fun j : Fin n => .inr j.val)

def initialSt {n : ℕ} (i : Fin (n+1)) (b : Bool) := List.ofFn (initialFn i b)

def start {n : ℕ} (idx : Fin (n+1)) (b : Bool) (y : Fin n → Bool) : Run :=
  ⟨initialSt idx b, [], List.ofFn (insAt idx b y)⟩

theorem hgetFn {α : Type} {n : ℕ} (f : Fin (n+1) → α) (d : α) (i : ℕ) (hi : i < n+1) :
    (List.ofFn f).getD i d = f ⟨i,hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hi]), Option.getD_some,
    List.getElem_ofFn]

theorem initial_inv {n : ℕ} (idx : Fin (n+1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (insAt idx b y)) (initialSt idx b, []) := by
  refine ⟨by simp [initialSt], ?_⟩
  intro i
  by_cases hi : i < n + 1
  · rw [show (initialSt idx b).getD i (Sum.inl false) = (initialFn idx b) ⟨i, hi⟩ from hgetFn (initialFn idx b) _ i hi,
        hgetFn (insAt idx b y) false i hi]
    dsimp only [initialFn, insAt]
    by_cases h1 : i < idx.val
    · simp only [h1, ↓reduceDIte, statValid, statVal, wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
      refine ⟨by omega, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
        Option.getD_some, List.getElem_ofFn]
    · by_cases h2 : i = idx.val
      · simp [h2, statValid, statVal]
      · simp only [h1, h2, ↓reduceDIte, statValid, statVal, wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
        refine ⟨by omega, ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
          Option.getD_some, List.getElem_ofFn]
  · have h1 : (initialSt idx b).getD i (Sum.inl false) = Sum.inl false :=
      List.getD_eq_default _ _ (by simp [initialSt]; omega)
    have h2 : (List.ofFn (insAt idx b y)).getD i false = false :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [h1, h2]; simp [statValid, statVal]

theorem initial_valid {n : ℕ} (idx : Fin (n+1)) (b : Bool) (y : Fin n → Bool) :
    valid (start idx b y) := by
  have h := initial_inv idx b y
  refine ⟨h.1, fun i => ?_⟩
  have hv := (h.2 i).2
  change compatible ((initialSt idx b).getD i (.inl false)) _
  cases e : (initialSt idx b).getD i (.inl false) with
  | inl c => rw [e] at hv; exact hv
  | inr j => trivial

theorem initial_common {n : ℕ} (idx : Fin (n+1)) (y : Fin n → Bool) :
    common false (start idx false y) (start idx true y) := by
  refine ⟨by simp [start, initialSt], fun i => ?_⟩
  change ok false
    (pack ((List.ofFn (initialFn idx false)).getD i (.inl false)) ((List.ofFn (insAt idx false y)).getD i false),
     pack ((List.ofFn (initialFn idx true)).getD i (.inl false)) ((List.ofFn (insAt idx true y)).getD i false))
  by_cases hi : i < n+1
  · rw [hgetFn _ _ _ hi, hgetFn _ _ _ hi, hgetFn _ _ _ hi, hgetFn _ _ _ hi]
    simp only [initialFn, insAt]
    by_cases h1 : i < idx.val
    · simp [h1, pack, ok]
    · by_cases h2 : i = idx.val <;> simp [h1,h2,pack,ok]
  · have hz {α : Type} (f : Fin (n+1) → α) (d : α) : (List.ofFn f).getD i d = d :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [hz,hz,hz,hz]
    rfl

theorem walk_pair (n : ℕ) (gs : List Gate) (r : Run) :
    ((walk n gs r).st, (walk n gs r).gs) = elim n gs (r.st,r.gs) := by
  induction gs generalizing r with
  | nil => rfl
  | cons g gs ih => exact ih (step n r g)

theorem walk_bits (n : ℕ) (gs : List Gate) (r : Run) :
    (walk n gs r).bits = wiresFrom gs r.bits := by
  induction gs generalizing r with
  | nil => rfl
  | cons g gs ih => exact ih (step n r g)

theorem drop_two {n : ℕ} (idx : Fin (n+1)) (F : (Fin (n+1) → Bool) → Bool)
    (yd : Fin n → Bool) (hd : F (insAt idx false yd) ≠ F (insAt idx true yd))
    (hnc : ∀ b, ∃ y z : Fin n → Bool, F (insAt idx b y) ≠ F (insAt idx b z))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin (n+1) → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    ∃ (b : Bool) (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', legal g) ∧
      binaryCost gs' + 2 ≤ binaryCost gs ∧
      ∀ y : Fin n → Bool, Circuit.eval ⟨gs',o'⟩ (List.ofFn y) = F (insAt idx b y) := by
  let R := fun b => walk n gs (start idx b yd)
  have pairEq (b) : ((R b).st, (R b).gs) = elim n gs (initialSt idx b,[]) := walk_pair _ _ _
  have ev (b) (y : Fin n → Bool) :
      statVal (wiresFrom (R b).gs (List.ofFn y)) ((R b).st.getD o (.inl false)) = F (insAt idx b y) := by
    have t := inv_elim n (List.ofFn y) (by simp) gs (List.ofFn (insAt idx b y)) (initialSt idx b,[])
      hg (initial_inv idx b y)
    rw [← pairEq] at t
    exact (t.2 o).2.trans (he _)
  have out (b) : ∃ k, (R b).st.getD o (.inl false) = .inr k := by
    cases et : (R b).st.getD o (.inl false) with
    | inl c =>
      obtain ⟨y,z,hne⟩ := hnc b
      have hy := ev b y
      have hz := ev b z
      rw [et] at hy hz
      exact (hne (hy.symm.trans hz)).elim
    | inr k => exact ⟨k,rfl⟩
  have hc : ∃ b, binaryCost (R b).gs + 2 ≤ binaryCost gs := by
    have z := two_saved_or_agree n gs hg (start idx false yd) (start idx true yd) false 0
      (initial_valid _ _ _) (initial_valid _ _ _) (initial_common _ _) (Nat.le_refl 0) (Nat.le_refl 0)
    rcases z with l | r | h
    · exact ⟨false, by simpa using l⟩
    · exact ⟨true, by simpa using r⟩
    · obtain ⟨k,hk⟩ := out false
      obtain ⟨j,hj⟩ := out true
      have hv := h.2 o
      change ok true (pack ((R false).st.getD o (.inl false)) ((R false).bits.getD o false),
        pack ((R true).st.getD o (.inl false)) ((R true).bits.getD o false)) = true at hv
      rw [hk,hj] at hv
      have eqbits : (R false).bits.getD o false = (R true).bits.getD o false := by
        simpa [ok,pack] using hv
      have ee (b : Bool) : (R b).bits.getD o false = F (insAt idx b yd) := by
        dsimp only [R]
        rw [walk_bits]
        exact he _
      exact (hd ((ee false).symm.trans (eqbits.trans (ee true)))).elim
  obtain ⟨b,hb⟩ := hc
  obtain ⟨k,hk⟩ := out b
  have hl := elim_legal n gs (initialSt idx b,[]) (by simp)
  rw [← pairEq b] at hl
  refine ⟨b,(R b).gs,k,hl,hb,fun y => ?_⟩
  have e := ev b y
  rw [hk] at e
  exact e

end PEqualNP.Outside.L_meta_40313_aux.TwoPin

namespace PEqualNP.Outside.L_meta_40313_aux.Relabel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem at_last {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp [List.getD_append_right]

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
    rw [he, hw, at_last, at_last]
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

theorem renamed (C : Circuit) (fit : FanInTwo C) (π : Fin 5 → Fin 5) :
    ∃ D : Circuit, D.gates.length = C.gates.length ∧ FanInTwo D ∧
      (∀ x : Fin 5 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π))) ∧
      ∀ paid : GateOp → Bool, D.gates.countP (fun g => paid g.op) =
        C.gates.countP (fun g => paid g.op) := by
  refine ⟨relabel 5 5 π C, by simp [relabel], ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop,hlen⟩ := fit h hh
    exact ⟨hop, by simpa [relGate] using hlen⟩
  · intro x
    exact (rel_fold 5 5 π C.gates _ _ (rel_init 5 5 π x)).2.2 C.output
  · intro paid
    simp [relabel, List.countP_map, Function.comp_def, relGate]

end PEqualNP.Outside.L_meta_40313_aux.Relabel

namespace PEqualNP.Outside.L_meta_40313_aux.Donor0

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 64

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 32 := ((x >>> 32) ^^^ x).setWidth 32
def cuts (ws : List W) : BitVec 32 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 32) ++ (0 : BitVec 32)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 32) (w : W) : Prop :=
  w.getLsbD (32+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 32) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 32+i.val < 64 := by omega
  have hi' : i.val < 64 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 32) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 32)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def targetFun (T : ℕ) (x : Fin 5 → Bool) : Bool :=
  Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (T : ℕ) (inputs : List W) (width : inputs.length = 5)
    (nd : inputs.Nodup) (reject : search 7 inputs = false)
    (sample : ∀ k : Fin 64,
      targetFun T (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun T x) :
    7 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 5) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 7 inputs nd (lift low run)))

def rows : List W := [0x510e10b5fb1e31ff,0x6962c65c05e3ce7c,0x8e016b0afe03ff8f,0xb6b40de007fc0ff0,0xc7dbb00007fff000]
def target (x : Fin 6 → Bool) : Bool := Nat.testBit 0xeeeaeaaaeee0e8a0 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def firstTest (i : Fin 10) : Bool :=
  let p := (pairs rows).getD i.val (0,0,[])
  dispatch 3 (optimized 6) p.1 p.2.1 p.2.2

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem full_search_of (pairsNo : ∀ i : Fin 10, firstTest i = false) : search 7 rows = false := by
  have sufficient : ∀ ws ∈ rows.sublists, cuts ws = -1 → ws = rows := by decide +kernel
  cases h : search 7 rows with
  | false => rfl
  | true =>
    obtain ⟨ws,hw,hyes⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hyes
    have eq := sufficient ws hw hyes.1.2
    subst ws
    have possible := hyes.2
    change optimized 7 3 rows = true at possible
    have first : (rows == [goal] || rows == [~~~goal]) = false := by decide +kernel
    rw [optimized, first, Bool.false_or] at possible
    obtain ⟨p,hp,htrue⟩ := List.any_eq_true.mp possible
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
    have bound : (pairs rows).length = 10 := by decide +kernel
    have hn := pairsNo ⟨i, by omega⟩
    simp only [firstTest, List.getD_eq_getElem _ _ hi, he] at hn
    cases p with
    | mk a rest =>
      cases rest with
      | mk b r => exact Bool.noConfusion (hn.symm.trans htrue)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_0 : firstTest 0 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_1 : firstTest 1 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_2 : firstTest 2 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_3 : firstTest 3 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_4 : firstTest 4 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_5 : firstTest 5 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_6 : firstTest 6 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_7 : firstTest 7 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_8 : firstTest 8 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_9 : firstTest 9 = false := by decide +kernel
theorem rejects : search 7 rows = false := full_search_of (by
  intro i
  fin_cases i
  · exact first_0
  · exact first_1
  · exact first_2
  · exact first_3
  · exact first_4
  · exact first_5
  · exact first_6
  · exact first_7
  · exact first_8
  · exact first_9)

def cofactor (x : Fin 5 → Bool) : Bool := targetFun 4007717024 x

theorem cofactor_bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = cofactor x) :
    7 < binaryCost gs :=
  bound_from_search 4007717024 rows rfl (by decide +kernel) rejects
    (by decide +kernel) gs o hg he

set_option maxRecDepth 100000 in
theorem compile_positive (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def dualTable (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 4209571976 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def dualRows : List W := [~~~(0x510e10b5fb1e31ff : W), ~~~(0x6962c65c05e3ce7c : W), ~~~(0x8e016b0afe03ff8f : W), ~~~(0xb6b40de007fc0ff0 : W), ~~~(0xc7dbb00007fff000 : W)]

set_option maxRecDepth 32000 in
theorem dual_lower (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = dualTable x) :
    7 < binaryCost gs := by
  by_contra h
  have init : ∀ u ∈ dualRows, holds rows.toFinset u := by
    intro u hu
    simp only [dualRows, List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact .inr (.inr ⟨0x510e10b5fb1e31ff, by decide +kernel, .inr rfl⟩)
    · exact .inr (.inr ⟨0x6962c65c05e3ce7c, by decide +kernel, .inr rfl⟩)
    · exact .inr (.inr ⟨0x8e016b0afe03ff8f, by decide +kernel, .inr rfl⟩)
    · exact .inr (.inr ⟨0xb6b40de007fc0ff0, by decide +kernel, .inr rfl⟩)
    · exact .inr (.inr ⟨0xc7dbb00007fff000, by decide +kernel, .inr rfl⟩)
  have same : ∀ k : Fin 64,
      List.ofFn (fun i : Fin 5 => bit k (dualRows.getD i.val 0)) = dualRows.map (bit k) := by
    decide +kernel
  have sample : ∀ k : Fin 64,
      dualTable (fun i : Fin 5 => bit k (dualRows.getD i.val 0)) = bit k goal := by
    decide +kernel
  have valid (k : Fin 64) :
      (gs.foldl step (dualRows.map (bit k))).getD o false = bit k goal := by
    change Circuit.eval ⟨gs,o⟩ (dualRows.map (bit k)) = bit k goal
    rw [← same k, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile_positive gs o hg dualRows rows.toFinset init valid
  have lift {a c : ℕ} (le : a ≤ c) (hr : build basicOps t a rows.toFinset) :
      build basicOps t c rows.toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (rejects.symm.trans
    (search_complete ht 7 rows (by decide +kernel) (lift (Nat.le_of_not_lt h) run)))

end PEqualNP.Outside.L_meta_40313_aux.Donor0

namespace PEqualNP.Outside.L_meta_40313_aux.Donor1

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 64

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 32 := ((x >>> 32) ^^^ x).setWidth 32
def cuts (ws : List W) : BitVec 32 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 32) ++ (0 : BitVec 32)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 32) (w : W) : Prop :=
  w.getLsbD (32+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 32) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 32+i.val < 64 := by omega
  have hi' : i.val < 64 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 32) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 32)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def targetFun (T : ℕ) (x : Fin 5 → Bool) : Bool :=
  Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (T : ℕ) (inputs : List W) (width : inputs.length = 5)
    (nd : inputs.Nodup) (reject : search 7 inputs = false)
    (sample : ∀ k : Fin 64,
      targetFun T (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun T x) :
    7 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 5) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 7 inputs nd (lift low run)))

def rows : List W := [0x4a166e1bfe3ffe3f,0xd6cb16c53fcf1fc7,0xa561a16efff1e3ff,0x7bbe03b0c1fe03f8,0xbdfdd80001fffc00]
def target (x : Fin 6 → Bool) : Bool := Nat.testBit 0xeee8eae8eee0e8e0 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def firstTest (i : Fin 10) : Bool :=
  let p := (pairs rows).getD i.val (0,0,[])
  dispatch 3 (optimized 6) p.1 p.2.1 p.2.2

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem full_search_of (pairsNo : ∀ i : Fin 10, firstTest i = false) : search 7 rows = false := by
  have sufficient : ∀ ws ∈ rows.sublists, cuts ws = -1 → ws = rows := by decide +kernel
  cases h : search 7 rows with
  | false => rfl
  | true =>
    obtain ⟨ws,hw,hyes⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hyes
    have eq := sufficient ws hw hyes.1.2
    subst ws
    have possible := hyes.2
    change optimized 7 3 rows = true at possible
    have first : (rows == [goal] || rows == [~~~goal]) = false := by decide +kernel
    rw [optimized, first, Bool.false_or] at possible
    obtain ⟨p,hp,htrue⟩ := List.any_eq_true.mp possible
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
    have bound : (pairs rows).length = 10 := by decide +kernel
    have hn := pairsNo ⟨i, by omega⟩
    simp only [firstTest, List.getD_eq_getElem _ _ hi, he] at hn
    cases p with
    | mk a rest =>
      cases rest with
      | mk b r => exact Bool.noConfusion (hn.symm.trans htrue)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_0 : firstTest 0 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_1 : firstTest 1 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_2 : firstTest 2 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_3 : firstTest 3 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_4 : firstTest 4 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_5 : firstTest 5 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_6 : firstTest 6 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_7 : firstTest 7 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_8 : firstTest 8 = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
theorem first_9 : firstTest 9 = false := by decide +kernel
theorem rejects : search 7 rows = false := full_search_of (by
  intro i
  fin_cases i
  · exact first_0
  · exact first_1
  · exact first_2
  · exact first_3
  · exact first_4
  · exact first_5
  · exact first_6
  · exact first_7
  · exact first_8
  · exact first_9)

def cofactor (x : Fin 5 → Bool) : Bool := targetFun 3903381632 x

theorem cofactor_bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = cofactor x) :
    7 < binaryCost gs :=
  bound_from_search 3903381632 rows rfl (by decide +kernel) rejects
    (by decide +kernel) gs o hg he

set_option maxRecDepth 100000 in
theorem compile_positive (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def dualTable (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 4277725928 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def dualRows : List W := [~~~(0x4a166e1bfe3ffe3f : W), ~~~(0xd6cb16c53fcf1fc7 : W), ~~~(0xa561a16efff1e3ff : W), ~~~(0x7bbe03b0c1fe03f8 : W), ~~~(0xbdfdd80001fffc00 : W)]

set_option maxRecDepth 32000 in
theorem dual_lower (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = dualTable x) :
    7 < binaryCost gs := by
  by_contra h
  have init : ∀ u ∈ dualRows, holds rows.toFinset u := by
    intro u hu
    simp only [dualRows, List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact .inr (.inr ⟨0x4a166e1bfe3ffe3f, by decide +kernel, .inr rfl⟩)
    · exact .inr (.inr ⟨0xd6cb16c53fcf1fc7, by decide +kernel, .inr rfl⟩)
    · exact .inr (.inr ⟨0xa561a16efff1e3ff, by decide +kernel, .inr rfl⟩)
    · exact .inr (.inr ⟨0x7bbe03b0c1fe03f8, by decide +kernel, .inr rfl⟩)
    · exact .inr (.inr ⟨0xbdfdd80001fffc00, by decide +kernel, .inr rfl⟩)
  have same : ∀ k : Fin 64,
      List.ofFn (fun i : Fin 5 => bit k (dualRows.getD i.val 0)) = dualRows.map (bit k) := by
    decide +kernel
  have sample : ∀ k : Fin 64,
      dualTable (fun i : Fin 5 => bit k (dualRows.getD i.val 0)) = bit k goal := by
    decide +kernel
  have valid (k : Fin 64) :
      (gs.foldl step (dualRows.map (bit k))).getD o false = bit k goal := by
    change Circuit.eval ⟨gs,o⟩ (dualRows.map (bit k)) = bit k goal
    rw [← same k, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile_positive gs o hg dualRows rows.toFinset init valid
  have lift {a c : ℕ} (le : a ≤ c) (hr : build basicOps t a rows.toFinset) :
      build basicOps t c rows.toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (rejects.symm.trans
    (search_complete ht 7 rows (by decide +kernel) (lift (Nat.le_of_not_lt h) run)))

end PEqualNP.Outside.L_meta_40313_aux.Donor1

namespace PEqualNP.Outside.L_meta_40313_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open Signed (legal isBinary binaryCost)

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808936 * 2 ^ 32 + 4272614528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def order0 : Fin 5 → Fin 5 := ![0, 3, 4, 2, 1]
set_option maxRecDepth 16000 in
theorem restrict0 : ∀ x : Fin 5 → Bool,
    target (insAt (5 : Fin 6) false (x ∘ order0)) = Donor0.dualTable x := by decide +kernel

theorem bound0 (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target (insAt 5 false x)) :
    8 ≤ binaryCost gs := by
  obtain ⟨D, _, hD, ev, counted⟩ := Relabel.renamed ⟨gs,o⟩ hg order0
  let paid : GateOp → Bool := fun op => match op with | .not => false | _ => true
  have eqcost : binaryCost D.gates = binaryCost gs := by
    have hp : (fun g : Gate => paid g.op) = isBinary := by
      funext g; obtain ⟨op,ins⟩ := g; cases op <;> rfl
    simpa only [List.countP_eq_length_filter, hp, binaryCost] using counted paid
  have lb := Donor0.dual_lower D.gates D.output (fun g mem => hD g mem)
    (fun x => (ev x).trans ((he (x ∘ order0)).trans (restrict0 x)))
  change 7 < binaryCost D.gates at lb
  omega

def order1 : Fin 5 → Fin 5 := ![0, 2, 1, 4, 3]
set_option maxRecDepth 16000 in
theorem restrict1 : ∀ x : Fin 5 → Bool,
    target (insAt (5 : Fin 6) true (x ∘ order1)) = Donor1.dualTable x := by decide +kernel

theorem bound1 (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target (insAt 5 true x)) :
    8 ≤ binaryCost gs := by
  obtain ⟨D, _, hD, ev, counted⟩ := Relabel.renamed ⟨gs,o⟩ hg order1
  let paid : GateOp → Bool := fun op => match op with | .not => false | _ => true
  have eqcost : binaryCost D.gates = binaryCost gs := by
    have hp : (fun g : Gate => paid g.op) = isBinary := by
      funext g; obtain ⟨op,ins⟩ := g; cases op <;> rfl
    simpa only [List.countP_eq_length_filter, hp, binaryCost] using counted paid
  have lb := Donor1.dual_lower D.gates D.output (fun g mem => hD g mem)
    (fun x => (ev x).trans ((he (x ∘ order1)).trans (restrict1 x)))
  change 7 < binaryCost D.gates at lb
  omega

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [3, 13]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [8, 15]⟩], 16⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

set_option maxRecDepth 16000 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem solve (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨⟨gs, o⟩, fits, size, computes⟩ := h
  by_cases hasNot : ∃ g ∈ gs, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost gs < gs.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    obtain ⟨b,small,j,valid,delta,ev⟩ := TwoPin.drop_two (5 : Fin 6) target
      (fun i => (3 : ℕ).testBit i.val) (by decide +kernel)
      (by intro p; refine ⟨fun _ => false, fun _ => true, ?_⟩; cases p <;> decide +kernel)
      gs o (fun g mem => fits g mem) computes
    have lb : 8 ≤ binaryCost small := by
      cases b
      · exact bound0 small j valid ev
      · exact bound1 small j valid ev
    have hws : witness.size = 11 := rfl
    change gs.length ≤ s at size
    exact ⟨witness, witness_mono, by omega, witness_eval⟩
  · refine ⟨⟨gs, o⟩, ?_, size, computes⟩
    intro g hg
    obtain ⟨ops, cap⟩ := fits g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at ops
    exact ⟨ops.elim Or.inl (fun h => h.elim Or.inr (fun op => (hasNot ⟨g, hg, op⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_40313_aux

theorem PEqualNP.Outside.L_meta_40313 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4272614528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4272614528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40313_aux.solve
