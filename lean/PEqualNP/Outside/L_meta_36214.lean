import Mathlib.Data.Tree.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36214

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The certificate checker, the restriction lemma and the relabeling below are taken from the merged proof of
-- L-meta-11082 by MartinMatoJames, which names its own sources in the next two lines. The certificate itself
-- (the table of unreachable live-wire states and its symmetry hints) and the circuit are new, found by our own search.
-- The six-input certificate and its checker are from L-meta-9553 in this repository.
-- The one-gate restriction and wire relabeling are from L-meta-9479, following L-meta-927.

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

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

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

def BT := BinaryTree (List ℕ)

def BT.lf : BT := BinaryTree.nil

def BT.nd (l : BT) (k : List ℕ) (r : BT) : BT := BinaryTree.node k l r

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
  | .nil, _ => false
  | .node k l r, x => leqL x k || (if ltL x k then BT.mem l x else BT.mem r x)

def BT.toList : BT → List (List ℕ)
  | .nil => []
  | .node k l r => BT.toList l ++ k :: BT.toList r

theorem BT.mem_toList : ∀ (T : BT) (x : List ℕ), T.mem x = true → x ∈ T.toList
  | .nil, x, h => by simp [BT.mem] at h
  | .node k l r, x, hm => by
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


def accD (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: t => Nat.lor (Nat.xor w (Nat.shiftRight w d)) (accD d t)


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

def L_ : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def M_ : ℕ := 18446744073709551615
def Y_ : ℕ := 18369895808705032384
def XS_ : List ℕ := [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320]
def PD_ : List (ℕ × ℕ) := [(1,115272371734743200),(2,96058089282718960),(3,86454280945757912),(4,72080986327760844),(5,79249773285775174),(6,78040051253494531),(7,77448624894732577),(8,4525667541728304),(9,4940748020750008),(10,4856913383867388),(11,4828194529290590),(12,303496620612623),(13,296452224648871),(14,282931330223091),(15,289399377825113),(16,4423885786636),(17,6182667849638),(18,5855121952627),(19,5725754617625),(20,5523619610412),(21,5633002420022),(22,1182276211515),(23,1190296887613),(24,94761261118),(25,101094360255),(26,99949366015),(27,99372740063),(28,30335524431),(29,30228031367),(30,12976593763),(31,4346414353),(32,2230824),(33,29068724),(34,24596090),(35,17903517),(36,19013486),(37,20678423),(38,20400939),(39,20000053),(40,3284538),(41,3377085),(42,3361662),(43,1256735),(44,204335),(45,198583),(46,199547),(47,68893),(48,3630),(49,4023),(50,3963),(51,3869),(52,3886),(53,1847),(54,827),(55,317),(56,62),(57,63),(58,63),(59,31),(60,15),(61,7),(62,3),(63,1)]
def PM_ : List (ℕ × ℕ) := [(0,18369895808705032384),(1,18369895808705032384),(2,18369895808705032384),(3,18369895808705032384),(4,18369895808705032384),(5,18369895808705032384),(8,18369895808705032384),(9,18369895808705032384),(10,18369895808705032384),(11,18369895808705032384),(16,18369895808705032384),(17,18369895808705032384),(20,18369895808705032384),(21,18369895808705032384),(24,18369895808705032384),(32,18369895808705032384),(33,18369895808705032384),(34,18369895808705032384),(36,18369895808705032384),(40,18369895808705032384),(42,18369895808705032384),(48,18369895808705032384),(52,18369895808705032384),(56,18369895808705032384)]
def G_ : List (List ℕ) := [[0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31,32,33,36,37,34,35,38,39,48,49,52,53,50,51,54,55,40,41,44,45,42,43,46,47,56,57,60,61,58,59,62,63]]

noncomputable def T_cert : BT := (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [2,12297829379609722880,18360329937284300492,18446727516610621680] BT.lf) [2,17207390840222969548,18062524867600773120,18446727516610621680] BT.lf) [2,17216886072605147136,18374388447579140336,18432388630850633676] (BT.nd (BT.nd BT.lf [3,12249977906276641280,12297829379609722880,18216212550151634124,18446727516610621680] BT.lf) [3,12249977906276641280,14757395258967641292,18062524867600773120,18446727516610621680] BT.lf)) [3,12297829379609722880,12297829382473034410,18360329937284300492,18446727516610621680] (BT.nd (BT.nd (BT.nd BT.lf [3,12297829379609722880,14757170082422194176,18085032171453214960,18432388630850633676] BT.lf) [3,12297829379609722880,14757395258967641292,18014673391583296000,18446727516610621680] BT.lf) [3,12297829379609722880,14757395258967641292,18070969245931993800,18446727516610621680] (BT.nd (BT.nd BT.lf [3,12297829379609722880,14757395258967641292,18302908165848628736,18446727516610621680] BT.lf) [3,12297829379609722880,14757395258967641292,18360329937284300492,18446727516610621680] BT.lf))) [3,12297829379609722880,14757395258967641292,18374388447579140336,18374966859414961920] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,12297829379609722880,14757395258967641292,18374388447579140336,18432388630850633676] BT.lf) [3,12297829379609722880,17216698429492559872,18374388447579140336,18432388630850633676] BT.lf) [3,12297829379609722880,17216961135462248174,18374388447579140336,18432388630850633676] (BT.nd (BT.nd BT.lf [3,12297829379609722880,18360329937284300492,18374966859414961920,18446727516610621680] BT.lf) [3,12297829379609722880,18360329937284300492,18446462603027742720,18446727516610621680] BT.lf)) [3,12297829379609722880,18360329937284300492,18446727516610621680] (BT.nd (BT.nd (BT.nd BT.lf [3,12297829379609722880,18360329937284300492,18446727516610621680,18446744069414584320] BT.lf) [3,12297829379609722880,18374403900871474942,18432388630850633676,18446727516610621680] BT.lf) [3,12297829382473034410,17216961131453612032,18374388447579140336,18432388630850633676] (BT.nd BT.lf [3,12297829382473034410,18360329937284300492,18446727516610621680,18446744069414584320] BT.lf)))) [3,14757395258967641292,17216886072605147136,18374388447579140336,18374966859414961920] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [3,14757395258967641292,17216886076041068544,18085032171453214960,18374966859414961920] BT.lf) [3,14757395258967641292,18014673391583296000,18062524863574179840,18446727516610621680] BT.lf) [3,17216886076613765802,18374388447579140336,18432388630850633676,18446744069414584320] (BT.nd (BT.nd BT.lf [4,12249977906276641280,12297829379609722880,14757395258967641292,17294086455919964160,18446727516610621680] BT.lf) [4,12249977906276641280,12297829379609722880,17361641481138401520,18216212550151634124,18446462603027742720] BT.lf)) [4,12249977906276641280,12297829382473034410,18216212550151634124,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [4,12249977906276641280,14757395258967641292,17361641481138401520,18062524867600773120,18446462603027742720] BT.lf) [4,12297829379609722880,12297829382473034410,14757395258967641292,18014673391583296000,18446727516610621680] BT.lf) [4,12297829379609722880,12297829382473034410,14757395258967641292,18374388447579140336,18374966859414961920] (BT.nd (BT.nd BT.lf [4,12297829379609722880,12297829382473034410,18216212550151634124,18374966859414961920,18446727516610621680] BT.lf) [4,12297829379609722880,12297829382473034410,18229723555195321596,18432388630850633676,18446727516610621680] BT.lf))) [4,12297829379609722880,14757170082422194176,14757395258967641292,18085032171453214960,18374966859414961920] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,12297829379609722880,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920] BT.lf) [4,12297829379609722880,14757395258967641292,17216698429492559872,17361641481138401520,18432388630850633676] BT.lf) [4,12297829379609722880,14757395258967641292,17216698429492559872,18374388447579140336,18374966859414961920] (BT.nd (BT.nd BT.lf [4,12297829379609722880,14757395258967641292,17216945682169913568,17361641481138401520,18374966859414961920] BT.lf) [4,12297829379609722880,14757395258967641292,17216961135462248174,18374388447579140336,18374966859414961920] BT.lf)) [4,12297829379609722880,14757395258967641292,17361641481138401520,18302908165848628736,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [4,12297829379609722880,14757395258967641292,17361641481138401520,18360329937284300492,18446462603027742720] BT.lf) [4,12297829379609722880,14757395258967641292,18014673391583296000,18085043209519168250,18446727516610621680] BT.lf) [4,12297829379609722880,14757395258967641292,18014673391583296000,18374966859414961920,18446727516610621680] (BT.nd BT.lf [4,12297829379609722880,14757395258967641292,18014673391583296000,18446462603027742720,18446727516610621680] BT.lf))))) [4,12297829379609722880,14757395258967641292,18014673391583296000,18446727516610621680] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,12297829379609722880,14757395258967641292,18014673391583296000,18446727516610621680,18446744069414584320] BT.lf) [4,12297829379609722880,14757395258967641292,18062524867779689130,18374966859414961920,18446727516610621680] BT.lf) [4,12297829379609722880,14757395258967641292,18082217421685453040,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [4,12297829379609722880,14757395258967641292,18082228416801733360,18374966859414961920,18446727516610621680] BT.lf) [4,12297829379609722880,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720] BT.lf)) [4,12297829379609722880,14757395258967641292,18085032171453214960,18374966859414961920,18446650250148904960] (BT.nd (BT.nd (BT.nd BT.lf [4,12297829379609722880,14757395258967641292,18085032171453214960,18374966859414961920,18446727516610621680] BT.lf) [4,12297829379609722880,14757395258967641292,18085032171453214960,18432388630850633676,18446462603027742720] BT.lf) [4,12297829379609722880,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680] (BT.nd (BT.nd BT.lf [4,12297829379609722880,14757395258967641292,18085043209519168250,18432388630850633676,18446727516610621680] BT.lf) [4,12297829379609722880,14757395258967641292,18374388447579140336,18374966859414961920] BT.lf))) [4,12297829379609722880,14757395258967641292,18374388447579140336,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,12297829379609722880,14757395258967641292,18374388447579140336,18374966859414961920,18446744069414584320] BT.lf) [4,12297829379609722880,14757395258967641292,18374403900871474942,18374966859414961920,18446727516610621680] BT.lf) [4,12297829382461849600,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [4,12297829382461849600,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680] BT.lf) [4,12297829382461890560,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf)) [4,12297829382461890560,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680] (BT.nd (BT.nd (BT.nd BT.lf [4,12297829382473034410,14757170082422194176,18085032171453214960,18432388630850633676,18446744069414584320] BT.lf) [4,12297829382473034410,14757395258967641292,17216961131453612032,18374388447579140336,18374966859414961920] BT.lf) [4,12297829382473034410,14757395258967641292,18014673391583296000,18085043205308416000,18446727516610621680] (BT.nd BT.lf [4,12297829382473034410,14757395258967641292,18014673391583296000,18446727516610621680,18446744069414584320] BT.lf)))) [4,12297829382473034410,14757395258967641292,18062524867600773120,18374966859414961920,18446727516610621680] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,12297829382473034410,14757395258967641292,18070969245931993800,18446727516610621680,18446744069414584320] BT.lf) [4,12297829382473034410,14757395258967641292,18302908165848628736,18446727516610621680,18446744069414584320] BT.lf) [4,12297829382473034410,14757395258967641292,18360329937284300492,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [4,12297829382473034410,14757395258967641292,18374388447579140336,18374966859414961920,18446744069414584320] BT.lf) [4,12297829382473034410,14757395258967641292,18374388447579140336,18432388630850633676,18446744069414584320] BT.lf)) [4,12297829382473034410,17216698429492559872,18374388447579140336,18432388630850633676,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [4,12297829382473034410,17216961135462248174,18374388447579140336,18432388630850633676,18446744069414584320] BT.lf) [4,12297829382473034410,18216212550151634124,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [4,12297829382473034410,18216212550151634124,18374966859414961920,18446727516610621680,18446744073441177600] (BT.nd (BT.nd BT.lf [4,12297829382473034410,18216212550151634124,18432388630850633676,18446727516610621680,18446744069414584320] BT.lf) [4,12297829382473034410,18229723555195321596,18432388579311026112,18446727516610621680,18446744069414584320] BT.lf))) [4,12297829382473034410,18229723555195321596,18432388630850633676,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,12297829382473034410,18360329937284300492,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [4,12297829382473034410,18360329937284300492,18446462603027742720,18446727516610621680,18446744069414584320] BT.lf) [4,12297829382473034410,18360329937284300492,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [4,12297829382473034410,18374403900871474942,18432388630850633676,18446727516610621680,18446744069414584320] BT.lf) [4,14757395258967641292,17216698429492559872,17216886072605147136,17361641481138401520,18374966859414961920] BT.lf)) [4,14757395258967641292,17216886076613765802,18374388447579140336,18374966859414961920,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [4,14757395258967641292,17216961131453612032,18085043209519168250,18374966859414961920,18446727516610621680] BT.lf) [4,14757395258967641292,18014673391583296000,18062524867779689130,18446727516610621680,18446744069414584320] BT.lf) [4,14757395258967641292,18062524863574179840,18062524867779689130,18374966859414961920,18446727516610621680] (BT.nd BT.lf [4,14757395258967641292,18062524867779689130,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf)))))) [4,14757395258967641292,18062524867779689130,18374966859414961920,18446727516610621680,18446744073441177600] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [4,14757395258967641292,18062524867779689130,18432388630850633676,18446727516610621680,18446744069414584320] BT.lf) [4,14757395258967641292,18080539541171272426,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [4,14757395258967641292,18080539541171272426,18432388630850633676,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [4,14757395258967641292,18085043209519168250,18374966859414961920,18422818331321958400,18446727516610621680] BT.lf) [4,17216886076613765802,18229710309516177648,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf)) [4,17216961135462248174,18085043209519168250,18432388630850633676,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,2863311530,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,72057589742960640,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,723401728380766730,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [5,768438411859724970,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,868082074056920076,12297829382473034410,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf))) [5,922126094231669964,12297829382473034410,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,1085086035472220160,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920] BT.lf) [5,1085086035472220160,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [5,1085086035472220160,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446744069414584320] (BT.nd (BT.nd BT.lf [5,1085086039514480640,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [5,1152640029898506240,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf)) [5,1152657617521213440,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [5,3038287259199220266,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,4539697694678990592,12297829382473034410,14757395258967641292,17361641481138401520,18446462603027742720,18446744069414584320] BT.lf) [5,4557430887737720832,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd BT.lf [5,4919131752989213764,12297829382473034410,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf)))) [5,4957412933946328268,12297829382473034410,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,6872211557990727680,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [5,12249790989299875840,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12249977906276641280,12297829379609722880,14757395258967641292,17294086455919964160,17361641481138401520,18446462603027742720] (BT.nd (BT.nd BT.lf [5,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680] BT.lf)) [5,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18422818335600213760,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [5,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720] BT.lf) [5,12249977906276641280,12297829379609722880,17207390840222969548,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12249977906276641280,12297829382473034410,14757395258967641292,17294086455919964160,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12249977906276641280,12297829382473034410,17361641481138401520,18216212550151634124,18446462603027742720,18446744069414584320] BT.lf) [5,12288259087233755784,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf))) [5,12288259087233755784,12297829379609722880,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12288259087233755784,17216961135462248174,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [5,12295014589755599520,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297828652328593920,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [5,12297829379609722880,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829379609722880,12297829382473034410,14757170082422194176,17361641481138401520,18432388630850633676,18446462603027742720] BT.lf)) [5,12297829379609722880,12297829382473034410,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446612720724672512] BT.lf) [5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446639212082954240] (BT.nd BT.lf [5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446639212082995360] BT.lf))))) [5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446649520004464640] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446674533894045888] BT.lf) [5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818470400] BT.lf) [5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610560000] (BT.nd (BT.nd BT.lf [5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680] BT.lf) [5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446727516610621680] BT.lf)) [5,12297829379609722880,12297829382473034410,14757395258967641292,17940362863708270832,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829379609722880,12297829382473034410,14757395258967641292,18082228416633958640,18374966859414961920,18446462603027742720] BT.lf) [5,12297829379609722880,12297829382473034410,14757395258967641292,18085032171284787440,18374966859414961920,18446462603027742720] BT.lf) [5,12297829379609722880,12297829382473034410,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [5,12297829379609722880,12297829382473034410,14757395258967641292,18085043209350738160,18374966859414961920,18446727516610621680] BT.lf) [5,12297829379609722880,12297829382473034410,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680] BT.lf))) [5,12297829379609722880,12297829382473034410,14757395258967641292,18229710309516177648,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829379609722880,12297829382473034410,14757395258967641292,18229723555195321596,18374966859414961920,18446727516610621680] BT.lf) [5,12297829379609722880,12297923206033637375,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829379609722880,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [5,12297829379609722880,14757395258967641292,17149969068787297792,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829379609722880,14757395258967641292,17197820544983690922,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf)) [5,12297829379609722880,14757395258967641292,17207390840222969548,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829379609722880,14757395258967641292,17216698429492559872,17216961135462248174,17361641481138401520,18374966859414961920] BT.lf) [5,12297829379609722880,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920] BT.lf) [5,12297829379609722880,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd BT.lf [5,12297829379609722880,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf)))) [5,12297829379609722880,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829379609722880,14757395258967641292,17216923606038006988,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829379609722880,14757395258967641292,17216961134316923562,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829379609722880,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [5,12297829379609722880,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446727516610621680] BT.lf) [5,12297829379609722880,14757395258967641292,17216961135462248174,17361641481138401520,18432388630850633676,18446462603027742720] BT.lf)) [5,12297829379609722880,14757395258967641292,17361641481138401520,18374403900871474942,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829379609722880,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720] BT.lf) [5,12297829379609722880,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829379609722880,14757395258967641292,18085043209519168250,18374966859414961920,18446462603027742720,18446727516610621680] (BT.nd BT.lf [5,12297829379609722880,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680] BT.lf))) [5,12297829379609722880,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829379778152970,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829381765628032,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829381900337152,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [5,12297829382461849600,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829382461849600,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720] BT.lf)) [5,12297829382461849600,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382461849600,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382461849600,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692774400] BT.lf) [5,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd BT.lf [5,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073456906480] BT.lf))))))) [5,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073709486080] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382461893120,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382470806152,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382470806152,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382472379040,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [5,12297829382473034240,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,12297923203170304000,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829382473034410,12659337080509235200,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [5,12297829382473034410,12659530243715891200,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757170082422194176,14757395258967641292,18085032171453214960,18374966859414961920,18446744069414584320] BT.lf) [5,12297829382473034410,14757170082422194176,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf))) [5,12297829382473034410,14757170082422194176,17361641481138401520,18432388630850633676,18446462603027742720,18446744072850505728] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757170082422194176,17361641481138401520,18432388630850633676,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757170082422194176,18229710309516177648,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757170958595522764,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757320200119158920,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757382013288497344,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf)) [5,12297829382473034410,14757382013288497344,17361641481138401520,18432388630850633676,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757382013288497344,18229723555195321596,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757390843741259976,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757390843741259976,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd BT.lf [5,12297829382473034410,14757394382794312704,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf)))) [5,12297829382473034410,14757395258967588864,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967638208,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967638208,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,14974187289516638208,17361641481138401520,18374966859414961920,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,16927600440168677376,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829382473034410,14757395258967641292,16927600443402535104,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf)) [5,12297829382473034410,14757395258967641292,17197820540979511296,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17216698429492559872,17216961131453612032,17361641481138401520,18374966859414961920] BT.lf) [5,12297829382473034410,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17216698429492559872,17361641481138401520,18432388630850633676,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17216698429492559872,18374388447579140336,18374966859414961920,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17216886072605147136,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf))) [5,12297829382473034410,14757395258967641292,17216886076041068544,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17216945682169913568,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18374966859414961920,18446727516610621680] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18432388630850633676,18446462603027742720] BT.lf) [5,12297829382473034410,14757395258967641292,17216961135462248174,18374388447579140336,18374966859414961920,18446744069414584320] BT.lf)) [5,12297829382473034410,14757395258967641292,17361641481138401520,18302908165848628736,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18360329937284300492,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374403896593350656,18374966859414961920,18446462603027742720] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374742559042843392,18446462603027742720,18446744069414584320] (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374961361856821760,18446462603027742720,18446744069414584320] BT.lf))))) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374961361856821760,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966855992357632,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859331074560,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414958080,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414958080,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422724872833597440,18446462603027742720] BT.lf)) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422724877111787520,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818331321958400,18446462603027742720] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818331321958400,18446727516610621680] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18441958921796059136,18446462603027742720] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18445336673056194560,18446462603027742720] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446743704342364160] BT.lf))) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414606165] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069498799365] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070559908932] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070840669440] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070846240085] BT.lf)) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744071570489472] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744071705198592] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072266711040] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072635858944] (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072648442048] BT.lf)))) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072837136384] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850505728] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850555072] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692774400] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692835840] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027804400,18446744069414584320] BT.lf)) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446463633819894000,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446481367739863313,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446515585744318512,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446550907555369040,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446603890271944832,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446612720724672512,18446744069414584320] BT.lf))) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446638524888227840,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446639212082954240,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446639212082995360,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446649520004464640,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446650245854003200,18446727516610621680] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446673709260324864,18446744069414584320] BT.lf)) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446674533893996544,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446674533894045888,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446674533894045888,18446744072648442048] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446709855705096416,18446744069414584320] (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818408960,18446744069414584320] BT.lf)))))) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818470400,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818470400,18446744073441177600] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727173013237920,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727310452191424,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610560000,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610601120,18446744069414584320] BT.lf)) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610609344,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621440,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446738550381608960] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744070846240085] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744072648442048] BT.lf))) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744072850505728] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744072850555072] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744073441177600] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744073692774400] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744073692835840] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18413248040372076424,18446727516610621680,18446744069414584320] BT.lf)) [5,12297829382473034410,14757395258967641292,17361641481138401520,18429010879589711808,18446674533894045888,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18429010879589711808,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18432387754677305088,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17361641481138401520,18432388579311026112,18446727516610621680,18446744069414584320] (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361641481138401520,18432388630837264128,18446727516610621680,18446744069414584320] BT.lf)))) [5,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17361658038237331455,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17365863605790044400,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17365863670214553855,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,17940354033390252272,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,17940362863708270832,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [5,12297829382473034410,14757395258967641292,17940362863843014904,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18014673391583296000,18085043209519168250,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18014673391583296000,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18014673391583296000,18446462603027742720,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18014673391583296000,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18062524867779689130,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf))) [5,12297829382473034410,14757395258967641292,18082217421685453040,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18082228416633958640,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18082228416801733360,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18085032171284787440,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18085032171453214960,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf)) [5,12297829382473034410,14757395258967641292,18085032171453214960,18432388630850633676,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18085043205308416000,18085043209519168250,18374966859414961920,18446727516610621680] BT.lf) [5,12297829382473034410,14757395258967641292,18085043209350738160,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18085043209519168250,18432388630850633676,18446727516610621680,18446744069414584320] BT.lf))))) [5,12297829382473034410,14757395258967641292,18158790778715962368,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18216212550151634124,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18226332609794863344,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18226345803934399728,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18229710309314064624,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18229710309516177648,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [5,12297829382473034410,14757395258967641292,18229710309516177648,18374966859414961920,18446462603027742720,18446744072850505728] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18229710309516177648,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18229710309516177648,18432387754677305088,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18229710309516177648,18432388630850633676,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18229723554993205488,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18229723555195321596,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf))) [5,12297829382473034410,14757395258967641292,18229723555195321596,18432388630850633676,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,14757395258967641292,18374388447579140336,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18374388447579140336,18374966859414961920,18446744069414584320] BT.lf) [5,12297829382473034410,14757395258967641292,18374403900871474942,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [5,12297829382473034410,18216212550151634124,18374966859414961920,18446462603027742720,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473034410,18216212550151634124,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf)) [5,12297829382473034410,18229723555195321596,18374966859414961920,18432388630850633676,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,12297829382473034410,18229723555195321596,18432388630850633676,18446727516610621680,18446744069414584320] BT.lf) [5,12297829382473056255,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,12297829383618359022,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd BT.lf [5,14757170082422194176,17216886076613765802,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf)))) [5,14757395258967641292,16909585770718358186,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,14757395258967641292,16927600440168677376,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [5,14757395258967641292,16927600443031988906,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [5,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744072648442048] BT.lf) [5,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446674533894045888,18446744069414584320] BT.lf)) [5,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,14757395258967641292,17197745778192984746,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [5,14757395258967641292,17216698429492559872,17216886076613765802,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [5,14757395258967641292,17216886072605147136,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd BT.lf [5,14757395258967641292,17216886075468458666,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf))) [5,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850505728] BT.lf) [5,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,14757395258967641292,17216886076613765802,17361641481138401520,18432387754677305088,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [5,14757395258967641292,17216886076613765802,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [5,14757395258967641292,17216886076613765802,18229710309516177648,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [5,14757395258967641292,17216956720235866858,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [5,14757395258967641292,17216956720235866858,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,14757395258967641292,17216961131453612032,17361641481138401520,18085043209519168250,18374966859414961920,18446462603027742720] BT.lf) [5,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446650245854003200] (BT.nd BT.lf [5,14757395258967641292,17216961135462248174,18085043209519168250,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf)))))))) [5,14757395258967641292,18062524867779689130,18374966859414961920,18446462603027742720,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [5,14757395258967641292,18062524867779689130,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [5,14757395258967641292,18085043209519168250,18374966859414961920,18422818335611355050,18446727516610621680,18446744069414584320] BT.lf) [6,0,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,65535,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,252645135,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [6,1431655765,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,2863311530,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,2863311530,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,3435973836,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,4278255360,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,4294967295,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920] BT.lf))) [6,4294967295,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,4294967295,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,4294967295,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [6,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680] BT.lf)) [6,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,1095216660735,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,16557098929935,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,16557098929935,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd BT.lf [6,16557098929935,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf)))) [6,56294136361779,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,93823560602965,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,187647121205930,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,225176545447116,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,264913582878960,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,280375465148160,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [6,281470681743360,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,281470681808895,71777214294589695,12297829382473034410,14757395258967641292,17361641481138401520,18446744069414584320] BT.lf) [6,281470681808895,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446744069414584320] BT.lf) [6,281470681808895,3689348814741910323,12297829382473034410,17361641481138401520,18374966859414961920,18446744069414584320] (BT.nd (BT.nd BT.lf [6,281470681808895,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [6,281470681808895,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920] BT.lf))) [6,281470681808895,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] (BT.nd (BT.nd BT.lf [6,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [6,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446744069414584320] BT.lf)) [6,281474976710655,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,72057589759737855,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,217020518514230019,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,361700864190383365,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd BT.lf [6,723401728380766730,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf))))) [6,868082074056920076,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1080880403494997760,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,1085086035472220160,1085102592571150095,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [6,1085086035472220160,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446744069414584320] (BT.nd (BT.nd BT.lf [6,1085086035472220160,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,1085086035472220160,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf)) [6,1085102592318504960,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,1085102592571150095,3689348814741910323,12297829382473034410,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,1085102592571150095,6148914691236517205,14757395258967641292,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,1085102592571150095,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [6,1085102592571150095,12297829379609722880,12297829382473034410,14757395258967641292,18374966859414961920,18446462603027742720] BT.lf) [6,1085102592571150095,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf))) [6,1085102592571150095,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,1085102592571150095,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [6,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [6,1085102592571150095,12297829382473034410,14757395258967641292,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [6,1085102596613472255,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [6,1085367506154029055,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,1152657617789587455,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,4557430888798830399,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,4919131752989213764,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd BT.lf [6,6124988953138320640,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)))) [6,6148914689804861440,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,6148914691236517205,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,6148914691236517205,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,6148914691236517205,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,6148914691236517205,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070846240085] BT.lf) [6,6148914691236517205,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf)) [6,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070846240085] BT.lf) [6,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,6148914694099828735,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [6,6148914694099828735,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,6148914694099828735,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf))) [6,6149102338357723135,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,6872316419617283935,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,9259542123273814144,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,9799982325021313024,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,9838113388281462784,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,9838263503687778304,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf)) [6,9838263503687778304,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,9838263505978427528,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd BT.lf [6,9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18413248040372076424,18446462603027742720,18446744069414584320] BT.lf)))))) [6,9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12153149036796881064,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12249790989299875840,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12249977903424471040,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [6,12249977903424471040,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12249977906276641280,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf)) [6,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [6,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12249977906276641280,12297829382473034410,14757395258967641292,17294086455919964160,17361641481138401520,18446462603027742720,18446744069414584320] BT.lf) [6,12249977906276641280,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12249977906276641280,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,12249977906276641280,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf))) [6,12249977906276641280,12297829382473034410,17207390840222969548,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12288259087233755784,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12288259087233755784,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [6,12295014589755599520,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297828652328593920,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829379609722880,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf)) [6,12297829379609722880,12297829382473034410,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829379609722880,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,12297829379609722880,12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,12297829379609722880,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd BT.lf [6,12297829379609722880,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf)))) [6,12297829379609722880,12297829382473034410,14757395258967641292,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829379609722880,12297829382473034410,14757395258967641292,17216961134889585868,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,12297829379609722880,12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18229723555195321596,18374966859414961920,18446462603027742720] (BT.nd (BT.nd BT.lf [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720] BT.lf) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18374966859414961920,18446462603027742720] BT.lf)) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374966859414961920,18446462603027742720] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335600213760,18446462603027742720] BT.lf) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335611355050,18446462603027742720] BT.lf) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630850633676,18446462603027742720] (BT.nd (BT.nd BT.lf [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884633399280,18446462603027742720] BT.lf) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf))) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742978492890880] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072277895850] BT.lf) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850558156] (BT.nd (BT.nd BT.lf [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692839680] BT.lf) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680] BT.lf)) [6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829379609722880,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,12297829379609722880,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829381900372104,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd BT.lf [6,12297829382461893120,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf))))) [6,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073692839680] BT.lf) [6,12297829382473034410,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,12297829383904690175,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,12297923206033637375,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [6,12297829382473034410,12659530246663417775,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,13835269164735971328,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,13889313181676863488,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072648442048] BT.lf) [6,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446674533894045888,18446744069414584320] BT.lf))) [6,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14468034567615334600,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14699749187159851008,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14699973484109365248,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf)) [6,12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14738254668489084040,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14754017507706719424,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757170078986272768,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd BT.lf [6,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)))) [6,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850505728] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18432387754677305088,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757170082422194176,14757395258967641292,18229710309516177648,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757170082422194176,17361641481138401520,18374966859414961920,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf)) [6,12297829382473034410,14757170082422194176,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757320200119158920,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757382013288497344,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757382013288497344,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd BT.lf [6,12297829382473034410,14757394382794312704,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf))) [6,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18432388630837264128,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395257822316680,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258765525184,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [6,12297829382473034410,14757395258954271744,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967588864,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf))))))) [6,12297829382473034410,14757395258967641292,14757395259826634751,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,14757451553104003071,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,14771750701826559231,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,14771750701826559231,17361641481138401520,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,14974415777481871311,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,15987178197214944733,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [6,12297829382473034410,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17072280789786094828,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17149969068787297792,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17197820544983690922,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17207390840222969548,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17216698429492559872,17216961135462248174,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf))) [6,12297829382473034410,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17216923606038006988,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17216961131453612032,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf) [6,12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf)) [6,12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17216961134316923562,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17216961134889585868,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf)))) [6,12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18158790778715962368,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18216212550151634124,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18226345803934399728,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18229723550950883328,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18229723554386857164,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [6,12297829382473034410,14757395258967641292,17361641481138401520,18229723555195321596,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18229723555195321596,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374403900871474942,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374686479671623680,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720,18446744073692774400] BT.lf))) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374873400926579200,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374910784321932288,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374950366740541440,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374950366740541440,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966857988876800,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966858559310848,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859163299840,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf))))) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414896640,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374966859431673855,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374967954631622655,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18379189048491114255,18446462603027742720,18446744069414584320] BT.lf)) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18389322302273879859,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18398892597513158485,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18413248040372076424,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18420003542893920160,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422724877122972330,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422817605466914560,18446462603027742720,18446744069414584320] BT.lf))) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818331321958400,18422818335611355050,18446462603027742720] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818331321958400,18446462603027742720] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818331321958400,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818334185269930,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335600213760,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335611355050,18446462603027742720,18446744069414584320] BT.lf)) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335611355050,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18429010879589711808,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432332555757604044,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432387754677305088,18446462603027742720,18446744069414584320] (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388626559008768,18446462603027742720,18446744069414584320] BT.lf)))) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388629994982604,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630837264128,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630850633676,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18441958926089912302,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442520853841248000,18446462603027742720,18446744069414584320] BT.lf)) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521880339415040,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884381737200,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884617670400,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884633399280,18446462603027742720,18446744069414584320] (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884633399280,18446727516610621680,18446744069414584320] BT.lf))) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18445336677350834170,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18445899635894321148,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742974197923840,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742978476179200,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742978492890880,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446743708637331370,18446744069414584320] BT.lf)) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446743854666219468,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744069414649855] (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744069667229455] BT.lf)))))) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744070846240085] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744071705233544] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072266754560] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072277895850] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072648442048] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072837188608] BT.lf)) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072850505728] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072850558156] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073423220462] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073659022588] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073692774400] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073692839680] BT.lf))) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073703980970] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073706209228] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073708568560] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073709551360] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073709551615] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070846240085] BT.lf)) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072648442048] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850505728] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850558156,18446744073456906480] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850558156,18446744073709486080] (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692774400] BT.lf)))) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692839680,18446744073709486080] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446639212082995360,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446650250148948650,18446727516610621680,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446674533894045888,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446687779573189836,18446727516610621680,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818470400,18446744069414584320] BT.lf)) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727512315658240,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610560000,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446727516610621680,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446738554676574970,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446740762289765628,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446742978492890880,18446744069414584320] BT.lf))) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744009285042160,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744072277895850] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744072850558156] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744073456906480] BT.lf)) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744073692839680] (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744073709486080] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744073709547760] BT.lf) [6,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446727516610621680,18446744069414584320] (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf))))) [6,12297829382473034410,14757395258967641292,18085043209519168250,18374966859414961920,18446462603027742720,18446727516610621680,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,18229710309516177648,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,12297829382473034410,14757395258967641292,18229723555195321596,18374966859414961920,18446462603027742720,18446727516610621680,18446744069414584320] (BT.nd (BT.nd BT.lf [6,12297829382473034410,14757395258967641292,18229723555195321596,18374966859414961920,18446727516610621680,18446744069414584320] BT.lf) [6,13889313184910721216,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [6,14757170082422194176,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [6,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [6,14757395258967641292,17216961135462248174,17361641481138401520,18085043209519168250,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [6,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446650250148948650,18446744069414584320] BT.lf) [7,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] BT.lf))) [7,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [7,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320] BT.lf) [7,1085102592571150095,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [7,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [7,6148914691236517205,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [7,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [7,9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [7,12249977906276641280,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [7,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] (BT.nd BT.lf [7,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)))) [7,12297829382473034410,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [7,12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [7,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd BT.lf [7,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [7,12297829382473034410,14757395258967641292,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)) [7,12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd BT.lf [7,12297829382473034410,14757395258967641292,17361641481138401520,18229723555195321596,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [7,12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18374966859414961920,18446462603027742720,18446744069414584320] (BT.nd BT.lf [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf))) [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335611355050,18446462603027742720,18446744069414584320] (BT.nd (BT.nd (BT.nd (BT.nd BT.lf [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630850633676,18446462603027742720,18446744069414584320] BT.lf) [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884633399280,18446462603027742720,18446744069414584320] BT.lf) [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742978492890880,18446744069414584320] (BT.nd (BT.nd BT.lf [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf) [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744069414584320] BT.lf)) [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072277895850] (BT.nd (BT.nd (BT.nd BT.lf [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072850558156] BT.lf) [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073692839680] BT.lf) [7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320] (BT.nd BT.lf [8,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320] BT.lf)))))))))

noncomputable def K_0 : List (List ℕ × List (ℕ × ℕ)) := [([2,12297829379609722880,18360329937284300492,18446727516610621680],[]),([2,17207390840222969548,18062524867600773120,18446727516610621680],[]),([2,17216886072605147136,18374388447579140336,18432388630850633676],[]),([3,12249977906276641280,12297829379609722880,18216212550151634124,18446727516610621680],[]),([3,12249977906276641280,14757395258967641292,18062524867600773120,18446727516610621680],[]),([3,12297829379609722880,12297829382473034410,18360329937284300492,18446727516610621680],[]),([3,12297829379609722880,14757170082422194176,18085032171453214960,18432388630850633676],[(56,0),(80,0)]),([3,12297829379609722880,14757395258967641292,18014673391583296000,18446727516610621680],[]),([3,12297829379609722880,14757395258967641292,18070969245931993800,18446727516610621680],[]),([3,12297829379609722880,14757395258967641292,18302908165848628736,18446727516610621680],[]),([3,12297829379609722880,14757395258967641292,18360329937284300492,18446727516610621680],[]),([3,12297829379609722880,14757395258967641292,18374388447579140336,18374966859414961920],[(104,0)]),([3,12297829379609722880,14757395258967641292,18374388447579140336,18432388630850633676],[(104,0)]),([3,12297829379609722880,17216698429492559872,18374388447579140336,18432388630850633676],[(80,0)]),([3,12297829379609722880,17216961135462248174,18374388447579140336,18432388630850633676],[(60,0)]),([3,12297829379609722880,18360329937284300492,18374966859414961920,18446727516610621680],[]),([3,12297829379609722880,18360329937284300492,18446462603027742720,18446727516610621680],[]),([3,12297829379609722880,18360329937284300492,18446727516610621680],[]),([3,12297829379609722880,18360329937284300492,18446727516610621680,18446744069414584320],[]),([3,12297829379609722880,18374403900871474942,18432388630850633676,18446727516610621680],[(108,0)]),([3,12297829382473034410,17216961131453612032,18374388447579140336,18432388630850633676],[(60,0)]),([3,12297829382473034410,18360329937284300492,18446727516610621680,18446744069414584320],[]),([3,14757395258967641292,17216886072605147136,18374388447579140336,18374966859414961920],[]),([3,14757395258967641292,17216886076041068544,18085032171453214960,18374966859414961920],[(96,0)]),([3,14757395258967641292,18014673391583296000,18062524863574179840,18446727516610621680],[(56,0)]),([3,17216886076613765802,18374388447579140336,18432388630850633676,18446744069414584320],[]),([4,12249977906276641280,12297829379609722880,14757395258967641292,17294086455919964160,18446727516610621680],[(72,0)]),([4,12249977906276641280,12297829379609722880,17361641481138401520,18216212550151634124,18446462603027742720],[(96,0)]),([4,12249977906276641280,12297829382473034410,18216212550151634124,18446727516610621680,18446744069414584320],[]),([4,12249977906276641280,14757395258967641292,17361641481138401520,18062524867600773120,18446462603027742720],[(56,0)]),([4,12297829379609722880,12297829382473034410,14757395258967641292,18014673391583296000,18446727516610621680],[]),([4,12297829379609722880,12297829382473034410,14757395258967641292,18374388447579140336,18374966859414961920],[(144,0)]),([4,12297829379609722880,12297829382473034410,18216212550151634124,18374966859414961920,18446727516610621680],[]),([4,12297829379609722880,12297829382473034410,18229723555195321596,18432388630850633676,18446727516610621680],[]),([4,12297829379609722880,14757170082422194176,14757395258967641292,18085032171453214960,18374966859414961920],[]),([4,12297829379609722880,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920],[(136,0)]),([4,12297829379609722880,14757395258967641292,17216698429492559872,17361641481138401520,18432388630850633676],[(136,0)]),([4,12297829379609722880,14757395258967641292,17216698429492559872,18374388447579140336,18374966859414961920],[]),([4,12297829379609722880,14757395258967641292,17216945682169913568,17361641481138401520,18374966859414961920],[(136,0)]),([4,12297829379609722880,14757395258967641292,17216961135462248174,18374388447579140336,18374966859414961920],[]),([4,12297829379609722880,14757395258967641292,17361641481138401520,18302908165848628736,18446462603027742720],[(104,0)]),([4,12297829379609722880,14757395258967641292,17361641481138401520,18360329937284300492,18446462603027742720],[(104,0)]),([4,12297829379609722880,14757395258967641292,18014673391583296000,18085043209519168250,18446727516610621680],[(80,0)]),([4,12297829379609722880,14757395258967641292,18014673391583296000,18374966859414961920,18446727516610621680],[]),([4,12297829379609722880,14757395258967641292,18014673391583296000,18446462603027742720,18446727516610621680],[]),([4,12297829379609722880,14757395258967641292,18014673391583296000,18446727516610621680],[(81,0)]),([4,12297829379609722880,14757395258967641292,18014673391583296000,18446727516610621680,18446744069414584320],[]),([4,12297829379609722880,14757395258967641292,18062524867779689130,18374966859414961920,18446727516610621680],[]),([4,12297829379609722880,14757395258967641292,18082217421685453040,18374966859414961920,18446462603027742720],[]),([4,12297829379609722880,14757395258967641292,18082228416801733360,18374966859414961920,18446727516610621680],[]),([4,12297829379609722880,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720],[]),([4,12297829379609722880,14757395258967641292,18085032171453214960,18374966859414961920,18446650250148904960],[]),([4,12297829379609722880,14757395258967641292,18085032171453214960,18374966859414961920,18446727516610621680],[]),([4,12297829379609722880,14757395258967641292,18085032171453214960,18432388630850633676,18446462603027742720],[]),([4,12297829379609722880,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680],[]),([4,12297829379609722880,14757395258967641292,18085043209519168250,18432388630850633676,18446727516610621680],[]),([4,12297829379609722880,14757395258967641292,18374388447579140336,18374966859414961920],[(104,0),(105,0)]),([4,12297829379609722880,14757395258967641292,18374388447579140336,18374966859414961920,18446462603027742720],[(104,0)]),([4,12297829379609722880,14757395258967641292,18374388447579140336,18374966859414961920,18446744069414584320],[(104,0)]),([4,12297829379609722880,14757395258967641292,18374403900871474942,18374966859414961920,18446727516610621680],[]),([4,12297829382461849600,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([4,12297829382461849600,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680],[]),([4,12297829382461890560,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([4,12297829382461890560,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680],[]),([4,12297829382473034410,14757170082422194176,18085032171453214960,18432388630850633676,18446744069414584320],[(80,0)]),([4,12297829382473034410,14757395258967641292,17216961131453612032,18374388447579140336,18374966859414961920],[]),([4,12297829382473034410,14757395258967641292,18014673391583296000,18085043205308416000,18446727516610621680],[(80,0)]),([4,12297829382473034410,14757395258967641292,18014673391583296000,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,14757395258967641292,18062524867600773120,18374966859414961920,18446727516610621680],[]),([4,12297829382473034410,14757395258967641292,18070969245931993800,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,14757395258967641292,18302908165848628736,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,14757395258967641292,18360329937284300492,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,14757395258967641292,18374388447579140336,18374966859414961920,18446744069414584320],[(104,0)]),([4,12297829382473034410,14757395258967641292,18374388447579140336,18432388630850633676,18446744069414584320],[(104,0)]),([4,12297829382473034410,17216698429492559872,18374388447579140336,18432388630850633676,18446744069414584320],[(80,0)]),([4,12297829382473034410,17216961135462248174,18374388447579140336,18432388630850633676,18446744069414584320],[(60,0)]),([4,12297829382473034410,18216212550151634124,18374966859414961920,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,18216212550151634124,18374966859414961920,18446727516610621680,18446744073441177600],[]),([4,12297829382473034410,18216212550151634124,18432388630850633676,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,18229723555195321596,18432388579311026112,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,18229723555195321596,18432388630850633676,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,18360329937284300492,18374966859414961920,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,18360329937284300492,18446462603027742720,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,18360329937284300492,18446727516610621680,18446744069414584320],[]),([4,12297829382473034410,18374403900871474942,18432388630850633676,18446727516610621680,18446744069414584320],[(108,0)]),([4,14757395258967641292,17216698429492559872,17216886072605147136,17361641481138401520,18374966859414961920],[(128,0)]),([4,14757395258967641292,17216886076613765802,18374388447579140336,18374966859414961920,18446744069414584320],[]),([4,14757395258967641292,17216961131453612032,18085043209519168250,18374966859414961920,18446727516610621680],[]),([4,14757395258967641292,18014673391583296000,18062524867779689130,18446727516610621680,18446744069414584320],[(56,0)]),([4,14757395258967641292,18062524863574179840,18062524867779689130,18374966859414961920,18446727516610621680],[]),([4,14757395258967641292,18062524867779689130,18374966859414961920,18446727516610621680,18446744069414584320],[]),([4,14757395258967641292,18062524867779689130,18374966859414961920,18446727516610621680,18446744073441177600],[]),([4,14757395258967641292,18062524867779689130,18432388630850633676,18446727516610621680,18446744069414584320],[]),([4,14757395258967641292,18080539541171272426,18374966859414961920,18446727516610621680,18446744069414584320],[]),([4,14757395258967641292,18080539541171272426,18432388630850633676,18446727516610621680,18446744069414584320],[]),([4,14757395258967641292,18085043209519168250,18374966859414961920,18422818331321958400,18446727516610621680],[]),([4,17216886076613765802,18229710309516177648,18432388630850633676,18446462603027742720,18446744069414584320],[]),([4,17216961135462248174,18085043209519168250,18432388630850633676,18446727516610621680,18446744069414584320],[]),([5,2863311530,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,72057589742960640,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[])]
noncomputable def K_1 : List (List ℕ × List (ℕ × ℕ)) := [([5,723401728380766730,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,768438411859724970,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,868082074056920076,12297829382473034410,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[]),([5,922126094231669964,12297829382473034410,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,1085086035472220160,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920],[]),([5,1085086035472220160,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[]),([5,1085086035472220160,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446744069414584320],[]),([5,1085086039514480640,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[]),([5,1152640029898506240,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[]),([5,1152657617521213440,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,3038287259199220266,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,4539697694678990592,12297829382473034410,14757395258967641292,17361641481138401520,18446462603027742720,18446744069414584320],[]),([5,4557430887737720832,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,4919131752989213764,12297829382473034410,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[]),([5,4957412933946328268,12297829382473034410,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,6872211557990727680,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[]),([5,12249790989299875840,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(72,0)]),([5,12249977906276641280,12297829379609722880,14757395258967641292,17294086455919964160,17361641481138401520,18446462603027742720],[(72,0),(96,0)]),([5,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(72,0)]),([5,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680],[(72,0)]),([5,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18422818335600213760,18446462603027742720],[(72,0)]),([5,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720],[(72,0)]),([5,12249977906276641280,12297829379609722880,17207390840222969548,17361641481138401520,18374966859414961920,18446462603027742720],[(72,0),(128,0)]),([5,12249977906276641280,12297829382473034410,14757395258967641292,17294086455919964160,18446727516610621680,18446744069414584320],[(72,0)]),([5,12249977906276641280,12297829382473034410,17361641481138401520,18216212550151634124,18446462603027742720,18446744069414584320],[(96,0)]),([5,12288259087233755784,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(72,0)]),([5,12288259087233755784,12297829379609722880,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720],[(72,0)]),([5,12288259087233755784,17216961135462248174,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[]),([5,12295014589755599520,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297828652328593920,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,12297829382473034410,14757170082422194176,17361641481138401520,18432388630850633676,18446462603027742720],[(72,0),(80,0),(180,0),(112,0)]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920],[(184,0)]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446612720724672512],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446639212082954240],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446639212082995360],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446649520004464640],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446674533894045888],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818470400],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610560000],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446727516610621680],[(80,0)]),([5,12297829379609722880,12297829382473034410,14757395258967641292,17940362863708270832,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,18082228416633958640,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,18085032171284787440,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,18085043209350738160,18374966859414961920,18446727516610621680],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680],[]),([5,12297829379609722880,12297829382473034410,14757395258967641292,18229710309516177648,18374966859414961920,18446462603027742720],[(180,0),(144,0)]),([5,12297829379609722880,12297829382473034410,14757395258967641292,18229723555195321596,18374966859414961920,18446727516610621680],[]),([5,12297829379609722880,12297923206033637375,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,14757395258967641292,17149969068787297792,17361641481138401520,18374966859414961920,18446462603027742720],[(80,0)]),([5,12297829379609722880,14757395258967641292,17197820544983690922,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,14757395258967641292,17207390840222969548,17361641481138401520,18374966859414961920,18446462603027742720],[(80,0),(136,0)]),([5,12297829379609722880,14757395258967641292,17216698429492559872,17216961135462248174,17361641481138401520,18374966859414961920],[(176,0)]),([5,12297829379609722880,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920],[(136,0),(137,0),(113,0)]),([5,12297829379609722880,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920,18446462603027742720],[(136,0)]),([5,12297829379609722880,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920,18446744069414584320],[(136,0)]),([5,12297829379609722880,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720],[(136,0)]),([5,12297829379609722880,14757395258967641292,17216923606038006988,17361641481138401520,18374966859414961920,18446462603027742720],[(136,0)]),([5,12297829379609722880,14757395258967641292,17216961134316923562,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720],[(136,0)]),([5,12297829379609722880,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446727516610621680],[(136,0)]),([5,12297829379609722880,14757395258967641292,17216961135462248174,17361641481138401520,18432388630850633676,18446462603027742720],[(80,0),(136,0)]),([5,12297829379609722880,14757395258967641292,17361641481138401520,18374403900871474942,18374966859414961920,18446462603027742720],[(136,0),(196,0)]),([5,12297829379609722880,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720],[]),([5,12297829379609722880,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829379609722880,14757395258967641292,18085043209519168250,18374966859414961920,18446462603027742720,18446727516610621680],[]),([5,12297829379609722880,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680],[]),([5,12297829379609722880,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829379778152970,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829381765628032,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829381900337152,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829382461849600,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829382461849600,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720],[]),([5,12297829382461849600,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(106,0)]),([5,12297829382461849600,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382461849600,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692774400],[]),([5,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073456906480],[]),([5,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073709486080],[]),([5,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382461893120,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[]),([5,12297829382470806152,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382470806152,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[]),([5,12297829382472379040,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034240,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,12297923203170304000,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829382473034410,12659337080509235200,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[]),([5,12297829382473034410,12659530243715891200,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829382473034410,14757170082422194176,14757395258967641292,18085032171453214960,18374966859414961920,18446744069414584320],[]),([5,12297829382473034410,14757170082422194176,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(56,0),(80,0)]),([5,12297829382473034410,14757170082422194176,17361641481138401520,18432388630850633676,18446462603027742720,18446744072850505728],[(56,0),(80,0)]),([5,12297829382473034410,14757170082422194176,17361641481138401520,18432388630850633676,18446727516610621680,18446744069414584320],[(56,0),(80,0)]),([5,12297829382473034410,14757170082422194176,18229710309516177648,18432388630850633676,18446462603027742720,18446744069414584320],[(80,0),(104,0),(136,0),(176,0)]),([5,12297829382473034410,14757170958595522764,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757320200119158920,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(56,0)]),([5,12297829382473034410,14757382013288497344,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(56,0),(80,0)])]
noncomputable def K_2 : List (List ℕ × List (ℕ × ℕ)) := [([5,12297829382473034410,14757382013288497344,17361641481138401520,18432388630850633676,18446727516610621680,18446744069414584320],[(56,0),(80,0)]),([5,12297829382473034410,14757382013288497344,18229723555195321596,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757390843741259976,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757390843741259976,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757394382794312704,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967588864,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967638208,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967638208,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,14974187289516638208,17361641481138401520,18374966859414961920,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,16927600440168677376,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,16927600443402535104,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17197820540979511296,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17216698429492559872,17216961131453612032,17361641481138401520,18374966859414961920],[(176,0)]),([5,12297829382473034410,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920,18446744069414584320],[(136,0)]),([5,12297829382473034410,14757395258967641292,17216698429492559872,17361641481138401520,18432388630850633676,18446744069414584320],[(136,0)]),([5,12297829382473034410,14757395258967641292,17216698429492559872,18374388447579140336,18374966859414961920,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17216886072605147136,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17216886076041068544,17361641481138401520,18374966859414961920,18446462603027742720],[(172,0),(136,0)]),([5,12297829382473034410,14757395258967641292,17216945682169913568,17361641481138401520,18374966859414961920,18446744069414584320],[(136,0)]),([5,12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18374966859414961920,18446727516610621680],[]),([5,12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18432388630850633676,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17216961135462248174,18374388447579140336,18374966859414961920,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18302908165848628736,18446462603027742720,18446744069414584320],[(104,0)]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18360329937284300492,18446462603027742720,18446744069414584320],[(104,0)]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374403896593350656,18374966859414961920,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374742559042843392,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374961361856821760,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374961361856821760,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966855992357632,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859331074560,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414958080,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414958080,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422724872833597440,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422724877111787520,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818331321958400,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818331321958400,18446727516610621680],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18441958921796059136,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18445336673056194560,18446462603027742720],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446743704342364160],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414606165],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069498799365],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070559908932],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070840669440],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070846240085],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744071570489472],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744071705198592],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072266711040],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072635858944],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072648442048],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072837136384],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850505728],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850555072],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692774400],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692835840],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027804400,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446463633819894000,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446481367739863313,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446515585744318512,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446550907555369040,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446603890271944832,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446612720724672512,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446638524888227840,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446639212082954240,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446639212082995360,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446649520004464640,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446650245854003200,18446727516610621680],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446673709260324864,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446674533893996544,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446674533894045888,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446674533894045888,18446744072648442048],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446709855705096416,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818408960,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818470400,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818470400,18446744073441177600],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727173013237920,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727310452191424,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610560000,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610601120,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610609344,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621440,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446738550381608960],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744070846240085],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744072648442048],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744072850505728],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744072850555072],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744073441177600],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744073692774400],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744073692835840],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18413248040372076424,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18429010879589711808,18446674533894045888,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18429010879589711808,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18432387754677305088,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18432388579311026112,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18432388630837264128,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17361658038237331455,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17365863605790044400,18374966859414961920,18446462603027742720,18446744069414584320],[])]
noncomputable def K_3 : List (List ℕ × List (ℕ × ℕ)) := [([5,12297829382473034410,14757395258967641292,17365863670214553855,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17940354033390252272,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17940362863708270832,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,17940362863843014904,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18014673391583296000,18085043209519168250,18446727516610621680,18446744069414584320],[(80,0)]),([5,12297829382473034410,14757395258967641292,18014673391583296000,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18014673391583296000,18446462603027742720,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18014673391583296000,18446727516610621680,18446744069414584320],[(81,0)]),([5,12297829382473034410,14757395258967641292,18062524867779689130,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18082217421685453040,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18082228416633958640,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18082228416801733360,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18085032171284787440,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18085032171453214960,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18085032171453214960,18432388630850633676,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18085043205308416000,18085043209519168250,18374966859414961920,18446727516610621680],[]),([5,12297829382473034410,14757395258967641292,18085043209350738160,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18085043209519168250,18432388630850633676,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18158790778715962368,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18216212550151634124,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18226332609794863344,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18226345803934399728,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18229710309314064624,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18229710309516177648,18374966859414961920,18446462603027742720,18446744069414584320],[(104,0)]),([5,12297829382473034410,14757395258967641292,18229710309516177648,18374966859414961920,18446462603027742720,18446744072850505728],[(104,0)]),([5,12297829382473034410,14757395258967641292,18229710309516177648,18374966859414961920,18446727516610621680,18446744069414584320],[(104,0)]),([5,12297829382473034410,14757395258967641292,18229710309516177648,18432387754677305088,18446462603027742720,18446744069414584320],[(104,0)]),([5,12297829382473034410,14757395258967641292,18229710309516177648,18432388630850633676,18446462603027742720,18446744069414584320],[(104,0)]),([5,12297829382473034410,14757395258967641292,18229723554993205488,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18229723555195321596,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18229723555195321596,18432388630850633676,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,14757395258967641292,18374388447579140336,18374966859414961920,18446462603027742720,18446744069414584320],[(104,0)]),([5,12297829382473034410,14757395258967641292,18374388447579140336,18374966859414961920,18446744069414584320],[(104,0),(105,0)]),([5,12297829382473034410,14757395258967641292,18374403900871474942,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,18216212550151634124,18374966859414961920,18446462603027742720,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,18216212550151634124,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,18229723555195321596,18374966859414961920,18432388630850633676,18446727516610621680,18446744069414584320],[]),([5,12297829382473034410,18229723555195321596,18432388630850633676,18446727516610621680,18446744069414584320],[(109,0)]),([5,12297829382473056255,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,12297829383618359022,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,14757170082422194176,17216886076613765802,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(56,0),(96,0),(128,0),(168,0)]),([5,14757395258967641292,16909585770718358186,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,14757395258967641292,16927600440168677376,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720],[]),([5,14757395258967641292,16927600443031988906,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744072648442048],[]),([5,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446674533894045888,18446744069414584320],[]),([5,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,14757395258967641292,17197745778192984746,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,14757395258967641292,17216698429492559872,17216886076613765802,17361641481138401520,18374966859414961920,18446744069414584320],[(128,0)]),([5,14757395258967641292,17216886072605147136,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720],[(128,0)]),([5,14757395258967641292,17216886075468458666,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(96,0)]),([5,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850505728],[(96,0)]),([5,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[(96,0)]),([5,14757395258967641292,17216886076613765802,17361641481138401520,18432387754677305088,18446462603027742720,18446744069414584320],[(96,0)]),([5,14757395258967641292,17216886076613765802,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(96,0)]),([5,14757395258967641292,17216886076613765802,18229710309516177648,18374966859414961920,18446462603027742720,18446744069414584320],[]),([5,14757395258967641292,17216956720235866858,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(96,0)]),([5,14757395258967641292,17216956720235866858,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[(96,0)]),([5,14757395258967641292,17216961131453612032,17361641481138401520,18085043209519168250,18374966859414961920,18446462603027742720],[]),([5,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446650245854003200],[(96,0)]),([5,14757395258967641292,17216961135462248174,18085043209519168250,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,14757395258967641292,18062524867779689130,18374966859414961920,18446462603027742720,18446727516610621680,18446744069414584320],[]),([5,14757395258967641292,18062524867779689130,18374966859414961920,18446727516610621680,18446744069414584320],[]),([5,14757395258967641292,18085043209519168250,18374966859414961920,18422818335611355050,18446727516610621680,18446744069414584320],[]),([6,0,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,65535,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,252645135,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,1431655765,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,2863311530,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,2863311530,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,3435973836,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0)]),([6,4278255360,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,4294967295,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920],[]),([6,4294967295,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446462603027742720],[]),([6,4294967295,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,4294967295,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680],[]),([6,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,1095216660735,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,16557098929935,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,16557098929935,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,16557098929935,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[]),([6,56294136361779,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,93823560602965,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,187647121205930,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,225176545447116,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0)]),([6,264913582878960,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,280375465148160,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(72,0)]),([6,281470681743360,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,281470681808895,71777214294589695,12297829382473034410,14757395258967641292,17361641481138401520,18446744069414584320],[]),([6,281470681808895,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446744069414584320],[]),([6,281470681808895,3689348814741910323,12297829382473034410,17361641481138401520,18374966859414961920,18446744069414584320],[]),([6,281470681808895,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[]),([6,281470681808895,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920],[])]
noncomputable def K_4 : List (List ℕ × List (ℕ × ℕ)) := [([6,281470681808895,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[]),([6,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(72,0)]),([6,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446744069414584320],[(2,0)]),([6,281474976710655,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,72057589759737855,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,217020518514230019,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,361700864190383365,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0)]),([6,723401728380766730,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,868082074056920076,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0)]),([6,1080880403494997760,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,1085086035472220160,1085102592571150095,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[]),([6,1085086035472220160,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446744069414584320],[]),([6,1085086035472220160,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,1085086035472220160,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[]),([6,1085102592318504960,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,1085102592571150095,3689348814741910323,12297829382473034410,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,1085102592571150095,6148914691236517205,14757395258967641292,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,1085102592571150095,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,1085102592571150095,12297829379609722880,12297829382473034410,14757395258967641292,18374966859414961920,18446462603027742720],[]),([6,1085102592571150095,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,1085102592571150095,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,1085102592571150095,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[]),([6,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,1085102592571150095,12297829382473034410,14757395258967641292,18432388630850633676,18446462603027742720,18446744069414584320],[(2,0)]),([6,1085102596613472255,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,1085367506154029055,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,1152657617789587455,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,4557430888798830399,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(172,0)]),([6,4919131752989213764,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0)]),([6,6124988953138320640,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,6148914689804861440,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,6148914691236517205,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,6148914691236517205,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,6148914691236517205,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,6148914691236517205,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070846240085],[]),([6,6148914691236517205,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[(100,0)]),([6,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070846240085],[]),([6,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,6148914694099828735,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,6148914694099828735,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,6148914694099828735,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,6149102338357723135,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(100,0)]),([6,6872316419617283935,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,9259542123273814144,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0)]),([6,9799982325021313024,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,9838113388281462784,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0)]),([6,9838263503687778304,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(168,0)]),([6,9838263503687778304,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0)]),([6,9838263505978427528,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(168,0)]),([6,9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0)]),([6,9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18413248040372076424,18446462603027742720,18446744069414584320],[(56,0),(72,0),(128,0)]),([6,9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(56,0),(72,0),(128,0)]),([6,12153149036796881064,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12249790989299875840,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(72,0)]),([6,12249977903424471040,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(96,0)]),([6,12249977903424471040,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(72,0)]),([6,12249977906276641280,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(96,0)]),([6,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(72,0),(97,0)]),([6,12249977906276641280,12297829379609722880,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(72,0)]),([6,12249977906276641280,12297829382473034410,14757395258967641292,17294086455919964160,17361641481138401520,18446462603027742720,18446744069414584320],[(72,0),(96,0)]),([6,12249977906276641280,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(72,0)]),([6,12249977906276641280,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[(72,0)]),([6,12249977906276641280,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(56,0),(72,0),(128,0)]),([6,12249977906276641280,12297829382473034410,17207390840222969548,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(56,0),(72,0),(128,0)]),([6,12288259087233755784,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(72,0),(128,0)]),([6,12288259087233755784,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(56,0),(72,0),(128,0)]),([6,12295014589755599520,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297828652328593920,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829379609722880,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,12297829379609722880,12297829382473034410,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,12297829379609722880,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(184,0)]),([6,12297829379609722880,12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,12297829379609722880,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(228,0),(184,0)]),([6,12297829379609722880,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(184,0)]),([6,12297829379609722880,12297829382473034410,14757395258967641292,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(184,0)]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17216961134889585868,17361641481138401520,18374966859414961920,18446462603027742720],[(184,0)]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720],[(184,0)]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18229723555195321596,18374966859414961920,18446462603027742720],[(184,0)]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18374966859414961920,18446462603027742720],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374966859414961920,18446462603027742720],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335600213760,18446462603027742720],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335611355050,18446462603027742720],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630850633676,18446462603027742720],[(80,0),(200,0)]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884633399280,18446462603027742720],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(105,0),(181,0),(146,0)]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742978492890880],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072277895850],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850558156],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692839680],[]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680],[(105,0),(181,0),(157,0)]),([6,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,12297829379609722880,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720],[(136,0),(137,0)])]
noncomputable def K_5 : List (List ℕ × List (ℕ × ℕ)) := [([6,12297829379609722880,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829381900372104,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382461893120,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382461893120,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073692839680],[]),([6,12297829382473034410,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,12297829383904690175,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,12297923206033637375,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,12659530246663417775,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,13835269164735971328,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,13889313181676863488,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072648442048],[(136,0)]),([6,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446674533894045888,18446744069414584320],[]),([6,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14468034567615334600,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14699749187159851008,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14699973484109365248,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(80,0),(136,0)]),([6,12297829382473034410,14738254668489084040,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14754017507706719424,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757170078986272768,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850505728],[(136,0)]),([6,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18432387754677305088,18446462603027742720,18446744069414584320],[(80,0),(136,0),(176,0),(224,0)]),([6,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(80,0),(136,0),(176,0),(224,0)]),([6,12297829382473034410,14757170082422194176,14757395258967641292,18229710309516177648,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757170082422194176,17361641481138401520,18374966859414961920,18432388630850633676,18446462603027742720,18446744069414584320],[(56,0),(80,0)]),([6,12297829382473034410,14757170082422194176,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(56,0),(58,0),(134,0),(80,0),(81,0)]),([6,12297829382473034410,14757320200119158920,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757382013288497344,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757382013288497344,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757394382794312704,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18432388630837264128,18446462603027742720,18446744069414584320],[(80,0),(136,0),(224,0)]),([6,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(80,0),(136,0),(224,0)]),([6,12297829382473034410,14757395257822316680,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258765525184,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258954271744,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967588864,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,14757395258967641292,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(64,0),(68,0),(136,0)]),([6,12297829382473034410,14757395258967641292,14757395259826634751,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,14757451553104003071,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,14771750701826559231,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,14771750701826559231,17361641481138401520,18446462603027742720,18446744069414584320],[(10,0)]),([6,12297829382473034410,14757395258967641292,14974415777481871311,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,15987178197214944733,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17072280789786094828,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,17149969068787297792,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(80,0)]),([6,12297829382473034410,14757395258967641292,17197820544983690922,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17207390840222969548,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(80,0),(136,0),(144,0)]),([6,12297829382473034410,14757395258967641292,17216698429492559872,17216961135462248174,17361641481138401520,18374966859414961920,18446744069414584320],[(176,0)]),([6,12297829382473034410,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,17216698429492559872,17361641481138401520,18374966859414961920,18446744069414584320],[(136,0),(137,0),(113,0)]),([6,12297829382473034410,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,17216923606038006988,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,17216961131453612032,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720],[(176,0)]),([6,12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18374966859414961920,18446462603027742720],[]),([6,12297829382473034410,14757395258967641292,17216961131453612032,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17216961134316923562,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17216961134889585868,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18432388630850633676,18446462603027742720,18446744069414584320],[(76,0),(80,0),(84,0),(136,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18158790778715962368,18374966859414961920,18446462603027742720,18446744069414584320],[(104,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18216212550151634124,18374966859414961920,18446462603027742720,18446744069414584320],[(104,0),(136,0),(152,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18226345803934399728,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18229723550950883328,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18229723554386857164,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18229723555195321596,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18229723555195321596,18374966859414961920,18446727516610621680,18446744069414584320],[(136,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374403900871474942,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0),(196,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374686479671623680,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720,18446744073692774400],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374873400926579200,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374910784321932288,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374950366740541440,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374950366740541440,18374966859414961920,18446727516610621680,18446744069414584320],[(116,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18432388630850633676,18446462603027742720,18446744069414584320],[(152,0),(240,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966857988876800,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966858559310848,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859163299840,18374966859414961920,18446462603027742720,18446744069414584320],[(240,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414896640,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374966859414961920,18446727516610621680,18446744069414584320],[(116,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374966859431673855,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374967954631622655,18446462603027742720,18446744069414584320],[(148,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18379189048491114255,18446462603027742720,18446744069414584320],[(204,0)])]
noncomputable def K_6 : List (List ℕ × List (ℕ × ℕ)) := [([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18389322302273879859,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18398892597513158485,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18413248040372076424,18446462603027742720,18446744069414584320],[(152,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18420003542893920160,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422724877122972330,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422817605466914560,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818331321958400,18422818335611355050,18446462603027742720],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818331321958400,18446462603027742720],[(73,0),(106,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818331321958400,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818334185269930,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335600213760,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335611355050,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335611355050,18446727516610621680,18446744069414584320],[(148,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18429010879589711808,18446462603027742720,18446744069414584320],[(152,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432332555757604044,18446462603027742720,18446744069414584320],[(152,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432387754677305088,18446462603027742720,18446744069414584320],[(152,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388626559008768,18446462603027742720,18446744069414584320],[(152,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388629994982604,18446462603027742720,18446744069414584320],[(152,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630837264128,18446462603027742720,18446744069414584320],[(152,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630850633676,18446462603027742720,18446744069414584320],[(152,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630850633676,18446727516610621680,18446744069414584320],[(116,0),(148,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18441958926089912302,18446462603027742720,18446744069414584320],[(148,0),(204,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442520853841248000,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521880339415040,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884381737200,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884617670400,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884633399280,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884633399280,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18445336677350834170,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18445899635894321148,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742974197923840,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742978476179200,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742978492890880,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446743708637331370,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446743854666219468,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(106,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744069414649855],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744069667229455],[(252,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744070846240085],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744071705233544],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072266754560],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072277895850],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072648442048],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072837188608],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072850505728],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072850558156],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073423220462],[(252,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073659022588],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073692774400],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073692839680],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073703980970],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073706209228],[(236,0),(252,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073708568560],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073709551360],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073709551615],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744070846240085],[(106,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072648442048],[(106,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850505728],[(106,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850558156,18446744073456906480],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744072850558156,18446744073709486080],[(220,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692774400],[(106,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744073692839680,18446744073709486080],[(220,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446639212082995360,18446744069414584320],[(106,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446650250148948650,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446674533894045888,18446744069414584320],[(106,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446687779573189836,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446726485818470400,18446744069414584320],[(106,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727512315658240,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610560000,18446744069414584320],[(106,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446738554676574970,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446740762289765628,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446742978492890880,18446744069414584320],[(188,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744009285042160,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[(117,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744072277895850],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744072850558156],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744073456906480],[]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744073692839680],[(236,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744073709486080],[(220,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320,18446744073709547760],[(220,0)]),([6,12297829382473034410,14757395258967641292,17361641481138401520,18432388630850633676,18446727516610621680,18446744069414584320],[(58,0),(81,0),(117,0)]),([6,12297829382473034410,14757395258967641292,18085032171453214960,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,18085043209519168250,18374966859414961920,18446462603027742720,18446727516610621680,18446744069414584320],[]),([6,12297829382473034410,14757395258967641292,18085043209519168250,18374966859414961920,18446727516610621680,18446744069414584320],[(133,0)]),([6,12297829382473034410,14757395258967641292,18229710309516177648,18374966859414961920,18446462603027742720,18446744069414584320],[(134,0),(104,0),(105,0)]),([6,12297829382473034410,14757395258967641292,18229723555195321596,18374966859414961920,18446462603027742720,18446727516610621680,18446744069414584320],[(104,0)]),([6,12297829382473034410,14757395258967641292,18229723555195321596,18374966859414961920,18446727516610621680,18446744069414584320],[]),([6,13889313184910721216,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0)]),([6,14757170082422194176,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[]),([6,14757395258967641292,16927600444109941482,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(98,0)]),([6,14757395258967641292,17216886076613765802,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(96,0),(97,0)]),([6,14757395258967641292,17216961135462248174,17361641481138401520,18085043209519168250,18374966859414961920,18446462603027742720,18446744069414584320],[(128,0),(244,0)]),([6,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446650250148948650,18446744069414584320],[(96,0)]),([7,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(10,0),(146,0),(18,0)]),([7,4294967295,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(97,0),(101,0),(169,0),(173,0),(146,0)]),([7,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(2,0),(97,0)]),([7,281470681808895,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446744069414584320],[(97,0)])]
noncomputable def K_7 : List (List ℕ × List (ℕ × ℕ)) := [([7,1085102592571150095,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(2,0),(169,0)]),([7,1085102592571150095,12297829382473034410,14757395258967641292,18374966859414961920,18446462603027742720,18446744069414584320],[(14,0)]),([7,6148914691236517205,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(97,0),(101,0),(169,0),(173,0),(146,0)]),([7,6148914691236517205,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(6,0),(106,0),(14,0)]),([7,9838263505978427528,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(2,0),(97,0),(128,0),(169,0)]),([7,12249977906276641280,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(2,0),(72,0),(97,0),(101,0),(169,0)]),([7,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720],[(99,0),(103,0),(171,0),(175,0),(105,0),(107,0),(111,0),(179,0),(181,0),(183,0),(10,0),(11,0),(146,0),(187,0),(13,0),(159,0),(195,0),(199,0),(18,0),(19,0),(21,0)]),([7,12297829379609722880,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(97,0),(101,0),(169,0),(173,0),(105,0),(181,0),(146,0),(242,0),(246,0),(258,0),(262,0)]),([7,12297829382473034410,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(97,0),(101,0),(169,0),(173,0),(146,0)]),([7,12297829382473034410,13889313184910721216,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(105,0),(136,0),(138,0),(177,0),(181,0),(146,0)]),([7,12297829382473034410,14699973487531969536,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(6,0),(177,0)]),([7,12297829382473034410,14757170082422194176,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(174,0),(6,0),(105,0),(109,0),(136,0),(177,0)]),([7,12297829382473034410,14757395255531667456,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(6,0),(105,0),(136,0),(177,0)]),([7,12297829382473034410,14757395258967641292,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(6,0),(136,0),(177,0)]),([7,12297829382473034410,14757395258967641292,17216961135462248174,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0),(137,0),(10,0),(117,0),(185,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18229723555195321596,18374966859414961920,18446462603027742720,18446744069414584320],[(136,0),(138,0),(137,0),(118,0),(193,0),(197,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374686483949813760,18374966859414961920,18446462603027742720,18446744069414584320],[(138,0),(114,0),(118,0),(193,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966855136706560,18374966859414961920,18446462603027742720,18446744069414584320],[(118,0),(14,0),(193,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18374966859414961920,18446462603027742720,18446744069414584320],[(118,0),(14,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18422818335611355050,18446462603027742720,18446744069414584320],[(73,0),(106,0),(150,0),(18,0),(205,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18432388630850633676,18446462603027742720,18446744069414584320],[(58,0),(98,0),(81,0),(106,0),(114,0),(118,0),(150,0),(14,0),(152,0),(153,0),(193,0),(197,0),(241,0),(18,0),(205,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18442521884633399280,18446462603027742720,18446744069414584320],[(106,0),(150,0),(18,0),(201,0),(205,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446742978492890880,18446744069414584320],[(106,0),(186,0),(190,0),(206,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(75,0),(79,0),(131,0),(135,0),(6,0),(7,0),(106,0),(139,0),(9,0),(119,0),(147,0),(151,0),(187,0),(191,0),(14,0),(15,0),(17,0),(203,0),(207,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744069414584320],[(106,0),(186,0),(190,0),(202,0),(206,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072277895850],[(106,0),(234,0),(238,0),(250,0),(254,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744072850558156],[(106,0),(238,0),(250,0),(254,0),(26,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320,18446744073692839680],[(106,0),(186,0),(238,0),(254,0),(26,0)]),([7,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446727516610621680,18446744069414584320],[(75,0),(79,0),(135,0),(6,0),(7,0),(9,0),(117,0),(119,0),(151,0),(191,0),(14,0),(15,0)]),([8,12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720,18446744069414584320],[(75,0),(79,0),(131,0),(135,0),(6,0),(7,0),(106,0),(139,0),(9,0),(119,0),(147,0),(151,0),(187,0),(191,0),(14,0),(15,0),(17,0),(203,0),(207,0)])]
set_option maxRecDepth 100000 in
theorem c_0 : K_0.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c_1 : K_1.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c_2 : K_2.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c_3 : K_3.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c_4 : K_4.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c_5 : K_5.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c_6 : K_6.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c_7 : K_7.all (fun kh => stepOK M_ Y_ PD_ PM_ G_ T_cert kh.1 kh.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem hK_cert : T_cert.toList = ((((((((K_0 ++ K_1) ++ K_2) ++ K_3) ++ K_4) ++ K_5) ++ K_6) ++ K_7)).map Prod.fst := by decide +kernel
set_option maxRecDepth 100000 in
theorem hT_cert : ∀ x, T_cert.mem x = true → ∃ h, (stepOK M_ Y_ PD_ PM_ G_ T_cert) x h = true :=
  cover (p := stepOK M_ Y_ PD_ PM_ G_ T_cert) T_cert _ hK_cert (all_app (all_app (all_app (all_app (all_app (all_app (all_app c_0 c_1) c_2) c_3) c_4) c_5) c_6) c_7)

namespace Restrict

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

end Restrict

def idx6 (x : Fin 6 → Bool) : ℕ :=
  (if x 0 then 2 ^ 0 else 0) + (if x 1 then 2 ^ 1 else 0) + (if x 2 then 2 ^ 2 else 0) +
    (if x 3 then 2 ^ 3 else 0) + (if x 4 then 2 ^ 4 else 0) + (if x 5 then 2 ^ 5 else 0)

theorem sum_eq (x : Fin 6 → Bool) : (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = idx6 x := by
  rw [Fin.sum_univ_six]; rfl

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074664 * 2 ^ 32 + 4274843840) (idx6 x)

theorem required (s : ℕ) (h : HasCircuitSize 6 target s) : 9 ≤ s :=
  lb_cert target L_ M_ Y_ XS_ PD_ PM_ G_ T_cert 8 9 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) ⟨fun _ => false, fun _ => true, by decide +kernel⟩ (by decide +kernel) (by decide +kernel) hT_cert (by decide +kernel) s h

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 1]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [5, 0]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [12, 13]⟩], 14⟩

set_option maxRecDepth 100000 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_36214

open PEqualNP.Outside.L_meta_36214 PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_36214 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4274843840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4274843840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  have h' : HasCircuitSize 6 target s := by
    obtain ⟨C, ok, sz, ev⟩ := h
    refine ⟨C, ok, sz, fun x => (ev x).trans ?_⟩
    show Nat.testBit (4277074664 * 2 ^ 32 + 4274843840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = target x
    rw [sum_eq]; rfl
  have big := required s h'
  refine ⟨witness, by simp [Monotone2, witness], ?_, fun x => ?_⟩
  · have : witness.size = 9 := rfl
    omega
  · show witness.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4274843840) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
    rw [witnessCorrect x, sum_eq]; rfl
