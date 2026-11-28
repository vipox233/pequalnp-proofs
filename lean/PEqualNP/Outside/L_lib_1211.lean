import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1211

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_front (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_front gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_front gs w
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
    obtain ⟨t, ht, _⟩ := wiresFrom_front r.1.toList w'
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

def cnt (gs : List Gate) : ℕ := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem cnt_le (gs : List Gate) : cnt gs ≤ gs.length := List.length_filter_le _ _

theorem cnt_append (a b : List Gate) : cnt (a ++ b) = cnt a + cnt b := by
  simp [cnt, PEqualNP.NotBracket.notCount, List.filter_append]

theorem cnt_not (g : Gate) (h : g.op = GateOp.not) : cnt [g] = 1 := by
  simp [cnt, PEqualNP.NotBracket.notCount, h]

theorem cnt_nnot (g : Gate) (h : g.op ≠ GateOp.not) : cnt [g] = 0 := by
  simp [cnt, PEqualNP.NotBracket.notCount, h]

theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

theorem step_count (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    ∃ a b : ℕ, cnt (elimStep n acc g).2 + a = cnt acc.2 + cnt [g] ∧
      (elimStep n acc g).2.length + a + b = acc.2.length + 1 ∧
      ((g.op ≠ GateOp.not ∧ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none) → 1 ≤ b) := by
  have hop := simplify_op g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  simp only [elimStep]
  cases ho : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 with
  | none =>
    by_cases hn : g.op = GateOp.not
    · exact ⟨1, 0, by simp [cnt_not g hn], by simp, fun h => absurd hn h.1⟩
    · exact ⟨0, 1, by simp [cnt_nnot g hn], by simp, fun _ => le_refl _⟩
  | some g' =>
    have hg' : g'.op = g.op := hop g' (by rw [ho]; rfl)
    refine ⟨0, 0, ?_, by simp, fun h => by simp at h⟩
    simp only [Option.toList_some, cnt_append, Nat.add_zero]
    by_cases hn : g.op = GateOp.not
    · rw [cnt_not g hn, cnt_not g' (hg'.trans hn)]
    · rw [cnt_nnot g hn, cnt_nnot g' (fun h => hn (hg'.symm.trans h))]

theorem elim_count (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ a b : ℕ, cnt (elim n gs acc).2 + a = cnt acc.2 + cnt gs ∧
      (elim n gs acc).2.length + a + b = acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; exact ⟨0, 0, rfl, rfl⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨a1, b1, e1, e2, _⟩ := step_count n acc g
    obtain ⟨a2, b2, f1, f2⟩ := ih (elimStep n acc g)
    refine ⟨a1 + a2, b1 + b2, ?_, ?_⟩
    · rw [elim_cons, cnt_append [g] gs |> fun h => (h : cnt (g :: gs) = _)]; omega
    · rw [elim_cons, List.length_cons]; omega

def J {X : Type} (st : List Stat) (W : X → Bool → List Bool) : Prop :=
  (∀ x y, (W x y).length = st.length) ∧ ∀ i : ℕ,
    (∀ c, st.getD i (Sum.inl false) = Sum.inl c →
      ∀ x z y, (W x y).getD i false = (W z y).getD i false) ∧
    (∀ j, st.getD i (Sum.inl false) = Sum.inr j →
      ∀ x y y', (W x y).getD i false = (W x y').getD i false)

theorem J_snoc {X : Type} (st : List Stat) (W : X → Bool → List Bool) (s : Stat)
    (f : X → Bool → Bool) (hJ : J st W)
    (h1 : ∀ c, s = Sum.inl c → ∀ x z y, f x y = f z y)
    (h2 : ∀ j, s = Sum.inr j → ∀ x y y', f x y = f x y') :
    J (st ++ [s]) (fun x y => W x y ++ [f x y]) := by
  refine ⟨fun x y => by simp [hJ.1 x y], ?_⟩
  intro i
  by_cases hi : i = st.length
  · subst hi
    rw [getD_snoc_eq]
    refine ⟨fun c hc x z y => ?_, fun j hj x y y' => ?_⟩
    · rw [getD_snoc_len _ _ _ _ (hJ.1 x y), getD_snoc_len _ _ _ _ (hJ.1 z y)]
      exact h1 c hc x z y
    · rw [getD_snoc_len _ _ _ _ (hJ.1 x y), getD_snoc_len _ _ _ _ (hJ.1 x y')]
      exact h2 j hj x y y'
  · rw [getD_snoc_ne _ _ _ _ hi]
    refine ⟨fun c hc x z y => ?_, fun j hj x y y' => ?_⟩
    · rw [getD_snoc_ne _ _ _ _ (by rw [hJ.1]; exact hi),
        getD_snoc_ne _ _ _ _ (by rw [hJ.1]; exact hi)]
      exact (hJ.2 i).1 c hc x z y
    · rw [getD_snoc_ne _ _ _ _ (by rw [hJ.1]; exact hi),
        getD_snoc_ne _ _ _ _ (by rw [hJ.1]; exact hi)]
      exact (hJ.2 i).2 j hj x y y'

theorem step_dich {X : Type} (m : ℕ) (st : List Stat) (W : X → Bool → List Bool) (g : Gate)
    (hg : Ok g) (hJ : J st W) :
    (g.op ≠ GateOp.not ∧
      (simplify g.op m (g.inputs.map fun i => st.getD i (Sum.inl false))).1 = none) ∨
    J (st ++ [(simplify g.op m (g.inputs.map fun i => st.getD i (Sum.inl false))).2])
      (fun x y => W x y ++ [g.op.eval (g.inputs.map fun i => (W x y).getD i false)]) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact Or.inl ⟨by simp, rfl⟩
    · refine Or.inl ⟨by simp, ?_⟩
      simp only [simplify, List.map]
      cases st.getD a (Sum.inl false) <;> rfl
    · cases ha : st.getD a (Sum.inl false) with
      | inl ca =>
        refine Or.inl ⟨by simp, ?_⟩
        simp only [simplify, List.map, ha]
        cases st.getD b (Sum.inl false) <;> rfl
      | inr ja =>
        cases hb : st.getD b (Sum.inl false) with
        | inl cb =>
          refine Or.inl ⟨by simp, ?_⟩
          simp only [simplify, List.map, ha, hb]; rfl
        | inr jb =>
          refine Or.inr (J_snoc _ _ _ _ hJ ?_ ?_)
          · intro c hc; simp only [List.map, ha, hb, simplify, simpAnd] at hc; cases hc
          · intro j _ x y y'
            simp only [List.map, GateOp.eval, List.all_cons, List.all_nil, id]
            rw [(hJ.2 a).2 ja ha x y y', (hJ.2 b).2 jb hb x y y']
    · simp at hlen
  · have : op = GateOp.or := h
    subst this
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact Or.inl ⟨by simp, rfl⟩
    · refine Or.inl ⟨by simp, ?_⟩
      simp only [simplify, List.map]
      cases st.getD a (Sum.inl false) <;> rfl
    · cases ha : st.getD a (Sum.inl false) with
      | inl ca =>
        refine Or.inl ⟨by simp, ?_⟩
        simp only [simplify, List.map, ha]
        cases st.getD b (Sum.inl false) <;> rfl
      | inr ja =>
        cases hb : st.getD b (Sum.inl false) with
        | inl cb =>
          refine Or.inl ⟨by simp, ?_⟩
          simp only [simplify, List.map, ha, hb]; rfl
        | inr jb =>
          refine Or.inr (J_snoc _ _ _ _ hJ ?_ ?_)
          · intro c hc; simp only [List.map, ha, hb, simplify, simpOr] at hc; cases hc
          · intro j _ x y y'
            simp only [List.map, GateOp.eval, List.any_cons, List.any_nil, id]
            rw [(hJ.2 a).2 ja ha x y y', (hJ.2 b).2 jb hb x y y']
    · simp at hlen
  · have : op = GateOp.not := h
    subst this
    refine Or.inr (J_snoc _ _ _ _ hJ ?_ ?_)
    · rcases inputs with _ | ⟨a, l⟩
      · intro c _ x z y; rfl
      · intro c hc x z y
        simp only [List.map, GateOp.eval, List.headD_cons]
        cases ha : st.getD a (Sum.inl false) with
        | inl ca => rw [(hJ.2 a).1 ca ha x z y]
        | inr ja => simp only [List.map, ha, simplify, simpNot] at hc; cases hc
    · rcases inputs with _ | ⟨a, l⟩
      · intro j _ x y y'; rfl
      · intro j hj x y y'
        simp only [List.map, GateOp.eval, List.headD_cons]
        cases ha : st.getD a (Sum.inl false) with
        | inl ca => simp only [List.map, ha, simplify, simpNot] at hj; cases hj
        | inr ja => rw [(hJ.2 a).2 ja ha x y y']

theorem elim_dich {X : Type} (n : ℕ) (gs : List Gate) :
    ∀ (acc : List Stat × List Gate) (W : X → Bool → List Bool), (∀ g ∈ gs, Ok g) → J acc.1 W →
    ∃ a b : ℕ, cnt (elim n gs acc).2 + a = cnt acc.2 + cnt gs ∧
      (elim n gs acc).2.length + a + b = acc.2.length + gs.length ∧
      (1 ≤ b ∨ J (elim n gs acc).1 (fun x y => wiresFrom gs (W x y))) := by
  induction gs with
  | nil => intro acc W _ hJ; exact ⟨0, 0, rfl, rfl, Or.inr hJ⟩
  | cons g gs ih =>
    intro acc W hok hJ
    obtain ⟨a1, b1, e1, e2, e3⟩ := step_count n acc g
    have hc : cnt (g :: gs) = cnt [g] + cnt gs := cnt_append [g] gs
    rcases step_dich (n + acc.2.length) acc.1 W g (hok g List.mem_cons_self) hJ with hd | hJ'
    · have hb1 := e3 hd
      obtain ⟨a2, b2, f1, f2⟩ := elim_count n gs (elimStep n acc g)
      refine ⟨a1 + a2, b1 + b2, ?_, ?_, Or.inl (by omega)⟩
      · rw [elim_cons, hc]; omega
      · rw [elim_cons, List.length_cons]; omega
    · obtain ⟨a2, b2, f1, f2, f3⟩ := ih (elimStep n acc g) _
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hJ'
      refine ⟨a1 + a2, b1 + b2, ?_, ?_, ?_⟩
      · rw [elim_cons, hc]; omega
      · rw [elim_cons, List.length_cons]; omega
      · rcases f3 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h

def st0 (n : ℕ) (v : Bool) : List Stat :=
  (List.range n).map Sum.inr ++ [Sum.inl v, Sum.inl false, Sum.inl true]

def tapNat (n : ℕ) (st : List Stat) (i : ℕ) : ℕ :=
  match st.getD i (Sum.inl false) with
  | Sum.inl c => bif c then n + 1 else n
  | Sum.inr j => j

theorem getD_app_add {α : Type} (L t : List α) (d : α) (n k : ℕ) (h : L.length = n) :
    (L ++ t).getD (n + k) d = t.getD k d := by
  subst h
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem st0_lt (n : ℕ) (v : Bool) (i : ℕ) (h : i < n) (d : Stat) :
    (st0 n v).getD i d = Sum.inr i := by
  simp only [st0]
  rw [List.getD_append _ _ _ _ (by simpa using h)]
  simp [h]

theorem st0_add (n : ℕ) (v : Bool) (k : ℕ) (d : Stat) :
    (st0 n v).getD (n + k) d = [Sum.inl v, Sum.inl false, Sum.inl true].getD k d :=
  getD_app_add _ _ _ _ _ (by simp)

theorem inp_lt {n : ℕ} (x : Fin n → Bool) (t : List Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x ++ t).getD i false = (List.ofFn x).getD i false :=
  List.getD_append _ _ _ _ (by simpa using h)

theorem inp_add {n : ℕ} (x : Fin n → Bool) (t : List Bool) (k : ℕ) :
    (List.ofFn x ++ t).getD (n + k) false = t.getD k false :=
  getD_app_add _ _ _ _ _ (by simp)

theorem inv0 (n : ℕ) (v : Bool) (x : Fin n → Bool) :
    Inv (n + 2) (List.ofFn x ++ [false, true]) (List.ofFn x ++ [v, false, true])
      (st0 n v, []) := by
  refine ⟨by simp [st0], ?_⟩
  intro i
  by_cases hi : i < n
  · show statValid _ ((st0 n v).getD i _) ∧ statVal _ ((st0 n v).getD i _) = _
    rw [st0_lt n v i hi, inp_lt x _ i hi]
    refine ⟨by simp [statValid]; omega, ?_⟩
    show (List.ofFn x ++ [false, true]).getD i false = _
    rw [inp_lt x _ i hi]
  · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    show statValid _ ((st0 n v).getD (n + k) _) ∧ statVal _ ((st0 n v).getD (n + k) _) = _
    rw [st0_add, inp_add]
    rcases k with _ | _ | _ | k <;> simp [statValid, statVal]

theorem J0 (n : ℕ) (v : Bool) :
    J (st0 n v) (fun (x : Fin n → Bool) (y : Bool) => List.ofFn x ++ [y, false, true]) := by
  refine ⟨fun x y => by simp [st0], ?_⟩
  intro i
  by_cases hi : i < n
  · rw [st0_lt n v i hi]
    refine ⟨fun c hc => by simp at hc, fun j _ x y y' => ?_⟩
    show (List.ofFn x ++ [y, false, true]).getD i false = (List.ofFn x ++ [y', false, true]).getD i false
    rw [inp_lt x _ i hi, inp_lt x _ i hi]
  · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    rw [st0_add]
    refine ⟨fun c _ x z y => ?_, fun j hj => ?_⟩
    · show (List.ofFn x ++ [y, false, true]).getD (n + k) false
        = (List.ofFn z ++ [y, false, true]).getD (n + k) false
      rw [inp_add, inp_add]
    · rcases k with _ | _ | _ | k <;> simp at hj

theorem simplify_inr (op : GateOp) (m : ℕ) (ins : List Stat) (g : Gate)
    (hg : (simplify op m ins).1 = some g) : (simplify op m ins).2 = Sum.inr m := by
  cases op <;> simp only [simplify] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simpOr]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp_all [simpNot]
  · simp at hg
  · simp at hg

theorem elim_fresh (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length = acc.2.length + gs.length →
    ∀ i, acc.1.length ≤ i → i < acc.1.length + gs.length →
      ∃ j, (elim n gs acc).1.getD i (Sum.inl false) = Sum.inr j := by
  induction gs with
  | nil => intro acc _ i h1 h2; simp at h2; omega
  | cons g gs ih =>
    intro acc hlen i h1 h2
    rw [elim_cons] at hlen ⊢
    have hA := elim_len n gs (elimStep n acc g)
    have hB : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    simp only [List.length_cons] at hlen h2
    have hC : (elimStep n acc g).1.length = acc.1.length + 1 := by simp [elimStep]
    by_cases hi : i = acc.1.length
    · subst hi
      rw [elim_getD _ _ _ _ _ (by omega)]
      cases ho : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 with
      | none =>
        exfalso
        have : (elimStep n acc g).2.length = acc.2.length := by
          simp only [elimStep, ho]; simp
        omega
      | some g' =>
        refine ⟨n + acc.2.length, ?_⟩
        show (acc.1 ++ [_]).getD acc.1.length _ = _
        rw [getD_snoc_eq]
        exact simplify_inr _ _ _ g' ho
    · exact ih (elimStep n acc g) (by omega) i (by omega) (by omega)

theorem ofFn_snoc {n : ℕ} (x : Fin n → Bool) (y : Bool) :
    List.ofFn (Fin.snoc (α := fun _ => Bool) x y) = List.ofFn x ++ [y] := by
  rw [List.ofFn_succ']
  simp

theorem len_filter_lt {α : Type} (q : α → Bool) : ∀ L : List α,
    (∃ t ∈ L, q t = false) → (L.filter q).length + 1 ≤ L.length
  | [] => by simp
  | t :: L => by
    rintro ⟨t0, ht0, hq0⟩
    have h1 := List.length_filter_le q L
    rw [List.filter_cons]
    rcases List.mem_cons.1 ht0 with rfl | hmem
    · rw [if_neg (by simp [hq0])]; simp only [List.length_cons]; omega
    · have h2 := len_filter_lt q L ⟨t0, hmem, hq0⟩
      split_ifs <;> simp only [List.length_cons] <;> omega

theorem countP_filter_le {α : Type} (q r : α → Bool) : ∀ L : List α,
    (L.filter q).countP r ≤ L.countP r
  | [] => by simp
  | t :: L => by
    have := countP_filter_le q r L
    rw [List.filter_cons]
    split_ifs <;> simp only [List.countP_cons] <;> split_ifs <;> omega

theorem countP_filter_lt {α : Type} (q r : α → Bool) : ∀ L : List α,
    (∃ t ∈ L, r t = true ∧ q t = false) → (L.filter q).countP r + 1 ≤ L.countP r
  | [] => by simp
  | t :: L => by
    rintro ⟨t0, ht0, hr0, hq0⟩
    have h1 := countP_filter_le q r L
    rw [List.filter_cons]
    rcases List.mem_cons.1 ht0 with rfl | hmem
    · rw [if_neg (by simp [hq0])]; simp only [List.countP_cons, hr0, if_true]; omega
    · have h2 := countP_filter_lt q r L ⟨t0, hmem, hr0, hq0⟩
      split_ifs <;> simp only [List.countP_cons] <;> split_ifs <;> omega

theorem lower (n : ℕ) : ∀ (gs : List Gate) (a : Fin n → Bool) (L : List (ℕ × Bool)),
    (∀ g ∈ gs, Ok g) → (∀ t ∈ L, t.1 < n + 2 + gs.length) →
    (∀ x : Fin n → Bool,
      (∀ t ∈ L, (wiresFrom gs (List.ofFn x ++ [false, true])).getD t.1 false = t.2) ↔ x = a) →
    n + cnt gs ≤ L.length + gs.length ∧
    ∀ c : Bool, (List.ofFn a).count c ≤ L.countP (fun t => t.2 == c) + gs.length := by
  induction n with
  | zero =>
    intro gs a L _ _ _
    exact ⟨by have := cnt_le gs; omega, fun c => by simp⟩
  | succ n ih =>
    intro gs a L hok hL H
    obtain ⟨a', v, rfl⟩ : ∃ (a' : Fin n → Bool) (v : Bool),
        a = Fin.snoc (α := fun _ => Bool) a' v := ⟨_, _, (Fin.snoc_init_self a).symm⟩
    set E := elim (n + 2) gs (st0 n v, []) with hE
    obtain ⟨W, hW⟩ : ∃ W : (Fin n → Bool) → Bool → List Bool,
        W = fun x y => List.ofFn x ++ [y, false, true] := ⟨_, rfl⟩
    have HW : ∀ x y, (∀ t ∈ L, (wiresFrom gs (W x y)).getD t.1 false = t.2) ↔
        (x = a' ∧ y = v) := by
      intro x y
      have := H (Fin.snoc (α := fun _ => Bool) x y)
      rw [ofFn_snoc, List.append_assoc] at this
      rw [hW]
      show (∀ t ∈ L, (wiresFrom gs (List.ofFn x ++ ([y] ++ [false, true]))).getD t.1 false
        = t.2) ↔ _
      rw [this]
      constructor
      · intro h
        have h1 := congrArg (Fin.init (α := fun _ => Bool)) h
        have h2 := congrFun h (Fin.last n)
        simp only [Fin.init_snoc, Fin.snoc_last] at h1 h2
        exact ⟨h1, h2⟩
      · rintro ⟨rfl, rfl⟩; rfl
    have hcount : ∀ c, (List.ofFn (Fin.snoc (α := fun _ => Bool) a' v)).count c
        = (List.ofFn a').count c + (if v = c then 1 else 0) := by
      intro c
      rw [ofFn_snoc, List.count_append]
      cases v <;> cases c <;> simp
    have hwv : ∀ x y k, k < 3 → (wiresFrom gs (W x y)).getD (n + k) false
        = [y, false, true].getD k false := by
      intro x y k hk
      rw [getD_wiresFrom _ _ _ (by rw [hW]; simp; omega), hW]
      exact inp_add x _ k
    have hinv : ∀ x : Fin n → Bool, Inv (n + 2) (List.ofFn x ++ [false, true])
        (wiresFrom gs (W x v)) E := by
      intro x; rw [hW]
      exact inv_elim (n + 2) _ (by simp) gs _ _ hok (inv0 n v x)
    have hvalid : ∀ i, statValid (n + 2 + E.2.length) (E.1.getD i (Sum.inl false)) :=
      fun i => ((hinv fun _ => false).2 i).1
    have htap : ∀ i, tapNat n E.1 i < n + 2 + E.2.length := by
      intro i
      have := hvalid i
      unfold tapNat
      cases h : E.1.getD i (Sum.inl false) with
      | inl c => cases c <;> simp <;> omega
      | inr j => rw [h] at this; exact this
    have htapv : ∀ (x : Fin n → Bool) (i : ℕ),
        (wiresFrom E.2 (List.ofFn x ++ [false, true])).getD (tapNat n E.1 i) false
        = (wiresFrom gs (W x v)).getD i false := by
      intro x i
      have := ((hinv x).2 i).2
      unfold tapNat
      cases h : E.1.getD i (Sum.inl false) with
      | inl c =>
        rw [h] at this
        rw [← this, getD_wiresFrom _ _ _ (by cases c <;> simp)]
        cases c
        · exact inp_add x [false, true] 0
        · exact inp_add x [false, true] 1
      | inr j => rw [h] at this; exact this
    obtain ⟨ea, eb, e1, e2, e3⟩ := elim_dich (n + 2) gs (st0 n v, [])
      W hok (hW ▸ J0 n v)
    simp only [List.length_nil, Nat.zero_add] at e1 e2
    rw [← hE] at e1 e2
    have e0 : cnt ([] : List Gate) = 0 := rfl
    rw [e0] at e1
    have hok' : ∀ g ∈ E.2, Ok g := elim_ok (n + 2) gs _ (fun g hg => by simp at hg)
    have hall := (HW a' v).2 ⟨rfl, rfl⟩
    have hflip : (∀ t ∈ L, (wiresFrom gs (W a' (!v))).getD t.1 false
        = (wiresFrom gs (W a' v)).getD t.1 false) → False := by
      intro hh
      have h2 := ((HW a' (!v)).1 (fun t ht => (hh t ht).trans (hall t ht))).2
      cases v <;> simp at h2
    have hgoal : ∀ (q : ℕ × Bool → Bool),
        (∀ t ∈ L, q t = false → ∀ x, (wiresFrom gs (W x v)).getD t.1 false
          = (wiresFrom gs (W a' v)).getD t.1 false) →
        n + cnt E.2 ≤ (L.filter q).length + E.2.length ∧
        ∀ c : Bool, (List.ofFn a').count c
          ≤ (L.filter q).countP (fun t => t.2 == c) + E.2.length := by
      intro q hq
      have := ih E.2 a' ((L.filter q).map fun t => (tapNat n E.1 t.1, t.2)) hok' ?_ ?_
      · simpa [List.countP_map, Function.comp_def] using this
      · intro t ht; obtain ⟨t0, _, rfl⟩ := List.mem_map.1 ht; exact htap _
      · intro x
        constructor
        · intro hx
          refine ((HW x v).1 fun t ht => ?_).1
          by_cases hqt : q t = true
          · have := hx (tapNat n E.1 t.1, t.2)
              (List.mem_map.2 ⟨t, List.mem_filter.2 ⟨ht, hqt⟩, rfl⟩)
            rw [← htapv x t.1]; exact this
          · rw [hq t ht (by simpa using hqt) x]; exact hall t ht
        · intro hx t ht
          subst hx
          obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
          show (wiresFrom E.2 _).getD (tapNat n E.1 t0.1) false = t0.2
          rw [htapv]; exact hall t0 (List.mem_filter.1 ht0).1
    rcases e3 with hb1 | hJ
    · obtain ⟨g1, g2⟩ := hgoal (fun _ => true) (by intro t _ h; simp at h)
      have hf : L.filter (fun _ => true) = L := by simp
      rw [hf] at g1 g2
      refine ⟨by omega, fun c => ?_⟩
      have := g2 c; have := hcount c
      split_ifs at this <;> omega
    · obtain ⟨q, hqdef⟩ : ∃ q : ℕ × Bool → Bool,
          q = fun t => (E.1.getD t.1 (Sum.inl false)).isRight := ⟨_, rfl⟩
      have hqR : ∀ (t : ℕ × Bool) (j : ℕ), E.1.getD t.1 (Sum.inl false) = Sum.inr j →
          q t = true := by
        intro t j hs; rw [hqdef]
        show Sum.isRight (E.1.getD t.1 (Sum.inl false)) = true
        rw [hs]; rfl
      have hqL : ∀ (t : ℕ × Bool) (c : Bool), E.1.getD t.1 (Sum.inl false) = Sum.inl c →
          q t = false := by
        intro t c hs; rw [hqdef]
        show Sum.isRight (E.1.getD t.1 (Sum.inl false)) = false
        rw [hs]; rfl
      have hqX : ∀ t, q t = true → ∀ x y y', (wiresFrom gs (W x y)).getD t.1 false
          = (wiresFrom gs (W x y')).getD t.1 false := by
        intro t ht x y y'
        cases hs : E.1.getD t.1 (Sum.inl false) with
        | inl c => rw [hqL t c hs] at ht; simp at ht
        | inr j => exact (hJ.2 t.1).2 j hs x y y'
      have hqY : ∀ t, q t = false → ∀ x z y, (wiresFrom gs (W x y)).getD t.1 false
          = (wiresFrom gs (W z y)).getD t.1 false := by
        intro t ht x z y
        cases hs : E.1.getD t.1 (Sum.inl false) with
        | inl c => exact (hJ.2 t.1).1 c hs x z y
        | inr j => rw [hqR t j hs] at ht; simp at ht
      obtain ⟨g1, g2⟩ := hgoal q (fun t _ hqt x => hqY t hqt x a' v)
      have hex : ∃ t ∈ L, q t = false := by
        by_contra hne
        push_neg at hne
        exact hflip fun t ht => hqX t (by simpa using hne t ht) a' (!v) v
      have hl := len_filter_lt q L hex
      refine ⟨by omega, fun c => ?_⟩
      have h3 := g2 c
      have h4 := hcount c
      have h5 := countP_filter_le q (fun t => t.2 == c) L
      by_cases hvc : v = c
      · rw [if_pos hvc] at h4
        by_cases hab : 1 ≤ ea + eb
        · omega
        · have hex2 : ∃ t ∈ L, (t.2 == c) = true ∧ q t = false := by
            by_contra hne
            push_neg at hne
            apply hflip
            intro t ht
            by_cases hqt : q t = true
            · exact hqX t hqt a' (!v) v
            · have hqf : q t = false := by simpa using hqt
              have hne' : ¬ (t.2 == c) = true := fun h => by
                have := hne t ht h; simp [hqf] at this
              have hlt : t.1 < n + 3 := by
                by_contra hge
                obtain ⟨j, hj⟩ := elim_fresh (n + 2) gs (st0 n v, [])
                  (by rw [← hE]; simp; omega) t.1 (by simp [st0]; omega)
                  (by have := hL t ht; simp [st0]; omega)
                rw [← hE] at hj
                rw [hqR t j hj] at hqf; simp at hqf
              have hst : E.1.getD t.1 (Sum.inl false) = (st0 n v).getD t.1 (Sum.inl false) := by
                rw [hE]; exact elim_getD _ _ _ _ _ (by simp [st0]; omega)
              by_cases hlt2 : t.1 < n
              · rw [st0_lt n v _ hlt2] at hst
                rw [hqR t _ hst] at hqf; simp at hqf
              · obtain ⟨k, hk⟩ : ∃ k, t.1 = n + k := ⟨t.1 - n, by omega⟩
                have hk3 : k < 3 := by omega
                rw [hk, hwv _ _ _ hk3, hwv _ _ _ hk3]
                have := hall t ht
                rw [hk, hwv _ _ _ hk3] at this
                rcases k with _ | _ | _ | k
                · exfalso; apply hne'; subst hvc; simpa using this.symm
                · rfl
                · rfl
                · omega
          have h6 := countP_filter_lt q (fun t => t.2 == c) L hex2
          omega
      · rw [if_neg hvc] at h4
        omega

def LE (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

theorem mono_wires : ∀ (gs : List Gate), (∀ g ∈ gs, Ok g) → cnt gs = 0 →
    ∀ w w', LE w w' → LE (wiresFrom gs w) (wiresFrom gs w') := by
  intro gs
  induction gs with
  | nil => intro _ _ w w' h; exact h
  | cons g gs ih =>
    intro hok hc w w' h
    have hc' : cnt (g :: gs) = cnt [g] + cnt gs := cnt_append [g] gs
    have hn : g.op ≠ GateOp.not := by
      intro hn; have := cnt_not g hn; omega
    apply ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) (by omega)
    refine ⟨by simp [h.1], ?_⟩
    intro i
    by_cases hi : i = w.length
    · subst hi
      rw [getD_snoc_eq, getD_snoc_len _ _ _ _ h.1.symm]
      rcases (hok g List.mem_cons_self).1 with ho | ho | ho
      · have ho' : g.op = GateOp.and := ho
        rw [ho']
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
        intro hall j hj; exact h.2 j (hall j hj)
      · have ho' : g.op = GateOp.or := ho
        rw [ho']
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
        rintro ⟨j, hj, hv⟩; exact ⟨j, hj, h.2 j hv⟩
      · exact absurd ho hn
    · rw [getD_snoc_ne _ _ _ _ hi, getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hi)]
      exact h.2 i

theorem getD_inp {k : ℕ} (x : Fin k → Bool) (i : ℕ) (hi : i < k) :
    (List.ofFn x ++ [false, true]).getD i false = x ⟨i, hi⟩ := by
  rw [inp_lt x _ i hi]
  simp [List.getD_eq_getElem?_getD, hi]

theorem LE_inp {k : ℕ} (x y : Fin k → Bool) (hxy : ∀ i, x i = true → y i = true) :
    LE (List.ofFn x ++ [false, true]) (List.ofFn y ++ [false, true]) := by
  refine ⟨by simp, ?_⟩
  intro i
  by_cases hi : i < k
  · rw [getD_inp x i hi, getD_inp y i hi]; exact hxy _
  · obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    rw [inp_add, inp_add]; exact id

theorem need_not (k : ℕ) (gs : List Gate) (a : Fin k → Bool) (L : List (ℕ × Bool))
    (hok : ∀ g ∈ gs, Ok g) (hc : cnt gs = 0)
    (H : ∀ x : Fin k → Bool,
      (∀ t ∈ L, (wiresFrom gs (List.ofFn x ++ [false, true])).getD t.1 false = t.2) ↔ x = a)
    (c : Bool) (i0 : Fin k) (hi0 : a i0 = c) (hL : ∀ t ∈ L, t.2 = !c) : False := by
  have hall := (H a).2 rfl
  have hx : Function.update a i0 (!c) = a := by
    apply (H _).1
    intro t ht
    have h1 := hall t ht
    rw [hL t ht] at h1 ⊢
    cases c
    ·
      have := (mono_wires gs hok hc _ _ (LE_inp a (Function.update a i0 (!false)) (by
        intro i hi
        by_cases hii : i = i0
        · subst hii; simp
        · rw [Function.update_of_ne hii]; exact hi))).2 t.1 h1
      exact this
    ·
      have hle := (mono_wires gs hok hc _ _ (LE_inp (Function.update a i0 (!true)) a (by
        intro i hi
        by_cases hii : i = i0
        · subst hii; simp at hi
        · rw [Function.update_of_ne hii] at hi; exact hi))).2 t.1
      cases hv : (wiresFrom gs (List.ofFn (Function.update a i0 (!true)) ++ [false, true])).getD
        t.1 false with
      | false => rfl
      | true => rw [hle hv] at h1; simp at h1
  have := congrFun hx i0
  rw [Function.update_self, hi0] at this
  cases c <;> simp at this

theorem card_eq_count : ∀ {k : ℕ} (a : Fin k → Bool) (c : Bool),
    (Finset.univ.filter (fun i => a i = c)).card = (List.ofFn a).count c := by
  intro k
  induction k with
  | zero => intro a c; simp
  | succ k ih =>
    intro a c
    rw [Fin.card_filter_univ_succ', List.ofFn_succ, List.count_cons, ← ih]
    simp only [Function.comp_def, beq_iff_eq]
    omega

theorem count_bool : ∀ l : List Bool, l.count true + l.count false = l.length
  | [] => rfl
  | x :: l => by
    have := count_bool l
    cases x <;> simp [List.count_cons] <;> omega

theorem countP_ofFn_snd : ∀ {m : ℕ} (f : Fin m → ℕ × Bool) (c : Bool),
    (List.ofFn f).countP (fun t => t.2 == c) = (List.ofFn fun j => (f j).2).count c := by
  intro m
  induction m with
  | zero => intro f c; simp
  | succ m ih =>
    intro f c
    rw [List.ofFn_succ, List.ofFn_succ, List.countP_cons, List.count_cons, ih]

theorem lowerMain (k m : ℕ) (a : Fin k → Bool) (h : Fin m → Bool) (s b r : ℕ)
    (H : ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (k+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) C ∧
      C.output < k+2+C.size ∧ C.size ≤ s ∧ C.size - PEqualNP.NotBracket.notCount C ≤ b ∧
      PEqualNP.NotBracket.notCount C ≤ r ∧ ∀ x : Fin k → Bool,
        let w := C.wires (List.ofFn x ++ [false,true])
        ((∀ j, w.getD (tap j).val false = h j) ↔ x = a)) :
    let p := (Finset.univ.filter (fun i => a i = true)).card
    let z := k-p
    let u := (Finset.univ.filter (fun j => h j = true)).card
    let v := m-u
    let M := min p u + min z v
    let d := if (0 < p ∧ u = 0) ∨ (0 < z ∧ v = 0) then 1 else 0
    let g := min (min k m) (M+r)
    (k = 0 ∨ 0 < m) ∧ d ≤ r ∧ k-g ≤ b ∧ k-g + max d (g-M) ≤ s := by
  obtain ⟨C, tap, hF, -, -, hs, hb, hr, H⟩ := H
  intro p z u v M d g
  have hp : p = (List.ofFn a).count true := card_eq_count a true
  have hu : u = (List.ofFn h).count true := card_eq_count h true
  have hz : z = k - p := rfl
  have hv : v = m - u := rfl
  have hM : M = min p u + min z v := rfl
  have hd : d = if (0 < p ∧ u = 0) ∨ (0 < z ∧ v = 0) then 1 else 0 := rfl
  have hg : g = min (min k m) (M+r) := rfl
  clear_value p z u v M d g
  have hok : ∀ g ∈ C.gates, Ok g := hF
  have hsz : C.size = C.gates.length := rfl
  have hnc : PEqualNP.NotBracket.notCount C = cnt C.gates := rfl
  rw [hsz] at hs hb
  rw [hnc] at hb hr
  obtain ⟨L, hLdef⟩ : ∃ L : List (ℕ × Bool), L = List.ofFn fun j => ((tap j).val, h j) :=
    ⟨_, rfl⟩
  have HH : ∀ x : Fin k → Bool,
      (∀ t ∈ L, (wiresFrom C.gates (List.ofFn x ++ [false, true])).getD t.1 false = t.2)
        ↔ x = a := by
    intro x
    have Hx : (∀ j, (wiresFrom C.gates (List.ofFn x ++ [false, true])).getD (tap j).val false
        = h j) ↔ x = a := H x
    rw [← Hx, hLdef]
    constructor
    · intro hx j; exact hx _ ((List.mem_ofFn' _ _).2 ⟨j, rfl⟩)
    · intro hx t ht
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ht
      exact hx j
  have hLb : ∀ t ∈ L, t.1 < k + 2 + C.gates.length := by
    intro t ht
    rw [hLdef] at ht
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ht
    exact (tap j).2
  obtain ⟨l1, l2⟩ := lower k C.gates a L hok hLb HH
  have hLl : L.length = m := by rw [hLdef]; simp
  have hLc : ∀ c, L.countP (fun t => t.2 == c) = (List.ofFn h).count c := by
    intro c
    rw [hLdef]; exact countP_ofFn_snd _ c
  have hca := count_bool (List.ofFn a)
  have hch := count_bool (List.ofFn h)
  simp only [List.length_ofFn] at hca hch
  have l2t := l2 true
  have l2f := l2 false
  rw [hLc] at l2t l2f
  have hcl := cnt_le C.gates
  have hm : k = 0 ∨ 0 < m := by
    by_contra hne
    push_neg at hne
    have hm0 : m = 0 := by omega
    have hL0 : L = [] := List.length_eq_zero_iff.1 (by omega)
    have hk : 0 < k := by omega
    have h1 := (HH (Function.update a ⟨0, hk⟩ (!a ⟨0, hk⟩))).1 (by rw [hL0]; simp)
    have := congrFun h1 ⟨0, hk⟩
    rw [Function.update_self] at this
    cases hh : a ⟨0, hk⟩ <;> rw [hh] at this <;> simp at this
  have hdr : d ≤ cnt C.gates := by
    by_contra hne
    have hc0 : cnt C.gates = 0 := by
      rw [hd] at hne; split_ifs at hne <;> omega
    have hd1 : (0 < p ∧ u = 0) ∨ (0 < z ∧ v = 0) := by
      by_contra hcon; rw [hd, if_neg hcon] at hne; omega
    rcases hd1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : true ∈ List.ofFn a := List.count_pos_iff.1 (by omega)
      obtain ⟨i0, hi0⟩ := (List.mem_ofFn' _ _).1 this
      refine need_not k C.gates a L hok hc0 HH true i0 hi0 ?_
      intro t ht
      rw [hLdef] at ht
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ht
      have hnot : true ∉ List.ofFn h := fun hmem => by
        have := List.count_pos_iff.2 hmem; omega
      cases hj : h j
      · show h j = !true
        rw [hj]; rfl
      · exact absurd ((List.mem_ofFn' _ _).2 ⟨j, hj⟩) hnot
    · have : false ∈ List.ofFn a := List.count_pos_iff.1 (by omega)
      obtain ⟨i0, hi0⟩ := (List.mem_ofFn' _ _).1 this
      refine need_not k C.gates a L hok hc0 HH false i0 hi0 ?_
      intro t ht
      rw [hLdef] at ht
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ht
      have hnot : false ∉ List.ofFn h := fun hmem => by
        have := List.count_pos_iff.2 hmem; omega
      cases hj : h j
      · exact absurd ((List.mem_ofFn' _ _).2 ⟨j, hj⟩) hnot
      · show h j = !false
        rw [hj]; rfl
  refine ⟨hm, by omega, by omega, ?_⟩
  rw [hd] at hdr ⊢
  split_ifs at hdr ⊢ <;> omega

def wfC (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wfC_append (gs gs' : List Gate) (w : List Bool) :
    wfC (gs ++ gs') w = wfC gs' (wfC gs w) := by
  simp [wfC, List.foldl_append]

theorem wfC_front (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wfC gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wfC], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wfC (g :: gs) w
        = wfC gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem wfC_length (gs : List Gate) (w : List Bool) :
    (wfC gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wfC_front gs w
  rw [ht]; simp [hl]

theorem wfC_getD (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wfC gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wfC_front gs w
  rw [ht, List.getD_append _ _ _ _ h]

def inC {k : ℕ} (x : Fin k → Bool) : List Bool := List.ofFn x ++ [false, true]

theorem inC_length {k : ℕ} (x : Fin k → Bool) : (inC x).length = k + 2 := by simp [inC]

def VC {k : ℕ} (gs : List Gate) (x : Fin k → Bool) (i : ℕ) : Bool :=
  (wfC gs (inC x)).getD i false

theorem VC_old {k : ℕ} (gs ext : List Gate) (x : Fin k → Bool) (i : ℕ)
    (h : i < k + 2 + gs.length) : VC (gs ++ ext) x i = VC gs x i := by
  unfold VC
  rw [wfC_append, wfC_getD _ _ _ (by rw [wfC_length, inC_length]; exact h)]

theorem VC_new {k : ℕ} (gs : List Gate) (g : Gate) (x : Fin k → Bool) :
    VC (gs ++ [g]) x (k + 2 + gs.length) = g.op.eval (g.inputs.map fun i => VC gs x i) := by
  unfold VC
  rw [wfC_append]
  have hl : (wfC gs (inC x)).length = k + 2 + gs.length := by rw [wfC_length, inC_length]
  show ((wfC gs (inC x)) ++ [_]).getD _ false = _
  rw [← hl]; simp

theorem VC_inp {k : ℕ} (gs : List Gate) (x : Fin k → Bool) (t : Fin k) :
    VC gs x t.val = x t := by
  unfold VC
  rw [wfC_getD _ _ _ (by rw [inC_length]; omega)]
  unfold inC
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem VC_false {k : ℕ} (gs : List Gate) (x : Fin k → Bool) : VC gs x k = false := by
  unfold VC
  rw [wfC_getD _ _ _ (by rw [inC_length]; omega)]
  unfold inC
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem VC_true {k : ℕ} (gs : List Gate) (x : Fin k → Bool) : VC gs x (k + 1) = true := by
  unfold VC
  rw [wfC_getD _ _ _ (by rw [inC_length]; omega)]
  unfold inC
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

def OkC (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def GoodC (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, OkC g) ∧ ∀ j g, gs[j]? = some g → ∀ i ∈ g.inputs, i < n + j

theorem GoodC_nil (n : ℕ) : GoodC n [] :=
  ⟨fun g hg => by simp at hg, fun j g hg => by simp at hg⟩

theorem GoodC_snoc {n : ℕ} {gs : List Gate} (hG : GoodC n gs) (g : Gate) (hg : OkC g)
    (hi : ∀ i ∈ g.inputs, i < n + gs.length) : GoodC n (gs ++ [g]) := by
  refine ⟨fun g' hg' => ?_, fun j g' hj => ?_⟩
  · rcases List.mem_append.1 hg' with h | h
    · exact hG.1 g' h
    · simp at h; subst h; exact hg
  · by_cases hlt : j < gs.length
    · rw [List.getElem?_append_left hlt] at hj
      exact hG.2 j g' hj
    · rw [List.getElem?_append_right (by omega)] at hj
      have hp0 : j - gs.length = 0 := by
        have := (List.getElem?_eq_some_iff.1 hj).1
        simp at this; omega
      rw [hp0] at hj
      simp at hj
      subst hj
      have : j = gs.length := by omega
      subst this
      exact hi

def cntC (gs : List Gate) : ℕ := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem cntC_append (a b : List Gate) : cntC (a ++ b) = cntC a + cntC b := by
  simp [cntC, PEqualNP.NotBracket.notCount, List.filter_append]

theorem cntC_nil : cntC [] = 0 := rfl

def TapC {k : ℕ} (a : Fin k → Bool) (gs : List Gate) (w : ℕ) (η : Bool) (G : Finset (Fin k)) :
    Prop :=
  w < k + 2 + gs.length ∧ ∀ x : Fin k → Bool, (VC gs x w = η ↔ ∀ t ∈ G, x t = a t)

theorem TapC_mono {k : ℕ} {a : Fin k → Bool} {gs : List Gate} {w : ℕ} {η : Bool}
    {G : Finset (Fin k)} (h : TapC a gs w η G) (ext : List Gate) : TapC a (gs ++ ext) w η G := by
  refine ⟨by simp; have := h.1; omega, fun x => ?_⟩
  rw [VC_old _ _ _ _ h.1]; exact h.2 x

theorem TapC_fold {k : ℕ} {a : Fin k → Bool} {gs : List Gate} {w : ℕ} {η : Bool}
    {G : Finset (Fin k)} (h : TapC a gs w η G) (t : Fin k) (ht : a t = η) :
    TapC a (gs ++ [⟨bif η then GateOp.and else GateOp.or, [w, t.val]⟩]) (k + 2 + gs.length) η
      (insert t G) := by
  refine ⟨by simp, fun x => ?_⟩
  rw [VC_new, Finset.forall_mem_insert, ← h.2 x]
  simp only [List.map, VC_inp]
  subst ht
  cases hη : a t <;> cases hx : x t <;> cases hw : VC gs x w <;> simp [GateOp.eval]

theorem TapC_flip {k : ℕ} {a : Fin k → Bool} {gs : List Gate} {w : ℕ} {η : Bool}
    {G : Finset (Fin k)} (h : TapC a gs w η G) :
    TapC a (gs ++ [⟨GateOp.not, [w]⟩]) (k + 2 + gs.length) (!η) G := by
  refine ⟨by simp, fun x => ?_⟩
  rw [VC_new, ← h.2 x]
  cases η <;> cases hw : VC gs x w <;> simp [GateOp.eval, hw]

theorem foldC {k : ℕ} (a : Fin k → Bool) (η : Bool) : ∀ (G : Finset (Fin k)),
    (∀ t ∈ G, a t = η) → ∀ (gs : List Gate) (w : ℕ) (G0 : Finset (Fin k)),
    GoodC (k + 2) gs → TapC a gs w η G0 →
    ∃ (ext : List Gate) (w' : ℕ), GoodC (k + 2) (gs ++ ext) ∧ TapC a (gs ++ ext) w' η (G0 ∪ G) ∧
      cntC ext = 0 ∧ ext.length = G.card := by
  intro G
  induction G using Finset.induction_on with
  | empty =>
    intro _ gs w G0 hG hT
    exact ⟨[], w, by simpa using hG, by simpa using hT, rfl, rfl⟩
  | insert t G' ht ih =>
    intro hall gs w G0 hG hT
    obtain ⟨ext, w', hG', hT', hc, hl⟩ := ih (fun t' h' => hall t' (Finset.mem_insert_of_mem h'))
      gs w G0 hG hT
    have hat := hall t (Finset.mem_insert_self _ _)
    refine ⟨ext ++ [⟨bif η then GateOp.and else GateOp.or, [w', t.val]⟩], k + 2 + (gs ++ ext).length,
      ?_, ?_, ?_, ?_⟩
    · rw [← List.append_assoc]
      refine GoodC_snoc hG' _ ⟨by cases η <;> simp, by simp⟩ ?_
      intro i hi
      simp at hi
      rcases hi with rfl | rfl
      · exact hT'.1
      · have := t.isLt; omega
    · rw [← List.append_assoc, Finset.union_insert]
      exact TapC_fold hT' t hat
    · rw [cntC_append, hc]
      cases η <;> simp [cntC, PEqualNP.NotBracket.notCount]
    · simp [hl, Finset.card_insert_of_notMem ht]

theorem pureC {k : ℕ} (a : Fin k → Bool) (η : Bool) (G : Finset (Fin k))
    (hall : ∀ t ∈ G, a t = η) (gs : List Gate) (hG : GoodC (k + 2) gs) :
    ∃ (ext : List Gate) (w' : ℕ), GoodC (k + 2) (gs ++ ext) ∧ TapC a (gs ++ ext) w' η G ∧
      cntC ext = 0 ∧ ext.length + (if G.Nonempty then 1 else 0) = G.card := by
  by_cases hne : G.Nonempty
  · obtain ⟨t0, ht0⟩ := hne
    have hT0 : TapC a gs t0.val η {t0} := by
      refine ⟨by have := t0.isLt; omega, fun x => ?_⟩
      rw [VC_inp, ← hall t0 ht0]; simp
    obtain ⟨ext, w', h1, h2, h3, h4⟩ := foldC a η (G.erase t0)
      (fun t h => hall t (Finset.mem_of_mem_erase h)) gs t0.val {t0} hG hT0
    refine ⟨ext, w', h1, ?_, h3, ?_⟩
    · have : ({t0} : Finset (Fin k)) ∪ G.erase t0 = G := by
        rw [← Finset.insert_eq, Finset.insert_erase ht0]
      rwa [this] at h2
    · rw [if_pos ⟨t0, ht0⟩, h4, Finset.card_erase_of_mem ht0]
      have := Finset.card_pos.2 ⟨t0, ht0⟩
      omega
  · have hE : G = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    subst hE
    refine ⟨[], bif η then k + 1 else k, by simpa using hG, ?_, rfl, by simp⟩
    refine ⟨by cases η <;> simp <;> omega, fun x => ?_⟩
    cases η <;> simp [VC_false, VC_true]

theorem tapC {k : ℕ} (a : Fin k → Bool) (η : Bool) (G : Finset (Fin k))
    (gs : List Gate) (hG : GoodC (k + 2) gs) :
    ∃ (ext : List Gate) (w' : ℕ), GoodC (k + 2) (gs ++ ext) ∧ TapC a (gs ++ ext) w' η G ∧
      cntC ext ≤ 1 ∧ ((∀ t ∈ G, a t = η) → cntC ext = 0) ∧
      ext.length + (if G.Nonempty then 1 else 0) = G.card + cntC ext := by
  by_cases hall : ∀ t ∈ G, a t = η
  · obtain ⟨ext, w', h1, h2, h3, h4⟩ := pureC a η G hall gs hG
    exact ⟨ext, w', h1, h2, by omega, fun _ => h3, by omega⟩
  · have hne : (G.filter fun t => ¬ a t = η).Nonempty := by
      by_contra hc
      apply hall
      intro t ht
      by_contra hc2
      exact hc ⟨t, Finset.mem_filter.2 ⟨ht, hc2⟩⟩
    have hGne : G.Nonempty := hne.mono (Finset.filter_subset _ _)
    obtain ⟨e1, w1, a1, a2, a3, a4⟩ := pureC a (!η) (G.filter fun t => ¬ a t = η)
      (fun t ht => by
        have := (Finset.mem_filter.1 ht).2
        revert this; cases a t <;> cases η <;> simp) gs hG
    rw [if_pos hne] at a4
    have b2 := TapC_flip a2
    rw [Bool.not_not] at b2
    have b1 : GoodC (k + 2) ((gs ++ e1) ++ [⟨GateOp.not, [w1]⟩]) := by
      refine GoodC_snoc a1 _ ⟨by simp, by simp⟩ ?_
      intro i hi
      simp at hi
      subst hi
      exact a2.1
    obtain ⟨e3, w3, c1, c2, c3, c4⟩ := foldC a η (G.filter fun t => a t = η)
      (fun t ht => (Finset.mem_filter.1 ht).2) _ _ _ b1 b2
    have hcard := Finset.card_filter_add_card_filter_not (s := G) (fun t => a t = η)
    refine ⟨e1 ++ [⟨GateOp.not, [w1]⟩] ++ e3, w3, ?_, ?_, ?_, fun h => absurd h hall, ?_⟩
    · simpa [List.append_assoc] using c1
    · have hU : (G.filter fun t => ¬ a t = η) ∪ (G.filter fun t => a t = η) = G := by
        rw [Finset.union_comm]; exact Finset.filter_union_filter_not_eq _ _
      rw [hU] at c2
      simpa [List.append_assoc] using c2
    · rw [cntC_append, cntC_append, a3, c3]
      simp [cntC, PEqualNP.NotBracket.notCount]
    · rw [if_pos hGne, cntC_append, cntC_append, a3, c3]
      simp [cntC, PEqualNP.NotBracket.notCount]
      omega

theorem allC {k m : ℕ} (a : Fin k → Bool) (h : Fin m → Bool) (G : Fin m → Finset (Fin k)) :
    ∀ J : Finset (Fin m), ∃ (gs : List Gate) (w : Fin m → ℕ), GoodC (k + 2) gs ∧
      (∀ j ∈ J, TapC a gs (w j) (h j) (G j)) ∧
      cntC gs ≤ (J.filter fun j => ¬ ∀ t ∈ G j, a t = h j).card ∧
      gs.length + (J.filter fun j => (G j).Nonempty).card = ∑ j ∈ J, (G j).card + cntC gs := by
  intro J
  induction J using Finset.induction_on with
  | empty => exact ⟨[], fun _ => 0, GoodC_nil _, by simp, by simp [cntC_nil], by simp [cntC_nil]⟩
  | insert j J' hj ih =>
    obtain ⟨gs, w, hG, hT, hc, hl⟩ := ih
    obtain ⟨ext, w', e1, e2, e3, e4, e5⟩ := tapC a (h j) (G j) gs hG
    refine ⟨gs ++ ext, Function.update w j w', e1, ?_, ?_, ?_⟩
    · intro j' hj'
      rcases Finset.mem_insert.1 hj' with rfl | h'
      · simpa using e2
      · have hne : j' ≠ j := fun e => hj (e ▸ h')
        rw [Function.update_of_ne hne]
        exact TapC_mono (hT j' h') ext
    · rw [cntC_append, Finset.filter_insert]
      by_cases hb : ∀ t ∈ G j, a t = h j
      · rw [if_neg (not_not.2 hb), e4 hb]; omega
      · rw [if_pos hb, Finset.card_insert_of_notMem (fun hh => hj (Finset.mem_filter.1 hh).1)]
        omega
    · rw [cntC_append, Finset.filter_insert, Finset.sum_insert hj, List.length_append]
      by_cases hb : (G j).Nonempty
      · rw [if_pos hb, Finset.card_insert_of_notMem (fun hh => hj (Finset.mem_filter.1 hh).1)]
        rw [if_pos hb] at e5
        omega
      · rw [if_neg hb]
        rw [if_neg hb] at e5
        omega

theorem pairC {k m : ℕ} (A : Finset (Fin k)) (B : Finset (Fin m)) (n : ℕ) (hA : n ≤ A.card)
    (hB : n ≤ B.card) (j0 : Fin m) :
    ∃ (A' : Finset (Fin k)) (f : Fin k → Fin m), A' ⊆ A ∧ A'.card = n ∧ (∀ t ∈ A', f t ∈ B) ∧
      Set.InjOn f A' := by
  obtain ⟨A', hs, hc⟩ := Finset.exists_subset_card_eq hA
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset (α := A') (s := B)
    (by rw [Fintype.card_coe, hc]; exact hB)
  refine ⟨A', fun t => if ht : t ∈ A' then e ⟨t, ht⟩ else j0, hs, hc, ?_, ?_⟩
  · intro t ht
    simp only [dif_pos ht]
    exact Finset.mem_coe.1 (he ⟨_, rfl⟩)
  · intro t ht t' ht' heq
    simp only [dif_pos (Finset.mem_coe.1 ht), dif_pos (Finset.mem_coe.1 ht')] at heq
    exact congrArg Subtype.val (e.injective heq)

theorem phiC (k m : ℕ) (a : Fin k → Bool) (h : Fin m → Bool) (r : ℕ)
    (p z u v M d g : ℕ)
    (hp : p = (Finset.univ.filter (fun i => a i = true)).card) (hz : z = k - p)
    (hu : u = (Finset.univ.filter (fun j => h j = true)).card) (hv : v = m - u)
    (hM : M = min p u + min z v)
    (hd : d = if (0 < p ∧ u = 0) ∨ (0 < z ∧ v = 0) then 1 else 0)
    (hg : g = min (min k m) (M + r)) (hkm : k = 0 ∨ 0 < m) (hdr : d ≤ r) :
    ∃ φ : Fin k → Fin m, g ≤ (Finset.univ.image φ).card ∧
      (Finset.univ.filter fun j => ∃ t, φ t = j ∧ a t ≠ h j).card ≤ max d (g - M) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    refine ⟨fun t => t.elim0, by omega, ?_⟩
    have : (Finset.univ.filter fun j : Fin m => ∃ t : Fin 0, t.elim0 = j ∧ a t ≠ h j) = ∅ := by
      ext j
      simp
    rw [this]; simp
  have hm : 0 < m := by omega
  have hPZ := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (fun i => a i = true)
  have hUV := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun j => h j = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hPZ hUV
  rw [← hp] at hPZ
  rw [← hu] at hUV
  obtain ⟨A1, f1, hA1, hc1, hf1, hi1⟩ := pairC (Finset.univ.filter (fun i => a i = true))
    (Finset.univ.filter (fun j => h j = true)) (min p u) (by omega) (by omega) ⟨0, hm⟩
  obtain ⟨A2, f2, hA2, hc2, hf2, hi2⟩ := pairC (Finset.univ.filter (fun i => ¬ a i = true))
    (Finset.univ.filter (fun j => ¬ h j = true)) (min z v) (by omega) (by omega) ⟨0, hm⟩
  have hB1 : (A1.image f1).card = min p u := by rw [Finset.card_image_of_injOn hi1, hc1]
  have hB2 : (A2.image f2).card = min z v := by rw [Finset.card_image_of_injOn hi2, hc2]
  have hRa : g - M ≤ (Finset.univ \ (A1 ∪ A2)).card := by
    have h1 := Finset.le_card_sdiff (A1 ∪ A2) Finset.univ
    have h2 := Finset.card_union_le A1 A2
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hRb : g - M ≤ (Finset.univ \ (A1.image f1 ∪ A2.image f2)).card := by
    have h1 := Finset.le_card_sdiff (A1.image f1 ∪ A2.image f2) Finset.univ
    have h2 := Finset.card_union_le (A1.image f1) (A2.image f2)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨A3, f3, hA3, hc3, hf3, hi3⟩ := pairC _ _ (g - M) hRa hRb ⟨0, hm⟩
  have hB3 : (A3.image f3).card = g - M := by rw [Finset.card_image_of_injOn hi3, hc3]
  obtain ⟨jP, hjP⟩ : ∃ jP : Fin m, h jP = true ∨ jP ∈ A3.image f3 ∨ (u = 0 ∧ g - M = 0) := by
    by_cases hu0 : u = 0
    · by_cases he0 : g - M = 0
      · exact ⟨⟨0, hm⟩, Or.inr (Or.inr ⟨hu0, he0⟩)⟩
      · obtain ⟨j, hj⟩ := Finset.card_pos.1 (by rw [hB3]; omega : 0 < (A3.image f3).card)
        exact ⟨j, Or.inr (Or.inl hj)⟩
    · obtain ⟨j, hj⟩ := Finset.card_pos.1
        (by rw [← hu]; omega : 0 < (Finset.univ.filter (fun j => h j = true)).card)
      exact ⟨j, Or.inl (Finset.mem_filter.1 hj).2⟩
  obtain ⟨jZ, hjZ⟩ : ∃ jZ : Fin m, ¬ h jZ = true ∨ jZ ∈ A3.image f3 ∨ (v = 0 ∧ g - M = 0) := by
    by_cases hv0 : v = 0
    · by_cases he0 : g - M = 0
      · exact ⟨⟨0, hm⟩, Or.inr (Or.inr ⟨hv0, he0⟩)⟩
      · obtain ⟨j, hj⟩ := Finset.card_pos.1 (by rw [hB3]; omega : 0 < (A3.image f3).card)
        exact ⟨j, Or.inr (Or.inl hj)⟩
    · obtain ⟨j, hj⟩ := Finset.card_pos.1
        (by omega : 0 < (Finset.univ.filter (fun j => ¬ h j = true)).card)
      exact ⟨j, Or.inl (Finset.mem_filter.1 hj).2⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin k → Fin m, ∀ t, φ t = if t ∈ A1 then f1 t else if t ∈ A2 then f2 t
      else if t ∈ A3 then f3 t else if a t = true then jP else jZ := ⟨_, fun _ => rfl⟩
  have m1 : ∀ t ∈ A1, a t = true := fun t ht => (Finset.mem_filter.1 (hA1 ht)).2
  have m2 : ∀ t ∈ A2, ¬ a t = true := fun t ht => (Finset.mem_filter.1 (hA2 ht)).2
  have m3 : ∀ t ∈ A3, t ∉ A1 ∧ t ∉ A2 := fun t ht => by
    have := (Finset.mem_sdiff.1 (hA3 ht)).2
    rw [Finset.mem_union] at this
    exact ⟨fun h1 => this (Or.inl h1), fun h2 => this (Or.inr h2)⟩
  have n1 : ∀ t ∈ A1, h (f1 t) = true := fun t ht => (Finset.mem_filter.1 (hf1 t ht)).2
  have n2 : ∀ t ∈ A2, ¬ h (f2 t) = true := fun t ht => (Finset.mem_filter.1 (hf2 t ht)).2
  have n3 : ∀ t ∈ A3, f3 t ∉ A1.image f1 ∧ f3 t ∉ A2.image f2 := fun t ht => by
    have := (Finset.mem_sdiff.1 (hf3 t ht)).2
    rw [Finset.mem_union] at this
    exact ⟨fun h1 => this (Or.inl h1), fun h2 => this (Or.inr h2)⟩
  have p1 : ∀ t ∈ A1, φ t = f1 t := fun t ht => by rw [hφ, if_pos ht]
  have p2 : ∀ t ∈ A2, φ t = f2 t := fun t ht => by
    rw [hφ, if_neg (fun h1 => m2 t ht (m1 t h1)), if_pos ht]
  have p3 : ∀ t ∈ A3, φ t = f3 t := fun t ht => by
    rw [hφ, if_neg (m3 t ht).1, if_neg (m3 t ht).2, if_pos ht]
  refine ⟨φ, ?_, ?_⟩
  · have hsub : A1.image f1 ∪ A2.image f2 ∪ A3.image f3 ⊆ Finset.univ.image φ := by
      intro j hj
      rw [Finset.mem_union, Finset.mem_union] at hj
      rcases hj with (hj | hj) | hj
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
        exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, p1 t ht⟩
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
        exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, p2 t ht⟩
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
        exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, p3 t ht⟩
    have hd12 : Disjoint (A1.image f1) (A2.image f2) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj1
      obtain ⟨t', ht', he⟩ := Finset.mem_image.1 hj2
      exact n2 t' ht' (he ▸ n1 t ht)
    have hd3 : Disjoint (A1.image f1 ∪ A2.image f2) (A3.image f3) := by
      rw [Finset.disjoint_right]
      intro j hj3 hj
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj3
      rw [Finset.mem_union] at hj
      rcases hj with hj | hj
      · exact (n3 t ht).1 hj
      · exact (n3 t ht).2 hj
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12, hB1, hB2, hB3]
      at hcard
    omega
  · have key : ∀ j, (∃ t, φ t = j ∧ a t ≠ h j) → j ∈ A3.image f3 ∨
        (j = jP ∧ u = 0 ∧ g - M = 0 ∧ 0 < p) ∨ (j = jZ ∧ v = 0 ∧ g - M = 0 ∧ 0 < z) := by
      rintro j ⟨t, rfl, hne⟩
      by_cases h1 : t ∈ A1
      · exact absurd ((m1 t h1).trans (by rw [p1 t h1]; exact (n1 t h1).symm)) hne
      by_cases h2 : t ∈ A2
      · exfalso
        have e1 := m2 t h2
        have e2 := n2 t h2
        rw [← p2 t h2] at e2
        revert hne e1 e2
        cases a t <;> cases h (φ t) <;> simp
      by_cases h3 : t ∈ A3
      · exact Or.inl (Finset.mem_image.2 ⟨t, h3, (p3 t h3).symm⟩)
      have hφt := hφ t
      rw [if_neg h1, if_neg h2, if_neg h3] at hφt
      by_cases hat : a t = true
      · rw [if_pos hat] at hφt
        have hppos : 0 < p := by
          rw [hp]; exact Finset.card_pos.2 ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, hat⟩⟩
        rcases hjP with e | e | e
        · exact absurd (hat.trans (by rw [hφt]; exact e.symm)) hne
        · exact Or.inl (hφt ▸ e)
        · exact Or.inr (Or.inl ⟨hφt, e.1, e.2, hppos⟩)
      · rw [if_neg hat] at hφt
        have hzpos : 0 < (Finset.univ.filter (fun i => ¬ a i = true)).card :=
          Finset.card_pos.2 ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, hat⟩⟩
        rcases hjZ with e | e | e
        · exfalso
          rw [← hφt] at e
          revert hne hat e
          cases a t <;> cases h (φ t) <;> simp
        · exact Or.inl (hφt ▸ e)
        · exact Or.inr (Or.inr ⟨hφt, e.1, e.2, by omega⟩)
    by_cases he0 : g - M = 0
    · have hB3e : A3.image f3 = ∅ := Finset.card_eq_zero.1 (by rw [hB3, he0])
      by_cases hx : 0 < p ∧ u = 0
      · have hd1 : d = 1 := by rw [hd, if_pos (Or.inl hx)]
        have : (Finset.univ.filter fun j => ∃ t, φ t = j ∧ a t ≠ h j) ⊆ {jP} := by
          intro j hj
          rcases key j (Finset.mem_filter.1 hj).2 with e | e | e
          · rw [hB3e] at e; simp at e
          · simp [e.1]
          · omega
        have := Finset.card_le_card this
        rw [Finset.card_singleton] at this
        omega
      by_cases hy : 0 < z ∧ v = 0
      · have hd1 : d = 1 := by rw [hd, if_pos (Or.inr hy)]
        have : (Finset.univ.filter fun j => ∃ t, φ t = j ∧ a t ≠ h j) ⊆ {jZ} := by
          intro j hj
          rcases key j (Finset.mem_filter.1 hj).2 with e | e | e
          · rw [hB3e] at e; simp at e
          · omega
          · simp [e.1]
        have := Finset.card_le_card this
        rw [Finset.card_singleton] at this
        omega
      · have : (Finset.univ.filter fun j => ∃ t, φ t = j ∧ a t ≠ h j) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro j hj
          rcases key j (Finset.mem_filter.1 hj).2 with e | e | e
          · rw [hB3e] at e; simp at e
          · omega
          · omega
        rw [this]; simp
    · have : (Finset.univ.filter fun j => ∃ t, φ t = j ∧ a t ≠ h j) ⊆ A3.image f3 := by
        intro j hj
        rcases key j (Finset.mem_filter.1 hj).2 with e | e | e
        · exact e
        · omega
        · omega
      have := Finset.card_le_card this
      rw [hB3] at this
      omega

theorem consMain (k m : ℕ) (a : Fin k → Bool) (h : Fin m → Bool) (s b r : ℕ)
  (H : let p := (Finset.univ.filter (fun i => a i = true)).card
    let z := k-p
    let u := (Finset.univ.filter (fun j => h j = true)).card
    let v := m-u
    let M := min p u + min z v
    let d := if (0 < p ∧ u = 0) ∨ (0 < z ∧ v = 0) then 1 else 0
    let g := min (min k m) (M+r)
    (k = 0 ∨ 0 < m) ∧ d ≤ r ∧ k-g ≤ b ∧ k-g + max d (g-M) ≤ s) :
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (k+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) C ∧
    C.output < k+2+C.size ∧ C.size ≤ s ∧ C.size - PEqualNP.NotBracket.notCount C ≤ b ∧
    PEqualNP.NotBracket.notCount C ≤ r ∧ ∀ x : Fin k → Bool,
      let w := C.wires (List.ofFn x ++ [false,true])
      ((∀ j, w.getD (tap j).val false = h j) ↔ x = a) := by
  obtain ⟨hkm, hdr, hb, hs⟩ := H
  obtain ⟨φ, hφ1, hφ2⟩ := phiC k m a h r _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl hkm hdr
  obtain ⟨gs, w, hG, hT, hc, hl⟩ := allC a h (fun j => Finset.univ.filter fun t => φ t = j)
    Finset.univ
  have hsum : ∑ j : Fin m, (Finset.univ.filter fun t => φ t = j).card = k := by
    have := Finset.card_eq_sum_card_fiberwise (f := φ) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    simpa using this.symm
  have him : (Finset.univ.filter fun j => (Finset.univ.filter fun t => φ t = j).Nonempty)
      = Finset.univ.image φ := by
    ext j
    simp [Finset.filter_nonempty_iff]
  have hbad : (Finset.univ.filter fun j => ¬ ∀ t ∈ (Finset.univ.filter fun t => φ t = j),
      a t = h j) = (Finset.univ.filter fun j => ∃ t, φ t = j ∧ a t ≠ h j) := by
    ext j
    simp
  rw [hbad] at hc
  rw [him, hsum] at hl
  have hkim : (Finset.univ.image φ).card ≤ k := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := φ)
    simpa using this
  refine ⟨⟨gs, 0⟩, fun j => ⟨w j, (hT j (Finset.mem_univ _)).1⟩, hG.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    have hget : gs[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, 0⟩ j) := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj]
    exact hG.2 j _ hget i hi
  · show 0 < k + 2 + gs.length
    omega
  · show gs.length ≤ s
    have : cntC gs ≤ max _ _ := le_trans hc hφ2
    omega
  · show gs.length - cntC gs ≤ b
    omega
  · show cntC gs ≤ r
    have : cntC gs ≤ max _ _ := le_trans hc hφ2
    omega
  · intro x
    show (∀ j, VC gs x (w j) = h j) ↔ x = a
    constructor
    · intro hx
      funext t
      exact ((hT (φ t) (Finset.mem_univ _)).2 x).1 (hx (φ t)) t (by simp)
    · rintro rfl j
      exact ((hT j (Finset.mem_univ _)).2 x).2 (fun _ _ => rfl)

end PEqualNP.Outside.L_lib_1211

theorem PEqualNP.Outside.L_lib_1211 : ∀ (k m : Nat) (a : Fin k → Bool) (h : Fin m → Bool) (s b r : Nat),
  let p := (Finset.univ.filter (fun i => a i = true)).card
  let z := k-p
  let u := (Finset.univ.filter (fun j => h j = true)).card
  let v := m-u
  let M := min p u + min z v
  let d := if (0 < p ∧ u = 0) ∨ (0 < z ∧ v = 0) then 1 else 0
  let g := min (min k m) (M+r)
  (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (k+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) C ∧
    C.output < k+2+C.size ∧ C.size ≤ s ∧ C.size - PEqualNP.NotBracket.notCount C ≤ b ∧
    PEqualNP.NotBracket.notCount C ≤ r ∧ ∀ x : Fin k → Bool,
      let w := C.wires (List.ofFn x ++ [false,true])
      ((∀ j, w.getD (tap j).val false = h j) ↔ x = a)) ↔
  (k = 0 ∨ 0 < m) ∧ d ≤ r ∧ k-g ≤ b ∧ k-g + max d (g-M) ≤ s := by
  intro k m a h s b r p z u v M d g
  constructor
  · intro H
    exact PEqualNP.Outside.L_lib_1211.lowerMain k m a h s b r H
  · intro H
    exact PEqualNP.Outside.L_lib_1211.consMain k m a h s b r H
