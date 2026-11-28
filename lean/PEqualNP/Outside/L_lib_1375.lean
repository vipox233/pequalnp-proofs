import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1375

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

def isC : Stat → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

def stat (st : List Stat) (S : Finset ℕ) : ℕ :=
  (S.filter (fun j => isC (st.getD j (Sum.inl false)) = true)).card

open Classical in
noncomputable def dstep {α : Type} [DecidableEq α] (w : List (Finset α)) (g : Gate) :
    List (Finset α) :=
  w ++ [(if g.op = GateOp.not then g.inputs.take 1 else g.inputs).foldl
    (fun A j => A ∪ w.getD j ∅) ∅]

theorem foldl_union {α : Type} [DecidableEq α] (f : ℕ → Finset α) :
    ∀ (l : List ℕ) (A : Finset α), l.foldl (fun A j => A ∪ f j) A = A ∪ l.toFinset.biUnion f := by
  intro l
  induction l with
  | nil => intro A; simp
  | cons a l ih =>
    intro A
    rw [List.foldl_cons, ih, List.toFinset_cons, Finset.biUnion_insert, Finset.union_assoc]

theorem statL (st : List Stat) (l : List ℕ) :
    stat st l.toFinset ≤ (l.filter (fun j => isC (st.getD j (Sum.inl false)))).length := by
  unfold stat
  rw [← List.toFinset_filter]
  exact List.toFinset_card_le _

theorem stat_union (st : List Stat) (A B : Finset ℕ) : stat st (A ∪ B) ≤ stat st A + stat st B := by
  unfold stat
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

open Classical in
theorem key (m : ℕ) (st : List Stat) (g : Gate) (hg : Ok g) :
    (simplify g.op m (g.inputs.map fun i => st.getD i (Sum.inl false))).1.toList.length + cnt [g] +
      stat st (if g.op = GateOp.not then g.inputs.take 1 else g.inputs).toFinset
      ≤ 1 + cnt (simplify g.op m (g.inputs.map fun i => st.getD i (Sum.inl false))).1.toList +
        (if isC (simplify g.op m (g.inputs.map fun i => st.getD i (Sum.inl false))).2 then 1 else 0) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  refine le_trans (Nat.add_le_add_left (statL _ _) _) ?_
  rcases hop with rfl | rfl | rfl <;>
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  all_goals (try (simp at hlen; done))
  all_goals (try cases ha : st.getD a (Sum.inl false))
  all_goals (try cases hb : st.getD b (Sum.inl false))
  all_goals (try rename_i x y; cases x <;> cases y)
  all_goals (try rename_i x; cases x)
  all_goals simp_all [simplify, simpAnd, simpOr, simpNot, cnt, PEqualNP.NotBracket.notCount, isC]

def Q {α : Type} [DecidableEq α] (st : List Stat) (dp : List (Finset α)) (D : List Gate) (l c : ℕ) : Prop :=
  st.length = dp.length ∧ ∀ S : Finset ℕ,
    (S.biUnion fun j => dp.getD j ∅).card + D.length + c ≤ l + cnt D + stat st S

open Classical in
theorem Q_step {α : Type} [DecidableEq α] (m : ℕ) (acc : List Stat × List Gate)
    (dp : List (Finset α)) (l c : ℕ) (g : Gate) (hg : Ok g) (h : Q acc.1 dp acc.2 l c) :
    Q (elimStep m acc g).1 (dstep dp g) (elimStep m acc g).2 (l + 1) (c + cnt [g]) := by
  obtain ⟨hl, hS⟩ := h
  obtain ⟨a, b, e1, e2, _⟩ := step_count m acc g
  have hk := key (m + acc.2.length) acc.1 g hg
  set r := simplify g.op (m + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    with hr
  set A := (if g.op = GateOp.not then g.inputs.take 1 else g.inputs) with hA
  have e1' : cnt (acc.2 ++ r.1.toList) + a = cnt acc.2 + cnt [g] := e1
  have e2' : (acc.2 ++ r.1.toList).length + a + b = acc.2.length + 1 := e2
  rw [cnt_append] at e1'
  rw [List.length_append] at e2'
  refine ⟨by simp [elimStep, dstep, hl], fun S => ?_⟩
  have hst : ∀ j, j ≠ dp.length → (acc.1 ++ [r.2]).getD j (Sum.inl false) = acc.1.getD j (Sum.inl false) :=
    fun j hj => getD_snoc_ne _ _ _ _ (by rw [hl]; exact hj)
  have hdp : ∀ j, j ≠ dp.length → (dstep dp g).getD j ∅ = dp.getD j ∅ :=
    fun j hj => getD_snoc_ne _ _ _ _ hj
  show (S.biUnion fun j => (dstep dp g).getD j ∅).card + (acc.2 ++ r.1.toList).length + (c + cnt [g])
    ≤ l + 1 + cnt (acc.2 ++ r.1.toList) + stat (acc.1 ++ [r.2]) S
  rw [cnt_append, List.length_append]
  by_cases hL : dp.length ∈ S
  · set T := S.erase dp.length with hT
    have hS' : S = insert dp.length T := (Finset.insert_erase hL).symm
    have hLT : dp.length ∉ T := Finset.notMem_erase _ _
    have hU : (S.biUnion fun j => (dstep dp g).getD j ∅) = (A.toFinset ∪ T).biUnion fun j => dp.getD j ∅ := by
      rw [hS', Finset.biUnion_insert, Finset.union_biUnion]
      have h1 : (dstep dp g).getD dp.length ∅ = A.toFinset.biUnion fun j => dp.getD j ∅ := by
        simp only [dstep]
        rw [getD_snoc_eq, foldl_union, Finset.empty_union]
      rw [h1]
      congr 1
      exact Finset.biUnion_congr rfl (fun j hj => hdp j (fun e => hLT (e ▸ hj)))
    have hstat : stat (acc.1 ++ [r.2]) S = stat acc.1 T + (if isC r.2 then 1 else 0) := by
      rw [hS']
      unfold stat
      rw [Finset.filter_insert]
      have hfl : (T.filter fun j => isC ((acc.1 ++ [r.2]).getD j (Sum.inl false)) = true)
          = T.filter fun j => isC (acc.1.getD j (Sum.inl false)) = true :=
        Finset.filter_congr (fun j hj => by rw [hst j (fun e => hLT (e ▸ hj))])
      have hL2 : (acc.1 ++ [r.2]).getD dp.length (Sum.inl false) = r.2 := by
        rw [← hl]; exact getD_snoc_eq _ _ _
      rw [hL2, hfl]
      split_ifs with hc
      · rw [Finset.card_insert_of_notMem (fun hm => hLT (Finset.mem_filter.1 hm).1)]
      · rfl
    rw [hU, hstat]
    have h1 := hS (A.toFinset ∪ T)
    have h2 := stat_union acc.1 A.toFinset T
    omega
  · have hU : (S.biUnion fun j => (dstep dp g).getD j ∅) = S.biUnion fun j => dp.getD j ∅ :=
      Finset.biUnion_congr rfl (fun j hj => hdp j (fun e => hL (e ▸ hj)))
    have hstat : stat (acc.1 ++ [r.2]) S = stat acc.1 S := by
      unfold stat
      congr 1
      exact Finset.filter_congr (fun j hj => by rw [hst j (fun e => hL (e ▸ hj))])
    rw [hU, hstat]
    have h1 := hS S
    omega

open Classical in
theorem Q_elim {α : Type} [DecidableEq α] (m : ℕ) (gs : List Gate) :
    ∀ (acc : List Stat × List Gate) (dp : List (Finset α)) (l c : ℕ), (∀ g ∈ gs, Ok g) →
      Q acc.1 dp acc.2 l c →
      Q (elim m gs acc).1 (gs.foldl dstep dp) (elim m gs acc).2 (l + gs.length) (c + cnt gs) := by
  induction gs with
  | nil =>
    intro acc dp l c _ h
    have h0 : cnt ([] : List Gate) = 0 := rfl
    simpa [elim, h0] using h
  | cons g gs ih =>
    intro acc dp l c hok h
    have h1 := Q_step m acc dp l c g (hok g (by simp)) h
    have h2 := ih _ _ _ _ (fun g' hg' => hok g' (by simp [hg'])) h1
    rw [elim_cons, List.foldl_cons]
    have e : cnt (g :: gs) = cnt [g] + cnt gs := cnt_append [g] gs
    rw [e, List.length_cons]
    have e3 : l + (gs.length + 1) = l + 1 + gs.length := by omega
    have e4 : c + (cnt [g] + cnt gs) = c + cnt [g] + cnt gs := by omega
    rw [e3, e4]; exact h2

theorem getD_app_add {α : Type} (L t : List α) (d : α) (n k : ℕ) (h : L.length = n) :
    (L ++ t).getD (n + k) d = t.getD k d := by
  subst h
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem inp_lt {n : ℕ} (x : Fin n → Bool) (t : List Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x ++ t).getD i false = (List.ofFn x).getD i false :=
  List.getD_append _ _ _ _ (by simpa using h)

theorem inp_add {n : ℕ} (x : Fin n → Bool) (t : List Bool) (k : ℕ) :
    (List.ofFn x ++ t).getD (n + k) false = t.getD k false :=
  getD_app_add _ _ _ _ _ (by simp)

def tapNat (n : ℕ) (st : List Stat) (i : ℕ) : ℕ :=
  match st.getD i (Sum.inl false) with
  | Sum.inl c => bif c then n + 1 else n
  | Sum.inr j => j

open Classical in
theorem eval_congr (g : Gate) (hg : Ok g) (f f' : ℕ → Bool)
    (h : ∀ a ∈ (if g.op = GateOp.not then g.inputs.take 1 else g.inputs), f a = f' a) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, _⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rw [if_neg (fun e => GateOp.noConfusion e)] at h
    show GateOp.eval GateOp.and (ins.map f) = GateOp.eval GateOp.and (ins.map f')
    rw [List.map_congr_left h]
  · rw [if_neg (fun e => GateOp.noConfusion e)] at h
    show GateOp.eval GateOp.or (ins.map f) = GateOp.eval GateOp.or (ins.map f')
    rw [List.map_congr_left h]
  · rw [if_pos rfl] at h
    rcases ins with _ | ⟨x, t⟩
    · rfl
    · show GateOp.eval GateOp.not (f x :: t.map f) = GateOp.eval GateOp.not (f' x :: t.map f')
      simp only [GateOp.eval, List.headD_cons]
      rw [h x (by simp)]

open Classical in
theorem sem (b b' : List Bool) (gs : List Gate) : ∀ (dp : List (Finset ℕ)) (x x' : List Bool),
    (∀ g ∈ gs, Ok g) → dp.length = x.length → x.length = x'.length →
    (∀ j, (∀ i ∈ dp.getD j ∅, b.getD i false = b'.getD i false) → x.getD j false = x'.getD j false) →
    ∀ j, (∀ i ∈ (gs.foldl dstep dp).getD j ∅, b.getD i false = b'.getD i false) →
      (wiresFrom gs x).getD j false = (wiresFrom gs x').getD j false := by
  induction gs with
  | nil => intro dp x x' _ _ _ h; exact h
  | cons g gs ih =>
    intro dp x x' hok hl hl' h j hj
    refine ih (dstep dp g) (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
      (x' ++ [g.op.eval (g.inputs.map fun i => x'.getD i false)])
      (fun g' hg' => hok g' (by simp [hg'])) (by simp [dstep, hl]) (by simp [hl']) ?_ j hj
    intro q hq
    by_cases hqL : q = x.length
    · subst hqL
      rw [getD_snoc_eq, getD_snoc_len _ _ _ _ hl'.symm]
      have hd : (dstep dp g).getD x.length ∅ = (if g.op = GateOp.not then g.inputs.take 1 else g.inputs).toFinset.biUnion
          (fun j => dp.getD j ∅) := by
        unfold dstep
        rw [getD_snoc_len _ _ _ _ hl, foldl_union, Finset.empty_union]
      rw [hd] at hq
      apply eval_congr g (hok g (by simp))
      intro a ha
      apply h a
      intro i hi
      exact hq i (Finset.mem_biUnion.2 ⟨a, List.mem_toFinset.2 ha, hi⟩)
    · rw [getD_snoc_ne _ _ _ _ hqL, getD_snoc_ne _ _ _ _ (by rw [← hl']; exact hqL)]
      apply h q
      intro i hi
      apply hq i
      unfold dstep
      rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hqL)]
      exact hi

theorem getD_app {α : Type} (L t : List α) (d : α) (i : ℕ) :
    (L ++ t).getD i d = if i < L.length then L.getD i d else t.getD (i - L.length) d := by
  split_ifs with h
  · exact List.getD_append _ _ _ _ h
  · exact List.getD_append_right _ _ _ _ (by omega)

theorem getD_rep {α : Type} (n : ℕ) (a d : α) (i : ℕ) :
    (List.replicate n a).getD i d = if i < n then a else d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> simp

theorem getD_mr {α : Type} (f : ℕ → α) (k j : ℕ) (d : α) :
    ((List.range k).map f).getD j d = if j < k then f j else d := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · exact List.getD_eq_default _ _ (by simpa using h)

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (j : ℕ) (d : α) :
    (List.ofFn f).getD j d = if h : j < n then f ⟨j, h⟩ else d := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · exact List.getD_eq_default _ _ (by simpa using h)

theorem getD_pair {α : Type} (a b d : α) (j : ℕ) :
    [a, b].getD j d = if j = 0 then a else if j = 1 then b else d := by
  rcases j with _ | _ | j <;> simp

def st2 (l k r : ℕ) : List Stat :=
  List.replicate l (Sum.inl true) ++ (List.range k).map Sum.inr ++
    List.replicate r (Sum.inl false) ++ [Sum.inl false, Sum.inl true]

def X (l k r : ℕ) (y : Fin k → Bool) : List Bool :=
  List.replicate l true ++ List.ofFn y ++ List.replicate r false ++ [false,true]

def ini (l k r : ℕ) : List (Finset ℕ) :=
  (List.range (l+k+r+2)).map (fun i => if i < l ∨ (l + k ≤ i ∧ i < l+k+r) then {i} else ∅)

def trace (n s : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i.val < s)) ++ [false, true]

theorem st2_get (l k r i : ℕ) : (st2 l k r).getD i (Sum.inl false) =
    if i < l then Sum.inl true else if i < l + k then Sum.inr (i - l) else
    if i < l + k + r + 1 then Sum.inl false else if i = l + k + r + 1 then Sum.inl true
    else Sum.inl false := by
  simp only [st2, getD_app, getD_rep, List.length_append, List.length_replicate, List.length_map,
    List.length_range, getD_mr, getD_pair]
  split_ifs <;> first | rfl | omega | (simp only [Sum.inl.injEq, reduceCtorEq]; omega) | skip

theorem X_get (l k r : ℕ) (y : Fin k → Bool) (i : ℕ) : (X l k r y).getD i false =
    if h0 : i < l then true else if h : i < l + k then y ⟨i - l, by omega⟩ else
    if i = l + k + r + 1 then true else false := by
  simp only [X, getD_app, getD_rep, List.length_append, List.length_replicate, List.length_ofFn, getD_ofFn, getD_pair]
  split_ifs <;> first | rfl | omega | (simp only [Sum.inl.injEq, reduceCtorEq]; omega) | skip

theorem trace_get (n s j : ℕ) : (trace n s).getD j false =
    if j < n then decide (j < s) else if j = n + 1 then true else false := by
  simp only [trace, getD_app, List.length_ofFn, getD_ofFn, getD_pair]
  split_ifs <;> first | rfl | omega | (simp only [Sum.inl.injEq, reduceCtorEq]; omega) | skip

theorem ini_get (l k r j : ℕ) : (ini l k r).getD j ∅ =
    if j < l ∨ (l + k ≤ j ∧ j < l+k+r) then {j} else ∅ := by
  simp only [ini, getD_mr]
  split_ifs <;> first | rfl | omega

theorem list_eq_of_getD (x x' : List Bool) (h1 : x.length = x'.length)
    (h2 : ∀ j, x.getD j false = x'.getD j false) : x = x' :=
  List.ext_getElem h1 (fun j hj hj' => by
    have := h2 j
    rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at this)

theorem trace_eq (l k r s : ℕ) (hs : s ≤ k) :
    trace (l + k + r) (l + s) = X l k r (fun i : Fin k => decide (i.val < s)) := by
  apply list_eq_of_getD _ _ (by simp [trace, X]; omega)
  intro j
  rw [trace_get, X_get]
  split_ifs <;> simp_all <;> omega

theorem inv2 (l k r : ℕ) (y : Fin k → Bool) :
    Inv (k + 2) (List.ofFn y ++ [false, true]) (X l k r y) (st2 l k r, []) := by
  refine ⟨by simp [st2, X], ?_⟩
  intro i
  show statValid _ ((st2 l k r).getD i _) ∧ statVal (List.ofFn y ++ [false, true]) ((st2 l k r).getD i _) = _
  rw [st2_get, X_get]
  split_ifs <;> simp_all [statValid, statVal] <;> (try omega)
  refine ⟨by omega, ?_⟩; rw [← List.getD_eq_getElem?_getD, getD_app, getD_ofFn]; simp [show i - l < k by omega]

theorem Q0' (l k r : ℕ) : Q (st2 l k r) (ini l k r) [] 0 0 := by
  refine ⟨by simp [st2, ini]; omega, fun S => ?_⟩
  have hc : cnt ([] : List Gate) = 0 := rfl
  simp only [List.length_nil, hc, Nat.add_zero, Nat.zero_add]
  refine le_trans Finset.card_biUnion_le ?_
  unfold stat
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro j _
  rw [ini_get, st2_get]
  split_ifs <;> simp_all [isC] <;> omega

theorem main : (∀ (l k r a : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
  let n := l+k+r
  let neg := PEqualNP.NotBracket.notCount
  let pos := fun D => PEqualNP.CircuitLowerBounds.Circuit.size D - neg D
  let old := fun (s w : Nat) => (C.wires
    (List.ofFn (fun i : Fin n => decide (i.val < s)) ++ [false,true])).getD w false
  let changed := (Finset.range n).filter (fun z => (z < l ∨ l+k ≤ z) ∧
    ∃ i, old z (tap i) ≠ old (z+1) (tap i))
  let constant := (List.ofFn tap).toFinset.filter (fun w =>
    ∀ s : Fin (k+1), old (l+s.val) w = old l w)
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
  (∀ i, tap i < n+2+C.size) →
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (T : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) D ∧
    D.output < k+2+D.size ∧ (∀ i, T i < k+2+D.size) ∧ neg D ≤ neg C ∧ pos D ≤ pos C ∧
    pos D + changed.card ≤ pos C + constant.card ∧ D.size + changed.card ≤ C.size + constant.card ∧
    ∀ y : Fin k → Bool, ∀ i,
      (D.wires (List.ofFn y ++ [false,true])).getD (T i) false =
      (C.wires (List.replicate l true ++ List.ofFn y ++ List.replicate r false ++ [false,true])).getD
        (tap i) false) := by
  intro l k r a C tap n neg pos old changed constant hF _ _
  have hok : ∀ g ∈ C.gates, Ok g := hF
  have hinv : ∀ y : Fin k → Bool, Inv (k + 2) (List.ofFn y ++ [false, true])
      (wiresFrom C.gates (X l k r y)) (elim (k + 2) C.gates (st2 l k r, [])) :=
    fun y => inv_elim (k + 2) _ (by simp) C.gates _ _ hok (inv2 l k r y)
  have hvalid : ∀ i, statValid (k + 2 + (elim (k + 2) C.gates (st2 l k r, [])).2.length)
      ((elim (k + 2) C.gates (st2 l k r, [])).1.getD i (Sum.inl false)) :=
    fun i => ((hinv fun _ => false).2 i).1
  have htap : ∀ i, tapNat k (elim (k + 2) C.gates (st2 l k r, [])).1 i
      < k + 2 + (elim (k + 2) C.gates (st2 l k r, [])).2.length := by
    intro i
    have := hvalid i
    unfold tapNat
    cases h : (elim (k + 2) C.gates (st2 l k r, [])).1.getD i (Sum.inl false) with
    | inl c => cases c <;> simp <;> omega
    | inr j => rw [h] at this; exact this
  have htapv : ∀ (y : Fin k → Bool) (i : ℕ),
      (wiresFrom (elim (k + 2) C.gates (st2 l k r, [])).2 (List.ofFn y ++ [false, true])).getD
        (tapNat k (elim (k + 2) C.gates (st2 l k r, [])).1 i) false
      = (wiresFrom C.gates (X l k r y)).getD i false := by
    intro y i
    have := ((hinv y).2 i).2
    unfold tapNat
    cases h : (elim (k + 2) C.gates (st2 l k r, [])).1.getD i (Sum.inl false) with
    | inl c =>
      rw [h] at this
      rw [← this, getD_wiresFrom _ _ _ (by cases c <;> simp)]
      cases c
      · exact inp_add y [false, true] 0
      · exact inp_add y [false, true] 1
    | inr j => rw [h] at this; exact this
  obtain ⟨a1, b1, e1, e2⟩ := elim_count (k + 2) C.gates (st2 l k r, [])
  have hQ := (Q_elim (k + 2) C.gates (st2 l k r, []) (ini l k r) 0 0 hok (Q0' l k r)).2
    (List.ofFn tap).toFinset
  have hch : changed ⊆ (List.ofFn tap).toFinset.biUnion
      (fun j => (C.gates.foldl dstep (ini l k r)).getD j ∅) := by
    intro z hz
    rw [Finset.mem_filter, Finset.mem_range] at hz
    obtain ⟨hzn, hout, i, hi⟩ := hz
    rw [Finset.mem_biUnion]
    refine ⟨tap i, by simp, ?_⟩
    by_contra hnot
    apply hi
    have hne : ∀ q, q ≠ z → (trace (l + k + r) z).getD q false = (trace (l + k + r) (z + 1)).getD q false := by
      intro q hq
      rw [trace_get, trace_get]
      split_ifs <;> simp <;> omega
    exact sem (trace (l + k + r) z) (trace (l + k + r) (z + 1)) C.gates (ini l k r) _ _ hok
      (by simp [ini, trace, n]) (by simp [trace])
      (fun j hj => by
        by_cases hjz : j = z
        · subst hjz
          apply hj
          rw [ini_get, if_pos (by omega)]
          simp
        · exact hne j hjz)
      (tap i) (fun q hq => hne q (fun e => hnot (e ▸ hq)))
  have hconst : stat (elim (k + 2) C.gates (st2 l k r, [])).1 (List.ofFn tap).toFinset
      ≤ constant.card := by
    unfold stat
    apply Finset.card_le_card
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨hw.1, fun s => ?_⟩
    have key : ∀ s : ℕ, s ≤ k → old (l + s) w = statVal (wiresFrom (elim (k + 2) C.gates (st2 l k r, [])).2
        (List.ofFn (fun i : Fin k => decide (i.val < s)) ++ [false, true]))
        ((elim (k + 2) C.gates (st2 l k r, [])).1.getD w (Sum.inl false)) := by
      intro s hs
      have := ((hinv fun i : Fin k => decide (i.val < s)).2 w).2
      rw [this]
      show (wiresFrom C.gates (trace (l + k + r) (l + s))).getD w false = _
      rw [trace_eq l k r s hs]
    have h1 := key s.val (by omega)
    have h0 := key 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [h1, h0]
    cases h : (elim (k + 2) C.gates (st2 l k r, [])).1.getD w (Sum.inl false) with
    | inl c => rfl
    | inr j => rw [h] at hw; simp [isC] at hw
  have hcc := Finset.card_le_card hch
  have hc1 := cnt_le (elim (k + 2) C.gates (st2 l k r, [])).2
  have hc2 := cnt_le C.gates
  have hclean : CleanL (k + 2) (elim (k + 2) C.gates (st2 l k r, [])).2 :=
    elim_clean (k + 2) C.gates (st2 l k r, []) hok
      (fun i => ((inv2 l k r fun _ => false).2 i).1) (fun p g h => by simp at h)
  simp only [List.length_nil, Nat.zero_add] at e1 e2 hQ
  have e0 : cnt ([] : List Gate) = 0 := rfl
  rw [e0, Nat.zero_add] at e1
  refine ⟨⟨(elim (k + 2) C.gates (st2 l k r, [])).2, k⟩,
    fun i => tapNat k (elim (k + 2) C.gates (st2 l k r, [])).1 (tap i),
    elim_ok (k + 2) C.gates _ (fun g hg => by simp at hg), ?_,
    show k < k + 2 + (elim (k + 2) C.gates (st2 l k r, [])).2.length by omega,
    fun i => htap _, ?_, ?_, ?_, ?_, fun y i => htapv y (tap i)⟩
  · intro j hj i hi
    have hget : (elim (k + 2) C.gates (st2 l k r, [])).2[j]?
        = some (PEqualNP.MetaComplexity.NestedCover.gateAt
          ⟨(elim (k + 2) C.gates (st2 l k r, [])).2, k⟩ j) := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj]
    exact cleanG_lt (hclean j _ hget) i hi
  · show cnt (elim (k + 2) C.gates (st2 l k r, [])).2 ≤ cnt C.gates
    omega
  · show (elim (k + 2) C.gates (st2 l k r, [])).2.length
        - cnt (elim (k + 2) C.gates (st2 l k r, [])).2 ≤ C.gates.length - cnt C.gates
    omega
  · show (elim (k + 2) C.gates (st2 l k r, [])).2.length
        - cnt (elim (k + 2) C.gates (st2 l k r, [])).2 + changed.card
        ≤ C.gates.length - cnt C.gates + constant.card
    omega
  · show (elim (k + 2) C.gates (st2 l k r, [])).2.length + changed.card
        ≤ C.gates.length + constant.card
    omega

end PEqualNP.Outside.L_lib_1375

theorem PEqualNP.Outside.L_lib_1375 : (∀ (l k r a : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
  let n := l+k+r
  let neg := PEqualNP.NotBracket.notCount
  let pos := fun D => PEqualNP.CircuitLowerBounds.Circuit.size D - neg D
  let old := fun (s w : Nat) => (C.wires
    (List.ofFn (fun i : Fin n => decide (i.val < s)) ++ [false,true])).getD w false
  let changed := (Finset.range n).filter (fun z => (z < l ∨ l+k ≤ z) ∧
    ∃ i, old z (tap i) ≠ old (z+1) (tap i))
  let constant := (List.ofFn tap).toFinset.filter (fun w =>
    ∀ s : Fin (k+1), old (l+s.val) w = old l w)
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
  (∀ i, tap i < n+2+C.size) →
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (T : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) D ∧
    D.output < k+2+D.size ∧ (∀ i, T i < k+2+D.size) ∧ neg D ≤ neg C ∧ pos D ≤ pos C ∧
    pos D + changed.card ≤ pos C + constant.card ∧ D.size + changed.card ≤ C.size + constant.card ∧
    ∀ y : Fin k → Bool, ∀ i,
      (D.wires (List.ofFn y ++ [false,true])).getD (T i) false =
      (C.wires (List.replicate l true ++ List.ofFn y ++ List.replicate r false ++ [false,true])).getD
        (tap i) false) :=
  PEqualNP.Outside.L_lib_1375.main
