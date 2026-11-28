import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1354

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
noncomputable def dstep {n : ℕ} [DecidableEq (Fin n)] (w : List (Finset (Fin n))) (g : Gate) :
    List (Finset (Fin n)) :=
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

def Q {n : ℕ} [DecidableEq (Fin n)] (st : List Stat) (dp : List (Finset (Fin n))) (D : List Gate) (l c : ℕ) : Prop :=
  st.length = dp.length ∧ ∀ S : Finset ℕ,
    (S.biUnion fun j => dp.getD j ∅).card + D.length + c ≤ l + cnt D + stat st S

open Classical in
theorem Q_step {n : ℕ} [DecidableEq (Fin n)] (m : ℕ) (acc : List Stat × List Gate)
    (dp : List (Finset (Fin n))) (l c : ℕ) (g : Gate) (hg : Ok g) (h : Q acc.1 dp acc.2 l c) :
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
theorem Q_elim {n : ℕ} [DecidableEq (Fin n)] (m : ℕ) (gs : List Gate) :
    ∀ (acc : List Stat × List Gate) (dp : List (Finset (Fin n))) (l c : ℕ), (∀ g ∈ gs, Ok g) →
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

def st1 (n m : ℕ) (pin : Fin n → Bool) : List Stat :=
  (List.ofFn pin).map Sum.inl ++ ((List.range m).map Sum.inr ++ [Sum.inl false, Sum.inl true])

theorem st1_lt (n m : ℕ) (pin : Fin n → Bool) (i : ℕ) (h : i < n) :
    (st1 n m pin).getD i (Sum.inl false) = Sum.inl (pin ⟨i, h⟩) := by
  unfold st1
  rw [List.getD_append _ _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem st1_add (n m : ℕ) (pin : Fin n → Bool) (k : ℕ) :
    (st1 n m pin).getD (n + k) (Sum.inl false)
      = ((List.range m).map Sum.inr ++ [Sum.inl false, Sum.inl true]).getD k (Sum.inl false) :=
  getD_app_add _ _ _ _ _ (by simp)

theorem rest_val (m : ℕ) (y : Fin m → Bool) (k : ℕ) :
    statVal (List.ofFn y ++ [false, true])
      (((List.range m).map Sum.inr ++ [Sum.inl false, Sum.inl true]).getD k (Sum.inl false))
      = (List.ofFn y ++ [false, true]).getD k false ∧
    statValid (m + 2)
      (((List.range m).map Sum.inr ++ [Sum.inl false, Sum.inl true]).getD k (Sum.inl false)) := by
  by_cases hk : k < m
  · rw [List.getD_append _ _ _ _ (by simpa using hk)]
    simp [List.getD_eq_getElem?_getD, hk, statVal, statValid]
    omega
  · obtain ⟨k', rfl⟩ : ∃ k', k = m + k' := ⟨k - m, by omega⟩
    rw [getD_app_add _ _ _ _ _ (by simp), getD_app_add _ _ _ _ _ (by simp)]
    rcases k' with _ | _ | k' <;> simp [statVal, statValid]

theorem inv1 (n m : ℕ) (pin : Fin n → Bool) (y : Fin m → Bool) :
    Inv (m + 2) (List.ofFn y ++ [false, true]) (List.ofFn pin ++ (List.ofFn y ++ [false, true]))
      (st1 n m pin, []) := by
  refine ⟨by simp [st1], ?_⟩
  intro i
  by_cases hi : i < n
  · show statValid _ ((st1 n m pin).getD i _) ∧ statVal _ ((st1 n m pin).getD i _) = _
    rw [st1_lt n m pin i hi, inp_lt pin _ i hi]
    refine ⟨trivial, ?_⟩
    simp [statVal, List.getD_eq_getElem?_getD, hi]
  · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    show statValid _ ((st1 n m pin).getD (n + k) _) ∧ statVal _ ((st1 n m pin).getD (n + k) _) = _
    rw [st1_add, inp_add]
    have := rest_val m y k
    exact ⟨by simpa using this.2, this.1⟩

theorem Q0 (n m : ℕ) [DecidableEq (Fin n)] (pin : Fin n → Bool) :
    Q (st1 n m pin) ((List.ofFn (fun i : Fin n => ({i} : Finset (Fin n)))) ++
      List.replicate (m+2) (∅ : Finset (Fin n))) [] 0 0 := by
  refine ⟨by simp [st1], fun S => ?_⟩
  have hc : cnt ([] : List Gate) = 0 := rfl
  simp only [List.length_nil, hc, Nat.add_zero, Nat.zero_add]
  refine le_trans Finset.card_biUnion_le ?_
  unfold stat
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j < n
  · rw [st1_lt n m pin j hj, List.getD_append _ _ _ _ (by simpa using hj)]
    simp [List.getD_eq_getElem?_getD, hj, isC]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hj)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp

theorem main : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
  C.output < n+2+C.size
let neg := PEqualNP.NotBracket.notCount
let pos := fun C : PEqualNP.CircuitLowerBounds.Circuit => C.size - neg C
∀ (n m t : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat)
    (pin : Fin n → Bool),
  valid (n+m) C → (∀ i, tap i < n+m+2+C.size) →
  let init := (List.ofFn (fun i : Fin n => ({i} : Finset (Fin n)))) ++
    List.replicate (m+2) (∅ : Finset (Fin n))
  let deps := C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
    let args := if g.op = PEqualNP.CircuitLowerBounds.GateOp.not then g.inputs.take 1 else g.inputs
    w ++ [args.foldl (fun A j => A ∪ w.getD j ∅) ∅]) init
  let out := (C.output :: List.ofFn tap).toFinset
  let used := out.biUnion (fun j => deps.getD j ∅)
  let raw := fun y : Fin m → Bool => List.ofFn y ++ [false,true]
  let value := fun (j : Nat) (y : Fin m → Bool) =>
    (C.wires (List.ofFn pin ++ raw y)).getD j false
  let constant := out.filter (fun j => ∀ y, value j y = value j (fun _ => false))
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (tap' : Fin t → Nat),
    valid m D ∧ (∀ i, tap' i < m+2+D.size) ∧ neg D ≤ neg C ∧ pos D ≤ pos C ∧
    pos D + used.card ≤ pos C + constant.card ∧
    ∀ y, D.eval (raw y) = value C.output y ∧
      ∀ i, (D.wires (raw y)).getD (tap' i) false = value (tap i) y) := by
  intro valid neg pos n m t C tap pin hv _ init deps out used raw value constant
  obtain ⟨hF, _, hO⟩ := hv
  have hok : ∀ g ∈ C.gates, Ok g := hF
  have hinv : ∀ y : Fin m → Bool, Inv (m + 2) (List.ofFn y ++ [false, true])
      (wiresFrom C.gates (List.ofFn pin ++ (List.ofFn y ++ [false, true])))
      (elim (m + 2) C.gates (st1 n m pin, [])) :=
    fun y => inv_elim (m + 2) _ (by simp) C.gates _ _ hok (inv1 n m pin y)
  have hvalid : ∀ i, statValid (m + 2 + (elim (m + 2) C.gates (st1 n m pin, [])).2.length)
      ((elim (m + 2) C.gates (st1 n m pin, [])).1.getD i (Sum.inl false)) :=
    fun i => ((hinv fun _ => false).2 i).1
  have htap : ∀ i, tapNat m (elim (m + 2) C.gates (st1 n m pin, [])).1 i
      < m + 2 + (elim (m + 2) C.gates (st1 n m pin, [])).2.length := by
    intro i
    have := hvalid i
    unfold tapNat
    cases h : (elim (m + 2) C.gates (st1 n m pin, [])).1.getD i (Sum.inl false) with
    | inl c => cases c <;> simp <;> omega
    | inr j => rw [h] at this; exact this
  have htapv : ∀ (y : Fin m → Bool) (i : ℕ),
      (wiresFrom (elim (m + 2) C.gates (st1 n m pin, [])).2 (List.ofFn y ++ [false, true])).getD
        (tapNat m (elim (m + 2) C.gates (st1 n m pin, [])).1 i) false
      = (wiresFrom C.gates (List.ofFn pin ++ (List.ofFn y ++ [false, true]))).getD i false := by
    intro y i
    have := ((hinv y).2 i).2
    unfold tapNat
    cases h : (elim (m + 2) C.gates (st1 n m pin, [])).1.getD i (Sum.inl false) with
    | inl c =>
      rw [h] at this
      rw [← this, getD_wiresFrom _ _ _ (by cases c <;> simp)]
      cases c
      · exact inp_add y [false, true] 0
      · exact inp_add y [false, true] 1
    | inr j => rw [h] at this; exact this
  obtain ⟨a, b, e1, e2⟩ := elim_count (m + 2) C.gates (st1 n m pin, [])
  have hQ := Q_elim (m + 2) C.gates (st1 n m pin, []) _ 0 0 hok (Q0 n m pin)
  have hQ' := hQ.2 out
  have hconst : stat (elim (m + 2) C.gates (st1 n m pin, [])).1 out ≤ constant.card := by
    unfold stat
    apply Finset.card_le_card
    intro j hj
    rw [Finset.mem_filter] at hj
    suffices hs : ∀ y, value j y = value j (fun _ => false) by
      have : j ∈ out.filter (fun j => ∀ y, value j y = value j (fun _ => false)) :=
        Finset.mem_filter.2 ⟨hj.1, hs⟩
      convert this
    intro y
    have hy := ((hinv y).2 j).2
    have h0 := ((hinv fun _ => false).2 j).2
    cases h : (elim (m + 2) C.gates (st1 n m pin, [])).1.getD j (Sum.inl false) with
    | inl c =>
      rw [h] at hy h0
      exact hy.symm.trans h0
    | inr k => rw [h] at hj; simp [isC] at hj
  have hused : used.card = ((out.biUnion fun j =>
      (C.gates.foldl dstep ((List.ofFn (fun i : Fin n => ({i} : Finset (Fin n)))) ++
        List.replicate (m+2) (∅ : Finset (Fin n)))).getD j ∅)).card := by
    simp only [used, deps, init, out]
    congr!
    unfold dstep
    congr!
  have hc1 := cnt_le (elim (m + 2) C.gates (st1 n m pin, [])).2
  have hc2 := cnt_le C.gates
  have hclean : CleanL (m + 2) (elim (m + 2) C.gates (st1 n m pin, [])).2 :=
    elim_clean (m + 2) C.gates (st1 n m pin, []) hok
      (fun i => ((inv1 n m pin fun _ => false).2 i).1) (fun p g h => by simp at h)
  simp only [List.length_nil, Nat.zero_add] at e1 e2 hQ'
  have e0 : cnt ([] : List Gate) = 0 := rfl
  rw [e0, Nat.zero_add] at e1
  refine ⟨⟨(elim (m + 2) C.gates (st1 n m pin, [])).2,
      tapNat m (elim (m + 2) C.gates (st1 n m pin, [])).1 C.output⟩,
    fun i => tapNat m (elim (m + 2) C.gates (st1 n m pin, [])).1 (tap i),
    ⟨elim_ok (m + 2) C.gates _ (fun g hg => by simp at hg), ?_, htap _⟩,
    fun i => htap _, ?_, ?_, ?_, fun y => ⟨htapv y C.output, fun i => htapv y (tap i)⟩⟩
  · intro j hj i hi
    have hget : (elim (m + 2) C.gates (st1 n m pin, [])).2[j]?
        = some (PEqualNP.MetaComplexity.NestedCover.gateAt
          ⟨(elim (m + 2) C.gates (st1 n m pin, [])).2,
            tapNat m (elim (m + 2) C.gates (st1 n m pin, [])).1 C.output⟩ j) := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj]
    exact cleanG_lt (hclean j _ hget) i hi
  · show cnt (elim (m + 2) C.gates (st1 n m pin, [])).2 ≤ cnt C.gates
    omega
  · show (elim (m + 2) C.gates (st1 n m pin, [])).2.length
        - cnt (elim (m + 2) C.gates (st1 n m pin, [])).2 ≤ C.gates.length - cnt C.gates
    omega
  · show (elim (m + 2) C.gates (st1 n m pin, [])).2.length
        - cnt (elim (m + 2) C.gates (st1 n m pin, [])).2 + used.card
        ≤ C.gates.length - cnt C.gates + constant.card
    rw [hused]
    omega

end PEqualNP.Outside.L_lib_1354

theorem PEqualNP.Outside.L_lib_1354 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let valid := fun (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
  C.output < n+2+C.size
let neg := PEqualNP.NotBracket.notCount
let pos := fun C : PEqualNP.CircuitLowerBounds.Circuit => C.size - neg C
∀ (n m t : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat)
    (pin : Fin n → Bool),
  valid (n+m) C → (∀ i, tap i < n+m+2+C.size) →
  let init := (List.ofFn (fun i : Fin n => ({i} : Finset (Fin n)))) ++
    List.replicate (m+2) (∅ : Finset (Fin n))
  let deps := C.gates.foldl (fun (w : List (Finset (Fin n))) g =>
    let args := if g.op = PEqualNP.CircuitLowerBounds.GateOp.not then g.inputs.take 1 else g.inputs
    w ++ [args.foldl (fun A j => A ∪ w.getD j ∅) ∅]) init
  let out := (C.output :: List.ofFn tap).toFinset
  let used := out.biUnion (fun j => deps.getD j ∅)
  let raw := fun y : Fin m → Bool => List.ofFn y ++ [false,true]
  let value := fun (j : Nat) (y : Fin m → Bool) =>
    (C.wires (List.ofFn pin ++ raw y)).getD j false
  let constant := out.filter (fun j => ∀ y, value j y = value j (fun _ => false))
  ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (tap' : Fin t → Nat),
    valid m D ∧ (∀ i, tap' i < m+2+D.size) ∧ neg D ≤ neg C ∧ pos D ≤ pos C ∧
    pos D + used.card ≤ pos C + constant.card ∧
    ∀ y, D.eval (raw y) = value C.output y ∧
      ∀ i, (D.wires (raw y)).getD (tap' i) false = value (tap i) y) :=
  PEqualNP.Outside.L_lib_1354.main
