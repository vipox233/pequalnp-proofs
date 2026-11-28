import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_50554
open PEqualNP.CircuitLowerBounds
def n6 (b0 b1 b2 b3 b4 b5 : Bool) : Nat :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
    (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0)
def ofB (f : Nat → Bool) : Nat := n6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)
def evT (o : GateOp) (l : List Nat) : Nat :=
  ofB (fun t => o.eval (l.map (fun v => v.testBit t)))
def stepT (T : List Nat) (g : Gate) : List Nat :=
  T ++ [evT g.op (g.inputs.map fun i => T.getD i 0)]
def T0 : List Nat := [62, 60, 56, 48, 32, 0, 63]
theorem n6_bit : ∀ b0 b1 b2 b3 b4 b5 : Bool, ∀ t, t < 6 →
    (n6 b0 b1 b2 b3 b4 b5).testBit t = [b0, b1, b2, b3, b4, b5].getD t false := by
  decide +kernel
theorem n6_lt : ∀ b0 b1 b2 b3 b4 b5 : Bool, n6 b0 b1 b2 b3 b4 b5 < 64 := by decide +kernel
theorem ofB_bit (f : Nat → Bool) (t : Nat) (ht : t < 6) : (ofB f).testBit t = f t := by
  have h := n6_bit (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) t ht
  simp only [ofB]
  rw [h]
  interval_cases t <;> rfl
theorem evT_lt (o : GateOp) (l : List Nat) : evT o l < 64 := n6_lt _ _ _ _ _ _
theorem ofB_self : ∀ a, a < 64 → ofB (fun t => a.testBit t) = a := by decide +kernel
theorem eq_of_bits (a b : Nat) (ha : a < 64) (hb : b < 64)
    (h : ∀ t, t < 6 → a.testBit t = b.testBit t) : a = b := by
  rw [← ofB_self a ha, ← ofB_self b hb]
  simp only [ofB]
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega)]
theorem getD_tb (T : List Nat) (i t : Nat) :
    (T.map (fun v => v.testBit t)).getD i false = (T.getD i 0).testBit t := by
  induction T generalizing i with
  | nil => simp
  | cons a T ih =>
    cases i with
    | zero => rfl
    | succ n => exact ih n
theorem sim (t : Nat) (ht : t < 6) : ∀ (gs : List Gate) (x : List Bool) (T : List Nat),
    x = T.map (fun v => v.testBit t) →
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x =
    (gs.foldl stepT T).map (fun v => v.testBit t) := by
  intro gs
  induction gs with
  | nil => intro x T h; simpa using h
  | cons g gs ih =>
    intro x T h
    simp only [List.foldl_cons]
    apply ih
    subst h
    simp only [stepT, List.map_append, List.map_cons, List.map_nil, evT, ofB_bit _ _ ht,
      List.map_map, Function.comp_def, getD_tb]
theorem evT_eq (o : GateOp) (l : List Nat) (c : Nat) (hc : c < 64)
    (h : ∀ t, t < 6 → o.eval (l.map (fun v => v.testBit t)) = c.testBit t) : evT o l = c :=
  eq_of_bits _ _ (evT_lt _ _) hc (fun t ht => by rw [evT, ofB_bit _ _ ht]; exact h t ht)
theorem evT_and2 (a : Nat) (ha : a < 64) (b : Nat) (_hb : b < 64) :
    evT GateOp.and [a, b] = a &&& b :=
  evT_eq _ _ _ (Nat.lt_of_le_of_lt Nat.and_le_left ha) (fun t _ => by simp [GateOp.eval])
theorem evT_or2 (a : Nat) (ha : a < 64) (b : Nat) (hb : b < 64) :
    evT GateOp.or [a, b] = a ||| b :=
  evT_eq _ _ _ (Nat.or_lt_two_pow (n := 6) ha hb) (fun t _ => by simp [GateOp.eval])
theorem evT_not2 (a b : Nat) : evT GateOp.not [a, b] = evT GateOp.not [a] := rfl
theorem evT_and1 : ∀ a, a < 64 → evT GateOp.and [a] = a := by decide +kernel
theorem evT_or1 : ∀ a, a < 64 → evT GateOp.or [a] = a := by decide +kernel
theorem evT_not1 : ∀ a, a < 64 → evT GateOp.not [a] = a ^^^ 63 := by decide +kernel
theorem evT_and0 : evT GateOp.and [] = 63 := by decide
theorem evT_or0 : evT GateOp.or [] = 0 := by decide
theorem evT_not0 : evT GateOp.not [] = 63 := by decide
theorem getD_mem (T : List Nat) (i : Nat) : T.getD i 0 ∈ T ∨ T.getD i 0 = 0 := by
  induction T generalizing i with
  | nil => right; simp
  | cons a T ih =>
    cases i with
    | zero => left; simp
    | succ i =>
      rcases ih i with h | h
      · left; exact List.mem_cons_of_mem a h
      · right; exact h
def mems (M : Nat) : List Nat := (List.range 64).filter (fun v => M.testBit v)
def cl (M : Nat) : List Nat :=
  (mems M).flatMap (fun a => (mems M).flatMap (fun b => [a &&& b, a ||| b]))
def orm (l : List Nat) (acc : Nat) : Nat := l.foldl (fun acc v => acc ||| 2 ^ v) acc
def cands (M : Nat) : List Nat :=
  (List.range 64).filter (fun v => (orm (cl M) 0).testBit v && !M.testBit v)
def ncands (M : Nat) : List Nat :=
  ((mems M).map (fun a => a ^^^ 63)).filter (fun v => !M.testBit v)
def miss (tg : List Nat) (M : Nat) : Nat := tg.countP (fun x => !M.testBit x)
def srch (tg : List Nat) : Nat → Nat → Nat → Bool
  | 0, _, M => miss tg M == 0
  | f+1, 0, M => miss tg M == 0 || (decide (miss tg M ≤ f + 1) &&
      (cands M).any (fun v => srch tg f 0 (M ||| 2 ^ v)))
  | f+1, c+1, M => miss tg M == 0 || (decide (miss tg M ≤ f + 1) &&
      ((cands M).any (fun v => srch tg f (c+1) (M ||| 2 ^ v)) ||
        (ncands M).any (fun v => srch tg f c (M ||| 2 ^ v))))
theorem tb_ins (M v u : Nat) : (M ||| 2 ^ v).testBit u = (M.testBit u || decide (v = u)) := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]
theorem tb_mono (M v u : Nat) (h : M.testBit u = true) : (M ||| 2 ^ v).testBit u = true := by
  rw [tb_ins, h, Bool.true_or]
theorem tb_self (M v : Nat) : (M ||| 2 ^ v).testBit v = true := by
  rw [tb_ins]; simp
theorem orm_mono (l : List Nat) : ∀ acc u, acc.testBit u = true → (orm l acc).testBit u = true := by
  induction l with
  | nil => intro acc u h; exact h
  | cons v l ih => intro acc u h; exact ih _ u (tb_mono _ _ _ h)
theorem orm_mem (l : List Nat) : ∀ acc u, u ∈ l → (orm l acc).testBit u = true := by
  induction l with
  | nil => intro acc u h; cases h
  | cons v l ih =>
    intro acc u h
    rcases List.mem_cons.mp h with rfl | h
    · exact orm_mono l _ _ (tb_self _ _)
    · exact ih _ u h
theorem cnt_le (p q : Nat → Bool) (v : Nat) (hpq : ∀ y, y ≠ v → p y = q y) :
    ∀ l : List Nat, l.Nodup → l.countP p ≤ l.countP q + 1 := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro hnd
    obtain ⟨hx, hl⟩ := List.nodup_cons.mp hnd
    rw [List.countP_cons, List.countP_cons]
    by_cases hxv : x = v
    · subst hxv
      have hc : l.countP p = l.countP q :=
        List.countP_congr (fun y hy => by simp [hpq y (fun h => hx (h ▸ hy))])
      rw [hc]
      split <;> split <;> omega
    · have := ih hl
      rw [hpq x hxv]
      split <;> omega
theorem miss_ins (tg : List Nat) (htg : tg.Nodup) (M v : Nat) :
    miss tg M ≤ miss tg (M ||| 2 ^ v) + 1 := by
  apply cnt_le _ _ v _ tg htg
  intro y hy
  rw [tb_ins]
  have : decide (v = y) = false := decide_eq_false (fun h => hy h.symm)
  rw [this, Bool.or_false]
theorem mem_mems {M a : Nat} (h : a ∈ mems M) : a < 64 ∧ M.testBit a = true := by
  simpa [mems] using h
theorem mems_of {M a : Nat} (h1 : a < 64) (h2 : M.testBit a = true) : a ∈ mems M := by
  simp [mems, h1, h2]
theorem inv_getD (T : List Nat) (M : Nat) (hinv : ∀ a ∈ T, a < 64 ∧ M.testBit a = true)
    (h0 : M.testBit 0 = true) (i : Nat) : T.getD i 0 ∈ mems M := by
  rcases getD_mem T i with h | h
  · exact mems_of (hinv _ h).1 (hinv _ h).2
  · rw [h]; exact mems_of (by omega) h0
theorem classify (g : Gate) (T : List Nat) (M : Nat)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hinv : ∀ a ∈ T, a < 64 ∧ M.testBit a = true) (h0 : M.testBit 0 = true)
    (h63 : M.testBit 63 = true) :
    M.testBit (evT g.op (g.inputs.map fun i => T.getD i 0)) = true ∨
    (g.op ≠ GateOp.not ∧ evT g.op (g.inputs.map fun i => T.getD i 0) ∈ cl M) ∨
    (g.op = GateOp.not ∧
      evT g.op (g.inputs.map fun i => T.getD i 0) ∈ (mems M).map (fun a => a ^^^ 63)) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen ⊢
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · simp only [List.map_nil]
    rcases hop with rfl | rfl | rfl
    · left; rw [evT_and0]; exact h63
    · left; rw [evT_or0]; exact h0
    · left; rw [evT_not0]; exact h63
  · simp only [List.map_cons, List.map_nil]
    have ha := inv_getD T M hinv h0 i
    rcases hop with rfl | rfl | rfl
    · left; rw [evT_and1 _ (mem_mems ha).1]; exact (mem_mems ha).2
    · left; rw [evT_or1 _ (mem_mems ha).1]; exact (mem_mems ha).2
    · right; right; refine ⟨rfl, ?_⟩
      rw [evT_not1 _ (mem_mems ha).1]; exact List.mem_map.mpr ⟨_, ha, rfl⟩
  · simp only [List.map_cons, List.map_nil]
    have ha := inv_getD T M hinv h0 i
    have hb := inv_getD T M hinv h0 j
    rcases hop with rfl | rfl | rfl
    · right; left; refine ⟨(fun h => by cases h), ?_⟩
      rw [evT_and2 _ (mem_mems ha).1 _ (mem_mems hb).1]
      exact List.mem_flatMap.mpr ⟨_, ha, List.mem_flatMap.mpr ⟨_, hb, by simp⟩⟩
    · right; left; refine ⟨(fun h => by cases h), ?_⟩
      rw [evT_or2 _ (mem_mems ha).1 _ (mem_mems hb).1]
      exact List.mem_flatMap.mpr ⟨_, ha, List.mem_flatMap.mpr ⟨_, hb, by simp⟩⟩
    · right; right; refine ⟨rfl, ?_⟩
      rw [evT_not2, evT_not1 _ (mem_mems ha).1]; exact List.mem_map.mpr ⟨_, ha, rfl⟩
  · simp only [List.length_cons] at hlen; omega
theorem srch_done (tg : List Nat) (f c M : Nat) (h : miss tg M = 0) : srch tg f c M = true := by
  cases f with
  | zero => simp [srch, h]
  | succ f => cases c <;> simp [srch, h]
theorem srch_ao (tg : List Nat) (f c M v : Nat) (h : miss tg M ≤ f + 1) (hv : v ∈ cands M)
    (hs : srch tg f c (M ||| 2 ^ v) = true) : srch tg (f + 1) c M = true := by
  cases c with
  | zero =>
    simp only [srch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    exact Or.inr ⟨h, v, hv, hs⟩
  | succ c =>
    simp only [srch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    exact Or.inr ⟨h, Or.inl ⟨v, hv, hs⟩⟩
theorem srch_not (tg : List Nat) (f c M v : Nat) (h : miss tg M ≤ f + 1) (hv : v ∈ ncands M)
    (hs : srch tg f c (M ||| 2 ^ v) = true) : srch tg (f + 1) (c + 1) M = true := by
  simp only [srch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  exact Or.inr ⟨h, Or.inr ⟨v, hv, hs⟩⟩
theorem nc_le (g : Gate) (gs : List Gate) :
    PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ PEqualNP.NotBracket.notCount ⟨g :: gs, 0⟩ := by
  unfold PEqualNP.NotBracket.notCount
  simp only [List.filter_cons]
  split
  · simp
  · exact le_refl _
theorem nc_not (g : Gate) (gs : List Gate) (h : g.op = GateOp.not) :
    PEqualNP.NotBracket.notCount ⟨g :: gs, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + 1 := by
  unfold PEqualNP.NotBracket.notCount
  simp [h]
theorem fold_lt : ∀ (gs : List Gate) (T : List Nat), (∀ a ∈ T, a < 64) →
    ∀ a ∈ gs.foldl stepT T, a < 64 := by
  intro gs
  induction gs with
  | nil => intro T h; exact h
  | cons g gs ih =>
    intro T h
    apply ih
    intro a ha
    unfold stepT at ha
    rcases List.mem_append.mp ha with h' | h'
    · exact h a h'
    · rw [List.mem_singleton] at h'; rw [h']; exact evT_lt _ _
theorem sound (tg : List Nat) (htg : tg.Nodup) : ∀ (gs : List Gate) (T : List Nat) (M f c : Nat),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    gs.length ≤ f → PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ c →
    (∀ a ∈ T, a < 64 ∧ M.testBit a = true) → M.testBit 0 = true → M.testBit 63 = true →
    (∀ x ∈ tg, ∃ i, (gs.foldl stepT T).getD i 0 = x) →
    srch tg f c M = true ∧ miss tg M ≤ gs.length := by
  intro gs
  induction gs with
  | nil =>
    intro T M f c _ _ _ hinv h0 _ hx
    have hm : miss tg M = 0 := by
      unfold miss
      rw [List.countP_eq_zero]
      intro x hxt
      obtain ⟨i, hi⟩ := hx x hxt
      have h1 := mem_mems (inv_getD T M hinv h0 i)
      rw [List.foldl_nil] at hi
      rw [hi] at h1
      simp [h1.2]
    exact ⟨srch_done tg f c M hm, by rw [hm]; exact Nat.zero_le _⟩
  | cons g gs ih =>
    intro T M f c hF hlen hnc hinv h0 h63 hx
    have hg := hF g (List.mem_cons_self ..)
    have hF' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 :=
      fun g' hg' => hF g' (List.mem_cons_of_mem _ hg')
    simp only [List.length_cons] at hlen ⊢
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hlen' : gs.length ≤ f := by omega
    have hx' : ∀ x ∈ tg, ∃ i, (gs.foldl stepT (stepT T g)).getD i 0 = x := hx
    have hvlt : evT g.op (g.inputs.map fun i => T.getD i 0) < 64 := evT_lt _ _
    by_cases hvM : M.testBit (evT g.op (g.inputs.map fun i => T.getD i 0)) = true
    · have hinv' : ∀ a ∈ stepT T g, a < 64 ∧ M.testBit a = true := by
        intro a ha
        unfold stepT at ha
        rcases List.mem_append.mp ha with h' | h'
        · exact hinv a h'
        · rw [List.mem_singleton] at h'; rw [h']; exact ⟨hvlt, hvM⟩
      have r := ih (stepT T g) M (f + 1) c hF' (by omega) (le_trans (nc_le g gs) hnc)
        hinv' h0 h63 hx'
      exact ⟨r.1, by omega⟩
    · have hcl := classify g T M hg hinv h0 h63
      generalize hv : evT g.op (g.inputs.map fun i => T.getD i 0) = v at hvM hvlt hcl
      have hinv' : ∀ a ∈ stepT T g, a < 64 ∧ (M ||| 2 ^ v).testBit a = true := by
        intro a ha
        unfold stepT at ha
        rw [hv] at ha
        rcases List.mem_append.mp ha with h' | h'
        · exact ⟨(hinv a h').1, tb_mono _ _ _ (hinv a h').2⟩
        · rw [List.mem_singleton] at h'; rw [h']; exact ⟨hvlt, tb_self _ _⟩
      have hmi := miss_ins tg htg M v
      rcases hcl with hin | ⟨_, hc⟩ | ⟨hop, hn⟩
      · exact absurd hin hvM
      · have r := ih (stepT T g) (M ||| 2 ^ v) f c hF' hlen' (le_trans (nc_le g gs) hnc) hinv'
          (tb_mono _ _ _ h0) (tb_mono _ _ _ h63) hx'
        refine ⟨srch_ao tg f c M v (by omega) ?_ r.1, by omega⟩
        simp only [cands, List.mem_filter, List.mem_range, Bool.and_eq_true]
        exact ⟨hvlt, orm_mem _ _ _ hc, by simpa using hvM⟩
      · have hnc' := nc_not g gs hop
        obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        have r := ih (stepT T g) (M ||| 2 ^ v) f c hF' hlen' (by omega) hinv'
          (tb_mono _ _ _ h0) (tb_mono _ _ _ h63) hx'
        refine ⟨srch_not tg f c M v (by omega) ?_ r.1, by omega⟩
        simp only [ncands, List.mem_filter]
        exact ⟨hn, by simpa using hvM⟩
theorem hxs : ∀ t : Fin 6, (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] =
    T0.map (fun v => v.testBit t.val) := by decide
theorem tab_of (D : Circuit) (P A : Nat) (hA : A < 64)
    (h : ∀ t : Fin 6, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++
      [false, true])).getD P false = A.testBit t.val) :
    ∃ i, (D.gates.foldl stepT T0).getD i 0 = A := by
  refine ⟨P, eq_of_bits _ _ ?_ hA ?_⟩
  · rcases getD_mem (D.gates.foldl stepT T0) P with h' | h'
    · exact fold_lt D.gates T0 (by decide) _ h'
    · rw [h']; omega
  · intro t ht
    have h1 := h ⟨t, ht⟩
    rw [← getD_tb, ← sim t ht D.gates _ T0 (hxs ⟨t, ht⟩)]
    exact h1
theorem tg3 (P : Nat → Prop) (a b c : Nat) (ha : P a) (hb : P b) (hc : P c) :
    ∀ x ∈ [a, b, c], P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hc
  cases hx
theorem fa_nil (P : Nat → Prop) : ∀ v ∈ ([] : List Nat), P v := by
  intro v hv
  cases hv
theorem fa_cons (P : Nat → Prop) (a : Nat) (l : List Nat) (ha : P a) (hl : ∀ v ∈ l, P v) :
    ∀ v ∈ a :: l, P v := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ha
  · exact hl v hv
theorem any_false (p : Nat → Bool) (l : List Nat) (h : ∀ v ∈ l, p v = false) :
    l.any p = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, h a (List.mem_cons_self ..), Bool.false_or]
    exact ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
theorem srch_cut (tg : List Nat) (f c M : Nat) (lc ln : List Nat)
    (hm : (miss tg M == 0) = false) (hc : cands M = lc) (hn : ncands M = ln)
    (hlc : ∀ v ∈ lc, srch tg f (c + 1) (M ||| 2 ^ v) = false)
    (hln : ∀ v ∈ ln, srch tg f c (M ||| 2 ^ v) = false) :
    srch tg (f + 1) (c + 1) M = false := by
  have h1 : (cands M).any (fun v => srch tg f (c + 1) (M ||| 2 ^ v)) = false := by
    rw [hc]
    exact any_false _ lc hlc
  have h2 : (ncands M).any (fun v => srch tg f c (M ||| 2 ^ v)) = false := by
    rw [hn]
    exact any_false _ ln hln
  simp only [srch, hm, h1, h2, Bool.false_or, Bool.or_false, Bool.and_false]
theorem k0 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ 16) = false := by decide +kernel
theorem k1 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ 24) = false := by decide +kernel
theorem k2 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ 28) = false := by decide +kernel
theorem k3 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ 30) = false := by decide +kernel
theorem k4 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ 15) = false := by decide +kernel
theorem k5 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ 7) = false := by decide +kernel
theorem k6 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ 3) = false := by decide +kernel
theorem k7 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ 1) = false := by decide +kernel
theorem k8 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ 8) = false := by decide +kernel
theorem k9 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ 12) = false := by decide +kernel
theorem k10 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ 14) = false := by decide +kernel
theorem k11 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ 47) = false := by decide +kernel
theorem k12 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ 31) = false := by decide +kernel
theorem k13 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ 7) = false := by decide +kernel
theorem k14 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ 3) = false := by decide +kernel
theorem k15 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ 1) = false := by decide +kernel
theorem k16 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ 4) = false := by decide +kernel
theorem k17 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ 6) = false := by decide +kernel
theorem k18 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ 39) = false := by decide +kernel
theorem k19 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ 55) = false := by decide +kernel
theorem k20 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ 31) = false := by decide +kernel
theorem k21 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ 15) = false := by decide +kernel
theorem k22 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ 3) = false := by decide +kernel
theorem k23 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ 1) = false := by decide +kernel
theorem k24 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ 2) = false := by decide +kernel
theorem k25 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ 35) = false := by decide +kernel
theorem k26 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ 51) = false := by decide +kernel
theorem k27 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ 59) = false := by decide +kernel
theorem k28 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ 31) = false := by decide +kernel
theorem k29 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ 15) = false := by decide +kernel
theorem k30 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ 7) = false := by decide +kernel
theorem k31 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ 1) = false := by decide +kernel
theorem k32 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ 33) = false := by decide +kernel
theorem k33 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ 49) = false := by decide +kernel
theorem k34 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ 57) = false := by decide +kernel
theorem k35 : srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ 61) = false := by decide +kernel
theorem k36 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ 31) = false := by decide +kernel
theorem k37 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ 15) = false := by decide +kernel
theorem k38 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ 7) = false := by decide +kernel
theorem k39 : srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ 3) = false := by decide +kernel
theorem srch_false : srch [6, 37, 54] 6 2 15060318633198616577 = false :=
  (srch_cut [6, 37, 54] 5 1 15060318633198616577 [] [31, 15, 7, 3, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fa_nil _)
      (fa_cons (fun v => srch [6, 37, 54] 5 1 (15060318633198616577 ||| 2 ^ v) = false) 31 [15, 7, 3, 1] (srch_cut [6, 37, 54] 4 0 (15060318633198616577 ||| 2 ^ 31) [16, 24, 28, 30] [15, 7, 3, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ v) = false) 16 [24, 28, 30] k0 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ v) = false) 24 [28, 30] k1 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ v) = false) 28 [30] k2 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ v) = false) 30 [] k3 (fa_nil _)))))
      (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ v) = false) 15 [7, 3, 1] k4 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ v) = false) 7 [3, 1] k5 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ v) = false) 3 [1] k6 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 31) ||| 2 ^ v) = false) 1 [] k7 (fa_nil _)))))) (fa_cons (fun v => srch [6, 37, 54] 5 1 (15060318633198616577 ||| 2 ^ v) = false) 15 [7, 3, 1] (srch_cut [6, 37, 54] 4 0 (15060318633198616577 ||| 2 ^ 15) [8, 12, 14, 47] [31, 7, 3, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ v) = false) 8 [12, 14, 47] k8 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ v) = false) 12 [14, 47] k9 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ v) = false) 14 [47] k10 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ v) = false) 47 [] k11 (fa_nil _)))))
      (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ v) = false) 31 [7, 3, 1] k12 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ v) = false) 7 [3, 1] k13 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ v) = false) 3 [1] k14 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 15) ||| 2 ^ v) = false) 1 [] k15 (fa_nil _)))))) (fa_cons (fun v => srch [6, 37, 54] 5 1 (15060318633198616577 ||| 2 ^ v) = false) 7 [3, 1] (srch_cut [6, 37, 54] 4 0 (15060318633198616577 ||| 2 ^ 7) [4, 6, 39, 55] [31, 15, 3, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ v) = false) 4 [6, 39, 55] k16 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ v) = false) 6 [39, 55] k17 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ v) = false) 39 [55] k18 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ v) = false) 55 [] k19 (fa_nil _)))))
      (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ v) = false) 31 [15, 3, 1] k20 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ v) = false) 15 [3, 1] k21 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ v) = false) 3 [1] k22 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 7) ||| 2 ^ v) = false) 1 [] k23 (fa_nil _)))))) (fa_cons (fun v => srch [6, 37, 54] 5 1 (15060318633198616577 ||| 2 ^ v) = false) 3 [1] (srch_cut [6, 37, 54] 4 0 (15060318633198616577 ||| 2 ^ 3) [2, 35, 51, 59] [31, 15, 7, 1] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ v) = false) 2 [35, 51, 59] k24 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ v) = false) 35 [51, 59] k25 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ v) = false) 51 [59] k26 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ v) = false) 59 [] k27 (fa_nil _)))))
      (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ v) = false) 31 [15, 7, 1] k28 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ v) = false) 15 [7, 1] k29 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ v) = false) 7 [1] k30 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 3) ||| 2 ^ v) = false) 1 [] k31 (fa_nil _)))))) (fa_cons (fun v => srch [6, 37, 54] 5 1 (15060318633198616577 ||| 2 ^ v) = false) 1 [] (srch_cut [6, 37, 54] 4 0 (15060318633198616577 ||| 2 ^ 1) [33, 49, 57, 61] [31, 15, 7, 3] (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ v) = false) 33 [49, 57, 61] k32 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ v) = false) 49 [57, 61] k33 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ v) = false) 57 [61] k34 (fa_cons (fun v => srch [6, 37, 54] 4 (0 + 1) ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ v) = false) 61 [] k35 (fa_nil _)))))
      (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ v) = false) 31 [15, 7, 3] k36 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ v) = false) 15 [7, 3] k37 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ v) = false) 7 [3] k38 (fa_cons (fun v => srch [6, 37, 54] 4 0 ((15060318633198616577 ||| 2 ^ 1) ||| 2 ^ v) = false) 3 [] k39 (fa_nil _)))))) (fa_nil _)))))))
end PEqualNP.Outside.L_meta_50554
theorem PEqualNP.Outside.L_meta_50554 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (37 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hF, -, hN, hS, hw⟩
  have h := PEqualNP.Outside.L_meta_50554.sound [6, 37, 54] (by decide) D.gates
    PEqualNP.Outside.L_meta_50554.T0 15060318633198616577 6 2 hF hS hN (by decide) (by decide) (by decide)
    (PEqualNP.Outside.L_meta_50554.tg3
      (fun x => ∃ i, (D.gates.foldl PEqualNP.Outside.L_meta_50554.stepT
        PEqualNP.Outside.L_meta_50554.T0).getD i 0 = x) 6 37 54
      (PEqualNP.Outside.L_meta_50554.tab_of D p.val 6 (by decide) (fun t => (hw t).1))
      (PEqualNP.Outside.L_meta_50554.tab_of D q.val 37 (by decide) (fun t => (hw t).2.1))
      (PEqualNP.Outside.L_meta_50554.tab_of D r.val 54 (by decide) (fun t => (hw t).2.2)))
  have h1 := h.1
  rw [PEqualNP.Outside.L_meta_50554.srch_false] at h1
  exact absurd h1 (by decide)
