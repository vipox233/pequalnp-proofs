import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25780

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev BT (α : Type) : ℕ → Type
  | 0 => α
  | d + 1 => BT α d × BT α d

def btGet {α : Type} : {d : ℕ} → BT α d → ℕ → α
  | 0, x, _ => x
  | d + 1, (l, r), i => if i.testBit d then btGet r i else btGet l i

def btAll {α : Type} (p : α → Bool) : {d : ℕ} → BT α d → Bool
  | 0, x => p x
  | _ + 1, (l, r) => btAll p l && btAll p r

theorem btAll_get {α : Type} (p : α → Bool) : ∀ {_d : ℕ} (t : BT α _d) (i : ℕ),
    btAll p t = true → p (btGet t i) = true
  | 0, _, _, h => h
  | _ + 1, (l, r), i, h => by
    simp only [btAll, Bool.and_eq_true] at h
    simp only [btGet]
    split_ifs
    · exact btAll_get p r i h.2
    · exact btAll_get p l i h.1

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
    have hstep : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [hstep, ht]
    simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]
  simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem wiresFrom_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (wiresFrom gs w).getD i false = false := by
  rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)]

theorem wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k]'hk :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    have h2 : gs.drop k = gs[k]'hk :: gs.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    exact h1
  conv_lhs => rw [hsplit]
  rw [wiresFrom_append]
  set w0 := wiresFrom (gs.take k) w
  have hw0len : w0.length = w.length + k := by
    rw [length_wiresFrom, List.length_take]
    omega
  have hstep : wiresFrom (gs[k]'hk :: gs.drop (k + 1)) w0 =
      wiresFrom (gs.drop (k + 1)) (w0 ++ [(gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => w0.getD i false)]) := rfl
  rw [hstep]
  have hlt : w.length + k < (w0 ++ [(gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => w0.getD i false)]).length := by
    simp [hw0len]
  rw [getD_wiresFrom _ _ _ hlt]
  have hidx : (w0 ++ [(gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => w0.getD i false)]).getD (w.length + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => w0.getD i false) := by
    rw [← hw0len]
    simp
  rw [hidx]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length + k
  · simp only [hi, ↓reduceIte]
    conv_rhs => rw [hsplit]
    rw [wiresFrom_append]
    exact (getD_wiresFrom _ _ i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    rw [List.getD_eq_default _ _ (by omega)]

def st (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)

def pick (b t f : Bool) : Bool := Bool.rec (motive := fun _ => Bool) f t b

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

def loopN (goal : ℕ) (f : ℕ → List ℕ → Bool) : ℕ → List ℕ → Bool
  | 0, _ => false
  | _, [] => false
  | n + 1, z :: post => pick (Nat.beq z goal) true (pick (f z post) true (loopN goal f n post))

theorem loop_split (goal : ℕ) (f : ℕ → List ℕ → Bool) (n : ℕ) :
    ∀ L, loopN goal f n L = false → loop goal f (L.drop n) = false → loop goal f L = false := by
  induction n with
  | zero => intro L _ h; exact h
  | succ n ih =>
    intro L h1 h2
    cases L with
    | nil => rfl
    | cons z post =>
      change pick (Nat.beq z goal) true (pick (f z post) true (loopN goal f n post)) = false at h1
      change pick (Nat.beq z goal) true (pick (f z post) true (loop goal f post)) = false
      cases hb : Nat.beq z goal
      · rw [hb] at h1
        change pick (f z post) true (loopN goal f n post) = false at h1
        cases hf : f z post
        · rw [hf] at h1
          exact ih post h1 h2
        · rw [hf] at h1; exact Bool.noConfusion h1
      · rw [hb] at h1; exact Bool.noConfusion h1

def srch (M goal : ℕ) (j : ℕ) : List ℕ → ℕ → List ℕ → Bool :=
  Nat.rec (motive := fun _ => List ℕ → ℕ → List ℕ → Bool) (fun ws _ L => chk M goal ws L)
    (fun _ ih ws s L => loop goal (fun z post => st (Nat.xor z M) fun q => ext1 q s post fun L s =>
      grow z ws s L fun L s => ih (z :: ws) s L) L) j

def stepTop (M goal : ℕ) (j : ℕ) (ws : List ℕ) (s : ℕ) (z : ℕ) (post : List ℕ) : Bool :=
  st (Nat.xor z M) fun q => ext1 q s post fun L s =>
    grow z ws s L fun L s => srch M goal j (z :: ws) s L

theorem srch_succ_eq (M goal j : ℕ) (ws : List ℕ) (s : ℕ) (L : List ℕ) :
    srch M goal (j + 1) ws s L = loop goal (stepTop M goal j ws s) L := rfl

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
      · have hcd : c = d := of_decide_eq_true hd
        exact .inr (hcd ▸ List.mem_cons_self)

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
    rcases hx with rfl | rfl | hx
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact (h x (.inr hx)).imp id .inr

theorem Der_snoc (M : ℕ) : ∀ (D ws : List ℕ) (d : ℕ),
    Der M ws D → (d ∈ 0 :: (D.reverse ++ ws) ∨ Ob M (D.reverse ++ ws) d) →
    Der M ws (D ++ [d]) := by
  intro D
  induction D with
  | nil =>
    intro ws d _ hd
    exact ⟨by simpa using hd, trivial⟩
  | cons a D ih =>
    intro ws d hD hd
    refine ⟨hD.1, ih (a :: ws) d hD.2 ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using hd

theorem Der_filter (M z : ℕ) : ∀ (D ws ws' : List ℕ), (∀ x ∈ ws, x ∈ ws') → z ∈ ws' →
    Der M ws D → Der M ws' (D.filter fun x => decide (x ≠ z)) := by
  intro D
  induction D with
  | nil => intro ws ws' _ _ _; trivial
  | cons d D ih =>
    intro ws ws' hsub hz hD
    have h0 : ∀ x ∈ 0 :: ws, x ∈ 0 :: ws' := fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub x hx)
    by_cases hdz : d = z
    · subst hdz
      simpa using ih (d :: ws) ws' (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hz
        · exact hsub x hx) hz hD.2
    · have hf : (d :: D).filter (fun x => decide (x ≠ z)) = d :: D.filter (fun x => decide (x ≠ z)) := by
        simp [hdz]
      rw [hf]
      refine ⟨Ob_mono h0 hD.1, ih (d :: ws) (d :: ws') (fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub x hx)) (List.mem_cons_of_mem _ hz) hD.2⟩

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
          · exact Der_filter M z D ws (z :: ws) (fun x hx => List.mem_cons_of_mem _ hx) List.mem_cons_self hD
          · have hlt : (D.filter fun x => decide (x ≠ z)).length < D.length :=
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

def W0 : List ℕ := [7, 56, 448, 73, 146, 292]

def L0 : List ℕ := [511, 504, 455, 63, 438, 365, 219, 1, 79, 2, 151, 4, 295, 8, 121, 16, 186, 32, 316, 64, 457, 128, 466, 256, 484]

def rawL0 : List ℕ :=
  511 :: W0.map (fun a => a ^^^ 511) ++
    W0.flatMap (fun a => W0.flatMap (fun b => [a &&& b, a ||| b]))

theorem raw_mem {d : ℕ} (h : Ob 511 W0 d) : d ∈ rawL0 := by
  unfold rawL0
  rcases h with rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl | rfl⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨a, ha, rfl⟩))
  · exact List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨a, ha, List.mem_flatMap.2 ⟨b, hb, by simp⟩⟩))
  · exact List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨a, ha, List.mem_flatMap.2 ⟨b, hb, by simp⟩⟩))

theorem raw_L0 : ∀ d ∈ rawL0, d ∈ 0 :: W0 ∨ d ∈ L0 := by decide +kernel

def maskOf : List ℕ → ℕ
  | [] => 0
  | x :: xs => 2 ^ x ||| maskOf xs

theorem maskOf_bit : ∀ (xs : List ℕ) (d : ℕ), (maskOf xs).testBit d = true → d ∈ xs := by
  intro xs
  induction xs with
  | nil => intro d h; simp [maskOf] at h
  | cons x xs ih =>
    intro d h
    simp only [maskOf, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at h
    rcases h with h | h
    · exact (of_decide_eq_true h) ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih d h)

def seen0 : ℕ := 6756278264645804627077973060856148259526718073466519407968896533989437490412491062901373979313941092812702659559342377725348607425508021385093378222391703

theorem seen0_eq : seen0 = maskOf (0 :: W0 ++ L0) := by decide +kernel

def Forbidden (goal cap : ℕ) : Prop :=
  ∀ D, Der 511 W0 D → D.length ≤ cap → goal ∉ 0 :: W0 ∧ goal ∉ D

theorem noneZero (g : ℕ) (hg : g ∉ 0 :: W0) : Forbidden g 0 := by
  intro D _ hl
  have h0 : D = [] := List.length_eq_zero_iff.mp (by omega)
  exact ⟨hg, by simp [h0]⟩

theorem noneOne (g : ℕ) (hg : g ∉ 0 :: W0) (hL : g ∉ L0) : Forbidden g 1 := by
  intro D hd hl
  refine ⟨hg, ?_⟩
  intro h
  obtain ⟨d, hdD, hd0, hdo⟩ := Der_first 511 g W0 hg D hd h
  have one : d = g := by
    cases D with
    | nil => simp at h
    | cons a ds =>
      have e : ds = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hl; omega)
      subst ds
      have da : d = a := by simpa using hdD
      have ga : g = a := by simpa using h
      exact da.trans ga.symm
  subst d
  exact hL ((raw_L0 g (raw_mem hdo)).resolve_left hg)

theorem noneSearch (g j : ℕ) (hg : g ∉ 0 :: W0)
    (hs : srch 511 g j W0 seen0 L0 = false) : Forbidden g (j + 2) := by
  intro D hd hl
  refine ⟨hg, fun h => ?_⟩
  have found := srch_sound 511 g j W0 seen0 L0 D hd hl h hg
    (fun d _ hd0 ho => (raw_L0 d (raw_mem ho)).resolve_left hd0)
    (fun d _ hd0 hb => by
      rw [seen0_eq] at hb
      rcases List.mem_append.1 (maskOf_bit _ _ hb) with h | h
      · exact (hd0 h).elim
      · exact h)
  rw [hs] at found
  exact Bool.noConfusion found

theorem noneSearchSplit (g j : ℕ) (hg : g ∉ 0 :: W0)
    (h0 : loopN g (stepTop 511 g j W0 seen0) 5 (L0.drop 0) = false)
    (h1 : loopN g (stepTop 511 g j W0 seen0) 5 (L0.drop 5) = false)
    (h2 : loopN g (stepTop 511 g j W0 seen0) 5 (L0.drop 10) = false)
    (h3 : loopN g (stepTop 511 g j W0 seen0) 5 (L0.drop 15) = false)
    (h4 : loop g (stepTop 511 g j W0 seen0) (L0.drop 20) = false) :
    Forbidden g (j + 3) := by
  have hs : srch 511 g (j + 1) W0 seen0 L0 = false := by
    rw [srch_succ_eq]
    have r3 : loop g (stepTop 511 g j W0 seen0) (L0.drop 15) = false :=
      loop_split g _ 5 (L0.drop 15) h3 (by simpa [List.drop_drop] using h4)
    have r2 : loop g (stepTop 511 g j W0 seen0) (L0.drop 10) = false :=
      loop_split g _ 5 (L0.drop 10) h2 (by simpa [List.drop_drop] using r3)
    have r1 : loop g (stepTop 511 g j W0 seen0) (L0.drop 5) = false :=
      loop_split g _ 5 (L0.drop 5) h1 (by simpa [List.drop_drop] using r2)
    exact loop_split g _ 5 L0 h0 r1
  exact noneSearch g (j + 1) hg hs

theorem forbid_1 : Forbidden 1 0 := noneZero 1 (by decide)
theorem forbid_127 : Forbidden 127 0 := noneZero 127 (by decide)
theorem forbid_3 : Forbidden 3 1 := noneOne 3 (by decide) (by decide)
theorem forbid_15 : Forbidden 15 1 := noneOne 15 (by decide) (by decide)
theorem forbid_27 : Forbidden 27 1 := noneOne 27 (by decide) (by decide)
theorem forbid_95 : Forbidden 95 1 := noneOne 95 (by decide) (by decide)
theorem forbid_255 : Forbidden 255 1 := noneOne 255 (by decide) (by decide)
theorem forbid_10 : Forbidden 10 2 := noneSearch 10 0 (by decide) (by decide +kernel)
theorem forbid_31 : Forbidden 31 2 := noneSearch 31 0 (by decide) (by decide +kernel)
theorem forbid_87 : Forbidden 87 2 := noneSearch 87 0 (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbid_11 : Forbidden 11 3 := noneSearch 11 1 (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbid_14 : Forbidden 14 3 := noneSearch 14 1 (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbid_78 : Forbidden 78 3 := noneSearch 78 1 (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbid_118 : Forbidden 118 3 := noneSearch 118 1 (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbid_119 : Forbidden 119 3 := noneSearch 119 1 (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbid_239 : Forbidden 239 3 := noneSearch 239 1 (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbid_29 : Forbidden 29 4 := noneSearch 29 2 (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbid_84 : Forbidden 84 4 := noneSearch 84 2 (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem forbid_85 : Forbidden 85 4 := noneSearch 85 2 (by decide) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f94_0 : loopN 94 (stepTop 511 94 2 W0 seen0) 5 (L0.drop 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f94_1 : loopN 94 (stepTop 511 94 2 W0 seen0) 5 (L0.drop 5) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f94_2 : loopN 94 (stepTop 511 94 2 W0 seen0) 5 (L0.drop 10) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f94_3 : loopN 94 (stepTop 511 94 2 W0 seen0) 5 (L0.drop 15) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f94_4 : loop 94 (stepTop 511 94 2 W0 seen0) (L0.drop 20) = false := by decide +kernel
theorem forbid_94 : Forbidden 94 5 := noneSearchSplit 94 2 (by decide) f94_0 f94_1 f94_2 f94_3 f94_4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f238_0 : loopN 238 (stepTop 511 238 2 W0 seen0) 5 (L0.drop 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f238_1 : loopN 238 (stepTop 511 238 2 W0 seen0) 5 (L0.drop 5) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f238_2 : loopN 238 (stepTop 511 238 2 W0 seen0) 5 (L0.drop 10) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f238_3 : loopN 238 (stepTop 511 238 2 W0 seen0) 5 (L0.drop 15) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem f238_4 : loop 238 (stepTop 511 238 2 W0 seen0) (L0.drop 20) = false := by decide +kernel
theorem forbid_238 : Forbidden 238 5 := noneSearchSplit 238 2 (by decide) f238_0 f238_1 f238_2 f238_3 f238_4

def bans3 : List (ℕ × ℕ) := [(1, 0), (127, 0), (3, 1), (15, 1), (27, 1), (95, 1), (255, 1), (10, 2), (31, 2), (87, 2), (11, 3), (14, 3), (78, 3), (118, 3), (119, 3), (239, 3), (29, 4), (84, 4), (85, 4), (94, 5), (238, 5)]

theorem certified_bans3 : ∀ b ∈ bans3, Forbidden b.1 b.2 := by
  intro b hb
  simp only [bans3, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact forbid_1
  · exact forbid_127
  · exact forbid_3
  · exact forbid_15
  · exact forbid_27
  · exact forbid_95
  · exact forbid_255
  · exact forbid_10
  · exact forbid_31
  · exact forbid_87
  · exact forbid_11
  · exact forbid_14
  · exact forbid_78
  · exact forbid_118
  · exact forbid_119
  · exact forbid_239
  · exact forbid_29
  · exact forbid_84
  · exact forbid_85
  · exact forbid_94
  · exact forbid_238

def effInputs (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def mask9Aux (gs : List Gate) (w : ℕ → List Bool) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
    mask9Aux gs w i r ||| (if (wiresFrom gs (w r)).getD i false then 2 ^ r else 0)

def mask9 (gs : List Gate) (w : ℕ → List Bool) (i : ℕ) : ℕ :=
  mask9Aux gs w i 9

theorem pow_ge_512 (r : ℕ) (hr : 9 ≤ r) : 512 ≤ 2 ^ r :=
  Nat.pow_le_pow_right (n := 2) (by decide) hr

theorem pow_ge_65536 (r : ℕ) (hr : 16 ≤ r) : 65536 ≤ 2 ^ r :=
  Nat.pow_le_pow_right (n := 2) (by decide) hr

theorem mask9Aux_lt (gs : List Gate) (w : ℕ → List Bool) (i : ℕ) :
    ∀ n, mask9Aux gs w i n < 2 ^ n := by
  intro n
  induction n with
  | zero => simp [mask9Aux]
  | succ n ih =>
    unfold mask9Aux
    have hpow : 2 ^ n < 2 ^ (n + 1) := by
      have hp : 0 < 2 ^ n := Nat.two_pow_pos n
      rw [Nat.pow_succ]
      omega
    have h1 : mask9Aux gs w i n < 2 ^ (n + 1) := lt_trans ih hpow
    cases (wiresFrom gs (w n)).getD i false
    · simpa using h1
    · exact Nat.or_lt_two_pow h1 hpow

theorem mask9_lt (gs : List Gate) (w : ℕ → List Bool) (i : ℕ) : mask9 gs w i < 512 :=
  mask9Aux_lt gs w i 9

theorem mask9Aux_testBit (gs : List Gate) (w : ℕ → List Bool) (i : ℕ) :
    ∀ n r, (mask9Aux gs w i n).testBit r = if r < n then (wiresFrom gs (w r)).getD i false else false := by
  intro n
  induction n with
  | zero => intro r; simp [mask9Aux]
  | succ n ih =>
    intro r
    unfold mask9Aux
    rw [Nat.testBit_or, ih r]
    by_cases hlt : r < n
    · have hne : n ≠ r := by omega
      have hlt2 : r < n + 1 := by omega
      cases (wiresFrom gs (w n)).getD i false <;>
        simp [hlt, hlt2, hne]
    · by_cases heq : r = n
      · subst heq
        cases hb : (wiresFrom gs (w r)).getD i false <;> simp
      · have hne : n ≠ r := by omega
        have hlt2 : ¬ r < n + 1 := by omega
        cases (wiresFrom gs (w n)).getD i false <;>
          simp [hlt, hlt2, hne]

theorem mask9_testBit (gs : List Gate) (w : ℕ → List Bool) (i r : ℕ) (hr : r < 9) :
    (mask9 gs w i).testBit r = (wiresFrom gs (w r)).getD i false := by
  rw [mask9, mask9Aux_testBit]
  simp only [hr, ↓reduceIte]

theorem mask9_ge (gs : List Gate) (w : ℕ → List Bool) (hw : ∀ r < 9, (w r).length = 8)
    (i : ℕ) (hi : 8 + gs.length ≤ i) : mask9 gs w i = 0 := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 9
  · rw [mask9_testBit gs w i r hr, Nat.zero_testBit]
    exact wiresFrom_getD_ge gs (w r) i (by rw [hw r hr]; exact hi)
  · have h2 : 512 ≤ 2 ^ r := pow_ge_512 r (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (mask9_lt gs w i) h2), Nat.zero_testBit]

theorem testBit_511 (r : ℕ) : (511 : ℕ).testBit r = decide (r < 9) := by
  have h : (511 : ℕ) = 2 ^ 9 - 1 := rfl
  rw [h, Nat.testBit_two_pow_sub_one]

theorem and_511 (x : ℕ) (hx : x < 512) : x &&& 511 = x := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [Nat.testBit_and, testBit_511]
  by_cases hr : r < 9
  · simp [hr]
  · have h2 : 512 ≤ 2 ^ r := pow_ge_512 r (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx h2)]
    simp [hr]

theorem or_511 (x : ℕ) (hx : x < 512) : x ||| 511 = 511 := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [Nat.testBit_or, testBit_511]
  by_cases hr : r < 9
  · simp [hr]
  · have h2 : 512 ≤ 2 ^ r := pow_ge_512 r (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx h2)]
    simp [hr]

theorem eq_of_bits_lt512 (x y : ℕ) (hx : x < 512) (hy : y < 512)
    (h : ∀ r < 9, x.testBit r = y.testBit r) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 9
  · exact h r hr
  · have h2 : 512 ≤ 2 ^ r := pow_ge_512 r (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx h2),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hy h2)]

theorem mask9_gate (gs : List Gate) (w : ℕ → List Bool) (hw : ∀ r < 9, (w r).length = 8)
    (k : ℕ) (hk : k < gs.length) :
    let v : ℕ → ℕ := fun i => if i < 8 + k then mask9 gs w i else 0
    match (gs[k]'hk).op, (gs[k]'hk).inputs with
    | .not, [] => mask9 gs w (8 + k) = 511
    | .not, a :: _ => mask9 gs w (8 + k) = v a ^^^ 511
    | .and, [] => mask9 gs w (8 + k) = 511
    | .and, [a] => mask9 gs w (8 + k) = v a
    | .and, [a, b] => mask9 gs w (8 + k) = v a &&& v b
    | .or, [] => mask9 gs w (8 + k) = 0
    | .or, [a] => mask9 gs w (8 + k) = v a
    | .or, [a, b] => mask9 gs w (8 + k) = v a ||| v b
    | _, _ => True := by
  intro v
  have hv_lt : ∀ i, v i < 512 := fun i => by
    dsimp only [v]
    split_ifs
    · exact mask9_lt gs w i
    · decide
  have hv_bit : ∀ i r, r < 9 → (v i).testBit r =
      if i < 8 + k then (wiresFrom gs (w r)).getD i false else false := by
    intro i r hr
    dsimp only [v]
    split_ifs with hi
    · exact mask9_testBit gs w i r hr
    · simp
  have hgate_bit : ∀ r, r < 9 → (mask9 gs w (8 + k)).testBit r =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => (v i).testBit r) := by
    intro r hr
    rw [mask9_testBit gs w (8 + k) r hr]
    have hlen := hw r hr
    have hg := wiresFrom_getD_gate gs (w r) k hk
    rw [hlen] at hg
    rw [hg]
    congr 1
    apply List.map_congr_left
    intro i _
    exact (hv_bit i r hr).symm
  cases hop : (gs[k]'hk).op with
  | and =>
    cases hins : (gs[k]'hk).inputs with
    | nil =>
      apply eq_of_bits_lt512 _ _ (mask9_lt gs w (8 + k)) (by decide)
      intro r hr; rw [hgate_bit r hr, hop, hins, testBit_511]; simp [GateOp.eval, hr]
    | cons a rest =>
      cases rest with
      | nil =>
        apply eq_of_bits_lt512 _ _ (mask9_lt gs w (8 + k)) (hv_lt a)
        intro r hr; rw [hgate_bit r hr, hop, hins]; simp [GateOp.eval]
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          apply eq_of_bits_lt512 _ _ (mask9_lt gs w (8 + k)) (Nat.and_lt_two_pow (n := 9) (v a) (hv_lt b))
          intro r hr; rw [hgate_bit r hr, hop, hins, Nat.testBit_and]; simp [GateOp.eval]
        | cons _ _ => trivial
  | or =>
    cases hins : (gs[k]'hk).inputs with
    | nil =>
      apply eq_of_bits_lt512 _ _ (mask9_lt gs w (8 + k)) (by decide)
      intro r hr; rw [hgate_bit r hr, hop, hins]; simp [GateOp.eval]
    | cons a rest =>
      cases rest with
      | nil =>
        apply eq_of_bits_lt512 _ _ (mask9_lt gs w (8 + k)) (hv_lt a)
        intro r hr; rw [hgate_bit r hr, hop, hins]; simp [GateOp.eval]
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          apply eq_of_bits_lt512 _ _ (mask9_lt gs w (8 + k)) (Nat.or_lt_two_pow (n := 9) (hv_lt a) (hv_lt b))
          intro r hr; rw [hgate_bit r hr, hop, hins, Nat.testBit_or]; simp [GateOp.eval]
        | cons _ _ => trivial
  | not =>
    cases hins : (gs[k]'hk).inputs with
    | nil =>
      apply eq_of_bits_lt512 _ _ (mask9_lt gs w (8 + k)) (by decide)
      intro r hr; rw [hgate_bit r hr, hop, hins, testBit_511]; simp [GateOp.eval, hr]
    | cons a rest =>
      apply eq_of_bits_lt512 _ _ (mask9_lt gs w (8 + k)) (Nat.xor_lt_two_pow (n := 9) (hv_lt a) (by decide))
      intro r hr; rw [hgate_bit r hr, hop, hins, Nat.testBit_xor, testBit_511]; simp [GateOp.eval, hr]
  | mod _ => trivial
  | maj => trivial

theorem gate_ob_or_mem (gs : List Gate) (w : ℕ → List Bool) (hw : ∀ r < 9, (w r).length = 8)
    (k : ℕ) (hk : k < gs.length)
    (hok : (gs[k]'hk).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (gs[k]'hk).inputs.length ≤ 2)
    (ws : List ℕ) (hws : ∀ i < 8 + k, mask9 gs w i ∈ 0 :: 511 :: ws) :
    mask9 gs w (8 + k) ∈ 0 :: 511 :: ws ∨ Ob 511 ws (mask9 gs w (8 + k)) := by
  have hg := mask9_gate gs w hw k hk
  set v : ℕ → ℕ := fun i => if i < 8 + k then mask9 gs w i else 0
  have hv_mem : ∀ i, v i ∈ 0 :: 511 :: ws := fun i => by
    dsimp only [v]
    split_ifs with hi
    · exact hws i hi
    · exact List.mem_cons_self
  have hv_lt : ∀ i, v i < 512 := fun i => by
    dsimp only [v]
    split_ifs
    · exact mask9_lt gs w i
    · decide
  obtain ⟨hopm, hlen⟩ := hok
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hopm
  rcases hopm with hop | hop | hop
  · rw [hop] at hg
    rcases hins : (gs[k]'hk).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · rw [hins] at hg; dsimp only at hg; exact .inl (hg ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    · rw [hins] at hg; dsimp only at hg; exact .inl (hg ▸ hv_mem a)
    · rw [hins] at hg; dsimp only at hg
      rcases List.mem_cons.1 (hv_mem a) with ha0 | ha1
      · rw [ha0] at hg; exact .inl (by simp [hg])
      · rcases List.mem_cons.1 ha1 with ha511 | haws
        · rw [ha511, Nat.and_comm, and_511 _ (hv_lt b)] at hg; exact .inl (hg ▸ hv_mem b)
        · rcases List.mem_cons.1 (hv_mem b) with hb0 | hb1
          · rw [hb0] at hg; exact .inl (by simp [hg])
          · rcases List.mem_cons.1 hb1 with hb511 | hbws
            · rw [hb511, and_511 _ (hv_lt a)] at hg; exact .inl (hg ▸ hv_mem a)
            · exact .inr (.inr (.inr ⟨v a, haws, v b, hbws, .inl hg⟩))
    · rw [hins] at hlen; simp at hlen
  · rw [hop] at hg
    rcases hins : (gs[k]'hk).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · rw [hins] at hg; dsimp only at hg; exact .inl (hg ▸ List.mem_cons_self)
    · rw [hins] at hg; dsimp only at hg; exact .inl (hg ▸ hv_mem a)
    · rw [hins] at hg; dsimp only at hg
      rcases List.mem_cons.1 (hv_mem a) with ha0 | ha1
      · rw [ha0] at hg; exact .inl (by simpa [hg] using hv_mem b)
      · rcases List.mem_cons.1 ha1 with ha511 | haws
        · rw [ha511, Nat.or_comm, or_511 _ (hv_lt b)] at hg
          exact .inl (hg ▸ List.mem_cons_of_mem _ List.mem_cons_self)
        · rcases List.mem_cons.1 (hv_mem b) with hb0 | hb1
          · rw [hb0] at hg; exact .inl (by simpa [hg] using hv_mem a)
          · rcases List.mem_cons.1 hb1 with hb511 | hbws
            · rw [hb511, or_511 _ (hv_lt a)] at hg
              exact .inl (hg ▸ List.mem_cons_of_mem _ List.mem_cons_self)
            · exact .inr (.inr (.inr ⟨v a, haws, v b, hbws, .inr hg⟩))
    · rw [hins] at hlen; simp at hlen
  · rw [hop] at hg
    rcases hins : (gs[k]'hk).inputs with _ | ⟨a, rest⟩
    · rw [hins] at hg; dsimp only at hg; exact .inl (hg ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    · rw [hins] at hg; dsimp only at hg
      rcases List.mem_cons.1 (hv_mem a) with ha0 | ha1
      · rw [ha0] at hg; exact .inl (by simp [hg])
      · rcases List.mem_cons.1 ha1 with ha511 | haws
        · rw [ha511, Nat.xor_self] at hg; exact .inl (hg ▸ List.mem_cons_self)
        · exact .inr (.inr (.inl ⟨v a, haws, hg⟩))

theorem gate_skip_of_zero (gs : List Gate) (w : ℕ → List Bool) (hw : ∀ r < 9, (w r).length = 8)
    (k : ℕ) (hk : k < gs.length)
    (hok : (gs[k]'hk).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (gs[k]'hk).inputs.length ≤ 2)
    (ws : List ℕ) (hws : ∀ i < 8 + k, mask9 gs w i ∈ 0 :: 511 :: ws)
    (a : ℕ) (ha : a ∈ effInputs (gs[k]'hk)) (halt : a < 8 + k) (ha0 : mask9 gs w a = 0) :
    mask9 gs w (8 + k) ∈ 0 :: 511 :: ws := by
  have hg := mask9_gate gs w hw k hk
  set v : ℕ → ℕ := fun i => if i < 8 + k then mask9 gs w i else 0
  have hva : v a = 0 := by simp [v, halt, ha0]
  have hv_mem : ∀ i, v i ∈ 0 :: 511 :: ws := fun i => by
    dsimp only [v]
    split_ifs with hi
    · exact hws i hi
    · exact List.mem_cons_self
  obtain ⟨hopm, hlen⟩ := hok
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hopm
  rcases hopm with hop | hop | hop
  · rw [hop] at hg
    have ha' : a ∈ (gs[k]'hk).inputs := by simpa [effInputs, hop] using ha
    rcases hins : (gs[k]'hk).inputs with _ | ⟨x, _ | ⟨y, _ | ⟨c, l⟩⟩⟩
    · rw [hins] at ha'; simp at ha'
    · rw [hins] at hg ha'; dsimp only at hg; simp at ha'; subst ha'; rw [hva] at hg; exact hg ▸ List.mem_cons_self
    · rw [hins] at hg ha'; dsimp only at hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · rw [hva] at hg; simp [hg]
      · rw [hva] at hg; simp [hg]
    · rw [hins] at hlen; simp at hlen
  · rw [hop] at hg
    have ha' : a ∈ (gs[k]'hk).inputs := by simpa [effInputs, hop] using ha
    rcases hins : (gs[k]'hk).inputs with _ | ⟨x, _ | ⟨y, _ | ⟨c, l⟩⟩⟩
    · rw [hins] at ha'; simp at ha'
    · rw [hins] at hg ha'; dsimp only at hg; simp at ha'; subst ha'; rw [hva] at hg; exact hg ▸ List.mem_cons_self
    · rw [hins] at hg ha'; dsimp only at hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · rw [hva] at hg; simpa [hg] using hv_mem y
      · rw [hva] at hg; simpa [hg] using hv_mem x
    · rw [hins] at hlen; simp at hlen
  · rw [hop] at hg
    have ha' : a ∈ (gs[k]'hk).inputs.take 1 := by simpa [effInputs, hop] using ha
    rcases hins : (gs[k]'hk).inputs with _ | ⟨x, rest⟩
    · rw [hins] at ha'; simp at ha'
    · rw [hins] at hg ha'; dsimp only at hg
      simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at ha'
      subst ha'
      rw [hva] at hg
      simp [hg]

theorem buildDer_aux (gs : List Gate) (w : ℕ → List Bool) (hw : ∀ r < 9, (w r).length = 8)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hinit : ∀ i < 8, mask9 gs w i ∈ 0 :: 511 :: W0)
    (k1 k2 : ℕ) (hne : k1 ≠ k2)
    (hsk1 : k1 < gs.length → ∀ ws, (∀ i < 8 + k1, mask9 gs w i ∈ 0 :: 511 :: ws) → mask9 gs w (8 + k1) ∈ 0 :: 511 :: ws)
    (hsk2 : k2 < gs.length → ∀ ws, (∀ i < 8 + k2, mask9 gs w i ∈ 0 :: 511 :: ws) → mask9 gs w (8 + k2) ∈ 0 :: 511 :: ws) :
    ∀ n ≤ gs.length, ∃ D : List ℕ,
      Der 511 W0 D ∧
      D.length + (if k1 < n then 1 else 0) + (if k2 < n then 1 else 0) ≤ n ∧
      (∀ i < 8 + n, mask9 gs w i ∈ 0 :: 511 :: (D.reverse ++ W0)) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨[], trivial, by simp, fun i hi => by simpa using hinit i hi⟩
  | succ n ih =>
    intro hle
    obtain ⟨D, hD, hlen, hcov⟩ := ih (by omega)
    have hn : n < gs.length := by omega
    have hok := hfan (gs[n]'hn) (List.getElem_mem hn)
    set ws := D.reverse ++ W0
    by_cases hmem : mask9 gs w (8 + n) ∈ 0 :: 511 :: ws
    · refine ⟨D, hD, ?_, ?_⟩
      · split_ifs at hlen ⊢ <;> omega
      · intro i hi
        by_cases hilt : i < 8 + n
        · exact hcov i hilt
        · have heq : i = 8 + n := by omega
          subst heq
          exact hmem
    · have hne1 : n ≠ k1 := fun e => hmem (by subst e; exact hsk1 hn ws hcov)
      have hne2 : n ≠ k2 := fun e => hmem (by subst e; exact hsk2 hn ws hcov)
      have hob : Ob 511 ws (mask9 gs w (8 + n)) :=
        (gate_ob_or_mem gs w hw n hn hok ws hcov).resolve_left hmem
      refine ⟨D ++ [mask9 gs w (8 + n)], Der_snoc 511 D W0 _ hD (.inr hob), ?_, ?_⟩
      · have h1 : (if k1 < n + 1 then 1 else 0) = if k1 < n then 1 else 0 := by
          split_ifs <;> omega
        have h2 : (if k2 < n + 1 then 1 else 0) = if k2 < n then 1 else 0 := by
          split_ifs <;> omega
        simp only [List.length_append, List.length_singleton, h1, h2]
        omega
      · intro i hi
        simp only [List.reverse_append, List.reverse_singleton, List.cons_append]
        by_cases hilt : i < 8 + n
        · rcases List.mem_cons.1 (hcov i hilt) with h0 | h1
          · exact h0 ▸ List.mem_cons_self
          · rcases List.mem_cons.1 h1 with h5 | hws
            · exact h5 ▸ List.mem_cons_of_mem _ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hws))
        · have heq : i = 8 + n := by omega
          subst heq
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

def InCone (C : Circuit) (v : ℕ) : Prop :=
  ∀ S : ℕ → Prop, S C.output →
    (∀ k (hk : k < C.gates.length) u, S (8 + k) → u ∈ effInputs (C.gates[k]'hk) → u < 8 + k → S u) →
    S v

theorem inCone_out (C : Circuit) : InCone C C.output := fun _ h _ => h

theorem inCone_step (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (u : ℕ)
    (hS : InCone C (8 + k)) (hu : u ∈ effInputs (C.gates[k]'hk)) (hlt : u < 8 + k) :
    InCone C u :=
  fun S hout hstep => hstep k hk u (hS S hout hstep) hu hlt

theorem inCone_cases (C : Circuit) (v : ℕ) (hv : InCone C v) :
    v = C.output ∨ ∃ k, ∃ hk : k < C.gates.length,
      InCone C (8 + k) ∧ v ∈ effInputs (C.gates[k]'hk) ∧ v < 8 + k := by
  apply hv (fun x => x = C.output ∨ ∃ k, ∃ hk : k < C.gates.length,
      InCone C (8 + k) ∧ x ∈ effInputs (C.gates[k]'hk) ∧ x < 8 + k) (Or.inl rfl)
  intro k hk u hSk hu hlt
  have hk_cone : InCone C (8 + k) := by
    rcases hSk with heq | ⟨k', hk', hc', hu', hlt'⟩
    · exact heq ▸ inCone_out C
    · exact inCone_step C k' hk' (8 + k) hc' hu' hlt'
  exact Or.inr ⟨k, hk, hk_cone, hu, hlt⟩

theorem eval_gate_eff (g : Gate) (f1 f2 : ℕ → Bool)
    (h : ∀ u ∈ effInputs g, f1 u = f2 u) :
    g.op.eval (g.inputs.map f1) = g.op.eval (g.inputs.map f2) := by
  cases hop : g.op with
  | not =>
    cases hins : g.inputs with
    | nil => rfl
    | cons a rest =>
      have ha : a ∈ effInputs g := by simp [effInputs, hop, hins]
      simp [GateOp.eval, h a ha]
  | and =>
    congr 1
    apply List.map_congr_left
    intro u hu
    exact h u (by simpa [effInputs, hop] using hu)
  | or =>
    congr 1
    apply List.map_congr_left
    intro u hu
    exact h u (by simpa [effInputs, hop] using hu)
  | mod m =>
    congr 1
    apply List.map_congr_left
    intro u hu
    exact h u (by simpa [effInputs, hop] using hu)
  | maj =>
    congr 1
    apply List.map_congr_left
    intro u hu
    exact h u (by simpa [effInputs, hop] using hu)

theorem wires_eq_of_inCone_agree (C : Circuit) (x y : List Bool)
    (hx : x.length = 8) (hy : y.length = 8)
    (h : ∀ i < 8, InCone C i → x.getD i false = y.getD i false) :
    ∀ v, InCone C v → (C.wires x).getD v false = (C.wires y).getD v false := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv
    by_cases hv8 : v < 8
    · change (wiresFrom C.gates x).getD v false = (wiresFrom C.gates y).getD v false
      rw [getD_wiresFrom C.gates x v (by omega), getD_wiresFrom C.gates y v (by omega)]
      exact h v hv8 hv
    · by_cases hvlen : v < 8 + C.gates.length
      · set k := v - 8
        have hk : k < C.gates.length := by omega
        have hveq : 8 + k = v := by omega
        change (wiresFrom C.gates x).getD v false = (wiresFrom C.gates y).getD v false
        rw [← hveq]
        have hx' := wiresFrom_getD_gate C.gates x k hk
        have hy' := wiresFrom_getD_gate C.gates y k hk
        rw [hx] at hx'
        rw [hy] at hy'
        rw [hx', hy']
        apply eval_gate_eff
        intro u hu
        by_cases hult : u < 8 + k
        · simp only [hult, ↓reduceIte]
          have huc : InCone C u := inCone_step C k hk u (hveq.symm ▸ hv) hu hult
          exact ih u (by omega) huc
        · simp only [hult, ↓reduceIte]
      · change (wiresFrom C.gates x).getD v false = (wiresFrom C.gates y).getD v false
        rw [wiresFrom_getD_ge C.gates x v (by omega), wiresFrom_getD_ge C.gates y v (by omega)]

theorem eval_eq_of_inCone_agree (C : Circuit) (x y : List Bool)
    (hx : x.length = 8) (hy : y.length = 8)
    (h : ∀ i < 8, InCone C i → x.getD i false = y.getD i false) :
    C.eval x = C.eval y :=
  wires_eq_of_inCone_agree C x y hx hy h C.output (inCone_out C)

def matOf (m : ℕ) (u v : Fin 4) : Bool := m.testBit (4 * u.val + v.val)

theorem oneEach_len (u v : Fin 4) : (oneEach u v).length = 8 := by
  simp [oneEach]

theorem oneEach_getD_row (u v : Fin 4) (i : ℕ) (hi : i < 4) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp [hi] : i < (List.ofFn (fun k : Fin 4 => decide (k = u))).length),
    List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
  exact decide_eq_decide.2 Fin.ext_iff

theorem oneEach_getD_col (u v : Fin 4) (j : ℕ) (hj : j < 4) :
    (oneEach u v).getD (4 + j) false = decide (j = v.val) := by
  have hlen : (List.ofFn (fun k : Fin 4 => decide (k = u))).length = 4 := by simp
  simp only [oneEach, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega : (List.ofFn (fun k : Fin 4 => decide (k = u))).length ≤ 4 + j),
    hlen, Nat.add_sub_cancel_left, List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
  exact decide_eq_decide.2 Fin.ext_iff

theorem exists_inCone_rows (m : ℕ)
    (hdist : ∀ u1 u2 : Fin 4, u1 ≠ u2 → ∃ v : Fin 4, matOf m u1 v ≠ matOf m u2 v)
    (C : Circuit) (hrep : Represents (matOf m) C) :
    ∃ rBad : Fin 4, ∀ r : Fin 4, r ≠ rBad → InCone C r.val := by
  classical
  by_cases hex : ∃ rBad : Fin 4, ¬ InCone C rBad.val
  · obtain ⟨rBad, hrBad⟩ := hex
    refine ⟨rBad, fun r hr => ?_⟩
    by_contra hnr
    obtain ⟨v, hv⟩ := hdist r rBad hr
    have hev : C.eval (oneEach r v) = C.eval (oneEach rBad v) := by
      apply eval_eq_of_inCone_agree C (oneEach r v) (oneEach rBad v) (oneEach_len r v) (oneEach_len rBad v)
      intro i hi hci
      by_cases hi4 : i < 4
      · rw [oneEach_getD_row r v i hi4, oneEach_getD_row rBad v i hi4]
        have h1 : i ≠ r.val := fun e => hnr (e ▸ hci)
        have h2 : i ≠ rBad.val := fun e => hrBad (e ▸ hci)
        simp [h1, h2]
      · have hj : i - 4 < 4 := by omega
        have hieq : i = 4 + (i - 4) := by omega
        rw [hieq, oneEach_getD_col r v (i - 4) hj, oneEach_getD_col rBad v (i - 4) hj]
    rw [hrep r v, hrep rBad v] at hev
    exact hv hev
  · refine ⟨0, fun r _ => ?_⟩
    by_contra hnr
    exact hex ⟨r, hnr⟩

theorem exists_inCone_cols (m : ℕ)
    (hdist : ∀ v1 v2 : Fin 4, v1 ≠ v2 → ∃ u : Fin 4, matOf m u v1 ≠ matOf m u v2)
    (C : Circuit) (hrep : Represents (matOf m) C) :
    ∃ cBad : Fin 4, ∀ c : Fin 4, c ≠ cBad → InCone C (4 + c.val) := by
  classical
  by_cases hex : ∃ cBad : Fin 4, ¬ InCone C (4 + cBad.val)
  · obtain ⟨cBad, hcBad⟩ := hex
    refine ⟨cBad, fun c hc => ?_⟩
    by_contra hnc
    obtain ⟨u, hu⟩ := hdist c cBad hc
    have hev : C.eval (oneEach u c) = C.eval (oneEach u cBad) := by
      apply eval_eq_of_inCone_agree C (oneEach u c) (oneEach u cBad) (oneEach_len u c) (oneEach_len u cBad)
      intro i hi hci
      by_cases hi4 : i < 4
      · rw [oneEach_getD_row u c i hi4, oneEach_getD_row u cBad i hi4]
      · have hj : i - 4 < 4 := by omega
        have hieq : i = 4 + (i - 4) := by omega
        rw [hieq, oneEach_getD_col u c (i - 4) hj, oneEach_getD_col u cBad (i - 4) hj]
        have h1 : i - 4 ≠ c.val := fun e => hnc (by rw [← e, ← hieq]; exact hci)
        have h2 : i - 4 ≠ cBad.val := fun e => hcBad (by rw [← e, ← hieq]; exact hci)
        simp [h1, h2]
    rw [hrep u c, hrep u cBad] at hev
    exact hu hev
  · refine ⟨0, fun c _ => ?_⟩
    by_contra hnc
    exact hex ⟨c, hnc⟩

set_option maxHeartbeats 0 in
def layouts3BT : BT (BT (Fin 3 × Fin 3) 4 × BT ℕ 3) 7 :=
  (((((((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (1, 0)), ((2, 0), (0, 1))), (((1, 1), (2, 1)), ((0, 2), (1, 2)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 146), (292, 7)), ((56, 448), (0, 0))))), (((((((0, 0), (0, 2)), ((0, 1), (1, 0))), (((1, 2), (1, 1)), ((2, 0), (2, 2)))), ((((2, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((292, 146), (0, 0)))), ((((((0, 0), (1, 0)), ((2, 0), (0, 2))), (((1, 2), (2, 2)), ((0, 1), (1, 1)))), ((((2, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 146), (292, 7)), ((448, 56), (0, 0)))))), ((((((((0, 1), (0, 0)), ((0, 2), (1, 1))), (((1, 0), (1, 2)), ((2, 1), (2, 0)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 146)), ((73, 292), (0, 0)))), ((((((0, 1), (1, 1)), ((2, 1), (0, 0))), (((1, 0), (2, 0)), ((0, 2), (1, 2)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 146), (292, 56)), ((7, 448), (0, 0))))), (((((((0, 1), (0, 2)), ((0, 0), (1, 1))), (((1, 2), (1, 0)), ((2, 1), (2, 2)))), ((((2, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 292)), ((73, 146), (0, 0)))), ((((((0, 1), (1, 1)), ((2, 1), (0, 2))), (((1, 2), (2, 2)), ((0, 0), (1, 0)))), ((((2, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 146), (292, 448)), ((7, 56), (0, 0))))))), (((((((((0, 2), (0, 0)), ((0, 1), (1, 2))), (((1, 0), (1, 1)), ((2, 2), (2, 0)))), ((((2, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 146)), ((292, 73), (0, 0)))), ((((((0, 2), (1, 2)), ((2, 2), (0, 0))), (((1, 0), (2, 0)), ((0, 1), (1, 1)))), ((((2, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 146), (292, 56)), ((448, 7), (0, 0))))), (((((((0, 2), (0, 1)), ((0, 0), (1, 2))), (((1, 1), (1, 0)), ((2, 2), (2, 1)))), ((((2, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 292)), ((146, 73), (0, 0)))), ((((((0, 2), (1, 2)), ((2, 2), (0, 1))), (((1, 1), (2, 1)), ((0, 0), (1, 0)))), ((((2, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 146), (292, 448)), ((56, 7), (0, 0)))))), ((((((((0, 0), (0, 1)), ((0, 2), (2, 0))), (((2, 1), (2, 2)), ((1, 0), (1, 1)))), ((((1, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 448), (56, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (2, 0)), ((1, 0), (0, 1))), (((2, 1), (1, 1)), ((0, 2), (2, 2)))), ((((1, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 292), (146, 7)), ((56, 448), (0, 0))))), (((((((0, 0), (0, 2)), ((0, 1), (2, 0))), (((2, 2), (2, 1)), ((1, 0), (1, 2)))), ((((1, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 448), (56, 73)), ((292, 146), (0, 0)))), ((((((0, 0), (2, 0)), ((1, 0), (0, 2))), (((2, 2), (1, 2)), ((0, 1), (2, 1)))), ((((1, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 292), (146, 7)), ((448, 56), (0, 0)))))))), ((((((((((0, 1), (0, 0)), ((0, 2), (2, 1))), (((2, 0), (2, 2)), ((1, 1), (1, 0)))), ((((1, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 448), (56, 146)), ((73, 292), (0, 0)))), ((((((0, 1), (2, 1)), ((1, 1), (0, 0))), (((2, 0), (1, 0)), ((0, 2), (2, 2)))), ((((1, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 292), (146, 56)), ((7, 448), (0, 0))))), (((((((0, 1), (0, 2)), ((0, 0), (2, 1))), (((2, 2), (2, 0)), ((1, 1), (1, 2)))), ((((1, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 448), (56, 292)), ((73, 146), (0, 0)))), ((((((0, 1), (2, 1)), ((1, 1), (0, 2))), (((2, 2), (1, 2)), ((0, 0), (2, 0)))), ((((1, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 292), (146, 448)), ((7, 56), (0, 0)))))), ((((((((0, 2), (0, 0)), ((0, 1), (2, 2))), (((2, 0), (2, 1)), ((1, 2), (1, 0)))), ((((1, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 448), (56, 146)), ((292, 73), (0, 0)))), ((((((0, 2), (2, 2)), ((1, 2), (0, 0))), (((2, 0), (1, 0)), ((0, 1), (2, 1)))), ((((1, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 292), (146, 56)), ((448, 7), (0, 0))))), (((((((0, 2), (0, 1)), ((0, 0), (2, 2))), (((2, 1), (2, 0)), ((1, 2), (1, 1)))), ((((1, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 448), (56, 292)), ((146, 73), (0, 0)))), ((((((0, 2), (2, 2)), ((1, 2), (0, 1))), (((2, 1), (1, 1)), ((0, 0), (2, 0)))), ((((1, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((73, 292), (146, 448)), ((56, 7), (0, 0))))))), (((((((((1, 0), (1, 1)), ((1, 2), (0, 0))), (((0, 1), (0, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 7), (448, 73)), ((146, 292), (0, 0)))), ((((((1, 0), (0, 0)), ((2, 0), (1, 1))), (((0, 1), (2, 1)), ((1, 2), (0, 2)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 73), (292, 7)), ((56, 448), (0, 0))))), (((((((1, 0), (1, 2)), ((1, 1), (0, 0))), (((0, 2), (0, 1)), ((2, 0), (2, 2)))), ((((2, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 7), (448, 73)), ((292, 146), (0, 0)))), ((((((1, 0), (0, 0)), ((2, 0), (1, 2))), (((0, 2), (2, 2)), ((1, 1), (0, 1)))), ((((2, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 73), (292, 7)), ((448, 56), (0, 0)))))), ((((((((1, 1), (1, 0)), ((1, 2), (0, 1))), (((0, 0), (0, 2)), ((2, 1), (2, 0)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 7), (448, 146)), ((73, 292), (0, 0)))), ((((((1, 1), (0, 1)), ((2, 1), (1, 0))), (((0, 0), (2, 0)), ((1, 2), (0, 2)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 73), (292, 56)), ((7, 448), (0, 0))))), (((((((1, 1), (1, 2)), ((1, 0), (0, 1))), (((0, 2), (0, 0)), ((2, 1), (2, 2)))), ((((2, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 7), (448, 292)), ((73, 146), (0, 0)))), ((((((1, 1), (0, 1)), ((2, 1), (1, 2))), (((0, 2), (2, 2)), ((1, 0), (0, 0)))), ((((2, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 73), (292, 448)), ((7, 56), (0, 0))))))))), (((((((((((1, 2), (1, 0)), ((1, 1), (0, 2))), (((0, 0), (0, 1)), ((2, 2), (2, 0)))), ((((2, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 7), (448, 146)), ((292, 73), (0, 0)))), ((((((1, 2), (0, 2)), ((2, 2), (1, 0))), (((0, 0), (2, 0)), ((1, 1), (0, 1)))), ((((2, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 73), (292, 56)), ((448, 7), (0, 0))))), (((((((1, 2), (1, 1)), ((1, 0), (0, 2))), (((0, 1), (0, 0)), ((2, 2), (2, 1)))), ((((2, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 7), (448, 292)), ((146, 73), (0, 0)))), ((((((1, 2), (0, 2)), ((2, 2), (1, 1))), (((0, 1), (2, 1)), ((1, 0), (0, 0)))), ((((2, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 73), (292, 448)), ((56, 7), (0, 0)))))), ((((((((1, 0), (1, 1)), ((1, 2), (2, 0))), (((2, 1), (2, 2)), ((0, 0), (0, 1)))), ((((0, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 7), (56, 73)), ((146, 292), (0, 0)))), ((((((1, 0), (2, 0)), ((0, 0), (1, 1))), (((2, 1), (0, 1)), ((1, 2), (2, 2)))), ((((0, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 73), (146, 7)), ((56, 448), (0, 0))))), (((((((1, 0), (1, 2)), ((1, 1), (2, 0))), (((2, 2), (2, 1)), ((0, 0), (0, 2)))), ((((0, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 7), (56, 73)), ((292, 146), (0, 0)))), ((((((1, 0), (2, 0)), ((0, 0), (1, 2))), (((2, 2), (0, 2)), ((1, 1), (2, 1)))), ((((0, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 73), (146, 7)), ((448, 56), (0, 0))))))), (((((((((1, 1), (1, 0)), ((1, 2), (2, 1))), (((2, 0), (2, 2)), ((0, 1), (0, 0)))), ((((0, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 7), (56, 146)), ((73, 292), (0, 0)))), ((((((1, 1), (2, 1)), ((0, 1), (1, 0))), (((2, 0), (0, 0)), ((1, 2), (2, 2)))), ((((0, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 73), (146, 56)), ((7, 448), (0, 0))))), (((((((1, 1), (1, 2)), ((1, 0), (2, 1))), (((2, 2), (2, 0)), ((0, 1), (0, 2)))), ((((0, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 7), (56, 292)), ((73, 146), (0, 0)))), ((((((1, 1), (2, 1)), ((0, 1), (1, 2))), (((2, 2), (0, 2)), ((1, 0), (2, 0)))), ((((0, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 73), (146, 448)), ((7, 56), (0, 0)))))), ((((((((1, 2), (1, 0)), ((1, 1), (2, 2))), (((2, 0), (2, 1)), ((0, 2), (0, 0)))), ((((0, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 7), (56, 146)), ((292, 73), (0, 0)))), ((((((1, 2), (2, 2)), ((0, 2), (1, 0))), (((2, 0), (0, 0)), ((1, 1), (2, 1)))), ((((0, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 73), (146, 56)), ((448, 7), (0, 0))))), (((((((1, 2), (1, 1)), ((1, 0), (2, 2))), (((2, 1), (2, 0)), ((0, 2), (0, 1)))), ((((0, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 7), (56, 292)), ((146, 73), (0, 0)))), ((((((1, 2), (2, 2)), ((0, 2), (1, 1))), (((2, 1), (0, 1)), ((1, 0), (2, 0)))), ((((0, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 73), (146, 448)), ((56, 7), (0, 0)))))))), ((((((((((2, 0), (2, 1)), ((2, 2), (0, 0))), (((0, 1), (0, 2)), ((1, 0), (1, 1)))), ((((1, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 448), (7, 73)), ((146, 292), (0, 0)))), ((((((2, 0), (0, 0)), ((1, 0), (2, 1))), (((0, 1), (1, 1)), ((2, 2), (0, 2)))), ((((1, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 292), (73, 7)), ((56, 448), (0, 0))))), (((((((2, 0), (2, 2)), ((2, 1), (0, 0))), (((0, 2), (0, 1)), ((1, 0), (1, 2)))), ((((1, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 448), (7, 73)), ((292, 146), (0, 0)))), ((((((2, 0), (0, 0)), ((1, 0), (2, 2))), (((0, 2), (1, 2)), ((2, 1), (0, 1)))), ((((1, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 292), (73, 7)), ((448, 56), (0, 0)))))), ((((((((2, 1), (2, 0)), ((2, 2), (0, 1))), (((0, 0), (0, 2)), ((1, 1), (1, 0)))), ((((1, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 448), (7, 146)), ((73, 292), (0, 0)))), ((((((2, 1), (0, 1)), ((1, 1), (2, 0))), (((0, 0), (1, 0)), ((2, 2), (0, 2)))), ((((1, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 292), (73, 56)), ((7, 448), (0, 0))))), (((((((2, 1), (2, 2)), ((2, 0), (0, 1))), (((0, 2), (0, 0)), ((1, 1), (1, 2)))), ((((1, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 448), (7, 292)), ((73, 146), (0, 0)))), ((((((2, 1), (0, 1)), ((1, 1), (2, 2))), (((0, 2), (1, 2)), ((2, 0), (0, 0)))), ((((1, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 292), (73, 448)), ((7, 56), (0, 0))))))), (((((((((2, 2), (2, 0)), ((2, 1), (0, 2))), (((0, 0), (0, 1)), ((1, 2), (1, 0)))), ((((1, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 448), (7, 146)), ((292, 73), (0, 0)))), ((((((2, 2), (0, 2)), ((1, 2), (2, 0))), (((0, 0), (1, 0)), ((2, 1), (0, 1)))), ((((1, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 292), (73, 56)), ((448, 7), (0, 0))))), (((((((2, 2), (2, 1)), ((2, 0), (0, 2))), (((0, 1), (0, 0)), ((1, 2), (1, 1)))), ((((1, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((56, 448), (7, 292)), ((146, 73), (0, 0)))), ((((((2, 2), (0, 2)), ((1, 2), (2, 1))), (((0, 1), (1, 1)), ((2, 0), (0, 0)))), ((((1, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((146, 292), (73, 448)), ((56, 7), (0, 0)))))), ((((((((2, 0), (2, 1)), ((2, 2), (1, 0))), (((1, 1), (1, 2)), ((0, 0), (0, 1)))), ((((0, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 56), (7, 73)), ((146, 292), (0, 0)))), ((((((2, 0), (1, 0)), ((0, 0), (2, 1))), (((1, 1), (0, 1)), ((2, 2), (1, 2)))), ((((0, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 146), (73, 7)), ((56, 448), (0, 0))))), (((((((2, 0), (2, 2)), ((2, 1), (1, 0))), (((1, 2), (1, 1)), ((0, 0), (0, 2)))), ((((0, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 56), (7, 73)), ((292, 146), (0, 0)))), ((((((2, 0), (1, 0)), ((0, 0), (2, 2))), (((1, 2), (0, 2)), ((2, 1), (1, 1)))), ((((0, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 146), (73, 7)), ((448, 56), (0, 0)))))))))), ((((((((((((2, 1), (2, 0)), ((2, 2), (1, 1))), (((1, 0), (1, 2)), ((0, 1), (0, 0)))), ((((0, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 56), (7, 146)), ((73, 292), (0, 0)))), ((((((2, 1), (1, 1)), ((0, 1), (2, 0))), (((1, 0), (0, 0)), ((2, 2), (1, 2)))), ((((0, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 146), (73, 56)), ((7, 448), (0, 0))))), (((((((2, 1), (2, 2)), ((2, 0), (1, 1))), (((1, 2), (1, 0)), ((0, 1), (0, 2)))), ((((0, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 56), (7, 292)), ((73, 146), (0, 0)))), ((((((2, 1), (1, 1)), ((0, 1), (2, 2))), (((1, 2), (0, 2)), ((2, 0), (1, 0)))), ((((0, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 146), (73, 448)), ((7, 56), (0, 0)))))), ((((((((2, 2), (2, 0)), ((2, 1), (1, 2))), (((1, 0), (1, 1)), ((0, 2), (0, 0)))), ((((0, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 56), (7, 146)), ((292, 73), (0, 0)))), ((((((2, 2), (1, 2)), ((0, 2), (2, 0))), (((1, 0), (0, 0)), ((2, 1), (1, 1)))), ((((0, 1), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 146), (73, 56)), ((448, 7), (0, 0))))), (((((((2, 2), (2, 1)), ((2, 0), (1, 2))), (((1, 1), (1, 0)), ((0, 2), (0, 1)))), ((((0, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((448, 56), (7, 292)), ((146, 73), (0, 0)))), ((((((2, 2), (1, 2)), ((0, 2), (2, 1))), (((1, 1), (0, 1)), ((2, 0), (1, 0)))), ((((0, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((292, 146), (73, 448)), ((56, 7), (0, 0))))))), (((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))))), ((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))))))), ((((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))))), ((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))))), (((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))))), ((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))))))), (((((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))))), ((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))))), (((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))))), ((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))))))), ((((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))))), ((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))))), (((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))))), ((((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0))))), (((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))), ((((((0, 0), (0, 1)), ((0, 2), (1, 0))), (((1, 1), (1, 2)), ((2, 0), (2, 1)))), ((((2, 2), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))), (((7, 56), (448, 73)), ((146, 292), (0, 0)))))))))))

def site3 (l : ℕ) (j : ℕ) : Fin 3 × Fin 3 := btGet (btGet layouts3BT l).1 j
def mask3 (l : ℕ) (i : ℕ) : ℕ := btGet (btGet layouts3BT l).2 i

def subSite (rdel cdel : Fin 4) (l : ℕ) (j : ℕ) : Fin 4 × Fin 4 :=
  (rdel.succAbove (site3 l j).1, cdel.succAbove (site3 l j).2)

def subInput (rdel cdel : Fin 4) (l : ℕ) (j : ℕ) : List Bool :=
  oneEach (subSite rdel cdel l j).1 (subSite rdel cdel l j).2

def checkLayout3 (entry : BT (Fin 3 × Fin 3) 4 × BT ℕ 3) : Bool :=
  (List.range 6).all fun i =>
    let mv := btGet entry.2 i
    W0.contains mv &&
    (List.range 9).all fun j =>
      let s := btGet entry.1 j
      (if i < 3 then decide (i = s.1.val) else decide (i - 3 = s.2.val)) == mv.testBit j

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem layouts3_ok : btAll checkLayout3 layouts3BT = true := by decide +kernel

theorem layout3_pins (l : ℕ) (i : ℕ) (hi : i < 6) :
    mask3 l i ∈ W0 ∧
    ∀ j < 9,
      (if i < 3 then decide (i = (site3 l j).1.val)
       else decide (i - 3 = (site3 l j).2.val)) =
      (mask3 l i).testBit j := by
  have h1 := btAll_get checkLayout3 layouts3BT l layouts3_ok
  have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true] at h2
  refine ⟨List.contains_iff_mem.1 h2.1, fun j hj => ?_⟩
  have h3 := List.all_eq_true.1 h2.2 j (List.mem_range.2 hj)
  exact beq_iff_eq.1 h3

theorem subInput_init (C : Circuit) (rdel cdel : Fin 4) (l : ℕ) :
    (∀ i < 8, mask9 C.gates (subInput rdel cdel l) i ∈ 0 :: 511 :: W0) ∧
    mask9 C.gates (subInput rdel cdel l) rdel.val = 0 ∧
    mask9 C.gates (subInput rdel cdel l) (4 + cdel.val) = 0 := by
  have hwlen : ∀ r, (subInput rdel cdel l r).length = 8 := fun r => oneEach_len _ _
  have hbit : ∀ i < 8, ∀ r < 9, (mask9 C.gates (subInput rdel cdel l) i).testBit r =
      (subInput rdel cdel l r).getD i false := by
    intro i hi r hr
    rw [mask9_testBit C.gates (subInput rdel cdel l) i r hr,
        getD_wiresFrom C.gates (subInput rdel cdel l r) i (by rw [hwlen r]; exact hi)]
  have hzero_r : mask9 C.gates (subInput rdel cdel l) rdel.val = 0 := by
    apply eq_of_bits_lt512 _ _ (mask9_lt _ _ _) (by decide)
    intro r hr
    rw [hbit rdel.val (by omega) r hr, subInput, subSite, oneEach_getD_row _ _ rdel.val rdel.isLt, Nat.zero_testBit]
    have hne : rdel.val ≠ (rdel.succAbove (site3 l r).1).val := by
      intro heq
      exact (Fin.succAbove_ne rdel (site3 l r).1) (Fin.ext heq.symm)
    simp [hne]
  have hzero_c : mask9 C.gates (subInput rdel cdel l) (4 + cdel.val) = 0 := by
    apply eq_of_bits_lt512 _ _ (mask9_lt _ _ _) (by decide)
    intro r hr
    rw [hbit (4 + cdel.val) (by omega) r hr, subInput, subSite, oneEach_getD_col _ _ cdel.val cdel.isLt, Nat.zero_testBit]
    have hne : cdel.val ≠ (cdel.succAbove (site3 l r).2).val := by
      intro heq
      exact (Fin.succAbove_ne cdel (site3 l r).2) (Fin.ext heq.symm)
    simp [hne]
  have hW0_lt : ∀ x ∈ W0, x < 512 := by decide
  refine ⟨fun i hi => ?_, hzero_r, hzero_c⟩
  by_cases hi4 : i < 4
  · let fi : Fin 4 := ⟨i, hi4⟩
    by_cases heq : fi = rdel
    · have : i = rdel.val := congrArg Fin.val heq
      rw [this, hzero_r]
      exact List.mem_cons_self
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq heq
      have hklt : k.val < 3 := k.isLt
      have hpin := layout3_pins l k.val (by omega)
      have hmeq : mask9 C.gates (subInput rdel cdel l) i = mask3 l k.val := by
        apply eq_of_bits_lt512 _ _ (mask9_lt _ _ _) (hW0_lt _ hpin.1)
        intro r hr
        rw [hbit i hi r hr, subInput, subSite, oneEach_getD_row _ _ i hi4]
        have hp := hpin.2 r hr
        simp only [hklt, ↓reduceIte] at hp
        rw [← hp]
        apply decide_eq_decide.2
        have hfi : i = (rdel.succAbove k).val := by rw [hk]
        rw [hfi]
        constructor
        · intro h; exact congrArg Fin.val (Fin.succAbove_right_injective (Fin.ext h))
        · intro h; exact congrArg (fun x => (rdel.succAbove x).val) (Fin.ext h)
      rw [hmeq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hpin.1)
  · let fj : Fin 4 := ⟨i - 4, by omega⟩
    have hieq : i = 4 + fj.val := by dsimp [fj]; omega
    by_cases heq : fj = cdel
    · have : i = 4 + cdel.val := by rw [hieq, heq]
      rw [this, hzero_c]
      exact List.mem_cons_self
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq heq
      have hklt : k.val < 3 := k.isLt
      have hpin := layout3_pins l (3 + k.val) (by omega)
      have hmeq : mask9 C.gates (subInput rdel cdel l) i = mask3 l (3 + k.val) := by
        apply eq_of_bits_lt512 _ _ (mask9_lt _ _ _) (hW0_lt _ hpin.1)
        intro r hr
        rw [hbit i hi r hr, hieq, subInput, subSite, oneEach_getD_col _ _ fj.val fj.isLt]
        have hp := hpin.2 r hr
        have hnot : ¬ 3 + k.val < 3 := by omega
        have hsub : 3 + k.val - 3 = k.val := by omega
        simp only [hnot, ↓reduceIte, hsub] at hp
        rw [← hp]
        apply decide_eq_decide.2
        have hfj : fj.val = (cdel.succAbove k).val := by rw [hk]
        rw [hfj]
        constructor
        · intro h; exact congrArg Fin.val (Fin.succAbove_right_injective (Fin.ext h))
        · intro h; exact congrArg (fun x => (cdel.succAbove x).val) (Fin.ext h)
      rw [hmeq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hpin.1)

def subMask3 (m : ℕ) (rdel cdel : Fin 4) (l : ℕ) : ℕ :=
  (List.range 9).foldr (fun j acc =>
    let p := subSite rdel cdel l j
    if matOf m p.1 p.2 then acc ||| 2 ^ j else acc) 0

theorem subMask3_lt (m : ℕ) (rdel cdel : Fin 4) (l : ℕ) : subMask3 m rdel cdel l < 512 := by
  have haux : ∀ (L : List ℕ), (∀ j ∈ L, j < 9) →
      L.foldr (fun j acc => let p := subSite rdel cdel l j; if matOf m p.1 p.2 then acc ||| 2 ^ j else acc) 0 < 512 := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons a L ih =>
      intro hL
      have ha : a < 9 := hL a List.mem_cons_self
      have hpow : 2 ^ a < 512 := Nat.pow_lt_pow_right (by decide) ha
      have hrest := ih (fun j hj => hL j (List.mem_cons_of_mem _ hj))
      simp only [List.foldr_cons]
      split_ifs
      · exact Nat.or_lt_two_pow (n := 9) hrest hpow
      · exact hrest
  exact haux (List.range 9) (fun j hj => List.mem_range.1 hj)

theorem subMask3_testBit (m : ℕ) (rdel cdel : Fin 4) (l : ℕ) (r : ℕ) (hr : r < 9) :
    (subMask3 m rdel cdel l).testBit r = matOf m (subSite rdel cdel l r).1 (subSite rdel cdel l r).2 := by
  have haux : ∀ (L : List ℕ), L.Nodup →
      (L.foldr (fun j acc => let p := subSite rdel cdel l j; if matOf m p.1 p.2 then acc ||| 2 ^ j else acc) 0).testBit r =
      if r ∈ L then matOf m (subSite rdel cdel l r).1 (subSite rdel cdel l r).2 else false := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons a L ih =>
      intro hnd
      obtain ⟨han, hndL⟩ := List.nodup_cons.1 hnd
      simp only [List.foldr_cons]
      by_cases hra : r = a
      · subst hra
        simp only [List.mem_cons_self, ↓reduceIte]
        cases hb : matOf m (subSite rdel cdel l r).1 (subSite rdel cdel l r).2
        · simp [ih hndL, han]
        · simp [Nat.testBit_or]
      · have hne : a ≠ r := fun e => hra e.symm
        simp only [List.mem_cons, hra, false_or]
        cases hb : matOf m (subSite rdel cdel l a).1 (subSite rdel cdel l a).2
        · simp [ih hndL]
        · simp [Nat.testBit_or, ih hndL, hne]
  have h := haux (List.range 9) List.nodup_range
  simp only [List.mem_range.2 hr, ↓reduceIte] at h
  exact h

theorem mask9_out_eq (m : ℕ) (C : Circuit) (hrep : Represents (matOf m) C)
    (rdel cdel : Fin 4) (l : ℕ) :
    mask9 C.gates (subInput rdel cdel l) C.output = subMask3 m rdel cdel l := by
  apply eq_of_bits_lt512 _ _ (mask9_lt _ _ _) (subMask3_lt _ _ _ _)
  intro r hr
  rw [mask9_testBit C.gates _ C.output r hr, subMask3_testBit m rdel cdel l r hr]
  exact hrep (subSite rdel cdel l r).1 (subSite rdel cdel l r).2

theorem level1_contra (m : ℕ) (C : Circuit) (hfan : FanInTwo C) (hrep : Represents (matOf m) C)
    (rdel cdel : Fin 4) (l : ℕ) (goal cap : ℕ)
    (hsub : subMask3 m rdel cdel l = goal)
    (hg511 : goal ≠ 511) (hforb : Forbidden goal cap) (hsize : C.size ≤ cap) : False := by
  set w := subInput rdel cdel l
  have hwlen : ∀ r < 9, (w r).length = 8 := fun r _ => oneEach_len _ _
  have hinit := (subInput_init C rdel cdel l).1
  obtain ⟨D, hD, hDlen, hcov⟩ := buildDer_aux C.gates w hwlen hfan hinit C.gates.length (C.gates.length + 1)
    (by omega) (fun hk => by omega) (fun hk => by omega) C.gates.length (le_refl _)
  have hlen : D.length ≤ cap := by
    have hcs : C.gates.length ≤ cap := hsize
    split_ifs at hDlen <;> omega
  have hout_eq : mask9 C.gates w C.output = goal := (mask9_out_eq m C hrep rdel cdel l).trans hsub
  have hout_mem : goal ∈ 0 :: 511 :: (D.reverse ++ W0) := by
    rw [← hout_eq]
    by_cases ho : C.output < 8 + C.gates.length
    · exact hcov C.output ho
    · rw [mask9_ge C.gates w hwlen C.output (by omega)]
      exact List.mem_cons_self
  have hno := hforb D hD hlen
  rcases List.mem_cons.1 hout_mem with h0 | h1
  · exact hno.1 (h0 ▸ List.mem_cons_self)
  · rcases List.mem_cons.1 h1 with h511 | h2
    · exact hg511 h511
    · rcases List.mem_append.1 h2 with hDmem | hWmem
      · exact hno.2 (List.mem_reverse.1 hDmem)
      · exact hno.1 (List.mem_cons_of_mem _ hWmem)

theorem level2_contra (m : ℕ) (C : Circuit) (hfan : FanInTwo C) (hrep : Represents (matOf m) C)
    (rdel cdel : Fin 4) (hr : InCone C rdel.val) (hc : InCone C (4 + cdel.val))
    (l : ℕ) (goal cap : ℕ)
    (hsub : subMask3 m rdel cdel l = goal)
    (hg0 : goal ≠ 0) (hg511 : goal ≠ 511) (hforb : Forbidden goal cap) (hsize : C.size ≤ cap + 2) : False := by
  set w := subInput rdel cdel l
  have hwlen : ∀ r < 9, (w r).length = 8 := fun r _ => oneEach_len _ _
  obtain ⟨hinit, hzr, hzc⟩ := subInput_init C rdel cdel l
  change mask9 C.gates w rdel.val = 0 at hzr
  change mask9 C.gates w (4 + cdel.val) = 0 at hzc
  have hout_eq : mask9 C.gates w C.output = goal := (mask9_out_eq m C hrep rdel cdel l).trans hsub
  have hr_ne_out : rdel.val ≠ C.output := fun e => hg0 (by rw [← hout_eq, ← e, hzr])
  have hc_ne_out : 4 + cdel.val ≠ C.output := fun e => hg0 (by rw [← hout_eq, ← e, hzc])
  obtain ⟨k1, hk1, hk1c, hru1, hrlt1⟩ := (inCone_cases C rdel.val hr).resolve_left hr_ne_out
  obtain ⟨k2, hk2, hk2c, hcu2, hclt2⟩ := (inCone_cases C (4 + cdel.val) hc).resolve_left hc_ne_out
  have hex_pair : ∃ (ka : ℕ) (hka : ka < C.gates.length) (kb : ℕ) (hkb : kb < C.gates.length), ka ≠ kb ∧
      (∃ a ∈ effInputs (C.gates[ka]'hka), a < 8 + ka ∧ mask9 C.gates w a = 0) ∧
      (∃ b ∈ effInputs (C.gates[kb]'hkb), b < 8 + kb ∧ mask9 C.gates w b = 0) := by
    by_cases h12 : k1 = k2
    · subst h12
      have hok1 := hfan (C.gates[k1]'hk1) (List.getElem_mem hk1)
      have hmask_k1 : mask9 C.gates w (8 + k1) = 0 := by
        have hg := mask9_gate C.gates w hwlen k1 hk1
        obtain ⟨hopm, hlen⟩ := hok1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hopm
        have hrc_ne : rdel.val ≠ 4 + cdel.val := by omega
        rcases hopm with hop | hop | hop
        · rw [hop] at hg
          have hru' : rdel.val ∈ (C.gates[k1]'hk1).inputs := by simpa [effInputs, hop] using hru1
          have hcu' : 4 + cdel.val ∈ (C.gates[k1]'hk1).inputs := by simpa [effInputs, hop] using hcu2
          rcases hins : (C.gates[k1]'hk1).inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z, ls⟩⟩⟩
          · rw [hins] at hru'; simp at hru'
          · rw [hins] at hru' hcu'; simp at hru' hcu'; exact absurd (hru'.trans hcu'.symm) hrc_ne
          · rw [hins] at hg hru' hcu'; dsimp only at hg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hru' hcu'
            rcases hru' with rfl | rfl <;> rcases hcu' with he | he
            · exact absurd he.symm hrc_ne
            · subst he; simp only [hrlt1, hclt2, ↓reduceIte, hzr, hzc] at hg; simpa using hg
            · subst he; simp only [hrlt1, hclt2, ↓reduceIte, hzr, hzc] at hg; simpa using hg
            · exact absurd he.symm hrc_ne
          · rw [hins] at hlen; simp at hlen
        · rw [hop] at hg
          have hru' : rdel.val ∈ (C.gates[k1]'hk1).inputs := by simpa [effInputs, hop] using hru1
          have hcu' : 4 + cdel.val ∈ (C.gates[k1]'hk1).inputs := by simpa [effInputs, hop] using hcu2
          rcases hins : (C.gates[k1]'hk1).inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z, ls⟩⟩⟩
          · rw [hins] at hru'; simp at hru'
          · rw [hins] at hru' hcu'; simp at hru' hcu'; exact absurd (hru'.trans hcu'.symm) hrc_ne
          · rw [hins] at hg hru' hcu'; dsimp only at hg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hru' hcu'
            rcases hru' with rfl | rfl <;> rcases hcu' with he | he
            · exact absurd he.symm hrc_ne
            · subst he; simp only [hrlt1, hclt2, ↓reduceIte, hzr, hzc] at hg; simpa using hg
            · subst he; simp only [hrlt1, hclt2, ↓reduceIte, hzr, hzc] at hg; simpa using hg
            · exact absurd he.symm hrc_ne
          · rw [hins] at hlen; simp at hlen
        · have hru' : rdel.val ∈ (C.gates[k1]'hk1).inputs.take 1 := by simpa [effInputs, hop] using hru1
          have hcu' : 4 + cdel.val ∈ (C.gates[k1]'hk1).inputs.take 1 := by simpa [effInputs, hop] using hcu2
          rcases hins : (C.gates[k1]'hk1).inputs with _ | ⟨x, rest⟩
          · rw [hins] at hru'; simp at hru'
          · rw [hins] at hru' hcu'
            simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hru' hcu'
            exact absurd (hru'.trans hcu'.symm) hrc_ne
      have hk1_ne_out : 8 + k1 ≠ C.output := fun e => hg0 (by rw [← hout_eq, ← e, hmask_k1])
      obtain ⟨k3, hk3, _, h3u, h3lt⟩ := (inCone_cases C (8 + k1) hk1c).resolve_left hk1_ne_out
      exact ⟨k1, hk1, k3, hk3, by omega, ⟨rdel.val, hru1, hrlt1, hzr⟩, ⟨8 + k1, h3u, h3lt, hmask_k1⟩⟩
    · exact ⟨k1, hk1, k2, hk2, h12, ⟨rdel.val, hru1, hrlt1, hzr⟩, ⟨4 + cdel.val, hcu2, hclt2, hzc⟩⟩
  obtain ⟨ka, hka, kb, hkb, hne, ⟨a, ha, halt, ha0⟩, ⟨b, hb, hblt, hb0⟩⟩ := hex_pair
  obtain ⟨D, hD, hDlen, hcov⟩ := buildDer_aux C.gates w hwlen hfan hinit ka kb hne
    (fun hk ws hws => gate_skip_of_zero C.gates w hwlen ka hk (hfan _ (List.getElem_mem hk)) ws hws a ha halt ha0)
    (fun hk ws hws => gate_skip_of_zero C.gates w hwlen kb hk (hfan _ (List.getElem_mem hk)) ws hws b hb hblt hb0)
    C.gates.length (le_refl _)
  have hlen : D.length ≤ cap := by
    have hcs : C.gates.length ≤ cap + 2 := hsize
    simp only [hka, hkb, ↓reduceIte] at hDlen
    omega
  have hout_mem : goal ∈ 0 :: 511 :: (D.reverse ++ W0) := by
    rw [← hout_eq]
    by_cases ho : C.output < 8 + C.gates.length
    · exact hcov C.output ho
    · rw [mask9_ge C.gates w hwlen C.output (by omega)]
      exact List.mem_cons_self
  have hno := hforb D hD hlen
  rcases List.mem_cons.1 hout_mem with h0 | h1
  · exact hg0 h0
  · rcases List.mem_cons.1 h1 with h511 | h2
    · exact hg511 h511
    · rcases List.mem_append.1 h2 with hDmem | hWmem
      · exact hno.2 (List.mem_reverse.1 hDmem)
      · exact hno.1 (List.mem_cons_of_mem _ hWmem)

def GoalProp (s : ℕ) (A : Fin 4 → Fin 4 → Bool) : Prop :=
  ∀ C : Circuit, FanInTwo C → C.size ≤ s → Represents A C → RepSizeAtMost A (s + 3)

def mapGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩
def mapCirc (f : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (mapGate f), f C.output⟩

theorem mapCirc_size (f : ℕ → ℕ) (C : Circuit) : (mapCirc f C).size = C.size := by
  simp [mapCirc, Circuit.size]

theorem mapCirc_fan (f : ℕ → ℕ) (C : Circuit) (h : FanInTwo C) : FanInTwo (mapCirc f C) := by
  intro g hg
  simp only [mapCirc, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨hop, hlen⟩ := h g0 hg0
  exact ⟨hop, by simp [mapGate, hlen]⟩

theorem mapCirc_mono (f : ℕ → ℕ) (C : Circuit) (h : Monotone2 C) : Monotone2 (mapCirc f C) := by
  intro g hg
  simp only [mapCirc, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨hop, hlen⟩ := h g0 hg0
  exact ⟨hop, by simp [mapGate, hlen]⟩

theorem mapCirc_wires_gate (f : ℕ → ℕ) (hf_hi : ∀ k, 8 ≤ k → f k = k) (hf_lo : ∀ i < 8, f i < 8)
    (gs : List Gate) (x y : List Bool) (hx : x.length = 8) (hy : y.length = 8)
    (hxy : ∀ i < 8, x.getD (f i) false = y.getD i false) :
    ∀ k < gs.length, (wiresFrom (gs.map (mapGate f)) x).getD (8 + k) false = (wiresFrom gs y).getD (8 + k) false := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    have hkm : k < (gs.map (mapGate f)).length := by simp [hk]
    have hl := wiresFrom_getD_gate (gs.map (mapGate f)) x k hkm
    have hr := wiresFrom_getD_gate gs y k hk
    rw [hx] at hl
    rw [hy] at hr
    rw [hl, hr]
    have hge : (gs.map (mapGate f))[k]'hkm = mapGate f (gs[k]'hk) := List.getElem_map _
    rw [hge]
    simp only [mapGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    by_cases hi8 : i < 8
    · have hfi8 : f i < 8 := hf_lo i hi8
      have h1 : f i < 8 + k := by omega
      have h2 : i < 8 + k := by omega
      simp only [h1, h2, ↓reduceIte]
      rw [getD_wiresFrom _ x (f i) (by omega), getD_wiresFrom _ y i (by omega)]
      exact hxy i hi8
    · rw [hf_hi i (by omega)]
      by_cases hik : i < 8 + k
      · simp only [hik, ↓reduceIte]
        have hsub : 8 + (i - 8) = i := by omega
        rw [← hsub]
        exact ih (i - 8) (by omega) (by omega)
      · simp only [hik, ↓reduceIte]

theorem mapCirc_eval (f : ℕ → ℕ) (hf_hi : ∀ k, 8 ≤ k → f k = k) (hf_lo : ∀ i < 8, f i < 8)
    (C : Circuit) (x y : List Bool) (hx : x.length = 8) (hy : y.length = 8)
    (hxy : ∀ i < 8, x.getD (f i) false = y.getD i false) :
    (mapCirc f C).eval x = C.eval y := by
  change (wiresFrom (C.gates.map (mapGate f)) x).getD (f C.output) false = (wiresFrom C.gates y).getD C.output false
  by_cases ho8 : C.output < 8
  · have hfo : f C.output < 8 := hf_lo C.output ho8
    rw [getD_wiresFrom _ x (f C.output) (by omega), getD_wiresFrom _ y C.output (by omega)]
    exact hxy C.output ho8
  · rw [hf_hi C.output (by omega)]
    by_cases holen : C.output < 8 + C.gates.length
    · have hsub : 8 + (C.output - 8) = C.output := by omega
      rw [← hsub]
      exact mapCirc_wires_gate f hf_hi hf_lo C.gates x y hx hy hxy (C.output - 8) (by omega)
    · rw [wiresFrom_getD_ge _ x C.output (by simp [hx]; omega),
          wiresFrom_getD_ge _ y C.output (by rw [hy]; omega)]

def permA (pr pc : Fin 4 → Fin 4) (tr : Bool) (A : Fin 4 → Fin 4 → Bool) (u v : Fin 4) : Bool :=
  if tr then A (pc v) (pr u) else A (pr u) (pc v)

def wireMap (pr pc : Fin 4 → Fin 4) (tr : Bool) (i : ℕ) : ℕ :=
  if h : i < 4 then
    if tr then 4 + (pr ⟨i, h⟩).val else (pr ⟨i, h⟩).val
  else if h2 : i < 8 then
    if tr then (pc ⟨i - 4, by omega⟩).val else 4 + (pc ⟨i - 4, by omega⟩).val
  else i

theorem wireMap_hi (pr pc : Fin 4 → Fin 4) (tr : Bool) (k : ℕ) (hk : 8 ≤ k) :
    wireMap pr pc tr k = k := by
  have h1 : ¬ k < 4 := by omega
  have h2 : ¬ k < 8 := by omega
  simp [wireMap, h1, h2]

theorem wireMap_lo (pr pc : Fin 4 → Fin 4) (tr : Bool) (i : ℕ) (hi : i < 8) :
    wireMap pr pc tr i < 8 := by
  unfold wireMap
  split_ifs with h1 h2 <;> omega

theorem wireMap_oneEach (pr pc : Fin 4 → Fin 4) (tr : Bool)
    (hpr : Function.Injective pr) (hpc : Function.Injective pc) (u v : Fin 4) (i : ℕ) (hi : i < 8) :
    (oneEach (if tr then pc v else pr u) (if tr then pr u else pc v)).getD (wireMap pr pc tr i) false =
      (oneEach u v).getD i false := by
  by_cases hi4 : i < 4
  · rw [oneEach_getD_row u v i hi4]
    cases tr
    · simp only [wireMap, hi4, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      rw [oneEach_getD_row _ _ _ (pr ⟨i, hi4⟩).isLt]
      exact decide_eq_decide.2 ⟨fun h => congrArg Fin.val (hpr (Fin.ext h)),
        fun h => congrArg (fun x => (pr x).val) (Fin.ext h)⟩
    · simp only [wireMap, hi4, ↓reduceDIte, ↓reduceIte]
      rw [oneEach_getD_col _ _ _ (pr ⟨i, hi4⟩).isLt]
      exact decide_eq_decide.2 ⟨fun h => congrArg Fin.val (hpr (Fin.ext h)),
        fun h => congrArg (fun x => (pr x).val) (Fin.ext h)⟩
  · have hj : i - 4 < 4 := by omega
    have hieq : i = 4 + (i - 4) := by omega
    rw [hieq, oneEach_getD_col u v (i - 4) hj]
    cases tr
    · simp only [wireMap, show ¬ 4 + (i - 4) < 4 by omega, show 4 + (i - 4) < 8 by omega,
        ↓reduceDIte, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel_left]
      rw [oneEach_getD_col _ _ _ (pc ⟨i - 4, hj⟩).isLt]
      exact decide_eq_decide.2 ⟨fun h => congrArg Fin.val (hpc (Fin.ext h)),
        fun h => congrArg (fun x => (pc x).val) (Fin.ext h)⟩
    · simp only [wireMap, show ¬ 4 + (i - 4) < 4 by omega, show 4 + (i - 4) < 8 by omega,
        ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left]
      rw [oneEach_getD_row _ _ _ (pc ⟨i - 4, hj⟩).isLt]
      exact decide_eq_decide.2 ⟨fun h => congrArg Fin.val (hpc (Fin.ext h)),
        fun h => congrArg (fun x => (pc x).val) (Fin.ext h)⟩

theorem goal_of_perm (s : ℕ) (A : Fin 4 → Fin 4 → Bool)
    (pr pc pri pci : Fin 4 → Fin 4) (tr : Bool)
    (hpr : ∀ x, pr (pri x) = x ∧ pri (pr x) = x)
    (hpc : ∀ x, pc (pci x) = x ∧ pci (pc x) = x)
    (hgoal : GoalProp s (permA pr pc tr A)) : GoalProp s A := by
  have hpr_inj : Function.Injective pr := fun a b h => by
    have := congrArg pri h; rw [(hpr a).2, (hpr b).2] at this; exact this
  have hpc_inj : Function.Injective pc := fun a b h => by
    have := congrArg pci h; rw [(hpc a).2, (hpc b).2] at this; exact this
  have hpri_inj : Function.Injective pri := fun a b h => by
    have := congrArg pr h; rw [(hpr a).1, (hpr b).1] at this; exact this
  have hpci_inj : Function.Injective pci := fun a b h => by
    have := congrArg pc h; rw [(hpc a).1, (hpc b).1] at this; exact this
  intro C hfan hsize hrep
  cases tr with
  | false =>
    set f := wireMap pri pci false
    have hrep' : Represents (permA pr pc false A) (mapCirc f C) := by
      intro u v
      have hev : (mapCirc f C).eval (oneEach u v) = C.eval (oneEach (pr u) (pc v)) := by
        apply mapCirc_eval f (wireMap_hi pri pci false) (wireMap_lo pri pci false) C
          (oneEach u v) (oneEach (pr u) (pc v)) (oneEach_len _ _) (oneEach_len _ _)
        intro i hi
        have h1 := wireMap_oneEach pri pci false hpri_inj hpci_inj (pr u) (pc v) i hi
        simpa only [Bool.false_eq_true, ↓reduceIte, (hpr u).2, (hpc v).2] using h1
      rw [hev, hrep]
      rfl
    obtain ⟨M, hm, hms, hmrep⟩ := hgoal (mapCirc f C) (mapCirc_fan f C hfan) (by rw [mapCirc_size]; exact hsize) hrep'
    set g := wireMap pr pc false
    refine ⟨mapCirc g M, mapCirc_mono g M hm, by rw [mapCirc_size]; exact hms, fun u v => ?_⟩
    have hev : (mapCirc g M).eval (oneEach u v) = M.eval (oneEach (pri u) (pci v)) := by
      apply mapCirc_eval g (wireMap_hi pr pc false) (wireMap_lo pr pc false) M
        (oneEach u v) (oneEach (pri u) (pci v)) (oneEach_len _ _) (oneEach_len _ _)
      intro i hi
      have h1 := wireMap_oneEach pr pc false hpr_inj hpc_inj (pri u) (pci v) i hi
      simpa only [Bool.false_eq_true, ↓reduceIte, (hpr u).1, (hpc v).1] using h1
    rw [hev, hmrep]
    simp only [permA, Bool.false_eq_true, ↓reduceIte, (hpr u).1, (hpc v).1]
  | true =>
    set f := wireMap pci pri true
    have hrep' : Represents (permA pr pc true A) (mapCirc f C) := by
      intro u v
      have hev : (mapCirc f C).eval (oneEach u v) = C.eval (oneEach (pc v) (pr u)) := by
        apply mapCirc_eval f (wireMap_hi pci pri true) (wireMap_lo pci pri true) C
          (oneEach u v) (oneEach (pc v) (pr u)) (oneEach_len _ _) (oneEach_len _ _)
        intro i hi
        have h1 := wireMap_oneEach pci pri true hpci_inj hpri_inj (pc v) (pr u) i hi
        simpa only [↓reduceIte, (hpr u).2, (hpc v).2] using h1
      rw [hev, hrep]
      rfl
    obtain ⟨M, hm, hms, hmrep⟩ := hgoal (mapCirc f C) (mapCirc_fan f C hfan) (by rw [mapCirc_size]; exact hsize) hrep'
    set g := wireMap pr pc true
    refine ⟨mapCirc g M, mapCirc_mono g M hm, by rw [mapCirc_size]; exact hms, fun u v => ?_⟩
    have hev : (mapCirc g M).eval (oneEach u v) = M.eval (oneEach (pri v) (pci u)) := by
      apply mapCirc_eval g (wireMap_hi pr pc true) (wireMap_lo pr pc true) M
        (oneEach u v) (oneEach (pri v) (pci u)) (oneEach_len _ _) (oneEach_len _ _)
      intro i hi
      have h1 := wireMap_oneEach pr pc true hpr_inj hpc_inj (pri v) (pci u) i hi
      simpa only [↓reduceIte, (hpr v).1, (hpc u).1] using h1
    rw [hev, hmrep]
    simp only [permA, ↓reduceIte, (hpr v).1, (hpc u).1]

def rowValA (A : Fin 4 → Fin 4 → Bool) (r : Fin 4) : ℕ :=
  (if A r 0 then 1 else 0) + (if A r 1 then 2 else 0) +
  (if A r 2 then 4 else 0) + (if A r 3 then 8 else 0)

def enc4 (A : Fin 4 → Fin 4 → Bool) : ℕ :=
  rowValA A 0 + 16 * (rowValA A 1 + 16 * (rowValA A 2 + 16 * rowValA A 3))

theorem rowValA_lt (A : Fin 4 → Fin 4 → Bool) (r : Fin 4) : rowValA A r < 16 := by
  unfold rowValA
  cases A r 0 <;> cases A r 1 <;> cases A r 2 <;> cases A r 3 <;> decide

theorem row4_bit_aux : ∀ (b0 b1 b2 b3 : Bool) (c : Fin 4),
    ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) + (if b3 then 8 else 0)).testBit c.val =
      match c.val with | 0 => b0 | 1 => b1 | 2 => b2 | _ => b3 := by
  decide

theorem rowValA_bit (A : Fin 4 → Fin 4 → Bool) (r c : Fin 4) :
    (rowValA A r).testBit c.val = A r c := by
  unfold rowValA
  rw [row4_bit_aux (A r 0) (A r 1) (A r 2) (A r 3) c]
  rcases c with ⟨c, hc⟩
  match c, hc with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem testBit_add_mul16 (a b k : ℕ) (ha : a < 16) :
    (a + 16 * b).testBit k = if k < 4 then a.testBit k else b.testBit (k - 4) := by
  by_cases hk : k < 4
  · simp only [hk, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 16 = 2 ^ k * 2 ^ (4 - k) := by
      have h4 : k + (4 - k) = 4 := by omega
      rw [← Nat.pow_add, h4]
    have hdiv : (a + 16 * b) / 2 ^ k = a / 2 ^ k + 2 ^ (4 - k) * b := by
      rw [hpow, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]
    rw [hdiv]
    have heven : 2 ∣ 2 ^ (4 - k) := by
      have : 2 ^ (4 - k) = 2 * 2 ^ (4 - k - 1) := by
        conv_lhs => rw [show 4 - k = (4 - k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      exact ⟨2 ^ (4 - k - 1), this⟩
    obtain ⟨q, hq⟩ := heven
    rw [hq, Nat.mul_assoc]
    have hmod : (a / 2 ^ k + 2 * (q * b)) % 2 = (a / 2 ^ k) % 2 := by omega
    rw [hmod]
  · simp only [hk, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ k = 16 * 2 ^ (k - 4) := by
      have h4 : 4 + (k - 4) = k := by omega
      conv_lhs => rw [← h4, Nat.pow_add]
    rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide : 0 < 16),
      Nat.div_eq_of_lt ha, Nat.zero_add]

theorem matOf_enc4 (A : Fin 4 → Fin 4 → Bool) : matOf (enc4 A) = A := by
  funext u v
  unfold matOf enc4
  have h0 := rowValA_lt A 0
  have h1 := rowValA_lt A 1
  have h2 := rowValA_lt A 2
  rcases u with ⟨u, hu⟩
  match u, hu with
  | 0, _ =>
    rw [testBit_add_mul16 _ _ _ h0]
    simp only [show 4 * 0 + v.val < 4 by omega, ↓reduceIte]
    simpa using rowValA_bit A 0 v
  | 1, _ =>
    rw [testBit_add_mul16 _ _ _ h0]
    simp only [show ¬ (4 * 1 + v.val < 4) by omega, ↓reduceIte]
    rw [testBit_add_mul16 _ _ _ h1]
    simp only [show 4 * 1 + v.val - 4 < 4 by omega, ↓reduceIte]
    simpa [show 4 * 1 + v.val - 4 = v.val by omega] using rowValA_bit A 1 v
  | 2, _ =>
    rw [testBit_add_mul16 _ _ _ h0]
    simp only [show ¬ (4 * 2 + v.val < 4) by omega, ↓reduceIte]
    rw [testBit_add_mul16 _ _ _ h1]
    simp only [show ¬ (4 * 2 + v.val - 4 < 4) by omega, ↓reduceIte]
    rw [testBit_add_mul16 _ _ _ h2]
    simp only [show 4 * 2 + v.val - 4 - 4 < 4 by omega, ↓reduceIte]
    simpa [show 4 * 2 + v.val - 4 - 4 = v.val by omega] using rowValA_bit A 2 v
  | 3, _ =>
    rw [testBit_add_mul16 _ _ _ h0]
    simp only [show ¬ (4 * 3 + v.val < 4) by omega, ↓reduceIte]
    rw [testBit_add_mul16 _ _ _ h1]
    simp only [show ¬ (4 * 3 + v.val - 4 < 4) by omega, ↓reduceIte]
    rw [testBit_add_mul16 _ _ _ h2]
    simp only [show ¬ (4 * 3 + v.val - 4 - 4 < 4) by omega, ↓reduceIte]
    simpa [show 4 * 3 + v.val - 4 - 4 - 4 = v.val by omega] using rowValA_bit A 3 v

def swapFin (a b x : Fin 4) : Fin 4 :=
  if x = a then b else if x = b then a else x

theorem swapFin_inv (a b x : Fin 4) : swapFin a b (swapFin a b x) = x := by
  unfold swapFin
  by_cases hxa : x = a
  · rw [hxa]; by_cases hab : b = a <;> simp [hab]
  · by_cases hxb : x = b
    · have hba : b ≠ a := fun h => hxa (hxb.trans h)
      rw [hxb]; simp [hba]
    · simp [hxa, hxb]

theorem goal_swapR (s : ℕ) (a b : Fin 4) (A : Fin 4 → Fin 4 → Bool)
    (h : GoalProp s (fun u v => A (swapFin a b u) v)) : GoalProp s A :=
  goal_of_perm s A (swapFin a b) id (swapFin a b) id false
    (fun x => ⟨swapFin_inv a b x, swapFin_inv a b x⟩) (fun _ => ⟨rfl, rfl⟩) h

def condSwapR (a b : Fin 4) (A : Fin 4 → Fin 4 → Bool) : Fin 4 → Fin 4 → Bool :=
  if rowValA A b < rowValA A a then (fun u v => A (swapFin a b u) v) else A

theorem goal_condSwapR (s : ℕ) (a b : Fin 4) (A : Fin 4 → Fin 4 → Bool)
    (h : GoalProp s (condSwapR a b A)) : GoalProp s A := by
  unfold condSwapR at h
  split_ifs at h
  · exact goal_swapR s a b A h
  · exact h

theorem rowValA_condSwapR (a b : Fin 4) (A : Fin 4 → Fin 4 → Bool) (r : Fin 4) :
    rowValA (condSwapR a b A) r =
      if rowValA A b < rowValA A a then rowValA A (swapFin a b r) else rowValA A r := by
  unfold condSwapR
  split_ifs <;> rfl

def sortRowsA (A : Fin 4 → Fin 4 → Bool) : Fin 4 → Fin 4 → Bool :=
  condSwapR 1 2 (condSwapR 1 3 (condSwapR 0 2 (condSwapR 2 3 (condSwapR 0 1 A))))

theorem goal_sortRowsA (s : ℕ) (A : Fin 4 → Fin 4 → Bool)
    (h : GoalProp s (sortRowsA A)) : GoalProp s A :=
  goal_condSwapR s 0 1 _ (goal_condSwapR s 2 3 _ (goal_condSwapR s 0 2 _
    (goal_condSwapR s 1 3 _ (goal_condSwapR s 1 2 _ h))))

theorem sortRowsA_sorted (A : Fin 4 → Fin 4 → Bool) :
    rowValA (sortRowsA A) 0 ≤ rowValA (sortRowsA A) 1 ∧
    rowValA (sortRowsA A) 1 ≤ rowValA (sortRowsA A) 2 ∧
    rowValA (sortRowsA A) 2 ≤ rowValA (sortRowsA A) 3 := by
  have hstep : ∀ (a b : Fin 4) (B : Fin 4 → Fin 4 → Bool),
      rowValA (condSwapR a b B) a = min (rowValA B a) (rowValA B b) ∧
      rowValA (condSwapR a b B) b = max (rowValA B a) (rowValA B b) ∧
      ∀ r : Fin 4, r ≠ a → r ≠ b → rowValA (condSwapR a b B) r = rowValA B r := by
    intro a b B
    refine ⟨?_, ?_, ?_⟩
    · rw [rowValA_condSwapR]; unfold swapFin; simp only [↓reduceIte]; split_ifs <;> omega
    · rw [rowValA_condSwapR]; unfold swapFin
      by_cases hba : b = a
      · subst hba; simp
      · simp only [hba, ↓reduceIte]; split_ifs <;> omega
    · intro r hra hrb; rw [rowValA_condSwapR]; unfold swapFin; simp [hra, hrb]
  set A1 := condSwapR 0 1 A
  set A2 := condSwapR 2 3 A1
  set A3 := condSwapR 0 2 A2
  set A4 := condSwapR 1 3 A3
  set A5 := condSwapR 1 2 A4
  obtain ⟨h1a, h1b, h1o⟩ := hstep 0 1 A
  obtain ⟨h2a, h2b, h2o⟩ := hstep 2 3 A1
  obtain ⟨h3a, h3b, h3o⟩ := hstep 0 2 A2
  obtain ⟨h4a, h4b, h4o⟩ := hstep 1 3 A3
  obtain ⟨h5a, h5b, h5o⟩ := hstep 1 2 A4
  change rowValA A1 0 = min (rowValA A 0) (rowValA A 1) at h1a
  change rowValA A1 1 = max (rowValA A 0) (rowValA A 1) at h1b
  change rowValA A2 2 = min (rowValA A1 2) (rowValA A1 3) at h2a
  change rowValA A2 3 = max (rowValA A1 2) (rowValA A1 3) at h2b
  change rowValA A3 0 = min (rowValA A2 0) (rowValA A2 2) at h3a
  change rowValA A3 2 = max (rowValA A2 0) (rowValA A2 2) at h3b
  change rowValA A4 1 = min (rowValA A3 1) (rowValA A3 3) at h4a
  change rowValA A4 3 = max (rowValA A3 1) (rowValA A3 3) at h4b
  change rowValA A5 1 = min (rowValA A4 1) (rowValA A4 2) at h5a
  change rowValA A5 2 = max (rowValA A4 1) (rowValA A4 2) at h5b
  have h1_2 : rowValA A1 2 = rowValA A 2 := h1o 2 (by decide) (by decide)
  have h1_3 : rowValA A1 3 = rowValA A 3 := h1o 3 (by decide) (by decide)
  have h2_0 : rowValA A2 0 = rowValA A1 0 := h2o 0 (by decide) (by decide)
  have h2_1 : rowValA A2 1 = rowValA A1 1 := h2o 1 (by decide) (by decide)
  have h3_1 : rowValA A3 1 = rowValA A2 1 := h3o 1 (by decide) (by decide)
  have h3_3 : rowValA A3 3 = rowValA A2 3 := h3o 3 (by decide) (by decide)
  have h4_0 : rowValA A4 0 = rowValA A3 0 := h4o 0 (by decide) (by decide)
  have h4_2 : rowValA A4 2 = rowValA A3 2 := h4o 2 (by decide) (by decide)
  have h5_0 : rowValA A5 0 = rowValA A4 0 := h5o 0 (by decide) (by decide)
  have h5_3 : rowValA A5 3 = rowValA A4 3 := h5o 3 (by decide) (by decide)
  change rowValA A5 0 ≤ rowValA A5 1 ∧ rowValA A5 1 ≤ rowValA A5 2 ∧ rowValA A5 2 ≤ rowValA A5 3
  omega

def swapRNat (a b m : ℕ) : ℕ :=
  let d := ((m >>> (4 * a)) &&& 15) ^^^ ((m >>> (4 * b)) &&& 15)
  m ^^^ (d <<< (4 * a)) ^^^ (d <<< (4 * b))

def condSwapRNat (a b m : ℕ) : ℕ :=
  if ((m >>> (4 * b)) &&& 15) < ((m >>> (4 * a)) &&& 15) then swapRNat a b m else m

def sortRowsNat (m : ℕ) : ℕ :=
  condSwapRNat 1 2 (condSwapRNat 1 3 (condSwapRNat 0 2 (condSwapRNat 2 3 (condSwapRNat 0 1 m))))

def swapCNat (a b m : ℕ) : ℕ :=
  let d := ((m >>> a) &&& 4369) ^^^ ((m >>> b) &&& 4369)
  m ^^^ (d <<< a) ^^^ (d <<< b)

def condSwapCNat (a b m : ℕ) : ℕ :=
  if ((m >>> b) &&& 4369) < ((m >>> a) &&& 4369) then swapCNat a b m else m

def sortColsNat (m : ℕ) : ℕ :=
  condSwapCNat 1 2 (condSwapCNat 1 3 (condSwapCNat 0 2 (condSwapCNat 2 3 (condSwapCNat 0 1 m))))

def swapStep (s mask m : ℕ) : ℕ :=
  let t := (m ^^^ (m >>> s)) &&& mask
  m ^^^ t ^^^ (t <<< s)

def transNat (m : ℕ) : ℕ :=
  swapStep 6 204 (swapStep 3 2570 m)

def condTransNat (m : ℕ) : ℕ :=
  let t := transNat m
  if t < m then t else m

def normNat (m : ℕ) : ℕ :=
  condTransNat (sortRowsNat (sortColsNat m))

theorem bit_15 (k : ℕ) : (15 : ℕ).testBit k = decide (k < 4) := by
  have h : (15 : ℕ) = 2 ^ 4 - 1 := rfl
  rw [h, Nat.testBit_two_pow_sub_one]

theorem bit_4369 (k : ℕ) : (4369 : ℕ).testBit k = decide (k < 16 ∧ Nat.mod k 4 = 0) := by
  by_cases hk : k < 16
  · have hfin : ∀ j : Fin 16, (4369 : ℕ).testBit j.val = decide (j.val < 16 ∧ Nat.mod j.val 4 = 0) := by decide
    exact hfin ⟨k, hk⟩
  · have h2 : 65536 ≤ 2 ^ k := pow_ge_65536 k (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 4369 < 65536) h2)]
    simp [hk]

theorem matOf_swapRNat (a b : Fin 4) (m : ℕ) :
    matOf (swapRNat a.val b.val m) = fun u v => matOf m (swapFin a b u) v := by
  funext u v
  unfold matOf swapRNat
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and, bit_15]
  have ha := a.isLt; have hb := b.isLt; have hu := u.isLt; have hv := v.isLt
  have hterm : ∀ x : Fin 4,
      (decide (4 * x.val ≤ 4 * u.val + v.val) &&
        ((m.testBit (4 * a.val + (4 * u.val + v.val - 4 * x.val)) && decide (4 * u.val + v.val - 4 * x.val < 4)) ^^
         (m.testBit (4 * b.val + (4 * u.val + v.val - 4 * x.val)) && decide (4 * u.val + v.val - 4 * x.val < 4)))) =
      if u = x then m.testBit (4 * a.val + v.val) ^^ m.testBit (4 * b.val + v.val) else false := by
    intro x; have hx := x.isLt
    by_cases hux : u = x
    · subst hux
      simp [show 4 * u.val + v.val - 4 * u.val = v.val by omega, hv]
    · have hne : u.val ≠ x.val := fun e => hux (Fin.ext e)
      by_cases hle : 4 * x.val ≤ 4 * u.val + v.val
      · simp [hux, hle, show ¬ (4 * u.val + v.val - 4 * x.val < 4) by omega]
      · simp [hux, hle]
  rw [hterm a, hterm b]
  unfold swapFin
  by_cases hua : u = a
  · subst hua
    by_cases hab : u = b
    · subst hab; simp
    · simp only [hab, ↓reduceIte]; cases m.testBit (4 * u.val + v.val) <;> cases m.testBit (4 * b.val + v.val) <;> rfl
  · by_cases hub : u = b
    · subst hub
      simp only [hua, ↓reduceIte]; cases m.testBit (4 * a.val + v.val) <;> cases m.testBit (4 * u.val + v.val) <;> rfl
    · simp [hua, hub]

theorem matOf_swapCNat (a b : Fin 4) (m : ℕ) :
    matOf (swapCNat a.val b.val m) = fun u v => matOf m u (swapFin a b v) := by
  funext u v
  unfold matOf swapCNat
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and, bit_4369]
  have ha := a.isLt; have hb := b.isLt; have hu := u.isLt; have hv := v.isLt
  have hterm : ∀ x : Fin 4,
      (decide (x.val ≤ 4 * u.val + v.val) &&
        ((m.testBit (a.val + (4 * u.val + v.val - x.val)) && decide (4 * u.val + v.val - x.val < 16 ∧ Nat.mod (4 * u.val + v.val - x.val) 4 = 0)) ^^
         (m.testBit (b.val + (4 * u.val + v.val - x.val)) && decide (4 * u.val + v.val - x.val < 16 ∧ Nat.mod (4 * u.val + v.val - x.val) 4 = 0)))) =
      if v = x then m.testBit (4 * u.val + a.val) ^^ m.testBit (4 * u.val + b.val) else false := by
    intro x; have hx := x.isLt
    by_cases hvx : v = x
    · subst hvx
      have hsub : 4 * u.val + v.val - v.val = 4 * u.val := by omega
      have hmod : Nat.mod (4 * u.val) 4 = 0 := by change (4 * u.val) % 4 = 0; omega
      rw [hsub]
      simp [show 4 * u.val < 16 by omega, hmod, Nat.add_comm]
    · have hne : v.val ≠ x.val := fun e => hvx (Fin.ext e)
      by_cases hle : x.val ≤ 4 * u.val + v.val
      · have hmod : ¬ Nat.mod (4 * u.val + v.val - x.val) 4 = 0 := by
          change ¬ (4 * u.val + v.val - x.val) % 4 = 0; omega
        simp [hvx, hle, hmod]
      · simp [hvx, hle]
  rw [hterm a, hterm b]
  unfold swapFin
  by_cases hva : v = a
  · subst hva
    by_cases hab : v = b
    · subst hab; simp
    · simp only [hab, ↓reduceIte]; cases m.testBit (4 * u.val + v.val) <;> cases m.testBit (4 * u.val + b.val) <;> rfl
  · by_cases hvb : v = b
    · subst hvb
      simp only [hva, ↓reduceIte]; cases m.testBit (4 * u.val + a.val) <;> cases m.testBit (4 * u.val + v.val) <;> rfl
    · simp [hva, hvb]

theorem swapStep_bit (s mask k m : ℕ) :
    (swapStep s mask m).testBit k =
      if mask.testBit k then
        if s ≤ k ∧ mask.testBit (k - s) then m.testBit (k + s) ^^ m.testBit (k - s) ^^ m.testBit k
        else m.testBit (k + s)
      else if s ≤ k ∧ mask.testBit (k - s) then m.testBit (k - s)
      else m.testBit k := by
  unfold swapStep
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and]
  have hsub : ∀ h : s ≤ k, s + (k - s) = k := fun h => by omega
  by_cases h1 : mask.testBit k = true
  · simp only [h1, Bool.and_true, ↓reduceIte]
    by_cases hle : s ≤ k
    · by_cases h2 : mask.testBit (k - s) = true
      · simp only [hle, h2, and_self, decide_true, Bool.and_true, Bool.true_and, ↓reduceIte, hsub hle, Nat.add_comm s k]
        cases m.testBit k <;> cases m.testBit (k + s) <;> cases m.testBit (k - s) <;> rfl
      · have h2f : mask.testBit (k - s) = false := Bool.eq_false_iff.2 h2
        simp only [hle, h2f, Bool.false_eq_true, and_false, Bool.and_false, ↓reduceIte, Nat.add_comm s k]
        cases m.testBit k <;> cases m.testBit (k + s) <;> rfl
    · simp only [hle, false_and, decide_false, Bool.false_and, ↓reduceIte, Nat.add_comm s k]
      cases m.testBit k <;> cases m.testBit (k + s) <;> rfl
  · have h1f : mask.testBit k = false := Bool.eq_false_iff.2 h1
    simp only [h1f, Bool.false_eq_true, Bool.and_false, Bool.xor_false, ↓reduceIte]
    by_cases hle : s ≤ k
    · by_cases h2 : mask.testBit (k - s) = true
      · simp only [hle, h2, and_self, decide_true, Bool.and_true, Bool.true_and, ↓reduceIte, hsub hle]
        cases m.testBit k <;> cases m.testBit (k - s) <;> rfl
      · have h2f : mask.testBit (k - s) = false := Bool.eq_false_iff.2 h2
        simp only [hle, h2f, Bool.false_eq_true, and_false, Bool.and_false, Bool.xor_false, ↓reduceIte]
    · simp only [hle, false_and, decide_false, Bool.false_and, Bool.xor_false, ↓reduceIte]

def swapIdx (s mask k : ℕ) : ℕ :=
  if mask.testBit k then k + s else if s ≤ k ∧ mask.testBit (k - s) then k - s else k

theorem swapStep_idx (s mask k m : ℕ)
    (hdisj : ¬ (mask.testBit k = true ∧ s ≤ k ∧ mask.testBit (k - s) = true)) :
    (swapStep s mask m).testBit k = m.testBit (swapIdx s mask k) := by
  rw [swapStep_bit]
  unfold swapIdx
  by_cases h1 : mask.testBit k = true
  · have h2 : ¬ (s ≤ k ∧ mask.testBit (k - s) = true) := fun h => hdisj ⟨h1, h⟩
    simp [h1, h2]
  · by_cases h2 : s ≤ k ∧ mask.testBit (k - s) = true
    · simp [h1, h2]
    · simp [h1, h2]

theorem trans_idx_ok : ∀ u v : Fin 4,
    let k := 4 * u.val + v.val
    let k1 := swapIdx 6 204 k
    ¬ ((204 : ℕ).testBit k = true ∧ 6 ≤ k ∧ (204 : ℕ).testBit (k - 6) = true) ∧
    ¬ ((2570 : ℕ).testBit k1 = true ∧ 3 ≤ k1 ∧ (2570 : ℕ).testBit (k1 - 3) = true) ∧
    swapIdx 3 2570 k1 = 4 * v.val + u.val := by
  decide

theorem matOf_transNat (m : ℕ) :
    matOf (transNat m) = permA id id true (matOf m) := by
  funext u v
  unfold matOf transNat permA
  obtain ⟨h1, h2, h3⟩ := trans_idx_ok u v
  rw [swapStep_idx 6 204 (4 * u.val + v.val) _ h1,
      swapStep_idx 3 2570 (swapIdx 6 204 (4 * u.val + v.val)) m h2, h3]
  rfl

theorem goal_condSwapRNat (s : ℕ) (a b : Fin 4) (m : ℕ)
    (h : GoalProp s (matOf (condSwapRNat a.val b.val m))) : GoalProp s (matOf m) := by
  unfold condSwapRNat at h
  split_ifs at h
  · rw [matOf_swapRNat] at h
    exact goal_swapR s a b (matOf m) h
  · exact h

theorem goal_condSwapCNat (s : ℕ) (a b : Fin 4) (m : ℕ)
    (h : GoalProp s (matOf (condSwapCNat a.val b.val m))) : GoalProp s (matOf m) := by
  unfold condSwapCNat at h
  split_ifs at h
  · rw [matOf_swapCNat] at h
    exact goal_of_perm s (matOf m) id (swapFin a b) id (swapFin a b) false
      (fun _ => ⟨rfl, rfl⟩) (fun x => ⟨swapFin_inv a b x, swapFin_inv a b x⟩) h
  · exact h

theorem goal_condTransNat (s : ℕ) (m : ℕ)
    (h : GoalProp s (matOf (condTransNat m))) : GoalProp s (matOf m) := by
  unfold condTransNat at h
  dsimp only at h
  split_ifs at h
  · rw [matOf_transNat] at h
    exact goal_of_perm s (matOf m) id id id id true
      (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩) h
  · exact h

theorem goal_normNat (s : ℕ) (m : ℕ)
    (h : GoalProp s (matOf (normNat m))) : GoalProp s (matOf m) := by
  unfold normNat sortRowsNat sortColsNat at h
  exact goal_condSwapCNat s 0 1 _ (goal_condSwapCNat s 2 3 _ (goal_condSwapCNat s 0 2 _
    (goal_condSwapCNat s 1 3 _ (goal_condSwapCNat s 1 2 _
      (goal_condSwapRNat s 0 1 _ (goal_condSwapRNat s 2 3 _ (goal_condSwapRNat s 0 2 _
        (goal_condSwapRNat s 1 3 _ (goal_condSwapRNat s 1 2 _
          (goal_condTransNat s _ h))))))))))

set_option maxHeartbeats 0 in
def perms4BT : BT (BT (Fin 4) 2) 5 :=
  (((((((0, 1), (2, 3)), ((0, 1), (3, 2))), (((0, 2), (1, 3)), ((0, 2), (3, 1)))), ((((0, 3), (1, 2)), ((0, 3), (2, 1))), (((1, 0), (2, 3)), ((1, 0), (3, 2))))), (((((1, 2), (0, 3)), ((1, 2), (3, 0))), (((1, 3), (0, 2)), ((1, 3), (2, 0)))), ((((2, 0), (1, 3)), ((2, 0), (3, 1))), (((2, 1), (0, 3)), ((2, 1), (3, 0)))))), ((((((2, 3), (0, 1)), ((2, 3), (1, 0))), (((3, 0), (1, 2)), ((3, 0), (2, 1)))), ((((3, 1), (0, 2)), ((3, 1), (2, 0))), (((3, 2), (0, 1)), ((3, 2), (1, 0))))), (((((0, 1), (2, 3)), ((0, 1), (2, 3))), (((0, 1), (2, 3)), ((0, 1), (2, 3)))), ((((0, 1), (2, 3)), ((0, 1), (2, 3))), (((0, 1), (2, 3)), ((0, 1), (2, 3)))))))

def permFn (p : ℕ) (x : Fin 4) : Fin 4 := btGet (btGet perms4BT p) x.val

def permInv (p : ℕ) (y : Fin 4) : Fin 4 :=
  if permFn p 0 = y then 0 else if permFn p 1 = y then 1 else if permFn p 2 = y then 2 else 3

def checkPerm4 (t : BT (Fin 4) 2) : Bool :=
  let fn (x : Fin 4) := btGet t x.val
  let inv (y : Fin 4) := if fn 0 = y then 0 else if fn 1 = y then 1 else if fn 2 = y then 2 else 3
  (List.range 4).all fun i =>
    let x := Fin.ofNat 4 i
    decide (fn (inv x) = x ∧ inv (fn x) = x)

theorem perms4_ok : btAll checkPerm4 perms4BT = true := by decide +kernel

theorem fin_ofNat_eq (x : Fin 4) : Fin.ofNat 4 x.val = x := by
  apply Fin.ext; simp

theorem perms4_bij (p : ℕ) (x : Fin 4) :
    permFn p (permInv p x) = x ∧ permInv p (permFn p x) = x := by
  have h1 := btAll_get checkPerm4 perms4BT p perms4_ok
  have h2 := List.all_eq_true.1 h1 x.val (List.mem_range.2 x.isLt)
  rw [fin_ofNat_eq x] at h2
  exact of_decide_eq_true h2

def applyPermNat (m pr pc : ℕ) (tr : Bool) : ℕ :=
  (List.range 16).foldr (fun k acc =>
    let u : Fin 4 := Fin.ofNat 4 (k / 4)
    let v : Fin 4 := Fin.ofNat 4 (Nat.mod k 4)
    let sr := if tr then permFn pc v else permFn pr u
    let sc := if tr then permFn pr u else permFn pc v
    if m.testBit (4 * sr.val + sc.val) then acc ||| 2 ^ k else acc) 0

theorem fold16_testBit (p : ℕ → Bool) (k : ℕ) (hk : k < 16) :
    ((List.range 16).foldr (fun j acc => if p j then acc ||| 2 ^ j else acc) 0).testBit k = p k := by
  have haux : ∀ (L : List ℕ), L.Nodup →
      (L.foldr (fun j acc => if p j then acc ||| 2 ^ j else acc) 0).testBit k =
      if k ∈ L then p k else false := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons a L ih =>
      intro hnd
      obtain ⟨han, hndL⟩ := List.nodup_cons.1 hnd
      simp only [List.foldr_cons]
      by_cases hka : k = a
      · subst hka
        simp only [List.mem_cons_self, ↓reduceIte]
        cases hp : p k
        · simp [ih hndL, han]
        · simp [Nat.testBit_or]
      · have hne : a ≠ k := fun e => hka e.symm
        simp only [List.mem_cons, hka, false_or]
        cases hp : p a
        · simp [ih hndL]
        · simp [Nat.testBit_or, ih hndL, hne]
  have h := haux (List.range 16) List.nodup_range
  simp only [List.mem_range.2 hk, ↓reduceIte] at h
  exact h

theorem matOf_applyPermNat (m pr pc : ℕ) (tr : Bool) :
    matOf (applyPermNat m pr pc tr) = permA (permFn pr) (permFn pc) tr (matOf m) := by
  funext u v
  unfold matOf applyPermNat permA
  rw [fold16_testBit _ (4 * u.val + v.val) (by omega)]
  have hu : Fin.ofNat 4 ((4 * u.val + v.val) / 4) = u := by
    apply Fin.ext; simp [show (4 * u.val + v.val) / 4 = u.val by omega]
  have hv : Fin.ofNat 4 (Nat.mod (4 * u.val + v.val) 4) = v := by
    have hmod : Nat.mod (4 * u.val + v.val) 4 = v.val := by
      change (4 * u.val + v.val) % 4 = v.val; omega
    apply Fin.ext; simp [hmod]
  rw [hu, hv]
  cases tr <;> rfl

set_option maxHeartbeats 0 in
def lvl2PlansBT : BT (BT (ℕ × ℕ × ℕ × ℕ) 4) 5 :=
  ((((((((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))), (((((1, 1, 14, 11), (1, 0, 2, 11)), ((1, 0, 2, 11), (1, 0, 2, 11))), (((0, 3, 0, 84), (0, 3, 0, 84)), ((0, 3, 0, 84), (2, 0, 4, 14)))), ((((0, 3, 0, 84), (0, 3, 0, 84)), ((0, 3, 0, 84), (1, 0, 2, 11))), (((0, 3, 0, 84), (0, 3, 0, 84)), ((0, 3, 0, 84), (1, 0, 2, 11)))))), ((((((1, 2, 0, 85), (1, 0, 0, 14)), ((1, 0, 0, 14), (1, 0, 0, 14))), (((0, 1, 12, 11), (0, 2, 25, 14)), ((0, 1, 12, 11), (0, 1, 12, 11)))), ((((0, 1, 12, 11), (0, 2, 25, 14)), ((0, 1, 12, 11), (0, 1, 12, 11))), (((0, 1, 12, 11), (0, 2, 25, 14)), ((0, 1, 12, 11), (0, 1, 12, 11))))), (((((1, 3, 1, 29), (1, 3, 1, 29)), ((1, 3, 1, 29), (2, 0, 0, 29))), (((0, 2, 1, 29), (0, 2, 1, 29)), ((2, 0, 0, 29), (0, 2, 1, 29)))), ((((0, 2, 1, 29), (0, 2, 1, 29)), ((1, 3, 1, 29), (0, 2, 1, 29))), (((0, 2, 1, 29), (0, 2, 1, 29)), ((1, 3, 1, 29), (0, 2, 1, 29))))))), (((((((1, 2, 0, 84), (1, 2, 0, 84)), ((1, 3, 0, 84), (1, 2, 0, 84))), (((0, 2, 1, 29), (0, 2, 1, 29)), ((2, 0, 4, 29), (0, 2, 1, 29)))), ((((0, 2, 1, 29), (0, 2, 1, 29)), ((1, 3, 0, 84), (0, 2, 1, 29))), (((0, 2, 1, 29), (0, 2, 1, 29)), ((1, 3, 0, 84), (0, 2, 1, 29))))), (((((1, 2, 0, 85), (1, 2, 0, 85)), ((1, 3, 0, 85), (1, 2, 0, 85))), (((0, 2, 1, 29), (0, 2, 1, 29)), ((2, 0, 4, 29), (0, 2, 1, 29)))), ((((0, 2, 1, 29), (0, 2, 1, 29)), ((1, 3, 0, 85), (0, 2, 1, 29))), (((0, 2, 1, 29), (0, 2, 1, 29)), ((1, 3, 0, 85), (0, 2, 1, 29)))))), ((((((1, 2, 0, 94), (1, 2, 0, 94)), ((1, 3, 0, 94), (1, 2, 0, 94))), (((2, 1, 0, 94), (2, 2, 0, 94)), ((2, 1, 0, 94), (2, 1, 0, 94)))), ((((1, 2, 0, 94), (1, 2, 0, 94)), ((1, 3, 0, 94), (1, 2, 0, 94))), (((1, 2, 0, 94), (1, 2, 0, 94)), ((1, 3, 0, 94), (1, 2, 0, 94))))), (((((1, 1, 0, 85), (1, 0, 0, 29)), ((1, 0, 0, 29), (1, 0, 0, 29))), (((0, 1, 1, 29), (0, 2, 1, 29)), ((0, 1, 1, 29), (0, 1, 1, 29)))), ((((0, 1, 1, 29), (0, 2, 1, 29)), ((0, 1, 1, 29), (0, 1, 1, 29))), (((0, 1, 1, 29), (0, 2, 1, 29)), ((0, 1, 1, 29), (0, 1, 1, 29)))))))), ((((((((1, 2, 0, 85), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 84), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 84), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 84), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))), (((((1, 1, 16, 85), (1, 2, 16, 85)), ((1, 1, 16, 85), (1, 1, 16, 85))), (((0, 1, 0, 84), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 84), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 84), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))))), ((((((1, 2, 0, 85), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 85), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 85), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 85), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))), (((((1, 1, 16, 85), (1, 2, 16, 85)), ((1, 1, 16, 85), (1, 1, 16, 85))), (((0, 1, 0, 85), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 85), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 85), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))))), (((((((1, 1, 0, 94), (1, 2, 0, 94)), ((1, 1, 0, 94), (1, 1, 0, 94))), (((2, 1, 2, 94), (2, 3, 0, 94)), ((2, 1, 2, 94), (2, 1, 2, 94)))), ((((1, 1, 0, 94), (1, 2, 0, 94)), ((1, 1, 0, 94), (1, 1, 0, 94))), (((1, 1, 0, 94), (1, 2, 0, 94)), ((1, 1, 0, 94), (1, 1, 0, 94))))), (((((1, 1, 0, 94), (1, 2, 12, 94)), ((1, 1, 0, 94), (1, 1, 0, 94))), (((2, 1, 2, 94), (2, 2, 0, 238)), ((2, 1, 2, 94), (2, 1, 2, 94)))), ((((1, 1, 0, 94), (1, 2, 12, 94)), ((1, 1, 0, 94), (1, 1, 0, 94))), (((1, 1, 0, 94), (1, 2, 12, 94)), ((1, 1, 0, 94), (1, 1, 0, 94)))))), ((((((1, 1, 0, 94), (1, 3, 68, 94)), ((1, 1, 0, 94), (1, 1, 0, 94))), (((0, 2, 12, 94), (0, 2, 12, 94)), ((0, 3, 40, 94), (0, 2, 12, 94)))), ((((0, 2, 12, 94), (0, 2, 12, 94)), ((0, 3, 40, 94), (0, 2, 12, 94))), (((0, 2, 12, 94), (0, 2, 12, 94)), ((0, 3, 40, 94), (0, 2, 12, 94))))), (((((1, 1, 0, 94), (1, 2, 12, 94)), ((1, 1, 0, 94), (1, 1, 0, 94))), (((2, 1, 2, 94), (0, 0, 0, 85)), ((0, 0, 0, 85), (0, 0, 0, 85)))), ((((1, 1, 0, 94), (0, 0, 0, 85)), ((0, 0, 0, 85), (0, 0, 0, 85))), (((1, 1, 0, 94), (0, 0, 0, 85)), ((0, 0, 0, 85), (0, 0, 0, 85))))))))), (((((((((2, 2, 56, 94), (1, 0, 0, 94)), ((1, 0, 0, 94), (1, 0, 0, 94))), (((0, 1, 0, 94), (0, 0, 0, 94)), ((0, 0, 0, 94), (0, 0, 0, 94)))), ((((0, 1, 0, 94), (0, 0, 0, 94)), ((0, 0, 0, 94), (0, 0, 0, 94))), (((0, 1, 0, 94), (0, 0, 0, 94)), ((0, 0, 0, 94), (0, 0, 0, 94))))), (((((1, 1, 0, 94), (2, 2, 0, 238)), ((1, 1, 0, 94), (1, 1, 0, 94))), (((2, 2, 0, 238), (0, 0, 0, 94)), ((0, 0, 0, 94), (0, 0, 0, 94)))), ((((1, 1, 0, 94), (0, 0, 0, 94)), ((0, 0, 0, 94), (0, 0, 0, 94))), (((1, 1, 0, 94), (0, 0, 0, 94)), ((0, 0, 0, 94), (0, 0, 0, 94)))))), ((((((1, 1, 0, 238), (2, 2, 0, 238)), ((1, 1, 0, 238), (1, 1, 0, 238))), (((2, 2, 0, 238), (0, 0, 0, 238)), ((0, 0, 0, 238), (0, 0, 0, 238)))), ((((1, 1, 0, 238), (0, 0, 0, 238)), ((0, 0, 0, 238), (0, 0, 0, 238))), (((1, 1, 0, 238), (0, 0, 0, 238)), ((0, 0, 0, 238), (0, 0, 0, 238))))), (((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))))), (((((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))), (((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))))), ((((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))), (((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))))))), ((((((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))), (((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))))), ((((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))), (((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))))), (((((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))), (((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))))), ((((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))), (((((1, 2, 0, 29), (1, 0, 4, 29)), ((1, 0, 4, 29), (1, 0, 4, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29)))), ((((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))), (((0, 1, 0, 29), (0, 0, 0, 29)), ((0, 0, 0, 29), (0, 0, 0, 29))))))))))

set_option maxHeartbeats 0 in
def atlasBT : BT (Circuit × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) 8 :=
  (((((((((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[⟨.and, [0, 4]⟩], 8⟩, 1, 1, 0, 0, 0, 0, 0)), ((⟨[⟨.or, [4, 5]⟩, ⟨.and, [0, 8]⟩], 9⟩, 3, 2, 0, 0, 0, 0, 0), (⟨[⟨.or, [4, 5]⟩, ⟨.or, [8, 6]⟩, ⟨.and, [0, 9]⟩], 10⟩, 7, 3, 0, 0, 0, 0, 0))), (((⟨[], 0⟩, 15, 0, 0, 0, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [8, 9]⟩], 10⟩, 18, 3, 0, 0, 0, 0, 0)), ((⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [8, 10]⟩], 11⟩, 19, 4, 1, 0, 1, 0, 1), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [8, 10]⟩], 11⟩, 22, 4, 1, 0, 1, 0, 1)))), ((((⟨[⟨.or, [0, 1]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [11, 9]⟩], 12⟩, 23, 5, 1, 1, 0, 0, 3), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [8, 11]⟩], 12⟩, 30, 5, 1, 1, 1, 6, 3)), ((⟨[⟨.and, [1, 4]⟩, ⟨.or, [0, 8]⟩], 9⟩, 31, 2, 0, 0, 0, 0, 0), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 9]⟩], 10⟩, 51, 3, 0, 0, 0, 0, 0))), (((⟨[⟨.or, [4, 5]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [11, 9]⟩], 12⟩, 53, 5, 1, 0, 2, 0, 3), (⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [8, 11]⟩], 12⟩, 55, 5, 1, 0, 2, 0, 3)), ((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [10, 11]⟩], 12⟩, 60, 5, 1, 0, 2, 0, 3), (⟨[⟨.or, [4, 5]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 9]⟩], 13⟩, 61, 6, 1, 2, 0, 0, 14))))), (((((⟨[⟨.or, [4, 5]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 9]⟩], 10⟩, 63, 3, 0, 0, 0, 0, 0), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [8, 10]⟩], 11⟩, 119, 4, 1, 0, 0, 0, 3)), ((⟨[⟨.or, [4, 5]⟩, ⟨.or, [8, 6]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 10]⟩], 13⟩, 123, 6, 1, 2, 0, 0, 29), (⟨[⟨.or, [4, 5]⟩, ⟨.or, [8, 6]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩], 11⟩, 127, 4, 1, 0, 0, 0, 3))), (((⟨[⟨.or, [0, 1]⟩], 8⟩, 255, 1, 0, 0, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [8, 11]⟩], 12⟩, 278, 5, 1, 0, 1, 1, 3)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 10]⟩], 13⟩, 279, 6, 1, 1, 1, 0, 11), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [8, 12]⟩], 13⟩, 286, 6, 1, 1, 1, 0, 14)))), ((((⟨[⟨.or, [1, 2]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [0, 9]⟩], 10⟩, 287, 3, 0, 0, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩, 292, 5, 1, 0, 2, 0, 10)), ((⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [8, 4]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, 293, 6, 1, 0, 2, 0, 10), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [10, 13]⟩], 14⟩, 295, 7, 1, 1, 1, 0, 11))), (((⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩, 300, 6, 1, 0, 2, 0, 10), (⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [13, 11]⟩], 14⟩, 301, 7, 1, 1, 2, 2, 11)), ((⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [0, 10]⟩], 11⟩, 303, 4, 1, 0, 0, 0, 1), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, 310, 7, 1, 0, 2, 0, 11)))))), ((((((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 11]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [12, 13]⟩], 14⟩, 311, 7, 1, 0, 2, 0, 11), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [11, 13]⟩], 14⟩, 316, 7, 1, 0, 2, 0, 11)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩, 317, 8, 1, 2, 2, 0, 29), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, 318, 8, 1, 2, 2, 4, 29))), (((⟨[⟨.or, [1, 2]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [10, 11]⟩], 12⟩, 319, 5, 1, 0, 1, 1, 3), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [9, 11]⟩], 12⟩, 358, 5, 1, 0, 0, 0, 3)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [12, 10]⟩], 13⟩, 359, 6, 1, 0, 1, 0, 10), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, 362, 7, 1, 0, 3, 0, 14)))), ((((⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [10, 14]⟩], 15⟩, 363, 8, 1, 2, 0, 0, 29), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 11]⟩], 14⟩, 366, 7, 1, 0, 3, 0, 14)), ((⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩, 367, 5, 1, 0, 0, 0, 3), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [12, 10]⟩], 13⟩, 375, 6, 1, 0, 1, 0, 11))), (((⟨[⟨.and, [2, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, 379, 8, 1, 2, 0, 0, 29), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩, 382, 8, 1, 2, 1, 4, 29)), ((⟨[⟨.or, [1, 2]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [12, 10]⟩], 13⟩, 383, 6, 1, 0, 1, 0, 11), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [9, 12]⟩], 13⟩, 494, 6, 1, 0, 1, 0, 14))))), (((((⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [0, 12]⟩], 13⟩, 495, 6, 1, 0, 1, 0, 14), (⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [8, 9]⟩], 10⟩, 511, 3, 0, 0, 0, 0, 0)), ((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [11, 12]⟩], 13⟩, 828, 6, 1, 1, 0, 0, 14), (⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [13, 10]⟩], 14⟩, 829, 7, 1, 1, 0, 0, 14))), (((⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [0, 10]⟩], 11⟩, 831, 4, 1, 0, 0, 1, 3), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [13, 12]⟩], 14⟩, 854, 7, 1, 0, 1, 0, 11)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 11]⟩], 14⟩, 855, 7, 1, 0, 1, 0, 11), (⟨[⟨.or, [4, 5]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩, 857, 8, 1, 0, 3, 0, 29)))), ((((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [12, 9]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [13, 14]⟩], 15⟩, 858, 8, 1, 0, 3, 0, 29), (⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [14, 12]⟩], 15⟩, 859, 8, 1, 0, 3, 0, 29)), ((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [11, 14]⟩], 15⟩, 862, 8, 1, 0, 3, 0, 29), (⟨[⟨.or, [4, 5]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [12, 10]⟩], 13⟩, 863, 6, 1, 0, 0, 0, 10))), (((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.and, [8, 6]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [9, 12]⟩], 13⟩, 887, 6, 1, 0, 0, 0, 11), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [14, 13]⟩], 15⟩, 891, 8, 1, 2, 0, 0, 29)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [11, 14]⟩], 15⟩, 892, 8, 1, 2, 0, 4, 29), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [14, 11]⟩, ⟨.or, [13, 15]⟩], 16⟩, 893, 9, 1, 3, 0, 0, 94))))))), (((((((⟨[⟨.or, [1, 2]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, 895, 6, 1, 0, 0, 0, 11), (⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [0, 12]⟩], 13⟩, 975, 6, 1, 0, 0, 0, 14)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 10]⟩], 14⟩, 989, 7, 1, 0, 0, 0, 14), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [13, 14]⟩], 15⟩, 990, 8, 1, 0, 2, 0, 29))), (((⟨[⟨.or, [4, 5]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [13, 10]⟩], 14⟩, 991, 7, 1, 0, 0, 0, 14), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩, 1023, 4, 1, 0, 0, 0, 15)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [9, 11]⟩], 12⟩, 1911, 5, 1, 0, 0, 0, 27), (⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [13, 11]⟩], 14⟩, 1915, 7, 1, 1, 0, 0, 29)))), ((((⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩, 1919, 5, 1, 0, 0, 0, 27), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 7]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [9, 15]⟩, ⟨.or, [14, 16]⟩], 17⟩, 1981, 10, 2, 0, 0, 0, 0)), ((⟨[⟨.or, [4, 5]⟩, ⟨.or, [8, 6]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [8, 7]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [13, 11]⟩], 14⟩, 1983, 7, 1, 0, 0, 0, 29), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [8, 11]⟩], 12⟩, 2047, 5, 1, 0, 0, 0, 31))), (((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩], 9⟩, 4095, 2, 0, 0, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [8, 13]⟩], 14⟩, 4382, 7, 1, 1, 1, 0, 78)), ((⟨[⟨.or, [0, 4]⟩], 8⟩, 4383, 1, 0, 0, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩, 4396, 7, 1, 0, 2, 1, 14))))), (((((⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩, 4397, 8, 1, 2, 2, 0, 85), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩, 4398, 8, 1, 2, 2, 16, 85)), ((⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩, 4399, 5, 1, 0, 1, 37, 3), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [11, 15]⟩], 16⟩, 4414, 9, 1, 2, 2, 0, 94))), (((⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [9, 8]⟩], 10⟩, 4415, 3, 0, 0, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, 4458, 8, 1, 2, 0, 0, 29)), ((⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [14, 13]⟩, ⟨.and, [10, 15]⟩], 16⟩, 4459, 9, 1, 2, 3, 24, 94), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, 4462, 8, 1, 2, 1, 16, 85)))), ((((⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [0, 12]⟩], 13⟩, 4463, 6, 1, 0, 1, 1, 14), (⟨[⟨.or, [5, 6]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 10]⟩], 13⟩, 4475, 6, 1, 2, 0, 0, 29)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 4478, 9, 1, 2, 1, 0, 94), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [10, 8]⟩], 11⟩, 4479, 4, 1, 0, 0, 0, 3))), (((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [9, 13]⟩], 14⟩, 4590, 7, 1, 0, 1, 0, 78), (⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩, 4591, 7, 1, 0, 1, 0, 78)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩], 9⟩, 4607, 2, 0, 0, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, 4680, 7, 1, 0, 3, 0, 84)))))), ((((((⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, 4681, 8, 1, 0, 3, 0, 84), (⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [10, 15]⟩], 16⟩, 4683, 9, 2, 1, 0, 0, 0)), ((⟨[⟨.or, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩, 4687, 6, 1, 0, 0, 0, 10), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, 4698, 8, 1, 0, 3, 0, 85))), (((⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [12, 9]⟩, ⟨.or, [10, 14]⟩, ⟨.and, [13, 15]⟩], 16⟩, 4699, 9, 1, 3, 3, 28, 94), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 4700, 9, 1, 2, 1, 0, 94)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 4701, 9, 2, 2, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [14, 6]⟩, ⟨.and, [11, 15]⟩], 16⟩, 4702, 9, 1, 2, 1, 0, 94)))), ((((⟨[⟨.or, [1, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩, 4703, 7, 1, 0, 1, 12, 11), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [11, 5]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [16, 15]⟩], 17⟩, 4731, 10, 2, 3, 0, 0, 0)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [8, 6]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [9, 15]⟩, ⟨.or, [14, 16]⟩], 17⟩, 4732, 10, 2, 4, 0, 0, 0), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [9, 15]⟩, ⟨.or, [14, 16]⟩], 17⟩, 4733, 10, 2, 5, 0, 0, 0))), (((⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [0, 14]⟩], 15⟩, 4735, 8, 1, 0, 2, 1, 29), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩, 4812, 7, 1, 0, 0, 0, 14)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩, 4813, 8, 1, 0, 2, 0, 84), (⟨[⟨.or, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩, 4815, 7, 1, 0, 0, 0, 14))))), (((((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [12, 9]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [13, 14]⟩], 15⟩, 4829, 8, 1, 0, 2, 0, 85), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [8, 14]⟩, ⟨.or, [15, 13]⟩], 16⟩, 4830, 9, 1, 2, 2, 2, 94)), ((⟨[⟨.or, [1, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩, 4831, 8, 1, 0, 2, 0, 85), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩], 12⟩, 4863, 5, 1, 0, 0, 0, 15))), (((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [8, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 4958, 9, 1, 1, 2, 0, 94), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [11, 8]⟩], 12⟩, 4959, 5, 1, 0, 0, 0, 10)), ((⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 4972, 9, 1, 0, 3, 0, 94), (⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [10, 14]⟩, ⟨.and, [11, 15]⟩], 16⟩, 4973, 9, 1, 0, 3, 0, 94)))), ((((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 4974, 9, 1, 0, 3, 0, 94), (⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, 4975, 8, 1, 0, 2, 25, 29)), ((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [10, 15]⟩, ⟨.or, [14, 16]⟩], 17⟩, 4990, 10, 2, 6, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [12, 11]⟩], 13⟩, 4991, 6, 1, 0, 0, 0, 11))), (((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [11, 14]⟩], 15⟩, 5068, 8, 1, 0, 2, 26, 85), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [15, 13]⟩], 16⟩, 5069, 9, 1, 3, 2, 56, 94)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩, 5070, 9, 1, 1, 2, 0, 94), (⟨[⟨.or, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩, 5071, 8, 1, 0, 2, 26, 85)))))))), ((((((((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [12, 4]⟩], 13⟩, 5085, 6, 1, 0, 0, 0, 14), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [14, 7]⟩, ⟨.and, [11, 15]⟩], 16⟩, 5086, 9, 1, 1, 2, 0, 94)), ((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [12, 8]⟩], 13⟩, 5087, 6, 1, 0, 0, 0, 14), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩, 5102, 9, 1, 0, 2, 0, 94))), (((⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [8, 5]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩, 5103, 9, 1, 0, 2, 0, 94), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [10, 9]⟩], 11⟩, 5119, 4, 1, 0, 0, 0, 15)), ((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [8, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩, 5754, 9, 1, 2, 2, 0, 94), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [0, 15]⟩, ⟨.or, [16, 14]⟩], 17⟩, 5755, 10, 2, 7, 0, 0, 0)))), ((((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 5758, 9, 1, 2, 1, 0, 94), (⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 11]⟩], 14⟩, 5759, 7, 1, 0, 1, 1, 29)), ((⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [4, 3]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [14, 10]⟩, ⟨.or, [15, 13]⟩], 16⟩, 5804, 9, 1, 3, 0, 0, 238), (⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [15, 10]⟩, ⟨.and, [14, 16]⟩], 17⟩, 5805, 10, 2, 8, 0, 0, 0))), (((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩, 5806, 9, 2, 9, 0, 0, 0), (⟨[⟨.or, [1, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, 5807, 8, 1, 0, 0, 0, 29)), ((⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [12, 8]⟩, ⟨.and, [13, 9]⟩, ⟨.or, [14, 11]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [16, 15]⟩], 17⟩, 5821, 10, 2, 10, 0, 0, 0), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [14, 3]⟩, ⟨.and, [11, 15]⟩, ⟨.or, [13, 16]⟩], 17⟩, 5822, 10, 2, 11, 0, 0, 0))))), (((((⟨[⟨.or, [1, 5]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩, 5823, 9, 1, 0, 3, 24, 94), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, 5870, 8, 1, 0, 1, 16, 85)), ((⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, 5871, 8, 1, 0, 1, 16, 85), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [8, 12]⟩], 13⟩, 5887, 6, 1, 0, 0, 0, 31))), (((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [14, 3]⟩, ⟨.and, [10, 15]⟩], 16⟩, 6014, 9, 1, 1, 1, 0, 94), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [11, 8]⟩], 12⟩, 6015, 5, 1, 0, 0, 0, 27)), ((⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [14, 12]⟩], 15⟩, 6077, 8, 1, 0, 0, 0, 29), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [8, 16]⟩, ⟨.or, [17, 15]⟩], 18⟩, 6078, 11, 2, 12, 0, 0, 0)))), ((((⟨[⟨.or, [0, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [13, 11]⟩], 14⟩, 6079, 7, 1, 0, 0, 0, 29), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 6126, 9, 1, 0, 1, 0, 94)), ((⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 6127, 9, 1, 0, 1, 0, 94), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [11, 9]⟩], 12⟩, 6143, 5, 1, 0, 0, 0, 31))), (((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [10, 13]⟩], 14⟩, 7918, 7, 1, 0, 1, 0, 118), (⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩, 7919, 7, 1, 0, 1, 0, 118)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩, 7935, 7, 1, 0, 1, 0, 119), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [9, 4]⟩], 10⟩, 8191, 3, 0, 0, 0, 0, 0)))))), ((((((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [11, 13]⟩], 14⟩, 13260, 7, 1, 0, 0, 0, 78), (⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [14, 3]⟩, ⟨.and, [13, 15]⟩], 16⟩, 13261, 9, 1, 2, 2, 56, 94)), ((⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩, 13263, 7, 1, 0, 0, 0, 78), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [14, 3]⟩, ⟨.and, [13, 15]⟩], 16⟩, 13278, 9, 1, 2, 2, 0, 238))), (((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩, 13279, 7, 1, 0, 0, 0, 78), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩], 10⟩, 13311, 3, 0, 0, 0, 0, 0)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [8, 7]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩, 13726, 11, 2, 13, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, 13727, 7, 1, 0, 0, 0, 84)))), ((((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [17, 15]⟩], 18⟩, 13740, 11, 2, 14, 0, 0, 0), (⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 13741, 9, 1, 0, 2, 12, 94)), ((⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩, 13743, 9, 1, 0, 2, 12, 94), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [14, 16]⟩], 17⟩, 13758, 10, 2, 15, 0, 0, 0))), (((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [10, 3]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, 13759, 8, 1, 0, 0, 0, 85), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [14, 3]⟩, ⟨.and, [11, 15]⟩], 16⟩, 13806, 9, 1, 0, 1, 0, 94)), ((⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 13807, 9, 1, 0, 1, 0, 94), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩, 13823, 6, 1, 0, 0, 0, 87))))), (((((⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [15, 3]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [13, 17]⟩], 18⟩, 14285, 11, 2, 16, 0, 0, 0), (⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [8, 6]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩, 14287, 9, 1, 0, 0, 0, 94)), ((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [15, 3]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [14, 17]⟩], 18⟩, 14302, 11, 2, 17, 0, 0, 0), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, 14303, 9, 1, 0, 0, 0, 94))), (((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [11, 5]⟩], 12⟩, 14335, 5, 1, 0, 0, 0, 95), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩, 15615, 7, 1, 0, 0, 0, 119)), ((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [14, 3]⟩, ⟨.and, [13, 15]⟩], 16⟩, 15838, 9, 1, 1, 2, 0, 238), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩, 15839, 7, 1, 0, 0, 0, 118)))), ((((⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [11, 15]⟩], 16⟩, 15855, 9, 1, 0, 2, 0, 238), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩, 15871, 7, 1, 0, 0, 0, 119)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [10, 5]⟩], 11⟩, 16383, 4, 1, 0, 0, 0, 127), (⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [14, 7]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [15, 3]⟩, ⟨.and, [16, 17]⟩], 18⟩, 31710, 11, 2, 18, 0, 0, 0))), (((⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩, 31711, 9, 1, 0, 0, 0, 238), (⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, 31743, 7, 1, 0, 0, 0, 239)), ((⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [11, 6]⟩], 12⟩, 32767, 5, 1, 0, 0, 0, 255), (⟨[⟨.and, []⟩], 8⟩, 65535, 1, 0, 0, 0, 0, 0))))))), (((((((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0))), (((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)))), ((((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0))), (((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0))))), (((((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0))), (((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)))), ((((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0))), (((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)))))), ((((((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0))), (((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)))), ((((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0))), (((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0))))), (((((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0))), (((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)))), ((((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0))), (((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)), ((⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0), (⟨[], 8⟩, 0, 0, 0, 0, 0, 0, 0)))))))))

set_option maxHeartbeats 0 in
def normBT : BT (ℕ × ℕ × ℕ × ℕ × Bool) 9 :=
  ((((((((((0, 0, 0, 0, false), (32768, 1, 18, 18, false)), ((33792, 5, 16, 22, false), (33824, 25, 9, 23, false))), (((33825, 95, 0, 23, false), (33826, 28, 9, 22, true)), ((33842, 96, 9, 11, false), (33843, 109, 0, 22, false)))), ((((33856, 7, 16, 21, true), (33858, 28, 15, 18, true)), ((33859, 79, 4, 16, false), (33860, 9, 16, 18, true))), (((34368, 26, 17, 17, false), (34369, 96, 13, 16, false)), ((34370, 39, 9, 23, true), (34371, 101, 3, 17, false))))), (((((34372, 29, 17, 16, true), (34386, 101, 9, 11, false)), ((34387, 138, 0, 23, false), (34388, 97, 16, 15, true))), (((34389, 110, 13, 16, true), (34400, 37, 9, 21, false)), ((34401, 109, 8, 18, false), (34404, 41, 15, 21, true)))), ((((34405, 110, 15, 4, true), (34406, 47, 9, 18, true)), ((34628, 80, 16, 16, false), (34660, 102, 15, 17, false))), (((34661, 140, 12, 23, false), (34662, 112, 9, 16, true)), ((34678, 145, 8, 21, false), (34679, 156, 0, 18, false)))))), ((((((34816, 2, 18, 16, true), (34880, 7, 22, 9, true)), ((34882, 28, 21, 6, true), (34883, 79, 0, 22, false))), (((34884, 14, 16, 16, true), (34912, 21, 9, 21, false)), ((34913, 79, 6, 18, false), (34916, 33, 23, 6, true)))), ((((34917, 85, 0, 23, false), (34918, 50, 21, 0, true)), ((34928, 23, 9, 18, false), (34932, 81, 6, 22, false))), (((34934, 87, 6, 21, false), (34935, 92, 0, 18, false)), ((34944, 3, 18, 9, true), (34948, 9, 22, 0, true))))), (((((34950, 23, 21, 0, true), (34951, 77, 0, 18, false)), ((34952, 4, 18, 0, true), (51200, 6, 22, 22, false))), (((51232, 26, 21, 21, false), (51233, 96, 18, 20, false)), ((51234, 33, 11, 22, true), (51236, 39, 17, 11, true)))), ((((51237, 101, 4, 21, false), (51250, 99, 10, 21, false)), ((51251, 124, 1, 22, false), (51252, 85, 16, 11, true))), (((51254, 118, 7, 23, false), (51264, 12, 16, 23, true)), ((51266, 39, 17, 5, true), (51267, 85, 16, 5, true))))))), (((((((51268, 15, 16, 22, true), (51282, 101, 10, 21, false)), ((51296, 31, 11, 23, false), (51297, 101, 10, 19, false))), (((51298, 56, 11, 21, true), (51299, 118, 1, 23, false)), ((51300, 40, 17, 11, true), (51301, 106, 22, 7, true)))), ((((51302, 62, 23, 1, true), (51312, 35, 11, 22, false)), ((51314, 103, 10, 21, false), (51315, 126, 7, 22, false))), (((51316, 86, 16, 11, true), (51318, 120, 7, 23, false)), ((51319, 131, 1, 22, false), (51328, 8, 22, 21, true))))), (((((51330, 29, 21, 18, true), (51331, 81, 22, 4, true)), ((51332, 15, 22, 18, true), (51334, 35, 23, 4, true))), (((51335, 83, 4, 22, false), (51336, 10, 22, 18, true)), ((51586, 97, 20, 22, true), (51602, 110, 18, 18, true)))), ((((51776, 31, 17, 17, false), (51777, 101, 16, 13, false)), ((51778, 56, 9, 23, true), (51779, 118, 3, 17, false))), (((51780, 35, 17, 16, true), (51794, 118, 11, 11, false)), ((51795, 168, 0, 23, false), (51796, 103, 16, 15, true)))))), ((((((51797, 126, 13, 16, true), (51808, 53, 9, 23, false)), ((51809, 138, 9, 5, false), (51810, 58, 9, 23, true))), (((51811, 139, 9, 5, true), (51812, 58, 15, 17, true)), ((51813, 139, 15, 3, true), (51814, 67, 9, 22, true)))), ((((51826, 119, 11, 11, false), (51827, 169, 10, 10, false)), ((51828, 119, 9, 17, false), (51829, 169, 8, 16, false))), (((51830, 142, 9, 11, true), (51831, 173, 0, 23, false)), ((51840, 27, 21, 23, true), (51841, 97, 18, 22, true))))), (((((51842, 40, 21, 22, true), (51843, 103, 21, 5, true)), ((51844, 40, 23, 16, true), (51845, 103, 23, 3, true))), (((51846, 58, 21, 5, true), (51847, 116, 3, 23, false)), ((51848, 30, 21, 22, true), (51856, 55, 9, 23, false)))), ((((51857, 106, 4, 23, true), (51858, 106, 10, 21, true)), ((51859, 139, 18, 19, true), (51860, 106, 16, 15, true))), (((51861, 139, 19, 13, true), (51862, 139, 21, 7, true)), ((51863, 166, 0, 23, false), (51864, 98, 18, 23, true)))))))), ((((((((51865, 111, 18, 22, true), (51872, 38, 21, 21, true)), ((51873, 110, 20, 18, true), (51874, 45, 11, 21, true))), (((51875, 113, 10, 18, true), (51876, 62, 17, 9, true)), ((51877, 126, 21, 4, true), (51878, 67, 11, 18, true)))), ((((51879, 129, 21, 4, true), (51880, 42, 21, 21, true)), ((51881, 111, 20, 18, true), (51882, 48, 21, 18, true))), (((52036, 83, 16, 16, false), (52068, 116, 15, 17, false)), ((52069, 166, 12, 17, false), (52070, 129, 15, 16, true))))), (((((52086, 171, 15, 15, false), (52087, 182, 12, 16, false)), ((52096, 34, 17, 22, false), (52098, 100, 16, 21, false))), (((52099, 125, 13, 22, false), (52100, 86, 22, 16, true)), ((52102, 119, 13, 23, false), (52103, 129, 3, 22, false)))), ((((52104, 82, 22, 16, true), (52114, 134, 10, 23, true)), ((52128, 57, 17, 21, false), (52129, 134, 4, 23, true))), (((52130, 107, 11, 17, true), (52131, 143, 10, 22, true)), ((52132, 120, 15, 17, false), (52133, 169, 12, 23, false)))))), ((((((52134, 142, 11, 16, true), (52135, 171, 3, 21, false)), ((52136, 104, 21, 17, true), (52137, 141, 18, 23, true))), (((52138, 114, 21, 16, true), (52144, 66, 9, 22, false)), ((52146, 136, 10, 21, true), (52147, 153, 1, 21, true)))), ((((52148, 131, 9, 16, false), (52150, 173, 8, 17, false)), ((52151, 182, 0, 22, false), (52152, 128, 9, 22, false))), (((52154, 146, 20, 21, true), (52155, 157, 18, 18, true)), ((52224, 11, 16, 16, false), (52256, 37, 17, 9, false))))), (((((52257, 109, 16, 6, false), (52258, 50, 9, 16, true)), ((52274, 124, 17, 6, false), (52275, 160, 0, 16, false))), (((52352, 13, 22, 17, true), (52354, 41, 23, 3, true)), ((52355, 87, 22, 3, true), (52356, 18, 16, 17, true)))), ((((52358, 45, 23, 3, true), (52359, 90, 22, 3, true)), ((52360, 16, 22, 16, true), (52370, 110, 23, 6, true))), (((52384, 38, 23, 9, true), (52385, 110, 22, 6, true)), ((52386, 62, 11, 17, true), (52387, 126, 23, 0, true))))))), (((((((52388, 45, 17, 9, true), (52389, 113, 16, 6, true)), ((52390, 67, 17, 6, true), (52391, 129, 23, 0, true))), (((52392, 42, 23, 9, true), (52393, 111, 22, 6, true)), ((52394, 65, 21, 16, true), (52400, 51, 9, 22, false)))), ((((52402, 125, 23, 6, true), (52403, 161, 6, 22, false)), ((52404, 90, 16, 9, true), (52406, 129, 17, 6, true))), (((52407, 163, 0, 22, false), (52408, 88, 22, 9, true)), ((52410, 127, 23, 6, true), (52411, 162, 22, 0, true))))), (((((52416, 17, 16, 9, true), (52418, 47, 17, 0, true)), ((52419, 92, 16, 0, true), (52424, 19, 22, 9, true))), (((52426, 48, 23, 0, true), (52427, 93, 22, 0, true)), ((52428, 20, 16, 0, true), (59520, 22, 21, 21, false)))), ((((59521, 80, 18, 18, false), (59524, 34, 23, 18, true)), ((59525, 86, 18, 22, false), (59526, 51, 21, 18, true))), (((59527, 90, 4, 21, false), (59528, 24, 21, 18, true)), ((59780, 100, 22, 22, false), (59781, 119, 19, 19, false)))))), ((((((59782, 125, 19, 18, false), (59783, 129, 5, 18, false)), ((59784, 82, 18, 22, true), (59798, 161, 18, 18, false))), (((59799, 163, 4, 18, false), (59800, 88, 18, 21, true)), ((59801, 93, 18, 18, true), (60544, 32, 23, 23, false)))), ((((60545, 102, 22, 19, false), (60546, 57, 21, 22, true)), ((60547, 120, 23, 5, true), (60548, 44, 17, 23, true))), (((60549, 107, 22, 19, true), (60550, 63, 23, 19, true)), ((60551, 122, 5, 23, false), (60552, 36, 23, 22, true))))), (((((60562, 134, 11, 11, false), (60563, 169, 19, 19, false)), ((60564, 107, 16, 21, true), (60565, 142, 16, 20, true))), (((60566, 143, 17, 10, true), (60567, 171, 4, 22, false)), ((60568, 104, 22, 21, true), (60569, 127, 19, 22, true)))), ((((60570, 141, 21, 11, true), (60576, 54, 21, 23, false)), ((60577, 140, 21, 5, false), (60578, 63, 11, 23, true))), (((60579, 143, 21, 5, true), (60580, 63, 17, 21, true)), ((60581, 143, 23, 4, true), (60582, 73, 9, 23, true))))))))), (((((((((60583, 151, 21, 5, true), (60584, 59, 21, 23, true)), ((60585, 141, 21, 5, true), (60586, 68, 21, 22, true))), (((60594, 135, 11, 11, false), (60595, 176, 7, 23, false)), ((60596, 122, 11, 17, false), (60597, 171, 10, 16, false)))), ((((60598, 151, 15, 11, true), (60599, 178, 1, 23, false)), ((60600, 121, 23, 11, true), (60601, 170, 19, 21, true))), (((60602, 144, 21, 11, true), (60603, 177, 23, 1, true)), ((60608, 43, 17, 21, true), (60609, 112, 16, 18, true))))), (((((60610, 66, 17, 18, true), (60611, 131, 17, 4, true)), ((60616, 46, 23, 21, true), (60617, 114, 22, 18, true))), (((60618, 68, 23, 18, true), (60619, 132, 23, 4, true)), ((60620, 49, 17, 18, true), (60804, 105, 16, 23, false)))), ((((60805, 135, 22, 22, false), (60806, 135, 16, 23, false)), ((60807, 151, 3, 23, false), (60808, 89, 16, 23, false))), (((60822, 176, 15, 15, false), (60823, 178, 5, 19, false)), ((60824, 121, 19, 23, true), (60825, 132, 19, 22, true)))))), ((((((60836, 135, 17, 17, false), (60837, 176, 13, 21, false)), ((60838, 151, 9, 17, true), (60839, 178, 3, 21, false))), (((60840, 121, 21, 17, true), (60841, 170, 18, 23, true)), ((60842, 132, 21, 16, true), (60854, 178, 9, 15, false)))), ((((60855, 187, 0, 23, false), (60856, 150, 9, 23, false)), ((60857, 174, 18, 23, true), (60858, 174, 20, 17, true))), (((60859, 184, 18, 22, true), (60864, 61, 17, 17, false)), ((60865, 136, 23, 3, false), (60866, 136, 17, 9, false))))), (((((60867, 173, 16, 5, true), (60872, 108, 22, 23, true)), ((60873, 144, 22, 22, true), (60874, 144, 23, 16, true))), (((60875, 174, 22, 5, true), (60876, 115, 16, 22, true)), ((60880, 71, 21, 16, false), (60881, 148, 3, 21, true)))), ((((60882, 153, 9, 9, false), (60883, 182, 3, 18, true)), ((60888, 137, 22, 21, true), (60889, 154, 19, 21, true))), (((60890, 177, 21, 9, true), (60891, 184, 19, 18, true)), ((60892, 147, 16, 21, true), (60893, 158, 16, 18, true))))))), (((((((61064, 52, 21, 16, true), (61080, 128, 17, 18, false)), ((61081, 162, 18, 16, true), (61120, 60, 17, 17, false))), (((61121, 145, 17, 3, false), (61122, 71, 9, 17, true)), ((61123, 153, 17, 3, true), (61128, 64, 23, 17, true)))), ((((61129, 146, 23, 3, true), (61130, 74, 21, 17, true)), ((61131, 154, 23, 3, true), (61132, 69, 17, 16, true))), (((61138, 148, 9, 9, false), (61139, 182, 9, 6, false)), ((61144, 137, 23, 9, true), (61145, 177, 19, 17, true))))), (((((61146, 154, 21, 9, true), (61147, 184, 21, 6, true)), ((61148, 147, 17, 9, true), (61149, 181, 16, 16, true))), (((61152, 70, 9, 9, false), (61153, 156, 9, 0, false)), ((61160, 72, 21, 9, true), (61161, 157, 21, 0, true)))), ((((61164, 75, 17, 9, true), (61165, 158, 17, 0, true)), ((61166, 76, 9, 0, true), (63624, 78, 18, 18, false))), (((64648, 84, 22, 22, false), (64680, 117, 21, 23, false)), ((64681, 167, 18, 23, false), (64682, 130, 21, 22, true)))))), ((((((64698, 172, 21, 21, false), (64699, 183, 18, 22, false)), ((64712, 91, 22, 21, true), (64714, 130, 23, 18, true))), (((64715, 164, 18, 22, false), (64716, 94, 16, 18, true)), ((65224, 123, 23, 23, false), (65225, 172, 22, 22, false)))), ((((65226, 152, 21, 23, true), (65227, 179, 19, 23, false)), ((65228, 133, 17, 22, true), (65242, 179, 21, 21, false))), (((65243, 188, 18, 23, false), (65244, 175, 16, 23, true)), ((65245, 185, 16, 22, true), (65256, 149, 21, 21, false))))), (((((65257, 183, 21, 18, false), (65260, 155, 17, 21, true)), ((65261, 185, 17, 18, true), (65262, 159, 9, 18, true))), (((65484, 165, 16, 16, false), (65516, 180, 17, 17, false)), ((65517, 189, 16, 17, false), (65518, 186, 9, 16, true)))), ((((65534, 190, 9, 9, false), (65535, 191, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))))))), ((((((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))), ((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))))), (((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))), ((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))))), ((((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))), ((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))))), (((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))), ((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))))))), (((((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))), ((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))))), (((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))), ((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))))), ((((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))), ((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))))), (((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false)))), ((((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))), (((0, 0, 0, 0, false), (0, 0, 0, 0, false)), ((0, 0, 0, 0, false), (0, 0, 0, 0, false))))))))))

set_option maxHeartbeats 0 in
def normIdx (m : ℕ) : ℕ :=
  (if m < 52385 then (if m < 51795 then (if m < 34948 then (if m < 34404 then (if m < 33860 then (if m < 33826 then (if m < 33792 then (if m < 32768 then 0 else 1) else (if m < 33824 then 2 else (if m < 33825 then 3 else 4))) else (if m < 33856 then (if m < 33842 then 5 else (if m < 33843 then 6 else 7)) else (if m < 33858 then 8 else (if m < 33859 then 9 else 10)))) else (if m < 34386 then (if m < 34370 then (if m < 34368 then 11 else (if m < 34369 then 12 else 13)) else (if m < 34371 then 14 else (if m < 34372 then 15 else 16))) else (if m < 34389 then (if m < 34387 then 17 else (if m < 34388 then 18 else 19)) else (if m < 34400 then 20 else (if m < 34401 then 21 else 22))))) else (if m < 34883 then (if m < 34662 then (if m < 34628 then (if m < 34405 then 23 else (if m < 34406 then 24 else 25)) else (if m < 34660 then 26 else (if m < 34661 then 27 else 28))) else (if m < 34816 then (if m < 34678 then 29 else (if m < 34679 then 30 else 31)) else (if m < 34880 then 32 else (if m < 34882 then 33 else 34)))) else (if m < 34918 then (if m < 34913 then (if m < 34884 then 35 else (if m < 34912 then 36 else 37)) else (if m < 34916 then 38 else (if m < 34917 then 39 else 40))) else (if m < 34934 then (if m < 34928 then 41 else (if m < 34932 then 42 else 43)) else (if m < 34935 then 44 else (if m < 34944 then 45 else 46)))))) else (if m < 51300 then (if m < 51251 then (if m < 51232 then (if m < 34951 then (if m < 34950 then 47 else 48) else (if m < 34952 then 49 else (if m < 51200 then 50 else 51))) else (if m < 51236 then (if m < 51233 then 52 else (if m < 51234 then 53 else 54)) else (if m < 51237 then 55 else (if m < 51250 then 56 else 57)))) else (if m < 51268 then (if m < 51264 then (if m < 51252 then 58 else (if m < 51254 then 59 else 60)) else (if m < 51266 then 61 else (if m < 51267 then 62 else 63))) else (if m < 51297 then (if m < 51282 then 64 else (if m < 51296 then 65 else 66)) else (if m < 51298 then 67 else (if m < 51299 then 68 else 69))))) else (if m < 51332 then (if m < 51316 then (if m < 51312 then (if m < 51301 then 70 else (if m < 51302 then 71 else 72)) else (if m < 51314 then 73 else (if m < 51315 then 74 else 75))) else (if m < 51328 then (if m < 51318 then 76 else (if m < 51319 then 77 else 78)) else (if m < 51330 then 79 else (if m < 51331 then 80 else 81)))) else (if m < 51776 then (if m < 51336 then (if m < 51334 then 82 else (if m < 51335 then 83 else 84)) else (if m < 51586 then 85 else (if m < 51602 then 86 else 87))) else (if m < 51779 then (if m < 51777 then 88 else (if m < 51778 then 89 else 90)) else (if m < 51780 then 91 else (if m < 51794 then 92 else 93))))))) else (if m < 52068 then (if m < 51847 then (if m < 51827 then (if m < 51810 then (if m < 51797 then (if m < 51796 then 94 else 95) else (if m < 51808 then 96 else (if m < 51809 then 97 else 98))) else (if m < 51813 then (if m < 51811 then 99 else (if m < 51812 then 100 else 101)) else (if m < 51814 then 102 else (if m < 51826 then 103 else 104)))) else (if m < 51841 then (if m < 51830 then (if m < 51828 then 105 else (if m < 51829 then 106 else 107)) else (if m < 51831 then 108 else (if m < 51840 then 109 else 110))) else (if m < 51844 then (if m < 51842 then 111 else (if m < 51843 then 112 else 113)) else (if m < 51845 then 114 else (if m < 51846 then 115 else 116))))) else (if m < 51872 then (if m < 51860 then (if m < 51857 then (if m < 51848 then 117 else (if m < 51856 then 118 else 119)) else (if m < 51858 then 120 else (if m < 51859 then 121 else 122))) else (if m < 51863 then (if m < 51861 then 123 else (if m < 51862 then 124 else 125)) else (if m < 51864 then 126 else (if m < 51865 then 127 else 128)))) else (if m < 51878 then (if m < 51875 then (if m < 51873 then 129 else (if m < 51874 then 130 else 131)) else (if m < 51876 then 132 else (if m < 51877 then 133 else 134))) else (if m < 51881 then (if m < 51879 then 135 else (if m < 51880 then 136 else 137)) else (if m < 51882 then 138 else (if m < 52036 then 139 else 140)))))) else (if m < 52144 then (if m < 52114 then (if m < 52098 then (if m < 52086 then (if m < 52069 then 141 else (if m < 52070 then 142 else 143)) else (if m < 52087 then 144 else (if m < 52096 then 145 else 146))) else (if m < 52102 then (if m < 52099 then 147 else (if m < 52100 then 148 else 149)) else (if m < 52103 then 150 else (if m < 52104 then 151 else 152)))) else (if m < 52133 then (if m < 52130 then (if m < 52128 then 153 else (if m < 52129 then 154 else 155)) else (if m < 52131 then 156 else (if m < 52132 then 157 else 158))) else (if m < 52136 then (if m < 52134 then 159 else (if m < 52135 then 160 else 161)) else (if m < 52137 then 162 else (if m < 52138 then 163 else 164))))) else (if m < 52258 then (if m < 52152 then (if m < 52148 then (if m < 52146 then 165 else (if m < 52147 then 166 else 167)) else (if m < 52150 then 168 else (if m < 52151 then 169 else 170))) else (if m < 52224 then (if m < 52154 then 171 else (if m < 52155 then 172 else 173)) else (if m < 52256 then 174 else (if m < 52257 then 175 else 176)))) else (if m < 52356 then (if m < 52352 then (if m < 52274 then 177 else (if m < 52275 then 178 else 179)) else (if m < 52354 then 180 else (if m < 52355 then 181 else 182))) else (if m < 52360 then (if m < 52358 then 183 else (if m < 52359 then 184 else 185)) else (if m < 52370 then 186 else (if m < 52384 then 187 else 188)))))))) else (if m < 60808 then (if m < 60549 then (if m < 52426 then (if m < 52402 then (if m < 52390 then (if m < 52387 then (if m < 52386 then 189 else 190) else (if m < 52388 then 191 else (if m < 52389 then 192 else 193))) else (if m < 52393 then (if m < 52391 then 194 else (if m < 52392 then 195 else 196)) else (if m < 52394 then 197 else (if m < 52400 then 198 else 199)))) else (if m < 52410 then (if m < 52406 then (if m < 52403 then 200 else (if m < 52404 then 201 else 202)) else (if m < 52407 then 203 else (if m < 52408 then 204 else 205))) else (if m < 52418 then (if m < 52411 then 206 else (if m < 52416 then 207 else 208)) else (if m < 52419 then 209 else (if m < 52424 then 210 else 211))))) else (if m < 59782 then (if m < 59525 then (if m < 59520 then (if m < 52427 then 212 else (if m < 52428 then 213 else 214)) else (if m < 59521 then 215 else (if m < 59524 then 216 else 217))) else (if m < 59528 then (if m < 59526 then 218 else (if m < 59527 then 219 else 220)) else (if m < 59780 then 221 else (if m < 59781 then 222 else 223)))) else (if m < 59801 then (if m < 59798 then (if m < 59783 then 224 else (if m < 59784 then 225 else 226)) else (if m < 59799 then 227 else (if m < 59800 then 228 else 229))) else (if m < 60546 then (if m < 60544 then 230 else (if m < 60545 then 231 else 232)) else (if m < 60547 then 233 else (if m < 60548 then 234 else 235)))))) else (if m < 60586 then (if m < 60569 then (if m < 60563 then (if m < 60551 then (if m < 60550 then 236 else 237) else (if m < 60552 then 238 else (if m < 60562 then 239 else 240))) else (if m < 60566 then (if m < 60564 then 241 else (if m < 60565 then 242 else 243)) else (if m < 60567 then 244 else (if m < 60568 then 245 else 246)))) else (if m < 60580 then (if m < 60577 then (if m < 60570 then 247 else (if m < 60576 then 248 else 249)) else (if m < 60578 then 250 else (if m < 60579 then 251 else 252))) else (if m < 60583 then (if m < 60581 then 253 else (if m < 60582 then 254 else 255)) else (if m < 60584 then 256 else (if m < 60585 then 257 else 258))))) else (if m < 60609 then (if m < 60599 then (if m < 60596 then (if m < 60594 then 259 else (if m < 60595 then 260 else 261)) else (if m < 60597 then 262 else (if m < 60598 then 263 else 264))) else (if m < 60602 then (if m < 60600 then 265 else (if m < 60601 then 266 else 267)) else (if m < 60603 then 268 else (if m < 60608 then 269 else 270)))) else (if m < 60619 then (if m < 60616 then (if m < 60610 then 271 else (if m < 60611 then 272 else 273)) else (if m < 60617 then 274 else (if m < 60618 then 275 else 276))) else (if m < 60805 then (if m < 60620 then 277 else (if m < 60804 then 278 else 279)) else (if m < 60806 then 280 else (if m < 60807 then 281 else 282))))))) else (if m < 61131 then (if m < 60873 then (if m < 60842 then (if m < 60836 then (if m < 60823 then (if m < 60822 then 283 else 284) else (if m < 60824 then 285 else (if m < 60825 then 286 else 287))) else (if m < 60839 then (if m < 60837 then 288 else (if m < 60838 then 289 else 290)) else (if m < 60840 then 291 else (if m < 60841 then 292 else 293)))) else (if m < 60859 then (if m < 60856 then (if m < 60854 then 294 else (if m < 60855 then 295 else 296)) else (if m < 60857 then 297 else (if m < 60858 then 298 else 299))) else (if m < 60866 then (if m < 60864 then 300 else (if m < 60865 then 301 else 302)) else (if m < 60867 then 303 else (if m < 60872 then 304 else 305))))) else (if m < 60892 then (if m < 60882 then (if m < 60876 then (if m < 60874 then 306 else (if m < 60875 then 307 else 308)) else (if m < 60880 then 309 else (if m < 60881 then 310 else 311))) else (if m < 60889 then (if m < 60883 then 312 else (if m < 60888 then 313 else 314)) else (if m < 60890 then 315 else (if m < 60891 then 316 else 317)))) else (if m < 61121 then (if m < 61080 then (if m < 60893 then 318 else (if m < 61064 then 319 else 320)) else (if m < 61081 then 321 else (if m < 61120 then 322 else 323))) else (if m < 61128 then (if m < 61122 then 324 else (if m < 61123 then 325 else 326)) else (if m < 61129 then 327 else (if m < 61130 then 328 else 329)))))) else (if m < 64712 then (if m < 61160 then (if m < 61146 then (if m < 61139 then (if m < 61132 then 330 else (if m < 61138 then 331 else 332)) else (if m < 61144 then 333 else (if m < 61145 then 334 else 335))) else (if m < 61149 then (if m < 61147 then 336 else (if m < 61148 then 337 else 338)) else (if m < 61152 then 339 else (if m < 61153 then 340 else 341)))) else (if m < 64648 then (if m < 61165 then (if m < 61161 then 342 else (if m < 61164 then 343 else 344)) else (if m < 61166 then 345 else (if m < 63624 then 346 else 347))) else (if m < 64682 then (if m < 64680 then 348 else (if m < 64681 then 349 else 350)) else (if m < 64698 then 351 else (if m < 64699 then 352 else 353))))) else (if m < 65245 then (if m < 65226 then (if m < 64716 then (if m < 64714 then 354 else (if m < 64715 then 355 else 356)) else (if m < 65224 then 357 else (if m < 65225 then 358 else 359))) else (if m < 65242 then (if m < 65227 then 360 else (if m < 65228 then 361 else 362)) else (if m < 65243 then 363 else (if m < 65244 then 364 else 365)))) else (if m < 65484 then (if m < 65260 then (if m < 65256 then 366 else (if m < 65257 then 367 else 368)) else (if m < 65261 then 369 else (if m < 65262 then 370 else 371))) else (if m < 65518 then (if m < 65516 then 372 else (if m < 65517 then 373 else 374)) else (if m < 65534 then 375 else (if m < 65535 then 376 else 377)))))))))

def checkSortedRange (lo cnt : ℕ) : Bool :=
  (List.range cnt).all fun off =>
  let r0 := lo + off
  (List.range (16 - r0)).all fun d1 =>
  let r1 := r0 + d1
  (List.range (16 - r1)).all fun d2 =>
  let r2 := r1 + d2
  (List.range (16 - r2)).all fun d3 =>
  let r3 := r2 + d3
  let m := normNat (r0 + 16 * (r1 + 16 * (r2 + 16 * r3)))
  decide ((btGet normBT (normIdx m)).1 = m)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem sorted_0 : checkSortedRange 0 4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem sorted_1 : checkSortedRange 4 4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem sorted_2 : checkSortedRange 8 4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem sorted_3 : checkSortedRange 12 4 = true := by decide +kernel

theorem sorted_in_normBT (r0 r1 r2 r3 : ℕ)
    (h01 : r0 ≤ r1) (h12 : r1 ≤ r2) (h23 : r2 ≤ r3) (h3 : r3 < 16) :
    let m := normNat (r0 + 16 * (r1 + 16 * (r2 + 16 * r3)))
    (btGet normBT (normIdx m)).1 = m := by
  have hget : ∀ lo cnt, checkSortedRange lo cnt = true → lo ≤ r0 → r0 < lo + cnt →
      (btGet normBT (normIdx (normNat (r0 + 16 * (r1 + 16 * (r2 + 16 * r3)))))).1 =
      normNat (r0 + 16 * (r1 + 16 * (r2 + 16 * r3))) := by
    intro lo cnt h hlo hhi
    unfold checkSortedRange at h
    have h0 := List.all_eq_true.1 h (r0 - lo) (List.mem_range.2 (by omega))
    simp only [show lo + (r0 - lo) = r0 by omega] at h0
    have h1 := List.all_eq_true.1 h0 (r1 - r0) (List.mem_range.2 (by omega))
    have h2 := List.all_eq_true.1 h1 (r2 - r1) (List.mem_range.2 (by omega))
    have h3' := List.all_eq_true.1 h2 (r3 - r2) (List.mem_range.2 (by omega))
    simp only [show r0 + (r1 - r0) = r1 by omega, show r1 + (r2 - r1) = r2 by omega,
      show r2 + (r3 - r2) = r3 by omega, decide_eq_true_eq] at h3'
    exact h3'
  by_cases c0 : r0 < 4
  · exact hget 0 4 sorted_0 (by omega) c0
  · by_cases c1 : r0 < 8
    · exact hget 4 4 sorted_1 (by omega) c1
    · by_cases c2 : r0 < 12
      · exact hget 8 4 sorted_2 (by omega) c2
      · exact hget 12 4 sorted_3 (by omega) (by omega)

def checkNormEntry (e : ℕ × ℕ × ℕ × ℕ × Bool) : Bool :=
  decide (applyPermNat e.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2 = (btGet atlasBT e.2.1).2.1)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem normBT_ok : btAll checkNormEntry normBT = true := by decide +kernel

def monoGateOK (g : Gate) : Bool :=
  match g.op with
  | .and | .or => decide (g.inputs.length ≤ 2)
  | _ => false

theorem monoGate_sound (g : Gate) (h : monoGateOK g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [monoGateOK]

def evalPacked16 (C : Circuit) : ℕ :=
  let init : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]
  let ws := C.gates.foldl (fun w g =>
    let v := match g.op with
      | .and => g.inputs.foldr (fun i acc => (w.getD i 0) &&& acc) 65535
      | .or => g.inputs.foldr (fun i acc => (w.getD i 0) ||| acc) 0
      | _ => 0
    w ++ [v]) init
  ws.getD C.output 0

theorem evalPacked16_bit (C : Circuit) (hm : C.gates.all monoGateOK = true) (u v : Fin 4) :
    (evalPacked16 C).testBit (4 * u.val + v.val) = C.eval (oneEach u v) := by
  set r := 4 * u.val + v.val
  have hr : r < 16 := by omega
  have h65535 : (65535 : ℕ).testBit r = true := by
    have h : (65535 : ℕ) = 2 ^ 16 - 1 := rfl
    rw [h, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hr
  have hstep : ∀ (gs : List Gate) (w : List ℕ), gs.all monoGateOK = true →
      (gs.foldl (fun w g =>
        let v := match g.op with
          | .and => g.inputs.foldr (fun i acc => (w.getD i 0) &&& acc) 65535
          | .or => g.inputs.foldr (fun i acc => (w.getD i 0) ||| acc) 0
          | _ => 0
        w ++ [v]) w).map (·.testBit r) =
      wiresFrom gs (w.map (·.testBit r)) := by
    intro gs
    induction gs with
    | nil => intro w _; rfl
    | cons g gs ih =>
      intro w hall
      simp only [List.all_cons, Bool.and_eq_true] at hall
      simp only [List.foldl_cons, wiresFrom]
      rw [ih _ hall.2]
      have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
        intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases w[i]? with | none => simp | some x => rfl
      have hval : (match g.op with
          | .and => g.inputs.foldr (fun i acc => (w.getD i 0) &&& acc) 65535
          | .or => g.inputs.foldr (fun i acc => (w.getD i 0) ||| acc) 0
          | _ => 0).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
        rcases g with ⟨op, ins⟩
        cases op with
        | and =>
          clear hall
          simp only [GateOp.eval]
          induction ins with
          | nil => simp [h65535]
          | cons i l ihl => simp only [List.foldr_cons, List.map_cons, List.all_cons, id_eq, Nat.testBit_and, hgd, ihl]
        | or =>
          clear hall
          simp only [GateOp.eval]
          induction ins with
          | nil => simp
          | cons i l ihl => simp only [List.foldr_cons, List.map_cons, List.any_cons, id_eq, Nat.testBit_or, hgd, ihl]
        | not => simp [monoGateOK] at hall
        | mod _ => simp [monoGateOK] at hall
        | maj => simp [monoGateOK] at hall
      rw [List.map_append, List.map_singleton, hval]; rfl
  have hinit : ([15, 240, 3840, 61440, 4369, 8738, 17476, 34952] : List ℕ).map (·.testBit r) = oneEach u v := by
    have hcheck : ∀ a b : Fin 4,
        ([15, 240, 3840, 61440, 4369, 8738, 17476, 34952] : List ℕ).map (·.testBit (4 * a.val + b.val)) = oneEach a b := by
      decide +kernel
    exact hcheck u v
  dsimp only [evalPacked16, Circuit.eval, Circuit.wires]
  have heq := hstep C.gates [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] hm
  rw [hinit] at heq
  set L := C.gates.foldl (fun w g =>
      let v := match g.op with
        | .and => g.inputs.foldr (fun i acc => (w.getD i 0) &&& acc) 65535
        | .or => g.inputs.foldr (fun i acc => (w.getD i 0) ||| acc) 0
        | _ => 0
      w ++ [v]) [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]
  have hgd : (L.getD C.output 0).testBit r = (wiresFrom C.gates (oneEach u v)).getD C.output false := by
    have h1 := congrArg (fun l => l.getD C.output false) heq
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map] at h1
    rw [List.getD_eq_getElem?_getD]
    cases hget : L[C.output]? with
    | none => rw [hget] at h1; simpa using h1
    | some val => rw [hget] at h1; simpa using h1
  exact hgd

def checkAtlasCirc (entry : Circuit × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  entry.1.gates.all monoGateOK && decide (entry.1.size ≤ entry.2.2.1) && decide (evalPacked16 entry.1 = entry.2.1)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem atlasCircs_ok : btAll checkAtlasCirc atlasBT = true := by decide +kernel

def checkAtlasPlan (entry : Circuit × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  let m := entry.2.1
  let b := entry.2.2.1
  let mode := entry.2.2.2.1
  if mode = 0 then
    decide (b ≤ 3)
  else if mode = 1 then
    let rdel := entry.2.2.2.2.1
    let cdel := entry.2.2.2.2.2.1
    let l3 := entry.2.2.2.2.2.2.1
    let g3 := entry.2.2.2.2.2.2.2
    decide (rdel < 4) && decide (cdel < 4) && decide (g3 ≠ 511) &&
    decide (subMask3 m (Fin.ofNat 4 rdel) (Fin.ofNat 4 cdel) l3 = g3) &&
    bans3.any (fun p => decide (p.1 = g3 ∧ b ≤ p.2 + 4))
  else
    let pidx := entry.2.2.2.2.1
    let tbl := btGet lvl2PlansBT pidx
    let distR := (List.range 4).all fun u1 => (List.range 4).all fun u2 =>
      decide (u1 = u2) || (List.range 4).any fun v => matOf m (Fin.ofNat 4 u1) (Fin.ofNat 4 v) != matOf m (Fin.ofNat 4 u2) (Fin.ofNat 4 v)
    let distC := (List.range 4).all fun v1 => (List.range 4).all fun v2 =>
      decide (v1 = v2) || (List.range 4).any fun u => matOf m (Fin.ofNat 4 u) (Fin.ofNat 4 v1) != matOf m (Fin.ofNat 4 u) (Fin.ofNat 4 v2)
    distR && distC &&
    (List.range 4).all fun rBad => (List.range 4).all fun cBad =>
      let e := btGet tbl (4 * rBad + cBad)
      decide (e.1 < 4) && decide (e.2.1 < 4) && decide (e.1 ≠ rBad) && decide (e.2.1 ≠ cBad) &&
      decide (e.2.2.2 ≠ 0) && decide (e.2.2.2 ≠ 511) &&
      decide (subMask3 m (Fin.ofNat 4 e.1) (Fin.ofNat 4 e.2.1) e.2.2.1 = e.2.2.2) &&
      bans3.any (fun p => decide (p.1 = e.2.2.2 ∧ b ≤ p.2 + 6))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem atlasPlans_ok : btAll checkAtlasPlan atlasBT = true := by decide +kernel

theorem atlas_goal (s : ℕ) (i : ℕ) :
    GoalProp s (matOf (btGet atlasBT i).2.1) := by
  set entry := btGet atlasBT i
  set m := entry.2.1
  set b := entry.2.2.1
  intro C hfan hsize hrep
  by_cases hle : b ≤ s + 3
  · have hc := btAll_get checkAtlasCirc atlasBT i atlasCircs_ok
    unfold checkAtlasCirc at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hm, hsz⟩, hev⟩ := hc
    refine ⟨entry.1, fun g hg => monoGate_sound g (List.all_eq_true.1 hm g hg), le_trans hsz hle, fun u v => ?_⟩
    rw [← evalPacked16_bit _ hm u v, hev]
    rfl
  · exfalso
    have hplan := btAll_get checkAtlasPlan atlasBT i atlasPlans_ok
    unfold checkAtlasPlan at hplan
    dsimp only at hplan
    change (if entry.2.2.2.1 = 0 then _ else if entry.2.2.2.1 = 1 then _ else _) = true at hplan
    by_cases hm0 : entry.2.2.2.1 = 0
    · simp only [hm0, ↓reduceIte] at hplan
      have hb3 : b ≤ 3 := of_decide_eq_true hplan
      omega
    · simp only [hm0, ↓reduceIte] at hplan
      by_cases hm1 : entry.2.2.2.1 = 1
      · simp only [hm1, ↓reduceIte] at hplan
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hplan
        obtain ⟨⟨⟨⟨hrlt, hclt⟩, hg511⟩, hsub⟩, hban⟩ := hplan
        obtain ⟨p, hp, hpeq⟩ := List.any_eq_true.1 hban
        obtain ⟨hp1, hp2⟩ := of_decide_eq_true hpeq
        change b ≤ p.2 + 4 at hp2
        have hforb : Forbidden entry.2.2.2.2.2.2.2 p.2 := hp1 ▸ certified_bans3 p hp
        exact level1_contra m C hfan hrep
          (Fin.ofNat 4 entry.2.2.2.2.1) (Fin.ofNat 4 entry.2.2.2.2.2.1)
          entry.2.2.2.2.2.2.1 entry.2.2.2.2.2.2.2 p.2 hsub hg511 hforb (by omega)
      · simp only [hm1, ↓reduceIte] at hplan
        simp only [Bool.and_eq_true] at hplan
        obtain ⟨⟨hdistR, hdistC⟩, hall⟩ := hplan
        have hR : ∀ u1 u2 : Fin 4, u1 ≠ u2 → ∃ v : Fin 4, matOf m u1 v ≠ matOf m u2 v := by
          intro u1 u2 hne
          have h1 := List.all_eq_true.1 (List.all_eq_true.1 hdistR u1.val (List.mem_range.2 u1.isLt)) u2.val (List.mem_range.2 u2.isLt)
          simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
          have hne_val : u1.val ≠ u2.val := fun e => hne (Fin.ext e)
          obtain ⟨v, hv, hneq⟩ := List.any_eq_true.1 (h1.resolve_left hne_val)
          have hvlt : v < 4 := List.mem_range.1 hv
          refine ⟨⟨v, hvlt⟩, ?_⟩
          rw [fin_ofNat_eq u1, fin_ofNat_eq u2, fin_ofNat_eq ⟨v, hvlt⟩] at hneq
          exact bne_iff_ne.1 hneq
        have hC : ∀ v1 v2 : Fin 4, v1 ≠ v2 → ∃ u : Fin 4, matOf m u v1 ≠ matOf m u v2 := by
          intro v1 v2 hne
          have h1 := List.all_eq_true.1 (List.all_eq_true.1 hdistC v1.val (List.mem_range.2 v1.isLt)) v2.val (List.mem_range.2 v2.isLt)
          simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
          have hne_val : v1.val ≠ v2.val := fun e => hne (Fin.ext e)
          obtain ⟨u, hu, hneq⟩ := List.any_eq_true.1 (h1.resolve_left hne_val)
          have hult : u < 4 := List.mem_range.1 hu
          refine ⟨⟨u, hult⟩, ?_⟩
          rw [fin_ofNat_eq ⟨u, hult⟩, fin_ofNat_eq v1, fin_ofNat_eq v2] at hneq
          exact bne_iff_ne.1 hneq
        obtain ⟨rBad, hrBad⟩ := exists_inCone_rows m hR C hrep
        obtain ⟨cBad, hcBad⟩ := exists_inCone_cols m hC C hrep
        have hent := List.all_eq_true.1 (List.all_eq_true.1 hall rBad.val (List.mem_range.2 rBad.isLt)) cBad.val (List.mem_range.2 cBad.isLt)
        set e := btGet (btGet lvl2PlansBT entry.2.2.2.2.1) (4 * rBad.val + cBad.val)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hent
        obtain ⟨⟨⟨⟨⟨⟨⟨hrlt, hclt⟩, hrne⟩, hcne⟩, hg0⟩, hg511⟩, hsub⟩, hban⟩ := hent
        obtain ⟨p, hp, hpeq⟩ := List.any_eq_true.1 hban
        obtain ⟨hp1, hp2⟩ := of_decide_eq_true hpeq
        change b ≤ p.2 + 6 at hp2
        have hforb : Forbidden e.2.2.2 p.2 := hp1 ▸ certified_bans3 p hp
        have hrdel_eq : (Fin.ofNat 4 e.1).val = e.1 := by simp [Nat.mod_eq_of_lt hrlt]
        have hcdel_eq : (Fin.ofNat 4 e.2.1).val = e.2.1 := by simp [Nat.mod_eq_of_lt hclt]
        have hincR : InCone C (Fin.ofNat 4 e.1).val := hrBad (Fin.ofNat 4 e.1) (fun h => hrne (by rw [← hrdel_eq, h]))
        have hincC : InCone C (4 + (Fin.ofNat 4 e.2.1).val) := hcBad (Fin.ofNat 4 e.2.1) (fun h => hcne (by rw [← hcdel_eq, h]))
        exact level2_contra m C hfan hrep (Fin.ofNat 4 e.1) (Fin.ofNat 4 e.2.1) hincR hincC
          e.2.2.1 e.2.2.2 p.2 hsub hg0 hg511 hforb (by omega)

theorem main_proof (s : ℕ) (A : Fin 4 → Fin 4 → Bool) : GoalProp s A := by
  apply goal_sortRowsA s A
  set A' := sortRowsA A
  rw [← matOf_enc4 A']
  apply goal_normNat s (enc4 A')
  obtain ⟨h01, h12, h23⟩ := sortRowsA_sorted A
  have h3lt := rowValA_lt A' 3
  have heq_m := sorted_in_normBT (rowValA A' 0) (rowValA A' 1) (rowValA A' 2) (rowValA A' 3) h01 h12 h23 h3lt
  change (btGet normBT (normIdx (normNat (enc4 A')))).1 = normNat (enc4 A') at heq_m
  set e := btGet normBT (normIdx (normNat (enc4 A')))
  have hval := of_decide_eq_true (btAll_get checkNormEntry normBT (normIdx (normNat (enc4 A'))) normBT_ok)
  apply goal_of_perm s (matOf (normNat (enc4 A')))
    (permFn e.2.2.1) (permFn e.2.2.2.1) (permInv e.2.2.1) (permInv e.2.2.2.1) e.2.2.2.2
    (perms4_bij e.2.2.1) (perms4_bij e.2.2.2.1)
  rw [← matOf_applyPermNat, ← heq_m, hval]
  exact atlas_goal s e.2.1

end PEqualNP.Outside.L_meta_25780

theorem PEqualNP.Outside.L_meta_25780 : ∀ (s : ℕ) (A : Fin 4 → Fin 4 → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s → PEqualNP.Represents.Represents A C → PEqualNP.Represents.RepSizeAtMost A (s + 3) :=
  fun s A => PEqualNP.Outside.L_meta_25780.main_proof s A
