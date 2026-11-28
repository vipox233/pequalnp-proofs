import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1195

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

def enc {k n : ℕ} (x : Fin k → Fin n → Bool) : List Bool :=
  (List.ofFn (fun j => List.ofFn (x j))).flatten ++ [false, true]

lemma flatten_ofFn_length {k n : ℕ} (x : Fin k → Fin n → Bool) :
    (List.ofFn (fun j => List.ofFn (x j))).flatten.length = k * n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn, ih]
    ring

lemma enc_length {k n : ℕ} (x : Fin k → Fin n → Bool) : (enc x).length = k * n + 2 := by
  rw [enc, List.length_append, flatten_ofFn_length]; rfl

lemma flatten_ofFn_getD {k n : ℕ} (x : Fin k → Fin n → Bool) (i : Fin k) (j : Fin n) :
    (List.ofFn (fun a => List.ofFn (x a))).flatten.getD (i.val * n + j.val) false = x i j := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.val_zero, zero_mul, zero_add]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [j.isLt])]
      simp [j.isLt]
    · intro i'
      have hge : (List.ofFn (x 0)).length ≤ i'.succ.val * n + j.val := by
        simp only [List.length_ofFn, Fin.val_succ]; nlinarith [i'.isLt, j.isLt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
      have hsub : i'.succ.val * n + j.val - (List.ofFn (x 0)).length = i'.val * n + j.val := by
        simp only [List.length_ofFn, Fin.val_succ]; ring_nf; omega
      rw [hsub, ← List.getD_eq_getElem?_getD]
      exact ih (fun a => x a.succ) i'

lemma enc_getD_bit {k n : ℕ} (x : Fin k → Fin n → Bool) (i : Fin k) (j : Fin n) :
    (enc x).getD (i.val * n + j.val) false = x i j := by
  have hlt : i.val * n + j.val < (List.ofFn (fun a => List.ofFn (x a))).flatten.length := by
    rw [flatten_ofFn_length]; nlinarith [i.isLt, j.isLt]
  rw [enc, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
  exact flatten_ofFn_getD x i j

lemma enc_getD_false {k n : ℕ} (x : Fin k → Fin n → Bool) :
    (enc x).getD (k * n) false = false := by
  have hlen : (List.ofFn (fun a => List.ofFn (x a))).flatten.length = k * n := flatten_ofFn_length x
  rw [enc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
  simp

lemma enc_getD_true {k n : ℕ} (x : Fin k → Fin n → Bool) :
    (enc x).getD (k * n + 1) false = true := by
  have hlen : (List.ofFn (fun a => List.ofFn (x a))).flatten.length = k * n := flatten_ofFn_length x
  rw [enc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
  have hsub : k * n + 1 - k * n = 1 := by omega
  rw [hsub]; rfl

def stepList (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma stepList_nil (w : List Bool) : stepList [] w = w := rfl

lemma stepList_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    stepList (g :: gs) w = stepList gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma stepList_append (gs1 gs2 : List Gate) (w : List Bool) :
    stepList (gs1 ++ gs2) w = stepList gs2 (stepList gs1 w) := by
  simp [stepList, List.foldl_append]

lemma stepList_length (gs : List Gate) (w : List Bool) :
    (stepList gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [stepList]
  | cons g gs ih =>
    rw [stepList_cons, ih, List.length_append]
    simp; omega

lemma stepList_prefix_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (stepList gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [stepList_cons, ih _ (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]

lemma stepList_last_getD (g : Gate) (w : List Bool) :
    (stepList [g] w).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [stepList_cons, stepList_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

def wireLe (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ i, u.getD i false = true → v.getD i false = true

lemma wireLe_refl (u : List Bool) : wireLe u u := ⟨rfl, fun _ h => h⟩

lemma wireLe_trans {u v w : List Bool} (h1 : wireLe u v) (h2 : wireLe v w) : wireLe u w :=
  ⟨h1.1.trans h2.1, fun i hi => h2.2 i (h1.2 i hi)⟩

lemma enc_wireLe {k n : ℕ} {x y : Fin k → Fin n → Bool}
    (hxy : ∀ i j, x i j = true → y i j = true) : wireLe (enc x) (enc y) := by
  refine ⟨by rw [enc_length, enc_length], fun w hw => ?_⟩
  by_cases h1 : w < k * n
  · have hnpos : 0 < n := by
      by_contra h0
      have : n = 0 := by omega
      subst this; simp at h1
    let i : Fin k := ⟨w / n, Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩
    let j : Fin n := ⟨w % n, Nat.mod_lt _ hnpos⟩
    have hw_eq : w = i.val * n + j.val := by
      simp only [i, j]; rw [mul_comm]; exact (Nat.div_add_mod w n).symm
    rw [hw_eq, enc_getD_bit] at hw ⊢
    exact hxy i j hw
  · by_cases h2 : w = k * n
    · rw [h2, enc_getD_false] at hw; cases hw
    · by_cases h3 : w = k * n + 1
      · rw [h3, enc_getD_true]
      · have hge : (enc x).length ≤ w := by rw [enc_length]; omega
        rw [List.getD_eq_default _ _ hge] at hw; cases hw

lemma step_mono_and_or (g : Gate) (hop : g.op = .and ∨ g.op = .or) {u v : List Bool} (huv : wireLe u v) :
    wireLe (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)])
           (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) := by
  have hval : g.op.eval (g.inputs.map fun i => u.getD i false) = true →
      g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
    intro h
    rcases hop with heq | heq <;> rw [heq] at h ⊢
    · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at h ⊢
      intro i hi; exact huv.2 i (h i hi)
    · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at h ⊢
      obtain ⟨i, hi, hti⟩ := h
      exact ⟨i, hi, huv.2 i hti⟩
  refine ⟨by simp [huv.1], fun i hi => ?_⟩
  by_cases hlt : i < u.length
  · have hltv : i < v.length := huv.1 ▸ hlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hltv]
    exact huv.2 i (by rwa [List.getD_eq_getElem?_getD])
  · by_cases heq : i = u.length
    · subst heq
      have h1 : (u ++ [g.op.eval (g.inputs.map fun j => u.getD j false)]).getD u.length false =
          g.op.eval (g.inputs.map fun j => u.getD j false) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      have h2 : (v ++ [g.op.eval (g.inputs.map fun j => v.getD j false)]).getD u.length false =
          g.op.eval (g.inputs.map fun j => v.getD j false) := by
        rw [huv.1, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      rw [h1] at hi; rw [h2]; exact hval hi
    · have hge : (u ++ [g.op.eval (g.inputs.map fun j => u.getD j false)]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hge] at hi; cases hi

lemma stepList_mono_noNot (gs : List Gate) (hno : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {u v : List Bool} (huv : wireLe u v) : wireLe (stepList gs u) (stepList gs v) := by
  induction gs generalizing u v with
  | nil => exact huv
  | cons g gs ih =>
    rw [stepList_cons, stepList_cons]
    exact ih (fun x hx => hno x (List.mem_cons_of_mem _ hx))
      (step_mono_and_or g (hno g (List.mem_cons_self ..)) huv)

lemma not_eval_anti (g : Gate) (hnot : g.op = .not) {u v : List Bool} (huv : wireLe u v) :
    g.op.eval (g.inputs.map fun i => u.getD i false) = false →
    g.op.eval (g.inputs.map fun i => v.getD i false) = false := by
  rw [hnot]
  cases h : g.inputs with
  | nil => simp [GateOp.eval]
  | cons i rest =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_false']
    exact huv.2 i

lemma split_first_not (gs : List Gate) (h : ∃ g ∈ gs, g.op = .not) :
    ∃ pre ng post, gs = pre ++ ng :: post ∧ ng.op = .not ∧ ∀ g ∈ pre, g.op ≠ .not := by
  induction gs with
  | nil => obtain ⟨_, hm, _⟩ := h; simp at hm
  | cons g rest ih =>
    by_cases hg : g.op = .not
    · exact ⟨[], g, rest, rfl, hg, by simp⟩
    · have hrest : ∃ x ∈ rest, x.op = .not := by
        obtain ⟨x, hx, hxo⟩ := h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (hg hxo).elim
        · exact ⟨x, hx, hxo⟩
      obtain ⟨pre, ng, post, heq, hngo, hpre⟩ := ih hrest
      exact ⟨g :: pre, ng, post, by simp [heq], hngo, fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hg
        · exact hpre x hx⟩

lemma wireLe_append_same {u v : List Bool} (huv : wireLe u v) (b : Bool) :
    wireLe (u ++ [b]) (v ++ [b]) := by
  refine ⟨by simp [huv.1], fun i hi => ?_⟩
  by_cases hlt : i < u.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (huv.1 ▸ hlt)]
    exact huv.2 i (by rwa [List.getD_eq_getElem?_getD])
  · by_cases heq : i = u.length
    · subst heq
      have h1 : (u ++ [b]).getD u.length false = b := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      have h2 : (v ++ [b]).getD u.length false = b := by
        rw [huv.1, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      rw [h1] at hi; rw [h2]; exact hi
    · have hge : (u ++ [b]).length ≤ i := by simp; omega
      rw [List.getD_eq_default _ _ hge] at hi; cases hi

lemma wireLe_chain {H : ℕ} {U : Fin (H + 1) → List Bool}
    (hstep : ∀ l : Fin H, wireLe (U l.castSucc) (U l.succ)) :
    ∀ a b : Fin (H + 1), a ≤ b → wireLe (U a) (U b) := by
  intro a b hab
  have hgen : ∀ d : ℕ, ∀ t : ℕ, (ht : t + d < H + 1) → wireLe (U ⟨t, by omega⟩) (U ⟨t + d, ht⟩) := by
    intro d
    induction d with
    | zero => intro t _; exact wireLe_refl _
    | succ d ih =>
      intro t ht
      have h1 := ih t (by omega)
      have h2 := hstep ⟨t + d, by omega⟩
      exact wireLe_trans h1 h2
  have hd : a.val + (b.val - a.val) = b.val := by omega
  have h := hgen (b.val - a.val) a.val (by omega)
  have hb : (⟨a.val + (b.val - a.val), by omega⟩ : Fin (H + 1)) = b := Fin.ext hd
  rwa [hb] at h

lemma wire_falls_lt_pow : ∀ (r : ℕ) (gs : List Gate),
    (∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) →
    notCount ⟨gs, 0⟩ ≤ r →
    ∀ (H : ℕ) (W : Fin (H + 1) → List Bool),
      (∀ l : Fin H, wireLe (W l.castSucc) (W l.succ)) →
      ∀ [DecidablePred (fun l : Fin H => ∃ idx,
        (stepList gs (W l.castSucc)).getD idx false = true ∧
        (stepList gs (W l.succ)).getD idx false = false)],
      ((Finset.univ : Finset (Fin H)).filter (fun l => ∃ idx,
        (stepList gs (W l.castSucc)).getD idx false = true ∧
        (stepList gs (W l.succ)).getD idx false = false)).card < 2 ^ r := by
  intro r
  induction r with
  | zero =>
    intro gs hgs hnot H W hW _
    classical
    have hno : ∀ g ∈ gs, g.op = .and ∨ g.op = .or := by
      intro g hg
      have hne : g.op ≠ .not := by
        intro heq
        have hpos : 0 < notCount ⟨gs, 0⟩ := by
          unfold notCount
          refine List.length_pos_of_mem (List.mem_filter.mpr ⟨hg, ?_⟩)
          simp [heq]
        omega
      rcases hgs g hg with h | h | h
      · exact .inl h
      · exact .inr h
      · exact (hne h).elim
    have hemp : ((Finset.univ : Finset (Fin H)).filter (fun l => ∃ idx,
        (stepList gs (W l.castSucc)).getD idx false = true ∧
        (stepList gs (W l.succ)).getD idx false = false)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro l _ ⟨idx, h1, h2⟩
      have hle := stepList_mono_noNot gs hno (hW l)
      have h3 := hle.2 idx h1
      rw [h2] at h3; cases h3
    rw [hemp]; simp
  | succ r ih =>
    intro gs hgs hnot H W hW _
    classical
    set S := (Finset.univ : Finset (Fin H)).filter (fun l => ∃ idx,
      (stepList gs (W l.castSucc)).getD idx false = true ∧
      (stepList gs (W l.succ)).getD idx false = false)
    by_cases hex : ∃ g ∈ gs, g.op = .not
    · obtain ⟨pre, ng, post, heq, hngo, hpre⟩ := split_first_not gs hex
      have hpre_ao : ∀ g ∈ pre, g.op = .and ∨ g.op = .or := by
        intro g hg
        rcases hgs g (by rw [heq]; simp [hg]) with h | h | h
        · exact .inl h
        · exact .inr h
        · exact (hpre g hg h).elim
      have hpost_op : ∀ g ∈ post, g.op = .and ∨ g.op = .or ∨ g.op = .not :=
        fun g hg => hgs g (by rw [heq]; simp [hg])
      have hpost_not : notCount ⟨post, 0⟩ ≤ r := by
        have hcnt : notCount ⟨gs, 0⟩ = notCount ⟨pre, 0⟩ + 1 + notCount ⟨post, 0⟩ := by
          simp only [notCount, heq, List.filter_append, List.filter_cons, hngo, decide_true,
            ↓reduceIte, List.length_append, List.length_cons]
          omega
        omega
      let U : Fin (H + 1) → List Bool := fun t => stepList pre (W t)
      have hU : ∀ l : Fin H, wireLe (U l.castSucc) (U l.succ) :=
        fun l => stepList_mono_noNot pre hpre_ao (hW l)
      let b : Fin (H + 1) → Bool := fun t => ng.op.eval (ng.inputs.map fun i => (U t).getD i false)
      have hb_anti : ∀ t1 t2 : Fin (H + 1), t1 ≤ t2 → b t1 = false → b t2 = false :=
        fun t1 t2 hle => not_eval_anti ng hngo (wireLe_chain hU t1 t2 hle)
      let V : Fin (H + 1) → List Bool := fun t => U t ++ [b t]
      have hstep_eq : ∀ t, stepList gs (W t) = stepList post (V t) := by
        intro t; rw [heq, stepList_append, stepList_cons]
      set St := S.filter (fun l => b l.castSucc = true ∧ b l.succ = true)
      set Sf := S.filter (fun l => b l.castSucc = false ∧ b l.succ = false)
      set Sc := S.filter (fun l => b l.castSucc = true ∧ b l.succ = false)
      have hcov : S ⊆ St ∪ Sf ∪ Sc := by
        intro l hl
        simp only [St, Sf, Sc, Finset.mem_union, Finset.mem_filter]
        cases h1 : b l.castSucc <;> cases h2 : b l.succ
        · left; right; exact ⟨hl, rfl, rfl⟩
        · exfalso
          have h3 := hb_anti l.castSucc l.succ (by change l.val ≤ l.val + 1; omega) h1
          rw [h2] at h3; cases h3
        · right; exact ⟨hl, rfl, rfl⟩
        · left; left; exact ⟨hl, rfl, rfl⟩
      have hSc : Sc.card ≤ 1 := by
        refine Finset.card_le_one.mpr ?_
        intro l1 hl1 l2 hl2
        simp only [Sc, Finset.mem_filter] at hl1 hl2
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have hle : l1.succ ≤ l2.castSucc := by change l1.val + 1 ≤ l2.val; exact Nat.succ_le_of_lt hlt
          have hfalse := hb_anti l1.succ l2.castSucc hle hl1.2.2
          rw [hl2.2.1] at hfalse; cases hfalse
        · have hle : l2.succ ≤ l1.castSucc := by change l2.val + 1 ≤ l1.val; exact Nat.succ_le_of_lt hlt
          have hfalse := hb_anti l2.succ l1.castSucc hle hl2.2.2
          rw [hl1.2.1] at hfalse; cases hfalse
      have hSt : St.card < 2 ^ r := by
        by_cases hemp : St = ∅
        · rw [hemp]; simp [Nat.pos_of_ne_zero (by positivity : 2 ^ r ≠ 0)]
        · obtain ⟨l0, hl0⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
          let Tset := (Finset.univ : Finset (Fin (H + 1))).filter (fun t => b t = true)
          have hTne : Tset.Nonempty := ⟨l0.succ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl0).2.2⟩⟩
          let p := Tset.max' hTne
          have hpb : b p = true := (Finset.mem_filter.mp (Finset.max'_mem Tset hTne)).2
          have hbt : ∀ t : Fin (H + 1), t ≤ p → b t = true := by
            intro t htp
            cases hbt' : b t
            · exfalso; have := hb_anti t p htp hbt'; rw [hpb] at this; cases this
            · rfl
          let Vp : Fin (p.val + 1) → List Bool := fun t => V ⟨t.val, by omega⟩
          have hVp : ∀ l : Fin p.val, wireLe (Vp l.castSucc) (Vp l.succ) := by
            intro l
            have hb1 : b ⟨l.val, by omega⟩ = true := hbt ⟨l.val, by omega⟩ (by change l.val ≤ p.val; omega)
            have hb2 : b ⟨l.val + 1, by omega⟩ = true := hbt ⟨l.val + 1, by omega⟩ (by change l.val + 1 ≤ p.val; omega)
            simp only [Vp, V, Fin.val_castSucc, Fin.val_succ, hb1, hb2]
            exact wireLe_append_same (hU ⟨l.val, by omega⟩) true
          have hih := ih post hpost_op hpost_not p.val Vp hVp
          let f : Fin H → Fin p.val := fun l =>
            if h : l.val < p.val then ⟨l.val, h⟩ else ⟨0, by
              have hle : l0.succ ≤ p := Finset.le_max' Tset l0.succ
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl0).2.2⟩)
              change l0.val + 1 ≤ p.val at hle; omega⟩
          have hcard_le : St.card ≤ ((Finset.univ : Finset (Fin p.val)).filter (fun l => ∃ idx,
              (stepList post (Vp l.castSucc)).getD idx false = true ∧
              (stepList post (Vp l.succ)).getD idx false = false)).card := by
            refine Finset.card_le_card_of_injOn f ?_ ?_
            · intro l hl
              have hl' := Finset.mem_filter.mp hl
              have hle : l.succ ≤ p := Finset.le_max' Tset l.succ
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'.2.2⟩)
              have hlt : l.val < p.val := by change l.val + 1 ≤ p.val at hle; omega
              simp only [f, dite_eq_left hlt, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
              obtain ⟨idx, h1, h2⟩ := (Finset.mem_filter.mp hl'.1).2
              rw [hstep_eq] at h1
              rw [hstep_eq] at h2
              exact ⟨idx, h1, h2⟩
            · intro l1 hl1 l2 hl2 hfeq
              have h1lt : l1.val < p.val := by
                have hle := Finset.le_max' Tset l1.succ
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl1).2.2⟩)
                change l1.val + 1 ≤ p.val at hle; omega
              have h2lt : l2.val < p.val := by
                have hle := Finset.le_max' Tset l2.succ
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl2).2.2⟩)
                change l2.val + 1 ≤ p.val at hle; omega
              simp only [f, dite_eq_left h1lt, dite_eq_left h2lt] at hfeq
              exact Fin.ext (congrArg (Fin.val : Fin p.val → ℕ) hfeq)
          exact lt_of_le_of_lt hcard_le hih
      have hSf : Sf.card < 2 ^ r := by
        by_cases hemp : Sf = ∅
        · rw [hemp]; simp [Nat.pos_of_ne_zero (by positivity : 2 ^ r ≠ 0)]
        · obtain ⟨l0, hl0⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
          let Fset := (Finset.univ : Finset (Fin (H + 1))).filter (fun t => b t = false)
          have hFne : Fset.Nonempty := ⟨l0.castSucc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl0).2.1⟩⟩
          let q := Fset.min' hFne
          have hqb : b q = false := (Finset.mem_filter.mp (Finset.min'_mem Fset hFne)).2
          have hbf : ∀ t : Fin (H + 1), q ≤ t → b t = false :=
            fun t hqt => hb_anti q t hqt hqb
          let Vq : Fin ((H - q.val) + 1) → List Bool := fun t => V ⟨q.val + t.val, by omega⟩
          have hVq : ∀ l : Fin (H - q.val), wireLe (Vq l.castSucc) (Vq l.succ) := by
            intro l
            have hb1 : b ⟨q.val + l.val, by omega⟩ = false := hbf _ (by change q.val ≤ q.val + l.val; omega)
            have hb2 : b ⟨q.val + (l.val + 1), by omega⟩ = false := hbf _ (by change q.val ≤ q.val + (l.val + 1); omega)
            simp only [Vq, V, Fin.val_castSucc, Fin.val_succ, hb1, hb2]
            have hu := hU ⟨q.val + l.val, by omega⟩
            have hadd : q.val + (l.val + 1) = q.val + l.val + 1 := by omega
            simpa [hadd] using wireLe_append_same hu false
          have hih := ih post hpost_op hpost_not (H - q.val) Vq hVq
          let f : Fin H → Fin (H - q.val) := fun l =>
            if h : q.val ≤ l.val then ⟨l.val - q.val, by omega⟩ else ⟨0, by
              have hle : q ≤ l0.castSucc := Finset.min'_le Fset l0.castSucc
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl0).2.1⟩)
              change q.val ≤ l0.val at hle; omega⟩
          have hcard_le : Sf.card ≤ ((Finset.univ : Finset (Fin (H - q.val))).filter (fun l => ∃ idx,
              (stepList post (Vq l.castSucc)).getD idx false = true ∧
              (stepList post (Vq l.succ)).getD idx false = false)).card := by
            refine Finset.card_le_card_of_injOn f ?_ ?_
            · intro l hl
              have hl' := Finset.mem_filter.mp hl
              have hle : q ≤ l.castSucc := Finset.min'_le Fset l.castSucc
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'.2.1⟩)
              have hge : q.val ≤ l.val := hle
              simp only [f, dite_eq_left hge, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
              obtain ⟨idx, h1, h2⟩ := (Finset.mem_filter.mp hl'.1).2
              rw [hstep_eq] at h1
              rw [hstep_eq] at h2
              have he1 : (⟨q.val + (l.val - q.val), by omega⟩ : Fin (H + 1)) = l.castSucc :=
                Fin.ext (by simp; omega)
              have he2 : (⟨q.val + (l.val - q.val + 1), by omega⟩ : Fin (H + 1)) = l.succ :=
                Fin.ext (by simp; omega)
              refine ⟨idx, ?_, ?_⟩
              · simpa [Vq, he1] using h1
              · simpa [Vq, he2] using h2
            · intro l1 hl1 l2 hl2 hfeq
              have h1ge : q.val ≤ l1.val := Finset.min'_le Fset l1.castSucc
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl1).2.1⟩)
              have h2ge : q.val ≤ l2.val := Finset.min'_le Fset l2.castSucc
                (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl2).2.1⟩)
              simp only [f, dite_eq_left h1ge, dite_eq_left h2ge] at hfeq
              have hv := congrArg (Fin.val : Fin (H - q.val) → ℕ) hfeq
              simp only at hv
              exact Fin.ext (by omega)
          exact lt_of_le_of_lt hcard_le hih
      have htot : S.card ≤ St.card + Sf.card + Sc.card := by
        calc S.card ≤ (St ∪ Sf ∪ Sc).card := Finset.card_le_card hcov
        _ ≤ (St ∪ Sf).card + Sc.card := Finset.card_union_le _ _
        _ ≤ St.card + Sf.card + Sc.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
      omega
    · have hno : ∀ g ∈ gs, g.op = .and ∨ g.op = .or := by
        intro g hg
        rcases hgs g hg with h | h | h
        · exact .inl h
        · exact .inr h
        · exact (hex ⟨g, hg, h⟩).elim
      have hemp : S = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro l _ ⟨idx, h1, h2⟩
        have hle := stepList_mono_noNot gs hno (hW l)
        have h3 := hle.2 idx h1
        rw [h2] at h3; cases h3
      rw [hemp]; simp [Nat.pos_of_ne_zero (by positivity : 2 ^ (r + 1) ≠ 0)]

def weight {n : ℕ} (x : Fin n → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => x i = true)).card

lemma weight_le {n : ℕ} (x : Fin n → Bool) : weight x ≤ n := by
  calc weight x ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
  _ = n := by simp

lemma weight_lt_of_le_ne {n : ℕ} {x y : Fin n → Bool}
    (hle : ∀ i, x i = true → y i = true) (hne : x ≠ y) : weight x < weight y := by
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨fun i hi => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hle i hi, ?_⟩
  intro heq
  apply hne; funext i
  have hiff : x i = true ↔ y i = true := by
    have := congrArg (fun s => i ∈ s) heq
    simpa using this
  cases hx : x i <;> cases hy : y i <;> simp_all

lemma le_of_testBit_imp {x y : ℕ} (h : ∀ j, y.testBit j = true → x.testBit j = true) : y ≤ x := by
  induction y using Nat.strongRecOn generalizing x with
  | ind y ih =>
    by_cases hy : y = 0
    · omega
    · have hdiv : y / 2 ≤ x / 2 := ih (y / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hy) (by omega)) (fun j hj => by
        have h1 := h (j + 1) (by simpa [Nat.testBit_succ] using hj)
        simpa [Nat.testBit_succ] using h1)
      have h0 : y % 2 ≤ x % 2 := by
        cases hmod : y % 2
        · omega
        · have hbit : y.testBit 0 = true := by simp [Nat.testBit_zero]; omega
          have hxbit := h 0 hbit
          simp [Nat.testBit_zero] at hxbit
          omega
      omega

lemma bit_mono_of_prefix {a b t r : ℕ} (hab : a ≤ b) (hbr : b < 2 ^ r)
    (hpref : ∀ s, t < s → s < r → b.testBit s = true → a.testBit s = true) :
    a.testBit t = true → b.testBit t = true := by
  have hq_le : a / 2 ^ (t + 1) ≤ b / 2 ^ (t + 1) := Nat.div_le_div_right hab
  have hq_ge : b / 2 ^ (t + 1) ≤ a / 2 ^ (t + 1) := by
    apply le_of_testBit_imp
    intro j hj
    rw [Nat.testBit_div_two_pow] at hj ⊢
    by_cases hlt : j + (t + 1) < r
    · exact hpref (j + (t + 1)) (by omega) hlt hj
    · exfalso
      have hge : 2 ^ r ≤ 2 ^ (j + (t + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
      have hlt2 : b < 2 ^ (j + (t + 1)) := lt_of_lt_of_le hbr hge
      rw [Nat.testBit_lt_two_pow hlt2] at hj; cases hj
  have hq_eq : a / 2 ^ (t + 1) = b / 2 ^ (t + 1) := le_antisymm hq_le hq_ge
  have hmod_le : a % 2 ^ (t + 1) ≤ b % 2 ^ (t + 1) := by
    have ha := Nat.div_add_mod a (2 ^ (t + 1))
    have hb := Nat.div_add_mod b (2 ^ (t + 1))
    rw [hq_eq] at ha; omega
  intro hat
  have hbit_iff : ∀ m : ℕ, m.testBit t = true ↔ 2 ^ t ≤ m % 2 ^ (t + 1) := by
    intro m
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
    have hpow : 2 ^ (t + 1) = 2 ^ t * 2 := by rw [Nat.pow_succ]
    have hdiv : (m % 2 ^ (t + 1)) / 2 ^ t = (m / 2 ^ t) % 2 := by
      rw [hpow, Nat.mod_mul_right_div_self]
    have hlt2 : (m % 2 ^ (t + 1)) / 2 ^ t < 2 := by
      rw [hdiv]; exact Nat.mod_lt _ (by omega)
    have hrem : (m % 2 ^ (t + 1)) % 2 ^ t < 2 ^ t := Nat.mod_lt _ (by positivity)
    have hda := Nat.div_add_mod (m % 2 ^ (t + 1)) (2 ^ t)
    constructor
    · intro hm1
      have h1 : (m % 2 ^ (t + 1)) / 2 ^ t = 1 := by rw [hdiv, hm1]
      rw [h1] at hda; omega
    · intro hge
      have h1 : 1 ≤ (m % 2 ^ (t + 1)) / 2 ^ t :=
        (Nat.le_div_iff_mul_le (by positivity)).mpr (by simpa using hge)
      omega
  rw [hbit_iff] at hat ⊢
  omega

lemma eq_of_le_all_bits {a b r : ℕ} (hab : a ≤ b) (hbr : b < 2 ^ r)
    (hall : ∀ s, s < r → b.testBit s = true → a.testBit s = true) : a = b := by
  refine le_antisymm hab (le_of_testBit_imp fun j hj => ?_)
  by_cases hlt : j < r
  · exact hall j hlt hj
  · exfalso
    have hlt2 : b < 2 ^ j := lt_of_lt_of_le hbr (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hlt2] at hj; cases hj

structure Builder (m0 : ℕ) where
  gs : List Gate
  fanIn : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  rb : ReadsBack m0 ⟨gs, 0⟩

lemma readsBack_append_one {m0 : ℕ} {gs : List Gate} (hrb : ReadsBack m0 ⟨gs, 0⟩)
    (g : Gate) (hg : ∀ i ∈ g.inputs, i < m0 + gs.length) :
    ReadsBack m0 ⟨gs ++ [g], 0⟩ := by
  intro j hj i hi
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < gs.length
  · have hgat : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
      simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [hgat] at hi
    exact hrb j hlt i hi
  · have heq : j = gs.length := by omega
    subst heq
    have hgat : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
      simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
    rw [hgat] at hi
    exact hg i hi

def pushGate {m0 : ℕ} (B : Builder m0) (g : Gate)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < m0 + B.gs.length) : Builder m0 × ℕ :=
  (⟨B.gs ++ [g], fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact B.fanIn x hx
      · exact (List.mem_singleton.mp hx) ▸ hfan,
    readsBack_append_one B.rb g hrb⟩, m0 + B.gs.length)

lemma ex_andList {m0 : ℕ} (trueW : ℕ) (htw : trueW < m0) (B : Builder m0) :
    ∀ (ws : List ℕ), (∀ w ∈ ws, w < m0 + B.gs.length) →
    ∃ (B' : Builder m0) (wout : ℕ) (ext : List Gate),
      wout < m0 + B'.gs.length ∧
      B'.gs = B.gs ++ ext ∧
      notCount ⟨ext, 0⟩ = 0 ∧
      ∀ inp : List Bool, inp.length = m0 → inp.getD trueW false = true →
        (stepList B'.gs inp).getD wout false = ws.all (fun w => (stepList B.gs inp).getD w false) := by
  intro ws
  induction ws with
  | nil =>
    intro _
    refine ⟨B, trueW, [], by omega, by simp, by simp [notCount], fun inp hlen htrue => ?_⟩
    rw [stepList_prefix_getD B.gs inp trueW (by omega), htrue]; rfl
  | cons w rest ih =>
    intro hws
    obtain ⟨B1, acc, ext1, hacc, hext1, hnot1, heval1⟩ := ih (fun u hu => hws u (List.mem_cons_of_mem _ hu))
    have hw1 : w < m0 + B1.gs.length := by
      have := hws w (List.mem_cons_self ..); rw [hext1, List.length_append]; omega
    let g : Gate := ⟨.and, [w, acc]⟩
    have hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      simp [g]
    have hrb : ∀ i ∈ g.inputs, i < m0 + B1.gs.length := by
      intro i hi; simp [g] at hi; rcases hi with rfl | rfl <;> assumption
    let res := pushGate B1 g hfan hrb
    refine ⟨res.1, res.2, ext1 ++ [g], by simp [res, pushGate], by simp [res, pushGate, hext1], ?_, ?_⟩
    · simp only [notCount, List.filter_append, List.filter_cons, g]
      simpa [notCount] using hnot1
    · intro inp hlen htrue
      simp only [res, pushGate]
      have hlen1 : (stepList B1.gs inp).length = m0 + B1.gs.length := by
        rw [stepList_length, hlen]
      rw [stepList_append, ← hlen1, stepList_last_getD]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      have hwb : (stepList B1.gs inp).getD w false = (stepList B.gs inp).getD w false := by
        rw [hext1, stepList_append]
        exact stepList_prefix_getD ext1 (stepList B.gs inp) w
          (by rw [stepList_length, hlen]; exact hws w (List.mem_cons_self ..))
      rw [hwb, heval1 inp hlen htrue]

lemma ex_orList {m0 : ℕ} (falseW : ℕ) (hfw : falseW < m0) (B : Builder m0) :
    ∀ (ws : List ℕ), (∀ w ∈ ws, w < m0 + B.gs.length) →
    ∃ (B' : Builder m0) (wout : ℕ) (ext : List Gate),
      wout < m0 + B'.gs.length ∧
      B'.gs = B.gs ++ ext ∧
      notCount ⟨ext, 0⟩ = 0 ∧
      ∀ inp : List Bool, inp.length = m0 → inp.getD falseW false = false →
        (stepList B'.gs inp).getD wout false = ws.any (fun w => (stepList B.gs inp).getD w false) := by
  intro ws
  induction ws with
  | nil =>
    intro _
    refine ⟨B, falseW, [], by omega, by simp, by simp [notCount], fun inp hlen hfalse => ?_⟩
    rw [stepList_prefix_getD B.gs inp falseW (by omega), hfalse]; rfl
  | cons w rest ih =>
    intro hws
    obtain ⟨B1, acc, ext1, hacc, hext1, hnot1, heval1⟩ := ih (fun u hu => hws u (List.mem_cons_of_mem _ hu))
    have hw1 : w < m0 + B1.gs.length := by
      have := hws w (List.mem_cons_self ..); rw [hext1, List.length_append]; omega
    let g : Gate := ⟨.or, [w, acc]⟩
    have hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      simp [g]
    have hrb : ∀ i ∈ g.inputs, i < m0 + B1.gs.length := by
      intro i hi; simp [g] at hi; rcases hi with rfl | rfl <;> assumption
    let res := pushGate B1 g hfan hrb
    refine ⟨res.1, res.2, ext1 ++ [g], by simp [res, pushGate], by simp [res, pushGate, hext1], ?_, ?_⟩
    · simp only [notCount, List.filter_append, List.filter_cons, g]
      simpa [notCount] using hnot1
    · intro inp hlen hfalse
      simp only [res, pushGate]
      have hlen1 : (stepList B1.gs inp).length = m0 + B1.gs.length := by
        rw [stepList_length, hlen]
      rw [stepList_append, ← hlen1, stepList_last_getD]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      have hwb : (stepList B1.gs inp).getD w false = (stepList B.gs inp).getD w false := by
        rw [hext1, stepList_append]
        exact stepList_prefix_getD ext1 (stepList B.gs inp) w
          (by rw [stepList_length, hlen]; exact hws w (List.mem_cons_self ..))
      rw [hwb, heval1 inp hlen hfalse]

lemma ex_dnfAux {m0 : ℕ} (trueW : ℕ) (htw : trueW < m0) :
    ∀ (terms : List (List ℕ)) (B : Builder m0), (∀ ts ∈ terms, ∀ w ∈ ts, w < m0 + B.gs.length) →
    ∃ (B' : Builder m0) (ws : List ℕ) (ext : List Gate),
      (∀ w ∈ ws, w < m0 + B'.gs.length) ∧
      B'.gs = B.gs ++ ext ∧
      notCount ⟨ext, 0⟩ = 0 ∧
      ∀ inp : List Bool, inp.length = m0 → inp.getD trueW false = true →
        ws.any (fun w => (stepList B'.gs inp).getD w false) =
        terms.any (fun ts => ts.all (fun w => (stepList B.gs inp).getD w false)) := by
  intro terms
  induction terms with
  | nil =>
    intro B _
    exact ⟨B, [], [], by simp, by simp, by simp [notCount], fun _ _ _ => rfl⟩
  | cons ts rest ih =>
    intro B hterms
    obtain ⟨B1, w1, ext1, hw1, hext1, hnot1, heval1⟩ :=
      ex_andList trueW htw B ts (hterms ts (List.mem_cons_self ..))
    obtain ⟨B2, ws2, ext2, hws2, hext2, hnot2, heval2⟩ :=
      ih B1 (fun u hu w hw => by
        have := hterms u (List.mem_cons_of_mem _ hu) w hw
        rw [hext1, List.length_append]; omega)
    refine ⟨B2, w1 :: ws2, ext1 ++ ext2, ?_, by rw [hext2, hext1, List.append_assoc], ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [hext2, List.length_append]; omega
      · exact hws2 w hw
    · simp only [notCount, List.filter_append, List.length_append]
      simp only [notCount] at hnot1 hnot2; omega
    · intro inp hlen htrue
      simp only [List.any_cons]
      have hw1_eq : (stepList B2.gs inp).getD w1 false = (stepList B1.gs inp).getD w1 false := by
        rw [hext2, stepList_append]
        exact stepList_prefix_getD ext2 (stepList B1.gs inp) w1 (by rw [stepList_length, hlen]; exact hw1)
      have hiff : ∀ (l : List (List ℕ)),
          (∀ u ∈ l, ∀ w ∈ u, w < m0 + B.gs.length) →
          l.any (fun u => u.all (fun w => (stepList B1.gs inp).getD w false)) =
          l.any (fun u => u.all (fun w => (stepList B.gs inp).getD w false)) := by
        intro l hl
        induction l with
        | nil => rfl
        | cons u us ihu =>
          simp only [List.any_cons]
          congr 1
          · clear ihu
            have hu : ∀ w ∈ u, w < m0 + B.gs.length := hl u (List.mem_cons_self ..)
            clear hl
            induction u with
            | nil => rfl
            | cons w ws ihw =>
              simp only [List.all_cons]
              congr 1
              · rw [hext1, stepList_append]
                exact stepList_prefix_getD ext1 (stepList B.gs inp) w
                  (by rw [stepList_length, hlen]; exact hu w (List.mem_cons_self ..))
              · exact ihw (fun x hx => hu x (List.mem_cons_of_mem _ hx))
          · exact ihu (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      rw [hw1_eq, heval1 inp hlen htrue, heval2 inp hlen htrue,
        hiff rest (fun u hu => hterms u (List.mem_cons_of_mem _ hu))]

lemma ex_dnf {m0 : ℕ} (falseW trueW : ℕ) (hfw : falseW < m0) (htw : trueW < m0) (B : Builder m0)
    (terms : List (List ℕ)) (hterms : ∀ ts ∈ terms, ∀ w ∈ ts, w < m0 + B.gs.length) :
    ∃ (B' : Builder m0) (wout : ℕ) (ext : List Gate),
      wout < m0 + B'.gs.length ∧
      B'.gs = B.gs ++ ext ∧
      notCount ⟨ext, 0⟩ = 0 ∧
      ∀ inp : List Bool, inp.length = m0 → inp.getD falseW false = false → inp.getD trueW false = true →
        (stepList B'.gs inp).getD wout false =
        terms.any (fun ts => ts.all (fun w => (stepList B.gs inp).getD w false)) := by
  obtain ⟨B1, ws1, ext1, hws1, hext1, hnot1, heval1⟩ := ex_dnfAux trueW htw terms B hterms
  obtain ⟨B2, outW, ext2, hout, hext2, hnot2, heval2⟩ := ex_orList falseW hfw B1 ws1 hws1
  refine ⟨B2, outW, ext1 ++ ext2, hout, by rw [hext2, hext1, List.append_assoc], ?_, ?_⟩
  · simp only [notCount, List.filter_append, List.length_append]
    simp only [notCount] at hnot1 hnot2; omega
  · intro inp hlen hfalse htrue
    rw [heval2 inp hlen hfalse, heval1 inp hlen htrue]

end PEqualNP.Outside.L_lib_1195

theorem PEqualNP.Outside.L_lib_1195 : (∀ (n q : Nat) (P : (Fin n → Bool) → Prop)
  (R : (Fin n → Bool) → (Fin q → Bool) → Prop),
  P (fun _ => false) → (∀ x, P x → ∃ y, R x y) →
  let bounded := fun (d : Nat) =>
    ∃ f : (Fin n → Bool) → Fin q → Bool, (∀ x, P x → R x (f x)) ∧
      ∀ (h : Nat) (x : Fin (h+1) → Fin n → Bool), (∀ i, P (x i)) →
        (∀ (l : Fin h) i, x l.castSucc i = true → x l.succ i = true) →
        ((Finset.univ : Finset (Fin h)).filter (fun l =>
          ∃ j, f (x l.castSucc) j = true ∧ f (x l.succ) j = false)).card ≤ d
  ∀ k r : Nat,
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
       (tap : Fin k → Fin q → Fin (k*n+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k*n+2) C ∧ C.output < k*n+2+C.size ∧
      PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ x : Fin k → Fin n → Bool, (∀ i, P (x i)) → ∀ i,
        let wires := (List.ofFn (fun j => List.ofFn (x j))).flatten ++ [false,true]
        R (x i) (fun j => (C.wires wires).getD (tap i j).val false)) ↔
    ∃ d, bounded d ∧ k*d < 2^r) := by
  open PEqualNP.Outside.L_lib_1195 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
    PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket in
  intro n q P R hP0 hR
  dsimp only
  set bounded : ℕ → Prop := fun d =>
    ∃ f : (Fin n → Bool) → Fin q → Bool, (∀ x, P x → R x (f x)) ∧
      ∀ (h : Nat) (x : Fin (h+1) → Fin n → Bool), (∀ i, P (x i)) →
        (∀ (l : Fin h) i, x l.castSucc i = true → x l.succ i = true) →
        ((Finset.univ : Finset (Fin h)).filter (fun l =>
          ∃ j, f (x l.castSucc) j = true ∧ f (x l.succ) j = false)).card ≤ d
  intro k r
  constructor
  · rintro ⟨C, tap, hfan, _hrb, _hout, hnot, hcomp⟩
    classical
    have hex_bd : ∃ d, bounded d := by
      let f0 : (Fin n → Bool) → Fin q → Bool :=
        fun x => if hx : P x then Classical.choose (hR x hx) else fun _ => false
      refine ⟨n, f0, fun x hx => by simp only [f0, dite_eq_left hx]; exact Classical.choose_spec (hR x hx), ?_⟩
      intro h x _ hmono
      set S := (Finset.univ : Finset (Fin h)).filter (fun l =>
        ∃ j, f0 (x l.castSucc) j = true ∧ f0 (x l.succ) j = false)
      have hcard : S.card ≤ weight (x (Fin.last h)) - weight (x 0) := by
        have hsum : ∀ m : ℕ, (hm : m ≤ h) →
            ((Finset.univ : Finset (Fin h)).filter (fun l => l.val < m ∧ l ∈ S)).card ≤
            weight (x ⟨m, by omega⟩) - weight (x 0) := by
          intro m
          induction m with
          | zero => intro _; simp
          | succ m ihm =>
            intro hm
            have hprev := ihm (by omega)
            have hle_w : weight (x ⟨m, by omega⟩) ≤ weight (x ⟨m + 1, by omega⟩) := by
              by_cases heq : x ⟨m, by omega⟩ = x ⟨m + 1, by omega⟩
              · rw [heq]
              · exact le_of_lt (weight_lt_of_le_ne (hmono ⟨m, by omega⟩) heq)
            have hle_0 : weight (x 0) ≤ weight (x ⟨m, by omega⟩) := by
              have hch : ∀ a : ℕ, (ha : a ≤ m) → weight (x 0) ≤ weight (x ⟨a, by omega⟩) := by
                intro a; induction a with
                | zero => intro _; exact le_rfl
                | succ a iha =>
                  intro ha
                  have h1 := iha (by omega)
                  have h2 : weight (x ⟨a, by omega⟩) ≤ weight (x ⟨a + 1, by omega⟩) := by
                    by_cases heq : x ⟨a, by omega⟩ = x ⟨a + 1, by omega⟩
                    · rw [heq]
                    · exact le_of_lt (weight_lt_of_le_ne (hmono ⟨a, by omega⟩) heq)
                  omega
              exact hch m le_rfl
            by_cases hmem : (⟨m, by omega⟩ : Fin h) ∈ S
            · have hne : x ⟨m, by omega⟩ ≠ x ⟨m + 1, by omega⟩ := by
                intro heq
                obtain ⟨j, h1, h2⟩ := (Finset.mem_filter.mp hmem).2
                change f0 (x ⟨m, by omega⟩) j = true at h1
                change f0 (x ⟨m + 1, by omega⟩) j = false at h2
                rw [heq] at h1; rw [h1] at h2; cases h2
              have hlt_w : weight (x ⟨m, by omega⟩) < weight (x ⟨m + 1, by omega⟩) :=
                weight_lt_of_le_ne (hmono ⟨m, by omega⟩) hne
              have hsub : (Finset.univ.filter fun l : Fin h => l.val < m + 1 ∧ l ∈ S) ⊆
                  insert ⟨m, by omega⟩ (Finset.univ.filter fun l : Fin h => l.val < m ∧ l ∈ S) := by
                intro l hl
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hl ⊢
                by_cases hlm : l.val = m
                · left; exact Fin.ext hlm
                · right; exact ⟨by omega, hl.2⟩
              have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
              omega
            · have heqset : (Finset.univ.filter fun l : Fin h => l.val < m + 1 ∧ l ∈ S) =
                  (Finset.univ.filter fun l : Fin h => l.val < m ∧ l ∈ S) := by
                ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · rintro ⟨hlt, hls⟩
                  refine ⟨?_, hls⟩
                  by_contra hge
                  have heql : l = ⟨m, by omega⟩ := Fin.ext (by change l.val = m; omega)
                  exact hmem (heql ▸ hls)
                · rintro ⟨hlt, hls⟩; exact ⟨by omega, hls⟩
              rw [heqset]; omega
        have hfull : S = (Finset.univ : Finset (Fin h)).filter (fun l => l.val < h ∧ l ∈ S) := by
          ext l; simp
        rw [hfull]
        exact hsum h le_rfl
      have hw := weight_le (x (Fin.last h))
      omega
    let d := Nat.find hex_bd
    have hd_bd : bounded d := Nat.find_spec hex_bd
    refine ⟨d, hd_bd, ?_⟩
    by_cases hkd0 : k * d = 0
    · rw [hkd0]; positivity
    · have hkpos : 0 < k := Nat.pos_of_ne_zero (fun h => hkd0 (by simp [h]))
      have hdpos : 0 < d := Nat.pos_of_ne_zero (fun h => hkd0 (by simp [h]))
      have hnot_prev : ¬ bounded (d - 1) := Nat.find_min hex_bd (by omega)
      let F : (Fin k → Fin n → Bool) → Fin k → Fin q → Bool :=
        fun X i j => (C.wires (enc X)).getD (tap i j).val false
      have hblock : ∀ (b : ℕ), (hb : b ≤ k) →
          ∃ (H : ℕ) (X : Fin (H + 1) → Fin k → Fin n → Bool),
            (∀ t i, P (X t i)) ∧
            (∀ (l : Fin H) i j, X l.castSucc i j = true → X l.succ i j = true) ∧
            (∀ i : Fin k, b ≤ i.val → X (Fin.last H) i = fun _ => false) ∧
            b * d ≤ ((Finset.univ : Finset (Fin H)).filter (fun l =>
              ∃ i j, F (X l.castSucc) i j = true ∧ F (X l.succ) i j = false)).card := by
        intro b
        induction b with
        | zero =>
          intro _
          exact ⟨0, fun _ _ _ => false, fun _ _ => hP0, fun l => Fin.elim0 l, fun _ _ => rfl, by simp⟩
        | succ b ihb =>
          intro hb
          obtain ⟨H1, X1, hP1, hM1, hZ1, hC1⟩ := ihb (by omega)
          let bFin : Fin k := ⟨b, by omega⟩
          let base := X1 (Fin.last H1)
          let lift : (Fin n → Bool) → Fin k → Fin n → Bool :=
            fun u i => if i = bFin then u else base i
          let fb : (Fin n → Bool) → Fin q → Bool := fun u => F (lift u) bFin
          have hfbR : ∀ u, P u → R u (fb u) := by
            intro u hu
            have hPlift : ∀ i, P (lift u i) := by
              intro i; dsimp only [lift]; split_ifs
              · exact hu
              · exact hP1 (Fin.last H1) i
            have hc := hcomp (lift u) hPlift bFin
            simpa [fb, F, enc, lift] using hc
          have hex_ch : ∃ (h2 : ℕ) (y : Fin (h2 + 1) → Fin n → Bool),
              (∀ t, P (y t)) ∧ (∀ (l : Fin h2) j, y l.castSucc j = true → y l.succ j = true) ∧
              d ≤ ((Finset.univ : Finset (Fin h2)).filter (fun l =>
                ∃ j, fb (y l.castSucc) j = true ∧ fb (y l.succ) j = false)).card := by
            by_contra hall
            push Not at hall
            apply hnot_prev
            exact ⟨fb, hfbR, fun h2 y hy hm => by have := hall h2 y hy hm; omega⟩
          obtain ⟨h2, y, hPy, hMy, hCy⟩ := hex_ch
          let H := H1 + (h2 + 1)
          let X : Fin (H + 1) → Fin k → Fin n → Bool := fun t =>
            if h : t.val ≤ H1 then X1 ⟨t.val, by omega⟩
            else lift (y ⟨t.val - (H1 + 1), by omega⟩)
          refine ⟨H, X, ?_, ?_, ?_, ?_⟩
          · intro t i
            dsimp only [X]; split_ifs with ht
            · exact hP1 _ i
            · dsimp only [lift]; split_ifs
              · exact hPy _
              · exact hP1 (Fin.last H1) i
          · intro l i j htrue
            dsimp only [X] at htrue ⊢
            by_cases h1 : l.val + 1 ≤ H1
            · have h0 : l.val ≤ H1 := by omega
              simp only [Fin.val_castSucc, Fin.val_succ, dite_eq_left h0, dite_eq_left h1] at htrue ⊢
              exact hM1 ⟨l.val, by omega⟩ i j htrue
            · by_cases h0 : l.val ≤ H1
              · have heq : l.val = H1 := by omega
                simp only [Fin.val_castSucc, Fin.val_succ, dite_eq_left h0, dite_eq_right h1] at htrue ⊢
                have hcast : (⟨l.val, by omega⟩ : Fin (H1 + 1)) = Fin.last H1 := Fin.ext heq
                rw [hcast] at htrue
                dsimp only [lift]
                split_ifs with hib
                · subst hib
                  have hz := hZ1 bFin (by simp [bFin])
                  change base bFin j = true at htrue
                  rw [show base bFin = (fun _ => false) from hz] at htrue
                  cases htrue
                · exact htrue
              · simp only [Fin.val_castSucc, Fin.val_succ, dite_eq_right h0, dite_eq_right h1] at htrue ⊢
                dsimp only [lift] at htrue ⊢
                split_ifs at htrue ⊢ with hib
                · have hsub : l.val + 1 - (H1 + 1) = (l.val - (H1 + 1)) + 1 := by omega
                  have hm := hMy ⟨l.val - (H1 + 1), by omega⟩ j htrue
                  simpa [hsub] using hm
                · exact htrue
          · intro i hi
            have hne : ¬ (H ≤ H1) := by omega
            have hib : i ≠ bFin := fun h => by subst h; simp [bFin] at hi
            simp only [X, Fin.val_last, dite_eq_right hne, lift, ite_eq_right hib]
            exact hZ1 i (by omega)
          · set S := (Finset.univ : Finset (Fin H)).filter (fun l =>
              ∃ i j, F (X l.castSucc) i j = true ∧ F (X l.succ) i j = false)
            set S1 := (Finset.univ : Finset (Fin H1)).filter (fun l =>
              ∃ i j, F (X1 l.castSucc) i j = true ∧ F (X1 l.succ) i j = false)
            set S2 := (Finset.univ : Finset (Fin h2)).filter (fun l =>
              ∃ j, fb (y l.castSucc) j = true ∧ fb (y l.succ) j = false)
            let f1 : Fin H1 → Fin H := fun l => ⟨l.val, by omega⟩
            let f2 : Fin h2 → Fin H := fun l => ⟨H1 + 1 + l.val, by omega⟩
            have hdisj : Disjoint (S1.image f1) (S2.image f2) := by
              rw [Finset.disjoint_left]
              intro u hu1 hu2
              obtain ⟨l1, _, rfl⟩ := Finset.mem_image.mp hu1
              obtain ⟨l2, _, heq⟩ := Finset.mem_image.mp hu2
              have hv := congrArg Fin.val heq
              simp only [f1, f2] at hv; omega
            have hsub1 : S1.image f1 ⊆ S := by
              intro u hu
              obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
              obtain ⟨i, j, h1, h2⟩ := (Finset.mem_filter.mp hl).2
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, j, ?_, ?_⟩
              · simp only [X, f1, Fin.val_castSucc, dite_eq_left (show l.val ≤ H1 by omega)]
                exact h1
              · simp only [X, f1, Fin.val_succ, dite_eq_left (show l.val + 1 ≤ H1 by omega)]
                exact h2
            have hsub2 : S2.image f2 ⊆ S := by
              intro u hu
              obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
              obtain ⟨j, hfb1, hfb2⟩ := (Finset.mem_filter.mp hl).2
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, bFin, j, ?_, ?_⟩
              · have hne1 : ¬ (H1 + 1 + l.val ≤ H1) := by omega
                have hs1 : (⟨H1 + 1 + l.val - (H1 + 1), by omega⟩ : Fin (h2 + 1)) = l.castSucc :=
                  Fin.ext (by simp)
                simp only [X, f2, Fin.val_castSucc, dite_eq_right hne1, hs1]
                exact hfb1
              · have hne2 : ¬ (H1 + 1 + l.val + 1 ≤ H1) := by omega
                have hs2 : (⟨H1 + 1 + l.val + 1 - (H1 + 1), by omega⟩ : Fin (h2 + 1)) = l.succ :=
                  Fin.ext (by simp; omega)
                simp only [X, f2, Fin.val_succ, dite_eq_right hne2, hs2]
                exact hfb2
            have hc1 : (S1.image f1).card = S1.card :=
              Finset.card_image_of_injective S1 (fun a b h => Fin.ext (by simpa [f1] using congrArg Fin.val h))
            have hc2 : (S2.image f2).card = S2.card :=
              Finset.card_image_of_injective S2 (fun a b h => Fin.ext (by simpa [f2] using congrArg Fin.val h))
            have hle : S1.card + S2.card ≤ S.card := by
              rw [← hc1, ← hc2, ← Finset.card_union_of_disjoint hdisj]
              exact Finset.card_le_card (Finset.union_subset hsub1 hsub2)
            have hmul : (b + 1) * d = b * d + d := by ring
            omega
      obtain ⟨H, X, _, hMX, _, hCX⟩ := hblock k le_rfl
      have hW_mono : ∀ l : Fin H, wireLe (enc (X l.castSucc)) (enc (X l.succ)) :=
        fun l => enc_wireLe (hMX l)
      have hgs_op : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not := fun g hg => by
        have hf := (hfan g hg).1
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hf
      have hnot' : notCount ⟨C.gates, 0⟩ ≤ r := hnot
      have hpow := wire_falls_lt_pow r C.gates hgs_op hnot' H (fun t => enc (X t)) hW_mono
      have hsub : ((Finset.univ : Finset (Fin H)).filter (fun l =>
          ∃ i j, F (X l.castSucc) i j = true ∧ F (X l.succ) i j = false)) ⊆
          ((Finset.univ : Finset (Fin H)).filter (fun l => ∃ idx,
            (stepList C.gates (enc (X l.castSucc))).getD idx false = true ∧
            (stepList C.gates (enc (X l.succ))).getD idx false = false)) := by
        intro l hl
        obtain ⟨i, j, h1, h2⟩ := (Finset.mem_filter.mp hl).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (tap i j).val, h1, h2⟩
      exact lt_of_le_of_lt (hCX.trans (Finset.card_le_card hsub)) hpow
  · rintro ⟨d, ⟨f, hfR, hfd⟩, hkd⟩
    classical
    let F : (Fin k → Fin n → Bool) → Fin k → Fin q → Bool := fun X i => f (X i)
    let inP : (Fin k → Fin n → Bool) → Prop := fun X => ∀ i, P (X i)
    have hF_falls : ∀ (h : ℕ) (X : Fin (h + 1) → Fin k → Fin n → Bool),
        (∀ t, inP (X t)) →
        (∀ (l : Fin h) i j, X l.castSucc i j = true → X l.succ i j = true) →
        ((Finset.univ : Finset (Fin h)).filter (fun l =>
          ∃ i j, F (X l.castSucc) i j = true ∧ F (X l.succ) i j = false)).card ≤ k * d := by
      intro h X hPX hMX
      have hsub : ((Finset.univ : Finset (Fin h)).filter (fun l =>
          ∃ i j, F (X l.castSucc) i j = true ∧ F (X l.succ) i j = false)) ⊆
          (Finset.univ : Finset (Fin k)).biUnion (fun i =>
            (Finset.univ : Finset (Fin h)).filter (fun l =>
              ∃ j, f (X l.castSucc i) j = true ∧ f (X l.succ i) j = false)) := by
        intro l hl
        obtain ⟨i, j, h1, h2⟩ := (Finset.mem_filter.mp hl).2
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, h1, h2⟩⟩
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ ∑ i : Fin k, ((Finset.univ : Finset (Fin h)).filter (fun l =>
              ∃ j, f (X l.castSucc i) j = true ∧ f (X l.succ i) j = false)).card := Finset.card_biUnion_le
        _ ≤ ∑ _i : Fin k, d := Finset.sum_le_sum (fun i _ => hfd h (fun t => X t i) (fun t => hPX t i) (fun l j => hMX l i j))
        _ = k * d := by simp
    let HasChain : (Fin k → Fin n → Bool) → ℕ → Prop := fun X m =>
      ∃ (h : ℕ) (C : Fin (h + 1) → Fin k → Fin n → Bool),
        (∀ t, inP (C t)) ∧
        (∀ (l : Fin h) i j, C l.castSucc i j = true → C l.succ i j = true) ∧
        C (Fin.last h) = X ∧
        ((Finset.univ : Finset (Fin h)).filter (fun l =>
          ∃ i j, F (C l.castSucc) i j = true ∧ F (C l.succ) i j = false)).card = m
    have hHas0 : ∀ X, inP X → HasChain X 0 := fun X hX =>
      ⟨0, fun _ => X, fun _ => hX, fun l => Fin.elim0 l, rfl, by simp⟩
    let rank : (Fin k → Fin n → Bool) → ℕ := fun X =>
      if hX : inP X then
        ((Finset.range (k * d + 1)).filter (HasChain X)).max'
          ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hHas0 X hX⟩⟩
      else 0
    have hrank_lt : ∀ X, rank X < 2 ^ r := by
      intro X
      dsimp only [rank]; split_ifs with hX
      · have hne : ((Finset.range (k * d + 1)).filter (HasChain X)).Nonempty :=
          ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hHas0 X hX⟩⟩
        have hm := Finset.max'_mem ((Finset.range (k * d + 1)).filter (HasChain X)) hne
        have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
        omega
      · positivity
    have hrank_has : ∀ X, inP X → HasChain X (rank X) := by
      intro X hX
      simp only [rank, dite_eq_left hX]
      exact (Finset.mem_filter.mp (Finset.max'_mem _ _)).2
    have hrank_ge : ∀ X m, inP X → HasChain X m → m ≤ rank X := by
      intro X m hX hm
      obtain ⟨h, C, hPC, hMC, hlast, rfl⟩ := hm
      have hle := hF_falls h C hPC hMC
      simp only [rank, dite_eq_left hX]
      exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h, C, hPC, hMC, hlast, rfl⟩)
    have hrank_step : ∀ X Y, inP X → inP Y → (∀ i j, X i j = true → Y i j = true) →
        rank X + (if ∃ i j, F X i j = true ∧ F Y i j = false then 1 else 0) ≤ rank Y := by
      intro X Y hX hY hXY
      obtain ⟨h, C, hPC, hMC, hlast, hcard⟩ := hrank_has X hX
      let C' : Fin (h + 2) → Fin k → Fin n → Bool := fun t =>
        if ht : t.val ≤ h then C ⟨t.val, by omega⟩ else Y
      have hPC' : ∀ t, inP (C' t) := fun t => by dsimp only [C']; split_ifs; exacts [hPC _, hY]
      have hMC' : ∀ (l : Fin (h + 1)) i j, C' l.castSucc i j = true → C' l.succ i j = true := by
        intro l i j htr
        dsimp only [C'] at htr ⊢
        by_cases h1 : l.val + 1 ≤ h
        · have h0 : l.val ≤ h := by omega
          simp only [Fin.val_castSucc, Fin.val_succ, dite_eq_left h0, dite_eq_left h1] at htr ⊢
          exact hMC ⟨l.val, by omega⟩ i j htr
        · have heq : l.val = h := by omega
          have h0 : l.val ≤ h := by omega
          simp only [Fin.val_castSucc, Fin.val_succ, dite_eq_left h0, dite_eq_right h1] at htr ⊢
          have hcl : (⟨l.val, by omega⟩ : Fin (h + 1)) = Fin.last h := Fin.ext heq
          rw [hcl, hlast] at htr
          exact hXY i j htr
      have hlast' : C' (Fin.last (h + 1)) = Y := by
        simp only [C', Fin.val_last, dite_eq_right (by omega : ¬ (h + 1 ≤ h))]
      set S' := (Finset.univ : Finset (Fin (h + 1))).filter (fun l =>
        ∃ i j, F (C' l.castSucc) i j = true ∧ F (C' l.succ) i j = false)
      set S := (Finset.univ : Finset (Fin h)).filter (fun l =>
        ∃ i j, F (C l.castSucc) i j = true ∧ F (C l.succ) i j = false)
      have himg : S.image Fin.castSucc ⊆ S' := by
        intro u hu
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨i, j, h1, h2⟩ := (Finset.mem_filter.mp hl).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, j, ?_, ?_⟩
        · simp only [C', Fin.val_castSucc, dite_eq_left (show l.val ≤ h by omega)]
          exact h1
        · simp only [C', Fin.val_succ, Fin.val_castSucc, dite_eq_left (show l.val + 1 ≤ h by omega)]
          exact h2
      have hcard_img : (S.image Fin.castSucc).card = rank X := by
        rw [Finset.card_image_of_injective S (Fin.castSucc_injective h), hcard]
      have hS'_ge : rank X + (if ∃ i j, F X i j = true ∧ F Y i j = false then 1 else 0) ≤ S'.card := by
        split_ifs with hfall
        · have hlast_mem : Fin.last h ∈ S' := by
            obtain ⟨i, j, h1, h2⟩ := hfall
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, j, ?_, ?_⟩
            · simp only [C', Fin.val_castSucc, Fin.val_last, dite_eq_left le_rfl]
              have hlh : (⟨h, by omega⟩ : Fin (h + 1)) = Fin.last h := rfl
              rw [hlh, hlast]; exact h1
            · simp only [C', Fin.val_succ, Fin.val_last, dite_eq_right (by omega : ¬ (h + 1 ≤ h))]
              exact h2
          have hnotmem : Fin.last h ∉ S.image Fin.castSucc := by
            intro hm; obtain ⟨l, _, heq⟩ := Finset.mem_image.mp hm
            have := congrArg Fin.val heq; simp at this; omega
          have hsub2 : insert (Fin.last h) (S.image Fin.castSucc) ⊆ S' :=
            Finset.insert_subset hlast_mem himg
          have hc := Finset.card_le_card hsub2
          rw [Finset.card_insert_of_notMem hnotmem, hcard_img] at hc
          omega
        · rw [← hcard_img]; exact Finset.card_le_card himg
      exact hS'_ge.trans (hrank_ge Y S'.card hY ⟨h + 1, C', hPC', hMC', hlast', rfl⟩)
    let m0 := k * n + 2
    let falseW := k * n
    let trueW := k * n + 1
    have hfw : falseW < m0 := by omega
    have htw : trueW < m0 := by omega
    let initB : Builder m0 := ⟨[], by simp, fun j hj => by simp at hj⟩
    let inputWires : List ℕ := List.range (k * n)
    have hinputW_lt : ∀ w ∈ inputWires, w < m0 := fun w hw => by
      have := List.mem_range.mp hw; omega
    have ex_mono : ∀ (B : Builder m0) (avail : List ℕ) (_hav : ∀ w ∈ avail, w < m0 + B.gs.length)
        (g : (Fin k → Fin n → Bool) → Bool)
        (_hg_mono : ∀ Y X, inP Y → inP X → g Y = true →
          (∀ w ∈ avail, (stepList B.gs (enc Y)).getD w false = true →
                        (stepList B.gs (enc X)).getD w false = true) → g X = true),
        ∃ (B' : Builder m0) (wout : ℕ) (ext : List Gate),
          wout < m0 + B'.gs.length ∧
          B'.gs = B.gs ++ ext ∧
          notCount ⟨ext, 0⟩ = 0 ∧
          ∀ X, inP X → (stepList B'.gs (enc X)).getD wout false = g X := by
      intro B avail hav g hg_mono
      let posInputs : List (Fin k → Fin n → Bool) :=
        ((Finset.univ : Finset (Fin k → Fin n → Bool)).filter (fun Y => inP Y ∧ g Y = true)).toList
      let terms : List (List ℕ) :=
        posInputs.map (fun Y => avail.filter (fun w => (stepList B.gs (enc Y)).getD w false))
      have hterms : ∀ ts ∈ terms, ∀ w ∈ ts, w < m0 + B.gs.length := by
        intro ts hts w hw
        obtain ⟨Y, _, rfl⟩ := List.mem_map.mp hts
        exact hav w (List.mem_filter.mp hw).1
      obtain ⟨B', wout, ext, hwout, hext, hnotExt, heval⟩ := ex_dnf falseW trueW hfw htw B terms hterms
      refine ⟨B', wout, ext, hwout, hext, hnotExt, fun X hPX => ?_⟩
      rw [heval (enc X) (enc_length X) (enc_getD_false X) (enc_getD_true X)]
      apply Bool.eq_iff_iff.mpr
      rw [List.any_eq_true]
      constructor
      · rintro ⟨ts, hts, hall⟩
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hts
        have hY' := Finset.mem_filter.mp (Finset.mem_toList.mp hY)
        refine hg_mono Y X hY'.2.1 hPX hY'.2.2 (fun w hw hwy => ?_)
        have hmem : w ∈ avail.filter (fun w => (stepList B.gs (enc Y)).getD w false) :=
          List.mem_filter.mpr ⟨hw, hwy⟩
        exact List.all_eq_true.mp hall w hmem
      · intro hgX
        have hXmem : X ∈ posInputs :=
          Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPX, hgX⟩)
        refine ⟨avail.filter (fun w => (stepList B.gs (enc X)).getD w false),
          List.mem_map.mpr ⟨X, hXmem, rfl⟩, ?_⟩
        rw [List.all_eq_true]
        intro w hw
        exact (List.mem_filter.mp hw).2
    have hstage : ∀ t : ℕ, t ≤ r →
        ∃ (B : Builder m0) (cws : Fin t → ℕ),
          notCount ⟨B.gs, 0⟩ ≤ t ∧
          (∀ s : Fin t, cws s < m0 + B.gs.length) ∧
          (∀ X, inP X → ∀ s : Fin t,
            (stepList B.gs (enc X)).getD (cws s) false = !((rank X).testBit (r - 1 - s.val))) := by
      intro t
      induction t with
      | zero =>
        intro _
        exact ⟨initB, Fin.elim0, by simp [initB, notCount], fun s => Fin.elim0 s, fun _ _ s => Fin.elim0 s⟩
      | succ t iht =>
        intro ht
        obtain ⟨B, cws, hnotB, hcws_lt, hcws_val⟩ := iht (by omega)
        let bitPos := r - 1 - t
        let avail : List ℕ := inputWires ++ List.ofFn cws
        have hav : ∀ w ∈ avail, w < m0 + B.gs.length := by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · have := hinputW_lt w hw; omega
          · obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hw; exact hcws_lt s
        have hg_mono : ∀ Y X, inP Y → inP X → (rank Y).testBit bitPos = true →
            (∀ w ∈ avail, (stepList B.gs (enc Y)).getD w false = true →
                          (stepList B.gs (enc X)).getD w false = true) →
            (rank X).testBit bitPos = true := by
          intro Y X hPY hPX hYbit hwa
          have hYX : ∀ i j, Y i j = true → X i j = true := by
            intro i j hyij
            have hw : i.val * n + j.val ∈ inputWires := List.mem_range.mpr (by nlinarith [i.isLt, j.isLt])
            have hltw : i.val * n + j.val < (enc Y).length := by rw [enc_length]; nlinarith [i.isLt, j.isLt]
            have h1 := hwa (i.val * n + j.val) (List.mem_append_left _ hw)
            rw [stepList_prefix_getD B.gs (enc Y) _ hltw, enc_getD_bit,
                stepList_prefix_getD B.gs (enc X) _ (by rw [enc_length]; nlinarith [i.isLt, j.isLt]),
                enc_getD_bit] at h1
            exact h1 hyij
          have hle_rank : rank Y ≤ rank X := by
            have := hrank_step Y X hPY hPX hYX; omega
          refine bit_mono_of_prefix hle_rank (hrank_lt X) ?_ hYbit
          intro s hs1 hs2 hXbit
          let sIdx : Fin t := ⟨r - 1 - s, by omega⟩
          have hpos_eq : r - 1 - sIdx.val = s := by simp [sIdx]; omega
          have hcw_mem : cws sIdx ∈ avail := List.mem_append_right _ (List.mem_ofFn.mpr ⟨sIdx, rfl⟩)
          have h1 := hwa (cws sIdx) hcw_mem
          rw [hcws_val Y hPY sIdx, hcws_val X hPX sIdx, hpos_eq] at h1
          cases hyb : (rank Y).testBit s
          · exfalso
            have := h1 (by simp [hyb])
            simp [hXbit] at this
          · rfl
        obtain ⟨B1, wbit, ext1, hwbit, hext1, hnot1, heval1⟩ :=
          ex_mono B avail hav (fun X => (rank X).testBit bitPos) hg_mono
        let ng : Gate := ⟨.not, [wbit]⟩
        have hfan_ng : ng.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ng.inputs.length ≤ 2 := by
          simp [ng]
        have hrb_ng : ∀ i ∈ ng.inputs, i < m0 + B1.gs.length := by
          intro i hi; simp [ng] at hi; subst hi; exact hwbit
        let pushed := pushGate B1 ng hfan_ng hrb_ng
        let B2 := pushed.1
        let wneg := pushed.2
        let cws2 : Fin (t + 1) → ℕ := Fin.snoc cws wneg
        refine ⟨B2, cws2, ?_, ?_, ?_⟩
        · have hnc2 : notCount ⟨B2.gs, 0⟩ = notCount ⟨B.gs, 0⟩ + notCount ⟨ext1, 0⟩ + 1 := by
            simp only [B2, pushed, pushGate, hext1, notCount, List.filter_append, List.filter_cons,
              List.filter_nil, ng, decide_true, ↓reduceIte, List.length_append, List.length_cons,
              List.length_nil]
          omega
        · intro s
          refine Fin.lastCases ?_ ?_ s
          · simp [cws2, wneg, B2, pushed, pushGate]
          · intro s'
            simp only [cws2, Fin.snoc_castSucc, B2, pushed, pushGate, hext1, List.length_append, List.length_singleton]
            have := hcws_lt s'; omega
        · intro X hPX s
          refine Fin.lastCases ?_ ?_ s
          · simp only [cws2, Fin.snoc_last, Fin.val_last, B2, wneg, pushed, pushGate]
            have hlen1 : (stepList B1.gs (enc X)).length = m0 + B1.gs.length := by
              rw [stepList_length, enc_length]
            rw [stepList_append, ← hlen1, stepList_last_getD]
            simp only [ng, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
            rw [heval1 X hPX]
          · intro s'
            simp only [cws2, Fin.snoc_castSucc, Fin.val_castSucc, B2, pushed, pushGate, hext1]
            rw [List.append_assoc, stepList_append,
              stepList_prefix_getD _ _ _ (by rw [stepList_length, enc_length]; exact hcws_lt s')]
            exact hcws_val X hPX s'
    obtain ⟨Br, cws, hnotBr, hcws_lt, hcws_val⟩ := hstage r le_rfl
    let availAll : List ℕ := inputWires ++ List.ofFn cws
    have havAll : ∀ w ∈ availAll, w < m0 + Br.gs.length := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · have := hinputW_lt w hw; omega
      · obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hw; exact hcws_lt s
    have hF_mono : ∀ (i : Fin k) (j : Fin q) (Y X : Fin k → Fin n → Bool),
        inP Y → inP X → F Y i j = true →
        (∀ w ∈ availAll, (stepList Br.gs (enc Y)).getD w false = true →
                         (stepList Br.gs (enc X)).getD w false = true) →
        F X i j = true := by
      intro i j Y X hPY hPX hFY hwa
      have hYX : ∀ a b, Y a b = true → X a b = true := by
        intro a b hyab
        have hw : a.val * n + b.val ∈ inputWires := List.mem_range.mpr (by nlinarith [a.isLt, b.isLt])
        have hltw : a.val * n + b.val < (enc Y).length := by rw [enc_length]; nlinarith [a.isLt, b.isLt]
        have h1 := hwa (a.val * n + b.val) (List.mem_append_left _ hw)
        rw [stepList_prefix_getD Br.gs (enc Y) _ hltw, enc_getD_bit,
            stepList_prefix_getD Br.gs (enc X) _ (by rw [enc_length]; nlinarith [a.isLt, b.isLt]),
            enc_getD_bit] at h1
        exact h1 hyab
      have hle_rank : rank Y ≤ rank X := by
        have := hrank_step Y X hPY hPX hYX; omega
      have hrank_eq : rank Y = rank X := by
        refine eq_of_le_all_bits hle_rank (hrank_lt X) (fun s hs hXbit => ?_)
        let sIdx : Fin r := ⟨r - 1 - s, by omega⟩
        have hpos_eq : r - 1 - sIdx.val = s := by simp [sIdx]; omega
        have hcw_mem : cws sIdx ∈ availAll := List.mem_append_right _ (List.mem_ofFn.mpr ⟨sIdx, rfl⟩)
        have h1 := hwa (cws sIdx) hcw_mem
        rw [hcws_val Y hPY sIdx, hcws_val X hPX sIdx, hpos_eq] at h1
        cases hyb : (rank Y).testBit s
        · exfalso; have := h1 (by simp [hyb]); simp [hXbit] at this
        · rfl
      by_contra hFXf
      have hFXfalse : F X i j = false := Bool.eq_false_iff.mpr hFXf
      have hstep := hrank_step Y X hPY hPX hYX
      rw [ite_eq_left ⟨i, j, hFY, hFXfalse⟩, hrank_eq] at hstep
      omega
    have hbuild_outs : ∀ (outs : List (Fin k × Fin q)),
        ∃ (B : Builder m0) (ext : List Gate) (mp : (Fin k × Fin q) → ℕ),
          B.gs = Br.gs ++ ext ∧
          notCount ⟨ext, 0⟩ = 0 ∧
          (∀ p ∈ outs, mp p < m0 + B.gs.length) ∧
          (∀ X, inP X → ∀ p ∈ outs, (stepList B.gs (enc X)).getD (mp p) false = F X p.1 p.2) := by
      intro outs
      induction outs with
      | nil => exact ⟨Br, [], fun _ => 0, by simp, by simp [notCount], by simp, fun _ _ _ h => (List.not_mem_nil h).elim⟩
      | cons p rest ih =>
        obtain ⟨B1, ext1, mp1, hB1eq, hnot1, hlt1, hval1⟩ := ih
        have hav1 : ∀ w ∈ availAll, w < m0 + B1.gs.length := fun w hw => by
          rw [hB1eq, List.length_append]; have := havAll w hw; omega
        have hwire_same : ∀ (X : Fin k → Fin n → Bool) (w : ℕ), w ∈ availAll →
            (stepList B1.gs (enc X)).getD w false = (stepList Br.gs (enc X)).getD w false := by
          intro X w hw
          rw [hB1eq, stepList_append]
          exact stepList_prefix_getD ext1 (stepList Br.gs (enc X)) w
            (by rw [stepList_length, enc_length]; exact havAll w hw)
        have hg_mono1 : ∀ Y X, inP Y → inP X → F Y p.1 p.2 = true →
            (∀ w ∈ availAll, (stepList B1.gs (enc Y)).getD w false = true →
                             (stepList B1.gs (enc X)).getD w false = true) →
            F X p.1 p.2 = true := by
          intro Y X hPY hPX hFY hwa
          refine hF_mono p.1 p.2 Y X hPY hPX hFY (fun w hw hwy => ?_)
          rw [← hwire_same X w hw]
          exact hwa w hw (by rwa [hwire_same Y w hw])
        obtain ⟨B2, wp, ext2, hwp, hext2, hnot2, heval2⟩ :=
          ex_mono B1 availAll hav1 (fun X => F X p.1 p.2) hg_mono1
        let mp2 : (Fin k × Fin q) → ℕ := fun u => if u = p then wp else mp1 u
        refine ⟨B2, ext1 ++ ext2, mp2, by rw [hext2, hB1eq, List.append_assoc], ?_, ?_, ?_⟩
        · simp only [notCount, List.filter_append, List.length_append]
          simp only [notCount] at hnot1 hnot2; omega
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · simp [mp2, hwp]
          · dsimp only [mp2]; split_ifs
            · exact hwp
            · rw [hext2, List.length_append]; have := hlt1 u hu; omega
        · intro X hPX u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · simp only [mp2, ite_eq_left rfl]; exact heval2 X hPX
          · dsimp only [mp2]; split_ifs with hup
            · subst hup; exact heval2 X hPX
            · rw [hext2, stepList_append,
                stepList_prefix_getD ext2 (stepList B1.gs (enc X)) (mp1 u)
                  (by rw [stepList_length, enc_length]; exact hlt1 u hu)]
              exact hval1 X hPX u hu
    let allPairs : List (Fin k × Fin q) := (Finset.univ : Finset (Fin k × Fin q)).toList
    obtain ⟨Bfin, extFin, mpFin, hBfin_eq, hnotFin, hltFin, hvalFin⟩ := hbuild_outs allPairs
    let Cfin : Circuit := ⟨Bfin.gs, 0⟩
    have hlt_all : ∀ (i : Fin k) (j : Fin q), mpFin (i, j) < k * n + 2 + Cfin.size :=
      fun i j => hltFin (i, j) (Finset.mem_toList.mpr (Finset.mem_univ _))
    let tapFin : Fin k → Fin q → Fin (k * n + 2 + Cfin.size) :=
      fun i j => ⟨mpFin (i, j), hlt_all i j⟩
    refine ⟨Cfin, tapFin, Bfin.fanIn, Bfin.rb, by simp [Cfin], ?_, ?_⟩
    · have hnc : notCount Cfin = notCount ⟨Br.gs, 0⟩ + notCount ⟨extFin, 0⟩ := by
        simp only [Cfin, hBfin_eq, notCount, List.filter_append, List.length_append]
      omega
    · intro X hPX i
      have hsame : (fun j => (Cfin.wires (enc X)).getD (tapFin i j).val false) = f (X i) := by
        funext j
        exact hvalFin X hPX (i, j) (Finset.mem_toList.mpr (Finset.mem_univ _))
      change R (X i) (fun j => (Cfin.wires (enc X)).getD (tapFin i j).val false)
      rw [hsame]
      exact hfR (X i) (hPX i)
