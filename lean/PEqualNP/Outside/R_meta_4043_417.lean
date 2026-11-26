import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4043_417
    (h_one_dirty :
      let G := edgeGraph 25 ((List.range 12).flatMap fun l =>
        [(l, 13 + l), ((l + 1) % 13, 13 + l), ((l + 3) % 13, 13 + l), ((l + 9) % 13, 13 + l)])
      ∀ C : Circuit, C.size ≤ 57 → IsLeastAO G C → (junk G C).card = 1 → False)
    (h_antichain :
      let G := edgeGraph 25 ((List.range 12).flatMap fun l =>
        [(l, 13 + l), ((l + 1) % 13, 13 + l), ((l + 3) % 13, 13 + l), ((l + 9) % 13, 13 + l)])
      ∀ C : Circuit, C.size ≤ 57 → IsLeastAO G C → 2 ≤ (junk G C).card →
        (∀ i ∈ junk G C, ∀ j ∈ junk G C, ¬ InCone 25 C i j) → False)
    (h_chain :
      let G := edgeGraph 25 ((List.range 12).flatMap fun l =>
        [(l, 13 + l), ((l + 1) % 13, 13 + l), ((l + 3) % 13, 13 + l), ((l + 9) % 13, 13 + l)])
      ∀ C : Circuit, C.size ≤ 57 → IsLeastAO G C → 2 ≤ (junk G C).card →
        (∃ i ∈ junk G C, ∃ j ∈ junk G C, InCone 25 C i j) → False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (58 : ℕ) ≤ x1.size) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have pairInput_left : ∀ (u v : Fin 25), pairInput u v u = true := fun u v => by
    change decide (u = u ∨ u = v) = true; simp only [true_or, decide_true]
  have pairInput_right : ∀ (u v : Fin 25), pairInput u v v = true := fun u v => by
    change decide (v = u ∨ v = v) = true; simp only [or_true, decide_true]
  have pairInput_true : ∀ (u v w : Fin 25), pairInput u v w = true ↔ w = u ∨ w = v := fun u v w => by
    change decide (w = u ∨ w = v) = true ↔ w = u ∨ w = v; simp only [decide_eq_true_eq]
  let E25 : List (ℕ × ℕ) := (List.range 12).flatMap fun l =>
    [(l, 13 + l), ((l + 1) % 13, 13 + l), ((l + 3) % 13, 13 + l), ((l + 9) % 13, 13 + l)]
  let G := edgeGraph 25 E25
  have hDiff4 : ∀ a ∈ ([0, 1, 3, 9] : List (Fin 13)),
      ∀ b ∈ ([0, 1, 3, 9] : List (Fin 13)),
      ∀ c ∈ ([0, 1, 3, 9] : List (Fin 13)),
      ∀ d ∈ ([0, 1, 3, 9] : List (Fin 13)),
      a ≠ b → a + d = b + c → a = c := by
    let D : Fin 4 → Fin 13 := fun i => ([0, 1, 3, 9] : List (Fin 13)).getD i.val 0
    have hD : ∀ i j k m : Fin 4, D i ≠ D j → D i + D m = D j + D k → D i = D k := by decide
    have hmemD : ∀ x ∈ ([0, 1, 3, 9] : List (Fin 13)), ∃ i : Fin 4, x = D i := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    intro a ha b hb c hc d hd hab hsum
    obtain ⟨ia, rfl⟩ := hmemD a ha
    obtain ⟨ib, rfl⟩ := hmemD b hb
    obtain ⟨ic, rfl⟩ := hmemD c hc
    obtain ⟨id', rfl⟩ := hmemD d hd
    exact hD ia ib ic id' hab hsum
  let Eset : Finset (Fin 13 × Fin 12) := Finset.univ.filter fun pl =>
    pl.1.val = pl.2.val ∨ pl.1.val = (pl.2.val + 1) % 13 ∨
    pl.1.val = (pl.2.val + 3) % 13 ∨ pl.1.val = (pl.2.val + 9) % 13
  have hEset_card : Eset.card = 48 := by
    let fiber (l : Fin 12) : Finset (Fin 13 × Fin 12) :=
      {(⟨l.val, by omega⟩, l), (⟨(l.val + 1) % 13, Nat.mod_lt _ (by omega)⟩, l),
       (⟨(l.val + 3) % 13, Nat.mod_lt _ (by omega)⟩, l),
       (⟨(l.val + 9) % 13, Nat.mod_lt _ (by omega)⟩, l)}
    have hEq : Eset = Finset.univ.biUnion fiber := by
      ext ⟨p, l⟩
      simp only [Eset, fiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff]
      constructor
      · intro h
        refine ⟨l, ?_⟩
        rcases h with h | h | h | h
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr (Or.inl ⟨h, rfl⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h, rfl⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h, rfl⟩))
      · rintro ⟨l', ⟨hp, hl⟩ | ⟨hp, hl⟩ | ⟨hp, hl⟩ | ⟨hp, hl⟩⟩
        · exact Or.inl (by rw [hp, ← hl])
        · exact Or.inr (Or.inl (by rw [hp, ← hl]))
        · exact Or.inr (Or.inr (Or.inl (by rw [hp, ← hl])))
        · exact Or.inr (Or.inr (Or.inr (by rw [hp, ← hl])))
    have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin 12)) : Set (Fin 12)) fiber := by
      intro l1 _ l2 _ hne
      exact Finset.disjoint_left.2 fun pl h1 h2 => by
        simp only [fiber, Finset.mem_insert, Finset.mem_singleton] at h1 h2
        have e1 : pl.2 = l1 := by rcases h1 with rfl | rfl | rfl | rfl <;> rfl
        have e2 : pl.2 = l2 := by rcases h2 with rfl | rfl | rfl | rfl <;> rfl
        exact hne (e1.symm.trans e2)
    have hfc : ∀ l : Fin 12, (fiber l).card = 4 := by
      intro l
      have hl : l.val < 12 := l.isLt
      have h12 : (⟨l.val, by omega⟩ : Fin 13) ≠ ⟨(l.val + 1) % 13, Nat.mod_lt _ (by omega)⟩ := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      have h13 : (⟨l.val, by omega⟩ : Fin 13) ≠ ⟨(l.val + 3) % 13, Nat.mod_lt _ (by omega)⟩ := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      have h14 : (⟨l.val, by omega⟩ : Fin 13) ≠ ⟨(l.val + 9) % 13, Nat.mod_lt _ (by omega)⟩ := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      have h23 : (⟨(l.val + 1) % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) ≠ ⟨(l.val + 3) % 13, Nat.mod_lt _ (by omega)⟩ := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      have h24 : (⟨(l.val + 1) % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) ≠ ⟨(l.val + 9) % 13, Nat.mod_lt _ (by omega)⟩ := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      have h34 : (⟨(l.val + 3) % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) ≠ ⟨(l.val + 9) % 13, Nat.mod_lt _ (by omega)⟩ := by
        intro h; have := congrArg Fin.val h; dsimp only at this; omega
      dsimp only [fiber]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simp only [Finset.mem_singleton, Prod.mk.injEq]; rintro ⟨h, _⟩; exact h34 h
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rintro (⟨h, _⟩ | ⟨h, _⟩); exact h23 h; exact h24 h
      · simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩); exact h12 h; exact h13 h; exact h14 h
    rw [hEq, Finset.card_biUnion hdisj]
    calc ∑ l : Fin 12, (fiber l).card = ∑ _l : Fin 12, 4 := Finset.sum_congr rfl fun l _ => hfc l
      _ = 48 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_length : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl stepWire w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      omega
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by
        simp only [stepWire, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (stepWire w g) i hlt]
      simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro w j hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by
          simp only [stepWire, List.length_append, List.length_cons, List.length_nil]; omega
        rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · simp only [hi, ↓reduceIte]
          rw [foldl_getD_lt gs (stepWire w g) i (by
            simp only [stepWire, List.length_append, List.length_cons, List.length_nil]; omega)]
          simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · simp only [hi, ↓reduceIte]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simp only [List.length_cons] at hj; omega
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by
          simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key
  have val_input : ∀ (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : Fin n),
      wireVal n C i.val x = x i := by
    intro n C x i
    unfold wireVal Circuit.wires
    have hlt : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
    change (C.gates.foldl stepWire (List.ofFn x)).getD i.val false = x i
    rw [foldl_getD_lt C.gates (List.ofFn x) i.val hlt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt, Option.getD_some, List.getElem_ofFn]
  have val_ge : ∀ (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ),
      n + C.gates.length ≤ u → wireVal n C u x = false := by
    intro n C x u hu
    unfold wireVal Circuit.wires
    change (C.gates.foldl stepWire (List.ofFn x)).getD u false = false
    apply getD_ge
    rw [foldl_length, List.length_ofFn]
    exact hu
  have val_gate : ∀ (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length),
      wireVal n C (n + j) x =
        (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
          if i < n + j then wireVal n C i x else false) := by
    intro n C x j hj
    unfold wireVal Circuit.wires
    have key := foldl_getD_gate C.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at key
    have hgat : gateAt C j = C.gates[j] := by
      unfold gateAt; simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [hgat]
    exact key
  let Inc13 (p l : Fin 13) : Prop :=
    p = l ∨ p = l + (1 : Fin 13) ∨ p = l + (3 : Fin 13) ∨ p = l + (9 : Fin 13)
  have hE25_mem : ∀ u v : ℕ, (u, v) ∈ E25 ↔
      ∃ k < 12, v = 13 + k ∧ (u = k ∨ u = (k + 1) % 13 ∨ u = (k + 3) % 13 ∨ u = (k + 9) % 13) := by
    intro u v
    simp only [E25, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq]
    constructor
    · rintro ⟨k, hk, ⟨hu, rfl⟩ | ⟨hu, rfl⟩ | ⟨hu, rfl⟩ | ⟨hu, rfl⟩⟩
      · exact ⟨k, hk, rfl, Or.inl hu⟩
      · exact ⟨k, hk, rfl, Or.inr (Or.inl hu)⟩
      · exact ⟨k, hk, rfl, Or.inr (Or.inr (Or.inl hu))⟩
      · exact ⟨k, hk, rfl, Or.inr (Or.inr (Or.inr hu))⟩
    · rintro ⟨k, hk, rfl, h1 | h2 | h3 | h4⟩
      · exact ⟨k, hk, Or.inl ⟨h1, rfl⟩⟩
      · exact ⟨k, hk, Or.inr (Or.inl ⟨h2, rfl⟩)⟩
      · exact ⟨k, hk, Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩))⟩
      · exact ⟨k, hk, Or.inr (Or.inr (Or.inr ⟨h4, rfl⟩))⟩
  have hInc13_val : ∀ (p : Fin 13) (l : Fin 12),
      Inc13 p ⟨l.val, by omega⟩ ↔
        (p.val = l.val ∨ p.val = (l.val + 1) % 13 ∨ p.val = (l.val + 3) % 13 ∨ p.val = (l.val + 9) % 13) := by
    intro p l
    simp only [Inc13, Fin.ext_iff, Fin.val_add]
    have h1 : (1 : Fin 13).val = 1 := rfl
    have h3 : (3 : Fin 13).val = 3 := rfl
    have h9 : (9 : Fin 13).val = 9 := rfl
    rw [h1, h3, h9]
  have hAdj_iff : ∀ u v : Fin 25, G.Adj u v ↔
      (∃ (p : Fin 13) (l : Fin 12), Inc13 p ⟨l.val, by omega⟩ ∧
        ((u = Fin.castAdd 12 p ∧ v = Fin.natAdd 13 l) ∨
         (u = Fin.natAdd 13 l ∧ v = Fin.castAdd 12 p))) := by
    intro u v
    change (u ≠ v ∧ ((u.val, v.val) ∈ E25 ∨ (v.val, u.val) ∈ E25)) ↔ _
    rw [hE25_mem, hE25_mem]
    constructor
    · rintro ⟨_, ⟨k, hk, hv, hu⟩ | ⟨k, hk, hu, hv⟩⟩
      · have hu13 : u.val < 13 := by omega
        refine ⟨⟨u.val, hu13⟩, ⟨k, hk⟩, (hInc13_val ⟨u.val, hu13⟩ ⟨k, hk⟩).2 hu, Or.inl ⟨?_, ?_⟩⟩
        · apply Fin.ext; rfl
        · apply Fin.ext; exact hv
      · have hv13 : v.val < 13 := by omega
        refine ⟨⟨v.val, hv13⟩, ⟨k, hk⟩, (hInc13_val ⟨v.val, hv13⟩ ⟨k, hk⟩).2 hv, Or.inr ⟨?_, ?_⟩⟩
        · apply Fin.ext; exact hu
        · apply Fin.ext; rfl
    · rintro ⟨p, l, hinc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · refine ⟨?_, Or.inl ⟨l.val, l.isLt, rfl, (hInc13_val p l).1 hinc⟩⟩
        intro heq; have := congrArg Fin.val heq; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
      · refine ⟨?_, Or.inr ⟨l.val, l.isLt, rfl, (hInc13_val p l).1 hinc⟩⟩
        intro heq; have := congrArg Fin.val heq; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  have hGraphFun_iff : ∀ x : Fin 25 → Bool,
      graphFun G ∅ x = true ↔
        ∃ (p : Fin 13) (l : Fin 12), Inc13 p ⟨l.val, by omega⟩ ∧
          x (Fin.castAdd 12 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    intro x
    unfold graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, hadj, hxu, hxv⟩
      obtain ⟨p, l, hinc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (hAdj_iff u v).1 hadj
      · exact ⟨p, l, hinc, hxu, hxv⟩
      · exact ⟨p, l, hinc, hxv, hxu⟩
    · rintro ⟨p, l, hinc, hxp, hxl⟩
      exact ⟨Fin.castAdd 12 p, Fin.natAdd 13 l, (hAdj_iff _ _).2 ⟨p, l, hinc, Or.inl ⟨rfl, rfl⟩⟩,
        hxp, hxl⟩
  have hNoC4 : ∀ a b : Fin 25, a ≠ b → ∀ u v : Fin 25, u ≠ v →
      G.Adj a u → G.Adj a v → G.Adj b u → G.Adj b v → False := by
    intro a b hab u v huv hau hav hbu hbv
    have hInc_mem : ∀ p l : Fin 13, Inc13 p l → p - l ∈ ([0, 1, 3, 9] : List (Fin 13)) := by
      intro p l h
      rcases h with rfl | rfl | rfl | rfl <;> simp
    obtain ⟨pa1, la1, h1, ⟨ha1, hu1⟩ | ⟨ha1, hu1⟩⟩ := (hAdj_iff a u).1 hau
    · obtain ⟨pa2, la2, h2, ⟨ha2, hv2⟩ | ⟨ha2, _⟩⟩ := (hAdj_iff a v).1 hav
      · obtain ⟨pb1, lb1, h3, ⟨hb1, hu3⟩ | ⟨_, hu3⟩⟩ := (hAdj_iff b u).1 hbu
        · obtain ⟨pb2, lb2, h4, ⟨hb2, hv4⟩ | ⟨hb2, _⟩⟩ := (hAdj_iff b v).1 hbv
          · have hpa : pa1 = pa2 := by apply Fin.ext; have := congrArg Fin.val (ha1.symm.trans ha2); simpa only [Fin.val_castAdd] using this
            have hpb : pb1 = pb2 := by apply Fin.ext; have := congrArg Fin.val (hb1.symm.trans hb2); simpa only [Fin.val_castAdd] using this
            have hla : la1 = lb1 := by apply Fin.ext; have := congrArg Fin.val (hu1.symm.trans hu3); simp only [Fin.val_natAdd] at this; omega
            have hlb : la2 = lb2 := by apply Fin.ext; have := congrArg Fin.val (hv2.symm.trans hv4); simp only [Fin.val_natAdd] at this; omega
            subst hpa; subst hpb; subst hla; subst hlb
            let l1 : Fin 13 := ⟨la1.val, by omega⟩
            let l2 : Fin 13 := ⟨la2.val, by omega⟩
            have hne_l : l1 ≠ l2 := by
              intro heq; apply huv; rw [hu1, hv2]; apply Fin.ext
              have := congrArg Fin.val heq; dsimp only [l1, l2] at this; simp only [Fin.val_natAdd]; omega
            have hne_p : pa1 ≠ pb1 := by
              intro heq; apply hab; rw [ha1, hb1, heq]
            have hne_d : pa1 - l1 ≠ pa1 - l2 := by
              intro heq; apply hne_l; exact sub_right_inj.mp heq
            have hsum : (pa1 - l1) + (pb1 - l2) = (pa1 - l2) + (pb1 - l1) := by abel
            have heq_d := hDiff4 _ (hInc_mem _ _ h1) _ (hInc_mem _ _ h2) _ (hInc_mem _ _ h3) _ (hInc_mem _ _ h4) hne_d hsum
            exact hne_p (sub_left_inj.mp heq_d)
          · have := congrArg Fin.val (hb1.symm.trans hb2); simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
        · have := congrArg Fin.val (hu1.symm.trans hu3); simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
      · have := congrArg Fin.val (ha1.symm.trans ha2); simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
    · obtain ⟨pa2, la2, h2, ⟨ha2, _⟩ | ⟨ha2, hv2⟩⟩ := (hAdj_iff a v).1 hav
      · have := congrArg Fin.val (ha1.symm.trans ha2); simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
      · obtain ⟨pb1, lb1, h3, ⟨_, hu3⟩ | ⟨hb1, hu3⟩⟩ := (hAdj_iff b u).1 hbu
        · have := congrArg Fin.val (hu1.symm.trans hu3); simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
        · obtain ⟨pb2, lb2, h4, ⟨hb2, _⟩ | ⟨hb2, hv4⟩⟩ := (hAdj_iff b v).1 hbv
          · have := congrArg Fin.val (hb1.symm.trans hb2); simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
          · have hla : la1 = la2 := by apply Fin.ext; have := congrArg Fin.val (ha1.symm.trans ha2); simp only [Fin.val_natAdd] at this; omega
            have hlb : lb1 = lb2 := by apply Fin.ext; have := congrArg Fin.val (hb1.symm.trans hb2); simp only [Fin.val_natAdd] at this; omega
            have hpa : pa1 = pb1 := by apply Fin.ext; have := congrArg Fin.val (hu1.symm.trans hu3); simpa only [Fin.val_castAdd] using this
            have hpb : pa2 = pb2 := by apply Fin.ext; have := congrArg Fin.val (hv2.symm.trans hv4); simpa only [Fin.val_castAdd] using this
            subst hla; subst hlb; subst hpa; subst hpb
            let l1 : Fin 13 := ⟨la1.val, by omega⟩
            let l2 : Fin 13 := ⟨lb1.val, by omega⟩
            have hne_l : l1 ≠ l2 := by
              intro heq; apply hab; rw [ha1, hb1]; apply Fin.ext
              have := congrArg Fin.val heq; dsimp only [l1, l2] at this; simp only [Fin.val_natAdd]; omega
            have hne_p : pa1 ≠ pa2 := by
              intro heq; apply huv; rw [hu1, hv2, heq]
            have hne_d : pa1 - l1 ≠ pa2 - l1 := by
              intro heq; apply hne_p; exact sub_left_inj.mp heq
            have hsum : (pa1 - l1) + (pa2 - l2) = (pa2 - l1) + (pa1 - l2) := by abel
            have heq_d := hDiff4 _ (hInc_mem _ _ h1) _ (hInc_mem _ _ h2) _ (hInc_mem _ _ h3) _ (hInc_mem _ _ h4) hne_d hsum
            exact hne_l (sub_right_inj.mp heq_d)
  have hDegLe4 : ∀ v : Fin 25, (Finset.univ.filter fun w : Fin 25 => G.Adj v w).card ≤ 4 := by
    intro v
    by_cases hv : v.val < 13
    · let S4 : Finset ℕ := {13 + v.val, 13 + (v.val + 12) % 13, 13 + (v.val + 10) % 13, 13 + (v.val + 4) % 13}
      have hsub : (Finset.univ.filter fun w : Fin 25 => G.Adj v w).image Fin.val ⊆ S4 := by
        intro n hn
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hn
        rw [Finset.mem_filter] at hw
        obtain ⟨p, l, hinc, ⟨hv1, hw1⟩ | ⟨hv1, _⟩⟩ := (hAdj_iff v w).1 hw.2
        · have hp : p.val = v.val := by have := congrArg Fin.val hv1; simpa only [Fin.val_castAdd] using this.symm
          have hwv : w.val = 13 + l.val := by have := congrArg Fin.val hw1; simpa only [Fin.val_natAdd] using this
          have hl := (hInc13_val p l).1 hinc
          rw [hp] at hl
          simp only [S4, Finset.mem_insert, Finset.mem_singleton, hwv]
          have hll : l.val < 12 := l.isLt
          omega
        · have := congrArg Fin.val hv1; simp only [Fin.val_natAdd] at this; omega
      have hcard1 : ((Finset.univ.filter fun w : Fin 25 => G.Adj v w).image Fin.val).card =
          (Finset.univ.filter fun w : Fin 25 => G.Adj v w).card :=
        Finset.card_image_of_injective _ Fin.val_injective
      rw [← hcard1]
      refine (Finset.card_le_card hsub).trans ?_
      dsimp only [S4]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp only [Finset.card_singleton, le_refl])))))
    · let S4 : Finset ℕ := {v.val - 13, (v.val - 12) % 13, (v.val - 10) % 13, (v.val - 4) % 13}
      have hsub : (Finset.univ.filter fun w : Fin 25 => G.Adj v w).image Fin.val ⊆ S4 := by
        intro n hn
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hn
        rw [Finset.mem_filter] at hw
        obtain ⟨p, l, hinc, ⟨hv1, _⟩ | ⟨hv1, hw1⟩⟩ := (hAdj_iff v w).1 hw.2
        · have := congrArg Fin.val hv1; simp only [Fin.val_castAdd] at this; omega
        · have hl : v.val = 13 + l.val := by have := congrArg Fin.val hv1; simpa only [Fin.val_natAdd] using this
          have hwv : w.val = p.val := by have := congrArg Fin.val hw1; simpa only [Fin.val_castAdd] using this
          have hpl := (hInc13_val p l).1 hinc
          simp only [S4, Finset.mem_insert, Finset.mem_singleton, hwv]
          have hll : l.val < 12 := l.isLt
          omega
      have hcard1 : ((Finset.univ.filter fun w : Fin 25 => G.Adj v w).image Fin.val).card =
          (Finset.univ.filter fun w : Fin 25 => G.Adj v w).card :=
        Finset.card_image_of_injective _ Fin.val_injective
      rw [← hcard1]
      refine (Finset.card_le_card hsub).trans ?_
      dsimp only [S4]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
        (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp only [Finset.card_singleton, le_refl])))))
  have hSingleFalse : ∀ u : Fin 25, graphFun G ∅ (fun w => decide (w = u)) = false := by
    intro u
    cases h' : graphFun G ∅ (fun w => decide (w = u))
    · rfl
    · obtain ⟨p, l, _, hp, hl⟩ := (hGraphFun_iff _).1 h'
      simp only [decide_eq_true_eq] at hp hl
      have heq := congrArg Fin.val (hp.trans hl.symm)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
      omega
  have hZeroFalse : graphFun G ∅ (fun _ => false) = false := by
    cases h' : graphFun G ∅ (fun _ => false)
    · rfl
    · obtain ⟨_, _, _, hp, _⟩ := (hGraphFun_iff _).1 h'
      cases hp
  have hEdgeTrue : ∀ u v : Fin 25, G.Adj u v → graphFun G ∅ (pairInput u v) = true := by
    intro u v hadj
    unfold graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact ⟨u, v, hadj, pairInput_left u v, pairInput_right u v⟩
  have hPairTrue : graphFun G ∅ (pairInput ⟨0, by omega⟩ ⟨13, by omega⟩) = true := by
    apply hEdgeTrue
    rw [hAdj_iff]
    exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩, Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
  intro C x2 hmono hcomp
  by_contra hlt58
  have hC_sz : C.size ≤ 57 := by omega
  have hSymm : ∃ C1 : Circuit, C1.size = C.size ∧ Monotone2 C1 ∧
      ∀ x : Fin 26 → Bool, x ⟨25, by omega⟩ = false →
        (C1.eval (List.ofFn x) = true ↔
          ∃ (p l : Fin 13), Inc13 p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
    clear h_one_dirty h_antichain h_chain hDiff4 hEset_card Eset hE25_mem hInc13_val hAdj_iff hGraphFun_iff hNoC4 hDegLe4 hSingleFalse hZeroFalse hEdgeTrue hPairTrue hlt58 hC_sz G E25 foldl_length foldl_getD_lt getD_ge foldl_getD_gate val_input val_ge val_gate
    have getD_rel : ∀ (ρ : ℕ → ℕ) (hl : ∀ a, a < 26 → ρ a < 26) (hb : ∀ a, 26 ≤ a → ρ a = a)
        (e : Fin 26 → Bool) (T : List Bool) (a : ℕ),
        (List.ofFn e ++ T).getD (ρ a) false =
          (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T).getD a false := by
      intro ρ hl hb e T a
      by_cases ha : a < 26
      · have h1 := hl a ha
        have hlen1 : ρ a < (List.ofFn e).length := by rw [List.length_ofFn]; exact h1
        have hlen2 : a < (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩)).length := by
          rw [List.length_ofFn]; exact ha
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hlen1, List.getElem?_append_left hlen2,
          List.getElem?_eq_getElem hlen1, List.getElem?_eq_getElem hlen2,
          Option.getD_some, Option.getD_some, List.getElem_ofFn, List.getElem_ofFn]
      · rw [hb a (by omega)]
        have hlen1 : (List.ofFn e).length ≤ a := by rw [List.length_ofFn]; omega
        have hlen2 : (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩)).length ≤ a := by
          rw [List.length_ofFn]; omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right hlen1, List.getElem?_append_right hlen2,
          List.length_ofFn, List.length_ofFn]
    have fold_rel : ∀ (ρ : ℕ → ℕ) (hl : ∀ a, a < 26 → ρ a < 26) (hb : ∀ a, 26 ≤ a → ρ a = a)
        (e : Fin 26 → Bool) (gs : List Gate) (T : List Bool), ∃ T' : List Bool,
        (gs.map (fun g => Gate.mk g.op (g.inputs.map ρ))).foldl stepWire (List.ofFn e ++ T) =
          List.ofFn e ++ T' ∧
        gs.foldl stepWire (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T) =
          List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T' := by
      intro ρ hl hb e gs
      induction gs with
      | nil => intro T; exact ⟨T, rfl, rfl⟩
      | cons g gs ih =>
        intro T
        have hval : (Gate.mk g.op (g.inputs.map ρ)).op.eval ((Gate.mk g.op (g.inputs.map ρ)).inputs.map
            fun i => (List.ofFn e ++ T).getD i false) =
            g.op.eval (g.inputs.map fun i =>
              (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T).getD i false) := by
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro a _
          exact getD_rel ρ hl hb e T a
        obtain ⟨T', h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i =>
          (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩) ++ T).getD i false)])
        refine ⟨T', ?_, ?_⟩
        · rw [List.map_cons, List.foldl_cons]; dsimp only [stepWire]; rw [hval, List.append_assoc]; exact h1
        · rw [List.foldl_cons]; dsimp only [stepWire]; rw [List.append_assoc]; exact h2
    have eval_rel : ∀ (ρ : ℕ → ℕ) (hl : ∀ a, a < 26 → ρ a < 26) (hb : ∀ a, 26 ≤ a → ρ a = a)
        (e : Fin 26 → Bool),
        (Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output)).eval (List.ofFn e) =
          C.eval (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩)) := by
      intro ρ hl hb e
      obtain ⟨T', h1, h2⟩ := fold_rel ρ hl hb e C.gates []
      simp only [List.append_nil] at h1 h2
      unfold Circuit.eval Circuit.wires
      change ((C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))).foldl stepWire (List.ofFn e)).getD (ρ C.output) false =
        (C.gates.foldl stepWire (List.ofFn (fun i : Fin 26 => e ⟨ρ i.val, hl i.val i.isLt⟩))).getD C.output false
      rw [h1, h2]
      exact getD_rel ρ hl hb e T' C.output
    by_cases hx2 : x2.val < 13
    · let p0 : Fin 13 := ⟨x2.val, hx2⟩
      let c : Fin 13 := (12 : Fin 13) + p0
      let ρ (w : ℕ) : ℕ :=
        if h1 : w < 13 then 13 + (c - (⟨w, h1⟩ : Fin 13)).val
        else if h2 : w < 26 then (c - (⟨w - 13, by omega⟩ : Fin 13)).val
        else w
      have hρ_lt : ∀ a, a < 26 → ρ a < 26 := by
        intro a ha
        dsimp only [ρ]
        split_ifs with h1
        · have := (c - (⟨a, h1⟩ : Fin 13)).isLt; omega
        · have := (c - (⟨a - 13, by omega⟩ : Fin 13)).isLt; omega
      have hρ_ge : ∀ a, 26 ≤ a → ρ a = a := by
        intro a ha
        dsimp only [ρ]
        simp only [show ¬ a < 13 by omega, show ¬ a < 26 by omega, ↓reduceDIte]
      refine ⟨Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output),
        List.length_map .., ?_, ?_⟩
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
        obtain ⟨hop, hlen⟩ := hmono g0 hg0
        exact ⟨hop, by simp only [List.length_map]; exact hlen⟩
      · intro x hx25
        rw [eval_rel ρ hρ_lt hρ_ge x]
        have hx'_false : (fun i : Fin 26 => x ⟨ρ i.val, hρ_lt i.val i.isLt⟩) x2 = false := by
          dsimp only
          have hρx2 : ρ x2.val = 25 := by
            dsimp only [ρ]
            simp only [hx2, ↓reduceDIte]
            have hsub : c - p0 = (12 : Fin 13) := by dsimp only [c]; abel
            change 13 + (c - p0).val = 25
            rw [hsub]; rfl
          have hidx : (⟨ρ x2.val, hρ_lt x2.val x2.isLt⟩ : Fin 26) = ⟨25, by omega⟩ := by
            apply Fin.ext; exact hρx2
          rw [hidx]; exact hx25
        rw [hcomp _ hx'_false]
        have hdual : ∀ p l : Fin 13, Inc13 p l ↔ Inc13 (c - l) (c - p) := by
          intro p l
          have hsub_eq : ∀ d : Fin 13, p = l + d ↔ c - l = (c - p) + d := by
            intro d
            constructor
            · intro h; subst h; abel
            · intro h
              have h1 : (c - l) + l + p = ((c - p) + d) + l + p := by rw [h]
              have h2 : (c - l) + l + p = c + p := by abel
              have h3 : ((c - p) + d) + l + p = c + (l + d) := by abel
              rw [h2, h3] at h1
              exact add_left_cancel h1
          exact ⟨fun h => by rcases h with h | h | h | h; exact Or.inl (by rw [h]); exact Or.inr (Or.inl ((hsub_eq 1).1 h)); exact Or.inr (Or.inr (Or.inl ((hsub_eq 3).1 h))); exact Or.inr (Or.inr (Or.inr ((hsub_eq 9).1 h))),
            fun h => by rcases h with h | h | h | h; exact Or.inl (sub_right_inj.mp h).symm; exact Or.inr (Or.inl ((hsub_eq 1).2 h)); exact Or.inr (Or.inr (Or.inl ((hsub_eq 3).2 h))); exact Or.inr (Or.inr (Or.inr ((hsub_eq 9).2 h)))⟩
        have hcast : ∀ p : Fin 13, (⟨ρ (Fin.castAdd 13 p).val, hρ_lt _ (Fin.castAdd 13 p).isLt⟩ : Fin 26) = Fin.natAdd 13 (c - p) := by
          intro p; apply Fin.ext; dsimp only [ρ]; simp only [Fin.val_castAdd, p.isLt, ↓reduceDIte, Fin.val_natAdd, Fin.eta]
        have hnat : ∀ l : Fin 13, (⟨ρ (Fin.natAdd 13 l).val, hρ_lt _ (Fin.natAdd 13 l).isLt⟩ : Fin 26) = Fin.castAdd 13 (c - l) := by
          intro l; apply Fin.ext; dsimp only [ρ]
          have h1 : ¬ 13 + l.val < 13 := by omega
          have h2 : 13 + l.val < 26 := by omega
          simp only [Fin.val_natAdd, Fin.val_castAdd, h1, h2, ↓reduceDIte, Nat.add_sub_cancel_left, Fin.eta]
        constructor
        · rintro ⟨p, l, hinc, hp, hl⟩
          rw [hcast] at hp; rw [hnat] at hl
          exact ⟨c - l, c - p, (hdual p l).1 hinc, hl, hp⟩
        · rintro ⟨p, l, hinc, hp, hl⟩
          refine ⟨c - l, c - p, (hdual (c - l) (c - p)).2 (by simpa only [sub_sub_cancel] using hinc), ?_, ?_⟩
          · rw [hcast]; simpa only [sub_sub_cancel] using hl
          · rw [hnat]; simpa only [sub_sub_cancel] using hp
    · let l0 : Fin 13 := ⟨x2.val - 13, by omega⟩
      let c : Fin 13 := (12 : Fin 13) - l0
      let ρ (w : ℕ) : ℕ :=
        if h1 : w < 13 then ((⟨w, h1⟩ : Fin 13) + c).val
        else if h2 : w < 26 then 13 + ((⟨w - 13, by omega⟩ : Fin 13) + c).val
        else w
      have hρ_lt : ∀ a, a < 26 → ρ a < 26 := by
        intro a ha
        dsimp only [ρ]
        split_ifs with h1
        · have := ((⟨a, h1⟩ : Fin 13) + c).isLt; omega
        · have := ((⟨a - 13, by omega⟩ : Fin 13) + c).isLt; omega
      have hρ_ge : ∀ a, 26 ≤ a → ρ a = a := by
        intro a ha
        dsimp only [ρ]
        simp only [show ¬ a < 13 by omega, show ¬ a < 26 by omega, ↓reduceDIte]
      refine ⟨Circuit.mk (C.gates.map (fun g => Gate.mk g.op (g.inputs.map ρ))) (ρ C.output),
        List.length_map .., ?_, ?_⟩
      · intro g hg
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
        obtain ⟨hop, hlen⟩ := hmono g0 hg0
        exact ⟨hop, by simp only [List.length_map]; exact hlen⟩
      · intro x hx25
        rw [eval_rel ρ hρ_lt hρ_ge x]
        have hx'_false : (fun i : Fin 26 => x ⟨ρ i.val, hρ_lt i.val i.isLt⟩) x2 = false := by
          dsimp only
          have hρx2 : ρ x2.val = 25 := by
            dsimp only [ρ]
            simp only [hx2, x2.isLt, ↓reduceDIte]
            have hadd : l0 + c = (12 : Fin 13) := by dsimp only [c]; abel
            change 13 + (l0 + c).val = 25
            rw [hadd]; rfl
          have hidx : (⟨ρ x2.val, hρ_lt x2.val x2.isLt⟩ : Fin 26) = ⟨25, by omega⟩ := by
            apply Fin.ext; exact hρx2
          rw [hidx]; exact hx25
        rw [hcomp _ hx'_false]
        have htrans : ∀ p l : Fin 13, Inc13 p l ↔ Inc13 (p + c) (l + c) := by
          intro p l
          have hadd_eq : ∀ d : Fin 13, p = l + d ↔ p + c = (l + c) + d := by
            intro d
            constructor
            · intro h; subst h; abel
            · intro h
              have : p + c = (l + d) + c := by rw [h]; abel
              exact add_right_cancel this
          exact ⟨fun h => by rcases h with h | h | h | h; exact Or.inl (by rw [h]); exact Or.inr (Or.inl ((hadd_eq 1).1 h)); exact Or.inr (Or.inr (Or.inl ((hadd_eq 3).1 h))); exact Or.inr (Or.inr (Or.inr ((hadd_eq 9).1 h))),
            fun h => by rcases h with h | h | h | h; exact Or.inl (add_right_cancel h); exact Or.inr (Or.inl ((hadd_eq 1).2 h)); exact Or.inr (Or.inr (Or.inl ((hadd_eq 3).2 h))); exact Or.inr (Or.inr (Or.inr ((hadd_eq 9).2 h)))⟩
        have hcast : ∀ p : Fin 13, (⟨ρ (Fin.castAdd 13 p).val, hρ_lt _ (Fin.castAdd 13 p).isLt⟩ : Fin 26) = Fin.castAdd 13 (p + c) := by
          intro p; apply Fin.ext; dsimp only [ρ]; simp only [Fin.val_castAdd, p.isLt, ↓reduceDIte, Fin.eta]
        have hnat : ∀ l : Fin 13, (⟨ρ (Fin.natAdd 13 l).val, hρ_lt _ (Fin.natAdd 13 l).isLt⟩ : Fin 26) = Fin.natAdd 13 (l + c) := by
          intro l; apply Fin.ext; dsimp only [ρ]
          have h1 : ¬ 13 + l.val < 13 := by omega
          have h2 : 13 + l.val < 26 := by omega
          simp only [Fin.val_natAdd, h1, h2, ↓reduceDIte, Nat.add_sub_cancel_left, Fin.eta]
        constructor
        · rintro ⟨p, l, hinc, hp, hl⟩
          rw [hcast] at hp; rw [hnat] at hl
          exact ⟨p + c, l + c, (htrans p l).1 hinc, hp, hl⟩
        · rintro ⟨p, l, hinc, hp, hl⟩
          refine ⟨p - c, l - c, (htrans (p - c) (l - c)).2 (by simpa only [sub_add_cancel] using hinc), ?_, ?_⟩
          · rw [hcast]; simpa only [sub_add_cancel] using hp
          · rw [hnat]; simpa only [sub_add_cancel] using hl
  obtain ⟨C1, hC1_sz, hC1_mono, hC1_comp⟩ := hSymm
  let ext26 (y : Fin 25 → Bool) : Fin 26 → Bool :=
    fun i => if h : i.val < 25 then y ⟨i.val, h⟩ else false
  have hC1_on_25 : ∀ y : Fin 25 → Bool, C1.eval (List.ofFn (ext26 y)) = graphFun G ∅ y := by
    intro y
    have h25 : ext26 y ⟨25, by omega⟩ = false := by dsimp only [ext26]; simp only [lt_self_iff_false, ↓reduceDIte]
    have hiff := hC1_comp (ext26 y) h25
    have hiff2 : (∃ (p l : Fin 13), Inc13 p l ∧ ext26 y (Fin.castAdd 13 p) = true ∧ ext26 y (Fin.natAdd 13 l) = true) ↔
        graphFun G ∅ y = true := by
      rw [hGraphFun_iff]
      constructor
      · rintro ⟨p, l, hinc, hp, hl⟩
        have hl12 : l.val < 12 := by
          by_contra hge
          have h25' : ¬ (Fin.natAdd 13 l : Fin 26).val < 25 := by simp only [Fin.val_natAdd]; omega
          dsimp only [ext26] at hl
          simp only [h25', ↓reduceDIte] at hl
          cases hl
        refine ⟨p, ⟨l.val, hl12⟩, hinc, ?_, ?_⟩
        · dsimp only [ext26] at hp
          have hlt : (Fin.castAdd 13 p : Fin 26).val < 25 := by simp only [Fin.val_castAdd]; omega
          simp only [hlt, ↓reduceDIte] at hp
          exact hp
        · dsimp only [ext26] at hl
          have hlt : (Fin.natAdd 13 l : Fin 26).val < 25 := by simp only [Fin.val_natAdd]; omega
          simp only [hlt, ↓reduceDIte] at hl
          exact hl
      · rintro ⟨p, l, hinc, hp, hl⟩
        refine ⟨p, ⟨l.val, by omega⟩, hinc, ?_, ?_⟩
        · dsimp only [ext26]
          have hlt : (Fin.castAdd 13 p : Fin 26).val < 25 := by simp only [Fin.val_castAdd]; omega
          simp only [hlt, ↓reduceDIte]
          exact hp
        · dsimp only [ext26]
          have hlt : (Fin.natAdd 13 (⟨l.val, by omega⟩ : Fin 13) : Fin 26).val < 25 := by simp only [Fin.val_natAdd]; omega
          simp only [hlt, ↓reduceDIte]
          exact hl
    have hfull : C1.eval (List.ofFn (ext26 y)) = true ↔ graphFun G ∅ y = true := hiff.trans hiff2
    cases h1 : C1.eval (List.ofFn (ext26 y))
    · cases h2 : graphFun G ∅ y
      · rfl
      · exact absurd (hfull.2 h2) (by rw [h1]; decide)
    · cases h2 : graphFun G ∅ y
      · exact absurd (hfull.1 h1) (by rw [h2]; decide)
      · rfl
  have hCanon : ∃ C2 : Circuit, IsAO2 25 C2 ∧ C2.size ≤ C1.size ∧ circuitFun 25 C2 = graphFun G ∅ := by
    clear h_one_dirty h_antichain h_chain hDiff4 hEset_card Eset hE25_mem hInc13_val hAdj_iff hGraphFun_iff hNoC4 hDegLe4 hSingleFalse hEdgeTrue hlt58 hC_sz hC1_sz hC1_comp C x2 hmono hcomp Inc13 foldl_getD_lt foldl_getD_gate val_input val_ge val_gate
    have hprop : ∀ gs : List Gate,
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        ∃ (gs' : List Gate) (M : ℕ → Bool × Bool × ℕ),
          gs'.length ≤ gs.length ∧
          (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
          ReadsBack 25 ⟨gs', 0⟩ ∧
          (∀ w < 26 + gs.length, (M w).1 = false → (M w).2.2 < 25 + gs'.length) ∧
          (∀ (y : Fin 25 → Bool) (w : ℕ), w < 26 + gs.length →
            (gs.foldl stepWire (List.ofFn (ext26 y))).getD w false =
              if (M w).1 then (M w).2.1
              else (gs'.foldl stepWire (List.ofFn y)).getD (M w).2.2 false) := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil =>
        intro _
        refine ⟨[], fun w => if w < 25 then (false, false, w) else (true, false, 0),
          le_refl 0, (fun _ h => by cases h), (fun j hj => by simp only [List.length_nil] at hj; omega), ?_, ?_⟩
        · intro w hw hM
          by_cases h25 : w < 25
          · simp only [h25, ↓reduceIte, List.length_nil, Nat.add_zero]
          · simp only [h25, ↓reduceIte] at hM; cases hM
        · intro y w hw
          simp only [List.foldl_nil, List.length_nil] at hw ⊢
          by_cases h25 : w < 25
          · simp only [h25, ↓reduceIte, Bool.false_eq_true, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show w < (List.ofFn (ext26 y)).length by rw [List.length_ofFn]; omega),
              List.getElem?_eq_getElem (show w < (List.ofFn y).length by rw [List.length_ofFn]; omega),
              List.getElem_ofFn, Option.getD_some, ext26, ↓reduceDIte]
          · have hw25 : w = 25 := by omega
            subst hw25
            simp only [show ¬ (25 : ℕ) < 25 by omega, ↓reduceIte, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show 25 < (List.ofFn (ext26 y)).length by rw [List.length_ofFn]; omega),
              List.getElem_ofFn, Option.getD_some, ext26, ↓reduceDIte]
      | append_singleton gs g ih =>
        intro hgs
        have hgs0 : ∀ g0 ∈ gs, (g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs.length ≤ 2 :=
          fun g0 hg0 => hgs g0 (List.mem_append_left _ hg0)
        have hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
          hgs g (List.mem_append_right _ (List.mem_singleton_self _))
        obtain ⟨gs', M, hlen, hgs'ok, hrb, hMlt, hMeval⟩ := ih hgs0
        let k := gs.length
        have hstep_old : ∀ (y : Fin 25 → Bool) (w : ℕ), w < 26 + k →
            ((gs ++ [g]).foldl stepWire (List.ofFn (ext26 y))).getD w false =
              (gs.foldl stepWire (List.ofFn (ext26 y))).getD w false := by
          intro y w hw
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hlw : w < (gs.foldl stepWire (List.ofFn (ext26 y))).length := by
            rw [foldl_length, List.length_ofFn]; exact hw
          change ((gs.foldl stepWire (List.ofFn (ext26 y))) ++ [_]).getD w false = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlw, ← List.getD_eq_getElem?_getD]
        have hstep_new : ∀ (y : Fin 25 → Bool),
            ((gs ++ [g]).foldl stepWire (List.ofFn (ext26 y))).getD (26 + k) false =
              g.op.eval (g.inputs.map fun i => (gs.foldl stepWire (List.ofFn (ext26 y))).getD i false) := by
          intro y
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hlw : (gs.foldl stepWire (List.ofFn (ext26 y))).length = 26 + k := by
            rw [foldl_length, List.length_ofFn]
          change ((gs.foldl stepWire (List.ofFn (ext26 y))) ++ [_]).getD (26 + k) false = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_of_eq hlw), hlw, Nat.sub_self,
            List.getElem?_cons_zero, Option.getD_some]
        let Meff (w : ℕ) : Bool × Bool × ℕ := if w < 26 + k then M w else (true, false, 0)
        have hMeff_lt : ∀ w, (Meff w).1 = false → (Meff w).2.2 < 25 + gs'.length := by
          intro w hw
          dsimp only [Meff] at hw ⊢
          by_cases hwk : w < 26 + k
          · simp only [hwk, ↓reduceIte] at hw ⊢; exact hMlt w hwk hw
          · simp only [hwk, ↓reduceIte] at hw; cases hw
        have hMeff_eval : ∀ (y : Fin 25 → Bool) (w : ℕ),
            (gs.foldl stepWire (List.ofFn (ext26 y))).getD w false =
              if (Meff w).1 then (Meff w).2.1
              else (gs'.foldl stepWire (List.ofFn y)).getD (Meff w).2.2 false := by
          intro y w
          dsimp only [Meff]
          by_cases hwk : w < 26 + k
          · simp only [hwk, ↓reduceIte]; exact hMeval y w hwk
          · simp only [hwk, ↓reduceIte]
            apply getD_ge; rw [foldl_length, List.length_ofFn]; omega
        have hno_add : ∀ (entry : Bool × Bool × ℕ),
            (entry.1 = false → entry.2.2 < 25 + gs'.length) →
            (∀ y : Fin 25 → Bool,
              g.op.eval (g.inputs.map fun i => (gs.foldl stepWire (List.ofFn (ext26 y))).getD i false) =
                if entry.1 then entry.2.1 else (gs'.foldl stepWire (List.ofFn y)).getD entry.2.2 false) →
            ∃ (gs'' : List Gate) (M' : ℕ → Bool × Bool × ℕ),
              gs''.length ≤ (gs ++ [g]).length ∧
              (∀ g0 ∈ gs'', (g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs.length = 2) ∧
              ReadsBack 25 ⟨gs'', 0⟩ ∧
              (∀ w < 26 + (gs ++ [g]).length, (M' w).1 = false → (M' w).2.2 < 25 + gs''.length) ∧
              (∀ (y : Fin 25 → Bool) (w : ℕ), w < 26 + (gs ++ [g]).length →
                ((gs ++ [g]).foldl stepWire (List.ofFn (ext26 y))).getD w false =
                  if (M' w).1 then (M' w).2.1
                  else (gs''.foldl stepWire (List.ofFn y)).getD (M' w).2.2 false) := by
          intro entry hentry_lt hentry_ev
          refine ⟨gs', fun w => if w = 26 + k then entry else M w,
            by simp only [List.length_append, List.length_cons, List.length_nil]; omega, hgs'ok, hrb, ?_, ?_⟩
          · intro w hw hM'
            simp only [List.length_append, List.length_cons, List.length_nil] at hw
            by_cases heq : w = 26 + k
            · simp only [heq, ↓reduceIte] at hM' ⊢; exact hentry_lt hM'
            · simp only [heq, ↓reduceIte] at hM' ⊢
              exact hMlt w (by omega) hM'
          · intro y w hw
            simp only [List.length_append, List.length_cons, List.length_nil] at hw
            by_cases heq : w = 26 + k
            · subst heq; simp only [↓reduceIte]; rw [hstep_new]; exact hentry_ev y
            · simp only [heq, ↓reduceIte]
              have hw' : w < 26 + k := by dsimp only [k]; omega
              rw [hstep_old y w hw', hMeval y w hw']
        have hadd_one : ∀ (op : GateOp) (u0 u1 : ℕ),
            (op = GateOp.and ∨ op = GateOp.or) →
            u0 < 25 + gs'.length → u1 < 25 + gs'.length →
            (∀ y : Fin 25 → Bool,
              g.op.eval (g.inputs.map fun i => (gs.foldl stepWire (List.ofFn (ext26 y))).getD i false) =
                op.eval [(gs'.foldl stepWire (List.ofFn y)).getD u0 false,
                         (gs'.foldl stepWire (List.ofFn y)).getD u1 false]) →
            ∃ (gs'' : List Gate) (M' : ℕ → Bool × Bool × ℕ),
              gs''.length ≤ (gs ++ [g]).length ∧
              (∀ g0 ∈ gs'', (g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs.length = 2) ∧
              ReadsBack 25 ⟨gs'', 0⟩ ∧
              (∀ w < 26 + (gs ++ [g]).length, (M' w).1 = false → (M' w).2.2 < 25 + gs''.length) ∧
              (∀ (y : Fin 25 → Bool) (w : ℕ), w < 26 + (gs ++ [g]).length →
                ((gs ++ [g]).foldl stepWire (List.ofFn (ext26 y))).getD w false =
                  if (M' w).1 then (M' w).2.1
                  else (gs''.foldl stepWire (List.ofFn y)).getD (M' w).2.2 false) := by
          intro op u0 u1 hop hu0 hu1 hev
          let g' : Gate := ⟨op, [u0, u1]⟩
          refine ⟨gs' ++ [g'], fun w => if w = 26 + k then (false, false, 25 + gs'.length) else M w,
            by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_⟩
          · intro g0 hg0
            rcases List.mem_append.1 hg0 with h1 | h2
            · exact hgs'ok g0 h1
            · rw [List.mem_singleton.1 h2]; exact ⟨hop, rfl⟩
          · intro j hj i hi
            simp only [List.length_append, List.length_singleton] at hj
            by_cases hlt : j < gs'.length
            · have hgat : gateAt ⟨gs' ++ [g'], 0⟩ j = gateAt ⟨gs', 0⟩ j := by
                unfold gateAt; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
              rw [hgat] at hi
              exact hrb j hlt i hi
            · have hj' : j = gs'.length := by omega
              subst hj'
              have hgat : gateAt ⟨gs' ++ [g'], 0⟩ gs'.length = g' := by
                unfold gateAt; simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
                  Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
              rw [hgat] at hi
              simp only [g', List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl <;> assumption
          · intro w hw hM'
            simp only [List.length_append, List.length_singleton] at hw ⊢
            by_cases heq : w = 26 + k
            · simp only [heq, ↓reduceIte]; omega
            · simp only [heq, ↓reduceIte] at hM' ⊢
              have hw' : w < 26 + k := by dsimp only [k]; omega
              have := hMlt w hw' hM'; omega
          · intro y w hw
            simp only [List.length_append, List.length_singleton] at hw
            have hgs'_old : ∀ u < 25 + gs'.length,
                ((gs' ++ [g']).foldl stepWire (List.ofFn y)).getD u false =
                  (gs'.foldl stepWire (List.ofFn y)).getD u false := by
              intro u hu
              rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
              have hlu : u < (gs'.foldl stepWire (List.ofFn y)).length := by
                rw [foldl_length, List.length_ofFn]; exact hu
              change ((gs'.foldl stepWire (List.ofFn y)) ++ [_]).getD u false = _
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlu, ← List.getD_eq_getElem?_getD]
            by_cases heq : w = 26 + k
            · subst heq
              simp only [↓reduceIte, Bool.false_eq_true]
              rw [hstep_new, hev y]
              rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
              have hlen' : (gs'.foldl stepWire (List.ofFn y)).length = 25 + gs'.length := by
                rw [foldl_length, List.length_ofFn]
              change _ = ((gs'.foldl stepWire (List.ofFn y)) ++ [_]).getD (25 + gs'.length) false
              conv_rhs =>
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_of_eq hlen'), hlen', Nat.sub_self,
                  List.getElem?_cons_zero, Option.getD_some]
              rfl
            · simp only [heq, ↓reduceIte]
              have hw' : w < 26 + k := by dsimp only [k]; omega
              rw [hstep_old y w hw', hMeval y w hw']
              cases hM1 : (M w).1
              · simp only [Bool.false_eq_true, ↓reduceIte]
                exact (hgs'_old _ (hMlt w hw' hM1)).symm
              · simp only [↓reduceIte]
        cases hins : g.inputs with
        | nil =>
          rcases hg.1 with hop | hop
          · exact hno_add (true, true, 0) (fun h => by cases h) (fun y => by simp only [hins, hop, List.map_nil, eval_and, List.all_nil, ↓reduceIte])
          · exact hno_add (true, false, 0) (fun h => by cases h) (fun y => by simp only [hins, hop, List.map_nil, eval_or, List.any_nil, ↓reduceIte])
        | cons w0 rest =>
          cases rest with
          | nil =>
            exact hno_add (Meff w0) (hMeff_lt w0) (fun y => by
              rcases hg.1 with hop | hop <;>
                simp only [hins, hop, List.map_cons, List.map_nil, eval_and, eval_or, List.all_cons, List.all_nil,
                  List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, hMeff_eval y w0])
          | cons w1 rest2 =>
            cases rest2 with
            | nil =>
              rcases hg.1 with hop | hop
              · cases hc0 : (Meff w0).1 with
                | true =>
                  cases hb0 : (Meff w0).2.1 with
                  | false =>
                    exact hno_add (true, false, 0) (fun h => by cases h) (fun y => by
                      simp only [hins, hop, List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil,
                        id_eq, Bool.and_true, hMeff_eval y w0, hc0, hb0, ↓reduceIte, Bool.false_and])
                  | true =>
                    exact hno_add (Meff w1) (hMeff_lt w1) (fun y => by
                      simp only [hins, hop, List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil,
                        id_eq, Bool.and_true, hMeff_eval y w0, hMeff_eval y w1, hc0, hb0, ↓reduceIte, Bool.true_and])
                | false =>
                  cases hc1 : (Meff w1).1 with
                  | true =>
                    cases hb1 : (Meff w1).2.1 with
                    | false =>
                      exact hno_add (true, false, 0) (fun h => by cases h) (fun y => by
                        simp only [hins, hop, List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil,
                          id_eq, Bool.and_true, hMeff_eval y w1, hc1, hb1, ↓reduceIte, Bool.and_false])
                    | true =>
                      exact hno_add (Meff w0) (hMeff_lt w0) (fun y => by
                        simp only [hins, hop, List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil,
                          id_eq, Bool.and_true, hMeff_eval y w0, hMeff_eval y w1, hc1, hb1, ↓reduceIte])
                  | false =>
                    exact hadd_one GateOp.and (Meff w0).2.2 (Meff w1).2.2 (Or.inl rfl)
                      (hMeff_lt w0 hc0) (hMeff_lt w1 hc1) (fun y => by
                        simp only [hins, hop, List.map_cons, List.map_nil, eval_and,
                          hMeff_eval y w0, hMeff_eval y w1, hc0, hc1, Bool.false_eq_true, ↓reduceIte])
              · cases hc0 : (Meff w0).1 with
                | true =>
                  cases hb0 : (Meff w0).2.1 with
                  | true =>
                    exact hno_add (true, true, 0) (fun h => by cases h) (fun y => by
                      simp only [hins, hop, List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil,
                        id_eq, Bool.or_false, hMeff_eval y w0, hc0, hb0, ↓reduceIte, Bool.true_or])
                  | false =>
                    exact hno_add (Meff w1) (hMeff_lt w1) (fun y => by
                      simp only [hins, hop, List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil,
                        id_eq, Bool.or_false, hMeff_eval y w0, hMeff_eval y w1, hc0, hb0, ↓reduceIte, Bool.false_or])
                | false =>
                  cases hc1 : (Meff w1).1 with
                  | true =>
                    cases hb1 : (Meff w1).2.1 with
                    | true =>
                      exact hno_add (true, true, 0) (fun h => by cases h) (fun y => by
                        simp only [hins, hop, List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil,
                          id_eq, Bool.or_false, hMeff_eval y w1, hc1, hb1, ↓reduceIte, Bool.or_true])
                    | false =>
                      exact hno_add (Meff w0) (hMeff_lt w0) (fun y => by
                        simp only [hins, hop, List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil,
                          id_eq, Bool.or_false, hMeff_eval y w0, hMeff_eval y w1, hc1, hb1, ↓reduceIte])
                  | false =>
                    exact hadd_one GateOp.or (Meff w0).2.2 (Meff w1).2.2 (Or.inr rfl)
                      (hMeff_lt w0 hc0) (hMeff_lt w1 hc1) (fun y => by
                        simp only [hins, hop, List.map_cons, List.map_nil, eval_or,
                          hMeff_eval y w0, hMeff_eval y w1, hc0, hc1, Bool.false_eq_true, ↓reduceIte])
            | cons _ _ =>
              have := hg.2; rw [hins] at this; simp only [List.length_cons] at this; omega
    obtain ⟨gs', M, hlen, hgs'ok, hrb, hMlt, hMeval⟩ := hprop C1.gates (fun g hg => hC1_mono g hg)
    have hout_lt : C1.output < 26 + C1.gates.length := by
      by_contra hge
      have hfalse : C1.eval (List.ofFn (ext26 (pairInput ⟨0, by omega⟩ ⟨13, by omega⟩))) = false := by
        unfold Circuit.eval Circuit.wires
        change (C1.gates.foldl stepWire _).getD C1.output false = false
        apply getD_ge; rw [foldl_length, List.length_ofFn]; omega
      rw [hC1_on_25, hPairTrue] at hfalse
      cases hfalse
    have hMout_nc : (M C1.output).1 = false := by
      cases hmc : (M C1.output).1
      · rfl
      · cases hb : (M C1.output).2.1 with
        | false =>
          have h1 := hMeval (pairInput ⟨0, by omega⟩ ⟨13, by omega⟩) C1.output hout_lt
          rw [hmc, hb] at h1
          simp only [↓reduceIte] at h1
          have h2 : C1.eval (List.ofFn (ext26 (pairInput ⟨0, by omega⟩ ⟨13, by omega⟩))) = false := h1
          rw [hC1_on_25, hPairTrue] at h2
          cases h2
        | true =>
          have h1 := hMeval (fun _ => false) C1.output hout_lt
          rw [hmc, hb] at h1
          simp only [↓reduceIte] at h1
          have h2 : C1.eval (List.ofFn (ext26 (fun _ => false))) = true := h1
          have h3 := hC1_on_25 (fun _ => false)
          rw [h3, hZeroFalse] at h2
          cases h2
    refine ⟨⟨gs', (M C1.output).2.2⟩, ⟨fun g hg => (hgs'ok g hg).1, hrb, fun g hg => (hgs'ok g hg).2⟩, hlen, ?_⟩
    funext y
    have h1 := hMeval y C1.output hout_lt
    rw [hMout_nc] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    change (gs'.foldl stepWire (List.ofFn y)).getD (M C1.output).2.2 false = graphFun G ∅ y
    rw [← h1]
    exact hC1_on_25 y
  obtain ⟨C2, hC2_ao, hC2_sz, hC2_fun⟩ := hCanon
  classical
  have hEx : ∃ s : ℕ, ∃ D : Circuit, IsAO2 25 D ∧ circuitFun 25 D = graphFun G ∅ ∧ D.size = s :=
    ⟨C2.size, C2, hC2_ao, hC2_fun, rfl⟩
  let s0 := Nat.find hEx
  obtain ⟨C0, hC0_ao, hC0_fun, hC0_s0⟩ := Nat.find_spec hEx
  have hC0_le57 : C0.size ≤ 57 := by
    have hle : s0 ≤ C2.size := Nat.find_min' hEx ⟨C2, hC2_ao, hC2_fun, rfl⟩
    omega
  have hC0_least : IsLeastAO G C0 :=
    ⟨hC0_ao, hC0_fun, fun D hDao hDfun => by
      rw [hC0_s0]; exact Nat.find_min' hEx ⟨D, hDao, hDfun, rfl⟩⟩
  have hCleanImpossible : (junk G C0).card = 0 → False := by
    clear h_one_dirty h_antichain h_chain hDiff4 hE25_mem hGraphFun_iff hZeroFalse hlt58 hC_sz hC1_sz hC1_mono hC1_comp hC1_on_25 ext26 C1 C x2 hmono hcomp hC2_ao hC2_sz hC2_fun C2 hEx s0 hC0_s0 foldl_length foldl_getD_lt getD_ge foldl_getD_gate stepWire
    intro hjunk0
    obtain ⟨hC0_op, hC0_rb, hC0_len2⟩ := hC0_ao
    have hC0_eval : ∀ x : Fin 25 → Bool, wireVal 25 C0 C0.output x = graphFun G ∅ x :=
      fun x => congrFun hC0_fun x
    have hCleanAnd : ∀ j < C0.gates.length, (gateAt C0 j).op = GateOp.and →
        ∀ x : Fin 25 → Bool, wireVal 25 C0 (25 + j) x = true → graphFun G ∅ x = true := by
      intro j hj hop x hval
      cases hgf : graphFun G ∅ x
      · exfalso
        have hmem : j ∈ junk G C0 :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop, hj, x, hval, hgf⟩
        have hpos : 0 < (junk G C0).card := Finset.card_pos.2 ⟨j, hmem⟩
        omega
      · rfl
    have hGateIn : ∀ j < C0.gates.length,
        (gateAt C0 j).inputs = [opnd C0 j 0, opnd C0 j 1] ∧
        opnd C0 j 0 < 25 + j ∧ opnd C0 j 1 < 25 + j := by
      intro j hj
      have hmem : gateAt C0 j ∈ C0.gates := by
        unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        exact List.getElem_mem hj
      have hl2 : (gateAt C0 j).inputs.length = 2 := hC0_len2 _ hmem
      cases hlist : (gateAt C0 j).inputs with
      | nil => rw [hlist] at hl2; cases hl2
      | cons a rest =>
        cases rest with
        | nil => rw [hlist] at hl2; cases hl2
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            have h0 : opnd C0 j 0 = a := by unfold opnd; rw [hlist]; rfl
            have h1 : opnd C0 j 1 = b := by unfold opnd; rw [hlist]; rfl
            rw [h0, h1]
            refine ⟨rfl, hC0_rb j hj a (by rw [hlist]; exact List.mem_cons_self ..),
              hC0_rb j hj b (by rw [hlist]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
          | cons _ _ => rw [hlist] at hl2; cases hl2
    have hValAnd : ∀ j < C0.gates.length, (gateAt C0 j).op = GateOp.and → ∀ x : Fin 25 → Bool,
        wireVal 25 C0 (25 + j) x = (wireVal 25 C0 (opnd C0 j 0) x && wireVal 25 C0 (opnd C0 j 1) x) := by
      intro j hj hop x
      obtain ⟨hins, h0, h1⟩ := hGateIn j hj
      rw [val_gate 25 C0 x j hj, hop, hins]
      simp only [List.map_cons, List.map_nil, h0, h1, ↓reduceIte, eval_and, List.all_cons,
        List.all_nil, id_eq, Bool.and_true]
    have hValOr : ∀ j < C0.gates.length, (gateAt C0 j).op = GateOp.or → ∀ x : Fin 25 → Bool,
        wireVal 25 C0 (25 + j) x = (wireVal 25 C0 (opnd C0 j 0) x || wireVal 25 C0 (opnd C0 j 1) x) := by
      intro j hj hop x
      obtain ⟨hins, h0, h1⟩ := hGateIn j hj
      rw [val_gate 25 C0 x j hj, hop, hins]
      simp only [List.map_cons, List.map_nil, h0, h1, ↓reduceIte, eval_or, List.any_cons,
        List.any_nil, id_eq, Bool.or_false]
    have hOutGate : 25 ≤ C0.output ∧ C0.output < 25 + C0.gates.length := by
      constructor
      · by_contra hlt
        have hu : C0.output < 25 := by omega
        let u : Fin 25 := ⟨C0.output, hu⟩
        have h1 := hC0_eval (fun w => decide (w = u))
        have h2 := val_input 25 C0 (fun w => decide (w = u)) u
        change wireVal 25 C0 C0.output (fun w => decide (w = u)) = decide (u = u) at h2
        rw [h1, hSingleFalse u] at h2
        simp only [decide_true] at h2
        cases h2
      · by_contra hge
        have h1 := hC0_eval (pairInput ⟨0, by omega⟩ ⟨13, by omega⟩)
        have h2 := val_ge 25 C0 (pairInput ⟨0, by omega⟩ ⟨13, by omega⟩) C0.output (by omega)
        rw [h1, hPairTrue] at h2
        cases h2
    let out_g : ℕ := C0.output - 25
    have hout_g_lt : out_g < C0.gates.length := by omega
    have hout_g_eq : C0.output = 25 + out_g := by omega
    have hDeleteGate : ∀ (j : ℕ) (hj : j < C0.gates.length) (repl : ℕ), repl < 25 + j →
        ((∀ k < C0.gates.length, 25 + j ∉ (gateAt C0 k).inputs) ∧ C0.output ≠ 25 + j) ∨
        ((∀ x : Fin 25 → Bool, graphFun G ∅ x = false →
            wireVal 25 C0 (25 + j) x = wireVal 25 C0 repl x) ∧
         (∀ x : Fin 25 → Bool, wireVal 25 C0 (25 + j) x = true →
            wireVal 25 C0 repl x = true)) → False := by
      intro j hj repl hrepl hcase
      let rmp (w : ℕ) : ℕ := if w = 25 + j then repl else if 25 + j < w then w - 1 else w
      let gs' : List Gate := (C0.gates.eraseIdx j).map fun g => ⟨g.op, g.inputs.map rmp⟩
      let C' : Circuit := ⟨gs', rmp C0.output⟩
      have hgs'_len : gs'.length = C0.gates.length - 1 := by
        simp only [gs', List.length_map, List.length_eraseIdx_of_lt hj]
      have hgateAt' : ∀ m (hm : m < gs'.length),
          gateAt C' m =
            let k := if m < j then m else m + 1
            ⟨(gateAt C0 k).op, (gateAt C0 k).inputs.map rmp⟩ := by
        intro m hm
        have hm' : m < (C0.gates.eraseIdx j).length := by simpa only [gs', List.length_map] using hm
        have hgat' : gateAt C' m = gs'[m] := by
          unfold gateAt; simp only [C', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
        rw [hgat']
        simp only [gs', List.getElem_map, List.getElem_eraseIdx]
        by_cases hmj : m < j
        · simp only [hmj, ↓reduceIte, ↓reduceDIte]
          have hgat0 : gateAt C0 m = C0.gates[m]'(by omega) := by
            unfold gateAt; simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m < C0.gates.length by omega), Option.getD_some]
          rw [hgat0]
        · simp only [hmj, ↓reduceIte, ↓reduceDIte]
          have hgat0 : gateAt C0 (m + 1) = C0.gates[m + 1]'(by omega) := by
            unfold gateAt; simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m + 1 < C0.gates.length by omega), Option.getD_some]
          rw [hgat0]
      have hC'_ao : IsAO2 25 C' := by
        refine ⟨?_, ?_, ?_⟩
        · intro g hg
          obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
          exact hC0_op g0 (List.mem_of_mem_eraseIdx hg0)
        · intro m hm i hi
          rw [hgateAt' m hm] at hi
          dsimp only at hi
          obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hi
          by_cases hmj : m < j
          · simp only [hmj, ↓reduceIte] at hw
            have hwlt := hC0_rb m (by omega) w hw
            dsimp only [rmp]
            simp only [show w ≠ 25 + j by omega, show ¬ 25 + j < w by omega, ↓reduceIte]
            exact hwlt
          · simp only [hmj, ↓reduceIte] at hw
            have hm_len : m < C0.gates.length - 1 := by rw [← hgs'_len]; exact hm
            have hwlt := hC0_rb (m + 1) (by omega) w hw
            dsimp only [rmp]
            split_ifs <;> omega
        · intro g hg
          obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
          simp only [List.length_map]
          exact hC0_len2 g0 (List.mem_of_mem_eraseIdx hg0)
      have hrmp_lt : ∀ w, w < 25 + j → rmp w = w := by
        intro w hw; dsimp only [rmp]; simp only [show w ≠ 25 + j by omega, show ¬ 25 + j < w by omega, ↓reduceIte]
      have hC'_fun : circuitFun 25 C' = graphFun G ∅ := by
        funext x
        have hev' : circuitFun 25 C' x = wireVal 25 C' (rmp C0.output) x := rfl
        rw [hev']
        rcases hcase with ⟨hdead, houtne⟩ | ⟨hbypass_f, hbypass_t⟩
        · have hagree : ∀ w < 25 + C0.gates.length, w ≠ 25 + j →
              wireVal 25 C' (rmp w) x = wireVal 25 C0 w x := by
            intro w
            induction w using Nat.strongRecOn with
            | ind w ih =>
              intro hw hne
              by_cases hw25 : w < 25
              · rw [hrmp_lt w (by omega)]
                exact (val_input 25 C' x ⟨w, hw25⟩).trans (val_input 25 C0 x ⟨w, hw25⟩).symm
              · let k := w - 25
                have hk_lt : k < C0.gates.length := by omega
                have hwk : w = 25 + k := by omega
                have hkj : k ≠ j := by omega
                let m := if k < j then k else k - 1
                have hm_lt : m < gs'.length := by dsimp only [m]; rw [hgs'_len]; split_ifs <;> omega
                have hrmp_w : rmp w = 25 + m := by
                  dsimp only [rmp, m]
                  rw [hwk]
                  by_cases hlt : k < j
                  · simp only [hlt, show 25 + k ≠ 25 + j by omega, show ¬ 25 + j < 25 + k by omega, ↓reduceIte]
                  · simp only [hlt, show 25 + k ≠ 25 + j by omega, show 25 + j < 25 + k by omega, ↓reduceIte]; omega
                have hmk : (if m < j then m else m + 1) = k := by
                  dsimp only [m]; split_ifs <;> omega
                rw [hrmp_w, val_gate 25 C' x m hm_lt, hgateAt' m hm_lt, hwk, val_gate 25 C0 x k hk_lt]
                dsimp only
                rw [hmk]
                simp only [List.map_map]
                congr 1
                apply List.map_congr_left
                intro u hu
                have hult : u < 25 + k := hC0_rb k hk_lt u hu
                have hune : u ≠ 25 + j := fun h => hdead k hk_lt (h ▸ hu)
                have hrmp_u_lt : rmp u < 25 + m := by
                  dsimp only [rmp, m]; split_ifs <;> omega
                simp only [Function.comp_apply, hrmp_u_lt, hult, ↓reduceIte]
                exact ih u (by omega) (by omega) hune
          rw [hagree C0.output hOutGate.2 houtne, hC0_eval x]
        · cases hgf : graphFun G ∅ x
          · have hagree : ∀ w < 25 + C0.gates.length,
                wireVal 25 C' (rmp w) x = wireVal 25 C0 w x := by
              intro w
              induction w using Nat.strongRecOn with
              | ind w ih =>
                intro hw
                by_cases hw25 : w < 25
                · rw [hrmp_lt w (by omega)]
                  exact (val_input 25 C' x ⟨w, hw25⟩).trans (val_input 25 C0 x ⟨w, hw25⟩).symm
                · by_cases hwj : w = 25 + j
                  · subst hwj
                    have hrmp_j : rmp (25 + j) = repl := by dsimp only [rmp]; simp only [↓reduceIte]
                    rw [hrmp_j, ← hrmp_lt repl hrepl, ih repl hrepl (by omega), hbypass_f x hgf]
                  · let k := w - 25
                    have hk_lt : k < C0.gates.length := by omega
                    have hwk : w = 25 + k := by omega
                    let m := if k < j then k else k - 1
                    have hm_lt : m < gs'.length := by dsimp only [m]; rw [hgs'_len]; split_ifs <;> omega
                    have hrmp_w : rmp w = 25 + m := by
                      dsimp only [rmp, m]
                      rw [hwk]
                      by_cases hlt : k < j
                      · simp only [hlt, show 25 + k ≠ 25 + j by omega, show ¬ 25 + j < 25 + k by omega, ↓reduceIte]
                      · simp only [hlt, show 25 + k ≠ 25 + j by omega, show 25 + j < 25 + k by omega, ↓reduceIte]; omega
                    have hmk : (if m < j then m else m + 1) = k := by
                      dsimp only [m]; split_ifs <;> omega
                    rw [hrmp_w, val_gate 25 C' x m hm_lt, hgateAt' m hm_lt, hwk, val_gate 25 C0 x k hk_lt]
                    dsimp only
                    rw [hmk]
                    simp only [List.map_map]
                    congr 1
                    apply List.map_congr_left
                    intro u hu
                    have hult : u < 25 + k := hC0_rb k hk_lt u hu
                    have hrmp_u_lt : rmp u < 25 + m := by
                      dsimp only [rmp, m]; split_ifs <;> omega
                    simp only [Function.comp_apply, hrmp_u_lt, hult, ↓reduceIte]
                    exact ih u (by omega) (by omega)
            rw [hagree C0.output hOutGate.2, hC0_eval x, hgf]
          · have hmono_w : ∀ w < 25 + C0.gates.length,
                wireVal 25 C0 w x = true → wireVal 25 C' (rmp w) x = true := by
              intro w
              induction w using Nat.strongRecOn with
              | ind w ih =>
                intro hw htrue
                by_cases hw25 : w < 25
                · rw [hrmp_lt w (by omega), val_input 25 C' x ⟨w, hw25⟩]
                  rwa [val_input 25 C0 x ⟨w, hw25⟩] at htrue
                · by_cases hwj : w = 25 + j
                  · subst hwj
                    have hrmp_j : rmp (25 + j) = repl := by dsimp only [rmp]; simp only [↓reduceIte]
                    rw [hrmp_j, ← hrmp_lt repl hrepl]
                    exact ih repl hrepl (by omega) (hbypass_t x htrue)
                  · let k := w - 25
                    have hk_lt : k < C0.gates.length := by omega
                    have hwk : w = 25 + k := by omega
                    let m := if k < j then k else k - 1
                    have hm_lt : m < gs'.length := by dsimp only [m]; rw [hgs'_len]; split_ifs <;> omega
                    have hrmp_w : rmp w = 25 + m := by
                      dsimp only [rmp, m]
                      rw [hwk]
                      by_cases hlt : k < j
                      · simp only [hlt, show 25 + k ≠ 25 + j by omega, show ¬ 25 + j < 25 + k by omega, ↓reduceIte]
                      · simp only [hlt, show 25 + k ≠ 25 + j by omega, show 25 + j < 25 + k by omega, ↓reduceIte]; omega
                    have hmk : (if m < j then m else m + 1) = k := by
                      dsimp only [m]; split_ifs <;> omega
                    obtain ⟨hins, h0lt, h1lt⟩ := hGateIn k hk_lt
                    have hrmp0 : rmp (opnd C0 k 0) < 25 + m := by dsimp only [rmp, m]; split_ifs <;> omega
                    have hrmp1 : rmp (opnd C0 k 1) < 25 + m := by dsimp only [rmp, m]; split_ifs <;> omega
                    have hgat_mem : gateAt C0 k ∈ C0.gates := by
                      unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt, Option.getD_some]
                      exact List.getElem_mem hk_lt
                    rw [hrmp_w, val_gate 25 C' x m hm_lt, hgateAt' m hm_lt]
                    dsimp only
                    rw [hmk, hins]
                    simp only [List.map_cons, List.map_nil, hrmp0, hrmp1, ↓reduceIte]
                    rcases hC0_op _ hgat_mem with hop | hop
                    · rw [hwk, hValAnd k hk_lt hop x] at htrue
                      simp only [Bool.and_eq_true] at htrue
                      rw [hop]
                      simp only [eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true]
                      exact ⟨ih _ (by omega) (by omega) htrue.1, ih _ (by omega) (by omega) htrue.2⟩
                    · rw [hwk, hValOr k hk_lt hop x] at htrue
                      simp only [Bool.or_eq_true] at htrue
                      rw [hop]
                      simp only [eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
                      rcases htrue with h1 | h2
                      · exact Or.inl (ih _ (by omega) (by omega) h1)
                      · exact Or.inr (ih _ (by omega) (by omega) h2)
            exact hmono_w C0.output hOutGate.2 (by rw [hC0_eval x, hgf])
      have hle := hC0_least.2.2 C' hC'_ao hC'_fun
      have hsz' : C'.size = C0.gates.length - 1 := hgs'_len
      have hsz0 : C0.size = C0.gates.length := rfl
      omega
    have hLive : ∀ j < C0.gates.length, 25 + j ≠ C0.output →
        ∃ k < C0.gates.length, 25 + j ∈ (gateAt C0 k).inputs := by
      intro j hj hne
      by_contra hnone
      push Not at hnone
      exact hDeleteGate j hj 0 (by omega) (Or.inl ⟨hnone, hne.symm⟩)
    have hNoCleanInAnd : ∀ j < C0.gates.length, (gateAt C0 j).op = GateOp.and →
        ∀ w ∈ (gateAt C0 j).inputs,
          ¬ (∀ x : Fin 25 → Bool, wireVal 25 C0 w x = true → graphFun G ∅ x = true) := by
      intro j hj hop w hw hclean
      have hw_lt : w < 25 + j := hC0_rb j hj w hw
      obtain ⟨hins, _, _⟩ := hGateIn j hj
      rw [hins] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      refine hDeleteGate j hj w hw_lt (Or.inr ⟨?_, ?_⟩)
      · intro x hgf
        have h1 : wireVal 25 C0 (25 + j) x = false := by
          cases h' : wireVal 25 C0 (25 + j) x
          · rfl
          · have := hCleanAnd j hj hop x h'; rw [hgf] at this; cases this
        have h2 : wireVal 25 C0 w x = false := by
          cases h' : wireVal 25 C0 w x
          · rfl
          · have := hclean x h'; rw [hgf] at this; cases this
        rw [h1, h2]
      · intro x ht
        rw [hValAnd j hj hop x] at ht
        simp only [Bool.and_eq_true] at ht
        rcases hw with rfl | rfl
        · exact ht.1
        · exact ht.2
    let sStep (ss : List (Finset (Fin 25))) (g : Gate) : List (Finset (Fin 25)) :=
      ss ++ [if g.op = GateOp.or then (g.inputs.map fun i => ss.getD i ∅).foldr (· ∪ ·) ∅ else ∅]
    let sInit : List (Finset (Fin 25)) := List.ofFn (fun i : Fin 25 => ({i} : Finset (Fin 25)))
    have sfold_len : ∀ (gs : List Gate) (ss : List (Finset (Fin 25))),
        (gs.foldl sStep ss).length = ss.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro ss; simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
      | cons g gs ih =>
        intro ss
        rw [List.foldl_cons, ih]
        simp only [sStep, List.length_append, List.length_cons, List.length_nil]
        omega
    have sfold_lt : ∀ (gs : List Gate) (ss : List (Finset (Fin 25))) (i : ℕ), i < ss.length →
        (gs.foldl sStep ss).getD i ∅ = ss.getD i ∅ := by
      intro gs
      induction gs with
      | nil => intro ss i _; rfl
      | cons g gs ih =>
        intro ss i hi
        rw [List.foldl_cons]
        have hlt : i < (sStep ss g).length := by
          simp only [sStep, List.length_append, List.length_cons, List.length_nil]; omega
        rw [ih (sStep ss g) i hlt]
        simp only [sStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have sfold_gate : ∀ (gs : List Gate) (ss : List (Finset (Fin 25))) (j : ℕ) (hj : j < gs.length),
        (gs.foldl sStep ss).getD (ss.length + j) ∅ =
          if (gs[j]).op = GateOp.or then
            ((gs[j]).inputs.map fun i =>
              if i < ss.length + j then (gs.foldl sStep ss).getD i ∅ else ∅).foldr (· ∪ ·) ∅
          else ∅ := by
      intro gs
      induction gs with
      | nil => intro ss j hj; simp at hj
      | cons g gs ih =>
        intro ss j hj
        rw [List.foldl_cons]
        cases j with
        | zero =>
          have h1 : ss.length < (sStep ss g).length := by
            simp only [sStep, List.length_append, List.length_cons, List.length_nil]; omega
          rw [Nat.add_zero, sfold_lt gs (sStep ss g) ss.length h1]
          simp only [List.getElem_cons_zero]
          have h2 : (sStep ss g).getD ss.length ∅ =
              if g.op = GateOp.or then (g.inputs.map fun i => ss.getD i ∅).foldr (· ∪ ·) ∅ else ∅ := by
            simp only [sStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          rw [h2]
          by_cases hop : g.op = GateOp.or
          · simp only [hop, ↓reduceIte]
            congr 1
            apply List.map_congr_left
            intro i _
            by_cases hi : i < ss.length
            · simp only [hi, ↓reduceIte]
              rw [sfold_lt gs (sStep ss g) i (by
                simp only [sStep, List.length_append, List.length_cons, List.length_nil]; omega)]
              simp only [sStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
            · simp only [hi, ↓reduceIte, List.getD_eq_getElem?_getD,
                List.getElem?_eq_none (show ss.length ≤ i by omega), Option.getD_none]
          · simp only [hop, ↓reduceIte]
        | succ j =>
          have hj' : j < gs.length := by simp only [List.length_cons] at hj; omega
          have key := ih (sStep ss g) j hj'
          have hl : (sStep ss g).length = ss.length + 1 := by
            simp only [sStep, List.length_append, List.length_cons, List.length_nil]
          rw [hl] at key
          have e : ss.length + (j + 1) = ss.length + 1 + j := by omega
          simp only [List.getElem_cons_succ]
          rw [e]
          exact key
    let S (w : ℕ) : Finset (Fin 25) := (C0.gates.foldl sStep sInit).getD w ∅
    have hS_in : ∀ i : Fin 25, S i.val = {i} := by
      intro i
      dsimp only [S]
      have hlt : i.val < sInit.length := by simp only [sInit, List.length_ofFn]; exact i.isLt
      rw [sfold_lt C0.gates sInit i.val hlt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
      simp only [sInit, List.getElem_ofFn, Fin.eta]
    have hS_and : ∀ j < C0.gates.length, (gateAt C0 j).op = GateOp.and → S (25 + j) = ∅ := by
      intro j hj hop
      dsimp only [S]
      have key := sfold_gate C0.gates sInit j hj
      have hsl : sInit.length = 25 := by simp only [sInit, List.length_ofFn]
      rw [hsl] at key
      have hgat : gateAt C0 j = C0.gates[j] := by
        unfold gateAt; simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      rw [key, ← hgat, hop]
      simp only [reduceCtorEq, ↓reduceIte]
    have hS_or : ∀ j < C0.gates.length, (gateAt C0 j).op = GateOp.or →
        S (25 + j) = S (opnd C0 j 0) ∪ S (opnd C0 j 1) := by
      intro j hj hop
      dsimp only [S]
      have key := sfold_gate C0.gates sInit j hj
      have hsl : sInit.length = 25 := by simp only [sInit, List.length_ofFn]
      rw [hsl] at key
      have hgat : gateAt C0 j = C0.gates[j] := by
        unfold gateAt; simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      obtain ⟨hins, h0, h1⟩ := hGateIn j hj
      rw [key, ← hgat, hop, hins]
      simp only [↓reduceIte, List.map_cons, List.map_nil, h0, h1, List.foldr_cons, List.foldr_nil,
        Finset.union_empty]
    have hS_sound : ∀ w < 25 + C0.gates.length, ∀ u ∈ S w, ∀ x : Fin 25 → Bool,
        x u = true → wireVal 25 C0 w x = true := by
      intro w
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hw u hu x hxu
        by_cases hw25 : w < 25
        · have hSw := hS_in ⟨w, hw25⟩
          rw [hSw, Finset.mem_singleton] at hu
          subst hu
          rw [val_input 25 C0 x ⟨w, hw25⟩]
          exact hxu
        · let j := w - 25
          have hj : j < C0.gates.length := by omega
          have hwj : w = 25 + j := by omega
          have hgat_mem : gateAt C0 j ∈ C0.gates := by
            unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
            exact List.getElem_mem hj
          rcases hC0_op _ hgat_mem with hop | hop
          · rw [hwj, hS_and j hj hop] at hu
            exact absurd hu (Finset.notMem_empty u)
          · rw [hwj, hS_or j hj hop] at hu
            obtain ⟨_, h0, h1⟩ := hGateIn j hj
            rw [hwj, hValOr j hj hop x, Bool.or_eq_true]
            rcases Finset.mem_union.1 hu with h | h
            · exact Or.inl (ih _ (by omega) (by omega) u h x hxu)
            · exact Or.inr (ih _ (by omega) (by omega) u h x hxu)
    have hS_empty_clean : ∀ w < 25 + C0.gates.length, S w = ∅ →
        ∀ x : Fin 25 → Bool, wireVal 25 C0 w x = true → graphFun G ∅ x = true := by
      intro w
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hw hSw x hval
        by_cases hw25 : w < 25
        · have h1 := hS_in ⟨w, hw25⟩
          rw [hSw] at h1
          exact absurd (Finset.mem_singleton_self (⟨w, hw25⟩ : Fin 25)) (by rw [← h1]; exact Finset.notMem_empty _)
        · let j := w - 25
          have hj : j < C0.gates.length := by omega
          have hwj : w = 25 + j := by omega
          have hgat_mem : gateAt C0 j ∈ C0.gates := by
            unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
            exact List.getElem_mem hj
          rcases hC0_op _ hgat_mem with hop | hop
          · rw [hwj] at hval; exact hCleanAnd j hj hop x hval
          · rw [hwj, hS_or j hj hop, Finset.union_eq_empty] at hSw
            obtain ⟨_, h0, h1⟩ := hGateIn j hj
            rw [hwj, hValOr j hj hop x, Bool.or_eq_true] at hval
            rcases hval with hv | hv
            · exact ih _ (by omega) (by omega) hSw.1 x hv
            · exact ih _ (by omega) (by omega) hSw.2 x hv
    have hS_out : S C0.output = ∅ := by
      by_contra hne
      obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have h1 := hS_sound C0.output hOutGate.2 u hu (fun w => decide (w = u)) (by simp only [decide_true])
      rw [hC0_eval, hSingleFalse u] at h1
      cases h1
    have hAnd_sides : ∀ j < C0.gates.length, (gateAt C0 j).op = GateOp.and →
        (S (opnd C0 j 0)).Nonempty ∧ (S (opnd C0 j 1)).Nonempty ∧
        (∀ u ∈ S (opnd C0 j 0), ∀ v ∈ S (opnd C0 j 1), G.Adj u v) ∧
        ((S (opnd C0 j 0)).card = 1 ∨ (S (opnd C0 j 1)).card = 1) := by
      intro j hj hop
      obtain ⟨hins, h0lt, h1lt⟩ := hGateIn j hj
      have hne0 : (S (opnd C0 j 0)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        exact hNoCleanInAnd j hj hop (opnd C0 j 0) (by rw [hins]; exact List.mem_cons_self ..)
          (hS_empty_clean (opnd C0 j 0) (by omega) hemp)
      have hne1 : (S (opnd C0 j 1)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        exact hNoCleanInAnd j hj hop (opnd C0 j 1)
          (by rw [hins]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
          (hS_empty_clean (opnd C0 j 1) (by omega) hemp)
      have hadj : ∀ u ∈ S (opnd C0 j 0), ∀ v ∈ S (opnd C0 j 1), G.Adj u v := by
        intro u hu v hv
        have hval0 := hS_sound (opnd C0 j 0) (by omega) u hu (pairInput u v) (pairInput_left u v)
        have hval1 := hS_sound (opnd C0 j 1) (by omega) v hv (pairInput u v) (pairInput_right u v)
        have hvalj : wireVal 25 C0 (25 + j) (pairInput u v) = true := by
          rw [hValAnd j hj hop, hval0, hval1]; rfl
        have hgf := hCleanAnd j hj hop (pairInput u v) hvalj
        unfold graphFun at hgf
        simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
          decide_eq_true_eq] at hgf
        obtain ⟨a, b, hab, ha, hb⟩ := hgf
        rw [pairInput_true] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab.ne
        · exact hab
        · exact hab.symm
        · exact absurd rfl hab.ne
      have hstar : (S (opnd C0 j 0)).card = 1 ∨ (S (opnd C0 j 1)).card = 1 := by
        by_contra hboth
        push Not at hboth
        have hc0 : 1 < (S (opnd C0 j 0)).card := by
          have := Finset.card_pos.2 hne0; omega
        have hc1 : 1 < (S (opnd C0 j 1)).card := by
          have := Finset.card_pos.2 hne1; omega
        obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.1 hc0
        obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.1 hc1
        exact hNoC4 u1 u2 hune v1 v2 hvne (hadj u1 hu1 v1 hv1) (hadj u1 hu1 v2 hv2)
          (hadj u2 hu2 v1 hv1) (hadj u2 hu2 v2 hv2)
      exact ⟨hne0, hne1, hadj, hstar⟩
    have hEdgeCov : ∀ u v : Fin 25, G.Adj u v →
        ∃ j < C0.gates.length, (gateAt C0 j).op = GateOp.and ∧
          ((u ∈ S (opnd C0 j 0) ∧ v ∈ S (opnd C0 j 1)) ∨
           (v ∈ S (opnd C0 j 0) ∧ u ∈ S (opnd C0 j 1))) := by
      intro u v huv
      have hind : ∀ w < 25 + C0.gates.length,
          wireVal 25 C0 w (pairInput u v) = true →
          (u ∈ S w ∨ v ∈ S w) ∨
            ∃ j < C0.gates.length, (gateAt C0 j).op = GateOp.and ∧
              ((u ∈ S (opnd C0 j 0) ∧ v ∈ S (opnd C0 j 1)) ∨
               (v ∈ S (opnd C0 j 0) ∧ u ∈ S (opnd C0 j 1))) := by
        intro w
        induction w using Nat.strongRecOn with
        | ind w ih =>
          intro hw hval
          by_cases hw25 : w < 25
          · rw [val_input 25 C0 (pairInput u v) ⟨w, hw25⟩, pairInput_true] at hval
            left
            rw [hS_in ⟨w, hw25⟩]
            rcases hval with h | h
            · left; rw [h]; exact Finset.mem_singleton_self _
            · right; rw [h]; exact Finset.mem_singleton_self _
          · let j := w - 25
            have hj : j < C0.gates.length := by omega
            have hwj : w = 25 + j := by omega
            obtain ⟨_, h0lt, h1lt⟩ := hGateIn j hj
            have hgat_mem : gateAt C0 j ∈ C0.gates := by
              unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
              exact List.getElem_mem hj
            rcases hC0_op _ hgat_mem with hop | hop
            · rw [hwj, hValAnd j hj hop, Bool.and_eq_true] at hval
              rcases ih (opnd C0 j 0) (by omega) (by omega) hval.1 with hs0 | hex
              · rcases ih (opnd C0 j 1) (by omega) (by omega) hval.2 with hs1 | hex
                · right
                  refine ⟨j, hj, hop, ?_⟩
                  have hdisj := (hAnd_sides j hj hop).2.2.1
                  rcases hs0 with hu0 | hv0 <;> rcases hs1 with hu1 | hv1
                  · exact absurd rfl (hdisj u hu0 u hu1).ne
                  · exact Or.inl ⟨hu0, hv1⟩
                  · exact Or.inr ⟨hv0, hu1⟩
                  · exact absurd rfl (hdisj v hv0 v hv1).ne
                · exact Or.inr hex
              · exact Or.inr hex
            · rw [hwj, hValOr j hj hop, Bool.or_eq_true] at hval
              rcases hval with hv | hv
              · rcases ih (opnd C0 j 0) (by omega) (by omega) hv with hs | hex
                · left; rw [hwj, hS_or j hj hop]
                  rcases hs with h | h
                  · exact Or.inl (Finset.mem_union_left _ h)
                  · exact Or.inr (Finset.mem_union_left _ h)
                · exact Or.inr hex
              · rcases ih (opnd C0 j 1) (by omega) (by omega) hv with hs | hex
                · left; rw [hwj, hS_or j hj hop]
                  rcases hs with h | h
                  · exact Or.inl (Finset.mem_union_right _ h)
                  · exact Or.inr (Finset.mem_union_right _ h)
                · exact Or.inr hex
      have hout_t : wireVal 25 C0 C0.output (pairInput u v) = true := by
        rw [hC0_eval, hEdgeTrue u v huv]
      rcases hind C0.output hOutGate.2 hout_t with hs | hex
      · rw [hS_out] at hs
        rcases hs with h | h <;> exact absurd h (Finset.notMem_empty _)
      · exact hex
    let A : Finset ℕ := (Finset.range C0.gates.length).filter fun j => (gateAt C0 j).op = GateOp.and
    let O_T : Finset ℕ := (Finset.range C0.gates.length).filter fun j =>
      (gateAt C0 j).op = GateOp.or ∧ S (opnd C0 j 0) = ∅ ∧ S (opnd C0 j 1) = ∅
    let O_01 : Finset ℕ := (Finset.range C0.gates.length).filter fun j =>
      (gateAt C0 j).op = GateOp.or ∧
        ((S (opnd C0 j 0) = ∅ ∧ S (opnd C0 j 1) ≠ ∅) ∨ (S (opnd C0 j 0) ≠ ∅ ∧ S (opnd C0 j 1) = ∅))
    let O_11 : Finset ℕ := (Finset.range C0.gates.length).filter fun j =>
      (gateAt C0 j).op = GateOp.or ∧ S (opnd C0 j 0) ≠ ∅ ∧ S (opnd C0 j 1) ≠ ∅
    have hPart : C0.gates.length = A.card + O_T.card + O_01.card + O_11.card := by
      have hdisj1 : Disjoint A O_T := Finset.disjoint_left.2 fun j hj1 hj2 => by
        simp only [A, O_T, Finset.mem_filter] at hj1 hj2; rw [hj1.2] at hj2; cases hj2.2.1
      have hdisj2 : Disjoint (A ∪ O_T) O_01 := Finset.disjoint_left.2 fun j hj1 hj2 => by
        simp only [A, O_T, O_01, Finset.mem_union, Finset.mem_filter] at hj1 hj2
        rcases hj1 with h1 | h2
        · rw [h1.2] at hj2; cases hj2.2.1
        · rcases hj2.2.2 with ⟨_, hne⟩ | ⟨hne, _⟩
          · exact hne h2.2.2.2
          · exact hne h2.2.2.1
      have hdisj3 : Disjoint (A ∪ O_T ∪ O_01) O_11 := Finset.disjoint_left.2 fun j hj1 hj2 => by
        simp only [A, O_T, O_01, O_11, Finset.mem_union, Finset.mem_filter] at hj1 hj2
        rcases hj1 with (h1 | h2) | h3
        · rw [h1.2] at hj2; cases hj2.2.1
        · exact hj2.2.2.1 h2.2.2.1
        · rcases h3.2.2 with ⟨he, _⟩ | ⟨_, he⟩
          · exact hj2.2.2.1 he
          · exact hj2.2.2.2 he
      have hunion : A ∪ O_T ∪ O_01 ∪ O_11 = Finset.range C0.gates.length := by
        ext j
        simp only [A, O_T, O_01, O_11, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro (((h | h) | h) | h) <;> exact h.1
        · intro hj
          have hgat_mem : gateAt C0 j ∈ C0.gates := by
            unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
            exact List.getElem_mem hj
          rcases hC0_op _ hgat_mem with hop | hop
          · exact Or.inl (Or.inl (Or.inl ⟨hj, hop⟩))
          · by_cases h0 : S (opnd C0 j 0) = ∅ <;> by_cases h1 : S (opnd C0 j 1) = ∅
            · exact Or.inl (Or.inl (Or.inr ⟨hj, hop, h0, h1⟩))
            · exact Or.inl (Or.inr ⟨hj, hop, Or.inl ⟨h0, h1⟩⟩)
            · exact Or.inl (Or.inr ⟨hj, hop, Or.inr ⟨h0, h1⟩⟩)
            · exact Or.inr ⟨hj, hop, h0, h1⟩
      rw [← Finset.card_range C0.gates.length, ← hunion,
        Finset.card_union_of_disjoint hdisj3, Finset.card_union_of_disjoint hdisj2,
        Finset.card_union_of_disjoint hdisj1]
    let ctr (j : ℕ) : Fin 25 :=
      if h : j < C0.gates.length ∧ (gateAt C0 j).op = GateOp.and then
        if h0 : (S (opnd C0 j 0)).card = 1 then
          Classical.choose (Finset.card_eq_one.1 h0)
        else
          Classical.choose (Finset.card_eq_one.1 ((hAnd_sides j h.1 h.2).2.2.2.resolve_left h0))
      else ⟨0, by omega⟩
    let lwire (j : ℕ) : ℕ :=
      if (S (opnd C0 j 0)).card = 1 then opnd C0 j 1 else opnd C0 j 0
    let L (j : ℕ) : Finset (Fin 25) := S (lwire j)
    have hCtrL : ∀ j ∈ A,
        (L j).Nonempty ∧ (∀ v ∈ L j, G.Adj (ctr j) v) ∧
        (∀ u ∈ S (opnd C0 j 0), ∀ v ∈ S (opnd C0 j 1),
          (u = ctr j ∧ v ∈ L j) ∨ (v = ctr j ∧ u ∈ L j)) := by
      intro j hjA
      simp only [A, Finset.mem_filter, Finset.mem_range] at hjA
      obtain ⟨hj, hop⟩ := hjA
      obtain ⟨hne0, hne1, hadj, hstar⟩ := hAnd_sides j hj hop
      by_cases h0 : (S (opnd C0 j 0)).card = 1
      · have hctr : ctr j = Classical.choose (Finset.card_eq_one.1 h0) := by
          dsimp only [ctr]; simp only [hj, hop, and_self, ↓reduceDIte, h0]
        have hS0 : S (opnd C0 j 0) = {ctr j} := by
          rw [hctr]; exact Classical.choose_spec (Finset.card_eq_one.1 h0)
        have hLj : L j = S (opnd C0 j 1) := by dsimp only [L, lwire]; simp only [h0, ↓reduceIte]
        rw [hLj]
        refine ⟨hne1, fun v hv => hadj (ctr j) (by rw [hS0]; exact Finset.mem_singleton_self _) v hv,
          fun u hu v hv => Or.inl ⟨by rw [hS0, Finset.mem_singleton] at hu; exact hu, hv⟩⟩
      · have h1 : (S (opnd C0 j 1)).card = 1 := hstar.resolve_left h0
        have hctr : ctr j = Classical.choose (Finset.card_eq_one.1 h1) := by
          dsimp only [ctr]; simp only [hj, hop, and_self, ↓reduceDIte, h0]
        have hS1 : S (opnd C0 j 1) = {ctr j} := by
          rw [hctr]; exact Classical.choose_spec (Finset.card_eq_one.1 h1)
        have hLj : L j = S (opnd C0 j 0) := by dsimp only [L, lwire]; simp only [h0, ↓reduceIte]
        rw [hLj]
        refine ⟨hne0, fun u hu => (hadj u hu (ctr j) (by rw [hS1]; exact Finset.mem_singleton_self _)).symm,
          fun u hu v hv => Or.inr ⟨by rw [hS1, Finset.mem_singleton] at hv; exact hv, hu⟩⟩
    let Ac (c : Fin 25) : Finset ℕ := A.filter fun j => ctr j = c
    let U (c : Fin 25) : Finset (Fin 25) := (Ac c).biUnion L
    have hU_adj : ∀ (c : Fin 25), ∀ v ∈ U c, G.Adj c v := by
      intro c v hv
      obtain ⟨j, hj, hvL⟩ := Finset.mem_biUnion.1 hv
      simp only [Ac, Finset.mem_filter] at hj
      rw [← hj.2]
      exact (hCtrL j hj.1).2.1 v hvL
    have hSumU : 48 ≤ ∑ c : Fin 25, (U c).card := by
      have hcov_pair : ∀ pl ∈ Eset,
          ∃ cw : Fin 25 × Fin 25, cw.2 ∈ U cw.1 ∧
            ((cw.1 = Fin.castAdd 12 pl.1 ∧ cw.2 = Fin.natAdd 13 pl.2) ∨
             (cw.1 = Fin.natAdd 13 pl.2 ∧ cw.2 = Fin.castAdd 12 pl.1)) := by
        intro pl hpl
        simp only [Eset, Finset.mem_filter, Finset.mem_univ, true_and] at hpl
        have hinc : Inc13 pl.1 ⟨pl.2.val, by omega⟩ := (hInc13_val pl.1 pl.2).2 hpl
        have hadj : G.Adj (Fin.castAdd 12 pl.1) (Fin.natAdd 13 pl.2) :=
          (hAdj_iff _ _).2 ⟨pl.1, pl.2, hinc, Or.inl ⟨rfl, rfl⟩⟩
        obtain ⟨j, hj, hop, hpair⟩ := hEdgeCov _ _ hadj
        have hjA : j ∈ A := by simp only [A, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hop⟩
        have hCL := (hCtrL j hjA).2.2
        rcases hpair with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · rcases hCL _ hu _ hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · refine ⟨(Fin.castAdd 12 pl.1, Fin.natAdd 13 pl.2), ?_, Or.inl ⟨rfl, rfl⟩⟩
            exact Finset.mem_biUnion.2 ⟨j, by simp only [Ac, Finset.mem_filter]; exact ⟨hjA, h1.symm⟩, h2⟩
          · refine ⟨(Fin.natAdd 13 pl.2, Fin.castAdd 12 pl.1), ?_, Or.inr ⟨rfl, rfl⟩⟩
            exact Finset.mem_biUnion.2 ⟨j, by simp only [Ac, Finset.mem_filter]; exact ⟨hjA, h1.symm⟩, h2⟩
        · rcases hCL _ hv _ hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · refine ⟨(Fin.natAdd 13 pl.2, Fin.castAdd 12 pl.1), ?_, Or.inr ⟨rfl, rfl⟩⟩
            exact Finset.mem_biUnion.2 ⟨j, by simp only [Ac, Finset.mem_filter]; exact ⟨hjA, h1.symm⟩, h2⟩
          · refine ⟨(Fin.castAdd 12 pl.1, Fin.natAdd 13 pl.2), ?_, Or.inl ⟨rfl, rfl⟩⟩
            exact Finset.mem_biUnion.2 ⟨j, by simp only [Ac, Finset.mem_filter]; exact ⟨hjA, h1.symm⟩, h2⟩
      let φ (pl : Fin 13 × Fin 12) : Fin 25 × Fin 25 :=
        if h : pl ∈ Eset then Classical.choose (hcov_pair pl h) else (⟨0, by omega⟩, ⟨0, by omega⟩)
      have hφ_inj : Set.InjOn φ (Eset : Set (Fin 13 × Fin 12)) := by
        intro pl1 h1 pl2 h2 heq
        have hs1 := (Classical.choose_spec (hcov_pair pl1 h1)).2
        have hs2 := (Classical.choose_spec (hcov_pair pl2 h2)).2
        dsimp only [φ] at heq
        simp only [Finset.mem_coe.1 h1, Finset.mem_coe.1 h2, ↓reduceDIte] at heq
        rw [heq] at hs1
        rcases hs1 with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩ <;> rcases hs2 with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
        · have hp : pl1.1 = pl2.1 := by apply Fin.ext; have := congrArg Fin.val (ha1.symm.trans ha2); simpa only [Fin.val_castAdd] using this
          have hl : pl1.2 = pl2.2 := by apply Fin.ext; have := congrArg Fin.val (hb1.symm.trans hb2); simp only [Fin.val_natAdd] at this; omega
          exact Prod.ext hp hl
        · have := congrArg Fin.val (ha1.symm.trans ha2); simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
        · have := congrArg Fin.val (ha1.symm.trans ha2); simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
        · have hl : pl1.2 = pl2.2 := by apply Fin.ext; have := congrArg Fin.val (ha1.symm.trans ha2); simp only [Fin.val_natAdd] at this; omega
          have hp : pl1.1 = pl2.1 := by apply Fin.ext; have := congrArg Fin.val (hb1.symm.trans hb2); simpa only [Fin.val_castAdd] using this
          exact Prod.ext hp hl
      have hφ_sub : Eset.image φ ⊆ Finset.univ.biUnion fun c : Fin 25 => (U c).image fun w => (c, w) := by
        intro cw hcw
        obtain ⟨pl, hpl, rfl⟩ := Finset.mem_image.1 hcw
        dsimp only [φ]
        simp only [hpl, ↓reduceDIte]
        have hs := (Classical.choose_spec (hcov_pair pl hpl)).1
        exact Finset.mem_biUnion.2 ⟨(Classical.choose (hcov_pair pl hpl)).1, Finset.mem_univ _,
          Finset.mem_image.2 ⟨(Classical.choose (hcov_pair pl hpl)).2, hs, by simp only [Prod.mk.eta]⟩⟩
      calc 48 = Eset.card := hEset_card.symm
        _ = (Eset.image φ).card := (Finset.card_image_of_injOn hφ_inj).symm
        _ ≤ (Finset.univ.biUnion fun c : Fin 25 => (U c).image fun w => (c, w)).card := Finset.card_le_card hφ_sub
        _ ≤ ∑ c : Fin 25, ((U c).image fun w => (c, w)).card := Finset.card_biUnion_le
        _ = ∑ c : Fin 25, (U c).card := by
          apply Finset.sum_congr rfl
          intro c _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
    have hAge12 : 12 ≤ A.card := by
      have hU_le : ∀ c : Fin 25, (U c).card ≤ ∑ j ∈ Ac c, (L j).card := fun c => Finset.card_biUnion_le
      have hSumAc : ∑ c : Fin 25, ∑ j ∈ Ac c, (L j).card = ∑ j ∈ A, (L j).card := by
        have hbi : Finset.univ.biUnion Ac = A := by
          ext j; simp only [Ac, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
          exact ⟨fun h => h.choose_spec.1, fun h => ⟨ctr j, h, rfl⟩⟩
        have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin 25)) : Set (Fin 25)) Ac := by
          intro c1 _ c2 _ hne
          exact Finset.disjoint_left.2 fun j hj1 hj2 => by
            simp only [Ac, Finset.mem_filter] at hj1 hj2
            exact hne (hj1.2.symm.trans hj2.2)
        rw [← hbi, Finset.sum_biUnion hdisj]
      have hL_le4 : ∀ j ∈ A, (L j).card ≤ 4 := by
        intro j hjA
        have hsub : L j ⊆ Finset.univ.filter fun w : Fin 25 => G.Adj (ctr j) w := by
          intro w hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (hCtrL j hjA).2.1 w hw
        exact (Finset.card_le_card hsub).trans (hDegLe4 (ctr j))
      have h48 : 48 ≤ 4 * A.card := by
        calc 48 ≤ ∑ c : Fin 25, (U c).card := hSumU
          _ ≤ ∑ c : Fin 25, ∑ j ∈ Ac c, (L j).card := Finset.sum_le_sum fun c _ => hU_le c
          _ = ∑ j ∈ A, (L j).card := hSumAc
          _ ≤ ∑ _j ∈ A, 4 := Finset.sum_le_sum hL_le4
          _ = 4 * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      omega
    let T (c : Fin 25) : Finset ℕ := O_11.filter fun g => 2 ≤ (S (25 + g)).card ∧ S (25 + g) ⊆ U c
    have hT_disj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin 25)) : Set (Fin 25)) T := by
      intro c1 _ c2 _ hne
      exact Finset.disjoint_left.2 fun g hg1 hg2 => by
        simp only [T, Finset.mem_filter] at hg1 hg2
        have hgt1 : 1 < (S (25 + g)).card := by omega
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 hgt1
        exact hNoC4 c1 c2 hne u v huv (hU_adj c1 u (hg1.2.2 hu)) (hU_adj c1 v (hg1.2.2 hv))
          (hU_adj c2 u (hg2.2.2 hu)) (hU_adj c2 v (hg2.2.2 hv))
    have hSumT_le : ∑ c : Fin 25, (T c).card ≤ O_11.card := by
      rw [← Finset.card_biUnion hT_disj]
      apply Finset.card_le_card
      intro g hg
      obtain ⟨c, _, hgc⟩ := Finset.mem_biUnion.1 hg
      exact (Finset.mem_filter.1 hgc).1
    have hSumAc_card : ∑ c : Fin 25, (Ac c).card = A.card := by
      have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin 25)) : Set (Fin 25)) Ac := by
        intro c1 _ c2 _ hne
        exact Finset.disjoint_left.2 fun j hj1 hj2 => by
          simp only [Ac, Finset.mem_filter] at hj1 hj2; exact hne (hj1.2.symm.trans hj2.2)
      rw [← Finset.card_biUnion hdisj]
      congr 1
      ext j; simp only [Ac, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
      exact ⟨fun h => h.choose_spec.1, fun h => ⟨ctr j, h, rfl⟩⟩
    have hU_bound : ∀ c : Fin 25, (U c).card ≤ (Ac c).card + (T c).card := by
      clear hDeleteGate hLive hNoCleanInAnd hValAnd hValOr hCleanAnd hC0_eval hC0_least hC0_fun hOutGate hEdgeCov hSumU hAge12 hNoC4 hDegLe4 hSingleFalse hEdgeTrue hPairTrue hAdj_iff hInc13_val hEset_card Eset hSumT_le hT_disj hSumAc_card hU_adj hPart hS_out hS_sound hS_empty_clean hC0_le57
      intro c
      let mergeStep (f : Fin 25 → Fin 25) (e : Fin 25 × Fin 25) : Fin 25 → Fin 25 :=
        fun v => if f v = f e.1 then f e.2 else f v
      have hmerge_card : ∀ (f : Fin 25 → Fin 25) (e : Fin 25 × Fin 25),
          ((U c).image f).card ≤ ((U c).image (mergeStep f e)).card + 1 := by
        intro f e
        have hsub : ((U c).image f).erase (f e.1) ⊆ (U c).image (mergeStep f e) := by
          intro z hz
          obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hz
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hmem
          refine Finset.mem_image.2 ⟨u, hu, ?_⟩
          dsimp only [mergeStep]
          simp only [hne, ↓reduceIte]
        have h1 := Finset.card_le_card hsub
        have h2 : ((U c).image f).card - 1 ≤ (((U c).image f).erase (f e.1)).card :=
          Finset.pred_card_le_card_erase
        omega
      have hfold_card : ∀ (es : List (Fin 25 × Fin 25)) (f : Fin 25 → Fin 25),
          ((U c).image f).card ≤ ((U c).image (es.foldl mergeStep f)).card + es.length := by
        intro es
        induction es with
        | nil => intro f; simp only [List.foldl_nil, List.length_nil, Nat.add_zero, le_refl]
        | cons e es ih =>
          intro f
          rw [List.foldl_cons, List.length_cons]
          have h1 := hmerge_card f e
          have h2 := ih (mergeStep f e)
          omega
      have hfold_eq : ∀ (es : List (Fin 25 × Fin 25)) (f : Fin 25 → Fin 25) (u v : Fin 25),
          f u = f v → es.foldl mergeStep f u = es.foldl mergeStep f v := by
        intro es
        induction es with
        | nil => intro f u v h; exact h
        | cons e es ih =>
          intro f u v h
          rw [List.foldl_cons]
          apply ih
          dsimp only [mergeStep]
          rw [h]
      have hfold_mem : ∀ (es : List (Fin 25 × Fin 25)) (f : Fin 25 → Fin 25) (e : Fin 25 × Fin 25),
          e ∈ es → es.foldl mergeStep f e.1 = es.foldl mergeStep f e.2 := by
        intro es
        induction es with
        | nil => intro _ _ h; cases h
        | cons e0 es ih =>
          intro f e he
          rw [List.foldl_cons]
          rcases List.mem_cons.1 he with rfl | htail
          · apply hfold_eq
            dsimp only [mergeStep]
            simp only [↓reduceIte, ite_self]
          · exact ih (mergeStep f e0) e htail
      let pickEdge (g : ℕ) : Fin 25 × Fin 25 :=
        if h : g ∈ O_11 then
          let hne0 : (S (opnd C0 g 0)).Nonempty :=
            Finset.nonempty_iff_ne_empty.2 (Finset.mem_filter.1 h).2.2.1
          let hne1 : (S (opnd C0 g 1)).Nonempty :=
            Finset.nonempty_iff_ne_empty.2 (Finset.mem_filter.1 h).2.2.2
          (Classical.choose hne0, Classical.choose hne1)
        else (⟨0, by omega⟩, ⟨0, by omega⟩)
      let es : List (Fin 25 × Fin 25) := (T c).toList.map pickEdge
      let col : Fin 25 → Fin 25 := es.foldl mergeStep id
      have hcol_const : ∀ w < 25 + C0.gates.length, S w ⊆ U c →
          ∀ u ∈ S w, ∀ v ∈ S w, col u = col v := by
        intro w
        induction w using Nat.strongRecOn with
        | ind w ih =>
          intro hw hsub u hu v hv
          by_cases hw25 : w < 25
          · rw [hS_in ⟨w, hw25⟩, Finset.mem_singleton] at hu hv
            rw [hu, hv]
          · let j := w - 25
            have hj : j < C0.gates.length := by omega
            have hwj : w = 25 + j := by omega
            have hgat_mem : gateAt C0 j ∈ C0.gates := by
              unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
              exact List.getElem_mem hj
            rcases hC0_op _ hgat_mem with hop | hop
            · rw [hwj, hS_and j hj hop] at hu; exact absurd hu (Finset.notMem_empty _)
            · obtain ⟨_, h0lt, h1lt⟩ := hGateIn j hj
              rw [hwj, hS_or j hj hop] at hsub hu hv
              have hsub0 : S (opnd C0 j 0) ⊆ U c := Finset.Subset.trans Finset.subset_union_left hsub
              have hsub1 : S (opnd C0 j 1) ⊆ U c := Finset.Subset.trans Finset.subset_union_right hsub
              by_cases he0 : S (opnd C0 j 0) = ∅
              · rw [he0, Finset.empty_union] at hu hv
                exact ih (opnd C0 j 1) (by omega) (by omega) hsub1 u hu v hv
              · by_cases he1 : S (opnd C0 j 1) = ∅
                · rw [he1, Finset.union_empty] at hu hv
                  exact ih (opnd C0 j 0) (by omega) (by omega) hsub0 u hu v hv
                · by_cases hcard : (S (25 + j)).card ≤ 1
                  · have hu' : u ∈ S (25 + j) := by rw [hS_or j hj hop]; exact hu
                    have hv' : v ∈ S (25 + j) := by rw [hS_or j hj hop]; exact hv
                    have huv : u = v := Finset.card_le_one.1 hcard u hu' v hv'
                    rw [huv]
                  · have hj11 : j ∈ O_11 := by
                      simp only [O_11, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hop, he0, he1⟩
                    have hjT : j ∈ T c := by
                      simp only [T, Finset.mem_filter]
                      refine ⟨hj11, by omega, ?_⟩
                      rw [hS_or j hj hop]; exact hsub
                    have he_mem : pickEdge j ∈ es :=
                      List.mem_map.2 ⟨j, Finset.mem_toList.2 hjT, rfl⟩
                    have hx0 : (pickEdge j).1 ∈ S (opnd C0 j 0) := by
                      dsimp only [pickEdge]; simp only [hj11, ↓reduceDIte]
                      exact Classical.choose_spec (Finset.nonempty_iff_ne_empty.2 he0)
                    have hy1 : (pickEdge j).2 ∈ S (opnd C0 j 1) := by
                      dsimp only [pickEdge]; simp only [hj11, ↓reduceDIte]
                      exact Classical.choose_spec (Finset.nonempty_iff_ne_empty.2 he1)
                    have hbridge : col (pickEdge j).1 = col (pickEdge j).2 :=
                      hfold_mem es id (pickEdge j) he_mem
                    have hcol0 : ∀ z ∈ S (opnd C0 j 0), col z = col (pickEdge j).1 :=
                      fun z hz => ih (opnd C0 j 0) (by omega) (by omega) hsub0 z hz _ hx0
                    have hcol1 : ∀ z ∈ S (opnd C0 j 1), col z = col (pickEdge j).2 :=
                      fun z hz => ih (opnd C0 j 1) (by omega) (by omega) hsub1 z hz _ hy1
                    rcases Finset.mem_union.1 hu with hu0 | hu1 <;>
                      rcases Finset.mem_union.1 hv with hv0 | hv1
                    · rw [hcol0 u hu0, hcol0 v hv0]
                    · rw [hcol0 u hu0, hbridge, hcol1 v hv1]
                    · rw [hcol1 u hu1, ← hbridge, hcol0 v hv0]
                    · rw [hcol1 u hu1, hcol1 v hv1]
      let rep (j : ℕ) : Fin 25 :=
        if h : j ∈ Ac c then Classical.choose (hCtrL j (Finset.mem_filter.1 h).1).1 else ⟨0, by omega⟩
      have himg_sub : (U c).image col ⊆ (Ac c).image (fun j => col (rep j)) := by
        intro z hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hz
        obtain ⟨j, hjAc, huL⟩ := Finset.mem_biUnion.1 hu
        refine Finset.mem_image.2 ⟨j, hjAc, ?_⟩
        have hjA : j ∈ A := (Finset.mem_filter.1 hjAc).1
        have hjlt : j < C0.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hjA).1
        have hlw_lt : lwire j < 25 + C0.gates.length := by
          obtain ⟨_, h0lt, h1lt⟩ := hGateIn j hjlt
          dsimp only [lwire]; split_ifs <;> omega
        have hLsub : S (lwire j) ⊆ U c := fun x hx => Finset.mem_biUnion.2 ⟨j, hjAc, hx⟩
        have hrep_mem : rep j ∈ S (lwire j) := by
          dsimp only [rep]; simp only [hjAc, ↓reduceDIte]
          exact Classical.choose_spec (hCtrL j hjA).1
        exact hcol_const (lwire j) hlw_lt hLsub (rep j) hrep_mem u huL
      have hcard_img : ((U c).image col).card ≤ (Ac c).card :=
        (Finset.card_le_card himg_sub).trans Finset.card_image_le
      have hcard_es : es.length = (T c).card := by
        simp only [es, List.length_map, Finset.length_toList]
      have hmain := hfold_card es id
      simp only [Finset.image_id] at hmain
      rw [hcard_es] at hmain
      exact hmain.trans (Nat.add_le_add_right hcard_img _)
    have h48_le : 48 ≤ A.card + O_11.card := by
      calc 48 ≤ ∑ c : Fin 25, (U c).card := hSumU
        _ ≤ ∑ c : Fin 25, ((Ac c).card + (T c).card) := Finset.sum_le_sum fun c _ => hU_bound c
        _ = (∑ c : Fin 25, (Ac c).card) + (∑ c : Fin 25, (T c).card) := Finset.sum_add_distrib
        _ ≤ A.card + O_11.card := by rw [hSumAc_card]; exact Nat.add_le_add_left hSumT_le _
    let Wclean : Finset ℕ := A ∪ O_T
    have hdisj_AO : Disjoint A O_T := Finset.disjoint_left.2 fun j hj1 hj2 => by
      simp only [A, O_T, Finset.mem_filter] at hj1 hj2; rw [hj1.2] at hj2; cases hj2.2.1
    have hout_mem : out_g ∈ Wclean := by
      simp only [Wclean, A, O_T, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      have hgat_mem : gateAt C0 out_g ∈ C0.gates := by
        unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hout_g_lt, Option.getD_some]
        exact List.getElem_mem hout_g_lt
      rcases hC0_op _ hgat_mem with hop | hop
      · exact Or.inl ⟨hout_g_lt, hop⟩
      · right
        have hso := hS_out
        rw [hout_g_eq, hS_or out_g hout_g_lt hop, Finset.union_eq_empty] at hso
        exact ⟨hout_g_lt, hop, hso.1, hso.2⟩
    have hWclean_S : ∀ j ∈ Wclean, S (25 + j) = ∅ := by
      intro j hj
      simp only [Wclean, A, O_T, Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hj
      rcases hj with ⟨hjlt, hop⟩ | ⟨hjlt, hop, h0, h1⟩
      · exact hS_and j hjlt hop
      · rw [hS_or j hjlt hop, h0, h1, Finset.empty_union]
    have hWclean_lt : ∀ j ∈ Wclean, j < C0.gates.length := by
      intro j hj
      simp only [Wclean, A, O_T, Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hj
      rcases hj with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
    let rdr (j : ℕ) : ℕ :=
      if h : j < C0.gates.length ∧ 25 + j ≠ C0.output then
        Classical.choose (hLive j h.1 h.2)
      else 0
    have hrdr_mem : ∀ j ∈ Wclean.erase out_g,
        rdr j ∈ O_T ∪ O_01 ∧ 25 + j ∈ (gateAt C0 (rdr j)).inputs := by
      intro j hj
      obtain ⟨hne, hjW⟩ := Finset.mem_erase.1 hj
      have hjlt : j < C0.gates.length := hWclean_lt j hjW
      have hjne : 25 + j ≠ C0.output := by omega
      have hspec := Classical.choose_spec (hLive j hjlt hjne)
      have hr_eq : rdr j = Classical.choose (hLive j hjlt hjne) := by
        dsimp only [rdr]
        split_ifs with h
        · rfl
        · exact absurd ⟨hjlt, hjne⟩ h
      rw [← hr_eq] at hspec
      refine ⟨?_, hspec.2⟩
      have hgat_mem : gateAt C0 (rdr j) ∈ C0.gates := by
        unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hspec.1, Option.getD_some]
        exact List.getElem_mem hspec.1
      rcases hC0_op _ hgat_mem with hop | hop
      · exfalso
        exact hNoCleanInAnd (rdr j) hspec.1 hop (25 + j) hspec.2
          (hS_empty_clean (25 + j) (by omega) (hWclean_S j hjW))
      · obtain ⟨hins, _, _⟩ := hGateIn (rdr j) hspec.1
        have hin := hspec.2
        rw [hins, List.mem_cons, List.mem_singleton] at hin
        simp only [O_T, O_01, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
        have hSj := hWclean_S j hjW
        rcases hin with heq0 | heq1
        · have hs0 : S (opnd C0 (rdr j) 0) = ∅ := by rw [← heq0]; exact hSj
          by_cases hs1 : S (opnd C0 (rdr j) 1) = ∅
          · exact Or.inl ⟨hspec.1, hop, hs0, hs1⟩
          · exact Or.inr ⟨hspec.1, hop, Or.inl ⟨hs0, hs1⟩⟩
        · have hs1 : S (opnd C0 (rdr j) 1) = ∅ := by rw [← heq1]; exact hSj
          by_cases hs0 : S (opnd C0 (rdr j) 0) = ∅
          · exact Or.inl ⟨hspec.1, hop, hs0, hs1⟩
          · exact Or.inr ⟨hspec.1, hop, Or.inr ⟨hs0, hs1⟩⟩
    have hCleanCount : A.card - 1 ≤ O_T.card + O_01.card := by
      clear hU_bound h48_le hSumT_le hT_disj T hSumAc_card hAge12 hSumU hU_adj U Ac hCtrL L lwire ctr hAnd_sides hEdgeCov hNoC4 hDegLe4 hSingleFalse hEdgeTrue hPairTrue hAdj_iff hInc13_val hEset_card Eset hDeleteGate hNoCleanInAnd hValAnd hValOr hCleanAnd hC0_eval hC0_least hC0_fun hOutGate hS_out hS_sound hS_empty_clean hPart hC0_le57
      have hdisj_O : Disjoint O_T O_01 := Finset.disjoint_left.2 fun k hk1 hk2 => by
        simp only [O_T, O_01, Finset.mem_filter] at hk1 hk2
        rcases hk2.2.2 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h hk1.2.2.2
        · exact h hk1.2.2.1
      have hfib_sum : (Wclean.erase out_g).card =
          ∑ k ∈ O_T ∪ O_01, ((Wclean.erase out_g).filter fun j => rdr j = k).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext j
          simp only [Finset.mem_biUnion, Finset.mem_filter]
          exact ⟨fun hj => ⟨rdr j, (hrdr_mem j hj).1, hj, rfl⟩, fun h => h.choose_spec.2.1⟩
        · intro k1 _ k2 _ hne
          exact Finset.disjoint_left.2 fun j hj1 hj2 => by
            simp only [Finset.mem_filter] at hj1 hj2; exact hne (hj1.2.symm.trans hj2.2)
      have hfib_T : ∀ k ∈ O_T, ((Wclean.erase out_g).filter fun j => rdr j = k).card ≤ 2 := by
        intro k hk
        have hklt : k < C0.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
        obtain ⟨hins, _, _⟩ := hGateIn k hklt
        have hsub : ((Wclean.erase out_g).filter fun j => rdr j = k) ⊆
            {opnd C0 k 0 - 25, opnd C0 k 1 - 25} := by
          intro j hj
          obtain ⟨hjW, hrk⟩ := Finset.mem_filter.1 hj
          have hin := (hrdr_mem j hjW).2
          rw [hrk, hins, List.mem_cons, List.mem_singleton] at hin
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hin with h | h <;> [left; right] <;> omega
        exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp only [Finset.card_singleton, le_refl]))
      have hfib_01 : ∀ k ∈ O_01, ((Wclean.erase out_g).filter fun j => rdr j = k).card ≤ 1 := by
        intro k hk
        simp only [O_01, Finset.mem_filter, Finset.mem_range] at hk
        obtain ⟨hins, _, _⟩ := hGateIn k hk.1
        rcases hk.2.2 with ⟨_, hne1⟩ | ⟨hne0, _⟩
        · have hsub : ((Wclean.erase out_g).filter fun j => rdr j = k) ⊆ {opnd C0 k 0 - 25} := by
            intro j hj
            obtain ⟨hjW, hrk⟩ := Finset.mem_filter.1 hj
            have hin := (hrdr_mem j hjW).2
            rw [hrk, hins, List.mem_cons, List.mem_singleton] at hin
            simp only [Finset.mem_singleton]
            rcases hin with h | h
            · omega
            · exfalso; apply hne1; rw [← h]; exact hWclean_S j (Finset.mem_of_mem_erase hjW)
          exact (Finset.card_le_card hsub).trans (by simp only [Finset.card_singleton, le_refl])
        · have hsub : ((Wclean.erase out_g).filter fun j => rdr j = k) ⊆ {opnd C0 k 1 - 25} := by
            intro j hj
            obtain ⟨hjW, hrk⟩ := Finset.mem_filter.1 hj
            have hin := (hrdr_mem j hjW).2
            rw [hrk, hins, List.mem_cons, List.mem_singleton] at hin
            simp only [Finset.mem_singleton]
            rcases hin with h | h
            · exfalso; apply hne0; rw [← h]; exact hWclean_S j (Finset.mem_of_mem_erase hjW)
            · omega
          exact (Finset.card_le_card hsub).trans (by simp only [Finset.card_singleton, le_refl])
      have hbound : (Wclean.erase out_g).card ≤ 2 * O_T.card + O_01.card := by
        rw [hfib_sum, Finset.sum_union hdisj_O]
        calc (∑ k ∈ O_T, ((Wclean.erase out_g).filter fun j => rdr j = k).card) +
              (∑ k ∈ O_01, ((Wclean.erase out_g).filter fun j => rdr j = k).card)
            ≤ (∑ _k ∈ O_T, 2) + (∑ _k ∈ O_01, 1) :=
              Nat.add_le_add (Finset.sum_le_sum hfib_T) (Finset.sum_le_sum hfib_01)
          _ = 2 * O_T.card + O_01.card := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm, Finset.sum_const, smul_eq_mul, mul_one]
      have hcard_er : (Wclean.erase out_g).card = A.card + O_T.card - 1 := by
        rw [Finset.card_erase_of_mem hout_mem, Finset.card_union_of_disjoint hdisj_AO]
      omega
    have hsz_eq : C0.size = C0.gates.length := rfl
    omega
  by_cases hj0 : (junk G C0).card = 0
  · exact hCleanImpossible hj0
  · by_cases hj1 : (junk G C0).card = 1
    · exact h_one_dirty C0 hC0_le57 hC0_least hj1
    · have hj2 : 2 ≤ (junk G C0).card := by omega
      by_cases hch : ∃ i ∈ junk G C0, ∃ j ∈ junk G C0, InCone 25 C0 i j
      · exact h_chain C0 hC0_le57 hC0_least hj2 hch
      · exact h_antichain C0 hC0_le57 hC0_least hj2 (fun i hi j hj hc => hch ⟨i, hi, j, hj, hc⟩)
