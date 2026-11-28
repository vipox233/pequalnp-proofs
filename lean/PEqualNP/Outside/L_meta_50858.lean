import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_50858_aux
open PEqualNP.CircuitLowerBounds

def gv (g : Gate) (V : List Nat) : Nat :=
  (match g.op with
    | GateOp.and => (g.inputs.map fun i => V.getD i 0).foldr (fun a b => a &&& b) 63
    | GateOp.or => (g.inputs.map fun i => V.getD i 0).foldr (fun a b => a ||| b) 0
    | GateOp.not => 63 ^^^ (g.inputs.map fun i => V.getD i 0).headD 0
    | _ => 0) &&& 63

def vw : List Gate → List Nat → List Nat
  | [], V => V
  | g :: gs, V => vw gs (V ++ [gv g V])

def RB : Nat → List Gate → Prop
  | _, [] => True
  | n, g :: gs => (∀ i ∈ g.inputs, i < n) ∧ RB (n + 1) gs

def elems (m : Nat) : List Nat := (List.range 64).filter fun u => m.testBit u

def orAll (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | a :: l => f a ||| orAll f l

def cAO (m : Nat) : Nat :=
  1 ||| (1 <<< 63) ||| orAll (fun u => orAll (fun v => (1 <<< (u &&& v)) ||| (1 <<< (u ||| v))) (elems m)) (elems m)

def cN (m : Nat) : Nat := orAll (fun u => 1 <<< (63 ^^^ u)) (elems m)

def allIn (T : List Nat) (m : Nat) : Bool := T.all fun x => m.testBit x

def reach (T : List Nat) : Nat → Nat → Nat → Bool
  | m, _, 0 => allIn T m
  | m, b, k + 1 => allIn T m || (List.range 64).any fun w => !m.testBit w &&
      ((cAO m).testBit w && reach T (m ||| 1 <<< w) b k ||
        (decide (0 < b) && (cN m).testBit w && reach T (m ||| 1 <<< w) (b - 1) k))

theorem h31 : ∀ t < 6, (63 : Nat).testBit t = true := by decide

theorem fold_and (t : Nat) : ∀ l : List Nat,
    (l.map fun x => x.testBit t).all id = (l.foldr (fun a b => a &&& b) 63 &&& 63).testBit t ∨ t ≥ 6
  | [] => by
    by_cases ht : t < 6
    · left; simp [Nat.testBit_and, h31 t ht]
    · right; omega
  | a :: l => by
    rcases fold_and t l with h | h
    · left; simp only [List.map_cons, List.all_cons, List.foldr_cons, Nat.testBit_and] at h ⊢
      rw [h]; cases a.testBit t <;> simp [Bool.and_assoc]
    · right; exact h

theorem fold_or (t : Nat) : ∀ l : List Nat,
    (l.map fun x => x.testBit t).any id = (l.foldr (fun a b => a ||| b) 0).testBit t
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.any_cons, List.foldr_cons, Nat.testBit_or, fold_or t l]
    rfl

theorem getD_map (V : List Nat) (t i : Nat) :
    (V.map fun x => x.testBit t).getD i false = (V.getD i 0).testBit t := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases V[i]? <;> simp

theorem step (t : Nat) (ht : t < 6) (g : Gate) (V : List Nat)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    g.op.eval (g.inputs.map fun i => (V.map fun x => x.testBit t).getD i false) = (gv g V).testBit t := by
  have hl : (g.inputs.map fun i => (V.map fun x => x.testBit t).getD i false)
      = (g.inputs.map fun i => V.getD i 0).map (fun x => x.testBit t) := by
    simp only [List.map_map, Function.comp_def, getD_map]
  rw [hl]
  obtain ⟨op, ins⟩ := g
  simp only at hop
  rcases hop with rfl | rfl | rfl
  · simp only [gv]
    generalize ins.map (fun i => V.getD i 0) = l
    rcases fold_and t l with h | h
    · simp only [GateOp.eval]; exact h
    · omega
  · simp only [gv]
    generalize ins.map (fun i => V.getD i 0) = l
    simp only [GateOp.eval]
    rw [Nat.testBit_and, h31 t ht, Bool.and_true]
    exact fold_or t l
  · simp only [gv]
    generalize ins.map (fun i => V.getD i 0) = l
    cases l <;> simp [GateOp.eval, Nat.testBit_and, Nat.testBit_xor, h31 t ht]

theorem fold_eq (t : Nat) (ht : t < 6) : ∀ (gs : List Gate) (V : List Nat),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (V.map fun x => x.testBit t)
      = (vw gs V).map fun x => x.testBit t
  | [], V, _ => rfl
  | g :: gs, V, h => by
    rw [List.foldl_cons, step t ht g V (h g (List.mem_cons_self ..))]
    have e : (V.map fun x => x.testBit t) ++ [(gv g V).testBit t] = (V ++ [gv g V]).map fun x => x.testBit t := by
      simp
    rw [e]
    exact fold_eq t ht gs _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

theorem gv_lt (g : Gate) (V : List Nat) : gv g V < 64 := by
  unfold gv
  have := Nat.and_le_right (n := (match g.op with
    | GateOp.and => (g.inputs.map fun i => V.getD i 0).foldr (fun a b => a &&& b) 63
    | GateOp.or => (g.inputs.map fun i => V.getD i 0).foldr (fun a b => a ||| b) 0
    | GateOp.not => 63 ^^^ (g.inputs.map fun i => V.getD i 0).headD 0
    | _ => 0)) (m := 63)
  omega

theorem vw_lt : ∀ (gs : List Gate) (V : List Nat), (∀ x ∈ V, x < 64) → ∀ x ∈ vw gs V, x < 64
  | [], V, h => h
  | g :: gs, V, h => vw_lt gs _ (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h x hx
      · rw [List.mem_singleton.1 hx]; exact gv_lt g V)

theorem vw_len : ∀ (gs : List Gate) (V : List Nat), (vw gs V).length = V.length + gs.length
  | [], V => rfl
  | g :: gs, V => by
    rw [vw, vw_len gs]
    simp; omega

theorem rb_of : ∀ (gs : List Gate) (n o : Nat),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨gs, o⟩ → RB n gs
  | [], _, _, _ => trivial
  | g :: gs, n, o, h => by
    refine ⟨fun i hi => ?_, rb_of gs (n + 1) o (fun j hj i hi => ?_)⟩
    · have := h 0 (by simp) i (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hi)
      simpa using this
    · have := h (j + 1) (by simp at hj ⊢; omega) i
        (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hi)
      omega

theorem orAll_mem (f : Nat → Nat) (x y : Nat) : ∀ l : List Nat, y ∈ l → (f y).testBit x = true →
    (orAll f l).testBit x = true
  | [], h, _ => by simp at h
  | a :: l, h, hy => by
    simp only [orAll, Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl hy
    · exact Or.inr (orAll_mem f x y l h hy)

theorem mem_elems {m u : Nat} (hu : u < 64) (hm : m.testBit u = true) : u ∈ elems m := by
  simp [elems, List.mem_filter, List.mem_range, hu, hm]

theorem bit_self (w : Nat) : (1 <<< w).testBit w = true := by
  simp [Nat.one_shiftLeft, Nat.testBit_two_pow_self]

theorem cAO_and {m u v : Nat} (hu : u < 64) (hmu : m.testBit u = true) (hv : v < 64)
    (hmv : m.testBit v = true) : (cAO m).testBit (u &&& v) = true := by
  unfold cAO
  rw [Nat.testBit_or, orAll_mem _ _ u _ (mem_elems hu hmu)]
  · simp
  · apply orAll_mem _ _ v _ (mem_elems hv hmv)
    rw [Nat.testBit_or, bit_self]; simp

theorem cAO_or {m u v : Nat} (hu : u < 64) (hmu : m.testBit u = true) (hv : v < 64)
    (hmv : m.testBit v = true) : (cAO m).testBit (u ||| v) = true := by
  unfold cAO
  rw [Nat.testBit_or, orAll_mem _ _ u _ (mem_elems hu hmu)]
  · simp
  · apply orAll_mem _ _ v _ (mem_elems hv hmv)
    rw [Nat.testBit_or, bit_self]; simp

theorem cAO_0 (m : Nat) : (cAO m).testBit 0 = true := by
  unfold cAO; simp [Nat.testBit_or]

theorem cAO_31 (m : Nat) : (cAO m).testBit 63 = true := by
  unfold cAO; rw [Nat.testBit_or, Nat.testBit_or, bit_self]; simp

theorem cN_not {m u : Nat} (hu : u < 64) (hmu : m.testBit u = true) : (cN m).testBit (63 ^^^ u) = true :=
  orAll_mem _ _ u _ (mem_elems hu hmu) (bit_self _)

theorem k1 : ∀ x < 64, (x &&& 63) &&& 63 = x &&& x := by decide +kernel
theorem k2 : ∀ x < 64, (x ||| 0) &&& 63 = x &&& x := by decide +kernel
theorem k3 : ∀ x < 64, (63 ^^^ x) &&& 63 = 63 ^^^ x := by decide +kernel
theorem k4 : ∀ x < 64, ∀ y < 64, (x &&& (y &&& 63)) &&& 63 = x &&& y := by decide +kernel
theorem k5 : ∀ x < 64, ∀ y < 64, (x ||| (y ||| 0)) &&& 63 = x ||| y := by decide +kernel
theorem k6 : ∀ x < 64, ∀ a < 64, (∀ t < 6, x.testBit t = a.testBit t) → x = a := by decide +kernel

theorem getD_mem {V : List Nat} {i : Nat} (h : i < V.length) : V.getD i 0 ∈ V := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

theorem gv_cases (m : Nat) (g : Gate) (V : List Nat)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (hl : g.inputs.length ≤ 2)
    (hr : ∀ i ∈ g.inputs, i < V.length) (hV : ∀ x ∈ V, x < 64 ∧ m.testBit x = true) :
    (cAO m).testBit (gv g V) = true ∨ (g.op = GateOp.not ∧ (cN m).testBit (gv g V) = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hl hr
  match ins, hl, hr with
  | [], _, _ =>
    rcases hop with rfl | rfl | rfl
    · left; rw [show gv ⟨GateOp.and, []⟩ V = 63 by simp [gv]]; exact cAO_31 m
    · left; rw [show gv ⟨GateOp.or, []⟩ V = 0 by simp [gv]]; exact cAO_0 m
    · left; rw [show gv ⟨GateOp.not, []⟩ V = 63 by simp [gv]]; exact cAO_31 m
  | [a], _, hr =>
    have ha := hV _ (getD_mem (hr a (by simp)))
    rcases hop with rfl | rfl | rfl
    · left
      rw [show gv ⟨GateOp.and, [a]⟩ V = (V.getD a 0 &&& 63) &&& 63 from rfl, k1 _ ha.1]
      exact cAO_and ha.1 ha.2 ha.1 ha.2
    · left
      rw [show gv ⟨GateOp.or, [a]⟩ V = (V.getD a 0 ||| 0) &&& 63 from rfl, k2 _ ha.1]
      exact cAO_and ha.1 ha.2 ha.1 ha.2
    · right
      refine ⟨rfl, ?_⟩
      rw [show gv ⟨GateOp.not, [a]⟩ V = (63 ^^^ V.getD a 0) &&& 63 from rfl, k3 _ ha.1]
      exact cN_not ha.1 ha.2
  | [a, b], _, hr =>
    have ha := hV _ (getD_mem (hr a (by simp)))
    have hb := hV _ (getD_mem (hr b (by simp)))
    rcases hop with rfl | rfl | rfl
    · left
      rw [show gv ⟨GateOp.and, [a, b]⟩ V = (V.getD a 0 &&& (V.getD b 0 &&& 63)) &&& 63 from rfl,
        k4 _ ha.1 _ hb.1]
      exact cAO_and ha.1 ha.2 hb.1 hb.2
    · left
      rw [show gv ⟨GateOp.or, [a, b]⟩ V = (V.getD a 0 ||| (V.getD b 0 ||| 0)) &&& 63 from rfl,
        k5 _ ha.1 _ hb.1]
      exact cAO_or ha.1 ha.2 hb.1 hb.2
    · right
      refine ⟨rfl, ?_⟩
      rw [show gv ⟨GateOp.not, [a, b]⟩ V = (63 ^^^ V.getD a 0) &&& 63 from rfl, k3 _ ha.1]
      exact cN_not ha.1 ha.2
  | _ :: _ :: _ :: _, hl, _ => simp at hl

theorem reach_eq (T : List Nat) (m b k : Nat) : reach T m b (k + 1) = (allIn T m || (List.range 64).any fun w => !m.testBit w &&
      ((cAO m).testBit w && reach T (m ||| 1 <<< w) b k ||
        (decide (0 < b) && (cN m).testBit w && reach T (m ||| 1 <<< w) (b - 1) k))) := rfl

theorem reach_succ (T : List Nat) : ∀ (k m b : Nat), reach T m b k = true → reach T m b (k + 1) = true
  | 0, m, b, h => by
    rw [reach_eq]
    simp only [reach] at h
    simp [h]
  | k + 1, m, b, h => by
    rw [reach_eq] at h ⊢
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with h | ⟨w, hw, h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨w, hw, h1, ?_⟩
      rcases h2 with ⟨h3, h4⟩ | ⟨h5, h7⟩
      · exact Or.inl ⟨h3, reach_succ T k _ _ h4⟩
      · exact Or.inr ⟨h5, reach_succ T k _ _ h7⟩

theorem notc_cons (g : Gate) (gs : List Gate) (b : Nat) (h : PEqualNP.NotBracket.notCount ⟨g :: gs, 0⟩ ≤ b) :
    PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b ∧
      (g.op = GateOp.not → PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + 1 ≤ b) := by
  unfold PEqualNP.NotBracket.notCount at h ⊢
  dsimp only at h ⊢
  rw [List.filter_cons] at h
  by_cases hg : g.op = GateOp.not
  · simp only [hg, decide_true, if_true, List.length_cons] at h
    exact ⟨by omega, fun _ => h⟩
  · simp only [hg, decide_false] at h
    exact ⟨by simpa using h, fun h' => absurd h' hg⟩

theorem sound (T : List Nat) : ∀ (gs : List Gate) (V : List Nat) (m b k : Nat),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    RB V.length gs →
    (∀ x ∈ V, x < 64 ∧ m.testBit x = true) →
    PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b → gs.length ≤ k →
    (∀ a ∈ T, a ∈ vw gs V) → reach T m b k = true
  | [], V, m, b, k, _, _, hV, _, _, hT => by
    have hA : allIn T m = true := by
      simp only [allIn, List.all_eq_true]
      intro a ha
      exact (hV a (hT a ha)).2
    cases k with
    | zero => simpa [reach] using hA
    | succ k => simp [reach, hA]
  | g :: gs, V, m, b, k, hF, hR, hV, hN, hk, hT => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hg := hF g (List.mem_cons_self ..)
    have hF' : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 :=
      fun g' h' => hF g' (List.mem_cons_of_mem _ h')
    obtain ⟨hR0, hR'⟩ := hR
    have hR2 : RB (V ++ [gv g V]).length gs := by simpa using hR'
    have hN2 := notc_cons g gs b hN
    have hk' : gs.length ≤ k := by simp at hk; omega
    have hT' : ∀ a ∈ T, a ∈ vw gs (V ++ [gv g V]) := hT
    have hv32 : gv g V < 64 := gv_lt g V
    have hc := gv_cases m g V hg.1 hg.2 hR0 hV
    by_cases hin : m.testBit (gv g V) = true
    · have hV' : ∀ x ∈ V ++ [gv g V], x < 64 ∧ m.testBit x = true := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hV x hx
        · rw [List.mem_singleton.1 hx]; exact ⟨hv32, hin⟩
      exact reach_succ T k m b (sound T gs _ m b k hF' hR2 hV' hN2.1 hk' hT')
    · have hV' : ∀ x ∈ V ++ [gv g V], x < 64 ∧ (m ||| 1 <<< gv g V).testBit x = true := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact ⟨(hV x hx).1, by rw [Nat.testBit_or, (hV x hx).2]; rfl⟩
        · rw [List.mem_singleton.1 hx]; exact ⟨hv32, by rw [Nat.testBit_or, bit_self]; simp⟩
      simp only [reach, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
      right
      refine ⟨gv g V, List.mem_range.2 hv32, by simpa using hin, ?_⟩
      rcases hc with hc | ⟨hop, hc⟩
      · exact Or.inl ⟨hc, sound T gs _ _ b k hF' hR2 hV' hN2.1 hk' hT'⟩
      · have hb := hN2.2 hop
        exact Or.inr ⟨⟨by simp; omega, hc⟩, sound T gs _ _ (b - 1) k hF' hR2 hV' (by omega) hk' hT'⟩

theorem inp : ∀ t : Fin 6, (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]
    = [62, 60, 56, 48, 32, 0, 63].map fun x => x.testBit t.val := by decide

def last (T : List Nat) (m b : Nat) : Bool :=
  allIn T m || (List.range 64).any fun w => !m.testBit w &&
    (allIn T (m ||| 1 <<< w) && ((cAO m).testBit w || (decide (0 < b) && (cN m).testBit w)))

theorem last_eq (T : List Nat) (m b : Nat) : last T m b = reach T m b 1 := by
  rw [reach_eq]
  unfold last
  congr 2
  funext w
  simp only [reach]
  cases (!m.testBit w) <;> cases allIn T (m ||| 1 <<< w) <;> cases (cAO m).testBit w <;>
    cases decide (0 < b) <;> cases (cN m).testBit w <;> rfl

def reachX (tbl : List (Nat × Nat)) (kk : Nat) (T : List Nat) : Nat → Nat → Nat → Bool
  | m, _, 0 => allIn T m
  | m, b, k + 1 => !(decide (k + 1 = kk) && tbl.contains (m, b)) && (if k = 0 then last T m b else
      (allIn T m || (List.range 64).any fun w => !m.testBit w &&
      ((cAO m).testBit w && reachX tbl kk T (m ||| 1 <<< w) b k ||
        (decide (0 < b) && (cN m).testBit w && reachX tbl kk T (m ||| 1 <<< w) (b - 1) k))))

theorem reachX_def (tbl : List (Nat × Nat)) (kk : Nat) (T : List Nat) (m b k : Nat) :
    reachX tbl kk T m b (k + 1) = (!(decide (k + 1 = kk) && tbl.contains (m, b)) && (if k = 0 then last T m b else
      (allIn T m || (List.range 64).any fun w => !m.testBit w &&
      ((cAO m).testBit w && reachX tbl kk T (m ||| 1 <<< w) b k ||
        (decide (0 < b) && (cN m).testBit w && reachX tbl kk T (m ||| 1 <<< w) (b - 1) k))))) := rfl

theorem reachX_eq (tbl : List (Nat × Nat)) (kk : Nat) (T : List Nat)
    (h : ∀ e ∈ tbl, reach T e.1 e.2 kk = false) : ∀ (k m b : Nat), reachX tbl kk T m b k = reach T m b k
  | 0, m, b => rfl
  | k + 1, m, b => by
    have ih := reachX_eq tbl kk T h k
    by_cases hc : (decide (k + 1 = kk) && tbl.contains (m, b)) = true
    · have hc2 := hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hc2
      have h2 : reach T m b (k + 1) = false := by
        rw [hc2.1]; exact h (m, b) hc2.2
      rw [reachX_def, hc, h2]; rfl
    · simp only [Bool.not_eq_true] at hc
      rw [reachX_def, hc]
      by_cases hk0 : k = 0
      · subst hk0
        rw [if_pos rfl]
        simp only [Bool.not_false, Bool.true_and]
        exact last_eq T m b
      · rw [if_neg hk0, reach_eq]
        simp only [ih, Bool.not_false, Bool.true_and]

theorem rx0 (T : List Nat) (m b k : Nat) : reach T m b k = reachX [] 0 T m b k :=
  (reachX_eq [] 0 T (by intro e h; cases h) k m b).symm

theorem s_0 : reachX [] 0 [28, 36, 54] 15060318633198616591 0 3 = false := by decide +kernel
theorem s_1 : reachX [] 0 [28, 36, 54] 15060318633198616717 0 3 = false := by decide +kernel
theorem s_2 : reachX [] 0 [28, 36, 54] 15060318633198616723 0 3 = false := by decide +kernel
theorem s_3 : reachX [] 0 [28, 36, 54] 15060318633198616729 0 3 = false := by decide +kernel
theorem s_4 : reachX [] 0 [28, 36, 54] 15060318633198616771 0 3 = false := by decide +kernel
theorem s_5 : reachX [] 0 [28, 36, 54] 15060318633198616777 0 3 = false := by decide +kernel
theorem s_6 : reachX [] 0 [28, 36, 54] 15060318633198616785 1 3 = false := by decide +kernel
theorem s_7 : reachX [] 0 [28, 36, 54] 15060318633198649357 0 3 = false := by decide +kernel
theorem s_8 : reachX [] 0 [28, 36, 54] 15060318633198649489 0 3 = false := by decide +kernel
theorem s_9 : reachX [] 0 [28, 36, 54] 15060318633198649537 0 3 = false := by decide +kernel
theorem s_10 : reachX [] 0 [28, 36, 54] 15060318633198649603 0 3 = false := by decide +kernel
theorem s_11 : reachX [] 0 [28, 36, 54] 15060318633198649609 0 3 = false := by decide +kernel
theorem s_12 : reachX [] 0 [28, 36, 54] 15060318633198649729 0 3 = false := by decide +kernel
theorem s_13 : reachX [] 0 [28, 36, 54] 15060318633198653443 0 3 = false := by decide +kernel
theorem s_14 : reachX [] 0 [28, 36, 54] 15060318633198653449 0 3 = false := by decide +kernel
theorem s_15 : reachX [] 0 [28, 36, 54] 15060318633198653569 0 3 = false := by decide +kernel
theorem s_16 : reachX [] 0 [28, 36, 54] 15060318633198653697 1 3 = false := by decide +kernel
theorem s_17 : reachX [] 0 [28, 36, 54] 15060318633198665731 0 3 = false := by decide +kernel
theorem s_18 : reachX [] 0 [28, 36, 54] 15060318633198665737 0 3 = false := by decide +kernel
theorem s_19 : reachX [] 0 [28, 36, 54] 15060318633198665857 0 3 = false := by decide +kernel
theorem s_20 : reachX [] 0 [28, 36, 54] 15060318633198665985 1 3 = false := by decide +kernel
theorem s_21 : reachX [] 0 [28, 36, 54] 15060318633198669825 1 3 = false := by decide +kernel
theorem s_22 : reachX [] 0 [28, 36, 54] 15060318635346100237 0 3 = false := by decide +kernel
theorem s_23 : reachX [] 0 [28, 36, 54] 15060318635346100369 0 3 = false := by decide +kernel
theorem s_24 : reachX [] 0 [28, 36, 54] 15060318635346100417 0 3 = false := by decide +kernel
theorem s_25 : reachX [] 0 [28, 36, 54] 15060318635346133249 0 3 = false := by decide +kernel
theorem s_26 : reachX [] 0 [28, 36, 54] 15060318635346137089 0 3 = false := by decide +kernel
theorem s_27 : reachX [] 0 [28, 36, 54] 15060318635346149377 0 3 = false := by decide +kernel
theorem s_28 : reachX [] 0 [28, 36, 54] 15060318635346165763 0 3 = false := by decide +kernel
theorem s_29 : reachX [] 0 [28, 36, 54] 15060318635346165769 0 3 = false := by decide +kernel
theorem s_30 : reachX [] 0 [28, 36, 54] 15060318635346165889 0 3 = false := by decide +kernel
theorem s_31 : reachX [] 0 [28, 36, 54] 15060318635346198529 0 3 = false := by decide +kernel
theorem s_32 : reachX [] 0 [28, 36, 54] 15060318635362877443 0 3 = false := by decide +kernel
theorem s_33 : reachX [] 0 [28, 36, 54] 15060318635362877449 0 3 = false := by decide +kernel
theorem s_34 : reachX [] 0 [28, 36, 54] 15060318635362877569 0 3 = false := by decide +kernel
theorem s_35 : reachX [] 0 [28, 36, 54] 15060318635362910209 0 3 = false := by decide +kernel
theorem s_36 : reachX [] 0 [28, 36, 54] 15060318635362942977 1 3 = false := by decide +kernel
theorem s_37 : reachX [] 0 [28, 36, 54] 15060318635614535683 0 3 = false := by decide +kernel
theorem s_38 : reachX [] 0 [28, 36, 54] 15060318635614535689 0 3 = false := by decide +kernel
theorem s_39 : reachX [] 0 [28, 36, 54] 15060318635614535809 0 3 = false := by decide +kernel
theorem s_40 : reachX [] 0 [28, 36, 54] 15060318635614568449 0 3 = false := by decide +kernel
theorem s_41 : reachX [] 0 [28, 36, 54] 15060318635614601217 1 3 = false := by decide +kernel
theorem s_42 : reachX [] 0 [28, 36, 54] 15060318635631312897 1 3 = false := by decide +kernel
theorem s_43 : reachX [] 0 [28, 36, 54] 15060318636419842051 0 3 = false := by decide +kernel
theorem s_44 : reachX [] 0 [28, 36, 54] 15060318636419842057 0 3 = false := by decide +kernel
theorem s_45 : reachX [] 0 [28, 36, 54] 15060318636419842177 0 3 = false := by decide +kernel
theorem s_46 : reachX [] 0 [28, 36, 54] 15060318636419874817 0 3 = false := by decide +kernel
theorem s_47 : reachX [] 0 [28, 36, 54] 15060318636419907585 1 3 = false := by decide +kernel
theorem s_48 : reachX [] 0 [28, 36, 54] 15060318636436619265 1 3 = false := by decide +kernel
theorem s_49 : reachX [] 0 [28, 36, 54] 15060318636688277505 1 3 = false := by decide +kernel
theorem s_50 : reachX [] 0 [28, 36, 54] 15060318641788551179 0 3 = false := by decide +kernel
theorem s_51 : reachX [] 0 [28, 36, 54] 15060318641788551299 0 3 = false := by decide +kernel
theorem s_52 : reachX [] 0 [28, 36, 54] 15060318641788583939 0 3 = false := by decide +kernel
theorem s_53 : reachX [] 0 [28, 36, 54] 15060318642862292995 0 3 = false := by decide +kernel
theorem s_54 : reachX [] 0 [28, 36, 54] 15060318643936034819 0 3 = false := by decide +kernel
theorem s_55 : reachX [] 0 [28, 36, 54] 15060318645009776641 0 3 = false := by decide +kernel
theorem s_56 : reachX [] 0 [28, 36, 54] 15060318650378485773 1 3 = false := by decide +kernel
theorem s_57 : reachX [] 0 [28, 36, 54] 15060318667558354955 0 3 = false := by decide +kernel
theorem s_58 : reachX [] 0 [28, 36, 54] 15060318667558354957 1 3 = false := by decide +kernel
theorem s_59 : reachX [] 0 [28, 36, 54] 15060318667558355081 0 3 = false := by decide +kernel
theorem s_60 : reachX [] 0 [28, 36, 54] 15060318667558387721 0 3 = false := by decide +kernel
theorem s_61 : reachX [] 0 [28, 36, 54] 15060318667826790409 0 3 = false := by decide +kernel
theorem s_62 : reachX [] 0 [28, 36, 54] 15060318669705838601 0 3 = false := by decide +kernel
theorem s_63 : reachX [] 0 [28, 36, 54] 15060318669974274049 0 3 = false := by decide +kernel
theorem s_64 : reachX [] 0 [28, 36, 54] 15060318684738224137 1 3 = false := by decide +kernel
theorem s_65 : reachX [] 0 [28, 36, 54] 15060318701918093457 1 3 = false := by decide +kernel
theorem s_66 : reachX [] 0 [28, 36, 54] 15060318908076523713 1 3 = false := by decide +kernel
theorem s_67 : reachX [] 0 [28, 36, 54] 15060319182954430595 0 3 = false := by decide +kernel
theorem s_68 : reachX [] 0 [28, 36, 54] 15060319182954430601 0 3 = false := by decide +kernel
theorem s_69 : reachX [] 0 [28, 36, 54] 15060319182954430609 1 3 = false := by decide +kernel
theorem s_70 : reachX [] 0 [28, 36, 54] 15060319182954430657 1 3 = false := by decide +kernel
theorem s_71 : reachX [] 0 [28, 36, 54] 15060319182954463361 0 3 = false := by decide +kernel
theorem s_72 : reachX [] 0 [28, 36, 54] 15060319182971207809 0 3 = false := by decide +kernel
theorem s_73 : reachX [] 0 [28, 36, 54] 15060319185101914241 0 3 = false := by decide +kernel
theorem s_74 : reachX [] 0 [28, 36, 54] 15060319185118691329 0 3 = false := by decide +kernel
theorem s_75 : reachX [] 0 [28, 36, 54] 15060319251673907329 1 3 = false := by decide +kernel
theorem s_76 : reachX [] 0 [28, 36, 54] 15060319457832337537 1 3 = false := by decide +kernel
theorem s_77 : reachX [] 0 [28, 36, 54] 15060319732710277377 1 3 = false := by decide +kernel
theorem s_78 : reachX [] 0 [28, 36, 54] 15060336225384697857 1 3 = false := by decide +kernel
theorem s_79 : reachX [] 0 [28, 36, 54] 15060389001942843393 1 3 = false := by decide +kernel
theorem s_80 : reachX [] 0 [28, 36, 54] 15060459370687004675 0 3 = false := by decide +kernel
theorem s_81 : reachX [] 0 [28, 36, 54] 15060459370687004681 0 3 = false := by decide +kernel
theorem s_82 : reachX [] 0 [28, 36, 54] 15060459370687004801 0 3 = false := by decide +kernel
theorem s_83 : reachX [] 0 [28, 36, 54] 15060459370687004929 1 3 = false := by decide +kernel
theorem s_84 : reachX [] 0 [28, 36, 54] 15060459370687008769 1 3 = false := by decide +kernel
theorem s_85 : reachX [] 0 [28, 36, 54] 15060459370687021057 1 3 = false := by decide +kernel
theorem s_86 : reachX [] 0 [28, 36, 54] 15060459370687070209 0 3 = false := by decide +kernel
theorem s_87 : reachX [] 0 [28, 36, 54] 15060459372834488321 0 3 = false := by decide +kernel
theorem s_88 : reachX [] 0 [28, 36, 54] 15060459372834521089 0 3 = false := by decide +kernel
theorem s_89 : reachX [] 0 [28, 36, 54] 15060460470198632449 1 3 = false := by decide +kernel
theorem s_90 : reachX [] 0 [28, 36, 54] 15060476962873049089 1 3 = false := by decide +kernel
theorem s_91 : reachX [] 0 [28, 36, 54] 15060529739431182337 1 3 = false := by decide +kernel
theorem s_92 : reachX [] 0 [28, 36, 54] 15060881583152037899 0 3 = false := by decide +kernel
theorem s_93 : reachX [] 0 [28, 36, 54] 15060881583152038019 0 3 = false := by decide +kernel
theorem s_94 : reachX [] 0 [28, 36, 54] 15060881583152054275 0 3 = false := by decide +kernel
theorem s_95 : reachX [] 0 [28, 36, 54] 15060881583152070659 0 3 = false := by decide +kernel
theorem s_96 : reachX [] 0 [28, 36, 54] 15060881583152087041 0 3 = false := by decide +kernel
theorem s_97 : reachX [] 0 [28, 36, 54] 15060881585299521539 0 3 = false := by decide +kernel
theorem s_98 : reachX [] 0 [28, 36, 54] 15060881591741972483 1 3 = false := by decide +kernel
theorem s_99 : reachX [] 0 [28, 36, 54] 15061444533105459213 1 3 = false := by decide +kernel
theorem s_100 : reachX [] 0 [28, 36, 54] 15062570433012301835 0 3 = false := by decide +kernel
theorem s_101 : reachX [] 0 [28, 36, 54] 15062570433012301837 1 3 = false := by decide +kernel
theorem s_102 : reachX [] 0 [28, 36, 54] 15062570433012301961 0 3 = false := by decide +kernel
theorem s_103 : reachX [] 0 [28, 36, 54] 15062570433012305929 0 3 = false := by decide +kernel
theorem s_104 : reachX [] 0 [28, 36, 54] 15062570433012334601 0 3 = false := by decide +kernel
theorem s_105 : reachX [] 0 [28, 36, 54] 15062570433012338689 0 3 = false := by decide +kernel
theorem s_106 : reachX [] 0 [28, 36, 54] 15062570435159785481 0 3 = false := by decide +kernel
theorem s_107 : reachX [] 0 [28, 36, 54] 15062570467372040201 1 3 = false := by decide +kernel
theorem s_108 : reachX [] 0 [28, 36, 54] 15063696332919144457 1 3 = false := by decide +kernel
theorem s_109 : reachX [] 0 [28, 36, 54] 15064822232825987217 1 3 = false := by decide +kernel
theorem s_110 : reachX [] 0 [28, 36, 54] 15078333031708098753 1 3 = false := by decide +kernel
theorem s_111 : reachX [] 0 [28, 36, 54] 15096347430217580675 0 3 = false := by decide +kernel
theorem s_112 : reachX [] 0 [28, 36, 54] 15096347430217580681 0 3 = false := by decide +kernel
theorem s_113 : reachX [] 0 [28, 36, 54] 15096347430217580689 1 3 = false := by decide +kernel
theorem s_114 : reachX [] 0 [28, 36, 54] 15096347430217580737 1 3 = false := by decide +kernel
theorem s_115 : reachX [] 0 [28, 36, 54] 15096347430217580929 0 3 = false := by decide +kernel
theorem s_116 : reachX [] 0 [28, 36, 54] 15096347430217613441 0 3 = false := by decide +kernel
theorem s_117 : reachX [] 0 [28, 36, 54] 15096347430217613569 0 3 = false := by decide +kernel
theorem s_118 : reachX [] 0 [28, 36, 54] 15096347432365064321 0 3 = false := by decide +kernel
theorem s_119 : reachX [] 0 [28, 36, 54] 15096347979973394561 1 3 = false := by decide +kernel
theorem s_120 : reachX [] 0 [28, 36, 54] 15100851029844951169 1 3 = false := by decide +kernel
theorem s_121 : reachX [] 0 [28, 36, 54] 15114361828727062657 1 3 = false := by decide +kernel
theorem s_122 : reachX [] 0 [28, 36, 54] 15204433821274472459 0 3 = false := by decide +kernel
theorem s_123 : reachX [] 0 [28, 36, 54] 15204433821274472515 0 3 = false := by decide +kernel
theorem s_124 : reachX [] 0 [28, 36, 54] 15204433821274472579 0 3 = false := by decide +kernel
theorem s_125 : reachX [] 0 [28, 36, 54] 15204433821274472641 0 3 = false := by decide +kernel
theorem s_126 : reachX [] 0 [28, 36, 54] 15204433821274505219 0 3 = false := by decide +kernel
theorem s_127 : reachX [] 0 [28, 36, 54] 15204433823421956099 0 3 = false := by decide +kernel
theorem s_128 : reachX [] 0 [28, 36, 54] 15204433829864407043 1 3 = false := by decide +kernel
theorem s_129 : reachX [] 0 [28, 36, 54] 15204996771227893763 1 3 = false := by decide +kernel
theorem s_130 : reachX [] 0 [28, 36, 54] 15348549009350328333 1 3 = false := by decide +kernel
theorem s_131 : reachX [] 0 [28, 36, 54] 15636779385502040075 0 3 = false := by decide +kernel
theorem s_132 : reachX [] 0 [28, 36, 54] 15636779385502040077 1 3 = false := by decide +kernel
theorem s_133 : reachX [] 0 [28, 36, 54] 15636779385502040089 0 3 = false := by decide +kernel
theorem s_134 : reachX [] 0 [28, 36, 54] 15636779385502040201 0 3 = false := by decide +kernel
theorem s_135 : reachX [] 0 [28, 36, 54] 15636779385502040209 0 3 = false := by decide +kernel
theorem s_136 : reachX [] 0 [28, 36, 54] 15636779385502072841 0 3 = false := by decide +kernel
theorem s_137 : reachX [] 0 [28, 36, 54] 15636779387649523721 0 3 = false := by decide +kernel
theorem s_138 : reachX [] 0 [28, 36, 54] 15636779419861778441 1 3 = false := by decide +kernel
theorem s_139 : reachX [] 0 [28, 36, 54] 15639031185315725321 1 3 = false := by decide +kernel
theorem s_140 : reachX [] 0 [28, 36, 54] 15925009761653751817 1 3 = false := by decide +kernel
theorem s_141 : reachX [] 0 [28, 36, 54] 17366161642412310535 0 3 = false := by decide +kernel
theorem s_142 : reachX [] 0 [28, 36, 54] 17366161642412310539 0 3 = false := by decide +kernel
theorem s_143 : reachX [] 0 [28, 36, 54] 17366161642412310541 0 3 = false := by decide +kernel
theorem s_144 : reachX [] 0 [28, 36, 54] 17366161642412310659 0 3 = false := by decide +kernel
theorem s_145 : reachX [] 0 [28, 36, 54] 17366161642412343299 0 3 = false := by decide +kernel
theorem s_146 : reachX [] 0 [28, 36, 54] 17366161644559794179 0 3 = false := by decide +kernel
theorem s_147 : reachX [] 0 [28, 36, 54] 17366161651002245123 1 3 = false := by decide +kernel
theorem s_148 : reachX [] 0 [28, 36, 54] 17366724592365731843 1 3 = false := by decide +kernel
theorem s_149 : reachX [] 0 [28, 36, 54] 17510276830488166403 1 3 = false := by decide +kernel

def tbl : List (Nat × Nat) := [(15060318633198616591, 0), (15060318633198616717, 0), (15060318633198616723, 0), (15060318633198616729, 0), (15060318633198616771, 0), (15060318633198616777, 0), (15060318633198616785, 1), (15060318633198649357, 0), (15060318633198649489, 0), (15060318633198649537, 0), (15060318633198649603, 0), (15060318633198649609, 0), (15060318633198649729, 0), (15060318633198653443, 0), (15060318633198653449, 0), (15060318633198653569, 0), (15060318633198653697, 1), (15060318633198665731, 0), (15060318633198665737, 0), (15060318633198665857, 0), (15060318633198665985, 1), (15060318633198669825, 1), (15060318635346100237, 0), (15060318635346100369, 0), (15060318635346100417, 0), (15060318635346133249, 0), (15060318635346137089, 0), (15060318635346149377, 0), (15060318635346165763, 0), (15060318635346165769, 0), (15060318635346165889, 0), (15060318635346198529, 0), (15060318635362877443, 0), (15060318635362877449, 0), (15060318635362877569, 0), (15060318635362910209, 0), (15060318635362942977, 1), (15060318635614535683, 0), (15060318635614535689, 0), (15060318635614535809, 0), (15060318635614568449, 0), (15060318635614601217, 1), (15060318635631312897, 1), (15060318636419842051, 0), (15060318636419842057, 0), (15060318636419842177, 0), (15060318636419874817, 0), (15060318636419907585, 1), (15060318636436619265, 1), (15060318636688277505, 1), (15060318641788551179, 0), (15060318641788551299, 0), (15060318641788583939, 0), (15060318642862292995, 0), (15060318643936034819, 0), (15060318645009776641, 0), (15060318650378485773, 1), (15060318667558354955, 0), (15060318667558354957, 1), (15060318667558355081, 0), (15060318667558387721, 0), (15060318667826790409, 0), (15060318669705838601, 0), (15060318669974274049, 0), (15060318684738224137, 1), (15060318701918093457, 1), (15060318908076523713, 1), (15060319182954430595, 0), (15060319182954430601, 0), (15060319182954430609, 1), (15060319182954430657, 1), (15060319182954463361, 0), (15060319182971207809, 0), (15060319185101914241, 0), (15060319185118691329, 0), (15060319251673907329, 1), (15060319457832337537, 1), (15060319732710277377, 1), (15060336225384697857, 1), (15060389001942843393, 1), (15060459370687004675, 0), (15060459370687004681, 0), (15060459370687004801, 0), (15060459370687004929, 1), (15060459370687008769, 1), (15060459370687021057, 1), (15060459370687070209, 0), (15060459372834488321, 0), (15060459372834521089, 0), (15060460470198632449, 1), (15060476962873049089, 1), (15060529739431182337, 1), (15060881583152037899, 0), (15060881583152038019, 0), (15060881583152054275, 0), (15060881583152070659, 0), (15060881583152087041, 0), (15060881585299521539, 0), (15060881591741972483, 1), (15061444533105459213, 1), (15062570433012301835, 0), (15062570433012301837, 1), (15062570433012301961, 0), (15062570433012305929, 0), (15062570433012334601, 0), (15062570433012338689, 0), (15062570435159785481, 0), (15062570467372040201, 1), (15063696332919144457, 1), (15064822232825987217, 1), (15078333031708098753, 1), (15096347430217580675, 0), (15096347430217580681, 0), (15096347430217580689, 1), (15096347430217580737, 1), (15096347430217580929, 0), (15096347430217613441, 0), (15096347430217613569, 0), (15096347432365064321, 0), (15096347979973394561, 1), (15100851029844951169, 1), (15114361828727062657, 1), (15204433821274472459, 0), (15204433821274472515, 0), (15204433821274472579, 0), (15204433821274472641, 0), (15204433821274505219, 0), (15204433823421956099, 0), (15204433829864407043, 1), (15204996771227893763, 1), (15348549009350328333, 1), (15636779385502040075, 0), (15636779385502040077, 1), (15636779385502040089, 0), (15636779385502040201, 0), (15636779385502040209, 0), (15636779385502072841, 0), (15636779387649523721, 0), (15636779419861778441, 1), (15639031185315725321, 1), (15925009761653751817, 1), (17366161642412310535, 0), (17366161642412310539, 0), (17366161642412310541, 0), (17366161642412310659, 0), (17366161642412343299, 0), (17366161644559794179, 0), (17366161651002245123, 1), (17366724592365731843, 1), (17510276830488166403, 1)]

theorem tblh : ∀ e ∈ tbl, reach [28, 36, 54] e.1 e.2 3 = false :=
  List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198616591 0 3).trans s_0, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198616717 0 3).trans s_1, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198616723 0 3).trans s_2, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198616729 0 3).trans s_3, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198616771 0 3).trans s_4, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198616777 0 3).trans s_5, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198616785 1 3).trans s_6, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198649357 0 3).trans s_7, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198649489 0 3).trans s_8, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198649537 0 3).trans s_9, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198649603 0 3).trans s_10, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198649609 0 3).trans s_11, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198649729 0 3).trans s_12, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198653443 0 3).trans s_13, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198653449 0 3).trans s_14, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198653569 0 3).trans s_15, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198653697 1 3).trans s_16, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198665731 0 3).trans s_17, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198665737 0 3).trans s_18, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198665857 0 3).trans s_19, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198665985 1 3).trans s_20, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318633198669825 1 3).trans s_21, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635346100237 0 3).trans s_22, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635346100369 0 3).trans s_23, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635346100417 0 3).trans s_24, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635346133249 0 3).trans s_25, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635346137089 0 3).trans s_26, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635346149377 0 3).trans s_27, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635346165763 0 3).trans s_28, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635346165769 0 3).trans s_29, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635346165889 0 3).trans s_30, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635346198529 0 3).trans s_31, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635362877443 0 3).trans s_32, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635362877449 0 3).trans s_33, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635362877569 0 3).trans s_34, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635362910209 0 3).trans s_35, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635362942977 1 3).trans s_36, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635614535683 0 3).trans s_37, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635614535689 0 3).trans s_38, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635614535809 0 3).trans s_39, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635614568449 0 3).trans s_40, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635614601217 1 3).trans s_41, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318635631312897 1 3).trans s_42, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318636419842051 0 3).trans s_43, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318636419842057 0 3).trans s_44, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318636419842177 0 3).trans s_45, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318636419874817 0 3).trans s_46, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318636419907585 1 3).trans s_47, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318636436619265 1 3).trans s_48, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318636688277505 1 3).trans s_49, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318641788551179 0 3).trans s_50, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318641788551299 0 3).trans s_51, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318641788583939 0 3).trans s_52, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318642862292995 0 3).trans s_53, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318643936034819 0 3).trans s_54, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318645009776641 0 3).trans s_55, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318650378485773 1 3).trans s_56, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318667558354955 0 3).trans s_57, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318667558354957 1 3).trans s_58, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318667558355081 0 3).trans s_59, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318667558387721 0 3).trans s_60, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318667826790409 0 3).trans s_61, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318669705838601 0 3).trans s_62, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318669974274049 0 3).trans s_63, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318684738224137 1 3).trans s_64, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318701918093457 1 3).trans s_65, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060318908076523713 1 3).trans s_66, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319182954430595 0 3).trans s_67, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319182954430601 0 3).trans s_68, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319182954430609 1 3).trans s_69, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319182954430657 1 3).trans s_70, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319182954463361 0 3).trans s_71, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319182971207809 0 3).trans s_72, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319185101914241 0 3).trans s_73, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319185118691329 0 3).trans s_74, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319251673907329 1 3).trans s_75, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319457832337537 1 3).trans s_76, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060319732710277377 1 3).trans s_77, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060336225384697857 1 3).trans s_78, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060389001942843393 1 3).trans s_79, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060459370687004675 0 3).trans s_80, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060459370687004681 0 3).trans s_81, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060459370687004801 0 3).trans s_82, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060459370687004929 1 3).trans s_83, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060459370687008769 1 3).trans s_84, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060459370687021057 1 3).trans s_85, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060459370687070209 0 3).trans s_86, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060459372834488321 0 3).trans s_87, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060459372834521089 0 3).trans s_88, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060460470198632449 1 3).trans s_89, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060476962873049089 1 3).trans s_90, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060529739431182337 1 3).trans s_91, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060881583152037899 0 3).trans s_92, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060881583152038019 0 3).trans s_93, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060881583152054275 0 3).trans s_94, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060881583152070659 0 3).trans s_95, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060881583152087041 0 3).trans s_96, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060881585299521539 0 3).trans s_97, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15060881591741972483 1 3).trans s_98, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15061444533105459213 1 3).trans s_99, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15062570433012301835 0 3).trans s_100, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15062570433012301837 1 3).trans s_101, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15062570433012301961 0 3).trans s_102, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15062570433012305929 0 3).trans s_103, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15062570433012334601 0 3).trans s_104, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15062570433012338689 0 3).trans s_105, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15062570435159785481 0 3).trans s_106, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15062570467372040201 1 3).trans s_107, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15063696332919144457 1 3).trans s_108, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15064822232825987217 1 3).trans s_109, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15078333031708098753 1 3).trans s_110, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15096347430217580675 0 3).trans s_111, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15096347430217580681 0 3).trans s_112, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15096347430217580689 1 3).trans s_113, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15096347430217580737 1 3).trans s_114, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15096347430217580929 0 3).trans s_115, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15096347430217613441 0 3).trans s_116, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15096347430217613569 0 3).trans s_117, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15096347432365064321 0 3).trans s_118, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15096347979973394561 1 3).trans s_119, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15100851029844951169 1 3).trans s_120, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15114361828727062657 1 3).trans s_121, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15204433821274472459 0 3).trans s_122, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15204433821274472515 0 3).trans s_123, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15204433821274472579 0 3).trans s_124, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15204433821274472641 0 3).trans s_125, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15204433821274505219 0 3).trans s_126, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15204433823421956099 0 3).trans s_127, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15204433829864407043 1 3).trans s_128, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15204996771227893763 1 3).trans s_129, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15348549009350328333 1 3).trans s_130, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15636779385502040075 0 3).trans s_131, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15636779385502040077 1 3).trans s_132, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15636779385502040089 0 3).trans s_133, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15636779385502040201 0 3).trans s_134, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15636779385502040209 0 3).trans s_135, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15636779385502072841 0 3).trans s_136, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15636779387649523721 0 3).trans s_137, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15636779419861778441 1 3).trans s_138, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15639031185315725321 1 3).trans s_139, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 15925009761653751817 1 3).trans s_140, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 17366161642412310535 0 3).trans s_141, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 17366161642412310539 0 3).trans s_142, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 17366161642412310541 0 3).trans s_143, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 17366161642412310659 0 3).trans s_144, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 17366161642412343299 0 3).trans s_145, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 17366161644559794179 0 3).trans s_146, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 17366161651002245123 1 3).trans s_147, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 17366724592365731843 1 3).trans s_148, List.forall_mem_cons.2 ⟨(rx0 [28, 36, 54] 17510276830488166403 1 3).trans s_149, (by intro e h; cases h)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem searchX : reachX tbl 3 [28, 36, 54] 15060318633198616577 2 6 = false := by decide +kernel

theorem search : reach [28, 36, 54] 15060318633198616577 2 6 = false := by
  rw [← reachX_eq tbl 3 [28, 36, 54] tblh]; exact searchX

end PEqualNP.Outside.L_meta_50858_aux

open PEqualNP.Outside.L_meta_50858_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_50858 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (28 : Nat).testBit t.val ∧
    w.getD q.val false = (36 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val) := by
  rintro ⟨⟨gs, o⟩, p, q, r, hF, hR, hN, hS, hT⟩
  have hF' : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hF g hg
    exact ⟨by simpa using h1, h2⟩
  have hW : ∀ t : Fin 6, Circuit.wires ⟨gs, o⟩ ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])
      = (vw gs [62, 60, 56, 48, 32, 0, 63]).map (fun x => x.testBit t.val) := by
    intro t
    rw [inp t]
    exact fold_eq t.val t.isLt gs _ (fun g hg => (hF' g hg).1)
  have hlt : ∀ x ∈ vw gs [62, 60, 56, 48, 32, 0, 63], x < 64 := vw_lt gs _ (by decide)
  have hlen : (vw gs [62, 60, 56, 48, 32, 0, 63]).length = 7 + gs.length := by rw [vw_len]; rfl
  have tap : ∀ (s : Fin (7 + gs.length)) (a : Nat), a < 64 →
      (∀ t : Fin 6, (Circuit.wires ⟨gs, o⟩ ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD s.val false = a.testBit t.val) →
      a ∈ vw gs [62, 60, 56, 48, 32, 0, 63] := by
    intro s a ha h
    have hs : s.val < (vw gs [62, 60, 56, 48, 32, 0, 63]).length := by rw [hlen]; exact s.isLt
    have he : (vw gs [62, 60, 56, 48, 32, 0, 63])[s.val] = a := by
      apply k6 _ (hlt _ (List.getElem_mem hs)) a ha
      intro t ht
      have h1 := h ⟨t, ht⟩
      rw [hW, getD_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs] at h1
      exact h1
    rw [← he]
    exact List.getElem_mem hs
  have hp := tap p 28 (by decide) (fun t => by have h := hT t; simp only at h; exact h.1)
  have hq := tap q 36 (by decide) (fun t => by have h := hT t; simp only at h; exact h.2.1)
  have hr := tap r 54 (by decide) (fun t => by have h := hT t; simp only at h; exact h.2.2)
  have hm0 : ∀ x ∈ [62, 60, 56, 48, 32, 0, 63], x < 64 ∧ (15060318633198616577 : Nat).testBit x = true := by decide
  have h := sound [28, 36, 54] gs [62, 60, 56, 48, 32, 0, 63] 15060318633198616577 2 6 hF' (rb_of gs 7 o hR) hm0 hN hS
    (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact hp
      · exact hq
      · exact hr)
  rw [search] at h
  exact absurd h (by decide)
