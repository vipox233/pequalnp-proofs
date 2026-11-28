import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50406_aux

open PEqualNP.CircuitLowerBounds

local instance gdec : DecidableEq GateOp := lineDegreeGateOpDecEq

def tA : ℕ := 4
def tB : ℕ := 36
def tC : ℕ := 46

def gv (g : Gate) (cs : List ℕ) : ℕ :=
  match g.op, g.inputs with
  | .and, l => l.foldr (fun i acc => cs.getD i 0 &&& acc) 63
  | .or, l => l.foldr (fun i acc => cs.getD i 0 ||| acc) 0
  | .not, [] => 63
  | .not, i :: _ => 63 ^^^ cs.getD i 0
  | _, _ => 0

def colsF (gs : List Gate) (cs : List ℕ) : List ℕ :=
  gs.foldl (fun acc g => acc ++ [gv g acc]) cs

def okOp (g : Gate) : Prop := g.op = .and ∨ g.op = .or ∨ g.op = .not

def nots (gs : List Gate) : ℕ := (gs.filter fun g : Gate => decide (g.op = GateOp.not)).length

def RB : ℕ → List Gate → Prop
  | _, [] => True
  | L, g :: gs => (∀ i ∈ g.inputs, i < L) ∧ RB (L + 1) gs

def tgt (cs : List ℕ) : Bool := cs.contains tA && cs.contains tB && cs.contains tC

def m1 (cs : List ℕ) (x : ℕ) : ℕ := if x ∈ cs then 0 else 1

def miss (cs : List ℕ) : ℕ := m1 cs tA + m1 cs tB + m1 cs tC

def orAll (f : ℕ → ℕ) (init : ℕ) (l : List ℕ) : ℕ := l.foldl (fun acc x => acc ||| f x) init

def bit (v : ℕ) : ℕ := 1 <<< v

def rm (cs : List ℕ) : ℕ :=
  orAll (fun a => orAll (fun b => bit (a &&& (b &&& 63)) ||| bit (a ||| (b ||| 0))) 0 cs)
    (bit 63 ||| bit 0 ||| orAll (fun a => bit (a &&& 63) ||| bit (a ||| 0)) 0 cs) cs

def rn (cs : List ℕ) : ℕ := orAll (fun a => bit (63 ^^^ a)) (bit 63) cs

def srch : ℕ → ℕ → List ℕ → Bool
  | 0, _, cs => tgt cs
  | k + 1, n, cs => tgt cs || (decide (miss cs ≤ k + 1) && (List.range 64).any (fun v =>
      ((rm cs).testBit v && srch k n (cs ++ [v])) ||
      (decide (0 < n) && (rn cs).testBit v && srch k (n - 1) (cs ++ [v]))))

theorem orAll_bit (f : ℕ → ℕ) (l : List ℕ) : ∀ (init v : ℕ),
    (orAll f init l).testBit v = (init.testBit v || l.any fun x => (f x).testBit v) := by
  induction l with
  | nil => intro init v; simp [orAll]
  | cons x l ih =>
    intro init v
    simp only [orAll, List.foldl_cons] at *
    rw [ih]; simp [Nat.testBit_or, Bool.or_assoc]

theorem bit_self (v : ℕ) : (bit v).testBit v = true := by
  simp [bit, Nat.testBit_shiftLeft]

theorem srch_miss : ∀ k n cs, srch k n cs = true → miss cs ≤ k := by
  intro k
  induction k with
  | zero =>
    intro n cs h
    simp only [srch, tgt, Bool.and_eq_true, List.contains_iff_mem] at h
    simp [miss, m1, h.1.1, h.1.2, h.2]
  | succ k ih =>
    intro n cs h
    simp only [srch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · simp only [tgt, Bool.and_eq_true, List.contains_iff_mem] at h
      simp [miss, m1, h.1.1, h.1.2, h.2]
    · exact h.1

theorem m1_le (cs : List ℕ) (v x : ℕ) : m1 (cs ++ [v]) x ≤ m1 cs x := by
  unfold m1; split_ifs <;> simp_all

theorem m1_ne (cs : List ℕ) (v x : ℕ) (h : x ≠ v) : m1 (cs ++ [v]) x = m1 cs x := by
  unfold m1; simp [List.mem_append, h]

theorem m1_le1 (cs : List ℕ) (x : ℕ) : m1 cs x ≤ 1 := by
  unfold m1; split_ifs <;> omega

theorem miss_step (hab : tA ≠ tB) (hac : tA ≠ tC) (hbc : tB ≠ tC) (cs : List ℕ) (v : ℕ) :
    miss cs ≤ miss (cs ++ [v]) + 1 := by
  unfold miss
  have hA := m1_le1 cs tA
  have hB := m1_le1 cs tB
  have hC := m1_le1 cs tC
  by_cases ha : tA = v
  · have hb : tB ≠ v := fun h => hab (ha.trans h.symm)
    have hc : tC ≠ v := fun h => hac (ha.trans h.symm)
    rw [m1_ne _ _ _ hb, m1_ne _ _ _ hc]; omega
  · by_cases hb : tB = v
    · have hc : tC ≠ v := fun h => hbc (hb.trans h.symm)
      rw [m1_ne _ _ _ ha, m1_ne _ _ _ hc]; omega
    · by_cases hc : tC = v
      · rw [m1_ne _ _ _ ha, m1_ne _ _ _ hb]; omega
      · rw [m1_ne _ _ _ ha, m1_ne _ _ _ hb, m1_ne _ _ _ hc]; omega

theorem lt_and (a b : ℕ) (hb : b < 64) : a &&& b < 64 :=
  lt_of_le_of_lt Nat.and_le_right hb

theorem lt_or (a b : ℕ) (ha : a < 64) (hb : b < 64) : a ||| b < 64 := by
  have := Nat.or_lt_two_pow (n := 6) ha hb; simpa using this

theorem lt_xor (a : ℕ) (ha : a < 64) : 63 ^^^ a < 64 := by
  have := Nat.xor_lt_two_pow (n := 6) (by norm_num : 63 < 2 ^ 6) ha; simpa using this

theorem getD_lt (cs : List ℕ) (h : ∀ x ∈ cs, x < 64) (i : ℕ) : cs.getD i 0 < 64 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : cs[i]? with
  | none => simp
  | some x => simpa using h x (List.mem_of_getElem? hi)

theorem foldr_and_lt (cs : List ℕ) : ∀ l : List ℕ, l.foldr (fun i acc => cs.getD i 0 &&& acc) 63 < 64 := by
  intro l
  induction l with
  | nil => show (63 : ℕ) < 64; norm_num
  | cons i l ih => simp only [List.foldr_cons]; exact lt_and _ _ ih

theorem foldr_or_lt (cs : List ℕ) (h : ∀ x ∈ cs, x < 64) :
    ∀ l : List ℕ, l.foldr (fun i acc => cs.getD i 0 ||| acc) 0 < 64 := by
  intro l
  induction l with
  | nil => show (0 : ℕ) < 64; norm_num
  | cons i l ih => simp only [List.foldr_cons]; exact lt_or _ _ (getD_lt cs h i) ih

theorem gv_lt (g : Gate) (cs : List ℕ) (h : ∀ x ∈ cs, x < 64) : gv g cs < 64 := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and => exact foldr_and_lt cs l
  | or => exact foldr_or_lt cs h l
  | not =>
    cases l with
    | nil => show (63 : ℕ) < 64; norm_num
    | cons i _ => exact lt_xor _ (getD_lt cs h i)
  | mod m => show (0 : ℕ) < 64; norm_num
  | maj => show (0 : ℕ) < 64; norm_num

theorem getD_mem (cs : List ℕ) (i : ℕ) (hi : i < cs.length) : cs.getD i 0 ∈ cs := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem any_mem {l : List ℕ} {x : ℕ} (hx : x ∈ l) (p : ℕ → Bool) (h : p x = true) :
    l.any p = true := List.any_eq_true.mpr ⟨x, hx, h⟩

theorem orAll_ge (f : ℕ → ℕ) (init : ℕ) (l : List ℕ) (v : ℕ) (h : init.testBit v = true) :
    (orAll f init l).testBit v = true := by
  rw [orAll_bit, h, Bool.true_or]

theorem orAll_mem (f : ℕ → ℕ) (init : ℕ) (l : List ℕ) (v x : ℕ) (hx : x ∈ l) (h : (f x).testBit v = true) :
    (orAll f init l).testBit v = true := by
  rw [orAll_bit, any_mem hx _ h, Bool.or_true]

theorem or_l (x y v : ℕ) (h : x.testBit v = true) : (x ||| y).testBit v = true := by
  rw [Nat.testBit_or, h, Bool.true_or]

theorem or_r (x y v : ℕ) (h : y.testBit v = true) : (x ||| y).testBit v = true := by
  rw [Nat.testBit_or, h, Bool.or_true]

theorem rm_31 (cs : List ℕ) : (rm cs).testBit 63 = true :=
  orAll_ge _ _ _ _ (or_l _ _ _ (or_l _ _ _ (bit_self 63)))

theorem rm_0 (cs : List ℕ) : (rm cs).testBit 0 = true :=
  orAll_ge _ _ _ _ (or_l _ _ _ (or_r _ _ _ (bit_self 0)))

theorem rm_and1 (cs : List ℕ) (a : ℕ) (ha : a ∈ cs) : (rm cs).testBit (a &&& 63) = true :=
  orAll_ge _ _ _ _ (or_r _ _ _ (orAll_mem _ _ _ _ a ha (or_l _ _ _ (bit_self _))))

theorem rm_or1 (cs : List ℕ) (a : ℕ) (ha : a ∈ cs) : (rm cs).testBit (a ||| 0) = true :=
  orAll_ge _ _ _ _ (or_r _ _ _ (orAll_mem _ _ _ _ a ha (or_r _ _ _ (bit_self _))))

theorem rm_and2 (cs : List ℕ) (a b : ℕ) (ha : a ∈ cs) (hb : b ∈ cs) :
    (rm cs).testBit (a &&& (b &&& 63)) = true :=
  orAll_mem _ _ _ _ a ha (orAll_mem _ _ _ _ b hb (or_l _ _ _ (bit_self _)))

theorem rm_or2 (cs : List ℕ) (a b : ℕ) (ha : a ∈ cs) (hb : b ∈ cs) :
    (rm cs).testBit (a ||| (b ||| 0)) = true :=
  orAll_mem _ _ _ _ a ha (orAll_mem _ _ _ _ b hb (or_r _ _ _ (bit_self _)))

theorem rn_31 (cs : List ℕ) : (rn cs).testBit 63 = true := orAll_ge _ _ _ _ (bit_self 63)

theorem rn_x (cs : List ℕ) (a : ℕ) (ha : a ∈ cs) : (rn cs).testBit (63 ^^^ a) = true :=
  orAll_mem _ _ _ _ a ha (bit_self _)

theorem gv_reach (g : Gate) (cs : List ℕ) (hop : okOp g) (hl : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < cs.length) :
    (g.op ≠ .not → (rm cs).testBit (gv g cs) = true) ∧
    (g.op = .not → (rn cs).testBit (gv g cs) = true) := by
  obtain ⟨op, l⟩ := g
  simp only [okOp] at hop
  simp only at hl hin ⊢
  have hm : ∀ i ∈ l, cs.getD i 0 ∈ cs := fun i hi => getD_mem cs i (hin i hi)
  rcases hop with rfl | rfl | rfl
  · refine ⟨fun _ => ?_, fun h => by cases h⟩
    rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · exact rm_31 cs
    · exact rm_and1 cs _ (hm i (by simp))
    · exact rm_and2 cs _ _ (hm i (by simp)) (hm j (by simp))
    · simp at hl
  · refine ⟨fun _ => ?_, fun h => by cases h⟩
    rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · exact rm_0 cs
    · exact rm_or1 cs _ (hm i (by simp))
    · exact rm_or2 cs _ _ (hm i (by simp)) (hm j (by simp))
    · simp at hl
  · refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
    rcases l with _ | ⟨i, l⟩
    · exact rn_31 cs
    · exact rn_x cs _ (hm i (by simp))

theorem colsF_cons (g : Gate) (gs : List Gate) (cs : List ℕ) :
    colsF (g :: gs) cs = colsF gs (cs ++ [gv g cs]) := rfl

theorem colsF_lt : ∀ (gs : List Gate) (cs : List ℕ), (∀ x ∈ cs, x < 64) → ∀ x ∈ colsF gs cs, x < 64 := by
  intro gs
  induction gs with
  | nil => intro cs h; exact h
  | cons g gs ih =>
    intro cs h
    rw [colsF_cons]
    apply ih
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h x hx
    · exact gv_lt g cs h

theorem colsF_length : ∀ (gs : List Gate) (cs : List ℕ), (colsF gs cs).length = cs.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro cs; simp [colsF]
  | cons g gs ih => intro cs; rw [colsF_cons, ih]; simp; omega

theorem comp (hab : tA ≠ tB) (hac : tA ≠ tC) (hbc : tB ≠ tC) : ∀ (gs : List Gate) (cs : List ℕ) (n : ℕ),
    (∀ x ∈ cs, x < 64) → (∀ g ∈ gs, okOp g ∧ g.inputs.length ≤ 2) → RB cs.length gs → nots gs ≤ n →
    tgt (colsF gs cs) = true → srch gs.length n cs = true := by
  intro gs
  induction gs with
  | nil => intro cs n _ _ _ _ h; simpa [srch, colsF] using h
  | cons g gs ih =>
    intro cs n hlt hok hrb hn ht
    obtain ⟨hop, hl⟩ := hok g (by simp)
    obtain ⟨hin, hrb'⟩ := hrb
    have hv := gv_lt g cs hlt
    have hlt' : ∀ x ∈ cs ++ [gv g cs], x < 64 := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hlt x hx
      · exact hv
    have hok' : ∀ g ∈ gs, okOp g ∧ g.inputs.length ≤ 2 := fun g' hg' => hok g' (by simp [hg'])
    have hrb2 : RB (cs ++ [gv g cs]).length gs := by simpa using hrb'
    rw [colsF_cons] at ht
    have hre := gv_reach g cs hop hl hin
    simp only [List.length_cons, srch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true, List.mem_range]
    by_cases hnot : g.op = .not
    · have hn' : nots gs ≤ n - 1 := by
        simp [nots, List.filter_cons, hnot] at hn; unfold nots; omega
      have hpos : 0 < n := by simp [nots, List.filter_cons, hnot] at hn; omega
      have hs := ih _ (n - 1) hlt' hok' hrb2 hn' ht
      have hm := srch_miss _ _ _ hs
      have hm2 := miss_step hab hac hbc cs (gv g cs)
      right
      refine ⟨by omega, gv g cs, hv, Or.inr ⟨⟨by simpa using hpos, hre.2 hnot⟩, hs⟩⟩
    · have hn' : nots gs ≤ n := by
        simp [nots, List.filter_cons, hnot] at hn; unfold nots; omega
      have hs := ih _ n hlt' hok' hrb2 hn' ht
      have hm := srch_miss _ _ _ hs
      have hm2 := miss_step hab hac hbc cs (gv g cs)
      right
      exact ⟨by omega, gv g cs, hv, Or.inl ⟨hre.1 hnot, hs⟩⟩

def bridgeB (w : List Bool) (cs : List ℕ) (t : ℕ) : Prop :=
  w.length = cs.length ∧ ∀ k, w.getD k false = (cs.getD k 0).testBit t

theorem bit31 (t : ℕ) (ht : t < 6) : (63 : ℕ).testBit t = true := by
  interval_cases t <;> decide

theorem gv_bit (g : Gate) (w : List Bool) (cs : List ℕ) (t : ℕ) (ht : t < 6) (hop : okOp g)
    (hw : ∀ k, w.getD k false = (cs.getD k 0).testBit t) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = (gv g cs).testBit t := by
  obtain ⟨op, l⟩ := g
  simp only [okOp] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [GateOp.eval, gv]
    induction l with
    | nil => simp [bit31 t ht]
    | cons i l ih =>
      simp only [List.map_cons, List.all_cons, List.foldr_cons, Nat.testBit_and, id_eq]
      rw [hw i, ih]
  · simp only [GateOp.eval, gv]
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.any_cons, List.foldr_cons, Nat.testBit_or, id_eq]
      rw [hw i, ih]
  · cases l with
    | nil => simp [GateOp.eval, gv, bit31 t ht]
    | cons i l =>
      simp only [GateOp.eval, gv, List.map_cons, List.headD_cons, Nat.testBit_xor, bit31 t ht]
      rw [hw i]
      cases (cs.getD i 0).testBit t <;> rfl

theorem getD_snoc_b (w : List Bool) (b : Bool) (k : ℕ) :
    (w ++ [b]).getD k false = if k < w.length then w.getD k false else if k = w.length then b else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : k - w.length ≠ 0 := by omega
    rw [List.getElem?_eq_none (by simp; omega)]; simp [List.getElem?_eq_none (by omega : w.length ≤ k)]

theorem getD_snoc_n (cs : List ℕ) (v : ℕ) (k : ℕ) :
    (cs ++ [v]).getD k 0 = if k < cs.length then cs.getD k 0 else if k = cs.length then v else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp [List.getElem?_eq_none (by omega : cs.length ≤ k)]

theorem wires_bit (t : ℕ) (ht : t < 6) : ∀ (gs : List Gate) (w : List Bool) (cs : List ℕ),
    (∀ g ∈ gs, okOp g) → bridgeB w cs t →
    bridgeB (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) (colsF gs cs) t := by
  intro gs
  induction gs with
  | nil => intro w cs _ h; simpa [colsF] using h
  | cons g gs ih =>
    intro w cs hok h
    rw [List.foldl_cons, colsF_cons]
    apply ih _ _ (fun g' hg' => hok g' (by simp [hg']))
    obtain ⟨hlen, hw⟩ := h
    refine ⟨by simp [hlen], fun k => ?_⟩
    rw [getD_snoc_b, getD_snoc_n, hlen]
    split_ifs
    · exact hw k
    · exact gv_bit g w cs t ht (hok g (by simp)) hw
    · simp

def inCols : List ℕ := [62, 60, 56, 48, 32, 0, 63]

theorem in_bridge (t : Fin 6) :
    bridgeB ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]) inCols t.val := by
  refine ⟨by simp [inCols], fun k => ?_⟩
  by_cases hk : k < 7
  · fin_cases t <;> interval_cases k <;> decide
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp [inCols]; omega)]
    simp

theorem eq_of_bits (x y : ℕ) (hx : x < 64) (hy : y < 64) (h : ∀ t : Fin 6, x.testBit t.val = y.testBit t.val) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact h ⟨i, hi⟩
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (by
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (by
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem rb_of (gs : List Gate) : ∀ L, (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < L + j) → RB L gs := by
  induction gs with
  | nil => intro L _; trivial
  | cons g gs ih =>
    intro L h
    refine ⟨fun i hi => by simpa using h 0 (by simp) i (by simpa using hi), ih (L + 1) ?_⟩
    intro j hj i hi
    have := h (j + 1) (by simp; omega) i (by simpa using hi)
    omega

theorem none_small : ∀ L ≤ 5, srch L 2 inCols = false := by decide +kernel

end PEqualNP.Outside.L_meta_50406_aux

open PEqualNP.Outside.L_meta_50406_aux in
theorem PEqualNP.Outside.L_meta_50406 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (36 : Nat).testBit t.val ∧
    w.getD r.val false = (46 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, hrb, hnot, hsize, hw⟩
  have hok : ∀ g ∈ D.gates, okOp g ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    simpa [okOp, or_assoc] using h1
  have hRB : RB inCols.length D.gates := by
    apply rb_of
    intro j hj i hi
    exact hrb j hj i hi
  have hlt0 : ∀ x ∈ inCols, x < 64 := by decide
  have hcl := colsF_lt D.gates inCols hlt0
  have hlen := colsF_length D.gates inCols
  have hbr : ∀ t : Fin 6, bridgeB (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]))
      (colsF D.gates inCols) t.val := fun t =>
    wires_bit t.val t.isLt D.gates _ inCols (fun g hg => (hok g hg).1) (in_bridge t)
  have hmem : ∀ (o : Fin (7 + D.size)) (m : ℕ), m < 64 →
      (∀ t : Fin 6, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD o.val false
        = m.testBit t.val) → (colsF D.gates inCols).contains m = true := by
    intro o m hm ho
    have hoL : o.val < (colsF D.gates inCols).length := by
      rw [hlen]; exact o.isLt
    have hx := getD_mem _ _ hoL
    have heq : (colsF D.gates inCols).getD o.val 0 = m := by
      apply eq_of_bits _ _ (hcl _ hx) hm
      intro t
      rw [← (hbr t).2 o.val, ho t]
    rw [heq] at hx
    simpa using hx
  have ht : tgt (colsF D.gates inCols) = true := by
    simp only [tgt, Bool.and_eq_true]
    refine ⟨⟨hmem p tA (by decide) (fun t => (hw t).1), hmem q tB (by decide) (fun t => (hw t).2.1)⟩,
      hmem r tC (by decide) (fun t => (hw t).2.2)⟩
  have hn : nots D.gates ≤ 2 := hnot
  have hs := comp (by decide) (by decide) (by decide) D.gates inCols 2 hlt0 hok hRB hn ht
  have hL : D.gates.length ≤ 5 := hsize
  rw [none_small _ hL] at hs
  exact Bool.false_ne_true hs
