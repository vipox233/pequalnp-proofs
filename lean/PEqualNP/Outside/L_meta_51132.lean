import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

-- The search over lists of reachable values (new values only: kids, nkids) follows the proof of L-meta-50101 by ptrdsh (pull request 54414).
namespace PEqualNP.Outside.L_meta_51132_aux

open PEqualNP.CircuitLowerBounds

local instance gdec : DecidableEq GateOp := lineDegreeGateOpDecEq

def tA : ℕ := 2
def tB : ℕ := 43
def tC : ℕ := 50

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

def kids (L : List ℕ) : List ℕ :=
  ((L.flatMap fun x => L.flatMap fun y => [x &&& y, x ||| y]).filter fun v => !L.contains v).dedup

def nkids (L : List ℕ) : List ℕ :=
  ((L.map fun x => 63 ^^^ x).filter fun v => !L.contains v).dedup

def reachM (L : List ℕ) (t : ℕ) : Bool := L.any fun x => L.any fun y => x &&& y == t || x ||| y == t

def reachN (L : List ℕ) (t : ℕ) : Bool := L.any fun x => 63 ^^^ x == t

def srch : ℕ → ℕ → List ℕ → Bool
  | 0, _, L => tgt L
  | k + 1, n, L => tgt L || (decide (miss L ≤ k + 1) &&
      (if miss L = k + 1 then
        [tA, tB, tC].any (fun t => !L.contains t &&
          ((reachM L t && srch k n (t :: L)) ||
            (decide (0 < n) && reachN L t && srch k (n - 1) (t :: L))))
      else
        ((kids L).any (fun v => srch k n (v :: L)) ||
          (decide (0 < n) && (nkids L).any (fun v => srch k (n - 1) (v :: L))))))

theorem srch_miss : ∀ k n L, srch k n L = true → miss L ≤ k := by
  intro k
  induction k with
  | zero =>
    intro n L h
    simp only [srch, tgt, Bool.and_eq_true, List.contains_iff_mem] at h
    simp [miss, m1, h.1.1, h.1.2, h.2]
  | succ k ih =>
    intro n L h
    simp only [srch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · simp only [tgt, Bool.and_eq_true, List.contains_iff_mem] at h
      simp [miss, m1, h.1.1, h.1.2, h.2]
    · exact h.1

theorem m1_ne (L : List ℕ) (v x : ℕ) (h : x ≠ v) : m1 (v :: L) x = m1 L x := by
  unfold m1; simp [List.mem_cons, h]

theorem m1_le1 (L : List ℕ) (x : ℕ) : m1 L x ≤ 1 := by
  unfold m1; split_ifs <;> omega

theorem miss_step (hab : tA ≠ tB) (hac : tA ≠ tC) (hbc : tB ≠ tC) (L : List ℕ) (v : ℕ) :
    miss L ≤ miss (v :: L) + 1 := by
  unfold miss
  have hA := m1_le1 L tA
  have hB := m1_le1 L tB
  have hC := m1_le1 L tC
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

theorem tgt_mono {cs L : List ℕ} (h : ∀ x ∈ cs, x ∈ L) (ht : tgt cs = true) : tgt L = true := by
  simp only [tgt, Bool.and_eq_true, List.contains_iff_mem] at ht ⊢
  exact ⟨⟨h _ ht.1.1, h _ ht.1.2⟩, h _ ht.2⟩

theorem srch_tgt {k n : ℕ} {L : List ℕ} (h : tgt L = true) : srch k n L = true := by
  cases k <;> simp [srch, h]

theorem mem_kids {L : List ℕ} {x y m : ℕ} (hx : x ∈ L) (hy : y ∈ L)
    (hm : m = x &&& y ∨ m = x ||| y) (hin : m ∉ L) : m ∈ kids L := by
  unfold kids
  rw [List.mem_dedup, List.mem_filter]
  refine ⟨List.mem_flatMap.2 ⟨x, hx, List.mem_flatMap.2 ⟨y, hy, ?_⟩⟩, by simpa using hin⟩
  simpa using hm

theorem mem_nkids {L : List ℕ} {x m : ℕ} (hx : x ∈ L) (hm : m = 63 ^^^ x) (hin : m ∉ L) : m ∈ nkids L := by
  subst hm
  unfold nkids
  rw [List.mem_dedup, List.mem_filter]
  exact ⟨List.mem_map.2 ⟨x, hx, rfl⟩, by simpa using hin⟩

theorem reachM_of {L : List ℕ} {x y t : ℕ} (hx : x ∈ L) (hy : y ∈ L)
    (h : t = x &&& y ∨ t = x ||| y) : reachM L t = true := by
  unfold reachM
  simp only [List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
  exact ⟨x, hx, y, hy, h.imp Eq.symm Eq.symm⟩

theorem reachN_of {L : List ℕ} {x t : ℕ} (hx : x ∈ L) (h : t = 63 ^^^ x) : reachN L t = true := by
  unfold reachN
  simp only [List.any_eq_true, beq_iff_eq]
  exact ⟨x, hx, h.symm⟩

theorem tight_target {L : List ℕ} {v : ℕ} (h : miss (v :: L) < miss L) : v = tA ∨ v = tB ∨ v = tC := by
  by_contra hc
  push_neg at hc
  obtain ⟨ha, hb, hc⟩ := hc
  unfold miss at h
  rw [m1_ne _ _ _ (Ne.symm ha), m1_ne _ _ _ (Ne.symm hb), m1_ne _ _ _ (Ne.symm hc)] at h
  omega

theorem srch_tight {k n : ℕ} {L : List ℕ} (h1 : miss L = k + 1) (t : ℕ) (ht : t = tA ∨ t = tB ∨ t = tC)
    (hn : t ∉ L)
    (h : (reachM L t = true ∧ srch k n (t :: L) = true) ∨
      (0 < n ∧ reachN L t = true ∧ srch k (n - 1) (t :: L) = true)) : srch (k + 1) n L = true := by
  have hc : L.contains t = false := by simpa using hn
  unfold srch
  simp only [h1, le_refl, decide_true, Bool.true_and, ↓reduceIte, Bool.or_eq_true, List.any_eq_true]
  right
  refine ⟨t, by rcases ht with rfl | rfl | rfl <;> simp, ?_⟩
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  exact ⟨hc, h.imp (fun a => a) (fun a => ⟨⟨a.1, a.2.1⟩, a.2.2⟩)⟩

theorem srch_loose {k n : ℕ} {L : List ℕ} (h0 : miss L ≤ k + 1) (h1 : miss L ≠ k + 1)
    (h : (∃ v ∈ kids L, srch k n (v :: L) = true) ∨
      (0 < n ∧ ∃ v ∈ nkids L, srch k (n - 1) (v :: L) = true)) : srch (k + 1) n L = true := by
  unfold srch
  simp only [h1, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  right
  exact ⟨h0, h⟩

theorem and31 : ∀ a < 64, a &&& 63 = a := by decide

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

theorem gv_reach (g : Gate) (cs L : List ℕ) (hop : okOp g) (hl : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < cs.length) (hlt : ∀ x ∈ cs, x < 64) (hsub : ∀ x ∈ cs, x ∈ L)
    (h31 : 63 ∈ L) (h0 : 0 ∈ L) :
    gv g cs ∈ L ∨ (g.op ≠ .not ∧ ∃ x ∈ L, ∃ y ∈ L, gv g cs = x &&& y ∨ gv g cs = x ||| y) ∨
      (g.op = .not ∧ ∃ x ∈ L, gv g cs = 63 ^^^ x) := by
  obtain ⟨op, l⟩ := g
  simp only [okOp] at hop
  simp only at hl hin ⊢
  have hm : ∀ i ∈ l, cs.getD i 0 ∈ cs := fun i hi => getD_mem cs i (hin i hi)
  rcases hop with rfl | rfl | rfl
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · exact Or.inl h31
    · have hi := hm i (by simp)
      left
      show cs.getD i 0 &&& 63 ∈ L
      rw [and31 _ (hlt _ hi)]; exact hsub _ hi
    · have hi := hm i (by simp)
      have hj := hm j (by simp)
      have e : gv ⟨.and, [i, j]⟩ cs = cs.getD i 0 &&& cs.getD j 0 := by
        show cs.getD i 0 &&& (cs.getD j 0 &&& 63) = _
        rw [and31 _ (hlt _ hj)]
      exact Or.inr (Or.inl ⟨(by intro h; cases h), _, hsub _ hi, _, hsub _ hj, Or.inl e⟩)
    · simp at hl
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · exact Or.inl h0
    · have hi := hm i (by simp)
      left
      show cs.getD i 0 ||| 0 ∈ L
      rw [Nat.or_zero]; exact hsub _ hi
    · have hi := hm i (by simp)
      have hj := hm j (by simp)
      have e : gv ⟨.or, [i, j]⟩ cs = cs.getD i 0 ||| cs.getD j 0 := by
        show cs.getD i 0 ||| (cs.getD j 0 ||| 0) = _
        rw [Nat.or_zero]
      exact Or.inr (Or.inl ⟨(by intro h; cases h), _, hsub _ hi, _, hsub _ hj, Or.inr e⟩)
    · simp at hl
  · rcases l with _ | ⟨i, l⟩
    · exact Or.inl h31
    · have hi := hm i (by simp)
      exact Or.inr (Or.inr ⟨rfl, _, hsub _ hi, rfl⟩)

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

theorem nots_cons_not (g : Gate) (gs : List Gate) (h : g.op = .not) : nots (g :: gs) = nots gs + 1 := by
  simp [nots, List.filter_cons, h]

theorem nots_cons_other (g : Gate) (gs : List Gate) (h : g.op ≠ .not) : nots (g :: gs) = nots gs := by
  simp [nots, List.filter_cons, h]

theorem comp (hab : tA ≠ tB) (hac : tA ≠ tC) (hbc : tB ≠ tC) : ∀ (gs : List Gate) (cs L : List ℕ) (k n : ℕ),
    (∀ x ∈ cs, x < 64) → (∀ x ∈ cs, x ∈ L) → 63 ∈ L → 0 ∈ L →
    (∀ g ∈ gs, okOp g ∧ g.inputs.length ≤ 2) → RB cs.length gs → gs.length ≤ k → nots gs ≤ n →
    tgt (colsF gs cs) = true → srch k n L = true := by
  intro gs
  induction gs with
  | nil =>
    intro cs L k n _ hsub _ _ _ _ _ _ ht
    exact srch_tgt (tgt_mono hsub (by simpa [colsF] using ht))
  | cons g gs ih =>
    intro cs L k n hlt hsub h31 h0 hok hrb hk hn ht
    obtain ⟨hop, hl⟩ := hok g (by simp)
    obtain ⟨hin, hrb'⟩ := hrb
    have hk' : gs.length + 1 ≤ k := by simpa using hk
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
    have hn0 : nots gs ≤ n := by
      by_cases hnot : g.op = .not
      · rw [nots_cons_not g gs hnot] at hn; omega
      · rw [nots_cons_other g gs hnot] at hn; exact hn
    have inL : gv g cs ∈ L → srch k n L = true := by
      intro hL
      have hsub' : ∀ x ∈ cs ++ [gv g cs], x ∈ L := by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hsub x hx
        · exact hL
      exact ih _ L k n hlt' hsub' h31 h0 hok' hrb2 (by omega) hn0 ht
    have hsub' : ∀ x ∈ cs ++ [gv g cs], x ∈ gv g cs :: L := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact List.mem_cons_of_mem _ (hsub x hx)
      · exact List.mem_cons_self
    rcases gv_reach g cs L hop hl hin hlt hsub h31 h0 with hL | ⟨hno, x, hx, y, hy, hxy⟩ | ⟨hno, x, hx, hxe⟩
    · exact inL hL
    · by_cases hvL : gv g cs ∈ L
      · exact inL hvL
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hs := ih _ (gv g cs :: L) k' n hlt' hsub' (List.mem_cons_of_mem _ h31)
          (List.mem_cons_of_mem _ h0) hok' hrb2 (by omega) hn0 ht
        have hm := srch_miss _ _ _ hs
        have hm2 := miss_step hab hac hbc L (gv g cs)
        by_cases htt : miss L = k' + 1
        · exact srch_tight htt _ (tight_target (L := L) (v := gv g cs) (by omega)) hvL (Or.inl ⟨reachM_of hx hy hxy, hs⟩)
        · exact srch_loose (by omega) htt (Or.inl ⟨_, mem_kids hx hy hxy hvL, hs⟩)
    · by_cases hvL : gv g cs ∈ L
      · exact inL hvL
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [nots_cons_not g gs hno] at hn
        have hs := ih _ (gv g cs :: L) k' (n - 1) hlt' hsub' (List.mem_cons_of_mem _ h31)
          (List.mem_cons_of_mem _ h0) hok' hrb2 (by omega) (by omega) ht
        have hm := srch_miss _ _ _ hs
        have hm2 := miss_step hab hac hbc L (gv g cs)
        by_cases htt : miss L = k' + 1
        · exact srch_tight htt _ (tight_target (L := L) (v := gv g cs) (by omega)) hvL (Or.inr ⟨by omega, reachN_of hx hxe, hs⟩)
        · exact srch_loose (by omega) htt (Or.inr ⟨by omega, _, mem_nkids hx hxe hvL, hs⟩)

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

theorem none_ok : srch 6 2 inCols = false := by decide +kernel

end PEqualNP.Outside.L_meta_51132_aux

open PEqualNP.Outside.L_meta_51132_aux in
theorem PEqualNP.Outside.L_meta_51132 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (43 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val) := by
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
  have hL : D.gates.length ≤ 6 := hsize
  have hs := comp (by decide) (by decide) (by decide) D.gates inCols inCols 6 2 hlt0 (fun x hx => hx)
    (by decide) (by decide) hok hRB hL hn ht
  rw [none_ok] at hs
  exact Bool.false_ne_true hs
