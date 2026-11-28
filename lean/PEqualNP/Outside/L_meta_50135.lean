import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket
import Mathlib.Tactic.SplitIfs

namespace PEqualNP.Outside.L_meta_50135_aux

-- The statement is false. On the six rows t = 0..5 (inputs x_i = [i < t], then false and true) a wire
-- carries a 6-bit mask, bit t its value on row t: the inputs carry 62 60 56 48 32 0 63, an AND or OR gate of
-- fan-in at most two the AND or OR of at most two masks read, a NOT gate the complement of one (sim).
-- The search srch, run by the kernel (srch_top), shows that no GB such gates with at most two NOT gates
-- put all three target masks on wires; step0 and sound carry any circuit through that search.
-- For another gap of the family change T1 T2 T3 (distinct, below 64), GB and the namespace.

open PEqualNP.CircuitLowerBounds

-- the gap: the three target masks and the gate bound
def T1 : Nat := 10
def T2 : Nat := 34
def T3 : Nat := 40
def GB : Nat := 6

-- the masks of the input wires x0 x1 x2 x3 x4, false, true
def M0 : List Nat := [62, 60, 56, 48, 32, 0, 63]

-- a search state S is a set of masks below 64, as a bit mask
def orF (f : Nat → Nat) (l : List Nat) : Nat := l.foldr (fun z a => f z ||| a) 0
def bitsOf (S : Nat) : List Nat := (List.range 64).filter (fun x => S.testBit x)
def aoAll (P : List Nat) : Nat := orF (fun x => orF (fun y => 2 ^ (x &&& y) ||| 2 ^ (x ||| y)) P) P
def notAll (P : List Nat) : Nat := orF (fun x => 2 ^ (63 ^^^ x)) P
def newOf (A S : Nat) : List Nat := (List.range 64).filter (fun m => A.testBit m && !S.testBit m)
def newAO (S : Nat) : List Nat := newOf (aoAll (bitsOf S)) S
def newNOT (S : Nat) : List Nat := newOf (notAll (bitsOf S)) S
def S0 : Nat := orF (fun x => 2 ^ x) M0

-- the number of target masks not in S
def miss (S : Nat) : Nat :=
  (if S.testBit T1 then 0 else 1) + (if S.testBit T2 then 0 else 1) + (if S.testBit T3 then 0 else 1)

-- srch k n S: no k more gates, n NOT gates of 2 used so far, bring all three targets into S
def srch : Nat → Nat → Nat → Bool
  | 0, _, S => decide (miss S ≠ 0)
  | k + 1, n, S => decide (miss S ≠ 0) && (decide (k + 1 < miss S) ||
      ((newAO S).all (fun m => srch k n (S ||| 2 ^ m)) && (srch k n S &&
        (decide (2 ≤ n) || ((newNOT S).all (fun m => srch k (n + 1) (S ||| 2 ^ m)) && srch k (n + 1) S)))))

set_option maxHeartbeats 0 in
theorem srch_top : srch GB 0 S0 = true := by decide +kernel

theorem srch_succ {k n S : Nat} (h : srch (k + 1) n S = true) :
    k + 1 < miss S ∨ ((∀ m ∈ newAO S, srch k n (S ||| 2 ^ m) = true) ∧ srch k n S = true ∧
      (2 ≤ n ∨ ((∀ m ∈ newNOT S, srch k (n + 1) (S ||| 2 ^ m) = true) ∧ srch k (n + 1) S = true))) := by
  simp only [srch, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact h.2

theorem srch_pos {k n S : Nat} (h : srch k n S = true) : miss S ≠ 0 := by
  cases k with
  | zero => simpa only [srch, decide_eq_true_eq] using h
  | succ k =>
    simp only [srch, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

theorem srch_of_miss {k n S : Nat} (h : k < miss S) : srch k n S = true := by
  cases k with
  | zero => simp only [srch, decide_eq_true_eq]; omega
  | succ k =>
    simp only [srch, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨by omega, Or.inl h⟩

theorem bit_le (S T m : Nat) : (if S.testBit T = true then 0 else 1) ≤
    (if (S ||| 2 ^ m).testBit T = true then 0 else 1) + (if m = T then 1 else 0) := by
  simp only [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases h1 : S.testBit T = true <;> by_cases h2 : m = T <;> simp [h1, h2]

-- adding one mask removes at most one missing target (the targets are distinct)
theorem miss_le (S m : Nat) : miss S ≤ miss (S ||| 2 ^ m) + 1 := by
  have a := bit_le S T1 m
  have b := bit_le S T2 m
  have c := bit_le S T3 m
  have d12 : T1 ≠ T2 := by decide
  have d13 : T1 ≠ T3 := by decide
  have d23 : T2 ≠ T3 := by decide
  have d : (if m = T1 then 1 else 0) + (if m = T2 then 1 else 0) + (if m = T3 then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  unfold miss
  omega

theorem orF_mem (f : Nat → Nat) (i z : Nat) (hi : (f z).testBit i = true) :
    ∀ l : List Nat, z ∈ l → (orF f l).testBit i = true
  | [], h => by cases h
  | a :: l, h => by
    show (f a ||| orF f l).testBit i = true
    rw [Nat.testBit_or]
    rcases List.mem_cons.mp h with e | e
    · rw [← e, hi, Bool.true_or]
    · rw [orF_mem f i z hi l e, Bool.or_true]

theorem mem_bitsOf {S x : Nat} (hx : x < 64) (hS : S.testBit x = true) : x ∈ bitsOf S :=
  List.mem_filter.mpr ⟨List.mem_range.mpr hx, hS⟩

theorem mem_newOf {A S m : Nat} (hm : m < 64) (hA : A.testBit m = true) (hS : S.testBit m = false) :
    m ∈ newOf A S :=
  List.mem_filter.mpr ⟨List.mem_range.mpr hm, by simp [hA, hS]⟩

theorem ao_mem (S a b : Nat) (ha : a ∈ bitsOf S) (hb : b ∈ bitsOf S) :
    (aoAll (bitsOf S)).testBit (a &&& b) = true ∧ (aoAll (bitsOf S)).testBit (a ||| b) = true := by
  unfold aoAll
  constructor
  · apply orF_mem _ _ a _ _ ha
    apply orF_mem _ _ b _ _ hb
    simp [Nat.testBit_or]
  · apply orF_mem _ _ a _ _ ha
    apply orF_mem _ _ b _ _ hb
    simp [Nat.testBit_or]

theorem not_mem (S a : Nat) (ha : a ∈ bitsOf S) : (notAll (bitsOf S)).testBit (63 ^^^ a) = true := by
  unfold notAll
  apply orF_mem _ _ a _ _ ha
  simp

theorem t63 : ∀ t < 6, (63 : Nat).testBit t = true := by decide +kernel
theorem and_lt : ∀ a < 64, ∀ b < 64, a &&& b < 64 := by decide +kernel
theorem or_lt : ∀ a < 64, ∀ b < 64, a ||| b < 64 := by decide +kernel
theorem xor_lt : ∀ a < 64, 63 ^^^ a < 64 := by decide +kernel
theorem eq_of_bits : ∀ x < 64, ∀ y < 64, (∀ t < 6, x.testBit t = y.testBit t) → x = y := by decide +kernel
theorem m0_good : ∀ x ∈ M0, x < 64 ∧ S0.testBit x = true := by decide +kernel
theorem s0_0 : S0.testBit 0 = true := by decide +kernel
theorem s0_63 : S0.testBit 63 = true := by decide +kernel
theorem t1_lt : T1 < 64 := by decide
theorem t2_lt : T2 < 64 := by decide
theorem t3_lt : T3 < 64 := by decide

-- one gate on a set S of present masks: its mask m is present, or an AND/OR of two present masks
-- (b = false), or the complement of a present mask (b = true, a NOT gate)
theorem step0 (k n S m : Nat) (b : Bool) (hlt : m < 64)
    (hc : S.testBit m = true ∨ (b = false ∧ (aoAll (bitsOf S)).testBit m = true) ∨
      (b = true ∧ (notAll (bitsOf S)).testBit m = true))
    (hf : srch (k + 1) n S = true) (hn : b = true → n < 2) :
    ∃ S', (∀ x, S.testBit x = true → S'.testBit x = true) ∧ S'.testBit m = true ∧
      srch k (n + (if b = true then 1 else 0)) S' = true := by
  have hsup : ∀ x, S.testBit x = true → (S ||| 2 ^ m).testBit x = true := fun x hx => by
    simp [Nat.testBit_or, hx]
  have hm : (S ||| 2 ^ m).testBit m = true := by simp [Nat.testBit_or]
  rcases srch_succ hf with hmiss | ⟨hAO, hk, hNOT⟩
  · exact ⟨S ||| 2 ^ m, hsup, hm, srch_of_miss (by have := miss_le S m; omega)⟩
  · by_cases hS : S.testBit m = true
    · refine ⟨S, fun x hx => hx, hS, ?_⟩
      cases b
      · exact hk
      · rcases hNOT with h2 | ⟨_, hk1⟩
        · exact absurd (hn rfl) (by omega)
        · exact hk1
    · have hSf : S.testBit m = false := by
        cases h : S.testBit m
        · rfl
        · exact absurd h hS
      refine ⟨S ||| 2 ^ m, hsup, hm, ?_⟩
      rcases hc with hc | ⟨hb, hA⟩ | ⟨hb, hA⟩
      · exact absurd hc hS
      · subst hb
        exact hAO m (mem_newOf hlt hA hSf)
      · subst hb
        rcases hNOT with h2 | ⟨hN, _⟩
        · exact absurd (hn rfl) (by omega)
        · exact hN m (mem_newOf hlt hA hSf)

-- the circuit side: masks of gates
def isNot : GateOp → Bool
  | GateOp.and => false
  | GateOp.or => false
  | GateOp.not => true
  | GateOp.mod _ => false
  | GateOp.maj => false

def nnot : List Gate → Nat
  | [] => 0
  | g :: gs => (if isNot g.op then 1 else 0) + nnot gs

-- the mask of a gate from the masks it reads (fan-in at most two)
def gm : GateOp → List Nat → Nat
  | GateOp.and, [] => 63
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => 63
  | GateOp.not, a :: _ => 63 ^^^ a
  | GateOp.mod _, _ => 0
  | GateOp.maj, _ => 0

def mstep (W : List Nat) (g : Gate) : List Nat := W ++ [gm g.op (g.inputs.map fun i => W.getD i 0)]

def smStep (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def xsN (t : Nat) : List Bool := List.ofFn (fun i : Fin 5 => decide (i.val < t)) ++ [false, true]

theorem xs_eq : ∀ t < 6, xsN t = M0.map (fun x => x.testBit t) := by decide +kernel

theorem nnot_eq (C : Circuit) : PEqualNP.NotBracket.notCount C = nnot C.gates := by
  unfold PEqualNP.NotBracket.notCount
  generalize C.gates = gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.filter_cons, nnot]
    rcases hop : g.op with _ | _ | _ | m | _ <;> simp [isNot, ih]
    omega

theorem getD_tb (t : Nat) : ∀ (W : List Nat) (i : Nat),
    (W.map (fun x => x.testBit t)).getD i false = (W.getD i 0).testBit t
  | [], i => by rw [List.map_nil, List.getD_nil, List.getD_nil, Nat.zero_testBit]
  | a :: W, 0 => by rw [List.map_cons, List.getD_cons_zero, List.getD_cons_zero]
  | a :: W, i + 1 => by
    rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]
    exact getD_tb t W i

theorem getD_mem : ∀ (W : List Nat) (i : Nat), i < W.length → W.getD i 0 ∈ W
  | [], i, h => by simp at h
  | a :: W, 0, _ => by rw [List.getD_cons_zero]; exact List.mem_cons.mpr (Or.inl rfl)
  | a :: W, i + 1, h => by
    rw [List.getD_cons_succ]
    exact List.mem_cons.mpr (Or.inr (getD_mem W i (by rw [List.length_cons] at h; omega)))

theorem getD_cases : ∀ (W : List Nat) (i : Nat), W.getD i 0 = 0 ∨ W.getD i 0 ∈ W
  | [], i => Or.inl List.getD_nil
  | a :: W, 0 => Or.inr (by rw [List.getD_cons_zero]; exact List.mem_cons.mpr (Or.inl rfl))
  | a :: W, i + 1 => by
    rw [List.getD_cons_succ]
    rcases getD_cases W i with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons.mpr (Or.inr h))

theorem evalm (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (t : Nat) (ht : t < 6) :
    ∀ ms : List Nat, ms.length ≤ 2 → op.eval (ms.map (fun x => x.testBit t)) = (gm op ms).testBit t
  | [], _ => by
    have h63 := t63 t ht
    rcases hop with rfl | rfl | rfl <;> simp [GateOp.eval, gm, h63]
  | [a], _ => by
    have h63 := t63 t ht
    rcases hop with rfl | rfl | rfl <;> simp [GateOp.eval, gm, h63]
  | [a, b], _ => by
    have h63 := t63 t ht
    rcases hop with rfl | rfl | rfl <;> simp [GateOp.eval, gm, h63]
  | _ :: _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

-- on row t the wires are the bits t of the masks
theorem sim (t : Nat) (ht : t < 6) : ∀ (gs : List Gate) (W : List Nat),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    gs.foldl smStep (W.map (fun x => x.testBit t)) = (gs.foldl mstep W).map (fun x => x.testBit t)
  | [], W, _ => rfl
  | g :: gs, W, hgs => by
    have hg := hgs g (List.mem_cons.mpr (Or.inl rfl))
    have e1 : (g.inputs.map fun i => (W.map (fun x => x.testBit t)).getD i false) =
        (g.inputs.map fun i => W.getD i 0).map (fun x => x.testBit t) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => getD_tb t W i)
    have e2 := evalm g.op hg.1 t ht (g.inputs.map fun i => W.getD i 0) (by rw [List.length_map]; exact hg.2)
    have e : smStep (W.map (fun x => x.testBit t)) g = (mstep W g).map (fun x => x.testBit t) := by
      simp only [smStep, mstep, List.map_append, List.map_cons, List.map_nil]
      rw [e1, e2]
    rw [List.foldl_cons, List.foldl_cons, e]
    exact sim t ht gs (mstep W g) (fun g' h' => hgs g' (List.mem_cons.mpr (Or.inr h')))

theorem mfold_len : ∀ (gs : List Gate) (W : List Nat), (gs.foldl mstep W).length = W.length + gs.length
  | [], W => rfl
  | g :: gs, W => by
    rw [List.foldl_cons, mfold_len gs (mstep W g)]
    simp only [mstep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem gm_cases (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (S : Nat)
    (h0 : S.testBit 0 = true) (h63 : S.testBit 63 = true) :
    ∀ ms : List Nat, (∀ x ∈ ms, x < 64 ∧ S.testBit x = true) →
    gm op ms < 64 ∧ (S.testBit (gm op ms) = true ∨
      (isNot op = false ∧ (aoAll (bitsOf S)).testBit (gm op ms) = true) ∨
      (isNot op = true ∧ (notAll (bitsOf S)).testBit (gm op ms) = true))
  | [], _ => by
    rcases hop with rfl | rfl | rfl
    · exact ⟨by decide, Or.inl h63⟩
    · exact ⟨by decide, Or.inl h0⟩
    · exact ⟨by decide, Or.inl h63⟩
  | [a], hms => by
    have ha := hms a (List.mem_cons.mpr (Or.inl rfl))
    rcases hop with rfl | rfl | rfl
    · exact ⟨ha.1, Or.inl ha.2⟩
    · exact ⟨ha.1, Or.inl ha.2⟩
    · exact ⟨xor_lt a ha.1, Or.inr (Or.inr ⟨rfl, not_mem S a (mem_bitsOf ha.1 ha.2)⟩)⟩
  | a :: b :: rest, hms => by
    have ha := hms a (List.mem_cons.mpr (Or.inl rfl))
    have hb := hms b (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    have hab := ao_mem S a b (mem_bitsOf ha.1 ha.2) (mem_bitsOf hb.1 hb.2)
    rcases hop with rfl | rfl | rfl
    · exact ⟨and_lt a ha.1 b hb.1, Or.inr (Or.inl ⟨rfl, hab.1⟩)⟩
    · exact ⟨or_lt a ha.1 b hb.1, Or.inr (Or.inl ⟨rfl, hab.2⟩)⟩
    · exact ⟨xor_lt a ha.1, Or.inr (Or.inr ⟨rfl, not_mem S a (mem_bitsOf ha.1 ha.2)⟩)⟩

-- any gate list drives the search: the masks of all wires end in a set that still misses a target
theorem sound : ∀ (gs : List Gate) (W : List Nat) (S k n : Nat),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    gs.length ≤ k → n + nnot gs ≤ 2 → (∀ x ∈ W, x < 64 ∧ S.testBit x = true) →
    S.testBit 0 = true → S.testBit 63 = true → srch k n S = true →
    ∃ S', (∀ x ∈ gs.foldl mstep W, x < 64 ∧ S'.testBit x = true) ∧ miss S' ≠ 0
  | [], W, S, _, _, _, _, _, hW, _, _, hf => ⟨S, hW, srch_pos hf⟩
  | g :: gs, W, S, k, n, hgs, hlen, hn, hW, h0, h63, hf => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by rw [List.length_cons] at hlen; omega⟩
    have hg := hgs g (List.mem_cons.mpr (Or.inl rfl))
    have hms : ∀ x ∈ g.inputs.map (fun i => W.getD i 0), x < 64 ∧ S.testBit x = true := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      rcases getD_cases W i with e | e
      · rw [e]; exact ⟨by decide, h0⟩
      · exact hW _ e
    have hn' : n + ((if isNot g.op = true then 1 else 0) + nnot gs) ≤ 2 := hn
    have hn2 : isNot g.op = true → n < 2 := fun hno => by
      have e : (if isNot g.op = true then 1 else 0) = 1 := by simp [hno]
      omega
    obtain ⟨hlt, hc⟩ := gm_cases g.op hg.1 S h0 h63 _ hms
    obtain ⟨S', hsup, hm, hf'⟩ := step0 k n S _ (isNot g.op) hlt hc hf hn2
    refine sound gs (mstep W g) S' k (n + (if isNot g.op = true then 1 else 0))
      (fun g' h' => hgs g' (List.mem_cons.mpr (Or.inr h'))) (by rw [List.length_cons] at hlen; omega)
      (by omega) (fun x hx => ?_) (hsup 0 h0) (hsup 63 h63) hf'
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨(hW x hx).1, hsup x (hW x hx).2⟩
    · rw [List.mem_singleton] at hx
      rw [hx]
      exact ⟨hlt, hm⟩

theorem key_lemma (Wf : List Nat) (S x T : Nat) (hS : ∀ y ∈ Wf, y < 64 ∧ S.testBit y = true)
    (hx : x < Wf.length) (hT : T < 64)
    (hb : ∀ t : Fin 6, (Wf.map (fun y => y.testBit t.val)).getD x false = T.testBit t.val) :
    S.testBit T = true := by
  have hmem := getD_mem Wf x hx
  obtain ⟨hlt, hbit⟩ := hS _ hmem
  have e : Wf.getD x 0 = T := eq_of_bits _ hlt _ hT (fun t ht => by
    have h1 := hb ⟨t, ht⟩
    rw [getD_tb] at h1
    exact h1)
  rw [← e]
  exact hbit

theorem main (D : Circuit) (p q r : Nat) (hp : p < 7 + D.size) (hq : q < 7 + D.size) (hr : r < 7 + D.size)
    (hfan : PEqualNP.MetaComplexity.FanInTwo D) (hnot : PEqualNP.NotBracket.notCount D ≤ 2)
    (hsize : D.size ≤ GB)
    (hval : ∀ t : Fin 6, (D.wires (xsN t.val)).getD p false = T1.testBit t.val ∧
      (D.wires (xsN t.val)).getD q false = T2.testBit t.val ∧
      (D.wires (xsN t.val)).getD r false = T3.testBit t.val) : False := by
  have hops : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 :=
    fun g hg => ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hfan g hg).1, (hfan g hg).2⟩
  have hsim : ∀ t : Fin 6, D.wires (xsN t.val) = (D.gates.foldl mstep M0).map (fun x => x.testBit t.val) := by
    intro t
    show D.gates.foldl smStep (xsN t.val) = _
    rw [xs_eq t.val t.isLt]
    exact sim t.val t.isLt D.gates M0 hops
  have hlen : (D.gates.foldl mstep M0).length = 7 + D.size := by rw [mfold_len]; rfl
  obtain ⟨S, hS, hmiss⟩ := sound D.gates M0 S0 GB 0 hops hsize (by rw [← nnot_eq]; omega) m0_good s0_0 s0_63
    srch_top
  have k1 := key_lemma _ S p T1 hS (by rw [hlen]; exact hp) t1_lt (fun t => by rw [← hsim t]; exact (hval t).1)
  have k2 := key_lemma _ S q T2 hS (by rw [hlen]; exact hq) t2_lt (fun t => by rw [← hsim t]; exact (hval t).2.1)
  have k3 := key_lemma _ S r T3 hS (by rw [hlen]; exact hr) t3_lt (fun t => by rw [← hsim t]; exact (hval t).2.2)
  exact hmiss (by simp [miss, k1, k2, k3])

end PEqualNP.Outside.L_meta_50135_aux

theorem PEqualNP.Outside.L_meta_50135 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (10 : Nat).testBit t.val ∧
    w.getD q.val false = (34 : Nat).testBit t.val ∧
    w.getD r.val false = (40 : Nat).testBit t.val) := by
  intro h
  obtain ⟨D, p, q, r, hfan, -, hnot, hsize, hval⟩ := h
  exact PEqualNP.Outside.L_meta_50135_aux.main D p.val q.val r.val p.isLt q.isLt r.isLt hfan hnot hsize hval
