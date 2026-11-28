import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53150

namespace fitPart

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩], 12⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end fitPart

set_option maxRecDepth 100000 in
theorem fitPart : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
    PEqualNP.NotBracket.notCount D ≤ 3 ∧ D.size ≤ 7 ∧
    ∀ t : Fin 5,
      let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
      let w := D.wires xs
      w.getD p.val false = (4 : Nat).testBit t.val ∧
      w.getD q.val false = (12 : Nat).testBit t.val ∧
      w.getD r.val false = (29 : Nat).testBit t.val :=
  ⟨fitPart.C, ⟨9, by decide⟩, ⟨12, by decide⟩, ⟨7, by decide⟩, fitPart.fan,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

namespace failPart

open PEqualNP.CircuitLowerBounds

def tA : Nat := 4
def tB : Nat := 12
def tC : Nat := 29

def ofb (a b c d e : Bool) : Nat := a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat

theorem ofb_lt : ∀ a b c d e : Bool, ofb a b c d e < 32 := by decide
theorem ofb_and : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
    ofb (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) (a4 && b4) =
      ofb a0 a1 a2 a3 a4 &&& ofb b0 b1 b2 b3 b4 := by decide
theorem ofb_or : ∀ a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Bool,
    ofb (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) =
      ofb a0 a1 a2 a3 a4 ||| ofb b0 b1 b2 b3 b4 := by decide
theorem ofb_not : ∀ a0 a1 a2 a3 a4 : Bool,
    ofb (!a0) (!a1) (!a2) (!a3) (!a4) = 31 ^^^ ofb a0 a1 a2 a3 a4 := by decide

def orAll (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i+1 => orAll f i ||| f i

theorem orAll_bit (f : Nat → Nat) (b : Nat) : ∀ N i, i < N → (f i).testBit b = true →
    (orAll f N).testBit b = true := by
  intro N
  induction N with
  | zero => intro i h; omega
  | succ N ih =>
    intro i hi hb
    simp only [orAll, Nat.testBit_or, Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact Or.inl (ih i h hb)
    · subst h; exact Or.inr hb

def allBelow (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | i+1 => allBelow f i && f i

theorem allBelow_spec (f : Nat → Bool) : ∀ N i, i < N → allBelow f N = true → f i = true := by
  intro N
  induction N with
  | zero => intro i h; omega
  | succ N ih =>
    intro i hi h
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
    · exact ih i h' h.1
    · subst h'; exact h.2

def succM (S : Nat) : Nat :=
  orAll (fun x => if S.testBit x then
    orAll (fun y => if S.testBit y then (1 <<< (x &&& y)) ||| (1 <<< (x ||| y)) else 0) 32 else 0) 32

def notM (S : Nat) : Nat :=
  orAll (fun x => if S.testBit x then 1 <<< (31 ^^^ x) else 0) 32

theorem bit_shift (v : Nat) : (1 <<< v).testBit v = true := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_self]

theorem succM_and (S x y : Nat) (hx : x < 32) (hy : y < 32) (hxs : S.testBit x = true)
    (hys : S.testBit y = true) : (succM S).testBit (x &&& y) = true := by
  apply orAll_bit _ _ 32 x hx
  simp only [hxs, ↓reduceIte]
  apply orAll_bit _ _ 32 y hy
  simp only [hys, ↓reduceIte]; rw [Nat.testBit_or, bit_shift]; rfl

theorem succM_or (S x y : Nat) (hx : x < 32) (hy : y < 32) (hxs : S.testBit x = true)
    (hys : S.testBit y = true) : (succM S).testBit (x ||| y) = true := by
  apply orAll_bit _ _ 32 x hx
  simp only [hxs, ↓reduceIte]
  apply orAll_bit _ _ 32 y hy
  simp only [hys, ↓reduceIte]; rw [Nat.testBit_or, bit_shift, Bool.or_true]

theorem notM_bit (S x : Nat) (hx : x < 32) (hxs : S.testBit x = true) :
    (notM S).testBit (31 ^^^ x) = true := by
  apply orAll_bit _ _ 32 x hx
  simp only [hxs, ↓reduceIte]; rw [bit_shift]

def miss (S : Nat) : Nat :=
  (if S.testBit tA then 0 else 1) + (if S.testBit tB then 0 else 1) + (if S.testBit tC then 0 else 1)

theorem ind (S v T : Nat) : (if S.testBit T = true then 0 else 1) ≤
    (if (S ||| 1 <<< v).testBit T = true then 0 else 1) + (if v = T then 1 else 0) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : v = T <;> by_cases hs : S.testBit T = true <;> simp [h, hs]

theorem miss_add (S v : Nat) : miss S ≤ miss (S ||| 1 <<< v) + 1 := by
  have h1 := ind S v tA
  have h2 := ind S v tB
  have h3 := ind S v tC
  have h4 : (if v = tA then 1 else 0) + (if v = tB then 1 else 0) + (if v = tC then 1 else 0) ≤ 1 := by
    unfold tA tB tC; split <;> split <;> split <;> omega
  unfold miss; omega

def safe : Nat → Nat → Nat → Bool
  | 0, _, S => miss S != 0
  | k+1, n, S => miss S != 0 && (decide (k + 1 < miss S) || allBelow (fun v => S.testBit v ||
      ((!(succM S).testBit v || safe k n (S ||| 1 <<< v)) &&
        (n == 0 || !(notM S).testBit v || safe k (n - 1) (S ||| 1 <<< v)))) 32)

theorem safe_miss : ∀ k n S, safe k n S = true → miss S ≠ 0 := by
  intro k n S h
  cases k with
  | zero => simpa [safe] using h
  | succ k => simp only [safe, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; exact h.1

theorem safe_of_lt : ∀ k n S, k < miss S → safe k n S = true := by
  intro k n S h
  cases k with
  | zero => simp [safe]; omega
  | succ k => simp [safe]; omega

theorem safe_split (k n S : Nat) (h : safe (k+1) n S = true) :
    k + 1 < miss S ∨ allBelow (fun v => S.testBit v ||
      ((!(succM S).testBit v || safe k n (S ||| 1 <<< v)) &&
        (n == 0 || !(notM S).testBit v || safe k (n - 1) (S ||| 1 <<< v)))) 32 = true := by
  simp only [safe, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem allBelow_mono (f g : Nat → Bool) (h : ∀ i, f i = true → g i = true) :
    ∀ N, allBelow f N = true → allBelow g N = true := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro h'
    simp only [allBelow, Bool.and_eq_true] at h' ⊢
    exact ⟨ih h'.1, h _ h'.2⟩

theorem imp_helper : ∀ (s a b d c1 c2 e1 e2 : Bool), (c1 = true → e1 = true) → (c2 = true → e2 = true) →
    (s || ((!a || c1) && (b || !d || c2))) = true → (s || ((!a || e1) && (b || !d || e2))) = true := by
  decide

def Good (L : List (Nat × Nat × Nat)) : Prop := ∀ x ∈ L, safe x.1 x.2.1 x.2.2 = true

theorem good_nil : Good [] := fun _ h => absurd h (List.not_mem_nil)

theorem good_cons (x : Nat × Nat × Nat) (L : List (Nat × Nat × Nat)) (h : safe x.1 x.2.1 x.2.2 = true)
    (hL : Good L) : Good (x :: L) := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact h
  · exact hL y hy

def safeC (L : List (Nat × Nat × Nat)) : Nat → Nat → Nat → Bool
  | 0, _, S => miss S != 0
  | k+1, n, S => miss S != 0 && (decide (k + 1 < miss S) ||
      L.any (fun x => x.1 == k + 1 && x.2.1 == n && x.2.2 == S) || allBelow (fun v => S.testBit v ||
      ((!(succM S).testBit v || safeC L k n (S ||| 1 <<< v)) &&
        (n == 0 || !(notM S).testBit v || safeC L k (n - 1) (S ||| 1 <<< v)))) 32)

theorem safeC_sound (L : List (Nat × Nat × Nat)) (hL : Good L) :
    ∀ k n S, safeC L k n S = true → safe k n S = true := by
  intro k
  induction k with
  | zero => intro n S h; simpa [safeC, safe] using h
  | succ k ih =>
    intro n S h
    simp only [safeC, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨hm, (h | h) | h⟩ := h
    · simp only [safe, Bool.and_eq_true, Bool.or_eq_true]; exact ⟨hm, Or.inl h⟩
    · rw [List.any_eq_true] at h
      obtain ⟨x, hx, he⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at he
      obtain ⟨⟨h1, h2⟩, h3⟩ := he
      have := hL x hx
      rw [h1, h2, h3] at this
      exact this
    · simp only [safe, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨hm, Or.inr ?_⟩
      exact allBelow_mono _ _ (fun v hv => imp_helper _ _ _ _ _ _ _ _ (ih _ _) (ih _ _) hv) 32 h

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ev (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def V (w0 w1 w2 w3 w4 : List Bool) (i : Nat) : Nat :=
  ofb (w0.getD i false) (w1.getD i false) (w2.getD i false) (w3.getD i false) (w4.getD i false)

def okG (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def nc (gs : List Gate) : Nat := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem nc_le (g : Gate) (gs : List Gate) : nc gs ≤ nc (g :: gs) := by
  unfold nc PEqualNP.NotBracket.notCount; rw [List.filter_cons]; split <;> simp

theorem nc_not (g : Gate) (gs : List Gate) (h : g.op = GateOp.not) : nc (g :: gs) = nc gs + 1 := by
  unfold nc PEqualNP.NotBracket.notCount; rw [List.filter_cons]; split
  · simp
  · rename_i h'; simp [h] at h'

theorem getD_snoc (w : List Bool) (e : Bool) (i : Nat) :
    (w ++ [e]).getD i false = if i = w.length then e else w.getD i false := by
  rcases Nat.lt_trichotomy i w.length with h | h | h
  · simp only [show ¬ (i = w.length) by omega, ↓reduceIte]; rw [List.getD_append _ _ _ _ h]
  · subst h; simp
  · simp only [show ¬ (i = w.length) by omega, ↓reduceIte]
    rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem V_snoc (g : Gate) (w0 w1 w2 w3 w4 : List Bool) (h1 : w1.length = w0.length)
    (h2 : w2.length = w0.length) (h3 : w3.length = w0.length) (h4 : w4.length = w0.length) (i : Nat) :
    V (stepW w0 g) (stepW w1 g) (stepW w2 g) (stepW w3 g) (stepW w4 g) i =
      if i = w0.length then ofb (ev g w0) (ev g w1) (ev g w2) (ev g w3) (ev g w4)
      else V w0 w1 w2 w3 w4 i := by
  unfold V stepW
  rw [getD_snoc, getD_snoc, getD_snoc, getD_snoc, getD_snoc, h1, h2, h3, h4]
  split <;> rfl

theorem ev_and1 (i : Nat) (w : List Bool) : ev ⟨GateOp.and, [i]⟩ w = w.getD i false := by
  simp [ev, GateOp.eval]
theorem ev_or1 (i : Nat) (w : List Bool) : ev ⟨GateOp.or, [i]⟩ w = w.getD i false := by
  simp [ev, GateOp.eval]
theorem ev_not1 (i : Nat) (r : List Nat) (w : List Bool) :
    ev ⟨GateOp.not, i :: r⟩ w = !w.getD i false := by
  simp [ev, GateOp.eval]
theorem ev_and2 (i j : Nat) (w : List Bool) :
    ev ⟨GateOp.and, [i, j]⟩ w = (w.getD i false && w.getD j false) := by
  simp [ev, GateOp.eval]
theorem ev_or2 (i j : Nat) (w : List Bool) :
    ev ⟨GateOp.or, [i, j]⟩ w = (w.getD i false || w.getD j false) := by
  simp [ev, GateOp.eval]

theorem cls (g : Gate) (hg : okG g) (w0 w1 w2 w3 w4 : List Bool) (S : Nat)
    (hS : ∀ i, S.testBit (V w0 w1 w2 w3 w4 i) = true) (h0 : S.testBit 0 = true)
    (h31 : S.testBit 31 = true) :
    S.testBit (ofb (ev g w0) (ev g w1) (ev g w2) (ev g w3) (ev g w4)) = true ∨
    (succM S).testBit (ofb (ev g w0) (ev g w1) (ev g w2) (ev g w3) (ev g w4)) = true ∨
    (g.op = GateOp.not ∧
      (notM S).testBit (ofb (ev g w0) (ev g w1) (ev g w2) (ev g w3) (ev g w4)) = true) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · left; exact h31
    · left; exact h0
    · left; exact h31
  | [i], _ =>
    rcases hop with rfl | rfl | rfl
    · left; simp only [ev_and1]; exact hS i
    · left; simp only [ev_or1]; exact hS i
    · right; right; refine ⟨rfl, ?_⟩
      simp only [ev_not1, ofb_not]; exact notM_bit S _ (ofb_lt _ _ _ _ _) (hS i)
  | [i, j], _ =>
    rcases hop with rfl | rfl | rfl
    · right; left; simp only [ev_and2, ofb_and]
      exact succM_and S _ _ (ofb_lt _ _ _ _ _) (ofb_lt _ _ _ _ _) (hS i) (hS j)
    · right; left; simp only [ev_or2, ofb_or]
      exact succM_or S _ _ (ofb_lt _ _ _ _ _) (ofb_lt _ _ _ _ _) (hS i) (hS j)
    · right; right; refine ⟨rfl, ?_⟩
      simp only [ev_not1, ofb_not]; exact notM_bit S _ (ofb_lt _ _ _ _ _) (hS i)
  | _ :: _ :: _ :: _, h => simp at h

theorem bitS (S v x : Nat) (h : S.testBit x = true) : (S ||| 1 <<< v).testBit x = true := by
  rw [Nat.testBit_or, h, Bool.true_or]

theorem core : ∀ (gs : List Gate) (w0 w1 w2 w3 w4 : List Bool) (S k n : Nat),
    w1.length = w0.length → w2.length = w0.length → w3.length = w0.length → w4.length = w0.length →
    (∀ i, S.testBit (V w0 w1 w2 w3 w4 i) = true) → S.testBit 0 = true → S.testBit 31 = true →
    safe k n S = true → gs.length ≤ k → nc gs ≤ n → (∀ g ∈ gs, okG g) →
    ∃ S', miss S' ≠ 0 ∧ ∀ i, S'.testBit (V (gs.foldl stepW w0) (gs.foldl stepW w1)
      (gs.foldl stepW w2) (gs.foldl stepW w3) (gs.foldl stepW w4) i) = true := by
  intro gs
  induction gs with
  | nil =>
    intro w0 w1 w2 w3 w4 S k n _ _ _ _ hS _ _ hs _ _ _
    exact ⟨S, safe_miss k n S hs, hS⟩
  | cons g rest ih =>
    intro w0 w1 w2 w3 w4 S k n l1 l2 l3 l4 hS h0 h31 hs hk hn hok
    have hg := hok g (List.mem_cons_self ..)
    have hok' : ∀ g ∈ rest, okG g := fun g' hm => hok g' (List.mem_cons_of_mem _ hm)
    have hnl := nc_le g rest
    simp only [List.length_cons] at hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have L1 : (stepW w1 g).length = (stepW w0 g).length := by simp [stepW, l1]
    have L2 : (stepW w2 g).length = (stepW w0 g).length := by simp [stepW, l2]
    have L3 : (stepW w3 g).length = (stepW w0 g).length := by simp [stepW, l3]
    have L4 : (stepW w4 g).length = (stepW w0 g).length := by simp [stepW, l4]
    have hc := cls g hg w0 w1 w2 w3 w4 S hS h0 h31
    have hlt := ofb_lt (ev g w0) (ev g w1) (ev g w2) (ev g w3) (ev g w4)
    have hV := V_snoc g w0 w1 w2 w3 w4 l1 l2 l3 l4
    generalize ofb (ev g w0) (ev g w1) (ev g w2) (ev g w3) (ev g w4) = v at hc hlt hV
    simp only [List.foldl_cons]
    have hS1 : ∀ T : Nat, (∀ i, T.testBit (V w0 w1 w2 w3 w4 i) = true) → T.testBit v = true →
        ∀ i, T.testBit (V (stepW w0 g) (stepW w1 g) (stepW w2 g) (stepW w3 g) (stepW w4 g) i) = true := by
      intro T hT hv i
      rw [hV i]
      split
      · exact hv
      · exact hT i
    by_cases hv : S.testBit v = true
    · exact ih _ _ _ _ _ S (k' + 1) n L1 L2 L3 L4 (hS1 S hS hv) h0 h31 hs (by omega) (by omega) hok'
    · have hvb : (S ||| 1 <<< v).testBit v = true := by rw [Nat.testBit_or, bit_shift, Bool.or_true]
      have hS' := hS1 (S ||| 1 <<< v) (fun i => bitS _ _ _ (hS i)) hvb
      have h0' := bitS S v 0 h0
      have h31' := bitS S v 31 h31
      rcases safe_split k' n S hs with hm | ha
      · have hm2 := miss_add S v
        exact ih _ _ _ _ _ _ k' n L1 L2 L3 L4 hS' h0' h31' (safe_of_lt _ _ _ (by omega))
          (by omega) (by omega) hok'
      · have hb := allBelow_spec _ 32 v hlt ha
        simp only [Bool.eq_false_iff.mpr hv, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
          Bool.not_eq_true', beq_iff_eq] at hb
        rcases hc with hc | hc | ⟨hgn, hc⟩
        · exact absurd hc hv
        · have hsf : safe k' n (S ||| 1 <<< v) = true := by
            rcases hb.1 with h | h
            · rw [hc] at h; exact absurd h (by decide)
            · exact h
          exact ih _ _ _ _ _ _ k' n L1 L2 L3 L4 hS' h0' h31' hsf (by omega) (by omega) hok'
        · have hn := nc_not g rest hgn
          have hsf : safe k' (n - 1) (S ||| 1 <<< v) = true := by
            rcases hb.2 with (h | h) | h
            · omega
            · rw [hc] at h; exact absurd h (by decide)
            · exact h
          exact ih _ _ _ _ _ _ k' (n - 1) L1 L2 L3 L4 hS' h0' h31' hsf (by omega) (by omega) hok'

def xs (t : Nat) : List Bool := List.ofFn (fun i : Fin 4 => decide (i.val < t)) ++ [false,true]

def S0 : Nat := 3506503681

theorem xs_len (t : Nat) : (xs t).length = 6 := by simp [xs]

theorem init_ok : ∀ i, S0.testBit (V (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) i) = true := by
  intro i
  rcases i with _ | _ | _ | _ | _ | _ | i
  all_goals try decide
  have hd : ∀ t, (xs t).getD (i + 6) false = false := fun t =>
    List.getD_eq_default _ _ (by rw [xs_len]; omega)
  unfold V
  rw [hd, hd, hd, hd, hd]
  decide

def L0 : List (Nat × Nat × Nat) := []

theorem g0 : Good L0 := good_nil

theorem s0 : safeC L0 4 0 3506503695 = true := by decide +kernel

def L1 : List (Nat × Nat × Nat) := (4, 0, 3506503695) :: L0

theorem g1 : Good L1 := good_cons _ _ (safeC_sound L0 g0 4 0 3506503695 s0) g0

theorem s1 : safeC L1 4 0 3506634763 = true := by decide +kernel

def L2 : List (Nat × Nat × Nat) := (4, 0, 3506634763) :: L1

theorem g2 : Good L2 := good_cons _ _ (safeC_sound L1 g1 4 0 3506634763 s1) g1

theorem s2 : safeC L2 4 0 3507027979 = true := by decide +kernel

def L3 : List (Nat × Nat × Nat) := (4, 0, 3507027979) :: L2

theorem g3 : Good L3 := good_cons _ _ (safeC_sound L2 g2 4 0 3507027979 s2) g2

theorem s3 : safeC L3 4 0 3540058123 = true := by decide +kernel

def L4 : List (Nat × Nat × Nat) := (4, 0, 3540058123) :: L3

theorem g4 : Good L4 := good_cons _ _ (safeC_sound L3 g3 4 0 3540058123 s3) g3

theorem s4 : safeC L4 4 0 3640721419 = true := by decide +kernel

def L5 : List (Nat × Nat × Nat) := (4, 0, 3640721419) :: L4

theorem g5 : Good L5 := good_cons _ _ (safeC_sound L4 g4 4 0 3640721419 s4) g4

theorem s5 : safeC L5 4 0 4043374603 = true := by decide +kernel

def L6 : List (Nat × Nat × Nat) := (4, 0, 4043374603) :: L5

theorem g6 : Good L6 := good_cons _ _ (safeC_sound L5 g5 4 0 4043374603 s5) g5

theorem s6 : safeC L6 5 0 3506503691 = true := by decide +kernel

def L7 : List (Nat × Nat × Nat) := (5, 0, 3506503691) :: L6

theorem g7 : Good L7 := good_cons _ _ (safeC_sound L6 g6 5 0 3506503691 s6) g6

theorem s7 : safeC L7 3 0 3506503859 = true := by decide +kernel

def L8 : List (Nat × Nat × Nat) := (3, 0, 3506503859) :: L7

theorem g8 : Good L8 := good_cons _ _ (safeC_sound L7 g7 3 0 3506503859 s7) g7

theorem s8 : safeC L8 3 0 3506503891 = true := by decide +kernel

def L9 : List (Nat × Nat × Nat) := (3, 0, 3506503891) :: L8

theorem g9 : Good L9 := good_cons _ _ (safeC_sound L8 g8 3 0 3506503891 s8) g8

theorem s9 : safeC L9 3 0 3506634899 = true := by decide +kernel

def L10 : List (Nat × Nat × Nat) := (3, 0, 3506634899) :: L9

theorem g10 : Good L10 := good_cons _ _ (safeC_sound L9 g9 3 0 3506634899 s9) g9

theorem s10 : safeC L10 3 0 3507552403 = true := by decide +kernel

def L11 : List (Nat × Nat × Nat) := (3, 0, 3507552403) :: L10

theorem g11 : Good L11 := good_cons _ _ (safeC_sound L10 g10 3 0 3507552403 s10) g10

theorem s11 : safeC L11 3 0 3514892435 = true := by decide +kernel

def L12 : List (Nat × Nat × Nat) := (3, 0, 3514892435) :: L11

theorem g12 : Good L12 := good_cons _ _ (safeC_sound L11 g11 3 0 3514892435 s11) g11

theorem s12 : safeC L12 3 0 3540058259 = true := by decide +kernel

def L13 : List (Nat × Nat × Nat) := (3, 0, 3540058259) :: L12

theorem g13 : Good L13 := good_cons _ _ (safeC_sound L12 g12 3 0 3540058259 s12) g12

theorem s13 : safeC L13 3 0 4043374739 = true := by decide +kernel

def L14 : List (Nat × Nat × Nat) := (3, 0, 4043374739) :: L13

theorem g14 : Good L14 := good_cons _ _ (safeC_sound L13 g13 3 0 4043374739 s13) g13

theorem s14 : safeC L14 4 0 3506503827 = true := by decide +kernel

def L15 : List (Nat × Nat × Nat) := (4, 0, 3506503827) :: L14

theorem g15 : Good L15 := good_cons _ _ (safeC_sound L14 g14 4 0 3506503827 s14) g14

theorem s15 : safeC L15 4 0 3506503875 = true := by decide +kernel

def L16 : List (Nat × Nat × Nat) := (4, 0, 3506503875) :: L15

theorem g16 : Good L16 := good_cons _ _ (safeC_sound L15 g15 4 0 3506503875 s15) g15

theorem s16 : safeC L16 4 0 3506634883 = true := by decide +kernel

def L17 : List (Nat × Nat × Nat) := (4, 0, 3506634883) :: L16

theorem g17 : Good L17 := good_cons _ _ (safeC_sound L16 g16 4 0 3506634883 s16) g16

theorem s17 : safeC L17 4 0 3514892419 = true := by decide +kernel

def L18 : List (Nat × Nat × Nat) := (4, 0, 3514892419) :: L17

theorem g18 : Good L18 := good_cons _ _ (safeC_sound L17 g17 4 0 3514892419 s17) g17

theorem s18 : safeC L18 4 0 3540058243 = true := by decide +kernel

def L19 : List (Nat × Nat × Nat) := (4, 0, 3540058243) :: L18

theorem g19 : Good L19 := good_cons _ _ (safeC_sound L18 g18 4 0 3540058243 s18) g18

theorem s19 : safeC L19 3 0 4043374755 = true := by decide +kernel

def L20 : List (Nat × Nat × Nat) := (3, 0, 4043374755) :: L19

theorem g20 : Good L20 := good_cons _ _ (safeC_sound L19 g19 3 0 4043374755 s19) g19

theorem s20 : safeC L20 3 0 4043374787 = true := by decide +kernel

def L21 : List (Nat × Nat × Nat) := (3, 0, 4043374787) :: L20

theorem g21 : Good L21 := good_cons _ _ (safeC_sound L20 g20 3 0 4043374787 s20) g20

theorem s21 : safeC L21 3 0 4043505795 = true := by decide +kernel

def L22 : List (Nat × Nat × Nat) := (3, 0, 4043505795) :: L21

theorem g22 : Good L22 := good_cons _ _ (safeC_sound L21 g21 3 0 4043505795 s21) g21

theorem s22 : safeC L22 3 0 4051763331 = true := by decide +kernel

def L23 : List (Nat × Nat × Nat) := (3, 0, 4051763331) :: L22

theorem g23 : Good L23 := good_cons _ _ (safeC_sound L22 g22 3 0 4051763331 s22) g22

theorem s23 : safeC L23 3 0 4076929155 = true := by decide +kernel

def L24 : List (Nat × Nat × Nat) := (3, 0, 4076929155) :: L23

theorem g24 : Good L24 := good_cons _ _ (safeC_sound L23 g23 3 0 4076929155 s23) g23

theorem s24 : safeC L24 4 0 4043374723 = true := by decide +kernel

def L25 : List (Nat × Nat × Nat) := (4, 0, 4043374723) :: L24

theorem g25 : Good L25 := good_cons _ _ (safeC_sound L24 g24 4 0 4043374723 s24) g24

theorem s25 : safeC L25 5 0 3506503811 = true := by decide +kernel

def L26 : List (Nat × Nat × Nat) := (5, 0, 3506503811) :: L25

theorem g26 : Good L26 := good_cons _ _ (safeC_sound L25 g25 5 0 3506503811 s25) g25

theorem s26 : safeC L26 4 0 3506536707 = true := by decide +kernel

def L27 : List (Nat × Nat × Nat) := (4, 0, 3506536707) :: L26

theorem g27 : Good L27 := good_cons _ _ (safeC_sound L26 g26 4 0 3506536707 s26) g26

theorem s27 : safeC L27 3 0 3506540803 = true := by decide +kernel

def L28 : List (Nat × Nat × Nat) := (3, 0, 3506540803) :: L27

theorem g28 : Good L28 := good_cons _ _ (safeC_sound L27 g27 3 0 3506540803 s27) g27

theorem s28 : safeC L28 3 0 3506548739 = true := by decide +kernel

def L29 : List (Nat × Nat × Nat) := (3, 0, 3506548739) :: L28

theorem g29 : Good L29 := good_cons _ _ (safeC_sound L28 g28 3 0 3506548739 s28) g28

theorem s29 : safeC L29 3 0 3506556931 = true := by decide +kernel

def L30 : List (Nat × Nat × Nat) := (3, 0, 3506556931) :: L29

theorem g30 : Good L30 := good_cons _ _ (safeC_sound L29 g29 3 0 3506556931 s29) g29

theorem s30 : safeC L30 3 0 3506671619 = true := by decide +kernel

def L31 : List (Nat × Nat × Nat) := (3, 0, 3506671619) :: L30

theorem g31 : Good L31 := good_cons _ _ (safeC_sound L30 g30 3 0 3506671619 s30) g30

theorem s31 : safeC L31 3 0 3540094979 = true := by decide +kernel

def L32 : List (Nat × Nat × Nat) := (3, 0, 3540094979) :: L31

theorem g32 : Good L32 := good_cons _ _ (safeC_sound L31 g31 3 0 3540094979 s31) g31

theorem s32 : safeC L32 3 0 4043411459 = true := by decide +kernel

def L33 : List (Nat × Nat × Nat) := (3, 0, 4043411459) :: L32

theorem g33 : Good L33 := good_cons _ _ (safeC_sound L32 g32 3 0 4043411459 s32) g32

theorem s33 : safeC L33 4 0 3506540547 = true := by decide +kernel

def L34 : List (Nat × Nat × Nat) := (4, 0, 3506540547) :: L33

theorem g34 : Good L34 := good_cons _ _ (safeC_sound L33 g33 4 0 3506540547 s33) g33

theorem s34 : safeC L34 4 0 3506552835 = true := by decide +kernel

def L35 : List (Nat × Nat × Nat) := (4, 0, 3506552835) :: L34

theorem g35 : Good L35 := good_cons _ _ (safeC_sound L34 g34 4 0 3506552835 s34) g34

theorem s35 : safeC L35 4 0 3506667523 = true := by decide +kernel

def L36 : List (Nat × Nat × Nat) := (4, 0, 3506667523) :: L35

theorem g36 : Good L36 := good_cons _ _ (safeC_sound L35 g35 4 0 3506667523 s35) g35

theorem s36 : safeC L36 4 0 3540090883 = true := by decide +kernel

def L37 : List (Nat × Nat × Nat) := (4, 0, 3540090883) :: L36

theorem g37 : Good L37 := good_cons _ _ (safeC_sound L36 g36 4 0 3540090883 s36) g36

theorem s37 : safeC L37 3 0 4043407619 = true := by decide +kernel

def L38 : List (Nat × Nat × Nat) := (3, 0, 4043407619) :: L37

theorem g38 : Good L38 := good_cons _ _ (safeC_sound L37 g37 3 0 4043407619 s37) g37

theorem s38 : safeC L38 3 0 4043415555 = true := by decide +kernel

def L39 : List (Nat × Nat × Nat) := (3, 0, 4043415555) :: L38

theorem g39 : Good L39 := good_cons _ _ (safeC_sound L38 g38 3 0 4043415555 s38) g38

theorem s39 : safeC L39 3 0 4043423747 = true := by decide +kernel

def L40 : List (Nat × Nat × Nat) := (3, 0, 4043423747) :: L39

theorem g40 : Good L40 := good_cons _ _ (safeC_sound L39 g39 3 0 4043423747 s39) g39

theorem s40 : safeC L40 3 0 4043538435 = true := by decide +kernel

def L41 : List (Nat × Nat × Nat) := (3, 0, 4043538435) :: L40

theorem g41 : Good L41 := good_cons _ _ (safeC_sound L40 g40 3 0 4043538435 s40) g40

theorem s41 : safeC L41 3 0 4076961795 = true := by decide +kernel

def L42 : List (Nat × Nat × Nat) := (3, 0, 4076961795) :: L41

theorem g42 : Good L42 := good_cons _ _ (safeC_sound L41 g41 3 0 4076961795 s41) g41

theorem s42 : safeC L42 4 0 4043407363 = true := by decide +kernel

def L43 : List (Nat × Nat × Nat) := (4, 0, 4043407363) :: L42

theorem g43 : Good L43 := good_cons _ _ (safeC_sound L42 g42 4 0 4043407363 s42) g42

theorem s43 : safeC L43 5 0 3506536451 = true := by decide +kernel

def L44 : List (Nat × Nat × Nat) := (5, 0, 3506536451) :: L43

theorem g44 : Good L44 := good_cons _ _ (safeC_sound L43 g43 5 0 3506536451 s43) g43

theorem s44 : safeC L44 4 0 3506651139 = true := by decide +kernel

def L45 : List (Nat × Nat × Nat) := (4, 0, 3506651139) :: L44

theorem g45 : Good L45 := good_cons _ _ (safeC_sound L44 g44 4 0 3506651139 s44) g44

theorem s45 : safeC L45 4 1 3540189187 = true := by decide +kernel

def L46 : List (Nat × Nat × Nat) := (4, 1, 3540189187) :: L45

theorem g46 : Good L46 := good_cons _ _ (safeC_sound L45 g45 4 1 3540189187 s45) g45

theorem s46 : safeC L46 4 1 4043505667 = true := by decide +kernel

def L47 : List (Nat × Nat × Nat) := (4, 1, 4043505667) :: L46

theorem g47 : Good L47 := good_cons _ _ (safeC_sound L46 g46 4 1 4043505667 s46) g46

theorem s47 : safeC L47 5 1 3506634755 = true := by decide +kernel

def L48 : List (Nat × Nat × Nat) := (5, 1, 3506634755) :: L47

theorem g48 : Good L48 := good_cons _ _ (safeC_sound L47 g47 5 1 3506634755 s47) g47

theorem s48 : safeC L48 4 0 3540058179 = true := by decide +kernel

def L49 : List (Nat × Nat × Nat) := (4, 0, 3540058179) :: L48

theorem g49 : Good L49 := good_cons _ _ (safeC_sound L48 g48 4 0 3540058179 s48) g48

theorem s49 : safeC L49 4 1 4076929027 = true := by decide +kernel

def L50 : List (Nat × Nat × Nat) := (4, 1, 4076929027) :: L49

theorem g50 : Good L50 := good_cons _ _ (safeC_sound L49 g49 4 1 4076929027 s49) g49

theorem s50 : safeC L50 5 1 3540058115 = true := by decide +kernel

def L51 : List (Nat × Nat × Nat) := (5, 1, 3540058115) :: L50

theorem g51 : Good L51 := good_cons _ _ (safeC_sound L50 g50 5 1 3540058115 s50) g50

theorem s51 : safeC L51 5 1 4043374595 = true := by decide +kernel

def L52 : List (Nat × Nat × Nat) := (5, 1, 4043374595) :: L51

theorem g52 : Good L52 := good_cons _ _ (safeC_sound L51 g51 5 1 4043374595 s51) g51

theorem s52 : safeC L52 6 1 3506503683 = true := by decide +kernel

def L53 : List (Nat × Nat × Nat) := (6, 1, 3506503683) :: L52

theorem g53 : Good L53 := good_cons _ _ (safeC_sound L52 g52 6 1 3506503683 s52) g52

theorem s53 : safeC L53 4 0 3506503821 = true := by decide +kernel

def L54 : List (Nat × Nat × Nat) := (4, 0, 3506503821) :: L53

theorem g54 : Good L54 := good_cons _ _ (safeC_sound L53 g53 4 0 3506503821 s53) g53

theorem s54 : safeC L54 4 0 3506536461 = true := by decide +kernel

def L55 : List (Nat × Nat × Nat) := (4, 0, 3506536461) :: L54

theorem g55 : Good L55 := good_cons _ _ (safeC_sound L54 g54 4 0 3506536461 s54) g54

theorem s55 : safeC L55 4 1 3506765837 = true := by decide +kernel

def L56 : List (Nat × Nat × Nat) := (4, 1, 3506765837) :: L55

theorem g56 : Good L56 := good_cons _ _ (safeC_sound L55 g55 4 1 3506765837 s55) g55

theorem s56 : safeC L56 4 1 3507027981 = true := by decide +kernel

def L57 : List (Nat × Nat × Nat) := (4, 1, 3507027981) :: L56

theorem g57 : Good L57 := good_cons _ _ (safeC_sound L56 g56 4 1 3507027981 s56) g56

theorem s57 : safeC L57 4 1 3573612557 = true := by decide +kernel

def L58 : List (Nat × Nat × Nat) := (4, 1, 3573612557) :: L57

theorem g58 : Good L58 := good_cons _ _ (safeC_sound L57 g57 4 1 3573612557 s57) g57

theorem s58 : safeC L58 4 1 3640721421 = true := by decide +kernel

def L59 : List (Nat × Nat × Nat) := (4, 1, 3640721421) :: L58

theorem g59 : Good L59 := good_cons _ _ (safeC_sound L58 g58 4 1 3640721421 s58) g58

theorem s59 : safeC L59 4 0 4043374605 = true := by decide +kernel

def L60 : List (Nat × Nat × Nat) := (4, 0, 4043374605) :: L59

theorem g60 : Good L60 := good_cons _ _ (safeC_sound L59 g59 4 0 4043374605 s59) g59

theorem s60 : safeC L60 5 1 3506503693 = true := by decide +kernel

def L61 : List (Nat × Nat × Nat) := (5, 1, 3506503693) :: L60

theorem g61 : Good L61 := good_cons _ _ (safeC_sound L60 g60 5 1 3506503693 s60) g60

theorem s61 : safeC L61 4 0 3506503833 = true := by decide +kernel

def L62 : List (Nat × Nat × Nat) := (4, 0, 3506503833) :: L61

theorem g62 : Good L62 := good_cons _ _ (safeC_sound L61 g61 4 0 3506503833 s61) g61

theorem s62 : safeC L62 4 0 3506503881 = true := by decide +kernel

def L63 : List (Nat × Nat × Nat) := (4, 0, 3506503881) :: L62

theorem g63 : Good L63 := good_cons _ _ (safeC_sound L62 g62 4 0 3506503881 s62) g62

theorem s63 : safeC L63 4 0 3507028105 = true := by decide +kernel

def L64 : List (Nat × Nat × Nat) := (4, 0, 3507028105) :: L63

theorem g64 : Good L64 := good_cons _ _ (safeC_sound L63 g63 4 0 3507028105 s63) g63

theorem s64 : safeC L64 4 0 3514892425 = true := by decide +kernel

def L65 : List (Nat × Nat × Nat) := (4, 0, 3514892425) :: L64

theorem g65 : Good L65 := good_cons _ _ (safeC_sound L64 g64 4 0 3514892425 s64) g64

theorem s65 : safeC L65 4 0 3640721545 = true := by decide +kernel

def L66 : List (Nat × Nat × Nat) := (4, 0, 3640721545) :: L65

theorem g66 : Good L66 := good_cons _ _ (safeC_sound L65 g65 4 0 3640721545 s65) g65

theorem s66 : safeC L66 5 0 3506503817 = true := by decide +kernel

def L67 : List (Nat × Nat × Nat) := (5, 0, 3506503817) :: L66

theorem g67 : Good L67 := good_cons _ _ (safeC_sound L66 g66 5 0 3506503817 s66) g66

theorem s67 : safeC L67 4 0 3506536713 = true := by decide +kernel

def L68 : List (Nat × Nat × Nat) := (4, 0, 3506536713) :: L67

theorem g68 : Good L68 := good_cons _ _ (safeC_sound L67 g67 4 0 3506536713 s67) g67

theorem s68 : safeC L68 4 0 3506540553 = true := by decide +kernel

def L69 : List (Nat × Nat × Nat) := (4, 0, 3506540553) :: L68

theorem g69 : Good L69 := good_cons _ _ (safeC_sound L68 g68 4 0 3506540553 s68) g68

theorem s69 : safeC L69 4 0 3506552841 = true := by decide +kernel

def L70 : List (Nat × Nat × Nat) := (4, 0, 3506552841) :: L69

theorem g70 : Good L70 := good_cons _ _ (safeC_sound L69 g69 4 0 3506552841 s69) g69

theorem s70 : safeC L70 4 0 3507060745 = true := by decide +kernel

def L71 : List (Nat × Nat × Nat) := (4, 0, 3507060745) :: L70

theorem g71 : Good L71 := good_cons _ _ (safeC_sound L70 g70 4 0 3507060745 s70) g70

theorem s71 : safeC L71 4 0 3640754185 = true := by decide +kernel

def L72 : List (Nat × Nat × Nat) := (4, 0, 3640754185) :: L71

theorem g72 : Good L72 := good_cons _ _ (safeC_sound L71 g71 4 0 3640754185 s71) g71

theorem s72 : safeC L72 5 0 3506536457 = true := by decide +kernel

def L73 : List (Nat × Nat × Nat) := (5, 0, 3506536457) :: L72

theorem g73 : Good L73 := good_cons _ _ (safeC_sound L72 g72 5 0 3506536457 s72) g72

theorem s73 : safeC L73 4 0 3507032073 = true := by decide +kernel

def L74 : List (Nat × Nat × Nat) := (4, 0, 3507032073) :: L73

theorem g74 : Good L74 := good_cons _ _ (safeC_sound L73 g73 4 0 3507032073 s73) g73

theorem s74 : safeC L74 4 1 3507290121 = true := by decide +kernel

def L75 : List (Nat × Nat × Nat) := (4, 1, 3507290121) :: L74

theorem g75 : Good L75 := good_cons _ _ (safeC_sound L74 g74 4 1 3507290121 s74) g74

theorem s75 : safeC L75 4 1 3641245705 = true := by decide +kernel

def L76 : List (Nat × Nat × Nat) := (4, 1, 3641245705) :: L75

theorem g76 : Good L76 := good_cons _ _ (safeC_sound L75 g75 4 1 3641245705 s75) g75

theorem s76 : safeC L76 5 1 3507027977 = true := by decide +kernel

def L77 : List (Nat × Nat × Nat) := (5, 1, 3507027977) :: L76

theorem g77 : Good L77 := good_cons _ _ (safeC_sound L76 g76 5 1 3507027977 s76) g76

theorem s77 : safeC L77 5 1 3640721417 = true := by decide +kernel

def L78 : List (Nat × Nat × Nat) := (5, 1, 3640721417) :: L77

theorem g78 : Good L78 := good_cons _ _ (safeC_sound L77 g77 5 1 3640721417 s77) g77

theorem s78 : safeC L78 6 1 3506503689 = true := by decide +kernel

def L79 : List (Nat × Nat × Nat) := (6, 1, 3506503689) :: L78

theorem g79 : Good L79 := good_cons _ _ (safeC_sound L78 g78 6 1 3506503689 s78) g78

theorem s79 : safeC L79 3 0 3506503897 = true := by decide +kernel

def L80 : List (Nat × Nat × Nat) := (3, 0, 3506503897) :: L79

theorem g80 : Good L80 := good_cons _ _ (safeC_sound L79 g79 3 0 3506503897 s79) g79

theorem s80 : safeC L80 3 0 3506536657 = true := by decide +kernel

def L81 : List (Nat × Nat × Nat) := (3, 0, 3506536657) :: L80

theorem g81 : Good L81 := good_cons _ _ (safeC_sound L80 g80 3 0 3506536657 s80) g80

theorem s81 : safeC L81 3 1 3507552465 = true := by decide +kernel

def L82 : List (Nat × Nat × Nat) := (3, 1, 3507552465) :: L81

theorem g82 : Good L82 := good_cons _ _ (safeC_sound L81 g81 3 1 3507552465 s81) g81

theorem s82 : safeC L82 3 1 3510698193 = true := by decide +kernel

def L83 : List (Nat × Nat × Nat) := (3, 1, 3510698193) :: L82

theorem g83 : Good L83 := good_cons _ _ (safeC_sound L82 g82 3 1 3510698193 s82) g82

theorem s83 : safeC L83 3 1 3514892497 = true := by decide +kernel

def L84 : List (Nat × Nat × Nat) := (3, 1, 3514892497) :: L83

theorem g84 : Good L84 := good_cons _ _ (safeC_sound L83 g83 3 1 3514892497 s83) g83

theorem s84 : safeC L84 3 0 3540058321 = true := by decide +kernel

def L85 : List (Nat × Nat × Nat) := (3, 0, 3540058321) :: L84

theorem g85 : Good L85 := good_cons _ _ (safeC_sound L84 g84 3 0 3540058321 s84) g84

theorem s85 : safeC L85 3 0 3640721617 = true := by decide +kernel

def L86 : List (Nat × Nat × Nat) := (3, 0, 3640721617) :: L85

theorem g86 : Good L86 := good_cons _ _ (safeC_sound L85 g85 3 0 3640721617 s85) g85

theorem s86 : safeC L86 4 1 3506503889 = true := by decide +kernel

def L87 : List (Nat × Nat × Nat) := (4, 1, 3506503889) :: L86

theorem g87 : Good L87 := good_cons _ _ (safeC_sound L86 g86 4 1 3506503889 s86) g86

theorem s87 : safeC L87 3 0 3506536849 = true := by decide +kernel

def L88 : List (Nat × Nat × Nat) := (3, 0, 3506536849) :: L87

theorem g88 : Good L88 := good_cons _ _ (safeC_sound L87 g87 3 0 3506536849 s87) g87

theorem s88 : safeC L88 3 0 3506540689 = true := by decide +kernel

def L89 : List (Nat × Nat × Nat) := (3, 0, 3506540689) :: L88

theorem g89 : Good L89 := good_cons _ _ (safeC_sound L88 g88 3 0 3506540689 s88) g88

theorem s89 : safeC L89 3 0 3506552977 = true := by decide +kernel

def L90 : List (Nat × Nat × Nat) := (3, 0, 3506552977) :: L89

theorem g90 : Good L90 := good_cons _ _ (safeC_sound L89 g89 3 0 3506552977 s89) g89

theorem s90 : safeC L90 3 0 3507585169 = true := by decide +kernel

def L91 : List (Nat × Nat × Nat) := (3, 0, 3507585169) :: L90

theorem g91 : Good L91 := good_cons _ _ (safeC_sound L90 g90 3 0 3507585169 s90) g90

theorem s91 : safeC L91 3 0 3514925201 = true := by decide +kernel

def L92 : List (Nat × Nat × Nat) := (3, 0, 3514925201) :: L91

theorem g92 : Good L92 := good_cons _ _ (safeC_sound L91 g91 3 0 3514925201 s91) g91

theorem s92 : safeC L92 4 0 3506536593 = true := by decide +kernel

def L93 : List (Nat × Nat × Nat) := (4, 0, 3506536593) :: L92

theorem g93 : Good L93 := good_cons _ _ (safeC_sound L92 g92 4 0 3506536593 s92) g92

theorem s93 : safeC L93 4 1 3507552401 = true := by decide +kernel

def L94 : List (Nat × Nat × Nat) := (4, 1, 3507552401) :: L93

theorem g94 : Good L94 := good_cons _ _ (safeC_sound L93 g93 4 1 3507552401 s93) g93

theorem s94 : safeC L94 4 1 3514892433 = true := by decide +kernel

def L95 : List (Nat × Nat × Nat) := (4, 1, 3514892433) :: L94

theorem g95 : Good L95 := good_cons _ _ (safeC_sound L94 g94 4 1 3514892433 s94) g94

theorem s95 : safeC L95 4 0 3640721553 = true := by decide +kernel

def L96 : List (Nat × Nat × Nat) := (4, 0, 3640721553) :: L95

theorem g96 : Good L96 := good_cons _ _ (safeC_sound L95 g95 4 0 3640721553 s95) g95

theorem s96 : safeC L96 5 1 3506503825 = true := by decide +kernel

def L97 : List (Nat × Nat × Nat) := (5, 1, 3506503825) :: L96

theorem g97 : Good L97 := good_cons _ _ (safeC_sound L96 g96 5 1 3506503825 s96) g96

theorem s97 : safeC L97 4 0 3506536641 = true := by decide +kernel

def L98 : List (Nat × Nat × Nat) := (4, 0, 3506536641) :: L97

theorem g98 : Good L98 := good_cons _ _ (safeC_sound L97 g97 4 0 3506536641 s97) g97

theorem s98 : safeC L98 4 1 3510698177 = true := by decide +kernel

def L99 : List (Nat × Nat × Nat) := (4, 1, 3510698177) :: L98

theorem g99 : Good L99 := good_cons _ _ (safeC_sound L98 g98 4 1 3510698177 s98) g98

theorem s99 : safeC L99 4 1 3514892481 = true := by decide +kernel

def L100 : List (Nat × Nat × Nat) := (4, 1, 3514892481) :: L99

theorem g100 : Good L100 := good_cons _ _ (safeC_sound L99 g99 4 1 3514892481 s99) g99

theorem s100 : safeC L100 4 0 3540058305 = true := by decide +kernel

def L101 : List (Nat × Nat × Nat) := (4, 0, 3540058305) :: L100

theorem g101 : Good L101 := good_cons _ _ (safeC_sound L100 g100 4 0 3540058305 s100) g100

theorem s101 : safeC L101 5 1 3506503873 = true := by decide +kernel

def L102 : List (Nat × Nat × Nat) := (5, 1, 3506503873) :: L101

theorem g102 : Good L102 := good_cons _ _ (safeC_sound L101 g101 5 1 3506503873 s101) g101

theorem s102 : safeC L102 4 0 3506536833 = true := by decide +kernel

def L103 : List (Nat × Nat × Nat) := (4, 0, 3506536833) :: L102

theorem g103 : Good L103 := good_cons _ _ (safeC_sound L102 g102 4 0 3506536833 s102) g102

theorem s103 : safeC L103 4 0 3506540673 = true := by decide +kernel

def L104 : List (Nat × Nat × Nat) := (4, 0, 3506540673) :: L103

theorem g104 : Good L104 := good_cons _ _ (safeC_sound L103 g103 4 0 3506540673 s103) g103

theorem s104 : safeC L104 4 0 3506552961 = true := by decide +kernel

def L105 : List (Nat × Nat × Nat) := (4, 0, 3506552961) :: L104

theorem g105 : Good L105 := good_cons _ _ (safeC_sound L104 g104 4 0 3506552961 s104) g104

theorem s105 : safeC L105 4 0 3514925185 = true := by decide +kernel

def L106 : List (Nat × Nat × Nat) := (4, 0, 3514925185) :: L105

theorem g106 : Good L106 := good_cons _ _ (safeC_sound L105 g105 4 0 3514925185 s105) g105

theorem s106 : safeC L106 5 0 3506536577 = true := by decide +kernel

def L107 : List (Nat × Nat × Nat) := (5, 0, 3506536577) :: L106

theorem g107 : Good L107 := good_cons _ _ (safeC_sound L106 g106 5 0 3506536577 s106) g106

theorem s107 : safeC L107 4 0 3514892673 = true := by decide +kernel

def L108 : List (Nat × Nat × Nat) := (4, 0, 3514892673) :: L107

theorem g108 : Good L108 := good_cons _ _ (safeC_sound L107 g107 4 0 3514892673 s107) g107

theorem s108 : safeC L108 4 1 3515940993 = true := by decide +kernel

def L109 : List (Nat × Nat × Nat) := (4, 1, 3515940993) :: L108

theorem g109 : Good L109 := good_cons _ _ (safeC_sound L108 g108 4 1 3515940993 s108) g108

theorem s109 : safeC L109 4 1 3519086721 = true := by decide +kernel

def L110 : List (Nat × Nat × Nat) := (4, 1, 3519086721) :: L109

theorem g110 : Good L110 := good_cons _ _ (safeC_sound L109 g109 4 1 3519086721 s109) g109

theorem s110 : safeC L110 5 1 3514892417 = true := by decide +kernel

def L111 : List (Nat × Nat × Nat) := (5, 1, 3514892417) :: L110

theorem g111 : Good L111 := good_cons _ _ (safeC_sound L110 g110 5 1 3514892417 s110) g110

theorem s111 : safeC L111 6 1 3506503809 = true := by decide +kernel

def L112 : List (Nat × Nat × Nat) := (6, 1, 3506503809) :: L111

theorem g112 : Good L112 := good_cons _ _ (safeC_sound L111 g111 6 1 3506503809 s111) g111

theorem s112 : safeC L112 4 1 3506540801 = true := by decide +kernel

def L113 : List (Nat × Nat × Nat) := (4, 1, 3506540801) :: L112

theorem g113 : Good L113 := good_cons _ _ (safeC_sound L112 g112 4 1 3506540801 s112) g112

theorem s113 : safeC L113 4 1 3506553089 = true := by decide +kernel

def L114 : List (Nat × Nat × Nat) := (4, 1, 3506553089) :: L113

theorem g114 : Good L114 := good_cons _ _ (safeC_sound L113 g113 4 1 3506553089 s113) g113

theorem s114 : safeC L114 4 0 3514925313 = true := by decide +kernel

def L115 : List (Nat × Nat × Nat) := (4, 0, 3514925313) :: L114

theorem g115 : Good L115 := good_cons _ _ (safeC_sound L114 g114 4 0 3514925313 s114) g114

theorem s115 : safeC L115 5 1 3506536705 = true := by decide +kernel

def L116 : List (Nat × Nat × Nat) := (5, 1, 3506536705) :: L115

theorem g116 : Good L116 := good_cons _ _ (safeC_sound L115 g115 5 1 3506536705 s115) g115

theorem s116 : safeC L116 4 1 3506556929 = true := by decide +kernel

def L117 : List (Nat × Nat × Nat) := (4, 1, 3506556929) :: L116

theorem g117 : Good L117 := good_cons _ _ (safeC_sound L116 g116 4 1 3506556929 s116) g116

theorem s117 : safeC L117 4 0 3507064833 = true := by decide +kernel

def L118 : List (Nat × Nat × Nat) := (4, 0, 3507064833) :: L117

theorem g118 : Good L118 := good_cons _ _ (safeC_sound L117 g117 4 0 3507064833 s117) g117

theorem s118 : safeC L118 5 1 3506540545 = true := by decide +kernel

def L119 : List (Nat × Nat × Nat) := (5, 1, 3506540545) :: L118

theorem g119 : Good L119 := good_cons _ _ (safeC_sound L118 g118 5 1 3506540545 s118) g118

theorem s119 : safeC L119 5 1 3506552833 = true := by decide +kernel

def L120 : List (Nat × Nat × Nat) := (5, 1, 3506552833) :: L119

theorem g120 : Good L120 := good_cons _ _ (safeC_sound L119 g119 5 1 3506552833 s119) g119

theorem s120 : safeC L120 6 1 3506536449 = true := by decide +kernel

def L121 : List (Nat × Nat × Nat) := (6, 1, 3506536449) :: L120

theorem g121 : Good L121 := good_cons _ _ (safeC_sound L120 g120 6 1 3506536449 s120) g120

theorem s121 : safeC L121 7 2 3506503681 = true := by decide +kernel

def L122 : List (Nat × Nat × Nat) := (7, 2, 3506503681) :: L121

theorem g122 : Good L122 := good_cons _ _ (safeC_sound L121 g121 7 2 3506503681 s121) g121

theorem search : safe 7 2 S0 = true := safeC_sound L122 g122 7 2 S0 (by decide +kernel)

theorem main : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
    PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 7 ∧
    ∀ t : Fin 5,
      let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
      let w := D.wires xs
      w.getD p.val false = (4 : Nat).testBit t.val ∧
      w.getD q.val false = (12 : Nat).testBit t.val ∧
      w.getD r.val false = (29 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, _, hnot, hsize, hall⟩
  have hok : ∀ g ∈ D.gates, okG g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    simpa using h1
  obtain ⟨S', hm, hb⟩ := core D.gates (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) S0 7 2 rfl rfl rfl rfl
    init_ok (by decide) (by decide) search hsize hnot hok
  have hp : ∀ t, t < 5 → (D.wires (xs t)).getD p.val false = tA.testBit t := fun t ht => (hall ⟨t, ht⟩).1
  have hq : ∀ t, t < 5 → (D.wires (xs t)).getD q.val false = tB.testBit t := fun t ht => (hall ⟨t, ht⟩).2.1
  have hr : ∀ t, t < 5 → (D.wires (xs t)).getD r.val false = tC.testBit t := fun t ht => (hall ⟨t, ht⟩).2.2
  have ea : V (D.wires (xs 0)) (D.wires (xs 1)) (D.wires (xs 2)) (D.wires (xs 3)) (D.wires (xs 4)) p.val = tA := by
    unfold V
    rw [hp 0 (by decide), hp 1 (by decide), hp 2 (by decide), hp 3 (by decide), hp 4 (by decide)]
    decide
  have eb : V (D.wires (xs 0)) (D.wires (xs 1)) (D.wires (xs 2)) (D.wires (xs 3)) (D.wires (xs 4)) q.val = tB := by
    unfold V
    rw [hq 0 (by decide), hq 1 (by decide), hq 2 (by decide), hq 3 (by decide), hq 4 (by decide)]
    decide
  have ec : V (D.wires (xs 0)) (D.wires (xs 1)) (D.wires (xs 2)) (D.wires (xs 3)) (D.wires (xs 4)) r.val = tC := by
    unfold V
    rw [hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide), hr 4 (by decide)]
    decide
  have ba := hb p.val
  have bb := hb q.val
  have bc := hb r.val
  change S'.testBit (V (D.wires (xs 0)) (D.wires (xs 1)) (D.wires (xs 2)) (D.wires (xs 3)) (D.wires (xs 4)) p.val) = true at ba
  change S'.testBit (V (D.wires (xs 0)) (D.wires (xs 1)) (D.wires (xs 2)) (D.wires (xs 3)) (D.wires (xs 4)) q.val) = true at bb
  change S'.testBit (V (D.wires (xs 0)) (D.wires (xs 1)) (D.wires (xs 2)) (D.wires (xs 3)) (D.wires (xs 4)) r.val) = true at bc
  rw [ea] at ba
  rw [eb] at bb
  rw [ec] at bc
  apply hm
  unfold miss
  rw [ba, bb, bc]
  rfl

end failPart

theorem failPart : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
    PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 7 ∧
    ∀ t : Fin 5,
      let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
      let w := D.wires xs
      w.getD p.val false = (4 : Nat).testBit t.val ∧
      w.getD q.val false = (12 : Nat).testBit t.val ∧
      w.getD r.val false = (29 : Nat).testBit t.val) :=
  failPart.main

end PEqualNP.Outside.L_meta_53150

theorem PEqualNP.Outside.L_meta_53150 : 
    let fits := fun (b : Nat) =>
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
        PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
        PEqualNP.NotBracket.notCount D ≤ b ∧ D.size ≤ 7 ∧
        ∀ t : Fin 5,
          let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
          let w := D.wires xs
          w.getD p.val false = (4 : Nat).testBit t.val ∧
          w.getD q.val false = (12 : Nat).testBit t.val ∧
          w.getD r.val false = (29 : Nat).testBit t.val
    fits 3 ∧ ¬ fits 2 :=
  ⟨PEqualNP.Outside.L_meta_53150.fitPart, PEqualNP.Outside.L_meta_53150.failPart⟩
