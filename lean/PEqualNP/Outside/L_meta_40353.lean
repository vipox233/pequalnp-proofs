import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40353

open PEqualNP.CircuitLowerBounds

def nl (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def chiF (u : Nat → Bool) (i : Nat) : Bool := xor (u i) (!(u (i+1)) && u (i+2))

def z (b : Bool) : ZMod 2 := if b then 1 else 0

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => simp [W_snoc, ih]; omega

lemma W_stable (gs hs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length + gs.length) :
    (W (gs ++ hs) x).getD i false = (W gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, W_snoc, List.getD_append _ _ _ _ (by rw [W_length]; simp; omega)]
    exact ih

lemma W_gate (pre : List Gate) (g : Gate) (post : List Gate) (x : List Bool) :
    (W (pre ++ g :: post) x).getD (x.length + pre.length) false
      = g.op.eval (g.inputs.map fun i => (W pre x).getD i false) := by
  have e : pre ++ g :: post = (pre ++ [g]) ++ post := by simp
  rw [e, W_stable _ _ _ _ (by simp), W_snoc,
    List.getD_append_right _ _ _ _ (by rw [W_length])]
  simp [W_length]

lemma W_at (gs : List Gate) (x : List Bool) (p : Nat) (g : Gate) (hg : gs[p]? = some g)
    (hr : ∀ i ∈ g.inputs, i < x.length + p) :
    (W gs x).getD (x.length + p) false = g.op.eval (g.inputs.map fun i => (W gs x).getD i false) := by
  obtain ⟨hp, hge⟩ := List.getElem?_eq_some_iff.1 hg
  have hsplit : gs.take p ++ g :: gs.drop (p+1) = gs := by
    rw [← hge, List.getElem_cons_drop, List.take_append_drop]
  have h1 := W_gate (gs.take p) g (gs.drop (p+1)) x
  rw [hsplit, List.length_take, min_eq_left hp.le] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have h2 := W_stable (gs.take p) (gs.drop p) x i
    (by have := hr i hi; rw [List.length_take, min_eq_left hp.le]; exact this)
  rw [List.take_append_drop] at h2
  exact h2.symm

lemma aff1 : ∀ a b x : Bool, z (if x then b else a) = z a + (z b + z a) * z x := by decide

lemma aff2 : ∀ a b c d x y : Bool, xor (xor a b) (xor c d) = false →
    z (if x then (if y then d else c) else (if y then b else a))
      = z a + (z c + z a) * z x + (z b + z a) * z y := by decide

lemma span_wires {U : Type} (S0 : Set (U → ZMod 2)) (inp : U → List Bool) (m : Nat)
    (hm : ∀ u, (inp u).length = m)
    (hin : ∀ i, (fun u => z ((inp u).getD i false)) ∈ Submodule.span (ZMod 2) S0)
    (h1 : (1 : U → ZMod 2) ∈ Submodule.span (ZMod 2) S0)
    (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ L : List (U → ZMod 2), L.length ≤ gs.countP nl ∧
      ∀ i, (fun u => z ((W gs (inp u)).getD i false))
        ∈ Submodule.span (ZMod 2) (S0 ∪ {f | f ∈ L}) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], by simp, fun i => ?_⟩
    exact Submodule.span_mono Set.subset_union_left (hin i)
  | append_singleton gs g ih =>
    obtain ⟨L, hL, hw⟩ := ih (fun g' hg' => hg g' (List.mem_append_left _ hg'))
    have hg2 : g.inputs.length ≤ 2 := hg g (by simp)
    set f : U → ZMod 2 := fun u => z (g.op.eval (g.inputs.map fun i => (W gs (inp u)).getD i false))
      with hf
    have hnew : ∀ i, (fun u => z ((W (gs ++ [g]) (inp u)).getD i false))
        = if i = m + gs.length then f else (fun u => z ((W gs (inp u)).getD i false)) := by
      intro i
      split
      · next h =>
        funext u
        rw [W_snoc, List.getD_append_right _ _ _ _ (by rw [W_length, hm]; omega)]
        simp [W_length, hm, h, hf]
      · next h =>
        funext u
        rcases lt_or_gt_of_ne h with h' | h'
        · rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_length, hm]; exact h')]
        · rw [List.getD_eq_default _ _ (by rw [W_length, hm]; simp; omega),
            List.getD_eq_default _ _ (by rw [W_length, hm]; omega)]
    by_cases hn : nl g = true
    · refine ⟨L ++ [f], by simp [List.countP_append, hn]; omega, fun i => ?_⟩
      rw [hnew]
      split
      · exact Submodule.subset_span (Or.inr (by simp))
      · refine Submodule.span_mono (Set.union_subset_union_right _ ?_) (hw i)
        intro a ha
        exact List.mem_append_left _ ha
    · refine ⟨L, by simp [List.countP_append, hn]; omega, fun i => ?_⟩
      rw [hnew]
      split
      swap
      · exact hw i
      have one : (1 : U → ZMod 2) ∈ Submodule.span (ZMod 2) (S0 ∪ {f | f ∈ L}) :=
        Submodule.span_mono Set.subset_union_left h1
      match hgi : g.inputs, hg2 with
      | [], _ =>
        have e : f = z (g.op.eval []) • (1 : U → ZMod 2) := by
          funext u; simp [hf, hgi]
        rw [e]; exact Submodule.smul_mem _ _ one
      | [a], _ =>
        have e : f = z (g.op.eval [false]) • (1 : U → ZMod 2)
            + (z (g.op.eval [true]) + z (g.op.eval [false]))
              • (fun u => z ((W gs (inp u)).getD a false)) := by
          funext u
          have := aff1 (g.op.eval [false]) (g.op.eval [true]) ((W gs (inp u)).getD a false)
          have e2 : ∀ x : Bool, (if x then g.op.eval [true] else g.op.eval [false]) = g.op.eval [x] := by
            intro x; cases x <;> rfl
          rw [e2] at this
          simpa [hf, hgi] using this
        rw [e]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ one) (Submodule.smul_mem _ _ (hw a))
      | [a, b], _ =>
        have hpar : xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
            (xor (g.op.eval [true,false]) (g.op.eval [true,true])) = false := by
          simpa [nl, hgi] using hn
        have e : f = z (g.op.eval [false,false]) • (1 : U → ZMod 2)
            + (z (g.op.eval [true,false]) + z (g.op.eval [false,false]))
              • (fun u => z ((W gs (inp u)).getD a false))
            + (z (g.op.eval [false,true]) + z (g.op.eval [false,false]))
              • (fun u => z ((W gs (inp u)).getD b false)) := by
          funext u
          have := aff2 _ _ _ _ ((W gs (inp u)).getD a false) ((W gs (inp u)).getD b false) hpar
          have e2 : ∀ x y : Bool,
              (if x then (if y then g.op.eval [true,true] else g.op.eval [true,false])
                else (if y then g.op.eval [false,true] else g.op.eval [false,false]))
                = g.op.eval [x,y] := by
            intro x y; cases x <;> cases y <;> rfl
          rw [e2] at this
          simpa [hf, hgi] using this
        rw [e]
        exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ one)
          (Submodule.smul_mem _ _ (hw a))) (Submodule.smul_mem _ _ (hw b))
      | a :: b :: c :: l, h => simp at h

lemma flat_length (n h : Nat) (f : Fin n → Fin h → Bool) :
    (List.ofFn (fun j => List.ofFn (f j))).flatten.length = n*h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, ih (fun j => f j.succ)]
    simp [Nat.succ_mul]; omega

lemma flat_get (n h : Nat) (f : Fin n → Fin h → Bool) (j : Fin n) (i : Fin h) :
    (List.ofFn (fun j => List.ofFn (f j))).flatten.getD (j.val*h+i.val) false = f j i := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    cases j using Fin.cases with
    | zero =>
      rw [List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, i.isLt]
    | succ j =>
      have e : (j.succ).val * h + i.val = h + (j.val*h+i.val) := by simp [Nat.succ_mul]; omega
      rw [e, List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      exact ih (fun j => f j.succ) j

lemma quadB : ∀ p q r s : Bool, (p && q) = false → (p && r) = false → (p && s) = false →
    (q && r) = false → (q && s) = false → (r && s) = false →
    z (xor (p || q) (!(r || p) && (s || r)))
      = z (xor p (!r && s)) + z (xor q (!p && r)) + z r := by decide

lemma quad (k m : Nat) :
    z (chiF (fun l => decide (k+1 = l) || decide (k+2 = l)) m)
      = z (chiF (fun l => decide (k+1 = l)) m) + z (chiF (fun l => decide (k+2 = l)) m)
        + z (decide (m = k)) := by
  unfold chiF
  have e1 : decide (k+2 = m+1) = decide (k+1 = m) := decide_eq_decide.2 (by omega)
  have e2 : decide (k+1 = m+2) = decide (k = m+1) := decide_eq_decide.2 (by omega)
  have e3 : decide (k+2 = m+2) = decide (m = k) := decide_eq_decide.2 (by omega)
  have e4 : decide (k+1 = m+1) = decide (m = k) := decide_eq_decide.2 (by omega)
  simp only [e1, e2, e3, e4]
  apply quadB <;> simp <;> omega

def bit {n h : Nat} (u : Fin n → Fin (2^(h+2))) (j i : Nat) : Bool :=
  if hj : j < n then (u ⟨j, hj⟩).val.testBit i else false

def sideF (n h b : Nat) (u : Fin n → Fin (2^(h+2))) (k : Fin b) : Bool :=
  if k.val < 2*n then bit u (k.val/2) (h + k.val % 2)
  else bit u ((k.val - 2*n)/h) (h - 1 - (k.val - 2*n) % h)

def tapN (n h b j i : Nat) : Nat :=
  if i < h then n*h+b + 4*(j*h + (h-1-i)) + 3 else n*h + 2*j + (i-h)

def blk (n h b q : Nat) : List Gate :=
  if q < b - 2*n then List.replicate 4 ⟨.and, [n*h + (2*n+q)]⟩
  else
    [⟨.not, [tapN n h b (q/h) (h-1-q%h+1)]⟩,
     ⟨.and, [n*h+b+4*q, tapN n h b (q/h) (h-1-q%h+2)]⟩,
     ⟨.mod 2, [n*h+b+4*q+1, (q/h)*h + (h-1-q%h)]⟩,
     ⟨.not, [n*h+b+4*q+2]⟩]

lemma blk_length (n h b q : Nat) : (blk n h b q).length = 4 := by
  unfold blk; split <;> simp

lemma blk_count (n h b q : Nat) : (blk n h b q).countP nl = if q < b - 2*n then 0 else 1 := by
  unfold blk; split
  · simp [nl, List.replicate]
  · simp [nl, List.countP_cons, GateOp.eval]

def gs (n h b m : Nat) : List Gate := (List.range m).flatMap (blk n h b)

lemma gs_succ (n h b m : Nat) : gs n h b (m+1) = gs n h b m ++ blk n h b m := by
  simp [gs, List.range_succ, List.flatMap_append]

lemma gs_length (n h b m : Nat) : (gs n h b m).length = 4*m := by
  induction m with
  | zero => simp [gs]
  | succ m ih => rw [gs_succ, List.length_append, ih, blk_length]; omega

lemma gs_count (n h b m : Nat) : (gs n h b m).countP nl = m - (b - 2*n) := by
  induction m with
  | zero => simp [gs]
  | succ m ih => rw [gs_succ, List.countP_append, ih, blk_count]; split <;> omega

lemma gs_get (n h b m q k : Nat) (hq : q < m) (hk : k < 4) :
    (gs n h b m)[4*q+k]? = (blk n h b q)[k]? := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [gs_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h' | h'
    · rw [List.getElem?_append_left (by rw [gs_length]; omega)]
      exact ih h'
    · subst h'
      rw [List.getElem?_append_right (by rw [gs_length]; omega), gs_length]
      congr 1; omega

lemma block_facts (n h q : Nat) (hq : q < n*h) :
    0 < h ∧ q/h < n ∧ h-1-q%h < h ∧ (q/h)*h + (h-1-(h-1-q%h)) = q := by
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0; simp at hq
    · exact h0
  have hm : q % h < h := Nat.mod_lt _ hh
  refine ⟨hh, (Nat.div_lt_iff_lt_mul hh).2 hq, by omega, ?_⟩
  have e : h-1-(h-1-q%h) = q % h := by omega
  rw [e, Nat.mul_comm]; exact Nat.div_add_mod q h

lemma tap_lt (n h b q i : Nat) (hb : 2*n ≤ b) (hq : q < n*h) (d : Nat) (hd : d = 1 ∨ d = 2)
    (hi : i = h-1-q%h) : tapN n h b (q/h) (i+d) < n*h+b+4*q := by
  obtain ⟨hh, hj, hi', hqe⟩ := block_facts n h q hq
  rw [← hi] at hi' hqe
  unfold tapN
  split
  · next hlt =>
    have : (q/h)*h + (h-1-(i+d)) + d = q := by omega
    omega
  · omega

lemma reads (n h b : Nat) (hb : 2*n ≤ b) (q k : Nat) (hq : q < n*h) (hk : k < 4) (g : Gate)
    (hg : (blk n h b q)[k]? = some g) :
    g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < n*h+b+(4*q+k) := by
  have t1 := tap_lt n h b q _ hb hq 1 (Or.inl rfl) rfl
  have t2 := tap_lt n h b q _ hb hq 2 (Or.inr rfl) rfl
  obtain ⟨hh, hj, hi, hqe⟩ := block_facts n h q hq
  have hy : (q/h)*h + (h-1-q%h) < n*h := by
    have : (q/h+1)*h ≤ n*h := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul] at this; omega
  unfold blk at hg
  split at hg
  · next hlt =>
    have : g = ⟨.and, [n*h + (2*n+q)]⟩ := by
      have := List.mem_of_getElem? hg
      exact List.eq_of_mem_replicate this
    subst this
    refine ⟨by simp, ?_⟩
    intro i hi'
    simp only [List.mem_singleton] at hi'
    omega
  · interval_cases k <;> simp at hg <;> subst hg <;>
      refine ⟨by simp, fun i hi' => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    · omega
    · rcases hi' with rfl | rfl <;> omega
    · rcases hi' with rfl | rfl <;> omega
    · omega

lemma notmod : ∀ a e : Bool,
    GateOp.not.eval [(GateOp.mod 2).eval [a, xor e a]] = e := by decide

theorem key (h n b t : Nat) :
    (∃ (side : (Fin n → Fin (2^(h+2))) → Fin b → Bool) (C : Circuit)
        (tap : Fin n → Fin (h+2) → Nat),
      (PEqualNP.MetaComplexity.NestedCover.ReadsBack (n*h+b) C ∧ ∀ g ∈ C.gates, g.inputs.length ≤ 2)
      ∧ C.gates.countP nl ≤ t ∧
      (∀ j i, tap j i < n*h+b+C.gates.length) ∧
      ∀ (u : Fin n → Fin (2^(h+2))),
        ∀ j i, (C.wires ((List.ofFn (fun j : Fin n =>
          List.ofFn (fun i : Fin h => chiF (fun l => (u j).val.testBit l) i))).flatten
            ++ List.ofFn (side u))).getD (tap j i) false = (u j).val.testBit i) ↔
      2*n ≤ b ∧ n*(h+2) ≤ b+t := by
  constructor
  · rintro ⟨side, C, tap, ⟨_, hlen⟩, hcnt, _, hw⟩
    set inp : (Fin n → Fin (2^(h+2))) → List Bool := fun u =>
      (List.ofFn (fun j : Fin n =>
          List.ofFn (fun i : Fin h => chiF (fun l => (u j).val.testBit l) i))).flatten
        ++ List.ofFn (side u) with hinp
    have hinplen : ∀ u, (inp u).length = n*h+b := by
      intro u; simp only [hinp, List.length_append, flat_length, List.length_ofFn]
    have hwW : ∀ u j i, (W C.gates (inp u)).getD (tap j i) false = (u j).val.testBit i := hw
    constructor
    · have inj : Function.Injective (fun u : Fin n → Fin (2^(h+2)) =>
          ((fun (j : Fin n) (i : Fin h) => chiF (fun l => (u j).val.testBit l) i), side u)) := by
        intro u v huv
        simp only [Prod.mk.injEq] at huv
        have e : inp u = inp v := by
          have h1 := huv.1
          simp only [hinp, huv.2]
          congr 2
          exact congrArg (fun f : Fin n → Fin h → Bool =>
            List.ofFn (fun j => List.ofFn (f j))) h1
        funext j
        apply Fin.ext
        apply Nat.eq_of_testBit_eq
        intro k
        by_cases hk : k < h+2
        · rw [← hwW u j ⟨k, hk⟩, ← hwW v j ⟨k, hk⟩, e]
        · have hle : 2^(h+2) ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (u j).isLt hle),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (v j).isLt hle)]
      have hc := Fintype.card_le_of_injective _ inj
      simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hc
      rw [← pow_mul, ← pow_mul, ← pow_add, Nat.pow_le_pow_iff_right (by norm_num)] at hc
      rw [Nat.add_mul] at hc
      omega
    · set yf : Fin n × Fin h → (Fin n → Fin (2^(h+2))) → ZMod 2 :=
        fun q u => z (chiF (fun l => (u q.1).val.testBit l) q.2) with hyf
      set sf : Fin b → (Fin n → Fin (2^(h+2))) → ZMod 2 := fun k u => z (side u k) with hsf
      set S0 : Set ((Fin n → Fin (2^(h+2))) → ZMod 2) :=
        Set.range yf ∪ Set.range sf ∪ {1} with hS0
      have one : (1 : (Fin n → Fin (2^(h+2))) → ZMod 2) ∈ Submodule.span (ZMod 2) S0 :=
        Submodule.subset_span (Or.inr rfl)
      have hin : ∀ i, (fun u => z ((inp u).getD i false)) ∈ Submodule.span (ZMod 2) S0 := by
        intro i
        by_cases h1 : i < n*h
        · obtain ⟨hh, _, _, _⟩ := block_facts n h i h1
          have hj : i/h < n := (Nat.div_lt_iff_lt_mul hh).2 h1
          have hr : i % h < h := Nat.mod_lt _ hh
          have e : (fun u => z ((inp u).getD i false)) = yf (⟨i/h, hj⟩, ⟨i%h, hr⟩) := by
            funext u
            simp only [hinp, hyf]
            rw [List.getD_append _ _ _ _ (by rw [flat_length]; exact h1)]
            have := flat_get n h (fun j i => chiF (fun l => (u j).val.testBit l) i)
              ⟨i/h, hj⟩ ⟨i%h, hr⟩
            have ei : i/h*h + i%h = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i h
            simp only [ei] at this
            rw [this]
          rw [e]; exact Submodule.subset_span (Or.inl (Or.inl ⟨_, rfl⟩))
        · by_cases h2 : i < n*h+b
          · have hk : i - n*h < b := by omega
            have e : (fun u => z ((inp u).getD i false)) = sf ⟨i - n*h, hk⟩ := by
              funext u
              simp only [hinp, hsf]
              rw [List.getD_append_right _ _ _ _ (by rw [flat_length]; omega), flat_length]
              simp [List.getD_eq_getElem?_getD, hk]
            rw [e]; exact Submodule.subset_span (Or.inl (Or.inr ⟨_, rfl⟩))
          · have e : (fun u => z ((inp u).getD i false)) = 0 := by
              funext u
              rw [List.getD_eq_default _ _ (by rw [hinplen]; omega)]
              rfl
            rw [e]; exact Submodule.zero_mem _
      obtain ⟨L, hL, hspan⟩ := span_wires S0 inp (n*h+b) hinplen hin one C.gates hlen
      set e : Fin n × Fin (h+2) → (Fin n → Fin (2^(h+2))) → ZMod 2 :=
        fun p u => z ((u p.1).val.testBit p.2) with he
      have hemem : ∀ p, e p ∈ Submodule.span (ZMod 2) (S0 ∪ {f | f ∈ L}) := by
        intro p
        have ee : e p = fun u => z ((W C.gates (inp u)).getD (tap p.1 p.2) false) := by
          funext u; rw [hwW]
        rw [ee]; exact hspan _
      set A := Submodule.span (ZMod 2) (insert 1 (Set.range yf)) with hA
      set v : Fin b ⊕ Fin L.length → (((Fin n → Fin (2^(h+2))) → ZMod 2) ⧸ A) :=
        fun s => A.mkQ (Sum.elim sf (fun k => L[k]) s) with hv
      have hsub : Submodule.span (ZMod 2) (S0 ∪ {f | f ∈ L})
          ≤ (Submodule.span (ZMod 2) (Set.range v)).comap A.mkQ := by
        rw [Submodule.span_le]
        rintro f (((⟨q, rfl⟩ | ⟨k, rfl⟩) | h1) | hfL)
        · have : A.mkQ (yf q) = 0 := (Submodule.Quotient.mk_eq_zero A).2
            (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨q, rfl⟩))
          simp only [SetLike.mem_coe, Submodule.mem_comap, this, Submodule.zero_mem]
        · exact Submodule.subset_span ⟨Sum.inl k, rfl⟩
        · have : A.mkQ f = 0 := by
            rw [Set.mem_singleton_iff] at h1
            rw [h1]
            exact (Submodule.Quotient.mk_eq_zero A).2 (Submodule.subset_span (Set.mem_insert _ _))
          simp only [SetLike.mem_coe, Submodule.mem_comap, this, Submodule.zero_mem]
        · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hfL
          exact Submodule.subset_span ⟨Sum.inr ⟨k, hk⟩, rfl⟩
      have hind : LinearIndependent (ZMod 2) (fun p => A.mkQ (e p)) := by
        rw [Fintype.linearIndependent_iff]
        intro lam hlam p
        have hmem : (∑ q, lam q • e q) ∈ A := by
          rw [← Submodule.Quotient.mk_eq_zero A, ← Submodule.mkQ_apply, map_sum]
          simpa only [map_smul] using hlam
        rw [hA, Submodule.mem_span_insert] at hmem
        obtain ⟨c, w, hw', heq⟩ := hmem
        obtain ⟨mu, hmu⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hw'
        have pt : ∀ u, ∑ q, lam q * e q u = c + ∑ q, mu q * yf q u := by
          intro u
          have := congrFun heq u
          rw [← hmu] at this
          simpa [Finset.sum_apply] using this
        obtain ⟨j, i⟩ := p
        have red : ∀ a : Fin (2^(h+2)),
            ∑ i : Fin (h+2), lam (j,i) * z (a.val.testBit i)
              = c + ∑ i : Fin h, mu (j,i) * z (chiF (fun l => a.val.testBit l) i) := by
          intro a
          have := pt (Function.update (fun _ => (⟨0, Nat.two_pow_pos _⟩ : Fin (2^(h+2)))) j a)
          rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_eq_single j,
            Finset.sum_eq_single j] at this
          · simpa [he, hyf] using this
          · intro j' _ hj'
            apply Finset.sum_eq_zero
            intro i' _
            simp [hyf, Function.update_of_ne hj', z, chiF]
          · simp
          · intro j' _ hj'
            apply Finset.sum_eq_zero
            intro i' _
            simp [he, Function.update_of_ne hj', z]
          · simp
        have hc : c = 0 := by
          have := red ⟨0, Nat.two_pow_pos _⟩
          simpa [z, chiF] using this.symm
        have hmu0 : ∀ k : Fin h, mu (j,k) = 0 := by
          intro k
          have l1 : 2^(k.val+1) < 2^(h+2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
          have l2 : 2^(k.val+2) < 2^(h+2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
          have r1 := red ⟨_, l1⟩
          have r2 := red ⟨_, l2⟩
          have r12 := red ⟨_, Nat.or_lt_two_pow l1 l2⟩
          have hl : ∀ i : Nat, z ((2^(k.val+1) ||| 2^(k.val+2)).testBit i)
              = z ((2^(k.val+1)).testBit i) + z ((2^(k.val+2)).testBit i) := by
            intro i
            simp only [Nat.testBit_or, Nat.testBit_two_pow]
            by_cases h1 : k.val+1 = i
            · have h2 : ¬ (k.val+2 = i) := by omega
              simp [h1, h2, z]
            · simp [h1, z]
          have hq : ∀ m : Fin h,
              z (chiF (fun l => (2^(k.val+1) ||| 2^(k.val+2)).testBit l) m)
                = z (chiF (fun l => (2^(k.val+1)).testBit l) m)
                  + z (chiF (fun l => (2^(k.val+2)).testBit l) m)
                  + (if m = k then 1 else 0) := by
            intro m
            have := quad k.val m.val
            simp only [Nat.testBit_or, Nat.testBit_two_pow]
            rw [this]
            congr 1
            simp [z, Fin.ext_iff]
          simp only at r1 r2 r12
          simp only [hl, hq, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true] at r12
          rw [r1, r2, hc] at r12
          simp only [zero_add] at r12
          exact left_eq_add.1 r12
        have := red ⟨2^i.val, Nat.pow_lt_pow_right (by norm_num) i.isLt⟩
        simpa [hc, hmu0, Nat.testBit_two_pow, z, Fin.val_inj] using this
      have hmemv : ∀ p, A.mkQ (e p) ∈ Submodule.span (ZMod 2) (Set.range v) :=
        fun p => hsub (hemem p)
      have hind' : LinearIndependent (ZMod 2)
          (fun p => (⟨A.mkQ (e p), hmemv p⟩ : Submodule.span (ZMod 2) (Set.range v))) :=
        LinearIndependent.of_comp (Submodule.span (ZMod 2) (Set.range v)).subtype hind
      have c1 := hind'.fintype_card_le_finrank
      have c2 := finrank_range_le_card (R := ZMod 2) v
      unfold Set.finrank at c2
      have c3 := c1.trans c2
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum] at c3
      omega
  · rintro ⟨hb, ht⟩
    refine ⟨sideF n h b, ⟨gs n h b (n*h), 0⟩, fun j i => tapN n h b j i, ?_, ?_, ?_, ?_⟩
    · have all : ∀ p < 4*(n*h), ∃ g, (gs n h b (n*h))[p]? = some g ∧ g.inputs.length ≤ 2 ∧
          ∀ i ∈ g.inputs, i < n*h+b+p := by
        intro p hp
        have hq : p/4 < n*h := by omega
        have hk : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
        have hk' : p % 4 < (blk n h b (p/4)).length := by rw [blk_length]; exact hk
        have hg : (blk n h b (p/4))[p%4]? = some ((blk n h b (p/4))[p%4]) :=
          List.getElem?_eq_getElem hk'
        have r := reads n h b hb (p/4) (p%4) hq hk _ hg
        have ep : 4*(p/4) + p%4 = p := by omega
        refine ⟨_, ?_, r.1, ?_⟩
        · have := gs_get n h b (n*h) (p/4) (p%4) hq hk
          rw [ep] at this
          rw [this]; exact hg
        · rw [ep] at r; exact r.2
      constructor
      · intro p hp i hi
        simp only [gs_length] at hp
        obtain ⟨g, hg, _, hr⟩ := all p hp
        have : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs n h b (n*h), 0⟩ p = g := by
          simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg]
        rw [this] at hi
        exact hr i hi
      · intro g hg
        obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hg
        have hp' : p < 4*(n*h) := by simpa [gs_length] using hp
        obtain ⟨g', hg', hl, _⟩ := all p hp'
        obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.1 hg'
        show ((gs n h b (n*h))[p]).inputs.length ≤ 2
        rw [e]; exact hl
    · show (gs n h b (n*h)).countP nl ≤ t
      rw [gs_count]
      rw [Nat.mul_add] at ht
      omega
    · intro j i
      show tapN n h b j i < n*h+b+(gs n h b (n*h)).length
      rw [gs_length]
      have hj := j.isLt
      have hi := i.isLt
      unfold tapN
      split
      · have : (j.val+1)*h ≤ n*h := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul] at this
        omega
      · omega
    · intro u j i
      set x : List Bool := (List.ofFn (fun j : Fin n =>
          List.ofFn (fun i : Fin h => chiF (fun l => (u j).val.testBit l) i))).flatten
            ++ List.ofFn (sideF n h b u) with hx
      show (W (gs n h b (n*h)) x).getD (tapN n h b j i) false = (u j).val.testBit i
      have xlen : x.length = n*h+b := by
        simp only [hx, List.length_append, flat_length, List.length_ofFn]
      have low : ∀ p < n*h+b, (W (gs n h b (n*h)) x).getD p false = x.getD p false := by
        intro p hp
        have := W_stable [] (gs n h b (n*h)) x p (by simpa [xlen] using hp)
        simpa [W] using this
      have sideval : ∀ k (hk : k < b), x.getD (n*h+k) false = sideF n h b u ⟨k, hk⟩ := by
        intro k hk
        rw [hx, List.getD_append_right _ _ _ _ (by rw [flat_length]; omega), flat_length]
        simp [List.getD_eq_getElem?_getD, hk]
      have main : ∀ d i, i < h+2 → h+2-i = d →
          (W (gs n h b (n*h)) x).getD (tapN n h b j i) false = (u j).val.testBit i := by
        intro d
        induction d using Nat.strong_induction_on with
        | _ d ih =>
          intro i hi hd
          have hj := j.isLt
          by_cases hih : i < h
          swap
          · have e1 : tapN n h b j i = n*h + (2*j.val + (i-h)) := by
              unfold tapN; rw [if_neg hih]; omega
            have hk : 2*j.val + (i-h) < b := by omega
            rw [e1, low _ (by omega), sideval _ hk]
            unfold sideF
            have h2 : 2*j.val + (i-h) < 2*n := by omega
            rw [if_pos h2]
            have a1 : (2*j.val + (i-h))/2 = j.val := by omega
            have a2 : h + (2*j.val + (i-h))%2 = i := by omega
            simp only [a1, a2, bit, hj, dif_pos]
          · have hh : 0 < h := by omega
            set q := j.val*h + (h-1-i) with hqdef
            have hq : q < n*h := by
              have : (j.val+1)*h ≤ n*h := Nat.mul_le_mul_right _ hj
              rw [Nat.add_mul] at this
              omega
            have hqj : q / h = j.val := by
              rw [hqdef, Nat.add_comm, Nat.add_mul_div_right _ _ hh,
                Nat.div_eq_of_lt (by omega)]; omega
            have hqm : q % h = h-1-i := by
              rw [hqdef, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
            have hqi : h-1-q%h = i := by omega
            have etap : tapN n h b j i = x.length + (4*q+3) := by
              unfold tapN; rw [if_pos hih, ← hqdef, xlen]; omega
            have gate : ∀ k < 4, ∀ g, (blk n h b q)[k]? = some g →
                (W (gs n h b (n*h)) x).getD (x.length + (4*q+k)) false
                  = g.op.eval (g.inputs.map fun i => (W (gs n h b (n*h)) x).getD i false) := by
              intro k hk g hg
              apply W_at
              · rw [gs_get n h b (n*h) q k hq hk]; exact hg
              · rw [xlen]; exact (reads n h b hb q k hq hk g hg).2
            rw [etap]
            by_cases hgiv : q < b - 2*n
            · have hg : (blk n h b q)[3]? = some ⟨.and, [n*h + (2*n+q)]⟩ := by
                unfold blk; rw [if_pos hgiv]; rfl
              rw [gate 3 (by norm_num) _ hg]
              have hk : 2*n+q < b := by omega
              simp only [List.map_cons, List.map_nil]
              rw [low _ (by omega), sideval _ hk]
              unfold sideF
              have h2 : ¬ (2*n+q < 2*n) := by omega
              rw [if_neg h2]
              have a : 2*n+q - 2*n = q := by omega
              simp only [a, hqj, hqi, bit, hj, dif_pos, GateOp.eval, List.all_cons, List.all_nil,
                id, Bool.and_true]
            · have g0 : (blk n h b q)[0]? = some ⟨.not, [tapN n h b j (i+1)]⟩ := by
                unfold blk; rw [if_neg hgiv, hqj, hqi]; rfl
              have g1 : (blk n h b q)[1]? =
                  some ⟨.and, [n*h+b+4*q, tapN n h b j (i+2)]⟩ := by
                unfold blk; rw [if_neg hgiv, hqj, hqi]; rfl
              have g2 : (blk n h b q)[2]? =
                  some ⟨.mod 2, [n*h+b+4*q+1, j.val*h+i]⟩ := by
                unfold blk; rw [if_neg hgiv, hqj, hqi]; rfl
              have g3 : (blk n h b q)[3]? = some ⟨.not, [n*h+b+4*q+2]⟩ := by
                unfold blk; rw [if_neg hgiv]; rfl
              have i1 := ih (h+2-(i+1)) (by omega) (i+1) (by omega) rfl
              have i2 := ih (h+2-(i+2)) (by omega) (i+2) (by omega) rfl
              have v0 : (W (gs n h b (n*h)) x).getD (n*h+b+4*q) false
                  = !((u j).val.testBit (i+1)) := by
                have := gate 0 (by norm_num) _ g0
                rw [xlen, Nat.add_zero] at this
                rw [this]
                simp only [List.map_cons, List.map_nil, i1]
                rfl
              have v1 : (W (gs n h b (n*h)) x).getD (n*h+b+4*q+1) false
                  = (!((u j).val.testBit (i+1)) && (u j).val.testBit (i+2)) := by
                have := gate 1 (by norm_num) _ g1
                rw [xlen, ← Nat.add_assoc] at this
                rw [this]
                simp only [List.map_cons, List.map_nil, v0, i2, GateOp.eval, List.all_cons,
                  List.all_nil, id, Bool.and_true]
              have vy : (W (gs n h b (n*h)) x).getD (j.val*h+i) false
                  = xor ((u j).val.testBit i)
                    (!((u j).val.testBit (i+1)) && (u j).val.testBit (i+2)) := by
                have hy : j.val*h+i < n*h := by
                  have : (j.val+1)*h ≤ n*h := Nat.mul_le_mul_right _ hj
                  rw [Nat.add_mul] at this
                  omega
                rw [low _ (by omega), hx,
                  List.getD_append _ _ _ _ (by rw [flat_length]; exact hy)]
                exact flat_get n h (fun j i => chiF (fun l => (u j).val.testBit l) i) j ⟨i, hih⟩
              have v2 := gate 2 (by norm_num) _ g2
              rw [xlen, ← Nat.add_assoc] at v2
              have v3 := gate 3 (by norm_num) _ g3
              rw [xlen] at v3
              rw [xlen, v3]
              simp only [List.map_cons, List.map_nil]
              rw [v2]
              simp only [List.map_cons, List.map_nil, v1, vy]
              exact notmod _ _
      exact main _ i.val i.isLt rfl

end PEqualNP.Outside.L_meta_40353

theorem PEqualNP.Outside.L_meta_40353 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
let valid := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧
  ∀ g ∈ C.gates, g.inputs.length ≤ 2
let chi := fun (u : Nat → Bool) (i : Nat) => xor (u i) (!(u (i+1)) && u (i+2))
∀ (h n b t : Nat),
  let U := Fin n → Fin (2^(h+2))
  let w := n*h+b
  (∃ (side : U → Fin b → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (tap : Fin n → Fin (h+2) → Nat),
    valid w C ∧ C.gates.countP nonlinear ≤ t ∧
    (∀ j i, tap j i < w+C.gates.length) ∧
    ∀ (u : U),
      let y := (List.ofFn (fun j : Fin n =>
        List.ofFn (fun i : Fin h => chi (fun l => (u j).val.testBit l) i))).flatten
      let wires := C.wires (y ++ List.ofFn (side u))
      ∀ j i, wires.getD (tap j i) false = (u j).val.testBit i) ↔
    2*n ≤ b ∧ n*(h+2) ≤ b+t) := by
  intro nonlinear valid chi h n b t U w
  exact PEqualNP.Outside.L_meta_40353.key h n b t
