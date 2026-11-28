import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50276_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def miss (a b c : Nat) (L : List Nat) : Nat :=
  (if a ∈ L then 0 else 1) + (if b ∈ L then 0 else 1) + (if c ∈ L then 0 else 1)

def kids (L : List Nat) : List Nat :=
  ((L.flatMap fun x => L.flatMap fun y => [x &&& y, x ||| y]).filter fun v => !L.contains v).dedup

def nkids (L : List Nat) : List Nat :=
  ((L.map fun x => 63 ^^^ x).filter fun v => !L.contains v).dedup

def unreach (a b c : Nat) : Nat → Nat → List Nat → Bool
  | 0, _, L => decide (0 < miss a b c L)
  | k + 1, 0, L => decide (k + 1 < miss a b c L) ||
      (decide (0 < miss a b c L) && (kids L).all fun v => unreach a b c k 0 (v :: L))
  | k + 1, n + 1, L => decide (k + 1 < miss a b c L) ||
      (decide (0 < miss a b c L) && ((kids L).all fun v => unreach a b c k (n + 1) (v :: L)) &&
        (nkids L).all fun v => unreach a b c k n (v :: L))

def check (K a b c : Nat) : Bool :=
  decide (a < b) && decide (b < c) && decide (c < 64) && unreach a b c K 2 [62, 60, 56, 48, 32, 0, 63]

theorem miss_step {a b c : Nat} (hab : a < b) (hbc : b < c) (v : Nat) (L : List Nat) :
    miss a b c L ≤ miss a b c (v :: L) + 1 := by
  have key : ∀ z : Nat, (if z ∈ L then 0 else 1) ≤
      (if z ∈ v :: L then 0 else 1) + (if z = v then 1 else 0) := by
    intro z
    by_cases h2 : z = v
    · subst h2
      by_cases h1 : z ∈ L <;> simp [h1]
    · by_cases h1 : z ∈ L <;> simp [h1, h2]
  have ka := key a
  have kb := key b
  have kc := key c
  have h1 : (if a = v then 1 else 0) + (if b = v then 1 else 0) + (if c = v then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  unfold miss
  omega

theorem miss_zero {a b c : Nat} {L : List Nat} (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) :
    miss a b c L = 0 := by
  simp [miss, ha, hb, hc]

theorem unreach_pos {a b c k n : Nat} {L : List Nat} (h : unreach a b c k n L = true) :
    0 < miss a b c L := by
  cases k with
  | zero => simpa [unreach] using h
  | succ k =>
    cases n with
    | zero =>
      simp only [unreach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨h, _⟩ <;> omega
    | succ n =>
      simp only [unreach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨⟨h, _⟩, _⟩ <;> omega

theorem cutTrue {a b c k n : Nat} {L : List Nat} (h : k < miss a b c L) :
    unreach a b c k n L = true := by
  cases k with
  | zero => simp [unreach, h]
  | succ k => cases n <;> simp [unreach, h]

theorem kid {a b c k n v : Nat} {L : List Nat} (h : unreach a b c (k + 1) n L = true)
    (hc : ¬ k + 1 < miss a b c L) (hv : v ∈ kids L) : unreach a b c k n (v :: L) = true := by
  cases n with
  | zero =>
    simp only [unreach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at h
    rcases h with h | ⟨_, h⟩
    · exact absurd h hc
    · exact h v hv
  | succ n =>
    simp only [unreach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at h
    rcases h with h | ⟨⟨_, h⟩, _⟩
    · exact absurd h hc
    · exact h v hv

theorem nkid {a b c k n v : Nat} {L : List Nat} (h : unreach a b c (k + 1) (n + 1) L = true)
    (hc : ¬ k + 1 < miss a b c L) (hv : v ∈ nkids L) : unreach a b c k n (v :: L) = true := by
  simp only [unreach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  rcases h with h | ⟨_, h⟩
  · exact absurd h hc
  · exact h v hv

theorem mem_kids {L : List Nat} {x y m : Nat} (hx : x ∈ L) (hy : y ∈ L)
    (hm : m = x &&& y ∨ m = x ||| y) (hin : m ∉ L) : m ∈ kids L := by
  unfold kids
  rw [List.mem_dedup, List.mem_filter]
  refine ⟨List.mem_flatMap.2 ⟨x, hx, List.mem_flatMap.2 ⟨y, hy, ?_⟩⟩, by simpa using hin⟩
  simpa using hm

theorem mem_nkids {L : List Nat} {x : Nat} (hx : x ∈ L) (hin : 63 ^^^ x ∉ L) :
    63 ^^^ x ∈ nkids L := by
  unfold nkids
  rw [List.mem_dedup, List.mem_filter]
  exact ⟨List.mem_map.2 ⟨x, hx, rfl⟩, by simpa using hin⟩

theorem b31 : ∀ t : Fin 6, Nat.testBit 63 t.val = true := by decide

theorem getD_tb (M : List Nat) (t i : Nat) :
    (M.map fun x => x.testBit t).getD i false = (M.getD i 0).testBit t := by
  have h := List.getD_map (l := M) (d := 0) (n := i) (fun x : Nat => x.testBit t)
  simpa using h

theorem getD_mem {L M : List Nat} (hML : ∀ x ∈ M, x ∈ L) (h0 : 0 ∈ L) (i : Nat) :
    M.getD i 0 ∈ L := by
  rw [List.getD_eq_getElem?_getD]
  cases h : M[i]? with
  | none => simpa using h0
  | some x => simpa using hML x (List.mem_of_getElem? h)

theorem eq5 {x a : Nat} (hx : x < 64) (ha : a < 64)
    (H : ∀ t : Fin 6, x.testBit t.val = a.testBit t.val) : x = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < 6
  · exact H ⟨i, h⟩
  · have h32 : 64 ≤ 2 ^ i := by
      have : 2 ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx h32),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha h32)]

theorem gstep (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {L M : List Nat} (hML : ∀ x ∈ M, x ∈ L) (h0 : 0 ∈ L) (h31 : 63 ∈ L) :
    ∃ m, (∀ t : Fin 6, g.op.eval (g.inputs.map fun i =>
        (M.map fun x => x.testBit t.val).getD i false) = m.testBit t.val) ∧
      ((g.op ≠ GateOp.not ∧ ∃ x ∈ L, ∃ y ∈ L, m = x &&& y ∨ m = x ||| y) ∨
        (g.op = GateOp.not ∧ ∃ x ∈ L, m = 63 ^^^ x)) := by
  obtain ⟨op, ins⟩ := g
  have gd := getD_mem hML h0
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    cases op with
    | and =>
      exact ⟨63, fun t => by simp [GateOp.eval, b31 t],
        Or.inl ⟨by simp, 63, h31, 63, h31, Or.inl (by decide)⟩⟩
    | or =>
      exact ⟨0, fun t => by simp [GateOp.eval],
        Or.inl ⟨by simp, 0, h0, 0, h0, Or.inl (by decide)⟩⟩
    | not =>
      exact ⟨63 ^^^ 0, fun t => by simpa [GateOp.eval] using (b31 t).symm,
        Or.inr ⟨rfl, 0, h0, rfl⟩⟩
    | mod m => simp at hop
    | maj => simp at hop
  | [i], _ =>
    cases op with
    | and =>
      exact ⟨M.getD i 0, fun t => by (simp only [List.map_cons, List.map_nil, getD_tb]; simp [GateOp.eval]),
        Or.inl ⟨by simp, _, gd i, _, gd i, Or.inl (Nat.and_self _).symm⟩⟩
    | or =>
      exact ⟨M.getD i 0, fun t => by (simp only [List.map_cons, List.map_nil, getD_tb]; simp [GateOp.eval]),
        Or.inl ⟨by simp, _, gd i, _, gd i, Or.inr (Nat.or_self _).symm⟩⟩
    | not =>
      exact ⟨63 ^^^ M.getD i 0, fun t => by (simp only [List.map_cons, List.map_nil, getD_tb]; simp [GateOp.eval, Nat.testBit_xor, b31 t]),
        Or.inr ⟨rfl, _, gd i, rfl⟩⟩
    | mod m => simp at hop
    | maj => simp at hop
  | [i, j], _ =>
    cases op with
    | and =>
      exact ⟨M.getD i 0 &&& M.getD j 0,
        fun t => by (simp only [List.map_cons, List.map_nil, getD_tb]; simp [GateOp.eval, Nat.testBit_and]),
        Or.inl ⟨by simp, _, gd i, _, gd j, Or.inl rfl⟩⟩
    | or =>
      exact ⟨M.getD i 0 ||| M.getD j 0,
        fun t => by (simp only [List.map_cons, List.map_nil, getD_tb]; simp [GateOp.eval, Nat.testBit_or]),
        Or.inl ⟨by simp, _, gd i, _, gd j, Or.inr rfl⟩⟩
    | not =>
      exact ⟨63 ^^^ M.getD i 0, fun t => by (simp only [List.map_cons, List.map_nil, getD_tb]; simp [GateOp.eval, Nat.testBit_xor, b31 t]),
        Or.inr ⟨rfl, _, gd i, rfl⟩⟩
    | mod m => simp at hop
    | maj => simp at hop
  | _ :: _ :: _ :: _, h => simp at h

theorem filter_len (P : Gate → Bool) (g : Gate) (rest : List Gate) :
    (rest.filter P).length ≤ ((g :: rest).filter P).length := by
  rw [List.filter_cons]
  split <;> simp

theorem core {a b c : Nat} (hab : a < b) (hbc : b < c) (hc : c < 64) (P : Gate → Bool)
    (hP : ∀ g : Gate, g.op = GateOp.not → P g = true) :
    ∀ (gs : List Gate) (k n : Nat) (L M : List Nat),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    gs.length ≤ k → (gs.filter P).length ≤ n →
    (∀ x ∈ M, x ∈ L) → 0 ∈ L → 63 ∈ L → (∀ x ∈ L, x < 64) → unreach a b c k n L = true →
    ∀ p q r : Nat, (∀ t : Fin 6,
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (M.map fun x => x.testBit t.val)).getD p false = a.testBit t.val ∧
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (M.map fun x => x.testBit t.val)).getD q false = b.testBit t.val ∧
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (M.map fun x => x.testBit t.val)).getD r false = c.testBit t.val) → False := by
  intro gs
  induction gs with
  | nil =>
    intro k n L M _ _ _ hML h0 _ hL hu p q r H
    have hpos := unreach_pos hu
    have key : ∀ (i z : Nat), z < 64 →
        (∀ t : Fin 6, (M.map fun x => x.testBit t.val).getD i false = z.testBit t.val) →
        z ∈ L := by
      intro i z hz Hz
      have hm := getD_mem hML h0 i
      have e : M.getD i 0 = z := eq5 (hL _ hm) hz (fun t => by rw [← getD_tb]; exact Hz t)
      exact e ▸ hm
    have ha := key p a (by omega) (fun t => (H t).1)
    have hb := key q b (by omega) (fun t => (H t).2.1)
    have hc' := key r c hc (fun t => (H t).2.2)
    have := miss_zero ha hb hc'
    omega
  | cons g rest ih =>
    intro k n L M hF hk hn hML h0 h31 hL hu p q r H
    obtain ⟨m, hm, hcase⟩ := gstep g (hF g (by simp)) hML h0 h31
    have hF' : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' h' => hF g' (List.mem_cons_of_mem _ h')
    have e : ∀ t : Fin 6, (M.map fun x => x.testBit t.val) ++
        [g.op.eval (g.inputs.map fun i => (M.map fun x => x.testBit t.val).getD i false)] =
        (M ++ [m]).map fun x => x.testBit t.val := by
      intro t
      rw [hm t]
      simp
    have H' : ∀ t : Fin 6,
        (rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          ((M ++ [m]).map fun x => x.testBit t.val)).getD p false = a.testBit t.val ∧
        (rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          ((M ++ [m]).map fun x => x.testBit t.val)).getD q false = b.testBit t.val ∧
        (rest.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          ((M ++ [m]).map fun x => x.testBit t.val)).getD r false = c.testBit t.val := by
      intro t
      have h := H t
      simp only [List.foldl_cons] at h
      rw [e t] at h
      exact h
    have hk' : rest.length + 1 ≤ k := by simpa using hk
    have hn' := filter_len P g rest
    by_cases hin : m ∈ L
    · refine ih k n L (M ++ [m]) hF' (by omega) (by omega) ?_ h0 h31 hL hu p q r H'
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hML x hx
      · rw [List.mem_singleton.1 hx]; exact hin
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have sub : ∀ x ∈ M ++ [m], x ∈ m :: L := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact List.mem_cons_of_mem _ (hML x hx)
        · rw [List.mem_singleton.1 hx]; exact List.mem_cons_self
      have hL' : m < 64 → ∀ x ∈ m :: L, x < 64 := by
        intro hm32 x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hm32
        · exact hL x hx
      have hstep := miss_step hab hbc m L
      rcases hcase with ⟨_, x, hx, y, hy, hxy⟩ | ⟨hop, x, hx, rfl⟩
      · have hm32 : m < 64 := by
          rcases hxy with rfl | rfl
          · exact Nat.and_lt_two_pow x (n := 6) (hL y hy)
          · exact Nat.or_lt_two_pow (n := 6) (hL x hx) (hL y hy)
        have hu' : unreach a b c k' n (m :: L) = true := by
          by_cases hcut : k' + 1 < miss a b c L
          · exact cutTrue (by omega)
          · exact kid hu hcut (mem_kids hx hy hxy hin)
        exact ih k' n (m :: L) (M ++ [m]) hF' (by omega) (by omega) sub
          (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h31) (hL' hm32) hu' p q r H'
      · have hm32 : 63 ^^^ x < 64 := Nat.xor_lt_two_pow (n := 6) (by omega) (hL x hx)
        have hPg : ((g :: rest).filter P).length = (rest.filter P).length + 1 := by
          simp [hP g hop]
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        have hu' : unreach a b c k' n' ((63 ^^^ x) :: L) = true := by
          by_cases hcut : k' + 1 < miss a b c L
          · exact cutTrue (by omega)
          · exact nkid hu hcut (mem_nkids hx hin)
        exact ih k' n' ((63 ^^^ x) :: L) (M ++ [63 ^^^ x]) hF' (by omega) (by omega) sub
          (List.mem_cons_of_mem _ h0) (List.mem_cons_of_mem _ h31) (hL' hm32) hu' p q r H'

theorem init : ∀ t : Fin 6,
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] =
      ([62, 60, 56, 48, 32, 0, 63] : List Nat).map fun x => x.testBit t.val := by
  decide

theorem final (K a b c : Nat) (h : check K a b c = true) :
    ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
      PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ K ∧
      ∀ t : Fin 6,
        let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
        let w := D.wires xs
        w.getD p.val false = (a : Nat).testBit t.val ∧
        w.getD q.val false = (b : Nat).testBit t.val ∧
        w.getD r.val false = (c : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hF, _, hN, hK, H⟩
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hab, hbc⟩, hc⟩, hu⟩ := h
  unfold PEqualNP.NotBracket.notCount at hN
  refine core hab hbc hc _ ?_ D.gates K 2 [62, 60, 56, 48, 32, 0, 63]
    [62, 60, 56, 48, 32, 0, 63] hF hK hN (fun x hx => hx) (by decide) (by decide) (by decide) hu
    p.val q.val r.val ?_
  · intro g hg
    simpa using hg
  intro t
  have h1 := H t
  simp only [Circuit.wires, init t] at h1
  exact h1

end PEqualNP.Outside.L_meta_50276_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem PEqualNP.Outside.L_meta_50276 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (12 : Nat).testBit t.val ∧
    w.getD q.val false = (40 : Nat).testBit t.val ∧
    w.getD r.val false = (61 : Nat).testBit t.val) :=
  PEqualNP.Outside.L_meta_50276_aux.final 5 12 40 61 (by decide +kernel)
