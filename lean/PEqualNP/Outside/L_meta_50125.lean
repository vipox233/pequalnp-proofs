import PEqualNP.Defs

-- Exhaustion certificate: a kernel-run search over sets of six-bit wire masks (a set is a Nat
-- bitset), with a soundness proof that every circuit of the statement is covered by the search.

namespace PEqualNP.Outside.L_meta_50125

open PEqualNP.CircuitLowerBounds

def elems (S : Nat) : List Nat := (List.range 64).filter (fun a => S.testBit a)

def aoHas (S v : Nat) : Bool :=
  (elems S).any (fun a => (elems S).any (fun c => (a &&& c == v) || (a ||| c == v)))

def notHas (S v : Nat) : Bool := (elems S).any (fun a => 63 ^^^ a == v)

def hit (A B C S : Nat) : Bool := S.testBit A && S.testBit B && S.testBit C

def miss (A B C S : Nat) : Nat :=
  (if S.testBit A then 0 else 1) + (if S.testBit B then 0 else 1) + (if S.testBit C then 0 else 1)

def reach (A B C : Nat) : Nat → Nat → Nat → Bool
  | 0, _, S => hit A B C S
  | k+1, b, S => hit A B C S || (decide (miss A B C S ≤ k+1) &&
      (reach A B C k b S || (decide (0 < b) && reach A B C k (b-1) S) ||
       (List.range 64).any (fun v => !S.testBit v &&
         ((aoHas S v && reach A B C k b (S ||| 2^v)) ||
          (decide (0 < b) && notHas S v && reach A B C k (b-1) (S ||| 2^v))))))

theorem mem_elems {S a : Nat} : a ∈ elems S ↔ a < 64 ∧ S.testBit a = true := by
  simp [elems, List.mem_filter, List.mem_range]

theorem bits32 : ∀ a < 64, ∀ c < 64, a &&& c < 64 ∧ a ||| c < 64 ∧ 63 ^^^ a < 64 := by
  decide +kernel

theorem uniq32 : ∀ m < 64, ∀ a < 64, (∀ t : Fin 6, m.testBit t.val = a.testBit t.val) → m = a := by
  decide +kernel

theorem t31 : ∀ t : Fin 6, (63 : Nat).testBit t.val = true := by decide

theorem or_pow_self {S v : Nat} (h : S.testBit v = true) : S ||| 2^v = S := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : v = i
  · subst hi; simp [h]
  · simp [hi]

theorem testBit_or_pow (S v x : Nat) : (S ||| 2^v).testBit x = (S.testBit x || decide (v = x)) := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]

theorem miss_step (A B C S v : Nat) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    miss A B C S ≤ miss A B C (S ||| 2^v) + 1 := by
  unfold miss
  rw [testBit_or_pow, testBit_or_pow, testBit_or_pow]
  by_cases a : S.testBit A = true <;> by_cases b : S.testBit B = true <;>
    by_cases c : S.testBit C = true <;> by_cases x : v = A <;> by_cases y : v = B <;>
    by_cases z : v = C <;> simp_all

theorem miss_of_hit {A B C S : Nat} (h : hit A B C S = true) : miss A B C S = 0 := by
  simp only [hit, Bool.and_eq_true] at h
  simp [miss, h.1.1, h.1.2, h.2]

theorem reach_hit {A B C S : Nat} (k b : Nat) (h : hit A B C S = true) : reach A B C k b S = true := by
  cases k with
  | zero => simpa [reach] using h
  | succ k => simp [reach, h]

theorem reach_miss {A B C S k b : Nat} (h : reach A B C k b S = true) :
    hit A B C S = true ∨ miss A B C S ≤ k := by
  cases k with
  | zero => left; simpa [reach] using h
  | succ k =>
    simp only [reach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem classify (S L : Nat) (W : Fin 6 → List Bool) (g : Gate)
    (h31 : S.testBit 63 = true) (h0 : S.testBit 0 = true)
    (hinv : ∀ i < L, ∃ m, m < 64 ∧ S.testBit m = true ∧ ∀ t, (W t).getD i false = m.testBit t.val)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < L) :
    ∃ v, v < 64 ∧ (∀ t, g.op.eval (g.inputs.map fun i => (W t).getD i false) = v.testBit t.val) ∧
      (S.testBit v = true ∨ (g.op ≠ GateOp.not ∧ aoHas S v = true) ∨
        (g.op = GateOp.not ∧ notHas S v = true)) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen hin ⊢
  match ins, hlen, hin with
  | [], _, _ =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨63, by decide, fun t => by simp [GateOp.eval, t31 t], Or.inl h31⟩
    · exact ⟨0, by decide, fun t => by simp [GateOp.eval], Or.inl h0⟩
    · exact ⟨63, by decide, fun t => by simp [GateOp.eval, t31 t], Or.inl h31⟩
  | [i], _, hin =>
    obtain ⟨m, hm, hS, hw⟩ := hinv i (hin i (by simp))
    rcases hop with rfl | rfl | rfl
    · exact ⟨m, hm, fun t => by simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval], Or.inl hS⟩
    · exact ⟨m, hm, fun t => by simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval], Or.inl hS⟩
    · refine ⟨63 ^^^ m, (bits32 m hm m hm).2.2, fun t => ?_, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval, Nat.testBit_xor, t31 t]
      · simp only [notHas, List.any_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, rfl⟩
  | [i, j], _, hin =>
    obtain ⟨m, hm, hS, hw⟩ := hinv i (hin i (by simp))
    obtain ⟨n, hn, hT, hv⟩ := hinv j (hin j (by simp))
    rcases hop with rfl | rfl | rfl
    · refine ⟨m &&& n, (bits32 m hm n hn).1, fun t => ?_, Or.inr (Or.inl ⟨(fun h => nomatch h), ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t, hv t]; simp [GateOp.eval, Nat.testBit_and]
      · simp only [aoHas, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, n, mem_elems.mpr ⟨hn, hT⟩, Or.inl rfl⟩
    · refine ⟨m ||| n, (bits32 m hm n hn).2.1, fun t => ?_, Or.inr (Or.inl ⟨(fun h => nomatch h), ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t, hv t]; simp [GateOp.eval, Nat.testBit_or]
      · simp only [aoHas, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, n, mem_elems.mpr ⟨hn, hT⟩, Or.inr rfl⟩
    · refine ⟨63 ^^^ m, (bits32 m hm m hm).2.2, fun t => ?_, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, hw t]; simp [GateOp.eval, Nat.testBit_xor, t31 t]
      · simp only [notHas, List.any_eq_true, beq_iff_eq]
        exact ⟨m, mem_elems.mpr ⟨hm, hS⟩, rfl⟩
  | _ :: _ :: _ :: _, hlen, _ => simp at hlen

theorem sound (A B C : Nat) (hA : A < 64) (hB : B < 64) (hC : C < 64)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    ∀ (gs : List Gate) (W : Fin 6 → List Bool) (L S k b : Nat),
      (∀ t, (W t).length = L) → S.testBit 63 = true → S.testBit 0 = true →
      (∀ i < L, ∃ m, m < 64 ∧ S.testBit m = true ∧ ∀ t, (W t).getD i false = m.testBit t.val) →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < L + j) →
      gs.length ≤ k → PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b →
      ∀ p q r, p < L + gs.length → q < L + gs.length → r < L + gs.length →
      (∀ t : Fin 6, (gs.foldl stepW (W t)).getD p false = A.testBit t.val ∧
        (gs.foldl stepW (W t)).getD q false = B.testBit t.val ∧
        (gs.foldl stepW (W t)).getD r false = C.testBit t.val) →
      reach A B C k b S = true := by
  intro gs
  induction gs with
  | nil =>
    intro W L S k b _ _ _ hinv _ _ _ _ p q r hp hq hr ht
    simp only [List.length_nil, Nat.add_zero, List.foldl_nil] at hp hq hr ht
    apply reach_hit
    obtain ⟨m1, h1, s1, w1⟩ := hinv p hp
    obtain ⟨m2, h2, s2, w2⟩ := hinv q hq
    obtain ⟨m3, h3, s3, w3⟩ := hinv r hr
    have e1 : m1 = A := uniq32 m1 h1 A hA (fun t => by rw [← w1 t, (ht t).1])
    have e2 : m2 = B := uniq32 m2 h2 B hB (fun t => by rw [← w2 t, (ht t).2.1])
    have e3 : m3 = C := uniq32 m3 h3 C hC (fun t => by rw [← w3 t, (ht t).2.2])
    subst e1 e2 e3
    simp [hit, s1, s2, s3]
  | cons g gs ih =>
    intro W L S k b hlen h31 h0 hinv hfan hrb hk hb p q r hp hq hr ht
    have hg := hfan g (by simp)
    have hin : ∀ i ∈ g.inputs, i < L := by
      intro i hi; have := hrb 0 (by simp) i (by simpa using hi); simpa using this
    obtain ⟨v, hv, hval, hcls⟩ := classify S L W g h31 h0 hinv hg.1 hg.2 hin
    let W' : Fin 6 → List Bool := fun t => stepW (W t) g
    have hlen' : ∀ t, (W' t).length = L + 1 := by intro t; simp [W', stepW, hlen t]
    have hinv' : ∀ i < L + 1, ∃ m, m < 64 ∧ (S ||| 2^v).testBit m = true ∧
        ∀ t, (W' t).getD i false = m.testBit t.val := by
      intro i hi
      by_cases hiL : i < L
      · obtain ⟨m, hm, hS, hw⟩ := hinv i hiL
        refine ⟨m, hm, by rw [testBit_or_pow, hS, Bool.true_or], fun t => ?_⟩
        simp only [W', stepW]
        rw [List.getD_append _ _ _ _ (by rw [hlen t]; exact hiL)]
        exact hw t
      · have hiE : i = L := by omega
        subst hiE
        refine ⟨v, hv, by rw [testBit_or_pow]; simp, fun t => ?_⟩
        simp only [W', stepW]
        rw [List.getD_append_right _ _ _ _ (by rw [hlen t]), hlen t, Nat.sub_self]
        exact hval t
    have hfan' : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hrb' : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < L + 1 + j := by
      intro j hj i hi
      have := hrb (j+1) (by simp; omega) i (by simpa using hi)
      omega
    have h31' : (S ||| 2^v).testBit 63 = true := by rw [testBit_or_pow, h31, Bool.true_or]
    have h00' : (S ||| 2^v).testBit 0 = true := by rw [testBit_or_pow, h0, Bool.true_or]
    simp only [List.length_cons] at hk hp hq hr
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have ht' : ∀ t : Fin 6, (gs.foldl stepW (W' t)).getD p false = A.testBit t.val ∧
        (gs.foldl stepW (W' t)).getD q false = B.testBit t.val ∧
        (gs.foldl stepW (W' t)).getD r false = C.testBit t.val := fun t => ht t
    have key : ∀ b', PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b' →
        reach A B C k b' (S ||| 2^v) = true := fun b' hb' =>
      ih W' (L+1) (S ||| 2^v) k b' hlen' h31' h00' hinv' hfan' hrb' (by omega) hb' p q r
        (by omega) (by omega) (by omega) ht'
    have hbn : g.op = GateOp.not →
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b - 1 ∧ 0 < b := by
      intro hn; simp [PEqualNP.NotBracket.notCount, List.filter_cons, hn] at hb ⊢; omega
    have hbo : g.op ≠ GateOp.not →
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ b := by
      intro hn; simp [PEqualNP.NotBracket.notCount, List.filter_cons, hn] at hb ⊢; omega
    have miss_ok : ∀ b', reach A B C k b' (S ||| 2^v) = true → miss A B C S ≤ k + 1 := by
      intro b' hR
      have := miss_step A B C S v hAB hAC hBC
      rcases reach_miss hR with hh | hh
      · have := miss_of_hit hh; omega
      · omega
    simp only [reach, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    right
    by_cases hn : g.op = GateOp.not
    · have hR := key (b-1) (hbn hn).1
      refine ⟨miss_ok _ hR, ?_⟩
      by_cases hsv : S.testBit v = true
      · rw [or_pow_self hsv] at hR
        exact Or.inl (Or.inr ⟨(hbn hn).2, hR⟩)
      · right
        rw [List.any_eq_true]
        refine ⟨v, List.mem_range.mpr hv, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        refine ⟨by simpa using hsv, ?_⟩
        rcases hcls with h | ⟨hn', h⟩ | ⟨_, h⟩
        · exact absurd h hsv
        · exact absurd hn hn'
        · exact Or.inr ⟨⟨(hbn hn).2, h⟩, hR⟩
    · have hR := key b (hbo hn)
      refine ⟨miss_ok _ hR, ?_⟩
      by_cases hsv : S.testBit v = true
      · rw [or_pow_self hsv] at hR
        exact Or.inl (Or.inl hR)
      · right
        rw [List.any_eq_true]
        refine ⟨v, List.mem_range.mpr hv, ?_⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        refine ⟨by simpa using hsv, ?_⟩
        rcases hcls with h | ⟨_, h⟩ | ⟨hn', h⟩
        · exact absurd h hsv
        · exact Or.inl ⟨h, hR⟩
        · exact absurd hn' hn

def S0 : Nat := 2^62 ||| 2^60 ||| 2^56 ||| 2^48 ||| 2^32 ||| 2^0 ||| 2^63

theorem cert : reach 14 24 44 5 2 S0 = false := by decide +kernel

theorem init : ∀ i < 7, ∃ m, m < 64 ∧ S0.testBit m = true ∧ ∀ t : Fin 6,
    ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]).getD i false =
      m.testBit t.val := by
  intro i hi
  refine ⟨[62, 60, 56, 48, 32, 0, 63].getD i 0, ?_⟩
  revert i
  decide +kernel

theorem main : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (14 : Nat).testBit t.val ∧
    w.getD q.val false = (24 : Nat).testBit t.val ∧
    w.getD r.val false = (44 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hf, hr, hn, hs, ht⟩
  have := sound 14 24 44 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    D.gates (fun t => (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])
    7 S0 5 2 (fun t => by simp) (by decide) (by decide) init hf hr hs hn p.val q.val r.val
    p.isLt q.isLt r.isLt (fun t => ht t)
  rw [cert] at this
  exact absurd this (by decide)

end PEqualNP.Outside.L_meta_50125

theorem PEqualNP.Outside.L_meta_50125 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (14 : Nat).testBit t.val ∧
    w.getD q.val false = (24 : Nat).testBit t.val ∧
    w.getD r.val false = (44 : Nat).testBit t.val) :=
  PEqualNP.Outside.L_meta_50125.main
