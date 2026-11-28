import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50904

open PEqualNP.CircuitLowerBounds

def tgts : List Nat := [6, 40, 44]

def hitAll (S : List Nat) : Bool := S.contains 6 && S.contains 40 && S.contains 44

def missing (S : List Nat) : Nat :=
  (if S.contains 6 then 0 else 1) + (if S.contains 40 then 0 else 1) +
    (if S.contains 44 then 0 else 1)

def stepAny (hrec : Nat → List Nat → Bool) (n : Nat) (S : List Nat) : Bool :=
  (decide (0 < n) && S.any (fun a => !S.contains (63 ^^^ a) && hrec (n - 1) ((63 ^^^ a) :: S))) ||
  S.any (fun a => S.any (fun b =>
    (!S.contains (a &&& b) && hrec n ((a &&& b) :: S)) ||
    (!S.contains (a ||| b) && hrec n ((a ||| b) :: S))))

def can (k : Nat) : Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Bool) (fun _ S => hitAll S)
    (fun k ih n S => hitAll S || (decide (missing S ≤ k + 1) && stepAny ih n S)) k

theorem can_zero (n : Nat) (S : List Nat) : can 0 n S = hitAll S := rfl

theorem can_succ (k n : Nat) (S : List Nat) :
    can (k + 1) n S = (hitAll S || (decide (missing S ≤ k + 1) && stepAny (can k) n S)) := rfl

def S0 : List Nat := [62, 60, 56, 48, 32, 0, 63]

theorem search_fails : can 5 2 S0 = false := by decide

theorem hit_can {S : List Nat} (h : hitAll S = true) : ∀ k n, can k n S = true
  | 0, _ => by rw [can_zero]; exact h
  | _ + 1, _ => by rw [can_succ, h, Bool.true_or]

theorem missing_zero {S : List Nat} (h : hitAll S = true) : missing S = 0 := by
  unfold hitAll at h
  simp only [Bool.and_eq_true] at h
  unfold missing; rw [h.1.1, h.1.2, h.2]; rfl

theorem can_missing : ∀ (k n : Nat) (S : List Nat), can k n S = true → missing S ≤ k
  | 0, n, S, h => by rw [can_zero] at h; rw [missing_zero h]
  | k + 1, n, S, h => by
    rw [can_succ] at h
    cases hh : hitAll S
    · rw [hh, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
    · rw [missing_zero hh]; omega

theorem missing_cons (z : Nat) (S : List Nat) : missing S ≤ missing (z :: S) + 1 := by
  unfold missing
  simp only [List.contains_cons]
  by_cases a : z = 6
  · subst a; cases S.contains 6 <;> cases S.contains 40 <;> cases S.contains 44 <;> decide
  · by_cases b : z = 40
    · subst b; cases S.contains 6 <;> cases S.contains 40 <;> cases S.contains 44 <;> decide
    · by_cases c : z = 44
      · subst c; cases S.contains 6 <;> cases S.contains 40 <;> cases S.contains 44 <;> decide
      · have a' : (6 == z) = false := by simp [beq_iff_eq]; omega
        have b' : (40 == z) = false := by simp [beq_iff_eq]; omega
        have c' : (44 == z) = false := by simp [beq_iff_eq]; omega
        rw [a', b', c']
        cases S.contains 6 <;> cases S.contains 40 <;> cases S.contains 44 <;> decide

theorem stepAny_mono {r r' : Nat → List Nat → Bool} (hr : ∀ n S, r n S = true → r' n S = true)
    {n : Nat} {S : List Nat} (h : stepAny r n S = true) : stepAny r' n S = true := by
  unfold stepAny at h ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h ⊢
  rcases h with ⟨h0, a, ha, h1, h2⟩ | ⟨a, ha, b, hb, h⟩
  · exact Or.inl ⟨h0, a, ha, h1, hr _ _ h2⟩
  · refine Or.inr ⟨a, ha, b, hb, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, hr _ _ h2⟩
    · exact Or.inr ⟨h1, hr _ _ h2⟩

theorem can_mono_k : ∀ (k n : Nat) (S : List Nat), can k n S = true → can (k + 1) n S = true
  | 0, n, S, h => hit_can (by rwa [can_zero] at h) _ _
  | k + 1, n, S, h => by
    rw [can_succ] at h ⊢
    cases hh : hitAll S
    · rw [hh, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, stepAny_mono (fun n S => can_mono_k k n S) h.2⟩
    · rfl

theorem can_mono_n : ∀ (k n : Nat) (S : List Nat), can k n S = true → can k (n + 1) S = true
  | 0, n, S, h => by rw [can_zero] at h ⊢; exact h
  | k + 1, n, S, h => by
    rw [can_succ] at h ⊢
    cases hh : hitAll S
    · rw [hh, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
      rw [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      unfold stepAny at h2 ⊢
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h2 ⊢
      rcases h2 with ⟨h0, a, ha, h1, h3⟩ | ⟨a, ha, b, hb, h3⟩
      · refine Or.inl ⟨by omega, a, ha, h1, ?_⟩
        have e : n + 1 - 1 = (n - 1) + 1 := by omega
        rw [e]; exact can_mono_n k (n - 1) _ h3
      · refine Or.inr ⟨a, ha, b, hb, ?_⟩
        rcases h3 with ⟨h1, h4⟩ | ⟨h1, h4⟩
        · exact Or.inl ⟨h1, can_mono_n k n _ h4⟩
        · exact Or.inr ⟨h1, can_mono_n k n _ h4⟩
    · rfl

theorem can_mono_n' {k n n' : Nat} {S : List Nat} (hn : n ≤ n') (h : can k n S = true) :
    can k n' S = true := by
  induction hn with
  | refl => exact h
  | step _ ih => exact can_mono_n _ _ _ ih

def gm (L : List Nat) (g : Gate) : Nat :=
  match g.op, g.inputs with
  | .and, [] => 63
  | .and, [a] => L.getD a 0
  | .and, [a, b] => L.getD a 0 &&& L.getD b 0
  | .or, [] => 0
  | .or, [a] => L.getD a 0
  | .or, [a, b] => L.getD a 0 ||| L.getD b 0
  | .not, [] => 63
  | .not, a :: _ => 63 ^^^ L.getD a 0
  | _, _ => 0

def run (L : List Nat) (gs : List Gate) : List Nat := gs.foldl (fun L g => L ++ [gm L g]) L

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def notCnt (gs : List Gate) : Nat := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem notCnt_not {g : Gate} (gs : List Gate) (h : g.op = GateOp.not) :
    notCnt (g :: gs) = notCnt gs + 1 := by
  unfold notCnt PEqualNP.NotBracket.notCount
  simp only [List.filter_cons, h, decide_true, if_true, List.length_cons]

theorem notCnt_other {g : Gate} (gs : List Gate) (h : g.op ≠ GateOp.not) :
    notCnt (g :: gs) = notCnt gs := by
  unfold notCnt PEqualNP.NotBracket.notCount
  simp only [List.filter_cons, h, decide_false, if_false, Bool.false_eq_true]

theorem t63' : ∀ t, t < 6 → (63 : Nat).testBit t = true := by decide

theorem t63 {t : Nat} (ht : t < 6) : (63 : Nat).testBit t = true := t63' t ht

theorem gate_sem {t : Nat} (ht : t < 6) (w : List Bool) (L : List Nat)
    (hw : ∀ i, w.getD i false = (L.getD i 0).testBit t) (g : Gate) (hg : Ok g) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = (gm L g).testBit t := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl <;>
  match ins, hlen with
  | [], _ =>
    simp only [GateOp.eval, gm, List.map_nil, List.all_nil, List.any_nil, List.headD_nil,
      Bool.not_false, t63 ht, Nat.zero_testBit]
  | [a], _ =>
    simp only [GateOp.eval, gm, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      List.any_cons, List.any_nil, List.headD_cons, id, Bool.and_true, Bool.or_false, hw,
      Nat.testBit_xor, t63 ht, Bool.true_xor]
  | [a, b], _ =>
    simp only [GateOp.eval, gm, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      List.any_cons, List.any_nil, List.headD_cons, id, Bool.and_true, Bool.or_false, hw,
      Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, t63 ht, Bool.true_xor]

theorem getD_snoc {α : Type} (l : List α) (x d : α) (i : Nat) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

theorem wires_sem {t : Nat} (ht : t < 6) : ∀ (gs : List Gate) (w : List Bool) (L : List Nat),
    (∀ g ∈ gs, Ok g) → w.length = L.length → (∀ i, w.getD i false = (L.getD i 0).testBit t) →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      (run L gs).length ∧
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
      ((run L gs).getD i 0).testBit t
  | [], w, L, _, hl, hw => ⟨hl, hw⟩
  | g :: gs, w, L, hok, hl, hw => by
    have hg := hok g (List.mem_cons_self ..)
    apply wires_sem ht gs _ _ (fun g' h' => hok g' (List.mem_cons_of_mem _ h'))
    · simp [hl]
    · intro i
      rw [getD_snoc, getD_snoc, hl]
      split_ifs
      · exact hw i
      · exact gate_sem ht w L hw g hg
      · simp

theorem gm_lt (L : List Nat) (hL : ∀ x ∈ L, x < 64) (g : Gate) : gm L g < 64 := by
  have hd : ∀ i, L.getD i 0 < 64 := by
    intro i
    by_cases h : i < L.length
    · rw [List.getD_eq_getElem _ _ h]; exact hL _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  obtain ⟨op, ins⟩ := g
  unfold gm
  split
  all_goals first
    | omega
    | exact hd _
    | exact lt_of_le_of_lt Nat.and_le_left (hd _)
    | exact Nat.or_lt_two_pow (n := 6) (hd _) (hd _)
    | exact Nat.xor_lt_two_pow (n := 6) (by omega) (hd _)

theorem run_lt : ∀ (gs : List Gate) (L : List Nat), (∀ x ∈ L, x < 64) → ∀ x ∈ run L gs, x < 64
  | [], L, hL => hL
  | g :: gs, L, hL => by
    apply run_lt gs
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hL x h
    · rw [List.mem_singleton.mp h]; exact gm_lt L hL g

theorem getD_mem_or_zero (L : List Nat) (i : Nat) : L.getD i 0 ∈ L ∨ L.getD i 0 = 0 := by
  by_cases h : i < L.length
  · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · right; exact List.getD_eq_default _ _ (by omega)

theorem step_ok (L S : List Nat) (hmem : ∀ i, L.getD i 0 ∈ S) (h0 : 0 ∈ S) (h63 : 63 ∈ S)
    (g : Gate) (hg : Ok g) :
    gm L g ∈ S ∨ (g.op ≠ GateOp.not ∧ ∃ a ∈ S, ∃ b ∈ S, gm L g = a &&& b ∨ gm L g = a ||| b) ∨
      (g.op = GateOp.not ∧ ∃ a ∈ S, gm L g = 63 ^^^ a) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases hop with rfl | rfl | rfl <;>
  match ins, hlen with
  | [], _ => left; simp only [gm]; first | exact h63 | exact h0
  | [a], _ =>
    first
      | (left; simp only [gm]; exact hmem a)
      | (right; right; exact ⟨rfl, _, hmem a, rfl⟩)
  | [a, b], _ =>
    first
      | (right; left; exact ⟨(by intro h; cases h), _, hmem a, _, hmem b, Or.inl rfl⟩)
      | (right; left; exact ⟨(by intro h; cases h), _, hmem a, _, hmem b, Or.inr rfl⟩)
      | (right; right; exact ⟨rfl, _, hmem a, rfl⟩)

theorem sound : ∀ (gs : List Gate) (k n : Nat) (L S : List Nat), (∀ g ∈ gs, Ok g) →
    gs.length ≤ k → notCnt gs ≤ n → (∀ x ∈ L, x ∈ S) → 0 ∈ S → 63 ∈ S →
    6 ∈ run L gs → 40 ∈ run L gs → 44 ∈ run L gs → can k n S = true
  | [], k, n, L, S, _, _, _, hLS, _, _, h6, h40, h44 => by
    apply hit_can
    unfold hitAll
    simp only [Bool.and_eq_true, List.contains_iff_mem]
    exact ⟨⟨hLS _ h6, hLS _ h40⟩, hLS _ h44⟩
  | g :: gs, k, n, L, S, hok, hk, hn, hLS, h0, h63, h6, h40, h44 => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hg := hok g (List.mem_cons_self ..)
    have hok' : ∀ g' ∈ gs, Ok g' := fun g' h' => hok g' (List.mem_cons_of_mem _ h')
    have hk' : gs.length ≤ k' := by simp at hk; omega
    have hmem : ∀ i, L.getD i 0 ∈ S := fun i =>
      (getD_mem_or_zero L i).elim (fun h => hLS _ h) (fun h => by rw [h]; exact h0)
    set z := gm L g with hz
    have h6' : 6 ∈ run (L ++ [z]) gs := h6
    have h40' : 40 ∈ run (L ++ [z]) gs := h40
    have h44' : 44 ∈ run (L ++ [z]) gs := h44
    have hnle : notCnt gs ≤ n := by
      by_cases hop : g.op = GateOp.not
      · rw [notCnt_not gs hop] at hn; omega
      · rw [notCnt_other gs hop] at hn; exact hn
    by_cases hzS : z ∈ S
    · apply can_mono_k
      apply sound gs k' n (L ++ [z]) S hok' hk' hnle _ h0 h63 h6' h40' h44'
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hLS x h
      · rw [List.mem_singleton.mp h]; exact hzS
    · have hLS' : ∀ x ∈ L ++ [z], x ∈ z :: S := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact List.mem_cons_of_mem _ (hLS x h)
        · rw [List.mem_singleton.mp h]; exact List.mem_cons_self ..
      have h0' : 0 ∈ z :: S := List.mem_cons_of_mem _ h0
      have h63' : 63 ∈ z :: S := List.mem_cons_of_mem _ h63
      have hzc : S.contains z = false := by simpa [List.contains_iff_mem] using hzS
      rw [can_succ]
      cases hh : hitAll S
      · rw [Bool.false_or, Bool.and_eq_true, decide_eq_true_eq]
        rcases step_ok L S hmem h0 h63 g hg with hin | ⟨hop, a, ha, b, hb, hab⟩ | ⟨hop, a, ha, hza⟩
        · exact absurd hin hzS
        · have hrec := sound gs k' n (L ++ [z]) (z :: S) hok' hk' hnle hLS' h0' h63' h6' h40' h44'
          refine ⟨le_trans (missing_cons z S) (by have := can_missing _ _ _ hrec; omega), ?_⟩
          unfold stepAny
          simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
          refine Or.inr ⟨a, ha, b, hb, ?_⟩
          rcases hab with e | e
          · left; rw [← e]; exact ⟨by simpa using hzS, hrec⟩
          · right; rw [← e]; exact ⟨by simpa using hzS, hrec⟩
        · rw [notCnt_not gs hop] at hn
          have hrec := sound gs k' (n - 1) (L ++ [z]) (z :: S) hok' hk' (by omega) hLS' h0' h63'
            h6' h40' h44'
          refine ⟨le_trans (missing_cons z S) (by have := can_missing _ _ _ hrec; omega), ?_⟩
          unfold stepAny
          simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
          refine Or.inl ⟨by omega, a, ha, ?_⟩
          rw [← hza]; exact ⟨by simpa using hzS, hrec⟩
      · rfl

theorem base_small : ∀ t : Fin 6, ∀ i : Fin 7,
    ((List.ofFn (fun j : Fin 5 => decide (j.val < t.val))) ++ [false, true]).getD i.val false =
      (S0.getD i.val 0).testBit t.val := by decide

theorem base_sem (t : Fin 6) (i : Nat) :
    ((List.ofFn (fun j : Fin 5 => decide (j.val < t.val))) ++ [false, true]).getD i false =
      (S0.getD i 0).testBit t.val := by
  by_cases hi : i < 7
  · exact base_small t ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [S0]; omega)]
    simp

theorem run_length : ∀ (gs : List Gate) (L : List Nat), (run L gs).length = L.length + gs.length
  | [], L => rfl
  | g :: gs, L => by
    show (run (L ++ [gm L g]) gs).length = _
    rw [run_length gs]; simp; omega

theorem eq_of_bits {x c : Nat} (hx : x < 64) (hc : c < 64)
    (h : ∀ t : Fin 6, x.testBit t.val = c.testBit t.val) : x = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact h ⟨i, hi⟩
  · have p : 64 ≤ 2 ^ i := by
      calc 64 = 2 ^ 6 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

end PEqualNP.Outside.L_meta_50904

theorem PEqualNP.Outside.L_meta_50904 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (40 : Nat).testBit t.val ∧
    w.getD r.val false = (44 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, -, hnot, hsize, hval⟩
  have hok : ∀ g ∈ D.gates, PEqualNP.Outside.L_meta_50904.Ok g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, hlen⟩
  have hsem : ∀ t : Fin 6, ∀ i, (D.wires ((List.ofFn (fun j : Fin 5 => decide (j.val < t.val))) ++
      [false, true])).getD i false =
      ((PEqualNP.Outside.L_meta_50904.run PEqualNP.Outside.L_meta_50904.S0 D.gates).getD i 0).testBit t.val :=
    fun t => (PEqualNP.Outside.L_meta_50904.wires_sem t.isLt D.gates _ _ hok (by simp [PEqualNP.Outside.L_meta_50904.S0])
      (PEqualNP.Outside.L_meta_50904.base_sem t)).2
  have hlt := PEqualNP.Outside.L_meta_50904.run_lt D.gates PEqualNP.Outside.L_meta_50904.S0 (by decide)
  have hlen : (PEqualNP.Outside.L_meta_50904.run PEqualNP.Outside.L_meta_50904.S0 D.gates).length = 7 + D.size := by
    rw [PEqualNP.Outside.L_meta_50904.run_length]; rfl
  have get : ∀ (j : Fin (7 + D.size)) (c : Nat), c < 64 →
      (∀ t : Fin 6, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD j.val false
        = c.testBit t.val) →
      c ∈ PEqualNP.Outside.L_meta_50904.run PEqualNP.Outside.L_meta_50904.S0 D.gates := by
    intro j c hc hj
    have hjl : j.val < (PEqualNP.Outside.L_meta_50904.run PEqualNP.Outside.L_meta_50904.S0 D.gates).length := by
      rw [hlen]; exact j.isLt
    have hm := List.getElem_mem hjl
    rw [← List.getD_eq_getElem _ 0 hjl] at hm
    have e := PEqualNP.Outside.L_meta_50904.eq_of_bits (hlt _ hm) hc (fun t => by rw [← hsem t j.val, hj t])
    rwa [e] at hm
  have h6 := get p 6 (by decide) (fun t => (hval t).1)
  have h40 := get q 40 (by decide) (fun t => (hval t).2.1)
  have h44 := get r 44 (by decide) (fun t => (hval t).2.2)
  have hcan := PEqualNP.Outside.L_meta_50904.sound D.gates 5 2 PEqualNP.Outside.L_meta_50904.S0
    PEqualNP.Outside.L_meta_50904.S0 hok hsize hnot (fun x hx => hx) (by decide) (by decide) h6 h40 h44
  rw [PEqualNP.Outside.L_meta_50904.search_fails] at hcan
  exact Bool.false_ne_true hcan
