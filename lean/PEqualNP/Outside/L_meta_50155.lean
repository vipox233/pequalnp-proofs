import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50155_aux

open PEqualNP.CircuitLowerBounds

def setOf (l : List Nat) : Nat := l.foldr (fun v acc => acc ||| 1 <<< v) 0

def vals (m : Nat) : List Nat := (List.range 64).filter m.testBit

def bin (m : Nat) : Nat :=
  setOf (63 :: (vals m).flatMap fun a => (vals m).flatMap fun b => [a &&& b, a ||| b])

def neg (m : Nat) : Nat := setOf ((vals m).map fun a => 63 ^^^ a)

def miss (tg : List Nat) (m : Nat) : Nat := (tg.filter fun c => !m.testBit c).length

def search (tg : List Nat) : Nat → Nat → Nat → Bool
  | 0, m, _ => decide (miss tg m ≤ 0)
  | l+1, m, nots => decide (miss tg m ≤ l+1) && (search tg l m nots ||
      (List.range 64).any fun v => !m.testBit v &&
        (((bin m).testBit v && search tg l (m ||| 1 <<< v) nots) ||
         (decide (0 < nots) && (neg m).testBit v && search tg l (m ||| 1 <<< v) (nots - 1))))

def m0 : Nat := setOf [62, 60, 56, 48, 32, 0, 63]

theorem bit_or (m v c : Nat) : (m ||| 1 <<< v).testBit c = (m.testBit c || decide (v = c)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_setOf (l : List Nat) (c : Nat) : (setOf l).testBit c = decide (c ∈ l) := by
  induction l with
  | nil => simp [setOf]
  | cons a t ih =>
    have : setOf (a :: t) = setOf t ||| 1 <<< a := rfl
    rw [this, bit_or, ih]
    by_cases h2 : a = c
    · subst h2; simp
    · by_cases h1 : c ∈ t <;> simp [h1, h2, show ¬ c = a from fun h => h2 h.symm]

theorem mem_vals {m a : Nat} (ha : a < 64) (h : m.testBit a = true) : a ∈ vals m := by
  simp [vals, ha, h]

theorem miss_le (tg : List Nat) (hn : tg.Nodup) (m v : Nat) :
    miss tg m ≤ miss tg (m ||| 1 <<< v) + 1 := by
  have key : ∀ l : List Nat, miss l m ≤ miss l (m ||| 1 <<< v) + l.count v := by
    intro l
    induction l with
    | nil => simp [miss]
    | cons a t ih =>
      simp only [miss, List.filter_cons, List.count_cons, bit_or] at ih ⊢
      cases h1 : m.testBit a <;> by_cases h2 : v = a <;>
        simp [h2, Ne.symm (a := v)] at ih ⊢ <;> omega
  have := key tg
  have := List.nodup_iff_count_le_one.mp hn v
  omega

theorem search_miss (tg : List Nat) : ∀ (l m n : Nat), search tg l m n = true → miss tg m ≤ l
  | 0, m, n, h => by simpa [search] using h
  | l+1, m, n, h => by
    simp only [search, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

theorem search_of_done (tg : List Nat) (m n : Nat) (h : miss tg m = 0) :
    ∀ l, search tg l m n = true
  | 0 => by simp [search, h]
  | l+1 => by simp [search, h, search_of_done tg m n h l]

def enc (f : Fin 6 → Bool) : Nat :=
  (f 0).toNat + 2 * (f 1).toNat + 4 * (f 2).toNat + 8 * (f 3).toNat + 16 * (f 4).toNat + 32 * (f 5).toNat

theorem enc_lt (f : Fin 6 → Bool) : enc f < 64 := by
  unfold enc
  cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> cases f 5 <;> decide

theorem enc_and (f g : Fin 6 → Bool) : enc (fun t => f t && g t) = enc f &&& enc g := by
  simp only [enc]
  generalize f 0 = a0; generalize f 1 = a1; generalize f 2 = a2; generalize f 3 = a3
  generalize f 4 = a4; generalize f 5 = a5; generalize g 0 = b0; generalize g 1 = b1; generalize g 2 = b2
  generalize g 3 = b3; generalize g 4 = b4; generalize g 5 = b5
  revert a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5; decide

theorem enc_or (f g : Fin 6 → Bool) : enc (fun t => f t || g t) = enc f ||| enc g := by
  simp only [enc]
  generalize f 0 = a0; generalize f 1 = a1; generalize f 2 = a2; generalize f 3 = a3
  generalize f 4 = a4; generalize f 5 = a5; generalize g 0 = b0; generalize g 1 = b1; generalize g 2 = b2
  generalize g 3 = b3; generalize g 4 = b4; generalize g 5 = b5
  revert a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5; decide

theorem enc_not (f : Fin 6 → Bool) : enc (fun t => !f t) = 63 ^^^ enc f := by
  simp only [enc]
  generalize f 0 = a0; generalize f 1 = a1; generalize f 2 = a2; generalize f 3 = a3
  generalize f 4 = a4; generalize f 5 = a5
  revert a0 a1 a2 a3 a4 a5; decide

def col (W : Fin 6 → List Bool) (i : Nat) : Nat := enc fun t => (W t).getD i false

theorem gate_col (op : GateOp) (inputs : List Nat) (X : Fin 6 → Nat → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : inputs.length ≤ 2) :
    (enc fun t => op.eval (inputs.map (X t))) = 63 ∨
    (enc fun t => op.eval (inputs.map (X t))) = 0 ∨
    (∃ a b, (enc fun t => op.eval (inputs.map (X t))) = (enc fun t => X t a) &&& (enc fun t => X t b) ∨
      (enc fun t => op.eval (inputs.map (X t))) = (enc fun t => X t a) ||| (enc fun t => X t b)) ∨
      (op = GateOp.not ∧ ∃ a, (enc fun t => op.eval (inputs.map (X t))) = 63 ^^^ (enc fun t => X t a)) := by
  match inputs, hlen with
  | [], _ =>
    rcases hop with h | h | h <;> subst h
    · left; simp [GateOp.eval, enc]
    · right; left; simp [GateOp.eval, enc]
    · left; simp [GateOp.eval, enc]
  | [a], _ =>
    rcases hop with h | h | h <;> subst h
    · right; right; left; refine ⟨a, a, Or.inl ?_⟩
      simp [GateOp.eval]
    · right; right; left; refine ⟨a, a, Or.inl ?_⟩
      simp [GateOp.eval]
    · right; right; right; refine ⟨rfl, a, ?_⟩
      have : (fun t => GateOp.not.eval (List.map (X t) [a])) = fun t => !X t a := by
        funext t; simp [GateOp.eval]
      rw [this]; exact enc_not _
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h
    · right; right; left; refine ⟨a, b, Or.inl ?_⟩
      have : (fun t => GateOp.and.eval (List.map (X t) [a, b])) = fun t => X t a && X t b := by
        funext t; simp [GateOp.eval]
      rw [this]; exact enc_and _ _
    · right; right; left; refine ⟨a, b, Or.inr ?_⟩
      have : (fun t => GateOp.or.eval (List.map (X t) [a, b])) = fun t => X t a || X t b := by
        funext t; simp [GateOp.eval]
      rw [this]; exact enc_or _ _
    · right; right; right; refine ⟨rfl, a, ?_⟩
      have : (fun t => GateOp.not.eval (List.map (X t) [a, b])) = fun t => !X t a := by
        funext t; simp [GateOp.eval]
      rw [this]; exact enc_not _

def isNot (g : Gate) : Bool :=
  @decide (g.op = GateOp.not) (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq _ _)

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem main (tg : List Nat) (hn : tg.Nodup) (gs : List Gate) :
    ∀ (left nots m : Nat) (W : Fin 6 → List Bool) (L : Nat), (∀ t, (W t).length = L) →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gs.filter isNot).length ≤ nots → gs.length ≤ left →
    (∀ i, m.testBit (col W i) = true) →
    (∀ c ∈ tg, ∃ p, col (fun t => gs.foldl stepW (W t)) p = c) →
    search tg left m nots = true := by
  induction gs with
  | nil =>
    intro left nots m W L _ _ _ _ hinv htg
    apply search_of_done
    simp only [miss, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    obtain ⟨p, hp⟩ := htg c hc
    have := hinv p
    simp only [List.foldl_nil] at hp
    simp [← hp, this]
  | cons g gs ih =>
    intro left nots m W L hL hg hnot hlen hinv htg
    obtain ⟨l, rfl⟩ : ∃ l, left = l + 1 := ⟨left - 1, by simp at hlen; omega⟩
    have hlen' : gs.length ≤ l := by simpa using hlen
    have hg' := fun g' (h : g' ∈ gs) => hg g' (List.mem_cons_of_mem _ h)
    obtain ⟨hop, hil⟩ := hg g List.mem_cons_self
    let W1 : Fin 6 → List Bool := fun t => stepW (W t) g
    have hL1 : ∀ t, (W1 t).length = L + 1 := by intro t; simp [W1, stepW, hL t]
    have htg1 : ∀ c ∈ tg, ∃ p, col (fun t => gs.foldl stepW (W1 t)) p = c := htg
    let v := col W1 L
    have hv32 : v < 64 := enc_lt _
    have hcol : ∀ i, col W1 i = if i = L then v else col W i := by
      intro i
      by_cases hi : i = L
      · simp [hi, v]
      · simp only [hi, ite_false, col, W1, stepW]
        congr 1; funext t
        rcases Nat.lt_or_gt_of_ne hi with h | h
        · rw [List.getD_append _ _ _ _ (by rw [hL t]; exact h)]
        · rw [List.getD_eq_default _ _ (by simp [hL t]; omega),
            List.getD_eq_default _ _ (by rw [hL t]; omega)]
    have hzero : m.testBit 0 = true := by
      have := hinv L
      have h0 : col W L = 0 := by
        have e : ∀ t, (W t).getD L false = false :=
          fun t => List.getD_eq_default _ _ (by rw [hL t])
        have e' : (fun t => (W t).getD L false) = fun _ => false := funext e
        show enc (fun t => (W t).getD L false) = 0
        rw [e']; rfl
      rwa [h0] at this
    have hnot_le : (gs.filter isNot).length ≤ nots := by
      refine le_trans ?_ hnot
      simp only [List.filter_cons]; split <;> simp
    by_cases hin : m.testBit v = true
    · have h1 : search tg l m nots = true := by
        refine ih l nots m W1 (L + 1) hL1 hg' hnot_le hlen' ?_ htg1
        intro i; rw [hcol]; split
        · exact hin
        · exact hinv i
      have := search_miss tg _ _ _ h1
      simp only [search, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
      exact ⟨by omega, Or.inl h1⟩
    · have hinv1 : ∀ i, (m ||| 1 <<< v).testBit (col W1 i) = true := by
        intro i; rw [hcol, bit_or]; split
        · simp
        · simp [hinv i]
      have hmiss := miss_le tg hn m v
      have hv : v = enc fun t => g.op.eval (g.inputs.map fun i => (W t).getD i false) := by
        simp only [v, col, W1, stepW]
        congr 1; funext t
        rw [← hL t]; simp
      have hcl := gate_col g.op g.inputs (fun t i => (W t).getD i false) hop hil
      beta_reduce at hcl
      rw [← hv] at hcl
      have hbin : ∀ a b, (bin m).testBit (col W a &&& col W b) = true ∧
          (bin m).testBit (col W a ||| col W b) = true := by
        intro a b
        have ha : col W a ∈ vals m := mem_vals (enc_lt _) (hinv a)
        have hb : col W b ∈ vals m := mem_vals (enc_lt _) (hinv b)
        simp only [bin, testBit_setOf, decide_eq_true_eq, List.mem_cons, List.mem_flatMap]
        exact ⟨Or.inr ⟨_, ha, _, hb, Or.inl rfl⟩,
          Or.inr ⟨_, ha, _, hb, Or.inr (Or.inl rfl)⟩⟩
      have finish_bin : (bin m).testBit v = true → search tg (l + 1) m nots = true := by
        intro hb
        have h1 := ih l nots _ W1 (L + 1) hL1 hg' hnot_le hlen' hinv1 htg1
        have := search_miss tg _ _ _ h1
        simp only [search, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true,
          List.mem_range]
        refine ⟨by omega, Or.inr ⟨v, hv32, ?_, Or.inl ⟨hb, h1⟩⟩⟩
        simpa using hin
      rcases hcl with h | h | ⟨a, b, h | h⟩ | ⟨hopn, a, h⟩
      · apply finish_bin; rw [h]; simp [bin, testBit_setOf]
      · rw [h] at hin; exact absurd hzero hin
      · apply finish_bin; change v = col W a &&& col W b at h; rw [h]; exact (hbin a b).1
      · apply finish_bin; change v = col W a ||| col W b at h; rw [h]; exact (hbin a b).2
      · change v = 63 ^^^ col W a at h
        have hnots : (gs.filter isNot).length ≤ nots - 1 ∧
            0 < nots := by
          have : isNot g = true := by simp [isNot, hopn]
          simp only [List.filter_cons, this, ite_true, List.length_cons] at hnot
          omega
        have h1 := ih l (nots - 1) _ W1 (L + 1) hL1 hg' hnots.1 hlen' hinv1 htg1
        have := search_miss tg _ _ _ h1
        have hneg : (neg m).testBit v = true := by
          simp only [neg, testBit_setOf, decide_eq_true_eq, List.mem_map]
          exact ⟨_, mem_vals (enc_lt _) (hinv a), h.symm⟩
        simp only [search, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.any_eq_true,
          List.mem_range]
        refine ⟨by omega, Or.inr ⟨v, hv32, ?_, Or.inr ⟨⟨hnots.2, hneg⟩, h1⟩⟩⟩
        simpa using hin

def xs (t : Fin 6) : List Bool :=
  (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]

theorem inv0 : ∀ i, m0.testBit (col xs i) = true := by
  intro i
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
  | n + 7 =>
    have : col xs (n + 7) = 0 := by
      simp [col, enc, xs]
    rw [this]; decide

theorem no_circuit (tg : List Nat) (hn : tg.Nodup) (k nots : Nat)
    (hs : search tg k m0 nots = false) (D : Circuit)
    (hF : PEqualNP.MetaComplexity.FanInTwo D) (hN : PEqualNP.NotBracket.notCount D ≤ nots)
    (hk : D.size ≤ k) (htg : ∀ c ∈ tg, ∃ p, col (fun t => D.wires (xs t)) p = c) : False := by
  have := main tg hn D.gates k nots m0 xs 7 (by intro t; simp [xs]) ?_ hN hk inv0 htg
  · rw [hs] at this; exact absurd this (by decide)
  · intro g hg
    obtain ⟨h1, h2⟩ := hF g hg
    refine ⟨?_, h2⟩
    simpa using h1

theorem col_eq (W : Fin 6 → List Bool) (p c : Nat)
    (h : ∀ t : Fin 6, (W t).getD p false = c.testBit t.val) (hc : c < 64) : col W p = c := by
  have : col W p = enc fun t => c.testBit t.val := by
    simp only [col]; congr 1; funext t; exact h t
  rw [this]
  have : ∀ c < 64, (enc fun t => c.testBit t.val) = c := by decide
  exact this c hc

theorem search_false : search [6, 38, 44] 5 m0 2 = false := by decide +kernel

end PEqualNP.Outside.L_meta_50155_aux

open PEqualNP.Outside.L_meta_50155_aux in
theorem PEqualNP.Outside.L_meta_50155 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (38 : Nat).testBit t.val ∧
    w.getD r.val false = (44 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hF, -, hN, hk, h⟩
  refine no_circuit [6, 38, 44] (by decide) 5 2 search_false D hF hN hk ?_
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨p, col_eq _ _ _ (fun t => (h t).1) (by decide)⟩
  · exact ⟨q, col_eq _ _ _ (fun t => (h t).2.1) (by decide)⟩
  · exact ⟨r, col_eq _ _ _ (fun t => (h t).2.2) (by decide)⟩
