import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50830

open PEqualNP.CircuitLowerBounds

abbrev W := BitVec 6

def roots : List W := [62, 60, 56, 48, 32, 0, 63]
def goals : Finset W := {24, 30, 52}
def missing (bank : List W) : Nat := (goals \ bank.toFinset).card

theorem missing_insert (x : W) (bank : List W) :
    missing bank ≤ missing (x :: bank) + 1 := by
  have sub : goals \ bank.toFinset ⊆ insert x (goals \ (x :: bank).toFinset) := by
    intro y hy
    obtain ⟨hgoal, hy⟩ := Finset.mem_sdiff.mp hy
    by_cases e : y = x
    · exact Finset.mem_insert.mpr (Or.inl e)
    · apply Finset.mem_insert.mpr
      refine Or.inr (Finset.mem_sdiff.mpr ⟨hgoal, ?_⟩)
      simpa [e] using hy
  exact (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)

theorem missing_zero {bank : List W} (done : ∀ w ∈ goals, w ∈ bank) :
    missing bank = 0 := by
  apply Finset.card_eq_zero.mpr
  exact Finset.sdiff_eq_empty_iff_subset.mpr (fun w hw => List.mem_toFinset.mpr (done w hw))

def advance (next : List W → Bool) (bank : List W) (x : W) : Bool :=
  if x ∈ bank then false else next (x :: bank)

def search : Nat → Nat → List W → Bool
  | 0, _, bank => missing bank == 0
  | k + 1, n, bank =>
      if missing bank = 0 then true
      else if k + 1 < missing bank then false
      else search k n bank ||
        (bank.any fun a =>
          (bank.any fun b =>
            advance (search k n) bank (a &&& b) ||
            advance (search k n) bank (a ||| b)) ||
          (match n with
          | 0 => false
          | m + 1 => advance (search k m) bank (~~~a)))

theorem search_done {k n : Nat} {bank : List W} (h : missing bank = 0) :
    search k n bank = true := by
  cases k <;> simp [search, h]

theorem via_stay {k n : Nat} {bank : List W}
    (hle : missing bank ≤ k + 1) (cont : search k n bank = true) :
    search (k + 1) n bank = true := by
  by_cases h : missing bank = 0
  · exact search_done h
  · simp [search, h, Nat.not_lt_of_ge hle, cont]

theorem via_and {k n : Nat} {bank : List W} {a b : W}
    (hle : missing bank ≤ k + 1) (ha : a ∈ bank) (hb : b ∈ bank)
    (hf : a &&& b ∉ bank) (cont : search k n ((a &&& b) :: bank) = true) :
    search (k + 1) n bank = true := by
  by_cases hz : missing bank = 0
  · exact search_done hz
  · simp only [search, hz, ite_false, Nat.not_lt_of_ge hle, Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    refine ⟨a, ha, ?_⟩
    rw [Bool.or_eq_true]
    left
    apply List.any_eq_true.mpr
    refine ⟨b, hb, ?_⟩
    rw [Bool.or_eq_true]
    left
    simp [advance, hf, cont]

theorem via_or {k n : Nat} {bank : List W} {a b : W}
    (hle : missing bank ≤ k + 1) (ha : a ∈ bank) (hb : b ∈ bank)
    (hf : a ||| b ∉ bank) (cont : search k n ((a ||| b) :: bank) = true) :
    search (k + 1) n bank = true := by
  by_cases hz : missing bank = 0
  · exact search_done hz
  · simp only [search, hz, ite_false, Nat.not_lt_of_ge hle, Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    refine ⟨a, ha, ?_⟩
    rw [Bool.or_eq_true]
    left
    apply List.any_eq_true.mpr
    refine ⟨b, hb, ?_⟩
    rw [Bool.or_eq_true]
    right
    simp [advance, hf, cont]

theorem via_not {k n : Nat} {bank : List W} {a : W}
    (hle : missing bank ≤ k + 1) (ha : a ∈ bank)
    (hf : ~~~a ∉ bank) (cont : search k n (~~~a :: bank) = true) :
    search (k + 1) (n + 1) bank = true := by
  by_cases hz : missing bank = 0
  · exact search_done hz
  · simp only [search, hz, ite_false, Nat.not_lt_of_ge hle, Bool.or_eq_true]
    right
    apply List.any_eq_true.mpr
    refine ⟨a, ha, ?_⟩
    rw [Bool.or_eq_true]
    right
    simp [advance, hf, cont]

def readWord (words : List W) (i : Nat) : W := words.getD i 0

def gateWord (words : List W) (g : Gate) : W :=
  match g.op, g.inputs with
  | .and, [] => 63
  | .and, [i] => readWord words i
  | .and, i :: j :: _ => readWord words i &&& readWord words j
  | .or, [] => 0
  | .or, [i] => readWord words i
  | .or, i :: j :: _ => readWord words i ||| readWord words j
  | .not, [] => 63
  | .not, i :: _ => ~~~readWord words i
  | _, _ => 0

def evalWords (gs : List Gate) (input : List W) : List W :=
  gs.foldl (fun bank g => bank ++ [gateWord bank g]) input

def fit (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def countNot (gs : List Gate) : Nat :=
  (gs.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)).length

theorem read_mem {words bank : List W} (subs : ∀ w ∈ words, w ∈ bank)
    (hzero : 0 ∈ bank) (i : Nat) : readWord words i ∈ bank := by
  unfold readWord
  rw [List.getD_eq_getElem?_getD]
  cases e : words[i]? with
  | none => exact hzero
  | some x => exact subs x (List.mem_of_getElem? e)

theorem shortage (gs : List Gate) (words bank : List W)
    (subs : ∀ w ∈ words, w ∈ bank)
    (hgoal : ∀ w ∈ goals, w ∈ evalWords gs words) :
    missing bank ≤ gs.length := by
  induction gs generalizing words bank with
  | nil => exact Nat.le_of_eq (missing_zero fun w hw => subs w (hgoal w hw))
  | cons g gs ih =>
    let v := gateWord words g
    have hs : ∀ w ∈ words ++ [v], w ∈ v :: bank := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_cons_of_mem _ (subs w hw)
      · rw [List.mem_singleton.mp hw]
        exact List.mem_cons_self
    have h := ih (words ++ [v]) (v :: bank) hs hgoal
    have h' := missing_insert v bank
    simp only [List.length_cons]
    omega

theorem fits_search (gs : List Gate) (words bank : List W) (k n : Nat)
    (legal : ∀ g ∈ gs, fit g)
    (subs : ∀ w ∈ words, w ∈ bank)
    (hzero : (0 : W) ∈ bank) (hone : (63 : W) ∈ bank)
    (hs : gs.length ≤ k) (hn : countNot gs ≤ n)
    (hgoal : ∀ w ∈ goals, w ∈ evalWords gs words) :
    search k n bank = true := by
  induction gs generalizing words bank k n with
  | nil => exact search_done (missing_zero fun w hw => subs w (hgoal w hw))
  | cons g gs ih =>
    cases k with
    | zero => simp at hs
    | succ k =>
      have hshort : missing bank ≤ k + 1 := by
        have h := shortage (g :: gs) words bank subs hgoal
        omega
      have hfit := legal g List.mem_cons_self
      have rest : ∀ d ∈ gs, fit d := fun d hd => legal d (List.mem_cons_of_mem _ hd)
      have hs' : gs.length ≤ k := by simpa using hs
      let v := gateWord words g
      have targetRest : ∀ w ∈ goals, w ∈ evalWords gs (words ++ [v]) := hgoal
      have takeNew (m : Nat) (hm : countNot gs ≤ m) :
          search k m (v :: bank) = true := by
        apply ih (words ++ [v]) (v :: bank) k m rest ?_
          (List.mem_cons_of_mem _ hzero) (List.mem_cons_of_mem _ hone) hs' hm targetRest
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_cons_of_mem _ (subs w hw)
        · rw [List.mem_singleton.mp hw]
          exact List.mem_cons_self
      have hrestNot : countNot gs ≤ n := by
        unfold countNot at *
        by_cases hg : g.op = .not <;> simp [hg] at hn <;> omega
      by_cases hv : v ∈ bank
      · apply via_stay hshort
        apply ih (words ++ [v]) bank k n rest ?_ hzero hone hs' hrestNot targetRest
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact subs w hw
        · rwa [List.mem_singleton.mp hw]
      · have available := read_mem subs hzero
        obtain ⟨hop, hlen⟩ := hfit
        obtain ⟨op, ins⟩ := g
        simp only at hop
        rcases hop with rfl | rfl | rfl
        · rcases ins with _ | ⟨i, _ | ⟨j, tail⟩⟩
          · exact (hv hone).elim
          · exact (hv (available i)).elim
          · exact via_and hshort (available i) (available j) hv (takeNew n hrestNot)
        · rcases ins with _ | ⟨i, _ | ⟨j, tail⟩⟩
          · exact (hv hzero).elim
          · exact (hv (available i)).elim
          · exact via_or hshort (available i) (available j) hv (takeNew n hrestNot)
        · cases ins with
          | nil => exact (hv hone).elim
          | cons i tl =>
            have hn' : countNot gs + 1 ≤ n := by simpa [countNot] using hn
            cases n with
            | zero => omega
            | succ m =>
              exact via_not hshort (available i) hv (takeNew m (by omega))

def bit (t : Fin 6) (w : W) : Bool := w.getLsbD t.val
def boolInputs (t : Fin 6) : List Bool :=
  List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false, true]

theorem roots_bits : ∀ t : Fin 6, roots.map (bit t) = boolInputs t := by decide +kernel

theorem map_read (t : Fin 6) (words : List W) (i : Nat) :
    (words.map (bit t)).getD i false = bit t (readWord words i) := by
  simp only [readWord, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases words[i]? <;> simp [bit]

theorem gate_bits (t : Fin 6) (words : List W) (g : Gate) (hg : fit g) :
    bit t (gateWord words g) =
      g.op.eval (g.inputs.map fun i => (words.map (bit t)).getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hn⟩ := hg
  simp only at hop hn
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, tail⟩⟩⟩
    · show (63 : W).getLsbD t.val = true
      have h : ∀ t : Fin 6, (63 : W).getLsbD t.val = true := by decide +kernel
      exact h t
    · simp only [gateWord, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, map_read, id_eq]
    · simp only [gateWord, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, map_read, id_eq]
      exact BitVec.getLsbD_and
    · simp at hn
  · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, tail⟩⟩⟩
    · simp [gateWord, GateOp.eval, bit]
    · simp only [gateWord, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, map_read, id_eq]
    · simp only [gateWord, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, map_read, id_eq]
      exact BitVec.getLsbD_or
    · simp at hn
  · rcases ins with _ | ⟨i, tail⟩
    · show (63 : W).getLsbD t.val = true
      have h : ∀ t : Fin 6, (63 : W).getLsbD t.val = true := by decide +kernel
      exact h t
    · simp only [gateWord, GateOp.eval, List.map_cons, List.headD_cons, map_read]
      simp [bit, t.isLt]

theorem eval_bits (t : Fin 6) (gs : List Gate) (words : List W)
    (h : ∀ g ∈ gs, fit g) :
    (evalWords gs words).map (bit t) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (words.map (bit t)) := by
  induction gs generalizing words with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalWords, List.foldl_cons]
    rw [show (gs.foldl (fun w d => w ++ [gateWord w d]) (words ++ [gateWord words g])) =
         evalWords gs (words ++ [gateWord words g]) by rfl]
    rw [ih _ (fun d hd => h d (List.mem_cons_of_mem _ hd))]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [gate_bits _ _ _ (h g List.mem_cons_self)]

theorem read_circuit (D : Circuit) (legal : ∀ g ∈ D.gates, fit g) (t : Fin 6) (i : Nat) :
    bit t (readWord (evalWords D.gates roots) i) = (D.wires (boolInputs t)).getD i false := by
  rw [← map_read, eval_bits _ _ _ legal, roots_bits]
  rfl

theorem recover {a b : W} (h : ∀ t : Fin 6, bit t a = bit t b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h ⟨i, hi⟩

def binaryMoves (bank : List W) : List W :=
  (bank.flatMap fun a => bank.flatMap fun b => [a &&& b, a ||| b]).eraseDups

def unaryMoves (bank : List W) : List W := (bank.map (fun a => ~~~a)).eraseDups

def compressed : Nat → Nat → List W → Bool
  | 0, _, bank => missing bank == 0
  | k + 1, n, bank =>
      if missing bank = 0 then true
      else if k + 1 < missing bank then false
      else compressed k n bank ||
        ((binaryMoves bank).any (advance (compressed k n) bank) ||
          match n with
          | 0 => false
          | m + 1 => (unaryMoves bank).any (advance (compressed k m) bank))

theorem advance_implication {f g : List W → Bool} {bank : List W} {x : W}
    (imp : f (x :: bank) = true → g (x :: bank) = true)
    (found : advance f bank x = true) : advance g bank x = true := by
  by_cases present : x ∈ bank
  · simp [advance, present] at found
  · simpa only [advance, ite_eq_right present] using imp (by simpa only [advance, ite_eq_right present] using found)

theorem compressed_complete (k n : Nat) (bank : List W) :
    search k n bank = true → compressed k n bank = true := by
  induction k generalizing n bank with
  | zero => exact id
  | succ k ih =>
    intro found
    by_cases done : missing bank = 0
    · simp [compressed, done]
    by_cases impossible : k + 1 < missing bank
    · simp [search, done, impossible] at found
    simp only [search, compressed, done, impossible, ite_false, Bool.or_eq_true, List.any_eq_true] at found ⊢
    rcases found with prev | ⟨a, ha, many | negated⟩
    · exact Or.inl (ih n bank prev)
    · obtain ⟨b, hb, step⟩ := many
      have move (v : W) (hv : v ∈ [a &&& b, a ||| b]) : v ∈ binaryMoves bank := by
        apply List.mem_eraseDups.mpr
        exact List.mem_flatMap.mpr ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, hv⟩⟩
      rcases step with step | step
      · exact Or.inr (.inl ⟨a &&& b, move _ (by simp), advance_implication (ih n _) step⟩)
      · exact Or.inr (.inl ⟨a ||| b, move _ (by simp), advance_implication (ih n _) step⟩)
    · cases n with
      | zero => contradiction
      | succ n =>
        have move : ~~~a ∈ unaryMoves bank :=
          List.mem_eraseDups.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)
        exact Or.inr (.inr (List.any_eq_true.mpr ⟨~~~a, move, advance_implication (ih n _) negated⟩))

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem compressed_rejected : compressed 5 2 roots = false := by decide +kernel

theorem rejected : search 5 2 roots = false := by
  cases eq : search 5 2 roots with
  | false => rfl
  | true =>
    have impossible := compressed_complete 5 2 roots eq
    rw [compressed_rejected] at impossible
    exact Bool.noConfusion impossible

end PEqualNP.Outside.L_meta_50830

open PEqualNP.Outside.L_meta_50830 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_50830 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (24 : Nat).testBit t.val ∧
    w.getD q.val false = (30 : Nat).testBit t.val ∧
    w.getD r.val false = (52 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, _, hnot, hsize, hs⟩
  have legal : ∀ g ∈ D.gates, fit g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    exact ⟨by simpa using hop, hlen⟩
  let words := evalWords D.gates roots
  have one (i : Nat) (w : W) (hw : ∀ t : Fin 6, (D.wires (boolInputs t)).getD i false = bit t w) : readWord words i = w :=
    recover fun t => (read_circuit D legal t i).trans (hw t)
  have hp : readWord words p.val = 24 := one p.val 24 fun t => (hs t).1
  have hq : readWord words q.val = 30 := one q.val 30 fun t => (hs t).2.1
  have hr : readWord words r.val = 52 := one r.val 52 fun t => (hs t).2.2
  have present (i : Nat) (w : W) (hw : w ≠ 0) (eq : readWord words i = w) : w ∈ words := by
    unfold readWord at eq
    rw [List.getD_eq_getElem?_getD] at eq
    cases e : words[i]? with
    | none =>
        have hz : (0 : W) = w := by simpa only [e, Option.getD_none] using eq
        exact (hw hz.symm).elim
    | some x =>
        have h : x = w := by simpa only [e, Option.getD_some] using eq
        exact h ▸ List.mem_of_getElem? e
  have allGoals : ∀ w ∈ goals, w ∈ evalWords D.gates roots := by
    intro w hw
    simp [goals] at hw
    rcases hw with rfl | rfl | rfl
    · exact present p.val 24 (by decide) hp
    · exact present q.val 30 (by decide) hq
    · exact present r.val 52 (by decide) hr
  have actual := fits_search D.gates roots roots 5 2 legal (fun _ h => h)
     (by decide) (by decide) hsize hnot allGoals
  rw [rejected] at actual
  exact Bool.noConfusion actual
