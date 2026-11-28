import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepInduced
import PEqualNP.MetaComplexity.L100
import PEqualNP.Outside.L_meta_18508

namespace PEqualNP.Outside.L_meta_30581

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Represents (oneEach Represents RepSizeAtMost)

def edge (x y : Nat) : Bool :=
  (64478 : Nat).testBit (4 * min x 3 + min y 3)

private theorem edge_spec (x y : Nat) : edge x y = !decide (x = y ∧ x < 3) := by
  have small : ∀ a b : Fin 4, (64478 : Nat).testBit (4*a.val+b.val) =
      !decide (a.val = b.val ∧ a.val < 3) := by decide
  unfold edge
  rw [small ⟨min x 3, by omega⟩ ⟨min y 3, by omega⟩]
  have h : (min x 3 = min y 3 ∧ min x 3 < 3) ↔ (x=y ∧ x<3) := by omega
  simp only [h]

private def low {n : Nat} (h : 3 ≤ n) : Finset (Fin n) :=
  Finset.univ.map (Fin.castLEEmb h)

private theorem mem_low {n : Nat} (h : 3 ≤ n) (i : Fin n) : i ∈ low h ↔ i.val < 3 := by
  simp only [low, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a,rfl⟩
    exact a.isLt
  · intro hi
    exact ⟨⟨i.val,hi⟩,rfl⟩

private theorem card_low {n : Nat} (h : 3 ≤ n) : (low h).card = 3 := by simp [low]

private theorem adjacent_low {m : Nat} (h : 3 ≤ m) (x : Nat) :
    ∃ j : Fin m, j.val < 3 ∧ edge x j.val = true := by
  by_cases hx : x = 0
  · exact ⟨⟨1,by omega⟩, by change 1 < 3; decide, by simp [edge_spec,hx]⟩
  · exact ⟨⟨0,by omega⟩, by change 0 < 3; decide, by simp [edge_spec,hx]⟩

private theorem edge_symm (x y : Nat) : edge x y = edge y x := by
  rw [edge_spec,edge_spec]
  by_cases h : x=y
  · subst y; rfl
  · simp [h,Ne.symm h]

-- Takes exactly the recorded type of L-meta-7872 as its first argument.
abbrev InducedBound : Prop :=
∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m)), (∀ u ∈ R, ∃ v ∈ K, A u v = false) → (∀ v ∈ K, ∃ u ∈ R, A u v = false) → (∃ u ∈ R, ∃ v ∈ K, A u v = true) → PEqualNP.Represents.RepSizeAtMost A s → ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card)

theorem saved (induced : InducedBound) (n m s : Nat) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (source : Represents.RepSizeAtMost (fun (i : Fin n) (j : Fin m) => edge i.val j.val) s) :
    ∃ t : Nat, Represents.RepSizeAtMost
        (fun (i : Fin n) (j : Fin m) => edge i.val j.val && decide (i.val < 3) && decide (j.val < 3)) t ∧
      t + (n+m) ≤ s + 6 := by
  let A := fun (i : Fin n) (j : Fin m) => edge i.val j.val
  have missR (i : Fin n) (hi : i ∈ low hn) : ∃ j ∈ low hm, A i j = false := by
    have h := (mem_low hn i).mp hi
    exact ⟨⟨i.val,by omega⟩, (mem_low hm _).mpr h, by simp [A,edge_spec,h]⟩
  have missK (j : Fin m) (hj : j ∈ low hm) : ∃ i ∈ low hn, A i j = false := by
    have h := (mem_low hm j).mp hj
    exact ⟨⟨j.val,by omega⟩, (mem_low hn _).mpr h, by simp [A,edge_spec,h]⟩
  have hit : ∃ i ∈ low hn, ∃ j ∈ low hm, A i j = true := by
    exact ⟨⟨0,by omega⟩, (mem_low hn _).mpr (by change 0 < 3; decide), ⟨1,by omega⟩,
      (mem_low hm _).mpr (by change 1 < 3; decide), by change edge 0 1 = true; decide⟩
  have activeR (a : Fin n) : ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false := by
    obtain ⟨b,hb,ab⟩ := adjacent_low hm a.val
    obtain ⟨a',_,zero⟩ := missK b ((mem_low hm _).mpr hb)
    exact ⟨b,ab,a',zero⟩
  have activeK (b : Fin m) : ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false := by
    obtain ⟨a,ha,ba⟩ := adjacent_low hn b.val
    obtain ⟨b',_,zero⟩ := missR a ((mem_low hn _).mpr ha)
    exact ⟨a, (edge_symm _ _).trans ba,b',zero⟩
  obtain ⟨t,rep,budget⟩ := induced n m s A (low hn) (low hm) missR missK hit source
  have r := Finset.card_filter_le (low hn) (fun a => ∃ b ∈ low hm, A a b = true)
  have c := Finset.card_filter_le (low hm) (fun b => ∃ a ∈ low hn, A a b = true)
  simp [activeR,activeK] at budget
  rw [card_low] at r c
  exact ⟨t,by simpa only [A,mem_low] using rep,by omega⟩

/-- Raw inputs outside the retained banks go to a wire beyond the whole new circuit.
Gate indices keep their offset from the end of the raw inputs. -/
private def wire (n m a b dead w : Nat) : Nat :=
  if w < n then (if w < a then w else dead)
  else if w < n + m then (if w - n < b then a + (w - n) else dead)
  else a + b + (w - (n + m))

private def rename (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

private def prefixStep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]

private theorem lengthInput {a b : Nat} (u : Fin a) (v : Fin b) : (oneEach u v).length = a + b := by
  simp [oneEach]

private theorem readInput {a b : Nat} (u : Fin a) (v : Fin b) (i : Nat) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = a + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold oneEach
  by_cases hi : i < a
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff, show i ≠ a + v.val by omega]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_ofFn]
    by_cases hj : i - a < b
    · simp [List.getD_eq_getElem?_getD, hj, Fin.ext_iff, show i ≠ u.val by omega,
        show i - a = v.val ↔ i = a + v.val by omega]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [show i ≠ u.val by omega, show i ≠ a + v.val by omega]

private theorem readPrefix {n m a b N : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (u : Fin a) (v : Fin b) (tail : List Bool) (ht : tail.length ≤ N) (w : Nat) :
    (oneEach u v ++ tail).getD (wire n m a b (a + b + N) w) false =
    (oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail).getD w false := by
  have hu := u.isLt
  have hv := v.isLt
  by_cases raw : w < n + m
  · conv_rhs => rw [List.getD_append _ _ _ _ (by rwa [lengthInput]), readInput]
    simp only [Fin.val_castLE]
    by_cases left : w < n
    · by_cases kept : w < a
      · simp only [wire, if_pos left, if_pos kept]
        rw [List.getD_append _ _ _ _ (by rw [lengthInput]; omega), readInput]
        simp [show w ≠ a + v.val by omega, show w ≠ n + v.val by omega]
      · simp only [wire, if_pos left, if_neg kept]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, lengthInput]; omega)]
        simp [show w ≠ u.val by omega, show w ≠ n + v.val by omega]
    · by_cases kept : w - n < b
      · simp only [wire, if_neg left, if_pos raw, if_pos kept]
        rw [List.getD_append _ _ _ _ (by rw [lengthInput]; omega), readInput]
        simp [show a + (w - n) ≠ u.val by omega, show w ≠ u.val by omega,
          show a + (w - n) = a + v.val ↔ w = n + v.val by omega] <;> omega
      · simp only [wire, if_neg left, if_pos raw, if_neg kept]
        rw [List.getD_eq_default _ _ (by rw [List.length_append, lengthInput]; omega)]
        simp [show w ≠ u.val by omega, show w ≠ n + v.val by omega]
  · simp only [wire, if_neg (show ¬ w < n by omega), if_neg raw]
    rw [List.getD_append_right _ _ _ _ (by rw [lengthInput]; omega),
      List.getD_append_right _ _ _ _ (by rw [lengthInput]; omega), lengthInput, lengthInput]
    congr 1
    omega

private theorem simulation {n m a b N : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (u : Fin a) (v : Fin b) (gs : List Gate) (tail : List Bool) (h : tail.length + gs.length ≤ N) :
    let r := wire n m a b (a + b + N)
    ∃ out : List Bool, out.length ≤ N ∧
      (gs.map (rename r)).foldl prefixStep (oneEach u v ++ tail) = oneEach u v ++ out ∧
      gs.foldl prefixStep (oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail) =
        oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ out := by
  induction gs generalizing tail with
  | nil => exact ⟨tail, by simpa using h, rfl, rfl⟩
  | cons g rest ih =>
    let old := oneEach (Fin.castLE ha u) (Fin.castLE hb v) ++ tail
    let bit := g.op.eval (g.inputs.map fun k => old.getD k false)
    have ht : tail.length ≤ N := by omega
    have same : (rename (wire n m a b (a + b + N)) g).op.eval
        ((rename (wire n m a b (a + b + N)) g).inputs.map fun k =>
          (oneEach u v ++ tail).getD k false) = bit := by
      simp only [rename, List.map_map, Function.comp_def, readPrefix ha hb u v tail ht, bit, old]
    have bound : (tail ++ [bit]).length + rest.length ≤ N := by
      simp only [List.length_cons] at h
      simp; omega
    simpa only [List.map_cons, List.foldl_cons, prefixStep, same, List.append_assoc, bit, old]
      using ih (tail ++ [bit]) bound

/-- Keeping an initial segment of each bank costs no gates, including for forward or missing reads. -/
theorem restrictPrefix {n m a b s : Nat} (ha : a ≤ n) (hb : b ≤ m)
    (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) :
    RepSizeAtMost (fun i j => A (Fin.castLE ha i) (Fin.castLE hb j)) s := by
  obtain ⟨C, mono, size, rep⟩ := h
  let r := wire n m a b (a + b + C.size)
  let D : Circuit := ⟨C.gates.map (rename r), r C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    simpa [rename] using mono f hf
  · simpa [D, Circuit.size] using size
  · intro u v
    obtain ⟨out, len, hnew, hold⟩ :=
      simulation (N := C.size) ha hb u v C.gates [] (by simp [Circuit.size])
    simp only [List.append_nil] at hnew hold
    have val := rep (Fin.castLE ha u) (Fin.castLE hb v)
    change (C.gates.foldl prefixStep _).getD C.output false = _ at val
    change ((C.gates.map (rename r)).foldl prefixStep _).getD (r C.output) false = _
    rw [hnew, readPrefix ha hb u v out len, ← hold, val]

/-- The clamped rectangular graph restricted to four rows and columns is mask 854. -/

private def step (v : List Bool) (g : Gate) : List Bool :=
  v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]

private def core (n total : Nat) : List Gate :=
  [⟨.or, [0,n]⟩, ⟨.or, [1,n+1]⟩, ⟨.or, [2,n+2]⟩,
   ⟨.and, [total,total+1]⟩, ⟨.or, [total,total+1]⟩,
   ⟨.and, [total+4,total+2]⟩, ⟨.or, [total+3,total+5]⟩]

private def bits (xs : List Bool) (n : Nat) : List Bool :=
  let p := xs.getD 0 false || xs.getD n false
  let q := xs.getD 1 false || xs.getD (n+1) false
  let r := xs.getD 2 false || xs.getD (n+2) false
  [p,q,r,p && q,p || q,(p || q) && r,(p && q) || ((p || q) && r)]

private theorem core_run (xs : List Bool) (n : Nat) (h : n+2 < xs.length) :
    (core n xs.length).foldl step xs = xs ++ bits xs n := by
  have raw (ls : List Bool) (j : Nat) (hj : j < xs.length) :
      (xs ++ ls).getD j false = xs.getD j false := List.getD_append _ _ _ _ hj
  have added (ls : List Bool) (j : Nat) :
      (xs ++ ls).getD (xs.length+j) false = ls.getD j false := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega
  have first (ls : List Bool) :
      (xs ++ ls).getD xs.length false = ls.getD 0 false := by simpa using added ls 0
  simp (disch := omega) only [core, step, bits, GateOp.eval, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false, Bool.and_true, List.append_assoc, List.cons_append, List.nil_append,
    added, first, raw, List.getD_cons_zero, List.getD_cons_succ, Nat.reduceAdd]

private def chain (last : Nat) : List Nat → List Gate
  | [] => []
  | w :: ws => ⟨.or,[last,w]⟩ :: chain (last+1) ws

private theorem chain_len (last : Nat) (ws : List Nat) : (chain last ws).length = ws.length := by
  induction ws generalizing last with
  | nil => rfl
  | cons _ _ ih => simp [chain, ih]

private theorem chain_pos (last : Nat) (ws : List Nat) :
    ∀ g ∈ chain last ws, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing last with
  | nil => simp [chain]
  | cons w ws ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | keep
    · simp
    · exact ih (last+1) g keep

private theorem anyAgree (xs : List Nat) (p q : Nat → Bool)
    (agree : ∀ k ∈ xs, p k = q k) : xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons k rest ih =>
    rw [List.any_cons, List.any_cons, agree k (by simp), ih (fun t ht => agree t (by simp [ht]))]

private theorem chain_run (xs : List Bool) (last : Nat) (ws : List Nat)
    (len : xs.length = last+1) (early : ∀ w ∈ ws, w < xs.length) :
    ((chain last ws).foldl step xs).getD (last+ws.length) false =
      (xs.getD last false || ws.any (fun w => xs.getD w false)) := by
  induction ws generalizing xs last with
  | nil => simp [chain]
  | cons w ws ih =>
    let v := xs.getD last false || xs.getD w false
    have e : ∀ k ∈ ws, k < xs.length := fun k hk => early k (List.mem_cons_of_mem _ hk)
    have eq : step xs ⟨GateOp.or,[last,w]⟩ = xs ++ [v] := by simp [step, v, GateOp.eval]
    have lastVal : (xs ++ [v]).getD (last+1) false = v := by
      rw [← len, List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
      rfl
    have other : ws.any (fun k => (xs ++ [v]).getD k false) = ws.any (fun k => xs.getD k false) := by
      apply anyAgree
      intro k hk
      exact List.getD_append _ _ _ _ (e k hk)
    simp only [chain,List.foldl_cons,List.length_cons,List.any_cons,eq]
    rw [show last+(ws.length+1) = (last+1)+ws.length by omega,
      ih (xs ++ [v]) (last+1) (by simp [len]) (by intro k hk; specialize e k hk; simp; omega),
      lastVal,other]
    exact Bool.or_assoc _ _ _

private def extras (n m : Nat) : List Nat :=
  ((List.range (n-3)).map (fun t => 3+t)) ++ ((List.range (m-3)).map (fun t => n+3+t))

private theorem extras_mem (n m k : Nat) :
    k ∈ extras n m ↔ (3 ≤ k ∧ k < n) ∨ (n+3 ≤ k ∧ k < n+m) := by
  simp only [extras, List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩)
    · left; omega
    · right; omega
  · rintro (h | h)
    · left; exact ⟨k-3,by omega,by omega⟩
    · right; exact ⟨k-(n+3),by omega,by omega⟩

private theorem rawBit {n m : Nat} (i : Fin n) (j : Fin m) (w : Nat) :
    (Represents.oneEach i j).getD w false = decide (w = i.val ∨ w = n+j.val) := by
  unfold Represents.oneEach
  by_cases lw : w < n
  · rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using lw)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using lw)]
    simp only [List.getElem_ofFn, Fin.ext_iff, decide_eq_decide]
    omega
  · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
    simp only [List.length_ofFn]
    by_cases rw' : w-n < m
    · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using rw')]
      simp only [List.getElem_ofFn, Fin.ext_iff, decide_eq_decide]
      omega
    · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]
      have neither : ¬(w=i.val ∨ w=n+j.val) := by omega
      simp [neither]

private def flag (a b k : Nat) : Bool := decide (a=k) || decide (b=k)

private def vote (a b c : Bool) : Bool := (a && b) || ((a || b) && c)

private theorem graphFormula (a b : Nat) :
    (vote (flag a b 0) (flag a b 1) (flag a b 2) || decide (3 ≤ a ∨ 3 ≤ b)) =
    (64478 : Nat).testBit (4 * min a 3 + min b 3) := by
  have control : ∀ i j : Fin 4,
      (vote (flag i.val j.val 0) (flag i.val j.val 1) (flag i.val j.val 2) ||
        decide (3 ≤ i.val ∨ 3 ≤ j.val)) = (64478 : Nat).testBit (4*i.val+j.val) := by decide
  have low (x k : Nat) (h : k < 3) : (min x 3 = k) ↔ x=k := by omega
  have high (x : Nat) : 3 ≤ min x 3 ↔ 3 ≤ x := by omega
  simpa (disch := decide) only [flag, low, high] using
    control ⟨min a 3,by omega⟩ ⟨min b 3,by omega⟩

private theorem extraValue {n m : Nat} (i : Fin n) (j : Fin m) :
    (extras n m).any (fun w => (Represents.oneEach i j).getD w false) =
      decide (3 ≤ i.val ∨ 3 ≤ j.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, extras_mem, rawBit, decide_eq_true_eq]
  constructor
  · rintro ⟨w, h, h'⟩
    omega
  · rintro (hi | hj)
    · exact ⟨i.val, Or.inl ⟨hi,i.isLt⟩, Or.inl rfl⟩
    · exact ⟨n+j.val, Or.inr ⟨by omega,by omega⟩, Or.inr rfl⟩

private theorem coreValue {n m : Nat} (hn : 3 ≤ n) (hm : 3 ≤ m) (i : Fin n) (j : Fin m) :
    (bits (Represents.oneEach i j) n).getD 6 false =
      vote (flag i.val j.val 0) (flag i.val j.val 1) (flag i.val j.val 2) := by
  have left (k : Nat) (hk : k < 3) :
      (Represents.oneEach i j).getD k false = decide (i.val=k) := by
    rw [rawBit, decide_eq_decide]; omega
  have right (k : Nat) (hk : k < 3) :
      (Represents.oneEach i j).getD (n+k) false = decide (j.val=k) := by
    rw [rawBit, decide_eq_decide]; omega
  have right0 := right 0 (by decide)
  rw [Nat.add_zero] at right0
  simp (disch := decide) only [bits, List.getD_cons_succ, List.getD_cons_zero,
    left, right, right0, vote, flag]

theorem threeHoleUpper :
∀ (n m : Nat), 3 ≤ n → 3 ≤ m →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = n + m + 1 ∧
      PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin m) =>
        (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)) C := by
  intro n m hn hm
  let N := n+m
  let rest := extras n m
  let C : Circuit := ⟨core n N ++ chain (N+6) rest, N+6+rest.length⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ core n N ++ chain (N+6) rest at hg
    rcases List.mem_append.mp hg with hc | he
    · simp only [core, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using chain_pos (N+6) rest g he
  · change (core n N ++ chain (N+6) rest).length = n+m+1
    simp only [List.length_append, chain_len, rest, extras, List.length_map,List.length_range]
    change 7 + ((n-3)+(m-3)) = n+m+1
    omega
  · intro i j
    let xs := Represents.oneEach i j
    have len : xs.length = N := by simp [xs, N, Represents.oneEach]
    have bLen : (bits xs n).length = 7 := rfl
    have short : ∀ w ∈ rest, w < xs.length := by
      intro w hw
      rcases (extras_mem n m w).mp hw with h | h <;> dsimp [N] at len <;> omega
    have init : (core n N).foldl step xs = xs ++ bits xs n := by
      rw [← len]; exact core_run xs n (by dsimp [N] at len; omega)
    have past : (xs ++ bits xs n).getD (N+6) false = (bits xs n).getD 6 false := by
      rw [List.getD_append_right _ _ _ _ (by omega),len]
      congr 1
      omega
    have same : rest.any (fun w => (xs ++ bits xs n).getD w false) =
        rest.any (fun w => xs.getD w false) := by
      apply anyAgree
      intro w hw
      exact List.getD_append _ _ _ _ (short w hw)
    change ((core n N ++ chain (N+6) rest).foldl step xs).getD (N+6+rest.length) false = _
    rw [List.foldl_append,init,chain_run _ _ _ (by simp [len,bLen])
      (by intro w hw; specialize short w hw; simp [bLen]; omega),past,same,
      coreValue hn hm i j,extraValue i j]
    exact graphFormula i.val j.val

/-- The value of wire `k` on the point set `X`: input wires read membership, gate wires apply
their operation to the wires they read (a wire not yet existing reads false), and a wire past
the end reads false. -/
def val (n : ℕ) (gs : List Gate) (X : Finset (Fin n)) (k : ℕ) : Bool :=
  if h : k < n then decide (⟨k, h⟩ ∈ X)
  else if h2 : k - n < gs.length then
    (gs[k - n]).op.eval
      ((gs[k - n]).inputs.map (fun j => if hj : j < k then val n gs X j else false))
  else false
termination_by k
decreasing_by exact hj

theorem val_input {n : ℕ} {gs : List Gate} {X : Finset (Fin n)} {k : ℕ} (h : k < n) :
    val n gs X k = decide (⟨k, h⟩ ∈ X) := by
  rw [val]; simp [h]

theorem val_gate {n : ℕ} {gs : List Gate} {X : Finset (Fin n)} {k : ℕ} (h : ¬ k < n)
    (h2 : k - n < gs.length) :
    val n gs X k = (gs[k - n]).op.eval
      ((gs[k - n]).inputs.map (fun j => if j < k then val n gs X j else false)) := by
  rw [val]; simp only [h, h2, dite_false, dite_true]
  congr 2

theorem val_past {n : ℕ} {gs : List Gate} {X : Finset (Fin n)} {k : ℕ}
    (h : n + gs.length ≤ k) : val n gs X k = false := by
  rw [val]
  have h1 : ¬ k < n := by omega
  have h2 : ¬ k - n < gs.length := by omega
  simp [h1, h2]

/-- The gate-by-gate fold of `Circuit.wires`, after `j` gates, lists the values `val`. -/
theorem foldl_take {n : ℕ} (gs : List Gate) (X : Finset (Fin n)) :
    ∀ j, j ≤ gs.length →
    (gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn (fun v : Fin n => decide (v ∈ X)))
      = List.ofFn (fun k : Fin (n + j) => val n gs X k) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [List.take_zero, List.foldl_nil]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.length_ofFn] at h1
      simp [val_input h1]
  | succ j ih =>
    intro hj
    have hj' : j < gs.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some, List.foldl_append,
      ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp only [List.length_append, List.length_ofFn, List.length_singleton] at h1
      by_cases hk : k < n + j
      · rw [List.getElem_append_left (by simpa using hk)]
        simp only [List.getElem_ofFn]
      · have hk' : k = n + j := by omega
        subst hk'
        rw [List.getElem_append_right (by simp)]
        simp only [List.length_ofFn, Nat.sub_self, List.getElem_singleton, List.getElem_ofFn]
        rw [val_gate (by omega) (by omega)]
        have : n + j - n = j := by omega
        simp only [this]
        congr 2
        funext i
        by_cases hi : i < n + j
        · simp [List.getD_eq_getElem?_getD, hi]
        · simp [List.getD_eq_getElem?_getD, hi]

theorem eval_eq {n : ℕ} (gs : List Gate) (X : Finset (Fin n)) (o : ℕ) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn fun v : Fin n => decide (v ∈ X)) = val n gs X o := by
  unfold Circuit.eval Circuit.wires
  simp only
  have := foldl_take gs X gs.length le_rfl
  rw [List.take_length] at this
  rw [this]
  by_cases ho : o < n + gs.length
  · simp [List.getD_eq_getElem?_getD, ho]
  · rw [val_past (by omega)]
    simp [List.getD_eq_getElem?_getD, ho]

theorem op_eval_mono {op : GateOp} (hop : op = .and ∨ op = .or) (l : List ℕ) (f f' : ℕ → Bool)
    (hff : ∀ a ∈ l, f a = true → f' a = true) (h : op.eval (l.map f) = true) :
    op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at h ⊢
    intro a ha; exact hff a ha (h a ha)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at h ⊢
    obtain ⟨a, ha, hfa⟩ := h
    exact ⟨a, ha, hff a ha hfa⟩

theorem val_mono {n : ℕ} {gs : List Gate} (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {X X' : Finset (Fin n)} (hXX : X ⊆ X') :
    ∀ k, val n gs X k = true → val n gs X' k = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h : k < n
    · rw [val_input h] at hk ⊢
      simp only [decide_eq_true_eq] at hk ⊢
      exact hXX hk
    · by_cases h2 : k - n < gs.length
      · rw [val_gate h h2] at hk ⊢
        refine op_eval_mono (hgs _ (List.getElem_mem _)) _ _ _ ?_ hk
        intro a _ ha
        by_cases hak : a < k
        · simp only [hak, ite_true] at ha ⊢
          exact ih a hak ha
        · simp [hak] at ha
      · rw [val_past (by omega)] at hk
        exact absurd hk (by simp)

/-- Checked statements L-meta-100 and L-meta-18508, respectively. -/
abbrev MajorityFloor : Prop :=
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)) s ↔ 4 ≤ s

abbrev CrownReduction : Prop :=
∀ n s : ℕ, 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + n ≤ s ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true = 2 → C.eval (List.ofFn x) = true) ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x) = false)

/-- Weight two already forces the all-ones response of a positive circuit.
The other seven inputs belong to the promise of the crown reduction. -/
theorem crownFloor (majority : MajorityFloor) (reduceCrown : CrownReduction) :
    ¬ Represents.RepSizeAtMost (fun i j : Fin 3 => decide (i ≠ j)) 6 := by
  intro rep
  obtain ⟨C, pos, size, two, low⟩ := reduceCrown 3 6 (by decide) rep
  have ops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (pos g hg).1
  have fan : FanInTwo C := by
    intro g hg
    refine ⟨?_, (pos g hg).2⟩
    rcases ops g hg with e | e <;> simp [e]
  let pair : Finset (Fin 3) := {0, 1}
  have atPair := two (fun i => decide (i ∈ pair)) (by decide)
  rw [eval_eq C.gates pair C.output] at atPair
  have atTop := val_mono ops (Finset.subset_univ pair) C.output atPair
  rw [← eval_eq C.gates Finset.univ C.output] at atTop
  have small : HasCircuitSize 3 (fun x : Fin 3 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)) 3 := by
    refine ⟨C, fan, by omega, ?_⟩
    intro x
    have table : ∀ y : Fin 3 → Bool,
        let maj := (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)
        ((List.ofFn y).count true ≤ 1 ∧ maj = false) ∨
        ((List.ofFn y).count true = 2 ∧ maj = true) ∨
        (y = (fun i => decide (i ∈ (Finset.univ : Finset (Fin 3)))) ∧ maj = true) := by decide
    rcases table x with ⟨h,e⟩ | ⟨h,e⟩ | ⟨h,e⟩
    · exact (low x h).trans e.symm
    · exact (two x h).trans e.symm
    · rw [h]; exact atTop.trans (h ▸ e).symm
  have := (majority 3).mp small
  omega

theorem exactFromThree (induced : InducedBound) (majority : MajorityFloor)
    (reduceCrown : CrownReduction) (n m : ℕ) (hn : 3 ≤ n) (hm : 3 ≤ m) :
    let A := fun (i : Fin n) (j : Fin m) => edge i.val j.val
    Represents.RepSizeAtMost A (n+m+1) ∧ ¬ Represents.RepSizeAtMost A (n+m) := by
  obtain ⟨C, pos, price, rep⟩ := threeHoleUpper n m hn hm
  refine ⟨⟨C,pos,price.le,rep⟩,?_⟩
  intro small
  obtain ⟨t, ⟨D, dp, ds, dr⟩, cost⟩ := saved induced n m (n+m) hn hm small
  have copy := restrictPrefix hn hm _ (s := 6) ⟨D,dp,by omega,dr⟩
  have eqn : ∀ i j : Fin 3, (edge i.val j.val && decide (i.val < 3) && decide (j.val < 3)) = decide (i ≠ j) := by decide
  apply crownFloor majority reduceCrown
  simpa only [Fin.coe_castLE, eqn] using copy

-- This wrapper uses the target graph from the register literally.
theorem exactThreeLinesFromReceipts
    (induced : InducedBound)
    (majority : MajorityFloor)
    (reduceCrown : CrownReduction) :
∀ (n m : Nat), 3 ≤ n → 3 ≤ m →
  let A := fun (u : Fin n) (v : Fin m) =>
    (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
  PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
    ¬ PEqualNP.Represents.RepSizeAtMost A (n + m)
 := by
  intro n m hn hm
  exact exactFromThree induced majority reduceCrown n m hn hm

end PEqualNP.Outside.L_meta_30581

theorem PEqualNP.Outside.L_meta_30581 :
  ∀ (n m : Nat), 3 ≤ n → 3 ≤ m →
    let A := fun (u : Fin n) (v : Fin m) =>
      (64478 : Nat).testBit (4 * min u.val 3 + min v.val 3)
    PEqualNP.Represents.RepSizeAtMost A (n + m + 1) ∧
      ¬ PEqualNP.Represents.RepSizeAtMost A (n + m) :=
  PEqualNP.Outside.L_meta_30581.exactThreeLinesFromReceipts
    PEqualNP.MetaComplexity.RepInduced.induced
    PEqualNP.MetaComplexity.L100
    PEqualNP.Outside.L_meta_18508
