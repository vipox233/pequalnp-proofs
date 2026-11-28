import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_49939

open PEqualNP.CircuitLowerBounds

abbrev M := BitVec 5

def raw : List M := [30, 28, 24, 16, 0, 31]

def row (t : Fin 5) (m : M) := m.getLsbD t.val

def allowed (o : GateOp) := o = .and ∨ o = .or ∨ o = .not

def legal (g : Gate) := allowed g.op ∧ g.inputs.length ≤ 2

def evalMask : GateOp → List M → M
  | .and, [] => ~~~0
  | .and, [a] => a
  | .and, a :: b :: _ => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, a :: b :: _ => a ||| b
  | .not, l => ~~~(l.headD 0)
  | _, _ => 0

def val (w : List M) (g : Gate) :=
  evalMask g.op (g.inputs.map fun i => w.getD i 0)

def push (w : List M) (g : Gate) := w ++ [val w g]

def pushB (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma calc_row (t : Fin 5) (o : GateOp) (l : List M) (ho : allowed o)
    (hl : l.length ≤ 2) : row t (evalMask o l) = o.eval (l.map (row t)) := by
  rcases ho with rfl | rfl | rfl <;>
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [evalMask, row, GateOp.eval, t.isLt] <;> revert t <;> decide

lemma get_row (t : Fin 5) (w : List M) (i : Nat) :
    (w.map (row t)).getD i false = row t (w.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [row]

lemma push_row (t : Fin 5) (w : List M) (g : Gate) (hg : legal g) :
    pushB (w.map (row t)) g = (push w g).map (row t) := by
  simp only [pushB, push, val, List.map_append, List.map_cons, List.map_nil]
  rw [calc_row t _ _ hg.1 (by simpa using hg.2), List.map_map]
  simp only [Function.comp_def, get_row]

lemma fold_row (t : Fin 5) (gs : List Gate) (w : List M) (hg : ∀ g ∈ gs, legal g) :
    gs.foldl pushB (w.map (row t)) = (gs.foldl push w).map (row t) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [push_row t w g (hg g (by simp))]
    exact ih _ (fun x hx => hg x (by simp [hx]))

lemma init_row (t : Fin 5) :
    List.ofFn (fun i : Fin 4 => decide (i.val < t.val)) ++ [false,true] = raw.map (row t) := by
  revert t
  decide

lemma read_row (D : Circuit) (hl : ∀ g ∈ D.gates, legal g) (i : Nat) (t : Fin 5) :
    (D.wires (List.ofFn (fun j : Fin 4 => decide (j.val < t.val)) ++ [false,true])).getD i false =
      row t ((D.gates.foldl push raw).getD i 0) := by
  rw [init_row]
  change (D.gates.foldl pushB (raw.map (row t))).getD i false = _
  rw [fold_row t _ _ hl, get_row]

lemma read_mem {w b : List M} (h : ∀ x ∈ w, x ∈ b) (hz : 0 ∈ b) (i : Nat) :
    w.getD i 0 ∈ b := by
  rw [List.getD_eq_getElem?_getD]
  cases e : w[i]? with
  | none => exact hz
  | some x => exact h x (List.mem_of_getElem? e)

def poss (b : List M) : List M :=
  b.map (fun x => ~~~x) ++ b.flatMap (fun x => b.flatMap (fun y => [x &&& y, x ||| y]))

def kids (b : List M) := ((poss b).filter (fun x => !b.contains x)).eraseDups

def need (b : List M) : Nat :=
  (if 12 ∈ b then 0 else 1) + (if 14 ∈ b then 0 else 1) + (if 22 ∈ b then 0 else 1)

def win : Nat → List M → Bool
  | 0, b => need b == 0
  | n + 1, b => if need b = 0 then true else if n + 1 < need b then false
      else (kids b).any (fun v => win n (v :: b))

set_option maxHeartbeats 8000000 in
theorem rootMiss : win 5 raw = false := by decide +kernel

lemma debt (x : M) (b : List M) : need b ≤ need (x :: b) + 1 := by
  have h12 : (12 : M) ≠ 14 := by decide
  have h13 : (12 : M) ≠ 22 := by decide
  have h23 : (14 : M) ≠ 22 := by decide
  simp only [need, List.mem_cons]
  split_ifs <;> first | omega | grind

lemma win_bound (n : Nat) (b : List M) (hw : win n b = true) : need b ≤ n := by
  cases n with
  | zero => simpa [win] using hw
  | succ n =>
    by_contra hn
    have h : n + 1 < need b := by omega
    simp [win, h, show need b ≠ 0 by omega] at hw

lemma neg_mem {x : M} {b : List M} (h : x ∈ b) : ~~~x ∈ poss b :=
  List.mem_append_left _ (List.mem_map.mpr ⟨x, h, rfl⟩)

lemma pair_mem {x y v : M} {b : List M} (hx : x ∈ b) (hy : y ∈ b)
    (hv : v = x &&& y ∨ v = x ||| y) : v ∈ poss b :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, List.mem_flatMap.mpr
    ⟨y, hy, by simpa using hv⟩⟩)

lemma eval_possible (o : GateOp) (l b : List M) (ho : allowed o) (hl : l.length ≤ 2)
    (h : ∀ x ∈ l, x ∈ b) (hz : 0 ∈ b) (ht : 31 ∈ b) :
    evalMask o l ∈ b ∨ evalMask o l ∈ poss b := by
  match l, hl with
  | [], _ =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ht
    · exact Or.inl hz
    · exact Or.inl ht
  | [x], _ =>
    have hx := h x (by simp)
    rcases ho with rfl | rfl | rfl
    · exact Or.inl hx
    · exact Or.inl hx
    · exact Or.inr (neg_mem hx)
  | [x,y], _ =>
    have hx := h x (by simp)
    have hy := h y (by simp)
    rcases ho with rfl | rfl | rfl
    · exact Or.inr (pair_mem hx hy (Or.inl rfl))
    · exact Or.inr (pair_mem hx hy (Or.inr rfl))
    · exact Or.inr (neg_mem hx)
  | _ :: _ :: _ :: _, he => simp at he

lemma step_possible (g : Gate) (w b : List M) (hl : legal g)
    (hc : ∀ x ∈ w, x ∈ b) (hz : 0 ∈ b) (ht : 31 ∈ b) :
    val w g ∈ b ∨ val w g ∈ poss b := by
  apply eval_possible g.op _ _ hl.1 (by simpa using hl.2) _ hz ht
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact read_mem hc hz i

def marks (w : List M) (p q r : Nat) :=
  w.getD p 0 = 12 ∧ w.getD q 0 = 14 ∧ w.getD r 0 = 22

lemma exhaustive (gs : List Gate) (p q r : Nat) :
    ∀ (n : Nat) (w b : List M), gs.length ≤ n → (∀ g ∈ gs, legal g) →
      (∀ x ∈ w, x ∈ b) → 0 ∈ b → 31 ∈ b →
      marks (gs.foldl push w) p q r → win n b = true := by
  induction gs with
  | nil =>
    intro n w b _ _ hc hz _ hm
    obtain ⟨hp, hq, hr⟩ := hm
    have h12 := read_mem hc hz p
    have h14 := read_mem hc hz q
    have h22 := read_mem hc hz r
    change w.getD p 0 = 12 at hp
    change w.getD q 0 = 14 at hq
    change w.getD r 0 = 22 at hr
    rw [hp] at h12
    rw [hq] at h14
    rw [hr] at h22
    have hn : need b = 0 := by
      unfold need
      rw [ite_eq_left h12, ite_eq_left h14, ite_eq_left h22]
    cases n <;> simp [win, hn]
  | cons g gs ih =>
    intro n w b hs hl hc hz ht hm
    cases n with
    | zero => simp at hs
    | succ n =>
      have hlen : gs.length ≤ n := by simpa using hs
      have tail : ∀ a ∈ gs, legal a := fun a ha => hl a (by simp [ha])
      let v := val w g
      have update (c : List M) (hsub : ∀ x ∈ b, x ∈ c) (hv : v ∈ c) :
          ∀ x ∈ push w g, x ∈ c := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hsub _ (hc _ hx)
        · simpa only [List.mem_singleton.mp hx] using hv
      by_cases hv : v ∈ b
      · exact ih (n + 1) (push w g) b (by omega) tail
          (update b (fun _ hx => hx) hv) hz ht hm
      · have hvp : v ∈ poss b :=
          (step_possible g w b (hl g (by simp)) hc hz ht).resolve_left hv
        have hvk : v ∈ kids b := by
          apply List.mem_eraseDups.mpr
          exact List.mem_filter.mpr ⟨hvp, by simpa using hv⟩
        have inc : ∀ x ∈ b, x ∈ v :: b := fun _ hx => List.mem_cons_of_mem _ hx
        have hrec : win n (v :: b) = true :=
          ih n (push w g) (v :: b) hlen tail
            (update _ inc List.mem_cons_self) (inc _ hz) (inc _ ht) hm
        have hd := debt v b
        have hb := win_bound _ _ hrec
        by_cases h : need b = 0
        · simp [win, h]
        · simp only [win, h, ite_false, show ¬ n + 1 < need b by omega]
          exact List.any_eq_true.mpr ⟨v, hvk, hrec⟩


end PEqualNP.Outside.L_meta_49939

open PEqualNP.Outside.L_meta_49939

theorem PEqualNP.Outside.L_meta_49939 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (12 : Nat).testBit t.val ∧
    w.getD q.val false = (14 : Nat).testBit t.val ∧
    w.getD r.val false = (22 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hfan, _, _, hsize, hout⟩
  have hl : ∀ g ∈ D.gates, legal g := by
    intro g hg
    exact hfan g hg
  let w := D.gates.foldl push raw
  have h (t : Fin 5) : row t (w.getD p.val 0) = (12 : Nat).testBit t.val ∧
      row t (w.getD q.val 0) = (14 : Nat).testBit t.val ∧
      row t (w.getD r.val 0) = (22 : Nat).testBit t.val :=
    ⟨(read_row D hl _ t).symm.trans (hout t).1,
      (read_row D hl _ t).symm.trans (hout t).2.1,
      (read_row D hl _ t).symm.trans (hout t).2.2⟩
  have hp : w.getD p.val 0 = 12 := BitVec.eq_of_getLsbD_eq fun i hi => (h ⟨i,hi⟩).1
  have hq : w.getD q.val 0 = 14 := BitVec.eq_of_getLsbD_eq fun i hi => (h ⟨i,hi⟩).2.1
  have hr : w.getD r.val 0 = 22 := BitVec.eq_of_getLsbD_eq fun i hi => (h ⟨i,hi⟩).2.2
  have he := exhaustive D.gates p.val q.val r.val 5 raw raw hsize hl
    (fun _ hx => hx) (by decide) (by decide) ⟨hp, hq, hr⟩
  simp [rootMiss] at he
