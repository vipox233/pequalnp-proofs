import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_29914_aux

private def valG (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun j => w.getD j false)
private def step (w : List Bool) (g : Gate) := w ++ [valG g w]
private def run (gs : List Gate) (w : List Bool) := gs.foldl step w

private theorem run_len (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step, Nat.add_comm, Nat.add_left_comm]

private theorem early (gs : List Gate) (w : List Bool) (j : Nat) (h : j < w.length) :
    (run gs w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD j false = _
    rw [ih]
    · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · simp [step]; omega

private def Agree (w z : List Bool) := ∀ j : Nat, j ≠ 0 → w.getD j false = z.getD j false

private theorem extend (w z : List Bool) (b : Bool) (hl : w.length = z.length)
    (h : Agree w z) : Agree (w ++ [b]) (z ++ [b]) := by
  intro j hj
  by_cases lt : j < w.length
  · have lt' : j < z.length := hl ▸ lt
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left lt,
      List.getElem?_append_left lt'] using h j hj
  · have le : w.length ≤ j := by omega
    have le' : z.length ≤ j := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right le,
      List.getElem?_append_right le', hl]

private theorem gate_eq (g : Gate) (w z : List Bool)
    (h : ∀ j ∈ g.inputs, w.getD j false = z.getD j false) : valG g w = valG g z := by
  unfold valG
  congr 1
  apply List.map_congr_left
  exact h

private theorem run_agree (gs : List Gate) (w z : List Bool) (hl : w.length = z.length)
    (h : Agree w z) (hn : ∀ g ∈ gs, 0 ∉ g.inputs) : Agree (run gs w) (run gs z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    change Agree (run gs (step w g)) (run gs (step z g))
    apply ih
    · simp [step, hl]
    · have eqv := gate_eq g w z (fun j hj => h j (fun e => hn g (by simp) (e ▸ hj)))
      simpa [step, eqv] using extend w z (valG g z) hl h
    · exact fun g' hg' => hn g' (by simp [hg'])

private def edge (x : Fin 7 → Bool) :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

private def mark (x : Fin 7 → Bool) (j : Fin 7) := if j = 0 then true else x j

private theorem input_agree (x : Fin 7 → Bool) : Agree (List.ofFn x) (List.ofFn (mark x)) := by
  intro j hj
  by_cases h : j < 7
  · have nz : (⟨j,h⟩ : Fin 7) ≠ 0 := by intro he; exact hj (congrArg Fin.val he)
    interval_cases j <;> simp_all [mark]
  · simp [List.getD_eq_getElem?_getD, h]

private theorem or_val (g : Gate) (w : List Bool) (hop : g.op = .or)
    (h0 : 0 ∈ g.inputs) (h8 : 8 ∈ g.inputs) (hlen : g.inputs.length ≤ 2) :
    valG g w = (w.getD 0 false || w.getD 8 false) := by
  have lists : ∀ l : List Nat, 0 ∈ l → 8 ∈ l → l.length ≤ 2 → l = [0,8] ∨ l = [8,0] := by
    intro l a b c
    rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩ <;> simp_all <;> omega
  rcases lists _ h0 h8 hlen with e | e <;> simp [valG, hop, GateOp.eval, e, Bool.or_comm]

private theorem and_false (g : Gate) (w : List Bool) (hop : g.op = .and)
    (hm : 15 ∈ g.inputs) (hf : w.getD 15 false = false) : valG g w = false := by
  simp [valG, hop, GateOp.eval, List.all_eq_false]
  exact ⟨15, hm, hf⟩

private theorem read_two (w : List Bool) (h : w.length = 15) (a b : Bool) (j : Nat) :
    (w ++ [a,b]).getD j false =
      if j = 15 then a else if j = 16 then b else w.getD j false := by
  by_cases lt : j < 15
  · have lt' : j < w.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left lt', show j ≠ 15 by omega,
      show j ≠ 16 by omega]
  · have le : w.length ≤ j := by omega
    by_cases e : j = 15
    · simp [List.getD_eq_getElem?_getD, h, e]
    by_cases f : j = 16
    · simp [List.getD_eq_getElem?_getD, h, f]
    · have far : 2 ≤ j - 15 := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right le, h, e, f,
        List.getElem?_eq_none (show w.length ≤ j by omega),
        List.getElem?_eq_none (show [a,b].length ≤ j - 15 by simpa using far)]

private def chosen (s : List Nat) (i : Fin 7) := decide (i.val ∈ s)

private theorem constraints (pre : List Gate) (o a : Gate) (out : Nat)
    (hlen : pre.length = 8) (hn : ∀ g ∈ pre, 0 ∉ g.inputs)
    (hor : o.op = .or) (h0 : 0 ∈ o.inputs) (h8 : 8 ∈ o.inputs) (ho : o.inputs.length ≤ 2)
    (hand : a.op = .and) (hm : 15 ∈ a.inputs) (hna : 0 ∉ a.inputs)
    (heval : ∀ x : Fin 7 → Bool,
      (run (pre ++ [o,a]) (List.ofFn x)).getD out false = edge x) :
    ∀ x : Fin 7 → Bool, x 0 = false →
      (edge x = true → (run pre (List.ofFn x)).getD 8 false = true) ∧
      (edge x = false → edge (mark x) = true → (run pre (List.ofFn x)).getD 8 false = false) := by
  let w (x : Fin 7 → Bool) := run pre (List.ofFn x)
  let p (x : Fin 7 → Bool) := valG o (w x)
  let q (x : Fin 7 → Bool) := valG a (w x ++ [p x])
  have wl x : (w x).length = 15 := by simp [w, run_len, hlen]
  have w0 x : (w x).getD 0 false = x 0 := by
    rw [show (w x).getD 0 false = _ from early pre (List.ofFn x) 0 (by simp)]
    simp
  have pv x : p x = (x 0 || (w x).getD 8 false) := by
    rw [show p x = _ from or_val o (w x) hor h0 h8 ho, w0]
  have av x : p x = false → q x = false := by
    intro eqp
    apply and_false a _ hand hm
    simp [List.getD_eq_getElem?_getD, wl, eqp]
  have formula x : (if out = 15 then p x else if out = 16 then q x else (w x).getD out false) = edge x := by
    rw [← read_two (w x) (wl x) (p x) (q x)]
    simpa only [run, List.foldl_append, List.foldl_cons, List.foldl_nil, step, List.append_assoc,
      List.singleton_append, w, p, q] using heval x
  have wa x : Agree (w x) (w (mark x)) :=
    run_agree pre _ _ (by simp) (input_agree x) hn
  have on : out ≠ 0 := by
    intro e
    have f := formula (chosen [0])
    rw [e] at f
    change (w (chosen [0])).getD 0 false = false at f
    rw [w0] at f
    contradiction
  have ends : out = 15 ∨ out = 16 := by
    by_contra! ne
    let x := chosen [1]
    have eqo := wa x out on
    have f := formula x
    have g := formula (mark x)
    simp only [ite_eq_right ne.1, ite_eq_right ne.2] at f g
    rw [f, g] at eqo
    exact Bool.noConfusion eqo
  intro x x0
  constructor
  · intro e
    cases neg : (w x).getD 8 false <;> try rfl
    exfalso
    have hp : p x = false := by rw [pv, x0, neg]; rfl
    have f := formula x
    rcases ends with h | h <;> simp [h, hp, av x hp, e] at f
  · intro e et
    cases pos : (w x).getD 8 false <;> try rfl
    exfalso
    have hp : p x = p (mark x) := by rw [pv, pv, pos]; simp [mark]
    have ag : Agree (w x ++ [p x]) (w (mark x) ++ [p (mark x)]) := by
      rw [hp]
      exact extend _ _ _ (by simp [wl]) (wa x)
    have hq : q x = q (mark x) := gate_eq a _ _ fun j hj => ag j (fun he => hna (he ▸ hj))
    have f := formula x
    have g := formula (mark x)
    rw [hp, hq, wa x out on, g] at f
    simp [e, et] at f

private theorem first_two (g b : Gate) (rs : List Gate) (x y : Fin 7 → Bool)
    (agree : ∀ j ∈ g.inputs ++ b.inputs,
      (List.ofFn x).getD j false = (List.ofFn y).getD j false) :
    (run (g :: b :: rs) (List.ofFn x)).getD 8 false =
    (run (g :: b :: rs) (List.ofFn y)).getD 8 false := by
  have eg := gate_eq g _ _ fun j hj => agree j (List.mem_append_left _ hj)
  have eb : valG b (step (List.ofFn x) g) = valG b (step (List.ofFn y) g) := by
    apply gate_eq
    intro j hj
    by_cases h : j < 7
    · have hx : j < (List.ofFn x).length := by simpa
      have hy : j < (List.ofFn y).length := by simpa
      simpa only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hx,
        List.getElem?_append_left hy] using agree j (List.mem_append_right _ hj)
    · have hx : (List.ofFn x).length ≤ j := by simp; omega
      have hy : (List.ofFn y).length ≤ j := by simp; omega
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_right hx,
        List.getElem?_append_right hy, List.length_ofFn, eg]
  have at8 (z : Fin 7 → Bool) : (run (g :: b :: rs) (List.ofFn z)).getD 8 false =
      valG b (step (List.ofFn z) g) := by
    change (run rs (step (step (List.ofFn z) g) b)).getD 8 false = _
    rw [early _ _ _ (by simp [step])]
    simp [step, List.getD_eq_getElem?_getD]
  rwa [at8, at8]

private theorem chosen_agree (d j : Nat) (s : List Nat) (hne : j ≠ d) :
    (List.ofFn (chosen s)).getD j false = (List.ofFn (chosen (d :: s))).getD j false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp_all [chosen]

private theorem impossible (g b : Gate) (rs : List Gate) (hg : g.inputs.length ≤ 2)
    (hb : b.inputs.length ≤ 2)
    (h : ∀ x : Fin 7 → Bool, x 0 = false →
      (edge x = true → (run (g :: b :: rs) (List.ofFn x)).getD 8 false = true) ∧
      (edge x = false → edge (mark x) = true → (run (g :: b :: rs) (List.ofFn x)).getD 8 false = false)) :
    False := by
  let support := (g.inputs ++ b.inputs).toFinset
  have force (d : Nat) (s : List Nat)
      (e0 : chosen s 0 = false) (e1 : chosen (d :: s) 0 = false)
      (f : edge (chosen s) = false) (t : edge (mark (chosen s)) = true)
      (f' : edge (chosen (d :: s)) = true) : d ∈ support := by
    by_contra hn
    have eqv := first_two g b rs (chosen s) (chosen (d :: s)) fun j hj =>
      chosen_agree d j s (fun eqd => hn (List.mem_toFinset.mpr (eqd ▸ hj)))
    rw [(h _ e0).2 f t, (h _ e1).1 f'] at eqv
    contradiction
  have h1 := force 1 [2,6] (by decide) (by decide) (by decide) (by decide) (by decide)
  have h2 := force 2 [1] (by decide) (by decide) (by decide) (by decide) (by decide)
  have h3 := force 3 [1,4] (by decide) (by decide) (by decide) (by decide) (by decide)
  have h4 := force 4 [1,3] (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 := force 5 [6] (by decide) (by decide) (by decide) (by decide) (by decide)
  have sub : ({1,2,3,4,5} : Finset Nat) ⊆ support := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> assumption
  have lo := Finset.card_le_card sub
  have hi := List.toFinset_card_le (g.inputs ++ b.inputs)
  change 5 ≤ support.card at lo
  change support.card ≤ _ at hi
  rw [List.length_append] at hi
  omega

end PEqualNP.Outside.L_meta_29914_aux
open PEqualNP.Outside.L_meta_29914_aux

theorem PEqualNP.Outside.L_meta_29914 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 8 ∈ (C.gates.get i).inputs ∧ 8 ≠ 0 ∧ 8 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 8 false = true)) := by
  rintro ⟨C, i, k, hi, fan, size, computes, hzero, unique, hor, hand, hlt, huse, height, _⟩
  change C.gates.length = 10 at size
  have hk : k.val = 9 := by have := k.isLt; omega
  let pre := C.gates.take 8
  let o := C.gates.get i
  let a := C.gates.get k
  have plen : pre.length = 8 := by simp [pre, size]
  have splitG : C.gates = pre ++ [o,a] := by
    have h₈ : 8 < C.gates.length := by omega
    have h₉ : 9 < C.gates.length := by omega
    have oi : o = C.gates[8] := by simp [o, List.get_eq_getElem, hi]
    have ak : a = C.gates[9] := by simp [a, List.get_eq_getElem, hk]
    have e := List.take_succ_eq_append_getElem h₉
    have f := List.take_succ_eq_append_getElem h₈
    change C.gates.take 10 = C.gates.take 9 ++ [_] at e
    change C.gates.take 9 = C.gates.take 8 ++ [_] at f
    rw [← size, List.take_length, f, List.append_assoc] at e
    simpa [oi, ak, pre] using e
  have hn : ∀ g ∈ pre, 0 ∉ g.inputs := by
    intro g hg hz
    obtain ⟨j, hj, ej⟩ := List.mem_iff_getElem.mp hg
    have hj' : j < 8 := by omega
    have hj'' : j < C.gates.length := by omega
    have eg : C.gates[j] = g := by simpa [pre] using ej
    let t : Fin C.gates.length := ⟨j,hj''⟩
    have et := unique t (by simpa [t, List.get_eq_getElem, eg] using hz)
    have hval := congrArg Fin.val et
    change j = i.val at hval
    omega
  have hna : 0 ∉ a.inputs := by
    intro hz
    have := congrArg Fin.val (unique k hz)
    omega
  have memG (g : Gate) (hg : g ∈ pre) : g ∈ C.gates := by rw [splitG]; simp [hg]
  have width : ∀ g ∈ pre, g.inputs.length ≤ 2 := fun g hg => (fan g (memG g hg)).2
  have bound := constraints pre o a C.output plen hn hor hzero height (fan o (List.get_mem ..)).2
    hand (by simpa only [a, hi] using huse) hna (fun x => by
      have e := computes x
      change (run C.gates (List.ofFn x)).getD C.output false = edge x at e
      rwa [splitG] at e)
  generalize he : pre = gs at plen width bound
  rcases gs with _ | ⟨g, _ | ⟨b, rs⟩⟩
  · simp at plen
  · simp at plen
  · exact impossible g b rs (width g (by simp)) (width b (by simp)) bound
