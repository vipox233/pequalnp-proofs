import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29922

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

private def pushGate (ys : List Bool) (g : Gate) : List Bool :=
  ys ++ [g.op.eval (g.inputs.map (fun w => ys.getD w false))]

private def tape (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl pushGate xs

private theorem tape_length (gs : List Gate) (xs : List Bool) :
    (tape gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [tape]
  | cons g gs ih =>
    change (tape gs (pushGate xs g)).length = _
    rw [ih]
    simp only [pushGate, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem tape_raw (gs : List Gate) (xs : List Bool) (w : ℕ)
    (hw : w < xs.length) : (tape gs xs).getD w false = xs.getD w false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (tape gs (pushGate xs g)).getD w false = xs.getD w false
    rw [ih _ (by simp [pushGate]; omega)]
    exact List.getD_append _ _ _ _ hw

private theorem tape_append_read (p s : List Gate) (xs : List Bool) (w : ℕ)
    (hw : w < xs.length + p.length) :
    (tape (p ++ s) xs).getD w false = (tape p xs).getD w false := by
  rw [show tape (p ++ s) xs = tape s (tape p xs) by simp [tape, List.foldl_append]]
  apply tape_raw
  simpa [tape_length] using hw

private theorem cons_read (a b : Bool) (xs : List Bool) (w : ℕ) (hw : w ≠ 0) :
    (a::xs).getD w false = (b::xs).getD w false := by
  cases w
  · contradiction
  · rfl

private theorem prefix_bits (gs : List Gate)
    (h : ∀ g ∈ gs, 0 ∉ g.inputs) (xs : List Bool) :
    ∃ zs, tape gs (false::xs) = false::zs ∧ tape gs (true::xs) = true::zs := by
  induction gs generalizing xs with
  | nil => exact ⟨xs,rfl,rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map (fun w => (false::xs).getD w false))
    have he : g.inputs.map (fun w => (true::xs).getD w false) =
        g.inputs.map (fun w => (false::xs).getD w false) := by
      apply List.map_congr_left
      intro w hw
      exact cons_read _ _ _ _ (fun e => h g (by simp) (e ▸ hw))
    have h1 : pushGate (true::xs) g = true :: (xs ++ [b]) := by
      simp only [pushGate, he, List.cons_append, b]
    change ∃ zs, tape gs (pushGate (false::xs) g) = false::zs ∧
      tape gs (pushGate (true::xs) g) = true::zs
    rw [h1]
    exact ih (fun g hg => h g (List.mem_cons_of_mem _ hg)) (xs ++ [b])

private def edgePath (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)

private def rootOn (x : Fin 6 → Bool) : Bool := x 0 || x 5 || edgePath x

private def setFirst (a : Bool) (x : Fin 6 → Bool) : Fin 7 → Bool :=
  Fin.cons a x

private def edgeCycle (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

private theorem edgeCycle_off (x : Fin 6 → Bool) : edgeCycle (setFirst false x) =
    edgePath x := by
  revert x
  decide +kernel

private theorem edgeCycle_on (x : Fin 6 → Bool) : edgeCycle (setFirst true x) =
    rootOn x := by
  revert x
  decide +kernel

private theorem both_first {l : List ℕ} (hl : l.length ≤ 2) {u v : ℕ}
    (hu : u ∈ l) (hv : v ∈ l) (hne : u ≠ v) : l = [u,v] ∨ l = [v,u] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c,r⟩⟩⟩
  · simp at hu
  · simp_all
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all
  · simp at hl

private theorem gate_disjunction (a : Gate) (h : a.op = .or)
    (ha : a.inputs = [0,12] ∨ a.inputs = [12,0]) (ys : List Bool) :
    pushGate ys a = ys ++ [ys.getD 0 false || ys.getD 12 false] := by
  rcases ha with ha | ha <;> simp [pushGate, h, ha, GateOp.eval, Bool.or_comm]

private theorem gate_conjunction (b : Gate) (h : b.op = .and)
    (hlen : b.inputs.length ≤ 2) (hm : 15 ∈ b.inputs) (h0 : 0 ∉ b.inputs) :
    ∃ q : ℕ, q ≠ 0 ∧ ∀ ys : List Bool,
      pushGate ys b = ys ++ [ys.getD 15 false && ys.getD q false] := by
  obtain ⟨op,inputs⟩ := b
  change op = GateOp.and at h
  subst op
  change inputs.length ≤ 2 at hlen
  change 15 ∈ inputs at hm
  change 0 ∉ inputs at h0
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,r⟩⟩⟩
  · simp at hm
  · have he : a = 15 := by simpa [eq_comm] using hm
    subst a
    exact ⟨15,by decide,by intro ys; simp [pushGate, GateOp.eval]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm h0
    rcases hm with ha | hb
    · subst a
      refine ⟨b,by tauto,?_⟩
      intro ys
      simp [pushGate, GateOp.eval]
    · subst b
      refine ⟨a,by tauto,?_⟩
      intro ys
      simp [pushGate, GateOp.eval, Bool.and_comm]
  · simp at hlen

private theorem two_last (p : List Gate) (a b : Gate) (xs : List Bool) :
    tape (p++[a,b]) xs = pushGate (pushGate (tape p xs) a) b := by
  simp only [tape, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem appendedBit (xs : List Bool) (b : Bool) :
    (xs++[b]).getD xs.length false = b := by
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

private theorem cofactor_reduction (p : List Gate) (A B : Gate) (o : ℕ)
    (hp : p.length = 8) (hno : ∀ g ∈ p, 0 ∉ g.inputs)
    (hA : A.op = .or) (hAA : A.inputs = [0,12] ∨ A.inputs = [12,0])
    (hB : B.op = .and) (hBB : B.inputs.length ≤ 2) (hread : 15 ∈ B.inputs)
    (hB0 : 0 ∉ B.inputs)
    (hmode : ∀ x : Fin 7 → Bool, (tape (p++[A,B]) (List.ofFn x)).getD o false = edgeCycle x) :
    ∀ x : Fin 6 → Bool, rootOn x = true →
      (tape p (false::List.ofFn x)).getD 12 false = edgePath x := by
  let xs (b : Bool) (x : Fin 6 → Bool) := b :: List.ofFn x
  have xsLength (b : Bool) (x : Fin 6 → Bool) : (xs b x).length = 7 := by simp [xs]
  have heval (b : Bool) (x : Fin 6 → Bool) :
      (tape (p++[A,B]) (xs b x)).getD o false =
        if b then rootOn x else edgePath x := by
    have he := hmode (setFirst b x)
    change (tape (p++[A,B]) (List.ofFn (Fin.cons b x))).getD o false = _ at he
    rw [List.ofFn_cons] at he
    cases b
    · simpa only [xs, Bool.false_eq_true, ↓reduceIte, edgeCycle_off] using he
    · simpa only [xs, ↓reduceIte, edgeCycle_on] using he
  let solo : Fin 6 → Bool := ![true,false,false,false,false,false]
  let empty : Fin 6 → Bool := fun _ => false
  let edge : Fin 6 → Bool := ![true,true,false,false,false,false]
  have out0 : o ≠ 0 := by
    intro h
    have e := heval false edge
    have hw := tape_raw (p++[A,B]) (xs false edge) 0 (by simp [xs])
    rw [h, hw] at e
    contradiction
  have outearly : 15 ≤ o := by
    by_contra! hearly
    have lo : o < (xs false solo).length + p.length := by rw [xsLength,hp]; omega
    have hi : o < (xs true solo).length + p.length := by rw [xsLength,hp]; omega
    obtain ⟨z,hz0,hz1⟩ := prefix_bits p hno (List.ofFn solo)
    have eqv : (tape (p++[A,B]) (xs false solo)).getD o false =
        (tape (p++[A,B]) (xs true solo)).getD o false := by
      rw [tape_append_read p [A,B] _ _ lo, tape_append_read p [A,B] _ _ hi]
      have e0 : tape p (xs false solo) = false::z := hz0
      have e1 : tape p (xs true solo) = true::z := hz1
      rw [e0,e1]
      exact cons_read _ _ _ _ out0
    rw [heval,heval] at eqv
    contradiction
  have outlt : o < 17 := by
    by_contra! ho
    have hlen : (tape (p++[A,B]) (xs true solo)).length = 17 := by
      simp [tape_length,xsLength,hp]
    have hn := heval true solo
    rw [List.getD_eq_default _ _ (by omega)] at hn
    contradiction
  have evalA (b : Bool) (x : Fin 6 → Bool) :
      pushGate (tape p (xs b x)) A = tape p (xs b x) ++
        [b || (tape p (xs b x)).getD 12 false] := by
    rw [gate_disjunction A hA hAA, tape_raw p _ 0 (by simp [xs])]
    rfl
  have out15 : o ≠ 15 := by
    intro o15
    have he := heval true empty
    rw [o15, two_last, evalA] at he
    have pLen : (tape p (xs true empty)).length = 15 := by simp [tape_length,xsLength,hp]
    unfold pushGate at he
    rw [List.getD_append _ _ _ _ (by simp [pLen]), ← pLen, appendedBit] at he
    contradiction
  have out16 : o = 16 := by omega
  obtain ⟨q,hq0,hqe⟩ := gate_conjunction B hB hBB hread hB0
  have fullFactor (b : Bool) (x : Fin 6 → Bool) :
      let y := pushGate (tape p (xs b x)) A
      (y.getD 15 false && y.getD q false) = (if b then rootOn x else edgePath x) := by
    have he := heval b x
    rw [out16,two_last,hqe] at he
    have sz : (pushGate (tape p (xs b x)) A).length = 16 := by
      simp [pushGate,tape_length,xsLength,hp]
    rwa [← sz, appendedBit] at he
  have aPort (b : Bool) (x : Fin 6 → Bool) :
      (pushGate (tape p (xs b x)) A).getD 15 false =
        (b || (tape p (xs b x)).getD 12 false) := by
    have hl : (tape p (xs b x)).length = 15 := by simp [tape_length,xsLength,hp]
    rw [evalA, ← hl, appendedBit]
  have hq15 : q ≠ 15 := by
    intro h
    have e := fullFactor true empty
    dsimp only at e
    rw [h, aPort] at e
    contradiction
  intro x hx
  have on := fullFactor true x
  dsimp only at on
  rw [aPort] at on
  simp only [Bool.true_or, Bool.true_and, ↓reduceIte, hx] at on
  have aq : (pushGate (tape p (xs false x)) A).getD q false =
      (pushGate (tape p (xs true x)) A).getD q false := by
    have h0 : (tape p (xs false x)).length = 15 := by simp [tape_length,xsLength,hp]
    have h1 : (tape p (xs true x)).length = 15 := by simp [tape_length,xsLength,hp]
    by_cases h : q < 15
    · rw [evalA, evalA, List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)]
      obtain ⟨z,hz0,hz1⟩ := prefix_bits p hno (List.ofFn x)
      have e0 : tape p (xs false x) = false::z := hz0
      have e1 : tape p (xs true x) = true::z := hz1
      rw [e0,e1]
      exact cons_read _ _ _ _ hq0
    · have hbig : 16 ≤ q := by omega
      rw [List.getD_eq_default _ _ (by rw [evalA]; simp [h0]; omega),
        List.getD_eq_default _ _ (by rw [evalA]; simp [h1]; omega)]
  have off := fullFactor false x
  dsimp only at off
  rw [aPort, aq, on] at off
  simpa [xs] using off

private theorem cut_from_cycle (C : Circuit) (i k : Fin C.gates.length)
    (hi : i.val = 8) (hk : i.val < k.val)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size = 10)
    (heval : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = edgeCycle x)
    (hi0 : 0 ∈ (C.gates.get i).inputs) (hi12 : 12 ∈ (C.gates.get i).inputs)
    (huniq : ∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i)
    (hio : (C.gates.get i).op = .or) (hka : (C.gates.get k).op = .and)
    (hkin : 7 + i.val ∈ (C.gates.get k).inputs) :
    ∃ E : Circuit, PEqualNP.MetaComplexity.FanInTwo E ∧ E.size = 6 ∧
      E.output = 12 ∧ (∀ g ∈ E.gates, 0 ∉ g.inputs) ∧
      ∀ x : Fin 6 → Bool, rootOn x = true → E.eval (false :: List.ofFn x) = edgePath x := by
  have hlen : C.gates.length = 10 := hs
  have hk9 : k.val = 9 := by have := k.isLt; omega
  let p := C.gates.take 8
  have hp : p.length = 8 := by simp [p,hlen]
  have hd : (C.gates.drop 8).length = 2 := by simp [hlen]
  obtain ⟨A,B,hAB⟩ := List.length_eq_two.mp hd
  have hlist : C.gates = p ++ [A,B] := by
    change C.gates = (C.gates.take 8) ++ [A,B]
    rw [← hAB, List.take_append_drop]
  let bogus : Gate := ⟨.or,[]⟩
  have getD_get (j : Fin C.gates.length) :
      C.gates.get j = C.gates.getD j.val bogus := by
    rw [List.getD_eq_getElem _ _ j.isLt]
    rfl
  have gi : C.gates.get i = A := by
    rw [getD_get, hi, hlist, List.getD_append_right _ _ _ _ (by omega)]
    simp [hp]
  have gk : C.gates.get k = B := by
    rw [getD_get, hk9, hlist, List.getD_append_right _ _ _ _ (by omega)]
    simp [hp]
  rw [gi] at hi0 hi12 hio
  rw [gk, hi] at hkin
  rw [gk] at hka
  have hA : A ∈ C.gates := by rw [hlist]; simp
  have hB : B ∈ C.gates := by rw [hlist]; simp
  have noB : 0 ∉ B.inputs := by
    intro haz
    have h := huniq k (gk ▸ haz)
    have e := congrArg Fin.val h
    omega
  have nop : ∀ g ∈ p, 0 ∉ g.inputs := by
    intro g hg hz
    obtain ⟨j,hj,hjv⟩ := List.mem_iff_getElem.mp hg
    let jj : Fin C.gates.length := ⟨j,by omega⟩
    have e : C.gates.get jj = g := by
      rw [getD_get]
      change C.gates.getD j bogus = g
      rw [hlist, List.getD_append _ _ _ _ hj, List.getD_eq_getElem _ _ hj, hjv]
    have he := huniq jj (e ▸ hz)
    have h := congrArg Fin.val he
    change j = i.val at h
    omega
  have hm : ∀ x : Fin 7 → Bool, (tape (p++[A,B]) (List.ofFn x)).getD C.output false =
      edgeCycle x := by
    intro x
    have h := heval x
    change (tape C.gates (List.ofFn x)).getD C.output false = edgeCycle x at h
    simpa only [hlist] using h
  have hoff := cofactor_reduction p A B C.output hp nop hio
    (both_first (hfan A hA).2 hi0 hi12 (by decide)) hka (hfan B hB).2 hkin noB hm
  let E : Circuit := ⟨p.take 6,12⟩
  have hpl : (p.take 6).length = 6 := by simp [hp]
  refine ⟨E,?_,hpl,rfl,?_,?_⟩
  · intro g hg
    have hin : g ∈ p := List.mem_of_mem_take hg
    exact hfan g (by rw [hlist]; exact List.mem_append.mpr (Or.inl hin))
  · intro g hg
    exact nop g (List.mem_of_mem_take hg)
  · intro x hx
    change (tape (p.take 6) (false :: List.ofFn x)).getD 12 false = edgePath x
    have e := hoff x hx
    rw [← List.take_append_drop 6 p,
      tape_append_read _ _ _ _ (by simp [hpl])] at e
    exact e

open PEqualNP.CircuitLowerBounds

def shiftGate (g : Gate) : Gate := ⟨g.op, g.inputs.map (· - 1)⟩

def shiftCircuit (C : Circuit) : Circuit := ⟨C.gates.map shiftGate, C.output-1⟩

@[simp] theorem shift_size (C : Circuit) : (shiftCircuit C).size = C.size := by
  simp [shiftCircuit, Circuit.size]

@[simp] theorem shift_output (C : Circuit) : (shiftCircuit C).output = C.output-1 := rfl

theorem shift_fanin (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (shiftCircuit C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  simpa [shiftGate] using h g' hg'

private theorem cons_getD_sub (xs : List Bool) (w : ℕ) (hw : w ≠ 0) :
    (false :: xs).getD w false = xs.getD (w-1) false := by
  cases w with
  | zero => exact (hw rfl).elim
  | succ w => rfl

private theorem shift_gate_val (g : Gate) (xs : List Bool) (h : 0 ∉ g.inputs) :
    g.op.eval (g.inputs.map (fun w => (false :: xs).getD w false)) =
      (shiftGate g).op.eval ((shiftGate g).inputs.map (fun w => xs.getD w false)) := by
  change _ = g.op.eval ((g.inputs.map (·-1)).map (fun w => xs.getD w false))
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro w hw
  exact cons_getD_sub xs w (fun he => h (he ▸ hw))

theorem shift_wires (C : Circuit) (xs : List Bool)
    (h : ∀ g ∈ C.gates, 0 ∉ g.inputs) :
    C.wires (false :: xs) = false :: (shiftCircuit C).wires xs := by
  rcases C with ⟨gs,o⟩
  simp only [Circuit.wires, shiftCircuit]
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht (k : Gate) (hk : k ∈ gs) : 0 ∉ k.inputs := h k (by simp [hk])
    simp only [List.foldl_cons, List.map_cons]
    rw [shift_gate_val g xs hg]
    simpa only [List.cons_append] using
      ih (xs ++ [(shiftGate g).op.eval ((shiftGate g).inputs.map (fun w => xs.getD w false))]) ht

theorem shift_eval (C : Circuit) (xs : List Bool)
    (h : ∀ g ∈ C.gates, 0 ∉ g.inputs) (hOut : C.output ≠ 0) :
    (shiftCircuit C).eval xs = C.eval (false :: xs) := by
  simp only [Circuit.eval, shift_output, shift_wires C xs h]
  exact (cons_getD_sub _ _ hOut).symm

private def path (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)

private def envelope (x : Fin 6 → Bool) : Bool :=
  x 0 || x 5 || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)

private def extra (x : Fin 6 → Bool) : Bool := x 1 && x 4

private def atExtra (i : Fin 6) : Bool := decide (i = 1 ∨ i = 4)

private def baseline (i : Fin 6) : Fin 6 → Bool :=
  let S : Fin 6 → List (Fin 6) := ![[1,5],[0],[1,5],[0,4],[5],[0,4]]
  fun j => decide (j ∈ S i)

private theorem path_covered : ∀ x : Fin 6 → Bool, path x = true → envelope x = true := by
  decide +kernel

private theorem forcing_false : ∀ x : Fin 6 → Bool, path x = false → extra x = false →
    ∃ y : Fin 6 → Bool, x ≤ y ∧ envelope y = true ∧ path y = false := by
  decide +kernel

private theorem only_extra : ∀ x : Fin 6 → Bool, path x = false → extra x = true →
    ∀ i, x i = atExtra i := by
  decide +kernel

private theorem positive_toggle (w : (Fin 6 → Bool) → Bool)
    (h : ∀ x, (envelope x && w x) = path x) (i : Fin 6) :
    ∃ x : Fin 6 → Bool, x i = false ∧ w x = false ∧ w (Function.update x i true) = true := by
  have check : ∀ j : Fin 6,
      baseline j j = false ∧ envelope (baseline j) = true ∧ path (baseline j) = false ∧
        envelope (Function.update (baseline j) j true) = true ∧
          path (Function.update (baseline j) j true) = true := by decide +kernel
  obtain ⟨h0,hq0,hp0,hq1,hp1⟩ := check i
  exact ⟨baseline i,h0,by simpa only [hq0, Bool.true_and, hp0] using h (baseline i),
    by simpa only [hq1, Bool.true_and, hp1] using h (Function.update (baseline i) i true)⟩

private theorem monotone_completion (w : (Fin 6 → Bool) → Bool) (mono : Monotone w)
    (h : ∀ x, (envelope x && w x) = path x) (x : Fin 6 → Bool) :
    w x = (path x || (w atExtra && extra x)) := by
  by_cases hp : path x = true
  · have hq := path_covered x hp
    simpa only [hq, Bool.true_and, hp, Bool.true_or] using h x
  have hpf : path x = false := Bool.eq_false_iff.mpr hp
  by_cases he : extra x = true
  · have eq := funext (only_extra x hpf he)
    rw [hpf, he, Bool.false_or, Bool.and_true, eq]
  have hef : extra x = false := Bool.eq_false_iff.mpr he
  obtain ⟨y,hxy,hq,hy⟩ := forcing_false x hpf hef
  have wy : w y = false := by simpa only [hq, Bool.true_and, hy] using h y
  have le := mono hxy
  rw [wy] at le
  have wx : w x = false := by
    cases e : w x with
    | false => rfl
    | true => rw [e] at le; contradiction
  simp only [hpf, hef, Bool.false_or, Bool.and_false, wx]

namespace LowerBounds

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool


def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨s', hs, h'⟩ := gate_elim_one n _ b s hdep' hnc' hg
  refine ⟨s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by simp [hσ, Equiv.swap_apply_right]
    rw [this]; exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

private theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s+1 := by
  simpa using dep_lower_set n f Finset.univ (fun i _ => hdep i) s h

def path3 (x : Fin 3 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2)

def path4 (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

def path5 (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)

def path6 (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5)

private def path2WithFree (x : Fin 3 → Bool) : Bool := x 0 || (x 1 && x 2)

private def path4WithFree (x : Fin 5 → Bool) : Bool :=
  x (Fin.last 4) || path4 (fun i => x i.castSucc)

private theorem same_cost_relabel {m n s bound : ℕ} {f : (Fin m → Bool) → Bool}
    {g : (Fin n → Bool) → Bool} (rename : Fin m → Fin n)
    (eq : ∀ x, f (x ∘ rename) = g x)
    (lower : ∀ t, HasCircuitSize n g t → bound ≤ t)
    (circuit : HasCircuitSize m f s) : bound ≤ s := by
  apply lower s
  rw [← funext eq]
  exact relabel_size rename f s circuit

private abbrev PathDep {m : ℕ} (f : (Fin m → Bool) → Bool) (j : Fin m) :=
  ∃ x, f (Function.update x j (!x j)) ≠ f x

private abbrev PathCofactorNC {m : ℕ} (f : (Fin m → Bool) → Bool) (j : Fin m) :=
  ∀ b : Bool, ∃ x y, f (Function.update x j b) ≠ f (Function.update y j b)

private theorem two_equal_cofactors {n bound s : ℕ} (f : (Fin (n + 1) → Bool) → Bool)
    (j : Fin (n + 1)) (essential : PathDep f j) (nc : PathCofactorNC f j)
    (lower : ∀ b t, HasCircuitSize (n + 1) (fun x => f (Function.update x j b)) t → bound ≤ t)
    (circuit : HasCircuitSize (n + 1) f s) : bound + 2 ≤ s := by
  obtain ⟨b, t, count, cofactor⟩ := gate_elim_at n f j s essential nc circuit
  have := lower b t cofactor
  omega

theorem path3_lower (s : ℕ) (circuit : HasCircuitSize 3 path3 s) : 2 ≤ s := by
  have deps : ∀ j : Fin 3, PathDep path3 j := by unfold PathDep; decide +kernel
  have := dep_lower 3 path3 deps s circuit
  omega

private theorem path2_with_free_lower (s : ℕ) (circuit : HasCircuitSize 3 path2WithFree s) : 2 ≤ s := by
  have deps : ∀ j : Fin 3, PathDep path2WithFree j := by unfold PathDep; decide +kernel
  have := dep_lower 3 path2WithFree deps s circuit
  omega

theorem path4_lower (s : ℕ) (circuit : HasCircuitSize 4 path4 s) : 4 ≤ s := by
  have essential : PathDep path4 0 := ⟨fun j => decide (j = 1), by decide +kernel⟩
  have nc : PathCofactorNC path4 0 := by
    intro b
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    cases b <;> decide +kernel
  have lower : ∀ b t, HasCircuitSize 4 (fun x => path4 (Function.update x 0 b)) t → 2 ≤ t := by
    intro b
    cases b
    · exact fun s h => same_cost_relabel (![0, 0, 1, 2] : Fin 4 → Fin 3)
        (by decide +kernel) path3_lower h
    · exact fun s h => same_cost_relabel (![0, 0, 1, 2] : Fin 4 → Fin 3)
        (by decide +kernel) path2_with_free_lower h
  exact two_equal_cofactors path4 0 essential nc lower circuit

theorem path5_lower (s : ℕ) (circuit : HasCircuitSize 5 path5 s) : 5 ≤ s := by
  have essential : PathDep path5 0 := ⟨fun j => decide (j = 1), by decide +kernel⟩
  have nc : PathCofactorNC path5 0 := by
    intro b
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    cases b <;> decide +kernel
  have lower : ∀ t, HasCircuitSize 5 (fun x => path5 (Function.update x 0 false)) t → 4 ≤ t :=
    fun _ h => same_cost_relabel (![0, 0, 1, 2, 3] : Fin 5 → Fin 4)
      (by decide +kernel) path4_lower h
  obtain ⟨t,ht,smaller⟩ := one_gate_at 4 path5 0 false s essential (nc false) circuit
  have := lower t smaller
  omega

private theorem path4_with_free_lower (s : ℕ) (circuit : HasCircuitSize 5 path4WithFree s) : 5 ≤ s := by
  have essential : PathDep path4WithFree 4 := ⟨fun _ => false, by decide +kernel⟩
  have nc : ∃ x y, path4WithFree (Function.update x 4 false) ≠
      path4WithFree (Function.update y 4 false) := ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨t,ht,smaller⟩ := one_gate_at 4 path4WithFree 4 false s essential nc circuit
  have lb : 4 ≤ t := same_cost_relabel (![0,1,2,3,0] : Fin 5 → Fin 4)
    (by decide +kernel) path4_lower smaller
  omega

theorem path6_lower (s : ℕ) (circuit : HasCircuitSize 6 path6 s) : 7 ≤ s := by
  have essential : PathDep path6 0 := ⟨fun j => decide (j = 1), by decide +kernel⟩
  have nc : PathCofactorNC path6 0 := by
    intro b
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    cases b <;> decide +kernel
  have lower : ∀ b t, HasCircuitSize 6 (fun x => path6 (Function.update x 0 b)) t → 5 ≤ t := by
    intro b
    cases b
    · exact fun s h => same_cost_relabel (![0, 0, 1, 2, 3, 4] : Fin 6 → Fin 5)
        (by decide +kernel) path5_lower h
    · exact fun s h => same_cost_relabel (![4, 4, 0, 1, 2, 3] : Fin 6 → Fin 5)
        (by decide +kernel) path4_with_free_lower h
  exact two_equal_cofactors path6 0 essential nc lower circuit

private def square (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 3)

private def starOrFree (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || x 3

private def squareLeaf (x : Fin 5 → Bool) : Bool :=
  square (fun i => x i.castSucc) || (x 3 && x 4)

private def path6Chord (x : Fin 6 → Bool) : Bool :=
  path6 x || (x 1 && x 4)

private theorem square_lower (s : ℕ) (c : HasCircuitSize 4 square s) : 3 ≤ s := by
  have h := dep_lower 4 square (by decide +kernel) s c
  omega

private theorem star_free_lower (s : ℕ) (c : HasCircuitSize 4 starOrFree s) : 3 ≤ s := by
  have h := dep_lower 4 starOrFree (by decide +kernel) s c
  omega

private theorem square_leaf_lower (s : ℕ) (c : HasCircuitSize 5 squareLeaf s) : 5 ≤ s := by
  have essential : PathDep squareLeaf 4 := ⟨fun j => decide (j=3), by decide +kernel⟩
  have nc : PathCofactorNC squareLeaf 4 := by
    intro b
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    cases b <;> decide +kernel
  have lower : ∀ b t, HasCircuitSize 5 (fun x => squareLeaf (Function.update x 4 b)) t → 3 ≤ t := by
    intro b
    cases b
    · exact fun _ h => same_cost_relabel (![0,1,2,3,0] : Fin 5 → Fin 4)
        (by decide +kernel) square_lower h
    · exact fun _ h => same_cost_relabel (![0,1,2,3,0] : Fin 5 → Fin 4)
        (by decide +kernel) star_free_lower h
  exact two_equal_cofactors squareLeaf 4 essential nc lower c

private theorem path6_chord_lower (s : ℕ) (c : HasCircuitSize 6 path6Chord s) : 7 ≤ s := by
  have essential : PathDep path6Chord 0 := ⟨fun j => decide (j=1), by decide +kernel⟩
  have nc : PathCofactorNC path6Chord 0 := by
    intro b
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    cases b <;> decide +kernel
  have lower : ∀ b t, HasCircuitSize 6 (fun x => path6Chord (Function.update x 0 b)) t → 5 ≤ t := by
    intro b
    cases b
    · exact fun _ h => same_cost_relabel (![0,0,1,2,3,4] : Fin 6 → Fin 5)
        (by decide +kernel) square_leaf_lower h
    · exact fun _ h => same_cost_relabel (![4,4,0,1,2,3] : Fin 6 → Fin 5)
        (by decide +kernel) path4_with_free_lower h
  exact two_equal_cofactors path6Chord 0 essential nc lower c

end LowerBounds

open LowerBounds

private theorem rootOn_envelope : ∀ x : Fin 6 → Bool, rootOn x = envelope x := by
  decide +kernel

private theorem envelope_agreement (C : Circuit)
    (hfit : ∀ x : Fin 6 → Bool, rootOn x = true →
      C.eval (List.ofFn x) = edgePath x) :
    ∀ x : Fin 6 → Bool, (envelope x && C.eval (List.ofFn x)) = path x := by
  intro x
  cases h : envelope x
  · have hn : path x ≠ true := fun hp => by
      have := path_covered x hp
      rw [h] at this
      contradiction
    have hf := Bool.eq_false_iff.mpr hn
    simp [hf]
  · have h' := hfit x ((rootOn_envelope x).trans h)
    simpa only [Bool.true_and, path, edgePath] using h'

private theorem complete_after_mono (C : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 6)
    (hfit : ∀ x : Fin 6 → Bool, (envelope x && C.eval (List.ofFn x)) = path x)
    (hm : Monotone (fun x : Fin 6 → Bool => C.eval (List.ofFn x))) : False := by
  let w := fun x : Fin 6 → Bool => C.eval (List.ofFn x)
  have hex := monotone_completion w hm hfit
  cases h : w atExtra
  · have ev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = path6 x := by
      intro x
      have eq := hex x
      simpa only [h, path6, path, w, Bool.false_and, Bool.or_false] using eq
    have impossible := path6_lower 6 ⟨C,hfan,hs,ev⟩
    omega
  · have ev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = path6Chord x := by
      intro x
      have eq := hex x
      simpa only [h, path6Chord, path6, path, extra, w, Bool.true_and] using eq
    have impossible := path6_chord_lower 6 ⟨C,hfan,hs,ev⟩
    omega

namespace Monotonicity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def compute (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => x.getD i false)

def step (x : List Bool) (g : Gate) : List Bool := x ++ [compute x g]

theorem snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl step x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, step, ih]; omega


theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem pre (gs : List Gate) : ∀ (x : List Bool) (w : ℕ), w < x.length →
    (gs.foldl step x).getD w false = x.getD w false := by
  induction gs with
  | nil => intro x w _; rfl
  | cons g gs ih =>
    intro x w h
    rw [List.foldl_cons, ih _ _ (by simp [step]; omega), step, snoc, ite_eq_left h]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl step w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (step (gs.foldl step w) g).getD i false = (gs.foldl step w).getD i false := by
      intro i hi
      simp only [step, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (step (gs.foldl step w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false) := by
        simp only [step, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen, compute, List.getD_eq_getElem?_getD]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl




theorem gate_formula (C : Circuit) {N j : ℕ} (x : List Bool)
    (hx : x.length = N) (hj : j < C.gates.length) :
    (C.gates.foldl step x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < N + j then (C.gates.foldl step x).getD i false else false) := by
  have h := foldl_char C.gates x j hj
  rw [hx] at h
  exact h

def before (C : Circuit) (N j w : ℕ) : Prop := w ∈ (gateAt C j).inputs ∧ w < N + j

def closed (N : ℕ) (C : Circuit) (L : Finset ℕ) : Prop :=
  (∀ j ∈ L, j < C.gates.length) ∧
    ∀ j ∈ L, ∀ i, before C N j (N + i) → i ∈ L

theorem minimal_closed (N : ℕ) (C : Circuit) (r : ℕ) (hr : r < C.gates.length) :
    ∃ L : Finset ℕ, r ∈ L ∧ closed N C L ∧
      ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N + i) := by
  classical
  let A := Finset.range C.gates.length
  have hc : closed N C A := by
    refine ⟨fun j hj => Finset.mem_range.mp hj, ?_⟩
    intro j hj i hi
    have hlt := Finset.mem_range.mp hj
    have hs := hi.2
    exact Finset.mem_range.mpr (by omega)
  let candidates := A.powerset.filter fun L => r ∈ L ∧ closed N C L
  have hA : A ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), Finset.mem_range.mpr hr, hc⟩
  obtain ⟨L, hL, hmin⟩ := candidates.exists_min_image Finset.card ⟨A, hA⟩
  obtain ⟨hsub, hrL, hclose⟩ := Finset.mem_filter.mp hL
  refine ⟨L, hrL, hclose, ?_⟩
  intro i hi hir
  by_contra hn
  have hs : L.erase i ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_erase.mpr ⟨Ne.symm hir, hrL⟩, ?_⟩
    · exact (Finset.erase_subset _ _).trans (Finset.mem_powerset.mp hsub)
    · constructor
      · intro j hj
        exact hclose.1 j (Finset.mem_of_mem_erase hj)
      · intro j hj k hkj
        have hj' := Finset.mem_of_mem_erase hj
        refine Finset.mem_erase.mpr ⟨?_, hclose.2 j hj' k hkj⟩
        rintro rfl
        exact hn ⟨j, hj', hkj⟩
  have h := hmin _ hs
  have hpos := Finset.card_pos.mpr ⟨i, hi⟩
  rw [Finset.card_erase_of_mem hi] at h
  omega

def inputSlots (N : ℕ) (C : Circuit) (j : ℕ) : Finset (ℕ × ℕ) :=
  ((gateAt C j).inputs.toFinset.filter (· < N + j)).image (Prod.mk j)

def slots (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (ℕ × ℕ) :=
  L.biUnion (inputSlots N C)

theorem mem_slot {N : ℕ} {C : Circuit} {L : Finset ℕ} {j w : ℕ} :
    (j,w) ∈ slots N C L ↔ j ∈ L ∧ before C N j w := by
  constructor
  · intro h
    obtain ⟨j', hj', hh⟩ := Finset.mem_biUnion.mp h
    obtain ⟨w', hw', he⟩ := Finset.mem_image.mp hh
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    have ⟨hi,hl⟩ := Finset.mem_filter.mp hw'
    exact ⟨hj', List.mem_toFinset.mp hi, hl⟩
  · rintro ⟨hj, hw, hl⟩
    exact Finset.mem_biUnion.mpr
      ⟨j,hj,Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw,hl⟩,rfl⟩⟩

def used (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset ℕ :=
  (slots N C L).image Prod.snd

theorem mem_used {N : ℕ} {C : Circuit} {L : Finset ℕ} {w : ℕ} :
    w ∈ used N C L ↔ ∃ j ∈ L, before C N j w := by
  constructor
  · intro h
    obtain ⟨⟨j,i⟩, hslot, e⟩ := Finset.mem_image.mp h
    change i = w at e
    subst i
    exact ⟨j,(mem_slot.mp hslot).1,(mem_slot.mp hslot).2⟩
  · rintro ⟨j,hj,hw⟩
    exact Finset.mem_image.mpr ⟨(j,w),mem_slot.mpr ⟨hj,hw⟩,rfl⟩

theorem closed_values {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (he : ∀ i ∈ used N C L, x.getD i false = y.getD i false) :
    ∀ j ∈ L, (C.gates.foldl step x).getD (N + j) false =
      (C.gates.foldl step y).getD (N + j) false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    rw [gate_formula C x hx (hL.1 j hj), gate_formula C y hy (hL.1 j hj)]
    congr 1
    apply List.map_congr_left
    intro w hw
    split_ifs with hb <;> try rfl
    by_cases hi : w < N
    · rw [pre _ _ _ (by omega : w < x.length), pre _ _ _ (by omega : w < y.length)]
      exact he w (mem_used.mpr ⟨j,hj,hw,hb⟩)
    · let i := w - N
      have e : N + i = w := by dsimp [i]; omega
      have hil : i < j := by omega
      rw [← e] at hw hb ⊢
      exact ih i hil (hL.2 j hj i ⟨hw,hb⟩)



namespace Network

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def trimGate (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.not, g.inputs.take 1⟩
  | _ => g

def trim (C : Circuit) : Circuit :=
  ⟨C.gates.map trimGate, C.output⟩

theorem trimGate_eval (g : Gate) (x : List Bool) :
    compute x (trimGate g) = compute x g := by
  cases g with
  | mk op inp =>
    cases op <;> try rfl
    cases inp <;> rfl

theorem trim_eval (C : Circuit) (x : List Bool) :
    (trim C).eval x = C.eval x := by
  have h (gs : List Gate) (v : List Bool) :
      (gs.map trimGate).foldl step v = gs.foldl step v := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, ih, step, trimGate_eval]
  change ((C.gates.map trimGate).foldl step x).getD C.output false = _
  rw [h]
  rfl

theorem trim_fan (C : Circuit) (h : FanInTwo C) : FanInTwo (trim C) := by
  intro g hg
  change g ∈ C.gates.map trimGate at hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨ha', hs⟩ := h a ha
  rcases a with ⟨o, l⟩
  cases o <;> simp_all [trimGate]

theorem trim_unary (C : Circuit) :
    ∀ g ∈ (trim C).gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
  intro g hg he
  change g ∈ C.gates.map trimGate at hg
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
  rcases a with ⟨o, l⟩
  cases o <;> simp_all [trimGate]

def edgeTo (N : ℕ) (C : Circuit) (L : Finset ℕ) (w v : ℕ) : Prop :=
  ∃ j ∈ L, v = N + j ∧ before C N j w

abbrev reaches (N : ℕ) (C : Circuit) (L : Finset ℕ) :=
  Relation.ReflTransGen (edgeTo N C L)

theorem edgeIncreases {N : ℕ} {C : Circuit} {L : Finset ℕ} {w v : ℕ}
    (h : edgeTo N C L w v) : w < v := by
  obtain ⟨j, _, rfl, _, h⟩ := h
  exact h

theorem reachIncreases {N : ℕ} {C : Circuit} {L : Finset ℕ} {w v : ℕ}
    (h : reaches N C L w v) : w ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ e ih => exact ih.trans (Nat.le_of_lt (edgeIncreases e))

def value (N : ℕ) (C : Circuit) (x : ℕ → Bool) (override : ℕ → Option Bool)
    (w : ℕ) : Bool :=
  match override w with
  | some b => b
  | none =>
    if w < N then x w
    else if w - N < C.gates.length then
      let g := gateAt C (w - N)
      g.op.eval (g.inputs.map fun u => if _h : u < w then value N C x override u else false)
    else false
termination_by w

def relay (f : ℕ) (b : Bool) (w : ℕ) : Option Bool :=
  if w = f then some b else none

theorem val_raw {N : ℕ} {C : Circuit} {x : ℕ → Bool} {O : ℕ → Option Bool}
    {w : ℕ} (hw : w < N) (ho : O w = none) :
    value N C x O w = x w := by
  rw [value, ho, ite_eq_left hw]

theorem val_gate {N : ℕ} {C : Circuit} {x : ℕ → Bool} {O : ℕ → Option Bool}
    {j : ℕ} (hj : j < C.gates.length) (ho : O (N+j) = none) :
    value N C x O (N+j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun u =>
        if u < N+j then value N C x O u else false) := by
  rw [value, ho, ite_eq_right (by omega : ¬ N+j < N)]
  simp only [Nat.add_sub_cancel_left, ite_eq_left hj]
  rfl

theorem val_relay (N : ℕ) (C : Circuit) (x : ℕ → Bool) (f : ℕ) (b : Bool) :
    value N C x (relay f b) f = b := by
  rw [value]
  simp [relay]

theorem val_fold (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (w : ℕ) :
    value N C (fun i => x.getD i false) (fun _ => none) w =
      (C.gates.foldl step x).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < N
    · rw [val_raw hw rfl, pre _ _ _ (by omega)]
    · by_cases hreal : w - N < C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w-N, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [val_gate hj rfl, gate_formula C x hx hj]
        congr 1
        apply List.map_congr_left
        intro u _
        split_ifs with h
        · exact ih u h
        · rfl
      · rw [value, ite_eq_right hw, ite_eq_right hreal, getD_ge]
        rw [len, hx]
        omega

theorem val_original (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) :
    value N C (fun i => x.getD i false) (fun _ => none) C.output = C.eval x :=
  val_fold N C x hx C.output

def live (N : ℕ) (L : Finset ℕ) (w : ℕ) : Prop :=
  w < N ∨ ∃ j ∈ L, w = N+j

theorem prev_live {N : ℕ} {C : Circuit} {L : Finset ℕ} (closedL : closed N C L)
    {j u : ℕ} (hj : j ∈ L) (hb : before C N j u) : live N L u := by
  by_cases hu : u < N
  · exact .inl hu
  · have eq : u = N + (u-N) := by omega
    right
    refine ⟨u-N, closedL.2 j hj _ ?_, eq⟩
    rwa [← eq]

theorem path_head {N : ℕ} {C : Circuit} {L : Finset ℕ} {w v : ℕ}
    (p : reaches N C L w v) (neq : w ≠ v) :
    ∃ z, edgeTo N C L w z ∧ reaches N C L z v := by
  induction p with
  | refl => exact (neq rfl).elim
  | @tail b c p e ih =>
    by_cases h : w = b
    · subst b
      exact ⟨c,e,.refl⟩
    · obtain ⟨z,hz,hp⟩ := ih h
      exact ⟨z,hz,hp.tail e⟩

theorem every_gate_reaches_root {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (cl : closed N C L) {r : ℕ}
    (next : ∀ j ∈ L, j ≠ r → ∃ k ∈ L, before C N k (N+j))
    (j : ℕ) (hj : j ∈ L) : reaches N C L (N+j) (N+r) := by
  by_cases e : j = r
  · subst j
    exact .refl
  · obtain ⟨k, hk, hb⟩ := next j hj e
    have hlt := hb.2
    have hkvalid := cl.1 k hk
    exact .head ⟨k, hk, rfl, hb⟩ (every_gate_reaches_root cl next k hk)
termination_by C.gates.length - j
decreasing_by omega

theorem value_agree {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (w : ℕ) (hw : live N L w) (x y : ℕ → Bool) (O P : ℕ → Option Bool)
    (raw : ∀ u < N, reaches N C L u w → x u = y u)
    (hOverride : ∀ u, reaches N C L u w → O u = P u) :
    value N C x O w = value N C y P w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have he := hOverride w (.refl)
    cases hO : O w with
    | some b =>
      have hP : P w = some b := he.symm.trans hO
      rw [value, hO]
      symm
      rw [value, hP]
    | none =>
      have hP : P w = none := he.symm.trans hO
      rcases hw with hw | ⟨j,hj,rfl⟩
      · rw [val_raw hw hO, val_raw hw hP, raw w hw .refl]
      · rw [val_gate (cl.1 j hj) hO, val_gate (cl.1 j hj) hP]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with h
        · let E : edgeTo N C L u (N+j) := ⟨j, hj, rfl, hu, h⟩
          apply ih u h (prev_live cl hj ⟨hu,h⟩)
          · intro v hv p
            exact raw v hv (p.tail E)
          · intro v p
            exact hOverride v (p.tail E)
        · rfl

theorem replace_signal {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (x : ℕ → Bool) (f w : ℕ) (hw : live N L w) :
    value N C x (fun _ => none) w =
      value N C x (relay f (value N C x (fun _ => none) f)) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w = f
    · subst w
      exact (val_relay N C x f _).symm
    · have ho : relay f (value N C x (fun _ => none) f) w = none := by simp [relay,h]
      rcases hw with hraw | ⟨j,hj,rfl⟩
      · rw [val_raw hraw ho, val_raw hraw rfl]
      · rw [val_gate (cl.1 j hj) ho, val_gate (cl.1 j hj) rfl]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with hlt
        · exact ih u hlt (prev_live cl hj ⟨hu,hlt⟩)
        · rfl

theorem no_leak {N : ℕ} {C : Circuit} {L : Finset ℕ} {f u w : ℕ}
    (single : ∀ a, a ≠ f → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    (e : edgeTo N C L u w) (inside : reaches N C L u f) (hne : u ≠ f) :
    reaches N C L w f := by
  obtain ⟨z, ez, p⟩ := path_head inside hne
  rwa [← single u hne w z e ez] at p

theorem cut_agree {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (f : ℕ)
    (single : ∀ a, a ≠ f → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    (b : Bool) (x y : ℕ → Bool)
    (raw : ∀ u < N, ¬ reaches N C L u f → x u = y u)
    (w : ℕ) (hw : live N L w) (out : w = f ∨ ¬ reaches N C L w f) :
    value N C x (relay f b) w = value N C y (relay f b) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases out with rfl | out
    · rw [val_relay, val_relay]
    · have ne : w ≠ f := fun e => out (e ▸ .refl)
      have ho : relay f b w = none := by simp [relay,ne]
      rcases hw with hw | ⟨j,hj,rfl⟩
      · rw [val_raw hw ho, val_raw hw ho, raw w hw out]
      · rw [val_gate (cl.1 j hj) ho, val_gate (cl.1 j hj) ho]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with h
        · let E : edgeTo N C L u (N+j) := ⟨j,hj,rfl,hu,h⟩
          apply ih u h (prev_live cl hj ⟨hu,h⟩)
          by_cases ef : u = f
          · exact .inl ef
          · exact .inr (fun p => out (no_leak single E p ef))
        · rfl

theorem gate_order (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : ℕ → Bool) (h : ∀ i ∈ g.inputs, u i = true → v i = true) :
    g.op.eval (g.inputs.map u) = true → g.op.eval (g.inputs.map v) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hm b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact h i hi (hm _ ⟨i,hi,rfl⟩)
  · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i,hi,rfl⟩, hb⟩
    exact ⟨v i, ⟨i,hi,rfl⟩, h i hi hb⟩

theorem value_mono {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (w : ℕ) (hw : live N L w) (x y : ℕ → Bool) (O P : ℕ → Option Bool)
    (raw : ∀ u < N, reaches N C L u w → x u = true → y u = true)
    (hOverride : ∀ u, reaches N C L u w → (O u = none ∧ P u = none) ∨
      ∃ b c, O u = some b ∧ P u = some c ∧ (b = true → c = true))
    (gates : ∀ j ∈ L, reaches N C L (N+j) w → O (N+j) = none →
      (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) :
    value N C x O w = true → value N C y P w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hOverride w .refl with ⟨hO,hP⟩ | ⟨b,c,hO,hP,hle⟩
    · rcases hw with hw | ⟨j,hj,rfl⟩
      · rw [val_raw hw hO, val_raw hw hP]
        exact raw w hw .refl
      · rw [val_gate (cl.1 j hj) hO, val_gate (cl.1 j hj) hP]
        apply gate_order _ (gates j hj .refl hO)
        intro u hu
        split_ifs with h
        · let E : edgeTo N C L u (N+j) := ⟨j,hj,rfl,hu,h⟩
          apply ih u h (prev_live cl hj ⟨hu,h⟩)
          · intro v hv p
            exact raw v hv (p.tail E)
          · intro v p
            exact hOverride v (p.tail E)
          · intro k hk p
            exact gates k hk (p.tail E)
        · exact id
    · have hx : value N C x O w = b := by rw [value,hO]
      have hy : value N C y P w = c := by rw [value,hP]
      simpa only [hx,hy] using hle

end Network


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

def rawUsed (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset ℕ :=
  (used N C L).filter (· < N)

noncomputable def activeNot (C : Circuit) (L : Finset ℕ) : Finset ℕ := by
  classical
  exact L.filter fun j => (gateAt C j).op = .not

theorem closed_eval_eq {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hL : closed N C L) (hr : r ∈ L) (ho : C.output = N+r)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (he : ∀ i ∈ used N C L, x.getD i false = y.getD i false) : C.eval x = C.eval y := by
  change (C.gates.foldl step x).getD C.output false = (C.gates.foldl step y).getD C.output false
  rw [ho]
  exact closed_values hL x y hx hy he r hr

theorem slots_count_low {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N+i)) :
    (rawUsed N C L).card + (L.card-1) ≤ (used N C L).card := by
  let I := (L.erase r).image (N + ·)
  have hdis : Disjoint (rawUsed N C L) I := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw'
    have := (Finset.mem_filter.mp hw).2
    omega
  have hsub : rawUsed N C L ∪ I ⊆ used N C L := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact (Finset.mem_filter.mp h).1
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hn,hm⟩ := Finset.mem_erase.mp hi
      exact mem_used.mpr (huse i hm hn)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ (fun a b h => by omega),
    Finset.card_erase_of_mem hr] at hc
  exact hc

theorem slots_count_high {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hC : FanInTwo C) (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) :
    (slots N C L).card + (activeNot C L).card ≤ 2*L.card := by
  classical
  have hmem (j : ℕ) (hj : j ∈ L) : gateAt C j ∈ C.gates := by
    have hb := hL.1 j hj
    rw [gateAt, List.getD_eq_getElem _ _ hb]
    exact List.getElem_mem _
  have hw (j : ℕ) : (inputSlots N C j).card ≤ (gateAt C j).inputs.length := by
    unfold inputSlots
    exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (List.toFinset_card_le _))
  have hpoint (j : ℕ) (hj : j ∈ L) :
      (inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0) ≤ 2 := by
    have hm := hmem j hj
    by_cases h : (gateAt C j).op = .not
    · have k := (hw j).trans (hNot _ hm h)
      simp [h]
      omega
    · simpa [h] using (hw j).trans (hC _ hm).2
  have hslots := Finset.card_biUnion_le (s := L) (t := inputSlots N C)
  have hn : (activeNot C L).card = ∑ j ∈ L, if (gateAt C j).op = .not then 1 else 0 := by
    unfold activeNot
    rw [Finset.card_filter]
  change (slots N C L).card ≤ ∑ j ∈ L, (inputSlots N C j).card at hslots
  have hsum : (∑ j ∈ L, ((inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0))) ≤
      ∑ _j ∈ L, (2 : ℕ) := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← hn] at hsum
  calc
    _ ≤ (∑ j ∈ L, (inputSlots N C j).card) + (activeNot C L).card := Nat.add_le_add_right hslots _
    _ ≤ ∑ _j ∈ L, (2 : ℕ) := hsum
    _ = _ := by simp [Nat.mul_comm]

theorem unique_reader_of_inj {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hinj : Set.InjOn Prod.snd (slots N C L : Set (ℕ × ℕ)))
    {j k w : ℕ} (hj : j ∈ L) (hk : k ∈ L) (he : before C N j w) (hf : before C N k w) : j = k := by
  exact congrArg Prod.fst (hinj (mem_slot.mpr ⟨hj,he⟩) (mem_slot.mpr ⟨hk,hf⟩) rfl)


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Network

private theorem gate_mem {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    {j : ℕ} (hj : j ∈ L) : gateAt C j ∈ C.gates := by
  rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
  exact List.getElem_mem _

private theorem budget_strict {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hC : FanInTwo C) (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1)
    {r : ℕ} (hr : r ∈ L) (hEmpty : ¬∃ w, before C N r w) :
    (slots N C L).card + (activeNot C L).card + 1 ≤ 2*L.card := by
  classical
  have hzero : inputSlots N C r = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨w, hw, _⟩ := Finset.mem_image.mp hp
    exact hEmpty ⟨w, List.mem_toFinset.mp (Finset.mem_filter.mp hw).1,
      (Finset.mem_filter.mp hw).2⟩
  have hpoint (j : ℕ) (hj : j ∈ L) :
      (inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0) ≤ 2 := by
    have hm := gate_mem hL hj
    have hw : (inputSlots N C j).card ≤ (gateAt C j).inputs.length := by
      unfold inputSlots
      exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (List.toFinset_card_le _))
    by_cases h : (gateAt C j).op = .not
    · have k := hw.trans (hNot _ hm h)
      simp [h]
      omega
    · simpa [h] using hw.trans (hC _ hm).2
  let fee (j : ℕ) := (inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0)
  have hf : fee r ≤ 1 := by
    by_cases h : (gateAt C r).op = .not <;> simp [fee,hzero,h]
  have hsum : (∑ j ∈ L.erase r, fee j) ≤ ∑ _j ∈ L.erase r, (2 : ℕ) :=
    Finset.sum_le_sum fun j hj => hpoint j (Finset.mem_of_mem_erase hj)
  have hslots := Finset.card_biUnion_le (s := L) (t := inputSlots N C)
  have hn : (activeNot C L).card = ∑ j ∈ L, if (gateAt C j).op = .not then 1 else 0 := by
    unfold activeNot
    rw [Finset.card_filter]
  have ha : (slots N C L).card + (activeNot C L).card ≤ ∑ j ∈ L, fee j := by
    simp only [fee, Finset.sum_add_distrib, ← hn]
    exact Nat.add_le_add_right hslots _
  have hfull := Finset.sum_erase_add _ fee hr
  have hs' : (∑ j ∈ L.erase r, fee j) ≤ 2*(L.card-1) := by
    simpa [Finset.card_erase_of_mem hr, Nat.mul_comm] using hsum
  have hpos : 0 < L.card := Finset.card_pos.mpr ⟨r,hr⟩
  omega

private theorem raw_ancestor {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hin : ∀ j ∈ L, ∃ w, before C N j w) {w : ℕ} (hw : live N L w) :
    ∃ i < N, reaches N C L i w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with hw | ⟨j,hj,rfl⟩
    · exact ⟨w,hw,.refl⟩
    · obtain ⟨u,hu⟩ := hin j hj
      obtain ⟨i,hi,hpath⟩ := ih u hu.2 (prev_live hL hj hu)
      exact ⟨i,hi,hpath.tail ⟨j,hj,rfl,hu⟩⟩

private theorem modes {C : Circuit} (hC : FanInTwo C) {g : Gate} (hg : g ∈ C.gates) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  simpa using (hC g hg).1

private theorem positive_op {C : Circuit} (hC : FanInTwo C) {g : Gate} (hg : g ∈ C.gates)
    (h : g.op ≠ .not) : g.op = .and ∨ g.op = .or := by
  rcases modes hC hg with ha | ho | hn
  · exact .inl ha
  · exact .inr ho
  · exact (h hn).elim

private theorem gate_not_order (g : Gate) (hop : g.op = .not)
    (u v : ℕ → Bool) (h : ∀ i ∈ g.inputs, u i = true → v i = true) :
    g.op.eval (g.inputs.map v) = true → g.op.eval (g.inputs.map u) = true := by
  rw [hop]
  cases hxs : g.inputs with
  | nil => simp [GateOp.eval]
  | cons a xs =>
    have ha := h a (by rw [hxs]; simp)
    cases hu : u a <;> cases hv : v a <;> simp_all [GateOp.eval]

private theorem negated_wire_order {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (hC : FanInTwo C) {j : ℕ} (hj : j ∈ L)
    (hnot : (gateAt C j).op = .not)
    (only : ∀ k ∈ L, (gateAt C k).op = .not → k = j)
    (x y : ℕ → Bool) (raw : ∀ i, x i = true → y i = true) :
    value N C y (fun _ => none) (N+j) = true →
      value N C x (fun _ => none) (N+j) = true := by
  rw [val_gate (hL.1 j hj) rfl, val_gate (hL.1 j hj) rfl]
  apply gate_not_order _ hnot
  intro u hu
  split_ifs with hlt
  · apply value_mono hL u (prev_live hL hj ⟨hu,hlt⟩) x y _ _
      (fun i _ _ => raw i) (fun _ _ => .inl ⟨rfl,rfl⟩)
    intro k hk hpath _
    apply positive_op hC (gate_mem hL hk)
    intro hn
    have := reachIncreases hpath
    have hk' := only k hk hn
    omega
  · intro h
    exact h

private theorem path_negative {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (hC : FanInTwo C) {j r i : ℕ} (hj : j ∈ L)
    (hr : r ∈ L) (notLe : j ≤ r)
    (hnot : (gateAt C j).op = .not)
    (only : ∀ k ∈ L, (gateAt C k).op = .not → k = j)
    (single : ∀ a b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    (hiPath : reaches N C L i (N+j))
    (x y : ℕ → Bool) (raw : ∀ u, x u = true → y u = true)
    (off : ∀ u < N, u ≠ i → x u = y u) :
    value N C y (fun _ => none) (N+r) = true →
      value N C x (fun _ => none) (N+r) = true := by
  let f := N+j
  let w := N+r
  let vx := value N C x (fun _ => none) f
  let vy := value N C y (fun _ => none) f
  have hw : live N L w := .inr ⟨r,hr,rfl⟩
  have dir : vy = true → vx = true := negated_wire_order hL hC hj hnot only x y raw
  have hOut : w = f ∨ ¬ reaches N C L w f := by
    by_cases eq : w=f
    · exact .inl eq
    · exact .inr fun h => by dsimp [w,f] at *; have := reachIncreases h; omega
  have cEq : value N C x (relay f vy) w = value N C y (relay f vy) w := by
    apply cut_agree hL f (fun a _ b c => single a b c) vy x y _ w hw hOut
    intro u hu hAway
    exact off u hu (fun e => hAway (e ▸ hiPath))
  have hMono : value N C x (relay f vy) w = true → value N C x (relay f vx) w = true := by
    apply value_mono hL w hw x x _ _ (fun _ _ _ h => h)
    · intro u _
      by_cases e : u=f
      · exact .inr ⟨vy,vx,by simp [relay,e],by simp [relay,e],dir⟩
      · exact .inl ⟨by simp [relay,e],by simp [relay,e]⟩
    · intro k hk _ h
      apply positive_op hC (gate_mem hL hk)
      intro hn
      have eq := only k hk hn
      subst k
      simp [relay,f] at h
  intro h
  change value N C y (fun _ => none) w = true at h
  change value N C x (fun _ => none) w = true
  rw [replace_signal hL x f w hw]
  exact hMono (cEq.trans (replace_signal hL y f w hw).symm ▸ h)


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Network

private def rawAssignment (x : Fin 6 → Bool) : ℕ → Bool :=
  fun i => (List.ofFn x).getD i false

private theorem raw_assignment_in (x : Fin 6 → Bool) {i : ℕ} (hi : i < 6) :
    rawAssignment x i = x ⟨i,hi⟩ := by
  unfold rawAssignment
  rw [List.getD_eq_getElem _ _ (by simpa)]
  exact List.getElem_ofFn _

private theorem raw_assignment_out (x : Fin 6 → Bool) {i : ℕ} (hi : 6 ≤ i) :
    rawAssignment x i = false :=
  List.getD_eq_default _ _ (by simpa using hi)

private theorem raw_assignment_mono {x y : Fin 6 → Bool} (h : x ≤ y) :
    ∀ i, rawAssignment x i = true → rawAssignment y i = true := by
  intro i ht
  by_cases hi : i < 6
  · rw [raw_assignment_in x hi] at ht
    rw [raw_assignment_in y hi]
    have nxt := h ⟨i,hi⟩
    rw [ht] at nxt
    cases yy : y ⟨i,hi⟩ with
    | true => rfl
    | false => exact ((by decide : ¬ true ≤ false) (yy ▸ nxt)).elim
  · rw [raw_assignment_out x (by omega)] at ht
    contradiction

private theorem raw_assignment_update (x : Fin 6 → Bool) (i : Fin 6) (w : ℕ)
    (h : w ≠ i.val) : rawAssignment x w = rawAssignment (Function.update x i true) w := by
  by_cases hw : w < 6
  · rw [raw_assignment_in x hw, raw_assignment_in _ hw, Function.update_of_ne]
    intro e
    exact h (congrArg Fin.val e)
  · rw [raw_assignment_out x (by omega), raw_assignment_out _ (by omega)]

private theorem pointwise_update_mono (x : Fin 6 → Bool) (i : Fin 6) :
    x ≤ Function.update x i true := by
  intro j
  by_cases h : j = i
  · subst j
    simp
  · rw [Function.update_of_ne h]

theorem partial_monotone (C : Circuit) (hfan : FanInTwo C) (hsmall : C.size ≤ 6)
    (hout : C.output = 11) (hpos : ∀ i : Fin 6,
      ∃ x : Fin 6 → Bool, x i = false ∧ C.eval (List.ofFn x) = false ∧
        C.eval (List.ofFn (Function.update x i true)) = true) :
    Monotone (fun x : Fin 6 → Bool => C.eval (List.ofFn x)) := by
  classical
  let D := trim C
  have hD : FanInTwo D := trim_fan C hfan
  have unary := trim_unary C
  have hDs : D.size ≤ 6 := by simpa [D, trim, Circuit.size] using hsmall
  have ho : D.output = 6+5 := hout
  have hpositive (i : Fin 6) : ∃ x : Fin 6 → Bool,
      D.eval (List.ofFn x) = false ∧ D.eval (List.ofFn (Function.update x i true)) = true := by
    obtain ⟨x,_,hx,hy⟩ := hpos i
    exact ⟨x,by simpa only [D,trim_eval] using hx,by simpa only [D,trim_eval] using hy⟩
  obtain ⟨x,_,hy⟩ := hpositive 0
  have hroot : 5 < D.gates.length := by
    by_contra! hn
    change ((D.gates.foldl step (List.ofFn (Function.update x 0 true))).getD D.output false) = true at hy
    rw [List.getD_eq_default _ _ (by rw [ho,len,List.length_ofFn]; omega)] at hy
    contradiction
  obtain ⟨L,hr,hL,hnext⟩ := minimal_closed 6 D 5 hroot
  have hrootLive : live 6 L (6+5) := .inr ⟨5,hr,rfl⟩
  have hrawUsed (i : Fin 6) : i.val ∈ used 6 D L := by
    by_contra hmiss
    obtain ⟨x,hx,hy⟩ := hpositive i
    have he := closed_eval_eq hL hr ho (List.ofFn x) (List.ofFn (Function.update x i true))
      List.length_ofFn List.length_ofFn (fun w hw => raw_assignment_update x i w (fun eq => hmiss (eq ▸ hw)))
    rw [hx,hy] at he
    contradiction
  have hraw : rawUsed 6 D L = Finset.range 6 := by
    ext w
    simp only [rawUsed, Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right,fun h => ⟨hrawUsed ⟨w,h⟩,h⟩⟩
  have hp : ∀ j ∈ L, (gateAt D j).op ≠ .not := by
    intro j hj hjNot
    have hlow := slots_count_low hr hnext
    rw [hraw,Finset.card_range] at hlow
    have hhigh := slots_count_high hL hD unary
    have hmid := Finset.card_image_le (s := slots 6 D L) (f := Prod.snd)
    change (used 6 D L).card ≤ (slots 6 D L).card at hmid
    have hjmem : j ∈ activeNot D L := Finset.mem_filter.mpr ⟨hj,hjNot⟩
    have hnotpos := Finset.card_pos.mpr ⟨j,hjmem⟩
    have hLc : L.card ≤ 6 := (Finset.card_le_card
      (show L ⊆ Finset.range D.size from fun i hi => Finset.mem_range.mpr (hL.1 i hi))).trans (by simpa)
    have hL6 : L.card = 6 := by omega
    have hN1 : (activeNot D L).card = 1 := by omega
    have hCounts : (used 6 D L).card = (slots 6 D L).card := by omega
    have hInj : Set.InjOn Prod.snd (slots 6 D L : Set (ℕ×ℕ)) :=
      Finset.injOn_of_card_image_eq hCounts
    have only (k : ℕ) (hk : k ∈ L) (hn : (gateAt D k).op = .not) : k = j :=
      (Finset.card_le_one.mp hN1.le) k (Finset.mem_filter.mpr ⟨hk,hn⟩) j hjmem
    have single (a b c : ℕ) (e1 : edgeTo 6 D L a b) (e2 : edgeTo 6 D L a c) : b = c := by
      rcases e1 with ⟨i,hi,rfl,e⟩
      rcases e2 with ⟨k,hk,rfl,f⟩
      rw [unique_reader_of_inj hInj hi hk e f]
    have noEmpty (k : ℕ) (hk : k ∈ L) : ∃ w, before D 6 k w := by
      by_contra h
      have hstrict := budget_strict hL hD unary hk h
      omega
    obtain ⟨i,hi,hpath⟩ := raw_ancestor hL noEmpty (.inr ⟨j,hj,rfl⟩)
    have hJle : j ≤ 5 := by
      have := reachIncreases (every_gate_reaches_root hL hnext j hj)
      omega
    let k : Fin 6 := ⟨i,hi⟩
    obtain ⟨x,hx,hy⟩ := hpositive k
    have hvx : value 6 D (rawAssignment x) (fun _ => none) (6+5) = false := by
      unfold rawAssignment
      rw [← ho, val_original 6 D (List.ofFn x) List.length_ofFn]
      exact hx
    have hvy : value 6 D (rawAssignment (Function.update x k true)) (fun _ => none) (6+5) = true := by
      unfold rawAssignment
      rw [← ho,val_original 6 D (List.ofFn (Function.update x k true)) List.length_ofFn]
      exact hy
    have anti := path_negative hL hD hj hr hJle hjNot only single hpath
      (rawAssignment x) (rawAssignment (Function.update x k true))
      (raw_assignment_mono (pointwise_update_mono x k)) (fun w _ hw => raw_assignment_update x k w hw)
      hvy
    rw [hvx] at anti
    contradiction
  intro x y hxy
  have mono := value_mono hL _ hrootLive (rawAssignment x) (rawAssignment y)
    (fun _ => none) (fun _ => none) (fun i _ _ => raw_assignment_mono hxy i)
    (fun _ _ => .inl ⟨rfl,rfl⟩)
    (fun j hj _ _ => positive_op hD (gate_mem hL hj) (hp j hj))
  unfold rawAssignment at mono
  rw [← ho,val_original 6 D (List.ofFn x) List.length_ofFn,
    val_original 6 D (List.ofFn y) List.length_ofFn] at mono
  simp only [D,trim_eval] at mono
  show C.eval (List.ofFn x) ≤ C.eval (List.ofFn y)
  cases hx : C.eval (List.ofFn x) <;> cases hy : C.eval (List.ofFn y) <;> simp_all

end Monotonicity

end PEqualNP.Outside.L_meta_29922

open PEqualNP.Outside.L_meta_29922 in
theorem PEqualNP.Outside.L_meta_29922 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 12 ∈ (C.gates.get i).inputs ∧ 12 ≠ 0 ∧ 12 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 12 false = true)) := by
  rintro ⟨C, i, k, hi, hfan, hsize, heval, hi0, huniq, hio, hka, hik, hkin,
    hi12, _, _, _⟩
  obtain ⟨E, ef, es, eo, en, ee⟩ := cut_from_cycle C i k hi hik hfan hsize
    heval hi0 hi12 huniq hio hka hkin
  let D := shiftCircuit E
  have df : PEqualNP.MetaComplexity.FanInTwo D := shift_fanin E ef
  have ds : D.size ≤ 6 := by simp [D, es]
  have do' : D.output = 11 := by simp [D, eo]
  have fit : ∀ x : Fin 6 → Bool, rootOn x = true → D.eval (List.ofFn x) = edgePath x := by
    intro x hx
    dsimp only [D]
    rw [shift_eval E _ en (by omega)]
    exact ee x hx
  have a := envelope_agreement D fit
  have pos := positive_toggle (fun x => D.eval (List.ofFn x)) a
  exact complete_after_mono D df ds a (Monotonicity.partial_monotone D df ds do' pos)
