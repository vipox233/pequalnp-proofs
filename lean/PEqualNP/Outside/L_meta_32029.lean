import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32029
open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def val (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (run gs x).getD w false

def Good (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

def Cmp (ι κ : Type) (S : ℕ) (F : (ι → Bool) → κ → Bool) : Prop :=
  ∀ (n : ℕ) (gs : List Gate), Good n gs → 0 < n + gs.length →
    ∀ ws : ι → ℕ, (∀ j, ws j < n + gs.length) →
    ∃ (more : List Gate) (outs : κ → ℕ), Good n (gs ++ more) ∧ more.length ≤ S ∧
      (∀ k, outs k < n + gs.length + more.length) ∧
      ∀ x : List Bool, x.length = n → ∀ k,
        val (gs ++ more) x (outs k) = F (fun j => val gs x (ws j)) k

def Cb (ι : Type) (S : ℕ) (φ : (ι → Bool) → Bool) : Prop := Cmp ι Unit S (fun v _ => φ v)

abbrev V (d : ℕ) := Fin d → ZMod 2

def mat {r c : ℕ} (v : Fin r × Fin c → Bool) : Matrix (Fin r) (Fin c) (ZMod 2) :=
  fun i j => if v (i, j) then 1 else 0

def tmat {D : ℕ} (t s : Fin D) (c : Bool) : Matrix (Fin D) (Fin D) (ZMod 2) :=
  Matrix.transvection t s (if c then 1 else 0)

def rowAdd {D : ℕ} (t s : Fin D) (c : Bool) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  fun p => if p.1 = t then xor (M p) (c && M (s, p.2)) else M p

def gjCtl {D : ℕ} (e : Bool × Fin D × Fin D) (M : Fin D × Fin D → Bool) : Bool :=
  if e.1 then M (e.2.2, e.2.1) && M (e.2.1, e.2.1)
  else (decide (e.2.1 < e.2.2) || !M (e.2.2, e.2.2)) && M (e.2.2, e.2.1) && !M (e.2.1, e.2.1)

def gjT {D : ℕ} (e : Bool × Fin D × Fin D) : Fin D := if e.1 then e.2.2 else e.2.1
def gjS {D : ℕ} (e : Bool × Fin D × Fin D) : Fin D := if e.1 then e.2.1 else e.2.2

def gjStep {D : ℕ} (e : Bool × Fin D × Fin D) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  rowAdd (gjT e) (gjS e) (gjCtl e M) M

def sched (D : ℕ) : List (Bool × Fin D × Fin D) :=
  (List.finRange D).flatMap fun p =>
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (false, p, i)) ++
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (true, p, i))

def gj (D : ℕ) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  (sched D).foldl (fun M e => gjStep e M) M

def cl (m : ℕ) {N : ℕ} (p : Fin N) : Fin (m + N + 1) := ⟨p.val, by omega⟩
def rc (m N : ℕ) : Fin (m + N + 1) := ⟨N, by omega⟩

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

def toZ {ι : Type} (f : ι → Bool) : ι → ZMod 2 := fun i => b2z (f i)

def bx {ι : Type} [Fintype ι] (f : ι → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => f i = true)).card % 2 = 1)

abbrev T (k m : ℕ) : Type := Fin k ⊕ (Fin m ⊕ (Fin k ⊕ Fin k))

def mk {k m : ℕ} {α : Type} (d : Fin k → α) (y : Fin m → α) (a b : Fin k → α) : T k m → α :=
  Sum.elim d (Sum.elim y (Sum.elim a b))

def pd {k m : ℕ} {α : Type} (v : T k m → α) : Fin k → α := fun i => v (Sum.inl i)
def py {k m : ℕ} {α : Type} (v : T k m → α) : Fin m → α := fun j => v (Sum.inr (Sum.inl j))
def pr {k m : ℕ} {α : Type} (v : T k m → α) : Fin k → α :=
  fun i => v (Sum.inr (Sum.inr (Sum.inl i)))
def pc {k m : ℕ} {α : Type} (v : T k m → α) : Fin k → α :=
  fun i => v (Sum.inr (Sum.inr (Sum.inr i)))

def ix {k : ℕ} (i : Fin k) (s : ℕ) : Fin k := ⟨(i.val + s) % k, Nat.mod_lt _ i.pos⟩

def rotZ {k : ℕ} (s : ℕ) (x : V k) : V k := fun i => x (ix i (k - s % k))
def mixZ {k : ℕ} (g : ℕ) (x : V k) : V k := fun i => x i + rotZ g x i + rotZ (k - g) x i
def chiZ {k : ℕ} (y : V k) : V k := fun i => y i + (1 + y (ix i 1)) * y (ix i 2)
def FZ {k : ℕ} (g : ℕ) (x : V k) : V k := chiZ (mixZ g x)
def PZ {k : ℕ} (g : ℕ) (e x : V k) : V k := fun i =>
  mixZ g x (ix i 1) * mixZ g e (ix i 2) + mixZ g e (ix i 1) * mixZ g x (ix i 2)

def rotB {k : ℕ} (s : ℕ) (x : Fin k → Bool) : Fin k → Bool := fun i => x (ix i (k - s % k))
def mixB {k : ℕ} (g : ℕ) (x : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (xor (x i) (rotB g x i)) (rotB (k - g) x i)
def chiB {k : ℕ} (y : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (y i) (!(y (ix i 1)) && y (ix i 2))
def FB {k : ℕ} (g : ℕ) (x : Fin k → Bool) : Fin k → Bool := chiB (mixB g x)
def PB {k : ℕ} (g : ℕ) (e x : Fin k → Bool) : Fin k → Bool := fun i =>
  xor (mixB g x (ix i 1) && mixB g e (ix i 2)) (mixB g e (ix i 1) && mixB g x (ix i 2))

def updZ {k m : ℕ} (t : ℕ) (x x' : V k) (v : T k m → ZMod 2) : T k m → ZMod 2 :=
  mk (pd v) (py v)
    (fun i => FZ 1 (x + pr v) i + FZ 1 x i + rotZ (2 * t) (pd v) i)
    (fun i => FZ 2 (x' + pc v) i + FZ 2 x' i + rotZ (3 * (t + 1) + 1) (pd v) i)

def ZB {k m : ℕ} (t : ℕ) (v : T k m → Bool) : T k m → Bool :=
  mk (pd v) (py v)
    (fun i => xor (FB 1 (pr v) i) (rotB (2 * t) (pd v) i))
    (fun i => xor (FB 2 (pc v) i) (rotB (3 * (t + 1) + 1) (pd v) i))

def termOk {k m : ℕ} (A B : Fin m × Fin k → Bool) (v : T k m → ZMod 2) : Prop :=
  ∀ j : Fin m, ∑ i, b2z (A (j, i)) * pr v i + ∑ i, b2z (B (j, i)) * pc v i + py v j = 0

def OkRem {k m : ℕ} (A B : Fin m × Fin k → Bool) : ℕ → ℕ → (T k m → ZMod 2) → Prop
  | 0, _, v => termOk A B v
  | s + 1, t, v => ∀ x x' : V k, OkRem A B s (t + 1) (updZ t x x' v)

def kerB {ι κ : Type} [Fintype κ] (C : ι × κ → Bool) (v : κ → ZMod 2) : Prop :=
  ∀ a, ∑ j, b2z (C (a, j)) * v j = 0

def termB {k m : ℕ} (A B : Fin m × Fin k → Bool) : T k m × T k m → Bool := fun p =>
  Sum.elim (fun _ => false)
    (Sum.elim
      (fun j => mk (fun _ => false) (fun j' => decide (j' = j)) (fun i => A (j, i))
        (fun i => B (j, i)) p.2)
      (fun _ => false)) p.1

noncomputable def rref {ι : Type} [Fintype ι] (M : ι × ι → Bool) : ι × ι → Bool := fun p =>
  gj (Fintype.card ι)
    (fun q => M ((Fintype.equivFin ι).symm q.1, (Fintype.equivFin ι).symm q.2))
    (Fintype.equivFin ι p.1, Fintype.equivFin ι p.2)

def stack {ι : Type} (R B : ι × ι → Bool) : (ι ⊕ ι) × (ι ⊕ ι) → Bool := fun p =>
  Sum.elim (fun j => Sum.elim (fun i => R (i, j)) (fun i => B (i, j)) p.1) (fun _ => false) p.2

noncomputable def absorb {ι : Type} [Fintype ι] (R B : ι × ι → Bool) : ι × ι → Bool := fun p =>
  rref (stack R B) (Sum.inl p.1, Sum.inl p.2)

def unitB {ι : Type} [DecidableEq ι] (c : ι) : ι → Bool := fun j => decide (j = c)

def polB {k m : ℕ} (C : T k m × T k m → Bool) (a : T k m) : T k m × T k m → Bool := fun p =>
  mk (fun _ => false) (fun _ => false)
    (fun i => mk (fun _ => false) (fun _ => false)
      (fun c => bx (fun j => C (a, Sum.inr (Sum.inr (Sum.inl j))) && PB 1 (unitB c) (unitB i) j))
      (fun _ => false) p.2)
    (fun i => mk (fun _ => false) (fun _ => false) (fun _ => false)
      (fun c => bx (fun j => C (a, Sum.inr (Sum.inr (Sum.inr j))) && PB 2 (unitB c) (unitB i) j))
      p.2) p.1

noncomputable def polR {k m : ℕ} (C : T k m × T k m → Bool) : T k m × T k m → Bool :=
  (Finset.univ : Finset (T k m)).toList.foldl (fun R a => absorb R (polB C a)) (fun _ => false)

def bvec {ι : Type} [DecidableEq ι] (R : ι × ι → Bool) (c : ι) : ι → Bool :=
  fun j => !R (c, c) && xor (decide (j = c)) (R (j, c))

def qB {k m : ℕ} (t : ℕ) (C R : T k m × T k m → Bool) : T k m × T k m → Bool := fun p =>
  bx (fun j => C (p.1, j) && ZB t (bvec R p.2) j)

noncomputable def tick {k m : ℕ} (t : ℕ) (C : T k m × T k m → Bool) : T k m × T k m → Bool :=
  absorb (polR C) (qB t C (polR C))

noncomputable def backC {k m : ℕ} (r : ℕ) (A B : Fin m × Fin k → Bool) : T k m × T k m → Bool :=
  (List.range r).foldr (fun t C => tick t C) (termB A B)

def v0B {k m : ℕ} (d : Fin k → Bool) (y : Fin m → Bool) : T k m → Bool :=
  mk d y (rotB 1 d) (rotB 3 d)

def finH {k m : ℕ} (C0 : T k m × T k m → Bool) (pin : Fin k → Bool) :
    (T k m ⊕ Fin k) × Fin k → Bool := fun p =>
  Sum.elim (fun a => bx (fun j => C0 (a, j) && v0B (unitB p.2) (fun _ => false) j))
    (fun i => pin i && decide (i = p.2)) p.1

def finR {k m : ℕ} (C0 : T k m × T k m → Bool) (y : Fin m → Bool) (pin value : Fin k → Bool) :
    T k m ⊕ Fin k → Bool :=
  Sum.elim (fun a => bx (fun j : Fin m => C0 (a, Sum.inr (Sum.inl j)) && y j))
    (fun i => pin i && value i)

def sysB {M N : ℕ} (H : Fin M × Fin N → Bool) (rhs : Fin M → Bool) :
    Fin (M + N + 1) × Fin (M + N + 1) → Bool := fun p =>
  if hi : p.1.val < M then
    (if hj : p.2.val < N then H (⟨p.1.val, hi⟩, ⟨p.2.val, hj⟩)
     else if p.2.val = N then rhs ⟨p.1.val, hi⟩ else false)
  else false

abbrev rowsN (k m : ℕ) : ℕ := Fintype.card (T k m ⊕ Fin k)

noncomputable def finSys {k m : ℕ} (C0 : T k m × T k m → Bool) (y : Fin m → Bool)
    (pin value : Fin k → Bool) :
    Fin (rowsN k m + k + 1) × Fin (rowsN k m + k + 1) → Bool :=
  sysB (fun p => finH C0 pin ((Fintype.equivFin (T k m ⊕ Fin k)).symm p.1, p.2))
    (fun i => finR C0 y pin value ((Fintype.equivFin (T k m ⊕ Fin k)).symm i))

def natOf {n : ℕ} (tb : Fin n → Bool) : ℕ := ∑ i : Fin n, if tb i then 2 ^ i.val else 0

def cmpB {k : ℕ} (tb : Fin (k + 1) → Bool) (fr : Fin k → Bool) (cons : Bool) : Bool :=
  decide (natOf tb ≤ if cons then 2 ^ (Finset.univ.filter (fun p => fr p = true)).card else 0)

abbrev In0 (k m : ℕ) : Type :=
  (Fin m × Fin k) ⊕ ((Fin m × Fin k) ⊕ (Fin m ⊕ (Fin k ⊕ (Fin k ⊕ Fin (k + 1)))))

noncomputable def finG {k m : ℕ} (r : ℕ) (v : In0 k m → Bool) :
    Fin (rowsN k m + k + 1) × Fin (rowsN k m + k + 1) → Bool :=
  gj _ (finSys (backC r (fun p => v (Sum.inl p)) (fun p => v (Sum.inr (Sum.inl p))))
    (fun j => v (Sum.inr (Sum.inr (Sum.inl j))))
    (fun i => v (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
    (fun i => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))))

noncomputable def top {k m : ℕ} (r : ℕ) (v : In0 k m → Bool) : Bool :=
  cmpB (fun i => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))))
    (fun p => !(finG r v (cl _ p, cl _ p)))
    (!(finG r v (rc _ k, rc _ k)))

def inpOf {k m : ℕ} (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (pin value : Fin (2 ^ k))
    (t : Fin (2 ^ (k + 1))) : In0 k m → Bool :=
  Sum.elim (fun p => (A p.1).val.testBit p.2.val)
    (Sum.elim (fun p => (B p.1).val.testBit p.2.val)
      (Sum.elim y
        (Sum.elim (fun i => pin.val.testBit i.val)
          (Sum.elim (fun i => value.val.testBit i.val) (fun i => t.val.testBit i.val)))))

theorem fa_run_append (gs more : List Gate) (x : List Bool) :
    run (gs ++ more) x = run more (run gs x) := by
  simp [run, List.foldl_append]

theorem fa_run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    have : run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl
    rw [this, ih]
    simp
    omega

theorem fa_run_getD (more : List Gate) (l : List Bool) (w : ℕ) (hw : w < l.length) :
    (run more l).getD w false = l.getD w false := by
  induction more generalizing l with
  | nil => simp [run]
  | cons g more ih =>
    have : run (g :: more) l =
        run more (l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) := rfl
    rw [this, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

theorem fa_val_append (n : ℕ) (gs more : List Gate) (x : List Bool) (w : ℕ)
    (hx : x.length = n) (hw : w < n + gs.length) :
    val (gs ++ more) x w = val gs x w := by
  unfold val
  rw [fa_run_append]
  exact fa_run_getD _ _ _ (by rw [fa_run_length]; omega)

theorem fa_good_snoc (n : ℕ) (gs : List Gate) (g : Gate) (hg : Good n gs)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hin : ∀ i ∈ g.inputs, i < n + gs.length) :
    Good n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hg.1 g' h
    · rw [List.mem_singleton.1 h]; exact ⟨hop, hl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [this] at hi
      exact hg.2 j hlt i hi
    · have hj' : j = gs.length := by omega
      subst hj'
      have : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [this] at hi
      exact hin i hi

theorem fa_val_snoc (n : ℕ) (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = n) :
    val (gs ++ [g]) x (n + gs.length) = g.op.eval (g.inputs.map fun i => val gs x i) := by
  unfold val
  rw [fa_run_append]
  have h1 : run [g] (run gs x) =
      run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := rfl
  rw [h1]
  have h2 : n + gs.length = (run gs x).length := by rw [fa_run_length]; omega
  rw [h2]
  simp [List.getD_eq_getElem?_getD]

theorem fa_gate {ι : Type} (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (js : List ι)
    (hl : js.length ≤ 2) : Cmp ι Unit 1 (fun v _ => op.eval (js.map v)) := by
  intro n gs hg hpos ws hws
  refine ⟨[⟨op, js.map ws⟩], fun _ => n + gs.length, ?_, by simp, ?_, ?_⟩
  · refine fa_good_snoc n gs _ hg hop (by simpa using hl) ?_
    intro i hi
    simp only [List.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact hws j
  · intro _; simp
  · intro x hx _
    rw [fa_val_snoc n gs _ x hx]
    simp [List.map_map, Function.comp_def]

theorem Cmp.mono {ι κ : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    (h : Cmp ι κ S F) (hS : S ≤ S') : Cmp ι κ S' F := by
  intro n gs hg hpos ws hws
  obtain ⟨more, outs, h1, h2, h3, h4⟩ := h n gs hg hpos ws hws
  exact ⟨more, outs, h1, le_trans h2 hS, h3, h4⟩

theorem Cmp.congr {ι κ : Type} {S : ℕ} {F F' : (ι → Bool) → κ → Bool}
    (h : Cmp ι κ S F) (hF : ∀ v k, F v k = F' v k) : Cmp ι κ S F' := by
  have : F = F' := by funext v k; exact hF v k
  exact this ▸ h

theorem Cmp.wire {ι κ : Type} (σ : κ → ι) : Cmp ι κ 0 (fun v k => v (σ k)) := by
  intro n gs hg hpos ws hws
  refine ⟨[], fun k => ws (σ k), by simpa using hg, by simp, ?_, ?_⟩
  · intro k; simpa using hws (σ k)
  · intro x hx k; simp

theorem Cmp.comp {ι κ μ : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    {G : (κ → Bool) → μ → Bool} (h1 : Cmp ι κ S F) (h2 : Cmp κ μ S' G) :
    Cmp ι μ (S + S') (fun v => G (F v)) := by
  intro n gs hg hpos ws hws
  obtain ⟨m1, o1, g1, l1, b1, v1⟩ := h1 n gs hg hpos ws hws
  obtain ⟨m2, o2, g2, l2, b2, v2⟩ := h2 n (gs ++ m1) g1 (by simp; omega) o1
    (by intro j; simpa [Nat.add_assoc] using b1 j)
  refine ⟨m1 ++ m2, o2, by simpa [List.append_assoc] using g2, by simp; omega, ?_, ?_⟩
  · intro k; have := b2 k; simp at this ⊢; omega
  · intro x hx k
    rw [← List.append_assoc, v2 x hx k]
    congr 1
    funext j
    exact v1 x hx j

theorem Cmp.pair {ι κ κ' : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    {F' : (ι → Bool) → κ' → Bool} (h1 : Cmp ι κ S F) (h2 : Cmp ι κ' S' F') :
    Cmp ι (κ ⊕ κ') (S + S') (fun v => Sum.elim (F v) (F' v)) := by
  intro n gs hg hpos ws hws
  obtain ⟨m1, o1, g1, l1, b1, v1⟩ := h1 n gs hg hpos ws hws
  obtain ⟨m2, o2, g2, l2, b2, v2⟩ := h2 n (gs ++ m1) g1 (by simp; omega) ws
    (by intro j; have := hws j; simp; omega)
  refine ⟨m1 ++ m2, Sum.elim o1 o2, by simpa [List.append_assoc] using g2, by simp; omega, ?_, ?_⟩
  · intro k
    cases k with
    | inl k => have := b1 k; simp; omega
    | inr k => have := b2 k; simp at this ⊢; omega
  · intro x hx k
    cases k with
    | inl k =>
      simp only [Sum.elim_inl]
      rw [← List.append_assoc, fa_val_append n (gs ++ m1) m2 x _ hx (by
        have := b1 k; simp; omega)]
      exact v1 x hx k
    | inr k =>
      simp only [Sum.elim_inr]
      rw [← List.append_assoc, v2 x hx k]
      congr 1
      funext j
      exact fa_val_append n gs m1 x _ hx (hws j)

theorem Cmp.keep {ι κ : Type} {S : ℕ} {F : (ι → Bool) → κ → Bool} (h : Cmp ι κ S F) :
    Cmp ι (ι ⊕ κ) S (fun v => Sum.elim v (F v)) := by
  have := Cmp.pair (Cmp.wire (ι := ι) (fun k : ι => k)) h
  rw [Nat.zero_add] at this
  exact this

theorem Cmp.sel {ι ι' κ : Type} {S : ℕ} {F : (ι' → Bool) → κ → Bool} (σ : ι' → ι)
    (h : Cmp ι' κ S F) : Cmp ι κ S (fun v => F (fun j => v (σ j))) := by
  intro n gs hg hpos ws hws
  exact h n gs hg hpos (fun j => ws (σ j)) (fun j => hws (σ j))

theorem fa_pi_list {ι κ I : Type} {S : I → ℕ} {F : I → (ι → Bool) → κ → Bool}
    (h : ∀ i, Cmp ι κ (S i) (F i)) (L : List I) :
    ∀ (n : ℕ) (gs : List Gate), Good n gs → 0 < n + gs.length →
    ∀ ws : ι → ℕ, (∀ j, ws j < n + gs.length) →
    ∃ (more : List Gate) (outs : I × κ → ℕ), Good n (gs ++ more) ∧
      more.length ≤ (L.map S).sum ∧
      (∀ k, outs k < n + gs.length + more.length) ∧
      ∀ x : List Bool, x.length = n → ∀ p : I × κ, p.1 ∈ L →
        val (gs ++ more) x (outs p) = F p.1 (fun j => val gs x (ws j)) p.2 := by
  classical
  induction L with
  | nil =>
    intro n gs hg hpos ws hws
    refine ⟨[], fun _ => 0, by simpa using hg, by simp, ?_, ?_⟩
    · intro _; simpa using hpos
    · intro x hx p hp; simp at hp
  | cons i L ih =>
    intro n gs hg hpos ws hws
    obtain ⟨m1, o1, g1, l1, b1, v1⟩ := ih n gs hg hpos ws hws
    obtain ⟨m2, o2, g2, l2, b2, v2⟩ := h i n (gs ++ m1) g1 (by simp; omega) ws
      (by intro j; have := hws j; simp; omega)
    refine ⟨m1 ++ m2, fun p => if p.1 = i then o2 p.2 else o1 p,
      by simpa [List.append_assoc] using g2, by simp; omega, ?_, ?_⟩
    · intro k
      by_cases hk : k.1 = i
      · have := b2 k.2; simp [hk] at this ⊢; omega
      · have := b1 k; simp [hk]; omega
    · intro x hx p hp
      by_cases hk : p.1 = i
      · simp only [hk, ite_true]
        rw [← List.append_assoc, v2 x hx p.2]
        congr 1
        funext j
        exact fa_val_append n gs m1 x _ hx (hws j)
      · simp only [hk, ite_false]
        have hp' : p.1 ∈ L := by
          rcases List.mem_cons.1 hp with h' | h'
          · exact absurd h' hk
          · exact h'
        rw [← List.append_assoc, fa_val_append n (gs ++ m1) m2 x _ hx (by
          have := b1 p; simp; omega)]
        exact v1 x hx p hp'

theorem Cmp.pi {ι κ I : Type} [Fintype I] {S : I → ℕ} {F : I → (ι → Bool) → κ → Bool}
    (h : ∀ i, Cmp ι κ (S i) (F i)) : Cmp ι (I × κ) (∑ i, S i) (fun v p => F p.1 v p.2) := by
  intro n gs hg hpos ws hws
  obtain ⟨more, outs, g1, l1, b1, v1⟩ :=
    fa_pi_list h (Finset.univ : Finset I).toList n gs hg hpos ws hws
  rw [Finset.sum_map_toList] at l1
  exact ⟨more, outs, g1, l1, b1, fun x hx p => v1 x hx p (by simp)⟩

theorem Cmp.piU {ι κ I : Type} [Fintype I] {s : ℕ} {F : I → (ι → Bool) → κ → Bool}
    (h : ∀ i, Cmp ι κ s (F i)) : Cmp ι (I × κ) (Fintype.card I * s) (fun v p => F p.1 v p.2) := by
  have := Cmp.pi h
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  exact this

theorem Cmp.foldl {ι α : Type} {s : ℕ} (L : List α) (F : α → (ι → Bool) → ι → Bool)
    (h : ∀ e ∈ L, Cmp ι ι s (F e)) :
    Cmp ι ι (L.length * s) (fun v => L.foldl (fun acc e => F e acc) v) := by
  induction L with
  | nil =>
    have := Cmp.wire (ι := ι) (fun k : ι => k)
    simpa using this
  | cons e L ih =>
    have h1 := h e (by simp)
    have h2 := ih (fun e' he' => h e' (by simp [he']))
    have := Cmp.comp h1 h2
    refine Cmp.mono this ?_
    simp [Nat.succ_mul]
    omega

theorem Cmp.chain {ι σ : Type} (n s : ℕ) (c : ℕ → (ι → Bool) → σ → Bool)
    (G : ℕ → (ι ⊕ σ → Bool) → σ → Bool)
    (h0 : Cmp ι σ s (c 0))
    (hG : ∀ i < n, Cmp (ι ⊕ σ) σ s (G i))
    (hc : ∀ i < n, ∀ v, c (i + 1) v = G i (Sum.elim v (c i v))) :
    Cmp ι (Fin (n + 1) × σ) ((n + 1) * s) (fun v p => c p.1.val v p.2) := by
  induction n with
  | zero =>
    have := Cmp.comp h0 (Cmp.wire (fun p : Fin 1 × σ => p.2))
    refine Cmp.congr (Cmp.mono this (by omega)) ?_
    intro v p
    have : p.1.val = 0 := by omega
    rw [this]
  | succ n ih =>
    have A := ih (fun i hi => hG i (by omega)) (fun i hi => hc i (by omega))
    have B := Cmp.sel (ι := ι ⊕ (Fin (n + 1) × σ))
      (fun j : ι ⊕ σ => Sum.map (fun k : ι => k) (fun k : σ => (Fin.last n, k)) j)
      (hG n (by omega))
    have C := Cmp.comp (Cmp.comp A.keep B.keep)
      (Cmp.wire (fun p : Fin (n + 2) × σ =>
        if hp : p.1.val < n + 1 then
          (Sum.inl (Sum.inr (⟨p.1.val, hp⟩, p.2)) : (ι ⊕ (Fin (n + 1) × σ)) ⊕ σ)
        else Sum.inr p.2))
    refine Cmp.congr (Cmp.mono C (by simp [Nat.succ_mul])) ?_
    intro v p
    by_cases hp : p.1.val < n + 1
    · simp [hp]
    · have hp' : p.1.val = n + 1 := by omega
      simp only [hp, ↓reduceDIte, Sum.elim_inr]
      rw [hp', hc n (by omega) v]
      congr 1
      funext j
      cases j with
      | inl j => simp
      | inr j => simp

theorem Cb.mono {ι : Type} {S S' : ℕ} {φ : (ι → Bool) → Bool} (h : Cb ι S φ) (hS : S ≤ S') :
    Cb ι S' φ := Cmp.mono h hS

theorem Cb.congr {ι : Type} {S : ℕ} {φ φ' : (ι → Bool) → Bool} (h : Cb ι S φ)
    (hF : ∀ v, φ v = φ' v) : Cb ι S φ' := Cmp.congr h (fun v _ => hF v)

theorem Cb.var {ι : Type} (i : ι) : Cb ι 0 (fun v => v i) := Cmp.wire (fun _ => i)

theorem Cb.const {ι : Type} (b : Bool) : Cb ι 1 (fun _ => b) := by
  cases b with
  | false =>
    have := fa_gate (ι := ι) GateOp.or (by simp) [] (by simp)
    exact Cmp.congr this (fun v k => by simp [GateOp.eval])
  | true =>
    have := fa_gate (ι := ι) GateOp.and (by simp) [] (by simp)
    exact Cmp.congr this (fun v k => by simp [GateOp.eval])

theorem Cb.not {ι : Type} {S : ℕ} {φ : (ι → Bool) → Bool} (h : Cb ι S φ) :
    Cb ι (S + 1) (fun v => !φ v) := by
  have g := fa_gate (ι := Unit) GateOp.not (by simp) [()] (by simp)
  have := Cmp.comp h g
  exact Cmp.congr this (fun v k => by simp [GateOp.eval])

theorem Cb.and {ι : Type} {S S' : ℕ} {φ ψ : (ι → Bool) → Bool} (h : Cb ι S φ) (h' : Cb ι S' ψ) :
    Cb ι (S + S' + 1) (fun v => φ v && ψ v) := by
  have g := fa_gate (ι := Unit ⊕ Unit) GateOp.and (by simp) [Sum.inl (), Sum.inr ()] (by simp)
  have := Cmp.comp (Cmp.pair h h') g
  exact Cmp.congr this (fun v k => by simp [GateOp.eval])

theorem Cb.or {ι : Type} {S S' : ℕ} {φ ψ : (ι → Bool) → Bool} (h : Cb ι S φ) (h' : Cb ι S' ψ) :
    Cb ι (S + S' + 1) (fun v => φ v || ψ v) := by
  have g := fa_gate (ι := Unit ⊕ Unit) GateOp.or (by simp) [Sum.inl (), Sum.inr ()] (by simp)
  have := Cmp.comp (Cmp.pair h h') g
  exact Cmp.congr this (fun v k => by simp [GateOp.eval])

theorem Cb.xor {ι : Type} {S S' : ℕ} {φ ψ : (ι → Bool) → Bool} (h : Cb ι S φ) (h' : Cb ι S' ψ) :
    Cb ι (S + S' + 4) (fun v => xor (φ v) (ψ v)) := by
  have l : Cb (Unit ⊕ Unit) 0 (fun v => v (Sum.inl ())) := Cb.var _
  have r : Cb (Unit ⊕ Unit) 0 (fun v => v (Sum.inr ())) := Cb.var _
  have g := Cb.and (Cb.or l r) (Cb.not (Cb.and l r))
  have := Cmp.comp (Cmp.pair h h') g
  refine Cmp.congr (Cmp.mono this (by omega)) ?_
  intro v k
  simp only [Sum.elim_inl, Sum.elim_inr]
  cases φ v <;> cases ψ v <;> rfl

theorem Cb.mux {ι : Type} {S S' S'' : ℕ} {χ φ ψ : (ι → Bool) → Bool} (hc : Cb ι S χ)
    (h : Cb ι S' φ) (h' : Cb ι S'' ψ) :
    Cb ι (S + S' + S'' + 4) (fun v => if χ v then φ v else ψ v) := by
  have c : Cb ((Unit ⊕ Unit) ⊕ Unit) 0 (fun v => v (Sum.inl (Sum.inl ()))) := Cb.var _
  have l : Cb ((Unit ⊕ Unit) ⊕ Unit) 0 (fun v => v (Sum.inl (Sum.inr ()))) := Cb.var _
  have r : Cb ((Unit ⊕ Unit) ⊕ Unit) 0 (fun v => v (Sum.inr ())) := Cb.var _
  have g := Cb.or (Cb.and c l) (Cb.and (Cb.not c) r)
  have := Cmp.comp (Cmp.pair (Cmp.pair hc h) h') g
  refine Cmp.congr (Cmp.mono this (by omega)) ?_
  intro v k
  simp only [Sum.elim_inl, Sum.elim_inr]
  cases χ v <;> cases φ v <;> cases ψ v <;> rfl

theorem Cb.comp {ι κ : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool} {φ : (κ → Bool) → Bool}
    (h : Cmp ι κ S F) (h' : Cb κ S' φ) : Cb ι (S + S') (fun v => φ (F v)) := Cmp.comp h h'

theorem fa_listOr {ι I : Type} {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) (L : List I) :
    Cb ι (L.length * (s + 1) + 1) (fun v => L.any (fun i => φ i v)) := by
  induction L with
  | nil => simpa using Cb.const (ι := ι) false
  | cons i L ih =>
    refine Cb.congr (Cb.mono (Cb.or (h i) ih) ?_) (fun v => by simp)
    simp [Nat.succ_mul]
    omega

theorem fa_listAnd {ι I : Type} {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) (L : List I) :
    Cb ι (L.length * (s + 1) + 1) (fun v => L.all (fun i => φ i v)) := by
  induction L with
  | nil => simpa using Cb.const (ι := ι) true
  | cons i L ih =>
    refine Cb.congr (Cb.mono (Cb.and (h i) ih) ?_) (fun v => by simp)
    simp [Nat.succ_mul]
    omega

theorem fa_listXor {ι I : Type} {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) (L : List I) :
    Cb ι (L.length * (s + 4) + 1)
      (fun v => L.foldr (fun i acc => xor (φ i v) acc) false) := by
  induction L with
  | nil => simpa using Cb.const (ι := ι) false
  | cons i L ih =>
    refine Cb.congr (Cb.mono (Cb.xor (h i) ih) ?_) (fun v => by simp)
    simp [Nat.succ_mul]
    omega

theorem fa_xor_sum {I : Type} (p : I → Bool) (L : List I) :
    L.foldr (fun i acc => xor (p i) acc) false =
      decide ((L.map (fun i => if p i = true then 1 else 0)).sum % 2 = 1) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]
    cases hp : p i
    · simp
    · simp only [ite_true, Bool.true_xor]
      by_cases hq : (L.map (fun i => if p i = true then 1 else 0)).sum % 2 = 1
      · have : (1 + (L.map (fun i => if p i = true then 1 else 0)).sum) % 2 ≠ 1 := by omega
        simp [hq, this]
      · have : (1 + (L.map (fun i => if p i = true then 1 else 0)).sum) % 2 = 1 := by omega
        simp [hq, this]

theorem Cb.bigOr {ι I : Type} [Fintype I] {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (Fintype.card I * (s + 1) + 1) (fun v => decide (∃ i, φ i v = true)) := by
  have := fa_listOr h (Finset.univ : Finset I).toList
  rw [Finset.length_toList, Finset.card_univ] at this
  refine Cb.congr this (fun v => ?_)
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true]

theorem Cb.bigAnd {ι I : Type} [Fintype I] {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (Fintype.card I * (s + 1) + 1) (fun v => decide (∀ i, φ i v = true)) := by
  have := fa_listAnd h (Finset.univ : Finset I).toList
  rw [Finset.length_toList, Finset.card_univ] at this
  refine Cb.congr this (fun v => ?_)
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true]

theorem Cb.bigXor {ι I : Type} [Fintype I] {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (Fintype.card I * (s + 4) + 1)
      (fun v => decide ((Finset.univ.filter (fun i => φ i v = true)).card % 2 = 1)) := by
  have := fa_listXor h (Finset.univ : Finset I).toList
  rw [Finset.length_toList, Finset.card_univ] at this
  refine Cb.congr this (fun v => ?_)
  rw [fa_xor_sum (fun i => φ i v), Finset.sum_map_toList, Finset.card_filter]

theorem Cmp.ofBits {ι κ : Type} [Fintype κ] {s : ℕ} {F : (ι → Bool) → κ → Bool}
    (h : ∀ k, Cb ι s (fun v => F v k)) : Cmp ι κ (Fintype.card κ * s) F := by
  have := Cmp.comp (Cmp.piU (I := κ) (κ := Unit) (F := fun k v _ => F v k) h)
    (Cmp.wire (fun k : κ => (k, ())))
  exact this

theorem Cmp.extract {ι κ : Type} {S : ℕ} {F : (ι → Bool) → κ → Bool} (h : Cmp ι κ S F)
    (n : ℕ) (ws : ι → ℕ) (hws : ∀ j, ws j < n + 1) :
    ∃ (gs : List Gate) (outs : κ → ℕ),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) ∧
      (∀ o : ℕ, PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨gs, o⟩) ∧
      gs.length ≤ S + 1 ∧ (∀ k, outs k < n + gs.length) ∧
      ∀ (o : ℕ) (x : List Bool), x.length = n → ∀ k,
        ((⟨gs, o⟩ : Circuit).wires x).getD (outs k) false =
          F (fun j => (x ++ [false]).getD (ws j) false) k := by
  have g0 : Good n [⟨GateOp.or, []⟩] := by
    have := fa_good_snoc n [] ⟨GateOp.or, []⟩ ⟨by simp, by simp⟩ (by simp) (by simp) (by simp)
    simpa using this
  obtain ⟨more, outs, g1, l1, b1, v1⟩ := h n [⟨GateOp.or, []⟩] g0 (by simp) ws
    (by simpa using hws)
  refine ⟨[(⟨GateOp.or, []⟩ : Gate)] ++ more, outs, g1.1,
    fun o => by intro j hj i hi; exact g1.2 j hj i hi, by simp; omega, ?_, ?_⟩
  · intro k; have := b1 k; simp at this ⊢; omega
  · intro o x hx k
    exact v1 x hx k
theorem fc_rowAdd_false {D : ℕ} (t s : Fin D) (M : Fin D × Fin D → Bool) :
    rowAdd t s false M = M := by
  funext p
  simp [rowAdd]

theorem fc_rowAdd_mat {D : ℕ} (t s : Fin D) (hts : t ≠ s) (c : Bool)
    (M : Fin D × Fin D → Bool) :
    mat M = tmat t s c * mat (rowAdd t s c M) := by
  ext i j
  by_cases hi : i = t
  · subst hi
    rw [tmat, Matrix.transvection_mul_apply_same]
    simp only [mat, rowAdd, if_true, if_neg (Ne.symm hts)]
    cases M (i, j) <;> cases c <;> cases M (s, j) <;> decide
  · rw [tmat, Matrix.transvection_mul_apply_of_ne _ _ _ _ hi]
    simp [mat, rowAdd, hi]

theorem fc_tmat_sq {D : ℕ} (t s : Fin D) (hts : t ≠ s) (c : Bool) :
    tmat t s c * tmat t s c = 1 := by
  rw [tmat, Matrix.transvection_mul_transvection_same _ _ hts]
  have : ((if c = true then (1 : ZMod 2) else 0) + (if c = true then (1 : ZMod 2) else 0)) = 0 := by
    cases c <;> decide
  rw [this, Matrix.transvection_zero]

theorem fc_gjTS {D : ℕ} (e : Bool × Fin D × Fin D) (he : e.2.1 ≠ e.2.2) : gjT e ≠ gjS e := by
  unfold gjT gjS
  split
  · exact he.symm
  · exact he

theorem gjStep_mat {D : ℕ} (e : Bool × Fin D × Fin D) (he : e.2.1 ≠ e.2.2)
    (M : Fin D × Fin D → Bool) :
    mat M = tmat (gjT e) (gjS e) (gjCtl e M) * mat (gjStep e M) :=
  fc_rowAdd_mat _ _ (fc_gjTS e he) _ M

theorem sched_ne {D : ℕ} (e : Bool × Fin D × Fin D) (he : e ∈ sched D) : e.2.1 ≠ e.2.2 := by
  unfold sched at he
  rw [List.mem_flatMap] at he
  obtain ⟨p, _, hp⟩ := he
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · rw [List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [List.mem_filter] at hi
    have := hi.2
    simp at this
    exact fun h => this h.symm
  · rw [List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [List.mem_filter] at hi
    have := hi.2
    simp at this
    exact fun h => this h.symm

theorem fc_equiv_list {D : ℕ} (l : List (Bool × Fin D × Fin D))
    (hl : ∀ e ∈ l, e.2.1 ≠ e.2.2) (M : Fin D × Fin D → Bool) :
    ∃ U U' : Matrix (Fin D) (Fin D) (ZMod 2),
      mat (l.foldl (fun M e => gjStep e M) M) = U * mat M ∧
      mat M = U' * mat (l.foldl (fun M e => gjStep e M) M) := by
  induction l generalizing M with
  | nil => exact ⟨1, 1, by simp, by simp⟩
  | cons e l ih =>
    have he := hl e (List.mem_cons_self)
    obtain ⟨U, U', h1, h2⟩ := ih (fun e' h' => hl e' (List.mem_cons_of_mem _ h')) (gjStep e M)
    have hs := gjStep_mat e he M
    have hs' : mat (gjStep e M) = tmat (gjT e) (gjS e) (gjCtl e M) * mat M := by
      rw [hs, ← mul_assoc, fc_tmat_sq _ _ (fc_gjTS e he), one_mul]
    refine ⟨U * tmat (gjT e) (gjS e) (gjCtl e M), tmat (gjT e) (gjS e) (gjCtl e M) * U', ?_, ?_⟩
    · rw [List.foldl_cons, h1, hs', mul_assoc]
    · rw [List.foldl_cons, mul_assoc, ← h2]
      exact hs

theorem gj_equiv {D : ℕ} (M : Fin D × Fin D → Bool) :
    ∃ U U' : Matrix (Fin D) (Fin D) (ZMod 2),
      mat (gj D M) = U * mat M ∧ mat M = U' * mat (gj D M) :=
  fc_equiv_list (sched D) (fun e he => sched_ne e he) M

def fc_Inv {D : ℕ} (k : ℕ) (M : Fin D × Fin D → Bool) : Prop :=
  (∀ q : Fin D, q.val < k → M (q, q) = true → ∀ i, M (i, q) = decide (i = q)) ∧
  (∀ i q : Fin D, q.val < k → (k ≤ i.val ∨ M (i, i) = false) → M (i, q) = false) ∧
  (∀ p q : Fin D, q < p → p.val < k → M (p, p) = true → M (p, q) = false)

theorem fc_Inv_congr {D : ℕ} (k : ℕ) (M M' : Fin D × Fin D → Bool)
    (h : ∀ i q : Fin D, q.val < k → M' (i, q) = M (i, q)) (hI : fc_Inv k M) : fc_Inv k M' := by
  obtain ⟨ha, hb, hc⟩ := hI
  refine ⟨?_, ?_, ?_⟩
  · intro q hq hqq i
    rw [h _ _ hq] at hqq ⊢
    exact ha q hq hqq i
  · intro i q hq hfree
    rw [h _ _ hq]
    apply hb i q hq
    by_cases hi : i.val < k
    · rcases hfree with hf | hf
      · omega
      · right
        rw [← h _ _ hi]
        exact hf
    · left
      omega
  · intro p q hqp hp hpp
    have hq : q.val < k := by
      have : q.val < p.val := hqp
      omega
    rw [h _ _ hq]
    rw [h _ _ hp] at hpp
    exact hc p q hqp hp hpp

theorem fc_A_id {D : ℕ} (p : Fin D) (l : List (Fin D)) (M : Fin D × Fin D → Bool)
    (hp : M (p, p) = true) : l.foldl (fun M i => gjStep (false, p, i) M) M = M := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    have : gjStep (false, p, i) M = M := by
      unfold gjStep
      have hc : gjCtl (false, p, i) M = false := by simp [gjCtl, hp]
      rw [hc, fc_rowAdd_false]
    rw [this]
    exact ih

theorem fc_B_id {D : ℕ} (p : Fin D) (l : List (Fin D)) (M : Fin D × Fin D → Bool)
    (hp : M (p, p) = false) : l.foldl (fun M i => gjStep (true, p, i) M) M = M := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    have : gjStep (true, p, i) M = M := by
      unfold gjStep
      have hc : gjCtl (true, p, i) M = false := by simp [gjCtl, hp]
      rw [hc, fc_rowAdd_false]
    rw [this]
    exact ih

theorem fc_A {D : ℕ} (p : Fin D) (k : ℕ) (hk : p.val = k) (l : List (Fin D))
    (hl : ∀ i ∈ l, i ≠ p) (M : Fin D × Fin D → Bool) (hI : fc_Inv k M) :
    fc_Inv k (l.foldl (fun M i => gjStep (false, p, i) M) M) ∧
    ((l.foldl (fun M i => gjStep (false, p, i) M) M) (p, p) = false →
      l.foldl (fun M i => gjStep (false, p, i) M) M = M ∧
      ∀ i ∈ l, (p < i ∨ M (i, i) = false) → M (i, p) = false) := by
  induction l with
  | nil => exact ⟨hI, fun _ => ⟨rfl, fun i hi => absurd hi (List.not_mem_nil)⟩⟩
  | cons i l ih =>
    have ih' := ih (fun i' h' => hl i' (List.mem_cons_of_mem _ h'))
    have hip : i ≠ p := hl i (List.mem_cons_self)
    rw [List.foldl_cons]
    by_cases hc : gjCtl (false, p, i) M = true
    · have hc' := hc
      simp only [gjCtl, Bool.false_eq_true, if_false, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, Bool.not_eq_true'] at hc'
      obtain ⟨⟨hfree, hip1⟩, hpp⟩ := hc'
      have hrow : ∀ q : Fin D, q.val < k → M (i, q) = false := by
        intro q hq
        apply hI.2.1 i q hq
        rcases hfree with hf | hf
        · left
          have : p.val < i.val := hf
          omega
        · right
          exact hf
      have hM1pp : gjStep (false, p, i) M (p, p) = true := by
        simp [gjStep, gjT, gjS, rowAdd, hc, hip1, hpp]
      rw [fc_A_id p l _ hM1pp]
      refine ⟨?_, ?_⟩
      · apply fc_Inv_congr k M _ _ hI
        intro j q hq
        simp only [gjStep, gjT, gjS, rowAdd, Bool.false_eq_true, if_false, hc]
        split
        · rw [hrow q hq]
          simp
        · rfl
      · intro h
        rw [hM1pp] at h
        exact absurd h (by simp)
    · have hcf : gjCtl (false, p, i) M = false := by simpa using hc
      have hM1 : gjStep (false, p, i) M = M := by
        unfold gjStep
        rw [hcf, fc_rowAdd_false]
      rw [hM1]
      refine ⟨ih'.1, ?_⟩
      intro h
      obtain ⟨hM, hrest⟩ := ih'.2 h
      refine ⟨hM, ?_⟩
      intro i' hi' hfree
      rcases List.mem_cons.1 hi' with rfl | hi'
      · rw [hM] at h
        rcases hfree with hf | hf
        · simpa [gjCtl, hf, h] using hcf
        · simpa [gjCtl, hf, h] using hcf
      · exact hrest i' hi' hfree

theorem fc_B {D : ℕ} (p : Fin D) (k : ℕ) (l : List (Fin D))
    (hl : ∀ i ∈ l, i ≠ p) (M : Fin D × Fin D → Bool) (hpp : M (p, p) = true)
    (hrow : ∀ q : Fin D, q.val < k → M (p, q) = false) :
    (∀ i q : Fin D, q.val < k →
      (l.foldl (fun M i => gjStep (true, p, i) M) M) (i, q) = M (i, q)) ∧
    (∀ j, (l.foldl (fun M i => gjStep (true, p, i) M) M) (p, j) = M (p, j)) ∧
    (∀ i, i ≠ p → (i ∈ l ∨ M (i, p) = false) →
      (l.foldl (fun M i => gjStep (true, p, i) M) M) (i, p) = false) := by
  induction l generalizing M with
  | nil =>
    refine ⟨fun _ _ _ => rfl, fun _ => rfl, ?_⟩
    intro i _ h
    rcases h with h | h
    · exact absurd h (List.not_mem_nil)
    · exact h
  | cons i l ih =>
    have hip : i ≠ p := hl i (List.mem_cons_self)
    rw [List.foldl_cons]
    have h1 : ∀ j, gjStep (true, p, i) M (p, j) = M (p, j) := by
      intro j
      simp [gjStep, gjT, gjS, rowAdd, Ne.symm hip]
    have h2 : ∀ i' q : Fin D, q.val < k → gjStep (true, p, i) M (i', q) = M (i', q) := by
      intro i' q hq
      simp [gjStep, gjT, gjS, rowAdd, hrow q hq]
    have h3 : gjStep (true, p, i) M (i, p) = false := by
      simp [gjStep, gjT, gjS, rowAdd, gjCtl, hpp]
    have h4 : ∀ i', i' ≠ i → gjStep (true, p, i) M (i', p) = M (i', p) := by
      intro i' hi'
      simp [gjStep, gjT, gjS, rowAdd, hi']
    obtain ⟨ia, ib, ic⟩ := ih (fun i' h' => hl i' (List.mem_cons_of_mem _ h'))
      (gjStep (true, p, i) M) (by rw [h1]; exact hpp)
      (fun q hq => by rw [h1]; exact hrow q hq)
    refine ⟨?_, ?_, ?_⟩
    · intro i' q hq
      rw [ia i' q hq, h2 i' q hq]
    · intro j
      rw [ib j, h1 j]
    · intro i' hi'p h
      apply ic i' hi'p
      by_cases hii : i' = i
      · right
        rw [hii]
        exact h3
      · rcases h with h | h
        · rcases List.mem_cons.1 h with h | h
          · exact absurd h hii
          · left
            exact h
        · right
          rw [h4 i' hii]
          exact h

def fc_col {D : ℕ} (p : Fin D) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  ((List.finRange D).filter (fun i => i ≠ p)).foldl (fun M i => gjStep (true, p, i) M)
    (((List.finRange D).filter (fun i => i ≠ p)).foldl (fun M i => gjStep (false, p, i) M) M)

theorem fc_gj_eq {D : ℕ} (M : Fin D × Fin D → Bool) :
    gj D M = (List.finRange D).foldl (fun M p => fc_col p M) M := by
  unfold gj sched
  rw [List.foldl_flatMap]
  simp only [List.foldl_append, List.foldl_map, fc_col]

theorem fc_colInv {D : ℕ} (p : Fin D) (M : Fin D × Fin D → Bool) (hI : fc_Inv p.val M) :
    fc_Inv (p.val + 1) (fc_col p M) := by
  have hl : ∀ i ∈ (List.finRange D).filter (fun i => i ≠ p), i ≠ p := by
    intro i hi
    rw [List.mem_filter] at hi
    simpa using hi.2
  have hmem : ∀ i, i ≠ p → i ∈ (List.finRange D).filter (fun i => i ≠ p) := by
    intro i hi
    rw [List.mem_filter]
    exact ⟨List.mem_finRange i, by simpa using hi⟩
  obtain ⟨hIA, hA⟩ := fc_A p p.val rfl _ hl M hI
  unfold fc_col
  generalize ((List.finRange D).filter (fun i => i ≠ p)).foldl
    (fun M i => gjStep (false, p, i) M) M = MA at hIA hA
  by_cases hpp : MA (p, p) = true
  · have hrow : ∀ q : Fin D, q.val < p.val → MA (p, q) = false :=
      fun q hq => hIA.2.1 p q hq (Or.inl le_rfl)
    obtain ⟨ba, bb, bc⟩ := fc_B p p.val _ hl MA hpp hrow
    generalize ((List.finRange D).filter (fun i => i ≠ p)).foldl
      (fun M i => gjStep (true, p, i) M) MA = MB at ba bb bc
    obtain ⟨ha, hb, hc⟩ := hIA
    have hBpp : MB (p, p) = true := by rw [bb]; exact hpp
    refine ⟨?_, ?_, ?_⟩
    · intro q hq hqq i
      by_cases hqp : q = p
      · subst hqp
        by_cases hiq : i = q
        · subst hiq
          simp [hqq]
        · rw [bc i hiq (Or.inl (hmem i hiq))]
          simp [hiq]
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h)
          omega
        rw [ba _ _ hq'] at hqq ⊢
        exact ha q hq' hqq i
    · intro i q hq hfree
      have hip : i ≠ p := by
        intro h
        subst h
        rcases hfree with hf | hf
        · omega
        · rw [hBpp] at hf
          exact absurd hf (by simp)
      by_cases hqp : q = p
      · subst hqp
        exact bc i hip (Or.inl (hmem i hip))
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h)
          omega
        rw [ba _ _ hq']
        apply hb i q hq'
        by_cases hi : i.val < p.val
        · right
          rcases hfree with hf | hf
          · omega
          · rw [← ba _ _ hi]
            exact hf
        · left
          omega
    · intro p' q hqp' hp' hp'p'
      have hq' : q.val < p'.val := hqp'
      by_cases hpe : p' = p
      · subst hpe
        rw [bb]
        exact hrow q hq'
      · have hp'' : p'.val < p.val := by
          have : p'.val ≠ p.val := fun h => hpe (Fin.ext h)
          omega
        rw [ba _ _ (by omega)]
        rw [ba _ _ hp''] at hp'p'
        exact hc p' q hqp' hp'' hp'p'
  · have hppf : MA (p, p) = false := by simpa using hpp
    rw [fc_B_id p _ MA hppf]
    obtain ⟨hMeq, hcol⟩ := hA hppf
    obtain ⟨ha, hb, hc⟩ := hIA
    have hfreecol : ∀ i : Fin D, (p.val + 1 ≤ i.val ∨ MA (i, i) = false) → MA (i, p) = false := by
      intro i hfree
      by_cases hip : i = p
      · rw [hip]
        exact hppf
      · rw [hMeq] at hfree ⊢
        apply hcol i (hmem i hip)
        rcases hfree with hf | hf
        · left
          show p.val < i.val
          omega
        · right
          exact hf
    refine ⟨?_, ?_, ?_⟩
    · intro q hq hqq i
      by_cases hqp : q = p
      · subst hqp
        rw [hppf] at hqq
        exact absurd hqq (by simp)
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h)
          omega
        exact ha q hq' hqq i
    · intro i q hq hfree
      by_cases hqp : q = p
      · subst hqp
        exact hfreecol i hfree
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h)
          omega
        apply hb i q hq'
        rcases hfree with hf | hf
        · left
          omega
        · right
          exact hf
    · intro p' q hqp' hp' hp'p'
      have hpe : p' ≠ p := by
        intro h
        subst h
        rw [hppf] at hp'p'
        exact absurd hp'p' (by simp)
      have hp'' : p'.val < p.val := by
        have : p'.val ≠ p.val := fun h => hpe (Fin.ext h)
        omega
      exact hc p' q hqp' hp'' hp'p'

theorem fc_fold {D : ℕ} (l : List (Fin D)) :
    ∀ (k : ℕ), (∀ i (h : i < l.length), (l[i]).val = k + i) →
    ∀ M : Fin D × Fin D → Bool, fc_Inv k M →
      fc_Inv (k + l.length) (l.foldl (fun M p => fc_col p M) M) := by
  induction l with
  | nil => intro k _ M hI; exact hI
  | cons p l ih =>
    intro k hidx M hI
    have hp : p.val = k := by
      have := hidx 0 (by simp)
      simpa using this
    rw [List.foldl_cons]
    have h1 : fc_Inv (k + 1) (fc_col p M) := by
      have := fc_colInv p M (hp ▸ hI)
      rw [hp] at this
      exact this
    have h2 := ih (k + 1) (fun i h => by
      have := hidx (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      omega) (fc_col p M) h1
    have e : k + (p :: l).length = k + 1 + l.length := by simp; omega
    rw [e]
    exact h2

theorem fc_gjInv {D : ℕ} (M : Fin D × Fin D → Bool) : fc_Inv D (gj D M) := by
  rw [fc_gj_eq]
  have h0 : fc_Inv 0 M := by
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      omega
    · intro i q hq
      omega
    · intro p q _ hp
      omega
  have := fc_fold (List.finRange D) 0 (fun i h => by simp) M h0
  simpa using this

theorem gj_pivcol {D : ℕ} (M : Fin D × Fin D → Bool) (p : Fin D) (hp : gj D M (p, p) = true)
    (i : Fin D) : gj D M (i, p) = decide (i = p) :=
  (fc_gjInv M).1 p p.isLt hp i

theorem gj_zerorow {D : ℕ} (M : Fin D × Fin D → Bool) (q : Fin D) (hq : gj D M (q, q) = false)
    (j : Fin D) : gj D M (q, j) = false :=
  (fc_gjInv M).2.1 q j j.isLt (Or.inr hq)

theorem gj_upper {D : ℕ} (M : Fin D × Fin D → Bool) (p q : Fin D) (h : q < p) :
    gj D M (p, q) = false := by
  by_cases hp : gj D M (p, p) = true
  · exact (fc_gjInv M).2.2 p q h p.isLt hp
  · exact gj_zerorow M p (by simpa using hp) q

def sysBits {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) :
    Fin (m + N + 1) × Fin (m + N + 1) → Bool := fun p =>
  if hi : p.1.val < m then
    (if hj : p.2.val < N then decide (Hf ⟨p.1.val, hi⟩ ⟨p.2.val, hj⟩ ≠ 0)
     else if p.2.val = N then decide (rhs ⟨p.1.val, hi⟩ ≠ 0) else false)
  else false

def pv {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) : Bool :=
  R (cl m p, cl m p)

def fh_w {m N : ℕ} (v : V N) : V (m + N + 1) := fun j =>
  if h : j.val < N then v ⟨j.val, h⟩ else if j.val = N then 1 else 0

theorem fh_two : (2 : ZMod 2) = 0 := by decide

theorem fh_sum_split {m N : ℕ} (a : Fin N → ZMod 2) (b : ZMod 2) :
    (∑ j : Fin (m + N + 1),
      (if h : j.val < N then a ⟨j.val, h⟩ else if j.val = N then b else 0)) =
      ∑ j, a j + b := by
  have hD : N + 1 + m = m + N + 1 := by omega
  rw [← Equiv.sum_comp (finCongr hD)]
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  have h3 : (∑ x : Fin m, (if h : (finCongr hD (Fin.natAdd (N + 1) x)).val < N then
      a ⟨(finCongr hD (Fin.natAdd (N + 1) x)).val, h⟩
      else if (finCongr hD (Fin.natAdd (N + 1) x)).val = N then b else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have e : (finCongr hD (Fin.natAdd (N + 1) x)).val = N + 1 + x.val := rfl
    rw [dif_neg (by rw [e]; omega), if_neg (by rw [e]; omega)]
  rw [h3, add_zero]
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    have e : (finCongr hD (Fin.castAdd m (Fin.castSucc x))).val = x.val := rfl
    rw [dif_pos (by rw [e]; exact x.isLt)]
    exact congrArg a (Fin.ext e)
  · have e : (finCongr hD (Fin.castAdd m (Fin.last N))).val = N := rfl
    rw [dif_neg (by rw [e]; omega), if_pos e]

theorem fh_mulVec_w {m N : ℕ} (X : Matrix (Fin (m + N + 1)) (Fin (m + N + 1)) (ZMod 2))
    (v : V N) (i : Fin (m + N + 1)) :
    X.mulVec (fh_w v) i = ∑ p : Fin N, X i (cl m p) * v p + X i (rc m N) := by
  rw [← fh_sum_split (m := m) (fun p => X i (cl m p) * v p) (X i (rc m N))]
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro j _
  unfold fh_w
  split_ifs with h1 h2
  · rfl
  · have : j = rc m N := Fin.ext h2
    rw [this, mul_one]
  · rw [mul_zero]

theorem fh_bit (x : ZMod 2) : (if decide (x ≠ 0) = true then (1 : ZMod 2) else 0) = x := by
  revert x; decide

theorem fh_sys_cl {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (i : Fin (m + N + 1))
    (p : Fin N) :
    mat (sysBits Hf rhs) i (cl m p) = if hi : i.val < m then Hf ⟨i.val, hi⟩ p else 0 := by
  unfold mat sysBits
  by_cases hi : i.val < m
  · have hp : (cl m p).val < N := p.isLt
    simp only [dif_pos hi, dif_pos hp]
    exact fh_bit _
  · simp only [dif_neg hi]
    rfl

theorem fh_sys_rc {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (i : Fin (m + N + 1)) :
    mat (sysBits Hf rhs) i (rc m N) = if hi : i.val < m then rhs ⟨i.val, hi⟩ else 0 := by
  unfold mat sysBits
  by_cases hi : i.val < m
  · have hp : ¬ (rc m N).val < N := by show ¬ N < N; omega
    have hp2 : (rc m N).val = N := rfl
    simp only [dif_pos hi, dif_neg hp, if_pos hp2]
    exact fh_bit _
  · simp only [dif_neg hi]
    rfl

theorem fh_sys_hi {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (i j : Fin (m + N + 1)) (hj : N < j.val) : mat (sysBits Hf rhs) i j = 0 := by
  unfold mat sysBits
  by_cases hi : i.val < m
  · simp only [dif_pos hi, dif_neg (show ¬ j.val < N by omega),
      if_neg (show ¬ j.val = N by omega)]
    rfl
  · simp only [dif_neg hi]
    rfl

theorem fh_sys_iff {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (v : V N) :
    (∀ i, Hf i ⬝ᵥ v = rhs i) ↔ (mat (sysBits Hf rhs)).mulVec (fh_w v) = 0 := by
  constructor
  · intro h
    funext i
    rw [fh_mulVec_w]
    simp only [fh_sys_cl, fh_sys_rc]
    by_cases hi : i.val < m
    · simp only [dif_pos hi]
      have := h ⟨i.val, hi⟩
      unfold dotProduct at this
      rw [this]
      show rhs ⟨i.val, hi⟩ + rhs ⟨i.val, hi⟩ = 0
      linear_combination rhs ⟨i.val, hi⟩ * fh_two
    · simp only [dif_neg hi, zero_mul, Finset.sum_const_zero, add_zero]
      rfl
  · intro h i
    have := congrFun h ⟨i.val, by omega⟩
    rw [fh_mulVec_w] at this
    simp only [fh_sys_cl, fh_sys_rc, dif_pos i.isLt] at this
    unfold dotProduct
    have e : (∑ x, Hf i x * v x) + rhs i = 0 := this
    linear_combination e - rhs i * fh_two

theorem fh_R_iff {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (v : V N) :
    (mat (sysBits Hf rhs)).mulVec (fh_w v) = 0 ↔
      (mat (gj _ (sysBits Hf rhs))).mulVec (fh_w v) = 0 := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv (sysBits Hf rhs)
  constructor
  · intro h
    rw [h1, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · intro h
    rw [h2, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

theorem fh_mat_zero {r c : ℕ} (R : Fin r × Fin c → Bool) (i : Fin r) (j : Fin c)
    (h : mat R i j = 0) : R (i, j) = false := by
  unfold mat at h
  by_contra hc
  rw [if_pos (by simpa using hc)] at h
  exact one_ne_zero h

theorem fh_mat_false {r c : ℕ} (R : Fin r × Fin c → Bool) (i : Fin r) (j : Fin c)
    (h : R (i, j) = false) : mat R i j = 0 := by
  unfold mat; rw [h]; rfl

theorem fh_mat_true {r c : ℕ} (R : Fin r × Fin c → Bool) (i : Fin r) (j : Fin c)
    (h : R (i, j) = true) : mat R i j = 1 := by
  unfold mat; rw [h]; rfl

theorem fh_hicol {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (i j : Fin (m + N + 1)) (hj : N < j.val) : gj _ (sysBits Hf rhs) (i, j) = false := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv (sysBits Hf rhs)
  apply fh_mat_zero
  rw [h1, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [fh_sys_hi Hf rhs k j hj, mul_zero]

theorem fh_row_split {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (hpc : ∀ p, R (p, p) = true → ∀ i, R (i, p) = decide (i = p))
    (p : Fin N) (hp : pv R p = true) (u : V N) :
    ∑ q, mat R (cl m p) (cl m q) * u q =
      u p + ∑ q, if pv R q = false then mat R (cl m p) (cl m q) * u q else 0 := by
  have hpt : ∀ q : Fin N, mat R (cl m p) (cl m q) * u q =
      (if q = p then u p else 0) +
        (if pv R q = false then mat R (cl m p) (cl m q) * u q else 0) := by
    intro q
    by_cases hq : q = p
    · subst hq
      rw [if_pos rfl, if_neg (by rw [hp]; simp), add_zero, fh_mat_true R _ _ hp, one_mul]
    · rw [if_neg hq, zero_add]
      by_cases hv : pv R q = false
      · rw [if_pos hv]
      · rw [if_neg hv]
        have hv' : R (cl m q, cl m q) = true := by simpa [pv] using hv
        have := hpc (cl m q) hv' (cl m p)
        have hne : cl m p ≠ cl m q := by
          intro h
          apply hq
          apply Fin.ext
          exact (congrArg Fin.val h).symm
        rw [decide_eq_false hne] at this
        rw [fh_mat_false R _ _ this, zero_mul]
  rw [Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_univ p)]

theorem fh_Rsol {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (hpc : ∀ p, R (p, p) = true → ∀ i, R (i, p) = decide (i = p))
    (hzr : ∀ q, R (q, q) = false → ∀ j, R (q, j) = false)
    (hhi : ∀ i j : Fin (m + N + 1), N < j.val → R (i, j) = false)
    (hcons : R (rc m N, rc m N) = false) (v : V N) :
    (mat R).mulVec (fh_w v) = 0 ↔
      ∀ p : Fin N, pv R p = true → v p = mat R (cl m p) (rc m N) +
        ∑ q, if pv R q = false then mat R (cl m p) (cl m q) * v q else 0 := by
  constructor
  · intro h p hp
    have := congrFun h (cl m p)
    rw [fh_mulVec_w, fh_row_split R hpc p hp] at this
    have e : v p + (∑ q, if pv R q = false then mat R (cl m p) (cl m q) * v q else 0) +
        mat R (cl m p) (rc m N) = 0 := this
    linear_combination e - (mat R (cl m p) (rc m N) +
      ∑ q, if pv R q = false then mat R (cl m p) (cl m q) * v q else 0) * fh_two
  · intro h
    funext i
    rw [fh_mulVec_w]
    by_cases hi : R (i, i) = true
    · have h1 : ¬ N < i.val := by
        intro hlt
        have := hhi i i hlt
        rw [hi] at this
        exact Bool.noConfusion this
      have h2 : i.val ≠ N := by
        intro he
        have : i = rc m N := Fin.ext he
        rw [this, hcons] at hi
        exact Bool.noConfusion hi
      have h3 : i.val < N := by omega
      have h4 : i = cl m (⟨i.val, h3⟩ : Fin N) := Fin.ext rfl
      have hp : pv R (⟨i.val, h3⟩ : Fin N) = true := by
        show R (cl m ⟨i.val, h3⟩, cl m ⟨i.val, h3⟩) = true
        rw [← h4]; exact hi
      rw [h4, fh_row_split R hpc _ hp, h _ hp]
      show _ = (0 : ZMod 2)
      linear_combination (mat R (cl m (⟨i.val, h3⟩ : Fin N)) (rc m N) +
        ∑ q, if pv R q = false then mat R (cl m (⟨i.val, h3⟩ : Fin N)) (cl m q) * v q else 0) *
          fh_two
    · have hz := hzr i (by simpa using hi)
      rw [fh_mat_false R _ _ (hz _)]
      rw [Finset.sum_eq_zero (fun q _ => by rw [fh_mat_false R _ _ (hz _), zero_mul]), add_zero]
      rfl

theorem fh_main_iff {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (hcons : gj _ (sysBits Hf rhs) (rc m N, rc m N) = false) (v : V N) :
    (∀ i, Hf i ⬝ᵥ v = rhs i) ↔
      ∀ p : Fin N, pv (gj _ (sysBits Hf rhs)) p = true →
        v p = mat (gj _ (sysBits Hf rhs)) (cl m p) (rc m N) +
          ∑ q, if pv (gj _ (sysBits Hf rhs)) q = false then
            mat (gj _ (sysBits Hf rhs)) (cl m p) (cl m q) * v q else 0 := by
  rw [fh_sys_iff, fh_R_iff]
  exact fh_Rsol _ (fun p hp i => gj_pivcol _ p hp i) (fun q hq j => gj_zerorow _ q hq j)
    (fun i j hj => fh_hicol Hf rhs i j hj) hcons v

theorem la_incons {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits Hf rhs) (rc m N, rc m N) = true) (v : V N) :
    ¬ ∀ i, Hf i ⬝ᵥ v = rhs i := by
  rw [fh_sys_iff, fh_R_iff]
  intro h0
  have := congrFun h0 (rc m N)
  rw [fh_mulVec_w, fh_mat_true _ _ _ h] at this
  rw [Finset.sum_eq_zero] at this
  · rw [zero_add] at this
    exact one_ne_zero this
  · intro q _
    have : gj _ (sysBits Hf rhs) (rc m N, cl m q) = false := by
      apply gj_upper
      show q.val < N
      exact q.isLt
    rw [fh_mat_false _ _ _ this, zero_mul]

theorem sc_b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> simp [b2z]

theorem sc_b2z_bx {ι : Type} [Fintype ι] (f : ι → Bool) : b2z (bx f) = ∑ i, b2z (f i) := by
  have h1 : (∑ i, b2z (f i)) = ((Finset.univ.filter (fun i => f i = true)).card : ZMod 2) := by
    unfold b2z
    rw [Finset.natCast_card_filter]
  rw [h1, ← ZMod.natCast_mod]
  unfold bx
  rcases Nat.mod_two_eq_zero_or_one (Finset.univ.filter (fun i => f i = true)).card with h | h
  · rw [h]; simp [b2z]
  · rw [h]; simp [b2z]

theorem sc_sum_dec {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι) (d : ι → ZMod 2) :
    ∑ c, b2z (decide (a = c)) * d c = d a := by
  simp [b2z]

theorem sc_sysB {M N : ℕ} (H : Fin M × Fin N → Bool) (rhs : Fin M → Bool) :
    sysB H rhs = sysBits (fun i c => b2z (H (i, c))) (fun i => b2z (rhs i)) := by
  have hb : ∀ b : Bool, decide (b2z b ≠ 0) = b := by
    intro b; cases b <;> simp [b2z]
  funext p
  unfold sysB sysBits
  simp only [hb]

theorem sc_count {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) :
    Nat.card {v : V N // ∀ i, Hf i ⬝ᵥ v = rhs i} =
      (if (!(gj _ (sysBits Hf rhs) (rc m N, rc m N))) = true then
        2 ^ (Finset.univ.filter (fun p : Fin N =>
          (!(gj _ (sysBits Hf rhs) (cl m p, cl m p))) = true)).card else 0) := by
  by_cases hc : gj _ (sysBits Hf rhs) (rc m N, rc m N) = true
  · have : IsEmpty {v : V N // ∀ i, Hf i ⬝ᵥ v = rhs i} :=
      ⟨fun v => la_incons Hf rhs hc v.1 v.2⟩
    rw [Nat.card_of_isEmpty, hc]; simp
  · have hc' : gj _ (sysBits Hf rhs) (rc m N, rc m N) = false := by simpa using hc
    have key := fh_main_iff Hf rhs hc'
    rw [hc']
    simp only [Bool.not_false, if_true]
    generalize gj _ (sysBits Hf rhs) = R at key
    let e : {v : V N // ∀ i, Hf i ⬝ᵥ v = rhs i} ≃ ({q : Fin N // pv R q = false} → ZMod 2) :=
      { toFun := fun v q => v.1 q.1
        invFun := fun f => ⟨fun p => if h : pv R p = false then f ⟨p, h⟩ else
            mat R (cl m p) (rc m N) +
              ∑ q, if h : pv R q = false then mat R (cl m p) (cl m q) * f ⟨q, h⟩ else 0, by
          rw [key]; intro p hp
          rw [dif_neg (by simp [hp])]
          congr 1
          apply Finset.sum_congr rfl; intro q _
          by_cases hq : pv R q = false
          · rw [dif_pos hq, if_pos hq, dif_pos hq]
          · rw [dif_neg hq, if_neg hq]⟩
        left_inv := by
          intro v; apply Subtype.ext; funext p
          by_cases hp : pv R p = false
          · simp [hp]
          · have := (key v.1).1 v.2 p (by simpa using hp)
            show (if h : pv R p = false then _ else _) = v.1 p
            rw [dif_neg hp]
            refine Eq.trans ?_ this.symm
            congr 1
        right_inv := by intro f; funext q; simp [q.2] }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_subtype]
    congr 2

theorem sc_two (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  revert x y; decide

theorem sc_v0 {k m : ℕ} (d : V k) (j : T k m) :
    ∑ c, b2z (v0B (unitB c) (fun _ => false) j) * d c =
      mk d (fun _ => 0) (rotZ 1 d) (rotZ 3 d) j := by
  rcases j with i | j | i | i
  · simp only [v0B, mk, Sum.elim_inl, unitB]
    exact sc_sum_dec i d
  · simp [v0B, mk, b2z]
  · simp only [v0B, mk, Sum.elim_inl, Sum.elim_inr, unitB, rotB, rotZ]
    exact sc_sum_dec _ d
  · simp only [v0B, mk, Sum.elim_inr, unitB, rotB, rotZ]
    exact sc_sum_dec _ d

theorem sc_row {k m : ℕ} (C0 : T k m × T k m → Bool) (y : Fin m → Bool) (pin value : Fin k → Bool)
    (d : V k) :
    ((∀ i, pin i = true → d i = b2z (value i)) ∧
        kerB C0 (mk d (toZ y) (rotZ 1 d) (rotZ 3 d))) ↔
      ∀ ρ : T k m ⊕ Fin k, ∑ c, b2z (finH C0 pin (ρ, c)) * d c = b2z (finR C0 y pin value ρ) := by
  have hA : ∀ a : T k m, ∑ c, b2z (finH C0 pin (Sum.inl a, c)) * d c =
      ∑ j, b2z (C0 (a, j)) * mk d (fun _ => 0) (rotZ 1 d) (rotZ 3 d) j := by
    intro a
    simp only [finH, Sum.elim_inl, sc_b2z_bx, sc_b2z_and, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← sc_v0 d j, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    ring
  have hB : ∀ a : T k m, ∑ j, b2z (C0 (a, j)) * mk d (toZ y) (rotZ 1 d) (rotZ 3 d) j =
      ∑ j, b2z (C0 (a, j)) * mk d (fun _ => 0) (rotZ 1 d) (rotZ 3 d) j +
        b2z (finR C0 y pin value (Sum.inl a)) := by
    intro a
    simp only [finR, Sum.elim_inl, sc_b2z_bx, sc_b2z_and, Fintype.sum_sum_type, mk, Sum.elim_inl,
      Sum.elim_inr, toZ, mul_zero, Finset.sum_const_zero]
    ring
  have hP : ∀ i : Fin k, ∑ c, b2z (finH C0 pin (Sum.inr i, c)) * d c = b2z (pin i) * d i := by
    intro i
    simp only [finH, Sum.elim_inr, sc_b2z_and, mul_assoc]
    rw [← Finset.mul_sum, sc_sum_dec]
  constructor
  · rintro ⟨h1, h2⟩ ρ
    rcases ρ with a | i
    · rw [hA, ← sc_two, ← hB]; exact h2 a
    · rw [hP]
      simp only [finR, Sum.elim_inr, sc_b2z_and]
      by_cases hp : pin i = true
      · rw [h1 i hp]
      · have : pin i = false := by simpa using hp
        simp [this, b2z]
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hp
      have := h (Sum.inr i)
      rw [hP] at this
      simpa [finR, sc_b2z_and, hp, b2z] using this
    · intro a
      rw [hB, sc_two, ← hA]; exact h (Sum.inl a)

theorem fin_count {k m : ℕ} (C0 : T k m × T k m → Bool) (y : Fin m → Bool)
    (pin value : Fin k → Bool) :
    (if (!(gj _ (finSys C0 y pin value) (rc _ k, rc _ k))) = true then
        2 ^ (Finset.univ.filter (fun p : Fin k =>
          (!(gj _ (finSys C0 y pin value) (cl _ p, cl _ p))) = true)).card else 0) =
      Nat.card {d : V k // (∀ i, pin i = true → d i = b2z (value i)) ∧
        kerB C0 (mk d (toZ y) (rotZ 1 d) (rotZ 3 d))} := by
  have hs : finSys C0 y pin value = sysBits
      (fun (i : Fin (rowsN k m)) (c : Fin k) =>
        b2z (finH C0 pin ((Fintype.equivFin (T k m ⊕ Fin k)).symm i, c)))
      (fun i => b2z (finR C0 y pin value ((Fintype.equivFin (T k m ⊕ Fin k)).symm i))) := by
    unfold finSys
    rw [sc_sysB]
  rw [hs, ← sc_count]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro d
  rw [sc_row]
  constructor
  · intro h ρ
    have := h (Fintype.equivFin (T k m ⊕ Fin k) ρ)
    simpa [dotProduct] using this
  · intro h i
    exact h _

theorem sb_two : (2 : ZMod 2) = 0 := by decide

theorem sb_z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem sb_add_self (a : ZMod 2) : a + a = 0 := by
  rcases sb_z2 a with h | h <;> subst h <;> decide

theorem sb_eq_of_add (a b : ZMod 2) (h : a + b = 0) : a = b := by
  revert a b; decide

@[simp] theorem sb_b2z_false : b2z false = 0 := rfl
@[simp] theorem sb_b2z_true : b2z true = 1 := rfl
@[simp] theorem sb_b2z_eq_zero (b : Bool) : b2z b = 0 ↔ b = false := by cases b <;> decide

theorem sb_b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide
theorem sb_b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide
theorem sb_b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by cases a <;> decide
theorem sb_b2z_decide (p : Prop) [Decidable p] : b2z (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

theorem sb_b2z_bx {ι : Type} [Fintype ι] (f : ι → Bool) : b2z (bx f) = ∑ i, b2z (f i) := by
  have h1 : ∑ i, b2z (f i) = (((Finset.univ.filter (fun i => f i = true)).card : ℕ) : ZMod 2) := by
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases f i <;> simp
  rw [h1, bx, ← ZMod.natCast_mod _ 2]
  rcases Nat.mod_two_eq_zero_or_one (Finset.univ.filter (fun i => f i = true)).card with h | h <;>
    rw [h] <;> simp

theorem sb_ker_mat {D : ℕ} (N : Fin D × Fin D → Bool) (w : Fin D → ZMod 2) :
    kerB N w ↔ (mat N).mulVec w = 0 := by
  constructor
  · intro h; funext a; exact h a
  · intro h a; exact congrFun h a

theorem sb_ker_gj {D : ℕ} (N : Fin D × Fin D → Bool) (w : Fin D → ZMod 2) :
    kerB (gj D N) w ↔ kerB N w := by
  rw [sb_ker_mat, sb_ker_mat]
  obtain ⟨U, U', h1, h2⟩ := gj_equiv N
  constructor
  · intro h; rw [h2, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · intro h; rw [h1, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

theorem sb_ker_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (N : κ × κ → Bool)
    (v : ι → ZMod 2) :
    kerB (fun p : ι × ι => N (e p.1, e p.2)) v ↔ kerB N (fun j => v (e.symm j)) := by
  have hs : ∀ a : κ, ∑ j : ι, b2z (N (a, e j)) * v j = ∑ j : κ, b2z (N (a, j)) * v (e.symm j) := by
    intro a
    apply Fintype.sum_equiv e
    intro j; simp
  constructor
  · intro h a
    rw [← hs]
    have := h (e.symm a)
    simpa using this
  · intro h a
    show ∑ j : ι, b2z (N (e a, e j)) * v j = 0
    rw [hs]; exact h (e a)

theorem sb_ker_reindex2 {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (M : ι × ι → Bool)
    (v : ι → ZMod 2) :
    kerB M v ↔ kerB (fun q : κ × κ => M (e.symm q.1, e.symm q.2)) (fun j => v (e.symm j)) := by
  have hs : ∀ a : ι, ∑ j : ι, b2z (M (a, j)) * v j =
      ∑ j : κ, b2z (M (a, e.symm j)) * v (e.symm j) := by
    intro a
    apply Fintype.sum_equiv e
    intro j; simp
  constructor
  · intro h a
    show ∑ j : κ, b2z (M (e.symm a, e.symm j)) * v (e.symm j) = 0
    rw [← hs]; exact h _
  · intro h a
    rw [hs]
    have := h (e a)
    simp only [Equiv.symm_apply_apply] at this
    exact this

theorem sb_rref_ker {ι : Type} [Fintype ι] (M : ι × ι → Bool) (v : ι → ZMod 2) :
    kerB (rref M) v ↔ kerB M v := by
  have h1 := sb_ker_reindex (Fintype.equivFin ι) (gj (Fintype.card ι)
    (fun q => M ((Fintype.equivFin ι).symm q.1, (Fintype.equivFin ι).symm q.2))) v
  have h2 := sb_ker_reindex2 (Fintype.equivFin ι) M v
  exact h1.trans ((sb_ker_gj _ _).trans h2.symm)

theorem sb_rref_piv {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι × ι → Bool) (p : ι)
    (hp : rref M (p, p) = true) (i : ι) : rref M (i, p) = decide (i = p) := by
  have h2 : rref M (i, p) = decide (Fintype.equivFin ι i = Fintype.equivFin ι p) :=
    gj_pivcol _ _ hp (Fintype.equivFin ι i)
  rw [h2]; simp

theorem sb_rref_zero {ι : Type} [Fintype ι] (M : ι × ι → Bool) (q : ι)
    (hq : rref M (q, q) = false) (j : ι) : rref M (q, j) = false :=
  gj_zerorow _ _ hq (Fintype.equivFin ι j)

theorem sb_absorb_zcol {ι : Type} [Fintype ι] [DecidableEq ι] (R B : ι × ι → Bool) (a : ι ⊕ ι)
    (q : ι) : rref (stack R B) (a, Sum.inr q) = false := by
  have h : kerB (stack R B) (Pi.single (Sum.inr q) 1) := by
    intro a; simp [stack, Fintype.sum_sum_type, Pi.single_apply]
  rw [← sb_rref_ker] at h
  have := h a
  simpa [Fintype.sum_sum_type, Pi.single_apply] using this

theorem sb_absorb_zrow {ι : Type} [Fintype ι] [DecidableEq ι] (R B : ι × ι → Bool) (q : ι)
    (j : ι ⊕ ι) : rref (stack R B) (Sum.inr q, j) = false :=
  sb_rref_zero _ _ (sb_absorb_zcol R B _ q) j

theorem sb_absorb_ker {ι : Type} [Fintype ι] [DecidableEq ι] (R B : ι × ι → Bool)
    (v : ι → ZMod 2) : kerB (absorb R B) v ↔ kerB R v ∧ kerB B v := by
  have h := sb_rref_ker (stack R B) (Sum.elim v (fun _ => 0))
  have h1 : kerB (rref (stack R B)) (Sum.elim v (fun _ => 0)) ↔ kerB (absorb R B) v := by
    constructor
    · intro hh a
      have := hh (Sum.inl a)
      simpa [Fintype.sum_sum_type, absorb] using this
    · intro hh a
      rcases a with a | a
      · have := hh a
        simpa [Fintype.sum_sum_type, absorb] using this
      · simp [Fintype.sum_sum_type, sb_absorb_zrow]
  have h2 : kerB (stack R B) (Sum.elim v (fun _ => 0)) ↔ kerB R v ∧ kerB B v := by
    constructor
    · intro hh
      refine ⟨fun a => ?_, fun a => ?_⟩
      · have := hh (Sum.inl a)
        simpa [stack, Fintype.sum_sum_type] using this
      · have := hh (Sum.inr a)
        simpa [stack, Fintype.sum_sum_type] using this
    · rintro ⟨k1, k2⟩ (a | a)
      · have := k1 a
        simpa [stack, Fintype.sum_sum_type] using this
      · have := k2 a
        simpa [stack, Fintype.sum_sum_type] using this
  exact h1.symm.trans (h.trans h2)

def sb_RR {ι : Type} [DecidableEq ι] (R : ι × ι → Bool) : Prop :=
  (∀ p, R (p, p) = true → ∀ i, R (i, p) = decide (i = p)) ∧
  (∀ q, R (q, q) = false → ∀ j, R (q, j) = false)

theorem sb_absorb_RR {ι : Type} [Fintype ι] [DecidableEq ι] (R B : ι × ι → Bool) :
    sb_RR (absorb R B) := by
  refine ⟨fun p hp i => ?_, fun q hq j => ?_⟩
  · have := sb_rref_piv (stack R B) (Sum.inl p) hp (Sum.inl i)
    simpa [absorb] using this
  · exact sb_rref_zero (stack R B) (Sum.inl q) hq (Sum.inl j)

theorem sb_fold_ker {ι α : Type} [Fintype ι] [DecidableEq ι] (Bf : α → ι × ι → Bool)
    (L : List α) (R0 : ι × ι → Bool) (v : ι → ZMod 2) :
    kerB (L.foldl (fun R a => absorb R (Bf a)) R0) v ↔ kerB R0 v ∧ ∀ a ∈ L, kerB (Bf a) v := by
  induction L generalizing R0 with
  | nil => simp
  | cons a L ih => rw [List.foldl_cons, ih, sb_absorb_ker]; simp [and_assoc]

theorem sb_fold_RR {ι α : Type} [Fintype ι] [DecidableEq ι] (Bf : α → ι × ι → Bool)
    (L : List α) (R0 : ι × ι → Bool) (h0 : sb_RR R0) :
    sb_RR (L.foldl (fun R a => absorb R (Bf a)) R0) := by
  induction L generalizing R0 with
  | nil => exact h0
  | cons a L ih => exact ih _ (sb_absorb_RR _ _)

theorem sb_polR_RR {k m : ℕ} (C : T k m × T k m → Bool) : sb_RR (polR C) :=
  sb_fold_RR _ _ _ ⟨fun p hp => by simp at hp, fun q _ j => rfl⟩

theorem sb_polR_ker {k m : ℕ} (C : T k m × T k m → Bool) (v : T k m → ZMod 2) :
    kerB (polR C) v ↔ ∀ a, kerB (polB C a) v := by
  unfold polR
  rw [sb_fold_ker]
  have : kerB (fun _ : T k m × T k m => false) v := by intro a; simp
  simp [this]

theorem sb_mix_add {k : ℕ} (g : ℕ) (x y : V k) : mixZ g (x + y) = mixZ g x + mixZ g y := by
  funext i; simp only [mixZ, rotZ, Pi.add_apply]; ring

theorem sb_key {k : ℕ} (g : ℕ) (x e : V k) (i : Fin k) :
    FZ g (x + e) i + FZ g x i = FZ g e i + PZ g e x i := by
  simp only [FZ, chiZ, PZ, sb_mix_add, Pi.add_apply]
  linear_combination (mixZ g x i + mixZ g x (ix i 2) + mixZ g x (ix i 1) * mixZ g x (ix i 2)) *
    sb_two

theorem sb_PZ_add_e {k : ℕ} (g : ℕ) (e e' x : V k) (i : Fin k) :
    PZ g (e + e') x i = PZ g e x i + PZ g e' x i := by
  simp only [PZ, sb_mix_add, Pi.add_apply]; ring

theorem sb_PZ_add_x {k : ℕ} (g : ℕ) (e x x' : V k) (i : Fin k) :
    PZ g e (x + x') i = PZ g e x i + PZ g e x' i := by
  simp only [PZ, sb_mix_add, Pi.add_apply]; ring

theorem sb_PZ_zero_x {k : ℕ} (g : ℕ) (e : V k) (i : Fin k) : PZ g e 0 i = 0 := by
  have := sb_PZ_add_x g e 0 0 i
  simpa using this

theorem sb_toZ_mix {k : ℕ} (g : ℕ) (x : Fin k → Bool) : toZ (mixB g x) = mixZ g (toZ x) := by
  funext i; simp only [toZ, mixB, mixZ, rotB, rotZ, sb_b2z_xor]

theorem sb_toZ_PB {k : ℕ} (g : ℕ) (e x : Fin k → Bool) :
    toZ (PB g e x) = PZ g (toZ e) (toZ x) := by
  funext i
  show b2z (PB g e x i) = _
  simp only [PZ, ← sb_toZ_mix, PB, sb_b2z_xor, sb_b2z_and]
  rfl

theorem sb_toZ_FB {k : ℕ} (g : ℕ) (x : Fin k → Bool) : toZ (FB g x) = FZ g (toZ x) := by
  funext i
  show b2z (chiB (mixB g x) i) = chiZ (mixZ g (toZ x)) i
  rw [← sb_toZ_mix]
  simp [chiB, chiZ, toZ, sb_b2z_xor, sb_b2z_and, sb_b2z_not]

theorem sb_toZ_unit {ι : Type} [DecidableEq ι] (c : ι) :
    toZ (unitB c) = (Pi.single c 1 : ι → ZMod 2) := by
  funext j; simp [toZ, unitB, Pi.single_apply, sb_b2z_decide]

def sb_Z0 {k m : ℕ} (t : ℕ) (v : T k m → ZMod 2) : T k m → ZMod 2 :=
  mk (pd v) (py v)
    (fun i => FZ 1 (pr v) i + rotZ (2 * t) (pd v) i)
    (fun i => FZ 2 (pc v) i + rotZ (3 * (t + 1) + 1) (pd v) i)

theorem sb_toZ_ZB {k m : ℕ} (t : ℕ) (w : T k m → Bool) : toZ (ZB t w) = sb_Z0 t (toZ w) := by
  funext j
  rcases j with j | j | j | j
  · rfl
  · rfl
  · show b2z (xor (FB 1 (pr w) j) (rotB (2 * t) (pd w) j)) =
      FZ 1 (pr (toZ w)) j + rotZ (2 * t) (pd (toZ w)) j
    rw [sb_b2z_xor]
    have h : pr (toZ w) = toZ (pr w) := rfl
    rw [h, ← sb_toZ_FB]; rfl
  · show b2z (xor (FB 2 (pc w) j) (rotB (3 * (t + 1) + 1) (pd w) j)) =
      FZ 2 (pc (toZ w)) j + rotZ (3 * (t + 1) + 1) (pd (toZ w)) j
    rw [sb_b2z_xor]
    have h : pc (toZ w) = toZ (pc w) := rfl
    rw [h, ← sb_toZ_FB]; rfl

def sb_slr {k m : ℕ} (j : Fin k) : T k m := Sum.inr (Sum.inr (Sum.inl j))
def sb_slc {k m : ℕ} (j : Fin k) : T k m := Sum.inr (Sum.inr (Sum.inr j))

def sb_pol {k m : ℕ} (C : T k m × T k m → Bool) (g : ℕ) (sl : Fin k → T k m) (a : T k m)
    (e x : V k) : ZMod 2 :=
  ∑ j, b2z (C (a, sl j)) * PZ g e x j

def sb_q {k m : ℕ} (t : ℕ) (C : T k m × T k m → Bool) (a : T k m) (v : T k m → ZMod 2) :
    ZMod 2 :=
  ∑ j, b2z (C (a, j)) * sb_Z0 t v j

theorem sb_expand {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ZMod 2) → ZMod 2)
    (hadd : ∀ u w, f (u + w) = f u + f w) (e : ι → ZMod 2) :
    f e = ∑ c, e c * f (Pi.single c 1) := by
  have h0 : f 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have hs : ∀ s : Finset ι,
      f (∑ c ∈ s, Pi.single c (e c)) = ∑ c ∈ s, e c * f (Pi.single c 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert c s hc ih =>
      rw [Finset.sum_insert hc, Finset.sum_insert hc, hadd, ih]
      congr 1
      rcases sb_z2 (e c) with h | h <;> rw [h] <;> simp [h0]
  have := hs Finset.univ
  rwa [Finset.univ_sum_single] at this

theorem sb_pol_expand_e {k m : ℕ} (C : T k m × T k m → Bool) (g : ℕ) (sl : Fin k → T k m)
    (a : T k m) (e x : V k) :
    sb_pol C g sl a e x = ∑ c, e c * sb_pol C g sl a (Pi.single c 1) x :=
  sb_expand (fun e => sb_pol C g sl a e x)
    (by intro u w; simp only [sb_pol, sb_PZ_add_e, mul_add, Finset.sum_add_distrib]) e

theorem sb_pol_expand_x {k m : ℕ} (C : T k m × T k m → Bool) (g : ℕ) (sl : Fin k → T k m)
    (a : T k m) (e x : V k) :
    sb_pol C g sl a e x = ∑ c, x c * sb_pol C g sl a e (Pi.single c 1) :=
  sb_expand (fun x => sb_pol C g sl a e x)
    (by intro u w; simp only [sb_pol, sb_PZ_add_x, mul_add, Finset.sum_add_distrib]) x

theorem sb_pol_zero {k m : ℕ} (C : T k m × T k m → Bool) (g : ℕ) (sl : Fin k → T k m)
    (a : T k m) (e : V k) : sb_pol C g sl a e 0 = 0 := by
  simp [sb_pol, sb_PZ_zero_x]

theorem sb_pol_all {k m : ℕ} (C : T k m × T k m → Bool) (g : ℕ) (sl : Fin k → T k m)
    (a : T k m) (e : V k) (h : ∀ i, sb_pol C g sl a e (Pi.single i 1) = 0) (x : V k) :
    sb_pol C g sl a e x = 0 := by
  rw [sb_pol_expand_x]; simp [h]

theorem sb_polB_ker {k m : ℕ} (C : T k m × T k m → Bool) (a : T k m) (v : T k m → ZMod 2) :
    kerB (polB C a) v ↔
      (∀ i, sb_pol C 1 sb_slr a (pr v) (Pi.single i 1) = 0) ∧
      (∀ i, sb_pol C 2 sb_slc a (pc v) (Pi.single i 1) = 0) := by
  have hr : ∀ i : Fin k, ∑ j, b2z (polB C a (Sum.inr (Sum.inr (Sum.inl i)), j)) * v j =
      sb_pol C 1 sb_slr a (pr v) (Pi.single i 1) := by
    intro i
    rw [sb_pol_expand_e]
    simp only [polB, mk, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sb_b2z_false, zero_mul,
      Finset.sum_const_zero, zero_add, add_zero]
    apply Finset.sum_congr rfl
    intro c _
    rw [sb_b2z_bx, mul_comm]
    congr 1
    unfold sb_pol
    apply Finset.sum_congr rfl
    intro j _
    rw [sb_b2z_and]
    congr 1
    have := congrFun (sb_toZ_PB 1 (unitB c) (unitB i)) j
    rw [sb_toZ_unit, sb_toZ_unit] at this
    exact this
  have hc : ∀ i : Fin k, ∑ j, b2z (polB C a (Sum.inr (Sum.inr (Sum.inr i)), j)) * v j =
      sb_pol C 2 sb_slc a (pc v) (Pi.single i 1) := by
    intro i
    rw [sb_pol_expand_e]
    simp only [polB, mk, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sb_b2z_false, zero_mul,
      Finset.sum_const_zero, zero_add, add_zero]
    apply Finset.sum_congr rfl
    intro c _
    rw [sb_b2z_bx, mul_comm]
    congr 1
    unfold sb_pol
    apply Finset.sum_congr rfl
    intro j _
    rw [sb_b2z_and]
    congr 1
    have := congrFun (sb_toZ_PB 2 (unitB c) (unitB i)) j
    rw [sb_toZ_unit, sb_toZ_unit] at this
    exact this
  constructor
  · intro h
    exact ⟨fun i => by rw [← hr]; exact h _, fun i => by rw [← hc]; exact h _⟩
  · rintro ⟨h1, h2⟩ (i | i | i | i)
    · simp [polB, mk]
    · simp [polB, mk]
    · rw [hr]; exact h1 i
    · rw [hc]; exact h2 i

theorem sb_row_upd {k m : ℕ} (t : ℕ) (C : T k m × T k m → Bool) (a : T k m) (x x' : V k)
    (v : T k m → ZMod 2) :
    ∑ j, b2z (C (a, j)) * updZ t x x' v j =
      sb_q t C a v + sb_pol C 1 sb_slr a (pr v) x + sb_pol C 2 sb_slc a (pc v) x' := by
  have hu : ∀ j, updZ t x x' v j = sb_Z0 t v j +
      mk (fun _ => 0) (fun _ => 0) (PZ 1 (pr v) x) (PZ 2 (pc v) x') j := by
    rintro (j | j | j | j)
    · simp [updZ, sb_Z0, mk]
    · simp [updZ, sb_Z0, mk]
    · show FZ 1 (x + pr v) j + FZ 1 x j + rotZ (2 * t) (pd v) j =
        FZ 1 (pr v) j + rotZ (2 * t) (pd v) j + PZ 1 (pr v) x j
      rw [sb_key]; ring
    · show FZ 2 (x' + pc v) j + FZ 2 x' j + rotZ (3 * (t + 1) + 1) (pd v) j =
        FZ 2 (pc v) j + rotZ (3 * (t + 1) + 1) (pd v) j + PZ 2 (pc v) x' j
      rw [sb_key]; ring
  simp only [hu, mul_add, Finset.sum_add_distrib, sb_q, sb_pol]
  rw [add_assoc]
  congr 1
  simp [Fintype.sum_sum_type, mk, sb_slr, sb_slc]

theorem sb_upd_all {k m : ℕ} (t : ℕ) (C : T k m × T k m → Bool) (v : T k m → ZMod 2) :
    (∀ x x', kerB C (updZ t x x' v)) ↔ (∀ a, sb_q t C a v = 0) ∧ kerB (polR C) v := by
  rw [sb_polR_ker]
  constructor
  · intro h
    have hq : ∀ a, sb_q t C a v = 0 := by
      intro a
      have := h 0 0 a
      rw [sb_row_upd, sb_pol_zero, sb_pol_zero] at this
      simpa using this
    refine ⟨hq, fun a => (sb_polB_ker C a v).2 ⟨fun i => ?_, fun i => ?_⟩⟩
    · have := h (Pi.single i 1) 0 a
      rw [sb_row_upd, hq, sb_pol_zero] at this
      simpa using this
    · have := h 0 (Pi.single i 1) a
      rw [sb_row_upd, hq, sb_pol_zero] at this
      simpa using this
  · rintro ⟨hq, hK⟩ x x' a
    obtain ⟨h1, h2⟩ := (sb_polB_ker C a v).1 (hK a)
    rw [sb_row_upd, hq, sb_pol_all _ _ _ _ _ h1 x, sb_pol_all _ _ _ _ _ h2 x']
    simp

theorem sb_bvec_ker {ι : Type} [Fintype ι] [DecidableEq ι] (R : ι × ι → Bool) (hR : sb_RR R)
    (c : ι) : kerB R (toZ (bvec R c)) := by
  intro p
  show ∑ j, b2z (R (p, j)) * b2z (bvec R c j) = 0
  cases hc : R (c, c) with
  | true => simp [bvec, hc]
  | false =>
    cases hp : R (p, p) with
    | false => simp [hR.2 p hp]
    | true =>
      have h1 : ∀ j, b2z (R (p, j)) * b2z (bvec R c j) =
          (if j = c then b2z (R (p, c)) else 0) + (if j = p then b2z (R (p, c)) else 0) := by
        intro j
        simp only [bvec, hc, Bool.not_false, Bool.true_and, sb_b2z_xor, sb_b2z_decide, mul_add]
        congr 1
        · by_cases h : j = c <;> simp [h]
        · cases hj : R (j, j) with
          | false =>
            rw [hR.2 j hj c]
            have : j ≠ p := by
              rintro rfl
              rw [hp] at hj
              cases hj
            simp [this]
          | true =>
            rw [hR.1 j hj p]
            by_cases h : p = j
            · subst h; simp
            · simp [h, Ne.symm h]
      simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact sb_add_self _

theorem sb_ker_decomp {ι : Type} [Fintype ι] [DecidableEq ι] (R : ι × ι → Bool) (hR : sb_RR R)
    (v : ι → ZMod 2) (hv : kerB R v) (j : ι) :
    v j = ∑ c, v c * b2z (bvec R c j) := by
  cases hj : R (j, j) with
  | false =>
    have h1 : ∀ c, v c * b2z (bvec R c j) = if c = j then v j else 0 := by
      intro c
      by_cases h : c = j
      · subst h; simp [bvec, hj]
      · simp [bvec, hR.2 j hj c, h, Ne.symm h]
    simp [h1]
  | true =>
    have h1 : ∀ c, b2z (R (j, c)) * v c =
        (if c = j then v j else 0) + v c * b2z (bvec R c j) := by
      intro c
      cases hc : R (c, c) with
      | true =>
        rw [hR.1 c hc j]
        by_cases h : c = j
        · subst h; simp [bvec, hc]
        · simp [bvec, hc, h, Ne.symm h]
      | false =>
        have h : c ≠ j := by
          rintro rfl
          rw [hj] at hc
          cases hc
        simp [bvec, hc, h, Ne.symm h, mul_comm]
    have h2 := hv j
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    exact sb_eq_of_add _ _ h2

theorem sb_q_add {k m : ℕ} (t : ℕ) (C : T k m × T k m → Bool) (a : T k m)
    (u w : T k m → ZMod 2) (hw : kerB (polR C) w) :
    sb_q t C a (u + w) = sb_q t C a u + sb_q t C a w := by
  have hz : ∀ j, sb_Z0 t (u + w) j = sb_Z0 t u j + updZ t (pr u) (pc u) w j := by
    rintro (j | j | j | j)
    · simp [sb_Z0, updZ, mk, pd]
    · simp [sb_Z0, updZ, mk, py]
    · show FZ 1 (pr u + pr w) j + (rotZ (2 * t) (pd u) j + rotZ (2 * t) (pd w) j) =
        (FZ 1 (pr u) j + rotZ (2 * t) (pd u) j) +
          (FZ 1 (pr u + pr w) j + FZ 1 (pr u) j + rotZ (2 * t) (pd w) j)
      linear_combination (-(FZ 1 (pr u) j)) * sb_two
    · show FZ 2 (pc u + pc w) j + (rotZ (3 * (t + 1) + 1) (pd u) j +
          rotZ (3 * (t + 1) + 1) (pd w) j) =
        (FZ 2 (pc u) j + rotZ (3 * (t + 1) + 1) (pd u) j) +
          (FZ 2 (pc u + pc w) j + FZ 2 (pc u) j + rotZ (3 * (t + 1) + 1) (pd w) j)
      linear_combination (-(FZ 2 (pc u) j)) * sb_two
  obtain ⟨h1, h2⟩ := (sb_polB_ker C a w).1 ((sb_polR_ker C w).1 hw a)
  have e1 : sb_q t C a (u + w) =
      sb_q t C a u + ∑ j, b2z (C (a, j)) * updZ t (pr u) (pc u) w j := by
    unfold sb_q
    simp only [hz, mul_add, Finset.sum_add_distrib]
  rw [e1, sb_row_upd, sb_pol_all _ _ _ _ _ h1, sb_pol_all _ _ _ _ _ h2]
  simp

theorem sb_addK {ι κ : Type} [DecidableEq κ] (K : (ι → ZMod 2) → Prop)
    (q : (ι → ZMod 2) → ZMod 2) (h0 : K 0) (hK : ∀ u w, K u → K w → K (u + w))
    (hq : ∀ u w, K u → K w → q (u + w) = q u + q w) (s : Finset κ) (f : κ → ι → ZMod 2)
    (hf : ∀ c, K (f c)) : K (∑ c ∈ s, f c) ∧ q (∑ c ∈ s, f c) = ∑ c ∈ s, q (f c) := by
  have hq0 : q 0 = 0 := by
    have := hq 0 0 h0 h0
    simpa using this
  induction s using Finset.induction_on with
  | empty => simpa using ⟨h0, hq0⟩
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc]
    exact ⟨hK _ _ (hf c) ih.1, by rw [hq _ _ (hf c) ih.1, ih.2]⟩

theorem sb_ker_zero {ι κ : Type} [Fintype κ] (C : ι × κ → Bool) : kerB C (0 : κ → ZMod 2) := by
  intro a; simp

theorem sb_ker_add {ι κ : Type} [Fintype κ] (C : ι × κ → Bool) (u w : κ → ZMod 2)
    (hu : kerB C u) (hw : kerB C w) : kerB C (u + w) := by
  intro a
  have h1 := hu a
  have h2 := hw a
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]

theorem sb_q_expand {k m : ℕ} (t : ℕ) (C : T k m × T k m → Bool) (a : T k m)
    (v : T k m → ZMod 2) (hv : kerB (polR C) v) :
    sb_q t C a v = ∑ c, b2z (qB t C (polR C) (a, c)) * v c := by
  have hdec : v = ∑ c, (fun j => v c * b2z (bvec (polR C) c j)) := by
    funext j
    rw [Finset.sum_apply]
    exact sb_ker_decomp _ (sb_polR_RR C) v hv j
  have hKf : ∀ c, kerB (polR C) (fun j => v c * b2z (bvec (polR C) c j)) := by
    intro c
    rcases sb_z2 (v c) with h | h
    · rw [h]; intro a; simp
    · rw [h]
      have e : (fun j : T k m => (1 : ZMod 2) * b2z (bvec (polR C) c j)) =
          toZ (bvec (polR C) c) := by
        funext j; simp [toZ]
      rw [e]
      exact sb_bvec_ker (polR C) (sb_polR_RR C) c
  have hsum := (sb_addK (kerB (polR C)) (sb_q t C a) (sb_ker_zero _)
    (fun u w hu hw => sb_ker_add _ u w hu hw)
    (fun u w _ hw => sb_q_add t C a u w hw) Finset.univ _ hKf).2
  rw [← hdec] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro c _
  have hqB : b2z (qB t C (polR C) (a, c)) = sb_q t C a (toZ (bvec (polR C) c)) := by
    unfold qB sb_q
    rw [sb_b2z_bx]
    apply Finset.sum_congr rfl
    intro j _
    rw [sb_b2z_and, ← sb_toZ_ZB]
    rfl
  have hq0 : sb_q t C a 0 = 0 := by
    have := sb_q_add t C a 0 0 (sb_ker_zero _)
    simpa using this
  rcases sb_z2 (v c) with h | h
  · rw [h]
    have e : (fun j : T k m => (0 : ZMod 2) * b2z (bvec (polR C) c j)) = 0 := by
      funext j; simp
    rw [e, hq0]; simp
  · rw [h]
    have e : (fun j : T k m => (1 : ZMod 2) * b2z (bvec (polR C) c j)) =
        toZ (bvec (polR C) c) := by
      funext j; simp [toZ]
    rw [e, hqB]; simp

theorem sb_tick_ker {k m : ℕ} (t : ℕ) (C : T k m × T k m → Bool) (v : T k m → ZMod 2) :
    kerB (tick t C) v ↔ ∀ x x', kerB C (updZ t x x' v) := by
  rw [sb_upd_all]
  unfold tick
  rw [sb_absorb_ker]
  constructor
  · rintro ⟨hK, hQ⟩
    exact ⟨fun a => by rw [sb_q_expand t C a v hK]; exact hQ a, hK⟩
  · rintro ⟨hq, hK⟩
    exact ⟨hK, fun a => by
      have := hq a
      rw [sb_q_expand t C a v hK] at this
      exact this⟩

theorem sb_term {k m : ℕ} (A B : Fin m × Fin k → Bool) (v : T k m → ZMod 2) :
    termOk A B v ↔ kerB (termB A B) v := by
  have h : ∀ j : Fin m, ∑ c, b2z (termB A B (Sum.inr (Sum.inl j), c)) * v c =
      ∑ i, b2z (A (j, i)) * pr v i + ∑ i, b2z (B (j, i)) * pc v i + py v j := by
    intro j
    simp [termB, mk, Fintype.sum_sum_type, sb_b2z_decide, pr, pc, py]
    ring
  constructor
  · rintro h1 (a | a | a | a)
    · simp [termB]
    · rw [h]; exact h1 a
    · simp [termB]
    · simp [termB]
  · intro h1 j
    rw [← h]; exact h1 _

theorem sb_okrem {k m : ℕ} (A B : Fin m × Fin k → Bool) (s : ℕ) :
    ∀ (t : ℕ) (v : T k m → ZMod 2), OkRem A B s t v ↔
      kerB ((List.range' t s).foldr (fun t C => tick t C) (termB A B)) v := by
  induction s with
  | zero => intro t v; simpa [OkRem] using sb_term A B v
  | succ s ih =>
    intro t v
    rw [List.range'_succ, List.foldr_cons, sb_tick_ker]
    show (∀ x x' : V k, OkRem A B s (t + 1) (updZ t x x' v)) ↔ _
    constructor
    · intro h x x'; exact (ih _ _).1 (h x x')
    · intro h x x'; exact (ih _ _).2 (h x x')

theorem okrem_iff_ker {k m : ℕ} (r : ℕ) (A B : Fin m × Fin k → Bool) (v : T k m → ZMod 2) :
    OkRem A B r 0 v ↔ kerB (backC r A B) v := by
  unfold backC
  rw [List.range_eq_range']
  exact sb_okrem A B r 0 v

abbrev sd_S (k : ℕ) : Type := (Fin (k + 1) ⊕ Unit) ⊕ (Fin k ⊕ Unit)

def sd_step {k : ℕ} (p : Fin k) (v : sd_S k → Bool) : sd_S k → Bool :=
  Sum.elim (Sum.elim
      (fun i => if v (Sum.inr (Sum.inl p)) then
          (if h : i.val + 1 < k + 1 then v (Sum.inl (Sum.inl ⟨i.val + 1, h⟩)) else false)
        else v (Sum.inl (Sum.inl i)))
      (fun _ => if v (Sum.inr (Sum.inl p)) then
          (v (Sum.inl (Sum.inr ())) || v (Sum.inl (Sum.inl 0)))
        else v (Sum.inl (Sum.inr ()))))
    (fun q => v (Sum.inr q))

def sd_init {k : ℕ} (v : Fin (k + 1) ⊕ (Fin k ⊕ Unit) → Bool) : sd_S k → Bool :=
  Sum.elim (Sum.elim (fun i => v (Sum.inl i)) (fun _ => false)) (fun q => v (Sum.inr q))

def sd_out {k : ℕ} (v : sd_S k → Bool) : Bool :=
  (!decide (∃ i : Fin (k + 1), (decide (i ≠ 0) && v (Sum.inl (Sum.inl i))) = true)) &&
    ((!v (Sum.inl (Sum.inl 0)) && (v (Sum.inr (Sum.inr ())) || !v (Sum.inl (Sum.inr ())))) ||
     ((v (Sum.inr (Sum.inr ())) && v (Sum.inl (Sum.inl 0))) && !v (Sum.inl (Sum.inr ()))))

theorem sd_stepbit {k : ℕ} (p : Fin k) (j : sd_S k) :
    Cb (sd_S k) 5 (fun v => sd_step p v j) := by
  rcases j with (i | u) | q
  · by_cases h : i.val + 1 < k + 1
    · have := Cb.mux (Cb.var (ι := sd_S k) (Sum.inr (Sum.inl p)))
        (Cb.var (ι := sd_S k) (Sum.inl (Sum.inl ⟨i.val + 1, h⟩)))
        (Cb.var (ι := sd_S k) (Sum.inl (Sum.inl i)))
      exact (this.mono (by omega)).congr (fun v => by
        simp only [sd_step, Sum.elim_inl, dif_pos h])
    · have := Cb.mux (Cb.var (ι := sd_S k) (Sum.inr (Sum.inl p)))
        (Cb.const (ι := sd_S k) false)
        (Cb.var (ι := sd_S k) (Sum.inl (Sum.inl i)))
      exact (this.mono (by omega)).congr (fun v => by
        simp only [sd_step, Sum.elim_inl, dif_neg h])
  · have := Cb.mux (Cb.var (ι := sd_S k) (Sum.inr (Sum.inl p)))
      (Cb.or (Cb.var (ι := sd_S k) (Sum.inl (Sum.inr ())))
        (Cb.var (ι := sd_S k) (Sum.inl (Sum.inl 0))))
      (Cb.var (ι := sd_S k) (Sum.inl (Sum.inr ())))
    exact (this.mono (by omega)).congr (fun v => by simp [sd_step])
  · have := Cb.var (ι := sd_S k) (Sum.inr q)
    exact (this.mono (by omega)).congr (fun v => by simp [sd_step])

theorem sd_initbit {k : ℕ} (j : sd_S k) :
    Cb (Fin (k + 1) ⊕ (Fin k ⊕ Unit)) 1 (fun v => sd_init v j) := by
  rcases j with (i | u) | q
  · exact ((Cb.var (Sum.inl i)).mono (by omega)).congr (fun v => by simp [sd_init])
  · exact (Cb.const false).congr (fun v => by simp [sd_init])
  · exact ((Cb.var (Sum.inr q)).mono (by omega)).congr (fun v => by simp [sd_init])

theorem sd_outcb (k : ℕ) : Cb (sd_S k) ((k + 1) * 3 + 12) (sd_out (k := k)) := by
  have hb : ∀ i : Fin (k + 1), Cb (sd_S k) 2
      (fun v => decide (i ≠ 0) && v (Sum.inl (Sum.inl i))) := fun i =>
    (Cb.and (Cb.const (decide (i ≠ 0))) (Cb.var (ι := sd_S k) (Sum.inl (Sum.inl i)))).mono
      (by omega)
  have hz := Cb.not (Cb.bigOr hb)
  have b0 := Cb.var (ι := sd_S k) (Sum.inl (Sum.inl 0))
  have c := Cb.var (ι := sd_S k) (Sum.inr (Sum.inr ()))
  have s := Cb.var (ι := sd_S k) (Sum.inl (Sum.inr ()))
  have hx := Cb.and (Cb.not b0) (Cb.or c (Cb.not s))
  have hy := Cb.and (Cb.and c b0) (Cb.not s)
  have := Cb.and hz (Cb.or hx hy)
  refine (this.mono ?_).congr (fun v => by unfold sd_out; congr)
  simp only [Fintype.card_fin]
  omega

theorem sd_natOf_split {n : ℕ} (w : Fin (n + 1) → Bool) :
    natOf w = (if w 0 then 1 else 0) + 2 * natOf (fun i : Fin n => w i.succ) := by
  have e : ∀ i : Fin n, (if w i.succ = true then 2 ^ (i.succ.val) else 0) =
      2 * (if w i.succ = true then 2 ^ i.val else 0) := by
    intro i
    by_cases h : w i.succ = true
    · simp [h, pow_succ, Nat.mul_comm]
    · simp [h]
  unfold natOf
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [e]
  simp

theorem sd_natOf_shift {n : ℕ} (w : Fin (n + 1) → Bool) :
    natOf (fun i : Fin (n + 1) => if h : i.val + 1 < n + 1 then w ⟨i.val + 1, h⟩ else false) =
      natOf (fun i : Fin n => w i.succ) := by
  unfold natOf
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, dite_false, Bool.false_eq_true, if_false,
    Nat.add_zero]
  apply Finset.sum_congr rfl
  intro i _
  have h : (i.castSucc : Fin (n + 1)).val + 1 < n + 1 := by simp
  simp only [dif_pos h]
  rfl

theorem sd_natOf_zero {n : ℕ} (w : Fin n → Bool) : natOf w = 0 ↔ ∀ i, w i = false := by
  unfold natOf
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h i
    have := h i (Finset.mem_univ i)
    by_contra hc
    simp at hc
    simp [hc] at this
  · intro h i _
    simp [h i]

def sd_Inv {k : ℕ} (N : ℕ) (fr : Fin k → Bool) (c : Bool) (f : ℕ) (v : sd_S k → Bool) : Prop :=
  (∀ q, v (Sum.inr (Sum.inl q)) = fr q) ∧ v (Sum.inr (Sum.inr ())) = c ∧
    ∃ low, N = natOf (fun i => v (Sum.inl (Sum.inl i))) * 2 ^ f + low ∧ low < 2 ^ f ∧
      (v (Sum.inl (Sum.inr ())) = true ↔ low ≠ 0)

theorem sd_Inv_step {k : ℕ} (N : ℕ) (fr : Fin k → Bool) (c : Bool) (f : ℕ) (v : sd_S k → Bool)
    (p : Fin k) (h : sd_Inv N fr c f v) :
    sd_Inv N fr c (f + if fr p then 1 else 0) (sd_step p v) := by
  obtain ⟨h1, h2, low, h3, h4, h5⟩ := h
  have hp := h1 p
  cases hfp : fr p with
  | false =>
    rw [hfp] at hp
    rw [if_neg Bool.false_ne_true, Nat.add_zero]
    refine ⟨fun q => by simpa [sd_step] using h1 q, by simpa [sd_step] using h2, low, ?_, ?_, ?_⟩
    · simpa [sd_step, hp] using h3
    · simpa using h4
    · simpa [sd_step, hp] using h5
  | true =>
    rw [hfp] at hp
    rw [if_pos rfl]
    have e : (fun i : Fin (k + 1) => sd_step p v (Sum.inl (Sum.inl i))) =
        (fun i : Fin (k + 1) => if h : i.val + 1 < k + 1 then
          (fun i => v (Sum.inl (Sum.inl i))) ⟨i.val + 1, h⟩ else false) := by
      funext i
      simp [sd_step, hp]
    have hs := sd_natOf_split (fun i : Fin (k + 1) => v (Sum.inl (Sum.inl i)))
    have hpow : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [pow_succ]; ring
    refine ⟨fun q => by simpa [sd_step] using h1 q, by simpa [sd_step] using h2,
      (if v (Sum.inl (Sum.inl 0)) then 1 else 0) * 2 ^ f + low, ?_, ?_, ?_⟩
    · rw [e, sd_natOf_shift (fun i : Fin (k + 1) => v (Sum.inl (Sum.inl i))), h3, hs, hpow]
      ring
    · rw [hpow]
      cases hb : v (Sum.inl (Sum.inl 0)) <;> simp <;> omega
    · have hpos : 0 < 2 ^ f := Nat.two_pow_pos f
      cases hb : v (Sum.inl (Sum.inl 0)) with
      | true =>
        have : 2 ^ f + low ≠ 0 := by omega
        simp [sd_step, hp, hb, this]
      | false =>
        simp [sd_step, hp, hb, h5]

theorem sd_Inv_fold {k : ℕ} (N : ℕ) (fr : Fin k → Bool) (c : Bool) (L : List (Fin k)) :
    ∀ (f : ℕ) (v : sd_S k → Bool), sd_Inv N fr c f v →
      sd_Inv N fr c (f + L.countP (fun p => fr p)) (L.foldl (fun acc p => sd_step p acc) v) := by
  induction L with
  | nil => intro f v h; simpa using h
  | cons p L ih =>
    intro f v h
    have := ih _ _ (sd_Inv_step N fr c f v p h)
    rw [List.foldl_cons, List.countP_cons]
    have e : f + (List.countP (fun p => fr p) L + if fr p = true then 1 else 0) =
        f + (if fr p = true then 1 else 0) + List.countP (fun p => fr p) L := by omega
    rw [e]
    exact this

theorem sd_Inv_out {k : ℕ} (N : ℕ) (fr : Fin k → Bool) (c : Bool) (F : ℕ) (v : sd_S k → Bool)
    (h : sd_Inv N fr c F v) : sd_out v = decide (N ≤ if c then 2 ^ F else 0) := by
  obtain ⟨_, h2, low, h3, h4, h5⟩ := h
  have hs := sd_natOf_split (fun i : Fin (k + 1) => v (Sum.inl (Sum.inl i)))
  have hz := sd_natOf_zero (fun i : Fin k => v (Sum.inl (Sum.inl i.succ)))
  have hpos : 0 < 2 ^ F := Nat.two_pow_pos F
  have hex : (∃ i : Fin (k + 1), (decide (i ≠ 0) && v (Sum.inl (Sum.inl i))) = true) ↔
      ¬ natOf (fun i : Fin k => v (Sum.inl (Sum.inl i.succ))) = 0 := by
    rw [hz]
    constructor
    · rintro ⟨i, hi⟩ hall
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi.1
      rw [hall j] at hi
      exact Bool.false_ne_true hi.2
    · intro hn
      rw [not_forall] at hn
      obtain ⟨j, hj⟩ := hn
      refine ⟨j.succ, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Fin.succ_ne_zero j, by simpa using hj⟩
  have hd : ∀ inst : Decidable (∃ i : Fin (k + 1),
      (decide (i ≠ 0) && v (Sum.inl (Sum.inl i))) = true),
      @decide _ inst = decide (¬ natOf (fun i : Fin k => v (Sum.inl (Sum.inl i.succ))) = 0) := by
    intro inst
    simp only [decide_eq_decide]
    exact hex
  unfold sd_out
  rw [hd, h2]
  generalize natOf (fun i : Fin k => v (Sum.inl (Sum.inl i.succ))) = t at hs
  generalize natOf (fun i : Fin (k + 1) => v (Sum.inl (Sum.inl i))) = U at hs h3
  have hmul : ∀ a : ℕ, 2 ≤ a → 2 * 2 ^ F ≤ a * 2 ^ F := fun a ha => Nat.mul_le_mul_right _ ha
  have hlow : (v (Sum.inl (Sum.inr ())) = false → low = 0) ∧
      (v (Sum.inl (Sum.inr ())) = true → low ≠ 0) := by
    refine ⟨fun hf => ?_, fun ht => h5.1 ht⟩
    by_contra hl
    rw [h5.2 hl] at hf
    exact Bool.noConfusion hf
  clear h5
  by_cases ht : t = 0
  · subst ht
    cases hb : v (Sum.inl (Sum.inl 0)) with
    | false =>
      rw [hb] at hs
      simp only [Bool.false_eq_true, if_false] at hs
      have hU : U = 0 := by omega
      subst hU
      simp only [Nat.zero_mul, Nat.zero_add] at h3
      cases c with
      | true =>
        have hr : N ≤ 2 ^ F := by omega
        simp [hr]
      | false =>
        cases hsb : v (Sum.inl (Sum.inr ())) with
        | false =>
          have := hlow.1 hsb
          have hr : N = 0 := by omega
          simp [hr]
        | true =>
          have := hlow.2 hsb
          have hr : ¬ N = 0 := by omega
          simp [hr]
    | true =>
      rw [hb] at hs
      simp only [if_true] at hs
      have hU : U = 1 := by omega
      subst hU
      simp only [Nat.one_mul] at h3
      cases c with
      | true =>
        cases hsb : v (Sum.inl (Sum.inr ())) with
        | false =>
          have := hlow.1 hsb
          have hr : N ≤ 2 ^ F := by omega
          simp [hr]
        | true =>
          have := hlow.2 hsb
          have hr : ¬ N ≤ 2 ^ F := by omega
          simp [hr]
      | false =>
        have hr : ¬ N = 0 := by omega
        simp [hr]
  · have hU : 2 ≤ U := by
      cases hb : v (Sum.inl (Sum.inl 0)) <;> rw [hb] at hs <;> simp at hs <;> omega
    have := hmul U hU
    cases c with
    | true =>
      have hr : ¬ N ≤ 2 ^ F := by omega
      simp [ht, hr]
    | false =>
      have hr : ¬ N = 0 := by omega
      simp [ht, hr]

theorem sd_card_countP {k : ℕ} (fr : Fin k → Bool) :
    (Finset.univ.filter (fun p => fr p = true)).card =
      (List.finRange k).countP (fun p => fr p) := by
  have e : (Finset.univ.filter (fun p : Fin k => fr p = true)) =
      ((List.finRange k).filter (fun p => fr p)).toFinset := by
    ext p; simp
  rw [e, List.toFinset_card_of_nodup ((List.nodup_finRange k).filter _),
    List.countP_eq_length_filter]

theorem cmp_cmpB (k : ℕ) : Cb (Fin (k + 1) ⊕ (Fin k ⊕ Unit)) (64 * (k + 2) ^ 2)
    (fun v => cmpB (fun i => v (Sum.inl i)) (fun p => v (Sum.inr (Sum.inl p)))
      (v (Sum.inr (Sum.inr ())))) := by
  have h1 : Cmp (Fin (k + 1) ⊕ (Fin k ⊕ Unit)) (sd_S k) (Fintype.card (sd_S k) * 1)
      (sd_init (k := k)) := Cmp.ofBits (fun j => sd_initbit j)
  have h2 := Cmp.foldl (ι := sd_S k) (s := Fintype.card (sd_S k) * 5) (List.finRange k)
    (fun p v => sd_step p v) (fun p _ => Cmp.ofBits (fun j => sd_stepbit p j))
  have h3 : Cb (sd_S k) ((k + 1) * 3 + 12) (sd_out (k := k)) := sd_outcb k
  have h := Cmp.comp (Cmp.comp h1 h2) h3
  refine (Cmp.mono h ?_).congr ?_
  · simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit, List.length_finRange]
    nlinarith [sq_nonneg k]
  · intro v _
    have h0 : sd_Inv (natOf (fun i : Fin (k + 1) => v (Sum.inl i)))
        (fun p => v (Sum.inr (Sum.inl p))) (v (Sum.inr (Sum.inr ()))) 0 (sd_init v) := by
      refine ⟨fun q => by simp [sd_init], by simp [sd_init], 0, ?_, by simp, ?_⟩
      · simp [sd_init]
      · simp [sd_init]
    have hf := sd_Inv_fold _ _ _ (List.finRange k) 0 _ h0
    have ho := sd_Inv_out _ _ _ _ _ hf
    show sd_out _ = cmpB _ _ _
    rw [ho]
    unfold cmpB
    rw [sd_card_countP, Nat.zero_add]

theorem sd_bound {i n j L : ℕ} (hi : i < n) (hj : j < L) : i * L + j < n * L := by
  have h1 : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right L hi
  have h2 : (i + 1) * L = i * L + L := by ring
  omega

theorem sd_flat {α β : Type} (d : α) (blk : β → List α) (L : ℕ) :
    ∀ (l : List β), (∀ x ∈ l, (blk x).length = L) →
      (l.flatMap blk).length = l.length * L ∧
      ∀ (i : ℕ) (hi : i < l.length) (j : ℕ), j < L →
        (l.flatMap blk).getD (i * L + j) d = (blk l[i]).getD j d := by
  intro l
  induction l with
  | nil => intro _; refine ⟨by simp, ?_⟩; intro i hi; simp at hi
  | cons x l ih =>
    intro h
    have hx : (blk x).length = L := h x (by simp)
    obtain ⟨ih1, ih2⟩ := ih (fun y hy => h y (by simp [hy]))
    refine ⟨?_, ?_⟩
    · rw [List.flatMap_cons, List.length_append, ih1, hx, List.length_cons]; ring
    · intro i hi j hj
      rw [List.flatMap_cons]
      cases i with
      | zero =>
        simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega)]
      | succ i =>
        have e : (i + 1) * L + j = (blk x).length + (i * L + j) := by rw [hx]; ring
        rw [List.getD_eq_getElem?_getD, e, List.getElem?_append_right (by omega),
          Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
        simp only [List.getElem_cons_succ]
        exact ih2 i (by simpa using hi) j hj

theorem sd_fin {α : Type} (d : α) (n L : ℕ) (blk : Fin n → List α)
    (h : ∀ i, (blk i).length = L) :
    ((List.finRange n).flatMap blk).length = n * L ∧
    ∀ (i : Fin n) (j : ℕ), j < L →
      ((List.finRange n).flatMap blk).getD (i.val * L + j) d = (blk i).getD j d := by
  obtain ⟨h1, h2⟩ := sd_flat d blk L (List.finRange n) (fun x _ => h x)
  refine ⟨by simpa using h1, ?_⟩
  intro i j hj
  have := h2 i.val (by simp) j hj
  simpa using this

theorem sd_getD_left {α : Type} (d : α) (A B : List α) (k : ℕ) (hk : k < A.length) :
    (A ++ B).getD k d = A.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem sd_getD_right {α : Type} (d : α) (A B : List α) (n k : ℕ) (hn : A.length = n) :
    (A ++ B).getD (n + k) d = B.getD k d := by
  subst hn
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem sd_getD_range (n : ℕ) (f : ℕ → Bool) (i : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i false = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem sd_layout (k m : ℕ) (LA LB Ly Lp Lv Lt : List Bool)
    (hA : LA.length = m * k) (hB : LB.length = m * k) (hy : Ly.length = m)
    (hp : Lp.length = k) (hv : Lv.length = k) (ht : Lt.length = k + 1) :
    (LA ++ LB ++ Ly ++ Lp ++ Lv ++ Lt).length = m * k + m * k + m + k + k + (k + 1) ∧
    (∀ a, a < m * k → (LA ++ LB ++ Ly ++ Lp ++ Lv ++ Lt).getD a false = LA.getD a false) ∧
    (∀ a, a < m * k →
      (LA ++ LB ++ Ly ++ Lp ++ Lv ++ Lt).getD (m * k + a) false = LB.getD a false) ∧
    (∀ a, a < m →
      (LA ++ LB ++ Ly ++ Lp ++ Lv ++ Lt).getD (m * k + m * k + a) false = Ly.getD a false) ∧
    (∀ a, a < k →
      (LA ++ LB ++ Ly ++ Lp ++ Lv ++ Lt).getD (m * k + m * k + m + a) false =
        Lp.getD a false) ∧
    (∀ a, a < k →
      (LA ++ LB ++ Ly ++ Lp ++ Lv ++ Lt).getD (m * k + m * k + m + k + a) false =
        Lv.getD a false) ∧
    (∀ a, a < k + 1 →
      (LA ++ LB ++ Ly ++ Lp ++ Lv ++ Lt).getD (m * k + m * k + m + k + k + a) false =
        Lt.getD a false) := by
  have l2 : (LA ++ LB).length = m * k + m * k := by rw [List.length_append, hA, hB]
  have l3 : (LA ++ LB ++ Ly).length = m * k + m * k + m := by rw [List.length_append, l2, hy]
  have l4 : (LA ++ LB ++ Ly ++ Lp).length = m * k + m * k + m + k := by
    rw [List.length_append, l3, hp]
  have l5 : (LA ++ LB ++ Ly ++ Lp ++ Lv).length = m * k + m * k + m + k + k := by
    rw [List.length_append, l4, hv]
  refine ⟨by rw [List.length_append, l5, ht], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [sd_getD_left _ _ _ _ (by omega), sd_getD_left _ _ _ _ (by omega),
      sd_getD_left _ _ _ _ (by omega), sd_getD_left _ _ _ _ (by omega),
      sd_getD_left _ _ _ _ (by omega)]
  · intro a ha
    rw [sd_getD_left _ _ _ _ (by omega), sd_getD_left _ _ _ _ (by omega),
      sd_getD_left _ _ _ _ (by omega), sd_getD_left _ _ _ _ (by omega),
      sd_getD_right _ _ _ _ _ hA]
  · intro a ha
    rw [sd_getD_left _ _ _ _ (by omega), sd_getD_left _ _ _ _ (by omega),
      sd_getD_left _ _ _ _ (by omega), sd_getD_right _ _ _ _ _ l2]
  · intro a ha
    rw [sd_getD_left _ _ _ _ (by omega), sd_getD_left _ _ _ _ (by omega),
      sd_getD_right _ _ _ _ _ l3]
  · intro a ha
    rw [sd_getD_left _ _ _ _ (by omega), sd_getD_right _ _ _ _ _ l4]
  · intro a ha
    rw [sd_getD_right _ _ _ _ _ l5]

theorem assemble (k r m S : ℕ) (hc : Cb (In0 k m) S (top (k := k) (m := m) r))
    (hS : S + 1 ≤ 2 ^ 20 * (r + 1) * (k + m + 1) ^ 8) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*m*k+m+2*k+(k+1)) C ∧
      C.size ≤ 2^20 * (r+1) * (k+m+1)^8 ∧
      ∀ (A B : Fin m → Fin (2^k)) (y : Fin m → Bool) (pin value : Fin (2^k)) (t : Fin (2^(k+1))),
        C.eval ((List.finRange m).flatMap (fun j => (List.range k).map (fun i => (A j).val.testBit i)) ++
          (List.finRange m).flatMap (fun j => (List.range k).map (fun i => (B j).val.testBit i)) ++
          List.ofFn y ++ (List.range k).map (fun i => pin.val.testBit i) ++
          (List.range k).map (fun i => value.val.testBit i) ++
          (List.range (k+1)).map (fun i => t.val.testBit i)) = top r (inpOf A B y pin value t) := by
  have hn : 2*m*k+m+2*k+(k+1) = m * k + m * k + m + k + k + (k + 1) := by ring
  rw [hn]
  have hws : ∀ j : In0 k m,
      (Sum.elim (fun p : Fin m × Fin k => p.1.val * k + p.2.val)
        (Sum.elim (fun p : Fin m × Fin k => m * k + (p.1.val * k + p.2.val))
          (Sum.elim (fun j : Fin m => m * k + m * k + j.val)
            (Sum.elim (fun i : Fin k => m * k + m * k + m + i.val)
              (Sum.elim (fun i : Fin k => m * k + m * k + m + k + i.val)
                (fun i : Fin (k + 1) => m * k + m * k + m + k + k + i.val))))) j) <
        m * k + m * k + m + k + k + (k + 1) := by
    intro j
    rcases j with p | p | j | i | i | i
    · have := sd_bound p.1.isLt p.2.isLt
      simp only [Sum.elim_inl]; omega
    · have := sd_bound p.1.isLt p.2.isLt
      simp only [Sum.elim_inl, Sum.elim_inr]; omega
    · have := j.isLt
      simp only [Sum.elim_inl, Sum.elim_inr]; omega
    · have := i.isLt
      simp only [Sum.elim_inl, Sum.elim_inr]; omega
    · have := i.isLt
      simp only [Sum.elim_inl, Sum.elim_inr]; omega
    · have := i.isLt
      simp only [Sum.elim_inr]; omega
  obtain ⟨gs, outs, hfan, hrb, hsize, hout, hsem⟩ :=
    Cmp.extract hc (m * k + m * k + m + k + k + (k + 1)) _ (fun j => Nat.lt_succ_of_lt (hws j))
  refine ⟨⟨gs, outs ()⟩, hfan, hrb _, le_trans hsize hS, ?_⟩
  intro A B y pin value t
  have fA := sd_fin false m k (fun j => (List.range k).map (fun i => (A j).val.testBit i))
    (fun j => by simp)
  have fB := sd_fin false m k (fun j => (List.range k).map (fun i => (B j).val.testBit i))
    (fun j => by simp)
  obtain ⟨hlen, g1, g2, g3, g4, g5, g6⟩ := sd_layout k m
    ((List.finRange m).flatMap (fun j => (List.range k).map (fun i => (A j).val.testBit i)))
    ((List.finRange m).flatMap (fun j => (List.range k).map (fun i => (B j).val.testBit i)))
    (List.ofFn y) ((List.range k).map (fun i => pin.val.testBit i))
    ((List.range k).map (fun i => value.val.testBit i))
    ((List.range (k+1)).map (fun i => t.val.testBit i))
    fA.1 fB.1 (by simp) (by simp) (by simp) (by simp)
  have e := hsem (outs ()) _ hlen ()
  show (PEqualNP.CircuitLowerBounds.Circuit.wires _ _).getD (outs ()) false = _
  rw [e]
  congr 1
  funext j
  rw [sd_getD_left _ _ _ _ (by rw [hlen]; exact hws j)]
  rcases j with p | p | j | i | i | i
  · simp only [Sum.elim_inl, inpOf]
    rw [g1 _ (sd_bound p.1.isLt p.2.isLt), fA.2 p.1 p.2.val p.2.isLt,
      sd_getD_range _ _ _ p.2.isLt]
  · simp only [Sum.elim_inl, Sum.elim_inr, inpOf]
    rw [g2 _ (sd_bound p.1.isLt p.2.isLt), fB.2 p.1 p.2.val p.2.isLt,
      sd_getD_range _ _ _ p.2.isLt]
  · simp only [Sum.elim_inl, Sum.elim_inr, inpOf]
    rw [g3 _ j.isLt]
    simp [List.getD_eq_getElem?_getD]
  · simp only [Sum.elim_inl, Sum.elim_inr, inpOf]
    rw [g4 _ i.isLt, sd_getD_range _ _ _ i.isLt]
  · simp only [Sum.elim_inl, Sum.elim_inr, inpOf]
    rw [g5 _ i.isLt, sd_getD_range _ _ _ i.isLt]
  · simp only [Sum.elim_inr, inpOf]
    rw [g6 _ i.isLt, sd_getD_range _ _ _ i.isLt]

theorem fd_ctl {D : ℕ} {τ : Type} (e : Bool × Fin D × Fin D) :
    Cb ((Fin D × Fin D) ⊕ τ) 6 (fun v => gjCtl e (fun p => v (Sum.inl p))) := by
  rcases e with ⟨k, p, i⟩
  cases k
  · have h := Cb.and (Cb.and (Cb.or (Cb.const (ι := (Fin D × Fin D) ⊕ τ) (decide (p < i)))
        (Cb.not (Cb.var (Sum.inl (i, i))))) (Cb.var (Sum.inl (i, p))))
        (Cb.not (Cb.var (Sum.inl (p, p))))
    refine Cb.mono (Cb.congr h ?_) (by norm_num)
    intro v
    simp [gjCtl]
  · have h := Cb.and (Cb.var (ι := (Fin D × Fin D) ⊕ τ) (Sum.inl (i, p)))
        (Cb.var (Sum.inl (p, p)))
    refine Cb.mono (Cb.congr h ?_) (by norm_num)
    intro v
    simp [gjCtl]

theorem fd_bit {D : ℕ} {τ : Type} (e : Bool × Fin D × Fin D) (p : Fin D × Fin D) :
    Cb ((Fin D × Fin D) ⊕ τ) 11 (fun v => gjStep e (fun p => v (Sum.inl p)) p) := by
  by_cases h : p.1 = gjT e
  · have hh := Cb.xor (Cb.var (ι := (Fin D × Fin D) ⊕ τ) (Sum.inl p))
        (Cb.and (fd_ctl (τ := τ) e) (Cb.var (Sum.inl (gjS e, p.2))))
    refine Cb.mono (Cb.congr hh ?_) (by norm_num)
    intro v
    simp [gjStep, rowAdd, h]
  · refine Cb.mono (Cb.congr (Cb.var (Sum.inl p)) ?_) (by norm_num)
    intro v
    simp [gjStep, rowAdd, h]

theorem fd_flatMap_len {α β : Type} (c : ℕ) (f : α → List β) (hf : ∀ x, (f x).length ≤ c) :
    ∀ L : List α, (L.flatMap f).length ≤ L.length * c := by
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := hf x
    omega

theorem fd_sched_len (D : ℕ) : (sched D).length ≤ 2 * (D * D) := by
  have h := fd_flatMap_len (2 * D) (fun p : Fin D =>
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (false, p, i)) ++
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (true, p, i))) (by
      intro p
      have h1 : ((List.finRange D).filter (fun i => decide (i ≠ p))).length ≤ D := by
        have := List.length_filter_le (fun i => decide (i ≠ p)) (List.finRange D)
        simpa using this
      simp only [List.length_append, List.length_map]
      omega) (List.finRange D)
  have h2 : (List.finRange D).length = D := List.length_finRange
  rw [h2] at h
  have h3 : D * (2 * D) = 2 * (D * D) := by ring
  rw [h3] at h
  exact h

def gjCost (D : ℕ) : ℕ := 32 * (D + 1) ^ 4

theorem fz2_gjbit {D : ℕ} (e : Bool × Fin D × Fin D) (p : Fin D × Fin D) :
    Cb (Fin D × Fin D) 11 (fun M => gjStep e M p) := by
  have h := Cmp.sel (ι := Fin D × Fin D)
    (fun j : (Fin D × Fin D) ⊕ Empty => Sum.elim id (fun x => x.elim) j)
    (fd_bit (τ := Empty) e p)
  exact h

theorem cmp_gj (D : ℕ) : Cmp (Fin D × Fin D) (Fin D × Fin D) (gjCost D) (gj D) := by
  have h := Cmp.foldl (ι := Fin D × Fin D) (s := Fintype.card (Fin D × Fin D) * 11) (sched D)
    (fun e M => gjStep e M) (fun e _ => Cmp.ofBits (fun p => fz2_gjbit e p))
  refine Cmp.mono h ?_
  have h1 := fd_sched_len D
  have h2 : Fintype.card (Fin D × Fin D) = D * D := by simp
  rw [h2]
  unfold gjCost
  have h3 : D ^ 4 ≤ (D + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h4 : 2 * (D * D) * (D * D * 11) = 22 * D ^ 4 := by ring
  calc (sched D).length * (D * D * 11) ≤ 2 * (D * D) * (D * D * 11) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ 32 * (D + 1) ^ 4 := by omega

theorem ca_rref (ι : Type) [Fintype ι] :
    Cmp (ι × ι) (ι × ι) (gjCost (Fintype.card ι)) (fun M => rref M) := by
  have h1 : Cmp (ι × ι) (Fin (Fintype.card ι) × Fin (Fintype.card ι)) 0
      (fun v q => v ((Fintype.equivFin ι).symm q.1, (Fintype.equivFin ι).symm q.2)) :=
    Cmp.wire _
  have h2 := Cmp.comp (Cmp.comp h1 (cmp_gj (Fintype.card ι)))
    (Cmp.wire (fun p : ι × ι => (Fintype.equivFin ι p.1, Fintype.equivFin ι p.2)))
  refine Cmp.mono (Cmp.congr h2 ?_) (by omega)
  intro v k
  rfl

def ca_absC (N : ℕ) : ℕ := (N + N) * (N + N) + gjCost (N + N)

theorem ca_stack_bit (ι : Type) (p : (ι ⊕ ι) × (ι ⊕ ι)) :
    Cb ((ι × ι) ⊕ (ι × ι)) 1
      (fun v => stack (fun q => v (Sum.inl q)) (fun q => v (Sum.inr q)) p) := by
  rcases p with ⟨i | i, j | j⟩
  · exact Cb.mono (Cb.var (Sum.inl (i, j))) (by omega)
  · exact Cb.const false
  · exact Cb.mono (Cb.var (Sum.inr (i, j))) (by omega)
  · exact Cb.const false

theorem ca_absorb (ι : Type) [Fintype ι] :
    Cmp ((ι × ι) ⊕ (ι × ι)) (ι × ι) (ca_absC (Fintype.card ι))
      (fun v => absorb (fun q => v (Sum.inl q)) (fun q => v (Sum.inr q))) := by
  have h1 := Cmp.ofBits
    (F := fun (v : (ι × ι) ⊕ (ι × ι) → Bool) p =>
      stack (fun q => v (Sum.inl q)) (fun q => v (Sum.inr q)) p)
    (fun p => ca_stack_bit ι p)
  have h2 := Cmp.comp (Cmp.comp h1 (ca_rref (ι ⊕ ι)))
    (Cmp.wire (fun p : ι × ι => ((Sum.inl p.1 : ι ⊕ ι), (Sum.inl p.2 : ι ⊕ ι))))
  refine Cmp.mono (Cmp.congr h2 ?_) ?_
  · intro v k
    rfl
  · simp [ca_absC, Fintype.card_sum, Fintype.card_prod]

theorem ca_mix {ι : Type} {k s : ℕ} (g : ℕ) (X : (ι → Bool) → Fin k → Bool)
    (hX : ∀ i, Cb ι s (fun v => X v i)) (i : Fin k) :
    Cb ι (3 * s + 8) (fun v => mixB g (X v) i) := by
  have h := Cb.xor (Cb.xor (hX i) (hX (ix i (k - g % k)))) (hX (ix i (k - (k - g) % k)))
  refine Cb.mono (Cb.congr h ?_) (by omega)
  intro v
  rfl

theorem ca_chi {ι : Type} {k s : ℕ} (Y : (ι → Bool) → Fin k → Bool)
    (hY : ∀ i, Cb ι s (fun v => Y v i)) (i : Fin k) :
    Cb ι (3 * s + 6) (fun v => chiB (Y v) i) := by
  have h := Cb.xor (hY i) (Cb.and (Cb.not (hY (ix i 1))) (hY (ix i 2)))
  refine Cb.mono (Cb.congr h ?_) (by omega)
  intro v
  rfl

theorem ca_F {ι : Type} {k s : ℕ} (g : ℕ) (X : (ι → Bool) → Fin k → Bool)
    (hX : ∀ i, Cb ι s (fun v => X v i)) (i : Fin k) :
    Cb ι (9 * s + 30) (fun v => FB g (X v) i) := by
  have h := ca_chi (fun v => mixB g (X v)) (ca_mix g X hX) i
  exact Cb.mono h (by omega)

theorem ca_ZB {ι : Type} {k m s : ℕ} (t : ℕ) (Vv : (ι → Bool) → T k m → Bool)
    (hV : ∀ j, Cb ι s (fun v => Vv v j)) (j : T k m) :
    Cb ι (10 * s + 34) (fun v => ZB t (Vv v) j) := by
  rcases j with i | j | i | i
  · exact Cb.mono (hV (Sum.inl i)) (by omega)
  · exact Cb.mono (hV (Sum.inr (Sum.inl j))) (by omega)
  · have h := Cb.xor (ca_F 1 (fun v => pr (Vv v)) (fun i => hV _) i)
      (hV (Sum.inl (ix i (k - (2 * t) % k))))
    refine Cb.mono (Cb.congr h ?_) (by omega)
    intro v
    rfl
  · have h := Cb.xor (ca_F 2 (fun v => pc (Vv v)) (fun i => hV _) i)
      (hV (Sum.inl (ix i (k - (3 * (t + 1) + 1) % k))))
    refine Cb.mono (Cb.congr h ?_) (by omega)
    intro v
    rfl

theorem ca_bvec (ι : Type) [DecidableEq ι] (τ : Type) (c j : ι) :
    Cb (τ ⊕ (ι × ι)) 7 (fun v => bvec (fun q => v (Sum.inr q)) c j) := by
  have h := Cb.and (Cb.not (Cb.var (ι := τ ⊕ (ι × ι)) (Sum.inr (c, c))))
    (Cb.xor (Cb.const (decide (j = c))) (Cb.var (Sum.inr (j, c))))
  refine Cb.mono (Cb.congr h ?_) (by norm_num)
  intro v
  rfl

def ca_qC (n : ℕ) : ℕ := n * n * (n * 109 + 1)

theorem ca_qB (k m t : ℕ) :
    Cmp ((T k m × T k m) ⊕ (T k m × T k m)) (T k m × T k m) (ca_qC (Fintype.card (T k m)))
      (fun v => qB t (fun q => v (Sum.inl q)) (fun q => v (Sum.inr q))) := by
  have hb : ∀ p : T k m × T k m, Cb ((T k m × T k m) ⊕ (T k m × T k m))
      (Fintype.card (T k m) * 109 + 1)
      (fun v => qB t (fun q => v (Sum.inl q)) (fun q => v (Sum.inr q)) p) := by
    intro p
    have h := Cb.bigXor (I := T k m) (s := 105)
      (φ := fun j (v : (T k m × T k m) ⊕ (T k m × T k m) → Bool) =>
        v (Sum.inl (p.1, j)) && ZB t (bvec (fun q => v (Sum.inr q)) p.2) j)
      (fun j => Cb.mono (Cb.and (Cb.var (Sum.inl (p.1, j)))
        (ca_ZB t (fun v => bvec (fun q => v (Sum.inr q)) p.2)
          (fun j' => ca_bvec (T k m) (T k m × T k m) p.2 j') j)) (by norm_num))
    refine Cb.mono (Cb.congr h ?_) (by omega)
    intro v
    rfl
  have h := Cmp.ofBits hb
  refine Cmp.mono h ?_
  rw [Fintype.card_prod]
  exact le_of_eq rfl

theorem ca_polB_bit (k m : ℕ) (a : T k m) (p : T k m × T k m) :
    Cb (T k m × T k m) (6 * k + 1) (fun C => polB C a p) := by
  rcases p with ⟨i | j | i | i, c | j' | c | c⟩
  case inr.inr.inl.inr.inr.inl =>
    have h := Cb.bigXor (I := Fin k) (s := 2)
      (φ := fun j (C : T k m × T k m → Bool) =>
        C (a, Sum.inr (Sum.inr (Sum.inl j))) && PB 1 (unitB c) (unitB i) j)
      (fun j => Cb.mono (Cb.and (Cb.var (a, Sum.inr (Sum.inr (Sum.inl j))))
        (Cb.const (PB 1 (unitB c) (unitB i) j))) (by norm_num))
    refine Cb.mono (Cb.congr h ?_) (by rw [Fintype.card_fin]; omega)
    intro v
    rfl
  case inr.inr.inr.inr.inr.inr =>
    have h := Cb.bigXor (I := Fin k) (s := 2)
      (φ := fun j (C : T k m × T k m → Bool) =>
        C (a, Sum.inr (Sum.inr (Sum.inr j))) && PB 2 (unitB c) (unitB i) j)
      (fun j => Cb.mono (Cb.and (Cb.var (a, Sum.inr (Sum.inr (Sum.inr j))))
        (Cb.const (PB 2 (unitB c) (unitB i) j))) (by norm_num))
    refine Cb.mono (Cb.congr h ?_) (by rw [Fintype.card_fin]; omega)
    intro v
    rfl
  all_goals exact Cb.mono (Cb.const false) (by omega)

def ca_polC (n k : ℕ) : ℕ := n * n * (6 * k + 1) + ca_absC n

noncomputable def ca_polStep {k m : ℕ} (a : T k m) (v : (T k m × T k m) ⊕ (T k m × T k m) → Bool) :
    (T k m × T k m) ⊕ (T k m × T k m) → Bool :=
  Sum.elim (fun q => v (Sum.inl q))
    (absorb (fun q => v (Sum.inr q)) (polB (fun q => v (Sum.inl q)) a))

theorem ca_polStep_cmp (k m : ℕ) (a : T k m) :
    Cmp ((T k m × T k m) ⊕ (T k m × T k m)) ((T k m × T k m) ⊕ (T k m × T k m))
      (ca_polC (Fintype.card (T k m)) k) (ca_polStep a) := by
  have hp : Cmp ((T k m × T k m) ⊕ (T k m × T k m)) (T k m × T k m)
      (Fintype.card (T k m × T k m) * (6 * k + 1))
      (fun v => polB (fun q => v (Sum.inl q)) a) :=
    Cmp.sel (fun q => Sum.inl q) (Cmp.ofBits (fun p => ca_polB_bit k m a p))
  have h1 := Cmp.comp (Cmp.pair
    (Cmp.wire (ι := (T k m × T k m) ⊕ (T k m × T k m)) (fun q : T k m × T k m => Sum.inr q)) hp)
    (ca_absorb (T k m))
  have h2 := Cmp.pair
    (Cmp.wire (ι := (T k m × T k m) ⊕ (T k m × T k m)) (fun q : T k m × T k m => Sum.inl q)) h1
  refine Cmp.mono (Cmp.congr h2 ?_) ?_
  · intro v p
    cases p <;> rfl
  · rw [Fintype.card_prod]
    unfold ca_polC
    omega

theorem ca_polR_fold {k m : ℕ} (C : T k m × T k m → Bool) (L : List (T k m))
    (R : T k m × T k m → Bool) :
    L.foldl (fun acc a => ca_polStep a acc) (Sum.elim C R) =
      Sum.elim C (L.foldl (fun R a => absorb R (polB C a)) R) := by
  induction L generalizing R with
  | nil => rfl
  | cons a L ih =>
    have h : ca_polStep a (Sum.elim C R) = Sum.elim C (absorb R (polB C a)) := rfl
    rw [List.foldl_cons, List.foldl_cons, h, ih]

def ca_polRC (n k : ℕ) : ℕ := n * n + n * ca_polC n k

theorem ca_polR (k m : ℕ) :
    Cmp (T k m × T k m) ((T k m × T k m) ⊕ (T k m × T k m))
      (ca_polRC (Fintype.card (T k m)) k) (fun C => Sum.elim C (polR C)) := by
  have h0 : Cmp (T k m × T k m) ((T k m × T k m) ⊕ (T k m × T k m))
      (0 + Fintype.card (T k m × T k m) * 1)
      (fun C => Sum.elim (fun q => C q) (fun _ => false)) :=
    Cmp.pair (Cmp.wire (fun q : T k m × T k m => q))
      (Cmp.ofBits (F := fun (_ : T k m × T k m → Bool) (_ : T k m × T k m) => false)
        (fun _ => Cb.const false))
  have h1 := Cmp.foldl (s := ca_polC (Fintype.card (T k m)) k)
    (Finset.univ : Finset (T k m)).toList (fun a v => ca_polStep a v)
    (fun a _ => ca_polStep_cmp k m a)
  have h2 := Cmp.comp h0 h1
  refine Cmp.mono (Cmp.congr h2 ?_) ?_
  · intro C p
    have := ca_polR_fold C (Finset.univ : Finset (T k m)).toList (fun _ => false)
    show ((Finset.univ : Finset (T k m)).toList.foldl (fun acc a => ca_polStep a acc)
      (Sum.elim C (fun _ => false))) p = _
    rw [this]
    rfl
  · rw [Finset.length_toList, Finset.card_univ, Fintype.card_prod]
    unfold ca_polRC
    omega

def ca_tickC (n k : ℕ) : ℕ := ca_polRC n k + ca_qC n + ca_absC n

theorem ca_tick (k m t : ℕ) :
    Cmp (T k m × T k m) (T k m × T k m) (ca_tickC (Fintype.card (T k m)) k)
      (fun C => tick t C) := by
  have h2 := Cmp.pair
    (Cmp.wire (ι := (T k m × T k m) ⊕ (T k m × T k m)) (fun q : T k m × T k m => Sum.inr q))
    (ca_qB k m t)
  have h3 := Cmp.comp (Cmp.comp (ca_polR k m) h2) (ca_absorb (T k m))
  refine Cmp.mono (Cmp.congr h3 ?_) ?_
  · intro C p
    rfl
  · unfold ca_tickC
    omega

theorem ca_term_bit (k m : ℕ) (p : T k m × T k m) :
    Cb ((Fin m × Fin k) ⊕ (Fin m × Fin k)) 1
      (fun v => termB (fun q => v (Sum.inl q)) (fun q => v (Sum.inr q)) p) := by
  rcases p with ⟨i | j | i | i, c | j' | c | c⟩
  case inr.inl.inr.inr.inl => exact Cb.mono (Cb.var (Sum.inl (j, c))) (by omega)
  case inr.inl.inr.inr.inr => exact Cb.mono (Cb.var (Sum.inr (j, c))) (by omega)
  all_goals exact Cb.const _

theorem ca_backC (k m r : ℕ) :
    Cmp ((Fin m × Fin k) ⊕ (Fin m × Fin k)) (T k m × T k m)
      (Fintype.card (T k m) * Fintype.card (T k m) + r * ca_tickC (Fintype.card (T k m)) k)
      (fun v => backC r (fun q => v (Sum.inl q)) (fun q => v (Sum.inr q))) := by
  have h0 := Cmp.ofBits (fun p => ca_term_bit k m p)
  have h1 := Cmp.foldl (s := ca_tickC (Fintype.card (T k m)) k) (List.range r).reverse
    (fun t (C : T k m × T k m → Bool) => tick t C) (fun t _ => ca_tick k m t)
  have h2 := Cmp.comp h0 h1
  refine Cmp.mono (Cmp.congr h2 ?_) ?_
  · intro v p
    show ((List.range r).reverse.foldl (fun acc e => tick e acc) _) p = _
    rw [List.foldl_reverse]
    rfl
  · rw [List.length_reverse, List.length_range, Fintype.card_prod]
    omega

abbrev ca_J (k m : ℕ) : Type := (T k m × T k m) ⊕ In0 k m

theorem ca_finH_bit (k m : ℕ) (ρ : T k m ⊕ Fin k) (c : Fin k) :
    Cb (ca_J k m) (6 * Fintype.card (T k m) + 2)
      (fun v => finH (fun q => v (Sum.inl q))
        (fun i => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))) (ρ, c)) := by
  rcases ρ with a | i
  · have h := Cb.bigXor (I := T k m) (s := 2)
      (φ := fun j (v : ca_J k m → Bool) =>
        v (Sum.inl (a, j)) && v0B (unitB c) (fun _ => false) j)
      (fun j => Cb.mono (Cb.and (Cb.var (Sum.inl (a, j)))
        (Cb.const (v0B (unitB c) (fun _ => false) j))) (by norm_num))
    refine Cb.mono (Cb.congr h ?_) (by omega)
    intro v
    rfl
  · have h := Cb.and
      (Cb.var (ι := ca_J k m) (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
      (Cb.const (decide (i = c)))
    refine Cb.mono (Cb.congr h ?_) (by omega)
    intro v
    rfl

theorem ca_finR_bit (k m : ℕ) (ρ : T k m ⊕ Fin k) :
    Cb (ca_J k m) (5 * m + 1)
      (fun v => finR (fun q => v (Sum.inl q))
        (fun j => v (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))
        (fun i => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
        (fun i => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))) ρ) := by
  rcases ρ with a | i
  · have h := Cb.bigXor (I := Fin m) (s := 1)
      (φ := fun j (v : ca_J k m → Bool) =>
        v (Sum.inl (a, Sum.inr (Sum.inl j))) && v (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))
      (fun j => Cb.mono (Cb.and (Cb.var (Sum.inl (a, Sum.inr (Sum.inl j))))
        (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))) (by norm_num))
    refine Cb.mono (Cb.congr h ?_) (by rw [Fintype.card_fin]; omega)
    intro v
    rfl
  · have h := Cb.and
      (Cb.var (ι := ca_J k m) (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
      (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))))
    refine Cb.mono (Cb.congr h ?_) (by omega)
    intro v
    rfl

theorem ca_finSys_bit (k m : ℕ) (p : Fin (rowsN k m + k + 1) × Fin (rowsN k m + k + 1)) :
    Cb (ca_J k m) (6 * Fintype.card (T k m) + 5 * m + 3)
      (fun v => finSys (fun q => v (Sum.inl q))
        (fun j => v (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))
        (fun i => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
        (fun i => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))) p) := by
  by_cases hi : p.1.val < rowsN k m
  · by_cases hj : p.2.val < k
    · refine Cb.mono (Cb.congr (ca_finH_bit k m
        ((Fintype.equivFin (T k m ⊕ Fin k)).symm ⟨p.1.val, hi⟩) ⟨p.2.val, hj⟩) ?_) (by omega)
      intro v
      simp only [finSys, sysB, dif_pos hi, dif_pos hj]
    · by_cases hN : p.2.val = k
      · refine Cb.mono (Cb.congr (ca_finR_bit k m
          ((Fintype.equivFin (T k m ⊕ Fin k)).symm ⟨p.1.val, hi⟩)) ?_) (by omega)
        intro v
        simp only [finSys, sysB, dif_pos hi, dif_neg hj, if_pos hN]
      · refine Cb.mono (Cb.congr (Cb.const false) ?_) (by omega)
        intro v
        simp only [finSys, sysB, dif_pos hi, dif_neg hj, if_neg hN]
  · refine Cb.mono (Cb.congr (Cb.const false) ?_) (by omega)
    intro v
    simp only [finSys, sysB, dif_neg hi]

theorem ca_fin_bit (k m : ℕ) (o : Fin (k + 1) ⊕ (Fin k ⊕ Unit)) :
    Cb ((Fin (rowsN k m + k + 1) × Fin (rowsN k m + k + 1)) ⊕ In0 k m) 1
      (fun w => Sum.elim
        (fun i => w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))))))
        (Sum.elim (fun p => !(w (Sum.inl (cl _ p, cl _ p))))
          (fun _ => !(w (Sum.inl (rc _ k, rc _ k))))) o) := by
  rcases o with i | p | u
  · exact Cb.mono (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))))) (by omega)
  · exact Cb.mono (Cb.not (Cb.var (Sum.inl (cl _ p, cl _ p)))) (by omega)
  · exact Cb.mono (Cb.not (Cb.var (Sum.inl (rc _ k, rc _ k)))) (by omega)

def ca_topC (n D k r m : ℕ) : ℕ :=
  (n * n + r * ca_tickC n k) + (D * D * (6 * n + 5 * m + 3) + gjCost D) + (2 * k + 2) +
    64 * (k + 2) ^ 2

theorem ca_top0 (k r m : ℕ) :
    Cb (In0 k m) (ca_topC (Fintype.card (T k m)) (rowsN k m + k + 1) k r m)
      (top (k := k) (m := m) r) := by
  have hA : Cmp (In0 k m) (T k m × T k m)
      (Fintype.card (T k m) * Fintype.card (T k m) + r * ca_tickC (Fintype.card (T k m)) k)
      (fun v => backC r (fun p => v (Sum.inl p)) (fun p => v (Sum.inr (Sum.inl p)))) :=
    Cmp.sel (fun q : (Fin m × Fin k) ⊕ (Fin m × Fin k) =>
      (Sum.elim (fun p => Sum.inl p) (fun p => Sum.inr (Sum.inl p)) q : In0 k m))
      (ca_backC k m r)
  have hJ := Cmp.pair hA (Cmp.wire (fun i : In0 k m => i))
  have hG := Cmp.comp (Cmp.ofBits (fun p => ca_finSys_bit k m p)) (cmp_gj (rowsN k m + k + 1))
  have hG2 := Cmp.pair hG (Cmp.wire (ι := ca_J k m) (fun i : In0 k m => Sum.inr i))
  have hF := Cmp.ofBits (fun o => ca_fin_bit k m o)
  have h := Cmp.comp (Cmp.comp (Cmp.comp hJ hG2) hF) (cmp_cmpB k)
  refine Cmp.mono (Cmp.congr h ?_) ?_
  · intro v u
    rfl
  · simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    unfold ca_topC
    omega

def topCost (k r m : ℕ) : ℕ := ca_topC (3 * k + m) (5 * k + m + 1) k r m

theorem cmp_top (k r m : ℕ) : Cb (In0 k m) (topCost k r m) (top (k := k) (m := m) r) := by
  have h := ca_top0 k r m
  have hn : Fintype.card (T k m) = 3 * k + m := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hD : rowsN k m + k + 1 = 5 * k + m + 1 := by
    simp only [rowsN, Fintype.card_sum, Fintype.card_fin]
    omega
  rw [hn, hD] at h
  exact h

theorem ca_absC_le (n s : ℕ) (hs : 1 ≤ s) (h2 : n + n + 1 ≤ 6 * s) :
    ca_absC n ≤ 41508 * s ^ 4 := by
  have h1 : n + n ≤ 6 * s := by omega
  have ha : (n + n) * (n + n) ≤ (6 * s) * (6 * s) := Nat.mul_le_mul h1 h1
  have hb : (n + n + 1) ^ 4 ≤ (6 * s) ^ 4 := Nat.pow_le_pow_left h2 4
  have hp : s ^ 2 ≤ s ^ 4 := Nat.pow_le_pow_right hs (by norm_num)
  unfold ca_absC gjCost
  have e1 : (6 * s) * (6 * s) = 36 * s ^ 2 := by ring
  have e2 : (6 * s) ^ 4 = 1296 * s ^ 4 := by ring
  omega

theorem ca_tickC_le (n k s : ℕ) (hs : 1 ≤ s) (hn : n ≤ 3 * s) (h2 : n + n + 1 ≤ 6 * s)
    (hk : k ≤ s) : ca_tickC n k ≤ 169182 * s ^ 5 := by
  have hA := ca_absC_le n s hs h2
  have hnn : n * n ≤ 9 * s ^ 2 := by
    have := Nat.mul_le_mul hn hn
    have e : (3 * s) * (3 * s) = 9 * s ^ 2 := by ring
    omega
  have p23 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right hs (by norm_num)
  have p24 : s ^ 2 ≤ s ^ 4 := Nat.pow_le_pow_right hs (by norm_num)
  have p34 : s ^ 3 ≤ s ^ 4 := Nat.pow_le_pow_right hs (by norm_num)
  have p25 : s ^ 2 ≤ s ^ 5 := Nat.pow_le_pow_right hs (by norm_num)
  have p35 : s ^ 3 ≤ s ^ 5 := Nat.pow_le_pow_right hs (by norm_num)
  have p45 : s ^ 4 ≤ s ^ 5 := Nat.pow_le_pow_right hs (by norm_num)
  have hpol : ca_polC n k ≤ 41571 * s ^ 4 := by
    unfold ca_polC
    have h6 : 6 * k + 1 ≤ 7 * s := by omega
    have := Nat.mul_le_mul hnn h6
    have e : 9 * s ^ 2 * (7 * s) = 63 * s ^ 3 := by ring
    omega
  have hpolR : ca_polRC n k ≤ 124722 * s ^ 5 := by
    unfold ca_polRC
    have := Nat.mul_le_mul hn hpol
    have e : 3 * s * (41571 * s ^ 4) = 124713 * s ^ 5 := by ring
    omega
  have hq : ca_qC n ≤ 2952 * s ^ 5 := by
    unfold ca_qC
    have h6 : n * 109 + 1 ≤ 328 * s := by omega
    have := Nat.mul_le_mul hnn h6
    have e : 9 * s ^ 2 * (328 * s) = 2952 * s ^ 3 := by ring
    omega
  unfold ca_tickC
  omega

theorem topCost_le (k r m : ℕ) (hk : 0 < k) :
    topCost k r m + 1 ≤ 2 ^ 20 * (r + 1) * (k + m + 1) ^ 8 := by
  obtain ⟨s, hs⟩ : ∃ s, s = k + m + 1 := ⟨_, rfl⟩
  rw [← hs]
  have hs1 : 1 ≤ s := by omega
  have hT := ca_tickC_le (3 * k + m) k s hs1 (by omega) (by omega) (by omega)
  have p14 : s ≤ s ^ 4 := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ 4 := Nat.pow_le_pow_right hs1 (by norm_num)
  have p24 : s ^ 2 ≤ s ^ 4 := Nat.pow_le_pow_right hs1 (by norm_num)
  have p34 : s ^ 3 ≤ s ^ 4 := Nat.pow_le_pow_right hs1 (by norm_num)
  have p48 : s ^ 4 ≤ s ^ 8 := Nat.pow_le_pow_right hs1 (by norm_num)
  have p58 : s ^ 5 ≤ s ^ 8 := Nat.pow_le_pow_right hs1 (by norm_num)
  have hnn : (3 * k + m) * (3 * k + m) ≤ 9 * s ^ 2 := by
    have := Nat.mul_le_mul (show 3 * k + m ≤ 3 * s by omega) (show 3 * k + m ≤ 3 * s by omega)
    have e : (3 * s) * (3 * s) = 9 * s ^ 2 := by ring
    omega
  have hDD : (5 * k + m + 1) * (5 * k + m + 1) ≤ 25 * s ^ 2 := by
    have := Nat.mul_le_mul (show 5 * k + m + 1 ≤ 5 * s by omega)
      (show 5 * k + m + 1 ≤ 5 * s by omega)
    have e : (5 * s) * (5 * s) = 25 * s ^ 2 := by ring
    omega
  have hsys : (5 * k + m + 1) * (5 * k + m + 1) * (6 * (3 * k + m) + 5 * m + 3) ≤ 650 * s ^ 3 := by
    have := Nat.mul_le_mul hDD (show 6 * (3 * k + m) + 5 * m + 3 ≤ 26 * s by omega)
    have e : 25 * s ^ 2 * (26 * s) = 650 * s ^ 3 := by ring
    omega
  have hgj : gjCost (5 * k + m + 1) ≤ 20000 * s ^ 4 := by
    unfold gjCost
    have := Nat.pow_le_pow_left (show 5 * k + m + 1 + 1 ≤ 5 * s by omega) 4
    have e : (5 * s) ^ 4 = 625 * s ^ 4 := by ring
    omega
  have hcmp : 64 * (k + 2) ^ 2 ≤ 256 * s ^ 2 := by
    have := Nat.pow_le_pow_left (show k + 2 ≤ 2 * s by omega) 2
    have e : (2 * s) ^ 2 = 4 * s ^ 2 := by ring
    omega
  have hr : r * ca_tickC (3 * k + m) k ≤ r * (169182 * s ^ 5) := Nat.mul_le_mul_left r hT
  have hr2 : r * (169182 * s ^ 5) ≤ r * (169182 * s ^ 8) :=
    Nat.mul_le_mul_left r (Nat.mul_le_mul_left _ p58)
  have e1 : r * (169182 * s ^ 8) = 169182 * (r * s ^ 8) := by ring
  have e2 : 2 ^ 20 * (r + 1) * s ^ 8 = 1048576 * (r * s ^ 8) + 1048576 * s ^ 8 := by ring
  unfold topCost ca_topC
  rw [e2]
  omega

def rotN (k s word : ℕ) : ℕ := ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepN (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

def fN (k : ℕ) (col : Bool) (x : ℕ) : ℕ :=
  stepN k (x ^^^ rotN k (if col then 2 else 1) x ^^^ rotN k (k - (if col then 2 else 1)) x)

def trN (k : ℕ) (col : Bool) (w u : ℕ) (c : ℕ → Fin (2 ^ k)) : ℕ → ℕ
  | 0 => rotN k (if col then 3 else 1) w ^^^ u
  | t + 1 => fN k col (trN k col w u c t) ^^^
      rotN k (if col then 3 * (t + 1) + 1 else 2 * t) w ^^^ (c (t + 1)).val

def parityN (k mask x : ℕ) : Bool :=
  (List.range k).foldl (fun b i => xor b (mask.testBit i && x.testBit i)) false

def vec (k : ℕ) (x : ℕ) : V k := fun i => b2z (x.testBit i.val)

def iter {k m : ℕ} (t0 : ℕ) (v : T k m → ZMod 2) (xs xs' : ℕ → V k) : ℕ → (T k m → ZMod 2)
  | 0 => v
  | n + 1 => updZ (t0 + n) (xs (t0 + n)) (xs' (t0 + n)) (iter t0 v xs xs' n)

theorem br_rot_lt (k s word : ℕ) : rotN k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

theorem br_xor_lt {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

theorem br_testBit_rot {k s word b : ℕ} (hw : word < 2 ^ k) (hb : b < k) :
    (rotN k s word).testBit b = word.testBit ((b + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [rotN, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hz : word.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (b + k - s % k) % k = b - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp [h, hz, he]
  · have he : (b + k - s % k) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [h, he]

theorem br_testBit_foldl_or (p : ℕ → Bool) (xs : List ℕ) (acc i : ℕ) :
    (xs.foldl (fun a j => a ||| ((p j).toNat <<< j)) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst j; cases p i <;> simp
    · by_cases hle : j ≤ i
      · have hsub : 1 ≤ i - j := by omega
        have hbt : (p j).toNat.testBit (i - j) = false := by
          cases p j
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hji]
      · simp [hle, Ne.symm hji]

theorem br_testBit_step_all (k word b : ℕ) :
    (stepN k word).testBit b = (decide (b < k) &&
      xor (word.testBit b) (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))) := by
  unfold stepN
  rw [br_testBit_foldl_or (fun i => xor (word.testBit i)
    (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)))]
  simp

theorem br_step_lt (k word : ℕ) : stepN k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [br_testBit_step_all, Nat.not_lt_of_ge hb]

theorem br_z2 (z : ZMod 2) : z + z = 0 := by
  revert z; decide

theorem br_b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem br_b2z_inj (a b : Bool) (h : b2z a = b2z b) : a = b := by
  revert h; cases a <;> cases b <;> decide

theorem br_vec_xor (k a b : ℕ) : vec k (a ^^^ b) = vec k a + vec k b := by
  funext i
  simp [vec, Nat.testBit_xor, br_b2z_xor]

theorem br_rotZ_add {k : ℕ} (s : ℕ) (x y : V k) : rotZ s (x + y) = rotZ s x + rotZ s y := by
  funext i; simp [rotZ]

theorem br_vec_rot {k : ℕ} (s : ℕ) {w : ℕ} (hw : w < 2 ^ k) :
    vec k (rotN k s w) = rotZ s (vec k w) := by
  funext i
  have hk : 0 < k := i.pos
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [vec, rotZ, ix]
  rw [br_testBit_rot hw i.isLt]
  have e : i.val + k - s % k = i.val + (k - s % k) := by omega
  rw [e]

theorem br_vec_step (k x : ℕ) : vec k (stepN k x) = chiZ (vec k x) := by
  funext i
  simp only [vec, chiZ, ix]
  rw [br_testBit_step_all]
  simp only [i.isLt, decide_true, Bool.true_and]
  generalize x.testBit i.val = a
  generalize x.testBit ((i.val + 1) % k) = b
  generalize x.testBit ((i.val + 2) % k) = c
  cases a <;> cases b <;> cases c <;> decide

theorem br_vec_f {k : ℕ} (col : Bool) {x : ℕ} (hx : x < 2 ^ k) :
    vec k (fN k col x) = FZ (if col then 2 else 1) (vec k x) := by
  unfold fN FZ
  rw [br_vec_step]
  congr 1
  funext i
  simp [mixZ, br_vec_xor, br_vec_rot _ hx]

theorem br_tr_lt {k : ℕ} (col : Bool) (w : ℕ) {u : ℕ} (hu : u < 2 ^ k) (c : ℕ → Fin (2 ^ k))
    (t : ℕ) : trN k col w u c t < 2 ^ k := by
  cases t with
  | zero => exact br_xor_lt (br_rot_lt _ _ _) hu
  | succ t => exact br_xor_lt (br_xor_lt (br_step_lt _ _) (br_rot_lt _ _ _)) (c (t + 1)).isLt

theorem br_state_eq (k r : ℕ) (col : Bool) (w u : ℕ) (c : ℕ → Fin (2 ^ k)) :
    (List.range r).foldl (fun x j =>
      stepN k (x ^^^ rotN k (if col then 2 else 1) x ^^^ rotN k (k - (if col then 2 else 1)) x) ^^^
        rotN k (if col then 3 * (j + 1) + 1 else 2 * j) w ^^^ (c (j + 1)).val)
      (rotN k (if col then 3 else 1) w ^^^ u) = trN k col w u c r := by
  induction r with
  | zero => simp [trN]
  | succ r ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [trN, fN]

theorem br_foldl_xor (f : ℕ → Bool) (n : ℕ) :
    b2z ((List.range n).foldl (fun b i => xor b (f i)) false) =
      ∑ i ∈ Finset.range n, b2z (f i) := by
  induction n with
  | zero => simp [b2z]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp [br_b2z_xor]

theorem br_b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem br_parity (k mask x : ℕ) :
    b2z (parityN k mask x) = ∑ i : Fin k, b2z (mask.testBit i.val) * vec k x i := by
  unfold parityN
  rw [br_foldl_xor (fun i => mask.testBit i && x.testBit i) k, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [vec, br_b2z_and]

def dl (k : ℕ) (col : Bool) (w d u : ℕ) (c : ℕ → Fin (2 ^ k)) (t : ℕ) : V k :=
  vec k (trN k col (w ^^^ d) u c t) + vec k (trN k col w u c t)

theorem br_dl_zero {k : ℕ} (col : Bool) {w d : ℕ} (hw : w < 2 ^ k) (hd : d < 2 ^ k) (u : ℕ)
    (c : ℕ → Fin (2 ^ k)) :
    dl k col w d u c 0 = rotZ (if col then 3 else 1) (vec k d) := by
  unfold dl
  simp only [trN]
  rw [br_vec_xor, br_vec_xor, br_vec_rot _ hw, br_vec_rot _ (br_xor_lt hw hd), br_vec_xor,
    br_rotZ_add]
  funext i
  simp only [Pi.add_apply]
  linear_combination br_z2 (rotZ (if col then 3 else 1) (vec k w) i) + br_z2 (vec k u i)

theorem br_dl_succ {k : ℕ} (col : Bool) {w d u : ℕ} (hw : w < 2 ^ k) (hd : d < 2 ^ k)
    (hu : u < 2 ^ k) (c : ℕ → Fin (2 ^ k)) (t : ℕ) :
    dl k col w d u c (t + 1) = fun i =>
      FZ (if col then 2 else 1) (vec k (trN k col w u c t) + dl k col w d u c t) i +
        FZ (if col then 2 else 1) (vec k (trN k col w u c t)) i +
        rotZ (if col then 3 * (t + 1) + 1 else 2 * t) (vec k d) i := by
  have e : vec k (trN k col w u c t) + dl k col w d u c t = vec k (trN k col (w ^^^ d) u c t) := by
    unfold dl
    funext i
    simp only [Pi.add_apply]
    linear_combination br_z2 (vec k (trN k col w u c t) i)
  rw [e]
  unfold dl
  simp only [trN]
  rw [br_vec_xor, br_vec_xor, br_vec_xor, br_vec_xor, br_vec_rot _ hw,
    br_vec_rot _ (br_xor_lt hw hd), br_vec_xor, br_rotZ_add,
    br_vec_f col (br_tr_lt col _ hu c t), br_vec_f col (br_tr_lt col _ hu c t)]
  funext i
  simp only [Pi.add_apply]
  linear_combination
    br_z2 (rotZ (if col then 3 * (t + 1) + 1 else 2 * t) (vec k w) i) +
      br_z2 (vec k (c (t + 1)).val i)

theorem br_iter_words {k m : ℕ} (y : Fin m → Bool) {w d u v : ℕ} (hw : w < 2 ^ k)
    (hd : d < 2 ^ k) (hu : u < 2 ^ k) (hv : v < 2 ^ k) (cr cc : ℕ → Fin (2 ^ k)) (t : ℕ) :
    iter 0 (mk (vec k d) (toZ y) (rotZ 1 (vec k d)) (rotZ 3 (vec k d)))
        (fun n => vec k (trN k false w u cr n)) (fun n => vec k (trN k true w v cc n)) t =
      mk (vec k d) (toZ y) (dl k false w d u cr t) (dl k true w d v cc t) := by
  induction t with
  | zero =>
    simp only [iter]
    rw [br_dl_zero false hw hd, br_dl_zero true hw hd]
    simp
  | succ t ih =>
    simp only [iter, zero_add]
    rw [ih, br_dl_succ false hw hd hu, br_dl_succ true hw hd hv]
    rfl

theorem br_iter_shift {k m : ℕ} (t0 : ℕ) (v : T k m → ZMod 2) (xs xs' : ℕ → V k) (n : ℕ) :
    iter t0 v xs xs' (n + 1) = iter (t0 + 1) (updZ t0 (xs t0) (xs' t0) v) xs xs' n := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    have e : t0 + (n + 1) = t0 + 1 + n := by omega
    calc iter t0 v xs xs' (n + 1 + 1)
        = updZ (t0 + (n + 1)) (xs (t0 + (n + 1))) (xs' (t0 + (n + 1)))
            (iter t0 v xs xs' (n + 1)) := rfl
      _ = updZ (t0 + 1 + n) (xs (t0 + 1 + n)) (xs' (t0 + 1 + n))
            (iter (t0 + 1) (updZ t0 (xs t0) (xs' t0) v) xs xs' n) := by rw [ih, e]
      _ = _ := rfl

theorem br_iter_congr {k m : ℕ} (t0 : ℕ) (v : T k m → ZMod 2) (xs xs' ys ys' : ℕ → V k)
    (h : ∀ n, xs (t0 + n) = ys (t0 + n)) (h' : ∀ n, xs' (t0 + n) = ys' (t0 + n)) (n : ℕ) :
    iter t0 v xs xs' n = iter t0 v ys ys' n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter]; rw [ih, h, h']

theorem br_okrem_seq {k m : ℕ} (A B : Fin m × Fin k → Bool) (s : ℕ) :
    ∀ (t : ℕ) (v : T k m → ZMod 2),
      OkRem A B s t v ↔ ∀ xs xs' : ℕ → V k, termOk A B (iter t v xs xs' s) := by
  induction s with
  | zero =>
    intro t v
    exact ⟨fun h _ _ => h, fun h => h (fun _ => 0) (fun _ => 0)⟩
  | succ s ih =>
    intro t v
    constructor
    · intro h xs xs'
      rw [br_iter_shift]
      exact (ih (t + 1) _).1 (h (xs t) (xs' t)) xs xs'
    · intro h x x'
      refine (ih (t + 1) _).2 ?_
      intro xs xs'
      have h1 := h (Function.update xs t x) (Function.update xs' t x')
      rw [br_iter_shift] at h1
      simp only [Function.update_self] at h1
      rw [br_iter_congr (t + 1) _ _ _ xs xs'
        (fun n => Function.update_of_ne (by omega) _ _)
        (fun n => Function.update_of_ne (by omega) _ _)] at h1
      exact h1

theorem br_vec_inj {k : ℕ} {a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (h : vec k a = vec k b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact br_b2z_inj _ _ (congrFun h ⟨i, hi⟩)
  · have hp := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_lt hi)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp), Nat.testBit_lt_two_pow (hb.trans_le hp)]

theorem br_vec_bij (k : ℕ) : Function.Bijective (fun a : Fin (2 ^ k) => vec k a.val) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b h => Fin.ext (br_vec_inj a.isLt b.isLt h), ?_⟩
  simp [V, ZMod.card]

theorem br_rot_zero (k s : ℕ) : rotN k s 0 = 0 := by simp [rotN]

theorem br_realize {k : ℕ} (col : Bool) (xs : ℕ → V k) :
    ∃ (u : Fin (2 ^ k)) (c : ℕ → Fin (2 ^ k)), ∀ t, vec k (trN k col 0 u.val c t) = xs t := by
  choose wd hwd using fun t => (br_vec_bij k).2 (xs t)
  refine ⟨wd 0, fun t => ⟨(wd t).val ^^^ fN k col (wd (t - 1)).val,
    br_xor_lt (wd t).isLt (br_step_lt _ _)⟩, ?_⟩
  have key : ∀ t, trN k col 0 (wd 0).val (fun t => ⟨(wd t).val ^^^ fN k col (wd (t - 1)).val,
      br_xor_lt (wd t).isLt (br_step_lt _ _)⟩) t = (wd t).val := by
    intro t
    induction t with
    | zero => simp [trN, br_rot_zero]
    | succ t ih =>
      simp only [trN, br_rot_zero, ih, Nat.add_sub_cancel, Nat.xor_zero]
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_xor]
      generalize (fN k col (wd t).val).testBit i = a
      generalize (wd (t + 1)).val.testBit i = b
      cases a <;> cases b <;> rfl
  intro t
  rw [key]
  exact hwd t

theorem br_term {k m : ℕ} (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (d0 : V k)
    (a a' b b' : ℕ) :
    termOk (fun p => (A p.1).val.testBit p.2.val) (fun p => (B p.1).val.testBit p.2.val)
        (mk d0 (toZ y) (vec k a + vec k a') (vec k b + vec k b')) ↔
      ∀ j : Fin m, xor (parityN k (A j).val (a ^^^ a')) (parityN k (B j).val (b ^^^ b')) = y j := by
  unfold termOk
  apply forall_congr'
  intro j
  have e1 : ∑ i, b2z ((A j).val.testBit i.val) *
      pr (mk (m := m) d0 (toZ y) (vec k a + vec k a') (vec k b + vec k b')) i =
      b2z (parityN k (A j).val (a ^^^ a')) := by
    rw [br_parity, br_vec_xor]; rfl
  have e2 : ∑ i, b2z ((B j).val.testBit i.val) *
      pc (mk (m := m) d0 (toZ y) (vec k a + vec k a') (vec k b + vec k b')) i =
      b2z (parityN k (B j).val (b ^^^ b')) := by
    rw [br_parity, br_vec_xor]; rfl
  have e3 : py (mk (k := k) d0 (toZ y) (vec k a + vec k a') (vec k b + vec k b')) j = b2z (y j) :=
    rfl
  rw [e1, e2, e3]
  generalize parityN k (A j).val (a ^^^ a') = p
  generalize parityN k (B j).val (b ^^^ b') = q
  generalize y j = z
  cases p <;> cases q <;> cases z <;> decide

theorem br_pin {k : ℕ} (d pin value : Fin (2 ^ k)) :
    (d.val &&& pin.val) = (value.val &&& pin.val) ↔
      ∀ i : Fin k, pin.val.testBit i.val = true → vec k d.val i = b2z (value.val.testBit i.val) := by
  constructor
  · intro h i hp
    have := congrArg (fun z => z.testBit i.val) h
    simp only [Nat.testBit_and, hp, Bool.and_true] at this
    simp [vec, this]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    by_cases hi : i < k
    · cases hp : pin.val.testBit i with
      | false => simp
      | true =>
        have := br_b2z_inj _ _ (h ⟨i, hi⟩ hp)
        simp [this]
    · have hp := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_lt hi)
      rw [Nat.testBit_lt_two_pow (pin.isLt.trans_le hp)]
      simp

theorem br_good_iff (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (pin value d : Fin (2 ^ k)) :
    ((d.val &&& pin.val) = (value.val &&& pin.val) ∧
      ∀ (w u v : Fin (2 ^ k)) (cr cc : ℕ → Fin (2 ^ k)) (j : Fin m),
        xor (parityN k (A j).val (trN k false (w.val ^^^ d.val) u.val cr r ^^^
            trN k false w.val u.val cr r))
          (parityN k (B j).val (trN k true (w.val ^^^ d.val) v.val cc r ^^^
            trN k true w.val v.val cc r)) = y j) ↔
    ((∀ i : Fin k, pin.val.testBit i.val = true →
        vec k d.val i = b2z (value.val.testBit i.val)) ∧
      OkRem (fun p => (A p.1).val.testBit p.2.val) (fun p => (B p.1).val.testBit p.2.val) r 0
        (mk (vec k d.val) (toZ y) (rotZ 1 (vec k d.val)) (rotZ 3 (vec k d.val)))) := by
  rw [br_pin, br_okrem_seq]
  apply and_congr_right
  intro _
  constructor
  · intro H xs xs'
    obtain ⟨u, cr, hu⟩ := br_realize false xs
    obtain ⟨v, cc, hv⟩ := br_realize true xs'
    have hz : (0 : ℕ) < 2 ^ k := Nat.two_pow_pos k
    have h1 := br_iter_words y hz d.isLt u.isLt v.isLt cr cc r
    rw [br_iter_congr 0 _ xs xs' (fun n => vec k (trN k false 0 u.val cr n))
      (fun n => vec k (trN k true 0 v.val cc n))
      (fun n => by simp [hu]) (fun n => by simp [hv]), h1]
    unfold dl
    rw [br_term]
    intro j
    have := H ⟨0, hz⟩ u v cr cc j
    simpa using this
  · intro H w u v cr cc j
    have h1 := br_iter_words y w.isLt d.isLt u.isLt v.isLt cr cc r
    have h2 := H (fun n => vec k (trN k false w.val u.val cr n))
      (fun n => vec k (trN k true w.val v.val cc n))
    rw [h1] at h2
    unfold dl at h2
    rw [br_term] at h2
    exact h2 j

theorem br_natOf (n t : ℕ) : natOf (fun i : Fin n => t.testBit i.val) = t % 2 ^ n := by
  induction n with
  | zero => simp [natOf, Nat.mod_one]
  | succ n ih =>
    unfold natOf at ih ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (t / 2 ^ n) with h | h <;> simp [h]

theorem br_top_sem (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (pin value : Fin (2 ^ k)) (t : Fin (2 ^ (k + 1))) (P : Fin (2 ^ k) → Prop)
    (hP : ∀ d, P d ↔ ((∀ i : Fin k, pin.val.testBit i.val = true →
        vec k d.val i = b2z (value.val.testBit i.val)) ∧
      OkRem (fun p => (A p.1).val.testBit p.2.val) (fun p => (B p.1).val.testBit p.2.val) r 0
        (mk (vec k d.val) (toZ y) (rotZ 1 (vec k d.val)) (rotZ 3 (vec k d.val))))) :
    top r (inpOf A B y pin value t) = decide (t.val ≤ Nat.card {d : Fin (2 ^ k) // P d}) := by
  have hc := fin_count (backC r (fun p : Fin m × Fin k => (A p.1).val.testBit p.2.val)
    (fun p => (B p.1).val.testBit p.2.val)) y (fun i => pin.val.testBit i.val)
    (fun i => value.val.testBit i.val)
  have hcard : Nat.card {d : Fin (2 ^ k) // P d} =
      Nat.card {d : V k // (∀ i, pin.val.testBit i.val = true →
        d i = b2z (value.val.testBit i.val)) ∧
        kerB (backC r (fun p : Fin m × Fin k => (A p.1).val.testBit p.2.val)
          (fun p => (B p.1).val.testBit p.2.val)) (mk d (toZ y) (rotZ 1 d) (rotZ 3 d))} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (Equiv.ofBijective _ (br_vec_bij k)) ?_
    intro d
    rw [hP d, okrem_iff_ker]
    rfl
  rw [hcard, ← hc]
  unfold top cmpB
  have hn : natOf (fun i : Fin (k + 1) => t.val.testBit i.val) = t.val := by
    rw [br_natOf, Nat.mod_eq_of_lt t.isLt]
  simp only [finG, inpOf, Sum.elim_inl, Sum.elim_inr, hn]
  congr 1

end PEqualNP.Outside.L_meta_32029

theorem PEqualNP.Outside.L_meta_32029 : (∀ (k r m : Nat), 0 < k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w u : Nat) (c : Nat → Fin (2^k)) =>
    let g := if col then 2 else 1
    (List.range r).foldl (fun x j =>
      step (x ^^^ rot g x ^^^ rot (k-g) x) ^^^
        rot (if col then 3*(j+1)+1 else 2*j) w ^^^ (c (j+1)).val)
      (rot (if col then 3 else 1) w ^^^ u)
  let parity := fun (mask x : Nat) =>
    (List.range k).foldl (fun b i => xor b (mask.testBit i && x.testBit i)) false
  let bits := fun (n x : Nat) => (List.range n).map (fun i => x.testBit i)
  let bank := fun (A : Fin m → Fin (2^k)) =>
    (List.finRange m).flatMap (fun j => bits k (A j).val)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*m*k+m+2*k+(k+1)) C ∧
    C.size ≤ 2^20 * (r+1) * (k+m+1)^8 ∧
    ∀ (A B : Fin m → Fin (2^k)) (y : Fin m → Bool)
      (pin value : Fin (2^k)) (t : Fin (2^(k+1))),
      let good := fun (d : Fin (2^k)) =>
        (d.val &&& pin.val) = (value.val &&& pin.val) ∧
        ∀ (w u v : Fin (2^k)) (cr cc : Nat → Fin (2^k)) (j : Fin m),
          let w' := w.val ^^^ d.val
          let dr := state false w' u.val cr ^^^ state false w.val u.val cr
          let dc := state true w' v.val cc ^^^ state true w.val v.val cc
          xor (parity (A j).val dr) (parity (B j).val dc) = y j
      C.eval (bank A ++ bank B ++ List.ofFn y ++ bits k pin.val ++ bits k value.val ++
        bits (k+1) t.val) = decide (t.val ≤ Nat.card {d : Fin (2^k) // good d})) := by
  intro k r m hk rot step state parity bits bank
  obtain ⟨C, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_meta_32029.assemble k r m _
    (PEqualNP.Outside.L_meta_32029.cmp_top k r m)
    (PEqualNP.Outside.L_meta_32029.topCost_le k r m hk)
  refine ⟨C, h1, h2, h3, ?_⟩
  intro A B y pin value t good
  have hst : ∀ (col : Bool) (w u : ℕ) (c : ℕ → Fin (2 ^ k)),
      state col w u c = PEqualNP.Outside.L_meta_32029.trN k col w u c r :=
    fun col w u c => PEqualNP.Outside.L_meta_32029.br_state_eq k r col w u c
  have hgood : ∀ d, good d ↔ _ := fun d => by
    refine Iff.trans ?_ (PEqualNP.Outside.L_meta_32029.br_good_iff k r m A B y pin value d)
    show (_ ∧ ∀ (w u v : Fin (2 ^ k)) (cr cc : ℕ → Fin (2 ^ k)) (j : Fin m),
      xor (parity (A j).val (state false (w.val ^^^ d.val) u.val cr ^^^ state false w.val u.val cr))
        (parity (B j).val (state true (w.val ^^^ d.val) v.val cc ^^^ state true w.val v.val cc))
        = y j) ↔ _
    simp only [hst]
    rfl
  rw [← PEqualNP.Outside.L_meta_32029.br_top_sem k r m A B y pin value t good hgood]
  exact h4 A B y pin value t
