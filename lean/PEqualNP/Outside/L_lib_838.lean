import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_838
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

def Cw (ι : Type) (W S : ℕ) (φ : (ι → Bool) → BitVec W) : Prop :=
  Cmp ι (Fin W) S (fun v i => (φ v).getLsbD i.val)

abbrev V (d : ℕ) := Fin d → ZMod 2

def bv {W : ℕ} (w : Fin W → Bool) : BitVec W := BitVec.ofFnLE w

def tab {α : Type} {W : ℕ} (v : α × Fin W → Bool) : α → BitVec W := fun x => bv (fun i => v (x, i))

def untab {α : Type} {W : ℕ} (T : α → BitVec W) : α × Fin W → Bool := fun p => (T p.1).getLsbD p.2.val

def mat {r c : ℕ} (v : Fin r × Fin c → Bool) : Matrix (Fin r) (Fin c) (ZMod 2) :=
  fun i j => if v (i, j) then 1 else 0

def sgn {W : ℕ} (b : ZMod 2) : BitVec W := if b = 0 then 1 else -1

def tmat {D : ℕ} (t s : Fin D) (c : Bool) : Matrix (Fin D) (Fin D) (ZMod 2) :=
  Matrix.transvection t s (if c then 1 else 0)

def zmat {D : ℕ} (q : Fin D) (c : Bool) : Matrix (Fin D) (Fin D) (ZMod 2) :=
  Matrix.diagonal (fun i => if i = q ∧ c = true then 0 else 1)

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

def offdiag (D : ℕ) : List (Fin D × Fin D) :=
  ((List.finRange D).flatMap fun p => (List.finRange D).map fun q => (p, q)).filter
    (fun e => e.1 ≠ e.2)

def join3 {a b c : ℕ} (h : V a × V b × V c) : V (a + b + c) := fun j =>
  if h1 : j.val < a then h.1 ⟨j.val, h1⟩
  else if h2 : j.val < a + b then h.2.1 ⟨j.val - a, by omega⟩
  else h.2.2 ⟨j.val - (a + b), by omega⟩

def sysBits {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) :
    Fin (m + N + 1) × Fin (m + N + 1) → Bool := fun p =>
  if hi : p.1.val < m then
    (if hj : p.2.val < N then decide (Hf ⟨p.1.val, hi⟩ ⟨p.2.val, hj⟩ ≠ 0)
     else if p.2.val = N then decide (rhs ⟨p.1.val, hi⟩ ≠ 0) else false)
  else false

def cl (m : ℕ) {N : ℕ} (p : Fin N) : Fin (m + N + 1) := ⟨p.val, by omega⟩
def rc (m N : ℕ) : Fin (m + N + 1) := ⟨N, by omega⟩

def pv {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) : Bool :=
  R (cl m p, cl m p)

def cntP {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) : ℕ :=
  (Finset.univ.filter (fun q : Fin N => q < p ∧ pv R q = true)).card

def cntN {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) : ℕ :=
  (Finset.univ.filter (fun q : Fin N => q < p ∧ pv R q = false)).card

def rkOf {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) : ℕ :=
  (Finset.univ.filter (fun q : Fin N => pv R q = true)).card

def rowSlot {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (s : Fin K)
    (j : Fin (m + N + 1)) : Bool :=
  decide (∃ p : Fin N, pv R p = true ∧ cntP R p = s.val ∧ R (cl m p, j) = true)

def nx {a b c : ℕ} (j : Fin a) : Fin (a + b + c) := ⟨j.val, by omega⟩
def ny {a b c : ℕ} (j : Fin b) : Fin (a + b + c) := ⟨a + j.val, by omega⟩
def nz {a b c : ℕ} (j : Fin c) : Fin (a + b + c) := ⟨a + b + j.val, by omega⟩

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

theorem getLsbD_bv {W : ℕ} (w : Fin W → Bool) (i : Fin W) : (bv w).getLsbD i.val = w i := by
  simp [bv]

theorem bv_getLsbD {W : ℕ} (x : BitVec W) : bv (fun i : Fin W => x.getLsbD i.val) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [bv, hi]

theorem tab_untab {α : Type} {W : ℕ} (T : α → BitVec W) : tab (untab T) = T := by
  funext x
  show bv (fun i : Fin W => (T x).getLsbD i.val) = T x
  exact bv_getLsbD _

theorem untab_tab {α : Type} {W : ℕ} (v : α × Fin W → Bool) : untab (tab v) = v := by
  funext p
  show (bv (fun i => v (p.1, i))).getLsbD p.2.val = v p
  exact getLsbD_bv _ _

theorem Cw.mono {ι : Type} {W S S' : ℕ} {φ : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (hS : S ≤ S') : Cw ι W S' φ := Cmp.mono h hS

theorem Cw.congr {ι : Type} {W S : ℕ} {φ φ' : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (hF : ∀ v, φ v = φ' v) : Cw ι W S φ' := Cmp.congr h (fun v _ => by rw [hF v])

theorem Cw.var {ι : Type} {W : ℕ} (σ : Fin W → ι) : Cw ι W 0 (fun v => bv (fun i => v (σ i))) :=
  Cmp.congr (Cmp.wire σ) (fun v k => (getLsbD_bv (fun i => v (σ i)) k).symm)

theorem Cw.comp {ι κ : Type} {W S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    {φ : (κ → Bool) → BitVec W} (h : Cmp ι κ S F) (h' : Cw κ W S' φ) :
    Cw ι W (S + S') (fun v => φ (F v)) := Cmp.comp h h'

theorem Cw.ofBits {ι : Type} {W s : ℕ} {φ : (ι → Bool) → BitVec W}
    (h : ∀ i : Fin W, Cb ι s (fun v => (φ v).getLsbD i.val)) : Cw ι W (W * s) φ := by
  have := Cmp.ofBits (F := fun v (i : Fin W) => (φ v).getLsbD i.val) h
  rw [Fintype.card_fin] at this
  exact this

theorem Cw.const {ι : Type} {W : ℕ} (c : BitVec W) : Cw ι W W (fun _ => c) := by
  have := Cw.ofBits (ι := ι) (φ := fun _ => c) (s := 1) (fun i => Cb.const _)
  rw [Nat.mul_one] at this
  exact this

theorem fb_addcore (W : ℕ) (c0 : Bool) :
    Cmp (Fin W ⊕ Fin W) (Fin W) (13 * (W + 1))
      (fun u i => (bv (fun j => u (Sum.inl j)) + bv (fun j => u (Sum.inr j)) +
        BitVec.setWidth W (BitVec.ofBool c0)).getLsbD i.val) := by
  have hch := Cmp.chain (ι := Fin W ⊕ Fin W) (σ := Unit) W 5
    (fun i u _ => BitVec.carry i (bv (fun j => u (Sum.inl j))) (bv (fun j => u (Sum.inr j))) c0)
    (fun i w _ => if h : i < W then
      ((w (Sum.inl (Sum.inl ⟨i, h⟩)) && w (Sum.inl (Sum.inr ⟨i, h⟩)) ||
        w (Sum.inl (Sum.inl ⟨i, h⟩)) && w (Sum.inr ())) ||
        w (Sum.inl (Sum.inr ⟨i, h⟩)) && w (Sum.inr ())) else false)
    (by
      refine Cmp.mono (Cmp.congr (Cb.const c0) ?_) (by omega)
      intro v k
      cases c0 <;> simp [BitVec.carry, Nat.mod_one])
    (by
      intro i hi
      have h := Cb.or (Cb.or (Cb.and (Cb.var (ι := (Fin W ⊕ Fin W) ⊕ Unit) (Sum.inl (Sum.inl ⟨i, hi⟩)))
          (Cb.var (Sum.inl (Sum.inr ⟨i, hi⟩))))
        (Cb.and (Cb.var (Sum.inl (Sum.inl ⟨i, hi⟩))) (Cb.var (Sum.inr ()))))
        (Cb.and (Cb.var (Sum.inl (Sum.inr ⟨i, hi⟩))) (Cb.var (Sum.inr ())))
      refine Cmp.mono (Cmp.congr h ?_) (by omega)
      intro v k
      simp [hi])
    (by
      intro i hi u
      funext k
      have hx : (bv (fun j => u (Sum.inl j))).getLsbD i = u (Sum.inl ⟨i, hi⟩) :=
        getLsbD_bv (fun j => u (Sum.inl j)) ⟨i, hi⟩
      have hy : (bv (fun j => u (Sum.inr j))).getLsbD i = u (Sum.inr ⟨i, hi⟩) :=
        getLsbD_bv (fun j => u (Sum.inr j)) ⟨i, hi⟩
      rw [BitVec.carry_succ, hx, hy]
      simp only [dite_true, hi, Sum.elim_inl, Sum.elim_inr, Bool.atLeastTwo])
  have hk := Cmp.keep hch
  have hb : Cmp ((Fin W ⊕ Fin W) ⊕ Fin (W + 1) × Unit) (Fin W) (Fintype.card (Fin W) * 8)
      (fun w i => xor (w (Sum.inl (Sum.inl i)))
        (xor (w (Sum.inl (Sum.inr i))) (w (Sum.inr ((⟨i.val, by omega⟩ : Fin (W + 1)), ()))))) := by
    apply Cmp.ofBits
    intro i
    exact Cb.mono (Cb.xor (Cb.var (Sum.inl (Sum.inl i)))
      (Cb.xor (Cb.var (Sum.inl (Sum.inr i))) (Cb.var (Sum.inr ((⟨i.val, by omega⟩ : Fin (W + 1)), ()))))) (by omega)
  refine Cmp.mono (Cmp.congr (Cmp.comp hk hb) ?_) (by rw [Fintype.card_fin]; omega)
  intro v i
  rw [BitVec.getLsbD_add_add_bool i.isLt]
  have hx : (bv (fun j => v (Sum.inl j))).getLsbD i.val = v (Sum.inl i) :=
    getLsbD_bv (fun j => v (Sum.inl j)) i
  have hy : (bv (fun j => v (Sum.inr j))).getLsbD i.val = v (Sum.inr i) :=
    getLsbD_bv (fun j => v (Sum.inr j)) i
  rw [hx, hy]
  rfl

theorem fb_adc {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (c0 : Bool)
    (h : Cw ι W S φ) (h' : Cw ι W S' ψ) :
    Cw ι W (S + S' + 13 * (W + 1))
      (fun v => φ v + ψ v + BitVec.setWidth W (BitVec.ofBool c0)) := by
  refine Cmp.congr (Cmp.comp (Cmp.pair h h') (fb_addcore W c0)) ?_
  intro v i
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [bv_getLsbD, bv_getLsbD]

theorem fb_not {ι : Type} {W S : ℕ} {φ : (ι → Bool) → BitVec W} (h : Cw ι W S φ) :
    Cw ι W (S + W) (fun v => ~~~ φ v) := by
  have hb : Cmp (Fin W) (Fin W) (Fintype.card (Fin W) * 1) (fun u i => !u i) := by
    apply Cmp.ofBits
    intro i
    exact Cb.mono (Cb.not (Cb.var i)) (by omega)
  refine Cmp.mono (Cmp.congr (Cmp.comp h hb) ?_) (by rw [Fintype.card_fin]; omega)
  intro v i
  simp

theorem Cw.add {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (h' : Cw ι W S' ψ) : Cw ι W (S + S' + 20 * (W + 1)) (fun v => φ v + ψ v) := by
  refine Cw.mono (Cw.congr (fb_adc false h h') ?_) (by omega)
  intro v
  simp

theorem fb_add13 {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (h' : Cw ι W S' ψ) : Cw ι W (S + S' + 13 * (W + 1)) (fun v => φ v + ψ v) := by
  refine Cw.congr (fb_adc false h h') ?_
  intro v
  simp

theorem fb_sub_eq {W : ℕ} (x y : BitVec W) :
    x + ~~~ y + BitVec.setWidth W (BitVec.ofBool true) = x - y := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp

theorem Cw.sub {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (h' : Cw ι W S' ψ) : Cw ι W (S + S' + 20 * (W + 1)) (fun v => φ v - ψ v) := by
  refine Cw.mono (Cw.congr (fb_adc true h (fb_not h')) ?_) (by omega)
  intro v
  exact fb_sub_eq _ _

theorem Cw.neg {ι : Type} {W S : ℕ} {φ : (ι → Bool) → BitVec W} (h : Cw ι W S φ) :
    Cw ι W (S + 20 * (W + 1)) (fun v => - φ v) := by
  refine Cw.mono (Cw.congr (fb_adc true (Cw.const (ι := ι) (0 : BitVec W)) (fb_not h)) ?_)
    (by omega)
  intro v
  rw [fb_sub_eq]
  simp

theorem fb_term (W k : ℕ) :
    Cw (Fin W ⊕ Fin W) W W
      (fun u => if (bv (fun j => u (Sum.inr j))).getLsbD k = true
        then bv (fun j => u (Sum.inl j)) <<< k else 0) := by
  have hb := Cw.ofBits (ι := Fin W ⊕ Fin W) (W := W) (s := 1)
    (φ := fun u => if (bv (fun j => u (Sum.inr j))).getLsbD k = true
        then bv (fun j => u (Sum.inl j)) <<< k else 0)
    (by
      intro i
      by_cases hk : k ≤ i.val
      · have hkW : k < W := lt_of_le_of_lt hk i.isLt
        refine Cb.congr (Cb.and (Cb.var (Sum.inr ⟨k, hkW⟩))
          (Cb.var (Sum.inl ⟨i.val - k, by omega⟩))) ?_
        intro v
        have hy : (bv (fun j => v (Sum.inr j))).getLsbD k = v (Sum.inr ⟨k, hkW⟩) :=
          getLsbD_bv (fun j => v (Sum.inr j)) ⟨k, hkW⟩
        have hx : (bv (fun j => v (Sum.inl j))).getLsbD (i.val - k)
            = v (Sum.inl ⟨i.val - k, by omega⟩) :=
          getLsbD_bv (fun j => v (Sum.inl j)) ⟨i.val - k, by omega⟩
        rw [hy]
        cases hv : v (Sum.inr ⟨k, hkW⟩)
        · simp
        · simp [i.isLt, Nat.not_lt.mpr hk]
          rw [← hx, BitVec.getLsbD_eq_getElem]
      · refine Cb.congr (Cb.const false) ?_
        intro v
        have hlt : i.val < k := Nat.lt_of_not_le hk
        split_ifs <;> simp [hlt])
  rw [Nat.mul_one] at hb
  exact hb

theorem fb_mulrec (W s : ℕ) :
    Cw (Fin W ⊕ Fin W) W (W + s * (W + 13 * (W + 1)))
      (fun u => (bv (fun j => u (Sum.inl j))).mulRec (bv (fun j => u (Sum.inr j))) s) := by
  induction s with
  | zero =>
    refine Cw.mono (Cw.congr (fb_term W 0) ?_) (by omega)
    intro v
    rw [BitVec.mulRec_zero_eq]
    simp
  | succ s ih =>
    refine Cw.mono (Cw.congr (fb_add13 ih (fb_term W (s + 1))) ?_) (by
      have := Nat.add_one_mul s (W + 13 * (W + 1)); omega)
    intro v
    rw [BitVec.mulRec_succ_eq]

theorem Cw.mul {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (h' : Cw ι W S' ψ) : Cw ι W (S + S' + 30 * (W + 1) ^ 2) (fun v => φ v * ψ v) := by
  refine Cmp.mono (Cmp.congr (Cmp.comp (Cmp.pair h h') (fb_mulrec W W)) ?_) (by nlinarith)
  intro v i
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [bv_getLsbD, bv_getLsbD, BitVec.getLsbD_mul]

theorem Cw.mux {ι : Type} {W S S' S'' : ℕ} {χ : (ι → Bool) → Bool} {φ ψ : (ι → Bool) → BitVec W}
    (hc : Cb ι S χ) (h : Cw ι W S' φ) (h' : Cw ι W S'' ψ) :
    Cw ι W (S + S' + S'' + 4 * W) (fun v => if χ v then φ v else ψ v) := by
  have hb : Cmp (Unit ⊕ (Fin W ⊕ Fin W)) (Fin W) (Fintype.card (Fin W) * 4)
      (fun w i => if w (Sum.inl ()) then w (Sum.inr (Sum.inl i)) else w (Sum.inr (Sum.inr i))) := by
    apply Cmp.ofBits
    intro i
    exact Cb.mono (Cb.mux (Cb.var (Sum.inl ())) (Cb.var (Sum.inr (Sum.inl i)))
      (Cb.var (Sum.inr (Sum.inr i)))) (by omega)
  refine Cmp.mono (Cmp.congr (Cmp.comp (Cmp.pair hc (Cmp.pair h h')) hb) ?_)
    (by rw [Fintype.card_fin]; omega)
  intro v i
  simp only [Sum.elim_inl, Sum.elim_inr]
  cases χ v <;> simp

theorem Cmp.ofWords {ι α : Type} [Fintype α] {W s : ℕ} {G : (ι → Bool) → α → BitVec W}
    (h : ∀ x : α, Cw ι W s (fun v => G v x)) :
    Cmp ι (α × Fin W) (Fintype.card α * s) (fun v => untab (G v)) := by
  exact Cmp.piU (κ := Fin W) (F := fun x v i => (G v x).getLsbD i.val) h

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

theorem fc_zprod {D : ℕ} (c : Fin D → Bool) (l : List (Fin D)) :
    (l.map (fun q => zmat q (c q))).prod =
      Matrix.diagonal (fun i => if i ∈ l ∧ c i = true then (0 : ZMod 2) else 1) := by
  induction l with
  | nil => simp
  | cons q l ih =>
    rw [List.map_cons, List.prod_cons, ih, zmat, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hiq : i = q
    · subst hiq
      by_cases hc : c i = true
      · simp [hc]
      · simp [hc]
    · simp [hiq]

theorem fc_cols {D : ℕ} (R : Fin D × Fin D → Bool)
    (hpiv : ∀ p, R (p, p) = true → ∀ i, R (i, p) = decide (i = p))
    (hzero : ∀ q, R (q, q) = false → ∀ j, R (q, j) = false)
    (l : List (Fin D × Fin D)) (hnd : l.Nodup) (hne : ∀ e ∈ l, e.1 ≠ e.2) :
    ∀ A : Matrix (Fin D) (Fin D) (ZMod 2),
      (∀ i j, A i j = if i = j then (if R (i, i) then 1 else 0)
        else if (i, j) ∈ l then 0 else if R (i, j) then 1 else 0) →
      A * (l.map (fun e => tmat e.1 e.2 (R e))).prod = mat R := by
  induction l with
  | nil =>
    intro A hA
    simp only [List.map_nil, List.prod_nil, mul_one]
    ext i j
    rw [hA i j]
    by_cases hij : i = j
    · subst hij
      simp [mat]
    · simp [mat, hij]
  | cons e l ih =>
    intro A hA
    obtain ⟨p, q⟩ := e
    have hpq : p ≠ q := hne (p, q) (List.mem_cons_self)
    have hnotin : (p, q) ∉ l := (List.nodup_cons.1 hnd).1
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    apply ih (List.nodup_cons.1 hnd).2 (fun e' h' => hne e' (List.mem_cons_of_mem _ h'))
    have hkey : ∀ a, a ≠ p → R (p, q) = true → A a p = 0 := by
      intro a hap hR
      have hpp : R (p, p) = true := by
        by_contra h
        have := hzero p (by simpa using h) q
        rw [this] at hR
        exact absurd hR (by simp)
      have hcol := hpiv p hpp a
      rw [hA a p, if_neg hap]
      split
      · rfl
      · rw [hcol]
        simp [hap]
    intro i j
    by_cases hjq : j = q
    · subst hjq
      rw [tmat, Matrix.mul_transvection_apply_same]
      by_cases hip : i = p
      · subst hip
        rw [hA i j, if_neg hpq, if_pos (List.mem_cons_self), hA i i, if_pos rfl,
          if_neg hpq, if_neg hnotin]
        by_cases hR : R (i, j) = true
        · have hpp : R (i, i) = true := by
            by_contra h
            have := hzero i (by simpa using h) j
            rw [this] at hR
            exact absurd hR (by simp)
          simp [hR, hpp]
        · simp [hR]
      · have hz : (if R (p, j) = true then (1 : ZMod 2) else 0) * A i p = 0 := by
          by_cases hR : R (p, j) = true
          · rw [hkey i hip hR]
            simp
          · simp [hR]
        rw [hz, add_zero, hA i j]
        have hmem : ((i, j) ∈ (p, j) :: l) ↔ (i, j) ∈ l := by
          rw [List.mem_cons]
          constructor
          · rintro (h | h)
            · exact absurd (Prod.ext_iff.1 h).1 hip
            · exact h
          · exact Or.inr
        simp only [hmem]
    · rw [tmat, Matrix.mul_transvection_apply_of_ne _ _ _ _ hjq, hA i j]
      have hmem : ((i, j) ∈ (p, q) :: l) ↔ (i, j) ∈ l := by
        rw [List.mem_cons]
        constructor
        · rintro (h | h)
          · exact absurd (Prod.ext_iff.1 h).2 hjq
          · exact h
        · exact Or.inr
      simp only [hmem]

theorem fc_offdiag_nodup (D : ℕ) : (offdiag D).Nodup := by
  unfold offdiag
  apply List.Nodup.filter
  exact (List.nodup_finRange D).product (List.nodup_finRange D)

theorem fc_mem_offdiag {D : ℕ} (e : Fin D × Fin D) : e ∈ offdiag D ↔ e.1 ≠ e.2 := by
  unfold offdiag
  rw [List.mem_filter]
  constructor
  · intro h
    simpa using h.2
  · intro h
    refine ⟨?_, by simpa using h⟩
    rw [List.mem_flatMap]
    exact ⟨e.1, List.mem_finRange _, List.mem_map.2 ⟨e.2, List.mem_finRange _, rfl⟩⟩

theorem gj_final {D : ℕ} (M : Fin D × Fin D → Bool) :
    mat (gj D M) =
      ((List.finRange D).map (fun q => zmat q (!(gj D M) (q, q)))).prod *
      ((offdiag D).map (fun e => tmat e.1 e.2 ((gj D M) e))).prod := by
  rw [fc_zprod (fun q => !(gj D M) (q, q))]
  symm
  apply fc_cols (gj D M) (gj_pivcol M) (gj_zerorow M) (offdiag D) (fc_offdiag_nodup D)
    (fun e he => (fc_mem_offdiag e).1 he)
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, if_pos rfl]
    cases gj D M (i, i) <;> simp
  · rw [Matrix.diagonal_apply_ne _ hij, if_neg hij, if_pos ((fc_mem_offdiag (i, j)).2 hij)]

def phiCost (D sE sZ : ℕ) : ℕ := 4 * (D + 1) ^ 2 * (sE + sZ + 16 * (D + 1) ^ 2)

def fd_step {D : ℕ} {τ : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (e : Bool × Fin D × Fin D) (v : (Fin D × Fin D) ⊕ τ → Bool) : (Fin D × Fin D) ⊕ τ → Bool :=
  Sum.elim (gjStep e (fun p => v (Sum.inl p)))
    (Φ (tmat (gjT e) (gjS e) (gjCtl e (fun p => v (Sum.inl p)))) (fun k => v (Sum.inr k)))

def fd_stepG {D : ℕ} {τ α : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (g : α → (Fin D × Fin D → Bool) → Matrix (Fin D) (Fin D) (ZMod 2))
    (x : α) (v : (Fin D × Fin D) ⊕ τ → Bool) : (Fin D × Fin D) ⊕ τ → Bool :=
  Sum.elim (fun p => v (Sum.inl p))
    (Φ (g x (fun p => v (Sum.inl p))) (fun k => v (Sum.inr k)))

theorem fd_fold1 {D : ℕ} {τ : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (hmul : ∀ A B T, Φ (A * B) T = Φ B (Φ A T)) :
    ∀ (L : List (Bool × Fin D × Fin D)), (∀ e ∈ L, e.2.1 ≠ e.2.2) →
    ∀ v : (Fin D × Fin D) ⊕ τ → Bool,
      (fun p => (L.foldl (fun acc e => fd_step Φ e acc) v) (Sum.inl p)) =
        L.foldl (fun M e => gjStep e M) (fun p => v (Sum.inl p)) ∧
      Φ (mat (fun p => v (Sum.inl p))) (fun k => v (Sum.inr k)) =
        Φ (mat (fun p => (L.foldl (fun acc e => fd_step Φ e acc) v) (Sum.inl p)))
          (fun k => (L.foldl (fun acc e => fd_step Φ e acc) v) (Sum.inr k)) := by
  intro L
  induction L with
  | nil => intro _ v; exact ⟨rfl, rfl⟩
  | cons e L ih =>
    intro hL v
    have he := hL e (List.mem_cons_self)
    obtain ⟨h1, h2⟩ := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) (fd_step Φ e v)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, ← h2]
    rw [gjStep_mat e he (fun p => v (Sum.inl p)), hmul]
    rfl

theorem fd_foldG {D : ℕ} {τ α : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (h1 : ∀ T, Φ 1 T = T) (hmul : ∀ A B T, Φ (A * B) T = Φ B (Φ A T))
    (g : α → (Fin D × Fin D → Bool) → Matrix (Fin D) (Fin D) (ZMod 2)) :
    ∀ (L : List α) (v : (Fin D × Fin D) ⊕ τ → Bool),
      (fun p => (L.foldl (fun acc x => fd_stepG Φ g x acc) v) (Sum.inl p)) =
        (fun p => v (Sum.inl p)) ∧
      (fun k => (L.foldl (fun acc x => fd_stepG Φ g x acc) v) (Sum.inr k)) =
        Φ ((L.map (fun x => g x (fun p => v (Sum.inl p)))).prod) (fun k => v (Sum.inr k)) := by
  intro L
  induction L with
  | nil => intro v; exact ⟨rfl, by simp [h1]⟩
  | cons x L ih =>
    intro v
    obtain ⟨h2, h3⟩ := ih (fd_stepG Φ g x v)
    refine ⟨h2, ?_⟩
    rw [List.foldl_cons, h3, List.map_cons, List.prod_cons, hmul]
    rfl

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

theorem fd_TS_ne {D : ℕ} (e : Bool × Fin D × Fin D) (he : e.2.1 ≠ e.2.2) : gjT e ≠ gjS e := by
  rcases e with ⟨k, p, i⟩
  cases k
  · simpa [gjT, gjS] using he
  · simpa [gjT, gjS] using (Ne.symm he)

theorem fd_cost_le (D sE sZ : ℕ) :
    Fintype.card (Fin D × Fin D) * 11 + (6 + 0 + sE) ≤ sE + sZ + 16 * (D + 1) ^ 2 := by
  have h : Fintype.card (Fin D × Fin D) = D * D := by simp
  rw [h]
  nlinarith [Nat.zero_le D, Nat.zero_le sZ]

theorem fd_cmp_step {D : ℕ} {τ : Type} [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool)) (sE sZ : ℕ)
    (hE : ∀ t s : Fin D, t ≠ s →
      Cmp (Unit ⊕ τ) τ sE (fun v => Φ (tmat t s (v (Sum.inl ()))) (fun k => v (Sum.inr k))))
    (e : Bool × Fin D × Fin D) (he : e.2.1 ≠ e.2.2) :
    Cmp ((Fin D × Fin D) ⊕ τ) ((Fin D × Fin D) ⊕ τ) (sE + sZ + 16 * (D + 1) ^ 2)
      (fd_step Φ e) := by
  have hm : Cmp ((Fin D × Fin D) ⊕ τ) (Fin D × Fin D) (Fintype.card (Fin D × Fin D) * 11)
      (fun v => gjStep e (fun p => v (Sum.inl p))) :=
    Cmp.ofBits (fun p => fd_bit e p)
  have hc : Cmp ((Fin D × Fin D) ⊕ τ) Unit 6
      (fun v _ => gjCtl e (fun p => v (Sum.inl p))) := fd_ctl e
  have ht := Cmp.comp (Cmp.pair hc (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) Sum.inr))
    (hE (gjT e) (gjS e) (fd_TS_ne e he))
  have h := Cmp.pair hm ht
  refine Cmp.mono (Cmp.congr h ?_) (fd_cost_le D sE sZ)
  intro v k
  rfl

theorem fd_cmp_stepZ {D : ℕ} {τ : Type} [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool)) (sE sZ : ℕ)
    (hZ : ∀ q : Fin D,
      Cmp (Unit ⊕ τ) τ sZ (fun v => Φ (zmat q (v (Sum.inl ()))) (fun k => v (Sum.inr k))))
    (q : Fin D) :
    Cmp ((Fin D × Fin D) ⊕ τ) ((Fin D × Fin D) ⊕ τ) (sE + sZ + 16 * (D + 1) ^ 2)
      (fd_stepG Φ (fun (q : Fin D) M => zmat q (!M (q, q))) q) := by
  have hc : Cmp ((Fin D × Fin D) ⊕ τ) Unit (0 + 1)
      (fun v _ => !v (Sum.inl (q, q))) := Cb.not (Cb.var (Sum.inl (q, q)))
  have ht := Cmp.comp (Cmp.pair hc (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) Sum.inr))
    (hZ q)
  have h := Cmp.pair (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := Fin D × Fin D) Sum.inl) ht
  refine Cmp.mono (Cmp.congr h ?_) (by nlinarith [Nat.zero_le D, Nat.zero_le sE])
  intro v k
  rfl

theorem fd_cmp_stepT {D : ℕ} {τ : Type} [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool)) (sE sZ : ℕ)
    (hE : ∀ t s : Fin D, t ≠ s →
      Cmp (Unit ⊕ τ) τ sE (fun v => Φ (tmat t s (v (Sum.inl ()))) (fun k => v (Sum.inr k))))
    (e : Fin D × Fin D) (he : e.1 ≠ e.2) :
    Cmp ((Fin D × Fin D) ⊕ τ) ((Fin D × Fin D) ⊕ τ) (sE + sZ + 16 * (D + 1) ^ 2)
      (fd_stepG Φ (fun (e : Fin D × Fin D) M => tmat e.1 e.2 (M e)) e) := by
  have hc : Cmp ((Fin D × Fin D) ⊕ τ) Unit 0
      (fun v _ => v (Sum.inl e)) := Cb.var (Sum.inl e)
  have ht := Cmp.comp (Cmp.pair hc (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) Sum.inr))
    (hE e.1 e.2 he)
  have h := Cmp.pair (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := Fin D × Fin D) Sum.inl) ht
  refine Cmp.mono (Cmp.congr h ?_) (by nlinarith [Nat.zero_le D, Nat.zero_le sZ])
  intro v k
  rfl

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

theorem fd_offdiag_len (D : ℕ) : (offdiag D).length ≤ D * D := by
  have h := fd_flatMap_len D (fun p : Fin D => (List.finRange D).map fun q => (p, q)) (by
      intro p
      simp) (List.finRange D)
  have h2 : (List.finRange D).length = D := List.length_finRange
  rw [h2] at h
  exact le_trans (List.length_filter_le _ _) h

theorem fd_offdiag_ne {D : ℕ} (e : Fin D × Fin D) (he : e ∈ offdiag D) : e.1 ≠ e.2 := by
  unfold offdiag at he
  have := (List.mem_filter.mp he).2
  simpa using this

theorem cmp_phi (D : ℕ) (τ : Type) [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (h1 : ∀ T, Φ 1 T = T) (hmul : ∀ A B T, Φ (A * B) T = Φ B (Φ A T))
    (sE sZ : ℕ)
    (hE : ∀ t s : Fin D, t ≠ s →
      Cmp (Unit ⊕ τ) τ sE (fun v => Φ (tmat t s (v (Sum.inl ()))) (fun k => v (Sum.inr k))))
    (hZ : ∀ q : Fin D,
      Cmp (Unit ⊕ τ) τ sZ (fun v => Φ (zmat q (v (Sum.inl ()))) (fun k => v (Sum.inr k)))) :
    Cmp ((Fin D × Fin D) ⊕ τ) τ (phiCost D sE sZ)
      (fun v => Φ (mat (fun p => v (Sum.inl p))) (fun k => v (Sum.inr k))) := by
  have c1 := Cmp.foldl (sched D) (fd_step Φ)
    (fun e he => fd_cmp_step Φ sE sZ hE e (sched_ne e he))
  have c2 := Cmp.foldl (List.finRange D)
    (fd_stepG Φ (fun (q : Fin D) M => zmat q (!M (q, q))))
    (fun q _ => fd_cmp_stepZ Φ sE sZ hZ q)
  have c3 := Cmp.foldl (offdiag D)
    (fd_stepG Φ (fun (e : Fin D × Fin D) M => tmat e.1 e.2 (M e)))
    (fun e he => fd_cmp_stepT Φ sE sZ hE e (fd_offdiag_ne e he))
  have c := Cmp.comp (Cmp.comp (Cmp.comp c1 c2) c3)
    (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) Sum.inr)
  refine Cmp.mono (Cmp.congr c ?_) ?_
  · intro v k
    obtain ⟨hM1, hT1⟩ := fd_fold1 Φ hmul (sched D) (fun e he => sched_ne e he) v
    obtain ⟨hM2, hT2⟩ := fd_foldG Φ h1 hmul (fun (q : Fin D) M => zmat q (!M (q, q)))
      (List.finRange D) ((sched D).foldl (fun acc e => fd_step Φ e acc) v)
    obtain ⟨_, hT3⟩ := fd_foldG Φ h1 hmul (fun (e : Fin D × Fin D) M => tmat e.1 e.2 (M e))
      (offdiag D) ((List.finRange D).foldl
        (fun acc x => fd_stepG Φ (fun (q : Fin D) M => zmat q (!M (q, q))) x acc)
        ((sched D).foldl (fun acc e => fd_step Φ e acc) v))
    refine (congrFun hT3 k).trans ?_
    rw [hM2, hT2, ← hmul, hT1, hM1]
    have hg : (sched D).foldl (fun M e => gjStep e M) (fun p => v (Sum.inl p)) =
        gj D (fun p => v (Sum.inl p)) := rfl
    rw [hg, ← gj_final]
  · have a1 := fd_sched_len D
    have a2 := fd_offdiag_len D
    have a3 : (List.finRange D).length = D := List.length_finRange
    rw [a3]
    unfold phiCost
    generalize sE + sZ + 16 * (D + 1) ^ 2 = s
    have : (sched D).length + D + (offdiag D).length ≤ 4 * (D + 1) ^ 2 := by nlinarith
    calc (sched D).length * s + D * s + (offdiag D).length * s + 0
        = ((sched D).length + D + (offdiag D).length) * s := by ring
      _ ≤ 4 * (D + 1) ^ 2 * s := Nat.mul_le_mul_right s this

def tcost (d k W : ℕ) : ℕ := 2 ^ 9 * (d + k + 2) ^ 4 * (W + 1) * 2 ^ (max d k)

def fp_ext (n : ℕ) {k : ℕ} (x : V k) : V n := fun j => if h : j.val < k then x ⟨j.val, h⟩ else 0

def fp_res {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : V n) : V k := fun j => x ⟨j.val, by omega⟩

def fp_pad (n : ℕ) {d k : ℕ} (B : Fin d × Fin k → Bool) : Fin n × Fin n → Bool := fun p =>
  if h : p.1.val < d ∧ p.2.val < k then B (⟨p.1.val, h.1⟩, ⟨p.2.val, h.2⟩) else false

theorem fp_res_ext {n k : ℕ} (hk : k ≤ n) (x : V k) : fp_res k hk (fp_ext n x) = x := by
  funext j
  simp [fp_res, fp_ext]

theorem fp_ext_inj (n : ℕ) {k : ℕ} (hk : k ≤ n) : Function.Injective (fp_ext n (k := k)) := by
  intro x y h
  have := congrArg (fp_res k hk) h
  rwa [fp_res_ext, fp_res_ext] at this

theorem fp_pad_mulVec {n d k : ℕ} (hk : k ≤ n) (B : Fin d × Fin k → Bool)
    (lam : V k) :
    (mat (fp_pad n B)).mulVec (fp_ext n lam) = fp_ext n ((mat B).mulVec lam) := by
  funext a
  by_cases ha : a.val < d
  · have e1 : fp_ext n ((mat B).mulVec lam) a = (mat B).mulVec lam ⟨a.val, ha⟩ := by
      simp [fp_ext, ha]
    rw [e1]
    unfold Matrix.mulVec dotProduct
    symm
    apply Fintype.sum_of_injective (fun j : Fin k => (⟨j.val, by omega⟩ : Fin n))
    · intro x y h
      apply Fin.ext
      simpa using congrArg Fin.val h
    · intro b hb
      have hb' : ¬ b.val < k := by
        intro h
        exact hb ⟨⟨b.val, h⟩, rfl⟩
      simp [fp_ext, hb']
    · intro j
      simp [mat, fp_pad, fp_ext, ha]
  · have e1 : fp_ext n ((mat B).mulVec lam) a = 0 := by
      simp [fp_ext, ha]
    rw [e1]
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_eq_zero
    intro b _
    simp [mat, fp_pad, ha]

theorem fp_cardV (n : ℕ) : Fintype.card (V n) = 2 ^ n := by
  simp [V, ZMod.card]

theorem fp_arith (Q X A B Cc Y : ℕ) (hA : A ≤ Q) (hB : B ≤ X) (hC : Cc ≤ Q) (hY : Y ≤ 29 * X)
    (hQ : 1 ≤ Q) (hX : 1 ≤ X) : A + B + 4 * Cc * (Y + 16 * Cc) ≤ 512 * (Q * Q) * X := by
  have h1 : 4 * Cc * (Y + 16 * Cc) ≤ 4 * Q * (29 * X + 16 * Q) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : Q ≤ Q * X := Nat.le_mul_of_pos_right _ hX
  have h3 : Q * X ≤ Q * Q * X := by
    have : Q ≤ Q * Q := Nat.le_mul_of_pos_right _ hQ
    exact Nat.mul_le_mul_right _ this
  have h4 : X ≤ Q * X := Nat.le_mul_of_pos_left _ hQ
  have h5 : Q * Q ≤ Q * Q * X := Nat.le_mul_of_pos_right _ hX
  nlinarith [h1, h2, h3, h4, h5]

theorem fp_bound (d k W A B Y : ℕ) (hA : A ≤ max d k * max d k)
    (hB : B ≤ 2 ^ (max d k) * W) (hY : Y ≤ 29 * ((W + 1) * 2 ^ (max d k))) :
    A + B + phiCost (max d k) Y 0 ≤ tcost d k W := by
  unfold phiCost tcost
  have hp : 1 ≤ 2 ^ (max d k) := Nat.one_le_two_pow
  have hm : max d k + 1 ≤ d + k + 2 := by omega
  have hC : (max d k + 1) ^ 2 ≤ (d + k + 2) ^ 2 := Nat.pow_le_pow_left hm 2
  have hA' : A ≤ (d + k + 2) ^ 2 := by
    have h0 : max d k * max d k = (max d k) ^ 2 := (sq _).symm
    have : (max d k) ^ 2 ≤ (max d k + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ _) 2
    omega
  have hB' : B ≤ (W + 1) * 2 ^ (max d k) := by
    have : 2 ^ (max d k) * W ≤ (W + 1) * 2 ^ (max d k) := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  have hQ : 1 ≤ (d + k + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hX : 1 ≤ (W + 1) * 2 ^ (max d k) := Nat.mul_pos (by omega) hp
  have := fp_arith ((d + k + 2) ^ 2) ((W + 1) * 2 ^ (max d k)) A B ((max d k + 1) ^ 2) Y
    hA' hB' hC hY hQ hX
  have e : 2 ^ 9 * (d + k + 2) ^ 4 * (W + 1) * 2 ^ (max d k) =
      512 * ((d + k + 2) ^ 2 * (d + k + 2) ^ 2) * ((W + 1) * 2 ^ (max d k)) := by ring
  rw [e]
  simpa using this

theorem fp_sum_eq {n W : ℕ} (f : V n → BitVec W) (z : V n) :
    (∑ x : V n, if x = z then f x else 0) = f z := by
  rw [Finset.sum_ite_eq' Finset.univ z f]
  simp

def fp_pullPhi (n W : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2)) (T : V n × Fin W → Bool) :
    V n × Fin W → Bool :=
  untab (fun x : V n => tab T (M.mulVec x))

def fp_pushPhi (n W : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2)) (T : V n × Fin W → Bool) :
    V n × Fin W → Bool :=
  untab (fun z : V n => ∑ x : V n, if M.transpose.mulVec x = z then tab T x else 0)

theorem fp_pull_one (n W : ℕ) (T : V n × Fin W → Bool) : fp_pullPhi n W 1 T = T := by
  unfold fp_pullPhi
  simp only [Matrix.one_mulVec]
  exact untab_tab T

theorem fp_pull_mul (n W : ℕ) (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (T : V n × Fin W → Bool) :
    fp_pullPhi n W (A * B) T = fp_pullPhi n W B (fp_pullPhi n W A T) := by
  unfold fp_pullPhi
  rw [tab_untab]
  simp only [Matrix.mulVec_mulVec]

theorem fp_pull_cw (n W : ℕ) (A : Bool → Matrix (Fin n) (Fin n) (ZMod 2)) (x : V n) :
    Cw (Unit ⊕ (V n × Fin W)) W (4 * W)
      (fun v => tab (fun k => v (Sum.inr k)) ((A (v (Sum.inl ()))).mulVec x)) := by
  have h := Cw.mux (Cb.var (Sum.inl () : Unit ⊕ (V n × Fin W)))
    (Cw.var (fun i : Fin W => (Sum.inr ((A true).mulVec x, i) : Unit ⊕ (V n × Fin W))))
    (Cw.var (fun i : Fin W => (Sum.inr ((A false).mulVec x, i) : Unit ⊕ (V n × Fin W))))
  refine (h.mono (by omega)).congr ?_
  intro v
  cases hv : v (Sum.inl ()) <;> simp [tab]

theorem fp_pull_step (n W : ℕ) (A : Bool → Matrix (Fin n) (Fin n) (ZMod 2)) :
    Cmp (Unit ⊕ (V n × Fin W)) (V n × Fin W) (Fintype.card (V n) * (4 * W))
      (fun v => fp_pullPhi n W (A (v (Sum.inl ()))) (fun k => v (Sum.inr k))) := by
  unfold fp_pullPhi
  exact Cmp.ofWords (fun x => fp_pull_cw n W A x)

theorem fp_push_one (n W : ℕ) (T : V n × Fin W → Bool) : fp_pushPhi n W 1 T = T := by
  unfold fp_pushPhi
  simp only [Matrix.transpose_one, Matrix.one_mulVec]
  have : (fun z : V n => ∑ x : V n, if x = z then tab T x else 0) = tab T := by
    funext z
    exact fp_sum_eq _ z
  rw [this]
  exact untab_tab T

theorem fp_push_mul (n W : ℕ) (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (T : V n × Fin W → Bool) :
    fp_pushPhi n W (A * B) T = fp_pushPhi n W B (fp_pushPhi n W A T) := by
  unfold fp_pushPhi
  rw [tab_untab]
  congr 1
  funext z
  have e : ∀ y : V n, (if B.transpose.mulVec y = z then
      (∑ x : V n, if A.transpose.mulVec x = y then tab T x else 0) else 0) =
      ∑ x : V n, if A.transpose.mulVec x = y then
        (if B.transpose.mulVec y = z then tab T x else 0) else 0 := by
    intro y
    by_cases h : B.transpose.mulVec y = z
    · simp [h]
    · simp [h]
  simp only [e]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_ite_eq]
  simp [Matrix.transpose_mul, Matrix.mulVec_mulVec]

theorem fp_invol_sum {n W : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (hA : A * A = 1)
    (f : V n → BitVec W) (z : V n) :
    (∑ x : V n, if A.mulVec x = z then f x else 0) = f (A.mulVec z) := by
  have key : ∀ x : V n, (A.mulVec x = z) ↔ (x = A.mulVec z) := by
    intro x
    constructor
    · intro h
      rw [← h, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
    · intro h
      rw [h, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  simp only [key]
  exact fp_sum_eq _ _

theorem fp_tmat_sq {n : ℕ} (t s : Fin n) (hts : t ≠ s) (c : Bool) :
    (tmat t s c).transpose * (tmat t s c).transpose = 1 := by
  rw [← Matrix.transpose_mul]
  unfold tmat
  rw [Matrix.transvection_mul_transvection_same (h := hts)]
  have : ((if c = true then (1 : ZMod 2) else 0) + (if c = true then 1 else 0)) = 0 := by
    cases c
    · simp
    · exact (by decide : (1 : ZMod 2) + 1 = 0)
  rw [this, Matrix.transvection_zero, Matrix.transpose_one]

theorem fp_push_tmat (n W : ℕ) (t s : Fin n) (hts : t ≠ s) (c : Bool) (T : V n × Fin W → Bool) :
    fp_pushPhi n W (tmat t s c) T = fp_pullPhi n W ((tmat t s c).transpose) T := by
  unfold fp_pushPhi fp_pullPhi
  congr 1
  funext z
  exact fp_invol_sum _ (fp_tmat_sq t s hts c) _ z

theorem fp_zmat_false {n : ℕ} (q : Fin n) : zmat q false = 1 := by
  unfold zmat
  simp

theorem fp_zmat_true_mulVec {n : ℕ} (q : Fin n) (x : V n) :
    (zmat q true).transpose.mulVec x = Function.update x q 0 := by
  unfold zmat
  rw [Matrix.diagonal_transpose]
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : i = q
  · subst h
    simp
  · simp [h]

theorem fp_zsum {n W : ℕ} (q : Fin n) (f : V n → BitVec W) (z : V n) :
    (∑ x : V n, if Function.update x q 0 = z then f x else 0) =
      if z q = 0 then f z + f (Function.update z q 1) else 0 := by
  have two : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  split_ifs with hz
  · have hne : z ≠ Function.update z q 1 := by
      intro h
      have := congrFun h q
      rw [Function.update_self, hz] at this
      exact absurd this (by decide)
    have key : ∀ x : V n, (if Function.update x q 0 = z then f x else 0) =
        (if x = z then f x else 0) + (if x = Function.update z q 1 then f x else 0) := by
      intro x
      by_cases h1 : x = z
      · subst h1
        have : Function.update x q 0 = x := by
          rw [← hz]
          exact Function.update_eq_self q x
        rw [if_pos this, if_pos rfl, if_neg hne, add_zero]
      · by_cases h2 : x = Function.update z q 1
        · subst h2
          have : Function.update (Function.update z q 1) q 0 = z := by
            rw [Function.update_idem, ← hz]
            exact Function.update_eq_self q z
          rw [if_pos this, if_neg h1, if_pos rfl, zero_add]
        · have : ¬ Function.update x q 0 = z := by
            intro h
            rcases two (x q) with h0 | h0
            · apply h1
              funext i
              by_cases hi : i = q
              · subst hi
                rw [h0, hz]
              · have := congrFun h i
                rwa [Function.update_of_ne hi] at this
            · apply h2
              funext i
              by_cases hi : i = q
              · subst hi
                rw [h0, Function.update_self]
              · have := congrFun h i
                rw [Function.update_of_ne hi] at this
                rw [Function.update_of_ne hi, this]
          rw [if_neg this, if_neg h1, if_neg h2, add_zero]
    simp only [key]
    rw [Finset.sum_add_distrib, fp_sum_eq, fp_sum_eq]
  · apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    intro h
    apply hz
    rw [← h, Function.update_self]

theorem fp_push_z_cw (n W : ℕ) (q : Fin n) (z : V n) :
    Cw (Unit ⊕ (V n × Fin W)) W (25 * (W + 1))
      (fun v => ∑ x : V n, if (zmat q (v (Sum.inl ()))).transpose.mulVec x = z
        then tab (fun k => v (Sum.inr k)) x else 0) := by
  by_cases hz : z q = 0
  · have h := Cw.mux (Cb.var (Sum.inl () : Unit ⊕ (V n × Fin W)))
      (Cw.add
        (Cw.var (fun i : Fin W => (Sum.inr (z, i) : Unit ⊕ (V n × Fin W))))
        (Cw.var (fun i : Fin W =>
          (Sum.inr (Function.update z q 1, i) : Unit ⊕ (V n × Fin W)))))
      (Cw.var (fun i : Fin W => (Sum.inr (z, i) : Unit ⊕ (V n × Fin W))))
    refine (h.mono (by omega)).congr ?_
    intro v
    cases hv : v (Sum.inl ())
    · simp only [fp_zmat_false, Matrix.transpose_one, Matrix.one_mulVec, fp_sum_eq]
      simp [tab]
    · simp only [fp_zmat_true_mulVec, fp_zsum, hz]
      simp [tab]
  · have h := Cw.mux (Cb.var (Sum.inl () : Unit ⊕ (V n × Fin W)))
      (Cw.const (ι := Unit ⊕ (V n × Fin W)) (0 : BitVec W))
      (Cw.var (fun i : Fin W => (Sum.inr (z, i) : Unit ⊕ (V n × Fin W))))
    refine (h.mono (by omega)).congr ?_
    intro v
    cases hv : v (Sum.inl ())
    · simp only [fp_zmat_false, Matrix.transpose_one, Matrix.one_mulVec, fp_sum_eq]
      simp [tab]
    · simp only [fp_zmat_true_mulVec, fp_zsum, hz]
      simp

theorem fp_push_z_step (n W : ℕ) (q : Fin n) :
    Cmp (Unit ⊕ (V n × Fin W)) (V n × Fin W) (Fintype.card (V n) * (25 * (W + 1)))
      (fun v => fp_pushPhi n W (zmat q (v (Sum.inl ()))) (fun k => v (Sum.inr k))) := by
  unfold fp_pushPhi
  exact Cmp.ofWords (fun z => fp_push_z_cw n W q z)

theorem fp_push_t_step (n W : ℕ) (t s : Fin n) (hts : t ≠ s) :
    Cmp (Unit ⊕ (V n × Fin W)) (V n × Fin W) (Fintype.card (V n) * (4 * W))
      (fun v => fp_pushPhi n W (tmat t s (v (Sum.inl ()))) (fun k => v (Sum.inr k))) := by
  have h := fp_pull_step n W (fun c => (tmat t s c).transpose)
  refine h.congr ?_
  intro v k
  rw [fp_push_tmat n W t s hts]

theorem fp_pad_cb (n : ℕ) {d k : ℕ} (τ : Type) (p : Fin n × Fin n) :
    Cb ((Fin d × Fin k) ⊕ τ) 1 (fun v => fp_pad n (fun e => v (Sum.inl e)) p) := by
  by_cases h : p.1.val < d ∧ p.2.val < k
  · refine ((Cb.var (Sum.inl (⟨p.1.val, h.1⟩, ⟨p.2.val, h.2⟩) :
      (Fin d × Fin k) ⊕ τ)).mono (by omega)).congr ?_
    intro v
    simp [fp_pad, h]
  · refine (Cb.const false).congr ?_
    intro v
    simp only [fp_pad, dif_neg h]

theorem cmp_pull (d k W : ℕ) :
    Cmp ((Fin d × Fin k) ⊕ (V d × Fin W)) (V k × Fin W) (tcost d k W)
      (fun v => untab (fun lam : V k =>
        tab (fun p => v (Sum.inr p)) ((mat (fun p => v (Sum.inl p))).mulVec lam))) := by
  have hd : d ≤ max d k := le_max_left d k
  have hk : k ≤ max d k := le_max_right d k
  have pre : Cmp ((Fin d × Fin k) ⊕ (V d × Fin W))
      ((Fin (max d k) × Fin (max d k)) ⊕ (V (max d k) × Fin W)) _ _ :=
    Cmp.pair
      (Cmp.ofBits (s := 1) (F := fun v p => fp_pad (max d k) (fun e => v (Sum.inl e)) p)
        (fun p => fp_pad_cb (max d k) (V d × Fin W) p))
      (Cmp.wire (fun p : V (max d k) × Fin W =>
        (Sum.inr (fp_res d hd p.1, p.2) : (Fin d × Fin k) ⊕ (V d × Fin W))))
  have mid := cmp_phi (max d k) (V (max d k) × Fin W) (fp_pullPhi (max d k) W)
    (fp_pull_one _ _) (fp_pull_mul _ _)
    (Fintype.card (V (max d k)) * (4 * W)) (Fintype.card (V (max d k)) * (4 * W))
    (fun t s _ => fp_pull_step _ _ (fun c => tmat t s c))
    (fun q => fp_pull_step _ _ (fun c => zmat q c))
  have post := Cmp.wire (ι := V (max d k) × Fin W)
    (fun p : V k × Fin W => (fp_ext (max d k) p.1, p.2))
  have tot := (pre.comp mid).comp post
  refine (tot.mono ?_).congr ?_
  · have hb := fp_bound d k W (max d k * max d k) 0
      (Fintype.card (V (max d k)) * (4 * W) + Fintype.card (V (max d k)) * (4 * W))
      le_rfl (Nat.zero_le _) (by rw [fp_cardV]; nlinarith [Nat.one_le_two_pow (n := max d k)])
    have e : phiCost (max d k) (Fintype.card (V (max d k)) * (4 * W))
        (Fintype.card (V (max d k)) * (4 * W)) =
        phiCost (max d k) (Fintype.card (V (max d k)) * (4 * W) +
          Fintype.card (V (max d k)) * (4 * W)) 0 := by
      unfold phiCost
      ring
    rw [e]
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  · intro v p
    obtain ⟨lam, i⟩ := p
    have e : fp_res d hd ((mat (fp_pad (max d k) (fun e => v (Sum.inl e)))).mulVec
        (fp_ext (max d k) lam)) = (mat (fun p => v (Sum.inl p))).mulVec lam := by
      rw [fp_pad_mulVec hk, fp_res_ext]
    show (bv (fun i => v (Sum.inr (fp_res d hd
      ((mat (fp_pad (max d k) (fun e => v (Sum.inl e)))).mulVec (fp_ext (max d k) lam)), i)))).getLsbD
        i.val = _
    rw [e]
    rfl

theorem fp_bv_false (W : ℕ) : bv (fun _ : Fin W => false) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bv, BitVec.getLsbD_ofFnLE]
  simp

theorem cmp_push (d k W : ℕ) :
    Cmp ((Fin d × Fin k) ⊕ (V k × Fin W)) (V d × Fin W) (tcost d k W)
      (fun v => untab (fun z : V d =>
        ∑ lam : V k, if (mat (fun p => v (Sum.inl p))).mulVec lam = z
          then tab (fun p => v (Sum.inr p)) lam else 0)) := by
  have hd : d ≤ max d k := le_max_left d k
  have hk : k ≤ max d k := le_max_right d k
  have tb : ∀ p : V (max d k) × Fin W, Cb ((Fin d × Fin k) ⊕ (V k × Fin W)) 1
      (fun v => if (∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0)
        then v (Sum.inr (fp_res k hk p.1, p.2)) else false) := by
    intro p
    by_cases h : ∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0
    · refine ((Cb.var (Sum.inr (fp_res k hk p.1, p.2) :
        (Fin d × Fin k) ⊕ (V k × Fin W))).mono (by omega)).congr ?_
      intro v
      rw [if_pos h]
    · refine (Cb.const false).congr ?_
      intro v
      rw [if_neg h]
  have pre : Cmp ((Fin d × Fin k) ⊕ (V k × Fin W))
      ((Fin (max d k) × Fin (max d k)) ⊕ (V (max d k) × Fin W)) _ _ :=
    Cmp.pair
      (Cmp.ofBits (s := 1)
        (F := fun v p => fp_pad (max d k) (fun e => v (Sum.inl e)) (p.2, p.1))
        (fun p => fp_pad_cb (max d k) (V k × Fin W) (p.2, p.1)))
      (Cmp.ofBits (s := 1)
        (F := fun v (p : V (max d k) × Fin W) =>
          if (∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0)
            then v (Sum.inr (fp_res k hk p.1, p.2)) else false) tb)
  have mid := cmp_phi (max d k) (V (max d k) × Fin W) (fp_pushPhi (max d k) W)
    (fp_push_one _ _) (fp_push_mul _ _)
    (Fintype.card (V (max d k)) * (4 * W)) (Fintype.card (V (max d k)) * (25 * (W + 1)))
    (fun t s hts => fp_push_t_step _ _ t s hts)
    (fun q => fp_push_z_step _ _ q)
  have post := Cmp.wire (ι := V (max d k) × Fin W)
    (fun p : V d × Fin W => (fp_ext (max d k) p.1, p.2))
  have tot := (pre.comp mid).comp post
  refine (tot.mono ?_).congr ?_
  · have hb := fp_bound d k W (max d k * max d k) (2 ^ (max d k) * W)
      (Fintype.card (V (max d k)) * (4 * W) + Fintype.card (V (max d k)) * (25 * (W + 1)))
      le_rfl le_rfl (by rw [fp_cardV]; nlinarith [Nat.one_le_two_pow (n := max d k)])
    have e : phiCost (max d k) (Fintype.card (V (max d k)) * (4 * W))
        (Fintype.card (V (max d k)) * (25 * (W + 1))) =
        phiCost (max d k) (Fintype.card (V (max d k)) * (4 * W) +
          Fintype.card (V (max d k)) * (25 * (W + 1))) 0 := by
      unfold phiCost
      ring
    rw [e]
    simp only [Fintype.card_prod, Fintype.card_fin, fp_cardV] at hb ⊢
    omega
  · intro v p
    obtain ⟨z, i⟩ := p
    show (∑ x : V (max d k),
      if (mat (fun p : Fin (max d k) × Fin (max d k) =>
          fp_pad (max d k) (fun e => v (Sum.inl e)) (p.2, p.1))).transpose.mulVec x =
          fp_ext (max d k) z
        then tab (fun p : V (max d k) × Fin W =>
          if (∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0)
            then v (Sum.inr (fp_res k hk p.1, p.2)) else false) x else 0).getLsbD i.val =
      (∑ lam : V k, if (mat (fun p => v (Sum.inl p))).mulVec lam = z
          then tab (fun p => v (Sum.inr p)) lam else 0).getLsbD i.val
    congr 1
    symm
    have hT : (mat (fun p : Fin (max d k) × Fin (max d k) =>
          fp_pad (max d k) (fun e => v (Sum.inl e)) (p.2, p.1))).transpose =
        mat (fp_pad (max d k) (fun e => v (Sum.inl e))) := rfl
    rw [hT]
    apply Fintype.sum_of_injective (fp_ext (max d k)) (fp_ext_inj _ hk)
    · intro x hx
      have hs : ¬ ∀ j : Fin (max d k), k ≤ j.val → x j = 0 := by
        intro h
        apply hx
        refine ⟨fp_res k hk x, ?_⟩
        funext j
        by_cases hj : j.val < k
        · simp [fp_ext, fp_res, hj]
        · simp [fp_ext, hj, h j (by omega)]
      have : tab (fun p : V (max d k) × Fin W =>
          if (∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0)
            then v (Sum.inr (fp_res k hk p.1, p.2)) else false) x = 0 := by
        unfold tab
        simp only [if_neg hs]
        exact fp_bv_false W
      rw [this]
      simp
    · intro lam
      have hs : ∀ j : Fin (max d k), k ≤ j.val → fp_ext (max d k) lam j = 0 := by
        intro j hj
        simp [fp_ext, Nat.not_lt.mpr hj]
      have e1 : tab (fun p : V (max d k) × Fin W =>
          if (∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0)
            then v (Sum.inr (fp_res k hk p.1, p.2)) else false) (fp_ext (max d k) lam) =
          tab (fun p => v (Sum.inr p)) lam := by
        unfold tab
        simp only [if_pos hs, fp_res_ext]
      rw [e1, fp_pad_mulVec hk]
      by_cases h : (mat (fun p => v (Sum.inl p))).mulVec lam = z
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun h' => h (fp_ext_inj _ hd h'))]

def whtCost (d W : ℕ) : ℕ := 2 ^ 7 * (d + 1) * (W + 1) * 2 ^ d

def fe_layer {d W : ℕ} (i : Fin d) (T : V d → BitVec W) : V d → BitVec W :=
  fun xi => T (Function.update xi i 0) + sgn (xi i) * T (Function.update xi i 1)

def fe_k {d : ℕ} (W : ℕ) (L : List (Fin d)) (xi x : V d) : BitVec W :=
  ∏ i : Fin d, (if i ∈ L then sgn (xi i * x i) else if x i = xi i then 1 else 0)

theorem fe_z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem fe_sgn_add {W : ℕ} (u v : ZMod 2) : (sgn (u + v) : BitVec W) = sgn u * sgn v := by
  rcases fe_z2 u with rfl | rfl <;> rcases fe_z2 v with rfl | rfl
  · simp [sgn]
  · simp [sgn]
  · simp [sgn]
  · have h : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h]; simp [sgn]

theorem fe_sgn_sum {W : ℕ} {ι : Type} (s : Finset ι) (f : ι → ZMod 2) :
    (sgn (∑ i ∈ s, f i) : BitVec W) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, fe_sgn_add, ih]

theorem fe_k_step {d : ℕ} (W : ℕ) (L : List (Fin d)) (e : Fin d) (he : e ∉ L) (xi x : V d) :
    fe_k W L (Function.update xi e 0) x + sgn (xi e) * fe_k W L (Function.update xi e 1) x
      = fe_k W (L ++ [e]) xi x := by
  unfold fe_k
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  have h0 : ∀ b : ZMod 2, ∏ i ∈ Finset.univ.erase e,
      (if i ∈ L then (sgn (Function.update xi e b i * x i) : BitVec W)
        else if x i = Function.update xi e b i then 1 else 0)
      = ∏ i ∈ Finset.univ.erase e,
      (if i ∈ L ++ [e] then (sgn (xi i * x i) : BitVec W) else if x i = xi i then 1 else 0) := by
    intro b
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ e := Finset.ne_of_mem_erase hi
    rw [Function.update_of_ne hne]
    simp [hne]
  rw [h0 0, h0 1]
  simp only [he, ite_false, Function.update_self, List.mem_append, List.mem_singleton, or_true,
    ite_true]
  rcases fe_z2 (x e) with h | h <;> rcases fe_z2 (xi e) with h' | h' <;>
    simp [h, h', sgn]

theorem fe_fold_sem {d W : ℕ} (T : V d → BitVec W) (L : List (Fin d)) (hL : L.Nodup) :
    ∀ xi, L.foldl (fun T e => fe_layer e T) T xi = ∑ x : V d, fe_k W L xi x * T x := by
  induction L using List.reverseRecOn with
  | nil =>
    intro xi
    have : ∀ x : V d, fe_k W [] xi x = if x = xi then 1 else 0 := by
      intro x
      unfold fe_k
      simp only [List.not_mem_nil, ite_false]
      rw [Finset.prod_ite_zero]
      simp only [Finset.prod_const_one, Finset.mem_univ, forall_true_left]
      congr 1
      exact propext funext_iff.symm
    simp only [this, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp
  | append_singleton L e ih =>
    intro xi
    have hn := List.nodup_append.1 hL
    have he : e ∉ L := fun h => hn.2.2 e h e (by simp) rfl
    rw [List.foldl_append]
    change List.foldl (fun T e => fe_layer e T) T L (Function.update xi e 0) +
      sgn (xi e) * List.foldl (fun T e => fe_layer e T) T L (Function.update xi e 1) = _
    rw [ih hn.1, ih hn.1, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [← fe_k_step W L e he xi x]
    ring

theorem fe_k_full {d : ℕ} (W : ℕ) (xi x : V d) :
    fe_k W (List.finRange d) xi x = sgn (xi ⬝ᵥ x) := by
  unfold fe_k dotProduct
  rw [fe_sgn_sum]
  apply Finset.prod_congr rfl
  intro i _
  simp

theorem fe_fold_tab {d W : ℕ} (L : List (Fin d)) :
    ∀ v : V d × Fin W → Bool,
      L.foldl (fun acc e => untab (fe_layer e (tab acc))) v
        = untab (L.foldl (fun T e => fe_layer e T) (tab v)) := by
  induction L with
  | nil => intro v; exact (untab_tab v).symm
  | cons e L ih =>
    intro v
    rw [List.foldl_cons, List.foldl_cons, ih, tab_untab]

theorem fe_layer_cmp {d W : ℕ} (i : Fin d) :
    Cmp (V d × Fin W) (V d × Fin W) (2 ^ d * (20 * (W + 1)))
      (fun v => untab (fe_layer i (tab v))) := by
  have hc : Fintype.card (V d) = 2 ^ d := by simp [V]
  have := Cmp.ofWords (ι := V d × Fin W) (α := V d) (W := W) (s := 20 * (W + 1))
    (G := fun v => fe_layer i (tab v)) (fun x => ?_)
  · rw [hc] at this; exact this
  · by_cases h : x i = 0
    · have hx : Function.update x i 0 = x := by rw [← h, Function.update_eq_self]
      refine Cw.congr (Cw.mono (Cw.add (Cw.var (fun k => (x, k)))
        (Cw.var (fun k => (Function.update x i 1, k)))) (by omega)) ?_
      intro v
      show tab v x + tab v (Function.update x i 1) = fe_layer i (tab v) x
      unfold fe_layer
      rw [hx, h]
      simp [sgn]
    · have h1 : x i = 1 := (fe_z2 (x i)).resolve_left h
      have hx : Function.update x i 1 = x := by rw [← h1, Function.update_eq_self]
      refine Cw.congr (Cw.mono (Cw.sub (Cw.var (fun k => (Function.update x i 0, k)))
        (Cw.var (fun k => (x, k)))) (by omega)) ?_
      intro v
      show tab v (Function.update x i 0) - tab v x = fe_layer i (tab v) x
      unfold fe_layer
      rw [hx, h1]
      have : (sgn (1 : ZMod 2) : BitVec W) = -1 := by simp [sgn]
      rw [this]
      ring

theorem cmp_wht (d W : ℕ) :
    Cmp (V d × Fin W) (V d × Fin W) (whtCost d W)
      (fun v => untab (fun xi : V d => ∑ x : V d, sgn (xi ⬝ᵥ x) * tab v x)) := by
  have h := Cmp.foldl (ι := V d × Fin W) (s := 2 ^ d * (20 * (W + 1))) (List.finRange d)
    (fun i v => untab (fe_layer i (tab v))) (fun e _ => fe_layer_cmp e)
  refine Cmp.congr (Cmp.mono h ?_) ?_
  · rw [List.length_finRange]
    unfold whtCost
    have h1 := Nat.zero_le (d * (2 ^ d * (W + 1)))
    have h2 := Nat.zero_le (2 ^ d * (W + 1))
    nlinarith
  · intro v k
    show (List.foldl (fun acc e => untab (fe_layer e (tab acc))) v (List.finRange d)) k = _
    rw [fe_fold_tab]
    congr 1
    funext xi
    rw [fe_fold_sem _ _ (List.nodup_finRange d)]
    apply Finset.sum_congr rfl
    intro x _
    rw [fe_k_full]

theorem fg_z2 (u : ZMod 2) : u = 0 ∨ u = 1 := by
  revert u; decide

theorem fg_sgn_add {W : ℕ} (u v : ZMod 2) : (sgn (u + v) : BitVec W) = sgn u * sgn v := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases fg_z2 u with rfl | rfl <;> rcases fg_z2 v with rfl | rfl <;> simp [sgn, h11]

theorem fg_sgn_sum {W : ℕ} {ι : Type} (s : Finset ι) (u : ι → ZMod 2) :
    (sgn (∑ i ∈ s, u i) : BitVec W) = ∏ i ∈ s, sgn (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, fg_sgn_add, ih]

theorem fg_char {W : ℕ} (K : ℕ) (w : Fin K → ZMod 2) :
    (∑ lam : V K, (sgn (∑ s, lam s * w s) : BitVec W)) = if w = 0 then 2 ^ K else 0 := by
  split_ifs with h
  · subst h
    simp [sgn]
  · obtain ⟨s, hs⟩ : ∃ s, w s ≠ 0 := by
      by_contra hh
      exact h (funext fun s => by_contra fun hs => hh ⟨s, hs⟩)
    have hs1 : w s = 1 := by
      rcases fg_z2 (w s) with h0 | h1
      · exact absurd h0 hs
      · exact h1
    have key : ∀ lam : V K, (∑ s', (lam + (Pi.single s 1 : V K)) s' * w s') = (∑ s', lam s' * w s') + 1 := by
      intro lam
      simp [add_mul, Finset.sum_add_distrib, Pi.single_apply, hs1]
    refine Finset.sum_involution (fun lam _ => lam + (Pi.single s 1 : V K)) ?_ ?_ ?_ ?_
    · intro lam _
      rw [key, fg_sgn_add]
      simp [sgn]
    · intro lam _ _ heq
      have := congrFun heq s
      simp at this
    · intro lam _
      simp
    · intro lam _
      funext i
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      by_cases hi : i = s
      · subst hi
        simp [add_assoc, h11]
      · simp [Pi.single_apply, hi]

theorem fg_split {R : Type} [AddCommMonoid R] (K : ℕ) (h : V (K + 1) → R) :
    (∑ lam : V (K + 1), h lam) =
      (∑ mu : V K, h (@Fin.snoc K (fun _ => ZMod 2) mu 0)) +
      (∑ mu : V K, h (@Fin.snoc K (fun _ => ZMod 2) mu 1)) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (K + 1) => ZMod 2)).sum_comp, Fintype.sum_prod_type]
  have h2 : ∀ F : ZMod 2 → R, ∑ x, F x = F 0 + F 1 := fun F => Fin.sum_univ_two F
  rw [h2]
  rfl

theorem fg_dot {a K : ℕ} (L : Matrix (Fin a) (Fin (K + 1)) (ZMod 2)) (mu : V K) (x : V a) :
    (L.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0)) ⬝ᵥ x =
      ∑ s : Fin K, mu s * ∑ j, L j s.castSucc * x j := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    mul_zero, add_zero, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem vecEquiv_exists (a : ℕ) :
    ∃ e : Fin (2 ^ a) ≃ V a, ∀ ix j, e ix j = if ix.val.testBit j.val then 1 else 0 := by
  let e0 : Fin (2 ^ a) → V a := fun ix j => if ix.val.testBit j.val then 1 else 0
  have hinj : Function.Injective e0 := by
    intro x y hxy
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < a
    · have := congrFun hxy ⟨i, hi⟩
      simp only [e0] at this
      by_cases hx : x.val.testBit i <;> by_cases hy : y.val.testBit i <;> simp_all
    · have hx : x.val < 2 ^ i := lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hy : y.val < 2 ^ i := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
  have hbij : Function.Bijective e0 := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [V]
  exact ⟨Equiv.ofBijective e0 hbij, fun ix j => rfl⟩

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

theorem fh_cnt_lt {N : ℕ} (P : Fin N → Prop) [DecidablePred P] (p p' : Fin N) (h : p < p')
    (hp : P p) :
    (Finset.univ.filter (fun q : Fin N => q < p ∧ P q)).card <
      (Finset.univ.filter (fun q : Fin N => q < p' ∧ P q)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨p, by simp [h, hp], by simp⟩
  · intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h1, h2⟩
    exact ⟨h1.trans h, h2⟩

theorem fh_cnt_lt_total {N : ℕ} (P : Fin N → Prop) [DecidablePred P] (p : Fin N) (hp : P p) :
    (Finset.univ.filter (fun q : Fin N => q < p ∧ P q)).card <
      (Finset.univ.filter (fun q : Fin N => P q)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨p, by simp [hp], by simp⟩
  · intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h1, h2⟩
    exact h2

theorem fh_cnt_inj {N : ℕ} (P : Fin N → Prop) [DecidablePred P] (p p' : Fin N)
    (hp : P p) (hp' : P p')
    (h : (Finset.univ.filter (fun q : Fin N => q < p ∧ P q)).card =
      (Finset.univ.filter (fun q : Fin N => q < p' ∧ P q)).card) : p = p' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have := fh_cnt_lt P p p' h1 hp; omega
  · have := fh_cnt_lt P p' p h1 hp'; omega

theorem fh_cntP_inj {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p p' : Fin N)
    (hp : pv R p = true) (hp' : pv R p' = true) (h : cntP R p = cntP R p') : p = p' :=
  fh_cnt_inj (fun q => pv R q = true) p p' hp hp' h

theorem fh_cntN_inj {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p p' : Fin N)
    (hp : pv R p = false) (hp' : pv R p' = false) (h : cntN R p = cntN R p') : p = p' :=
  fh_cnt_inj (fun q => pv R q = false) p p' hp hp' h

theorem fh_cntP_lt {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N)
    (hp : pv R p = true) : cntP R p < rkOf R :=
  fh_cnt_lt_total (fun q => pv R q = true) p hp

theorem fh_cntN_lt {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N)
    (hp : pv R p = false) : cntN R p < N - rkOf R := by
  have h1 := fh_cnt_lt_total (fun q => pv R q = false) p hp
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun q : Fin N => pv R q = true)
  have h3 : (Finset.univ.filter (fun q : Fin N => ¬ pv R q = true)) =
      (Finset.univ.filter (fun q : Fin N => pv R q = false)) := by
    apply Finset.filter_congr
    intro q _
    simp
  rw [h3, Finset.card_univ, Fintype.card_fin] at h2
  unfold cntN rkOf
  omega

theorem fh_rowSlot_eq {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (p : Fin N) (hp : pv R p = true) (s : Fin K) (hs : cntP R p = s.val)
    (j : Fin (m + N + 1)) : rowSlot K R s j = R (cl m p, j) := by
  unfold rowSlot
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨p', hp', hc, hr⟩
    have := fh_cntP_inj R p' p hp' hp (hc.trans hs.symm)
    subst this
    exact hr
  · intro hr
    exact ⟨p, hp, hs, hr⟩

theorem fh_rowSlot_none {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (s : Fin K) (hs : ¬ ∃ p : Fin N, pv R p = true ∧ cntP R p = s.val)
    (j : Fin (m + N + 1)) : rowSlot K R s j = false := by
  unfold rowSlot
  rw [decide_eq_false_iff_not]
  rintro ⟨p, h1, h2, _⟩
  exact hs ⟨p, h1, h2⟩

theorem ft_sum3 {a b c : ℕ} (F : Fin (a + b + c) → ZMod 2) :
    ∑ j : Fin (a + b + c), F j =
      ∑ j : Fin a, F (nx j) + ∑ j : Fin b, F (ny j) + ∑ j : Fin c, F (nz j) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  rfl

theorem ft_join_nx {a b c : ℕ} (h : V a × V b × V c) (j : Fin a) :
    join3 h (nx j) = h.1 j := by
  simp [join3, nx]

theorem ft_join_ny {a b c : ℕ} (h : V a × V b × V c) (j : Fin b) :
    join3 h (ny j) = h.2.1 j := by
  simp [join3, ny]

theorem ft_join_nz {a b c : ℕ} (h : V a × V b × V c) (j : Fin c) :
    join3 h (nz j) = h.2.2 j := by
  have h1 : ¬ (a + b + j.val < a) := by omega
  have h2 : ¬ (a + b + j.val < a + b) := by omega
  simp [join3, nz, h1, h2]

theorem ft_ext {a b c : ℕ} (u w : V (a + b + c))
    (hx : ∀ j : Fin a, u (nx j) = w (nx j)) (hy : ∀ j : Fin b, u (ny j) = w (ny j))
    (hz : ∀ j : Fin c, u (nz j) = w (nz j)) : u = w := by
  funext j
  by_cases h1 : j.val < a
  · have := hx ⟨j.val, h1⟩
    have e : (nx ⟨j.val, h1⟩ : Fin (a + b + c)) = j := Fin.ext rfl
    rwa [e] at this
  · by_cases h2 : j.val < a + b
    · have := hy ⟨j.val - a, by omega⟩
      have e : (ny ⟨j.val - a, by omega⟩ : Fin (a + b + c)) = j := Fin.ext (by simp [ny]; omega)
      rwa [e] at this
    · have := hz ⟨j.val - (a + b), by omega⟩
      have e : (nz ⟨j.val - (a + b), by omega⟩ : Fin (a + b + c)) = j :=
        Fin.ext (by simp [nz]; omega)
      rwa [e] at this

theorem ft_dot {a b c : ℕ} (h : V a × V b × V c) (x : V a) (y : V b) (z : V c) :
    join3 h ⬝ᵥ join3 (x, y, z) = h.1 ⬝ᵥ x + h.2.1 ⬝ᵥ y + h.2.2 ⬝ᵥ z := by
  unfold dotProduct
  rw [ft_sum3]
  simp only [ft_join_nx, ft_join_ny, ft_join_nz]

theorem ft_eqn {a b c m : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (x : V a) (y : V b) (z : V c) :
    (∀ i, (fun i => join3 (H i)) i ⬝ᵥ join3 (x, y, z) = rhs i) ↔
      ∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i := by
  constructor
  · intro h i
    rw [← ft_dot]
    exact h i
  · intro h i
    show join3 (H i) ⬝ᵥ join3 (x, y, z) = rhs i
    rw [ft_dot]
    exact h i

theorem ft_join_inj {a b c : ℕ} (h h' : V a × V b × V c) (e : join3 h = join3 h') : h = h' := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext j; rw [← ft_join_nx h, ← ft_join_nx h', e]
  · funext j; rw [← ft_join_ny h, ← ft_join_ny h', e]
  · funext j; rw [← ft_join_nz h, ← ft_join_nz h', e]

theorem fi_bound {i n j L : ℕ} (hi : i < n) (hj : j < L) : i * L + j < n * L := by
  have h1 : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right L hi
  have h2 : (i + 1) * L = i * L + L := by ring
  omega

theorem fi_flat {α β : Type} (d : α) (blk : β → List α) (L : ℕ) :
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

theorem fi_fin {α : Type} (d : α) (n L : ℕ) (blk : Fin n → List α)
    (h : ∀ i, (blk i).length = L) :
    ((List.finRange n).flatMap blk).length = n * L ∧
    ∀ (i : Fin n) (j : ℕ), j < L →
      ((List.finRange n).flatMap blk).getD (i.val * L + j) d = (blk i).getD j d := by
  obtain ⟨h1, h2⟩ := fi_flat d blk L (List.finRange n) (fun x _ => h x)
  refine ⟨by simpa using h1, ?_⟩
  intro i j hj
  have := h2 i.val (by simp) j hj
  simpa using this

theorem fi_getD_left {α : Type} (d : α) (A B : List α) (k : ℕ) (hk : k < A.length) :
    (A ++ B).getD k d = A.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem fi_getD_right {α : Type} (d : α) (A B : List α) (n k : ℕ) (hn : A.length = n) :
    (A ++ B).getD (n + k) d = B.getD k d := by
  subst hn
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem fi_block {a b c : ℕ} (h : V a × V b × V c) (r : Bool) (j : ℕ) (hj : j < a + b + c + 1) :
    (List.ofFn (fun j : Fin a => decide (h.1 j ≠ 0)) ++
      List.ofFn (fun j : Fin b => decide (h.2.1 j ≠ 0)) ++
      List.ofFn (fun j : Fin c => decide (h.2.2 j ≠ 0)) ++ [r]).getD j false =
      if hh : j < a + b + c then decide (join3 h ⟨j, hh⟩ ≠ 0) else r := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : j < a
  · have hh : j < a + b + c := by omega
    rw [dif_pos hh, List.append_assoc, List.append_assoc,
      List.getElem?_append_left (by simpa using h1)]
    simp [join3, h1]
  · by_cases h2 : j < a + b
    · have hh : j < a + b + c := by omega
      rw [dif_pos hh, List.append_assoc, List.append_assoc,
        List.getElem?_append_right (by simpa using h1),
        List.getElem?_append_left (by simp; omega)]
      have : j - a < b := by omega
      simp [join3, h1, h2, this]
    · by_cases h3 : j < a + b + c
      · rw [dif_pos h3, List.append_assoc, List.append_assoc,
          List.getElem?_append_right (by simpa using h1),
          List.getElem?_append_right (by simp; omega),
          List.getElem?_append_left (by simp; omega)]
        have e : j - a - b = j - (a + b) := by omega
        have h4 : j - (a + b) < c := by omega
        simp [join3, h1, h2, e, h4]
      · have e : j = a + b + c := by omega
        subst e
        rw [dif_neg h3, List.getElem?_append_right (by simp; omega)]
        have e : a + b + c - (a + (b + c)) = 0 := by omega
        simp [e]

theorem input_layout (a b c m t : ℕ) (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (bits : List Bool)
    (hbits : bits = (List.finRange m).flatMap (fun i =>
        List.ofFn (fun j : Fin a => decide ((H i).1 j ≠ 0)) ++
        List.ofFn (fun j : Fin b => decide ((H i).2.1 j ≠ 0)) ++
        List.ofFn (fun j : Fin c => decide ((H i).2.2 j ≠ 0)) ++ [decide (rhs i ≠ 0)]) ++
        (List.finRange (2 ^ a)).flatMap (fun ix =>
          List.ofFn (fun j : Fin t => (f ix).val.testBit j.val)) ++
        (List.finRange (2 ^ b)).flatMap (fun iy =>
          List.ofFn (fun j : Fin t => (g iy).val.testBit j.val))) :
    bits.length = m * (a + b + c + 1) + (2 ^ a + 2 ^ b) * t ∧
    (∀ (i : Fin m) (j : Fin (a + b + c + 1)),
      bits.getD (i.val * (a + b + c + 1) + j.val) false =
        if h : j.val < a + b + c then decide (join3 (H i) ⟨j.val, h⟩ ≠ 0)
        else decide (rhs i ≠ 0)) ∧
    (∀ (ix : Fin (2 ^ a)) (j : Fin t),
      bits.getD (m * (a + b + c + 1) + ix.val * t + j.val) false = (f ix).val.testBit j.val) ∧
    (∀ (iy : Fin (2 ^ b)) (j : Fin t),
      bits.getD (m * (a + b + c + 1) + 2 ^ a * t + iy.val * t + j.val) false =
        (g iy).val.testBit j.val) := by
  obtain ⟨hA1, hA2⟩ := fi_fin false m (a + b + c + 1) (fun i =>
        List.ofFn (fun j : Fin a => decide ((H i).1 j ≠ 0)) ++
        List.ofFn (fun j : Fin b => decide ((H i).2.1 j ≠ 0)) ++
        List.ofFn (fun j : Fin c => decide ((H i).2.2 j ≠ 0)) ++ [decide (rhs i ≠ 0)])
        (fun i => by simp; omega)
  obtain ⟨hB1, hB2⟩ := fi_fin false (2 ^ a) t (fun ix =>
          List.ofFn (fun j : Fin t => (f ix).val.testBit j.val)) (fun i => by simp)
  obtain ⟨hC1, hC2⟩ := fi_fin false (2 ^ b) t (fun iy =>
          List.ofFn (fun j : Fin t => (g iy).val.testBit j.val)) (fun i => by simp)
  subst hbits
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.length_append, List.length_append, hA1, hB1, hC1]; ring
  · intro i j
    rw [List.append_assoc, fi_getD_left _ _ _ _ (by rw [hA1]; exact fi_bound i.2 j.2),
      hA2 i j.val j.2]
    exact fi_block (H i) _ j.val j.2
  · intro ix j
    rw [List.append_assoc, Nat.add_assoc, fi_getD_right _ _ _ _ _ hA1,
      fi_getD_left _ _ _ _ (by rw [hB1]; exact fi_bound ix.2 j.2), hB2 ix j.val j.2]
    simp [List.getD_eq_getElem?_getD]
  · intro iy j
    have e : m * (a + b + c + 1) + 2 ^ a * t + iy.val * t + j.val =
        (m * (a + b + c + 1) + 2 ^ a * t) + (iy.val * t + j.val) := by ring
    rw [e, fi_getD_right _ _ _ _ _ (by rw [List.length_append, hA1, hB1]), hC2 iy j.val j.2]
    simp [List.getD_eq_getElem?_getD]

def cnt {N : ℕ} (fl : Fin N → Bool) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun q : Fin N => q.val < i ∧ fl q = true)).card

theorem cnt_zero {N : ℕ} (fl : Fin N → Bool) : cnt fl 0 = 0 := by simp [cnt]

theorem cnt_succ {N : ℕ} (fl : Fin N → Bool) (i : ℕ) (h : i < N) :
    cnt fl (i + 1) = cnt fl i + (if fl ⟨i, h⟩ = true then 1 else 0) := by
  unfold cnt
  by_cases hf : fl ⟨i, h⟩ = true
  · have : (Finset.univ.filter (fun q : Fin N => q.val < i + 1 ∧ fl q = true)) =
        insert ⟨i, h⟩ (Finset.univ.filter (fun q : Fin N => q.val < i ∧ fl q = true)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hq : q.val = i
        · left; exact Fin.ext hq
        · right; exact ⟨by omega, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Nat.lt_succ_self i, hf⟩
        · exact ⟨by omega, h2⟩
    rw [this, Finset.card_insert_of_notMem (by simp), if_pos hf]
  · have : (Finset.univ.filter (fun q : Fin N => q.val < i + 1 ∧ fl q = true)) =
        (Finset.univ.filter (fun q : Fin N => q.val < i ∧ fl q = true)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_contra hc
        have : q = ⟨i, h⟩ := Fin.ext (show q.val = i by omega)
        exact hf (this ▸ h2)
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    rw [this, if_neg hf, Nat.add_zero]

def cntG (N K : ℕ) (i : ℕ) (v : Fin N ⊕ Fin (K + 1) → Bool) (s : Fin (K + 1)) : Bool :=
  if hi : i < N then
    (if v (Sum.inl ⟨i, hi⟩) = true then
      (if hs : 0 < s.val then v (Sum.inr ⟨s.val - 1, by omega⟩) else false)
     else v (Sum.inr s))
  else v (Sum.inr s)

theorem cntG_cb (N K i : ℕ) (s : Fin (K + 1)) :
    Cb (Fin N ⊕ Fin (K + 1)) 6 (fun v => cntG N K i v s) := by
  by_cases hi : i < N
  · by_cases hs : 0 < s.val
    · refine ((Cb.mux (Cb.var (Sum.inl ⟨i, hi⟩)) (Cb.var (Sum.inr ⟨s.val - 1, by omega⟩))
        (Cb.var (Sum.inr s))).mono (by norm_num)).congr ?_
      intro v; simp [cntG, hi, hs]
    · refine ((Cb.mux (Cb.var (Sum.inl ⟨i, hi⟩)) (Cb.const false)
        (Cb.var (Sum.inr s))).mono (by norm_num)).congr ?_
      intro v; simp [cntG, hi, hs]
  · refine ((Cb.var (Sum.inr s)).mono (by norm_num)).congr ?_
    intro v; simp [cntG, hi]

theorem cmp_counter (N K : ℕ) :
    Cmp (Fin N) (Fin (N + 1) × Fin (K + 1)) ((N + 1) * ((K + 1) * 6))
      (fun fl p => decide (cnt fl p.1.val = p.2.val)) := by
  refine Cmp.chain N ((K + 1) * 6) (fun i fl s => decide (cnt fl i = s.val)) (cntG N K) ?_ ?_ ?_
  · have := Cmp.ofBits (ι := Fin N) (κ := Fin (K + 1)) (s := 6)
      (F := fun fl s => decide (cnt fl 0 = s.val)) (fun s => by
        refine ((Cb.const (decide (0 = s.val))).mono (by norm_num)).congr ?_
        intro v; simp [cnt_zero])
    rw [Fintype.card_fin] at this
    exact this
  · intro i _
    have := Cmp.ofBits (ι := Fin N ⊕ Fin (K + 1)) (κ := Fin (K + 1)) (s := 6)
      (F := cntG N K i) (fun s => cntG_cb N K i s)
    rw [Fintype.card_fin] at this
    exact this
  · intro i hi v
    funext s
    simp only [cntG, dif_pos hi, Sum.elim_inl, Sum.elim_inr, cnt_succ v i hi]
    by_cases hv : v ⟨i, hi⟩ = true
    · by_cases hs : 0 < s.val
      · simp [hv, hs]; omega
      · simp [hv, hs]; omega
    · simp [hv]

theorem cnt_le {N : ℕ} (fl : Fin N → Bool) (i : ℕ) : cnt fl i ≤ N := by
  unfold cnt
  calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := by simp

theorem cnt_compl {N : ℕ} (fl : Fin N → Bool) :
    cnt (fun q => !fl q) N = N - cnt fl N := by
  have h : cnt fl N + cnt (fun q => !fl q) N = N := by
    unfold cnt
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun q : Fin N => fl q = true)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have e1 : (Finset.univ.filter (fun q : Fin N => q.val < N ∧ fl q = true)) =
        Finset.univ.filter (fun q : Fin N => fl q = true) := by
      ext q; simp
    have e2 : (Finset.univ.filter (fun q : Fin N => q.val < N ∧ (!fl q) = true)) =
        Finset.univ.filter (fun q : Fin N => ¬ fl q = true) := by
      ext q; simp
    rw [e1, e2]; exact this
  omega

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

theorem fz3_pull {ι : Type} {d k W S S' : ℕ} {L : (ι → Bool) → Fin d × Fin k → Bool}
    {T : (ι → Bool) → V d × Fin W → Bool} (hL : Cmp ι (Fin d × Fin k) S L)
    (hT : Cmp ι (V d × Fin W) S' T) :
    Cmp ι (V k × Fin W) (S + S' + tcost d k W)
      (fun v => untab (fun lam : V k => tab (T v) ((mat (L v)).mulVec lam))) :=
  Cmp.congr (Cmp.comp (Cmp.pair hL hT) (cmp_pull d k W)) (fun _ _ => rfl)

theorem fz3_push {ι : Type} {d k W S S' : ℕ} {L : (ι → Bool) → Fin d × Fin k → Bool}
    {T : (ι → Bool) → V k × Fin W → Bool} (hL : Cmp ι (Fin d × Fin k) S L)
    (hT : Cmp ι (V k × Fin W) S' T) :
    Cmp ι (V d × Fin W) (S + S' + tcost d k W)
      (fun v => untab (fun z : V d =>
        ∑ lam : V k, if (mat (L v)).mulVec lam = z then tab (T v) lam else 0)) :=
  Cmp.congr (Cmp.comp (Cmp.pair hL hT) (cmp_push d k W)) (fun _ _ => rfl)

theorem fz3_card (k : ℕ) : Fintype.card (V k) = 2 ^ k := by
  simp [V, ZMod.card]

abbrev In0 (a b c m t : ℕ) : Type :=
  (Fin m × Fin (a + b + c + 1)) ⊕ ((Fin (2 ^ a) × Fin t) ⊕ (Fin (2 ^ b) × Fin t))

def Mb (a b c m t : ℕ) (v : In0 a b c m t → Bool) :
    Fin (m + (a + b + c) + 1) × Fin (m + (a + b + c) + 1) → Bool := fun p =>
  if hi : p.1.val < m then
    (if hj : p.2.val < a + b + c + 1 then v (Sum.inl (⟨p.1.val, hi⟩, ⟨p.2.val, hj⟩)) else false)
  else false

def Rb (a b c m t : ℕ) (v : In0 a b c m t → Bool) :
    Fin (m + (a + b + c) + 1) × Fin (m + (a + b + c) + 1) → Bool :=
  gj _ (Mb a b c m t v)

def fTab (a b c m t W : ℕ) (ea : Fin (2 ^ a) ≃ V a) (v : In0 a b c m t → Bool) :
    V a × Fin W → Bool := fun p =>
  if h : p.2.val < t then v (Sum.inr (Sum.inl (ea.symm p.1, ⟨p.2.val, h⟩))) else false

def gTab (a b c m t W : ℕ) (eb : Fin (2 ^ b) ≃ V b) (v : In0 a b c m t → Bool) :
    V b × Fin W → Bool := fun p =>
  if h : p.2.val < t then v (Sum.inr (Sum.inr (eb.symm p.1, ⟨p.2.val, h⟩))) else false

def inpOf {a b c m t : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) : In0 a b c m t → Bool :=
  Sum.elim (fun p => if h : p.2.val < a + b + c then decide (join3 (H p.1) ⟨p.2.val, h⟩ ≠ 0)
      else decide (rhs p.1 ≠ 0))
    (Sum.elim (fun p => (f p.1).val.testBit p.2.val) (fun p => (g p.1).val.testBit p.2.val))

theorem fz4_cardV (d : ℕ) : Fintype.card (V d) = 2 ^ d := by
  simp [V]

theorem fz4_Mb (a b c m t : ℕ) :
    Cmp (In0 a b c m t) (Fin (m + (a + b + c) + 1) × Fin (m + (a + b + c) + 1))
      ((m + (a + b + c) + 1) ^ 2) (Mb a b c m t) := by
  refine (Cmp.ofBits (s := 1) (F := Mb a b c m t) (fun p => ?_)).mono (by simp [sq])
  by_cases hi : p.1.val < m
  · by_cases hj : p.2.val < a + b + c + 1
    · refine ((Cb.var (Sum.inl (⟨p.1.val, hi⟩, ⟨p.2.val, hj⟩))).mono (by norm_num)).congr ?_
      intro v; simp [Mb, hi, hj]
    · refine (Cb.const false).congr ?_
      intro v; simp [Mb, hi, hj]
  · refine (Cb.const false).congr ?_
    intro v; simp [Mb, hi]

theorem fz4_fTab (a b c m t W : ℕ) (ea : Fin (2 ^ a) ≃ V a) :
    Cmp (In0 a b c m t) (V a × Fin W) (2 ^ a * W) (fTab a b c m t W ea) := by
  refine (Cmp.ofBits (s := 1) (F := fTab a b c m t W ea) (fun p => ?_)).mono
    (by simp)
  by_cases h : p.2.val < t
  · refine ((Cb.var (Sum.inr (Sum.inl (ea.symm p.1, ⟨p.2.val, h⟩)))).mono (by norm_num)).congr ?_
    intro v; simp [fTab, h]
  · refine (Cb.const false).congr ?_
    intro v; simp [fTab, h]

theorem fz4_gTab (a b c m t W : ℕ) (eb : Fin (2 ^ b) ≃ V b) :
    Cmp (In0 a b c m t) (V b × Fin W) (2 ^ b * W) (gTab a b c m t W eb) := by
  refine (Cmp.ofBits (s := 1) (F := gTab a b c m t W eb) (fun p => ?_)).mono
    (by simp)
  by_cases h : p.2.val < t
  · refine ((Cb.var (Sum.inr (Sum.inr (eb.symm p.1, ⟨p.2.val, h⟩)))).mono (by norm_num)).congr ?_
    intro v; simp [gTab, h]
  · refine (Cb.const false).congr ?_
    intro v; simp [gTab, h]

theorem fz5_Mb {a b c m t : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) :
    Mb a b c m t (inpOf H rhs f g) = sysBits (fun i => join3 (H i)) rhs := by
  funext p
  unfold Mb sysBits inpOf
  by_cases hi : p.1.val < m
  · by_cases hj : p.2.val < a + b + c
    · have hj' : p.2.val < a + b + c + 1 := by omega
      simp [hi, hj, hj']
    · by_cases hj2 : p.2.val = a + b + c
      · have hj' : p.2.val < a + b + c + 1 := by omega
        simp [hi, hj, hj', hj2]
      · have hj' : ¬ p.2.val < a + b + c + 1 := by omega
        simp [hi, hj, hj', hj2]
  · simp [hi]

theorem fz5_tabf {a b c m t : ℕ} (W : ℕ) (ea : Fin (2 ^ a) ≃ V a)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (x : V a) :
    tab (fTab a b c m t W ea (inpOf H rhs f g)) x = BitVec.ofNat W (f (ea.symm x)).val := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 := getLsbD_bv (fun k : Fin W => fTab a b c m t W ea (inpOf H rhs f g) (x, k)) ⟨i, hi⟩
  have h2 : (tab (fTab a b c m t W ea (inpOf H rhs f g)) x).getLsbD i =
      fTab a b c m t W ea (inpOf H rhs f g) (x, ⟨i, hi⟩) := h1
  rw [h2, BitVec.getLsbD_ofNat]
  unfold fTab inpOf
  by_cases h : i < t
  · simp [h, hi]
  · have hlt : (f (ea.symm x)).val < 2 ^ i :=
      lt_of_lt_of_le (f (ea.symm x)).isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [h, hi, Nat.testBit_lt_two_pow hlt]

theorem fz5_tabg {a b c m t : ℕ} (W : ℕ) (eb : Fin (2 ^ b) ≃ V b)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (y : V b) :
    tab (gTab a b c m t W eb (inpOf H rhs f g)) y = BitVec.ofNat W (g (eb.symm y)).val := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 := getLsbD_bv (fun k : Fin W => gTab a b c m t W eb (inpOf H rhs f g) (y, k)) ⟨i, hi⟩
  have h2 : (tab (gTab a b c m t W eb (inpOf H rhs f g)) y).getLsbD i =
      gTab a b c m t W eb (inpOf H rhs f g) (y, ⟨i, hi⟩) := h1
  rw [h2, BitVec.getLsbD_ofNat]
  unfold gTab inpOf
  by_cases h : i < t
  · simp [h, hi]
  · have hlt : (g (eb.symm y)).val < 2 ^ i :=
      lt_of_lt_of_le (g (eb.symm y)).isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [h, hi, Nat.testBit_lt_two_pow hlt]

theorem fz5_total {a b c m t : ℕ} (W : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (z : V c) :
    (∑ x : V a, ∑ y : V b,
      if (∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i) then
        BitVec.ofNat W (f (ea.symm x)).val * BitVec.ofNat W (g (eb.symm y)).val else 0) =
    BitVec.ofNat W (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ z = rhs i) then
        (f ix).val * (g iy).val else 0) := by
  rw [← Equiv.sum_comp ea]
  have : ∀ ix : Fin (2 ^ a), (∑ y : V b,
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i) then
        BitVec.ofNat W (f (ea.symm (ea ix))).val * BitVec.ofNat W (g (eb.symm y)).val else 0) =
      ∑ iy : Fin (2 ^ b),
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ z = rhs i) then
        ((f ix).val : BitVec W) * ((g iy).val : BitVec W) else 0 := by
    intro ix
    rw [← Equiv.sum_comp eb]
    apply Finset.sum_congr rfl
    intro iy _
    simp only [Equiv.symm_apply_apply, BitVec.natCast_eq_ofNat]
  rw [Finset.sum_congr rfl (fun ix _ => this ix)]
  rw [← BitVec.natCast_eq_ofNat]
  push_cast
  rfl

theorem fz5_two (W K n : ℕ) : (2 : BitVec W) ^ K * BitVec.ofNat W n = BitVec.ofNat W (2 ^ K * n) := by
  rw [← BitVec.natCast_eq_ofNat, ← BitVec.natCast_eq_ofNat]
  push_cast
  rfl

theorem fin_idx_lt (i n j L : ℕ) (hi : i < n) (hj : j < L) : i * L + j < n * L := by
  calc i * L + j < i * L + L := by omega
    _ = (i + 1) * L := by ring
    _ ≤ n * L := Nat.mul_le_mul_right L hi

theorem gj_mulVec {D : ℕ} (M : Fin D × Fin D → Bool) (c : V D) (h : (mat M).mulVec c = 0) :
    (mat (gj D M)).mulVec c = 0 := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv M
  rw [h1, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

theorem gj_zcol {D : ℕ} (M : Fin D × Fin D → Bool) (j : Fin D) (h : ∀ i, M (i, j) = false)
    (i : Fin D) : gj D M (i, j) = false := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv M
  apply fh_mat_zero
  rw [h1, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [fh_mat_false M k j (h k), mul_zero]

theorem gj_comb_piv {D : ℕ} (M : Fin D × Fin D → Bool) (lam : Fin D → ZMod 2) (p : Fin D)
    (hp : gj D M (p, p) = true) : ∑ q, lam q * mat (gj D M) q p = lam p := by
  rw [Finset.sum_eq_single p]
  · rw [fh_mat_true _ _ _ hp, mul_one]
  · intro q _ hq
    rw [fh_mat_false _ _ _ (by rw [gj_pivcol M p hp q]; simp [hq]), mul_zero]
  · intro h; exact absurd (Finset.mem_univ p) h

theorem gj_comb_supp {D : ℕ} (M : Fin D × Fin D → Bool) (lam : Fin D → ZMod 2) (j : Fin D)
    (hj : ∑ q, lam q * mat (gj D M) q j ≠ 0) :
    ∃ p, p ≤ j ∧ gj D M (p, p) = true ∧ lam p ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hj
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : j < q
  · rw [fh_mat_false _ _ _ (gj_upper M q j hq), mul_zero]
  · by_cases hp : gj D M (q, q) = true
    · rw [hc q (not_lt.mp hq) hp, zero_mul]
    · rw [fh_mat_false _ _ _ (gj_zerorow M q (by simpa using hp) j), mul_zero]

theorem gj_lead {D : ℕ} (M : Fin D × Fin D → Bool) (lam : Fin D → ZMod 2) (j : Fin D)
    (hj : ∑ q, lam q * mat (gj D M) q j ≠ 0)
    (hmin : ∀ j', j' < j → ∑ q, lam q * mat (gj D M) q j' = 0) : gj D M (j, j) = true := by
  obtain ⟨p, hpj, hp, hl⟩ := gj_comb_supp M lam j hj
  rcases lt_or_eq_of_le hpj with h | h
  · exact absurd (by rw [← gj_comb_piv M lam p hp]; exact hmin p h) hl
  · rw [← h]; exact hp

theorem gj_rank {D : ℕ} (M : Fin D × Fin D → Bool) :
    (Finset.univ.filter (fun p : Fin D => gj D M (p, p) = true)).card ≤
      (Finset.univ.filter (fun i : Fin D => ∃ j, M (i, j) = true)).card := by
  obtain ⟨U, U', h1, -⟩ := gj_equiv M
  let f : ({p : Fin D // gj D M (p, p) = true} → ZMod 2) →
      ({i : Fin D // ∃ j, M (i, j) = true} → ZMod 2) := fun v s => ∑ p, v p * U p.1 s.1
  let g : ({i : Fin D // ∃ j, M (i, j) = true} → ZMod 2) →
      ({p : Fin D // gj D M (p, p) = true} → ZMod 2) := fun y p => ∑ s, y s * mat M s.1 p.1
  have hS : ∀ (h : Fin D → ZMod 2) (p : Fin D),
      ∑ s : {i : Fin D // ∃ j, M (i, j) = true}, h s.1 * mat M s.1 p =
        ∑ s : Fin D, h s * mat M s p := by
    intro h p
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin D => ∃ j, M (i, j) = true)
      (fun s => h s * mat M s p)]
    have : ∑ s : {i : Fin D // ¬ ∃ j, M (i, j) = true}, h s.1 * mat M s.1 p = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      have hs := s.2
      push_neg at hs
      rw [fh_mat_false M _ _ (by simpa using hs p), mul_zero]
    rw [this, add_zero]
  have hinv : Function.LeftInverse g f := by
    intro v
    funext p'
    show ∑ s : {i : Fin D // ∃ j, M (i, j) = true},
      (∑ p : {p : Fin D // gj D M (p, p) = true}, v p * U p.1 s.1) * mat M s.1 p'.1 = v p'
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have e : ∀ p : {p : Fin D // gj D M (p, p) = true},
        ∑ s : {i : Fin D // ∃ j, M (i, j) = true}, v p * U p.1 s.1 * mat M s.1 p'.1 =
          v p * mat (gj D M) p.1 p'.1 := by
      intro p
      have h2 : ∑ s : {i : Fin D // ∃ j, M (i, j) = true}, v p * U p.1 s.1 * mat M s.1 p'.1 =
          ∑ s : Fin D, v p * U p.1 s * mat M s p'.1 := hS (fun s => v p * U p.1 s) p'.1
      rw [h2, h1, Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [Finset.sum_congr rfl (fun p _ => e p)]
    rw [Finset.sum_eq_single p']
    · rw [fh_mat_true _ _ _ p'.2, mul_one]
    · intro p _ hp
      have hne : p.1 ≠ p'.1 := fun h => hp (Subtype.ext h)
      rw [fh_mat_false _ _ _ (by rw [gj_pivcol M p'.1 p'.2 p.1]; simp [hne]), mul_zero]
    · intro h; exact absurd (Finset.mem_univ p') h
  have hc := Fintype.card_le_of_injective f hinv.injective
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_subtype] at hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hc

def Phi (w : ℕ) : ℕ := 2 ^ (w % 2) * 7 ^ (w / 2)

theorem two_pow_le_Phi (w : ℕ) : 2 ^ w ≤ Phi w := by
  unfold Phi
  have e : 2 ^ w = 2 ^ (w % 2) * 4 ^ (w / 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [e]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) _)

theorem Phi_exp (w q d r1 r2 r3 μ : ℕ) (h1 : q + d + r1 + r2 ≤ w) (h2 : q + d + r1 + r3 ≤ w)
    (h3 : q + d + r2 + r3 ≤ w) (hμ : μ = min r1 (min r2 r3)) :
    2 ^ (q + d + r1 + r2 + r3 - 3 * μ) * 7 ^ μ ≤ Phi w := by
  have hs : q + d + r1 + r2 + r3 - 3 * μ ≤ w % 2 + 2 * (w / 2 - μ) := by
    have := Nat.mod_add_div w 2
    rcases le_total r1 r2 with h12 | h12 <;> rcases le_total r1 r3 with h13 | h13 <;>
      rcases le_total r2 r3 with h23 | h23 <;>
      simp only [hμ, min_eq_left, min_eq_right, h12, h13, h23] <;> omega
  have hμw : μ ≤ w / 2 := by
    have := Nat.mod_add_div w 2
    rcases le_total r1 r2 with h12 | h12 <;> rcases le_total r1 r3 with h13 | h13 <;>
      rcases le_total r2 r3 with h23 | h23 <;>
      simp only [hμ, min_eq_left, min_eq_right, h12, h13, h23] <;> omega
  calc 2 ^ (q + d + r1 + r2 + r3 - 3 * μ) * 7 ^ μ
      ≤ 2 ^ (w % 2 + 2 * (w / 2 - μ)) * 7 ^ μ :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hs)
    _ = 2 ^ (w % 2) * (4 ^ (w / 2 - μ) * 7 ^ μ) := by
        rw [pow_add, pow_mul]; norm_num; ring
    _ ≤ 2 ^ (w % 2) * (7 ^ (w / 2 - μ) * 7 ^ μ) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) _))
    _ = Phi w := by
        unfold Phi; rw [← pow_add, Nat.sub_add_cancel hμw]

def co {w : ℕ} (u : V w) (i : ℕ) : ZMod 2 := if h : i < w then u ⟨i, h⟩ else 0

def Std (w q d r1 r2 r3 : ℕ) (u v t : V w) : Prop :=
  (∀ i < q, co u i + co v i = co t i) ∧
  (∀ i < d, co u (q + i) = co t (q + i) ∧ co v (q + i) = co t (q + i)) ∧
  (∀ i < r2, co u (q + d + i) = co t (q + d + i)) ∧
  (∀ i < r1, co u (q + d + r2 + i) = co v (q + d + i)) ∧
  (∀ i < r3, co v (q + d + r1 + i) = co t (q + d + r2 + i)) ∧
  (∀ i : Fin w, q + d + r2 + r1 ≤ i.val → u i = 0) ∧
  (∀ i : Fin w, q + d + r1 + r3 ≤ i.val → v i = 0) ∧
  (∀ i : Fin w, q + d + r2 + r3 ≤ i.val → t i = 0)

instance (w q d r1 r2 r3 : ℕ) (u v t : V w) : Decidable (Std w q d r1 r2 r3 u v t) := by
  unfold Std; infer_instance

def ShapeSpec (w W B q d r1 r2 r3 : ℕ) : Prop :=
  ∃ S, S ≤ 2 ^ 30 * (W + w + 1) ^ 3 * Phi w ∧
    Cmp ((V w × Fin W) ⊕ (V w × Fin W)) (V w × Fin B) S
      (fun v p => (∑ x : V w, ∑ y : V w, if Std w q d r1 r2 r3 x y p.1 then
        tab (fun e => v (Sum.inl e)) x * tab (fun e => v (Sum.inr e)) y else 0 : BitVec W).getLsbD
          p.2.val)

def wOf (a b c : ℕ) : ℕ := max a (max b c)

def WOf (a b c t : ℕ) : ℕ := a + b + 2 * t + 1 + wOf a b c

def fitsW (w : ℕ) (s : Fin 5 → ℕ) : Prop :=
  s 0 + s 1 + s 2 + s 3 ≤ w ∧ s 0 + s 1 + s 2 + s 4 ≤ w ∧ s 0 + s 1 + s 3 + s 4 ≤ w

def CtlSpec (a b c m t : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b) : Prop :=
  ∃ (S : ℕ) (dims : (In0 a b c m t → Bool) → Fin 5 → ℕ)
    (FF GG : (In0 a b c m t → Bool) → V (wOf a b c) × Fin (WOf a b c t) → Bool)
    (EE : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin c → Bool)
    (CZ : (In0 a b c m t → Bool) → V c → Bool),
    S ≤ 2 ^ 50 * (a + b + c + m + t + 4) ^ 20 * Phi (wOf a b c) ∧
    Cmp (In0 a b c m t) ((Fin 5 × Fin (wOf a b c + 1)) ⊕ ((V (wOf a b c) × Fin (WOf a b c t)) ⊕
      ((V (wOf a b c) × Fin (WOf a b c t)) ⊕ ((Fin (wOf a b c) × Fin c) ⊕ V c)))) S
      (fun v => Sum.elim (fun p => decide (dims v p.1 = p.2.val))
        (Sum.elim (FF v) (Sum.elim (GG v) (Sum.elim (EE v) (CZ v))))) ∧
    ∀ (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2) (f : Fin (2 ^ a) → Fin (2 ^ t))
      (g : Fin (2 ^ b) → Fin (2 ^ t)),
      fitsW (wOf a b c) (dims (inpOf H rhs f g)) ∧
      ∀ z : V c, BitVec.ofNat (WOf a b c t) (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
          if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ z = rhs i) then
            (f ix).val * (g iy).val else 0) =
        if CZ (inpOf H rhs f g) z = true then
          ∑ x : V (wOf a b c), ∑ y : V (wOf a b c),
            if Std (wOf a b c) (dims (inpOf H rhs f g) 0) (dims (inpOf H rhs f g) 1)
              (dims (inpOf H rhs f g) 2) (dims (inpOf H rhs f g) 3) (dims (inpOf H rhs f g) 4) x y
              ((mat (EE (inpOf H rhs f g))).mulVec z)
            then tab (FF (inpOf H rhs f g)) x * tab (GG (inpOf H rhs f g)) y else 0
        else 0

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

abbrev rpCol (a b c : ℕ) : Type := Fin a ⊕ Fin b ⊕ Fin c ⊕ Unit

abbrev rpX {a b c : ℕ} (i : Fin a) : rpCol a b c := Sum.inl i
abbrev rpY {a b c : ℕ} (j : Fin b) : rpCol a b c := Sum.inr (Sum.inl j)
abbrev rpZ {a b c : ℕ} (k : Fin c) : rpCol a b c := Sum.inr (Sum.inr (Sum.inl k))
abbrev rpR {a b c : ℕ} : rpCol a b c := Sum.inr (Sum.inr (Sum.inr ()))

def rpBit (b : Bool) : ZMod 2 := if b then 1 else 0

def rpPar {I : Type} [Fintype I] (p : I → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => p i = true)).card % 2 = 1)

def rpEv {κ : Type} [Fintype κ] (w : κ → ZMod 2) (r : κ → Bool) : ZMod 2 :=
  ∑ q, rpBit (r q) * w q

def rpRk1 (a b c m : ℕ) : rpCol a b c ⊕ Fin m → ℕ
  | Sum.inl (Sum.inl i) => i.val
  | Sum.inl (Sum.inr (Sum.inl j)) => a + j.val
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl k))) => a + b + k.val
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr _))) => a + b + c
  | Sum.inr i => a + b + c + 1 + i.val

def rpRk2 (a b c : ℕ) : rpCol a b c → ℕ
  | Sum.inl i => b + i.val
  | Sum.inr (Sum.inl j) => j.val
  | Sum.inr (Sum.inr (Sum.inl k)) => a + b + k.val
  | Sum.inr (Sum.inr (Sum.inr _)) => a + b + c

def rpRk3 (a b c : ℕ) : rpCol a b c → ℕ
  | Sum.inl i => c + i.val
  | Sum.inr (Sum.inl j) => c + a + j.val
  | Sum.inr (Sum.inr (Sum.inl k)) => k.val
  | Sum.inr (Sum.inr (Sum.inr _)) => a + b + c

def rpRk5 (a b c : ℕ) : rpCol a b c → ℕ
  | Sum.inl i => c + b + i.val
  | Sum.inr (Sum.inl j) => c + j.val
  | Sum.inr (Sum.inr (Sum.inl k)) => k.val
  | Sum.inr (Sum.inr (Sum.inr _)) => a + b + c

def rpRk4 (a b c : ℕ) : Fin c ⊕ rpCol a b c → ℕ
  | Sum.inl l => l.val
  | Sum.inr p => c + rpRk5 a b c p

theorem rp_rk1_inj (a b c m : ℕ) : Function.Injective (rpRk1 a b c m) := by
  rintro ((i | j | k | u) | i) ((i' | j' | k' | u') | i') h <;> simp only [rpRk1] at h <;>
    first
      | (exfalso; omega)
      | rfl
      | (have h' := Fin.ext (show i.val = i'.val by omega); subst h'; rfl)
      | (have h' := Fin.ext (show j.val = j'.val by omega); subst h'; rfl)
      | (have h' := Fin.ext (show k.val = k'.val by omega); subst h'; rfl)

theorem rp_rk2_inj (a b c : ℕ) : Function.Injective (rpRk2 a b c) := by
  rintro (i | j | k | u) (i' | j' | k' | u') h <;> simp only [rpRk2] at h <;>
    first
      | (exfalso; omega)
      | rfl
      | (have h' := Fin.ext (show i.val = i'.val by omega); subst h'; rfl)
      | (have h' := Fin.ext (show j.val = j'.val by omega); subst h'; rfl)
      | (have h' := Fin.ext (show k.val = k'.val by omega); subst h'; rfl)

theorem rp_rk3_inj (a b c : ℕ) : Function.Injective (rpRk3 a b c) := by
  rintro (i | j | k | u) (i' | j' | k' | u') h <;> simp only [rpRk3] at h <;>
    first
      | (exfalso; omega)
      | rfl
      | (have h' := Fin.ext (show i.val = i'.val by omega); subst h'; rfl)
      | (have h' := Fin.ext (show j.val = j'.val by omega); subst h'; rfl)
      | (have h' := Fin.ext (show k.val = k'.val by omega); subst h'; rfl)

theorem rp_rk5_inj (a b c : ℕ) : Function.Injective (rpRk5 a b c) := by
  rintro (i | j | k | u) (i' | j' | k' | u') h <;> simp only [rpRk5] at h <;>
    first
      | (exfalso; omega)
      | rfl
      | (have h' := Fin.ext (show i.val = i'.val by omega); subst h'; rfl)
      | (have h' := Fin.ext (show j.val = j'.val by omega); subst h'; rfl)
      | (have h' := Fin.ext (show k.val = k'.val by omega); subst h'; rfl)

theorem rp_rk5_lt (a b c : ℕ) (p : rpCol a b c) : rpRk5 a b c p < a + b + c + 1 := by
  rcases p with i | j | k | u <;> simp only [rpRk5] <;> omega

theorem rp_rk4_inj (a b c : ℕ) : Function.Injective (rpRk4 a b c) := by
  rintro (l | p) (l' | p') h <;> simp only [rpRk4] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · exfalso; omega
  · exfalso; omega
  · exact congrArg Sum.inr (rp_rk5_inj a b c (by omega))

theorem rp_exists_ord {ι : Type} [Fintype ι] (rk : ι → ℕ) (h : Function.Injective rk) :
    ∃ e : ι ≃ Fin (Fintype.card ι), ∀ p q, e p < e q ↔ rk p < rk q := by
  let _ : LinearOrder ι := LinearOrder.lift' rk h
  refine ⟨(Fintype.orderIsoFinOfCardEq ι rfl).symm.toEquiv, fun p q => ?_⟩
  exact (Fintype.orderIsoFinOfCardEq ι rfl).symm.lt_iff_lt

noncomputable def rpOrd {ι : Type} [Fintype ι] (rk : ι → ℕ) (h : Function.Injective rk) :
    ι ≃ Fin (Fintype.card ι) := Classical.choose (rp_exists_ord rk h)

theorem rp_ord_lt {ι : Type} [Fintype ι] (rk : ι → ℕ) (h : Function.Injective rk) (p q : ι) :
    rpOrd rk h p < rpOrd rk h q ↔ rk p < rk q :=
  Classical.choose_spec (rp_exists_ord rk h) p q

def rpGj {ι : Type} {D : ℕ} (e : ι ≃ Fin D) (M : ι × ι → Bool) : ι × ι → Bool :=
  fun p => gj D (fun q => M (e.symm q.1, e.symm q.2)) (e p.1, e p.2)

def rpIn1 {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    (rpCol a b c ⊕ Fin m) × (rpCol a b c ⊕ Fin m) → Bool
  | (Sum.inr i, Sum.inl q) => M0 (i, q)
  | _ => false

noncomputable def rpG1 {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    rpCol a b c × rpCol a b c → Bool :=
  fun p => rpGj (rpOrd (rpRk1 a b c m) (rp_rk1_inj a b c m)) (rpIn1 M0) (Sum.inl p.1, Sum.inl p.2)

def rpOnlyX {a b c : ℕ} (R : rpCol a b c × rpCol a b c → Bool) :
    rpCol a b c × rpCol a b c → Bool
  | (Sum.inl i, q) => R (Sum.inl i, q)
  | _ => false

noncomputable def rpG2 {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    rpCol a b c × rpCol a b c → Bool :=
  rpGj (rpOrd (rpRk2 a b c) (rp_rk2_inj a b c)) (rpOnlyX (rpG1 M0))

noncomputable def rpG3 {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    rpCol a b c × rpCol a b c → Bool :=
  rpGj (rpOrd (rpRk3 a b c) (rp_rk3_inj a b c)) (rpOnlyX (rpG2 M0))

def rpDec {a b c : ℕ} (U : rpCol a b c × rpCol a b c → Bool) (r : rpCol a b c → Bool)
    (l : Fin c) : Bool :=
  xor (r (rpZ l)) (rpPar fun k : Fin c => r (rpZ k) && U (rpZ k, rpZ l))

noncomputable def rpIn4 {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    (Fin c ⊕ rpCol a b c) × (Fin c ⊕ rpCol a b c) → Bool
  | (Sum.inr (Sum.inr (Sum.inl j)), Sum.inl l) =>
      rpDec (rpG3 M0) (fun q => rpG1 M0 (rpY j, q)) l
  | (Sum.inr (Sum.inr (Sum.inl j)), Sum.inr q) => rpG1 M0 (rpY j, q)
  | _ => false

noncomputable def rpG4 {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    (Fin c ⊕ rpCol a b c) × (Fin c ⊕ rpCol a b c) → Bool :=
  rpGj (rpOrd (rpRk4 a b c) (rp_rk4_inj a b c)) (rpIn4 M0)

abbrev rpPz {a b c : ℕ} (k : Fin c) : Fin c ⊕ rpCol a b c := Sum.inr (rpZ k)

noncomputable def rpUfix {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin c × rpCol a b c → Bool := fun p =>
  if rpG4 M0 (rpPz p.1, rpPz p.1) = true then
    rpPar (fun k : Fin c => rpG4 M0 (rpPz p.1, rpPz k) && rpG3 M0 (rpZ k, p.2))
  else rpG3 M0 (rpZ p.1, p.2)

noncomputable def rpYt {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin c × rpCol a b c → Bool := fun p =>
  xor (rpG4 M0 (Sum.inl p.1, Sum.inr p.2))
    (rpPar fun k : Fin c => rpG4 M0 (Sum.inl p.1, rpPz k) && rpG3 M0 (rpZ k, p.2))

noncomputable def rpClr1 {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin b × rpCol a b c → Bool := fun p =>
  xor (rpG2 M0 (rpY p.1, p.2))
    (rpPar fun k : Fin c => rpG2 M0 (rpY p.1, rpZ k) && rpG3 M0 (rpZ k, p.2))

noncomputable def rpClr2 {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin b × rpCol a b c → Bool := fun p =>
  xor (rpClr1 M0 p)
    (rpPar fun l : Fin c => rpClr1 M0 (p.1, rpZ l) && rpYt M0 (l, p.2))

noncomputable def rpIn5 {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    rpCol a b c × rpCol a b c → Bool
  | (Sum.inr (Sum.inl j), q) => rpClr2 M0 (j, q)
  | _ => false

noncomputable def rpG5 {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    rpCol a b c × rpCol a b c → Bool :=
  rpGj (rpOrd (rpRk5 a b c) (rp_rk5_inj a b c)) (rpIn5 M0)

noncomputable def rpXOR {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin c × rpCol a b c → Bool := fun p => rpG5 M0 (rpZ p.1, p.2)

noncomputable def rpXY {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin b × rpCol a b c → Bool := fun p => rpG5 M0 (rpY p.1, p.2)

noncomputable def rpDY {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin c × rpCol a b c → Bool := fun p => rpG4 M0 (rpPz p.1, Sum.inr p.2)

noncomputable def rpYZ {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin c × rpCol a b c → Bool := fun p => rpG4 M0 (Sum.inl p.1, Sum.inr p.2)

noncomputable def rpPX {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    (Fin a ⊕ Fin a) × rpCol a b c → Bool
  | (Sum.inl i, q) => rpG3 M0 (rpX i, q)
  | (Sum.inr i, q) => rpG5 M0 (rpX i, q)

noncomputable def rpPY {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin b × rpCol a b c → Bool := fun p => rpG4 M0 (Sum.inr (rpY p.1), Sum.inr p.2)

abbrev rpCNI (c : ℕ) : Type := (Fin c ⊕ Unit) ⊕ (Fin c ⊕ Unit) ⊕ Unit ⊕ Unit ⊕ Unit

noncomputable def rpCN {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    rpCNI c × rpCol a b c → Bool
  | (Sum.inl s, q) => rpG1 M0 (Sum.inr (Sum.inr s), q)
  | (Sum.inr (Sum.inl s), q) => rpG2 M0 (Sum.inr (Sum.inr s), q)
  | (Sum.inr (Sum.inr (Sum.inl _)), q) => rpG3 M0 (rpR, q)
  | (Sum.inr (Sum.inr (Sum.inr (Sum.inl _))), q) => rpG4 M0 (Sum.inr rpR, Sum.inr q)
  | (Sum.inr (Sum.inr (Sum.inr (Sum.inr _))), q) => rpG5 M0 (rpR, q)

noncomputable def rpAxor {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) (k : Fin c) : Bool :=
  rpG5 M0 (rpZ k, rpZ k)

noncomputable def rpAdg {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) (k : Fin c) : Bool :=
  rpG4 M0 (rpPz k, rpPz k)

noncomputable def rpAxz {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) (k : Fin c) : Bool :=
  rpG3 M0 (rpZ k, rpZ k) && !rpG4 M0 (rpPz k, rpPz k)

noncomputable def rpAxy {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) (j : Fin b) : Bool :=
  rpG5 M0 (rpY j, rpY j)

noncomputable def rpAyz {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) (l : Fin c) : Bool :=
  rpG4 M0 (Sum.inl l, Sum.inl l)

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

def ctrlB (u : ZMod 2) : Bool := decide (u ≠ 0)

def ctrlF (b : Bool) : ZMod 2 := if b then 1 else 0

theorem ctrlB_F (b : Bool) : ctrlB (ctrlF b) = b := by cases b <;> decide

theorem ctrlF_B (u : ZMod 2) : ctrlF (ctrlB u) = u := by revert u; decide

theorem ctrlB_add (x y : ZMod 2) : ctrlB (x+y) = xor (ctrlB x) (ctrlB y) := by
  revert x y; decide

theorem ctrlB_mul (x y : ZMod 2) : ctrlB (x*y) = (ctrlB x && ctrlB y) := by
  revert x y; decide

theorem ctrl_add {ι : Type} {S T : ℕ} {f g : (ι → Bool) → ZMod 2}
    (hf : Cb ι S (fun v => ctrlB (f v))) (hg : Cb ι T (fun v => ctrlB (g v))) :
    Cb ι (S + T + 4) (fun v => ctrlB (f v + g v)) :=
  (Cb.xor hf hg).congr fun _ => (ctrlB_add _ _).symm

theorem ctrl_mul {ι : Type} {S T : ℕ} {f g : (ι → Bool) → ZMod 2}
    (hf : Cb ι S (fun v => ctrlB (f v))) (hg : Cb ι T (fun v => ctrlB (g v))) :
    Cb ι (S + T + 1) (fun v => ctrlB (f v * g v)) :=
  (Cb.and hf hg).congr fun _ => (ctrlB_mul _ _).symm

theorem ctrl_sum {ι I : Type} [Fintype I] {S : ℕ} {f : I → (ι → Bool) → ZMod 2}
    (hf : ∀ i, Cb ι S (fun v => ctrlB (f i v))) :
    Cb ι (Fintype.card I * (S + 4) + 1) (fun v => ctrlB (∑ i, f i v)) := by
  apply (Cb.bigXor hf).congr
  intro v
  have he : ∀ i, f i v = if ctrlB (f i v) then 1 else 0 :=
    fun i => (ctrlF_B (f i v)).symm
  unfold ctrlB
  apply decide_eq_decide.mpr
  conv_rhs => rw [Finset.sum_congr rfl fun i _ => he i, Finset.sum_boole]
  rw [Ne, ZMod.natCast_eq_zero_iff]
  simp only [ctrlB, decide_eq_true_eq]
  apply Iff.trans (b := ¬ 2 ∣ (Finset.univ.filter fun i => f i v ≠ 0).card) (by omega)
  apply not_congr
  apply iff_of_eq
  exact congrArg (fun s : Finset I => 2 ∣ s.card) (by ext; simp)

theorem ctrl_entry {ι κ : Type} {S : ℕ} {F : (ι → Bool) → κ → Bool}
    (h : Cmp ι κ S F) (k : κ) : Cb ι S (fun v => F v k) :=
  Cb.comp h (Cb.var k)

theorem ctrl_rewire {ι κ μ : Type} {S : ℕ} {F : (ι → Bool) → κ → Bool}
    (h : Cmp ι κ S F) (e : μ → κ) : Cmp ι μ S (fun v j => F v (e j)) :=
  Cmp.comp h (Cmp.wire e)

def ctrlPacked {N : ℕ} {J : Type} (K : ℕ) (fl : Fin N → Bool)
    (payload : Fin N × J → Bool) (p : Fin K × J) : Bool :=
  decide (∃ i, fl i = true ∧ cnt fl i.val = p.1.val ∧ payload (i,p.2) = true)

theorem ctrl_rank_lt {N : ℕ} (fl : Fin N → Bool) (i : Fin N) (hi : fl i = true) :
    cnt fl i.val < cnt fl N := by
  unfold cnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, by simp [hi], by simp⟩
  · intro j hj
    simpa using (Finset.mem_filter.mp hj).2.2

theorem ctrl_rank_surj {N : ℕ} (fl : Fin N → Bool) (s : ℕ) (hs : s < cnt fl N) :
    ∃ i : Fin N, fl i = true ∧ cnt fl i.val = s := by
  suffices h : ∀ n ≤ N, s < cnt fl n → ∃ i : Fin N, fl i = true ∧ cnt fl i.val = s from
    h N le_rfl hs
  intro n
  induction n with
  | zero => simp [cnt_zero]
  | succ n ih =>
    intro hn he
    have hn' : n < N := by omega
    rw [cnt_succ fl n hn'] at he
    by_cases h : s < cnt fl n
    · exact ih (by omega) h
    · split_ifs at he with hj
      · exact ⟨⟨n,hn'⟩, hj, by change cnt fl n = s; omega⟩
      · omega

theorem ctrlPacked_hit {N K : ℕ} {J : Type} (fl : Fin N → Bool) (payload : Fin N × J → Bool)
    (i : Fin N) (s : Fin K) (j : J) (hi : fl i = true) (hs : cnt fl i.val = s.val) :
    ctrlPacked K fl payload (s,j) = payload (i,j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [ctrlPacked, decide_eq_true_eq]
  constructor
  · rintro ⟨q,hq,hqs,hv⟩
    have he : q = i := fh_cnt_inj (fun p => fl p = true) q i hq hi (hqs.trans hs.symm)
    simpa only [he] using hv
  · exact fun h => ⟨i, hi, hs, h⟩

theorem ctrlPacked_tail {N K : ℕ} {J : Type} (fl : Fin N → Bool) (payload : Fin N × J → Bool)
    (s : Fin K) (j : J) (hs : cnt fl N ≤ s.val) :
    ctrlPacked K fl payload (s,j) = false := by
  unfold ctrlPacked
  apply decide_eq_false
  rintro ⟨i,hi,his,_⟩
  have := ctrl_rank_lt fl i hi
  change cnt fl i.val = s.val at his
  omega

theorem ctrl_pack {ι J : Type} [Fintype J] {S T N K : ℕ}
    {fl : (ι → Bool) → Fin N → Bool} {dat : (ι → Bool) → Fin N × J → Bool}
    (hf : Cmp ι (Fin N) S fl) (hd : Cmp ι (Fin N × J) T dat) :
    Cmp ι (Fin K × J)
      (S + ((N+1)*((K+1)*6)) + T + ((K * Fintype.card J) * (N*3+1)))
      (fun v => ctrlPacked K (fl v) (dat v)) := by
  let B := (Fin N ⊕ (Fin (N+1) × Fin (K+1))) ⊕ (Fin N × J)
  let step (p : Fin K × J) (v : B → Bool) (i : Fin N) : Bool :=
    v (.inl (.inl i)) && v (.inl (.inr (i.castSucc, p.1.castSucc))) && v (.inr (i,p.2))
  have cb (p : Fin K × J) : Cb B (N*3+1) (fun v => decide (∃ i, step p v i = true)) := by
    have hh := Cb.bigOr (I := Fin N) (ι := B) (s := 2) (φ := fun i v => step p v i)
      (fun i => (Cb.and (Cb.and (Cb.var _) (Cb.var _)) (Cb.var _)))
    rw [Fintype.card_fin] at hh
    exact hh.congr fun _ => decide_eq_decide.mpr Iff.rfl
  have hc := Cmp.ofBits (F := fun v (p : Fin K × J) => decide (∃ i, step p v i = true)) cb
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  refine (Cmp.comp (Cmp.pair (hf.comp (cmp_counter N K).keep) hd) hc).congr ?_
  intro v p
  simp [step, ctrlPacked, and_assoc]

def ctrlAffine {d k : ℕ} (L : Fin d × Fin (k+1) → Bool) (x : V k) : V d :=
  (mat L).mulVec (@Fin.snoc k (fun _ => ZMod 2) x 1)

def ctrlPushed {d k W : ℕ} (L : Fin d × Fin (k+1) → Bool)
    (mask : V k → Bool) (T : V k × Fin W → Bool) : V d × Fin W → Bool :=
  untab (fun z => ∑ x : V k, if ctrlAffine L x = z ∧ mask x = true then tab T x else 0)

theorem ctrl_split {R : Type} [AddCommMonoid R] (k : ℕ) (h : V (k+1) → R) :
    (∑ l : V (k+1), h l) =
      (∑ x : V k, h (@Fin.snoc k (fun _ => ZMod 2) x 0)) +
      (∑ x : V k, h (@Fin.snoc k (fun _ => ZMod 2) x 1)) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (k+1) => ZMod 2)).sum_comp, Fintype.sum_prod_type]
  have h2 : ∀ F : ZMod 2 → R, ∑ x, F x = F 0 + F 1 := fun F => Fin.sum_univ_two F
  rw [h2]
  rfl

theorem ctrl_push {ι : Type} {S T U d k W : ℕ}
    {L : (ι → Bool) → Fin d × Fin (k+1) → Bool} {msk : (ι → Bool) → V k → Bool}
    {tabB : (ι → Bool) → V k × Fin W → Bool}
    (hL : Cmp ι (Fin d × Fin (k+1)) S L) (hm : Cmp ι (V k) T msk)
    (ht : Cmp ι (V k × Fin W) U tabB) :
    Cmp ι (V d × Fin W) (S + ((T + U) + 2^(k+1)*W) + tcost d (k+1) W)
      (fun v => ctrlPushed (L v) (msk v) (tabB v)) := by
  let B := V k ⊕ (V k × Fin W)
  let pad (v : B → Bool) (p : V (k+1) × Fin W) : Bool :=
    if p.1 (Fin.last k) = 1 then
      v (.inl (Fin.init p.1)) && v (.inr (Fin.init p.1, p.2))
    else false
  have hp (p : V (k+1) × Fin W) : Cb B 1 (fun v => pad v p) := by
    by_cases h : p.1 (Fin.last k) = 1
    · simpa [pad,h] using Cb.and (Cb.var (ι := B) (.inl (Fin.init p.1)))
        (Cb.var (ι := B) (.inr (Fin.init p.1,p.2)))
    · simpa [pad,h] using Cb.const (ι := B) false
  have hb := Cmp.ofBits (F := pad) hp
  simp only [Fintype.card_prod, fp_cardV, Fintype.card_fin, Nat.mul_one] at hb
  have hc := hL.pair ((hm.pair ht).comp hb)
  refine (hc.comp (cmp_push d (k+1) W)).congr ?_
  intro v p
  unfold ctrlPushed untab
  apply congrArg (fun u : BitVec W => u.getLsbD p.2.val)
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [ctrl_split k]
  simp only [Sum.elim_inl, Sum.elim_inr, tab, pad, Fin.snoc_last, zero_ne_one,
    ite_false, fp_bv_false, ite_self, Finset.sum_const_zero, zero_add, ite_true, Fin.init_snoc]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : msk v x = true
  · simp [ctrlAffine, h]
  · simp [ctrlAffine, Bool.eq_false_iff.mpr h, fp_bv_false]

def ctrlSat {I : Type} [Fintype I] {k : ℕ} (R : I × Fin (k+1) → Bool) (x : V k) : Bool :=
  decide (∀ i, (∑ j : Fin k, ctrlF (R (i,j.castSucc)) * x j) = ctrlF (R (i,Fin.last k)))

theorem ctrl_pin {ι I : Type} [Fintype I] {k S : ℕ}
    {R : (ι → Bool) → I × Fin (k+1) → Bool} (hr : Cmp ι (I × Fin (k+1)) S R) :
    Cmp ι (V k) (S + 2^k * (Fintype.card I * (k*6+7) + 1))
      (fun v => ctrlSat (R v)) := by
  let B := I × Fin (k+1)
  have mit (x : V k) (i : I) (j : Fin k) :
      Cb B 2 (fun r => ctrlB (ctrlF (r (i,j.castSucc)) * x j)) := by
    have hb : Cb B 0 (fun r => ctrlB (ctrlF (r (i,j.castSucc)))) :=
      (Cb.var (i,j.castSucc)).congr fun _ => (ctrlB_F _).symm
    exact ctrl_mul hb (Cb.const (ctrlB (x j)))
  have lit (x : V k) (i : I) :
      Cb B (k*6+6) (fun r => decide
        ((∑ j : Fin k, ctrlF (r (i,j.castSucc)) * x j) = ctrlF (r (i,Fin.last k)))) := by
    let A (r : B → Bool) := ∑ j : Fin k, ctrlF (r (i,j.castSucc)) * x j
    have ha : Cb B (k*6+1) (fun r => ctrlB (A r)) := by
      simpa [A] using ctrl_sum (mit x i)
    have hb : Cb B 0 (fun r => r (i,Fin.last k)) := Cb.var _
    have hh : ∀ u b, (!(xor (ctrlB u) b)) = decide (u = ctrlF b) := by decide
    exact (Cb.not (ha.xor hb)).congr fun r => hh (A r) (r (i,Fin.last k))
  have bit (x : V k) : Cb B (Fintype.card I * (k*6+7) + 1) (fun r => ctrlSat r x) := by
    apply (Cb.bigAnd (fun i => lit x i)).congr
    intro r
    apply decide_eq_decide.mpr
    simp
  have h := Cmp.ofBits (F := fun r (x : V k) => ctrlSat r x) bit
  rw [fp_cardV] at h
  exact hr.comp h

theorem ctrl_cnt_test {ι : Type} {N S : ℕ} {fl : (ι → Bool) → Fin N → Bool}
    (h : Cmp ι (Fin N) S fl) (i : Fin (N+1)) (k : ℕ) :
    Cb ι (S + (N+1)*((k+1)*6)) (fun v => decide (cnt (fl v) i.val = k)) :=
  ctrl_entry (h.comp (cmp_counter N k)) (i, Fin.last k)

theorem ctrl_gj_map {ι κ : Type} {D S : ℕ} {R : (ι → Bool) → Fin D × Fin D → Bool}
    (h : Cmp ι (Fin D × Fin D) S R) (e : κ → Fin D × Fin D) :
    Cmp ι κ (S + gjCost D) (fun v p => gj D (R v) (e p)) :=
  ctrl_rewire (h.comp (cmp_gj D)) e

def ctrlPushExtra (w k W : ℕ) := (2^k*W + 2^(k+1)*W) + tcost w (k+1) W

theorem ctrl_push_extra {w k W P : ℕ} (hk : k ≤ w) (hw : w+2 ≤ P)
    (hW : W+1 ≤ 4*P) : ctrlPushExtra w k W ≤ 2^18 * P^5 * 2^w := by
  have hP : 1 ≤ P := by omega
  have hp : 2^k ≤ 2^w := Nat.pow_le_pow_right (by norm_num) hk
  have hq : 2^(max w (k+1)) ≤ 2^(w+1) :=
    Nat.pow_le_pow_right (by norm_num) (max_le (by omega) (by omega))
  have hs : w + (k+1) + 2 ≤ 2*P := by omega
  have hW' : W ≤ 4*P := by omega
  have hpow : P ≤ P^5 := by simpa using Nat.pow_le_pow_right hP (show 1 ≤ 5 by decide)
  unfold ctrlPushExtra tcost
  calc
    _ ≤ (2^w*(4*P) + 2^(w+1)*(4*P)) + 2^9*(2*P)^4*(4*P)*2^(w+1) := by
      gcongr
    _ = 12 * P * 2^w + 65536 * P^5 * 2^w := by rw [pow_succ]; ring
    _ ≤ 12 * P^5 * 2^w + 65536 * P^5 * 2^w := by gcongr
    _ = (12+65536) * P^5 * 2^w := by ring
    _ ≤ _ := by gcongr; norm_num

theorem ctrl_bundle {a b c m t w W S : ℕ} (ea : Fin (2^a) ≃ V a) (eb : Fin (2^b) ≃ V b)
    {D : (In0 a b c m t → Bool) → Fin 5 × Fin (w+1) → Bool}
    {L : (In0 a b c m t → Bool) → Fin w × Fin (a+1) → Bool}
    {M : (In0 a b c m t → Bool) → Fin w × Fin (b+1) → Bool}
    {E : (In0 a b c m t → Bool) → Fin w × Fin c → Bool}
    {X : (In0 a b c m t → Bool) → V a → Bool}
    {Y : (In0 a b c m t → Bool) → V b → Bool}
    {Z : (In0 a b c m t → Bool) → V c → Bool}
    (hD : Cmp _ _ S D) (hL : Cmp _ _ S L) (hM : Cmp _ _ S M)
    (hE : Cmp _ _ S E) (hX : Cmp _ _ S X) (hY : Cmp _ _ S Y) (hZ : Cmp _ _ S Z) :
    Cmp (In0 a b c m t)
      ((Fin 5 × Fin (w+1)) ⊕ ((V w × Fin W) ⊕ ((V w × Fin W) ⊕ ((Fin w × Fin c) ⊕ V c))))
      (7*S + ctrlPushExtra w a W + ctrlPushExtra w b W)
      (fun v => Sum.elim (D v) (Sum.elim (ctrlPushed (L v) (X v) (fTab a b c m t W ea v))
        (Sum.elim (ctrlPushed (M v) (Y v) (gTab a b c m t W eb v)) (Sum.elim (E v) (Z v))))) := by
  have hf := ctrl_push hL hX (fz4_fTab a b c m t W ea)
  have hg := ctrl_push hM hY (fz4_gTab a b c m t W eb)
  exact (hD.pair (hf.pair (hg.pair (hE.pair hZ)))).mono (by unfold ctrlPushExtra; omega)

theorem ctrl_eval_fiber {I J R : Type} [Fintype I] [Fintype J] [DecidableEq J] [Semiring R]
    (L : I → J) (m : I → Bool) (F : I → R) (K : J → R) :
    (∑ j, (∑ i, if L i = j ∧ m i = true then F i else 0) * K j) =
      ∑ i, if m i then F i * K (L i) else 0 := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases m i <;> simp [ite_mul]

theorem ctrl_regroup {a b w W : ℕ}
    (L : Fin w × Fin (a+1) → Bool) (M : Fin w × Fin (b+1) → Bool)
    (mx : V a → Bool) (my : V b → Bool) (F : V a × Fin W → Bool) (G : V b × Fin W → Bool)
    (R : V w → V w → Prop) [DecidableRel R] :
    (∑ u, ∑ v, if R u v then tab (ctrlPushed L mx F) u * tab (ctrlPushed M my G) v else 0) =
      ∑ x, ∑ y, if mx x = true ∧ my y = true ∧ R (ctrlAffine L x) (ctrlAffine M y) then
        tab F x * tab G y else 0 := by
  classical
  let h (u v : V w) : BitVec W := if R u v then 1 else 0
  let ff := tab (ctrlPushed L mx F)
  let gg := tab (ctrlPushed M my G)
  have t (u v : V w) : (if R u v then ff u * gg v else 0) = ff u * (gg v * h u v) := by
    by_cases hr : R u v <;> simp [h,hr]
  change (∑ u, ∑ v, if R u v then ff u * gg v else 0) = _
  simp_rw [t, ← Finset.mul_sum]
  dsimp only [ff, gg, ctrlPushed]
  rw [tab_untab, tab_untab, ctrl_eval_fiber]
  apply Finset.sum_congr rfl
  intro x _
  cases mx x with
  | false => simp
  | true =>
    simp only [ite_true, true_and, ctrl_eval_fiber, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hr : R (ctrlAffine L x) (ctrlAffine M y) <;> cases my y <;> simp [hr,h]

theorem ctrl_total {a b c w m t W : ℕ} (ea : Fin (2^a) ≃ V a) (eb : Fin (2^b) ≃ V b)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t)) (z : V c)
    (L : Fin w × Fin (a+1) → Bool) (M : Fin w × Fin (b+1) → Bool)
    (X : V a → Bool) (Y : V b → Bool) (Z : Bool)
    (R : V w → V w → Prop) [DecidableRel R]
    (hs : ∀ x y, (∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i) ↔
      X x = true ∧ Y y = true ∧ Z = true ∧ R (ctrlAffine L x) (ctrlAffine M y)) :
    BitVec.ofNat W (∑ ix : Fin (2^a), ∑ iy : Fin (2^b),
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ z = rhs i) then
        (f ix).val * (g iy).val else 0) = if Z then
      ∑ x, ∑ y, if R x y then
        tab (ctrlPushed L X (fTab a b c m t W ea (inpOf H rhs f g))) x *
        tab (ctrlPushed M Y (gTab a b c m t W eb (inpOf H rhs f g))) y else 0
      else 0 := by
  rw [← fz5_total, ctrl_regroup]
  cases Z <;> simp [hs, fz5_tabf, fz5_tabg]

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

def ceCat {α : Type} {b c : ℕ} (f0 f1 f2 : Fin c → α) (f3 : Fin b → α) (f4 : Fin c → α) :
    Fin (c + c + c + b + c) → α :=
  Fin.append (Fin.append (Fin.append (Fin.append f0 f1) f2) f3) f4

def ceSel {n : ℕ} {α : Type} (l : α) (f : Fin n → α) (j : Fin (n + 1)) : α :=
  if h : j.val < n then f ⟨j.val, h⟩ else l

def ceColA {a b c : ℕ} (j : Fin (a + 1)) : rpCol a b c := ceSel rpR (fun i => rpX i) j

def ceColB {a b c : ℕ} (j : Fin (b + 1)) : rpCol a b c := ceSel rpR (fun i => rpY i) j

def ceColC {a b c : ℕ} (j : Fin (c + 1)) : rpCol a b c := ceSel rpR (fun i => rpZ i) j

noncomputable def ceFlU {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin (c + c + c + b + c) → Bool :=
  ceCat (rpAxor M0) (rpAdg M0) (rpAxz M0) (rpAxy M0) (fun _ => false)

noncomputable def ceFlV {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin (c + c + c + b + c) → Bool :=
  ceCat (rpAxor M0) (rpAdg M0) (fun _ => false) (rpAxy M0) (rpAyz M0)

noncomputable def ceFlT {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin (c + c + c + b + c) → Bool :=
  ceCat (rpAxor M0) (rpAdg M0) (rpAxz M0) (fun _ => false) (rpAyz M0)

noncomputable def cePayU {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin (c + c + c + b + c) × Fin (a + 1) → Bool := fun p =>
  ceCat (fun k => rpXOR M0 (k, ceColA p.2)) (fun k => rpUfix M0 (k, ceColA p.2))
    (fun k => rpUfix M0 (k, ceColA p.2)) (fun j => rpXY M0 (j, ceColA p.2))
    (fun _ => false) p.1

noncomputable def cePayV {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin (c + c + c + b + c) × Fin (b + 1) → Bool := fun p =>
  ceCat (fun k => ceSel false (fun j => rpXOR M0 (k, rpY j)) p.2)
    (fun k => rpDY M0 (k, ceColB p.2)) (fun _ => false)
    (fun i => ceSel false (fun j => rpXY M0 (i, rpY j)) p.2)
    (fun l => rpYZ M0 (l, ceColB p.2)) p.1

noncomputable def cePayT {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin (c + c + c + b + c) × Fin c → Bool := fun p =>
  ceCat (fun k => rpXOR M0 (k, rpZ p.2)) (fun k => rpUfix M0 (k, rpZ p.2))
    (fun k => rpUfix M0 (k, rpZ p.2)) (fun _ => false)
    (fun l => rpYZ M0 (l, rpZ p.2)) p.1

noncomputable def ceL {a b c m : ℕ} (w : ℕ) (M0 : Fin m × rpCol a b c → Bool) :
    Fin w × Fin (a + 1) → Bool := ctrlPacked w (ceFlU M0) (cePayU M0)

noncomputable def ceM {a b c m : ℕ} (w : ℕ) (M0 : Fin m × rpCol a b c → Bool) :
    Fin w × Fin (b + 1) → Bool := ctrlPacked w (ceFlV M0) (cePayV M0)

noncomputable def ceE {a b c m : ℕ} (w : ℕ) (M0 : Fin m × rpCol a b c → Bool) :
    Fin w × Fin c → Bool := ctrlPacked w (ceFlT M0) (cePayT M0)

noncomputable def ceRX {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    (Fin a ⊕ Fin a) × Fin (a + 1) → Bool := fun p => rpPX M0 (p.1, ceColA p.2)

noncomputable def ceRY {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    Fin b × Fin (b + 1) → Bool := fun p => rpPY M0 (p.1, ceColB p.2)

noncomputable def ceRZ {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) :
    rpCNI c × Fin (c + 1) → Bool := fun p => rpCN M0 (p.1, ceColC p.2)

noncomputable def ceDims {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) : Fin 5 → ℕ :=
  ![cnt (rpAxor M0) c, cnt (rpAdg M0) c, cnt (rpAxy M0) b, cnt (rpAxz M0) c, cnt (rpAyz M0) c]

def ceIdx {a b c : ℕ} : rpCol a b c → Fin (a + b + c + 1)
  | Sum.inl i => ⟨i.val, by omega⟩
  | Sum.inr (Sum.inl j) => ⟨a + j.val, by omega⟩
  | Sum.inr (Sum.inr (Sum.inl k)) => ⟨a + b + k.val, by omega⟩
  | Sum.inr (Sum.inr (Sum.inr _)) => ⟨a + b + c, by omega⟩

def ceM0 (a b c m t : ℕ) (v : In0 a b c m t → Bool) : Fin m × rpCol a b c → Bool :=
  fun p => v (Sum.inl (p.1, ceIdx p.2))

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

structure rpFacts {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool) : Prop where
  sat : ∀ w : rpCol a b c → ZMod 2,
    (∀ i, rpEv w (fun q => M0 (i, q)) = 0) ↔
      (∀ k, rpEv w (fun q => rpXOR M0 (k, q)) = 0) ∧
      (∀ j, rpEv w (fun q => rpXY M0 (j, q)) = 0) ∧
      (∀ k, rpEv w (fun q => rpUfix M0 (k, q)) = 0) ∧
      (∀ k, rpEv w (fun q => rpDY M0 (k, q)) = 0) ∧
      (∀ l, rpEv w (fun q => rpYZ M0 (l, q)) = 0) ∧
      (∀ p, rpEv w (fun q => rpPX M0 (p, q)) = 0) ∧
      (∀ p, rpEv w (fun q => rpPY M0 (p, q)) = 0) ∧
      (∀ p, rpEv w (fun q => rpCN M0 (p, q)) = 0)
  xy_z : ∀ (j : Fin b) (k : Fin c), rpXY M0 (j, rpZ k) = false
  ux_y : ∀ (k : Fin c) (j : Fin b), rpUfix M0 (k, rpY j) = false
  dy_x : ∀ (k : Fin c) (i : Fin a), rpDY M0 (k, rpX i) = false
  yz_x : ∀ (l : Fin c) (i : Fin a), rpYZ M0 (l, rpX i) = false
  px_y : ∀ (p : Fin a ⊕ Fin a) (j : Fin b), rpPX M0 (p, rpY j) = false
  px_z : ∀ (p : Fin a ⊕ Fin a) (k : Fin c), rpPX M0 (p, rpZ k) = false
  py_x : ∀ (p : Fin b) (i : Fin a), rpPY M0 (p, rpX i) = false
  py_z : ∀ (p : Fin b) (k : Fin c), rpPY M0 (p, rpZ k) = false
  cn_x : ∀ (p : rpCNI c) (i : Fin a), rpCN M0 (p, rpX i) = false
  cn_y : ∀ (p : rpCNI c) (j : Fin b), rpCN M0 (p, rpY j) = false
  dg_z : ∀ (k l : Fin c), rpAdg M0 k = true → rpUfix M0 (k, rpZ l) = rpDY M0 (k, rpZ l)
  xor_off : ∀ (k : Fin c) (q : rpCol a b c), rpAxor M0 k = false → rpXOR M0 (k, q) = false
  xy_off : ∀ (j : Fin b) (q : rpCol a b c), rpAxy M0 j = false → rpXY M0 (j, q) = false
  dy_off : ∀ (k : Fin c) (q : rpCol a b c), rpAdg M0 k = false → rpDY M0 (k, q) = false
  yz_off : ∀ (l : Fin c) (q : rpCol a b c), rpAyz M0 l = false → rpYZ M0 (l, q) = false
  ux_off : ∀ (k : Fin c) (q : rpCol a b c), rpAdg M0 k = false → rpAxz M0 k = false →
    rpUfix M0 (k, q) = false
  dg_xz : ∀ k : Fin c, rpAdg M0 k = true → rpAxz M0 k = false
  fit_x : (Finset.univ.filter (fun k => rpAxor M0 k = true)).card +
      (Finset.univ.filter (fun k => rpAdg M0 k = true)).card +
      (Finset.univ.filter (fun j => rpAxy M0 j = true)).card +
      (Finset.univ.filter (fun k => rpAxz M0 k = true)).card ≤ a
  fit_y : (Finset.univ.filter (fun k => rpAxor M0 k = true)).card +
      (Finset.univ.filter (fun k => rpAdg M0 k = true)).card +
      (Finset.univ.filter (fun j => rpAxy M0 j = true)).card +
      (Finset.univ.filter (fun l => rpAyz M0 l = true)).card ≤ b
  fit_z : (Finset.univ.filter (fun k => rpAxor M0 k = true)).card +
      (Finset.univ.filter (fun k => rpAdg M0 k = true)).card +
      (Finset.univ.filter (fun k => rpAxz M0 k = true)).card +
      (Finset.univ.filter (fun l => rpAyz M0 l = true)).card ≤ c

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

theorem swCntFalse {n : Nat} (j : Nat) : cnt (fun _ : Fin n => false) j = 0 := by
  simp [cnt]

theorem swCntAll {m : Nat} (f : Fin m → Bool) (j : Nat) (hj : m ≤ j) :
    cnt f j = cnt f m := by
  unfold cnt
  congr 1
  ext i
  simp [show i.val < j by omega]

theorem swCntAppendLeft {m n : Nat} (f : Fin m → Bool) (g : Fin n → Bool) (j : Nat) (h : j ≤ m) :
    cnt (Fin.append f g) j = cnt f j := by
  induction j with
  | zero => simp [cnt_zero]
  | succ j ih =>
    have hj : j < m := by omega
    rw [cnt_succ _ _ (by omega), cnt_succ _ _ hj, ih (by omega)]
    exact congrArg (fun x : Bool => cnt f j + if x = true then 1 else 0)
      (Fin.append_left f g (⟨j,hj⟩ : Fin m))

theorem swCntAppendRight {m n : Nat} (f : Fin m → Bool) (g : Fin n → Bool)
    (j : Nat) (h : j ≤ n) :
    cnt (Fin.append f g) (m+j) = cnt f m + cnt g j := by
  induction j with
  | zero => simp [swCntAppendLeft, cnt_zero]
  | succ j ih =>
    have hj : j < n := by omega
    rw [Nat.add_succ, cnt_succ _ _ (by omega), cnt_succ _ _ hj, ih (by omega), Nat.add_assoc]
    have e := Fin.append_right f g (⟨j,hj⟩ : Fin n)
    simpa only [Fin.natAdd_mk] using congrArg
      (fun x : Bool => cnt f m + (cnt g j + if x = true then 1 else 0)) e

theorem swCntAppendAll {m n : Nat} (f : Fin m → Bool) (g : Fin n → Bool) :
    cnt (Fin.append f g) (m+n) = cnt f m + cnt g n :=
  swCntAppendRight f g n le_rfl

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

theorem ce_fits {a b c m w : ℕ} {M : Fin m × rpCol a b c → Bool} (hF : rpFacts M)
    (ha : a ≤ w) (hb : b ≤ w) (hc : c ≤ w) : fitsW w (ceDims M) := by
  exact ⟨by simpa [ceDims,cnt] using hF.fit_x.trans ha,
    by simpa [ceDims,cnt] using hF.fit_y.trans hb, by simpa [ceDims,cnt] using hF.fit_z.trans hc⟩

abbrev ceSeg (b c : ℕ) := Fin c ⊕ Fin c ⊕ Fin c ⊕ Fin b ⊕ Fin c

def cePos {b c : ℕ} : ceSeg b c → Fin (c+c+c+b+c)
  | .inl k => (((k.castAdd c).castAdd c).castAdd b).castAdd c
  | .inr (.inl k) => (((k.natAdd c).castAdd c).castAdd b).castAdd c
  | .inr (.inr (.inl k)) => ((k.natAdd (c+c)).castAdd b).castAdd c
  | .inr (.inr (.inr (.inl j))) => (j.natAdd (c+c+c)).castAdd c
  | .inr (.inr (.inr (.inr k))) => k.natAdd (c+c+c+b)

def ceChoose {b c : ℕ} {A : Type} (f g h : Fin c → A) (l : Fin b → A) (r : Fin c → A) :
    ceSeg b c → A := Sum.elim f (Sum.elim g (Sum.elim h (Sum.elim l r)))

theorem ceCat_pos {b c : ℕ} {A : Type} (f g h : Fin c → A) (l : Fin b → A) (r : Fin c → A)
    (p : ceSeg b c) : ceCat f g h l r (cePos p) = ceChoose f g h l r p := by
  rcases p with p|p|p|p|p <;> simp only [cePos,ceCat,ceChoose,
    Fin.append_left,Fin.append_right,Sum.elim_inl,Sum.elim_inr]

def ceRank {b c : ℕ} (f g h : Fin c → Bool) (l : Fin b → Bool) (r : Fin c → Bool) :
    ceSeg b c → ℕ :=
  ceChoose (fun k => cnt f k.val) (fun k => cnt f c + cnt g k.val)
    (fun k => cnt f c + cnt g c + cnt h k.val)
    (fun j => cnt f c + cnt g c + cnt h c + cnt l j.val)
    (fun k => cnt f c + cnt g c + cnt h c + cnt l b + cnt r k.val)

theorem ceApL {n k : ℕ} (f : Fin n → Bool) (g : Fin k → Bool) (i : Fin n) :
    cnt (Fin.append f g) (i.castAdd k).val = cnt f i.val :=
  swCntAppendLeft f g i.val (Nat.le_of_lt i.isLt)

theorem ceApR {n k : ℕ} (f : Fin n → Bool) (g : Fin k → Bool) (i : Fin k) :
    cnt (Fin.append f g) (i.natAdd n).val = cnt f n + cnt g i.val :=
  swCntAppendRight f g i.val (Nat.le_of_lt i.isLt)

theorem ceCat_cnt {b c : ℕ} (f g h : Fin c → Bool) (l : Fin b → Bool) (r : Fin c → Bool)
    (p : ceSeg b c) : cnt (ceCat f g h l r) (cePos p).val = ceRank f g h l r p := by
  rcases p with p|p|p|p|p <;> simp only [cePos,ceCat,ceRank,ceChoose,Sum.elim_inl,Sum.elim_inr,
    ceApL,ceApR,swCntAppendAll]

theorem ceSel_cast {n : ℕ} {A : Type} (v : A) (f : Fin n → A) (i : Fin n) :
    ceSel v f i.castSucc = f i := by simp [ceSel]

theorem ceSel_last {n : ℕ} {A : Type} (v : A) (f : Fin n → A) :
    ceSel v f (Fin.last n) = v := by simp [ceSel]

theorem ceHit {N n w : ℕ} (fl : Fin N → Bool) (pay : Fin N × Fin n → Bool)
    (x : V n) (fit : cnt fl N ≤ w) (i : Fin N) (hi : fl i = true) :
    co ((mat (ctrlPacked w fl pay)).mulVec x) (cnt fl i.val) =
      ∑ j, ctrlF (pay (i,j))*x j := by
  have hlt := (ctrl_rank_lt fl i hi).trans_le fit
  simp only [co,dif_pos hlt,Matrix.mulVec,dotProduct,mat,
    ctrlPacked_hit fl pay i (⟨_,hlt⟩ : Fin w) _ hi rfl,ctrlF]

theorem ceTail {N n w : ℕ} (fl : Fin N → Bool) (pay : Fin N × Fin n → Bool)
    (x : V n) (i : Fin w) (hi : cnt fl N ≤ i.val) :
    (mat (ctrlPacked w fl pay)).mulVec x i = 0 := by
  simp [Matrix.mulVec,dotProduct,mat,ctrlPacked_tail fl pay i _ hi]

def ceDot {a b c n : ℕ} (r : rpCol a b c → Bool) (e : Fin n → rpCol a b c) (x : V n) :
    ZMod 2 := ∑ j, ctrlF (r (e j)) * x j

def ceRow {I C : Type} (r : I × C → Bool) (i : I) : C → Bool := fun q => r (i,q)

section
variable {a b c m w : ℕ} (M : Fin m × rpCol a b c → Bool) (x : V a) (y : V b) (z : V c)

theorem ceU_hit (fit : fitsW w (ceDims M)) (p : ceSeg b c)
    (hp : ceChoose (rpAxor M) (rpAdg M) (rpAxz M) (rpAxy M) (fun _ => false) p = true) :
    co (ctrlAffine (ceL w M) x)
      (ceRank (rpAxor M) (rpAdg M) (rpAxz M) (rpAxy M) (fun _ => false) p) =
      let v := fun r : rpCol a b c → Bool => ceDot r rpX x + ctrlF (r rpR)
      ceChoose (fun k => v (ceRow (rpXOR M) k)) (fun k => v (ceRow (rpUfix M) k))
        (fun k => v (ceRow (rpUfix M) k)) (fun j => v (ceRow (rpXY M) j)) (fun _ => 0) p := by
  have hf : cnt (ceFlU M) (c+c+c+b+c) ≤ w := by
    simp only [ceFlU,ceCat,swCntAppendAll,swCntFalse,Nat.add_zero]
    have h := fit.1
    simp [ceDims] at h
    omega
  have h := ceHit (ceFlU M) (cePayU M) (@Fin.snoc a (fun _ => ZMod 2) x 1) hf (cePos p)
    (by simpa only [ceFlU,ceCat_pos] using hp)
  rw [Fin.sum_univ_castSucc] at h
  simp only [ceFlU,ceCat_cnt,cePayU,ceCat_pos,Fin.snoc_castSucc,Fin.snoc_last,mul_one] at h
  refine h.trans ?_
  rcases p with k|k|k|j|k <;>
    simp only [ceChoose,ceColA,ceSel_cast,ceSel_last,ceRow,ceDot,Sum.elim_inl,Sum.elim_inr] <;>
    first | rfl | simp [ctrlF]

theorem ceV_hit (fit : fitsW w (ceDims M)) (p : ceSeg b c)
    (hp : ceChoose (rpAxor M) (rpAdg M) (fun _ => false) (rpAxy M) (rpAyz M) p = true) :
    co (ctrlAffine (ceM w M) y)
      (ceRank (rpAxor M) (rpAdg M) (fun _ => false) (rpAxy M) (rpAyz M) p) =
      let v := fun r : rpCol a b c → Bool => ceDot r rpY y + ctrlF (r rpR)
      ceChoose (fun k => ceDot (ceRow (rpXOR M) k) rpY y) (fun k => v (ceRow (rpDY M) k))
        (fun _ => 0) (fun j => ceDot (ceRow (rpXY M) j) rpY y) (fun k => v (ceRow (rpYZ M) k)) p := by
  have hf : cnt (ceFlV M) (c+c+c+b+c) ≤ w := by
    simpa [ceFlV,ceCat,swCntAppendAll,swCntFalse,ceDims] using fit.2.1
  have h := ceHit (ceFlV M) (cePayV M) (@Fin.snoc b (fun _ => ZMod 2) y 1) hf (cePos p)
    (by simpa only [ceFlV,ceCat_pos] using hp)
  rw [Fin.sum_univ_castSucc] at h
  simp only [ceFlV,ceCat_cnt,cePayV,ceCat_pos,Fin.snoc_castSucc,Fin.snoc_last,mul_one] at h
  refine h.trans ?_
  rcases p with k|k|k|j|k <;>
    simp only [ceChoose,ceColB,ceSel_cast,ceSel_last,ceRow,ceDot,Sum.elim_inl,Sum.elim_inr] <;>
    first | rfl | simp [ctrlF,ite_mul]

theorem ceT_hit (fit : fitsW w (ceDims M)) (p : ceSeg b c)
    (hp : ceChoose (rpAxor M) (rpAdg M) (rpAxz M) (fun _ => false) (rpAyz M) p = true) :
    co ((mat (ceE w M)).mulVec z)
      (ceRank (rpAxor M) (rpAdg M) (rpAxz M) (fun _ => false) (rpAyz M) p) =
      let v := fun r : rpCol a b c → Bool => ceDot r rpZ z
      ceChoose (fun k => v (ceRow (rpXOR M) k)) (fun k => v (ceRow (rpUfix M) k))
        (fun k => v (ceRow (rpUfix M) k)) (fun _ => 0) (fun k => v (ceRow (rpYZ M) k)) p := by
  have hf : cnt (ceFlT M) (c+c+c+b+c) ≤ w := by
    simpa [ceFlT,ceCat,swCntAppendAll,swCntFalse,ceDims] using fit.2.2
  have h := ceHit (ceFlT M) (cePayT M) z hf (cePos p) (by simpa only [ceFlT,ceCat_pos] using hp)
  simp only [ceFlT,ceCat_cnt,cePayT,ceCat_pos] at h
  refine h.trans ?_
  rcases p with k|k|k|j|k <;> simp only [ceChoose,ceRow,ceDot,Sum.elim_inl,Sum.elim_inr] <;>
    first | rfl | simp [ctrlF]

end

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

def swVal {a b c n : Nat} (R : rpCol a b c → Bool) (p : Fin n → rpCol a b c) (x : V n) :
    ZMod 2 := ∑ i, rpBit (R (p i)) * x i

def swRhs {a b c : Nat} (R : rpCol a b c → Bool) : ZMod 2 := rpBit (R rpR)

def swSlotEqs {a b c m : Nat} (M : Fin m × rpCol a b c → Bool) (x : V a) (y : V b) (z : V c) : Prop :=
  (∀ i, rpAxor M i = true → let R := fun q => rpXOR M (i,q)
    (swVal R rpX x + swRhs R) + swVal R rpY y = swVal R rpZ z) ∧
  (∀ i, rpAdg M i = true →
    let R := fun q => rpUfix M (i,q)
    let S := fun q => rpDY M (i,q)
    swVal R rpX x + swRhs R = swVal R rpZ z ∧ swVal S rpY y + swRhs S = swVal R rpZ z) ∧
  (∀ i, rpAxz M i = true → let R := fun q => rpUfix M (i,q)
    swVal R rpX x + swRhs R = swVal R rpZ z) ∧
  (∀ i, rpAxy M i = true → let R := fun q => rpXY M (i,q)
    swVal R rpX x + swRhs R = swVal R rpY y) ∧
  (∀ i, rpAyz M i = true → let R := fun q => rpYZ M (i,q)
    swVal R rpY y + swRhs R = swVal R rpZ z)

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

theorem swRankQuant {n : Nat} (f : Fin n → Bool) (P : Nat → Prop) (Q : Fin n → Prop)
    (h : ∀ i, f i = true → (P (cnt f i.val) ↔ Q i)) :
    (∀ j < cnt f n, P j) ↔ ∀ i, f i = true → Q i := by
  constructor
  · intro hh i hi
    exact (h i hi).mp (hh _ (ctrl_rank_lt f i hi))
  · intro hh j hj
    obtain ⟨i,hi,rfl⟩ := ctrl_rank_surj f j hj
    exact (h i hi).mpr (hh i hi)

theorem swSlotsIff {a b c m w : Nat} (M : Fin m × rpCol a b c → Bool)
    (x : V a) (y : V b) (z : V c) (fit : fitsW w (ceDims M)) :
    Std w (ceDims M 0) (ceDims M 1) (ceDims M 2) (ceDims M 3) (ceDims M 4)
      (ctrlAffine (ceL w M) x) (ctrlAffine (ceM w M) y) ((mat (ceE w M)).mulVec z) ↔
      swSlotEqs M x y z := by
  let q := cnt (rpAxor M) c
  let d := cnt (rpAdg M) c
  let k := cnt (rpAxy M) b
  let e := cnt (rpAxz M) c
  let l := cnt (rpAyz M) c
  let U := ctrlAffine (ceL w M) x
  let Vv := ctrlAffine (ceM w M) y
  let Z := (mat (ceE w M)).mulVec z
  have tu : ∀ j : Fin w, q+d+e+k ≤ j.val → U j = 0 := by
    intro j hj
    exact ceTail _ _ _ _ (by simpa only [ceFlU,ceCat,swCntAppendAll,swCntFalse,Nat.add_zero]
      using hj)
  have tv : ∀ j : Fin w, q+d+k+l ≤ j.val → Vv j = 0 := by
    intro j hj
    exact ceTail _ _ _ _ (by simpa only [ceFlV,ceCat,swCntAppendAll,swCntFalse,Nat.add_zero]
      using hj)
  have tz : ∀ j : Fin w, q+d+e+l ≤ j.val → Z j = 0 := by
    intro j hj
    exact ceTail _ _ _ _ (by simpa only [ceFlT,ceCat,swCntAppendAll,swCntFalse,Nat.add_zero]
      using hj)
  change Std w q d k e l U Vv Z ↔ _
  unfold Std swSlotEqs
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · refine swRankQuant (rpAxor M) _ _ (fun i hi => ?_)
    have h1 := ceU_hit M x fit (.inl i) hi
    have h2 := ceV_hit M y fit (.inl i) hi
    have h3 := ceT_hit M z fit (.inl i) hi
    simp only [ceRank,ceChoose,Sum.elim_inl] at h1 h2 h3
    change (co (ctrlAffine (ceL w M) x) _ + co (ctrlAffine (ceM w M) y) _ =
      co ((mat (ceE w M)).mulVec z) _) ↔ _
    rw [h1,h2,h3]
    rfl
  · refine swRankQuant (rpAdg M) _ _ (fun i hi => ?_)
    have h1 := ceU_hit M x fit (.inr (.inl i)) hi
    have h2 := ceV_hit M y fit (.inr (.inl i)) hi
    have h3 := ceT_hit M z fit (.inr (.inl i)) hi
    simp only [ceRank,ceChoose,Sum.elim_inr,Sum.elim_inl] at h1 h2 h3
    dsimp only [q, U, Vv, Z]
    rw [h1,h2,h3]
    rfl
  · refine swRankQuant (rpAxz M) _ _ (fun i hi => ?_)
    have h1 := ceU_hit M x fit (.inr (.inr (.inl i))) hi
    have h3 := ceT_hit M z fit (.inr (.inr (.inl i))) hi
    simp only [ceRank,ceChoose,Sum.elim_inr,Sum.elim_inl] at h1 h3
    dsimp only [q, d, U, Z]
    rw [h1,h3]
    rfl
  · refine swRankQuant (rpAxy M) _ _ (fun i hi => ?_)
    have h1 := ceU_hit M x fit (.inr (.inr (.inr (.inl i)))) hi
    have h2 := ceV_hit M y fit (.inr (.inr (.inr (.inl i)))) hi
    simp only [ceRank,ceChoose,Sum.elim_inr,Sum.elim_inl,swCntFalse,Nat.add_zero] at h1 h2
    dsimp only [q, d, e, U, Vv]
    rw [h1,h2]
    rfl
  · refine (and_iff_left ⟨tu,tv,tz⟩).trans (swRankQuant (rpAyz M) _ _ (fun i hi => ?_))
    have h2 := ceV_hit M y fit (.inr (.inr (.inr (.inr i)))) hi
    have h3 := ceT_hit M z fit (.inr (.inr (.inr (.inr i)))) hi
    simp only [ceRank,ceChoose,Sum.elim_inr,swCntFalse,Nat.add_zero] at h2 h3
    dsimp only [q, d, e, k, Vv, Z]
    rw [h2,h3]
    rfl

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

def cePoint {a b c : ℕ} (x : V a) (y : V b) (z : V c) : rpCol a b c → ZMod 2 :=
  Sum.elim x (Sum.elim y (Sum.elim z (fun _ => 1)))

theorem ceEval {a b c : ℕ} (x : V a) (y : V b) (z : V c) (r : rpCol a b c → Bool) :
    rpEv (cePoint x y z) r =
      swVal r rpX x + swVal r rpY y + swVal r rpZ z + swRhs r := by
  simp only [rpEv,cePoint,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Fintype.sum_unique,mul_one,swVal,swRhs,rpX,rpY,rpZ,rpR,add_assoc]

theorem ceZero {a b c n : ℕ} (r : rpCol a b c → Bool) (e : Fin n → rpCol a b c) (x : V n)
    (hr : ∀ j, r (e j) = false) : swVal r e x = 0 := by simp [swVal,hr,rpBit]

theorem ceInactive {a b c : ℕ} (x : V a) (y : V b) (z : V c) (r : rpCol a b c → Bool)
    (hr : ∀ q, r q = false) : rpEv (cePoint x y z) r = 0 := by simp [rpEv,hr,rpBit]

theorem ceZ2_4 (u v s l : ZMod 2) :
    u + v + s + l = 0 ↔ (u + l) + v = s := by revert u v s l; decide

theorem ceZ2_3 (u v l : ZMod 2) :
    u + v + l = 0 ↔ u + l = v := by revert u v l; decide

theorem ceZ2_2 (u l : ZMod 2) : u + l = 0 ↔ u = l := by revert u l; decide

section
variable {a b c m : ℕ} (M : Fin m × rpCol a b c → Bool) (hF : rpFacts M)
variable (x : V a) (y : V b) (z : V c)

theorem ceXOR_eq (k : Fin c) :
    let R := ceRow (rpXOR M) k
    rpEv (cePoint x y z) R = 0 ↔
      (swVal R rpX x + swRhs R) + swVal R rpY y = swVal R rpZ z := by
  dsimp only
  rw [ceEval,ceZ2_4]

include hF

theorem ceUX_eq (k : Fin c) :
    let R := ceRow (rpUfix M) k
    rpEv (cePoint x y z) R = 0 ↔ swVal R rpX x + swRhs R = swVal R rpZ z := by
  have h := ceZero (ceRow (rpUfix M) k) rpY y (hF.ux_y k)
  dsimp only
  rw [ceEval,h,add_zero,ceZ2_3]

theorem ceDY_eq (k : Fin c) (hk : rpAdg M k = true) :
    let R := ceRow (rpDY M) k
    rpEv (cePoint x y z) R = 0 ↔ swVal R rpY y + swRhs R = swVal (ceRow (rpUfix M) k) rpZ z := by
  have h := ceZero (ceRow (rpDY M) k) rpX x (hF.dy_x k)
  have hz : swVal (ceRow (rpDY M) k) rpZ z = swVal (ceRow (rpUfix M) k) rpZ z := by
    simp only [swVal,ceRow, hF.dg_z k _ hk]
  dsimp only
  rw [ceEval,h,zero_add,hz,ceZ2_3]

theorem ceXY_eq (j : Fin b) :
    let R := ceRow (rpXY M) j
    rpEv (cePoint x y z) R = 0 ↔ swVal R rpX x + swRhs R = swVal R rpY y := by
  have h := ceZero (ceRow (rpXY M) j) rpZ z (hF.xy_z j)
  dsimp only
  rw [ceEval,h,add_zero,ceZ2_3]

theorem ceYZ_eq (k : Fin c) :
    let R := ceRow (rpYZ M) k
    rpEv (cePoint x y z) R = 0 ↔ swVal R rpY y + swRhs R = swVal R rpZ z := by
  have h := ceZero (ceRow (rpYZ M) k) rpX x (hF.yz_x k)
  dsimp only
  rw [ceEval,h,zero_add,ceZ2_3]

theorem cePX_eq :
    (∀ i, rpEv (cePoint x y z) (ceRow (rpPX M) i) = 0) ↔ ctrlSat (ceRX M) x = true := by
  simp only [ctrlSat,decide_eq_true_eq,ceRX,ceColA,ceSel_last,ceSel_cast]
  apply forall_congr'
  intro i
  have hy := ceZero (ceRow (rpPX M) i) rpY y (hF.px_y i)
  have hz := ceZero (ceRow (rpPX M) i) rpZ z (hF.px_z i)
  rw [ceEval,hy,hz,add_zero,add_zero,ceZ2_2]
  rfl

theorem cePY_eq :
    (∀ i, rpEv (cePoint x y z) (ceRow (rpPY M) i) = 0) ↔ ctrlSat (ceRY M) y = true := by
  simp only [ctrlSat,decide_eq_true_eq,ceRY,ceColB,ceSel_last,ceSel_cast]
  apply forall_congr'
  intro i
  have hx := ceZero (ceRow (rpPY M) i) rpX x (hF.py_x i)
  have hz := ceZero (ceRow (rpPY M) i) rpZ z (hF.py_z i)
  rw [ceEval,hx,hz,zero_add,add_zero,ceZ2_2]
  rfl

theorem ceCZ_eq :
    (∀ i, rpEv (cePoint x y z) (ceRow (rpCN M) i) = 0) ↔ ctrlSat (ceRZ M) z = true := by
  simp only [ctrlSat,decide_eq_true_eq,ceRZ,ceColC,ceSel_last,ceSel_cast]
  apply forall_congr'
  intro i
  have hx := ceZero (ceRow (rpCN M) i) rpX x (hF.cn_x i)
  have hy := ceZero (ceRow (rpCN M) i) rpY y (hF.cn_y i)
  rw [ceEval,hx,hy,zero_add,zero_add,ceZ2_2]
  rfl

theorem ceFacts_iff :
    (∀ i, rpEv (cePoint x y z) (ceRow M i) = 0) ↔
      ctrlSat (ceRX M) x = true ∧ ctrlSat (ceRY M) y = true ∧ ctrlSat (ceRZ M) z = true ∧
      swSlotEqs M x y z := by
  rw [show (∀ i, rpEv (cePoint x y z) (ceRow M i) = 0) ↔ _ from hF.sat (cePoint x y z)]
  rw [← cePX_eq M hF x y z, ← cePY_eq M hF x y z, ← ceCZ_eq M hF x y z]
  constructor
  · rintro ⟨qo,io,uo,do_,lo,px,py,cz⟩
    refine ⟨px,py,cz,fun k _ => (ceXOR_eq M x y z k).mp (qo k), ?_, ?_, ?_, ?_⟩
    · exact fun k hk => ⟨(ceUX_eq M hF x y z k).mp (uo k), (ceDY_eq M hF x y z k hk).mp (do_ k)⟩
    · exact fun k _ => (ceUX_eq M hF x y z k).mp (uo k)
    · exact fun j _ => (ceXY_eq M hF x y z j).mp (io j)
    · exact fun l _ => (ceYZ_eq M hF x y z l).mp (lo l)
  · rintro ⟨px,py,cz,qo,do_,ko,io,lo⟩
    refine ⟨fun k => ?_, fun j => ?_, fun k => ?_, fun k => ?_, fun l => ?_, px,py,cz⟩
    · cases hf : rpAxor M k with
      | false => exact ceInactive x y z _ (fun q => hF.xor_off k q hf)
      | true => exact (ceXOR_eq M x y z k).mpr (qo k hf)
    · cases hf : rpAxy M j with
      | false => exact ceInactive x y z _ (fun q => hF.xy_off j q hf)
      | true => exact (ceXY_eq M hF x y z j).mpr (io j hf)
    · cases hf : rpAdg M k with
      | true => exact (ceUX_eq M hF x y z k).mpr (do_ k hf).1
      | false =>
        cases hg : rpAxz M k with
        | true => exact (ceUX_eq M hF x y z k).mpr (ko k hg)
        | false => exact ceInactive x y z _ (fun q => hF.ux_off k q hf hg)
    · cases hf : rpAdg M k with
      | true => exact (ceDY_eq M hF x y z k hf).mpr (do_ k hf).2
      | false => exact ceInactive x y z _ (fun q => hF.dy_off k q hf)
    · cases hf : rpAyz M l with
      | true => exact (ceYZ_eq M hF x y z l).mpr (lo l hf)
      | false => exact ceInactive x y z _ (fun q => hF.yz_off l q hf)
end

theorem ceInpRow {a b c m t : ℕ} (H : Fin m → V a × V b × V c)
    (rhs : Fin m → ZMod 2) (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t))
    (x : V a) (y : V b) (z : V c) (i : Fin m) :
    let M := ceM0 a b c m t (inpOf H rhs f g)
    rpEv (cePoint x y z) (ceRow M i) = 0 ↔
      (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i := by
  let M := ceM0 a b c m t (inpOf H rhs f g)
  have hbit : ∀ u : ZMod 2, rpBit (decide (u ≠ 0)) = u := by decide
  have hx (j : Fin a) : rpBit (M (i,rpX j)) = (H i).1 j := by
    change rpBit (if h : j.val < a+b+c then decide (join3 (H i) ⟨_,h⟩ ≠ 0) else _) = _
    rw [dif_pos (by omega),hbit]
    exact ft_join_nx _ j
  have hy (j : Fin b) : rpBit (M (i,rpY j)) = (H i).2.1 j := by
    change rpBit (if h : a+j.val < a+b+c then decide (join3 (H i) ⟨_,h⟩ ≠ 0) else _) = _
    rw [dif_pos (by omega),hbit]
    exact ft_join_ny _ j
  have hz (j : Fin c) : rpBit (M (i,rpZ j)) = (H i).2.2 j := by
    change rpBit (if h : a+b+j.val < a+b+c then decide (join3 (H i) ⟨_,h⟩ ≠ 0) else _) = _
    rw [dif_pos (by omega),hbit]
    exact ft_join_nz _ j
  have hr : rpBit (M (i,rpR)) = rhs i := by
    change rpBit (if h : a+b+c < a+b+c then decide (join3 (H i) ⟨_,h⟩ ≠ 0) else decide (rhs i ≠ 0)) = _
    rw [dif_neg (lt_irrefl _),hbit]
  dsimp only
  rw [ceEval]
  change swVal (ceRow M i) rpX x + swVal (ceRow M i) rpY y + swVal (ceRow M i) rpZ z +
    swRhs (ceRow M i) = 0 ↔ _
  rw [ceZ2_2]
  simp only [swVal,swRhs,ceRow,hx,hy,hz,hr,dotProduct]

theorem ce_iff {a b c m t : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t))
    (hF : rpFacts (ceM0 a b c m t (inpOf H rhs f g))) (x : V a) (y : V b) (z : V c) :
    let M := ceM0 a b c m t (inpOf H rhs f g)
    let w := wOf a b c
    (∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i) ↔
      ctrlSat (ceRX M) x = true ∧ ctrlSat (ceRY M) y = true ∧ ctrlSat (ceRZ M) z = true ∧
      Std w (ceDims M 0) (ceDims M 1) (ceDims M 2) (ceDims M 3) (ceDims M 4)
        (ctrlAffine (ceL w M) x) (ctrlAffine (ceM w M) y) ((mat (ceE w M)).mulVec z) := by
  let M := ceM0 a b c m t (inpOf H rhs f g)
  have hfit : fitsW (wOf a b c) (ceDims M) :=
    ce_fits hF (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
  dsimp only
  rw [swSlotsIff M x y z hfit]
  exact (forall_congr' fun i => (ceInpRow H rhs f g x y z i).symm).trans (ceFacts_iff M hF x y z)

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

theorem ctrl_gjE {I : Type} {D : ℕ} (e : I ≃ Fin D) :
    Cmp (I × I) (I × I) (gjCost D)
      (fun v p => gj D (fun j => v (e.symm j.1,e.symm j.2)) (e p.1,e p.2)) :=
  ctrl_rewire (Cmp.sel (fun j => (e.symm j.1,e.symm j.2)) (cmp_gj D))
    (fun p : I × I => (e p.1,e p.2))

theorem ctrl_parts_cost (a b c m t : ℕ) :
    let P := a+b+c+m+t+4
    let w := wOf a b c
    let W := WOf a b c t
    7*(2^40*P^18*Phi w) + ctrlPushExtra w a W + ctrlPushExtra w b W ≤
      2^50*P^20*Phi w := by
  let P := a+b+c+m+t+4
  let w := wOf a b c
  let W := WOf a b c t
  have ha : a ≤ w := le_max_left _ _
  have hb : b ≤ w := le_trans (le_max_left _ _) (le_max_right _ _)
  have hP : 1 ≤ P := by dsimp [P]; omega
  have hw : w+2 ≤ P := by dsimp [w,wOf,P]; omega
  have hW : W+1 ≤ 4*P := by dsimp [W,WOf,wOf,P]; omega
  have e {n : ℕ} (hn : n ≤ 20) : P^n ≤ P^20 := Nat.pow_le_pow_right hP hn
  have ex (k : ℕ) (hk : k ≤ w) : ctrlPushExtra w k W ≤ 2^18 * (P^20*Phi w) := calc
    _ ≤ 2^18*P^5*2^w := ctrl_push_extra hk hw hW
    _ ≤ 2^18*P^20*Phi w :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (e (show 5 ≤ 20 by decide))) (two_pow_le_Phi _)
    _ = _ := Nat.mul_assoc _ _ _
  have hmain : 2^40 * P^18 * Phi w ≤ 2^40 * (P^20 * Phi w) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (e (show 18 ≤ 20 by decide)))
  change 7*(2^40*P^18*Phi w) + ctrlPushExtra w a W + ctrlPushExtra w b W ≤ 2^50*P^20*Phi w
  rw [Nat.mul_assoc (2^50)]
  exact le_trans (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hmain) (ex a ha)) (ex b hb))
    ((show ∀ n : ℕ, 7*(2^40*n) + 2^18*n + 2^18*n ≤ 2^50*n from fun n => by omega) _)

theorem ccOption {I J : Type} (s : J → Option I) :
    Cmp I J 1 (fun v j => (s j).elim false v) := by
  let f (j : J) : I ⊕ Unit := (s j).elim (.inr ()) Sum.inl
  refine (ctrl_rewire (Cmp.keep (Cb.const (ι := I) false)) f).congr ?_
  intro v j
  cases h : s j <;> simp [f,h]

theorem ccCorr {I A B J : Type} [Fintype J] {c S T : ℕ}
    {F : (I → Bool) → A → Bool} {G : (I → Bool) → B → Bool}
    (hf : Cmp I A S F) (hg : Cmp I B T G)
    (base : J → A) (left : J → Fin c → A) (right : J → Fin c → B) :
    Cmp I J (S+T + Fintype.card J*(c*5+5))
      (fun v j => xor (F v (base j)) (rpPar fun k => F v (left j k) && G v (right j k))) := by
  have hp (j : J) : Cb (A ⊕ B) (c*5+1)
      (fun v => rpPar fun k => v (.inl (left j k)) && v (.inr (right j k))) := by
    simpa only [rpPar, Fintype.card_fin] using
      Cb.bigXor (ι := A ⊕ B) (I := Fin c) (s := 1)
        (φ := fun k v => v (.inl (left j k)) && v (.inr (right j k)))
        (fun k => Cb.and (Cb.var _) (Cb.var _))
  have h := Cmp.ofBits (s := c*5+5) (F := fun (v : A ⊕ B → Bool) (j : J) =>
    xor (v (.inl (base j))) (rpPar fun k => v (.inl (left j k)) && v (.inr (right j k))))
    (fun j => (Cb.xor (Cb.var _) (hp j)).mono (by omega))
  exact ((hf.pair hg).comp h).congr fun _ _ => rfl

def ccP (a b c m : ℕ) := a+b+c+m+4
def ccB (a b c m : ℕ) := 1024*(ccP a b c m)^4

theorem ccPos (a b c m : ℕ) : 1 ≤ ccB a b c m := by
  unfold ccB ccP
  change 0 < _
  positivity

theorem ccGjLe {n a b c m : ℕ} (h : n+1 ≤ 2*ccP a b c m) :
    gjCost n ≤ ccB a b c m := by
  unfold gjCost ccB
  calc
    _ ≤ 32*(2*ccP a b c m)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = 512*(ccP a b c m)^4 := by rw [mul_pow]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

theorem ccGlueLe {a b c m n k l : ℕ} (hn : n ≤ 2*ccP a b c m)
    (hk : k ≤ 2*ccP a b c m) (hl : l ≤ 12*ccP a b c m) :
    n*k*l ≤ ccB a b c m := by
  let P := ccP a b c m
  have hp : 1 ≤ P := by dsimp [P,ccP]; omega
  calc
    _ ≤ (2*P)*(2*P)*(12*P) := Nat.mul_le_mul (Nat.mul_le_mul hn hk) hl
    _ = 48 * P^3 := by ring
    _ ≤ 1024*P^4 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right hp (by decide))

theorem ccOnly {a b c : ℕ} : Cmp _ _ 1 (@rpOnlyX a b c) := by
  let f : rpCol a b c × rpCol a b c → Option (rpCol a b c × rpCol a b c)
    | (.inl i,q) => some (.inl i,q)
    | _ => none
  apply (ccOption f).congr
  rintro v ⟨i|s,j⟩ <;> rfl

theorem ccG1 (a b c m : ℕ) : Cmp _ _ (2*ccB a b c m) (@rpG1 a b c m) := by
  let f : (rpCol a b c ⊕ Fin m) × (rpCol a b c ⊕ Fin m) → Option (Fin m × rpCol a b c)
    | (.inr i,.inl q) => some (i,q)
    | _ => none
  have h1 : Cmp _ _ 1 (@rpIn1 a b c m) := by
    apply (ccOption f).congr
    rintro v ⟨i|s,j|t⟩ <;> rfl
  have h := ctrl_rewire (h1.comp (ctrl_gjE (rpOrd _ (rp_rk1_inj a b c m))))
    (fun p : rpCol a b c × rpCol a b c => (Sum.inl p.1, Sum.inl p.2))
  apply h.mono
  have hgc := ccGjLe (a := a) (b := b) (c := c) (m := m)
    (n := Fintype.card (rpCol a b c ⊕ Fin m)) (by simp [rpCol,ccP]; omega)
  have := ccPos a b c m
  omega

theorem ccG2 (a b c m : ℕ) : Cmp _ _ (4*ccB a b c m) (@rpG2 a b c m) := by
  apply (((ccG1 a b c m).comp ccOnly).comp (ctrl_gjE (rpOrd _ (rp_rk2_inj a b c)))).mono
  have hgc := ccGjLe (a := a) (b := b) (c := c) (m := m)
    (n := Fintype.card (rpCol a b c)) (by simp [rpCol,ccP]; omega)
  have := ccPos a b c m
  omega

theorem ccG3 (a b c m : ℕ) : Cmp _ _ (6*ccB a b c m) (@rpG3 a b c m) := by
  apply (((ccG2 a b c m).comp ccOnly).comp (ctrl_gjE (rpOrd _ (rp_rk3_inj a b c)))).mono
  have hgc := ccGjLe (a := a) (b := b) (c := c) (m := m)
    (n := Fintype.card (rpCol a b c)) (by simp [rpCol,ccP]; omega)
  have := ccPos a b c m
  omega

theorem ccDec (a b c m : ℕ) : Cmp _ (Fin b × Fin c) (9*ccB a b c m)
    (fun (v : Fin m × rpCol a b c → Bool) p => rpDec (rpG3 v) (fun q => rpG1 v (rpY p.1,q)) p.2) := by
  have h := ccCorr (ccG1 a b c m) (ccG3 a b c m)
    (fun p : Fin b × Fin c => (rpY p.1, rpZ p.2))
    (fun p k => (rpY p.1, rpZ k)) (fun p k => (rpZ k, rpZ p.2))
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  apply h.mono
  have hl := ccGlueLe (a := a) (b := b) (c := c) (m := m) (n := b) (k := c) (l := c*5+5)
    (by unfold ccP; omega) (by unfold ccP; omega) (by unfold ccP; omega)
  omega

theorem ccG4 (a b c m : ℕ) : Cmp _ _ (14*ccB a b c m) (@rpG4 a b c m) := by
  let C := rpCol a b c
  let A := Fin c ⊕ C
  let sel : A × A → Option ((Fin b × Fin c) ⊕ (C × C))
    | (.inr (.inr (.inl j)), .inl l) => some (.inl (j,l))
    | (.inr (.inr (.inl j)), .inr q) => some (.inr (rpY j,q))
    | _ => none
  have hi : Cmp _ _ (9*ccB a b c m + 2*ccB a b c m + 1) (@rpIn4 a b c m) := by
    apply ((((ccDec a b c m).pair (ccG1 a b c m)).comp (ccOption sel))).congr
    rintro v ⟨(l|x|y|z|u),l'|q⟩ <;> rfl
  apply (hi.comp (ctrl_gjE (rpOrd _ (rp_rk4_inj a b c)))).mono
  have hgc := ccGjLe (a := a) (b := b) (c := c) (m := m)
    (n := Fintype.card (Fin c ⊕ rpCol a b c)) (by simp [rpCol,ccP]; omega)
  have := ccPos a b c m
  omega

theorem ccGlueCol {a b c m n : ℕ} (hn : n ≤ ccP a b c m) :
    Fintype.card (Fin n × rpCol a b c) * (c*5+5) ≤ ccB a b c m := by
  rw [Fintype.card_prod,Fintype.card_fin]
  apply ccGlueLe
  · omega
  · simp [rpCol,ccP]; omega
  · unfold ccP; omega

theorem ccYt (a b c m : ℕ) : Cmp _ _ (21*ccB a b c m) (@rpYt a b c m) := by
  have h := ccCorr (ccG4 a b c m) (ccG3 a b c m)
    (fun p : Fin c × rpCol a b c => (Sum.inl p.1, Sum.inr p.2))
    (fun p k => (Sum.inl p.1, rpPz k)) (fun p k => (rpZ k, p.2))
  apply h.mono
  have hgl := ccGlueCol (a := a) (b := b) (c := c) (m := m) (n := c) (by unfold ccP; omega)
  omega

theorem ccClr1 (a b c m : ℕ) : Cmp _ _ (11*ccB a b c m) (@rpClr1 a b c m) := by
  have h := ccCorr (ccG2 a b c m) (ccG3 a b c m)
    (fun p : Fin b × rpCol a b c => (rpY p.1, p.2))
    (fun p k => (rpY p.1, rpZ k)) (fun p k => (rpZ k, p.2))
  apply h.mono
  have hgl := ccGlueCol (a := a) (b := b) (c := c) (m := m) (n := b) (by unfold ccP; omega)
  omega

theorem ccClr2 (a b c m : ℕ) : Cmp _ _ (33*ccB a b c m) (@rpClr2 a b c m) := by
  have h := ccCorr (ccClr1 a b c m) (ccYt a b c m)
    (fun p : Fin b × rpCol a b c => p)
    (fun p k => (p.1, rpZ k)) (fun p k => (k, p.2))
  apply h.mono
  have hgl := ccGlueCol (a := a) (b := b) (c := c) (m := m) (n := b) (by unfold ccP; omega)
  omega

theorem ccG5 (a b c m : ℕ) : Cmp _ _ (35*ccB a b c m) (@rpG5 a b c m) := by
  let C := rpCol a b c
  let sel : C × C → Option (Fin b × C)
    | (.inr (.inl j),q) => some (j,q)
    | _ => none
  have hi : Cmp _ _ (33*ccB a b c m + 1) (@rpIn5 a b c m) := by
    apply ((ccClr2 a b c m).comp (ccOption sel)).congr
    rintro v ⟨(x|y|z|u),q⟩ <;> rfl
  apply (hi.comp (ctrl_gjE (rpOrd _ (rp_rk5_inj a b c)))).mono
  have hgc := ccGjLe (a := a) (b := b) (c := c) (m := m)
    (n := Fintype.card (rpCol a b c)) (by simp [rpCol,ccP]; omega)
  have := ccPos a b c m
  omega

theorem ccUfix (a b c m : ℕ) : Cmp _ _ (21*ccB a b c m) (@rpUfix a b c m) := by
  let C := rpCol a b c
  let A := Fin c ⊕ C
  let I := (A × A) ⊕ (C × C)
  let g (v : I → Bool) (p : Fin c × C) :=
    if v (.inl (rpPz p.1, rpPz p.1)) then
      rpPar (fun k : Fin c => v (.inl (rpPz p.1, rpPz k)) && v (.inr (rpZ k,p.2)))
    else v (.inr (rpZ p.1,p.2))
  have hp (p : Fin c × C) : Cb I (c*5+1) (fun v =>
      rpPar (fun k : Fin c => v (.inl (rpPz p.1, rpPz k)) && v (.inr (rpZ k,p.2)))) := by
    simpa only [rpPar,Fintype.card_fin] using Cb.bigXor (ι := I) (I := Fin c) (s := 1)
      (φ := fun k v => v (.inl (rpPz p.1,rpPz k)) && v (.inr (rpZ k,p.2)))
      (fun k => Cb.and (Cb.var _) (Cb.var _))
  have bit (p : Fin c × C) : Cb I (c*5+5) (fun v => g v p) :=
    (Cb.mux (Cb.var _) (hp p) (Cb.var _)).mono (by omega)
  have h := ((ccG4 a b c m).pair (ccG3 a b c m)).comp (Cmp.ofBits (F := g) bit)
  apply h.mono
  have hgl := ccGlueCol (a := a) (b := b) (c := c) (m := m) (n := c) (by unfold ccP; omega)
  change 14*ccB a b c m + 6*ccB a b c m + Fintype.card (Fin c × rpCol a b c)*(c*5+5) ≤ _
  omega

theorem ccRaw_le (a b c m t k : ℕ) (hk : k ≤ 35) :
    k*ccB a b c m ≤ 2^20*(a+b+c+m+t+4)^6 := by
  let P := a+b+c+m+t+4
  have hp : 1 ≤ P := by dsimp [P]; omega
  have hn : ccP a b c m ≤ P := by dsimp [ccP,P]; omega
  calc
    _ ≤ 35*(1024*P^4) := Nat.mul_le_mul hk (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _))
    _ = (35*1024)*P^4 := (Nat.mul_assoc _ _ _).symm
    _ ≤ 2^20*P^6 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right hp (by decide))

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

def swPartSize (a b c m t : Nat) := 2^40 * (a+b+c+m+t+4)^18 * Phi (wOf a b c)

theorem swCtlSpec {a b c m t : Nat} (ea : Fin (2^a) ≃ V a) (eb : Fin (2^b) ≃ V b)
    {D : (In0 a b c m t → Bool) → Fin 5 → Nat}
    {L : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin (a+1) → Bool}
    {M : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin (b+1) → Bool}
    {E : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin c → Bool}
    {X : (In0 a b c m t → Bool) → V a → Bool}
    {Y : (In0 a b c m t → Bool) → V b → Bool}
    {Z : (In0 a b c m t → Bool) → V c → Bool}
    (hD : Cmp _ (Fin 5 × Fin (wOf a b c+1)) (swPartSize a b c m t)
      (fun v p => decide (D v p.1 = p.2.val)))
    (hL : Cmp _ _ (swPartSize a b c m t) L) (hM : Cmp _ _ (swPartSize a b c m t) M)
    (hE : Cmp _ _ (swPartSize a b c m t) E) (hX : Cmp _ _ (swPartSize a b c m t) X)
    (hY : Cmp _ _ (swPartSize a b c m t) Y) (hZ : Cmp _ _ (swPartSize a b c m t) Z)
    (hfit : ∀ (H : Fin m → V a × V b × V c) (r : Fin m → ZMod 2)
      (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t)),
      fitsW (wOf a b c) (D (inpOf H r f g)))
    (hsat : ∀ (H : Fin m → V a × V b × V c) (r : Fin m → ZMod 2)
      (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t))
      (x : V a) (y : V b) (z : V c),
      let u := inpOf H r f g
      (∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = r i) ↔
      X u x = true ∧ Y u y = true ∧ Z u z = true ∧
      Std (wOf a b c) (D u 0) (D u 1) (D u 2) (D u 3) (D u 4)
        (ctrlAffine (L u) x) (ctrlAffine (M u) y) ((mat (E u)).mulVec z)) :
    CtlSpec a b c m t ea eb := by
  let W := WOf a b c t
  refine ⟨_, D, _, _, E, Z, ctrl_parts_cost a b c m t,
    ctrl_bundle (W := W) ea eb hD hL hM hE hX hY hZ, ?_⟩
  intro H r f g
  refine ⟨hfit H r f g, fun z => ?_⟩
  exact ctrl_total ea eb H r f g z _ _ _ _ _ _ (fun x y => hsat H r f g x y z)

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

abbrev swIn (a b c m : Nat) := Fin m × rpCol a b c

structure SwStages (a b c m S : Nat) : Prop where
  g1 : Cmp (swIn a b c m) _ S rpG1
  g2 : Cmp (swIn a b c m) _ S rpG2
  g3 : Cmp (swIn a b c m) _ S rpG3
  g4 : Cmp (swIn a b c m) _ S rpG4
  g5 : Cmp (swIn a b c m) _ S rpG5
  uf : Cmp (swIn a b c m) _ S rpUfix

def SwBits {ι κ : Type} (S : Nat) (f : (ι → Bool) → κ → Bool) : Prop :=
  ∀ k, Cb ι S (fun v => f v k)

theorem swOfCmp {ι κ : Type} {f : (ι → Bool) → κ → Bool} {S T : Nat}
    (h : Cmp ι κ S f) (hS : S ≤ T) : SwBits T f :=
  fun k => (ctrl_entry h k).mono hS

theorem swOfBits {ι κ : Type} [Fintype κ] {f : (ι → Bool) → κ → Bool} {S : Nat}
    (h : SwBits S f) : Cmp ι κ (Fintype.card κ*S) f := Cmp.ofBits h

theorem swAppendBits {m n S : Nat} {ι : Type}
    {f : (ι → Bool) → Fin m → Bool} {g : (ι → Bool) → Fin n → Bool}
    (hf : SwBits S f) (hg : SwBits S g) : SwBits S (fun v => Fin.append (f v) (g v)) := by
  intro i
  induction i using Fin.addCases with
  | left k => simpa only [Fin.append_left] using hf k
  | right k => simpa only [Fin.append_right] using hg k

theorem swCatBits {m n S : Nat} {ι : Type} {f0 f1 f2 f4 : (ι → Bool) → Fin n → Bool}
    {f3 : (ι → Bool) → Fin m → Bool}
    (h0 : SwBits S f0) (h1 : SwBits S f1) (h2 : SwBits S f2) (h3 : SwBits S f3)
    (h4 : SwBits S f4) : SwBits S (fun v => ceCat (f0 v) (f1 v) (f2 v) (f3 v) (f4 v)) :=
  swAppendBits (swAppendBits (swAppendBits (swAppendBits h0 h1) h2) h3) h4

theorem swFalseBits {ι κ : Type} {S : Nat} (hs : 1 ≤ S) :
    SwBits S (fun (_ : ι → Bool) (_ : κ) => false) := fun _ => (Cb.const _).mono hs

structure SwRows (a b c m T : Nat) : Prop where
  f0 : SwBits T (@rpAxor a b c m)
  f1 : SwBits T (@rpAdg a b c m)
  f2 : SwBits T (@rpAxz a b c m)
  f3 : SwBits T (@rpAxy a b c m)
  f4 : SwBits T (@rpAyz a b c m)
  r0 : SwBits T (@rpXOR a b c m)
  r1 : SwBits T (@rpUfix a b c m)
  r2 : SwBits T (@rpDY a b c m)
  r3 : SwBits T (@rpXY a b c m)
  r4 : SwBits T (@rpYZ a b c m)
  rx : SwBits T (@ceRX a b c m)
  ry : SwBits T (@ceRY a b c m)
  rz : SwBits T (@ceRZ a b c m)

theorem swRows {a b c m S : Nat} (h : SwStages a b c m S) : SwRows a b c m (2*S+2) := by
  have le : S ≤ 2*S+2 := by omega
  have h1 := swOfCmp h.g1 le
  have h2 := swOfCmp h.g2 le
  have h3 := swOfCmp h.g3 le
  have h4 := swOfCmp h.g4 le
  have h5 := swOfCmp h.g5 le
  refine ⟨fun k => h5 _, fun k => h4 _, ?_, fun k => h5 _, fun k => h4 _, fun p => h5 _,
    swOfCmp h.uf le, fun p => h4 _, fun p => h5 _, fun p => h4 _, ?_, fun p => h4 _, ?_⟩
  · intro k
    exact ((ctrl_entry h.g3 (rpZ k,rpZ k)).and (ctrl_entry h.g4 (rpPz k,rpPz k)).not).mono (by omega)
  · rintro ⟨i|i,j⟩
    · exact h3 _
    · exact h5 _
  · rintro ⟨(i|i|i|i|i),j⟩
    · exact h1 _
    · exact h2 _
    · exact h3 _
    · exact h4 _
    · exact h5 _

structure SwPackedBits (a b c m T : Nat) : Prop where
  fu : SwBits T (@ceFlU a b c m)
  fv : SwBits T (@ceFlV a b c m)
  ft : SwBits T (@ceFlT a b c m)
  pu : SwBits T (@cePayU a b c m)
  pv : SwBits T (@cePayV a b c m)
  pt : SwBits T (@cePayT a b c m)

theorem swPackedBits {a b c m T : Nat} (h : SwRows a b c m T) (ht : 1 ≤ T) :
    SwPackedBits a b c m T := by
  refine ⟨swCatBits h.f0 h.f1 h.f2 h.f3 (swFalseBits ht),
    swCatBits h.f0 h.f1 (swFalseBits ht) h.f3 h.f4,
    swCatBits h.f0 h.f1 h.f2 (swFalseBits ht) h.f4, ?_, ?_, ?_⟩
  · rintro ⟨i,j⟩
    exact swCatBits (fun k => h.r0 (k,ceColA j)) (fun k => h.r1 (k,ceColA j))
      (fun k => h.r1 (k,ceColA j)) (fun k => h.r3 (k,ceColA j)) (swFalseBits ht) i
  · rintro ⟨i,j⟩
    let H {n : Nat} (F : (swIn a b c m → Bool) → Fin n × rpCol a b c → Bool) (hF : SwBits T F) :
        SwBits T (fun v (k : Fin n) => ceSel false (fun l => F v (k,rpY l)) j) := by
      intro k
      by_cases he : j.val < b
      · simpa only [ceSel, dif_pos he] using hF (k,rpY ⟨j.val,he⟩)
      · simpa only [ceSel, dif_neg he] using (Cb.const (ι := swIn a b c m) false).mono ht
    exact swCatBits (H _ h.r0) (fun k => h.r2 (k,ceColB j)) (swFalseBits ht)
      (H _ h.r3) (fun k => h.r4 (k,ceColB j)) i
  · rintro ⟨i,j⟩
    exact swCatBits (fun k => h.r0 (k,rpZ j)) (fun k => h.r1 (k,rpZ j))
      (fun k => h.r1 (k,rpZ j)) (swFalseBits ht) (fun k => h.r4 (k,rpZ j)) i

theorem swPhiPos (w : Nat) : 0 < Phi w := (Nat.two_pow_pos w).trans_le (two_pow_le_Phi w)

theorem swDimCost {P w T : Nat} (hp : 1 ≤ P) (hw : w ≤ P) (ht : T ≤ 2^22*P^6) :
    5*(w+1)*(P*T+(P+1)*((w+1)*6)) ≤ 2^40*P^18*Phi w := by
  have h8 : P^8 ≤ P^18 := Nat.pow_le_pow_right hp (by decide)
  have h3 : P^3 ≤ P^18 := Nat.pow_le_pow_right hp (by decide)
  have h2p : w+1 ≤ 2*P := by omega
  have h2p' : P+1 ≤ 2*P := by omega
  calc
    _ ≤ 5*(2*P)*(P*(2^22*P^6)+(2*P)*((2*P)*6)) := by gcongr
    _ ≤ 2^40*P^18 := by ring_nf; omega
    _ ≤ _ := Nat.le_mul_of_pos_right _ (swPhiPos w)

theorem swMtrxCost {P w T n j : Nat} (hp : 1 ≤ P) (hw : w ≤ P)
    (hn : n ≤ 5*P) (hj : j ≤ 2*P) (ht : T ≤ 2^22*P^6) :
    n*T+(n+1)*((w+1)*6)+(n*j)*T+(w*j)*(n*3+1) ≤ 2^40*P^18*Phi w := by
  have h8 : P^8 ≤ P^18 := Nat.pow_le_pow_right hp (by decide)
  have h7 : P^7 ≤ P^18 := Nat.pow_le_pow_right hp (by decide)
  have h3 : P^3 ≤ P^18 := Nat.pow_le_pow_right hp (by decide)
  have h2 : P^2 ≤ P^18 := Nat.pow_le_pow_right hp (by decide)
  have hw1 : w+1 ≤ 2*P := by omega
  have hn1 : n+1 ≤ 6*P := by omega
  have hn3 : n*3+1 ≤ 16*P := by omega
  calc
    _ ≤ (5*P)*(2^22*P^6)+(6*P)*((2*P)*6)+((5*P)*(2*P))*(2^22*P^6)+
        (P*(2*P))*(16*P) := by gcongr
    _ ≤ 2^40*P^18 := by ring_nf; omega
    _ ≤ _ := Nat.le_mul_of_pos_right _ (swPhiPos w)

theorem swPinCost {P w T n k : Nat} (hp : 1 ≤ P) (hw : w ≤ P)
    (hn : n ≤ 5*P) (hk : k ≤ w) (ht : T ≤ 2^22*P^6) :
    (n*(k+1))*T+2^k*(n*(k*6+7)+1) ≤ 2^40*P^18*Phi w := by
  have h8 : P^8 ≤ P^18 := Nat.pow_le_pow_right hp (by decide)
  have h2 : P^2 ≤ P^18 := Nat.pow_le_pow_right hp (by decide)
  have h0 : 1 ≤ P^18 := Nat.pow_pos hp
  have hw1 : k+1 ≤ 2*P := by omega
  have hw2 : k*6+7 ≤ 13*P := by omega
  have hz : 2^k ≤ Phi w := (Nat.pow_le_pow_right (by decide) hk).trans (two_pow_le_Phi w)
  have hs : (n*(k+1))*T+(n*(k*6+7)+1) ≤ 2^40*P^18 := calc
    _ ≤ ((5*P)*(2*P))*(2^22*P^6)+((5*P)*(13*P)+1) := by gcongr
    _ ≤ _ := by ring_nf; omega
  calc
    _ ≤ ((n*(k+1))*T)*Phi w + Phi w*(n*(k*6+7)+1) :=
      Nat.add_le_add (Nat.le_mul_of_pos_right _ (swPhiPos w)) (Nat.mul_le_mul_right _ hz)
    _ = ((n*(k+1))*T+(n*(k*6+7)+1))*Phi w := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hs

theorem swDims {a b c m T P w : Nat} (h : SwRows a b c m T) (hp : 1 ≤ P)
    (hw : w ≤ P) (hb : b ≤ P) (hc : c ≤ P) (ht : T ≤ 2^22*P^6) :
    Cmp (swIn a b c m) (Fin 5 × Fin (w+1)) (2^40*P^18*Phi w)
      (fun v p => decide (ceDims v p.1 = p.2.val)) := by
  have ct {n : Nat} (hn : n ≤ P) {f : (swIn a b c m → Bool) → Fin n → Bool}
      (hf : SwBits T f) (j : Fin (w+1)) :
      Cb _ (P*T+(P+1)*((w+1)*6)) (fun v => decide (cnt (f v) n = j.val)) := by
    have hh := ctrl_cnt_test (swOfBits hf) (Fin.last n) j.val
    simp only [Fintype.card_fin, Fin.val_last] at hh
    exact hh.mono (Nat.add_le_add (by gcongr)
      (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))))
  refine Cmp.mono (Cmp.ofBits (s := P*T+(P+1)*((w+1)*6)) ?_) ?_
  · rintro ⟨i,j⟩
    fin_cases i
    · exact ct hc h.f0 j
    · exact ct hc h.f1 j
    · exact ct hb h.f3 j
    · exact ct hc h.f2 j
    · exact ct hc h.f4 j
  · simpa only [Fintype.card_prod, Fintype.card_fin] using swDimCost hp hw ht

theorem swPackCtrl {ι J : Type} [Fintype J] {P T n w : Nat} (hp : 1 ≤ P) (hw : w ≤ P)
    (hn : n ≤ 5*P) (hj : Fintype.card J ≤ 2*P) (ht : T ≤ 2^22*P^6)
    {fl : (ι → Bool) → Fin n → Bool} {dat : (ι → Bool) → Fin n × J → Bool}
    (hf : SwBits T fl) (hd : SwBits T dat) :
    Cmp ι (Fin w × J) (2^40*P^18*Phi w) (fun v => ctrlPacked w (fl v) (dat v)) := by
  refine (ctrl_pack (swOfBits hf) (swOfBits hd)).mono ?_
  simpa only [Fintype.card_fin, Fintype.card_prod] using swMtrxCost hp hw hn hj ht

theorem swPinCtrl {ι J : Type} [Fintype J] {P T k w : Nat} (hp : 1 ≤ P) (hw : w ≤ P)
    (hj : Fintype.card J ≤ 5*P) (hk : k ≤ w) (ht : T ≤ 2^22*P^6)
    {R : (ι → Bool) → J × Fin (k+1) → Bool} (hr : SwBits T R) :
    Cmp ι (V k) (2^40*P^18*Phi w) (fun v => ctrlSat (R v)) := by
  refine (ctrl_pin (swOfBits hr)).mono ?_
  simpa only [Fintype.card_fin, Fintype.card_prod] using swPinCost hp hw hj hk ht

def SwCertFacts (a b c m t : Nat) : Prop :=
  ∀ (H : Fin m → V a × V b × V c) (r : Fin m → ZMod 2)
    (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t)),
    let M0 := ceM0 a b c m t (inpOf H r f g)
    let w := wOf a b c
    let D := ceDims M0
    fitsW w D ∧ ∀ (x : V a) (y : V b) (z : V c),
      (∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = r i) ↔
      ctrlSat (ceRX M0) x = true ∧ ctrlSat (ceRY M0) y = true ∧ ctrlSat (ceRZ M0) z = true ∧
      Std w (D 0) (D 1) (D 2) (D 3) (D 4)
        (ctrlAffine (ceL w M0) x) (ctrlAffine (ceM w M0) y) ((mat (ceE w M0)).mulVec z)

theorem swCtlFromFacts {a b c m t : Nat} (ea : Fin (2^a) ≃ V a) (eb : Fin (2^b) ≃ V b)
    (cert : SwCertFacts a b c m t) : CtlSpec a b c m t ea eb := by
  let P := a+b+c+m+t+4
  let S := 2^20*P^6
  let T := 2*S+2
  let w := wOf a b c
  have st : SwStages a b c m S := ⟨(ccG1 a b c m).mono (ccRaw_le _ _ _ _ t _ (by decide)),
    (ccG2 a b c m).mono (ccRaw_le _ _ _ _ t _ (by decide)),
    (ccG3 a b c m).mono (ccRaw_le _ _ _ _ t _ (by decide)),
    (ccG4 a b c m).mono (ccRaw_le _ _ _ _ t _ (by decide)),
    (ccG5 a b c m).mono (ccRaw_le _ _ _ _ t _ (by decide)),
    (ccUfix a b c m).mono (ccRaw_le _ _ _ _ t _ (by decide))⟩
  have rows := swRows st
  have dat := swPackedBits rows (by omega)
  have hp : 1 ≤ P := by dsimp [P]; omega
  have hw : w ≤ P := by dsimp [w,wOf,P]; omega
  have ha : a ≤ w := by dsimp [w,wOf]; omega
  have hb : b ≤ w := by dsimp [w,wOf]; omega
  have hc : c ≤ w := by dsimp [w,wOf]; omega
  have ht : T ≤ 2^22*P^6 := by have h := Nat.pow_pos hp (n := 6); dsimp [T,S]; omega
  have hn : c+c+c+b+c ≤ 5*P := by omega
  let i0 (p : swIn a b c m) : In0 a b c m t := Sum.inl (p.1,ceIdx p.2)
  have mS : ∀ {κ : Type} {F : (swIn a b c m → Bool) → κ → Bool},
      Cmp _ _ (2^40*P^18*Phi w) F →
      Cmp (In0 a b c m t) _ (swPartSize a b c m t) (fun v => F (ceM0 a b c m t v)) :=
    fun h => Cmp.sel i0 h
  refine swCtlSpec ea eb (D := fun v => ceDims (ceM0 a b c m t v))
    (L := fun v => ceL w (ceM0 a b c m t v)) (M := fun v => ceM w (ceM0 a b c m t v))
    (E := fun v => ceE w (ceM0 a b c m t v))
    (X := fun v => ctrlSat (ceRX (ceM0 a b c m t v)))
    (Y := fun v => ctrlSat (ceRY (ceM0 a b c m t v)))
    (Z := fun v => ctrlSat (ceRZ (ceM0 a b c m t v)))
    (mS (swDims rows hp hw (by omega) (by omega) ht)) ?_ ?_ ?_ ?_ ?_ ?_
    (fun H r f g => (cert H r f g).1) (fun H r f g => (cert H r f g).2)
  · exact mS (swPackCtrl hp hw hn (by simp; omega) ht dat.fu dat.pu)
  · exact mS (swPackCtrl hp hw hn (by simp; omega) ht dat.fv dat.pv)
  · exact mS (swPackCtrl hp hw hn (by simp; omega) ht dat.ft dat.pt)
  · exact mS (swPinCtrl hp hw (by simp; omega) ha ht rows.rx)
  · exact mS (swPinCtrl hp hw (by simp; omega) hb ht rows.ry)
  · exact mS (swPinCtrl hp hw (by simp [rpCNI]; omega) hc ht rows.rz)

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

theorem rp_bit_false : rpBit false = 0 := rfl

theorem rp_bit_true : rpBit true = 1 := rfl

theorem rp_bit_xor (x y : Bool) : rpBit (xor x y) = rpBit x + rpBit y := by
  cases x <;> cases y <;> decide

theorem rp_bit_and (x y : Bool) : rpBit (x && y) = rpBit x * rpBit y := by
  cases x <;> cases y <;> decide

theorem rp_bit_inj (x y : Bool) (h : rpBit x = rpBit y) : x = y := by
  revert h; cases x <;> cases y <;> decide

theorem rp_bit_eq_zero (x : Bool) : rpBit x = 0 ↔ x = false := by
  cases x <;> decide

theorem rp_bit_decide_eq {I : Type} [DecidableEq I] (i j : I) :
    rpBit (decide (i = j)) = if i = j then 1 else 0 := by
  by_cases h : i = j <;> simp [rpBit, h]

theorem rp_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

theorem rp_add_eq_zero (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  revert x y; decide

theorem rp_bit_par {I : Type} [Fintype I] (p : I → Bool) :
    rpBit (rpPar p) = ∑ i, rpBit (p i) := by
  have h1 : (∑ i, rpBit (p i)) =
      ((Finset.univ.filter (fun i => p i = true)).card : ZMod 2) := by
    simp only [rpBit]
    rw [Finset.sum_boole]
  rw [h1, ← ZMod.natCast_mod, rpPar, rpBit]
  rcases Nat.mod_two_eq_zero_or_one (Finset.univ.filter (fun i => p i = true)).card with h | h <;>
    simp [h]

theorem rp_par_false {I : Type} [Fintype I] : rpPar (fun _ : I => false) = false := by
  simp [rpPar]

theorem rp_ev_false {κ : Type} [Fintype κ] (w : κ → ZMod 2) :
    rpEv w (fun _ => false) = 0 := by
  simp [rpEv, rpBit]

theorem rp_ev_zero {κ : Type} [Fintype κ] (w : κ → ZMod 2) (r : κ → Bool)
    (h : ∀ q, r q = false) : rpEv w r = 0 := by
  have : r = fun _ => false := funext h
  rw [this, rp_ev_false]

theorem rp_ev_xor {κ : Type} [Fintype κ] (w : κ → ZMod 2) (r s : κ → Bool) :
    rpEv w (fun q => xor (r q) (s q)) = rpEv w r + rpEv w s := by
  simp only [rpEv, rp_bit_xor, add_mul, Finset.sum_add_distrib]

theorem rp_ev_par {κ I : Type} [Fintype κ] [Fintype I] (w : κ → ZMod 2) (cf : I → Bool)
    (R : I × κ → Bool) :
    rpEv w (fun q => rpPar (fun k => cf k && R (k, q))) =
      ∑ k, rpBit (cf k) * rpEv w (fun q => R (k, q)) := by
  simp only [rpEv, rp_bit_par, rp_bit_and, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun q _ => ?_))
  ring

theorem rp_ev_inl {α β : Type} [Fintype α] [Fintype β] (w : α → ZMod 2) (r : α ⊕ β → Bool) :
    rpEv (Sum.elim w (fun _ => 0)) r = rpEv w (fun q => r (Sum.inl q)) := by
  simp [rpEv, Fintype.sum_sum_type]

theorem rp_ev_inr {α β : Type} [Fintype α] [Fintype β] (w : β → ZMod 2) (r : α ⊕ β → Bool) :
    rpEv (Sum.elim (fun _ => 0) w) r = rpEv w (fun q => r (Sum.inr q)) := by
  simp [rpEv, Fintype.sum_sum_type]

theorem rp_ev_single {κ : Type} [Fintype κ] [DecidableEq κ] (j : κ) (r : κ → Bool) :
    rpEv (fun q => if q = j then 1 else 0) r = rpBit (r j) := by
  simp [rpEv]

theorem rp_mulVec_iff {ι : Type} [Fintype ι] {D : ℕ} (e : ι ≃ Fin D)
    (N : Fin D × Fin D → Bool) (w : ι → ZMod 2) :
    (mat N).mulVec (fun j => w (e.symm j)) = 0 ↔
      ∀ i : ι, rpEv w (fun q => N (e i, e q)) = 0 := by
  have key : ∀ i : ι, (mat N).mulVec (fun j => w (e.symm j)) (e i) =
      rpEv w (fun q => N (e i, e q)) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, mat, rpEv, rpBit]
    rw [← Equiv.sum_comp e]
    simp
  constructor
  · intro h i
    rw [← key, h]
    rfl
  · intro h
    funext i'
    have := h (e.symm i')
    rw [← key, Equiv.apply_symm_apply] at this
    exact this

theorem rp_gj_sat {ι : Type} [Fintype ι] {D : ℕ} (e : ι ≃ Fin D) (M : ι × ι → Bool)
    (w : ι → ZMod 2) :
    (∀ i, rpEv w (fun q => rpGj e M (i, q)) = 0) ↔ (∀ i, rpEv w (fun q => M (i, q)) = 0) := by
  have h1 := rp_mulVec_iff e (gj D (fun q => M (e.symm q.1, e.symm q.2))) w
  have h2 := rp_mulVec_iff e (fun q => M (e.symm q.1, e.symm q.2)) w
  simp only [Equiv.symm_apply_apply] at h2
  obtain ⟨U, U', hu, hu'⟩ := gj_equiv (fun q : Fin D × Fin D => M (e.symm q.1, e.symm q.2))
  have h3 : (mat (gj D (fun q => M (e.symm q.1, e.symm q.2)))).mulVec (fun j => w (e.symm j)) = 0 ↔
      (mat (fun q : Fin D × Fin D => M (e.symm q.1, e.symm q.2))).mulVec
        (fun j => w (e.symm j)) = 0 := by
    constructor
    · intro h
      rw [hu', ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    · intro h
      rw [hu, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  exact h1.symm.trans (h3.trans h2)

theorem rp_gj_pivcol {ι : Type} [DecidableEq ι] {D : ℕ} (e : ι ≃ Fin D) (M : ι × ι → Bool)
    (p : ι) (hp : rpGj e M (p, p) = true) (i : ι) : rpGj e M (i, p) = decide (i = p) := by
  have h := gj_pivcol (fun q => M (e.symm q.1, e.symm q.2)) (e p) hp (e i)
  show gj D _ (e i, e p) = _
  rw [h]
  simp

theorem rp_gj_zerorow {ι : Type} {D : ℕ} (e : ι ≃ Fin D) (M : ι × ι → Bool)
    (q : ι) (hq : rpGj e M (q, q) = false) (j : ι) : rpGj e M (q, j) = false :=
  gj_zerorow (fun q => M (e.symm q.1, e.symm q.2)) (e q) hq (e j)

theorem rp_gj_upper {ι : Type} {D : ℕ} (e : ι ≃ Fin D) (M : ι × ι → Bool)
    (p q : ι) (h : e q < e p) : rpGj e M (p, q) = false :=
  gj_upper (fun q => M (e.symm q.1, e.symm q.2)) (e p) (e q) h

theorem rp_gj_zcol {ι : Type} {D : ℕ} (e : ι ≃ Fin D) (M : ι × ι → Bool)
    (j : ι) (h : ∀ i, M (i, j) = false) (i : ι) : rpGj e M (i, j) = false :=
  gj_zcol (fun q => M (e.symm q.1, e.symm q.2)) (e j)
    (fun i' => by simpa using h (e.symm i')) (e i)

theorem rp_gj_card {ι : Type} [Fintype ι] [DecidableEq ι] {D : ℕ} (e : ι ≃ Fin D)
    (M : ι × ι → Bool) (S : Finset ι) (hS : ∀ i, i ∉ S → ∀ j, M (i, j) = false) :
    (Finset.univ.filter (fun p : ι => rpGj e M (p, p) = true)).card ≤ S.card := by
  have h := gj_rank (fun q : Fin D × Fin D => M (e.symm q.1, e.symm q.2))
  have h1 : (Finset.univ.filter (fun p : ι => rpGj e M (p, p) = true)).card ≤
      (Finset.univ.filter (fun p : Fin D =>
        gj D (fun q => M (e.symm q.1, e.symm q.2)) (p, p) = true)).card := by
    apply Finset.card_le_card_of_injOn (fun p => e p)
    · intro p hp
      have hp' : rpGj e M (p, p) = true := by simpa using hp
      have hp2 : gj D (fun q => M (e.symm q.1, e.symm q.2)) (e p, e p) = true := hp'
      simpa using hp2
    · intro p _ p' _ hpp
      exact e.injective hpp
  have h2 : (Finset.univ.filter (fun i : Fin D =>
      ∃ j, M (e.symm i, e.symm j) = true)).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun i => e.symm i)
    · intro i hi
      have hi' : ∃ j, M (e.symm i, e.symm j) = true := by simpa using hi
      obtain ⟨j, hj⟩ := hi'
      by_contra hc
      have := hS (e.symm i) hc (e.symm j)
      rw [this] at hj
      exact Bool.false_ne_true hj
    · intro i _ i' _ hii
      exact e.symm.injective hii
  exact h1.trans (h.trans h2)

section stages

variable {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool)

theorem rp_card_col (P : rpCol a b c → Bool) :
    (Finset.univ.filter (fun p => P p = true)).card =
      (Finset.univ.filter (fun i : Fin a => P (rpX i) = true)).card +
      ((Finset.univ.filter (fun j : Fin b => P (rpY j) = true)).card +
      ((Finset.univ.filter (fun k : Fin c => P (rpZ k) = true)).card +
      (if P rpR = true then 1 else 0))) := by
  simp only [Finset.card_filter, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton]

theorem rp_onlyx_sat (R : rpCol a b c × rpCol a b c → Bool) (w : rpCol a b c → ZMod 2) :
    (∀ p, rpEv w (fun q => rpOnlyX R (p, q)) = 0) ↔
      (∀ i : Fin a, rpEv w (fun q => R (rpX i, q)) = 0) := by
  constructor
  · intro h i
    exact h (rpX i)
  · intro h p
    rcases p with i | p
    · exact h i
    · exact rp_ev_zero _ _ (fun q => rfl)

theorem rp_onlyx_card {D : ℕ} (e : rpCol a b c ≃ Fin D) (R : rpCol a b c × rpCol a b c → Bool)
    (hz : ∀ i : Fin a, R (rpX i, rpX i) = false → ∀ q, R (rpX i, q) = false) :
    (Finset.univ.filter (fun p => rpGj e (rpOnlyX R) (p, p) = true)).card ≤
      (Finset.univ.filter (fun i : Fin a => R (rpX i, rpX i) = true)).card := by
  have h := rp_gj_card e (rpOnlyX R)
    ((Finset.univ.filter (fun i : Fin a => R (rpX i, rpX i) = true)).map
      ⟨Sum.inl, Sum.inl_injective⟩) (by
      intro p hp q
      rcases p with i | p
      · apply hz i
        by_contra hc
        apply hp
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        exact ⟨i, by simpa using hc, rfl⟩
      · rfl)
  rwa [Finset.card_map] at h

theorem rp_g1_upper (p q : rpCol a b c)
    (h : rpRk1 a b c m (Sum.inl q) < rpRk1 a b c m (Sum.inl p)) : rpG1 M0 (p, q) = false :=
  rp_gj_upper _ _ _ _ ((rp_ord_lt _ _ _ _).2 h)

theorem rp_g1_pivcol (p : rpCol a b c) (hp : rpG1 M0 (p, p) = true) (i : rpCol a b c) :
    rpG1 M0 (i, p) = decide (i = p) := by
  have h := rp_gj_pivcol (rpOrd (rpRk1 a b c m) (rp_rk1_inj a b c m)) (rpIn1 M0)
    (Sum.inl p) hp (Sum.inl i)
  show rpGj _ _ (Sum.inl i, Sum.inl p) = _
  rw [h]
  simp

theorem rp_g1_zerorow (p : rpCol a b c) (hp : rpG1 M0 (p, p) = false) (q : rpCol a b c) :
    rpG1 M0 (p, q) = false :=
  rp_gj_zerorow _ _ (Sum.inl p) hp (Sum.inl q)

theorem rp_g1_extra (i : Fin m) (j : rpCol a b c ⊕ Fin m) :
    rpGj (rpOrd (rpRk1 a b c m) (rp_rk1_inj a b c m)) (rpIn1 M0) (Sum.inr i, j) = false := by
  apply rp_gj_zerorow
  apply rp_gj_zcol
  intro p
  rcases p with p | i' <;> rfl

theorem rp_g1_sat (w : rpCol a b c → ZMod 2) :
    (∀ p, rpEv w (fun q => rpG1 M0 (p, q)) = 0) ↔ (∀ i, rpEv w (fun q => M0 (i, q)) = 0) := by
  have h := rp_gj_sat (rpOrd (rpRk1 a b c m) (rp_rk1_inj a b c m)) (rpIn1 M0)
    (Sum.elim w (fun _ => 0))
  simp only [rp_ev_inl] at h
  constructor
  · intro hp
    have h1 := h.1 (fun i => by
      rcases i with p | i
      · exact hp p
      · exact rp_ev_zero _ _ (fun q => rp_g1_extra M0 i _))
    exact fun i => h1 (Sum.inr i)
  · intro hi
    have h1 := h.2 (fun i => by
      rcases i with p | i
      · exact rp_ev_zero _ _ (fun q => rfl)
      · exact hi i)
    exact fun p => h1 (Sum.inl p)

theorem rp_g1_yx (j : Fin b) (i : Fin a) : rpG1 M0 (rpY j, rpX i) = false :=
  rp_g1_upper M0 _ _ (by simp only [rpRk1]; omega)

theorem rp_g1_tx (s : Fin c ⊕ Unit) (i : Fin a) :
    rpG1 M0 (Sum.inr (Sum.inr s), rpX i) = false := by
  rcases s with k | u <;> exact rp_g1_upper M0 _ _ (by simp only [rpRk1]; omega)

theorem rp_g1_ty (s : Fin c ⊕ Unit) (j : Fin b) :
    rpG1 M0 (Sum.inr (Sum.inr s), rpY j) = false := by
  rcases s with k | u <;> exact rp_g1_upper M0 _ _ (by simp only [rpRk1]; omega)

theorem rp_g2_upper (p q : rpCol a b c) (h : rpRk2 a b c q < rpRk2 a b c p) :
    rpG2 M0 (p, q) = false :=
  rp_gj_upper _ _ _ _ ((rp_ord_lt _ _ _ _).2 h)

theorem rp_g2_sat (w : rpCol a b c → ZMod 2) :
    (∀ p, rpEv w (fun q => rpG2 M0 (p, q)) = 0) ↔
      (∀ i : Fin a, rpEv w (fun q => rpG1 M0 (rpX i, q)) = 0) :=
  (rp_gj_sat _ _ w).trans (rp_onlyx_sat _ w)

theorem rp_g2_xy (i : Fin a) (j : Fin b) : rpG2 M0 (rpX i, rpY j) = false :=
  rp_g2_upper M0 _ _ (by simp only [rpRk2]; omega)

theorem rp_g2_tx (s : Fin c ⊕ Unit) (i : Fin a) :
    rpG2 M0 (Sum.inr (Sum.inr s), rpX i) = false := by
  rcases s with k | u <;> exact rp_g2_upper M0 _ _ (by simp only [rpRk2]; omega)

theorem rp_g2_ty (s : Fin c ⊕ Unit) (j : Fin b) :
    rpG2 M0 (Sum.inr (Sum.inr s), rpY j) = false := by
  rcases s with k | u <;> exact rp_g2_upper M0 _ _ (by simp only [rpRk2]; omega)

theorem rp_g2_zerorow (p : rpCol a b c) (hp : rpG2 M0 (p, p) = false) (q : rpCol a b c) :
    rpG2 M0 (p, q) = false :=
  rp_gj_zerorow _ _ p hp q

theorem rp_g2_disj (j : Fin b) (h : rpG1 M0 (rpY j, rpY j) = true) :
    rpG2 M0 (rpY j, rpY j) = false := by
  apply rp_gj_zcol
  intro p
  rcases p with i | p
  · show rpG1 M0 (rpX i, rpY j) = false
    rw [rp_g1_pivcol M0 _ h]
    simp
  · rfl

theorem rp_g2_card :
    (Finset.univ.filter (fun i : Fin a => rpG2 M0 (rpX i, rpX i) = true)).card +
      (Finset.univ.filter (fun j : Fin b => rpG2 M0 (rpY j, rpY j) = true)).card ≤ a := by
  have h := rp_onlyx_card (rpOrd (rpRk2 a b c) (rp_rk2_inj a b c)) (rpG1 M0)
    (fun i hi q => rp_g1_zerorow M0 _ hi q)
  have h2 := rp_card_col (fun p : rpCol a b c => rpG2 M0 (p, p))
  have h3 : (Finset.univ.filter (fun i : Fin a => rpG1 M0 (rpX i, rpX i) = true)).card ≤ a := by
    calc _ ≤ (Finset.univ : Finset (Fin a)).card := Finset.card_filter_le _ _
      _ = a := by simp
  have h4 : (Finset.univ.filter (fun p : rpCol a b c => rpG2 M0 (p, p) = true)).card ≤ a :=
    h.trans h3
  omega

theorem rp_card_sum {α β : Type} [Fintype α] [Fintype β] (P : α ⊕ β → Bool) :
    (Finset.univ.filter (fun p => P p = true)).card =
      (Finset.univ.filter (fun x : α => P (Sum.inl x) = true)).card +
      (Finset.univ.filter (fun y : β => P (Sum.inr y) = true)).card := by
  simp only [Finset.card_filter, Fintype.sum_sum_type]

theorem rp_g3_upper (p q : rpCol a b c) (h : rpRk3 a b c q < rpRk3 a b c p) :
    rpG3 M0 (p, q) = false :=
  rp_gj_upper _ _ _ _ ((rp_ord_lt _ _ _ _).2 h)

theorem rp_g3_sat (w : rpCol a b c → ZMod 2) :
    (∀ p, rpEv w (fun q => rpG3 M0 (p, q)) = 0) ↔
      (∀ i : Fin a, rpEv w (fun q => rpG2 M0 (rpX i, q)) = 0) :=
  (rp_gj_sat _ _ w).trans (rp_onlyx_sat _ w)

theorem rp_g3_zerorow (p : rpCol a b c) (hp : rpG3 M0 (p, p) = false) (q : rpCol a b c) :
    rpG3 M0 (p, q) = false :=
  rp_gj_zerorow _ _ p hp q

theorem rp_g3_pivcol (p : rpCol a b c) (hp : rpG3 M0 (p, p) = true) (i : rpCol a b c) :
    rpG3 M0 (i, p) = decide (i = p) :=
  rp_gj_pivcol _ _ p hp i

theorem rp_g3_y (p : rpCol a b c) (j : Fin b) : rpG3 M0 (p, rpY j) = false := by
  apply rp_gj_zcol
  intro p'
  rcases p' with i | p'
  · exact rp_g2_xy M0 i j
  · rfl

theorem rp_g3_yrow (j : Fin b) (q : rpCol a b c) : rpG3 M0 (rpY j, q) = false :=
  rp_g3_zerorow M0 _ (rp_g3_y M0 _ j) q

theorem rp_g3_xz (i : Fin a) (k : Fin c) : rpG3 M0 (rpX i, rpZ k) = false :=
  rp_g3_upper M0 _ _ (by simp only [rpRk3]; omega)

theorem rp_g3_rz (k : Fin c) : rpG3 M0 (rpR, rpZ k) = false :=
  rp_g3_upper M0 _ _ (by simp only [rpRk3]; omega)

theorem rp_g3_rx (i : Fin a) : rpG3 M0 (rpR, rpX i) = false :=
  rp_g3_upper M0 _ _ (by simp only [rpRk3]; omega)

theorem rp_g3_card :
    (Finset.univ.filter (fun k : Fin c => rpG3 M0 (rpZ k, rpZ k) = true)).card ≤
      (Finset.univ.filter (fun i : Fin a => rpG2 M0 (rpX i, rpX i) = true)).card := by
  have h := rp_onlyx_card (rpOrd (rpRk3 a b c) (rp_rk3_inj a b c)) (rpG2 M0)
    (fun i hi q => rp_g2_zerorow M0 _ hi q)
  have h2 := rp_card_col (fun p : rpCol a b c => rpG3 M0 (p, p))
  have h4 : (Finset.univ.filter (fun p : rpCol a b c => rpG3 M0 (p, p) = true)).card ≤
      (Finset.univ.filter (fun i : Fin a => rpG2 M0 (rpX i, rpX i) = true)).card := h
  omega

theorem rp_dec_piv (r : rpCol a b c → Bool) (k : Fin c)
    (h : rpG3 M0 (rpZ k, rpZ k) = true) : rpDec (rpG3 M0) r k = false := by
  apply (rp_bit_eq_zero _).1
  have hk : ∀ k' : Fin c, rpBit (rpG3 M0 (rpZ k', rpZ k)) = if k' = k then 1 else 0 := by
    intro k'
    rw [rp_g3_pivcol M0 _ h]
    by_cases hkk : k' = k
    · subst hkk; simp [rpBit]
    · have : (rpZ k' : rpCol a b c) ≠ rpZ k := fun hh => hkk (by simpa using hh)
      simp [rpBit, this, hkk]
  simp only [rpDec, rp_bit_xor, rp_bit_par, rp_bit_and, hk, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact rp_add_self _

theorem rp_dec_zero (U : rpCol a b c × rpCol a b c → Bool) (r : rpCol a b c → Bool)
    (h : ∀ q, r q = false) (l : Fin c) : rpDec U r l = false := by
  simp [rpDec, h, rp_par_false]

theorem rp_g4_upper (p q : Fin c ⊕ rpCol a b c) (h : rpRk4 a b c q < rpRk4 a b c p) :
    rpG4 M0 (p, q) = false :=
  rp_gj_upper _ _ _ _ ((rp_ord_lt _ _ _ _).2 h)

theorem rp_g4_zerorow (p : Fin c ⊕ rpCol a b c) (hp : rpG4 M0 (p, p) = false)
    (q : Fin c ⊕ rpCol a b c) : rpG4 M0 (p, q) = false :=
  rp_gj_zerorow _ _ p hp q

theorem rp_g4_pivcol (p : Fin c ⊕ rpCol a b c) (hp : rpG4 M0 (p, p) = true)
    (i : Fin c ⊕ rpCol a b c) : rpG4 M0 (i, p) = decide (i = p) :=
  rp_gj_pivcol _ _ p hp i

theorem rp_g4_x (p : Fin c ⊕ rpCol a b c) (i : Fin a) :
    rpG4 M0 (p, Sum.inr (rpX i)) = false := by
  apply rp_gj_zcol
  intro p'
  rcases p' with l | (i' | j | k | u)
  · rfl
  · rfl
  · exact rp_g1_yx M0 j i
  · rfl
  · rfl

theorem rp_g4_xrow (i : Fin a) (q : Fin c ⊕ rpCol a b c) :
    rpG4 M0 (Sum.inr (rpX i), q) = false :=
  rp_g4_zerorow M0 _ (rp_g4_x M0 _ i) q

theorem rp_g4_decz (k : Fin c) (h : rpG3 M0 (rpZ k, rpZ k) = true)
    (p : Fin c ⊕ rpCol a b c) : rpG4 M0 (p, Sum.inl k) = false := by
  apply rp_gj_zcol
  intro p'
  rcases p' with l | (i' | j | k' | u)
  · rfl
  · rfl
  · show rpDec (rpG3 M0) (fun q => rpG1 M0 (rpY j, q)) k = false
    exact rp_dec_piv M0 (fun q => rpG1 M0 (rpY j, q)) k h
  · rfl
  · rfl

theorem rp_g4_sat (w : rpCol a b c → ZMod 2) :
    (∀ p, rpEv w (fun q => rpG4 M0 (p, Sum.inr q)) = 0) ↔
      (∀ j : Fin b, rpEv w (fun q => rpG1 M0 (rpY j, q)) = 0) := by
  have h := rp_gj_sat (rpOrd (rpRk4 a b c) (rp_rk4_inj a b c)) (rpIn4 M0)
    (Sum.elim (fun _ => 0) w)
  simp only [rp_ev_inr] at h
  refine h.trans ?_
  constructor
  · intro hp j
    exact hp (Sum.inr (rpY j))
  · intro hj p
    rcases p with l | (i' | j | k' | u)
    · exact rp_ev_zero _ _ (fun q => rfl)
    · exact rp_ev_zero _ _ (fun q => rfl)
    · exact hj j
    · exact rp_ev_zero _ _ (fun q => rfl)
    · exact rp_ev_zero _ _ (fun q => rfl)

theorem rp_lin_ev (l : Fin c) (r : Fin c ⊕ rpCol a b c → Bool) :
    rpEv (Sum.elim (fun l' : Fin c => if l' = l then (1 : ZMod 2) else 0)
      (Sum.elim (fun _ : Fin a => 0) (Sum.elim (fun _ : Fin b => 0)
        (Sum.elim (fun k : Fin c => (if k = l then (1 : ZMod 2) else 0) +
          rpBit (rpG3 M0 (rpZ k, rpZ l))) (fun _ : Unit => 0))))) r =
      rpBit (r (Sum.inl l)) + (rpBit (r (rpPz l)) +
        ∑ k : Fin c, rpBit (r (rpPz k)) * rpBit (rpG3 M0 (rpZ k, rpZ l))) := by
  simp only [rpEv, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
    Finset.sum_const_zero, mul_add, Finset.sum_add_distrib, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, add_zero, zero_add]

theorem rp_g4_lin (p : Fin c ⊕ rpCol a b c) (l : Fin c) :
    rpBit (rpG4 M0 (p, Sum.inl l)) = rpBit (rpG4 M0 (p, rpPz l)) +
      ∑ k : Fin c, rpBit (rpG4 M0 (p, rpPz k)) * rpBit (rpG3 M0 (rpZ k, rpZ l)) := by
  have h := rp_gj_sat (rpOrd (rpRk4 a b c) (rp_rk4_inj a b c)) (rpIn4 M0)
    (Sum.elim (fun l' : Fin c => if l' = l then (1 : ZMod 2) else 0)
      (Sum.elim (fun _ : Fin a => 0) (Sum.elim (fun _ : Fin b => 0)
        (Sum.elim (fun k : Fin c => (if k = l then (1 : ZMod 2) else 0) +
          rpBit (rpG3 M0 (rpZ k, rpZ l))) (fun _ : Unit => 0)))))
  simp only [rp_lin_ev] at h
  have h2 := h.2 (by
    intro p'
    rcases p' with l' | (i' | j | k' | u)
    · show rpBit false + (rpBit false + ∑ k : Fin c, rpBit false * _) = 0
      simp [rp_bit_false]
    · show rpBit false + (rpBit false + ∑ k : Fin c, rpBit false * _) = 0
      simp [rp_bit_false]
    · show rpBit (rpDec (rpG3 M0) (fun q => rpG1 M0 (rpY j, q)) l) +
        (rpBit (rpG1 M0 (rpY j, rpZ l)) +
          ∑ k : Fin c, rpBit (rpG1 M0 (rpY j, rpZ k)) * rpBit (rpG3 M0 (rpZ k, rpZ l))) = 0
      simp only [rpDec, rp_bit_xor, rp_bit_par, rp_bit_and]
      exact rp_add_self _
    · show rpBit false + (rpBit false + ∑ k : Fin c, rpBit false * _) = 0
      simp [rp_bit_false]
    · show rpBit false + (rpBit false + ∑ k : Fin c, rpBit false * _) = 0
      simp [rp_bit_false]) p
  exact (rp_add_eq_zero _ _).1 h2

end stages

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

section mid

variable {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool)

theorem rp_g4_yd (j : Fin b) (l : Fin c) : rpG4 M0 (Sum.inr (rpY j), Sum.inl l) = false :=
  rp_g4_upper M0 _ _ (by simp only [rpRk4, rpRk5]; omega)

theorem rp_g4_yz (j : Fin b) (k : Fin c) : rpG4 M0 (Sum.inr (rpY j), rpPz k) = false :=
  rp_g4_upper M0 _ _ (by simp only [rpRk4, rpRk5]; omega)

theorem rp_g4_zd (k l : Fin c) : rpG4 M0 (rpPz k, Sum.inl l) = false :=
  rp_g4_upper M0 _ _ (by simp only [rpRk4, rpRk5]; omega)

theorem rp_g4_zz (k k' : Fin c) (h : k' < k) : rpG4 M0 (rpPz k, rpPz k') = false :=
  rp_g4_upper M0 _ _ (by simp only [rpRk4, rpRk5]; omega)

theorem rp_g4_rd (l : Fin c) : rpG4 M0 (Sum.inr rpR, Sum.inl l) = false :=
  rp_g4_upper M0 _ _ (by simp only [rpRk4, rpRk5]; omega)

theorem rp_g4_rz (k : Fin c) : rpG4 M0 (Sum.inr rpR, rpPz k) = false :=
  rp_g4_upper M0 _ _ (by simp only [rpRk4, rpRk5]; omega)

theorem rp_g4_ry (j : Fin b) : rpG4 M0 (Sum.inr rpR, Sum.inr (rpY j)) = false :=
  rp_g4_upper M0 _ _ (by simp only [rpRk4, rpRk5]; omega)

theorem rp_g4_card :
    (Finset.univ.filter (fun l : Fin c => rpG4 M0 (Sum.inl l, Sum.inl l) = true)).card +
      (Finset.univ.filter (fun k : Fin c => rpG4 M0 (rpPz k, rpPz k) = true)).card ≤
      (Finset.univ.filter (fun j : Fin b => rpG1 M0 (rpY j, rpY j) = true)).card := by
  have h := rp_gj_card (rpOrd (rpRk4 a b c) (rp_rk4_inj a b c)) (rpIn4 M0)
    ((Finset.univ.filter (fun j : Fin b => rpG1 M0 (rpY j, rpY j) = true)).map
      ⟨fun j => (Sum.inr (rpY j) : Fin c ⊕ rpCol a b c), fun j j' hj => by simpa using hj⟩) (by
      intro p hp q
      rcases p with l | (i | j | k | u)
      · rfl
      · rfl
      · have hz : rpG1 M0 (rpY j, rpY j) = false := by
          by_contra hc
          apply hp
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, by simpa using hc, rfl⟩
        rcases q with l | q
        · show rpDec (rpG3 M0) (fun q => rpG1 M0 (rpY j, q)) l = false
          exact rp_dec_zero _ _ (fun q => rp_g1_zerorow M0 _ hz q) l
        · show rpG1 M0 (rpY j, q) = false
          exact rp_g1_zerorow M0 _ hz q
      · rfl
      · rfl)
  rw [Finset.card_map] at h
  have h2 := rp_card_sum (fun p : Fin c ⊕ rpCol a b c => rpG4 M0 (p, p))
  have h3 := rp_card_col (fun p : rpCol a b c => rpG4 M0 (Sum.inr p, Sum.inr p))
  have h4 : (Finset.univ.filter (fun p : Fin c ⊕ rpCol a b c => rpG4 M0 (p, p) = true)).card ≤
      (Finset.univ.filter (fun j : Fin b => rpG1 M0 (rpY j, rpY j) = true)).card := h
  have h5 : (Finset.univ.filter (fun k : Fin c => rpG4 M0 (rpPz k, rpPz k) = true)).card =
      (Finset.univ.filter (fun k : Fin c =>
        rpG4 M0 (Sum.inr (rpZ k), Sum.inr (rpZ k)) = true)).card := rfl
  omega

theorem rp_g4_active (k : Fin c) (h : rpG4 M0 (rpPz k, rpPz k) = true) :
    rpG3 M0 (rpZ k, rpZ k) = true := by
  by_contra hc
  have hc' : rpG3 M0 (rpZ k, rpZ k) = false := by simpa using hc
  have hl := rp_g4_lin M0 (rpPz k) k
  rw [rp_g4_zd, h] at hl
  have hs : ∑ k' : Fin c, rpBit (rpG4 M0 (rpPz k, rpPz k')) *
      rpBit (rpG3 M0 (rpZ k', rpZ k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k' _
    rcases lt_trichotomy k' k with hlt | heq | hgt
    · rw [rp_g4_zz M0 k k' hlt, rp_bit_false, zero_mul]
    · subst heq
      rw [hc', rp_bit_false, mul_zero]
    · rw [rp_g3_upper M0 (rpZ k') (rpZ k) (by simp only [rpRk3]; exact hgt), rp_bit_false,
        mul_zero]
  rw [hs] at hl
  exact absurd hl (by decide)

theorem rp_ufix_ev (w : rpCol a b c → ZMod 2) (k : Fin c) :
    rpEv w (fun q => rpUfix M0 (k, q)) =
      if rpG4 M0 (rpPz k, rpPz k) = true then
        ∑ k' : Fin c, rpBit (rpG4 M0 (rpPz k, rpPz k')) * rpEv w (fun q => rpG3 M0 (rpZ k', q))
      else rpEv w (fun q => rpG3 M0 (rpZ k, q)) := by
  by_cases h : rpG4 M0 (rpPz k, rpPz k) = true
  · simp only [rpUfix, h, ↓reduceIte]
    exact rp_ev_par w (fun k' => rpG4 M0 (rpPz k, rpPz k')) (fun p => rpG3 M0 (rpZ p.1, p.2))
  · simp only [rpUfix, h, Bool.false_eq_true, ↓reduceIte]

theorem rp_ufix_sat (w : rpCol a b c → ZMod 2) :
    (∀ k : Fin c, rpEv w (fun q => rpUfix M0 (k, q)) = 0) ↔
      (∀ k : Fin c, rpEv w (fun q => rpG3 M0 (rpZ k, q)) = 0) := by
  constructor
  · intro h k
    by_cases hk : rpG4 M0 (rpPz k, rpPz k) = true
    · have h1 := h k
      simp only [rp_ufix_ev, hk, ↓reduceIte] at h1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hk] at h1
      have hrest : ∑ k' ∈ Finset.univ.erase k, rpBit (rpG4 M0 (rpPz k, rpPz k')) *
          rpEv w (fun q => rpG3 M0 (rpZ k', q)) = 0 := by
        apply Finset.sum_eq_zero
        intro k' hk'
        have hne : k' ≠ k := Finset.ne_of_mem_erase hk'
        by_cases hd : rpG4 M0 (rpPz k', rpPz k') = true
        · rw [rp_g4_pivcol M0 _ hd]
          have : (rpPz k : Fin c ⊕ rpCol a b c) ≠ rpPz k' := fun hh => hne (by simpa using hh.symm)
          simp [this, rp_bit_false]
        · have h2 := h k'
          simp only [rp_ufix_ev, hd, Bool.false_eq_true, ↓reduceIte] at h2
          rw [h2, mul_zero]
      rw [hrest, add_zero, rp_bit_true, one_mul] at h1
      exact h1
    · have h1 := h k
      simp only [rp_ufix_ev, hk, Bool.false_eq_true, ↓reduceIte] at h1
      exact h1
  · intro h k
    rw [rp_ufix_ev]
    split_ifs
    · exact Finset.sum_eq_zero (fun k' _ => by rw [h k', mul_zero])
    · exact h k

theorem rp_ufix_z (k l : Fin c) (h : rpG4 M0 (rpPz k, rpPz k) = true) :
    rpUfix M0 (k, rpZ l) = rpG4 M0 (rpPz k, rpPz l) := by
  apply rp_bit_inj
  have hl := rp_g4_lin M0 (rpPz k) l
  rw [rp_g4_zd, rp_bit_false] at hl
  have hu : rpBit (rpUfix M0 (k, rpZ l)) = ∑ k' : Fin c,
      rpBit (rpG4 M0 (rpPz k, rpPz k')) * rpBit (rpG3 M0 (rpZ k', rpZ l)) := by
    simp only [rpUfix, h, ↓reduceIte, rp_bit_par, rp_bit_and]
  rw [hu]
  exact ((rp_add_eq_zero _ _).1 hl.symm).symm

theorem rp_ufix_y (k : Fin c) (j : Fin b) : rpUfix M0 (k, rpY j) = false := by
  simp only [rpUfix, rp_g3_y, Bool.and_false, rp_par_false, ite_self]

theorem rp_ufix_off (k : Fin c) (h : rpG3 M0 (rpZ k, rpZ k) = false) (q : rpCol a b c) :
    rpUfix M0 (k, q) = false := by
  have hd : ¬ rpG4 M0 (rpPz k, rpPz k) = true := by
    intro hd
    have := rp_g4_active M0 k hd
    rw [h] at this
    exact Bool.false_ne_true this
  simp only [rpUfix, hd, Bool.false_eq_true, ↓reduceIte]
  exact rp_g3_zerorow M0 _ h q

end mid

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

section s7

variable {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool)

theorem rp7_yt_ev (w : rpCol a b c → ZMod 2) (l : Fin c) :
    rpEv w (fun q => rpYt M0 (l, q)) = rpEv w (fun q => rpG4 M0 (Sum.inl l, Sum.inr q)) +
      ∑ k : Fin c, rpBit (rpG4 M0 (Sum.inl l, rpPz k)) * rpEv w (fun q => rpG3 M0 (rpZ k, q)) := by
  show rpEv w (fun q => xor (rpG4 M0 (Sum.inl l, Sum.inr q))
    (rpPar fun k : Fin c => rpG4 M0 (Sum.inl l, rpPz k) && rpG3 M0 (rpZ k, q))) = _
  rw [rp_ev_xor]
  congr 1
  exact rp_ev_par w (fun k : Fin c => rpG4 M0 (Sum.inl l, rpPz k))
    (fun p : Fin c × rpCol a b c => rpG3 M0 (rpZ p.1, p.2))

theorem rp7_yt_z (l l' : Fin c) : rpYt M0 (l, rpZ l') = rpG4 M0 (Sum.inl l, Sum.inl l') := by
  apply rp_bit_inj
  rw [rp_g4_lin M0 (Sum.inl l) l']
  show rpBit (xor (rpG4 M0 (Sum.inl l, rpPz l'))
    (rpPar fun k : Fin c => rpG4 M0 (Sum.inl l, rpPz k) && rpG3 M0 (rpZ k, rpZ l'))) = _
  simp only [rp_bit_xor, rp_bit_par, rp_bit_and]

theorem rp7_clr1_ev (w : rpCol a b c → ZMod 2) (j : Fin b) :
    rpEv w (fun q => rpClr1 M0 (j, q)) = rpEv w (fun q => rpG2 M0 (rpY j, q)) +
      ∑ k : Fin c, rpBit (rpG2 M0 (rpY j, rpZ k)) * rpEv w (fun q => rpG3 M0 (rpZ k, q)) := by
  show rpEv w (fun q => xor (rpG2 M0 (rpY j, q))
    (rpPar fun k : Fin c => rpG2 M0 (rpY j, rpZ k) && rpG3 M0 (rpZ k, q))) = _
  rw [rp_ev_xor]
  congr 1
  exact rp_ev_par w (fun k : Fin c => rpG2 M0 (rpY j, rpZ k))
    (fun p : Fin c × rpCol a b c => rpG3 M0 (rpZ p.1, p.2))

theorem rp7_clr2_ev (w : rpCol a b c → ZMod 2) (j : Fin b) :
    rpEv w (fun q => rpClr2 M0 (j, q)) = rpEv w (fun q => rpClr1 M0 (j, q)) +
      ∑ l : Fin c, rpBit (rpClr1 M0 (j, rpZ l)) * rpEv w (fun q => rpYt M0 (l, q)) := by
  show rpEv w (fun q => xor (rpClr1 M0 (j, q))
    (rpPar fun l : Fin c => rpClr1 M0 (j, rpZ l) && rpYt M0 (l, q))) = _
  rw [rp_ev_xor]
  congr 1
  exact rp_ev_par w (fun l : Fin c => rpClr1 M0 (j, rpZ l))
    (fun p : Fin c × rpCol a b c => rpYt M0 (p.1, p.2))

theorem rp7_clr1_piv (j : Fin b) (k : Fin c) (h : rpG3 M0 (rpZ k, rpZ k) = true) :
    rpClr1 M0 (j, rpZ k) = false := by
  apply (rp_bit_eq_zero _).1
  have hk : ∀ k' : Fin c, rpBit (rpG3 M0 (rpZ k', rpZ k)) = if k' = k then 1 else 0 := by
    intro k'
    rw [rp_g3_pivcol M0 _ h]
    by_cases hkk : k' = k
    · subst hkk; simp [rpBit]
    · have : (rpZ k' : rpCol a b c) ≠ rpZ k := fun hh => hkk (by simpa using hh)
      simp [rpBit, this, hkk]
  show rpBit (xor (rpG2 M0 (rpY j, rpZ k))
    (rpPar fun k' : Fin c => rpG2 M0 (rpY j, rpZ k') && rpG3 M0 (rpZ k', rpZ k))) = 0
  simp only [rp_bit_xor, rp_bit_par, rp_bit_and, hk, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact rp_add_self _

theorem rp7_clr2_z1 (j : Fin b) (k : Fin c) (h : rpG3 M0 (rpZ k, rpZ k) = true) :
    rpClr2 M0 (j, rpZ k) = false := by
  apply (rp_bit_eq_zero _).1
  show rpBit (xor (rpClr1 M0 (j, rpZ k))
    (rpPar fun l : Fin c => rpClr1 M0 (j, rpZ l) && rpYt M0 (l, rpZ k))) = 0
  simp only [rp_bit_xor, rp_bit_par, rp_bit_and, rp7_yt_z, rp_g4_decz M0 k h, rp_bit_false,
    mul_zero, Finset.sum_const_zero, add_zero, rp7_clr1_piv M0 j k h]

theorem rp7_clr2_z2 (j : Fin b) (l : Fin c) (h : rpG4 M0 (Sum.inl l, Sum.inl l) = true) :
    rpClr2 M0 (j, rpZ l) = false := by
  apply (rp_bit_eq_zero _).1
  have hl : ∀ l' : Fin c, rpBit (rpYt M0 (l', rpZ l)) = if l' = l then 1 else 0 := by
    intro l'
    rw [rp7_yt_z, rp_g4_pivcol M0 _ h]
    by_cases hll : l' = l
    · subst hll; simp [rpBit]
    · have : (Sum.inl l' : Fin c ⊕ rpCol a b c) ≠ Sum.inl l := fun hh => hll (by simpa using hh)
      simp [rpBit, this, hll]
  show rpBit (xor (rpClr1 M0 (j, rpZ l))
    (rpPar fun l' : Fin c => rpClr1 M0 (j, rpZ l') && rpYt M0 (l', rpZ l))) = 0
  simp only [rp_bit_xor, rp_bit_par, rp_bit_and, hl, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact rp_add_self _

theorem rp7_clr1_zero (j : Fin b) (h : rpG2 M0 (rpY j, rpY j) = false) (q : rpCol a b c) :
    rpClr1 M0 (j, q) = false := by
  show xor (rpG2 M0 (rpY j, q))
    (rpPar fun k : Fin c => rpG2 M0 (rpY j, rpZ k) && rpG3 M0 (rpZ k, q)) = false
  simp only [rp_g2_zerorow M0 _ h, Bool.false_and, rp_par_false, Bool.xor_false]

theorem rp7_clr2_zero (j : Fin b) (h : rpG2 M0 (rpY j, rpY j) = false) (q : rpCol a b c) :
    rpClr2 M0 (j, q) = false := by
  show xor (rpClr1 M0 (j, q))
    (rpPar fun l : Fin c => rpClr1 M0 (j, rpZ l) && rpYt M0 (l, q)) = false
  simp only [rp7_clr1_zero M0 j h, Bool.false_and, rp_par_false, Bool.xor_false]

theorem rp7_g5_upper (p q : rpCol a b c) (h : rpRk5 a b c q < rpRk5 a b c p) :
    rpG5 M0 (p, q) = false :=
  rp_gj_upper _ _ _ _ ((rp_ord_lt _ _ _ _).2 h)

theorem rp7_g5_zerorow (p : rpCol a b c) (hp : rpG5 M0 (p, p) = false) (q : rpCol a b c) :
    rpG5 M0 (p, q) = false :=
  rp_gj_zerorow _ _ p hp q

theorem rp7_g5_zcol (k : Fin c)
    (h : rpG3 M0 (rpZ k, rpZ k) = true ∨ rpG4 M0 (Sum.inl k, Sum.inl k) = true)
    (p : rpCol a b c) : rpG5 M0 (p, rpZ k) = false := by
  apply rp_gj_zcol
  intro p'
  rcases p' with i | j | k' | u
  · rfl
  · show rpClr2 M0 (j, rpZ k) = false
    rcases h with h | h
    · exact rp7_clr2_z1 M0 j k h
    · exact rp7_clr2_z2 M0 j k h
  · rfl
  · rfl

theorem rp7_g5_card :
    (Finset.univ.filter (fun k : Fin c => rpG5 M0 (rpZ k, rpZ k) = true)).card +
      (Finset.univ.filter (fun j : Fin b => rpG5 M0 (rpY j, rpY j) = true)).card ≤
      (Finset.univ.filter (fun j : Fin b => rpG2 M0 (rpY j, rpY j) = true)).card := by
  have h := rp_gj_card (rpOrd (rpRk5 a b c) (rp_rk5_inj a b c)) (rpIn5 M0)
    ((Finset.univ.filter (fun j : Fin b => rpG2 M0 (rpY j, rpY j) = true)).map
      ⟨fun j : Fin b => (rpY j : rpCol a b c), fun j j' hh => by simpa using hh⟩) (by
      intro p hp q
      rcases p with i | j | k | u
      · rfl
      · show rpClr2 M0 (j, q) = false
        apply rp7_clr2_zero
        by_contra hc
        apply hp
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        exact ⟨j, by simpa using hc, rfl⟩
      · rfl
      · rfl)
  rw [Finset.card_map] at h
  have h2 := rp_card_col (fun p : rpCol a b c => rpG5 M0 (p, p))
  have h4 : (Finset.univ.filter (fun p : rpCol a b c => rpG5 M0 (p, p) = true)).card ≤
      (Finset.univ.filter (fun j : Fin b => rpG2 M0 (rpY j, rpY j) = true)).card := h
  omega

theorem rp7_link (w : rpCol a b c → ZMod 2)
    (hU : ∀ k : Fin c, rpEv w (fun q => rpG3 M0 (rpZ k, q)) = 0)
    (hY : ∀ l : Fin c, rpEv w (fun q => rpG4 M0 (Sum.inl l, Sum.inr q)) = 0) :
    (∀ j : Fin b, rpEv w (fun q => rpG2 M0 (rpY j, q)) = 0) ↔
      (∀ p : rpCol a b c, rpEv w (fun q => rpG5 M0 (p, q)) = 0) := by
  have key : ∀ j : Fin b, rpEv w (fun q => rpClr2 M0 (j, q)) =
      rpEv w (fun q => rpG2 M0 (rpY j, q)) := by
    intro j
    rw [rp7_clr2_ev, rp7_clr1_ev]
    simp only [rp7_yt_ev, hU, hY, mul_zero, Finset.sum_const_zero, add_zero]
  have hs := rp_gj_sat (rpOrd (rpRk5 a b c) (rp_rk5_inj a b c)) (rpIn5 M0) w
  constructor
  · intro hj
    refine hs.2 (fun p => ?_)
    rcases p with i | j | k | u
    · exact rp_ev_zero _ _ (fun q => rfl)
    · show rpEv w (fun q => rpClr2 M0 (j, q)) = 0
      rw [key]
      exact hj j
    · exact rp_ev_zero _ _ (fun q => rfl)
    · exact rp_ev_zero _ _ (fun q => rfl)
  · intro hp j
    have h1 : rpEv w (fun q => rpClr2 M0 (j, q)) = 0 := hs.1 hp (rpY j)
    rw [← key]
    exact h1

end s7

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

abbrev swCount {n : Nat} (f : Fin n → Bool) := (Finset.univ.filter fun i => f i = true).card

theorem swCountSum {n : Nat} (f : Fin n → Bool) : swCount f = ∑ i, (f i).toNat := by
  rw [swCount,Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => by cases f i <;> decide

theorem swBnd2 {n : Nat} (f g : Fin n → Bool) (h : ∀ i, f i = true → g i = false) :
    swCount f + swCount g ≤ n := by
  rw [swCountSum,swCountSum,← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _i : Fin n, 1 := by
      refine Finset.sum_le_sum fun i _ => ?_
      cases he : f i <;> cases he' : g i <;> simp_all
    _ = n := by simp

theorem swBnd3 {n : Nat} (f g h : Fin n → Bool)
    (fg : ∀ i, f i = true → g i = false) (fh : ∀ i, f i = true → h i = false)
    (gh : ∀ i, g i = true → h i = false) : swCount f + swCount g + swCount h ≤ n := by
  rw [swCountSum,swCountSum,swCountSum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _i : Fin n, 1 := by
      refine Finset.sum_le_sum fun i _ => ?_
      cases he : f i <;> cases he' : g i <;> cases he'' : h i <;> simp_all
    _ = n := by simp

theorem swRowFits {a b c m : Nat} (M : Fin m × rpCol a b c → Bool)
    (hDG : ∀ i, rpAdg M i = true → rpG3 M (rpZ i,rpZ i) = true)
    (h5X : ∀ i, rpG3 M (rpZ i,rpZ i) = true ∨ rpAyz M i = true → rpAxor M i = false)
    (h4YZ : swCount (rpAdg M) + swCount (rpAyz M) ≤ swCount (fun i => rpG1 M (rpY i,rpY i)))
    (h5XY : swCount (rpAxor M) + swCount (rpAxy M) ≤ swCount (fun i => rpG2 M (rpY i,rpY i))) :
    (swCount (rpAxor M) + swCount (rpAdg M) + swCount (rpAxy M) + swCount (rpAxz M) ≤ a) ∧
    (swCount (rpAxor M) + swCount (rpAdg M) + swCount (rpAxy M) + swCount (rpAyz M) ≤ b) ∧
    (swCount (rpAxor M) + swCount (rpAdg M) + swCount (rpAxz M) + swCount (rpAyz M) ≤ c) := by
  let G3 := fun i : Fin c => rpG3 M (rpZ i,rpZ i)
  let G2Y := fun i : Fin b => rpG2 M (rpY i,rpY i)
  let G2X := fun i : Fin a => rpG2 M (rpX i,rpX i)
  let G1Y := fun i : Fin b => rpG1 M (rpY i,rpY i)
  have part : swCount (rpAdg M) + swCount (rpAxz M) = swCount G3 := by
    rw [swCountSum,swCountSum,swCountSum,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (rpAdg M i).toNat + ((G3 i) && !(rpAdg M i)).toNat = (G3 i).toNat
    have h : rpAdg M i = true → G3 i = true := hDG i
    cases hd : rpAdg M i <;> cases hg : G3 i <;> simp_all
  have x1 : swCount G3 ≤ swCount G2X := rp_g3_card M
  have x2 : swCount G2X + swCount G2Y ≤ a := rp_g2_card M
  have y1 : swCount G1Y + swCount G2Y ≤ b := swBnd2 _ _ (rp_g2_disj M)
  have z1 : swCount G3 + swCount (rpAyz M) + swCount (rpAxor M) ≤ c :=
    swBnd3 _ _ _ (fun i hi => rp_g4_decz M i hi (.inl i)) (fun i hi => h5X i (.inl hi))
      (fun i hi => h5X i (.inr hi))
  change swCount (rpAxor M) + swCount (rpAxy M) ≤ swCount G2Y at h5XY
  change swCount (rpAdg M) + swCount (rpAyz M) ≤ swCount G1Y at h4YZ
  exact ⟨by omega, by omega, by omega⟩

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

section final

variable {a b c m : ℕ} (M0 : Fin m × rpCol a b c → Bool)

theorem rp_sat (w : rpCol a b c → ZMod 2) :
    (∀ i, rpEv w (fun q => M0 (i, q)) = 0) ↔
      (∀ k, rpEv w (fun q => rpXOR M0 (k, q)) = 0) ∧
      (∀ j, rpEv w (fun q => rpXY M0 (j, q)) = 0) ∧
      (∀ k, rpEv w (fun q => rpUfix M0 (k, q)) = 0) ∧
      (∀ k, rpEv w (fun q => rpDY M0 (k, q)) = 0) ∧
      (∀ l, rpEv w (fun q => rpYZ M0 (l, q)) = 0) ∧
      (∀ p, rpEv w (fun q => rpPX M0 (p, q)) = 0) ∧
      (∀ p, rpEv w (fun q => rpPY M0 (p, q)) = 0) ∧
      (∀ p, rpEv w (fun q => rpCN M0 (p, q)) = 0) := by
  constructor
  · intro hM
    have h1 : ∀ p, rpEv w (fun q => rpG1 M0 (p, q)) = 0 := (rp_g1_sat M0 w).2 hM
    have h2 : ∀ p, rpEv w (fun q => rpG2 M0 (p, q)) = 0 :=
      (rp_g2_sat M0 w).2 (fun i => h1 (rpX i))
    have h3 : ∀ p, rpEv w (fun q => rpG3 M0 (p, q)) = 0 :=
      (rp_g3_sat M0 w).2 (fun i => h2 (rpX i))
    have h4 : ∀ p, rpEv w (fun q => rpG4 M0 (p, Sum.inr q)) = 0 :=
      (rp_g4_sat M0 w).2 (fun j => h1 (rpY j))
    have hU : ∀ k : Fin c, rpEv w (fun q => rpG3 M0 (rpZ k, q)) = 0 := fun k => h3 (rpZ k)
    have hY : ∀ l : Fin c, rpEv w (fun q => rpG4 M0 (Sum.inl l, Sum.inr q)) = 0 :=
      fun l => h4 (Sum.inl l)
    have h5 : ∀ p, rpEv w (fun q => rpG5 M0 (p, q)) = 0 :=
      (rp7_link M0 w hU hY).1 (fun j => h2 (rpY j))
    refine ⟨fun k => h5 (rpZ k), fun j => h5 (rpY j), (rp_ufix_sat M0 w).2 hU,
      fun k => h4 (rpPz k), hY, ?_, fun j => h4 (Sum.inr (rpY j)), ?_⟩
    · intro p
      rcases p with i | i
      · exact h3 (rpX i)
      · exact h5 (rpX i)
    · intro p
      rcases p with s | s | u | u | u
      · exact h1 (Sum.inr (Sum.inr s))
      · exact h2 (Sum.inr (Sum.inr s))
      · exact h3 rpR
      · exact h4 (Sum.inr rpR)
      · exact h5 rpR
  · rintro ⟨hXOR, hXY, hUf, hDY, hYZ, hPX, hPY, hCN⟩
    have hU : ∀ k : Fin c, rpEv w (fun q => rpG3 M0 (rpZ k, q)) = 0 :=
      (rp_ufix_sat M0 w).1 hUf
    have h3 : ∀ p, rpEv w (fun q => rpG3 M0 (p, q)) = 0 := by
      intro p
      rcases p with i | j | k | u
      · exact hPX (Sum.inl i)
      · exact rp_ev_zero _ _ (fun q => rp_g3_yrow M0 j q)
      · exact hU k
      · exact hCN (Sum.inr (Sum.inr (Sum.inl ())))
    have h5 : ∀ p, rpEv w (fun q => rpG5 M0 (p, q)) = 0 := by
      intro p
      rcases p with i | j | k | u
      · exact hPX (Sum.inr i)
      · exact hXY j
      · exact hXOR k
      · exact hCN (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))
    have h2Y : ∀ j : Fin b, rpEv w (fun q => rpG2 M0 (rpY j, q)) = 0 :=
      (rp7_link M0 w hU hYZ).2 h5
    have h2X : ∀ i : Fin a, rpEv w (fun q => rpG2 M0 (rpX i, q)) = 0 := (rp_g3_sat M0 w).1 h3
    have h2 : ∀ p, rpEv w (fun q => rpG2 M0 (p, q)) = 0 := by
      intro p
      rcases p with i | j | s
      · exact h2X i
      · exact h2Y j
      · exact hCN (Sum.inr (Sum.inl s))
    have h1X : ∀ i : Fin a, rpEv w (fun q => rpG1 M0 (rpX i, q)) = 0 := (rp_g2_sat M0 w).1 h2
    have h4 : ∀ p, rpEv w (fun q => rpG4 M0 (p, Sum.inr q)) = 0 := by
      intro p
      rcases p with l | i | j | k | u
      · exact hYZ l
      · exact rp_ev_zero _ _ (fun q => rp_g4_xrow M0 i _)
      · exact hPY j
      · exact hDY k
      · exact hCN (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
    have h1Y : ∀ j : Fin b, rpEv w (fun q => rpG1 M0 (rpY j, q)) = 0 := (rp_g4_sat M0 w).1 h4
    have h1 : ∀ p, rpEv w (fun q => rpG1 M0 (p, q)) = 0 := by
      intro p
      rcases p with i | j | s
      · exact h1X i
      · exact h1Y j
      · exact hCN (Sum.inl s)
    exact (rp_g1_sat M0 w).1 h1

theorem rp_facts : rpFacts M0 where
  sat := rp_sat M0
  xy_z := fun j k => rp7_g5_upper M0 (rpY j) (rpZ k) (by simp only [rpRk5]; omega)
  ux_y := rp_ufix_y M0
  dy_x := fun k i => rp_g4_x M0 (rpPz k) i
  yz_x := fun l i => rp_g4_x M0 (Sum.inl l) i
  px_y := by
    intro p j
    rcases p with i | i
    · exact rp_g3_y M0 (rpX i) j
    · exact rp7_g5_upper M0 (rpX i) (rpY j) (by simp only [rpRk5]; omega)
  px_z := by
    intro p k
    rcases p with i | i
    · exact rp_g3_xz M0 i k
    · exact rp7_g5_upper M0 (rpX i) (rpZ k) (by simp only [rpRk5]; omega)
  py_x := fun p i => rp_g4_x M0 (Sum.inr (rpY p)) i
  py_z := fun p k => rp_g4_yz M0 p k
  cn_x := by
    intro p i
    rcases p with s | s | u | u | u
    · exact rp_g1_tx M0 s i
    · exact rp_g2_tx M0 s i
    · exact rp_g3_rx M0 i
    · exact rp_g4_x M0 (Sum.inr rpR) i
    · exact rp7_g5_upper M0 rpR (rpX i) (by simp only [rpRk5]; omega)
  cn_y := by
    intro p j
    rcases p with s | s | u | u | u
    · exact rp_g1_ty M0 s j
    · exact rp_g2_ty M0 s j
    · exact rp_g3_y M0 rpR j
    · exact rp_g4_ry M0 j
    · exact rp7_g5_upper M0 rpR (rpY j) (by simp only [rpRk5]; omega)
  dg_z := fun k l h => rp_ufix_z M0 k l h
  xor_off := fun k q h => rp7_g5_zerorow M0 (rpZ k) h q
  xy_off := fun j q h => rp7_g5_zerorow M0 (rpY j) h q
  dy_off := fun k q h => rp_g4_zerorow M0 (rpPz k) h (Sum.inr q)
  yz_off := fun l q h => rp_g4_zerorow M0 (Sum.inl l) h (Sum.inr q)
  ux_off := by
    intro k q h1 h2
    apply rp_ufix_off M0 k _ q
    have h1' : rpG4 M0 (rpPz k, rpPz k) = false := h1
    have h2' : (rpG3 M0 (rpZ k, rpZ k) && !rpG4 M0 (rpPz k, rpPz k)) = false := h2
    rw [h1'] at h2'
    simpa using h2'
  dg_xz := by
    intro k h
    have h' : rpG4 M0 (rpPz k, rpPz k) = true := h
    show (rpG3 M0 (rpZ k, rpZ k) && !rpG4 M0 (rpPz k, rpPz k)) = false
    rw [h']
    simp
  fit_x := (swRowFits M0 (fun k h => rp_g4_active M0 k h)
    (fun k h => rp7_g5_zcol M0 k h (rpZ k))
    ((Nat.add_comm _ _).trans_le (rp_g4_card M0)) (rp7_g5_card M0)).1
  fit_y := (swRowFits M0 (fun k h => rp_g4_active M0 k h)
    (fun k h => rp7_g5_zcol M0 k h (rpZ k))
    ((Nat.add_comm _ _).trans_le (rp_g4_card M0)) (rp7_g5_card M0)).2.1
  fit_z := (swRowFits M0 (fun k h => rp_g4_active M0 k h)
    (fun k h => rp7_g5_zcol M0 k h (rpZ k))
    ((Nat.add_comm _ _).trans_le (rp_g4_card M0)) (rp7_g5_card M0)).2.2

end final

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

theorem ctl_spec (a b c m t : ℕ) (ea : Fin (2^a) ≃ V a) (eb : Fin (2^b) ≃ V b) :
    CtlSpec a b c m t ea eb := by
  apply swCtlFromFacts
  intro H r f g
  let M := ceM0 a b c m t (inpOf H r f g)
  have hF := rp_facts M
  exact ⟨ce_fits hF (le_max_left ..) ((le_max_left ..).trans (le_max_right ..))
    ((le_max_right ..).trans (le_max_right ..)), ce_iff H r f g hF⟩

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

private def rcRead {ι : Type} {W : ℕ} (v : ι → Bool) (f : Fin W → ι) : BitVec W :=
  bv (fun i => v (f i))

private def rcProblem (X Y Z : Type) [Fintype Y] (W C : ℕ) : Prop :=
  ∀ {ι : Type} (A : X → Y → Fin W → ι) (B : Y → Z → Fin W → ι),
  Cmp ι ((X × Z) × Fin W) C (fun v => untab (fun p =>
    ∑ j, rcRead v (A p.1 j) * rcRead v (B j p.2)))

private theorem rcSum {ι T : Type} {W C : ℕ} (f : T → (ι → Bool) → BitVec W)
    (h : ∀ j, Cw ι W C (f j)) (s : Finset T) :
    Cw ι W (W + s.card * (C + 20 * (W + 1))) (fun v => ∑ j ∈ s, f j v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cw.const (ι := ι) (0 : BitVec W)
  | @insert j s hj ih =>
    simpa [hj, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Cw.add (h j) ih)

private theorem rcNaive {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (W D : ℕ) (hXZ : Fintype.card (X × Z) ≤ D)
    (hXYZ : Fintype.card (X × Z) * Fintype.card Y ≤ D) :
    rcProblem X Y Z W (D * (64 * (W+1)^2)) := by
  intro ι A B
  have h (p : X × Z) (j : Y) :
      Cw ι W (30 * (W+1)^2) (fun v => rcRead v (A p.1 j) * rcRead v (B j p.2)) :=
    by simpa only [Nat.zero_add, rcRead] using (Cw.mul (Cw.var (A p.1 j)) (Cw.var (B j p.2)))
  have hs (p : X × Z) := rcSum _ (h p) Finset.univ
  simp only [Finset.card_univ] at hs
  refine (Cmp.ofWords hs).mono ?_
  have hw : W+1 ≤ (W+1)^2 := by nlinarith
  calc
    _ = Fintype.card (X × Z) * W +
        (Fintype.card (X × Z) * Fintype.card Y) * (30*(W+1)^2 + 20*(W+1)) := by ring
    _ ≤ D * W + D * (30*(W+1)^2 + 20*(W+1)) := by gcongr
    _ ≤ _ := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)

private def rcL {R : Type} [Add R] [Sub R] (a b c d : R) (i : Fin 7) : R :=
  match i.val with
  | 0 => a+d
  | 1 => c+d
  | 2 => a
  | 3 => d
  | 4 => a+b
  | 5 => c-a
  | _ => b-d

private def rcR {R : Type} [Add R] [Sub R] (e f g h : R) (i : Fin 7) : R :=
  match i.val with
  | 0 => e+h
  | 1 => e
  | 2 => f-h
  | 3 => g-e
  | 4 => h
  | 5 => e+f
  | _ => g+h

private def rcOut {R : Type} [Add R] [Sub R] (p : Fin 7 → R) : Bool → Bool → R
  | false, false => (p 0 + p 3) + (p 6 - p 4)
  | false, true => p 2 + p 4
  | true, false => p 1 + p 3
  | true, true => (p 0 - p 1) + (p 2 + p 5)

private theorem rcLCw {ι : Type} {W : ℕ} (a b c d : Fin W → ι) (i : Fin 7) :
    Cw ι W (20*(W+1)) (fun v => rcL (rcRead v a) (rcRead v b) (rcRead v c) (rcRead v d) i) := by
  have H (u : Fin W → ι) : Cw ι W 0 (fun v => rcRead v u) := Cw.var _
  fin_cases i <;> dsimp [rcL]
  · simpa only [Nat.zero_add] using Cw.add (H a) (H d)
  · simpa only [Nat.zero_add] using Cw.add (H c) (H d)
  · exact (H a).mono (Nat.zero_le _)
  · exact (H d).mono (Nat.zero_le _)
  · simpa only [Nat.zero_add] using Cw.add (H a) (H b)
  · simpa only [Nat.zero_add] using Cw.sub (H c) (H a)
  · simpa only [Nat.zero_add] using Cw.sub (H b) (H d)

private theorem rcRCw {ι : Type} {W : ℕ} (a b c d : Fin W → ι) (i : Fin 7) :
    Cw ι W (20*(W+1)) (fun v => rcR (rcRead v a) (rcRead v b) (rcRead v c) (rcRead v d) i) := by
  have H (u : Fin W → ι) : Cw ι W 0 (fun v => rcRead v u) := Cw.var _
  fin_cases i <;> dsimp [rcR]
  · simpa only [Nat.zero_add] using Cw.add (H a) (H d)
  · exact (H a).mono (Nat.zero_le _)
  · simpa only [Nat.zero_add] using Cw.sub (H b) (H d)
  · simpa only [Nat.zero_add] using Cw.sub (H c) (H a)
  · exact (H d).mono (Nat.zero_le _)
  · simpa only [Nat.zero_add] using Cw.add (H a) (H b)
  · simpa only [Nat.zero_add] using Cw.add (H c) (H d)

private theorem rcOutCw {ι : Type} {W : ℕ} (f : Fin 7 → Fin W → ι) (a b : Bool) :
    Cw ι W (60*(W+1)) (fun v => rcOut (fun k => rcRead v (f k)) a b) := by
  have H (k : Fin 7) : Cw ι W 0 (fun v => rcRead v (f k)) := Cw.var _
  cases a <;> cases b
  · exact (Cw.add (Cw.add (H 0) (H 3)) (Cw.sub (H 6) (H 4))).mono (by omega)
  · exact (Cw.add (H 2) (H 4)).mono (by omega)
  · exact (Cw.add (H 1) (H 3)).mono (by omega)
  · exact (Cw.add (Cw.sub (H 0) (H 1)) (Cw.add (H 2) (H 5))).mono (by omega)

private theorem rcLaw {R T : Type} [CommRing R] [Fintype T]
    (A B : Bool → Bool → T → R) (x z : Bool) :
    rcOut (fun k => ∑ j, rcL (A false false j) (A false true j) (A true false j) (A true true j) k *
      rcR (B false false j) (B false true j) (B true false j) (B true true j) k) x z =
    ∑ j : Bool × T, A x j.1 j.2 * B j.1 z j.2 := by
  cases x <;> cases z <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, rcOut, rcL, rcR,
      show (0 : Fin 7).val = 0 by rfl, show (1 : Fin 7).val = 1 by rfl,
      show (2 : Fin 7).val = 2 by rfl, show (3 : Fin 7).val = 3 by rfl,
      show (4 : Fin 7).val = 4 by rfl, show (5 : Fin 7).val = 5 by rfl,
      show (6 : Fin 7).val = 6 by rfl,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib] <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

private theorem rcStep {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {W C M : ℕ} (hP : rcProblem X Y Z W C)
    (hXY : Fintype.card (X × Y) ≤ M) (hYZ : Fintype.card (Y × Z) ≤ M)
    (hXZ : Fintype.card (X × Z) ≤ M) :
    rcProblem (Bool × X) (Bool × Y) (Bool × Z) W (7*C + 520*(W+1)*M) := by
  intro ι A B
  let L (i : Fin 7) (v : ι → Bool) (p : X × Y) := rcL
    (rcRead v (A (false,p.1) (false,p.2))) (rcRead v (A (false,p.1) (true,p.2)))
    (rcRead v (A (true,p.1) (false,p.2))) (rcRead v (A (true,p.1) (true,p.2))) i
  let R (i : Fin 7) (v : ι → Bool) (p : Y × Z) := rcR
    (rcRead v (B (false,p.1) (false,p.2))) (rcRead v (B (false,p.1) (true,p.2)))
    (rcRead v (B (true,p.1) (false,p.2))) (rcRead v (B (true,p.1) (true,p.2))) i
  let P (i : Fin 7) (v : ι → Bool) (p : X × Z) := ∑ j, L i v (p.1,j) * R i v (j,p.2)
  have hp (i : Fin 7) : Cmp ι ((X × Z) × Fin W) (M*(20*(W+1)) + M*(20*(W+1)) + C)
      (fun v => untab (P i v)) := by
    have l : Cmp ι ((X × Y) × Fin W) (M*(20*(W+1))) (fun v => untab (L i v)) :=
      (Cmp.ofWords (G := L i) (fun p => rcLCw _ _ _ _ i)).mono (Nat.mul_le_mul_right _ hXY)
    have r : Cmp ι ((Y × Z) × Fin W) (M*(20*(W+1))) (fun v => untab (R i v)) :=
      (Cmp.ofWords (G := R i) (fun p => rcRCw _ _ _ _ i)).mono (Nat.mul_le_mul_right _ hYZ)
    refine ((l.pair r).comp (hP (fun x y t => Sum.inl ((x,y),t))
      (fun y z t => Sum.inr ((y,z),t)))).congr ?_
    intro v p
    simp only [rcRead, Sum.elim_inl, Sum.elim_inr, untab, bv_getLsbD, P]
  let G (w : Fin 7 × ((X × Z) × Fin W) → Bool) (p : (Bool × X) × (Bool × Z)) :=
    rcOut (fun i => rcRead w (fun t => (i,((p.1.2,p.2.2),t)))) p.1.1 p.2.1
  have hG := Cmp.ofWords (G := G) (fun p => rcOutCw _ p.1.1 p.2.1)
  refine ((Cmp.piU hp).comp hG).congr ?_ |>.mono ?_
  · intro v p
    rcases p with ⟨⟨⟨x,u⟩,⟨z,w⟩⟩,t⟩
    simp only [untab, G, rcRead, bv_getLsbD]
    exact congrArg (fun q : BitVec W => q.getLsbD t.val)
      (rcLaw (fun x y j => rcRead v (A (x,u) (y,j))) (fun y z j => rcRead v (B (y,j) (z,w))) x z)
  · have hh : Fintype.card ((Bool × X) × (Bool × Z)) ≤ 4*M := by
      simp only [Fintype.card_prod, Fintype.card_bool] at hXZ ⊢
      nlinarith
    rw [Fintype.card_fin]
    calc
      _ ≤ 7*(M*(20*(W+1)) + M*(20*(W+1)) + C) + (4*M)*(60*(W+1)) := by gcongr
      _ = _ := by ring

private def rcIx (a : ℕ) : ℕ → Type
  | 0 => Fin (2^a)
  | s+1 => Bool × rcIx a s

private instance rcFintype (a : ℕ) : (s : ℕ) → Fintype (rcIx a s)
  | 0 => inferInstanceAs (Fintype (Fin (2^a)))
  | s+1 => @instFintypeProd _ _ inferInstance (rcFintype a s)

private theorem rcCard (a s : ℕ) : Fintype.card (rcIx a s) = 2^a * 2^s := by
  induction s with
  | zero =>
    change Fintype.card (Fin (2^a)) = _
    simp
  | succ s ih =>
    change Fintype.card (Bool × rcIx a s) = _
    rw [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]; ring

private def rcCost (W : ℕ) : ℕ → ℕ
  | 0 => 64*(W+1)^2
  | s+1 => 7*rcCost W s + 520*(W+1)*4^s

private theorem rcCostBound (W s : ℕ) :
    rcCost W s + 200*(W+1)^2*4^s ≤ 2048*(W+1)^2*7^s := by
  have hw : W+1 ≤ (W+1)^2 := by nlinarith
  induction s with
  | zero => simp only [rcCost, pow_zero, mul_one]; omega
  | succ s ih =>
    have h : 520*(W+1)*4^s ≤ 600*(W+1)^2*4^s :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [rcCost, pow_succ (4:ℕ) s, pow_succ (7:ℕ) s]
    nlinarith only [h, ih]

private theorem rcPairCard (a b s D : ℕ) (h : 2^a * 2^b ≤ D) :
    Fintype.card (rcIx a s × rcIx b s) ≤ D * 4^s := by
  rw [Fintype.card_prod, rcCard, rcCard, show (4:ℕ) = 2*2 by decide, mul_pow]
  calc
    _ = (2^a * 2^b) * (2^s * 2^s) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ h

private theorem rcBuilt (W a b c s : ℕ) :
    rcProblem (rcIx a s) (rcIx b s) (rcIx c s) W (2^(a+b+c)*rcCost W s) := by
  let D := 2^(a+b+c)
  have cab : 2^a * 2^b ≤ D := by
    dsimp [D]; rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have cbc : 2^b * 2^c ≤ D := by
    dsimp [D]; rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have cac : 2^a * 2^c ≤ D := by
    dsimp [D]; rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  change rcProblem _ _ _ _ (D * rcCost W s)
  induction s with
  | zero =>
    apply rcNaive
    · simpa using rcPairCard a c 0 D cac
    · simp [Fintype.card_prod, rcCard, D, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  | succ s ih =>
    rw [show D*rcCost W (s+1) = 7*(D*rcCost W s) + 520*(W+1)*(D*4^s) by
      dsimp [rcCost]; ring]
    exact rcStep ih (rcPairCard a b s D cab) (rcPairCard b c s D cbc) (rcPairCard a c s D cac)

private theorem rcTransport {X Y Z X₁ Y₁ Z₁ : Type} [Fintype Y] [Fintype Y₁]
    {W C : ℕ} (ex : X ≃ X₁) (ey : Y ≃ Y₁) (ez : Z ≃ Z₁)
    (h : rcProblem X Y Z W C) : rcProblem X₁ Y₁ Z₁ W C := by
  intro ι A B
  have h₁ := h (fun x y => A (ex x) (ey y)) (fun y z => B (ey y) (ez z))
  have h₂ := h₁.comp (Cmp.wire (fun p : (X₁ × Z₁) × Fin W =>
    ((ex.symm p.1.1,ez.symm p.1.2),p.2)))
  rw [Nat.add_zero] at h₂
  apply h₂.congr
  rintro v ⟨⟨x,z⟩,t⟩
  simp only [untab, Equiv.apply_symm_apply]
  exact congrArg (fun q : BitVec W => q.getLsbD t.val)
    (ey.sum_comp (fun j => rcRead v (A x j) * rcRead v (B j z)))

private noncomputable def rcEquiv (a s : ℕ) (hs : s ≤ a) : rcIx (a-s) s ≃ V a :=
  Fintype.equivOfCardEq (by
    rw [rcCard, ← pow_add, Nat.sub_add_cancel hs]
    simp [V, ZMod.card])

theorem rectCore (W a b c s : ℕ) (ha : s ≤ a) (hb : s ≤ b) (hc : s ≤ c)
    {ι : Type} (A : V a → V b → Fin W → ι) (B : V b → V c → Fin W → ι) :
    Cmp ι ((V a × V c) × Fin W) (2048*(W+1)^2 * 2^(a+b+c-3*s) * 7^s)
      (fun v => untab (fun p => ∑ j, bv (fun t => v (A p.1 j t)) * bv (fun t => v (B j p.2 t)))) := by
  have h := rcTransport (rcEquiv a s ha) (rcEquiv b s hb) (rcEquiv c s hc)
    (rcBuilt W (a-s) (b-s) (c-s) s) A B
  apply h.mono
  rw [show a-s+(b-s)+(c-s) = a+b+c-3*s by omega]
  calc
    _ ≤ 2^(a+b+c-3*s)*(2048*(W+1)^2*7^s) :=
      Nat.mul_le_mul_left _ (le_trans (Nat.le_add_right _ _) (rcCostBound W s))
    _ = _ := by ring

private theorem rcBudget (w k m : ℕ) (h : k + 2*m ≤ w) :
    2^k * 7^m ≤ 2^(w%2) * 7^(w/2) := by
  have h₁ : k ≤ w%2 + 2*(w/2-m) := by omega
  have h₂ : 2^k ≤ 2^(w%2 + 2*(w/2-m)) := Nat.pow_le_pow_right (by decide) h₁
  calc
    _ ≤ 2^(w%2 + 2*(w/2-m))*7^m := Nat.mul_le_mul_right _ h₂
    _ = 2^(w%2)*4^(w/2-m)*7^m := by rw [pow_add, pow_mul]; norm_num
    _ ≤ 2^(w%2)*7^(w/2-m)*7^m := by gcongr; decide
    _ = _ := by rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]

theorem rcFinalCost (W w q d a b c : ℕ)
    (hx : q+d+a+b ≤ w) (hy : q+d+b+c ≤ w) (hz : q+d+a+c ≤ w) :
    let m := min a (min b c)
    (2^(d+a+b)+2^(d+b+c)+2^(d+a+c))*(2^7*(q+1)*(W+1)*2^q) +
      2^(q+d)*(2048*(W+1)^2*2^(a+b+c-3*m)*7^m) + (1 + 2^w) ≤
      2^30*(W+w+1)^3*(2^(w%2)*7^(w/2)) := by
  dsimp only
  let m := min a (min b c)
  let T := W+w+1
  let U := 2^(w%2)*7^(w/2)
  have hP : 2^w ≤ U := by simpa [U] using rcBudget w w 0 (by omega)
  have hbnd (e : ℕ) (he : q+e ≤ w) : 2^e * 2^q ≤ U := by
    rw [← pow_add]
    exact (Nat.pow_le_pow_right (by decide) (by omega : e+q ≤ w)).trans hP
  have h₁ := hbnd (d+a+b) (by omega)
  have h₂ := hbnd (d+b+c) (by omega)
  have h₃ := hbnd (d+a+c) (by omega)
  have h₄ : 2^(q+d)*2^(a+b+c-3*m)*7^m ≤ U := by
    rw [← pow_add]
    apply rcBudget
    dsimp [m]; omega
  have h₅ : (q+1)*(W+1) ≤ T^3 := by
    calc
      _ ≤ T*T := Nat.mul_le_mul (by dsimp [T]; omega) (by dsimp [T]; omega)
      _ ≤ _ := by dsimp [T]; nlinarith
  have h₆ : (W+1)^2 ≤ T^3 := by
    calc
      _ ≤ T^2 := Nat.pow_le_pow_left (by dsimp [T]; omega) _
      _ ≤ _ := Nat.pow_le_pow_right (by dsimp [T]; omega) (by decide)
  have h₇ : 1 ≤ U := by change 0 < U; dsimp [U]; positivity
  have h₈ : 1 ≤ T^3 := by change 0 < T^3; dsimp [T]; positivity
  have hs : (2^(d+a+b)+2^(d+b+c)+2^(d+a+c))*(2^7*(q+1)*(W+1)*2^q) ≤
      (3*128)*(T^3 * U) := by
    calc
      _ = 128*((q+1)*(W+1))*((2^(d+a+b)*2^q)+(2^(d+b+c)*2^q)+(2^(d+a+c)*2^q)) := by ring
      _ ≤ 128*T^3*(U+U+U) := by gcongr
      _ = _ := by ring
  have ht : 2^(q+d)*(2048*(W+1)^2*2^(a+b+c-3*m)*7^m) ≤ 2048*(T^3 * U) := by
    calc
      _ = 2048*(W+1)^2*(2^(q+d)*2^(a+b+c-3*m)*7^m) := by ring
      _ ≤ 2048*T^3*U := by gcongr
      _ = _ := by ring
  have hU : U ≤ T^3*U := by simpa only [one_mul] using Nat.mul_le_mul_right U h₈
  change _ + (2^(q+d)*(2048*(W+1)^2*2^(a+b+c-3*m)*7^m)) + _ ≤ 2^30*T^3*U
  rw [Nat.mul_assoc (2^30)]
  omega

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

def swTransform {q W : Nat} (F : V q → BitVec W) (z : V q) : BitVec W :=
  ∑ x, sgn (z ⬝ᵥ x) * F x

theorem swConv {q W : Nat} (F G : V q → BitVec W) (t : V q) :
    swTransform (fun z => swTransform F z * swTransform G z) t =
      2 ^ q * ∑ x, F x * G (t + x) := by
  classical
  have hterm (z : V q) :
      sgn (t ⬝ᵥ z) * (swTransform F z * swTransform G z) =
        ∑ x, ∑ y, sgn (z ⬝ᵥ (x + y + t)) * (F x * G y) := by
    unfold swTransform
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [dotProduct_add, dotProduct_add, fe_sgn_add, fe_sgn_add, dotProduct_comm t z]
    ring
  change (∑ z, sgn (t ⬝ᵥ z) * (swTransform F z * swTransform G z)) = _
  simp_rw [hterm]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  have hxy (y : V q) :
      (∑ z : V q, sgn (z ⬝ᵥ (x+y+t)) * (F x * G y)) =
        if y = t+x then 2^q * (F x * G y) else 0 := by
    rw [← Finset.sum_mul, show (∑ z : V q, (sgn (z ⬝ᵥ (x+y+t)) : BitVec W)) =
        (if x+y+t = 0 then 2^q else 0) from fg_char q (x+y+t)]
    have iff0 : x+y+t = 0 ↔ y = t+x := by
      have hh : ∀ a b c : ZMod 2, a+b+c = 0 ↔ b = c+a := by decide
      constructor
      · intro h
        exact funext fun j => (hh _ _ _).mp (congrFun h j)
      · intro h
        exact funext fun j => (hh _ _ _).mpr (congrFun h j)
    by_cases h : y = t+x
    · rw [if_pos (iff0.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (iff0.mp hh)), if_neg h, zero_mul]
  simp_rw [hxy]
  rw [Finset.sum_ite_eq']
  simp

theorem swContract {q W : Nat} {ι : Type} [Fintype ι]
    (F G : ι → V q → BitVec W) (t : V q) :
    swTransform (fun z => ∑ i, swTransform (F i) z * swTransform (G i) z) t =
      2^q * ∑ i, ∑ x, F i x * G i (t+x) := by
  unfold swTransform
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa only [swTransform, Finset.mul_sum] using swConv (F i) (G i) t

theorem swBit {q W : Nat} (x : BitVec W) (i : Nat) (hi : q+i < W) :
    ((2^q : BitVec W) * x).getLsbD (q+i) = x.getLsbD i := by
  have hk : (2^q : BitVec W) = BitVec.twoPow W q := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_twoPow]
    exact (Nat.pow_mod ..).symm
  rw [hk, mul_comm, BitVec.mul_twoPow_eq_shiftLeft, BitVec.getLsbD_shiftLeft]
  simp [hi]

abbrev SWRect (W a b c cost : Nat) :=
  ∀ {ι : Type} (A : V a → V b → Fin W → ι) (B : V b → V c → Fin W → ι),
    Cmp ι ((V a × V c) × Fin W) cost (fun v => untab (fun p =>
      ∑ j, bv (fun t => v (A p.1 j t)) * bv (fun t => v (B j p.2 t))))

def swCost (q d a b c W R : Nat) : Nat :=
  (2^(d+a+b) + 2^(d+b+c) + 2^(d+a+c)) * whtCost q W + 2^(q+d) * R

theorem swPacked {q d a b c W R : Nat} (hm : SWRect W a b c R)
    {ι : Type} (F : V q → V d → V a → V b → Fin W → ι)
    (G : V q → V d → V b → V c → Fin W → ι) :
    Cmp ι ((V d × V a × V c) × V q × Fin W) (swCost q d a b c W R)
      (fun v p => ((2^q : BitVec W) * ∑ k, ∑ x,
        bv (fun j => v (F x p.1.1 p.1.2.1 k j)) *
        bv (fun j => v (G (p.2.1+x) p.1.1 k p.1.2.2 j))).getLsbD p.2.2.val) := by
  let U := ((V d × V a × V b) × V q × Fin W) ⊕ ((V d × V b × V c) × V q × Fin W)
  let T := (V q × V d) × (V a × V c) × Fin W
  let frontF := Cmp.piU (fun k : V d × V a × V b =>
    Cmp.sel (fun j : V q × Fin W => F j.1 k.1 k.2.1 k.2.2 j.2) (cmp_wht q W))
  let frontG := Cmp.piU (fun k : V d × V b × V c =>
    Cmp.sel (fun j : V q × Fin W => G j.1 k.1 k.2.1 k.2.2 j.2) (cmp_wht q W))
  let mult := Cmp.piU (fun p : V q × V d =>
    hm (ι := U) (fun i j t => Sum.inl ((p.2,i,j),p.1,t))
      (fun j k t => Sum.inr ((p.2,j,k),p.1,t)))
  let back := Cmp.piU (fun p : V d × V a × V c =>
    Cmp.sel (fun k : V q × Fin W => ((k.1,p.1),(p.2.1,p.2.2),k.2) : V q × Fin W → T)
      (cmp_wht q W))
  have H := Cmp.comp (Cmp.comp (Cmp.pair frontF frontG) mult) back
  refine Cmp.mono (Cmp.congr H ?_) ?_
  · rintro v ⟨⟨delta,i,l⟩,z,j⟩
    let A := fun k x => bv (fun j => v (F x delta i k j))
    let B := fun k x => bv (fun j => v (G x delta k l j))
    change (∑ t, sgn (z ⬝ᵥ t) * bv (fun e : Fin W =>
      (∑ k, bv (fun f : Fin W => (swTransform (A k) t).getLsbD f.val) *
        bv (fun f : Fin W => (swTransform (B k) t).getLsbD f.val) : BitVec W).getLsbD e.val)).getLsbD j.val =
      ((2^q : BitVec W) * ∑ k, ∑ x, A k x * B k (z+x)).getLsbD j.val
    simp only [bv_getLsbD]
    exact congrArg (fun x : BitVec W => x.getLsbD j.val) (swContract A B z)
  · simp only [Fintype.card_prod, fp_cardV, swCost, pow_add]
    exact le_of_eq (by ring)

def swPre {k : Nat} (x : V k) (r : Nat → ZMod 2) (i : Nat) : ZMod 2 :=
  if h : i < k then x ⟨i,h⟩ else r (i-k)

def sw4 (w : Nat) {q d a b : Nat} (Q : V q) (D : V d) (A : V a) (B : V b) : V w :=
  fun i => swPre Q (swPre D (swPre A (swPre B (fun _ => 0)))) i.val

def swSl (off n : Nat) {w : Nat} (x : V w) : V n := fun i => co x (off+i.val)

def swTail (n : Nat) {w : Nat} (x : V w) : Prop := ∀ j : Fin w, n ≤ j.val → x j = 0

theorem swPre1 {k : Nat} (x : V k) (r : Nat → ZMod 2) (i : Fin k) :
    swPre x r i.val = x i := by simp [swPre]

theorem swPre2 {k : Nat} (x : V k) (r : Nat → ZMod 2) (i : Nat) :
    swPre x r (k+i) = r i := by simp [swPre]

theorem swRead4 {w q d a b : Nat} (hf : q+d+a+b ≤ w)
    (Q : V q) (D : V d) (A : V a) (B : V b) :
    swSl 0 q (sw4 w Q D A B) = Q ∧ swSl q d (sw4 w Q D A B) = D ∧
    swSl (q+d) a (sw4 w Q D A B) = A ∧ swSl (q+d+a) b (sw4 w Q D A B) = B ∧
    swTail (q+d+a+b) (sw4 w Q D A B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i
    simp [swSl, co, show i.val < w by omega, sw4, swPre1]
  · funext i
    simp [swSl, co, show q+i.val < w by omega, sw4, swPre1, swPre2]
  · funext i
    simp [swSl, co, show q+(d+i.val) < w by omega, sw4, Nat.add_assoc, swPre1, swPre2]
  · funext i
    simp [swSl, co, show q+(d+(a+i.val)) < w by omega, sw4, Nat.add_assoc, swPre1, swPre2]
  · intro i hi
    have e : i.val = q+(d+(a+(b+(i.val-(q+d+a+b))))) := by omega
    unfold sw4
    rw [e]
    simp only [swPre2]

theorem swEta {w q d a b : Nat} (x : V w) (ht : swTail (q+d+a+b) x) :
    sw4 w (swSl 0 q x) (swSl q d x) (swSl (q+d) a x) (swSl (q+d+a) b x) = x := by
  funext i
  simp only [sw4, swPre]
  split_ifs with h1 h2 h3 h4
  · simp [swSl, co]
  · simp [swSl, co, show q+(i.val-q) = i.val by omega]
  · simp [swSl, co, show q+d+(i.val-q-d) = i.val by omega]
  · simp [swSl, co, show q+d+a+(i.val-q-d-a) = i.val by omega]
  · exact (ht i (by omega)).symm

theorem swStdSl {w q d k a b : Nat} (x y z : V w) :
    Std w q d k a b x y z ↔
      swSl 0 q y = swSl 0 q z + swSl 0 q x ∧
      swSl q d x = swSl q d z ∧ swSl q d y = swSl q d z ∧
      swSl (q+d) a x = swSl (q+d) a z ∧
      swSl (q+d+a) k x = swSl (q+d) k y ∧
      swSl (q+d+k) b y = swSl (q+d+a) b z ∧
      swTail (q+d+a+k) x ∧ swTail (q+d+k+b) y ∧ swTail (q+d+a+b) z := by
  have hh : ∀ i j k : ZMod 2, i+j = k ↔ j = k+i := by decide
  constructor
  · rintro ⟨hq,hd,ha,hk,hb,hx,hy,hz⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hx, hy, hz⟩
    · funext i; simpa [swSl] using (hh _ _ _).mp (hq i.val i.isLt)
    · funext i; exact (hd i.val i.isLt).1
    · funext i; exact (hd i.val i.isLt).2
    · funext i; exact ha i.val i.isLt
    · funext i; exact hk i.val i.isLt
    · funext i; exact hb i.val i.isLt
  · rintro ⟨hq,hdx,hdy,ha,hk,hb,hx,hy,hz⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, hx, hy, hz⟩
    · intro i hi; apply (hh _ _ _).mpr; simpa [swSl] using congrFun hq ⟨i,hi⟩
    · intro i hi; exact ⟨congrFun hdx ⟨i,hi⟩,congrFun hdy ⟨i,hi⟩⟩
    · intro i hi; exact congrFun ha ⟨i,hi⟩
    · intro i hi; exact congrFun hk ⟨i,hi⟩
    · intro i hi; exact congrFun hb ⟨i,hi⟩

theorem swSumGraph {α β γ M : Type} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (pick : α → β → Prop) [DecidableRel pick] (u : γ → α) (v : γ → β) (ex : α → γ)
    (left : Function.LeftInverse ex u)
    (spec : ∀ x y, pick x y ↔ u (ex x) = x ∧ v (ex x) = y)
    (f : α → β → M) :
    (∑ x, ∑ y, if pick x y then f x y else 0) = ∑ p, f (u p) (v p) := by
  classical
  have step (x : α) : (∑ y, if pick x y then f x y else 0) =
      if u (ex x) = x then f x (v (ex x)) else 0 := by
    by_cases h : u (ex x) = x
    · simp only [spec, h, true_and, ite_true, Finset.sum_ite_eq, Finset.mem_univ]
    · simp [spec, h]
  simp_rw [step]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun x => u (ex x) = x) = Finset.univ.image u := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨ex x, h⟩
    · rintro ⟨y,rfl⟩; rw [left y]
  rw [he, Finset.sum_image (fun _ _ _ _ h => left.injective h)]
  exact Finset.sum_congr rfl fun i _ => by rw [left i]

theorem swStdSum {w W q d k a b : Nat}
    (hx : q+d+a+k ≤ w) (hy : q+d+k+b ≤ w)
    (z : V w) (ht : swTail (q+d+a+b) z) (F G : V w → BitVec W) :
    (∑ x, ∑ y, if Std w q d k a b x y z then F x * G y else 0) =
      ∑ j : V k, ∑ s : V q,
        F (sw4 w s (swSl q d z) (swSl (q+d) a z) j) *
        G (sw4 w (swSl 0 q z+s) (swSl q d z) j (swSl (q+d+a) b z)) := by
  let K := V k × V q
  let U (p : K) := sw4 w p.2 (swSl q d z) (swSl (q+d) a z) p.1
  let Vv (p : K) := sw4 w (swSl 0 q z+p.2) (swSl q d z) p.1 (swSl (q+d+a) b z)
  let ex (x : V w) : K := (swSl (q+d+a) k x,swSl 0 q x)
  have L : Function.LeftInverse ex U := by
    intro p
    have e := swRead4 hx p.2 (swSl q d z) (swSl (q+d) a z) p.1
    exact Prod.ext e.2.2.2.1 e.1
  have H (x y : V w) : Std w q d k a b x y z ↔ U (ex x) = x ∧ Vv (ex x) = y := by
    constructor
    · intro h
      obtain ⟨hQ,hD,hD',hA,hK,hB,hX,hY,_⟩ := (swStdSl x y z).mp h
      constructor
      · simpa only [U, ex, hD, hA] using swEta x hX
      · simpa only [Vv, ex, hQ, hD', ← hK, hB] using swEta y hY
    · rintro ⟨h1,h2⟩
      let p := ex x
      have ex1 := swRead4 hx p.2 (swSl q d z) (swSl (q+d) a z) p.1
      have ex2 := swRead4 hy (swSl 0 q z+p.2) (swSl q d z) p.1 (swSl (q+d+a) b z)
      change U p = x at h1
      change Vv p = y at h2
      rw [← h1, ← h2, swStdSl]
      exact ⟨ex2.1.trans (congrArg _ ex1.1.symm), ex1.2.1, ex2.2.1,
        ex1.2.2.1, ex1.2.2.2.1.trans ex2.2.2.1.symm, ex2.2.2.2.1,
        ex1.2.2.2.2, ex2.2.2.2.2, ht⟩
  rw [swSumGraph (fun x y => Std w q d k a b x y z) U Vv ex L H (fun x y => F x * G y)]
  exact Fintype.sum_prod_type _

theorem swShapeAt {w W B q d k a b R : Nat} (hm : SWRect W a k b R)
    (hx : q+d+a+k ≤ w) (hy : q+d+k+b ≤ w) (hB : q+B ≤ W)
    (hCost : swCost q d a k b W R + 1 ≤ 2^30*(W+w+1)^3*Phi w) :
    ShapeSpec w W B q d k a b := by
  classical
  let I := ((V w × Fin W) ⊕ (V w × Fin W))
  let L := ((V d × V a × V b) × V q × Fin W)
  let F (s : V q) (u : V d) (i : V a) (j : V k) (e : Fin W) : I :=
    Sum.inl (sw4 w s u i j, e)
  let G (s : V q) (u : V d) (j : V k) (l : V b) (e : Fin W) : I :=
    Sum.inr (sw4 w s u j l, e)
  let pick (p : V w × Fin B) : L ⊕ Unit :=
    if swTail (q+d+a+b) p.1 then
      Sum.inl ((swSl q d p.1,swSl (q+d) a p.1,swSl (q+d+a) b p.1),swSl 0 q p.1,
        ⟨q+p.2.val,by omega⟩)
    else Sum.inr ()
  have h := Cmp.comp (Cmp.pair (swPacked hm F G) (Cb.const (ι := I) false)) (Cmp.wire pick)
  refine ⟨_, by simpa only [Nat.add_zero] using hCost, Cmp.congr h ?_⟩
  rintro v ⟨z,j⟩
  by_cases ht : swTail (q+d+a+b) z
  · simp only [pick, ht, ite_true, Sum.elim_inl]
    rw [swStdSum hx hy z ht]
    exact swBit _ j.val (by omega)
  · simp only [pick, ht, ite_false, Sum.elim_inr]
    have he (x y : V w) : ¬Std w q d k a b x y z :=
      fun h => ht (swStdSl x y z |>.mp h).2.2.2.2.2.2.2.2
    simp [he]

theorem shape_solver (w W B q d r1 r2 r3 : ℕ) (h1 : q+d+r1+r2 ≤ w)
    (h2 : q+d+r1+r3 ≤ w) (h3 : q+d+r2+r3 ≤ w) (hB : q+B ≤ W) :
    ShapeSpec w W B q d r1 r2 r3 := by
  let s := min r2 (min r1 r3)
  have h1' : q+d+r2+r1 ≤ w := by omega
  refine swShapeAt (q := q) (d := d) (rectCore W r2 r1 r3 s
    (min_le_left ..) ((min_le_right ..).trans (min_le_left ..))
    ((min_le_right ..).trans (min_le_right ..)))
    h1' h2 hB ?_
  have h := rcFinalCost W w q d r2 r1 r3 h1' h2 h3
  change swCost q d r2 r1 r3 W
    (2048*(W+1)^2*2^(r2+r1+r3-3*s)*7^s) + 1 ≤ _
  exact (Nat.add_le_add_left (Nat.le_add_right 1 (2^w)) _).trans h

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838
open PEqualNP.CircuitLowerBounds

instance (w : ℕ) (s : Fin 5 → ℕ) : Decidable (fitsW w s) := by
  unfold fitsW; infer_instance

def ShapeHyp : Prop := ∀ w W B q d r1 r2 r3 : ℕ, q + d + r1 + r2 ≤ w → q + d + r1 + r3 ≤ w →
  q + d + r2 + r3 ≤ w → q + B ≤ W → ShapeSpec w W B q d r1 r2 r3

def CtlHyp : Prop := ∀ (a b c m t : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b),
  CtlSpec a b c m t ea eb

abbrev dpK (w W c : ℕ) : Type :=
  (Fin 5 × Fin (w + 1)) ⊕ ((V w × Fin W) ⊕ ((V w × Fin W) ⊕ ((Fin w × Fin c) ⊕ V c)))

def dpSel {w W c : ℕ} (σ : Fin 5 → Fin (w + 1)) (u : dpK w W c → Bool) : Bool :=
  decide (∀ k, u (Sum.inl (k, σ k)) = true)

def dpOut (w W B : ℕ) (δ : Fin 5 → ℕ) (F G : V w × Fin W → Bool) (p : V w × Fin B) : Bool :=
  (∑ x : V w, ∑ y : V w, if Std w (δ 0) (δ 1) (δ 2) (δ 3) (δ 4) x y p.1 then
    tab F x * tab G y else 0 : BitVec W).getLsbD p.2.val

def dpGate (w W B c : ℕ) (σ : Fin 5 → Fin (w + 1)) (u : dpK w W c → Bool) (p : V w × Fin B) :
    Bool :=
  dpSel σ u && (if fitsW w (fun k => (σ k).val) then
    dpOut w W B (fun k => (σ k).val) (fun e => u (Sum.inr (Sum.inl e)))
      (fun e => u (Sum.inr (Sum.inr (Sum.inl e)))) p else false)

def dpCost (w W B : ℕ) : ℕ := 6 + 2 ^ 30 * (W + w + 1) ^ 3 * Phi w + 2 ^ w * B

theorem dp_gate_cmp (w W B c : ℕ) (hsh : ShapeHyp) (hB : w + B ≤ W) (σ : Fin 5 → Fin (w + 1)) :
    Cmp (dpK w W c) (V w × Fin B) (dpCost w W B) (dpGate w W B c σ) := by
  by_cases hf : fitsW w (fun k => (σ k).val)
  · obtain ⟨h1, h2, h3⟩ := hf
    have h0 : (σ 0).val + B ≤ W := by have := (σ 0).isLt; omega
    obtain ⟨S, hS, hc⟩ := hsh w W B (σ 0).val (σ 1).val (σ 2).val (σ 3).val (σ 4).val h1 h2 h3 h0
    have hc' := Cmp.sel (ι := dpK w W c)
      (fun e : (V w × Fin W) ⊕ (V w × Fin W) => Sum.elim (fun p => Sum.inr (Sum.inl p))
        (fun p => Sum.inr (Sum.inr (Sum.inl p))) e) hc
    have hs : Cb (dpK w W c) (Fintype.card (Fin 5) * (0 + 1) + 1) (dpSel σ) :=
      (Cb.bigAnd (ι := dpK w W c) (fun k : Fin 5 => Cb.var (ι := dpK w W c)
        (Sum.inl (k, σ k)))).congr (fun u => by simp [dpSel])
    have hp := Cmp.comp (Cmp.pair hs hc')
      (Cmp.ofBits (fun p : V w × Fin B => Cb.and (Cb.var (Sum.inl ())) (Cb.var (Sum.inr p))))
    refine (hp.mono ?_).congr ?_
    · rw [Fintype.card_fin, Fintype.card_prod, fp_cardV, Fintype.card_fin]
      unfold dpCost
      omega
    · intro u p
      have hf' : fitsW w (fun k => (σ k).val) := ⟨h1, h2, h3⟩
      simp only [dpGate, if_pos hf']
      rfl
  · refine ((Cmp.comp (Cb.const false) (Cmp.wire (fun _ : V w × Fin B => ()))).mono ?_).congr ?_
    · unfold dpCost; omega
    · intro u p
      simp only [dpGate, if_neg hf, Bool.and_false]

abbrev dpL (w c B : ℕ) : Type := ((Fin w × Fin c) ⊕ (V w × Fin B)) ⊕ V c

def dpMux (w W B c : ℕ) (u : dpK w W c ⊕ ((Fin 5 → Fin (w + 1)) × (V w × Fin B)) → Bool) :
    dpL w c B → Bool :=
  Sum.elim (Sum.elim (fun p => u (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))))
    (fun p => decide (∃ σ, u (Sum.inr (σ, p)) = true)))
    (fun z => u (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr z))))))

theorem dp_mux_cmp (w W B c : ℕ) :
    Cmp (dpK w W c ⊕ ((Fin 5 → Fin (w + 1)) × (V w × Fin B))) (dpL w c B)
      (2 ^ w * B * ((w + 1) ^ 5 + 1)) (dpMux w W B c) := by
  have h := Cmp.pair (Cmp.pair
    (Cmp.wire (ι := dpK w W c ⊕ ((Fin 5 → Fin (w + 1)) × (V w × Fin B)))
      (fun p : Fin w × Fin c => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))))
    (Cmp.ofBits (fun p : V w × Fin B =>
      Cb.bigOr (fun σ : Fin 5 → Fin (w + 1) => Cb.var (Sum.inr (σ, p))))))
    (Cmp.wire (ι := dpK w W c ⊕ ((Fin 5 → Fin (w + 1)) × (V w × Fin B)))
      (fun z : V c => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr z))))))
  refine (h.mono ?_).congr ?_
  · simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, ZMod.card, zero_add,
      mul_one]
    omega
  · intro u p
    rcases p with (p | p) | p <;> rfl

def dpPull (w c B : ℕ) (v : dpL w c B → Bool) : (V c × Fin B) ⊕ V c → Bool :=
  Sum.elim (untab (fun lam : V c => tab (fun p => v (Sum.inl (Sum.inr p)))
    ((mat (fun p => v (Sum.inl (Sum.inl p)))).mulVec lam))) (fun z => v (Sum.inr z))

theorem dp_pull_cmp (w c B : ℕ) :
    Cmp (dpL w c B) ((V c × Fin B) ⊕ V c) (tcost w c B) (dpPull w c B) := by
  have h := Cmp.pair (Cmp.sel (ι := dpL w c B) Sum.inl (cmp_pull w c B))
    (Cmp.wire (ι := dpL w c B) (fun z : V c => Sum.inr z))
  refine (h.mono (by omega)).congr ?_
  intro v p
  rcases p with p | p <;> rfl

theorem dp_pull_inl (w c B : ℕ) (X : dpL w c B → Bool) (z : V c) (j : Fin B) :
    dpPull w c B X (Sum.inl (z, j)) =
      X (Sum.inl (Sum.inr ((mat (fun p => X (Sum.inl (Sum.inl p)))).mulVec z, j))) :=
  getLsbD_bv _ j

def dpFin (c B : ℕ) (ec : Fin (2 ^ c) ≃ V c) (v : (V c × Fin B) ⊕ V c → Bool) :
    Fin (2 ^ c) × Fin B → Bool :=
  fun p => v (Sum.inr (ec p.1)) && v (Sum.inl (ec p.1, p.2))

theorem dp_fin_cmp (c B : ℕ) (ec : Fin (2 ^ c) ≃ V c) :
    Cmp ((V c × Fin B) ⊕ V c) (Fin (2 ^ c) × Fin B) (2 ^ c * B) (dpFin c B ec) := by
  have h := Cmp.ofBits (ι := (V c × Fin B) ⊕ V c) (F := dpFin c B ec)
    (fun p => Cb.and (Cb.var (Sum.inr (ec p.1))) (Cb.var (Sum.inl (ec p.1, p.2))))
  refine h.mono ?_
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

theorem dp_gate_eq (w W B c : ℕ) (δ : Fin 5 → ℕ) (hf : fitsW w δ) (u : dpK w W c → Bool)
    (hu : ∀ k (i : Fin (w + 1)), u (Sum.inl (k, i)) = decide (δ k = i.val)) (p : V w × Fin B) :
    decide (∃ σ, dpGate w W B c σ u p = true) =
      dpOut w W B δ (fun e => u (Sum.inr (Sum.inl e)))
        (fun e => u (Sum.inr (Sum.inr (Sum.inl e)))) p := by
  have hδ : ∀ k, δ k < w + 1 := by
    obtain ⟨h1, h2, h3⟩ := hf
    intro k; fin_cases k <;> simp <;> omega
  have hsel : ∀ σ : Fin 5 → Fin (w + 1), dpSel σ u = true ↔ (fun k => (σ k).val) = δ := by
    intro σ
    simp only [dpSel, hu, decide_eq_true_eq]
    constructor
    · intro h; funext k; exact (h k).symm
    · intro h k; rw [← h]
  have hfs : fitsW w (fun k => ((⟨δ k, hδ k⟩ : Fin (w + 1))).val) := hf
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    simp only [dpGate, Bool.and_eq_true] at hσ
    obtain ⟨h1, h2⟩ := hσ
    have e := (hsel σ).mp h1
    rw [e, if_pos hf] at h2
    exact h2
  · intro h
    refine ⟨fun k => ⟨δ k, hδ k⟩, ?_⟩
    have e1 : dpSel (fun k => (⟨δ k, hδ k⟩ : Fin (w + 1))) u = true := (hsel _).mpr rfl
    simp only [dpGate, e1, Bool.true_and]
    rw [if_pos hfs]
    exact h

def dpCtl {a b c m t : ℕ} (dims : (In0 a b c m t → Bool) → Fin 5 → ℕ)
    (FF GG : (In0 a b c m t → Bool) → V (wOf a b c) × Fin (WOf a b c t) → Bool)
    (EE : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin c → Bool)
    (CZ : (In0 a b c m t → Bool) → V c → Bool) (v : In0 a b c m t → Bool) :
    dpK (wOf a b c) (WOf a b c t) c → Bool :=
  Sum.elim (fun p => decide (dims v p.1 = p.2.val))
    (Sum.elim (FF v) (Sum.elim (GG v) (Sum.elim (EE v) (CZ v))))

def dpAll {a b c m t : ℕ} (ec : Fin (2 ^ c) ≃ V c) (dims : (In0 a b c m t → Bool) → Fin 5 → ℕ)
    (FF GG : (In0 a b c m t → Bool) → V (wOf a b c) × Fin (WOf a b c t) → Bool)
    (EE : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin c → Bool)
    (CZ : (In0 a b c m t → Bool) → V c → Bool) (v : In0 a b c m t → Bool) :
    Fin (2 ^ c) × Fin (a + b + 2 * t + 1) → Bool :=
  dpFin c (a + b + 2 * t + 1) ec (dpPull (wOf a b c) c (a + b + 2 * t + 1)
    (dpMux (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) c
      (Sum.elim (dpCtl dims FF GG EE CZ v)
        (fun q => dpGate (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) c q.1
          (dpCtl dims FF GG EE CZ v) q.2))))

theorem dp_all_eq {a b c m t : ℕ} (ec : Fin (2 ^ c) ≃ V c)
    (dims : (In0 a b c m t → Bool) → Fin 5 → ℕ)
    (FF GG : (In0 a b c m t → Bool) → V (wOf a b c) × Fin (WOf a b c t) → Bool)
    (EE : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin c → Bool)
    (CZ : (In0 a b c m t → Bool) → V c → Bool) (v : In0 a b c m t → Bool)
    (hf : fitsW (wOf a b c) (dims v)) (iz : Fin (2 ^ c)) (j : Fin (a + b + 2 * t + 1)) :
    dpAll ec dims FF GG EE CZ v (iz, j) = (CZ v (ec iz) &&
      dpOut (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) (dims v) (FF v) (GG v)
        ((mat (EE v)).mulVec (ec iz), j)) := by
  have hg := dp_gate_eq (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) c (dims v) hf
    (dpCtl dims FF GG EE CZ v) (fun k i => rfl) ((mat (EE v)).mulVec (ec iz), j)
  have e : dpAll ec dims FF GG EE CZ v (iz, j) = (CZ v (ec iz) &&
      decide (∃ σ, dpGate (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) c σ
        (dpCtl dims FF GG EE CZ v) ((mat (EE v)).mulVec (ec iz), j) = true)) := by
    show (dpPull _ _ _ _ (Sum.inr (ec iz)) && dpPull _ _ _ _ (Sum.inl (ec iz, j))) = _
    rw [dp_pull_inl]
    rfl
  rw [e, hg]
  rfl

theorem dp_out_val (W B : ℕ) (hB : B ≤ W) (w : ℕ) (δ : Fin 5 → ℕ) (F G : V w × Fin W → Bool)
    (t0 : V w) (j : Fin B) (cz : Bool) (n : ℕ)
    (h : BitVec.ofNat W n = if cz = true then (∑ x : V w, ∑ y : V w,
      if Std w (δ 0) (δ 1) (δ 2) (δ 3) (δ 4) x y t0 then tab F x * tab G y else 0) else 0) :
    (cz && dpOut w W B δ F G (t0, j)) = n.testBit j.val := by
  have hj : j.val < W := lt_of_lt_of_le j.isLt hB
  have e : n.testBit j.val = (BitVec.ofNat W n).getLsbD j.val := by
    rw [BitVec.getLsbD_ofNat]; simp [hj]
  rw [e, h]
  cases cz
  · simp
  · simp [dpOut]

theorem dp_cost (a b c m t S0 : ℕ)
    (hS0 : S0 ≤ 2 ^ 50 * (a + b + c + m + t + 4) ^ 20 * Phi (wOf a b c)) :
    S0 + (wOf a b c + 1) ^ 5 * dpCost (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) +
      2 ^ wOf a b c * (a + b + 2 * t + 1) * ((wOf a b c + 1) ^ 5 + 1) +
      tcost (wOf a b c) c (a + b + 2 * t + 1) + 2 ^ c * (a + b + 2 * t + 1) + 1 ≤
    2 ^ 60 * (a + b + c + m + t + 4) ^ 30 * Phi (wOf a b c) := by
  have hwd : wOf a b c = max a (max b c) := rfl
  have hw : wOf a b c ≤ a + b + c := by rw [hwd]; omega
  have hcw : c ≤ wOf a b c := by rw [hwd]; omega
  have hWd : WOf a b c t = a + b + 2 * t + 1 + wOf a b c := rfl
  have hmax : max (wOf a b c) c = wOf a b c := max_eq_left hcw
  have hΦ := two_pow_le_Phi (wOf a b c)
  have h2c : 2 ^ c ≤ 2 ^ wOf a b c := Nat.pow_le_pow_right (by norm_num) hcw
  have hQ1 : 1 ≤ 2 ^ wOf a b c := Nat.one_le_two_pow
  unfold dpCost tcost
  rw [hWd, hmax]
  generalize wOf a b c = w at *
  generalize Phi w = Φ at *
  generalize 2 ^ w = Q at *
  generalize hP : a + b + c + m + t + 4 = P at *
  have hP1 : 1 ≤ P := by omega
  have hw1 : w + 1 ≤ P := by omega
  have hK : a + b + 2 * t + 1 + w + w + 1 ≤ 3 * P := by omega
  have hB : a + b + 2 * t + 1 ≤ 2 * P := by omega
  have hB1 : a + b + 2 * t + 1 + 1 ≤ 2 * P := by omega
  have hwc : w + c + 2 ≤ 2 * P := by omega
  have hpow : ∀ i, i ≤ 30 → P ^ i * Φ ≤ P ^ 30 * Φ := fun i hi =>
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hP1 hi)
  have hΦ1 : 1 ≤ Φ := le_trans hQ1 hΦ
  have z0 := hpow 0 (by norm_num)
  have z1 := hpow 1 (by norm_num)
  have z5 := hpow 5 (by norm_num)
  have z6 := hpow 6 (by norm_num)
  have z8 := hpow 8 (by norm_num)
  have z20 := hpow 20 (by norm_num)
  have p5 : P ^ 5 ≤ P ^ 5 * Φ := Nat.le_mul_of_pos_right _ hΦ1
  have e2 : (w + 1) ^ 5 * (6 + 2 ^ 30 * (a + b + 2 * t + 1 + w + w + 1) ^ 3 * Φ +
      Q * (a + b + 2 * t + 1)) ≤ 6 * P ^ 5 + 2 ^ 30 * 27 * (P ^ 8 * Φ) + 2 * (P ^ 6 * Φ) := by
    calc _ ≤ P ^ 5 * (6 + 2 ^ 30 * (3 * P) ^ 3 * Φ + Φ * (2 * P)) := by gcongr
      _ = _ := by ring
  have e3 : Q * (a + b + 2 * t + 1) * ((w + 1) ^ 5 + 1) ≤ 4 * (P ^ 6 * Φ) := by
    calc _ ≤ Φ * (2 * P) * (P ^ 5 + P ^ 5) := by
          gcongr
          exact Nat.one_le_pow _ _ (by omega)
      _ = _ := by ring
  have e4 : 2 ^ 9 * (w + c + 2) ^ 4 * (a + b + 2 * t + 1 + 1) * Q ≤ 2 ^ 14 * (P ^ 5 * Φ) := by
    calc _ ≤ 2 ^ 9 * (2 * P) ^ 4 * (2 * P) * Φ := by gcongr
      _ = _ := by ring
  have e5 : 2 ^ c * (a + b + 2 * t + 1) ≤ 2 * (P ^ 1 * Φ) := by
    calc _ ≤ Φ * (2 * P) := Nat.mul_le_mul (le_trans h2c hΦ) hB
      _ = _ := by ring
  have e6 : 2 ^ 50 * P ^ 20 * Φ = 2 ^ 50 * (P ^ 20 * Φ) := by ring
  have e7 : 2 ^ 60 * P ^ 30 * Φ = 2 ^ 60 * (P ^ 30 * Φ) := by ring
  have e8 : P ^ 0 * Φ = Φ := by ring
  rw [e7]
  rw [e6] at hS0
  omega

theorem main_of (hsh : ShapeHyp) (hct : CtlHyp) : (∀ (a b c m t : Nat),
  let F := ZMod 2
  let X := Fin a → F
  let Y := Fin b → F
  let Z := Fin c → F
  let N := a+b+c
  let w := max a (max b c)
  let inputs := m*(N+1)+(2^a+2^b)*t
  let bitsOut := a+b+2*t+1
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (answer : Fin (2^c) → Fin bitsOut → Fin (inputs+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.output = (answer 0 0).val ∧ C.size ≤ 2^60*(N+m+t+4)^30*2^(w % 2)*7^(w/2) ∧
    ∀ (H : Fin m → X × Y × Z) (rhs : Fin m → F)
      (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t)),
      let pack := fun (s : Nat) (v : Fin s → F) => List.ofFn (fun j : Fin s => decide (v j ≠ 0))
      let bits := (List.finRange m).flatMap (fun i =>
        pack a (H i).1 ++ pack b (H i).2.1 ++ pack c (H i).2.2 ++ [decide (rhs i ≠ 0)]) ++
        (List.finRange (2^a)).flatMap (fun ix => List.ofFn (fun j : Fin t => (f ix).val.testBit j.val)) ++
        (List.finRange (2^b)).flatMap (fun iy => List.ofFn (fun j : Fin t => (g iy).val.testBit j.val))
      let decode := fun (s v : Nat) (j : Fin s) => (if v.testBit j.val then 1 else 0 : F)
      let readWire := fun n : Fin (inputs+C.size) => (C.wires bits).getD n.val false
      let total := fun iz : Fin (2^c) =>
        ∑ ix : Fin (2^a), ∑ iy : Fin (2^b),
          if ∀ i, dotProduct (H i).1 (decode a ix.val) + dotProduct (H i).2.1 (decode b iy.val) +
            dotProduct (H i).2.2 (decode c iz.val) = rhs i then (f ix).val*(g iy).val else 0
      ∀ iz j, readWire (answer iz j) = (total iz).testBit j.val) := by
  intro a b c m t
  obtain ⟨ea, hea⟩ := vecEquiv_exists a
  obtain ⟨eb, heb⟩ := vecEquiv_exists b
  obtain ⟨ec, hec⟩ := vecEquiv_exists c
  obtain ⟨S0, dims, FF, GG, EE, CZ, hS0, hctl, hsem⟩ := hct a b c m t ea eb
  have hBW : wOf a b c + (a + b + 2 * t + 1) ≤ WOf a b c t := by unfold WOf; omega
  have hB := Cmp.keep (Cmp.piU (fun σ => dp_gate_cmp (wOf a b c) (WOf a b c t)
    (a + b + 2 * t + 1) c hsh hBW σ))
  have htop0 := Cmp.comp (Cmp.comp (Cmp.comp (Cmp.comp hctl hB) (dp_mux_cmp _ _ _ _))
    (dp_pull_cmp _ _ _)) (dp_fin_cmp c (a + b + 2 * t + 1) ec)
  have htop : Cmp (In0 a b c m t) (Fin (2 ^ c) × Fin (a + b + 2 * t + 1))
      (S0 + (wOf a b c + 1) ^ 5 * dpCost (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) +
        2 ^ wOf a b c * (a + b + 2 * t + 1) * ((wOf a b c + 1) ^ 5 + 1) +
        tcost (wOf a b c) c (a + b + 2 * t + 1) + 2 ^ c * (a + b + 2 * t + 1))
      (dpAll ec dims FF GG EE CZ) := by
    refine (htop0.mono ?_).congr ?_
    · simp only [Fintype.card_fun, Fintype.card_fin]
      exact le_refl _
    · intro v p; rfl
  have hws : ∀ j : In0 a b c m t,
      (Sum.elim (fun p : Fin m × Fin (a + b + c + 1) => p.1.val * (a + b + c + 1) + p.2.val)
        (Sum.elim (fun p : Fin (2 ^ a) × Fin t => m * (a + b + c + 1) + p.1.val * t + p.2.val)
          (fun p : Fin (2 ^ b) × Fin t => m * (a + b + c + 1) + 2 ^ a * t + p.1.val * t + p.2.val))
        j) < m * (a + b + c + 1) + (2 ^ a + 2 ^ b) * t := by
    intro j
    rcases j with p | p | p
    · have := fin_idx_lt p.1.val m p.2.val (a + b + c + 1) p.1.isLt p.2.isLt
      simp only [Sum.elim_inl]
      omega
    · have := fin_idx_lt p.1.val (2 ^ a) p.2.val t p.1.isLt p.2.isLt
      simp only [Sum.elim_inr, Sum.elim_inl]
      rw [Nat.add_mul]; omega
    · have := fin_idx_lt p.1.val (2 ^ b) p.2.val t p.1.isLt p.2.isLt
      simp only [Sum.elim_inr]
      rw [Nat.add_mul]; omega
  obtain ⟨gs, outs, hfan, hrb, hsize, hout, hsem2⟩ :=
    htop.extract (m * (a + b + c + 1) + (2 ^ a + 2 ^ b) * t) _
      (fun j => Nat.lt_succ_of_lt (hws j))
  dsimp only
  refine ⟨⟨gs, _⟩, fun iz j => ⟨outs (iz, j), hout _⟩, hfan, hrb _, rfl, ?_, ?_⟩
  · show gs.length ≤ _
    refine le_trans hsize (le_trans (dp_cost a b c m t S0 hS0) (le_of_eq ?_))
    unfold Phi wOf
    exact (Nat.mul_assoc _ _ _).symm
  · intro H rhs f g
    obtain ⟨hlen, h1, h2, h3⟩ := input_layout a b c m t H rhs f g _ rfl
    have hin : (fun j : In0 a b c m t => (((List.finRange m).flatMap (fun i =>
        List.ofFn (fun j : Fin a => decide ((H i).1 j ≠ 0)) ++
        List.ofFn (fun j : Fin b => decide ((H i).2.1 j ≠ 0)) ++
        List.ofFn (fun j : Fin c => decide ((H i).2.2 j ≠ 0)) ++ [decide (rhs i ≠ 0)]) ++
        (List.finRange (2 ^ a)).flatMap (fun ix =>
          List.ofFn (fun j : Fin t => (f ix).val.testBit j.val)) ++
        (List.finRange (2 ^ b)).flatMap (fun iy =>
          List.ofFn (fun j : Fin t => (g iy).val.testBit j.val))) ++ [false]).getD
        ((Sum.elim (fun p : Fin m × Fin (a + b + c + 1) => p.1.val * (a + b + c + 1) + p.2.val)
        (Sum.elim (fun p : Fin (2 ^ a) × Fin t => m * (a + b + c + 1) + p.1.val * t + p.2.val)
          (fun p : Fin (2 ^ b) × Fin t => m * (a + b + c + 1) + 2 ^ a * t + p.1.val * t + p.2.val))
        j)) false) = inpOf H rhs f g := by
      funext j
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hws j)]
      rcases j with p | p | p
      · exact h1 p.1 p.2
      · exact h2 p.1 p.2
      · exact h3 p.1 p.2
    obtain ⟨hfit, hval⟩ := hsem H rhs f g
    have hea' : ∀ ix, ea ix = (fun j : Fin a => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
      fun ix => funext (hea ix)
    have heb' : ∀ ix, eb ix = (fun j : Fin b => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
      fun ix => funext (heb ix)
    have hec' : ∀ ix, ec ix = (fun j : Fin c => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
      fun ix => funext (hec ix)
    intro iz j
    have e2 := hsem2 (outs (0, 0)) _ hlen (iz, j)
    rw [hin] at e2
    show (PEqualNP.CircuitLowerBounds.Circuit.wires _ _).getD (outs (iz, j)) false = _
    rw [e2, dp_all_eq ec dims FF GG EE CZ _ hfit iz j,
      dp_out_val (WOf a b c t) (a + b + 2 * t + 1) (by unfold WOf; omega) _ _ _ _ _ j _ _
        (hval (ec iz))]
    simp only [hea', heb', hec']

end PEqualNP.Outside.L_lib_838

namespace PEqualNP.Outside.L_lib_838

theorem shape_hyp : ShapeHyp := fun w W B q d r1 r2 r3 h1 h2 h3 hB =>
  shape_solver w W B q d r1 r2 r3 h1 h2 h3 hB

theorem ctl_hyp : CtlHyp := fun a b c m t ea eb => ctl_spec a b c m t ea eb

theorem main : (∀ (a b c m t : Nat),
  let F := ZMod 2
  let X := Fin a → F
  let Y := Fin b → F
  let Z := Fin c → F
  let N := a+b+c
  let w := max a (max b c)
  let inputs := m*(N+1)+(2^a+2^b)*t
  let bitsOut := a+b+2*t+1
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (answer : Fin (2^c) → Fin bitsOut → Fin (inputs+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.output = (answer 0 0).val ∧ C.size ≤ 2^60*(N+m+t+4)^30*2^(w % 2)*7^(w/2) ∧
    ∀ (H : Fin m → X × Y × Z) (rhs : Fin m → F)
      (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t)),
      let pack := fun (s : Nat) (v : Fin s → F) => List.ofFn (fun j : Fin s => decide (v j ≠ 0))
      let bits := (List.finRange m).flatMap (fun i =>
        pack a (H i).1 ++ pack b (H i).2.1 ++ pack c (H i).2.2 ++ [decide (rhs i ≠ 0)]) ++
        (List.finRange (2^a)).flatMap (fun ix => List.ofFn (fun j : Fin t => (f ix).val.testBit j.val)) ++
        (List.finRange (2^b)).flatMap (fun iy => List.ofFn (fun j : Fin t => (g iy).val.testBit j.val))
      let decode := fun (s v : Nat) (j : Fin s) => (if v.testBit j.val then 1 else 0 : F)
      let readWire := fun n : Fin (inputs+C.size) => (C.wires bits).getD n.val false
      let total := fun iz : Fin (2^c) =>
        ∑ ix : Fin (2^a), ∑ iy : Fin (2^b),
          if ∀ i, dotProduct (H i).1 (decode a ix.val) + dotProduct (H i).2.1 (decode b iy.val) +
            dotProduct (H i).2.2 (decode c iz.val) = rhs i then (f ix).val*(g iy).val else 0
      ∀ iz j, readWire (answer iz j) = (total iz).testBit j.val) := main_of shape_hyp ctl_hyp

end PEqualNP.Outside.L_lib_838

theorem PEqualNP.Outside.L_lib_838 : (∀ (a b c m t : Nat),
  let F := ZMod 2
  let X := Fin a → F
  let Y := Fin b → F
  let Z := Fin c → F
  let N := a+b+c
  let w := max a (max b c)
  let inputs := m*(N+1)+(2^a+2^b)*t
  let bitsOut := a+b+2*t+1
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (answer : Fin (2^c) → Fin bitsOut → Fin (inputs+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.output = (answer 0 0).val ∧ C.size ≤ 2^60*(N+m+t+4)^30*2^(w % 2)*7^(w/2) ∧
    ∀ (H : Fin m → X × Y × Z) (rhs : Fin m → F)
      (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t)),
      let pack := fun (s : Nat) (v : Fin s → F) => List.ofFn (fun j : Fin s => decide (v j ≠ 0))
      let bits := (List.finRange m).flatMap (fun i =>
        pack a (H i).1 ++ pack b (H i).2.1 ++ pack c (H i).2.2 ++ [decide (rhs i ≠ 0)]) ++
        (List.finRange (2^a)).flatMap (fun ix => List.ofFn (fun j : Fin t => (f ix).val.testBit j.val)) ++
        (List.finRange (2^b)).flatMap (fun iy => List.ofFn (fun j : Fin t => (g iy).val.testBit j.val))
      let decode := fun (s v : Nat) (j : Fin s) => (if v.testBit j.val then 1 else 0 : F)
      let readWire := fun n : Fin (inputs+C.size) => (C.wires bits).getD n.val false
      let total := fun iz : Fin (2^c) =>
        ∑ ix : Fin (2^a), ∑ iy : Fin (2^b),
          if ∀ i, dotProduct (H i).1 (decode a ix.val) + dotProduct (H i).2.1 (decode b iy.val) +
            dotProduct (H i).2.2 (decode c iz.val) = rhs i then (f ix).val*(g iy).val else 0
      ∀ iz j, readWire (answer iz j) = (total iz).testBit j.val) :=
  PEqualNP.Outside.L_lib_838.main
