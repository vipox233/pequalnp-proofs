import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_958_aux
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

def kerSlot {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (s : Fin K)
    (j : Fin N) : Bool :=
  decide (∃ q : Fin N, pv R q = false ∧ cntN R q = s.val ∧
    xor (decide (j = q)) (R (cl m j, cl m q)) = true)

def deadSlot {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (s : Fin K) :
    Bool :=
  decide (¬ ∃ q : Fin N, pv R q = false ∧ cntN R q = s.val)

def kerPt {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (lam : V K) : V N :=
  fun j => (if R (cl m j, rc m N) then 1 else 0) +
    ∑ s : Fin K, lam s * (if kerSlot K R s j then 1 else 0)

def nx {a b c : ℕ} (j : Fin a) : Fin (a + b + c) := ⟨j.val, by omega⟩
def ny {a b c : ℕ} (j : Fin b) : Fin (a + b + c) := ⟨a + j.val, by omega⟩
def nz {a b c : ℕ} (j : Fin c) : Fin (a + b + c) := ⟨a + b + j.val, by omega⟩

def LrBits {m N d : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (e : Fin d → Fin N) : Fin d × Fin (K + 1) → Bool := fun p =>
  if h : p.2.val < K then rowSlot K R ⟨p.2.val, h⟩ (cl m (e p.1)) else false

def LnBits {m N d : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (e : Fin d → Fin N) : Fin d × Fin (K + 1) → Bool := fun p =>
  if h : p.2.val < K then kerSlot K R ⟨p.2.val, h⟩ (e p.1) else R (cl m (e p.1), rc m N)

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

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

def toZ (b : Bool) : ZMod 2 := if b then 1 else 0
def ofZ (z : ZMod 2) : Bool := decide (z = 1)

theorem toZ_ofZ (z : ZMod 2) : toZ (ofZ z) = z := by
  fin_cases z <;> rfl
theorem ofZ_toZ (b : Bool) : ofZ (toZ b) = b := by
  cases b <;> rfl
theorem toZ_xor (a b : Bool) : toZ (xor a b) = toZ a + toZ b := by
  cases a <;> cases b <;> rfl
theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by
  cases a <;> cases b <;> rfl
theorem toZ_or (a b : Bool) : toZ (a || b) = toZ a + toZ b + toZ a * toZ b := by
  cases a <;> cases b <;> rfl
theorem toZ_not (a : Bool) : toZ (!a) = 1 + toZ a := by
  cases a <;> rfl
@[simp] theorem toZ_false : toZ false = 0 := rfl
@[simp] theorem toZ_true : toZ true = 1 := rfl
theorem toZ_inj {a b : Bool} : toZ a = toZ b ↔ a = b := by
  cases a <;> cases b <;> decide
theorem toZ_eq_zero {a : Bool} : toZ a = 0 ↔ a = false := by
  cases a <;> decide
theorem toZ_eq_one {a : Bool} : toZ a = 1 ↔ a = true := by
  cases a <;> decide
theorem toZ_decide (p : Prop) [Decidable p] : toZ (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h, toZ]
theorem zsq (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl
theorem z2 (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl
theorem z01 (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl
theorem zneg (x : ZMod 2) : -x = x := by
  fin_cases x <;> rfl
theorem zsub (x y : ZMod 2) : x - y = x + y := by
  fin_cases x <;> fin_cases y <;> rfl
theorem ofZ_add (a b : ZMod 2) : ofZ (a + b) = xor (ofZ a) (ofZ b) := by
  fin_cases a <;> fin_cases b <;> rfl
theorem ofZ_mul (a b : ZMod 2) : ofZ (a * b) = (ofZ a && ofZ b) := by
  fin_cases a <;> fin_cases b <;> rfl
theorem ofZ_eq_iff (a b : ZMod 2) : ofZ a = ofZ b ↔ a = b := by
  constructor
  · intro h; rw [← toZ_ofZ a, ← toZ_ofZ b, h]
  · intro h; rw [h]
theorem mat_eq_toZ {r c : ℕ} (v : Fin r × Fin c → Bool) (i : Fin r) (j : Fin c) :
    mat v i j = toZ (v (i, j)) := rfl

theorem foldl_xor_toZ {α : Type} (L : List α) (g : α → Bool) (t0 : Bool) :
    toZ (L.foldl (fun t i => xor t (g i)) t0) = toZ t0 + (L.map (fun i => toZ (g i))).sum := by
  induction L generalizing t0 with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, toZ_xor]
    ring

theorem foldl_xor_fin {d : ℕ} (g : Fin d → Bool) (t0 : Bool) :
    toZ ((List.finRange d).foldl (fun t i => xor t (g i)) t0) = toZ t0 + ∑ i, toZ (g i) := by
  rw [foldl_xor_toZ, Fin.sum_univ_def]

theorem foldl2_xor_fin {d e : ℕ} (g : Fin d → Fin e → Bool) (t0 : Bool) :
    toZ ((List.finRange d).foldl (fun acc i => (List.finRange e).foldl
      (fun v p => xor v (g i p)) acc) t0) = toZ t0 + ∑ i, ∑ p, toZ (g i p) := by
  rw [Fin.sum_univ_def]
  generalize (List.finRange d) = L
  induction L generalizing t0 with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, foldl_xor_fin]
    ring

def dotB {d : ℕ} (a b : Fin d → Bool) : Bool :=
  (List.finRange d).foldl (fun t i => xor t (a i && b i)) false

theorem toZ_dotB {d : ℕ} (a b : Fin d → Bool) :
    toZ (dotB a b) = ∑ i, toZ (a i) * toZ (b i) := by
  unfold dotB
  rw [foldl_xor_fin]
  simp [toZ_and]

def zv {d : ℕ} (a : Fin d → Bool) : V d := fun i => toZ (a i)
def bvv {d : ℕ} (a : V d) : Fin d → Bool := fun i => ofZ (a i)

theorem zv_bvv {d : ℕ} (a : V d) : zv (bvv a) = a := by
  funext i; simp [zv, bvv, toZ_ofZ]
theorem bvv_zv {d : ℕ} (a : Fin d → Bool) : bvv (zv a) = a := by
  funext i; simp [zv, bvv, ofZ_toZ]
theorem zv_inj {d : ℕ} {a b : Fin d → Bool} : zv a = zv b ↔ a = b := by
  constructor
  · intro h; rw [← bvv_zv a, ← bvv_zv b, h]
  · intro h; rw [h]

def zvEquiv (d : ℕ) : (Fin d → Bool) ≃ V d where
  toFun := zv
  invFun := bvv
  left_inv := bvv_zv
  right_inv := zv_bvv

theorem toZ_dotB' {d : ℕ} (a b : Fin d → Bool) :
    toZ (dotB a b) = ∑ i, zv a i * zv b i := toZ_dotB a b

def GJF {D : ℕ} (R : Fin D × Fin D → Bool) : Prop :=
  (∀ p, R (p, p) = true → ∀ i, R (i, p) = decide (i = p)) ∧
  (∀ q, R (q, q) = false → ∀ j, R (q, j) = false)

theorem gj_GJF {D : ℕ} (M : Fin D × Fin D → Bool) : GJF (gj D M) :=
  ⟨gj_pivcol M, gj_zerorow M⟩

theorem GJF_term {D : ℕ} {R : Fin D × Fin D → Bool} (hR : GJF R) (i j s : Fin D) :
    toZ (R (i, j)) * toZ (R (j, s)) = (if i = j then toZ (R (j, s)) else 0) := by
  by_cases hj : R (j, j) = true
  · rw [hR.1 j hj i]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  · have hz := hR.2 j (by simpa using hj) s
    rw [hz]
    by_cases hij : i = j <;> simp [hij]

theorem GJF_idem {D : ℕ} {R : Fin D × Fin D → Bool} (hR : GJF R) :
    mat R * mat R = mat R := by
  ext i s
  rw [Matrix.mul_apply]
  simp only [mat_eq_toZ]
  rw [Finset.sum_congr rfl (fun j _ => GJF_term hR i j s)]
  simp

theorem gj_sol_iff {D : ℕ} (M : Fin D × Fin D → Bool) (v : Fin D → ZMod 2) :
    (mat (gj D M)).mulVec v = 0 ↔ (mat M).mulVec v = 0 := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv M
  constructor
  · intro h
    rw [h2, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · intro h
    rw [h1, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

theorem gj_col_zero {D : ℕ} (M : Fin D × Fin D → Bool) (c : Fin D)
    (hc : ∀ r, M (r, c) = false) (r : Fin D) : gj D M (r, c) = false := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv M
  have := congrFun (congrFun h1 r) c
  rw [Matrix.mul_apply] at this
  simp only [mat_eq_toZ, hc, toZ_false, mul_zero, Finset.sum_const_zero] at this
  exact toZ_eq_zero.1 this

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

def xb {k : ℕ} (x : Fin (2 ^ k)) : Fin k → Bool := fun i => x.val.testBit i.val

def affOn {k m : ℕ} (f : Fin (2 ^ k) → Fin m → Bool) (S : Finset (Fin (2 ^ k)))
    (l : Fin m → Bool) : Prop :=
  ∃ (a : Fin k → Bool) (b : Bool), ∀ z ∈ S,
    dotB l (f z) = xor b (dotB a (fun i => z.val.testBit i.val))

def IsPrune {k m : ℕ} (f : Fin (2 ^ k) → Fin m → Bool) (y : Fin m → Bool)
    (prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))) : Prop :=
  ∀ S x, x ∈ prune S ↔ x ∈ S ∧ ∀ l, affOn f S l → dotB l (f x) = dotB l y

def tri {k : ℕ} (x1 x2 x3 : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨x1.val ^^^ x2.val ^^^ x3.val, Nat.xor_lt_two_pow (Nat.xor_lt_two_pow x1.isLt x2.isLt) x3.isLt⟩

def Closed3 {k : ℕ} (S : Finset (Fin (2 ^ k))) : Prop :=
  ∀ x1 ∈ S, ∀ x2 ∈ S, ∀ x3 ∈ S, tri x1 x2 x3 ∈ S

theorem dotB_tri {k : ℕ} (a : Fin k → Bool) (x1 x2 x3 : Fin (2 ^ k)) :
    dotB a (fun i => (tri x1 x2 x3).val.testBit i.val) =
      xor (xor (dotB a (fun i => x1.val.testBit i.val)) (dotB a (fun i => x2.val.testBit i.val)))
        (dotB a (fun i => x3.val.testBit i.val)) := by
  rw [← toZ_inj]
  simp only [toZ_xor, toZ_dotB, tri, Nat.testBit_xor, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem prune_sub {k m : ℕ} {f : Fin (2 ^ k) → Fin m → Bool} {y : Fin m → Bool}
    {prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))} (hp : IsPrune f y prune)
    (S : Finset (Fin (2 ^ k))) : prune S ⊆ S := by
  intro x hx
  exact ((hp S x).1 hx).1

theorem affOn_mono {k m : ℕ} {f : Fin (2 ^ k) → Fin m → Bool} {S T : Finset (Fin (2 ^ k))}
    (hST : S ⊆ T) {l : Fin m → Bool} (h : affOn f T l) : affOn f S l := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, b, fun z hz => hab z (hST hz)⟩

theorem prune_mono {k m : ℕ} {f : Fin (2 ^ k) → Fin m → Bool} {y : Fin m → Bool}
    {prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))} (hp : IsPrune f y prune)
    {S T : Finset (Fin (2 ^ k))} (hST : S ⊆ T) : prune S ⊆ prune T := by
  intro x hx
  obtain ⟨h1, h2⟩ := (hp S x).1 hx
  exact (hp T x).2 ⟨hST h1, fun l hl => h2 l (affOn_mono hST hl)⟩

theorem closed_univ {k : ℕ} : Closed3 (Finset.univ : Finset (Fin (2 ^ k))) := by
  intro _ _ _ _ _ _; exact Finset.mem_univ _

theorem closed_prune {k m : ℕ} {f : Fin (2 ^ k) → Fin m → Bool} {y : Fin m → Bool}
    {prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))} (hp : IsPrune f y prune)
    {S : Finset (Fin (2 ^ k))} (hS : Closed3 S) : Closed3 (prune S) := by
  intro x1 h1 x2 h2 x3 h3
  obtain ⟨m1, q1⟩ := (hp S x1).1 h1
  obtain ⟨m2, q2⟩ := (hp S x2).1 h2
  obtain ⟨m3, q3⟩ := (hp S x3).1 h3
  refine (hp S _).2 ⟨hS x1 m1 x2 m2 x3 m3, ?_⟩
  intro l hl
  obtain ⟨a, b, hab⟩ := hl
  rw [hab _ (hS x1 m1 x2 m2 x3 m3), dotB_tri]
  have e1 := hab x1 m1
  have e2 := hab x2 m2
  have e3 := hab x3 m3
  rw [q1 l ⟨a, b, hab⟩] at e1
  rw [q2 l ⟨a, b, hab⟩] at e2
  rw [q3 l ⟨a, b, hab⟩] at e3
  revert e1 e2 e3
  cases dotB l y <;> cases b <;> cases dotB a (fun i => x1.val.testBit i.val) <;>
    cases dotB a (fun i => x2.val.testBit i.val) <;>
    cases dotB a (fun i => x3.val.testBit i.val) <;> decide

theorem tri_cancel {k : ℕ} (x t s : Fin (2 ^ k)) : tri (tri x t s) t s = x := by
  apply Fin.ext
  simp only [tri]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.val.testBit i <;> cases t.val.testBit i <;> cases s.val.testBit i <;> rfl

theorem tri_swap {k : ℕ} (x t s : Fin (2 ^ k)) : tri (tri x t s) x t = s := by
  apply Fin.ext
  simp only [tri]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.val.testBit i <;> cases t.val.testBit i <;> cases s.val.testBit i <;> rfl

theorem halving {k : ℕ} {S T : Finset (Fin (2 ^ k))} (hTS : T ⊆ S) (hT : Closed3 T)
    (hS : Closed3 S) (hne : T ≠ S) : 2 * T.card ≤ S.card := by
  classical
  obtain ⟨s, hsS, hsT⟩ : ∃ s ∈ S, s ∉ T := by
    by_contra hcon
    push_neg at hcon
    exact hne (Finset.Subset.antisymm hTS hcon)
  rcases Finset.eq_empty_or_nonempty T with hTe | ⟨t0, ht0⟩
  · rw [hTe]; simp
  have h1 : T.card ≤ (S \ T).card := by
    apply Finset.card_le_card_of_injOn (fun x => tri x t0 s)
    · intro x hx
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hx ⊢
      refine ⟨hS x (hTS hx) t0 (hTS ht0) s hsS, ?_⟩
      intro hin
      apply hsT
      have := hT _ hin x hx t0 ht0
      rwa [tri_swap] at this
    · intro x _ x' _ hxx
      have := congrArg (fun z => tri z t0 s) hxx
      simp only [tri_cancel] at this
      exact this
  have h2 := Finset.card_sdiff_add_card_eq_card hTS
  omega

theorem iter_dich {k m : ℕ} {f : Fin (2 ^ k) → Fin m → Bool} {y : Fin m → Bool}
    {prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))} (hp : IsPrune f y prune) :
    ∀ n : ℕ, Closed3 (prune^[n] Finset.univ) ∧
      (prune (prune^[n] Finset.univ) = prune^[n] Finset.univ ∨
        2 ^ n * (prune^[n] Finset.univ).card ≤ 2 ^ k) := by
  intro n
  induction n with
  | zero =>
    refine ⟨closed_univ, Or.inr ?_⟩
    simp
  | succ n ih =>
    obtain ⟨hc, hd⟩ := ih
    have hc' : Closed3 (prune^[n + 1] Finset.univ) := by
      rw [Function.iterate_succ_apply']
      exact closed_prune hp hc
    refine ⟨hc', ?_⟩
    rw [Function.iterate_succ_apply']
    by_cases heq : prune (prune^[n] Finset.univ) = prune^[n] Finset.univ
    · left; rw [heq, heq]
    · right
      rcases hd with hd | hd
      · exact absurd hd heq
      have := halving (prune_sub hp _) (closed_prune hp hc) hc heq
      calc 2 ^ (n + 1) * (prune (prune^[n] Finset.univ)).card
          = 2 ^ n * (2 * (prune (prune^[n] Finset.univ)).card) := by ring
        _ ≤ 2 ^ n * (prune^[n] Finset.univ).card := Nat.mul_le_mul_left _ this
        _ ≤ 2 ^ k := hd

theorem prune_empty {k m : ℕ} {f : Fin (2 ^ k) → Fin m → Bool} {y : Fin m → Bool}
    {prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))} (hp : IsPrune f y prune) :
    prune ∅ = ∅ :=
  Finset.subset_empty.1 (prune_sub hp ∅)

theorem fixed_final {k m : ℕ} {f : Fin (2 ^ k) → Fin m → Bool} {y : Fin m → Bool}
    {prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))} (hp : IsPrune f y prune) :
    prune (prune^[k + 1] Finset.univ) = prune^[k + 1] Finset.univ := by
  rcases (iter_dich hp (k + 1)).2 with h | h
  · exact h
  · have h2 : (prune^[k + 1] Finset.univ).card = 0 := by
      by_contra hne
      have : 2 ^ (k + 1) * 1 ≤ 2 ^ (k + 1) * (prune^[k + 1] Finset.univ).card :=
        Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.2 hne)
      have h3 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    rw [Finset.card_eq_zero] at h2
    rw [h2, prune_empty hp]

theorem greatest {k m : ℕ} {f : Fin (2 ^ k) → Fin m → Bool} {y : Fin m → Bool}
    {prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))} (hp : IsPrune f y prune)
    (V : Finset (Fin (2 ^ k))) (hV : prune V = V) : ∀ n, V ⊆ prune^[n] Finset.univ := by
  intro n
  induction n with
  | zero => exact Finset.subset_univ _
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hV]
    exact prune_mono hp ih

theorem foldl_range_iter {α : Type} (g : α → α) (n : ℕ) (S : α) :
    (List.range n).foldl (fun D _ => g D) S = g^[n] S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Function.iterate_succ_apply']
    rfl

theorem fiber_fixed {k m : ℕ} {f : Fin (2 ^ k) → Fin m → Bool} {y : Fin m → Bool}
    {prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))} (hp : IsPrune f y prune) :
    prune (Finset.univ.filter (fun x => f x = y)) = Finset.univ.filter (fun x => f x = y) := by
  apply Finset.Subset.antisymm (prune_sub hp _)
  intro x hx
  refine (hp _ x).2 ⟨hx, fun l _ => ?_⟩
  rw [(Finset.mem_filter.1 hx).2]

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

def sgnZ (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

theorem sgnZ_add (a b : ZMod 2) : sgnZ (a + b) = sgnZ a * sgnZ b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem sgnZ_zero : sgnZ 0 = 1 := rfl
theorem sgnZ_one : sgnZ 1 = -1 := rfl

def evalQ {k : ℕ} (c : Bool) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool) (u : V k) : ZMod 2 :=
  toZ c + ∑ a, toZ (α a) * u a + ∑ a, ∑ b, toZ (γ (a, b)) * u a * u b

def gsum {k : ℕ} (c : Bool) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool) : ℤ :=
  ∑ u : V k, sgnZ (evalQ c α γ u)

theorem flip_sum {k : ℕ} (g : V k → ℤ) (i : Fin k) :
    2 * ∑ u, g u = ∑ u, (g (Function.update u i 0) + g (Function.update u i 1)) := by
  have h1 : ∑ u, g (u + Pi.single i 1) = ∑ u, g u :=
    Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ (fun u => rfl)
  rw [two_mul]
  nth_rewrite 2 [← h1]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rcases z01 (u i) with h | h
  · have e0 : Function.update u i 0 = u := by
      funext a
      by_cases ha : a = i
      · subst ha; simp [h]
      · simp [ha]
    have e1 : Function.update u i 1 = u + Pi.single i 1 := by
      funext a
      by_cases ha : a = i
      · subst ha; simp [h]
      · simp [ha]
    rw [e0, e1]
  · have e0 : Function.update u i 0 = u + Pi.single i 1 := by
      funext a
      by_cases ha : a = i
      · subst ha; simp [h]; rfl
      · simp [ha]
    have e1 : Function.update u i 1 = u := by
      funext a
      by_cases ha : a = i
      · subst ha; simp [h]
      · simp [ha]
    rw [e0, e1, add_comm]

theorem flip_sum2 {k : ℕ} (g : V k → ℤ) (i j : Fin k) (hij : i ≠ j) :
    4 * ∑ u, g u = ∑ u, (g (Function.update (Function.update u i 0) j 0) +
      g (Function.update (Function.update u i 0) j 1) +
      g (Function.update (Function.update u i 1) j 0) +
      g (Function.update (Function.update u i 1) j 1)) := by
  have h4 : (4 : ℤ) = 2 * 2 := by norm_num
  rw [h4, mul_assoc, flip_sum g i]
  rw [flip_sum (fun u => g (Function.update u i 0) + g (Function.update u i 1)) j]
  apply Finset.sum_congr rfl
  intro u _
  rw [Function.update_comm (Ne.symm hij) _ _ u, Function.update_comm (Ne.symm hij) _ _ u,
    Function.update_comm (Ne.symm hij) _ _ u, Function.update_comm (Ne.symm hij) _ _ u]
  ring

theorem evalQ_add {k : ℕ} (c : Bool) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool) (v w : V k) :
    evalQ c α γ (v + w) = evalQ c α γ v + evalQ c α γ w + toZ c +
      ∑ a, ∑ b, toZ (γ (a, b)) * (v a * w b + w a * v b) := by
  have h1 : ∑ a, toZ (α a) * (v + w) a = ∑ a, toZ (α a) * v a + ∑ a, toZ (α a) * w a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Pi.add_apply]
    ring
  have h2 : ∑ a, ∑ b, toZ (γ (a, b)) * (v + w) a * (v + w) b =
      ∑ a, ∑ b, toZ (γ (a, b)) * v a * v b + ∑ a, ∑ b, toZ (γ (a, b)) * w a * w b +
      ∑ a, ∑ b, toZ (γ (a, b)) * (v a * w b + w a * v b) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    simp only [Pi.add_apply]
    ring
  unfold evalQ
  rw [h1, h2]
  have hc := z2 (toZ c)
  linear_combination (-1 : ZMod 2) * hc

def sv2 {k : ℕ} (i j : Fin k) (x y : ZMod 2) : V k :=
  fun a => (if a = i then x else 0) + (if a = j then y else 0)

theorem evalQ_sv2 {k : ℕ} (c : Bool) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool)
    (i j : Fin k) (x y : ZMod 2) :
    evalQ c α γ (sv2 i j x y) = toZ c + (toZ (α i) * x + toZ (α j) * y) +
      ((toZ (γ (i, i)) * x * x + toZ (γ (i, j)) * x * y) +
       (toZ (γ (j, i)) * y * x + toZ (γ (j, j)) * y * y)) := by
  unfold evalQ sv2
  congr 1
  · congr 1
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  · simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

theorem cross_sv2 {k : ℕ} (γ : Fin k × Fin k → Bool) (v : V k) (i j : Fin k) (x y : ZMod 2) :
    ∑ a, ∑ b, toZ (γ (a, b)) * (v a * sv2 i j x y b + sv2 i j x y a * v b) =
      x * ∑ a, v a * (toZ (γ (a, i)) + toZ (γ (i, a))) +
      y * ∑ a, v a * (toZ (γ (a, j)) + toZ (γ (j, a))) := by
  have e : ∀ a, ∑ b, toZ (γ (a, b)) * (v a * sv2 i j x y b + sv2 i j x y a * v b) =
      v a * (toZ (γ (a, i)) * x + toZ (γ (a, j)) * y) +
      ((if a = i then x else 0) + (if a = j then y else 0)) * ∑ b, toZ (γ (a, b)) * v b := by
    intro a
    unfold sv2
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, add_mul, ite_mul, zero_mul]
    rw [Finset.mul_sum, Finset.mul_sum]
    by_cases hi : a = i <;> by_cases hj : a = j <;> simp [hi, hj] <;> ring_nf
  rw [Finset.sum_congr rfl (fun a _ => e a)]
  simp only [Finset.sum_add_distrib, add_mul, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have s1 : ∑ b, x * (toZ (γ (i, b)) * v b) = ∑ a, x * (v a * toZ (γ (i, a))) := by
    apply Finset.sum_congr rfl; intro a _; ring
  have s2 : ∑ b, y * (toZ (γ (j, b)) * v b) = ∑ a, y * (v a * toZ (γ (j, a))) := by
    apply Finset.sum_congr rfl; intro a _; ring
  have s3 : ∑ a, v a * (toZ (γ (a, i)) * x) = ∑ a, x * (v a * toZ (γ (a, i))) := by
    apply Finset.sum_congr rfl; intro a _; ring
  have s4 : ∑ a, v a * (toZ (γ (a, j)) * y) = ∑ a, y * (v a * toZ (γ (a, j))) := by
    apply Finset.sum_congr rfl; intro a _; ring
  rw [s1, s2, s3, s4]
  ring

theorem split2 {k : ℕ} (c : Bool) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool)
    (i j : Fin k) (hij : i ≠ j) (u : V k) (x y : ZMod 2) :
    evalQ c α γ (Function.update (Function.update u i x) j y) =
      evalQ c α γ (Function.update (Function.update u i 0) j 0) +
      x * (toZ (α i) + toZ (γ (i, i)) +
        ∑ a, Function.update (Function.update u i 0) j 0 a * (toZ (γ (a, i)) + toZ (γ (i, a)))) +
      y * (toZ (α j) + toZ (γ (j, j)) +
        ∑ a, Function.update (Function.update u i 0) j 0 a * (toZ (γ (a, j)) + toZ (γ (j, a)))) +
      x * y * (toZ (γ (i, j)) + toZ (γ (j, i))) := by
  have hv : Function.update (Function.update u i x) j y =
      Function.update (Function.update u i 0) j 0 + sv2 i j x y := by
    funext a
    simp only [Pi.add_apply, sv2]
    by_cases ha : a = j
    · subst ha; simp [Ne.symm hij]
    · by_cases hb : a = i
      · subst hb; simp [ha]
      · simp [ha, hb]
  rw [hv, evalQ_add, evalQ_sv2, cross_sv2]
  have hx := zsq x
  have hy := zsq y
  have hc := z2 (toZ c)
  have e1 : toZ (γ (i, i)) * x * x = toZ (γ (i, i)) * x := by rw [mul_assoc, hx]
  have e2 : toZ (γ (j, j)) * y * y = toZ (γ (j, j)) * y := by rw [mul_assoc, hy]
  rw [e1, e2]
  linear_combination hc

theorem split1 {k : ℕ} (c : Bool) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool)
    (i : Fin k) (u : V k) (x : ZMod 2) :
    evalQ c α γ (Function.update u i x) =
      evalQ c α γ (Function.update u i 0) +
      x * (toZ (α i) + toZ (γ (i, i)) +
        ∑ a, Function.update u i 0 a * (toZ (γ (a, i)) + toZ (γ (i, a)))) := by
  have hv : Function.update u i x = Function.update u i 0 + sv2 i i x 0 := by
    funext a
    simp only [Pi.add_apply, sv2]
    by_cases ha : a = i
    · subst ha; simp
    · simp [ha]
  rw [hv, evalQ_add, evalQ_sv2, cross_sv2]
  have hx := zsq x
  have hc := z2 (toZ c)
  have e1 : toZ (γ (i, i)) * x * x = toZ (γ (i, i)) * x := by rw [mul_assoc, hx]
  rw [e1]
  simp only [mul_zero, zero_mul, add_zero]
  linear_combination hc

theorem four_terms (C A B : ZMod 2) :
    sgnZ (C + 0 * A + 0 * B + 0 * 0 * 1) + sgnZ (C + 0 * A + 1 * B + 0 * 1 * 1) +
      sgnZ (C + 1 * A + 0 * B + 1 * 0 * 1) + sgnZ (C + 1 * A + 1 * B + 1 * 1 * 1) =
      2 * sgnZ (C + A * B) := by
  fin_cases C <;> fin_cases A <;> fin_cases B <;> rfl

theorem two_terms (C A : ZMod 2) :
    sgnZ (C + 0 * A) + sgnZ (C + 1 * A) = sgnZ C * (1 + sgnZ A) := by
  fin_cases C <;> fin_cases A <;> rfl

def gS {k : ℕ} (i : Fin k) (γ : Fin k × Fin k → Bool) (b : Fin k) : Bool :=
  decide (b ≠ i) && xor (γ (i, b)) (γ (b, i))

def gSel {k : ℕ} (i : Fin k) (γ : Fin k × Fin k → Bool) (b : Fin k) : Bool :=
  gS i γ b && !(decide (∃ b' : Fin k, (decide (b' < b) && gS i γ b') = true))

def gAny {k : ℕ} (i : Fin k) (γ : Fin k × Fin k → Bool) : Bool :=
  decide (∃ b : Fin k, gS i γ b = true)

def gA0 {k : ℕ} (i : Fin k) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool) : Bool :=
  xor (α i) (γ (i, i))

def gB0 {k : ℕ} (i : Fin k) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool) : Bool :=
  decide (∃ b : Fin k, (gSel i γ b && xor (α b) (γ (b, b))) = true)

def gKeep {k : ℕ} (i : Fin k) (γ : Fin k × Fin k → Bool) (a : Fin k) : Bool :=
  decide (a ≠ i) && !gSel i γ a

def gAA {k : ℕ} (i : Fin k) (γ : Fin k × Fin k → Bool) (a : Fin k) : Bool :=
  gS i γ a && !gSel i γ a

def gBB {k : ℕ} (i : Fin k) (γ : Fin k × Fin k → Bool) (a : Fin k) : Bool :=
  gKeep i γ a && decide (∃ b : Fin k, (gSel i γ b && xor (γ (a, b)) (γ (b, a))) = true)

def nC (c : Bool) (a0 b0 : Bool) : Bool := xor c (a0 && b0)

def nAl {k : ℕ} (α : Fin k → Bool) (keep aa bb : Fin k → Bool) (a0 b0 : Bool) (a : Fin k) :
    Bool :=
  xor (xor (keep a && α a) (a0 && bb a)) (b0 && aa a)

def nGa {k : ℕ} (γ : Fin k × Fin k → Bool) (keep aa bb : Fin k → Bool) (p : Fin k × Fin k) :
    Bool :=
  xor (keep p.1 && keep p.2 && γ p) (aa p.1 && bb p.2)

theorem q_update_alg {k : ℕ} (c : Bool) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool)
    (keep aa bb : Fin k → Bool) (a0 b0 : Bool) (u : V k) :
    evalQ (nC c a0 b0) (nAl α keep aa bb a0 b0) (nGa γ keep aa bb) u =
      evalQ c α γ (fun a => toZ (keep a) * u a) +
      (toZ a0 + ∑ a, toZ (aa a) * u a) * (toZ b0 + ∑ a, toZ (bb a) * u a) := by
  unfold evalQ nC nAl nGa
  simp only [toZ_xor, toZ_and]
  have h1 : ∑ a, (toZ (keep a) * toZ (α a) + toZ a0 * toZ (bb a) + toZ b0 * toZ (aa a)) * u a =
      ∑ a, toZ (α a) * (toZ (keep a) * u a) + toZ a0 * ∑ a, toZ (bb a) * u a +
        toZ b0 * ∑ a, toZ (aa a) * u a := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _; ring
  have h2 : ∑ a, ∑ b, (toZ (keep a) * toZ (keep b) * toZ (γ (a, b)) + toZ (aa a) * toZ (bb b)) *
      u a * u b = ∑ a, ∑ b, toZ (γ (a, b)) * (toZ (keep a) * u a) * (toZ (keep b) * u b) +
      (∑ a, toZ (aa a) * u a) * (∑ a, toZ (bb a) * u a) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro b _; ring
  rw [h1, h2]
  ring

def Dead {k : ℕ} (α : Fin k → Bool) (γ : Fin k × Fin k → Bool) (a : Fin k) : Prop :=
  α a = false ∧ ∀ b, γ (a, b) = false ∧ γ (b, a) = false

structure GSt (k : ℕ) where
  z : Bool
  c : Bool
  al : Fin k → Bool
  ga : Fin k × Fin k → Bool
  n3 : ℕ

def gstep {k : ℕ} (i : Fin k) (s : GSt k) : GSt k :=
  ⟨s.z || (!gAny i s.ga && gA0 i s.al s.ga),
   nC s.c (gA0 i s.al s.ga) (gB0 i s.al s.ga),
   nAl s.al (gKeep i s.ga) (gAA i s.ga) (gBB i s.ga) (gA0 i s.al s.ga) (gB0 i s.al s.ga),
   nGa s.ga (gKeep i s.ga) (gAA i s.ga) (gBB i s.ga),
   s.n3 + (if gAny i s.ga then 1 else 0)⟩

theorem gSel_gS {k : ℕ} {i : Fin k} {γ : Fin k × Fin k → Bool} {b : Fin k}
    (h : gSel i γ b = true) : gS i γ b = true := by
  unfold gSel at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem gSel_unique {k : ℕ} {i : Fin k} {γ : Fin k × Fin k → Bool} {b b' : Fin k}
    (h : gSel i γ b = true) (h' : gSel i γ b' = true) : b = b' := by
  unfold gSel at h h'
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h h'
  rcases lt_trichotomy b b' with hl | he | hl
  · exact absurd ⟨b, by simp [hl, h.1]⟩ h'.2
  · exact he
  · exact absurd ⟨b', by simp [hl, h'.1]⟩ h.2

theorem gAny_sel {k : ℕ} {i : Fin k} {γ : Fin k × Fin k → Bool} (h : gAny i γ = true) :
    ∃ j, gSel i γ j = true := by
  classical
  unfold gAny at h
  rw [decide_eq_true_iff] at h
  let T := Finset.univ.filter (fun b => gS i γ b = true)
  have hT : T.Nonempty := by
    obtain ⟨b, hb⟩ := h
    exact ⟨b, by simp [T, hb]⟩
  refine ⟨T.min' hT, ?_⟩
  have hm : gS i γ (T.min' hT) = true := (Finset.mem_filter.1 (Finset.min'_mem T hT)).2
  unfold gSel
  rw [hm, Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not]
  rintro ⟨b', hb'⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
  have : T.min' hT ≤ b' := Finset.min'_le T b' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb'.2⟩)
  exact absurd hb'.1 (not_lt.2 this)

theorem gAny_false {k : ℕ} {i : Fin k} {γ : Fin k × Fin k → Bool} (h : gAny i γ = false)
    (b : Fin k) : gS i γ b = false := by
  unfold gAny at h
  rw [decide_eq_false_iff_not] at h
  by_contra hb
  exact h ⟨b, by simpa using hb⟩

theorem gSel_of_any_false {k : ℕ} {i : Fin k} {γ : Fin k × Fin k → Bool} (h : gAny i γ = false)
    (b : Fin k) : gSel i γ b = false := by
  unfold gSel
  rw [gAny_false h b]
  rfl

theorem gstep_any {k : ℕ} (i : Fin k) (s : GSt k) (h : gAny i s.ga = true) :
    2 * gsum s.c s.al s.ga = gsum (gstep i s).c (gstep i s).al (gstep i s).ga := by
  obtain ⟨j, hj⟩ := gAny_sel h
  have hSj := gSel_gS hj
  have hij : i ≠ j := by
    intro e
    unfold gS at hSj
    simp [e] at hSj
  have hsel : ∀ b, gSel i s.ga b = decide (b = j) := by
    intro b
    by_cases hb : b = j
    · subst hb; simp [hj]
    · simp only [hb, decide_false]
      by_contra hc
      exact hb (gSel_unique (by simpa using hc) hj)
  have hcij : toZ (s.ga (i, j)) + toZ (s.ga (j, i)) = 1 := by
    unfold gS at hSj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hSj
    rw [← toZ_xor, hSj.2]; rfl
  have hv : ∀ u : V k, (fun a => toZ (gKeep i s.ga a) * u a) =
      Function.update (Function.update u i 0) j 0 := by
    intro u
    funext a
    unfold gKeep
    rw [hsel a]
    by_cases ha : a = j
    · subst ha; simp [Ne.symm hij]
    · by_cases hb : a = i
      · subst hb; simp [ha]
      · simp [ha, hb]
  have hA : ∀ u : V k, toZ (s.al i) + toZ (s.ga (i, i)) +
      ∑ a, Function.update (Function.update u i 0) j 0 a *
        (toZ (s.ga (a, i)) + toZ (s.ga (i, a))) =
      toZ (gA0 i s.al s.ga) + ∑ a, toZ (gAA i s.ga a) * u a := by
    intro u
    unfold gA0
    rw [toZ_xor]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    unfold gAA gS
    rw [hsel a]
    by_cases haj : a = j
    · subst haj; simp
    · by_cases hai : a = i
      · subst hai; simp [haj]
      · simp [haj, hai, toZ_and, toZ_xor]; ring
  have hB : ∀ u : V k, toZ (s.al j) + toZ (s.ga (j, j)) +
      ∑ a, Function.update (Function.update u i 0) j 0 a *
        (toZ (s.ga (a, j)) + toZ (s.ga (j, a))) =
      toZ (gB0 i s.al s.ga) + ∑ a, toZ (gBB i s.ga a) * u a := by
    intro u
    have hb0 : gB0 i s.al s.ga = xor (s.al j) (s.ga (j, j)) := by
      unfold gB0
      simp only [hsel, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hx : xor (s.al j) (s.ga (j, j)) = true
      · rw [hx]; simp only [decide_eq_true_eq]; exact ⟨j, rfl, hx⟩
      · simp only [Bool.not_eq_true] at hx
        rw [hx]
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro b hb; subst hb; simp [hx]
    rw [hb0, toZ_xor]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    have hbb : gBB i s.ga a = (gKeep i s.ga a && xor (s.ga (a, j)) (s.ga (j, a))) := by
      unfold gBB
      congr 1
      simp only [hsel]
      by_cases hx : xor (s.ga (a, j)) (s.ga (j, a)) = true
      · rw [hx]; simp only [decide_eq_true_eq]; exact ⟨j, by simp [hx]⟩
      · simp only [Bool.not_eq_true] at hx
        rw [hx]
        simp only [decide_eq_false_iff_not, not_exists]
        intro b
        by_cases hb : b = j
        · subst hb; simp [hx]
        · simp [hb]
    rw [hbb]
    unfold gKeep
    rw [hsel a]
    by_cases haj : a = j
    · subst haj; simp
    · by_cases hai : a = i
      · subst hai; simp [haj]
      · simp [haj, hai, toZ_and, toZ_xor]; ring
  have key : ∀ u : V k,
      sgnZ (evalQ s.c s.al s.ga (Function.update (Function.update u i 0) j 0)) +
      sgnZ (evalQ s.c s.al s.ga (Function.update (Function.update u i 0) j 1)) +
      sgnZ (evalQ s.c s.al s.ga (Function.update (Function.update u i 1) j 0)) +
      sgnZ (evalQ s.c s.al s.ga (Function.update (Function.update u i 1) j 1)) =
      2 * sgnZ (evalQ (gstep i s).c (gstep i s).al (gstep i s).ga u) := by
    intro u
    rw [split2 s.c s.al s.ga i j hij u 0 0, split2 s.c s.al s.ga i j hij u 0 1,
      split2 s.c s.al s.ga i j hij u 1 0, split2 s.c s.al s.ga i j hij u 1 1, hA u, hB u, hcij]
    have hq := q_update_alg s.c s.al s.ga (gKeep i s.ga) (gAA i s.ga) (gBB i s.ga)
      (gA0 i s.al s.ga) (gB0 i s.al s.ga) u
    rw [hv u] at hq
    show _ = 2 * sgnZ (evalQ (nC s.c (gA0 i s.al s.ga) (gB0 i s.al s.ga))
      (nAl s.al (gKeep i s.ga) (gAA i s.ga) (gBB i s.ga) (gA0 i s.al s.ga) (gB0 i s.al s.ga))
      (nGa s.ga (gKeep i s.ga) (gAA i s.ga) (gBB i s.ga)) u)
    rw [hq]
    exact four_terms _ _ _
  have h4 := flip_sum2 (fun u => sgnZ (evalQ s.c s.al s.ga u)) i j hij
  beta_reduce at h4
  rw [Finset.sum_congr rfl (fun u _ => key u), ← Finset.mul_sum] at h4
  unfold gsum
  linarith

theorem gstep_none {k : ℕ} (i : Fin k) (s : GSt k) (h : gAny i s.ga = false) :
    2 * gsum s.c s.al s.ga =
      (1 + sgnZ (toZ (gA0 i s.al s.ga))) *
        gsum (gstep i s).c (gstep i s).al (gstep i s).ga := by
  have hsel := gSel_of_any_false h
  have hS := gAny_false h
  have hv : ∀ u : V k, (fun a => toZ (gKeep i s.ga a) * u a) = Function.update u i 0 := by
    intro u
    funext a
    unfold gKeep
    rw [hsel a]
    by_cases ha : a = i
    · subst ha; simp
    · simp [ha]
  have hb0 : gB0 i s.al s.ga = false := by
    unfold gB0
    simp [hsel]
  have haa : ∀ a, gAA i s.ga a = false := by
    intro a; unfold gAA; simp [hS a]
  have hbb : ∀ a, gBB i s.ga a = false := by
    intro a; unfold gBB; simp [hsel]
  have hA : ∀ u : V k, toZ (s.al i) + toZ (s.ga (i, i)) +
      ∑ a, Function.update u i 0 a * (toZ (s.ga (a, i)) + toZ (s.ga (i, a))) =
      toZ (gA0 i s.al s.ga) := by
    intro u
    unfold gA0
    rw [toZ_xor]
    have : ∑ a, Function.update u i 0 a * (toZ (s.ga (a, i)) + toZ (s.ga (i, a))) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : a = i
      · subst ha; simp
      · have := hS a
        unfold gS at this
        simp only [ha, ne_eq, not_false_eq_true, decide_true, Bool.true_and] at this
        rw [← toZ_xor, Bool.xor_comm, this]
        simp
    rw [this, add_zero]
  have key : ∀ u : V k,
      sgnZ (evalQ s.c s.al s.ga (Function.update u i 0)) +
      sgnZ (evalQ s.c s.al s.ga (Function.update u i 1)) =
      (1 + sgnZ (toZ (gA0 i s.al s.ga))) *
        sgnZ (evalQ (gstep i s).c (gstep i s).al (gstep i s).ga u) := by
    intro u
    rw [split1 s.c s.al s.ga i u 0, split1 s.c s.al s.ga i u 1, hA u, two_terms]
    have hq := q_update_alg s.c s.al s.ga (gKeep i s.ga) (gAA i s.ga) (gBB i s.ga)
      (gA0 i s.al s.ga) (gB0 i s.al s.ga) u
    rw [hv u] at hq
    show _ = _ * sgnZ (evalQ (nC s.c (gA0 i s.al s.ga) (gB0 i s.al s.ga))
      (nAl s.al (gKeep i s.ga) (gAA i s.ga) (gBB i s.ga) (gA0 i s.al s.ga) (gB0 i s.al s.ga))
      (nGa s.ga (gKeep i s.ga) (gAA i s.ga) (gBB i s.ga)) u)
    rw [hq, hb0]
    simp only [haa, hbb, toZ_false, zero_mul, Finset.sum_const_zero, add_zero, mul_zero]
    ring
  have h2 := flip_sum (fun u => sgnZ (evalQ s.c s.al s.ga u)) i
  beta_reduce at h2
  rw [Finset.sum_congr rfl (fun u _ => key u), ← Finset.mul_sum] at h2
  unfold gsum
  exact h2

theorem gstep_dead_i {k : ℕ} (i : Fin k) (s : GSt k) : Dead (gstep i s).al (gstep i s).ga i := by
  have hk : gKeep i s.ga i = false := by unfold gKeep; simp
  have ha : gAA i s.ga i = false := by unfold gAA gS; simp
  have hb : ∀ a, gKeep i s.ga a = false → gBB i s.ga a = false := by
    intro a h; unfold gBB; simp [h]
  refine ⟨?_, ?_⟩
  · show nAl s.al _ _ _ _ _ i = false
    unfold nAl; simp [hk, ha, hb i hk]
  · intro b
    refine ⟨?_, ?_⟩
    · show nGa s.ga _ _ _ (i, b) = false
      unfold nGa; simp [hk, ha]
    · show nGa s.ga _ _ _ (b, i) = false
      unfold nGa; simp [hk, hb i hk]

theorem gstep_dead_keep {k : ℕ} (i : Fin k) (s : GSt k) (d : Fin k) (hd : Dead s.al s.ga d) :
    Dead (gstep i s).al (gstep i s).ga d := by
  obtain ⟨hd1, hd2⟩ := hd
  have hS : gS i s.ga d = false := by
    unfold gS; simp [(hd2 i).1, (hd2 i).2]
  have hsel : gSel i s.ga d = false := by unfold gSel; simp [hS]
  have ha : gAA i s.ga d = false := by unfold gAA; simp [hS]
  have hb : gBB i s.ga d = false := by
    unfold gBB
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_exists]
    right
    intro b
    simp [(hd2 b).1, (hd2 b).2]
  refine ⟨?_, ?_⟩
  · show nAl s.al _ _ _ _ _ d = false
    unfold nAl; simp [hd1, ha, hb]
  · intro b
    refine ⟨?_, ?_⟩
    · show nGa s.ga _ _ _ (d, b) = false
      unfold nGa; simp [(hd2 b).1, ha]
    · show nGa s.ga _ _ _ (b, d) = false
      unfold nGa; simp [(hd2 b).2, hb]

def GInv {k : ℕ} (G0 : ℤ) (s : GSt k) : Prop :=
  (s.z = true → G0 = 0) ∧ (s.z = false → G0 * 2 ^ s.n3 = gsum s.c s.al s.ga)

theorem gstep_inv {k : ℕ} (G0 : ℤ) (i : Fin k) (s : GSt k) (h : GInv G0 s) :
    GInv G0 (gstep i s) := by
  obtain ⟨h1, h2⟩ := h
  cases hz : s.z
  · have h2' := h2 hz
    cases ha : gAny i s.ga
    · have hn := gstep_none i s ha
      cases h0 : gA0 i s.al s.ga
      · refine ⟨?_, ?_⟩
        · intro hz'
          simp [gstep, hz, ha, h0] at hz'
        · intro _
          have e : (gstep i s).n3 = s.n3 := by simp [gstep, ha]
          rw [e, h2']
          rw [h0] at hn
          simp only [toZ_false, sgnZ_zero] at hn
          linarith
      · refine ⟨?_, ?_⟩
        · intro _
          rw [h0] at hn
          simp only [toZ_true, sgnZ_one] at hn
          have : gsum s.c s.al s.ga = 0 := by linarith
          rw [this] at h2'
          have hp : (2 : ℤ) ^ s.n3 ≠ 0 := by positivity
          exact (mul_eq_zero.1 h2').resolve_right hp
        · intro hz'
          simp [gstep, hz, ha, h0] at hz'
    · have hn := gstep_any i s ha
      refine ⟨?_, ?_⟩
      · intro hz'
        simp [gstep, hz, ha] at hz'
      · intro _
        have e : (gstep i s).n3 = s.n3 + 1 := by simp [gstep, ha]
        rw [e, ← hn, ← h2', pow_succ]
        ring
  · refine ⟨fun _ => h1 hz, ?_⟩
    intro hz'
    simp [gstep, hz] at hz'

def gfold {k : ℕ} (L : List (Fin k)) (s : GSt k) : GSt k :=
  L.foldl (fun s i => gstep i s) s

theorem gfold_inv {k : ℕ} (G0 : ℤ) (L : List (Fin k)) (s : GSt k) (h : GInv G0 s) :
    GInv G0 (gfold L s) := by
  induction L generalizing s with
  | nil => exact h
  | cons i L ih => exact ih _ (gstep_inv G0 i s h)

theorem gfold_dead_keep {k : ℕ} (L : List (Fin k)) (s : GSt k) (d : Fin k)
    (h : Dead s.al s.ga d) : Dead (gfold L s).al (gfold L s).ga d := by
  induction L generalizing s with
  | nil => exact h
  | cons i L ih => exact ih _ (gstep_dead_keep i s d h)

theorem gfold_dead {k : ℕ} (L : List (Fin k)) (s : GSt k) (d : Fin k) (hd : d ∈ L) :
    Dead (gfold L s).al (gfold L s).ga d := by
  induction L generalizing s with
  | nil => simp at hd
  | cons i L ih =>
    rcases List.mem_cons.1 hd with e | e
    · subst e
      exact gfold_dead_keep L _ d (gstep_dead_i d s)
    · exact ih _ e

theorem gfold_n3 {k : ℕ} (L : List (Fin k)) (s : GSt k) :
    (gfold L s).n3 ≤ s.n3 + L.length := by
  induction L generalizing s with
  | nil => simp [gfold]
  | cons i L ih =>
    have := ih (gstep i s)
    have e : (gstep i s).n3 ≤ s.n3 + 1 := by
      simp only [gstep]; split <;> omega
    simp only [gfold, List.foldl_cons, List.length_cons] at this ⊢
    omega

theorem gsum_dead {k : ℕ} (c : Bool) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool)
    (h : ∀ d, Dead α γ d) : gsum c α γ = 2 ^ k * sgnZ (toZ c) := by
  have e : ∀ u : V k, evalQ c α γ u = toZ c := by
    intro u
    unfold evalQ
    have h1 : ∑ a, toZ (α a) * u a = 0 := by
      apply Finset.sum_eq_zero; intro a _; simp [(h a).1]
    have h2 : ∑ a, ∑ b, toZ (γ (a, b)) * u a * u b = 0 := by
      apply Finset.sum_eq_zero; intro a _
      apply Finset.sum_eq_zero; intro b _
      simp [((h a).2 b).1]
    rw [h1, h2]; ring
  unfold gsum
  simp only [e, Finset.sum_const, Finset.card_univ]
  have : Fintype.card (V k) = 2 ^ k := by simp
  rw [this]
  simp

def gval {k : ℕ} (s : GSt k) : ℤ :=
  if s.z then 0 else (if s.c then -((2 ^ k / 2 ^ s.n3 : ℕ) : ℤ) else ((2 ^ k / 2 ^ s.n3 : ℕ) : ℤ))

theorem gauss_correct {k : ℕ} (c : Bool) (α : Fin k → Bool) (γ : Fin k × Fin k → Bool) :
    gsum c α γ = gval (gfold (List.finRange k) ⟨false, c, α, γ, 0⟩) := by
  set s := gfold (List.finRange k) ⟨false, c, α, γ, 0⟩ with hs
  have hinv : GInv (gsum c α γ) s :=
    gfold_inv _ _ _ ⟨fun h => by simp at h, fun _ => by simp⟩
  have hdead : ∀ d, Dead s.al s.ga d := fun d => gfold_dead _ _ d (List.mem_finRange d)
  have hn : s.n3 ≤ k := by
    have := gfold_n3 (List.finRange k) ⟨false, c, α, γ, 0⟩
    simp only [List.length_finRange] at this
    rw [hs]; omega
  have hpow : (2 : ℤ) ^ k = 2 ^ (k - s.n3) * 2 ^ s.n3 := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  have hdiv : (2 ^ k / 2 ^ s.n3 : ℕ) = 2 ^ (k - s.n3) := Nat.pow_div hn (by norm_num)
  have hp : (2 : ℤ) ^ s.n3 ≠ 0 := by positivity
  unfold gval
  rw [hdiv]
  cases hz : s.z
  · have h2 := hinv.2 hz
    rw [gsum_dead _ _ _ hdead, hpow] at h2
    simp only [Bool.false_eq_true, if_false]
    cases hc : s.c
    · rw [hc] at h2
      simp only [toZ_false, sgnZ_zero, mul_one] at h2
      simp only [Bool.false_eq_true, if_false]
      push_cast
      exact mul_right_cancel₀ hp h2
    · rw [hc] at h2
      simp only [toZ_true, sgnZ_one] at h2
      simp only [if_true]
      push_cast
      exact mul_right_cancel₀ hp (by rw [h2]; ring)
  · simp only [if_true]
    exact hinv.1 hz

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

def evalQZ {k : ℕ} (c : ZMod 2) (α : V k) (γ : Fin k → Fin k → ZMod 2) (u : V k) : ZMod 2 :=
  c + ∑ a, α a * u a + ∑ a, ∑ b, γ a b * u a * u b

def IsQuad {k : ℕ} (P : V k → ZMod 2) : Prop :=
  ∃ (c : ZMod 2) (α : V k) (γ : Fin k → Fin k → ZMod 2), ∀ u, P u = evalQZ c α γ u

def IsAff {k : ℕ} (P : V k → ZMod 2) : Prop :=
  ∃ (c : ZMod 2) (α : V k), ∀ u, P u = c + ∑ a, α a * u a

theorem IsAff.quad {k : ℕ} {P : V k → ZMod 2} (h : IsAff P) : IsQuad P := by
  obtain ⟨c, α, h⟩ := h
  exact ⟨c, α, fun _ _ => 0, fun u => by simp [evalQZ, h u]⟩

theorem isAff_const {k : ℕ} (c : ZMod 2) : IsAff (fun _ : V k => c) :=
  ⟨c, 0, fun u => by simp⟩

theorem isAff_coord {k : ℕ} (i : Fin k) : IsAff (fun u : V k => u i) :=
  ⟨0, fun a => if a = i then 1 else 0, fun u => by simp⟩

theorem IsAff.add {k : ℕ} {P Q : V k → ZMod 2} (hP : IsAff P) (hQ : IsAff Q) :
    IsAff (fun u => P u + Q u) := by
  obtain ⟨c, α, hP⟩ := hP
  obtain ⟨d, β, hQ⟩ := hQ
  refine ⟨c + d, α + β, fun u => ?_⟩
  beta_reduce
  rw [hP, hQ]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem IsAff.smul {k : ℕ} {P : V k → ZMod 2} (hP : IsAff P) (s : ZMod 2) :
    IsAff (fun u => s * P u) := by
  obtain ⟨c, α, hP⟩ := hP
  refine ⟨s * c, fun a => s * α a, fun u => ?_⟩
  beta_reduce
  rw [hP, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro a _; ring

theorem isAff_sum {k : ℕ} {ι : Type} [Fintype ι] {P : ι → V k → ZMod 2}
    (h : ∀ t, IsAff (P t)) : IsAff (fun u => ∑ t, P t u) := by
  classical
  have : ∀ s : Finset ι, IsAff (fun u => ∑ t ∈ s, P t u) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isAff_const (k := k) 0
    | insert a s ha ih =>
      have := (h a).add ih
      simpa [Finset.sum_insert ha] using this
  exact this Finset.univ

theorem isQuad_const {k : ℕ} (c : ZMod 2) : IsQuad (fun _ : V k => c) :=
  (isAff_const c).quad

theorem IsQuad.add {k : ℕ} {P Q : V k → ZMod 2} (hP : IsQuad P) (hQ : IsQuad Q) :
    IsQuad (fun u => P u + Q u) := by
  obtain ⟨c, α, γ, hP⟩ := hP
  obtain ⟨d, β, δ, hQ⟩ := hQ
  refine ⟨c + d, α + β, fun a b => γ a b + δ a b, fun u => ?_⟩
  beta_reduce
  rw [hP, hQ]
  unfold evalQZ
  have h1 : ∑ a, (α + β) a * u a = ∑ a, α a * u a + ∑ a, β a * u a := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _
    simp only [Pi.add_apply]; ring
  have h2 : ∑ a, ∑ b, (γ a b + δ a b) * u a * u b =
      ∑ a, ∑ b, γ a b * u a * u b + ∑ a, ∑ b, δ a b * u a * u b := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro b _
    ring
  rw [h1, h2]; ring

theorem IsQuad.smul {k : ℕ} {P : V k → ZMod 2} (hP : IsQuad P) (s : ZMod 2) :
    IsQuad (fun u => s * P u) := by
  obtain ⟨c, α, γ, hP⟩ := hP
  refine ⟨s * c, fun a => s * α a, fun a b => s * γ a b, fun u => ?_⟩
  beta_reduce
  rw [hP]
  unfold evalQZ
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl; intro a _; ring
  · apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _; ring

theorem isQuad_sum {k : ℕ} {ι : Type} [Fintype ι] {P : ι → V k → ZMod 2}
    (h : ∀ t, IsQuad (P t)) : IsQuad (fun u => ∑ t, P t u) := by
  classical
  have : ∀ s : Finset ι, IsQuad (fun u => ∑ t ∈ s, P t u) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isQuad_const (k := k) 0
    | insert a s ha ih =>
      have := (h a).add ih
      simpa [Finset.sum_insert ha] using this
  exact this Finset.univ

theorem IsAff.mul {k : ℕ} {P Q : V k → ZMod 2} (hP : IsAff P) (hQ : IsAff Q) :
    IsQuad (fun u => P u * Q u) := by
  obtain ⟨c, α, hP⟩ := hP
  obtain ⟨d, β, hQ⟩ := hQ
  refine ⟨c * d, fun a => c * β a + d * α a, fun a b => α a * β b, fun u => ?_⟩
  beta_reduce
  rw [hP, hQ]
  unfold evalQZ
  have h2 : ∑ a, ∑ b, α a * β b * u a * u b = (∑ a, α a * u a) * (∑ b, β b * u b) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _; ring
  have h1 : ∑ a, (c * β a + d * α a) * u a = c * ∑ a, β a * u a + d * ∑ a, α a * u a := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _; ring
  rw [h1, h2]; ring

theorem IsQuad.congr {k : ℕ} {P Q : V k → ZMod 2} (hP : IsQuad P) (h : ∀ u, P u = Q u) :
    IsQuad Q := by
  obtain ⟨c, α, γ, hP⟩ := hP
  exact ⟨c, α, γ, fun u => by rw [← h u, hP u]⟩

def e1 {k : ℕ} (q : Fin k) : V k := fun a => if a = q then 1 else 0

def Δ2 {k : ℕ} (P : V k → ZMod 2) (v w : V k) : ZMod 2 := P (v + w) + P v + P w + P 0

theorem evalQZ_zero {k : ℕ} (c : ZMod 2) (α : V k) (γ : Fin k → Fin k → ZMod 2) :
    evalQZ c α γ 0 = c := by
  simp [evalQZ]

theorem evalQZ_e1 {k : ℕ} (c : ZMod 2) (α : V k) (γ : Fin k → Fin k → ZMod 2) (q : Fin k) :
    evalQZ c α γ (e1 q) = c + α q + γ q q := by
  simp [evalQZ, e1]

theorem evalQZ_e2 {k : ℕ} (c : ZMod 2) (α : V k) (γ : Fin k → Fin k → ZMod 2) (q r : Fin k)
    (hqr : q ≠ r) :
    evalQZ c α γ (e1 q + e1 r) = c + α q + α r + γ q q + γ q r + γ r q + γ r r := by
  unfold evalQZ
  have hv : ∀ a, (e1 q + e1 r) a = (if a = q then (1 : ZMod 2) else 0) + (if a = r then 1 else 0) :=
    fun a => rfl
  simp only [hv, mul_add, add_mul, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem dsum_split {k : ℕ} (γ : Fin k → Fin k → ZMod 2) (u : V k) :
    ∑ a, ∑ b, γ a b * u a * u b = ∑ a, γ a a * u a +
      ∑ a, ∑ b, (if a < b then u a * u b * (γ a b + γ b a) else 0) := by
  have h1 : ∀ a b, γ a b * u a * u b = (if a = b then γ a a * u a else 0) +
      (if a < b then γ a b * u a * u b else 0) + (if b < a then γ a b * u a * u b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_gt h]
    · subst h; simp [mul_assoc, zsq]
    · simp [h, ne_of_gt h, not_lt_of_gt h]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun a b => if b < a then γ a b * u a * u b else 0)]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _
  by_cases h : a < b
  · simp [h]; ring
  · simp [h]

theorem interp {k : ℕ} {P : V k → ZMod 2} (hP : IsQuad P) (u : V k) :
    P u = P 0 + ∑ q, u q * (P (e1 q) + P 0) +
      ∑ q, ∑ r, (if q < r then u q * u r * Δ2 P (e1 q) (e1 r) else 0) := by
  obtain ⟨c, α, γ, hP⟩ := hP
  have hz : P 0 = c := by rw [hP, evalQZ_zero]
  have he : ∀ q, P (e1 q) + P 0 = α q + γ q q := by
    intro q; rw [hP, evalQZ_e1, hz]
    have := z2 c
    linear_combination this
  have hd : ∀ q r, q < r → Δ2 P (e1 q) (e1 r) = γ q r + γ r q := by
    intro q r h
    unfold Δ2
    rw [hP (e1 q + e1 r), evalQZ_e2 _ _ _ _ _ (ne_of_lt h), hP (e1 q), hP (e1 r),
      evalQZ_e1, evalQZ_e1, hz]
    have := z2 c
    have h2 := z2 (α q)
    have h3 := z2 (α r)
    have h4 := z2 (γ q q)
    have h5 := z2 (γ r r)
    linear_combination 2 * this + h2 + h3 + h4 + h5
  have e2 : ∀ q r, (if q < r then u q * u r * Δ2 P (e1 q) (e1 r) else 0) =
      (if q < r then u q * u r * (γ q r + γ r q) else 0) := by
    intro q r
    by_cases h : q < r
    · rw [if_pos h, if_pos h, hd q r h]
    · rw [if_neg h, if_neg h]
  have e3 : ∑ q, u q * (α q + γ q q) = ∑ a, α a * u a + ∑ a, γ a a * u a := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _; ring
  rw [hP u]
  unfold evalQZ
  rw [dsum_split]
  simp only [he, e2]
  rw [hz, e3]; ring

theorem interp_aff {k : ℕ} {P : V k → ZMod 2} (hP : IsQuad P)
    (h0 : ∀ q r : Fin k, Δ2 P (e1 q) (e1 r) = 0) (u : V k) :
    P u = P 0 + ∑ q, u q * (P (e1 q) + P 0) := by
  rw [interp hP u]
  simp [h0]

theorem IsAff.delta {k : ℕ} {P : V k → ZMod 2} (hP : IsAff P) (v w : V k) : Δ2 P v w = 0 := by
  obtain ⟨c, α, hP⟩ := hP
  unfold Δ2
  rw [hP, hP, hP, hP]
  simp only [Pi.add_apply, Pi.zero_apply, mul_add, mul_zero, Finset.sum_add_distrib,
    Finset.sum_const_zero]
  have := z2 c
  have h2 := z2 (∑ a, α a * v a)
  have h3 := z2 (∑ a, α a * w a)
  linear_combination 2 * this + h2 + h3

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

def ext {k : ℕ} (z : V k) : Fin (k + 1) → ZMod 2 :=
  fun i => if h : i.val < k then z ⟨i.val, h⟩ else 1

theorem ext_cs {k : ℕ} (z : V k) (i : Fin k) : ext z (Fin.castSucc i) = z i := by
  simp [ext]

theorem ext_last {k : ℕ} (z : V k) : ext z (Fin.last k) = 1 := by
  simp [ext]

def Sol {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) (z : V k) : Prop :=
  (mat R).mulVec (ext z) = 0

instance solDec {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) (z : V k) : Decidable (Sol R z) :=
  inferInstanceAs (Decidable ((mat R).mulVec (ext z) = 0))

def Upper {D : ℕ} (R : Fin D × Fin D → Bool) : Prop :=
  ∀ p q : Fin D, q < p → R (p, q) = false

def FlatOK {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) : Prop := GJF R ∧ Upper R

def cons {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) : Prop := R (Fin.last k, Fin.last k) = false

def piR {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) (u : V k) : V k :=
  fun i => u i + (mat R).mulVec (ext u) (Fin.castSucc i)

theorem mulVec_ext {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) (u : V k) (r : Fin (k + 1)) :
    (mat R).mulVec (ext u) r = ∑ q, toZ (R (r, Fin.castSucc q)) * u q + toZ (R (r, Fin.last k)) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, ext_cs, ext_last, mul_one]
  rfl

theorem row_last_zero {k : ℕ} {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R)
    (hc : cons R) (u : V k) : (mat R).mulVec (ext u) (Fin.last k) = 0 := by
  rw [mulVec_ext]
  have hz := hR.1.2 (Fin.last k) hc
  simp [hz]

theorem sol_iff_fix {k : ℕ} {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R)
    (hc : cons R) (z : V k) : Sol R z ↔ piR R z = z := by
  constructor
  · intro h
    have h' : (mat R).mulVec (ext z) = 0 := h
    funext i
    simp [piR, h']
  · intro h
    funext r
    refine Fin.lastCases ?_ (fun i => ?_) r
    · exact row_last_zero hR hc z
    · have := congrFun h i
      simp only [piR] at this
      simpa using this

theorem ext_piR {k : ℕ} {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R)
    (hc : cons R) (u : V k) : ext (piR R u) = ext u + (mat R).mulVec (ext u) := by
  funext r
  refine Fin.lastCases ?_ (fun i => ?_) r
  · rw [Pi.add_apply, ext_last, ext_last, row_last_zero hR hc, add_zero]
  · rw [Pi.add_apply, ext_cs, ext_cs]
    rfl

theorem sol_piR {k : ℕ} {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R)
    (hc : cons R) (u : V k) : Sol R (piR R u) := by
  unfold Sol
  rw [ext_piR hR hc, Matrix.mulVec_add, Matrix.mulVec_mulVec, GJF_idem hR.1]
  funext r
  simp [z2]

theorem not_cons_empty {k : ℕ} {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R)
    (hc : ¬ cons R) (z : V k) : ¬ Sol R z := by
  intro h
  have := congrFun h (Fin.last k)
  rw [mulVec_ext] at this
  have hl : R (Fin.last k, Fin.last k) = true := by simpa [cons] using hc
  have hq : ∀ q : Fin k, R (Fin.last k, Fin.castSucc q) = false :=
    fun q => hR.2 _ _ (Fin.castSucc_lt_last q)
  simp [hq, hl] at this

theorem piR_aff {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) (i : Fin k) :
    IsAff (fun u => piR R u i) := by
  refine ⟨toZ (R (Fin.castSucc i, Fin.last k)),
    fun q => (if q = i then 1 else 0) + toZ (R (Fin.castSucc i, Fin.castSucc q)), fun u => ?_⟩
  simp only [piR, mulVec_ext, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

def xz {k : ℕ} (x : Fin (2 ^ k)) : V k := fun i => toZ (x.val.testBit i.val)

theorem xz_inj {k : ℕ} : Function.Injective (xz (k := k)) := by
  intro x x' h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · have := congrFun h ⟨i, hi⟩
    simpa [xz, toZ_inj] using this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num)
      (not_lt.1 hi))), Nat.testBit_lt_two_pow (lt_of_lt_of_le x'.isLt
      (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)))]

theorem xz_bij {k : ℕ} : Function.Bijective (xz (k := k)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨xz_inj, ?_⟩
  simp

noncomputable def xzE (k : ℕ) : Fin (2 ^ k) ≃ V k := Equiv.ofBijective _ xz_bij

theorem xz_xzE {k : ℕ} (z : V k) : xz ((xzE k).symm z) = z :=
  (xzE k).apply_symm_apply z

theorem xz_tb {k : ℕ} (x : Fin (2 ^ k)) (i : Fin k) : toZ (x.val.testBit i.val) = xz x i := rfl

def fz {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) (z : V k) (j : Fin m) : ZMod 2 :=
  toZ (bI j) + ∑ i, toZ (AI j i) * z i + ∑ i, ∑ p, toZ (BI j i p) * z i * z p

def fB {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) (x : Fin (2 ^ k)) (j : Fin m) : Bool :=
  (List.finRange k).foldl (fun acc i => (List.finRange k).foldl (fun v p =>
    xor v ((BI j i p && x.val.testBit i.val) && x.val.testBit p.val)) acc)
    (xor (bI j) (dotB (AI j) (fun i => x.val.testBit i.val)))

theorem toZ_fB {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) (x : Fin (2 ^ k)) (j : Fin m) :
    toZ (fB bI AI BI x j) = fz bI AI BI (xz x) j := by
  unfold fB fz
  rw [foldl2_xor_fin, toZ_xor, toZ_dotB]
  simp only [toZ_and, xz_tb]

theorem fz_quad {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) (R : Fin (k + 1) × Fin (k + 1) → Bool) (j : Fin m) :
    IsQuad (fun u => fz bI AI BI (piR R u) j) := by
  unfold fz
  refine ((isQuad_const _).add ?_).add ?_
  · exact (isAff_sum (fun i => (piR_aff R i).smul (toZ (AI j i)))).quad
  · refine isQuad_sum (fun i => isQuad_sum (fun p => ?_))
    refine IsQuad.congr (((piR_aff R i).smul (toZ (BI j i p))).mul (piR_aff R p)) ?_
    intro u; ring

theorem comb_quad {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) (R : Fin (k + 1) × Fin (k + 1) → Bool) (l : V m)
    (yv : V m) :
    IsQuad (fun u => ∑ j, l j * (fz bI AI BI (piR R u) j + yv j)) := by
  refine isQuad_sum (fun j => ?_)
  refine IsQuad.congr (((fz_quad bI AI BI R j).add (isQuad_const (yv j))).smul (l j)) ?_
  intro u; rfl

def ind {k : ℕ} (a : Fin (k + 1)) : V k := fun q => if Fin.castSucc q = a then 1 else 0

def ptv {k : ℕ} (a b : Fin (k + 1)) : V k := ind a + ind b

theorem ind_last {k : ℕ} : ind (Fin.last k) = (0 : V k) := by
  funext q; simp [ind, Fin.castSucc_ne_last]

theorem ind_cs {k : ℕ} (q : Fin k) : ind (Fin.castSucc q) = e1 q := by
  funext a; simp [ind, e1]

theorem ptv_last {k : ℕ} (a : Fin (k + 1)) : ptv a (Fin.last k) = ind a := by
  simp [ptv, ind_last]

theorem ptv_ll {k : ℕ} : ptv (Fin.last k) (Fin.last k) = (0 : V k) := by
  simp [ptv, ind_last]

def FZ {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) (R : Fin (k + 1) × Fin (k + 1) → Bool)
    (a b : Fin (k + 1)) (j : Fin m) : ZMod 2 :=
  fz bI AI BI (piR R (ptv a b)) j

def CZ {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) (R : Fin (k + 1) × Fin (k + 1) → Bool)
    (a b : Fin (k + 1)) (j : Fin m) : ZMod 2 :=
  FZ bI AI BI R a b j + FZ bI AI BI R a (Fin.last k) j + FZ bI AI BI R b (Fin.last k) j +
    FZ bI AI BI R (Fin.last k) (Fin.last k) j

theorem delta_comb {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) (R : Fin (k + 1) × Fin (k + 1) → Bool) (l yv : V m)
    (a b : Fin (k + 1)) :
    Δ2 (fun u => ∑ j, l j * (fz bI AI BI (piR R u) j + yv j)) (ind a) (ind b) =
      ∑ j, l j * CZ bI AI BI R a b j := by
  unfold Δ2 CZ FZ
  rw [← ptv_last a, ← ptv_last b, ← ptv_ll]
  have : ind a + ind b = ptv a b := rfl
  rw [ptv_last, ptv_last, this]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  have := z2 (yv j)
  linear_combination (2 * l j) * this

def SolX {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) : Finset (Fin (2 ^ k)) :=
  Finset.univ.filter (fun x => Sol R (xz x))

theorem dot_f_toZ {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) (l : Fin m → Bool) (x : Fin (2 ^ k)) :
    toZ (dotB l (fB bI AI BI x)) = ∑ j, zv l j * fz bI AI BI (xz x) j := by
  rw [toZ_dotB]
  simp only [toZ_fB]
  rfl

theorem aff_iff {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) {R : Fin (k + 1) × Fin (k + 1) → Bool}
    (hR : FlatOK R) (hc : cons R) (l : Fin m → Bool) :
    affOn (fB bI AI BI) (SolX R) l ↔ ∀ a b, ∑ j, zv l j * CZ bI AI BI R a b j = 0 := by
  set P := fun u => ∑ j, zv l j * (fz bI AI BI (piR R u) j + (0 : V m) j) with hPdef
  have hPq : IsQuad P := comb_quad bI AI BI R (zv l) 0
  constructor
  · rintro ⟨av, bv, hab⟩ a b
    rw [← delta_comb bI AI BI R (zv l) 0 a b]
    have hL : ∀ u, P u = toZ bv + ∑ i, toZ (av i) * piR R u i := by
      intro u
      set x := (xzE k).symm (piR R u) with hx
      have hxS : x ∈ SolX R := by
        simp only [SolX, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hx, xz_xzE]; exact sol_piR hR hc u
      have h1 := hab x hxS
      have h2 := congrArg toZ h1
      rw [dot_f_toZ, toZ_xor, toZ_dotB] at h2
      simp only [xz_tb] at h2
      rw [hx, xz_xzE] at h2
      simp only [hPdef, Pi.zero_apply, add_zero]
      rw [h2]
    have hA : IsAff (fun u => toZ bv + ∑ i, toZ (av i) * piR R u i) :=
      (isAff_const _).add (isAff_sum (fun i => (piR_aff R i).smul (toZ (av i))))
    have : Δ2 P (ind a) (ind b) = Δ2 (fun u => toZ bv + ∑ i, toZ (av i) * piR R u i)
        (ind a) (ind b) := by
      unfold Δ2; rw [hL, hL, hL, hL]
    rw [this]
    exact hA.delta _ _
  · intro h
    have h0 : ∀ q r : Fin k, Δ2 P (e1 q) (e1 r) = 0 := by
      intro q r
      rw [← ind_cs, ← ind_cs, delta_comb]
      exact h _ _
    refine ⟨fun q => ofZ (P (e1 q) + P 0), ofZ (P 0), fun x hx => ?_⟩
    rw [← toZ_inj, dot_f_toZ, toZ_xor, toZ_dotB]
    simp only [toZ_ofZ, xz_tb]
    have hxs : Sol R (xz x) := by simpa [SolX] using hx
    have hfix := (sol_iff_fix hR hc (xz x)).1 hxs
    have := interp_aff hPq h0 (xz x)
    simp only [hPdef, Pi.zero_apply, add_zero] at this
    rw [hfix] at this
    rw [this]
    simp only [hPdef, Pi.zero_apply, add_zero]
    congr 1
    apply Finset.sum_congr rfl; intro q _; ring

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

def splitF {a b : ℕ} {α : Type} (f : Fin a → α) (g : Fin b → α) (i : Fin (a + b)) : α :=
  if h : i.val < a then f ⟨i.val, h⟩ else g ⟨i.val - a, by omega⟩

@[simp] theorem splitF_castAdd {a b : ℕ} {α : Type} (f : Fin a → α) (g : Fin b → α) (i : Fin a) :
    splitF f g (Fin.castAdd b i) = f i := by
  simp [splitF]

@[simp] theorem splitF_natAdd {a b : ℕ} {α : Type} (f : Fin a → α) (g : Fin b → α) (i : Fin b) :
    splitF f g (Fin.natAdd a i) = g i := by
  simp [splitF]

theorem forall_add {a b : ℕ} (P : Fin (a + b) → Prop) :
    (∀ r, P r) ↔ (∀ i, P (Fin.castAdd b i)) ∧ (∀ i, P (Fin.natAdd a i)) := by
  constructor
  · intro h; exact ⟨fun i => h _, fun i => h _⟩
  · rintro ⟨h1, h2⟩ r
    exact Fin.addCases h1 h2 r

def ext1 {m n : ℕ} (l : V m) : Fin (m + n) → ZMod 2 := splitF l 0

theorem mulVec_ext1 {m n : ℕ} (R : Fin (m + n) × Fin (m + n) → Bool) (l : V m) (r : Fin (m + n)) :
    (mat R).mulVec (ext1 l) r = ∑ j, toZ (R (r, Fin.castAdd n j)) * l j := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, ext1, splitF_castAdd, splitF_natAdd,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

def kvZ {m n : ℕ} (R : Fin (m + n) × Fin (m + n) → Bool) (s : Fin m) : V m := fun j =>
  if R (Fin.castAdd n s, Fin.castAdd n s) then 0
  else (if j = s then 1 else 0) + toZ (R (Fin.castAdd n j, Fin.castAdd n s))

def ZeroCols {m n : ℕ} (R : Fin (m + n) × Fin (m + n) → Bool) : Prop :=
  ∀ r t, R (r, Fin.natAdd m t) = false

theorem idem_part {m n : ℕ} {R : Fin (m + n) × Fin (m + n) → Bool} (hR : GJF R) (hz : ZeroCols R)
    (r c : Fin (m + n)) :
    ∑ j, toZ (R (r, Fin.castAdd n j)) * toZ (R (Fin.castAdd n j, c)) = toZ (R (r, c)) := by
  have hz' : ∀ r t, R (r, Fin.natAdd m t) = false := hz
  have h := congrFun (congrFun (GJF_idem hR) r) c
  rw [Matrix.mul_apply, Fin.sum_univ_add] at h
  simp only [mat_eq_toZ, hz', toZ_false, zero_mul, Finset.sum_const_zero, add_zero] at h
  exact h

theorem kv_ker {m n : ℕ} {R : Fin (m + n) × Fin (m + n) → Bool} (hR : GJF R) (hz : ZeroCols R)
    (s : Fin m) : (mat R).mulVec (ext1 (kvZ R s)) = 0 := by
  funext r
  rw [mulVec_ext1]
  unfold kvZ
  by_cases hs : R (Fin.castAdd n s, Fin.castAdd n s) = true
  · simp [hs]
  · simp only [hs, Bool.false_eq_true, if_false, mul_add, mul_ite, mul_one, mul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [idem_part hR hz, Pi.zero_apply, z2]

theorem ker_span {m n : ℕ} {R : Fin (m + n) × Fin (m + n) → Bool} (hR : GJF R) (hz : ZeroCols R)
    (l : V m) (hl : (mat R).mulVec (ext1 l) = 0) (j : Fin m) :
    l j = ∑ s, l s * kvZ R s j := by
  by_cases hj : R (Fin.castAdd n j, Fin.castAdd n j) = true
  · have hrow := congrFun hl (Fin.castAdd n j)
    rw [mulVec_ext1] at hrow
    have e : ∀ s, l s * kvZ R s j =
        toZ (R (Fin.castAdd n j, Fin.castAdd n s)) * l s + (if s = j then l s else 0) := by
      intro s
      unfold kvZ
      by_cases hs : R (Fin.castAdd n s, Fin.castAdd n s) = true
      · rw [hR.1 _ hs (Fin.castAdd n j)]
        simp only [hs, if_true, mul_zero, Fin.castAdd_inj]
        by_cases hjs : j = s
        · subst hjs; simp [z2]
        · simp [hjs, Ne.symm hjs]
      · have hjs : s ≠ j := by intro e; subst e; exact hs hj
        simp [hs, hjs, Ne.symm hjs]
        ring
    rw [Finset.sum_congr rfl (fun s _ => e s), Finset.sum_add_distrib, hrow]
    simp
  · have e : ∀ s, l s * kvZ R s j = if s = j then l s else 0 := by
      intro s
      unfold kvZ
      have hrz := hR.2 _ (by simpa using hj) (Fin.castAdd n s)
      by_cases hs : R (Fin.castAdd n s, Fin.castAdd n s) = true
      · have hjs : s ≠ j := by intro e; subst e; exact hj hs
        simp [hs, hjs]
      · by_cases hjs : s = j
        · subst hjs; simp [hs, hrz]
        · simp [hs, hjs, Ne.symm hjs, hrz]
    rw [Finset.sum_congr rfl (fun s _ => e s)]
    simp

theorem ker_comb {m n : ℕ} {R : Fin (m + n) × Fin (m + n) → Bool} (hR : GJF R) (hz : ZeroCols R)
    (w : V m) : (mat R).mulVec (ext1 (fun j => ∑ s, w s * kvZ R s j)) = 0 := by
  have : ext1 (n := n) (fun j => ∑ s, w s * kvZ R s j) = ∑ s, w s • ext1 (kvZ R s) := by
    funext c
    refine Fin.addCases (fun j => ?_) (fun t => ?_) c
    · simp [ext1, Finset.sum_apply]
    · simp [ext1, Finset.sum_apply]
  rw [this, Matrix.mulVec_sum]
  simp [Matrix.mulVec_smul, kv_ker hR hz]

def piv {m n : ℕ} (R : Fin (m + n) × Fin (m + n) → Bool) (j : Fin m) : Bool :=
  R (Fin.castAdd n j, Fin.castAdd n j)

def rho {m n : ℕ} (R : Fin (m + n) × Fin (m + n) → Bool) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => piv R j = true)).card

theorem ker_card {m n : ℕ} {R : Fin (m + n) × Fin (m + n) → Bool} (hR : GJF R) (hz : ZeroCols R) :
    (Finset.univ.filter (fun l : V m => (mat R).mulVec (ext1 l) = 0)).card = 2 ^ (m - rho R) := by
  classical
  set T := Fintype.piFinset (fun j : Fin m => if piv R j = true then ({0} : Finset (ZMod 2))
    else Finset.univ) with hT
  have hcardT : T.card = 2 ^ (m - rho R) := by
    rw [hT, Fintype.card_piFinset]
    have : ∀ j : Fin m, (if piv R j = true then ({0} : Finset (ZMod 2)) else Finset.univ).card =
        if piv R j = true then 1 else 2 := by
      intro j; split <;> simp
    simp only [this]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun j => piv R j = true)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    unfold rho
    omega
  rw [← hcardT]
  have hmemT : ∀ w, w ∈ T ↔ ∀ j, piv R j = true → w j = 0 := by
    intro w
    rw [hT, Fintype.mem_piFinset]
    constructor
    · intro h j hj; have := h j; simp [hj] at this; exact this
    · intro h j; by_cases hj : piv R j = true <;> simp [hj, h j]
  apply Finset.card_nbij' (fun l => fun j => if piv R j = true then 0 else l j)
    (fun w => fun j => ∑ s, w s * kvZ R s j)
  · intro l _
    simp only [Finset.mem_coe, hmemT]
    intro j hj; simp [hj]
  · intro w _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact ker_comb hR hz w
  · intro l hl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hl
    funext j
    rw [ker_span hR hz l hl j]
    apply Finset.sum_congr rfl; intro s _
    unfold kvZ
    by_cases hs : piv R s = true
    · simp [hs, piv] at hs ⊢; simp [hs]
    · simp only [piv] at hs; simp [hs, piv]
  · intro w hw
    simp only [Finset.mem_coe, hmemT] at hw
    funext j
    by_cases hj : piv R j = true
    · simp [hj, hw j hj]
    · simp only [hj, Bool.false_eq_true, if_false]
      have hrz := hR.2 _ (by simpa [piv] using hj)
      have e : ∀ s, w s * kvZ R s j = if s = j then w s else 0 := by
        intro s
        unfold kvZ
        by_cases hs : R (Fin.castAdd n s, Fin.castAdd n s) = true
        · have hsj : s ≠ j := by intro e; subst e; exact hj (by simpa [piv] using hs)
          simp [hs, hsj, hw s (by simpa [piv] using hs)]
        · by_cases hjs : s = j
          · subst hjs; simp [hs, hrz]
          · simp [hs, hjs, Ne.symm hjs, hrz]
      rw [Finset.sum_congr rfl (fun s _ => e s)]
      simp

def pairOf {k : ℕ} (pr : Fin ((k + 1) * (k + 1))) : Fin (k + 1) × Fin (k + 1) :=
  finProdFinEquiv.symm pr

def M1 {k m : ℕ} (CB : Fin (k + 1) → Fin (k + 1) → Fin m → Bool) :
    Fin (m + (k + 1) * (k + 1)) × Fin (m + (k + 1) * (k + 1)) → Bool := fun p =>
  splitF (fun _ : Fin m => false)
    (fun pr => splitF (fun j : Fin m => CB (pairOf pr).1 (pairOf pr).2 j) (fun _ => false) p.2) p.1

theorem M1_zc {k m : ℕ} (CB : Fin (k + 1) → Fin (k + 1) → Fin m → Bool) :
    ZeroCols (gj (m + (k + 1) * (k + 1)) (M1 CB)) := by
  intro r t
  apply gj_col_zero
  intro r'
  unfold M1
  refine Fin.addCases (fun i => ?_) (fun pr => ?_) r'
  · simp
  · simp

theorem M1_ker {k m : ℕ} (CB : Fin (k + 1) → Fin (k + 1) → Fin m → Bool) (v : V m) :
    (mat (M1 CB)).mulVec (ext1 v) = 0 ↔ ∀ a b, ∑ j, v j * toZ (CB a b j) = 0 := by
  rw [funext_iff, forall_add]
  simp only [mulVec_ext1, Pi.zero_apply, M1, splitF_castAdd, splitF_natAdd, toZ_false, zero_mul,
    Finset.sum_const_zero, implies_true, true_and]
  constructor
  · intro h a b
    have := h (finProdFinEquiv (a, b))
    simp only [pairOf, Equiv.symm_apply_apply] at this
    rw [← this]
    apply Finset.sum_congr rfl; intro j _; ring
  · intro h pr
    rw [← h (pairOf pr).1 (pairOf pr).2]
    apply Finset.sum_congr rfl; intro j _; ring

def M2 {k m : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) (NR : Fin m → Fin (k + 1) → Bool) :
    Fin ((k + 1) + m) × Fin ((k + 1) + m) → Bool := fun p =>
  splitF (fun a => splitF (fun b => R (a, b)) (fun _ => false) p.2)
    (fun s => splitF (fun b => NR s b) (fun _ => false) p.2) p.1

def stepMat {k m : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) (NR : Fin m → Fin (k + 1) → Bool) :
    Fin (k + 1) × Fin (k + 1) → Bool := fun p =>
  gj ((k + 1) + m) (M2 R NR) (Fin.castAdd m p.1, Fin.castAdd m p.2)

theorem stepMat_ok {k m : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool)
    (NR : Fin m → Fin (k + 1) → Bool) : FlatOK (stepMat R NR) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp i
    have := gj_pivcol (M2 R NR) (Fin.castAdd m p) hp (Fin.castAdd m i)
    simp only [stepMat]
    rw [this]
    simp [Fin.castAdd_inj]
  · intro q hq j
    exact gj_zerorow (M2 R NR) (Fin.castAdd m q) hq (Fin.castAdd m j)
  · intro p q hpq
    exact gj_upper (M2 R NR) (Fin.castAdd m p) (Fin.castAdd m q) (by
      simp only [Fin.lt_def, Fin.coe_castAdd] at hpq ⊢; exact hpq)

def ext2 {k m : ℕ} (z : V k) : Fin ((k + 1) + m) → ZMod 2 := splitF (ext z) 0

theorem mulVec_ext2 {k m : ℕ} (M : Fin ((k + 1) + m) × Fin ((k + 1) + m) → Bool) (z : V k)
    (r : Fin ((k + 1) + m)) :
    (mat M).mulVec (ext2 z) r = ∑ b, toZ (M (r, Fin.castAdd m b)) * ext z b := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, ext2, splitF_castAdd, splitF_natAdd,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

theorem stack_sol {k m : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool)
    (NR : Fin m → Fin (k + 1) → Bool) (z : V k) :
    Sol (stepMat R NR) z ↔ Sol R z ∧ ∀ s, ∑ b, toZ (NR s b) * ext z b = 0 := by
  have hA : (mat (M2 R NR)).mulVec (ext2 z) = 0 ↔
      Sol R z ∧ ∀ s, ∑ b, toZ (NR s b) * ext z b = 0 := by
    rw [funext_iff, forall_add]
    simp only [mulVec_ext2, Pi.zero_apply, M2, splitF_castAdd, splitF_natAdd]
    unfold Sol
    rw [funext_iff]
    rfl
  rw [← hA, ← gj_sol_iff]
  rw [funext_iff, forall_add]
  have hzr : ∀ s : Fin m, ∀ b, gj ((k + 1) + m) (M2 R NR) (Fin.natAdd (k + 1) s, b) = false := by
    intro s b
    apply gj_zerorow
    apply gj_col_zero
    intro r
    unfold M2
    refine Fin.addCases (fun i => ?_) (fun t => ?_) r
    · simp
    · simp
  simp only [mulVec_ext2, Pi.zero_apply, hzr, toZ_false, zero_mul, Finset.sum_const_zero,
    implies_true, and_true]
  unfold Sol
  rw [funext_iff]
  simp only [Pi.zero_apply]
  rfl

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

section step
variable {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
  (BI : Fin m → Fin k → Fin k → Bool) (yI : Fin m → Bool)

def CBB (R : Fin (k + 1) × Fin (k + 1) → Bool) (a b : Fin (k + 1)) (j : Fin m) : Bool :=
  ofZ (CZ bI AI BI R a b j)

def R1B (R : Fin (k + 1) × Fin (k + 1) → Bool) :
    Fin (m + (k + 1) * (k + 1)) × Fin (m + (k + 1) * (k + 1)) → Bool :=
  gj (m + (k + 1) * (k + 1)) (M1 (CBB bI AI BI R))

def NRZ (R : Fin (k + 1) × Fin (k + 1) → Bool) (s : Fin m) (b : Fin (k + 1)) : ZMod 2 :=
  ∑ j, kvZ (R1B bI AI BI R) s j * (FZ bI AI BI R b (Fin.last k) j +
    (if b = Fin.last k then toZ (yI j) else FZ bI AI BI R (Fin.last k) (Fin.last k) j))

def NRB (R : Fin (k + 1) × Fin (k + 1) → Bool) (s : Fin m) (b : Fin (k + 1)) : Bool :=
  ofZ (NRZ bI AI BI yI R s b)

def stepR (R : Fin (k + 1) × Fin (k + 1) → Bool) : Fin (k + 1) × Fin (k + 1) → Bool :=
  stepMat R (NRB bI AI BI yI R)

theorem ker_iff (R : Fin (k + 1) × Fin (k + 1) → Bool) (v : V m) :
    (∀ a b, ∑ j, v j * CZ bI AI BI R a b j = 0) ↔
      (mat (R1B bI AI BI R)).mulVec (ext1 v) = 0 := by
  rw [R1B, gj_sol_iff, M1_ker]
  simp [CBB, toZ_ofZ]

theorem R1B_gjf (R : Fin (k + 1) × Fin (k + 1) → Bool) : GJF (R1B bI AI BI R) := gj_GJF _

theorem R1B_zc (R : Fin (k + 1) × Fin (k + 1) → Bool) : ZeroCols (R1B bI AI BI R) := M1_zc _

theorem nrow_meaning {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R) (hc : cons R)
    (z : V k) (hz : Sol R z) (s : Fin m) :
    ∑ b, toZ (NRB bI AI BI yI R s b) * ext z b =
      ∑ j, kvZ (R1B bI AI BI R) s j * (fz bI AI BI z j + toZ (yI j)) := by
  set kv := kvZ (R1B bI AI BI R) s with hkv
  set P := fun u => ∑ j, kv j * (fz bI AI BI (piR R u) j + (0 : V m) j) with hPdef
  have hPq : IsQuad P := comb_quad bI AI BI R kv 0
  have hker : ∀ a b, ∑ j, kv j * CZ bI AI BI R a b j = 0 :=
    (ker_iff bI AI BI R kv).2 (kv_ker (R1B_gjf bI AI BI R) (R1B_zc bI AI BI R) s)
  have h0 : ∀ q r : Fin k, Δ2 P (e1 q) (e1 r) = 0 := by
    intro q r
    rw [← ind_cs, ← ind_cs, delta_comb]
    exact hker _ _
  have hint := interp_aff hPq h0 z
  have hfix := (sol_iff_fix hR hc z).1 hz
  have hPz : P z = ∑ j, kv j * fz bI AI BI z j := by
    simp only [hPdef, Pi.zero_apply, add_zero, hfix]
  have hP0 : P 0 = ∑ j, kv j * FZ bI AI BI R (Fin.last k) (Fin.last k) j := by
    simp only [hPdef, Pi.zero_apply, add_zero, FZ, ptv_ll]
  have hPe : ∀ q, P (e1 q) = ∑ j, kv j * FZ bI AI BI R (Fin.castSucc q) (Fin.last k) j := by
    intro q
    simp only [hPdef, Pi.zero_apply, add_zero, FZ, ptv_last, ind_cs]
  have hNq : ∀ q : Fin k, NRZ bI AI BI yI R s (Fin.castSucc q) = P (e1 q) + P 0 := by
    intro q
    rw [hPe, hP0, ← Finset.sum_add_distrib]
    unfold NRZ
    apply Finset.sum_congr rfl; intro j _
    rw [if_neg (Fin.castSucc_ne_last q)]
    ring
  have hNl : NRZ bI AI BI yI R s (Fin.last k) = P 0 + ∑ j, kv j * toZ (yI j) := by
    rw [hP0, ← Finset.sum_add_distrib]
    unfold NRZ
    apply Finset.sum_congr rfl; intro j _
    rw [if_pos rfl]
    ring
  rw [Fin.sum_univ_castSucc]
  simp only [NRB, toZ_ofZ, ext_cs, ext_last, mul_one, hNq, hNl]
  have e1' : ∑ j, kv j * (fz bI AI BI z j + toZ (yI j)) =
      P z + ∑ j, kv j * toZ (yI j) := by
    rw [hPz, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [e1', hint]
  have e2 : ∑ i, (P (e1 i) + P 0) * z i = ∑ q, z q * (P (e1 q) + P 0) := by
    apply Finset.sum_congr rfl; intro q _; ring
  rw [e2]
  ring

theorem dot_eq_iff (l : Fin m → Bool) (x : Fin (2 ^ k)) :
    dotB l (fB bI AI BI x) = dotB l yI ↔
      ∑ j, zv l j * (fz bI AI BI (xz x) j + zv yI j) = 0 := by
  rw [← toZ_inj, dot_f_toZ, toZ_dotB]
  have : ∑ j, zv l j * (fz bI AI BI (xz x) j + zv yI j) =
      ∑ j, zv l j * fz bI AI BI (xz x) j + ∑ i, toZ (l i) * toZ (yI i) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
    simp only [zv]; ring
  rw [this]
  constructor
  · intro h; rw [h, z2]
  · intro h
    have := congrArg (· + ∑ i, toZ (l i) * toZ (yI i)) h
    simp only [zero_add] at this
    rw [← this, add_assoc, z2, add_zero]

theorem prune_step {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R) (x : Fin (2 ^ k)) :
    x ∈ SolX (stepR bI AI BI yI R) ↔ x ∈ SolX R ∧
      ∀ l, affOn (fB bI AI BI) (SolX R) l → dotB l (fB bI AI BI x) = dotB l yI := by
  simp only [SolX, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [stepR, stack_sol]
  by_cases hc : cons R
  · constructor
    · rintro ⟨hs, hn⟩
      refine ⟨hs, fun l hl => ?_⟩
      have hk := (ker_iff bI AI BI R (zv l)).1 ((aff_iff bI AI BI hR hc l).1 hl)
      rw [dot_eq_iff]
      have hsp := ker_span (R1B_gjf bI AI BI R) (R1B_zc bI AI BI R) (zv l) hk
      have e : ∑ j, zv l j * (fz bI AI BI (xz x) j + zv yI j) =
          ∑ s, zv l s * ∑ j, kvZ (R1B bI AI BI R) s j * (fz bI AI BI (xz x) j + toZ (yI j)) := by
        conv_lhs => rw [Finset.sum_congr rfl (fun j _ => by rw [hsp j])]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro s _
        apply Finset.sum_congr rfl; intro j _
        simp only [zv]; ring
      rw [e]
      apply Finset.sum_eq_zero
      intro s _
      rw [← nrow_meaning bI AI BI yI hR hc _ hs s, hn s, mul_zero]
    · rintro ⟨hs, hp⟩
      refine ⟨hs, fun s => ?_⟩
      rw [nrow_meaning bI AI BI yI hR hc _ hs s]
      set kv := kvZ (R1B bI AI BI R) s
      have hkv : (mat (R1B bI AI BI R)).mulVec (ext1 kv) = 0 :=
        kv_ker (R1B_gjf bI AI BI R) (R1B_zc bI AI BI R) s
      have hl : affOn (fB bI AI BI) (SolX R) (bvv kv) := by
        rw [aff_iff bI AI BI hR hc, zv_bvv]
        exact (ker_iff bI AI BI R kv).2 hkv
      have := (dot_eq_iff bI AI BI yI (bvv kv) x).1 (hp _ hl)
      rw [zv_bvv] at this
      exact this
  · have := not_cons_empty hR hc (xz x)
    simp only [this, false_and]

def R0 (k : ℕ) : Fin (k + 1) × Fin (k + 1) → Bool := fun _ => false

theorem R0_ok (k : ℕ) : FlatOK (R0 k) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp; simp [R0] at hp
  · intro q _ j; rfl
  · intro p q _; rfl

theorem R0_sol (k : ℕ) : SolX (R0 k) = Finset.univ := by
  ext x
  simp only [SolX, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  unfold Sol
  funext r
  simp [Matrix.mulVec, dotProduct, mat_eq_toZ, R0]

theorem iter_sol {prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))}
    (hp : IsPrune (fB bI AI BI) yI prune) :
    ∀ n, FlatOK ((stepR bI AI BI yI)^[n] (R0 k)) ∧
      SolX ((stepR bI AI BI yI)^[n] (R0 k)) = prune^[n] Finset.univ := by
  intro n
  induction n with
  | zero => exact ⟨R0_ok k, R0_sol k⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨stepMat_ok _ _, ?_⟩
    ext x
    rw [prune_step bI AI BI yI ih.1, hp, ih.2]

end step

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

theorem sgnZ_sum {ι : Type} (s : Finset ι) (x : ι → ZMod 2) :
    sgnZ (∑ i ∈ s, x i) = ∏ i ∈ s, sgnZ (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgnZ_add, ih]

theorem cnt_lt_rho {N : ℕ} (fl : Fin N → Bool) (j : Fin N) (hj : fl j = true) :
    cnt fl j.val < (Finset.univ.filter (fun q : Fin N => fl q = true)).card := by
  unfold cnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨j, by simp [hj], by simp⟩
  · intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨_, h2⟩
    exact h2

theorem cnt_strict {N : ℕ} (fl : Fin N → Bool) (j j' : Fin N) (h : j < j') (hj : fl j = true) :
    cnt fl j.val < cnt fl j'.val := by
  unfold cnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨j, by simp [h, hj, Fin.lt_def.1 h], by simp⟩
  · intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h1, h2⟩
    exact ⟨lt_trans h1 (Fin.lt_def.1 h), h2⟩

theorem cnt_inj {N : ℕ} (fl : Fin N → Bool) (j j' : Fin N) (hj : fl j = true)
    (hj' : fl j' = true) (h : cnt fl j.val = cnt fl j'.val) : j = j' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have := cnt_strict fl j j' h1 hj; omega
  · have := cnt_strict fl j' j h1 hj'; omega

section count
variable {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
  (BI : Fin m → Fin k → Fin k → Bool) (yI : Fin m → Bool)

theorem card_aff {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R) (hc : cons R)
    [DecidablePred (affOn (fB bI AI BI) (SolX R))] :
    (Finset.univ.filter (affOn (fB bI AI BI) (SolX R))).card =
      2 ^ (m - rho (R1B bI AI BI R)) := by
  rw [← ker_card (R1B_gjf bI AI BI R) (R1B_zc bI AI BI R)]
  apply Finset.card_nbij' zv bvv
  · intro l hl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hl ⊢
    exact (ker_iff bI AI BI R (zv l)).1 ((aff_iff bI AI BI hR hc l).1 hl)
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv ⊢
    rw [aff_iff bI AI BI hR hc, zv_bvv]
    exact (ker_iff bI AI BI R v).2 hv
  · intro l _; exact bvv_zv l
  · intro v _; exact zv_bvv v

theorem card_aff_empty {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R) (hc : ¬ cons R)
    [DecidablePred (affOn (fB bI AI BI) (SolX R))] :
    (Finset.univ.filter (affOn (fB bI AI BI) (SolX R))).card = 2 ^ m := by
  have hE : SolX R = ∅ := by
    ext x; simp [SolX, not_cons_empty hR hc]
  have : Finset.univ.filter (affOn (fB bI AI BI) (SolX R)) = Finset.univ := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    refine ⟨fun _ => false, false, fun z hz => ?_⟩
    rw [hE] at hz; simp at hz
  rw [this, Finset.card_univ]
  simp

def npiv {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => R (Fin.castSucc i, Fin.castSucc i) = true)).card

theorem piR_dep {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R) (u v : V k)
    (h : ∀ i, R (Fin.castSucc i, Fin.castSucc i) = false → u i = v i) : piR R u = piR R v := by
  funext i
  simp only [piR, mulVec_ext]
  have e : ∀ w : V k, w i + (∑ q, toZ (R (Fin.castSucc i, Fin.castSucc q)) * w q +
      toZ (R (Fin.castSucc i, Fin.last k))) =
      ∑ q, ((if q = i then 1 else 0) + toZ (R (Fin.castSucc i, Fin.castSucc q))) * w q +
        toZ (R (Fin.castSucc i, Fin.last k)) := by
    intro w
    simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  rw [e u, e v]
  congr 1
  apply Finset.sum_congr rfl; intro q _
  by_cases hq : R (Fin.castSucc q, Fin.castSucc q) = true
  · have := hR.1.1 _ hq (Fin.castSucc i)
    rw [this]
    by_cases hqi : q = i
    · subst hqi; simp [z2]
    · simp [hqi, Ne.symm hqi]
  · rw [h q (by simpa using hq)]

theorem fiber_sum {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R) (hc : cons R)
    (g : V k → ℤ) :
    ∑ u, g (piR R u) = 2 ^ npiv R * ∑ z ∈ Finset.univ.filter (Sol R), g z := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.filter (Sol R))
    (g := piR R) (fun u _ => by simp [sol_piR hR hc u]), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hzs : Sol R z := by simpa using hz
  have hfix := (sol_iff_fix hR hc z).1 hzs
  have e : ∀ u ∈ Finset.univ.filter (fun u => piR R u = z), g (piR R u) = g z := by
    intro u hu
    simp only [Finset.mem_filter] at hu
    rw [hu.2]
  rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hset : Finset.univ.filter (fun u => piR R u = z) =
      Fintype.piFinset (fun i : Fin k => if R (Fin.castSucc i, Fin.castSucc i) = true
        then (Finset.univ : Finset (ZMod 2)) else {z i}) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hu i
      by_cases hi : R (Fin.castSucc i, Fin.castSucc i) = true
      · simp [hi]
      · simp only [hi, Bool.false_eq_true, if_false, Finset.mem_singleton]
        have := congrFun hu i
        simp only [piR, mulVec_ext, hR.1.2 _ (by simpa using hi), toZ_false, zero_mul,
          Finset.sum_const_zero, add_zero] at this
        exact this
    · intro hu
      rw [← hfix]
      apply piR_dep hR
      intro i hi
      have := hu i
      simp only [hi, Bool.false_eq_true, if_false, Finset.mem_singleton] at this
      exact this
  rw [hset, Fintype.card_piFinset]
  have : ∀ i : Fin k, (if R (Fin.castSucc i, Fin.castSucc i) = true
      then (Finset.univ : Finset (ZMod 2)) else {z i}).card =
      if R (Fin.castSucc i, Fin.castSucc i) = true then 2 else 1 := by
    intro i; split <;> simp
  simp only [this]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  push_cast
  rfl

def wS {D : ℕ} (h' : ℕ) (R1 : Fin (m + D) × Fin (m + D) → Bool) (σ : Fin h' → Bool)
    (j : Fin m) : Bool :=
  piv R1 j && decide (∃ s : Fin h', σ s = true ∧ cnt (piv R1) j.val = s.val)

def validS {D : ℕ} (h' : ℕ) (R1 : Fin (m + D) × Fin (m + D) → Bool) (σ : Fin h' → Bool) : Bool :=
  decide (∀ s : Fin h', σ s = true → s.val < rho R1)

theorem orth_zero {D : ℕ} {R1 : Fin (m + D) × Fin (m + D) → Bool} (hR : GJF R1) (d : V m)
    (hd : ∀ s, ∑ j, kvZ R1 s j * d j = 0) (hp : ∀ j, piv R1 j = true → d j = 0) :
    ∀ j, d j = 0 := by
  intro j
  by_cases hj : piv R1 j = true
  · exact hp j hj
  · have := hd j
    have e : ∀ j', kvZ R1 j j' * d j' = if j' = j then d j' else 0 := by
      intro j'
      unfold kvZ
      simp only [piv] at hj
      simp only [hj, Bool.false_eq_true, if_false]
      by_cases hjj : j' = j
      · subst hjj
        rw [hR.2 _ (by simpa using hj)]
        simp
      · by_cases hp' : R1 (Fin.castAdd D j', Fin.castAdd D j') = true
        · rw [hp j' hp']; simp
        · rw [hR.2 _ (by simpa using hp')]
          simp [hjj]
    rw [Finset.sum_congr rfl (fun j' _ => e j')] at this
    simpa using this

theorem slot_sum {D : ℕ} (h' : ℕ) {R1 : Fin (m + D) × Fin (m + D) → Bool} (hR : GJF R1)
    (hrho : rho R1 ≤ h') (d : V m) (hd : ∀ s, ∑ j, kvZ R1 s j * d j = 0) :
    ∑ σ : Fin h' → Bool, (if validS h' R1 σ = true then sgnZ (∑ j, toZ (wS h' R1 σ j) * d j)
      else 0) = 2 ^ rho R1 * (if ∀ j, d j = 0 then 1 else 0) := by
  classical
  set ρ := rho R1 with hρ
  set c := fun j : Fin m => cnt (piv R1) j.val with hcdef
  let δ : Fin h' → ZMod 2 := fun s => ∑ j, if piv R1 j = true ∧ c j = s.val then d j else 0
  have hF1 : ∀ j, piv R1 j = true → c j < ρ := fun j hj => cnt_lt_rho (piv R1) j hj
  have hS1 : ∀ σ : Fin h' → Bool, ∑ j, toZ (wS h' R1 σ j) * d j = ∑ s, toZ (σ s) * δ s := by
    intro σ
    have e : ∀ j, toZ (wS h' R1 σ j) * d j =
        ∑ s, toZ (σ s) * (if piv R1 j = true ∧ c j = s.val then d j else 0) := by
      intro j
      unfold wS
      by_cases hj : piv R1 j = true
      · have hlt : c j < h' := lt_of_lt_of_le (hF1 j hj) hrho
        have hex : decide (∃ s : Fin h', σ s = true ∧ cnt (piv R1) j.val = s.val) =
            σ ⟨c j, hlt⟩ := by
          by_cases hs : σ ⟨c j, hlt⟩ = true
          · rw [hs]; simp only [decide_eq_true_eq]; exact ⟨⟨c j, hlt⟩, hs, rfl⟩
          · simp only [Bool.not_eq_true] at hs
            rw [hs]; simp only [decide_eq_false_iff_not, not_exists, not_and]
            intro s hs' hcs
            have : s = ⟨c j, hlt⟩ := Fin.ext hcs.symm
            rw [this, hs] at hs'; exact absurd hs' (by simp)
        rw [hj, Bool.true_and, hex]
        rw [Finset.sum_eq_single ⟨c j, hlt⟩]
        · simp [hj]
        · intro s _ hs
          have : ¬ (c j = s.val) := fun h => hs (Fin.ext h.symm)
          simp [this]
        · simp
      · simp only [Bool.not_eq_true] at hj
        simp [hj]
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    rw [Finset.mul_sum]
  let φ : Fin h' → Bool → ℤ := fun s b =>
    (if b = true ∧ ¬ s.val < ρ then 0 else 1) * sgnZ (toZ b * δ s)
  have hS3 : ∀ σ : Fin h' → Bool, (if validS h' R1 σ = true then
      sgnZ (∑ j, toZ (wS h' R1 σ j) * d j) else 0) = ∏ s, φ s (σ s) := by
    intro σ
    rw [hS1 σ]
    by_cases hv : validS h' R1 σ = true
    · rw [if_pos hv, sgnZ_sum]
      apply Finset.prod_congr rfl; intro s _
      simp only [validS, decide_eq_true_eq] at hv
      have : ¬ (σ s = true ∧ ¬ s.val < ρ) := by
        rintro ⟨h1, h2⟩; exact h2 (hv s h1)
      simp only [φ, this, if_false, one_mul]
    · rw [if_neg hv]
      simp only [validS, decide_eq_true_eq, not_forall] at hv
      obtain ⟨s, hs1, hs2⟩ := hv
      rw [← hρ] at hs2
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ s)
      simp [φ, hs1, hs2]
  rw [Finset.sum_congr rfl (fun σ _ => hS3 σ)]
  rw [← Fintype.prod_sum (fun s b => φ s b)]
  have hS4 : ∀ s, ∑ b, φ s b = 1 + (if s.val < ρ then sgnZ (δ s) else 0) := by
    intro s
    rw [Fintype.sum_bool]
    by_cases hs : s.val < ρ
    · have : ¬ (ρ ≤ s.val) := not_le.mpr hs
      simp [φ, hs, this, sgnZ_zero]
      ring
    · simp [φ, hs, sgnZ_zero]
  simp only [hS4]
  have hS6 : (∀ s : Fin h', s.val < ρ → δ s = 0) ↔ ∀ j, piv R1 j = true → d j = 0 := by
    constructor
    · intro h j hj
      have hlt : c j < h' := lt_of_lt_of_le (hF1 j hj) hrho
      have := h ⟨c j, hlt⟩ (hF1 j hj)
      simp only [δ] at this
      rw [Finset.sum_eq_single j] at this
      · simpa [hj] using this
      · intro j' _ hj'
        by_cases hp' : piv R1 j' = true
        · have : ¬ (c j' = c j) := fun h => hj' (cnt_inj _ j' j hp' hj h)
          simp [this]
        · simp [hp']
      · simp
    · intro h s _
      simp only [δ]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : piv R1 j = true
      · simp [h j hj]
      · simp [hj]
  by_cases hall : ∀ j, d j = 0
  · rw [if_pos hall]
    have hδ : ∀ s : Fin h', s.val < ρ → δ s = 0 := hS6.2 (fun j _ => hall j)
    have e : ∀ s : Fin h', (1 + (if s.val < ρ then sgnZ (δ s) else 0) : ℤ) =
        if s.val < ρ then 2 else 1 := by
      intro s
      by_cases hs : s.val < ρ
      · simp [hs, hδ s hs, sgnZ_zero]
        try norm_num
      · simp [hs]
    rw [Finset.prod_congr rfl (fun s _ => e s), Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one, mul_one]
    congr 1
    rw [Fin.card_filter_val_lt]
    omega
  · rw [if_neg hall, mul_zero]
    have hnot : ¬ ∀ j, piv R1 j = true → d j = 0 := fun h => hall (orth_zero hR d hd h)
    rw [← hS6] at hnot
    simp only [not_forall] at hnot
    obtain ⟨s, hs, hδs⟩ := hnot
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    rcases z01 (δ s) with h0 | h1
    · exact absurd h0 hδs
    · simp [hs, h1, sgnZ_one]

end count

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

section slots
variable {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
  (BI : Fin m → Fin k → Fin k → Bool) (yI : Fin m → Bool) (h' : ℕ)

def Pt (R : Fin (k + 1) × Fin (k + 1) → Bool) (σ : Fin h' → Bool) (a b : Fin (k + 1)) : ZMod 2 :=
  ∑ j, toZ (wS h' (R1B bI AI BI R) σ j) * (FZ bI AI BI R a b j + toZ (yI j))

def coefC (R : Fin (k + 1) × Fin (k + 1) → Bool) (σ : Fin h' → Bool) : Bool :=
  ofZ (Pt bI AI BI yI h' R σ (Fin.last k) (Fin.last k))

def coefA (R : Fin (k + 1) × Fin (k + 1) → Bool) (σ : Fin h' → Bool) (q : Fin k) : Bool :=
  ofZ (Pt bI AI BI yI h' R σ q.castSucc (Fin.last k) +
    Pt bI AI BI yI h' R σ (Fin.last k) (Fin.last k))

def coefG (R : Fin (k + 1) × Fin (k + 1) → Bool) (σ : Fin h' → Bool) (p : Fin k × Fin k) : Bool :=
  decide (p.1 < p.2) && ofZ (Pt bI AI BI yI h' R σ p.1.castSucc p.2.castSucc +
    Pt bI AI BI yI h' R σ p.1.castSucc (Fin.last k) +
    Pt bI AI BI yI h' R σ p.2.castSucc (Fin.last k) +
    Pt bI AI BI yI h' R σ (Fin.last k) (Fin.last k))

def PS (R : Fin (k + 1) × Fin (k + 1) → Bool) (σ : Fin h' → Bool) (u : V k) : ZMod 2 :=
  ∑ j, toZ (wS h' (R1B bI AI BI R) σ j) * (fz bI AI BI (piR R u) j + zv yI j)

theorem Pt_PS (R : Fin (k + 1) × Fin (k + 1) → Bool) (σ : Fin h' → Bool) (a b : Fin (k + 1)) :
    Pt bI AI BI yI h' R σ a b = PS bI AI BI yI h' R σ (ptv a b) := rfl

theorem evalQ_coef (R : Fin (k + 1) × Fin (k + 1) → Bool) (σ : Fin h' → Bool) (u : V k) :
    evalQ (coefC bI AI BI yI h' R σ) (coefA bI AI BI yI h' R σ) (coefG bI AI BI yI h' R σ) u =
      PS bI AI BI yI h' R σ u := by
  have hq : IsQuad (PS bI AI BI yI h' R σ) :=
    comb_quad bI AI BI R (zv (wS h' (R1B bI AI BI R) σ)) (zv yI)
  rw [interp hq u]
  unfold evalQ coefC coefA coefG
  simp only [Pt_PS, toZ_ofZ, ptv_ll, ptv_last, ind_cs, ind_last, toZ_and, toZ_decide]
  have hpt : ∀ q r : Fin k, ptv q.castSucc r.castSucc = e1 q + e1 r := by
    intro q r; simp [ptv, ind_cs]
  simp only [hpt]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl; intro q _; ring
  · apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro r _
    by_cases h : q < r
    · simp only [h, if_true, one_mul, Δ2]; ring
    · simp [h]

def Tsum (R : Fin (k + 1) × Fin (k + 1) → Bool) : ℤ :=
  ∑ σ : Fin h' → Bool, if validS h' (R1B bI AI BI R) σ = true then
    gsum (coefC bI AI BI yI h' R σ) (coefA bI AI BI yI h' R σ) (coefG bI AI BI yI h' R σ) else 0

def hitsV (R : Fin (k + 1) × Fin (k + 1) → Bool) : ℕ :=
  (Finset.univ.filter (fun z : V k => Sol R z ∧ ∀ j, fz bI AI BI z j = toZ (yI j))).card

theorem orth_of_fix {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R) (hc : cons R)
    (hfix : ∀ x ∈ SolX R, ∀ l, affOn (fB bI AI BI) (SolX R) l →
      dotB l (fB bI AI BI x) = dotB l yI)
    (z : V k) (hz : Sol R z) (s : Fin m) :
    ∑ j, kvZ (R1B bI AI BI R) s j * (fz bI AI BI z j + toZ (yI j)) = 0 := by
  set x := (xzE k).symm z with hx
  have hxz : xz x = z := xz_xzE z
  have hxS : x ∈ SolX R := by
    simp only [SolX, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hxz]; exact hz
  set kv := kvZ (R1B bI AI BI R) s
  have hkv : (mat (R1B bI AI BI R)).mulVec (ext1 kv) = 0 :=
    kv_ker (R1B_gjf bI AI BI R) (R1B_zc bI AI BI R) s
  have hl : affOn (fB bI AI BI) (SolX R) (bvv kv) := by
    rw [aff_iff bI AI BI hR hc, zv_bvv]
    exact (ker_iff bI AI BI R kv).2 hkv
  have := (dot_eq_iff bI AI BI yI (bvv kv) x).1 (hfix x hxS _ hl)
  rw [zv_bvv, hxz] at this
  exact this

theorem T_eq {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R) (hc : cons R)
    (hfix : ∀ x ∈ SolX R, ∀ l, affOn (fB bI AI BI) (SolX R) l →
      dotB l (fB bI AI BI x) = dotB l yI)
    (hrho : rho (R1B bI AI BI R) ≤ h') :
    Tsum bI AI BI yI h' R = 2 ^ npiv R * 2 ^ rho (R1B bI AI BI R) * hitsV bI AI BI yI R := by
  classical
  unfold Tsum
  set R1 := R1B bI AI BI R with hR1
  have hg : ∀ σ, gsum (coefC bI AI BI yI h' R σ) (coefA bI AI BI yI h' R σ)
      (coefG bI AI BI yI h' R σ) = 2 ^ npiv R * ∑ z ∈ Finset.univ.filter (Sol R),
        sgnZ (∑ j, toZ (wS h' R1 σ j) * (fz bI AI BI z j + toZ (yI j))) := by
    intro σ
    unfold gsum
    simp only [evalQ_coef]
    exact fiber_sum hR hc (fun z => sgnZ (∑ j, toZ (wS h' R1 σ j) * (fz bI AI BI z j + zv yI j)))
  simp only [hg]
  have e1 : ∀ σ : Fin h' → Bool, (if validS h' R1 σ = true then 2 ^ npiv R *
      ∑ z ∈ Finset.univ.filter (Sol R),
        sgnZ (∑ j, toZ (wS h' R1 σ j) * (fz bI AI BI z j + toZ (yI j))) else (0 : ℤ)) =
      2 ^ npiv R * ∑ z ∈ Finset.univ.filter (Sol R),
        (if validS h' R1 σ = true then
          sgnZ (∑ j, toZ (wS h' R1 σ j) * (fz bI AI BI z j + toZ (yI j))) else 0) := by
    intro σ
    split
    · rfl
    · simp
  simp only [e1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have e2 : ∀ z ∈ Finset.univ.filter (Sol R), ∑ σ : Fin h' → Bool,
      (if validS h' R1 σ = true then
        sgnZ (∑ j, toZ (wS h' R1 σ j) * (fz bI AI BI z j + toZ (yI j))) else 0) =
      2 ^ rho R1 * (if ∀ j, fz bI AI BI z j + toZ (yI j) = 0 then 1 else 0) := by
    intro z hz
    have hzs : Sol R z := by simpa using hz
    exact slot_sum h' (R1B_gjf bI AI BI R) hrho _ (orth_of_fix bI AI BI yI hR hc hfix z hzs)
  rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, Finset.sum_boole, mul_assoc]
  congr 2
  unfold hitsV
  rw [Finset.filter_filter]
  congr 2
  apply Finset.filter_congr
  intro z _
  simp only [and_congr_right_iff]
  intro _
  constructor
  · intro h j; have := h j; rw [← zsub, sub_eq_zero] at this; exact this
  · intro h j; rw [h j, z2]

theorem hits_eq {R : Fin (k + 1) × Fin (k + 1) → Bool}
    (hsub : Finset.univ.filter (fun x => fB bI AI BI x = yI) ⊆ SolX R) :
    Nat.card {x : Fin (2 ^ k) // fB bI AI BI x = yI} = hitsV bI AI BI yI R := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold hitsV
  apply Finset.card_nbij' xz (xzE k).symm
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    have hS := hsub (by simpa using hx)
    simp only [SolX, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    refine ⟨hS, fun j => ?_⟩
    rw [← toZ_fB, hx]
  · intro z hz
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hz ⊢
    funext j
    rw [← toZ_inj, toZ_fB, xz_xzE, hz.2 j]
  · intro x _
    exact (xzE k).symm_apply_apply x
  · intro z _
    exact xz_xzE z

end slots

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

theorem Cmp.thn {ι κ μ : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    {G : (ι ⊕ κ → Bool) → μ → Bool} (h1 : Cmp ι κ S F) (h2 : Cmp (ι ⊕ κ) μ S' G) :
    Cmp ι μ (S + S') (fun v => G (Sum.elim v (F v))) :=
  Cmp.comp (Cmp.keep h1) h2

theorem ofZ_sum_toZ {I : Type} [Fintype I] (φ : I → Bool) :
    ofZ (∑ i, toZ (φ i)) = decide ((Finset.univ.filter (fun i => φ i = true)).card % 2 = 1) := by
  have : ∑ i, toZ (φ i) = ((Finset.univ.filter (fun i => φ i = true)).card : ZMod 2) := by
    rw [← Finset.sum_boole]; rfl
  rw [this]
  unfold ofZ
  rw [← ZMod.natCast_mod _ 2]
  rcases Nat.mod_two_eq_zero_or_one (Finset.univ.filter (fun i => φ i = true)).card with h | h <;>
    simp [h]

theorem Cb.sumZ {ι I : Type} [Fintype I] {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (Fintype.card I * (s + 4) + 1) (fun v => ofZ (∑ i, toZ (φ i v))) :=
  Cb.congr (Cb.bigXor h) (fun v => (ofZ_sum_toZ _).symm)

theorem Cb.condVar {ι : Type} (c : Prop) [Decidable c] (i : ι) :
    Cb ι 1 (fun v => if c then false else v i) := by
  by_cases hc : c
  · exact Cb.congr (Cb.const false) (fun v => by simp [hc])
  · exact Cb.congr (Cb.mono (Cb.var i) (by omega)) (fun v => by simp [hc])

theorem Cb.iteVar {ι : Type} (c : Prop) [Decidable c] (i i' : ι) :
    Cb ι 0 (fun v => if c then v i else v i') := by
  by_cases hc : c
  · exact Cb.congr (Cb.var i) (fun v => by simp [hc])
  · exact Cb.congr (Cb.var i') (fun v => by simp [hc])

theorem Cb.optVar {ι : Type} (o : Option ι) : Cb ι 1 (fun v => o.elim false v) := by
  cases o with
  | none => exact Cb.congr (Cb.const false) (fun v => rfl)
  | some i => exact Cb.mono (Cb.var i) (by omega)

structure Sl (ι : Type) (k m : ℕ) where
  b : Fin m → ι
  A : Fin m → Fin k → ι
  B : Fin m → Fin k → Fin k → ι
  y : Fin m → ι
  R : Fin (k + 1) × Fin (k + 1) → ι

def Sl.vb {ι : Type} {k m : ℕ} (sl : Sl ι k m) (v : ι → Bool) : Fin m → Bool := fun j => v (sl.b j)
def Sl.vA {ι : Type} {k m : ℕ} (sl : Sl ι k m) (v : ι → Bool) : Fin m → Fin k → Bool :=
  fun j i => v (sl.A j i)
def Sl.vB {ι : Type} {k m : ℕ} (sl : Sl ι k m) (v : ι → Bool) : Fin m → Fin k → Fin k → Bool :=
  fun j i p => v (sl.B j i p)
def Sl.vy {ι : Type} {k m : ℕ} (sl : Sl ι k m) (v : ι → Bool) : Fin m → Bool := fun j => v (sl.y j)
def Sl.vR {ι : Type} {k m : ℕ} (sl : Sl ι k m) (v : ι → Bool) : Fin (k + 1) × Fin (k + 1) → Bool :=
  fun p => v (sl.R p)

def NN (k m : ℕ) : ℕ := k + m + 4

theorem NN_k {k m : ℕ} : k + 1 ≤ NN k m := by unfold NN; omega
theorem NN_m {k m : ℕ} : m ≤ NN k m := by unfold NN; omega
theorem NN_4 {k m : ℕ} : 4 ≤ NN k m := by unfold NN; omega

theorem pow_mono_N {N a b : ℕ} (hN : 1 ≤ N) (h : a ≤ b) : N ^ a ≤ N ^ b :=
  Nat.pow_le_pow_right hN h

theorem piR_ptv {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) (a b : Fin (k + 1)) (i : Fin k) :
    piR R (ptv a b) i = toZ (decide (Fin.castSucc i = a)) + toZ (decide (Fin.castSucc i = b)) +
      (if a = Fin.last k then 0 else toZ (R (Fin.castSucc i, a))) +
      (if b = Fin.last k then 0 else toZ (R (Fin.castSucc i, b))) +
      toZ (R (Fin.castSucc i, Fin.last k)) := by
  have hs : ∀ c : Fin (k + 1), ∑ q : Fin k, toZ (R (Fin.castSucc i, Fin.castSucc q)) * ind c q =
      if c = Fin.last k then 0 else toZ (R (Fin.castSucc i, c)) := by
    intro c
    refine Fin.lastCases ?_ (fun c' => ?_) c
    · simp [ind, Fin.castSucc_ne_last]
    · simp [ind, Fin.castSucc_inj, Fin.castSucc_ne_last]
  simp only [piR, mulVec_ext, ptv, Pi.add_apply, mul_add, Finset.sum_add_distrib, hs]
  simp only [ind, toZ_decide]
  ring

theorem cPT {ι : Type} {k m : ℕ} (sl : Sl ι k m) :
    Cmp ι (Fin (k + 1) × Fin (k + 1) × Fin k) ((k + 1) * (k + 1) * k * 21)
      (fun v p => ofZ (piR (sl.vR v) (ptv p.1 p.2.1) p.2.2)) := by
  have h : ∀ p : Fin (k + 1) × Fin (k + 1) × Fin k,
      Cb ι 21 (fun v => ofZ (piR (sl.vR v) (ptv p.1 p.2.1) p.2.2)) := by
    rintro ⟨a, b, i⟩
    have c := Cb.xor (Cb.xor (Cb.xor (Cb.xor (Cb.const (ι := ι) (decide (Fin.castSucc i = a)))
      (Cb.const (decide (Fin.castSucc i = b)))) (Cb.condVar (a = Fin.last k) (sl.R (Fin.castSucc i, a))))
      (Cb.condVar (b = Fin.last k) (sl.R (Fin.castSucc i, b)))) (Cb.var (sl.R (Fin.castSucc i, Fin.last k)))
    refine Cb.mono (Cb.congr c ?_) (by norm_num)
    intro v
    rw [← toZ_inj, toZ_ofZ, piR_ptv]
    simp only [toZ_xor, Sl.vR]
    congr 1
    congr 1
    · congr 1
      split <;> rfl
    · split <;> rfl
  have := Cmp.ofBits h
  simp only [Fintype.card_prod, Fintype.card_fin] at this
  refine Cmp.mono this (le_of_eq ?_)
  ring

theorem cFB {ι : Type} {k m : ℕ} (sl : Sl ι k m) :
    Cmp ι (Fin (k + 1) × Fin (k + 1) × Fin m) (64 * NN k m ^ 5)
      (fun v p => ofZ (FZ (sl.vb v) (sl.vA v) (sl.vB v) (sl.vR v) p.1 p.2.1 p.2.2)) := by
  have h2 : ∀ p : Fin (k + 1) × Fin (k + 1) × Fin m,
      Cb (ι ⊕ (Fin (k + 1) × Fin (k + 1) × Fin k)) (k * 5 + 1 + (k * k * 6 + 1) + 8)
        (fun w => xor (w (Sum.inl (sl.b p.2.2)))
          (xor (ofZ (∑ i : Fin k, toZ (w (Sum.inl (sl.A p.2.2 i)) &&
              w (Sum.inr (p.1, p.2.1, i)))))
            (ofZ (∑ ip : Fin k × Fin k, toZ ((w (Sum.inl (sl.B p.2.2 ip.1 ip.2)) &&
              w (Sum.inr (p.1, p.2.1, ip.1))) && w (Sum.inr (p.1, p.2.1, ip.2))))))) := by
    rintro ⟨a, b, j⟩
    have c1 := Cb.sumZ (ι := ι ⊕ (Fin (k + 1) × Fin (k + 1) × Fin k)) (I := Fin k)
      (fun i => Cb.and (Cb.var (Sum.inl (sl.A j i))) (Cb.var (Sum.inr (a, b, i))))
    have c2 := Cb.sumZ (ι := ι ⊕ (Fin (k + 1) × Fin (k + 1) × Fin k)) (I := Fin k × Fin k)
      (fun ip => Cb.and (Cb.and (Cb.var (Sum.inl (sl.B j ip.1 ip.2)))
        (Cb.var (Sum.inr (a, b, ip.1)))) (Cb.var (Sum.inr (a, b, ip.2))))
    have c := Cb.xor (Cb.var (Sum.inl (sl.b j))) (Cb.xor c1 c2)
    simp only [Fintype.card_fin, Fintype.card_prod] at c
    exact Cb.mono c (by ring_nf; omega)
  have h3 := Cmp.thn (cPT sl) (Cmp.ofBits h2)
  simp only [Fintype.card_prod, Fintype.card_fin] at h3
  refine Cmp.mono (Cmp.congr h3 ?_) ?_
  · intro v p
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← toZ_inj, toZ_ofZ]
    simp only [toZ_xor, toZ_ofZ, toZ_and, FZ, fz, Fintype.sum_prod_type, Sl.vb, Sl.vA, Sl.vB]
    ring
  · have hk : k + 1 ≤ NN k m := NN_k
    have hm : m ≤ NN k m := NN_m
    have h4 : 4 ≤ NN k m := NN_4
    set N := NN k m
    have e1 : (k + 1) * (k + 1) * k * 21 ≤ 21 * N ^ 3 := by
      calc (k + 1) * (k + 1) * k * 21 ≤ N * N * N * 21 := by gcongr <;> omega
        _ = 21 * N ^ 3 := by ring
    have e2 : (k + 1) * (k + 1) * m * (k * 5 + 1 + (k * k * 6 + 1) + 8) ≤
        N * N * N * (N * 5 + 1 + (N * N * 6 + 1) + 8) := by gcongr <;> omega
    have e3 : N * N * N * (N * 5 + 1 + (N * N * 6 + 1) + 8) + 21 * N ^ 3 =
        6 * N ^ 5 + 5 * N ^ 4 + 31 * N ^ 3 := by ring
    have p4 : N ^ 4 ≤ N ^ 5 := pow_mono_N (by omega) (by norm_num)
    have p3 : N ^ 3 ≤ N ^ 5 := pow_mono_N (by omega) (by norm_num)
    have : (k + 1) * (k + 1) * k * 21 + (k + 1) * ((k + 1) * m) * (k * 5 + 1 + (k * k * 6 + 1) + 8)
        = (k + 1) * (k + 1) * k * 21 + (k + 1) * (k + 1) * m * (k * 5 + 1 + (k * k * 6 + 1) + 8) :=
      by ring
    rw [this]
    calc (k + 1) * (k + 1) * k * 21 + (k + 1) * (k + 1) * m * (k * 5 + 1 + (k * k * 6 + 1) + 8)
        ≤ 21 * N ^ 3 + N * N * N * (N * 5 + 1 + (N * N * 6 + 1) + 8) := add_le_add e1 e2
      _ = 6 * N ^ 5 + 5 * N ^ 4 + 31 * N ^ 3 := by rw [← e3]; ring
      _ ≤ 6 * N ^ 5 + 5 * N ^ 5 + 31 * N ^ 5 := by gcongr
      _ = 42 * N ^ 5 := by ring
      _ ≤ 64 * N ^ 5 := Nat.mul_le_mul_right _ (by norm_num)

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

theorem cCB {ι : Type} {k m : ℕ} (sl : Sl ι k m) :
    Cmp ι (Fin (k + 1) × Fin (k + 1) × Fin m) (128 * NN k m ^ 5)
      (fun v p => CBB (sl.vb v) (sl.vA v) (sl.vB v) (sl.vR v) p.1 p.2.1 p.2.2) := by
  have h2 : ∀ p : Fin (k + 1) × Fin (k + 1) × Fin m,
      Cb (Fin (k + 1) × Fin (k + 1) × Fin m) 12
        (fun w => xor (xor (xor (w (p.1, p.2.1, p.2.2)) (w (p.1, Fin.last k, p.2.2)))
          (w (p.2.1, Fin.last k, p.2.2))) (w (Fin.last k, Fin.last k, p.2.2))) := by
    rintro ⟨a, b, j⟩
    exact Cb.mono (Cb.xor (Cb.xor (Cb.xor (Cb.var _) (Cb.var _)) (Cb.var _)) (Cb.var _))
      (by norm_num)
  have h3 := Cmp.comp (cFB sl) (Cmp.ofBits h2)
  simp only [Fintype.card_prod, Fintype.card_fin] at h3
  refine Cmp.mono (Cmp.congr h3 ?_) ?_
  · intro v p
    simp only [CBB, CZ, ofZ_add]
  · have hk : k + 1 ≤ NN k m := NN_k
    have hm : m ≤ NN k m := NN_m
    set N := NN k m
    have e : (k + 1) * ((k + 1) * m) * 12 ≤ N * (N * N) * 12 := by gcongr
    have p3 : N ^ 3 ≤ N ^ 5 := pow_mono_N (by omega) (by norm_num)
    have : N * (N * N) * 12 = 12 * N ^ 3 := by ring
    omega

def m1sel {k m : ℕ} (p : Fin (m + (k + 1) * (k + 1)) × Fin (m + (k + 1) * (k + 1))) :
    Option (Fin (k + 1) × Fin (k + 1) × Fin m) :=
  splitF (fun _ : Fin m => none)
    (fun pr => splitF (fun j : Fin m => some ((pairOf pr).1, (pairOf pr).2, j)) (fun _ => none) p.2)
    p.1

theorem M1_opt {k m : ℕ} (w : Fin (k + 1) × Fin (k + 1) × Fin m → Bool)
    (p : Fin (m + (k + 1) * (k + 1)) × Fin (m + (k + 1) * (k + 1))) :
    M1 (fun a b j => w (a, b, j)) p = (m1sel p).elim false w := by
  unfold M1 m1sel splitF
  split_ifs <;> rfl

theorem cR1 {ι : Type} {k m : ℕ} (sl : Sl ι k m) :
    Cmp ι (Fin (m + (k + 1) * (k + 1)) × Fin (m + (k + 1) * (k + 1))) (256 * NN k m ^ 8)
      (fun v => R1B (sl.vb v) (sl.vA v) (sl.vB v) (sl.vR v)) := by
  have hM : Cmp (Fin (k + 1) × Fin (k + 1) × Fin m)
      (Fin (m + (k + 1) * (k + 1)) × Fin (m + (k + 1) * (k + 1)))
      (Fintype.card (Fin (m + (k + 1) * (k + 1)) × Fin (m + (k + 1) * (k + 1))) * 1)
      (fun w p => (m1sel p).elim false w) := Cmp.ofBits (fun p => Cb.optVar (m1sel p))
  have h3 := Cmp.comp (Cmp.comp (cCB sl) hM) (cmp_gj (m + (k + 1) * (k + 1)))
  simp only [Fintype.card_prod, Fintype.card_fin] at h3
  refine Cmp.mono (Cmp.congr h3 ?_) ?_
  · intro v p
    simp only [R1B]
    congr 1
    funext q
    rw [← M1_opt]
  · have hk : k + 1 ≤ NN k m := NN_k
    have hm : m ≤ NN k m := NN_m
    have h4 : 4 ≤ NN k m := NN_4
    have hN : NN k m = k + m + 4 := rfl
    set N := NN k m
    have hD : m + (k + 1) * (k + 1) + 1 ≤ N * N := by rw [hN]; nlinarith
    have e1 : (m + (k + 1) * (k + 1)) * (m + (k + 1) * (k + 1)) * 1 ≤ N * N * (N * N) := by
      have : m + (k + 1) * (k + 1) ≤ N * N := by omega
      calc _ = (m + (k + 1) * (k + 1)) * (m + (k + 1) * (k + 1)) := by ring
        _ ≤ N * N * (N * N) := Nat.mul_le_mul this this
    have e2 : gjCost (m + (k + 1) * (k + 1)) ≤ 32 * (N * N) ^ 4 := by
      unfold gjCost
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 4)
    have p5 : N ^ 5 ≤ N ^ 8 := pow_mono_N (by omega) (by norm_num)
    have p4 : N ^ 4 ≤ N ^ 8 := pow_mono_N (by omega) (by norm_num)
    have a1 : N * N * (N * N) = N ^ 4 := by ring
    have a2 : (N * N) ^ 4 = N ^ 8 := by ring
    rw [a1] at e1
    rw [a2] at e2
    omega

theorem cKV {ι : Type} {k m : ℕ} (sl : Sl ι k m) :
    Cmp ι (Fin m × Fin m) (512 * NN k m ^ 8)
      (fun v p => ofZ (kvZ (R1B (sl.vb v) (sl.vA v) (sl.vB v) (sl.vR v)) p.1 p.2)) := by
  have h2 : ∀ p : Fin m × Fin m,
      Cb (Fin (m + (k + 1) * (k + 1)) × Fin (m + (k + 1) * (k + 1))) 7
        (fun w => (!w (Fin.castAdd _ p.1, Fin.castAdd _ p.1)) &&
          xor (decide (p.2 = p.1)) (w (Fin.castAdd _ p.2, Fin.castAdd _ p.1))) := by
    rintro ⟨s, j⟩
    exact Cb.mono (Cb.and (Cb.not (Cb.var _)) (Cb.xor (Cb.const _) (Cb.var _))) (by norm_num)
  have h3 := Cmp.comp (cR1 sl) (Cmp.ofBits h2)
  simp only [Fintype.card_prod, Fintype.card_fin] at h3
  refine Cmp.mono (Cmp.congr h3 ?_) ?_
  · rintro v ⟨s, j⟩
    simp only [kvZ]
    split
    · rename_i h; simp [h]; rfl
    · rename_i h
      simp only [Bool.not_eq_true] at h
      rw [h, Bool.not_false, Bool.true_and, ← toZ_inj, toZ_ofZ, toZ_xor, toZ_decide]
  · have hm : m ≤ NN k m := NN_m
    have h4 : 4 ≤ NN k m := NN_4
    set N := NN k m
    have e : m * m * 7 ≤ N * N * 7 := by gcongr
    have p2 : N ^ 2 ≤ N ^ 8 := pow_mono_N (by omega) (by norm_num)
    have : N * N * 7 = 7 * N ^ 2 := by ring
    omega

theorem cNR {ι : Type} {k m : ℕ} (sl : Sl ι k m) :
    Cmp ι (Fin m × Fin (k + 1)) (1024 * NN k m ^ 8)
      (fun v p => NRB (sl.vb v) (sl.vA v) (sl.vB v) (sl.vy v) (sl.vR v) p.1 p.2) := by
  have h2 : ∀ p : Fin m × Fin (k + 1),
      Cb ((Fin m × Fin m) ⊕ ((Fin (k + 1) × Fin (k + 1) × Fin m) ⊕ Fin m)) (m * 9 + 1)
        (fun w => ofZ (∑ j : Fin m, toZ (w (Sum.inl (p.1, j)) &&
          xor (w (Sum.inr (Sum.inl (p.2, Fin.last k, j))))
            (if p.2 = Fin.last k then w (Sum.inr (Sum.inr j))
             else w (Sum.inr (Sum.inl (Fin.last k, Fin.last k, j))))))) := by
    rintro ⟨s, b⟩
    have c := Cb.sumZ (I := Fin m) (fun j => Cb.and (Cb.var (Sum.inl (s, j)))
      (Cb.xor (Cb.var (Sum.inr (Sum.inl (b, Fin.last k, j))))
        (Cb.iteVar (b = Fin.last k) (Sum.inr (Sum.inr j))
          (Sum.inr (Sum.inl (Fin.last k, Fin.last k, j))))))
    simp only [Fintype.card_fin] at c
    exact Cb.mono c (by omega)
  have h3 := Cmp.comp (Cmp.pair (cKV sl) (Cmp.pair (cFB sl) (Cmp.wire sl.y))) (Cmp.ofBits h2)
  simp only [Fintype.card_prod, Fintype.card_fin] at h3
  refine Cmp.mono (Cmp.congr h3 ?_) ?_
  · rintro v ⟨s, b⟩
    simp only [Sum.elim_inl, Sum.elim_inr, NRB, NRZ]
    congr 1
    apply Finset.sum_congr rfl; intro j _
    rw [toZ_and, toZ_ofZ, toZ_xor, toZ_ofZ]
    congr 2
    split
    · rfl
    · rw [toZ_ofZ]
  · have hk : k + 1 ≤ NN k m := NN_k
    have hm : m ≤ NN k m := NN_m
    have h4 : 4 ≤ NN k m := NN_4
    set N := NN k m
    have e : m * (k + 1) * (m * 9 + 1) ≤ N * N * (N * 9 + 1) := by gcongr
    have p5 : N ^ 5 ≤ N ^ 8 := pow_mono_N (by omega) (by norm_num)
    have p3 : N ^ 3 ≤ N ^ 8 := pow_mono_N (by omega) (by norm_num)
    have p2 : N ^ 2 ≤ N ^ 8 := pow_mono_N (by omega) (by norm_num)
    have : N * N * (N * 9 + 1) = 9 * N ^ 3 + N ^ 2 := by ring
    omega

def m2sel {k m : ℕ} (p : Fin ((k + 1) + m) × Fin ((k + 1) + m)) :
    Option ((Fin m × Fin (k + 1)) ⊕ (Fin (k + 1) × Fin (k + 1))) :=
  splitF (fun a => splitF (fun b => some (Sum.inr (a, b))) (fun _ => none) p.2)
    (fun s => splitF (fun b => some (Sum.inl (s, b))) (fun _ => none) p.2) p.1

theorem M2_opt {k m : ℕ} (w : (Fin m × Fin (k + 1)) ⊕ (Fin (k + 1) × Fin (k + 1)) → Bool)
    (p : Fin ((k + 1) + m) × Fin ((k + 1) + m)) :
    M2 (fun q => w (Sum.inr q)) (fun s b => w (Sum.inl (s, b))) p = (m2sel p).elim false w := by
  unfold M2 m2sel splitF
  split_ifs <;> rfl

theorem cStep {ι : Type} {k m : ℕ} (sl : Sl ι k m) :
    Cmp ι (Fin (k + 1) × Fin (k + 1)) (2048 * NN k m ^ 8)
      (fun v => stepR (sl.vb v) (sl.vA v) (sl.vB v) (sl.vy v) (sl.vR v)) := by
  have hM : Cmp ((Fin m × Fin (k + 1)) ⊕ (Fin (k + 1) × Fin (k + 1)))
      (Fin ((k + 1) + m) × Fin ((k + 1) + m))
      (Fintype.card (Fin ((k + 1) + m) × Fin ((k + 1) + m)) * 1)
      (fun w p => (m2sel p).elim false w) := Cmp.ofBits (fun p => Cb.optVar (m2sel p))
  have h3 := Cmp.comp (Cmp.comp (Cmp.comp (Cmp.pair (cNR sl) (Cmp.wire sl.R)) hM)
    (cmp_gj ((k + 1) + m)))
    (Cmp.wire (fun p : Fin (k + 1) × Fin (k + 1) => (Fin.castAdd m p.1, Fin.castAdd m p.2)))
  simp only [Fintype.card_prod, Fintype.card_fin] at h3
  refine Cmp.mono (Cmp.congr h3 ?_) ?_
  · intro v p
    simp only [stepR, stepMat]
    congr 2
    funext q
    rw [← M2_opt]
    rfl
  · have hk : k + 1 ≤ NN k m := NN_k
    have hm : m ≤ NN k m := NN_m
    have h4 : 4 ≤ NN k m := NN_4
    have hN : NN k m = k + m + 4 := rfl
    set N := NN k m
    have hD : (k + 1) + m + 1 ≤ N := by omega
    have e1 : ((k + 1) + m) * ((k + 1) + m) * 1 ≤ N * N := by
      have : (k + 1) + m ≤ N := by omega
      calc _ = ((k + 1) + m) * ((k + 1) + m) := by ring
        _ ≤ N * N := Nat.mul_le_mul this this
    have e2 : gjCost ((k + 1) + m) ≤ 32 * N ^ 4 := by
      unfold gjCost
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 4)
    have p4 : N ^ 4 ≤ N ^ 8 := pow_mono_N (by omega) (by norm_num)
    have p2 : N ^ 2 ≤ N ^ 8 := pow_mono_N (by omega) (by norm_num)
    have a1 : N * N = N ^ 2 := by ring
    rw [a1] at e1
    omega

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

abbrev GW (k W : ℕ) : Type := Unit ⊕ (Unit ⊕ (Fin k ⊕ ((Fin k × Fin k) ⊕ Fin W)))

def gz {k W : ℕ} (w : GW k W → Bool) : Bool := w (Sum.inl ())
def gc {k W : ℕ} (w : GW k W → Bool) : Bool := w (Sum.inr (Sum.inl ()))
def gal {k W : ℕ} (w : GW k W → Bool) (a : Fin k) : Bool := w (Sum.inr (Sum.inr (Sum.inl a)))
def gga {k W : ℕ} (w : GW k W → Bool) (p : Fin k × Fin k) : Bool :=
  w (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))
def gP {k W : ℕ} (w : GW k W → Bool) (t : Fin W) : Bool :=
  w (Sum.inr (Sum.inr (Sum.inr (Sum.inr t))))

def genc {k : ℕ} (W : ℕ) (s : GSt k) : GW k W → Bool :=
  Sum.elim (fun _ => s.z) (Sum.elim (fun _ => s.c) (Sum.elim s.al (Sum.elim s.ga
    (fun t => (2 ^ k / 2 ^ s.n3).testBit t.val))))

def gPnext {k W : ℕ} (i : Fin k) (w : GW k W → Bool) (t : Fin W) : Bool :=
  if gAny i (gga w) then (if h : t.val + 1 < W then gP w ⟨t.val + 1, h⟩ else false) else gP w t

def gstepW {k W : ℕ} (i : Fin k) (w : GW k W → Bool) : GW k W → Bool :=
  Sum.elim (fun _ => gz w || (!gAny i (gga w) && gA0 i (gal w) (gga w)))
    (Sum.elim (fun _ => nC (gc w) (gA0 i (gal w) (gga w)) (gB0 i (gal w) (gga w)))
      (Sum.elim (nAl (gal w) (gKeep i (gga w)) (gAA i (gga w)) (gBB i (gga w))
          (gA0 i (gal w) (gga w)) (gB0 i (gal w) (gga w)))
        (Sum.elim (nGa (gga w) (gKeep i (gga w)) (gAA i (gga w)) (gBB i (gga w)))
          (gPnext i w))))

theorem gstepW_enc {k W : ℕ} (hW : k < W) (i : Fin k) (s : GSt k) :
    gstepW i (genc W s) = genc W (gstep i s) := by
  funext x
  rcases x with ⟨⟩ | ⟨⟩ | a | p | t
  · rfl
  · rfl
  · rfl
  · rfl
  · show gPnext i (genc W s) t = (2 ^ k / 2 ^ (gstep i s).n3).testBit t.val
    unfold gPnext
    have hga : gga (genc W s) = s.ga := rfl
    rw [hga]
    have hn : (gstep i s).n3 = s.n3 + (if gAny i s.ga then 1 else 0) := rfl
    rw [hn]
    by_cases ha : gAny i s.ga = true
    · simp only [ha, if_true]
      have hdiv : 2 ^ k / 2 ^ (s.n3 + 1) = 2 ^ k / 2 ^ s.n3 / 2 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      rw [hdiv]
      by_cases ht : t.val + 1 < W
      · rw [dif_pos ht]
        show (2 ^ k / 2 ^ s.n3).testBit (t.val + 1) = _
        rw [Nat.testBit_succ]
      · rw [dif_neg ht]
        symm
        apply Nat.testBit_lt_two_pow
        have h1 : 2 ^ k / 2 ^ s.n3 / 2 < 2 ^ k := by
          have := Nat.div_le_self (2 ^ k) (2 ^ s.n3)
          have h2 : 0 < 2 ^ k := by positivity
          omega
        have h3 : 2 ^ k ≤ 2 ^ t.val := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    · simp only [Bool.not_eq_true] at ha
      simp only [ha, Bool.false_eq_true, if_false, add_zero]
      rfl

theorem gfoldW {k W : ℕ} (hW : k < W) (L : List (Fin k)) (s : GSt k) :
    L.foldl (fun w i => gstepW i w) (genc W s) = genc W (gfold L s) := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldl_cons]
    rw [gstepW_enc hW, ih]
    rfl

section cbs
variable {k W : ℕ} (i : Fin k)

theorem cbS (b : Fin k) : Cb (GW k W) 6 (fun w => gS i (gga w) b) :=
  Cb.mono (Cb.and (Cb.const _) (Cb.xor (Cb.var _) (Cb.var _))) (by norm_num)

theorem cbSel (b : Fin k) : Cb (GW k W) (10 * (k + 1)) (fun w => gSel i (gga w) b) := by
  have c := Cb.and (cbS (W := W) i b) (Cb.not (Cb.bigOr (fun b' : Fin k =>
    Cb.and (Cb.const (decide (b' < b))) (cbS (W := W) i b'))))
  simp only [Fintype.card_fin] at c
  refine Cb.mono (Cb.congr c (fun w => by unfold gSel; congr)) ?_
  ring_nf; omega

theorem cbAny : Cb (GW k W) (8 * (k + 1)) (fun w => gAny i (gga w)) := by
  have c := Cb.bigOr (fun b : Fin k => cbS (W := W) i b)
  simp only [Fintype.card_fin] at c
  refine Cb.mono (Cb.congr c (fun w => by unfold gAny; congr)) ?_
  ring_nf; omega

theorem cbA0 : Cb (GW k W) 4 (fun w => gA0 i (gal w) (gga w)) :=
  Cb.mono (Cb.congr (Cb.xor (Cb.var (Sum.inr (Sum.inr (Sum.inl i))))
    (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, i))))))) (fun w => rfl)) (by norm_num)

theorem cbB0 : Cb (GW k W) (20 * (k + 1) ^ 2) (fun w => gB0 i (gal w) (gga w)) := by
  have c := Cb.bigOr (fun b : Fin k => Cb.and (cbSel (W := W) i b)
    (Cb.xor (Cb.var (Sum.inr (Sum.inr (Sum.inl b))))
      (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl (b, b))))))))
  simp only [Fintype.card_fin] at c
  refine Cb.mono (Cb.congr c (fun w => by unfold gB0; congr)) ?_
  ring_nf; nlinarith

theorem cbKeep (a : Fin k) : Cb (GW k W) (20 * (k + 1)) (fun w => gKeep i (gga w) a) := by
  have c := Cb.and (Cb.const (ι := GW k W) (decide (a ≠ i))) (Cb.not (cbSel (W := W) i a))
  refine Cb.mono (Cb.congr c (fun w => rfl)) ?_
  nlinarith

theorem cbAA (a : Fin k) : Cb (GW k W) (20 * (k + 1)) (fun w => gAA i (gga w) a) := by
  have c := Cb.and (cbS (W := W) i a) (Cb.not (cbSel (W := W) i a))
  refine Cb.mono (Cb.congr c (fun w => rfl)) ?_
  nlinarith

theorem cbBB (a : Fin k) : Cb (GW k W) (50 * (k + 1) ^ 2) (fun w => gBB i (gga w) a) := by
  have c := Cb.and (cbKeep (W := W) i a) (Cb.bigOr (fun b : Fin k => Cb.and (cbSel (W := W) i b)
    (Cb.xor (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl (a, b))))))
      (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl (b, a)))))))))
  simp only [Fintype.card_fin] at c
  refine Cb.mono (Cb.congr c (fun w => by unfold gBB; congr)) ?_
  ring_nf; nlinarith

end cbs

theorem cGstep {k W : ℕ} (i : Fin k) :
    Cmp (GW k W) (GW k W) (300 * (k + 1) ^ 4 + 20 * W * (k + 1)) (gstepW i) := by
  have cz : Cb (GW k W) (20 * (k + 1))
      (fun w => gz w || (!gAny i (gga w) && gA0 i (gal w) (gga w))) :=
    Cb.mono (Cb.or (Cb.var _) (Cb.and (Cb.not (cbAny i)) (cbA0 i))) (by ring_nf; omega)
  have cc : Cb (GW k W) (30 * (k + 1) ^ 2)
      (fun w => nC (gc w) (gA0 i (gal w) (gga w)) (gB0 i (gal w) (gga w))) :=
    Cb.mono (Cb.xor (Cb.var _) (Cb.and (cbA0 i) (cbB0 i))) (by ring_nf; nlinarith)
  have ca : ∀ a : Fin k, Cb (GW k W) (125 * (k + 1) ^ 2)
      (fun w => nAl (gal w) (gKeep i (gga w)) (gAA i (gga w)) (gBB i (gga w))
          (gA0 i (gal w) (gga w)) (gB0 i (gal w) (gga w)) a) := by
    intro a
    exact Cb.mono (Cb.xor (Cb.xor (Cb.and (cbKeep i a) (Cb.var _)) (Cb.and (cbA0 i) (cbBB i a)))
      (Cb.and (cbB0 i) (cbAA i a))) (by ring_nf; nlinarith)
  have cg : ∀ p : Fin k × Fin k, Cb (GW k W) (125 * (k + 1) ^ 2)
      (fun w => nGa (gga w) (gKeep i (gga w)) (gAA i (gga w)) (gBB i (gga w)) p) := by
    intro p
    exact Cb.mono (Cb.xor (Cb.and (Cb.and (cbKeep i p.1) (cbKeep i p.2)) (Cb.var _))
      (Cb.and (cbAA i p.1) (cbBB i p.2))) (by ring_nf; nlinarith)
  have cp : ∀ t : Fin W, Cb (GW k W) (20 * (k + 1)) (fun w => gPnext i w t) := by
    intro t
    by_cases ht : t.val + 1 < W
    · refine Cb.mono (Cb.congr (Cb.mux (cbAny i) (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        ⟨t.val + 1, ht⟩))))) (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))))) ?_)
        (by ring_nf; omega)
      intro w; simp [gPnext, ht, gP]
    · refine Cb.mono (Cb.congr (Cb.mux (cbAny i) (Cb.const false)
        (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))))) ?_)
        (by ring_nf; omega)
      intro w; simp [gPnext, ht, gP]
  have hA := Cmp.ofBits ca
  have hG := Cmp.ofBits cg
  have hP := Cmp.ofBits cp
  have h := Cmp.pair cz (Cmp.pair cc (Cmp.pair hA (Cmp.pair hG hP)))
  simp only [Fintype.card_fin, Fintype.card_prod] at h
  refine Cmp.mono (Cmp.congr h ?_) ?_
  · intro w x
    rcases x with ⟨⟩ | ⟨⟩ | a | p | t <;> rfl
  · have hk : k ≤ k + 1 := by omega
    have e1 : k * (125 * (k + 1) ^ 2) ≤ 125 * (k + 1) ^ 3 := by
      calc k * (125 * (k + 1) ^ 2) ≤ (k + 1) * (125 * (k + 1) ^ 2) := by gcongr
        _ = 125 * (k + 1) ^ 3 := by ring
    have e2 : k * k * (125 * (k + 1) ^ 2) ≤ 125 * (k + 1) ^ 4 := by
      calc k * k * (125 * (k + 1) ^ 2) ≤ (k + 1) * (k + 1) * (125 * (k + 1) ^ 2) := by gcongr
        _ = 125 * (k + 1) ^ 4 := by ring
    have e3 : W * (20 * (k + 1)) = 20 * W * (k + 1) := by ring
    have p1 : (k + 1) ≤ (k + 1) ^ 4 := by
      calc k + 1 = (k + 1) ^ 1 := by ring
        _ ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p2 : (k + 1) ^ 2 ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p3 : (k + 1) ^ 3 ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

structure FSl (ι : Type) (k m : ℕ) where
  fb : Fin (k + 1) × Fin (k + 1) × Fin m → ι
  y : Fin m → ι
  pv : Fin m → ι
  cn : Fin (m + 1) × Fin (m + 1) → ι

section slotc
variable {ι : Type} {k m : ℕ} (fs : FSl ι k m) (h' : ℕ) (hh : h' ≤ m)

def wB (σ : Fin h' → Bool) (v : ι → Bool) (j : Fin m) : Bool :=
  v (fs.pv j) && decide (∃ s : Fin h', (σ s && v (fs.cn (j.castSucc, ⟨s.val, by omega⟩))) = true)

def PtB (σ : Fin h' → Bool) (v : ι → Bool) (a b : Fin (k + 1)) : Bool :=
  ofZ (∑ j, toZ (wB fs h' hh σ v j && xor (v (fs.fb (a, b, j))) (v (fs.y j))))

def ginit (P : Fin (k + 1) × Fin (k + 1) → Bool) : GSt k :=
  ⟨false, P (Fin.last k, Fin.last k),
    fun q => xor (P (q.castSucc, Fin.last k)) (P (Fin.last k, Fin.last k)),
    fun p => decide (p.1 < p.2) && xor (xor (xor (P (p.1.castSucc, p.2.castSucc))
      (P (p.1.castSucc, Fin.last k))) (P (p.2.castSucc, Fin.last k))) (P (Fin.last k, Fin.last k)),
    0⟩

def slotBV (W : ℕ) (σ : Fin h' → Bool) (v : ι → Bool) : BitVec W :=
  BitVec.ofInt W (gval (gfold (List.finRange k) (ginit (fun p => PtB fs h' hh σ v p.1 p.2))))

theorem cPt (σ : Fin h' → Bool) :
    Cmp ι (Fin (k + 1) × Fin (k + 1)) (6 * NN k m ^ 4) (fun v p => PtB fs h' hh σ v p.1 p.2) := by
  have hw : ∀ j : Fin m, Cb ι (h' * 3 + 2) (fun v => wB fs h' hh σ v j) := by
    intro j
    have c := Cb.and (Cb.var (fs.pv j)) (Cb.bigOr (fun s : Fin h' =>
      Cb.and (Cb.const (ι := ι) (σ s)) (Cb.var (fs.cn (j.castSucc, ⟨s.val, by omega⟩)))))
    simp only [Fintype.card_fin] at c
    exact Cb.mono (Cb.congr c (fun v => by unfold wB; congr)) (by ring_nf; omega)
  have hp : ∀ p : Fin (k + 1) × Fin (k + 1), Cb ι (m * (h' * 3 + 11) + 1)
      (fun v => PtB fs h' hh σ v p.1 p.2) := by
    intro p
    have c := Cb.sumZ (I := Fin m) (fun j => Cb.and (hw j) (Cb.xor (Cb.var (fs.fb (p.1, p.2, j)))
      (Cb.var (fs.y j))))
    simp only [Fintype.card_fin] at c
    exact Cb.mono (Cb.congr c (fun v => rfl)) (by ring_nf; omega)
  have h := Cmp.ofBits hp
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  refine Cmp.mono h ?_
  have hk : k + 1 ≤ NN k m := NN_k
  have hm : m ≤ NN k m := NN_m
  have h4 : 4 ≤ NN k m := NN_4
  set N := NN k m
  have e : (k + 1) * (k + 1) * (m * (h' * 3 + 11) + 1) ≤ N * N * (N * (N * 3 + 11) + 1) := by
    gcongr; omega
  have e2 : N * N * (N * (N * 3 + 11) + 1) ≤ 6 * N ^ 4 := by
    have : N * 11 + 1 ≤ 3 * N * N := by nlinarith
    nlinarith
  omega

end slotc

theorem genc_P0 {k : ℕ} (W : ℕ) (t : Fin W) : (2 ^ k / 2 ^ 0 : ℕ).testBit t.val = (2 ^ k).testBit t.val := by
  simp

theorem cInit (k W : ℕ) :
    Cmp (Fin (k + 1) × Fin (k + 1)) (GW k W) (1 + 0 + (k * 4 + (k * k * 14 + W * 1)))
      (fun w => genc W (ginit w)) := by
  have cz : Cb (Fin (k + 1) × Fin (k + 1)) 1 (fun _ => false) := Cb.const false
  have cc : Cb (Fin (k + 1) × Fin (k + 1)) 0 (fun w => w (Fin.last k, Fin.last k)) := Cb.var _
  have ca : ∀ q : Fin k, Cb (Fin (k + 1) × Fin (k + 1)) 4
      (fun w => xor (w (q.castSucc, Fin.last k)) (w (Fin.last k, Fin.last k))) :=
    fun q => Cb.mono (Cb.xor (Cb.var _) (Cb.var _)) (by norm_num)
  have cg : ∀ p : Fin k × Fin k, Cb (Fin (k + 1) × Fin (k + 1)) 14
      (fun w => decide (p.1 < p.2) && xor (xor (xor (w (p.1.castSucc, p.2.castSucc))
        (w (p.1.castSucc, Fin.last k))) (w (p.2.castSucc, Fin.last k)))
        (w (Fin.last k, Fin.last k))) :=
    fun p => Cb.mono (Cb.and (Cb.const _) (Cb.xor (Cb.xor (Cb.xor (Cb.var _) (Cb.var _))
      (Cb.var _)) (Cb.var _))) (by norm_num)
  have cp : ∀ t : Fin W, Cb (Fin (k + 1) × Fin (k + 1)) 1
      (fun _ => (2 ^ k / 2 ^ 0 : ℕ).testBit t.val) := fun t => Cb.const _
  have h := Cmp.pair cz (Cmp.pair cc (Cmp.pair (Cmp.ofBits ca) (Cmp.pair (Cmp.ofBits cg)
    (Cmp.ofBits cp))))
  simp only [Fintype.card_fin, Fintype.card_prod] at h
  refine Cmp.mono (Cmp.congr h ?_) (by omega)
  intro w x
  rcases x with ⟨⟩ | ⟨⟩ | a | p | t <;> rfl

theorem gout_enc {k : ℕ} (W : ℕ) (s : GSt k) :
    (if gz (genc W s) then (0 : BitVec W) else if gc (genc W s) then -(bv (gP (genc W s)))
      else bv (gP (genc W s))) = BitVec.ofInt W (gval s) := by
  have hb : bv (gP (genc W s)) = BitVec.ofNat W (2 ^ k / 2 ^ s.n3) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [getLsbD_bv (gP (genc W s)) ⟨i, hi⟩, BitVec.getLsbD_ofNat]
    simp [gP, genc, hi]
  rw [hb]
  unfold gval
  show (if s.z then (0 : BitVec W) else if s.c then -(BitVec.ofNat W (2 ^ k / 2 ^ s.n3))
      else BitVec.ofNat W (2 ^ k / 2 ^ s.n3)) = _
  by_cases hz : s.z = true
  · simp only [hz, if_true]
    rfl
  · simp only [hz, Bool.false_eq_true, if_false]
    by_cases hc : s.c = true
    · simp only [hc, if_true]
      rw [BitVec.ofInt_neg, BitVec.ofInt_natCast]
    · simp only [hc, Bool.false_eq_true, if_false]
      rw [BitVec.ofInt_natCast]

theorem cGout (k W : ℕ) :
    Cw (GW k W) W (30 * (W + 1))
      (fun w => if gz w then (0 : BitVec W) else if gc w then -(bv (gP w)) else bv (gP w)) := by
  have hv : Cw (GW k W) W 0 (fun w => bv (gP w)) :=
    Cw.var (fun t => Sum.inr (Sum.inr (Sum.inr (Sum.inr t))))
  have h := Cw.mux (Cb.var (Sum.inl ())) (Cw.const (ι := GW k W) (0 : BitVec W))
    (Cw.mux (Cb.var (Sum.inr (Sum.inl ()))) (Cw.neg hv) hv)
  exact Cw.mono (Cw.congr h (fun w => rfl)) (by omega)

theorem cSlot {ι : Type} {k m : ℕ} (fs : FSl ι k m) (h' : ℕ) (hh : h' ≤ m) (W : ℕ)
    (hW : k < W) (hW2 : W ≤ 2 * NN k m) (σ : Fin h' → Bool) :
    Cw ι W (512 * NN k m ^ 5) (slotBV fs h' hh W σ) := by
  have h1 := Cmp.comp (cPt fs h' hh σ) (cInit k W)
  have h2 := Cmp.comp h1 (Cmp.foldl (List.finRange k) (fun i w => gstepW (W := W) i w)
    (fun i _ => cGstep i))
  have h3 := Cmp.comp h2 (cGout k W)
  refine Cmp.mono (Cmp.congr h3 ?_) ?_
  · intro v t
    simp only
    rw [gfoldW hW, gout_enc]
    rfl
  · have hk : k + 1 ≤ NN k m := NN_k
    have hm : m ≤ NN k m := NN_m
    have h4 : 4 ≤ NN k m := NN_4
    set N := NN k m
    rw [List.length_finRange]
    have e1 : 1 + 0 + (k * 4 + (k * k * 14 + W * 1)) ≤ 20 * N * N := by nlinarith
    have e2 : k * (300 * (k + 1) ^ 4 + 20 * W * (k + 1)) ≤ N * (300 * N ^ 4 + 40 * N * N) := by
      have a1 : 20 * W * (k + 1) ≤ 20 * (2 * N) * N :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hW2) hk
      have a2 : 300 * (k + 1) ^ 4 ≤ 300 * N ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk 4)
      have a3 : 20 * (2 * N) * N = 40 * N * N := by ring
      exact Nat.mul_le_mul (by omega) (by omega)
    have e3 : 30 * (W + 1) ≤ 75 * N := by omega
    have e4 : N * (300 * N ^ 4 + 40 * N * N) = 300 * N ^ 5 + 40 * N ^ 3 := by ring
    have p4 : N ^ 4 ≤ N ^ 5 := pow_mono_N (by omega) (by norm_num)
    have p3 : N ^ 3 ≤ N ^ 5 := pow_mono_N (by omega) (by norm_num)
    have p2 : N * N ≤ N ^ 5 := by
      calc N * N = N ^ 2 := by ring
        _ ≤ N ^ 5 := pow_mono_N (by omega) (by norm_num)
    have p1 : N ≤ N ^ 5 := by
      calc N = N ^ 1 := by ring
        _ ≤ N ^ 5 := pow_mono_N (by omega) (by norm_num)
    have : 20 * N * N = 20 * (N * N) := by ring
    omega

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

theorem Cw.lsum {ι α : Type} {W s : ℕ} (φ : α → (ι → Bool) → BitVec W)
    (h : ∀ a, Cw ι W s (φ a)) :
    ∀ L : List α, Cw ι W (L.length * (s + 20 * (W + 1)) + W)
      (fun v => (L.map (fun a => φ a v)).sum) := by
  intro L
  induction L with
  | nil => exact Cw.congr (Cw.mono (Cw.const 0) (by simp)) (fun v => by simp)
  | cons a L ih =>
    refine Cw.mono (Cw.congr (Cw.add (h a) ih) (fun v => by simp)) ?_
    simp only [List.length_cons]
    ring_nf
    omega

theorem shift_bit {W : ℕ} (c : Bool) (x : BitVec W) (t : Fin W) :
    (if c then x <<< 1 else x).getLsbD t.val =
      (if c then (if t.val = 0 then false else x.getLsbD (t.val - 1)) else x.getLsbD t.val) := by
  cases c
  · rfl
  · simp only [if_true, BitVec.getLsbD_shiftLeft, t.isLt, decide_true, Bool.true_and]
    by_cases ht : t.val = 0
    · simp [ht]
    · have : ¬ t.val < 1 := by omega
      simp [ht, this]

theorem Cw.dbl {ι : Type} {W : ℕ} (ℓ : ι) {S0 : ℕ} {φ0 : (ι → Bool) → BitVec W}
    (h0 : Cw ι W S0 φ0) :
    Cw ι W (S0 + W * 5) (fun v => if v ℓ then φ0 v <<< 1 else φ0 v) := by
  have hb : ∀ t : Fin W, Cb (ι ⊕ Fin W) 5
      (fun w => if w (Sum.inl ℓ) then (if t.val = 0 then false else
        (if h : t.val - 1 < W then w (Sum.inr ⟨t.val - 1, h⟩) else false))
        else w (Sum.inr t)) := by
    intro t
    by_cases ht : t.val = 0
    · exact Cb.mono (Cb.congr (Cb.mux (Cb.var (Sum.inl ℓ)) (Cb.const false) (Cb.var (Sum.inr t)))
        (fun w => by simp [ht])) (by norm_num)
    · exact Cb.mono (Cb.congr (Cb.mux (Cb.var (Sum.inl ℓ))
        (Cb.var (Sum.inr ⟨t.val - 1, by omega⟩)) (Cb.var (Sum.inr t)))
        (fun w => by simp [ht, show t.val - 1 < W by omega])) (by norm_num)
  have h := Cmp.thn h0 (Cmp.ofBits hb)
  simp only [Fintype.card_fin] at h
  refine Cmp.congr h ?_
  intro v t
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [shift_bit]
  by_cases ht : t.val = 0
  · simp [ht]
  · simp [ht, show t.val - 1 < W by omega]

theorem Cw.dblChain {ι : Type} {W : ℕ} :
    ∀ (L : List ι) {S0 : ℕ} {φ0 : (ι → Bool) → BitVec W}, Cw ι W S0 φ0 →
      Cw ι W (S0 + L.length * (W * 5))
        (fun v => L.foldl (fun x ℓ => if v ℓ then x <<< 1 else x) (φ0 v)) := by
  intro L
  induction L with
  | nil => intro S0 φ0 h0; simpa using h0
  | cons ℓ L ih =>
    intro S0 φ0 h0
    have := ih (Cw.dbl ℓ h0)
    refine Cw.mono (Cw.congr this (fun v => rfl)) ?_
    simp only [List.length_cons]
    ring_nf
    omega

section outs
variable {ι : Type} {k m : ℕ} (fs : FSl ι k m) (rr : Fin (k + 1) × Fin (k + 1) → ι)
  (tb : Fin (k + 1) → ι) (h h' : ℕ) (hh : h' ≤ m) (W : ℕ)

def tzeroB (v : ι → Bool) : Bool := decide (∀ i : Fin (k + 1), (!v (tb i)) = true)

def okB (v : ι → Bool) : Bool :=
  decide (∃ t : Fin (m + 1), (decide (t.val ≤ h) && v (fs.cn (Fin.last m, t))) = true)

def validB (σ : Fin h' → Bool) (v : ι → Bool) : Bool :=
  decide (∀ s : Fin h', (!σ s || decide (∃ t : Fin (m + 1),
    (decide (s.val < t.val) && v (fs.cn (Fin.last m, t))) = true)) = true)

noncomputable def TB (v : ι → Bool) : BitVec W :=
  ((Finset.univ : Finset (Fin h' → Bool)).toList.map
    (fun σ => if validB fs h' σ v then slotBV fs h' hh W σ v else 0)).sum

def tvecB (v : ι → Bool) : BitVec W :=
  bv (fun i : Fin W => if hi : i.val < k + 1 then v (tb ⟨i.val, hi⟩) else false)

def pivList : List ι :=
  (List.finRange k).map (fun i => rr (i.castSucc, i.castSucc)) ++ (List.finRange m).map fs.pv

def ttB (v : ι → Bool) : BitVec W :=
  (pivList fs rr).foldl (fun x ℓ => if v ℓ then x <<< 1 else x) (tvecB tb W v)

noncomputable def OUTB (v : ι → Bool) : Bool :=
  if v (rr (Fin.last k, Fin.last k)) then tzeroB tb v
  else (okB fs h v && !(TB fs h' hh W v - ttB fs rr tb W v).getLsbD (W - 1))

theorem cOut (hW : k < W) (hW2 : W ≤ 2 * NN k m) :
    Cb ι (2 ^ h' * (2048 * NN k m ^ 5) + 64 * NN k m ^ 2) (OUTB fs rr tb h h' hh W) := by
  have hk : k + 1 ≤ NN k m := NN_k
  have hm : m ≤ NN k m := NN_m
  have h4 : 4 ≤ NN k m := NN_4
  have hm1 : m + 1 ≤ NN k m := by unfold NN; omega
  have hkm : k + m ≤ NN k m := by unfold NN; omega
  have cval : ∀ σ : Fin h' → Bool, Cb ι (h' * ((m + 1) * 3 + 4) + 1) (validB fs h' σ) := by
    intro σ
    have c := Cb.bigAnd (fun s : Fin h' => Cb.or (Cb.const (ι := ι) (!σ s))
      (Cb.bigOr (fun t : Fin (m + 1) => Cb.and (Cb.const (decide (s.val < t.val)))
        (Cb.var (fs.cn (Fin.last m, t))))))
    simp only [Fintype.card_fin] at c
    exact Cb.mono (Cb.congr c (fun v => Bool.eq_iff_iff.2 (by unfold validB; simp)))
      (by ring_nf; omega)
  have cterm : ∀ σ : Fin h' → Bool, Cw ι W (1024 * NN k m ^ 5)
      (fun v => if validB fs h' σ v then slotBV fs h' hh W σ v else 0) := by
    intro σ
    have c := Cw.mux (cval σ) (cSlot fs h' hh W hW hW2 σ) (Cw.const (ι := ι) (0 : BitVec W))
    refine Cw.mono c ?_
    set N := NN k m
    have e1 : h' * ((m + 1) * 3 + 4) + 1 ≤ N * (N * 3 + 4) + 1 := by gcongr <;> omega
    have e2 : N * (N * 3 + 4) + 1 + W + 4 * W ≤ 512 * N ^ 5 := by
      have p2 : N ^ 2 ≤ N ^ 5 := pow_mono_N (by omega) (by norm_num)
      have p1 : N ≤ N ^ 5 := by
        calc N = N ^ 1 := by ring
          _ ≤ N ^ 5 := pow_mono_N (by omega) (by norm_num)
      have : N * (N * 3 + 4) = 3 * N ^ 2 + 4 * N := by ring
      omega
    omega
  have cT := Cw.lsum _ cterm (Finset.univ : Finset (Fin h' → Bool)).toList
  rw [Finset.length_toList, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at cT
  have cv : Cw ι W W (tvecB tb W) := by
    have := Cw.ofBits (ι := ι) (W := W) (s := 1) (φ := tvecB tb W) (fun i => by
      by_cases hi : i.val < k + 1
      · exact Cb.mono (Cb.congr (Cb.var (tb ⟨i.val, hi⟩)) (fun v => by
          unfold tvecB; rw [getLsbD_bv, dif_pos hi])) (by norm_num)
      · exact Cb.congr (Cb.const false) (fun v => by
          unfold tvecB; rw [getLsbD_bv, dif_neg hi]))
    simpa using this
  have ctt := Cw.dblChain (pivList fs rr) cv
  have hlen : (pivList fs rr).length = k + m := by simp [pivList]
  rw [hlen] at ctt
  have csub := Cw.sub cT ctt
  have cmsb := Cb.comp csub (Cb.var (ι := Fin W) ⟨W - 1, by omega⟩)
  have ctz : Cb ι ((k + 1) * (0 + 1 + 1) + 1) (tzeroB tb) := by
    have c := Cb.bigAnd (fun i : Fin (k + 1) => Cb.not (Cb.var (ι := ι) (tb i)))
    simp only [Fintype.card_fin] at c
    exact Cb.congr c (fun v => Bool.eq_iff_iff.2 (by unfold tzeroB; simp))
  have cok : Cb ι ((m + 1) * (1 + 0 + 1 + 1) + 1) (okB fs h) := by
    have c := Cb.bigOr (fun t : Fin (m + 1) => Cb.and (Cb.const (ι := ι) (decide (t.val ≤ h)))
      (Cb.var (fs.cn (Fin.last m, t))))
    simp only [Fintype.card_fin] at c
    exact Cb.congr c (fun v => Bool.eq_iff_iff.2 (by unfold okB; simp))
  have cfin := Cb.mux (Cb.var (rr (Fin.last k, Fin.last k))) ctz (Cb.and cok (Cb.not cmsb))
  refine Cb.mono (Cb.congr cfin (fun v => by unfold OUTB; rfl)) ?_
  set N := NN k m
  have e1 : 2 ^ h' * (1024 * N ^ 5 + 20 * (W + 1)) + W ≤ 2 ^ h' * (2048 * N ^ 5) := by
    have : 20 * (W + 1) + W ≤ 1024 * N ^ 5 := by
      have p1 : N ≤ N ^ 5 := by
        calc N = N ^ 1 := by ring
          _ ≤ N ^ 5 := pow_mono_N (by omega) (by norm_num)
      omega
    have hp : 1 ≤ 2 ^ h' := Nat.one_le_two_pow
    nlinarith
  have e2 : W + (k + m) * (W * 5) + 20 * (W + 1) + ((k + 1) * (0 + 1 + 1) + 1) +
      ((m + 1) * (1 + 0 + 1 + 1) + 1) + 10 ≤ 64 * N ^ 2 := by
    have : (k + m) * (W * 5) ≤ N * (2 * N * 5) := by gcongr <;> omega
    have : N ^ 2 = N * N := by ring
    nlinarith
  omega

end outs

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

abbrev Inp (k m : ℕ) : Type :=
  Fin m ⊕ ((Fin m × Fin k) ⊕ ((Fin m × Fin k × Fin k) ⊕ (Fin m ⊕ Fin (k + 1))))

abbrev St (k m : ℕ) : Type := Inp k m ⊕ (Fin (k + 1) × Fin (k + 1))

def iB {k m : ℕ} (j : Fin m) : Inp k m := Sum.inl j
def iA {k m : ℕ} (j : Fin m) (i : Fin k) : Inp k m := Sum.inr (Sum.inl (j, i))
def iBB {k m : ℕ} (j : Fin m) (i p : Fin k) : Inp k m := Sum.inr (Sum.inr (Sum.inl (j, i, p)))
def iY {k m : ℕ} (j : Fin m) : Inp k m := Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))
def iT {k m : ℕ} (i : Fin (k + 1)) : Inp k m := Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))

def slSt (k m : ℕ) : Sl (St k m) k m :=
  ⟨fun j => Sum.inl (iB j), fun j i => Sum.inl (iA j i), fun j i p => Sum.inl (iBB j i p),
    fun j => Sum.inl (iY j), fun p => Sum.inr p⟩

def stG {k m : ℕ} (w : St k m → Bool) : St k m → Bool :=
  Sum.elim (fun i => w (Sum.inl i))
    (stepR ((slSt k m).vb w) ((slSt k m).vA w) ((slSt k m).vB w) ((slSt k m).vy w)
      ((slSt k m).vR w))

def dB {k m : ℕ} (v : Inp k m → Bool) : Fin m → Bool := fun j => v (iB j)
def dA {k m : ℕ} (v : Inp k m → Bool) : Fin m → Fin k → Bool := fun j i => v (iA j i)
def dBB {k m : ℕ} (v : Inp k m → Bool) : Fin m → Fin k → Fin k → Bool := fun j i p => v (iBB j i p)
def dY {k m : ℕ} (v : Inp k m → Bool) : Fin m → Bool := fun j => v (iY j)

def Rfin {k m : ℕ} (v : Inp k m → Bool) : Fin (k + 1) × Fin (k + 1) → Bool :=
  (stepR (dB v) (dA v) (dBB v) (dY v))^[k + 1] (R0 k)

theorem stG_iter {k m : ℕ} (v : Inp k m → Bool) (n : ℕ) :
    (stG (k := k) (m := m))^[n] (Sum.elim v (R0 k)) =
      Sum.elim v ((stepR (dB v) (dA v) (dBB v) (dY v))^[n] (R0 k)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext x
    rcases x with x | p
    · rfl
    · rfl

theorem cIter (k m : ℕ) :
    Cmp (Inp k m) (St k m) ((k + 1) * (k + 1) + (k + 1) * (2048 * NN k m ^ 8))
      (fun v => Sum.elim v (Rfin v)) := by
  have hinit : Cmp (Inp k m) (St k m) (0 + Fintype.card (Fin (k + 1) × Fin (k + 1)) * 1)
      (fun v => Sum.elim v (R0 k)) :=
    Cmp.pair (Cmp.wire (fun i => i)) (Cmp.ofBits (fun _ => Cb.const false))
  have hstep : Cmp (St k m) (St k m) (0 + 2048 * NN k m ^ 8) stG :=
    Cmp.pair (Cmp.wire Sum.inl) (cStep (slSt k m))
  have h := Cmp.comp hinit (Cmp.foldl (List.range (k + 1)) (fun _ w => stG w) (fun _ _ => hstep))
  simp only [Fintype.card_prod, Fintype.card_fin, List.length_range, zero_add] at h
  refine Cmp.mono (Cmp.congr h ?_) (by omega)
  intro v x
  rw [foldl_range_iter, stG_iter]
  rfl

abbrev Xd (k m : ℕ) : Type :=
  (Fin (k + 1) × Fin (k + 1) × Fin m) ⊕
    ((Fin (m + (k + 1) * (k + 1)) × Fin (m + (k + 1) * (k + 1))) ⊕ (Fin (m + 1) × Fin (m + 1)))

def Xsem {k m : ℕ} (w : St k m → Bool) : Xd k m → Bool :=
  Sum.elim (fun p => ofZ (FZ ((slSt k m).vb w) ((slSt k m).vA w) ((slSt k m).vB w)
      ((slSt k m).vR w) p.1 p.2.1 p.2.2))
    (Sum.elim (R1B ((slSt k m).vb w) ((slSt k m).vA w) ((slSt k m).vB w) ((slSt k m).vR w))
      (fun p => decide (cnt (piv (R1B ((slSt k m).vb w) ((slSt k m).vA w) ((slSt k m).vB w)
        ((slSt k m).vR w))) p.1.val = p.2.val)))

theorem cX (k m : ℕ) : Cmp (St k m) (Xd k m) (1024 * NN k m ^ 8) Xsem := by
  have hc := Cmp.comp (Cmp.comp (cR1 (slSt k m))
    (Cmp.wire (fun j : Fin m => (Fin.castAdd ((k + 1) * (k + 1)) j,
      Fin.castAdd ((k + 1) * (k + 1)) j)))) (cmp_counter m m)
  have h := Cmp.pair (cFB (slSt k m)) (Cmp.pair (cR1 (slSt k m)) hc)
  refine Cmp.mono (Cmp.congr h ?_) ?_
  · intro w x
    rcases x with p | p | p <;> rfl
  · have hm : m ≤ NN k m := NN_m
    have h4 : 4 ≤ NN k m := NN_4
    set N := NN k m
    have e : (m + 1) * ((m + 1) * 6) ≤ (N + 1) * ((N + 1) * 6) := by gcongr
    have p5 : N ^ 5 ≤ N ^ 8 := pow_mono_N (by omega) (by norm_num)
    have p2 : (N + 1) * ((N + 1) * 6) ≤ 24 * N ^ 8 := by
      have : (N + 1) * ((N + 1) * 6) ≤ 24 * N ^ 2 := by nlinarith
      have p2' : N ^ 2 ≤ N ^ 8 := pow_mono_N (by omega) (by norm_num)
      omega
    omega

def Usel (k m : ℕ) : Type := St k m ⊕ Xd k m

def fsU (k m : ℕ) : FSl (St k m ⊕ Xd k m) k m :=
  ⟨fun p => Sum.inr (Sum.inl p), fun j => Sum.inl (Sum.inl (iY j)),
    fun j => Sum.inr (Sum.inr (Sum.inl (Fin.castAdd _ j, Fin.castAdd _ j))),
    fun p => Sum.inr (Sum.inr (Sum.inr p))⟩

def rrU (k m : ℕ) : Fin (k + 1) × Fin (k + 1) → St k m ⊕ Xd k m := fun p => Sum.inl (Sum.inr p)
def tbU (k m : ℕ) : Fin (k + 1) → St k m ⊕ Xd k m := fun i => Sum.inl (Sum.inl (iT i))

def WW (k m : ℕ) : ℕ := 2 * k + m + 4

noncomputable def FULL (k m h : ℕ) (v : Inp k m → Bool) : Bool :=
  OUTB (fsU k m) (rrU k m) (tbU k m) h (min h m) (min_le_right h m) (WW k m)
    (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v))))

theorem cFull (k m h : ℕ) :
    Cb (Inp k m) (2 ^ (min h m) * (8192 * NN k m ^ 9)) (FULL k m h) := by
  have hW : k < WW k m := by unfold WW; omega
  have hW2 : WW k m ≤ 2 * NN k m := by unfold WW NN; omega
  have hf := Cmp.thn (cX k m) (cOut (fsU k m) (rrU k m) (tbU k m) h (min h m) (min_le_right h m)
    (WW k m) hW hW2)
  have hc := Cmp.comp (cIter k m) hf
  refine Cb.mono (Cb.congr hc (fun v => rfl)) ?_
  have hk : k + 1 ≤ NN k m := NN_k
  have h4 : 4 ≤ NN k m := NN_4
  set N := NN k m
  have hp : 1 ≤ 2 ^ (min h m) := Nat.one_le_two_pow
  have p8 : N ^ 8 ≤ N ^ 9 := pow_mono_N (by omega) (by norm_num)
  have p5 : N ^ 5 ≤ N ^ 9 := pow_mono_N (by omega) (by norm_num)
  have p2 : N ^ 2 ≤ N ^ 9 := pow_mono_N (by omega) (by norm_num)
  have e1 : (k + 1) * (k + 1) ≤ N ^ 2 := by
    calc (k + 1) * (k + 1) ≤ N * N := Nat.mul_le_mul hk hk
      _ = N ^ 2 := by ring
  have e2 : (k + 1) * (2048 * N ^ 8) ≤ 2048 * N ^ 9 := by
    calc (k + 1) * (2048 * N ^ 8) ≤ N * (2048 * N ^ 8) := Nat.mul_le_mul_right _ hk
      _ = 2048 * N ^ 9 := by ring
  have e3 : 2 ^ (min h m) * (2048 * N ^ 5) ≤ 2 ^ (min h m) * (2048 * N ^ 9) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ p5)
  have e4 : N ^ 2 + 2048 * N ^ 9 + 1024 * N ^ 8 + 64 * N ^ 2 ≤ 2 ^ (min h m) * (4096 * N ^ 9) := by
    have : N ^ 2 + 2048 * N ^ 9 + 1024 * N ^ 8 + 64 * N ^ 2 ≤ 4096 * N ^ 9 := by omega
    calc _ ≤ 4096 * N ^ 9 := this
      _ = 1 * (4096 * N ^ 9) := by ring
      _ ≤ 2 ^ (min h m) * (4096 * N ^ 9) := Nat.mul_le_mul_right _ hp
  have e5 : 2 ^ (min h m) * (2048 * N ^ 9) + 2 ^ (min h m) * (4096 * N ^ 9) ≤
      2 ^ (min h m) * (8192 * N ^ 9) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  omega

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

theorem rho_cnt {D m : ℕ} (R1 : Fin (m + D) × Fin (m + D) → Bool) :
    rho R1 = cnt (piv R1) m := by
  unfold rho cnt
  congr 1
  apply Finset.filter_congr
  intro q _
  simp [q.isLt]

theorem rho_le {D m : ℕ} (R1 : Fin (m + D) × Fin (m + D) → Bool) : rho R1 ≤ m := by
  unfold rho
  calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = m := by simp

theorem npiv_le {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) : npiv R ≤ k := by
  unfold npiv
  calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = k := by simp

theorem countP_finRange (n : ℕ) (p : Fin n → Bool) :
    (List.finRange n).countP p = (Finset.univ.filter (fun i => p i = true)).card := by
  rw [List.countP_eq_length_filter]
  rw [Finset.card_def, Finset.filter_val, Fin.univ_def]
  simp

theorem ofNat_shl1 (W x : ℕ) : BitVec.ofNat W x <<< 1 = BitVec.ofNat W (x * 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [pow_one, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem dbl_fold {ι : Type} (W : ℕ) (u : ι → Bool) :
    ∀ (L : List ι) (x0 : ℕ), L.foldl (fun (x : BitVec W) ℓ => if u ℓ then x <<< 1 else x)
      (BitVec.ofNat W x0) =
      BitVec.ofNat W (x0 * 2 ^ (L.countP u)) := by
  intro L
  induction L with
  | nil => intro x0; simp
  | cons ℓ L ih =>
    intro x0
    simp only [List.foldl_cons, List.countP_cons]
    by_cases hl : u ℓ = true
    · rw [if_pos hl, ofNat_shl1, ih, if_pos hl, pow_succ]
      congr 1; ring
    · rw [if_neg hl, ih, if_neg hl, add_zero]

theorem msb_sub (W a b : ℕ) (hW : 1 ≤ W) (ha : a < 2 ^ (W - 1)) (hb : b < 2 ^ (W - 1)) :
    (BitVec.ofNat W a - BitVec.ofNat W b).getLsbD (W - 1) = decide (a < b) := by
  have hP : 2 ^ W = 2 * 2 ^ (W - 1) := by
    rw [← pow_succ']; congr 1; omega
  set P := 2 ^ (W - 1)
  have ha' : a < 2 ^ W := by omega
  have hb' : b < 2 ^ W := by omega
  rw [← BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_decide, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb']
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  rw [hP]
  by_cases hab : b ≤ a
  · have : 2 * P - b + a = (a - b) + 2 * P := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    constructor
    · intro h; omega
    · intro h; omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    constructor
    · intro _; omega
    · intro _; omega

theorem ofInt_sum {α : Type} (W : ℕ) (s : Finset α) (f : α → ℤ) :
    BitVec.ofInt W (∑ a ∈ s, f a) = ∑ a ∈ s, BitVec.ofInt W (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BitVec.ofInt_add, ih]

section sem
variable {k m : ℕ} (v : Inp k m → Bool)

theorem sl_vb (R : Fin (k + 1) × Fin (k + 1) → Bool) : (slSt k m).vb (Sum.elim v R) = dB v := rfl
theorem sl_vA (R : Fin (k + 1) × Fin (k + 1) → Bool) : (slSt k m).vA (Sum.elim v R) = dA v := rfl
theorem sl_vB (R : Fin (k + 1) × Fin (k + 1) → Bool) : (slSt k m).vB (Sum.elim v R) = dBB v := rfl
theorem sl_vy (R : Fin (k + 1) × Fin (k + 1) → Bool) : (slSt k m).vy (Sum.elim v R) = dY v := rfl
theorem sl_vR (R : Fin (k + 1) × Fin (k + 1) → Bool) : (slSt k m).vR (Sum.elim v R) = R := rfl

theorem wB_eq (h' : ℕ) (hh : h' ≤ m) (σ : Fin h' → Bool) (j : Fin m) :
    wB (fsU k m) h' hh σ (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v)))) j =
      wS h' (R1B (dB v) (dA v) (dBB v) (Rfin v)) σ j := by
  unfold wB wS
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true, fsU, Xsem, Sum.elim_inr, Sum.elim_inl]
  simp only [decide_eq_true_eq, Fin.coe_castSucc]
  exact Iff.rfl

theorem PtB_eq (h' : ℕ) (hh : h' ≤ m) (σ : Fin h' → Bool) (a b : Fin (k + 1)) :
    PtB (fsU k m) h' hh σ (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v)))) a b =
      ofZ (Pt (dB v) (dA v) (dBB v) (dY v) h' (Rfin v) σ a b) := by
  unfold PtB Pt
  congr 1
  apply Finset.sum_congr rfl; intro j _
  rw [wB_eq, toZ_and, toZ_xor]
  show toZ (wS h' _ σ j) * (toZ (ofZ (FZ (dB v) (dA v) (dBB v) (Rfin v) a b j)) + toZ (dY v j)) = _
  rw [toZ_ofZ]

theorem slot_eq (h' : ℕ) (hh : h' ≤ m) (W : ℕ) (σ : Fin h' → Bool) :
    slotBV (fsU k m) h' hh W σ (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v)))) =
      BitVec.ofInt W (gsum (coefC (dB v) (dA v) (dBB v) (dY v) h' (Rfin v) σ)
        (coefA (dB v) (dA v) (dBB v) (dY v) h' (Rfin v) σ)
        (coefG (dB v) (dA v) (dBB v) (dY v) h' (Rfin v) σ)) := by
  unfold slotBV
  rw [gauss_correct]
  congr 3
  simp only [PtB_eq]
  unfold ginit coefC coefA coefG
  simp only [ofZ_add]

theorem cnt_m_le {m : ℕ} (fl : Fin m → Bool) : cnt fl m ≤ m := cnt_le fl m

theorem valid_eq (h' : ℕ) (σ : Fin h' → Bool) :
    validB (fsU k m) h' σ (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v)))) =
      validS h' (R1B (dB v) (dA v) (dBB v) (Rfin v)) σ := by
  unfold validB validS
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true]
  have hc := cnt_m_le (piv (R1B (dB v) (dA v) (dBB v) (Rfin v)))
  rw [rho_cnt]
  set c := cnt (piv (R1B (dB v) (dA v) (dBB v) (Rfin v))) m
  constructor
  · intro H s hs
    rcases H s with h1 | ⟨t, ht1, ht2⟩
    · rw [hs] at h1; exact absurd h1 (by simp)
    · have ht2' := ht2
      simp only [fsU, Xsem, Sum.elim_inr] at ht2'
      rw [decide_eq_true_eq] at ht2'
      have : c = t.val := ht2'
      have ht1' : s.val < t.val := by simpa using ht1
      omega
  · intro H s
    by_cases hs : σ s = true
    · right
      refine ⟨⟨c, by omega⟩, ?_, ?_⟩
      · simp only [decide_eq_true_eq]; exact H s hs
      · (simp only [fsU, Xsem, Sum.elim_inr]; rw [decide_eq_true_eq]; rfl)
    · left; simpa using hs

theorem ok_eq (h : ℕ) :
    okB (fsU k m) h (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v)))) =
      decide (rho (R1B (dB v) (dA v) (dBB v) (Rfin v)) ≤ h) := by
  unfold okB
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  have hc := cnt_m_le (piv (R1B (dB v) (dA v) (dBB v) (Rfin v)))
  rw [rho_cnt]
  set c := cnt (piv (R1B (dB v) (dA v) (dBB v) (Rfin v))) m
  constructor
  · rintro ⟨t, ht1, ht2⟩
    have ht2' := ht2
    simp only [fsU, Xsem, Sum.elim_inr] at ht2'
    rw [decide_eq_true_eq] at ht2'
    have : c = t.val := ht2'
    have ht1' : t.val ≤ h := by simpa using ht1
    omega
  · intro H
    exact ⟨⟨c, by omega⟩, H, by (simp only [fsU, Xsem, Sum.elim_inr]; rw [decide_eq_true_eq]; rfl)⟩

theorem TB_eq (h' : ℕ) (hh : h' ≤ m) (W : ℕ) :
    TB (fsU k m) h' hh W (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v)))) =
      BitVec.ofInt W (Tsum (dB v) (dA v) (dBB v) (dY v) h' (Rfin v)) := by
  unfold TB Tsum
  rw [Finset.sum_map_toList, ofInt_sum]
  apply Finset.sum_congr rfl; intro σ _
  rw [valid_eq, slot_eq]
  split <;> simp

theorem tzero_eq (t : Fin (2 ^ (k + 1))) (ht : ∀ i, v (iT i) = t.val.testBit i.val) :
    tzeroB (tbU k m) (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v)))) =
      decide (t.val = 0) := by
  unfold tzeroB
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.not_eq_true']
  constructor
  · intro H
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < k + 1
    · have := H ⟨i, hi⟩
      simpa [tbU, ht] using this
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le t.isLt
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · intro H i
    simp [tbU, ht, H]

theorem tt_eq (W : ℕ) (hW : k + 1 ≤ W) (t : Fin (2 ^ (k + 1)))
    (ht : ∀ i, v (iT i) = t.val.testBit i.val) :
    ttB (fsU k m) (rrU k m) (tbU k m) W
        (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v)))) =
      BitVec.ofNat W (t.val * 2 ^ (npiv (Rfin v) + rho (R1B (dB v) (dA v) (dBB v) (Rfin v)))) := by
  unfold ttB
  have hv : tvecB (tbU k m) W (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v)))) =
      BitVec.ofNat W t.val := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    unfold tvecB
    rw [getLsbD_bv _ ⟨i, hi⟩, BitVec.getLsbD_ofNat]
    by_cases hik : i < k + 1
    · rw [dif_pos hik]; simp [tbU, ht, hi]
    · rw [dif_neg hik]
      simp only [hi, decide_true, Bool.true_and]
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le t.isLt
        (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
  rw [hv, dbl_fold]
  congr 3
  unfold pivList
  rw [List.countP_append, List.countP_map, List.countP_map, countP_finRange, countP_finRange]
  rfl

end sem

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

instance consDec {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) : Decidable (cons R) :=
  inferInstanceAs (Decidable (R (Fin.last k, Fin.last k) = false))

theorem card_aff' {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R)
    (D : Finset (Fin (2 ^ k))) (hD : D = SolX R) (inst : DecidablePred (affOn (fB bI AI BI) D)) :
    (@Finset.filter _ (affOn (fB bI AI BI) D) inst Finset.univ).card =
      if cons R then 2 ^ (m - rho (R1B bI AI BI R)) else 2 ^ m := by
  subst hD
  split
  · rename_i hc; exact card_aff bI AI BI hR hc
  · rename_i hc; exact card_aff_empty bI AI BI hR hc

theorem hitsV_le {k m : ℕ} (bI : Fin m → Bool) (AI : Fin m → Fin k → Bool)
    (BI : Fin m → Fin k → Fin k → Bool) (yI : Fin m → Bool) (R : Fin (k + 1) × Fin (k + 1) → Bool) :
    hitsV bI AI BI yI R ≤ 2 ^ k := by
  unfold hitsV
  calc _ ≤ (Finset.univ : Finset (V k)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ k := by simp

theorem FULL_correct (k m h : ℕ) (v : Inp k m → Bool) (b : Fin m → Bool) (A : Fin m → Fin k → Bool)
    (B : Fin m → Fin k → Fin k → Bool) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1)))
    (hb : ∀ j, v (iB j) = b j) (hA : ∀ j i, v (iA j i) = A j i)
    (hB : ∀ j i p, v (iBB j i p) = B j i p) (hy : ∀ j, v (iY j) = y j)
    (ht : ∀ i, v (iT i) = t.val.testBit i.val)
    (prune : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k))) (hp : IsPrune (fB b A B) y prune)
    (D : Finset (Fin (2 ^ k))) (hD : D = prune^[k + 1] Finset.univ)
    (inst : DecidablePred (affOn (fB b A B) D)) :
    FULL k m h v = true ↔
      (2 ^ m ≤ 2 ^ h * (@Finset.filter _ (affOn (fB b A B) D) inst Finset.univ).card ∧
        t.val ≤ Nat.card {x : Fin (2 ^ k) // fB b A B x = y}) := by
  have eb : dB v = b := funext hb
  have eA : dA v = A := funext (fun j => funext (hA j))
  have eB : dBB v = B := funext (fun j => funext (fun i => funext (hB j i)))
  have ey : dY v = y := funext hy
  have hRf : Rfin v = (stepR b A B y)^[k + 1] (R0 k) := by
    unfold Rfin; rw [eb, eA, eB, ey]
  obtain ⟨hok, hsol⟩ := iter_sol b A B y hp (k + 1)
  rw [← hRf] at hok hsol
  have hDS : D = SolX (Rfin v) := by rw [hD, hsol]
  have hfixD := fixed_final hp
  have hfix : ∀ x ∈ SolX (Rfin v), ∀ l, affOn (fB b A B) (SolX (Rfin v)) l →
      dotB l (fB b A B x) = dotB l y := by
    intro x hx l hl
    rw [hsol] at hx hl
    rw [← hfixD] at hx
    exact ((hp _ x).1 hx).2 l hl
  have hsub : Finset.univ.filter (fun x => fB b A B x = y) ⊆ SolX (Rfin v) := by
    rw [hsol]; exact greatest hp _ (fiber_fixed hp) (k + 1)
  have hhits := hits_eq b A B y hsub
  rw [hhits, card_aff' b A B hok D hDS inst]
  have hW1 : 1 ≤ WW k m := by unfold WW; omega
  unfold FULL OUTB
  rw [tzero_eq v t ht, ok_eq v h, TB_eq v, tt_eq v (WW k m) (by unfold WW; omega) t ht]
  rw [eb, eA, eB, ey]
  have hcond : (Sum.elim (Sum.elim v (Rfin v)) (Xsem (Sum.elim v (Rfin v))))
      (rrU k m (Fin.last k, Fin.last k)) = Rfin v (Fin.last k, Fin.last k) := rfl
  rw [hcond]
  have hρm := rho_le (R1B b A B (Rfin v))
  have hnp := npiv_le (Rfin v)
  have hhv := hitsV_le b A B y (Rfin v)
  by_cases hc : cons (Rfin v)
  · have hc' : Rfin v (Fin.last k, Fin.last k) = false := hc
    rw [if_neg (by simp [hc']), if_pos hc]
    have hsmall : 2 ^ m ≤ 2 ^ h * 2 ^ (m - rho (R1B b A B (Rfin v))) ↔
        rho (R1B b A B (Rfin v)) ≤ h := by
      rw [← pow_add, Nat.pow_le_pow_iff_right (by norm_num)]
      omega
    rw [hsmall]
    by_cases hρ : rho (R1B b A B (Rfin v)) ≤ h
    · have hρ' : rho (R1B b A B (Rfin v)) ≤ min h m := le_min hρ hρm
      rw [T_eq b A B y (min h m) hok hc hfix hρ']
      set ρ := rho (R1B b A B (Rfin v))
      set np := npiv (Rfin v)
      set hv := hitsV b A B y (Rfin v)
      have hcast : (2 : ℤ) ^ np * 2 ^ ρ * (hv : ℤ) = ((2 ^ np * 2 ^ ρ * hv : ℕ) : ℤ) := by
        push_cast; ring
      have hWe : WW k m - 1 = 2 * k + m + 3 := by unfold WW; omega
      have ha : 2 ^ np * 2 ^ ρ * hv < 2 ^ (WW k m - 1) := by
        rw [hWe]
        have e1 : 2 ^ np ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hnp
        have e2 : 2 ^ ρ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hρm
        have e3 : 2 ^ np * 2 ^ ρ * hv ≤ 2 ^ k * 2 ^ m * 2 ^ k := by gcongr
        have e4 : 2 ^ k * 2 ^ m * 2 ^ k < 2 ^ (2 * k + m + 3) := by
          rw [show 2 * k + m + 3 = (k + m + k) + 3 by ring, pow_add, pow_add, pow_add]
          have : 0 < 2 ^ k * 2 ^ m * 2 ^ k := by positivity
          omega
        omega
      have hb' : t.val * 2 ^ (np + ρ) < 2 ^ (WW k m - 1) := by
        rw [hWe]
        have e1 : 2 ^ (np + ρ) ≤ 2 ^ (k + m) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have e2 : t.val * 2 ^ (np + ρ) < 2 ^ (k + 1) * 2 ^ (k + m) := by
          calc t.val * 2 ^ (np + ρ) ≤ t.val * 2 ^ (k + m) := Nat.mul_le_mul_left _ e1
            _ < 2 ^ (k + 1) * 2 ^ (k + m) := Nat.mul_lt_mul_of_pos_right t.isLt (by positivity)
        have e3 : 2 ^ (k + 1) * 2 ^ (k + m) ≤ 2 ^ (2 * k + m + 3) := by
          rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [hcast, BitVec.ofInt_natCast, msb_sub (WW k m) _ _ hW1 ha hb']
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      have hpos : 0 < 2 ^ np * 2 ^ ρ := by positivity
      have hrw : t.val * 2 ^ (np + ρ) = t.val * (2 ^ np * 2 ^ ρ) :=
        congrArg (fun z => t.val * z) (pow_add 2 np ρ)
      rw [hrw]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        by_contra hlt0
        have hlt : hv < t.val := Nat.lt_of_not_le hlt0
        apply h2
        calc 2 ^ np * 2 ^ ρ * hv = hv * (2 ^ np * 2 ^ ρ) := by ring
          _ < t.val * (2 ^ np * 2 ^ ρ) := Nat.mul_lt_mul_of_pos_right hlt hpos
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        intro hlt
        have : hv * (2 ^ np * 2 ^ ρ) < t.val * (2 ^ np * 2 ^ ρ) := by
          calc hv * (2 ^ np * 2 ^ ρ) = 2 ^ np * 2 ^ ρ * hv := by ring
            _ < _ := hlt
        have := Nat.lt_of_mul_lt_mul_right this
        omega
    · simp only [hρ, decide_false, Bool.false_and, Bool.false_eq_true, false_and]
  · have hc' : Rfin v (Fin.last k, Fin.last k) = true := by simpa [cons] using hc
    rw [if_pos hc', if_neg hc]
    have h0 : hitsV b A B y (Rfin v) = 0 := by
      unfold hitsV
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z _ hz
      exact not_cons_empty hok hc z hz.1
    rw [h0]
    simp only [decide_eq_true_eq, Nat.le_zero]
    constructor
    · intro ht0
      refine ⟨?_, ht0⟩
      calc 2 ^ m = 1 * 2 ^ m := by ring
        _ ≤ 2 ^ h * 2 ^ m := Nat.mul_le_mul_right _ Nat.one_le_two_pow
    · intro hh; exact hh.2

end PEqualNP.Outside.L_lib_958_aux

namespace PEqualNP.Outside.L_lib_958_aux
open PEqualNP.CircuitLowerBounds

theorem flat_getD {α β : Type} (d : α) (f : β → List α) (c : ℕ) (hf : ∀ x, (f x).length = c) :
    ∀ (L : List β) (j : ℕ) (hj : j < L.length) (r : ℕ), r < c →
      (L.flatMap f).getD (j * c + r) d = (f L[j]).getD r d := by
  intro L
  induction L with
  | nil => intro j hj; simp at hj
  | cons x L ih =>
    intro j hj r hr
    rw [List.flatMap_cons]
    rcases j with _ | j
    · rw [List.getD_append _ _ _ _ (by rw [hf]; omega)]
      simp
    · rw [List.getD_append_right _ _ _ _ (by rw [hf]; nlinarith), hf]
      have e : (j + 1) * c + r - c = j * c + r := by
        rw [Nat.add_mul, one_mul]; omega
      rw [e, ih j (by simp at hj; omega) r hr]
      simp

theorem flat_len {α β : Type} (f : β → List α) (c : ℕ) (hf : ∀ x, (f x).length = c) :
    ∀ L : List β, (L.flatMap f).length = L.length * c := by
  intro L
  induction L with
  | nil => simp
  | cons x L ih => rw [List.flatMap_cons, List.length_append, ih, hf]; simp; ring

def blk {k m : ℕ} (b : Fin m → Bool) (A : Fin m → Fin k → Bool) (B : Fin m → Fin k → Fin k → Bool)
    (j : Fin m) : List Bool :=
  [b j] ++ (List.finRange k).map (A j) ++ (List.finRange k).flatMap (fun i => (List.finRange k).map (B j i))

theorem blk_len {k m : ℕ} (b : Fin m → Bool) (A : Fin m → Fin k → Bool)
    (B : Fin m → Fin k → Fin k → Bool) (j : Fin m) : (blk b A B j).length = 1 + k + k * k := by
  unfold blk
  rw [List.length_append, List.length_append, flat_len _ k (fun i => by simp)]
  simp

def inputL {k m : ℕ} (b : Fin m → Bool) (A : Fin m → Fin k → Bool) (B : Fin m → Fin k → Fin k → Bool)
    (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) : List Bool :=
  (List.finRange m).flatMap (blk b A B) ++ List.ofFn y ++
    (List.range (k + 1)).map (fun i => t.val.testBit i)

theorem inputL_len {k m : ℕ} (b : Fin m → Bool) (A : Fin m → Fin k → Bool)
    (B : Fin m → Fin k → Fin k → Bool) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) :
    (inputL b A B y t).length = m * (1 + k + k * k) + m + k + 1 := by
  unfold inputL
  rw [List.length_append, List.length_append, flat_len _ _ (blk_len b A B)]
  simp
  ring

def pos (k m : ℕ) : Inp k m → ℕ :=
  Sum.elim (fun j => j.val * (1 + k + k * k))
    (Sum.elim (fun ji => ji.1.val * (1 + k + k * k) + (1 + ji.2.val))
      (Sum.elim (fun jip => jip.1.val * (1 + k + k * k) + (1 + k + (jip.2.1.val * k + jip.2.2.val)))
        (Sum.elim (fun j => m * (1 + k + k * k) + j.val)
          (fun i => m * (1 + k + k * k) + m + i.val))))

theorem pos_lt (k m : ℕ) (x : Inp k m) : pos k m x < m * (1 + k + k * k) + m + k + 1 := by
  rcases x with j | ⟨j, i⟩ | ⟨j, i, p⟩ | j | i
  · simp only [pos, Sum.elim_inl]
    have : j.val * (1 + k + k * k) + (1 + k + k * k) ≤ m * (1 + k + k * k) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ j.isLt
    omega
  · simp only [pos, Sum.elim_inl, Sum.elim_inr]
    have : j.val * (1 + k + k * k) + (1 + k + k * k) ≤ m * (1 + k + k * k) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ j.isLt
    have := i.isLt
    omega
  · simp only [pos, Sum.elim_inl, Sum.elim_inr]
    have : j.val * (1 + k + k * k) + (1 + k + k * k) ≤ m * (1 + k + k * k) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ j.isLt
    have : i.val * k + p.val < k * k := by
      have : i.val * k + k ≤ k * k := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ i.isLt
      have := p.isLt
      omega
    omega
  · simp only [pos, Sum.elim_inr, Sum.elim_inl]
    have := j.isLt
    omega
  · simp only [pos, Sum.elim_inr]
    have := i.isLt
    omega

section lay
variable {k m : ℕ} (b : Fin m → Bool) (A : Fin m → Fin k → Bool) (B : Fin m → Fin k → Fin k → Bool)
  (y : Fin m → Bool) (t : Fin (2 ^ (k + 1)))

theorem lay_main (j : Fin m) (r : ℕ) (hr : r < 1 + k + k * k) :
    (inputL b A B y t ++ [false]).getD (j.val * (1 + k + k * k) + r) false =
      (blk b A B j).getD r false := by
  have hlt : j.val * (1 + k + k * k) + r < m * (1 + k + k * k) := by
    have : j.val * (1 + k + k * k) + (1 + k + k * k) ≤ m * (1 + k + k * k) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ j.isLt
    omega
  have hl1 : ((List.finRange m).flatMap (blk b A B)).length = m * (1 + k + k * k) := by
    rw [flat_len _ _ (blk_len b A B)]; simp
  unfold inputL
  rw [List.getD_append _ _ _ _ (by rw [List.length_append, List.length_append]; omega),
    List.getD_append _ _ _ _ (by rw [List.length_append]; omega),
    List.getD_append _ _ _ _ (by omega),
    flat_getD false (blk b A B) (1 + k + k * k) (blk_len b A B) _ j.val (by simp) r hr]
  simp

theorem lay_b (j : Fin m) :
    (inputL b A B y t ++ [false]).getD (pos k m (iB j)) false = b j := by
  have := lay_main b A B y t j 0 (by omega)
  simp only [add_zero] at this
  simp only [pos, iB, Sum.elim_inl]
  rw [this]
  unfold blk
  rw [List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simp)]
  simp

theorem lay_A (j : Fin m) (i : Fin k) :
    (inputL b A B y t ++ [false]).getD (pos k m (iA j i)) false = A j i := by
  have := lay_main b A B y t j (1 + i.val) (by have := i.isLt; omega)
  simp only [pos, iA, Sum.elim_inl, Sum.elim_inr]
  rw [this]
  unfold blk
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_singleton, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem lay_B (j : Fin m) (i p : Fin k) :
    (inputL b A B y t ++ [false]).getD (pos k m (iBB j i p)) false = B j i p := by
  have hip : i.val * k + p.val < k * k := by
    have : i.val * k + k ≤ k * k := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ i.isLt
    have := p.isLt
    omega
  have := lay_main b A B y t j (1 + k + (i.val * k + p.val)) (by omega)
  simp only [pos, iBB, Sum.elim_inl, Sum.elim_inr]
  rw [this]
  unfold blk
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_append, List.length_singleton, List.length_map, List.length_finRange]
  rw [show 1 + k + (i.val * k + p.val) - (1 + k) = i.val * k + p.val by omega]
  rw [flat_getD false _ k (fun i => by simp) _ i.val (by simp) p.val p.isLt]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem lay_y (j : Fin m) :
    (inputL b A B y t ++ [false]).getD (pos k m (iY j)) false = y j := by
  have hl1 : ((List.finRange m).flatMap (blk b A B)).length = m * (1 + k + k * k) := by
    rw [flat_len _ _ (blk_len b A B)]; simp
  simp only [pos, iY, Sum.elim_inl, Sum.elim_inr]
  unfold inputL
  have := j.isLt
  rw [List.getD_append _ _ _ _ (by simp [hl1] <;> omega),
    List.getD_append _ _ _ _ (by simp [hl1] <;> omega),
    List.getD_append_right _ _ _ _ (by omega), hl1, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ (by simp <;> omega)]
  simp

theorem lay_t (i : Fin (k + 1)) :
    (inputL b A B y t ++ [false]).getD (pos k m (iT i)) false = t.val.testBit i.val := by
  have hl1 : ((List.finRange m).flatMap (blk b A B)).length = m * (1 + k + k * k) := by
    rw [flat_len _ _ (blk_len b A B)]; simp
  simp only [pos, iT, Sum.elim_inr]
  unfold inputL
  have := i.isLt
  rw [List.getD_append _ _ _ _ (by simp [hl1] <;> omega),
    List.getD_append_right _ _ _ _ (by simp [hl1] <;> omega),
    List.length_append, hl1, List.length_ofFn,
    show m * (1 + k + k * k) + m + i.val - (m * (1 + k + k * k) + m) = i.val by omega,
    List.getD_eq_getElem _ _ (by simp <;> omega)]
  simp

end lay

theorem size_bound (k m h : ℕ) :
    2 ^ (min h m) * (8192 * NN k m ^ 9) + 1 ≤ 2 ^ 34 * (k + m + 4) ^ 14 * 2 ^ (min h m) := by
  have hN : NN k m = k + m + 4 := rfl
  rw [hN]
  set N := k + m + 4
  have h1 : 1 ≤ N := by omega
  have hp : 1 ≤ 2 ^ (min h m) := Nat.one_le_two_pow
  have p : N ^ 9 ≤ N ^ 14 := Nat.pow_le_pow_right h1 (by norm_num)
  have p0 : 1 ≤ N ^ 14 := Nat.one_le_pow _ _ h1
  have e : 8192 * N ^ 9 + 1 ≤ 2 ^ 34 * N ^ 14 := by
    have : (2 : ℕ) ^ 34 = 17179869184 := by norm_num
    rw [this]; omega
  calc 2 ^ (min h m) * (8192 * N ^ 9) + 1 ≤ 2 ^ (min h m) * (8192 * N ^ 9) + 2 ^ (min h m) := by
        omega
    _ = 2 ^ (min h m) * (8192 * N ^ 9 + 1) := by ring
    _ ≤ 2 ^ (min h m) * (2 ^ 34 * N ^ 14) := Nat.mul_le_mul_left _ e
    _ = 2 ^ 34 * N ^ 14 * 2 ^ (min h m) := by ring

end PEqualNP.Outside.L_lib_958_aux

theorem PEqualNP.Outside.L_lib_958 : (∀ (k m h : Nat),
  let X := Fin (2^k)
  let Y := Fin m → Bool

  let dot := fun {d : Nat} (a b : Fin d → Bool) =>
    (List.finRange d).foldl (fun t i => xor t (a i && b i)) false

  let bits := fun (d x : Nat) => (List.range d).map (fun i => x.testBit i)
  let ks := List.finRange k
  let ms := List.finRange m
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (m*(1+k+k*k)+m+k+1) C ∧
    C.size ≤ 2^34*(k+m+4)^14*2^(min h m) ∧
    ∀ (b : Y) (A : Fin m → Fin k → Bool) (B : Fin m → Fin k → Fin k → Bool)
      (y : Y) (t : Fin (2^(k+1))),
      let f := fun (x : X) (j : Fin m) =>
        (ks.foldl (fun acc i => ks.foldl (fun v p =>
          xor v ((B j i p && x.val.testBit i.val) && x.val.testBit p.val)) acc)
          (xor (b j) (dot (A j) (fun i => x.val.testBit i.val))))

      let affineOn := fun (S : Finset X) (l : Y) =>
        ∃ (a : Fin k → Bool) (b : Bool), ∀ z ∈ S,
          dot l (f z) = xor b (dot a (fun i => z.val.testBit i.val))
      let prune := fun (S : Finset X) => S.filter (fun x =>
        ∀ l : Y, affineOn S l → dot l (f x) = dot l y)
      let finish := fun (S : Finset X) =>
        (List.range (k+1)).foldl (fun D _ => prune D) S
      let small := fun (S : Finset X) =>
        2^m ≤ 2^h * ((Finset.univ : Finset Y).filter (affineOn S)).card

      let D := finish Finset.univ
      let hits := Nat.card {x : X // f x = y}
      let input := ms.flatMap (fun j =>
        [b j] ++ ks.map (A j) ++ ks.flatMap (fun i => ks.map (B j i))) ++
        List.ofFn y ++ bits (k+1) t.val
      prune D = D ∧ (∀ V : Finset X, prune V = V → V ⊆ D) ∧
        C.eval input = decide (small D ∧ t.val ≤ hits)) := by
  intro k m h
  obtain ⟨gs, outs, hg, hrb, hlen, -, hev⟩ :=
    PEqualNP.Outside.L_lib_958_aux.Cmp.extract (PEqualNP.Outside.L_lib_958_aux.cFull k m h)
      (m * (1 + k + k * k) + m + k + 1) (PEqualNP.Outside.L_lib_958_aux.pos k m)
      (fun x => Nat.lt_succ_of_lt (PEqualNP.Outside.L_lib_958_aux.pos_lt k m x))
  refine ⟨⟨gs, outs ()⟩, hg, hrb (outs ()), ?_, ?_⟩
  · exact le_trans hlen (PEqualNP.Outside.L_lib_958_aux.size_bound k m h)
  · intro b A B y t f affineOn prune finish small D hits input
    have hp : PEqualNP.Outside.L_lib_958_aux.IsPrune (PEqualNP.Outside.L_lib_958_aux.fB b A B) y
        prune := fun S x => Finset.mem_filter
    have hD : D = prune^[k + 1] Finset.univ :=
      PEqualNP.Outside.L_lib_958_aux.foldl_range_iter prune (k + 1) Finset.univ
    refine ⟨?_, ?_, ?_⟩
    · rw [hD]
      exact PEqualNP.Outside.L_lib_958_aux.fixed_final hp
    · intro V hV
      rw [hD]
      exact PEqualNP.Outside.L_lib_958_aux.greatest hp V hV (k + 1)
    · have hin := PEqualNP.Outside.L_lib_958_aux.inputL_len b A B y t
      have he := hev (outs ()) (PEqualNP.Outside.L_lib_958_aux.inputL b A B y t) hin ()
      show ((⟨gs, outs ()⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
        (PEqualNP.Outside.L_lib_958_aux.inputL b A B y t)).getD (outs ()) false = _
      rw [he, Bool.eq_iff_iff, decide_eq_true_iff]
      exact PEqualNP.Outside.L_lib_958_aux.FULL_correct k m h _ b A B y t
        (PEqualNP.Outside.L_lib_958_aux.lay_b b A B y t)
        (PEqualNP.Outside.L_lib_958_aux.lay_A b A B y t)
        (PEqualNP.Outside.L_lib_958_aux.lay_B b A B y t)
        (PEqualNP.Outside.L_lib_958_aux.lay_y b A B y t)
        (PEqualNP.Outside.L_lib_958_aux.lay_t b A B y t) prune hp D hD _
