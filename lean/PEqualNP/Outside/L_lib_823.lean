import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_823
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

theorem fourier_id (K a b c W : ℕ) (f : V a → BitVec W) (g : V b → BitVec W)
    (Lx : Matrix (Fin a) (Fin (K + 1)) (ZMod 2)) (Ly : Matrix (Fin b) (Fin (K + 1)) (ZMod 2))
    (Lz : Matrix (Fin c) (Fin (K + 1)) (ZMod 2)) (σ : Fin K → ZMod 2) (z : V c) :
    (∑ ζ : V c, sgn (ζ ⬝ᵥ z) * ∑ lam : V (K + 1), if Lz.mulVec lam = ζ then
        (if lam (Fin.last K) ≠ 0 then 0 else
          (if (∑ s : Fin K, lam s.castSucc * σ s) ≠ 0 then
            -((∑ x, sgn (Lx.mulVec lam ⬝ᵥ x) * f x) * (∑ y, sgn (Ly.mulVec lam ⬝ᵥ y) * g y))
          else (∑ x, sgn (Lx.mulVec lam ⬝ᵥ x) * f x) * (∑ y, sgn (Ly.mulVec lam ⬝ᵥ y) * g y)))
        else 0)
      = 2 ^ K * ∑ x, ∑ y,
          if (∀ s : Fin K, (∑ j, Lx j s.castSucc * x j) + (∑ j, Ly j s.castSucc * y j) +
              (∑ j, Lz j s.castSucc * z j) = σ s) then f x * g y else 0 := by
  have h11 : (1 : ZMod 2) ≠ 0 := by decide
  have step1 : ∀ (w : V (K + 1) → BitVec W),
      (∑ ζ : V c, sgn (ζ ⬝ᵥ z) * ∑ lam : V (K + 1), if Lz.mulVec lam = ζ then w lam else 0) =
        ∑ lam : V (K + 1), sgn (Lz.mulVec lam ⬝ᵥ z) * w lam := by
    intro w
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun lam _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [step1, fg_split]
  simp only [Fin.snoc_last, Fin.snoc_castSucc, ne_eq, not_true_eq_false, if_false, h11,
    not_false_eq_true, if_true, mul_zero, Finset.sum_const_zero, add_zero]
  have term : ∀ mu : V K,
      sgn (Lz.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ z) *
        (if (∑ s : Fin K, mu s * σ s) = 0 then
          (∑ x, sgn (Lx.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ x) * f x) *
            (∑ y, sgn (Ly.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ y) * g y)
         else
          -((∑ x, sgn (Lx.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ x) * f x) *
            (∑ y, sgn (Ly.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ y) * g y)))
      = ∑ x, ∑ y, sgn (∑ s : Fin K, mu s * ((∑ j, Lx j s.castSucc * x j) +
          (∑ j, Ly j s.castSucc * y j) + (∑ j, Lz j s.castSucc * z j) + σ s)) * (f x * g y) := by
    intro mu
    have hs : ∀ x y, (sgn (∑ s : Fin K, mu s * ((∑ j, Lx j s.castSucc * x j) +
          (∑ j, Ly j s.castSucc * y j) + (∑ j, Lz j s.castSucc * z j) + σ s)) : BitVec W) =
        sgn (Lz.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ z) * sgn (∑ s : Fin K, mu s * σ s) *
          sgn (Lx.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ x) *
          sgn (Ly.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ y) := by
      intro x y
      rw [fg_dot, fg_dot, fg_dot, ← fg_sgn_add, ← fg_sgn_add, ← fg_sgn_add]
      congr 1
      simp only [mul_add, Finset.sum_add_distrib]
      ring
    have hif : ∀ t : BitVec W, (if (∑ s : Fin K, mu s * σ s) = 0 then t else -t) =
        sgn (∑ s : Fin K, mu s * σ s) * t := by
      intro t
      unfold sgn
      split_ifs <;> simp
    rw [hif, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hs]
    ring
  simp only [ite_not]
  rw [Finset.sum_congr rfl (fun mu _ => term mu)]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_mul, fg_char]
  have hiff : ((fun s : Fin K => (∑ j, Lx j s.castSucc * x j) + (∑ j, Ly j s.castSucc * y j) +
      (∑ j, Lz j s.castSucc * z j) + σ s) = 0) ↔
      (∀ s : Fin K, (∑ j, Lx j s.castSucc * x j) + (∑ j, Ly j s.castSucc * y j) +
        (∑ j, Lz j s.castSucc * z j) = σ s) := by
    constructor
    · intro h s
      have := congrFun h s
      exact CharTwo.add_eq_zero.mp this
    · intro h
      funext s
      exact CharTwo.add_eq_zero.mpr (h s)
  by_cases hc : (∀ s : Fin K, (∑ j, Lx j s.castSucc * x j) + (∑ j, Ly j s.castSucc * y j) +
        (∑ j, Lz j s.castSucc * z j) = σ s)
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
    simp

theorem kernel_id (K a b c W : ℕ) (f : V a → BitVec W) (g : V b → BitVec W)
    (Lx : Matrix (Fin a) (Fin (K + 1)) (ZMod 2)) (Ly : Matrix (Fin b) (Fin (K + 1)) (ZMod 2))
    (Lz : Matrix (Fin c) (Fin (K + 1)) (ZMod 2)) (dead : Fin K → Bool)
    (S : V a → V b → V c → Prop) [∀ x y z, Decidable (S x y z)]
    (hsol : ∀ lam : V (K + 1), lam (Fin.last K) = 1 →
      S (Lx.mulVec lam) (Ly.mulVec lam) (Lz.mulVec lam))
    (huniq : ∀ x y z, S x y z → ∃! lam : V (K + 1), lam (Fin.last K) = 1 ∧
      (∀ s : Fin K, dead s = true → lam s.castSucc = 0) ∧
      Lx.mulVec lam = x ∧ Ly.mulVec lam = y ∧ Lz.mulVec lam = z) (z : V c) :
    (∑ lam : V (K + 1), if Lz.mulVec lam = z then
        (if (lam (Fin.last K) = 0 ∨ ∃ s : Fin K, dead s = true ∧ lam s.castSucc ≠ 0) then 0
         else f (Lx.mulVec lam) * g (Ly.mulVec lam)) else 0)
      = ∑ x, ∑ y, if S x y z then f x * g y else 0 := by
  classical
  have hL : (∑ lam : V (K + 1), if Lz.mulVec lam = z then
        (if (lam (Fin.last K) = 0 ∨ ∃ s : Fin K, dead s = true ∧ lam s.castSucc ≠ 0) then 0
         else f (Lx.mulVec lam) * g (Ly.mulVec lam)) else 0) =
      ∑ lam ∈ Finset.univ.filter (fun lam : V (K + 1) => Lz.mulVec lam = z ∧
        lam (Fin.last K) = 1 ∧ ∀ s : Fin K, dead s = true → lam s.castSucc = 0),
        f (Lx.mulVec lam) * g (Ly.mulVec lam) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun lam _ => ?_
    by_cases h1 : Lz.mulVec lam = z
    · by_cases h2 : lam (Fin.last K) = 0
      · have : ¬ lam (Fin.last K) = 1 := by rw [h2]; decide
        simp [h1, h2]
      · have h3 : lam (Fin.last K) = 1 := (fg_z2 _).resolve_left h2
        by_cases h4 : ∃ s : Fin K, dead s = true ∧ lam s.castSucc ≠ 0
        · have : ¬ ∀ s : Fin K, dead s = true → lam s.castSucc = 0 := by
            intro hh
            obtain ⟨s, hs, hne⟩ := h4
            exact hne (hh s hs)
          rw [if_pos h1, if_pos (Or.inr h4), if_neg (fun hh => this hh.2.2)]
        · have : ∀ s : Fin K, dead s = true → lam s.castSucc = 0 := by
            intro s hs
            by_contra hne
            exact h4 ⟨s, hs, hne⟩
          rw [if_pos h1, if_neg (fun hh => hh.elim h2 h4), if_pos ⟨h1, h3, this⟩]
    · rw [if_neg h1, if_neg (fun hh => h1 hh.1)]
  have hR : (∑ x, ∑ y, if S x y z then f x * g y else 0) =
      ∑ p ∈ Finset.univ.filter (fun p : V a × V b => S p.1 p.2 z), f p.1 * g p.2 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [hL, hR]
  refine Finset.sum_bij (fun lam _ => (Lx.mulVec lam, Ly.mulVec lam)) ?_ ?_ ?_ ?_
  · intro lam hlam
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
    have := hsol lam hlam.2.1
    rw [hlam.1] at this
    exact this
  · intro l1 h1 l2 h2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have hS := hsol l1 h1.2.1
    obtain ⟨l0, _, hu⟩ := huniq _ _ _ hS
    have e1 := hu l1 ⟨h1.2.1, h1.2.2, rfl, rfl, rfl⟩
    have e2 := hu l2 ⟨h2.2.1, h2.2.2, (congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm,
      h2.1.trans h1.1.symm⟩
    rw [e1, e2]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨l0, ⟨hl1, hl2, hx, hy, hz⟩, _⟩ := huniq _ _ _ hp
    refine ⟨l0, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, hl1, hl2⟩
    · exact Prod.ext hx hy
  · intro lam _
    rfl

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

theorem la_rank {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Hf)) =
      rkOf (gj _ (sysBits Hf rhs)) := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv (sysBits Hf rhs)
  have hb : ∃ b : {p : Fin N // pv (gj _ (sysBits Hf rhs)) p = true} → V N,
      b = fun p q => mat (gj _ (sysBits Hf rhs)) (cl m p.1) (cl m q) := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ := hb
  have hrho : ∀ k : Fin (m + N + 1),
      (fun q : Fin N => mat (gj _ (sysBits Hf rhs)) k (cl m q)) ∈
        Submodule.span (ZMod 2) (Set.range b) := by
    intro k
    by_cases hk : k.val < N ∧ gj _ (sysBits Hf rhs) (k, k) = true
    · apply Submodule.subset_span
      refine ⟨⟨⟨k.val, hk.1⟩, hk.2⟩, ?_⟩
      rw [hbdef]
      rfl
    · have hz : (fun q : Fin N => mat (gj _ (sysBits Hf rhs)) k (cl m q)) = 0 := by
        funext q
        apply fh_mat_false
        by_cases hkk : gj _ (sysBits Hf rhs) (k, k) = true
        · apply gj_upper
          have : ¬ k.val < N := fun h => hk ⟨h, hkk⟩
          show q.val < k.val
          have := q.isLt
          omega
        · exact gj_zerorow _ k (by simpa using hkk) _
      rw [hz]
      exact Submodule.zero_mem _
  have hmu : ∀ k : Fin (m + N + 1),
      (fun q : Fin N => mat (sysBits Hf rhs) k (cl m q)) ∈
        Submodule.span (ZMod 2) (Set.range Hf) := by
    intro k
    by_cases hk : k.val < m
    · apply Submodule.subset_span
      refine ⟨⟨k.val, hk⟩, ?_⟩
      funext q
      rw [fh_sys_cl, dif_pos hk]
    · have hz : (fun q : Fin N => mat (sysBits Hf rhs) k (cl m q)) = 0 := by
        funext q
        rw [fh_sys_cl, dif_neg hk]
        rfl
      rw [hz]
      exact Submodule.zero_mem _
  have hspan : Submodule.span (ZMod 2) (Set.range Hf) =
      Submodule.span (ZMod 2) (Set.range b) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have e : Hf i = ∑ k, U' ⟨i.val, by omega⟩ k •
          (fun q : Fin N => mat (gj _ (sysBits Hf rhs)) k (cl m q)) := by
        funext q
        have := congrFun (congrFun h2 ⟨i.val, by omega⟩) (cl m q)
        rw [fh_sys_cl, dif_pos i.isLt, Matrix.mul_apply] at this
        rw [Finset.sum_apply]
        exact this
      rw [e]
      exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hrho k))
    · apply Submodule.span_le.mpr
      rintro _ ⟨p, rfl⟩
      have e : b p = ∑ k, U (cl m p.1) k •
          (fun q : Fin N => mat (sysBits Hf rhs) k (cl m q)) := by
        funext q
        have := congrFun (congrFun h1 (cl m p.1)) (cl m q)
        rw [Matrix.mul_apply] at this
        rw [Finset.sum_apply, hbdef]
        exact this
      rw [e]
      exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hmu k))
  have hli : LinearIndependent (ZMod 2) b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have key : ∀ x : {p : Fin N // pv (gj _ (sysBits Hf rhs)) p = true},
        b x i.1 = if x = i then 1 else 0 := by
      intro x
      rw [hbdef]
      show mat (gj _ (sysBits Hf rhs)) (cl m x.1) (cl m i.1) = _
      have hpc := gj_pivcol (sysBits Hf rhs) (cl m i.1) i.2 (cl m x.1)
      by_cases hx : x = i
      · subst hx
        rw [if_pos rfl]
        exact fh_mat_true _ _ _ x.2
      · rw [if_neg hx]
        have hne : cl m x.1 ≠ cl m i.1 := by
          intro h
          apply hx
          apply Subtype.ext
          apply Fin.ext
          have h' : (cl m x.1).val = (cl m i.1).val := congrArg Fin.val h
          exact h'
        rw [decide_eq_false hne] at hpc
        exact fh_mat_false _ _ _ hpc
    have := congrFun hg i.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, key, Pi.zero_apply] at this
    simp at this
    exact this
  rw [hspan, finrank_span_eq_card hli, Fintype.card_subtype]
  rfl

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

theorem la_rows {m N : ℕ} (K : ℕ) (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits Hf rhs) (rc m N, rc m N) = false)
    (hr : rkOf (gj _ (sysBits Hf rhs)) ≤ K) (v : V N) :
    (∀ s : Fin K,
      (∑ j : Fin N, (if rowSlot K (gj _ (sysBits Hf rhs)) s (cl m j) then (1 : ZMod 2) else 0) * v j)
        = (if rowSlot K (gj _ (sysBits Hf rhs)) s (rc m N) then 1 else 0)) ↔
      ∀ i, Hf i ⬝ᵥ v = rhs i := by
  rw [fh_main_iff Hf rhs h]
  have hpc : ∀ p, gj _ (sysBits Hf rhs) (p, p) = true →
      ∀ i, gj _ (sysBits Hf rhs) (i, p) = decide (i = p) := fun p hp i => gj_pivcol _ p hp i
  constructor
  · intro hs p hp
    have hlt : cntP (gj _ (sysBits Hf rhs)) p < K := (fh_cntP_lt _ p hp).trans_le hr
    have e := hs ⟨cntP (gj _ (sysBits Hf rhs)) p, hlt⟩
    simp only [fh_rowSlot_eq K _ p hp ⟨_, hlt⟩ rfl] at e
    have e' : ∑ j, mat (gj _ (sysBits Hf rhs)) (cl m p) (cl m j) * v j =
        mat (gj _ (sysBits Hf rhs)) (cl m p) (rc m N) := e
    rw [fh_row_split _ hpc p hp] at e'
    linear_combination e' - (∑ q, if pv (gj _ (sysBits Hf rhs)) q = false then
      mat (gj _ (sysBits Hf rhs)) (cl m p) (cl m q) * v q else 0) * fh_two
  · intro hs s
    by_cases hex : ∃ p : Fin N, pv (gj _ (sysBits Hf rhs)) p = true ∧
        cntP (gj _ (sysBits Hf rhs)) p = s.val
    · obtain ⟨p, hp, hc⟩ := hex
      simp only [fh_rowSlot_eq K _ p hp s hc]
      show ∑ j, mat (gj _ (sysBits Hf rhs)) (cl m p) (cl m j) * v j =
        mat (gj _ (sysBits Hf rhs)) (cl m p) (rc m N)
      rw [fh_row_split _ hpc p hp, hs p hp]
      linear_combination (∑ q, if pv (gj _ (sysBits Hf rhs)) q = false then
        mat (gj _ (sysBits Hf rhs)) (cl m p) (cl m q) * v q else 0) * fh_two
    · simp only [fh_rowSlot_none K _ s hex]
      simp

def fh_E {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (q j : Fin N) : ZMod 2 :=
  (if j = q then 1 else 0) + mat R (cl m j) (cl m q)

def fh_mu {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (lam : V K)
    (q : Fin N) : ZMod 2 :=
  ∑ s : Fin K, if s.val = cntN R q then lam s else 0

theorem fh_xor_val (x y : Bool) :
    (if xor x y = true then (1 : ZMod 2) else 0) =
      (if x = true then 1 else 0) + (if y = true then 1 else 0) := by
  revert x y; decide

theorem fh_kerSlot_val {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (s : Fin K) (j : Fin N) :
    (if kerSlot K R s j = true then (1 : ZMod 2) else 0) =
      ∑ q : Fin N, if (pv R q = false ∧ cntN R q = s.val) then fh_E R q j else 0 := by
  by_cases hex : ∃ q0 : Fin N, pv R q0 = false ∧ cntN R q0 = s.val
  · obtain ⟨q0, h0, hc⟩ := hex
    rw [Finset.sum_eq_single q0]
    · rw [if_pos (show pv R q0 = false ∧ cntN R q0 = s.val from ⟨h0, hc⟩)]
      have : kerSlot K R s j = xor (decide (j = q0)) (R (cl m j, cl m q0)) := by
        unfold kerSlot
        rw [Bool.eq_iff_iff]
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨q, hq, hcq, hx⟩
          have := fh_cntN_inj R q q0 hq h0 (hcq.trans hc.symm)
          subst this
          exact hx
        · intro hx
          exact ⟨q0, h0, hc, hx⟩
      rw [this, fh_xor_val]
      unfold fh_E mat
      simp only [decide_eq_true_eq]
    · intro q _ hq
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hq (fh_cntN_inj R q q0 h1 h0 (h2.trans hc.symm))
    · intro hn
      exact absurd (Finset.mem_univ q0) hn
  · have : kerSlot K R s j = false := by
      unfold kerSlot
      rw [decide_eq_false_iff_not]
      rintro ⟨q, h1, h2, _⟩
      exact hex ⟨q, h1, h2⟩
    rw [this, if_neg (by simp)]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hex ⟨q, h1, h2⟩

theorem fh_kerPt_eq {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (lam : V K) (j : Fin N) :
    kerPt K R lam j = mat R (cl m j) (rc m N) +
      ∑ q : Fin N, if pv R q = false then fh_mu K R lam q * fh_E R q j else 0 := by
  unfold kerPt
  show mat R (cl m j) (rc m N) + _ = _
  congr 1
  simp only [fh_kerSlot_val, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : pv R q = false
  · rw [if_pos hq]
    unfold fh_mu
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : s.val = cntN R q
    · rw [if_pos ⟨hq, h.symm⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.2.symm), if_neg h, mul_zero, zero_mul]
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro s _
    rw [if_neg (fun hh => hq hh.1), mul_zero]

theorem fh_ker_np {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (hzr : ∀ q, R (q, q) = false → ∀ j, R (q, j) = false)
    (lam : V K) (j : Fin N) (hj : pv R j = false) :
    kerPt K R lam j = fh_mu K R lam j := by
  rw [fh_kerPt_eq, fh_mat_false R _ _ (hzr (cl m j) hj _), zero_add]
  rw [Finset.sum_eq_single j]
  · rw [if_pos hj]
    unfold fh_E
    rw [if_pos rfl, fh_mat_false R _ _ (hzr (cl m j) hj _), add_zero, mul_one]
  · intro q _ hq
    by_cases hv : pv R q = false
    · rw [if_pos hv]
      unfold fh_E
      rw [if_neg (fun h => hq h.symm), fh_mat_false R _ _ (hzr (cl m j) hj _), add_zero, mul_zero]
    · rw [if_neg hv]
  · intro hn
    exact absurd (Finset.mem_univ j) hn

theorem fh_ker_pv {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (lam : V K) (j : Fin N) (hj : pv R j = true) :
    kerPt K R lam j = mat R (cl m j) (rc m N) +
      ∑ q, if pv R q = false then mat R (cl m j) (cl m q) * fh_mu K R lam q else 0 := by
  rw [fh_kerPt_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  by_cases hv : pv R q = false
  · rw [if_pos hv, if_pos hv]
    unfold fh_E
    have hne : ¬ j = q := by
      intro h
      rw [h, hv] at hj
      exact Bool.noConfusion hj
    rw [if_neg hne, zero_add, mul_comm]
  · rw [if_neg hv, if_neg hv]

theorem fh_mu_slot {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (lam : V K) (q : Fin N) (s : Fin K) (hs : cntN R q = s.val) : fh_mu K R lam q = lam s := by
  unfold fh_mu
  rw [Finset.sum_eq_single s]
  · rw [if_pos hs.symm]
  · intro s' _ hne
    rw [if_neg]
    intro h
    apply hne
    apply Fin.ext
    exact h.trans hs
  · intro hn
    exact absurd (Finset.mem_univ s) hn

theorem la_ker_sol {m N : ℕ} (K : ℕ) (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits Hf rhs) (rc m N, rc m N) = false) (lam : V K) :
    ∀ i, Hf i ⬝ᵥ kerPt K (gj _ (sysBits Hf rhs)) lam = rhs i := by
  rw [fh_main_iff Hf rhs h]
  intro p hp
  rw [fh_ker_pv K _ lam p hp]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : pv (gj _ (sysBits Hf rhs)) q = false
  · rw [if_pos hq, if_pos hq, fh_ker_np K _ (fun q hq j => gj_zerorow _ q hq j) lam q hq]
  · rw [if_neg hq, if_neg hq]

theorem la_ker_uniq {m N : ℕ} (K : ℕ) (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits Hf rhs) (rc m N, rc m N) = false)
    (hk : N - rkOf (gj _ (sysBits Hf rhs)) ≤ K) (v : V N) (hv : ∀ i, Hf i ⬝ᵥ v = rhs i) :
    ∃! lam : V K, (∀ s, deadSlot K (gj _ (sysBits Hf rhs)) s = true → lam s = 0) ∧
      kerPt K (gj _ (sysBits Hf rhs)) lam = v := by
  have hzr : ∀ q, gj _ (sysBits Hf rhs) (q, q) = false →
      ∀ j, gj _ (sysBits Hf rhs) (q, j) = false := fun q hq j => gj_zerorow _ q hq j
  have hv' := (fh_main_iff Hf rhs h v).mp hv
  have hl : ∃ lam0 : V K, lam0 = fun s => ∑ q : Fin N,
      if (pv (gj _ (sysBits Hf rhs)) q = false ∧ cntN (gj _ (sysBits Hf rhs)) q = s.val)
        then v q else 0 := ⟨_, rfl⟩
  obtain ⟨lam0, hlam0⟩ := hl
  have hdead : ∀ (lam : V K) (s : Fin K),
      (¬ ∃ q : Fin N, pv (gj _ (sysBits Hf rhs)) q = false ∧
        cntN (gj _ (sysBits Hf rhs)) q = s.val) →
      deadSlot K (gj _ (sysBits Hf rhs)) s = true := by
    intro lam s hs
    unfold deadSlot
    rw [decide_eq_true_eq]
    exact hs
  have hmask0 : ∀ s, deadSlot K (gj _ (sysBits Hf rhs)) s = true → lam0 s = 0 := by
    intro s hs
    unfold deadSlot at hs
    rw [decide_eq_true_eq] at hs
    rw [hlam0]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hs ⟨q, h1, h2⟩
  have hmu0 : ∀ q : Fin N, pv (gj _ (sysBits Hf rhs)) q = false →
      fh_mu K (gj _ (sysBits Hf rhs)) lam0 q = v q := by
    intro q hq
    have hlt : cntN (gj _ (sysBits Hf rhs)) q < K := (fh_cntN_lt _ q hq).trans_le hk
    rw [fh_mu_slot K _ lam0 q ⟨_, hlt⟩ rfl, hlam0]
    show (∑ q' : Fin N, if (pv (gj _ (sysBits Hf rhs)) q' = false ∧
      cntN (gj _ (sysBits Hf rhs)) q' = cntN (gj _ (sysBits Hf rhs)) q) then v q' else 0) = v q
    rw [Finset.sum_eq_single q]
    · rw [if_pos ⟨hq, rfl⟩]
    · intro q' _ hne
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hne (fh_cntN_inj _ q' q h1 hq h2)
    · intro hn
      exact absurd (Finset.mem_univ q) hn
  have hpt0 : kerPt K (gj _ (sysBits Hf rhs)) lam0 = v := by
    funext j
    by_cases hj : pv (gj _ (sysBits Hf rhs)) j = true
    · rw [fh_ker_pv K _ lam0 j hj, hv' j hj]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : pv (gj _ (sysBits Hf rhs)) q = false
      · rw [if_pos hq, if_pos hq, hmu0 q hq]
      · rw [if_neg hq, if_neg hq]
    · have hj' : pv (gj _ (sysBits Hf rhs)) j = false := by simpa using hj
      rw [fh_ker_np K _ hzr lam0 j hj', hmu0 j hj']
  refine ⟨lam0, ⟨hmask0, hpt0⟩, ?_⟩
  rintro lam ⟨hm, hp⟩
  funext s
  by_cases hex : ∃ q : Fin N, pv (gj _ (sysBits Hf rhs)) q = false ∧
      cntN (gj _ (sysBits Hf rhs)) q = s.val
  · obtain ⟨q, hq, hc⟩ := hex
    rw [← fh_mu_slot K _ lam q s hc, ← fh_mu_slot K _ lam0 q s hc, hmu0 q hq,
      ← fh_ker_np K _ hzr lam q hq, hp]
  · rw [hm s (hdead lam s hex), hmask0 s (hdead lam s hex)]

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

theorem ft_mulVec {m N d : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (e : Fin d → Fin N) (lam : V (K + 1)) (hl : lam (Fin.last K) = 1) (j : Fin d) :
    (mat (LnBits K R e)).mulVec lam j = kerPt K R (fun s => lam s.castSucc) (e j) := by
  unfold Matrix.mulVec dotProduct kerPt
  rw [Fin.sum_univ_castSucc, add_comm]
  congr 1
  · simp [mat, LnBits, hl]
  · apply Finset.sum_congr rfl
    intro s _
    simp [mat, LnBits, mul_comm]

theorem ft_kerPt {a b c m : ℕ} (K : ℕ)
    (R : Fin (m + (a + b + c) + 1) × Fin (m + (a + b + c) + 1) → Bool)
    (lam : V (K + 1)) (hl : lam (Fin.last K) = 1) :
    kerPt K R (fun s => lam s.castSucc) =
      join3 ((mat (LnBits K R (nx (b := b) (c := c)))).mulVec lam,
        (mat (LnBits K R (ny (a := a) (c := c)))).mulVec lam,
        (mat (LnBits K R (nz (a := a) (b := b)))).mulVec lam) := by
  apply ft_ext
  · intro j; rw [ft_join_nx]; exact (ft_mulVec K R _ lam hl j).symm
  · intro j; rw [ft_join_ny]; exact (ft_mulVec K R _ lam hl j).symm
  · intro j; rw [ft_join_nz]; exact (ft_mulVec K R _ lam hl j).symm

theorem ft_join_inj {a b c : ℕ} (h h' : V a × V b × V c) (e : join3 h = join3 h') : h = h' := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext j; rw [← ft_join_nx h, ← ft_join_nx h', e]
  · funext j; rw [← ft_join_ny h, ← ft_join_ny h', e]
  · funext j; rw [← ft_join_nz h, ← ft_join_nz h', e]

theorem tr_rank {a b c m : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) =
      rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) := by
  rw [← la_rank]
  let e : (V a × V b × V c) →ₗ[ZMod 2] V (a + b + c) :=
    { toFun := join3
      map_add' := by
        intro u w
        apply ft_ext
        · intro j; simp [ft_join_nx]
        · intro j; simp [ft_join_ny]
        · intro j; simp [ft_join_nz]
      map_smul' := by
        intro r u
        apply ft_ext
        · intro j; simp [ft_join_nx]
        · intro j; simp [ft_join_ny]
        · intro j; simp [ft_join_nz] }
  have hinj : Function.Injective e := fun h h' he => ft_join_inj h h' he
  have hr : Set.range (fun i => join3 (H i)) = e '' Set.range H := by
    rw [← Set.range_comp]; rfl
  rw [hr, ← Submodule.map_span]
  exact (Submodule.equivMapOfInjective e hinj _).finrank_eq

theorem tr_incons {a b c m : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = true)
    (x : V a) (y : V b) (z : V c) :
    ¬ ∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i := by
  intro hh
  exact la_incons _ rhs h (join3 (x, y, z)) ((ft_eqn H rhs x y z).2 hh)

theorem ft_lr {m N d : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (e : Fin d → Fin N) (j : Fin d) (s : Fin K) :
    mat (LrBits K R e) j s.castSucc = if rowSlot K R s (cl m (e j)) then 1 else 0 := by
  simp [mat, LrBits]

theorem tr_rows {a b c m : ℕ} (K : ℕ) (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = false)
    (hr : rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ K)
    (x : V a) (y : V b) (z : V c) :
    (∀ s : Fin K,
      (∑ j, mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c))) j s.castSucc * x j) +
      (∑ j, mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c))) j s.castSucc * y j) +
      (∑ j, mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b))) j s.castSucc * z j)
        = (if rowSlot K (gj _ (sysBits (fun i => join3 (H i)) rhs)) s (rc m (a + b + c)) then 1 else 0)) ↔
      ∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i := by
  rw [← ft_eqn H rhs x y z, ← la_rows K _ rhs h hr (join3 (x, y, z))]
  apply forall_congr'
  intro s
  rw [ft_sum3]
  simp only [ft_join_nx, ft_join_ny, ft_join_nz, ft_lr]

theorem tr_ker_sol {a b c m : ℕ} (K : ℕ) (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = false)
    (lam : V (K + 1)) (hl : lam (Fin.last K) = 1) :
    ∀ i, (H i).1 ⬝ᵥ ((mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c)))).mulVec lam) +
      (H i).2.1 ⬝ᵥ ((mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c)))).mulVec lam) +
      (H i).2.2 ⬝ᵥ ((mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b)))).mulVec lam)
        = rhs i := by
  have := la_ker_sol K (fun i => join3 (H i)) rhs h (fun s => lam s.castSucc)
  rw [ft_kerPt K _ lam hl] at this
  exact (ft_eqn H rhs _ _ _).1 this

theorem tr_ker_uniq {a b c m : ℕ} (K : ℕ) (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = false)
    (hk : a + b + c - rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ K)
    (x : V a) (y : V b) (z : V c)
    (hsol : ∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i) :
    ∃! lam : V (K + 1), lam (Fin.last K) = 1 ∧
      (∀ s : Fin K, deadSlot K (gj _ (sysBits (fun i => join3 (H i)) rhs)) s = true →
        lam s.castSucc = 0) ∧
      (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c)))).mulVec lam = x ∧
      (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c)))).mulVec lam = y ∧
      (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b)))).mulVec lam = z := by
  obtain ⟨lam', ⟨hm, hp⟩, hu⟩ := la_ker_uniq K (fun i => join3 (H i)) rhs h hk (join3 (x, y, z))
    ((ft_eqn H rhs x y z).2 hsol)
  refine ⟨Fin.snoc lam' 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp
  · intro s hs
    simpa using hm s hs
  · have hl : (Fin.snoc lam' (1 : ZMod 2) : V (K + 1)) (Fin.last K) = 1 := by simp
    have hc : (fun s : Fin K => (Fin.snoc lam' (1 : ZMod 2) : V (K + 1)) s.castSucc) = lam' := by
      funext s; simp
    have hj := ft_kerPt (a := a) (b := b) (c := c) K
      (gj _ (sysBits (fun i => join3 (H i)) rhs)) (Fin.snoc lam' 1) hl
    rw [hc, hp] at hj
    have := ft_join_inj _ _ hj
    have h1 := congrArg Prod.fst this
    have h2 := congrArg (fun q => q.2.1) this
    have h3 := congrArg (fun q => q.2.2) this
    exact ⟨h1.symm, h2.symm, h3.symm⟩
  · rintro lam2 ⟨hl, hm2, hx, hy, hz⟩
    have hj := ft_kerPt (a := a) (b := b) (c := c) K
      (gj _ (sysBits (fun i => join3 (H i)) rhs)) lam2 hl
    rw [hx, hy, hz] at hj
    have he := hu (fun s => lam2 s.castSucc) ⟨hm2, hj⟩
    funext s
    refine Fin.lastCases ?_ (fun s => ?_) s
    · simp [hl]
    · simp [← he]

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

def laC (N K : ℕ) : ℕ := 2 ^ 7 * (N + 2) ^ 2 * (K + 2)

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

abbrev fz2_B (m N K : ℕ) : Type :=
  (Fin (m + N + 1) × Fin (m + N + 1)) ⊕ ((Fin (N + 1) × Fin (K + 1)) ⊕ (Fin (N + 1) × Fin (K + 1)))

def fz2_blk {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) :
    fz2_B m N K → Bool :=
  Sum.elim R (Sum.elim (fun p => decide (cnt (pv R) p.1.val = p.2.val))
    (fun p => decide (cnt (fun q => !pv R q) p.1.val = p.2.val)))

theorem fz2_cmp_blk (m N K : ℕ) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (fz2_B m N K) (13 * ((N + 1) * (K + 1)))
      (fz2_blk K) := by
  have hP := Cmp.comp (Cmp.wire (ι := Fin (m + N + 1) × Fin (m + N + 1))
    (fun p : Fin N => (cl m p, cl m p))) (cmp_counter N K)
  have hn : Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (Fin N) (Fintype.card (Fin N) * (0 + 1))
      (fun R q => !R (cl m q, cl m q)) :=
    Cmp.ofBits (fun q => Cb.not (Cb.var (cl m q, cl m q)))
  have hN := Cmp.comp hn (cmp_counter N K)
  have h := Cmp.pair (Cmp.wire (ι := Fin (m + N + 1) × Fin (m + N + 1)) id) (Cmp.pair hP hN)
  refine Cmp.mono (Cmp.congr h ?_) ?_
  · intro R k
    rcases k with k | k | k <;> rfl
  · rw [Fintype.card_fin]
    have h1 : N ≤ (N + 1) * (K + 1) := by nlinarith
    have e : (N + 1) * ((K + 1) * 6) = 6 * ((N + 1) * (K + 1)) := by ring
    omega

theorem fz2_laC (N K : ℕ) : 13 * ((N + 1) * (K + 1)) + (K + 2) ≤ laC N K := by
  unfold laC
  have h1 : (N + 1) * (K + 1) ≤ (N + 2) ^ 2 * (K + 2) :=
    Nat.mul_le_mul (by nlinarith) (by omega)
  have h2 : K + 2 ≤ (N + 2) ^ 2 * (K + 2) := Nat.le_mul_of_pos_left _ (by positivity)
  have e : 2 ^ 7 * (N + 2) ^ 2 * (K + 2) = 128 * ((N + 2) ^ 2 * (K + 2)) := by ring
  omega

theorem fz2_cntP {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) :
    cntP R p = cnt (pv R) p.val := by
  unfold cntP cnt
  congr 1

theorem fz2_cntN {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) :
    cntN R p = cnt (fun q => !pv R q) p.val := by
  unfold cntN cnt
  congr 1

theorem fz2_rk {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) :
    rkOf R = cnt (pv R) N := by
  unfold rkOf cnt
  congr 1
  ext q
  simp

theorem fz2_row (m N K : ℕ) (s : Fin K) (j : Fin (m + N + 1)) :
    ∃ φ : (fz2_B m N K → Bool) → Bool, Cb (fz2_B m N K) (N * 3 + 1) φ ∧
      ∀ R, rowSlot K R s j = φ (fz2_blk K R) := by
  refine ⟨fun w => decide (∃ p : Fin N, (w (Sum.inl (cl m p, cl m p)) &&
    w (Sum.inr (Sum.inl (⟨p.val, by omega⟩, ⟨s.val, by omega⟩))) &&
    w (Sum.inl (cl m p, j))) = true), ?_, ?_⟩
  · have := Cb.bigOr (ι := fz2_B m N K) (I := Fin N)
      (φ := fun p w => (w (Sum.inl (cl m p, cl m p)) &&
        w (Sum.inr (Sum.inl (⟨p.val, by omega⟩, ⟨s.val, by omega⟩))) &&
        w (Sum.inl (cl m p, j))))
      (fun p => (Cb.and (Cb.and (Cb.var _) (Cb.var _)) (Cb.var _)))
    rw [Fintype.card_fin] at this
    exact (this.mono (by norm_num)).congr (fun w => decide_eq_decide.mpr Iff.rfl)
  · intro R
    unfold rowSlot
    refine decide_eq_decide.mpr (exists_congr fun p => ?_)
    rw [fz2_cntP]
    simp [fz2_blk, pv, and_assoc]

theorem fz2_xbit (m N K : ℕ) (j q : Fin N) :
    Cb (fz2_B m N K) 1 (fun w => xor (decide (j = q)) (w (Sum.inl (cl m j, cl m q)))) := by
  by_cases h : j = q
  · refine ((Cb.not (Cb.var (Sum.inl (cl m j, cl m q)))).mono (by norm_num)).congr ?_
    intro w; simp [h]
  · refine ((Cb.var (Sum.inl (cl m j, cl m q))).mono (by norm_num)).congr ?_
    intro w; simp [h]

theorem fz2_ker (m N K : ℕ) (s : Fin K) (j : Fin N) :
    ∃ φ : (fz2_B m N K → Bool) → Bool, Cb (fz2_B m N K) (N * 5 + 1) φ ∧
      ∀ R, kerSlot K R s j = φ (fz2_blk K R) := by
  refine ⟨fun w => decide (∃ q : Fin N, ((!w (Sum.inl (cl m q, cl m q))) &&
    w (Sum.inr (Sum.inr (⟨q.val, by omega⟩, ⟨s.val, by omega⟩))) &&
    xor (decide (j = q)) (w (Sum.inl (cl m j, cl m q)))) = true), ?_, ?_⟩
  · have := Cb.bigOr (ι := fz2_B m N K) (I := Fin N)
      (φ := fun q w => ((!w (Sum.inl (cl m q, cl m q))) &&
        w (Sum.inr (Sum.inr (⟨q.val, by omega⟩, ⟨s.val, by omega⟩))) &&
        xor (decide (j = q)) (w (Sum.inl (cl m j, cl m q)))))
      (fun q => (Cb.and (Cb.and (Cb.not (Cb.var _)) (Cb.var _)) (fz2_xbit m N K j q)))
    rw [Fintype.card_fin] at this
    exact (this.mono (by norm_num)).congr (fun w => decide_eq_decide.mpr Iff.rfl)
  · intro R
    unfold kerSlot
    refine decide_eq_decide.mpr (exists_congr fun q => ?_)
    rw [fz2_cntN]
    simp only [fz2_blk, pv, Sum.elim_inl, Sum.elim_inr, Bool.and_eq_true, Bool.not_eq_true',
      and_assoc]
    exact and_congr Iff.rfl (and_congr decide_eq_true_iff.symm Iff.rfl)

theorem fz2_dead (m N K : ℕ) (s : Fin K) :
    ∃ φ : (fz2_B m N K → Bool) → Bool, Cb (fz2_B m N K) (N * 3 + 2) φ ∧
      ∀ R, deadSlot K R s = φ (fz2_blk K R) := by
  refine ⟨fun w => !decide (∃ q : Fin N, ((!w (Sum.inl (cl m q, cl m q))) &&
    w (Sum.inr (Sum.inr (⟨q.val, by omega⟩, ⟨s.val, by omega⟩)))) = true), ?_, ?_⟩
  · have := Cb.not (Cb.bigOr (ι := fz2_B m N K) (I := Fin N)
      (φ := fun q w => ((!w (Sum.inl (cl m q, cl m q))) &&
        w (Sum.inr (Sum.inr (⟨q.val, by omega⟩, ⟨s.val, by omega⟩)))))
      (fun q => (Cb.and (Cb.not (Cb.var _)) (Cb.var _))))
    rw [Fintype.card_fin] at this
    exact (this.mono (by norm_num)).congr
      (fun w => congrArg (fun b => !b) (decide_eq_decide.mpr Iff.rfl))
  · intro R
    unfold deadSlot
    rw [decide_not]
    refine congrArg (fun b => !b) (decide_eq_decide.mpr (exists_congr fun q => ?_))
    rw [fz2_cntN]
    simp only [fz2_blk, pv, Sum.elim_inl, Sum.elim_inr, Bool.and_eq_true, Bool.not_eq_true',
      ]
    exact and_congr Iff.rfl decide_eq_true_iff.symm

theorem fz2_piece {m N K : ℕ} {κ : Type} [Fintype κ]
    (Q : (Fin (m + N + 1) × Fin (m + N + 1) → Bool) → κ → Bool) (s : ℕ)
    (h : ∀ k, ∃ φ : (fz2_B m N K → Bool) → Bool, Cb (fz2_B m N K) s φ ∧
      ∀ R, Q R k = φ (fz2_blk K R)) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) κ (13 * ((N + 1) * (K + 1)) + Fintype.card κ * s)
      Q := by
  choose φ hφ hQ using h
  have := Cmp.comp (fz2_cmp_blk m N K) (Cmp.ofBits (F := fun w k => φ k w) hφ)
  exact Cmp.congr this (fun R k => (hQ k R).symm)

theorem cmp_LrBits (m N d K : ℕ) (e : Fin d → Fin N) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (Fin d × Fin (K + 1))
      (laC N K + d * (K + 1) * (8 * N + 8)) (fun R => LrBits K R e) := by
  have h := fz2_piece (m := m) (N := N) (K := K) (fun R => LrBits K R e) (8 * N + 8) (by
    intro k
    by_cases hk : k.2.val < K
    · obtain ⟨φ, h1, h2⟩ := fz2_row m N K ⟨k.2.val, hk⟩ (cl m (e k.1))
      refine ⟨φ, h1.mono (by omega), fun R => ?_⟩
      rw [← h2 R]
      simp [LrBits, hk]
    · refine ⟨fun _ => false, (Cb.const false).mono (by omega), fun R => ?_⟩
      simp [LrBits, hk])
  refine Cmp.mono h ?_
  have := fz2_laC N K
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

theorem cmp_LnBits (m N d K : ℕ) (e : Fin d → Fin N) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (Fin d × Fin (K + 1))
      (laC N K + d * (K + 1) * (8 * N + 8)) (fun R => LnBits K R e) := by
  have h := fz2_piece (m := m) (N := N) (K := K) (fun R => LnBits K R e) (8 * N + 8) (by
    intro k
    by_cases hk : k.2.val < K
    · obtain ⟨φ, h1, h2⟩ := fz2_ker m N K ⟨k.2.val, hk⟩ (e k.1)
      refine ⟨φ, h1.mono (by omega), fun R => ?_⟩
      rw [← h2 R]
      simp [LnBits, hk]
    · refine ⟨fun w => w (Sum.inl (cl m (e k.1), rc m N)),
        (Cb.var _).mono (by omega), fun R => ?_⟩
      simp [LnBits, hk, fz2_blk])
  refine Cmp.mono h ?_
  have := fz2_laC N K
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

theorem fz2_zsum (K : ℕ) (x : Fin K → ZMod 2) (b : Fin K → Bool) :
    (∑ s, x s * (if b s = true then (1 : ZMod 2) else 0)) ≠ 0 ↔
      (Finset.univ.filter (fun s => (decide (x s ≠ 0) && b s) = true)).card % 2 = 1 := by
  have key : ∀ s, x s * (if b s = true then (1 : ZMod 2) else 0) =
      if (decide (x s ≠ 0) && b s) = true then 1 else 0 := by
    intro s
    have hall : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    have hx : x s = 0 ∨ x s = 1 := hall (x s)
    rcases hx with hx | hx <;> cases b s <;> simp [hx]
  simp_rw [key]
  rw [Finset.sum_boole, Ne, ZMod.natCast_eq_zero_iff]
  omega

theorem fz2_cardV (K : ℕ) : Fintype.card (V (K + 1)) = 2 ^ (K + 1) := by
  simp [V, ZMod.card]

theorem fz2_wcost (N K : ℕ) :
    13 * ((N + 1) * (K + 1)) + 2 ^ (K + 1) * ((K + 1) * (8 * N + 8)) ≤
      laC N K + 2 ^ (K + 1) * ((K + 1) * (8 * N + 8)) := by
  have := fz2_laC N K
  omega

theorem cmp_wnR (m N K : ℕ) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (V (K + 1))
      (laC N K + 2 ^ (K + 1) * ((K + 1) * (8 * N + 8)))
      (fun R lam => decide ((∑ s : Fin K, lam s.castSucc *
        (if rowSlot K R s (rc m N) = true then (1 : ZMod 2) else 0)) ≠ 0)) := by
  choose ρφ hρ hρQ using fun s : Fin K => fz2_row m N K s (rc m N)
  have h := fz2_piece (m := m) (N := N) (K := K) (κ := V (K + 1))
    (fun R lam => decide ((∑ s : Fin K, lam s.castSucc *
        (if rowSlot K R s (rc m N) = true then (1 : ZMod 2) else 0)) ≠ 0))
    ((K + 1) * (8 * N + 8)) (by
    intro lam
    refine ⟨fun w => decide ((Finset.univ.filter (fun s : Fin K =>
      (decide (lam s.castSucc ≠ 0) && ρφ s w) = true)).card % 2 = 1), ?_, ?_⟩
    · have := Cb.bigXor (ι := fz2_B m N K) (I := Fin K) (s := N * 3 + 1)
        (φ := fun s w => (decide (lam s.castSucc ≠ 0) && ρφ s w)) (fun s => by
          by_cases hl : lam s.castSucc ≠ 0
          · refine (hρ s).congr ?_
            intro w; simp [hl]
          · refine ((Cb.const false).mono (by omega)).congr ?_
            intro w; simp [hl])
      rw [Fintype.card_fin] at this
      refine this.mono ?_
      nlinarith
    · intro R
      refine decide_eq_decide.mpr ?_
      rw [fz2_zsum]
      simp only [hρQ])
  rw [fz2_cardV] at h
  exact Cmp.mono h (fz2_wcost N K)

theorem cmp_wzN (m N K : ℕ) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (V (K + 1))
      (laC N K + 2 ^ (K + 1) * ((K + 1) * (8 * N + 8)))
      (fun R lam => decide (lam (Fin.last K) = 0 ∨
        ∃ s : Fin K, deadSlot K R s = true ∧ lam s.castSucc ≠ 0)) := by
  choose δ hδ hδQ using fun s : Fin K => fz2_dead m N K s
  have h := fz2_piece (m := m) (N := N) (K := K) (κ := V (K + 1))
    (fun R lam => decide (lam (Fin.last K) = 0 ∨
        ∃ s : Fin K, deadSlot K R s = true ∧ lam s.castSucc ≠ 0))
    ((K + 1) * (8 * N + 8)) (by
    intro lam
    by_cases h0 : lam (Fin.last K) = 0
    · refine ⟨fun _ => true, (Cb.const true).mono (by nlinarith), fun R => ?_⟩
      simp [h0]
    · refine ⟨fun w => decide (∃ s : Fin K,
        (decide (lam s.castSucc ≠ 0) && δ s w) = true), ?_, ?_⟩
      · have := Cb.bigOr (ι := fz2_B m N K) (I := Fin K) (s := N * 3 + 2)
          (φ := fun s w => (decide (lam s.castSucc ≠ 0) && δ s w)) (fun s => by
            by_cases hl : lam s.castSucc ≠ 0
            · refine (hδ s).congr ?_
              intro w; simp [hl]
            · refine ((Cb.const false).mono (by omega)).congr ?_
              intro w; simp [hl])
        rw [Fintype.card_fin] at this
        refine (this.mono ?_).congr (fun w => decide_eq_decide.mpr Iff.rfl)
        nlinarith
      · intro R
        refine decide_eq_decide.mpr ?_
        simp only [h0, false_or, hδQ, Bool.and_eq_true, decide_eq_true_eq]
        exact exists_congr fun s => and_comm)
  rw [fz2_cardV] at h
  exact Cmp.mono h (fz2_wcost N K)

theorem fz2_last (m N K : ℕ) (g : (Fin (N + 1) × Fin (K + 1)) → fz2_B m N K) :
    Cb (fz2_B m N K) ((K + 1) * (0 + 1) + 1)
      (fun w => decide (∃ s : Fin (K + 1), w (g (Fin.last N, s)) = true)) := by
  have := Cb.bigOr (ι := fz2_B m N K) (I := Fin (K + 1)) (s := 0)
    (φ := fun s w => w (g (Fin.last N, s))) (fun s => Cb.var _)
  rw [Fintype.card_fin] at this
  exact this.congr (fun w => decide_eq_decide.mpr Iff.rfl)

theorem fz2_exle (c K : ℕ) : (∃ s : Fin (K + 1), c = s.val) ↔ c ≤ K := by
  constructor
  · rintro ⟨s, hs⟩
    have := s.isLt
    omega
  · intro h
    exact ⟨⟨c, by omega⟩, rfl⟩

theorem cb_okr (m N K : ℕ) :
    Cb (Fin (m + N + 1) × Fin (m + N + 1)) (laC N K) (fun R => decide (rkOf R ≤ K)) := by
  have h := Cb.comp (fz2_cmp_blk m N K) (fz2_last m N K (fun p => Sum.inr (Sum.inl p)))
  refine (h.mono ?_).congr ?_
  · have := fz2_laC N K
    omega
  · intro R
    refine decide_eq_decide.mpr ?_
    rw [fz2_rk, ← fz2_exle]
    simp [fz2_blk]

theorem cb_okn (m N K : ℕ) :
    Cb (Fin (m + N + 1) × Fin (m + N + 1)) (laC N K) (fun R => decide (N - rkOf R ≤ K)) := by
  have h := Cb.comp (fz2_cmp_blk m N K) (fz2_last m N K (fun p => Sum.inr (Sum.inr p)))
  refine (h.mono ?_).congr ?_
  · have := fz2_laC N K
    omega
  · intro R
    refine decide_eq_decide.mpr ?_
    rw [fz2_rk, ← cnt_compl, ← fz2_exle]
    simp [fz2_blk]

def coreSem {a b c K W : ℕ} (F : V a × Fin W → Bool) (G : V b × Fin W → Bool)
    (Lx : Fin a × Fin (K + 1) → Bool) (Ly : Fin b × Fin (K + 1) → Bool)
    (Lz : Fin c × Fin (K + 1) → Bool) (wz wn : V (K + 1) → Bool) : V c → BitVec W :=
  fun z => ∑ lam : V (K + 1), if (mat Lz).mulVec lam = z then
    (if wz lam = true then 0
     else if wn lam = true then
       -(tab F ((mat Lx).mulVec lam) * tab G ((mat Ly).mulVec lam))
     else tab F ((mat Lx).mulVec lam) * tab G ((mat Ly).mulVec lam))
    else 0

def coreCost (a b c K W : ℕ) : ℕ :=
  tcost a (K + 1) W + tcost b (K + 1) W + tcost c (K + 1) W + 2 ^ (K + 1) * (60 * (W + 1) ^ 2)

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

theorem fz3_prod {ι : Type} {k W SA SB S6 S7 : ℕ} {A B : (ι → Bool) → V k × Fin W → Bool}
    {WZ WN : (ι → Bool) → V k → Bool}
    (hA : Cmp ι (V k × Fin W) SA A) (hB : Cmp ι (V k × Fin W) SB B)
    (hwz : Cmp ι (V k) S6 WZ) (hwn : Cmp ι (V k) S7 WN) :
    Cmp ι (V k × Fin W) (SA + SB + S6 + S7 + 2 ^ k * (60 * (W + 1) ^ 2))
      (fun v => untab (fun lam : V k => if WZ v lam = true then 0
        else if WN v lam = true then -(tab (A v) lam * tab (B v) lam)
        else tab (A v) lam * tab (B v) lam)) := by
  have hb := Cmp.pair (Cmp.pair hA hB) (Cmp.pair hwz hwn)
  have hw : ∀ lam : V k, Cw (((V k × Fin W) ⊕ (V k × Fin W)) ⊕ (V k ⊕ V k)) W (60 * (W + 1) ^ 2)
      (fun v => if v (Sum.inr (Sum.inl lam)) = true then 0
        else if v (Sum.inr (Sum.inr lam)) = true then
          -(tab (fun p => v (Sum.inl (Sum.inl p))) lam * tab (fun p => v (Sum.inl (Sum.inr p))) lam)
        else tab (fun p => v (Sum.inl (Sum.inl p))) lam *
          tab (fun p => v (Sum.inl (Sum.inr p))) lam) := by
    intro lam
    have hAv : Cw (((V k × Fin W) ⊕ (V k × Fin W)) ⊕ (V k ⊕ V k)) W 0
        (fun v => tab (fun p => v (Sum.inl (Sum.inl p))) lam) :=
      Cw.var (fun i => Sum.inl (Sum.inl (lam, i)))
    have hBv : Cw (((V k × Fin W) ⊕ (V k × Fin W)) ⊕ (V k ⊕ V k)) W 0
        (fun v => tab (fun p => v (Sum.inl (Sum.inr p))) lam) :=
      Cw.var (fun i => Sum.inl (Sum.inr (lam, i)))
    have h1 := Cw.mux (Cb.var (Sum.inr (Sum.inr lam))) (Cw.neg hAv) hAv
    have h2 := Cw.mul h1 hBv
    have h3 := Cw.mux (Cb.var (Sum.inr (Sum.inl lam))) (Cw.const 0) h2
    refine (h3.mono ?_).congr ?_
    · nlinarith [Nat.zero_le W]
    · intro v
      by_cases h1 : v (Sum.inr (Sum.inl lam)) = true
      · simp [h1]
      · by_cases h2 : v (Sum.inr (Sum.inr lam)) = true
        · simp [h1, h2]
        · simp [h1, h2]
  have h := Cmp.comp hb (Cmp.ofWords hw)
  rw [fz3_card] at h
  exact Cmp.congr (h.mono (by omega)) (fun _ _ => rfl)

theorem Cmp.core {ι : Type} {a b c K W S1 S2 S3 S4 S5 S6 S7 : ℕ}
    {FF : (ι → Bool) → V a × Fin W → Bool} {GG : (ι → Bool) → V b × Fin W → Bool}
    {LX : (ι → Bool) → Fin a × Fin (K + 1) → Bool} {LY : (ι → Bool) → Fin b × Fin (K + 1) → Bool}
    {LZ : (ι → Bool) → Fin c × Fin (K + 1) → Bool} {WZ WN : (ι → Bool) → V (K + 1) → Bool}
    (hF : Cmp ι (V a × Fin W) S1 FF) (hG : Cmp ι (V b × Fin W) S2 GG)
    (hX : Cmp ι (Fin a × Fin (K + 1)) S3 LX) (hY : Cmp ι (Fin b × Fin (K + 1)) S4 LY)
    (hZ : Cmp ι (Fin c × Fin (K + 1)) S5 LZ) (hwz : Cmp ι (V (K + 1)) S6 WZ)
    (hwn : Cmp ι (V (K + 1)) S7 WN) :
    Cmp ι (V c × Fin W) (S1 + S2 + S3 + S4 + S5 + S6 + S7 + coreCost a b c K W)
      (fun v => untab (coreSem (FF v) (GG v) (LX v) (LY v) (LZ v) (WZ v) (WN v))) := by
  have h := fz3_push hZ (fz3_prod (fz3_pull hX hF) (fz3_pull hY hG) hwz hwn)
  refine (h.mono ?_).congr ?_
  · unfold coreCost
    generalize 2 ^ (K + 1) * (60 * (W + 1) ^ 2) = q
    omega
  · intro v k
    simp only [tab_untab]
    rfl

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

def whtF {d W : ℕ} (T : V d × Fin W → Bool) : V d × Fin W → Bool :=
  untab (fun xi : V d => ∑ x : V d, sgn (xi ⬝ᵥ x) * tab T x)

def Kof (a b c u : ℕ) : ℕ := min (a + b + c) u

def Wof (a b c t u : ℕ) : ℕ := a + b + 2 * t + 1 + Kof a b c u

def wzRf (K : ℕ) : V (K + 1) → Bool := fun lam => decide (lam (Fin.last K) ≠ 0)

def wnRf {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) : V (K + 1) → Bool :=
  fun lam => decide ((∑ s : Fin K, lam s.castSucc *
    (if rowSlot K R s (rc m N) = true then (1 : ZMod 2) else 0)) ≠ 0)

def wzNf {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) : V (K + 1) → Bool :=
  fun lam => decide (lam (Fin.last K) = 0 ∨
    ∃ s : Fin K, deadSlot K R s = true ∧ lam s.castSucc ≠ 0)

def ansR (a b c m t u : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (v : In0 a b c m t → Bool) : V c × Fin (Wof a b c t u) → Bool :=
  whtF (untab (coreSem (whtF (fTab a b c m t (Wof a b c t u) ea v))
    (whtF (gTab a b c m t (Wof a b c t u) eb v))
    (LrBits (Kof a b c u) (Rb a b c m t v) (nx (b := b) (c := c)))
    (LrBits (Kof a b c u) (Rb a b c m t v) (ny (a := a) (c := c)))
    (LrBits (Kof a b c u) (Rb a b c m t v) (nz (a := a) (b := b)))
    (wzRf (Kof a b c u)) (wnRf (Kof a b c u) (Rb a b c m t v))))

def ansN (a b c m t u : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (v : In0 a b c m t → Bool) : V c × Fin (Wof a b c t u) → Bool :=
  untab (coreSem (fTab a b c m t (Wof a b c t u) ea v)
    (gTab a b c m t (Wof a b c t u) eb v)
    (LnBits (Kof a b c u) (Rb a b c m t v) (nx (b := b) (c := c)))
    (LnBits (Kof a b c u) (Rb a b c m t v) (ny (a := a) (c := c)))
    (LnBits (Kof a b c u) (Rb a b c m t v) (nz (a := a) (b := b)))
    (wzNf (Kof a b c u) (Rb a b c m t v)) (fun _ => false))

def okR (a b c m t u : ℕ) (v : In0 a b c m t → Bool) : Bool :=
  decide (rkOf (Rb a b c m t v) ≤ Kof a b c u)

def okN (a b c m t u : ℕ) (v : In0 a b c m t → Bool) : Bool :=
  decide (a + b + c - rkOf (Rb a b c m t v) ≤ Kof a b c u)

def consB (a b c m t : ℕ) (v : In0 a b c m t → Bool) : Bool :=
  !(Rb a b c m t v) (rc m (a + b + c), rc m (a + b + c))

def topF (a b c m t u : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (ec : Fin (2 ^ c) ≃ V c) (v : In0 a b c m t → Bool) :
    Unit ⊕ (Fin (2 ^ c) × Fin (a + b + 2 * t + 1)) → Bool :=
  Sum.elim (fun _ => okR a b c m t u v || okN a b c m t u v)
    (fun p => (okR a b c m t u v || okN a b c m t u v) && consB a b c m t v &&
      (if okR a b c m t u v = true then
        ansR a b c m t u ea eb v (ec p.1, ⟨Kof a b c u + p.2.val, by unfold Wof; omega⟩)
       else ansN a b c m t u ea eb v (ec p.1, ⟨p.2.val, by unfold Wof; omega⟩)))

def inpOf {a b c m t : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) : In0 a b c m t → Bool :=
  Sum.elim (fun p => if h : p.2.val < a + b + c then decide (join3 (H p.1) ⟨p.2.val, h⟩ ≠ 0)
      else decide (rhs p.1 ≠ 0))
    (Sum.elim (fun p => (f p.1).val.testBit p.2.val) (fun p => (g p.1).val.testBit p.2.val))

def topSum (a b c m t u : ℕ) : ℕ :=
  gjCost (m + (a + b + c) + 1) + (m + (a + b + c) + 1) ^ 2 +
  (2 ^ a + 2 ^ b) * (Wof a b c t u + 1) +
  whtCost a (Wof a b c t u) + whtCost b (Wof a b c t u) + whtCost c (Wof a b c t u) +
  laC (a + b + c) (Kof a b c u) +
  (a + b + c) * (Kof a b c u + 1) * (8 * (a + b + c) + 8) +
  2 ^ (Kof a b c u + 1) * ((Kof a b c u + 1) * (8 * (a + b + c) + 8)) +
  coreCost a b c (Kof a b c u) (Wof a b c t u) + 2 ^ (Kof a b c u + 1) +
  2 ^ c * (a + b + 2 * t + 1) * 16 + 16

def topCost (a b c m t u : ℕ) : ℕ := 16 * topSum a b c m t u

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

theorem fz4_const (ι : Type) (K : ℕ) (w : V (K + 1) → Bool) :
    Cmp ι (V (K + 1)) (2 ^ (K + 1)) (fun _ => w) :=
  (Cmp.ofBits (s := 1) (F := fun _ => w) (fun k => Cb.const (w k))).mono
    (by simp)

def fz4_fin (a b c t u : ℕ) (ec : Fin (2 ^ c) ≃ V c)
    (w : ((Unit ⊕ Unit) ⊕ Unit) ⊕
      ((V c × Fin (Wof a b c t u)) ⊕ (V c × Fin (Wof a b c t u))) → Bool) :
    Unit ⊕ (Fin (2 ^ c) × Fin (a + b + 2 * t + 1)) → Bool :=
  Sum.elim (fun _ => w (Sum.inl (Sum.inl (Sum.inl ()))) || w (Sum.inl (Sum.inl (Sum.inr ()))))
    (fun p => (w (Sum.inl (Sum.inl (Sum.inl ()))) || w (Sum.inl (Sum.inl (Sum.inr ())))) &&
      w (Sum.inl (Sum.inr ())) &&
      (if w (Sum.inl (Sum.inl (Sum.inl ()))) = true then
        w (Sum.inr (Sum.inl (ec p.1, ⟨Kof a b c u + p.2.val, by unfold Wof; omega⟩)))
       else w (Sum.inr (Sum.inr (ec p.1, ⟨p.2.val, by unfold Wof; omega⟩)))))

theorem fz4_fin_cmp (a b c t u : ℕ) (ec : Fin (2 ^ c) ≃ V c) :
    Cmp (((Unit ⊕ Unit) ⊕ Unit) ⊕
      ((V c × Fin (Wof a b c t u)) ⊕ (V c × Fin (Wof a b c t u))))
      (Unit ⊕ (Fin (2 ^ c) × Fin (a + b + 2 * t + 1)))
      ((1 + 2 ^ c * (a + b + 2 * t + 1)) * 7) (fz4_fin a b c t u ec) := by
  refine (Cmp.ofBits (s := 7) (F := fz4_fin a b c t u ec) (fun k => ?_)).mono (by simp)
  rcases k with k | p
  · exact (Cb.or (Cb.var (Sum.inl (Sum.inl (Sum.inl ()))))
      (Cb.var (Sum.inl (Sum.inl (Sum.inr ()))))).mono (by norm_num)
  · exact (Cb.and (Cb.and (Cb.or (Cb.var (Sum.inl (Sum.inl (Sum.inl ()))))
      (Cb.var (Sum.inl (Sum.inl (Sum.inr ()))))) (Cb.var (Sum.inl (Sum.inr ()))))
      (Cb.mux (Cb.var (Sum.inl (Sum.inl (Sum.inl ()))))
        (Cb.var (Sum.inr (Sum.inl (ec p.1,
          (⟨Kof a b c u + p.2.val, by unfold Wof; omega⟩ : Fin (Wof a b c t u))))))
        (Cb.var (Sum.inr (Sum.inr (ec p.1,
          (⟨p.2.val, by unfold Wof; omega⟩ : Fin (Wof a b c t u)))))))).mono
      (by norm_num)

theorem cmp_top (a b c m t u : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (ec : Fin (2 ^ c) ≃ V c) :
    Cmp (In0 a b c m t) (Unit ⊕ (Fin (2 ^ c) × Fin (a + b + 2 * t + 1))) (topCost a b c m t u)
      (topF a b c m t u ea eb ec) := by
  have hR : Cmp (In0 a b c m t) (Fin (m + (a + b + c) + 1) × Fin (m + (a + b + c) + 1))
      ((m + (a + b + c) + 1) ^ 2 + gjCost (m + (a + b + c) + 1)) (Rb a b c m t) := by
    have h0 := Cmp.comp (fz4_Mb a b c m t) (cmp_gj (m + (a + b + c) + 1))
    exact h0
  have hf := fz4_fTab a b c m t (Wof a b c t u) ea
  have hg := fz4_gTab a b c m t (Wof a b c t u) eb
  have hwf : Cmp (In0 a b c m t) _ _ (fun v => whtF (fTab a b c m t (Wof a b c t u) ea v)) :=
    Cmp.comp hf (cmp_wht a (Wof a b c t u))
  have hwg : Cmp (In0 a b c m t) _ _ (fun v => whtF (gTab a b c m t (Wof a b c t u) eb v)) :=
    Cmp.comp hg (cmp_wht b (Wof a b c t u))
  have hrx := Cmp.comp hR (cmp_LrBits m (a + b + c) a (Kof a b c u) (nx (b := b) (c := c)))
  have hry := Cmp.comp hR (cmp_LrBits m (a + b + c) b (Kof a b c u) (ny (a := a) (c := c)))
  have hrz := Cmp.comp hR (cmp_LrBits m (a + b + c) c (Kof a b c u) (nz (a := a) (b := b)))
  have hnx := Cmp.comp hR (cmp_LnBits m (a + b + c) a (Kof a b c u) (nx (b := b) (c := c)))
  have hny := Cmp.comp hR (cmp_LnBits m (a + b + c) b (Kof a b c u) (ny (a := a) (c := c)))
  have hnz := Cmp.comp hR (cmp_LnBits m (a + b + c) c (Kof a b c u) (nz (a := a) (b := b)))
  have hwnR : Cmp (In0 a b c m t) _ _ (fun v => wnRf (Kof a b c u) (Rb a b c m t v)) :=
    Cmp.comp hR (cmp_wnR m (a + b + c) (Kof a b c u))
  have hwzN : Cmp (In0 a b c m t) _ _ (fun v => wzNf (Kof a b c u) (Rb a b c m t v)) :=
    Cmp.comp hR (cmp_wzN m (a + b + c) (Kof a b c u))
  have hwzR := fz4_const (In0 a b c m t) (Kof a b c u) (wzRf (Kof a b c u))
  have hwnN := fz4_const (In0 a b c m t) (Kof a b c u) (fun _ => false)
  have hcR := Cmp.core hwf hwg hrx hry hrz hwzR hwnR
  have hansR0 := Cmp.comp hcR (cmp_wht c (Wof a b c t u))
  have hansR : Cmp (In0 a b c m t) _ _ (ansR a b c m t u ea eb) := hansR0
  have hansN : Cmp (In0 a b c m t) _ _ (ansN a b c m t u ea eb) :=
    Cmp.core hf hg hnx hny hnz hwzN hwnN
  have hokR0 := Cb.comp hR (cb_okr m (a + b + c) (Kof a b c u))
  have hokR : Cb (In0 a b c m t) _ (okR a b c m t u) := hokR0
  have hokN0 := Cb.comp hR (cb_okn m (a + b + c) (Kof a b c u))
  have hokN : Cb (In0 a b c m t) _ (okN a b c m t u) := hokN0
  have hcons0 := Cb.comp hR (Cb.not (Cb.var (rc m (a + b + c), rc m (a + b + c))))
  have hcons : Cb (In0 a b c m t) _ (consB a b c m t) := hcons0
  have hb := Cmp.pair (Cmp.pair (Cmp.pair hokR hokN) hcons) (Cmp.pair hansR hansN)
  have htop := Cmp.comp hb (fz4_fin_cmp a b c t u ec)
  refine Cmp.mono (Cmp.congr htop ?_) ?_
  · intro v k
    rcases k with k | p
    · rfl
    · rfl
  · unfold topCost topSum coreCost
    have e1 : a * (Kof a b c u + 1) * (8 * (a + b + c) + 8) ≤
        (a + b + c) * (Kof a b c u + 1) * (8 * (a + b + c) + 8) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have e2 : b * (Kof a b c u + 1) * (8 * (a + b + c) + 8) ≤
        (a + b + c) * (Kof a b c u + 1) * (8 * (a + b + c) + 8) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have e3 : c * (Kof a b c u + 1) * (8 * (a + b + c) + 8) ≤
        (a + b + c) * (Kof a b c u + 1) * (8 * (a + b + c) + 8) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have e4 : (2 ^ a + 2 ^ b) * (Wof a b c t u + 1) =
        2 ^ a * Wof a b c t u + 2 ^ b * Wof a b c t u + 2 ^ a + 2 ^ b := by ring
    have p1 := Nat.zero_le (2 ^ Kof a b c u)
    have p2 := Nat.zero_le (2 ^ a)
    have p3 := Nat.zero_le (2 ^ b)
    omega

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

theorem fz5_R {a b c m t : ℕ} (K W : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (z : V c)
    (hc : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = false)
    (hr : rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ K) :
    (∑ ζ : V c, sgn (z ⬝ᵥ ζ) *
      coreSem (whtF (fTab a b c m t W ea (inpOf H rhs f g)))
        (whtF (gTab a b c m t W eb (inpOf H rhs f g)))
        (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c)))
        (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c)))
        (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b)))
        (wzRf K) (wnRf K (gj _ (sysBits (fun i => join3 (H i)) rhs))) ζ) =
    BitVec.ofNat W (2 ^ K * ∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ z = rhs i) then
        (f ix).val * (g iy).val else 0) := by
  have key := fourier_id K a b c W (fun x => BitVec.ofNat W (f (ea.symm x)).val)
    (fun y => BitVec.ofNat W (g (eb.symm y)).val)
    (mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c))))
    (mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c))))
    (mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b))))
    (fun s => if rowSlot K (gj _ (sysBits (fun i => join3 (H i)) rhs)) s (rc m (a + b + c)) = true
      then 1 else 0) z
  rw [← fz5_two, ← fz5_total]
  refine Eq.trans ?_ (key.trans ?_)
  · apply Finset.sum_congr rfl
    intro ζ _
    rw [dotProduct_comm z ζ]
    congr 1
    unfold coreSem
    apply Finset.sum_congr rfl
    intro lam _
    simp only [whtF, tab_untab, wzRf, wnRf, decide_eq_true_eq, fz5_tabf, fz5_tabg]
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact if_congr (tr_rows K H rhs hc hr x y z) rfl rfl

theorem fz5_N {a b c m t : ℕ} (K W : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (z : V c)
    (hc : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = false)
    (hk : a + b + c - rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ K) :
    coreSem (fTab a b c m t W ea (inpOf H rhs f g))
        (gTab a b c m t W eb (inpOf H rhs f g))
        (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c)))
        (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c)))
        (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b)))
        (wzNf K (gj _ (sysBits (fun i => join3 (H i)) rhs))) (fun _ => false) z =
    BitVec.ofNat W (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ z = rhs i) then
        (f ix).val * (g iy).val else 0) := by
  have key := kernel_id K a b c W (fun x => BitVec.ofNat W (f (ea.symm x)).val)
    (fun y => BitVec.ofNat W (g (eb.symm y)).val)
    (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c))))
    (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c))))
    (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b))))
    (deadSlot K (gj _ (sysBits (fun i => join3 (H i)) rhs)))
    (fun x y z => ∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i)
    (fun lam hl => tr_ker_sol K H rhs hc lam hl)
    (fun x y z hs => tr_ker_uniq K H rhs hc hk x y z hs) z
  rw [← fz5_total]
  refine Eq.trans ?_ key
  unfold coreSem
  apply Finset.sum_congr rfl
  intro lam _
  simp only [wzNf, decide_eq_true_eq, fz5_tabf, fz5_tabg, Bool.false_eq_true, if_false]

theorem top_sem (a b c m t u : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (ec : Fin (2 ^ c) ≃ V c)
    (hea : ∀ ix j, ea ix j = if ix.val.testBit j.val then 1 else 0)
    (heb : ∀ ix j, eb ix j = if ix.val.testBit j.val then 1 else 0)
    (hec : ∀ ix j, ec ix j = if ix.val.testBit j.val then 1 else 0)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) :
    (topF a b c m t u ea eb ec (inpOf H rhs f g) (Sum.inl ()) = true ↔
      min (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)))
        (a + b + c - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H))) ≤ u) ∧
    ∀ (iz : Fin (2 ^ c)) (j : Fin (a + b + 2 * t + 1)),
      topF a b c m t u ea eb ec (inpOf H rhs f g) (Sum.inr (iz, j)) =
        (if topF a b c m t u ea eb ec (inpOf H rhs f g) (Sum.inl ()) = true then
          (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
            if ∀ i, (H i).1 ⬝ᵥ (fun j : Fin a => if ix.val.testBit j.val then (1 : ZMod 2) else 0) +
                (H i).2.1 ⬝ᵥ (fun j : Fin b => if iy.val.testBit j.val then (1 : ZMod 2) else 0) +
                (H i).2.2 ⬝ᵥ (fun j : Fin c => if iz.val.testBit j.val then (1 : ZMod 2) else 0) =
                rhs i
            then (f ix).val * (g iy).val else 0)
         else 0).testBit j.val := by
  have hea' : ∀ ix, ea ix = (fun j : Fin a => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
    fun ix => funext (hea ix)
  have heb' : ∀ ix, eb ix = (fun j : Fin b => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
    fun ix => funext (heb ix)
  have hec' : ∀ ix, ec ix = (fun j : Fin c => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
    fun ix => funext (hec ix)
  have hRb : Rb a b c m t (inpOf H rhs f g) = gj _ (sysBits (fun i => join3 (H i)) rhs) := by
    unfold Rb; rw [fz5_Mb]
  have hrk := tr_rank H rhs
  have hle : rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ a + b + c := by
    unfold rkOf
    calc _ ≤ (Finset.univ : Finset (Fin (a + b + c))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = a + b + c := by simp
  have hok : (okR a b c m t u (inpOf H rhs f g) || okN a b c m t u (inpOf H rhs f g)) = true ↔
      min (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)))
        (a + b + c - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H))) ≤ u := by
    unfold okR okN Kof
    rw [hRb, hrk]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  refine ⟨hok, ?_⟩
  intro iz j
  have htot : (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
            if ∀ i, (H i).1 ⬝ᵥ (fun j : Fin a => if ix.val.testBit j.val then (1 : ZMod 2) else 0) +
                (H i).2.1 ⬝ᵥ (fun j : Fin b => if iy.val.testBit j.val then (1 : ZMod 2) else 0) +
                (H i).2.2 ⬝ᵥ (fun j : Fin c => if iz.val.testBit j.val then (1 : ZMod 2) else 0) =
                rhs i
            then (f ix).val * (g iy).val else 0) =
      ∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
        if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ ec iz = rhs i) then
          (f ix).val * (g iy).val else 0 := by
    simp only [hea', heb', hec']
  rw [htot]
  have hK : Kof a b c u + j.val < Wof a b c t u := by unfold Wof; omega
  have hj : j.val < Wof a b c t u := by unfold Wof; omega
  show ((okR a b c m t u (inpOf H rhs f g) || okN a b c m t u (inpOf H rhs f g)) &&
      consB a b c m t (inpOf H rhs f g) &&
      (if okR a b c m t u (inpOf H rhs f g) = true then
        ansR a b c m t u ea eb (inpOf H rhs f g) (ec iz, ⟨Kof a b c u + j.val, hK⟩)
       else ansN a b c m t u ea eb (inpOf H rhs f g) (ec iz, ⟨j.val, hj⟩))) =
    (if (okR a b c m t u (inpOf H rhs f g) || okN a b c m t u (inpOf H rhs f g)) = true then _
      else 0).testBit j.val
  by_cases hO : (okR a b c m t u (inpOf H rhs f g) || okN a b c m t u (inpOf H rhs f g)) = true
  swap
  · rw [if_neg hO]
    rw [Bool.not_eq_true] at hO
    rw [hO]
    simp
  rw [if_pos hO, hO, Bool.true_and]
  by_cases hC : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = true
  · have h0 : (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
        if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ ec iz = rhs i) then
          (f ix).val * (g iy).val else 0) = 0 := by
      apply Finset.sum_eq_zero; intro ix _
      apply Finset.sum_eq_zero; intro iy _
      exact if_neg (tr_incons H rhs hC _ _ _)
    rw [h0]
    have : consB a b c m t (inpOf H rhs f g) = false := by
      unfold consB; rw [hRb, hC]; rfl
    rw [this]; simp
  rw [Bool.not_eq_true] at hC
  have hcons : consB a b c m t (inpOf H rhs f g) = true := by
    unfold consB; rw [hRb, hC]; rfl
  rw [hcons, Bool.true_and]
  by_cases hR : okR a b c m t u (inpOf H rhs f g) = true
  · rw [if_pos hR]
    have hr : rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ Kof a b c u := by
      have := hR; unfold okR at this; rw [hRb] at this; exact of_decide_eq_true this
    have e1 : ansR a b c m t u ea eb (inpOf H rhs f g) (ec iz, ⟨Kof a b c u + j.val, hK⟩) =
        (∑ ζ : V c, sgn (ec iz ⬝ᵥ ζ) *
          tab (untab (coreSem (whtF (fTab a b c m t (Wof a b c t u) ea (inpOf H rhs f g)))
            (whtF (gTab a b c m t (Wof a b c t u) eb (inpOf H rhs f g)))
            (LrBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (nx (b := b) (c := c)))
            (LrBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (ny (a := a) (c := c)))
            (LrBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (nz (a := a) (b := b)))
            (wzRf (Kof a b c u)) (wnRf (Kof a b c u) (Rb a b c m t (inpOf H rhs f g))))) ζ).getLsbD
          (Kof a b c u + j.val) := by
      simp only [ansR, whtF, untab]
    rw [e1, tab_untab, hRb, fz5_R (Kof a b c u) (Wof a b c t u) ea eb H rhs f g (ec iz) hC hr,
      BitVec.getLsbD_ofNat, Nat.testBit_two_pow_mul]
    simp [hK]
  · rw [if_neg hR]
    have hk : a + b + c - rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ Kof a b c u := by
      rw [Bool.not_eq_true] at hR
      rw [hR, Bool.false_or] at hO
      unfold okN at hO; rw [hRb] at hO; exact of_decide_eq_true hO
    have e1 : ansN a b c m t u ea eb (inpOf H rhs f g) (ec iz, ⟨j.val, hj⟩) =
        (coreSem (fTab a b c m t (Wof a b c t u) ea (inpOf H rhs f g))
            (gTab a b c m t (Wof a b c t u) eb (inpOf H rhs f g))
            (LnBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (nx (b := b) (c := c)))
            (LnBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (ny (a := a) (c := c)))
            (LnBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (nz (a := a) (b := b)))
            (wzNf (Kof a b c u) (Rb a b c m t (inpOf H rhs f g))) (fun _ => false) (ec iz)).getLsbD
          j.val := by
      simp only [ansN, untab]
    rw [e1, hRb, fz5_N (Kof a b c u) (Wof a b c t u) ea eb H rhs f g (ec iz) hC hk,
      BitVec.getLsbD_ofNat]
    simp [hj]

theorem fz6_low (P B i : ℕ) (hi : i ≤ 5) (hP : 1 ≤ P) (hB : 1 ≤ B) : P ^ i ≤ P ^ 5 * B := by
  calc P ^ i ≤ P ^ 5 := Nat.pow_le_pow_right hP hi
    _ = P ^ 5 * 1 := (Nat.mul_one _).symm
    _ ≤ P ^ 5 * B := Nat.mul_le_mul_left _ hB

theorem fz6_lowB (P B i : ℕ) (hi : i ≤ 5) (hP : 1 ≤ P) : P ^ i * B ≤ P ^ 5 * B :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hP hi)

theorem fz6_tc (d K W P B : ℕ) (h1 : d + (K + 1) + 2 ≤ 2 * P) (h2 : W + 1 ≤ 2 * P)
    (h3 : 2 ^ (max d (K + 1)) ≤ 2 * B) : tcost d (K + 1) W ≤ 2 ^ 15 * (P ^ 5 * B) := by
  unfold tcost
  calc 2 ^ 9 * (d + (K + 1) + 2) ^ 4 * (W + 1) * 2 ^ (max d (K + 1))
      ≤ 2 ^ 9 * (2 * P) ^ 4 * (2 * P) * (2 * B) := by gcongr
    _ = 2 ^ 15 * (P ^ 5 * B) := by ring

theorem fz6_wht (d W P B : ℕ) (h1 : d + 1 ≤ P) (h2 : W + 1 ≤ 2 * P) (h3 : 2 ^ d ≤ B)
    (hP : 1 ≤ P) : whtCost d W ≤ 2 ^ 8 * (P ^ 5 * B) := by
  unfold whtCost
  calc 2 ^ 7 * (d + 1) * (W + 1) * 2 ^ d ≤ 2 ^ 7 * P * (2 * P) * B := by gcongr
    _ = 2 ^ 8 * (P ^ 2 * B) := by ring
    _ ≤ 2 ^ 8 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 2 (by norm_num) hP)

theorem fz6_max (d K B : ℕ) (hd : 2 ^ d + 2 ^ K ≤ B) : 2 ^ (max d (K + 1)) ≤ 2 * B := by
  have hd0 : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
  have hk0 : 0 < 2 ^ K := Nat.pos_of_ne_zero (by positivity)
  rcases max_cases d (K + 1) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; omega
  · rw [h, pow_succ]; omega

theorem fz6_main (a b c m t K P B : ℕ) (hK : K ≤ a + b + c)
    (hP : P = a + b + c + m + t + 3) (hB : B = 2 ^ a + 2 ^ b + 2 ^ c + 2 ^ K) :
    gjCost (m + (a + b + c) + 1) + (m + (a + b + c) + 1) ^ 2 +
    (2 ^ a + 2 ^ b) * (a + b + 2 * t + 1 + K + 1) +
    whtCost a (a + b + 2 * t + 1 + K) + whtCost b (a + b + 2 * t + 1 + K) +
    whtCost c (a + b + 2 * t + 1 + K) +
    laC (a + b + c) K +
    (a + b + c) * (K + 1) * (8 * (a + b + c) + 8) +
    2 ^ (K + 1) * ((K + 1) * (8 * (a + b + c) + 8)) +
    (tcost a (K + 1) (a + b + 2 * t + 1 + K) + tcost b (K + 1) (a + b + 2 * t + 1 + K) +
      tcost c (K + 1) (a + b + 2 * t + 1 + K) +
      2 ^ (K + 1) * (60 * (a + b + 2 * t + 1 + K + 1) ^ 2)) + 2 ^ (K + 1) +
    2 ^ c * (a + b + 2 * t + 1) * 16 + 16 ≤ 2 ^ 17 * (P ^ 5 * B) := by
  have ha0 : 0 < 2 ^ a := Nat.pos_of_ne_zero (by positivity)
  have hb0 : 0 < 2 ^ b := Nat.pos_of_ne_zero (by positivity)
  have hc0 : 0 < 2 ^ c := Nat.pos_of_ne_zero (by positivity)
  have hk0 : 0 < 2 ^ K := Nat.pos_of_ne_zero (by positivity)
  have hP1 : 1 ≤ P := by omega
  have hB1 : 1 ≤ B := by omega
  have hW : a + b + 2 * t + 1 + K + 1 ≤ 2 * P := by omega
  have hK2 : 2 ^ (K + 1) ≤ 2 * B := by rw [pow_succ]; omega
  have e1 : gjCost (m + (a + b + c) + 1) ≤ 32 * (P ^ 5 * B) := by
    unfold gjCost
    calc 32 * (m + (a + b + c) + 1 + 1) ^ 4 ≤ 32 * P ^ 4 := by gcongr; omega
      _ ≤ 32 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_low P B 4 (by norm_num) hP1 hB1)
  have e2 : (m + (a + b + c) + 1) ^ 2 ≤ 1 * (P ^ 5 * B) := by
    calc (m + (a + b + c) + 1) ^ 2 ≤ P ^ 2 := by gcongr; omega
      _ ≤ P ^ 5 * B := fz6_low P B 2 (by norm_num) hP1 hB1
      _ = 1 * (P ^ 5 * B) := (Nat.one_mul _).symm
  have e3 : (2 ^ a + 2 ^ b) * (a + b + 2 * t + 1 + K + 1) ≤ 2 * (P ^ 5 * B) := by
    calc (2 ^ a + 2 ^ b) * (a + b + 2 * t + 1 + K + 1) ≤ B * (2 * P) := by gcongr; omega
      _ = 2 * (P ^ 1 * B) := by ring
      _ ≤ 2 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 1 (by norm_num) hP1)
  have e4 := fz6_wht a (a + b + 2 * t + 1 + K) P B (by omega) hW (by omega) hP1
  have e5 := fz6_wht b (a + b + 2 * t + 1 + K) P B (by omega) hW (by omega) hP1
  have e6 := fz6_wht c (a + b + 2 * t + 1 + K) P B (by omega) hW (by omega) hP1
  have e7 : laC (a + b + c) K ≤ 2 ^ 7 * (P ^ 5 * B) := by
    unfold laC
    calc 2 ^ 7 * (a + b + c + 2) ^ 2 * (K + 2) ≤ 2 ^ 7 * P ^ 2 * P := by gcongr <;> omega
      _ = 2 ^ 7 * P ^ 3 := by ring
      _ ≤ 2 ^ 7 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_low P B 3 (by norm_num) hP1 hB1)
  have e8 : (a + b + c) * (K + 1) * (8 * (a + b + c) + 8) ≤ 8 * (P ^ 5 * B) := by
    calc (a + b + c) * (K + 1) * (8 * (a + b + c) + 8) ≤ P * P * (8 * P) := by gcongr <;> omega
      _ = 8 * P ^ 3 := by ring
      _ ≤ 8 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_low P B 3 (by norm_num) hP1 hB1)
  have e9 : 2 ^ (K + 1) * ((K + 1) * (8 * (a + b + c) + 8)) ≤ 16 * (P ^ 5 * B) := by
    calc 2 ^ (K + 1) * ((K + 1) * (8 * (a + b + c) + 8)) ≤ (2 * B) * (P * (8 * P)) := by
          gcongr <;> omega
      _ = 16 * (P ^ 2 * B) := by ring
      _ ≤ 16 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 2 (by norm_num) hP1)
  have e10 := fz6_tc a K (a + b + 2 * t + 1 + K) P B (by omega) hW (fz6_max a K B (by omega))
  have e11 := fz6_tc b K (a + b + 2 * t + 1 + K) P B (by omega) hW (fz6_max b K B (by omega))
  have e12 := fz6_tc c K (a + b + 2 * t + 1 + K) P B (by omega) hW (fz6_max c K B (by omega))
  have e13 : 2 ^ (K + 1) * (60 * (a + b + 2 * t + 1 + K + 1) ^ 2) ≤ 480 * (P ^ 5 * B) := by
    calc 2 ^ (K + 1) * (60 * (a + b + 2 * t + 1 + K + 1) ^ 2) ≤ (2 * B) * (60 * (2 * P) ^ 2) := by
          gcongr
      _ = 480 * (P ^ 2 * B) := by ring
      _ ≤ 480 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 2 (by norm_num) hP1)
  have e14 : 2 ^ (K + 1) ≤ 2 * (P ^ 5 * B) := by
    calc 2 ^ (K + 1) ≤ 2 * (P ^ 0 * B) := by simpa using hK2
      _ ≤ 2 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 0 (by norm_num) hP1)
  have e15 : 2 ^ c * (a + b + 2 * t + 1) * 16 ≤ 32 * (P ^ 5 * B) := by
    calc 2 ^ c * (a + b + 2 * t + 1) * 16 ≤ B * (2 * P) * 16 := by gcongr <;> omega
      _ = 32 * (P ^ 1 * B) := by ring
      _ ≤ 32 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 1 (by norm_num) hP1)
  have e16 : 16 ≤ 16 * (P ^ 5 * B) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.pos_of_ne_zero (by positivity)) hB1)
  norm_num at e4 e5 e6 e7 e10 e11 e12 ⊢
  omega

theorem topCost_le (a b c m t u : ℕ) :
    topCost a b c m t u + 1 ≤
      2 ^ 24 * (a + b + c + m + t + 3) ^ 12 * (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ (min (a + b + c) u)) := by
  have hK : Kof a b c u ≤ a + b + c := Nat.min_le_left _ _
  have hKd : min (a + b + c) u = Kof a b c u := rfl
  rw [hKd]
  have hm := fz6_main a b c m t (Kof a b c u) _ _ hK rfl rfl
  have hk0 : 0 < 2 ^ (Kof a b c u) := Nat.pos_of_ne_zero (by positivity)
  have hX : (a + b + c + m + t + 3) ^ 5 * (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ Kof a b c u) ≤
      (a + b + c + m + t + 3) ^ 12 * (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ Kof a b c u) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hX1 : 1 ≤ (a + b + c + m + t + 3) ^ 5 * (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ Kof a b c u) :=
    Nat.mul_pos (Nat.pos_of_ne_zero (by positivity)) (Nat.pos_of_ne_zero (by positivity))
  have hT : topSum a b c m t u ≤
      2 ^ 17 * ((a + b + c + m + t + 3) ^ 5 * (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ Kof a b c u)) := by
    unfold topSum coreCost Wof
    exact hm
  unfold topCost
  rw [Nat.mul_assoc]
  norm_num at hT ⊢
  omega

theorem fin_idx_lt (i n j L : ℕ) (hi : i < n) (hj : j < L) : i * L + j < n * L := by
  calc i * L + j < i * L + L := by omega
    _ = (i + 1) * L := by ring
    _ ≤ n * L := Nat.mul_le_mul_right L hi

theorem main : ∀ (a b c m t u : Nat),
  let F := ZMod 2
  let X := Fin a → F
  let Y := Fin b → F
  let Z := Fin c → F
  let N := a+b+c
  let inputs := m*(N+1)+(2^a+2^b)*t
  let bitsOut := a+b+2*t+1
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (ok : Fin (inputs+C.size))
    (answer : Fin (2^c) → Fin bitsOut → Fin (inputs+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.output = ok.val ∧ C.size ≤ 2^24*(N+m+t+3)^12*(2^a+2^b+2^c+2^(min N u)) ∧
    ∀ (H : Fin m → X × Y × Z) (rhs : Fin m → F)
      (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t)),
      let pack := fun (s : Nat) (v : Fin s → F) => List.ofFn (fun j : Fin s => decide (v j ≠ 0))
      let bits := (List.finRange m).flatMap (fun i =>
        pack a (H i).1 ++ pack b (H i).2.1 ++ pack c (H i).2.2 ++ [decide (rhs i ≠ 0)]) ++
        (List.finRange (2^a)).flatMap (fun ix => List.ofFn (fun j : Fin t => (f ix).val.testBit j.val)) ++
        (List.finRange (2^b)).flatMap (fun iy => List.ofFn (fun j : Fin t => (g iy).val.testBit j.val))
      let decode := fun (s v : Nat) (j : Fin s) => (if v.testBit j.val then 1 else 0 : F)
      let readWire := fun n : Fin (inputs+C.size) => (C.wires bits).getD n.val false
      let rank := Module.finrank F (Submodule.span F (Set.range H))
      let good := min rank (N-rank) ≤ u
      let total := fun iz : Fin (2^c) =>
        ∑ ix : Fin (2^a), ∑ iy : Fin (2^b),
          if ∀ i, dotProduct (H i).1 (decode a ix.val) + dotProduct (H i).2.1 (decode b iy.val) +
            dotProduct (H i).2.2 (decode c iz.val) = rhs i then (f ix).val*(g iy).val else 0
      (readWire ok = true ↔ good) ∧ ∀ iz j, readWire (answer iz j) =
        (if readWire ok then total iz else 0).testBit j.val := by
  intro a b c m t u
  obtain ⟨ea, hea⟩ := vecEquiv_exists a
  obtain ⟨eb, heb⟩ := vecEquiv_exists b
  obtain ⟨ec, hec⟩ := vecEquiv_exists c
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
  obtain ⟨gs, outs, hfan, hrb, hsize, hout, hsem⟩ :=
    (cmp_top a b c m t u ea eb ec).extract (m * (a + b + c + 1) + (2 ^ a + 2 ^ b) * t) _
      (fun j => Nat.lt_succ_of_lt (hws j))
  dsimp only
  refine ⟨⟨gs, outs (Sum.inl ())⟩, ⟨outs (Sum.inl ()), hout _⟩,
    fun iz j => ⟨outs (Sum.inr (iz, j)), hout _⟩, hfan, hrb _, rfl, ?_, ?_⟩
  · have h5 := topCost_le a b c m t u
    have h6 : (a + b + c + m + t + 3) = (a + b + c + m + t + 3) := rfl
    show gs.length ≤ _
    exact le_trans hsize h5
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
    obtain ⟨k1, k2⟩ := top_sem a b c m t u ea eb ec hea heb hec H rhs f g
    have e1 := hsem (outs (Sum.inl ())) _ hlen (Sum.inl ())
    rw [hin] at e1
    refine ⟨?_, ?_⟩
    · show (PEqualNP.CircuitLowerBounds.Circuit.wires _ _).getD (outs (Sum.inl ())) false = true ↔ _
      rw [e1]
      exact k1
    · intro iz j
      have e2 := hsem (outs (Sum.inl ())) _ hlen (Sum.inr (iz, j))
      rw [hin] at e2
      show (PEqualNP.CircuitLowerBounds.Circuit.wires _ _).getD (outs (Sum.inr (iz, j))) false =
        (if (PEqualNP.CircuitLowerBounds.Circuit.wires _ _).getD (outs (Sum.inl ())) false = true
          then _ else 0).testBit j.val
      rw [e1, e2]
      exact k2 iz j

end PEqualNP.Outside.L_lib_823

theorem PEqualNP.Outside.L_lib_823 : (∀ (a b c m t u : Nat),
  let F := ZMod 2
  let X := Fin a → F
  let Y := Fin b → F
  let Z := Fin c → F
  let N := a+b+c
  let inputs := m*(N+1)+(2^a+2^b)*t
  let bitsOut := a+b+2*t+1
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (ok : Fin (inputs+C.size))
    (answer : Fin (2^c) → Fin bitsOut → Fin (inputs+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.output = ok.val ∧ C.size ≤ 2^24*(N+m+t+3)^12*(2^a+2^b+2^c+2^(min N u)) ∧
    ∀ (H : Fin m → X × Y × Z) (rhs : Fin m → F)
      (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t)),
      let pack := fun (s : Nat) (v : Fin s → F) => List.ofFn (fun j : Fin s => decide (v j ≠ 0))
      let bits := (List.finRange m).flatMap (fun i =>
        pack a (H i).1 ++ pack b (H i).2.1 ++ pack c (H i).2.2 ++ [decide (rhs i ≠ 0)]) ++
        (List.finRange (2^a)).flatMap (fun ix => List.ofFn (fun j : Fin t => (f ix).val.testBit j.val)) ++
        (List.finRange (2^b)).flatMap (fun iy => List.ofFn (fun j : Fin t => (g iy).val.testBit j.val))
      let decode := fun (s v : Nat) (j : Fin s) => (if v.testBit j.val then 1 else 0 : F)
      let readWire := fun n : Fin (inputs+C.size) => (C.wires bits).getD n.val false
      let rank := Module.finrank F (Submodule.span F (Set.range H))
      let good := min rank (N-rank) ≤ u
      let total := fun iz : Fin (2^c) =>
        ∑ ix : Fin (2^a), ∑ iy : Fin (2^b),
          if ∀ i, dotProduct (H i).1 (decode a ix.val) + dotProduct (H i).2.1 (decode b iy.val) +
            dotProduct (H i).2.2 (decode c iz.val) = rhs i then (f ix).val*(g iy).val else 0
      (readWire ok = true ↔ good) ∧ ∀ iz j, readWire (answer iz j) =
        (if readWire ok then total iz else 0).testBit j.val) :=
  PEqualNP.Outside.L_lib_823.main

