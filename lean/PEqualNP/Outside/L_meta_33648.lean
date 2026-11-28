import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33648
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

def rotN (k h w : ℕ) : ℕ := ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2^k

def stepN (k w : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
    (!(w.testBit ((i+1)%k)) && w.testBit ((i+2)%k))).toNat <<< i)) 0

noncomputable def stateN (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2^k)) : ℕ :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let g := if col then 2 else 1
  (List.finRange r).foldl (fun x j =>
    stepN k (x ^^^ rotN k g x ^^^ rotN k (k-g) x) ^^^
      rotN k (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
    (rotN k (if col then 3 else 1) w ^^^ name)

noncomputable def reachN (r : ℕ) (col : Bool) : ℕ :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  if col then 7*r-2 else 5*r-3

noncomputable def delayN (r : ℕ) (col : Bool) : ℕ :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  if col then 3*r+1 else 2*r-2

def bitsN (a x : ℕ) : List Bool := (List.range a).map (fun i => x.testBit i)

noncomputable def reportN (k r m : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (w : ℕ) : ℕ :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  (List.finRange k).foldl (fun z p =>
    let bit := fun col : Bool => (stateN k r col w (if col then nc.val else nr.val)
      (if col then cc else cr)).testBit ((p.val+delayN r col)%k)
    (z ^^^ (if bit false then (A p).val else 0)) ^^^
      (if bit true then (B p).val else 0)) (0 : Nat)

def passP (k r m b : ℕ) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) : Prop :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let V := Fin m → ZMod 2
  let vec := fun (w : Nat) (i : Fin m) => if w.testBit i.val then (1 : ZMod 2) else 0
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  let sites := List.ofFn ord
  let span := fun (ps : List (Fin k)) => Submodule.span (ZMod 2)
    (↑((ps.flatMap (fun p => [vec (A p).val, vec (B p).val])).toFinset) : Set V)
  let arc := fun (p : Fin k) (col : Bool) =>
    (Finset.univ : Finset (Fin k)).filter (fun z =>
      (if col then (B p).val else (A p).val) ≠ 0 ∧
      ∃ h : Fin (reach col + 1), (p.val+h.val)%k = z.val)
  let scope := fun p => arc p false ∪ arc p true
  let pool := fun (ps : List (Fin k)) => ps.toFinset.biUnion scope
  Function.Bijective ord ∧ ∀ i : Fin k,
    let L := sites.take i.val
    let R := sites.drop i.val
    ((pool L ∩ pool R) ∪ scope (ord i)).card +
      Module.finrank (ZMod 2) (span L ⊓ span R : Submodule (ZMod 2) V) ≤ b

noncomputable def cntPin (k : ℕ) (h : ℕ → Prop) (pin value : Fin k → Bool) : ℕ :=
  Nat.card {w : Fin (2^k) // h w.val ∧ ∀ i : Fin k, pin i = true → w.val.testBit i.val = value i}

abbrev Dat (k r m : ℕ) : Type :=
  (Fin k ⊕ Fin k) ⊕ (((Fin r × Fin k) ⊕ (Fin r × Fin k)) ⊕
    (((Fin k × Fin m) ⊕ (Fin k × Fin m)) ⊕ ((Fin k × Fin k) ⊕ Fin m)))

def encD {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) : Dat k r m → Bool :=
  Sum.elim (Sum.elim (fun i => nr.val.testBit i.val) (fun i => nc.val.testBit i.val))
    (Sum.elim (Sum.elim (fun p => (cr p.1).val.testBit p.2.val)
        (fun p => (cc p.1).val.testBit p.2.val))
      (Sum.elim (Sum.elim (fun p => (A p.1).val.testBit p.2.val)
          (fun p => (B p.1).val.testBit p.2.val))
        (Sum.elim (fun p => (ord p.1).val.testBit p.2.val) (fun i => y.val.testBit i.val))))

abbrev CoreIn (k r m : ℕ) : Type := Dat k r m ⊕ (Fin k ⊕ Fin k)

def coreS (k r m b : ℕ) : ℕ := 2^47 * (k+r+m+5)^19 * 2^b

def CoreSpec (k r m b : ℕ) (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k+1)) → Bool) : Prop :=
  ∀ (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m))
    (ord : Fin k → Fin k) (y : Fin (2^m)) (pin value : Fin k → Bool),
    (F (Sum.elim (encD nr nc cr cc A B ord y) (Sum.elim pin value)) (Sum.inl ()) = true ↔
      passP k r m b A B ord) ∧
    (passP k r m b A B ord → ∀ j : Fin (k+1),
      F (Sum.elim (encD nr nc cr cc A B ord y) (Sum.elim pin value)) (Sum.inr j) =
        (cntPin k (fun w => reportN k r m nr nc cr cc A B w = y.val) pin value).testBit j.val)

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

def vecN (m x : ℕ) : Fin m → ZMod 2 := fun i => if x.testBit i.val then 1 else 0

def scopeS (k r m : ℕ) (A B : Fin k → Fin (2^m)) (p : Fin k) : Finset (Fin k) :=
  Finset.univ.filter (fun z =>
    ((A p).val ≠ 0 ∧ ∃ h : ℕ, h ≤ 5*r-3 ∧ (p.val+h)%k = z.val) ∨
    ((B p).val ≠ 0 ∧ ∃ h : ℕ, h ≤ 7*r-2 ∧ (p.val+h)%k = z.val))

def poolLo (k r m : ℕ) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun z => ∃ i' : Fin k, i'.val < i ∧ z ∈ scopeS k r m A B (ord i'))

def poolHi (k r m : ℕ) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun z => ∃ i' : Fin k, i ≤ i'.val ∧ z ∈ scopeS k r m A B (ord i'))

def spanLo (k m : ℕ) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ) :
    Submodule (ZMod 2) (Fin m → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ i' : Fin k, i'.val < i ∧
    (v = vecN m (A (ord i')).val ∨ v = vecN m (B (ord i')).val)}

def spanHi (k m : ℕ) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ) :
    Submodule (ZMod 2) (Fin m → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ i' : Fin k, i ≤ i'.val ∧
    (v = vecN m (A (ord i')).val ∨ v = vecN m (B (ord i')).val)}

def glSol (M N1 N2 : ℕ) (Hb : Fin M × Fin (N1+N2+1) → Bool) (e : Fin N2 → ZMod 2) : Prop :=
  ∃ c : Fin N1 → ZMod 2, ∀ i : Fin M,
    (∑ j : Fin N1, b2z (Hb (i, ⟨j.val, by omega⟩)) * c j) +
    (∑ j : Fin N2, b2z (Hb (i, ⟨N1 + j.val, by omega⟩)) * e j) =
      b2z (Hb (i, ⟨N1 + N2, by omega⟩))

def glCost (M N1 N2 β : ℕ) : ℕ := 2^12 * (M + N1 + N2 + β + 2)^6

abbrev GlOut (N2 β : ℕ) : Type := (Fin N2 × Fin β) ⊕ (Fin N2 ⊕ (Fin β ⊕ Unit))

def glPt {N2 β : ℕ} (o : GlOut N2 β → Bool) (x : Fin β → ZMod 2) : Fin N2 → ZMod 2 :=
  fun j => b2z (o (Sum.inr (Sum.inl j))) + ∑ t : Fin β, b2z (o (Sum.inl (j, t))) * x t

def glOk {N2 β : ℕ} (o : GlOut N2 β → Bool) (x : Fin β → ZMod 2) : Prop :=
  ∀ t : Fin β, o (Sum.inr (Sum.inr (Sum.inl t))) = false → x t = 0

def GlSpec (M N1 N2 β : ℕ)
    (F : (Fin M × Fin (N1+N2+1) → Bool) → GlOut N2 β → Bool)
    (nf : (Fin M × Fin (N1+N2+1) → Bool) → ℕ) : Prop :=
  ∀ Hb : Fin M × Fin (N1+N2+1) → Bool,
    (F Hb (Sum.inr (Sum.inr (Sum.inr ()))) = false → ∀ e, ¬ glSol M N1 N2 Hb e) ∧
    (F Hb (Sum.inr (Sum.inr (Sum.inr ()))) = true →
      Nat.card {e : Fin N2 → ZMod 2 // glSol M N1 N2 Hb e} = 2^(nf Hb) ∧
      (∀ t : Fin β, F Hb (Sum.inr (Sum.inr (Sum.inl t))) = true ↔ t.val < nf Hb) ∧
      (nf Hb ≤ β →
        (∀ x, glOk (F Hb) x → glSol M N1 N2 Hb (glPt (F Hb) x)) ∧
        (∀ e, glSol M N1 N2 Hb e → ∃ x, glOk (F Hb) x ∧ glPt (F Hb) x = e) ∧
        (∀ x x', glOk (F Hb) x → glOk (F Hb) x' → glPt (F Hb) x = glPt (F Hb) x' → x = x')))

def gl_P {n : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (e : Fin n → ZMod 2) : Prop :=
  ∀ j, fl j = false → e j = b2z (a j) + ∑ q, if fl q = true then b2z (G (j, q)) * e q else 0

def gl_A {n : ℕ} (β : ℕ) (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool) :
    GlOut n β → Bool :=
  Sum.elim (fun p => decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = p.2.val ∧
      xor (decide (p.1 = q)) (G (p.1, q)) = true))
    (Sum.elim a (Sum.elim (fun t => decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = t.val))
      (fun _ => c)))

def gl_xs {n β : ℕ} (fl : Fin n → Bool) (x : Fin β → ZMod 2) (q : Fin n) : ZMod 2 :=
  if h : cnt fl q.val < β then x ⟨_, h⟩ else 0

theorem gl_cnt_mono {n : ℕ} (fl : Fin n → Bool) (i i' : ℕ) (h : i ≤ i') : cnt fl i ≤ cnt fl i' := by
  unfold cnt
  apply Finset.card_le_card
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨h1, h2⟩
  exact ⟨by omega, h2⟩

theorem gl_cnt_lt {n : ℕ} (fl : Fin n → Bool) (q : Fin n) (hq : fl q = true) :
    cnt fl q.val < cnt fl n := by
  have h1 := cnt_succ fl q.val q.isLt
  rw [if_pos hq] at h1
  have h2 := gl_cnt_mono fl (q.val + 1) n q.isLt
  omega

theorem gl_cnt_inj {n : ℕ} (fl : Fin n → Bool) (q q' : Fin n) (hq : fl q = true)
    (hq' : fl q' = true) (h : cnt fl q.val = cnt fl q'.val) : q = q' := by
  by_contra hne
  have key : ∀ a b : Fin n, a < b → fl a = true → cnt fl a.val < cnt fl b.val := by
    intro a b hab ha
    have h1 := cnt_succ fl a.val a.isLt
    rw [if_pos ha] at h1
    have h2 := gl_cnt_mono fl (a.val + 1) b.val hab
    omega
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have := key q q' h1 hq; omega
  · have := key q' q h1 hq'; omega

theorem gl_cnt_surj {n : ℕ} (fl : Fin n → Bool) : ∀ i, i ≤ n → ∀ t, t < cnt fl i →
    ∃ q : Fin n, q.val < i ∧ fl q = true ∧ cnt fl q.val = t := by
  intro i
  induction i with
  | zero => intro _ t ht; rw [cnt_zero] at ht; omega
  | succ i ih =>
    intro hi t ht
    rw [cnt_succ fl i hi] at ht
    by_cases h : t < cnt fl i
    · obtain ⟨q, h1, h2, h3⟩ := ih (by omega) t h
      exact ⟨q, by omega, h2, h3⟩
    · by_cases hf : fl ⟨i, hi⟩ = true
      · rw [if_pos hf] at ht
        exact ⟨⟨i, hi⟩, by simp, hf, by simp; omega⟩
      · rw [if_neg hf] at ht; omega

theorem gl_b2z_ex {n : ℕ} (fl : Fin n → Bool) (t : ℕ) (c : Fin n → Bool) :
    b2z (decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = t ∧ c q = true)) =
      ∑ q : Fin n, if (fl q = true ∧ cnt fl q.val = t) then b2z (c q) else 0 := by
  by_cases h : ∃ q : Fin n, fl q = true ∧ cnt fl q.val = t
  · obtain ⟨q0, h1, h2⟩ := h
    rw [Finset.sum_eq_single q0]
    · rw [if_pos ⟨h1, h2⟩]
      cases hc : c q0
      · have : ¬ ∃ q : Fin n, fl q = true ∧ cnt fl q.val = t ∧ c q = true := by
          rintro ⟨q, a1, a2, a3⟩
          have := gl_cnt_inj fl q q0 a1 h1 (a2.trans h2.symm)
          subst this
          rw [hc] at a3; exact Bool.false_ne_true a3
        simp [this, b2z]
      · have : ∃ q : Fin n, fl q = true ∧ cnt fl q.val = t ∧ c q = true := ⟨q0, h1, h2, hc⟩
        simp [this, b2z]
    · intro q _ hq
      rw [if_neg]
      rintro ⟨a1, a2⟩
      exact hq (gl_cnt_inj fl q q0 a1 h1 (a2.trans h2.symm))
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · have h' : ¬ ∃ q : Fin n, fl q = true ∧ cnt fl q.val = t ∧ c q = true := by
      rintro ⟨q, a1, a2, _⟩; exact h ⟨q, a1, a2⟩
    rw [decide_eq_false h']
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨a1, a2⟩; exact h ⟨q, a1, a2⟩

theorem gl_pt {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) (j : Fin n) :
    glPt (gl_A β fl a G c) x j = b2z (a j) +
      ∑ q, if fl q = true then b2z (xor (decide (j = q)) (G (j, q))) * gl_xs fl x q else 0 := by
  unfold glPt
  simp only [gl_A, Sum.elim_inl, Sum.elim_inr]
  congr 1
  have e1 : ∀ t : Fin β, b2z (decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = t.val ∧
      xor (decide (j = q)) (G (j, q)) = true)) * x t =
      ∑ q : Fin n, (if (fl q = true ∧ cnt fl q.val = t.val) then
        b2z (xor (decide (j = q)) (G (j, q))) else 0) * x t := by
    intro t
    rw [gl_b2z_ex fl t.val (fun q => xor (decide (j = q)) (G (j, q))), Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun t _ => e1 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : fl q = true
  · rw [if_pos hq]
    have hlt : cnt fl q.val < β := lt_of_lt_of_le (gl_cnt_lt fl q hq) hβ
    rw [Finset.sum_eq_single (⟨cnt fl q.val, hlt⟩ : Fin β)]
    · rw [if_pos ⟨hq, rfl⟩]
      simp [gl_xs, hlt]
    · intro t _ ht
      rw [if_neg, zero_mul]
      rintro ⟨_, a2⟩
      exact ht (Fin.ext a2.symm)
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro t _
    rw [if_neg (fun hh => hq hh.1), zero_mul]

theorem gl_pt_free {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) (j : Fin n) (hj : fl j = true) :
    glPt (gl_A β fl a G c) x j = gl_xs fl x j := by
  rw [gl_pt fl a G c hβ x j, (hz j hj).1]
  rw [Finset.sum_eq_single j]
  · rw [if_pos hj, (hz j hj).2 j]
    simp [b2z]
  · intro q _ hq
    by_cases hf : fl q = true
    · rw [if_pos hf, (hz j hj).2 q]
      have : decide (j = q) = false := decide_eq_false (fun h => hq h.symm)
      simp [this, b2z]
    · rw [if_neg hf]
  · intro hh; exact absurd (Finset.mem_univ _) hh

theorem gl_pt_piv {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) (j : Fin n) (hj : fl j = false) :
    glPt (gl_A β fl a G c) x j = b2z (a j) +
      ∑ q, if fl q = true then b2z (G (j, q)) * gl_xs fl x q else 0 := by
  rw [gl_pt fl a G c hβ x j]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  by_cases hf : fl q = true
  · rw [if_pos hf, if_pos hf]
    have : decide (j = q) = false := decide_eq_false (fun h => by rw [h, hf] at hj; exact Bool.noConfusion hj)
    simp [this]
  · rw [if_neg hf, if_neg hf]

theorem gl_A_sol {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) : gl_P fl a G (glPt (gl_A β fl a G c) x) := by
  intro j hj
  rw [gl_pt_piv fl a G c hβ x j hj]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  by_cases hf : fl q = true
  · rw [if_pos hf, if_pos hf, gl_pt_free fl a G c hz hβ x q hf]
  · rw [if_neg hf, if_neg hf]

theorem gl_A_inj {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (x x' : Fin β → ZMod 2)
    (hx : glOk (gl_A β fl a G c) x) (hx' : glOk (gl_A β fl a G c) x')
    (h : glPt (gl_A β fl a G c) x = glPt (gl_A β fl a G c) x') : x = x' := by
  funext t
  by_cases hu : ∃ q : Fin n, fl q = true ∧ cnt fl q.val = t.val
  · obtain ⟨q, h1, h2⟩ := hu
    have e1 := gl_pt_free fl a G c hz hβ x q h1
    have e2 := gl_pt_free fl a G c hz hβ x' q h1
    rw [h] at e1
    have e3 : gl_xs fl x q = gl_xs fl x' q := e1.symm.trans e2
    have hlt : cnt fl q.val < β := by rw [h2]; exact t.isLt
    have ht : (⟨cnt fl q.val, hlt⟩ : Fin β) = t := Fin.ext h2
    simpa [gl_xs, hlt, ht] using e3
  · have u : gl_A β fl a G c (Sum.inr (Sum.inr (Sum.inl t))) = false := by
      simp only [gl_A, Sum.elim_inr, Sum.elim_inl]
      exact decide_eq_false hu
    rw [hx t u, hx' t u]

theorem gl_A_surj {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (e : Fin n → ZMod 2) (he : gl_P fl a G e) :
    ∃ x, glOk (gl_A β fl a G c) x ∧ glPt (gl_A β fl a G c) x = e := by
  refine ⟨fun t => ∑ q : Fin n, if (fl q = true ∧ cnt fl q.val = t.val) then e q else 0, ?_, ?_⟩
  · intro t ht
    simp only [gl_A, Sum.elim_inr, Sum.elim_inl, decide_eq_false_iff_not] at ht
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨a1, a2⟩; exact ht ⟨q, a1, a2⟩
  · have hxs : ∀ q, fl q = true → gl_xs fl (fun t : Fin β => ∑ q : Fin n,
        if (fl q = true ∧ cnt fl q.val = t.val) then e q else 0) q = e q := by
      intro q hq
      have hlt : cnt fl q.val < β := lt_of_lt_of_le (gl_cnt_lt fl q hq) hβ
      simp only [gl_xs, hlt, dif_pos]
      rw [Finset.sum_eq_single q]
      · rw [if_pos ⟨hq, rfl⟩]
      · intro q' _ hne
        rw [if_neg]
        rintro ⟨a1, a2⟩
        exact hne (gl_cnt_inj fl q' q a1 hq a2)
      · intro hh; exact absurd (Finset.mem_univ _) hh
    funext j
    by_cases hj : fl j = true
    · rw [gl_pt_free fl a G c hz hβ _ j hj, hxs j hj]
    · have hj' : fl j = false := by simpa using hj
      rw [gl_pt_piv fl a G c hβ _ j hj', he j hj']
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      by_cases hf : fl q = true
      · rw [if_pos hf, if_pos hf, hxs q hf]
      · rw [if_neg hf, if_neg hf]

theorem gl_A_used {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (t : Fin β) : gl_A β fl a G c (Sum.inr (Sum.inr (Sum.inl t))) = true ↔ t.val < cnt fl n := by
  simp only [gl_A, Sum.elim_inr, Sum.elim_inl, decide_eq_true_eq]
  constructor
  · rintro ⟨q, h1, h2⟩
    rw [← h2]; exact gl_cnt_lt fl q h1
  · intro h
    obtain ⟨q, _, h2, h3⟩ := gl_cnt_surj fl n le_rfl t.val h
    exact ⟨q, h2, h3⟩

theorem gl_P_card {n : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) :
    Nat.card {e : Fin n → ZMod 2 // gl_P fl a G e} = 2 ^ (cnt fl n) := by
  have hcard : Fintype.card {q : Fin n // fl q = true} = cnt fl n := by
    rw [Fintype.card_subtype]; unfold cnt; congr 1; ext q; simp
  have hext : ∀ g : {q : Fin n // fl q = true} → ZMod 2, gl_P fl a G (fun j =>
      if h : fl j = true then g ⟨j, h⟩ else b2z (a j) +
        ∑ q, if h : fl q = true then b2z (G (j, q)) * g ⟨q, h⟩ else 0) := by
    intro g j hj
    have hj' : ¬ fl j = true := by rw [hj]; exact Bool.false_ne_true
    simp only [dif_neg hj']
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    by_cases hf : fl q = true
    · rw [if_pos hf, dif_pos hf, dif_pos hf]
    · rw [if_neg hf, dif_neg hf]
  have e : {e : Fin n → ZMod 2 // gl_P fl a G e} ≃ ({q : Fin n // fl q = true} → ZMod 2) :=
    { toFun := fun e q => e.1 q.1
      invFun := fun g => ⟨_, hext g⟩
      left_inv := by
        intro e
        apply Subtype.ext
        funext j
        by_cases hj : fl j = true
        · simp only [dif_pos hj]
        · have hj' : fl j = false := by simpa using hj
          simp only [dif_neg hj]
          rw [e.2 j hj']
          congr 1 <;> (
            apply Finset.sum_congr rfl
            intro q _
            by_cases hf : fl q = true
            · rw [if_pos hf, dif_pos hf]
            · rw [if_neg hf, dif_neg hf])
      right_inv := by
        intro g
        funext q
        simp only [dif_pos q.2] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, hcard]

def gl_Hf {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool) : Fin M → V (N1+N2) :=
  fun i j => b2z (Hb (i, ⟨j.val, by omega⟩))

def gl_rhs {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool) : Fin M → ZMod 2 :=
  fun i => b2z (Hb (i, ⟨N1+N2, by omega⟩))

def gl_mat {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool) :
    Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool := fun p =>
  if hi : p.1.val < M then
    (if hj : p.2.val < N1+N2+1 then Hb (⟨p.1.val, hi⟩, ⟨p.2.val, hj⟩) else false)
  else false

theorem gl_mat_eq {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool) :
    gl_mat Hb = sysBits (gl_Hf Hb) (gl_rhs Hb) := by
  have hb : ∀ x : Bool, x = decide (b2z x ≠ 0) := by intro x; cases x <;> simp [b2z]
  funext p
  unfold gl_mat sysBits
  by_cases hi : p.1.val < M
  · simp only [dif_pos hi]
    by_cases hj : p.2.val < N1 + N2
    · have hj' : p.2.val < N1 + N2 + 1 := by omega
      simp only [dif_pos hj, dif_pos hj', gl_Hf]
      exact hb _
    · simp only [dif_neg hj]
      by_cases hj2 : p.2.val = N1 + N2
      · have hj' : p.2.val < N1 + N2 + 1 := by omega
        simp only [dif_pos hj', if_pos hj2, gl_rhs]
        have : (⟨p.2.val, hj'⟩ : Fin (N1+N2+1)) = ⟨N1+N2, by omega⟩ := Fin.ext hj2
        rw [this]
        exact hb _
      · have hj' : ¬ p.2.val < N1 + N2 + 1 := by omega
        simp only [dif_neg hj', if_neg hj2]
  · simp only [dif_neg hi]

def gl_vc (M N1 : ℕ) {N2 : ℕ} (j : Fin N2) : Fin (M + (N1+N2) + 1) := cl M (Fin.natAdd N1 j)

def gl_fl {M N1 N2 : ℕ} (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool)
    (j : Fin N2) : Bool := !R (gl_vc M N1 j, gl_vc M N1 j)

def gl_O {M N1 N2 : ℕ} (β : ℕ) (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool) :
    GlOut N2 β → Bool :=
  gl_A β (gl_fl R) (fun j => R (gl_vc M N1 j, rc M (N1+N2)))
    (fun p => R (gl_vc M N1 p.1, gl_vc M N1 p.2)) (!R (rc M (N1+N2), rc M (N1+N2)))

theorem gl_dot {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool) (c : Fin N1 → ZMod 2)
    (e : Fin N2 → ZMod 2) (i : Fin M) :
    gl_Hf Hb i ⬝ᵥ Fin.append c e =
      (∑ j : Fin N1, b2z (Hb (i, ⟨j.val, by omega⟩)) * c j) +
      (∑ j : Fin N2, b2z (Hb (i, ⟨N1 + j.val, by omega⟩)) * e j) := by
  simp only [dotProduct]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rfl

theorem gl_split {M N1 N2 : ℕ} (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool)
    (c : Fin N1 → ZMod 2) (e : Fin N2 → ZMod 2) (p : Fin (N1+N2))
    (hc0 : ∀ q : Fin N1, pv R (Fin.castAdd N2 q) = false →
      (c q = 0 ∨ R (cl M p, cl M (Fin.castAdd N2 q)) = false)) :
    (∑ q : Fin (N1+N2), if pv R q = false then mat R (cl M p) (cl M q) * Fin.append c e q else 0) =
      ∑ q : Fin N2, if gl_fl R q = true then b2z (R (cl M p, gl_vc M N1 q)) * e q else 0 := by
  rw [Fin.sum_univ_add]
  have h1 : (∑ q : Fin N1, if pv R (Fin.castAdd N2 q) = false then
      mat R (cl M p) (cl M (Fin.castAdd N2 q)) * Fin.append c e (Fin.castAdd N2 q) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    by_cases h : pv R (Fin.castAdd N2 q) = false
    · rw [if_pos h, Fin.append_left]
      rcases hc0 q h with h0 | h0
      · rw [h0, mul_zero]
      · simp [mat, h0]
    · rw [if_neg h]
  rw [h1, zero_add]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fin.append_right]
  have hiff : (pv R (Fin.natAdd N1 q) = false) ↔ (gl_fl R q = true) := by
    simp [gl_fl, pv, gl_vc]
  by_cases h : gl_fl R q = true
  · rw [if_pos h, if_pos (hiff.mpr h)]
    rfl
  · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]

theorem gl_char {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool)
    (hcons : gj _ (gl_mat Hb) (rc M (N1+N2), rc M (N1+N2)) = false) (e : Fin N2 → ZMod 2) :
    glSol M N1 N2 Hb e ↔ gl_P (gl_fl (gj _ (gl_mat Hb)))
      (fun j => gj _ (gl_mat Hb) (gl_vc M N1 j, rc M (N1+N2)))
      (fun p => gj _ (gl_mat Hb) (gl_vc M N1 p.1, gl_vc M N1 p.2)) e := by
  rw [gl_mat_eq] at hcons ⊢
  have hmain := fun v => fh_main_iff (gl_Hf Hb) (gl_rhs Hb) hcons v
  constructor
  · rintro ⟨c, hc⟩ j hj
    have h1 : ∀ i, gl_Hf Hb i ⬝ᵥ Fin.append c e = gl_rhs Hb i := by
      intro i; rw [gl_dot]; exact hc i
    have h2 := (hmain _).mp h1 (Fin.natAdd N1 j) (by simpa [gl_fl, pv, gl_vc] using hj)
    rw [Fin.append_right, gl_split _ c e (Fin.natAdd N1 j) (fun q _ => Or.inr
      (gj_upper _ _ _ (by
        show (cl M (Fin.castAdd N2 q)).val < (cl M (Fin.natAdd N1 j)).val
        simp [cl]; omega)))] at h2
    rw [h2]
    congr 1
  · intro hP
    have hcl : ∀ (x : Fin (M + (N1+N2) + 1)) (y : Fin (M + (N1+N2) + 1)),
        mat (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb))) x y =
          b2z (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb)) (x, y)) := fun x y => rfl
    refine ⟨fun q => if pv (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb))) (Fin.castAdd N2 q) = true then
      b2z (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb)) (cl M (Fin.castAdd N2 q), rc M (N1+N2))) +
        ∑ q' : Fin N2, (if gl_fl (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb))) q' = true then
          b2z (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb)) (cl M (Fin.castAdd N2 q), gl_vc M N1 q')) * e q'
          else 0) else 0, ?_⟩
    intro i
    rw [← gl_dot]
    revert i
    refine (hmain _).mpr ?_
    intro p hp
    rw [gl_split _ _ e p (fun q hq => Or.inl (by rw [if_neg (by rw [hq]; exact Bool.false_ne_true)])),
      hcl]
    revert hp
    refine Fin.addCases (fun q => ?_) (fun j => ?_) p
    · intro hp
      rw [Fin.append_left, if_pos hp]
    · intro hp
      rw [Fin.append_right]
      exact hP j (by simpa [gl_fl, pv, gl_vc] using hp)

abbrev gl_B (M N1 N2 β : ℕ) : Type :=
  (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) ⊕ (Fin (N2 + 1) × Fin (β + 1))

def gl_blk {M N1 N2 : ℕ} (β : ℕ) (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool) :
    gl_B M N1 N2 β → Bool :=
  Sum.elim R (fun p => decide (cnt (gl_fl R) p.1.val = p.2.val))

def gl_Psi {M N1 N2 : ℕ} (β : ℕ) (w : gl_B M N1 N2 β → Bool) : GlOut N2 β → Bool :=
  Sum.elim (fun p => decide (∃ q : Fin N2, ((!w (Sum.inl (gl_vc M N1 q, gl_vc M N1 q))) &&
      w (Sum.inr (⟨q.val, by omega⟩, ⟨p.2.val, by omega⟩)) &&
      xor (decide (p.1 = q)) (w (Sum.inl (gl_vc M N1 p.1, gl_vc M N1 q)))) = true))
    (Sum.elim (fun j => w (Sum.inl (gl_vc M N1 j, rc M (N1+N2))))
      (Sum.elim (fun t => decide (∃ q : Fin N2, ((!w (Sum.inl (gl_vc M N1 q, gl_vc M N1 q))) &&
        w (Sum.inr (⟨q.val, by omega⟩, ⟨t.val, by omega⟩))) = true))
      (fun _ => !w (Sum.inl (rc M (N1+N2), rc M (N1+N2))))))

theorem gl_Psi_eq {M N1 N2 : ℕ} (β : ℕ)
    (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool) :
    gl_Psi β (gl_blk β R) = gl_O β R := by
  funext k
  rcases k with p | j | t | u
  · simp only [gl_Psi, gl_blk, gl_O, gl_A, Sum.elim_inl, Sum.elim_inr]
    refine decide_eq_decide.mpr (exists_congr fun q => ?_)
    simp [gl_fl, and_assoc]
  · rfl
  · simp only [gl_Psi, gl_blk, gl_O, gl_A, Sum.elim_inl, Sum.elim_inr]
    refine decide_eq_decide.mpr (exists_congr fun q => ?_)
    simp [gl_fl]
  · rfl

theorem gl_xbit (M N1 N2 β : ℕ) (j q : Fin N2) :
    Cb (gl_B M N1 N2 β) 1
      (fun w => xor (decide (j = q)) (w (Sum.inl (gl_vc M N1 j, gl_vc M N1 q)))) := by
  by_cases h : j = q
  · refine ((Cb.not (Cb.var (Sum.inl (gl_vc M N1 j, gl_vc M N1 q)))).mono (by norm_num)).congr ?_
    intro w; simp [h]
  · refine ((Cb.var (Sum.inl (gl_vc M N1 j, gl_vc M N1 q))).mono (by norm_num)).congr ?_
    intro w; simp [h]

theorem gl_Psi_cb (M N1 N2 β : ℕ) (k : GlOut N2 β) :
    Cb (gl_B M N1 N2 β) (N2 * 5 + 1) (fun w => gl_Psi β w k) := by
  rcases k with p | j | t | u
  · have := Cb.bigOr (ι := gl_B M N1 N2 β) (I := Fin N2)
      (φ := fun q w => ((!w (Sum.inl (gl_vc M N1 q, gl_vc M N1 q))) &&
        w (Sum.inr (⟨q.val, by omega⟩, ⟨p.2.val, by omega⟩)) &&
        xor (decide (p.1 = q)) (w (Sum.inl (gl_vc M N1 p.1, gl_vc M N1 q)))))
      (fun q => (Cb.and (Cb.and (Cb.not (Cb.var _)) (Cb.var _)) (gl_xbit M N1 N2 β p.1 q)))
    rw [Fintype.card_fin] at this
    exact (this.mono (by norm_num)).congr (fun w => decide_eq_decide.mpr Iff.rfl)
  · exact (Cb.var (Sum.inl (gl_vc M N1 j, rc M (N1+N2)))).mono (by omega)
  · have := Cb.bigOr (ι := gl_B M N1 N2 β) (I := Fin N2)
      (φ := fun q w => ((!w (Sum.inl (gl_vc M N1 q, gl_vc M N1 q))) &&
        w (Sum.inr (⟨q.val, by omega⟩, ⟨t.val, by omega⟩))))
      (fun q => (Cb.and (Cb.not (Cb.var _)) (Cb.var _)))
    rw [Fintype.card_fin] at this
    exact (this.mono (by omega)).congr (fun w => decide_eq_decide.mpr Iff.rfl)
  · exact (Cb.not (Cb.var (Sum.inl (rc M (N1+N2), rc M (N1+N2))))).mono (by omega)

theorem gl_mat_cb (M N1 N2 : ℕ) (p : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) :
    Cb (Fin M × Fin (N1+N2+1)) 1 (fun Hb => gl_mat Hb p) := by
  by_cases hi : p.1.val < M
  · by_cases hj : p.2.val < N1+N2+1
    · refine ((Cb.var ((⟨p.1.val, hi⟩ : Fin M), (⟨p.2.val, hj⟩ : Fin (N1+N2+1)))).mono
        (by norm_num)).congr ?_
      intro v; simp [gl_mat, hi, hj]
    · refine (Cb.const false).congr ?_
      intro v; simp [gl_mat, hi, hj]
  · refine (Cb.const false).congr ?_
    intro v; simp [gl_mat, hi]

theorem gl_arith (d n b X : ℕ) (hd : d + 1 ≤ X) (hn : n + 1 ≤ X) (hb : b + 1 ≤ X) :
    d * d * 1 + 32 * (d + 1) ^ 4 + (0 + (n * (0 + 1) + (n + 1) * ((b + 1) * 6))) +
      (n * b + (n + (b + 1))) * (n * 5 + 1) ≤ 2 ^ 12 * X ^ 6 := by
  have hX : 1 ≤ X := by omega
  have a1 : d * d ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have a2 : (d + 1) ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left hd 4
  have a3 : (n + 1) * (b + 1) ≤ X * X := Nat.mul_le_mul hn hb
  have a4 : n * 5 + 1 ≤ 5 * X := by omega
  have a5 : (n * b + (n + (b + 1))) = (n + 1) * (b + 1) := by ring
  have a6 : ((n + 1) * (b + 1)) * (n * 5 + 1) ≤ (X * X) * (5 * X) := Nat.mul_le_mul a3 a4
  have p2 : X * X ≤ X ^ 6 := by
    calc X * X = X ^ 2 := by ring
      _ ≤ X ^ 6 := Nat.pow_le_pow_right hX (by norm_num)
  have p4 : X ^ 4 ≤ X ^ 6 := Nat.pow_le_pow_right hX (by norm_num)
  have p3 : (X * X) * (5 * X) ≤ 5 * X ^ 6 := by
    calc (X * X) * (5 * X) = 5 * X ^ 3 := by ring
      _ ≤ 5 * X ^ 6 := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_right hX (by norm_num))
  have a7 : (n + 1) * ((b + 1) * 6) = 6 * ((n + 1) * (b + 1)) := by ring
  have a8 : n ≤ X ^ 6 := by
    have : n ≤ X * X := by nlinarith
    omega
  rw [a5, a7]
  generalize (n + 1) * (b + 1) * (n * 5 + 1) = T at a6 ⊢
  generalize (n + 1) * (b + 1) = U at a3 ⊢
  generalize (d + 1) ^ 4 = E at a2 ⊢
  generalize d * d = Q at a1 ⊢
  generalize X * X * (5 * X) = P3 at a6 p3
  generalize X * X = P2 at a1 a3 p2
  generalize X ^ 4 = P4 at a2 p4
  generalize X ^ 6 = Y at *
  omega

theorem gl_main (M N1 N2 β : ℕ) :
    ∃ (F : (Fin M × Fin (N1+N2+1) → Bool) → GlOut N2 β → Bool)
      (nf : (Fin M × Fin (N1+N2+1) → Bool) → ℕ),
      Cmp (Fin M × Fin (N1+N2+1)) (GlOut N2 β) (glCost M N1 N2 β) F ∧ GlSpec M N1 N2 β F nf := by
  refine ⟨fun Hb => gl_O β (gj _ (gl_mat Hb)), fun Hb => cnt (gl_fl (gj _ (gl_mat Hb))) N2, ?_, ?_⟩
  · have c1 : Cmp (Fin M × Fin (N1+N2+1))
        (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1))
        (Fintype.card (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) * 1) gl_mat :=
      Cmp.ofBits (fun p => gl_mat_cb M N1 N2 p)
    have c2 := cmp_gj (M + (N1+N2) + 1)
    have hn : Cmp (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) (Fin N2)
        (Fintype.card (Fin N2) * (0 + 1)) (fun R q => gl_fl R q) :=
      Cmp.ofBits (fun q => Cb.not (Cb.var (gl_vc M N1 q, gl_vc M N1 q)))
    have c3 := Cmp.pair (Cmp.wire (ι := Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) id)
      (Cmp.comp hn (cmp_counter N2 β))
    have c3' : Cmp (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) (gl_B M N1 N2 β) _
        (gl_blk β) := Cmp.congr c3 (by intro R k; rcases k with k | k <;> rfl)
    have c4 : Cmp (gl_B M N1 N2 β) (GlOut N2 β) (Fintype.card (GlOut N2 β) * (N2 * 5 + 1))
        (gl_Psi β) := Cmp.ofBits (fun k => gl_Psi_cb M N1 N2 β k)
    have call := ((c1.comp c2).comp c3').comp c4
    refine Cmp.mono (Cmp.congr call ?_) ?_
    · intro Hb k
      show gl_Psi β (gl_blk β (gj _ (gl_mat Hb))) k = _
      rw [gl_Psi_eq]
    · simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
      unfold gjCost glCost
      exact gl_arith (M + (N1+N2) + 1) N2 β (M + N1 + N2 + β + 2) (by omega) (by omega) (by omega)
  · intro Hb
    have hz : ∀ q : Fin N2, gl_fl (gj _ (gl_mat Hb)) q = true →
        gj _ (gl_mat Hb) (gl_vc M N1 q, rc M (N1+N2)) = false ∧
        ∀ q' : Fin N2, gj _ (gl_mat Hb) (gl_vc M N1 q, gl_vc M N1 q') = false := by
      intro q hq
      have hq' : gj _ (gl_mat Hb) (gl_vc M N1 q, gl_vc M N1 q) = false := by
        simpa [gl_fl] using hq
      exact ⟨gj_zerorow _ _ hq' _, fun q' => gj_zerorow _ _ hq' _⟩
    refine ⟨?_, ?_⟩
    · intro hc e he
      have hc' : gj _ (gl_mat Hb) (rc M (N1+N2), rc M (N1+N2)) = true := by
        simpa [gl_O, gl_A] using hc
      obtain ⟨c, hce⟩ := he
      rw [gl_mat_eq] at hc'
      refine la_incons (gl_Hf Hb) (gl_rhs Hb) hc' (Fin.append c e) ?_
      intro i; rw [gl_dot]; exact hce i
    · intro hc
      have hc' : gj _ (gl_mat Hb) (rc M (N1+N2), rc M (N1+N2)) = false := by
        simpa [gl_O, gl_A] using hc
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.card_congr (Equiv.subtypeEquivRight (fun e => gl_char Hb hc' e))]
        exact gl_P_card _ _ _
      · intro t
        exact gl_A_used _ _ _ _ t
      · intro hβ
        refine ⟨?_, ?_, ?_⟩
        · intro x _
          exact (gl_char Hb hc' _).mpr (gl_A_sol _ _ _ _ hz hβ x)
        · intro e he
          exact gl_A_surj _ _ _ _ hz hβ e ((gl_char Hb hc' e).mp he)
        · intro x x' hx hx' h
          exact gl_A_inj _ _ _ _ hz hβ x x' hx hx' h

def solS {ρ ι1 ι2 : Type} [Fintype ι1] [Fintype ι2]
    (Hb : ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) (e : ι2 → ZMod 2) : Prop :=
  ∃ c : ι1 → ZMod 2, ∀ i : ρ,
    (∑ j : ι1, b2z (Hb (i, Sum.inl j)) * c j) +
    (∑ j : ι2, b2z (Hb (i, Sum.inr (Sum.inl j))) * e j) = b2z (Hb (i, Sum.inr (Sum.inr ())))

abbrev SOut (ι2 : Type) (β : ℕ) : Type := (ι2 × Fin β) ⊕ (ι2 ⊕ (Fin β ⊕ Unit))

def sPt {ι2 : Type} {β : ℕ} (o : SOut ι2 β → Bool) (x : Fin β → ZMod 2) : ι2 → ZMod 2 :=
  fun j => b2z (o (Sum.inr (Sum.inl j))) + ∑ t : Fin β, b2z (o (Sum.inl (j, t))) * x t

def sOk {ι2 : Type} {β : ℕ} (o : SOut ι2 β → Bool) (x : Fin β → ZMod 2) : Prop :=
  ∀ t : Fin β, o (Sum.inr (Sum.inr (Sum.inl t))) = false → x t = 0

def SSpec (ρ ι1 ι2 : Type) [Fintype ι1] [Fintype ι2] (β : ℕ)
    (F : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → SOut ι2 β → Bool)
    (nf : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → ℕ) : Prop :=
  ∀ Hb : ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool,
    (F Hb (Sum.inr (Sum.inr (Sum.inr ()))) = false → ∀ e, ¬ solS Hb e) ∧
    (F Hb (Sum.inr (Sum.inr (Sum.inr ()))) = true →
      Nat.card {e : ι2 → ZMod 2 // solS Hb e} = 2^(nf Hb) ∧
      (∀ t : Fin β, F Hb (Sum.inr (Sum.inr (Sum.inl t))) = true ↔ t.val < nf Hb) ∧
      (nf Hb ≤ β →
        (∀ x, sOk (F Hb) x → solS Hb (sPt (F Hb) x)) ∧
        (∀ e, solS Hb e → ∃ x, sOk (F Hb) x ∧ sPt (F Hb) x = e) ∧
        (∀ x x', sOk (F Hb) x → sOk (F Hb) x' → sPt (F Hb) x = sPt (F Hb) x' → x = x')))

def tabN {t : ℕ} (T : Fin t → Bool) : ℕ := ∑ j : Fin t, if T j then 2^j.val else 0

theorem st_tabN_succ {t : ℕ} (T : Fin (t+1) → Bool) :
    tabN T = tabN (fun j : Fin t => T j.castSucc) + (if T (Fin.last t) then 2^t else 0) := by
  unfold tabN
  rw [Fin.sum_univ_castSucc]
  simp

theorem st_tabN_lt : ∀ {t : ℕ} (T : Fin t → Bool), tabN T < 2^t := by
  intro t
  induction t with
  | zero => intro T; simp [tabN]
  | succ t ih =>
    intro T
    rw [st_tabN_succ]
    have := ih (fun j : Fin t => T j.castSucc)
    rw [pow_succ]
    split <;> omega

theorem st_tabN_testBit : ∀ {t : ℕ} (T : Fin t → Bool) (j : Fin t),
    (tabN T).testBit j.val = T j := by
  intro t
  induction t with
  | zero => intro T j; exact j.elim0
  | succ t ih =>
    intro T j
    rw [st_tabN_succ]
    have hlt := st_tabN_lt (fun j : Fin t => T j.castSucc)
    by_cases hj : j.val < t
    · have e : j = (⟨j.val, hj⟩ : Fin t).castSucc := Fin.ext rfl
      have := ih (fun j : Fin t => T j.castSucc) ⟨j.val, hj⟩
      by_cases hT : T (Fin.last t) = true
      · rw [if_pos hT, add_comm, Nat.testBit_two_pow_add_gt hj, this]
        exact congrArg T e.symm
      · rw [if_neg hT, add_zero, this]
        exact congrArg T e.symm
    · have e : j = Fin.last t := Fin.ext (by have := j.isLt; simp; omega)
      subst e
      by_cases hT : T (Fin.last t) = true
      · rw [if_pos hT, add_comm]
        simp only [Fin.val_last]
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt, hT]
        rfl
      · rw [if_neg hT, add_zero]
        simp only [Fin.val_last]
        rw [Nat.testBit_lt_two_pow hlt]
        simpa using hT

theorem st_dec_b2z (x : Bool) : decide (b2z x ≠ 0) = x := by
  cases x <;> simp [b2z]

theorem st_count {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) :
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

theorem st_hom_rank {m N : ℕ} (Hf : Fin m → V N) :
    Nat.card {v : V N // ∀ i, Hf i ⬝ᵥ v = 0} =
      2 ^ (N - rkOf (gj _ (sysBits Hf (fun _ => 0)))) := by
  have sc := st_count Hf (fun _ => 0)
  have hc : gj _ (sysBits Hf (fun _ => 0)) (rc m N, rc m N) = false := by
    by_contra h
    exact la_incons Hf (fun _ => 0) (by simpa using h) 0 (fun i => by simp)
  rw [hc] at sc
  simp only [Bool.not_false, if_true] at sc
  rw [sc]
  congr 1
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun q : Fin N => pv (gj _ (sysBits Hf (fun _ => 0))) q = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have e : (Finset.univ.filter (fun p : Fin N =>
      (!(gj _ (sysBits Hf (fun _ => 0)) (cl m p, cl m p))) = true)) =
      (Finset.univ.filter (fun q : Fin N => ¬ pv (gj _ (sysBits Hf (fun _ => 0))) q = true)) := by
    apply Finset.filter_congr
    intro q _
    simp [pv]
  rw [e]
  unfold rkOf
  omega

theorem glS (ρ ι1 ι2 : Type) [Fintype ρ] [Fintype ι1] [Fintype ι2] (β : ℕ) :
    ∃ (F : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → SOut ι2 β → Bool)
      (nf : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → ℕ),
      Cmp (ρ × (ι1 ⊕ (ι2 ⊕ Unit))) (SOut ι2 β)
        (glCost (Fintype.card ρ) (Fintype.card ι1) (Fintype.card ι2) β) F ∧
      SSpec ρ ι1 ι2 β F nf := by
  classical
  obtain ⟨F0, nf0, hC, hS⟩ :=
    gl_main (Fintype.card ρ) (Fintype.card ι1) (Fintype.card ι2) β
  let eρ := Fintype.equivFin ρ
  let e1 := Fintype.equivFin ι1
  let e2 := Fintype.equivFin ι2
  let col : Fin (Fintype.card ι1 + Fintype.card ι2 + 1) → ι1 ⊕ (ι2 ⊕ Unit) := fun j =>
    if h : j.val < Fintype.card ι1 then Sum.inl (e1.symm ⟨j.val, h⟩)
    else if h2 : j.val < Fintype.card ι1 + Fintype.card ι2 then
      Sum.inr (Sum.inl (e2.symm ⟨j.val - Fintype.card ι1, by omega⟩))
    else Sum.inr (Sum.inr ())
  let σ : Fin (Fintype.card ρ) × Fin (Fintype.card ι1 + Fintype.card ι2 + 1) →
      ρ × (ι1 ⊕ (ι2 ⊕ Unit)) := fun p => (eρ.symm p.1, col p.2)
  let om : SOut ι2 β → GlOut (Fintype.card ι2) β :=
    Sum.elim (fun p => Sum.inl (e2 p.1, p.2))
      (Sum.elim (fun j => Sum.inr (Sum.inl (e2 j))) (fun x => Sum.inr (Sum.inr x)))
  have hcol1 : ∀ (j : Fin (Fintype.card ι1)) (h : j.val < Fintype.card ι1 + Fintype.card ι2 + 1),
      col ⟨j.val, h⟩ = Sum.inl (e1.symm j) := by
    intro j h
    simp [col, j.isLt]
  have hcol2 : ∀ (j : Fin (Fintype.card ι2))
      (h : Fintype.card ι1 + j.val < Fintype.card ι1 + Fintype.card ι2 + 1),
      col ⟨Fintype.card ι1 + j.val, h⟩ = Sum.inr (Sum.inl (e2.symm j)) := by
    intro j h
    simp [col, j.isLt]
  have hcol3 : ∀ (h : Fintype.card ι1 + Fintype.card ι2 < Fintype.card ι1 + Fintype.card ι2 + 1),
      col ⟨Fintype.card ι1 + Fintype.card ι2, h⟩ = Sum.inr (Sum.inr ()) := by
    intro h
    simp [col]
  refine ⟨fun Hb o => F0 (fun p => Hb (σ p)) (om o), fun Hb => nf0 (fun p => Hb (σ p)), ?_, ?_⟩
  · exact (Cmp.comp (Cmp.sel σ hC) (Cmp.wire om)).mono (by omega)
  · intro Hb
    have hs1 : ∀ (i : Fin (Fintype.card ρ)) (c' : Fin (Fintype.card ι1) → ZMod 2),
        (∑ j : ι1, b2z (Hb (eρ.symm i, Sum.inl j)) * c' (e1 j)) =
        ∑ j : Fin (Fintype.card ι1), b2z (Hb (σ (i, ⟨j.val, by omega⟩))) * c' j := by
      intro i c'
      rw [← Equiv.sum_comp e1 (fun j : Fin (Fintype.card ι1) =>
        b2z (Hb (σ (i, ⟨j.val, by omega⟩))) * c' j)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [σ]
      rw [hcol1]
      simp
    have hs2 : ∀ (i : Fin (Fintype.card ρ)) (e' : Fin (Fintype.card ι2) → ZMod 2),
        (∑ j : ι2, b2z (Hb (eρ.symm i, Sum.inr (Sum.inl j))) * e' (e2 j)) =
        ∑ j : Fin (Fintype.card ι2),
          b2z (Hb (σ (i, ⟨Fintype.card ι1 + j.val, by omega⟩))) * e' j := by
      intro i e'
      rw [← Equiv.sum_comp e2 (fun j : Fin (Fintype.card ι2) =>
        b2z (Hb (σ (i, ⟨Fintype.card ι1 + j.val, by omega⟩))) * e' j)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [σ]
      rw [hcol2]
      simp
    have hs3 : ∀ (i : Fin (Fintype.card ρ)),
        b2z (Hb (σ (i, ⟨Fintype.card ι1 + Fintype.card ι2, by omega⟩))) =
          b2z (Hb (eρ.symm i, Sum.inr (Sum.inr ()))) := by
      intro i
      simp only [σ]
      rw [hcol3]
    have key : ∀ e' : Fin (Fintype.card ι2) → ZMod 2,
        solS Hb (fun j => e' (e2 j)) ↔
          glSol (Fintype.card ρ) (Fintype.card ι1) (Fintype.card ι2) (fun p => Hb (σ p)) e' := by
      intro e'
      constructor
      · rintro ⟨c, hc⟩
        refine ⟨fun j => c (e1.symm j), fun i => ?_⟩
        have h := hc (eρ.symm i)
        rw [← hs1 i (fun j => c (e1.symm j)), ← hs2 i e', hs3]
        simpa using h
      · rintro ⟨c', hc⟩
        refine ⟨fun j => c' (e1 j), fun i => ?_⟩
        have h := hc (eρ i)
        rw [← hs1, ← hs2, hs3] at h
        simpa using h
    have key2 : ∀ e : ι2 → ZMod 2,
        solS Hb e ↔ glSol (Fintype.card ρ) (Fintype.card ι1) (Fintype.card ι2)
          (fun p => Hb (σ p)) (fun j => e (e2.symm j)) := by
      intro e
      rw [← key]
      simp
    have hpt : ∀ x : Fin β → ZMod 2,
        sPt (fun o => F0 (fun p => Hb (σ p)) (om o)) x =
          fun j => glPt (F0 (fun p => Hb (σ p))) x (e2 j) := by
      intro x
      rfl
    have hok : ∀ x : Fin β → ZMod 2,
        sOk (fun o => F0 (fun p => Hb (σ p)) (om o)) x ↔ glOk (F0 (fun p => Hb (σ p))) x := by
      intro x
      exact Iff.rfl
    obtain ⟨g1, g2⟩ := hS (fun p => Hb (σ p))
    refine ⟨?_, ?_⟩
    · intro h e he
      exact g1 h _ ((key2 e).1 he)
    · intro h
      obtain ⟨c1, c2, c3⟩ := g2 h
      refine ⟨?_, c2, ?_⟩
      · rw [← c1]
        refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr e2 (Equiv.refl _)) ?_)
        intro e
        exact key2 e
      · intro hnf
        obtain ⟨d1, d2, d3⟩ := c3 hnf
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          rw [hpt]
          exact (key _).2 (d1 x ((hok x).1 hx))
        · intro e he
          obtain ⟨x, hx, hxe⟩ := d2 _ ((key2 e).1 he)
          refine ⟨x, (hok x).2 hx, ?_⟩
          rw [hpt, hxe]
          funext j
          simp
        · intro x x' hx hx' hxx
          apply d3 x x' ((hok x).1 hx) ((hok x').1 hx')
          rw [hpt, hpt] at hxx
          funext j
          have := congrFun hxx (e2.symm j)
          simpa using this

abbrev JIn (ρ : Type) (a bb c t : ℕ) : Type :=
  (ρ × (Fin a ⊕ (Fin bb ⊕ (Fin c ⊕ Unit)))) ⊕ ((Fin (2^a) × Fin t) ⊕ (Fin (2^bb) × Fin t))

def jSat {ρ : Type} {a bb c t : ℕ} (v : JIn ρ a bb c t → Bool)
    (x : Fin a → ZMod 2) (y : Fin bb → ZMod 2) (z : Fin c → ZMod 2) : Prop :=
  ∀ i : ρ, (∑ j : Fin a, b2z (v (Sum.inl (i, Sum.inl j))) * x j) +
    (∑ j : Fin bb, b2z (v (Sum.inl (i, Sum.inr (Sum.inl j)))) * y j) +
    (∑ j : Fin c, b2z (v (Sum.inl (i, Sum.inr (Sum.inr (Sum.inl j))))) * z j) =
      b2z (v (Sum.inl (i, Sum.inr (Sum.inr (Sum.inr ())))))

def jHom {ρ : Type} {a bb c t : ℕ} (v : JIn ρ a bb c t → Bool)
    (x : Fin a → ZMod 2) (y : Fin bb → ZMod 2) (z : Fin c → ZMod 2) : Prop :=
  ∀ i : ρ, (∑ j : Fin a, b2z (v (Sum.inl (i, Sum.inl j))) * x j) +
    (∑ j : Fin bb, b2z (v (Sum.inl (i, Sum.inr (Sum.inl j)))) * y j) +
    (∑ j : Fin c, b2z (v (Sum.inl (i, Sum.inr (Sum.inr (Sum.inl j))))) * z j) = 0

noncomputable def jTot {ρ : Type} {a bb c t : ℕ} (v : JIn ρ a bb c t → Bool)
    (iz : Fin (2^c)) : ℕ :=
  ∑ ix : Fin (2^a), ∑ iy : Fin (2^bb),
    @ite ℕ (jSat v (vecN a ix.val) (vecN bb iy.val) (vecN c iz.val)) (Classical.propDecidable _)
      (tabN (fun j => v (Sum.inr (Sum.inl (ix, j)))) * tabN (fun j => v (Sum.inr (Sum.inr (iy, j)))))
      0

theorem joinS (ρ : Type) [Fintype ρ] (a bb c t u : ℕ) :
    ∃ F : (JIn ρ a bb c t → Bool) → (Fin (2^c) × Fin t → Bool),
      Cmp (JIn ρ a bb c t) (Fin (2^c) × Fin t) (topCost a bb c (Fintype.card ρ) t u) F ∧
      ∀ v : JIn ρ a bb c t → Bool,
        Nat.card {p : (Fin a → ZMod 2) × (Fin bb → ZMod 2) × (Fin c → ZMod 2) //
          jHom v p.1 p.2.1 p.2.2} ≤ 2^u →
        ∀ (iz : Fin (2^c)) (j : Fin t), F v (iz, j) = (jTot v iz).testBit j.val := by
  classical
  let eρ := Fintype.equivFin ρ
  obtain ⟨ea, hea⟩ := vecEquiv_exists a
  obtain ⟨eb, heb⟩ := vecEquiv_exists bb
  obtain ⟨ec, hec⟩ := vecEquiv_exists c
  let colJ : Fin (a + bb + c + 1) → Fin a ⊕ (Fin bb ⊕ (Fin c ⊕ Unit)) := fun j =>
    if h : j.val < a then Sum.inl ⟨j.val, h⟩
    else if h2 : j.val < a + bb then Sum.inr (Sum.inl ⟨j.val - a, by omega⟩)
    else if h3 : j.val < a + bb + c then Sum.inr (Sum.inr (Sum.inl ⟨j.val - (a + bb), by omega⟩))
    else Sum.inr (Sum.inr (Sum.inr ()))
  let σ : In0 a bb c (Fintype.card ρ) t → JIn ρ a bb c t :=
    Sum.elim (fun p => Sum.inl (eρ.symm p.1, colJ p.2)) Sum.inr
  let om : Fin (2^c) × Fin t → Unit ⊕ (Fin (2^c) × Fin (a + bb + 2 * t + 1)) :=
    fun p => Sum.inr (p.1, ⟨p.2.val, by have := p.2.isLt; omega⟩)
  refine ⟨fun v p => topF a bb c (Fintype.card ρ) t u ea eb ec (fun j => v (σ j)) (om p), ?_, ?_⟩
  · exact (Cmp.comp (Cmp.sel σ (cmp_top a bb c (Fintype.card ρ) t u ea eb ec))
      (Cmp.wire om)).mono (by omega)
  · intro v hcard iz j
    let H : Fin (Fintype.card ρ) → V a × V bb × V c := fun i =>
      (fun j => b2z (v (Sum.inl (eρ.symm i, Sum.inl j))),
       fun j => b2z (v (Sum.inl (eρ.symm i, Sum.inr (Sum.inl j)))),
       fun j => b2z (v (Sum.inl (eρ.symm i, Sum.inr (Sum.inr (Sum.inl j))))))
    let rhs : Fin (Fintype.card ρ) → ZMod 2 := fun i =>
      b2z (v (Sum.inl (eρ.symm i, Sum.inr (Sum.inr (Sum.inr ())))))
    let f : Fin (2^a) → Fin (2^t) := fun ix =>
      ⟨tabN (fun j => v (Sum.inr (Sum.inl (ix, j)))), st_tabN_lt _⟩
    let g : Fin (2^bb) → Fin (2^t) := fun iy =>
      ⟨tabN (fun j => v (Sum.inr (Sum.inr (iy, j)))), st_tabN_lt _⟩
    have hin : (fun j => v (σ j)) = inpOf H rhs f g := by
      funext q
      rcases q with p | p | p
      · show v (Sum.inl (eρ.symm p.1, colJ p.2)) =
          if h : p.2.val < a + bb + c then decide (join3 (H p.1) ⟨p.2.val, h⟩ ≠ 0)
          else decide (rhs p.1 ≠ 0)
        by_cases h1 : p.2.val < a
        · have h : p.2.val < a + bb + c := by omega
          rw [dif_pos h]
          have e1 : colJ p.2 = Sum.inl ⟨p.2.val, h1⟩ := by simp [colJ, h1]
          have e2 : join3 (H p.1) ⟨p.2.val, h⟩ = (H p.1).1 ⟨p.2.val, h1⟩ := by
            simp [join3, h1]
          rw [e1, e2, st_dec_b2z]
        · by_cases h2 : p.2.val < a + bb
          · have h : p.2.val < a + bb + c := by omega
            rw [dif_pos h]
            have e1 : colJ p.2 = Sum.inr (Sum.inl ⟨p.2.val - a, by omega⟩) := by
              simp [colJ, h1, h2]
            have e2 : join3 (H p.1) ⟨p.2.val, h⟩ = (H p.1).2.1 ⟨p.2.val - a, by omega⟩ := by
              simp [join3, h1, h2]
            rw [e1, e2, st_dec_b2z]
          · by_cases h3 : p.2.val < a + bb + c
            · rw [dif_pos h3]
              have e1 : colJ p.2 =
                  Sum.inr (Sum.inr (Sum.inl ⟨p.2.val - (a + bb), by omega⟩)) := by
                simp [colJ, h1, h2, h3]
              have e2 : join3 (H p.1) ⟨p.2.val, h3⟩ =
                  (H p.1).2.2 ⟨p.2.val - (a + bb), by omega⟩ := by
                simp [join3, h1, h2]
              rw [e1, e2, st_dec_b2z]
            · rw [dif_neg h3]
              have e1 : colJ p.2 = Sum.inr (Sum.inr (Sum.inr ())) := by
                simp [colJ, h1, h2, h3]
              rw [e1, st_dec_b2z]
      · show v (Sum.inr (Sum.inl p)) = (f p.1).val.testBit p.2.val
        exact (st_tabN_testBit (fun j => v (Sum.inr (Sum.inl (p.1, j)))) p.2).symm
      · show v (Sum.inr (Sum.inr p)) = (g p.1).val.testBit p.2.val
        exact (st_tabN_testBit (fun j => v (Sum.inr (Sum.inr (p.1, j)))) p.2).symm
    obtain ⟨k1, k2⟩ := top_sem a bb c (Fintype.card ρ) t u ea eb ec hea heb hec H rhs f g
    have hN : a + bb + c - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) ≤ u := by
      rw [tr_rank H (fun _ => 0)]
      have hh := st_hom_rank (fun i => join3 (H i))
      have hle : Nat.card {w : V (a + bb + c) // ∀ i, (fun i => join3 (H i)) i ⬝ᵥ w = 0} ≤
          Nat.card {p : (Fin a → ZMod 2) × (Fin bb → ZMod 2) × (Fin c → ZMod 2) //
            jHom v p.1 p.2.1 p.2.2} := by
        refine Nat.card_le_card_of_injective
          (fun w => ⟨(fun j => w.1 (nx j), fun j => w.1 (ny j), fun j => w.1 (nz j)), ?_⟩) ?_
        · intro i
          have hw := w.2 (eρ i)
          have ew : w.1 = join3 ((fun j => w.1 (nx j), fun j => w.1 (ny j),
              fun j => w.1 (nz j)) : V a × V bb × V c) := by
            apply ft_ext
            · intro j; rw [ft_join_nx]
            · intro j; rw [ft_join_ny]
            · intro j; rw [ft_join_nz]
          rw [ew] at hw
          have hd := ft_dot (H (eρ i)) (fun j => w.1 (nx j)) (fun j => w.1 (ny j))
            (fun j => w.1 (nz j))
          rw [hd] at hw
          simp only [H, dotProduct, Equiv.symm_apply_apply] at hw
          exact hw
        · intro w w' hww
          apply Subtype.ext
          have h1 := congrArg (fun q => q.1.1) hww
          have h2 := congrArg (fun q => q.1.2.1) hww
          have h3 := congrArg (fun q => q.1.2.2) hww
          simp only at h1 h2 h3
          exact ft_ext _ _ (fun j => congrFun h1 j) (fun j => congrFun h2 j)
            (fun j => congrFun h3 j)
      rw [hh] at hle
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (le_trans hle hcard)
    have hflag := k1.2 (le_trans (min_le_right _ _) hN)
    show topF a bb c (Fintype.card ρ) t u ea eb ec (fun j => v (σ j))
      (Sum.inr (iz, ⟨j.val, _⟩)) = _
    rw [hin, k2 iz ⟨j.val, by have := j.isLt; omega⟩, if_pos hflag]
    congr 1
    unfold jTot
    apply Finset.sum_congr rfl
    intro ix _
    apply Finset.sum_congr rfl
    intro iy _
    have hiff : (∀ i, (H i).1 ⬝ᵥ (fun j : Fin a => if ix.val.testBit j.val then (1 : ZMod 2) else 0) +
        (H i).2.1 ⬝ᵥ (fun j : Fin bb => if iy.val.testBit j.val then (1 : ZMod 2) else 0) +
        (H i).2.2 ⬝ᵥ (fun j : Fin c => if iz.val.testBit j.val then (1 : ZMod 2) else 0) = rhs i) ↔
        jSat v (vecN a ix.val) (vecN bb iy.val) (vecN c iz.val) := by
      constructor
      · intro h i
        have := h (eρ i)
        simp only [H, rhs, dotProduct, Equiv.symm_apply_apply] at this
        exact this
      · intro h i
        exact h (eρ.symm i)
    by_cases hs : jSat v (vecN a ix.val) (vecN bb iy.val) (vecN c iz.val)
    · rw [if_pos (hiff.2 hs), if_pos hs]
    · rw [if_neg (fun h => hs (hiff.1 h)), if_neg hs]

theorem sn_ite_cl {α : Type} (c : Bool) (x y : α) :
    @ite α (c = true) (Classical.propDecidable (c = true)) x y = cond c x y := by
  cases c
  · exact if_neg Bool.false_ne_true
  · exact if_pos rfl

theorem sn_ite_any {α : Type} (c : Bool) (inst : Decidable (c = true)) (x y : α) :
    @ite α (c = true) inst x y = cond c x y := by
  cases c
  · exact if_neg Bool.false_ne_true
  · exact if_pos rfl

theorem sn_ite_T {α : Type} (inst : Decidable True) (x y : α) : @ite α True inst x y = x :=
  if_pos trivial

theorem sn_ite_F {α : Type} (inst : Decidable False) (x y : α) : @ite α False inst x y = y :=
  if_neg not_false

theorem sn_rot_lt (k s x : ℕ) : rotN k s x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

theorem sn_xor_lt {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

theorem sn_testBit_rot {k s x b : ℕ} (hw : x < 2 ^ k) (hb : b < k) :
    (rotN k s x).testBit b = x.testBit ((b + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [rotN, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hz : x.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (b + k - s % k) % k = b - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    simp [h, hz, he]
  · have he : (b + k - s % k) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [h, he]

theorem sn_testBit_foldl_or (p : ℕ → Bool) (xs : List ℕ) (acc i : ℕ) :
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

theorem sn_testBit_step (k x b : ℕ) :
    (stepN k x).testBit b = (decide (b < k) &&
      xor (x.testBit b) (!(x.testBit ((b + 1) % k)) && x.testBit ((b + 2) % k))) := by
  have h := sn_testBit_foldl_or (fun i => xor (x.testBit i)
    (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))) (List.range k) 0 b
  unfold stepN
  rw [h]
  simp

theorem sn_step_lt (k x : ℕ) : stepN k x < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [sn_testBit_step, Nat.not_lt_of_ge hb]

def sn_g (col : Bool) : ℕ := cond col 2 1
def sn_s0 (col : Bool) : ℕ := cond col 3 1
def sn_sh (col : Bool) (j : ℕ) : ℕ := cond col (3 * (j + 1) + 1) (2 * j)

def sn_body (k g s w x cj : ℕ) : ℕ :=
  stepN k (x ^^^ rotN k g x ^^^ rotN k (k - g) x) ^^^ rotN k s w ^^^ cj

theorem sn_state_fold (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2^k)) :
    stateN k r col w name c = (List.finRange r).foldl (fun x j =>
      sn_body k (sn_g col) (sn_sh col j.val) w x (c j).val) (rotN k (sn_s0 col) w ^^^ name) := by
  unfold stateN
  simp only [sn_ite_cl]
  rfl

def sn_stN (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2^k)) : ℕ → ℕ
  | 0 => rotN k (sn_s0 col) w ^^^ name
  | t + 1 => if h : t < r then
      sn_body k (sn_g col) (sn_sh col t) w (sn_stN k r col w name c t) (c ⟨t, h⟩).val
    else sn_stN k r col w name c t

theorem sn_fold_take (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2^k)) :
    ∀ t, t ≤ r → ((List.finRange r).take t).foldl (fun x j =>
      sn_body k (sn_g col) (sn_sh col j.val) w x (c j).val) (rotN k (sn_s0 col) w ^^^ name) =
      sn_stN k r col w name c t := by
  intro t
  induction t with
  | zero => intro _; simp [sn_stN]
  | succ t ih =>
    intro ht
    have ht' : t < r := by omega
    have htake : (List.finRange r).take (t + 1) =
        (List.finRange r).take t ++ [⟨t, ht'⟩] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [ht'])]
      simp [List.getElem_finRange]
    rw [htake, List.foldl_append, ih (by omega)]
    simp [sn_stN, ht']

theorem sn_state_eq (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2^k)) :
    stateN k r col w name c = sn_stN k r col w name c r := by
  rw [sn_state_fold, ← sn_fold_take k r col w name c r le_rfl,
    List.take_of_length_le (by simp)]

theorem sn_body_lt (k g s w x cj : ℕ) (hc : cj < 2^k) : sn_body k g s w x cj < 2^k :=
  sn_xor_lt (sn_xor_lt (sn_step_lt k _) (sn_rot_lt k _ _)) hc

theorem sn_stN_lt (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2^k))
    (hn : name < 2^k) : ∀ t, sn_stN k r col w name c t < 2^k := by
  intro t
  induction t with
  | zero => exact sn_xor_lt (sn_rot_lt k _ _) hn
  | succ t ih =>
    by_cases h : t < r
    · simp only [sn_stN, h, dif_pos]
      exact sn_body_lt _ _ _ _ _ _ (c ⟨t, h⟩).isLt
    · simp only [sn_stN, h, dif_neg, not_false_eq_true]
      exact ih

def sn_ri {k : ℕ} (s : ℕ) (i : Fin k) : Fin k := ⟨(i.val + k - s % k) % k, Nat.mod_lt _ i.pos⟩
def sn_ad {k : ℕ} (e : ℕ) (i : Fin k) : Fin k := ⟨(i.val + e) % k, Nat.mod_lt _ i.pos⟩

def sn_mix {k : ℕ} (g : ℕ) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (xor (x i) (x (sn_ri g i))) (x (sn_ri (k - g) i))

def sn_rnd {k : ℕ} (g s : ℕ) (x w cj : Fin k → Bool) (i : Fin k) : Bool :=
  xor (xor (xor (sn_mix g x i) (!(sn_mix g x (sn_ad 1 i)) && sn_mix g x (sn_ad 2 i)))
    (w (sn_ri s i))) (cj i)

def sn_pre {k r : ℕ} (col : Bool) (w name : Fin k → Bool) (c : Fin r × Fin k → Bool) :
    ℕ → Fin k → Bool
  | 0 => fun i => xor (w (sn_ri (sn_s0 col) i)) (name i)
  | t + 1 => if h : t < r then
      sn_rnd (sn_g col) (sn_sh col t) (sn_pre col w name c t) w (fun i => c (⟨t, h⟩, i))
    else sn_pre col w name c t

def sn_bits (k x : ℕ) : Fin k → Bool := fun i => x.testBit i.val

theorem sn_mix_bit (k g x : ℕ) (hx : x < 2^k) (i : Fin k) :
    (x ^^^ rotN k g x ^^^ rotN k (k - g) x).testBit i.val = sn_mix g (sn_bits k x) i := by
  simp only [Nat.testBit_xor, sn_testBit_rot hx i.isLt, sn_mix, sn_bits, sn_ri]

theorem sn_body_bit (k g s w x cj : ℕ) (hx : x < 2^k) (hw : w < 2^k) (i : Fin k) :
    (sn_body k g s w x cj).testBit i.val =
      sn_rnd g s (sn_bits k x) (sn_bits k w) (sn_bits k cj) i := by
  unfold sn_body sn_rnd
  simp only [Nat.testBit_xor, sn_testBit_step, i.isLt, decide_true, Bool.true_and,
    sn_testBit_rot hw i.isLt, sn_testBit_rot hx i.isLt,
    sn_testBit_rot hx (Nat.mod_lt (i.val + 1) i.pos),
    sn_testBit_rot hx (Nat.mod_lt (i.val + 2) i.pos), sn_mix, sn_bits, sn_ri, sn_ad]

theorem sn_st_bit (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2^k))
    (hw : w < 2^k) (hn : name < 2^k) : ∀ (t : ℕ) (i : Fin k),
    (sn_stN k r col w name c t).testBit i.val =
      sn_pre col (sn_bits k w) (sn_bits k name) (fun p => (c p.1).val.testBit p.2.val) t i := by
  intro t
  induction t with
  | zero =>
    intro i
    simp only [sn_stN, sn_pre, Nat.testBit_xor, sn_testBit_rot hw i.isLt, sn_bits, sn_ri]
  | succ t ih =>
    intro i
    by_cases h : t < r
    · simp only [sn_stN, sn_pre, h, dif_pos]
      rw [sn_body_bit k _ _ w _ _ (sn_stN_lt k r col w name c hn t) hw i]
      have e : sn_bits k (sn_stN k r col w name c t) =
          sn_pre col (sn_bits k w) (sn_bits k name) (fun p => (c p.1).val.testBit p.2.val) t :=
        funext (fun j => ih j)
      rw [e]
      rfl
    · simp only [sn_stN, sn_pre, h, dif_neg, not_false_eq_true]
      exact ih i

theorem sn_cb_mix {ι : Type} {k : ℕ} (g : ℕ) (X : Fin k → ι) (i : Fin k) :
    Cb ι 8 (fun v => sn_mix g (fun a => v (X a)) i) :=
  Cb.mono (Cb.xor (Cb.xor (Cb.var (X i)) (Cb.var (X (sn_ri g i)))) (Cb.var (X (sn_ri (k - g) i))))
    (by norm_num)

theorem sn_cb_rnd {ι : Type} {k : ℕ} (g s : ℕ) (X W C : Fin k → ι) (i : Fin k) :
    Cb ι 38 (fun v => sn_rnd g s (fun a => v (X a)) (fun a => v (W a)) (fun a => v (C a)) i) :=
  Cb.mono (Cb.xor (Cb.xor (Cb.xor (sn_cb_mix g X i)
    (Cb.and (Cb.not (sn_cb_mix g X (sn_ad 1 i))) (sn_cb_mix g X (sn_ad 2 i))))
    (Cb.var (W (sn_ri s i)))) (Cb.var (C i))) (by norm_num)

theorem sn_cmp_pre (k r : ℕ) (col : Bool) :
    Cmp (Fin k ⊕ (Fin k ⊕ (Fin r × Fin k))) (Fin k) (64 * k * (r + 1))
      (fun v => sn_pre col (fun a => v (Sum.inl a)) (fun a => v (Sum.inr (Sum.inl a)))
        (fun p => v (Sum.inr (Sum.inr p))) r) := by
  have h0 : Cmp (Fin k ⊕ (Fin k ⊕ (Fin r × Fin k))) (Fin k) (38 * k)
      (fun v => sn_pre col (fun a => v (Sum.inl a)) (fun a => v (Sum.inr (Sum.inl a)))
        (fun p => v (Sum.inr (Sum.inr p))) 0) := by
    refine Cmp.mono (Cmp.ofBits (s := 4) (fun i => ?_)) (by simp; omega)
    exact Cb.mono (Cb.xor (Cb.var (Sum.inl (sn_ri (sn_s0 col) i))) (Cb.var (Sum.inr (Sum.inl i))))
      (by norm_num)
  have hG : ∀ t < r, Cmp ((Fin k ⊕ (Fin k ⊕ (Fin r × Fin k))) ⊕ Fin k) (Fin k) (38 * k)
      (fun u i => if h : t < r then
        sn_rnd (sn_g col) (sn_sh col t) (fun a => u (Sum.inr a)) (fun a => u (Sum.inl (Sum.inl a)))
          (fun a => u (Sum.inl (Sum.inr (Sum.inr (⟨t, h⟩, a))))) i
        else u (Sum.inr i)) := by
    intro t ht
    refine Cmp.mono (Cmp.congr (Cmp.ofBits (s := 38) (fun i =>
      sn_cb_rnd (sn_g col) (sn_sh col t) (fun a => Sum.inr a) (fun a => Sum.inl (Sum.inl a))
        (fun a => Sum.inl (Sum.inr (Sum.inr (⟨t, ht⟩, a)))) i)) ?_) (by simp; omega)
    intro v i
    simp only [ht, dif_pos]
  have hch := Cmp.chain r (38 * k)
    (fun t (v : Fin k ⊕ (Fin k ⊕ (Fin r × Fin k)) → Bool) =>
      sn_pre col (fun a => v (Sum.inl a)) (fun a => v (Sum.inr (Sum.inl a)))
        (fun p => v (Sum.inr (Sum.inr p))) t)
    (fun t u i => if h : t < r then
        sn_rnd (sn_g col) (sn_sh col t) (fun a => u (Sum.inr a)) (fun a => u (Sum.inl (Sum.inl a)))
          (fun a => u (Sum.inl (Sum.inr (Sum.inr (⟨t, h⟩, a))))) i
        else u (Sum.inr i)) h0 hG
    (by
      intro t ht v
      funext i
      simp only [sn_pre, ht, dif_pos, Sum.elim_inl, Sum.elim_inr])
  have hw := Cmp.comp hch (Cmp.wire (fun i : Fin k => ((Fin.last r, i) : Fin (r + 1) × Fin k)))
  refine Cmp.mono (Cmp.congr hw ?_) ?_
  · intro v i
    simp
  · have : (r + 1) * (38 * k) + 0 = 38 * (k * (r + 1)) := by ring
    have h2 : 64 * k * (r + 1) = 64 * (k * (r + 1)) := by ring
    omega

theorem sens_cmp (k r : ℕ) (hk : 0 < k) (col : Bool) :
    ∃ F : ((Fin k ⊕ (Fin k ⊕ (Fin r × Fin k))) → Bool) → Fin k → Bool,
      Cmp (Fin k ⊕ (Fin k ⊕ (Fin r × Fin k))) (Fin k) (64 * k * (r + 1)) F ∧
      ∀ (w name : Fin (2^k)) (c : Fin r → Fin (2^k)) (i : Fin k),
        F (Sum.elim (fun i => w.val.testBit i.val) (Sum.elim (fun i => name.val.testBit i.val)
          (fun p => (c p.1).val.testBit p.2.val))) i =
          (stateN k r col w.val name.val c).testBit i.val := by
  refine ⟨_, sn_cmp_pre k r col, ?_⟩
  intro w name c i
  rw [sn_state_eq, sn_st_bit k r col w.val name.val c w.isLt name.isLt r i]
  rfl

theorem sn_idx_sub (k x s y : ℕ) (hk : 0 < k) (hs : y + s = x) :
    (x % k + k - s % k) % k = y % k := by
  have hu : s % k < k := Nat.mod_lt _ hk
  have h1 : x % k + k - s % k = x % k + (k - s % k) := by omega
  rw [h1, Nat.mod_add_mod]
  have h2 : s = k * (s / k) + s % k := (Nat.div_add_mod s k).symm
  have h3 : x + (k - s % k) = y + k * (s / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [h3, Nat.add_mul_mod_self_left]

theorem sn_idx_add (k x e y : ℕ) (h : y = x + e) : (x % k + e) % k = y % k := by
  rw [Nat.mod_add_mod, h]

theorem sn_idx_cmp (k x g y : ℕ) (hk : 0 < k) (hg : g = 1 ∨ g = 2) (h : y = x + g) :
    (x % k + k - (k - g) % k) % k = y % k := by
  subst h
  by_cases hgk : g < k
  · have h1 : (k - g) % k = k - g := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have h2 : x % k + k - (k - g) = x % k + g := by omega
    rw [h2, Nat.mod_add_mod]
  · have h1 : k - g = 0 := by omega
    rw [h1, Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod]
    have hk' : k = 1 ∨ (k = 2 ∧ g = 2) := by omega
    rcases hk' with rfl | ⟨rfl, rfl⟩
    · simp [Nat.mod_one]
    · simp

theorem sn_mix_loc {k : ℕ} (g : ℕ) (hg : g = 1 ∨ g = 2) (x x' : Fin k → Bool) (a L : ℕ)
    (hgL : g ≤ L)
    (hx : ∀ L', L - g ≤ L' → L' ≤ L + g → ∀ j : Fin k, j.val = (a + L') % k → x j = x' j)
    (i : Fin k) (hi : i.val = (a + L) % k) : sn_mix g x i = sn_mix g x' i := by
  unfold sn_mix
  have e1 := hx L (by omega) (by omega) i hi
  have e2 := hx (L - g) (by omega) (by omega) (sn_ri g i) (by
    show (i.val + k - g % k) % k = _
    rw [hi]; exact sn_idx_sub k _ g _ i.pos (by omega))
  have e3 := hx (L + g) (by omega) (by omega) (sn_ri (k - g) i) (by
    show (i.val + k - (k - g) % k) % k = _
    rw [hi]; exact sn_idx_cmp k _ g _ i.pos hg (by omega))
  rw [e1, e2, e3]

theorem sn_rnd_loc {k : ℕ} (g s : ℕ) (hg : g = 1 ∨ g = 2) (x x' w w' cj : Fin k → Bool)
    (a L E : ℕ) (hgL : g ≤ L) (hsL : s ≤ L) (hsE : L - s ≤ E)
    (hx : ∀ L', L - g ≤ L' → L' ≤ L + 2 + g → ∀ j : Fin k, j.val = (a + L') % k → x j = x' j)
    (hw : ∀ d, d ≤ E → ∀ q : Fin k, q.val = (a + d) % k → w q = w' q)
    (i : Fin k) (hi : i.val = (a + L) % k) :
    sn_rnd g s x w cj i = sn_rnd g s x' w' cj i := by
  unfold sn_rnd
  have m0 := sn_mix_loc g hg x x' a L hgL
    (fun L' h1 h2 => hx L' h1 (by omega)) i hi
  have m1 := sn_mix_loc g hg x x' a (L + 1) (by omega)
    (fun L' h1 h2 => hx L' (by omega) (by omega)) (sn_ad 1 i) (by
      show (i.val + 1) % k = _
      rw [hi]; exact sn_idx_add k _ 1 _ (by omega))
  have m2 := sn_mix_loc g hg x x' a (L + 2) (by omega)
    (fun L' h1 h2 => hx L' (by omega) (by omega)) (sn_ad 2 i) (by
      show (i.val + 2) % k = _
      rw [hi]; exact sn_idx_add k _ 2 _ (by omega))
  have ew := hw (L - s) hsE (sn_ri s i) (by
    show (i.val + k - s % k) % k = _
    rw [hi]; exact sn_idx_sub k _ s _ i.pos (by omega))
  rw [m0, m1, m2, ew]

theorem sn_loc_f {k r : ℕ} (w w' name : Fin k → Bool) (c : Fin r × Fin k → Bool) :
    ∀ (t a L E : ℕ), t + 1 ≤ L → 2 * t ≤ L + 2 → L + 3 * t ≤ E + 1 →
      (∀ d, d ≤ E → ∀ q : Fin k, q.val = (a + d) % k → w q = w' q) →
      ∀ i : Fin k, i.val = (a + L) % k →
        sn_pre false w name c t i = sn_pre false w' name c t i := by
  intro t
  induction t with
  | zero =>
    intro a L E h1 h2 h3 hw i hi
    simp only [sn_pre]
    have ew := hw (L - 1) (by omega) (sn_ri (sn_s0 false) i) (by
      show (i.val + k - 1 % k) % k = _
      rw [hi]; exact sn_idx_sub k _ 1 _ i.pos (by omega))
    rw [ew]
  | succ t ih =>
    intro a L E h1 h2 h3 hw i hi
    by_cases h : t < r
    · simp only [sn_pre, h, dif_pos]
      exact sn_rnd_loc 1 (2 * t) (Or.inl rfl) _ _ w w' _ a L E (by omega) (by omega) (by omega)
        (fun L' l1 l2 j hj => ih a L' E (by omega) (by omega) (by omega) hw j hj) hw i hi
    · simp only [sn_pre, h, dif_neg, not_false_eq_true]
      exact ih a L E (by omega) (by omega) (by omega) hw i hi

theorem sn_loc_t {k r : ℕ} (w w' name : Fin k → Bool) (c : Fin r × Fin k → Bool) :
    ∀ (t a L E : ℕ), 2 * t + 3 ≤ L → 3 * t + 1 ≤ L → L + 4 * t ≤ E + 3 →
      (∀ d, d ≤ E → ∀ q : Fin k, q.val = (a + d) % k → w q = w' q) →
      ∀ i : Fin k, i.val = (a + L) % k →
        sn_pre true w name c t i = sn_pre true w' name c t i := by
  intro t
  induction t with
  | zero =>
    intro a L E h1 h2 h3 hw i hi
    simp only [sn_pre]
    have ew := hw (L - 3) (by omega) (sn_ri (sn_s0 true) i) (by
      show (i.val + k - 3 % k) % k = _
      rw [hi]; exact sn_idx_sub k _ 3 _ i.pos (by omega))
    rw [ew]
  | succ t ih =>
    intro a L E h1 h2 h3 hw i hi
    by_cases h : t < r
    · simp only [sn_pre, h, dif_pos]
      exact sn_rnd_loc 2 (3 * (t + 1) + 1) (Or.inr rfl) _ _ w w' _ a L E (by omega) (by omega)
        (by omega)
        (fun L' l1 l2 j hj => ih a L' E (by omega) (by omega) (by omega) hw j hj) hw i hi
    · simp only [sn_pre, h, dif_neg, not_false_eq_true]
      exact ih a L E (by omega) (by omega) (by omega) hw i hi

theorem sens_local (k r : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (col : Bool) (w w' name : ℕ)
    (c : Fin r → Fin (2^k)) (p : Fin k) (hw : w < 2^k) (hw' : w' < 2^k) (hn : name < 2^k)
    (h : ∀ h : ℕ, h ≤ (if col then 7*r-2 else 5*r-3) →
      w.testBit ((p.val+h)%k) = w'.testBit ((p.val+h)%k)) :
    (stateN k r col w name c).testBit ((p.val + (if col then 3*r+1 else 2*r-2)) % k) =
      (stateN k r col w' name c).testBit ((p.val + (if col then 3*r+1 else 2*r-2)) % k) := by
  rw [sn_state_eq, sn_state_eq]
  cases col
  · simp only [Bool.false_eq_true, if_false] at h ⊢
    have b1 := sn_st_bit k r false w name c hw hn r ⟨(p.val + (2*r-2)) % k, Nat.mod_lt _ hk⟩
    have b2 := sn_st_bit k r false w' name c hw' hn r ⟨(p.val + (2*r-2)) % k, Nat.mod_lt _ hk⟩
    simp only at b1 b2
    rw [b1, b2]
    exact sn_loc_f _ _ _ _ r p.val (2*r-2) (5*r-3) (by omega) (by omega) (by omega)
      (fun d hd q hq => by
        show w.testBit q.val = w'.testBit q.val
        rw [hq]; exact h d hd) _ rfl
  · simp only [if_true] at h ⊢
    have b1 := sn_st_bit k r true w name c hw hn r ⟨(p.val + (3*r+1)) % k, Nat.mod_lt _ hk⟩
    have b2 := sn_st_bit k r true w' name c hw' hn r ⟨(p.val + (3*r+1)) % k, Nat.mod_lt _ hk⟩
    simp only at b1 b2
    rw [b1, b2]
    exact sn_loc_t _ _ _ _ r p.val (3*r+1) (7*r-2) (by omega) (by omega) (by omega)
      (fun d hd q hq => by
        show w.testBit q.val = w'.testBit q.val
        rw [hq]; exact h d hd) _ rfl

theorem sn_report_eq (k r m : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (w : ℕ) :
    reportN k r m nr nc cr cc A B w = (List.finRange k).foldl (fun z p =>
      (z ^^^ cond ((stateN k r false w nr.val cr).testBit ((p.val + (2*r-2)) % k)) (A p).val 0) ^^^
        cond ((stateN k r true w nc.val cc).testBit ((p.val + (3*r+1)) % k)) (B p).val 0) 0 := by
  unfold reportN delayN
  simp only [sn_ite_any, sn_ite_T, sn_ite_F, Bool.cond_false, Bool.cond_true]

theorem sn_cond_lt (m : ℕ) (c : Bool) (x : ℕ) (hx : x < 2^m) : cond c x 0 < 2^m := by
  cases c
  · exact Nat.two_pow_pos m
  · exact hx

theorem reportN_lt (k r m : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (w : ℕ) : reportN k r m nr nc cr cc A B w < 2^m := by
  rw [sn_report_eq]
  have : ∀ (l : List (Fin k)) (z : ℕ), z < 2^m → l.foldl (fun z p =>
      (z ^^^ cond ((stateN k r false w nr.val cr).testBit ((p.val + (2*r-2)) % k)) (A p).val 0) ^^^
        cond ((stateN k r true w nc.val cc).testBit ((p.val + (3*r+1)) % k)) (B p).val 0) z
      < 2^m := by
    intro l
    induction l with
    | nil => intro z hz; exact hz
    | cons p l ih =>
      intro z hz
      simp only [List.foldl_cons]
      exact ih _ (sn_xor_lt (sn_xor_lt hz (sn_cond_lt m _ _ (A p).isLt))
        (sn_cond_lt m _ _ (B p).isLt))
  exact this _ 0 (Nat.two_pow_pos m)

theorem vecN_inj (m x y : ℕ) (hx : x < 2^m) (hy : y < 2^m) (h : vecN m x = vecN m y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · have e := congrFun h ⟨i, hi⟩
    simp only [vecN] at e
    cases hxb : x.testBit i <;> cases hyb : y.testBit i <;> simp [hxb, hyb] at e ⊢
  · have hpow : 2^m ≤ 2^i := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    rw [Nat.testBit_lt_two_pow (hx.trans_le hpow), Nat.testBit_lt_two_pow (hy.trans_le hpow)]

theorem sn_vec_xor (m a b : ℕ) : vecN m (a ^^^ b) = vecN m a + vecN m b := by
  funext i
  simp only [vecN, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i.val <;> cases b.testBit i.val <;> decide

theorem sn_vec_zero (m : ℕ) : vecN m 0 = 0 := by
  funext i
  simp [vecN]

theorem sn_vec_cond (m : ℕ) (c : Bool) (x : ℕ) : vecN m (cond c x 0) = b2z c • vecN m x := by
  cases c
  · simp [b2z, sn_vec_zero]
  · simp [b2z]

theorem report_vec (k r m : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (w : ℕ) :
    vecN m (reportN k r m nr nc cr cc A B w) = ∑ p : Fin k,
      (b2z ((stateN k r false w nr.val cr).testBit ((p.val + (2*r-2)) % k)) • vecN m (A p).val +
       b2z ((stateN k r true w nc.val cc).testBit ((p.val + (3*r+1)) % k)) • vecN m (B p).val) := by
  rw [sn_report_eq]
  have : ∀ (l : List (Fin k)) (z : ℕ), vecN m (l.foldl (fun z p =>
      (z ^^^ cond ((stateN k r false w nr.val cr).testBit ((p.val + (2*r-2)) % k)) (A p).val 0) ^^^
        cond ((stateN k r true w nc.val cc).testBit ((p.val + (3*r+1)) % k)) (B p).val 0) z) =
      vecN m z + (l.map (fun p =>
        b2z ((stateN k r false w nr.val cr).testBit ((p.val + (2*r-2)) % k)) • vecN m (A p).val +
        b2z ((stateN k r true w nc.val cc).testBit ((p.val + (3*r+1)) % k)) • vecN m (B p).val)).sum := by
    intro l
    induction l with
    | nil => intro z; simp
    | cons p l ih =>
      intro z
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, sn_vec_xor, sn_vec_xor, sn_vec_cond, sn_vec_cond]
      abel
  rw [this, sn_vec_zero, zero_add, Fin.sum_univ_def]

theorem pb_mem_take {k : ℕ} (ord : Fin k → Fin k) (i : ℕ) (p : Fin k) :
    p ∈ (List.ofFn ord).take i ↔ ∃ i' : Fin k, i'.val < i ∧ ord i' = p := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨n, hn, h⟩
    simp only [List.length_take, List.length_ofFn] at hn
    rw [List.getElem_take, List.getElem_ofFn] at h
    exact ⟨⟨n, by omega⟩, by simp; omega, h⟩
  · rintro ⟨i', h1, h2⟩
    refine ⟨i'.val, by simp; exact h1, ?_⟩
    rw [List.getElem_take, List.getElem_ofFn]
    exact h2

theorem pb_mem_drop {k : ℕ} (ord : Fin k → Fin k) (i : ℕ) (p : Fin k) :
    p ∈ (List.ofFn ord).drop i ↔ ∃ i' : Fin k, i ≤ i'.val ∧ ord i' = p := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨n, hn, h⟩
    simp only [List.length_drop, List.length_ofFn] at hn
    rw [List.getElem_drop, List.getElem_ofFn] at h
    exact ⟨⟨i + n, by omega⟩, Nat.le_add_right _ _, h⟩
  · rintro ⟨i', h1, h2⟩
    refine ⟨i'.val - i, by simp; omega, ?_⟩
    have hlt : i + (i'.val - i) < k := by omega
    rw [List.getElem_drop, List.getElem_ofFn]
    have : (⟨i + (i'.val - i), hlt⟩ : Fin k) = i' := Fin.ext (by simp; omega)
    rw [this]; exact h2

theorem pb_vec (m x : ℕ) (inst : ∀ P : Prop, Decidable P) :
    (fun i : Fin m => @ite (ZMod 2) (x.testBit i.val = true) (inst _) 1 0) = vecN m x := by
  funext i; unfold vecN; congr

theorem pb_fr {m : ℕ} (S S' : Submodule (ZMod 2) (Fin m → ZMod 2)) (h : S = S') :
    Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) S' := by rw [h]

theorem pb_exfin (n : ℕ) (P : ℕ → Prop) : (∃ h : Fin (n + 1), P h.val) ↔ ∃ h : ℕ, h ≤ n ∧ P h := by
  constructor
  · rintro ⟨h, hh⟩; exact ⟨h.val, by omega, hh⟩
  · rintro ⟨h, h1, h2⟩; exact ⟨⟨h, by omega⟩, h2⟩

theorem pass_iff (k r m b : ℕ) (hk : 0 < k) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) :
    passP k r m b A B ord ↔ Function.Bijective ord ∧ ∀ i : Fin k,
      ((poolLo k r m A B ord i.val ∩ poolHi k r m A B ord i.val) ∪
        scopeS k r m A B (ord i)).card +
        Module.finrank (ZMod 2) (spanLo k m A B ord i.val ⊓ spanHi k m A B ord i.val :
          Submodule (ZMod 2) (Fin m → ZMod 2)) ≤ b := by
  unfold passP
  dsimp only
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  refine Iff.of_eq (congrArg₂ (fun a c => a + c ≤ b) (congrArg Finset.card ?_) (pb_fr _ _ ?_))
  · ext z
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and, List.mem_toFinset, pb_mem_take, pb_mem_drop, poolLo, poolHi,
      scopeS, Bool.false_eq_true, ite_false, ite_true]
    have hE : ∀ (n a : ℕ), (∃ h : Fin (n+1), (a + h.val) % k = z.val) ↔
        ∃ h, h ≤ n ∧ (a + h) % k = z.val := fun n a => pb_exfin n (fun h => (a + h) % k = z.val)
    have hQ : ∀ (c : Fin k → Prop) (Q : Fin k → Prop),
        (∃ a, (∃ i', c i' ∧ ord i' = a) ∧ Q a) ↔ ∃ i', c i' ∧ Q (ord i') := by
      intro c Q
      constructor
      · rintro ⟨a, ⟨i', h1, rfl⟩, h2⟩; exact ⟨i', h1, h2⟩
      · rintro ⟨i', h1, h2⟩; exact ⟨_, ⟨i', h1, rfl⟩, h2⟩
    simp only [hE]
    rw [hQ (fun i' => i'.val < i.val), hQ (fun i' => i.val ≤ i'.val)]
    have hf : ¬ (false = true) := Bool.false_ne_true
    simp only [if_neg hf, if_pos trivial]
  · unfold spanLo spanHi
    simp only [pb_vec]
    congr 2
    · ext v
      simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_flatMap, pb_mem_take,
        List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨a, ⟨i', h1, rfl⟩, h2⟩; exact ⟨i', h1, h2⟩
      · rintro ⟨i', h1, h2⟩; exact ⟨_, ⟨i', h1, rfl⟩, h2⟩
    · ext v
      simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_flatMap, pb_mem_drop,
        List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨a, ⟨i', h1, rfl⟩, h2⟩; exact ⟨i', h1, h2⟩
      · rintro ⟨i', h1, h2⟩; exact ⟨_, ⟨i', h1, rfl⟩, h2⟩

def pbA {k r m : ℕ} (col : Bool) (p : Fin k) (c : Fin m) : Dat k r m :=
  Sum.inr (Sum.inr (Sum.inl (if col then Sum.inr (p, c) else Sum.inl (p, c))))

def pbO {k r m : ℕ} (i t : Fin k) : Dat k r m := Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, t))))

def pbOrdEq {k r m : ℕ} (v : Dat k r m → Bool) (i p : Fin k) : Bool :=
  decide (∀ t : Fin k, (if p.val.testBit t.val then v (pbO i t) else !v (pbO i t)) = true)

def pbNz {k r m : ℕ} (v : Dat k r m → Bool) (col : Bool) (p : Fin k) : Bool :=
  decide (∃ c : Fin m, v (pbA col p c) = true)

def pbRc (k n : ℕ) (p z : Fin k) : Bool :=
  decide (∃ h : Fin (n + 1), (p.val + h.val) % k = z.val)

def pbSc {k r m : ℕ} (v : Dat k r m → Bool) (p z : Fin k) : Bool :=
  (pbNz v false p && pbRc k (5*r-3) p z) || (pbNz v true p && pbRc k (7*r-2) p z)

def pbScAt {k r m : ℕ} (v : Dat k r m → Bool) (i z : Fin k) : Bool :=
  decide (∃ p : Fin k, (pbOrdEq v i p && pbSc v p z) = true)

def pbLo {k r m : ℕ} (v : Dat k r m → Bool) (i : ℕ) (z : Fin k) : Bool :=
  decide (∃ i' : Fin k, (decide (i'.val < i) && pbScAt v i' z) = true)

def pbHi {k r m : ℕ} (v : Dat k r m → Bool) (i : ℕ) (z : Fin k) : Bool :=
  decide (∃ i' : Fin k, (decide (i ≤ i'.val) && pbScAt v i' z) = true)

def pbFlag {k r m : ℕ} (v : Dat k r m → Bool) (i z : Fin k) : Bool :=
  (pbLo v i.val z && pbHi v i.val z) || pbScAt v i z

def pbRow {k r m : ℕ} (v : Dat k r m → Bool) (col : Bool) (i : Fin k) (c : Fin m) : Bool :=
  decide (∃ p : Fin k, (pbOrdEq v i p && v (pbA col p c)) = true)

def pbMat {k r m : ℕ} (μ : Fin k → Bool) (v : Dat k r m → Bool) :
    Fin (k + k + m + 1) × Fin (k + k + m + 1) → Bool := fun q =>
  if h1 : q.1.val < k then
    (if h2 : q.2.val < m then μ ⟨q.1.val, h1⟩ && pbRow v false ⟨q.1.val, h1⟩ ⟨q.2.val, h2⟩
     else false)
  else if h3 : q.1.val < k + k then
    (if h2 : q.2.val < m then
      μ ⟨q.1.val - k, by omega⟩ && pbRow v true ⟨q.1.val - k, by omega⟩ ⟨q.2.val, h2⟩
     else false)
  else false

def pbH {k m : ℕ} (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (μ : Fin k → Bool) :
    Fin (k + k) → V m := fun j =>
  if h : j.val < k then (if μ ⟨j.val, h⟩ = true then vecN m (A (ord ⟨j.val, h⟩)).val else 0)
  else (if μ ⟨j.val - k, by omega⟩ = true then vecN m (B (ord ⟨j.val - k, by omega⟩)).val else 0)

def pbSpan {k m : ℕ} (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (μ : Fin k → Bool) :
    Submodule (ZMod 2) (Fin m → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ i' : Fin k, μ i' = true ∧
    (v = vecN m (A (ord i')).val ∨ v = vecN m (B (ord i')).val)}

def pbcAt (k m : ℕ) : ℕ := k * (2 * k + 2 * m + 10) + 1
def pbcLo (k m : ℕ) : ℕ := k * (pbcAt k m + 3) + 1
def pbcFlag (k m : ℕ) : ℕ := pbcLo k m + pbcLo k m + 1 + pbcAt k m + 1
def pbcRow (k : ℕ) : ℕ := k * (2 * k + 3) + 1
def pbcMat (k m : ℕ) : ℕ := (k + k + m + 1) * (k + k + m + 1) * (pbcRow k + 2)
def pbcRk (k m : ℕ) : ℕ := pbcMat k m + gjCost (k + k + m + 1) + 0 + (m + 1) * ((m + 1) * 6)
def pbcCut (k m : ℕ) : ℕ :=
  (k * pbcFlag k m + (k + 1) * ((k + 1) * 6)) + (pbcRk k m + (pbcRk k m + pbcRk k m)) +
    ((k + 1) * ((m + 1) * ((m + 1) * (m + 1))) * 6 + 1)
def pbcBij (k : ℕ) : ℕ := k * (k * (2 * k + 2) + 1 + 1) + 1
def pbcTot (k m : ℕ) : ℕ := pbcBij k + (k * (pbcCut k m + 1) + 1) + 1

theorem pb_or {ι : Type} {n s : ℕ} {φ : Fin n → (ι → Bool) → Bool} (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (n * (s + 1) + 1) (fun v => decide (∃ i, φ i v = true)) := by
  have := Cb.bigOr h
  rw [Fintype.card_fin] at this
  exact this.congr (fun v => decide_eq_decide.mpr Iff.rfl)

theorem pb_and {ι : Type} {n s : ℕ} {φ : Fin n → (ι → Bool) → Bool} (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (n * (s + 1) + 1) (fun v => decide (∀ i, φ i v = true)) := by
  have := Cb.bigAnd h
  rw [Fintype.card_fin] at this
  exact this.congr (fun v => decide_eq_decide.mpr Iff.rfl)

theorem pb_ordEq_cb {k r m : ℕ} (i p : Fin k) :
    Cb (Dat k r m) (2 * k + 1) (fun v => pbOrdEq v i p) := by
  have h : ∀ t : Fin k, Cb (Dat k r m) 1
      (fun v => if p.val.testBit t.val then v (pbO i t) else !v (pbO i t)) := by
    intro t
    by_cases hp : p.val.testBit t.val = true
    · exact ((Cb.var (pbO i t)).mono (by omega)).congr (fun v => by simp [hp])
    · exact ((Cb.not (Cb.var (pbO i t)))).congr (fun v => by simp [hp])
  exact (pb_and h).mono (by omega)

theorem pb_nz_cb {k r m : ℕ} (col : Bool) (p : Fin k) :
    Cb (Dat k r m) (m + 1) (fun v => pbNz v col p) := by
  have h : ∀ c : Fin m, Cb (Dat k r m) 0 (fun v => v (pbA col p c)) := fun c => Cb.var _
  exact (pb_or h).mono (by omega)

theorem pb_sc_cb {k r m : ℕ} (p z : Fin k) :
    Cb (Dat k r m) (2 * m + 7) (fun v => pbSc v p z) :=
  (Cb.or (Cb.and (pb_nz_cb false p) (Cb.const (pbRc k (5*r-3) p z)))
    (Cb.and (pb_nz_cb true p) (Cb.const (pbRc k (7*r-2) p z)))).mono (by omega)

theorem pb_scAt_cb {k r m : ℕ} (i z : Fin k) :
    Cb (Dat k r m) (pbcAt k m) (fun v => pbScAt v i z) := by
  have h : ∀ p : Fin k, Cb (Dat k r m) (2 * k + 2 * m + 9)
      (fun v => pbOrdEq v i p && pbSc v p z) :=
    fun p => (Cb.and (pb_ordEq_cb i p) (pb_sc_cb p z)).mono (by omega)
  exact (pb_or h).mono (by unfold pbcAt; exact Nat.le_of_eq (by ring))

theorem pb_lo_cb {k r m : ℕ} (i : ℕ) (z : Fin k) :
    Cb (Dat k r m) (pbcLo k m) (fun v => pbLo v i z) := by
  have h : ∀ i' : Fin k, Cb (Dat k r m) (pbcAt k m + 2)
      (fun v => decide (i'.val < i) && pbScAt v i' z) :=
    fun i' => (Cb.and (Cb.const _) (pb_scAt_cb i' z)).mono (by omega)
  exact (pb_or h).mono (by unfold pbcLo; exact Nat.le_of_eq (by ring))

theorem pb_hi_cb {k r m : ℕ} (i : ℕ) (z : Fin k) :
    Cb (Dat k r m) (pbcLo k m) (fun v => pbHi v i z) := by
  have h : ∀ i' : Fin k, Cb (Dat k r m) (pbcAt k m + 2)
      (fun v => decide (i ≤ i'.val) && pbScAt v i' z) :=
    fun i' => (Cb.and (Cb.const _) (pb_scAt_cb i' z)).mono (by omega)
  exact (pb_or h).mono (by unfold pbcLo; exact Nat.le_of_eq (by ring))

theorem pb_flag_cb {k r m : ℕ} (i z : Fin k) :
    Cb (Dat k r m) (pbcFlag k m) (fun v => pbFlag v i z) :=
  (Cb.or (Cb.and (pb_lo_cb i.val z) (pb_hi_cb i.val z)) (pb_scAt_cb i z)).mono
    (by unfold pbcFlag; omega)

theorem pb_row_cb {k r m : ℕ} (col : Bool) (i : Fin k) (c : Fin m) :
    Cb (Dat k r m) (pbcRow k) (fun v => pbRow v col i c) := by
  have h : ∀ p : Fin k, Cb (Dat k r m) (2 * k + 2)
      (fun v => pbOrdEq v i p && v (pbA col p c)) :=
    fun p => (Cb.and (pb_ordEq_cb i p) (Cb.var _)).mono (by omega)
  exact (pb_or h).mono (by unfold pbcRow; exact Nat.le_of_eq (by ring))

theorem pb_mat_cmp {k r m : ℕ} (μ : Fin k → Bool) :
    Cmp (Dat k r m) (Fin (k + k + m + 1) × Fin (k + k + m + 1)) (pbcMat k m) (pbMat μ) := by
  have h : ∀ q : Fin (k + k + m + 1) × Fin (k + k + m + 1),
      Cb (Dat k r m) (pbcRow k + 2) (fun v => pbMat μ v q) := by
    intro q
    by_cases h1 : q.1.val < k
    · by_cases h2 : q.2.val < m
      · exact ((Cb.and (Cb.const (μ ⟨q.1.val, h1⟩))
          (pb_row_cb false ⟨q.1.val, h1⟩ ⟨q.2.val, h2⟩)).mono (by omega)).congr
          (fun v => by simp [pbMat, h1, h2])
      · exact ((Cb.const false).mono (by omega)).congr (fun v => by simp [pbMat, h1, h2])
    · by_cases h3 : q.1.val < k + k
      · by_cases h2 : q.2.val < m
        · exact ((Cb.and (Cb.const (μ ⟨q.1.val - k, by omega⟩))
            (pb_row_cb true ⟨q.1.val - k, by omega⟩ ⟨q.2.val, h2⟩)).mono (by omega)).congr
            (fun v => by simp [pbMat, h1, h2, h3])
        · exact ((Cb.const false).mono (by omega)).congr
            (fun v => by simp [pbMat, h1, h2, h3])
      · exact ((Cb.const false).mono (by omega)).congr (fun v => by simp [pbMat, h1, h3])
  have := Cmp.ofBits h
  rw [Fintype.card_prod, Fintype.card_fin] at this
  exact this

theorem pb_rk_cmp {k r m : ℕ} (μ : Fin k → Bool) :
    Cmp (Dat k r m) (Fin (m + 1) × Fin (m + 1)) (pbcRk k m)
      (fun v p => decide (cnt (pv (gj (k + k + m + 1) (pbMat μ v))) p.1.val = p.2.val)) := by
  have hR := Cmp.comp (pb_mat_cmp (r := r) μ) (cmp_gj (k + k + m + 1))
  have hP := Cmp.comp hR (Cmp.wire (ι := Fin (k + k + m + 1) × Fin (k + k + m + 1))
    (fun p : Fin m => (cl (k + k) p, cl (k + k) p)))
  have hC := Cmp.comp hP (cmp_counter m m)
  exact hC

theorem pb_cut_cb {k r m : ℕ} (b : ℕ) (i : Fin k) :
    Cb (Dat k r m) (pbcCut k m) (fun v => decide (∃ q : Fin (k+1) × Fin (m+1) × Fin (m+1) × Fin (m+1),
      cnt (pbFlag v i) k = q.1.val ∧
      cnt (pv (gj (k + k + m + 1) (pbMat (fun i' => decide (i'.val < i.val)) v))) m = q.2.1.val ∧
      cnt (pv (gj (k + k + m + 1) (pbMat (fun i' => decide (i.val ≤ i'.val)) v))) m = q.2.2.1.val ∧
      cnt (pv (gj (k + k + m + 1) (pbMat (fun _ => true) v))) m = q.2.2.2.val ∧
      q.1.val + q.2.1.val + q.2.2.1.val ≤ b + q.2.2.2.val)) := by
  have hF : Cmp (Dat k r m) (Fin k) (k * pbcFlag k m) (fun v z => pbFlag v i z) := by
    have := Cmp.ofBits (ι := Dat k r m) (κ := Fin k) (F := fun v z => pbFlag v i z)
      (fun z => pb_flag_cb i z)
    rwa [Fintype.card_fin] at this
  have hFc := Cmp.comp hF (cmp_counter k k)
  have hK := Cmp.pair hFc (Cmp.pair (pb_rk_cmp (r := r) (fun i' => decide (i'.val < i.val)))
    (Cmp.pair (pb_rk_cmp (r := r) (fun i' => decide (i.val ≤ i'.val)))
      (pb_rk_cmp (r := r) (fun _ => true))))
  have hφ : ∀ q : Fin (k+1) × Fin (m+1) × Fin (m+1) × Fin (m+1),
      Cb ((Fin (k + 1) × Fin (k + 1)) ⊕ ((Fin (m + 1) × Fin (m + 1)) ⊕
        ((Fin (m + 1) × Fin (m + 1)) ⊕ (Fin (m + 1) × Fin (m + 1))))) 5
        (fun w => w (Sum.inl (Fin.last k, q.1)) && w (Sum.inr (Sum.inl (Fin.last m, q.2.1))) &&
          w (Sum.inr (Sum.inr (Sum.inl (Fin.last m, q.2.2.1)))) &&
          w (Sum.inr (Sum.inr (Sum.inr (Fin.last m, q.2.2.2)))) &&
          decide (q.1.val + q.2.1.val + q.2.2.1.val ≤ b + q.2.2.2.val)) :=
    fun q => (Cb.and (Cb.and (Cb.and (Cb.and (Cb.var _) (Cb.var _)) (Cb.var _)) (Cb.var _))
      (Cb.const _)).mono (by omega)
  have hO := Cb.bigOr hφ
  have hc : Fintype.card (Fin (k+1) × Fin (m+1) × Fin (m+1) × Fin (m+1)) =
      (k + 1) * ((m + 1) * ((m + 1) * (m + 1))) := by simp
  rw [hc] at hO
  refine ((Cb.comp hK hO).mono (by unfold pbcCut; omega)).congr ?_
  intro v
  refine decide_eq_decide.mpr (exists_congr fun q => ?_)
  simp only [Sum.elim_inl, Sum.elim_inr, Bool.and_eq_true, decide_eq_true_eq, Fin.val_last]
  tauto

theorem pb_bij_cb {k r m : ℕ} :
    Cb (Dat k r m) (pbcBij k)
      (fun v => decide (∀ z : Fin k, decide (∃ i : Fin k, pbOrdEq v i z = true) = true)) := by
  have h : ∀ z : Fin k, Cb (Dat k r m) (k * (2 * k + 2) + 1)
      (fun v => decide (∃ i : Fin k, pbOrdEq v i z = true)) :=
    fun z => pb_or (fun i => pb_ordEq_cb i z)
  exact (pb_and h).mono (by unfold pbcBij; omega)

theorem pb_enc_O {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i t : Fin k) :
    encD nr nc cr cc A B ord y (pbO i t) = (ord i).val.testBit t.val := rfl

theorem pb_enc_A {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (col : Bool)
    (p : Fin k) (c : Fin m) :
    encD nr nc cr cc A B ord y (pbA col p c) =
      (if col then B p else A p).val.testBit c.val := by
  cases col <;> rfl

theorem pb_bits_eq (n x p : ℕ) (hx : x < 2^n) (hp : p < 2^n)
    (h : ∀ t : Fin n, x.testBit t.val = p.testBit t.val) : x = p := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · exact h ⟨j, hj⟩
  · have h2 : 2^n ≤ 2^j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem pb_ordEq_enc {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i p : Fin k) :
    pbOrdEq (encD nr nc cr cc A B ord y) i p = decide (ord i = p) := by
  unfold pbOrdEq
  refine decide_eq_decide.mpr ?_
  simp only [pb_enc_O]
  constructor
  · intro h
    apply Fin.ext
    have hk : k < 2^k := Nat.lt_two_pow_self
    refine pb_bits_eq k _ _ (by omega) (by omega) ?_
    intro t
    have := h t
    by_cases hp : p.val.testBit t.val = true
    · rw [if_pos hp] at this; rw [this, hp]
    · rw [if_neg hp] at this
      simp only [Bool.not_eq_true] at hp
      rw [hp]; simpa using this
  · rintro rfl t
    by_cases hp : (ord i).val.testBit t.val = true
    · rw [if_pos hp]; exact hp
    · rw [if_neg hp]; simpa using hp

theorem pb_nz_enc {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (col : Bool) (p : Fin k) :
    pbNz (encD nr nc cr cc A B ord y) col p = decide ((if col then B p else A p).val ≠ 0) := by
  unfold pbNz
  refine decide_eq_decide.mpr ?_
  simp only [pb_enc_A]
  constructor
  · rintro ⟨c, hc⟩ h0
    rw [h0] at hc
    simp at hc
  · intro h
    by_contra hn
    apply h
    refine pb_bits_eq m _ 0 (if col then B p else A p).isLt (by positivity) ?_
    intro t
    rw [Nat.zero_testBit]
    by_contra ht
    exact hn ⟨t, by simpa using ht⟩

theorem pb_rc_iff (k n : ℕ) (p z : Fin k) :
    pbRc k n p z = true ↔ ∃ h : ℕ, h ≤ n ∧ (p.val + h) % k = z.val := by
  unfold pbRc
  rw [decide_eq_true_eq]
  exact pb_exfin n (fun h => (p.val + h) % k = z.val)

theorem pb_sc_enc {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (p z : Fin k) :
    pbSc (encD nr nc cr cc A B ord y) p z = true ↔ z ∈ scopeS k r m A B p := by
  unfold pbSc scopeS
  simp only [pb_nz_enc, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, pb_rc_iff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  simp

theorem pb_scAt_enc {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i z : Fin k) :
    pbScAt (encD nr nc cr cc A B ord y) i z = true ↔ z ∈ scopeS k r m A B (ord i) := by
  unfold pbScAt
  simp only [decide_eq_true_eq, Bool.and_eq_true, pb_ordEq_enc, pb_sc_enc]
  constructor
  · rintro ⟨p, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

theorem pb_lo_enc {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : ℕ) (z : Fin k) :
    pbLo (encD nr nc cr cc A B ord y) i z = true ↔ z ∈ poolLo k r m A B ord i := by
  unfold pbLo poolLo
  simp only [decide_eq_true_eq, Bool.and_eq_true, pb_scAt_enc, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem pb_hi_enc {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : ℕ) (z : Fin k) :
    pbHi (encD nr nc cr cc A B ord y) i z = true ↔ z ∈ poolHi k r m A B ord i := by
  unfold pbHi poolHi
  simp only [decide_eq_true_eq, Bool.and_eq_true, pb_scAt_enc, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem pb_cnt_flag {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : Fin k) :
    cnt (pbFlag (encD nr nc cr cc A B ord y) i) k =
      ((poolLo k r m A B ord i.val ∩ poolHi k r m A B ord i.val) ∪
        scopeS k r m A B (ord i)).card := by
  unfold cnt
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, z.isLt, pbFlag, Bool.or_eq_true,
    Bool.and_eq_true, pb_lo_enc, pb_hi_enc, pb_scAt_enc, Finset.mem_union, Finset.mem_inter]

theorem pb_row_enc {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (col : Bool)
    (i : Fin k) (c : Fin m) :
    pbRow (encD nr nc cr cc A B ord y) col i c =
      (if col then B (ord i) else A (ord i)).val.testBit c.val := by
  unfold pbRow
  simp only [pb_ordEq_enc, pb_enc_A, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h : (if col then B (ord i) else A (ord i)).val.testBit c.val = true
  · rw [h, decide_eq_true_eq]; exact ⟨_, rfl, h⟩
  · simp only [Bool.not_eq_true] at h
    rw [h, decide_eq_false_iff_not]
    rintro ⟨p, rfl, hp⟩
    rw [h] at hp; exact Bool.false_ne_true hp

theorem pb_vec_bit (m x : ℕ) (c : Fin m) : decide (vecN m x c ≠ 0) = x.testBit c.val := by
  unfold vecN
  by_cases h : x.testBit c.val = true <;> simp [h]

theorem pb_vec_bit' (m x : ℕ) (c : Fin m) : (!decide (vecN m x c = 0)) = x.testBit c.val := by
  unfold vecN
  by_cases h : x.testBit c.val = true <;> simp [h]

theorem pb_mat_enc {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (μ : Fin k → Bool) :
    pbMat μ (encD nr nc cr cc A B ord y) = sysBits (pbH A B ord μ) 0 := by
  funext q
  unfold pbMat sysBits pbH
  by_cases h1 : q.1.val < k
  · have h1' : q.1.val < k + k := by omega
    by_cases h2 : q.2.val < m
    · simp only [dif_pos h1, dif_pos h2, dif_pos h1', pb_row_enc]
      by_cases hμ : μ ⟨q.1.val, h1⟩ = true
      · simp [hμ]
        exact (pb_vec_bit' _ _ _).symm
      · simp [hμ]
    · simp [h1, h2, h1']
  · by_cases h3 : q.1.val < k + k
    · by_cases h2 : q.2.val < m
      · simp only [dif_neg h1, dif_pos h2, dif_pos h3, pb_row_enc]
        by_cases hμ : μ ⟨q.1.val - k, by omega⟩ = true
        · simp [hμ]
          exact (pb_vec_bit' _ _ _).symm
        · simp [hμ]
      · simp [h1, h2, h3]
    · simp [h1, h3]

theorem pb_span_range {k m : ℕ} (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k)
    (μ : Fin k → Bool) :
    Submodule.span (ZMod 2) (Set.range (pbH A B ord μ)) = pbSpan A B ord μ := by
  unfold pbSpan
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨j, rfl⟩
    unfold pbH
    by_cases h : j.val < k
    · rw [dif_pos h]
      by_cases hμ : μ ⟨j.val, h⟩ = true
      · rw [if_pos hμ]; exact Submodule.subset_span ⟨_, hμ, Or.inl rfl⟩
      · rw [if_neg hμ]; exact Submodule.zero_mem _
    · rw [dif_neg h]
      by_cases hμ : μ ⟨j.val - k, by omega⟩ = true
      · rw [if_pos hμ]; exact Submodule.subset_span ⟨_, hμ, Or.inr rfl⟩
      · rw [if_neg hμ]; exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro v ⟨i', hμ, hv | hv⟩
    · refine Submodule.subset_span ⟨⟨i'.val, by omega⟩, ?_⟩
      simp [pbH, hμ, hv]
    · refine Submodule.subset_span ⟨⟨k + i'.val, by omega⟩, ?_⟩
      simp [pbH, hμ, hv]

theorem pb_rank {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (μ : Fin k → Bool) :
    cnt (pv (gj (k + k + m + 1) (pbMat μ (encD nr nc cr cc A B ord y)))) m =
      Module.finrank (ZMod 2) (pbSpan A B ord μ) := by
  rw [pb_mat_enc, ← fz2_rk, ← la_rank, pb_span_range]

theorem pb_sup {k m : ℕ} (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ) :
    pbSpan A B ord (fun i' => decide (i'.val < i)) ⊔ pbSpan A B ord (fun i' => decide (i ≤ i'.val)) =
      pbSpan A B ord (fun _ => true) := by
  unfold pbSpan
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_union, Set.mem_ofPred_eq, decide_eq_true_eq]
  constructor
  · rintro (⟨i', _, h⟩ | ⟨i', _, h⟩) <;> exact ⟨i', trivial, h⟩
  · rintro ⟨i', _, h⟩
    by_cases hi : i'.val < i
    · exact Or.inl ⟨i', hi, h⟩
    · exact Or.inr ⟨i', by omega, h⟩

theorem pb_lo_span {k m : ℕ} (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ) :
    pbSpan A B ord (fun i' => decide (i'.val < i)) = spanLo k m A B ord i := by
  unfold pbSpan spanLo
  simp only [decide_eq_true_eq]

theorem pb_hi_span {k m : ℕ} (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ) :
    pbSpan A B ord (fun i' => decide (i ≤ i'.val)) = spanHi k m A B ord i := by
  unfold pbSpan spanHi
  simp only [decide_eq_true_eq]

theorem pb_cut_enc {k r m : ℕ} (b : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : Fin k) :
    (∃ q : Fin (k+1) × Fin (m+1) × Fin (m+1) × Fin (m+1),
      cnt (pbFlag (encD nr nc cr cc A B ord y) i) k = q.1.val ∧
      cnt (pv (gj (k + k + m + 1) (pbMat (fun i' => decide (i'.val < i.val))
        (encD nr nc cr cc A B ord y)))) m = q.2.1.val ∧
      cnt (pv (gj (k + k + m + 1) (pbMat (fun i' => decide (i.val ≤ i'.val))
        (encD nr nc cr cc A B ord y)))) m = q.2.2.1.val ∧
      cnt (pv (gj (k + k + m + 1) (pbMat (fun _ => true) (encD nr nc cr cc A B ord y)))) m =
        q.2.2.2.val ∧
      q.1.val + q.2.1.val + q.2.2.1.val ≤ b + q.2.2.2.val) ↔
    ((poolLo k r m A B ord i.val ∩ poolHi k r m A B ord i.val) ∪
        scopeS k r m A B (ord i)).card +
        Module.finrank (ZMod 2) (spanLo k m A B ord i.val ⊓ spanHi k m A B ord i.val :
          Submodule (ZMod 2) (Fin m → ZMod 2)) ≤ b := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (pbSpan A B ord (fun i' => decide (i'.val < i.val)))
    (pbSpan A B ord (fun i' => decide (i.val ≤ i'.val)))
  rw [pb_sup] at hs
  rw [← pb_lo_span, ← pb_hi_span, ← pb_cnt_flag nr nc cr cc A B ord y i]
  have e1 := pb_rank nr nc cr cc A B ord y (fun i' => decide (i'.val < i.val))
  have e2 := pb_rank nr nc cr cc A B ord y (fun i' => decide (i.val ≤ i'.val))
  have e3 := pb_rank nr nc cr cc A B ord y (fun _ => true)
  have l0 := cnt_le (pbFlag (encD nr nc cr cc A B ord y) i) k
  have l1 := cnt_le (pv (gj (k + k + m + 1) (pbMat (fun i' => decide (i'.val < i.val))
        (encD nr nc cr cc A B ord y)))) m
  have l2 := cnt_le (pv (gj (k + k + m + 1) (pbMat (fun i' => decide (i.val ≤ i'.val))
        (encD nr nc cr cc A B ord y)))) m
  have l3 := cnt_le (pv (gj (k + k + m + 1) (pbMat (fun _ => true)
    (encD nr nc cr cc A B ord y)))) m
  rw [← e1, ← e2, ← e3] at hs
  constructor
  · rintro ⟨q, h0, h1, h2, h3, h4⟩
    omega
  · intro h
    exact ⟨(⟨_, Nat.lt_succ_of_le l0⟩, ⟨_, Nat.lt_succ_of_le l1⟩, ⟨_, Nat.lt_succ_of_le l2⟩,
      ⟨_, Nat.lt_succ_of_le l3⟩), rfl, rfl, rfl, rfl, by simp only; omega⟩

theorem pb_bij_enc {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) :
    (∀ z : Fin k, decide (∃ i : Fin k, pbOrdEq (encD nr nc cr cc A B ord y) i z = true) = true) ↔
      Function.Bijective ord := by
  simp only [pb_ordEq_enc, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨Finite.injective_iff_surjective.mpr h, h⟩
  · intro h; exact h.2

theorem pb_cost_mono (k m X : ℕ) (hk : k ≤ X) (hm : m ≤ X) : pbcTot k m ≤ pbcTot X X := by
  unfold pbcTot pbcBij pbcCut pbcRk pbcMat pbcRow pbcFlag pbcLo pbcAt gjCost
  gcongr

theorem pb_cost_X (X : ℕ) (hX : 10 ≤ X) : pbcTot X X ≤ 2^30 * X^10 := by
  unfold pbcTot pbcBij pbcCut pbcRk pbcMat pbcRow pbcFlag pbcLo pbcAt gjCost
  have h1 : 1 ≤ X := by omega
  have p0 : 1 ≤ X^10 := Nat.one_le_pow _ _ h1
  have p1 : X^1 ≤ X^10 := Nat.pow_le_pow_right h1 (by norm_num)
  have p2 : X^2 ≤ X^10 := Nat.pow_le_pow_right h1 (by norm_num)
  have p3 : X^3 ≤ X^10 := Nat.pow_le_pow_right h1 (by norm_num)
  have p4 : X^4 ≤ X^10 := Nat.pow_le_pow_right h1 (by norm_num)
  have p5 : X^5 ≤ X^10 := Nat.pow_le_pow_right h1 (by norm_num)
  have p6 : X^6 ≤ X^10 := Nat.pow_le_pow_right h1 (by norm_num)
  rw [pow_one] at p1
  linarith

theorem pass_cb (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) :
    ∃ φ : (Dat k r m → Bool) → Bool, Cb (Dat k r m) (2^30 * (k+r+m+5)^10) φ ∧
      ∀ (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m))
        (ord : Fin k → Fin k) (y : Fin (2^m)),
        (φ (encD nr nc cr cc A B ord y) = true ↔ passP k r m b A B ord) := by
  have hcuts := pb_and (fun i : Fin k => pb_cut_cb (r := r) (m := m) b i)
  have hall := Cb.and (pb_bij_cb (k := k) (r := r) (m := m)) hcuts
  refine ⟨_, hall.mono ?_, ?_⟩
  · have h1 := pb_cost_mono k m (k+r+m+5) (by omega) (by omega)
    have h2 := pb_cost_X (k+r+m+5) (by omega)
    exact le_trans h1 h2
  · intro nr nc cr cc A B ord y
    rw [pass_iff k r m b hk, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      pb_bij_enc]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    rw [decide_eq_true_eq]
    exact pb_cut_enc b nr nc cr cc A B ord y i

def dNr {k r m : ℕ} (d : Dat k r m → Bool) (i : Fin k) : Bool := d (Sum.inl (Sum.inl i))
def dNc {k r m : ℕ} (d : Dat k r m → Bool) (i : Fin k) : Bool := d (Sum.inl (Sum.inr i))
def dCr {k r m : ℕ} (d : Dat k r m → Bool) (p : Fin r × Fin k) : Bool :=
  d (Sum.inr (Sum.inl (Sum.inl p)))
def dCc {k r m : ℕ} (d : Dat k r m → Bool) (p : Fin r × Fin k) : Bool :=
  d (Sum.inr (Sum.inl (Sum.inr p)))
def dA {k r m : ℕ} (d : Dat k r m → Bool) (p : Fin k × Fin m) : Bool :=
  d (Sum.inr (Sum.inr (Sum.inl (Sum.inl p))))
def dB {k r m : ℕ} (d : Dat k r m → Bool) (p : Fin k × Fin m) : Bool :=
  d (Sum.inr (Sum.inr (Sum.inl (Sum.inr p))))
def dOrd {k r m : ℕ} (d : Dat k r m → Bool) (p : Fin k × Fin k) : Bool :=
  d (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))
def dY {k r m : ℕ} (d : Dat k r m → Bool) (i : Fin m) : Bool :=
  d (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))

def eqOrd {k r m : ℕ} (d : Dat k r m → Bool) (i p : Fin k) : Bool :=
  decide (∀ t : Fin k, dOrd d (i, t) = p.val.testBit t.val)

def aV {k r m : ℕ} (d : Dat k r m → Bool) (i : Fin k) (ρ : Fin m) : Bool :=
  decide (∃ p : Fin k, eqOrd d i p = true ∧ dA d (p, ρ) = true)

def bV {k r m : ℕ} (d : Dat k r m → Bool) (i : Fin k) (ρ : Fin m) : Bool :=
  decide (∃ p : Fin k, eqOrd d i p = true ∧ dB d (p, ρ) = true)

def arcC (k r : ℕ) (col : Bool) (p q : Fin k) : Bool :=
  decide (∃ h : ℕ, h ≤ (if col then 7*r-2 else 5*r-3) ∧ (p.val + h) % k = q.val)

def scP {k r m : ℕ} (d : Dat k r m → Bool) (p q : Fin k) : Bool :=
  (decide (∃ ρ : Fin m, dA d (p, ρ) = true) && arcC k r false p q) ||
  (decide (∃ ρ : Fin m, dB d (p, ρ) = true) && arcC k r true p q)

def scB {k r m : ℕ} (d : Dat k r m → Bool) (i q : Fin k) : Bool :=
  decide (∃ p : Fin k, eqOrd d i p = true ∧ scP d p q = true)

def loB {k r m : ℕ} (d : Dat k r m → Bool) (i : ℕ) (q : Fin k) : Bool :=
  decide (∃ i' : Fin k, i'.val < i ∧ scB d i' q = true)

def hiB {k r m : ℕ} (d : Dat k r m → Bool) (i : ℕ) (q : Fin k) : Bool :=
  decide (∃ i' : Fin k, i ≤ i'.val ∧ scB d i' q = true)

def liveB {k r m : ℕ} (d : Dat k r m → Bool) (i : ℕ) (q : Fin k) : Bool :=
  loB d i q && hiB d i q

def DB {k r m : ℕ} (d : Dat k r m → Bool) (i : Fin k) (q : Fin k) : Bool :=
  liveB d i.val q || scB d i q

abbrev ERow (k m : ℕ) : Type := Fin m ⊕ (Fin m ⊕ Fin k)
abbrev EHid (k : ℕ) : Type := Fin k ⊕ Fin k
abbrev EVis (k m : ℕ) : Type := Fin k ⊕ Fin m

def HbE {k r m : ℕ} (d : Dat k r m → Bool) (i : ℕ) :
    ERow k m × (EHid k ⊕ (EVis k m ⊕ Unit)) → Bool := fun e =>
  match e.1, e.2 with
  | Sum.inl ρ, Sum.inl (Sum.inl j) => decide (j.val < i) && aV d j ρ
  | Sum.inl ρ, Sum.inl (Sum.inr j) => decide (j.val < i) && bV d j ρ
  | Sum.inl _, Sum.inr (Sum.inl (Sum.inl _)) => false
  | Sum.inl ρ, Sum.inr (Sum.inl (Sum.inr ρ')) => decide (ρ' = ρ)
  | Sum.inl _, Sum.inr (Sum.inr _) => false
  | Sum.inr (Sum.inl ρ), Sum.inl (Sum.inl j) => decide (i ≤ j.val) && aV d j ρ
  | Sum.inr (Sum.inl ρ), Sum.inl (Sum.inr j) => decide (i ≤ j.val) && bV d j ρ
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl (Sum.inl _)) => false
  | Sum.inr (Sum.inl ρ), Sum.inr (Sum.inl (Sum.inr ρ')) => decide (ρ' = ρ)
  | Sum.inr (Sum.inl ρ), Sum.inr (Sum.inr _) => dY d ρ
  | Sum.inr (Sum.inr _), Sum.inl _ => false
  | Sum.inr (Sum.inr q), Sum.inr (Sum.inl (Sum.inl q')) => decide (q' = q) && !liveB d i q
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl (Sum.inr _)) => false
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => false

abbrev YVis (k : ℕ) : Type := Fin k ⊕ Fin 2

def HbY {k r m : ℕ} (d : Dat k r m → Bool) (i : Fin k) :
    Fin k × (Empty ⊕ (YVis k ⊕ Unit)) → Bool := fun e =>
  match e.2 with
  | Sum.inr (Sum.inl (Sum.inl q')) => decide (q' = e.1) && !DB d i e.1
  | _ => false

noncomputable def slE (k m b : ℕ) :
    (ERow k m × (EHid k ⊕ (EVis k m ⊕ Unit)) → Bool) → SOut (EVis k m) b → Bool :=
  Classical.choose (glS (ERow k m) (EHid k) (EVis k m) b)

noncomputable def nfE (k m b : ℕ) : (ERow k m × (EHid k ⊕ (EVis k m ⊕ Unit)) → Bool) → ℕ :=
  Classical.choose (Classical.choose_spec (glS (ERow k m) (EHid k) (EVis k m) b))

theorem slE_cmp (k m b : ℕ) : Cmp (ERow k m × (EHid k ⊕ (EVis k m ⊕ Unit))) (SOut (EVis k m) b)
    (glCost (Fintype.card (ERow k m)) (Fintype.card (EHid k)) (Fintype.card (EVis k m)) b)
    (slE k m b) :=
  (Classical.choose_spec (Classical.choose_spec (glS (ERow k m) (EHid k) (EVis k m) b))).1

theorem slE_spec (k m b : ℕ) : SSpec (ERow k m) (EHid k) (EVis k m) b (slE k m b) (nfE k m b) :=
  (Classical.choose_spec (Classical.choose_spec (glS (ERow k m) (EHid k) (EVis k m) b))).2

noncomputable def slY (k b : ℕ) :
    (Fin k × (Empty ⊕ (YVis k ⊕ Unit)) → Bool) → SOut (YVis k) (b+2) → Bool :=
  Classical.choose (glS (Fin k) Empty (YVis k) (b+2))

noncomputable def nfY (k b : ℕ) : (Fin k × (Empty ⊕ (YVis k ⊕ Unit)) → Bool) → ℕ :=
  Classical.choose (Classical.choose_spec (glS (Fin k) Empty (YVis k) (b+2)))

theorem slY_cmp (k b : ℕ) : Cmp (Fin k × (Empty ⊕ (YVis k ⊕ Unit))) (SOut (YVis k) (b+2))
    (glCost (Fintype.card (Fin k)) (Fintype.card Empty) (Fintype.card (YVis k)) (b+2))
    (slY k b) :=
  (Classical.choose_spec (Classical.choose_spec (glS (Fin k) Empty (YVis k) (b+2)))).1

theorem slY_spec (k b : ℕ) : SSpec (Fin k) Empty (YVis k) (b+2) (slY k b) (nfY k b) :=
  (Classical.choose_spec (Classical.choose_spec (glS (Fin k) Empty (YVis k) (b+2)))).2

def sPtB {ι2 : Type} {β : ℕ} (o : SOut ι2 β → Bool) (xb : Fin β → Bool) (j : ι2) : Bool :=
  xor (o (Sum.inr (Sum.inl j)))
    (decide ((Finset.univ.filter (fun t : Fin β => (o (Sum.inl (j, t)) && xb t) = true)).card
      % 2 = 1))

noncomputable def stFn (k r : ℕ) (col : Bool) (wb nb : Fin k → Bool) (cb : Fin r × Fin k → Bool)
    (i : Fin k) : Bool :=
  (stateN k r col (tabN wb) (tabN nb)
    (fun j => ⟨tabN (fun t => cb (j, t)) % 2^k, Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))⟩)
    ).testBit i.val

noncomputable def senB {k r m : ℕ} (col : Bool) (d : Dat k r m → Bool) (i : Fin k)
    (τ : Fin k → Bool) : Bool :=
  decide (∃ p : Fin k, eqOrd d i p = true ∧
    stFn k r col τ (if col then dNc d else dNr d) (if col then dCc d else dCr d)
      ⟨(p.val + (if col then 3*r+1 else 2*r-2)) % k, Nat.mod_lt _ p.pos⟩ = true)

noncomputable def gT {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (pin value : Fin k → Bool)
    (i : Fin k) (iy : Fin (2^(b+2))) : Bool :=
  (sPtB (slY k b (HbY d i)) (fun t => iy.val.testBit t.val) (Sum.inr 0) ==
    senB false d i (fun q => sPtB (slY k b (HbY d i)) (fun t => iy.val.testBit t.val)
      (Sum.inl q))) &&
  (sPtB (slY k b (HbY d i)) (fun t => iy.val.testBit t.val) (Sum.inr 1) ==
    senB true d i (fun q => sPtB (slY k b (HbY d i)) (fun t => iy.val.testBit t.val)
      (Sum.inl q))) &&
  decide (∀ q : Fin k, (DB d i q && pin q) = true →
    sPtB (slY k b (HbY d i)) (fun t => iy.val.testBit t.val) (Sum.inl q) = value q)

abbrev JRow (k m b : ℕ) : Type :=
  Fin k ⊕ (Fin k ⊕ (Fin m ⊕ (Fin b ⊕ (Fin (b+2) ⊕ Fin b))))

noncomputable def HJ {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (i : Fin k) :
    JRow k m b × (Fin b ⊕ (Fin (b+2) ⊕ (Fin b ⊕ Unit))) → Bool := fun e =>
  let oE := slE k m b (HbE d i.val)
  let oE' := slE k m b (HbE d (i.val+1))
  let oY := slY k b (HbY d i)
  match e.1, e.2 with
  | Sum.inl q, Sum.inl t => liveB d i.val q && oE (Sum.inl (Sum.inl q, t))
  | Sum.inl q, Sum.inr (Sum.inl t) => liveB d i.val q && oY (Sum.inl (Sum.inl q, t))
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inl _)) => false
  | Sum.inl q, Sum.inr (Sum.inr (Sum.inr _)) => liveB d i.val q &&
      xor (oE (Sum.inr (Sum.inl (Sum.inl q)))) (oY (Sum.inr (Sum.inl (Sum.inl q))))
  | Sum.inr (Sum.inl _), Sum.inl _ => false
  | Sum.inr (Sum.inl q), Sum.inr (Sum.inl t) =>
      liveB d (i.val+1) q && oY (Sum.inl (Sum.inl q, t))
  | Sum.inr (Sum.inl q), Sum.inr (Sum.inr (Sum.inl t)) =>
      liveB d (i.val+1) q && oE' (Sum.inl (Sum.inl q, t))
  | Sum.inr (Sum.inl q), Sum.inr (Sum.inr (Sum.inr _)) => liveB d (i.val+1) q &&
      xor (oE' (Sum.inr (Sum.inl (Sum.inl q)))) (oY (Sum.inr (Sum.inl (Sum.inl q))))
  | Sum.inr (Sum.inr (Sum.inl ρ)), Sum.inl t => oE (Sum.inl (Sum.inr ρ, t))
  | Sum.inr (Sum.inr (Sum.inl ρ)), Sum.inr (Sum.inl t) =>
      xor (oY (Sum.inl (Sum.inr 0, t)) && aV d i ρ) (oY (Sum.inl (Sum.inr 1, t)) && bV d i ρ)
  | Sum.inr (Sum.inr (Sum.inl ρ)), Sum.inr (Sum.inr (Sum.inl t)) => oE' (Sum.inl (Sum.inr ρ, t))
  | Sum.inr (Sum.inr (Sum.inl ρ)), Sum.inr (Sum.inr (Sum.inr _)) =>
      xor (xor (oE (Sum.inr (Sum.inl (Sum.inr ρ)))) (oE' (Sum.inr (Sum.inl (Sum.inr ρ)))))
        (xor (oY (Sum.inr (Sum.inl (Sum.inr 0))) && aV d i ρ)
          (oY (Sum.inr (Sum.inl (Sum.inr 1))) && bV d i ρ))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))), Sum.inl t' =>
      decide (t' = t) && !oE (Sum.inr (Sum.inr (Sum.inl t)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))), Sum.inr _ => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))), Sum.inr (Sum.inl t') =>
      decide (t' = t) && !oY (Sum.inr (Sum.inr (Sum.inl t)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))), Sum.inl _ => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))), Sum.inr (Sum.inr _) => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))), Sum.inr (Sum.inr (Sum.inl t')) =>
      decide (t' = t) && !oE' (Sum.inr (Sum.inr (Sum.inl t)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))), Sum.inl _ => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))), Sum.inr (Sum.inl _) => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))), Sum.inr (Sum.inr (Sum.inr _)) => false

noncomputable def jnF (k m b : ℕ) :
    (JIn (JRow k m b) b (b+2) b (k+1) → Bool) → (Fin (2^b) × Fin (k+1) → Bool) :=
  Classical.choose (joinS (JRow k m b) b (b+2) b (k+1) (b+2))

theorem jnF_cmp (k m b : ℕ) : Cmp (JIn (JRow k m b) b (b+2) b (k+1)) (Fin (2^b) × Fin (k+1))
    (topCost b (b+2) b (Fintype.card (JRow k m b)) (k+1) (b+2)) (jnF k m b) :=
  (Classical.choose_spec (joinS (JRow k m b) b (b+2) b (k+1) (b+2))).1

theorem jnF_spec (k m b : ℕ) (v : JIn (JRow k m b) b (b+2) b (k+1) → Bool)
    (h : Nat.card {p : (Fin b → ZMod 2) × (Fin (b+2) → ZMod 2) × (Fin b → ZMod 2) //
      jHom v p.1 p.2.1 p.2.2} ≤ 2^(b+2)) (iz : Fin (2^b)) (j : Fin (k+1)) :
    jnF k m b v (iz, j) = (jTot v iz).testBit j.val :=
  (Classical.choose_spec (joinS (JRow k m b) b (b+2) b (k+1) (b+2))).2 v h iz j

noncomputable def jInp {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (pin value : Fin k → Bool)
    (i : Fin k) (T : Fin (2^b) × Fin (k+1) → Bool) : JIn (JRow k m b) b (b+2) b (k+1) → Bool :=
  Sum.elim (HJ b d i) (Sum.elim T (fun p => decide (p.2.val = 0) && gT b d pin value i p.1))

noncomputable def stepT {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (pin value : Fin k → Bool)
    (i : Fin k) (T : Fin (2^b) × Fin (k+1) → Bool) : Fin (2^b) × Fin (k+1) → Bool :=
  jnF k m b (jInp b d pin value i T)

noncomputable def tblT {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (pin value : Fin k → Bool) :
    ℕ → Fin (2^b) × Fin (k+1) → Bool
  | 0 => fun p => decide (p.2.val = 0)
  | i+1 => if h : i < k then stepT b d pin value ⟨i, h⟩ (tblT b d pin value i)
      else tblT b d pin value i

noncomputable def allCons {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) : Bool :=
  decide (∀ i : Fin (k+1), slE k m b (HbE d i.val) (Sum.inr (Sum.inr (Sum.inr ()))) = true)

noncomputable def finW {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (pin value : Fin k → Bool) :
    BitVec (k+1) :=
  (List.finRange k).foldl (fun acc q => if (!loB d k q && !pin q) = true then acc + acc else acc)
    (bv (fun j => tblT b d pin value k (⟨0, Nat.pos_of_ne_zero (by positivity)⟩, j)))

noncomputable def passF (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) : (Dat k r m → Bool) → Bool :=
  Classical.choose (pass_cb k r m b hk hr)

noncomputable def coreF (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (v : CoreIn k r m → Bool) :
    Unit ⊕ Fin (k+1) → Bool :=
  Sum.elim (fun _ => passF k r m b hk hr (fun x => v (Sum.inl x)))
    (fun j => allCons b (fun x => v (Sum.inl x)) &&
      (finW b (fun x => v (Sum.inl x)) (fun q => v (Sum.inr (Sum.inl q)))
        (fun q => v (Sum.inr (Sum.inr q)))).getLsbD j.val)

noncomputable def sSen (k r : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (col : Bool) (p : Fin k) (ω : Fin k → Bool) : Bool :=
  (stateN k r col (tabN ω) (if col then nc.val else nr.val) (if col then cc else cr)).testBit
    ((p.val + (if col then 3*r+1 else 2*r-2)) % k)

noncomputable def phiS (k r m : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (p : Fin k) (ω : Fin k → Bool) : Fin m → ZMod 2 :=
  b2z (sSen k r nr nc cr cc false p ω) • vecN m (A p).val +
    b2z (sSen k r nr nc cr cc true p ω) • vecN m (B p).val

theorem ch_tabN_lt {n : ℕ} (T : Fin n → Bool) : tabN T < 2^n := st_tabN_lt T

theorem ch_tabN_testBit {n : ℕ} (T : Fin n → Bool) (i : Fin n) : (tabN T).testBit i.val = T i :=
  st_tabN_testBit T i

theorem ch_tabN_bits (n x : ℕ) (hx : x < 2^n) : tabN (fun i : Fin n => x.testBit i.val) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact ch_tabN_testBit (fun i : Fin n => x.testBit i.val) ⟨i, hi⟩
  · have hpow : 2^n ≤ 2^i := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    rw [Nat.testBit_lt_two_pow ((ch_tabN_lt _).trans_le hpow),
      Nat.testBit_lt_two_pow (hx.trans_le hpow)]

theorem ch_bits_eq (n x y : ℕ) (hx : x < 2^n) (hy : y < 2^n)
    (h : ∀ t : Fin n, x.testBit t.val = y.testBit t.val) : x = y := by
  rw [← ch_tabN_bits n x hx, ← ch_tabN_bits n y hy]
  congr 1
  funext t
  exact h t

theorem ch_nz (m x : ℕ) (hx : x < 2^m) : (∃ ρ : Fin m, x.testBit ρ.val = true) ↔ x ≠ 0 := by
  constructor
  · rintro ⟨ρ, h⟩ h0
    rw [h0] at h
    simp at h
  · intro h0
    by_contra hne
    apply h0
    apply ch_bits_eq m x 0 hx (Nat.pos_of_ne_zero (by positivity))
    intro t
    have : ¬ x.testBit t.val = true := fun h => hne ⟨t, h⟩
    simpa using this

theorem ch_eqOrd {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i p : Fin k) :
    eqOrd (encD nr nc cr cc A B ord y) i p = decide (ord i = p) := by
  have e : eqOrd (encD nr nc cr cc A B ord y) i p =
      decide (∀ t : Fin k, (ord i).val.testBit t.val = p.val.testBit t.val) := rfl
  rw [e]
  apply decide_eq_decide.mpr
  constructor
  · intro h
    apply Fin.ext
    have hk : k < 2^k := Nat.lt_two_pow_self
    exact ch_bits_eq k _ _ ((ord i).isLt.trans hk) (p.isLt.trans hk) h
  · intro h t
    rw [h]

theorem ch_aV0 {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : Fin k) (ρ : Fin m) :
    aV (encD nr nc cr cc A B ord y) i ρ = (A (ord i)).val.testBit ρ.val := by
  have e : aV (encD nr nc cr cc A B ord y) i ρ = decide (∃ p : Fin k,
      eqOrd (encD nr nc cr cc A B ord y) i p = true ∧ (A p).val.testBit ρ.val = true) := rfl
  rw [e]
  apply Bool.eq_iff_iff.mpr
  simp only [ch_eqOrd, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, h⟩
    rw [hp]; exact h
  · intro h
    exact ⟨ord i, rfl, h⟩

theorem ch_bV0 {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : Fin k) (ρ : Fin m) :
    bV (encD nr nc cr cc A B ord y) i ρ = (B (ord i)).val.testBit ρ.val := by
  have e : bV (encD nr nc cr cc A B ord y) i ρ = decide (∃ p : Fin k,
      eqOrd (encD nr nc cr cc A B ord y) i p = true ∧ (B p).val.testBit ρ.val = true) := rfl
  rw [e]
  apply Bool.eq_iff_iff.mpr
  simp only [ch_eqOrd, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, h⟩
    rw [hp]; exact h
  · intro h
    exact ⟨ord i, rfl, h⟩

theorem ch_aV {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : Fin k) (ρ : Fin m) :
    b2z (aV (encD nr nc cr cc A B ord y) i ρ) = vecN m (A (ord i)).val ρ := by
  rw [ch_aV0]; rfl

theorem ch_bV {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : Fin k) (ρ : Fin m) :
    b2z (bV (encD nr nc cr cc A B ord y) i ρ) = vecN m (B (ord i)).val ρ := by
  rw [ch_bV0]; rfl

theorem ch_dY {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (ρ : Fin m) :
    b2z (dY (encD nr nc cr cc A B ord y) ρ) = vecN m y.val ρ := rfl

theorem ch_scP {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (p q : Fin k) :
    (scP (encD nr nc cr cc A B ord y) p q = true ↔ q ∈ scopeS k r m A B p) := by
  have e : scP (encD nr nc cr cc A B ord y) p q =
      ((decide (∃ ρ : Fin m, (A p).val.testBit ρ.val = true) && arcC k r false p q) ||
       (decide (∃ ρ : Fin m, (B p).val.testBit ρ.val = true) && arcC k r true p q)) := rfl
  rw [e]
  simp only [scopeS, arcC, Finset.mem_filter, Finset.mem_univ, true_and, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, ch_nz m _ (A p).isLt, ch_nz m _ (B p).isLt,
    Bool.false_eq_true, if_false, if_true]

theorem ch_scB {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i q : Fin k) :
    (scB (encD nr nc cr cc A B ord y) i q = true ↔ q ∈ scopeS k r m A B (ord i)) := by
  unfold scB
  simp only [ch_eqOrd, decide_eq_true_eq, ch_scP]
  constructor
  · rintro ⟨p, hp, h⟩
    rw [hp]; exact h
  · intro h
    exact ⟨ord i, rfl, h⟩

theorem ch_loB {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : ℕ) (q : Fin k) :
    (loB (encD nr nc cr cc A B ord y) i q = true ↔ q ∈ poolLo k r m A B ord i) := by
  unfold loB poolLo
  simp only [decide_eq_true_eq, ch_scB, Finset.mem_filter, Finset.mem_univ, true_and]

theorem ch_hiB {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : ℕ) (q : Fin k) :
    (hiB (encD nr nc cr cc A B ord y) i q = true ↔ q ∈ poolHi k r m A B ord i) := by
  unfold hiB poolHi
  simp only [decide_eq_true_eq, ch_scB, Finset.mem_filter, Finset.mem_univ, true_and]

theorem ch_stFn {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (col : Bool)
    (τ : Fin k → Bool) (i' : Fin k) :
    stFn k r col τ (if col then dNc (encD nr nc cr cc A B ord y) else dNr (encD nr nc cr cc A B ord y))
      (if col then dCc (encD nr nc cr cc A B ord y) else dCr (encD nr nc cr cc A B ord y)) i' =
    (stateN k r col (tabN τ) (if col then nc.val else nr.val) (if col then cc else cr)).testBit
      i'.val := by
  have hc : ∀ (c : Fin r → Fin (2^k)),
      (fun j : Fin r => (⟨tabN (fun t : Fin k => (c j).val.testBit t.val) % 2^k,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))⟩ : Fin (2^k))) = c := by
    intro c
    funext j
    apply Fin.ext
    show tabN (fun t : Fin k => (c j).val.testBit t.val) % 2^k = (c j).val
    rw [ch_tabN_bits _ _ (c j).isLt, Nat.mod_eq_of_lt (c j).isLt]
  cases col
  · simp only [Bool.false_eq_true, if_false]
    show (stateN k r false (tabN τ) (tabN (fun i : Fin k => nr.val.testBit i.val))
      (fun j : Fin r => (⟨tabN (fun t : Fin k => (cr j).val.testBit t.val) % 2^k,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))⟩ : Fin (2^k)))).testBit i'.val = _
    rw [hc cr, ch_tabN_bits _ _ nr.isLt]
  · simp only [if_true]
    show (stateN k r true (tabN τ) (tabN (fun i : Fin k => nc.val.testBit i.val))
      (fun j : Fin r => (⟨tabN (fun t : Fin k => (cc j).val.testBit t.val) % 2^k,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))⟩ : Fin (2^k)))).testBit i'.val = _
    rw [hc cc, ch_tabN_bits _ _ nc.isLt]

theorem ch_senB {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (col : Bool) (i : Fin k)
    (τ : Fin k → Bool) :
    senB col (encD nr nc cr cc A B ord y) i τ = sSen k r nr nc cr cc col (ord i) τ := by
  unfold senB sSen
  apply Bool.eq_iff_iff.mpr
  simp only [ch_eqOrd, ch_stFn, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, h⟩
    rw [hp]; exact h
  · intro h
    exact ⟨ord i, rfl, h⟩

theorem ch_vec0 (m : ℕ) : vecN m 0 = 0 := by
  funext i
  simp [vecN]

theorem ch_phi_local (k r m : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (nr nc : Fin (2^k))
    (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m)) (p : Fin k) (ω ω' : Fin k → Bool)
    (h : ∀ q ∈ scopeS k r m A B p, ω q = ω' q) :
    phiS k r m nr nc cr cc A B p ω = phiS k r m nr nc cr cc A B p ω' := by
  unfold phiS
  have key : ∀ (col : Bool), (if col then (B p).val else (A p).val) ≠ 0 →
      sSen k r nr nc cr cc col p ω = sSen k r nr nc cr cc col p ω' := by
    intro col hne
    unfold sSen
    apply sens_local k r hk hr col _ _ _ _ p (ch_tabN_lt ω) (ch_tabN_lt ω')
    · cases col
      · simp
      · simp
    · intro h' hh
      have hq : (p.val + h') % k < k := Nat.mod_lt _ hk
      have e1 := ch_tabN_testBit ω ⟨(p.val + h') % k, hq⟩
      have e2 := ch_tabN_testBit ω' ⟨(p.val + h') % k, hq⟩
      simp only at e1 e2
      rw [e1, e2]
      apply h
      simp only [scopeS, Finset.mem_filter, Finset.mem_univ, true_and]
      cases col
      · left
        exact ⟨by simpa using hne, h', by simpa using hh, rfl⟩
      · right
        exact ⟨by simpa using hne, h', by simpa using hh, rfl⟩
  congr 1
  · by_cases hA : (A p).val = 0
    · rw [hA, ch_vec0]; simp
    · rw [key false (by simpa using hA)]
  · by_cases hB : (B p).val = 0
    · rw [hB, ch_vec0]; simp
    · rw [key true (by simpa using hB)]

theorem ch_hit (k r m : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (y : Fin (2^m)) (ω : Fin k → Bool) :
    (reportN k r m nr nc cr cc A B (tabN ω) = y.val ↔
      ∑ p : Fin k, phiS k r m nr nc cr cc A B p ω = vecN m y.val) := by
  have e : ∑ p : Fin k, phiS k r m nr nc cr cc A B p ω =
      vecN m (reportN k r m nr nc cr cc A B (tabN ω)) := by
    rw [report_vec]
    apply Finset.sum_congr rfl
    intro p _
    simp [phiS, sSen]
  rw [e]
  constructor
  · intro h; rw [h]
  · intro h
    exact vecN_inj m _ _ (reportN_lt k r m nr nc cr cc A B _) y.isLt h

theorem sy_b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> simp [b2z]

theorem sy_b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> simp [b2z] <;> decide

theorem sy_b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> simp [b2z] <;> decide

theorem sy_b2z_false : b2z false = 0 := by simp [b2z]

theorem sy_b2z_true : b2z true = 1 := by simp [b2z]

theorem sy_par (n : ℕ) : b2z (decide (n % 2 = 1)) = (n : ZMod 2) := by
  rw [← ZMod.natCast_mod n 2]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, b2z]

theorem sy_sum_dec {β : ℕ} (t : Fin β) (c : Bool) (x : Fin β → ZMod 2) :
    (∑ t' : Fin β, b2z (decide (t' = t) && c) * x t') = b2z c * x t := by
  rw [Fintype.sum_eq_single t]
  · simp [sy_b2z_and, b2z]
  · intro t' h
    simp [h, b2z]

theorem sy_z1 (p q a b : ZMod 2) : p + q = a + b ↔ a + p = b + q := by
  revert p q a b; decide

theorem sy_z2 (p q : ZMod 2) : p + q = 0 ↔ p = q := by
  revert p q; decide

theorem sy_z3 (c x : ZMod 2) : (1 + c) * x = 0 ↔ (c = 0 → x = 0) := by
  revert c x; decide

theorem sy_zd (X P Q Z e e' f0 f1 a b : ZMod 2) :
    X + (P * a + Q * b) + Z = e + e' + (f0 * a + f1 * b) ↔
      (e + X) + (e' + Z) + (f0 + P) * a + (f1 + Q) * b = 0 := by
  revert X P Q Z e e' f0 f1 a b; decide

theorem sy_b2z_eq_zero (c : Bool) : b2z c = 0 ↔ c = false := by
  cases c <;> simp [b2z]

theorem sy_rowA {β γ : ℕ} (mk : Bool) (ox : Fin β → Bool) (oy : Fin γ → Bool) (a b : Bool)
    (x : Fin β → ZMod 2) (y : Fin γ → ZMod 2) :
    (∑ t, b2z (mk && ox t) * x t) + (∑ t, b2z (mk && oy t) * y t) = b2z (mk && xor a b) ↔
      (mk = true → b2z a + ∑ t, b2z (ox t) * x t = b2z b + ∑ t, b2z (oy t) * y t) := by
  cases mk
  · simp [b2z]
  · simp only [Bool.true_and, forall_const, sy_b2z_xor]
    exact sy_z1 _ _ _ _

theorem sy_rowAh {β γ : ℕ} (mk : Bool) (ox : Fin β → Bool) (oy : Fin γ → Bool)
    (x : Fin β → ZMod 2) (y : Fin γ → ZMod 2) :
    (∑ t, b2z (mk && ox t) * x t) + (∑ t, b2z (mk && oy t) * y t) = 0 ↔
      (mk = true → ∑ t, b2z (ox t) * x t = ∑ t, b2z (oy t) * y t) := by
  cases mk
  · simp [b2z]
  · simp only [Bool.true_and, forall_const]
    exact sy_z2 _ _

theorem sy_rowU {β : ℕ} (t : Fin β) (u : Bool) (x : Fin β → ZMod 2) :
    (∑ t' : Fin β, b2z (decide (t' = t) && !u) * x t') = 0 ↔ (u = false → x t = 0) := by
  rw [sy_sum_dec]
  cases u <;> simp [b2z]

theorem sy_sumD {γ : ℕ} (o0 o1 : Fin γ → Bool) (av bv : Bool) (y : Fin γ → ZMod 2) :
    (∑ t, b2z (xor (o0 t && av) (o1 t && bv)) * y t) =
      (∑ t, b2z (o0 t) * y t) * b2z av + (∑ t, b2z (o1 t) * y t) * b2z bv := by
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [sy_b2z_xor, sy_b2z_and, sy_b2z_and]
  ring

theorem sy_rowC {β γ : ℕ} (mk : Bool) (oy : Fin γ → Bool) (oz : Fin β → Bool) (a b : Bool)
    (y : Fin γ → ZMod 2) (z : Fin β → ZMod 2) :
    (∑ t, b2z (mk && oy t) * y t) + (∑ t, b2z (mk && oz t) * z t) = b2z (mk && xor a b) ↔
      (mk = true → b2z a + ∑ t, b2z (oz t) * z t = b2z b + ∑ t, b2z (oy t) * y t) := by
  cases mk
  · simp [b2z]
  · simp only [Bool.true_and, forall_const, sy_b2z_xor]
    rw [add_comm (∑ t, b2z (oy t) * y t)]
    exact sy_z1 _ _ _ _

theorem sy_rowCh {β γ : ℕ} (mk : Bool) (oy : Fin γ → Bool) (oz : Fin β → Bool)
    (y : Fin γ → ZMod 2) (z : Fin β → ZMod 2) :
    (∑ t, b2z (mk && oy t) * y t) + (∑ t, b2z (mk && oz t) * z t) = 0 ↔
      (mk = true → ∑ t, b2z (oz t) * z t = ∑ t, b2z (oy t) * y t) := by
  cases mk
  · simp [b2z]
  · simp only [Bool.true_and, forall_const]
    rw [add_comm]
    exact sy_z2 _ _

theorem sy_zdh (X P Q Z a b : ZMod 2) :
    X + (P * a + Q * b) + Z = 0 ↔ X + Z + P * a + Q * b = 0 := by
  revert X P Q Z a b; decide

theorem sy_z4 (p q a b : ZMod 2) : a + p = b + q ↔ a + q = b + p := by
  revert p q a b; decide

theorem sy_sum_dec1 {β : ℕ} (t : Fin β) (x : Fin β → ZMod 2) :
    (∑ t' : Fin β, b2z (decide (t' = t)) * x t') = x t := by
  rw [Fintype.sum_eq_single t]
  · simp [b2z]
  · intro t' h
    simp [h, b2z]

theorem sy_pt {k m : ℕ} (P : Fin k → Prop) [DecidablePred P] (f g : Fin k → Fin m → ZMod 2)
    (av bv : Fin k → Bool) (ρ : Fin m) (ha : ∀ j, b2z (av j) = f j ρ)
    (hb : ∀ j, b2z (bv j) = g j ρ) (c0 c1 : Fin k → ZMod 2) :
    (∑ j, if P j then c0 j • f j + c1 j • g j else 0) ρ =
      (∑ j, b2z (decide (P j) && av j) * c0 j) + ∑ j, b2z (decide (P j) && bv j) * c1 j := by
  rw [Finset.sum_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : P j
  · simp [h, ← ha, ← hb, mul_comm]
  · simp [h, b2z]

theorem ch_solE {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : ℕ)
    (e : EVis k m → ZMod 2) :
    solS (HbE (encD nr nc cr cc A B ord y) i) e ↔
      (∀ q : Fin k, liveB (encD nr nc cr cc A B ord y) i q = false → e (Sum.inl q) = 0) ∧
      ∃ c0 c1 : Fin k → ZMod 2,
        (∑ j : Fin k, if j.val < i then
          (c0 j • vecN m (A (ord j)).val + c1 j • vecN m (B (ord j)).val) else 0) =
          (fun ρ => e (Sum.inr ρ)) ∧
        (∑ j : Fin k, if i ≤ j.val then
          (c0 j • vecN m (A (ord j)).val + c1 j • vecN m (B (ord j)).val) else 0) +
          (fun ρ => e (Sum.inr ρ)) = vecN m y.val := by
  unfold solS
  simp only [Sum.forall, Fintype.sum_sum_type, HbE]
  simp only [sy_b2z_false, zero_mul, Finset.sum_const_zero, add_zero, zero_add, sy_sum_dec1,
    sy_rowU]
  constructor
  · rintro ⟨c, h1, h2, h3⟩
    refine ⟨h3, fun j => c (Sum.inl j), fun j => c (Sum.inr j), ?_, ?_⟩
    · funext ρ
      rw [sy_pt (fun j : Fin k => j.val < i) _ _ _ _ ρ (fun j => ch_aV nr nc cr cc A B ord y j ρ)
        (fun j => ch_bV nr nc cr cc A B ord y j ρ)]
      exact (sy_z2 _ _).1 (h1 ρ)
    · funext ρ
      rw [Pi.add_apply, sy_pt (fun j : Fin k => i ≤ j.val) _ _ _ _ ρ
        (fun j => ch_aV nr nc cr cc A B ord y j ρ)
        (fun j => ch_bV nr nc cr cc A B ord y j ρ), ← ch_dY nr nc cr cc A B ord y ρ]
      exact h2 ρ
  · rintro ⟨h3, c0, c1, e1, e2⟩
    refine ⟨Sum.elim c0 c1, fun ρ => ?_, fun ρ => ?_, h3⟩
    · have h := congrFun e1 ρ
      rw [sy_pt (fun j : Fin k => j.val < i) _ _ _ _ ρ (fun j => ch_aV nr nc cr cc A B ord y j ρ)
        (fun j => ch_bV nr nc cr cc A B ord y j ρ)] at h
      exact (sy_z2 _ _).2 h
    · have h := congrFun e2 ρ
      rw [Pi.add_apply, sy_pt (fun j : Fin k => i ≤ j.val) _ _ _ _ ρ
        (fun j => ch_aV nr nc cr cc A B ord y j ρ)
        (fun j => ch_bV nr nc cr cc A B ord y j ρ), ← ch_dY nr nc cr cc A B ord y ρ] at h
      exact h

theorem ch_solY {k r m : ℕ} (d : Dat k r m → Bool) (i : Fin k) (e : YVis k → ZMod 2) :
    solS (HbY d i) e ↔ ∀ q : Fin k, DB d i q = false → e (Sum.inl q) = 0 := by
  unfold solS
  simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add, Fintype.sum_sum_type, HbY,
    sy_b2z_false, zero_mul, Finset.sum_const_zero, add_zero, sy_sum_dec, sy_b2z_not, sy_z3,
    sy_b2z_eq_zero]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨fun _ => 0, h⟩

theorem ch_jSat {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (pin value : Fin k → Bool)
    (i : Fin k) (T : Fin (2^b) × Fin (k+1) → Bool)
    (x : Fin b → ZMod 2) (yy : Fin (b+2) → ZMod 2) (z : Fin b → ZMod 2) :
    jSat (jInp b d pin value i T) x yy z ↔
      sOk (slE k m b (HbE d i.val)) x ∧ sOk (slY k b (HbY d i)) yy ∧
      sOk (slE k m b (HbE d (i.val+1))) z ∧
      (∀ q : Fin k, liveB d i.val q = true →
        sPt (slE k m b (HbE d i.val)) x (Sum.inl q) = sPt (slY k b (HbY d i)) yy (Sum.inl q)) ∧
      (∀ q : Fin k, liveB d (i.val+1) q = true →
        sPt (slE k m b (HbE d (i.val+1))) z (Sum.inl q) =
          sPt (slY k b (HbY d i)) yy (Sum.inl q)) ∧
      (∀ ρ : Fin m, sPt (slE k m b (HbE d i.val)) x (Sum.inr ρ) +
        sPt (slE k m b (HbE d (i.val+1))) z (Sum.inr ρ) +
        sPt (slY k b (HbY d i)) yy (Sum.inr 0) * b2z (aV d i ρ) +
        sPt (slY k b (HbY d i)) yy (Sum.inr 1) * b2z (bV d i ρ) = 0) := by
  unfold jSat
  simp only [jInp, Sum.elim_inl, Sum.forall, HJ]
  simp only [sy_b2z_false, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  simp only [sy_rowA, sy_rowU, sy_sumD]
  simp only [sy_b2z_xor, sy_b2z_and, sy_zd]
  unfold sOk sPt
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h4, h5, h6, h1, fun q hq => (sy_z4 _ _ _ _).1 (h2 q hq), h3⟩
  · rintro ⟨h4, h5, h6, h1, h2, h3⟩
    exact ⟨h1, fun q hq => (sy_z4 _ _ _ _).1 (h2 q hq), h3, h4, h5, h6⟩

theorem ch_jHom {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (pin value : Fin k → Bool)
    (i : Fin k) (T : Fin (2^b) × Fin (k+1) → Bool)
    (x : Fin b → ZMod 2) (yy : Fin (b+2) → ZMod 2) (z : Fin b → ZMod 2) :
    jHom (jInp b d pin value i T) x yy z ↔
      sOk (slE k m b (HbE d i.val)) x ∧ sOk (slY k b (HbY d i)) yy ∧
      sOk (slE k m b (HbE d (i.val+1))) z ∧
      (∀ q : Fin k, liveB d i.val q = true →
        (∑ t, b2z (slE k m b (HbE d i.val) (Sum.inl (Sum.inl q, t))) * x t) =
          ∑ t, b2z (slY k b (HbY d i) (Sum.inl (Sum.inl q, t))) * yy t) ∧
      (∀ q : Fin k, liveB d (i.val+1) q = true →
        (∑ t, b2z (slE k m b (HbE d (i.val+1)) (Sum.inl (Sum.inl q, t))) * z t) =
          ∑ t, b2z (slY k b (HbY d i) (Sum.inl (Sum.inl q, t))) * yy t) ∧
      (∀ ρ : Fin m, (∑ t, b2z (slE k m b (HbE d i.val) (Sum.inl (Sum.inr ρ, t))) * x t) +
        (∑ t, b2z (slE k m b (HbE d (i.val+1)) (Sum.inl (Sum.inr ρ, t))) * z t) +
        (∑ t, b2z (slY k b (HbY d i) (Sum.inl (Sum.inr 0, t))) * yy t) * b2z (aV d i ρ) +
        (∑ t, b2z (slY k b (HbY d i) (Sum.inl (Sum.inr 1, t))) * yy t) * b2z (bV d i ρ) = 0) := by
  unfold jHom
  simp only [jInp, Sum.elim_inl, Sum.forall, HJ]
  simp only [sy_b2z_false, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  simp only [sy_rowAh, sy_rowU, sy_sumD]
  simp only [sy_zdh]
  unfold sOk
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h4, h5, h6, h1, fun q hq => (h2 q hq).symm, h3⟩
  · rintro ⟨h4, h5, h6, h1, h2, h3⟩
    exact ⟨h1, fun q hq => (h2 q hq).symm, h3, h4, h5, h6⟩

theorem ch_sPtB {ι2 : Type} {β : ℕ} (o : SOut ι2 β → Bool) (xb : Fin β → Bool) (j : ι2) :
    b2z (sPtB o xb j) = sPt o (fun t => b2z (xb t)) j := by
  unfold sPtB sPt
  rw [sy_b2z_xor, sy_par, Finset.card_filter, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  cases h1 : o (Sum.inl (j, t)) <;> cases h2 : xb t <;> simp_all [b2z]

theorem cd_card_fun {k : ℕ} (L : Finset (Fin k)) : Nat.card (↥L → ZMod 2) = 2 ^ L.card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_coe]

theorem cd_card_sub {m : ℕ} (U : Submodule (ZMod 2) (Fin m → ZMod 2)) :
    Nat.card U = 2 ^ Module.finrank (ZMod 2) U := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp

theorem cd_card_two : Nat.card (Fin 2 → ZMod 2) = 2 ^ 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem cd_solE_bound {k m : ℕ} (L : Finset (Fin k)) (U : Submodule (ZMod 2) (Fin m → ZMod 2))
    (S : (EVis k m → ZMod 2) → Prop)
    (h1 : ∀ e, S e → ∀ q, q ∉ L → e (Sum.inl q) = 0)
    (h2 : ∀ e e', S e → S e' → (fun ρ => e (Sum.inr ρ)) - (fun ρ => e' (Sum.inr ρ)) ∈ U) :
    Nat.card {e // S e} ≤ 2 ^ (L.card + Module.finrank (ZMod 2) U) := by
  by_cases hne : Nonempty {e // S e}
  · obtain ⟨⟨e0, he0⟩⟩ := hne
    have hinj : Function.Injective (fun e : {e // S e} =>
        ((fun q : ↥L => e.1 (Sum.inl q.1)),
          (⟨(fun ρ => e.1 (Sum.inr ρ)) - (fun ρ => e0 (Sum.inr ρ)), h2 e.1 e0 e.2 he0⟩ : ↥U))) := by
      intro e e' h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      apply Subtype.ext
      funext j
      rcases j with q | ρ
      · by_cases hq : q ∈ L
        · exact congrFun h.1 ⟨q, hq⟩
        · rw [h1 _ e.2 q hq, h1 _ e'.2 q hq]
      · have := congrFun h.2 ρ
        simpa using this
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, cd_card_fun, cd_card_sub, ← pow_add] at this
    exact this
  · rw [not_nonempty_iff] at hne
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

theorem cd_solY_bound {k : ℕ} (D : Finset (Fin k)) (S : (YVis k → ZMod 2) → Prop)
    (h1 : ∀ e, S e → ∀ q, q ∉ D → e (Sum.inl q) = 0) :
    Nat.card {e // S e} ≤ 2 ^ (D.card + 2) := by
  have hinj : Function.Injective (fun e : {e // S e} =>
      ((fun q : ↥D => e.1 (Sum.inl q.1)), (fun a : Fin 2 => e.1 (Sum.inr a)))) := by
    intro e e' h
    simp only [Prod.mk.injEq] at h
    apply Subtype.ext
    funext j
    rcases j with q | a
    · by_cases hq : q ∈ D
      · exact congrFun h.1 ⟨q, hq⟩
      · rw [h1 _ e.2 q hq, h1 _ e'.2 q hq]
    · exact congrFun h.2 a
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, cd_card_fun, cd_card_two, ← pow_add] at this
  exact this

theorem cd_lo_mem {k m : ℕ} (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ)
    (c0 c1 : Fin k → ZMod 2) :
    (∑ j : Fin k, if j.val < i then
      (c0 j • vecN m (A (ord j)).val + c1 j • vecN m (B (ord j)).val) else 0) ∈
      spanLo k m A B ord i := by
  apply Submodule.sum_mem
  intro j _
  split_ifs with h
  · exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, Or.inl rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, Or.inr rfl⟩))
  · exact Submodule.zero_mem _

theorem cd_hi_mem {k m : ℕ} (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ)
    (c0 c1 : Fin k → ZMod 2) :
    (∑ j : Fin k, if i ≤ j.val then
      (c0 j • vecN m (A (ord j)).val + c1 j • vecN m (B (ord j)).val) else 0) ∈
      spanHi k m A B ord i := by
  apply Submodule.sum_mem
  intro j _
  split_ifs with h
  · exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, Or.inl rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, Or.inr rfl⟩))
  · exact Submodule.zero_mem _

theorem cd_diff {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : ℕ)
    (e e' : EVis k m → ZMod 2)
    (h : solS (HbE (encD nr nc cr cc A B ord y) i) e) (h' : solS (HbE (encD nr nc cr cc A B ord y) i) e') :
    (fun ρ => e (Sum.inr ρ)) - (fun ρ => e' (Sum.inr ρ)) ∈
      (spanLo k m A B ord i ⊓ spanHi k m A B ord i : Submodule (ZMod 2) (Fin m → ZMod 2)) := by
  obtain ⟨_, c0, c1, a1, a2⟩ := (ch_solE nr nc cr cc A B ord y i e).mp h
  obtain ⟨_, c0', c1', a1', a2'⟩ := (ch_solE nr nc cr cc A B ord y i e').mp h'
  refine ⟨?_, ?_⟩
  · rw [← a1, ← a1']
    exact Submodule.sub_mem _ (cd_lo_mem A B ord i c0 c1) (cd_lo_mem A B ord i c0' c1')
  · have hm := Submodule.sub_mem _ (cd_hi_mem A B ord i c0' c1') (cd_hi_mem A B ord i c0 c1)
    have he : (fun ρ => e (Sum.inr ρ)) - (fun ρ => e' (Sum.inr ρ)) =
        (∑ j : Fin k, if i ≤ j.val then
          (c0' j • vecN m (A (ord j)).val + c1' j • vecN m (B (ord j)).val) else 0) -
        (∑ j : Fin k, if i ≤ j.val then
          (c0 j • vecN m (A (ord j)).val + c1 j • vecN m (B (ord j)).val) else 0) := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm, a2, a2']
    rw [he]
    exact hm

theorem cd_live_sub {k r m : ℕ} (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : ℕ) (q : Fin k)
    (h : liveB (encD nr nc cr cc A B ord y) i q = true) :
    q ∈ poolLo k r m A B ord i ∩ poolHi k r m A B ord i := by
  unfold liveB at h
  rw [Bool.and_eq_true] at h
  exact Finset.mem_inter.mpr ⟨(ch_loB nr nc cr cc A B ord y i q).mp h.1,
    (ch_hiB nr nc cr cc A B ord y i q).mp h.2⟩

theorem cd_live_card {k r m : ℕ} (b : ℕ) (hk : 0 < k) (nr nc : Fin (2^k))
    (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (hp : passP k r m b A B ord) (i : ℕ) (hi : i ≤ k) :
    (Finset.univ.filter (fun q : Fin k => liveB (encD nr nc cr cc A B ord y) i q = true)).card +
      Module.finrank (ZMod 2)
        (spanLo k m A B ord i ⊓ spanHi k m A B ord i : Submodule (ZMod 2) (Fin m → ZMod 2)) ≤ b := by
  obtain ⟨_, hpass⟩ := (pass_iff k r m b hk A B ord).mp hp
  rcases Nat.lt_or_ge i k with hlt | hge
  · have h1 := hpass ⟨i, hlt⟩
    have h2 : (Finset.univ.filter (fun q : Fin k => liveB (encD nr nc cr cc A B ord y) i q = true)).card ≤
        ((poolLo k r m A B ord i ∩ poolHi k r m A B ord i) ∪
          scopeS k r m A B (ord ⟨i, hlt⟩)).card := by
      apply Finset.card_le_card
      intro q hq
      rw [Finset.mem_filter] at hq
      exact Finset.mem_union_left _ (cd_live_sub nr nc cr cc A B ord y i q hq.2)
    simp only at h1
    omega
  · have h0 : (Finset.univ.filter (fun q : Fin k => liveB (encD nr nc cr cc A B ord y) i q = true)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro q _ hq
      have := (Finset.mem_inter.mp (cd_live_sub nr nc cr cc A B ord y i q hq)).2
      unfold poolHi at this
      rw [Finset.mem_filter] at this
      obtain ⟨_, i', hi', _⟩ := this
      have := i'.isLt
      omega
    have hbot : spanHi k m A B ord i = ⊥ := by
      unfold spanHi
      rw [Submodule.span_eq_bot]
      rintro v ⟨i', hi', _⟩
      have := i'.isLt
      omega
    rw [h0, hbot, inf_bot_eq, finrank_bot]
    simp

theorem cd_nfE (k r m b : ℕ) (hk : 0 < k) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (hp : passP k r m b A B ord) (i : ℕ) (hi : i ≤ k)
    (hc : slE k m b (HbE (encD nr nc cr cc A B ord y) i) (Sum.inr (Sum.inr (Sum.inr ()))) = true) :
    nfE k m b (HbE (encD nr nc cr cc A B ord y) i) ≤ b := by
  have hcard := ((slE_spec k m b (HbE (encD nr nc cr cc A B ord y) i)).2 hc).1
  have hb := cd_solE_bound (Finset.univ.filter (fun q : Fin k => liveB (encD nr nc cr cc A B ord y) i q = true))
    (spanLo k m A B ord i ⊓ spanHi k m A B ord i) (solS (HbE (encD nr nc cr cc A B ord y) i))
    (fun e he q hq => ((ch_solE nr nc cr cc A B ord y i e).mp he).1 q (by simpa using hq))
    (fun e e' he he' => cd_diff nr nc cr cc A B ord y i e e' he he')
  rw [hcard] at hb
  have h3 := cd_live_card b hk nr nc cr cc A B ord y hp i hi
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp
    (hb.trans (Nat.pow_le_pow_right (by norm_num) h3))

theorem cd_D_card {k r m : ℕ} (b : ℕ) (hk : 0 < k) (nr nc : Fin (2^k))
    (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (hp : passP k r m b A B ord) (i : Fin k) :
    (Finset.univ.filter (fun q : Fin k => DB (encD nr nc cr cc A B ord y) i q = true)).card +
      Module.finrank (ZMod 2)
        (spanLo k m A B ord i.val ⊓ spanHi k m A B ord i.val :
          Submodule (ZMod 2) (Fin m → ZMod 2)) ≤ b := by
  obtain ⟨_, hpass⟩ := (pass_iff k r m b hk A B ord).mp hp
  have h1 := hpass i
  have h2 : (Finset.univ.filter (fun q : Fin k => DB (encD nr nc cr cc A B ord y) i q = true)).card ≤
      ((poolLo k r m A B ord i.val ∩ poolHi k r m A B ord i.val) ∪
        scopeS k r m A B (ord i)).card := by
    apply Finset.card_le_card
    intro q hq
    rw [Finset.mem_filter] at hq
    have hq2 := hq.2
    unfold DB at hq2
    rw [Bool.or_eq_true] at hq2
    rcases hq2 with h | h
    · exact Finset.mem_union_left _ (cd_live_sub nr nc cr cc A B ord y i.val q h)
    · exact Finset.mem_union_right _ ((ch_scB nr nc cr cc A B ord y i q).mp h)
  omega

theorem cd_Y (k r m b : ℕ) (hk : 0 < k) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (hp : passP k r m b A B ord) (i : Fin k) :
    slY k b (HbY (encD nr nc cr cc A B ord y) i) (Sum.inr (Sum.inr (Sum.inr ()))) = true ∧
    nfY k b (HbY (encD nr nc cr cc A B ord y) i) ≤ b + 2 := by
  have hcons : slY k b (HbY (encD nr nc cr cc A B ord y) i) (Sum.inr (Sum.inr (Sum.inr ()))) = true := by
    by_contra h
    rw [Bool.not_eq_true] at h
    exact (slY_spec k b (HbY (encD nr nc cr cc A B ord y) i)).1 h 0
      ((ch_solY (encD nr nc cr cc A B ord y) i 0).mpr (fun _ _ => rfl))
  refine ⟨hcons, ?_⟩
  have hcard := ((slY_spec k b (HbY (encD nr nc cr cc A B ord y) i)).2 hcons).1
  have hb := cd_solY_bound (Finset.univ.filter (fun q : Fin k => DB (encD nr nc cr cc A B ord y) i q = true))
    (solS (HbY (encD nr nc cr cc A B ord y) i))
    (fun e he q hq => (ch_solY (encD nr nc cr cc A B ord y) i e).mp he q (by simpa using hq))
  rw [hcard] at hb
  have h3 := cd_D_card b hk nr nc cr cc A B ord y hp i
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp
    (hb.trans (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem cd_lin_mem {k r m : ℕ} (b : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m)) (i : ℕ)
    (hsol : ∀ x, sOk (slE k m b (HbE (encD nr nc cr cc A B ord y) i)) x →
      solS (HbE (encD nr nc cr cc A B ord y) i) (sPt (slE k m b (HbE (encD nr nc cr cc A B ord y) i)) x))
    (x : Fin b → ZMod 2) (okx : sOk (slE k m b (HbE (encD nr nc cr cc A B ord y) i)) x) :
    (fun ρ : Fin m => ∑ t, b2z (slE k m b (HbE (encD nr nc cr cc A B ord y) i) (Sum.inl (Sum.inr ρ, t))) * x t) ∈
      (spanLo k m A B ord i ⊓ spanHi k m A B ord i : Submodule (ZMod 2) (Fin m → ZMod 2)) := by
  have h := cd_diff nr nc cr cc A B ord y i _ _ (hsol x okx) (hsol 0 (fun _ _ => rfl))
  convert h using 1
  funext ρ
  simp [sPt]

theorem cd_hom (k r m b : ℕ) (hk : 0 < k) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (hp : passP k r m b A B ord) (i : Fin k)
    (hc : slE k m b (HbE (encD nr nc cr cc A B ord y) i.val)
      (Sum.inr (Sum.inr (Sum.inr ()))) = true)
    (hc' : slE k m b (HbE (encD nr nc cr cc A B ord y) (i.val+1))
      (Sum.inr (Sum.inr (Sum.inr ()))) = true)
    (pin value : Fin k → Bool) (T : Fin (2^b) × Fin (k+1) → Bool) :
    Nat.card {p : (Fin b → ZMod 2) × (Fin (b+2) → ZMod 2) × (Fin b → ZMod 2) //
      jHom (jInp b (encD nr nc cr cc A B ord y) pin value i T) p.1 p.2.1 p.2.2} ≤ 2^(b+2) := by
  have hnE := cd_nfE k r m b hk nr nc cr cc A B ord y hp i.val (le_of_lt i.isLt) hc
  have hnE' := cd_nfE k r m b hk nr nc cr cc A B ord y hp (i.val+1) i.isLt hc'
  obtain ⟨hcY, hnY⟩ := cd_Y k r m b hk nr nc cr cc A B ord y hp i
  have hE := ((slE_spec k m b (HbE (encD nr nc cr cc A B ord y) i.val)).2 hc).2.2 hnE
  have hE' := ((slE_spec k m b (HbE (encD nr nc cr cc A B ord y) (i.val+1))).2 hc').2.2 hnE'
  have hY := ((slY_spec k b (HbY (encD nr nc cr cc A B ord y) i)).2 hcY).2.2 hnY
  have hinj : Function.Injective (fun p : {p : (Fin b → ZMod 2) × (Fin (b+2) → ZMod 2) ×
      (Fin b → ZMod 2) // jHom (jInp b (encD nr nc cr cc A B ord y) pin value i T) p.1 p.2.1 p.2.2} =>
      ((fun q : ↥(Finset.univ.filter (fun q : Fin k => DB (encD nr nc cr cc A B ord y) i q = true)) =>
          sPt (slY k b (HbY (encD nr nc cr cc A B ord y) i)) p.1.2.1 (Sum.inl q.1)),
        (fun a : Fin 2 => sPt (slY k b (HbY (encD nr nc cr cc A B ord y) i)) p.1.2.1 (Sum.inr a)),
        (⟨_, cd_lin_mem b nr nc cr cc A B ord y i.val hE.1 p.1.1
          ((ch_jHom b (encD nr nc cr cc A B ord y) pin value i T p.1.1 p.1.2.1 p.1.2.2).mp p.2).1⟩ :
          ↥(spanLo k m A B ord i.val ⊓ spanHi k m A B ord i.val :
            Submodule (ZMod 2) (Fin m → ZMod 2))))) := by
    intro p p' h
    obtain ⟨⟨x, yy, z⟩, hp1⟩ := p
    obtain ⟨⟨x', yy', z'⟩, hp2⟩ := p'
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨okx, oky, okz, ha, hb1, hs⟩ := (ch_jHom b (encD nr nc cr cc A B ord y) pin value i T x yy z).mp hp1
    obtain ⟨okx', oky', okz', ha', hb1', hs'⟩ := (ch_jHom b (encD nr nc cr cc A B ord y) pin value i T x' yy' z').mp hp2
    have hyy : yy = yy' := by
      apply hY.2.2 _ _ oky oky'
      funext j
      rcases j with q | a
      · by_cases hq : DB (encD nr nc cr cc A B ord y) i q = true
        · exact congrFun h1 ⟨q, by simpa using hq⟩
        · rw [Bool.not_eq_true] at hq
          rw [(ch_solY (encD nr nc cr cc A B ord y) i _).mp (hY.1 yy oky) q hq,
            (ch_solY (encD nr nc cr cc A B ord y) i _).mp (hY.1 yy' oky') q hq]
      · exact congrFun h2 a
    subst hyy
    have hx : x = x' := by
      apply hE.2.2 _ _ okx okx'
      funext j
      rcases j with q | ρ
      · by_cases hq : liveB (encD nr nc cr cc A B ord y) i.val q = true
        · simp only [sPt]
          rw [ha q hq, ha' q hq]
        · rw [Bool.not_eq_true] at hq
          rw [((ch_solE nr nc cr cc A B ord y i.val _).mp (hE.1 x okx)).1 q hq,
            ((ch_solE nr nc cr cc A B ord y i.val _).mp (hE.1 x' okx')).1 q hq]
      · simp only [sPt]
        rw [congrFun h3 ρ]
    subst hx
    have hz : z = z' := by
      apply hE'.2.2 _ _ okz okz'
      funext j
      rcases j with q | ρ
      · by_cases hq : liveB (encD nr nc cr cc A B ord y) (i.val+1) q = true
        · simp only [sPt]
          rw [hb1 q hq, hb1' q hq]
        · rw [Bool.not_eq_true] at hq
          rw [((ch_solE nr nc cr cc A B ord y (i.val+1) _).mp (hE'.1 z okz)).1 q hq,
            ((ch_solE nr nc cr cc A B ord y (i.val+1) _).mp (hE'.1 z' okz')).1 q hq]
      · simp only [sPt]
        congr 1
        have := (hs ρ).trans (hs' ρ).symm
        linear_combination this
    subst hz
    rfl
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_prod, cd_card_fun, cd_card_two, cd_card_sub, ← pow_add,
    ← pow_add] at hle
  have h3 := cd_D_card b hk nr nc cr cc A B ord y hp i
  exact hle.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem iv_b2z_inj (a b : Bool) (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h ⊢

theorem iv_two : (2 : ZMod 2) = 0 := by decide

theorem iv_vec_surj (n : ℕ) (x : Fin n → ZMod 2) : ∃ ix : Fin (2^n), vecN n ix.val = x := by
  obtain ⟨e, he⟩ := vecEquiv_exists n
  refine ⟨e.symm x, ?_⟩
  funext j
  have := he (e.symm x) j
  simp only [Equiv.apply_symm_apply] at this
  rw [this]; rfl

theorem iv_vec_inj (n : ℕ) (ix iy : Fin (2^n)) (h : vecN n ix.val = vecN n iy.val) : ix = iy :=
  Fin.ext (vecN_inj n _ _ ix.isLt iy.isLt h)

noncomputable def nsB {k m : ℕ} (lo pin value live : Fin k → Bool)
    (Phi : (Fin k → Bool) → Fin m → ZMod 2) (e : EVis k m → ZMod 2) (ω : Fin k → Bool) : Bool :=
  @decide ((∀ q, lo q = false → ω q = false) ∧
    (∀ q, lo q = true → pin q = true → ω q = value q) ∧
    (∀ q, live q = true → b2z (ω q) = e (Sum.inl q)) ∧
    Phi ω = fun ρ => e (Sum.inr ρ)) (Classical.propDecidable _)

noncomputable def NSetA {k m : ℕ} (lo pin value live : Fin k → Bool)
    (Phi : (Fin k → Bool) → Fin m → ZMod 2) (e : EVis k m → ZMod 2) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun ω => nsB lo pin value live Phi e ω = true)

theorem iv_mem {k m : ℕ} (lo pin value live : Fin k → Bool)
    (Phi : (Fin k → Bool) → Fin m → ZMod 2) (e : EVis k m → ZMod 2) (ω : Fin k → Bool) :
    ω ∈ NSetA lo pin value live Phi e ↔ ((∀ q, lo q = false → ω q = false) ∧
    (∀ q, lo q = true → pin q = true → ω q = value q) ∧
    (∀ q, live q = true → b2z (ω q) = e (Sum.inl q)) ∧
    Phi ω = fun ρ => e (Sum.inr ρ)) := by
  unfold NSetA nsB
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, decide_eq_true_eq]

def JSA {k m b : ℕ} (oE oE' : SOut (EVis k m) b → Bool) (oY : SOut (YVis k) (b+2) → Bool)
    (live live' : Fin k → Bool) (av bv : Fin m → ZMod 2)
    (x : Fin b → ZMod 2) (yy : Fin (b+2) → ZMod 2) (z : Fin b → ZMod 2) : Prop :=
  sOk oE x ∧ sOk oY yy ∧ sOk oE' z ∧
  (∀ q : Fin k, live q = true → sPt oE x (Sum.inl q) = sPt oY yy (Sum.inl q)) ∧
  (∀ q : Fin k, live' q = true → sPt oE' z (Sum.inl q) = sPt oY yy (Sum.inl q)) ∧
  (∀ ρ : Fin m, sPt oE x (Sum.inr ρ) + sPt oE' z (Sum.inr ρ) +
    sPt oY yy (Sum.inr 0) * av ρ + sPt oY yy (Sum.inr 1) * bv ρ = 0)

set_option maxHeartbeats 1600000 in
theorem iv_step {k m b : ℕ} (lo sc hi hi' pin value : Fin k → Bool)
    (hhi : ∀ q, hi' q = true → hi q = true) (hsc : ∀ q, sc q = true → hi q = true)
    (oE oE' : SOut (EVis k m) b → Bool) (oY : SOut (YVis k) (b+2) → Bool)
    (Phi phi : (Fin k → Bool) → Fin m → ZMod 2) (av bv : Fin m → ZMod 2)
    (sa sb : (Fin k → Bool) → Bool)
    (hphi : ∀ ω, phi ω = b2z (sa ω) • av + b2z (sb ω) • bv)
    (hPl : ∀ ω ω', (∀ q, lo q = true → ω q = ω' q) → Phi ω = Phi ω')
    (hpl : ∀ ω ω', (∀ q, sc q = true → ω q = ω' q) → phi ω = phi ω')
    (hE1 : ∀ x, sOk oE x → ∀ q, (lo q && hi q) = false → sPt oE x (Sum.inl q) = 0)
    (hE2 : ∀ (ω' : Fin k → Bool) (iz : Fin (2^b)), sOk oE' (vecN b iz.val) →
      ((fun ρ => Phi ω' ρ + phi ω' ρ) = fun ρ => sPt oE' (vecN b iz.val) (Sum.inr ρ)) →
      ∃ x, sOk oE x ∧ sPt oE x =
        (Sum.elim (fun q => if (lo q && hi q) = true then b2z (ω' q) else 0) (Phi ω')))
    (hE3 : ∀ x x', sOk oE x → sOk oE x' → sPt oE x = sPt oE x' → x = x')
    (hY1 : ∀ yy, sOk oY yy → ∀ q, ((lo q && hi q) || sc q) = false → sPt oY yy (Sum.inl q) = 0)
    (hY2 : ∀ e : YVis k → ZMod 2, (∀ q, ((lo q && hi q) || sc q) = false → e (Sum.inl q) = 0) →
      ∃ yy, sOk oY yy ∧ sPt oY yy = e)
    (hY3 : ∀ x x', sOk oY x → sOk oY x' → sPt oY x = sPt oY x' → x = x')
    (N : Fin (2^b) → ℕ)
    (hN : ∀ ix : Fin (2^b), sOk oE (vecN b ix.val) →
      N ix = (NSetA lo pin value (fun q => lo q && hi q) Phi (sPt oE (vecN b ix.val))).card)
    (G : Fin (2^(b+2)) → Bool) (τB : Fin (2^(b+2)) → Fin k → Bool)
    (hτ : ∀ iy q, b2z (τB iy q) = sPt oY (vecN (b+2) iy.val) (Sum.inl q))
    (hG : ∀ iy, G iy = true ↔ (sPt oY (vecN (b+2) iy.val) (Sum.inr 0) = b2z (sa (τB iy)) ∧
      sPt oY (vecN (b+2) iy.val) (Sum.inr 1) = b2z (sb (τB iy)) ∧
      ∀ q, ((lo q && hi q) || sc q) = true → pin q = true → τB iy q = value q))
    (iz : Fin (2^b)) (hz : sOk oE' (vecN b iz.val)) :
    (∑ ix : Fin (2^b), ∑ iy : Fin (2^(b+2)),
      @ite ℕ (JSA oE oE' oY (fun q => lo q && hi q) (fun q => (lo q || sc q) && hi' q) av bv
        (vecN b ix.val) (vecN (b+2) iy.val) (vecN b iz.val)) (Classical.propDecidable _)
        (N ix * (if G iy = true then 1 else 0)) 0) =
      (NSetA (fun q => lo q || sc q) pin value (fun q => (lo q || sc q) && hi' q)
        (fun ω ρ => Phi ω ρ + phi ω ρ) (sPt oE' (vecN b iz.val))).card := by
  classical
  have hterm : ∀ (ix : Fin (2^b)) (iy : Fin (2^(b+2))),
      @ite ℕ (JSA oE oE' oY (fun q => lo q && hi q) (fun q => (lo q || sc q) && hi' q) av bv
        (vecN b ix.val) (vecN (b+2) iy.val) (vecN b iz.val)) (Classical.propDecidable _)
        (N ix * (if G iy = true then 1 else 0)) 0 =
      if (JSA oE oE' oY (fun q => lo q && hi q) (fun q => (lo q || sc q) && hi' q) av bv
        (vecN b ix.val) (vecN (b+2) iy.val) (vecN b iz.val) ∧ G iy = true) then
        (NSetA lo pin value (fun q => lo q && hi q) Phi (sPt oE (vecN b ix.val))).card else 0 := by
    intro ix iy
    by_cases h1 : JSA oE oE' oY (fun q => lo q && hi q) (fun q => (lo q || sc q) && hi' q) av bv
        (vecN b ix.val) (vecN (b+2) iy.val) (vecN b iz.val)
    · by_cases h2 : G iy = true
      · rw [if_pos h1, if_pos h2, mul_one, if_pos (And.intro h1 h2)]
        exact hN ix h1.1
      · rw [if_pos h1, if_neg h2, mul_zero, if_neg (not_and_of_not_right _ h2)]
    · rw [if_neg h1, if_neg (not_and_of_not_left _ h1)]
  simp only [hterm]
  rw [← Finset.sum_product' Finset.univ Finset.univ (fun (ix : Fin (2^b)) (iy : Fin (2^(b+2))) =>
    if (JSA oE oE' oY (fun q => lo q && hi q) (fun q => (lo q || sc q) && hi' q) av bv
        (vecN b ix.val) (vecN (b+2) iy.val) (vecN b iz.val) ∧ G iy = true) then
        (NSetA lo pin value (fun q => lo q && hi q) Phi (sPt oE (vecN b ix.val))).card else 0)]
  rw [← Finset.sum_filter, ← Finset.card_sigma]
  refine Finset.card_bij (fun a _ => fun q => if lo q = true then a.2 q else τB a.1.2 q) ?_ ?_ ?_
  ·
    rintro ⟨⟨ix, iy⟩, ω⟩ ha
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at ha
    obtain ⟨⟨hJ, hGt⟩, hω⟩ := ha
    obtain ⟨hx, hy, hz', ha', hc', hd⟩ := hJ
    obtain ⟨g0, g1, gp⟩ := (hG iy).1 hGt
    obtain ⟨w1, w2, w3, w4⟩ := (iv_mem _ _ _ _ _ _ _).1 hω
    have K : ∀ q, lo q = true → hi q = true → ω q = τB iy q := by
      intro q h1 h2
      apply iv_b2z_inj
      rw [w3 q (by simp [h1, h2]), hτ iy q]
      exact ha' q (by simp [h1, h2])
    have K0 : ∀ q, ((lo q && hi q) || sc q) = false → τB iy q = false := by
      intro q h1
      apply iv_b2z_inj
      rw [hτ iy q, hY1 _ hy q h1]; rfl
    refine (iv_mem _ _ _ _ _ _ _).2 ⟨?_, ?_, ?_, ?_⟩
    · intro q hq
      have h1 : lo q = false := by cases hl : lo q <;> simp_all
      have h2 : sc q = false := by cases hl : sc q <;> simp_all
      show (if lo q = true then ω q else τB iy q) = false
      rw [if_neg (by simp [h1])]
      exact K0 q (by simp [h1, h2])
    · intro q hq hpin
      show (if lo q = true then ω q else τB iy q) = value q
      by_cases hl : lo q = true
      · rw [if_pos hl]; exact w2 q hl hpin
      · rw [if_neg hl]
        have h2 : sc q = true := by cases hs : sc q <;> simp_all
        exact gp q (by simp [h2]) hpin
    · intro q hq
      have hq1 : (lo q || sc q) = true := by cases h : (lo q || sc q) <;> simp_all
      have hq2 : hi' q = true := by cases h : hi' q <;> simp_all
      show b2z (if lo q = true then ω q else τB iy q) = _
      rw [hc' q hq, ← hτ iy q]
      by_cases hl : lo q = true
      · rw [if_pos hl, K q hl (hhi q hq2)]
      · rw [if_neg hl]
    · have e1 : Phi (fun q => if lo q = true then ω q else τB iy q) = Phi ω :=
        hPl _ _ (fun q hq => by simp [hq])
      have e2 : phi (fun q => if lo q = true then ω q else τB iy q) = phi (τB iy) :=
        hpl _ _ (fun q hq => by
          by_cases hl : lo q = true
          · simp only [if_pos hl]; exact K q hl (hsc q hq)
          · simp only [if_neg hl])
      funext ρ
      show Phi (fun q => if lo q = true then ω q else τB iy q) ρ +
        phi (fun q => if lo q = true then ω q else τB iy q) ρ = _
      rw [e1, e2, hphi]
      have h4 := congrFun w4 ρ
      have h5 := hd ρ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← g0, ← g1]
      linear_combination h4 + h5 - (sPt oE' (vecN b iz.val) (Sum.inr ρ)) * iv_two
  ·
    rintro ⟨⟨ix, iy⟩, ω⟩ ha ⟨⟨ix', iy'⟩, ω'⟩ ha' heq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at ha ha'
    obtain ⟨⟨⟨hx, hy, -, haa, -, -⟩, hGt⟩, hω⟩ := ha
    obtain ⟨⟨⟨hx', hy', -, haa', -, -⟩, hGt'⟩, hω'⟩ := ha'
    obtain ⟨g0, g1, -⟩ := (hG iy).1 hGt
    obtain ⟨g0', g1', -⟩ := (hG iy').1 hGt'
    obtain ⟨w1, -, w3, w4⟩ := (iv_mem _ _ _ _ _ _ _).1 hω
    obtain ⟨w1', -, w3', w4'⟩ := (iv_mem _ _ _ _ _ _ _).1 hω'
    have hq : ∀ q, (if lo q = true then ω q else τB iy q) =
        (if lo q = true then ω' q else τB iy' q) := fun q => congrFun heq q
    have hωe : ω = ω' := by
      funext q
      by_cases hl : lo q = true
      · have := hq q; rwa [if_pos hl, if_pos hl] at this
      · have hl' : lo q = false := by simpa using hl
        rw [w1 q hl', w1' q hl']
    subst hωe
    have hτe : τB iy = τB iy' := by
      funext q
      by_cases hl : lo q = true
      · by_cases hh : hi q = true
        · have a1 : ω q = τB iy q := by
            apply iv_b2z_inj
            rw [w3 q (by simp [hl, hh]), hτ iy q]
            exact haa q (by simp [hl, hh])
          have a2 : ω q = τB iy' q := by
            apply iv_b2z_inj
            rw [w3' q (by simp [hl, hh]), hτ iy' q]
            exact haa' q (by simp [hl, hh])
          rw [← a1, ← a2]
        · have hs : sc q = false := by
            cases hs : sc q
            · rfl
            · exact absurd (hsc q hs) hh
          have hh' : hi q = false := by simpa using hh
          have b1 : τB iy q = false := by
            apply iv_b2z_inj
            rw [hτ iy q, hY1 _ hy q (by simp [hh', hs])]; rfl
          have b2 : τB iy' q = false := by
            apply iv_b2z_inj
            rw [hτ iy' q, hY1 _ hy' q (by simp [hh', hs])]; rfl
          rw [b1, b2]
      · have := hq q; rwa [if_neg hl, if_neg hl] at this
    have hye : iy = iy' := by
      apply iv_vec_inj
      apply hY3 _ _ hy hy'
      funext j
      rcases j with q | t
      · rw [← hτ iy q, ← hτ iy' q, hτe]
      · fin_cases t
        · exact g0.trans (by rw [hτe]; exact g0'.symm)
        · exact g1.trans (by rw [hτe]; exact g1'.symm)
    subst hye
    have hxe : ix = ix' := by
      apply iv_vec_inj
      apply hE3 _ _ hx hx'
      funext j
      rcases j with q | ρ
      · by_cases hl : (lo q && hi q) = true
        · rw [← w3 q hl, ← w3' q hl]
        · have hl' : (lo q && hi q) = false := by simpa using hl
          rw [hE1 _ hx q hl', hE1 _ hx' q hl']
      · exact (congrFun w4 ρ).symm.trans (congrFun w4' ρ)
    subst hxe
    rfl
  ·
    intro ω' hω'
    obtain ⟨v1, v2, v3, v4⟩ := (iv_mem _ _ _ _ _ _ _).1 hω'
    obtain ⟨yy, hyy, hyp⟩ := hY2
      (Sum.elim (fun q => b2z (((lo q && hi q) || sc q) && ω' q))
        (fun t => if t = 0 then b2z (sa (fun q => ((lo q && hi q) || sc q) && ω' q))
          else b2z (sb (fun q => ((lo q && hi q) || sc q) && ω' q))))
      (fun q hq => by
        show b2z (((lo q && hi q) || sc q) && ω' q) = 0
        rw [hq]; rfl)
    obtain ⟨iy, rfl⟩ := iv_vec_surj (b+2) yy
    have hτf : τB iy = fun q => ((lo q && hi q) || sc q) && ω' q := by
      funext q
      apply iv_b2z_inj
      rw [hτ iy q, hyp]; rfl
    have hphi' : phi ω' = phi (τB iy) := hpl _ _ (fun q hq => by rw [hτf]; simp [hq])
    obtain ⟨x, hxx, hxp⟩ := hE2 ω' iz hz v4
    obtain ⟨ix, rfl⟩ := iv_vec_surj b x
    have hPhi' : Phi (fun q => lo q && ω' q) = Phi ω' := hPl _ _ (fun q hq => by simp [hq])
    refine ⟨⟨(ix, iy), fun q => lo q && ω' q⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and]
      refine ⟨⟨⟨hxx, hyy, hz, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · intro q hq
        rw [hxp, hyp]
        simp only [Sum.elim_inl]
        rw [if_pos hq]
        simp [hq]
      · intro q hq
        have hq1 : (lo q || sc q) = true := by cases h : (lo q || sc q) <;> simp_all
        have hq2 : hi' q = true := by cases h : hi' q <;> simp_all
        have hh : hi q = true := hhi q hq2
        rw [← v3 q hq, hyp]
        simp only [Sum.elim_inl]
        have : ((lo q && hi q) || sc q) = true := by
          cases hl : lo q <;> cases hs : sc q <;> simp_all
        rw [this]; simp
      · intro ρ
        have h4 := congrFun v4 ρ
        rw [hxp, hyp]
        simp only [Sum.elim_inr, Sum.elim_inl]
        have h6 : phi ω' ρ = b2z (sa (τB iy)) * av ρ + b2z (sb (τB iy)) * bv ρ := by
          rw [hphi', hphi]; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hτf] at h6
        have h01 : ((1 : Fin 2) = 0) = False := by simp
        simp only [if_true, h01, if_false]
        linear_combination (-1 : ZMod 2) * h4 - h6 + (Phi ω' ρ + phi ω' ρ) * iv_two
      · rw [hG]
        refine ⟨?_, ?_, ?_⟩
        · rw [hyp, hτf]; simp
        · rw [hyp, hτf]; simp
        · intro q hq hpin
          rw [hτf]
          simp only [hq, Bool.true_and]
          have : (lo q || sc q) = true := by
            cases hl : lo q <;> cases hs : sc q <;> simp_all
          exact v2 q this hpin
      · refine (iv_mem _ _ _ _ _ _ _).2 ⟨?_, ?_, ?_, ?_⟩
        · intro q hq; simp [hq]
        · intro q hq hpin
          simp only [hq, Bool.true_and]
          exact v2 q (by simp [hq]) hpin
        · intro q hq
          rw [hxp]
          simp only [Sum.elim_inl]
          rw [if_pos hq]
          have : lo q = true := by cases hl : lo q <;> simp_all
          simp [this]
        · rw [hPhi', hxp]; rfl
    · funext q
      show (if lo q = true then (lo q && ω' q) else τB iy q) = ω' q
      by_cases hl : lo q = true
      · rw [if_pos hl]; simp [hl]
      · rw [if_neg hl, hτf]
        have hl' : lo q = false := by simpa using hl
        cases hs : sc q
        · have := v1 q (by simp [hl', hs])
          simp [hl', hs, this]
        · simp [hl', hs]

noncomputable def PhiS (k r m : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ) (ω : Fin k → Bool) :
    Fin m → ZMod 2 :=
  ∑ j : Fin k, if j.val < i then phiS k r m nr nc cr cc A B (ord j) ω else 0

theorem iw_lo_succ {k r m : ℕ} (d : Dat k r m → Bool) (i : ℕ) (h : i < k) (q : Fin k) :
    loB d (i+1) q = (loB d i q || scB d ⟨i, h⟩ q) := by
  unfold loB
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨i', h1, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h3 | h3
    · exact Or.inl ⟨i', h3, h2⟩
    · have : i' = ⟨i, h⟩ := Fin.ext h3
      subst this
      exact Or.inr h2
  · rintro (⟨i', h1, h2⟩ | h2)
    · exact ⟨i', Nat.lt_succ_of_lt h1, h2⟩
    · exact ⟨⟨i, h⟩, Nat.lt_succ_self i, h2⟩

theorem iw_hi_mono {k r m : ℕ} (d : Dat k r m → Bool) (i : ℕ) (q : Fin k)
    (h : hiB d (i+1) q = true) : hiB d i q = true := by
  unfold hiB at h ⊢
  simp only [decide_eq_true_eq] at h ⊢
  obtain ⟨i', h1, h2⟩ := h
  exact ⟨i', by omega, h2⟩

theorem iw_sc_hi {k r m : ℕ} (d : Dat k r m → Bool) (i : ℕ) (h : i < k) (q : Fin k)
    (hs : scB d ⟨i, h⟩ q = true) : hiB d i q = true := by
  unfold hiB
  simp only [decide_eq_true_eq]
  exact ⟨⟨i, h⟩, le_refl _, hs⟩

theorem iw_Phi_succ (k r m : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (i : ℕ) (h : i < k) (ω : Fin k → Bool) :
    PhiS k r m nr nc cr cc A B ord (i+1) ω =
      PhiS k r m nr nc cr cc A B ord i ω + phiS k r m nr nc cr cc A B (ord ⟨i, h⟩) ω := by
  unfold PhiS
  have h1 : ∀ j : Fin k, (if j.val < i + 1 then phiS k r m nr nc cr cc A B (ord j) ω else 0) =
      (if j.val < i then phiS k r m nr nc cr cc A B (ord j) ω else 0) +
      (if j = ⟨i, h⟩ then phiS k r m nr nc cr cc A B (ord j) ω else 0) := by
    intro j
    by_cases h2 : j.val < i
    · have h3 : j ≠ ⟨i, h⟩ := fun e => by rw [e] at h2; exact lt_irrefl _ h2
      rw [if_pos h2, if_pos (Nat.lt_succ_of_lt h2), if_neg h3, add_zero]
    · by_cases h3 : j = ⟨i, h⟩
      · subst h3
        rw [if_pos (Nat.lt_succ_self i), if_neg h2, if_pos rfl, zero_add]
      · have h4 : ¬ j.val < i + 1 := by
          intro h5
          apply h3
          apply Fin.ext
          show j.val = i
          omega
        rw [if_neg h4, if_neg h2, if_neg h3, add_zero]
  simp only [h1]
  rw [Finset.sum_add_distrib]
  congr 1
  simp

theorem iw_Phi_local (k r m : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (nr nc : Fin (2^k))
    (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (i : ℕ) (ω ω' : Fin k → Bool)
    (h : ∀ q, loB (encD nr nc cr cc A B ord y) i q = true → ω q = ω' q) :
    PhiS k r m nr nc cr cc A B ord i ω = PhiS k r m nr nc cr cc A B ord i ω' := by
  unfold PhiS
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < i
  · rw [if_pos hj, if_pos hj]
    apply ch_phi_local k r m hk hr
    intro q hq
    apply h
    rw [ch_loB]
    unfold poolLo
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, j, hj, hq⟩
  · rw [if_neg hj, if_neg hj]

theorem iw_tab_one {t : ℕ} (g : Bool) :
    tabN (fun j : Fin (t+1) => decide (j.val = 0) && g) = if g = true then 1 else 0 := by
  unfold tabN
  rw [Finset.sum_eq_single (⟨0, Nat.succ_pos t⟩ : Fin (t+1))]
  · cases g <;> simp
  · intro j _ hj
    have : j.val ≠ 0 := fun e => hj (Fin.ext e)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem iw_E2 (k r m b : ℕ) (nr nc : Fin (2^k))
    (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (i : ℕ) (h : i < k)
    (hc : slE k m b (HbE (encD nr nc cr cc A B ord y) i) (Sum.inr (Sum.inr (Sum.inr ()))) = true)
    (hn : nfE k m b (HbE (encD nr nc cr cc A B ord y) i) ≤ b)
    (hc' : slE k m b (HbE (encD nr nc cr cc A B ord y) (i+1))
      (Sum.inr (Sum.inr (Sum.inr ()))) = true)
    (hn' : nfE k m b (HbE (encD nr nc cr cc A B ord y) (i+1)) ≤ b)
    (ω' : Fin k → Bool) (z : Fin b → ZMod 2)
    (hz : sOk (slE k m b (HbE (encD nr nc cr cc A B ord y) (i+1))) z)
    (hs : (fun ρ => PhiS k r m nr nc cr cc A B ord i ω' ρ +
        phiS k r m nr nc cr cc A B (ord ⟨i, h⟩) ω' ρ) =
      fun ρ => sPt (slE k m b (HbE (encD nr nc cr cc A B ord y) (i+1))) z (Sum.inr ρ)) :
    ∃ x, sOk (slE k m b (HbE (encD nr nc cr cc A B ord y) i)) x ∧
      sPt (slE k m b (HbE (encD nr nc cr cc A B ord y) i)) x =
        (Sum.elim (fun q => if liveB (encD nr nc cr cc A B ord y) i q = true
          then b2z (ω' q) else 0) (PhiS k r m nr nc cr cc A B ord i ω')) := by
  obtain ⟨hA', -, -⟩ := ((slE_spec k m b (HbE (encD nr nc cr cc A B ord y) (i+1))).2 hc').2.2 hn'
  obtain ⟨-, hB, -⟩ := ((slE_spec k m b (HbE (encD nr nc cr cc A B ord y) i)).2 hc).2.2 hn
  obtain ⟨-, c0', c1', -, h2⟩ := (ch_solE nr nc cr cc A B ord y (i+1) _).1 (hA' z hz)
  apply hB
  rw [ch_solE]
  refine ⟨fun q hq => by simp [hq],
    fun j => if j.val ≤ i then b2z (sSen k r nr nc cr cc false (ord j) ω') else c0' j,
    fun j => if j.val ≤ i then b2z (sSen k r nr nc cr cc true (ord j) ω') else c1' j, ?_, ?_⟩
  · show _ = PhiS k r m nr nc cr cc A B ord i ω'
    unfold PhiS
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    by_cases hj : j.val < i
    · rw [if_pos hj, if_pos hj, if_pos (le_of_lt hj), if_pos (le_of_lt hj)]
      rfl
    · rw [if_neg hj, if_neg hj]
  · have hterm : ∀ j : Fin k,
        (if i ≤ j.val then
          ((if j.val ≤ i then b2z (sSen k r nr nc cr cc false (ord j) ω') else c0' j) •
            vecN m (A (ord j)).val +
          (if j.val ≤ i then b2z (sSen k r nr nc cr cc true (ord j) ω') else c1' j) •
            vecN m (B (ord j)).val) else 0) =
        (if j = ⟨i, h⟩ then phiS k r m nr nc cr cc A B (ord j) ω' else 0) +
        (if i + 1 ≤ j.val then (c0' j • vecN m (A (ord j)).val + c1' j • vecN m (B (ord j)).val)
          else 0) := by
      intro j
      by_cases h3 : j = ⟨i, h⟩
      · subst h3
        rw [if_pos (le_refl _), if_pos (le_refl _), if_pos (le_refl _), if_pos rfl,
          if_neg (Nat.not_succ_le_self i), add_zero]
        rfl
      · by_cases h4 : i ≤ j.val
        · have h5 : i + 1 ≤ j.val := by
            rcases Nat.lt_or_eq_of_le h4 with h6 | h6
            · exact h6
            · exact absurd (Fin.ext h6.symm) h3
          have h7 : ¬ j.val ≤ i := by omega
          rw [if_pos h4, if_neg h7, if_neg h7, if_neg h3, if_pos h5, zero_add]
        · have h5 : ¬ i + 1 ≤ j.val := by omega
          rw [if_neg h4, if_neg h3, if_neg h5, add_zero]
    have hsum : (∑ x : Fin k, if x = ⟨i, h⟩ then phiS k r m nr nc cr cc A B (ord x) ω' else 0) =
        phiS k r m nr nc cr cc A B (ord ⟨i, h⟩) ω' := by simp
    dsimp only
    simp only [hterm]
    rw [Finset.sum_add_distrib, hsum]
    show _ + _ + PhiS k r m nr nc cr cc A B ord i ω' = _
    rw [← h2, ← hs]
    funext ρ
    simp only [Pi.add_apply]
    ring

theorem iw_gT (k r m b : ℕ) (nr nc : Fin (2^k))
    (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (pin value : Fin k → Bool) (i : Fin k) (iy : Fin (2^(b+2))) :
    gT b (encD nr nc cr cc A B ord y) pin value i iy = true ↔
      (sPt (slY k b (HbY (encD nr nc cr cc A B ord y) i)) (vecN (b+2) iy.val) (Sum.inr 0) =
        b2z (sSen k r nr nc cr cc false (ord i)
          (fun q => sPtB (slY k b (HbY (encD nr nc cr cc A B ord y) i))
            (fun t => iy.val.testBit t.val) (Sum.inl q))) ∧
      sPt (slY k b (HbY (encD nr nc cr cc A B ord y) i)) (vecN (b+2) iy.val) (Sum.inr 1) =
        b2z (sSen k r nr nc cr cc true (ord i)
          (fun q => sPtB (slY k b (HbY (encD nr nc cr cc A B ord y) i))
            (fun t => iy.val.testBit t.val) (Sum.inl q))) ∧
      ∀ q, ((loB (encD nr nc cr cc A B ord y) i.val q && hiB (encD nr nc cr cc A B ord y) i.val q)
          || scB (encD nr nc cr cc A B ord y) i q) = true → pin q = true →
        sPtB (slY k b (HbY (encD nr nc cr cc A B ord y) i))
          (fun t => iy.val.testBit t.val) (Sum.inl q) = value q) := by
  have F0 : ∀ j : YVis k, b2z (sPtB (slY k b (HbY (encD nr nc cr cc A B ord y) i))
      (fun t => iy.val.testBit t.val) j) =
      sPt (slY k b (HbY (encD nr nc cr cc A B ord y) i)) (vecN (b+2) iy.val) j := by
    intro j
    rw [ch_sPtB]; rfl
  unfold gT
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨e0, e1⟩, e2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← F0, e0, ch_senB]
    · rw [← F0, e1, ch_senB]
    · intro q hq hpin
      exact e2 q (by rw [Bool.and_eq_true]; exact ⟨hq, hpin⟩)
  · rintro ⟨e0, e1, e2⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply iv_b2z_inj
      rw [F0, e0, ch_senB]
    · apply iv_b2z_inj
      rw [F0, e1, ch_senB]
    · intro q hq
      rw [Bool.and_eq_true] at hq
      exact e2 q hq.1 hq.2

set_option maxHeartbeats 1600000 in
theorem iw_inv (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (nr nc : Fin (2^k))
    (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (hp : passP k r m b A B ord) (pin value : Fin k → Bool)
    (hall : ∀ i : ℕ, i ≤ k → slE k m b (HbE (encD nr nc cr cc A B ord y) i)
      (Sum.inr (Sum.inr (Sum.inr ()))) = true) :
    ∀ i : ℕ, i ≤ k → ∀ ix : Fin (2^b),
      sOk (slE k m b (HbE (encD nr nc cr cc A B ord y) i)) (vecN b ix.val) →
      tabN (fun j => tblT b (encD nr nc cr cc A B ord y) pin value i (ix, j)) =
        (NSetA (loB (encD nr nc cr cc A B ord y) i) pin value
          (liveB (encD nr nc cr cc A B ord y) i) (PhiS k r m nr nc cr cc A B ord i)
          (sPt (slE k m b (HbE (encD nr nc cr cc A B ord y) i)) (vecN b ix.val))).card := by
  intro i
  induction i with
  | zero =>
    intro _ ix hx
    have hc := hall 0 (Nat.zero_le _)
    have hn := cd_nfE k r m b hk nr nc cr cc A B ord y hp 0 (Nat.zero_le _) hc
    obtain ⟨hEA, -, -⟩ := ((slE_spec k m b (HbE (encD nr nc cr cc A B ord y) 0)).2 hc).2.2 hn
    obtain ⟨-, c0, c1, h1, -⟩ := (ch_solE nr nc cr cc A B ord y 0 _).1 (hEA _ hx)
    have hlo : ∀ q, loB (encD nr nc cr cc A B ord y) 0 q = false := by
      intro q; unfold loB; simp
    have hset : NSetA (loB (encD nr nc cr cc A B ord y) 0) pin value
        (liveB (encD nr nc cr cc A B ord y) 0) (PhiS k r m nr nc cr cc A B ord 0)
        (sPt (slE k m b (HbE (encD nr nc cr cc A B ord y) 0)) (vecN b ix.val)) =
        {fun _ => false} := by
      ext ω
      rw [iv_mem, Finset.mem_singleton]
      constructor
      · rintro ⟨w1, -, -, -⟩
        funext q
        exact w1 q (hlo q)
      · rintro rfl
        refine ⟨fun _ _ => rfl, fun q hq => by rw [hlo q] at hq; exact absurd hq (by simp),
          fun q hq => by unfold liveB at hq; rw [hlo q] at hq; exact absurd hq (by simp), ?_⟩
        rw [← h1]
        unfold PhiS
        simp
    rw [hset, Finset.card_singleton]
    show tabN (fun j : Fin (k+1) => decide (j.val = 0)) = 1
    have := iw_tab_one (t := k) true
    simpa using this
  | succ i ih =>
    intro hi iz hz
    have h : i < k := hi
    have hc := hall i (le_of_lt h)
    have hc' := hall (i+1) hi
    have hn := cd_nfE k r m b hk nr nc cr cc A B ord y hp i (le_of_lt h) hc
    have hn' := cd_nfE k r m b hk nr nc cr cc A B ord y hp (i+1) hi hc'
    obtain ⟨hEA, -, hEC⟩ := ((slE_spec k m b (HbE (encD nr nc cr cc A B ord y) i)).2 hc).2.2 hn
    obtain ⟨hcY, hnY⟩ := cd_Y k r m b hk nr nc cr cc A B ord y hp ⟨i, h⟩
    obtain ⟨hYA, hYB, hYC⟩ :=
      ((slY_spec k b (HbY (encD nr nc cr cc A B ord y) ⟨i, h⟩)).2 hcY).2.2 hnY
    have key := iv_step (loB (encD nr nc cr cc A B ord y) i)
      (scB (encD nr nc cr cc A B ord y) ⟨i, h⟩) (hiB (encD nr nc cr cc A B ord y) i)
      (hiB (encD nr nc cr cc A B ord y) (i+1)) pin value
      (fun q hq => iw_hi_mono _ i q hq) (fun q hq => iw_sc_hi _ i h q hq)
      (slE k m b (HbE (encD nr nc cr cc A B ord y) i))
      (slE k m b (HbE (encD nr nc cr cc A B ord y) (i+1)))
      (slY k b (HbY (encD nr nc cr cc A B ord y) ⟨i, h⟩))
      (PhiS k r m nr nc cr cc A B ord i) (phiS k r m nr nc cr cc A B (ord ⟨i, h⟩))
      (vecN m (A (ord ⟨i, h⟩)).val) (vecN m (B (ord ⟨i, h⟩)).val)
      (sSen k r nr nc cr cc false (ord ⟨i, h⟩)) (sSen k r nr nc cr cc true (ord ⟨i, h⟩))
      (fun ω => rfl)
      (fun ω ω' hω => iw_Phi_local k r m hk hr nr nc cr cc A B ord y i ω ω' hω)
      (fun ω ω' hω => ch_phi_local k r m hk hr nr nc cr cc A B (ord ⟨i, h⟩) ω ω'
        (fun q hq => hω q ((ch_scB nr nc cr cc A B ord y ⟨i, h⟩ q).2 hq)))
      (fun x hx q hq => ((ch_solE nr nc cr cc A B ord y i _).1 (hEA x hx)).1 q hq)
      (fun ω' iz' hz' hs => iw_E2 k r m b nr nc cr cc A B ord y i h hc hn hc' hn' ω' _ hz' hs)
      hEC
      (fun yy hyy q hq => (ch_solY _ ⟨i, h⟩ _).1 (hYA yy hyy) q hq)
      (fun e he => hYB e ((ch_solY _ ⟨i, h⟩ _).2 he))
      hYC
      (fun ix => tabN (fun j => tblT b (encD nr nc cr cc A B ord y) pin value i (ix, j)))
      (fun ix hx => ih (le_of_lt h) ix hx)
      (gT b (encD nr nc cr cc A B ord y) pin value ⟨i, h⟩)
      (fun iy q => sPtB (slY k b (HbY (encD nr nc cr cc A B ord y) ⟨i, h⟩))
        (fun t => iy.val.testBit t.val) (Sum.inl q))
      (fun iy q => by rw [ch_sPtB]; rfl)
      (fun iy => iw_gT k r m b nr nc cr cc A B ord y pin value ⟨i, h⟩ iy)
      iz hz
    have e1 : loB (encD nr nc cr cc A B ord y) (i+1) = fun q =>
        loB (encD nr nc cr cc A B ord y) i q || scB (encD nr nc cr cc A B ord y) ⟨i, h⟩ q :=
      funext (fun q => iw_lo_succ _ i h q)
    have e2 : liveB (encD nr nc cr cc A B ord y) (i+1) = fun q =>
        (loB (encD nr nc cr cc A B ord y) i q || scB (encD nr nc cr cc A B ord y) ⟨i, h⟩ q) &&
          hiB (encD nr nc cr cc A B ord y) (i+1) q :=
      funext (fun q => by unfold liveB; rw [iw_lo_succ _ i h q])
    have e3 : PhiS k r m nr nc cr cc A B ord (i+1) = fun ω ρ =>
        PhiS k r m nr nc cr cc A B ord i ω ρ + phiS k r m nr nc cr cc A B (ord ⟨i, h⟩) ω ρ :=
      funext (fun ω => by rw [iw_Phi_succ k r m nr nc cr cc A B ord i h ω]; rfl)
    rw [← e2, ← e1, ← e3] at key
    have htbl : tblT b (encD nr nc cr cc A B ord y) pin value (i+1) =
        stepT b (encD nr nc cr cc A B ord y) pin value ⟨i, h⟩
          (tblT b (encD nr nc cr cc A B ord y) pin value i) := by
      show (if h : i < k then _ else _) = _
      rw [dif_pos h]
    have hbit : ∀ j : Fin (k+1), tblT b (encD nr nc cr cc A B ord y) pin value (i+1) (iz, j) =
        (jTot (jInp b (encD nr nc cr cc A B ord y) pin value ⟨i, h⟩
          (tblT b (encD nr nc cr cc A B ord y) pin value i)) iz).testBit j.val := by
      intro j
      rw [htbl]
      exact jnF_spec k m b _
        (cd_hom k r m b hk nr nc cr cc A B ord y hp ⟨i, h⟩ hc hc' pin value _) iz j
    have hJ : jTot (jInp b (encD nr nc cr cc A B ord y) pin value ⟨i, h⟩
          (tblT b (encD nr nc cr cc A B ord y) pin value i)) iz =
        (NSetA (loB (encD nr nc cr cc A B ord y) (i+1)) pin value
          (liveB (encD nr nc cr cc A B ord y) (i+1)) (PhiS k r m nr nc cr cc A B ord (i+1))
          (sPt (slE k m b (HbE (encD nr nc cr cc A B ord y) (i+1))) (vecN b iz.val))).card := by
      rw [← key]
      unfold jTot
      apply Finset.sum_congr rfl
      intro ix _
      apply Finset.sum_congr rfl
      intro iy _
      have hiff : jSat (jInp b (encD nr nc cr cc A B ord y) pin value ⟨i, h⟩
          (tblT b (encD nr nc cr cc A B ord y) pin value i))
          (vecN b ix.val) (vecN (b+2) iy.val) (vecN b iz.val) ↔
          JSA (slE k m b (HbE (encD nr nc cr cc A B ord y) i))
            (slE k m b (HbE (encD nr nc cr cc A B ord y) (i+1)))
            (slY k b (HbY (encD nr nc cr cc A B ord y) ⟨i, h⟩))
            (fun q => loB (encD nr nc cr cc A B ord y) i q && hiB (encD nr nc cr cc A B ord y) i q)
            (liveB (encD nr nc cr cc A B ord y) (i+1))
            (vecN m (A (ord ⟨i, h⟩)).val) (vecN m (B (ord ⟨i, h⟩)).val)
            (vecN b ix.val) (vecN (b+2) iy.val) (vecN b iz.val) := by
        rw [ch_jSat]
        unfold JSA
        simp only [ch_aV, ch_bV]
        exact Iff.rfl
      have hG1 : tabN (fun j : Fin (k+1) => jInp b (encD nr nc cr cc A B ord y) pin value ⟨i, h⟩
          (tblT b (encD nr nc cr cc A B ord y) pin value i) (Sum.inr (Sum.inr (iy, j)))) =
          if gT b (encD nr nc cr cc A B ord y) pin value ⟨i, h⟩ iy = true then 1 else 0 :=
        iw_tab_one (t := k) (gT b (encD nr nc cr cc A B ord y) pin value ⟨i, h⟩ iy)
      by_cases hcond : JSA (slE k m b (HbE (encD nr nc cr cc A B ord y) i))
            (slE k m b (HbE (encD nr nc cr cc A B ord y) (i+1)))
            (slY k b (HbY (encD nr nc cr cc A B ord y) ⟨i, h⟩))
            (fun q => loB (encD nr nc cr cc A B ord y) i q && hiB (encD nr nc cr cc A B ord y) i q)
            (liveB (encD nr nc cr cc A B ord y) (i+1))
            (vecN m (A (ord ⟨i, h⟩)).val) (vecN m (B (ord ⟨i, h⟩)).val)
            (vecN b ix.val) (vecN (b+2) iy.val) (vecN b iz.val)
      · rw [if_pos (hiff.2 hcond), if_pos hcond, hG1]
        rfl
      · rw [if_neg (fun hh => hcond (hiff.1 hh)), if_neg hcond]
    have hlt : jTot (jInp b (encD nr nc cr cc A B ord y) pin value ⟨i, h⟩
          (tblT b (encD nr nc cr cc A B ord y) pin value i)) iz < 2^(k+1) := by
      rw [hJ]
      calc _ ≤ Fintype.card (Fin k → Bool) := Finset.card_le_univ _
        _ = 2^k := by simp
        _ < 2^(k+1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
    rw [show (fun j : Fin (k+1) => tblT b (encD nr nc cr cc A B ord y) pin value (i+1) (iz, j)) =
      fun j : Fin (k+1) => (jTot (jInp b (encD nr nc cr cc A B ord y) pin value ⟨i, h⟩
          (tblT b (encD nr nc cr cc A B ord y) pin value i)) iz).testBit j.val from funext hbit,
      ch_tabN_bits _ _ hlt, hJ]

theorem fin_bv {W : ℕ} (w : Fin W → Bool) : bv w = BitVec.ofNat W (tabN w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ofNat]
  have h1 : (bv w).getLsbD i = w ⟨i, hi⟩ := getLsbD_bv w ⟨i, hi⟩
  have h2 : (tabN w).testBit i = w ⟨i, hi⟩ := ch_tabN_testBit w ⟨i, hi⟩
  rw [h1, h2]
  simp [hi]

theorem fin_word {k W : ℕ} (c : Fin k → Bool) (L : List (Fin k)) (n : ℕ) :
    L.foldl (fun acc q => if c q = true then acc + acc else acc) (BitVec.ofNat W n) =
      BitVec.ofNat W (n * 2^(L.countP c)) := by
  induction L generalizing n with
  | nil => simp
  | cons q L ih =>
    rw [List.foldl_cons, List.countP_cons]
    by_cases hc : c q = true
    · rw [if_pos hc, ← BitVec.ofNat_add, ih, if_pos hc]
      congr 1
      ring
    · rw [if_neg hc, ih, if_neg hc]
      rfl

theorem fin_cnt_fun (k : ℕ) (h : ℕ → Prop) (pin value : Fin k → Bool) :
    cntPin k h pin value =
      Nat.card {ω : Fin k → Bool // h (tabN ω) ∧ ∀ i : Fin k, pin i = true → ω i = value i} := by
  unfold cntPin
  refine Nat.card_congr (Equiv.subtypeEquiv
    ⟨fun w i => w.val.testBit i.val, fun ω => ⟨tabN ω, ch_tabN_lt ω⟩,
      fun w => Fin.ext (ch_tabN_bits k w.val w.isLt), fun ω => funext (ch_tabN_testBit ω)⟩ ?_)
  intro w
  show (h w.val ∧ ∀ i : Fin k, pin i = true → w.val.testBit i.val = value i) ↔
    (h (tabN (fun i : Fin k => w.val.testBit i.val)) ∧
      ∀ i : Fin k, pin i = true → w.val.testBit i.val = value i)
  rw [ch_tabN_bits k w.val w.isLt]

theorem fin_supp_card {k : ℕ} (c : Fin k → Bool) :
    (Finset.univ.filter (fun g : Fin k → Bool => ∀ q, c q = false → g q = false)).card =
      2^((List.finRange k).countP c) := by
  classical
  have hS : ((List.finRange k).filter c).toFinset =
      Finset.univ.filter (fun q : Fin k => c q = true) := by
    ext q; simp
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange k).filter _), hS, ← Finset.card_powerset]
  refine Finset.card_bij (fun g _ => Finset.univ.filter (fun q => g q = true)) ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_filter] at hg
    rw [Finset.mem_powerset]
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    cases hc : c q
    · rw [hg.2 q hc] at hq; exact absurd hq.2 (by simp)
    · rfl
  · intro g1 _ g2 _ heq
    funext q
    have h1 : q ∈ Finset.univ.filter (fun q => g1 q = true) ↔
        q ∈ Finset.univ.filter (fun q => g2 q = true) := by rw [heq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
    cases h2 : g2 q
    · cases h3 : g1 q
      · rfl
      · rw [h1.1 h3] at h2; exact absurd h2 (by simp)
    · exact h1.2 h2
  · intro T hT
    rw [Finset.mem_powerset] at hT
    refine ⟨fun q => decide (q ∈ T), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro q hq
      rw [decide_eq_false_iff_not]
      intro hqT
      have := hT hqT
      rw [Finset.mem_filter] at this
      rw [this.2] at hq
      exact absurd hq (by simp)
    · ext q; simp

theorem fin_Phi_all (k r m : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (hbij : Function.Bijective ord)
    (ω : Fin k → Bool) :
    PhiS k r m nr nc cr cc A B ord k ω = ∑ p : Fin k, phiS k r m nr nc cr cc A B p ω := by
  unfold PhiS
  rw [← Function.Bijective.sum_comp hbij (fun p => phiS k r m nr nc cr cc A B p ω)]
  apply Finset.sum_congr rfl
  intro j _
  rw [if_pos j.isLt]

theorem fin_Phi_loc (k r m : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (nr nc : Fin (2^k))
    (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (i : ℕ) (ω ω' : Fin k → Bool)
    (h : ∀ q, loB (encD nr nc cr cc A B ord y) i q = true → ω q = ω' q) :
    PhiS k r m nr nc cr cc A B ord i ω = PhiS k r m nr nc cr cc A B ord i ω' := by
  unfold PhiS
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < i
  · rw [if_pos hj, if_pos hj]
    apply ch_phi_local k r m hk hr
    intro q hq
    apply h
    rw [ch_loB]
    unfold poolLo
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, j, hj, hq⟩
  · rw [if_neg hj, if_neg hj]

theorem fin_live_k {k r m : ℕ} (d : Dat k r m → Bool) (q : Fin k) (h : liveB d k q = true) :
    False := by
  unfold liveB at h
  rw [Bool.and_eq_true] at h
  have h2 := h.2
  unfold hiB at h2
  rw [decide_eq_true_iff] at h2
  obtain ⟨i', h1, _⟩ := h2
  exact absurd i'.isLt (by omega)

theorem fin_count (k r m : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (nr nc : Fin (2^k))
    (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (hbij : Function.Bijective ord) (pin value : Fin k → Bool) (e : EVis k m → ZMod 2)
    (he : (fun ρ => e (Sum.inr ρ)) = vecN m y.val) :
    cntPin k (fun w => reportN k r m nr nc cr cc A B w = y.val) pin value =
      (NSetA (loB (encD nr nc cr cc A B ord y) k) pin value
        (liveB (encD nr nc cr cc A B ord y) k) (PhiS k r m nr nc cr cc A B ord k) e).card *
      2^((List.finRange k).countP
        (fun q => !loB (encD nr nc cr cc A B ord y) k q && !pin q)) := by
  classical
  have hloc := fin_Phi_loc k r m hk hr nr nc cr cc A B ord y k
  rw [fin_cnt_fun, Nat.card_eq_fintype_card,
    Fintype.card_of_subtype (Finset.univ.filter (fun ω : Fin k → Bool =>
      reportN k r m nr nc cr cc A B (tabN ω) = y.val ∧
        ∀ i : Fin k, pin i = true → ω i = value i)) (fun x => by simp),
    ← fin_supp_card, ← Finset.card_product]
  symm
  refine Finset.card_bij (fun a _ => fun q =>
    if loB (encD nr nc cr cc A B ord y) k q = true then a.1 q
    else if pin q = true then value q else a.2 q) ?_ ?_ ?_
  · rintro ⟨ω0, g⟩ ha
    rw [Finset.mem_product] at ha
    obtain ⟨w1, w2, w3, w4⟩ := (iv_mem _ _ _ _ _ _ _).1 ha.1
    have e1 : PhiS k r m nr nc cr cc A B ord k (fun q =>
        if loB (encD nr nc cr cc A B ord y) k q = true then ω0 q
        else if pin q = true then value q else g q) = PhiS k r m nr nc cr cc A B ord k ω0 :=
      hloc _ _ (fun q hq => by simp [hq])
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (ch_hit k r m nr nc cr cc A B y _).2 ?_, ?_⟩
    · rw [← fin_Phi_all k r m nr nc cr cc A B ord hbij, e1, w4, he]
    · intro q hp
      show (if loB (encD nr nc cr cc A B ord y) k q = true then ω0 q
        else if pin q = true then value q else g q) = value q
      by_cases hl : loB (encD nr nc cr cc A B ord y) k q = true
      · rw [if_pos hl]; exact w2 q hl hp
      · rw [if_neg hl, if_pos hp]
  · rintro ⟨ω0, g⟩ ha ⟨ω0', g'⟩ ha' heq
    rw [Finset.mem_product] at ha ha'
    have w1 : ∀ q, loB (encD nr nc cr cc A B ord y) k q = false → ω0 q = false :=
      ((iv_mem _ _ _ _ _ _ _).1 ha.1).1
    have w1' : ∀ q, loB (encD nr nc cr cc A B ord y) k q = false → ω0' q = false :=
      ((iv_mem _ _ _ _ _ _ _).1 ha'.1).1
    have hg : ∀ q, (!loB (encD nr nc cr cc A B ord y) k q && !pin q) = false → g q = false :=
      (Finset.mem_filter.1 ha.2).2
    have hg' : ∀ q, (!loB (encD nr nc cr cc A B ord y) k q && !pin q) = false → g' q = false :=
      (Finset.mem_filter.1 ha'.2).2
    have hq : ∀ q, (if loB (encD nr nc cr cc A B ord y) k q = true then ω0 q
        else if pin q = true then value q else g q) =
        (if loB (encD nr nc cr cc A B ord y) k q = true then ω0' q
        else if pin q = true then value q else g' q) := fun q => congrFun heq q
    have h1 : ω0 = ω0' := by
      funext q
      by_cases hl : loB (encD nr nc cr cc A B ord y) k q = true
      · have := hq q; rwa [if_pos hl, if_pos hl] at this
      · have hl' : loB (encD nr nc cr cc A B ord y) k q = false := by simpa using hl
        rw [w1 q hl', w1' q hl']
    have h2 : g = g' := by
      funext q
      by_cases hl : loB (encD nr nc cr cc A B ord y) k q = true
      · rw [hg q (by simp [hl]), hg' q (by simp [hl])]
      · by_cases hp : pin q = true
        · rw [hg q (by simp [hp]), hg' q (by simp [hp])]
        · have := hq q
          rwa [if_neg hl, if_neg hp, if_neg hl, if_neg hp] at this
    rw [h1, h2]
  · intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨-, hhit, hpin⟩ := hω
    have e1 : PhiS k r m nr nc cr cc A B ord k
        (fun q => loB (encD nr nc cr cc A B ord y) k q && ω q) =
        PhiS k r m nr nc cr cc A B ord k ω := hloc _ _ (fun q hq => by simp [hq])
    refine ⟨(fun q => loB (encD nr nc cr cc A B ord y) k q && ω q,
      fun q => (!loB (encD nr nc cr cc A B ord y) k q && !pin q) && ω q), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨(iv_mem _ _ _ _ _ _ _).2 ⟨fun q hq => by simp [hq], ?_,
        fun q hq => (fin_live_k _ q hq).elim, ?_⟩, ?_⟩
      · intro q hq hp
        simp only [hq, Bool.true_and]
        exact hpin q hp
      · rw [e1, fin_Phi_all k r m nr nc cr cc A B ord hbij,
          (ch_hit k r m nr nc cr cc A B y ω).1 hhit, he]
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, fun q hq => by
          show ((!loB (encD nr nc cr cc A B ord y) k q && !pin q) && ω q) = false
          rw [hq]; rfl⟩
    · funext q
      show (if loB (encD nr nc cr cc A B ord y) k q = true then
          (loB (encD nr nc cr cc A B ord y) k q && ω q)
        else if pin q = true then value q
        else ((!loB (encD nr nc cr cc A B ord y) k q && !pin q) && ω q)) = ω q
      by_cases hl : loB (encD nr nc cr cc A B ord y) k q = true
      · rw [if_pos hl, hl]; rfl
      · by_cases hp : pin q = true
        · rw [if_neg hl, if_pos hp]; exact (hpin q hp).symm
        · have hl' : loB (encD nr nc cr cc A B ord y) k q = false := by simpa using hl
          have hp' : pin q = false := by simpa using hp
          rw [if_neg hl, if_neg hp, hl', hp']; rfl

theorem fin_zero (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (nr nc : Fin (2^k))
    (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (hbij : Function.Bijective ord) (pin value : Fin k → Bool) (i : ℕ) (hi : i ≤ k)
    (hc : slE k m b (HbE (encD nr nc cr cc A B ord y) i) (Sum.inr (Sum.inr (Sum.inr ()))) = false) :
    cntPin k (fun w => reportN k r m nr nc cr cc A B w = y.val) pin value = 0 := by
  rw [fin_cnt_fun]
  have hemp : IsEmpty {ω : Fin k → Bool // reportN k r m nr nc cr cc A B (tabN ω) = y.val ∧
      ∀ i : Fin k, pin i = true → ω i = value i} := by
    refine ⟨fun a => ?_⟩
    obtain ⟨ω, hhit, -⟩ := a
    have hy := (ch_hit k r m nr nc cr cc A B y ω).1 hhit
    refine (slE_spec k m b (HbE (encD nr nc cr cc A B ord y) i)).1 hc
      (Sum.elim (fun q => if liveB (encD nr nc cr cc A B ord y) i q = true then b2z (ω q) else 0)
        (PhiS k r m nr nc cr cc A B ord i ω)) ?_
    rw [ch_solE]
    refine ⟨fun q hq => by simp [hq],
      fun j => b2z (sSen k r nr nc cr cc false (ord j) ω),
      fun j => b2z (sSen k r nr nc cr cc true (ord j) ω), rfl, ?_⟩
    show (∑ j : Fin k, if i ≤ j.val then phiS k r m nr nc cr cc A B (ord j) ω else 0) +
      PhiS k r m nr nc cr cc A B ord i ω = vecN m y.val
    rw [← hy, ← Function.Bijective.sum_comp hbij (fun p => phiS k r m nr nc cr cc A B p ω)]
    unfold PhiS
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j.val < i
    · rw [if_neg (by omega), if_pos h, zero_add]
    · rw [if_pos (by omega), if_neg h, add_zero]
  exact Nat.card_of_isEmpty

theorem cc_sel {ι ι' : Type} {S : ℕ} {φ : (ι' → Bool) → Bool} (σ : ι' → ι) (h : Cb ι' S φ) :
    Cb ι S (fun v => φ (fun j => v (σ j))) := Cmp.sel σ h

theorem cc_bind {ι κ : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    {φ : (ι ⊕ κ → Bool) → Bool} (h : Cmp ι κ S F) (h' : Cb (ι ⊕ κ) S' φ) :
    Cb ι (S + S') (fun v => φ (Sum.elim v (F v))) := Cmp.comp h.keep h'

theorem cc_ex {ι I : Type} [Fintype I] {s : ℕ} {P : I → (ι → Bool) → Prop}
    {inst : ∀ v, Decidable (∃ i, P i v)} (φ : I → (ι → Bool) → Bool)
    (h : ∀ i, Cb ι s (φ i)) (hP : ∀ i v, φ i v = true ↔ P i v) :
    Cb ι (Fintype.card I * (s + 1) + 1) (fun v => @decide (∃ i, P i v) (inst v)) :=
  (Cb.bigOr h).congr (fun v => decide_eq_decide.2 (exists_congr (fun i => hP i v)))

theorem cc_all {ι I : Type} [Fintype I] {s : ℕ} {P : I → (ι → Bool) → Prop}
    {inst : ∀ v, Decidable (∀ i, P i v)} (φ : I → (ι → Bool) → Bool)
    (h : ∀ i, Cb ι s (φ i)) (hP : ∀ i v, φ i v = true ↔ P i v) :
    Cb ι (Fintype.card I * (s + 1) + 1) (fun v => @decide (∀ i, P i v) (inst v)) :=
  (Cb.bigAnd h).congr (fun v => decide_eq_decide.2 (forall_congr' (fun i => hP i v)))

theorem cc_beq {ι : Type} {S S' : ℕ} {φ ψ : (ι → Bool) → Bool} (h : Cb ι S φ) (h' : Cb ι S' ψ) :
    Cb ι (S + S' + 4 + 1) (fun v => φ v == ψ v) :=
  ((h.xor h').not).congr (fun v => by cases φ v <;> cases ψ v <;> rfl)

def cEq (k : ℕ) : ℕ := k * 2 + 1

theorem cc_eqOrd {k r m : ℕ} (i p : Fin k) : Cb (Dat k r m) (cEq k) (fun d => eqOrd d i p) := by
  have h : ∀ t : Fin k, Cb (Dat k r m) 1
      (fun d => if p.val.testBit t.val = true then dOrd d (i, t) else !dOrd d (i, t)) := by
    intro t
    by_cases hb : p.val.testBit t.val = true
    · simp only [hb, if_true]
      exact (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, t)))))).mono (by omega)
    · simp only [hb, if_false]
      exact ((Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, t)))))).not).mono (by omega)
  have h2 := cc_all (P := fun t d => dOrd d (i, t) = p.val.testBit t.val)
    (inst := fun _ => inferInstance) _ h
    (fun t d => by cases hb : p.val.testBit t.val <;> simp)
  refine Cb.mono (Cb.congr h2 (fun d => ?_)) (by rw [Fintype.card_fin]; unfold cEq; omega)
  unfold eqOrd
  exact decide_eq_decide.2 Iff.rfl

def cAV (k : ℕ) : ℕ := k * (cEq k + 0 + 1 + 1) + 1

theorem cc_aV {k r m : ℕ} (i : Fin k) (ρ : Fin m) : Cb (Dat k r m) (cAV k) (fun d => aV d i ρ) := by
  have h2 := cc_ex (P := fun p d => eqOrd d i p = true ∧ dA d (p, ρ) = true)
    (inst := fun _ => inferInstance) _
    (fun p => (cc_eqOrd (r := r) (m := m) i p).and
      (Cb.var (Sum.inr (Sum.inr (Sum.inl (Sum.inl (p, ρ)))))))
    (fun p d => by simp [dA])
  refine Cb.mono (Cb.congr h2 (fun d => ?_)) (by rw [Fintype.card_fin]; unfold cAV; omega)
  unfold aV
  exact decide_eq_decide.2 Iff.rfl

theorem cc_bV {k r m : ℕ} (i : Fin k) (ρ : Fin m) : Cb (Dat k r m) (cAV k) (fun d => bV d i ρ) := by
  have h2 := cc_ex (P := fun p d => eqOrd d i p = true ∧ dB d (p, ρ) = true)
    (inst := fun _ => inferInstance) _
    (fun p => (cc_eqOrd (r := r) (m := m) i p).and
      (Cb.var (Sum.inr (Sum.inr (Sum.inl (Sum.inr (p, ρ)))))))
    (fun p d => by simp [dB])
  refine Cb.mono (Cb.congr h2 (fun d => ?_)) (by rw [Fintype.card_fin]; unfold cAV; omega)
  unfold bV
  exact decide_eq_decide.2 Iff.rfl

def cScP (m : ℕ) : ℕ := (m * (0 + 1) + 1 + 1 + 1) + (m * (0 + 1) + 1 + 1 + 1) + 1

theorem cc_scP {k r m : ℕ} (p q : Fin k) : Cb (Dat k r m) (cScP m) (fun d => scP d p q) := by
  have hA := cc_ex (P := fun ρ (d : Dat k r m → Bool) => dA d (p, ρ) = true)
    (inst := fun _ => inferInstance) _
    (fun ρ => Cb.var (Sum.inr (Sum.inr (Sum.inl (Sum.inl (p, ρ))))))
    (fun ρ d => by simp [dA])
  have hB := cc_ex (P := fun ρ (d : Dat k r m → Bool) => dB d (p, ρ) = true)
    (inst := fun _ => inferInstance) _
    (fun ρ => Cb.var (Sum.inr (Sum.inr (Sum.inl (Sum.inr (p, ρ))))))
    (fun ρ d => by simp [dB])
  have h := (hA.and (Cb.const (arcC k r false p q))).or (hB.and (Cb.const (arcC k r true p q)))
  refine Cb.mono (Cb.congr h (fun d => ?_)) (by rw [Fintype.card_fin]; unfold cScP; omega)
  unfold scP
  congr 2 <;> exact decide_eq_decide.2 Iff.rfl

def cScB (k m : ℕ) : ℕ := k * (cEq k + cScP m + 1 + 1) + 1

theorem cc_scB {k r m : ℕ} (i q : Fin k) : Cb (Dat k r m) (cScB k m) (fun d => scB d i q) := by
  have h2 := cc_ex (P := fun p d => eqOrd d i p = true ∧ scP d p q = true)
    (inst := fun _ => inferInstance) _
    (fun p => (cc_eqOrd (r := r) (m := m) i p).and (cc_scP p q))
    (fun p d => by simp)
  refine Cb.mono (Cb.congr h2 (fun d => ?_)) (by rw [Fintype.card_fin]; unfold cScB; omega)
  unfold scB
  exact decide_eq_decide.2 Iff.rfl

def cLo (k m : ℕ) : ℕ := k * (1 + cScB k m + 1 + 1) + 1

theorem cc_loB {k r m : ℕ} (i : ℕ) (q : Fin k) : Cb (Dat k r m) (cLo k m) (fun d => loB d i q) := by
  have h2 := cc_ex (P := fun (i' : Fin k) d => i'.val < i ∧ scB d i' q = true)
    (inst := fun _ => inferInstance) _
    (fun i' => (Cb.const (decide (i'.val < i))).and (cc_scB (r := r) (m := m) i' q))
    (fun p d => by simp)
  refine Cb.mono (Cb.congr h2 (fun d => ?_)) (by rw [Fintype.card_fin]; unfold cLo; omega)
  unfold loB
  exact decide_eq_decide.2 Iff.rfl

theorem cc_hiB {k r m : ℕ} (i : ℕ) (q : Fin k) : Cb (Dat k r m) (cLo k m) (fun d => hiB d i q) := by
  have h2 := cc_ex (P := fun (i' : Fin k) d => i ≤ i'.val ∧ scB d i' q = true)
    (inst := fun _ => inferInstance) _
    (fun i' => (Cb.const (decide (i ≤ i'.val))).and (cc_scB (r := r) (m := m) i' q))
    (fun p d => by simp)
  refine Cb.mono (Cb.congr h2 (fun d => ?_)) (by rw [Fintype.card_fin]; unfold cLo; omega)
  unfold hiB
  exact decide_eq_decide.2 Iff.rfl

def cLive (k m : ℕ) : ℕ := cLo k m + cLo k m + 1

theorem cc_liveB {k r m : ℕ} (i : ℕ) (q : Fin k) :
    Cb (Dat k r m) (cLive k m) (fun d => liveB d i q) :=
  (cc_loB i q).and (cc_hiB i q)

def cDB (k m : ℕ) : ℕ := cLive k m + cScB k m + 1

theorem cc_DB {k r m : ℕ} (i q : Fin k) : Cb (Dat k r m) (cDB k m) (fun d => DB d i q) :=
  (cc_liveB i.val q).or (cc_scB i q)

def sE (k m : ℕ) : ℕ := cLive k m + cAV k + 4

theorem cc_HbE {k r m : ℕ} (i : ℕ) :
    Cmp (Dat k r m) (ERow k m × (EHid k ⊕ (EVis k m ⊕ Unit)))
      (Fintype.card (ERow k m × (EHid k ⊕ (EVis k m ⊕ Unit))) * sE k m) (fun d => HbE d i) := by
  apply Cmp.ofBits
  rintro ⟨(ρ | ρ | q), ((j | j) | (q' | ρ') | u)⟩
  all_goals first
    | exact (Cb.const false).mono (by unfold sE; omega)
    | exact (Cb.const (decide (ρ' = ρ))).mono (by unfold sE; omega)
    | exact ((Cb.const (decide (j.val < i))).and (cc_aV j ρ)).mono (by unfold sE; omega)
    | exact ((Cb.const (decide (j.val < i))).and (cc_bV j ρ)).mono (by unfold sE; omega)
    | exact ((Cb.const (decide (i ≤ j.val))).and (cc_aV j ρ)).mono (by unfold sE; omega)
    | exact ((Cb.const (decide (i ≤ j.val))).and (cc_bV j ρ)).mono (by unfold sE; omega)
    | exact (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inr ρ))))).mono (by unfold sE; omega)
    | exact ((Cb.const (decide (q' = q))).and ((cc_liveB i q).not)).mono (by unfold sE; omega)

def sY (k m : ℕ) : ℕ := cDB k m + 3

theorem cc_HbY {k r m : ℕ} (i : Fin k) :
    Cmp (Dat k r m) (Fin k × (Empty ⊕ (YVis k ⊕ Unit)))
      (Fintype.card (Fin k × (Empty ⊕ (YVis k ⊕ Unit))) * sY k m) (fun d => HbY d i) := by
  apply Cmp.ofBits
  rintro ⟨q, (e | (q' | t) | u)⟩
  · exact e.elim
  all_goals first
    | exact (Cb.const false).mono (by unfold sY; omega)
    | exact ((Cb.const (decide (q' = q))).and ((cc_DB i q).not)).mono (by unfold sY; omega)

theorem cc_sPtB {ι ι2 : Type} {β : ℕ} (σo : SOut ι2 β → ι) (xb : Fin β → Bool) (j : ι2) :
    Cb ι (β * 6 + 5) (fun v => sPtB (fun x => v (σo x)) xb j) := by
  have h := (Cb.var (σo (Sum.inr (Sum.inl j)))).xor
    (Cb.bigXor (fun t : Fin β => (Cb.var (σo (Sum.inl (j, t)))).and (Cb.const (xb t))))
  exact h.mono (by rw [Fintype.card_fin]; omega)

theorem cc_stFn (k r : ℕ) (hk : 0 < k) (col : Bool) :
    Cmp (Fin k ⊕ (Fin k ⊕ (Fin r × Fin k))) (Fin k) (64 * k * (r + 1))
      (fun u i => stFn k r col (fun q => u (Sum.inl q)) (fun q => u (Sum.inr (Sum.inl q)))
        (fun p => u (Sum.inr (Sum.inr p))) i) := by
  obtain ⟨F, hF, hs⟩ := sens_cmp k r hk col
  refine hF.congr (fun u i => ?_)
  have h := hs ⟨tabN (fun q => u (Sum.inl q)), st_tabN_lt _⟩
    ⟨tabN (fun q => u (Sum.inr (Sum.inl q))), st_tabN_lt _⟩
    (fun j => ⟨tabN (fun t => u (Sum.inr (Sum.inr (j, t)))), st_tabN_lt _⟩) i
  have e : (Sum.elim (fun i : Fin k => (tabN (fun q => u (Sum.inl q))).testBit i.val)
      (Sum.elim (fun i : Fin k => (tabN (fun q => u (Sum.inr (Sum.inl q)))).testBit i.val)
        (fun p : Fin r × Fin k =>
          (tabN (fun t => u (Sum.inr (Sum.inr (p.1, t))))).testBit p.2.val))) = u := by
    funext x
    rcases x with q | q | p
    · exact st_tabN_testBit (fun q => u (Sum.inl q)) q
    · exact st_tabN_testBit (fun q => u (Sum.inr (Sum.inl q))) q
    · exact st_tabN_testBit (fun t => u (Sum.inr (Sum.inr (p.1, t)))) p.2
  dsimp only at h
  rw [e] at h
  rw [h]
  unfold stFn
  congr 2
  funext j
  exact Fin.ext (Nat.mod_eq_of_lt (st_tabN_lt _)).symm

def cSen (k r : ℕ) : ℕ := 64 * k * (r + 1) + (k * (cEq k + 0 + 1 + 1) + 1)

theorem cc_senB {ι : Type} {k r m : ℕ} (hk : 0 < k) (col : Bool) (σd : Dat k r m → ι)
    (στ : Fin k → ι) (i : Fin k) :
    Cb ι (cSen k r) (fun v => senB col (fun x => v (σd x)) i (fun q => v (στ q))) := by
  cases col
  · have hst := Cmp.sel (Sum.elim στ (Sum.elim (fun q => σd (Sum.inl (Sum.inl q)))
      (fun p => σd (Sum.inr (Sum.inl (Sum.inl p)))))) (cc_stFn k r hk false)
    have h2 := cc_ex (ι := ι ⊕ Fin k)
      (P := fun (p : Fin k) u => eqOrd (fun x => u (Sum.inl (σd x))) i p = true ∧
        u (Sum.inr ⟨(p.val + (2*r-2)) % k, Nat.mod_lt _ p.pos⟩) = true)
      (inst := fun _ => inferInstance) _
      (fun p => (cc_sel (fun x => Sum.inl (σd x)) (cc_eqOrd i p)).and
        (Cb.var (Sum.inr ⟨(p.val + (2*r-2)) % k, Nat.mod_lt _ p.pos⟩)))
      (fun p u => by simp)
    refine Cb.mono (Cb.congr (cc_bind hst h2) (fun v => ?_))
      (by rw [Fintype.card_fin]; unfold cSen; omega)
    unfold senB
    exact decide_eq_decide.2 Iff.rfl
  · have hst := Cmp.sel (Sum.elim στ (Sum.elim (fun q => σd (Sum.inl (Sum.inr q)))
      (fun p => σd (Sum.inr (Sum.inl (Sum.inr p)))))) (cc_stFn k r hk true)
    have h2 := cc_ex (ι := ι ⊕ Fin k)
      (P := fun (p : Fin k) u => eqOrd (fun x => u (Sum.inl (σd x))) i p = true ∧
        u (Sum.inr ⟨(p.val + (3*r+1)) % k, Nat.mod_lt _ p.pos⟩) = true)
      (inst := fun _ => inferInstance) _
      (fun p => (cc_sel (fun x => Sum.inl (σd x)) (cc_eqOrd i p)).and
        (Cb.var (Sum.inr ⟨(p.val + (3*r+1)) % k, Nat.mod_lt _ p.pos⟩)))
      (fun p u => by simp)
    refine Cb.mono (Cb.congr (cc_bind hst h2) (fun v => ?_))
      (by rw [Fintype.card_fin]; unfold cSen; omega)
    unfold senB
    exact decide_eq_decide.2 Iff.rfl

noncomputable def gTo {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (pin value : Fin k → Bool)
    (i : Fin k) (o : SOut (YVis k) (b+2) → Bool) (iy : Fin (2^(b+2))) : Bool :=
  (sPtB o (fun t => iy.val.testBit t.val) (Sum.inr 0) ==
    senB false d i (fun q => sPtB o (fun t => iy.val.testBit t.val) (Sum.inl q))) &&
  (sPtB o (fun t => iy.val.testBit t.val) (Sum.inr 1) ==
    senB true d i (fun q => sPtB o (fun t => iy.val.testBit t.val) (Sum.inl q))) &&
  decide (∀ q : Fin k, (DB d i q && pin q) = true →
    sPtB o (fun t => iy.val.testBit t.val) (Sum.inl q) = value q)

theorem cc_gT_eq {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (pin value : Fin k → Bool)
    (i : Fin k) (iy : Fin (2^(b+2))) :
    gT b d pin value i iy = gTo b d pin value i (slY k b (HbY d i)) iy := rfl

def cGT (k r m b : ℕ) : ℕ :=
  k * ((b+2) * 6 + 5) +
    (((((b+2) * 6 + 5) + cSen k r + 4 + 1) + (((b+2) * 6 + 5) + cSen k r + 4 + 1) + 1) +
      (k * (((cDB k m + 0 + 1) + 1 + (0 + 0 + 4 + 1) + 1) + 1) + 1) + 1)

theorem cc_gTo {ι : Type} {k r m : ℕ} (b : ℕ) (hk : 0 < k) (σd : Dat k r m → ι)
    (σp σv : Fin k → ι) (σo : SOut (YVis k) (b+2) → ι) (i : Fin k) (iy : Fin (2^(b+2))) :
    Cb ι (cGT k r m b) (fun v => gTo b (fun x => v (σd x)) (fun q => v (σp q))
      (fun q => v (σv q)) i (fun x => v (σo x)) iy) := by
  have hτ : Cmp ι (Fin k) (Fintype.card (Fin k) * ((b+2) * 6 + 5))
      (fun v q => sPtB (fun x => v (σo x)) (fun t => iy.val.testBit t.val) (Sum.inl q)) :=
    Cmp.ofBits (fun q => cc_sPtB σo (fun t => iy.val.testBit t.val) (Sum.inl q))
  have hA := cc_beq (cc_sPtB (ι := ι ⊕ Fin k) (fun x => Sum.inl (σo x))
      (fun t => iy.val.testBit t.val) (Sum.inr 0))
    (cc_senB hk false (fun x => Sum.inl (σd x)) Sum.inr i)
  have hB := cc_beq (cc_sPtB (ι := ι ⊕ Fin k) (fun x => Sum.inl (σo x))
      (fun t => iy.val.testBit t.val) (Sum.inr 1))
    (cc_senB hk true (fun x => Sum.inl (σd x)) Sum.inr i)
  have hC := cc_all (ι := ι ⊕ Fin k)
    (P := fun (q : Fin k) u => (DB (fun x => u (Sum.inl (σd x))) i q && u (Sum.inl (σp q))) = true →
      u (Sum.inr q) = u (Sum.inl (σv q)))
    (inst := fun _ => inferInstance) _
    (fun q => (((cc_sel (fun x => Sum.inl (σd x)) (cc_DB i q)).and
      (Cb.var (Sum.inl (σp q)))).not).or (cc_beq (Cb.var (Sum.inr q)) (Cb.var (Sum.inl (σv q)))))
    (fun q u => by
      cases DB (fun x => u (Sum.inl (σd x))) i q <;> cases u (Sum.inl (σp q)) <;>
        cases u (Sum.inr q) <;> cases u (Sum.inl (σv q)) <;> simp)
  refine Cb.mono (Cb.congr (cc_bind hτ ((hA.and hB).and hC)) (fun v => ?_))
    (by rw [Fintype.card_fin]; unfold cGT; omega)
  unfold gTo
  congr 1

def HJo {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (i : Fin k)
    (oE oE' : SOut (EVis k m) b → Bool) (oY : SOut (YVis k) (b+2) → Bool) :
    JRow k m b × (Fin b ⊕ (Fin (b+2) ⊕ (Fin b ⊕ Unit))) → Bool := fun e =>
  match e.1, e.2 with
  | Sum.inl q, Sum.inl t => liveB d i.val q && oE (Sum.inl (Sum.inl q, t))
  | Sum.inl q, Sum.inr (Sum.inl t) => liveB d i.val q && oY (Sum.inl (Sum.inl q, t))
  | Sum.inl _, Sum.inr (Sum.inr (Sum.inl _)) => false
  | Sum.inl q, Sum.inr (Sum.inr (Sum.inr _)) => liveB d i.val q &&
      xor (oE (Sum.inr (Sum.inl (Sum.inl q)))) (oY (Sum.inr (Sum.inl (Sum.inl q))))
  | Sum.inr (Sum.inl _), Sum.inl _ => false
  | Sum.inr (Sum.inl q), Sum.inr (Sum.inl t) =>
      liveB d (i.val+1) q && oY (Sum.inl (Sum.inl q, t))
  | Sum.inr (Sum.inl q), Sum.inr (Sum.inr (Sum.inl t)) =>
      liveB d (i.val+1) q && oE' (Sum.inl (Sum.inl q, t))
  | Sum.inr (Sum.inl q), Sum.inr (Sum.inr (Sum.inr _)) => liveB d (i.val+1) q &&
      xor (oE' (Sum.inr (Sum.inl (Sum.inl q)))) (oY (Sum.inr (Sum.inl (Sum.inl q))))
  | Sum.inr (Sum.inr (Sum.inl ρ)), Sum.inl t => oE (Sum.inl (Sum.inr ρ, t))
  | Sum.inr (Sum.inr (Sum.inl ρ)), Sum.inr (Sum.inl t) =>
      xor (oY (Sum.inl (Sum.inr 0, t)) && aV d i ρ) (oY (Sum.inl (Sum.inr 1, t)) && bV d i ρ)
  | Sum.inr (Sum.inr (Sum.inl ρ)), Sum.inr (Sum.inr (Sum.inl t)) => oE' (Sum.inl (Sum.inr ρ, t))
  | Sum.inr (Sum.inr (Sum.inl ρ)), Sum.inr (Sum.inr (Sum.inr _)) =>
      xor (xor (oE (Sum.inr (Sum.inl (Sum.inr ρ)))) (oE' (Sum.inr (Sum.inl (Sum.inr ρ)))))
        (xor (oY (Sum.inr (Sum.inl (Sum.inr 0))) && aV d i ρ)
          (oY (Sum.inr (Sum.inl (Sum.inr 1))) && bV d i ρ))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))), Sum.inl t' =>
      decide (t' = t) && !oE (Sum.inr (Sum.inr (Sum.inl t)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))), Sum.inr _ => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))), Sum.inr (Sum.inl t') =>
      decide (t' = t) && !oY (Sum.inr (Sum.inr (Sum.inl t)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))), Sum.inl _ => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))), Sum.inr (Sum.inr _) => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))), Sum.inr (Sum.inr (Sum.inl t')) =>
      decide (t' = t) && !oE' (Sum.inr (Sum.inr (Sum.inl t)))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))), Sum.inl _ => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))), Sum.inr (Sum.inl _) => false
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))), Sum.inr (Sum.inr (Sum.inr _)) => false

theorem cc_HJ_eq {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (i : Fin k) :
    HJ b d i = HJo b d i (slE k m b (HbE d i.val)) (slE k m b (HbE d (i.val+1)))
      (slY k b (HbY d i)) := by
  funext e
  rcases e with ⟨(q | q | ρ | t | t | t), (t' | t' | t' | u)⟩ <;> rfl

def sJ (k m : ℕ) : ℕ := cLive k m + cAV k + cAV k + 30

theorem cc_HJo {ι : Type} {k r m : ℕ} (b : ℕ) (σd : Dat k r m → ι)
    (σE σE' : SOut (EVis k m) b → ι) (σY : SOut (YVis k) (b+2) → ι) (i : Fin k) :
    Cmp ι (JRow k m b × (Fin b ⊕ (Fin (b+2) ⊕ (Fin b ⊕ Unit))))
      (Fintype.card (JRow k m b × (Fin b ⊕ (Fin (b+2) ⊕ (Fin b ⊕ Unit)))) * sJ k m)
      (fun v => HJo b (fun x => v (σd x)) i (fun x => v (σE x)) (fun x => v (σE' x))
        (fun x => v (σY x))) := by
  apply Cmp.ofBits
  rintro ⟨(q | q | ρ | t | t | t), (t' | t' | t' | u)⟩
  all_goals first
    | exact (Cb.const false).mono (by unfold sJ; omega)
    | exact ((cc_sel σd (cc_liveB i.val q)).and (Cb.var (σE (Sum.inl (Sum.inl q, t'))))).mono
        (by unfold sJ; omega)
    | exact ((cc_sel σd (cc_liveB i.val q)).and (Cb.var (σY (Sum.inl (Sum.inl q, t'))))).mono
        (by unfold sJ; omega)
    | exact ((cc_sel σd (cc_liveB i.val q)).and ((Cb.var (σE (Sum.inr (Sum.inl (Sum.inl q))))).xor
        (Cb.var (σY (Sum.inr (Sum.inl (Sum.inl q))))))).mono (by unfold sJ; omega)
    | exact ((cc_sel σd (cc_liveB (i.val+1) q)).and
        (Cb.var (σY (Sum.inl (Sum.inl q, t'))))).mono (by unfold sJ; omega)
    | exact ((cc_sel σd (cc_liveB (i.val+1) q)).and
        (Cb.var (σE' (Sum.inl (Sum.inl q, t'))))).mono (by unfold sJ; omega)
    | exact ((cc_sel σd (cc_liveB (i.val+1) q)).and
        ((Cb.var (σE' (Sum.inr (Sum.inl (Sum.inl q))))).xor
        (Cb.var (σY (Sum.inr (Sum.inl (Sum.inl q))))))).mono (by unfold sJ; omega)
    | exact (Cb.var (σE (Sum.inl (Sum.inr ρ, t')))).mono (by unfold sJ; omega)
    | exact (Cb.var (σE' (Sum.inl (Sum.inr ρ, t')))).mono (by unfold sJ; omega)
    | exact (((Cb.var (σY (Sum.inl (Sum.inr 0, t')))).and (cc_sel σd (cc_aV i ρ))).xor
        ((Cb.var (σY (Sum.inl (Sum.inr 1, t')))).and (cc_sel σd (cc_bV i ρ)))).mono
        (by unfold sJ; omega)
    | exact ((((Cb.var (σE (Sum.inr (Sum.inl (Sum.inr ρ))))).xor
          (Cb.var (σE' (Sum.inr (Sum.inl (Sum.inr ρ)))))).xor
        (((Cb.var (σY (Sum.inr (Sum.inl (Sum.inr 0))))).and (cc_sel σd (cc_aV i ρ))).xor
        ((Cb.var (σY (Sum.inr (Sum.inl (Sum.inr 1))))).and (cc_sel σd (cc_bV i ρ)))))).mono
        (by unfold sJ; omega)
    | exact ((Cb.const (decide (t' = t))).and
        ((Cb.var (σE (Sum.inr (Sum.inr (Sum.inl t))))).not)).mono (by unfold sJ; omega)
    | exact ((Cb.const (decide (t' = t))).and
        ((Cb.var (σY (Sum.inr (Sum.inr (Sum.inl t))))).not)).mono (by unfold sJ; omega)
    | exact ((Cb.const (decide (t' = t))).and
        ((Cb.var (σE' (Sum.inr (Sum.inr (Sum.inl t))))).not)).mono (by unfold sJ; omega)

abbrev JCol (b : ℕ) : Type := Fin b ⊕ (Fin (b+2) ⊕ (Fin b ⊕ Unit))
abbrev K1 (k m b : ℕ) : Type := (Fin (k+1) × SOut (EVis k m) b) ⊕ (Fin k × SOut (YVis k) (b+2))
abbrev K2 (k m b : ℕ) : Type :=
  (Fin k × (Fin (2^(b+2)) × Fin (k+1))) ⊕ (Fin k × (JRow k m b × JCol b))
abbrev TB (k b : ℕ) : Type := Fin (2^b) × Fin (k+1)
abbrev I2 (k r m b : ℕ) : Type := (CoreIn k r m ⊕ K1 k m b) ⊕ K2 k m b
abbrev I3 (k r m b : ℕ) : Type := I2 k r m b ⊕ (Fin (k+1) × TB k b)

noncomputable def cc_F1 (k r m b : ℕ) (v : CoreIn k r m → Bool) : K1 k m b → Bool :=
  Sum.elim (fun p => slE k m b (HbE (fun x => v (Sum.inl x)) p.1.val) p.2)
    (fun p => slY k b (HbY (fun x => v (Sum.inl x)) p.1) p.2)

def c1 (k m b : ℕ) : ℕ :=
  Fintype.card (Fin (k+1)) * (Fintype.card (ERow k m × (EHid k ⊕ (EVis k m ⊕ Unit))) * sE k m +
    glCost (Fintype.card (ERow k m)) (Fintype.card (EHid k)) (Fintype.card (EVis k m)) b) +
  Fintype.card (Fin k) * (Fintype.card (Fin k × (Empty ⊕ (YVis k ⊕ Unit))) * sY k m +
    glCost (Fintype.card (Fin k)) (Fintype.card Empty) (Fintype.card (YVis k)) (b+2))

theorem cc_F1_cmp (k r m b : ℕ) : Cmp (CoreIn k r m) (K1 k m b) (c1 k m b) (cc_F1 k r m b) :=
  Cmp.pair
    (Cmp.piU (fun i : Fin (k+1) => Cmp.comp (Cmp.sel Sum.inl (cc_HbE (r := r) i.val))
      (slE_cmp k m b)))
    (Cmp.piU (fun i : Fin k => Cmp.comp (Cmp.sel Sum.inl (cc_HbY (r := r) (m := m) i))
      (slY_cmp k b)))

noncomputable def cc_F2 (k r m b : ℕ) (u : CoreIn k r m ⊕ K1 k m b → Bool) : K2 k m b → Bool :=
  Sum.elim
    (fun p => decide (p.2.2.val = 0) &&
      gTo b (fun x => u (Sum.inl (Sum.inl x))) (fun q => u (Sum.inl (Sum.inr (Sum.inl q))))
        (fun q => u (Sum.inl (Sum.inr (Sum.inr q)))) p.1
        (fun x => u (Sum.inr (Sum.inr (p.1, x)))) p.2.1)
    (fun p => HJo b (fun x => u (Sum.inl (Sum.inl x))) p.1
      (fun x => u (Sum.inr (Sum.inl (p.1.castSucc, x))))
      (fun x => u (Sum.inr (Sum.inl (p.1.succ, x))))
      (fun x => u (Sum.inr (Sum.inr (p.1, x)))) p.2)

def c2 (k r m b : ℕ) : ℕ :=
  Fintype.card (Fin k) * (Fintype.card (Fin (2^(b+2)) × Fin (k+1)) * (1 + cGT k r m b + 1)) +
  Fintype.card (Fin k) * (Fintype.card (JRow k m b × JCol b) * sJ k m)

theorem cc_F2_cmp (k r m b : ℕ) (hk : 0 < k) :
    Cmp (CoreIn k r m ⊕ K1 k m b) (K2 k m b) (c2 k r m b) (cc_F2 k r m b) :=
  Cmp.pair
    (Cmp.piU (fun i : Fin k => Cmp.ofBits (fun p : Fin (2^(b+2)) × Fin (k+1) =>
      (Cb.const (decide (p.2.val = 0))).and
        (cc_gTo b hk (fun x => Sum.inl (Sum.inl x)) (fun q => Sum.inl (Sum.inr (Sum.inl q)))
          (fun q => Sum.inl (Sum.inr (Sum.inr q))) (fun x => Sum.inr (Sum.inr (i, x))) i p.1))))
    (Cmp.piU (fun i : Fin k => cc_HJo b (fun x => Sum.inl (Sum.inl x))
      (fun x => Sum.inr (Sum.inl (i.castSucc, x))) (fun x => Sum.inr (Sum.inl (i.succ, x)))
      (fun x => Sum.inr (Sum.inr (i, x))) i))

noncomputable def tblO (k m b : ℕ) (hj : Fin k × (JRow k m b × JCol b) → Bool)
    (g : Fin k × (Fin (2^(b+2)) × Fin (k+1)) → Bool) : ℕ → TB k b → Bool
  | 0 => fun p => decide (p.2.val = 0)
  | i+1 => if h : i < k then
      jnF k m b (Sum.elim (fun e => hj (⟨i, h⟩, e))
        (Sum.elim (tblO k m b hj g i) (fun p => g (⟨i, h⟩, p))))
      else tblO k m b hj g i

def cc_wm (k r m b : ℕ) (i : Fin k) :
    JIn (JRow k m b) b (b+2) b (k+1) → I2 k r m b ⊕ TB k b :=
  Sum.elim (fun e => Sum.inl (Sum.inr (Sum.inr (i, e))))
    (Sum.elim (fun p => Sum.inr p) (fun p => Sum.inl (Sum.inr (Sum.inl (i, p)))))

noncomputable def cc_G3 (k r m b : ℕ) (i : ℕ) (x : I2 k r m b ⊕ TB k b → Bool) : TB k b → Bool :=
  if h : i < k then jnF k m b (fun e => x (cc_wm k r m b ⟨i, h⟩ e)) else fun p => x (Sum.inr p)

noncomputable def cc_F3 (k r m b : ℕ) (w : I2 k r m b → Bool) : Fin (k+1) × TB k b → Bool :=
  fun p => tblO k m b (fun q => w (Sum.inr (Sum.inr q))) (fun q => w (Sum.inr (Sum.inl q)))
    p.1.val p.2

def c3 (k m b : ℕ) : ℕ :=
  (k+1) * (topCost b (b+2) b (Fintype.card (JRow k m b)) (k+1) (b+2) + Fintype.card (TB k b) * 1)

theorem cc_F3_cmp (k r m b : ℕ) :
    Cmp (I2 k r m b) (Fin (k+1) × TB k b) (c3 k m b) (cc_F3 k r m b) := by
  refine Cmp.chain k _
    (fun i w => tblO k m b (fun q => w (Sum.inr (Sum.inr q))) (fun q => w (Sum.inr (Sum.inl q))) i)
    (cc_G3 k r m b) ?_ ?_ ?_
  · exact (Cmp.ofBits (fun p : TB k b => Cb.const (decide (p.2.val = 0)))).mono (by omega)
  · intro i hi
    have h := (Cmp.sel (cc_wm k r m b ⟨i, hi⟩) (jnF_cmp k m b)).mono
      (Nat.le_add_right _ (Fintype.card (TB k b) * 1))
    refine h.congr (fun x p => ?_)
    unfold cc_G3
    rw [dif_pos hi]
  · intro i hi w
    show tblO k m b _ _ (i+1) = _
    rw [tblO]
    unfold cc_G3
    rw [dif_pos hi, dif_pos hi]
    congr 1
    funext e
    rcases e with e | p | p <;> rfl

def cc_Fq {I α : Type} {W : ℕ} (cond : α → (I → Bool) → Bool) (q : α)
    (x : I ⊕ Fin W → Bool) : I ⊕ Fin W → Bool :=
  Sum.elim (fun y => x (Sum.inl y))
    (fun j => (if cond q (fun y => x (Sum.inl y)) = true then
      bv (fun i => x (Sum.inr i)) + bv (fun i => x (Sum.inr i))
      else bv (fun i => x (Sum.inr i))).getLsbD j.val)

theorem cc_Fq_cmp {I α : Type} {W sc : ℕ} (cond : α → (I → Bool) → Bool) (q : α)
    (hc : Cb I sc (cond q)) :
    Cmp (I ⊕ Fin W) (I ⊕ Fin W) (0 + (sc + (0 + 0 + 20 * (W + 1)) + 0 + 4 * W))
      (cc_Fq cond q) :=
  Cmp.pair (Cmp.wire Sum.inl)
    (Cw.mux (cc_sel Sum.inl hc) (Cw.add (Cw.var Sum.inr) (Cw.var Sum.inr)) (Cw.var Sum.inr))

theorem cc_fold_eq {I α : Type} {W : ℕ} (cond : α → (I → Bool) → Bool) (L : List α)
    (s : I → Bool) (a : Fin W → Bool) :
    L.foldl (fun acc e => cc_Fq cond e acc) (Sum.elim s a) =
      Sum.elim s (fun j => (L.foldl (fun acc q => if cond q s = true then acc + acc else acc)
        (bv a)).getLsbD j.val) := by
  induction L generalizing a with
  | nil =>
    simp only [List.foldl_nil]
    congr 1
    funext j
    exact (getLsbD_bv a j).symm
  | cons e L ih =>
    simp only [List.foldl_cons]
    have h1 : cc_Fq cond e (Sum.elim s a) = Sum.elim s (fun j : Fin W =>
        (if cond e s = true then bv a + bv a else bv a).getLsbD j.val) := rfl
    rw [h1, ih, bv_getLsbD]

def cc_cond {k r m b : ℕ} (q : Fin k) (s : I3 k r m b → Bool) : Bool :=
  !loB (fun x => s (Sum.inl (Sum.inl (Sum.inl (Sum.inl x))))) k q &&
    !s (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl q)))))

theorem cc_cond_cb {k r m b : ℕ} (q : Fin k) :
    Cb (I3 k r m b) (cLo k m + 1 + (0 + 1) + 1) (cc_cond q) :=
  ((cc_sel (fun x => Sum.inl (Sum.inl (Sum.inl (Sum.inl x)))) (cc_loB k q)).not).and
    ((Cb.var (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl q)))))).not)

noncomputable def cc_out (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r)
    (x : I3 k r m b ⊕ Fin (k+1) → Bool) : Unit ⊕ Fin (k+1) → Bool :=
  Sum.elim (fun _ => passF k r m b hk hr
      (fun y => x (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl y)))))))
    (fun j => decide (∀ i : Fin (k+1),
      x (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (i, Sum.inr (Sum.inr (Sum.inr ())))))))) = true)
      && x (Sum.inr j))

def c4 (k r m : ℕ) : ℕ :=
  2^30 * (k+r+m+5)^10 +
    Fintype.card (Fin (k+1)) * ((Fintype.card (Fin (k+1)) * (0 + 1) + 1) + 0 + 1)

theorem cc_out_cmp (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) :
    Cmp (I3 k r m b ⊕ Fin (k+1)) (Unit ⊕ Fin (k+1)) (c4 k r m) (cc_out k r m b hk hr) := by
  have hp : Cb (I3 k r m b ⊕ Fin (k+1)) (2^30 * (k+r+m+5)^10)
      (fun x => passF k r m b hk hr
        (fun y => x (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl y))))))) :=
    cc_sel (fun y => Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl y)))))
      (Classical.choose_spec (pass_cb k r m b hk hr)).1
  have ha := cc_all (ι := I3 k r m b ⊕ Fin (k+1))
    (P := fun (i : Fin (k+1)) x =>
      x (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl (i, Sum.inr (Sum.inr (Sum.inr ())))))))) = true)
    (inst := fun _ => inferInstance) _
    (fun i => Cb.var (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl
      (i, Sum.inr (Sum.inr (Sum.inr ())))))))))
    (fun i x => Iff.rfl)
  exact Cmp.pair hp (Cmp.ofBits (fun j : Fin (k+1) => ha.and (Cb.var (Sum.inr j))))

theorem cc_tbl {k r m : ℕ} (b : ℕ) (d : Dat k r m → Bool) (pin value : Fin k → Bool) (i : ℕ) :
    tblT b d pin value i = tblO k m b
      (fun p => HJo b d p.1 (slE k m b (HbE d p.1.val)) (slE k m b (HbE d (p.1.val+1)))
        (slY k b (HbY d p.1)) p.2)
      (fun p => decide (p.2.2.val = 0) && gTo b d pin value p.1 (slY k b (HbY d p.1)) p.2.1) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [tblT, tblO]
    by_cases h : i < k
    · rw [dif_pos h, dif_pos h, ← ih]
      unfold stepT jInp
      rw [cc_HJ_eq]
      rfl
    · rw [dif_neg h, dif_neg h, ih]

def cTot (k r m b : ℕ) : ℕ :=
  c1 k m b + c2 k r m b + c3 k m b + 0 +
    k * (0 + ((cLo k m + 1 + (0 + 1) + 1) + (0 + 0 + 20 * ((k+1) + 1)) + 0 + 4 * (k+1))) +
    c4 k r m

theorem cc_core (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) :
    Cmp (CoreIn k r m) (Unit ⊕ Fin (k+1)) (cTot k r m b) (coreF k r m b hk hr) := by
  have hinit : Cmp (I3 k r m b) (I3 k r m b ⊕ Fin (k+1)) 0
      (fun z => Sum.elim z (fun j => z (Sum.inr (Fin.last k,
        ((⟨0, Nat.pos_of_ne_zero (by positivity)⟩ : Fin (2^b)), j))))) :=
    Cmp.keep (Cmp.wire (fun j => Sum.inr (Fin.last k,
        ((⟨0, Nat.pos_of_ne_zero (by positivity)⟩ : Fin (2^b)), j))))
  have hfold := Cmp.foldl (List.finRange k)
    (fun q (acc : I3 k r m b ⊕ Fin (k+1) → Bool) => cc_Fq (W := k+1) cc_cond q acc)
    (fun q _ => cc_Fq_cmp (W := k+1) cc_cond q (cc_cond_cb q))
  rw [List.length_finRange] at hfold
  have hall := (((((cc_F1_cmp k r m b).keep.comp (cc_F2_cmp k r m b hk).keep).comp
    (cc_F3_cmp k r m b).keep).comp hinit).comp hfold).comp (cc_out_cmp k r m b hk hr)
  refine Cmp.congr hall (fun v o => ?_)
  show (cc_out k r m b hk hr ((List.finRange k).foldl (fun acc e => cc_Fq cc_cond e acc)
      (Sum.elim _ _))) o = _
  rw [cc_fold_eq]
  rcases o with u | j
  · rfl
  · show (decide (∀ i : Fin (k+1), slE k m b (HbE (fun x => v (Sum.inl x)) i.val)
      (Sum.inr (Sum.inr (Sum.inr ()))) = true) && _) = _
    unfold coreF allCons finW
    simp only [Sum.elim_inr]
    congr 2
    rw [cc_tbl]
    rfl

theorem cc_p (X n : ℕ) (h : 10 ≤ X) : 10 * X^n ≤ X^(n+1) := by
  rw [pow_succ, Nat.mul_comm]; exact Nat.mul_le_mul_left _ h

theorem cc_small (k r m b X : ℕ) (hX : X = k+r+m+5) (hk0 : 0 < k) (hr : 4 ≤ r) (hb : b ≤ k+m) :
    cEq k ≤ 2*X ∧ cAV k ≤ 3*X^2 ∧ cScP m ≤ 2*X ∧ cScB k m ≤ 5*X^2 ∧ cLo k m ≤ 6*X^3 ∧
    cLive k m ≤ 13*X^3 ∧ cDB k m ≤ 14*X^3 ∧ sE k m ≤ 14*X^3 ∧ sY k m ≤ 15*X^3 ∧
    cSen k r ≤ 67*X^2 ∧ cGT k r m b ≤ 16*X^4 ∧ sJ k m ≤ 14*X^3 := by
  have h10 : 10 ≤ X := by omega
  have hk : k ≤ X := by omega
  have hr1 : r + 1 ≤ X := by omega
  have hb2 : b + 2 ≤ X := by omega
  have p1 : 10 * X ≤ X^2 := by simpa using cc_p X 1 h10
  have p2 : 10 * X^2 ≤ X^3 := cc_p X 2 h10
  have p3 : 10 * X^3 ≤ X^4 := cc_p X 3 h10
  have e1 : cEq k ≤ 2*X := by unfold cEq; omega
  have e2 : cAV k ≤ 3*X^2 := by
    unfold cAV
    calc k * (cEq k + 0 + 1 + 1) + 1 ≤ X * (2*X + 0 + 1 + 1) + 1 := by gcongr
      _ ≤ 3*X^2 := by nlinarith
  have e3 : cScP m ≤ 2*X := by unfold cScP; omega
  have e4 : cScB k m ≤ 5*X^2 := by
    unfold cScB
    calc k * (cEq k + cScP m + 1 + 1) + 1 ≤ X * (2*X + 2*X + 1 + 1) + 1 := by gcongr
      _ ≤ 5*X^2 := by nlinarith
  have e5 : cLo k m ≤ 6*X^3 := by
    unfold cLo
    calc k * (1 + cScB k m + 1 + 1) + 1 ≤ X * (1 + 5*X^2 + 1 + 1) + 1 := by gcongr
      _ ≤ 6*X^3 := by nlinarith
  have e6 : cLive k m ≤ 13*X^3 := by unfold cLive; nlinarith
  have e7 : cDB k m ≤ 14*X^3 := by unfold cDB; nlinarith
  have e8 : sE k m ≤ 14*X^3 := by unfold sE; nlinarith
  have e9 : sY k m ≤ 15*X^3 := by unfold sY; nlinarith
  have e10 : cSen k r ≤ 67*X^2 := by
    unfold cSen
    calc 64 * k * (r + 1) + (k * (cEq k + 0 + 1 + 1) + 1)
        ≤ 64 * X * X + (X * (2*X + 0 + 1 + 1) + 1) := by gcongr
      _ ≤ 67*X^2 := by nlinarith
  have e11 : cGT k r m b ≤ 16*X^4 := by
    unfold cGT
    calc k * ((b+2) * 6 + 5) +
        (((((b+2) * 6 + 5) + cSen k r + 4 + 1) + (((b+2) * 6 + 5) + cSen k r + 4 + 1) + 1) +
          (k * (((cDB k m + 0 + 1) + 1 + (0 + 0 + 4 + 1) + 1) + 1) + 1) + 1)
        ≤ X * (X * 6 + 5) +
        ((((X * 6 + 5) + 67*X^2 + 4 + 1) + ((X * 6 + 5) + 67*X^2 + 4 + 1) + 1) +
          (X * (((14*X^3 + 0 + 1) + 1 + (0 + 0 + 4 + 1) + 1) + 1) + 1) + 1) := by gcongr
      _ ≤ 16*X^4 := by nlinarith
  have e12 : sJ k m ≤ 14*X^3 := by unfold sJ; nlinarith
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩

theorem cc_cards (k m b : ℕ) :
    Fintype.card (ERow k m × (EHid k ⊕ (EVis k m ⊕ Unit))) = (m+(m+k))*((k+k)+((k+m)+1)) ∧
    Fintype.card (ERow k m) = m+(m+k) ∧ Fintype.card (EHid k) = k+k ∧
    Fintype.card (EVis k m) = k+m ∧
    Fintype.card (Fin k × (Empty ⊕ (YVis k ⊕ Unit))) = k*(0+((k+2)+1)) ∧
    Fintype.card Empty = 0 ∧ Fintype.card (YVis k) = k+2 ∧
    Fintype.card (Fin (2^(b+2)) × Fin (k+1)) = 2^(b+2)*(k+1) ∧
    Fintype.card (JRow k m b × JCol b) =
      (k+(k+(m+(b+((b+2)+b)))))*(b+((b+2)+(b+1))) ∧
    Fintype.card (JRow k m b) = k+(k+(m+(b+((b+2)+b)))) ∧
    Fintype.card (TB k b) = 2^b*(k+1) := by
  simp [Fintype.card_sum, Fintype.card_prod]

set_option maxHeartbeats 1600000 in
theorem cc_total (k r m b : ℕ) (hk0 : 0 < k) (hr : 4 ≤ r) (hb : b ≤ k + m) :
    cTot k r m b ≤ coreS k r m b := by
  obtain ⟨X, hX⟩ : ∃ X, X = k+r+m+5 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2^b := ⟨_, rfl⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := cc_small k r m b X hX hk0 hr hb
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := cc_cards k m b
  have h10 : 10 ≤ X := by omega
  have hk : k ≤ X := by omega
  have hk1 : k + 1 ≤ X := by omega
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact Nat.one_le_two_pow
  have p1 : 10 * X ≤ X^2 := by simpa using cc_p X 1 h10
  have p2 : 10 * X^2 ≤ X^3 := cc_p X 2 h10
  have p3 : 10 * X^3 ≤ X^4 := cc_p X 3 h10
  have p4 : 10 * X^4 ≤ X^5 := cc_p X 4 h10
  have p5 : 10 * X^5 ≤ X^6 := cc_p X 5 h10
  have p6 : 10 * X^6 ≤ X^7 := cc_p X 6 h10
  have p7 : 10 * X^7 ≤ X^8 := cc_p X 7 h10
  have p8 : 10 * X^8 ≤ X^9 := cc_p X 8 h10
  have p9 : 10 * X^9 ≤ X^10 := cc_p X 9 h10

  have b1 : c1 k m b ≤ 2^27 * X^7 := by
    unfold c1
    rw [d1, d2, d3, d4, d5, d6, d7, Fintype.card_fin, Fintype.card_fin]
    unfold glCost
    have g1 : m+(m+k) + (k+k) + (k+m) + b + 2 ≤ 5*X := by omega
    have g2 : k + 0 + (k+2) + (b+2) + 2 ≤ 3*X := by omega
    have g3 : m+(m+k) ≤ 2*X := by omega
    have g4 : (k+k)+((k+m)+1) ≤ 3*X := by omega
    have g5 : 0+((k+2)+1) ≤ X := by omega
    calc (k+1) * ((m+(m+k))*((k+k)+((k+m)+1)) * sE k m +
          2^12 * (m+(m+k) + (k+k) + (k+m) + b + 2)^6) +
        k * (k*(0+((k+2)+1)) * sY k m + 2^12 * (k + 0 + (k+2) + (b+2) + 2)^6)
        ≤ X * ((2*X)*(3*X) * (14*X^3) + 2^12 * (5*X)^6) +
          X * (X*X * (15*X^3) + 2^12 * (3*X)^6) := by gcongr
      _ = 99 * X^6 + (2^12 * 5^6 + 2^12 * 3^6) * X^7 := by ring
      _ ≤ 10 * X^7 + (2^12 * 5^6 + 2^12 * 3^6) * X^7 :=
        Nat.add_le_add_right (by linarith [p6]) _
      _ = (10 + (2^12 * 5^6 + 2^12 * 3^6)) * X^7 := by ring
      _ ≤ 2^27 * X^7 := Nat.mul_le_mul_right _ (by norm_num)

  have b2 : c2 k r m b ≤ 300 * X^6 * Q := by
    unfold c2
    rw [d8, d9, Fintype.card_fin]
    have g1 : k+(k+(m+(b+((b+2)+b)))) ≤ 5*X := by omega
    have g2 : b+((b+2)+(b+1)) ≤ 3*X := by omega
    have g3 : (2:ℕ)^(b+2) = 4 * Q := by rw [hQ]; ring
    rw [g3]
    have q1 : X^2 * Q ≤ X^6 * Q := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
    have q2 : X^6 ≤ X^6 * Q := Nat.le_mul_of_pos_right _ hQ1
    calc k * (4 * Q * (k+1) * (1 + cGT k r m b + 1)) +
          k * ((k+(k+(m+(b+((b+2)+b)))))*(b+((b+2)+(b+1))) * sJ k m)
        ≤ X * (4 * Q * X * (1 + 16*X^4 + 1)) + X * ((5*X)*(3*X) * (14*X^3)) := by gcongr
      _ = 64 * (X^6 * Q) + 8 * (X^2 * Q) + 210 * X^6 := by ring
      _ ≤ 300 * X^6 * Q := by linarith [q1, q2]

  have b3 : c3 k m b ≤ 2^24 * 9^12 * 10 * X^13 * Q + X^2 * Q := by
    unfold c3
    rw [d10, d11]
    have ht := topCost_le b (b+2) b (k+(k+(m+(b+((b+2)+b))))) (k+1) (b+2)
    have g1 : b + (b+2) + b + (k+(k+(m+(b+((b+2)+b))))) + (k+1) + 3 ≤ 9*X := by omega
    have g2 : min (b + (b+2) + b) (b+2) = b+2 := by omega
    rw [g2] at ht
    have g3 : (2:ℕ)^b + 2^(b+2) + 2^b + 2^(b+2) = 10 * Q := by rw [hQ]; ring
    rw [g3] at ht
    have ht2 : topCost b (b+2) b (k+(k+(m+(b+((b+2)+b))))) (k+1) (b+2) ≤
        2^24 * (9*X)^12 * (10 * Q) := by
      refine le_trans (Nat.le_succ _) (le_trans ht ?_)
      gcongr
    rw [← hQ]
    calc (k+1) * (topCost b (b+2) b (k+(k+(m+(b+((b+2)+b))))) (k+1) (b+2) + Q*(k+1) * 1)
        ≤ X * (2^24 * (9*X)^12 * (10 * Q) + Q * X * 1) := by gcongr
      _ = 2^24 * 9^12 * 10 * X^13 * Q + X^2 * Q := by ring

  have b4 : k * (0 + ((cLo k m + 1 + (0 + 1) + 1) + (0 + 0 + 20 * ((k+1) + 1)) + 0 + 4 * (k+1)))
      ≤ 7 * X^4 := by
    have g1 : (k+1)+1 ≤ X := by omega
    calc k * (0 + ((cLo k m + 1 + (0 + 1) + 1) + (0 + 0 + 20 * ((k+1) + 1)) + 0 + 4 * (k+1)))
        ≤ X * (0 + ((6*X^3 + 1 + (0 + 1) + 1) + (0 + 0 + 20 * X) + 0 + 4 * X)) := by gcongr
      _ = 6 * X^4 + 24 * X^2 + 3 * X := by ring
      _ ≤ 7 * X^4 := by linarith [p1, p2, p3]
  have b5 : c4 k r m ≤ 2^30 * X^10 + X^2 := by
    unfold c4
    rw [Fintype.card_fin, ← hX]
    have g1 : ((k+1) * (0 + 1) + 1) + 0 + 1 ≤ X := by omega
    calc 2^30 * X^10 + (k+1) * (((k+1) * (0 + 1) + 1) + 0 + 1)
        ≤ 2^30 * X^10 + X * X := by gcongr
      _ = 2^30 * X^10 + X^2 := by ring
  unfold cTot coreS
  rw [← hX, ← hQ]
  have r1 : X^7 ≤ X^10 * Q := le_trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    (Nat.le_mul_of_pos_right _ hQ1)
  have r2 : X^6 * Q ≤ X^10 * Q := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have r3 : X^2 * Q ≤ X^10 * Q := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have r4 : X^4 ≤ X^10 * Q := le_trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    (Nat.le_mul_of_pos_right _ hQ1)
  have r5 : X^10 ≤ X^10 * Q := Nat.le_mul_of_pos_right _ hQ1
  have r6 : X^2 ≤ X^10 * Q := le_trans (Nat.pow_le_pow_right (by omega) (by norm_num))
    (Nat.le_mul_of_pos_right _ hQ1)
  have r7 : X^10 * Q ≤ X^13 * Q := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have r8 : 10^6 * (X^13 * Q) ≤ X^19 * Q := by
    have : 10^6 ≤ X^6 := Nat.pow_le_pow_left h10 6
    calc 10^6 * (X^13 * Q) ≤ X^6 * (X^13 * Q) := Nat.mul_le_mul_right _ this
      _ = X^19 * Q := by ring
  have key : c1 k m b + c2 k r m b + c3 k m b + 0 +
      k * (0 + ((cLo k m + 1 + (0 + 1) + 1) + (0 + 0 + 20 * ((k+1) + 1)) + 0 + 4 * (k+1))) +
      c4 k r m ≤ (2^24 * 9^12 * 10 + 2^31) * (X^13 * Q) := by
    have s1 : 2^27 * X^7 + 300 * X^6 * Q + X^2 * Q + 7 * X^4 + (2^30 * X^10 + X^2) ≤
        2^31 * (X^10 * Q) := by linarith [r1, r2, r3, r4, r5, r6]
    linarith [b1, b2, b3, b4, b5, s1, r7]
  calc _ ≤ (2^24 * 9^12 * 10 + 2^31) * (X^13 * Q) := key
    _ ≤ (2^47 * 10^6) * (X^13 * Q) := Nat.mul_le_mul_right (X^13 * Q)
        (show 2^24 * 9^12 * 10 + 2^31 ≤ 2^47 * 10^6 by norm_num)
    _ = 2^47 * (10^6 * (X^13 * Q)) := Nat.mul_assoc _ _ _
    _ ≤ 2^47 * (X^19 * Q) := Nat.mul_le_mul_left _ r8
    _ = 2^47 * X^19 * Q := by ring

theorem core_cmp (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (hb : b ≤ k + m) :
    Cmp (CoreIn k r m) (Unit ⊕ Fin (k+1)) (coreS k r m b) (coreF k r m b hk hr) :=
  (cc_core k r m b hk hr).mono (cc_total k r m b hk hr hb)

theorem core_spec (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) :
    CoreSpec k r m b (coreF k r m b hk hr) := by
  intro nr nc cr cc A B ord y pin value
  refine ⟨?_, ?_⟩
  · exact (Classical.choose_spec (pass_cb k r m b hk hr)).2 nr nc cr cc A B ord y
  · intro hp j
    have hbij : Function.Bijective ord := ((pass_iff k r m b hk A B ord).1 hp).1
    show (allCons b (encD nr nc cr cc A B ord y) &&
      (finW b (encD nr nc cr cc A B ord y) pin value).getLsbD j.val) = _
    by_cases hall : allCons b (encD nr nc cr cc A B ord y) = true
    · rw [hall, Bool.true_and]
      have hall' : ∀ i : ℕ, i ≤ k → slE k m b (HbE (encD nr nc cr cc A B ord y) i)
          (Sum.inr (Sum.inr (Sum.inr ()))) = true := by
        intro i hi
        unfold allCons at hall
        rw [decide_eq_true_iff] at hall
        exact hall ⟨i, Nat.lt_succ_of_le hi⟩
      have hc := hall' k (le_refl k)
      have hn := cd_nfE k r m b hk nr nc cr cc A B ord y hp k (le_refl k) hc
      obtain ⟨hEA, -, -⟩ := ((slE_spec k m b (HbE (encD nr nc cr cc A B ord y) k)).2 hc).2.2 hn
      have hv0 : vecN b (0 : ℕ) = fun _ => 0 := by
        funext t; simp [vecN]
      have hok : sOk (slE k m b (HbE (encD nr nc cr cc A B ord y) k)) (vecN b (0 : ℕ)) := by
        intro t _; rw [hv0]
      have hinv := iw_inv k r m b hk hr nr nc cr cc A B ord y hp pin value hall' k (le_refl k)
        ⟨0, Nat.pos_of_ne_zero (by positivity)⟩ hok
      obtain ⟨-, c0, c1, -, h2⟩ := (ch_solE nr nc cr cc A B ord y k _).1 (hEA _ hok)
      have he : (fun ρ => sPt (slE k m b (HbE (encD nr nc cr cc A B ord y) k)) (vecN b (0 : ℕ))
          (Sum.inr ρ)) = vecN m y.val := by
        rw [← h2]
        rw [Finset.sum_eq_zero (fun j _ => if_neg (not_le.2 j.isLt)), zero_add]
      have hcnt := fin_count k r m hk hr nr nc cr cc A B ord y hbij pin value _ he
      have hW : finW b (encD nr nc cr cc A B ord y) pin value =
          BitVec.ofNat (k+1) (cntPin k (fun w => reportN k r m nr nc cr cc A B w = y.val)
            pin value) := by
        unfold finW
        rw [fin_bv, hcnt, ← hinv]
        exact fin_word (fun q => !loB (encD nr nc cr cc A B ord y) k q && !pin q) _ _
      rw [hW, BitVec.getLsbD_ofNat]
      simp [j.isLt]
    · have hall' : allCons b (encD nr nc cr cc A B ord y) = false := by simpa using hall
      rw [hall', Bool.false_and]
      unfold allCons at hall'
      rw [decide_eq_false_iff_not] at hall'
      push_neg at hall'
      obtain ⟨i, hi⟩ := hall'
      have hi' : slE k m b (HbE (encD nr nc cr cc A B ord y) i.val)
          (Sum.inr (Sum.inr (Sum.inr ()))) = false := by simpa using hi
      rw [fin_zero k r m b hk hr nr nc cr cc A B ord y hbij pin value i.val
        (Nat.le_of_lt_succ i.isLt) hi']
      simp

theorem core (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (hb : b ≤ k + m) :
    ∃ F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k+1)) → Bool,
      Cmp (CoreIn k r m) (Unit ⊕ Fin (k+1)) (coreS k r m b) F ∧ CoreSpec k r m b F :=
  ⟨coreF k r m b hk hr, core_cmp k r m b hk hr hb, core_spec k r m b hk hr⟩

noncomputable def ta_cnt {n : ℕ} (p : Fin n → Prop) : ℕ := Nat.card {z : Fin n // p z}

theorem ta_cnt_eq {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ta_cnt p = (Finset.univ.filter p).card := by
  unfold ta_cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem ta_cnt_congr {n : ℕ} (p p' : Fin n → Prop) (hp : ∀ z, p z ↔ p' z) :
    ta_cnt p = ta_cnt p' := by
  have : p = p' := funext (fun z => propext (hp z))
  rw [this]

theorem ta_cnt_split {n : ℕ} (p q : Fin n → Prop) :
    ta_cnt p = ta_cnt (fun z => p z ∧ q z) + ta_cnt (fun z => p z ∧ ¬ q z) := by
  classical
  rw [ta_cnt_eq, ta_cnt_eq, ta_cnt_eq, ← Finset.filter_filter, ← Finset.filter_filter]
  exact (Finset.card_filter_add_card_filter_not (s := Finset.univ.filter p) q).symm

theorem ta_cnt_lt {n : ℕ} (p p' : Fin n → Prop) (hp : ∀ z, p z → p' z)
    (hw : ∃ w, p' w ∧ ¬ p w) : ta_cnt p < ta_cnt p' := by
  classical
  rw [ta_cnt_eq, ta_cnt_eq]
  apply Finset.card_lt_card
  obtain ⟨w, hw1, hw2⟩ := hw
  refine ⟨fun z hz => ?_, fun H => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hp z hz
  · have : w ∈ Finset.univ.filter p := H (by simp [hw1])
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hw2 this

theorem ta_cnt_zero {n : ℕ} (p : Fin n → Prop) (hp : ∀ z, ¬ p z) : ta_cnt p = 0 := by
  classical
  rw [ta_cnt_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro z _
  exact hp z

theorem ta_cnt_pos {n : ℕ} (p : Fin n → Prop) (w : Fin n) (hw : p w) : 0 < ta_cnt p := by
  classical
  rw [ta_cnt_eq, Finset.card_pos]
  exact ⟨w, by simp [hw]⟩

theorem ta_cnt_exists {n : ℕ} (p : Fin n → Prop) (h : 0 < ta_cnt p) : ∃ w, p w := by
  by_contra hc
  have := ta_cnt_zero p (fun z hz => hc ⟨z, hz⟩)
  omega

theorem ta_cnt_le_one {n : ℕ} (p : Fin n → Prop) (hp : ∀ a b, p a → p b → a = b) :
    ta_cnt p ≤ 1 := by
  classical
  rw [ta_cnt_eq, Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hp a b ha hb

theorem ta_cnt_le {n : ℕ} (p : Fin n → Prop) : ta_cnt p ≤ n := by
  classical
  rw [ta_cnt_eq]
  calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

def ta_Ag (k q : ℕ) (pre : Fin k → Bool) (z : ℕ) : Prop :=
  ∀ i : Fin k, q ≤ i.val → z.testBit i.val = pre i

theorem ta_hi_bit {k : ℕ} (z : ℕ) (hz : z < 2 ^ k) (i : ℕ) (hi : k ≤ i) :
    z.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by norm_num) hi))

theorem ta_lt_of_bits {k q : ℕ} (pre : Fin k → Bool) (z w : ℕ) (hz : z < 2 ^ k)
    (hw : w < 2 ^ k) (az : ta_Ag k (q + 1) pre z) (aw : ta_Ag k (q + 1) pre w)
    (bz : z.testBit q = false) (bw : w.testBit q = true) : z < w := by
  apply Nat.lt_of_testBit q bz bw
  intro j hj
  by_cases hjk : j < k
  · rw [az ⟨j, hjk⟩ (by simpa using hj), aw ⟨j, hjk⟩ (by simpa using hj)]
  · rw [ta_hi_bit z hz j (by omega), ta_hi_bit w hw j (by omega)]

def ta_Inv (k : ℕ) (h : ℕ → Prop) (t q : ℕ) (pre : Fin k → Bool) (t' : ℕ) : Prop :=
  (∀ i : Fin k, i.val < q → pre i = false) ∧
  ∀ w : Fin (2 ^ k), h w.val →
    (ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val) = t ↔
      ta_Ag k q pre w.val ∧
        ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val ∧ ta_Ag k q pre z.val) = t')

theorem ta_Inv_init (k : ℕ) (h : ℕ → Prop) (t : ℕ) :
    ta_Inv k h t k (fun _ => false) t := by
  refine ⟨fun _ _ => rfl, fun w _ => ?_⟩
  have hA : ∀ z : ℕ, ta_Ag k k (fun _ => false) z := fun z i hi => absurd i.isLt (by omega)
  have e : ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val ∧ ta_Ag k k (fun _ => false) z.val) =
      ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val) :=
    ta_cnt_congr _ _ (fun z => ⟨fun H => ⟨H.1, H.2.1⟩, fun H => ⟨H.1, H.2, hA _⟩⟩)
  rw [e]
  exact ⟨fun H => ⟨hA _, H⟩, fun H => H.2⟩

theorem ta_Ag_upd {k q : ℕ} (hq : q < k) (pre : Fin k → Bool) (X : Bool) (z : ℕ) :
    ta_Ag k q (fun i => if i.val = q then X else pre i) z ↔
      ta_Ag k (q + 1) pre z ∧ z.testBit q = X := by
  constructor
  · intro H
    refine ⟨fun i hi => ?_, ?_⟩
    · have := H i (by omega)
      dsimp only at this
      rw [if_neg (by omega)] at this
      exact this
    · have := H ⟨q, hq⟩ le_rfl
      simpa using this
  · rintro ⟨H1, H2⟩ i hi
    dsimp only
    by_cases e : i.val = q
    · rw [if_pos e, e]; exact H2
    · rw [if_neg e]; exact H1 i (by omega)

theorem ta_Inv_step {k : ℕ} (h : ℕ → Prop) (t q : ℕ) (hq : q < k) (pre : Fin k → Bool) (t' : ℕ)
    (hI : ta_Inv k h t (q + 1) pre t') (c : ℕ)
    (hc : c = ta_cnt (fun z : Fin (2 ^ k) => h z.val ∧ ta_Ag k q pre z.val)) :
    ta_Inv k h t q (fun i => if i.val = q then decide (c ≤ t') else pre i)
      (if t' < c then t' else t' - c) := by
  obtain ⟨ha, hb⟩ := hI
  refine ⟨fun i hi => ?_, fun w hw => ?_⟩
  · dsimp only; rw [if_neg (by omega)]; exact ha i (by omega)
  rw [hb w hw]
  have hpre0 : (fun i : Fin k => if i.val = q then false else pre i) = pre := by
    funext i
    by_cases e : i.val = q
    · rw [if_pos e, ha i (by omega)]
    · rw [if_neg e]
  have hAg0 : ∀ z : ℕ, ta_Ag k q pre z ↔ ta_Ag k (q + 1) pre z ∧ z.testBit q = false := by
    intro z
    have := ta_Ag_upd hq pre false z
    rw [hpre0] at this
    exact this
  have hAg1 := ta_Ag_upd hq pre true
  by_cases hwA : ta_Ag k (q + 1) pre w.val
  swap
  · constructor
    · intro H; exact absurd H.1 hwA
    · intro H; exact absurd ((ta_Ag_upd hq pre _ _).1 H.1).1 hwA
  cases hbit : w.val.testBit q
  · have e1 : ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val ∧ ta_Ag k (q + 1) pre z.val) =
        ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val ∧ ta_Ag k q pre z.val) := by
      apply ta_cnt_congr
      intro z
      constructor
      · rintro ⟨z1, z2, z3⟩
        refine ⟨z1, z2, (hAg0 _).2 ⟨z3, ?_⟩⟩
        by_contra hz
        have hz' : z.val.testBit q = true := by simpa using hz
        have := ta_lt_of_bits pre w.val z.val w.isLt z.isLt hwA z3 hbit hz'
        exact absurd (Fin.lt_def.1 z1) (by omega)
      · rintro ⟨z1, z2, z3⟩
        exact ⟨z1, z2, ((hAg0 _).1 z3).1⟩
    have e2 : ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val ∧ ta_Ag k q pre z.val) < c := by
      rw [hc]
      exact ta_cnt_lt _ _ (fun z hz => ⟨hz.2.1, hz.2.2⟩)
        ⟨w, ⟨hw, (hAg0 _).2 ⟨hwA, hbit⟩⟩, fun H => lt_irrefl _ H.1⟩
    rw [e1]
    by_cases hct : t' < c
    · have hX : decide (c ≤ t') = false := decide_eq_false (by omega)
      rw [hX, hpre0, if_pos hct]
      exact ⟨fun H => ⟨(hAg0 _).2 ⟨hwA, hbit⟩, H.2⟩, fun H => ⟨hwA, H.2⟩⟩
    · have hX : decide (c ≤ t') = true := decide_eq_true (by omega)
      rw [hX]
      constructor
      · intro H; omega
      · intro H
        have := ((hAg1 _).1 H.1).2
        rw [hbit] at this
        exact absurd this (by simp)
  · have e3 : ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val ∧ ta_Ag k (q + 1) pre z.val) =
        c + ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val ∧
          ta_Ag k q (fun i => if i.val = q then true else pre i) z.val) := by
      rw [ta_cnt_split _ (fun z : Fin (2 ^ k) => z.val.testBit q = false), hc]
      congr 1
      · apply ta_cnt_congr
        intro z
        constructor
        · rintro ⟨⟨_, z2, z3⟩, z4⟩
          exact ⟨z2, (hAg0 _).2 ⟨z3, z4⟩⟩
        · rintro ⟨z2, z3⟩
          obtain ⟨z5, z6⟩ := (hAg0 _).1 z3
          refine ⟨⟨?_, z2, z5⟩, z6⟩
          exact Fin.lt_def.2 (ta_lt_of_bits pre z.val w.val z.isLt w.isLt z5 hwA z6 hbit)
      · apply ta_cnt_congr
        intro z
        constructor
        · rintro ⟨⟨z1, z2, z3⟩, z4⟩
          exact ⟨z1, z2, (hAg1 _).2 ⟨z3, by simpa using z4⟩⟩
        · rintro ⟨z1, z2, z3⟩
          obtain ⟨z5, z6⟩ := (hAg1 _).1 z3
          exact ⟨⟨z1, z2, z5⟩, by simp [z6]⟩
    rw [e3]
    by_cases hct : t' < c
    · have hX : decide (c ≤ t') = false := decide_eq_false (by omega)
      rw [hX, hpre0, if_pos hct]
      constructor
      · intro H; omega
      · intro H
        have := ((hAg0 _).1 H.1).2
        rw [hbit] at this
        exact absurd this (by simp)
    · have hX : decide (c ≤ t') = true := decide_eq_true (by omega)
      rw [hX, if_neg hct]
      constructor
      · intro H
        exact ⟨(hAg1 _).2 ⟨hwA, hbit⟩, by omega⟩
      · intro H
        exact ⟨hwA, by omega⟩

theorem ta_final {k : ℕ} (h : ℕ → Prop) (t : ℕ) (pre : Fin k → Bool) (t' : ℕ)
    (hI : ta_Inv k h t 0 pre t') (j : ℕ) (hj : j < k + 1) :
    (t' < ta_cnt (fun z : Fin (2 ^ k) => h z.val ∧ ta_Ag k 0 pre z.val) ∧
        (j = 0 ∨ ∃ q : Fin k, j = q.val + 1 ∧ pre q = true)) ↔
      ∃ w : Fin (2 ^ k), h w.val ∧ ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val) = t ∧
        (j = 0 ∨ w.val.testBit (j - 1) = true) := by
  obtain ⟨_, hb⟩ := hI
  have huniq : ∀ a b : Fin (2 ^ k), ta_Ag k 0 pre a.val → ta_Ag k 0 pre b.val → a = b := by
    intro a b ha hb'
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · rw [ha ⟨i, hi⟩ (Nat.zero_le _), hb' ⟨i, hi⟩ (Nat.zero_le _)]
    · rw [ta_hi_bit a.val a.isLt i (by omega), ta_hi_bit b.val b.isLt i (by omega)]
  have hempty : ∀ w : Fin (2 ^ k), ta_Ag k 0 pre w.val →
      ta_cnt (fun z : Fin (2 ^ k) => z < w ∧ h z.val ∧ ta_Ag k 0 pre z.val) = 0 := by
    intro w hw
    apply ta_cnt_zero
    rintro z ⟨z1, _, z3⟩
    have := huniq z w z3 hw
    rw [this] at z1
    exact lt_irrefl _ z1
  have hbitj : ∀ w : Fin (2 ^ k), ta_Ag k 0 pre w.val →
      ((j = 0 ∨ ∃ q : Fin k, j = q.val + 1 ∧ pre q = true) ↔
        (j = 0 ∨ w.val.testBit (j - 1) = true)) := by
    intro w hw
    constructor
    · rintro (h0 | ⟨q, hq1, hq2⟩)
      · exact Or.inl h0
      · right
        rw [hq1, Nat.add_sub_cancel, hw q (Nat.zero_le _)]
        exact hq2
    · rintro (h0 | h1)
      · exact Or.inl h0
      · by_cases hj0 : j = 0
        · exact Or.inl hj0
        · right
          refine ⟨⟨j - 1, by omega⟩, by simp; omega, ?_⟩
          rw [← hw ⟨j - 1, by omega⟩ (Nat.zero_le _)]
          exact h1
  constructor
  · rintro ⟨h1, h2⟩
    have hle := ta_cnt_le_one (fun z : Fin (2 ^ k) => h z.val ∧ ta_Ag k 0 pre z.val)
      (fun a b ha hb' => huniq a b ha.2 hb'.2)
    obtain ⟨w, hw1, hw2⟩ := ta_cnt_exists _ (lt_of_le_of_lt (Nat.zero_le _) h1)
    refine ⟨w, hw1, (hb w hw1).2 ⟨hw2, ?_⟩, (hbitj w hw2).1 h2⟩
    rw [hempty w hw2]
    omega
  · rintro ⟨w, hw1, hw2, hw3⟩
    obtain ⟨g1, g2⟩ := (hb w hw1).1 hw2
    rw [hempty w g1] at g2
    refine ⟨?_, (hbitj w g1).2 hw3⟩
    rw [← g2]
    exact ta_cnt_pos _ w ⟨hw1, g1⟩

noncomputable def ta_rnd (k : ℕ) (h : ℕ → Prop) (s : (Fin k → Bool) × ℕ) (q : ℕ) :
    (Fin k → Bool) × ℕ :=
  (fun i => if i.val = q then
      decide (ta_cnt (fun z : Fin (2 ^ k) => h z.val ∧ ta_Ag k q s.1 z.val) ≤ s.2) else s.1 i,
   if s.2 < ta_cnt (fun z : Fin (2 ^ k) => h z.val ∧ ta_Ag k q s.1 z.val) then s.2
   else s.2 - ta_cnt (fun z : Fin (2 ^ k) => h z.val ∧ ta_Ag k q s.1 z.val))

noncomputable def ta_st (k : ℕ) (h : ℕ → Prop) (t : ℕ) : ℕ → (Fin k → Bool) × ℕ
  | 0 => (fun _ => false, t)
  | d + 1 => ta_rnd k h (ta_st k h t d) (k - 1 - d)

theorem ta_st_inv (k : ℕ) (h : ℕ → Prop) (t : ℕ) :
    ∀ d, d ≤ k → ta_Inv k h t (k - d) (ta_st k h t d).1 (ta_st k h t d).2 := by
  intro d
  induction d with
  | zero => intro _; exact ta_Inv_init k h t
  | succ d ih =>
    intro hd
    have ih' := ih (by omega)
    have e : k - d = (k - 1 - d) + 1 := by omega
    rw [e] at ih'
    have e2 : k - (d + 1) = k - 1 - d := by omega
    rw [e2]
    exact ta_Inv_step h t (k - 1 - d) (by omega) _ _ ih' _ rfl

theorem ta_st_le (k : ℕ) (h : ℕ → Prop) (t : ℕ) : ∀ d, (ta_st k h t d).2 ≤ t := by
  intro d
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    show (ta_rnd k h (ta_st k h t d) (k - 1 - d)).2 ≤ t
    unfold ta_rnd
    dsimp only
    split_ifs <;> omega

theorem ta_st_fold (k : ℕ) (h : ℕ → Prop) (t : ℕ) (n : ℕ) :
    ((List.range n).map (fun d => k - 1 - d)).foldl (ta_rnd k h) (fun _ => false, t) =
      ta_st k h t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    rfl

abbrev ta_TI (k r m : ℕ) : Type := Dat k r m ⊕ (Fin (k + 1) ⊕ Fin (k + 1))

abbrev ta_St (k r m : ℕ) : Type := ta_TI k r m ⊕ (Fin k ⊕ Fin (k + 2))

def ta_arg {k r m : ℕ} (q : ℕ) (v : ta_St k r m → Bool) : CoreIn k r m → Bool :=
  Sum.elim (fun d => v (Sum.inl (Sum.inl d)))
    (Sum.elim (fun i : Fin k => decide (q ≤ i.val)) (fun i => v (Sum.inr (Sum.inl i))))

def ta_pad {k : ℕ} (u : Unit ⊕ Fin (k + 1) → Bool) : BitVec (k + 2) :=
  bv (fun i : Fin (k + 2) => if h : i.val < k + 1 then u (Sum.inr ⟨i.val, h⟩) else false)

def ta_dw {k r m : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool) (q : ℕ)
    (v : ta_St k r m → Bool) : BitVec (k + 2) :=
  bv (fun i : Fin (k + 2) => v (Sum.inr (Sum.inr i))) - ta_pad (F (ta_arg q v))

def ta_post {k r m : ℕ} (q : ℕ) (u : ta_St k r m ⊕ Fin (k + 2) → Bool) : ta_St k r m → Bool :=
  Sum.elim (fun x => u (Sum.inl (Sum.inl x)))
    (Sum.elim (fun i : Fin k => if i.val = q then !u (Sum.inr (Fin.last (k + 1)))
        else u (Sum.inl (Sum.inr (Sum.inl i))))
      (fun i : Fin (k + 2) => if u (Sum.inr (Fin.last (k + 1))) = true
        then u (Sum.inl (Sum.inr (Sum.inr i))) else u (Sum.inr i)))

def ta_R {k r m : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool) (q : ℕ)
    (v : ta_St k r m → Bool) : ta_St k r m → Bool :=
  ta_post q (Sum.elim v (fun i : Fin (k + 2) => (ta_dw F q v).getLsbD i.val))

def ta_init {k r m : ℕ} (u : ta_TI k r m → Bool) : ta_St k r m → Bool :=
  Sum.elim (fun x => u x)
    (Sum.elim (fun _ : Fin k => false)
      (fun i : Fin (k + 2) => if h : i.val < k + 1 then u (Sum.inr (Sum.inl ⟨i.val, h⟩))
        else false))

def ta_jeq {k r m : ℕ} (n : ℕ) (v : ta_St k r m → Bool) : Bool :=
  decide (∀ i : Fin (k + 1), (if n.testBit i.val = true then v (Sum.inl (Sum.inr (Sum.inr i)))
    else !v (Sum.inl (Sum.inr (Sum.inr i)))) = true)

def ta_jb {k r m : ℕ} (v : ta_St k r m → Bool) : Bool :=
  ta_jeq 0 v || decide (∃ q : Fin k, (ta_jeq (q.val + 1) v && v (Sum.inr (Sum.inl q))) = true)

def ta_out {k r m : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (v : ta_St k r m → Bool) : Bool :=
  F (ta_arg 0 v) (Sum.inl ()) && (ta_dw F 0 v).getLsbD (k + 1) && ta_jb v

def ta_top {k r m : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (u : ta_TI k r m → Bool) : Bool :=
  ta_out F (((List.range k).map (fun d => k - 1 - d)).foldl (fun acc q => ta_R F q acc)
    (ta_init u))

theorem ta_call {k r m S : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (hF : Cmp (CoreIn k r m) (Unit ⊕ Fin (k + 1)) S F) (q : ℕ) :
    Cmp (ta_St k r m) (Unit ⊕ Fin (k + 1)) (S + k) (fun v => F (ta_arg q v)) := by
  have h1 : Cmp (ta_St k r m) (CoreIn k r m) k (fun v => ta_arg q v) := by
    have a := Cmp.wire (ι := ta_St k r m) (fun d : Dat k r m => Sum.inl (Sum.inl d))
    have b := Cmp.ofBits (ι := ta_St k r m) (F := fun _ (i : Fin k) => decide (q ≤ i.val))
      (fun i => Cb.const _)
    have c := Cmp.wire (ι := ta_St k r m) (fun i : Fin k => Sum.inr (Sum.inl i))
    refine ((Cmp.pair a (Cmp.pair b c)).mono ?_).congr ?_
    · simp only [Fintype.card_fin]; omega
    · intro v x
      rcases x with d | i | i <;> rfl
  exact (Cmp.comp h1 hF).mono (by omega)

theorem ta_cw_pad (k : ℕ) : Cw (Unit ⊕ Fin (k + 1)) (k + 2) (k + 2) (ta_pad (k := k)) := by
  have h : ∀ i : Fin (k + 2), Cb (Unit ⊕ Fin (k + 1)) 1
      (fun v => (ta_pad v).getLsbD i.val) := by
    intro i
    by_cases hi : i.val < k + 1
    · refine ((Cb.var (Sum.inr ⟨i.val, hi⟩)).mono (by omega)).congr (fun v => ?_)
      rw [ta_pad, getLsbD_bv, dif_pos hi]
    · refine (Cb.const false).congr (fun v => ?_)
      rw [ta_pad, getLsbD_bv, dif_neg hi]
  exact (Cw.ofBits h).mono (by omega)

theorem ta_cw_dw {k r m S : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (hF : Cmp (CoreIn k r m) (Unit ⊕ Fin (k + 1)) S F) (q : ℕ) :
    Cw (ta_St k r m) (k + 2) (S + 22 * (k + 3)) (ta_dw F q) := by
  have a := Cw.var (ι := ta_St k r m) (fun i : Fin (k + 2) => Sum.inr (Sum.inr i))
  have b := Cw.comp (ta_call F hF q) (ta_cw_pad k)
  exact (Cw.sub a b).mono (by omega)

theorem ta_cmp_post {k r m : ℕ} (q : ℕ) :
    Cmp (ta_St k r m ⊕ Fin (k + 2)) (ta_St k r m) (5 * (k + 2)) (ta_post q) := by
  have a := Cmp.wire (ι := ta_St k r m ⊕ Fin (k + 2))
    (fun x : ta_TI k r m => Sum.inl (Sum.inl x))
  have b : Cmp (ta_St k r m ⊕ Fin (k + 2)) (Fin k) (k * 1)
      (fun u i => if i.val = q then !u (Sum.inr (Fin.last (k + 1)))
        else u (Sum.inl (Sum.inr (Sum.inl i)))) := by
    have := Cmp.ofBits (ι := ta_St k r m ⊕ Fin (k + 2)) (s := 1)
      (F := fun u (i : Fin k) => if i.val = q then !u (Sum.inr (Fin.last (k + 1)))
        else u (Sum.inl (Sum.inr (Sum.inl i))))
      (fun i => by
        by_cases hi : i.val = q
        · exact ((Cb.not (Cb.var (Sum.inr (Fin.last (k + 1))))).mono (by omega)).congr
            (fun u => by rw [if_pos hi])
        · exact ((Cb.var (Sum.inl (Sum.inr (Sum.inl i)))).mono (by omega)).congr
            (fun u => by rw [if_neg hi]))
    exact this.mono (by simp only [Fintype.card_fin]; omega)
  have c : Cmp (ta_St k r m ⊕ Fin (k + 2)) (Fin (k + 2)) ((k + 2) * 4)
      (fun u i => if u (Sum.inr (Fin.last (k + 1))) = true
        then u (Sum.inl (Sum.inr (Sum.inr i))) else u (Sum.inr i)) := by
    have := Cmp.ofBits (ι := ta_St k r m ⊕ Fin (k + 2)) (s := 4)
      (F := fun u (i : Fin (k + 2)) => if u (Sum.inr (Fin.last (k + 1))) = true
        then u (Sum.inl (Sum.inr (Sum.inr i))) else u (Sum.inr i))
      (fun i => (Cb.mux (Cb.var (Sum.inr (Fin.last (k + 1))))
        (Cb.var (Sum.inl (Sum.inr (Sum.inr i)))) (Cb.var (Sum.inr i))).mono (by omega))
    exact this.mono (by simp only [Fintype.card_fin]; omega)
  refine ((Cmp.pair a (Cmp.pair b c)).mono (by omega)).congr ?_
  intro v x
  rcases x with d | i | i <;> rfl

theorem ta_cmp_R {k r m S : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (hF : Cmp (CoreIn k r m) (Unit ⊕ Fin (k + 1)) S F) (q : ℕ) :
    Cmp (ta_St k r m) (ta_St k r m) (S + 30 * (k + 3)) (ta_R F q) :=
  (Cmp.comp (Cmp.keep (ta_cw_dw F hF q)) (ta_cmp_post q)).mono (by omega)

theorem ta_cmp_init (k r m : ℕ) :
    Cmp (ta_TI k r m) (ta_St k r m) (2 * k + 2) (ta_init (k := k) (r := r) (m := m)) := by
  have a := Cmp.wire (ι := ta_TI k r m) (fun x : ta_TI k r m => x)
  have b := Cmp.ofBits (ι := ta_TI k r m) (F := fun _ (_ : Fin k) => false)
    (fun i => Cb.const _)
  have c : Cmp (ta_TI k r m) (Fin (k + 2)) ((k + 2) * 1)
      (fun u i => if h : i.val < k + 1 then u (Sum.inr (Sum.inl ⟨i.val, h⟩)) else false) := by
    have := Cmp.ofBits (ι := ta_TI k r m) (s := 1)
      (F := fun u (i : Fin (k + 2)) =>
        if h : i.val < k + 1 then u (Sum.inr (Sum.inl ⟨i.val, h⟩)) else false)
      (fun i => by
        by_cases hi : i.val < k + 1
        · exact ((Cb.var (Sum.inr (Sum.inl ⟨i.val, hi⟩))).mono (by omega)).congr
            (fun u => by rw [dif_pos hi])
        · exact (Cb.const false).congr (fun u => by rw [dif_neg hi]))
    exact this.mono (by simp only [Fintype.card_fin]; omega)
  refine ((Cmp.pair a (Cmp.pair b c)).mono ?_).congr ?_
  · simp only [Fintype.card_fin]; omega
  · intro v x
    rcases x with d | i | i <;> rfl

theorem ta_cb_jeq {k r m : ℕ} (n : ℕ) : Cb (ta_St k r m) (2 * k + 3) (ta_jeq n) := by
  have h : ∀ i : Fin (k + 1), Cb (ta_St k r m) 1
      (fun v => if n.testBit i.val = true then v (Sum.inl (Sum.inr (Sum.inr i)))
        else !v (Sum.inl (Sum.inr (Sum.inr i)))) := by
    intro i
    by_cases hb : n.testBit i.val = true
    · exact ((Cb.var (Sum.inl (Sum.inr (Sum.inr i)))).mono (by omega)).congr
        (fun v => by rw [if_pos hb])
    · exact ((Cb.not (Cb.var (Sum.inl (Sum.inr (Sum.inr i))))).mono (by omega)).congr
        (fun v => by rw [if_neg hb])
  refine ((Cb.bigAnd h).mono (S' := 2 * k + 3) (by simp only [Fintype.card_fin]; omega)).congr
    (fun v => ?_)
  unfold ta_jeq
  congr

theorem ta_cb_jb (k r m : ℕ) :
    Cb (ta_St k r m) (2 * k + 3 + (k * (2 * k + 4 + 1) + 1) + 1)
      (ta_jb (k := k) (r := r) (m := m)) := by
  have h : ∀ q : Fin k, Cb (ta_St k r m) (2 * k + 4)
      (fun v => ta_jeq (q.val + 1) v && v (Sum.inr (Sum.inl q))) := fun q =>
    (Cb.and (ta_cb_jeq (q.val + 1)) (Cb.var (Sum.inr (Sum.inl q)))).mono (by omega)
  have hb := (Cb.bigOr h).mono (S' := k * (2 * k + 4 + 1) + 1)
    (by simp only [Fintype.card_fin]; exact le_rfl)
  refine (Cb.or (ta_cb_jeq 0) hb).congr (fun v => ?_)
  unfold ta_jb
  congr

theorem ta_cb_out {k r m S : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (hF : Cmp (CoreIn k r m) (Unit ⊕ Fin (k + 1)) S F) :
    Cb (ta_St k r m) (2 * S + (2 * (k * k) + 30 * k + 73)) (ta_out F) := by
  have a : Cb (ta_St k r m) (S + k) (fun v => F (ta_arg 0 v) (Sum.inl ())) :=
    Cb.comp (ta_call F hF 0) (Cb.var (Sum.inl ()))
  have b : Cb (ta_St k r m) (S + 22 * (k + 3))
      (fun v => (ta_dw F 0 v).getLsbD (k + 1)) :=
    Cb.comp (ta_cw_dw F hF 0) (Cb.var (Fin.last (k + 1)))
  refine (Cb.and (Cb.and a b) (ta_cb_jb k r m)).mono ?_
  have e : k * (2 * k + 4 + 1) = 2 * (k * k) + 5 * k := by ring
  omega

theorem ta_cb_top {k r m S : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (hF : Cmp (CoreIn k r m) (Unit ⊕ Fin (k + 1)) S F) :
    Cb (ta_TI k r m) ((k + 2) * S + (32 * (k * k) + 122 * k + 75)) (ta_top F) := by
  have hfold := Cmp.foldl (ι := ta_St k r m) ((List.range k).map (fun d => k - 1 - d))
    (fun q => ta_R F q) (fun q _ => ta_cmp_R F hF q)
  have h := Cb.comp (Cmp.comp (ta_cmp_init k r m) hfold) (ta_cb_out F hF)
  refine h.mono ?_
  simp only [List.length_map, List.length_range]
  have e1 : k * (S + 30 * (k + 3)) = k * S + 30 * (k * k) + 90 * k := by ring
  have e2 : (k + 2) * S = k * S + 2 * S := by ring
  omega

theorem ta_sub (W a c : ℕ) (ha : a < 2 ^ W) (hc : c < 2 ^ W) :
    (BitVec.ofNat (W + 1) a - BitVec.ofNat (W + 1) c).getLsbD W = decide (a < c) ∧
    (c ≤ a → BitVec.ofNat (W + 1) a - BitVec.ofNat (W + 1) c = BitVec.ofNat (W + 1) (a - c)) := by
  have hP : 2 ^ (W + 1) = 2 * 2 ^ W := by rw [pow_succ]; ring
  have hN : (BitVec.ofNat (W + 1) a - BitVec.ofNat (W + 1) c).toNat =
      (2 * 2 ^ W - c + a) % (2 * 2 ^ W) := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hP,
      Nat.mod_eq_of_lt (by omega : a < 2 * 2 ^ W), Nat.mod_eq_of_lt (by omega : c < 2 * 2 ^ W)]
  constructor
  · show (BitVec.ofNat (W + 1) a - BitVec.ofNat (W + 1) c).toNat.testBit W = _
    rw [hN]
    by_cases hac : a < c
    · rw [Nat.mod_eq_of_lt (by omega), Nat.testBit_eq_decide_div_mod_eq,
        Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
      simp [hac]
    · have e : 2 * 2 ^ W - c + a = (a - c) + 2 * 2 ^ W := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
        Nat.testBit_lt_two_pow (by omega)]
      simp [hac]
  · intro hca
    apply BitVec.eq_of_toNat_eq
    rw [hN, BitVec.toNat_ofNat, hP]
    have e : 2 * 2 ^ W - c + a = (a - c) + 2 * 2 ^ W := by omega
    rw [e, Nat.add_mod_right]

theorem ta_bv_pad {k : ℕ} (f : Fin (k + 2) → Bool) (c : ℕ) (hc : c < 2 ^ (k + 1))
    (hf : ∀ i : Fin (k + 2), f i = if i.val < k + 1 then c.testBit i.val else false) :
    bv f = BitVec.ofNat (k + 2) c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := getLsbD_bv f ⟨i, hi⟩
  dsimp only at this
  rw [this, hf, BitVec.getLsbD_ofNat]
  by_cases h : i < k + 1
  · simp [h, hi]
  · have : i = k + 1 := by omega
    subst this
    simp [Nat.testBit_lt_two_pow hc]

theorem ta_bits_eq (n a b : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (∀ i : Fin n, (if b.testBit i.val = true then a.testBit i.val else !a.testBit i.val) = true) ↔
      a = b := by
  constructor
  · intro H
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < n
    · have := H ⟨i, hi⟩
      dsimp only at this
      by_cases hbi : b.testBit i = true
      · rw [if_pos hbi] at this; rw [this, hbi]
      · rw [if_neg hbi] at this
        simp only [Bool.not_eq_true] at hbi
        simp only [Bool.not_eq_true'] at this
        rw [this, hbi]
    · rw [ta_hi_bit a ha i (by omega), ta_hi_bit b hb i (by omega)]
  · rintro rfl i
    by_cases hbi : a.testBit i.val = true
    · rw [if_pos hbi]; exact hbi
    · rw [if_neg hbi]; simpa using hbi

def ta_Rel {k r m : ℕ} (u : ta_TI k r m → Bool) (v : ta_St k r m → Bool)
    (s : (Fin k → Bool) × ℕ) : Prop :=
  (∀ x, v (Sum.inl x) = u x) ∧ (∀ i, v (Sum.inr (Sum.inl i)) = s.1 i) ∧
    bv (fun i : Fin (k + 2) => v (Sum.inr (Sum.inr i))) = BitVec.ofNat (k + 2) s.2 ∧
    s.2 < 2 ^ (k + 1)

theorem ta_cntPin_eq (k : ℕ) (h : ℕ → Prop) (q : ℕ) (pre : Fin k → Bool) :
    cntPin k h (fun i => decide (q ≤ i.val)) pre =
      ta_cnt (fun z : Fin (2 ^ k) => h z.val ∧ ta_Ag k q pre z.val) := by
  unfold cntPin ta_cnt ta_Ag
  simp only [decide_eq_true_eq]

theorem ta_cnt_bound (k : ℕ) (p : Fin (2 ^ k) → Prop) : ta_cnt p < 2 ^ (k + 1) := by
  have := ta_cnt_le p
  have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
  omega

theorem ta_dw_sem {k r m b : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (hF : CoreSpec k r m b F)
    (nr nc : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin k → Fin (2 ^ m))
    (ord : Fin k → Fin k) (y : Fin (2 ^ m)) (ut : Fin (k + 1) ⊕ Fin (k + 1) → Bool)
    (hp : passP k r m b A B ord)
    (v : ta_St k r m → Bool) (s : (Fin k → Bool) × ℕ) (q : ℕ)
    (hr : ta_Rel (Sum.elim (encD nr nc cr cc A B ord y) ut) v s) :
    (ta_dw F q v).getLsbD (k + 1) =
      decide (s.2 < ta_cnt (fun z : Fin (2 ^ k) =>
        reportN k r m nr nc cr cc A B z.val = y.val ∧ ta_Ag k q s.1 z.val)) ∧
    (ta_cnt (fun z : Fin (2 ^ k) =>
        reportN k r m nr nc cr cc A B z.val = y.val ∧ ta_Ag k q s.1 z.val) ≤ s.2 →
      ta_dw F q v = BitVec.ofNat (k + 2) (s.2 - ta_cnt (fun z : Fin (2 ^ k) =>
        reportN k r m nr nc cr cc A B z.val = y.val ∧ ta_Ag k q s.1 z.val))) := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have harg : ta_arg q v = Sum.elim (encD nr nc cr cc A B ord y)
      (Sum.elim (fun i : Fin k => decide (q ≤ i.val)) s.1) := by
    funext x
    rcases x with d | i | i
    · exact h1 (Sum.inl d)
    · rfl
    · exact h2 i
  have hc := (hF nr nc cr cc A B ord y (fun i : Fin k => decide (q ≤ i.val)) s.1).2 hp
  rw [ta_cntPin_eq] at hc
  have hpad : ta_pad (F (ta_arg q v)) = BitVec.ofNat (k + 2) (ta_cnt (fun z : Fin (2 ^ k) =>
        reportN k r m nr nc cr cc A B z.val = y.val ∧ ta_Ag k q s.1 z.val)) := by
    apply ta_bv_pad _ _ (ta_cnt_bound k _)
    intro i
    by_cases hi : i.val < k + 1
    · rw [dif_pos hi, if_pos hi, harg, hc ⟨i.val, hi⟩]
    · rw [dif_neg hi, if_neg hi]
  unfold ta_dw
  rw [hpad, h3]
  exact ta_sub (k + 1) _ _ h4 (ta_cnt_bound k _)

theorem ta_R_rel {k r m b : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (hF : CoreSpec k r m b F)
    (nr nc : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin k → Fin (2 ^ m))
    (ord : Fin k → Fin k) (y : Fin (2 ^ m)) (ut : Fin (k + 1) ⊕ Fin (k + 1) → Bool)
    (hp : passP k r m b A B ord)
    (v : ta_St k r m → Bool) (s : (Fin k → Bool) × ℕ) (q : ℕ)
    (hr : ta_Rel (Sum.elim (encD nr nc cr cc A B ord y) ut) v s) :
    ta_Rel (Sum.elim (encD nr nc cr cc A B ord y) ut) (ta_R F q v)
      (ta_rnd k (fun w => reportN k r m nr nc cr cc A B w = y.val) s q) := by
  obtain ⟨d1, d2⟩ := ta_dw_sem F hF nr nc cr cc A B ord y ut hp v s q hr
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have hlast : (ta_dw F q v).getLsbD ((Fin.last (k + 1) : Fin (k + 2)).val) =
      decide (s.2 < ta_cnt (fun z : Fin (2 ^ k) =>
        reportN k r m nr nc cr cc A B z.val = y.val ∧ ta_Ag k q s.1 z.val)) := d1
  refine ⟨fun x => h1 x, fun i => ?_, ?_, ?_⟩
  · show (if i.val = q then !(ta_dw F q v).getLsbD ((Fin.last (k + 1) : Fin (k + 2)).val)
      else v (Sum.inr (Sum.inl i))) = _
    rw [hlast, h2 i]
    unfold ta_rnd
    dsimp only
    by_cases hi : i.val = q
    · rw [if_pos hi, if_pos hi]
      by_cases hc : s.2 < ta_cnt (fun z : Fin (2 ^ k) =>
        reportN k r m nr nc cr cc A B z.val = y.val ∧ ta_Ag k q s.1 z.val)
      · simp [hc]
      · simp [hc]; omega
    · rw [if_neg hi, if_neg hi]
  · show bv (fun i : Fin (k + 2) =>
      if (ta_dw F q v).getLsbD ((Fin.last (k + 1) : Fin (k + 2)).val) = true
        then v (Sum.inr (Sum.inr i)) else (ta_dw F q v).getLsbD i.val) = _
    rw [hlast]
    unfold ta_rnd
    dsimp only
    by_cases hc : s.2 < ta_cnt (fun z : Fin (2 ^ k) =>
        reportN k r m nr nc cr cc A B z.val = y.val ∧ ta_Ag k q s.1 z.val)
    · simp only [hc, decide_true, if_true]
      exact h3
    · simp only [hc, decide_false, if_false, Bool.false_eq_true]
      rw [bv_getLsbD]
      exact d2 (by omega)
  · unfold ta_rnd
    dsimp only
    split_ifs <;> omega

theorem ta_R_data {k r m : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (u : ta_TI k r m → Bool) (L : List ℕ) :
    ∀ v : ta_St k r m → Bool, (∀ x, v (Sum.inl x) = u x) →
      ∀ x, (L.foldl (fun acc q => ta_R F q acc) v) (Sum.inl x) = u x := by
  induction L with
  | nil => intro v hv; exact hv
  | cons q L ih =>
    intro v hv
    exact ih (ta_R F q v) (fun x => hv x)

theorem ta_fold_rel {k r m b : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (hF : CoreSpec k r m b F)
    (nr nc : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin k → Fin (2 ^ m))
    (ord : Fin k → Fin k) (y : Fin (2 ^ m)) (ut : Fin (k + 1) ⊕ Fin (k + 1) → Bool)
    (hp : passP k r m b A B ord) (t : ℕ)
    (v : ta_St k r m → Bool)
    (hr : ta_Rel (Sum.elim (encD nr nc cr cc A B ord y) ut) v (fun _ => false, t)) (n : ℕ) :
    ta_Rel (Sum.elim (encD nr nc cr cc A B ord y) ut)
      (((List.range n).map (fun d => k - 1 - d)).foldl (fun acc q => ta_R F q acc) v)
      (ta_st k (fun w => reportN k r m nr nc cr cc A B w = y.val) t n) := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    exact ta_R_rel F hF nr nc cr cc A B ord y ut hp _ _ _ ih

theorem ta_jeq_sem {k r m : ℕ} (v : ta_St k r m → Bool) (j n : ℕ) (hj : j < k + 1)
    (hn : n < k + 1)
    (hv : ∀ i : Fin (k + 1), v (Sum.inl (Sum.inr (Sum.inr i))) = j.testBit i.val) :
    ta_jeq n v = decide (j = n) := by
  have hlt : ∀ a : ℕ, a < k + 1 → a < 2 ^ (k + 1) := fun a ha =>
    lt_trans ha (Nat.lt_two_pow_self)
  unfold ta_jeq
  simp only [hv]
  rw [decide_eq_decide]
  exact ta_bits_eq (k + 1) j n (hlt j hj) (hlt n hn)

theorem ta_jb_sem {k r m : ℕ} (v : ta_St k r m → Bool) (j : ℕ) (hj : j < k + 1)
    (pre : Fin k → Bool)
    (hv : ∀ i : Fin (k + 1), v (Sum.inl (Sum.inr (Sum.inr i))) = j.testBit i.val)
    (hpre : ∀ i, v (Sum.inr (Sum.inl i)) = pre i) :
    (ta_jb v = true) ↔ (j = 0 ∨ ∃ q : Fin k, j = q.val + 1 ∧ pre q = true) := by
  unfold ta_jb
  rw [ta_jeq_sem v j 0 hj (by omega) hv]
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro (h0 | ⟨q, hq1, hq2⟩)
    · exact Or.inl h0
    · rw [ta_jeq_sem v j (q.val + 1) hj (by omega) hv] at hq1
      exact Or.inr ⟨q, by simpa using hq1, by rw [← hpre q]; exact hq2⟩
  · rintro (h0 | ⟨q, hq1, hq2⟩)
    · exact Or.inl h0
    · refine Or.inr ⟨q, ?_, by rw [hpre q]; exact hq2⟩
      rw [ta_jeq_sem v j (q.val + 1) hj (by omega) hv]
      simpa using hq1

theorem ta_top_sem {k r m b : ℕ} (F : (CoreIn k r m → Bool) → (Unit ⊕ Fin (k + 1)) → Bool)
    (hF : CoreSpec k r m b F)
    (nr nc : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin k → Fin (2 ^ m))
    (ord : Fin k → Fin k) (y : Fin (2 ^ m)) (t : Fin (2 ^ (k + 1))) (j : Fin (k + 1)) :
    (ta_top F (Sum.elim (encD nr nc cr cc A B ord y)
        (Sum.elim (fun i => t.val.testBit i.val) (fun i => j.val.testBit i.val))) = true) ↔
      (passP k r m b A B ord ∧ ∃ w : Fin (2 ^ k),
        reportN k r m nr nc cr cc A B w.val = y.val ∧
        Nat.card {z : Fin (2 ^ k) // z < w ∧ reportN k r m nr nc cr cc A B z.val = y.val}
          = t.val ∧
        (j.val = 0 ∨ w.val.testBit (j.val - 1) = true)) := by
  set ut : Fin (k + 1) ⊕ Fin (k + 1) → Bool :=
    Sum.elim (fun i => t.val.testBit i.val) (fun i => j.val.testBit i.val) with hut
  set u : ta_TI k r m → Bool := Sum.elim (encD nr nc cr cc A B ord y) ut with hu
  have hinit : ta_Rel u (ta_init u) (fun _ => false, t.val) := by
    refine ⟨fun x => rfl, fun i => rfl, ?_, t.isLt⟩
    apply ta_bv_pad _ _ t.isLt
    intro i
    by_cases hi : i.val < k + 1
    · show (if h : i.val < k + 1 then u (Sum.inr (Sum.inl ⟨i.val, h⟩)) else false) = _
      rw [dif_pos hi, if_pos hi]
      rfl
    · show (if h : i.val < k + 1 then u (Sum.inr (Sum.inl ⟨i.val, h⟩)) else false) = _
      rw [dif_neg hi, if_neg hi]
  unfold ta_top ta_out
  by_cases hp : passP k r m b A B ord
  swap
  · have hd := ta_R_data F u ((List.range k).map (fun d => k - 1 - d)) (ta_init u)
      (fun x => rfl)
    set vf := ((List.range k).map (fun d => k - 1 - d)).foldl (fun acc q => ta_R F q acc)
      (ta_init u) with hvf
    have harg : ta_arg 0 vf = Sum.elim (encD nr nc cr cc A B ord y)
        (Sum.elim (fun i : Fin k => decide (0 ≤ i.val)) (fun i => vf (Sum.inr (Sum.inl i)))) := by
      funext x
      rcases x with d | i | i
      · exact hd (Sum.inl d)
      · rfl
      · rfl
    have h1 := (hF nr nc cr cc A B ord y (fun i : Fin k => decide (0 ≤ i.val))
      (fun i => vf (Sum.inr (Sum.inl i)))).1
    rw [← harg] at h1
    constructor
    · intro H
      simp only [Bool.and_eq_true] at H
      exact absurd (h1.1 H.1.1) hp
    · intro H; exact absurd H.1 hp
  · have hrel := ta_fold_rel F hF nr nc cr cc A B ord y ut hp t.val (ta_init u) hinit k
    set vf := ((List.range k).map (fun d => k - 1 - d)).foldl (fun acc q => ta_R F q acc)
      (ta_init u) with hvf
    set sf := ta_st k (fun w => reportN k r m nr nc cr cc A B w = y.val) t.val k with hsf
    have hinv := ta_st_inv k (fun w => reportN k r m nr nc cr cc A B w = y.val) t.val k le_rfl
    rw [Nat.sub_self] at hinv
    obtain ⟨d1, _⟩ := ta_dw_sem F hF nr nc cr cc A B ord y ut hp vf sf 0 hrel
    have harg : ta_arg 0 vf = Sum.elim (encD nr nc cr cc A B ord y)
        (Sum.elim (fun i : Fin k => decide (0 ≤ i.val)) sf.1) := by
      funext x
      rcases x with d | i | i
      · exact hrel.1 (Sum.inl d)
      · rfl
      · exact hrel.2.1 i
    have h1 := (hF nr nc cr cc A B ord y (fun i : Fin k => decide (0 ≤ i.val)) sf.1).1
    rw [← harg] at h1
    have hjb := ta_jb_sem vf j.val j.isLt sf.1
      (fun i => hrel.1 (Sum.inr (Sum.inr i))) hrel.2.1
    have hfin := ta_final (fun w => reportN k r m nr nc cr cc A B w = y.val) t.val sf.1 sf.2
      hinv j.val j.isLt
    simp only [Bool.and_eq_true]
    rw [d1, hjb, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨_, g2⟩, g3⟩
      exact ⟨hp, hfin.1 ⟨g2, g3⟩⟩
    · rintro ⟨_, g⟩
      obtain ⟨g2, g3⟩ := hfin.2 g
      exact ⟨⟨h1.2 hp, g2⟩, g3⟩

def schedN (k r : ℕ) (c : Fin r → Fin (2^k)) : List Bool :=
  (List.finRange r).flatMap (fun j => bitsN k (c j).val)

def packN (k m : ℕ) (A : Fin k → Fin (2^m)) : List Bool :=
  (List.finRange k).flatMap (fun p => bitsN m (A p).val)

def inputN (k r m : ℕ) (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k))
    (A B : Fin k → Fin (2^m)) (ord : Fin k → Fin k) (y : Fin (2^m))
    (t : Fin (2^(k+1))) (j : Fin (k+1)) : List Bool :=
  bitsN k nr.val ++ bitsN k nc.val ++ schedN k r cr ++ schedN k r cc ++ packN k m A ++
    packN k m B ++ (List.ofFn ord).flatMap (fun p => bitsN k p.val) ++ bitsN m y.val ++
    bitsN (k+1) t.val ++ bitsN (k+1) j.val

theorem ta_bits_len (a x : ℕ) : (bitsN a x).length = a := by simp [bitsN]

theorem ta_bits_getD (a x i : ℕ) (hi : i < a) : (bitsN a x).getD i false = x.testBit i := by
  simp [bitsN, List.getD_eq_getElem?_getD, hi]

def ta_ws (k r m : ℕ) : ta_TI k r m → ℕ :=
  Sum.elim
    (Sum.elim (Sum.elim (fun i => i.val) (fun i => k + i.val))
      (Sum.elim (Sum.elim (fun p => k + k + (p.1.val * k + p.2.val))
          (fun p => k + k + r * k + (p.1.val * k + p.2.val)))
        (Sum.elim (Sum.elim (fun p => k + k + r * k + r * k + (p.1.val * m + p.2.val))
            (fun p => k + k + r * k + r * k + k * m + (p.1.val * m + p.2.val)))
          (Sum.elim (fun p => k + k + r * k + r * k + k * m + k * m + (p.1.val * k + p.2.val))
            (fun i => k + k + r * k + r * k + k * m + k * m + k * k + i.val)))))
    (Sum.elim (fun i => k + k + r * k + r * k + k * m + k * m + k * k + m + i.val)
      (fun i => k + k + r * k + r * k + k * m + k * m + k * k + m + (k + 1) + i.val))

theorem ta_ws_lt (k r m : ℕ) (x : ta_TI k r m) :
    ta_ws k r m x < k + k + r * k + r * k + k * m + k * m + k * k + m + (k + 1) + (k + 1) := by
  rcases x with ((i | i) | ((p | p) | ((p | p) | (p | i)))) | (i | i)
  · have := i.isLt
    simp only [ta_ws, Sum.elim_inl]; omega
  · have := i.isLt
    simp only [ta_ws, Sum.elim_inl, Sum.elim_inr]; omega
  · have := fin_idx_lt p.1.val r p.2.val k p.1.isLt p.2.isLt
    simp only [ta_ws, Sum.elim_inl, Sum.elim_inr]; omega
  · have := fin_idx_lt p.1.val r p.2.val k p.1.isLt p.2.isLt
    simp only [ta_ws, Sum.elim_inl, Sum.elim_inr]; omega
  · have := fin_idx_lt p.1.val k p.2.val m p.1.isLt p.2.isLt
    simp only [ta_ws, Sum.elim_inl, Sum.elim_inr]; omega
  · have := fin_idx_lt p.1.val k p.2.val m p.1.isLt p.2.isLt
    simp only [ta_ws, Sum.elim_inl, Sum.elim_inr]; omega
  · have := fin_idx_lt p.1.val k p.2.val k p.1.isLt p.2.isLt
    simp only [ta_ws, Sum.elim_inl, Sum.elim_inr]; omega
  · have := i.isLt
    simp only [ta_ws, Sum.elim_inl, Sum.elim_inr]; omega
  · have := i.isLt
    simp only [ta_ws, Sum.elim_inl, Sum.elim_inr]; omega
  · have := i.isLt
    simp only [ta_ws, Sum.elim_inr]; omega

theorem ta_size (k r m b : ℕ) :
    (k + 2) * coreS k r m b + (32 * (k * k) + 122 * k + 75) + 1 ≤
      2 ^ 48 * (k + r + m + 5) ^ 20 * 2 ^ b := by
  unfold coreS
  have hX : k + 5 ≤ k + r + m + 5 := by omega
  generalize k + r + m + 5 = X at hX ⊢
  have e : 2 ^ 48 * X ^ 20 * 2 ^ b = 2 * (X * (2 ^ 47 * X ^ 19 * 2 ^ b)) := by ring
  rw [e]
  have hcs : 32 * (X * X) ≤ 2 ^ 47 * X ^ 19 * 2 ^ b := by
    have h1 : 1 ≤ X ^ 17 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by omega)
    have h3 : X ^ 19 = X * X * X ^ 17 := by ring
    rw [h3]
    calc 32 * (X * X) ≤ 2 ^ 47 * (X * X * 1) * 1 := by
          rw [Nat.mul_one, Nat.mul_one]
          exact Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 2 ^ 47 * (X * X * X ^ 17) * 2 ^ b :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)) h2
  generalize 2 ^ 47 * X ^ 19 * 2 ^ b = cs at hcs ⊢
  have hA : (k + 5) * (k + 5) ≤ X * X := Nat.mul_le_mul hX hX
  have h3 : (k + 5) * cs ≤ X * cs := Nat.mul_le_mul_right cs hX
  generalize X * cs = Xc at h3 ⊢
  generalize X * X = A at hA hcs
  have e2 : (k + 5) * (k + 5) = k * k + 10 * k + 25 := by ring
  have e3 : (k + 5) * cs = (k + 2) * cs + 3 * cs := by ring
  generalize (k + 2) * cs = kc at e3 ⊢
  generalize (k + 5) * cs = k5 at e3 h3
  generalize k * k = kk at e2 ⊢
  omega

theorem ta_layout (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 : List Bool) (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 : ℕ)
    (h0 : l0.length = n0)
    (h1 : l1.length = n1)
    (h2 : l2.length = n2)
    (h3 : l3.length = n3)
    (h4 : l4.length = n4)
    (h5 : l5.length = n5)
    (h6 : l6.length = n6)
    (h7 : l7.length = n7)
    (h8 : l8.length = n8)
    (h9 : l9.length = n9) :
    (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).length = n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 ∧
    (∀ i, i < n0 → (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).getD (i) false = l0.getD i false) ∧
    (∀ i, i < n1 → (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).getD (n0 + i) false = l1.getD i false) ∧
    (∀ i, i < n2 → (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).getD (n0 + n1 + i) false = l2.getD i false) ∧
    (∀ i, i < n3 → (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).getD (n0 + n1 + n2 + i) false = l3.getD i false) ∧
    (∀ i, i < n4 → (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).getD (n0 + n1 + n2 + n3 + i) false = l4.getD i false) ∧
    (∀ i, i < n5 → (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).getD (n0 + n1 + n2 + n3 + n4 + i) false = l5.getD i false) ∧
    (∀ i, i < n6 → (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).getD (n0 + n1 + n2 + n3 + n4 + n5 + i) false = l6.getD i false) ∧
    (∀ i, i < n7 → (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).getD (n0 + n1 + n2 + n3 + n4 + n5 + n6 + i) false = l7.getD i false) ∧
    (∀ i, i < n8 → (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).getD (n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + i) false = l8.getD i false) ∧
    (∀ i, i < n9 → (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7 ++ l8 ++ l9).getD (n0 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + i) false = l9.getD i false) := by
  subst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨by simp only [List.length_append], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
  · intro i hi
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    exact fi_getD_right _ _ _ _ _ (by first | rfl | simp only [List.length_append])
  · intro i hi
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    exact fi_getD_right _ _ _ _ _ (by first | rfl | simp only [List.length_append])
  · intro i hi
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    exact fi_getD_right _ _ _ _ _ (by first | rfl | simp only [List.length_append])
  · intro i hi
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    exact fi_getD_right _ _ _ _ _ (by first | rfl | simp only [List.length_append])
  · intro i hi
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    exact fi_getD_right _ _ _ _ _ (by first | rfl | simp only [List.length_append])
  · intro i hi
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    exact fi_getD_right _ _ _ _ _ (by first | rfl | simp only [List.length_append])
  · intro i hi
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    exact fi_getD_right _ _ _ _ _ (by first | rfl | simp only [List.length_append])
  · intro i hi
    rw [fi_getD_left _ _ _ _ (by first | omega | (simp only [List.length_append]; omega))]
    exact fi_getD_right _ _ _ _ _ (by first | rfl | simp only [List.length_append])
  · intro i hi
    exact fi_getD_right _ _ _ _ _ (by first | rfl | simp only [List.length_append])

theorem assembled (k r m b : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (hb : b ≤ k + m) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack
        (2*k+2*r*k+2*k*m+k*k+m+2*(k+1)) C ∧
      C.size ≤ 2^48*(k+r+m+5)^20*2^b ∧
      ∀ (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (A B : Fin k → Fin (2^m))
        (ord : Fin k → Fin k) (y : Fin (2^m)) (t : Fin (2^(k+1))) (j : Fin (k+1)),
        C.eval (inputN k r m nr nc cr cc A B ord y t j) =
          @decide (passP k r m b A B ord ∧ ∃ w : Fin (2^k),
            reportN k r m nr nc cr cc A B w.val = y.val ∧
            Nat.card {z : Fin (2^k) // z < w ∧ reportN k r m nr nc cr cc A B z.val = y.val}
              = t.val ∧
            (j.val = 0 ∨ w.val.testBit (j.val-1) = true)) (Classical.propDecidable _) := by
  obtain ⟨F, hC, hSpec⟩ := core k r m b hk hr hb
  have hc := ta_cb_top F hC
  have hn : 2*k+2*r*k+2*k*m+k*k+m+2*(k+1) =
      k + k + r * k + r * k + k * m + k * m + k * k + m + (k + 1) + (k + 1) := by ring
  rw [hn]
  obtain ⟨gs, outs, hfan, hrb, hsize, hout, hsem⟩ :=
    Cmp.extract hc (k + k + r * k + r * k + k * m + k * m + k * k + m + (k + 1) + (k + 1))
      (ta_ws k r m) (fun x => Nat.lt_succ_of_lt (ta_ws_lt k r m x))
  refine ⟨⟨gs, outs ()⟩, hfan, hrb _, le_trans hsize (ta_size k r m b), ?_⟩
  intro nr nc cr cc A B ord y t j
  have fcr := fi_fin false r k (fun i => bitsN k (cr i).val) (fun _ => ta_bits_len _ _)
  have fcc := fi_fin false r k (fun i => bitsN k (cc i).val) (fun _ => ta_bits_len _ _)
  have fA := fi_fin false k m (fun i => bitsN m (A i).val) (fun _ => ta_bits_len _ _)
  have fB := fi_fin false k m (fun i => bitsN m (B i).val) (fun _ => ta_bits_len _ _)
  have fO := fi_fin false k k (fun i => bitsN k (ord i).val) (fun _ => ta_bits_len _ _)
  have hord : (List.ofFn ord).flatMap (fun p => bitsN k p.val) =
      (List.finRange k).flatMap (fun i => bitsN k (ord i).val) := by
    rw [List.ofFn_eq_map, List.flatMap_map]
  obtain ⟨hlen, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := ta_layout
    (bitsN k nr.val) (bitsN k nc.val) (schedN k r cr) (schedN k r cc) (packN k m A)
    (packN k m B) ((List.finRange k).flatMap (fun i => bitsN k (ord i).val)) (bitsN m y.val)
    (bitsN (k+1) t.val) (bitsN (k+1) j.val) k k (r * k) (r * k) (k * m) (k * m) (k * k) m
    (k + 1) (k + 1) (ta_bits_len _ _) (ta_bits_len _ _) fcr.1 fcc.1 fA.1 fB.1 fO.1
    (ta_bits_len _ _) (ta_bits_len _ _) (ta_bits_len _ _)
  have hin : inputN k r m nr nc cr cc A B ord y t j =
      bitsN k nr.val ++ bitsN k nc.val ++ schedN k r cr ++ schedN k r cc ++ packN k m A ++
        packN k m B ++ (List.finRange k).flatMap (fun i => bitsN k (ord i).val) ++
        bitsN m y.val ++ bitsN (k+1) t.val ++ bitsN (k+1) j.val := by
    unfold inputN
    rw [hord]
  rw [hin]
  have e := hsem (outs ()) _ hlen ()
  show (PEqualNP.CircuitLowerBounds.Circuit.wires _ _).getD (outs ()) false = _
  rw [e]
  have hu : (fun x : ta_TI k r m =>
      ((bitsN k nr.val ++ bitsN k nc.val ++ schedN k r cr ++ schedN k r cc ++ packN k m A ++
        packN k m B ++ (List.finRange k).flatMap (fun i => bitsN k (ord i).val) ++
        bitsN m y.val ++ bitsN (k+1) t.val ++ bitsN (k+1) j.val) ++ [false]).getD
        (ta_ws k r m x) false) =
      Sum.elim (encD nr nc cr cc A B ord y)
        (Sum.elim (fun i => t.val.testBit i.val) (fun i => j.val.testBit i.val)) := by
    funext x
    rw [fi_getD_left _ _ _ _ (by rw [hlen]; exact ta_ws_lt k r m x)]
    rcases x with ((i | i) | ((p | p) | ((p | p) | (p | i)))) | (i | i)
    · simp only [ta_ws, Sum.elim_inl, encD]
      rw [g0 _ i.isLt, ta_bits_getD _ _ _ i.isLt]
    · simp only [ta_ws, Sum.elim_inl, Sum.elim_inr, encD]
      rw [g1 _ i.isLt, ta_bits_getD _ _ _ i.isLt]
    · simp only [ta_ws, Sum.elim_inl, Sum.elim_inr, encD]
      rw [g2 _ (fin_idx_lt p.1.val r p.2.val k p.1.isLt p.2.isLt)]
      unfold schedN
      rw [fcr.2 p.1 p.2.val p.2.isLt, ta_bits_getD _ _ _ p.2.isLt]
    · simp only [ta_ws, Sum.elim_inl, Sum.elim_inr, encD]
      rw [g3 _ (fin_idx_lt p.1.val r p.2.val k p.1.isLt p.2.isLt)]
      unfold schedN
      rw [fcc.2 p.1 p.2.val p.2.isLt, ta_bits_getD _ _ _ p.2.isLt]
    · simp only [ta_ws, Sum.elim_inl, Sum.elim_inr, encD]
      rw [g4 _ (fin_idx_lt p.1.val k p.2.val m p.1.isLt p.2.isLt)]
      unfold packN
      rw [fA.2 p.1 p.2.val p.2.isLt, ta_bits_getD _ _ _ p.2.isLt]
    · simp only [ta_ws, Sum.elim_inl, Sum.elim_inr, encD]
      rw [g5 _ (fin_idx_lt p.1.val k p.2.val m p.1.isLt p.2.isLt)]
      unfold packN
      rw [fB.2 p.1 p.2.val p.2.isLt, ta_bits_getD _ _ _ p.2.isLt]
    · simp only [ta_ws, Sum.elim_inl, Sum.elim_inr, encD]
      rw [g6 _ (fin_idx_lt p.1.val k p.2.val k p.1.isLt p.2.isLt),
        fO.2 p.1 p.2.val p.2.isLt, ta_bits_getD _ _ _ p.2.isLt]
    · simp only [ta_ws, Sum.elim_inl, Sum.elim_inr, encD]
      rw [g7 _ i.isLt, ta_bits_getD _ _ _ i.isLt]
    · simp only [ta_ws, Sum.elim_inl, Sum.elim_inr]
      rw [g8 _ i.isLt, ta_bits_getD _ _ _ i.isLt]
    · simp only [ta_ws, Sum.elim_inr]
      rw [g9 _ i.isLt, ta_bits_getD _ _ _ i.isLt]
  rw [hu]
  apply Bool.eq_iff_iff.mpr
  exact Iff.trans (ta_top_sem F hSpec nr nc cr cc A B ord y t j)
    (@decide_eq_true_iff _ (Classical.propDecidable _)).symm

end PEqualNP.Outside.L_meta_33648

theorem PEqualNP.Outside.L_meta_33648 : (∀ (k r m b : Nat), 0 < k → 4 ≤ r → b ≤ k+m →
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let V := Fin m → ZMod 2
  let W := Fin (2^k)
  let Y := Fin (2^m)
  let vec := fun (w : Nat) (i : Fin m) => if w.testBit i.val then (1 : ZMod 2) else 0
  let rot := fun (h w : Nat) =>
    ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2^k
  let step := fun (w : Nat) =>
    (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
      (!(w.testBit ((i+1)%k)) && w.testBit ((i+2)%k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w name : Nat) (c : Fin r → Fin (2^k)) =>
    let g := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot g x ^^^ rot (k-g) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
      (rot (if col then 3 else 1) w ^^^ name)
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let bits := fun (a x : Nat) => (List.range a).map (fun i => x.testBit i)
  let sched := fun (c : Fin r → Fin (2^k)) =>
    (List.finRange r).flatMap (fun j => bits k (c j).val)
  let pack := fun (A : Fin k → Y) => (List.finRange k).flatMap (fun p => bits m (A p).val)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack
      (2*k+2*r*k+2*k*m+k*k+m+2*(k+1)) C ∧
    C.size ≤ 2^48*(k+r+m+5)^20*2^b ∧
    ∀ (nr nc : W) (cr cc : Fin r → W) (A B : Fin k → Y) (ord : Fin k → Fin k)
      (y : Y) (t : Fin (2^(k+1))) (j : Fin (k+1)),
      let sites := List.ofFn ord
      let span := fun (ps : List (Fin k)) => Submodule.span (ZMod 2)
        (↑((ps.flatMap (fun p => [vec (A p).val, vec (B p).val])).toFinset) : Set V)
      let arc := fun (p : Fin k) (col : Bool) =>
        (Finset.univ : Finset (Fin k)).filter (fun z =>
          (if col then (B p).val else (A p).val) ≠ 0 ∧
          ∃ h : Fin (reach col + 1), (p.val+h.val)%k = z.val)
      let scope := fun p => arc p false ∪ arc p true
      let pool := fun (ps : List (Fin k)) => ps.toFinset.biUnion scope
      let pass := Function.Bijective ord ∧ ∀ i : Fin k,
        let L := sites.take i.val
        let R := sites.drop i.val
        ((pool L ∩ pool R) ∪ scope (ord i)).card +
          Module.finrank (ZMod 2) (span L ⊓ span R : Submodule (ZMod 2) V) ≤ b
      let report := fun (w : W) => (List.finRange k).foldl (fun z p =>
        let bit := fun col : Bool => (state col w.val (if col then nc.val else nr.val)
          (if col then cc else cr)).testBit ((p.val+delay col)%k)
        (z ^^^ (if bit false then (A p).val else 0)) ^^^
          (if bit true then (B p).val else 0)) (0 : Nat)
      let hit := fun w => report w = y.val
      let orderBits := sites.flatMap (fun p => bits k p.val)
      C.eval (bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ pack A ++ pack B ++
        orderBits ++ bits m y.val ++ bits (k+1) t.val ++ bits (k+1) j.val) =
        decide (pass ∧ ∃ w : W, hit w ∧
          Nat.card {z : W // z < w ∧ hit z} = t.val ∧
          (j.val = 0 ∨ w.val.testBit (j.val-1) = true))) := by
  intro k r m b hk hr hb
  exact PEqualNP.Outside.L_meta_33648.assembled k r m b hk hr hb
