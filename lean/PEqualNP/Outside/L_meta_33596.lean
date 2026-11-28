import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_33596_aux
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

def bv {W : ℕ} (w : Fin W → Bool) : BitVec W :=
  BitVec.ofNat W ((List.range W).foldl
    (fun acc i => acc ||| ((if h : i < W then w ⟨i, h⟩ else false).toNat <<< i)) 0)

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

theorem Cmp.thn {ι κ μ : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    {G : (ι ⊕ κ → Bool) → μ → Bool} (h1 : Cmp ι κ S F) (h2 : Cmp (ι ⊕ κ) μ S' G) :
    Cmp ι μ (S + S') (fun v => G (Sum.elim v (F v))) :=
  Cmp.comp (Cmp.keep h1) h2

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

theorem Cb.beq {ι : Type} {S S' : ℕ} {φ ψ : (ι → Bool) → Bool} (h : Cb ι S φ) (h' : Cb ι S' ψ) :
    Cb ι (S + S' + 5) (fun v => φ v == ψ v) := by
  refine Cb.congr (Cb.not (Cb.xor h h')) ?_
  intro v
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

theorem testBit_foldl_or (p : ℕ → Bool) (xs : List ℕ) (acc i : ℕ) :
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

theorem getLsbD_bv {W : ℕ} (w : Fin W → Bool) (i : Fin W) : (bv w).getLsbD i.val = w i := by
  unfold bv
  rw [BitVec.getLsbD_ofNat, testBit_foldl_or]
  simp [i.isLt]

theorem bv_getLsbD {W : ℕ} (x : BitVec W) : bv (fun i : Fin W => x.getLsbD i.val) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact getLsbD_bv (fun j : Fin W => x.getLsbD j.val) ⟨i, hi⟩

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

theorem shr_bit {W : ℕ} (c : Bool) (x : BitVec W) (t : Fin W) :
    (if c then x >>> 1 else x).getLsbD t.val =
      (if c then (if t.val + 1 < W then x.getLsbD (t.val + 1) else false) else x.getLsbD t.val) := by
  cases c
  · rfl
  · simp only [ite_true, BitVec.getLsbD_ushiftRight]
    by_cases ht : t.val + 1 < W
    · simp [ht, Nat.add_comm]
    · simp only [ht, ↓reduceIte]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt
        (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))

theorem Cw.shr {ι : Type} {W : ℕ} (ℓ : ι) {S0 : ℕ} {φ0 : (ι → Bool) → BitVec W}
    (h0 : Cw ι W S0 φ0) :
    Cw ι W (S0 + W * 5) (fun v => if v ℓ then φ0 v >>> 1 else φ0 v) := by
  have hb : ∀ t : Fin W, Cb (ι ⊕ Fin W) 5
      (fun w => if w (Sum.inl ℓ) then (if h : t.val + 1 < W then w (Sum.inr ⟨t.val + 1, h⟩) else false)
        else w (Sum.inr t)) := by
    intro t
    by_cases ht : t.val + 1 < W
    · exact Cb.mono (Cb.congr (Cb.mux (Cb.var (Sum.inl ℓ))
        (Cb.var (Sum.inr ⟨t.val + 1, ht⟩)) (Cb.var (Sum.inr t)))
        (fun w => by simp [ht])) (by norm_num)
    · exact Cb.mono (Cb.congr (Cb.mux (Cb.var (Sum.inl ℓ)) (Cb.const false) (Cb.var (Sum.inr t)))
        (fun w => by simp [ht])) (by norm_num)
  have h := Cmp.thn h0 (Cmp.ofBits hb)
  simp only [Fintype.card_fin] at h
  refine Cmp.congr h ?_
  intro v t
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [shr_bit]
  by_cases ht : t.val + 1 < W
  · simp [ht]
  · simp [ht]

theorem Cw.shrChain {ι : Type} {W : ℕ} :
    ∀ (L : List ι) {S0 : ℕ} {φ0 : (ι → Bool) → BitVec W}, Cw ι W S0 φ0 →
      Cw ι W (S0 + L.length * (W * 5))
        (fun v => L.foldl (fun x ℓ => if v ℓ then x >>> 1 else x) (φ0 v)) := by
  intro L
  induction L with
  | nil => intro S0 φ0 h0; simpa using h0
  | cons ℓ L ih =>
    intro S0 φ0 h0
    have := ih (Cw.shr ℓ h0)
    refine Cw.mono (Cw.congr this (fun v => rfl)) ?_
    simp only [List.length_cons]
    ring_nf
    omega

theorem Cw.eqBV {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W}
    (h : Cw ι W S φ) (h' : Cw ι W S' ψ) :
    Cb ι (S + S' + (W * 6 + 1)) (fun v => decide (φ v = ψ v)) := by
  have hb := Cb.bigAnd (I := Fin W) (fun i => Cb.beq (Cb.var (ι := Fin W ⊕ Fin W) (Sum.inl i))
    (Cb.var (Sum.inr i)))
  have hc := Cb.comp (Cmp.pair h h') hb
  rw [Fintype.card_fin] at hc
  refine Cb.mono (Cb.congr hc ?_) (by omega)
  intro v
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Sum.elim_inl, Sum.elim_inr, beq_iff_eq]
  constructor
  · intro heq
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact heq ⟨i, hi⟩
  · intro heq i
    rw [heq]

def minBV {W : ℕ} (x y : BitVec W) : BitVec W :=
  if (x - y).getLsbD (W - 1) then x else y

theorem Cw.min {ι : Type} {W S S' : ℕ} (hW : 0 < W) {φ ψ : (ι → Bool) → BitVec W}
    (h : Cw ι W S φ) (h' : Cw ι W S' ψ) :
    Cw ι W (S + S' + 30 * (W + 1)) (fun v => minBV (φ v) (ψ v)) := by
  have hsub : Cw (Fin W ⊕ Fin W) W (20 * (W + 1))
      (fun u => bv (fun i => u (Sum.inl i)) - bv (fun i => u (Sum.inr i))) :=
    Cw.mono (Cw.sub (Cw.var Sum.inl) (Cw.var Sum.inr)) (by omega)
  have hlt : Cb (Fin W ⊕ Fin W) (20 * (W + 1))
      (fun u => (bv (fun i => u (Sum.inl i)) - bv (fun i => u (Sum.inr i))).getLsbD (W - 1)) :=
    Cb.comp hsub (Cb.var (ι := Fin W) ⟨W - 1, by omega⟩)
  have hmux := Cw.mux hlt (Cw.var (ι := Fin W ⊕ Fin W) Sum.inl) (Cw.var Sum.inr)
  have htot := Cw.comp (Cmp.pair h h') hmux
  refine Cw.mono (Cw.congr htot ?_) (by omega)
  intro v
  simp only [minBV, Sum.elim_inl, Sum.elim_inr, bv_getLsbD]

theorem nat_testBit_top {W a : ℕ} (hW : 1 ≤ W) (ha : a < 2 ^ W) :
    a.testBit (W - 1) = decide (2 ^ (W - 1) ≤ a) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 : 2 ^ W = 2 * 2 ^ (W - 1) := by
    have : W = (W - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_comm]
  have hpos : 0 < 2 ^ (W - 1) := Nat.two_pow_pos _
  by_cases hge : 2 ^ (W - 1) ≤ a
  · have hd : a / 2 ^ (W - 1) = 1 := by
      apply Nat.div_eq_of_lt_le
      · simpa using hge
      · omega
    simp [hge, hd]
  · have hd : a / 2 ^ (W - 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [hge, hd]

theorem ofInt_msb_iff {W : ℕ} (hW : 1 ≤ W) (z : ℤ)
    (hlo : -(2 : ℤ) ^ (W - 1) ≤ z) (hhi : z < (2 : ℤ) ^ (W - 1)) :
    (BitVec.ofInt W z).getLsbD (W - 1) = decide (z < 0) := by
  have h2 : (2 : ℤ) ^ W = 2 * (2 : ℤ) ^ (W - 1) := by
    have : W = (W - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_comm]
  have hpos : (0 : ℤ) < (2 : ℤ) ^ (W - 1) := by positivity
  have hltW : W - 1 < W := by omega
  rw [BitVec.getLsbD_eq_getElem hltW, BitVec.getElem_eq_testBit_toNat, nat_testBit_top hW (BitVec.isLt _)]
  rw [BitVec.toNat_ofInt]
  have hcast : ((2 ^ W : ℕ) : ℤ) = (2 : ℤ) ^ W := by push_cast; rfl
  rw [hcast]
  by_cases hz : z < 0
  · have hm : z % (2 : ℤ) ^ W = z + (2 : ℤ) ^ W := by
      have hq := Int.emod_add_mul_ediv z ((2 : ℤ) ^ W)
      have h1 := Int.emod_nonneg z (by positivity : (2 : ℤ) ^ W ≠ 0)
      have h2' := Int.emod_lt_of_pos z (by positivity : (0 : ℤ) < (2 : ℤ) ^ W)
      have hd : z / (2 : ℤ) ^ W = -1 := by nlinarith
      rw [hd] at hq
      omega
    rw [hm]
    have hge : 2 ^ (W - 1) ≤ (z + (2 : ℤ) ^ W).toNat := by
      have : ((2 ^ (W - 1) : ℕ) : ℤ) ≤ z + (2 : ℤ) ^ W := by push_cast; omega
      omega
    simp [hz, hge]
  · have hm : z % (2 : ℤ) ^ W = z := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hm]
    have hlt : ¬ (2 ^ (W - 1) ≤ z.toNat) := by
      have : z < ((2 ^ (W - 1) : ℕ) : ℤ) := by push_cast; omega
      omega
    simp [hz, hlt]

theorem ofInt_sub_eq {W : ℕ} (x y : ℤ) :
    BitVec.ofInt W x - BitVec.ofInt W y = BitVec.ofInt W (x - y) := by
  rw [BitVec.sub_eq_add_neg, sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add]

theorem ofInt_minBV {W : ℕ} (hW : 2 ≤ W) (x y : ℤ)
    (hxlo : -(2 : ℤ) ^ (W - 2) ≤ x) (hxhi : x < (2 : ℤ) ^ (W - 2))
    (hylo : -(2 : ℤ) ^ (W - 2) ≤ y) (hyhi : y < (2 : ℤ) ^ (W - 2)) :
    minBV (BitVec.ofInt W x) (BitVec.ofInt W y) = BitVec.ofInt W (min x y) := by
  have h2 : (2 : ℤ) ^ (W - 1) = 2 * (2 : ℤ) ^ (W - 2) := by
    have : W - 1 = (W - 2) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_comm]
  unfold minBV
  rw [ofInt_sub_eq, ofInt_msb_iff (by omega) (x - y) (by omega) (by omega)]
  by_cases h : x < y
  · have h1 : x - y < 0 := by omega
    simp [h1, min_eq_left (le_of_lt h)]
  · have h1 : ¬ (x - y < 0) := by omega
    simp [h1, min_eq_right (le_of_not_gt h)]

theorem ofInt_inj {W : ℕ} (hW : 1 ≤ W) (x y : ℤ)
    (hxlo : -(2 : ℤ) ^ (W - 1) ≤ x) (hxhi : x < (2 : ℤ) ^ (W - 1))
    (hylo : -(2 : ℤ) ^ (W - 1) ≤ y) (hyhi : y < (2 : ℤ) ^ (W - 1)) :
    BitVec.ofInt W x = BitVec.ofInt W y ↔ x = y := by
  have h2 : (2 : ℤ) ^ W = 2 * (2 : ℤ) ^ (W - 1) := by
    have : W = (W - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_comm]
  have hcast : ((2 ^ W : ℕ) : ℤ) = (2 : ℤ) ^ W := by push_cast; rfl
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofInt, hcast] at ht
    have hxnn : 0 ≤ x % (2 : ℤ) ^ W := Int.emod_nonneg _ (by positivity)
    have hynn : 0 ≤ y % (2 : ℤ) ^ W := Int.emod_nonneg _ (by positivity)
    have heq : x % (2 : ℤ) ^ W = y % (2 : ℤ) ^ W := by omega
    have hsub : (x - y) % (2 : ℤ) ^ W = 0 := by
      rw [Int.sub_emod, heq, sub_self, Int.zero_emod]
    have hdvd : (2 : ℤ) ^ W ∣ (x - y) := Int.dvd_of_emod_eq_zero hsub
    obtain ⟨q, hq⟩ := hdvd
    have hq0 : q = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have : q ≤ -1 := by omega
        nlinarith
      · have : 1 ≤ q := by omega
        nlinarith
    rw [hq0, mul_zero] at hq
    omega
  · intro h; rw [h]

def toZ (b : Bool) : ZMod 2 := if b then 1 else 0
def ofZ (z : ZMod 2) : Bool := decide (z = 1)
def sgnZ (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

theorem toZ_ofZ (z : ZMod 2) : toZ (ofZ z) = z := by fin_cases z <;> rfl
theorem ofZ_toZ (b : Bool) : ofZ (toZ b) = b := by cases b <;> rfl
theorem toZ_xor (a b : Bool) : toZ (xor a b) = toZ a + toZ b := by cases a <;> cases b <;> rfl
theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by cases a <;> cases b <;> rfl
theorem toZ_not (a : Bool) : toZ (!a) = 1 + toZ a := by cases a <;> rfl
theorem toZ_false : toZ false = 0 := rfl
theorem toZ_true : toZ true = 1 := rfl
theorem toZ_inj {a b : Bool} : toZ a = toZ b ↔ a = b := by cases a <;> cases b <;> decide
theorem toZ_eq_zero {a : Bool} : toZ a = 0 ↔ a = false := by cases a <;> decide
theorem toZ_eq_one {a : Bool} : toZ a = 1 ↔ a = true := by cases a <;> decide
theorem toZ_decide (p : Prop) [Decidable p] : toZ (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h, toZ]
theorem zsq (x : ZMod 2) : x * x = x := by fin_cases x <;> rfl
theorem z2 (x : ZMod 2) : x + x = 0 := by fin_cases x <;> rfl
theorem z01 (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl
theorem zsub (x y : ZMod 2) : x - y = x + y := by fin_cases x <;> fin_cases y <;> rfl
theorem ofZ_add (a b : ZMod 2) : ofZ (a + b) = xor (ofZ a) (ofZ b) := by
  fin_cases a <;> fin_cases b <;> rfl
theorem ofZ_mul (a b : ZMod 2) : ofZ (a * b) = (ofZ a && ofZ b) := by
  fin_cases a <;> fin_cases b <;> rfl
theorem sgnZ_add (a b : ZMod 2) : sgnZ (a + b) = sgnZ a * sgnZ b := by
  fin_cases a <;> fin_cases b <;> rfl
theorem sgnZ_zero : sgnZ 0 = 1 := rfl
theorem sgnZ_one : sgnZ 1 = -1 := rfl

theorem sgnZ_sum {ι : Type} (s : Finset ι) (x : ι → ZMod 2) :
    sgnZ (∑ i ∈ s, x i) = ∏ i ∈ s, sgnZ (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgnZ_add, ih]

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

theorem foldl_xor_toZ {α : Type} (L : List α) (g : α → Bool) (t0 : Bool) :
    toZ (L.foldl (fun t i => xor t (g i)) t0) = toZ t0 + (L.map (fun i => toZ (g i))).sum := by
  induction L generalizing t0 with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, toZ_xor]
    ring

def mat {r c : ℕ} (v : Fin r × Fin c → Bool) : Matrix (Fin r) (Fin c) (ZMod 2) :=
  fun i j => if v (i, j) then 1 else 0

theorem mat_eq_toZ {r c : ℕ} (v : Fin r × Fin c → Bool) (i : Fin r) (j : Fin c) :
    mat v i j = toZ (v (i, j)) := rfl

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

def schedGJ (D : ℕ) : List (Bool × Fin D × Fin D) :=
  (List.finRange D).flatMap fun p =>
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (false, p, i)) ++
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (true, p, i))

def gj (D : ℕ) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  (schedGJ D).foldl (fun M e => gjStep e M) M

theorem fc_rowAdd_false {D : ℕ} (t s : Fin D) (M : Fin D × Fin D → Bool) :
    rowAdd t s false M = M := by
  funext p; simp [rowAdd]

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

theorem schedGJ_ne {D : ℕ} (e : Bool × Fin D × Fin D) (he : e ∈ schedGJ D) : e.2.1 ≠ e.2.2 := by
  unfold schedGJ at he
  rw [List.mem_flatMap] at he
  obtain ⟨p, _, hp⟩ := he
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · rw [List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [List.mem_filter] at hi
    have := hi.2; simp at this; exact fun h => this h.symm
  · rw [List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [List.mem_filter] at hi
    have := hi.2; simp at this; exact fun h => this h.symm

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
    · rw [List.foldl_cons, mul_assoc, ← h2]; exact hs

theorem gj_equiv {D : ℕ} (M : Fin D × Fin D → Bool) :
    ∃ U U' : Matrix (Fin D) (Fin D) (ZMod 2),
      mat (gj D M) = U * mat M ∧ mat M = U' * mat (gj D M) :=
  fc_equiv_list (schedGJ D) (fun e he => schedGJ_ne e he) M

def fc_Inv {D : ℕ} (k : ℕ) (M : Fin D × Fin D → Bool) : Prop :=
  (∀ q : Fin D, q.val < k → M (q, q) = true → ∀ i, M (i, q) = decide (i = q)) ∧
  (∀ i q : Fin D, q.val < k → (k ≤ i.val ∨ M (i, i) = false) → M (i, q) = false) ∧
  (∀ p q : Fin D, q < p → p.val < k → M (p, p) = true → M (p, q) = false)

theorem fc_Inv_congr {D : ℕ} (k : ℕ) (M M' : Fin D × Fin D → Bool)
    (h : ∀ i q : Fin D, q.val < k → M' (i, q) = M (i, q)) (hI : fc_Inv k M) : fc_Inv k M' := by
  obtain ⟨ha, hb, hc⟩ := hI
  refine ⟨?_, ?_, ?_⟩
  · intro q hq hqq i; rw [h _ _ hq] at hqq ⊢; exact ha q hq hqq i
  · intro i q hq hfree
    rw [h _ _ hq]; apply hb i q hq
    by_cases hi : i.val < k
    · rcases hfree with hf | hf
      · omega
      · right; rw [← h _ _ hi]; exact hf
    · left; omega
  · intro p q hqp hp hpp
    have hq : q.val < k := by have : q.val < p.val := hqp; omega
    rw [h _ _ hq]; rw [h _ _ hp] at hpp; exact hc p q hqp hp hpp

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
    rw [this]; exact ih

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
    rw [this]; exact ih

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
        intro q hq; apply hI.2.1 i q hq
        rcases hfree with hf | hf
        · left; have : p.val < i.val := hf; omega
        · right; exact hf
      have hM1pp : gjStep (false, p, i) M (p, p) = true := by
        simp [gjStep, gjT, gjS, rowAdd, hc, hip1, hpp]
      rw [fc_A_id p l _ hM1pp]
      refine ⟨?_, ?_⟩
      · apply fc_Inv_congr k M _ _ hI
        intro j q hq
        simp only [gjStep, gjT, gjS, rowAdd, Bool.false_eq_true, if_false, hc]
        split
        · rw [hrow q hq]; simp
        · rfl
      · intro h; rw [hM1pp] at h; exact absurd h (by simp)
    · have hcf : gjCtl (false, p, i) M = false := by simpa using hc
      have hM1 : gjStep (false, p, i) M = M := by
        unfold gjStep; rw [hcf, fc_rowAdd_false]
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
      intro j; simp [gjStep, gjT, gjS, rowAdd, Ne.symm hip]
    have h2 : ∀ i' q : Fin D, q.val < k → gjStep (true, p, i) M (i', q) = M (i', q) := by
      intro i' q hq; simp [gjStep, gjT, gjS, rowAdd, hrow q hq]
    have h3 : gjStep (true, p, i) M (i, p) = false := by
      simp [gjStep, gjT, gjS, rowAdd, gjCtl, hpp]
    have h4 : ∀ i', i' ≠ i → gjStep (true, p, i) M (i', p) = M (i', p) := by
      intro i' hi'; simp [gjStep, gjT, gjS, rowAdd, hi']
    obtain ⟨ia, ib, ic⟩ := ih (fun i' h' => hl i' (List.mem_cons_of_mem _ h'))
      (gjStep (true, p, i) M) (by rw [h1]; exact hpp)
      (fun q hq => by rw [h1]; exact hrow q hq)
    refine ⟨?_, ?_, ?_⟩
    · intro i' q hq; rw [ia i' q hq, h2 i' q hq]
    · intro j; rw [ib j, h1 j]
    · intro i' hi'p h
      apply ic i' hi'p
      by_cases hii : i' = i
      · right; rw [hii]; exact h3
      · rcases h with h | h
        · rcases List.mem_cons.1 h with h | h
          · exact absurd h hii
          · left; exact h
        · right; rw [h4 i' hii]; exact h

def fc_col {D : ℕ} (p : Fin D) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  ((List.finRange D).filter (fun i => i ≠ p)).foldl (fun M i => gjStep (true, p, i) M)
    (((List.finRange D).filter (fun i => i ≠ p)).foldl (fun M i => gjStep (false, p, i) M) M)

theorem fc_gj_eq {D : ℕ} (M : Fin D × Fin D → Bool) :
    gj D M = (List.finRange D).foldl (fun M p => fc_col p M) M := by
  unfold gj schedGJ
  rw [List.foldl_flatMap]
  simp only [List.foldl_append, List.foldl_map, fc_col]

theorem fc_colInv {D : ℕ} (p : Fin D) (M : Fin D × Fin D → Bool) (hI : fc_Inv p.val M) :
    fc_Inv (p.val + 1) (fc_col p M) := by
  have hl : ∀ i ∈ (List.finRange D).filter (fun i => i ≠ p), i ≠ p := by
    intro i hi; rw [List.mem_filter] at hi; simpa using hi.2
  have hmem : ∀ i, i ≠ p → i ∈ (List.finRange D).filter (fun i => i ≠ p) := by
    intro i hi; rw [List.mem_filter]; exact ⟨List.mem_finRange i, by simpa using hi⟩
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
        · subst hiq; simp [hqq]
        · rw [bc i hiq (Or.inl (hmem i hiq))]; simp [hiq]
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h); omega
        rw [ba _ _ hq'] at hqq ⊢; exact ha q hq' hqq i
    · intro i q hq hfree
      have hip : i ≠ p := by
        intro h; subst h
        rcases hfree with hf | hf
        · omega
        · rw [hBpp] at hf; exact absurd hf (by simp)
      by_cases hqp : q = p
      · subst hqp; exact bc i hip (Or.inl (hmem i hip))
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h); omega
        rw [ba _ _ hq']; apply hb i q hq'
        by_cases hi : i.val < p.val
        · right
          rcases hfree with hf | hf
          · omega
          · rw [← ba _ _ hi]; exact hf
        · left; omega
    · intro p' q hqp' hp' hp'p'
      have hq' : q.val < p'.val := hqp'
      by_cases hpe : p' = p
      · subst hpe; rw [bb]; exact hrow q hq'
      · have hp'' : p'.val < p.val := by
          have : p'.val ≠ p.val := fun h => hpe (Fin.ext h); omega
        rw [ba _ _ (by omega)]; rw [ba _ _ hp''] at hp'p'; exact hc p' q hqp' hp'' hp'p'
  · have hppf : MA (p, p) = false := by simpa using hpp
    rw [fc_B_id p _ MA hppf]
    obtain ⟨hMeq, hcol⟩ := hA hppf
    obtain ⟨ha, hb, hc⟩ := hIA
    have hfreecol : ∀ i : Fin D, (p.val + 1 ≤ i.val ∨ MA (i, i) = false) → MA (i, p) = false := by
      intro i hfree
      by_cases hip : i = p
      · rw [hip]; exact hppf
      · rw [hMeq] at hfree ⊢; apply hcol i (hmem i hip)
        rcases hfree with hf | hf
        · left; show p.val < i.val; omega
        · right; exact hf
    refine ⟨?_, ?_, ?_⟩
    · intro q hq hqq i
      by_cases hqp : q = p
      · subst hqp; rw [hppf] at hqq; exact absurd hqq (by simp)
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h); omega
        exact ha q hq' hqq i
    · intro i q hq hfree
      by_cases hqp : q = p
      · subst hqp; exact hfreecol i hfree
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h); omega
        apply hb i q hq'
        rcases hfree with hf | hf
        · left; omega
        · right; exact hf
    · intro p' q hqp' hp' hp'p'
      have hpe : p' ≠ p := by
        intro h; subst h; rw [hppf] at hp'p'; exact absurd hp'p' (by simp)
      have hp'' : p'.val < p.val := by
        have : p'.val ≠ p.val := fun h => hpe (Fin.ext h); omega
      exact hc p' q hqp' hp'' hp'p'

theorem fc_fold {D : ℕ} (l : List (Fin D)) :
    ∀ (k : ℕ), (∀ i (h : i < l.length), (l[i]).val = k + i) →
    ∀ M : Fin D × Fin D → Bool, fc_Inv k M →
      fc_Inv (k + l.length) (l.foldl (fun M p => fc_col p M) M) := by
  induction l with
  | nil => intro k _ M hI; exact hI
  | cons p l ih =>
    intro k hidx M hI
    have hp : p.val = k := by have := hidx 0 (by simp); simpa using this
    rw [List.foldl_cons]
    have h1 : fc_Inv (k + 1) (fc_col p M) := by
      have := fc_colInv p M (hp ▸ hI); rw [hp] at this; exact this
    have h2 := ih (k + 1) (fun i h => by
      have := hidx (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this; omega) (fc_col p M) h1
    have e : k + (p :: l).length = k + 1 + l.length := by simp; omega
    rw [e]; exact h2

theorem fc_gjInv {D : ℕ} (M : Fin D × Fin D → Bool) : fc_Inv D (gj D M) := by
  rw [fc_gj_eq]
  have h0 : fc_Inv 0 M := ⟨fun q hq => by omega, fun i q hq => by omega, fun p q _ hp => by omega⟩
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

def GJF {D : ℕ} (R : Fin D × Fin D → Bool) : Prop :=
  (∀ p, R (p, p) = true → ∀ i, R (i, p) = decide (i = p)) ∧
  (∀ q, R (q, q) = false → ∀ j, R (q, j) = false)

theorem gj_GJF {D : ℕ} (M : Fin D × Fin D → Bool) : GJF (gj D M) :=
  ⟨gj_pivcol M, gj_zerorow M⟩

theorem GJF_term {D : ℕ} {R : Fin D × Fin D → Bool} (hR : GJF R) (i j s : Fin D) :
    toZ (R (i, j)) * toZ (R (j, s)) = (if i = j then toZ (R (j, s)) else 0) := by
  by_cases hj : R (j, j) = true
  · rw [hR.1 j hj i]
    by_cases hij : i = j <;> simp [hij, toZ]
  · rw [hR.2 j (by simpa using hj) s]
    by_cases hij : i = j <;> simp [hij, toZ]

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
  · intro h; rw [h2, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · intro h; rw [h1, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

theorem gj_col_zero {D : ℕ} (M : Fin D × Fin D → Bool) (c : Fin D)
    (hc : ∀ r, M (r, c) = false) (r : Fin D) : gj D M (r, c) = false := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv M
  have := congrFun (congrFun h1 r) c
  rw [Matrix.mul_apply] at this
  simp only [mat_eq_toZ, hc, toZ_false, mul_zero, Finset.sum_const_zero] at this
  exact toZ_eq_zero.1 this

theorem fd_ctl {D : ℕ} (e : Bool × Fin D × Fin D) :
    Cb (Fin D × Fin D) 6 (fun M => gjCtl e M) := by
  rcases e with ⟨k, p, i⟩
  cases k
  · have h := Cb.and (Cb.and (Cb.or (Cb.const (ι := Fin D × Fin D) (decide (p < i)))
        (Cb.not (Cb.var (i, i)))) (Cb.var (i, p))) (Cb.not (Cb.var (p, p)))
    refine Cb.mono (Cb.congr h ?_) (by norm_num)
    intro v; simp [gjCtl]
  · have h := Cb.and (Cb.var (ι := Fin D × Fin D) (i, p)) (Cb.var (p, p))
    refine Cb.mono (Cb.congr h ?_) (by norm_num)
    intro v; simp [gjCtl]

theorem fd_bit {D : ℕ} (e : Bool × Fin D × Fin D) (p : Fin D × Fin D) :
    Cb (Fin D × Fin D) 11 (fun M => gjStep e M p) := by
  by_cases h : p.1 = gjT e
  · have hh := Cb.xor (Cb.var p) (Cb.and (fd_ctl e) (Cb.var (gjS e, p.2)))
    refine Cb.mono (Cb.congr hh ?_) (by norm_num)
    intro v; simp [gjStep, rowAdd, h]
  · refine Cb.mono (Cb.congr (Cb.var p) ?_) (by norm_num)
    intro v; simp [gjStep, rowAdd, h]

theorem fd_flatMap_len {α β : Type} (c : ℕ) (f : α → List β) (hf : ∀ x, (f x).length ≤ c) :
    ∀ L : List α, (L.flatMap f).length ≤ L.length * c := by
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := hf x; omega

theorem fd_schedGJ_len (D : ℕ) : (schedGJ D).length ≤ 2 * (D * D) := by
  have h := fd_flatMap_len (2 * D) (fun p : Fin D =>
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (false, p, i)) ++
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (true, p, i))) (by
      intro p
      have h1 : ((List.finRange D).filter (fun i => decide (i ≠ p))).length ≤ D := by
        have := List.length_filter_le (fun i => decide (i ≠ p)) (List.finRange D)
        simpa using this
      simp only [List.length_append, List.length_map]; omega) (List.finRange D)
  have h2 : (List.finRange D).length = D := List.length_finRange
  rw [h2] at h
  have h3 : D * (2 * D) = 2 * (D * D) := by ring
  rw [h3] at h
  exact h

def gjCost (D : ℕ) : ℕ := 32 * (D + 1) ^ 4

theorem cmp_gj (D : ℕ) : Cmp (Fin D × Fin D) (Fin D × Fin D) (gjCost D) (gj D) := by
  have h := Cmp.foldl (ι := Fin D × Fin D) (s := Fintype.card (Fin D × Fin D) * 11) (schedGJ D)
    (fun e M => gjStep e M) (fun e _ => Cmp.ofBits (fun p => fd_bit e p))
  refine Cmp.mono h ?_
  have h1 := fd_schedGJ_len D
  have h2 : Fintype.card (Fin D × Fin D) = D * D := by simp
  rw [h2]; unfold gjCost
  have h3 : D ^ 4 ≤ (D + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h4 : 2 * (D * D) * (D * D * 11) = 22 * D ^ 4 := by ring
  calc (schedGJ D).length * (D * D * 11) ≤ 2 * (D * D) * (D * D * 11) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ 32 * (D + 1) ^ 4 := by omega

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
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    rw [this, if_neg hf, Nat.add_zero]

theorem cnt_full {N : ℕ} (fl : Fin N → Bool) :
    cnt fl N = (Finset.univ.filter (fun q : Fin N => fl q = true)).card := by
  unfold cnt
  congr 1; ext q; simp

theorem cnt_lt_rho {N : ℕ} (fl : Fin N → Bool) (j : Fin N) (hj : fl j = true) :
    cnt fl j.val < (Finset.univ.filter (fun q : Fin N => fl q = true)).card := by
  unfold cnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨j, by simp [hj], by simp⟩
  · intro q; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rintro ⟨_, h2⟩; exact h2

theorem cnt_strict {N : ℕ} (fl : Fin N → Bool) (j j' : Fin N) (h : j < j') (hj : fl j = true) :
    cnt fl j.val < cnt fl j'.val := by
  unfold cnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨j, by simp [h, hj, Fin.lt_def.1 h], by simp⟩
  · intro q; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h1, h2⟩; exact ⟨lt_trans h1 (Fin.lt_def.1 h), h2⟩

theorem cnt_inj {N : ℕ} (fl : Fin N → Bool) (j j' : Fin N) (hj : fl j = true)
    (hj' : fl j' = true) (h : cnt fl j.val = cnt fl j'.val) : j = j' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have := cnt_strict fl j j' h1 hj; omega
  · have := cnt_strict fl j' j h1 hj'; omega

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

def splitF {a b : ℕ} {α : Type} (f : Fin a → α) (g : Fin b → α) (i : Fin (a + b)) : α :=
  if h : i.val < a then f ⟨i.val, h⟩ else g ⟨i.val - a, by omega⟩

theorem splitF_castAdd {a b : ℕ} {α : Type} (f : Fin a → α) (g : Fin b → α) (i : Fin a) :
    splitF f g (Fin.castAdd b i) = f i := by
  simp [splitF]

theorem splitF_natAdd {a b : ℕ} {α : Type} (f : Fin a → α) (g : Fin b → α) (i : Fin b) :
    splitF f g (Fin.natAdd a i) = g i := by
  simp [splitF]

theorem forall_add {a b : ℕ} (P : Fin (a + b) → Prop) :
    (∀ r, P r) ↔ (∀ i, P (Fin.castAdd b i)) ∧ (∀ i, P (Fin.natAdd a i)) := by
  constructor
  · intro h; exact ⟨fun i => h _, fun i => h _⟩
  · rintro ⟨h1, h2⟩ r; exact Fin.addCases h1 h2 r

def rotN (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepN (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

def stateN (k r : ℕ) (col : Bool) (w u : ℕ) (c : Fin r → Fin (2 ^ k)) : ℕ :=
  let g := if col then 2 else 1
  (List.finRange r).foldl (fun x j =>
    stepN k (x ^^^ rotN k g x ^^^ rotN k (k - g) x) ^^^
      rotN k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val)
    (rotN k (if col then 3 else 1) w ^^^ u)

def parityN (k mask x : ℕ) : Bool :=
  (List.range k).foldl (fun b i => xor b (mask.testBit i && x.testBit i)) false

def delayN (r : ℕ) (col : Bool) : ℕ := if col then 3 * r + 1 else 2 * r - 2
def reachN (r : ℕ) (col : Bool) : ℕ := if col then 7 * r - 2 else 5 * r - 3

def scopeN (k r : ℕ) (a : Bool × Fin k) : Finset (Fin k) :=
  (Finset.univ : Finset (Fin k)).filter (fun i =>
    ∃ d : Fin (reachN r a.1 + 1), (a.2.val + d.val) % k = i.val)

def colN {k m : ℕ} (r : ℕ) (R B : Fin m → Fin (2 ^ k)) (a : Bool × Fin k) (j : Fin m) : ZMod 2 :=
  if (if a.1 then B j else R j).val.testBit ((a.2.val + delayN r a.1) % k) then 1 else 0

def sensorN {k r : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (a : Bool × Fin k) (w : ℕ) : Bool :=
  (stateN k r a.1 w (if a.1 then v.val else u.val) (if a.1 then cc else cr)).testBit
    ((a.2.val + delayN r a.1) % k)

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

def sn_g (col : Bool) : ℕ := if col then 2 else 1
def sn_s0 (col : Bool) : ℕ := if col then 3 else 1
def sn_sh (col : Bool) (j : ℕ) : ℕ := if col then 3 * (j + 1) + 1 else 2 * j

def sn_body (k g s w x cj : ℕ) : ℕ :=
  stepN k (x ^^^ rotN k g x ^^^ rotN k (k - g) x) ^^^ rotN k s w ^^^ cj

def sn_stN (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2 ^ k)) : ℕ → ℕ
  | 0 => rotN k (sn_s0 col) w ^^^ name
  | t + 1 => if h : t < r then
      sn_body k (sn_g col) (sn_sh col t) w (sn_stN k r col w name c t) (c ⟨t, h⟩).val
    else sn_stN k r col w name c t

theorem sn_fold_take (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2 ^ k)) :
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

theorem sn_state_eq (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2 ^ k)) :
    stateN k r col w name c = sn_stN k r col w name c r := by
  have h1 : stateN k r col w name c = (List.finRange r).foldl (fun x j =>
      sn_body k (sn_g col) (sn_sh col j.val) w x (c j).val) (rotN k (sn_s0 col) w ^^^ name) := rfl
  rw [h1, ← sn_fold_take k r col w name c r le_rfl, List.take_of_length_le (by simp)]

theorem sn_body_lt (k g s w x cj : ℕ) (hc : cj < 2 ^ k) : sn_body k g s w x cj < 2 ^ k :=
  sn_xor_lt (sn_xor_lt (sn_step_lt k _) (sn_rot_lt k _ _)) hc

theorem sn_stN_lt (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2 ^ k))
    (hn : name < 2 ^ k) : ∀ t, sn_stN k r col w name c t < 2 ^ k := by
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

theorem sn_body_bit (k g s w x cj : ℕ) (hx : x < 2 ^ k) (hw : w < 2 ^ k) (i : Fin k) :
    (sn_body k g s w x cj).testBit i.val =
      sn_rnd g s (sn_bits k x) (sn_bits k w) (sn_bits k cj) i := by
  unfold sn_body sn_rnd
  simp only [Nat.testBit_xor, sn_testBit_step, i.isLt, decide_true, Bool.true_and,
    sn_testBit_rot hw i.isLt, sn_testBit_rot hx i.isLt,
    sn_testBit_rot hx (Nat.mod_lt (i.val + 1) i.pos),
    sn_testBit_rot hx (Nat.mod_lt (i.val + 2) i.pos), sn_mix, sn_bits, sn_ri, sn_ad]

theorem sn_st_bit (k r : ℕ) (col : Bool) (w name : ℕ) (c : Fin r → Fin (2 ^ k))
    (hw : w < 2 ^ k) (hn : name < 2 ^ k) : ∀ (t : ℕ) (i : Fin k),
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
    intro v i; simp only [ht, dif_pos]
  have hch := Cmp.chain r (38 * k)
    (fun t (v : Fin k ⊕ (Fin k ⊕ (Fin r × Fin k)) → Bool) =>
      sn_pre col (fun a => v (Sum.inl a)) (fun a => v (Sum.inr (Sum.inl a)))
        (fun p => v (Sum.inr (Sum.inr p))) t)
    (fun t u i => if h : t < r then
        sn_rnd (sn_g col) (sn_sh col t) (fun a => u (Sum.inr a)) (fun a => u (Sum.inl (Sum.inl a)))
          (fun a => u (Sum.inl (Sum.inr (Sum.inr (⟨t, h⟩, a))))) i
        else u (Sum.inr i)) h0 hG
    (by
      intro t ht v; funext i
      simp only [sn_pre, ht, dif_pos, Sum.elim_inl, Sum.elim_inr])
  have hw := Cmp.comp hch (Cmp.wire (fun i : Fin k => ((Fin.last r, i) : Fin (r + 1) × Fin k)))
  refine Cmp.mono (Cmp.congr hw ?_) ?_
  · intro v i; simp
  · have : (r + 1) * (38 * k) + 0 = 38 * (k * (r + 1)) := by ring
    have h2 : 64 * k * (r + 1) = 64 * (k * (r + 1)) := by ring
    omega

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

theorem sens_local (k r : ℕ) (hk : 0 < k) (hr : 4 ≤ r) (u v : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (a : Bool × Fin k) (w w' : ℕ) (hw : w < 2 ^ k) (hw' : w' < 2 ^ k)
    (h : ∀ i ∈ scopeN k r a, w.testBit i.val = w'.testBit i.val) :
    sensorN u v cr cc a w = sensorN u v cr cc a w' := by
  unfold sensorN
  rw [sn_state_eq, sn_state_eq]
  have hsc : ∀ d : ℕ, d ≤ reachN r a.1 →
      w.testBit ((a.2.val + d) % k) = w'.testBit ((a.2.val + d) % k) := by
    intro d hd
    let i : Fin k := ⟨(a.2.val + d) % k, Nat.mod_lt _ hk⟩
    have hi : i ∈ scopeN k r a := by
      simp only [scopeN, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨d, by omega⟩, rfl⟩
    exact h i hi
  cases hc : a.1
  · simp only [hc, Bool.false_eq_true, if_false, delayN]
    have b1 := sn_st_bit k r false w u.val cr hw u.isLt r
      ⟨(a.2.val + (2 * r - 2)) % k, Nat.mod_lt _ hk⟩
    have b2 := sn_st_bit k r false w' u.val cr hw' u.isLt r
      ⟨(a.2.val + (2 * r - 2)) % k, Nat.mod_lt _ hk⟩
    simp only at b1 b2
    rw [b1, b2]
    exact sn_loc_f _ _ _ _ r a.2.val (2 * r - 2) (5 * r - 3) (by omega) (by omega) (by omega)
      (fun d hd q hq => by
        show w.testBit q.val = w'.testBit q.val
        rw [hq]; exact hsc d (by simpa [reachN, hc] using hd)) _ rfl
  · simp only [hc, if_true, delayN]
    have b1 := sn_st_bit k r true w v.val cc hw v.isLt r
      ⟨(a.2.val + (3 * r + 1)) % k, Nat.mod_lt _ hk⟩
    have b2 := sn_st_bit k r true w' v.val cc hw' v.isLt r
      ⟨(a.2.val + (3 * r + 1)) % k, Nat.mod_lt _ hk⟩
    simp only at b1 b2
    rw [b1, b2]
    exact sn_loc_t _ _ _ _ r a.2.val (3 * r + 1) (7 * r - 2) (by omega) (by omega) (by omega)
      (fun d hd q hq => by
        show w.testBit q.val = w'.testBit q.val
        rw [hq]; exact hsc d (by simpa [reachN, hc] using hd)) _ rfl

theorem toZ_parityN (k mask x : ℕ) :
    toZ (parityN k mask x) = ∑ i : Fin k, toZ (mask.testBit i.val) * toZ (x.testBit i.val) := by
  unfold parityN
  rw [foldl_xor_toZ, toZ_false, zero_add]
  have h1 : (List.range k).map (fun i => toZ (mask.testBit i && x.testBit i)) =
      (List.finRange k).map (fun i : Fin k => toZ (mask.testBit i.val && x.testBit i.val)) := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp
  rw [h1, ← Fin.sum_univ_def]
  apply Finset.sum_congr rfl
  intro i _
  exact toZ_and _ _

def shiftEquiv (k d : ℕ) (hk : 0 < k) : Fin k ≃ Fin k where
  toFun p := ⟨(p.val + d) % k, Nat.mod_lt _ hk⟩
  invFun q := ⟨(q.val + k - d % k) % k, Nat.mod_lt _ hk⟩
  left_inv p := by
    apply Fin.ext
    show ((p.val + d) % k + k - d % k) % k = p.val
    rw [sn_idx_sub k (p.val + d) d p.val hk (by omega), Nat.mod_eq_of_lt p.isLt]
  right_inv q := by
    apply Fin.ext
    show ((q.val + k - d % k) % k + d) % k = q.val
    have hd : d % k < k := Nat.mod_lt _ hk
    rw [Nat.mod_add_mod]
    have h1 : q.val + k - d % k + d = q.val + k * (d / k + 1) := by
      have := Nat.div_add_mod d k
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt q.isLt]

theorem parity_reindex {k r m : ℕ} (hk : 0 < k) (R B : Fin m → Fin (2 ^ k))
    (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (w : Fin (2 ^ k)) (j : Fin m) :
    toZ (xor (parityN k (R j).val (stateN k r false w.val u.val cr))
      (parityN k (B j).val (stateN k r true w.val v.val cc))) =
    ∑ a ∈ (Finset.univ : Finset (Bool × Fin k)).filter (fun a => colN r R B a ≠ 0),
      toZ (sensorN u v cr cc a w.val) * colN r R B a j := by
  rw [toZ_xor, toZ_parityN, toZ_parityN]
  have hF : ∑ i : Fin k, toZ ((R j).val.testBit i.val) *
        toZ ((stateN k r false w.val u.val cr).testBit i.val) =
      ∑ p : Fin k, toZ (sensorN u v cr cc (false, p) w.val) * colN r R B (false, p) j := by
    rw [← Equiv.sum_comp (shiftEquiv k (delayN r false) hk)]
    apply Finset.sum_congr rfl
    intro p _
    simp only [shiftEquiv, Equiv.coe_fn_mk, sensorN, colN, toZ, Bool.false_eq_true, ite_false]
    exact mul_comm _ _
  have hT : ∑ i : Fin k, toZ ((B j).val.testBit i.val) *
        toZ ((stateN k r true w.val v.val cc).testBit i.val) =
      ∑ p : Fin k, toZ (sensorN u v cr cc (true, p) w.val) * colN r R B (true, p) j := by
    rw [← Equiv.sum_comp (shiftEquiv k (delayN r true) hk)]
    apply Finset.sum_congr rfl
    intro p _
    simp only [shiftEquiv, Equiv.coe_fn_mk, sensorN, colN, toZ, ite_true]
    exact mul_comm _ _
  rw [hF, hT]
  have hsum : ∑ a : Bool × Fin k, toZ (sensorN u v cr cc a w.val) * colN r R B a j =
      (∑ p : Fin k, toZ (sensorN u v cr cc (false, p) w.val) * colN r R B (false, p) j) +
      (∑ p : Fin k, toZ (sensorN u v cr cc (true, p) w.val) * colN r R B (true, p) j) := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rw [← hsum]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a _ ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha
  rw [ha]; simp

abbrev EvalIn (k r m : ℕ) : Type :=
  Fin k ⊕ ((Fin k ⊕ Fin k) ⊕ (((Fin r × Fin k) ⊕ (Fin r × Fin k)) ⊕
    ((Fin m × Fin k) ⊕ (Fin m × Fin k))))

def evalF {k r m : ℕ} (v : EvalIn k r m → Bool) (j : Fin m) : Bool :=
  let w := fun i => v (Sum.inl i)
  let u := fun i => v (Sum.inr (Sum.inl (Sum.inl i)))
  let vv := fun i => v (Sum.inr (Sum.inl (Sum.inr i)))
  let cr := fun p => v (Sum.inr (Sum.inr (Sum.inl (Sum.inl p))))
  let cc := fun p => v (Sum.inr (Sum.inr (Sum.inl (Sum.inr p))))
  let R := fun p => v (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))
  let B := fun p => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))
  let sf := sn_pre false w u cr r
  let st := sn_pre true w vv cc r
  xor (ofZ (∑ i : Fin k, toZ (R (j, i) && sf i))) (ofZ (∑ i : Fin k, toZ (B (j, i) && st i)))

theorem evalF_eq {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (R B : Fin m → Fin (2 ^ k)) (w : Fin (2 ^ k)) (j : Fin m) :
    evalF (k := k) (r := r) (m := m) (Sum.elim (fun i : Fin k => w.val.testBit i.val)
      (Sum.elim (Sum.elim (fun i : Fin k => u.val.testBit i.val) (fun i : Fin k => v.val.testBit i.val))
        (Sum.elim (Sum.elim (fun p : Fin r × Fin k => (cr p.1).val.testBit p.2.val)
            (fun p : Fin r × Fin k => (cc p.1).val.testBit p.2.val))
          (Sum.elim (fun p : Fin m × Fin k => (R p.1).val.testBit p.2.val)
            (fun p : Fin m × Fin k => (B p.1).val.testBit p.2.val))))) j =
      xor (parityN k (R j).val (stateN k r false w.val u.val cr))
        (parityN k (B j).val (stateN k r true w.val v.val cc)) := by
  rw [← toZ_inj]
  unfold evalF
  simp only [Sum.elim_inl, Sum.elim_inr, toZ_xor, toZ_ofZ, toZ_and, toZ_parityN]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    rw [sn_state_eq, sn_st_bit k r false w.val u.val cr w.isLt u.isLt r i]; rfl
  · apply Finset.sum_congr rfl; intro i _
    rw [sn_state_eq, sn_st_bit k r true w.val v.val cc w.isLt v.isLt r i]; rfl

theorem cmp_evalF (k r m : ℕ) :
    Cmp (EvalIn k r m) (Fin m) (128 * k * (r + 1) + m * (10 * k + 6)) (evalF (k := k) (r := r) (m := m)) := by
  have hsf : Cmp (EvalIn k r m) (Fin k) (64 * k * (r + 1))
      (fun v => sn_pre false (fun i => v (Sum.inl i))
        (fun i => v (Sum.inr (Sum.inl (Sum.inl i))))
        (fun p => v (Sum.inr (Sum.inr (Sum.inl (Sum.inl p))))) r) :=
    Cmp.sel (fun x => Sum.elim Sum.inl (fun y => Sum.elim (fun i => Sum.inr (Sum.inl (Sum.inl i)))
      (fun p => Sum.inr (Sum.inr (Sum.inl (Sum.inl p)))) y) x) (sn_cmp_pre k r false)
  have hst : Cmp (EvalIn k r m) (Fin k) (64 * k * (r + 1))
      (fun v => sn_pre true (fun i => v (Sum.inl i))
        (fun i => v (Sum.inr (Sum.inl (Sum.inr i))))
        (fun p => v (Sum.inr (Sum.inr (Sum.inl (Sum.inr p))))) r) :=
    Cmp.sel (fun x => Sum.elim Sum.inl (fun y => Sum.elim (fun i => Sum.inr (Sum.inl (Sum.inr i)))
      (fun p => Sum.inr (Sum.inr (Sum.inl (Sum.inr p)))) y) x) (sn_cmp_pre k r true)
  have hboth := Cmp.pair hsf hst
  let J := EvalIn k r m ⊕ (Fin k ⊕ Fin k)
  have hpar : Cmp J (Fin m) (m * (10 * k + 6))
      (fun w j => xor (ofZ (∑ i : Fin k, toZ (w (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (j, i)))))) &&
          w (Sum.inr (Sum.inl i)))))
        (ofZ (∑ i : Fin k, toZ (w (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, i)))))) &&
          w (Sum.inr (Sum.inr i)))))) := by
    have h := Cmp.ofBits (ι := J) (κ := Fin m) (s := 10 * k + 6) (fun j : Fin m => by
      have c1 := Cb.sumZ (ι := J) (I := Fin k) (fun i => Cb.and
        (Cb.var (ι := J) (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (j, i)))))))
        (Cb.var (ι := J) (Sum.inr (Sum.inl i))))
      have c2 := Cb.sumZ (ι := J) (I := Fin k) (fun i => Cb.and
        (Cb.var (ι := J) (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, i)))))))
        (Cb.var (ι := J) (Sum.inr (Sum.inr i))))
      simp only [Fintype.card_fin] at c1 c2
      exact Cb.mono (Cb.xor c1 c2) (by omega))
    rw [Fintype.card_fin] at h
    exact h
  have htot := Cmp.thn hboth hpar
  refine Cmp.mono (Cmp.congr htot ?_) (by ring_nf; omega)
  intro v j
  simp only [Sum.elim_inl, Sum.elim_inr]
  rfl

theorem welsh_transversal {I Y : Type*} [DecidableEq I] [DecidableEq Y]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (E : Finset (Finset I)) (B : Finset I → Finset Y) (M : ℕ)
    (hM : ∀ c : Finset I → Y, (∀ e ∈ E, c e ∈ B e ∨ c e = 0) →
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ((E.image c : Finset Y) : Set Y)) ≤ M) :
    ∃ E' ⊆ E, (E \ E').card +
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ((E'.biUnion B : Finset Y) : Set Y)) ≤ M := by
  classical
  have main : ∀ N : ℕ, ∀ B : Finset I → Finset Y, (∑ e ∈ E, (B e).card) = N →
      (∀ c : Finset I → Y, (∀ e ∈ E, c e ∈ B e ∨ c e = 0) →
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ((E.image c : Finset Y) : Set Y)) ≤ M) →
      ∃ E' ⊆ E, (E \ E').card +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ((E'.biUnion B : Finset Y) : Set Y)) ≤ M := by
    intro N
    induction N using Nat.strong_induction_on with
    | ind N ih =>
      intro B hN hMB
      by_cases hsmall : ∀ e ∈ E, (B e).card ≤ 1
      · let c : Finset I → Y := fun e => if h : (B e).Nonempty then h.choose else 0
        have hc : ∀ e ∈ E, c e ∈ B e ∨ c e = 0 := by
          intro e _
          by_cases hne : (B e).Nonempty
          · left; simp only [c, dif_pos hne]; exact hne.choose_spec
          · right; simp only [c, dif_neg hne]
        have hsub : Submodule.span (ZMod 2) ((E.biUnion B : Finset Y) : Set Y) ≤
            Submodule.span (ZMod 2) ((E.image c : Finset Y) : Set Y) := by
          apply Submodule.span_mono
          intro y hy
          simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image] at hy ⊢
          obtain ⟨e, heE, hyB⟩ := hy
          have hne : (B e).Nonempty := ⟨y, hyB⟩
          have hcard : (B e).card ≤ 1 := hsmall e heE
          have huniq : y = hne.choose := Finset.card_le_one.1 hcard y hyB hne.choose hne.choose_spec
          exact ⟨e, heE, by simp only [c, dif_pos hne, huniq]⟩
        refine ⟨E, Finset.Subset.refl E, ?_⟩
        rw [Finset.sdiff_self, Finset.card_empty, zero_add]
        exact le_trans (Submodule.finrank_mono hsub) (hMB c hc)
      · push_neg at hsmall
        obtain ⟨e0, he0E, hgt⟩ := hsmall
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hgt
        let B1 : Finset I → Finset Y := Function.update B e0 ((B e0).erase x)
        let B2 : Finset I → Finset Y := Function.update B e0 ((B e0).erase y)
        have hB1sub : ∀ e, B1 e ⊆ B e := by
          intro e; by_cases he : e = e0
          · subst he; simp [B1, Finset.erase_subset]
          · simp [B1, he]
        have hB2sub : ∀ e, B2 e ⊆ B e := by
          intro e; by_cases he : e = e0
          · subst he; simp [B2, Finset.erase_subset]
          · simp [B2, he]
        have hlt1 : ∑ e ∈ E, (B1 e).card < N := by
          rw [← hN]
          apply Finset.sum_lt_sum
          · intro e _; exact Finset.card_le_card (hB1sub e)
          · exact ⟨e0, he0E, by simp only [B1, Function.update_self]; exact Finset.card_erase_lt_of_mem hx⟩
        have hlt2 : ∑ e ∈ E, (B2 e).card < N := by
          rw [← hN]
          apply Finset.sum_lt_sum
          · intro e _; exact Finset.card_le_card (hB2sub e)
          · exact ⟨e0, he0E, by simp only [B2, Function.update_self]; exact Finset.card_erase_lt_of_mem hy⟩
        obtain ⟨S, hSE, hSM⟩ := ih _ hlt1 B1 rfl (fun c hc =>
          hMB c (fun e he => (hc e he).imp (fun h => hB1sub e h) id))
        obtain ⟨T, hTE, hTM⟩ := ih _ hlt2 B2 rfl (fun c hc =>
          hMB c (fun e he => (hc e he).imp (fun h => hB2sub e h) id))
        by_contra hcon
        push_neg at hcon
        have he0S : e0 ∈ S := by
          by_contra hnot
          have heq : S.biUnion B1 = S.biUnion B := by
            apply Finset.biUnion_congr rfl
            intro e he
            have : e ≠ e0 := fun h => hnot (h ▸ he)
            simp [B1, this]
          rw [heq] at hSM
          have := hcon S hSE
          omega
        have he0T : e0 ∈ T := by
          by_contra hnot
          have heq : T.biUnion B2 = T.biUnion B := by
            apply Finset.biUnion_congr rfl
            intro e he
            have : e ≠ e0 := fun h => hnot (h ▸ he)
            simp [B2, this]
          rw [heq] at hTM
          have := hcon T hTE
          omega
        let US := Submodule.span (ZMod 2) ((S.biUnion B1 : Finset Y) : Set Y)
        let UT := Submodule.span (ZMod 2) ((T.biUnion B2 : Finset Y) : Set Y)
        have hsup_set : (S.biUnion B1) ∪ (T.biUnion B2) = (S ∪ T).biUnion B := by
          ext z
          simp only [Finset.mem_union, Finset.mem_biUnion]
          constructor
          · rintro (⟨e, he, hz⟩ | ⟨e, he, hz⟩)
            · exact ⟨e, Or.inl he, hB1sub e hz⟩
            · exact ⟨e, Or.inr he, hB2sub e hz⟩
          · rintro ⟨e, he | he, hz⟩
            · by_cases h0 : e = e0
              · subst h0
                by_cases hzx : z = x
                · right; exact ⟨e, he0T, by simp [B2, hzx, hxy, hx]⟩
                · left; exact ⟨e, he0S, by simp [B1, hzx, hz]⟩
              · left; exact ⟨e, he, by simpa [B1, h0] using hz⟩
            · by_cases h0 : e = e0
              · subst h0
                by_cases hzx : z = x
                · right; exact ⟨e, he0T, by simp [B2, hzx, hxy, hx]⟩
                · left; exact ⟨e, he0S, by simp [B1, hzx, hz]⟩
              · right; exact ⟨e, he, by simpa [B2, h0] using hz⟩
        have hsup : US ⊔ UT = Submodule.span (ZMod 2) ((((S ∪ T).biUnion B : Finset Y)) : Set Y) := by
          dsimp only [US, UT]
          rw [← Submodule.span_union, ← Finset.coe_union, hsup_set]
        have hinf : Submodule.span (ZMod 2) ((((S ∩ T).erase e0).biUnion B : Finset Y) : Set Y) ≤ US ⊓ UT := by
          rw [le_inf_iff]
          constructor
          · apply Submodule.span_mono
            intro z hz
            simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_inter] at hz ⊢
            obtain ⟨e, ⟨hne, heS, _⟩, hzB⟩ := hz
            exact ⟨e, heS, by simpa [B1, hne] using hzB⟩
          · apply Submodule.span_mono
            intro z hz
            simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_erase, Finset.mem_inter] at hz ⊢
            obtain ⟨e, ⟨hne, _, heT⟩, hzB⟩ := hz
            exact ⟨e, heT, by simpa [B2, hne] using hzB⟩
        have hrank : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ((((S ∪ T).biUnion B : Finset Y)) : Set Y)) +
            Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ((((S ∩ T).erase e0).biUnion B : Finset Y) : Set Y)) ≤
            Module.finrank (ZMod 2) US + Module.finrank (ZMod 2) UT := by
          have h1 := Submodule.finrank_sup_add_finrank_inf_eq US UT
          have h2 := Submodule.finrank_mono hinf
          rw [hsup] at h1
          omega
        have hcard1 : (E \ S).card + (E \ T).card = (E \ (S ∩ T)).card + (E \ (S ∪ T)).card := by
          have hu : (E \ S) ∪ (E \ T) = E \ (S ∩ T) := by ext e; simp; tauto
          have hi : (E \ S) ∩ (E \ T) = E \ (S ∪ T) := by ext e; simp; tauto
          rw [← hu, ← hi]
          exact (Finset.card_union_add_card_inter (E \ S) (E \ T)).symm
        have hcard2 : (E \ ((S ∩ T).erase e0)).card = (E \ (S ∩ T)).card + 1 := by
          have hins : E \ ((S ∩ T).erase e0) = insert e0 (E \ (S ∩ T)) := by
            ext e
            simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_inter, Finset.mem_insert]
            by_cases he : e = e0
            · subst he; simp [he0E]
            · simp [he]
          rw [hins, Finset.card_insert_of_notMem (by simp [he0S, he0T])]
        have hST1 := hcon (S ∪ T) (Finset.union_subset hSE hTE)
        have hST2 := hcon ((S ∩ T).erase e0) (Finset.Subset.trans (Finset.erase_subset _ _)
          (Finset.Subset.trans Finset.inter_subset_left hSE))
        dsimp only [US, UT] at hrank
        omega
  exact main _ B rfl hM

theorem exists_basis_finset {Y : Type*} [DecidableEq Y]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y] (S : Finset Y) :
    ∃ T ⊆ S, T.card = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S : Set Y)) ∧
      Submodule.span (ZMod 2) (T : Set Y) = Submodule.span (ZMod 2) (S : Set Y) := by
  classical
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent (ZMod 2) (S : Set Y)
  let T : Finset Y := S.filter (fun y => y ∈ b)
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hTb : b = (T : Set Y) := by
    ext y
    simp only [T, Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨hbS h, h⟩, fun h => h.2⟩
  rw [hTb] at hsp hli
  refine ⟨T, hTS, ?_, hsp⟩
  have hcard := finrank_span_eq_card hli
  rw [Subtype.range_coe] at hcard
  rw [← hsp, hcard, ← Fintype.card_coe T]
  exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Finset.mem_coe))).symm

def M_tup {k m h' : ℕ} (col : Bool × Fin k → Fin m → ZMod 2)
    (tup : Fin h' → Option (Bool × Fin k)) : Fin (m + h') × Fin (m + h') → Bool := fun p =>
  splitF (fun _ : Fin m => false)
    (fun s : Fin h' => splitF (fun j : Fin m => (tup s).elim false (fun a => ofZ (col a j)))
      (fun _ : Fin h' => false) p.2) p.1

def R_tup {k m h' : ℕ} (col : Bool × Fin k → Fin m → ZMod 2)
    (tup : Fin h' → Option (Bool × Fin k)) : Fin m × Fin m → Bool := fun p =>
  gj (m + h') (M_tup col tup) (Fin.castAdd h' p.1, Fin.castAdd h' p.2)

def tilde {m : ℕ} (R : Fin m × Fin m → Bool) (z : Fin m → ZMod 2) : Fin m → ZMod 2 :=
  fun j => z j + ∑ p : Fin m, z p * toZ (R (p, j))

def rowSpan {m : ℕ} (R : Fin m × Fin m → Bool) : Submodule (ZMod 2) (Fin m → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun p : Fin m => fun j : Fin m => toZ (R (p, j)))

def rhoM {m : ℕ} (R : Fin m × Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun p : Fin m => R (p, p) = true)).card

theorem R_tup_gjf {k m h' : ℕ} (col : Bool × Fin k → Fin m → ZMod 2)
    (tup : Fin h' → Option (Bool × Fin k)) : GJF (R_tup col tup) := by
  refine ⟨?_, ?_⟩
  · intro p hp i
    have h := gj_pivcol (M_tup col tup) (Fin.castAdd h' p) hp (Fin.castAdd h' i)
    simp only [R_tup]
    rw [h]
    simp [Fin.castAdd_inj]
  · intro q hq j
    exact gj_zerorow (M_tup col tup) (Fin.castAdd h' q) hq (Fin.castAdd h' j)

theorem R_tup_zero_tail {k m h' : ℕ} (col : Bool × Fin k → Fin m → ZMod 2)
    (tup : Fin h' → Option (Bool × Fin k)) (s : Fin h') (c : Fin (m + h')) :
    gj (m + h') (M_tup col tup) (Fin.natAdd m s, c) = false := by
  apply gj_zerorow
  apply gj_col_zero
  intro r
  unfold M_tup
  refine Fin.addCases (fun i => ?_) (fun s' => ?_) r
  · simp [splitF_castAdd]
  · simp [splitF_natAdd]

theorem rowSpan_R_tup {k m h' : ℕ} (col : Bool × Fin k → Fin m → ZMod 2)
    (tup : Fin h' → Option (Bool × Fin k)) :
    rowSpan (R_tup col tup) =
      Submodule.span (ZMod 2) (Set.range fun s : Fin h' => (tup s).elim 0 col) := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv (M_tup col tup)
  have hMrow : ∀ s : Fin h', ∀ j : Fin m,
      mat (M_tup col tup) (Fin.natAdd m s) (Fin.castAdd h' j) = (tup s).elim 0 col j := by
    intro s j
    simp only [mat_eq_toZ, M_tup, splitF_natAdd, splitF_castAdd]
    cases tup s with
    | none => rfl
    | some a => exact toZ_ofZ (col a j)
  apply le_antisymm
  · rw [rowSpan, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have hrow : (fun j : Fin m => toZ (R_tup col tup (p, j))) =
        ∑ s : Fin h', U (Fin.castAdd h' p) (Fin.natAdd m s) • ((tup s).elim 0 col) := by
      funext j
      have hc := congrFun (congrFun h1 (Fin.castAdd h' p)) (Fin.castAdd h' j)
      rw [Matrix.mul_apply, Fin.sum_univ_add] at hc
      have hz0 : ∑ i : Fin m, U (Fin.castAdd h' p) (Fin.castAdd h' i) *
          mat (M_tup col tup) (Fin.castAdd h' i) (Fin.castAdd h' j) = 0 := by
        apply Finset.sum_eq_zero; intro i _
        simp [mat_eq_toZ, M_tup, splitF_castAdd, toZ_false]
      rw [hz0, zero_add] at hc
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change mat (gj (m + h') (M_tup col tup)) (Fin.castAdd h' p) (Fin.castAdd h' j) = _
      rw [hc]
      apply Finset.sum_congr rfl; intro s _
      rw [hMrow s j]
    dsimp only
    rw [hrow]
    exact Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    have hrow : (tup s).elim 0 col =
        ∑ p : Fin m, U' (Fin.natAdd m s) (Fin.castAdd h' p) •
          (fun j : Fin m => toZ (R_tup col tup (p, j))) := by
      funext j
      have hc := congrFun (congrFun h2 (Fin.natAdd m s)) (Fin.castAdd h' j)
      rw [hMrow s j, Matrix.mul_apply, Fin.sum_univ_add] at hc
      have hz1 : ∑ s' : Fin h', U' (Fin.natAdd m s) (Fin.natAdd m s') *
          mat (gj (m + h') (M_tup col tup)) (Fin.natAdd m s') (Fin.castAdd h' j) = 0 := by
        apply Finset.sum_eq_zero; intro s' _
        rw [mat_eq_toZ, R_tup_zero_tail, toZ_false, mul_zero]
      rw [hz1, add_zero] at hc
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hc]
      rfl
    dsimp only
    rw [hrow]
    exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))

theorem tilde_eq_zero_iff {m : ℕ} {R : Fin m × Fin m → Bool} (hR : GJF R) (z : Fin m → ZMod 2) :
    tilde R z = 0 ↔ z ∈ rowSpan R := by
  constructor
  · intro h
    have hz : z = ∑ p : Fin m, z p • (fun j => toZ (R (p, j))) := by
      funext j
      have hj := congrFun h j
      simp only [tilde, Pi.zero_apply] at hj
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have := congrArg (· + ∑ p : Fin m, z p * toZ (R (p, j))) hj
      simp only [zero_add, add_assoc, z2, add_zero] at this
      exact this
    rw [hz]
    exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩))
  · intro h
    have hmem : ∀ w ∈ rowSpan R, tilde R w = 0 := by
      intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨q, rfl⟩
        funext j
        simp only [tilde, Pi.zero_apply]
        have := Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => GJF_term hR q p j)
        rw [this]
        simp [z2]
      · funext j; simp [tilde]
      · intro a b _ _ ha hb
        funext j
        have ha' := congrFun ha j
        have hb' := congrFun hb j
        simp only [tilde, Pi.add_apply, Pi.zero_apply, add_mul, Finset.sum_add_distrib] at ha' hb' ⊢
        linear_combination ha' + hb'
      · intro c a _ ha
        funext j
        have ha' := congrFun ha j
        simp only [tilde, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha' ⊢
        have hmul : ∑ p : Fin m, c * a p * toZ (R (p, j)) = c * ∑ p : Fin m, a p * toZ (R (p, j)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
        rw [hmul, ← mul_add, ha', mul_zero]
    exact hmem z h

theorem eq_zero_iff_tilde_and_piv {m : ℕ} {R : Fin m × Fin m → Bool} (hR : GJF R)
    (z : Fin m → ZMod 2) :
    z = 0 ↔ tilde R z = 0 ∧ ∀ p : Fin m, R (p, p) = true → z p = 0 := by
  constructor
  · intro h; subst h; exact ⟨by funext j; simp [tilde], fun _ _ => rfl⟩
  · rintro ⟨ht, hp⟩
    funext j
    have hj := congrFun ht j
    simp only [tilde, Pi.zero_apply] at hj
    have hsum : ∑ p : Fin m, z p * toZ (R (p, j)) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      by_cases hpp : R (p, p) = true
      · rw [hp p hpp, zero_mul]
      · rw [hR.2 p (by simpa using hpp) j, toZ_false, mul_zero]
    rw [hsum, add_zero] at hj
    exact hj

theorem finrank_rowSpan {m : ℕ} {R : Fin m × Fin m → Bool} (hR : GJF R) :
    Module.finrank (ZMod 2) (rowSpan R) = rhoM R := by
  let Pset : Finset (Fin m) := Finset.univ.filter (fun p : Fin m => R (p, p) = true)
  let v : Pset → (Fin m → ZMod 2) := fun p j => toZ (R (p.1, j))
  have hli : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have hp := congrFun hg p.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at hp
    have hpp : R (p.1, p.1) = true := (Finset.mem_filter.1 p.2).2
    have hterm : ∀ q : Pset, g q * toZ (R (q.1, p.1)) = if q = p then g p else 0 := by
      intro q
      rw [hR.1 p.1 hpp q.1]
      by_cases hqp : q = p
      · subst hqp; simp [toZ_true]
      · have hne : q.1 ≠ p.1 := fun h => hqp (Subtype.ext h)
        simp [hqp, hne, toZ_false]
    rw [Finset.sum_congr rfl (fun q _ => hterm q)] at hp
    simpa using hp
  have hsp : Submodule.span (ZMod 2) (Set.range v) = rowSpan R := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact Submodule.subset_span ⟨p.1, rfl⟩
    · rw [rowSpan, Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      by_cases hq : R (q, q) = true
      · exact Submodule.subset_span ⟨⟨q, Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩⟩, rfl⟩
      · have hz : (fun j => toZ (R (q, j))) = 0 := by
          funext j; rw [hR.2 q (by simpa using hq) j, toZ_false]; rfl
        dsimp only
        rw [hz]
        exact Submodule.zero_mem _
  rw [← hsp, finrank_span_eq_card hli, Fintype.card_coe]
  rfl

theorem tilde_linear {m : ℕ} (R : Fin m × Fin m → Bool) :
    (∀ z1 z2, tilde R (z1 + z2) = tilde R z1 + tilde R z2) ∧
    (∀ (c : ZMod 2) z, tilde R (c • z) = c • tilde R z) ∧
    tilde R 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro z1 z2; funext j
    simp only [tilde, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  · intro c z; funext j
    simp only [tilde, Pi.smul_apply, smul_eq_mul]
    rw [mul_add, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro p _; ring
  · funext j; simp [tilde]

def activeN {k m : ℕ} (r : ℕ) (R B : Fin m → Fin (2 ^ k)) : Finset (Bool × Fin k) :=
  (Finset.univ : Finset (Bool × Fin k)).filter (fun a => colN r R B a ≠ 0)

def leftN {k : ℕ} (r : ℕ) (P : Finset (Fin k)) (a : Bool × Fin k) : Finset (Fin k) :=
  scopeN k r a \ P

def goodN {k m : ℕ} (r : ℕ) (R B : Fin m → Fin (2 ^ k)) (P : Finset (Fin k)) : Prop :=
  ∀ a ∈ activeN r R B, (leftN r P a).card ≤ 2

def pairsN {k m : ℕ} (r : ℕ) (R B : Fin m → Fin (2 ^ k)) (P : Finset (Fin k)) :
    Finset (Finset (Fin k)) :=
  ((activeN r R B).image (leftN r P)).filter (fun e => e.card = 2)

noncomputable def worstN {k m : ℕ} (r : ℕ) (R B : Fin m → Fin (2 ^ k)) (P : Finset (Fin k)) : ℕ :=
  (Finset.univ : Finset (Bool × Fin k → ZMod 2)).sup (fun w =>
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      ((((pairsN r R B P).image (fun e =>
        ∑ a ∈ (activeN r R B).filter (fun a => leftN r P a = e), w a • colN r R B a)) :
          Finset (Fin m → ZMod 2)) : Set (Fin m → ZMod 2))))

def worksN {k m : ℕ} (r b h : ℕ) (R B : Fin m → Fin (2 ^ k)) (P : Finset (Fin k)) : Prop :=
  goodN r R B P ∧ worstN r R B P ≤ h ∧ P.card + worstN r R B P ≤ b

theorem exists_tup_of_works {k r m b h : ℕ} (hk : 0 < k) (R B : Fin m → Fin (2 ^ k))
    (P0 : Finset (Fin k)) (hw : worksN r b h R B P0) :
    let h' := min h (min b (min m (2 * k)))
    ∃ (tup : Fin h' → Option (Bool × Fin k)) (P1 : Finset (Fin k)),
      P1.card + rhoM (R_tup (colN r R B) tup) ≤ b ∧
      rhoM (R_tup (colN r R B) tup) ≤ h ∧
      ∀ a ∈ activeN r R B,
        (leftN r P1 a).card ≤ if tilde (R_tup (colN r R B) tup) (colN r R B a) = 0 then 2 else 1 := by
  classical
  intro h'
  obtain ⟨hgood, hwh, hwb⟩ := hw
  let E := pairsN r R B P0
  let Bf : Finset (Fin k) → Finset (Fin m → ZMod 2) :=
    fun e => ((activeN r R B).filter (fun a => leftN r P0 a = e)).image (colN r R B)
  have hM : ∀ c : Finset (Fin k) → (Fin m → ZMod 2), (∀ e ∈ E, c e ∈ Bf e ∨ c e = 0) →
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (((E.image c : Finset (Fin m → ZMod 2)) : Set (Fin m → ZMod 2)))) ≤
        worstN r R B P0 := by
    intro c hc
    have hch : ∀ e ∈ E, ∃ a_opt : Option (Bool × Fin k),
        match a_opt with
        | none => c e = 0
        | some a => a ∈ activeN r R B ∧ leftN r P0 a = e ∧ colN r R B a = c e := by
      intro e he
      rcases hc e he with hmem | hz
      · simp only [Bf, Finset.mem_image, Finset.mem_filter] at hmem
        obtain ⟨a, ⟨ha, hle⟩, hcol⟩ := hmem
        exact ⟨some a, ha, hle, hcol⟩
      · exact ⟨none, hz⟩
    let w : Bool × Fin k → ZMod 2 := fun a =>
      if hE : leftN r P0 a ∈ E then
        match (hch (leftN r P0 a) hE).choose with
        | none => 0
        | some a0 => if a = a0 then 1 else 0
      else 0
    have himg : E.image c = E.image (fun e =>
        ∑ a ∈ (activeN r R B).filter (fun a => leftN r P0 a = e), w a • colN r R B a) := by
      apply Finset.image_congr
      intro e he
      have he' : e ∈ E := Finset.mem_coe.1 he
      have hspec := (hch e he').choose_spec
      cases hopt : (hch e he').choose with
      | none =>
        rw [hopt] at hspec
        rw [hspec]
        symm
        apply Finset.sum_eq_zero
        intro a ha
        have hle : leftN r P0 a = e := (Finset.mem_filter.1 ha).2
        simp [w, hle, he', hopt]
      | some a0 =>
        rw [hopt] at hspec
        obtain ⟨ha0, hle0, hcol0⟩ := hspec
        dsimp only
        symm
        rw [Finset.sum_eq_single a0]
        · simp [w, hle0, he', hopt, hcol0]
        · intro a ha hne
          have hle : leftN r P0 a = e := (Finset.mem_filter.1 ha).2
          simp [w, hle, he', hopt, hne]
        · intro hnot
          exact absurd (Finset.mem_filter.2 ⟨ha0, hle0⟩) hnot
    rw [himg]
    unfold worstN
    exact Finset.le_sup (f := fun w : Bool × Fin k → ZMod 2 =>
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (((pairsN r R B P0 |>.image (fun e => ∑ a ∈ (activeN r R B).filter (fun a => leftN r P0 a = e),
          w a • colN r R B a)) : Finset (Fin m → ZMod 2)) : Set (Fin m → ZMod 2)))) (Finset.mem_univ w)
  obtain ⟨E', hE'E, hE'bound⟩ := welsh_transversal E Bf (worstN r R B P0) hM
  obtain ⟨T, hTsub, hTcard, hTspan⟩ := exists_basis_finset (E'.biUnion Bf)
  have hTd_le_w : T.card ≤ worstN r R B P0 := by omega
  have hTd_le_m : T.card ≤ m := by
    rw [hTcard]
    calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ((E'.biUnion Bf : Finset (Fin m → ZMod 2)) : Set _))
        ≤ Module.finrank (ZMod 2) (Fin m → ZMod 2) := Submodule.finrank_le _
      _ = m := by simp
  have hTd_le_2k : T.card ≤ 2 * k := by
    have hsubA : E'.biUnion Bf ⊆ (activeN r R B).image (colN r R B) := by
      intro y hy
      simp only [Finset.mem_biUnion, Bf, Finset.mem_image, Finset.mem_filter] at hy ⊢
      obtain ⟨e, _, a, ⟨ha, _⟩, rfl⟩ := hy
      exact ⟨a, ha, rfl⟩
    calc T.card ≤ (E'.biUnion Bf).card := Finset.card_le_card hTsub
      _ ≤ ((activeN r R B).image (colN r R B)).card := Finset.card_le_card hsubA
      _ ≤ (activeN r R B).card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Bool × Fin k)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 * k := by simp
  have hTd_le_h' : T.card ≤ h' := by
    dsimp only [h']; omega
  have hTmem : ∀ y ∈ T, ∃ a ∈ activeN r R B, colN r R B a = y := by
    intro y hy
    have hy' := hTsub hy
    simp only [Finset.mem_biUnion, Bf, Finset.mem_image, Finset.mem_filter] at hy'
    obtain ⟨_, _, a, ⟨ha, _⟩, hcol⟩ := hy'
    exact ⟨a, ha, hcol⟩
  let TL := T.toList
  have hTLlen : TL.length = T.card := Finset.length_toList T
  let tup : Fin h' → Option (Bool × Fin k) := fun s =>
    if hs : s.val < TL.length then
      some (hTmem (TL[s.val]) (Finset.mem_toList.1 (List.getElem_mem hs))).choose
    else none
  have hspan_eq : rowSpan (R_tup (colN r R B) tup) =
      Submodule.span (ZMod 2) ((E'.biUnion Bf : Finset (Fin m → ZMod 2)) : Set _) := by
    rw [rowSpan_R_tup, ← hTspan]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      by_cases hs : s.val < TL.length
      · simp only [tup, dif_pos hs, Option.elim_some]
        rw [(hTmem (TL[s.val]) (Finset.mem_toList.1 (List.getElem_mem hs))).choose_spec.2]
        exact Submodule.subset_span (Finset.mem_toList.1 (List.getElem_mem hs))
      · simp only [tup, dif_neg hs, Option.elim_none]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      intro y hy
      have hyL : y ∈ TL := Finset.mem_toList.2 hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hyL
      have hi' : i < h' := by omega
      have hcol : (tup ⟨i, hi'⟩).elim 0 (colN r R B) = TL[i] := by
        simp only [tup, dif_pos hi, Option.elim_some]
        exact (hTmem (TL[i]) (Finset.mem_toList.1 (List.getElem_mem hi))).choose_spec.2
      rw [← hcol]
      exact Submodule.subset_span ⟨⟨i, hi'⟩, rfl⟩
  have hrho : rhoM (R_tup (colN r R B) tup) = T.card := by
    rw [← finrank_rowSpan (R_tup_gjf (colN r R B) tup), hspan_eq, hTcard]
  let P1 : Finset (Fin k) := P0 ∪ (E \ E').image (fun e => if he : e.Nonempty then e.min' he else ⟨0, hk⟩)
  refine ⟨tup, P1, ?_, ?_, ?_⟩
  · have hP1card : P1.card ≤ P0.card + (E \ E').card := by
      calc P1.card ≤ P0.card + ((E \ E').image _).card := Finset.card_union_le _ _
        _ ≤ P0.card + (E \ E').card := Nat.add_le_add_left Finset.card_image_le _
    rw [hrho]
    omega
  · rw [hrho]; omega
  · intro a ha
    have hP0sub : P0 ⊆ P1 := Finset.subset_union_left
    have hlsub : leftN r P1 a ⊆ leftN r P0 a := Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hP0sub
    have hle2 : (leftN r P1 a).card ≤ 2 := le_trans (Finset.card_le_card hlsub) (hgood a ha)
    by_cases htil : tilde (R_tup (colN r R B) tup) (colN r R B a) = 0
    · simp [htil, hle2]
    · simp only [htil, ↓reduceIte]
      by_contra hgt1
      have hcard2 : (leftN r P1 a).card = 2 := by omega
      have hcardP0 : (leftN r P0 a).card = 2 := by
        have := hgood a ha; have := Finset.card_le_card hlsub; omega
      have hleq : leftN r P1 a = leftN r P0 a := Finset.eq_of_subset_of_card_le hlsub (by omega)
      have heE : leftN r P0 a ∈ E := by
        simp only [E, pairsN, Finset.mem_filter, Finset.mem_image]
        exact ⟨⟨a, ha, rfl⟩, hcardP0⟩
      by_cases heE' : leftN r P0 a ∈ E'
      · apply htil
        rw [tilde_eq_zero_iff (R_tup_gjf (colN r R B) tup), hspan_eq]
        apply Submodule.subset_span
        simp only [Finset.mem_coe, Finset.mem_biUnion, Bf, Finset.mem_image, Finset.mem_filter]
        exact ⟨leftN r P0 a, heE', a, ⟨ha, rfl⟩, rfl⟩
      · have hne : (leftN r P0 a).Nonempty := Finset.card_pos.1 (by omega)
        set x0 := (leftN r P0 a).min' hne
        have hm1 : x0 ∈ leftN r P0 a := Finset.min'_mem _ hne
        have hmP1 : x0 ∈ P1 := by
          apply Finset.mem_union_right
          simp only [Finset.mem_image, Finset.mem_sdiff]
          exact ⟨leftN r P0 a, ⟨heE, heE'⟩, by simp [hne, x0]⟩
        rw [← hleq] at hm1
        exact (Finset.mem_sdiff.1 hm1).2 hmP1

theorem works_of_feasible {k r m b h : ℕ} (R B : Fin m → Fin (2 ^ k))
    (Rmm : Fin m × Fin m → Bool) (hR : GJF Rmm) (P : Finset (Fin k))
    (hdh : rhoM Rmm ≤ h) (hPb : P.card + rhoM Rmm ≤ b)
    (hcap : ∀ a ∈ activeN r R B, (leftN r P a).card ≤ if tilde Rmm (colN r R B a) = 0 then 2 else 1) :
    worksN r b h R B P := by
  have hgood : goodN r R B P := by
    intro a ha
    have h1 := hcap a ha
    by_cases ht : tilde Rmm (colN r R B a) = 0 <;> simp [ht] at h1 <;> omega
  have hworst : worstN r R B P ≤ rhoM Rmm := by
    unfold worstN
    apply Finset.sup_le
    intro w _
    rw [← finrank_rowSpan hR]
    apply Submodule.finrank_mono
    rw [Submodule.span_le]
    intro y hy
    simp only [Finset.mem_coe, Finset.mem_image, pairsN, Finset.mem_filter] at hy
    obtain ⟨e, ⟨_, he2⟩, rfl⟩ := hy
    apply Submodule.sum_mem
    intro a ha
    simp only [Finset.mem_filter] at ha
    apply Submodule.smul_mem
    rw [← tilde_eq_zero_iff hR]
    have hc := hcap a ha.1
    rw [ha.2, he2] at hc
    by_contra hne
    simp [hne] at hc
  exact ⟨hgood, le_trans hworst hdh, by omega⟩

def bfWinCand (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (col_b : Bool) (d : Fin (k + 1) → ℤ) (v : Fin (k + 1)) (cur : ℤ) : ℤ :=
  let L := reachN r col_b + 1
  if hL : L < k then
    if hv : 0 < v.val then
      let u : Fin k := if hlv : L ≤ v.val then ⟨v.val - L, by omega⟩ else ⟨v.val + k - L, by omega⟩
      let w : ℤ := (if inW (col_b, u) then 2 else 1) - (if L ≤ v.val then 0 else (S.val : ℤ))
      if act (col_b, u) then min cur (d ⟨u.val, by omega⟩ + w) else cur
    else cur
  else cur

def bfStepZ (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (d : Fin (k + 1) → ℤ) (v : Fin (k + 1)) : ℤ :=
  let c0 := d v
  let c1 := if h : 0 < v.val then min c0 (d ⟨v.val - 1, by omega⟩ + 1) else c0
  let c2 := if h : v.val < k then min c1 (d ⟨v.val + 1, by omega⟩) else c1
  let c3 := if v.val = k then min c2 (d ⟨0, by omega⟩ + (S.val : ℤ)) else c2
  let c4 := if v.val = 0 then min c3 (d ⟨k, by omega⟩ - (S.val : ℤ)) else c3
  let c5 := bfWinCand k r S act inW false d v c4
  bfWinCand k r S act inW true d v c5

def bfDist (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool) :
    ℕ → Fin (k + 1) → ℤ
  | 0 => fun _ => 0
  | t + 1 => bfStepZ k r S act inW (bfDist k r S act inW t)

def fullOK (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool) : Bool :=
  decide (∀ a : Bool × Fin k, k ≤ reachN r a.1 + 1 → act a = true →
    S.val ≤ if inW a then 2 else 1)

def bfOK (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool) : Bool :=
  fullOK k r S act inW && decide (bfDist k r S act inW (k + 1) = bfDist k r S act inW k)

def bfP (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool) (i : Fin k) : Bool :=
  decide (bfDist k r S act inW k ⟨i.val + 1, by omega⟩ = bfDist k r S act inW k ⟨i.val, by omega⟩)

def BFEdge (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (u v : Fin (k + 1)) (w : ℤ) : Prop :=
  (u.val + 1 = v.val ∧ w = 1) ∨
  (v.val + 1 = u.val ∧ w = 0) ∨
  (u.val = 0 ∧ v.val = k ∧ w = (S.val : ℤ)) ∨
  (u.val = k ∧ v.val = 0 ∧ w = -(S.val : ℤ)) ∨
  (∃ (col_b : Bool) (hL : reachN r col_b + 1 < k) (hv : 0 < v.val),
    let L := reachN r col_b + 1
    let ui : Fin k := if hlv : L ≤ v.val then ⟨v.val - L, by omega⟩ else ⟨v.val + k - L, by omega⟩
    act (col_b, ui) = true ∧ u.val = ui.val ∧
      w = (if inW (col_b, ui) then 2 else 1) - (if L ≤ v.val then 0 else (S.val : ℤ)))

theorem bfWinCand_le_self (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (col_b : Bool) (d : Fin (k + 1) → ℤ) (v : Fin (k + 1)) (cur : ℤ) :
    bfWinCand k r S act inW col_b d v cur ≤ cur := by
  dsimp only [bfWinCand]
  split_ifs <;> first | exact le_rfl | exact min_le_left _ _

theorem bfStepZ_le_self (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (d : Fin (k + 1) → ℤ) (v : Fin (k + 1)) :
    bfStepZ k r S act inW d v ≤ d v := by
  set c0 := d v
  set c1 := if h : 0 < v.val then min c0 (d ⟨v.val - 1, by omega⟩ + 1) else c0
  set c2 := if h : v.val < k then min c1 (d ⟨v.val + 1, by omega⟩) else c1
  set c3 := if v.val = k then min c2 (d ⟨0, by omega⟩ + (S.val : ℤ)) else c2
  set c4 := if v.val = 0 then min c3 (d ⟨k, by omega⟩ - (S.val : ℤ)) else c3
  set c5 := bfWinCand k r S act inW false d v c4
  change bfWinCand k r S act inW true d v c5 ≤ c0
  have h5 : bfWinCand k r S act inW true d v c5 ≤ c5 := bfWinCand_le_self ..
  have h4 : c5 ≤ c4 := bfWinCand_le_self ..
  have h3 : c4 ≤ c3 := by dsimp only [c4]; split_ifs; exact min_le_left _ _; exact le_rfl
  have h2 : c3 ≤ c2 := by dsimp only [c3]; split_ifs; exact min_le_left _ _; exact le_rfl
  have h1 : c2 ≤ c1 := by dsimp only [c2]; split_ifs; exact min_le_left _ _; exact le_rfl
  have h0 : c1 ≤ c0 := by dsimp only [c1]; split_ifs; exact min_le_left _ _; exact le_rfl
  omega

theorem bfStepZ_le_edge (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (d : Fin (k + 1) → ℤ) (u v : Fin (k + 1)) (w : ℤ)
    (he : BFEdge k r S act inW u v w) :
    bfStepZ k r S act inW d v ≤ d u + w := by
  set c0 := d v
  set c1 := if h : 0 < v.val then min c0 (d ⟨v.val - 1, by omega⟩ + 1) else c0
  set c2 := if h : v.val < k then min c1 (d ⟨v.val + 1, by omega⟩) else c1
  set c3 := if v.val = k then min c2 (d ⟨0, by omega⟩ + (S.val : ℤ)) else c2
  set c4 := if v.val = 0 then min c3 (d ⟨k, by omega⟩ - (S.val : ℤ)) else c3
  set c5 := bfWinCand k r S act inW false d v c4
  change bfWinCand k r S act inW true d v c5 ≤ d u + w
  have hl5 : bfWinCand k r S act inW true d v c5 ≤ c5 := bfWinCand_le_self ..
  have hl4 : c5 ≤ c4 := bfWinCand_le_self ..
  have hl3 : c4 ≤ c3 := by dsimp only [c4]; split_ifs; exact min_le_left _ _; exact le_rfl
  have hl2 : c3 ≤ c2 := by dsimp only [c3]; split_ifs; exact min_le_left _ _; exact le_rfl
  have hl1 : c2 ≤ c1 := by dsimp only [c2]; split_ifs; exact min_le_left _ _; exact le_rfl
  rcases he with ⟨hu, rfl⟩ | ⟨hv, rfl⟩ | ⟨hu, hv, rfl⟩ | ⟨hu, hv, rfl⟩ | ⟨col_b, hL, hv0, hact, hu, rfl⟩
  · have hpos : 0 < v.val := by omega
    have hfin : (⟨v.val - 1, by omega⟩ : Fin (k + 1)) = u := Fin.ext (by simp; omega)
    have : c1 ≤ d u + 1 := by dsimp only [c1]; rw [dif_pos hpos, hfin]; exact min_le_right _ _
    omega
  · have hlt : v.val < k := by omega
    have hfin : (⟨v.val + 1, by omega⟩ : Fin (k + 1)) = u := Fin.ext (by simp; omega)
    have : c2 ≤ d u + 0 := by dsimp only [c2]; rw [dif_pos hlt, hfin, add_zero]; exact min_le_right _ _
    omega
  · have hfin : (⟨0, by omega⟩ : Fin (k + 1)) = u := Fin.ext hu.symm
    have : c3 ≤ d u + (S.val : ℤ) := by dsimp only [c3]; rw [if_pos hv, hfin]; exact min_le_right _ _
    omega
  · have hfin : (⟨k, by omega⟩ : Fin (k + 1)) = u := Fin.ext hu.symm
    have : c4 ≤ d u + -(S.val : ℤ) := by
      dsimp only [c4]; rw [if_pos hv, hfin, ← sub_eq_add_neg]; exact min_le_right _ _
    omega
  · cases col_b
    · set ui : Fin k := if hlv : reachN r false + 1 ≤ v.val then
        ⟨v.val - (reachN r false + 1), by omega⟩ else ⟨v.val + k - (reachN r false + 1), by omega⟩
      have hc5 : c5 ≤ d u + ((if inW (false, ui) = true then (2 : ℤ) else 1) -
          if reachN r false + 1 ≤ v.val then 0 else (S.val : ℤ)) := by
        dsimp only [c5]; unfold bfWinCand
        rw [dif_pos hL, dif_pos hv0, if_pos hact]
        have hfin : (⟨ui.val, by omega⟩ : Fin (k + 1)) = u := Fin.ext hu.symm
        rw [hfin]
        exact min_le_right _ _
      omega
    · set ui : Fin k := if hlv : reachN r true + 1 ≤ v.val then
        ⟨v.val - (reachN r true + 1), by omega⟩ else ⟨v.val + k - (reachN r true + 1), by omega⟩
      have hc6 : bfWinCand k r S act inW true d v c5 ≤ d u + ((if inW (true, ui) = true then (2 : ℤ) else 1) -
          if reachN r true + 1 ≤ v.val then 0 else (S.val : ℤ)) := by
        unfold bfWinCand
        rw [dif_pos hL, dif_pos hv0, if_pos hact]
        have hfin : (⟨ui.val, by omega⟩ : Fin (k + 1)) = u := Fin.ext hu.symm
        rw [hfin]
        exact min_le_right _ _
      exact hc6

theorem bfWinCand_eq_or_edge (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (col_b : Bool) (d : Fin (k + 1) → ℤ) (v : Fin (k + 1)) (cur : ℤ) :
    bfWinCand k r S act inW col_b d v cur = cur ∨
      ∃ u w, BFEdge k r S act inW u v w ∧ bfWinCand k r S act inW col_b d v cur = d u + w := by
  unfold bfWinCand
  by_cases hL : reachN r col_b + 1 < k
  · rw [dif_pos hL]
    by_cases hv : 0 < v.val
    · rw [dif_pos hv]
      set ui : Fin k := if hlv : reachN r col_b + 1 ≤ v.val then
        ⟨v.val - (reachN r col_b + 1), by omega⟩ else ⟨v.val + k - (reachN r col_b + 1), by omega⟩
      by_cases hact : act (col_b, ui) = true
      · rw [if_pos hact]
        rcases min_choice cur (d ⟨ui.val, by omega⟩ + ((if inW (col_b, ui) = true then (2 : ℤ) else 1) -
            if reachN r col_b + 1 ≤ v.val then 0 else (S.val : ℤ))) with h | h
        · left; exact h
        · right
          refine ⟨⟨ui.val, by omega⟩, _, Or.inr (Or.inr (Or.inr (Or.inr ⟨col_b, hL, hv, hact, rfl, rfl⟩))), h⟩
      · left; rw [if_neg hact]
    · left; rw [dif_neg hv]
  · left; rw [dif_neg hL]

theorem bfStepZ_eq_or_edge (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (d : Fin (k + 1) → ℤ) (v : Fin (k + 1)) :
    bfStepZ k r S act inW d v = d v ∨
      ∃ u w, BFEdge k r S act inW u v w ∧ bfStepZ k r S act inW d v = d u + w := by
  set c0 := d v
  set c1 := if h : 0 < v.val then min c0 (d ⟨v.val - 1, by omega⟩ + 1) else c0
  set c2 := if h : v.val < k then min c1 (d ⟨v.val + 1, by omega⟩) else c1
  set c3 := if v.val = k then min c2 (d ⟨0, by omega⟩ + (S.val : ℤ)) else c2
  set c4 := if v.val = 0 then min c3 (d ⟨k, by omega⟩ - (S.val : ℤ)) else c3
  set c5 := bfWinCand k r S act inW false d v c4
  change bfWinCand k r S act inW true d v c5 = c0 ∨
    ∃ u w, BFEdge k r S act inW u v w ∧ bfWinCand k r S act inW true d v c5 = d u + w
  rcases bfWinCand_eq_or_edge k r S act inW true d v c5 with h6 | ⟨u, w, he, h6⟩
  · rw [h6]
    rcases bfWinCand_eq_or_edge k r S act inW false d v c4 with h5 | ⟨u, w, he, h5⟩
    · have h5' : c5 = c4 := h5
      rw [h5']
      have h4 : c4 = c3 ∨ ∃ u w, BFEdge k r S act inW u v w ∧ c4 = d u + w := by
        dsimp only [c4]
        by_cases hv : v.val = 0
        · rw [if_pos hv]
          rcases min_choice c3 (d ⟨k, by omega⟩ - (S.val : ℤ)) with hm | hm
          · left; exact hm
          · right; refine ⟨⟨k, by omega⟩, -(S.val : ℤ), Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hv, rfl⟩))), ?_⟩
            rw [hm, sub_eq_add_neg]
        · left; rw [if_neg hv]
      rcases h4 with h4 | ⟨u, w, he, h4⟩
      · rw [h4]
        have h3 : c3 = c2 ∨ ∃ u w, BFEdge k r S act inW u v w ∧ c3 = d u + w := by
          dsimp only [c3]
          by_cases hv : v.val = k
          · rw [if_pos hv]
            rcases min_choice c2 (d ⟨0, by omega⟩ + (S.val : ℤ)) with hm | hm
            · left; exact hm
            · right; exact ⟨⟨0, by omega⟩, (S.val : ℤ), Or.inr (Or.inr (Or.inl ⟨rfl, hv, rfl⟩)), hm⟩
          · left; rw [if_neg hv]
        rcases h3 with h3 | ⟨u, w, he, h3⟩
        · rw [h3]
          have h2 : c2 = c1 ∨ ∃ u w, BFEdge k r S act inW u v w ∧ c2 = d u + w := by
            dsimp only [c2]
            by_cases hv : v.val < k
            · rw [dif_pos hv]
              rcases min_choice c1 (d ⟨v.val + 1, by omega⟩) with hm | hm
              · left; exact hm
              · right; refine ⟨⟨v.val + 1, by omega⟩, 0, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
                rw [hm, add_zero]
            · left; rw [dif_neg hv]
          rcases h2 with h2 | ⟨u, w, he, h2⟩
          · rw [h2]
            dsimp only [c1]
            by_cases hv : 0 < v.val
            · rw [dif_pos hv]
              rcases min_choice c0 (d ⟨v.val - 1, by omega⟩ + 1) with hm | hm
              · left; exact hm
              · right; exact ⟨⟨v.val - 1, by omega⟩, 1, Or.inl ⟨by simp; omega, rfl⟩, hm⟩
            · left; rw [dif_neg hv]
          · right; exact ⟨u, w, he, h2⟩
        · right; exact ⟨u, w, he, h3⟩
      · right; exact ⟨u, w, he, h4⟩
    · right; exact ⟨u, w, he, h5⟩
  · right; exact ⟨u, w, he, h6⟩

theorem bfEdge_w_bounds {k r : ℕ} {S : Fin (k + 1)} {act inW : Bool × Fin k → Bool}
    {u v : Fin (k + 1)} {w : ℤ} (he : BFEdge k r S act inW u v w) :
    -(k : ℤ) ≤ w ∧ w ≤ (k : ℤ) + 2 := by
  have hSk : (S.val : ℤ) ≤ (k : ℤ) := by omega
  rcases he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩
  · omega
  · omega
  · omega
  · omega
  · split_ifs <;> omega

theorem bfDist_bounds (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool) :
    ∀ t v, -(t * (k : ℤ)) ≤ bfDist k r S act inW t v ∧ bfDist k r S act inW t v ≤ 0 := by
  intro t
  induction t with
  | zero => intro v; simp [bfDist]
  | succ t ih =>
    intro v
    have hle0 : bfDist k r S act inW (t + 1) v ≤ 0 :=
      le_trans (bfStepZ_le_self ..) (ih v).2
    refine ⟨?_, hle0⟩
    rcases bfStepZ_eq_or_edge k r S act inW (bfDist k r S act inW t) v with h | ⟨u, w, he, h⟩
    · change bfStepZ k r S act inW (bfDist k r S act inW t) v ≥ _
      rw [h]; have := (ih v).1; push_cast; nlinarith
    · change bfStepZ k r S act inW (bfDist k r S act inW t) v ≥ _
      rw [h]
      have hu := (ih u).1
      have hw := (bfEdge_w_bounds he).1
      push_cast; nlinarith

theorem bfDist_anti (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool) (t : ℕ)
    (v : Fin (k + 1)) :
    bfDist k r S act inW (t + 1) v ≤ bfDist k r S act inW t v :=
  bfStepZ_le_self ..

def IsWalk (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (len : ℕ) (seq : Fin (len + 1) → Fin (k + 1)) (ws : Fin len → ℤ) : Prop :=
  ∀ i : Fin len, BFEdge k r S act inW (seq i.castSucc) (seq i.succ) (ws i)

theorem bfDist_walk (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool) :
    ∀ t v, ∃ (len : ℕ) (seq : Fin (len + 1) → Fin (k + 1)) (ws : Fin len → ℤ),
      len ≤ t ∧ seq (Fin.last len) = v ∧ IsWalk k r S act inW len seq ws ∧
      bfDist k r S act inW t v = ∑ i : Fin len, ws i := by
  intro t
  induction t with
  | zero =>
    intro v
    refine ⟨0, fun _ => v, Fin.elim0, le_rfl, rfl, fun i => Fin.elim0 i, by simp [bfDist]⟩
  | succ t ih =>
    intro v
    rcases bfStepZ_eq_or_edge k r S act inW (bfDist k r S act inW t) v with h | ⟨u, w, he, h⟩
    · obtain ⟨len, seq, ws, hlen, hend, hwk, hsum⟩ := ih v
      exact ⟨len, seq, ws, by omega, hend, hwk, by change bfStepZ .. = _; rw [h, hsum]⟩
    · obtain ⟨len, seq, ws, hlen, hend, hwk, hsum⟩ := ih u
      let seq' : Fin (len + 1 + 1) → Fin (k + 1) :=
        Fin.snoc seq v
      let ws' : Fin (len + 1) → ℤ :=
        Fin.snoc ws w
      refine ⟨len + 1, seq', ws', by omega, by simp [seq'], ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [seq', ws', Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hend]
          exact he
        · simp only [seq', ws', Fin.snoc_castSucc, Fin.succ_castSucc]
          exact hwk j
      · change bfStepZ .. = _
        rw [h, hsum, Fin.sum_univ_castSucc]
        simp [ws']

theorem bfDist_le_walk (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool) :
    ∀ t (len : ℕ) (seq : Fin (len + 1) → Fin (k + 1)) (ws : Fin len → ℤ),
      len ≤ t → IsWalk k r S act inW len seq ws →
      bfDist k r S act inW t (seq (Fin.last len)) ≤ ∑ i : Fin len, ws i := by
  intro t
  induction t with
  | zero =>
    intro len seq ws hlen _
    have hl0 : len = 0 := by omega
    subst hl0
    change (0 : ℤ) ≤ ∑ i : Fin 0, ws i
    rw [Fin.sum_univ_zero]
  | succ t ih =>
    intro len seq ws hlen hwk
    cases len with
    | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact (bfDist_bounds k r S act inW (t + 1) _).2
    | succ len =>
      have h1 := bfStepZ_le_edge k r S act inW (bfDist k r S act inW t)
        (seq (Fin.last len).castSucc) (seq (Fin.last (len + 1))) (ws (Fin.last len))
        (by simpa [Fin.succ_last] using hwk (Fin.last len))
      have h2 := ih len (fun i => seq i.castSucc) (fun i => ws i.castSucc) (by omega)
        (fun i => by
          have h := hwk i.castSucc
          rw [Fin.succ_castSucc] at h
          exact h)
      rw [Fin.sum_univ_castSucc]
      change bfStepZ .. ≤ _
      omega

theorem bf_walk_telescope {k r : ℕ} {S : Fin (k + 1)} {act inW : Bool × Fin k → Bool}
    (z : Fin (k + 1) → ℤ) (hz : ∀ u v w, BFEdge k r S act inW u v w → z v - z u ≤ w)
    {len : ℕ} {seq : Fin (len + 1) → Fin (k + 1)} {ws : Fin len → ℤ}
    (hwk : IsWalk k r S act inW len seq ws) (a b : ℕ) (hab : a ≤ b) (hbl : b ≤ len) :
    z (seq ⟨b, by omega⟩) - z (seq ⟨a, by omega⟩) ≤
      ∑ i ∈ (Finset.univ : Finset (Fin len)).filter (fun i => a ≤ i.val ∧ i.val < b), ws i := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    simp
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq
      have hemp : (Finset.univ : Finset (Fin len)).filter (fun i => b + 1 ≤ i.val ∧ i.val < b + 1) = ∅ := by
        ext i; simp
      rw [hemp, Finset.sum_empty]
      exact le_of_eq (sub_self _)
    · have hab' : a ≤ b := by omega
      have hlt : b < len := by omega
      have hfilt : (Finset.univ : Finset (Fin len)).filter (fun i => a ≤ i.val ∧ i.val < b + 1) =
          insert ⟨b, hlt⟩ ((Finset.univ : Finset (Fin len)).filter (fun i => a ≤ i.val ∧ i.val < b)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hib : i.val = b
          · left; exact Fin.ext hib
          · right; exact ⟨h1, by omega⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hab', by simp⟩
          · exact ⟨h1, by omega⟩
      rw [hfilt, Finset.sum_insert (by simp)]
      have hstep := hz _ _ _ (hwk ⟨b, hlt⟩)
      have hih := ih hab' (by omega)
      have hs1 : (⟨b, hlt⟩ : Fin len).castSucc = ⟨b, by omega⟩ := rfl
      have hs2 : (⟨b, hlt⟩ : Fin len).succ = ⟨b + 1, by omega⟩ := rfl
      rw [hs1, hs2] at hstep
      omega

theorem bf_short_walk {k r : ℕ} {S : Fin (k + 1)} {act inW : Bool × Fin k → Bool}
    (z : Fin (k + 1) → ℤ) (hz : ∀ u v w, BFEdge k r S act inW u v w → z v - z u ≤ w) :
    ∀ (len : ℕ) (seq : Fin (len + 1) → Fin (k + 1)) (ws : Fin len → ℤ),
      IsWalk k r S act inW len seq ws →
      ∃ (len' : ℕ) (seq' : Fin (len' + 1) → Fin (k + 1)) (ws' : Fin len' → ℤ),
        len' ≤ k ∧ seq' (Fin.last len') = seq (Fin.last len) ∧
        IsWalk k r S act inW len' seq' ws' ∧ ∑ i : Fin len', ws' i ≤ ∑ i : Fin len, ws i := by
  intro len
  induction len using Nat.strong_induction_on with
  | ind len ih =>
    intro seq ws hwk
    by_cases hle : len ≤ k
    · exact ⟨len, seq, ws, hle, rfl, hwk, le_rfl⟩
    · have hcard : Fintype.card (Fin (k + 1)) < Fintype.card (Fin (len + 1)) := by simp; omega
      obtain ⟨p, q, hpq, hseq⟩ := Fintype.exists_ne_map_eq_of_card_lt seq hcard
      wlog hlt : p < q generalizing p q
      · exact this q p hpq.symm hseq.symm (lt_of_le_of_ne (not_lt.1 hlt) hpq.symm)
      have hpqv : p.val < q.val := hlt
      let d := q.val - p.val
      have hd : 0 < d := by omega
      have hlen' : len - d < len := by omega
      let seq1 : Fin (len - d + 1) → Fin (k + 1) := fun i =>
        if hi : i.val < p.val then seq ⟨i.val, by omega⟩ else seq ⟨i.val + d, by omega⟩
      let ws1 : Fin (len - d) → ℤ := fun i =>
        if hi : i.val < p.val then ws ⟨i.val, by omega⟩ else ws ⟨i.val + d, by omega⟩
      have hwk1 : IsWalk k r S act inW (len - d) seq1 ws1 := by
        intro i
        by_cases hi : i.val < p.val
        · by_cases hi1 : i.val + 1 < p.val
          · simp only [seq1, ws1, Fin.val_castSucc, Fin.val_succ, dif_pos hi, dif_pos hi1]
            exact hwk ⟨i.val, by omega⟩
          · have heqp : i.val + 1 = p.val := by omega
            simp only [seq1, ws1, Fin.val_castSucc, Fin.val_succ, dif_pos hi, dif_neg hi1]
            have hqeq : (⟨i.val + 1 + d, by omega⟩ : Fin (len + 1)) = q := Fin.ext (by simp [d]; omega)
            have hpeq : (⟨i.val + 1, by omega⟩ : Fin (len + 1)) = p := Fin.ext (by simp [heqp])
            have hsq : seq ⟨i.val + 1 + d, by omega⟩ = seq ⟨i.val + 1, by omega⟩ :=
              (congrArg seq hqeq).trans (hseq.symm.trans (congrArg seq hpeq.symm))
            rw [hsq]
            exact hwk ⟨i.val, by omega⟩
        · have hi1 : ¬ (i.val + 1 < p.val) := by omega
          simp only [seq1, ws1, Fin.val_castSucc, Fin.val_succ, dif_neg hi, dif_neg hi1]
          have hs : (⟨i.val + 1 + d, by omega⟩ : Fin (len + 1)) = (⟨i.val + d, by omega⟩ : Fin len).succ :=
            Fin.ext (by simp; omega)
          rw [hs]
          exact hwk ⟨i.val + d, by omega⟩
      have hend1 : seq1 (Fin.last (len - d)) = seq (Fin.last len) := by
        have hnot : ¬ (len - d < p.val) := by omega
        simp only [seq1, Fin.val_last, dif_neg hnot]
        congr 1; apply Fin.ext; simp; omega
      have hcyc : 0 ≤ ∑ i ∈ (Finset.univ : Finset (Fin len)).filter (fun i => p.val ≤ i.val ∧ i.val < q.val),
          ws i := by
        have ht := bf_walk_telescope z hz hwk p.val q.val (by omega) (by omega)
        have hp' : (⟨p.val, by omega⟩ : Fin (len + 1)) = p := Fin.ext rfl
        have hq' : (⟨q.val, by omega⟩ : Fin (len + 1)) = q := Fin.ext rfl
        rw [hp', hq', hseq, sub_self] at ht
        exact ht
      have hsum1 : ∑ i : Fin (len - d), ws1 i +
          ∑ i ∈ (Finset.univ : Finset (Fin len)).filter (fun i => p.val ≤ i.val ∧ i.val < q.val), ws i =
          ∑ i : Fin len, ws i := by
        let A := (Finset.univ : Finset (Fin len)).filter (fun i => i.val < p.val)
        let B := (Finset.univ : Finset (Fin len)).filter (fun i => p.val ≤ i.val ∧ i.val < q.val)
        let C := (Finset.univ : Finset (Fin len)).filter (fun i => q.val ≤ i.val)
        have hsplit : ∑ i : Fin len, ws i = (∑ i ∈ A, ws i) + (∑ i ∈ B, ws i) + (∑ i ∈ C, ws i) := by
          have h1 : (Finset.univ : Finset (Fin len)) = (A ∪ B) ∪ C := by
            ext i; simp only [A, B, C, Finset.mem_univ, Finset.mem_union, Finset.mem_filter,
              true_and, true_iff]; omega
          have hd1 : Disjoint A B := Finset.disjoint_filter.2 (fun _ _ h1 h2 => by omega)
          have hd2 : Disjoint (A ∪ B) C := by
            rw [Finset.disjoint_union_left]
            exact ⟨Finset.disjoint_filter.2 (fun _ _ h1 h2 => by omega),
              Finset.disjoint_filter.2 (fun _ _ h1 h2 => by omega)⟩
          conv_lhs => rw [h1, Finset.sum_union hd2, Finset.sum_union hd1]
        let A1 := (Finset.univ : Finset (Fin (len - d))).filter (fun i => i.val < p.val)
        let C1 := (Finset.univ : Finset (Fin (len - d))).filter (fun i => ¬ i.val < p.val)
        have hsplit1 : ∑ i : Fin (len - d), ws1 i = (∑ i ∈ A1, ws1 i) + (∑ i ∈ C1, ws1 i) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin (len - d) => i.val < p.val)]
        have hAA : ∑ i ∈ A1, ws1 i = ∑ i ∈ A, ws i := by
          refine Finset.sum_bij (fun i hi => ⟨i.val, by omega⟩) ?_ ?_ ?_ ?_
          · intro i hi; simp only [A1, A, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi
          · intro i1 _ i2 _ heq; apply Fin.ext; simpa using congrArg Fin.val heq
          · intro j hj
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact ⟨⟨j.val, by omega⟩, by simp [A1, hj], Fin.ext rfl⟩
          · intro i hi
            simp only [A1, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            simp [ws1, hi]
        have hCC : ∑ i ∈ C1, ws1 i = ∑ i ∈ C, ws i := by
          refine Finset.sum_bij (fun i hi => ⟨i.val + d, by omega⟩) ?_ ?_ ?_ ?_
          · intro i hi; simp only [C1, C, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; omega
          · intro i1 _ i2 _ heq; apply Fin.ext; have := congrArg Fin.val heq; simp at this; omega
          · intro j hj
            simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact ⟨⟨j.val - d, by omega⟩, by simp only [C1, Finset.mem_filter, Finset.mem_univ, true_and]; omega,
              Fin.ext (by simp; omega)⟩
          · intro i hi
            simp only [C1, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            simp [ws1, hi]
        rw [hsplit, hsplit1, hAA, hCC]; ring
      obtain ⟨len', seq', ws', hle', hend', hwk', hle_sum⟩ := ih (len - d) hlen' seq1 ws1 hwk1
      exact ⟨len', seq', ws', hle', by rw [hend', hend1], hwk', by omega⟩

theorem bfDist_stable_of_pot {k r : ℕ} {S : Fin (k + 1)} {act inW : Bool × Fin k → Bool}
    (z : Fin (k + 1) → ℤ) (hz : ∀ u v w, BFEdge k r S act inW u v w → z v - z u ≤ w) :
    bfDist k r S act inW (k + 1) = bfDist k r S act inW k := by
  funext v
  apply le_antisymm (bfDist_anti k r S act inW k v)
  obtain ⟨len, seq, ws, _, hend, hwk, hsum⟩ := bfDist_walk k r S act inW (k + 1) v
  obtain ⟨len', seq', ws', hle', hend', hwk', hle_sum⟩ := bf_short_walk z hz len seq ws hwk
  have h1 := bfDist_le_walk k r S act inW k len' seq' ws' hle' hwk'
  rw [hend', hend] at h1
  omega

theorem scopeN_full {k r : ℕ} (hk : 0 < k) (a : Bool × Fin k) (hL : k ≤ reachN r a.1 + 1) :
    scopeN k r a = Finset.univ := by
  ext i
  simp only [scopeN, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  let d : ℕ := (i.val + k - a.2.val) % k
  have hd : d < reachN r a.1 + 1 := lt_of_lt_of_le (Nat.mod_lt _ hk) hL
  refine ⟨⟨d, hd⟩, ?_⟩
  have hmod : (a.2.val + d) % k = (a.2.val + (i.val + k - a.2.val)) % k := by
    dsimp only [d]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [hmod]
  have hsum : a.2.val + (i.val + k - a.2.val) = i.val + k := by omega
  rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem scopeN_nowrap {k r : ℕ} (a : Bool × Fin k) (hL : reachN r a.1 + 1 < k)
    (hnw : a.2.val + (reachN r a.1 + 1) ≤ k) (i : Fin k) :
    i ∈ scopeN k r a ↔ a.2.val ≤ i.val ∧ i.val < a.2.val + (reachN r a.1 + 1) := by
  simp only [scopeN, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, hd⟩
    have hlt : a.2.val + d.val < k := by omega
    rw [Nat.mod_eq_of_lt hlt] at hd
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨i.val - a.2.val, by omega⟩, ?_⟩
    have hsum : a.2.val + (i.val - a.2.val) = i.val := by omega
    rw [hsum, Nat.mod_eq_of_lt i.isLt]

theorem scopeN_wrap {k r : ℕ} (a : Bool × Fin k) (hL : reachN r a.1 + 1 < k)
    (hwr : k < a.2.val + (reachN r a.1 + 1)) (i : Fin k) :
    i ∈ scopeN k r a ↔ a.2.val ≤ i.val ∨ i.val < a.2.val + (reachN r a.1 + 1) - k := by
  simp only [scopeN, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, hd⟩
    by_cases hlt : a.2.val + d.val < k
    · rw [Nat.mod_eq_of_lt hlt] at hd; left; omega
    · have hsub : (a.2.val + d.val) % k = a.2.val + d.val - k := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at hd; right; omega
  · rintro (h1 | h2)
    · refine ⟨⟨i.val - a.2.val, by omega⟩, ?_⟩
      have hsum : a.2.val + (i.val - a.2.val) = i.val := by omega
      rw [hsum, Nat.mod_eq_of_lt i.isLt]
    · refine ⟨⟨i.val + k - a.2.val, by omega⟩, ?_⟩
      have hsum : a.2.val + (i.val + k - a.2.val) = i.val + k := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

theorem psum_card_sub {k : ℕ} (P : Finset (Fin k)) (a b : ℕ) (hab : a ≤ b) (hbk : b ≤ k) :
    ((Finset.univ.filter (fun i : Fin k => i.val < b ∧ i ∉ P)).card : ℤ) -
      ((Finset.univ.filter (fun i : Fin k => i.val < a ∧ i ∉ P)).card : ℤ) =
    ((Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < b ∧ i ∉ P)).card : ℤ) := by
  have hsub : Finset.univ.filter (fun i : Fin k => i.val < a ∧ i ∉ P) ⊆
      Finset.univ.filter (fun i : Fin k => i.val < b ∧ i ∉ P) := by
    intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact ⟨by omega, hi.2⟩
  have hsdiff : Finset.univ.filter (fun i : Fin k => i.val < b ∧ i ∉ P) \
      Finset.univ.filter (fun i : Fin k => i.val < a ∧ i ∉ P) =
      Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < b ∧ i ∉ P) := by
    ext i; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; refine ⟨?_, h1, h2⟩; by_contra hlt; exact h3 ⟨by omega, h2⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h2, h3⟩, fun h => by omega⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [hsdiff] at hcard
  omega

theorem bf_sound {k r : ℕ} (hk : 0 < k) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (hok : bfOK k r S act inW = true) :
    let P := Finset.univ.filter (fun i : Fin k => bfP k r S act inW i = true)
    P.card = k - S.val ∧
    ∀ a : Bool × Fin k, act a = true → (scopeN k r a \ P).card ≤ if inW a then 2 else 1 := by
  intro P
  unfold bfOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hfull, hfix⟩ := hok
  let d := bfDist k r S act inW k
  let z : Fin (k + 1) → ℤ := fun t => d t - d ⟨0, by omega⟩
  have hz_edge : ∀ u v w, BFEdge k r S act inW u v w → z v - z u ≤ w := by
    intro u v w he
    have h1 := bfStepZ_le_edge k r S act inW d u v w he
    have h2 : bfStepZ k r S act inW d v = d v := congrFun hfix v
    rw [h2] at h1
    dsimp only [z]
    omega
  have hz0 : z ⟨0, by omega⟩ = 0 := by simp [z]
  have hzk : z ⟨k, by omega⟩ = (S.val : ℤ) := by
    have h1 := hz_edge ⟨0, by omega⟩ ⟨k, by omega⟩ (S.val : ℤ) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
    have h2 := hz_edge ⟨k, by omega⟩ ⟨0, by omega⟩ (-(S.val : ℤ)) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
    rw [hz0] at h1 h2
    omega
  have hz_step : ∀ i : Fin k, z ⟨i.val + 1, by omega⟩ - z ⟨i.val, by omega⟩ =
      if i ∈ P then 0 else 1 := by
    intro i
    have h1 := hz_edge ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ 1 (Or.inl ⟨rfl, rfl⟩)
    have h2 := hz_edge ⟨i.val + 1, by omega⟩ ⟨i.val, by omega⟩ 0 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    by_cases hi : i ∈ P
    · simp only [hi, ite_true]
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, bfP, decide_eq_true_eq] at hi
      dsimp only [z, d]; rw [hi]; omega
    · simp only [hi, ite_false]
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, bfP, decide_eq_true_eq] at hi
      dsimp only [z, d] at h1 h2 ⊢
      omega
  have hz_eq : ∀ t : ℕ, (ht : t ≤ k) →
      z ⟨t, by omega⟩ = ((Finset.univ.filter (fun i : Fin k => i.val < t ∧ i ∉ P)).card : ℤ) := by
    intro t
    induction t with
    | zero => intro _; simpa using hz0
    | succ t ih =>
      intro ht
      have hst := hz_step ⟨t, by omega⟩
      have hih := ih (by omega)
      have hsub := psum_card_sub P t (t + 1) (by omega) ht
      have h1 : (Finset.univ.filter (fun i : Fin k => t ≤ i.val ∧ i.val < t + 1 ∧ i ∉ P)).card =
          if (⟨t, by omega⟩ : Fin k) ∈ P then 0 else 1 := by
        by_cases hp : (⟨t, by omega⟩ : Fin k) ∈ P
        · simp only [hp, ite_true, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro i _ h; have heq : i = ⟨t, by omega⟩ := Fin.ext (by simp; omega); exact h.2.2 (heq ▸ hp)
        · simp only [hp, ite_false]
          have hsing : Finset.univ.filter (fun i : Fin k => t ≤ i.val ∧ i.val < t + 1 ∧ i ∉ P) =
              {⟨t, by omega⟩} := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro ⟨h1, h2, _⟩; exact Fin.ext (by simp; omega)
            · rintro rfl; exact ⟨le_rfl, Nat.lt_succ_self t, hp⟩
          rw [hsing, Finset.card_singleton]
      rw [h1] at hsub
      by_cases hp : (⟨t, by omega⟩ : Fin k) ∈ P <;> simp only [hp, ite_true, ite_false] at hst hsub <;> omega
  have hcardU : (Finset.univ \ P).card = S.val := by
    have h := hz_eq k le_rfl
    rw [hzk] at h
    have heq : Finset.univ.filter (fun i : Fin k => i.val < k ∧ i ∉ P) = Finset.univ \ P := by
      ext i; simp
    rw [heq] at h
    omega
  have hPcard : P.card = k - S.val := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  refine ⟨hPcard, ?_⟩
  intro a ha
  let L := reachN r a.1 + 1
  by_cases hL : k ≤ L
  · rw [scopeN_full hk a hL, hcardU]
    simp only [fullOK, decide_eq_true_eq] at hfull
    exact hfull a hL ha
  · have hL' : L < k := by omega
    by_cases hnw : a.2.val + L ≤ k
    · have hsc : scopeN k r a \ P =
          Finset.univ.filter (fun i : Fin k => a.2.val ≤ i.val ∧ i.val < a.2.val + L ∧ i ∉ P) := by
        ext i; simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
          scopeN_nowrap a hL' hnw]; tauto
      have hcard : ((scopeN k r a \ P).card : ℤ) =
          z ⟨a.2.val + L, by omega⟩ - z ⟨a.2.val, by omega⟩ := by
        rw [hsc, hz_eq (a.2.val + L) hnw, hz_eq a.2.val (by omega), psum_card_sub P _ _ (by omega) hnw]
      have hpos : 0 < a.2.val + L := by dsimp only [L]; omega
      have hleL : reachN r a.1 + 1 ≤ a.2.val + L := by dsimp only [L]; omega
      have hedge : BFEdge k r S act inW ⟨a.2.val, by omega⟩ ⟨a.2.val + L, by omega⟩
          ((if inW a then 2 else 1) - 0) := by
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a.1, hL', hpos, ?_, ?_, ?_⟩)))
        · rw [dif_pos hleL]
          have : (⟨a.2.val + L - (reachN r a.1 + 1), by dsimp only [L]; omega⟩ : Fin k) = a.2 :=
            Fin.ext (by dsimp only [L]; omega)
          rw [this]; exact ha
        · rw [dif_pos hleL]; dsimp only [L]; omega
        · rw [dif_pos hleL, if_pos hleL]
          have : (⟨a.2.val + L - (reachN r a.1 + 1), by dsimp only [L]; omega⟩ : Fin k) = a.2 :=
            Fin.ext (by dsimp only [L]; omega)
          rw [this]
      have hle := hz_edge _ _ _ hedge
      rw [← hcard, sub_zero] at hle
      by_cases hiw : inW a = true <;> simp [hiw] at hle ⊢ <;> omega
    · have hwr : k < a.2.val + L := by omega
      let q := a.2.val + L - k
      have hqpos : 0 < q := by omega
      have hqlt : q < L := by omega
      have hsc : scopeN k r a \ P =
          (Finset.univ.filter (fun i : Fin k => i.val < q ∧ i ∉ P)) ∪
          (Finset.univ.filter (fun i : Fin k => a.2.val ≤ i.val ∧ i.val < k ∧ i ∉ P)) := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          scopeN_wrap a hL' hwr, i.isLt, true_and]
        tauto
      have hdisj : Disjoint (Finset.univ.filter (fun i : Fin k => i.val < q ∧ i ∉ P))
          (Finset.univ.filter (fun i : Fin k => a.2.val ≤ i.val ∧ i.val < k ∧ i ∉ P)) :=
        Finset.disjoint_filter.2 (fun i _ h1 h2 => by omega)
      have hcard : ((scopeN k r a \ P).card : ℤ) =
          z ⟨q, by omega⟩ + (S.val : ℤ) - z ⟨a.2.val, by omega⟩ := by
        rw [hsc, Finset.card_union_of_disjoint hdisj, Nat.cast_add, ← hz_eq q (by omega),
          ← psum_card_sub P a.2.val k (by omega) le_rfl, ← hz_eq k le_rfl,
          ← hz_eq a.2.val (by omega), hzk]
        ring
      have hnotL : ¬ (reachN r a.1 + 1 ≤ q) := by dsimp only [q, L]; omega
      have hedge : BFEdge k r S act inW ⟨a.2.val, by omega⟩ ⟨q, by omega⟩
          ((if inW a then 2 else 1) - (S.val : ℤ)) := by
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a.1, hL', hqpos, ?_, ?_, ?_⟩)))
        · rw [dif_neg hnotL]
          have : (⟨q + k - (reachN r a.1 + 1), by dsimp only [q, L]; omega⟩ : Fin k) = a.2 :=
            Fin.ext (by dsimp only [q, L]; omega)
          rw [this]; exact ha
        · rw [dif_neg hnotL]; dsimp only [q, L]; omega
        · rw [dif_neg hnotL, if_neg hnotL]
          have : (⟨q + k - (reachN r a.1 + 1), by dsimp only [q, L]; omega⟩ : Fin k) = a.2 :=
            Fin.ext (by dsimp only [q, L]; omega)
          rw [this]
      have hle := hz_edge _ _ _ hedge
      by_cases hiw : inW a = true <;> simp [hiw] at hle ⊢ <;> omega

theorem bf_complete {k r : ℕ} (hk : 0 < k) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (P : Finset (Fin k)) (hPcard : P.card = k - S.val)
    (hcap : ∀ a : Bool × Fin k, act a = true → (scopeN k r a \ P).card ≤ if inW a then 2 else 1) :
    bfOK k r S act inW = true := by
  have hcardU : (Finset.univ \ P).card = S.val := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  have hfull : fullOK k r S act inW = true := by
    simp only [fullOK, decide_eq_true_eq]
    intro a hL ha
    have h1 := hcap a ha
    rw [scopeN_full hk a hL, hcardU] at h1
    exact h1
  let z : Fin (k + 1) → ℤ := fun t =>
    ((Finset.univ.filter (fun i : Fin k => i.val < t.val ∧ i ∉ P)).card : ℤ)
  have hz0 : z ⟨0, by omega⟩ = 0 := by simp [z]
  have hzk : z ⟨k, by omega⟩ = (S.val : ℤ) := by
    dsimp only [z]
    have heq : Finset.univ.filter (fun i : Fin k => i.val < k ∧ i ∉ P) = Finset.univ \ P := by
      ext i; simp
    rw [heq, hcardU]
  have hz_edge : ∀ u v w, BFEdge k r S act inW u v w → z v - z u ≤ w := by
    intro u v w he
    rcases he with ⟨hu, rfl⟩ | ⟨hv, rfl⟩ | ⟨hu, hv, rfl⟩ | ⟨hu, hv, rfl⟩ | ⟨col_b, hL, hv0, hact, hu, rfl⟩
    · have hsub := psum_card_sub P u.val v.val (by omega) (by omega)
      dsimp only [z]; rw [hsub]
      have hle : (Finset.univ.filter (fun i : Fin k => u.val ≤ i.val ∧ i.val < v.val ∧ i ∉ P)).card ≤ 1 := by
        have hsub1 : Finset.univ.filter (fun i : Fin k => u.val ≤ i.val ∧ i.val < v.val ∧ i ∉ P) ⊆
            {⟨u.val, by omega⟩} := by
          intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hi ⊢
          exact Fin.ext (by simp; omega)
        exact le_trans (Finset.card_le_card hsub1) (by simp)
      omega
    · have hsub := psum_card_sub P v.val u.val (by omega) (by omega)
      dsimp only [z]; omega
    · have hzu : z u = 0 := by have : u = ⟨0, by omega⟩ := Fin.ext hu; rw [this, hz0]
      have hzv : z v = (S.val : ℤ) := by have : v = ⟨k, by omega⟩ := Fin.ext hv; rw [this, hzk]
      omega
    · have hzu : z u = (S.val : ℤ) := by have : u = ⟨k, by omega⟩ := Fin.ext hu; rw [this, hzk]
      have hzv : z v = 0 := by have : v = ⟨0, by omega⟩ := Fin.ext hv; rw [this, hz0]
      omega
    · let L := reachN r col_b + 1
      by_cases hlv : L ≤ v.val
      · simp only [L] at hlv ⊢
        rw [if_pos hlv, sub_zero]
        set ui : Fin k := ⟨v.val - L, by omega⟩
        have hui : (if hlv' : reachN r col_b + 1 ≤ v.val then
            (⟨v.val - (reachN r col_b + 1), by omega⟩ : Fin k)
            else ⟨v.val + k - (reachN r col_b + 1), by omega⟩) = ui := dif_pos hlv
        rw [hui] at hact hu ⊢
        have hsc : scopeN k r (col_b, ui) \ P =
            Finset.univ.filter (fun i : Fin k => ui.val ≤ i.val ∧ i.val < v.val ∧ i ∉ P) := by
          ext i
          have hnw : ui.val + L ≤ k := by dsimp only [ui]; omega
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            scopeN_nowrap (col_b, ui) hL hnw]
          have heqv : ui.val + L = v.val := by dsimp only [ui]; omega
          rw [heqv]; tauto
        have hsub := psum_card_sub P ui.val v.val (by dsimp only [ui]; omega) (by omega)
        have h1 : z v - z u = ((scopeN k r (col_b, ui) \ P).card : ℤ) := by
          dsimp only [z]; rw [hu, hsub, hsc]
        have h2 := hcap (col_b, ui) hact
        rw [h1]
        by_cases hiw : inW (col_b, ui) = true <;> simp [hiw] at h2 ⊢ <;> omega
      · simp only [L] at hlv ⊢
        rw [if_neg hlv]
        set ui : Fin k := ⟨v.val + k - L, by omega⟩
        have hui : (if hlv' : reachN r col_b + 1 ≤ v.val then
            (⟨v.val - (reachN r col_b + 1), by omega⟩ : Fin k)
            else ⟨v.val + k - (reachN r col_b + 1), by omega⟩) = ui := dif_neg hlv
        rw [hui] at hact hu ⊢
        have hwr : k < ui.val + L := by dsimp only [ui]; omega
        have hsc : scopeN k r (col_b, ui) \ P =
            (Finset.univ.filter (fun i : Fin k => i.val < v.val ∧ i ∉ P)) ∪
            (Finset.univ.filter (fun i : Fin k => ui.val ≤ i.val ∧ i.val < k ∧ i ∉ P)) := by
          ext i
          simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
            scopeN_wrap (col_b, ui) hL hwr, i.isLt]
          have heqv : ui.val + L - k = v.val := by dsimp only [ui]; omega
          rw [heqv]; tauto
        have hdisj : Disjoint (Finset.univ.filter (fun i : Fin k => i.val < v.val ∧ i ∉ P))
            (Finset.univ.filter (fun i : Fin k => ui.val ≤ i.val ∧ i.val < k ∧ i ∉ P)) :=
          Finset.disjoint_filter.2 (fun i _ h1 h2 => by dsimp only [ui] at h2; omega)
        have h1 : ((scopeN k r (col_b, ui) \ P).card : ℤ) = z v + (S.val : ℤ) - z u := by
          rw [hsc, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
          have hsub := psum_card_sub P ui.val k (by omega) le_rfl
          have hzu : z u = ((Finset.univ.filter (fun i : Fin k => i.val < ui.val ∧ i ∉ P)).card : ℤ) := by
            dsimp only [z]; rw [hu]
          have hzv : z v = ((Finset.univ.filter (fun i : Fin k => i.val < v.val ∧ i ∉ P)).card : ℤ) := rfl
          have hzk' : ((Finset.univ.filter (fun i : Fin k => i.val < k ∧ i ∉ P)).card : ℤ) = (S.val : ℤ) :=
            hzk
          omega
        have h2 := hcap (col_b, ui) hact
        by_cases hiw : inW (col_b, ui) = true <;> simp [hiw] at h2 ⊢ <;> omega
  unfold bfOK
  rw [hfull, Bool.true_and, decide_eq_true_iff]
  exact bfDist_stable_of_pot z hz_edge

theorem pow_two_gt_quad (k : ℕ) : (k + 1) * k + 4 < 2 ^ (k + 4) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h1 : 2 ^ (k + 1 + 4) = 2 * 2 ^ (k + 4) := by rw [show k + 1 + 4 = (k + 4) + 1 by omega, pow_succ, mul_comm]
    have h2 : (k + 1 + 1) * (k + 1) + 4 = (k + 1) * k + 4 + 2 * k + 2 := by ring
    have h3 : 2 * k + 2 ≤ 2 ^ (k + 4) := by
      have : k + 1 ≤ 2 ^ (k + 3) := by
        clear ih h1 h2
        induction k with
        | zero => norm_num
        | succ n ihn =>
          have : 2 ^ (n + 1 + 3) = 2 * 2 ^ (n + 3) := by rw [show n + 1 + 3 = (n + 3) + 1 by omega, pow_succ, mul_comm]
          omega
      have : 2 ^ (k + 4) = 2 * 2 ^ (k + 3) := by rw [show k + 4 = (k + 3) + 1 by omega, pow_succ, mul_comm]
      omega
    omega

def bfWinCandBV (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (col_b : Bool) (d : Fin (k + 1) → BitVec (k + 6)) (v : Fin (k + 1))
    (cur : BitVec (k + 6)) : BitVec (k + 6) :=
  let L := reachN r col_b + 1
  if hL : L < k then
    if hv : 0 < v.val then
      let u : Fin k := if hlv : L ≤ v.val then ⟨v.val - L, by omega⟩ else ⟨v.val + k - L, by omega⟩
      let w : BitVec (k + 6) :=
        if inW (col_b, u) then BitVec.ofInt (k + 6) (2 - if L ≤ v.val then 0 else (S.val : ℤ))
        else BitVec.ofInt (k + 6) (1 - if L ≤ v.val then 0 else (S.val : ℤ))
      if act (col_b, u) then minBV cur (d ⟨u.val, by omega⟩ + w) else cur
    else cur
  else cur

def bfStepBV (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool)
    (d : Fin (k + 1) → BitVec (k + 6)) (v : Fin (k + 1)) : BitVec (k + 6) :=
  let c0 := d v
  let c1 := if h : 0 < v.val then minBV c0 (d ⟨v.val - 1, by omega⟩ + BitVec.ofInt (k + 6) 1) else c0
  let c2 := if h : v.val < k then minBV c1 (d ⟨v.val + 1, by omega⟩) else c1
  let c3 := if v.val = k then minBV c2 (d ⟨0, by omega⟩ + BitVec.ofInt (k + 6) (S.val : ℤ)) else c2
  let c4 := if v.val = 0 then minBV c3 (d ⟨k, by omega⟩ + BitVec.ofInt (k + 6) (-(S.val : ℤ))) else c3
  let c5 := bfWinCandBV k r S act inW false d v c4
  bfWinCandBV k r S act inW true d v c5

def bfDistBV (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool) :
    ℕ → Fin (k + 1) → BitVec (k + 6)
  | 0 => fun _ => 0
  | t + 1 => bfStepBV k r S act inW (bfDistBV k r S act inW t)

theorem bfDistBV_eq (k r : ℕ) (S : Fin (k + 1)) (act inW : Bool × Fin k → Bool) :
    ∀ t ≤ k + 1, ∀ v, bfDistBV k r S act inW t v = BitVec.ofInt (k + 6) (bfDist k r S act inW t v) := by
  intro t
  induction t with
  | zero => intro _ v; rfl
  | succ t ih =>
    intro ht v
    have hpow : ((k + 1) * k + 4 : ℤ) < (2 : ℤ) ^ (k + 4) := by exact_mod_cast pow_two_gt_quad k
    have ht1 : t ≤ k := by omega
    have hb : ∀ u, -((t : ℤ) * k) ≤ bfDist k r S act inW t u ∧ bfDist k r S act inW t u ≤ 0 :=
      bfDist_bounds k r S act inW t
    have htk : (t : ℤ) * k ≤ (k : ℤ) * k := by nlinarith
    have hstep_min : ∀ (x y : ℤ), -(2 : ℤ) ^ (k + 4) ≤ x → x < (2 : ℤ) ^ (k + 4) →
        -(2 : ℤ) ^ (k + 4) ≤ y → y < (2 : ℤ) ^ (k + 4) →
        minBV (BitVec.ofInt (k + 6) x) (BitVec.ofInt (k + 6) y) = BitVec.ofInt (k + 6) (min x y) :=
      fun x y h1 h2 h3 h4 => ofInt_minBV (W := k + 6) (by omega) x y h1 h2 h3 h4
    have hwin : ∀ (col_b : Bool) (cur : ℤ), -(2 : ℤ) ^ (k + 4) ≤ cur → cur < (2 : ℤ) ^ (k + 4) →
        bfWinCandBV k r S act inW col_b (bfDistBV k r S act inW t) v (BitVec.ofInt (k + 6) cur) =
        BitVec.ofInt (k + 6) (bfWinCand k r S act inW col_b (bfDist k r S act inW t) v cur) := by
      intro col_b cur hclo hchi
      unfold bfWinCandBV bfWinCand
      by_cases hL : reachN r col_b + 1 < k
      · rw [dif_pos hL, dif_pos hL]
        by_cases hv : 0 < v.val
        · rw [dif_pos hv, dif_pos hv]
          set ui : Fin k := if hlv : reachN r col_b + 1 ≤ v.val then
            ⟨v.val - (reachN r col_b + 1), by omega⟩ else ⟨v.val + k - (reachN r col_b + 1), by omega⟩
          by_cases hact : act (col_b, ui) = true
          · rw [if_pos hact, if_pos hact, ih (by omega) ⟨ui.val, by omega⟩]
            have hdu := hb ⟨ui.val, by omega⟩
            by_cases hiw : inW (col_b, ui) = true
            · rw [if_pos hiw, if_pos hiw, ← BitVec.ofInt_add]
              apply hstep_min _ _ hclo hchi
              · split_ifs <;> nlinarith [S.isLt]
              · split_ifs <;> nlinarith [S.isLt]
            · rw [if_neg hiw, if_neg hiw, ← BitVec.ofInt_add]
              apply hstep_min _ _ hclo hchi
              · split_ifs <;> nlinarith [S.isLt]
              · split_ifs <;> nlinarith [S.isLt]
          · rw [if_neg hact, if_neg hact]
        · rw [dif_neg hv, dif_neg hv]
      · rw [dif_neg hL, dif_neg hL]
    set dZ := bfDist k r S act inW t
    set c0Z := dZ v
    set c1Z := if h : 0 < v.val then min c0Z (dZ ⟨v.val - 1, by omega⟩ + 1) else c0Z
    set c2Z := if h : v.val < k then min c1Z (dZ ⟨v.val + 1, by omega⟩) else c1Z
    set c3Z := if v.val = k then min c2Z (dZ ⟨0, by omega⟩ + (S.val : ℤ)) else c2Z
    set c4Z := if v.val = 0 then min c3Z (dZ ⟨k, by omega⟩ - (S.val : ℤ)) else c3Z
    set c5Z := bfWinCand k r S act inW false dZ v c4Z
    have h0b : -(2 : ℤ) ^ (k + 4) ≤ c0Z ∧ c0Z < (2 : ℤ) ^ (k + 4) := by
      have := hb v; constructor <;> nlinarith
    have h1b : -(2 : ℤ) ^ (k + 4) ≤ c1Z ∧ c1Z < (2 : ℤ) ^ (k + 4) := by
      dsimp only [c1Z]; split_ifs
      · have := hb ⟨v.val - 1, by omega⟩; constructor <;> [exact le_min h0b.1 (by nlinarith); exact lt_of_le_of_lt (min_le_left _ _) h0b.2]
      · exact h0b
    have h2b : -(2 : ℤ) ^ (k + 4) ≤ c2Z ∧ c2Z < (2 : ℤ) ^ (k + 4) := by
      dsimp only [c2Z]; split_ifs
      · have := hb ⟨v.val + 1, by omega⟩; constructor <;> [exact le_min h1b.1 (by nlinarith); exact lt_of_le_of_lt (min_le_left _ _) h1b.2]
      · exact h1b
    have h3b : -(2 : ℤ) ^ (k + 4) ≤ c3Z ∧ c3Z < (2 : ℤ) ^ (k + 4) := by
      dsimp only [c3Z]; split_ifs
      · have := hb ⟨0, by omega⟩; constructor <;> [exact le_min h2b.1 (by nlinarith); exact lt_of_le_of_lt (min_le_left _ _) h2b.2]
      · exact h2b
    have h4b : -(2 : ℤ) ^ (k + 4) ≤ c4Z ∧ c4Z < (2 : ℤ) ^ (k + 4) := by
      dsimp only [c4Z]; split_ifs
      · have := hb ⟨k, by omega⟩; constructor <;> [exact le_min h3b.1 (by nlinarith [S.isLt]); exact lt_of_le_of_lt (min_le_left _ _) h3b.2]
      · exact h3b
    have h5b : -(2 : ℤ) ^ (k + 4) ≤ c5Z ∧ c5Z < (2 : ℤ) ^ (k + 4) := by
      have hle : c5Z ≤ c4Z := bfWinCand_le_self ..
      refine ⟨?_, lt_of_le_of_lt hle h4b.2⟩
      dsimp only [c5Z]
      rcases bfWinCand_eq_or_edge k r S act inW false dZ v c4Z with h | ⟨u, w, he, h⟩
      · rw [h]; exact h4b.1
      · rw [h]; have := hb u; have := (bfEdge_w_bounds he).1; nlinarith
    set dB := bfDistBV k r S act inW t
    set c0B := dB v
    set c1B := if h : 0 < v.val then minBV c0B (dB ⟨v.val - 1, by omega⟩ + BitVec.ofInt (k + 6) 1) else c0B
    set c2B := if h : v.val < k then minBV c1B (dB ⟨v.val + 1, by omega⟩) else c1B
    set c3B := if v.val = k then minBV c2B (dB ⟨0, by omega⟩ + BitVec.ofInt (k + 6) (S.val : ℤ)) else c2B
    set c4B := if v.val = 0 then minBV c3B (dB ⟨k, by omega⟩ + BitVec.ofInt (k + 6) (-(S.val : ℤ))) else c3B
    set c5B := bfWinCandBV k r S act inW false dB v c4B
    change bfWinCandBV k r S act inW true dB v c5B = BitVec.ofInt (k + 6) (bfWinCand k r S act inW true dZ v c5Z)
    have e0 : c0B = BitVec.ofInt (k + 6) c0Z := ih (by omega) v
    have e1 : c1B = BitVec.ofInt (k + 6) c1Z := by
      dsimp only [c1B, c1Z]; rw [e0]; split_ifs
      · rw [ih (by omega) ⟨v.val - 1, by omega⟩, ← BitVec.ofInt_add]
        have := hb ⟨v.val - 1, by omega⟩
        exact hstep_min _ _ h0b.1 h0b.2 (by nlinarith) (by nlinarith)
      · rfl
    have e2 : c2B = BitVec.ofInt (k + 6) c2Z := by
      dsimp only [c2B, c2Z]; rw [e1]; split_ifs
      · rw [ih (by omega) ⟨v.val + 1, by omega⟩]
        have := hb ⟨v.val + 1, by omega⟩
        exact hstep_min _ _ h1b.1 h1b.2 (by nlinarith) (by nlinarith)
      · rfl
    have e3 : c3B = BitVec.ofInt (k + 6) c3Z := by
      dsimp only [c3B, c3Z]; rw [e2]; split_ifs
      · rw [ih (by omega) ⟨0, by omega⟩, ← BitVec.ofInt_add]
        have := hb ⟨0, by omega⟩
        exact hstep_min _ _ h2b.1 h2b.2 (by nlinarith) (by nlinarith [S.isLt])
      · rfl
    have e4 : c4B = BitVec.ofInt (k + 6) c4Z := by
      dsimp only [c4B, c4Z]; rw [e3]; split_ifs
      · rw [ih (by omega) ⟨k, by omega⟩, ← BitVec.ofInt_add, ← sub_eq_add_neg]
        have := hb ⟨k, by omega⟩
        exact hstep_min _ _ h3b.1 h3b.2 (by nlinarith [S.isLt]) (by nlinarith [S.isLt])
      · rfl
    have e5 : c5B = BitVec.ofInt (k + 6) c5Z := by
      dsimp only [c5B, c5Z]; rw [e4]; exact hwin false c4Z h4b.1 h4b.2
    rw [e5]
    exact hwin true c5Z h5b.1 h5b.2

abbrev BFIn (k : ℕ) : Type := (Bool × Fin k) ⊕ (Bool × Fin k)

theorem cw_bfWinCand (k r : ℕ) (S : Fin (k + 1)) (col_b : Bool) (v : Fin (k + 1))
    {S0 : ℕ} {cur : (BFIn k ⊕ (Fin (k + 1) × Fin (k + 6)) → Bool) → BitVec (k + 6)}
    (hcur : Cw (BFIn k ⊕ (Fin (k + 1) × Fin (k + 6))) (k + 6) S0 cur) :
    Cw (BFIn k ⊕ (Fin (k + 1) × Fin (k + 6))) (k + 6) (S0 + 80 * (k + 7))
      (fun x => bfWinCandBV k r S (fun a => x (Sum.inl (Sum.inl a)))
        (fun a => x (Sum.inl (Sum.inr a))) col_b
        (fun u => bv (fun b => x (Sum.inr (u, b)))) v (cur x)) := by
  let J := BFIn k ⊕ (Fin (k + 1) × Fin (k + 6))
  by_cases hL : reachN r col_b + 1 < k
  · by_cases hv : 0 < v.val
    · set ui : Fin k := if hlv : reachN r col_b + 1 ≤ v.val then
        ⟨v.val - (reachN r col_b + 1), by omega⟩ else ⟨v.val + k - (reachN r col_b + 1), by omega⟩
      have hw : Cw (J ⊕ Fin (k + 6)) (k + 6) (6 * (k + 6)) (fun x =>
          if x (Sum.inl (Sum.inl (Sum.inr (col_b, ui)))) then
            BitVec.ofInt (k + 6) (2 - if reachN r col_b + 1 ≤ v.val then 0 else (S.val : ℤ))
          else BitVec.ofInt (k + 6) (1 - if reachN r col_b + 1 ≤ v.val then 0 else (S.val : ℤ))) :=
        Cw.mono (Cw.mux (Cb.var (ι := J ⊕ Fin (k + 6)) (Sum.inl (Sum.inl (Sum.inr (col_b, ui)))))
          (Cw.const (ι := J ⊕ Fin (k + 6)) _) (Cw.const (ι := J ⊕ Fin (k + 6)) _)) (by omega)
      have hdu : Cw (J ⊕ Fin (k + 6)) (k + 6) 0
          (fun x => bv (fun b : Fin (k + 6) => x (Sum.inl (Sum.inr (⟨ui.val, by omega⟩, b))))) :=
        Cw.var (ι := J ⊕ Fin (k + 6)) (W := k + 6) (fun b : Fin (k + 6) => Sum.inl (Sum.inr (⟨ui.val, by omega⟩, b)))
      have hc0 : Cw (J ⊕ Fin (k + 6)) (k + 6) 0 (fun x => bv (fun b : Fin (k + 6) => x (Sum.inr b))) :=
        Cw.var (ι := J ⊕ Fin (k + 6)) (W := k + 6) (fun b : Fin (k + 6) => Sum.inr b)
      have hsum := Cw.add hdu hw
      have hmin := Cw.min (by omega) hc0 hsum
      have hmux := Cw.mux (Cb.var (ι := J ⊕ Fin (k + 6)) (Sum.inl (Sum.inl (Sum.inl (col_b, ui))))) hmin hc0
      have htot := Cmp.thn hcur hmux
      refine Cw.mono (Cw.congr htot ?_) (by omega)
      intro x
      simp only [Sum.elim_inl, Sum.elim_inr, bv_getLsbD]
      unfold bfWinCandBV
      rw [dif_pos hL, dif_pos hv]
      rfl
    · refine Cw.mono (Cw.congr hcur ?_) (by omega)
      intro x; unfold bfWinCandBV; rw [dif_pos hL, dif_neg hv]
  · refine Cw.mono (Cw.congr hcur ?_) (by omega)
    intro x; unfold bfWinCandBV; rw [dif_neg hL]

theorem cmp_bfStep (k r : ℕ) (S : Fin (k + 1)) :
    Cmp (BFIn k ⊕ (Fin (k + 1) × Fin (k + 6))) (Fin (k + 1) × Fin (k + 6))
      ((k + 1) * (400 * (k + 7)))
      (fun x p => (bfStepBV k r S (fun a => x (Sum.inl (Sum.inl a)))
        (fun a => x (Sum.inl (Sum.inr a)))
        (fun u => bv (fun b => x (Sum.inr (u, b)))) p.1).getLsbD p.2.val) := by
  let J := BFIn k ⊕ (Fin (k + 1) × Fin (k + 6))
  have hv : ∀ v : Fin (k + 1), Cw J (k + 6) (400 * (k + 7))
      (fun x => bfStepBV k r S (fun a => x (Sum.inl (Sum.inl a)))
        (fun a => x (Sum.inl (Sum.inr a)))
        (fun u => bv (fun b => x (Sum.inr (u, b)))) v) := by
    intro v
    have h0 : Cw J (k + 6) 0 (fun x => bv (fun b => x (Sum.inr (v, b)))) :=
      Cw.var (fun b => Sum.inr (v, b))
    have h1 : Cw J (k + 6) (60 * (k + 7)) (fun x =>
        if h : 0 < v.val then minBV (bv (fun b => x (Sum.inr (v, b))))
          (bv (fun b => x (Sum.inr (⟨v.val - 1, by omega⟩, b))) + BitVec.ofInt (k + 6) 1)
        else bv (fun b => x (Sum.inr (v, b)))) := by
      by_cases hv1 : 0 < v.val
      · have h := Cw.min (by omega) h0 (Cw.add (Cw.var (fun b => Sum.inr (⟨v.val - 1, by omega⟩, b)))
          (Cw.const (BitVec.ofInt (k + 6) 1)))
        exact Cw.mono (Cw.congr h (fun x => by simp [hv1])) (by omega)
      · exact Cw.mono (Cw.congr h0 (fun x => by simp [hv1])) (by omega)
    have h2 : Cw J (k + 6) (100 * (k + 7)) (fun x =>
        if h : v.val < k then minBV (if h1 : 0 < v.val then minBV (bv (fun b => x (Sum.inr (v, b))))
          (bv (fun b => x (Sum.inr (⟨v.val - 1, by omega⟩, b))) + BitVec.ofInt (k + 6) 1)
          else bv (fun b => x (Sum.inr (v, b))))
          (bv (fun b => x (Sum.inr (⟨v.val + 1, by omega⟩, b))))
        else (if h1 : 0 < v.val then minBV (bv (fun b => x (Sum.inr (v, b))))
          (bv (fun b => x (Sum.inr (⟨v.val - 1, by omega⟩, b))) + BitVec.ofInt (k + 6) 1)
          else bv (fun b => x (Sum.inr (v, b))))) := by
      by_cases hv2 : v.val < k
      · have h := Cw.min (by omega) h1 (Cw.var (fun b => Sum.inr (⟨v.val + 1, by omega⟩, b)))
        exact Cw.mono (Cw.congr h (fun x => by simp [hv2])) (by omega)
      · exact Cw.mono (Cw.congr h1 (fun x => by simp [hv2])) (by omega)
    have h3 : Cw J (k + 6) (160 * (k + 7)) (fun x =>
        let c1 := if h1 : 0 < v.val then minBV (bv (fun b => x (Sum.inr (v, b))))
          (bv (fun b => x (Sum.inr (⟨v.val - 1, by omega⟩, b))) + BitVec.ofInt (k + 6) 1)
          else bv (fun b => x (Sum.inr (v, b)))
        let c2 := if h2 : v.val < k then minBV c1 (bv (fun b => x (Sum.inr (⟨v.val + 1, by omega⟩, b)))) else c1
        if v.val = k then minBV c2 (bv (fun b => x (Sum.inr (⟨0, by omega⟩, b))) + BitVec.ofInt (k + 6) (S.val : ℤ))
        else c2) := by
      by_cases hv3 : v.val = k
      · have h := Cw.min (by omega) h2 (Cw.add (Cw.var (fun b => Sum.inr (⟨0, by omega⟩, b)))
          (Cw.const (BitVec.ofInt (k + 6) (S.val : ℤ))))
        exact Cw.mono (Cw.congr h (fun x => by simp [hv3])) (by omega)
      · exact Cw.mono (Cw.congr h2 (fun x => by simp [hv3])) (by omega)
    have h4 : Cw J (k + 6) (220 * (k + 7)) (fun x =>
        let c1 := if h1 : 0 < v.val then minBV (bv (fun b => x (Sum.inr (v, b))))
          (bv (fun b => x (Sum.inr (⟨v.val - 1, by omega⟩, b))) + BitVec.ofInt (k + 6) 1)
          else bv (fun b => x (Sum.inr (v, b)))
        let c2 := if h2 : v.val < k then minBV c1 (bv (fun b => x (Sum.inr (⟨v.val + 1, by omega⟩, b)))) else c1
        let c3 := if v.val = k then minBV c2 (bv (fun b => x (Sum.inr (⟨0, by omega⟩, b))) + BitVec.ofInt (k + 6) (S.val : ℤ)) else c2
        if v.val = 0 then minBV c3 (bv (fun b => x (Sum.inr (⟨k, by omega⟩, b))) + BitVec.ofInt (k + 6) (-(S.val : ℤ)))
        else c3) := by
      by_cases hv4 : v.val = 0
      · have h := Cw.min (by omega) h3 (Cw.add (Cw.var (fun b => Sum.inr (⟨k, by omega⟩, b)))
          (Cw.const (BitVec.ofInt (k + 6) (-(S.val : ℤ)))))
        exact Cw.mono (Cw.congr h (fun x => by simp [hv4])) (by omega)
      · exact Cw.mono (Cw.congr h3 (fun x => by simp [hv4])) (by omega)
    have h5 := cw_bfWinCand k r S false v h4
    have h6 := cw_bfWinCand k r S true v h5
    exact Cw.mono (Cw.congr h6 (fun x => rfl)) (by omega)
  have hpi := Cmp.piU hv
  rw [Fintype.card_fin] at hpi
  exact hpi

theorem cmp_bf (k r : ℕ) (S : Fin (k + 1)) :
    Cmp (BFIn k) (Unit ⊕ Fin k) (600 * (k + 7) ^ 3)
      (fun x => Sum.elim
        (fun _ => bfOK k r S (fun a => x (Sum.inl a)) (fun a => x (Sum.inr a)))
        (bfP k r S (fun a => x (Sum.inl a)) (fun a => x (Sum.inr a)))) := by
  have hch := Cmp.chain (k + 1) ((k + 1) * (400 * (k + 7)))
    (fun t (x : BFIn k → Bool) (p : Fin (k + 1) × Fin (k + 6)) =>
      (bfDistBV k r S (fun a => x (Sum.inl a)) (fun a => x (Sum.inr a)) t p.1).getLsbD p.2.val)
    (fun _ => fun x p => (bfStepBV k r S (fun a => x (Sum.inl (Sum.inl a)))
      (fun a => x (Sum.inl (Sum.inr a)))
      (fun u => bv (fun b => x (Sum.inr (u, b)))) p.1).getLsbD p.2.val)
    (by
      have h0 := Cmp.ofBits (ι := BFIn k) (κ := Fin (k + 1) × Fin (k + 6)) (s := 1)
        (fun p => Cb.const false)
      simp only [Fintype.card_prod, Fintype.card_fin] at h0
      refine Cmp.mono (Cmp.congr h0 ?_) ?_
      · intro x p; simp [bfDistBV]
      · nlinarith)
    (fun _ _ => cmp_bfStep k r S)
    (by
      intro t _ x; funext p
      simp only [Sum.elim_inl, Sum.elim_inr, bfDistBV]
      congr 2; funext u; exact (bv_getLsbD _).symm)
  let J := BFIn k ⊕ (Fin (k + 2) × (Fin (k + 1) × Fin (k + 6)))
  have hfull : Cb J (2 * k * 9 + 1) (fun w => fullOK k r S
      (fun a => w (Sum.inl (Sum.inl a))) (fun a => w (Sum.inl (Sum.inr a)))) := by
    have ha_cb : ∀ a : Bool × Fin k, Cb J 8 (fun w =>
        if k ≤ reachN r a.1 + 1 then
          (!w (Sum.inl (Sum.inl a)) ||
            if w (Sum.inl (Sum.inr a)) then decide (S.val ≤ 2) else decide (S.val ≤ 1))
        else true) := by
      intro a
      by_cases hL : k ≤ reachN r a.1 + 1
      · refine Cb.mono (Cb.congr (Cb.or (Cb.not (Cb.var (ι := J) (Sum.inl (Sum.inl a))))
          (Cb.mux (Cb.var (ι := J) (Sum.inl (Sum.inr a))) (Cb.const (ι := J) (decide (S.val ≤ 2)))
            (Cb.const (ι := J) (decide (S.val ≤ 1))))) (fun w => by simp [hL])) (by omega)
      · exact Cb.mono (Cb.congr (Cb.const (ι := J) true) (fun w => by simp [hL])) (by omega)
    have h := Cb.bigAnd (ι := J) (I := Bool × Fin k) (s := 8) ha_cb
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at h
    refine Cb.mono (Cb.congr h ?_) (by omega)
    intro w
    rw [Bool.eq_iff_iff]
    simp only [fullOK, decide_eq_true_eq]
    constructor
    · intro ha a hL hact
      have h1 := ha a
      simp only [hL, ite_true, hact, Bool.not_true, Bool.false_or] at h1
      by_cases hiw : w (Sum.inl (Sum.inr a)) = true <;> simp [hiw] at h1 ⊢ <;> exact h1
    · intro ha a
      by_cases hL : k ≤ reachN r a.1 + 1
      · simp only [hL, ite_true]
        by_cases hact : w (Sum.inl (Sum.inl a)) = true
        · simp only [hact, Bool.not_true, Bool.false_or]
          have h1 := ha a hL hact
          by_cases hiw : w (Sum.inl (Sum.inr a)) = true <;> simp [hiw] at h1 ⊢ <;> exact h1
        · simp [hact]
      · simp [hL]
  have heqD : Cb J ((k + 1) * (6 * (k + 6) + 2) + 1)
      (fun w => decide (∀ v : Fin (k + 1),
        bv (fun b : Fin (k + 6) => w (Sum.inr (Fin.last (k + 1), (v, b)))) =
        bv (fun b : Fin (k + 6) => w (Sum.inr (⟨k, by omega⟩, (v, b)))))) := by
    have h := Cb.bigAnd (ι := J) (I := Fin (k + 1)) (s := 6 * (k + 6) + 1) (fun v =>
      Cb.mono (Cw.eqBV (W := k + 6) (Cw.var (ι := J) (W := k + 6) (fun b : Fin (k + 6) => Sum.inr (Fin.last (k + 1), (v, b))))
        (Cw.var (ι := J) (W := k + 6) (fun b : Fin (k + 6) => Sum.inr (⟨k, by omega⟩, (v, b))))) (by omega))
    simp only [Fintype.card_fin] at h
    refine Cb.mono (Cb.congr h ?_) (by ring_nf; omega)
    intro w
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
  have hok : Cb J ((k + 1) * (6 * (k + 6) + 2) + 2 * k * 9 + 3)
      (fun w => fullOK k r S (fun a => w (Sum.inl (Sum.inl a))) (fun a => w (Sum.inl (Sum.inr a))) &&
        decide (∀ v : Fin (k + 1),
          bv (fun b : Fin (k + 6) => w (Sum.inr (Fin.last (k + 1), (v, b)))) =
          bv (fun b : Fin (k + 6) => w (Sum.inr (⟨k, by omega⟩, (v, b)))))) :=
    Cb.mono (Cb.and hfull heqD) (by omega)
  have hP : Cmp J (Fin k) (k * ((k + 6) * 6 + 1))
      (fun w i => decide (bv (fun b : Fin (k + 6) => w (Sum.inr (⟨k, by omega⟩, (⟨i.val + 1, by omega⟩, b)))) =
        bv (fun b : Fin (k + 6) => w (Sum.inr (⟨k, by omega⟩, (⟨i.val, by omega⟩, b)))))) := by
    have h := Cmp.ofBits (ι := J) (κ := Fin k) (s := (k + 6) * 6 + 1) (fun i =>
      Cb.mono (Cw.eqBV (W := k + 6)
        (Cw.var (ι := J) (W := k + 6) (fun b : Fin (k + 6) => Sum.inr (⟨k, by omega⟩, (⟨i.val + 1, by omega⟩, b))))
        (Cw.var (ι := J) (W := k + 6) (fun b : Fin (k + 6) => Sum.inr (⟨k, by omega⟩, (⟨i.val, by omega⟩, b))))) (by omega))
    simp only [Fintype.card_fin] at h
    exact Cmp.mono h (by omega)
  have htot := Cmp.thn hch (Cmp.pair hok hP)
  have hpow : ((k + 1) * k + 4 : ℤ) < (2 : ℤ) ^ (k + 4) := by exact_mod_cast pow_two_gt_quad k
  have hpow5 : (2 : ℤ) ^ (k + 4) ≤ (2 : ℤ) ^ (k + 5) := by
    have : (2 : ℤ) ^ (k + 5) = 2 * (2 : ℤ) ^ (k + 4) := by
      rw [show k + 5 = (k + 4) + 1 by omega, pow_succ, mul_comm]
    have : (0 : ℤ) < (2 : ℤ) ^ (k + 4) := by positivity
    omega
  refine Cmp.mono (Cmp.congr htot ?_) ?_
  · intro x o
    have hbv : ∀ (t : ℕ) (ht : t ≤ k + 1) (v : Fin (k + 1)),
        bv (fun b : Fin (k + 6) => (bfDistBV k r S (fun a => x (Sum.inl a)) (fun a => x (Sum.inr a)) t v).getLsbD b.val) =
        BitVec.ofInt (k + 6) (bfDist k r S (fun a => x (Sum.inl a)) (fun a => x (Sum.inr a)) t v) := by
      intro t ht v; rw [bv_getLsbD, bfDistBV_eq k r S _ _ t ht v]
    cases o with
    | inl u =>
      change (fullOK k r S _ _ && decide _) = (fullOK k r S _ _ && decide _)
      congr 1
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, funext_iff]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.val_last]
      constructor
      · intro hall v
        have h1 := hall v
        rw [hbv (k + 1) le_rfl v, hbv k (by omega) v] at h1
        have hb1 := bfDist_bounds k r S (fun a => x (Sum.inl a)) (fun a => x (Sum.inr a)) (k + 1) v
        have hb2 := bfDist_bounds k r S (fun a => x (Sum.inl a)) (fun a => x (Sum.inr a)) k v
        have h65 : k + 6 - 1 = k + 5 := by omega
        exact (ofInt_inj (W := k + 6) (by omega) _ _
          (by rw [h65]; push_cast at hb1; nlinarith)
          (by rw [h65]; nlinarith)
          (by rw [h65]; push_cast at hb2; nlinarith)
          (by rw [h65]; nlinarith)).1 h1
      · intro hall v
        rw [hbv (k + 1) le_rfl v, hbv k (by omega) v, hall v]
    | inr i =>
      change decide _ = decide _
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hbv k (by omega) ⟨i.val + 1, by omega⟩, hbv k (by omega) ⟨i.val, by omega⟩]
      have hb1 := bfDist_bounds k r S (fun a => x (Sum.inl a)) (fun a => x (Sum.inr a)) k ⟨i.val + 1, by omega⟩
      have hb2 := bfDist_bounds k r S (fun a => x (Sum.inl a)) (fun a => x (Sum.inr a)) k ⟨i.val, by omega⟩
      have h65 : k + 6 - 1 = k + 5 := by omega
      exact ofInt_inj (W := k + 6) (by omega) _ _
        (by rw [h65]; push_cast at hb1; nlinarith)
        (by rw [h65]; nlinarith)
        (by rw [h65]; push_cast at hb2; nlinarith)
        (by rw [h65]; nlinarith)
  · have h1 : (k + 1 + 1) * ((k + 1) * (400 * (k + 7))) ≤ 400 * (k + 7) ^ 3 := by
      have : (k + 1 + 1) * (k + 1) ≤ (k + 7) ^ 2 := by nlinarith
      have : 400 * (k + 7) ^ 3 = (k + 7) ^ 2 * (400 * (k + 7)) := by ring
      nlinarith
    have h2 : (k + 1) * (6 * (k + 6) + 2) + 2 * k * 9 + 3 + k * ((k + 6) * 6 + 1) ≤ 200 * (k + 7) ^ 3 := by
      nlinarith
    omega

abbrev RBIn (k m : ℕ) : Type := (Fin m × Fin k) ⊕ (Fin m × Fin k)
abbrev P1Out (k m : ℕ) : Type := Unit ⊕ (Fin k ⊕ (Fin m × Fin m))

def colOfRB {k m : ℕ} (r : ℕ) (v : RBIn k m → Bool) (a : Bool × Fin k) (j : Fin m) : ZMod 2 :=
  toZ (if a.1 then v (Sum.inr (j, ⟨(a.2.val + delayN r true) % k, Nat.mod_lt _ a.2.pos⟩))
    else v (Sum.inl (j, ⟨(a.2.val + delayN r false) % k, Nat.mod_lt _ a.2.pos⟩)))

def actOfRB {k m : ℕ} (r : ℕ) (v : RBIn k m → Bool) (a : Bool × Fin k) : Bool :=
  decide (∃ j : Fin m, ofZ (colOfRB r v a j) = true)

def inWOfRB {k m : ℕ} (r : ℕ) (v : RBIn k m → Bool) (Rmm : Fin m × Fin m → Bool)
    (a : Bool × Fin k) : Bool :=
  decide (∀ j : Fin m, ofZ (tilde Rmm (colOfRB r v a) j) = false)

def tupStepS {k r m b h' : ℕ} (v : RBIn k m → Bool) (tup : Fin h' → Option (Bool × Fin k))
    (S : Fin (k + 1)) (acc : Unit ⊕ Fin k → Bool) : Unit ⊕ Fin k → Bool :=
  let Rmm := R_tup (colOfRB r v) tup
  let d := rhoM Rmm
  let act := actOfRB r v
  let inW := inWOfRB r v Rmm
  let okS := decide (k - S.val + d ≤ b) && bfOK k r S act inW
  let take := !acc (Sum.inl ()) && okS
  Sum.elim (fun _ => acc (Sum.inl ()) || okS)
    (fun i => if take then bfP k r S act inW i else acc (Sum.inr i))

def tupSolve {k r m b h' : ℕ} (v : RBIn k m → Bool) (tup : Fin h' → Option (Bool × Fin k)) :
    Unit ⊕ Fin k → Bool :=
  (List.finRange (k + 1)).foldl (fun acc S => tupStepS (r := r) (b := b) v tup S acc) (fun _ => false)

def p1Step {k r m b h' : ℕ} (tup : Fin h' → Option (Bool × Fin k))
    (v : RBIn k m → Bool) (acc : P1Out k m → Bool) : P1Out k m → Bool :=
  let res := tupSolve (r := r) (b := b) v tup
  let ok := res (Sum.inl ())
  let take := !acc (Sum.inl ()) && ok
  let Rmm := R_tup (colOfRB r v) tup
  Sum.elim (fun _ => acc (Sum.inl ()) || ok)
    (Sum.elim (fun i => if take then res (Sum.inr i) else acc (Sum.inr (Sum.inl i)))
      (fun p => if take then Rmm p else acc (Sum.inr (Sum.inr p))))

noncomputable def phase1Out (k r m b h' : ℕ) (v : RBIn k m → Bool) : P1Out k m → Bool :=
  ((Finset.univ : Finset (Fin h' → Option (Bool × Fin k))).toList).foldl
    (fun acc tup => p1Step (r := r) (b := b) tup v acc) (fun _ => false)

theorem tupSolve_spec {k r m b h' : ℕ} (hk : 0 < k) (v : RBIn k m → Bool)
    (tup : Fin h' → Option (Bool × Fin k)) :
    let Rmm := R_tup (colOfRB r v) tup
    let d := rhoM Rmm
    let act := actOfRB r v
    let inW := inWOfRB r v Rmm
    let res := tupSolve (r := r) (b := b) v tup
    (res (Sum.inl ()) = true ↔ ∃ S : Fin (k + 1), k - S.val + d ≤ b ∧ bfOK k r S act inW = true) ∧
    (res (Sum.inl ()) = true →
      ∃ S : Fin (k + 1), k - S.val + d ≤ b ∧ bfOK k r S act inW = true ∧
        ∀ i : Fin k, res (Sum.inr i) = bfP k r S act inW i) ∧
    (res (Sum.inl ()) = false → ∀ i : Fin k, res (Sum.inr i) = false) := by
  intro Rmm d act inW res
  have hgen : ∀ (L : List (Fin (k + 1))) (acc : Unit ⊕ Fin k → Bool),
      (acc (Sum.inl ()) = true → ∃ S : Fin (k + 1), k - S.val + d ≤ b ∧ bfOK k r S act inW = true ∧
        ∀ i : Fin k, acc (Sum.inr i) = bfP k r S act inW i) →
      (acc (Sum.inl ()) = false → ∀ i : Fin k, acc (Sum.inr i) = false) →
      let out := L.foldl (fun a S => tupStepS (r := r) (b := b) v tup S a) acc
      (out (Sum.inl ()) = true ↔ acc (Sum.inl ()) = true ∨
        ∃ S ∈ L, k - S.val + d ≤ b ∧ bfOK k r S act inW = true) ∧
      (out (Sum.inl ()) = true → ∃ S : Fin (k + 1), k - S.val + d ≤ b ∧ bfOK k r S act inW = true ∧
        ∀ i : Fin k, out (Sum.inr i) = bfP k r S act inW i) ∧
      (out (Sum.inl ()) = false → ∀ i : Fin k, out (Sum.inr i) = false) := by
    intro L
    induction L with
    | nil =>
      intro acc h1 h2
      refine ⟨by simp, h1, h2⟩
    | cons S L ih =>
      intro acc h1 h2
      have hstep1 : (tupStepS (r := r) (b := b) v tup S acc) (Sum.inl ()) = true →
          ∃ S' : Fin (k + 1), k - S'.val + d ≤ b ∧ bfOK k r S' act inW = true ∧
            ∀ i : Fin k, (tupStepS (r := r) (b := b) v tup S acc) (Sum.inr i) = bfP k r S' act inW i := by
        intro h
        cases ha : acc (Sum.inl ())
        · simp only [tupStepS, Sum.elim_inl, ha, Bool.false_or, Bool.and_eq_true,
            decide_eq_true_eq] at h
          exact ⟨S, h.1, h.2, fun i => by simp [tupStepS, ha, h.1, h.2]; rfl⟩
        · obtain ⟨S', hS1, hS2, hS3⟩ := h1 ha
          exact ⟨S', hS1, hS2, fun i => by simp [tupStepS, ha, hS3 i]⟩
      have hstep2 : (tupStepS (r := r) (b := b) v tup S acc) (Sum.inl ()) = false →
          ∀ i : Fin k, (tupStepS (r := r) (b := b) v tup S acc) (Sum.inr i) = false := by
        intro h i
        simp only [tupStepS, Sum.elim_inl, Bool.or_eq_false_iff] at h
        simp only [tupStepS, Sum.elim_inr, h.1, h.2, Bool.and_false]
        exact h2 h.1 i
      have hrec := ih (tupStepS (r := r) (b := b) v tup S acc) hstep1 hstep2
      refine ⟨?_, hrec.2.1, hrec.2.2⟩
      rw [List.foldl_cons, hrec.1]
      simp only [tupStepS, Sum.elim_inl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.mem_cons]
      constructor
      · rintro ((h | ⟨h1', h2'⟩) | ⟨S', hS', h1', h2'⟩)
        · left; exact h
        · right; exact ⟨S, Or.inl rfl, h1', h2'⟩
        · right; exact ⟨S', Or.inr hS', h1', h2'⟩
      · rintro (h | ⟨S', rfl | hS', h1', h2'⟩)
        · left; left; exact h
        · left; right; exact ⟨h1', h2'⟩
        · right; exact ⟨S', hS', h1', h2'⟩
  have h := hgen (List.finRange (k + 1)) (fun _ => false) (by intro h; simp at h) (fun _ _ => rfl)
  refine ⟨?_, h.2.1, h.2.2⟩
  dsimp only [res, tupSolve]
  rw [h.1]
  simp

theorem phase1_spec {k r m b h : ℕ} (hk : 0 < k) (R B : Fin m → Fin (2 ^ k)) :
    let h' := min h (min b (min m (2 * k)))
    let v : RBIn k m → Bool := Sum.elim (fun p => (R p.1).val.testBit p.2.val)
      (fun p => (B p.1).val.testBit p.2.val)
    let out := phase1Out k r m b h' v
    let passP := ∃ P : Finset (Fin k), worksN r b h R B P
    let P := Finset.univ.filter (fun i : Fin k => out (Sum.inr (Sum.inl i)) = true)
    let Rmm : Fin m × Fin m → Bool := fun p => out (Sum.inr (Sum.inr p))
    (out (Sum.inl ()) = true ↔ passP) ∧
    (out (Sum.inl ()) = false → P = ∅) ∧
    (out (Sum.inl ()) = true → GJF Rmm ∧ rhoM Rmm ≤ h ∧ P.card + rhoM Rmm ≤ b ∧
      (∀ a ∈ activeN r R B, (leftN r P a).card ≤ if tilde Rmm (colN r R B a) = 0 then 2 else 1) ∧
      worksN r b h R B P) := by
  intro h' v out passP P Rmm
  have hcol : colOfRB r v = colN r R B := by
    funext a j
    unfold colOfRB colN
    cases ha : a.1
    · simp only [ha, Bool.false_eq_true, ite_false, v, Sum.elim_inl, toZ]
    · simp only [ha, ite_true, v, Sum.elim_inr, toZ]
  have hact : ∀ a, actOfRB r v a = true ↔ a ∈ activeN r R B := by
    intro a
    simp only [actOfRB, decide_eq_true_eq, activeN, Finset.mem_filter, Finset.mem_univ, true_and, hcol]
    constructor
    · rintro ⟨j, hj⟩ h0
      rw [h0] at hj; simp [ofZ] at hj
    · intro hne
      by_contra hall; push_neg at hall
      apply hne; funext j
      have := hall j
      rw [← toZ_ofZ (colN r R B a j)]
      simp only [Bool.not_eq_true] at this
      rw [this]; rfl
  have hinW : ∀ (R1 : Fin m × Fin m → Bool) a,
      inWOfRB r v R1 a = true ↔ tilde R1 (colN r R B a) = 0 := by
    intro R1 a
    simp only [inWOfRB, decide_eq_true_eq, hcol, funext_iff, Pi.zero_apply]
    constructor
    · intro h j; rw [← toZ_ofZ (tilde R1 (colN r R B a) j), h j]; rfl
    · intro h j; rw [h j]; rfl
  let GoodAcc : (P1Out k m → Bool) → Prop := fun acc =>
    let Pa := Finset.univ.filter (fun i : Fin k => acc (Sum.inr (Sum.inl i)) = true)
    let Ra : Fin m × Fin m → Bool := fun p => acc (Sum.inr (Sum.inr p))
    (acc (Sum.inl ()) = false → ∀ i, acc (Sum.inr (Sum.inl i)) = false) ∧
    (acc (Sum.inl ()) = true → GJF Ra ∧ rhoM Ra ≤ h ∧ Pa.card + rhoM Ra ≤ b ∧
      ∀ a ∈ activeN r R B, (leftN r Pa a).card ≤ if tilde Ra (colN r R B a) = 0 then 2 else 1)
  have hgen : ∀ (L : List (Fin h' → Option (Bool × Fin k))) (acc : P1Out k m → Bool),
      GoodAcc acc →
      let res := L.foldl (fun a tup => p1Step (r := r) (b := b) tup v a) acc
      (res (Sum.inl ()) = true ↔ acc (Sum.inl ()) = true ∨
        ∃ tup ∈ L, tupSolve (r := r) (b := b) v tup (Sum.inl ()) = true) ∧
      GoodAcc res := by
    intro L
    induction L with
    | nil => intro acc hacc; exact ⟨by simp, hacc⟩
    | cons tup L ih =>
      intro acc hacc
      have hstepG : GoodAcc (p1Step (r := r) (b := b) tup v acc) := by
        refine ⟨?_, ?_⟩
        · intro hf i
          simp only [p1Step, Sum.elim_inl, Bool.or_eq_false_iff] at hf
          simp only [p1Step, Sum.elim_inr, Sum.elim_inl, hf.1, hf.2, Bool.and_false, ite_false]
          exact hacc.1 hf.1 i
        · intro ht
          cases ha : acc (Sum.inl ())
          · simp only [p1Step, Sum.elim_inl, ha, Bool.false_or] at ht
            have hts := tupSolve_spec (r := r) (b := b) hk v tup
            obtain ⟨S, hSb, hbf, hPi⟩ := hts.2.1 ht
            have hsnd := bf_sound hk S (actOfRB r v) (inWOfRB r v (R_tup (colOfRB r v) tup)) hbf
            have hRgjf : GJF (R_tup (colOfRB r v) tup) := R_tup_gjf _ _
            have hrh : rhoM (R_tup (colOfRB r v) tup) ≤ h := by
              rw [← finrank_rowSpan hRgjf, rowSpan_R_tup]
              calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun s : Fin h' => (tup s).elim 0 (colOfRB r v)))
                  ≤ (Set.range fun s : Fin h' => (tup s).elim 0 (colOfRB r v)).toFinset.card := finrank_span_le_card _
                _ ≤ h' := by
                    rw [Set.toFinset_range]
                    exact Finset.card_image_le.trans (by simp)
                _ ≤ h := Nat.min_le_left _ _
            have hPeq : Finset.univ.filter (fun i : Fin k =>
                p1Step (r := r) (b := b) tup v acc (Sum.inr (Sum.inl i)) = true) =
                Finset.univ.filter (fun i : Fin k =>
                  bfP k r S (actOfRB r v) (inWOfRB r v (R_tup (colOfRB r v) tup)) i = true) := by
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, p1Step, Sum.elim_inr,
                Sum.elim_inl, ha, Bool.not_false, ht, Bool.true_and, ite_true, hPi i]
            have hReq : (fun p => p1Step (r := r) (b := b) tup v acc (Sum.inr (Sum.inr p))) =
                R_tup (colOfRB r v) tup := by
              funext p
              simp [p1Step, ha, ht]
            rw [hPeq, hReq]
            refine ⟨hRgjf, hrh, by omega, ?_⟩
            intro a haA
            have h1 := hsnd.2 a ((hact a).2 haA)
            by_cases htil : tilde (R_tup (colOfRB r v) tup) (colN r R B a) = 0
            · have hiw : inWOfRB r v (R_tup (colOfRB r v) tup) a = true := (hinW _ a).2 htil
              simpa [htil, hiw, leftN] using h1
            · have hiw : inWOfRB r v (R_tup (colOfRB r v) tup) a = false := by
                by_contra hc; exact htil ((hinW _ a).1 (by simpa using hc))
              simpa [htil, hiw, leftN] using h1
          · have hPeq : Finset.univ.filter (fun i : Fin k =>
                p1Step (r := r) (b := b) tup v acc (Sum.inr (Sum.inl i)) = true) =
                Finset.univ.filter (fun i : Fin k => acc (Sum.inr (Sum.inl i)) = true) := by
              ext i; simp [p1Step, ha]
            have hReq : (fun p => p1Step (r := r) (b := b) tup v acc (Sum.inr (Sum.inr p))) =
                (fun p => acc (Sum.inr (Sum.inr p))) := by funext p; simp [p1Step, ha]
            rw [hPeq, hReq]
            exact hacc.2 ha
      have hrec := ih (p1Step (r := r) (b := b) tup v acc) hstepG
      refine ⟨?_, hrec.2⟩
      rw [List.foldl_cons, hrec.1]
      simp only [p1Step, Sum.elim_inl, Bool.or_eq_true, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨t, ht, hok⟩)
        · left; exact h
        · right; exact ⟨tup, Or.inl rfl, h⟩
        · right; exact ⟨t, Or.inr ht, hok⟩
      · rintro (h | ⟨t, rfl | ht, hok⟩)
        · left; left; exact h
        · left; right; exact hok
        · right; exact ⟨t, ht, hok⟩
  have h0G : GoodAcc (fun _ => false) := ⟨fun _ _ => rfl, fun h => by simp at h⟩
  have hmain := hgen (Finset.univ : Finset (Fin h' → Option (Bool × Fin k))).toList (fun _ => false) h0G
  have hout_iff : out (Sum.inl ()) = true ↔ passP := by
    constructor
    · intro ht
      obtain ⟨hRgjf, hrh, hPb, hcap⟩ := hmain.2.2 ht
      exact ⟨P, works_of_feasible R B Rmm hRgjf P hrh hPb hcap⟩
    · rintro ⟨P0, hw0⟩
      obtain ⟨tup, P1, hP1b, hP1h, hP1cap⟩ := exists_tup_of_works hk R B P0 hw0
      have hP1k : P1.card ≤ k := by
        calc P1.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = k := by simp
      let S : Fin (k + 1) := ⟨k - P1.card, by omega⟩
      have hbf : bfOK k r S (actOfRB r v) (inWOfRB r v (R_tup (colOfRB r v) tup)) = true := by
        apply bf_complete hk S _ _ P1 (by dsimp only [S]; omega)
        intro a ha
        have haA : a ∈ activeN r R B := (hact a).1 ha
        have h1 := hP1cap a haA
        rw [hcol]
        by_cases htil : tilde (R_tup (colN r R B) tup) (colN r R B a) = 0
        · have hiw : inWOfRB r v (R_tup (colN r R B) tup) a = true := (hinW _ a).2 htil
          simpa [htil, hiw, leftN] using h1
        · have hiw : inWOfRB r v (R_tup (colN r R B) tup) a = false := by
            by_contra hc; exact htil ((hinW _ a).1 (by simpa using hc))
          simpa [htil, hiw, leftN] using h1
      have hts : tupSolve (r := r) (b := b) v tup (Sum.inl ()) = true := by
        rw [(tupSolve_spec (r := r) (b := b) hk v tup).1]
        refine ⟨S, ?_, hbf⟩
        rw [hcol]
        dsimp only [S]; omega
      dsimp only [out, phase1Out]
      rw [hmain.1]
      right
      exact ⟨tup, by simp, hts⟩
  refine ⟨hout_iff, ?_, ?_⟩
  · intro hf
    ext i
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    dsimp only [out, phase1Out] at hf ⊢
    rw [hmain.2.1 hf i]; simp
  · intro ht
    obtain ⟨hRgjf, hrh, hPb, hcap⟩ := hmain.2.2 ht
    exact ⟨hRgjf, hrh, hPb, hcap, works_of_feasible R B Rmm hRgjf P hrh hPb hcap⟩

theorem cmp_colOfRB (k r m : ℕ) (a : Bool × Fin k) (j : Fin m) :
    Cb (RBIn k m) 0 (fun v => ofZ (colOfRB r v a j)) := by
  by_cases ha : a.1 = true
  · refine Cb.congr (Cb.var (Sum.inr (j, ⟨(a.2.val + delayN r true) % k, Nat.mod_lt _ a.2.pos⟩))) ?_
    intro v; simp [colOfRB, ha, ofZ_toZ]
  · refine Cb.congr (Cb.var (Sum.inl (j, ⟨(a.2.val + delayN r false) % k, Nat.mod_lt _ a.2.pos⟩))) ?_
    intro v; simp [colOfRB, ha, ofZ_toZ]

theorem cmp_R_tup (k r m h' : ℕ) (hhm : h' ≤ m) (tup : Fin h' → Option (Bool × Fin k)) :
    Cmp (RBIn k m) (Fin m × Fin m) (600 * (m + 1) ^ 4)
      (fun v => R_tup (colOfRB r v) tup) := by
  have hM : Cmp (RBIn k m) (Fin (m + h') × Fin (m + h')) ((m + h') * (m + h') * 1)
      (fun v => M_tup (colOfRB r v) tup) := by
    have h := Cmp.ofBits (ι := RBIn k m) (κ := Fin (m + h') × Fin (m + h')) (s := 1)
      (F := fun v => M_tup (colOfRB r v) tup) (fun p => by
      by_cases h1 : p.1.val < m
      · exact Cb.congr (Cb.const false) (fun v => by simp [M_tup, splitF, h1])
      · by_cases h2 : p.2.val < m
        · cases ho : tup ⟨p.1.val - m, by omega⟩ with
          | none => exact Cb.congr (Cb.const false) (fun v => by simp [M_tup, splitF, h1, h2, ho])
          | some a =>
            exact Cb.mono (Cb.congr (cmp_colOfRB k r m a ⟨p.2.val, h2⟩)
              (fun v => by simp [M_tup, splitF, h1, h2, ho])) (by omega)
        · exact Cb.congr (Cb.const false) (fun v => by simp [M_tup, splitF, h1, h2]))
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact h
  have htot := Cmp.comp (Cmp.comp hM (cmp_gj (m + h')))
    (Cmp.wire (fun p : Fin m × Fin m => (Fin.castAdd h' p.1, Fin.castAdd h' p.2)))
  refine Cmp.mono (Cmp.congr htot (fun v p => rfl)) ?_
  unfold gjCost
  have hD : m + h' + 1 ≤ 2 * (m + 1) := by omega
  have h1 : (m + h') * (m + h') * 1 ≤ (2 * (m + 1)) ^ 4 := by
    have : m + h' ≤ 2 * (m + 1) := by omega
    have hsq : (m + h') * (m + h') ≤ (2 * (m + 1)) * (2 * (m + 1)) := Nat.mul_le_mul this this
    have hsq2 : (2 * (m + 1)) * (2 * (m + 1)) ≤ (2 * (m + 1)) ^ 4 := by
      calc (2 * (m + 1)) * (2 * (m + 1)) = (2 * (m + 1)) ^ 2 := by ring
        _ ≤ (2 * (m + 1)) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have h2 : 32 * (m + h' + 1) ^ 4 ≤ 32 * (2 * (m + 1)) ^ 4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 4)
  have h3 : (2 * (m + 1)) ^ 4 = 16 * (m + 1) ^ 4 := by ring
  omega

theorem cmp_tupSolve (k r m b h' : ℕ) (hhm : h' ≤ m) (tup : Fin h' → Option (Bool × Fin k)) :
    Cmp (RBIn k m) ((Unit ⊕ Fin k) ⊕ (Fin m × Fin m)) (2048 * (k + r + m + 6) ^ 5)
      (fun v => Sum.elim (tupSolve (r := r) (b := b) v tup) (R_tup (colOfRB r v) tup)) := by
  set N := k + r + m + 6
  have hR := cmp_R_tup k r m h' hhm tup
  let J1 := RBIn k m ⊕ (Fin m × Fin m)
  have hcnt : Cmp J1 (Fin (m + 1) × Fin (m + 1)) ((m + 1) * ((m + 1) * 6))
      (fun w p => decide (cnt (fun q : Fin m => w (Sum.inr (q, q))) p.1.val = p.2.val)) :=
    Cmp.sel (fun q : Fin m => Sum.inr (q, q)) (cmp_counter m m)
  have hact : Cmp J1 (Bool × Fin k) (2 * k * (m + 1))
      (fun w a => actOfRB r (fun x => w (Sum.inl x)) a) := by
    have h := Cmp.ofBits (ι := J1) (κ := Bool × Fin k) (s := m + 1)
      (F := fun w a => actOfRB r (fun x => w (Sum.inl x)) a) (fun a => by
      have c := Cb.bigOr (I := Fin m) (fun j =>
        Cmp.sel (ι := J1) Sum.inl (cmp_colOfRB k r m a j))
      rw [Fintype.card_fin] at c
      exact Cb.mono (Cb.congr c (fun w => by rw [Bool.eq_iff_iff]; simp [actOfRB])) (by omega))
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at h
    exact Cmp.mono h (by omega)
  have hinW : Cmp J1 (Bool × Fin k) (2 * k * (m * (m * 5 + 7) + 1))
      (fun w a => inWOfRB r (fun x => w (Sum.inl x)) (fun p => w (Sum.inr p)) a) := by
    have h := Cmp.ofBits (ι := J1) (κ := Bool × Fin k) (s := m * (m * 5 + 7) + 1)
      (F := fun w a => inWOfRB r (fun x => w (Sum.inl x)) (fun p => w (Sum.inr p)) a) (fun a => by
      have c := Cb.bigAnd (ι := J1) (I := Fin m) (s := m * 5 + 6) (fun j => by
        have cs := Cb.sumZ (ι := J1) (I := Fin m) (fun p => Cb.and
          (Cmp.sel (ι := J1) Sum.inl (cmp_colOfRB k r m a p))
          (Cb.var (ι := J1) (Sum.inr (p, j))))
        rw [Fintype.card_fin] at cs
        exact Cb.mono (Cb.not (Cb.xor (Cmp.sel (ι := J1) Sum.inl (cmp_colOfRB k r m a j)) cs)) (by omega))
      rw [Fintype.card_fin] at c
      refine Cb.mono (Cb.congr c ?_) (by ring_nf; omega)
      intro w
      rw [Bool.eq_iff_iff]
      have hxor : ∀ a b : Bool, xor a b = false ↔ a = b := by decide
      simp only [inWOfRB, decide_eq_true_eq, Bool.not_eq_true', hxor]
      apply forall_congr'; intro j
      simp only [tilde, ofZ_add, hxor]
      have h1 : ofZ (∑ p : Fin m, colOfRB r (fun x => w (Sum.inl x)) a p * toZ (w (Sum.inr (p, j)))) =
          ofZ (∑ p : Fin m, toZ (ofZ (colOfRB r (fun x => w (Sum.inl x)) a p) && w (Sum.inr (p, j)))) := by
        congr 1; apply Finset.sum_congr rfl; intro p _; rw [toZ_and, toZ_ofZ]
      rw [h1])
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at h
    exact Cmp.mono h (by omega)
  have hprep : Cmp (RBIn k m) ((Fin m × Fin m) ⊕ ((Fin (m + 1) × Fin (m + 1)) ⊕ BFIn k))
      (600 * (m + 1) ^ 4 + ((m + 1) * ((m + 1) * 6) + (2 * k * (m + 1) + 2 * k * (m * (m * 5 + 7) + 1))))
      (fun v => Sum.elim (R_tup (colOfRB r v) tup)
        (Sum.elim (fun p => decide (cnt (fun q : Fin m => R_tup (colOfRB r v) tup (q, q)) p.1.val = p.2.val))
          (Sum.elim (actOfRB r v) (inWOfRB r v (R_tup (colOfRB r v) tup))))) :=
    Cmp.mono (Cmp.congr (Cmp.thn hR (Cmp.pair (Cmp.wire (ι := J1) Sum.inr) (Cmp.pair hcnt (Cmp.pair hact hinW))))
      (fun v x => by rcases x with p | p | a | a <;> rfl)) (by omega)
  let Pre := (Fin m × Fin m) ⊕ ((Fin (m + 1) × Fin (m + 1)) ⊕ BFIn k)
  let StS := Pre ⊕ (Unit ⊕ Fin k)
  have hstepS : ∀ S : Fin (k + 1), Cmp StS StS (600 * (k + 7) ^ 3 + 3 * m + 5 * k + 15)
      (fun w => Sum.elim (fun x => w (Sum.inl x))
        (let act := fun a => w (Sum.inl (Sum.inr (Sum.inr (Sum.inl a))))
         let inW := fun a => w (Sum.inl (Sum.inr (Sum.inr (Sum.inr a))))
         let okd := decide (∃ t : Fin (m + 1),
           (decide (k - S.val + t.val ≤ b) && w (Sum.inl (Sum.inr (Sum.inl (Fin.last m, t))))) = true)
         let okS := okd && bfOK k r S act inW
         let take := !w (Sum.inr (Sum.inl ())) && okS
         Sum.elim (fun _ => w (Sum.inr (Sum.inl ())) || okS)
           (fun i => if take then bfP k r S act inW i else w (Sum.inr (Sum.inr i))))) := by
    intro S
    have hbf : Cmp StS (Unit ⊕ Fin k) (600 * (k + 7) ^ 3)
        (fun w => Sum.elim
          (fun _ => bfOK k r S (fun a => w (Sum.inl (Sum.inr (Sum.inr (Sum.inl a)))))
            (fun a => w (Sum.inl (Sum.inr (Sum.inr (Sum.inr a))))))
          (bfP k r S (fun a => w (Sum.inl (Sum.inr (Sum.inr (Sum.inl a)))))
            (fun a => w (Sum.inl (Sum.inr (Sum.inr (Sum.inr a))))))) :=
      Cmp.sel (fun x => Sum.inl (Sum.inr (Sum.inr x))) (cmp_bf k r S)
    let StS2 := StS ⊕ (Unit ⊕ Fin k)
    have hokd : Cb StS2 ((m + 1) * 3 + 1)
        (fun u => decide (∃ t : Fin (m + 1),
          (decide (k - S.val + t.val ≤ b) && u (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Fin.last m, t)))))) = true)) := by
      have c := Cb.bigOr (I := Fin (m + 1)) (fun t =>
        Cb.and (Cb.const (ι := StS2) (decide (k - S.val + t.val ≤ b)))
          (Cb.var (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Fin.last m, t)))))))
      rw [Fintype.card_fin] at c
      exact Cb.mono (Cb.congr c (fun u => by rw [Bool.eq_iff_iff]; simp)) (by omega)
    have hokS : Cb StS2 ((m + 1) * 3 + 2)
        (fun u => decide (∃ t : Fin (m + 1),
          (decide (k - S.val + t.val ≤ b) && u (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Fin.last m, t)))))) = true) &&
          u (Sum.inr (Sum.inl ()))) :=
      Cb.mono (Cb.and hokd (Cb.var (Sum.inr (Sum.inl ())))) (by omega)
    let StS3 := StS2 ⊕ Unit
    have hupd : Cmp StS3 StS (5 * k + 8)
        (fun u => Sum.elim (fun x => u (Sum.inl (Sum.inl (Sum.inl x))))
          (Sum.elim (fun _ => u (Sum.inl (Sum.inl (Sum.inr (Sum.inl ())))) || u (Sum.inr ()))
            (fun i => if !u (Sum.inl (Sum.inl (Sum.inr (Sum.inl ())))) && u (Sum.inr ())
              then u (Sum.inl (Sum.inr (Sum.inr i)))
              else u (Sum.inl (Sum.inl (Sum.inr (Sum.inr i))))))) := by
      have htake : Cb StS3 2 (fun u => !u (Sum.inl (Sum.inl (Sum.inr (Sum.inl ())))) && u (Sum.inr ())) :=
        Cb.and (Cb.not (Cb.var _)) (Cb.var _)
      have hflag : Cb StS3 1 (fun u => u (Sum.inl (Sum.inl (Sum.inr (Sum.inl ())))) || u (Sum.inr ())) :=
        Cb.or (Cb.var _) (Cb.var _)
      have hP : Cmp (StS3 ⊕ Unit) (Fin k) (k * 4)
          (fun u i => if u (Sum.inr ()) then u (Sum.inl (Sum.inl (Sum.inr (Sum.inr i))))
            else u (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr i)))))) := by
        have h := Cmp.ofBits (ι := StS3 ⊕ Unit) (κ := Fin k) (s := 4)
          (F := fun u i => if u (Sum.inr ()) then u (Sum.inl (Sum.inl (Sum.inr (Sum.inr i))))
            else u (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr i)))))) (fun i =>
          Cb.mux (Cb.var (ι := StS3 ⊕ Unit) (Sum.inr ()))
            (Cb.var (ι := StS3 ⊕ Unit) (Sum.inl (Sum.inl (Sum.inr (Sum.inr i)))))
            (Cb.var (ι := StS3 ⊕ Unit) (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr i)))))))
        rw [Fintype.card_fin] at h
        exact h
      have hP' := Cmp.thn htake hP
      have hpair := Cmp.pair (Cmp.wire (ι := StS3) (fun x => Sum.inl (Sum.inl (Sum.inl x))))
        (Cmp.pair hflag hP')
      exact Cmp.mono (Cmp.congr hpair (fun u x => by rcases x with x | ⟨⟩ | i <;> rfl)) (by omega)
    have htot := Cmp.thn hbf (Cmp.thn hokS hupd)
    exact Cmp.mono (Cmp.congr htot (fun w x => by rcases x with x | ⟨⟩ | i <;> rfl)) (by omega)
  have hfold := Cmp.foldl (List.finRange (k + 1)) (fun S w =>
    Sum.elim (fun x => w (Sum.inl x))
      (let act := fun a => w (Sum.inl (Sum.inr (Sum.inr (Sum.inl a))))
       let inW := fun a => w (Sum.inl (Sum.inr (Sum.inr (Sum.inr a))))
       let okd := decide (∃ t : Fin (m + 1),
         (decide (k - S.val + t.val ≤ b) && w (Sum.inl (Sum.inr (Sum.inl (Fin.last m, t))))) = true)
       let okS := okd && bfOK k r S act inW
       let take := !w (Sum.inr (Sum.inl ())) && okS
       Sum.elim (fun _ => w (Sum.inr (Sum.inl ())) || okS)
         (fun i => if take then bfP k r S act inW i else w (Sum.inr (Sum.inr i)))))
    (fun S _ => hstepS S)
  have hinit : Cmp Pre StS (1 + k) (fun p => Sum.elim p (fun _ => false)) := by
    have h := Cmp.pair (Cmp.wire (ι := Pre) id)
      (Cmp.pair (Cb.const (ι := Pre) false) (Cmp.ofBits (ι := Pre) (κ := Fin k) (fun _ => Cb.const false)))
    rw [Fintype.card_fin] at h
    exact Cmp.mono (Cmp.congr h (fun p x => by rcases x with x | ⟨⟩ | i <;> rfl)) (by omega)
  have hout : Cmp StS ((Unit ⊕ Fin k) ⊕ (Fin m × Fin m)) 0
      (fun w => Sum.elim (fun x => w (Sum.inr x)) (fun p => w (Sum.inl (Sum.inl p)))) :=
    Cmp.congr (Cmp.wire (ι := StS) (fun x : (Unit ⊕ Fin k) ⊕ (Fin m × Fin m) =>
      Sum.elim Sum.inr (fun p => Sum.inl (Sum.inl p)) x)) (fun w x => by cases x <;> rfl)
  have hfull := Cmp.comp (Cmp.comp (Cmp.comp hprep hinit) hfold) hout
  refine Cmp.mono (Cmp.congr hfull ?_) ?_
  · intro v o
    let Rmm := R_tup (colOfRB r v) tup
    let preV : Pre → Bool := Sum.elim Rmm
      (Sum.elim (fun p => decide (cnt (fun q : Fin m => Rmm (q, q)) p.1.val = p.2.val))
        (Sum.elim (actOfRB r v) (inWOfRB r v Rmm)))
    have hfold_eq : ∀ (L : List (Fin (k + 1))) (acc : Unit ⊕ Fin k → Bool),
        L.foldl (fun w S => Sum.elim (fun x => w (Sum.inl x))
          (let act := fun a => w (Sum.inl (Sum.inr (Sum.inr (Sum.inl a))))
           let inW := fun a => w (Sum.inl (Sum.inr (Sum.inr (Sum.inr a))))
           let okd := decide (∃ t : Fin (m + 1),
             (decide (k - S.val + t.val ≤ b) && w (Sum.inl (Sum.inr (Sum.inl (Fin.last m, t))))) = true)
           let okS := okd && bfOK k r S act inW
           let take := !w (Sum.inr (Sum.inl ())) && okS
           Sum.elim (fun _ => w (Sum.inr (Sum.inl ())) || okS)
             (fun i => if take then bfP k r S act inW i else w (Sum.inr (Sum.inr i)))))
          (Sum.elim preV acc) =
        Sum.elim preV (L.foldl (fun a S => tupStepS (r := r) (b := b) v tup S a) acc) := by
      intro L
      induction L with
      | nil => intro acc; rfl
      | cons S L ih =>
        intro acc
        rw [List.foldl_cons, List.foldl_cons]
        have hstep_eq : (Sum.elim (fun x => (Sum.elim preV acc) (Sum.inl x))
            (let act := fun a => (Sum.elim preV acc) (Sum.inl (Sum.inr (Sum.inr (Sum.inl a))))
             let inW := fun a => (Sum.elim preV acc) (Sum.inl (Sum.inr (Sum.inr (Sum.inr a))))
             let okd := decide (∃ t : Fin (m + 1),
               (decide (k - S.val + t.val ≤ b) && (Sum.elim preV acc) (Sum.inl (Sum.inr (Sum.inl (Fin.last m, t))))) = true)
             let okS := okd && bfOK k r S act inW
             let take := !(Sum.elim preV acc) (Sum.inr (Sum.inl ())) && okS
             Sum.elim (fun _ => (Sum.elim preV acc) (Sum.inr (Sum.inl ())) || okS)
               (fun i => if take then bfP k r S act inW i else (Sum.elim preV acc) (Sum.inr (Sum.inr i))))) =
            Sum.elim preV (tupStepS (r := r) (b := b) v tup S acc) := by
          have hokd_eq : decide (∃ t : Fin (m + 1),
              (decide (k - S.val + t.val ≤ b) && (Sum.elim preV acc) (Sum.inl (Sum.inr (Sum.inl (Fin.last m, t))))) = true) =
              decide (k - S.val + rhoM Rmm ≤ b) := by
            rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
            simp only [preV, Sum.elim_inr, Sum.elim_inl, Fin.val_last, cnt_full, Bool.and_eq_true,
              decide_eq_true_eq]
            constructor
            · rintro ⟨t, h1, h2⟩; dsimp only [rhoM]; rw [h2]; exact h1
            · intro h1
              have hle : rhoM Rmm ≤ m := by
                unfold rhoM
                calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.filter_subset _ _)
                  _ = m := by simp
              exact ⟨⟨rhoM Rmm, by omega⟩, h1, rfl⟩
          funext x
          rcases x with x | ⟨⟩ | i
          · rfl
          · change (acc (Sum.inl ()) || (decide (∃ t : Fin (m + 1),
                (decide (k - S.val + t.val ≤ b) && (Sum.elim preV acc) (Sum.inl (Sum.inr (Sum.inl (Fin.last m, t))))) = true) &&
                bfOK k r S (actOfRB r v) (inWOfRB r v Rmm))) =
              (acc (Sum.inl ()) || (decide (k - S.val + rhoM Rmm ≤ b) && bfOK k r S (actOfRB r v) (inWOfRB r v Rmm)))
            rw [hokd_eq]
          · change (if (!acc (Sum.inl ()) && (decide (∃ t : Fin (m + 1),
                (decide (k - S.val + t.val ≤ b) && (Sum.elim preV acc) (Sum.inl (Sum.inr (Sum.inl (Fin.last m, t))))) = true) &&
                bfOK k r S (actOfRB r v) (inWOfRB r v Rmm))) then bfP k r S (actOfRB r v) (inWOfRB r v Rmm) i
                else acc (Sum.inr i)) =
              (if (!acc (Sum.inl ()) && (decide (k - S.val + rhoM Rmm ≤ b) && bfOK k r S (actOfRB r v) (inWOfRB r v Rmm)))
                then bfP k r S (actOfRB r v) (inWOfRB r v Rmm) i else acc (Sum.inr i))
            rw [hokd_eq]
        rw [hstep_eq, ih]
    rcases o with x | p
    · change (List.foldl _ (Sum.elim preV (fun _ => false)) (List.finRange (k + 1))) (Sum.inr x) = _
      rw [hfold_eq (List.finRange (k + 1)) (fun _ => false)]; rfl
    · change (List.foldl _ (Sum.elim preV (fun _ => false)) (List.finRange (k + 1))) (Sum.inl (Sum.inl p)) = _
      rw [hfold_eq (List.finRange (k + 1)) (fun _ => false)]; rfl
  · rw [List.length_finRange]
    have hkN : k + 1 ≤ N := by dsimp only [N]; omega
    have hmN : m + 1 ≤ N := by dsimp only [N]; omega
    have h6N : 6 ≤ N := by dsimp only [N]; omega
    have hA : 600 * (m + 1) ^ 4 ≤ 600 * N ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmN 4)
    have hB : (m + 1) * ((m + 1) * 6) + (2 * k * (m + 1) + 2 * k * (m * (m * 5 + 7) + 1)) + (1 + k) ≤ 20 * N ^ 4 := by
      have hmle : m ≤ N := by omega
      have hkle : k ≤ N := by omega
      have h1 : (m + 1) * ((m + 1) * 6) ≤ 6 * N ^ 2 := by
        calc (m + 1) * ((m + 1) * 6) ≤ N * (N * 6) := by gcongr
          _ = 6 * N ^ 2 := by ring
      have h2 : 2 * k * (m + 1) ≤ 2 * N ^ 2 := by
        calc 2 * k * (m + 1) ≤ 2 * N * N := by gcongr
          _ = 2 * N ^ 2 := by ring
      have h3 : 2 * k * (m * (m * 5 + 7) + 1) ≤ 10 * N ^ 3 + 16 * N ^ 2 := by
        have : m * (m * 5 + 7) + 1 ≤ 5 * N ^ 2 + 8 * N := by nlinarith
        calc 2 * k * (m * (m * 5 + 7) + 1) ≤ 2 * N * (5 * N ^ 2 + 8 * N) := by gcongr
          _ = 10 * N ^ 3 + 16 * N ^ 2 := by ring
      have hN14 : N ≤ N ^ 4 := by
        calc N = N ^ 1 := by ring
          _ ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have hN24 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have hN34 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have hN23 : 24 * N ^ 2 ≤ 4 * N ^ 4 := by
        have : N ^ 4 = N ^ 2 * N ^ 2 := by ring
        have : 36 ≤ N ^ 2 := by nlinarith
        nlinarith
      have hN34' : 10 * N ^ 3 ≤ 2 * N ^ 4 := by
        have : N ^ 4 = N * N ^ 3 := by ring
        nlinarith
      omega
    have hC : (k + 1) * (600 * (k + 7) ^ 3 + 3 * m + 5 * k + 15) ≤ 1000 * N ^ 5 := by
      have h1 : k + 7 ≤ N + 1 := by dsimp only [N]; omega
      have h2 : (k + 7) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left h1 3
      have h3 : (N + 1) ^ 3 ≤ 2 * N ^ 3 := by
        have : (N + 1) ^ 3 = N ^ 3 + 3 * N ^ 2 + 3 * N + 1 := by ring
        have : 3 * N ^ 2 + 3 * N + 1 ≤ N ^ 3 := by
          have : N ^ 3 = N * N ^ 2 := by ring
          nlinarith
        omega
      have h4 : 600 * (k + 7) ^ 3 + 3 * m + 5 * k + 15 ≤ 1300 * N ^ 3 := by
        have : 3 * m + 5 * k + 15 ≤ 100 * N ^ 3 := by
          have : 3 * m + 5 * k + 15 ≤ 15 * N := by dsimp only [N]; omega
          have : N ≤ N ^ 3 := by
            calc N = N ^ 1 := by ring
              _ ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
          omega
        omega
      have h5 : (k + 1) * (1300 * N ^ 3) ≤ N * (1300 * N ^ 3) := Nat.mul_le_mul_right _ hkN
      have h6 : N * (1300 * N ^ 3) = 1300 * N ^ 4 := by ring
      have h7 : 1300 * N ^ 4 ≤ 1000 * N ^ 5 := by
        calc 1300 * N ^ 4 ≤ 1000 * 6 * N ^ 4 := by omega
          _ ≤ 1000 * N * N ^ 4 := by gcongr
          _ = 1000 * N ^ 5 := by ring
      calc (k + 1) * (600 * (k + 7) ^ 3 + 3 * m + 5 * k + 15)
          ≤ (k + 1) * (1300 * N ^ 3) := Nat.mul_le_mul_left _ h4
        _ ≤ 1000 * N ^ 5 := by omega
    have hN45 : N ^ 4 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

theorem cmp_phase1 (k r m b h' : ℕ) (hhm : h' ≤ m) :
    Cmp (RBIn k m) (P1Out k m) ((2 * k + 1) ^ h' * (4096 * (k + r + m + 6) ^ 5) + (k + m + 1) ^ 2)
      (phase1Out k r m b h') := by
  set N := k + r + m + 6
  let StP := RBIn k m ⊕ P1Out k m
  have hstep : ∀ tup : Fin h' → Option (Bool × Fin k),
      Cmp StP StP (4096 * N ^ 5)
        (fun w => Sum.elim (fun x => w (Sum.inl x))
          (p1Step (r := r) (b := b) tup (fun x => w (Sum.inl x)) (fun x => w (Sum.inr x)))) := by
    intro tup
    have hts : Cmp StP ((Unit ⊕ Fin k) ⊕ (Fin m × Fin m)) (2048 * N ^ 5)
        (fun w => Sum.elim (tupSolve (r := r) (b := b) (fun x => w (Sum.inl x)) tup)
          (R_tup (colOfRB r (fun x => w (Sum.inl x))) tup)) :=
      Cmp.sel Sum.inl (cmp_tupSolve k r m b h' hhm tup)
    let StP2 := StP ⊕ ((Unit ⊕ Fin k) ⊕ (Fin m × Fin m))
    have htake : Cb StP2 2
        (fun u => !u (Sum.inl (Sum.inr (Sum.inl ()))) && u (Sum.inr (Sum.inl (Sum.inl ())))) :=
      Cb.and (Cb.not (Cb.var _)) (Cb.var _)
    let StP3 := StP2 ⊕ Unit
    have hupd : Cmp StP3 StP (1 + k * 4 + m * m * 4)
        (fun u => Sum.elim (fun x => u (Sum.inl (Sum.inl (Sum.inl x))))
          (Sum.elim (fun _ => u (Sum.inl (Sum.inl (Sum.inr (Sum.inl ())))) ||
              u (Sum.inl (Sum.inr (Sum.inl (Sum.inl ())))))
            (Sum.elim (fun i => if u (Sum.inr ()) then u (Sum.inl (Sum.inr (Sum.inl (Sum.inr i))))
                else u (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inl i))))))
              (fun p => if u (Sum.inr ()) then u (Sum.inl (Sum.inr (Sum.inr p)))
                else u (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr p))))))))) := by
      have hf : Cb StP3 1 (fun u => u (Sum.inl (Sum.inl (Sum.inr (Sum.inl ())))) ||
          u (Sum.inl (Sum.inr (Sum.inl (Sum.inl ()))))) := Cb.or (Cb.var _) (Cb.var _)
      have hP : Cmp StP3 (Fin k) (k * 4)
          (fun u i => if u (Sum.inr ()) then u (Sum.inl (Sum.inr (Sum.inl (Sum.inr i))))
            else u (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))))) := by
        have h := Cmp.ofBits (ι := StP3) (κ := Fin k) (s := 4)
          (F := fun u i => if u (Sum.inr ()) then u (Sum.inl (Sum.inr (Sum.inl (Sum.inr i))))
            else u (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))))) (fun i =>
          Cb.mux (Cb.var (ι := StP3) (Sum.inr ()))
            (Cb.var (ι := StP3) (Sum.inl (Sum.inr (Sum.inl (Sum.inr i)))))
            (Cb.var (ι := StP3) (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))))))
        rw [Fintype.card_fin] at h; exact h
      have hR : Cmp StP3 (Fin m × Fin m) (m * m * 4)
          (fun u p => if u (Sum.inr ()) then u (Sum.inl (Sum.inr (Sum.inr p)))
            else u (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr p)))))) := by
        have h := Cmp.ofBits (ι := StP3) (κ := Fin m × Fin m) (s := 4)
          (F := fun u p => if u (Sum.inr ()) then u (Sum.inl (Sum.inr (Sum.inr p)))
            else u (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr p)))))) (fun p =>
          Cb.mux (Cb.var (ι := StP3) (Sum.inr ()))
            (Cb.var (ι := StP3) (Sum.inl (Sum.inr (Sum.inr p))))
            (Cb.var (ι := StP3) (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr p)))))))
        simp only [Fintype.card_prod, Fintype.card_fin] at h; exact h
      have hp := Cmp.pair (Cmp.wire (ι := StP3) (fun x => Sum.inl (Sum.inl (Sum.inl x))))
        (Cmp.pair hf (Cmp.pair hP hR))
      exact Cmp.mono (Cmp.congr hp (fun u x => by rcases x with x | ⟨⟩ | i | p <;> rfl)) (by omega)
    have htot := Cmp.thn hts (Cmp.thn htake hupd)
    refine Cmp.mono (Cmp.congr htot (fun w x => by rcases x with x | ⟨⟩ | i | p <;> rfl)) ?_
    have hkN : k ≤ N := by dsimp only [N]; omega
    have hmN : m ≤ N := by dsimp only [N]; omega
    have h6N : 6 ≤ N := by dsimp only [N]; omega
    have : 2 + (1 + k * 4 + m * m * 4) ≤ 2048 * N ^ 5 := by
      have h1 : N ^ 2 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have h2 : N ^ 2 = N * N := by ring
      nlinarith
    omega
  have hinit : Cmp (RBIn k m) StP ((k + m + 1) ^ 2) (fun v => Sum.elim v (fun _ => false)) := by
    have h := Cmp.pair (Cmp.wire (ι := RBIn k m) id)
      (Cmp.pair (Cb.const (ι := RBIn k m) false)
        (Cmp.pair (Cmp.ofBits (ι := RBIn k m) (κ := Fin k) (fun _ => Cb.const false))
          (Cmp.ofBits (ι := RBIn k m) (κ := Fin m × Fin m) (fun _ => Cb.const false))))
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Cmp.mono (Cmp.congr h (fun v x => by rcases x with x | ⟨⟩ | i | p <;> rfl)) (by nlinarith)
  have hfold := Cmp.foldl (Finset.univ : Finset (Fin h' → Option (Bool × Fin k))).toList
    (fun tup w => Sum.elim (fun x => w (Sum.inl x))
      (p1Step (r := r) (b := b) tup (fun x => w (Sum.inl x)) (fun x => w (Sum.inr x))))
    (fun tup _ => hstep tup)
  have htot := Cmp.comp (Cmp.comp hinit hfold) (Cmp.wire (ι := StP) Sum.inr)
  have hlen : (Finset.univ : Finset (Fin h' → Option (Bool × Fin k))).toList.length = (2 * k + 1) ^ h' := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_fun, Fintype.card_option,
      Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, add_comm]
  rw [hlen] at htot
  refine Cmp.mono (Cmp.congr htot ?_) (by omega)
  intro v o
  have hf : ∀ (L : List (Fin h' → Option (Bool × Fin k))) (acc : P1Out k m → Bool),
      L.foldl (fun w tup => Sum.elim (fun x => w (Sum.inl x))
        (p1Step (r := r) (b := b) tup (fun x => w (Sum.inl x)) (fun x => w (Sum.inr x))))
        (Sum.elim v acc) =
      Sum.elim v (L.foldl (fun a tup => p1Step (r := r) (b := b) tup v a) acc) := by
    intro L
    induction L with
    | nil => intro acc; rfl
    | cons tup L ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons]
      have : (Sum.elim (fun x => (Sum.elim v acc) (Sum.inl x))
          (p1Step (r := r) (b := b) tup (fun x => (Sum.elim v acc) (Sum.inl x))
            (fun x => (Sum.elim v acc) (Sum.inr x)))) =
          Sum.elim v (p1Step (r := r) (b := b) tup v acc) := rfl
      rw [this, ih]
  change (List.foldl _ (Sum.elim v (fun _ => false)) _) (Sum.inr o) = _
  rw [hf]
  rfl

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
      Finset.mem_univ, ite_true]
  · simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
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
      Finset.mem_univ, ite_true, add_mul, ite_mul, zero_mul]
    rw [Finset.mul_sum, Finset.mul_sum]
    by_cases hi : a = i <;> by_cases hj : a = j <;> simp [hi, hj] <;> ring_nf
  rw [Finset.sum_congr rfl (fun a _ => e a)]
  simp only [Finset.sum_add_distrib, add_mul, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
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
    · subst ha; simp [Ne.symm hij, toZ_false]
    · by_cases hb : a = i
      · subst hb; simp [ha, toZ_false]
      · simp [ha, hb, toZ_true]
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
    · subst haj; simp [toZ_false]
    · by_cases hai : a = i
      · subst hai; simp [haj, toZ_false]
      · simp [haj, hai, toZ_xor]; ring
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
    · subst haj; simp [toZ_false]
    · by_cases hai : a = i
      · subst hai; simp [haj, toZ_false]
      · simp [haj, hai, toZ_xor]; ring
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
    · subst ha; simp [toZ_false]
    · simp [ha, toZ_true]
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
        simp [toZ_false]
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
      apply Finset.sum_eq_zero; intro a _; simp [(h a).1, toZ_false]
    have h2 : ∑ a, ∑ b, toZ (γ (a, b)) * u a * u b = 0 := by
      apply Finset.sum_eq_zero; intro a _
      apply Finset.sum_eq_zero; intro b _
      simp [((h a).2 b).1, toZ_false]
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
    simp only [Bool.false_eq_true, ite_false]
    cases hc : s.c
    · rw [hc] at h2
      simp only [toZ_false, sgnZ_zero, mul_one] at h2
      simp only [Bool.false_eq_true, ite_false]
      push_cast
      exact mul_right_cancel₀ hp h2
    · rw [hc] at h2
      simp only [toZ_true, sgnZ_one] at h2
      simp only [ite_true]
      push_cast
      exact mul_right_cancel₀ hp (by rw [h2]; ring)
  · simp only [ite_true]
    exact hinv.1 hz

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
    · simp only [ha, ite_true]
      have hdiv : 2 ^ k / 2 ^ (s.n3 + 1) = 2 ^ k / 2 ^ s.n3 / 2 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      rw [hdiv]
      by_cases ht : t.val + 1 < W
      · rw [dite_eq_left ht]
        show (2 ^ k / 2 ^ s.n3).testBit (t.val + 1) = _
        rw [Nat.testBit_succ]
      · rw [dite_eq_right ht]
        symm
        apply Nat.testBit_lt_two_pow
        have h1 : 2 ^ k / 2 ^ s.n3 / 2 < 2 ^ k := by
          have := Nat.div_le_self (2 ^ k) (2 ^ s.n3)
          have h2 : 0 < 2 ^ k := by positivity
          omega
        have h3 : 2 ^ k ≤ 2 ^ t.val := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    · simp only [Bool.not_eq_true] at ha
      simp only [ha, Bool.false_eq_true, ite_false, add_zero]
      rfl

theorem gfoldW {k W : ℕ} (hW : k < W) (L : List (Fin k)) (s : GSt k) :
    L.foldl (fun w i => gstepW i w) (genc W s) = genc W (gfold L s) := by
  induction L generalizing s with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldl_cons]
    rw [gstepW_enc hW, ih]
    rfl

theorem cbS {k W : ℕ} (i : Fin k) (b : Fin k) : Cb (GW k W) 6 (fun w => gS i (gga w) b) :=
  Cb.mono (Cb.and (Cb.const _) (Cb.xor (Cb.var _) (Cb.var _))) (by norm_num)

theorem cbSel {k W : ℕ} (i : Fin k) (b : Fin k) :
    Cb (GW k W) (10 * (k + 1)) (fun w => gSel i (gga w) b) := by
  have c := Cb.and (cbS (W := W) i b) (Cb.not (Cb.bigOr (fun b' : Fin k =>
    Cb.and (Cb.const (decide (b' < b))) (cbS (W := W) i b'))))
  simp only [Fintype.card_fin] at c
  refine Cb.mono (Cb.congr c (fun w => by unfold gSel; congr)) ?_
  ring_nf; omega

theorem cbAny {k W : ℕ} (i : Fin k) : Cb (GW k W) (8 * (k + 1)) (fun w => gAny i (gga w)) := by
  have c := Cb.bigOr (fun b : Fin k => cbS (W := W) i b)
  simp only [Fintype.card_fin] at c
  refine Cb.mono (Cb.congr c (fun w => by unfold gAny; congr)) ?_
  ring_nf; omega

theorem cbA0 {k W : ℕ} (i : Fin k) : Cb (GW k W) 4 (fun w => gA0 i (gal w) (gga w)) :=
  Cb.mono (Cb.congr (Cb.xor (Cb.var (Sum.inr (Sum.inr (Sum.inl i))))
    (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, i))))))) (fun w => rfl)) (by norm_num)

theorem cbB0 {k W : ℕ} (i : Fin k) :
    Cb (GW k W) (20 * (k + 1) ^ 2) (fun w => gB0 i (gal w) (gga w)) := by
  have c := Cb.bigOr (fun b : Fin k => Cb.and (cbSel (W := W) i b)
    (Cb.xor (Cb.var (Sum.inr (Sum.inr (Sum.inl b))))
      (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl (b, b))))))))
  simp only [Fintype.card_fin] at c
  refine Cb.mono (Cb.congr c (fun w => by unfold gB0; congr)) ?_
  ring_nf; nlinarith

theorem cbKeep {k W : ℕ} (i : Fin k) (a : Fin k) :
    Cb (GW k W) (20 * (k + 1)) (fun w => gKeep i (gga w) a) := by
  have c := Cb.and (Cb.const (ι := GW k W) (decide (a ≠ i))) (Cb.not (cbSel (W := W) i a))
  refine Cb.mono (Cb.congr c (fun w => rfl)) ?_
  nlinarith

theorem cbAA {k W : ℕ} (i : Fin k) (a : Fin k) :
    Cb (GW k W) (20 * (k + 1)) (fun w => gAA i (gga w) a) := by
  have c := Cb.and (cbS (W := W) i a) (Cb.not (cbSel (W := W) i a))
  refine Cb.mono (Cb.congr c (fun w => rfl)) ?_
  nlinarith

theorem cbBB {k W : ℕ} (i : Fin k) (a : Fin k) :
    Cb (GW k W) (50 * (k + 1) ^ 2) (fun w => gBB i (gga w) a) := by
  have c := Cb.and (cbKeep (W := W) i a) (Cb.bigOr (fun b : Fin k => Cb.and (cbSel (W := W) i b)
    (Cb.xor (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl (a, b))))))
      (Cb.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl (b, a)))))))))
  simp only [Fintype.card_fin] at c
  refine Cb.mono (Cb.congr c (fun w => by unfold gBB; congr)) ?_
  ring_nf; nlinarith

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

def ginit {k : ℕ} (P : Fin (k + 1) × Fin (k + 1) → Bool) : GSt k :=
  ⟨false, P (Fin.last k, Fin.last k),
    fun q => xor (P (q.castSucc, Fin.last k)) (P (Fin.last k, Fin.last k)),
    fun p => decide (p.1 < p.2) && xor (xor (xor (P (p.1.castSucc, p.2.castSucc))
      (P (p.1.castSucc, Fin.last k))) (P (p.2.castSucc, Fin.last k))) (P (Fin.last k, Fin.last k)),
    0⟩

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

theorem shr_ofNat {W n : ℕ} (hn : n < 2 ^ W) :
    (BitVec.ofNat W n) >>> 1 = BitVec.ofNat W (n / 2) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
  by_cases hi1 : 1 + i < W
  · simp only [hi, hi1, decide_true, Bool.true_and]
    rw [show (2 : ℕ) = 2 ^ 1 from rfl, Nat.testBit_div_two_pow, Nat.add_comm 1 i]
  · simp only [hi, hi1, decide_false, Bool.false_and, decide_true, Bool.true_and]
    symm
    apply Nat.testBit_lt_two_pow
    have h1 : 2 ^ W = 2 * 2 ^ (W - 1) := by
      have : W = (W - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ, mul_comm]
    have h2 : i = W - 1 := by omega
    rw [h2]; omega

theorem foldl_shr_ofNat {α : Type} {W : ℕ} (f : α → Bool) (L : List α) :
    ∀ (n : ℕ), n < 2 ^ W →
      L.foldl (fun (x : BitVec W) a => if f a then x >>> 1 else x) (BitVec.ofNat W n) =
      BitVec.ofNat W (n / 2 ^ (L.countP f)) := by
  induction L with
  | nil => intro n _; simp
  | cons a L ih =>
    intro n hn
    simp only [List.foldl_cons, List.countP_cons]
    cases hf : f a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih n hn
    · simp only [ite_true]
      rw [shr_ofNat hn, ih (n / 2) (lt_of_le_of_lt (Nat.div_le_self n 2) hn),
        Nat.div_div_eq_div_mul, ← pow_succ']

theorem dbl_ofNat {W n : ℕ} :
    (BitVec.ofNat W n) <<< 1 = BitVec.ofNat W (2 * n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hi0 : i = 0
  · subst hi0; simp
  · have hlt : ¬ i < 1 := by omega
    have h1 : i - 1 < W := by omega
    have h2 : i = (i - 1) + 1 := by omega
    simp only [hlt, decide_false, Bool.not_false, Bool.true_and, h1, decide_true]
    conv_rhs => rw [h2, Nat.testBit_succ, Nat.mul_div_right n (by norm_num)]

theorem foldl_dbl_ofNat {α : Type} {W : ℕ} (f : α → Bool) (L : List α) :
    ∀ (n : ℕ),
      L.foldl (fun (x : BitVec W) a => if f a then x <<< 1 else x) (BitVec.ofNat W n) =
      BitVec.ofNat W (2 ^ (L.countP f) * n) := by
  induction L with
  | nil => intro n; simp
  | cons a L ih =>
    intro n
    simp only [List.foldl_cons, List.countP_cons]
    cases hf : f a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih n
    · simp only [ite_true]
      rw [dbl_ofNat, ih (2 * n)]
      congr 1; rw [pow_succ]; ring

theorem countP_finRange {N : ℕ} (f : Fin N → Bool) :
    (List.finRange N).countP f = (Finset.univ.filter (fun i : Fin N => f i = true)).card := by
  rw [List.countP_eq_length_filter]
  have hnodup : ((List.finRange N).filter (fun i => f i)).Nodup :=
    (List.nodup_finRange N).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  congr 1; ext i; simp

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

theorem isAff_sum_finset {k : ℕ} {ι : Type} (S : Finset ι) {P : ι → V k → ZMod 2}
    (h : ∀ t ∈ S, IsAff (P t)) : IsAff (fun u => ∑ t ∈ S, P t u) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isAff_const (k := k) 0
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).add (ih (fun t ht => h t (Finset.mem_insert_of_mem ht)))
    simpa [Finset.sum_insert ha] using h1

theorem isAff_sum {k : ℕ} {ι : Type} [Fintype ι] {P : ι → V k → ZMod 2}
    (h : ∀ t, IsAff (P t)) : IsAff (fun u => ∑ t, P t u) :=
  isAff_sum_finset Finset.univ (fun t _ => h t)

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

theorem isQuad_sum_finset {k : ℕ} {ι : Type} (S : Finset ι) {P : ι → V k → ZMod 2}
    (h : ∀ t ∈ S, IsQuad (P t)) : IsQuad (fun u => ∑ t ∈ S, P t u) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isQuad_const (k := k) 0
  | insert a s ha ih =>
    have h1 := (h a (Finset.mem_insert_self a s)).add (ih (fun t ht => h t (Finset.mem_insert_of_mem ht)))
    simpa [Finset.sum_insert ha] using h1

theorem isQuad_sum {k : ℕ} {ι : Type} [Fintype ι] {P : ι → V k → ZMod 2}
    (h : ∀ t, IsQuad (P t)) : IsQuad (fun u => ∑ t, P t u) :=
  isQuad_sum_finset Finset.univ (fun t _ => h t)

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

theorem IsAff.congr {k : ℕ} {P Q : V k → ZMod 2} (hP : IsAff P) (h : ∀ u, P u = Q u) :
    IsAff Q := by
  obtain ⟨c, α, hP⟩ := hP
  exact ⟨c, α, fun u => by rw [← h u, hP u]⟩

theorem IsQuad.comp_aff {k : ℕ} {P : V k → ZMod 2} (hP : IsQuad P) {L : V k → V k}
    (hL : ∀ i, IsAff (fun u => L u i)) : IsQuad (fun u => P (L u)) := by
  obtain ⟨c, α, γ, hP⟩ := hP
  have h1 : IsQuad (fun u => c + ∑ a, α a * L u a) :=
    (isQuad_const c).add (isAff_sum (fun a => (hL a).smul (α a))).quad
  have h2 : IsQuad (fun u => ∑ a, ∑ b, γ a b * L u a * L u b) :=
    isQuad_sum (fun a => isQuad_sum (fun b =>
      IsQuad.congr (((hL a).smul (γ a b)).mul (hL b)) (fun _ => rfl)))
  exact (h1.add h2).congr (fun u => by rw [hP (L u)]; rfl)

def e1 {k : ℕ} (q : Fin k) : V k := fun a => if a = q then 1 else 0

def Δ2 {k : ℕ} (P : V k → ZMod 2) (v w : V k) : ZMod 2 := P (v + w) + P v + P w + P 0

theorem isAff_of_dep_le_one {k : ℕ} {g : V k → ZMod 2} {S : Finset (Fin k)} (hS : S.card ≤ 1)
    (hdep : ∀ x y : V k, (∀ i ∈ S, x i = y i) → g x = g y) : IsAff g := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hS with h0 | h1
  · have hE : S = ∅ := Finset.card_eq_zero.1 h0
    refine (isAff_const (g 0)).congr (fun u => ?_)
    exact (hdep u 0 (fun i hi => by rw [hE] at hi; exact absurd hi (Finset.notMem_empty i))).symm
  · obtain ⟨i0, rfl⟩ := Finset.card_eq_one.1 h1
    refine ⟨g 0, fun a => if a = i0 then g (e1 i0) + g 0 else 0, fun u => ?_⟩
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rcases z01 (u i0) with h | h
    · have hgu : g u = g 0 := hdep u 0 (fun i hi => by
        rw [Finset.mem_singleton.1 hi]; exact h)
      rw [hgu, h, mul_zero, add_zero]
    · have hgu : g u = g (e1 i0) := hdep u (e1 i0) (fun i hi => by
        rw [Finset.mem_singleton.1 hi]; simp [e1, h])
      rw [hgu, h, mul_one]
      have hz := z2 (g 0)
      linear_combination -hz

theorem isQuad_of_dep_le_two {k : ℕ} {g : V k → ZMod 2} {S : Finset (Fin k)} (hS : S.card ≤ 2)
    (hdep : ∀ x y : V k, (∀ i ∈ S, x i = y i) → g x = g y) : IsQuad g := by
  by_cases h1 : S.card ≤ 1
  · exact (isAff_of_dep_le_one h1 hdep).quad
  · have h2 : S.card = 2 := by omega
    obtain ⟨i0, i1, hne, rfl⟩ := Finset.card_eq_two.1 h2
    refine ⟨g 0, fun a => (if a = i0 then g (e1 i0) + g 0 else 0) +
        (if a = i1 then g (e1 i1) + g 0 else 0),
      fun a b => if a = i0 ∧ b = i1 then Δ2 g (e1 i0) (e1 i1) else 0, fun u => ?_⟩
    unfold evalQZ
    have hs1 : ∑ a, ((if a = i0 then g (e1 i0) + g 0 else 0) +
        (if a = i1 then g (e1 i1) + g 0 else 0)) * u a =
        (g (e1 i0) + g 0) * u i0 + (g (e1 i1) + g 0) * u i1 := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    have hs2 : ∑ a, ∑ b, (if a = i0 ∧ b = i1 then Δ2 g (e1 i0) (e1 i1) else 0) * u a * u b =
        Δ2 g (e1 i0) (e1 i1) * u i0 * u i1 := by
      rw [Finset.sum_eq_single i0]
      · rw [Finset.sum_eq_single i1]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [ha]
      · simp
    rw [hs1, hs2]
    rcases z01 (u i0) with h0 | h0 <;> rcases z01 (u i1) with h1' | h1'
    · have hgu : g u = g 0 := hdep u 0 (fun i hi => by
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h0
        · rw [Finset.mem_singleton.1 hi]; exact h1')
      rw [hgu, h0, h1']; ring
    · have hgu : g u = g (e1 i1) := hdep u (e1 i1) (fun i hi => by
        rcases Finset.mem_insert.1 hi with rfl | hi
        · simp [e1, hne, h0]
        · rw [Finset.mem_singleton.1 hi]; simp [e1, h1'])
      rw [hgu, h0, h1']; have := z2 (g 0); linear_combination -this
    · have hgu : g u = g (e1 i0) := hdep u (e1 i0) (fun i hi => by
        rcases Finset.mem_insert.1 hi with rfl | hi
        · simp [e1, h0]
        · rw [Finset.mem_singleton.1 hi]; simp [e1, Ne.symm hne, h1'])
      rw [hgu, h0, h1']; have := z2 (g 0); linear_combination -this
    · have hgu : g u = g (e1 i0 + e1 i1) := hdep u (e1 i0 + e1 i1) (fun i hi => by
        rcases Finset.mem_insert.1 hi with rfl | hi
        · simp [e1, hne, h0]
        · rw [Finset.mem_singleton.1 hi]; simp [e1, Ne.symm hne, h1'])
      rw [hgu, h0, h1']; unfold Δ2
      have z0 := z2 (g 0); have za := z2 (g (e1 i0)); have zb := z2 (g (e1 i1))
      linear_combination -(2 * z0 + za + zb)

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
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
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
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
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
    · rw [ite_eq_left h, ite_eq_left h, hd q r h]
    · rw [ite_eq_right h, ite_eq_right h]
  have e3 : ∑ q, u q * (α q + γ q q) = ∑ a, α a * u a + ∑ a, γ a a * u a := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro a _; ring
  rw [hP u]
  unfold evalQZ
  rw [dsum_split]
  simp only [he, e2]
  rw [hz, e3]; ring

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

theorem interp_aff {k : ℕ} {P : V k → ZMod 2} (hP : IsAff P) (u : V k) :
    P u = P 0 + ∑ q, u q * (P (e1 q) + P 0) := by
  rw [interp hP.quad u]
  simp [hP.delta]

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
  simp [hz, toZ_false]

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
  simp [hq, hl, toZ_false, toZ_true] at this

theorem piR_aff {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) (i : Fin k) :
    IsAff (fun u => piR R u i) := by
  refine ⟨toZ (R (Fin.castSucc i, Fin.last k)),
    fun q => (if q = i then 1 else 0) + toZ (R (Fin.castSucc i, Fin.castSucc q)), fun u => ?_⟩
  simp only [piR, mulVec_ext, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

def npiv {k : ℕ} (R : Fin (k + 1) × Fin (k + 1) → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => R (Fin.castSucc i, Fin.castSucc i) = true)).card

theorem piR_dep {k : ℕ} {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R) (u v : V k)
    (h : ∀ i, R (Fin.castSucc i, Fin.castSucc i) = false → u i = v i) : piR R u = piR R v := by
  funext i
  simp only [piR, mulVec_ext]
  have e : ∀ w : V k, w i + (∑ q, toZ (R (Fin.castSucc i, Fin.castSucc q)) * w q +
      toZ (R (Fin.castSucc i, Fin.last k))) =
      ∑ q, ((if q = i then 1 else 0) + toZ (R (Fin.castSucc i, Fin.castSucc q))) * w q +
        toZ (R (Fin.castSucc i, Fin.last k)) := by
    intro w
    simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring
  rw [e u, e v]
  congr 1
  apply Finset.sum_congr rfl; intro q _
  by_cases hq : R (Fin.castSucc q, Fin.castSucc q) = true
  · have := hR.1.1 _ hq (Fin.castSucc i)
    rw [this]
    by_cases hqi : q = i
    · subst hqi; simp [toZ_true, z2]
    · simp [hqi, Ne.symm hqi, toZ_false]
  · rw [h q (by simpa using hq)]

theorem fiber_sum {k : ℕ} {R : Fin (k + 1) × Fin (k + 1) → Bool} (hR : FlatOK R) (hc : cons R)
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
      · simp only [hi, Bool.false_eq_true, ite_false, Finset.mem_singleton]
        have := congrFun hu i
        simp only [piR, mulVec_ext, hR.1.2 _ (by simpa using hi), toZ_false, zero_mul,
          Finset.sum_const_zero, add_zero] at this
        exact this
    · intro hu
      rw [← hfix]
      apply piR_dep hR
      intro i hi
      have := hu i
      simp only [hi, Bool.false_eq_true, ite_false, Finset.mem_singleton] at this
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

theorem cnt_surj {N : ℕ} (fl : Fin N → Bool) (s : ℕ)
    (hs : s < (Finset.univ.filter (fun q : Fin N => fl q = true)).card) :
    ∃ i : Fin N, fl i = true ∧ cnt fl i.val = s := by
  classical
  let T : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => s < cnt fl (i.val + 1))
  have hT : T.Nonempty := by
    have hN : 0 < N := by
      by_contra h0
      have hN0 : N = 0 := by omega
      subst hN0; simp at hs
    refine ⟨⟨N - 1, by omega⟩, ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    have heq : N - 1 + 1 = N := by omega
    rw [heq, cnt_full]; exact hs
  let i0 := T.min' hT
  have hi0 : s < cnt fl (i0.val + 1) := (Finset.mem_filter.1 (Finset.min'_mem T hT)).2
  have hle : cnt fl i0.val ≤ s := by
    by_cases h0 : i0.val = 0
    · rw [h0, cnt_zero]; omega
    · let j : Fin N := ⟨i0.val - 1, by omega⟩
      have hjlt : j < i0 := by show i0.val - 1 < i0.val; omega
      have hnot : j ∉ T := fun hm => not_le.2 hjlt (Finset.min'_le T j hm)
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
      have heq : j.val + 1 = i0.val := by dsimp only [j]; omega
      rw [heq] at hnot; exact hnot
  have hstep := cnt_succ fl i0.val i0.isLt
  have hfi : fl i0 = true := by
    by_contra hc
    simp only [Bool.not_eq_true] at hc
    have hfl : fl ⟨i0.val, i0.isLt⟩ = false := hc
    rw [hfl] at hstep; simp at hstep; omega
  have hfl : fl ⟨i0.val, i0.isLt⟩ = true := hfi
  rw [hfl] at hstep; simp at hstep
  exact ⟨i0, hfi, by omega⟩

abbrev ParamsIn (k r m : ℕ) : Type :=
  (Fin k ⊕ Fin k) ⊕ (((Fin r × Fin k) ⊕ (Fin r × Fin k)) ⊕ ((Fin m × Fin k) ⊕ (Fin m × Fin k)))

def mkParams {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (R B : Fin m → Fin (2 ^ k)) : ParamsIn k r m → Bool :=
  Sum.elim (Sum.elim (fun i : Fin k => u.val.testBit i.val) (fun i : Fin k => v.val.testBit i.val))
    (Sum.elim (Sum.elim (fun p : Fin r × Fin k => (cr p.1).val.testBit p.2.val)
        (fun p : Fin r × Fin k => (cc p.1).val.testBit p.2.val))
      (Sum.elim (fun p : Fin m × Fin k => (R p.1).val.testBit p.2.val)
        (fun p : Fin m × Fin k => (B p.1).val.testBit p.2.val)))

def sliceVec {k : ℕ} (P_bits w0 : Fin k → Bool) (x : V k) : Fin k → Bool :=
  fun i => if P_bits i then w0 i else ofZ (x i)

noncomputable def bvFin {k : ℕ} (bits : Fin k → Bool) : Fin (2 ^ k) :=
  (xzE k).symm (fun i => toZ (bits i))

theorem bvFin_testBit {k : ℕ} (bits : Fin k → Bool) (i : Fin k) :
    (bvFin bits).val.testBit i.val = bits i := by
  rw [← toZ_inj]
  have h := congrFun (xz_xzE (fun q => toZ (bits q))) i
  exact h

def Gslice {k r m : ℕ} (params : ParamsIn k r m → Bool) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool) (x : V k) (j : Fin m) : ZMod 2 :=
  toZ (xor (evalF (Sum.elim (sliceVec P_bits w0 x) params) j) (y j))

theorem Gslice_eq_eval {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (P_bits w0 : Fin k → Bool) (x : V k) (j : Fin m) :
    Gslice (mkParams u v cr cc R B) y P_bits w0 x j =
      toZ (xor (xor (parityN k (R j).val (stateN k r false (bvFin (sliceVec P_bits w0 x)).val u.val cr))
        (parityN k (B j).val (stateN k r true (bvFin (sliceVec P_bits w0 x)).val v.val cc))) (y j)) := by
  unfold Gslice
  congr 2
  have hfun : (fun i : Fin k => (bvFin (sliceVec P_bits w0 x)).val.testBit i.val) = sliceVec P_bits w0 x := by
    funext i; exact bvFin_testBit _ i
  conv_lhs => rw [← hfun]
  exact evalF_eq u v cr cc R B (bvFin (sliceVec P_bits w0 x)) j

theorem Gslice_eq_parity {k r m : ℕ} (hk : 0 < k) (u v : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool) (x : V k) (j : Fin m) :
    Gslice (mkParams u v cr cc R B) y P_bits w0 x j =
      toZ (y j) + ∑ a ∈ activeN r R B, toZ (sensorN u v cr cc a (bvFin (sliceVec P_bits w0 x)).val) *
        colN r R B a j := by
  rw [Gslice_eq_eval, toZ_xor, parity_reindex hk R B u v cr cc (bvFin (sliceVec P_bits w0 x)) j, add_comm]
  rfl

theorem sensor_slice_dep {k r : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (u v : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (P_bits w0 : Fin k → Bool) (a : Bool × Fin k) (x x' : V k)
    (h : ∀ i ∈ leftN r (Finset.univ.filter (fun i : Fin k => P_bits i = true)) a, x i = x' i) :
    sensorN u v cr cc a (bvFin (sliceVec P_bits w0 x)).val =
      sensorN u v cr cc a (bvFin (sliceVec P_bits w0 x')).val := by
  apply sens_local k r hk hr u v cr cc a _ _ (bvFin _).isLt (bvFin _).isLt
  intro i hi
  rw [bvFin_testBit, bvFin_testBit]
  unfold sliceVec
  by_cases hp : P_bits i = true
  · simp [hp]
  · simp only [hp, Bool.false_eq_true, ite_false]
    have hmem : i ∈ leftN r (Finset.univ.filter (fun q : Fin k => P_bits q = true)) a := by
      simp only [leftN, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hi, hp⟩
    rw [h i hmem]

theorem Gslice_isQuad {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (u v : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool)
    (hgood : ∀ a ∈ activeN r R B, (leftN r (Finset.univ.filter (fun i : Fin k => P_bits i = true)) a).card ≤ 2)
    (j : Fin m) :
    IsQuad (fun x => Gslice (mkParams u v cr cc R B) y P_bits w0 x j) := by
  refine IsQuad.congr ((isQuad_const (toZ (y j))).add (isQuad_sum_finset (activeN r R B) (fun a ha => ?_)))
    (fun x => (Gslice_eq_parity hk u v cr cc R B y P_bits w0 x j).symm)
  have hsq : IsQuad (fun x : V k => toZ (sensorN u v cr cc a (bvFin (sliceVec P_bits w0 x)).val)) :=
    isQuad_of_dep_le_two (hgood a ha) (fun x x' h => by rw [sensor_slice_dep hk hr u v cr cc P_bits w0 a x x' h])
  exact (hsq.smul (colN r R B a j)).congr (fun x => mul_comm _ _)

theorem tilde_Gslice_isAff {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (u v : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool) (Rmm : Fin m × Fin m → Bool)
    (hcap : ∀ a ∈ activeN r R B,
      (leftN r (Finset.univ.filter (fun i : Fin k => P_bits i = true)) a).card ≤
        if tilde Rmm (colN r R B a) = 0 then 2 else 1)
    (j : Fin m) :
    IsAff (fun x => tilde Rmm (Gslice (mkParams u v cr cc R B) y P_bits w0 x) j) := by
  have heq : ∀ x : V k, tilde Rmm (Gslice (mkParams u v cr cc R B) y P_bits w0 x) j =
      tilde Rmm (fun j' => toZ (y j')) j +
        ∑ a ∈ activeN r R B, toZ (sensorN u v cr cc a (bvFin (sliceVec P_bits w0 x)).val) *
          tilde Rmm (colN r R B a) j := by
    intro x
    have hvec : Gslice (mkParams u v cr cc R B) y P_bits w0 x =
        (fun j' => toZ (y j')) + ∑ a ∈ activeN r R B,
          toZ (sensorN u v cr cc a (bvFin (sliceVec P_bits w0 x)).val) • colN r R B a := by
      funext j'
      rw [Gslice_eq_parity hk u v cr cc R B y P_bits w0 x j', Pi.add_apply, Finset.sum_apply]
      rfl
    have htilde_sum : ∀ (S : Finset (Bool × Fin k)) (f : Bool × Fin k → Fin m → ZMod 2),
        tilde Rmm (∑ a ∈ S, f a) = ∑ a ∈ S, tilde Rmm (f a) := by
      intro S f
      induction S using Finset.induction_on with
      | empty => funext q; simp [tilde]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, (tilde_linear Rmm).1, ih]
    rw [hvec, (tilde_linear Rmm).1, htilde_sum, Pi.add_apply, Finset.sum_apply]
    congr 1
    apply Finset.sum_congr rfl; intro a _
    rw [(tilde_linear Rmm).2.1]; rfl
  refine IsAff.congr ((isAff_const _).add (isAff_sum_finset (activeN r R B) (fun a ha => ?_)))
    (fun x => (heq x).symm)
  by_cases ht : tilde Rmm (colN r R B a) = 0
  · refine (isAff_const 0).congr (fun x => by rw [ht]; simp)
  · have hle1 : (leftN r (Finset.univ.filter (fun i : Fin k => P_bits i = true)) a).card ≤ 1 := by
      have := hcap a ha; rwa [ite_eq_right ht] at this
    have hsa : IsAff (fun x : V k => toZ (sensorN u v cr cc a (bvFin (sliceVec P_bits w0 x)).val)) :=
      isAff_of_dep_le_one hle1 (fun x x' h => by rw [sensor_slice_dep hk hr u v cr cc P_bits w0 a x x' h])
    exact (hsa.smul (tilde Rmm (colN r R B a) j)).congr (fun x => mul_comm _ _)

def M_aff {k m : ℕ} (P_bits : Fin k → Bool) (t0 : Fin m → Bool) (te : Fin k → Fin m → Bool) :
    Fin ((k + 1) + (k + m)) × Fin ((k + 1) + (k + m)) → Bool := fun p =>
  splitF (fun _ : Fin (k + 1) => false)
    (splitF
      (fun i : Fin k => splitF
        (fun c : Fin (k + 1) => decide (c = i.castSucc) && P_bits i)
        (fun _ : Fin (k + m) => false) p.2)
      (fun j : Fin m => splitF
        (fun c : Fin (k + 1) => if hc : c.val < k then xor (te ⟨c.val, hc⟩ j) (t0 j) else t0 j)
        (fun _ : Fin (k + m) => false) p.2))
    p.1

def R_aff {k m : ℕ} (P_bits : Fin k → Bool) (t0 : Fin m → Bool) (te : Fin k → Fin m → Bool) :
    Fin (k + 1) × Fin (k + 1) → Bool := fun p =>
  gj ((k + 1) + (k + m)) (M_aff P_bits t0 te) (Fin.castAdd (k + m) p.1, Fin.castAdd (k + m) p.2)

theorem R_aff_flatOK {k m : ℕ} (P_bits : Fin k → Bool) (t0 : Fin m → Bool)
    (te : Fin k → Fin m → Bool) : FlatOK (R_aff P_bits t0 te) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp i
    have := gj_pivcol (M_aff P_bits t0 te) (Fin.castAdd (k + m) p) hp (Fin.castAdd (k + m) i)
    simp only [R_aff]
    rw [this]
    simp [Fin.castAdd_inj]
  · intro q hq j
    exact gj_zerorow (M_aff P_bits t0 te) (Fin.castAdd (k + m) q) hq (Fin.castAdd (k + m) j)
  · intro p q hpq
    exact gj_upper (M_aff P_bits t0 te) (Fin.castAdd (k + m) p) (Fin.castAdd (k + m) q)
      (by simp only [Fin.lt_def, Fin.coe_castAdd] at hpq ⊢; exact hpq)

theorem sol_R_aff_iff {k m : ℕ} (P_bits : Fin k → Bool) (t0 : Fin m → Bool)
    (te : Fin k → Fin m → Bool) (x : V k) :
    Sol (R_aff P_bits t0 te) x ↔
      (∀ i : Fin k, P_bits i = true → x i = 0) ∧
      (∀ j : Fin m, toZ (t0 j) + ∑ i : Fin k, x i * (toZ (te i j) + toZ (t0 j)) = 0) := by
  let extA : Fin ((k + 1) + (k + m)) → ZMod 2 := splitF (ext x) 0
  have hmul : ∀ (M : Fin ((k + 1) + (k + m)) × Fin ((k + 1) + (k + m)) → Bool)
      (r : Fin ((k + 1) + (k + m))),
      (mat M).mulVec extA r = ∑ c : Fin (k + 1), toZ (M (r, Fin.castAdd (k + m) c)) * ext x c := by
    intro M r
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, extA, splitF_castAdd, splitF_natAdd,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    rfl
  have hgj : (mat (gj ((k + 1) + (k + m)) (M_aff P_bits t0 te))).mulVec extA = 0 ↔
      Sol (R_aff P_bits t0 te) x := by
    have hzr : ∀ s : Fin (k + m), ∀ c,
        gj ((k + 1) + (k + m)) (M_aff P_bits t0 te) (Fin.natAdd (k + 1) s, c) = false := by
      intro s c
      apply gj_zerorow
      apply gj_col_zero
      intro r
      unfold M_aff
      refine Fin.addCases (fun _ => by simp [splitF_castAdd]) (fun s' => ?_) r
      rw [splitF_natAdd]
      refine Fin.addCases (fun _ => by simp [splitF_castAdd, splitF_natAdd])
        (fun _ => by simp [splitF_natAdd]) s'
    rw [funext_iff]
    constructor
    · intro h
      funext r
      have hr := h (Fin.castAdd (k + m) r)
      rw [hmul] at hr
      exact hr
    · intro h r
      refine Fin.addCases (fun r' => ?_) (fun s => ?_) r
      · rw [hmul]; exact congrFun h r'
      · rw [hmul]
        apply Finset.sum_eq_zero; intro c _; rw [hzr s]; simp [toZ_false]
  rw [← hgj, gj_sol_iff, funext_iff]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun j => ?_⟩
    · have hr := h (Fin.natAdd (k + 1) (Fin.castAdd m i))
      rw [hmul] at hr
      simp only [M_aff, splitF_natAdd, splitF_castAdd, toZ_and, toZ_decide, Pi.zero_apply] at hr
      rw [Fin.sum_univ_castSucc] at hr
      simp only [Fin.castSucc_inj, Ne.symm (Fin.castSucc_ne_last i), ite_false, zero_mul, add_zero, ext_cs] at hr
      rw [Finset.sum_eq_single i] at hr
      · simpa [hi, toZ_true] using hr
      · intro q _ hqi; simp [hqi]
      · simp
    · have hr := h (Fin.natAdd (k + 1) (Fin.natAdd k j))
      rw [hmul] at hr
      simp only [M_aff, splitF_natAdd, splitF_castAdd, Pi.zero_apply] at hr
      rw [Fin.sum_univ_castSucc] at hr
      simp only [Fin.val_castSucc, Fin.is_lt, dite_true, Fin.val_last, lt_self_iff_false,
        dite_false, ext_cs, ext_last, mul_one, toZ_xor] at hr
      rw [add_comm, ← hr]
      congr 1; apply Finset.sum_congr rfl; intro i _; ring
  · rintro ⟨hP, hA⟩ r
    rw [hmul]
    refine Fin.addCases (fun r' => ?_) (fun s => ?_) r
    · simp [M_aff, splitF_castAdd, toZ_false]
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) s
      · simp only [M_aff, splitF_natAdd, splitF_castAdd, toZ_and, toZ_decide, Pi.zero_apply]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.castSucc_inj, Ne.symm (Fin.castSucc_ne_last i), ite_false, zero_mul, add_zero, ext_cs]
        rw [Finset.sum_eq_single i]
        · by_cases hi : P_bits i = true
          · simp [hi, hP i hi]
          · simp [hi, toZ_false]
        · intro q _ hqi; simp [hqi]
        · simp
      · simp only [M_aff, splitF_natAdd, splitF_castAdd, Pi.zero_apply]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.is_lt, dite_true, Fin.val_last, lt_self_iff_false,
          dite_false, ext_cs, ext_last, mul_one, toZ_xor]
        rw [add_comm, ← hA j]
        congr 1; apply Finset.sum_congr rfl; intro i _; ring

def t0Of {k r m : ℕ} (params : ParamsIn k r m → Bool) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool) (Rmm : Fin m × Fin m → Bool) (j : Fin m) : Bool :=
  ofZ (tilde Rmm (Gslice params y P_bits w0 0) j)

def teOf {k r m : ℕ} (params : ParamsIn k r m → Bool) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool) (Rmm : Fin m × Fin m → Bool) (i : Fin k) (j : Fin m) : Bool :=
  ofZ (tilde Rmm (Gslice params y P_bits w0 (e1 i)) j)

def R_slice {k r m : ℕ} (params : ParamsIn k r m → Bool) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool) (Rmm : Fin m × Fin m → Bool) : Fin (k + 1) × Fin (k + 1) → Bool :=
  R_aff P_bits (t0Of params y P_bits w0 Rmm) (teOf params y P_bits w0 Rmm)

theorem sol_R_slice_iff {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (u v : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool) (Rmm : Fin m × Fin m → Bool)
    (hcap : ∀ a ∈ activeN r R B,
      (leftN r (Finset.univ.filter (fun i : Fin k => P_bits i = true)) a).card ≤
        if tilde Rmm (colN r R B a) = 0 then 2 else 1)
    (x : V k) :
    Sol (R_slice (mkParams u v cr cc R B) y P_bits w0 Rmm) x ↔
      (∀ i : Fin k, P_bits i = true → x i = 0) ∧
      tilde Rmm (Gslice (mkParams u v cr cc R B) y P_bits w0 x) = 0 := by
  rw [R_slice, sol_R_aff_iff, funext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j => ?_⟩
    have haff := tilde_Gslice_isAff hk hr u v cr cc R B y P_bits w0 Rmm hcap j
    rw [interp_aff haff x]
    simpa [t0Of, teOf, toZ_ofZ] using h2 j
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j => ?_⟩
    have haff := tilde_Gslice_isAff hk hr u v cr cc R B y P_bits w0 Rmm hcap j
    have hj := h2 j
    rw [interp_aff haff x] at hj
    simpa [t0Of, teOf, toZ_ofZ] using hj

def PtS {k r m : ℕ} (params : ParamsIn k r m → Bool) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool) (gam : Fin m → Bool) (R_s : Fin (k + 1) × Fin (k + 1) → Bool)
    (p : Fin (k + 1) × Fin (k + 1)) : Bool :=
  ofZ (∑ j : Fin m, toZ (gam j) * Gslice params y P_bits w0 (piR R_s (ptv p.1 p.2)) j)

theorem evalQ_PtS {k r m : ℕ} (params : ParamsIn k r m → Bool) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool) (gam : Fin m → Bool) (R_s : Fin (k + 1) × Fin (k + 1) → Bool)
    (hQ : ∀ j : Fin m, IsQuad (fun x => Gslice params y P_bits w0 x j)) (u : V k) :
    let gs := ginit (PtS params y P_bits w0 gam R_s)
    evalQ gs.c gs.al gs.ga u =
      ∑ j : Fin m, toZ (gam j) * Gslice params y P_bits w0 (piR R_s u) j := by
  let PS : V k → ZMod 2 := fun u => ∑ j : Fin m, toZ (gam j) * Gslice params y P_bits w0 (piR R_s u) j
  have hPS : IsQuad PS :=
    isQuad_sum (fun j => ((hQ j).comp_aff (piR_aff R_s)).smul (toZ (gam j)))
  have hPt : ∀ a b, toZ (PtS params y P_bits w0 gam R_s (a, b)) = PS (ptv a b) := fun a b => by
    unfold PtS PS; rw [toZ_ofZ]
  rw [show (∑ j : Fin m, toZ (gam j) * Gslice params y P_bits w0 (piR R_s u) j) = PS u from rfl]
  rw [interp hPS u]
  unfold evalQ ginit
  simp only [toZ_xor, toZ_and, toZ_decide, hPt, ptv_ll, ptv_last, ind_cs, ind_last]
  have hpt : ∀ q r : Fin k, ptv q.castSucc r.castSucc = e1 q + e1 r := by
    intro q r; simp [ptv, ind_cs]
  simp only [hpt]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl; intro q _; ring
  · apply Finset.sum_congr rfl; intro q _
    apply Finset.sum_congr rfl; intro r _
    by_cases h : q < r
    · simp only [h, ite_true, one_mul, Δ2]; ring
    · simp [h]

def goutDivBV {k : ℕ} (W : ℕ) (R_s : Fin (k + 1) × Fin (k + 1) → Bool) (w : GW k W → Bool) :
    BitVec W :=
  let mag := (List.finRange k).foldl
    (fun (x : BitVec W) i => if R_s (i.castSucc, i.castSucc) then x >>> 1 else x) (bv (gP w))
  if gz w then 0 else if gc w then -mag else mag

def sliceTermBV {k r m : ℕ} (W : ℕ) (params : ParamsIn k r m → Bool) (y : Fin m → Bool)
    (P_bits w0 : Fin k → Bool) (gam : Fin m → Bool) (R_s : Fin (k + 1) × Fin (k + 1) → Bool) :
    BitVec W :=
  if R_s (Fin.last k, Fin.last k) then 0
  else goutDivBV W R_s (genc W (gfold (List.finRange k) (ginit (PtS params y P_bits w0 gam R_s))))

theorem sliceTermBV_eq {k r m : ℕ} (W : ℕ) (hW : k < W) (params : ParamsIn k r m → Bool)
    (y : Fin m → Bool) (P_bits w0 : Fin k → Bool) (gam : Fin m → Bool)
    (R_s : Fin (k + 1) × Fin (k + 1) → Bool) (hR : FlatOK R_s)
    (hQ : ∀ j : Fin m, IsQuad (fun x => Gslice params y P_bits w0 x j)) :
    sliceTermBV W params y P_bits w0 gam R_s =
      BitVec.ofInt W (∑ x ∈ Finset.univ.filter (Sol R_s),
        sgnZ (∑ j : Fin m, toZ (gam j) * Gslice params y P_bits w0 x j)) := by
  by_cases hc : cons R_s
  · unfold sliceTermBV
    have hfl : R_s (Fin.last k, Fin.last k) = false := hc
    rw [hfl]; simp only [Bool.false_eq_true, ite_false]
    set gs := ginit (PtS params y P_bits w0 gam R_s) with hgs
    set s := gfold (List.finRange k) gs with hs
    set S_sol : ℤ := ∑ x ∈ Finset.univ.filter (Sol R_s),
      sgnZ (∑ j : Fin m, toZ (gam j) * Gslice params y P_bits w0 x j) with hSsol
    have hgval : gval s = (2 : ℤ) ^ npiv R_s * S_sol := by
      have h1 : gsum gs.c gs.al gs.ga = gval s := gauss_correct gs.c gs.al gs.ga
      rw [← h1]
      unfold gsum
      have h2 : ∀ u : V k, sgnZ (evalQ gs.c gs.al gs.ga u) =
          sgnZ (∑ j : Fin m, toZ (gam j) * Gslice params y P_bits w0 (piR R_s u) j) := by
        intro u; rw [evalQ_PtS params y P_bits w0 gam R_s hQ u]
      rw [Finset.sum_congr rfl (fun u _ => h2 u)]
      exact fiber_sum hR hc (fun x => sgnZ (∑ j : Fin m, toZ (gam j) * Gslice params y P_bits w0 x j))
    have hn3 : s.n3 ≤ k := by
      have := gfold_n3 (List.finRange k) gs
      simp only [List.length_finRange] at this
      have hn0 : gs.n3 = 0 := rfl
      rw [hn0, zero_add] at this
      exact this
    have hbvP : bv (gP (genc W s)) = BitVec.ofNat W (2 ^ k / 2 ^ s.n3) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [getLsbD_bv (gP (genc W s)) ⟨i, hi⟩, BitVec.getLsbD_ofNat]
      simp [gP, genc, hi]
    have hltW : 2 ^ k / 2 ^ s.n3 < 2 ^ W := by
      calc 2 ^ k / 2 ^ s.n3 ≤ 2 ^ k := Nat.div_le_self _ _
        _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hW
    unfold goutDivBV
    rw [hbvP, foldl_shr_ofNat (fun i : Fin k => R_s (i.castSucc, i.castSucc)) (List.finRange k) _ hltW,
      countP_finRange]
    change (if s.z then (0 : BitVec W) else if s.c then -(BitVec.ofNat W (2 ^ k / 2 ^ s.n3 / 2 ^ npiv R_s))
      else BitVec.ofNat W (2 ^ k / 2 ^ s.n3 / 2 ^ npiv R_s)) = BitVec.ofInt W S_sol
    cases hz : s.z
    · simp only [Bool.false_eq_true, ite_false]
      unfold gval at hgval
      rw [hz] at hgval; simp only [Bool.false_eq_true, ite_false] at hgval
      have hdiv1 : 2 ^ k / 2 ^ s.n3 = 2 ^ (k - s.n3) := Nat.pow_div hn3 (by norm_num)
      rw [hdiv1] at hgval ⊢
      have habs : 2 ^ npiv R_s * S_sol.natAbs = 2 ^ (k - s.n3) := by
        have h1 := congrArg Int.natAbs hgval
        rw [Int.natAbs_mul, Int.natAbs_pow] at h1
        cases hc' : s.c <;> rw [hc'] at h1 <;> simpa using h1.symm
      have hpos : 0 < S_sol.natAbs := by
        by_contra h0
        have h0' : S_sol.natAbs = 0 := by omega
        rw [h0', mul_zero] at habs
        exact absurd habs.symm (by positivity)
      have hnp : npiv R_s ≤ k - s.n3 := by
        have hle : 2 ^ npiv R_s ≤ 2 ^ (k - s.n3) := by
          calc 2 ^ npiv R_s = 2 ^ npiv R_s * 1 := by ring
            _ ≤ 2 ^ npiv R_s * S_sol.natAbs := Nat.mul_le_mul_left _ hpos
            _ = 2 ^ (k - s.n3) := habs
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
      have hdiv2 : 2 ^ (k - s.n3) / 2 ^ npiv R_s = 2 ^ (k - s.n3 - npiv R_s) :=
        Nat.pow_div hnp (by norm_num)
      rw [hdiv2]
      have hsplit : (2 : ℤ) ^ (k - s.n3) = (2 : ℤ) ^ npiv R_s * (2 : ℤ) ^ (k - s.n3 - npiv R_s) := by
        rw [← pow_add, Nat.add_sub_cancel' hnp]
      have hp2 : (2 : ℤ) ^ npiv R_s ≠ 0 := by positivity
      cases hc' : s.c
      · rw [hc'] at hgval
        simp only [Bool.false_eq_true, ite_false] at hgval ⊢
        have hS : S_sol = ((2 ^ (k - s.n3 - npiv R_s) : ℕ) : ℤ) := by
          push_cast at hgval ⊢
          rw [hsplit] at hgval
          exact mul_left_cancel₀ hp2 hgval.symm
        rw [hS, BitVec.ofInt_natCast]
      · rw [hc'] at hgval
        simp only [ite_true] at hgval ⊢
        have hS : S_sol = -((2 ^ (k - s.n3 - npiv R_s) : ℕ) : ℤ) := by
          push_cast at hgval ⊢
          rw [hsplit] at hgval
          exact mul_left_cancel₀ hp2 (by rw [← hgval]; ring)
        rw [hS, BitVec.ofInt_neg, BitVec.ofInt_natCast]
    · simp only [ite_true]
      unfold gval at hgval
      rw [hz] at hgval; simp only [ite_true] at hgval
      have hp2 : (2 : ℤ) ^ npiv R_s ≠ 0 := by positivity
      have hS0 : S_sol = 0 := (mul_eq_zero.1 hgval.symm).resolve_left hp2
      rw [hS0]; rfl
  · unfold sliceTermBV
    have htr : R_s (Fin.last k, Fin.last k) = true := by simpa [cons] using hc
    rw [htr]; simp only [ite_true]
    have hemp : Finset.univ.filter (Sol R_s) = ∅ := by
      ext x; simp [not_cons_empty hR hc x]
    rw [hemp, Finset.sum_empty]; rfl

def validMask {k m b : ℕ} (P_bits : Fin k → Bool) (Rmm : Fin m × Fin m → Bool)
    (σ : Fin b → Bool) : Bool :=
  decide (∀ q : Fin b, σ q = true → q.val < cnt P_bits k + cnt (fun j => Rmm (j, j)) m)

def w0Mask {k b : ℕ} (P_bits : Fin k → Bool) (σ : Fin b → Bool) (i : Fin k) : Bool :=
  P_bits i && decide (∃ q : Fin b, σ q = true ∧ cnt P_bits i.val = q.val)

def gamMask {k m b : ℕ} (P_bits : Fin k → Bool) (Rmm : Fin m × Fin m → Bool)
    (σ : Fin b → Bool) (j : Fin m) : Bool :=
  Rmm (j, j) && decide (∃ q : Fin b, σ q = true ∧
    cnt P_bits k + cnt (fun j' => Rmm (j', j')) j.val = q.val)

theorem sum_contrib_eq {k r m b : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (R B : Fin m → Fin (2 ^ k))
    (y : Fin m → Bool) (P_bits : Fin k → Bool) (Rmm : Fin m × Fin m → Bool)
    (hR : GJF Rmm)
    (hPb : (Finset.univ.filter (fun i : Fin k => P_bits i = true)).card + rhoM Rmm ≤ b)
    (hcap : ∀ a ∈ activeN r R B,
      (leftN r (Finset.univ.filter (fun i : Fin k => P_bits i = true)) a).card ≤
        if tilde Rmm (colN r R B a) = 0 then 2 else 1) :
    ∑ σ : Fin b → Bool, (if validMask P_bits Rmm σ = true then
      ∑ x ∈ Finset.univ.filter (Sol (R_slice (mkParams u v cr cc R B) y P_bits (w0Mask P_bits σ) Rmm)),
        sgnZ (∑ j : Fin m, toZ (gamMask P_bits Rmm σ j) *
          Gslice (mkParams u v cr cc R B) y P_bits (w0Mask P_bits σ) x j) else (0 : ℤ)) =
      (2 : ℤ) ^ rhoM Rmm *
        (Nat.card {w : Fin (2 ^ k) // (fun j => xor (parityN k (R j).val (stateN k r false w.val u.val cr))
          (parityN k (B j).val (stateN k r true w.val v.val cc))) = y} : ℤ) := by
  classical
  set P := Finset.univ.filter (fun i : Fin k => P_bits i = true) with hPdef
  set p := P.card with hpdef
  set d := rhoM Rmm with hddef
  have hcp : cnt P_bits k = p := cnt_full P_bits
  have hcd : cnt (fun j => Rmm (j, j)) m = d := cnt_full (fun j => Rmm (j, j))
  let eFin : Fin b ≃ Fin p ⊕ (Fin d ⊕ Fin (b - (p + d))) :=
    { toFun := fun q =>
        if h1 : q.val < p then Sum.inl ⟨q.val, h1⟩
        else if h2 : q.val < p + d then Sum.inr (Sum.inl ⟨q.val - p, by omega⟩)
        else Sum.inr (Sum.inr ⟨q.val - (p + d), by omega⟩)
      invFun := fun s => match s with
        | Sum.inl i => ⟨i.val, by omega⟩
        | Sum.inr (Sum.inl j) => ⟨p + j.val, by omega⟩
        | Sum.inr (Sum.inr t) => ⟨p + d + t.val, by omega⟩
      left_inv := fun q => by
        by_cases h1 : q.val < p
        · simp [h1]
        · by_cases h2 : q.val < p + d
          · simp only [dite_eq_right h1, dite_eq_left h2]; apply Fin.ext; simp; omega
          · simp only [dite_eq_right h1, dite_eq_right h2]; apply Fin.ext; simp; omega
      right_inv := fun s => by
        rcases s with i | j | t
        · simp [i.isLt]
        · have h1 : ¬ (p + j.val < p) := by omega
          have h2 : p + j.val < p + d := by omega
          simp only [dite_eq_right h1, dite_eq_left h2]
          congr 2; apply Fin.ext; simp
        · have h1 : ¬ (p + d + t.val < p) := by omega
          have h2 : ¬ (p + d + t.val < p + d) := by omega
          simp only [dite_eq_right h1, dite_eq_right h2]
          congr 2; apply Fin.ext; simp }
  let eSig : (Fin b → Bool) ≃ ((Fin p → Bool) × (Fin d → Bool) × (Fin (b - (p + d)) → Bool)) :=
    { toFun := fun σ => (fun i => σ ⟨i.val, by omega⟩, fun j => σ ⟨p + j.val, by omega⟩,
        fun t => σ ⟨p + d + t.val, by omega⟩)
      invFun := fun ⟨α, β, τ⟩ q =>
        match eFin q with
        | Sum.inl i => α i
        | Sum.inr (Sum.inl j) => β j
        | Sum.inr (Sum.inr t) => τ t
      left_inv := fun σ => by
        funext q
        by_cases h1 : q.val < p
        · simp [eFin, h1]
        · by_cases h2 : q.val < p + d
          · simp only [eFin, Equiv.coe_fn_mk, dite_eq_right h1, dite_eq_left h2]
            congr 1; apply Fin.ext; simp; omega
          · simp only [eFin, Equiv.coe_fn_mk, dite_eq_right h1, dite_eq_right h2]
            congr 1; apply Fin.ext; simp; omega
      right_inv := fun ⟨α, β, τ⟩ => by
        ext q
        · simp [eFin, q.isLt]
        · have h1 : ¬ (p + q.val < p) := by omega
          have h2 : p + q.val < p + d := by omega
          simp [eFin, h1, h2]
        · have h1 : ¬ (p + d + q.val < p) := by omega
          have h2 : ¬ (p + d + q.val < p + d) := by omega
          simp [eFin, h1, h2] }
  let w0Of : (Fin p → Bool) → Fin k → Bool := fun α i =>
    P_bits i && if h : cnt P_bits i.val < p then α ⟨cnt P_bits i.val, h⟩ else false
  let gamOf : (Fin d → Bool) → Fin m → Bool := fun β j =>
    Rmm (j, j) && if h : cnt (fun q => Rmm (q, q)) j.val < d then
      β ⟨cnt (fun q => Rmm (q, q)) j.val, h⟩ else false
  have hw0_eq : ∀ α β τ, w0Mask P_bits (eSig.symm (α, β, τ)) = w0Of α := by
    intro α β τ; funext i
    unfold w0Mask; dsimp only [w0Of]
    by_cases hp' : P_bits i = true
    · have hlt : cnt P_bits i.val < p := cnt_lt_rho P_bits i hp'
      simp only [hp', Bool.true_and, dite_eq_left hlt]
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨q, hq1, hq2⟩
        have hqp : q.val < p := by omega
        simp only [eSig, Equiv.coe_fn_symm_mk, eFin, Equiv.coe_fn_mk, dite_eq_left hqp] at hq1
        have hfeq : (⟨q.val, hqp⟩ : Fin p) = ⟨cnt P_bits i.val, hlt⟩ := Fin.ext hq2.symm
        rwa [← hfeq]
      · intro hα
        refine ⟨⟨cnt P_bits i.val, by omega⟩, ?_, rfl⟩
        simp only [eSig, Equiv.coe_fn_symm_mk, eFin, Equiv.coe_fn_mk, dite_eq_left hlt]
        exact hα
    · simp [hp']
  have hgam_eq : ∀ α β τ, gamMask P_bits Rmm (eSig.symm (α, β, τ)) = gamOf β := by
    intro α β τ; funext j
    unfold gamMask; dsimp only [gamOf]
    by_cases hr' : Rmm (j, j) = true
    · have hlt : cnt (fun q => Rmm (q, q)) j.val < d := cnt_lt_rho (fun q => Rmm (q, q)) j hr'
      simp only [hr', Bool.true_and, dite_eq_left hlt, hcp]
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨q, hq1, hq2⟩
        have h1 : ¬ (q.val < p) := by omega
        have h2 : q.val < p + d := by omega
        simp only [eSig, Equiv.coe_fn_symm_mk, eFin, Equiv.coe_fn_mk, dite_eq_right h1,
          dite_eq_left h2] at hq1
        have hfeq : (⟨q.val - p, by omega⟩ : Fin d) = ⟨cnt (fun q => Rmm (q, q)) j.val, hlt⟩ :=
          Fin.ext (by simp; omega)
        rwa [← hfeq]
      · intro hβ
        refine ⟨⟨p + cnt (fun q => Rmm (q, q)) j.val, by omega⟩, ?_, rfl⟩
        have h1 : ¬ (p + cnt (fun q => Rmm (q, q)) j.val < p) := by omega
        have h2 : p + cnt (fun q => Rmm (q, q)) j.val < p + d := by omega
        simp only [eSig, Equiv.coe_fn_symm_mk, eFin, Equiv.coe_fn_mk, dite_eq_right h1,
          dite_eq_left h2]
        have hfeq : (⟨p + cnt (fun q => Rmm (q, q)) j.val - p, by omega⟩ : Fin d) =
            ⟨cnt (fun q => Rmm (q, q)) j.val, hlt⟩ := Fin.ext (by simp)
        rwa [hfeq]
    · simp [hr']
  have hval_eq : ∀ α β τ, validMask P_bits Rmm (eSig.symm (α, β, τ)) = true ↔ τ = (fun _ => false) := by
    intro α β τ
    simp only [validMask, decide_eq_true_eq, hcp, hcd, funext_iff]
    constructor
    · intro h t
      by_contra ht
      have ht' : τ t = true := by simpa using ht
      have hq : eSig.symm (α, β, τ) ⟨p + d + t.val, by omega⟩ = true := by
        have h1 : ¬ (p + d + t.val < p) := by omega
        have h2 : ¬ (p + d + t.val < p + d) := by omega
        simp only [eSig, Equiv.coe_fn_symm_mk, eFin, Equiv.coe_fn_mk, dite_eq_right h1,
          dite_eq_right h2]
        have hfeq : (⟨p + d + t.val - (p + d), by omega⟩ : Fin (b - (p + d))) = t :=
          Fin.ext (by simp)
        rwa [hfeq]
      have hlt' := h ⟨p + d + t.val, by omega⟩ hq
      simp only at hlt'
      omega
    · intro h q hq
      by_contra hge
      have h1 : ¬ (q.val < p) := by omega
      have h2 : ¬ (q.val < p + d) := by omega
      simp only [eSig, Equiv.coe_fn_symm_mk, eFin, Equiv.coe_fn_mk, dite_eq_right h1,
        dite_eq_right h2, h] at hq
      exact absurd hq (by decide)
  rw [← Equiv.sum_comp eSig.symm]
  simp only [Fintype.sum_prod_type]
  have hcollapse : ∀ α β,
      (∑ τ : Fin (b - (p + d)) → Bool,
        if validMask P_bits Rmm (eSig.symm (α, β, τ)) = true then
          ∑ x ∈ Finset.univ.filter (Sol (R_slice (mkParams u v cr cc R B) y P_bits
              (w0Mask P_bits (eSig.symm (α, β, τ))) Rmm)),
            sgnZ (∑ j : Fin m, toZ (gamMask P_bits Rmm (eSig.symm (α, β, τ)) j) *
              Gslice (mkParams u v cr cc R B) y P_bits (w0Mask P_bits (eSig.symm (α, β, τ))) x j)
        else (0 : ℤ)) =
      ∑ x ∈ Finset.univ.filter (Sol (R_slice (mkParams u v cr cc R B) y P_bits (w0Of α) Rmm)),
        sgnZ (∑ j : Fin m, toZ (gamOf β j) *
          Gslice (mkParams u v cr cc R B) y P_bits (w0Of α) x j) := by
    intro α β
    rw [Finset.sum_eq_single (fun _ => false)]
    · rw [ite_eq_left ((hval_eq α β _).2 rfl), hw0_eq, hgam_eq]
    · intro τ _ hne
      rw [ite_eq_right (fun h => hne ((hval_eq α β τ).1 h))]
    · simp
  simp only [hcollapse]
  have hinner : ∀ α : Fin p → Bool,
      (∑ β : Fin d → Bool,
        ∑ x ∈ Finset.univ.filter (Sol (R_slice (mkParams u v cr cc R B) y P_bits (w0Of α) Rmm)),
          sgnZ (∑ j : Fin m, toZ (gamOf β j) *
            Gslice (mkParams u v cr cc R B) y P_bits (w0Of α) x j)) =
      (2 : ℤ) ^ d *
        ((Finset.univ.filter (fun x : V k => (∀ i : Fin k, P_bits i = true → x i = 0) ∧
          Gslice (mkParams u v cr cc R B) y P_bits (w0Of α) x = 0)).card : ℤ) := by
    intro α
    rw [Finset.sum_comm]
    have hβsum : ∀ x ∈ Finset.univ.filter (Sol (R_slice (mkParams u v cr cc R B) y P_bits (w0Of α) Rmm)),
        (∑ β : Fin d → Bool, sgnZ (∑ j : Fin m, toZ (gamOf β j) *
          Gslice (mkParams u v cr cc R B) y P_bits (w0Of α) x j)) =
        (2 : ℤ) ^ d * (if Gslice (mkParams u v cr cc R B) y P_bits (w0Of α) x = 0 then 1 else 0) := by
      intro x hx
      have hxsol := (sol_R_slice_iff hk hr u v cr cc R B y P_bits (w0Of α) Rmm hcap x).1
        (Finset.mem_filter.1 hx).2
      set g := Gslice (mkParams u v cr cc R B) y P_bits (w0Of α) x
      let δ : Fin d → ZMod 2 := fun s =>
        ∑ j : Fin m, if Rmm (j, j) = true ∧ cnt (fun q => Rmm (q, q)) j.val = s.val then g j else 0
      have hdot : ∀ β : Fin d → Bool, ∑ j : Fin m, toZ (gamOf β j) * g j = ∑ s : Fin d, toZ (β s) * δ s := by
        intro β
        have he : ∀ j : Fin m, toZ (gamOf β j) * g j =
            ∑ s : Fin d, toZ (β s) *
              (if Rmm (j, j) = true ∧ cnt (fun q => Rmm (q, q)) j.val = s.val then g j else 0) := by
          intro j
          dsimp only [gamOf]
          by_cases hr' : Rmm (j, j) = true
          · have hlt : cnt (fun q => Rmm (q, q)) j.val < d := cnt_lt_rho (fun q => Rmm (q, q)) j hr'
            simp only [hr', Bool.true_and, dite_eq_left hlt]
            rw [Finset.sum_eq_single ⟨cnt (fun q => Rmm (q, q)) j.val, hlt⟩]
            · simp [hr']
            · intro s _ hs
              have hne : cnt (fun q => Rmm (q, q)) j.val ≠ s.val := fun h => hs (Fin.ext h.symm)
              simp [hne]
            · simp
          · simp [hr', toZ_false]
        rw [Finset.sum_congr rfl (fun j _ => he j), Finset.sum_comm]
        apply Finset.sum_congr rfl; intro s _; rw [Finset.mul_sum]
      have hprod : ∑ β : Fin d → Bool, sgnZ (∑ j : Fin m, toZ (gamOf β j) * g j) =
          ∏ s : Fin d, (1 + sgnZ (δ s)) := by
        have e1 : ∀ β : Fin d → Bool, sgnZ (∑ j : Fin m, toZ (gamOf β j) * g j) =
            ∏ s : Fin d, sgnZ (toZ (β s) * δ s) := fun β => by rw [hdot β, sgnZ_sum]
        rw [Finset.sum_congr rfl (fun β _ => e1 β), ← Fintype.prod_sum (fun s b => sgnZ (toZ b * δ s))]
        apply Finset.prod_congr rfl; intro s _
        rw [Fintype.sum_bool]; simp [toZ_false, toZ_true, sgnZ_zero, add_comm]
      rw [hprod]
      have hδ_iff : (∀ s : Fin d, δ s = 0) ↔ g = 0 := by
        rw [eq_zero_iff_tilde_and_piv hR g]
        simp only [hxsol.2, true_and]
        constructor
        · intro h j hj
          have hlt := cnt_lt_rho (fun q => Rmm (q, q)) j hj
          have hs := h ⟨cnt (fun q => Rmm (q, q)) j.val, hlt⟩
          dsimp only [δ] at hs
          rw [Finset.sum_eq_single j] at hs
          · simpa [hj] using hs
          · intro j' _ hne
            by_cases hj' : Rmm (j', j') = true
            · have : cnt (fun q => Rmm (q, q)) j'.val ≠ cnt (fun q => Rmm (q, q)) j.val :=
                fun he => hne (cnt_inj _ j' j hj' hj he)
              simp [this]
            · simp [hj']
          · simp
        · intro h s
          dsimp only [δ]
          apply Finset.sum_eq_zero; intro j _
          by_cases hj : Rmm (j, j) = true
          · simp [hj, h j hj]
          · simp [hj]
      by_cases hg0 : g = 0
      · rw [ite_eq_left hg0, mul_one]
        have hδ0 := hδ_iff.2 hg0
        have e2 : ∀ s : Fin d, (1 + sgnZ (δ s) : ℤ) = 2 := fun s => by rw [hδ0 s, sgnZ_zero]; norm_num
        rw [Finset.prod_congr rfl (fun s _ => e2 s), Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      · rw [ite_eq_right hg0, mul_zero]
        have hnot : ¬ ∀ s : Fin d, δ s = 0 := fun h => hg0 (hδ_iff.1 h)
        push Not at hnot
        obtain ⟨s, hs⟩ := hnot
        apply Finset.prod_eq_zero (Finset.mem_univ s)
        rcases z01 (δ s) with h0 | h1
        · exact absurd h0 hs
        · rw [h1, sgnZ_one]; norm_num
    rw [Finset.sum_congr rfl hβsum, ← Finset.mul_sum, Finset.sum_boole, Finset.filter_filter]
    congr 1
    apply congrArg (fun s : Finset (V k) => (s.card : ℤ))
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      sol_R_slice_iff hk hr u v cr cc R B y P_bits (w0Of α) Rmm hcap x]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      rw [h2]; funext q; simp [tilde]
  simp only [hinner, ← Finset.mul_sum]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  norm_cast
  have hsum_card : (∑ α : Fin p → Bool,
      (Finset.univ.filter (fun x : V k => (∀ i : Fin k, P_bits i = true → x i = 0) ∧
        Gslice (mkParams u v cr cc R B) y P_bits (w0Of α) x = 0)).card) =
      (Finset.univ.filter (fun ax : (Fin p → Bool) × V k =>
        (∀ i : Fin k, P_bits i = true → ax.2 i = 0) ∧
        Gslice (mkParams u v cr cc R B) y P_bits (w0Of ax.1) ax.2 = 0)).card := by
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [hsum_card]
  apply Finset.card_nbij'
    (fun ax => bvFin (sliceVec P_bits (w0Of ax.1) ax.2))
    (fun w => (fun s : Fin p => decide (∃ i : Fin k, P_bits i = true ∧ cnt P_bits i.val = s.val ∧
        w.val.testBit i.val = true),
      fun i : Fin k => if P_bits i then 0 else toZ (w.val.testBit i.val)))
  · intro ax hax
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hax ⊢
    funext j
    have hj := congrFun hax.2 j
    rw [Gslice_eq_eval] at hj
    have h0 := toZ_eq_zero.1 hj
    have hxor : ∀ a b : Bool, xor a b = false ↔ a = b := by decide
    exact (hxor _ _).1 h0
  · intro w hw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hw ⊢
    have hslice : sliceVec P_bits (w0Of (fun s : Fin p => decide (∃ i : Fin k,
        P_bits i = true ∧ cnt P_bits i.val = s.val ∧ w.val.testBit i.val = true)))
        (fun i : Fin k => if P_bits i then 0 else toZ (w.val.testBit i.val)) =
        fun i : Fin k => w.val.testBit i.val := by
      funext i
      unfold sliceVec; dsimp only [w0Of]
      by_cases hp' : P_bits i = true
      · have hlt : cnt P_bits i.val < p := cnt_lt_rho P_bits i hp'
        simp only [hp', ite_true, Bool.true_and, dite_eq_left hlt]
        rw [Bool.eq_iff_iff, decide_eq_true_iff]
        constructor
        · rintro ⟨i', hi1, hi2, hi3⟩
          have : i' = i := cnt_inj P_bits i' i hi1 hp' hi2
          rwa [← this]
        · intro htb; exact ⟨i, hp', rfl, htb⟩
      · simp [hp', ofZ_toZ]
    have hbv : bvFin (sliceVec P_bits (w0Of (fun s : Fin p => decide (∃ i : Fin k,
        P_bits i = true ∧ cnt P_bits i.val = s.val ∧ w.val.testBit i.val = true)))
        (fun i : Fin k => if P_bits i then 0 else toZ (w.val.testBit i.val))) = w := by
      rw [hslice]; apply xz_inj; funext i; exact congrArg toZ (bvFin_testBit _ i)
    refine ⟨fun i hi => by simp [hi], ?_⟩
    funext j
    rw [Gslice_eq_eval, hbv]
    have hj := congrFun hw j
    rw [hj, Bool.xor_self]; rfl
  · intro ax hax
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hax
    ext s
    · simp only [bvFin_testBit, sliceVec]
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨i, hi1, hi2, hi3⟩
        have hlt : cnt P_bits i.val < p := cnt_lt_rho P_bits i hi1
        simp only [hi1, ite_true, w0Of, Bool.true_and, dite_eq_left hlt] at hi3
        have hfeq : (⟨cnt P_bits i.val, hlt⟩ : Fin p) = s := Fin.ext hi2
        rwa [← hfeq]
      · intro hα
        obtain ⟨i, hi1, hi2⟩ := cnt_surj P_bits s.val s.isLt
        have hlt : cnt P_bits i.val < p := cnt_lt_rho P_bits i hi1
        refine ⟨i, hi1, hi2, ?_⟩
        simp only [hi1, ite_true, w0Of, Bool.true_and, dite_eq_left hlt]
        have hfeq : (⟨cnt P_bits i.val, hlt⟩ : Fin p) = s := Fin.ext hi2
        rwa [hfeq]
    · simp only [bvFin_testBit, sliceVec]
      by_cases hp' : P_bits s = true
      · simp [hp', hax.1 s hp']
      · simp [hp', toZ_ofZ]
  · intro w _
    apply xz_inj; funext i
    dsimp only [xz]
    rw [toZ_inj, bvFin_testBit]
    unfold sliceVec; dsimp only [w0Of]
    by_cases hp' : P_bits i = true
    · have hlt : cnt P_bits i.val < p := cnt_lt_rho P_bits i hp'
      simp only [hp', ite_true, Bool.true_and, dite_eq_left hlt]
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨i', hi1, hi2, hi3⟩
        have : i' = i := cnt_inj P_bits i' i hi1 hp' hi2
        rwa [← this]
      · intro htb; exact ⟨i, hp', rfl, htb⟩
    · simp [hp', ofZ_toZ]

abbrev P2In (k r m : ℕ) : Type :=
  ParamsIn k r m ⊕ (Fin m ⊕ (Fin (k + 1) ⊕ P1Out k m))

def p2Params {k r m : ℕ} (v : P2In k r m → Bool) : ParamsIn k r m → Bool := fun x => v (Sum.inl x)
def p2Y {k r m : ℕ} (v : P2In k r m → Bool) : Fin m → Bool := fun j => v (Sum.inr (Sum.inl j))
def p2T {k r m : ℕ} (v : P2In k r m → Bool) : Fin (k + 1) → Bool := fun i => v (Sum.inr (Sum.inr (Sum.inl i)))
def p2Pass {k r m : ℕ} (v : P2In k r m → Bool) : Bool := v (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))
def p2P {k r m : ℕ} (v : P2In k r m → Bool) : Fin k → Bool := fun i => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
def p2R {k r m : ℕ} (v : P2In k r m → Bool) : Fin m × Fin m → Bool := fun p => v (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))))

noncomputable def phase2Out (k r m b : ℕ) (v : P2In k r m → Bool) : Bool :=
  let W := k + b + 3
  let tot : BitVec W := ((Finset.univ : Finset (Fin b → Bool)).toList.map (fun σ =>
    if validMask (p2P v) (p2R v) σ then
      sliceTermBV W (p2Params v) (p2Y v) (p2P v) (w0Mask (p2P v) σ) (gamMask (p2P v) (p2R v) σ)
        (R_slice (p2Params v) (p2Y v) (p2P v) (w0Mask (p2P v) σ) (p2R v))
    else 0)).sum
  let tBV : BitVec W := bv (fun i : Fin W => if hi : i.val < k + 1 then p2T v ⟨i.val, hi⟩ else false)
  let tScaled : BitVec W := (List.finRange m).foldl
    (fun (x : BitVec W) j => if p2R v (j, j) then x <<< 1 else x) tBV
  p2Pass v && !(tot - tScaled).getLsbD (W - 1)

theorem phase2Out_spec {k r m b : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (u v0 : Fin (2 ^ k))
    (cr cc : Fin r → Fin (2 ^ k)) (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (t : Fin (2 ^ (k + 1))) (p1 : P1Out k m → Bool)
    (hspec : p1 (Sum.inl ()) = true →
      let P := Finset.univ.filter (fun i : Fin k => p1 (Sum.inr (Sum.inl i)) = true)
      let Rmm : Fin m × Fin m → Bool := fun p => p1 (Sum.inr (Sum.inr p))
      GJF Rmm ∧ P.card + rhoM Rmm ≤ b ∧
      ∀ a ∈ activeN r R B, (leftN r P a).card ≤ if tilde Rmm (colN r R B a) = 0 then 2 else 1) :
    let vin : P2In k r m → Bool := Sum.elim (mkParams u v0 cr cc R B)
      (Sum.elim y (Sum.elim (fun i : Fin (k + 1) => t.val.testBit i.val) p1))
    let hits := Nat.card {w : Fin (2 ^ k) // (fun j => xor (parityN k (R j).val (stateN k r false w.val u.val cr))
      (parityN k (B j).val (stateN k r true w.val v0.val cc))) = y}
    phase2Out k r m b vin = decide (p1 (Sum.inl ()) = true ∧ t.val ≤ hits) := by
  intro vin hits
  unfold phase2Out
  cases hp : p1 (Sum.inl ())
  · have hpass : p2Pass vin = false := hp
    simp [hpass, hp]
  · have hpass : p2Pass vin = true := hp
    simp only [hpass, Bool.true_and, true_and]
    obtain ⟨hR, hPb, hcap⟩ := hspec hp
    have hgood : ∀ a ∈ activeN r R B,
        (leftN r (Finset.univ.filter (fun i : Fin k => p2P vin i = true)) a).card ≤ 2 := by
      intro a ha
      have h1 : (leftN r (Finset.univ.filter (fun i : Fin k => p2P vin i = true)) a).card ≤
          if tilde (p2R vin) (colN r R B a) = 0 then 2 else 1 := hcap a ha
      by_cases ht : tilde (p2R vin) (colN r R B a) = 0 <;> simp [ht] at h1 <;> omega
    set W := k + b + 3
    have hW : k < W := by omega
    have hsum_bv : ∀ (L : List (Fin b → Bool)) (f : (Fin b → Bool) → ℤ),
        (L.map (fun σ => BitVec.ofInt W (f σ))).sum = BitVec.ofInt W ((L.map f).sum) := by
      intro L f
      induction L with
      | nil => rfl
      | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, BitVec.ofInt_add]
    have hterm : ∀ σ : Fin b → Bool,
        (if validMask (p2P vin) (p2R vin) σ = true then
          sliceTermBV W (p2Params vin) (p2Y vin) (p2P vin) (w0Mask (p2P vin) σ) (gamMask (p2P vin) (p2R vin) σ)
            (R_slice (p2Params vin) (p2Y vin) (p2P vin) (w0Mask (p2P vin) σ) (p2R vin))
        else (0 : BitVec W)) =
        BitVec.ofInt W (if validMask (p2P vin) (p2R vin) σ = true then
          ∑ x ∈ Finset.univ.filter (Sol (R_slice (mkParams u v0 cr cc R B) y (p2P vin)
              (w0Mask (p2P vin) σ) (p2R vin))),
            sgnZ (∑ j : Fin m, toZ (gamMask (p2P vin) (p2R vin) σ j) *
              Gslice (mkParams u v0 cr cc R B) y (p2P vin) (w0Mask (p2P vin) σ) x j)
        else 0) := by
      intro σ
      by_cases hv : validMask (p2P vin) (p2R vin) σ = true
      · rw [ite_eq_left hv, ite_eq_left hv]
        exact sliceTermBV_eq W hW (mkParams u v0 cr cc R B) y (p2P vin) (w0Mask (p2P vin) σ)
          (gamMask (p2P vin) (p2R vin) σ) _ (R_aff_flatOK _ _ _)
          (Gslice_isQuad hk hr u v0 cr cc R B y (p2P vin) (w0Mask (p2P vin) σ) hgood)
      · rw [ite_eq_right hv, ite_eq_right hv]; rfl
    have htot_eq : ((Finset.univ : Finset (Fin b → Bool)).toList.map (fun σ =>
        if validMask (p2P vin) (p2R vin) σ = true then
          sliceTermBV W (p2Params vin) (p2Y vin) (p2P vin) (w0Mask (p2P vin) σ) (gamMask (p2P vin) (p2R vin) σ)
            (R_slice (p2Params vin) (p2Y vin) (p2P vin) (w0Mask (p2P vin) σ) (p2R vin))
        else 0)).sum = BitVec.ofInt W ((2 : ℤ) ^ rhoM (p2R vin) * (hits : ℤ)) := by
      have hm := List.map_congr_left (l := (Finset.univ : Finset (Fin b → Bool)).toList)
        (fun σ _ => hterm σ)
      rw [hm, hsum_bv]
      congr 1
      have hlist : ((Finset.univ : Finset (Fin b → Bool)).toList.map (fun σ =>
          if validMask (p2P vin) (p2R vin) σ = true then
            ∑ x ∈ Finset.univ.filter (Sol (R_slice (mkParams u v0 cr cc R B) y (p2P vin)
                (w0Mask (p2P vin) σ) (p2R vin))),
              sgnZ (∑ j : Fin m, toZ (gamMask (p2P vin) (p2R vin) σ j) *
                Gslice (mkParams u v0 cr cc R B) y (p2P vin) (w0Mask (p2P vin) σ) x j)
          else (0 : ℤ))).sum =
          ∑ σ : Fin b → Bool, (if validMask (p2P vin) (p2R vin) σ = true then
            ∑ x ∈ Finset.univ.filter (Sol (R_slice (mkParams u v0 cr cc R B) y (p2P vin)
                (w0Mask (p2P vin) σ) (p2R vin))),
              sgnZ (∑ j : Fin m, toZ (gamMask (p2P vin) (p2R vin) σ j) *
                Gslice (mkParams u v0 cr cc R B) y (p2P vin) (w0Mask (p2P vin) σ) x j)
          else (0 : ℤ)) := by
        rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl
      rw [hlist]
      exact sum_contrib_eq hk hr u v0 cr cc R B y (p2P vin) (p2R vin) hR hPb hcap
    have htBV : bv (fun i : Fin W => if hi : i.val < k + 1 then p2T vin ⟨i.val, hi⟩ else false) =
        BitVec.ofNat W t.val := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [getLsbD_bv _ ⟨i, hi⟩, BitVec.getLsbD_ofNat]
      simp only [hi, decide_true, Bool.true_and]
      by_cases hi1 : i < k + 1
      · rw [dite_eq_left hi1]; rfl
      · rw [dite_eq_right hi1]; symm
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le t.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have htSc : (List.finRange m).foldl (fun (x : BitVec W) j => if p2R vin (j, j) then x <<< 1 else x)
        (bv (fun i : Fin W => if hi : i.val < k + 1 then p2T vin ⟨i.val, hi⟩ else false)) =
        BitVec.ofInt W ((2 : ℤ) ^ rhoM (p2R vin) * (t.val : ℤ)) := by
      rw [htBV, foldl_dbl_ofNat, countP_finRange, ← BitVec.ofInt_natCast]
      push_cast; rfl
    rw [htot_eq, htSc, ofInt_sub_eq]
    have hdle : rhoM (p2R vin) ≤ b := le_trans (Nat.le_add_left _ _) hPb
    have hhits_le : hits ≤ 2 ^ k := by
      dsimp only [hits]
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      calc (Finset.univ.filter _).card ≤ (Finset.univ : Finset (Fin (2 ^ k))).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2 ^ k := by simp
    have h2d : (2 : ℤ) ^ rhoM (p2R vin) ≤ (2 : ℤ) ^ b :=
      pow_le_pow_right₀ (by norm_num) hdle
    have h2d_pos : (0 : ℤ) < (2 : ℤ) ^ rhoM (p2R vin) := by positivity
    have h1 : (2 : ℤ) ^ rhoM (p2R vin) * (hits : ℤ) < (2 : ℤ) ^ (W - 1) := by
      have hh : (hits : ℤ) ≤ (2 : ℤ) ^ k := by exact_mod_cast hhits_le
      have hp : (2 : ℤ) ^ b * (2 : ℤ) ^ k < (2 : ℤ) ^ (W - 1) := by
        rw [← pow_add]; exact pow_lt_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have h2 : (2 : ℤ) ^ rhoM (p2R vin) * (t.val : ℤ) < (2 : ℤ) ^ (W - 1) := by
      have ht : (t.val : ℤ) < (2 : ℤ) ^ (k + 1) := by exact_mod_cast t.isLt
      have hp : (2 : ℤ) ^ b * (2 : ℤ) ^ (k + 1) ≤ (2 : ℤ) ^ (W - 1) := by
        rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    rw [ofInt_msb_iff (by omega) _ (by nlinarith) (by nlinarith)]
    rw [Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, not_lt]
    constructor
    · intro h
      have hle : (2 : ℤ) ^ rhoM (p2R vin) * (t.val : ℤ) ≤ (2 : ℤ) ^ rhoM (p2R vin) * (hits : ℤ) := by linarith
      have : (t.val : ℤ) ≤ (hits : ℤ) := le_of_mul_le_mul_left hle h2d_pos
      exact_mod_cast this
    · intro h
      have : (t.val : ℤ) ≤ (hits : ℤ) := by exact_mod_cast h
      nlinarith

theorem cmp_phase2 (k r m b : ℕ) (hbk : b < k) :
    Cb (P2In k r m) (2 ^ b * (4096 * (k + r + m + 6) ^ 5) + 1024 * (k + r + m + 6) ^ 3)
      (phase2Out k r m b) := by
  set N := k + r + m + 6
  set W := k + b + 3
  have hkN : k + 1 ≤ N := by omega
  have hmN : m + 1 ≤ N := by omega
  have hrN : r + 1 ≤ N := by omega
  have hbN : b ≤ N := by omega
  have hWN : W ≤ 2 * N := by omega
  have hWpos : k < W := by omega
  have h6N : 6 ≤ N := by omega
  let Pre := P2In k r m ⊕ ((Fin (k + 1) × Fin (k + 1)) ⊕ (Fin (m + 1) × Fin (m + 1)))
  have hcntP : Cmp (P2In k r m) (Fin (k + 1) × Fin (k + 1)) ((k + 1) * ((k + 1) * 6))
      (fun v p => decide (cnt (p2P v) p.1.val = p.2.val)) :=
    Cmp.sel (fun i : Fin k => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))) (cmp_counter k k)
  have hcntD : Cmp (P2In k r m) (Fin (m + 1) × Fin (m + 1)) ((m + 1) * ((m + 1) * 6))
      (fun v p => decide (cnt (fun j : Fin m => p2R v (j, j)) p.1.val = p.2.val)) :=
    Cmp.sel (fun j : Fin m => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, j)))))) (cmp_counter m m)
  have hpre : Cmp (P2In k r m) Pre ((k + 1) * ((k + 1) * 6) + (m + 1) * ((m + 1) * 6))
      (fun v => Sum.elim v (Sum.elim (fun p => decide (cnt (p2P v) p.1.val = p.2.val))
        (fun p => decide (cnt (fun j : Fin m => p2R v (j, j)) p.1.val = p.2.val)))) :=
    Cmp.mono (Cmp.keep (Cmp.pair hcntP hcntD)) (by omega)
  let validPre : (Fin b → Bool) → (Pre → Bool) → Bool := fun σ w =>
    decide (∀ q : Fin b, (!σ q || decide (∃ ts : Fin (k + 1) × Fin (m + 1),
      (decide (q.val < ts.1.val + ts.2.val) && (w (Sum.inr (Sum.inl (Fin.last k, ts.1))) &&
        w (Sum.inr (Sum.inr (Fin.last m, ts.2))))) = true)) = true)
  let w0Pre : (Fin b → Bool) → (Pre → Bool) → Fin k → Bool := fun σ w i =>
    p2P (fun x => w (Sum.inl x)) i &&
      decide (∃ q : Fin b, (σ q && w (Sum.inr (Sum.inl (i.castSucc, ⟨q.val, by omega⟩)))) = true)
  let gamPre : (Fin b → Bool) → (Pre → Bool) → Fin m → Bool := fun σ w j =>
    p2R (fun x => w (Sum.inl x)) (j, j) &&
      decide (∃ qt : Fin b × Fin (k + 1),
        (σ qt.1 && (w (Sum.inr (Sum.inl (Fin.last k, qt.2))) &&
          (if h : qt.2.val ≤ qt.1.val ∧ qt.1.val - qt.2.val < m + 1 then
            w (Sum.inr (Sum.inr (j.castSucc, ⟨qt.1.val - qt.2.val, h.2⟩))) else false))) = true)
  let St1 := Pre ⊕ (Unit ⊕ (Fin k ⊕ Fin m))
  let St2 := St1 ⊕ (Fin (k + 1) × Fin (k + 1))
  let St3 := St2 ⊕ (Fin (k + 1) × Fin (k + 1))
  let St4 := St2 ⊕ GW k W
  have hslot : ∀ σ : Fin b → Bool, Cw Pre W (2048 * N ^ 5)
      (fun w =>
        let v := fun x => w (Sum.inl x)
        let w0 := w0Pre σ w
        let gam := gamPre σ w
        let R_s := R_slice (p2Params v) (p2Y v) (p2P v) w0 (p2R v)
        if validPre σ w then
          sliceTermBV W (p2Params v) (p2Y v) (p2P v) w0 gam R_s
        else 0) := by
    intro σ
    have hcval : Cb Pre (b * ((k + 1) * (m + 1) * 4 + 4) + 1) (validPre σ) := by
      have c := Cb.bigAnd (ι := Pre) (I := Fin b) (s := (k + 1) * (m + 1) * 4 + 3) (fun q => by
        have c1 := Cb.bigOr (ι := Pre) (I := Fin (k + 1) × Fin (m + 1)) (s := 3) (fun ts =>
          Cb.mono (Cb.and (Cb.const (ι := Pre) (decide (q.val < ts.1.val + ts.2.val)))
            (Cb.and (Cb.var (ι := Pre) (Sum.inr (Sum.inl (Fin.last k, ts.1))))
              (Cb.var (ι := Pre) (Sum.inr (Sum.inr (Fin.last m, ts.2)))))) (by omega))
        simp only [Fintype.card_prod, Fintype.card_fin] at c1
        exact Cb.mono (Cb.or (Cb.const (ι := Pre) (!σ q)) c1) (by omega))
      rw [Fintype.card_fin] at c
      exact Cb.mono (Cb.congr c (fun w => Bool.eq_iff_iff.2 (by dsimp only [validPre]; simp))) (by ring_nf; omega)
    have hcw0 : Cmp Pre (Fin k) (k * (b * 3 + 2)) (w0Pre σ) := by
      have h := Cmp.ofBits (ι := Pre) (κ := Fin k) (s := b * 3 + 2) (F := w0Pre σ) (fun i => by
        have c := Cb.bigOr (ι := Pre) (I := Fin b) (s := 2) (fun q =>
          Cb.and (Cb.const (ι := Pre) (σ q))
            (Cb.var (ι := Pre) (Sum.inr (Sum.inl (i.castSucc, ⟨q.val, by omega⟩)))))
        rw [Fintype.card_fin] at c
        exact Cb.mono (Cb.congr (Cb.and (Cb.var (ι := Pre)
            (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))) c)
          (fun w => Bool.eq_iff_iff.2 (by dsimp only [w0Pre, p2P]; simp))) (by omega))
      rw [Fintype.card_fin] at h; exact h
    have hcgam : Cmp Pre (Fin m) (m * (b * (k + 1) * 5 + 2)) (gamPre σ) := by
      have h := Cmp.ofBits (ι := Pre) (κ := Fin m) (s := b * (k + 1) * 5 + 2) (F := gamPre σ) (fun j => by
        have c := Cb.bigOr (ι := Pre) (I := Fin b × Fin (k + 1)) (s := 4)
          (φ := fun qt w => σ qt.1 && (w (Sum.inr (Sum.inl (Fin.last k, qt.2))) &&
            (if h : qt.2.val ≤ qt.1.val ∧ qt.1.val - qt.2.val < m + 1 then
              w (Sum.inr (Sum.inr (j.castSucc, ⟨qt.1.val - qt.2.val, h.2⟩))) else false))) (fun qt => by
          by_cases hq : qt.2.val ≤ qt.1.val ∧ qt.1.val - qt.2.val < m + 1
          · exact Cb.mono (Cb.congr (Cb.and (Cb.const (ι := Pre) (σ qt.1))
              (Cb.and (Cb.var (ι := Pre) (Sum.inr (Sum.inl (Fin.last k, qt.2))))
                (Cb.var (ι := Pre) (Sum.inr (Sum.inr (j.castSucc, ⟨qt.1.val - qt.2.val, hq.2⟩))))))
              (fun w => by simp [hq])) (by omega)
          · exact Cb.mono (Cb.congr (Cb.const (ι := Pre) false) (fun w => by rw [dite_eq_right hq]; simp)) (by omega))
        simp only [Fintype.card_prod, Fintype.card_fin] at c
        exact Cb.mono (Cb.congr (Cb.and (Cb.var (ι := Pre)
            (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, j)))))))) c)
          (fun w => Bool.eq_iff_iff.2 (by dsimp only [gamPre, p2R]; simp))) (by omega))
      rw [Fintype.card_fin] at h; exact h
    have hst1 : Cmp Pre St1
        (b * ((k + 1) * (m + 1) * 4 + 4) + 1 + (k * (b * 3 + 2) + m * (b * (k + 1) * 5 + 2)))
        (fun w => Sum.elim w (Sum.elim (fun _ => validPre σ w) (Sum.elim (w0Pre σ w) (gamPre σ w)))) :=
      Cmp.mono (Cmp.keep (Cmp.pair hcval (Cmp.pair hcw0 hcgam))) (by omega)
    have hRs : Cmp St1 (Fin (k + 1) × Fin (k + 1)) (800 * N ^ 4)
        (fun u => R_slice (p2Params (fun x => u (Sum.inl (Sum.inl x))))
          (p2Y (fun x => u (Sum.inl (Sum.inl x)))) (p2P (fun x => u (Sum.inl (Sum.inl x))))
          (fun i => u (Sum.inr (Sum.inr (Sum.inl i)))) (p2R (fun x => u (Sum.inl (Sum.inl x))))) := by
      have hGpt : ∀ c : Fin (k + 1), Cmp St1 (Fin m) (k * 5 + (128 * k * (r + 1) + m * (10 * k + 6)) + m * 4)
          (fun u j => ofZ (Gslice (p2Params (fun x => u (Sum.inl (Sum.inl x))))
            (p2Y (fun x => u (Sum.inl (Sum.inl x)))) (p2P (fun x => u (Sum.inl (Sum.inl x))))
            (fun i => u (Sum.inr (Sum.inr (Sum.inl i)))) (ind c) j)) := by
        intro c
        have hvec : Cmp St1 (Fin k) (k * 5)
            (fun u i => sliceVec (p2P (fun x => u (Sum.inl (Sum.inl x))))
              (fun q => u (Sum.inr (Sum.inr (Sum.inl q)))) (ind c) i) := by
          have h := Cmp.ofBits (ι := St1) (κ := Fin k) (s := 5)
            (F := fun u i => sliceVec (p2P (fun x => u (Sum.inl (Sum.inl x))))
              (fun q => u (Sum.inr (Sum.inr (Sum.inl q)))) (ind c) i) (fun i =>
            Cb.mono (Cb.congr (Cb.mux
              (Cb.var (ι := St1) (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))))
              (Cb.var (ι := St1) (Sum.inr (Sum.inr (Sum.inl i))))
              (Cb.const (ι := St1) (decide (Fin.castSucc i = c))))
              (fun u => by
                unfold sliceVec ind p2P
                by_cases hc' : Fin.castSucc i = c <;> simp [hc', ofZ])) (by omega))
          rw [Fintype.card_fin] at h; exact h
        have hEv := Cmp.comp (Cmp.pair hvec (Cmp.wire (ι := St1) (fun x : ParamsIn k r m => Sum.inl (Sum.inl (Sum.inl x)))))
          (cmp_evalF k r m)
        have hXor : Cmp (St1 ⊕ Fin m) (Fin m) (m * 4)
            (fun w j => xor (w (Sum.inr j)) (w (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl j))))))) := by
          have h := Cmp.ofBits (ι := St1 ⊕ Fin m) (κ := Fin m) (s := 4)
            (fun j => Cb.xor (Cb.var (ι := St1 ⊕ Fin m) (Sum.inr j))
              (Cb.var (ι := St1 ⊕ Fin m) (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl j)))))))
          rw [Fintype.card_fin] at h; exact h
        exact Cmp.mono (Cmp.congr (Cmp.thn hEv hXor)
          (fun u j => by simp only [Gslice, ofZ_toZ, Sum.elim_inl, Sum.elim_inr, p2Params, p2Y]; rfl)) (by omega)
      have hGall := Cmp.piU hGpt
      rw [Fintype.card_fin] at hGall
      let Jg := St1 ⊕ (Fin (k + 1) × Fin m)
      have hTall : Cmp Jg (Fin (k + 1) × Fin m) ((k + 1) * m * (m * 5 + 6))
          (fun w cm => xor (w (Sum.inr cm))
            (ofZ (∑ p : Fin m, toZ (w (Sum.inr (cm.1, p)) &&
              p2R (fun x => w (Sum.inl (Sum.inl (Sum.inl x)))) (p, cm.2))))) := by
        have h := Cmp.ofBits (ι := Jg) (κ := Fin (k + 1) × Fin m) (s := m * 5 + 6) (fun cm => by
          have cs := Cb.sumZ (ι := Jg) (I := Fin m) (fun p => Cb.and
            (Cb.var (ι := Jg) (Sum.inr (cm.1, p)))
            (Cb.var (ι := Jg) (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (p, cm.2)))))))))))
          rw [Fintype.card_fin] at cs
          exact Cb.mono (Cb.xor (Cb.var (ι := Jg) (Sum.inr cm)) cs) (by omega))
        simp only [Fintype.card_prod, Fintype.card_fin] at h; exact h
      have hT := Cmp.thn hGall hTall
      let Jt := St1 ⊕ (Fin (k + 1) × Fin m)
      have hM : Cmp Jt (Fin ((k + 1) + (k + m)) × Fin ((k + 1) + (k + m)))
          (((k + 1) + (k + m)) * ((k + 1) + (k + m)) * 5)
          (fun w p => M_aff (p2P (fun x => w (Sum.inl (Sum.inl (Sum.inl x)))))
            (fun j => w (Sum.inr (Fin.last k, j)))
            (fun i j => w (Sum.inr (i.castSucc, j))) p) := by
        have h := Cmp.ofBits (ι := Jt) (κ := Fin ((k + 1) + (k + m)) × Fin ((k + 1) + (k + m))) (s := 5)
          (F := fun w p => M_aff (p2P (fun x => w (Sum.inl (Sum.inl (Sum.inl x)))))
            (fun j => w (Sum.inr (Fin.last k, j)))
            (fun i j => w (Sum.inr (i.castSucc, j))) p)
          (fun p => by
            by_cases h1 : p.1.val < k + 1
            · exact Cb.mono (Cb.congr (Cb.const false) (fun w => by simp [M_aff, splitF, h1])) (by omega)
            · by_cases h2 : p.2.val < k + 1
              · by_cases h3 : p.1.val - (k + 1) < k
                · by_cases h4 : (⟨p.2.val, h2⟩ : Fin (k + 1)) = (⟨p.1.val - (k + 1), h3⟩ : Fin k).castSucc
                  · exact Cb.mono (Cb.congr (Cb.var (ι := Jt)
                      (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨p.1.val - (k + 1), h3⟩)))))))))
                      (fun w => by simp [M_aff, splitF, h1, h2, h3, h4, p2P])) (by omega)
                  · have h4' : p.2.val ≠ p.1.val - (k + 1) := fun h => h4 (Fin.ext h)
                    exact Cb.mono (Cb.congr (Cb.const false)
                      (fun w => by simp [M_aff, splitF, h1, h2, h3, h4'])) (by omega)
                · by_cases h5 : p.2.val < k
                  · exact Cb.mono (Cb.congr (Cb.xor
                      (Cb.var (ι := Jt) (Sum.inr ((⟨p.2.val, h5⟩ : Fin k).castSucc, ⟨p.1.val - (k + 1) - k, by omega⟩)))
                      (Cb.var (ι := Jt) (Sum.inr (Fin.last k, ⟨p.1.val - (k + 1) - k, by omega⟩))))
                      (fun w => by simp [M_aff, splitF, h1, h2, h3, h5])) (by omega)
                  · exact Cb.mono (Cb.congr (Cb.var (ι := Jt)
                      (Sum.inr (Fin.last k, ⟨p.1.val - (k + 1) - k, by omega⟩)))
                      (fun w => by simp [M_aff, splitF, h1, h2, h3, h5])) (by omega)
              · exact Cb.mono (Cb.congr (Cb.const false) (fun w => by
                  unfold M_aff
                  simp only [splitF, h1, h2, dite_false]
                  split_ifs <;> rfl)) (by omega))
        simp only [Fintype.card_prod, Fintype.card_fin] at h; exact h
      have hGJ := Cmp.comp (Cmp.comp (Cmp.thn hT hM) (cmp_gj ((k + 1) + (k + m))))
        (Cmp.wire (fun p : Fin (k + 1) × Fin (k + 1) => (Fin.castAdd (k + m) p.1, Fin.castAdd (k + m) p.2)))
      refine Cmp.mono (Cmp.congr hGJ ?_) ?_
      · intro u p
        have hTeq : ∀ (c : Fin (k + 1)) (j : Fin m),
            xor (ofZ (Gslice (p2Params (fun x => u (Sum.inl (Sum.inl x)))) (p2Y (fun x => u (Sum.inl (Sum.inl x))))
              (p2P (fun x => u (Sum.inl (Sum.inl x)))) (fun i => u (Sum.inr (Sum.inr (Sum.inl i)))) (ind c) j))
              (ofZ (∑ q : Fin m, toZ (ofZ (Gslice (p2Params (fun x => u (Sum.inl (Sum.inl x))))
                (p2Y (fun x => u (Sum.inl (Sum.inl x)))) (p2P (fun x => u (Sum.inl (Sum.inl x))))
                (fun i => u (Sum.inr (Sum.inr (Sum.inl i)))) (ind c) q) &&
                p2R (fun x => u (Sum.inl (Sum.inl x))) (q, j)))) =
            ofZ (tilde (p2R (fun x => u (Sum.inl (Sum.inl x))))
              (Gslice (p2Params (fun x => u (Sum.inl (Sum.inl x)))) (p2Y (fun x => u (Sum.inl (Sum.inl x))))
                (p2P (fun x => u (Sum.inl (Sum.inl x)))) (fun i => u (Sum.inr (Sum.inr (Sum.inl i)))) (ind c)) j) := by
          intro c j
          unfold tilde
          rw [ofZ_add]
          congr 2
          apply Finset.sum_congr rfl; intro q _; rw [toZ_and, toZ_ofZ]
        change gj _ (M_aff _ _ _) _ = gj _ (M_aff _ _ _) _
        congr 2
        · funext j; simpa [t0Of, ind_last] using hTeq (Fin.last k) j
        · funext i j; simpa [teOf, ind_cs] using hTeq i.castSucc j
      · unfold gjCost
        have hD : (k + 1) + (k + m) + 1 ≤ 2 * N := by omega
        have e1 : (k + 1) * (k * 5 + (128 * k * (r + 1) + m * (10 * k + 6)) + m * 4) ≤ 160 * N ^ 3 := by
          have : k * 5 + (128 * k * (r + 1) + m * (10 * k + 6)) + m * 4 ≤ 160 * N ^ 2 := by
            have : k ≤ N := by omega
            have : m ≤ N := by omega
            have : r + 1 ≤ N := by omega
            have : N ^ 2 = N * N := by ring
            nlinarith
          have : (k + 1) * (160 * N ^ 2) ≤ N * (160 * N ^ 2) := Nat.mul_le_mul_right _ hkN
          have : N * (160 * N ^ 2) = 160 * N ^ 3 := by ring
          nlinarith
        have e2 : (k + 1) * m * (m * 5 + 6) ≤ 10 * N ^ 3 := by
          have : m * 5 + 6 ≤ 6 * N := by omega
          have : (k + 1) * m ≤ N * N := Nat.mul_le_mul hkN (by omega)
          have : (k + 1) * m * (m * 5 + 6) ≤ (N * N) * (6 * N) := Nat.mul_le_mul this (by omega)
          have : (N * N) * (6 * N) = 6 * N ^ 3 := by ring
          omega
        have e3 : ((k + 1) + (k + m)) * ((k + 1) + (k + m)) * 5 ≤ 20 * N ^ 2 := by
          have : (k + 1) + (k + m) ≤ 2 * N := by omega
          have : ((k + 1) + (k + m)) * ((k + 1) + (k + m)) ≤ (2 * N) * (2 * N) := Nat.mul_le_mul this this
          have : (2 * N) * (2 * N) * 5 = 20 * N ^ 2 := by ring
          omega
        have e4 : 32 * ((k + 1) + (k + m) + 1) ^ 4 ≤ 512 * N ^ 4 := by
          have : 32 * ((k + 1) + (k + m) + 1) ^ 4 ≤ 32 * (2 * N) ^ 4 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 4)
          have : 32 * (2 * N) ^ 4 = 512 * N ^ 4 := by ring
          omega
        have p3 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have p2 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
    have hPt : Cmp St2 (Fin (k + 1) × Fin (k + 1)) (400 * N ^ 4)
        (fun u ab => PtS (p2Params (fun x => u (Sum.inl (Sum.inl (Sum.inl x)))))
          (p2Y (fun x => u (Sum.inl (Sum.inl (Sum.inl x)))))
          (p2P (fun x => u (Sum.inl (Sum.inl (Sum.inl x)))))
          (fun i => u (Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))))
          (fun j => u (Sum.inl (Sum.inr (Sum.inr (Sum.inr j)))))
          (fun p => u (Sum.inr p)) ab) := by
      have hOne : ∀ ab : Fin (k + 1) × Fin (k + 1),
          Cb St2 (k * 26 + (128 * k * (r + 1) + m * (10 * k + 6)) + (m * 10 + 1))
            (fun u => PtS (p2Params (fun x => u (Sum.inl (Sum.inl (Sum.inl x)))))
              (p2Y (fun x => u (Sum.inl (Sum.inl (Sum.inl x)))))
              (p2P (fun x => u (Sum.inl (Sum.inl (Sum.inl x)))))
              (fun i => u (Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))))
              (fun j => u (Sum.inl (Sum.inr (Sum.inr (Sum.inr j)))))
              (fun p => u (Sum.inr p)) ab) := by
        intro ab
        have hvec : Cmp St2 (Fin k) (k * 26)
            (fun u i => sliceVec (p2P (fun x => u (Sum.inl (Sum.inl (Sum.inl x)))))
              (fun q => u (Sum.inl (Sum.inr (Sum.inr (Sum.inl q)))))
              (piR (fun p => u (Sum.inr p)) (ptv ab.1 ab.2)) i) := by
          have h := Cmp.ofBits (ι := St2) (κ := Fin k) (s := 26) (fun i => by
            have hca : Cb St2 1 (fun u => if ab.1 = Fin.last k then false else u (Sum.inr (i.castSucc, ab.1))) := by
              by_cases ha : ab.1 = Fin.last k
              · exact Cb.congr (Cb.const false) (fun u => by simp [ha])
              · exact Cb.mono (Cb.congr (Cb.var (ι := St2) (Sum.inr (i.castSucc, ab.1))) (fun u => by simp [ha])) (by omega)
            have hcb : Cb St2 1 (fun u => if ab.2 = Fin.last k then false else u (Sum.inr (i.castSucc, ab.2))) := by
              by_cases hb' : ab.2 = Fin.last k
              · exact Cb.congr (Cb.const false) (fun u => by simp [hb'])
              · exact Cb.mono (Cb.congr (Cb.var (ι := St2) (Sum.inr (i.castSucc, ab.2))) (fun u => by simp [hb'])) (by omega)
            have hpi : Cb St2 21 (fun u => ofZ (piR (fun p => u (Sum.inr p)) (ptv ab.1 ab.2) i)) := by
              have c := Cb.xor (Cb.xor (Cb.xor (Cb.xor (Cb.const (ι := St2) (decide (Fin.castSucc i = ab.1)))
                (Cb.const (ι := St2) (decide (Fin.castSucc i = ab.2)))) hca) hcb)
                (Cb.var (ι := St2) (Sum.inr (i.castSucc, Fin.last k)))
              refine Cb.mono (Cb.congr c ?_) (by omega)
              intro u
              rw [← toZ_inj, toZ_ofZ, piR_ptv]
              simp only [toZ_xor]
              congr 1; congr 1
              · congr 1; split_ifs <;> rfl
              · split_ifs <;> rfl
            exact Cb.mono (Cb.mux
              (Cb.var (ι := St2) (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))))))
              (Cb.var (ι := St2) (Sum.inl (Sum.inr (Sum.inr (Sum.inl i))))) hpi) (by omega))
          rw [Fintype.card_fin] at h; exact h
        have hEv := Cmp.comp (Cmp.pair hvec
            (Cmp.wire (ι := St2) (fun x : ParamsIn k r m => Sum.inl (Sum.inl (Sum.inl (Sum.inl x))))))
          (cmp_evalF k r m)
        have hDot : Cb (St2 ⊕ Fin m) (m * 10 + 1)
            (fun w => ofZ (∑ j : Fin m, toZ (w (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr j))))) &&
              xor (w (Sum.inr j)) (w (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl j)))))))))) := by
          have c := Cb.sumZ (ι := St2 ⊕ Fin m) (I := Fin m) (fun j => Cb.and
            (Cb.var (ι := St2 ⊕ Fin m) (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr j))))))
            (Cb.xor (Cb.var (ι := St2 ⊕ Fin m) (Sum.inr j))
              (Cb.var (ι := St2 ⊕ Fin m) (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl j)))))))))
          rw [Fintype.card_fin] at c; exact Cb.mono c (by omega)
        refine Cb.mono (Cb.congr (Cmp.thn hEv hDot) ?_) (by omega)
        intro u
        dsimp only
        unfold PtS Gslice
        congr 1; apply Finset.sum_congr rfl; intro j _
        simp only [Sum.elim_inl, Sum.elim_inr, toZ_and, p2Params, p2Y]; rfl
      have h := Cmp.ofBits hOne
      simp only [Fintype.card_prod, Fintype.card_fin] at h
      refine Cmp.mono h ?_
      have e1 : k * 26 + (128 * k * (r + 1) + m * (10 * k + 6)) + (m * 10 + 1) ≤ 200 * N ^ 2 := by
        have : k ≤ N := by omega
        have : m ≤ N := by omega
        have : r + 1 ≤ N := by omega
        have : N ^ 2 = N * N := by ring
        nlinarith
      have e2 : (k + 1) * (k + 1) * (k * 26 + (128 * k * (r + 1) + m * (10 * k + 6)) + (m * 10 + 1)) ≤
          (N * N) * (200 * N ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul hkN hkN) e1
      have e3 : (N * N) * (200 * N ^ 2) = 200 * N ^ 4 := by ring
      omega
    have hGauss : Cmp St2 (GW k W) (800 * N ^ 5)
        (fun u => genc W (gfold (List.finRange k) (ginit (PtS (p2Params (fun x => u (Sum.inl (Sum.inl (Sum.inl x)))))
          (p2Y (fun x => u (Sum.inl (Sum.inl (Sum.inl x)))))
          (p2P (fun x => u (Sum.inl (Sum.inl (Sum.inl x)))))
          (fun i => u (Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))))
          (fun j => u (Sum.inl (Sum.inr (Sum.inr (Sum.inr j)))))
          (fun p => u (Sum.inr p)))))) := by
      have h1 := Cmp.comp hPt (cInit k W)
      have h2 := Cmp.comp h1 (Cmp.foldl (List.finRange k) (fun i w => gstepW (W := W) i w) (fun i _ => cGstep i))
      refine Cmp.mono (Cmp.congr h2 ?_) ?_
      · intro u x; rw [gfoldW hWpos]
      · rw [List.length_finRange]
        have e1 : 1 + 0 + (k * 4 + (k * k * 14 + W * 1)) ≤ 25 * N ^ 2 := by
          have : k ≤ N := by omega
          have : N ^ 2 = N * N := by ring
          nlinarith
        have e2 : k * (300 * (k + 1) ^ 4 + 20 * W * (k + 1)) ≤ 360 * N ^ 5 := by
          have a1 : 20 * W * (k + 1) ≤ 20 * (2 * N) * N :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hWN) hkN
          have a2 : 300 * (k + 1) ^ 4 ≤ 300 * N ^ 4 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkN 4)
          have a3 : 20 * (2 * N) * N = 40 * N ^ 2 := by ring
          have p2 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
          have a4 : k * (300 * (k + 1) ^ 4 + 20 * W * (k + 1)) ≤ N * (340 * N ^ 4) :=
            Nat.mul_le_mul (by omega) (by omega)
          have a5 : N * (340 * N ^ 4) = 340 * N ^ 5 := by ring
          omega
        have p4 : N ^ 4 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have p2 : N ^ 2 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
    have hOutDiv : Cw St4 W (k * (W * 5) + 40 * (W + 1))
        (fun u =>
          if u (Sum.inl (Sum.inl (Sum.inr (Sum.inl ())))) && !(u (Sum.inl (Sum.inr (Fin.last k, Fin.last k)))) then
            goutDivBV W (fun p => u (Sum.inl (Sum.inr p))) (fun x => u (Sum.inr x))
          else 0) := by
      have hvP : Cw St4 W 0 (fun u => bv (fun t : Fin W => u (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr t))))))) :=
        Cw.var (ι := St4) (W := W) (fun t : Fin W => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr t)))))
      have hmag := Cw.shrChain ((List.finRange k).map (fun i : Fin k =>
        (Sum.inl (Sum.inr (i.castSucc, i.castSucc)) : St4))) hvP
      rw [List.length_map, List.length_finRange, zero_add] at hmag
      have hmag' : Cw St4 W (k * (W * 5))
          (fun u => (List.finRange k).foldl
            (fun (x : BitVec W) i => if u (Sum.inl (Sum.inr (i.castSucc, i.castSucc))) then x >>> 1 else x)
            (bv (gP (fun x => u (Sum.inr x))))) :=
        Cw.congr hmag (fun u => by rw [List.foldl_map]; rfl)
      have hdiv : Cw St4 W (k * (W * 5) + 30 * (W + 1))
          (fun u => goutDivBV W (fun p => u (Sum.inl (Sum.inr p))) (fun x => u (Sum.inr x))) := by
        have hstep := Cmp.thn hmag' (Cw.mux (Cb.var (ι := St4 ⊕ Fin W) (Sum.inl (Sum.inr (Sum.inl ()))))
          (Cw.const (ι := St4 ⊕ Fin W) (0 : BitVec W))
          (Cw.mux (Cb.var (ι := St4 ⊕ Fin W) (Sum.inl (Sum.inr (Sum.inr (Sum.inl ())))))
            (Cw.neg (Cw.var (ι := St4 ⊕ Fin W) (W := W) Sum.inr))
            (Cw.var (ι := St4 ⊕ Fin W) (W := W) Sum.inr)))
        exact Cw.mono (Cw.congr hstep (fun u => by
          simp only [Sum.elim_inl, Sum.elim_inr, bv_getLsbD]; rfl)) (by omega)
      have hcond : Cb St4 3 (fun u => u (Sum.inl (Sum.inl (Sum.inr (Sum.inl ())))) &&
          !(u (Sum.inl (Sum.inr (Fin.last k, Fin.last k))))) :=
        Cb.mono (Cb.and (Cb.var _) (Cb.not (Cb.var _))) (by omega)
      exact Cw.mono (Cw.mux hcond hdiv (Cw.const (ι := St4) (0 : BitVec W))) (by omega)
    have hfull := Cmp.comp (Cmp.comp (Cmp.keep hRs) (Cmp.keep hGauss)) hOutDiv
    have htot := Cmp.comp hst1 hfull
    refine Cw.mono (Cw.congr htot ?_) ?_
    · intro w
      simp only [Sum.elim_inl, Sum.elim_inr, sliceTermBV]
      by_cases hv : validPre σ w = true
      · simp only [hv, Bool.true_and, ite_true]
        by_cases hlast : R_slice (p2Params (fun x => w (Sum.inl x))) (p2Y (fun x => w (Sum.inl x)))
            (p2P (fun x => w (Sum.inl x))) (w0Pre σ w) (p2R (fun x => w (Sum.inl x)))
            (Fin.last k, Fin.last k) = true
        · simp [hlast]
        · simp [hlast]
      · simp [hv]
    · have e1 : b * ((k + 1) * (m + 1) * 4 + 4) + 1 + (k * (b * 3 + 2) + m * (b * (k + 1) * 5 + 2)) ≤
          25 * N ^ 3 := by
        have h1 : (k + 1) * (m + 1) ≤ N * N := Nat.mul_le_mul hkN hmN
        have h2 : b * ((k + 1) * (m + 1) * 4 + 4) ≤ N * (N * N * 4 + 4) := by gcongr
        have h3 : k * (b * 3 + 2) ≤ N * (N * 3 + 2) := by gcongr <;> omega
        have h4 : m * (b * (k + 1) * 5 + 2) ≤ N * (N * N * 5 + 2) := by gcongr <;> omega
        have hsumN : N * (N * N * 4 + 4) + 1 + (N * (N * 3 + 2) + N * (N * N * 5 + 2)) =
            9 * N ^ 3 + 3 * N ^ 2 + 8 * N + 1 := by ring
        have p2 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have p1 : N ≤ N ^ 3 := by
          calc N = N ^ 1 := by ring
            _ ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have p0 : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ (by omega)
        have htotN : b * ((k + 1) * (m + 1) * 4 + 4) + 1 + (k * (b * 3 + 2) + m * (b * (k + 1) * 5 + 2)) ≤
            N * (N * N * 4 + 4) + 1 + (N * (N * 3 + 2) + N * (N * N * 5 + 2)) := by omega
        rw [hsumN] at htotN
        omega
      have e2 : k * (W * 5) + 40 * (W + 1) ≤ 100 * N ^ 2 := by
        have : k * (W * 5) ≤ N * (2 * N * 5) := by gcongr <;> omega
        have : N * (2 * N * 5) = 10 * N ^ 2 := by ring
        have : N ≤ N ^ 2 := by
          calc N = N ^ 1 := by ring
            _ ≤ N ^ 2 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
      have p4 : N ^ 4 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have p3 : N ^ 3 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have p2 : N ^ 2 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
  have hsum := Cw.lsum _ hslot (Finset.univ : Finset (Fin b → Bool)).toList
  rw [Finset.length_toList, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsum
  have htBV : Cw Pre W W
      (fun w => bv (fun i : Fin W => if hi : i.val < k + 1 then p2T (fun x => w (Sum.inl x)) ⟨i.val, hi⟩ else false)) := by
    have h := Cw.ofBits (ι := Pre) (W := W) (s := 1)
      (φ := fun w => bv (fun i : Fin W => if hi : i.val < k + 1 then p2T (fun x => w (Sum.inl x)) ⟨i.val, hi⟩ else false))
      (fun i => by
        by_cases hi : i.val < k + 1
        · exact Cb.mono (Cb.congr (Cb.var (ι := Pre) (Sum.inl (Sum.inr (Sum.inr (Sum.inl ⟨i.val, hi⟩)))))
            (fun w => by rw [getLsbD_bv, dite_eq_left hi]; rfl)) (by omega)
        · exact Cb.congr (Cb.const false)
            (fun w => by rw [getLsbD_bv, dite_eq_right hi]))
    simpa using h
  have htSc := Cw.dblChain ((List.finRange m).map (fun j : Fin m =>
    (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, j)))))) : Pre))) htBV
  rw [List.length_map, List.length_finRange] at htSc
  have hsub := Cw.sub hsum htSc
  have hmsb := Cb.comp hsub (Cb.var (ι := Fin W) ⟨W - 1, by omega⟩)
  have hfin := Cb.and (Cb.var (ι := Pre) (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))) (Cb.not hmsb)
  have htot := Cb.comp hpre hfin
  refine Cb.mono (Cb.congr htot ?_) ?_
  · intro v
    let pv : Pre → Bool := Sum.elim v (Sum.elim (fun p => decide (cnt (p2P v) p.1.val = p.2.val))
      (fun p => decide (cnt (fun j : Fin m => p2R v (j, j)) p.1.val = p.2.val)))
    have hval_eq : ∀ σ : Fin b → Bool, validPre σ pv = validMask (p2P v) (p2R v) σ := by
      intro σ
      rw [Bool.eq_iff_iff]
      simp only [validPre, validMask, decide_eq_true_eq, pv, Sum.elim_inr, Sum.elim_inl, Fin.val_last,
        cnt_full, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true]
      constructor
      · intro h q hq
        rcases h q with hf | ⟨ts, hlt, h1, h2⟩
        · rw [hq] at hf; exact absurd hf (by decide)
        · omega
      · intro h q
        by_cases hq : σ q = true
        · right
          have hp : cnt (p2P v) k ≤ k := by
            rw [cnt_full]
            calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.filter_subset _ _)
              _ = k := by simp
          have hd : cnt (fun j => p2R v (j, j)) m ≤ m := by
            rw [cnt_full]
            calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.filter_subset _ _)
              _ = m := by simp
          refine ⟨(⟨cnt (p2P v) k, by omega⟩, ⟨cnt (fun j => p2R v (j, j)) m, by omega⟩), ?_, ?_, ?_⟩
          · simpa [cnt_full] using h q hq
          · simp [cnt_full]
          · simp [cnt_full]
        · left; simpa using hq
    have hw0_eq : ∀ σ : Fin b → Bool, w0Pre σ pv = w0Mask (p2P v) σ := by
      intro σ; funext i
      unfold w0Mask; dsimp only [w0Pre]
      have h1 : p2P (fun x => pv (Sum.inl x)) i = p2P v i := rfl
      rw [h1]; congr 1
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
      simp only [pv, Sum.elim_inr, Sum.elim_inl, Bool.and_eq_true, decide_eq_true_eq, Fin.val_castSucc]
    have hgam_eq : ∀ σ : Fin b → Bool, gamPre σ pv = gamMask (p2P v) (p2R v) σ := by
      intro σ; funext j
      unfold gamMask; dsimp only [gamPre]
      have h1 : p2R (fun x => pv (Sum.inl x)) (j, j) = p2R v (j, j) := rfl
      rw [h1]; congr 1
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨⟨q, t⟩, hqt⟩
        simp only [pv, Sum.elim_inr, Sum.elim_inl, Bool.and_eq_true, decide_eq_true_eq, Fin.val_last] at hqt
        rcases hqt with ⟨hq, ht, hif⟩
        by_cases hcond : t.val ≤ q.val ∧ q.val - t.val < m + 1
        · rw [dite_eq_left hcond] at hif
          simp only [decide_eq_true_eq, Fin.val_castSucc] at hif
          exact ⟨q, hq, by omega⟩
        · rw [dite_eq_right hcond] at hif; exact absurd hif (by decide)
      · rintro ⟨q, hq, hsum⟩
        have hp : cnt (p2P v) k ≤ k := by
          rw [cnt_full]
          calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.filter_subset _ _)
            _ = k := by simp
        have hd : cnt (fun j' => p2R v (j', j')) j.val ≤ m := by
          calc cnt (fun j' => p2R v (j', j')) j.val ≤ (Finset.univ : Finset (Fin m)).card :=
                Finset.card_le_card (Finset.filter_subset _ _)
            _ = m := by simp
        refine ⟨(q, ⟨cnt (p2P v) k, by omega⟩), ?_⟩
        simp only [pv, Sum.elim_inr, Sum.elim_inl, Bool.and_eq_true, decide_eq_true_eq, Fin.val_last]
        refine ⟨hq, trivial, ?_⟩
        have hcond : cnt (p2P v) k ≤ q.val ∧ q.val - cnt (p2P v) k < m + 1 := by omega
        rw [dite_eq_left hcond]
        simp only [decide_eq_true_eq, Fin.val_castSucc]
        omega
    unfold phase2Out
    have hlmap : ((Finset.univ : Finset (Fin b → Bool)).toList.map (fun σ =>
        if validPre σ pv = true then
          sliceTermBV W (p2Params (fun x => pv (Sum.inl x))) (p2Y (fun x => pv (Sum.inl x)))
            (p2P (fun x => pv (Sum.inl x))) (w0Pre σ pv) (gamPre σ pv)
            (R_slice (p2Params (fun x => pv (Sum.inl x))) (p2Y (fun x => pv (Sum.inl x)))
              (p2P (fun x => pv (Sum.inl x))) (w0Pre σ pv) (p2R (fun x => pv (Sum.inl x))))
        else 0)) =
        ((Finset.univ : Finset (Fin b → Bool)).toList.map (fun σ =>
          if validMask (p2P v) (p2R v) σ = true then
            sliceTermBV W (p2Params v) (p2Y v) (p2P v) (w0Mask (p2P v) σ) (gamMask (p2P v) (p2R v) σ)
              (R_slice (p2Params v) (p2Y v) (p2P v) (w0Mask (p2P v) σ) (p2R v))
          else 0)) := by
      apply List.map_congr_left
      intro σ _
      rw [hval_eq σ, hw0_eq σ, hgam_eq σ]
      rfl
    have hfold_t : ((List.finRange m).map (fun j : Fin m =>
        (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, j)))))) : Pre))).foldl
        (fun (x : BitVec W) ℓ => if pv ℓ then x <<< 1 else x)
        (bv (fun i : Fin W => if hi : i.val < k + 1 then p2T (fun x => pv (Sum.inl x)) ⟨i.val, hi⟩ else false)) =
        (List.finRange m).foldl (fun (x : BitVec W) j => if p2R v (j, j) then x <<< 1 else x)
        (bv (fun i : Fin W => if hi : i.val < k + 1 then p2T v ⟨i.val, hi⟩ else false)) := by
      rw [List.foldl_map]; rfl
    change (pv (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))) &&
      !(BitVec.getLsbD ((((Finset.univ : Finset (Fin b → Bool)).toList.map (fun σ =>
        if validPre σ pv = true then
          sliceTermBV W (p2Params (fun x => pv (Sum.inl x))) (p2Y (fun x => pv (Sum.inl x)))
            (p2P (fun x => pv (Sum.inl x))) (w0Pre σ pv) (gamPre σ pv)
            (R_slice (p2Params (fun x => pv (Sum.inl x))) (p2Y (fun x => pv (Sum.inl x)))
              (p2P (fun x => pv (Sum.inl x))) (w0Pre σ pv) (p2R (fun x => pv (Sum.inl x))))
        else 0)).sum) -
        ((List.finRange m).map (fun j : Fin m =>
          (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, j)))))) : Pre))).foldl
          (fun (x : BitVec W) ℓ => if pv ℓ then x <<< 1 else x)
          (bv (fun i : Fin W => if hi : i.val < k + 1 then p2T (fun x => pv (Sum.inl x)) ⟨i.val, hi⟩ else false))) (W - 1))) = _
    rw [hlmap, hfold_t]; rfl
  · have e1 : (k + 1) * ((k + 1) * 6) + (m + 1) * ((m + 1) * 6) ≤ 12 * N ^ 2 := by
      have : (k + 1) * ((k + 1) * 6) ≤ N * (N * 6) := by gcongr
      have : (m + 1) * ((m + 1) * 6) ≤ N * (N * 6) := by gcongr
      have : N * (N * 6) + N * (N * 6) = 12 * N ^ 2 := by ring
      omega
    have e2 : 2 ^ b * (2048 * N ^ 5 + 20 * (W + 1)) + W ≤ 2 ^ b * (4096 * N ^ 5) := by
      have : 20 * (W + 1) + W ≤ 2048 * N ^ 5 := by
        have p1 : N ≤ N ^ 5 := by
          calc N = N ^ 1 := by ring
            _ ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
      have hp : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      nlinarith
    have e3 : W + m * (W * 5) + 20 * (W + 1) + 4 ≤ 100 * N ^ 2 := by
      have : m * (W * 5) ≤ N * (2 * N * 5) := by gcongr <;> omega
      have : N * (2 * N * 5) = 10 * N ^ 2 := by ring
      have : N ≤ N ^ 2 := by
        calc N = N ^ 1 := by ring
          _ ≤ N ^ 2 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    have p2 : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

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

def bitsN (n x : ℕ) : List Bool := (List.range n).map (fun i => x.testBit i)

def bankN {k m : ℕ} (A : Fin m → Fin (2 ^ k)) : List Bool :=
  (List.finRange m).flatMap (fun j => bitsN k (A j).val)

def schedN {k r : ℕ} (c : Fin r → Fin (2 ^ k)) : List Bool :=
  (List.finRange r).flatMap (fun j => bitsN k (c j).val)

theorem bitsN_len (n x : ℕ) : (bitsN n x).length = n := by simp [bitsN]

theorem bitsN_getD (n x i : ℕ) (hi : i < n) : (bitsN n x).getD i false = x.testBit i := by
  unfold bitsN
  rw [List.getD_eq_getElem _ _ (by simp [hi])]
  simp

theorem bankN_len {k m : ℕ} (A : Fin m → Fin (2 ^ k)) : (bankN A).length = m * k := by
  unfold bankN; rw [flat_len _ k (fun j => bitsN_len k _)]; simp

theorem schedN_len {k r : ℕ} (c : Fin r → Fin (2 ^ k)) : (schedN c).length = r * k := by
  unfold schedN; rw [flat_len _ k (fun j => bitsN_len k _)]; simp

theorem bankN_getD {k m : ℕ} (A : Fin m → Fin (2 ^ k)) (j : Fin m) (i : Fin k) :
    (bankN A).getD (j.val * k + i.val) false = (A j).val.testBit i.val := by
  unfold bankN
  rw [flat_getD false _ k (fun q => bitsN_len k _) _ j.val (by simp) i.val i.isLt]
  simp only [List.getElem_finRange, Fin.eta]
  exact bitsN_getD k _ i.val i.isLt

theorem schedN_getD {k r : ℕ} (c : Fin r → Fin (2 ^ k)) (j : Fin r) (i : Fin k) :
    (schedN c).getD (j.val * k + i.val) false = (c j).val.testBit i.val := by
  unfold schedN
  rw [flat_getD false _ k (fun q => bitsN_len k _) _ j.val (by simp) i.val i.isLt]
  simp only [List.getElem_finRange, Fin.eta]
  exact bitsN_getD k _ i.val i.isLt

abbrev MainIn (k r m : ℕ) : Type :=
  ParamsIn k r m ⊕ (Fin m ⊕ (Fin (k + 1) ⊕ Fin (k + 1)))

def mkMain {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (t : Fin (2 ^ (k + 1))) (mode : Fin (k + 1)) : MainIn k r m → Bool :=
  Sum.elim (mkParams u v cr cc R B)
    (Sum.elim y (Sum.elim (fun i : Fin (k + 1) => t.val.testBit i.val)
      (fun i : Fin (k + 1) => mode.val.testBit i.val)))

def mainInput {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (t : Fin (2 ^ (k + 1))) (mode : Fin (k + 1)) : List Bool :=
  bitsN k u.val ++ bitsN k v.val ++ schedN cr ++ schedN cc ++ bankN R ++ bankN B ++
    List.ofFn y ++ bitsN (k + 1) t.val ++ bitsN (k + 1) mode.val

theorem mainInput_len {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (t : Fin (2 ^ (k + 1))) (mode : Fin (k + 1)) :
    (mainInput u v cr cc R B y t mode).length =
      2 * k + 2 * r * k + 2 * m * k + m + 2 * (k + 1) := by
  unfold mainInput
  simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]
  ring

def mainPos (k r m : ℕ) : MainIn k r m → ℕ :=
  Sum.elim
    (Sum.elim
      (Sum.elim (fun i : Fin k => i.val) (fun i : Fin k => k + i.val))
      (Sum.elim
        (Sum.elim (fun p : Fin r × Fin k => 2 * k + (p.1.val * k + p.2.val))
          (fun p : Fin r × Fin k => 2 * k + r * k + (p.1.val * k + p.2.val)))
        (Sum.elim (fun p : Fin m × Fin k => 2 * k + 2 * r * k + (p.1.val * k + p.2.val))
          (fun p : Fin m × Fin k => 2 * k + 2 * r * k + m * k + (p.1.val * k + p.2.val)))))
    (Sum.elim (fun j : Fin m => 2 * k + 2 * r * k + 2 * m * k + j.val)
      (Sum.elim (fun i : Fin (k + 1) => 2 * k + 2 * r * k + 2 * m * k + m + i.val)
        (fun i : Fin (k + 1) => 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) + i.val)))

theorem mainPos_lt (k r m : ℕ) (x : MainIn k r m) :
    mainPos k r m x < 2 * k + 2 * r * k + 2 * m * k + m + 2 * (k + 1) := by
  have hrk : 2 * r * k = r * k + r * k := by ring
  have hmk : 2 * m * k = m * k + m * k := by ring
  have hmul : ∀ {a b : ℕ} (j : Fin a) (i : Fin b), j.val * b + i.val < a * b := by
    intro a b j i
    have h1 : j.val * b + b ≤ a * b := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ j.isLt
    have := i.isLt; omega
  rcases x with ((((i | i) | ((⟨j, i⟩ | ⟨j, i⟩) | (⟨j, i⟩ | ⟨j, i⟩)))) | (j | (i | i)))
  · simp only [mainPos, Sum.elim_inl]; have := i.isLt; omega
  · simp only [mainPos, Sum.elim_inl, Sum.elim_inr]; have := i.isLt; omega
  · simp only [mainPos, Sum.elim_inl, Sum.elim_inr]; have := hmul j i; omega
  · simp only [mainPos, Sum.elim_inl, Sum.elim_inr]; have := hmul j i; omega
  · simp only [mainPos, Sum.elim_inl, Sum.elim_inr]; have := hmul j i; omega
  · simp only [mainPos, Sum.elim_inl, Sum.elim_inr]; have := hmul j i; omega
  · simp only [mainPos, Sum.elim_inr, Sum.elim_inl]; have := j.isLt; omega
  · simp only [mainPos, Sum.elim_inr, Sum.elim_inl]; have := i.isLt; omega
  · simp only [mainPos, Sum.elim_inr]; have := i.isLt; omega

theorem mainInput_getD {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool)
    (t : Fin (2 ^ (k + 1))) (mode : Fin (k + 1)) (x : MainIn k r m) :
    (mainInput u v cr cc R B y t mode ++ [false]).getD (mainPos k r m x) false =
      mkMain u v cr cc R B y t mode x := by
  have hrk : 2 * r * k = r * k + r * k := by ring
  have hmk : 2 * m * k = m * k + m * k := by ring
  have hmul : ∀ {a b : ℕ} (j : Fin a) (i : Fin b), j.val * b + i.val < a * b := by
    intro a b j i
    have h1 : j.val * b + b ≤ a * b := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ j.isLt
    have := i.isLt; omega
  rw [List.getD_append _ _ _ _ (by rw [mainInput_len]; exact mainPos_lt k r m x)]
  unfold mainInput
  rcases x with ((((i | i) | ((⟨j, i⟩ | ⟨j, i⟩) | (⟨j, i⟩ | ⟨j, i⟩)))) | (j | (i | i)))
  · simp only [mainPos, mkMain, mkParams, Sum.elim_inl]
    have hi := i.isLt
    repeat (rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)])
    exact bitsN_getD k u.val i.val hi
  · simp only [mainPos, mkMain, mkParams, Sum.elim_inl, Sum.elim_inr]
    have hi := i.isLt
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp only [bitsN_len]; omega)]
    rw [bitsN_len, Nat.add_sub_cancel_left]
    exact bitsN_getD k v.val i.val hi
  · simp only [mainPos, mkMain, mkParams, Sum.elim_inl, Sum.elim_inr]
    have hji := hmul j i
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, bitsN_len]; omega)]
    simp only [List.length_append, bitsN_len]
    rw [show 2 * k + (j.val * k + i.val) - (k + k) = j.val * k + i.val by omega]
    exact schedN_getD cr j i
  · simp only [mainPos, mkMain, mkParams, Sum.elim_inl, Sum.elim_inr]
    have hji := hmul j i
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len]; omega)]
    simp only [List.length_append, bitsN_len, schedN_len]
    rw [show 2 * k + r * k + (j.val * k + i.val) - (k + k + r * k) = j.val * k + i.val by omega]
    exact schedN_getD cc j i
  · simp only [mainPos, mkMain, mkParams, Sum.elim_inl, Sum.elim_inr]
    have hji := hmul j i
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len]; omega)]
    simp only [List.length_append, bitsN_len, schedN_len]
    rw [show 2 * k + 2 * r * k + (j.val * k + i.val) - (k + k + r * k + r * k) = j.val * k + i.val by omega]
    exact bankN_getD R j i
  · simp only [mainPos, mkMain, mkParams, Sum.elim_inl, Sum.elim_inr]
    have hji := hmul j i
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len]; omega)]
    simp only [List.length_append, bitsN_len, schedN_len, bankN_len]
    rw [show 2 * k + 2 * r * k + m * k + (j.val * k + i.val) - (k + k + r * k + r * k + m * k) = j.val * k + i.val by omega]
    exact bankN_getD B j i
  · simp only [mainPos, mkMain, Sum.elim_inr, Sum.elim_inl]
    have hj := j.isLt
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len]; omega)]
    simp only [List.length_append, bitsN_len, schedN_len, bankN_len]
    rw [show 2 * k + 2 * r * k + 2 * m * k + j.val - (k + k + r * k + r * k + m * k + m * k) = j.val by omega]
    rw [List.getD_eq_getElem _ _ (by simp [hj])]
    simp
  · simp only [mainPos, mkMain, Sum.elim_inr, Sum.elim_inl]
    have hi := i.isLt
    rw [List.getD_append _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]
    rw [show 2 * k + 2 * r * k + 2 * m * k + m + i.val - (k + k + r * k + r * k + m * k + m * k + m) = i.val by omega]
    exact bitsN_getD (k + 1) t.val i.val hi
  · simp only [mainPos, mkMain, Sum.elim_inr]
    have hi := i.isLt
    rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]; omega)]
    simp only [List.length_append, bitsN_len, schedN_len, bankN_len, List.length_ofFn]
    rw [show 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) + i.val - (k + k + r * k + r * k + m * k + m * k + m + (k + 1)) = i.val by omega]
    exact bitsN_getD (k + 1) mode.val i.val hi

theorem testBit_eq_zero_iff {n a : ℕ} (ha : a < 2 ^ n) :
    (∀ i : Fin n, a.testBit i.val = false) ↔ a = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < n
    · exact h ⟨i, hi⟩
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)))
  · rintro rfl i; exact Nat.zero_testBit _

theorem testBit_eq_iff {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    (∀ i : Fin n, a.testBit i.val = b.testBit i.val) ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < n
    · exact h ⟨i, hi⟩
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)))]
  · rintro rfl i; rfl

theorem t_le_two_pow_iff {k : ℕ} (t : Fin (2 ^ (k + 1))) :
    (!t.val.testBit k || decide (∀ i : Fin k, (!t.val.testBit i.val) = true)) =
      decide (t.val ≤ 2 ^ k) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  have htop : t.val.testBit k = decide (2 ^ k ≤ t.val) := by
    have h := nat_testBit_top (W := k + 1) (by omega) t.isLt
    simpa using h
  rw [htop]
  by_cases hlt : t.val < 2 ^ k
  · have hge : ¬ (2 ^ k ≤ t.val) := by omega
    simp [hge, le_of_lt hlt]
  · have hge : 2 ^ k ≤ t.val := by omega
    simp only [hge, decide_true, Bool.true_eq_false, false_or]
    constructor
    · intro hall
      have heq : t.val = 2 ^ k := by
        apply Nat.eq_of_testBit_eq
        intro i
        by_cases hi : i < k
        · rw [hall ⟨i, hi⟩, Nat.testBit_two_pow]
          simp [ne_of_gt hi]
        · by_cases hik : i = k
          · subst hik; rw [htop, decide_eq_true hge, Nat.testBit_two_pow]; simp
          · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le t.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))),
              Nat.testBit_two_pow]
            simp [Ne.symm hik]
      omega
    · intro hle i
      have heq : t.val = 2 ^ k := by omega
      rw [heq, Nat.testBit_two_pow]
      simp [ne_of_gt i.isLt]

def outM0 {k r : ℕ} (w : MainIn k r 0 → Bool) : Bool :=
  decide (∀ i : Fin (k + 1), (!w (Sum.inr (Sum.inr (Sum.inr i)))) = true) &&
    (!w (Sum.inr (Sum.inr (Sum.inl (Fin.last k)))) ||
      decide (∀ i : Fin k, (!w (Sum.inr (Sum.inr (Sum.inl i.castSucc)))) = true))

theorem cmp_outM0 (k r : ℕ) : Cb (MainIn k r 0) (4 * k + 12) (outM0 (k := k) (r := r)) := by
  have hm0 := Cb.bigAnd (ι := MainIn k r 0) (I := Fin (k + 1)) (s := 1)
    (fun i => Cb.not (Cb.var (ι := MainIn k r 0) (Sum.inr (Sum.inr (Sum.inr i)))))
  have ht0 := Cb.bigAnd (ι := MainIn k r 0) (I := Fin k) (s := 1)
    (fun i => Cb.not (Cb.var (ι := MainIn k r 0) (Sum.inr (Sum.inr (Sum.inl i.castSucc)))))
  simp only [Fintype.card_fin] at hm0 ht0
  have h := Cb.and hm0 (Cb.or (Cb.not (Cb.var (ι := MainIn k r 0) (Sum.inr (Sum.inr (Sum.inl (Fin.last k)))))) ht0)
  exact Cb.mono (Cb.congr h (fun w => Bool.eq_iff_iff.2 (by unfold outM0; simp))) (by omega)

noncomputable def outBrute (k r m : ℕ) (w : MainIn k r m → Bool) : Bool :=
  let modeZero := decide (∀ i : Fin (k + 1), (!w (Sum.inr (Sum.inr (Sum.inr i)))) = true)
  let W := k + 3
  let hitsBV : BitVec W := ((Finset.univ : Finset (Fin (2 ^ k))).toList.map (fun x =>
    if decide (∀ j : Fin m, (evalF (Sum.elim (fun i : Fin k => x.val.testBit i.val) (fun p => w (Sum.inl p))) j ==
      w (Sum.inr (Sum.inl j))) = true) then BitVec.ofNat W 1 else 0)).sum
  let tBV : BitVec W := bv (fun i : Fin W =>
    if hi : i.val < k + 1 then w (Sum.inr (Sum.inr (Sum.inl ⟨i.val, hi⟩))) else false)
  if modeZero then !(hitsBV - tBV).getLsbD (W - 1) else true

theorem cmp_outBrute (k r m : ℕ) :
    Cb (MainIn k r m) (2 ^ k * (512 * (k + r + m + 6) ^ 2) + 128 * (k + r + m + 6))
      (outBrute k r m) := by
  set N := k + r + m + 6
  set W := k + 3
  have hkN : k + 1 ≤ N := by omega
  have hmN : m + 1 ≤ N := by omega
  have hrN : r + 1 ≤ N := by omega
  have h6N : 6 ≤ N := by omega
  have hterm : ∀ x : Fin (2 ^ k), Cw (MainIn k r m) W (256 * N ^ 2)
      (fun w => if decide (∀ j : Fin m, (evalF (Sum.elim (fun i : Fin k => x.val.testBit i.val)
          (fun p => w (Sum.inl p))) j == w (Sum.inr (Sum.inl j))) = true)
        then BitVec.ofNat W 1 else 0) := by
    intro x
    have hx : Cmp (MainIn k r m) (Fin k) (k * 1) (fun _ i => x.val.testBit i.val) := by
      have h := Cmp.ofBits (ι := MainIn k r m) (κ := Fin k) (s := 1) (fun i => Cb.const (x.val.testBit i.val))
      rw [Fintype.card_fin] at h; exact h
    have hEv := Cmp.comp (Cmp.pair hx (Cmp.wire (ι := MainIn k r m) (fun p : ParamsIn k r m => Sum.inl p)))
      (cmp_evalF k r m)
    have hEq : Cb (MainIn k r m ⊕ Fin m) (m * 6 + 1)
        (fun u => decide (∀ j : Fin m, (u (Sum.inr j) == u (Sum.inl (Sum.inr (Sum.inl j)))) = true)) := by
      have h := Cb.bigAnd (ι := MainIn k r m ⊕ Fin m) (I := Fin m) (s := 5) (fun j =>
        Cb.beq (Cb.var (ι := MainIn k r m ⊕ Fin m) (Sum.inr j))
          (Cb.var (ι := MainIn k r m ⊕ Fin m) (Sum.inl (Sum.inr (Sum.inl j)))))
      rw [Fintype.card_fin] at h
      exact Cb.mono (Cb.congr h (fun u => Bool.eq_iff_iff.2 (by simp))) (by omega)
    have hhit := Cmp.thn hEv hEq
    have hmux := Cw.mux hhit (Cw.const (ι := MainIn k r m) (BitVec.ofNat W 1))
      (Cw.const (ι := MainIn k r m) (0 : BitVec W))
    refine Cw.mono (Cw.congr hmux ?_) ?_
    · intro w; simp only [Sum.elim_inl, Sum.elim_inr]; rfl
    · have e1 : k * 1 + (128 * k * (r + 1) + m * (10 * k + 6)) + (m * 6 + 1) + W + W + 4 * W ≤ 256 * N ^ 2 := by
        have : k ≤ N := by omega
        have : m ≤ N := by omega
        have : r + 1 ≤ N := by omega
        have : W ≤ N := by omega
        have : N ^ 2 = N * N := by ring
        nlinarith
      omega
  have hsum := Cw.lsum _ hterm (Finset.univ : Finset (Fin (2 ^ k))).toList
  rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin] at hsum
  have htBV : Cw (MainIn k r m) W W
      (fun w => bv (fun i : Fin W => if hi : i.val < k + 1 then w (Sum.inr (Sum.inr (Sum.inl ⟨i.val, hi⟩))) else false)) := by
    have h := Cw.ofBits (ι := MainIn k r m) (W := W) (s := 1)
      (φ := fun w => bv (fun i : Fin W => if hi : i.val < k + 1 then w (Sum.inr (Sum.inr (Sum.inl ⟨i.val, hi⟩))) else false))
      (fun i => by
        by_cases hi : i.val < k + 1
        · exact Cb.mono (Cb.congr (Cb.var (ι := MainIn k r m) (Sum.inr (Sum.inr (Sum.inl ⟨i.val, hi⟩))))
            (fun w => by rw [getLsbD_bv, dite_eq_left hi])) (by omega)
        · exact Cb.congr (Cb.const false) (fun w => by rw [getLsbD_bv, dite_eq_right hi]))
    simpa using h
  have hsub := Cw.sub hsum htBV
  have hmsb := Cb.comp hsub (Cb.var (ι := Fin W) ⟨W - 1, by omega⟩)
  have hm0 : Cb (MainIn k r m) ((k + 1) * 2 + 1)
      (fun w => decide (∀ i : Fin (k + 1), (!w (Sum.inr (Sum.inr (Sum.inr i)))) = true)) := by
    have h := Cb.bigAnd (ι := MainIn k r m) (I := Fin (k + 1)) (s := 1)
      (fun i => Cb.not (Cb.var (ι := MainIn k r m) (Sum.inr (Sum.inr (Sum.inr i)))))
    rw [Fintype.card_fin] at h
    exact Cb.mono (Cb.congr h (fun w => Bool.eq_iff_iff.2 (by simp))) (by omega)
  have hfin := Cb.mux hm0 (Cb.not hmsb) (Cb.const true)
  refine Cb.mono (Cb.congr hfin (fun w => by unfold outBrute; rfl)) ?_
  have e1 : 2 ^ k * (256 * N ^ 2 + 20 * (W + 1)) + W ≤ 2 ^ k * (512 * N ^ 2) := by
    have : 20 * (W + 1) + W ≤ 256 * N ^ 2 := by
      have : W ≤ N := by omega
      have : N ^ 2 = N * N := by ring
      nlinarith
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    nlinarith
  omega

theorem outBrute_spec {k r m : ℕ} (u v0 : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (R B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) (mode : Fin (k + 1)) :
    let hits := Nat.card {w : Fin (2 ^ k) // (fun j => xor (parityN k (R j).val (stateN k r false w.val u.val cr))
      (parityN k (B j).val (stateN k r true w.val v0.val cc))) = y}
    outBrute k r m (mkMain u v0 cr cc R B y t mode) =
      if mode.val = 0 then decide (t.val ≤ hits) else true := by
  intro hits
  unfold outBrute
  have hm0 : decide (∀ i : Fin (k + 1), (!mkMain u v0 cr cc R B y t mode (Sum.inr (Sum.inr (Sum.inr i)))) = true) =
      decide (mode.val = 0) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    simp only [mkMain, Sum.elim_inr, Bool.not_eq_true']
    have hlt : mode.val < 2 ^ (k + 1) := lt_trans mode.isLt Nat.lt_two_pow_self
    exact testBit_eq_zero_iff hlt
  rw [hm0]
  by_cases hmode : mode.val = 0
  · simp only [hmode, decide_true, ite_true]
    set W := k + 3
    have hterm : ∀ x : Fin (2 ^ k),
        (if decide (∀ j : Fin m, (evalF (Sum.elim (fun i : Fin k => x.val.testBit i.val)
            (fun p => mkMain u v0 cr cc R B y t mode (Sum.inl p))) j ==
            mkMain u v0 cr cc R B y t mode (Sum.inr (Sum.inl j))) = true)
          then BitVec.ofNat W 1 else 0) =
        BitVec.ofInt W (if (fun j => xor (parityN k (R j).val (stateN k r false x.val u.val cr))
          (parityN k (B j).val (stateN k r true x.val v0.val cc))) = y then (1 : ℤ) else 0) := by
      intro x
      have hiff : (∀ j : Fin m, (evalF (Sum.elim (fun i : Fin k => x.val.testBit i.val)
            (fun p => mkMain u v0 cr cc R B y t mode (Sum.inl p))) j ==
            mkMain u v0 cr cc R B y t mode (Sum.inr (Sum.inl j))) = true) ↔
          (fun j => xor (parityN k (R j).val (stateN k r false x.val u.val cr))
            (parityN k (B j).val (stateN k r true x.val v0.val cc))) = y := by
        rw [funext_iff]
        apply forall_congr'; intro j
        simp only [mkMain, Sum.elim_inl, Sum.elim_inr, beq_iff_eq]
        have hev : evalF (Sum.elim (fun i : Fin k => x.val.testBit i.val)
            (fun p => mkParams u v0 cr cc R B p)) j =
            xor (parityN k (R j).val (stateN k r false x.val u.val cr))
              (parityN k (B j).val (stateN k r true x.val v0.val cc)) := evalF_eq u v0 cr cc R B x j
        rw [hev]
      by_cases hf : (fun j => xor (parityN k (R j).val (stateN k r false x.val u.val cr))
          (parityN k (B j).val (stateN k r true x.val v0.val cc))) = y
      · rw [ite_eq_left (decide_eq_true (hiff.2 hf)), ite_eq_left hf]; rfl
      · rw [ite_eq_right (fun h => hf (hiff.1 (decide_eq_true_iff.1 h))), ite_eq_right hf]; rfl
    have hsum_bv : ∀ (L : List (Fin (2 ^ k))) (f : Fin (2 ^ k) → ℤ),
        (L.map (fun x => BitVec.ofInt W (f x))).sum = BitVec.ofInt W ((L.map f).sum) := by
      intro L f
      induction L with
      | nil => rfl
      | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, BitVec.ofInt_add]
    have hhits_bv : ((Finset.univ : Finset (Fin (2 ^ k))).toList.map (fun x =>
        if decide (∀ j : Fin m, (evalF (Sum.elim (fun i : Fin k => x.val.testBit i.val)
            (fun p => mkMain u v0 cr cc R B y t mode (Sum.inl p))) j ==
            mkMain u v0 cr cc R B y t mode (Sum.inr (Sum.inl j))) = true)
          then BitVec.ofNat W 1 else 0)).sum = BitVec.ofInt W (hits : ℤ) := by
      have hm := List.map_congr_left (l := (Finset.univ : Finset (Fin (2 ^ k))).toList)
        (fun x _ => hterm x)
      rw [hm, hsum_bv]
      congr 1
      have hlist : ((Finset.univ : Finset (Fin (2 ^ k))).toList.map (fun x =>
          if (fun j => xor (parityN k (R j).val (stateN k r false x.val u.val cr))
            (parityN k (B j).val (stateN k r true x.val v0.val cc))) = y then (1 : ℤ) else 0)).sum =
          ∑ x : Fin (2 ^ k), (if (fun j => xor (parityN k (R j).val (stateN k r false x.val u.val cr))
            (parityN k (B j).val (stateN k r true x.val v0.val cc))) = y then (1 : ℤ) else 0) := by
        rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl
      rw [hlist, Finset.sum_boole]
      dsimp only [hits]
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have htBV : bv (fun i : Fin W =>
        if hi : i.val < k + 1 then mkMain u v0 cr cc R B y t mode (Sum.inr (Sum.inr (Sum.inl ⟨i.val, hi⟩)))
        else false) = BitVec.ofInt W (t.val : ℤ) := by
      rw [BitVec.ofInt_natCast]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [getLsbD_bv _ ⟨i, hi⟩, BitVec.getLsbD_ofNat]
      simp only [hi, decide_true, Bool.true_and]
      by_cases hi1 : i < k + 1
      · rw [dite_eq_left hi1]; rfl
      · rw [dite_eq_right hi1]; symm
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le t.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hhits_bv, htBV, ofInt_sub_eq]
    have hhits_le : hits ≤ 2 ^ k := by
      dsimp only [hits]
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      calc (Finset.univ.filter _).card ≤ (Finset.univ : Finset (Fin (2 ^ k))).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2 ^ k := by simp
    have h1 : (hits : ℤ) < (2 : ℤ) ^ (W - 1) := by
      have : (hits : ℤ) ≤ (2 : ℤ) ^ k := by exact_mod_cast hhits_le
      have : (2 : ℤ) ^ k < (2 : ℤ) ^ (W - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      omega
    have h2 : (t.val : ℤ) < (2 : ℤ) ^ (W - 1) := by
      have : (t.val : ℤ) < (2 : ℤ) ^ (k + 1) := by exact_mod_cast t.isLt
      have : (2 : ℤ) ^ (k + 1) ≤ (2 : ℤ) ^ (W - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    rw [ofInt_msb_iff (by omega) _ (by omega) (by omega)]
    rw [Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, not_lt]
    omega
  · simp [hmode]

noncomputable def outMain (k r m b h' : ℕ) (w : MainIn k r m → Bool) : Bool :=
  let vRB : RBIn k m → Bool := Sum.elim
    (fun p => w (Sum.inl (Sum.inr (Sum.inr (Sum.inl p)))))
    (fun p => w (Sum.inl (Sum.inr (Sum.inr (Sum.inr p)))))
  let p1 := phase1Out k r m b h' vRB
  let modeZero := decide (∀ q : Fin (k + 1), (!w (Sum.inr (Sum.inr (Sum.inr q)))) = true)
  let p2 := phase2Out k r m b (Sum.elim (fun x => w (Sum.inl x))
    (Sum.elim (fun j => w (Sum.inr (Sum.inl j)))
      (Sum.elim (fun i => w (Sum.inr (Sum.inr (Sum.inl i)))) p1)))
  let modePos := decide (∃ i : Fin k, (p1 (Sum.inr (Sum.inl i)) &&
    decide (∀ q : Fin (k + 1), (w (Sum.inr (Sum.inr (Sum.inr q))) == (i.val + 1).testBit q.val) = true)) = true)
  if modeZero then p2 else modePos

theorem cmp_outMain (k r m b h' : ℕ) (hbk : b < k) (hhm : h' ≤ m) :
    Cb (MainIn k r m)
      (((2 * k + 1) ^ h' + 2 ^ b) * (8192 * (k + r + m + 6) ^ 5))
      (outMain k r m b h') := by
  set N := k + r + m + 6
  have hkN : k + 1 ≤ N := by omega
  have hmN : m + 1 ≤ N := by omega
  have h6N : 6 ≤ N := by omega
  have hp1 : Cmp (MainIn k r m) (P1Out k m) ((2 * k + 1) ^ h' * (4096 * N ^ 5) + (k + m + 1) ^ 2)
      (fun w => phase1Out k r m b h' (Sum.elim
        (fun p => w (Sum.inl (Sum.inr (Sum.inr (Sum.inl p)))))
        (fun p => w (Sum.inl (Sum.inr (Sum.inr (Sum.inr p))))))) :=
    Cmp.congr (Cmp.sel (Sum.elim (fun p => Sum.inl (Sum.inr (Sum.inr (Sum.inl p))))
      (fun p => Sum.inl (Sum.inr (Sum.inr (Sum.inr p))))) (cmp_phase1 k r m b h' hhm))
      (fun w o => by congr 1; funext x; rcases x with p | p <;> rfl)
  let St := MainIn k r m ⊕ P1Out k m
  have hp2 : Cb St (2 ^ b * (4096 * N ^ 5) + 1024 * N ^ 3)
      (fun u => phase2Out k r m b (Sum.elim (fun x => u (Sum.inl (Sum.inl x)))
        (Sum.elim (fun j => u (Sum.inl (Sum.inr (Sum.inl j))))
          (Sum.elim (fun i => u (Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))))
            (fun o => u (Sum.inr o)))))) :=
    Cb.congr (Cmp.sel (Sum.elim (fun x => Sum.inl (Sum.inl x))
      (Sum.elim (fun j => Sum.inl (Sum.inr (Sum.inl j)))
        (Sum.elim (fun i => Sum.inl (Sum.inr (Sum.inr (Sum.inl i)))) Sum.inr)))
      (cmp_phase2 k r m b hbk))
      (fun u => by congr 1; funext x; rcases x with x | j | i | o <;> rfl)
  have hm0 : Cb St ((k + 1) * 2 + 1)
      (fun u => decide (∀ q : Fin (k + 1), (!u (Sum.inl (Sum.inr (Sum.inr (Sum.inr q))))) = true)) := by
    have h := Cb.bigAnd (ι := St) (I := Fin (k + 1)) (s := 1)
      (fun q => Cb.not (Cb.var (ι := St) (Sum.inl (Sum.inr (Sum.inr (Sum.inr q))))))
    rw [Fintype.card_fin] at h
    exact Cb.mono (Cb.congr h (fun u => Bool.eq_iff_iff.2 (by simp))) (by ring_nf; omega)
  have hmp : Cb St (k * ((k + 1) * 7 + 4) + 1)
      (fun u => decide (∃ i : Fin k, (u (Sum.inr (Sum.inr (Sum.inl i))) &&
        decide (∀ q : Fin (k + 1), (u (Sum.inl (Sum.inr (Sum.inr (Sum.inr q)))) ==
          (i.val + 1).testBit q.val) = true)) = true)) := by
    have h := Cb.bigOr (ι := St) (I := Fin k) (s := (k + 1) * 7 + 3)
      (φ := fun i u => u (Sum.inr (Sum.inr (Sum.inl i))) &&
        decide (∀ q : Fin (k + 1), (u (Sum.inl (Sum.inr (Sum.inr (Sum.inr q)))) ==
          (i.val + 1).testBit q.val) = true)) (fun i => by
      have heq := Cb.bigAnd (ι := St) (I := Fin (k + 1)) (s := 6) (fun q =>
        Cb.beq (Cb.var (ι := St) (Sum.inl (Sum.inr (Sum.inr (Sum.inr q)))))
          (Cb.const (ι := St) ((i.val + 1).testBit q.val)))
      rw [Fintype.card_fin] at heq
      exact Cb.mono (Cb.congr (Cb.and (Cb.var (ι := St) (Sum.inr (Sum.inr (Sum.inl i)))) heq)
        (fun u => Bool.eq_iff_iff.2 (by simp))) (by omega))
    rw [Fintype.card_fin] at h
    exact Cb.mono (Cb.congr h (fun u => Bool.eq_iff_iff.2 (by simp))) (by ring_nf; omega)
  have htot := Cmp.thn hp1 (Cb.mux hm0 hp2 hmp)
  refine Cb.mono (Cb.congr htot (fun w => by unfold outMain; rfl)) ?_
  have h1 : (k + m + 1) ^ 2 + 1024 * N ^ 3 + ((k + 1) * 2 + 1) + (k * ((k + 1) * 7 + 4) + 1) + 4 ≤
      4096 * N ^ 5 := by
    have e1 : (k + m + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have e2 : k * ((k + 1) * 7 + 4) ≤ N * (N * 7 + 4) := by gcongr <;> omega
    have e3 : N * (N * 7 + 4) = 7 * N ^ 2 + 4 * N := by ring
    have p3 : N ^ 3 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p2 : N ^ 2 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p1 : N ≤ N ^ 5 := by
      calc N = N ^ 1 := by ring
        _ ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have hpA : 1 ≤ (2 * k + 1) ^ h' := Nat.one_le_pow _ _ (by omega)
  have hpB : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hmul_eq : ((2 * k + 1) ^ h' + 2 ^ b) * (8192 * N ^ 5) =
      (2 * k + 1) ^ h' * (4096 * N ^ 5) + 2 ^ b * (4096 * N ^ 5) +
      ((2 * k + 1) ^ h' + 2 ^ b) * (4096 * N ^ 5) := by ring
  rw [hmul_eq]
  have hge : 4096 * N ^ 5 ≤ ((2 * k + 1) ^ h' + 2 ^ b) * (4096 * N ^ 5) := by
    calc 4096 * N ^ 5 = 1 * (4096 * N ^ 5) := by ring
      _ ≤ ((2 * k + 1) ^ h' + 2 ^ b) * (4096 * N ^ 5) := Nat.mul_le_mul_right _ (by omega)
  omega

theorem size_bound_final (k r m b h : ℕ) (S : ℕ)
    (hS : S ≤ ((2 * k + 1) ^ (min h (min b (min m (2 * k)))) + 2 ^ (min b k)) * (8192 * (k + r + m + 6) ^ 5)) :
    S + 1 ≤ 2 ^ 45 * (k + r + m + 6) ^ 18 *
      ((2 * k + 1) ^ (min h (min b (min m (2 * k)))) + 2 ^ (min b k)) := by
  set N := k + r + m + 6
  set T := (2 * k + 1) ^ (min h (min b (min m (2 * k)))) + 2 ^ (min b k)
  have hT : 1 ≤ T := by
    have : 1 ≤ 2 ^ (min b k) := Nat.one_le_two_pow
    omega
  have hN : 1 ≤ N := by omega
  have p5 : N ^ 5 ≤ N ^ 18 := Nat.pow_le_pow_right hN (by norm_num)
  have p0 : 1 ≤ N ^ 18 := Nat.one_le_pow _ _ hN
  have e : 8192 * N ^ 5 + 1 ≤ 2 ^ 45 * N ^ 18 := by
    have : 8192 + 1 ≤ 2 ^ 45 := by norm_num
    nlinarith
  calc S + 1 ≤ T * (8192 * N ^ 5) + T := by omega
    _ = T * (8192 * N ^ 5 + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ T * (2 ^ 45 * N ^ 18) := Nat.mul_le_mul_left _ e
    _ = 2 ^ 45 * N ^ 18 * T := Nat.mul_comm _ _

end PEqualNP.Outside.L_meta_33596_aux

theorem PEqualNP.Outside.L_meta_33596 : (∀ (k r m b h : Nat), 0 < k → 4 ≤ r →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w u : Nat) (c : Fin r → Fin (2^k)) =>
    let g := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot g x ^^^ rot (k-g) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
      (rot (if col then 3 else 1) w ^^^ u)
  let parity := fun (mask x : Nat) =>
    (List.range k).foldl (fun b i => xor b (mask.testBit i && x.testBit i)) false
  let bits := fun (n x : Nat) => (List.range n).map (fun i => x.testBit i)
  let bank := fun (A : Fin m → Fin (2^k)) =>
    (List.finRange m).flatMap (fun j => bits k (A j).val)
  let sched := fun (c : Fin r → Fin (2^k)) =>
    (List.finRange r).flatMap (fun j => bits k (c j).val)
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3

  let F := ZMod 2
  let I := Fin k
  let A := Bool × I
  let Y := Fin m → F
  let scope := fun a : A => (Finset.univ : Finset I).filter (fun i =>
    ∃ d : Fin (reach a.1+1), (a.2.val+d.val)%k = i.val)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*k+2*r*k+2*m*k+m+2*(k+1)) C ∧
    C.size ≤ 2^45*(k+r+m+6)^18 *
      ((2*k+1)^(min h (min b (min m (2*k)))) + 2^(min b k)) ∧
    ∀ (R B : Fin m → Fin (2^k)),
      let col := fun (a : A) (j : Fin m) => if
        ((if a.1 then B j else R j).val.testBit ((a.2.val+delay a.1)%k)) then (1 : F) else 0

      let active := (Finset.univ : Finset A).filter (fun a => col a ≠ 0)
      let left := fun (P : Finset I) (a : A) => scope a \ P
      let good := fun (P : Finset I) => ∀ a ∈ active, (left P a).card ≤ 2
      let pairs := fun (P : Finset I) => (active.image (left P)).filter (fun e => e.card = 2)
      let rank := fun (V : Finset Y) => Module.finrank F (Submodule.span F (V : Set Y))
      let worst := fun (P : Finset I) =>
        (Finset.univ : Finset (A → F)).sup (fun w =>
          rank ((pairs P).image (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a)))

      let works := fun (P : Finset I) => good P ∧ worst P ≤ h ∧ P.card + worst P ≤ b
      let pass := ∃ P : Finset I, works P
      ∃ P : Finset I, (pass → works P) ∧ (¬pass → P = ∅) ∧
        ∀ (u v : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (y : Fin m → Bool)
          (t : Fin (2^(k+1))) (mode : Fin (k+1)),
          let f := fun (w : Fin (2^k)) (j : Fin m) =>
            xor (parity (R j).val (state false w.val u.val cr))
              (parity (B j).val (state true w.val v.val cc))
          let hits := Nat.card {w : Fin (2^k) // f w = y}
          C.eval (bits k u.val ++ bits k v.val ++ sched cr ++ sched cc ++ bank R ++ bank B ++
            List.ofFn y ++ bits (k+1) t.val ++ bits (k+1) mode.val) =
            if mode.val = 0 then decide (pass ∧ t.val ≤ hits)
            else decide (∃ i ∈ P, i.val+1 = mode.val)) := by
  intro k r m b h hk hr
  open PEqualNP.Outside.L_meta_33596_aux in
  by_cases hm0 : m = 0
  · subst hm0
    obtain ⟨gs, outs, hg, hrb, hlen, -, hev⟩ :=
      Cmp.extract (cmp_outM0 k r)
        (2 * k + 2 * r * k + 2 * 0 * k + 0 + 2 * (k + 1)) (mainPos k r 0)
        (fun x => Nat.lt_succ_of_lt (mainPos_lt k r 0 x))
    refine ⟨⟨gs, outs ()⟩, hg, hrb (outs ()), ?_, ?_⟩
    · refine le_trans hlen (size_bound_final k r 0 b h (4 * k + 12) ?_)
      set N := k + r + 0 + 6
      have hT : 1 ≤ (2 * k + 1) ^ (min h (min b (min 0 (2 * k)))) + 2 ^ (min b k) := by
        have := Nat.one_le_two_pow (n := min b k); omega
      have hN : 4 * k + 12 ≤ 8192 * N ^ 5 := by
        have h1 : N ≤ N ^ 5 := by
          calc N = N ^ 1 := by ring
            _ ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
        omega
      nlinarith
    · intro R B
      dsimp only
      have hactE : activeN r R B = ∅ := by
        ext a; simp only [activeN, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_not]; funext j; exact Fin.elim0 j
      have hworst0 : worstN r R B ∅ = 0 := by
        unfold worstN pairsN
        rw [hactE]
        apply Nat.eq_zero_of_le_zero
        apply Finset.sup_le
        intro w _
        exact le_trans (finrank_span_le_card _) (Nat.le_of_eq (Finset.card_eq_zero.2 (by ext x; simp)))
      have hworks0 : worksN r b h R B ∅ := by
        refine ⟨?_, ?_, ?_⟩
        · intro a ha; rw [hactE] at ha; exact absurd ha (Finset.notMem_empty a)
        · rw [hworst0]; omega
        · rw [hworst0]; simp
      have hpass : ∃ P : Finset (Fin k), worksN r b h R B P := ⟨∅, hworks0⟩
      refine ⟨∅, fun _ => hworks0, fun _ => rfl, ?_⟩
      intro u v cr cc y t mode
      have hin := mainInput_len u v cr cc R B y t mode
      have he := hev (outs ()) (mainInput u v cr cc R B y t mode) hin ()
      show ((⟨gs, outs ()⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
        (mainInput u v cr cc R B y t mode)).getD (outs ()) false = _
      rw [he]
      have hmain_eq : (fun j => (mainInput u v cr cc R B y t mode ++ [false]).getD (mainPos k r 0 j) false) =
          mkMain u v cr cc R B y t mode := funext (mainInput_getD u v cr cc R B y t mode)
      rw [hmain_eq]
      unfold outM0
      have hm0_eq : decide (∀ i : Fin (k + 1), (!mkMain u v cr cc R B y t mode (Sum.inr (Sum.inr (Sum.inr i)))) = true) =
          decide (mode.val = 0) := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
        simp only [mkMain, Sum.elim_inr, Bool.not_eq_true']
        exact testBit_eq_zero_iff (lt_trans mode.isLt Nat.lt_two_pow_self)
      rw [hm0_eq]
      by_cases hmode : mode.val = 0
      · simp only [hmode, decide_true, Bool.true_and, ite_true]
        have hhits : ∀ f0 : Fin (2 ^ k) → Fin 0 → Bool, Nat.card {w : Fin (2 ^ k) // f0 w = y} = 2 ^ k := by
          intro f0
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          have : Finset.univ.filter (fun w : Fin (2 ^ k) => f0 w = y) = Finset.univ := by
            ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
            funext j; exact Fin.elim0 j
          rw [this, Finset.card_univ, Fintype.card_fin]
        have ht_eq : (!mkMain u v cr cc R B y t mode (Sum.inr (Sum.inr (Sum.inl (Fin.last k)))) ||
            decide (∀ i : Fin k, (!mkMain u v cr cc R B y t mode (Sum.inr (Sum.inr (Sum.inl i.castSucc)))) = true)) =
            decide (t.val ≤ 2 ^ k) := t_le_two_pow_iff t
        rw [ht_eq, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hhits]
        exact ⟨fun ht => ⟨hpass, ht⟩, fun h => h.2⟩
      · simp [hmode]
  · by_cases hbk : b < k
    · set h' := min h (min b (min m (2 * k)))
      have hhm : h' ≤ m := le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))
      obtain ⟨gs, outs, hg, hrb, hlen, -, hev⟩ :=
        Cmp.extract (cmp_outMain k r m b h' hbk hhm)
          (2 * k + 2 * r * k + 2 * m * k + m + 2 * (k + 1)) (mainPos k r m)
          (fun x => Nat.lt_succ_of_lt (mainPos_lt k r m x))
      refine ⟨⟨gs, outs ()⟩, hg, hrb (outs ()), ?_, ?_⟩
      · refine le_trans hlen (size_bound_final k r m b h _ ?_)
        have hmin : min b k = b := Nat.min_eq_left (le_of_lt hbk)
        rw [hmin]
      · intro R B
        let vRB : RBIn k m → Bool := Sum.elim (fun p => (R p.1).val.testBit p.2.val)
          (fun p => (B p.1).val.testBit p.2.val)
        let p1 := phase1Out k r m b h' vRB
        let P := Finset.univ.filter (fun i : Fin k => p1 (Sum.inr (Sum.inl i)) = true)
        have hp1 := phase1_spec (r := r) (b := b) (h := h) hk R B
        refine ⟨P, fun hp => (hp1.2.2 (hp1.1.2 hp)).2.2.2.2, fun hnp => hp1.2.1 (by
          by_contra hc; exact hnp (hp1.1.1 (by simpa using hc))), ?_⟩
        intro u v cr cc y t mode
        have hin := mainInput_len u v cr cc R B y t mode
        have he := hev (outs ()) (mainInput u v cr cc R B y t mode) hin ()
        show ((⟨gs, outs ()⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
          (mainInput u v cr cc R B y t mode)).getD (outs ()) false = _
        rw [he]
        have hmain_eq : (fun j => (mainInput u v cr cc R B y t mode ++ [false]).getD (mainPos k r m j) false) =
            mkMain u v cr cc R B y t mode := funext (mainInput_getD u v cr cc R B y t mode)
        rw [hmain_eq]
        unfold outMain
        have hvRB_eq : (Sum.elim (fun p => mkMain u v cr cc R B y t mode (Sum.inl (Sum.inr (Sum.inr (Sum.inl p)))))
            (fun p => mkMain u v cr cc R B y t mode (Sum.inl (Sum.inr (Sum.inr (Sum.inr p)))))) = vRB := by
          funext x; rcases x with p | p <;> rfl
        rw [hvRB_eq]
        have hm0_eq : decide (∀ q : Fin (k + 1), (!mkMain u v cr cc R B y t mode (Sum.inr (Sum.inr (Sum.inr q)))) = true) =
            decide (mode.val = 0) := by
          rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
          simp only [mkMain, Sum.elim_inr, Bool.not_eq_true']
          exact testBit_eq_zero_iff (lt_trans mode.isLt Nat.lt_two_pow_self)
        rw [hm0_eq]
        by_cases hmode : mode.val = 0
        · simp only [hmode, decide_true, ite_true]
          have hp2 := phase2Out_spec hk hr u v cr cc R B y t p1 (fun ht =>
            let h := hp1.2.2 ht; ⟨h.1, h.2.2.1, h.2.2.2.1⟩)
          have hvin : (Sum.elim (fun x => mkMain u v cr cc R B y t mode (Sum.inl x))
              (Sum.elim (fun j => mkMain u v cr cc R B y t mode (Sum.inr (Sum.inl j)))
                (Sum.elim (fun i => mkMain u v cr cc R B y t mode (Sum.inr (Sum.inr (Sum.inl i)))) p1))) =
              Sum.elim (mkParams u v cr cc R B)
                (Sum.elim y (Sum.elim (fun i : Fin (k + 1) => t.val.testBit i.val) p1)) := by
            funext x; rcases x with x | j | i | o <;> rfl
          rw [hvin, hp2]
          rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
          exact and_congr hp1.1 Iff.rfl
        · simp only [hmode, decide_false, Bool.false_eq_true, ite_false]
          rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
          simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
            decide_eq_true_eq, mkMain, Sum.elim_inr, beq_iff_eq]
          apply exists_congr; intro i
          refine and_congr Iff.rfl ?_
          have h1 : mode.val < 2 ^ (k + 1) := lt_trans mode.isLt Nat.lt_two_pow_self
          have h2 : i.val + 1 < 2 ^ (k + 1) := lt_trans (by omega : i.val + 1 < k + 1) Nat.lt_two_pow_self
          rw [testBit_eq_iff h1 h2, eq_comm]
    · have hkb : k ≤ b := by omega
      obtain ⟨gs, outs, hg, hrb, hlen, -, hev⟩ :=
        Cmp.extract (cmp_outBrute k r m)
          (2 * k + 2 * r * k + 2 * m * k + m + 2 * (k + 1)) (mainPos k r m)
          (fun x => Nat.lt_succ_of_lt (mainPos_lt k r m x))
      refine ⟨⟨gs, outs ()⟩, hg, hrb (outs ()), ?_, ?_⟩
      · refine le_trans hlen (size_bound_final k r m b h _ ?_)
        have hmin : min b k = k := Nat.min_eq_right hkb
        rw [hmin]
        set N := k + r + m + 6
        have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have p2 : N ^ 2 ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have p1 : N ≤ N ^ 5 := by
          calc N = N ^ 1 := by ring
            _ ≤ N ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have hle : 2 ^ k * (512 * N ^ 2) + 128 * N ≤ 2 ^ k * (8192 * N ^ 5) := by nlinarith
        have hle2 : 2 ^ k * (8192 * N ^ 5) ≤
            ((2 * k + 1) ^ (min h (min b (min m (2 * k)))) + 2 ^ k) * (8192 * N ^ 5) :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
        omega
      · intro R B
        have hworksU : worksN r b h R B Finset.univ := by
          have hlE : ∀ a : Bool × Fin k, leftN r Finset.univ a = ∅ := fun a => by
            unfold leftN; exact Finset.sdiff_eq_empty_iff_subset.2 (Finset.subset_univ _)
          have hpE : pairsN r R B Finset.univ = ∅ := by
            ext e
            simp only [pairsN, Finset.mem_filter, Finset.mem_image, Finset.notMem_empty,
              iff_false, not_and]
            rintro ⟨a, _, rfl⟩
            rw [hlE]; simp
          have hworstU : worstN r R B Finset.univ = 0 := by
            unfold worstN; rw [hpE]
            apply Nat.eq_zero_of_le_zero
            apply Finset.sup_le
            intro w _
            exact le_trans (finrank_span_le_card _) (Nat.le_of_eq (Finset.card_eq_zero.2 (by ext x; rw [Set.mem_toFinset]; simp)))
          refine ⟨fun a _ => by simp [hlE], ?_, ?_⟩
          · rw [hworstU]; omega
          · rw [hworstU]; simp [hkb]
        have hpass : ∃ P : Finset (Fin k), worksN r b h R B P := ⟨Finset.univ, hworksU⟩
        refine ⟨Finset.univ, fun _ => hworksU, fun hnp => absurd hpass hnp, ?_⟩
        intro u v cr cc y t mode
        have hin := mainInput_len u v cr cc R B y t mode
        have he := hev (outs ()) (mainInput u v cr cc R B y t mode) hin ()
        show ((⟨gs, outs ()⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
          (mainInput u v cr cc R B y t mode)).getD (outs ()) false = _
        rw [he]
        have hmain_eq : (fun j => (mainInput u v cr cc R B y t mode ++ [false]).getD (mainPos k r m j) false) =
            mkMain u v cr cc R B y t mode := funext (mainInput_getD u v cr cc R B y t mode)
        rw [hmain_eq, outBrute_spec]
        by_cases hmode : mode.val = 0
        · simp only [hmode, ite_true]
          rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
          exact ⟨fun ht => ⟨hpass, ht⟩, fun h => h.2⟩
        · simp only [hmode, ite_false]
          symm; rw [decide_eq_true_iff]
          exact ⟨⟨mode.val - 1, by omega⟩, Finset.mem_univ _, by simp; omega⟩
