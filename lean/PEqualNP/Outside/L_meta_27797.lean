import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27797_aux

namespace Restriction
open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

def Const {Y : Type} (f : Y → Bool) : Prop := ∃ c, ∀ y, f y = c

def Drop {Y : Type} (n : ℕ) (F : ℕ → Y → Bool) (j : ℕ) : Prop :=
  Const (F (n + j)) ∨ ∃ w < n + j, ∀ y, F (n + j) y = F w y

def GateArity (g : Gate) : Prop :=
  (g.op = .not ∧ g.inputs.length = 1) ∨
    ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)

theorem GateArity.allowed {g : Gate} (h : GateArity g) :
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
  rcases h with ⟨h,hn⟩ | ⟨h,hn⟩
  · exact ⟨Or.inr (Or.inr h),by rw [hn]; decide⟩
  · exact ⟨h.elim Or.inl (fun e => Or.inr (Or.inl e)),by rw [hn]⟩

theorem restrict (n m : ℕ) (gs : List Gate) (F : ℕ → (Fin m → Bool) → Bool)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i < n, Const (F i) ∨ ∃ k < m, ∀ y, F i y = (List.ofFn y).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < gs.length) (y : Fin m → Bool), F (n + j) y =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then F i y else false)) :
    ∀ K ≤ gs.length, ∃ (ds : List Gate) (S : Finset ℕ),
      (∀ g ∈ ds, GateArity g) ∧
      (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
      (∀ j ∈ S, j < K ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
      ∀ w < n + K, Const (F w) ∨
        ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, by simp, fun w hw => ?_⟩
    simpa [run] using hin w (by omega)
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := ih (by omega)
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j := fun j hj =>
      ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
    by_cases hd : Drop n F K
    · refine ⟨ds, S, h1, hb, h2', h3, fun w hw => ?_⟩
      rcases Nat.lt_or_ge w (n + K) with h | h
      · exact h4 w h
      · rw [show w = n + K by omega]
        rcases hd with hc | ⟨u, hu, he⟩
        · exact Or.inl hc
        · rcases h4 u hu with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun y => (he y).trans (hc y)⟩
          · exact Or.inr ⟨k, hk, fun y => (he y).trans (hk' y)⟩
    · have hnc : ¬ Const (F (n + K)) := fun h => hd (Or.inl h)
      have hne : ∀ u < n + K, ¬ ∀ y, F (n + K) y = F u y := fun u hu h => hd (Or.inr ⟨u, hu, h⟩)
      have addg : ∀ g : Gate, GateArity g → (∀ i ∈ g.inputs, i < m + ds.length) →
          (∀ y, F (n + K) y = g.op.eval (g.inputs.map fun i =>
            (run ds (List.ofFn y)).getD i false)) →
          ∃ (ds : List Gate) (S : Finset ℕ),
            (∀ g ∈ ds, GateArity g) ∧
            (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
            (∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
            ∀ w < n + (K + 1), Const (F w) ∨
              ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
        intro g ho hgb hg
        have hKS : K ∉ S := fun h => by have := (h2 K h).1; omega
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.1 hg' with h | h
          · exact h1 g' h
          · rw [List.mem_singleton.1 h]; exact ho
        · intro j hj i hi
          rcases Nat.lt_or_ge j ds.length with h | h
          · rw [List.getElem_append_left h] at hi
            exact hb j h i hi
          · have hjj : j = ds.length := by simp at hj; omega
            subst hjj
            exact hgb i (by simpa using hi)
        · intro j hj
          rcases Finset.mem_insert.1 hj with rfl | h
          · exact ⟨by omega, hd⟩
          · exact h2' j h
        · rw [Finset.card_insert_of_notMem hKS]; simp; omega
        · intro w hw
          rcases Nat.lt_or_ge w (n + K) with h | h
          · rcases h4 w h with hc | ⟨k, hk, hk'⟩
            · exact Or.inl hc
            · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
              rw [run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_ofFn]; exact hk)]
              exact hk' y
          · refine Or.inr ⟨m + ds.length, by simp, fun y => ?_⟩
            have hl' : (run ds (List.ofFn y)).length = m + ds.length := by
              rw [run_length, List.length_ofFn]
            rw [show w = n + K by omega, run_snoc, ← hl', getD_at]
            exact hg y
      have hval : ∀ i, (∃ c, ∀ y, (if i < n + K then F i y else false) = c) ∨
          (i < n + K ∧ ∃ k < m + ds.length, ∀ y,
            F i y = (run ds (List.ofFn y)).getD k false) := by
        intro i
        by_cases hi : i < n + K
        · rcases h4 i hi with ⟨c, hc⟩ | h
          · exact Or.inl ⟨c, fun y => by rw [ite_eq_left hi]; exact hc y⟩
          · exact Or.inr ⟨hi, h⟩
        · exact Or.inl ⟨false, fun y => by rw [ite_eq_right hi]⟩
      have hj : K < gs.length := by omega
      have hFK := hF K hj
      obtain ⟨hop, hlen⟩ := hops _ (List.getElem_mem hj)
      generalize gs[K].inputs = I at *
      generalize gs[K].op = o at *
      match I, hlen with
      | [], _ =>
        refine absurd ⟨o.eval [], fun y => ?_⟩ hnc
        simpa using hFK y
      | [a], _ =>
        rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
        · refine absurd ⟨o.eval [c], fun y => ?_⟩ hnc
          rw [hFK y, List.map_singleton, hc y]
        · rcases hop with rfl | rfl | rfl
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp [GateArity]) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]
      | [a, b], _ =>
        rcases hop with rfl | rfl | rfl
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c && if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · exact absurd ⟨false, fun y => by rw [he y]; rfl⟩ hnc
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, ite_eq_left hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, ite_eq_right hb']; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y && c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd ⟨false, fun y => by rw [he y]; simp⟩ hnc
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
            · refine addg ⟨GateOp.and, [k, l]⟩ (by simp [GateArity]) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c || if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, ite_eq_left hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, ite_eq_right hb']; rfl⟩ hnc
            · exact absurd ⟨true, fun y => by rw [he y]; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y || c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
              · exact absurd ⟨true, fun y => by rw [he y]; simp⟩ hnc
            · refine addg ⟨GateOp.or, [k, l]⟩ (by simp [GateArity]) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · refine absurd ⟨!c, fun y => ?_⟩ hnc
            rw [hFK y, List.map_cons, hc y]; simp [GateOp.eval]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp [GateArity]) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]

theorem circuit (n m : ℕ) (C : Circuit) (X : (Fin m → Bool) → List Bool)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (_hX : ∀ y, (X y).length = n)
    (hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨
      ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false)
    (hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin m → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun i => if i < n + j then (C.wires (X y)).getD i false else false))
    (hinw : ∀ i < n, ∀ y, (C.wires (X y)).getD i false = (X y).getD i false)
    (hout : C.output < n + C.gates.length)
    (hnc : ¬ ∃ c, ∀ y, C.eval (X y) = c) :
    ∃ (D : Circuit) (S : Finset ℕ),
      (∀ g ∈ D.gates, GateArity g) ∧
      (∀ (j : ℕ) (hj : j < D.gates.length), ∀ i ∈ D.gates[j].inputs, i < m + j) ∧
      D.output < m + D.gates.length ∧ D.gates.length ≤ S.card ∧
      (∀ j ∈ S, j < C.gates.length ∧
        ¬ Drop n (fun w (y : Fin m → Bool) => (C.wires (X y)).getD w false) j) ∧
      ∀ y, D.eval (List.ofFn y) = C.eval (X y) := by
  obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := restrict n m C.gates
    (fun w y => (C.wires (X y)).getD w false) hops (fun i hi => by
      rcases hin i hi with ⟨c, hc⟩ | ⟨k, hk, h⟩
      · exact Or.inl ⟨c, fun y => (hinw i hi y).trans (hc y)⟩
      · exact Or.inr ⟨k, hk, fun y => (hinw i hi y).trans (h y)⟩) hrec C.gates.length le_rfl
  rcases h4 C.output hout with hc | ⟨k, hk, hk'⟩
  · exact absurd hc hnc
  · exact ⟨⟨ds, k⟩, S, h1, hb, hk, h3, h2, fun y => (hk' y).symm⟩

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

theorem many_drops_normal (n m : ℕ) (C : Circuit) (X : (Fin m → Bool) → List Bool)
    (fan : PEqualNP.MetaComplexity.FanInTwo C) (hX : ∀ y, (X y).length = n)
    (hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨
      ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false)
    (hnc : ¬ ∃ c, ∀ y, C.eval (X y) = c)
    (drops : Finset ℕ)
    (hdrop : ∀ j ∈ drops, j < C.gates.length ∧
      Drop n (fun w y => (C.wires (X y)).getD w false) j) :
    ∃ D : Circuit, (∀ g ∈ D.gates, GateArity g) ∧
      (∀ j (hj : j < D.gates.length), ∀ i ∈ D.gates[j].inputs, i < m+j) ∧
      D.output < m+D.gates.length ∧ D.size + drops.card ≤ C.size ∧
      ∀ y, D.eval (List.ofFn y) = C.eval (X y) := by
  have hops : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := fan g hg
    exact ⟨by simpa using h1, h2⟩
  have hout : C.output < n + C.gates.length := by
    by_contra h
    apply hnc
    refine ⟨false, fun y => ?_⟩
    change (run C.gates (X y)).getD C.output false = false
    exact List.getD_eq_default _ _ (by rw [run_length, hX]; omega)
  have hrec (j : ℕ) (hj : j < C.gates.length) (y : Fin m → Bool) :
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun i =>
          if i < n + j then (C.wires (X y)).getD i false else false) := by
    have h := run_gate C.gates (X y) j hj
    rw [hX] at h
    exact h
  have hinw (i : ℕ) (hi : i < n) (y : Fin m → Bool) :
      (C.wires (X y)).getD i false = (X y).getD i false :=
    run_input _ _ _ (by rwa [hX])
  obtain ⟨D, S, d1, d2, d3, d4, d5, d6⟩ := circuit n m C X hops hX hin hrec hinw hout hnc
  have hrange : drops ⊆ Finset.range C.gates.length :=
    fun j hj => Finset.mem_range.2 (hdrop j hj).1
  have hsub : S ⊆ Finset.range C.gates.length \ drops := by
    intro j hj
    obtain ⟨hjrange, hndrop⟩ := d5 j hj
    exact Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hjrange, fun h => hndrop (hdrop j h).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hrange, Finset.card_range] at hcard
  have hlen := Finset.card_le_card hrange
  rw [Finset.card_range] at hlen
  refine ⟨D,d1,d2,d3,?_,d6⟩
  change D.gates.length + drops.card ≤ C.gates.length
  omega

theorem many_drops (n m : ℕ) (C : Circuit) (X : (Fin m → Bool) → List Bool)
    (fan : PEqualNP.MetaComplexity.FanInTwo C) (hX : ∀ y, (X y).length = n)
    (hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨
      ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false)
    (hnc : ¬ ∃ c, ∀ y, C.eval (X y) = c)
    (drops : Finset ℕ)
    (hdrop : ∀ j ∈ drops, j < C.gates.length ∧
      Drop n (fun w y => (C.wires (X y)).getD w false) j) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + drops.card ≤ C.size ∧
      ∀ y, D.eval (List.ofFn y) = C.eval (X y) := by
  obtain ⟨D,ar,_,_,sz,ev⟩ := many_drops_normal n m C X fan hX hin hnc drops hdrop
  refine ⟨D,fun g hg => ?_, sz,ev⟩
  obtain ⟨h1,h2⟩ := (ar g hg).allowed
  exact ⟨by simpa using h1,h2⟩

end Restriction

namespace Hard27797Ports

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

def Normal (n : ℕ) (C : Circuit) : Prop :=
  (∀ g ∈ C.gates, GateArity g) ∧
  ∀ j (hj : j<C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n+j

def Live (C : Circuit) : Prop :=
  ∀ j < C.gates.length, 8+j ≠ C.output → 8+j ∈ C.gates.flatMap Gate.inputs

def ProperGate (width : ℕ) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ a, g.inputs = [a] ∧ a < width) ∨
  ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a < width ∧ b < width)

def ports (gs : List Gate) : List ℕ := gs.flatMap Gate.inputs

def isNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

def notCount (gs : List Gate) : ℕ := gs.countP isNot
def branchingBudget (gs : List Gate) : ℕ := gs.countP (fun g => !(isNot g))

theorem branching_not_budget (gs : List Gate) :
    branchingBudget gs + notCount gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases code : g.op <;> simp [branchingBudget,notCount,List.countP_cons,isNot,code] at ih ⊢ <;> omega

theorem port_length_raw (gs : List Gate) (shape : ∀ g ∈ gs, GateArity g) :
    (ports gs).length = gs.length + branchingBudget gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have rest := ih (fun d hd => shape d (List.mem_cons_of_mem _ hd))
    change (g.inputs ++ ports gs).length = (g::gs).length + branchingBudget (g::gs)
    rw [List.length_append,rest]
    rcases shape g (by simp) with ⟨op,arity⟩ | ⟨op,arity⟩
    · simp [arity,branchingBudget,isNot,op] <;> omega
    · rcases op with op | op <;> simp [arity,branchingBudget,isNot,op] <;> omega

end Hard27797Ports

namespace Hard27797PrefixDrops

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def pin (x : Fin 8 → Bool) : Fin 9 → Bool := Fin.cases true x
def residual (x : Fin 8 → Bool) : Bool := target (pin x)

def gate0 : Gate := ⟨.or,[0,4]⟩
def gate1 : Gate := ⟨.or,[2,9]⟩

def wire (C : Circuit) (x : Fin 9 → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

def shaped (C : Circuit) : Prop := ∀ j : Fin C.gates.length,
  ((C.gates.get j).op = .not ∧ ∃ a, a < 9+j.val ∧ (C.gates.get j).inputs = [a]) ∨
  (((C.gates.get j).op = .and ∨ (C.gates.get j).op = .or) ∧
    ∃ a b, a<b ∧ b<9+j.val ∧ (C.gates.get j).inputs = [a,b])

def fresh (C : Circuit) : Prop := ∀ j : Fin C.gates.length,
  ∀ k, k<9+j.val → ∃ x : Fin 9 → Bool, wire C x (9+j.val) ≠ wire C x k

theorem raw (C : Circuit) (x : Fin 9 → Bool) (i : Fin 9) : wire C x i.val = x i := by
  unfold wire
  change (run C.gates (List.ofFn x)).getD i.val false = _
  rw [run_input _ _ _ (by simp [i.isLt]), List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]

theorem gate_eq (C : Circuit) (x : Fin 9 → Bool) (j : Fin C.gates.length)
    (hback : ∀ i ∈ (C.gates.get j).inputs, i < 9+j.val) :
    wire C x (9+j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (wire C x)) := by
  have h := run_gate C.gates (List.ofFn x) j.val j.isLt
  simp only [List.length_ofFn] at h
  change wire C x (9+j.val) = (C.gates.get j).op.eval
    ((C.gates.get j).inputs.map fun i => if i<9+j.val then wire C x i else false) at h
  rw [h]
  congr 1
  exact List.map_congr_left fun i hi => ite_eq_left (hback i hi)

theorem fixed_pair (C : Circuit) (tail : List Gate) (hprefix : C.gates = gate0::gate1::tail)
    (x : Fin 9 → Bool) : wire C x 9 = (x 0 || x 4) ∧
      wire C x 10 = (x 2 || (x 0 || x 4)) := by
  have hlen : 2 ≤ C.gates.length := by rw [hprefix]; simp
  let j0 : Fin C.gates.length := ⟨0,by omega⟩
  let j1 : Fin C.gates.length := ⟨1,by omega⟩
  have h0 : C.gates.get j0 = gate0 := by
    change C.gates[0] = _
    simp [hprefix]
  have h1 : C.gates.get j1 = gate1 := by
    change C.gates[1] = _
    simp [hprefix]
  have hback0 (i : ℕ) (h : i ∈ (C.gates.get j0).inputs) : i < 9+j0.val := by
    rw [h0] at h
    simp [gate0] at h
    rcases h with rfl | rfl <;> simp [j0]
  have hback1 (i : ℕ) (h : i ∈ (C.gates.get j1).inputs) : i < 9+j1.val := by
    rw [h1] at h
    simp [gate1] at h
    rcases h with rfl | rfl <;> simp [j1]
  have a := gate_eq C x j0 hback0
  have b := gate_eq C x j1 hback1
  rw [h0] at a
  rw [h1] at b
  simp [j0, gate0, GateOp.eval] at a
  simp [j1, gate1, GateOp.eval] at b
  have w0 : wire C x 0 = x 0 := raw C x (0:Fin 9)
  have w2 : wire C x 2 = x 2 := raw C x (2:Fin 9)
  have w4 : wire C x 4 = x 4 := raw C x (4:Fin 9)
  rw [w0, w4] at a
  rw [w2, a] at b
  exact ⟨a,b⟩

theorem run_agrees_except_zero (gs : List Gate) (u v : List Bool) (hlen : u.length = v.length)
    (h : ∀ i : ℕ, i ≠ 0 → u.getD i false = v.getD i false)
    (avoid : ∀ g ∈ gs, 0 ∉ g.inputs) : ∀ i : ℕ, i ≠ 0 →
      (run gs u).getD i false = (run gs v).getD i false := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    have hv : g.inputs.map (fun i => u.getD i false) = g.inputs.map (fun i => v.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact h i fun he => avoid g (by simp) (he ▸ hi)
    let b := g.op.eval (g.inputs.map fun i => v.getD i false)
    change ∀ i, i ≠ 0 →
      (run gs (u ++ [g.op.eval (g.inputs.map fun j => u.getD j false)])).getD i false =
      (run gs (v ++ [b])).getD i false
    rw [hv]
    apply ih (u:=u++[b]) (v:=v++[b]) (by simp [hlen])
    · intro i hi
      by_cases hlt : i < u.length
      · rw [getD_lt _ _ _ hlt, getD_lt _ _ _ (by omega)]
        exact h i hi
      · by_cases he : i = u.length
        · subst i
          rw [getD_at, hlen, getD_at]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · exact fun g hg => avoid g (List.mem_cons_of_mem _ hg)

def probe (m : ℕ) : Fin 9 → Bool := fun i => m.testBit i.val

theorem raw_zero_reader (C : Circuit) (tail : List Gate)
    (hprefix : C.gates = gate0::gate1::tail)
    (last : C.output+1 = 9+C.gates.length)
    (heval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x) :
    ∃ j : Fin C.gates.length, 2 ≤ j.val ∧ 0 ∈ (C.gates.get j).inputs := by
  classical
  have htail : ∃ g ∈ tail, 0 ∈ g.inputs := by
    by_contra! avoid
    let u := run [gate0,gate1] (List.ofFn (probe 272))
    let v := run [gate0,gate1] (List.ofFn (probe 273))
    have hLen : u.length = 11 ∧ v.length = 11 := by decide +kernel
    have htest : ∀ i : Fin 11, i.val ≠ 0 → u.getD i.val false = v.getD i.val false := by decide +kernel
    have hinit (i : ℕ) (hi : i ≠ 0) : u.getD i false = v.getD i false := by
      by_cases hs : i < 11
      · exact htest ⟨i,hs⟩ hi
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    have hout : C.output ≠ 0 := by
      have hL : 2 ≤ C.gates.length := by rw [hprefix]; simp
      omega
    have he := run_agrees_except_zero tail u v (hLen.1.trans hLen.2.symm) hinit avoid C.output hout
    have hh (m : ℕ) : C.wires (List.ofFn (probe m)) = run tail (run [gate0,gate1] (List.ofFn (probe m))) := by
      change run C.gates (List.ofFn (probe m)) = _
      rw [hprefix]
      rfl
    have hf : target (probe 272) = target (probe 273) := by
      rw [← heval, ← heval]
      unfold Circuit.eval
      rw [hh,hh]
      exact he
    exact (by decide +kernel : target (probe 272) ≠ target (probe 273)) hf
  obtain ⟨g,hg,hread⟩ := htail
  obtain ⟨i,hi⟩ := List.get_of_mem hg
  have hJ : i.val+2 < C.gates.length := by rw [hprefix]; simp
  let j : Fin C.gates.length := ⟨i.val+2,hJ⟩
  refine ⟨j,by dsimp [j]; omega,?_⟩
  have hgj : C.gates.get j = g := by
    change C.gates[i.val+2] = g
    simpa [hprefix, List.getElem_cons_succ] using hi
  rw [hgj]
  exact hread

private theorem fresh_reader_separation (C : Circuit) (tail : List Gate)
    (hprefix : C.gates = gate0 :: gate1 :: tail) (shape : shaped C) (new : fresh C)
    (j : Fin C.gates.length) (after : 2 ≤ j.val) (read0 : 0 ∈ (C.gates.get j).inputs) :
    10 ∉ (C.gates.get j).inputs := by
  intro read10
  rcases shape j with ⟨op,a,ha,inputs⟩ | ⟨op,a,b,hab,hb,inputs⟩
  · rw [inputs] at read0 read10
    simp at read0 read10
    omega
  · rw [inputs] at read0 read10
    simp at read0 read10
    have lo : a = 0 := by omega
    have hi : b = 10 := by omega
    subst a
    subst b
    have wires (x : Fin 9 → Bool) := gate_eq C x j (by
      rw [inputs]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega)
    rcases op with h | h
    · obtain ⟨x,hx⟩ := new j 0 (by omega)
      apply hx
      rw [wires, h, inputs]
      simp only [GateOp.eval,List.map_cons,List.map_nil,List.foldl]
      rw [(fixed_pair C tail hprefix x).2, show wire C x 0 = x 0 from raw C x (0:Fin 9)]
      cases x 0 <;> cases x 2 <;> cases x 4 <;> rfl
    · obtain ⟨x,hx⟩ := new j 10 (by omega)
      apply hx
      rw [wires, h, inputs]
      simp only [GateOp.eval,List.map_cons,List.map_nil,List.foldl]
      rw [(fixed_pair C tail hprefix x).2, show wire C x 0 = x 0 from raw C x (0:Fin 9)]
      cases x 0 <;> cases x 2 <;> cases x 4 <;> rfl

private theorem pin_true_reader_drop (C : Circuit) (shape : shaped C) (j : Fin C.gates.length)
    (i : ℕ) (read : i ∈ (C.gates.get j).inputs)
    (setTrue : ∀ x : Fin 8 → Bool, wire C (pin x) i = true) :
    Drop 9 (fun w x => wire C (pin x) w) j.val := by
  rcases shape j with ⟨op,a,ha,inputs⟩ | ⟨op,a,b,hab,hb,inputs⟩
  · rw [inputs] at read
    have ia : i = a := by simpa using read
    subst i
    left
    refine ⟨false, fun x => ?_⟩
    change wire C (pin x) (9+j.val) = false
    rw [gate_eq C (pin x) j (by rw [inputs]; simpa using ha), op, inputs]
    simp [GateOp.eval, setTrue]
  · rw [inputs] at read
    have eq : i = a ∨ i = b := by simpa using read
    have wires (x : Fin 8 → Bool) := gate_eq C (pin x) j (by
      rw [inputs]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega)
    rcases eq with rfl | rfl
    · rcases op with h | h
      · exact Or.inr ⟨b,hb,fun x => by
          change wire C (pin x) (9+j.val) = wire C (pin x) b
          rw [wires,h,inputs]
          simp [GateOp.eval,setTrue]⟩
      · exact Or.inl ⟨true,fun x => by
          change wire C (pin x) (9+j.val) = true
          rw [wires,h,inputs]
          simp [GateOp.eval,setTrue]⟩
    · rcases op with h | h
      · exact Or.inr ⟨a,by omega,fun x => by
          change wire C (pin x) (9+j.val) = wire C (pin x) a
          rw [wires,h,inputs]
          simp [GateOp.eval,setTrue]⟩
      · exact Or.inl ⟨true,fun x => by
          change wire C (pin x) (9+j.val) = true
          rw [wires,h,inputs]
          simp [GateOp.eval,setTrue]⟩

theorem drop_to_eight (C : Circuit) (tail : List Gate)
    (hprefix : C.gates = gate0 :: gate1 :: tail)
    (fan : FanInTwo C) (size : C.size ≤ 12)
    (last : C.output + 1 = 9 + C.gates.length) (shape : shaped C) (new : fresh C)
    (live : ∀ j : Fin C.gates.length, j.val+1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs)
    (correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 8 ∧
      ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = residual x := by
  obtain ⟨j,hj,rj⟩ := raw_zero_reader C tail hprefix last correct
  let j1 : Fin C.gates.length := ⟨1,by have := j.isLt; omega⟩
  obtain ⟨k,hk,rk⟩ := live j1 (by dsimp [j1]; have := j.isLt; omega)
  change 1 < k.val at hk
  change 10 ∈ (C.gates.get k).inputs at rk
  have ne : j.val ≠ k.val := by
    intro eq
    have eq' : j = k := Fin.ext eq
    exact fresh_reader_separation C tail hprefix shape new j hj rj (eq'.symm ▸ rk)
  have w0 (x : Fin 8 → Bool) : wire C (pin x) 0 = true := raw C (pin x) (0:Fin 9)
  have w9 (x : Fin 8 → Bool) : wire C (pin x) 9 = true := by
    rw [(fixed_pair C tail hprefix (pin x)).1]
    change (true || _) = true
    rfl
  have w10 (x : Fin 8 → Bool) : wire C (pin x) 10 = true := by
    rw [(fixed_pair C tail hprefix (pin x)).2]
    change (_ || (true || _)) = true
    simp
  let X (x : Fin 8 → Bool) := List.ofFn (pin x)
  have xcons (x : Fin 8 → Bool) : X x = true :: List.ofFn x := by
    simp [X, pin, List.ofFn_succ]
  have hin (i : ℕ) (hi : i < 9) : (∃ c, ∀ x, (X x).getD i false = c) ∨
      ∃ b < 8, ∀ x, (X x).getD i false = (List.ofFn x).getD b false := by
    cases i with
    | zero => exact Or.inl ⟨true,fun x => by simp [xcons]⟩
    | succ i => exact Or.inr ⟨i,by omega,fun x => by simp [xcons]⟩
  have nc : ¬ ∃ b, ∀ x, C.eval (X x) = b := by
    rintro ⟨b,h⟩
    have no := (correct (pin (fun _ => false))).symm.trans (h (fun _ => false))
    have yes := (correct (pin (fun _ => true))).symm.trans (h (fun _ => true))
    have hno : target (pin (fun _ => false)) = false := by decide +kernel
    have hyes : target (pin (fun _ => true)) = true := by decide +kernel
    simp only [hno,hyes] at no yes
    exact Bool.false_ne_true (no.trans yes.symm)
  let drops : Finset ℕ := {0,1,j.val,k.val}
  have drops_card : drops.card = 4 := by
    have h0j : 0 ≠ j.val := by omega
    have h0k : 0 ≠ k.val := by omega
    have h1j : 1 ≠ j.val := by omega
    have h1k : 1 ≠ k.val := by omega
    simp [drops,h0j,h0k,h1j,h1k,ne]
  have hd (i : ℕ) (hi : i ∈ drops) : i < C.gates.length ∧
      Drop 9 (fun w x => (C.wires (X x)).getD w false) i := by
    simp only [drops, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨by have := j.isLt; omega,Or.inl ⟨true,w9⟩⟩
    · exact ⟨by have := j.isLt; omega,Or.inl ⟨true,w10⟩⟩
    · exact ⟨j.isLt,pin_true_reader_drop C shape j 0 rj w0⟩
    · exact ⟨k.isLt,pin_true_reader_drop C shape k 10 rk w10⟩
  obtain ⟨D,hfan,hsize,he⟩ := many_drops 9 8 C X fan (by simp [X]) hin nc drops hd
  refine ⟨D,hfan,by omega,fun x => (he x).trans (correct (pin x))⟩

end Hard27797PrefixDrops

namespace Hard27797ProbeData

def essential : Array (Fin 256) := #[
  0, 40, 66, 34, 64, 10, 6, 8, 48, 0, 129, 128, 33, 17, 16, 5,
  48, 40, 0, 34, 33, 10, 16, 8, 48, 68, 66, 0, 33, 17, 6, 5,
  132, 40, 66, 34, 0, 10, 6, 5, 132, 68, 66, 128, 64, 0, 6, 5,
  48, 40, 129, 34, 33, 10, 0, 5, 48, 40, 66, 34, 33, 10, 6, 0,
  48, 40, 66, 34, 33, 10, 6, 5
]

def triples : Array (Fin 4 × Fin 4 × Fin 4 × Fin 256 × Fin 256 × Fin 256) := #[
  (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0),
  (0,0,0,0,0,0), (0,0,0,0,0,0), (0,1,3,40,40,64), (0,1,2,68,128,68), (0,1,2,40,64,40), (0,1,3,68,8,8), (0,1,2,40,16,16), (0,1,2,40,8,8),
  (0,0,0,0,0,0), (0,2,3,40,40,64), (0,0,0,0,0,0), (0,1,2,66,34,34), (0,1,2,66,64,64), (0,1,2,66,10,10), (0,2,3,16,2,2), (0,1,2,66,8,8),
  (0,0,0,0,0,0), (0,1,2,128,68,68), (0,1,2,34,66,34), (0,0,0,0,0,0), (0,1,2,34,64,34), (0,1,3,128,2,2), (0,1,2,34,6,6), (0,1,3,34,0,0),
  (0,0,0,0,0,0), (0,1,2,64,40,40), (0,1,2,64,66,64), (0,1,2,64,34,34), (0,0,0,0,0,0), (0,1,2,64,10,10), (0,2,3,6,0,0), (0,1,2,64,8,8),
  (0,0,0,0,0,0), (0,2,3,68,8,8), (0,1,2,10,66,10), (0,2,3,128,2,2), (0,1,2,10,64,10), (0,0,0,0,0,0), (0,1,2,10,6,6), (0,1,2,10,8,8),
  (0,0,0,0,0,0), (0,1,2,16,40,16), (0,1,3,16,2,2), (0,1,2,6,34,6), (0,1,3,6,0,0), (0,1,2,6,10,6), (0,0,0,0,0,0), (0,1,2,6,8,6),
  (0,0,0,0,0,0), (0,1,2,8,40,8), (0,1,2,8,66,8), (0,2,3,34,0,0), (0,1,2,8,64,8), (0,1,2,8,10,8), (0,1,2,8,6,6), (0,0,0,0,0,0),
  (0,0,0,0,0,0), (0,0,0,0,0,0), (0,1,3,48,48,128), (0,1,2,48,128,48), (0,1,2,132,64,64), (0,1,3,132,16,16), (0,1,2,48,16,16), (0,1,2,48,8,8),
  (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0),
  (0,2,3,48,48,128), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,1,2,129,128,128), (0,1,2,129,33,33), (0,1,2,129,17,17), (0,1,2,129,16,16), (0,2,3,8,1,1),
  (0,1,2,128,48,48), (0,0,0,0,0,0), (0,1,2,128,129,128), (0,0,0,0,0,0), (0,1,2,128,33,33), (0,1,2,128,17,17), (0,1,2,128,16,16), (0,2,3,5,0,0),
  (0,1,2,64,132,64), (0,0,0,0,0,0), (0,1,2,33,129,33), (0,1,2,33,128,33), (0,0,0,0,0,0), (0,1,3,64,1,1), (0,1,3,33,0,0), (0,1,2,33,5,5),
  (0,2,3,132,16,16), (0,0,0,0,0,0), (0,1,2,17,129,17), (0,1,2,17,128,17), (0,2,3,64,1,1), (0,0,0,0,0,0), (0,1,2,17,16,16), (0,1,2,17,5,5),
  (0,1,2,16,48,16), (0,0,0,0,0,0), (0,1,2,16,129,16), (0,1,2,16,128,16), (0,2,3,33,0,0), (0,1,2,16,17,16), (0,0,0,0,0,0), (0,1,2,16,5,5),
  (0,1,2,8,48,8), (0,0,0,0,0,0), (0,1,3,8,1,1), (0,1,3,5,0,0), (0,1,2,5,33,5), (0,1,2,5,17,5), (0,1,2,5,16,5), (0,0,0,0,0,0),
  (0,0,0,0,0,0), (0,1,2,48,40,40), (0,0,0,0,0,0), (0,1,2,48,34,34), (0,2,3,64,32,32), (0,2,3,10,10,16), (0,1,2,48,16,16), (0,1,2,48,8,8),
  (0,1,2,40,48,40), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,2,3,128,32,32), (0,1,2,40,33,33), (0,2,3,17,8,8), (0,1,2,40,16,16), (0,1,2,40,8,8),
  (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0),
  (0,1,2,34,48,34), (0,1,3,128,32,32), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,1,2,34,33,33), (0,1,2,128,17,17), (0,1,2,34,16,16), (0,1,3,34,0,0),
  (0,1,3,64,32,32), (0,1,2,33,40,33), (0,0,0,0,0,0), (0,1,2,33,34,33), (0,0,0,0,0,0), (0,1,2,64,10,10), (0,1,3,33,0,0), (0,1,2,33,8,8),
  (0,1,3,10,10,16), (0,1,3,17,8,8), (0,0,0,0,0,0), (0,1,2,17,128,17), (0,1,2,10,64,10), (0,0,0,0,0,0), (0,1,2,10,16,10), (0,1,2,10,8,8),
  (0,1,2,16,48,16), (0,1,2,16,40,16), (0,0,0,0,0,0), (0,1,2,16,34,16), (0,2,3,33,0,0), (0,1,2,16,10,10), (0,0,0,0,0,0), (0,1,2,16,8,8),
  (0,1,2,8,48,8), (0,1,2,8,40,8), (0,0,0,0,0,0), (0,2,3,34,0,0), (0,1,2,8,33,8), (0,1,2,8,10,8), (0,1,2,8,16,8), (0,0,0,0,0,0),
  (0,0,0,0,0,0), (0,1,2,48,68,48), (0,1,2,48,66,48), (0,0,0,0,0,0), (0,1,2,132,64,64), (0,1,3,132,16,16), (0,1,2,48,6,6), (0,1,3,48,4,4),
  (0,1,2,68,48,48), (0,0,0,0,0,0), (0,2,3,129,64,64), (0,0,0,0,0,0), (0,1,2,68,33,33), (0,1,2,68,17,17), (0,2,3,16,4,4), (0,1,2,68,5,5),
  (0,1,2,66,48,48), (0,1,3,129,64,64), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,1,2,66,33,33), (0,1,2,66,17,17), (0,1,2,129,16,16), (0,1,3,66,1,1),
  (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0),
  (0,1,2,64,132,64), (0,1,2,33,68,33), (0,1,2,33,66,33), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,1,3,64,1,1), (0,1,2,33,6,6), (0,1,2,33,5,5),
  (0,2,3,132,16,16), (0,1,2,17,68,17), (0,1,2,17,66,17), (0,0,0,0,0,0), (0,2,3,64,1,1), (0,0,0,0,0,0), (0,1,2,17,6,6), (0,1,2,17,5,5),
  (0,1,2,6,48,6), (0,1,3,16,4,4), (0,1,2,16,129,16), (0,0,0,0,0,0), (0,1,2,6,33,6), (0,1,2,6,17,6), (0,0,0,0,0,0), (0,1,2,6,5,5),
  (0,2,3,48,4,4), (0,1,2,5,68,5), (0,2,3,66,1,1), (0,0,0,0,0,0), (0,1,2,5,33,5), (0,1,2,5,17,5), (0,1,2,5,6,5), (0,0,0,0,0,0),
  (0,0,0,0,0,0), (0,1,2,132,40,40), (0,2,3,66,66,128), (0,1,2,132,34,34), (0,0,0,0,0,0), (0,1,2,132,10,10), (0,1,2,132,6,6), (0,2,3,8,4,4),
  (0,1,2,40,132,40), (0,0,0,0,0,0), (0,1,2,40,129,40), (0,1,2,68,128,68), (0,0,0,0,0,0), (0,1,3,68,8,8), (0,1,3,40,4,4), (0,1,2,40,5,5),
  (0,1,3,66,66,128), (0,1,2,129,40,40), (0,0,0,0,0,0), (0,1,2,66,34,34), (0,0,0,0,0,0), (0,1,2,66,10,10), (0,1,3,129,2,2), (0,1,2,66,8,8),
  (0,1,2,34,132,34), (0,1,2,128,68,68), (0,1,2,34,66,34), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,1,3,128,2,2), (0,1,2,34,6,6), (0,1,2,34,5,5),
  (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0),
  (0,1,2,10,132,10), (0,2,3,68,8,8), (0,1,2,10,66,10), (0,2,3,128,2,2), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,1,2,10,6,6), (0,1,2,10,5,5),
  (0,1,2,6,132,6), (0,2,3,40,4,4), (0,2,3,129,2,2), (0,1,2,6,34,6), (0,0,0,0,0,0), (0,1,2,6,10,6), (0,0,0,0,0,0), (0,1,2,6,5,5),
  (0,1,3,8,4,4), (0,1,2,5,40,5), (0,1,2,8,66,8), (0,1,2,5,34,5), (0,0,0,0,0,0), (0,1,2,5,10,5), (0,1,2,5,6,5), (0,0,0,0,0,0),
  (0,0,0,0,0,0), (0,1,2,132,68,68), (0,2,3,66,66,128), (0,1,2,132,128,128), (0,1,2,132,64,64), (0,0,0,0,0,0), (0,1,2,132,6,6), (0,2,3,8,4,4),
  (0,1,2,68,132,68), (0,0,0,0,0,0), (0,2,3,129,64,64), (0,1,2,68,128,68), (0,1,2,68,64,64), (0,0,0,0,0,0), (0,2,3,16,4,4), (0,1,2,68,5,5),
  (0,1,3,66,66,128), (0,1,3,129,64,64), (0,0,0,0,0,0), (0,1,2,66,128,66), (0,1,2,66,64,64), (0,0,0,0,0,0), (0,1,2,129,16,16), (0,1,2,66,8,8),
  (0,1,2,128,132,128), (0,1,2,128,68,68), (0,1,2,128,66,66), (0,0,0,0,0,0), (0,1,2,128,64,64), (0,0,0,0,0,0), (0,1,2,128,6,6), (0,2,3,5,0,0),
  (0,1,2,64,132,64), (0,1,2,64,68,64), (0,1,2,64,66,64), (0,1,2,64,128,64), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,2,3,6,0,0), (0,1,2,64,5,5),
  (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0),
  (0,1,2,6,132,6), (0,1,3,16,4,4), (0,1,2,16,129,16), (0,1,2,6,128,6), (0,1,3,6,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,1,2,6,5,5),
  (0,1,3,8,4,4), (0,1,2,5,68,5), (0,1,2,8,66,8), (0,1,3,5,0,0), (0,1,2,5,64,5), (0,0,0,0,0,0), (0,1,2,5,6,5), (0,0,0,0,0,0),
  (0,0,0,0,0,0), (0,1,2,48,40,40), (0,1,3,48,48,128), (0,1,2,48,34,34), (0,1,3,132,32,32), (0,1,2,132,10,10), (0,0,0,0,0,0), (0,1,2,48,8,8),
  (0,1,2,40,48,40), (0,0,0,0,0,0), (0,1,2,40,129,40), (0,2,3,128,32,32), (0,1,2,40,33,33), (0,2,3,17,8,8), (0,0,0,0,0,0), (0,1,2,40,5,5),
  (0,2,3,48,48,128), (0,1,2,129,40,40), (0,0,0,0,0,0), (0,1,2,129,34,34), (0,1,2,129,33,33), (0,1,2,129,10,10), (0,0,0,0,0,0), (0,2,3,8,1,1),
  (0,1,2,34,48,34), (0,1,3,128,32,32), (0,1,2,34,129,34), (0,0,0,0,0,0), (0,1,2,34,33,33), (0,1,2,128,17,17), (0,0,0,0,0,0), (0,1,2,34,5,5),
  (0,2,3,132,32,32), (0,1,2,33,40,33), (0,1,2,33,129,33), (0,1,2,33,34,33), (0,0,0,0,0,0), (0,2,3,10,1,1), (0,0,0,0,0,0), (0,1,2,33,5,5),
  (0,1,2,10,132,10), (0,1,3,17,8,8), (0,1,2,10,129,10), (0,1,2,17,128,17), (0,1,3,10,1,1), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,1,2,10,5,5),
  (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0),
  (0,1,2,8,48,8), (0,1,2,5,40,5), (0,1,3,8,1,1), (0,1,2,5,34,5), (0,1,2,5,33,5), (0,1,2,5,10,5), (0,0,0,0,0,0), (0,0,0,0,0,0),
  (0,0,0,0,0,0), (0,1,2,48,40,40), (0,1,2,48,66,48), (0,1,2,48,34,34), (0,2,3,64,32,32), (0,2,3,10,10,16), (0,1,2,48,6,6), (0,0,0,0,0,0),
  (0,1,2,40,48,40), (0,0,0,0,0,0), (0,1,3,40,40,64), (0,1,3,68,32,32), (0,1,2,40,33,33), (0,1,2,68,17,17), (0,1,2,40,16,16), (0,0,0,0,0,0),
  (0,1,2,66,48,48), (0,2,3,40,40,64), (0,0,0,0,0,0), (0,1,2,66,34,34), (0,1,2,66,33,33), (0,1,2,66,10,10), (0,2,3,16,2,2), (0,0,0,0,0,0),
  (0,1,2,34,48,34), (0,2,3,68,32,32), (0,1,2,34,66,34), (0,0,0,0,0,0), (0,1,2,34,33,33), (0,2,3,17,2,2), (0,1,2,34,6,6), (0,0,0,0,0,0),
  (0,1,3,64,32,32), (0,1,2,33,40,33), (0,1,2,33,66,33), (0,1,2,33,34,33), (0,0,0,0,0,0), (0,1,2,64,10,10), (0,1,2,33,6,6), (0,0,0,0,0,0),
  (0,1,3,10,10,16), (0,1,2,17,68,17), (0,1,2,10,66,10), (0,1,3,17,2,2), (0,1,2,10,64,10), (0,0,0,0,0,0), (0,1,2,10,6,6), (0,0,0,0,0,0),
  (0,1,2,6,48,6), (0,1,2,16,40,16), (0,1,3,16,2,2), (0,1,2,6,34,6), (0,1,2,6,33,6), (0,1,2,6,10,6), (0,0,0,0,0,0), (0,0,0,0,0,0),
  (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0), (0,0,0,0,0,0),
  (0,0,0,0,0,0), (0,1,2,48,40,40), (0,1,2,48,66,48), (0,1,2,48,34,34), (0,1,2,132,64,64), (0,1,2,132,10,10), (0,1,2,48,6,6), (0,1,2,48,8,8),
  (0,1,2,40,48,40), (0,0,0,0,0,0), (0,1,2,40,129,40), (0,1,2,68,128,68), (0,1,2,40,33,33), (0,1,2,68,17,17), (0,1,2,40,16,16), (0,1,2,40,5,5),
  (0,1,2,66,48,48), (0,1,2,129,40,40), (0,0,0,0,0,0), (0,1,2,66,34,34), (0,1,2,66,33,33), (0,1,2,66,10,10), (0,1,2,129,16,16), (0,1,2,66,8,8),
  (0,1,2,34,48,34), (0,1,2,128,68,68), (0,1,2,34,66,34), (0,0,0,0,0,0), (0,1,2,34,33,33), (0,1,2,128,17,17), (0,1,2,34,6,6), (0,1,2,34,5,5),
  (0,1,2,64,132,64), (0,1,2,33,40,33), (0,1,2,33,66,33), (0,1,2,33,34,33), (0,0,0,0,0,0), (0,1,2,64,10,10), (0,1,2,33,6,6), (0,1,2,33,5,5),
  (0,1,2,10,132,10), (0,1,2,17,68,17), (0,1,2,10,66,10), (0,1,2,17,128,17), (0,1,2,10,64,10), (0,0,0,0,0,0), (0,1,2,10,6,6), (0,1,2,10,5,5),
  (0,1,2,6,48,6), (0,1,2,16,40,16), (0,1,2,16,129,16), (0,1,2,6,34,6), (0,1,2,6,33,6), (0,1,2,6,10,6), (0,0,0,0,0,0), (0,1,2,6,5,5),
  (0,1,2,8,48,8), (0,1,2,5,40,5), (0,1,2,8,66,8), (0,1,2,5,34,5), (0,1,2,5,33,5), (0,1,2,5,10,5), (0,1,2,5,6,5), (0,0,0,0,0,0)
]

end Hard27797ProbeData

namespace Hard27797Probes

open Hard27797PrefixDrops (residual)

def family (p : Fin 9) (x : Fin 8 → Bool) : Bool :=
  residual (fun i => if i.val = p.val then false else x i)

theorem all_free (x : Fin 8 → Bool) : family 8 x = residual x := by
  unfold family
  congr 1
  funext i
  have off : i.val ≠ (8 : Fin 9).val := by
    have := i.isLt
    change i.val ≠ 8
    omega
  exact ite_eq_right off

private def row (m : Fin 256) (i : Fin 8) : Bool := m.val.testBit i.val
private def flipped (m : Fin 256) (a i : Fin 8) : Bool :=
  if i = a then !(row m i) else row m i

private def rawProbe (p : Fin 9) (a : Fin 8) : Fin 256 :=
  Hard27797ProbeData.essential[p.val*8+a.val]?.getD 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem essentialChecked : ∀ (p : Fin 9) (a : Fin 8), a.val ≠ p.val →
    family p (row (rawProbe p a)) ≠ family p (flipped (rawProbe p a) a) := by
  decide +kernel

theorem essential (p : Fin 9) (a : Fin 8) (ha : a.val ≠ p.val) :
    ∃ x y : Fin 8 → Bool, (∀ i, i ≠ a → x i = y i) ∧ family p x ≠ family p y := by
  exact ⟨row (rawProbe p a),flipped (rawProbe p a) a,
    fun i hi => by simp [flipped,hi],essentialChecked p a ha⟩

theorem oriented_pivots (a : Fin 8) :
    ∃ x y : Fin 8 → Bool,
      (∀ i, i ≠ a → x i = y i) ∧ x a = false ∧ y a = true ∧
      family 8 x = false ∧ family 8 y = true := by
  have props : ∀ a : Fin 8, row (rawProbe 8 a) a = false ∧
      flipped (rawProbe 8 a) a a = true ∧
      family 8 (row (rawProbe 8 a)) = false ∧
      family 8 (flipped (rawProbe 8 a) a) = true := by decide +kernel
  exact ⟨row (rawProbe 8 a),flipped (rawProbe 8 a) a,
    fun i hi => by simp [flipped,hi],props a⟩

private def sample (a b : Fin 8) (u : Fin 4) (m : Fin 256) (i : Fin 8) : Bool :=
  if i = a then u.val.testBit 0 else if i = b then u.val.testBit 1 else row m i

private abbrev distinct (p : Fin 9) (a b : Fin 8) (u v : Fin 4) (m : Fin 256) : Prop :=
  family p (sample a b u m) ≠ family p (sample a b v m)

private def lookup (p : Fin 9) (a b : Fin 8) :
    Fin 4 × Fin 4 × Fin 4 × Fin 256 × Fin 256 × Fin 256 :=
  Hard27797ProbeData.triples[(p.val*8+a.val)*8+b.val]?.getD (0,0,0,0,0,0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem signatures : ∀ (p : Fin 9) (a b : Fin 8), a ≠ b →
    a.val ≠ p.val → b.val ≠ p.val →
    let (u,v,w,r,s,t) := lookup p a b
    distinct p a b u v r ∧ distinct p a b u w s ∧ distinct p a b v w t := by
  decide +kernel

set_option maxRecDepth 10000 in

theorem no_pair (p : Fin 9) (a b : Fin 8) (ab : a ≠ b) (ap : a.val ≠ p.val)
    (bp : b.val ≠ p.val) (signal : (Fin 8 → Bool) → Bool)
    (depend : ∀ x y, x a = y a → x b = y b → signal x = signal y)
    (factor : ∀ x y, (∀ i, i ≠ a → i ≠ b → x i = y i) →
      signal x = signal y → family p x = family p y) : False := by
  have hk := signatures p a b ab ap bp
  generalize lookup p a b = results at hk
  rcases results with ⟨u,v,w,r,s,t⟩
  obtain ⟨uv,uw,vw⟩ := hk
  let z : Fin 256 := 0
  have contexts (q : Fin 4) (m : Fin 256) : signal (sample a b q m) = signal (sample a b q z) := by
    apply depend
    · simp [sample]
    · simp [sample, ab.symm]
  have apart (j k : Fin 4) (m : Fin 256) (h : distinct p a b j k m) :
      signal (sample a b j z) ≠ signal (sample a b k z) := by
    intro he
    apply h
    apply factor
    · intro i ia ib
      simp [sample,ia,ib]
    · exact (contexts j m).trans (he.trans (contexts k m).symm)
  have a1 := apart u v r uv
  have a2 := apart u w s uw
  have a3 := apart v w t vw
  have pigeon : ∀ a b c : Bool, a ≠ b → a ≠ c → b ≠ c → False := by decide +kernel
  exact pigeon _ _ _ a1 a2 a3

end Hard27797Probes

namespace Hard27797CircuitCounts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Hard27797Ports Hard27797Probes
open Restriction

def computes (p : Fin 9) (C : Circuit) : Prop :=
  ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = family p x

theorem agree (hidden : Finset ℕ) (gs : List Gate) (a b : List Bool)
    (hlen : a.length = b.length)
    (same : ∀ i, i ∉ hidden → a.getD i false = b.getD i false)
    (avoid : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ hidden) :
    ∀ i, i ∉ hidden → (run gs a).getD i false = (run gs b).getD i false := by
  induction gs generalizing a b with
  | nil => exact same
  | cons g gs ih =>
    have mapEq : g.inputs.map (fun i => a.getD i false) =
        g.inputs.map (fun i => b.getD i false) :=
      List.map_congr_left fun i hi => same i (avoid g (by simp) i hi)
    let v := g.op.eval (g.inputs.map fun i => b.getD i false)
    change ∀ i, i ∉ hidden →
      (run gs (a ++ [g.op.eval (g.inputs.map fun j => a.getD j false)])).getD i false =
      (run gs (b ++ [v])).getD i false
    rw [mapEq]
    apply ih (a:=a++[v]) (b:=b++[v]) (by simp [hlen])
    · intro i hi
      by_cases hlt : i < a.length
      · rw [getD_lt _ _ _ hlt, getD_lt _ _ _ (by omega)]
        exact same i hi
      · by_cases he : i = a.length
        · subst i
          rw [getD_at, hlen, getD_at]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · exact fun d hd => avoid d (List.mem_cons_of_mem _ hd)

theorem ofFn_get (x : Fin 8 → Bool) (i : Fin 8) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]

theorem computed_output (p : Fin 9) (C : Circuit) (he : computes p C) :
    8 ≤ C.output := by
  by_contra! h
  let a : Fin 8 := ⟨C.output,h⟩
  have fail : ∀ (p : Fin 9) (i : Fin 8), family p (fun j => decide (j=i)) = false := by
    decide +kernel
  let x : Fin 8 → Bool := fun i => decide (i=a)
  have hx := he x
  rw [show family p x = false from fail p a] at hx
  change (run C.gates (List.ofFn x)).getD a.val false = false at hx
  rw [run_input _ _ _ (by simp),ofFn_get] at hx
  simp [x] at hx

theorem normal_fan (C : Circuit) (norm : Normal 8 C) : FanInTwo C := by
  intro g hg
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (norm.1 g hg).allowed

private theorem run_append (gs ds : List Gate) (x : List Bool) :
    run (gs++ds) x = run ds (run gs x) := by
  simp only [run,List.foldl_append]

theorem nonconstant (p : Fin 9) (C : Circuit) (he : computes p C) :
    ¬ ∃ c, ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = c := by
  have differs : ∀ p : Fin 9, family p (fun _ => false) ≠ family p (fun _ => true) := by
    decide +kernel
  rintro ⟨c,hc⟩
  exact differs p ((he _).symm.trans ((hc _).trans ((hc _).symm.trans (he _))))

theorem input_identity (i : ℕ) (hi : i < 8) :
    (∃ c, ∀ x : Fin 8 → Bool, (List.ofFn x).getD i false = c) ∨
      ∃ j<8, ∀ x : Fin 8 → Bool, (List.ofFn x).getD i false = (List.ofFn x).getD j false :=
  Or.inr ⟨i,hi,fun _ => rfl⟩

private theorem no_unread (p : Fin 9) (C : Circuit) (norm : Normal 8 C) (he : computes p C)
    (least : ∀ D : Circuit, FanInTwo D → computes p D → C.size ≤ D.size) : Live C := by
  intro j hj off
  by_contra missing
  let pre := C.gates.take j
  let tail := C.gates.drop (j+1)
  let g := C.gates[j]
  let zero : Gate := ⟨.or,[]⟩
  let E : Circuit := ⟨pre ++ zero::tail,C.output⟩
  have exactC : C.gates = pre ++ g::tail := by
    dsimp [pre,g,tail]
    rw [List.getElem_cons_drop,List.take_append_drop]
  have lenPre : pre.length = j := by
    simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
  have Esize : E.size = C.size := by
    change (pre ++ zero::tail).length = C.gates.length
    conv_rhs => rw [exactC]
    simp
  have fan := normal_fan C norm
  have efan : FanInTwo E := by
    intro u hu
    change u ∈ pre ++ zero::tail at hu
    rcases List.mem_append.mp hu with upre | other
    · exact fan u (by rw [exactC]; exact List.mem_append_left _ upre)
    · rcases List.mem_cons.mp other with rfl | utail
      · simp [zero]
      · exact fan u (by rw [exactC]; simp [utail])
  have equal (x : Fin 8 → Bool) : E.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    let w := run pre (List.ofFn x)
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    have wl : w.length = 8+j := by simp [w,run_length,lenPre]
    change (run (pre ++ zero::tail) (List.ofFn x)).getD C.output false =
      (run C.gates (List.ofFn x)).getD C.output false
    rw [exactC,run_append,run_append]
    change (run tail (w ++ [false])).getD C.output false =
      (run tail (w ++ [v])).getD C.output false
    apply agree {8+j} tail _ _ (by simp) _ _ C.output (by simpa [eq_comm] using off)
    · intro i hi
      have away : i ≠ w.length := by simpa [wl] using hi
      by_cases early : i < w.length
      · rw [getD_lt _ _ _ early,getD_lt _ _ _ early]
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
    · intro d hd i hi hm
      have e : i=8+j := by simpa using hm
      exact missing (List.mem_flatMap.mpr ⟨d,by rw [exactC]; simp [hd],e ▸ hi⟩)
  have evalid : computes p E := fun x => (equal x).trans (he x)
  have drop : ∀ i ∈ ({j}:Finset ℕ), i < E.gates.length ∧
      Drop 8 (fun w (x : Fin 8 → Bool) => (E.wires (List.ofFn x)).getD w false) i := by
    intro i hi
    have ij : i=j := by simpa using hi
    subst i
    have inE : j < E.gates.length := by
      change j < E.size
      rw [Esize]
      exact hj
    refine ⟨inE,Or.inl ⟨false,fun x => ?_⟩⟩
    have ee : E.gates[j] = zero := by
      change (pre ++ zero::tail)[j] = zero
      rw [List.getElem_append_right (by omega)]
      simp [lenPre]
    change (run E.gates (List.ofFn x)).getD (8+j) false = false
    have hh := run_gate E.gates (List.ofFn x) j inE
    simp only [List.length_ofFn] at hh
    rw [hh,ee]
    rfl
  obtain ⟨D,dfan,size,exactD⟩ := many_drops 8 8 E List.ofFn efan
    (by simp) input_identity (nonconstant p E evalid) {j} drop
  have no := least D dfan (fun x => (exactD x).trans (evalid x))
  simp only [Finset.card_singleton,Esize] at size
  omega

theorem normalize_least (p : Fin 9) (bound : ℕ)
    (given : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ bound ∧ computes p C) :
    ∃ C : Circuit, Normal 8 C ∧ C.size ≤ bound ∧ computes p C ∧
      C.output < 8+C.gates.length ∧
      Live C ∧
      (∀ D : Circuit, FanInTwo D → computes p D → C.size ≤ D.size) := by
  classical
  let feasible (s : ℕ) := ∃ D : Circuit, FanInTwo D ∧ computes p D ∧ D.size = s
  obtain ⟨seed,seedFan,seedCap,seedEval⟩ := given
  have some : ∃ s, feasible s := ⟨seed.size,seed,seedFan,seedEval,rfl⟩
  obtain ⟨M,fan,correct,ms⟩ := Nat.find_spec some
  have least (D : Circuit) (leg : FanInTwo D) (eval : computes p D) : M.size ≤ D.size := by
    rw [ms]
    exact Nat.find_min' some ⟨D,leg,eval,rfl⟩
  obtain ⟨D,shape,back,inside,cap,same⟩ :=
    many_drops_normal 8 8 M List.ofFn fan (by simp) input_identity
      (nonconstant p M correct) ∅ (by simp)
  simp at cap
  have exactD : computes p D := fun x => (same x).trans (correct x)
  have minimal : ∀ E : Circuit, FanInTwo E → computes p E → D.size ≤ E.size :=
    fun E leg ev => cap.trans (least E leg ev)
  exact ⟨D,⟨shape,back⟩,cap.trans ((least seed seedFan seedEval).trans seedCap),
    exactD,inside,no_unread p D ⟨shape,back⟩ exactD minimal,minimal⟩

theorem last (C : Circuit) (inside : C.output < 8+C.gates.length)
    (out : 8 ≤ C.output) (norm : Normal 8 C) (live : Live C) :
    C.output+1 = 8+C.gates.length := by
  let j := C.gates.length-1
  have bj : j < C.gates.length := by dsimp [j]; omega
  by_contra off
  have away : 8+j ≠ C.output := by dsimp [j]; omega
  obtain ⟨g,mem,used⟩ := List.mem_flatMap.mp (live j bj away)
  obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem mem
  have early := norm.2 k hk _ used
  dsimp [j] at early
  omega

theorem actual_ports (C : Circuit) (_norm : Normal 8 C) :
    ports C.gates = C.gates.flatMap Gate.inputs := by
  rfl

theorem unpinned_used (p : Fin 9) (C : Circuit) (he : computes p C)
    (i : Fin 8) (ip : i.val ≠ p.val) : i.val ∈ C.gates.flatMap Gate.inputs := by
  by_contra absent
  have hout := computed_output p C he
  obtain ⟨x,y,close,sep⟩ := essential p i ip
  have h (j : ℕ) (hj : j ∉ ({i.val}:Finset ℕ)) :
      (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
    by_cases ij : j < 8
    · let k : Fin 8 := ⟨j,ij⟩
      exact (ofFn_get x k).trans ((close k (by intro e; apply hj; simp [k,←e])).trans
        (ofFn_get y k).symm)
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
  have avoid (g : Gate) (hg : g ∈ C.gates) (j : ℕ) (hj : j ∈ g.inputs) :
      j ∉ ({i.val}:Finset ℕ) := by
    intro same
    have e : j = i.val := by simpa using same
    exact absent (List.mem_flatMap.mpr ⟨g,hg,e ▸ hj⟩)
  have same := agree {i.val} C.gates (List.ofFn x) (List.ofFn y) (by simp) h avoid C.output
    (by simp; have := i.isLt; omega)
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at same
  exact sep ((he x).symm.trans (same.trans (he y)))

theorem support_lower (p : Fin 9) (C : Circuit) (norm : Normal 8 C)
    (he : computes p C) (hl : C.output+1 = 8+C.gates.length)
    (live : Live C) :
    (if p.val < 8 then 7 else 8) + (C.gates.length-1) ≤
      (if p.val < 8 then (ports C.gates).toFinset.erase p.val else (ports C.gates).toFinset).card := by
  let low := (Finset.range 8).erase p.val
  let high := (Finset.range (C.gates.length-1)).image (fun j : ℕ => 8+j)
  have dis : Disjoint low high := by
    apply Finset.disjoint_left.mpr
    intro i il ih
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ih
    have := Finset.mem_range.mp (Finset.mem_erase.mp il).2
    omega
  have sub : low ∪ high ⊆ (ports C.gates).toFinset := by
    intro i hi
    rw [actual_ports C norm, List.mem_toFinset]
    rcases Finset.mem_union.mp hi with lo | high
    · have l : i<8 := Finset.mem_range.mp (Finset.mem_erase.mp lo).2
      exact unpinned_used p C he ⟨i,l⟩ (Finset.mem_erase.mp lo).1
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp high
      have jlt := Finset.mem_range.mp hj
      exact live j (by omega) (by omega)
  have sub' : low ∪ high ⊆
      (if p.val < 8 then (ports C.gates).toFinset.erase p.val else (ports C.gates).toFinset) := by
    intro i hi
    split
    · rename_i hp
      refine Finset.mem_erase.mpr ⟨?_,sub hi⟩
      intro same
      subst i
      rcases Finset.mem_union.mp hi with lo | high
      · exact (Finset.mem_erase.mp lo).1 rfl
      · obtain ⟨j,_,eq⟩ := Finset.mem_image.mp high
        omega
    · exact sub hi
  have cards := Finset.card_le_card sub'
  rw [Finset.card_union_of_disjoint dis] at cards
  have highCard : high.card = C.gates.length-1 := by
    rw [Finset.card_image_of_injective _ (by intro a b eq; change 8+a=8+b at eq; omega),
      Finset.card_range]
  have lowCard : low.card = if p.val<8 then 7 else 8 := by
    split
    · rename_i l
      have := Finset.card_erase_add_one (Finset.mem_range.mpr l)
      simpa [low] using Nat.eq_sub_of_add_eq this
    · rename_i l
      have no : p.val ∉ Finset.range 8 := by simpa using l
      simp [low,Finset.erase_eq_of_notMem no]
  rwa [lowCard,highCard] at cards

theorem port_length (C : Circuit) (norm : Normal 8 C) :
    (ports C.gates).length = C.gates.length + branchingBudget C.gates :=
  port_length_raw _ norm.1

end Hard27797CircuitCounts

namespace Hard27797GateTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Hard27797Ports
open Restriction Hard27797CircuitCounts Hard27797Probes

def wire (C : Circuit) (x : Fin 8 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem gate (C : Circuit) (norm : Normal 8 C) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin 8 → Bool) :
    wire C x (8+j) = C.gates[j].op.eval (C.gates[j].inputs.map (wire C x)) := by
  have h := run_gate C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  change wire C x (8+j) =
    C.gates[j].op.eval (C.gates[j].inputs.map fun w => if w < 8+j then wire C x w else false) at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro w hw
  exact ite_eq_left (norm.2 j hj w hw)

theorem shape (C : Circuit) (norm : Normal 8 C) (j : ℕ) (hj : j < C.gates.length) :
    ProperGate (8+j) C.gates[j] := by
  have hg : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have back := norm.2 j hj
  rcases norm.1 _ hg with ⟨h,one⟩ | ⟨h,two⟩
  · obtain ⟨a,e⟩ := List.length_eq_one_iff.mp one
    exact Or.inl ⟨h,a,e,back a (by rw [e]; simp)⟩
  ·
    obtain ⟨a,b,e⟩ := List.length_eq_two.mp two
    exact Or.inr ⟨h,a,b,e,back a (by rw [e]; simp),back b (by rw [e]; simp)⟩

theorem no_duplicate (p : Fin 9) (C : Circuit) (norm : Normal 8 C) (he : computes p C)
    (least : ∀ D : Circuit, FanInTwo D → computes p D → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) (a : ℕ) :
    C.gates[j].inputs ≠ [a,a] := by
  intro equal
  have early := norm.2 j hj a (by rw [equal]; simp)
  have sameWire (x : Fin 8 → Bool) : wire C x (8+j) = wire C x a := by
    rw [gate C norm j hj x,equal]
    rcases shape C norm j hj with ⟨_,b,bb,_⟩ | ⟨k,_⟩
    · rw [equal] at bb
      simp at bb
    · rcases k with h | h <;> rw [h] <;> simp [GateOp.eval]
  let X := fun x : Fin 8 → Bool => List.ofFn x
  have hin (i : ℕ) (hi : i<8) : (∃ c, ∀ x, (X x).getD i false = c) ∨
      ∃ k<8, ∀ x, (X x).getD i false = (List.ofFn x).getD k false :=
    Or.inr ⟨i,hi,fun _ => rfl⟩
  have hd (i : ℕ) (hi : i ∈ ({j} : Finset ℕ)) : i < C.gates.length ∧
      Drop 8 (fun w x => (C.wires (X x)).getD w false) i := by
    have ij : i=j := by simpa using hi
    subst i
    exact ⟨hj,Or.inr ⟨a,early,sameWire⟩⟩
  obtain ⟨D,fan,sz,correct⟩ := many_drops 8 8 C X (normal_fan C norm)
    (by simp [X]) hin (nonconstant p C he) {j} hd
  have minimal := least D fan (fun x => (correct x).trans (he x))
  simp at sz
  omega

def pinFalse (p : Fin 8) (x : Fin 8 → Bool) (i : Fin 8) : Bool :=
  if i=p then false else x i

private theorem family_pin (p : Fin 8) (x : Fin 8 → Bool) :
    family 8 (pinFalse p x) = family (Fin.castSucc p) x := by
  rw [all_free]
  unfold pinFalse family
  congr 1
  funext i
  simp only [Fin.val_castSucc]
  by_cases eq : i=p
  · simp [eq]
  · have ne : i.val ≠ p.val := fun equal => eq (Fin.ext equal)
    rw [ite_eq_right eq,ite_eq_right ne]

private theorem reader_drop (C : Circuit) (norm : Normal 8 C) (p : Fin 8) (j : ℕ)
    (hj : j<C.gates.length) (read : p.val ∈ C.gates[j].inputs) :
    Drop 8 (fun w x => wire C (pinFalse p x) w) j := by
  have off (x : Fin 8 → Bool) : wire C (pinFalse p x) p.val = false := by
    unfold wire
    change (run C.gates (List.ofFn (pinFalse p x))).getD p.val false = false
    rw [run_input _ _ _ (by simp),ofFn_get]
    simp [pinFalse]
  rcases shape C norm j hj with ⟨op,a,ports,ha⟩ | ⟨op,a,b,ports,ha,hb⟩
  · have ea : a=p.val := by rw [ports] at read; simpa [eq_comm] using read
    exact Or.inl ⟨true,fun x => by
      change wire C (pinFalse p x) (8+j) = true
      rw [gate C norm j hj,op,ports,ea]
      simp [GateOp.eval,off]⟩
  · rw [ports] at read
    have hits : p.val=a ∨ p.val=b := by simpa using read
    rcases op with kind | kind
    · exact Or.inl ⟨false,fun x => by
        change wire C (pinFalse p x) (8+j) = false
        rw [gate C norm j hj,kind,ports]
        rcases hits with rfl | rfl <;> simp [GateOp.eval,off]⟩
    · rcases hits with rfl | rfl
      · exact Or.inr ⟨b,hb,fun x => by
          change wire C (pinFalse p x) (8+j) = wire C (pinFalse p x) b
          rw [gate C norm j hj,kind,ports]
          simp [GateOp.eval,off]⟩
      · exact Or.inr ⟨a,ha,fun x => by
          change wire C (pinFalse p x) (8+j) = wire C (pinFalse p x) a
          rw [gate C norm j hj,kind,ports]
          simp [GateOp.eval,off]⟩

theorem two_readers_drop (C : Circuit) (norm : Normal 8 C) (he : computes 8 C)
    (p : Fin 8) (j k : ℕ) (jne : j ≠ k) (hj : j<C.gates.length) (hk : k<C.gates.length)
    (J : p.val ∈ C.gates[j].inputs) (K : p.val ∈ C.gates[k].inputs) :
    ∃ D : Circuit, FanInTwo D ∧ D.size+2 ≤ C.size ∧ computes (Fin.castSucc p) D := by
  let X := fun x : Fin 8 → Bool => List.ofFn (pinFalse p x)
  have hx (i : Fin 8) (x : Fin 8 → Bool) :
      (X x).getD i.val false = if i=p then false else x i := ofFn_get _ i
  have hin (i : ℕ) (hi : i<8) : (∃ c, ∀ x, (X x).getD i false = c) ∨
      ∃ k<8, ∀ x, (X x).getD i false = (List.ofFn x).getD k false := by
    let a : Fin 8 := ⟨i,hi⟩
    by_cases e : a=p
    · exact Or.inl ⟨false,fun x => by rw [← show a.val=i from rfl,hx,ite_eq_left e]⟩
    · exact Or.inr ⟨i,hi,fun x => by rw [← show a.val=i from rfl,hx,ite_eq_right e,ofFn_get]⟩
  have exactX (x : Fin 8 → Bool) : C.eval (X x) = family (Fin.castSucc p) x :=
    (he (pinFalse p x)).trans (family_pin p x)
  have nc : ¬ ∃ c, ∀ x, C.eval (X x) = c := by
    have differs : ∀ p : Fin 9, family p (fun _ => false) ≠ family p (fun _ => true) := by
      decide +kernel
    rintro ⟨c,h⟩
    exact differs (Fin.castSucc p) ((exactX _).symm.trans ((h _).trans ((h _).symm.trans (exactX _))))
  have hd (i : ℕ) (hi : i ∈ ({j,k}:Finset ℕ)) : i<C.gates.length ∧
      Drop 8 (fun w x => (C.wires (X x)).getD w false) i := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with h | h
    · subst i
      exact ⟨hj,reader_drop C norm p j hj J⟩
    · subst i
      exact ⟨hk,reader_drop C norm p k hk K⟩
  obtain ⟨D,fan,sz,ev⟩ := many_drops 8 8 C X (normal_fan C norm) (by simp [X]) hin nc {j,k} hd
  exact ⟨D,fan,by simpa [jne] using sz,fun x => (ev x).trans (exactX x)⟩

end Hard27797GateTools

namespace Hard27797Head

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction
open Hard27797Probes Hard27797CircuitCounts

private theorem snoc_getD (x : Fin 8 → Bool) (v : Bool) (i : ℕ) :
    (List.ofFn x ++ [v]).getD i false =
      if h : i<8 then x ⟨i,h⟩ else if i=8 then v else false := by
  split
  · rename_i h
    rw [getD_lt _ _ _ (by simpa using h)]
    exact ofFn_get _ ⟨i,h⟩
  · rename_i h
    split
    · rename_i e
      subst i
      simpa using getD_at (List.ofFn x) v
    · rw [List.getD_eq_default _ _ (by simp; omega)]

private theorem at_most_once_tail (C : Circuit) (g : Gate) (gs : List Gate)
    (h : C.gates=g::gs) (i : ℕ) (used : i ∈ g.inputs)
    (once : (C.gates.flatMap Gate.inputs).count i ≤ 1) :
    ∀ d ∈ gs, i ∉ d.inputs := by
  intro d hd read
  have h1 := List.count_pos_iff.mpr used
  have h2 := List.count_pos_iff.mpr (List.mem_flatMap.mpr ⟨d,hd,read⟩)
  have total : (C.gates.flatMap Gate.inputs).count i =
      g.inputs.count i + (gs.flatMap Gate.inputs).count i := by
    rw [h,List.flatMap_cons,List.count_append]
  omega

theorem binary (p : Fin 9) (C : Circuit) (he : computes p C) (out : 8 ≤ C.output)
    (op : GateOp) (gs : List Gate) (a b : Fin 8) (ab : a ≠ b)
    (ha : a.val ≠ p.val) (hb : b.val ≠ p.val)
    (hd : C.gates = ⟨op,[a.val,b.val]⟩ :: gs)
    (oa : (C.gates.flatMap Gate.inputs).count a.val ≤ 1)
    (ob : (C.gates.flatMap Gate.inputs).count b.val ≤ 1) : False := by
  let signal (x : Fin 8 → Bool) := op.eval [x a,x b]
  apply no_pair p a b ab ha hb signal
  · intro x y ha hb
    simp [signal,ha,hb]
  · intro x y close sign
    have tails (x : Fin 8 → Bool) : C.eval (List.ofFn x) =
        (run gs (List.ofFn x ++ [signal x])).getD C.output false := by
      change (run C.gates (List.ofFn x)).getD C.output false = _
      rw [hd]
      change (run gs (List.ofFn x ++ [op.eval
        [(List.ofFn x).getD a.val false,(List.ofFn x).getD b.val false]])).getD C.output false = _
      rw [ofFn_get,ofFn_get]
    let hidden : Finset ℕ := {a.val,b.val}
    have start (i : ℕ) (allowed : i ∉ hidden) :
        (List.ofFn x ++ [signal x]).getD i false =
        (List.ofFn y ++ [signal y]).getD i false := by
      rw [snoc_getD,snoc_getD,sign]
      split
      · rename_i ih
        let j : Fin 8 := ⟨i,ih⟩
        exact close j (by intro e; apply allowed; simp [hidden,←e,j])
          (by intro e; apply allowed; simp [hidden,←e,j])
      · rfl
    have avoid (g : Gate) (hg : g ∈ gs) (i : ℕ) (hi : i ∈ g.inputs) : i ∉ hidden := by
      intro inside
      simp only [hidden,Finset.mem_insert,Finset.mem_singleton] at inside
      rcases inside with rfl | rfl
      · exact at_most_once_tail C _ gs hd _ (by simp) oa g hg hi
      · exact at_most_once_tail C _ gs hd _ (by simp) ob g hg hi
    have on : C.output ∉ hidden := by
      have := a.isLt
      have := b.isLt
      simp only [hidden,Finset.mem_insert,Finset.mem_singleton,not_or]
      omega
    rw [← he x,← he y,tails,tails]
    exact agree hidden gs _ _ (by simp) start avoid C.output on

private theorem list_eval_mono (op : GateOp) (p : op = .and ∨ op = .or)
    (is : List ℕ) (a b : ℕ → Bool)
    (pointwise : ∀ i ∈ is, a i = true → b i = true) :
    op.eval (is.map a) = true → op.eval (is.map b) = true := by
  rcases p with rfl | rfl
  · simp only [GateOp.eval,List.all_eq_true]
    intro h bit member
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
    exact pointwise i hi (h _ (List.mem_map.mpr ⟨i,hi,rfl⟩))
  · simp only [GateOp.eval,List.any_eq_true,List.mem_map]
    rintro ⟨v,⟨i,hi,rfl⟩,h⟩
    exact ⟨b i,⟨i,hi,rfl⟩,pointwise i hi h⟩

private theorem run_mono_away (gs : List Gate) (skip : ℕ) (a b : List Bool)
    (len : a.length = b.length)
    (start : ∀ i, i ≠ skip → a.getD i false = true → b.getD i false = true)
    (allowed : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ skip ∉ g.inputs) :
    ∀ i, i ≠ skip → (run gs a).getD i false = true → (run gs b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact start
  | cons g gs ih =>
    let va := g.op.eval (g.inputs.map fun i => a.getD i false)
    let vb := g.op.eval (g.inputs.map fun i => b.getD i false)
    have here := allowed g (by simp)
    have v := list_eval_mono g.op here.1 g.inputs _ _
      (fun i hi => start i fun same => here.2 (same ▸ hi))
    change ∀ i, i ≠ skip → (run gs (a++[va])).getD i false = true →
      (run gs (b++[vb])).getD i false = true
    apply ih _ _ (by simp [len]) _ (fun d hd => allowed d (List.mem_cons_of_mem _ hd))
    intro i hs
    by_cases prev : i < a.length
    · rw [getD_lt _ _ _ prev,getD_lt _ _ _ (by omega)]
      exact start i hs
    · by_cases same : i=a.length
      · subst i
        rw [getD_at,len,getD_at]
        exact v
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
        exact id

theorem first_not (C : Circuit) (he : computes 8 C) (out : 8 ≤ C.output)
    (a : Fin 8) (gs : List Gate) (hd : C.gates = ⟨.not,[a.val]⟩ :: gs)
    (once : (C.gates.flatMap Gate.inputs).count a.val ≤ 1)
    (positive : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) : False := by
  obtain ⟨x,y,close,hx,hy,no,yes⟩ := oriented_pivots a
  have split (z : Fin 8 → Bool) : C.eval (List.ofFn z) =
      (run gs (List.ofFn z ++ [!z a])).getD C.output false := by
    change (run C.gates (List.ofFn z)).getD C.output false = _
    rw [hd]
    change (run gs (List.ofFn z ++ [!(List.ofFn z).getD a.val false])).getD C.output false = _
    rw [ofFn_get]
  have allow (g : Gate) (hg : g ∈ gs) : (g.op = .and ∨ g.op = .or) ∧ a.val ∉ g.inputs :=
    ⟨positive g hg,at_most_once_tail C _ gs hd _ (by simp) once g hg⟩
  have initial (i : ℕ) (off : i ≠ a.val) :
      (List.ofFn y ++ [!y a]).getD i false = true →
      (List.ofFn x ++ [!x a]).getD i false = true := by
    rw [snoc_getD,snoc_getD]
    split
    · rename_i h
      let j : Fin 8 := ⟨i,h⟩
      rw [show y j = x j from (close j (by intro e; exact off (congrArg Fin.val e))).symm]
      exact id
    · split <;> simp [hx,hy]
  have small := a.isLt
  have contra := run_mono_away gs a.val _ _ (by simp) initial allow C.output (by omega)
  rw [← split y,← split x,he y,he x,yes,no] at contra
  exact Bool.false_ne_true (contra rfl)

end Hard27797Head

namespace Hard27797ResidualFloor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Hard27797Ports Hard27797CircuitCounts Hard27797GateTools

private theorem no_not (gs : List Gate) (h : notCount gs = 0) :
    ∀ g ∈ gs, g.op ≠ .not := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    by_cases neg : g.op = .not
    · cases op : g.op <;> simp [notCount,List.countP_cons,isNot,op] at h neg
    · have rest : notCount gs = 0 := by
        cases op : g.op <;> simp_all [notCount,List.countP_cons,isNot]
      intro d hd
      rcases List.mem_cons.mp hd with rfl | other
      · exact neg
      · exact ih rest d other

private theorem no_inverter_head_rest (gs : List Gate) (a : ℕ)
    (cap : notCount (⟨GateOp.not,[a]⟩::gs) ≤ 1) : notCount gs = 0 := by
  rw [notCount,List.countP_cons] at cap
  change List.countP isNot gs + 1 ≤ 1 at cap
  unfold notCount
  omega

private theorem shape_head (C : Circuit) (norm : Normal 8 C) (g : Gate) (gs : List Gate)
    (hd : C.gates=g::gs) : ProperGate 8 g := by
  have h0 : 0 < C.gates.length := by simp [hd]
  have e : C.gates[0] = g := by simp [hd]
  have ch := shape C norm 0 h0
  rwa [e] at ch

private theorem no_duplicate_head (p : Fin 9) (C : Circuit) (norm : Normal 8 C)
    (he : computes p C) (least : ∀ D : Circuit, FanInTwo D → computes p D → C.size ≤ D.size)
    (g : Gate) (gs : List Gate) (hd : C.gates=g::gs) (a : ℕ) :
    g.inputs ≠ [a,a] := by
  have h0 : 0 < C.gates.length := by simp [hd]
  have e : C.gates[0] = g := by simp [hd]
  have h := no_duplicate p C norm he least 0 h0 a
  rwa [e] at h

private theorem repeat_two_gates (gs : List Gate) (a : ℕ)
    (per : ∀ g ∈ gs, g.inputs.count a ≤ 1)
    (twice : 2 ≤ (gs.flatMap Gate.inputs).count a) :
    ∃ (j k : Fin gs.length), j ≠ k ∧ a ∈ (gs.get j).inputs ∧ a ∈ (gs.get k).inputs := by
  induction gs with
  | nil => simp at twice
  | cons g gs ih =>
    have head := per g (by simp)
    have basic : 2 ≤ g.inputs.count a + (gs.flatMap Gate.inputs).count a := by
      simpa only [List.flatMap_cons,List.count_append] using twice
    by_cases used : a ∈ g.inputs
    · have tailPos : 0 < (gs.flatMap Gate.inputs).count a := by omega
      obtain ⟨d,mem,hit⟩ := List.mem_flatMap.mp (List.count_pos_iff.mp tailPos)
      obtain ⟨k,eq⟩ := List.get_of_mem mem
      refine ⟨⟨0,by simp⟩,k.succ,by intro e; have := congrArg Fin.val e; simp at this,used,?_⟩
      change a ∈ (gs.get k).inputs
      rwa [eq]
    · have zero : g.inputs.count a = 0 := List.count_eq_zero_of_not_mem used
      obtain ⟨j,k,ne,hj,hk⟩ := ih (fun d mem => per d (List.mem_cons_of_mem _ mem)) (by omega)
      exact ⟨j.succ,k.succ,fun eq => ne (Fin.succ_injective _ eq),hj,hk⟩

private theorem per_gate (p : Fin 9) (C : Circuit) (norm : Normal 8 C)
    (he : computes p C) (least : ∀ D : Circuit, FanInTwo D → computes p D → C.size ≤ D.size)
    (a : ℕ) : ∀ g ∈ C.gates, g.inputs.count a ≤ 1 := by
  intro g mem
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem mem
  rcases shape C norm j hj with ⟨_,u,ar,_⟩ | ⟨_,u,v,ar,_,_⟩
  · rw [ar]
    exact List.nodup_iff_count_le_one.mp (by simp : [u].Nodup) a
  · have ne : u ≠ v := by
      rintro rfl
      exact no_duplicate p C norm he least j hj u ar
    rw [ar]
    exact List.nodup_iff_count_le_one.mp (by simp [ne] : [u,v].Nodup) a

private theorem free_at_most_one_not (C : Circuit) (norm : Normal 8 C)
    (he : computes 8 C) (cap : C.size ≤ 8) (hl : C.output+1 = 8+C.gates.length)
    (live : Live C) :
    notCount C.gates ≤ 1 := by
  have low := support_lower 8 C norm he hl live
  have subset := (ports C.gates).toFinset_card_le
  have total := port_length C norm
  have sum := branching_not_budget C.gates
  have out := computed_output 8 C he
  simp at low
  unfold Circuit.size at cap
  omega

private theorem pinned_six (p : Fin 8) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ computes (Fin.castSucc p) C := by
  intro given
  let q := Fin.castSucc p
  obtain ⟨C,norm,cap,he,inside,live,least⟩ := normalize_least q 6 given
  have out := computed_output q C he
  have hl := last C inside out norm live
  have qp : q.val < 8 := p.isLt
  have support := support_lower q C norm he hl live
  simp only [qp,ite_true] at support
  have erase := Finset.card_erase_le (s := (ports C.gates).toFinset) (a := q.val)
  have subset := (ports C.gates).toFinset_card_le
  have total := port_length C norm
  have sum := branching_not_budget C.gates
  unfold Circuit.size at cap
  have hnot : notCount C.gates = 0 := by omega
  have tight : ((ports C.gates).toFinset.erase q.val).card = (ports C.gates).length := by omega
  have never : q.val ∉ ports C.gates := by
    intro m
    have next := Finset.card_erase_add_one (List.mem_toFinset.mpr m)
    omega
  have equality : (ports C.gates).toFinset.card = (ports C.gates).length := by omega
  have unique : (ports C.gates).Nodup := by
    exact (Multiset.toFinset_card_eq_card_iff_nodup (m := (ports C.gates : Multiset ℕ))).mp equality
  have nonempty : C.gates ≠ [] := by intro e; simp [e] at inside; omega
  obtain ⟨g,gs,hd⟩ := List.exists_cons_of_ne_nil nonempty
  have mem : g ∈ C.gates := by rw [hd]; simp
  rcases shape_head C norm g gs hd with ⟨op,a,ar,ha⟩ | ⟨_,a,b,ar,ha,hb⟩
  · exact no_not C.gates hnot g mem op
  · let A : Fin 8 := ⟨a,ha⟩
    let B : Fin 8 := ⟨b,hb⟩
    have diff : A ≠ B := by
      intro eq
      have same : a=b := congrArg Fin.val eq
      exact no_duplicate_head q C norm he least g gs hd a (by simpa [same] using ar)
    have hGate : g = ⟨g.op,[a,b]⟩ := by cases g; simp_all
    have prog : C.gates = ⟨g.op,[A.val,B.val]⟩ :: gs := hd.trans (congrArg (·::gs) hGate)
    have rawOnce (i : Fin 8) : (C.gates.flatMap Gate.inputs).count i.val ≤ 1 := by
      rw [← actual_ports C norm]
      exact List.nodup_iff_count_le_one.mp unique i.val
    have unpinned (i : ℕ) (h : i ∈ g.inputs) : i ≠ q.val := by
      intro same
      apply never
      rw [actual_ports C norm]
      exact List.mem_flatMap.mpr ⟨g,mem,same ▸ h⟩
    exact Hard27797Head.binary q C he out g.op gs A B diff
      (unpinned a (by simp [ar])) (unpinned b (by simp [ar])) prog (rawOnce A) (rawOnce B)

theorem free_eight : ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ computes 8 C := by
  intro given
  obtain ⟨C,norm,cap,he,inside,live,least⟩ := normalize_least 8 8 given
  have out := computed_output 8 C he
  have hl := last C inside out norm live
  by_cases once : ∀ a : Fin 8, (C.gates.flatMap Gate.inputs).count a.val ≤ 1
  · have nonempty : C.gates ≠ [] := by intro e; simp [e] at inside; omega
    obtain ⟨g,gs,hd⟩ := List.exists_cons_of_ne_nil nonempty
    rcases shape_head C norm g gs hd with ⟨op,a,ar,ha⟩ | ⟨_,a,b,ar,ha,hb⟩
    · let A : Fin 8 := ⟨a,ha⟩
      have hGate : g = ⟨.not,[a]⟩ := by cases g; simp_all
      have prog : C.gates = ⟨.not,[A.val]⟩::gs := hd.trans (congrArg (·::gs) hGate)
      have one := free_at_most_one_not C norm he cap hl live
      rw [prog] at one
      have no := no_inverter_head_rest gs a one
      apply Hard27797Head.first_not C he out A gs prog (once A)
      intro d hd'
      rcases norm.1 d (by rw [hd]; exact List.mem_cons_of_mem _ hd') with h | h
      · exact (no_not gs no d hd' h.1).elim
      · exact h.1
    · let A : Fin 8 := ⟨a,ha⟩
      let B : Fin 8 := ⟨b,hb⟩
      have diff : A ≠ B := by
        intro eq
        have same : a=b := congrArg Fin.val eq
        exact no_duplicate_head 8 C norm he least g gs hd a (by simpa [same] using ar)
      have hGate : g = ⟨g.op,[a,b]⟩ := by cases g; simp_all
      have prog : C.gates = ⟨g.op,[A.val,B.val]⟩::gs := hd.trans (congrArg (·::gs) hGate)
      apply Hard27797Head.binary 8 C he out g.op gs A B diff _ _ prog (once A) (once B)
      · change a ≠ 8; omega
      · change b ≠ 8; omega
  · push Not at once
    obtain ⟨a,many⟩ := once
    obtain ⟨j,k,ne,J,K⟩ := repeat_two_gates C.gates a.val
      (per_gate 8 C norm he least a.val) (by omega)
    have different : j.val ≠ k.val := fun e => ne (Fin.ext e)
    obtain ⟨D,legal,size,correct⟩ := two_readers_drop C norm he a j.val k.val
      different j.isLt k.isLt J K
    exact pinned_six a ⟨D,legal,by omega,correct⟩

end Hard27797ResidualFloor

namespace Hard27797Exact

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Hard27797PrefixDrops

theorem impossible (C : Circuit) (fan : FanInTwo C) (cap : C.size ≤ 12)
    (correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x)
    (last : C.output+1 = 9+C.size) (shape : shaped C) (new : fresh C)
    (live : ∀ j : Fin C.gates.length, j.val+1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs)
    (first : C.gates.head? = some gate0) (second : C.gates.tail.head? = some gate1) :
    False := by
  obtain ⟨a,as,h⟩ := List.exists_cons_of_ne_nil (l := C.gates) (by intro e; simp [e] at first)
  have a_eq : a = gate0 := by simpa [h] using first
  have hd : as.head? = some gate1 := by simpa [h] using second
  obtain ⟨b,bs,hb⟩ := List.exists_cons_of_ne_nil (l := as) (by intro e; simp [e] at hd)
  have b_eq : b = gate1 := by simpa [hb] using hd
  have pr : C.gates = gate0::gate1::bs := by rw [h,a_eq,hb,b_eq]
  obtain ⟨D,allowed,size,eval⟩ := drop_to_eight C bs pr fan cap last shape new live correct
  exact Hard27797ResidualFloor.free_eight ⟨D,allowed,size,fun x =>
    (eval x).trans (Hard27797Probes.all_free x).symm⟩

end Hard27797Exact

end PEqualNP.Outside.L_meta_27797_aux

theorem PEqualNP.Outside.L_meta_27797 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩)) := by
  rintro ⟨C,fan,cap,correct,last,shape,fresh,live,first,second⟩
  exact PEqualNP.Outside.L_meta_27797_aux.Hard27797Exact.impossible C fan cap correct last shape
    (fun j => (fresh j).2) live first second
