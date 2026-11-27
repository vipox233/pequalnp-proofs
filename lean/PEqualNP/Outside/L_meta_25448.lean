import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25448

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The evaluator argument uses the same snoc decomposition as L-meta-8115.
private def trace (gs : List Gate) (x : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires x

private theorem trace_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    trace (gs ++ [g]) x = trace gs x ++ [g.op.eval (g.inputs.map fun i => (trace gs x).getD i false)] := by
  simp [trace, Circuit.wires, List.foldl_append]

private theorem trace_length (gs : List Gate) (x : List Bool) :
    (trace gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [trace, Circuit.wires]
  | append_singleton gs g ih => rw [trace_snoc]; simp [ih]; omega

private theorem trace_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (trace (gs ++ hs) x).getD i false = (trace gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    have h : i < (trace (gs ++ hs) x).length := by
      rw [trace_length, List.length_append]; omega
    rw [← List.append_assoc, trace_snoc]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left h] using ih

private theorem trace_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (trace gs x).getD i false = x.getD i false := by
  simpa [trace, Circuit.wires] using trace_prefix [] gs x i (by simpa using hi)

private theorem trace_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (trace gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (trace gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton gs g ih =>
    have hlen : (trace gs x).length = x.length + gs.length := trace_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (trace (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (trace gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact trace_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), trace_prefix gs [g] x _ (by omega)]
      exact ih h
    · have hjj : j = gs.length := by simp at hj; omega
      subst j
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, trace_snoc, ← hlen]
      have hget (z : Bool) : ((trace gs x) ++ [z]).getD (trace gs x).length false = z := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

private def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates[j]?.getD ⟨.and, []⟩

private abbrev isOr (C : Circuit) (j : ℕ) : Prop :=
  (match (gateAt C j).op with | .or => true | _ => false) = true

private theorem isOr_iff (C : Circuit) (j : ℕ) : isOr C j ↔ (gateAt C j).op = .or := by
  unfold isOr
  cases (gateAt C j).op <;> simp

private theorem gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.size) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getElem?_eq_getElem hj]

private theorem isOr_lt (C : Circuit) (j : ℕ) (h : isOr C j) : j < C.size := by
  by_contra hj
  have hg : C.gates[j]? = none := List.getElem?_eq_none (by simpa [Circuit.size] using hj)
  have hor := (isOr_iff C j).1 h
  simp [gateAt, hg] at hor

-- In the auxiliary numbering, wire zero is always false.
private def wire (C : Circuit) (x : List Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => (C.wires x).getD i false

private def predecessor (d j : ℕ) (C : Circuit) (p : Bool) : ℕ :=
  match (gateAt C j).inputs[if p then 1 else 0]? with
  | none => 0
  | some k => if k < d+j then k+1 else 0

private theorem predecessor_lt (d j : ℕ) (C : Circuit) (p : Bool) :
    predecessor d j C p < d+1+j := by
  unfold predecessor
  split
  · omega
  · split <;> omega

private def leftBase (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => u.val + 1 = w

private def rightBase (n m : ℕ) (w : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun v => n + v.val + 1 = w

private theorem mem_leftBase {n w : ℕ} {u : Fin n} : u ∈ leftBase n w ↔ u.val + 1 = w := by
  simp [leftBase]

private theorem mem_rightBase {n m w : ℕ} {v : Fin m} : v ∈ rightBase n m w ↔ n + v.val + 1 = w := by
  simp [rightBase]

private theorem leftBase_card (n w : ℕ) : (leftBase n w).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  rw [mem_leftBase] at ha hb
  exact Fin.ext (by omega)

private theorem rightBase_card (n m w : ℕ) : (rightBase n m w).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  rw [mem_rightBase] at ha hb
  exact Fin.ext (by omega)

private theorem promise_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n+m := by
  simp [oneEach]

private theorem wire_input {n m : ℕ} (C : Circuit) (u : Fin n) (v : Fin m) (w : ℕ)
    (hw : w < n+m+1) :
    wire C (oneEach u v) w = true ↔ u ∈ leftBase n w ∨ v ∈ rightBase n m w := by
  rw [mem_leftBase, mem_rightBase]
  cases w with
  | zero => simp [wire]
  | succ i =>
    change (trace C.gates (oneEach u v)).getD i false = true ↔ _
    rw [trace_input _ _ _ (by rw [promise_length]; omega)]
    simp only [oneEach, List.getD_eq_getElem?_getD]
    by_cases hi : i < n
    · rw [List.getElem?_append_left (by simpa using hi)]
      simp only [List.getElem?_ofFn, dite_eq_left hi, Option.getD_some, decide_eq_true_eq, Nat.succ.injEq]
      have hv : ¬ n + v.val = i := by omega
      simp [hv, Fin.ext_iff, eq_comm]
    · rw [List.getElem?_append_right (by simpa using hi)]
      simp only [List.length_ofFn]
      have him : i - n < m := by omega
      simp only [List.getElem?_ofFn, dite_eq_left him, Option.getD_some, decide_eq_true_eq, Nat.succ.injEq]
      have hu : ¬ u.val = i := by have := u.isLt; omega
      rw [or_iff_right hu, Fin.ext_iff]
      change i - n = v.val ↔ n + v.val = i
      omega

private theorem list_cases2 {α : Type} (l : List α) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ (∃ a b, l = [a,b]) := by
  cases l with
  | nil => exact Or.inl rfl
  | cons a t =>
    cases t with
    | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
    | cons b t =>
      cases t with
      | nil => exact Or.inr (Or.inr ⟨a,b,rfl⟩)
      | cons c t => simp at h

private theorem wire_read (C : Circuit) (x : List Bool) (k d j : ℕ) :
    (if k < d+j then (trace C.gates x).getD k false else false) =
      wire C x (if k < d+j then k+1 else 0) := by
  split <;> rfl

private theorem wire_value (C : Circuit) (x : List Bool) (d j : ℕ)
    (hx : x.length = d) (hj : j < C.size) :
    wire C x (d+1+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun k =>
      wire C x (if k < d+j then k+1 else 0)) := by
  rw [gateAt_get C j hj, show d+1+j = (d+j)+1 by omega]
  change (trace C.gates x).getD (d+j) false = _
  nth_rw 1 [← hx]
  rw [trace_gate C.gates x j hj, hx]
  congr 1
  exact List.map_congr_left fun k _ => wire_read C x k d j

private theorem gateLength (C : Circuit) (mono : Monotone2 C) (j : ℕ) (hj : j < C.size) :
    (gateAt C j).inputs.length ≤ 2 := by
  rw [gateAt_get C j hj]
  exact (mono _ (List.getElem_mem hj)).2

private theorem gateOp (C : Circuit) (mono : Monotone2 C) (j : ℕ) (hj : j < C.size) :
    (gateAt C j).op = .and ∨ isOr C j := by
  rw [isOr_iff, gateAt_get C j hj]
  simpa using (mono _ (List.getElem_mem hj)).1

private theorem wire_or (C : Circuit) (x : List Bool) (d j : ℕ)
    (hx : x.length = d) (hj : j < C.size) (len : (gateAt C j).inputs.length ≤ 2) (ho : isOr C j) :
    wire C x (d+1+j) = (wire C x (predecessor d j C false) || wire C x (predecessor d j C true)) := by
  rw [wire_value C x d j hx hj, (isOr_iff C j).1 ho]
  rcases list_cases2 _ len with h | ⟨a,h⟩ | ⟨a,b,h⟩ <;>
    simp [predecessor, h, GateOp.eval, wire]

private theorem wire_and_null (C : Circuit) (x : List Bool) (d j : ℕ)
    (hx : x.length = d) (hj : j < C.size) (ho : (gateAt C j).op = .and)
    (h : (gateAt C j).inputs = []) : wire C x (d+1+j) = true := by
  simp [wire_value C x d j hx hj, ho, h, GateOp.eval]

private theorem wire_and_unary (C : Circuit) (x : List Bool) (d j : ℕ)
    (hx : x.length = d) (hj : j < C.size) (ho : (gateAt C j).op = .and) {a : ℕ}
    (h : (gateAt C j).inputs = [a]) :
    wire C x (d+1+j) = wire C x (predecessor d j C false) := by
  simp [wire_value C x d j hx hj, ho, h, GateOp.eval, predecessor]

private theorem wire_and_binary (C : Circuit) (x : List Bool) (d j : ℕ)
    (hx : x.length = d) (hj : j < C.size) (ho : (gateAt C j).op = .and) {a b : ℕ}
    (h : (gateAt C j).inputs = [a,b]) :
    wire C x (d+1+j) = (wire C x (predecessor d j C false) && wire C x (predecessor d j C true)) := by
  simp [wire_value C x d j hx hj, ho, h, GateOp.eval, predecessor]

private def frontier {α : Type} [DecidableEq α] (base : ℕ → Finset α)
    (C : Circuit) (d : ℕ) (w : ℕ) : Finset α := by
  exact if hw : w < d+1 then base w
    else
      let j := w-(d+1)
      if isOr C j then
        have h₀ : predecessor d j C false < w := by
          have := predecessor_lt d j C false; dsimp [j] at *; omega
        have h₁ : predecessor d j C true < w := by
          have := predecessor_lt d j C true; dsimp [j] at *; omega
        frontier base C d (predecessor d j C false) ∪ frontier base C d (predecessor d j C true)
      else ∅
termination_by w

private theorem frontier_input {α : Type} [DecidableEq α] (base : ℕ → Finset α)
    (C : Circuit) (d w : ℕ) (hw : w < d+1) : frontier base C d w = base w := by
  rw [frontier]; simp [hw]

private theorem frontier_gate {α : Type} [DecidableEq α] (base : ℕ → Finset α)
    (C : Circuit) (d j : ℕ) :
    frontier base C d (d+1+j) = if isOr C j then
      frontier base C d (predecessor d j C false) ∪ frontier base C d (predecessor d j C true)
      else ∅ := by
  classical
  rw [frontier]
  have h₁ : ¬ (d+1+j < d+1) := by omega
  have h₂ : d+1+j-(d+1)=j := by omega
  simp only [h₁, dite_false, h₂]

private abbrev L (n m : ℕ) (C : Circuit) := frontier (leftBase n) C (n+m)
private abbrev R (n m : ℕ) (C : Circuit) := frontier (rightBase n m) C (n+m)

private theorem frontierEval {n m : ℕ} (C : Circuit) (mono : Monotone2 C) (u : Fin n) (v : Fin m) :
    ∀ w : ℕ, (u ∈ L n m C w ∨ v ∈ R n m C w → wire C (oneEach u v) w = true) ∧
      ((∀ j < C.size, n+m+1+j ≤ w → (gateAt C j).op = .and →
        wire C (oneEach u v) (n+m+1+j) = false) → wire C (oneEach u v) w = true →
        u ∈ L n m C w ∨ v ∈ R n m C w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n+m+1
    · have e := wire_input C u v w hin
      rw [show L n m C w = leftBase n w from frontier_input _ _ _ _ hin,
        show R n m C w = rightBase n m w from frontier_input _ _ _ _ hin]
      exact ⟨e.mpr, fun _ => e.mp⟩
    let j := w-(n+m+1)
    have hw : w=n+m+1+j := by dsimp [j]; omega
    have eL := frontier_gate (leftBase n) C (n+m) j
    have eR := frontier_gate (rightBase n m) C (n+m) j
    rw [hw]
    change (u ∈ frontier (leftBase n) C (n+m) (n+m+1+j) ∨
      v ∈ frontier (rightBase n m) C (n+m) (n+m+1+j) → _) ∧ _
    by_cases hOr : isOr C j
    · rw [ite_eq_left hOr] at eL eR
      by_cases hj : j < C.size
      · have e := wire_or C (oneEach u v) (n+m) j (promise_length u v) hj (gateLength C mono j hj) hOr
        have a := ih (predecessor (n+m) j C false) (by rw [hw]; exact predecessor_lt _ _ _ _)
        have b := ih (predecessor (n+m) j C true) (by rw [hw]; exact predecessor_lt _ _ _ _)
        have ha : ∀ k, n+m+1+k ≤ predecessor (n+m) j C false → n+m+1+k ≤ n+m+1+j :=
          fun k hk => hk.trans (predecessor_lt _ _ _ _).le
        have hb : ∀ k, n+m+1+k ≤ predecessor (n+m) j C true → n+m+1+k ≤ n+m+1+j :=
          fun k hk => hk.trans (predecessor_lt _ _ _ _).le
        simp only [L, R, eL, eR, Finset.mem_union, e, Bool.or_eq_true] at *
        exact ⟨by tauto, fun hc hv => by
          rcases hv with hv | hv
          · have := a.2 (fun k hk hp => hc k hk (ha k hp)) hv
            tauto
          · have := b.2 (fun k hk hp => hc k hk (hb k hp)) hv
            tauto⟩
      · have hg : C.gates[j]? = none := List.getElem?_eq_none (by simpa [Circuit.size] using hj)
        have : (gateAt C j).op = .and := by simp [gateAt, hg]
        simp [isOr_iff, this] at hOr
    · rw [ite_eq_right hOr] at eL eR
      simp only [L, R, eL, eR, Finset.notMem_empty, false_or]
      refine ⟨False.elim, fun hc hv => ?_⟩
      by_cases hj : j < C.size
      · have hop := (gateOp C mono j hj).resolve_right hOr
        rw [hc j hj le_rfl hop] at hv
        contradiction
      · have len := trace_length C.gates (oneEach u v)
        rw [promise_length] at len
        rw [show n+m+1+j=n+m+j+1 by omega] at hv
        change (trace C.gates (oneEach u v)).getD (n+m+j) false = true at hv
        rw [List.getD_eq_default _ _ (by unfold Circuit.size at hj; omega)] at hv
        contradiction

/-- Charge each covered edge to one of the two slots of one gate. A large
support descends to a singleton child of an OR, whose support identifies
its center by the no-rectangle hypothesis. -/
private theorem card_le_two_mul {n m : ℕ} (E : Finset (Fin n × Fin m))
    (A : Fin n → Fin m → Prop)
    (hC4 : ∀ ⦃u u' v v'⦄, v ≠ v' → A u v → A u v' → A u' v → A u' v' → u = u')
    (N s : ℕ) (S : ℕ → Finset (Fin m)) (isOr : ℕ → Prop)
    (a b : ℕ → ℕ)
    (shape : ∀ w, 2 ≤ (S w).card → ∃ j < s,
      w = N + j ∧ isOr j ∧ S w = S (a j) ∪ S (b j) ∧ a j < w ∧ b j < w)
    (center : ℕ → Bool → Option (Fin n)) (root : ℕ → Bool → ℕ)
    (cover : ∀ u v, (u, v) ∈ E → ∃ j < s, ∃ p : Bool,
      ¬ isOr j ∧ center j p = some u ∧ v ∈ S (root j p) ∧
        ∀ v' ∈ S (root j p), A u v') : E.card ≤ 2 * s := by
  classical
  let child := fun (j : ℕ) (p : Bool) => if p then b j else a j
  have singleton_of_small (w : ℕ) (v : Fin m) (hv : v ∈ S w)
      (h : ¬ 2 ≤ (S w).card) : S w = {v} := by
    exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hv)
      (by simp; omega)).symm
  have descend (w : ℕ) (v : Fin m) (hv : v ∈ S w) (h : 2 ≤ (S w).card) :
      ∃ j < s, ∃ p : Bool, isOr j ∧ 2 ≤ (S (N + j)).card ∧
        S (N + j) ⊆ S w ∧ S (child j p) = {v} := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      obtain ⟨j, hj, rfl, hor, hu, ha, hb⟩ := shape w h
      have hm : v ∈ S (a j) ∨ v ∈ S (b j) := Finset.mem_union.mp (hu ▸ hv)
      have step (p : Bool) (hlt : child j p < N + j) (hm : v ∈ S (child j p))
          (hs : S (child j p) ⊆ S (N + j)) :
          ∃ k < s, ∃ q : Bool, isOr k ∧ 2 ≤ (S (N + k)).card ∧
            S (N + k) ⊆ S (N + j) ∧ S (child k q) = {v} := by
        by_cases hc : 2 ≤ (S (child j p)).card
        · obtain ⟨k, hk, q, ho, hc', hs', he⟩ := ih _ hlt hm hc
          exact ⟨k, hk, q, ho, hc', hs'.trans hs, he⟩
        · exact ⟨j, hj, p, hor, h, by rfl, singleton_of_small _ _ hm hc⟩
      rcases hm with hm | hm
      · apply step false (by simpa [child] using ha) (by simpa [child] using hm)
        simp [child, hu]
      · apply step true (by simpa [child] using hb) (by simpa [child] using hm)
        simp [child, hu]
  let Valid := fun (e : Fin n × Fin m) (t : Fin s × Bool) =>
    (¬ isOr t.1 ∧ center t.1 t.2 = some e.1 ∧ S (root t.1 t.2) = {e.2}) ∨
    (isOr t.1 ∧ 2 ≤ (S (N + t.1)).card ∧
      (∀ v ∈ S (N + t.1), A e.1 v) ∧ S (child t.1 t.2) = {e.2})
  have exists_charge (e : ↥E) : ∃ t, Valid e.val t := by
    obtain ⟨j, hj, p, hor, hc, hm, hadj⟩ := cover _ _ e.property
    by_cases h : 2 ≤ (S (root j p)).card
    · obtain ⟨k, hk, q, ho, hb, hs, he⟩ := descend _ _ hm h
      exact ⟨(⟨k, hk⟩, q), Or.inr ⟨ho, hb, fun v hv => hadj v (hs hv), he⟩⟩
    · exact ⟨(⟨j, hj⟩, p), Or.inl ⟨hor, hc, singleton_of_small _ _ hm h⟩⟩
  have unique_edge {e f : Fin n × Fin m} {t : Fin s × Bool}
      (he : Valid e t) (hf : Valid f t) : e = f := by
    rcases he with ⟨hn, hc, hs⟩ | ⟨ho, hb, ha, hs⟩ <;>
      rcases hf with ⟨hn', hc', hs'⟩ | ⟨ho', hb', ha', hs'⟩
    · exact Prod.ext (by simpa using hc.symm.trans hc') (by simpa using hs.symm.trans hs')
    · exact (hn ho').elim
    · exact (hn' ho).elim
    · obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.mp hb
      exact Prod.ext (hC4 hne (ha _ hv) (ha _ hv') (ha' _ hv) (ha' _ hv'))
        (by simpa using hs.symm.trans hs')
  choose charge hcharge using exists_charge
  have hinj : Function.Injective charge := by
    intro e f h
    exact Subtype.ext (unique_edge (hcharge e) (h.symm ▸ hcharge f))
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective charge hinj


private def Clean {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) : Prop :=
  ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → g.op = .and → ∀ (u : Fin n) (v : Fin m),
    (C.wires (oneEach u v)).getD (n+m+k) false = true → A u v = true

private theorem on_and {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (clean : Clean A C) {j : ℕ} (hj : j < C.size) (hop : (gateAt C j).op = .and)
    {u : Fin n} {v : Fin m} (hw : wire C (oneEach u v) (n+m+1+j) = true) : A u v = true := by
  rw [gateAt_get C j hj] at hop
  apply clean j C.gates[j] (List.getElem?_eq_getElem hj) hop u v
  rwa [show n+m+1+j = (n+m+j)+1 by omega] at hw

private theorem frontier_shape {α : Type} [DecidableEq α] (base : ℕ → Finset α)
    (baseCard : ∀ w, (base w).card ≤ 1) (C : Circuit) (d : ℕ) :
    ∀ w, 2 ≤ (frontier base C d w).card → ∃ j < C.size,
      w = d+1+j ∧ isOr C j ∧ frontier base C d w =
        frontier base C d (predecessor d j C false) ∪ frontier base C d (predecessor d j C true) ∧
        predecessor d j C false < w ∧ predecessor d j C true < w := by
  intro w h
  by_cases hw : w < d+1
  · rw [frontier_input _ _ _ _ hw] at h
    have := baseCard w
    omega
  let j := w-(d+1)
  have he : w=d+1+j := by dsimp [j]; omega
  have ef := frontier_gate base C d j
  by_cases ho : isOr C j
  · have hj : j < C.size := isOr_lt C j ho
    rw [ite_eq_left ho] at ef
    exact ⟨j, hj, he, ho, he ▸ ef, he.symm ▸ predecessor_lt _ _ _ _, he.symm ▸ predecessor_lt _ _ _ _⟩
  · rw [ite_eq_right ho] at ef
    rw [he, ef] at h
    simp at h

private def binaryAt (C : Circuit) (j : ℕ) : Prop :=
  ∃ a b, (gateAt C j).inputs = [a,b]

private abbrev pred (n m : ℕ) (C : Circuit) (j : ℕ) (p : Bool) := predecessor (n+m) j C p

private theorem binary_rect {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (clean : Clean A C) (mono : Monotone2 C) (j : ℕ) (hj : j < C.size) (hor : ¬ isOr C j)
    (hbin : binaryAt C j) (p : Bool) (u : Fin n) (v : Fin m)
    (hu : u ∈ L n m C (pred n m C j (!p))) (hv : v ∈ R n m C (pred n m C j p)) :
    A u v = true := by
  have hop := (gateOp C mono j hj).resolve_right hor
  obtain ⟨a,b,h⟩ := hbin
  apply on_and clean hj hop
  rw [wire_and_binary C _ _ _ (promise_length u v) hj hop h, Bool.and_eq_true]
  have ea := (frontierEval C mono u v _).1 (Or.inl hu)
  have eb := (frontierEval C mono u v _).1 (Or.inr hv)
  cases p
  · exact ⟨eb, ea⟩
  · exact ⟨ea, eb⟩

private theorem first_binary {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (mono : Monotone2 C) (rep : Represents A C) (clean : Clean A C)
    (nr : ∀ u, ∃ v, A u v = false) (nc : ∀ v, ∃ u, A u v = false)
    (u : Fin n) (v : Fin m) (he : A u v = true) :
    ∃ j < C.size, ∃ p : Bool, ¬ isOr C j ∧ binaryAt C j ∧
      u ∈ L n m C (pred n m C j (!p)) ∧ v ∈ R n m C (pred n m C j p) := by
  classical
  let Q := fun j : ℕ => j < C.size ∧ (gateAt C j).op = .and ∧
    wire C (oneEach u v) (n+m+1+j) = true
  have existsAnd : ∃ j, Q j := by
    by_contra hn
    have hc : ∀ j < C.size, n+m+1+j ≤ C.output+1 → (gateAt C j).op = .and →
        wire C (oneEach u v) (n+m+1+j) = false := by
      intro j hj _ hop
      apply Bool.eq_false_iff.mpr
      exact fun ht => hn ⟨j,hj,hop,ht⟩
    have hout : wire C (oneEach u v) (C.output+1) = true := (rep u v).trans he
    rcases (frontierEval C mono u v _).2 hc hout with hu | hv
    · obtain ⟨v', hv'⟩ := nr u
      have h := (frontierEval C mono u v' (C.output+1)).1 (Or.inl hu)
      change C.eval (oneEach u v') = true at h
      rw [rep u v', hv'] at h
      contradiction
    · obtain ⟨u', hu'⟩ := nc v
      have h := (frontierEval C mono u' v (C.output+1)).1 (Or.inr hv)
      change C.eval (oneEach u' v) = true at h
      rw [rep u' v, hu'] at h
      contradiction
  let j := Nat.find existsAnd
  obtain ⟨hj, hop, hvj⟩ := Nat.find_spec existsAnd
  have nOr : ¬ isOr C j := by rw [isOr_iff, show (gateAt C j).op = .and from hop]; simp
  have hfront (p : Bool) (ht : wire C (oneEach u v) (pred n m C j p) = true) :
      u ∈ L n m C (pred n m C j p) ∨ v ∈ R n m C (pred n m C j p) := by
    refine (frontierEval C mono u v _).2 (fun k hk hb ho => ?_) ht
    apply Bool.eq_false_iff.mpr
    intro htrue
    apply Nat.find_min existsAnd (show k < j by
      have hh := predecessor_lt (n+m) j C p; dsimp [pred] at hb; omega)
    exact ⟨hk,ho,htrue⟩
  rcases list_cases2 _ (gateLength C mono j hj) with h | ⟨a,h⟩ | ⟨a,b,h⟩
  · obtain ⟨v', hv'⟩ := nr u
    have e := on_and clean hj hop (u := u) (v := v')
      (wire_and_null C _ _ _ (promise_length u v') hj hop h)
    exact (Bool.noConfusion (hv'.symm.trans e))
  · have ht := (wire_and_unary C _ _ _ (promise_length u v) hj hop h).symm.trans hvj
    rcases hfront false ht with hu | hv
    · obtain ⟨v', hv'⟩ := nr u
      have e := (frontierEval C mono u v' _).1 (Or.inl hu)
      have e' := on_and clean hj hop ((wire_and_unary C _ _ _ (promise_length u v') hj hop h).trans e)
      exact Bool.noConfusion (hv'.symm.trans e')
    · obtain ⟨u', hu'⟩ := nc v
      have e := (frontierEval C mono u' v _).1 (Or.inr hv)
      have e' := on_and clean hj hop ((wire_and_unary C _ _ _ (promise_length u' v) hj hop h).trans e)
      exact Bool.noConfusion (hu'.symm.trans e')
  · have ht : wire C (oneEach u v) (pred n m C j false) = true ∧
        wire C (oneEach u v) (pred n m C j true) = true := by
      simpa only [wire_and_binary C _ _ _ (promise_length u v) hj hop h, Bool.and_eq_true] using hvj
    rcases hfront false ht.1 with ha | ha <;> rcases hfront true ht.2 with hb | hb
    · obtain ⟨v', hv'⟩ := nr u
      have ea := (frontierEval C mono u v' _).1 (Or.inl ha)
      have eb := (frontierEval C mono u v' _).1 (Or.inl hb)
      have e := on_and clean hj hop ((wire_and_binary C _ _ _ (promise_length u v') hj hop h).trans
        (by simpa only [Bool.and_eq_true] using And.intro ea eb))
      exact Bool.noConfusion (hv'.symm.trans e)
    · exact ⟨j,hj,true,nOr,⟨a,b,h⟩,ha,hb⟩
    · exact ⟨j,hj,false,nOr,⟨a,b,h⟩,hb,ha⟩
    · obtain ⟨u', hu'⟩ := nc v
      have ea := (frontierEval C mono u' v _).1 (Or.inr ha)
      have eb := (frontierEval C mono u' v _).1 (Or.inr hb)
      have e := on_and clean hj hop ((wire_and_binary C _ _ _ (promise_length u' v) hj hop h).trans
        (by simpa only [Bool.and_eq_true] using And.intro ea eb))
      exact Bool.noConfusion (hu'.symm.trans e)

private theorem singleton_side {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : α → β → Bool)
    (hC4 : ∀ ⦃u u' v v'⦄, v ≠ v' → A u v = true → A u v' = true → A u' v = true → A u' v' = true → u = u')
    {S : Finset α} {T : Finset β} {u : α} {v : β} (hu : u ∈ S) (hv : v ∈ T)
    (hr : ∀ a ∈ S, ∀ b ∈ T, A a b = true) : S = {u} ∨ T = {v} := by
  by_cases hlarge : 1 < T.card
  · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hlarge
    left
    ext z
    simp only [Finset.mem_singleton]
    exact ⟨fun hz => hC4 hab (hr z hz a ha) (hr z hz b hb) (hr u hu a ha) (hr u hu b hb),
      fun e => e.symm ▸ hu⟩
  · right
    exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hv) (by simp; omega)).symm

private theorem head_singleton {α : Type} (S : Finset α) (a : α) (h : S = {a}) :
    S.toList.head? = some a := by
  subst S
  simp

private def edges {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n × Fin m) :=
  Finset.univ.filter fun e => A e.1 e.2 = true

private theorem clean_lower {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hC4 : ∀ ⦃u u' v v'⦄, v ≠ v' → A u v = true → A u v' = true → A u' v = true → A u' v' = true → u = u')
    (nr : ∀ u, ∃ v, A u v = false) (nc : ∀ v, ∃ u, A u v = false)
    (C : Circuit) (mono : Monotone2 C) (rep : Represents A C) (clean : Clean A C) :
    (edges A).card ≤ 4 * C.size := by
  classical
  let orientation := fun (e : Fin n × Fin m) => ∃ j < C.size, ∃ p : Bool,
    ¬ isOr C j ∧ binaryAt C j ∧ L n m C (pred n m C j (!p)) = {e.1} ∧ e.2 ∈ R n m C (pred n m C j p)
  let E₁ := (edges A).filter orientation
  let E₂ := (edges A).filter fun e => ¬ orientation e
  have sum : E₁.card + E₂.card = (edges A).card :=
    Finset.card_filter_add_card_filter_not (s := edges A) orientation
  have h₁ : E₁.card ≤ 2*C.size := by
    apply card_le_two_mul E₁ (fun u v => A u v = true) hC4 (n+m+1) C.size (R n m C) (isOr C)
      (fun j => pred n m C j false) (fun j => pred n m C j true)
      (frontier_shape _ (rightBase_card n m) C _)
      (fun j p => (L n m C (pred n m C j (!p))).toList.head?) (pred n m C)
    intro u v he
    obtain ⟨j,hj,p,ho,hb,hs,hv⟩ := (Finset.mem_filter.mp he).2
    have hu : u ∈ L n m C (pred n m C j (!p)) := by simp [hs]
    exact ⟨j,hj,p,ho,head_singleton _ _ hs,hv,fun v' hv' => binary_rect clean mono j hj ho hb p u v' hu hv'⟩
  let sw : (Fin n × Fin m) ↪ (Fin m × Fin n) := (Equiv.prodComm _ _).toEmbedding
  have transC4 : ∀ ⦃v v' u u'⦄, u ≠ u' → A u v = true → A u' v = true →
      A u v' = true → A u' v' = true → v = v' := by
    intro v v' u u' hn e₁ e₂ e₃ e₄
    by_contra hv
    exact hn (hC4 hv e₁ e₃ e₂ e₄)
  have h₂ : (E₂.map sw).card ≤ 2*C.size := by
    apply card_le_two_mul (E₂.map sw) (fun v u => A u v = true) transC4
      (n+m+1) C.size (L n m C) (isOr C)
      (fun j => pred n m C j false) (fun j => pred n m C j true)
      (frontier_shape _ (leftBase_card n) C _)
      (fun j p => (R n m C (pred n m C j (!p))).toList.head?) (pred n m C)
    intro v u he
    have he' : (u,v) ∈ E₂ := by
      obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_map.mp he
      change (b,a)=(v,u) at he
      cases he
      exact hab
    have e : A u v = true := (Finset.mem_filter.mp (Finset.mem_filter.mp he').1).2
    have hn := (Finset.mem_filter.mp he').2
    obtain ⟨j,hj,p,ho,hb,hu,hv⟩ := first_binary mono rep clean nr nc u v e
    have rect := binary_rect clean mono j hj ho hb p
    have hs : R n m C (pred n m C j p) = {v} :=
      (singleton_side A hC4 hu hv (fun u' hu' v' hv' => rect u' v' hu' hv')).resolve_left
        (fun hh => hn ⟨j,hj,p,ho,hb,hh,hv⟩)
    refine ⟨j,hj,!p,ho,?_,hu,fun u' hu' => rect u' v hu' hv⟩
    simpa using head_singleton _ _ hs
  rw [Finset.card_map] at h₂
  omega

section AffineFacts

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q]

private def coordinate : Fin (q*q) ≃ ZMod q × ZMod q :=
  finProdFinEquiv.symm.trans
    ((ZMod.finEquiv q).toEquiv.prodCongr (ZMod.finEquiv q).toEquiv)

private def affine (u v : Fin (q*q)) : Bool :=
  decide ((coordinate q u).2 = (coordinate q u).1 * (coordinate q v).1 + (coordinate q v).2)

private theorem affine_c4 : ∀ ⦃u u' v v'⦄, v ≠ v' → affine q u v = true → affine q u v' = true →
    affine q u' v = true → affine q u' v' = true → u = u' := by
  intro u u' v v' hne h₁ h₂ h₃ h₄
  simp only [affine, decide_eq_true_eq] at h₁ h₂ h₃ h₄
  have hmul : ((coordinate q u).1 - (coordinate q u').1) *
      ((coordinate q v).1 - (coordinate q v').1) = 0 := by
    linear_combination -h₁ + h₂ + h₃ - h₄
  rcases mul_eq_zero.mp hmul with ha | hx
  · have ha' := sub_eq_zero.mp ha
    apply (coordinate q).injective
    refine Prod.ext ha' ?_
    rw [ha'] at h₁
    exact h₁.trans h₃.symm
  · have hx' := sub_eq_zero.mp hx
    exfalso
    apply hne
    apply (coordinate q).injective
    refine Prod.ext hx' ?_
    rw [hx'] at h₁
    exact add_left_cancel (h₁.symm.trans h₂)

private theorem affine_noRows (u : Fin (q*q)) : ∃ v, affine q u v = false := by
  refine ⟨(coordinate q).symm (0, (coordinate q u).2 + 1), ?_⟩
  simp [affine, eq_comm (a := (coordinate q u).2)]

private theorem affine_noCols (v : Fin (q*q)) : ∃ u, affine q u v = false := by
  refine ⟨(coordinate q).symm (0, (coordinate q v).2 + 1), ?_⟩
  simp [affine]

private theorem affine_card :
    (Finset.univ.filter (fun (e : Fin (q*q) × Fin (q*q)) => affine q e.1 e.2 = true)).card = q*q*q := by
  let E : Finset (Fin (q*q) × Fin (q*q)) := Finset.univ.filter fun e => affine q e.1 e.2 = true
  let enc : ZMod q × ZMod q × ZMod q ≃ ↥E :=
    { toFun := fun t => ⟨((coordinate q).symm (t.1, t.1*t.2.1+t.2.2),
        (coordinate q).symm t.2), by simp [E, affine]⟩
      invFun := fun e => ((coordinate q) e.val.1 |>.1, (coordinate q) e.val.2)
      left_inv := fun t => by simp
      right_inv := fun e => by
        have he : affine q e.val.1 e.val.2 = true := (Finset.mem_filter.mp e.property).2
        have hh := of_decide_eq_true he
        apply Subtype.ext
        apply Prod.ext
        · apply (coordinate q).injective
          simp only [Equiv.apply_symm_apply]
          exact Prod.ext rfl hh.symm
        · exact (coordinate q).symm_apply_apply _ }
  have h := Fintype.card_congr enc
  simpa only [Fintype.card_prod, Fintype.card_coe, ZMod.card, Nat.mul_assoc] using h.symm

end AffineFacts

namespace Upper

private def wires (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

private theorem wires_append (gs hs : List Gate) (x : List Bool) :
    wires (gs ++ hs) x = wires hs (wires gs x) := by
  simp [wires, Circuit.wires, List.foldl_append]

private theorem wires_length (gs : List Gate) (x : List Bool) :
    (wires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wires, Circuit.wires]
  | cons g gs ih =>
      rw [show g :: gs = [g] ++ gs from rfl, wires_append, ih]
      simp [wires, Circuit.wires]; omega

private theorem input_prefix (gs : List Gate) (x : List Bool) : x <+: wires gs x := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [wires, Circuit.wires]⟩
  | cons g gs ih =>
      rw [show g :: gs = [g] ++ gs from rfl, wires_append]
      apply List.IsPrefix.trans _ (ih _)
      exact ⟨_, rfl⟩

private abbrev Mono (gs : List Gate) : Prop := Monotone2 (Circuit.mk gs 0)

private def Signal {ι : Type*} {n : ℕ} (input : ι → List Bool)
    (gs : List Gate) (i : ℕ) (f : ι → Bool) : Prop :=
  i < n + gs.length ∧ ∀ t, (wires gs (input t)).getD i false = f t

private theorem liftSignal {ι : Type*} {n : ℕ} {input : ι → List Bool}
    (hlen : ∀ t, (input t).length = n) {gs hs : List Gate} (hp : gs <+: hs)
    {i : ℕ} {f : ι → Bool} (h : Signal (n := n) input gs i f) :
    Signal (n := n) input hs i f := by
  rcases hp with ⟨rest, rfl⟩
  refine ⟨by have := h.1; simp; omega, ?_⟩
  intro t
  rw [wires_append]
  obtain ⟨more, hm⟩ := input_prefix rest (wires gs (input t))
  rw [← hm, List.getD_append _ _ _ _ (by rw [wires_length, hlen]; exact h.1)]
  exact h.2 t

private theorem appendMono {gs : List Gate} (h : Mono gs) {g : Gate}
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hi : g.inputs.length ≤ 2) :
    Mono (gs ++ [g]) := by
  intro g' hg'
  change g' ∈ gs ++ [g] at hg'
  rcases List.mem_append.mp hg' with hg' | hg'
  · exact h _ hg'
  · have := List.mem_singleton.mp hg'
    subst g'
    exact ⟨hop, hi⟩

private theorem emit {ι : Type*} {n : ℕ} {input : ι → List Bool}
    (hlen : ∀ t, (input t).length = n) (gs : List Gate) (op : GateOp) (ins : List ℕ)
    (f : ι → List Bool)
    (h : ∀ t, (ins.map fun i => (wires gs (input t)).getD i false) = f t) :
    Signal (n := n) input (gs ++ [⟨op, ins⟩]) (n + gs.length) (fun t => op.eval (f t)) := by
  refine ⟨by simp, ?_⟩
  intro t
  have he : (wires gs (input t)).length = n + gs.length := by rw [wires_length, hlen]
  rw [wires_append]
  change ((wires gs (input t)) ++
    [op.eval (ins.map fun i => (wires gs (input t)).getD i false)]).getD
      (n + gs.length) false = _
  rw [← he, List.getD_append_right _ _ _ _ le_rfl, h]
  simp

/-- Append a pair of gates per item, accumulating the conjunctions in their respective buckets. -/
private theorem scatter {ι α β : Type*} [DecidableEq β] {n : ℕ} {input : ι → List Bool}
    (hlen : ∀ t, (input t).length = n) {gs : List Gate} (hm : Mono gs)
    (l : List α) (key : α → β) {s₁ s₂ : α → ℕ} {f₁ f₂ : α → ι → Bool}
    (h₁ : ∀ a, Signal (n := n) input gs (s₁ a) (f₁ a))
    (h₂ : ∀ a, Signal (n := n) input gs (s₂ a) (f₂ a))
    {z : ℕ} (hz : Signal (n := n) input gs z (fun _ => false)) :
    ∃ (hs : List Gate) (o : β → ℕ), gs <+: hs ∧ Mono hs ∧
      hs.length = gs.length + 2 * l.length ∧
      ∀ j, Signal (n := n) input hs (o j)
        (fun t => l.any fun a => decide (key a = j) && (f₁ a t && f₂ a t)) := by
  induction l with
  | nil => exact ⟨gs, fun _ => z, ⟨[], by simp⟩, hm, by simp, fun _ => hz⟩
  | cons a l ih =>
    obtain ⟨hs, o, hp, hmono, hc, ho⟩ := ih
    let w := n + hs.length
    let andGate : Gate := ⟨.and, [s₁ a, s₂ a]⟩
    let js := hs ++ [andGate]
    let r := n + js.length
    let orGate : Gate := ⟨.or, [w, o (key a)]⟩
    let ks := js ++ [orGate]
    have e₁ : hs <+: js := ⟨_, rfl⟩
    have e₂ : js <+: ks := ⟨_, rfl⟩
    have ha : Signal (n := n) input js w (fun t => f₁ a t && f₂ a t) := by
      have h := emit hlen hs .and [s₁ a, s₂ a] (fun t => [f₁ a t, f₂ a t]) (by
        intro t
        simp only [List.map_cons, List.map_nil, (liftSignal hlen hp (h₁ a)).2 t,
          (liftSignal hlen hp (h₂ a)).2 t])
      simpa [w, js, andGate, GateOp.eval] using h
    have hb : Signal (n := n) input ks r
        (fun t => (f₁ a t && f₂ a t) ||
          (l.any fun b => decide (key b = key a) && (f₁ b t && f₂ b t))) := by
      have h := emit hlen js .or [w, o (key a)] (fun t => [f₁ a t && f₂ a t,
        l.any fun b => decide (key b = key a) && (f₁ b t && f₂ b t)]) (by
        intro t
        simp only [List.map_cons, List.map_nil, ha.2 t,
          (liftSignal hlen e₁ (ho (key a))).2 t])
      simpa [r, ks, orGate, GateOp.eval] using h
    refine ⟨ks, fun j => if key a = j then r else o j, hp.trans (e₁.trans e₂), ?_, ?_, ?_⟩
    · exact appendMono (appendMono hmono (g := andGate) (by simp [andGate]) (by simp [andGate]))
        (g := orGate) (by simp [orGate]) (by simp [orGate])
    · simp [ks, js, hc]; omega
    · intro j
      by_cases e : key a = j
      · subst j
        simpa using hb
      · simpa [e] using liftSignal hlen (e₁.trans e₂) (ho j)

private theorem scatterUnique {ι α β : Type*} [DecidableEq α] [DecidableEq β]
    {n : ℕ} {input : ι → List Bool} (hlen : ∀ t, (input t).length = n)
    {gs : List Gate} (hm : Mono gs) (l : List α) (key : α → β)
    {s₁ s₂ : α → ℕ} {f₁ f₂ : α → ι → Bool}
    (h₁ : ∀ a, Signal (n := n) input gs (s₁ a) (f₁ a))
    (h₂ : ∀ a, Signal (n := n) input gs (s₂ a) (f₂ a))
    {z : ℕ} (hz : Signal (n := n) input gs z (fun _ => false))
    (sel : ι → α) (hmem : ∀ t, sel t ∈ l)
    (hsel : ∀ a t, (f₁ a t && f₂ a t) = decide (a = sel t)) :
    ∃ (hs : List Gate) (o : β → ℕ), gs <+: hs ∧ Mono hs ∧
      hs.length = gs.length + 2 * l.length ∧
      ∀ j, Signal (n := n) input hs (o j) (fun t => decide (key (sel t) = j)) := by
  obtain ⟨hs, o, hp, hm', hc, ho⟩ := scatter hlen hm l key h₁ h₂ hz
  refine ⟨hs, o, hp, hm', hc, fun j => ⟨(ho j).1, ?_⟩⟩
  intro t
  rw [(ho j).2 t, Bool.eq_iff_iff]
  simp only [List.any_eq_true, hsel, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, _, hk, rfl⟩
    exact hk
  · intro hk
    exact ⟨sel t, hmem t, hk, rfl⟩

private abbrev trace {n m : ℕ} (t : Fin n × Fin m) : List Bool := oneEach t.1 t.2

private theorem trace_length {n m : ℕ} (t : Fin n × Fin m) : (trace t).length = n + m := by
  simp [trace, oneEach]

private theorem left_signal {n m : ℕ} (i : Fin n) :
    Signal (n := n + m) (trace (n := n) (m := m)) [] i.val (fun t => decide (i = t.1)) := by
  refine ⟨by simp; omega, ?_⟩
  intro t
  change (oneEach t.1 t.2).getD i.val false = _
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp),
    List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem right_signal {n m : ℕ} (i : Fin m) :
    Signal (n := n + m) (trace (n := n) (m := m)) [] (n + i.val)
      (fun t => decide (i = t.2)) := by
  refine ⟨by simp, ?_⟩
  intro t
  change (oneEach t.1 t.2).getD (n + i.val) false = _
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.add_sub_cancel_left,
    List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private def pairList (q : ℕ) [NeZero q] : List (ZMod q × ZMod q) :=
  List.ofFn fun i : Fin (q*q) =>
    let p := (finProdFinEquiv (m := q) (n := q)).symm i
    (ZMod.finEquiv q p.1, ZMod.finEquiv q p.2)

private theorem mem_pairList {q : ℕ} [NeZero q] (p : ZMod q × ZMod q) : p ∈ pairList q := by
  apply List.mem_ofFn.mpr
  refine ⟨finProdFinEquiv ((ZMod.finEquiv q).symm p.1, (ZMod.finEquiv q).symm p.2), ?_⟩
  simp

private theorem pair_eq {q : ℕ} (a b : ZMod q × ZMod q) :
    (decide (b.1 = a.1) && decide (b.2 = a.2)) = decide (a = b) := by
  simp [Prod.ext_iff, eq_comm]

/-- Incidence for any four maps giving the two coordinates on each side. -/
private theorem repSizeAtMost_of_coordinates (q : ℕ) (a b x y : Fin (q*q) → ZMod q) :
    RepSizeAtMost (fun u v => decide (b u = a u * x v + y v)) (20 * q * q) := by
  by_cases hq : q = 0
  · subst q
    exact ⟨⟨[], 0⟩, by simp [Monotone2], by simp [Circuit.size], fun u => u.elim0⟩
  let _ : NeZero q := ⟨hq⟩
  let N := q*q + q*q
  let gs₀ : List Gate := [⟨.or, []⟩]
  have hm₀ : Mono gs₀ := by
    exact appendMono (gs := []) (by simp [Monotone2]) (by simp) (by simp)
  have hz₀ : Signal (n := N) trace gs₀ N (fun _ : Fin (q*q) × Fin (q*q) => false) := by
    simpa [gs₀, GateOp.eval] using
      (emit (n := N) (input := trace (n := q*q) (m := q*q)) trace_length [] .or []
        (fun _ => []) (by simp))
  have e₀ : [] <+: gs₀ := ⟨gs₀, rfl⟩
  have hl₀ (i : Fin (q*q)) := liftSignal (n := N) trace_length e₀ (left_signal (m := q*q) i)
  have hr₀ (i : Fin (q*q)) := liftSignal (n := N) trace_length e₀ (right_signal (n := q*q) i)
  let verts := List.finRange (q*q)
  have vm (i : Fin (q*q)) : i ∈ verts := by simp [verts]
  obtain ⟨gs₁, oa, e₁, hm₁, hc₁, ha⟩ := scatterUnique trace_length hm₀ verts a hl₀ hl₀ hz₀
    Prod.fst (fun t => vm t.1) (by simp)
  have hl₁ i := liftSignal trace_length e₁ (hl₀ i)
  have hz₁ := liftSignal trace_length e₁ hz₀
  obtain ⟨gs₂, ob, e₂, hm₂, hc₂, hb⟩ := scatterUnique trace_length hm₁ verts b hl₁ hl₁ hz₁
    Prod.fst (fun t => vm t.1) (by simp)
  have hr₂ i := liftSignal trace_length (e₁.trans e₂) (hr₀ i)
  have hz₂ := liftSignal trace_length e₂ hz₁
  obtain ⟨gs₃, ox, e₃, hm₃, hc₃, hx⟩ := scatterUnique trace_length hm₂ verts x hr₂ hr₂ hz₂
    Prod.snd (fun t => vm t.2) (by simp)
  have hr₃ i := liftSignal trace_length e₃ (hr₂ i)
  have hz₃ := liftSignal trace_length e₃ hz₂
  obtain ⟨gs₄, oy, e₄, hm₄, hc₄, hy⟩ := scatterUnique trace_length hm₃ verts y hr₃ hr₃ hz₃
    Prod.snd (fun t => vm t.2) (by simp)
  have hz₄ := liftSignal trace_length e₄ hz₃
  obtain ⟨gs₅, op, e₅, hm₅, hc₅, hp⟩ := scatterUnique trace_length hm₄ (pairList q)
    (fun j => j.1 * j.2) (fun j => liftSignal trace_length (e₂.trans (e₃.trans e₄)) (ha j.1))
    (fun j => liftSignal trace_length e₄ (hx j.2)) hz₄
    (fun t => (a t.1, x t.2)) (fun _ => mem_pairList _) (fun j t => pair_eq j (a t.1, x t.2))
  have hz₅ := liftSignal trace_length e₅ hz₄
  obtain ⟨gs₆, os, e₆, hm₆, hc₆, hs⟩ := scatterUnique trace_length hm₅ (pairList q)
    (fun j => j.1 + j.2) (fun j => hp j.1) (fun j => liftSignal trace_length e₅ (hy j.2)) hz₅
    (fun t => (a t.1 * x t.2, y t.2)) (fun _ => mem_pairList _)
    (fun j t => pair_eq j (a t.1 * x t.2, y t.2))
  let symbols := List.ofFn (ZMod.finEquiv q)
  have sm (j : ZMod q) : j ∈ symbols := by
    exact List.mem_ofFn.mpr ⟨(ZMod.finEquiv q).symm j, by simp⟩
  obtain ⟨gs₇, o, _, hm₇, hc₇, hout⟩ := scatter trace_length hm₆ symbols (fun _ => ())
    (fun j => liftSignal trace_length (e₃.trans (e₄.trans (e₅.trans e₆))) (hb j)) hs
    (liftSignal trace_length e₆ hz₅)
  refine ⟨⟨gs₇, o ()⟩, hm₇, ?_, ?_⟩
  · change gs₇.length ≤ 20 * q * q
    rw [Nat.mul_assoc]
    have hqc : q ≤ q*q := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hq)
    simp only [verts, pairList, symbols, List.length_ofFn, List.length_finRange, gs₀,
      List.length_cons, List.length_nil, Nat.zero_add] at hc₁ hc₂ hc₃ hc₄ hc₅ hc₆ hc₇
    omega
  · intro u v
    change (wires gs₇ (trace (u,v))).getD (o ()) false = _
    rw [(hout ()).2 (u,v), Bool.eq_iff_iff]
    simp only [decide_true, Bool.true_and, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨j, _, hj, hj'⟩
      exact hj.trans hj'.symm
    · intro e
      exact ⟨b u, sm (b u), rfl, e.symm⟩

end Upper

end PEqualNP.Outside.L_meta_25448

open PEqualNP.Outside.L_meta_25448

theorem PEqualNP.Outside.L_meta_25448 :
    ¬ (∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (s : ℕ), PEqualNP.Represents.RepSizeAtMost A s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C ∧ ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD (n + m + k) false = true → A u v = true) := by
  intro assumed
  let _ : Fact (Nat.Prime 101) := ⟨by decide⟩
  have upper : PEqualNP.Represents.RepSizeAtMost (affine 101) (20 * 101 * 101) := by
    exact Upper.repSizeAtMost_of_coordinates 101
      (fun u => (coordinate 101 u).1) (fun u => (coordinate 101 u).2)
      (fun v => (coordinate 101 v).1) (fun v => (coordinate 101 v).2)
  obtain ⟨C, mono, small, rep, clean⟩ := assumed (101*101) (101*101) (affine 101) _ upper
  have lower := clean_lower (affine 101) (affine_c4 101) (affine_noRows 101) (affine_noCols 101) C mono rep clean
  have count : (edges (affine 101)).card = 101*101*101 := affine_card 101
  rw [count] at lower
  omega

