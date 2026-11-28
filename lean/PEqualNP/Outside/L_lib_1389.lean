import Mathlib
import PEqualNP.Defs

-- The wire-evaluation lemmas (run, run_snoc, run_length, run_gate) follow
-- lean/PEqualNP/Outside/L_lib_1311.lean on upstream main by Anmol Agarwal (Apache-2.0),
-- generalised here to any value type so that they serve both wire values and supports.

namespace PEqualNP.Outside.L_lib_1389

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

section Gen
variable {α : Type}

def runG (F : List α → Gate → α) (gs : List Gate) (x : List α) : List α :=
  gs.foldl (fun w g => w ++ [F w g]) x

theorem runG_snoc (F : List α → Gate → α) (gs : List Gate) (g : Gate) (x : List α) :
    runG F (gs ++ [g]) x = runG F gs x ++ [F (runG F gs x) g] := by
  simp only [runG, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem runG_length (F : List α → Gate → α) (gs : List Gate) (x : List α) :
    (runG F gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runG]
  | append_singleton gs g ih =>
    rw [runG_snoc, List.length_append, List.length_singleton, ih, List.length_append,
      List.length_singleton]
    omega

theorem getD_snoc_lt (l : List α) (b e : α) (t : ℕ) (ht : t < l.length) :
    (l ++ [b]).getD t e = l.getD t e := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]

theorem getD_snoc_at (l : List α) (b e : α) : (l ++ [b]).getD l.length e = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp

theorem runG_init (F : List α → Gate → α) (gs hs : List Gate) (x : List α) (e : α) (i : ℕ)
    (hi : i < x.length + gs.length) :
    (runG F (gs ++ hs) x).getD i e = (runG F gs x).getD i e := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, runG_snoc,
      getD_snoc_lt _ _ _ _ (by rw [runG_length, List.length_append]; omega), ih]

theorem runG_input (F : List α → Gate → α) (gs : List Gate) (x : List α) (e : α) (i : ℕ)
    (hi : i < x.length) : (runG F gs x).getD i e = x.getD i e := by
  have h := runG_init F [] gs x e i (by simpa using hi)
  simpa [runG] using h

theorem runG_gate (F : List α → Gate → α) (gs : List Gate) (x : List α) (e : α) (j : ℕ)
    (hj : j < gs.length) :
    (runG F gs x).getD (x.length + j) e = F (runG F (gs.take j) x) gs[j] := by
  have hsp : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 : gs.take (j + 1) = gs.take j ++ [gs[j]] := List.take_succ_eq_append_getElem hj
    rw [← h1, List.take_append_drop]
  have htl : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have h1 : (runG F gs x).getD (x.length + j) e =
      (runG F (gs.take j ++ [gs[j]]) x).getD (x.length + j) e := by
    conv_lhs => rw [hsp]
    exact runG_init _ _ _ _ _ _ (by rw [List.length_append, htl, List.length_singleton]; omega)
  rw [h1, runG_snoc]
  have hlen : (runG F (gs.take j) x).length = x.length + j := by rw [runG_length, htl]
  rw [← hlen, getD_snoc_at]

theorem runG_take (F : List α → Gate → α) (gs : List Gate) (x : List α) (e : α) (j i : ℕ)
    (hj : j ≤ gs.length) (hi : i < x.length + j) :
    (runG F (gs.take j) x).getD i e = (runG F gs x).getD i e := by
  conv_rhs => rw [← List.take_append_drop j gs]
  exact (runG_init F _ _ x e i (by rw [List.length_take_of_le hj]; exact hi)).symm

theorem runG_big (F : List α → Gate → α) (gs : List Gate) (x : List α) (e : α) (i : ℕ)
    (hi : x.length + gs.length ≤ i) : (runG F gs x).getD i e = e :=
  List.getD_eq_default _ _ (by rw [runG_length]; exact hi)

end Gen

inductive Cone (d : ℕ) (C : Circuit) : ℕ → Prop
  | out : Cone d C C.output
  | read (j w : ℕ) : j < C.gates.length → Cone d C (d + 2 + j) → w ∈ (gateAt C j).inputs →
      Cone d C w

inductive Reach (d : ℕ) (C : Circuit) : ℕ → ℕ → Prop
  | refl (u : ℕ) : Reach d C u u
  | step (c u j : ℕ) : j < C.gates.length → c ∈ (gateAt C j).inputs → Reach d C (d + 2 + j) u →
      Reach d C c u

section Main
variable (d : ℕ) (C : Circuit)

def WF : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)

def xs (S : Finset (Fin d)) : List Bool := List.ofFn (fun i : Fin d => decide (i ∈ S)) ++ [false, true]

def V (S : Finset (Fin d)) (w : ℕ) : Bool := (runG WF C.gates (xs d S)).getD w false

def depF : List (Finset (Fin d)) → Gate → Finset (Fin d) :=
  fun ws g => g.inputs.foldl (fun S i => S ∪ ws.getD i ∅) ∅

def dep0 : List (Finset (Fin d)) := List.ofFn (fun i : Fin d => ({i} : Finset (Fin d))) ++ [∅, ∅]

def D (w : ℕ) : Finset (Fin d) := (runG (depF d) C.gates (dep0 d)).getD w ∅

theorem xs_length (S : Finset (Fin d)) : (xs d S).length = d + 2 := by simp [xs]

theorem dep0_length : (dep0 d).length = d + 2 := by simp [dep0]

theorem gateAt_eq (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt; rw [List.getD_eq_getElem _ _ hj]

theorem V_gate (hrb : ReadsBack (d + 2) C) (S : Finset (Fin d)) (j : ℕ) (hj : j < C.gates.length) :
    V d C S (d + 2 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V d C S)) := by
  have h := runG_gate WF C.gates (xs d S) false j hj
  rw [xs_length] at h
  unfold V; rw [h, gateAt_eq C j hj]
  unfold WF; congr 1
  refine List.map_congr_left fun i hi => ?_
  have hlt : i < d + 2 + j := hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)
  exact runG_take WF C.gates (xs d S) false j i (Nat.le_of_lt hj) (by rw [xs_length]; exact hlt)

theorem V_input (S : Finset (Fin d)) (w : ℕ) (hw : w < d) : V d C S w = decide (⟨w, hw⟩ ∈ S) := by
  unfold V; rw [runG_input _ _ _ _ _ (by rw [xs_length]; omega)]
  unfold xs
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hw)]
  simp [hw]

theorem V_d (S : Finset (Fin d)) : V d C S d = false := by
  unfold V; rw [runG_input _ _ _ _ _ (by rw [xs_length]; omega)]
  unfold xs
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem V_d1 (S : Finset (Fin d)) : V d C S (d + 1) = true := by
  unfold V; rw [runG_input _ _ _ _ _ (by rw [xs_length]; omega)]
  unfold xs
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem V_big (S : Finset (Fin d)) (w : ℕ) (hw : d + 2 + C.gates.length ≤ w) : V d C S w = false := by
  unfold V; exact runG_big _ _ _ _ _ (by rw [xs_length]; exact hw)

theorem foldl_union_mem (ws : List (Finset (Fin d))) (l : List ℕ) (T : Finset (Fin d)) (k : Fin d) :
    k ∈ l.foldl (fun S i => S ∪ ws.getD i ∅) T ↔ k ∈ T ∨ ∃ i ∈ l, k ∈ ws.getD i ∅ := by
  induction l generalizing T with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    simp only [Finset.mem_union, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨i, hi, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, Or.inl rfl, h⟩
      · exact Or.inr ⟨i, Or.inr hi, h⟩
    · rintro (h | ⟨i, (rfl | hi), h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨i, hi, h⟩

theorem D_gate (hrb : ReadsBack (d + 2) C) (j : ℕ) (hj : j < C.gates.length) (k : Fin d) :
    k ∈ D d C (d + 2 + j) ↔ ∃ i ∈ (gateAt C j).inputs, k ∈ D d C i := by
  have h := runG_gate (depF d) C.gates (dep0 d) ∅ j hj
  rw [dep0_length] at h
  unfold D; rw [h, gateAt_eq C j hj]
  show k ∈ (C.gates[j]).inputs.foldl
    (fun S i => S ∪ (runG (depF d) (C.gates.take j) (dep0 d)).getD i ∅) ∅ ↔ _
  rw [foldl_union_mem]
  simp only [Finset.notMem_empty, false_or]
  constructor
  · rintro ⟨i, hi, hk⟩
    have hlt : i < d + 2 + j := hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)
    refine ⟨i, hi, ?_⟩
    rwa [runG_take (depF d) C.gates (dep0 d) ∅ j i (Nat.le_of_lt hj) (by rw [dep0_length]; exact hlt)] at hk
  · rintro ⟨i, hi, hk⟩
    have hlt : i < d + 2 + j := hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)
    refine ⟨i, hi, ?_⟩
    rwa [runG_take (depF d) C.gates (dep0 d) ∅ j i (Nat.le_of_lt hj) (by rw [dep0_length]; exact hlt)]

theorem D_input (w : ℕ) (hw : w < d) : D d C w = {⟨w, hw⟩} := by
  unfold D; rw [runG_input _ _ _ _ _ (by rw [dep0_length]; omega)]
  unfold dep0
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hw)]
  simp [hw]

theorem D_d : D d C d = ∅ := by
  unfold D; rw [runG_input _ _ _ _ _ (by rw [dep0_length]; omega)]
  unfold dep0
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem D_d1 : D d C (d + 1) = ∅ := by
  unfold D; rw [runG_input _ _ _ _ _ (by rw [dep0_length]; omega)]
  unfold dep0
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem D_big (w : ℕ) (hw : d + 2 + C.gates.length ≤ w) : D d C w = ∅ := by
  unfold D; exact runG_big _ _ _ _ _ (by rw [dep0_length]; exact hw)

theorem wire_cases (w : ℕ) : w < d ∨ w = d ∨ w = d + 1 ∨ (∃ j < C.gates.length, w = d + 2 + j) ∨
    d + 2 + C.gates.length ≤ w := by
  by_cases h1 : w < d
  · exact Or.inl h1
  by_cases h2 : w = d
  · exact Or.inr (Or.inl h2)
  by_cases h3 : w = d + 1
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : d + 2 + C.gates.length ≤ w
  · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨w - (d + 2), by omega, by omega⟩)))

theorem D_form (hrb : ReadsBack (d + 2) C) (w : ℕ) (k : Fin d) (hk : k ∈ D d C w) :
    w = k.val ∨ ∃ j < C.gates.length, w = d + 2 + j := by
  rcases wire_cases d C w with h | h | h | h | h
  · rw [D_input d C w h, Finset.mem_singleton] at hk; subst hk; exact Or.inl rfl
  · subst h; rw [D_d] at hk; simp at hk
  · subst h; rw [D_d1] at hk; simp at hk
  · exact Or.inr h
  · rw [D_big d C w h] at hk; simp at hk

theorem D_le (hrb : ReadsBack (d + 2) C) (w : ℕ) (k : Fin d) (hk : k ∈ D d C w) : k.val ≤ w := by
  rcases D_form d C hrb w k hk with h | ⟨j, _, h⟩ <;> omega

theorem V_local (hrb : ReadsBack (d + 2) C) : ∀ (w : ℕ) (S S' : Finset (Fin d)),
    (∀ k ∈ D d C w, (k ∈ S ↔ k ∈ S')) → V d C S w = V d C S' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro S S' hSS
  rcases wire_cases d C w with h | h | h | ⟨j, hj, rfl⟩ | h
  · rw [V_input d C S w h, V_input d C S' w h]
    have := hSS ⟨w, h⟩ (by rw [D_input d C w h]; exact Finset.mem_singleton_self _)
    simp only [this]
  · subst h; rw [V_d, V_d]
  · subst h; rw [V_d1, V_d1]
  · rw [V_gate d C hrb S j hj, V_gate d C hrb S' j hj]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hlt : i < d + 2 + j := hrb j hj i hi
    exact ih i hlt S S' fun k hk => hSS k ((D_gate d C hrb j hj k).2 ⟨i, hi, hk⟩)
  · rw [V_big d C S w h, V_big d C S' w h]

theorem ops (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hnot : PEqualNP.NotBracket.notCount C = 0)
    (j : ℕ) (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧ (gateAt C j).inputs.length ≤ 2 := by
  rw [gateAt_eq C j hj]
  have hm : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have h1 := (hfan _ hm).1
  have h2 : C.gates[j].op ≠ GateOp.not := by
    intro hn
    unfold PEqualNP.NotBracket.notCount at hnot
    have h0 := List.eq_nil_of_length_eq_zero hnot
    rw [List.filter_eq_nil_iff] at h0
    exact h0 _ hm (by simp [hn])
  refine ⟨?_, (hfan _ hm).2⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h2

theorem V_mono (hrb : ReadsBack (d + 2) C)
    (hop : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) :
    ∀ (w : ℕ) (S S' : Finset (Fin d)), S ⊆ S' → V d C S w = true → V d C S' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro S S' hSS hv
  rcases wire_cases d C w with h | h | h | ⟨j, hj, rfl⟩ | h
  · rw [V_input d C S w h] at hv; rw [V_input d C S' w h]
    simp only [decide_eq_true_eq] at hv ⊢
    exact hSS hv
  · subst h; rw [V_d] at hv; exact absurd hv (by simp)
  · subst h; exact V_d1 d C S'
  · rw [V_gate d C hrb S j hj] at hv; rw [V_gate d C hrb S' j hj]
    rcases hop j hj with ho | ho <;> rw [ho] at hv ⊢
    · simp only [GateOp.eval, List.all_eq_true, List.mem_map] at hv ⊢
      rintro _ ⟨i, hi, rfl⟩
      exact ih i (hrb j hj i hi) S S' hSS (hv _ ⟨i, hi, rfl⟩)
    · simp only [GateOp.eval, List.any_eq_true, List.mem_map] at hv ⊢
      obtain ⟨_, ⟨i, hi, rfl⟩, hv⟩ := hv
      exact ⟨_, ⟨i, hi, rfl⟩, ih i (hrb j hj i hi) S S' hSS hv⟩
  · rw [V_big d C S w h] at hv; exact absurd hv (by simp)

theorem cone_le (hrb : ReadsBack (d + 2) C) {w : ℕ} (h : Cone d C w) : w ≤ C.output := by
  induction h with
  | out => exact le_rfl
  | read j w hj _ hw ih => have := hrb j hj w hw; omega

theorem cone_lt (hrb : ReadsBack (d + 2) C) (hout : C.output < d + 2 + C.gates.length) {w : ℕ}
    (h : Cone d C w) : w < d + 2 + C.gates.length :=
  lt_of_le_of_lt (cone_le d C hrb h) hout

theorem reach_le (hrb : ReadsBack (d + 2) C) {c u : ℕ} (h : Reach d C c u) : c ≤ u := by
  induction h with
  | refl => exact le_rfl
  | step c u j hj hc _ ih => have := hrb j hj c hc; omega

theorem reach_cone {c u : ℕ} (h : Reach d C c u) (hu : Cone d C u) : Cone d C c := by
  induction h with
  | refl => exact hu
  | step c u j hj hc _ ih => exact Cone.read j c hj (ih hu) hc

theorem reach_trans {a b c : ℕ} (h1 : Reach d C a b) (h2 : Reach d C b c) : Reach d C a c := by
  induction h1 with
  | refl => exact h2
  | step a b j hj ha _ ih => exact Reach.step a c j hj ha (ih h2)

theorem cone_D (hrb : ReadsBack (d + 2) C) {w : ℕ} (h : Cone d C w) : D d C w ⊆ D d C C.output := by
  induction h with
  | out => exact Finset.Subset.refl _
  | read j w hj _ hw ih => exact fun k hk => ih ((D_gate d C hrb j hj k).2 ⟨w, hw, hk⟩)

theorem D_cone (hrb : ReadsBack (d + 2) C) :
    ∀ w, Cone d C w → ∀ k ∈ D d C w, Cone d C k.val := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw k hk
  rcases D_form d C hrb w k hk with h | ⟨j, hj, rfl⟩
  · exact h ▸ hw
  · obtain ⟨i, hi, hki⟩ := (D_gate d C hrb j hj k).1 hk
    exact ih i (hrb j hj i hi) (Cone.read j i hj hw hi) k hki

noncomputable def G : Finset ℕ :=
  @Finset.filter ℕ (fun j => Cone d C (d + 2 + j)) (fun _ => Classical.propDecidable _)
    (Finset.range C.gates.length)

theorem mem_G {j : ℕ} : j ∈ G d C ↔ j < C.gates.length ∧ Cone d C (d + 2 + j) := by
  classical
  unfold G; rw [Finset.mem_filter, Finset.mem_range]

noncomputable def usesK (w : ℕ) : ℕ :=
  (∑ j ∈ G d C, (gateAt C j).inputs.count w) + (if C.output = w then 1 else 0)

theorem usesK_pos {w : ℕ} (h : Cone d C w) : 1 ≤ usesK d C w := by
  cases h with
  | out => unfold usesK; simp
  | read j w hj hc hw =>
    unfold usesK
    have hjG : j ∈ G d C := (mem_G d C).2 ⟨hj, hc⟩
    have h1 : 1 ≤ (gateAt C j).inputs.count w := List.count_pos_iff.2 hw
    have h2 := Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count w)
      (fun _ _ => Nat.zero_le _) hjG
    omega

theorem usesK_two (j1 j2 c : ℕ) (h1 : j1 ∈ G d C) (h2 : j2 ∈ G d C) (hne : j1 ≠ j2)
    (c1 : c ∈ (gateAt C j1).inputs) (c2 : c ∈ (gateAt C j2).inputs) : 2 ≤ usesK d C c := by
  unfold usesK
  have hsub : ({j1, j2} : Finset ℕ) ⊆ G d C := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have := Finset.sum_le_sum_of_subset (f := fun j => (gateAt C j).inputs.count c) hsub
  rw [Finset.sum_pair hne] at this
  have a1 := List.count_pos_iff.2 c1
  have a2 := List.count_pos_iff.2 c2
  omega

theorem usesK_dup (j c : ℕ) (h : j ∈ G d C) (hc : 2 ≤ (gateAt C j).inputs.count c) :
    2 ≤ usesK d C c := by
  unfold usesK
  have h2 := Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count c)
    (fun _ _ => Nat.zero_le _) h
  omega

theorem sum_map_list (f : Gate → ℕ) : ∀ l : List Gate,
    (l.map f).sum = ∑ j ∈ Finset.range l.length, f (l.getD j ⟨GateOp.or, []⟩)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_list f l, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

theorem usesK_le (w : ℕ) : usesK d C w ≤
    (C.gates.map (fun g => g.inputs.count w)).sum + (if C.output = w then 1 else 0) := by
  unfold usesK
  rw [sum_map_list]
  have hsub : G d C ⊆ Finset.range C.gates.length := fun j hj =>
    Finset.mem_range.2 ((mem_G d C).1 hj).1
  exact Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsub) _

theorem sum_count_range (N : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x < N) →
    ∑ w ∈ Finset.range N, l.count w = l.length
  | [], _ => by simp
  | a :: l, hl => by
    have ih := sum_count_range N l (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    have ha : a < N := hl a List.mem_cons_self
    simp only [List.count_cons, Finset.sum_add_distrib, ih, List.length_cons, beq_iff_eq]
    rw [Finset.sum_ite_eq]
    simp [ha]

theorem count_bound (hrb : ReadsBack (d + 2) C)
    (hfan2 : ∀ j < C.gates.length, (gateAt C j).inputs.length ≤ 2)
    (hout : C.output < d + 2 + C.gates.length) (hrel : ∀ i : Fin d, Cone d C i.val)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Cone d C q ∧ 2 ≤ usesK d C q) :
    Q.card + d ≤ C.gates.length + 1 := by
  classical
  let K := (Finset.range (d + 2 + C.gates.length)).filter (fun w => Cone d C w)
  have hQK : Q ⊆ K := fun q hq =>
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (cone_lt d C hrb hout (hQ q hq).1), (hQ q hq).1⟩
  have htot : ∑ w ∈ Finset.range (d + 2 + C.gates.length), usesK d C w =
      (∑ j ∈ G d C, (gateAt C j).inputs.length) + 1 := by
    unfold usesK
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' := (mem_G d C).1 hj
      exact sum_count_range _ _ (fun x hx => by have := hrb j hj'.1 x hx; omega)
    · rw [Finset.sum_ite_eq]
      simp only [Finset.mem_range, hout, ite_true]
  have hlen : (∑ j ∈ G d C, (gateAt C j).inputs.length) ≤ 2 * (G d C).card := by
    calc (∑ j ∈ G d C, (gateAt C j).inputs.length) ≤ ∑ _j ∈ G d C, 2 :=
          Finset.sum_le_sum fun j hj => hfan2 j ((mem_G d C).1 hj).1
      _ = 2 * (G d C).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hK : Q.card + K.card ≤ ∑ w ∈ Finset.range (d + 2 + C.gates.length), usesK d C w := by
    have h1 : ∑ w ∈ K, usesK d C w ≤ ∑ w ∈ Finset.range (d + 2 + C.gates.length), usesK d C w :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have h2 : ∑ w ∈ K, (1 + if w ∈ Q then 1 else 0) ≤ ∑ w ∈ K, usesK d C w :=
      Finset.sum_le_sum fun w hw => by
        have hc := (Finset.mem_filter.1 hw).2
        split_ifs with hq
        · exact (hQ w hq).2
        · have := usesK_pos d C hc; omega
    have h3 : ∑ w ∈ K, (1 + if w ∈ Q then 1 else 0) = K.card + Q.card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_boole,
        Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hQK]
      simp
    omega
  have hKc : d + (G d C).card ≤ K.card := by
    have hdisj : Disjoint (Finset.range d) ((G d C).image (fun j => d + 2 + j)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_range] at ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hb
      omega
    have hsub : Finset.range d ∪ (G d C).image (fun j => d + 2 + j) ⊆ K := by
      intro w hw
      rw [Finset.mem_union] at hw
      rcases hw with hw | hw
      · have hwd := Finset.mem_range.1 hw
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hrel ⟨w, hwd⟩⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
        have := (mem_G d C).1 hj
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), this.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range,
      Finset.card_image_of_injective _ (add_right_injective _)] at this
    exact this
  have hGc : (G d C).card ≤ C.gates.length := by
    have : G d C ⊆ Finset.range C.gates.length := fun j hj =>
      Finset.mem_range.2 ((mem_G d C).1 hj).1
    simpa using Finset.card_le_card this
  omega

theorem erase_sub {S T : Finset (Fin d)} {i : Fin d} (h : S \ T = {i}) : S.erase i ⊆ T := by
  intro k hk
  rw [Finset.mem_erase] at hk
  by_contra hkT
  have : k ∈ S \ T := Finset.mem_sdiff.2 ⟨hk.2, hkT⟩
  rw [h, Finset.mem_singleton] at this
  exact hk.1 this

theorem sub_insert {S T : Finset (Fin d)} {i : Fin d} (h : S \ T = {i}) : S ⊆ insert i T := by
  intro k hk
  rw [Finset.mem_insert]
  by_cases hkT : k ∈ T
  · exact Or.inr hkT
  · have : k ∈ S \ T := Finset.mem_sdiff.2 ⟨hk, hkT⟩
    rw [h, Finset.mem_singleton] at this
    exact Or.inl this

theorem relevant (hrb : ReadsBack (d + 2) C)
    (hop : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or)
    (hh ll : ℕ) (H : Fin hh → Finset (Fin d)) (L : Fin ll → Finset (Fin d))
    (hforced : ∀ i, ∃ x y, H x \ L y = {i})
    (hH : ∀ x, V d C (H x) C.output = true) (hL : ∀ y, V d C (L y) C.output = false)
    (i : Fin d) : Cone d C i.val := by
  by_contra hc
  obtain ⟨x, y, hxy⟩ := hforced i
  have hni : i ∉ D d C C.output := fun hi => hc (D_cone d C hrb _ Cone.out i hi)
  have h1 : V d C (H x) C.output = V d C ((H x).erase i) C.output :=
    V_local d C hrb _ _ _ fun k hk => by
      have : k ≠ i := fun h => hni (h ▸ hk)
      simp [Finset.mem_erase, this]
  have := V_mono d C hrb hop _ _ _ (erase_sub d hxy) (h1 ▸ hH x)
  rw [hL y] at this
  exact absurd this (by simp)

theorem reach_of (hrb : ReadsBack (d + 2) C) (i : Fin d)
    (Hi : ∀ w, Cone d C w → i ∈ D d C w → usesK d C w ≤ 1) :
    ∀ w u, Cone d C u → Cone d C w → u < w → i ∈ D d C u → i ∈ D d C w → Reach d C u w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro u hu hw huw hiu hiw
  rcases D_form d C hrb w i hiw with h | ⟨j, hj, rfl⟩
  · have := D_le d C hrb u i hiu; omega
  · obtain ⟨c, hc, hic⟩ := (D_gate d C hrb j hj i).1 hiw
    have hcc : Cone d C c := Cone.read j c hj hw hc
    have hcw : c < d + 2 + j := hrb j hj c hc
    have hstep : Reach d C c (d + 2 + j) := Reach.step c _ j hj hc (Reach.refl _)
    rcases lt_trichotomy u c with h | h | h
    · exact reach_trans d C (ih c hcw u hu hcc h hiu hic) hstep
    · subst h; exact hstep
    · have hr := ih u huw c hcc hu h hic hiu
      cases hr with
      | refl => omega
      | step _ _ j' hj' hc' hr' =>
        have h1 := reach_le d C hrb hr'
        have h2 : 2 ≤ usesK d C c := usesK_two d C j' j c
          ((mem_G d C).2 ⟨hj', reach_cone d C hr' hu⟩) ((mem_G d C).2 ⟨hj, hw⟩) (by omega) hc' hc
        have := Hi c hcc hic
        omega

theorem dom (hrb : ReadsBack (d + 2) C) (i : Fin d)
    (Hi : ∀ w, Cone d C w → i ∈ D d C w → usesK d C w ≤ 1)
    (g : ℕ) (hg : Cone d C g) (hig : i ∈ D d C g) (T T' : Finset (Fin d))
    (hTT : ∀ k, k ≠ i → (k ∈ T ↔ k ∈ T')) (heq : V d C T g = V d C T' g) :
    ∀ w, Cone d C w → g ≤ w → V d C T w = V d C T' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hgw
  by_cases hiw : i ∈ D d C w
  swap
  · exact V_local d C hrb w T T' fun k hk => hTT k (fun h => hiw (h ▸ hk))
  rcases Nat.eq_or_lt_of_le hgw with h | h
  · subst h; exact heq
  rcases D_form d C hrb w i hiw with h' | ⟨j, hj, rfl⟩
  · have := D_le d C hrb g i hig; omega
  · rw [V_gate d C hrb T j hj, V_gate d C hrb T' j hj]
    congr 1
    refine List.map_congr_left fun c hc => ?_
    have hcw := hrb j hj c hc
    by_cases hic : i ∈ D d C c
    swap
    · exact V_local d C hrb c T T' fun k hk => hTT k (fun h => hic (h ▸ hk))
    have hcc : Cone d C c := Cone.read j c hj hw hc
    by_cases hgc : g ≤ c
    · exact ih c hcw hcc hgc
    · have hr := reach_of d C hrb i Hi g c hcc hg (by omega) hic hig
      cases hr with
      | refl => omega
      | step _ _ j' hj' hc' hr' =>
        have h1 := reach_le d C hrb hr'
        have h2 := usesK_two d C j' j c ((mem_G d C).2 ⟨hj', reach_cone d C hr' hg⟩)
          ((mem_G d C).2 ⟨hj, hw⟩) (by omega) hc' hc
        have := Hi c hcc hic
        omega

theorem pivot (hrb : ReadsBack (d + 2) C)
    (hop : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or)
    (i : Fin d) (Hi : ∀ w, Cone d C w → i ∈ D d C w → usesK d C w ≤ 1)
    (g : ℕ) (hg : Cone d C g) (hig : i ∈ D d C g) (T T' : Finset (Fin d)) (hsub : T ⊆ T')
    (hTT : ∀ k, k ≠ i → (k ∈ T ↔ k ∈ T'))
    (h0 : V d C T C.output = false) (h1 : V d C T' C.output = true) :
    V d C T g = false ∧ V d C T' g = true := by
  have hne : V d C T g ≠ V d C T' g := fun he => by
    have := dom d C hrb i Hi g hg hig T T' hTT he C.output Cone.out (cone_le d C hrb hg)
    rw [h0, h1] at this
    exact absurd this (by simp)
  rcases Bool.eq_false_or_eq_true (V d C T g) with hT | hT
  · exact absurd (hT.trans (V_mono d C hrb hop g T T' hsub hT).symm) hne
  · refine ⟨hT, ?_⟩
    rcases Bool.eq_false_or_eq_true (V d C T' g) with hT' | hT'
    · exact hT'
    · exact absurd (hT.trans hT'.symm) hne

theorem excl (hrb : ReadsBack (d + 2) C) (k : Fin d)
    (Hk : ∀ w, Cone d C w → k ∈ D d C w → usesK d C w ≤ 1)
    (j : ℕ) (hj : j < C.gates.length) (hwg : Cone d C (d + 2 + j)) (a b : ℕ) (hab : a < b)
    (ha : a ∈ (gateAt C j).inputs) (hb : b ∈ (gateAt C j).inputs)
    (hka : k ∈ D d C a) (hkb : k ∈ D d C b) : False := by
  have hca : Cone d C a := Cone.read j a hj hwg ha
  have hcb : Cone d C b := Cone.read j b hj hwg hb
  have hbg := hrb j hj b hb
  have hr := reach_of d C hrb k Hk b a hca hcb hab hka hkb
  cases hr with
  | refl => omega
  | step _ _ j' hj' hc' hr' =>
    have h1 := reach_le d C hrb hr'
    have h2 := usesK_two d C j' j a ((mem_G d C).2 ⟨hj', reach_cone d C hr' hcb⟩)
      ((mem_G d C).2 ⟨hj, hwg⟩) (by omega) hc' ha
    have := Hk a hca hka
    omega

theorem no_obs (hrb : ReadsBack (d + 2) C)
    (hop : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or)
    (hfan2 : ∀ j < C.gates.length, (gateAt C j).inputs.length ≤ 2)
    (hh ll : ℕ) (H : Fin hh → Finset (Fin d)) (L : Fin ll → Finset (Fin d))
    (hH : ∀ x, V d C (H x) C.output = true) (hL : ∀ y, V d C (L y) C.output = false)
    (hrel : ∀ i : Fin d, Cone d C i.val)
    (S : Finset (Fin d)) (hcard : 2 ≤ S.card)
    (hrow : ∀ U : Finset (Fin d), U.Nonempty → U ⊂ S → ∃ i ∈ U, ∃ j ∈ S \ U,
      ∃ x y z, H x \ L y = {i} ∧ H x \ L z = {j})
    (hcol : ∀ U : Finset (Fin d), U.Nonempty → U ⊂ S → ∃ i ∈ U, ∃ j ∈ S \ U,
      ∃ x y z, H x \ L z = {i} ∧ H y \ L z = {j})
    (hS : ∀ i ∈ S, ∀ w, Cone d C w → i ∈ D d C w → usesK d C w ≤ 1) : False := by
  classical
  have hex : ∃ w, Cone d C w ∧ S ⊆ D d C w := ⟨C.output, Cone.out, fun k _ =>
    cone_D d C hrb (hrel k) (by rw [D_input d C k.val k.isLt]; simp)⟩
  have hg : Cone d C (Nat.find hex) ∧ S ⊆ D d C (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ w < Nat.find hex, ¬ (Cone d C w ∧ S ⊆ D d C w) := fun w hw => Nat.find_min hex hw
  obtain ⟨s0, hs0⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  rcases D_form d C hrb _ s0 (hg.2 hs0) with hgi | ⟨j, hj, hgj⟩
  · have hgd : Nat.find hex < d := by rw [hgi]; exact s0.isLt
    have := Finset.card_le_card hg.2
    rw [D_input d C _ hgd, Finset.card_singleton] at this
    omega
  rw [hgj] at hg hmin
  have hwg := hg.1
  have hSg := hg.2
  have hmin' : ∀ w < d + 2 + j, Cone d C w → ¬ S ⊆ D d C w := fun w hw hc hs => hmin w hw ⟨hc, hs⟩
  have hl2 := hfan2 j hj
  have hops := hop j hj
  have hmemD := D_gate d C hrb j hj
  have hVg : ∀ T, V d C T (d + 2 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V d C T)) :=
    fun T => V_gate d C hrb T j hj
  have hrbj : ∀ c ∈ (gateAt C j).inputs, c < d + 2 + j := hrb j hj
  have hconej : ∀ c ∈ (gateAt C j).inputs, Cone d C c := fun c hc => Cone.read j c hj hwg hc
  have hexcl : ∀ k : Fin d, (∀ w, Cone d C w → k ∈ D d C w → usesK d C w ≤ 1) → ∀ a b : ℕ, a < b →
      a ∈ (gateAt C j).inputs → b ∈ (gateAt C j).inputs → k ∈ D d C a → k ∈ D d C b → False :=
    fun k Hk a b h ha hb => excl d C hrb k Hk j hj hwg a b h ha hb
  have hjG : j ∈ G d C := (mem_G d C).2 ⟨hj, hwg⟩
  have hdup := usesK_dup d C j
  generalize hinp : (gateAt C j).inputs = inp at hmemD hVg hrbj hconej hl2 hexcl hdup
  rcases inp with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · obtain ⟨i, hi, _⟩ := (hmemD s0).1 (hSg hs0)
    simp at hi
  · apply hmin' a (hrbj a (by simp)) (hconej a (by simp))
    intro k hk
    obtain ⟨i, hi, hki⟩ := (hmemD k).1 (hSg hk)
    rw [List.mem_singleton] at hi
    exact hi ▸ hki
  · have ha := hconej a (by simp)
    have hb := hconej b (by simp)
    have hag := hrbj a (by simp)
    have hbg := hrbj b (by simp)
    have hab : ∀ k ∈ S, k ∈ D d C a ∨ k ∈ D d C b := by
      intro k hk
      obtain ⟨i, hi, hki⟩ := (hmemD k).1 (hSg hk)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact Or.inl hki
      · exact Or.inr hki
    let U := S.filter (fun k => k ∈ D d C a)
    have hmU : ∀ k, k ∈ U ↔ k ∈ S ∧ k ∈ D d C a := fun k => Finset.mem_filter
    have hUne : U.Nonempty := by
      by_contra hne
      apply hmin' b hbg hb
      intro k hk
      rcases hab k hk with h | h
      · exact absurd ⟨k, (hmU k).2 ⟨hk, h⟩⟩ hne
      · exact h
    have hUS : U ⊂ S := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, fun he => ?_⟩
      apply hmin' a hag ha
      intro k hk
      rw [← he] at hk
      exact ((hmU k).1 hk).2
    have hnb : ∀ k ∈ U, k ∉ D d C b := by
      intro k hk hkb
      have hkS := ((hmU k).1 hk).1
      have hka := ((hmU k).1 hk).2
      rcases lt_trichotomy a b with h | h | h
      · exact hexcl k (hS k hkS) a b h (by simp) (by simp) hka hkb
      · subst h
        have := hdup a hjG (by simp)
        have := hS k hkS a ha hka
        omega
      · exact hexcl k (hS k hkS) b a h (by simp) (by simp) hkb hka
    have hna : ∀ k ∈ S \ U, k ∉ D d C a ∧ k ∈ D d C b := by
      intro k hk
      rw [Finset.mem_sdiff] at hk
      have hka : k ∉ D d C a := fun h => hk.2 ((hmU k).2 ⟨hk.1, h⟩)
      exact ⟨hka, (hab k hk.1).resolve_left hka⟩
    have hgD : ∀ k ∈ S, k ∈ D d C (d + 2 + j) := fun k hk => hSg hk
    rcases hops with hand | hor
    · -- AND gate: columns
      obtain ⟨i, hiU, k, hkSU, x, y, z, hxz, hyz⟩ := hcol U hUne hUS
      have hiS := ((hmU i).1 hiU).1
      have hkS := (Finset.mem_sdiff.1 hkSU).1
      have ins_agree : ∀ m : Fin d, ∀ k' : Fin d, k' ≠ m → (k' ∈ L z ↔ k' ∈ insert m (L z)) :=
        fun m k' hk' => by rw [Finset.mem_insert]; simp [hk']
      have hp1 := pivot d C hrb hop i (hS i hiS) _ hwg (hgD i hiS) (L z) (insert i (L z))
        (Finset.subset_insert _ _) (ins_agree i) (hL z)
        (V_mono d C hrb hop _ _ _ (sub_insert d hxz) (hH x))
      have hp2 := pivot d C hrb hop k (hS k hkS) _ hwg (hgD k hkS) (L z) (insert k (L z))
        (Finset.subset_insert _ _) (ins_agree k) (hL z)
        (V_mono d C hrb hop _ _ _ (sub_insert d hyz) (hH y))
      have e1 := hp1.2
      have e2 := hp2.2
      have e0 := hp1.1
      rw [hVg, hand] at e0 e1 e2
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
        Bool.and_true, Bool.and_eq_true] at e0 e1 e2
      have hb' : V d C (L z) b = true := by
        rw [V_local d C hrb b (L z) (insert i (L z)) fun m hm =>
          ins_agree i m (fun h => hnb i hiU (h ▸ hm))]
        exact e1.2
      have ha' : V d C (L z) a = true := by
        rw [V_local d C hrb a (L z) (insert k (L z)) fun m hm =>
          ins_agree k m (fun h => (hna k hkSU).1 (h ▸ hm))]
        exact e2.1
      rw [ha', hb'] at e0
      simp at e0
    · -- OR gate: rows
      obtain ⟨i, hiU, k, hkSU, x, y, z, hxy, hxz⟩ := hrow U hUne hUS
      have hiS := ((hmU i).1 hiU).1
      have hkS := (Finset.mem_sdiff.1 hkSU).1
      have er_agree : ∀ m : Fin d, ∀ k' : Fin d, k' ≠ m → (k' ∈ (H x).erase m ↔ k' ∈ H x) :=
        fun m k' hk' => by rw [Finset.mem_erase]; simp [hk']
      have hlow : ∀ m y', H x \ L y' = {m} → V d C ((H x).erase m) C.output = false := by
        intro m y' hm
        rcases Bool.eq_false_or_eq_true (V d C ((H x).erase m) C.output) with h | h
        · have := V_mono d C hrb hop _ _ _ (erase_sub d hm) h
          rw [hL y'] at this
          exact absurd this (by simp)
        · exact h
      have hp1 := pivot d C hrb hop i (hS i hiS) _ hwg (hgD i hiS) ((H x).erase i) (H x)
        (Finset.erase_subset _ _) (er_agree i) (hlow i y hxy) (hH x)
      have hp2 := pivot d C hrb hop k (hS k hkS) _ hwg (hgD k hkS) ((H x).erase k) (H x)
        (Finset.erase_subset _ _) (er_agree k) (hlow k z hxz) (hH x)
      have e1 := hp1.1
      have e2 := hp2.1
      have e0 := hp1.2
      rw [hVg, hor] at e0 e1 e2
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false, Bool.or_eq_false_iff] at e0 e1 e2
      have hb' : V d C (H x) b = false := by
        rw [← V_local d C hrb b ((H x).erase i) (H x) fun m hm =>
          er_agree i m (fun h => hnb i hiU (h ▸ hm))]
        exact e1.2
      have ha' : V d C (H x) a = false := by
        rw [← V_local d C hrb a ((H x).erase k) (H x) fun m hm =>
          er_agree k m (fun h => (hna k hkSU).1 (h ▸ hm))]
        exact e2.1
      rw [ha', hb'] at e0
      simp at e0
  · simp at hl2

theorem main (d hh ll : ℕ) (H : Fin hh → Finset (Fin d)) (L : Fin ll → Finset (Fin d))
    (hforced : ∀ i, ∃ x y, H x \ L y = {i}) (C : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hrb : ReadsBack (d + 2) C)
    (hnot : PEqualNP.NotBracket.notCount C = 0) (hout : C.output < d + 2 + C.size)
    (hH : ∀ x, V d C (H x) C.output = true) (hL : ∀ y, V d C (L y) C.output = false) :
    ∃ Q : Finset (Fin (d + 2 + C.size)), Q.card + d ≤ C.size + 1 ∧
      (∀ q ∈ Q, 2 ≤ (C.gates.map (fun g => g.inputs.count q.val)).sum +
        (if C.output = q.val then 1 else 0)) ∧
      ∀ S : Finset (Fin d), (2 ≤ S.card ∧
        (∀ U : Finset (Fin d), U.Nonempty → U ⊂ S → ∃ i ∈ U, ∃ j ∈ S \ U,
          ∃ x y z, H x \ L y = {i} ∧ H x \ L z = {j}) ∧
        (∀ U : Finset (Fin d), U.Nonempty → U ⊂ S → ∃ i ∈ U, ∃ j ∈ S \ U,
          ∃ x y z, H x \ L z = {i} ∧ H y \ L z = {j})) →
        ∃ q ∈ Q, (S ∩ D d C q.val).Nonempty := by
  classical
  have hop : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
    fun j hj => (ops C hfan hnot j hj).1
  have hfan2 : ∀ j < C.gates.length, (gateAt C j).inputs.length ≤ 2 :=
    fun j hj => (ops C hfan hnot j hj).2
  have hout' : C.output < d + 2 + C.gates.length := hout
  have hrel := relevant d C hrb hop hh ll H L hforced hH hL
  refine ⟨Finset.univ.filter (fun q : Fin (d + 2 + C.size) => Cone d C q.val ∧ 2 ≤ usesK d C q.val),
    ?_, ?_, ?_⟩
  · have := count_bound d C hrb hfan2 hout' hrel
      ((Finset.univ.filter (fun q : Fin (d + 2 + C.size) => Cone d C q.val ∧ 2 ≤ usesK d C q.val)).map
        Fin.valEmbedding) (fun q hq => by
          rw [Finset.mem_map] at hq
          obtain ⟨q', hq', rfl⟩ := hq
          exact (Finset.mem_filter.1 hq').2)
    rw [Finset.card_map] at this
    exact this
  · intro q hq
    exact le_trans (Finset.mem_filter.1 hq).2.2 (usesK_le d C q.val)
  · rintro S ⟨hcard, hrow, hcol⟩
    by_contra hno
    push Not at hno
    apply no_obs d C hrb hop hfan2 hh ll H L hH hL hrel S hcard hrow hcol
    intro i hi w hw hiw
    by_contra hlt
    push Not at hlt
    have hq : (⟨w, cone_lt d C hrb hout' hw⟩ : Fin (d + 2 + C.size)) ∈
        Finset.univ.filter (fun q : Fin (d + 2 + C.size) => Cone d C q.val ∧ 2 ≤ usesK d C q.val) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hw, hlt⟩
    have := hno _ hq
    have hmem : i ∈ S ∩ D d C w := Finset.mem_inter.2 ⟨hi, hiw⟩
    rw [this] at hmem
    simp at hmem

end Main

end PEqualNP.Outside.L_lib_1389

theorem PEqualNP.Outside.L_lib_1389 :
∀ (d h l : Nat) (H : Fin h → Finset (Fin d)) (L : Fin l → Finset (Fin d)),
  let forced := fun (i : Fin d) (x : Fin h) (y : Fin l) => H x \ L y = {i}
  let row := fun i j => ∃ x y z, forced i x y ∧ forced j x z
  let col := fun i j => ∃ x y z, forced i x z ∧ forced j y z
  let conn := fun (S : Finset (Fin d)) (edge : Fin d → Fin d → Prop) =>
    ∀ U : Finset (Fin d), U.Nonempty → U ⊂ S → ∃ i ∈ U, ∃ j ∈ S \ U, edge i j
  let obstruction := fun (S : Finset (Fin d)) => 2 ≤ S.card ∧ conn S row ∧ conn S col
  (∀ i, ∃ x y, forced i x y) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C →
    PEqualNP.NotBracket.notCount C = 0 → C.output < d+2+C.size →
    let val := fun (S : Finset (Fin d)) =>
      C.eval (List.ofFn (fun i : Fin d => decide (i ∈ S)) ++ [false,true])
    (∀ x, val (H x) = true) → (∀ y, val (L y) = false) →
    let uses := fun (w : Nat) => (C.gates.map (fun g => g.inputs.count w)).sum +
      (if C.output = w then 1 else 0)
    let dep := C.gates.foldl (fun (ws : List (Finset (Fin d))) g =>
      ws ++ [g.inputs.foldl (fun S i => S ∪ ws.getD i ∅) ∅])
      (List.ofFn (fun i : Fin d => ({i} : Finset (Fin d))) ++ [∅,∅])
    ∃ Q : Finset (Fin (d+2+C.size)), Q.card+d ≤ C.size+1 ∧
      (∀ q ∈ Q, 2 ≤ uses q.val) ∧
      ∀ S : Finset (Fin d), obstruction S → ∃ q ∈ Q, (S ∩ dep.getD q.val ∅).Nonempty := by
  intro d h l H L forced row col conn obstruction hforced C hfan hrb hnot hout val hH hL uses dep
  exact PEqualNP.Outside.L_lib_1389.main d h l H L hforced C hfan hrb hnot hout hH hL
