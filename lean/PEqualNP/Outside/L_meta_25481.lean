import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25481

open PEqualNP.CircuitLowerBounds

-- helpers stp, getD_snoc, getD_ge, pre, vgate, run, oe_len, allP, anyP, p1and, p1or copied from our parked Pre_L_meta_25458

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem stp_len (W : List Bool) (g : Gate) : (stp W g).length = W.length + 1 := by
  simp [stp]

theorem stp_getD (W : List Bool) (g : Gate) (j : ℕ) : (stp W g).getD j false =
    if j < W.length then W.getD j false else if j = W.length then
      g.op.eval (g.inputs.map fun i => W.getD i false) else false := getD_snoc _ _ _

theorem flen : ∀ (gs : List Gate) (W : List Bool), (gs.foldl stp W).length = W.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro W; simp
  | cons g t ih => intro W; rw [List.foldl_cons, ih, stp_len]; simp; omega

theorem pre : ∀ (gs : List Gate) (W : List Bool) (j : ℕ), j < W.length →
    (gs.foldl stp W).getD j false = W.getD j false := by
  intro gs
  induction gs with
  | nil => intro W j _; rfl
  | cons g t ih =>
    intro W j hj
    rw [List.foldl_cons, ih _ _ (by rw [stp_len]; omega), stp_getD, if_pos hj]

theorem vgate : ∀ (gs : List Gate) (W : List Bool) (r : ℕ) (h : r < gs.length),
    (gs.foldl stp W).getD (W.length + r) false = gs[r].op.eval (gs[r].inputs.map fun a =>
      if a < W.length + r then (gs.foldl stp W).getD a false else false) := by
  intro gs
  induction gs with
  | nil => intro W r h; simp at h
  | cons g t ih =>
    intro W r h
    cases r with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [pre t (stp W g) W.length (by rw [stp_len]; omega), stp_getD, if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro a _
      split_ifs with ha
      · rw [pre t _ a (by rw [stp_len]; omega), stp_getD, if_pos ha]
      · exact getD_ge W a (by omega)
    | succ r =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have := ih (stp W g) r (by simp at h; omega)
      rw [stp_len] at this
      rw [show W.length + (r + 1) = W.length + 1 + r by omega]
      exact this

theorem run (R : ℕ → Bool → Prop) : ∀ (gs : List Gate) (W : List Bool),
    (∀ j < W.length, R j (W.getD j false)) →
    (∀ r (h : r < gs.length) (w : List Bool), w.length = W.length + r →
      (∀ j < W.length + r, R j (w.getD j false)) →
      R (W.length + r) (gs[r].op.eval (gs[r].inputs.map fun a => w.getD a false))) →
    ∀ j < W.length + gs.length, R j ((gs.foldl stp W).getD j false) := by
  intro gs
  induction gs with
  | nil => intro W hW _ j hj; exact hW j (by simpa using hj)
  | cons g t ih =>
    intro W hW H j hj
    rw [List.foldl_cons]
    apply ih (stp W g)
    · intro j' hj'
      rw [stp_len] at hj'
      rw [stp_getD]
      by_cases h1 : j' < W.length
      · rw [if_pos h1]; exact hW j' h1
      · have e : j' = W.length := by omega
        rw [if_neg h1, if_pos e]
        subst e
        have := H 0 (by simp) W (by simp) (by intro j2 hj2; exact hW j2 (by omega))
        simpa using this
    · intro r hr w hw hrel
      rw [stp_len] at hw hrel ⊢
      have := H (r + 1) (by simp; omega) w (by omega) (by intro j2 hj2; exact hrel j2 (by omega))
      rw [show W.length + 1 + r = W.length + (r + 1) by omega]
      simpa using this
    · rw [stp_len]; simp at hj; omega
theorem allP (P : Bool → Bool → Prop) (ht : P true true)
    (hand : ∀ a b c d : Bool, P a b → P c d → P (a && c) (b && d)) :
    ∀ (l : List ℕ) (f1 f2 : ℕ → Bool), (∀ a ∈ l, P (f1 a) (f2 a)) →
      P ((l.map f1).all id) ((l.map f2).all id) := by
  intro l
  induction l with
  | nil => intro f1 f2 _; simpa using ht
  | cons x l ih =>
    intro f1 f2 h
    simp only [List.map_cons, List.all_cons, id]
    exact hand _ _ _ _ (h x (by simp)) (by simpa using ih f1 f2 (fun a ha => h a (by simp [ha])))

theorem anyP (P : Bool → Bool → Prop) (hf : P false false)
    (hor : ∀ a b c d : Bool, P a b → P c d → P (a || c) (b || d)) :
    ∀ (l : List ℕ) (f1 f2 : ℕ → Bool), (∀ a ∈ l, P (f1 a) (f2 a)) →
      P ((l.map f1).any id) ((l.map f2).any id) := by
  intro l
  induction l with
  | nil => intro f1 f2 _; simpa using hf
  | cons x l ih =>
    intro f1 f2 h
    simp only [List.map_cons, List.any_cons, id]
    exact hor _ _ _ _ (h x (by simp)) (by simpa using ih f1 f2 (fun a ha => h a (by simp [ha])))


theorem oe_len {n m : ℕ} (u : Fin n) (v : Fin m) : (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]


theorem p1and : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a && c) = true → (b && d) = true := by decide

theorem p1or : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a || c) = true → (b || d) = true := by decide


theorem oe_get {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_ofFn, h, dite_true, Option.getD_some, Fin.ext_iff]
    apply decide_eq_decide.2
    constructor <;> intro hh <;> omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp only [h2, dite_true, Option.getD_some, Fin.ext_iff]
      apply decide_eq_decide.2
      constructor <;> intro hh <;> omega
    · simp only [h2, dite_false, Option.getD_none]
      symm
      apply decide_eq_false
      omega

end PEqualNP.Outside.L_meta_25481

open PEqualNP.Outside.L_meta_25481 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25481 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (u v : Fin n) (O : ℕ),
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  u ≠ v →
  PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) u.val = 1 →
  C.output ≠ u.val →
  O < n + m + C.gates.length →
  (∀ c : Fin m, (C.wires (PEqualNP.Represents.oneEach v c)).getD O false = true) →
  (¬ Relation.TransGen
    (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧
      ∃ j : Fin C.gates.length, b = n + m + j.val ∧
        a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).inputs)
    u.val C.output) →
  ∀ c : Fin m, G u c = true → G v c = true := by
  intro n m G C u v O hC _ hrep huv _ hout _ hO hpath c hGu
  have hvu : u.val ≠ v.val := fun e => huv (Fin.ext e)
  have hu1 := u.2
  have hc1 := c.2
  have hXl : (PEqualNP.Represents.oneEach u c).length = n + m := oe_len u c
  have hYl : (PEqualNP.Represents.oneEach v c).length = n + m := oe_len v c
  have hOu : O ≠ u.val := by
    intro e
    have h := hO c
    rw [e] at h
    have e2 : (C.wires (PEqualNP.Represents.oneEach v c)).getD u.val false =
        (PEqualNP.Represents.oneEach v c).getD u.val false := pre _ _ _ (by rw [hYl]; omega)
    rw [e2, oe_get] at h
    simp only [decide_eq_true_eq] at h
    omega
  have hOS : ¬ Relation.TransGen
      (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧
        ∃ j : Fin C.gates.length, b = n + m + j.val ∧
          a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).inputs) u.val O := by
    intro h
    cases h with
    | single h => exact h.2.1 rfl
    | tail _ h => exact h.2.1 rfl
  have hrun := run (fun j bb => ¬ (j = u.val ∨ Relation.TransGen
      (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧
        ∃ j : Fin C.gates.length, b = n + m + j.val ∧
          a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).inputs) u.val j) →
      bb = true → (C.gates.foldl stp (PEqualNP.Represents.oneEach v c)).getD j false = true)
    C.gates (PEqualNP.Represents.oneEach u c)
    (by
      intro j hj hS h
      rw [hXl] at hj
      rw [pre _ _ _ (by rw [hYl]; exact hj), oe_get]
      rw [oe_get] at h
      simp only [decide_eq_true_eq] at h ⊢
      have : j ≠ u.val := fun e => hS (Or.inl e)
      omega)
    (by
      intro r hr w hw hrel
      rw [hXl] at hw hrel ⊢
      intro hS h
      by_cases hrO : n + m + r = O
      · rw [hrO]; exact hO c
      have hv := vgate C.gates (PEqualNP.Represents.oneEach v c) r hr
      rw [hYl] at hv
      rw [hv]
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C r = C.gates[r] := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hr]
      have key : ∀ a ∈ (C.gates[r]).inputs, (fun p q : Bool => p = true → q = true) (w.getD a false)
          (if a < n + m + r then (C.gates.foldl stp (PEqualNP.Represents.oneEach v c)).getD a false
            else false) := by
        intro a ha
        by_cases hlt : a < n + m + r
        · rw [if_pos hlt]
          apply hrel a hlt
          intro haS
          apply hS
          right
          have haO : a ≠ O := by
            rcases haS with e | e
            · rw [e]; exact fun h => hOu h.symm
            · intro e2; rw [e2] at e; exact hOS e
          have hedge : (fun a b : ℕ => a ≠ O ∧ b ≠ O ∧
              ∃ j : Fin C.gates.length, b = n + m + j.val ∧
                a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).inputs) a (n + m + r) :=
            ⟨haO, hrO, ⟨r, hr⟩, rfl, by rw [hga]; exact ha⟩
          rcases haS with e | e
          · rw [e] at hedge; exact Relation.TransGen.single hedge
          · exact Relation.TransGen.tail e hedge
        · rw [getD_ge w a (by omega)]; intro h; exact absurd h (by simp)
      have hop := (hC _ (List.getElem_mem hr)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with e | e
      · rw [e] at h ⊢
        simp only [GateOp.eval] at h ⊢
        exact allP (fun p q : Bool => p = true → q = true) (fun h => h) p1and _ _ _ key h
      · rw [e] at h ⊢
        simp only [GateOp.eval] at h ⊢
        exact anyP (fun p q : Bool => p = true → q = true) (fun h => h) p1or _ _ _ key h)
  have hX : (C.gates.foldl stp (PEqualNP.Represents.oneEach u c)).getD C.output false = true := by
    have := hrep u c
    rw [hGu] at this
    exact this
  rw [← hrep v c]
  show (C.gates.foldl stp (PEqualNP.Represents.oneEach v c)).getD C.output false = true
  by_cases hl : C.output < n + m + C.gates.length
  · refine hrun C.output (by rw [hXl]; exact hl) ?_ hX
    rintro (e | e)
    · exact hout e
    · exact hpath e
  · rw [getD_ge _ _ (by rw [flen, hXl]; omega)] at hX
    exact absurd hX (by simp)
