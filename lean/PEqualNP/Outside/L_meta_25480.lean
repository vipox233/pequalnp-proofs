import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25480

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

theorem row_get {n : ℕ} (u : Fin n) (m i : ℕ) :
    (List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false).getD i false =
      decide (i = u.val) := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_ofFn, h, dite_true, Option.getD_some, Fin.ext_iff]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_replicate]
    symm
    rw [decide_eq_false (by omega)]
    split_ifs <;> rfl

theorem col_get {m : ℕ} (v : Fin m) (n i : ℕ) :
    (List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))).getD i false =
      decide (i = n + v.val) := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_replicate, h, if_true, Option.getD_some]
    symm
    apply decide_eq_false
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp only [h2, dite_true, Option.getD_some, Fin.ext_iff]
      apply decide_eq_decide.2
      constructor <;> intro hh <;> omega
    · simp only [h2, dite_false, Option.getD_none]
      symm
      apply decide_eq_false
      omega

theorem mono (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C) (X Y : List Bool)
    (hl : X.length = Y.length)
    (hXY : ∀ j, X.getD j false = true → Y.getD j false = true) (j : ℕ) :
    (C.wires X).getD j false = true → (C.wires Y).getD j false = true := by
  show (C.gates.foldl stp X).getD j false = true → (C.gates.foldl stp Y).getD j false = true
  have hrun := run (fun j bb => bb = true → (C.gates.foldl stp Y).getD j false = true) C.gates X
    (by
      intro j hj h
      rw [pre _ _ _ (by omega)]
      exact hXY j h)
    (by
      intro r hr w hw hrel
      have hv := vgate C.gates Y r hr
      rw [← hl] at hv
      rw [hv]
      have key : ∀ a ∈ (C.gates[r]).inputs, (fun p q : Bool => p = true → q = true) (w.getD a false)
          (if a < X.length + r then (C.gates.foldl stp Y).getD a false else false) := by
        intro a _
        by_cases ha : a < X.length + r
        · rw [if_pos ha]; exact hrel a ha
        · rw [getD_ge w a (by omega)]; intro h; exact absurd h (by simp)
      rcases hC _ (List.getElem_mem hr) with h | h
      · simp only [h, GateOp.eval]
        exact allP (fun p q : Bool => p = true → q = true) (fun h => h) p1and _ _ _ key
      · simp only [h, GateOp.eval]
        exact anyP (fun p q : Bool => p = true → q = true) (fun h => h) p1or _ _ _ key)
  intro h
  by_cases hj : j < X.length + C.gates.length
  · exact hrun j hj h
  · rw [getD_ge _ _ (by rw [flen]; omega)] at h
    exact absurd h (by simp)

theorem gval (C : Circuit) (N : ℕ) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    (X : List Bool) (hX : X.length = N) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires X).getD (N + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun a => (C.wires X).getD a false) := by
  have hv := vgate C.gates X k hk
  rw [hX] at hv
  show (C.gates.foldl stp X).getD (N + k) false = _
  rw [hv]
  congr 1
  apply List.map_congr_left
  intro a ha
  have : a < N + k := by
    apply hrb k hk a
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk]
    exact ha
  rw [if_pos this]
  rfl

theorem bl : ∀ p1 q1 p2 q2 : Bool, ¬ (p1 = false ∧ q1 = false) → ¬ (p2 = false ∧ q2 = false) →
    (p1 && p2) = false → (q1 && q2) = false →
    ((p1 = true ∧ p2 = false ∧ q2 = true ∧ q1 = false) ∨
      (p2 = true ∧ p1 = false ∧ q1 = true ∧ q2 = false)) := by decide

theorem desc (C : Circuit) (n m : ℕ) (hA : PEqualNP.TopForm.IsAO2 (n + m) C)
    (x r c : List Bool) (hx : x.length = n + m) (hr : r.length = n + m) (hc : c.length = n + m)
    (hin : ∀ i < n + m, x.getD i false = true → r.getD i false = true ∨ c.getD i false = true) :
    ∀ w, (C.wires x).getD w false = true → (C.wires r).getD w false = false →
      (C.wires c).getD w false = false →
      ∃ (j : Fin C.gates.length) (a b : ℕ),
        (C.gates.get j).op = GateOp.and ∧ (C.gates.get j).inputs = [a, b] ∧
        (C.wires x).getD (n + m + j.val) false = true ∧
        (((C.wires r).getD a false = true ∧ (C.wires r).getD b false = false ∧
          (C.wires c).getD b false = true ∧ (C.wires c).getD a false = false) ∨
         ((C.wires r).getD b false = true ∧ (C.wires r).getD a false = false ∧
          (C.wires c).getD a false = true ∧ (C.wires c).getD b false = false)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h1 h2 h3
    by_cases hw : w < n + m
    · exfalso
      have e1 : (C.wires x).getD w false = x.getD w false := pre _ _ _ (by omega)
      have e2 : (C.wires r).getD w false = r.getD w false := pre _ _ _ (by omega)
      have e3 : (C.wires c).getD w false = c.getD w false := pre _ _ _ (by omega)
      rw [e1] at h1
      rw [e2] at h2
      rw [e3] at h3
      rcases hin w hw h1 with e | e
      · rw [e] at h2; exact absurd h2 (by simp)
      · rw [e] at h3; exact absurd h3 (by simp)
    by_cases hw2 : w < n + m + C.gates.length
    swap
    · exfalso
      have : (C.wires x).getD w false = false := by
        show (C.gates.foldl stp x).getD w false = false
        exact getD_ge _ _ (by rw [flen]; omega)
      rw [this] at h1
      exact absurd h1 (by simp)
    obtain ⟨k, rfl⟩ : ∃ k, w = n + m + k := ⟨w - (n + m), by omega⟩
    have hk : k < C.gates.length := by omega
    have h1o := h1
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (hA.2.2 _ (List.getElem_mem hk))
    have hrb : ∀ i ∈ (C.gates[k]).inputs, i < n + m + k := by
      intro i hi
      apply hA.2.1 k hk i
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hk]
      exact hi
    have ha : a < n + m + k := hrb a (by rw [hab]; simp)
    have hb : b < n + m + k := hrb b (by rw [hab]; simp)
    rw [gval C (n + m) hA.2.1 x hx k hk, hab] at h1
    rw [gval C (n + m) hA.2.1 r hr k hk, hab] at h2
    rw [gval C (n + m) hA.2.1 c hc k hk, hab] at h3
    rcases hA.1 _ (List.getElem_mem hk) with hop | hop
    · rw [hop] at h1 h2 h3
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
        Bool.and_true] at h1 h2 h3
      rw [Bool.and_eq_true] at h1
      by_cases hfa : (C.wires r).getD a false = false ∧ (C.wires c).getD a false = false
      · exact ih a (by omega) h1.1 hfa.1 hfa.2
      by_cases hfb : (C.wires r).getD b false = false ∧ (C.wires c).getD b false = false
      · exact ih b (by omega) h1.2 hfb.1 hfb.2
      refine ⟨⟨k, hk⟩, a, b, ?_, ?_, h1o, ?_⟩
      · exact hop
      · exact hab
      · rcases bl _ _ _ _ hfa hfb h2 h3 with e | e
        · exact Or.inl ⟨e.1, e.2.1, e.2.2.1, e.2.2.2⟩
        · exact Or.inr ⟨e.1, e.2.1, e.2.2.1, e.2.2.2⟩
    · rw [hop] at h1 h2 h3
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false] at h1 h2 h3
      rw [Bool.or_eq_true] at h1
      rw [Bool.or_eq_false_iff] at h2 h3
      rcases h1 with e | e
      · exact ih a (by omega) e h2.1 h3.1
      · exact ih b (by omega) e h2.2 h3.2

end PEqualNP.Outside.L_meta_25480

open PEqualNP.Outside.L_meta_25480 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25480 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.IsAO2 (n + m) C →
  PEqualNP.Represents.Represents G C →
  ∀ (u : Fin n) (v : Fin m), G u v = true →
    (∃ c : Fin m, G u c = false) → (∃ r : Fin n, G r v = false) →
    let rowOnly := List.ofFn (fun r₀ : Fin n => decide (r₀ = u)) ++ List.replicate m false
    let colOnly := List.replicate n false ++ List.ofFn (fun c₀ : Fin m => decide (c₀ = v))
    let value := fun (x : List Bool) (w : ℕ) => (C.wires x).getD w false
    let split := fun (left right : ℕ) =>
      value rowOnly left = true ∧ value rowOnly right = false ∧
      value colOnly right = true ∧ value colOnly left = false
    ∃ (j : Fin C.gates.length) (a b : ℕ),
      (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (C.gates.get j).inputs = [a, b] ∧
      value (PEqualNP.Represents.oneEach u v) (n + m + j.val) = true ∧
      (split a b ∨ split b a) := by
  intro n m G C hA hrep u v huv hc hr rowOnly colOnly value split
  obtain ⟨c, hc⟩ := hc
  obtain ⟨r, hr⟩ := hr
  have hrowg : ∀ i, rowOnly.getD i false = decide (i = u.val) := fun i => row_get u m i
  have hcolg : ∀ i, colOnly.getD i false = decide (i = n + v.val) := fun i => col_get v n i
  have hrowl : rowOnly.length = n + m := by simp [rowOnly]
  have hcoll : colOnly.length = n + m := by simp [colOnly]
  have hout : (C.wires (PEqualNP.Represents.oneEach u v)).getD C.output false = true := by
    show C.eval _ = true
    rw [hrep]
    exact huv
  have hrow : (C.wires rowOnly).getD C.output false = false := by
    by_contra hne
    rw [Bool.not_eq_false] at hne
    have := mono C hA.1 rowOnly (PEqualNP.Represents.oneEach u c) (by rw [hrowl, oe_len])
      (by
        intro j hj
        rw [hrowg] at hj
        rw [oe_get]
        simp only [decide_eq_true_eq] at hj ⊢
        omega) C.output hne
    have e : C.eval (PEqualNP.Represents.oneEach u c) = true := this
    rw [hrep, hc] at e
    exact absurd e (by simp)
  have hcol : (C.wires colOnly).getD C.output false = false := by
    by_contra hne
    rw [Bool.not_eq_false] at hne
    have := mono C hA.1 colOnly (PEqualNP.Represents.oneEach r v) (by rw [hcoll, oe_len])
      (by
        intro j hj
        rw [hcolg] at hj
        rw [oe_get]
        simp only [decide_eq_true_eq] at hj ⊢
        omega) C.output hne
    have e : C.eval (PEqualNP.Represents.oneEach r v) = true := this
    rw [hrep, hr] at e
    exact absurd e (by simp)
  exact desc C n m hA (PEqualNP.Represents.oneEach u v) rowOnly colOnly (oe_len u v) hrowl hcoll
    (by
      intro i _ hi
      rw [oe_get] at hi
      rw [hrowg, hcolg]
      simp only [decide_eq_true_eq] at hi ⊢
      omega) C.output hout hrow hcol
