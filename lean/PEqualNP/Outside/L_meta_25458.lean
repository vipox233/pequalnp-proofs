import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25458

open PEqualNP.CircuitLowerBounds

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

def fixg (N k i r : ℕ) (g : Gate) : Gate :=
  if r = k then ⟨g.op, []⟩ else ⟨g.op, g.inputs.map fun a => if k < r ∧ a = N + k then i else a⟩

def red (N k i : ℕ) (C : Circuit) : Circuit :=
  ⟨List.ofFn (fun r : Fin C.gates.length => fixg N k i r.1 (C.gates.get r)),
    if C.output = N + k then i else C.output⟩

def mu (C : Circuit) : ℕ := (C.gates.map fun g => g.inputs.length).sum

theorem red_len (N k i : ℕ) (C : Circuit) : (red N k i C).gates.length = C.gates.length := by
  simp [red]

theorem red_get (N k i : ℕ) (C : Circuit) (r : ℕ) (h : r < (red N k i C).gates.length) :
    (red N k i C).gates[r] = fixg N k i r (C.gates[r]'(by simpa [red] using h)) := by
  simp [red]

theorem red_mono (N k i : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (red N k i C) := by
  intro g hg
  simp only [red, List.mem_ofFn] at hg
  obtain ⟨r, rfl⟩ := hg
  have h := hC (C.gates.get r) (List.get_mem _ _)
  unfold fixg
  split_ifs
  · exact ⟨h.1, by simp⟩
  · exact ⟨h.1, by simpa using h.2⟩

theorem red_mu (N k i : ℕ) (C : Circuit) (hk : k < C.gates.length) (hi : i ∈ (C.gates[k]).inputs) :
    mu (red N k i C) < mu C := by
  have e1 : mu C = ∑ r : Fin C.gates.length, (C.gates.get r).inputs.length := by
    unfold mu
    conv_lhs => rw [← List.ofFn_get C.gates]
    rw [List.map_ofFn, List.sum_ofFn]
    rfl
  have e2 : mu (red N k i C) = ∑ r : Fin C.gates.length, (fixg N k i r.1 (C.gates.get r)).inputs.length := by
    unfold mu red
    rw [List.map_ofFn, List.sum_ofFn]
    rfl
  rw [e1, e2]
  apply Finset.sum_lt_sum
  · intro r _
    unfold fixg
    split_ifs <;> simp
  · refine ⟨⟨k, hk⟩, Finset.mem_univ _, ?_⟩
    unfold fixg
    rw [if_pos rfl]
    simp only [List.length_nil, List.get_eq_getElem]
    exact List.length_pos_of_mem hi

theorem cmp (P : Bool → Bool → Prop) (hrefl : ∀ b, P b b) (htr : ∀ a b c, P a b → P b c → P a c)
    (hand : ∀ a b c d : Bool, P a b → P c d → P (a && c) (b && d))
    (hor : ∀ a b c d : Bool, P a b → P c d → P (a || c) (b || d))
    (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (N k i : ℕ) (x : List Bool)
    (hx : x.length = N) (hk : k < C.gates.length) (hik : i < N + k)
    (hQ : P ((C.gates.foldl stp x).getD (N + k) false) ((C.gates.foldl stp x).getD i false)) :
    P (C.eval x) ((red N k i C).eval x) := by
  have hrun := run (fun j b => j = N + k ∨ P ((C.gates.foldl stp x).getD j false) b)
    (red N k i C).gates x
    (by
      intro j hj
      right
      rw [pre _ _ _ hj]
      exact hrefl _)
    (by
      intro r hr w hw hrel
      rw [hx] at hw hrel ⊢
      rw [red_len] at hr
      by_cases hrk : r = k
      · left; rw [hrk]
      right
      have hr' : r < (red N k i C).gates.length := by rw [red_len]; exact hr
      rw [red_get N k i C r hr']
      have hv := vgate C.gates x r hr
      rw [hx] at hv
      rw [hv]
      unfold fixg
      rw [if_neg hrk]
      simp only [List.map_map, Function.comp_def]
      have hop := (hC (C.gates[r]) (List.getElem_mem hr)).1
      have key : ∀ a ∈ (C.gates[r]).inputs, P (if a < N + r then (C.gates.foldl stp x).getD a false else false)
          (w.getD (if k < r ∧ a = N + k then i else a) false) := by
        intro a _
        by_cases ha : a < N + r
        · rw [if_pos ha]
          by_cases hred : k < r ∧ a = N + k
          · rw [if_pos hred, hred.2]
            rcases hrel i (by omega) with h0 | h0
            · omega
            · exact htr _ _ _ hQ h0
          · rw [if_neg hred]
            rcases hrel a ha with h0 | h0
            · omega
            · exact h0
        · rw [if_neg ha]
          have hred : ¬ (k < r ∧ a = N + k) := by omega
          rw [if_neg hred, getD_ge w a (by omega)]
          exact hrefl _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h
      · simp only [h, GateOp.eval]
        exact allP P (hrefl true) hand _ _ _ key
      · simp only [h, GateOp.eval]
        exact anyP P (hrefl false) hor _ _ _ key)
  have hlenC : (C.gates.foldl stp x).length = N + C.gates.length := by rw [flen, hx]
  have hlenD : ((red N k i C).gates.foldl stp x).length = N + C.gates.length := by
    rw [flen, hx, red_len]
  show P ((C.gates.foldl stp x).getD C.output false)
    (((red N k i C).gates.foldl stp x).getD (red N k i C).output false)
  by_cases ho : C.output = N + k
  · have e : (red N k i C).output = i := by simp [red, ho]
    rw [e, ho]
    rcases hrun i (by rw [hx, red_len]; omega) with h0 | h0
    · omega
    · exact htr _ _ _ hQ h0
  · have e : (red N k i C).output = C.output := by simp [red, ho]
    rw [e]
    by_cases hl : C.output < N + C.gates.length
    · rcases hrun C.output (by rw [hx, red_len]; exact hl) with h0 | h0
      · exact absurd h0 ho
      · exact h0
    · rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
      exact hrefl _

theorem oe_len {n m : ℕ} (u : Fin n) (v : Fin m) : (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem all_mem_true (l : List ℕ) (f : ℕ → Bool) (a : ℕ) (ha : a ∈ l)
    (h : GateOp.and.eval (l.map f) = true) : f a = true := by
  have h' : (l.map f).all id = true := h
  rw [List.all_eq_true] at h'
  exact h' (f a) (List.mem_map.2 ⟨a, ha, rfl⟩)

theorem any_mem_true (l : List ℕ) (f : ℕ → Bool) (a : ℕ) (ha : a ∈ l) (h : f a = true) :
    GateOp.or.eval (l.map f) = true := by
  show (l.map f).any id = true
  rw [List.any_eq_true]
  exact ⟨f a, List.mem_map.2 ⟨a, ha, rfl⟩, h⟩

theorem gk (C : Circuit) (x : List Bool) (N k : ℕ) (hx : x.length = N) (hk : k < C.gates.length) :
    (C.gates.foldl stp x).getD (N + k) false = (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun a =>
      if a < N + k then (C.gates.foldl stp x).getD a false else false) := by
  have := vgate C.gates x k hk
  rw [hx] at this
  exact this

theorem p1and : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a && c) = true → (b && d) = true := by decide

theorem p1or : ∀ a b c d : Bool, (a = true → b = true) → (c = true → d = true) →
    (a || c) = true → (b || d) = true := by decide

theorem p2and : ∀ a b c d : Bool, (b = true → a = true) → (d = true → c = true) →
    (b && d) = true → (a && c) = true := by decide

theorem p2or : ∀ a b c d : Bool, (b = true → a = true) → (d = true → c = true) →
    (b || d) = true → (a || c) = true := by decide

end PEqualNP.Outside.L_meta_25458

open PEqualNP.Outside.L_meta_25458 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25458 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (s : ℕ), PEqualNP.Represents.RepSizeAtMost A s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C ∧ ∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ), C.gates[k]? = some g → i ∈ g.inputs → i < n + m + k → ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD i false = true ∧ A u v = false) ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∃ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD i false = false ∧ A u v = true)) := by
  intro n m A s hs
  classical
  have hex : ∃ t, ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      PEqualNP.Represents.Represents A C ∧ mu C = t := by
    obtain ⟨C, h1, h2, h3⟩ := hs
    exact ⟨_, C, h1, h2, h3, rfl⟩
  obtain ⟨C, h1, h2, h3, h4⟩ := Nat.find_spec hex
  have hmin : ∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ s →
      PEqualNP.Represents.Represents A D → mu C ≤ mu D := by
    intro D d1 d2 d3
    rw [h4]
    exact Nat.find_min' hex ⟨D, d1, d2, d3, rfl⟩
  refine ⟨C, h1, h2, h3, ?_⟩
  intro k g i hk hi hlt
  have hkl : k < C.gates.length := (List.getElem?_eq_some_iff.1 hk).1
  have hg : C.gates[k] = g := (List.getElem?_eq_some_iff.1 hk).2
  have hi' : i ∈ (C.gates[k]).inputs := by rw [hg]; exact hi
  have hsz : (red (n + m) k i C).size ≤ s := by
    show (red (n + m) k i C).gates.length ≤ s
    rw [red_len]; exact h2
  have hmu := red_mu (n + m) k i C hkl hi'
  have peq := cmp (fun a b => a = b) (fun b => rfl) (fun a b c e1 e2 => e1.trans e2)
    (by intro a b c d e1 e2; rw [e1, e2]) (by intro a b c d e1 e2; rw [e1, e2]) C h1 (n + m) k i
  constructor
  · intro hop
    by_contra hne
    have hrep : PEqualNP.Represents.Represents A (red (n + m) k i C) := by
      intro u v
      have e := h3 u v
      have hx := oe_len u v
      have hgk := gk C (PEqualNP.Represents.oneEach u v) (n + m) k hx hkl
      rw [hg, hop] at hgk
      cases hA : A u v
      · have hvi : (C.gates.foldl stp (PEqualNP.Represents.oneEach u v)).getD i false = false := by
          cases hc : (C.gates.foldl stp (PEqualNP.Represents.oneEach u v)).getD i false
          · rfl
          · exact (hne ⟨u, v, hc, hA⟩).elim
        have hvk : (C.gates.foldl stp (PEqualNP.Represents.oneEach u v)).getD (n + m + k) false = false := by
          cases hc : (C.gates.foldl stp (PEqualNP.Represents.oneEach u v)).getD (n + m + k) false
          · rfl
          · rw [hgk] at hc
            have h5 := all_mem_true _ _ i hi hc
            rw [if_pos hlt, hvi] at h5
            exact absurd h5 (by decide)
        have := peq (PEqualNP.Represents.oneEach u v) hx hkl hlt (by rw [hvk, hvi])
        rw [← this]; exact e.trans hA
      · have := cmp (fun a b => a = true → b = true) (fun b h => h) (fun a b c e1 e2 h => e2 (e1 h))
          p1and p1or
          C h1 (n + m) k i (PEqualNP.Represents.oneEach u v) hx hkl hlt
          (by
            intro hc
            rw [hgk] at hc
            have h5 := all_mem_true _ _ i hi hc
            rw [if_pos hlt] at h5
            exact h5)
        rw [this (e.trans hA)]
    have := hmin _ (red_mono _ _ _ C h1) hsz hrep
    omega
  · intro hop
    by_contra hne
    have hrep : PEqualNP.Represents.Represents A (red (n + m) k i C) := by
      intro u v
      have e := h3 u v
      have hx := oe_len u v
      have hgk := gk C (PEqualNP.Represents.oneEach u v) (n + m) k hx hkl
      rw [hg, hop] at hgk
      cases hA : A u v
      · have := cmp (fun a b => b = true → a = true) (fun b h => h) (fun a b c e1 e2 h => e1 (e2 h))
          p2and p2or
          C h1 (n + m) k i (PEqualNP.Represents.oneEach u v) hx hkl hlt
          (by
            intro hc
            rw [hgk]
            exact any_mem_true _ _ i hi (by rw [if_pos hlt]; exact hc))
        cases hr : (red (n + m) k i C).eval (PEqualNP.Represents.oneEach u v)
        · rfl
        · have h6 := this hr
          rw [e, hA] at h6
          exact absurd h6 (by decide)
      · have hvi : (C.gates.foldl stp (PEqualNP.Represents.oneEach u v)).getD i false = true := by
          cases hc : (C.gates.foldl stp (PEqualNP.Represents.oneEach u v)).getD i false
          · exact (hne ⟨u, v, hc, hA⟩).elim
          · rfl
        have hvk : (C.gates.foldl stp (PEqualNP.Represents.oneEach u v)).getD (n + m + k) false = true := by
          rw [hgk]
          exact any_mem_true _ _ i hi (by rw [if_pos hlt]; exact hvi)
        have := peq (PEqualNP.Represents.oneEach u v) hx hkl hlt (by rw [hvk, hvi])
        rw [← this]; exact e.trans hA
    have := hmin _ (red_mono _ _ _ C h1) hsz hrep
    omega
