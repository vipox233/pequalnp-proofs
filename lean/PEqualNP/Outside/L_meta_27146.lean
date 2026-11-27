import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27146_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def perm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private def f0 (y : Fin 8 → Bool) : Bool :=
  (y 0 && y 2 && y 7) || (y 0 && y 4 && y 5) ||
  (y 1 && y 2 && y 6) || (y 1 && y 3 && y 5)

private def pad0 (y : Fin 8 → Bool) : Fin 9 → Bool :=
  fun i => if h : i.val = 0 then false else y ⟨i.val - 1, by omega⟩

private lemma perm3_pad0 (y : Fin 8 → Bool) : perm3 (pad0 y) = f0 y := by
  simp [perm3, f0, pad0]

private def mix (S : Finset (Fin 8)) (x y : Fin 8 → Bool) : Fin 8 → Bool :=
  fun i => if i ∈ S then x i else y i

private lemma same_mem_of_minterm {S M : Finset (Fin 8)}
    (hclosed : ∀ x y : Fin 8 → Bool, f0 x = false → f0 y = false → f0 (mix S x y) = false)
    (hM1 : f0 (fun i => decide (i ∈ M)) = true)
    (hM0 : ∀ u ∈ M, f0 (fun i => decide (i ∈ M.erase u)) = false)
    {u v : Fin 8} (hu : u ∈ M) (hv : v ∈ M) : u ∈ S ↔ v ∈ S := by
  have dir : ∀ a ∈ M, ∀ b ∈ M, a ∈ S → b ∉ S → False := by
    intro a ha b hb haS hbS
    let x : Fin 8 → Bool := fun i => decide (i ∈ M.erase b)
    let y : Fin 8 → Bool := fun i => decide (i ∈ M.erase a)
    have hx : f0 x = false := hM0 b hb
    have hy : f0 y = false := hM0 a ha
    have hmix_eq : mix S x y = fun i => decide (i ∈ M) := by
      funext i
      simp only [mix, x, y]
      by_cases hiS : i ∈ S
      · simp only [hiS, ↓reduceIte, Finset.mem_erase]
        have hib : i ≠ b := fun h => hbS (h ▸ hiS)
        simp [hib]
      · simp only [hiS, ↓reduceIte, Finset.mem_erase]
        have hia : i ≠ a := fun h => hiS (h ▸ haS)
        simp [hia]
    have hfalse := hclosed x y hx hy
    rw [hmix_eq, hM1] at hfalse
    cases hfalse
  constructor
  · intro huS
    by_contra hvS
    exact dir u hu v hv huS hvS
  · intro hvS
    by_contra huS
    exact dir v hv u hu hvS huS

private lemma same_mem_of_maxterm {S H : Finset (Fin 8)}
    (hclosed : ∀ x y : Fin 8 → Bool, f0 x = true → f0 y = true → f0 (mix S x y) = true)
    (hH0 : f0 (fun i => decide (i ∉ H)) = false)
    (hH1 : ∀ u ∈ H, f0 (fun i => decide (i ∉ H.erase u)) = true)
    {u v : Fin 8} (hu : u ∈ H) (hv : v ∈ H) : u ∈ S ↔ v ∈ S := by
  have dir : ∀ a ∈ H, ∀ b ∈ H, a ∈ S → b ∉ S → False := by
    intro a ha b hb haS hbS
    let x : Fin 8 → Bool := fun i => decide (i ∉ H.erase b)
    let y : Fin 8 → Bool := fun i => decide (i ∉ H.erase a)
    have hx : f0 x = true := hH1 b hb
    have hy : f0 y = true := hH1 a ha
    have hmix_eq : mix S x y = fun i => decide (i ∉ H) := by
      funext i
      simp only [mix, x, y]
      by_cases hiS : i ∈ S
      · simp only [hiS, ↓reduceIte, Finset.mem_erase]
        have hib : i ≠ b := fun h => hbS (h ▸ hiS)
        simp [hib]
      · simp only [hiS, ↓reduceIte, Finset.mem_erase]
        have hia : i ≠ a := fun h => hiS (h ▸ haS)
        simp [hia]
    have htrue := hclosed x y hx hy
    rw [hmix_eq, hH0] at htrue
    cases htrue
  constructor
  · intro huS
    by_contra hvS
    exact dir u hu v hv huS hvS
  · intro hvS
    by_contra huS
    exact dir v hv u hu hvS huS

private lemma no_or_decomp (S : Finset (Fin 8)) (hSne : S.Nonempty) (hScne : Sᶜ.Nonempty) :
    ¬ (∀ x y : Fin 8 → Bool, f0 x = false → f0 y = false → f0 (mix S x y) = false) := by
  intro hclosed
  have e02 : (0 : Fin 8) ∈ S ↔ (2 : Fin 8) ∈ S :=
    same_mem_of_minterm (M := {0, 2, 7}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e07 : (0 : Fin 8) ∈ S ↔ (7 : Fin 8) ∈ S :=
    same_mem_of_minterm (M := {0, 2, 7}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e04 : (0 : Fin 8) ∈ S ↔ (4 : Fin 8) ∈ S :=
    same_mem_of_minterm (M := {0, 4, 5}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e05 : (0 : Fin 8) ∈ S ↔ (5 : Fin 8) ∈ S :=
    same_mem_of_minterm (M := {0, 4, 5}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e21 : (2 : Fin 8) ∈ S ↔ (1 : Fin 8) ∈ S :=
    same_mem_of_minterm (M := {1, 2, 6}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e26 : (2 : Fin 8) ∈ S ↔ (6 : Fin 8) ∈ S :=
    same_mem_of_minterm (M := {1, 2, 6}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e13 : (1 : Fin 8) ∈ S ↔ (3 : Fin 8) ∈ S :=
    same_mem_of_minterm (M := {1, 3, 5}) hclosed (by decide) (by decide) (by decide) (by decide)
  have hall : ∀ i : Fin 8, i ∈ S ↔ (0 : Fin 8) ∈ S := by
    intro i
    fin_cases i
    · rfl
    · exact (e02.trans e21).symm
    · exact e02.symm
    · exact ((e02.trans e21).trans e13).symm
    · exact e04.symm
    · exact e05.symm
    · exact (e02.trans e26).symm
    · exact e07.symm
  obtain ⟨a, ha⟩ := hSne
  obtain ⟨b, hb⟩ := hScne
  have hb' : b ∉ S := Finset.mem_compl.mp hb
  exact hb' ((hall b).mpr ((hall a).mp ha))

private lemma no_and_decomp (S : Finset (Fin 8)) (hSne : S.Nonempty) (hScne : Sᶜ.Nonempty) :
    ¬ (∀ x y : Fin 8 → Bool, f0 x = true → f0 y = true → f0 (mix S x y) = true) := by
  intro hclosed
  have e01 : (0 : Fin 8) ∈ S ↔ (1 : Fin 8) ∈ S :=
    same_mem_of_maxterm (H := {0, 1}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e25 : (2 : Fin 8) ∈ S ↔ (5 : Fin 8) ∈ S :=
    same_mem_of_maxterm (H := {2, 5}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e12 : (1 : Fin 8) ∈ S ↔ (2 : Fin 8) ∈ S :=
    same_mem_of_maxterm (H := {1, 2, 4}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e14 : (1 : Fin 8) ∈ S ↔ (4 : Fin 8) ∈ S :=
    same_mem_of_maxterm (H := {1, 2, 4}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e03 : (0 : Fin 8) ∈ S ↔ (3 : Fin 8) ∈ S :=
    same_mem_of_maxterm (H := {0, 3, 6}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e06 : (0 : Fin 8) ∈ S ↔ (6 : Fin 8) ∈ S :=
    same_mem_of_maxterm (H := {0, 3, 6}) hclosed (by decide) (by decide) (by decide) (by decide)
  have e17 : (1 : Fin 8) ∈ S ↔ (7 : Fin 8) ∈ S :=
    same_mem_of_maxterm (H := {1, 4, 7}) hclosed (by decide) (by decide) (by decide) (by decide)
  have hall : ∀ i : Fin 8, i ∈ S ↔ (0 : Fin 8) ∈ S := by
    intro i
    fin_cases i
    · rfl
    · exact e01.symm
    · exact (e01.trans e12).symm
    · exact e03.symm
    · exact (e01.trans e14).symm
    · exact ((e01.trans e12).trans e25).symm
    · exact e06.symm
    · exact (e01.trans e17).symm
  obtain ⟨a, ha⟩ := hSne
  obtain ⟨b, hb⟩ := hScne
  have hb' : b ∉ S := Finset.mem_compl.mp hb
  exact hb' ((hall b).mpr ((hall a).mp ha))

private lemma f0_essential (i : Fin 8) :
    ∃ x y : Fin 8 → Bool, (∀ j, j ≠ i → x j = y j) ∧ f0 x ≠ f0 y := by
  fin_cases i
  · exact ⟨fun j => decide (j ∈ ({2, 7} : Finset (Fin 8))),
           fun j => decide (j ∈ ({0, 2, 7} : Finset (Fin 8))), by decide, by decide⟩
  · exact ⟨fun j => decide (j ∈ ({2, 6} : Finset (Fin 8))),
           fun j => decide (j ∈ ({1, 2, 6} : Finset (Fin 8))), by decide, by decide⟩
  · exact ⟨fun j => decide (j ∈ ({0, 7} : Finset (Fin 8))),
           fun j => decide (j ∈ ({0, 2, 7} : Finset (Fin 8))), by decide, by decide⟩
  · exact ⟨fun j => decide (j ∈ ({1, 5} : Finset (Fin 8))),
           fun j => decide (j ∈ ({1, 3, 5} : Finset (Fin 8))), by decide, by decide⟩
  · exact ⟨fun j => decide (j ∈ ({0, 5} : Finset (Fin 8))),
           fun j => decide (j ∈ ({0, 4, 5} : Finset (Fin 8))), by decide, by decide⟩
  · exact ⟨fun j => decide (j ∈ ({0, 4} : Finset (Fin 8))),
           fun j => decide (j ∈ ({0, 4, 5} : Finset (Fin 8))), by decide, by decide⟩
  · exact ⟨fun j => decide (j ∈ ({1, 2} : Finset (Fin 8))),
           fun j => decide (j ∈ ({1, 2, 6} : Finset (Fin 8))), by decide, by decide⟩
  · exact ⟨fun j => decide (j ∈ ({0, 2} : Finset (Fin 8))),
           fun j => decide (j ∈ ({0, 2, 7} : Finset (Fin 8))), by decide, by decide⟩

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

private lemma getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

private lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_append]; omega), ih]

private lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

private lemma run_gate_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs x).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ, List.take_append_drop]
  have htlen : (gs.take j).length = j := by simp; omega
  have h1 : (run gs x).getD (x.length + j) false =
      (run (gs.take j ++ [gs[j]]) x).getD (x.length + j) false := by
    conv_lhs => rw [hsplit]
    exact run_prefix (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) x (x.length + j)
      (by simp only [List.length_append, List.length_singleton, htlen]; omega)
  rw [h1, run_snoc]
  have hlen : (run (gs.take j) x).length = x.length + j := by rw [run_length, htlen]
  rw [← hlen, getD_at]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < x.length + (gs.take j).length := by rw [htlen]; exact hback i hi
  conv_rhs => rw [hsplit, List.append_assoc]
  exact (run_prefix (gs.take j) ([gs[j]] ++ gs.drop (j + 1)) x i hlt).symm

private def sg (c i : ℕ) : ℕ := if i < c then i else i - 1

private def sh (c : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg c)⟩

private lemma del_eval (x : List Bool) (n : ℕ) (hx : x.length = n) (p : List Gate) (g : Gate) :
    ∀ q : List Gate, (∀ h ∈ q, n + p.length ∉ h.inputs) →
    ∀ i, i ≠ n + p.length →
      (run (p ++ q.map (sh (n + p.length))) x).getD (sg (n + p.length) i) false =
      (run (p ++ [g] ++ q) x).getD i false := by
  intro q
  induction q using List.reverseRecOn with
  | nil =>
    intro _ i hi
    simp only [List.map_nil, List.append_nil]
    rcases Nat.lt_or_ge i (n + p.length) with h | h
    · simp only [sg, h, ↓reduceIte]
      exact (run_prefix p [g] x i (by omega)).symm
    · have hnot : ¬ i < n + p.length := by omega
      simp only [sg, hnot, ↓reduceIte]
      rw [List.getD_eq_default _ _ (by rw [run_length]; omega),
          List.getD_eq_default _ _ (by rw [run_length]; simp; omega)]
  | append_singleton q h ih =>
    intro hq i hi
    have ih := ih (fun h' hh => hq h' (List.mem_append_left _ hh))
    have hh : n + p.length ∉ h.inputs := hq h (by simp)
    rw [List.map_append, List.map_singleton, ← List.append_assoc, ← List.append_assoc, run_snoc, run_snoc]
    have l1 : (run (p ++ q.map (sh (n + p.length))) x).length = n + p.length + q.length := by
      rw [run_length]; simp [hx]; omega
    have l2 : (run (p ++ [g] ++ q) x).length = n + p.length + 1 + q.length := by
      rw [run_length]; simp [hx]; omega
    rcases Nat.lt_trichotomy i (n + p.length + 1 + q.length) with h1 | h1 | h1
    · rw [getD_lt _ _ _ (by rw [l1, sg]; split_ifs <;> omega), getD_lt _ _ _ (by rw [l2]; omega), ih i hi]
    · have hnot : ¬ i < n + p.length := by omega
      have e1 : sg (n + p.length) i = (run (p ++ q.map (sh (n + p.length))) x).length := by
        simp only [l1, sg, hnot, ↓reduceIte]; omega
      have e2 : i = (run (p ++ [g] ++ q) x).length := by rw [l2]; exact h1
      rw [e1, getD_at]
      conv_rhs => rw [e2, getD_at]
      simp only [sh, List.map_map]
      congr 1
      exact List.map_congr_left fun k hk => ih k (fun e => hh (e ▸ hk))
    · have hnot : ¬ i < n + p.length := by omega
      rw [List.getD_eq_default _ _ (by simp only [List.length_append, l1, sg, hnot, ↓reduceIte, List.length_singleton]; omega),
          List.getD_eq_default _ _ (by rw [List.length_append, l2]; simp; omega)]

private lemma indep_eval (w : ℕ) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ w → x.getD i false = y.getD i false) :
    ∀ gs : List Gate, (∀ g ∈ gs, w ∉ g.inputs) →
    ∀ i, i ≠ w → (run gs x).getD i false = (run gs y).getD i false := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ i hi; simpa [run] using hxy i hi
  | append_singleton gs g ih =>
    intro hg i hi
    have ih := ih (fun h hh => hg h (List.mem_append_left _ hh))
    have hw : w ∉ g.inputs := hg g (by simp)
    rw [run_snoc, run_snoc]
    have l1 : (run gs x).length = x.length + gs.length := run_length gs x
    have l2 : (run gs y).length = x.length + gs.length := by rw [run_length, hl]
    rcases Nat.lt_trichotomy i (x.length + gs.length) with h1 | h1 | h1
    · rw [getD_lt _ _ _ (by omega), getD_lt _ _ _ (by omega), ih i hi]
    · conv_lhs => rw [show i = (run gs x).length by omega, getD_at]
      conv_rhs => rw [show i = (run gs y).length by omega, getD_at]
      congr 1
      exact List.map_congr_left fun k hk => ih k (fun e => hw (e ▸ hk))
    · rw [List.getD_eq_default _ _ (by rw [List.length_append, l1]; simp; omega),
        List.getD_eq_default _ _ (by rw [List.length_append, l2]; simp; omega)]

private def act (g : Gate) : List ℕ :=
  g.inputs.take (match g.op with | GateOp.not => 1 | _ => 2)

private lemma act_eval (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : ℕ → Bool) :
    g.op.eval ((act g).map f) = g.op.eval (g.inputs.map f) := by
  rcases hg with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp [act, h, List.take_of_length_le hlen]
  · simp [act, h, List.take_of_length_le hlen]
  · simp only [act, h]
    cases h2 : g.inputs with
    | nil => rfl
    | cons a tl => simp [GateOp.eval]

private lemma trim_run (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (x : List Bool) :
    run (gs.map fun g => ⟨g.op, act g⟩) x = run gs x := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [List.map_append, List.map_singleton, run_snoc, run_snoc,
      ih (fun g' h => hfan g' (List.mem_append_left _ h))]
    congr 2
    exact act_eval g (hfan g (by simp)) _

private def coneOf (s : ℕ) (gIn0 gIn1 : Fin s → ℕ)
    (h0 : ∀ j : Fin s, gIn0 j < 8 + j.val) (h1 : ∀ j : Fin s, gIn1 j < 8 + j.val) : ℕ → Finset ℕ
  | w =>
    if h8 : w < 8 then {w}
    else if hlt : w < 8 + s then
      have _ : gIn0 ⟨w - 8, by omega⟩ < w := by
        have := h0 ⟨w - 8, by omega⟩; dsimp at this; omega
      have _ : gIn1 ⟨w - 8, by omega⟩ < w := by
        have := h1 ⟨w - 8, by omega⟩; dsimp at this; omega
      insert w (coneOf s gIn0 gIn1 h0 h1 (gIn0 ⟨w - 8, by omega⟩) ∪
                coneOf s gIn0 gIn1 h0 h1 (gIn1 ⟨w - 8, by omega⟩))
    else ∅

private lemma coneOf_self (s : ℕ) (gIn0 gIn1 : Fin s → ℕ)
    (h0 : ∀ j : Fin s, gIn0 j < 8 + j.val) (h1 : ∀ j : Fin s, gIn1 j < 8 + j.val)
    (w : ℕ) (hw : w < 8 + s) : w ∈ coneOf s gIn0 gIn1 h0 h1 w := by
  rw [coneOf]
  by_cases h8 : w < 8
  · simp [h8]
  · simp [h8, hw]

private lemma coneOf_le (s : ℕ) (gIn0 gIn1 : Fin s → ℕ)
    (h0 : ∀ j : Fin s, gIn0 j < 8 + j.val) (h1 : ∀ j : Fin s, gIn1 j < 8 + j.val) :
    ∀ w < 8 + s, ∀ u ∈ coneOf s gIn0 gIn1 h0 h1 w, u ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw u hu
    rw [coneOf] at hu
    by_cases h8 : w < 8
    · simp only [h8, ↓reduceDIte, Finset.mem_singleton] at hu; omega
    · simp only [h8, hw, ↓reduceDIte, Finset.mem_insert, Finset.mem_union] at hu
      have hj0 : gIn0 ⟨w - 8, by omega⟩ < w := by have := h0 ⟨w - 8, by omega⟩; dsimp at this; omega
      have hj1 : gIn1 ⟨w - 8, by omega⟩ < w := by have := h1 ⟨w - 8, by omega⟩; dsimp at this; omega
      rcases hu with rfl | hu0 | hu1
      · exact le_rfl
      · exact le_trans (ih _ hj0 (by omega) u hu0) (le_of_lt hj0)
      · exact le_trans (ih _ hj1 (by omega) u hu1) (le_of_lt hj1)

private lemma coneOf_leaf (s : ℕ) (gIn0 gIn1 : Fin s → ℕ)
    (h0 : ∀ j : Fin s, gIn0 j < 8 + j.val) (h1 : ∀ j : Fin s, gIn1 j < 8 + j.val) :
    ∀ w < 8 + s, ∃ i < 8, i ∈ coneOf s gIn0 gIn1 h0 h1 w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rw [coneOf]
    by_cases h8 : w < 8
    · simp only [h8, ↓reduceDIte]
      exact ⟨w, h8, Finset.mem_singleton_self w⟩
    · simp only [h8, hw, ↓reduceDIte]
      have hj0 : gIn0 ⟨w - 8, by omega⟩ < w := by have := h0 ⟨w - 8, by omega⟩; dsimp at this; omega
      obtain ⟨i, hi8, hic⟩ := ih _ hj0 (by omega)
      exact ⟨i, hi8, Finset.mem_insert_of_mem (Finset.mem_union_left _ hic)⟩

private lemma coneOf_parent (s : ℕ) (gIn0 gIn1 : Fin s → ℕ)
    (h0 : ∀ j : Fin s, gIn0 j < 8 + j.val) (h1 : ∀ j : Fin s, gIn1 j < 8 + j.val) :
    ∀ w < 8 + s, ∀ u ∈ coneOf s gIn0 gIn1 h0 h1 w, u ≠ w →
      ∃ j : Fin s, 8 + j.val ∈ coneOf s gIn0 gIn1 h0 h1 w ∧ (u = gIn0 j ∨ u = gIn1 j) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw u hu hne
    rw [coneOf] at hu
    by_cases h8 : w < 8
    · simp only [h8, ↓reduceDIte, Finset.mem_singleton] at hu; exact absurd hu hne
    · simp only [h8, hw, ↓reduceDIte, Finset.mem_insert, Finset.mem_union] at hu
      have hj0 : gIn0 ⟨w - 8, by omega⟩ < w := by have := h0 ⟨w - 8, by omega⟩; dsimp at this; omega
      have hj1 : gIn1 ⟨w - 8, by omega⟩ < w := by have := h1 ⟨w - 8, by omega⟩; dsimp at this; omega
      have hjw : 8 + (⟨w - 8, by omega⟩ : Fin s).val = w := by simp; omega
      rcases hu with rfl | hu0 | hu1
      · exact absurd rfl hne
      · by_cases heq : u = gIn0 ⟨w - 8, by omega⟩
        · exact ⟨⟨w - 8, by omega⟩, by rw [hjw]; exact coneOf_self s gIn0 gIn1 h0 h1 w hw, Or.inl heq⟩
        · obtain ⟨j', hj'c, hj'in⟩ := ih _ hj0 (by omega) u hu0 heq
          refine ⟨j', ?_, hj'in⟩
          rw [coneOf]
          simp only [h8, hw, ↓reduceDIte]
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hj'c)
      · by_cases heq : u = gIn1 ⟨w - 8, by omega⟩
        · exact ⟨⟨w - 8, by omega⟩, by rw [hjw]; exact coneOf_self s gIn0 gIn1 h0 h1 w hw, Or.inr heq⟩
        · obtain ⟨j', hj'c, hj'in⟩ := ih _ hj1 (by omega) u hu1 heq
          refine ⟨j', ?_, hj'in⟩
          rw [coneOf]
          simp only [h8, hw, ↓reduceDIte]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hj'c)

private lemma no_min_circuit_le7 (s : ℕ) (hs7 : s ≤ 7) (D : Circuit)
    (hDlen : D.gates.length = s) (hDfan : FanInTwo D) (hDread : ReadsBack 8 D)
    (hDeval : ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f0 y)
    (hDact : ∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (hmin : ∀ D' : Circuit, FanInTwo D' → ReadsBack 8 D' →
      (∀ y : Fin 8 → Bool, D'.eval (List.ofFn y) = f0 y) → s ≤ D'.size) : False := by
  classical
  have hout_ge : 8 ≤ D.output := by
    by_contra hlt
    have hlt8 : D.output < 8 := by omega
    have hvar : ∀ y : Fin 8 → Bool, f0 y = y ⟨D.output, hlt8⟩ := by
      intro y
      rw [← hDeval y]
      change (run D.gates (List.ofFn y)).getD D.output false = y ⟨D.output, hlt8⟩
      rw [run_input _ _ _ (by simp [hlt8]), List.getD_eq_getElem _ _ (by simp [hlt8]), List.getElem_ofFn]
    have h1 := hvar (fun j => decide (j = ⟨D.output, hlt8⟩))
    simp only [decide_true] at h1
    have hfalse : ∀ k : Fin 8, f0 (fun j => decide (j = k)) = false := by decide
    rw [hfalse ⟨D.output, hlt8⟩] at h1
    cases h1
  have hout_lt : D.output < 8 + s := by
    by_contra hge
    have hfalse : ∀ y : Fin 8 → Bool, f0 y = false := by
      intro y
      rw [← hDeval y]
      change (run D.gates (List.ofFn y)).getD D.output false = false
      exact List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn, hDlen]; omega)
    have h1 := hfalse (fun _ => true)
    have h2 : f0 (fun _ => true) = true := by decide
    rw [h2] at h1
    cases h1
  have hread_wire : ∀ w ∈ (Finset.range (8 + s)).erase D.output,
      ∃ j : Fin s, w ∈ D.gates[j.val].inputs := by
    intro w hw
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
    have hwlt : w < 8 + s := Finset.mem_range.mp hmem
    by_cases hw8 : w < 8
    · by_contra hno
      push Not at hno
      obtain ⟨x, y, hxy, hne_f⟩ := f0_essential ⟨w, hw8⟩
      apply hne_f
      rw [← hDeval x, ← hDeval y]
      change (run D.gates (List.ofFn x)).getD D.output false =
        (run D.gates (List.ofFn y)).getD D.output false
      refine indep_eval w (List.ofFn x) (List.ofFn y) (by simp) ?_ D.gates ?_ D.output hne.symm
      · intro i hi
        by_cases hi8 : i < 8
        · rw [List.getD_eq_getElem _ _ (by simp [hi8]), List.getD_eq_getElem _ _ (by simp [hi8]),
            List.getElem_ofFn, List.getElem_ofFn]
          exact hxy ⟨i, hi8⟩ (fun e => hi (congrArg Fin.val e))
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      · intro g hg
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        exact hno ⟨j, by omega⟩
    · by_contra hno
      push Not at hno
      let idx := w - 8
      have hidx : idx < D.gates.length := by omega
      let p := D.gates.take idx
      let q := D.gates.drop (idx + 1)
      have hp : p.length = idx := by simp [p]; omega
      have hsplit : D.gates = p ++ [D.gates[idx]] ++ q := by
        simp only [p, q]
        rw [List.append_assoc, List.singleton_append, List.cons_getElem_drop_succ, List.take_append_drop]
      have hnow : ∀ g ∈ D.gates, w ∉ g.inputs := by
        intro g hg
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        exact hno ⟨j, by omega⟩
      let D' : Circuit := ⟨p ++ q.map (sh (8 + p.length)), sg (8 + p.length) D.output⟩
      have hD'size : D'.size = s - 1 := by
        simp only [D', Circuit.size, List.length_append, List.length_map, hp, q, List.length_drop, hDlen]
        omega
      have hD'fan : FanInTwo D' := by
        intro g hg
        rcases List.mem_append.mp hg with h1 | h2
        · exact hDfan g (List.mem_of_mem_take h1)
        · rcases List.mem_map.mp h2 with ⟨g0, hg0, rfl⟩
          have := hDfan g0 (List.mem_of_mem_drop hg0)
          exact ⟨this.1, by simpa [sh] using this.2⟩
      have hD'read : ReadsBack 8 D' := by
        intro j hj i hi
        simp only [D', List.length_append, List.length_map, hp, q, List.length_drop, hDlen] at hj
        by_cases hjp : j < idx
        · have hget : gateAt D' j = gateAt D j := by
            simp only [gateAt, D', List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_left (by omega)]
            simp only [p, List.getElem?_take_of_lt hjp]
          rw [hget] at hi
          exact hDread j (by omega) i hi
        · have hk : j + 1 < D.gates.length := by omega
          have hget : gateAt D' j = sh (8 + idx) (gateAt D (j + 1)) := by
            have hjl : p.length ≤ j := by omega
            have h1 : gateAt D' j = (q.map (sh (8 + p.length))).getD (j - p.length) ⟨GateOp.or, []⟩ := by
              simp [gateAt, D', List.getD_eq_getElem?_getD, List.getElem?_append_right hjl]
            have hqlt : j - p.length < q.length := by simp [q, hp, hDlen]; omega
            have hqmlt : j - p.length < (q.map (sh (8 + p.length))).length := by simp [hqlt]
            rw [h1, List.getD_eq_getElem _ _ hqmlt, List.getElem_map]
            simp only [q, hp, List.getElem_drop, gateAt, List.getD_eq_getElem _ _ hk]
            congr 1
            congr 1
            omega
          rw [hget] at hi
          rcases List.mem_map.mp hi with ⟨i0, hi0, rfl⟩
          have hi0lt : i0 < 8 + (j + 1) := hDread (j + 1) hk i0 hi0
          have hi0ne : i0 ≠ 8 + idx := by
            have hmem : gateAt D (j + 1) ∈ D.gates := by
              simp only [gateAt, List.getD_eq_getElem _ _ hk]
              exact List.getElem_mem hk
            have := hnow _ hmem
            intro heq; apply this; rw [show w = 8 + idx by omega, ← heq]; exact hi0
          unfold sg
          split_ifs <;> omega
      have hD'eval : ∀ y : Fin 8 → Bool, D'.eval (List.ofFn y) = f0 y := by
        intro y
        rw [← hDeval y]
        change (run D'.gates (List.ofFn y)).getD D'.output false =
          (run D.gates (List.ofFn y)).getD D.output false
        have hw_eq : 8 + p.length = w := by omega
        rw [hsplit]
        exact del_eval (List.ofFn y) 8 (by simp) p D.gates[idx] q
          (fun h hh => by rw [hw_eq]; exact hnow h (List.mem_of_mem_drop hh))
          D.output (by rw [hw_eq]; exact hne.symm)
      have hge := hmin D' hD'fan hD'read hD'eval
      omega
  let slots : Finset (Σ j : Fin s, Fin (D.gates[j.val].inputs.length)) := Finset.univ
  let readFn : (Σ j : Fin s, Fin (D.gates[j.val].inputs.length)) → ℕ :=
    fun p => D.gates[p.1.val].inputs[p.2.val]
  have hWsub : (Finset.range (8 + s)).erase D.output ⊆ slots.image readFn := by
    intro w hw
    obtain ⟨j, hj⟩ := hread_wire w hw
    obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hj
    exact Finset.mem_image.mpr ⟨⟨j, ⟨t, ht⟩⟩, Finset.mem_univ _, hteq⟩
  have hWcard : ((Finset.range (8 + s)).erase D.output).card = 7 + s := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hout_lt), Finset.card_range]
    omega
  have hScard_eq : slots.card = ∑ j : Fin s, D.gates[j.val].inputs.length := by
    simp [slots]
  have hScard_le : slots.card ≤ 2 * s := by
    rw [hScard_eq]
    calc ∑ j : Fin s, D.gates[j.val].inputs.length
        ≤ ∑ _j : Fin s, 2 := Finset.sum_le_sum fun j _ =>
          (hDfan _ (List.getElem_mem (show j.val < D.gates.length by have := j.isLt; omega))).2
      _ = 2 * s := by simp [mul_comm]
  have hImg_le : (slots.image readFn).card ≤ slots.card := Finset.card_image_le
  have hWle : 7 + s ≤ (slots.image readFn).card := by
    rw [← hWcard]; exact Finset.card_le_card hWsub
  have hs_eq : s = 7 := by omega
  have hScard14 : slots.card = 14 := by omega
  have hImg14 : (slots.image readFn).card = 14 := by omega
  have hall_len2 : ∀ j : Fin s, D.gates[j.val].inputs.length = 2 := by
    intro j
    have hjD : j.val < D.gates.length := by have := j.isLt; omega
    by_contra hne
    have hlt2 : D.gates[j.val].inputs.length ≤ 1 := by
      have := (hDfan _ (List.getElem_mem hjD)).2; omega
    have hsum : ∑ k : Fin s, D.gates[k.val].inputs.length ≤ 2 * s - 1 := by
      have h1 : ∑ k ∈ Finset.univ.erase j, D.gates[k.val].inputs.length ≤ ∑ _k ∈ Finset.univ.erase j, 2 :=
        Finset.sum_le_sum fun k _ =>
          (hDfan _ (List.getElem_mem (show k.val < D.gates.length by have := k.isLt; omega))).2
      have h2 := Finset.add_sum_erase Finset.univ (fun k : Fin s => D.gates[k.val].inputs.length) (Finset.mem_univ j)
      simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
        Fintype.card_fin, smul_eq_mul] at h1
      omega
    omega
  have hno_not : ∀ j : Fin s, D.gates[j.val].op = GateOp.and ∨ D.gates[j.val].op = GateOp.or := by
    intro j
    have hjD : j.val < D.gates.length := by have := j.isLt; omega
    have hop := (hDfan _ (List.getElem_mem hjD)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have h1 := hDact _ (List.getElem_mem hjD) h
      have h2 := hall_len2 j
      omega
  have hreadInj : Function.Injective readFn := by
    have hinjOn : Set.InjOn readFn (slots : Set _) :=
      Finset.injOn_of_card_image_eq (by rw [hImg14, hScard14])
    intro a b hab
    exact hinjOn (Finset.mem_coe.mpr (Finset.mem_univ a)) (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
  have hback_get : ∀ (j : Fin s) (t : Fin (D.gates[j.val].inputs.length)),
      D.gates[j.val].inputs[t.val] < 8 + j.val := by
    intro j t
    have hj : j.val < D.gates.length := by have := j.isLt; omega
    have hmem : D.gates[j.val].inputs[t.val] ∈ (gateAt D j.val).inputs := by
      simp only [gateAt, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem t.isLt
    exact hDread j.val hj _ hmem
  let gIn0 (j : Fin s) : ℕ := D.gates[j.val].inputs[0]'(by rw [hall_len2 j]; omega)
  let gIn1 (j : Fin s) : ℕ := D.gates[j.val].inputs[1]'(by rw [hall_len2 j]; omega)
  have hgIn_list : ∀ j : Fin s, D.gates[j.val].inputs = [gIn0 j, gIn1 j] := by
    intro j
    have hlen := hall_len2 j
    match h : D.gates[j.val].inputs with
    | [a, b] => simp [gIn0, gIn1, h]
    | [] => simp [h] at hlen
    | [_] => simp [h] at hlen
    | _ :: _ :: _ :: _ => simp [h] at hlen
  have hIn0_lt : ∀ j : Fin s, gIn0 j < 8 + j.val := fun j =>
    hback_get j ⟨0, by rw [hall_len2 j]; omega⟩
  have hIn1_lt : ∀ j : Fin s, gIn1 j < 8 + j.val := fun j =>
    hback_get j ⟨1, by rw [hall_len2 j]; omega⟩
  have hIn_ne : ∀ j : Fin s, gIn0 j ≠ gIn1 j := by
    intro j heq
    have hinj : (⟨j, ⟨0, by rw [hall_len2 j]; omega⟩⟩ : Σ k : Fin s, Fin (D.gates[k.val].inputs.length)) =
        ⟨j, ⟨1, by rw [hall_len2 j]; omega⟩⟩ := hreadInj heq
    have : (⟨0, by rw [hall_len2 j]; omega⟩ : Fin (D.gates[j.val].inputs.length)) =
        ⟨1, by rw [hall_len2 j]; omega⟩ := eq_of_heq (Sigma.mk.inj_iff.mp hinj).2
    have h01 : (0 : ℕ) = 1 := congrArg Fin.val this
    omega
  have hUniqueReader : ∀ (w : ℕ) (j1 j2 : Fin s),
      (w = gIn0 j1 ∨ w = gIn1 j1) → (w = gIn0 j2 ∨ w = gIn1 j2) → j1 = j2 := by
    intro w j1 j2 h1 h2
    obtain ⟨t1, ht1⟩ : ∃ t1 : Fin (D.gates[j1.val].inputs.length), readFn ⟨j1, t1⟩ = w := by
      rcases h1 with rfl | rfl
      · exact ⟨⟨0, by rw [hall_len2 j1]; omega⟩, rfl⟩
      · exact ⟨⟨1, by rw [hall_len2 j1]; omega⟩, rfl⟩
    obtain ⟨t2, ht2⟩ : ∃ t2 : Fin (D.gates[j2.val].inputs.length), readFn ⟨j2, t2⟩ = w := by
      rcases h2 with rfl | rfl
      · exact ⟨⟨0, by rw [hall_len2 j2]; omega⟩, rfl⟩
      · exact ⟨⟨1, by rw [hall_len2 j2]; omega⟩, rfl⟩
    exact congrArg Sigma.fst (hreadInj (ht1.trans ht2.symm))
  let cone := coneOf s gIn0 gIn1 hIn0_lt hIn1_lt
  have hcone_dep : ∀ w < 8 + s, ∀ x y : Fin 8 → Bool,
      (∀ i : Fin 8, i.val ∈ cone w → x i = y i) →
      (run D.gates (List.ofFn x)).getD w false = (run D.gates (List.ofFn y)).getD w false := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw x y hagree
      by_cases h8 : w < 8
      · rw [run_input _ _ _ (by simp [h8]), run_input _ _ _ (by simp [h8]),
          List.getD_eq_getElem _ _ (by simp [h8]), List.getD_eq_getElem _ _ (by simp [h8]),
          List.getElem_ofFn, List.getElem_ofFn]
        exact hagree ⟨w, h8⟩ (by simp only [cone]; rw [coneOf]; simp [h8])
      · let j : Fin s := ⟨w - 8, by omega⟩
        have hwj : w = 8 + j.val := by simp only [j]; omega
        have h0 : gIn0 j < w := by have := hIn0_lt j; omega
        have h1 : gIn1 j < w := by have := hIn1_lt j; omega
        have hsub0 : ∀ i : Fin 8, i.val ∈ cone (gIn0 j) → x i = y i := by
          intro i hi
          apply hagree i
          simp only [cone] at hi ⊢
          rw [coneOf]
          simp only [h8, hw, ↓reduceDIte]
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hi)
        have hsub1 : ∀ i : Fin 8, i.val ∈ cone (gIn1 j) → x i = y i := by
          intro i hi
          apply hagree i
          simp only [cone] at hi ⊢
          rw [coneOf]
          simp only [h8, hw, ↓reduceDIte]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hi)
        have hv0 := ih (gIn0 j) h0 (by omega) x y hsub0
        have hv1 := ih (gIn1 j) h1 (by omega) x y hsub1
        have hback : ∀ a ∈ D.gates[j.val].inputs, a < (List.ofFn x).length + j.val := by
          intro a ha
          rw [hgIn_list j] at ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          simp only [List.length_ofFn]
          rcases ha with rfl | rfl
          · exact hIn0_lt j
          · exact hIn1_lt j
        have hbacky : ∀ a ∈ D.gates[j.val].inputs, a < (List.ofFn y).length + j.val := by
          simpa [List.length_ofFn] using hback
        rw [hwj]
        have hx8 : 8 + j.val = (List.ofFn x).length + j.val := by simp
        have hy8 : 8 + j.val = (List.ofFn y).length + j.val := by simp
        conv_lhs => rw [hx8]
        conv_rhs => rw [hy8]
        rw [run_gate_val D.gates (List.ofFn x) j.val (by omega) hback,
            run_gate_val D.gates (List.ofFn y) j.val (by omega) hbacky]
        rw [hgIn_list j]
        simp only [List.map_cons, List.map_nil, hv0, hv1]
  let jOut : Fin s := ⟨D.output - 8, by omega⟩
  have hjOut_eq : 8 + jOut.val = D.output := by simp only [jOut]; omega
  let u := gIn0 jOut
  let v := gIn1 jOut
  have hu_lt : u < D.output := by have := hIn0_lt jOut; omega
  have hv_lt : v < D.output := by have := hIn1_lt jOut; omega
  have huv_ne : u ≠ v := hIn_ne jOut
  have hdisj_cone : Disjoint (cone u) (cone v) := by
    rw [Finset.disjoint_left]
    intro w0 hwu hwv
    have hne : (cone u ∩ cone v).Nonempty := ⟨w0, Finset.mem_inter.mpr ⟨hwu, hwv⟩⟩
    let w := (cone u ∩ cone v).max' hne
    have hw_mem : w ∈ cone u ∩ cone v := Finset.max'_mem _ hne
    have hwu' : w ∈ cone u := (Finset.mem_inter.mp hw_mem).1
    have hwv' : w ∈ cone v := (Finset.mem_inter.mp hw_mem).2
    have hw_max : ∀ z ∈ cone u ∩ cone v, z ≤ w := fun z hz => Finset.le_max' _ z hz
    have hwu_ne : w ≠ u := by
      intro heq
      rw [heq] at hwv'
      obtain ⟨j, hjv, hjin⟩ := coneOf_parent s gIn0 gIn1 hIn0_lt hIn1_lt v (by omega) u hwv' huv_ne
      have hj_eq : j = jOut := hUniqueReader u j jOut hjin (Or.inl rfl)
      rw [hj_eq] at hjv
      have hle := coneOf_le s gIn0 gIn1 hIn0_lt hIn1_lt v (by omega) (8 + jOut.val) hjv
      omega
    have hwv_ne : w ≠ v := by
      intro heq
      rw [heq] at hwu'
      obtain ⟨j, hju, hjin⟩ := coneOf_parent s gIn0 gIn1 hIn0_lt hIn1_lt u (by omega) v hwu' huv_ne.symm
      have hj_eq : j = jOut := hUniqueReader v j jOut hjin (Or.inr rfl)
      rw [hj_eq] at hju
      have hle := coneOf_le s gIn0 gIn1 hIn0_lt hIn1_lt u (by omega) (8 + jOut.val) hju
      omega
    obtain ⟨j1, hj1u, hj1in⟩ := coneOf_parent s gIn0 gIn1 hIn0_lt hIn1_lt u (by omega) w hwu' hwu_ne
    obtain ⟨j2, hj2v, hj2in⟩ := coneOf_parent s gIn0 gIn1 hIn0_lt hIn1_lt v (by omega) w hwv' hwv_ne
    have hj_eq : j1 = j2 := hUniqueReader w j1 j2 hj1in hj2in
    rw [← hj_eq] at hj2v
    have hw_lt_p : w < 8 + j1.val := by
      rcases hj1in with h | h
      · rw [h]; exact hIn0_lt j1
      · rw [h]; exact hIn1_lt j1
    have hle := hw_max (8 + j1.val) (Finset.mem_inter.mpr ⟨hj1u, hj2v⟩)
    omega
  let S : Finset (Fin 8) := Finset.univ.filter fun i => i.val ∈ cone u
  have hSne : S.Nonempty := by
    obtain ⟨i, hi8, hiu⟩ := coneOf_leaf s gIn0 gIn1 hIn0_lt hIn1_lt u (by omega)
    exact ⟨⟨i, hi8⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiu⟩⟩
  have hScne : Sᶜ.Nonempty := by
    obtain ⟨i, hi8, hiv⟩ := coneOf_leaf s gIn0 gIn1 hIn0_lt hIn1_lt v (by omega)
    refine ⟨⟨i, hi8⟩, Finset.mem_compl.mpr ?_⟩
    intro hiS
    have hiu : i ∈ cone u := (Finset.mem_filter.mp hiS).2
    exact Finset.disjoint_left.mp hdisj_cone hiu hiv
  have heval_root : ∀ x : Fin 8 → Bool,
      f0 x = (D.gates[jOut.val].op).eval
        [(run D.gates (List.ofFn x)).getD u false, (run D.gates (List.ofFn x)).getD v false] := by
    intro x
    rw [← hDeval x]
    change (run D.gates (List.ofFn x)).getD D.output false = _
    have hback : ∀ a ∈ D.gates[jOut.val].inputs, a < (List.ofFn x).length + jOut.val := by
      intro a ha
      rw [hgIn_list jOut] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      simp only [List.length_ofFn]
      rcases ha with rfl | rfl
      · exact hIn0_lt jOut
      · exact hIn1_lt jOut
    have h8 : D.output = (List.ofFn x).length + jOut.val := by simp [← hjOut_eq]
    conv_lhs => rw [h8]
    rw [run_gate_val D.gates (List.ofFn x) jOut.val (by omega) hback, hgIn_list jOut]
    rfl
  have hu_mix : ∀ x y : Fin 8 → Bool,
      (run D.gates (List.ofFn (mix S x y))).getD u false = (run D.gates (List.ofFn x)).getD u false := by
    intro x y
    apply hcone_dep u (by omega)
    intro i hi
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    simp [mix, hiS]
  have hv_mix : ∀ x y : Fin 8 → Bool,
      (run D.gates (List.ofFn (mix S x y))).getD v false = (run D.gates (List.ofFn y)).getD v false := by
    intro x y
    apply hcone_dep v (by omega)
    intro i hi
    have hiS : i ∉ S := by
      intro h
      exact Finset.disjoint_left.mp hdisj_cone (Finset.mem_filter.mp h).2 hi
    simp [mix, hiS]
  rcases hno_not jOut with hand | hor
  · apply no_and_decomp S hSne hScne
    intro x y hx hy
    rw [heval_root, hand] at hx hy ⊢
    simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hx hy ⊢
    rw [hu_mix, hv_mix]
    exact ⟨hx.1, hy.2⟩
  · apply no_or_decomp S hSne hScne
    intro x y hx hy
    rw [heval_root, hor] at hx hy ⊢
    simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_false_iff] at hx hy ⊢
    rw [hu_mix, hv_mix]
    exact ⟨hx.1, hy.2⟩

private lemma no_circuit_le7 :
    ¬ ∃ D : Circuit, FanInTwo D ∧ ReadsBack 8 D ∧ D.size ≤ 7 ∧
      ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f0 y := by
  classical
  intro hex
  have hexS : ∃ s : ℕ, s ≤ 7 ∧ ∃ D : Circuit, FanInTwo D ∧ ReadsBack 8 D ∧ D.size = s ∧
      ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f0 y := by
    obtain ⟨D, h1, h2, h3, h4⟩ := hex
    exact ⟨D.size, h3, D, h1, h2, rfl, h4⟩
  set s := Nat.find hexS
  obtain ⟨hs7, D0, hfan0, hread0, hsize0, heval0⟩ := Nat.find_spec hexS
  have hsize0' : D0.gates.length = s := hsize0
  have hmin : ∀ D' : Circuit, FanInTwo D' → ReadsBack 8 D' →
      (∀ y : Fin 8 → Bool, D'.eval (List.ofFn y) = f0 y) → s ≤ D'.size := by
    intro D' hf' hr' he'
    by_contra hlt
    have hlt' : D'.size < s := by omega
    exact Nat.find_min hexS hlt' ⟨by omega, D', hf', hr', rfl, he'⟩
  let D : Circuit := ⟨D0.gates.map fun g => ⟨g.op, act g⟩, D0.output⟩
  have hDlen : D.gates.length = s := by simp [D, hsize0']
  have hDfan : FanInTwo D := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
    refine ⟨(hfan0 g0 hg0).1, ?_⟩
    simp only [act, List.length_take]
    have := (hfan0 g0 hg0).2
    cases g0.op <;> omega
  have hDread : ReadsBack 8 D := by
    intro j hj i hi
    simp only [D, List.length_map] at hj
    have hj' : j < D.gates.length := by simp [D, hj]
    have hget : gateAt D j = ⟨(gateAt D0 j).op, act (gateAt D0 j)⟩ := by
      simp only [gateAt, D] at hj' ⊢
      rw [List.getD_eq_getElem _ _ hj', List.getElem_map, List.getD_eq_getElem _ _ hj]
    rw [hget] at hi
    exact hread0 j hj i (List.mem_of_mem_take hi)
  have hDeval : ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f0 y := by
    intro y
    change (run D.gates (List.ofFn y)).getD D.output false = f0 y
    rw [trim_run D0.gates hfan0 (List.ofFn y)]
    exact heval0 y
  have hDact : ∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
    intro g hg hop
    rcases List.mem_map.mp hg with ⟨g0, _, rfl⟩
    simp only at hop
    simp [act, hop]
  exact no_min_circuit_le7 s hs7 D hDlen hDfan hDread hDeval hDact hmin

private inductive SymWire
  | const (b : Bool)
  | ref (w : ℕ)

private def symEval (y : Fin 8 → Bool) (gs : List Gate) : SymWire → Bool
  | .const b => b
  | .ref w => (run gs (List.ofFn y)).getD w false

private def symLt (bound : ℕ) : SymWire → Prop
  | .const _ => True
  | .ref w => w < bound

private def reduceGates (gs : List Gate) (env : ℕ → SymWire) (outGs : List Gate) (idx : ℕ) :
    List Gate × (ℕ → SymWire) :=
  match gs with
  | [] => (outGs, env)
  | g :: rest =>
    match g.op, g.inputs with
    | GateOp.not, [a] =>
      match env a with
      | .const b =>
        reduceGates rest (fun w => if w = idx then .const (!b) else env w) outGs (idx + 1)
      | .ref u =>
        let nw := 8 + outGs.length
        reduceGates rest (fun w => if w = idx then .ref nw else env w)
          (outGs ++ [⟨GateOp.not, [u]⟩]) (idx + 1)
    | GateOp.and, [a, b] =>
      match env a, env b with
      | .const false, _ =>
        reduceGates rest (fun w => if w = idx then .const false else env w) outGs (idx + 1)
      | _, .const false =>
        reduceGates rest (fun w => if w = idx then .const false else env w) outGs (idx + 1)
      | .const true, sb =>
        reduceGates rest (fun w => if w = idx then sb else env w) outGs (idx + 1)
      | sa, .const true =>
        reduceGates rest (fun w => if w = idx then sa else env w) outGs (idx + 1)
      | .ref u, .ref v =>
        let nw := 8 + outGs.length
        reduceGates rest (fun w => if w = idx then .ref nw else env w)
          (outGs ++ [⟨GateOp.and, [u, v]⟩]) (idx + 1)
    | GateOp.or, [a, b] =>
      match env a, env b with
      | .const true, _ =>
        reduceGates rest (fun w => if w = idx then .const true else env w) outGs (idx + 1)
      | _, .const true =>
        reduceGates rest (fun w => if w = idx then .const true else env w) outGs (idx + 1)
      | .const false, sb =>
        reduceGates rest (fun w => if w = idx then sb else env w) outGs (idx + 1)
      | sa, .const false =>
        reduceGates rest (fun w => if w = idx then sa else env w) outGs (idx + 1)
      | .ref u, .ref v =>
        let nw := 8 + outGs.length
        reduceGates rest (fun w => if w = idx then .ref nw else env w)
          (outGs ++ [⟨GateOp.or, [u, v]⟩]) (idx + 1)
    | _, _ =>
      reduceGates rest (fun w => if w = idx then .const false else env w) outGs (idx + 1)

private def isConstWire (env : ℕ → SymWire) (w : ℕ) : Prop :=
  ∃ b : Bool, env w = .const b

private def wfGate (idx : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ a, a < idx ∧ g.inputs = [a]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, a < b ∧ b < idx ∧ g.inputs = [a, b])

private lemma GoodAppend {gs : List Gate} {g : Gate}
    (hf : FanInTwo ⟨gs, 0⟩) (hr : ReadsBack 8 ⟨gs, 0⟩)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < 8 + gs.length) :
    FanInTwo ⟨gs ++ [g], 0⟩ ∧ ReadsBack 8 ⟨gs ++ [g], 0⟩ := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hf g' h1
    · rw [List.mem_singleton.mp h2]; exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hr j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      have hget : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        simp [gateAt, List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hback i hi

private lemma symEval_ext {y : Fin 8 → Bool} {gs ext : List Gate} {sw : SymWire}
    (hlt : symLt (8 + gs.length) sw) :
    symEval y (gs ++ ext) sw = symEval y gs sw := by
  cases sw with
  | const b => rfl
  | ref w => exact run_prefix gs ext (List.ofFn y) w (by simpa [symLt] using hlt)

private lemma symLt_mono {a b : ℕ} {sw : SymWire} (h : a ≤ b) (hs : symLt a sw) : symLt b sw := by
  cases sw with
  | const _ => trivial
  | ref w => exact lt_of_lt_of_le hs h

private lemma reduceGates_spec (gs : List Gate) (pref : List Gate)
    (env : ℕ → SymWire) (outGs : List Gate)
    (hfan : FanInTwo ⟨outGs, 0⟩) (hread : ReadsBack 8 ⟨outGs, 0⟩)
    (hwf : ∀ k : Fin gs.length, wfGate (9 + pref.length + k.val) (gs.get k))
    (henv_lt : ∀ w < 9 + pref.length, symLt (8 + outGs.length) (env w))
    (henv_ev : ∀ (y : Fin 8 → Bool) (w : ℕ), w < 9 + pref.length →
      symEval y outGs (env w) = (run pref (List.ofFn (pad0 y))).getD w false)
    (K : Finset ℕ)
    (hK : ∀ k ∈ K, ∃ hk : k < gs.length, ∃ a ∈ gs[k].inputs, a < 9 + pref.length ∧ isConstWire env a) :
    let res := reduceGates gs env outGs (9 + pref.length)
    FanInTwo ⟨res.1, 0⟩ ∧ ReadsBack 8 ⟨res.1, 0⟩ ∧
    res.1.length + K.card ≤ outGs.length + gs.length ∧
    (∀ w < 9 + pref.length + gs.length, symLt (8 + res.1.length) (res.2 w)) ∧
    (∀ (y : Fin 8 → Bool) (w : ℕ), w < 9 + pref.length + gs.length →
      symEval y res.1 (res.2 w) = (run (pref ++ gs) (List.ofFn (pad0 y))).getD w false) := by
  induction gs generalizing pref env outGs K with
  | nil =>
    have hK0 : K = ∅ := by
      ext k; simp only [Finset.notMem_empty, iff_false]
      intro hk; obtain ⟨h1, _⟩ := hK k hk; simp at h1
    subst hK0
    refine ⟨hfan, hread, by simp [reduceGates], by simpa [reduceGates] using henv_lt, ?_⟩
    intro y w hw
    simpa [reduceGates] using henv_ev y w hw
  | cons g rest ih =>
    set idx := 9 + pref.length
    have hwg : wfGate idx g := hwf ⟨0, by simp⟩
    have hwf_rest : ∀ k : Fin rest.length, wfGate (9 + (pref ++ [g]).length + k.val) (rest.get k) := by
      intro k
      have hk := hwf ⟨k.val + 1, by simp⟩
      have hlen : 9 + (pref ++ [g]).length + k.val = 9 + pref.length + (k.val + 1) := by simp; omega
      rw [hlen]
      exact hk
    let K' : Finset ℕ := (K.erase 0).image (fun k => k - 1)
    have hK'_card : K'.card = (K.erase 0).card := by
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      dsimp only at hab
      have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
      have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
      omega
    have hfinish : ∀ (outGs' : List Gate) (sw : SymWire)
        (hext : ∃ ext, outGs' = outGs ++ ext)
        (hsize_step : outGs'.length + (if 0 ∈ K then 1 else 0) ≤ outGs.length + 1)
        (hfan' : FanInTwo ⟨outGs', 0⟩) (hread' : ReadsBack 8 ⟨outGs', 0⟩)
        (hsw_lt : symLt (8 + outGs'.length) sw)
        (hsw_ev : ∀ y : Fin 8 → Bool,
          symEval y outGs' sw = g.op.eval (g.inputs.map fun i => (run pref (List.ofFn (pad0 y))).getD i false)),
        let env' : ℕ → SymWire := fun w => if w = idx then sw else env w
        let res := reduceGates rest env' outGs' (idx + 1)
        FanInTwo ⟨res.1, 0⟩ ∧ ReadsBack 8 ⟨res.1, 0⟩ ∧
        res.1.length + K.card ≤ outGs.length + (g :: rest).length ∧
        (∀ w < 9 + pref.length + (g :: rest).length, symLt (8 + res.1.length) (res.2 w)) ∧
        (∀ (y : Fin 8 → Bool) (w : ℕ), w < 9 + pref.length + (g :: rest).length →
          symEval y res.1 (res.2 w) = (run (pref ++ g :: rest) (List.ofFn (pad0 y))).getD w false) := by
      intro outGs' sw hext hsize_step hfan' hread' hsw_lt hsw_ev
      rcases hext with ⟨ext, rfl⟩
      let env' : ℕ → SymWire := fun w => if w = idx then sw else env w
      have henv'_lt : ∀ w < 9 + (pref ++ [g]).length, symLt (8 + (outGs ++ ext).length) (env' w) := by
        intro w hw
        simp only [List.length_append, List.length_singleton] at hw
        by_cases hwi : w = idx
        · simp only [env', hwi, ↓reduceIte]; exact hsw_lt
        · simp only [env', hwi, ↓reduceIte]
          exact symLt_mono (by simp) (henv_lt w (by omega))
      have henv'_ev : ∀ (y : Fin 8 → Bool) (w : ℕ), w < 9 + (pref ++ [g]).length →
          symEval y (outGs ++ ext) (env' w) = (run (pref ++ [g]) (List.ofFn (pad0 y))).getD w false := by
        intro y w hw
        simp only [List.length_append, List.length_singleton] at hw
        have hlen_p : (run pref (List.ofFn (pad0 y))).length = idx := by
          rw [run_length, List.length_ofFn]
        rw [run_snoc]
        by_cases hwi : w = idx
        · subst hwi
          simp only [env', ↓reduceIte, ← hlen_p, getD_at]
          exact hsw_ev y
        · simp only [env', hwi, ↓reduceIte]
          rw [getD_lt _ _ _ (by omega), symEval_ext (henv_lt w (by omega))]
          exact henv_ev y w (by omega)
      have hK' : ∀ k ∈ K', ∃ hk : k < rest.length,
          ∃ a ∈ rest[k].inputs, a < 9 + (pref ++ [g]).length ∧ isConstWire env' a := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨k0, hk0, rfl⟩
        obtain ⟨hk0_ne, hk0_mem⟩ := Finset.mem_erase.mp hk0
        obtain ⟨hk0_lt, a, ha_in, ha_lt, b, hb⟩ := hK k0 hk0_mem
        have hk_lt : k0 - 1 < rest.length := by simp at hk0_lt; omega
        refine ⟨hk_lt, a, ?_, by simp; omega, b, ?_⟩
        · have heq_g : (g :: rest)[k0]'hk0_lt = rest[k0 - 1]'hk_lt := by
            cases k0 with
            | zero => omega
            | succ m => rfl
          rw [← heq_g]
          exact ha_in
        · have hne : a ≠ idx := by omega
          simp [env', hne, hb]
      have hrec := ih (pref ++ [g]) env' (outGs ++ ext) hfan' hread' hwf_rest henv'_lt henv'_ev K' hK'
      have hidx_eq : 9 + (pref ++ [g]).length = idx + 1 := by simp [idx]; omega
      rw [hidx_eq] at hrec
      have hcardK : K.card = K'.card + (if 0 ∈ K then 1 else 0) := by
        rw [hK'_card]
        by_cases h0 : 0 ∈ K
        · simp only [h0, ↓reduceIte]; exact (Finset.card_erase_add_one h0).symm
        · simp only [h0, ↓reduceIte, Nat.add_zero, Finset.erase_eq_of_notMem h0]
      have hpref_eq : pref ++ g :: rest = (pref ++ [g]) ++ rest := by simp
      dsimp only
      refine ⟨hrec.1, hrec.2.1, ?_, ?_, ?_⟩
      · have h1 := hrec.2.2.1
        dsimp only [env'] at h1
        simp only [List.length_cons, List.length_append] at h1 hsize_step ⊢
        omega
      · intro w hw
        have hw' : w < idx + 1 + rest.length := by simp only [List.length_cons] at hw; omega
        exact hrec.2.2.2.1 w hw'
      · intro y w hw
        have hw' : w < idx + 1 + rest.length := by simp only [List.length_cons] at hw; omega
        rw [hpref_eq]
        exact hrec.2.2.2.2 y w hw'
    have h0K_const : 0 ∈ K → ∃ a ∈ g.inputs, isConstWire env a := by
      intro h0
      obtain ⟨_, a, ha, _, hc⟩ := hK 0 h0
      exact ⟨a, ha, hc⟩
    rcases hwg with ⟨hop, a, halt, hin⟩ | ⟨hop, a, b, hab, hblt, hin⟩
    · simp only [reduceGates, hop, hin]
      cases hea : env a with
      | const bv =>
        exact hfinish outGs (.const (!bv)) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread trivial
          (fun y => by
            have h1 := henv_ev y a halt
            rw [hea] at h1; simp only [symEval] at h1
            rw [hop, hin]; simp only [List.map_cons, List.map_nil, symEval, ← h1]; rfl)
      | ref u =>
        have hu_lt : u < 8 + outGs.length := by
          have := henv_lt a halt; rw [hea] at this; exact this
        have hnot0K : 0 ∉ K := by
          intro h0
          obtain ⟨a0, ha0, bv, hbv⟩ := h0K_const h0
          rw [hin] at ha0; simp only [List.mem_singleton] at ha0; subst ha0
          rw [hea] at hbv; cases hbv
        have ⟨hf', hr'⟩ := GoodAppend (g := ⟨GateOp.not, [u]⟩) hfan hread (by simp) (by simp)
          (fun i hi => by simp at hi; subst hi; exact hu_lt)
        exact hfinish (outGs ++ [⟨GateOp.not, [u]⟩]) (.ref (8 + outGs.length)) ⟨_, rfl⟩
          (by simp [hnot0K]) hf' hr' (by simp [symLt])
          (fun y => by
            have hev := henv_ev y a halt
            rw [hea] at hev; simp only [symEval] at hev
            simp only [symEval, run_snoc]
            have hlen : (run outGs (List.ofFn y)).length = 8 + outGs.length := by
              rw [run_length, List.length_ofFn]
            rw [← hlen, getD_at, hop, hin]
            simp only [List.map_cons, List.map_nil, ← hev])
    · rcases hop with hop | hop
      · simp only [reduceGates, hop, hin]
        cases hea : env a with
        | const ba =>
          cases ba with
          | false =>
            exact hfinish outGs (.const false) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread trivial
              (fun y => by
                have h1 := henv_ev y a (by omega)
                rw [hea] at h1; simp only [symEval] at h1
                rw [hop, hin]; simp only [List.map_cons, List.map_nil, symEval, ← h1]; rfl)
          | true =>
            cases heb : env b with
            | const bb =>
              cases bb with
              | false =>
                exact hfinish outGs (.const false) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread trivial
                  (fun y => by
                    have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                    have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                    rw [hop, hin]; simp only [List.map_cons, List.map_nil, symEval, ← h1, ← h2]; rfl)
              | true =>
                exact hfinish outGs (.const true) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread trivial
                  (fun y => by
                    have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                    have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                    rw [hop, hin]; simp only [List.map_cons, List.map_nil, symEval, ← h1, ← h2]; rfl)
            | ref v =>
              have hv_lt : v < 8 + outGs.length := by
                have := henv_lt b hblt; rw [heb] at this; exact this
              exact hfinish outGs (.ref v) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread hv_lt
                (fun y => by
                  have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                  have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                  rw [hop, hin]; simp only [List.map_cons, List.map_nil, GateOp.eval, symEval, ← h1, ← h2]
                  simp)
        | ref u =>
          have hu_lt : u < 8 + outGs.length := by
            have := henv_lt a (by omega); rw [hea] at this; exact this
          cases heb : env b with
          | const bb =>
            cases bb with
            | false =>
              exact hfinish outGs (.const false) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread trivial
                (fun y => by
                  have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                  rw [hop, hin]; simp only [List.map_cons, List.map_nil, GateOp.eval, symEval, ← h2]
                  simp)
            | true =>
              exact hfinish outGs (.ref u) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread hu_lt
                (fun y => by
                  have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                  have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                  rw [hop, hin]; simp only [List.map_cons, List.map_nil, GateOp.eval, symEval, ← h1, ← h2]
                  simp)
          | ref v =>
            have hv_lt : v < 8 + outGs.length := by
              have := henv_lt b hblt; rw [heb] at this; exact this
            have hnot0K : 0 ∉ K := by
              intro h0
              obtain ⟨a0, ha0, bv, hbv⟩ := h0K_const h0
              rw [hin] at ha0; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha0
              rcases ha0 with rfl | rfl
              · rw [hea] at hbv; cases hbv
              · rw [heb] at hbv; cases hbv
            have ⟨hf', hr'⟩ := GoodAppend (g := ⟨GateOp.and, [u, v]⟩) hfan hread (by simp) (by simp)
              (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> omega)
            exact hfinish (outGs ++ [⟨GateOp.and, [u, v]⟩]) (.ref (8 + outGs.length)) ⟨_, rfl⟩
              (by simp [hnot0K]) hf' hr' (by simp [symLt])
              (fun y => by
                have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                simp only [symEval, run_snoc]
                have hlen : (run outGs (List.ofFn y)).length = 8 + outGs.length := by
                  rw [run_length, List.length_ofFn]
                rw [← hlen, getD_at, hop, hin]
                simp only [List.map_cons, List.map_nil, ← h1, ← h2])
      · simp only [reduceGates, hop, hin]
        cases hea : env a with
        | const ba =>
          cases ba with
          | true =>
            exact hfinish outGs (.const true) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread trivial
              (fun y => by
                have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                rw [hop, hin]; simp only [List.map_cons, List.map_nil, symEval, ← h1]; rfl)
          | false =>
            cases heb : env b with
            | const bb =>
              cases bb with
              | true =>
                exact hfinish outGs (.const true) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread trivial
                  (fun y => by
                    have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                    have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                    rw [hop, hin]; simp only [List.map_cons, List.map_nil, symEval, ← h1, ← h2]; rfl)
              | false =>
                exact hfinish outGs (.const false) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread trivial
                  (fun y => by
                    have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                    have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                    rw [hop, hin]; simp only [List.map_cons, List.map_nil, symEval, ← h1, ← h2]; rfl)
            | ref v =>
              have hv_lt : v < 8 + outGs.length := by
                have := henv_lt b hblt; rw [heb] at this; exact this
              exact hfinish outGs (.ref v) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread hv_lt
                (fun y => by
                  have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                  have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                  rw [hop, hin]; simp only [List.map_cons, List.map_nil, GateOp.eval, symEval, ← h1, ← h2]
                  simp)
        | ref u =>
          have hu_lt : u < 8 + outGs.length := by
            have := henv_lt a (by omega); rw [hea] at this; exact this
          cases heb : env b with
          | const bb =>
            cases bb with
            | true =>
              exact hfinish outGs (.const true) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread trivial
                (fun y => by
                  have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                  rw [hop, hin]; simp only [List.map_cons, List.map_nil, GateOp.eval, symEval, ← h2]
                  simp)
            | false =>
              exact hfinish outGs (.ref u) ⟨[], by simp⟩ (by split_ifs <;> omega) hfan hread hu_lt
                (fun y => by
                  have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                  have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                  rw [hop, hin]; simp only [List.map_cons, List.map_nil, GateOp.eval, symEval, ← h1, ← h2]
                  simp)
          | ref v =>
            have hv_lt : v < 8 + outGs.length := by
              have := henv_lt b hblt; rw [heb] at this; exact this
            have hnot0K : 0 ∉ K := by
              intro h0
              obtain ⟨a0, ha0, bv, hbv⟩ := h0K_const h0
              rw [hin] at ha0; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha0
              rcases ha0 with rfl | rfl
              · rw [hea] at hbv; cases hbv
              · rw [heb] at hbv; cases hbv
            have ⟨hf', hr'⟩ := GoodAppend (g := ⟨GateOp.or, [u, v]⟩) hfan hread (by simp) (by simp)
              (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> omega)
            exact hfinish (outGs ++ [⟨GateOp.or, [u, v]⟩]) (.ref (8 + outGs.length)) ⟨_, rfl⟩
              (by simp [hnot0K]) hf' hr' (by simp [symLt])
              (fun y => by
                have h1 := henv_ev y a (by omega); rw [hea] at h1; simp only [symEval] at h1
                have h2 := henv_ev y b hblt; rw [heb] at h2; simp only [symEval] at h2
                simp only [symEval, run_snoc]
                have hlen : (run outGs (List.ofFn y)).length = 8 + outGs.length := by
                  rw [run_length, List.length_ofFn]
                rw [← hlen, getD_at, hop, hin]
                simp only [List.map_cons, List.map_nil, ← h1, ← h2])

private theorem main_thm : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩) := by
  rintro ⟨C, hfan, hsize, heval, hout, hwf, hdist, hused, hhead0, hhead1⟩
  let g0 : Gate := ⟨GateOp.and, [0, 1]⟩
  let g1 : Gate := ⟨GateOp.and, [2, 9]⟩
  rcases hgs : C.gates with _ | ⟨a0, tl0⟩
  · simp [hgs] at hhead0
  rcases tl0 with _ | ⟨a1, rest⟩
  · simp [hgs] at hhead1
  simp only [hgs, List.head?_cons, List.tail_cons, Option.some.injEq] at hhead0 hhead1
  subst hhead0 hhead1
  have hlenC : C.gates.length = rest.length + 2 := by simp [hgs]
  have hrest_le : rest.length ≤ 9 := by change C.gates.length ≤ 11 at hsize; omega
  have hpref_split : C.gates = [g0, g1] ++ rest := by simp [hgs, g0, g1]
  have hwire01 : ∀ x : Fin 9 → Bool,
      (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 1) ∧
      (C.wires (List.ofFn x)).getD 10 false = (x 2 && (x 0 && x 1)) := by
    intro x
    change (run C.gates (List.ofFn x)).getD 9 false = _ ∧
           (run C.gates (List.ofFn x)).getD 10 false = _
    rw [hpref_split]
    have h9 : (run ([g0, g1] ++ rest) (List.ofFn x)).getD 9 false =
        (run [g0, g1] (List.ofFn x)).getD 9 false :=
      run_prefix [g0, g1] rest (List.ofFn x) 9 (by simp)
    have h10 : (run ([g0, g1] ++ rest) (List.ofFn x)).getD 10 false =
        (run [g0, g1] (List.ofFn x)).getD 10 false :=
      run_prefix [g0, g1] rest (List.ofFn x) 10 (by simp)
    rw [h9, h10]
    have hrun2 : run [g0, g1] (List.ofFn x) =
        List.ofFn x ++ [x 0 && x 1] ++ [x 2 && (x 0 && x 1)] := by
      have h0 : run [g0] (List.ofFn x) = List.ofFn x ++ [x 0 && x 1] := by
        change run ([] ++ [g0]) (List.ofFn x) = _
        rw [run_snoc]
        simp [run, g0, GateOp.eval]
      change run ([g0] ++ [g1]) (List.ofFn x) = _
      rw [run_snoc, h0]
      simp [g1, GateOp.eval]
    rw [hrun2]
    constructor
    · rw [getD_lt _ _ _ (by simp)]
      simp
    · simp
  have hrest_pos : 0 < rest.length := by
    by_contra h0
    have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hout10 : C.output = 10 := by change C.output + 1 = 9 + C.gates.length at hout; omega
    let xtest : Fin 9 → Bool := fun i => decide (i.val < 3)
    have h1 := heval xtest
    change (C.wires (List.ofFn xtest)).getD C.output false = _ at h1
    rw [hout10, (hwire01 xtest).2] at h1
    have hL : (xtest 2 && (xtest 0 && xtest 1)) = true := by decide
    have hR : ((xtest 0 && xtest 4 && xtest 8) || (xtest 0 && xtest 5 && xtest 7) ||
        (xtest 1 && xtest 3 && xtest 8) || (xtest 1 && xtest 5 && xtest 6) ||
        (xtest 2 && xtest 3 && xtest 7) || (xtest 2 && xtest 4 && xtest 6)) = false := by decide
    rw [hL, hR] at h1
    cases h1
  have h1ltC : (⟨1, by omega⟩ : Fin C.gates.length).val + 1 < C.gates.length := by simp; omega
  obtain ⟨k1, hk1_gt, hk1_in⟩ := hused ⟨1, by omega⟩ h1ltC
  simp only at hk1_gt hk1_in
  have hk1_ge2 : 2 ≤ k1.val := by omega
  have hex_k2 : ∃ k2 : Fin C.gates.length, 2 ≤ k2.val ∧ 0 ∈ (C.gates.get k2).inputs := by
    by_contra hno
    push Not at hno
    let xA : Fin 9 → Bool := fun i => decide (i.val = 4 ∨ i.val = 8)
    let xB : Fin 9 → Bool := fun i => decide (i.val = 0 ∨ i.val = 4 ∨ i.val = 8)
    have heq_prefix : ∀ i, i ≠ 0 →
        (run [g0, g1] (List.ofFn xA)).getD i false = (run [g0, g1] (List.ofFn xB)).getD i false := by
      intro i hi0
      have hlenA : (run [g0, g1] (List.ofFn xA)).length = 11 := by rw [run_length]; simp
      have hlenB : (run [g0, g1] (List.ofFn xB)).length = 11 := by rw [run_length]; simp
      by_cases hi9 : i < 9
      · rw [run_input _ _ _ (by simp [hi9]), run_input _ _ _ (by simp [hi9]),
          List.getD_eq_getElem _ _ (by simp [hi9]), List.getD_eq_getElem _ _ (by simp [hi9]),
          List.getElem_ofFn, List.getElem_ofFn]
        simp [xA, xB, hi0]
      · by_cases hi10 : i = 9
        · subst hi10
          have h1 := (hwire01 xA).1
          have h2 := (hwire01 xB).1
          change (run C.gates (List.ofFn xA)).getD 9 false = _ at h1
          change (run C.gates (List.ofFn xB)).getD 9 false = _ at h2
          rw [hpref_split, run_prefix [g0, g1] rest _ 9 (by simp)] at h1 h2
          rw [h1, h2]; decide
        · by_cases hi11 : i = 10
          · subst hi11
            have h1 := (hwire01 xA).2
            have h2 := (hwire01 xB).2
            change (run C.gates (List.ofFn xA)).getD 10 false = _ at h1
            change (run C.gates (List.ofFn xB)).getD 10 false = _ at h2
            rw [hpref_split, run_prefix [g0, g1] rest _ 10 (by simp)] at h1 h2
            rw [h1, h2]; decide
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    have hno_rest : ∀ g ∈ rest, 0 ∉ g.inputs := by
      intro g hg
      obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hg
      have hget : C.gates.get ⟨r + 2, by omega⟩ = rest[r]'hr := by simp [hgs]
      rw [← hget]
      exact hno ⟨r + 2, by omega⟩ (by simp)
    have heval_eq : C.eval (List.ofFn xA) = C.eval (List.ofFn xB) := by
      change (run C.gates (List.ofFn xA)).getD C.output false =
        (run C.gates (List.ofFn xB)).getD C.output false
      rw [hpref_split]
      change (run rest (run [g0, g1] (List.ofFn xA))).getD C.output false =
        (run rest (run [g0, g1] (List.ofFn xB))).getD C.output false
      have hout_ne0 : C.output ≠ 0 := by change C.output + 1 = 9 + C.gates.length at hout; omega
      exact indep_eval 0 (run [g0, g1] (List.ofFn xA)) (run [g0, g1] (List.ofFn xB))
        (by rw [run_length, run_length]; simp) heq_prefix rest hno_rest C.output hout_ne0
    rw [heval xA, heval xB] at heval_eq
    have hA : ((xA 0 && xA 4 && xA 8) || (xA 0 && xA 5 && xA 7) || (xA 1 && xA 3 && xA 8) ||
        (xA 1 && xA 5 && xA 6) || (xA 2 && xA 3 && xA 7) || (xA 2 && xA 4 && xA 6)) = false := by decide
    have hB : ((xB 0 && xB 4 && xB 8) || (xB 0 && xB 5 && xB 7) || (xB 1 && xB 3 && xB 8) ||
        (xB 1 && xB 5 && xB 6) || (xB 2 && xB 3 && xB 7) || (xB 2 && xB 4 && xB 6)) = true := by decide
    rw [hA, hB] at heval_eq
    cases heval_eq
  obtain ⟨k2, hk2_ge2, hk2_in⟩ := hex_k2
  have hk1_ne_k2 : k1 ≠ k2 := by
    intro heq; subst heq
    have hwf_k := hwf k1
    have hback_k : ∀ i ∈ C.gates[k1.val].inputs, i < 9 + k1.val := by
      intro i hi
      rw [← List.get_eq_getElem] at hi
      rcases hwf_k with ⟨_, a, halt, hlist⟩ | ⟨_, a, b, hab, hblt, hlist⟩
      · rw [hlist] at hi; simp at hi; omega
      · rw [hlist] at hi; simp at hi; rcases hi with rfl | rfl <;> omega
    rcases hwf_k with ⟨_, a, _, hlist⟩ | ⟨hop, a, b, hab, _, hlist⟩
    · rw [hlist] at hk1_in hk2_in
      simp only [List.mem_singleton] at hk1_in hk2_in
      omega
    · rw [hlist] at hk1_in hk2_in
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk1_in hk2_in
      have ha0 : a = 0 := by rcases hk2_in with h | h <;> omega
      have hb10 : b = 10 := by rcases hk1_in with h | h <;> omega
      subst ha0 hb10
      rcases hop with hop | hop
      · obtain ⟨x, hxne⟩ := (hdist k1).2 10 (by omega)
        apply hxne
        change (run C.gates (List.ofFn x)).getD (9 + k1.val) false =
          (run C.gates (List.ofFn x)).getD 10 false
        have h9len : 9 + k1.val = (List.ofFn x).length + k1.val := by simp
        rw [h9len, run_gate_val C.gates (List.ofFn x) k1.val k1.isLt
          (fun i hi => by simp only [List.length_ofFn]; exact hback_k i hi)]
        rw [← List.get_eq_getElem, hop, hlist]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have h0x : (run C.gates (List.ofFn x)).getD 0 false = x 0 := by
          rw [run_input _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
        have h10x : (run C.gates (List.ofFn x)).getD 10 false = (x 2 && (x 0 && x 1)) := (hwire01 x).2
        rw [h0x, h10x]
        cases x 0 <;> cases x 1 <;> cases x 2 <;> rfl
      · obtain ⟨x, hxne⟩ := (hdist k1).2 0 (by omega)
        apply hxne
        change (run C.gates (List.ofFn x)).getD (9 + k1.val) false =
          (run C.gates (List.ofFn x)).getD 0 false
        have h9len : 9 + k1.val = (List.ofFn x).length + k1.val := by simp
        rw [h9len, run_gate_val C.gates (List.ofFn x) k1.val k1.isLt
          (fun i hi => by simp only [List.length_ofFn]; exact hback_k i hi)]
        rw [← List.get_eq_getElem, hop, hlist]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        have h0x : (run C.gates (List.ofFn x)).getD 0 false = x 0 := by
          rw [run_input _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; rfl
        have h10x : (run C.gates (List.ofFn x)).getD 10 false = (x 2 && (x 0 && x 1)) := (hwire01 x).2
        rw [h0x, h10x]
        cases x 0 <;> cases x 1 <;> cases x 2 <;> rfl
  let env0 : ℕ → SymWire := fun w =>
    if w = 0 then .const false
    else if w < 9 then .ref (w - 1)
    else .const false
  have henv0_lt : ∀ w < 9 + ([g0, g1] : List Gate).length, symLt (8 + ([] : List Gate).length) (env0 w) := by
    intro w hw
    simp only [env0]
    split_ifs <;> simp [symLt]; omega
  have henv0_ev : ∀ (y : Fin 8 → Bool) (w : ℕ), w < 9 + ([g0, g1] : List Gate).length →
      symEval y [] (env0 w) = (run [g0, g1] (List.ofFn (pad0 y))).getD w false := by
    intro y w hw
    simp only [List.length_cons, List.length_nil] at hw
    by_cases hw0 : w = 0
    · subst hw0
      simp only [env0, ↓reduceIte, symEval]
      rw [run_input _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      simp [pad0]
    · by_cases hw9 : w < 9
      · simp only [env0, hw0, hw9, ↓reduceIte, symEval]
        rw [run_input _ _ _ (by simp; omega), run_input _ _ _ (by simp [hw9]),
          List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp [hw9]),
          List.getElem_ofFn, List.getElem_ofFn]
        simp [pad0, hw0]
      · simp only [env0, hw0, hw9, ↓reduceIte, symEval]
        by_cases hw9eq : w = 9
        · subst hw9eq
          have h1 := (hwire01 (pad0 y)).1
          change (run C.gates (List.ofFn (pad0 y))).getD 9 false = _ at h1
          rw [hpref_split, run_prefix [g0, g1] rest _ 9 (by simp)] at h1
          rw [h1]; simp [pad0]
        · have hw10 : w = 10 := by omega
          subst hw10
          have h2 := (hwire01 (pad0 y)).2
          change (run C.gates (List.ofFn (pad0 y))).getD 10 false = _ at h2
          rw [hpref_split, run_prefix [g0, g1] rest _ 10 (by simp)] at h2
          rw [h2]; simp [pad0]
  have hwf_rest : ∀ k : Fin rest.length, wfGate (9 + ([g0, g1] : List Gate).length + k.val) (rest.get k) := by
    intro k
    have hk := hwf ⟨k.val + 2, by omega⟩
    have hget : C.gates.get ⟨k.val + 2, by omega⟩ = rest.get k := by simp [hgs]
    rw [hget] at hk
    have hlen : 9 + ([g0, g1] : List Gate).length + k.val = 9 + (k.val + 2) := by simp; omega
    rw [hlen]
    exact hk
  let K : Finset ℕ := {k1.val - 2, k2.val - 2}
  have hKcard : K.card = 2 := by
    have hne : k1.val - 2 ≠ k2.val - 2 := by
      intro heq
      apply hk1_ne_k2
      exact Fin.ext (by omega)
    simp [K, hne]
  have hK : ∀ k ∈ K, ∃ hk : k < rest.length,
      ∃ a ∈ rest[k].inputs, a < 9 + ([g0, g1] : List Gate).length ∧ isConstWire env0 a := by
    intro k hk
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · have hklt : k1.val - 2 < rest.length := by omega
      have hget : C.gates.get k1 = rest[k1.val - 2]'hklt := by
        simp only [List.get_eq_getElem]
        have h1 : C.gates[k1.val]'k1.isLt = C.gates[(k1.val - 2) + 2]'(by omega) := by
          congr 1; omega
        rw [h1]
        simp [hgs]
      refine ⟨hklt, 10, by rw [← hget]; exact hk1_in, by simp, false, by simp [env0]⟩
    · have hklt : k2.val - 2 < rest.length := by omega
      have hget : C.gates.get k2 = rest[k2.val - 2]'hklt := by
        simp only [List.get_eq_getElem]
        have h1 : C.gates[k2.val]'k2.isLt = C.gates[(k2.val - 2) + 2]'(by omega) := by
          congr 1; omega
        rw [h1]
        simp [hgs]
      refine ⟨hklt, 0, by rw [← hget]; exact hk2_in, by simp, false, by simp [env0]⟩
  have hred := reduceGates_spec rest [g0, g1] env0 []
    (fun _ h => by cases h) (fun _ h => by simp at h) hwf_rest henv0_lt henv0_ev K hK
  set res := reduceGates rest env0 [] (9 + ([g0, g1] : List Gate).length)
  obtain ⟨hDfan, hDread, hDlen, hDlt, hDev⟩ := hred
  have hout_ltC : C.output < 9 + ([g0, g1] : List Gate).length + rest.length := by
    change C.output + 1 = 9 + C.gates.length at hout
    simp; omega
  have heval_pad0 : ∀ y : Fin 8 → Bool,
      (run ([g0, g1] ++ rest) (List.ofFn (pad0 y))).getD C.output false = f0 y := by
    intro y
    rw [← perm3_pad0 y]
    have h1 := heval (pad0 y)
    change (run C.gates (List.ofFn (pad0 y))).getD C.output false = perm3 (pad0 y) at h1
    rw [hpref_split] at h1
    exact h1
  cases hout_sw : res.2 C.output with
  | const b =>
    have hconst : ∀ y : Fin 8 → Bool, f0 y = b := by
      intro y
      have h1 := hDev y C.output hout_ltC
      rw [hout_sw, heval_pad0 y] at h1
      exact h1.symm
    have h0 := hconst (fun _ => false)
    have h1 := hconst (fun _ => true)
    have hf0 : f0 (fun _ => false) = false := by decide
    have hf1 : f0 (fun _ => true) = true := by decide
    rw [hf0] at h0; rw [hf1] at h1
    rw [← h0] at h1; cases h1
  | ref outW =>
    apply no_circuit_le7
    refine ⟨⟨res.1, outW⟩, hDfan, hDread, ?_, ?_⟩
    · change res.1.length ≤ 7
      simp only [List.length_nil, Nat.zero_add] at hDlen
      omega
    · intro y
      have h1 := hDev y C.output hout_ltC
      rw [hout_sw, heval_pad0 y] at h1
      exact h1

end PEqualNP.Outside.L_meta_27146_aux

theorem PEqualNP.Outside.L_meta_27146 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩)) :=
  PEqualNP.Outside.L_meta_27146_aux.main_thm
