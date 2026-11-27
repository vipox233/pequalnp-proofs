import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_687_aux

def L (D : Finset ℕ) (n : ℕ) : List ℕ := (List.range n).filter (fun j => decide (j ∉ D))

def cnt (D : Finset ℕ) (n : ℕ) : ℕ := (D.filter (fun i => i < n)).card

theorem L_succ (D : Finset ℕ) (n : ℕ) : L D (n+1) = L D n ++ (if n ∈ D then [] else [n]) := by
  unfold L
  rw [List.range_succ, List.filter_append]
  by_cases h : n ∈ D <;> simp [h]

theorem cnt_succ (D : Finset ℕ) (n : ℕ) : cnt D (n+1) = cnt D n + (if n ∈ D then 1 else 0) := by
  unfold cnt
  by_cases h : n ∈ D
  · have e : D.filter (fun i => i < n+1) = insert n (D.filter (fun i => i < n)) := by
      ext a; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
      · rintro ⟨ha, hlt⟩; by_cases han : a = n
        · left; exact han
        · right; exact ⟨ha, by omega⟩
      · rintro (rfl | ⟨ha, hlt⟩)
        · exact ⟨h, by omega⟩
        · exact ⟨ha, by omega⟩
    rw [e, Finset.card_insert_of_notMem (by simp), if_pos h]
  · have e : D.filter (fun i => i < n+1) = D.filter (fun i => i < n) := by
      ext a; simp only [Finset.mem_filter]; constructor
      · rintro ⟨ha, hlt⟩; refine ⟨ha, ?_⟩; by_contra hc
        have : a = n := by omega
        exact h (this ▸ ha)
      · rintro ⟨ha, hlt⟩; exact ⟨ha, by omega⟩
    rw [e, if_neg h]; rfl

theorem L_len (D : Finset ℕ) : ∀ n, (L D n).length + cnt D n = n := by
  intro n
  induction n with
  | zero => simp [L, cnt]
  | succ n ih =>
    rw [L_succ, cnt_succ, List.length_append]
    by_cases h : n ∈ D <;> simp [h] <;> omega

theorem cnt_mono (D : Finset ℕ) (i n : ℕ) (h : i ≤ n) : cnt D i ≤ cnt D n := by
  unfold cnt
  exact Finset.card_le_card (fun a ha => by
    simp only [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, by omega⟩)

theorem cnt_gap (D : Finset ℕ) (i : ℕ) (hi : i ∉ D) : ∀ n, i < n → cnt D n + i + 1 ≤ cnt D i + n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rw [cnt_succ]
    by_cases hin : i = n
    · subst hin
      rw [if_neg hi]
      omega
    · have := ih (by omega)
      split_ifs <;> omega

theorem L_get (D : Finset ℕ) (d : ℕ) : ∀ n, ∀ i < n, i ∉ D → (L D n).getD (i - cnt D i) d = i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi hiD
    rw [L_succ]
    by_cases hin : i = n
    · subst hin
      rw [if_neg hiD]
      have hl := L_len D i
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have : i - cnt D i - (L D i).length = 0 := by omega
      rw [this]; rfl
    · have hlt : i < n := by omega
      have hl := L_len D n
      have hg := cnt_gap D i hiD n hlt
      have hidx : i - cnt D i < (L D n).length := by
        have hci : cnt D i ≤ i := by
          have := L_len D i
          omega
        omega
      rw [List.getD_append _ _ _ _ hidx]
      exact ih i hlt hiD

open PEqualNP.CircuitLowerBounds

def er (D : Finset ℕ) (v : List Bool) : List Bool := (L D v.length).map (fun i => v.getD i false)

theorem cnt_full (D : Finset ℕ) (n : ℕ) (h : ∀ a ∈ D, a < n) : cnt D n = D.card := by
  unfold cnt
  rw [Finset.filter_true_of_mem h]

theorem key (D : Finset ℕ) (k : ℕ) (hD : ∀ a ∈ D, a < k) (w : List Bool) (hw : k ≤ w.length)
    (i : ℕ) (hi : i ∉ D) : (er D w).getD (i - cnt D i) false = w.getD i false := by
  unfold er
  have hm := List.getD_map (fun j => w.getD j false) (l := L D w.length) (d := w.length) (n := i - cnt D i)
  have hf : w.getD w.length false = false := by simp
  rw [hf] at hm
  rw [hm]
  by_cases hil : i < w.length
  · rw [L_get D w.length w.length i hil hi]
  · have h1 : cnt D i = D.card := cnt_full D i (fun a ha => by have := hD a ha; omega)
    have h2 : cnt D w.length = D.card := cnt_full D w.length (fun a ha => by have := hD a ha; omega)
    have hl := L_len D w.length
    have hidx : (L D w.length).getD (i - cnt D i) w.length = w.length :=
      List.getD_eq_default _ _ (by omega)
    rw [hidx, hf, List.getD_eq_default _ _ (by omega : w.length ≤ i)]

theorem er_snoc (D : Finset ℕ) (w : List Bool) (b : Bool) (h : w.length ∉ D) :
    er D (w ++ [b]) = er D w ++ [b] := by
  unfold er
  rw [List.length_append, List.length_singleton, L_succ, if_neg h, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have : i < w.length := by
      unfold L at hi
      simp only [List.mem_filter, List.mem_range] at hi
      exact hi.1
    rw [List.getD_append _ _ _ _ this]
  · simp

theorem main_ind (D : Finset ℕ) (k : ℕ) (hD : ∀ a ∈ D, a < k) :
    ∀ (gs : List Gate), (∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ D) → ∀ w : List Bool, k ≤ w.length →
    (gs.map (fun g => (⟨g.op, g.inputs.map (fun w => w - cnt D w)⟩ : Gate))).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (er D w) =
    er D (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  intro gs
  induction gs with
  | nil => intro _ w _; rfl
  | cons g gs ih =>
    intro hg w hw
    simp only [List.map_cons, List.foldl_cons]
    have hval : (g.inputs.map (fun w => w - cnt D w)).map (fun i => (er D w).getD i false) =
        g.inputs.map (fun i => w.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact key D k hD w hw i (hg g (List.mem_cons_self) i hi)
    rw [hval, ← er_snoc D w _ (fun h => by have := hD _ h; omega)]
    exact ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _ (by simp; omega)

end PEqualNP.Outside.L_lib_687_aux

theorem PEqualNP.Outside.L_lib_687 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) (D : Finset ℕ),
  (∀ i ∈ D, i < x.length) →
  (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ D) →
  let erase : List Bool → List Bool := fun v =>
    ((List.range v.length).filter fun i => decide (i ∉ D)).map fun i => v.getD i false
  let ren : ℕ → ℕ := fun w => w - (D.filter fun i => i < w).card
  let small : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ren⟩), ren C.output⟩
  small.wires (erase x) = erase (C.wires x) := by
  intro C x D hD hg erase ren small
  exact PEqualNP.Outside.L_lib_687_aux.main_ind D x.length hD C.gates hg x le_rfl
