import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20544_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem spec (f : ℕ → Bool) : ∀ (gs : List Gate) (x : List Bool),
    (∀ i < x.length, x.getD i false = f i) →
    (∀ k (h : k < gs.length), (∀ i ∈ gs[k].inputs, i < x.length + k) ∧
      gs[k].op.eval (gs[k].inputs.map f) = f (x.length + k)) →
    ∀ i < x.length + gs.length, (gs.foldl stp x).getD i false = f i := by
  intro gs
  induction gs with
  | nil => intro x hx _ i hi; exact hx i (by simpa using hi)
  | cons g gs ih =>
    intro x hx hg i hi
    obtain ⟨h1, h2⟩ := hg 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h1 h2
    have hl : (stp x g).length = x.length + 1 := by simp [stp]
    have hx' : ∀ i < (stp x g).length, (stp x g).getD i false = f i := by
      intro i hi
      rw [stp, getD_snoc]
      split_ifs with h3 h4
      · exact hx i h3
      · subst h4; rw [← h2]; congr 1
        exact List.map_congr_left fun j hj => hx j (by have := h1 j hj; omega)
      · omega
    refine ih (stp x g) hx' (fun k hk => ?_) i (by simp at hi; omega)
    obtain ⟨h5, h6⟩ := hg (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at h5 h6
    exact ⟨fun j hj => by have := h5 j hj; omega, by rw [h6, hl]; congr 1; omega⟩

def tl (u v : ℕ) : ℕ → Bool
  | 0 => decide (v ≤ 1)
  | 1 => decide (u ≤ 1)
  | 2 => decide (2 ≤ u)
  | 3 => decide (1 ≤ u)
  | 4 => decide (u = 0 ∨ 3 ≤ u)
  | 5 => decide (3 ≤ v ∧ u ≤ 1)
  | 6 => decide (v ≤ 1 ∧ 1 ≤ u)
  | 7 => decide (v = 2 ∧ (u = 0 ∨ 3 ≤ u))
  | 8 => decide ((3 ≤ v ∧ u ≤ 1) ∨ (v ≤ 1 ∧ 1 ≤ u))
  | 9 => decide ((u = 0 ∧ 2 ≤ v) ∨ (u = 1 ∧ (v ≤ 1 ∨ 3 ≤ v)) ∨ (u = 2 ∧ v ≤ 1) ∨ (3 ≤ u ∧ v ≤ 2))
  | _ => false

def val (n u v k : ℕ) : Bool :=
  if k < n - 4 then decide (3 ≤ v ∧ v ≤ k + 4)
  else if k < 2 * (n - 4) then decide (3 ≤ u ∧ u ≤ k - (n - 4) + 4)
  else tl u v (k - 2 * (n - 4))

def f (n u v w : ℕ) : Bool :=
  if w < n then decide (u = w) else if w < 2 * n then decide (v + n = w) else val n u v (w - 2 * n)

def ay (n k : ℕ) : ℕ := if k = 0 then n + 3 else 2 * n + k - 1
def ax (n k : ℕ) : ℕ := if k = n - 4 then 3 else 2 * n + k - 1

def tg (n : ℕ) : ℕ → Gate
  | 0 => ⟨GateOp.or, [n, n + 1]⟩
  | 1 => ⟨GateOp.or, [0, 1]⟩
  | 2 => ⟨GateOp.or, [2, ax n (2 * (n - 4))]⟩
  | 3 => ⟨GateOp.or, [1, 2 * n + (2 * (n - 4) + 2)]⟩
  | 4 => ⟨GateOp.or, [0, ax n (2 * (n - 4))]⟩
  | 5 => ⟨GateOp.and, [ay n (n - 4), 2 * n + (2 * (n - 4) + 1)]⟩
  | 6 => ⟨GateOp.and, [2 * n + 2 * (n - 4), 2 * n + (2 * (n - 4) + 3)]⟩
  | 7 => ⟨GateOp.and, [n + 2, 2 * n + (2 * (n - 4) + 4)]⟩
  | 8 => ⟨GateOp.or, [2 * n + (2 * (n - 4) + 5), 2 * n + (2 * (n - 4) + 6)]⟩
  | 9 => ⟨GateOp.or, [2 * n + (2 * (n - 4) + 8), 2 * n + (2 * (n - 4) + 7)]⟩
  | _ => ⟨GateOp.or, []⟩

theorem tg_ok (n j : ℕ) : ((tg n j).op = GateOp.and ∨ (tg n j).op = GateOp.or) ∧ (tg n j).inputs.length ≤ 2 := by
  unfold tg; split <;> simp

def gate (n k : ℕ) : Gate :=
  if k < n - 4 then ⟨GateOp.or, [ay n k, n + k + 4]⟩
  else if k < 2 * (n - 4) then ⟨GateOp.or, [ax n k, k - (n - 4) + 4]⟩
  else tg n (k - 2 * (n - 4))

theorem fX (n u v w : ℕ) (h : w < n) : f n u v w = decide (u = w) := by simp [f, h]

theorem fY (n u v w : ℕ) (h1 : n ≤ w) (h2 : w < 2 * n) : f n u v w = decide (v + n = w) := by
  simp [f, h2, show ¬ w < n by omega]

theorem fG (n u v k : ℕ) : f n u v (2 * n + k) = val n u v k := by
  simp [f, show ¬ 2 * n + k < n by omega]

theorem vC (n u v k : ℕ) (h : k < n - 4) : val n u v k = decide (3 ≤ v ∧ v ≤ k + 4) := by simp [val, h]

theorem vR (n u v k : ℕ) (h1 : n - 4 ≤ k) (h2 : k < 2 * (n - 4)) :
    val n u v k = decide (3 ≤ u ∧ u ≤ k - (n - 4) + 4) := by
  simp [val, h2, show ¬ k < n - 4 by omega]

theorem vT (n u v k j : ℕ) (h : k = 2 * (n - 4) + j) : val n u v k = tl u v j := by
  subst h; rw [val, ite_cond_eq_false _ _ (eq_false (by omega)), ite_cond_eq_false _ _ (eq_false (by omega)), Nat.add_sub_cancel_left]

theorem fA (n u v k : ℕ) (hn : 4 ≤ n) (hk : k ≤ n - 4) : f n u v (ay n k) = decide (3 ≤ v ∧ v ≤ k + 3) := by
  unfold ay
  split_ifs with h
  · subst h; rw [fY n u v (n + 3) (by omega) (by omega)]; exact decide_eq_decide.2 (by omega)
  · rw [show 2 * n + k - 1 = 2 * n + (k - 1) by omega, fG, vC n u v _ (by omega)]
    exact decide_eq_decide.2 (by omega)

theorem fRi (n u v k : ℕ) (hn : 4 ≤ n) (h1 : n - 4 ≤ k) (h2 : k ≤ 2 * (n - 4)) :
    f n u v (ax n k) = decide (3 ≤ u ∧ u ≤ k - (n - 4) + 3) := by
  unfold ax
  split_ifs with h
  · rw [fX n u v 3 (by omega)]; exact decide_eq_decide.2 (by omega)
  · rw [show 2 * n + k - 1 = 2 * n + (k - 1) by omega, fG, vR n u v _ (by omega) (by omega)]
    exact decide_eq_decide.2 (by omega)

theorem gate_ok (n u v k : ℕ) (hn : 4 ≤ n) (hu : u < n) (hv : v < n) (hk : k < 2 * n + 2) :
    (∀ i ∈ (gate n k).inputs, i < 2 * n + k) ∧
      (gate n k).op.eval ((gate n k).inputs.map (f n u v)) = f n u v (2 * n + k) := by
  unfold gate
  split_ifs with h1 h2
  · refine ⟨fun i hi => ?_, ?_⟩
    · (simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> (try simp only [ay, ax]) <;> (try split_ifs) <;> omega)
    · simp only [List.map, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id,
        Bool.or_false, Bool.and_true, fG]
      rw [fA n u v k hn (by omega), fY n u v _ (by omega) (by omega), vC n u v k h1]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · refine ⟨fun i hi => ?_, ?_⟩
    · (simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> (try simp only [ay, ax]) <;> (try split_ifs) <;> omega)
    · simp only [List.map, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id,
        Bool.or_false, Bool.and_true, fG]
      rw [fRi n u v k hn (by omega) (by omega), fX n u v _ (by omega), vR n u v k (by omega) h2]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * (n - 4) + j := ⟨k - 2 * (n - 4), by omega⟩
    rw [Nat.add_sub_cancel_left]
    have hj : j < 10 := by omega
    interval_cases j <;> simp only [tg] <;> refine ⟨fun i hi => ?_, ?_⟩
    all_goals first
      | (simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> (try simp only [ay, ax]) <;> (try split_ifs) <;> omega)
      | skip
    all_goals simp only [List.map, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id,
        Bool.or_false, Bool.and_true, fG]
    · rw [fY n u v n (by omega) (by omega), fY n u v (n + 1) (by omega) (by omega), vT n u v _ 0 rfl]
      simp only [tl]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
    · rw [fX n u v 0 (by omega), fX n u v 1 (by omega), vT n u v _ 1 rfl]
      simp only [tl]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
    · rw [fX n u v 2 (by omega), fRi n u v _ hn (by omega) le_rfl, vT n u v _ 2 rfl]
      simp only [tl]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
    · rw [fX n u v 1 (by omega), vT n u v _ 2 rfl, vT n u v _ 3 rfl]
      simp only [tl]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
    · rw [fX n u v 0 (by omega), fRi n u v _ hn (by omega) le_rfl, vT n u v _ 4 rfl]
      simp only [tl]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
    · rw [fA n u v _ hn le_rfl, vT n u v _ 1 rfl, vT n u v _ 5 rfl]
      simp only [tl]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
    · rw [vT n u v _ 0 (by omega), vT n u v _ 3 rfl, vT n u v _ 6 rfl]
      simp only [tl]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
    · rw [fY n u v (n + 2) (by omega) (by omega), vT n u v _ 4 rfl, vT n u v _ 7 rfl]
      simp only [tl]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
    · rw [vT n u v _ 5 rfl, vT n u v _ 6 rfl, vT n u v _ 8 rfl]
      simp only [tl]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
    · rw [vT n u v _ 8 rfl, vT n u v _ 7 rfl, vT n u v _ 9 rfl]
      simp only [tl]
      apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega

end PEqualNP.Outside.L_meta_20544_aux

open PEqualNP.Outside.L_meta_20544_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_20544 : ∀ n : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u.val = 0 ∧ 2 ≤ v.val) ∨ (u.val = 1 ∧ (v.val ≤ 1 ∨ 3 ≤ v.val)) ∨ (u.val = 2 ∧ v.val ≤ 1) ∨ (3 ≤ u.val ∧ v.val ≤ 2))) (2 * n + 2) := by
  intro n hn
  refine ⟨⟨(List.range (2 * n + 2)).map (gate n), 2 * n + (2 * (n - 4) + 9)⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, -, rfl⟩ := hg
    unfold gate
    split_ifs
    · simp
    · simp
    · exact tg_ok n _
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = 2 * n := by
      simp [PEqualNP.Represents.oneEach]; omega
    have hx : ∀ i < (PEqualNP.Represents.oneEach u v).length,
        (PEqualNP.Represents.oneEach u v).getD i false = f n u v i := by
      intro i hi
      rw [hl] at hi
      apply Bool.eq_iff_iff.2
      simp only [PEqualNP.Represents.oneEach, List.getD_eq_getElem?_getD, List.getElem?_append,
        List.length_ofFn, List.getElem?_ofFn, f]
      split_ifs <;> simp [Fin.ext_iff] <;> omega
    show (List.foldl stp (PEqualNP.Represents.oneEach u v) ((List.range (2 * n + 2)).map (gate n))).getD (2 * n + (2 * (n - 4) + 9)) false = _
    rw [spec (f n u v) _ _ hx (fun k hk => by
      simp only [List.length_map, List.length_range] at hk
      simp only [List.getElem_map, List.getElem_range, hl]
      exact gate_ok n u v k hn u.2 v.2 hk) _ (by simp [hl]; omega), fG, vT n u v _ 9 rfl]
    simp only [tl]
