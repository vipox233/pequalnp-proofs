import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19535_aux
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

def tl (n u v : ℕ) : ℕ → Bool
  | 0 => decide (1 ≤ v)
  | 1 => decide (u = 0 ∧ 1 ≤ v)
  | 2 => decide (v + 2 ≤ n)
  | 3 => decide (2 ≤ u ∧ v + 2 ≤ n)
  | 4 => decide (u = 1 ∧ v = 0)
  | 5 => decide ((u = 0 ∧ 1 ≤ v) ∨ (2 ≤ u ∧ v + 2 ≤ n))
  | 6 => decide ((u = 0 ∧ 1 ≤ v) ∨ (u = 1 ∧ v = 0) ∨ (2 ≤ u ∧ v + 2 ≤ n))
  | _ => false

def val (n u v k : ℕ) : Bool :=
  if k < n - 3 then decide (1 ≤ v ∧ v ≤ k + 2)
  else if k < 2 * (n - 3) then decide (2 ≤ u ∧ u ≤ k - (n - 3) + 3)
  else tl n u v (k - 2 * (n - 3))

def f (n u v w : ℕ) : Bool :=
  if w < n then decide (u = w) else if w < 2 * n then decide (v + n = w) else val n u v (w - 2 * n)

def ai (n k : ℕ) : ℕ := if k = 0 then n + 1 else 2 * n + k - 1
def ri (n k : ℕ) : ℕ := if k = n - 3 then 2 else 2 * n + k - 1

def gate (n k : ℕ) : Gate :=
  if k < n - 3 then ⟨GateOp.or, [ai n k, n + k + 2]⟩
  else if k < 2 * (n - 3) then ⟨GateOp.or, [ri n k, k - (n - 3) + 3]⟩
  else if k = 2 * (n - 3) then ⟨GateOp.or, [ai n (n - 3), 2 * n - 1]⟩
  else if k = 2 * (n - 3) + 1 then ⟨GateOp.and, [0, 2 * n + 2 * (n - 3)]⟩
  else if k = 2 * (n - 3) + 2 then ⟨GateOp.or, [ai n (n - 3), n]⟩
  else if k = 2 * (n - 3) + 3 then ⟨GateOp.and, [ri n (2 * (n - 3)), 2 * n + (2 * (n - 3) + 2)]⟩
  else if k = 2 * (n - 3) + 4 then ⟨GateOp.and, [1, n]⟩
  else if k = 2 * (n - 3) + 5 then ⟨GateOp.or, [2 * n + (2 * (n - 3) + 1), 2 * n + (2 * (n - 3) + 3)]⟩
  else ⟨GateOp.or, [2 * n + (2 * (n - 3) + 5), 2 * n + (2 * (n - 3) + 4)]⟩

theorem fX (n u v w : ℕ) (h : w < n) : f n u v w = decide (u = w) := by simp [f, h]

theorem fY (n u v w : ℕ) (h1 : n ≤ w) (h2 : w < 2 * n) : f n u v w = decide (v + n = w) := by
  simp [f, h2, show ¬ w < n by omega]

theorem fG (n u v k : ℕ) : f n u v (2 * n + k) = val n u v k := by
  simp [f, show ¬ 2 * n + k < n by omega]

theorem vC (n u v k : ℕ) (h : k < n - 3) : val n u v k = decide (1 ≤ v ∧ v ≤ k + 2) := by simp [val, h]

theorem vR (n u v k : ℕ) (h1 : n - 3 ≤ k) (h2 : k < 2 * (n - 3)) :
    val n u v k = decide (2 ≤ u ∧ u ≤ k - (n - 3) + 3) := by
  simp [val, h2, show ¬ k < n - 3 by omega]

theorem vT (n u v k j : ℕ) (h : k = 2 * (n - 3) + j) : val n u v k = tl n u v j := by
  subst h; rw [val, ite_cond_eq_false _ _ (eq_false (by omega)), ite_cond_eq_false _ _ (eq_false (by omega)), Nat.add_sub_cancel_left]

theorem fA (n u v k : ℕ) (hn : 3 ≤ n) (hk : k ≤ n - 3) : f n u v (ai n k) = decide (1 ≤ v ∧ v ≤ k + 1) := by
  unfold ai
  split_ifs with h
  · subst h; rw [fY n u v (n + 1) (by omega) (by omega)]; exact decide_eq_decide.2 (by omega)
  · rw [show 2 * n + k - 1 = 2 * n + (k - 1) by omega, fG, vC n u v _ (by omega)]
    exact decide_eq_decide.2 (by omega)

theorem fRi (n u v k : ℕ) (hn : 3 ≤ n) (h1 : n - 3 ≤ k) (h2 : k ≤ 2 * (n - 3)) :
    f n u v (ri n k) = decide (2 ≤ u ∧ u ≤ k - (n - 3) + 2) := by
  unfold ri
  split_ifs with h
  · rw [fX n u v 2 (by omega)]; exact decide_eq_decide.2 (by omega)
  · rw [show 2 * n + k - 1 = 2 * n + (k - 1) by omega, fG, vR n u v _ (by omega) (by omega)]
    exact decide_eq_decide.2 (by omega)

theorem gate_ok (n u v k : ℕ) (hn : 3 ≤ n) (hu : u < n) (hv : v < n) (hk : k < 2 * n + 1) :
    (∀ i ∈ (gate n k).inputs, i < 2 * n + k) ∧
      (gate n k).op.eval ((gate n k).inputs.map (f n u v)) = f n u v (2 * n + k) := by
  unfold gate
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> refine ⟨fun i hi => ?_, ?_⟩
  all_goals first
    | (simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
       rcases hi with rfl | rfl <;> (try simp only [ai, ri]) <;> (try split_ifs) <;> omega)
    | skip
  all_goals simp only [List.map, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id,
      Bool.or_false, Bool.and_true, fG]
  · rw [fA n u v k hn (by omega), fY n u v _ (by omega) (by omega), vC n u v k h1]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [fRi n u v k hn (by omega) (by omega), fX n u v _ (by omega), vR n u v k (by omega) h2]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [fA n u v _ hn le_rfl, fY n u v _ (by omega) (by omega), vT n u v k 0 (by omega)]
    simp only [tl]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [fX n u v 0 (by omega), vT n u v _ 0 (by omega), vT n u v k 1 (by omega)]
    simp only [tl]
    apply Bool.eq_iff_iff.2; simp only [Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [fA n u v _ hn le_rfl, fY n u v _ (by omega) (by omega), vT n u v k 2 (by omega)]
    simp only [tl]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [fRi n u v (2 * (n - 3)) hn (by omega) le_rfl, vT n u v _ 2 rfl, vT n u v k 3 (by omega)]
    simp only [tl]
    apply Bool.eq_iff_iff.2; simp only [Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [fX n u v 1 (by omega), fY n u v _ (by omega) (by omega), vT n u v k 4 (by omega)]
    simp only [tl]
    apply Bool.eq_iff_iff.2; simp only [Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [vT n u v _ 1 rfl, vT n u v _ 3 rfl, vT n u v k 5 (by omega)]
    simp only [tl]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega
  · rw [vT n u v _ 5 rfl, vT n u v _ 4 rfl, vT n u v k 6 (by omega)]
    simp only [tl]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;> omega

end PEqualNP.Outside.L_meta_19535_aux

open PEqualNP.Outside.L_meta_19535_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19535 : ∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u.val = 0 ∧ 1 ≤ v.val) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val + 2 ≤ n))) (2 * n + 1) := by
  intro n hn
  refine ⟨⟨(List.range (2 * n + 1)).map (gate n), 2 * n + (2 * (n - 3) + 6)⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, -, rfl⟩ := hg
    unfold gate
    split_ifs <;> simp
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
    show (List.foldl stp (PEqualNP.Represents.oneEach u v) ((List.range (2 * n + 1)).map (gate n))).getD (2 * n + (2 * (n - 3) + 6)) false = _
    rw [spec (f n u v) _ _ hx (fun k hk => by
      simp only [List.length_map, List.length_range] at hk
      simp only [List.getElem_map, List.getElem_range, hl]
      exact gate_ok n u v k hn u.2 v.2 hk) _ (by simp [hl]; omega), fG, vT n u v _ 6 rfl]
    simp only [tl]
