import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20784_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def P (xs : List Bool) (t : ℕ) : Bool := decide ((xs.take (t + 1)).count true % 2 = 1)

theorem P0 (xs : List Bool) (h : 0 < xs.length) : P xs 0 = xs.getD 0 false := by
  obtain ⟨b, ys, rfl⟩ : ∃ b ys, xs = b :: ys := by
    cases xs with
    | nil => simp at h
    | cons b ys => exact ⟨b, ys, rfl⟩
  cases b <;> simp [P]

theorem Ps (xs : List Bool) (t : ℕ) (h : t + 1 < xs.length) :
    P xs (t + 1) = ((P xs t || xs.getD (t + 1) false) && !(P xs t && xs.getD (t + 1) false)) := by
  unfold P
  rw [List.take_succ, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, Option.getD_some, List.count_append]
  generalize (List.take (t + 1) xs).count true = c
  generalize xs[t + 1] = b
  cases b <;> rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [Nat.add_mod, h]

def pw (n t : ℕ) : ℕ := if t = 0 then 0 else n + 4 * t - 1

def gate (n k : ℕ) : Gate :=
  if k % 4 = 0 then ⟨GateOp.or, [pw n (k / 4), k / 4 + 1]⟩
  else if k % 4 = 1 then ⟨GateOp.and, [pw n (k / 4), k / 4 + 1]⟩
  else if k % 4 = 2 then ⟨GateOp.not, [n + k - 1]⟩
  else ⟨GateOp.and, [n + k - 3, n + k - 1]⟩

def f (n : ℕ) (xs : List Bool) (w : ℕ) : Bool :=
  if w < n then xs.getD w false
  else if (w - n) % 4 = 0 then (P xs ((w - n) / 4) || xs.getD ((w - n) / 4 + 1) false)
  else if (w - n) % 4 = 1 then (P xs ((w - n) / 4) && xs.getD ((w - n) / 4 + 1) false)
  else if (w - n) % 4 = 2 then !(P xs ((w - n) / 4) && xs.getD ((w - n) / 4 + 1) false)
  else P xs ((w - n) / 4 + 1)

theorem pw_lt (n t k : ℕ) (h : 4 * t ≤ k) (hn : 1 ≤ n) : pw n t < n + k := by
  unfold pw; split_ifs <;> omega

theorem fP (n : ℕ) (xs : List Bool) (hl : xs.length = n) (t : ℕ) (ht : t + 1 < n) :
    f n xs (pw n t) = P xs t := by
  unfold pw
  split_ifs with h0
  · subst h0; rw [P0 xs (by omega)]; simp [f, show 0 < n by omega]
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [f, show ¬ n + 4 * (s + 1) - 1 < n by omega, if_false,
      show (n + 4 * (s + 1) - 1 - n) % 4 = 3 by omega, show (n + 4 * (s + 1) - 1 - n) / 4 = s by omega]
    simp

theorem gate_ok (n : ℕ) (xs : List Bool) (hl : xs.length = n) (k : ℕ) (hk : k < 4 * (n - 1)) :
    (∀ i ∈ (gate n k).inputs, i < n + k) ∧
      (gate n k).op.eval ((gate n k).inputs.map (f n xs)) = f n xs (n + k) := by
  have hb : f n xs (k / 4 + 1) = xs.getD (k / 4 + 1) false := by simp [f, show k / 4 + 1 < n by omega]
  have hp := pw_lt n (k / 4) k (by omega) (by omega)
  have hf := fP n xs hl (k / 4) (by omega)
  unfold gate
  split_ifs with h0 h1 h2 <;> refine ⟨by simp; omega, ?_⟩ <;>
    simp only [List.map, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id,
      Bool.or_false, Bool.and_true, List.headD_cons, hb, hf]
  · simp [f, h0]
  · simp [f, h1]
  · simp only [f, show ¬ n + k < n by omega, if_false,
      show (n + k - 1 - n) % 4 = 1 by omega, show (n + k - n) % 4 = 2 by omega,
      show (n + k - n) / 4 = k / 4 by omega]
    simp [show ¬ n + k - 1 < n by omega, show (n + k - 1 - n) / 4 = k / 4 by omega]
  · simp only [f, show ¬ n + k < n by omega, if_false,
      show (n + k - 1 - n) % 4 = 2 by omega, show (n + k - 3 - n) % 4 = 0 by omega,
      show (n + k - 3 - n) / 4 = k / 4 by omega, show (n + k - n) % 4 = 3 by omega,
      show (n + k - n) / 4 = k / 4 by omega]
    simp [show ¬ n + k - 1 < n by omega, show ¬ n + k - 3 < n by omega,
      show (n + k - 1 - n) / 4 = k / 4 by omega]
    rw [Ps xs (k / 4) (by omega)]
    simp

end PEqualNP.Outside.L_meta_20784_aux

open PEqualNP.Outside.L_meta_20784_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_20784 : ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((List.ofFn x).count true % 2 = 1)) (4 * (n - 1)) := by
  intro n hn
  refine ⟨⟨(List.range (4 * (n - 1))).map (gate n), 5 * n - 5⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, -, rfl⟩ := hg
    unfold gate
    split_ifs <;> simp
  · intro x
    have hl : (List.ofFn x).length = n := by simp
    have hx : ∀ i < (List.ofFn x).length, (List.ofFn x).getD i false = f n (List.ofFn x) i := by
      intro i hi
      rw [hl] at hi
      simp [f, hi]
    show (List.foldl stp (List.ofFn x) ((List.range (4 * (n - 1))).map (gate n))).getD (5 * n - 5) false = decide ((List.ofFn x).count true % 2 = 1)
    rw [spec (f n (List.ofFn x)) _ _ hx (fun k hk => by
      simp only [List.length_map, List.length_range] at hk
      simp only [List.getElem_map, List.getElem_range, hl]
      exact gate_ok n _ hl k hk) _ (by simp [hl]; omega)]
    have hP : P (List.ofFn x) (n - 1) = decide ((List.ofFn x).count true % 2 = 1) := by
      unfold P; rw [List.take_of_length_le (by simp; omega)]
    rw [← hP]
    by_cases h1 : n = 1
    · subst h1; rw [P0 _ (by simp)]; simp [f]
    · simp only [f, show ¬ 5 * n - 5 < n by omega, if_false, show (5 * n - 5 - n) % 4 = 3 by omega,
        show (5 * n - 5 - n) / 4 + 1 = n - 1 by omega]
      simp

