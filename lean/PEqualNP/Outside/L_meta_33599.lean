import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepReads
import PEqualNP.MetaComplexity.Helpers.OneNotRelabel

namespace PEqualNP.Outside.L_meta_33599_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.Represents PEqualNP.MetaComplexity.RepReads PEqualNP.MetaComplexity.OneNot

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i < n + m ∧ (i = u.val ∨ i = n + v.val)) := by
  rw [oneEach_eq, inp_getD]; simp

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

def guard (N k : ℕ) : List Gate :=
  (List.range k).map fun j => ⟨GateOp.or, [if j = 0 then 0 else N + j - 1, j + 1]⟩

theorem guard_succ (N k : ℕ) : guard N (k + 1) =
    guard N k ++ [⟨GateOp.or, [if k = 0 then 0 else N + k - 1, k + 1]⟩] := by
  simp [guard, List.range_succ]

theorem guard_length (N k : ℕ) : (guard N k).length = k := by simp [guard]

theorem guard_spec (N a : ℕ) (x : List Bool) (hx : x.length = N) :
    ∀ k, k + 1 < N → (∀ j ≤ k, x.getD j false = decide (j = a)) →
    ∀ i, (wiresFrom (guard N k) x).getD i false =
      if i < N then x.getD i false else if i < N + k then decide (a ≤ i - N + 1) else false := by
  intro k
  induction k with
  | zero =>
    intro _ _ i
    show x.getD i false = _
    split_ifs with h1 h2
    · rfl
    · omega
    · exact List.getD_eq_default _ _ (by omega)
  | succ k ih =>
    intro hk hj i
    have IH := ih (by omega) (fun j hj' => hj j (by omega))
    rw [guard_succ, wiresFrom_snoc, getD_snoc, length_wiresFrom, guard_length, hx]
    by_cases hi : i = N + k
    · rw [if_pos hi]
      subst hi
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      have e1 : (wiresFrom (guard N k) x).getD (k + 1) false = decide (k + 1 = a) := by
        rw [IH (k + 1), if_pos (by omega : k + 1 < N), hj (k + 1) le_rfl]
      rw [e1, if_neg (by omega : ¬ N + k < N), if_pos (by omega : N + k < N + (k + 1))]
      by_cases hk0 : k = 0
      · subst hk0
        have e0 : (wiresFrom (guard N 0) x).getD 0 false = decide (0 = a) := by
          rw [IH 0, if_pos (by omega : 0 < N), hj 0 (by omega)]
        simp only [↓reduceIte]
        rw [e0, Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff,
          decide_eq_true_iff]
        omega
      · have e0 : (wiresFrom (guard N k) x).getD (N + k - 1) false = decide (a ≤ k) := by
          rw [IH (N + k - 1), if_neg (by omega : ¬ N + k - 1 < N),
            if_pos (by omega : N + k - 1 < N + k), decide_eq_decide]
          omega
        simp only [hk0, ↓reduceIte]
        rw [e0, Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff,
          decide_eq_true_iff]
        omega
    · rw [if_neg hi, IH i]
      by_cases h1 : i < N
      · simp [h1]
      · simp only [h1, if_false]
        by_cases h2 : i < N + k
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]

def rmap (n m : ℕ) (i : ℕ) : ℕ := if i < n then i else if i < n + m then i + 1 else i + n

theorem part1 (n m s : ℕ) (A : Fin n → Fin m → Bool) (h : RepSizeAtMost A s) :
    RepSizeAtMost
      (fun (i : Fin (n+1)) j => if h : i.val < n then A ⟨i.val,h⟩ j else false) (s+n) := by
  obtain ⟨C, hC, hs, hR⟩ := h
  have hs' : C.gates.length ≤ s := hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨⟨[], 1 + m⟩, by intro g hg; simp at hg, by simp [Circuit.size], ?_⟩
    intro u v
    show (oneEach u v).getD (1 + m) false = _
    rw [oneEach_getD]; simp
  · refine ⟨⟨guard (n + 1 + m) (n - 1) ++ (C.gates.map (on1_relabel (rmap n m)) ++
        [⟨GateOp.and, [if n = 1 then 0 else n + 1 + m + n - 2, rmap n m C.output]⟩]),
        n + 1 + m + (n - 1) + C.gates.length⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_map, List.mem_singleton, guard] at hg
      rcases hg with ⟨j, _, rfl⟩ | ⟨g', hg', rfl⟩ | rfl
      · simp
      · have := hC g' hg'; simpa [on1_relabel] using this
      · simp
    · simp only [Circuit.size, List.length_append, guard_length, List.length_map,
        List.length_singleton]
      omega
    · intro u v
      have hu := u.2
      show (wiresFrom _ (oneEach u v)).getD _ false = _
      rw [wiresFrom_append, wiresFrom_snoc]
      set V1 := wiresFrom (guard (n + 1 + m) (n - 1)) (oneEach u v) with hV1
      have hV1l : V1.length = n + 1 + m + (n - 1) := by
        rw [hV1, length_wiresFrom, guard_length, oneEach_length]
      have hV1v := guard_spec (n + 1 + m) u.val (oneEach u v) (oneEach_length u v) (n - 1)
        (by omega) (fun j hj => by rw [oneEach_getD, decide_eq_decide]; omega)
      rw [← hV1] at hV1v
      set V2 := wiresFrom (C.gates.map (on1_relabel (rmap n m))) V1 with hV2
      have hV2l : V2.length = n + 1 + m + (n - 1) + C.gates.length := by
        rw [hV2, length_wiresFrom, hV1l, List.length_map]
      rw [getD_snoc, if_pos hV2l.symm]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
        Bool.and_true]
      have hG : V2.getD (if n = 1 then 0 else n + 1 + m + n - 2) false = decide (u.val < n) := by
        rw [hV2, getD_wiresFrom _ _ _ (by rw [hV1l]; split_ifs <;> omega), hV1v]
        by_cases h1 : n = 1
        · simp only [h1, ↓reduceIte]
          rw [if_pos (by omega : 0 < 1 + 1 + m), oneEach_getD, decide_eq_decide]; omega
        · simp only [h1, ↓reduceIte]
          rw [if_neg (by omega : ¬ n + 1 + m + n - 2 < n + 1 + m),
            if_pos (by omega : n + 1 + m + n - 2 < n + 1 + m + (n - 1)), decide_eq_decide]; omega
      rw [hG]
      by_cases hlt : u.val < n
      · simp only [hlt, decide_true, Bool.true_and, dite_true]
        rw [← hR ⟨u.val, hlt⟩ v]
        show _ = (wiresFrom C.gates (oneEach (⟨u.val, hlt⟩ : Fin n) v)).getD C.output false
        rw [hV2]
        apply on1_relabel_sim
        · intro i hi
          rw [oneEach_length] at hi
          rw [hV1v, oneEach_getD]
          unfold rmap
          split_ifs with h1 <;>
            first | (exfalso; omega) | (rw [oneEach_getD, decide_eq_decide]; simp only [Fin.val_mk]; omega)
        · intro i hi
          rw [oneEach_length] at hi
          left; rw [hV1l]; unfold rmap; split_ifs <;> omega
        · intro k _
          rw [oneEach_length, hV1l]; unfold rmap
          rw [if_neg (by omega), if_neg (by omega)]; omega
        · intro i hi
          rw [oneEach_length] at hi
          rw [hV1l]; unfold rmap
          rw [if_neg (by omega), if_neg (by omega)]; omega
      · simp [hlt]

end PEqualNP.Outside.L_meta_33599_aux

open PEqualNP.Outside.L_meta_33599_aux PEqualNP.Represents PEqualNP.MetaComplexity.RepReads in
theorem PEqualNP.Outside.L_meta_33599 : (∀ (n m s : Nat) (A : Fin n → Fin m → Bool),
  PEqualNP.Represents.RepSizeAtMost A s →
  PEqualNP.Represents.RepSizeAtMost
    (fun (i : Fin (n+1)) j => if h : i.val < n then A ⟨i.val,h⟩ j else false) (s+n)) ∧
(∀ n s : Nat,
  PEqualNP.Represents.RepSizeAtMost
    (fun (_ : Fin n) (j : Fin 2) => decide (j.val = 0)) 0 ∧
  (PEqualNP.Represents.RepSizeAtMost
    (fun (i : Fin (n+1)) (j : Fin 2) => decide (i.val < n ∧ j.val = 0)) s ↔ n ≤ s)) := by
  refine ⟨part1, fun n s => ?_⟩
  have h0 : RepSizeAtMost (fun (_ : Fin n) (j : Fin 2) => decide (j.val = 0)) 0 := by
    refine ⟨⟨[], n⟩, by intro g hg; simp at hg, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
    intro u v
    show (oneEach u v).getD n false = _
    have := u.2
    have := v.2
    rw [oneEach_getD, decide_eq_decide]; omega
  refine ⟨h0, ?_, ?_⟩
  · intro h
    have hr := reads_le _ h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · omega
    · have hL : (Finset.univ.map Fin.castSuccEmb : Finset (Fin (n+1))) ⊆ forcedL
          (fun (i : Fin (n+1)) (j : Fin 2) => decide (i.val < n ∧ j.val = 0)) := by
        intro i hi
        obtain ⟨i', _, rfl⟩ := Finset.mem_map.1 hi
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, 0, ?_, Fin.last n, ?_⟩ <;> simp
      have hRr : ({0} : Finset (Fin 2)) ⊆ forcedR
          (fun (i : Fin (n+1)) (j : Fin 2) => decide (i.val < n ∧ j.val = 0)) := by
        intro j hj
        rw [Finset.mem_singleton.1 hj]
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨0, by omega⟩, ?_, 1, ?_⟩ <;> simp [hn]
      have h1 := Finset.card_le_card hL
      have h2 := Finset.card_le_card hRr
      rw [Finset.card_map, Finset.card_univ, Fintype.card_fin] at h1
      rw [Finset.card_singleton] at h2
      omega
  · intro hns
    have h1 := part1 n 2 0 _ h0
    obtain ⟨C, hC, hsz, hR⟩ := h1
    refine ⟨C, hC, by omega, ?_⟩
    intro u v
    rw [hR u v]
    by_cases hlt : u.val < n <;> simp [hlt]
