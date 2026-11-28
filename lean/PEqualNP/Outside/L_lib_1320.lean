import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1320

open PEqualNP.CircuitLowerBounds

private theorem andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
private theorem orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
private theorem notEval_nil : GateOp.not.eval [] = true := rfl
private theorem notEval_cons (a : Bool) (as : List Bool) : GateOp.not.eval (a :: as) = !a := rfl

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

private theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (ht : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]

private theorem getD_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

private theorem run_prefix (gs1 gs2 : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs1.length) :
    (run (gs1 ++ gs2) x).getD w false = (run gs1 x).getD w false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, run_snoc, getD_lt]
    · exact ih
    · rw [run_length, List.length_append]; omega

private theorem run_input (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  simpa [run] using run_prefix [] gs x w (by simpa using hw)

private theorem run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < x.length + j then (run gs x).getD i false else false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1
  have hlen : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hp1 : (run gs x).getD (x.length + j) false =
      (run (gs.take j ++ [gs[j]]) x).getD (x.length + j) false := by
    conv_lhs => rw [hsplit]
    exact run_prefix (gs.take j ++ [gs[j]]) (gs.drop (j + 1)) x (x.length + j)
      (by rw [List.length_append, List.length_singleton, hlen]; omega)
  rw [hp1, run_snoc]
  have hrlen : (run (gs.take j) x).length = x.length + j := by rw [run_length, hlen]
  rw [← hrlen, getD_eq]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [hrlen]
  by_cases hi : i < x.length + j
  · rw [if_pos hi]
    have htake : (run gs x).getD i false = (run (gs.take j) x).getD i false := by
      conv_lhs => rw [hsplit, List.append_assoc]
      exact run_prefix (gs.take j) ([gs[j]] ++ gs.drop (j + 1)) x i (by rw [hlen]; exact hi)
    exact htake.symm
  · rw [if_neg hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

private theorem notCount_snoc (gs : List Gate) (g : Gate) (o : ℕ) :
    PEqualNP.NotBracket.notCount ⟨gs ++ [g], o⟩ =
    PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + (match g.op with | .not => 1 | _ => 0) := by
  dsimp only [PEqualNP.NotBracket.notCount]
  rw [List.filter_append, List.length_append]
  cases h : g.op <;> simp [h]

private theorem notCount_le_size (C : Circuit) : PEqualNP.NotBracket.notCount C ≤ C.size :=
  List.length_filter_le _ _

-- Helper: rise vs fall balance on any Bool sequence
private theorem rise_fall_balance (f : ℕ → Bool) (l : ℕ) :
    let R := ((Finset.range l).filter (fun t => f t = false ∧ f (t + 1) = true)).card
    let F := ((Finset.range l).filter (fun t => f t = true ∧ f (t + 1) = false)).card
    if f l = true then R ≤ F + 1 ∧ F ≤ R else R ≤ F ∧ F ≤ R + 1 := by
  induction l with
  | zero =>
    simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty]
    cases f 0 <;> simp
  | succ l ih =>
    dsimp only at ih ⊢
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    have hnr : l ∉ (Finset.range l).filter (fun t => f t = false ∧ f (t + 1) = true) := by simp
    have hnf : l ∉ (Finset.range l).filter (fun t => f t = true ∧ f (t + 1) = false) := by simp
    cases hfl : f l <;> cases hfl1 : f (l + 1) <;>
      simp only [hfl, hfl1, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
        Finset.card_insert_of_notMem hnr, Finset.card_insert_of_notMem hnf] at ih ⊢ <;> omega

private theorem rise_le_fall_add_one (f : ℕ → Bool) (l : ℕ) :
    ((Finset.range l).filter (fun t => f t = false ∧ f (t + 1) = true)).card ≤
    ((Finset.range l).filter (fun t => f t = true ∧ f (t + 1) = false)).card + 1 := by
  have h := rise_fall_balance f l
  dsimp only at h
  cases hfl : f l <;> simp only [hfl, ↓reduceIte, Bool.false_eq_true] at h <;> omega

-- Monotone input bit flips at most once
private theorem mono_chain (n l : ℕ) (x : ℕ → Fin n → Bool)
    (hx : ∀ t < l, ∀ j, x t j = true → x (t + 1) j = true)
    (t1 t2 : ℕ) (h12 : t1 ≤ t2) (h2l : t2 ≤ l) (j : Fin n) (ht1 : x t1 j = true) :
    x t2 j = true := by
  induction h12 with
  | refl => exact ht1
  | @step m h1m ih => exact hx m (by omega) j (ih (by omega))

private theorem mono_input_change_subsingleton (n l : ℕ) (x : ℕ → Fin n → Bool)
    (hx : ∀ t < l, ∀ j, x t j = true → x (t + 1) j = true) (j : Fin n) :
    ((Finset.range l).filter (fun t => x t j ≠ x (t + 1) j)).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro t1 ht1 t2 ht2
  obtain ⟨ht1l, hne1⟩ := Finset.mem_filter.mp ht1
  obtain ⟨ht2l, hne2⟩ := Finset.mem_filter.mp ht2
  rw [Finset.mem_range] at ht1l ht2l
  have hflip1 : x t1 j = false ∧ x (t1 + 1) j = true := by
    cases h1 : x t1 j <;> cases h2 : x (t1 + 1) j
    · exact absurd (h1.trans h2.symm) hne1
    · exact ⟨rfl, rfl⟩
    · have := hx t1 ht1l j h1; rw [h2] at this; cases this
    · exact absurd (h1.trans h2.symm) hne1
  have hflip2 : x t2 j = false ∧ x (t2 + 1) j = true := by
    cases h1 : x t2 j <;> cases h2 : x (t2 + 1) j
    · exact absurd (h1.trans h2.symm) hne2
    · exact ⟨rfl, rfl⟩
    · have := hx t2 ht2l j h1; rw [h2] at this; cases this
    · exact absurd (h1.trans h2.symm) hne2
  rcases lt_trichotomy t1 t2 with hlt | heq | hgt
  · have := mono_chain n l x hx (t1 + 1) t2 (by omega) (by omega) j hflip1.2
    rw [hflip2.1] at this; cases this
  · exact heq
  · have := mono_chain n l x hx (t2 + 1) t1 (by omega) (by omega) j hflip2.2
    rw [hflip1.1] at this; cases this

-- Part 1: inductive construction of tree circuit
private theorem part1_ind (n l : ℕ) (x : ℕ → Fin n → Bool)
    (hx : ∀ t < l, ∀ j, x t j = true → x (t + 1) j = true) :
    ∀ (k : ℕ) (y : ℕ → Bool),
      let changes := (Finset.range l).filter (fun t => y t ≠ y (t + 1))
      let S := ((Finset.range l).filter (fun t => y t = true ∧ y (t + 1) = false)).card
      changes.card = k → 0 < k →
      (∀ t ∈ changes, ∃ j : Fin n, x t j = false ∧ x (t + 1) j = true) →
      ∃ C : Circuit,
        PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
        C.output < n + C.size ∧
        (∀ t ≤ l, C.eval (List.ofFn (x t)) = y t) ∧
        C.size - PEqualNP.NotBracket.notCount C = k - 1 ∧
        PEqualNP.NotBracket.notCount C = S ∧
        (∀ i : ℕ, (C.gates.flatMap (fun g => g.inputs)).count i ≤ 1) ∧
        (C.gates.flatMap (fun g => g.inputs)).count C.output = 0 ∧
        (∀ j : Fin n, (j.val ∈ C.gates.flatMap (fun g => g.inputs) ∨ C.output = j.val) →
          ∃ t ∈ changes, x t j = false ∧ x (t + 1) j = true) := by
  intro k
  induction k with
  | zero => intro _ _ hk hpos; omega
  | succ k ih =>
    intro y changes S hk _ hchg
    have hne : changes.Nonempty := Finset.card_pos.mp (by omega)
    let tmax := changes.max' hne
    have htmax_mem : tmax ∈ changes := Finset.max'_mem changes hne
    have htmax_lt : tmax < l := Finset.mem_range.mp (Finset.mem_filter.mp htmax_mem).1
    have htmax_ne : y tmax ≠ y (tmax + 1) := (Finset.mem_filter.mp htmax_mem).2
    obtain ⟨jstar, hj0, hj1⟩ := hchg tmax htmax_mem
    have hj_before : ∀ t ≤ tmax, x t jstar = false := by
      intro t ht
      by_contra hne'
      have httrue : x t jstar = true := by cases h : x t jstar <;> simp_all
      have := mono_chain n l x hx t tmax ht (by omega) jstar httrue
      rw [hj0] at this; cases this
    have hj_after : ∀ t, tmax < t → t ≤ l → x t jstar = true := by
      intro t hgt hle
      exact mono_chain n l x hx (tmax + 1) t (by omega) hle jstar hj1
    have hy_after : ∀ t, tmax < t → t ≤ l → y t = y (tmax + 1) := by
      intro t hgt hle
      have hsub : ∀ d, tmax + 1 + d ≤ l → y (tmax + 1 + d) = y (tmax + 1) := by
        intro d
        induction d with
        | zero => intro _; rfl
        | succ d ihd =>
          intro hd
          have hnotmem : tmax + 1 + d ∉ changes := by
            intro hm
            have := Finset.le_max' changes _ hm
            dsimp only [tmax] at this; omega
          have heq : y (tmax + 1 + d) = y (tmax + 1 + d + 1) := by
            by_contra hne'
            exact hnotmem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hne'⟩)
          rw [show tmax + 1 + (d + 1) = tmax + 1 + d + 1 by omega, ← heq, ihd (by omega)]
      have := hsub (t - (tmax + 1)) (by omega)
      rwa [show tmax + 1 + (t - (tmax + 1)) = t by omega] at this
    by_cases hk0 : k = 0
    · subst hk0
      have hcard1 : changes.card = 1 := hk
      have hsing : changes = {tmax} := by
        have := Finset.card_eq_one.mp hcard1
        obtain ⟨a, ha⟩ := this
        have hmem := htmax_mem
        rw [ha, Finset.mem_singleton] at hmem
        rw [ha, hmem]
      have hy_before : ∀ t ≤ tmax, y t = y tmax := by
        intro t ht
        have hsub : ∀ d, t + d ≤ tmax → y t = y (t + d) := by
          intro d
          induction d with
          | zero => intro _; rfl
          | succ d ihd =>
            intro hd
            have hnotmem : t + d ∉ changes := by
              rw [hsing, Finset.mem_singleton]; omega
            have heq : y (t + d) = y (t + d + 1) := by
              by_contra hne'
              exact hnotmem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hne'⟩)
            rw [show t + (d + 1) = t + d + 1 by omega, ← heq]
            exact ihd (by omega)
        have := hsub (tmax - t) (by omega)
        rwa [show t + (tmax - t) = tmax by omega] at this
      cases hyt : y tmax
      · have hyt1 : y (tmax + 1) = true := by cases h : y (tmax + 1) <;> simp_all
        have hS0 : S = 0 := by
          dsimp only [S]
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro t ht ⟨ht1, ht2⟩
          have hm : t ∈ changes := Finset.mem_filter.mpr ⟨ht, by rw [ht1, ht2]; decide⟩
          rw [hsing, Finset.mem_singleton] at hm
          rw [hm, hyt] at ht1; cases ht1
        refine ⟨⟨[], jstar.val⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg; simp at hg
        · intro i hi; simp at hi
        · dsimp [Circuit.size]; omega
        · intro t ht
          change (List.ofFn (x t)).getD jstar.val false = y t
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [jstar.isLt, ↓reduceDIte, Option.getD_some, Fin.eta]
          by_cases hle : t ≤ tmax
          · rw [hj_before t hle, hy_before t hle, hyt]
          · rw [hj_after t (by omega) ht, hy_after t (by omega) ht, hyt1]
        · simp [Circuit.size, PEqualNP.NotBracket.notCount]
        · rw [hS0]; simp [PEqualNP.NotBracket.notCount]
        · intro i; simp
        · simp
        · intro j hj
          simp only [List.flatMap_nil, List.not_mem_nil, false_or] at hj
          have hjeq : j = jstar := Fin.ext hj.symm
          subst hjeq
          exact ⟨tmax, htmax_mem, hj0, hj1⟩
      · have hyt1 : y (tmax + 1) = false := by cases h : y (tmax + 1) <;> simp_all
        have hS1 : S = 1 := by
          dsimp only [S]
          have heq : (Finset.range l).filter (fun t => y t = true ∧ y (t + 1) = false) = {tmax} := by
            ext t
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
            constructor
            · rintro ⟨htl, ht1, ht2⟩
              have hm : t ∈ changes := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htl, by rw [ht1, ht2]; decide⟩
              rw [hsing, Finset.mem_singleton] at hm; exact hm
            · rintro rfl; exact ⟨htmax_lt, hyt, hyt1⟩
          rw [heq]; simp
        refine ⟨⟨[⟨.not, [jstar.val]⟩], n⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
        · intro i hi w hw
          simp only [List.length_singleton] at hi
          have hi0 : i = 0 := by omega
          subst hi0
          dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hw
          simp only [List.getD_cons_zero, List.mem_singleton] at hw
          subst hw; have := jstar.isLt; omega
        · dsimp [Circuit.size]; omega
        · intro t ht
          change (run [⟨.not, [jstar.val]⟩] (List.ofFn (x t))).getD n false = y t
          have hrg := run_gate [⟨.not, [jstar.val]⟩] (List.ofFn (x t)) 0 (by simp)
          simp only [List.length_ofFn, Nat.add_zero, List.getElem_cons_zero, List.map_cons, List.map_nil, notEval_cons] at hrg
          rw [hrg, if_pos (by omega), run_input _ _ jstar.val (by simp)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [jstar.isLt, ↓reduceDIte, Option.getD_some, Fin.eta]
          by_cases hle : t ≤ tmax
          · rw [hj_before t hle, hy_before t hle, hyt]; rfl
          · rw [hj_after t (by omega) ht, hy_after t (by omega) ht, hyt1]; rfl
        · simp [Circuit.size, PEqualNP.NotBracket.notCount]
        · rw [hS1]; simp [PEqualNP.NotBracket.notCount]
        · intro i; simp [List.count_cons]; split_ifs <;> omega
        · simp [List.count_cons]; omega
        · intro j hj
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton] at hj
          rcases hj with heq | heq
          · have hjeq : j = jstar := Fin.ext heq
            subst hjeq
            exact ⟨tmax, htmax_mem, hj0, hj1⟩
          · omega
    · -- Inductive step k ≥ 1 (so k + 1 ≥ 2)
      let y' : ℕ → Bool := fun t => if t ≤ tmax then y t else y tmax
      have hchg_eq : (Finset.range l).filter (fun t => y' t ≠ y' (t + 1)) = changes.erase tmax := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, changes]
        constructor
        · rintro ⟨htl, hne'⟩
          by_cases hlt : t < tmax
          · dsimp only [y'] at hne'
            rw [if_pos (by omega), if_pos (by omega)] at hne'
            exact ⟨by omega, htl, hne'⟩
          · exfalso; dsimp only [y'] at hne'
            by_cases heq : t = tmax
            · rw [if_pos (by omega), if_neg (by omega), heq] at hne'; exact hne' rfl
            · rw [if_neg (by omega), if_neg (by omega)] at hne'; exact hne' rfl
        · rintro ⟨hne_t, htl, hne'⟩
          have hlt : t < tmax := by
            have hle := Finset.le_max' changes t (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htl, hne'⟩)
            omega
          refine ⟨htl, ?_⟩
          dsimp only [y']
          rw [if_pos (by omega), if_pos (by omega)]
          exact hne'
      have hcard' : ((Finset.range l).filter (fun t => y' t ≠ y' (t + 1))).card = k := by
        rw [hchg_eq, Finset.card_erase_of_mem htmax_mem]; omega
      have hchg' : ∀ t ∈ (Finset.range l).filter (fun t => y' t ≠ y' (t + 1)),
          ∃ j : Fin n, x t j = false ∧ x (t + 1) j = true := by
        intro t ht
        rw [hchg_eq] at ht
        exact hchg t (Finset.mem_of_mem_erase ht)
      obtain ⟨C', hfan', hrb', hout', heval', hpos', hnot', hcnt', hout0', hsupp'⟩ :=
        ih y' hcard' (by omega) hchg'
      have hjstar_not_in : jstar.val ∉ C'.gates.flatMap (fun g => g.inputs) ∧ C'.output ≠ jstar.val := by
        have hnot_ex : ¬ ∃ t ∈ (Finset.range l).filter (fun t => y' t ≠ y' (t + 1)),
            x t jstar = false ∧ x (t + 1) jstar = true := by
          rintro ⟨t, ht, h0, h1⟩
          rw [hchg_eq] at ht
          have hne_t : t ≠ tmax := (Finset.mem_erase.mp ht).1
          have htl : t < l := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase ht)).1
          have hle1 := mono_input_change_subsingleton n l x hx jstar
          have hm1 : t ∈ (Finset.range l).filter (fun s => x s jstar ≠ x (s + 1) jstar) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htl, by rw [h0, h1]; decide⟩
          have hm2 : tmax ∈ (Finset.range l).filter (fun s => x s jstar ≠ x (s + 1) jstar) :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htmax_lt, by rw [hj0, hj1]; decide⟩
          exact hne_t (Finset.card_le_one.mp hle1 t hm1 tmax hm2)
        constructor
        · intro hm; exact hnot_ex (hsupp' jstar (Or.inl hm))
        · intro he; exact hnot_ex (hsupp' jstar (Or.inr he))
      have hjstar_cnt0 : (C'.gates.flatMap (fun g => g.inputs)).count jstar.val = 0 :=
        List.count_eq_zero.mpr hjstar_not_in.1
      have hS_rel :
          ((Finset.range l).filter (fun t => y t = true ∧ y (t + 1) = false)).card =
          ((Finset.range l).filter (fun t => y' t = true ∧ y' (t + 1) = false)).card +
            (if y tmax = true then 1 else 0) := by
        cases hyt : y tmax
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          congr 1; ext t
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨htl, ht1, ht2⟩
            have htm : t ∈ changes := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htl, by rw [ht1, ht2]; decide⟩
            have hle := Finset.le_max' changes t htm
            have hlt : t < tmax := by
              rcases Nat.lt_or_eq_of_le hle with h | h
              · exact h
              · rw [h, hyt] at ht1; cases ht1
            refine ⟨htl, ?_, ?_⟩ <;> dsimp only [y'] <;> rw [if_pos (by omega)] <;> assumption
          · rintro ⟨htl, ht1, ht2⟩
            have htm : t ∈ (Finset.range l).filter (fun s => y' s ≠ y' (s + 1)) :=
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htl, by rw [ht1, ht2]; decide⟩
            rw [hchg_eq] at htm
            have hne_t := (Finset.mem_erase.mp htm).1
            have hle := Finset.le_max' changes t (Finset.mem_of_mem_erase htm)
            have hlt : t < tmax := by omega
            dsimp only [y'] at ht1 ht2
            rw [if_pos (by omega)] at ht1 ht2
            exact ⟨htl, ht1, ht2⟩
        · have hyt1 : y (tmax + 1) = false := by cases h : y (tmax + 1) <;> simp_all
          simp only [↓reduceIte]
          have hset : (Finset.range l).filter (fun t => y t = true ∧ y (t + 1) = false) =
              insert tmax ((Finset.range l).filter (fun t => y' t = true ∧ y' (t + 1) = false)) := by
            ext t
            simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
            constructor
            · rintro ⟨htl, ht1, ht2⟩
              by_cases heq : t = tmax
              · exact Or.inl heq
              · right
                have htm : t ∈ changes := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htl, by rw [ht1, ht2]; decide⟩
                have hle := Finset.le_max' changes t htm
                have hlt : t < tmax := by omega
                refine ⟨htl, ?_, ?_⟩ <;> dsimp only [y'] <;> rw [if_pos (by omega)] <;> assumption
            · rintro (rfl | ⟨htl, ht1, ht2⟩)
              · exact ⟨htmax_lt, hyt, hyt1⟩
              · have htm : t ∈ (Finset.range l).filter (fun s => y' s ≠ y' (s + 1)) :=
                  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htl, by rw [ht1, ht2]; decide⟩
                rw [hchg_eq] at htm
                have hne_t := (Finset.mem_erase.mp htm).1
                have hle := Finset.le_max' changes t (Finset.mem_of_mem_erase htm)
                have hlt : t < tmax := by omega
                dsimp only [y'] at ht1 ht2
                rw [if_pos (by omega)] at ht1 ht2
                exact ⟨htl, ht1, ht2⟩
          have hnotmem : tmax ∉ (Finset.range l).filter (fun t => y' t = true ∧ y' (t + 1) = false) := by
            simp only [Finset.mem_filter, y', le_refl, ↓reduceIte, show ¬ (tmax + 1 ≤ tmax) by omega, hyt]
            intro h; exact absurd h.2.2 (by decide)
          rw [hset, Finset.card_insert_of_notMem hnotmem]
      cases hyt : y tmax
      · -- Rise 0 -> 1 at tmax: C = C' ++ [OR(C'.output, jstar.val)], output = n + C'.size
        have hyt1 : y (tmax + 1) = true := by cases h : y (tmax + 1) <;> simp_all
        let C : Circuit := ⟨C'.gates ++ [⟨.or, [C'.output, jstar.val]⟩], n + C'.size⟩
        have hnotC : PEqualNP.NotBracket.notCount C = PEqualNP.NotBracket.notCount C' := by
          dsimp only [C]; rw [notCount_snoc]; simp [PEqualNP.NotBracket.notCount]
        have hszC : C.size = C'.size + 1 := by simp [C, Circuit.size]
        have hnot_le' : PEqualNP.NotBracket.notCount C' ≤ C'.size := notCount_le_size C'
        refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.mp hg with h1 | h2
          · exact hfan' g h1
          · rw [List.mem_singleton.mp h2]; simp
        · intro i hi w hw
          dsimp only [C, PEqualNP.MetaComplexity.NestedCover.gateAt] at hi hw
          rw [List.length_append, List.length_singleton] at hi
          by_cases hlt : i < C'.gates.length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hw
            exact hrb' i hlt w hw
          · have hieq : i = C'.gates.length := by omega
            subst hieq
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl] at hw
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw with rfl | rfl
            · exact hout'
            · have := jstar.isLt; omega
        · simp [C, Circuit.size]
        · intro t ht
          change (run (C'.gates ++ [⟨.or, [C'.output, jstar.val]⟩]) (List.ofFn (x t))).getD (n + C'.size) false = y t
          rw [run_snoc]
          have hrlen : (run C'.gates (List.ofFn (x t))).length = n + C'.size := by rw [run_length, List.length_ofFn]; rfl
          rw [← hrlen, getD_eq, orEval]
          simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          have he1 : (run C'.gates (List.ofFn (x t))).getD C'.output false = y' t := heval' t ht
          have he2 : (run C'.gates (List.ofFn (x t))).getD jstar.val false = x t jstar := by
            rw [run_input C'.gates _ jstar.val (by simp), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            simp [jstar.isLt]
          rw [he1, he2]
          by_cases hle : t ≤ tmax
          · dsimp only [y']; rw [if_pos hle, hj_before t hle, Bool.or_false]
          · rw [hj_after t (by omega) ht, Bool.or_true, hy_after t (by omega) ht, hyt1]
        · rw [hszC, hnotC]; omega
        · rw [hnotC, hnot']; dsimp only [S]; rw [hS_rel, hyt]; simp
        · intro i
          dsimp only [C]
          rw [List.flatMap_append, List.count_append]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_cons, List.count_nil]
          have h1 := hcnt' i
          by_cases hi1 : i = C'.output
          · subst hi1; have hne := hjstar_not_in.2; simp [hout0', beq_iff_eq, hne]; omega
          · by_cases hi2 : i = jstar.val
            · subst hi2; simp [hjstar_cnt0, beq_iff_eq, hi1]; omega
            · simp [beq_iff_eq, Ne.symm hi1, Ne.symm hi2]; exact h1
        · dsimp only [C]
          rw [List.flatMap_append, List.count_append]
          have hno : n + C'.size ∉ C'.gates.flatMap (fun g => g.inputs) := by
            intro hm
            obtain ⟨g, hg, hgi⟩ := List.mem_flatMap.mp hm
            obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hg
            have hlt := hrb' idx hidx (n + C'.size) (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem _ _ hidx]; exact hgi)
            dsimp [Circuit.size] at hlt; omega
          rw [List.count_eq_zero.mpr hno]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_cons, List.count_nil, Nat.zero_add]
          have h1 : C'.output ≠ n + C'.size := by omega
          have h2 : jstar.val ≠ n + C'.size := by omega
          simp [beq_iff_eq, h1, h2]
        · intro j hj
          dsimp only [C] at hj
          rw [List.flatMap_append, List.mem_append] at hj
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with (h1 | (h2 | h3)) | h4
          · obtain ⟨t, ht, h0, h1'⟩ := hsupp' j (Or.inl h1)
            rw [hchg_eq] at ht; exact ⟨t, Finset.mem_of_mem_erase ht, h0, h1'⟩
          · obtain ⟨t, ht, h0, h1'⟩ := hsupp' j (Or.inr h2.symm)
            rw [hchg_eq] at ht; exact ⟨t, Finset.mem_of_mem_erase ht, h0, h1'⟩
          · have hjeq : j = jstar := Fin.ext h3; subst hjeq; exact ⟨tmax, htmax_mem, hj0, hj1⟩
          · omega
      · -- Fall 1 -> 0 at tmax: C = C' ++ [NOT(jstar.val), AND(C'.output, n + C'.size)], output = n + C'.size + 1
        have hyt1 : y (tmax + 1) = false := by cases h : y (tmax + 1) <;> simp_all
        let gs1 : List Gate := C'.gates ++ [⟨.not, [jstar.val]⟩]
        let C : Circuit := ⟨gs1 ++ [⟨.and, [C'.output, n + C'.size]⟩], n + C'.size + 1⟩
        have hnot1 : PEqualNP.NotBracket.notCount ⟨gs1, 0⟩ = PEqualNP.NotBracket.notCount C' + 1 := by
          dsimp only [gs1]; rw [notCount_snoc]; simp [PEqualNP.NotBracket.notCount]
        have hnotC : PEqualNP.NotBracket.notCount C = PEqualNP.NotBracket.notCount C' + 1 := by
          dsimp only [C]; rw [notCount_snoc]; simp [hnot1]
        have hszC : C.size = C'.size + 2 := by simp [C, gs1, Circuit.size]
        have hnot_le' : PEqualNP.NotBracket.notCount C' ≤ C'.size := notCount_le_size C'
        refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.mp hg with h1 | h2
          · rcases List.mem_append.mp h1 with h1a | h1b
            · exact hfan' g h1a
            · rw [List.mem_singleton.mp h1b]; simp
          · rw [List.mem_singleton.mp h2]; simp
        · intro i hi w hw
          dsimp only [C, gs1, PEqualNP.MetaComplexity.NestedCover.gateAt] at hi hw
          rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton] at hi
          by_cases hlt1 : i < C'.gates.length
          · rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1, ← List.getD_eq_getElem?_getD] at hw
            exact hrb' i hlt1 w hw
          · by_cases hlt2 : i = C'.gates.length
            · subst hlt2
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp), List.getElem?_append_right le_rfl] at hw
              simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_singleton] at hw
              subst hw; have := jstar.isLt; omega
            · have hieq : i = C'.gates.length + 1 := by omega
              subst hieq
              have hlen1 : (C'.gates ++ [({ op := .not, inputs := [jstar.val] } : Gate)]).length = C'.gates.length + 1 := by simp
              rw [← hlen1, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl] at hw
              simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hw
              rcases hw with rfl | rfl
              · exact Nat.lt_succ_of_lt hout'
              · dsimp [Circuit.size]; omega
        · simp [C, gs1, Circuit.size]; omega
        · intro t ht
          change (run (gs1 ++ [⟨.and, [C'.output, n + C'.size]⟩]) (List.ofFn (x t))).getD (n + C'.size + 1) false = y t
          rw [run_snoc]
          have hrlen1 : (run gs1 (List.ofFn (x t))).length = n + C'.size + 1 := by
            dsimp only [gs1]; rw [run_length, List.length_ofFn, List.length_append, List.length_singleton]; dsimp [Circuit.size]; omega
          rw [← hrlen1, getD_eq, andEval]
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          have he1 : (run gs1 (List.ofFn (x t))).getD C'.output false = y' t := by
            dsimp only [gs1]; rw [run_prefix C'.gates _ _ C'.output (by simp; exact hout')]; exact heval' t ht
          have he2 : (run gs1 (List.ofFn (x t))).getD (n + C'.size) false = !(x t jstar) := by
            dsimp only [gs1]; rw [run_snoc]
            have hrlen0 : (run C'.gates (List.ofFn (x t))).length = n + C'.size := by rw [run_length, List.length_ofFn]; rfl
            rw [← hrlen0, getD_eq, List.map_cons, List.map_nil, notEval_cons]
            rw [run_input C'.gates _ jstar.val (by simp), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            simp [jstar.isLt]
          rw [he1, he2]
          by_cases hle : t ≤ tmax
          · dsimp only [y']; rw [if_pos hle, hj_before t hle]; simp
          · rw [hj_after t (by omega) ht, hy_after t (by omega) ht, hyt1]; simp
        · rw [hszC, hnotC]; omega
        · rw [hnotC, hnot']; dsimp only [S]; rw [hS_rel, hyt]; simp
        · intro i
          dsimp only [C, gs1]
          rw [List.flatMap_append, List.flatMap_append, List.count_append, List.count_append]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_cons, List.count_nil]
          have h1 := hcnt' i
          have hno : n + C'.size ∉ C'.gates.flatMap (fun g => g.inputs) := by
            intro hm
            obtain ⟨g, hg, hgi⟩ := List.mem_flatMap.mp hm
            obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hg
            have hlt := hrb' idx hidx (n + C'.size) (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem _ _ hidx]; exact hgi)
            dsimp [Circuit.size] at hlt; omega
          by_cases hi1 : i = C'.output
          · subst hi1
            have hne1 : jstar.val ≠ C'.output := hjstar_not_in.2.symm
            have hne2 : n + C'.size ≠ C'.output := by omega
            simp [hout0', beq_iff_eq, hne1, hne2]
          · by_cases hi2 : i = jstar.val
            · subst hi2
              have hne2 : n + C'.size ≠ jstar.val := by have := jstar.isLt; omega
              simp [hjstar_cnt0, beq_iff_eq, Ne.symm hi1, hne2]
            · by_cases hi3 : i = n + C'.size
              · subst hi3
                rw [List.count_eq_zero.mpr hno]
                simp [beq_iff_eq, Ne.symm hi1, Ne.symm hi2]
              · simp [beq_iff_eq, Ne.symm hi1, Ne.symm hi2, Ne.symm hi3]; exact h1
        · dsimp only [C, gs1]
          rw [List.flatMap_append, List.flatMap_append, List.count_append, List.count_append]
          have hno : n + C'.size + 1 ∉ C'.gates.flatMap (fun g => g.inputs) := by
            intro hm
            obtain ⟨g, hg, hgi⟩ := List.mem_flatMap.mp hm
            obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hg
            have hlt := hrb' idx hidx (n + C'.size + 1) (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem _ _ hidx]; exact hgi)
            dsimp [Circuit.size] at hlt; omega
          rw [List.count_eq_zero.mpr hno]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_cons, List.count_nil, Nat.zero_add]
          have h1 : C'.output ≠ n + C'.size + 1 := by omega
          have h2 : jstar.val ≠ n + C'.size + 1 := by omega
          have h3 : n + C'.size ≠ n + C'.size + 1 := by omega
          simp [beq_iff_eq, h1, h2, h3]
        · intro j hj
          dsimp only [C, gs1] at hj
          rw [List.flatMap_append, List.flatMap_append, List.mem_append, List.mem_append] at hj
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with ((h1 | h2) | (h3 | h4)) | h5
          · obtain ⟨t, ht, h0, h1'⟩ := hsupp' j (Or.inl h1)
            rw [hchg_eq] at ht; exact ⟨t, Finset.mem_of_mem_erase ht, h0, h1'⟩
          · have hjeq : j = jstar := Fin.ext h2; subst hjeq; exact ⟨tmax, htmax_mem, hj0, hj1⟩
          · obtain ⟨t, ht, h0, h1'⟩ := hsupp' j (Or.inr h3.symm)
            rw [hchg_eq] at ht; exact ⟨t, Finset.mem_of_mem_erase ht, h0, h1'⟩
          · omega
          · omega

-- Part 2: DAG reachability & lower bounds
private def wireChildren (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  if n ≤ w ∧ w < n + C.size then
    let g := C.gates.getD (w - n) ⟨.or, []⟩
    match g.op with
    | .not => match g.inputs with | a :: _ => {a} | [] => ∅
    | .and => g.inputs.toFinset
    | .or => g.inputs.toFinset
    | _ => ∅
  else ∅

private theorem wireChildren_lt (n : ℕ) (C : Circuit)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (w u : ℕ)
    (hu : u ∈ wireChildren n C w) : u < w := by
  dsimp only [wireChildren] at hu
  split_ifs at hu with h
  · have hidx : w - n < C.gates.length := by dsimp [Circuit.size] at h; omega
    have hmem : u ∈ (C.gates.getD (w - n) ⟨.or, []⟩).inputs := by
      cases hop : (C.gates.getD (w - n) ⟨.or, []⟩).op <;> rw [hop] at hu
      · exact List.mem_toFinset.mp hu
      · exact List.mem_toFinset.mp hu
      · cases hin : (C.gates.getD (w - n) ⟨.or, []⟩).inputs <;> rw [hin] at hu
        · simp at hu
        · rw [Finset.mem_singleton.mp hu]; exact List.mem_cons_self
      · simp at hu
      · simp at hu
    have := hrb (w - n) hidx u (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; exact hmem)
    omega
  · simp at hu

private def nodeSet (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  insert w (((wireChildren n C w).filter (· < w)).biUnion fun u =>
    if h : u < w then nodeSet n C u else ∅)
termination_by w

private theorem nodeSet_eq (n : ℕ) (C : Circuit)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (w : ℕ) :
    nodeSet n C w = insert w ((wireChildren n C w).biUnion (nodeSet n C)) := by
  rw [nodeSet]
  congr 1
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, hlt⟩, hv⟩
    rw [dif_pos hlt] at hv
    exact ⟨u, hu, hv⟩
  · rintro ⟨u, hu, hv⟩
    have hlt := wireChildren_lt n C hrb w u hu
    exact ⟨u, ⟨hu, hlt⟩, by rwa [dif_pos hlt]⟩

private theorem mem_nodeSet_self (n : ℕ) (C : Circuit)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (w : ℕ) : w ∈ nodeSet n C w := by
  rw [nodeSet_eq n C hrb]; exact Finset.mem_insert_self _ _

private theorem mem_nodeSet_le (n : ℕ) (C : Circuit)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) :
    ∀ w v, v ∈ nodeSet n C w → v ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    rw [nodeSet_eq n C hrb] at hv
    rcases Finset.mem_insert.mp hv with rfl | h2
    · exact le_rfl
    · obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp h2
      have hlt := wireChildren_lt n C hrb w u hu
      exact le_trans (ih u hlt v hvu) (Nat.le_of_lt hlt)

private theorem nodeSet_subset_of_mem (n : ℕ) (C : Circuit)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) :
    ∀ w v, v ∈ nodeSet n C w → nodeSet n C v ⊆ nodeSet n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    rw [nodeSet_eq n C hrb w] at hv
    rcases Finset.mem_insert.mp hv with rfl | h2
    · exact Finset.Subset.refl _
    · obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp h2
      have hlt := wireChildren_lt n C hrb w u hu
      have hsub := ih u hlt v hvu
      intro z hz
      rw [nodeSet_eq n C hrb w]
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, hsub hz⟩)

private theorem nodeSet_erase_sub_biUnion (n : ℕ) (C : Circuit)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) :
    ∀ w, (nodeSet n C w).erase w ⊆ (nodeSet n C w).biUnion (wireChildren n C) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    obtain ⟨hne, hvw⟩ := Finset.mem_erase.mp hv
    rw [nodeSet_eq n C hrb w] at hvw
    rcases Finset.mem_insert.mp hvw with rfl | h2
    · exact absurd rfl hne
    · obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp h2
      have hlt := wireChildren_lt n C hrb w u hu
      by_cases hveq : v = u
      · subst hveq
        exact Finset.mem_biUnion.mpr ⟨w, mem_nodeSet_self n C hrb w, hu⟩
      · have hmem := ih u hlt (Finset.mem_erase.mpr ⟨hveq, hvu⟩)
        obtain ⟨p, hp, hvp⟩ := Finset.mem_biUnion.mp hmem
        have hpw : p ∈ nodeSet n C w := by
          rw [nodeSet_eq n C hrb w]
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, hp⟩)
        exact Finset.mem_biUnion.mpr ⟨p, hpw, hvp⟩

set_option maxHeartbeats 800000 in
private theorem part2_clean (n l : ℕ) (x : ℕ → Fin n → Bool) (y : ℕ → Bool)
    (hx : ∀ t < l, ∀ j, x t j = true → x (t + 1) j = true)
    (C : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hout : C.output < n + C.size)
    (heval : ∀ t ≤ l, C.eval (List.ofFn (x t)) = y t) :
    let changes := (Finset.range l).filter (fun t => y t ≠ y (t + 1))
    let k := changes.card
    let S := ((Finset.range l).filter (fun t => y t = true ∧ y (t + 1) = false)).card
    let positive := C.size - PEqualNP.NotBracket.notCount C
    k - 1 ≤ positive ∧ (positive = k - 1 → S ≤ PEqualNP.NotBracket.notCount C) := by
  let _ : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  dsimp only
  let wire : ℕ → ℕ → Bool := fun t w => (run C.gates (List.ofFn (x t))).getD w false
  let chg : ℕ → Finset ℕ := fun w => (Finset.range l).filter (fun t => wire t w ≠ wire (t + 1) w)
  let fall : ℕ → Finset ℕ := fun w => (Finset.range l).filter (fun t => wire t w = true ∧ wire (t + 1) w = false)
  let inSet : ℕ → Finset ℕ := fun w => (nodeSet n C w).filter (· < n)
  let posSet : ℕ → Finset ℕ := fun w => (nodeSet n C w).filter (fun u => n ≤ u ∧ (C.gates.getD (u - n) ⟨.or, []⟩).op ≠ .not)
  let notSet : ℕ → Finset ℕ := fun w => (nodeSet n C w).filter (fun u => n ≤ u ∧ (C.gates.getD (u - n) ⟨.or, []⟩).op = .not)
  have hchg_out : chg C.output = (Finset.range l).filter (fun t => y t ≠ y (t + 1)) := by
    ext t; simp only [chg, wire, Finset.mem_filter, Finset.mem_range]
    constructor <;> rintro ⟨ht, h⟩ <;> refine ⟨ht, ?_⟩
    · change C.eval (List.ofFn (x t)) ≠ C.eval (List.ofFn (x (t + 1))) at h
      rwa [heval t (by omega), heval (t + 1) (by omega)] at h
    · change C.eval (List.ofFn (x t)) ≠ C.eval (List.ofFn (x (t + 1)))
      rwa [heval t (by omega), heval (t + 1) (by omega)]
  have hfall_out : fall C.output = (Finset.range l).filter (fun t => y t = true ∧ y (t + 1) = false) := by
    ext t; simp only [fall, wire, Finset.mem_filter, Finset.mem_range]
    constructor <;> rintro ⟨ht, h1, h2⟩ <;> refine ⟨ht, ?_, ?_⟩
    · change C.eval (List.ofFn (x t)) = true at h1; rwa [heval t (by omega)] at h1
    · change C.eval (List.ofFn (x (t + 1))) = false at h2; rwa [heval (t + 1) (by omega)] at h2
    · change C.eval (List.ofFn (x t)) = true; rwa [heval t (by omega)]
    · change C.eval (List.ofFn (x (t + 1))) = false; rwa [heval (t + 1) (by omega)]
  have hwire_step : ∀ w < n + C.size, chg w ⊆ (wireChildren n C w).biUnion chg ∨ w < n := by
    intro w hw
    by_cases hwn : w < n
    · exact Or.inr hwn
    · left
      intro t ht
      obtain ⟨htl, hne⟩ := Finset.mem_filter.mp ht
      rw [Finset.mem_range] at htl
      have hg_idx : w - n < C.gates.length := by dsimp [Circuit.size] at hw; omega
      have hw_eq : w = n + (w - n) := by omega
      have hrg1 := run_gate C.gates (List.ofFn (x t)) (w - n) hg_idx
      have hrg2 := run_gate C.gates (List.ofFn (x (t + 1))) (w - n) hg_idx
      rw [List.length_ofFn, ← hw_eq] at hrg1 hrg2
      change (run C.gates (List.ofFn (x t))).getD w false ≠ (run C.gates (List.ofFn (x (t + 1)))).getD w false at hne
      rw [hrg1, hrg2] at hne
      have hg_eq : C.gates[w - n] = C.gates.getD (w - n) ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hg_idx).symm
      by_contra hnotmem
      apply hne
      have hsame : ∀ u ∈ wireChildren n C w, wire t u = wire (t + 1) u := by
        intro u hu
        by_contra hune
        exact hnotmem (Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htl, hune⟩⟩)
      rcases (hfan _ (List.getElem_mem hg_idx)).1 with hand | hor | hnot'
      · congr 1
        apply List.map_congr_left
        intro u hu
        have hu_ch : u ∈ wireChildren n C w := by
          dsimp only [wireChildren]; rw [if_pos ⟨by omega, hw⟩, ← hg_eq, hand]; exact List.mem_toFinset.mpr hu
        have hult := wireChildren_lt n C hrb w u hu_ch
        rw [if_pos hult, if_pos hult]; exact hsame u hu_ch
      · congr 1
        apply List.map_congr_left
        intro u hu
        have hu_ch : u ∈ wireChildren n C w := by
          dsimp only [wireChildren]; rw [if_pos ⟨by omega, hw⟩, ← hg_eq, hor]; exact List.mem_toFinset.mpr hu
        have hult := wireChildren_lt n C hrb w u hu_ch
        rw [if_pos hult, if_pos hult]; exact hsame u hu_ch
      · rw [hnot']
        rcases hin : (C.gates[w - n]).inputs with _ | ⟨a, rest⟩
        · simp
        · simp only [List.map_cons, notEval_cons]
          have ha_ch : a ∈ wireChildren n C w := by
            dsimp only [wireChildren]; rw [if_pos ⟨by omega, hw⟩, ← hg_eq, hnot', hin]; exact Finset.mem_singleton_self a
          have halt := wireChildren_lt n C hrb w a ha_ch
          rw [if_pos halt, if_pos halt]
          exact congrArg Bool.not (hsame a ha_ch)
  have hchg_sub_in : ∀ w < n + C.size, chg w ⊆ (inSet w).biUnion chg := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      rcases hwire_step w hw with hsub | hwn
      · intro t ht
        obtain ⟨u, hu, htu⟩ := Finset.mem_biUnion.mp (hsub ht)
        have hult := wireChildren_lt n C hrb w u hu
        obtain ⟨j, hj, htj⟩ := Finset.mem_biUnion.mp (ih u hult (by omega) htu)
        have hju : j ∈ nodeSet n C u := (Finset.mem_filter.mp hj).1
        have hjn : j < n := (Finset.mem_filter.mp hj).2
        have hjw : j ∈ nodeSet n C w := by
          rw [nodeSet_eq n C hrb w]
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, hju⟩)
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjw, hjn⟩, htj⟩
      · intro t ht
        exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨mem_nodeSet_self n C hrb w, hwn⟩, ht⟩
  have hchg_in_le1 : ∀ j < n, (chg j).card ≤ 1 := by
    intro j hjn
    have heq : chg j = (Finset.range l).filter (fun t => x t ⟨j, hjn⟩ ≠ x (t + 1) ⟨j, hjn⟩) := by
      ext t; simp only [chg, wire, Finset.mem_filter, Finset.mem_range]
      constructor <;> rintro ⟨ht, hne⟩ <;> refine ⟨ht, ?_⟩
      · rwa [run_input C.gates _ j (by simp [hjn]), run_input C.gates _ j (by simp [hjn]),
          List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getElem?_ofFn,
          dif_pos hjn, dif_pos hjn] at hne
      · rw [run_input C.gates _ j (by simp [hjn]), run_input C.gates _ j (by simp [hjn]),
          List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getElem?_ofFn,
          dif_pos hjn, dif_pos hjn]
        exact hne
    rw [heq]; exact mono_input_change_subsingleton n l x hx ⟨j, hjn⟩
  have hnode_part : ∀ w, (nodeSet n C w).card = (inSet w).card + (posSet w).card + (notSet w).card := by
    intro w
    have hdisj1 : Disjoint (inSet w) (posSet w) := Finset.disjoint_left.mpr fun u h1 h2 => by
      have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2.1; omega
    have hdisj2 : Disjoint (inSet w ∪ posSet w) (notSet w) := Finset.disjoint_left.mpr fun u h1 h2 => by
      have h2' := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with ha | hb
      · have := (Finset.mem_filter.mp ha).2; omega
      · exact (Finset.mem_filter.mp hb).2.2 h2'.2
    have hunion : inSet w ∪ posSet w ∪ notSet w = nodeSet n C w := by
      ext u; simp only [inSet, posSet, notSet, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hu : u < n
        · exact Or.inl (Or.inl ⟨h, hu⟩)
        · by_cases hop : (C.gates.getD (u - n) ⟨.or, []⟩).op = .not
          · exact Or.inr ⟨h, by omega, hop⟩
          · exact Or.inl (Or.inr ⟨h, by omega, hop⟩)
    rw [← hunion, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1]
  have hdeg_sum : ∀ w < n + C.size,
      ∑ u ∈ nodeSet n C w, (wireChildren n C u).card ≤ 2 * (posSet w).card + (notSet w).card := by
    intro w hw
    have hunion : inSet w ∪ posSet w ∪ notSet w = nodeSet n C w := by
      ext u; simp only [inSet, posSet, notSet, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hu : u < n
        · exact Or.inl (Or.inl ⟨h, hu⟩)
        · by_cases hop : (C.gates.getD (u - n) ⟨.or, []⟩).op = .not
          · exact Or.inr ⟨h, by omega, hop⟩
          · exact Or.inl (Or.inr ⟨h, by omega, hop⟩)
    have hdisj1 : Disjoint (inSet w) (posSet w) := Finset.disjoint_left.mpr fun u h1 h2 => by
      have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2.1; omega
    have hdisj2 : Disjoint (inSet w ∪ posSet w) (notSet w) := Finset.disjoint_left.mpr fun u h1 h2 => by
      have h2' := (Finset.mem_filter.mp h2).2
      rcases Finset.mem_union.mp h1 with ha | hb
      · have := (Finset.mem_filter.mp ha).2; omega
      · exact (Finset.mem_filter.mp hb).2.2 h2'.2
    rw [← hunion, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
    have h0 : ∑ u ∈ inSet w, (wireChildren n C u).card = 0 := by
      apply Finset.sum_eq_zero; intro u hu
      have hun := (Finset.mem_filter.mp hu).2
      dsimp only [wireChildren]; rw [if_neg (by omega)]; simp
    have hpos_le : ∑ u ∈ posSet w, (wireChildren n C u).card ≤ 2 * (posSet w).card := by
      calc ∑ u ∈ posSet w, (wireChildren n C u).card
          ≤ ∑ _u ∈ posSet w, 2 := by
            apply Finset.sum_le_sum; intro u hu
            obtain ⟨huw, hun, _⟩ := Finset.mem_filter.mp hu
            have hule : u ≤ w := mem_nodeSet_le n C hrb w u huw
            have hidx : u - n < C.gates.length := by dsimp [Circuit.size] at hw; omega
            have hlen : (C.gates.getD (u - n) ⟨.or, []⟩).inputs.length ≤ 2 := by
              rw [List.getD_eq_getElem C.gates _ hidx]; exact (hfan _ (List.getElem_mem hidx)).2
            dsimp only [wireChildren]; rw [if_pos ⟨hun, by omega⟩]
            cases (C.gates.getD (u - n) ⟨.or, []⟩).op <;> simp only [Finset.card_empty]
            · exact le_trans (List.toFinset_card_le _) hlen
            · exact le_trans (List.toFinset_card_le _) hlen
            · cases (C.gates.getD (u - n) ⟨.or, []⟩).inputs <;> simp
            · omega
            · omega
        _ = 2 * (posSet w).card := by simp [Nat.mul_comm]
    have hnot_le : ∑ u ∈ notSet w, (wireChildren n C u).card ≤ (notSet w).card := by
      calc ∑ u ∈ notSet w, (wireChildren n C u).card
          ≤ ∑ _u ∈ notSet w, 1 := by
            apply Finset.sum_le_sum; intro u hu
            obtain ⟨huw, hun, hop⟩ := Finset.mem_filter.mp hu
            have hule : u ≤ w := mem_nodeSet_le n C hrb w u huw
            dsimp only [wireChildren]; rw [if_pos ⟨hun, by omega⟩, hop]
            cases (C.gates.getD (u - n) ⟨.or, []⟩).inputs <;> simp
        _ = (notSet w).card := by simp
    omega
  have hposSet_le_pos : ∀ w < n + C.size, (posSet w).card ≤ C.size - PEqualNP.NotBracket.notCount C := by
    intro w hw
    have hnot_eq : ((Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op ≠ .not)).card =
        C.size - PEqualNP.NotBracket.notCount C := by
      have htot : ((Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op = .not)).card +
                  ((Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op ≠ .not)).card = C.size := by
        have hdisj : Disjoint ((Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op = .not))
            ((Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op ≠ .not)) :=
          Finset.disjoint_left.mpr fun i h1 h2 => (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
        have hunion : (Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op = .not) ∪
            (Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op ≠ .not) = Finset.range C.size := by
          ext i; simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h; by_cases hp : (C.gates.getD i ⟨.or, []⟩).op = .not
            · exact Or.inl ⟨h, hp⟩
            · exact Or.inr ⟨h, hp⟩
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
      have hnc : ((Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op = .not)).card =
          PEqualNP.NotBracket.notCount C := by
        have hnd : ((List.range C.size).filter (fun i => decide ((C.gates.getD i ⟨.or, []⟩).op = .not))).Nodup :=
          List.Nodup.filter _ List.nodup_range
        have h1 : ((Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op = .not)).card =
            ((List.range C.size).filter (fun i => decide ((C.gates.getD i ⟨.or, []⟩).op = .not))).length := by
          rw [← List.toFinset_card_of_nodup hnd]; congr 1; ext i; simp
        rw [h1]
        dsimp only [PEqualNP.NotBracket.notCount, Circuit.size]
        -- filter_range_length_eq inline
        have hlen : ∀ (L : List Gate), ((List.range L.length).filter (fun i => decide ((L.getD i ⟨.or, []⟩).op = .not))).length =
            (L.filter (fun g => decide (g.op = .not))).length := by
          intro L; induction L using List.reverseRecOn with
          | nil => simp
          | append_singleton xs g ihL =>
            rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append, List.filter_append,
              List.length_append, List.length_append]
            have ha : (List.range xs.length).filter (fun i => decide (((xs ++ [g]).getD i ⟨.or, []⟩).op = .not)) =
                (List.range xs.length).filter (fun i => decide ((xs.getD i ⟨.or, []⟩).op = .not)) := by
              apply List.filter_congr; intro i hi
              have hilt := List.mem_range.mp hi
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt, ← List.getD_eq_getElem?_getD]
            have hb : ([xs.length].filter (fun i => decide (((xs ++ [g]).getD i ⟨.or, []⟩).op = .not))).length =
                ([g].filter (fun g' => decide (g'.op = .not))).length := by
              have hgd : (xs ++ [g]).getD xs.length ⟨.or, []⟩ = g := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
              cases h : g.op <;> simp [hgd, h]
            rw [ha, ihL, hb]
        exact hlen C.gates
      omega
    rw [← hnot_eq]
    refine Finset.card_le_card_of_injOn (fun u => u - n) ?_ ?_
    · intro u hu
      dsimp only
      obtain ⟨huw, hun, hop⟩ := Finset.mem_filter.mp hu
      have hule := mem_nodeSet_le n C hrb w u huw
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hop⟩
    · intro u1 hu1 u2 hu2 heq
      dsimp only at heq
      have h1 := (Finset.mem_filter.mp hu1).2.1
      have h2 := (Finset.mem_filter.mp hu2).2.1
      omega
  have hnotSet_le_not : ∀ w < n + C.size, (notSet w).card ≤ PEqualNP.NotBracket.notCount C := by
    intro w hw
    have hnc : ((Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op = .not)).card =
        PEqualNP.NotBracket.notCount C := by
      have hnd : ((List.range C.size).filter (fun i => decide ((C.gates.getD i ⟨.or, []⟩).op = .not))).Nodup :=
        List.Nodup.filter _ List.nodup_range
      have h1 : ((Finset.range C.size).filter (fun i => (C.gates.getD i ⟨.or, []⟩).op = .not)).card =
          ((List.range C.size).filter (fun i => decide ((C.gates.getD i ⟨.or, []⟩).op = .not))).length := by
        rw [← List.toFinset_card_of_nodup hnd]; congr 1; ext i; simp
      rw [h1]
      dsimp only [PEqualNP.NotBracket.notCount, Circuit.size]
      have hlen : ∀ (L : List Gate), ((List.range L.length).filter (fun i => decide ((L.getD i ⟨.or, []⟩).op = .not))).length =
          (L.filter (fun g => decide (g.op = .not))).length := by
        intro L; induction L using List.reverseRecOn with
        | nil => simp
        | append_singleton xs g ihL =>
          rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append, List.filter_append,
            List.length_append, List.length_append]
          have ha : (List.range xs.length).filter (fun i => decide (((xs ++ [g]).getD i ⟨.or, []⟩).op = .not)) =
              (List.range xs.length).filter (fun i => decide ((xs.getD i ⟨.or, []⟩).op = .not)) := by
            apply List.filter_congr; intro i hi
            have hilt := List.mem_range.mp hi
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt, ← List.getD_eq_getElem?_getD]
          have hb : ([xs.length].filter (fun i => decide (((xs ++ [g]).getD i ⟨.or, []⟩).op = .not))).length =
              ([g].filter (fun g' => decide (g'.op = .not))).length := by
            have hgd : (xs ++ [g]).getD xs.length ⟨.or, []⟩ = g := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
            cases h : g.op <;> simp [hgd, h]
          rw [ha, ihL, hb]
      exact hlen C.gates
    rw [← hnc]
    refine Finset.card_le_card_of_injOn (fun u => u - n) ?_ ?_
    · intro u hu
      dsimp only
      obtain ⟨huw, hun, hop⟩ := Finset.mem_filter.mp hu
      have hule := mem_nodeSet_le n C hrb w u huw
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hop⟩
    · intro u1 hu1 u2 hu2 heq
      dsimp only at heq
      have h1 := (Finset.mem_filter.mp hu1).2.1
      have h2 := (Finset.mem_filter.mp hu2).2.1
      omega
  have hmain_ineq : ∀ w < n + C.size,
      (chg w).card ≤ (inSet w).card ∧ (inSet w).card ≤ (posSet w).card + 1 := by
    intro w hw
    constructor
    · calc (chg w).card
          ≤ ((inSet w).biUnion chg).card := Finset.card_le_card (hchg_sub_in w hw)
        _ ≤ ∑ j ∈ inSet w, (chg j).card := Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ inSet w, 1 := Finset.sum_le_sum fun j hj => hchg_in_le1 j (Finset.mem_filter.mp hj).2
        _ = (inSet w).card := by simp
    · have h1 : (nodeSet n C w).card - 1 ≤ ((nodeSet n C w).biUnion (wireChildren n C)).card := by
        have := Finset.card_le_card (nodeSet_erase_sub_biUnion n C hrb w)
        rwa [Finset.card_erase_of_mem (mem_nodeSet_self n C hrb w)] at this
      have h2 : ((nodeSet n C w).biUnion (wireChildren n C)).card ≤ ∑ u ∈ nodeSet n C w, (wireChildren n C u).card :=
        Finset.card_biUnion_le
      have h3 := hdeg_sum w hw
      have h4 := hnode_part w
      have h5 : 1 ≤ (nodeSet n C w).card := Finset.card_pos.mpr ⟨w, mem_nodeSet_self n C hrb w⟩
      omega
  have hpart_a : ((Finset.range l).filter (fun t => y t ≠ y (t + 1))).card - 1 ≤
      C.size - PEqualNP.NotBracket.notCount C := by
    rw [← hchg_out]
    have ⟨h1, h2⟩ := hmain_ineq C.output hout
    have h3 := hposSet_le_pos C.output hout
    omega
  refine ⟨hpart_a, ?_⟩
  intro htight
  rw [← hchg_out] at htight
  have ⟨h1, h2⟩ := hmain_ineq C.output hout
  have h3 := hposSet_le_pos C.output hout
  have hbi_ge : (nodeSet n C C.output).card - 1 ≤ ((nodeSet n C C.output).biUnion (wireChildren n C)).card := by
    have := Finset.card_le_card (nodeSet_erase_sub_biUnion n C hrb C.output)
    rwa [Finset.card_erase_of_mem (mem_nodeSet_self n C hrb C.output)] at this
  have hbi_le : ((nodeSet n C C.output).biUnion (wireChildren n C)).card ≤
      ∑ u ∈ nodeSet n C C.output, (wireChildren n C u).card := Finset.card_biUnion_le
  have hsum_le := hdeg_sum C.output hout
  have hpart := hnode_part C.output
  have hpos_ne : 1 ≤ (nodeSet n C C.output).card := Finset.card_pos.mpr ⟨C.output, mem_nodeSet_self n C hrb C.output⟩
  by_cases hchg0 : (chg C.output).card = 0
  · have hfall0 : (fall C.output).card = 0 := by
      have hsub : fall C.output ⊆ chg C.output := fun t ht => by
        obtain ⟨htl, h1', h2'⟩ := Finset.mem_filter.mp ht
        exact Finset.mem_filter.mpr ⟨htl, by rw [h1', h2']; decide⟩
      have := Finset.card_le_card hsub; omega
    rw [← hfall_out, hfall0]; omega
  -- Now (chg C.output).card ≥ 1, so ALL inequalities are equalities!
  have hsum_eq : ((nodeSet n C C.output).biUnion (wireChildren n C)).card =
      ∑ u ∈ nodeSet n C C.output, (wireChildren n C u).card := by omega
  -- Pairwise disjointness of wireChildren on nodeSet C.output
  have hch_disj : ∀ u1 ∈ nodeSet n C C.output, ∀ u2 ∈ nodeSet n C C.output,
      u1 ≠ u2 → Disjoint (wireChildren n C u1) (wireChildren n C u2) := by
    by_contra hnot
    push_neg at hnot
    obtain ⟨u1, hu1, u2, hu2, hne, hnd⟩ := hnot
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨v, hv1, hv2⟩ := hnd
    have hlt : ((nodeSet n C C.output).biUnion (wireChildren n C)).card <
        ∑ u ∈ nodeSet n C C.output, (wireChildren n C u).card := by
      let rest := ((nodeSet n C C.output).erase u1).erase u2
      have hu2' : u2 ∈ (nodeSet n C C.output).erase u1 := Finset.mem_erase.mpr ⟨hne.symm, hu2⟩
      have hsplit : nodeSet n C C.output = insert u1 (insert u2 rest) := by
        rw [Finset.insert_erase hu2', Finset.insert_erase hu1]
      have hu1_ni : u1 ∉ insert u2 rest := by simp [rest, hne]
      have hu2_ni : u2 ∉ rest := by simp [rest]
      rw [hsplit, Finset.biUnion_insert, Finset.biUnion_insert,
        Finset.sum_insert hu1_ni, Finset.sum_insert hu2_ni]
      have h12 : (wireChildren n C u1 ∪ wireChildren n C u2).card <
          (wireChildren n C u1).card + (wireChildren n C u2).card := by
        have hcap := Finset.card_union_add_card_inter (wireChildren n C u1) (wireChildren n C u2)
        have hpos : 0 < (wireChildren n C u1 ∩ wireChildren n C u2).card :=
          Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hv1, hv2⟩⟩
        omega
      have hrest_le : (rest.biUnion (wireChildren n C)).card ≤ ∑ u ∈ rest, (wireChildren n C u).card :=
        Finset.card_biUnion_le
      have hun_le : (wireChildren n C u1 ∪ (wireChildren n C u2 ∪ rest.biUnion (wireChildren n C))).card ≤
          (wireChildren n C u1 ∪ wireChildren n C u2).card + (rest.biUnion (wireChildren n C)).card := by
        rw [← Finset.union_assoc]; exact Finset.card_union_le _ _
      omega
    omega
  -- Pairwise disjointness of chg on inSet C.output
  have hchg_in_eq : ((inSet C.output).biUnion chg).card = ∑ j ∈ inSet C.output, (chg j).card := by
    have ha : (chg C.output).card ≤ ((inSet C.output).biUnion chg).card :=
      Finset.card_le_card (hchg_sub_in C.output hout)
    have hb : ((inSet C.output).biUnion chg).card ≤ ∑ j ∈ inSet C.output, (chg j).card := Finset.card_biUnion_le
    have hc : ∑ j ∈ inSet C.output, (chg j).card ≤ (inSet C.output).card := by
      calc ∑ j ∈ inSet C.output, (chg j).card
          ≤ ∑ _j ∈ inSet C.output, 1 := Finset.sum_le_sum fun j hj => hchg_in_le1 j (Finset.mem_filter.mp hj).2
        _ = (inSet C.output).card := by simp
    omega
  have hchg_disj : ∀ j1 ∈ inSet C.output, ∀ j2 ∈ inSet C.output, j1 ≠ j2 → Disjoint (chg j1) (chg j2) := by
    by_contra hnot
    push_neg at hnot
    obtain ⟨j1, hj1, j2, hj2, hne, hnd⟩ := hnot
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨t, ht1, ht2⟩ := hnd
    have hlt : ((inSet C.output).biUnion chg).card < ∑ j ∈ inSet C.output, (chg j).card := by
      let rest := ((inSet C.output).erase j1).erase j2
      have hj2' : j2 ∈ (inSet C.output).erase j1 := Finset.mem_erase.mpr ⟨hne.symm, hj2⟩
      have hsplit : inSet C.output = insert j1 (insert j2 rest) := by
        rw [Finset.insert_erase hj2', Finset.insert_erase hj1]
      have hj1_ni : j1 ∉ insert j2 rest := by simp [rest, hne]
      have hj2_ni : j2 ∉ rest := by simp [rest]
      rw [hsplit, Finset.biUnion_insert, Finset.biUnion_insert,
        Finset.sum_insert hj1_ni, Finset.sum_insert hj2_ni]
      have h12 : (chg j1 ∪ chg j2).card < (chg j1).card + (chg j2).card := by
        have hcap := Finset.card_union_add_card_inter (chg j1) (chg j2)
        have hpos : 0 < (chg j1 ∩ chg j2).card := Finset.card_pos.mpr ⟨t, Finset.mem_inter.mpr ⟨ht1, ht2⟩⟩
        omega
      have hrest_le : (rest.biUnion chg).card ≤ ∑ j ∈ rest, (chg j).card := Finset.card_biUnion_le
      have hun_le : (chg j1 ∪ (chg j2 ∪ rest.biUnion chg)).card ≤ (chg j1 ∪ chg j2).card + (rest.biUnion chg).card := by
        rw [← Finset.union_assoc]; exact Finset.card_union_le _ _
      omega
    omega
  -- Children of any u ∈ nodeSet C.output have disjoint nodeSets!
  have hnode_disj : ∀ u ∈ nodeSet n C C.output, ∀ a ∈ wireChildren n C u, ∀ b ∈ wireChildren n C u,
      a ≠ b → Disjoint (nodeSet n C a) (nodeSet n C b) := by
    intro u hu a ha b hb hab
    by_contra hnd
    rw [Finset.not_disjoint_iff] at hnd
    have hne : (nodeSet n C a ∩ nodeSet n C b).Nonempty := by
      obtain ⟨v, hv1, hv2⟩ := hnd; exact ⟨v, Finset.mem_inter.mpr ⟨hv1, hv2⟩⟩
    let v := (nodeSet n C a ∩ nodeSet n C b).max' hne
    have hvm : v ∈ nodeSet n C a ∩ nodeSet n C b := Finset.max'_mem _ hne
    obtain ⟨hva, hvb⟩ := Finset.mem_inter.mp hvm
    have ha_in : a ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output u hu
      (by rw [nodeSet_eq n C hrb u]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha, mem_nodeSet_self n C hrb a⟩))
    have hb_in : b ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output u hu
      (by rw [nodeSet_eq n C hrb u]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨b, hb, mem_nodeSet_self n C hrb b⟩))
    by_cases hva_eq : v = a
    · rw [hva_eq] at hvb
      have hmem := nodeSet_erase_sub_biUnion n C hrb b (Finset.mem_erase.mpr ⟨hab, hvb⟩)
      obtain ⟨p, hpb, hap⟩ := Finset.mem_biUnion.mp hmem
      have hpu : p ≠ u := by
        have h1 := mem_nodeSet_le n C hrb b p hpb
        have h2 := wireChildren_lt n C hrb u b hb
        omega
      have hp_in : p ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output b hb_in hpb
      exact Finset.disjoint_left.mp (hch_disj u hu p hp_in hpu.symm) ha hap
    · by_cases hvb_eq : v = b
      · rw [hvb_eq] at hva
        have hmem := nodeSet_erase_sub_biUnion n C hrb a (Finset.mem_erase.mpr ⟨hab.symm, hva⟩)
        obtain ⟨p, hpa, hbp⟩ := Finset.mem_biUnion.mp hmem
        have hpu : p ≠ u := by
          have h1 := mem_nodeSet_le n C hrb a p hpa
          have h2 := wireChildren_lt n C hrb u a ha
          omega
        have hp_in : p ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output a ha_in hpa
        exact Finset.disjoint_left.mp (hch_disj u hu p hp_in hpu.symm) hb hbp
      · have hma := nodeSet_erase_sub_biUnion n C hrb a (Finset.mem_erase.mpr ⟨hva_eq, hva⟩)
        have hmb := nodeSet_erase_sub_biUnion n C hrb b (Finset.mem_erase.mpr ⟨hvb_eq, hvb⟩)
        obtain ⟨pa, hpa, hvpa⟩ := Finset.mem_biUnion.mp hma
        obtain ⟨pb, hpb, hvpb⟩ := Finset.mem_biUnion.mp hmb
        have hpne : pa ≠ pb := by
          intro hpeq; subst hpeq
          have hle := Finset.le_max' (nodeSet n C a ∩ nodeSet n C b) pa (Finset.mem_inter.mpr ⟨hpa, hpb⟩)
          have hlt := wireChildren_lt n C hrb pa v hvpa
          dsimp only [v] at hlt; omega
        have hpa_in : pa ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output a ha_in hpa
        have hpb_in : pb ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output b hb_in hpb
        exact Finset.disjoint_left.mp (hch_disj pa hpa_in pb hpb_in hpne) hvpa hvpb
  -- Strong induction on w ∈ nodeSet C.output: (fall w).card ≤ (notSet w).card
  have hfall_le_not : ∀ w ∈ nodeSet n C C.output, (fall w).card ≤ (notSet w).card := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwo
      have hwlt : w < n + C.size := lt_of_le_of_lt (mem_nodeSet_le n C hrb C.output w hwo) hout
      by_cases hwn : w < n
      · have hfe : fall w = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro t ht ⟨h1, h2⟩
          rw [Finset.mem_range] at ht
          have hw1 : wire t w = x t ⟨w, hwn⟩ := by
            dsimp only [wire]; rw [run_input C.gates _ w (by simp [hwn]), List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hwn]; rfl
          have hw2 : wire (t + 1) w = x (t + 1) ⟨w, hwn⟩ := by
            dsimp only [wire]; rw [run_input C.gates _ w (by simp [hwn]), List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hwn]; rfl
          rw [hw1] at h1; rw [hw2] at h2
          have := hx t ht ⟨w, hwn⟩ h1; rw [h2] at this; cases this
        rw [hfe]; simp
      · have hg_idx : w - n < C.gates.length := by dsimp [Circuit.size] at hwlt; omega
        have hg_eq : C.gates[w - n] = C.gates.getD (w - n) ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hg_idx).symm
        have hw_eq : w = n + (w - n) := by omega
        rcases (hfan _ (List.getElem_mem hg_idx)).1 with hand | hor | hnot'
        · -- AND gate
          have hlen := (hfan _ (List.getElem_mem hg_idx)).2
          rcases hin : (C.gates[w - n]).inputs with _ | ⟨a, rest⟩
          · -- constant true: fall = ∅
            have hfe : fall w = ∅ := by
              rw [Finset.filter_eq_empty_iff]; intro t _ ⟨_, h2⟩
              have hrg := run_gate C.gates (List.ofFn (x (t + 1))) (w - n) hg_idx
              rw [List.length_ofFn, ← hw_eq, hand, hin] at hrg
              change (run C.gates _).getD w false = false at h2; rw [hrg] at h2; cases h2
            rw [hfe]; simp
          · rcases rest with _ | ⟨b, rest2⟩
            · -- unary AND [a]: wire t w = wire t a
              have ha_ch : a ∈ wireChildren n C w := by
                dsimp only [wireChildren]; rw [if_pos ⟨by omega, hwlt⟩, ← hg_eq, hand, hin]; simp
              have halt := wireChildren_lt n C hrb w a ha_ch
              have hao : a ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output w hwo
                (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩))
              have hweq : ∀ t, wire t w = wire t a := fun t => by
                dsimp only [wire]; have hrg := run_gate C.gates (List.ofFn (x t)) (w - n) hg_idx
                rw [List.length_ofFn, ← hw_eq, hand, hin, andEval] at hrg
                rw [hrg]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, if_pos halt]
              have hfeq : fall w = fall a := by ext t; simp [fall, hweq]
              have hnsub : notSet a ⊆ notSet w := Finset.filter_subset_filter _
                (nodeSet_subset_of_mem n C hrb w a (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩)))
              rw [hfeq]; exact le_trans (ih a halt hao) (Finset.card_le_card hnsub)
            · have hrest2 : rest2 = [] := by rw [hin] at hlen; cases rest2 <;> simp at hlen ⊢
              subst hrest2
              have ha_ch : a ∈ wireChildren n C w := by
                dsimp only [wireChildren]; rw [if_pos ⟨by omega, hwlt⟩, ← hg_eq, hand, hin]; simp
              have hb_ch : b ∈ wireChildren n C w := by
                dsimp only [wireChildren]; rw [if_pos ⟨by omega, hwlt⟩, ← hg_eq, hand, hin]; simp
              have halt := wireChildren_lt n C hrb w a ha_ch
              have hblt := wireChildren_lt n C hrb w b hb_ch
              have hao : a ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output w hwo
                (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩))
              have hbo : b ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output w hwo
                (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨b, hb_ch, mem_nodeSet_self n C hrb b⟩))
              have hweq : ∀ t, wire t w = (wire t a && wire t b) := fun t => by
                dsimp only [wire]; have hrg := run_gate C.gates (List.ofFn (x t)) (w - n) hg_idx
                rw [List.length_ofFn, ← hw_eq, hand, hin, andEval] at hrg
                rw [hrg]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, if_pos halt, if_pos hblt]
              by_cases hab : a = b
              · subst hab
                have hfeq : fall w = fall a := by ext t; simp [fall, hweq]
                have hnsub : notSet a ⊆ notSet w := Finset.filter_subset_filter _
                  (nodeSet_subset_of_mem n C hrb w a (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩)))
                rw [hfeq]; exact le_trans (ih a halt hao) (Finset.card_le_card hnsub)
              · have hfsub : fall w ⊆ fall a ∪ fall b := by
                  intro t ht
                  obtain ⟨htl, h1', h2'⟩ := Finset.mem_filter.mp ht
                  rw [hweq t] at h1'; rw [hweq (t + 1)] at h2'
                  dsimp only [fall]
                  cases ha1 : wire t a <;> cases hb1 : wire t b <;> cases ha2 : wire (t + 1) a <;> cases hb2 : wire (t + 1) b <;>
                    simp only [ha1, hb1, ha2, hb2, Bool.and_true, Bool.and_false] at h1' h2'
                  all_goals first
                    | exact absurd h1' (by decide)
                    | exact absurd h2' (by decide)
                    | exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨htl, ha1, ha2⟩)
                    | exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htl, hb1, hb2⟩)
                have hdisj_ab : Disjoint (notSet a) (notSet b) :=
                  Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
                    (hnode_disj w hwo a ha_ch b hb_ch hab)
                have hnsub : notSet a ∪ notSet b ⊆ notSet w := Finset.union_subset
                  (Finset.filter_subset_filter _ (nodeSet_subset_of_mem n C hrb w a
                    (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩))))
                  (Finset.filter_subset_filter _ (nodeSet_subset_of_mem n C hrb w b
                    (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨b, hb_ch, mem_nodeSet_self n C hrb b⟩))))
                calc (fall w).card
                    ≤ (fall a ∪ fall b).card := Finset.card_le_card hfsub
                  _ ≤ (fall a).card + (fall b).card := Finset.card_union_le _ _
                  _ ≤ (notSet a).card + (notSet b).card := Nat.add_le_add (ih a halt hao) (ih b hblt hbo)
                  _ = (notSet a ∪ notSet b).card := (Finset.card_union_of_disjoint hdisj_ab).symm
                  _ ≤ (notSet w).card := Finset.card_le_card hnsub
        · -- OR gate
          have hlen := (hfan _ (List.getElem_mem hg_idx)).2
          rcases hin : (C.gates[w - n]).inputs with _ | ⟨a, rest⟩
          · have hfe : fall w = ∅ := by
              rw [Finset.filter_eq_empty_iff]; intro t _ ⟨h1', _⟩
              have hrg := run_gate C.gates (List.ofFn (x t)) (w - n) hg_idx
              rw [List.length_ofFn, ← hw_eq, hor, hin] at hrg
              change (run C.gates _).getD w false = true at h1'; rw [hrg] at h1'; cases h1'
            rw [hfe]; simp
          · rcases rest with _ | ⟨b, rest2⟩
            · have ha_ch : a ∈ wireChildren n C w := by
                dsimp only [wireChildren]; rw [if_pos ⟨by omega, hwlt⟩, ← hg_eq, hor, hin]; simp
              have halt := wireChildren_lt n C hrb w a ha_ch
              have hao : a ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output w hwo
                (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩))
              have hweq : ∀ t, wire t w = wire t a := fun t => by
                dsimp only [wire]; have hrg := run_gate C.gates (List.ofFn (x t)) (w - n) hg_idx
                rw [List.length_ofFn, ← hw_eq, hor, hin, orEval] at hrg
                rw [hrg]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, if_pos halt]
              have hfeq : fall w = fall a := by ext t; simp [fall, hweq]
              have hnsub : notSet a ⊆ notSet w := Finset.filter_subset_filter _
                (nodeSet_subset_of_mem n C hrb w a (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩)))
              rw [hfeq]; exact le_trans (ih a halt hao) (Finset.card_le_card hnsub)
            · have hrest2 : rest2 = [] := by rw [hin] at hlen; cases rest2 <;> simp at hlen ⊢
              subst hrest2
              have ha_ch : a ∈ wireChildren n C w := by
                dsimp only [wireChildren]; rw [if_pos ⟨by omega, hwlt⟩, ← hg_eq, hor, hin]; simp
              have hb_ch : b ∈ wireChildren n C w := by
                dsimp only [wireChildren]; rw [if_pos ⟨by omega, hwlt⟩, ← hg_eq, hor, hin]; simp
              have halt := wireChildren_lt n C hrb w a ha_ch
              have hblt := wireChildren_lt n C hrb w b hb_ch
              have hao : a ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output w hwo
                (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩))
              have hbo : b ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output w hwo
                (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨b, hb_ch, mem_nodeSet_self n C hrb b⟩))
              have hweq : ∀ t, wire t w = (wire t a || wire t b) := fun t => by
                dsimp only [wire]; have hrg := run_gate C.gates (List.ofFn (x t)) (w - n) hg_idx
                rw [List.length_ofFn, ← hw_eq, hor, hin, orEval] at hrg
                rw [hrg]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, if_pos halt, if_pos hblt]
              by_cases hab : a = b
              · subst hab
                have hfeq : fall w = fall a := by ext t; simp [fall, hweq]
                have hnsub : notSet a ⊆ notSet w := Finset.filter_subset_filter _
                  (nodeSet_subset_of_mem n C hrb w a (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩)))
                rw [hfeq]; exact le_trans (ih a halt hao) (Finset.card_le_card hnsub)
              · have hfsub : fall w ⊆ fall a ∪ fall b := by
                  intro t ht
                  obtain ⟨htl, h1', h2'⟩ := Finset.mem_filter.mp ht
                  rw [hweq t] at h1'; rw [hweq (t + 1)] at h2'
                  dsimp only [fall]
                  cases ha1 : wire t a <;> cases hb1 : wire t b <;> cases ha2 : wire (t + 1) a <;> cases hb2 : wire (t + 1) b <;>
                    simp only [ha1, hb1, ha2, hb2, Bool.or_true, Bool.or_false] at h1' h2'
                  all_goals first
                    | exact absurd h1' (by decide)
                    | exact absurd h2' (by decide)
                    | exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨htl, ha1, ha2⟩)
                    | exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htl, hb1, hb2⟩)
                have hdisj_ab : Disjoint (notSet a) (notSet b) :=
                  Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
                    (hnode_disj w hwo a ha_ch b hb_ch hab)
                have hnsub : notSet a ∪ notSet b ⊆ notSet w := Finset.union_subset
                  (Finset.filter_subset_filter _ (nodeSet_subset_of_mem n C hrb w a
                    (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩))))
                  (Finset.filter_subset_filter _ (nodeSet_subset_of_mem n C hrb w b
                    (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨b, hb_ch, mem_nodeSet_self n C hrb b⟩))))
                calc (fall w).card
                    ≤ (fall a ∪ fall b).card := Finset.card_le_card hfsub
                  _ ≤ (fall a).card + (fall b).card := Finset.card_union_le _ _
                  _ ≤ (notSet a).card + (notSet b).card := Nat.add_le_add (ih a halt hao) (ih b hblt hbo)
                  _ = (notSet a ∪ notSet b).card := (Finset.card_union_of_disjoint hdisj_ab).symm
                  _ ≤ (notSet w).card := Finset.card_le_card hnsub
        · -- NOT gate
          rcases hin : (C.gates[w - n]).inputs with _ | ⟨a, rest⟩
          · have hfe : fall w = ∅ := by
              rw [Finset.filter_eq_empty_iff]; intro t _ ⟨_, h2'⟩
              have hrg := run_gate C.gates (List.ofFn (x (t + 1))) (w - n) hg_idx
              rw [List.length_ofFn, ← hw_eq, hnot', hin] at hrg
              change (run C.gates _).getD w false = false at h2'; rw [hrg] at h2'; cases h2'
            rw [hfe]; simp
          · have ha_ch : a ∈ wireChildren n C w := by
              dsimp only [wireChildren]; rw [if_pos ⟨by omega, hwlt⟩, ← hg_eq, hnot', hin]; simp
            have halt := wireChildren_lt n C hrb w a ha_ch
            have hao : a ∈ nodeSet n C C.output := nodeSet_subset_of_mem n C hrb C.output w hwo
              (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩))
            have hweq : ∀ t, wire t w = !(wire t a) := fun t => by
              dsimp only [wire]; have hrg := run_gate C.gates (List.ofFn (x t)) (w - n) hg_idx
              rw [List.length_ofFn, ← hw_eq, hnot', hin, List.map_cons, notEval_cons] at hrg
              rw [hrg, if_pos halt]
            have hfeq : fall w = (Finset.range l).filter (fun t => wire t a = false ∧ wire (t + 1) a = true) := by
              ext t; simp only [fall, Finset.mem_filter, hweq]
              constructor <;> rintro ⟨ht, h1', h2'⟩ <;> refine ⟨ht, ?_, ?_⟩
              · cases h : wire t a <;> rw [h] at h1' <;> first | rfl | cases h1'
              · cases h : wire (t + 1) a <;> rw [h] at h2' <;> first | rfl | cases h2'
              · rw [h1']; rfl
              · rw [h2']; rfl
            have hle1 : (fall w).card ≤ (fall a).card + 1 := by
              rw [hfeq]; exact rise_le_fall_add_one (fun t => wire t a) l
            have hw_in_not : w ∈ notSet w :=
              Finset.mem_filter.mpr ⟨mem_nodeSet_self n C hrb w, by omega, hg_eq ▸ hnot'⟩
            have hw_ni_a : w ∉ notSet a := fun hm => by
              have := mem_nodeSet_le n C hrb a w (Finset.mem_filter.mp hm).1; omega
            have hsub : insert w (notSet a) ⊆ notSet w := Finset.insert_subset hw_in_not
              (Finset.filter_subset_filter _ (nodeSet_subset_of_mem n C hrb w a
                (by rw [nodeSet_eq n C hrb w]; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha_ch, mem_nodeSet_self n C hrb a⟩))))
            have hncard : (notSet a).card + 1 ≤ (notSet w).card := by
              have := Finset.card_le_card hsub
              rwa [Finset.card_insert_of_notMem hw_ni_a] at this
            have := ih a halt hao
            omega
  rw [← hfall_out]
  exact le_trans (hfall_le_not C.output (mem_nodeSet_self n C hrb C.output)) (hnotSet_le_not C.output hout)

private theorem main_clean (n l : ℕ) (x : ℕ → Fin n → Bool) (y : ℕ → Bool)
    (hx : ∀ t < l, ∀ j, x t j = true → x (t + 1) j = true) :
    let changes := (Finset.range l).filter (fun t => y t ≠ y (t + 1))
    let k := changes.card
    let S := ((Finset.range l).filter (fun t => y t = true ∧ y (t + 1) = false)).card
    0 < k → (∀ t ∈ changes, ∃ j, x t j = false ∧ x (t + 1) j = true) →
    let fits := fun (C : Circuit) =>
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      C.output < n + C.size ∧ ∀ t ≤ l, C.eval (List.ofFn (x t)) = y t
    let positive := fun (C : Circuit) => C.size - PEqualNP.NotBracket.notCount C
    (∃ C, fits C ∧ positive C = k - 1 ∧ PEqualNP.NotBracket.notCount C = S ∧
      ∀ i : ℕ, (C.gates.flatMap (fun g => g.inputs)).count i ≤ 1) ∧
    (∀ C, fits C → k - 1 ≤ positive C ∧ (positive C = k - 1 → S ≤ PEqualNP.NotBracket.notCount C)) := by
  dsimp only
  intro hpos hchg
  constructor
  · obtain ⟨C, h1, h2, h3, h4, h5, h6, h7, _, _⟩ := part1_ind n l x hx _ y rfl hpos hchg
    exact ⟨C, ⟨h1, h2, h3, h4⟩, h5, h6, h7⟩
  · rintro C ⟨h1, h2, h3, h4⟩
    exact part2_clean n l x y hx C h1 h2 h3 h4

end PEqualNP.Outside.L_lib_1320

theorem PEqualNP.Outside.L_lib_1320 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n l : Nat) (x : Nat → Fin n → Bool) (y : Nat → Bool),
      (∀ t < l, ∀ j, x t j = true → x (t+1) j = true) →
      let changes := (Finset.range l).filter (fun t => y t ≠ y (t+1))
      let k := changes.card
      let S := ((Finset.range l).filter (fun t => y t = true ∧ y (t+1) = false)).card
      0 < k → (∀ t ∈ changes, ∃ j, x t j = false ∧ x (t+1) j = true) →
      let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
        C.output < n+C.size ∧ ∀ t ≤ l, C.eval (List.ofFn (x t)) = y t
      let positive := fun (C : PEqualNP.CircuitLowerBounds.Circuit) => C.size-PEqualNP.NotBracket.notCount C
      (∃ C, fits C ∧ positive C = k-1 ∧ PEqualNP.NotBracket.notCount C = S ∧
        ∀ i : Nat, (C.gates.flatMap (fun g => g.inputs)).count i ≤ 1) ∧
      (∀ C, fits C → k-1 ≤ positive C ∧ (positive C = k-1 → S ≤ PEqualNP.NotBracket.notCount C)) := by
  dsimp only
  intro n l x y hx hpos hchg
  have hfeq1 :
      @Finset.filter ℕ (fun t => y t ≠ y (t + 1)) (fun t => Classical.propDecidable _) (Finset.range l) =
      (Finset.range l).filter (fun t => y t ≠ y (t + 1)) := by ext t; simp
  have hfeq2 :
      @Finset.filter ℕ (fun t => y t = true ∧ y (t + 1) = false) (fun t => Classical.propDecidable _) (Finset.range l) =
      (Finset.range l).filter (fun t => y t = true ∧ y (t + 1) = false) := by ext t; simp
  rw [hfeq1] at hpos hchg ⊢
  rw [hfeq2]
  have hdec : (fun a b : ℕ => Classical.propDecidable (a = b)) = instDecidableEqNat := by
    funext a b; exact Subsingleton.elim _ _
  rw [hdec]
  have h := PEqualNP.Outside.L_lib_1320.main_clean n l x y hx hpos hchg
  dsimp only at h
  exact h
