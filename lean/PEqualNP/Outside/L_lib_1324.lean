import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1324

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

private abbrev W (n : ℕ) := Fin (n + 1) → Bool

private def threshold {n : ℕ} (q : Fin n) (t : Fin (n + 1)) : Bool := decide (q.val < t.val)
private def neg {n : ℕ} (f : W n) (t : Fin (n + 1)) : Bool := !(f t)
private def meet {n : ℕ} (f g : W n) (t : Fin (n + 1)) : Bool := f t && g t
private def join {n : ℕ} (f g : W n) (t : Fin (n + 1)) : Bool := f t || g t

private def down {n : ℕ} (f : W n) : Finset (Fin n) :=
  Finset.univ.filter (fun t => f t.castSucc = true ∧ f t.succ = false)

private def raw (n : ℕ) : Finset (W n) :=
  insert (fun _ => false) (insert (fun _ => true) (Finset.univ.image threshold))

private def inp {n : ℕ} (t : Fin (n + 1)) : List Bool :=
  List.ofFn (fun q : Fin n => threshold q t) ++ [false, true]

private theorem inp_len {n : ℕ} (t : Fin (n + 1)) : (inp t).length = n + 2 := by simp [inp]

private theorem inp_getD_lt {n : ℕ} (t : Fin (n + 1)) (q : Fin n) :
    (inp t).getD q.val false = threshold q t := by
  dsimp only [inp]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp), List.getElem?_ofFn]
  simp [q.isLt]

private theorem inp_getD_false {n : ℕ} (t : Fin (n + 1)) : (inp t).getD n false = false := by
  dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp

private theorem inp_getD_true {n : ℕ} (t : Fin (n + 1)) : (inp t).getD (n + 1) false = true := by
  dsimp only [inp]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]; simp

-- Helper: if f has no transitions in [a, b], f a = f b
private theorem const_of_no_trans {n : ℕ} (f : W n) (a b : Fin (n + 1)) (hab : a.val ≤ b.val)
    (hno : ∀ t : Fin n, a.val ≤ t.val → t.val < b.val → f t.castSucc = f t.succ) :
    f a = f b := by
  have ha := a.isLt
  have hb := b.isLt
  have hsub : ∀ d (hd : a.val + d ≤ b.val), f ⟨a.val + d, by omega⟩ = f a := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have ht_lt : a.val + d < n := by omega
      have h1 := hno ⟨a.val + d, ht_lt⟩ (by dsimp; omega) (by dsimp; omega)
      have h2 := ih (by omega)
      exact h1.symm.trans h2
  have := hsub (b.val - a.val) (by omega)
  have heq : (⟨a.val + (b.val - a.val), by omega⟩ : Fin (n + 1)) = b := Fin.ext (by dsimp; omega)
  rw [heq] at this
  exact this.symm

-- Characterization of single-fall single-rise function
private theorem interval_char {n : ℕ} (f : W n) (d u : Fin n)
    (hd : down f = {d}) (hu : down (neg f) = {u}) :
    (u < d → f = meet (threshold u) (neg (threshold d))) ∧
    (d < u → f = join (threshold u) (neg (threshold d))) ∧
    u ≠ d := by
  have hd_mem : d ∈ down f := by rw [hd]; exact Finset.mem_singleton_self d
  have hu_mem : u ∈ down (neg f) := by rw [hu]; exact Finset.mem_singleton_self u
  have hd1 : f d.castSucc = true := (Finset.mem_filter.mp hd_mem).2.1
  have hd2 : f d.succ = false := (Finset.mem_filter.mp hd_mem).2.2
  have hu1 : f u.castSucc = false := by
    have := (Finset.mem_filter.mp hu_mem).2.1; dsimp [neg] at this; cases h : f u.castSucc <;> simp_all
  have hu2 : f u.succ = true := by
    have := (Finset.mem_filter.mp hu_mem).2.2; dsimp [neg] at this; cases h : f u.succ <;> simp_all
  have hne : u ≠ d := fun h => by rw [h, hd1] at hu1; cases hu1
  have hno : ∀ t : Fin n, t ≠ d → t ≠ u → f t.castSucc = f t.succ := by
    intro t htd htu
    cases h1 : f t.castSucc <;> cases h2 : f t.succ
    · rfl
    · exfalso
      have hm : t ∈ down (neg f) := Finset.mem_filter.mpr ⟨Finset.mem_univ t, by simp [neg, h1, h2]⟩
      rw [hu, Finset.mem_singleton] at hm; exact htu hm
    · exfalso
      have hm : t ∈ down f := Finset.mem_filter.mpr ⟨Finset.mem_univ t, h1, h2⟩
      rw [hd, Finset.mem_singleton] at hm; exact htd hm
    · rfl
  refine ⟨?_, ?_, hne⟩
  · intro hlt
    have hlt' : u.val < d.val := hlt
    funext t
    dsimp only [meet, threshold, neg]
    by_cases h1 : t.val ≤ u.val
    · have hc := const_of_no_trans f t u.castSucc h1 (fun s hs1 hs2 =>
        hno s (fun h => by rw [h] at hs2; simp only [Fin.val_castSucc] at hs2; omega)
              (fun h => by rw [h] at hs2; simp only [Fin.val_castSucc] at hs2; omega))
      rw [hc, hu1]; simp [show ¬ (u.val < t.val) by omega]
    · by_cases h2 : t.val ≤ d.val
      · have hc := const_of_no_trans f u.succ t (by simp; omega) (fun s hs1 hs2 =>
          hno s (fun h => by rw [h] at hs2; omega)
                (fun h => by rw [h] at hs1; simp only [Fin.val_succ] at hs1; omega))
        rw [← hc, hu2]; simp [show u.val < t.val by omega, show ¬ (d.val < t.val) by omega]
      · have hc := const_of_no_trans f d.succ t (by simp; omega) (fun s hs1 hs2 =>
          hno s (fun h => by rw [h] at hs1; simp only [Fin.val_succ] at hs1; omega)
                (fun h => by rw [h] at hs1; simp only [Fin.val_succ] at hs1; omega))
        rw [← hc, hd2]; simp [show d.val < t.val by omega]
  · intro hlt
    have hlt' : d.val < u.val := hlt
    funext t
    dsimp only [join, threshold, neg]
    by_cases h1 : t.val ≤ d.val
    · have hc := const_of_no_trans f t d.castSucc h1 (fun s hs1 hs2 =>
        hno s (fun h => by rw [h] at hs2; simp only [Fin.val_castSucc] at hs2; omega)
              (fun h => by rw [h] at hs2; simp only [Fin.val_castSucc] at hs2; omega))
      rw [hc, hd1]; simp [show ¬ (d.val < t.val) by omega]
    · by_cases h2 : t.val ≤ u.val
      · have hc := const_of_no_trans f d.succ t (by simp; omega) (fun s hs1 hs2 =>
          hno s (fun h => by rw [h] at hs1; simp only [Fin.val_succ] at hs1; omega)
                (fun h => by rw [h] at hs2; omega))
        rw [← hc, hd2]; simp [show ¬ (u.val < t.val) by omega, show d.val < t.val by omega]
      · have hc := const_of_no_trans f u.succ t (by simp; omega) (fun s hs1 hs2 =>
          hno s (fun h => by rw [h] at hs1; simp only [Fin.val_succ] at hs1; omega)
                (fun h => by rw [h] at hs1; simp only [Fin.val_succ] at hs1; omega))
        rw [← hc, hu2]; simp [show u.val < t.val by omega]

private theorem down_raw_empty {n : ℕ} (f : W n) (hf : f ∈ raw n) : down f = ∅ := by
  dsimp only [down]
  rw [Finset.filter_eq_empty_iff]
  intro t _ ⟨h1, h2⟩
  simp only [raw, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hf
  rcases hf with rfl | rfl | ⟨q, rfl⟩
  · cases h1
  · cases h2
  · dsimp only [threshold] at h1 h2
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Fin.val_castSucc, Fin.val_succ] at h1 h2
    omega

private theorem down_neg_threshold {n : ℕ} (q : Fin n) : down (neg (threshold q)) = {q} := by
  ext t
  simp only [down, neg, threshold, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not, decide_eq_true_eq, Fin.val_castSucc, Fin.val_succ]
  constructor
  · rintro ⟨h1, h2⟩; exact Fin.ext (by omega)
  · rintro rfl; omega

private theorem down_neg_neg {n : ℕ} (f : W n) : neg (neg f) = f := by
  funext t; simp [neg]

private theorem down_driver_properties {n : ℕ} (i j k : Fin n) (hij : i < j) (hjk : j < k) :
    let middle := neg (threshold j)
    let driver := join (meet (threshold i) middle) (threshold k)
    down driver = {j} ∧ down (neg driver) = {i, k} ∧
    (down (neg driver)).card = 2 ∧
    driver ∉ raw n ∧ driver ≠ middle ∧ driver ≠ neg driver := by
  intro middle driver
  have hval : ∀ t : Fin (n + 1), driver t = decide ((i.val < t.val ∧ t.val ≤ j.val) ∨ k.val < t.val) := fun t => by
    dsimp only [driver, join, meet, threshold, middle, neg]
    by_cases h1 : i.val < t.val <;> by_cases h2 : j.val < t.val <;> by_cases h3 : k.val < t.val <;>
      simp [h1, h2, h3] <;> omega
  have hdd : down driver = {j} := by
    ext t
    simp only [down, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hval,
      decide_eq_true_eq, decide_eq_false_iff_not, Fin.val_castSucc, Fin.val_succ]
    constructor
    · rintro ⟨h1, h2⟩; exact Fin.ext (by omega)
    · rintro rfl; omega
  have hdn : down (neg driver) = {i, k} := by
    ext t
    simp only [down, neg, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, hval,
      Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, Fin.val_castSucc, Fin.val_succ]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hi : t.val = i.val
      · exact Or.inl (Fin.ext hi)
      · right; exact Fin.ext (by omega)
    · rintro (rfl | rfl) <;> omega
  have hcard : (down (neg driver)).card = 2 := by
    rw [hdn, Finset.card_pair (ne_of_lt (lt_trans hij hjk))]
  have hnr : driver ∉ raw n := fun h => by
    have := down_raw_empty driver h; rw [hdd] at this; exact Finset.singleton_ne_empty j this
  have hnm : driver ≠ middle := fun h => by
    have h0 : down (neg middle) = ∅ := by
      dsimp only [middle]; rw [down_neg_neg]
      exact down_raw_empty (threshold j) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
    have h1 : (down (neg middle)).card = 0 := by rw [h0]; simp
    rw [h] at hcard; omega
  have hnn : driver ≠ neg driver := fun h => by
    let z : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩
    have h1 := congrArg (fun f => f z) h
    dsimp only [neg] at h1; cases h2 : driver z <;> rw [h2] at h1 <;> cases h1
  exact ⟨hdd, hdn, hcard, hnr, hnm, hnn⟩

private def fitsClean {n : ℕ} (A : Finset (W n)) (b s : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : W n → ℕ),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
    C.output < n + 2 + C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ s ∧
    ∀ f ∈ A, tap f < n + 2 + C.size ∧ ∀ t : Fin (n + 1),
      (C.wires (inp t)).getD (tap f) false = f t

-- Helper: Ctx for building circuits cleanly
private def Ctx (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) ∧
  (∀ i < gs.length, ∀ w ∈ (gs.getD i ⟨.or, []⟩).inputs, w < n + 2 + i)

private theorem ctx_snoc (n : ℕ) (gs : List Gate) (g : Gate) (hctx : Ctx n gs)
    (hfan : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ w ∈ g.inputs, w < n + 2 + gs.length) :
    Ctx n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hctx.1 g' h1
    · rw [List.mem_singleton.mp h2]; exact hfan
  · intro i hi w hw
    rw [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < gs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hw
      exact hctx.2 i hlt w hw
    · have hieq : i = gs.length := by omega
      subst hieq
      have hge : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
      rw [hge] at hw
      exact hrb w hw

-- Part 1: fits 3 (A.card + 3)
private theorem part1_clean (n : ℕ) (i j k : Fin n)
    (A : Finset (W n))
    (hA : ∀ f ∈ A, (down f).card = 1 ∧ (down (neg f)).card = 1)
    (hbi : A.biUnion down = {i, j, k}) :
    fitsClean A 3 (A.card + 3) := by
  -- Base 3 NOT gates: neg(threshold i), neg(threshold j), neg(threshold k) at wires n+2, n+3, n+4
  let base : List Gate := [⟨.not, [i.val]⟩, ⟨.not, [j.val]⟩, ⟨.not, [k.val]⟩]
  have hbase_ctx : Ctx n base := by
    refine ⟨?_, ?_⟩
    · intro g hg; simp [base] at hg; rcases hg with rfl | rfl | rfl <;> simp
    · intro idx hidx w hw
      simp only [base, List.length_cons, List.length_nil] at hidx
      interval_cases idx <;> simp [base] at hw <;> subst hw <;> omega
  have hbase_not : PEqualNP.NotBracket.notCount ⟨base, 0⟩ = 3 := by simp [base, PEqualNP.NotBracket.notCount]
  have hbase_ev : ∀ t : Fin (n + 1),
      (run base (inp t)).getD (n + 2) false = neg (threshold i) t ∧
      (run base (inp t)).getD (n + 3) false = neg (threshold j) t ∧
      (run base (inp t)).getD (n + 4) false = neg (threshold k) t := by
    intro t
    have h0 := run_gate base (inp t) 0 (by simp [base])
    have h1 := run_gate base (inp t) 1 (by simp [base])
    have h2 := run_gate base (inp t) 2 (by simp [base])
    rw [inp_len] at h0 h1 h2
    simp only [base, List.getElem_cons_zero, List.getElem_cons_succ, List.map_cons, List.map_nil, notEval_cons, Nat.add_zero] at h0 h1 h2
    rw [if_pos (by omega), run_input base (inp t) i.val (by rw [inp_len]; omega), inp_getD_lt] at h0
    rw [if_pos (by omega), run_input base (inp t) j.val (by rw [inp_len]; omega), inp_getD_lt] at h1
    rw [if_pos (by omega), run_input base (inp t) k.val (by rw [inp_len]; omega), inp_getD_lt] at h2
    exact ⟨h0, h1, h2⟩
  -- Build one AND/OR gate for each f in any subset L ⊆ A
  have hbuild : ∀ (B : Finset (W n)), B ⊆ A →
      ∃ (gs : List Gate) (tap : W n → ℕ),
        (∃ ext, gs = base ++ ext) ∧
        Ctx n gs ∧
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ = 3 ∧
        gs.length = B.card + 3 ∧
        ∀ f ∈ B, tap f < n + 2 + gs.length ∧ ∀ t : Fin (n + 1), (run gs (inp t)).getD (tap f) false = f t := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨base, fun _ => 0, ⟨[], by simp⟩, hbase_ctx, hbase_not, by simp [base], by simp⟩
    | @insert f B' hfni ih =>
      intro hsub
      have hB' : B' ⊆ A := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hfA : f ∈ A := hsub (Finset.mem_insert_self f B')
      obtain ⟨gs1, tap1, ⟨ext1, hext1⟩, hctx1, hnot1, hlen1, hev1⟩ := ih hB'
      obtain ⟨hd1, hu1⟩ := hA f hfA
      obtain ⟨d, hd_eq⟩ := Finset.card_eq_one.mp hd1
      obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hu1
      have hd_ijk : d = i ∨ d = j ∨ d = k := by
        have hm : d ∈ A.biUnion down := Finset.mem_biUnion.mpr ⟨f, hfA, by rw [hd_eq]; exact Finset.mem_singleton_self d⟩
        rw [hbi] at hm; simpa [Finset.mem_insert, Finset.mem_singleton] using hm
      let dw : ℕ := if d = i then n + 2 else if d = j then n + 3 else n + 4
      have hdw_lt : dw < n + 2 + gs1.length := by
        have : base.length = 3 := rfl
        have : 3 ≤ gs1.length := by omega
        dsimp only [dw]; split_ifs <;> omega
      have hdw_ev : ∀ t : Fin (n + 1), (run gs1 (inp t)).getD dw false = neg (threshold d) t := by
        intro t
        have hpref : ∀ w < n + 2 + base.length, (run gs1 (inp t)).getD w false = (run base (inp t)).getD w false := fun w hw => by
          rw [hext1]; exact run_prefix base ext1 (inp t) w (by rw [inp_len]; exact hw)
        rcases hd_ijk with hdi | hdj | hdk
        · dsimp only [dw]; rw [if_pos hdi, hdi, hpref (n + 2) (by simp [base])]; exact (hbase_ev t).1
        · by_cases hji : j = i
          · dsimp only [dw]; rw [hdj, if_pos hji, hji, hpref (n + 2) (by simp [base])]; exact (hbase_ev t).1
          · dsimp only [dw]; rw [hdj, if_neg hji, if_pos rfl, hpref (n + 3) (by simp [base])]; exact (hbase_ev t).2.1
        · by_cases hki : k = i
          · dsimp only [dw]; rw [hdk, if_pos hki, hki, hpref (n + 2) (by simp [base])]; exact (hbase_ev t).1
          · by_cases hkj : k = j
            · dsimp only [dw]; rw [hdk, if_neg hki, if_pos hkj, hkj, hpref (n + 3) (by simp [base])]; exact (hbase_ev t).2.1
            · dsimp only [dw]; rw [hdk, if_neg hki, if_neg hkj, hpref (n + 4) (by simp [base])]; exact (hbase_ev t).2.2
      obtain ⟨hchar_lt, hchar_gt, hne⟩ := interval_char f d u hd_eq hu_eq
      let g : Gate := if u < d then ⟨.and, [u.val, dw]⟩ else ⟨.or, [u.val, dw]⟩
      let gs2 := gs1 ++ [g]
      let tap2 : W n → ℕ := fun x => if x = f then n + 2 + gs1.length else tap1 x
      have hctx2 : Ctx n gs2 := ctx_snoc n gs1 g hctx1
        (by dsimp only [g]; split_ifs <;> simp)
        (by intro w hw; dsimp only [g] at hw; split_ifs at hw <;> simp at hw <;> rcases hw with rfl | rfl <;> omega)
      have hnot2 : PEqualNP.NotBracket.notCount ⟨gs2, 0⟩ = 3 := by
        dsimp only [gs2]; rw [notCount_snoc]; dsimp only [g]; split_ifs <;> simpa using hnot1
      refine ⟨gs2, tap2, ⟨ext1 ++ [g], by simp [gs2, hext1, List.append_assoc]⟩, hctx2, hnot2,
        by dsimp only [gs2]; rw [List.length_append, List.length_singleton, hlen1, Finset.card_insert_of_notMem hfni], ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxB'
      · refine ⟨by dsimp only [tap2, gs2]; rw [if_pos rfl, List.length_append, List.length_singleton]; omega, ?_⟩
        intro t
        dsimp only [tap2]; rw [if_pos rfl]
        dsimp only [gs2]; rw [run_snoc]
        have hrlen : (run gs1 (inp t)).length = n + 2 + gs1.length := by rw [run_length, inp_len]
        rw [← hrlen, getD_eq]
        have hu_ev : (run gs1 (inp t)).getD u.val false = threshold u t := by
          rw [run_input gs1 (inp t) u.val (by rw [inp_len]; omega), inp_getD_lt]
        by_cases hlt : u < d
        · dsimp only [g]; rw [if_pos hlt, andEval]
          simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hu_ev, hdw_ev t]
          rw [hchar_lt hlt]; rfl
        · have hgt : d < u := lt_of_le_of_ne (not_lt.mp hlt) hne.symm
          dsimp only [g]; rw [if_neg hlt, orEval]
          simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hu_ev, hdw_ev t]
          rw [hchar_gt hgt]; rfl
      · have hne' : x ≠ f := fun h => hfni (h ▸ hxB')
        obtain ⟨hw1, he1⟩ := hev1 x hxB'
        refine ⟨by dsimp only [tap2, gs2]; rw [if_neg hne', List.length_append, List.length_singleton]; omega, ?_⟩
        intro t
        dsimp only [tap2]; rw [if_neg hne']
        dsimp only [gs2]; rw [run_prefix gs1 [g] (inp t) (tap1 x) (by rw [inp_len]; exact hw1)]
        exact he1 t
  obtain ⟨gs, tap, _, hctx, hnot, hlen, hev⟩ := hbuild A (Finset.Subset.refl A)
  refine ⟨⟨gs, 0⟩, tap, ?_, ?_, by dsimp [Circuit.size]; omega, by rw [hnot], by dsimp [Circuit.size]; omega, hev⟩
  · intro g hg; obtain ⟨ho, hl⟩ := hctx.1 g hg
    exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩
  · intro idx hidx w hw
    dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hw
    rw [List.getD_eq_getElem _ _ hidx] at hw
    exact hctx.2 idx hidx w (by rw [List.getD_eq_getElem _ _ hidx]; exact hw)

-- Helper: monotone iteration of step
private def stepFun {n : ℕ} (driver : W n) (allow : Finset (W n)) (B : Finset (W n)) : Finset (W n) :=
  let pairs := B.product B
  let positive := (pairs.image (fun z => meet z.1 z.2)) ∪ (pairs.image (fun z => join z.1 z.2))
  (B ∪ (allow ∩ positive)) ∪ (if driver ∈ B then {neg driver} else ∅)

private theorem sub_stepFun {n : ℕ} (driver : W n) (allow B : Finset (W n)) :
    B ⊆ stepFun driver allow B := by
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

private theorem stepFun_mono {n : ℕ} (driver : W n) (allow : Finset (W n)) {B1 B2 : Finset (W n)}
    (h : B1 ⊆ B2) : stepFun driver allow B1 ⊆ stepFun driver allow B2 := by
  intro x hx
  dsimp only [stepFun] at hx ⊢
  rcases Finset.mem_union.mp hx with h1 | h2
  · refine Finset.mem_union_left _ ?_
    rcases Finset.mem_union.mp h1 with ha | hb
    · exact Finset.mem_union_left _ (h ha)
    · refine Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hb).1, ?_⟩)
      rcases Finset.mem_union.mp (Finset.mem_inter.mp hb).2 with hm | hj
      · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hm
        obtain ⟨ha', hb'⟩ := Finset.mem_product.mp hab
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨h ha', h hb'⟩, rfl⟩)
      · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hj
        obtain ⟨ha', hb'⟩ := Finset.mem_product.mp hab
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨h ha', h hb'⟩, rfl⟩)
  · refine Finset.mem_union_right _ ?_
    split_ifs at h2 with hd
    · rw [if_pos (h hd)]; exact h2
    · simp at h2

private theorem iterate_stepFun_mono {n : ℕ} (driver : W n) (allow B : Finset (W n))
    {m1 m2 : ℕ} (hle : m1 ≤ m2) :
    (stepFun driver allow)^[m1] B ⊆ (stepFun driver allow)^[m2] B := by
  induction hle with
  | refl => exact Finset.Subset.refl _
  | @step m _ ih =>
    rw [Function.iterate_succ_apply']
    exact Finset.Subset.trans ih (sub_stepFun driver allow _)

-- Part 2 (←): reachability → fits 2 (A.card + 3 + s)
set_option maxHeartbeats 800000 in
private theorem part2_bwd (n : ℕ) (i j k : Fin n) (hij : i < j) (hjk : j < k)
    (A : Finset (W n)) (s : ℕ) (E : Finset (W n)) (hEs : E.card ≤ s)
    (hreach :
      let middle := neg (threshold j)
      let driver := join (meet (threshold i) middle) (threshold k)
      let allow := insert driver (A ∪ E)
      let reachable := (stepFun driver allow)^[A.card + s + 3] (insert middle (raw n))
      A ⊆ reachable ∧ driver ∈ reachable) :
    fitsClean A 2 (A.card + 3 + s) := by
  let middle : W n := neg (threshold j)
  let driver : W n := join (meet (threshold i) middle) (threshold k)
  let allow : Finset (W n) := insert driver (A ∪ E)
  let B0 : Finset (W n) := insert middle (raw n)
  let step := stepFun driver allow
  -- Maintain: gs with distinct outputs in B \ raw, all NOT gates only for middle or neg driver
  let wf : List Gate → ℕ → W n := fun gs w t => (run gs (inp t)).getD w false
  let Good (B : Finset (W n)) (gs : List Gate) : Prop :=
    Ctx n gs ∧
    (∀ f ∈ B, ∃ w < n + 2 + gs.length, wf gs w = f) ∧
    (∀ idx < gs.length, wf gs (n + 2 + idx) ∈ B \ raw n) ∧
    (∀ idx1 < gs.length, ∀ idx2 < gs.length, wf gs (n + 2 + idx1) = wf gs (n + 2 + idx2) → idx1 = idx2) ∧
    (∀ idx < gs.length, (gs.getD idx ⟨.or, []⟩).op = .not →
      wf gs (n + 2 + idx) = middle ∨ wf gs (n + 2 + idx) = neg driver)
  have hmid_nr : middle ∉ raw n := fun h => by
    have := down_raw_empty middle h; rw [down_neg_threshold j] at this; exact Finset.singleton_ne_empty j this
  have hbase : Good B0 [⟨.not, [j.val]⟩] := by
    have hctx0 : Ctx n [⟨.not, [j.val]⟩] := ⟨by intro g hg; simp at hg; subst hg; simp,
      by intro idx hidx w hw; simp at hidx; subst hidx; simp at hw; subst hw; omega⟩
    have hmid_ev : wf [⟨.not, [j.val]⟩] (n + 2) = middle := by
      funext t; dsimp only [wf]
      have hrg := run_gate [⟨.not, [j.val]⟩] (inp t) 0 (by simp)
      rw [inp_len] at hrg; simp only [Nat.add_zero, List.getElem_cons_zero, List.map_cons, List.map_nil, notEval_cons] at hrg
      rw [hrg, if_pos (by omega), run_input _ _ j.val (by rw [inp_len]; omega), inp_getD_lt]; rfl
    refine ⟨hctx0, ?_, ?_, ?_, ?_⟩
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hraw
      · exact ⟨n + 2, by simp, hmid_ev⟩
      · simp only [raw, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hraw
        rcases hraw with rfl | rfl | ⟨q, rfl⟩
        · exact ⟨n, by simp, by funext t; dsimp [wf]; rw [run_input _ _ n (by rw [inp_len]; omega), inp_getD_false]⟩
        · exact ⟨n + 1, by simp, by funext t; dsimp [wf]; rw [run_input _ _ (n + 1) (by rw [inp_len]; omega), inp_getD_true]⟩
        · exact ⟨q.val, by simp; omega, by funext t; dsimp [wf]; rw [run_input _ _ q.val (by rw [inp_len]; omega), inp_getD_lt]⟩
    · intro idx hidx
      simp only [List.length_singleton] at hidx
      rcases Nat.lt_one_iff.mp hidx with rfl
      exact Finset.mem_sdiff.mpr ⟨by rw [hmid_ev]; exact Finset.mem_insert_self _ _, by rw [hmid_ev]; exact hmid_nr⟩
    · intro i1 hi1 i2 hi2 _; simp at hi1 hi2; omega
    · intro idx hidx _
      simp only [List.length_singleton] at hidx
      rcases Nat.lt_one_iff.mp hidx with rfl
      left; exact hmid_ev
  -- Adding one positive gate for f ∈ positive B \ B preserves Good (insert f B)
  have hadd_pos : ∀ (B : Finset (W n)) (gs : List Gate), Good B gs →
      ∀ f, f ∉ B → raw n ⊆ B →
      (∃ a ∈ B, ∃ b ∈ B, f = meet a b ∨ f = join a b) →
      ∃ gs', Good (insert f B) gs' := by
    intro B gs ⟨hctx, hcov, hmem, hinj, hnot⟩ f hfni hrawB ⟨a, ha, b, hb, hfab⟩
    obtain ⟨wa, hwa, hwa_ev⟩ := hcov a ha
    obtain ⟨wb, hwb, hwb_ev⟩ := hcov b hb
    let g : Gate := if f = meet a b then ⟨.and, [wa, wb]⟩ else ⟨.or, [wa, wb]⟩
    let gs' := gs ++ [g]
    have hctx' : Ctx n gs' := ctx_snoc n gs g hctx
      (by dsimp [g]; split_ifs <;> simp)
      (by intro w hw; dsimp [g] at hw; split_ifs at hw <;> simp at hw <;> rcases hw with rfl | rfl <;> omega)
    have hpref : ∀ w < n + 2 + gs.length, wf gs' w = wf gs w := fun w hw => by
      funext t; dsimp only [wf, gs']; exact run_prefix gs [g] (inp t) w (by rw [inp_len]; exact hw)
    have hnew : wf gs' (n + 2 + gs.length) = f := by
      funext t; dsimp only [wf, gs']; rw [run_snoc]
      have hrlen : (run gs (inp t)).length = n + 2 + gs.length := by rw [run_length, inp_len]
      rw [← hrlen, getD_eq]
      by_cases hm : f = meet a b
      · dsimp only [g]; rw [if_pos hm, andEval]
        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have ea : (run gs (inp t)).getD wa false = a t := congrFun hwa_ev t
        have eb : (run gs (inp t)).getD wb false = b t := congrFun hwb_ev t
        rw [ea, eb, hm]; rfl
      · have hj : f = join a b := hfab.resolve_left hm
        dsimp only [g]; rw [if_neg hm, orEval]
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        have ea : (run gs (inp t)).getD wa false = a t := congrFun hwa_ev t
        have eb : (run gs (inp t)).getD wb false = b t := congrFun hwb_ev t
        rw [ea, eb, hj]; rfl
    refine ⟨gs', hctx', ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxB
      · exact ⟨n + 2 + gs.length, by simp [gs'], hnew⟩
      · obtain ⟨w, hw, hev⟩ := hcov x hxB
        exact ⟨w, by simp [gs']; omega, (hpref w hw).trans hev⟩
    · intro idx hidx
      simp only [gs', List.length_append, List.length_singleton] at hidx
      by_cases hlt : idx < gs.length
      · rw [hpref (n + 2 + idx) (by omega)]
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp (hmem idx hlt)
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem h1, h2⟩
      · have hidx_eq : idx = gs.length := by omega
        subst hidx_eq
        rw [hnew]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, fun hr => hfni (hrawB hr)⟩
    · intro i1 hi1 i2 hi2 heq
      simp only [gs', List.length_append, List.length_singleton] at hi1 hi2
      by_cases h1 : i1 < gs.length <;> by_cases h2 : i2 < gs.length
      · rw [hpref _ (by omega), hpref _ (by omega)] at heq; exact hinj i1 h1 i2 h2 heq
      · have hi2_eq : i2 = gs.length := by omega
        subst hi2_eq
        rw [hpref _ (by omega), hnew] at heq
        exact absurd (heq ▸ (Finset.mem_sdiff.mp (hmem i1 h1)).1) hfni
      · have hi1_eq : i1 = gs.length := by omega
        subst hi1_eq
        rw [hnew, hpref (n + 2 + i2) (by omega)] at heq
        exact absurd (heq.symm ▸ (Finset.mem_sdiff.mp (hmem i2 h2)).1) hfni
      · omega
    · intro idx hidx hop
      simp only [gs', List.length_append, List.length_singleton] at hidx
      by_cases hlt : idx < gs.length
      · rw [hpref _ (by omega)]
        have hgd : gs'.getD idx ⟨.or, []⟩ = gs.getD idx ⟨.or, []⟩ := by
          dsimp only [gs']; rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
        rw [hgd] at hop; exact hnot idx hlt hop
      · have hidx_eq : idx = gs.length := by omega
        subst hidx_eq
        have hgd : gs'.getD gs.length ⟨.or, []⟩ = g := by
          dsimp only [gs']; rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
        rw [hgd] at hop; dsimp only [g] at hop; split_ifs at hop <;> cases hop
  -- Build Good for step^[r] B0 by induction on r
  have hstep_good : ∀ r, ∃ gs, Good (step^[r] B0) gs := by
    intro r
    induction r with
    | zero => exact ⟨[⟨.not, [j.val]⟩], hbase⟩
    | succ r ih =>
      obtain ⟨gs1, hg1⟩ := ih
      set B := step^[r] B0
      have hrawB : raw n ⊆ B := Finset.Subset.trans (Finset.subset_insert _ _)
        (iterate_stepFun_mono driver allow B0 (Nat.zero_le r))
      -- First add all new positive elements in (allow ∩ positive B) \ B one by one
      let pairs := B.product B
      let posB := (pairs.image (fun z => meet z.1 z.2)) ∪ (pairs.image (fun z => join z.1 z.2))
      let toAdd := (allow ∩ posB) \ B
      have hadd_all : ∀ (S : Finset (W n)), S ⊆ toAdd → ∃ gs, Good (B ∪ S) gs := by
        intro S
        induction S using Finset.induction_on with
        | empty => intro _; simpa using ⟨gs1, hg1⟩
        | @insert f S' hfni ihS =>
          intro hSsub
          obtain ⟨gsS, hgS⟩ := ihS (fun x hx => hSsub (Finset.mem_insert_of_mem hx))
          have hf_toAdd : f ∈ toAdd := hSsub (Finset.mem_insert_self f S')
          have hf_niB : f ∉ B := (Finset.mem_sdiff.mp hf_toAdd).2
          have hf_ni : f ∉ B ∪ S' := by simp [hf_niB, hfni]
          have hf_pos : f ∈ posB := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hf_toAdd).1).2
          have hex : ∃ a ∈ B ∪ S', ∃ b ∈ B ∪ S', f = meet a b ∨ f = join a b := by
            rcases Finset.mem_union.mp hf_pos with hm | hj
            · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hm
              obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
              exact ⟨a, Finset.mem_union_left _ ha, b, Finset.mem_union_left _ hb, Or.inl rfl⟩
            · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hj
              obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
              exact ⟨a, Finset.mem_union_left _ ha, b, Finset.mem_union_left _ hb, Or.inr rfl⟩
          obtain ⟨gs', hg'⟩ := hadd_pos (B ∪ S') gsS hgS f hf_ni (Finset.Subset.trans hrawB Finset.subset_union_left) hex
          refine ⟨gs', ?_⟩
          rwa [Finset.union_insert]
      obtain ⟨gs2, hg2⟩ := hadd_all toAdd (Finset.Subset.refl toAdd)
      have hB2_eq : B ∪ toAdd = B ∪ (allow ∩ posB) := by ext x; simp [toAdd]
      rw [hB2_eq] at hg2
      rw [Function.iterate_succ_apply']
      dsimp only [step, stepFun]
      change ∃ gs, Good ((B ∪ (allow ∩ posB)) ∪ (if driver ∈ B then {neg driver} else ∅)) gs
      by_cases hdrv : driver ∈ B
      · rw [if_pos hdrv]
        by_cases hndrv : neg driver ∈ B ∪ (allow ∩ posB)
        · refine ⟨gs2, ?_⟩
          have heq : (B ∪ (allow ∩ posB)) ∪ {neg driver} = B ∪ (allow ∩ posB) := by
            ext x; simp [hndrv]
          rwa [heq]
        · obtain ⟨hctx2, hcov2, hmem2, hinj2, hnot2⟩ := hg2
          obtain ⟨wd, hwd, hwd_ev⟩ := hcov2 driver (Finset.mem_union_left _ hdrv)
          let gnot : Gate := ⟨.not, [wd]⟩
          let gs3 := gs2 ++ [gnot]
          have hctx3 : Ctx n gs3 := ctx_snoc n gs2 gnot hctx2 ⟨Or.inr (Or.inr rfl), by simp [gnot]⟩
            (by intro w hw; simp [gnot] at hw; subst hw; exact hwd)
          have hpref : ∀ w < n + 2 + gs2.length, wf gs3 w = wf gs2 w := fun w hw => by
            funext t; dsimp only [wf, gs3]; exact run_prefix gs2 [gnot] (inp t) w (by rw [inp_len]; exact hw)
          have hnew : wf gs3 (n + 2 + gs2.length) = neg driver := by
            funext t; dsimp only [wf, gs3]; rw [run_snoc]
            have hrlen : (run gs2 (inp t)).length = n + 2 + gs2.length := by rw [run_length, inp_len]
            rw [← hrlen, getD_eq, List.map_cons, List.map_nil, notEval_cons]
            exact congrArg (! ·) (congrFun hwd_ev t)
          have hnd_nr : neg driver ∉ raw n := fun h => by
            have := down_raw_empty (neg driver) h
            have hc := (down_driver_properties i j k hij hjk).2.2.1
            rw [this] at hc; simp at hc
          have hun_eq : (B ∪ (allow ∩ posB)) ∪ {neg driver} = insert (neg driver) (B ∪ (allow ∩ posB)) := by
            ext x; simp [or_comm]
          rw [hun_eq]
          refine ⟨gs3, hctx3, ?_, ?_, ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx2
            · exact ⟨n + 2 + gs2.length, by simp [gs3], hnew⟩
            · obtain ⟨w, hw, hev⟩ := hcov2 x hx2
              exact ⟨w, by simp [gs3]; omega, (hpref w hw).trans hev⟩
          · intro idx hidx
            simp only [gs3, List.length_append, List.length_singleton] at hidx
            by_cases hlt : idx < gs2.length
            · rw [hpref _ (by omega)]
              obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp (hmem2 idx hlt)
              exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem h1, h2⟩
            · have hidx_eq : idx = gs2.length := by omega
              subst hidx_eq
              rw [hnew]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, hnd_nr⟩
          · intro i1 hi1 i2 hi2 heq
            simp only [gs3, List.length_append, List.length_singleton] at hi1 hi2
            by_cases h1 : i1 < gs2.length <;> by_cases h2 : i2 < gs2.length
            · rw [hpref _ (by omega), hpref _ (by omega)] at heq; exact hinj2 i1 h1 i2 h2 heq
            · have hi2_eq : i2 = gs2.length := by omega
              subst hi2_eq
              rw [hpref _ (by omega), hnew] at heq
              exact absurd (heq ▸ (Finset.mem_sdiff.mp (hmem2 i1 h1)).1) hndrv
            · have hi1_eq : i1 = gs2.length := by omega
              subst hi1_eq
              rw [hnew, hpref (n + 2 + i2) (by omega)] at heq
              exact absurd (heq.symm ▸ (Finset.mem_sdiff.mp (hmem2 i2 h2)).1) hndrv
            · omega
          · intro idx hidx hop
            simp only [gs3, List.length_append, List.length_singleton] at hidx
            by_cases hlt : idx < gs2.length
            · rw [hpref _ (by omega)]
              have hgd : gs3.getD idx ⟨.or, []⟩ = gs2.getD idx ⟨.or, []⟩ := by
                dsimp only [gs3]; rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
              rw [hgd] at hop; exact hnot2 idx hlt hop
            · have hidx_eq : idx = gs2.length := by omega
              subst hidx_eq
              right; exact hnew
      · rw [if_neg hdrv, Finset.union_empty]; exact ⟨gs2, hg2⟩
  -- Also prove every element of step^[r] B0 \ raw n lies in insert middle (insert (neg driver) allow)
  have hreach_sub : ∀ r, (step^[r] B0) \ raw n ⊆ insert middle (insert (neg driver) allow) := by
    intro r
    induction r with
    | zero =>
      intro x hx
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_insert.mp h1 with rfl | hraw
      · exact Finset.mem_insert_self _ _
      · exact absurd hraw h2
    | succ r ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
      dsimp only [step, stepFun] at h1
      rcases Finset.mem_union.mp h1 with ha | hb
      · rcases Finset.mem_union.mp ha with ha1 | ha2
        · exact ih (Finset.mem_sdiff.mpr ⟨ha1, h2⟩)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_inter.mp ha2).1)
      · split_ifs at hb with hd
        · rw [Finset.mem_singleton.mp hb]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · simp at hb
  obtain ⟨gs, hctx, hcov, hmem, hinj, hnot⟩ := hstep_good (A.card + s + 3)
  have hgs_len : gs.length ≤ A.card + 3 + s := by
    have hcard_le : gs.length ≤ (insert middle (insert (neg driver) allow)).card := by
      have h1 := Finset.card_le_card_of_injOn (s := Finset.range gs.length)
        (fun idx => wf gs (n + 2 + idx))
        (fun idx hidx => hreach_sub _ (hmem idx (Finset.mem_range.mp hidx)))
        (fun a ha b hb heq => hinj a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb) heq)
      simpa using h1
    have hallow_le : allow.card ≤ A.card + s + 1 := by
      calc allow.card ≤ (A ∪ E).card + 1 := Finset.card_insert_le _ _
        _ ≤ A.card + E.card + 1 := by have := Finset.card_union_le A E; omega
        _ ≤ A.card + s + 1 := by omega
    have h2 : (insert middle (insert (neg driver) allow)).card ≤ allow.card + 2 := by
      have ha := Finset.card_insert_le middle (insert (neg driver) allow)
      have hb := Finset.card_insert_le (neg driver) allow
      omega
    omega
  have hgs_not : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ 2 := by
    let _ : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
    have hnc : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ =
        ((Finset.range gs.length).filter (fun idx => (gs.getD idx ⟨.or, []⟩).op = .not)).card := by
      have hnd : ((List.range gs.length).filter (fun idx => decide ((gs.getD idx ⟨.or, []⟩).op = .not))).Nodup :=
        List.Nodup.filter _ List.nodup_range
      have h1 : ((Finset.range gs.length).filter (fun idx => (gs.getD idx ⟨.or, []⟩).op = .not)).card =
          ((List.range gs.length).filter (fun idx => decide ((gs.getD idx ⟨.or, []⟩).op = .not))).length := by
        rw [← List.toFinset_card_of_nodup hnd]; congr 1; ext idx; simp
      rw [h1]
      dsimp only [PEqualNP.NotBracket.notCount]
      have hlen : ∀ (L : List Gate), ((List.range L.length).filter (fun idx => decide ((L.getD idx ⟨.or, []⟩).op = .not))).length =
          (L.filter (fun g => decide (g.op = .not))).length := by
        intro L; induction L using List.reverseRecOn with
        | nil => simp
        | append_singleton xs g ihL =>
          rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append, List.filter_append,
            List.length_append, List.length_append]
          have ha : (List.range xs.length).filter (fun idx => decide (((xs ++ [g]).getD idx ⟨.or, []⟩).op = .not)) =
              (List.range xs.length).filter (fun idx => decide ((xs.getD idx ⟨.or, []⟩).op = .not)) := by
            apply List.filter_congr; intro idx hi
            have hilt := List.mem_range.mp hi
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt, ← List.getD_eq_getElem?_getD]
          have hb : ([xs.length].filter (fun idx => decide (((xs ++ [g]).getD idx ⟨.or, []⟩).op = .not))).length =
              ([g].filter (fun g' => decide (g'.op = .not))).length := by
            have hgd : (xs ++ [g]).getD xs.length ⟨.or, []⟩ = g := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
            cases h : g.op <;> simp [hgd, h]
          rw [ha, ihL, hb]
      exact (hlen gs).symm
    rw [hnc]
    have hle := Finset.card_le_card_of_injOn
      (s := (Finset.range gs.length).filter (fun idx => (gs.getD idx ⟨.or, []⟩).op = .not))
      (t := ({middle, neg driver} : Finset (W n)))
      (fun idx => wf gs (n + 2 + idx))
      (fun idx hidx => by
        dsimp only
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hidx
        rcases hnot idx (Finset.mem_range.mp h1) h2 with hm | hn
        · rw [hm]; exact Finset.mem_insert_self _ _
        · rw [hn]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      (fun a ha b hb heq => hinj a (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
        b (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) heq)
    have h2 : ({middle, neg driver} : Finset (W n)).card ≤ 2 := Finset.card_le_two
    omega
  have hA_cov : ∀ f ∈ A, ∃ w < n + 2 + gs.length, wf gs w = f := fun f hf => hcov f (hreach.1 hf)
  let tap : W n → ℕ := fun f => if h : f ∈ A then (hA_cov f h).choose else 0
  refine ⟨⟨gs, 0⟩, tap, ?_, ?_, by dsimp [Circuit.size]; omega, hgs_not, by dsimp [Circuit.size]; omega, ?_⟩
  · intro g hg; obtain ⟨ho, hl⟩ := hctx.1 g hg
    exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩
  · intro idx hidx w hw
    dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hw
    rw [List.getD_eq_getElem _ _ hidx] at hw
    exact hctx.2 idx hidx w (by rw [List.getD_eq_getElem _ _ hidx]; exact hw)
  · intro f hf
    dsimp only [tap]; rw [dif_pos hf]
    obtain ⟨hw, hev⟩ := (hA_cov f hf).choose_spec
    exact ⟨hw, fun t => congrFun hev t⟩

-- Part 2 (→): fits 2 (A.card + 3 + s) → ∃ E, E.card ≤ s ∧ A ⊆ reachable ∧ driver ∈ reachable
set_option maxHeartbeats 1000000 in
private theorem part2_fwd (n : ℕ) (i j k : Fin n) (hij : i < j) (hjk : j < k)
    (A : Finset (W n))
    (hA : ∀ f ∈ A, (down f).card = 1 ∧ (down (neg f)).card = 1)
    (hbi : A.biUnion down = {i, j, k})
    (s : ℕ) (hfits : fitsClean A 2 (A.card + 3 + s)) :
    let middle := neg (threshold j)
    let driver := join (meet (threshold i) middle) (threshold k)
    ∃ E : Finset (W n), E.card ≤ s ∧
      let allow := insert driver (A ∪ E)
      let reachable := (stepFun driver allow)^[A.card + s + 3] (insert middle (raw n))
      A ⊆ reachable ∧ driver ∈ reachable := by
  let _ : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  let middle : W n := neg (threshold j)
  let driver : W n := join (meet (threshold i) middle) (threshold k)
  obtain ⟨C, tap, hfan, hrb, _hout, hnot_le, hsz_le, htap⟩ := hfits
  let wf : ℕ → W n := fun w t => (run C.gates (inp t)).getD w false
  let op : ℕ → GateOp := fun idx => (C.gates.getD idx ⟨.or, []⟩).op
  let notList : List ℕ := (List.range C.size).filter (fun idx => decide (op idx = .not))
  have hnotList_len : notList.length = PEqualNP.NotBracket.notCount C := by
    dsimp only [notList, PEqualNP.NotBracket.notCount, Circuit.size]
    have hlen : ∀ (L : List Gate), ((List.range L.length).filter (fun idx => decide ((L.getD idx ⟨.or, []⟩).op = .not))).length =
        (L.filter (fun g => decide (g.op = .not))).length := by
      intro L; induction L using List.reverseRecOn with
      | nil => simp
      | append_singleton xs g ihL =>
        rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append, List.filter_append,
          List.length_append, List.length_append]
        have ha : (List.range xs.length).filter (fun idx => decide (((xs ++ [g]).getD idx ⟨.or, []⟩).op = .not)) =
            (List.range xs.length).filter (fun idx => decide ((xs.getD idx ⟨.or, []⟩).op = .not)) := by
          apply List.filter_congr; intro idx hi
          have hilt := List.mem_range.mp hi
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hilt, ← List.getD_eq_getElem?_getD]
        have hb : ([xs.length].filter (fun idx => decide (((xs ++ [g]).getD idx ⟨.or, []⟩).op = .not))).length =
            ([g].filter (fun g' => decide (g'.op = .not))).length := by
          have hgd : (xs ++ [g]).getD xs.length ⟨.or, []⟩ = g := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]; simp
          cases h : g.op <;> simp [hgd, h]
        rw [ha, ihL, hb]
    exact hlen C.gates
  -- Monotonicity propagation on any step t0 → t1 where no NOT gate falls
  have hmono_step : ∀ (t0 t1 : Fin (n + 1)), t0.val ≤ t1.val →
      ∀ (m : ℕ), m ≤ C.gates.length →
      (∀ idx < m, op idx = .not → wf (n + 2 + idx) t0 = true → wf (n + 2 + idx) t1 = true) →
      ∀ w < n + 2 + m, wf w t0 = true → wf w t1 = true := by
    intro t0 t1 ht01 m hm hnot w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hwt0
      by_cases hwin : w < n + 2
      · dsimp only [wf] at hwt0 ⊢
        rw [run_input C.gates (inp t0) w (by rw [inp_len]; exact hwin)] at hwt0
        rw [run_input C.gates (inp t1) w (by rw [inp_len]; exact hwin)]
        by_cases hwn : w < n
        · rw [inp_getD_lt t0 ⟨w, hwn⟩] at hwt0; rw [inp_getD_lt t1 ⟨w, hwn⟩]
          dsimp only [threshold] at hwt0 ⊢; simp only [decide_eq_true_eq] at hwt0 ⊢; omega
        · rcases (show w = n ∨ w = n + 1 by omega) with hwn1 | hwn2
          · rw [hwn1, inp_getD_false] at hwt0; cases hwt0
          · rw [hwn2, inp_getD_true]
      · let idx := w - (n + 2)
        have hw_eq : w = n + 2 + idx := by omega
        have hidx_lt : idx < m := by omega
        have hidxC : idx < C.gates.length := by omega
        rw [hw_eq] at hwt0 ⊢
        have hg_eq : C.gates[idx] = C.gates.getD idx ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hidxC).symm
        have hop_eq : (C.gates[idx]).op = op idx := congrArg Gate.op hg_eq
        rcases (hfan _ (List.getElem_mem hidxC)).1 with hand | hor | hnot'
        · have rg0 := run_gate C.gates (inp t0) idx hidxC
          have rg1 := run_gate C.gates (inp t1) idx hidxC
          rw [inp_len, hand, andEval] at rg0 rg1
          dsimp only [wf] at hwt0 ⊢; rw [rg0, List.all_eq_true] at hwt0; rw [rg1, List.all_eq_true]
          intro b' hb'; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb'
          have hqlt : q < n + 2 + idx := hrb idx hidxC q (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hidxC]; exact hq)
          have hbt := hwt0 _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
          simp only [id_eq, if_pos hqlt] at hbt ⊢
          exact ih q (by omega) (by omega) hbt
        · have rg0 := run_gate C.gates (inp t0) idx hidxC
          have rg1 := run_gate C.gates (inp t1) idx hidxC
          rw [inp_len, hor, orEval] at rg0 rg1
          dsimp only [wf] at hwt0 ⊢; rw [rg0, List.any_eq_true] at hwt0; rw [rg1, List.any_eq_true]
          obtain ⟨b', hb', hbt⟩ := hwt0; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb'
          have hqlt : q < n + 2 + idx := hrb idx hidxC q (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hidxC]; exact hq)
          simp only [id_eq, if_pos hqlt] at hbt
          refine ⟨if q < n + 2 + idx then (run C.gates (inp t1)).getD q false else false, List.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
          simp only [id_eq, if_pos hqlt]
          exact ih q (by omega) (by omega) hbt
        · exact hnot idx hidx_lt (hop_eq.symm.trans hnot') hwt0
  -- Helper: any wire w has down (wf w) ⊆ biUnion of down over NOT gates
  have hdown_sub : ∀ (w : ℕ), w < n + 2 + C.size → ∀ t : Fin n, t ∈ down (wf w) →
      ∃ idx < C.gates.length, op idx = .not ∧ t ∈ down (wf (n + 2 + idx)) := by
    intro w hw t ht
    by_contra hnone
    push_neg at hnone
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp ht
    have h3 := hmono_step t.castSucc t.succ (by simp) C.gates.length le_rfl
      (fun idx hidx hop ht1 => by
        by_contra hnottrue
        have ht2 : wf (n + 2 + idx) t.succ = false := by cases h : wf (n + 2 + idx) t.succ <;> [rfl; exact absurd h hnottrue]
        exact hnone idx hidx hop (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht1, ht2⟩))
      w hw h1
    rw [h2] at h3; cases h3
  have hijk_card : ({i, j, k} : Finset (Fin n)).card = 3 := by
    have hij' : i ≠ j := ne_of_lt hij
    have hik' : i ≠ k := ne_of_lt (lt_trans hij hjk)
    have hjk' : j ≠ k := ne_of_lt hjk
    rw [Finset.card_insert_of_notMem (by simp [hij', hik']), Finset.card_pair hjk']
  -- Show every t ∈ {i, j, k} is a fall of some NOT gate
  have hijk_in_not : ∀ t ∈ ({i, j, k} : Finset (Fin n)),
      ∃ idx < C.gates.length, op idx = .not ∧ t ∈ down (wf (n + 2 + idx)) := by
    intro t ht
    rw [← hbi] at ht
    obtain ⟨f, hfA, htf⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨hwf, hevf⟩ := htap f hfA
    have hfeq : wf (tap f) = f := funext hevf
    rw [← hfeq] at htf
    exact hdown_sub (tap f) hwf t htf
  -- Show notList.length = 2
  have hnot_antitone_first : ∀ idx < C.gates.length, op idx = .not →
      (∀ idx' < idx, op idx' ≠ .not) → (down (wf (n + 2 + idx))).card ≤ 1 := by
    intro idx hidx hop hfirst
    -- Input to idx is monotone, so wf (n+2+idx) is antitone!
    have hanti : ∀ (t0 t1 : Fin (n + 1)), t0.val ≤ t1.val →
        wf (n + 2 + idx) t1 = true → wf (n + 2 + idx) t0 = true := by
      intro t0 t1 ht01 h1
      have hg_eq : C.gates[idx] = C.gates.getD idx ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hidx).symm
      have hop' : (C.gates[idx]).op = .not := (congrArg Gate.op hg_eq).trans hop
      have rg0 := run_gate C.gates (inp t0) idx hidx
      have rg1 := run_gate C.gates (inp t1) idx hidx
      simp only [inp_len, hop'] at rg0 rg1
      dsimp only [wf] at h1 ⊢; rw [rg1] at h1; rw [rg0]
      rcases hin : (C.gates[idx]).inputs with _ | ⟨a, rest⟩
      · simp [notEval_nil]
      · simp only [hin, List.map_cons, notEval_cons] at h1 ⊢
        have halt : a < n + 2 + idx := hrb idx hidx a (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hidx, hin]; exact List.mem_cons_self)
        rw [if_pos halt] at h1 ⊢
        cases ha0 : (run C.gates (inp t0)).getD a false
        · rfl
        · have ha1 := hmono_step t0 t1 ht01 idx (Nat.le_of_lt hidx) (fun idx' h' hop' => absurd hop' (hfirst idx' h')) a halt ha0
          change (run C.gates (inp t1)).getD a false = true at ha1
          rw [ha1] at h1; cases h1
    refine Finset.card_le_one.mpr fun t1 ht1 t2 ht2 => ?_
    obtain ⟨_, ht1a, ht1b⟩ := Finset.mem_filter.mp ht1
    obtain ⟨_, ht2a, ht2b⟩ := Finset.mem_filter.mp ht2
    rcases lt_trichotomy t1 t2 with hlt | heq | hgt
    · have := hanti t1.succ t2.castSucc (by simp; omega) ht2a
      rw [ht1b] at this; cases this
    · exact heq
    · have := hanti t2.succ t1.castSucc (by simp; omega) ht1a
      rw [ht2b] at this; cases this
  have hnot_eq2 : notList.length = 2 := by
    have hle2 : notList.length ≤ 2 := by omega
    by_contra hne2
    rcases (show notList.length = 0 ∨ notList.length = 1 by omega) with h0 | h1
    · obtain ⟨idx, hidx, hop, _⟩ := hijk_in_not i (by simp)
      have hm : idx ∈ notList := List.mem_filter.mpr ⟨List.mem_range.mpr hidx, decide_eq_true hop⟩
      rw [List.eq_nil_of_length_eq_zero h0] at hm; simp at hm
    · obtain ⟨u, hu_eq⟩ := List.length_eq_one_iff.mp h1
      have hu_mem : u ∈ notList := by rw [hu_eq]; simp
      have huC : u < C.gates.length := List.mem_range.mp (List.mem_filter.mp hu_mem).1
      have hu_op : op u = .not := of_decide_eq_true (List.mem_filter.mp hu_mem).2
      have huniq : ∀ idx < C.gates.length, op idx = .not → idx = u := fun idx hidx hop => by
        have hm : idx ∈ notList := List.mem_filter.mpr ⟨List.mem_range.mpr hidx, decide_eq_true hop⟩
        rw [hu_eq, List.mem_singleton] at hm; exact hm
      have hsub : ({i, j, k} : Finset (Fin n)) ⊆ down (wf (n + 2 + u)) := by
        intro t ht
        obtain ⟨idx, hidx, hop, htd⟩ := hijk_in_not t ht
        rwa [huniq idx hidx hop] at htd
      have hc1 := hnot_antitone_first u huC hu_op (fun idx' hlt hop' => by have := huniq idx' (by omega) hop'; omega)
      have hc2 := Finset.card_le_card hsub
      omega
  -- Extract the two distinct NOT gates u < v
  rcases hnl : notList with _ | ⟨u, _ | ⟨v, rest⟩⟩
  · rw [hnl] at hnot_eq2; simp at hnot_eq2
  · rw [hnl] at hnot_eq2; simp at hnot_eq2
  · have hrest : rest = [] := by rw [hnl] at hnot_eq2; simpa using hnot_eq2
    subst hrest
    have hpw : notList.Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
    rw [hnl] at hpw
    have huv : u < v := by simp at hpw; exact hpw
    have hu_mem : u ∈ notList := by rw [hnl]; simp
    have hv_mem : v ∈ notList := by rw [hnl]; simp
    have huC : u < C.gates.length := List.mem_range.mp (List.mem_filter.mp hu_mem).1
    have hvC : v < C.gates.length := List.mem_range.mp (List.mem_filter.mp hv_mem).1
    have hu_op : op u = .not := of_decide_eq_true (List.mem_filter.mp hu_mem).2
    have hv_op : op v = .not := of_decide_eq_true (List.mem_filter.mp hv_mem).2
    have hnot_only : ∀ idx < C.gates.length, op idx = .not → idx = u ∨ idx = v := fun idx hidx hop => by
      have hm : idx ∈ notList := List.mem_filter.mpr ⟨List.mem_range.mpr hidx, decide_eq_true hop⟩
      rw [hnl] at hm; simpa using hm
    -- u is the first NOT gate, so wf (n+2+u) is antitone with at most 1 fall
    have hu_anti : ∀ (t0 t1 : Fin (n + 1)), t0.val ≤ t1.val →
        wf (n + 2 + u) t1 = true → wf (n + 2 + u) t0 = true := by
      intro t0 t1 ht01 h1
      have hg_eq : C.gates[u] = C.gates.getD u ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ huC).symm
      have hop' : (C.gates[u]).op = .not := (congrArg Gate.op hg_eq).trans hu_op
      have rg0 := run_gate C.gates (inp t0) u huC
      have rg1 := run_gate C.gates (inp t1) u huC
      simp only [inp_len, hop'] at rg0 rg1
      dsimp only [wf] at h1 ⊢; rw [rg1] at h1; rw [rg0]
      rcases hin : (C.gates[u]).inputs with _ | ⟨a, rest⟩
      · simp [notEval_nil]
      · simp only [hin, List.map_cons, notEval_cons] at h1 ⊢
        have halt : a < n + 2 + u := hrb u huC a (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ huC, hin]; exact List.mem_cons_self)
        rw [if_pos halt] at h1 ⊢
        cases ha0 : (run C.gates (inp t0)).getD a false
        · rfl
        · have ha1 := hmono_step t0 t1 ht01 u (Nat.le_of_lt huC) (fun idx' h' hop'' => by
            rcases hnot_only idx' (by omega) hop'' with rfl | rfl <;> omega) a halt ha0
          change (run C.gates (inp t1)).getD a false = true at ha1
          rw [ha1] at h1; cases h1
    have hu_card : (down (wf (n + 2 + u))).card ≤ 1 :=
      hnot_antitone_first u huC hu_op (fun idx' hlt hop' => by rcases hnot_only idx' (by omega) hop' with rfl | rfl <;> omega)
    -- u MUST have a fall p (otherwise wf (n+2+u) is constant, so wf (n+2+v) has ≤ 1 fall, contradicting 3 falls!)
    have hu_ne : (down (wf (n + 2 + u))).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hu_const : ∀ t0 t1 : Fin (n + 1), t0.val ≤ t1.val → wf (n + 2 + u) t0 = true → wf (n + 2 + u) t1 = true := by
        intro t0 t1 ht01 h0
        have hc := const_of_no_trans (wf (n + 2 + u)) t0 t1 ht01 (fun t _ _ => by
          cases h1 : wf (n + 2 + u) t.castSucc <;> cases h2 : wf (n + 2 + u) t.succ
          · rfl
          · have := hu_anti t.castSucc t.succ (by simp) h2; rw [h1] at this; cases this
          · exfalso; have hm : t ∈ down (wf (n + 2 + u)) := Finset.mem_filter.mpr ⟨Finset.mem_univ t, h1, h2⟩
            rw [hempty] at hm; simp at hm
          · rfl)
        rw [← hc, h0]
      -- Then wf (n+2+v) is also antitone → card (down (wf (n+2+v))) ≤ 1!
      have hv_card : (down (wf (n + 2 + v))).card ≤ 1 := by
        have hv_anti : ∀ (t0 t1 : Fin (n + 1)), t0.val ≤ t1.val →
            wf (n + 2 + v) t1 = true → wf (n + 2 + v) t0 = true := by
          intro t0 t1 ht01 h1
          have hg_eq : C.gates[v] = C.gates.getD v ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hvC).symm
          have hop' : (C.gates[v]).op = .not := (congrArg Gate.op hg_eq).trans hv_op
          have rg0 := run_gate C.gates (inp t0) v hvC
          have rg1 := run_gate C.gates (inp t1) v hvC
          simp only [inp_len, hop'] at rg0 rg1
          dsimp only [wf] at h1 ⊢; rw [rg1] at h1; rw [rg0]
          rcases hin : (C.gates[v]).inputs with _ | ⟨a, rest⟩
          · simp [notEval_nil]
          · simp only [hin, List.map_cons, notEval_cons] at h1 ⊢
            have halt : a < n + 2 + v := hrb v hvC a (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hvC, hin]; exact List.mem_cons_self)
            rw [if_pos halt] at h1 ⊢
            cases ha0 : (run C.gates (inp t0)).getD a false
            · rfl
            · have ha1 := hmono_step t0 t1 ht01 v (Nat.le_of_lt hvC) (fun idx' h' hop'' => by
                rcases hnot_only idx' (by omega) hop'' with rfl | rfl
                · exact hu_const t0 t1 ht01
                · omega) a halt ha0
              change (run C.gates (inp t1)).getD a false = true at ha1
              rw [ha1] at h1; cases h1
        refine Finset.card_le_one.mpr fun t1 ht1 t2 ht2 => ?_
        obtain ⟨_, ht1a, ht1b⟩ := Finset.mem_filter.mp ht1
        obtain ⟨_, ht2a, ht2b⟩ := Finset.mem_filter.mp ht2
        rcases lt_trichotomy t1 t2 with hlt | heq | hgt
        · have := hv_anti t1.succ t2.castSucc (by simp; omega) ht2a; rw [ht1b] at this; cases this
        · exact heq
        · have := hv_anti t2.succ t1.castSucc (by simp; omega) ht1a; rw [ht2b] at this; cases this
      have hsub : ({i, j, k} : Finset (Fin n)) ⊆ down (wf (n + 2 + v)) := by
        intro t ht
        obtain ⟨idx, hidx, hop, htd⟩ := hijk_in_not t ht
        rcases hnot_only idx hidx hop with rfl | rfl
        · rw [hempty] at htd; simp at htd
        · exact htd
      have := Finset.card_le_card hsub; omega
    obtain ⟨p, hp_mem⟩ := hu_ne
    have hu_down : down (wf (n + 2 + u)) = {p} := by
      have hc1 : (down (wf (n + 2 + u))).card = 1 := by
        have := Finset.card_pos.mpr ⟨p, hp_mem⟩; omega
      obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hc1
      rw [hq] at hp_mem
      have hpq : p = q := Finset.mem_singleton.mp hp_mem
      subst hpq; exact hq
    -- Therefore wf (n+2+u) = neg (threshold p)!
    have hu_eq : wf (n + 2 + u) = neg (threshold p) := by
      obtain ⟨_, hp1, hp2⟩ := Finset.mem_filter.mp hp_mem
      funext t
      dsimp only [neg, threshold]
      by_cases hle : t.val ≤ p.val
      · have := hu_anti t p.castSucc (by simp; omega) hp1
        rw [this]; simp [show ¬ (p.val < t.val) by omega]
      · have h2 : wf (n + 2 + u) t = false := by
          by_contra hnt
          have ht : wf (n + 2 + u) t = true := by cases h : wf (n + 2 + u) t <;> [exact absurd h hnt; rfl]
          have := hu_anti p.succ t (by simp; omega) ht
          rw [hp2] at this; cases this
        rw [h2]; simp [show p.val < t.val by omega]
    -- Every wire w < n + 2 + v is monotone on [0, p] and monotone on [p+1, n]!
    have hmono_lo : ∀ w < n + 2 + v, ∀ t0 t1 : Fin (n + 1), t0.val ≤ t1.val → t1.val ≤ p.val →
        wf w t0 = true → wf w t1 = true := by
      intro w hw t0 t1 ht01 ht1p
      refine hmono_step t0 t1 ht01 v (Nat.le_of_lt hvC) (fun idx' h' hop' => ?_) w hw
      rcases hnot_only idx' (by omega) hop' with rfl | rfl
      · intro _; rw [hu_eq]; simp [neg, threshold, show ¬ (p.val < t1.val) by omega]
      · omega
    have hmono_hi : ∀ w < n + 2 + v, ∀ t0 t1 : Fin (n + 1), p.val < t0.val → t0.val ≤ t1.val →
        wf w t0 = true → wf w t1 = true := by
      intro w hw t0 t1 hpt0 ht01
      refine hmono_step t0 t1 ht01 v (Nat.le_of_lt hvC) (fun idx' h' hop' => ?_) w hw
      rcases hnot_only idx' (by omega) hop' with rfl | rfl
      · intro h0; rw [hu_eq] at h0; simp [neg, threshold, hpt0] at h0
      · omega
    -- Extract input w_in of NOT gate v!
    have hv_hg : C.gates[v] = C.gates.getD v ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hvC).symm
    have hv_op' : (C.gates[v]).op = .not := (congrArg Gate.op hv_hg).trans hv_op
    rcases hvin : (C.gates[v]).inputs with _ | ⟨w_in, w_rest⟩
    · -- Impossible: wf (n+2+v) would be constant true → down empty → only 1 fall total!
      exfalso
      have hv_empty : down (wf (n + 2 + v)) = ∅ := by
        dsimp only [down]
        rw [Finset.filter_eq_empty_iff]; intro t _ ⟨_, h2⟩
        have rg := run_gate C.gates (inp t.succ) v hvC
        rw [inp_len, hv_op', hvin, List.map_nil, notEval_nil] at rg
        dsimp only [wf] at h2; rw [rg] at h2; cases h2
      have hsub : ({i, j, k} : Finset (Fin n)) ⊆ {p} := by
        intro t ht; obtain ⟨idx, hidx, hop, htd⟩ := hijk_in_not t ht
        rcases hnot_only idx hidx hop with rfl | rfl
        · rwa [hu_down] at htd
        · rw [hv_empty] at htd; simp at htd
      have := Finset.card_le_card hsub; simp at this; omega
    · have hw_in_lt : w_in < n + 2 + v := hrb v hvC w_in (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hvC, hvin]; exact List.mem_cons_self)
      have hv_eval : wf (n + 2 + v) = neg (wf w_in) := by
        funext t; dsimp only [wf, neg]
        have rg := run_gate C.gates (inp t) v hvC
        rw [inp_len, hv_op', hvin, List.map_cons, notEval_cons, if_pos hw_in_lt] at rg
        exact rg
      -- down (wf (n+2+v)) has at most 1 element < p and at most 1 element > p!
      have hv_lo_le1 : ((down (wf (n + 2 + v))).filter (· < p)).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun t1 ht1 t2 ht2 => ?_
        obtain ⟨h1, h1p⟩ := Finset.mem_filter.mp ht1
        obtain ⟨h2, h2p⟩ := Finset.mem_filter.mp ht2
        rw [hv_eval] at h1 h2
        have h1a : wf w_in t1.succ = true := by
          have hh := (Finset.mem_filter.mp h1).2.2; dsimp only [neg] at hh; cases h : wf w_in t1.succ <;> rw [h] at hh <;> first | rfl | cases hh
        have h2a : wf w_in t2.castSucc = false := by
          have hh := (Finset.mem_filter.mp h2).2.1; dsimp only [neg] at hh; cases h : wf w_in t2.castSucc <;> rw [h] at hh <;> first | rfl | cases hh
        have h1b : wf w_in t1.castSucc = false := by
          have hh := (Finset.mem_filter.mp h1).2.1; dsimp only [neg] at hh; cases h : wf w_in t1.castSucc <;> rw [h] at hh <;> first | rfl | cases hh
        have h2b : wf w_in t2.succ = true := by
          have hh := (Finset.mem_filter.mp h2).2.2; dsimp only [neg] at hh; cases h : wf w_in t2.succ <;> rw [h] at hh <;> first | rfl | cases hh
        rcases lt_trichotomy t1 t2 with hlt | heq | hgt
        · have := hmono_lo w_in hw_in_lt t1.succ t2.castSucc (by simp; omega) (by simp; omega) h1a
          rw [h2a] at this; cases this
        · exact heq
        · have := hmono_lo w_in hw_in_lt t2.succ t1.castSucc (by simp; omega) (by simp; omega) h2b
          rw [h1b] at this; cases this
      have hv_hi_le1 : ((down (wf (n + 2 + v))).filter (p < ·)).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun t1 ht1 t2 ht2 => ?_
        obtain ⟨h1, h1p⟩ := Finset.mem_filter.mp ht1
        obtain ⟨h2, h2p⟩ := Finset.mem_filter.mp ht2
        rw [hv_eval] at h1 h2
        have h1a : wf w_in t1.succ = true := by
          have hh := (Finset.mem_filter.mp h1).2.2; dsimp only [neg] at hh; cases h : wf w_in t1.succ <;> rw [h] at hh <;> first | rfl | cases hh
        have h2a : wf w_in t2.castSucc = false := by
          have hh := (Finset.mem_filter.mp h2).2.1; dsimp only [neg] at hh; cases h : wf w_in t2.castSucc <;> rw [h] at hh <;> first | rfl | cases hh
        have h1b : wf w_in t1.castSucc = false := by
          have hh := (Finset.mem_filter.mp h1).2.1; dsimp only [neg] at hh; cases h : wf w_in t1.castSucc <;> rw [h] at hh <;> first | rfl | cases hh
        have h2b : wf w_in t2.succ = true := by
          have hh := (Finset.mem_filter.mp h2).2.2; dsimp only [neg] at hh; cases h : wf w_in t2.succ <;> rw [h] at hh <;> first | rfl | cases hh
        rcases lt_trichotomy t1 t2 with hlt | heq | hgt
        · have := hmono_hi w_in hw_in_lt t1.succ t2.castSucc (by simp; omega) (by simp; omega) h1a
          rw [h2a] at this; cases this
        · exact heq
        · have := hmono_hi w_in hw_in_lt t2.succ t1.castSucc (by simp; omega) (by simp; omega) h2b
          rw [h1b] at this; cases this
      -- Every t ∈ {i, j, k} is either = p, or in lo (< p), or in hi (> p)!
      have hijk_sub : ({i, j, k} : Finset (Fin n)) ⊆
          insert p (((down (wf (n + 2 + v))).filter (· < p)) ∪ ((down (wf (n + 2 + v))).filter (p < ·))) := by
        intro t ht
        by_cases htp : t = p
        · rw [htp]; exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem ?_
          obtain ⟨idx, hidx, hop, htd⟩ := hijk_in_not t ht
          rcases hnot_only idx hidx hop with rfl | rfl
          · rw [hu_down, Finset.mem_singleton] at htd; exact absurd htd htp
          · rcases lt_or_gt_of_ne htp with hlt | hgt
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨htd, hlt⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htd, hgt⟩)
      -- Deduce p = j, i ∈ down (wf (n+2+v)), k ∈ down (wf (n+2+v))!
      have hp_eq_j : p = j := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · -- p < j < k: both j and k are > p, so both are in hi (> p), contradicting hv_hi_le1!
          have hj_hi : j ∈ (down (wf (n + 2 + v))).filter (p < ·) := by
            have hm := hijk_sub (show j ∈ ({i, j, k} : Finset (Fin n)) by simp)
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hm
            rcases hm with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact absurd h.symm hne
            · exact absurd (lt_trans hlt h2) (lt_irrefl _)
            · exact Finset.mem_filter.mpr ⟨h1, h2⟩
          have hk_hi : k ∈ (down (wf (n + 2 + v))).filter (p < ·) := by
            have hm := hijk_sub (show k ∈ ({i, j, k} : Finset (Fin n)) by simp)
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hm
            rcases hm with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact absurd (lt_trans hlt hjk) (by rw [h]; exact lt_irrefl _)
            · exact absurd (lt_trans (lt_trans hlt hjk) h2) (lt_irrefl _)
            · exact Finset.mem_filter.mpr ⟨h1, h2⟩
          exact ne_of_lt hjk (Finset.card_le_one.mp hv_hi_le1 j hj_hi k hk_hi)
        · -- i < j < p: both i and j are < p, contradicting hv_lo_le1!
          have hi_lo : i ∈ (down (wf (n + 2 + v))).filter (· < p) := by
            have hm := hijk_sub (show i ∈ ({i, j, k} : Finset (Fin n)) by simp)
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hm
            rcases hm with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact absurd (lt_trans hij hgt) (by rw [h]; exact lt_irrefl _)
            · exact Finset.mem_filter.mpr ⟨h1, h2⟩
            · exact absurd (lt_trans (lt_trans hij hgt) h2) (lt_irrefl _)
          have hj_lo : j ∈ (down (wf (n + 2 + v))).filter (· < p) := by
            have hm := hijk_sub (show j ∈ ({i, j, k} : Finset (Fin n)) by simp)
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hm
            rcases hm with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact absurd h.symm hne
            · exact Finset.mem_filter.mpr ⟨h1, h2⟩
            · exact absurd (lt_trans hgt h2) (lt_irrefl _)
          exact ne_of_lt hij (Finset.card_le_one.mp hv_lo_le1 i hi_lo j hj_lo)
      rcases hp_eq_j.symm with rfl
      have hi_v : i ∈ down (wf (n + 2 + v)) := by
        have hm := hijk_sub (show i ∈ ({i, j, k} : Finset (Fin n)) by simp)
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hm
        rcases hm with h | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h (ne_of_lt hij)
        · exact h1
        · exact h1
      have hk_v : k ∈ down (wf (n + 2 + v)) := by
        have hm := hijk_sub (show k ∈ ({i, j, k} : Finset (Fin n)) by simp)
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hm
        rcases hm with h | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd h.symm (ne_of_lt hjk)
        · exact h1
        · exact h1
      -- Now deduce wf w_in = driver!
      have hwin_eq : wf w_in = driver := by
        rw [hv_eval] at hi_v hk_v
        have hi0 : wf w_in i.castSucc = false := by
          have hh := (Finset.mem_filter.mp hi_v).2.1; dsimp only [neg] at hh; cases h : wf w_in i.castSucc <;> rw [h] at hh <;> first | rfl | cases hh
        have hi1 : wf w_in i.succ = true := by
          have hh := (Finset.mem_filter.mp hi_v).2.2; dsimp only [neg] at hh; cases h : wf w_in i.succ <;> rw [h] at hh <;> first | rfl | cases hh
        have hk0 : wf w_in k.castSucc = false := by
          have hh := (Finset.mem_filter.mp hk_v).2.1; dsimp only [neg] at hh; cases h : wf w_in k.castSucc <;> rw [h] at hh <;> first | rfl | cases hh
        have hk1 : wf w_in k.succ = true := by
          have hh := (Finset.mem_filter.mp hk_v).2.2; dsimp only [neg] at hh; cases h : wf w_in k.succ <;> rw [h] at hh <;> first | rfl | cases hh
        have hij' : i.val < j.val := hij
        have hjk' : j.val < k.val := hjk
        funext t
        dsimp only [driver, join, meet, threshold, middle, neg]
        by_cases h1 : t.val ≤ i.val
        · have hf : wf w_in t = false := by
            by_contra hnt; have ht : wf w_in t = true := by cases h : wf w_in t <;> [exact absurd h hnt; rfl]
            have := hmono_lo w_in hw_in_lt t i.castSucc (by simp; omega) (by simp; omega) ht
            rw [hi0] at this; cases this
          rw [hf]; simp [show ¬ (i.val < t.val) by omega, show ¬ (k.val < t.val) by omega]
        · by_cases h2 : t.val ≤ j.val
          · have ht := hmono_lo w_in hw_in_lt i.succ t (by simp; omega) h2 hi1
            rw [ht]; simp [show i.val < t.val by omega, show ¬ (j.val < t.val) by omega]
          · by_cases h3 : t.val ≤ k.val
            · have hf : wf w_in t = false := by
                by_contra hnt; have ht : wf w_in t = true := by cases h : wf w_in t <;> [exact absurd h hnt; rfl]
                have := hmono_hi w_in hw_in_lt t k.castSucc (by omega) (by simp; omega) ht
                rw [hk0] at this; cases this
              rw [hf]; simp [show j.val < t.val by omega, show ¬ (k.val < t.val) by omega]
            · have ht := hmono_hi w_in hw_in_lt k.succ t (by simp; omega) (by simp; omega) hk1
              rw [ht]; simp [show k.val < t.val by omega]
      have hv_eq : wf (n + 2 + v) = neg driver := by rw [hv_eval, hwin_eq]
      -- Now define posIdx, posFuns, E := posFuns \ insert driver A!
      let posIdx : Finset ℕ := (Finset.range C.size).filter (fun r => r ≠ u ∧ r ≠ v)
      have hposIdx_card : posIdx.card = C.size - 2 := by
        have h1 : posIdx = ((Finset.range C.size).erase u).erase v := by
          ext r; simp only [posIdx, Finset.mem_filter, Finset.mem_erase, Finset.mem_range]; tauto
        have hu_sz : u < C.size := huC
        have hv_sz : v < C.size := hvC
        rw [h1, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne_of_gt huv, Finset.mem_range.mpr hv_sz⟩),
          Finset.card_erase_of_mem (Finset.mem_range.mpr hu_sz), Finset.card_range]
        omega
      let posFuns : Finset (W n) := posIdx.image (fun r => wf (n + 2 + r))
      have hposFuns_card : posFuns.card ≤ A.card + 1 + s := by
        have h1 : posFuns.card ≤ posIdx.card := Finset.card_image_le
        omega
      obtain ⟨_, _, hdrv_c2, hdrv_nr, hdrv_nm, hdrv_nn⟩ := down_driver_properties i j k hij hjk
      change (down (neg driver)).card = 2 at hdrv_c2
      have hdrv_not_A : driver ∉ A := fun h => by
        have := (hA driver h).2; omega
      have hsub_pos : insert driver A ⊆ posFuns := by
        intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hfA
        · -- driver = wf w_in, w_in < n + 2 + v
          have hw_ge : n + 2 ≤ w_in := by
            by_contra hlt
            have hraw : wf w_in ∈ raw n := by
              by_cases hwn : w_in < n
              · have : wf w_in = threshold ⟨w_in, hwn⟩ := by
                  funext t; dsimp [wf]; rw [run_input C.gates (inp t) w_in (by rw [inp_len]; omega)]
                  exact inp_getD_lt t ⟨w_in, hwn⟩
                rw [this]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
              · rcases (show w_in = n ∨ w_in = n + 1 by omega) with hw1 | hw2
                · have : wf w_in = fun _ => false := by
                    funext t; dsimp [wf]; rw [hw1, run_input C.gates (inp t) n (by rw [inp_len]; omega), inp_getD_false]
                  rw [this]; exact Finset.mem_insert_self _ _
                · have : wf w_in = fun _ => true := by
                    funext t; dsimp [wf]; rw [hw2, run_input C.gates (inp t) (n + 1) (by rw [inp_len]; omega), inp_getD_true]
                  rw [this]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            rw [hwin_eq] at hraw; exact hdrv_nr hraw
          let r := w_in - (n + 2)
          have hr_eq : n + 2 + r = w_in := by omega
          have hru : r ≠ u := fun h => by
            have : driver = middle := by rw [← hwin_eq, ← hr_eq, h, hu_eq]
            exact hdrv_nm this
          have hrv : r ≠ v := by omega
          exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [Circuit.size]; omega), hru, hrv⟩, by rw [hr_eq, hwin_eq]⟩
        · obtain ⟨htap_lt, htap_ev⟩ := htap f hfA
          have hfeq : wf (tap f) = f := funext htap_ev
          have hfnr : f ∉ raw n := fun hr => by
            have hd0 := down_raw_empty f hr; have hd1 := (hA f hfA).1; rw [hd0] at hd1; simp at hd1
          have hfnm : f ≠ middle := fun h => by
            have h1 := (hA f hfA).2
            rw [h] at h1
            have h2 : down (neg middle) = ∅ := by
              dsimp only [middle]; rw [down_neg_neg]
              exact down_raw_empty (threshold j) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
            rw [h2] at h1; simp at h1
          have hfnn : f ≠ neg driver := fun h => by
            have h1 := (hA f hfA).1
            rw [h] at h1; omega
          have hw_ge : n + 2 ≤ tap f := by
            by_contra hlt
            have hraw : wf (tap f) ∈ raw n := by
              by_cases hwn : tap f < n
              · have : wf (tap f) = threshold ⟨tap f, hwn⟩ := by
                  funext t; dsimp [wf]; rw [run_input C.gates (inp t) (tap f) (by rw [inp_len]; omega)]
                  exact inp_getD_lt t ⟨tap f, hwn⟩
                rw [this]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
              · rcases (show tap f = n ∨ tap f = n + 1 by omega) with h1 | h1
                · have : wf (tap f) = fun _ => false := by
                    funext t; dsimp [wf]; rw [h1, run_input C.gates (inp t) n (by rw [inp_len]; omega), inp_getD_false]
                  rw [this]; exact Finset.mem_insert_self _ _
                · have : wf (tap f) = fun _ => true := by
                    funext t; dsimp [wf]; rw [h1, run_input C.gates (inp t) (n + 1) (by rw [inp_len]; omega), inp_getD_true]
                  rw [this]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            rw [hfeq] at hraw; exact hfnr hraw
          let r := tap f - (n + 2)
          have hr_eq : n + 2 + r = tap f := by omega
          have hru : r ≠ u := fun h => hfnm (by rw [← hfeq, ← hr_eq, h, hu_eq])
          have hrv : r ≠ v := fun h => hfnn (by rw [← hfeq, ← hr_eq, h, hv_eq])
          exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hru, hrv⟩, by rw [hr_eq, hfeq]⟩
      let E : Finset (W n) := posFuns \ insert driver A
      have hE_card : E.card ≤ s := by
        have h1 := Finset.card_sdiff_add_card_eq_card hsub_pos
        rw [Finset.card_insert_of_notMem hdrv_not_A] at h1
        change E.card + (A.card + 1) = posFuns.card at h1
        omega
      let allow : Finset (W n) := insert driver (A ∪ E)
      have hposFuns_allow : posFuns ⊆ allow := by
        intro f hf
        by_cases h1 : f ∈ insert driver A
        · rcases Finset.mem_insert.mp h1 with rfl | hA'
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hA')
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hf, h1⟩))
      -- Induction along C.gates: every wire < n + 2 + m is in (stepFun driver allow)^[m] (insert middle (raw n))!
      have hreach_m : ∀ m ≤ C.size, ∀ w < n + 2 + m, wf w ∈ (stepFun driver allow)^[m] (insert middle (raw n)) := by
        intro m
        induction m with
        | zero =>
          intro _ w hw
          refine Finset.mem_insert_of_mem ?_
          by_cases hwn : w < n
          · have : wf w = threshold ⟨w, hwn⟩ := by
              funext t; dsimp [wf]; rw [run_input C.gates (inp t) w (by rw [inp_len]; omega)]
              exact inp_getD_lt t ⟨w, hwn⟩
            rw [this]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
          · rcases (show w = n ∨ w = n + 1 by omega) with hw1 | hw2
            · have : wf w = fun _ => false := by
                funext t; dsimp [wf]; rw [hw1, run_input C.gates (inp t) n (by rw [inp_len]; omega), inp_getD_false]
              rw [this]; exact Finset.mem_insert_self _ _
            · have : wf w = fun _ => true := by
                funext t; dsimp [wf]; rw [hw2, run_input C.gates (inp t) (n + 1) (by rw [inp_len]; omega), inp_getD_true]
              rw [this]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        | succ m ih =>
          intro hm w hw
          rw [Function.iterate_succ_apply']
          by_cases hlt : w < n + 2 + m
          · exact sub_stepFun driver allow _ (ih (by omega) w hlt)
          · have hweq : w = n + 2 + m := by omega
            subst hweq
            by_cases hmu : m = u
            · rw [hmu, hu_eq, ← Function.iterate_succ_apply' (stepFun driver allow) u]
              have hmem0 : middle ∈ (stepFun driver allow)^[0] (insert middle (raw n)) := Finset.mem_insert_self _ _
              exact iterate_stepFun_mono driver allow (insert middle (raw n)) (Nat.zero_le (u + 1)) hmem0
            · by_cases hmv : m = v
              · rw [hmv, hv_eq]
                have hdrv_in : driver ∈ (stepFun driver allow)^[v] (insert middle (raw n)) := by
                  have h := ih (by omega) w_in (by omega)
                  rw [hmv, hwin_eq] at h
                  exact h
                dsimp only [stepFun]
                exact Finset.mem_union_right _ (by rw [if_pos hdrv_in]; exact Finset.mem_singleton_self _)
              · -- m is a positive gate: wf (n+2+m) ∈ posFuns ⊆ allow!
                have hm_allow : wf (n + 2 + m) ∈ allow :=
                  hposFuns_allow (Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hmu, hmv⟩, rfl⟩)
                have hmC : m < C.gates.length := by dsimp [Circuit.size] at hm; omega
                have hmg : C.gates[m] = C.gates.getD m ⟨.or, []⟩ := (List.getD_eq_getElem C.gates _ hmC).symm
                have hlen := (hfan _ (List.getElem_mem hmC)).2
                set B := (stepFun driver allow)^[m] (insert middle (raw n))
                have hrawB : raw n ⊆ B := Finset.Subset.trans (Finset.subset_insert _ _)
                  (iterate_stepFun_mono driver allow _ (Nat.zero_le m))
                rcases (hfan _ (List.getElem_mem hmC)).1 with hand | hor | hnot'
                · rcases hin : (C.gates[m]).inputs with _ | ⟨a, rest⟩
                  · have : wf (n + 2 + m) = fun _ => true := by
                      funext t; dsimp [wf]; have rg := run_gate C.gates (inp t) m hmC
                      rw [inp_len, hand, hin] at rg; exact rg
                    exact sub_stepFun driver allow B (hrawB (by rw [this]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
                  · rcases rest with _ | ⟨b, rest2⟩
                    · have halt : a < n + 2 + m := hrb m hmC a (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hmC, hin]; simp)
                      have : wf (n + 2 + m) = wf a := by
                        funext t; dsimp [wf]; have rg := run_gate C.gates (inp t) m hmC
                        rw [inp_len, hand, hin, andEval] at rg; rw [rg]
                        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, if_pos halt]
                      exact sub_stepFun driver allow B (by rw [this]; exact ih (by omega) a halt)
                    · have hrest2 : rest2 = [] := by rw [hin] at hlen; cases rest2 <;> simp at hlen ⊢
                      subst hrest2
                      have halt : a < n + 2 + m := hrb m hmC a (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hmC, hin]; simp)
                      have hblt : b < n + 2 + m := hrb m hmC b (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hmC, hin]; simp)
                      have hmeq : wf (n + 2 + m) = meet (wf a) (wf b) := by
                        funext t; dsimp [wf, meet]; have rg := run_gate C.gates (inp t) m hmC
                        rw [inp_len, hand, hin, andEval] at rg; rw [rg]
                        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, if_pos halt, if_pos hblt]
                      dsimp only [stepFun]
                      refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hm_allow, ?_⟩))
                      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(wf a, wf b),
                        Finset.mem_product.mpr ⟨ih (by omega) a halt, ih (by omega) b hblt⟩, hmeq.symm⟩)
                · rcases hin : (C.gates[m]).inputs with _ | ⟨a, rest⟩
                  · have : wf (n + 2 + m) = fun _ => false := by
                      funext t; dsimp [wf]; have rg := run_gate C.gates (inp t) m hmC
                      rw [inp_len, hor, hin] at rg; exact rg
                    exact sub_stepFun driver allow B (hrawB (by rw [this]; exact Finset.mem_insert_self _ _))
                  · rcases rest with _ | ⟨b, rest2⟩
                    · have halt : a < n + 2 + m := hrb m hmC a (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hmC, hin]; simp)
                      have : wf (n + 2 + m) = wf a := by
                        funext t; dsimp [wf]; have rg := run_gate C.gates (inp t) m hmC
                        rw [inp_len, hor, hin, orEval] at rg; rw [rg]
                        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, if_pos halt]
                      exact sub_stepFun driver allow B (by rw [this]; exact ih (by omega) a halt)
                    · have hrest2 : rest2 = [] := by rw [hin] at hlen; cases rest2 <;> simp at hlen ⊢
                      subst hrest2
                      have halt : a < n + 2 + m := hrb m hmC a (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hmC, hin]; simp)
                      have hblt : b < n + 2 + m := hrb m hmC b (by dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]; rw [List.getD_eq_getElem C.gates _ hmC, hin]; simp)
                      have hjeq : wf (n + 2 + m) = join (wf a) (wf b) := by
                        funext t; dsimp [wf, join]; have rg := run_gate C.gates (inp t) m hmC
                        rw [inp_len, hor, hin, orEval] at rg; rw [rg]
                        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, if_pos halt, if_pos hblt]
                      dsimp only [stepFun]
                      refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hm_allow, ?_⟩))
                      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(wf a, wf b),
                        Finset.mem_product.mpr ⟨ih (by omega) a halt, ih (by omega) b hblt⟩, hjeq.symm⟩)
                · exfalso
                  have hop_m : op m = .not := (congrArg Gate.op hmg).symm.trans hnot'
                  rcases hnot_only m hmC hop_m with rfl | rfl <;> [exact hmu rfl; exact hmv rfl]
      refine ⟨E, hE_card, ?_, ?_⟩
      · intro f hfA
        obtain ⟨htap_lt, htap_ev⟩ := htap f hfA
        have hfeq : wf (tap f) = f := funext htap_ev
        rw [← hfeq]
        exact iterate_stepFun_mono driver allow (insert middle (raw n)) (by omega)
          (hreach_m C.size le_rfl (tap f) htap_lt)
      · have h := iterate_stepFun_mono driver allow (insert middle (raw n)) (show C.size ≤ A.card + s + 3 by omega)
          (hreach_m C.size le_rfl w_in (by dsimp [Circuit.size]; omega))
        rw [hwin_eq] at h
        exact h

private theorem main_clean (n : ℕ) (i j k : Fin n) (hij : i < j) (hjk : j < k)
    (A : Finset (W n))
    (hA : ∀ f ∈ A, (down f).card = 1 ∧ (down (neg f)).card = 1)
    (hbi : A.biUnion down = {i, j, k}) :
    let middle := neg (threshold j)
    let driver := join (meet (threshold i) middle) (threshold k)
    fitsClean A 3 (A.card + 3) ∧ ∀ s : ℕ,
      fitsClean A 2 (A.card + 3 + s) ↔
        ∃ E : Finset (W n), E.card ≤ s ∧
          let allow := insert driver (A ∪ E)
          let reachable := (stepFun driver allow)^[A.card + s + 3] (insert middle (raw n))
          A ⊆ reachable ∧ driver ∈ reachable := by
  refine ⟨part1_clean n i j k A hA hbi, fun s => ⟨part2_fwd n i j k hij hjk A hA hbi s, ?_⟩⟩
  rintro ⟨E, hEs, hreach⟩
  exact part2_bwd n i j k hij hjk A s E hEs hreach

end PEqualNP.Outside.L_lib_1324

theorem PEqualNP.Outside.L_lib_1324 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n : Nat) (i j k : Fin n), i < j → j < k →
      let W := Fin (n+1) → Bool
      let threshold := fun (q : Fin n) (t : Fin (n+1)) => decide (q.val < t.val)
      let neg := fun (f : W) (t : Fin (n+1)) => !(f t)
      let meet := fun (f g : W) (t : Fin (n+1)) => f t && g t
      let join := fun (f g : W) (t : Fin (n+1)) => f t || g t
      let down := fun (f : W) => (Finset.univ : Finset (Fin n)).filter
        (fun t => f t.castSucc = true ∧ f t.succ = false)
      let middle := neg (threshold j)
      let driver := join (meet (threshold i) middle) (threshold k)
      let raw := insert (fun _ => false) (insert (fun _ => true) (Finset.univ.image threshold))
      ∀ (A : Finset W), (∀ f ∈ A, (down f).card = 1 ∧ (down (neg f)).card = 1) →
        A.biUnion down = {i,j,k} →
        let fits := fun (b s : Nat) =>
          ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : W → Nat),
            PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
            C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ s ∧
            ∀ f ∈ A, tap f < n+2+C.size ∧ ∀ t : Fin (n+1),
              (C.wires (List.ofFn (fun q => threshold q t) ++ [false,true])).getD (tap f) false = f t
        fits 3 (A.card+3) ∧ ∀ s : Nat,
          fits 2 (A.card+3+s) ↔
            ∃ E : Finset W, E.card ≤ s ∧
              let allow := insert driver (A ∪ E)
              let step := fun (B : Finset W) =>
                let pairs := B.product B
                let positive := (pairs.image (fun z => meet z.1 z.2)) ∪ (pairs.image (fun z => join z.1 z.2))
                (B ∪ (allow ∩ positive)) ∪ (if driver ∈ B then {neg driver} else ∅)
              let reachable := (step^[A.card+s+3]) (insert middle raw)
              A ⊆ reachable ∧ driver ∈ reachable := by
  dsimp only
  intro n i j k hij hjk A hA hbi
  have hdec_lt : ∀ (a b : ℕ), @decide (a < b) (Classical.propDecidable _) = decide (a < b) :=
    fun _ _ => decide_eq_decide.mpr Iff.rfl
  simp only [hdec_lt] at hA hbi ⊢
  have hA' : ∀ f ∈ A, (PEqualNP.Outside.L_lib_1324.down f).card = 1 ∧
      (PEqualNP.Outside.L_lib_1324.down (PEqualNP.Outside.L_lib_1324.neg f)).card = 1 := by
    intro f hf
    have hf' := hA f hf
    have h1 : PEqualNP.Outside.L_lib_1324.down f =
        @Finset.filter (Fin n) (fun t => f t.castSucc = true ∧ f t.succ = false) (fun _ => Classical.propDecidable _) Finset.univ := by
      ext t; simp [PEqualNP.Outside.L_lib_1324.down]
    have h2 : PEqualNP.Outside.L_lib_1324.down (PEqualNP.Outside.L_lib_1324.neg f) =
        @Finset.filter (Fin n) (fun t => (!f t.castSucc) = true ∧ (!f t.succ) = false) (fun _ => Classical.propDecidable _) Finset.univ := by
      ext t; simp [PEqualNP.Outside.L_lib_1324.down, PEqualNP.Outside.L_lib_1324.neg]
    rw [h1, h2]; exact hf'
  have hbi' : A.biUnion PEqualNP.Outside.L_lib_1324.down = {i, j, k} := by
    ext t
    have hm := congrArg (t ∈ ·) hbi
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    simpa [PEqualNP.Outside.L_lib_1324.down] using hm
  obtain ⟨hp1, hp2⟩ := PEqualNP.Outside.L_lib_1324.main_clean n i j k hij hjk A hA' hbi'
  have hiter : ∀ {α : Type} (f g : α → α), (∀ x, f x = g x) → ∀ m x y, x = y → f^[m] x = g^[m] y := by
    intro α f g hfg m
    induction m with
    | zero => intro x y h; exact h
    | succ m ih => intro x y h; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hfg, ih x y h]
  refine ⟨hp1, fun s => (hp2 s).trans (exists_congr fun E => and_congr_right fun _ => ?_)⟩
  dsimp only
  have hcongr : ∀ (s1 s2 : Finset (Fin (n + 1) → Bool)), s1 = s2 →
      ((A ⊆ s1 ∧ PEqualNP.Outside.L_lib_1324.join (PEqualNP.Outside.L_lib_1324.meet (PEqualNP.Outside.L_lib_1324.threshold i)
        (PEqualNP.Outside.L_lib_1324.neg (PEqualNP.Outside.L_lib_1324.threshold j)))
        (PEqualNP.Outside.L_lib_1324.threshold k) ∈ s1) ↔
       (A ⊆ s2 ∧ (fun t => decide (i.val < t.val) && !decide (j.val < t.val) || decide (k.val < t.val)) ∈ s2)) := by
    rintro s1 _ rfl; rfl
  refine hcongr _ _ (hiter _ _ (fun B => ?_) (A.card + s + 3) _ _ ?_)
  · ext f
    dsimp only [PEqualNP.Outside.L_lib_1324.stepFun]
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_image]
    split_ifs <;> first | exact Iff.rfl | contradiction
  · ext f
    simp only [PEqualNP.Outside.L_lib_1324.raw, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
    exact Iff.rfl
