import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1321_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

/-! ## Running gates -/

def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [value w g]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [value w g]) := rfl

lemma getD_snoc_lt (w : List Bool) (b : Bool) (p : ℕ) (hp : p < w.length) :
    (w ++ [b]).getD p false = w.getD p false := List.getD_append _ _ _ _ hp

lemma getD_snoc_eq (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp

lemma getD_snoc_gt (w : List Bool) (b : Bool) (p : ℕ) (hp : w.length < p) :
    (w ++ [b]).getD p false = false := by
  rw [List.getD_eq_default _ _ (by simp; omega)]

def Cons (V : ℕ → Bool) (base : ℕ) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), V (base + j) = gs[j].op.eval (gs[j].inputs.map V)

def RB (base : ℕ) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), ∀ v ∈ gs[j].inputs, v < base + j

lemma run_spec (gs : List Gate) : ∀ (x : List Bool), RB x.length gs →
    (∀ p, p < x.length → (run gs x).getD p false = x.getD p false) ∧
    Cons (fun p => (run gs x).getD p false) x.length gs := by
  induction gs with
  | nil => intro x _; exact ⟨fun p _ => rfl, fun j h => absurd h (by simp)⟩
  | cons g gs ih =>
    intro x hrb
    have hlen : (x ++ [value x g]).length = x.length + 1 := by simp
    have hrb' : RB (x ++ [value x g]).length gs := by
      intro j hj v hv
      have := hrb (j+1) (by simp; omega) v (by simpa using hv)
      rw [hlen]; omega
    obtain ⟨h1, h2⟩ := ih _ hrb'
    refine ⟨fun p hp => ?_, fun j hj => ?_⟩
    · rw [run_cons, h1 p (by rw [hlen]; omega)]; exact getD_snoc_lt _ _ _ hp
    · cases j with
      | zero =>
        show (run gs (x ++ [value x g])).getD (x.length + 0) false = _
        rw [Nat.add_zero, h1 _ (by rw [hlen]; omega), getD_snoc_eq]
        simp only [List.getElem_cons_zero]
        unfold value
        congr 1
        apply List.map_congr_left
        intro v hv
        have hvlt := hrb 0 (by simp) v (by simpa using hv)
        show x.getD v false = (run gs (x ++ [value x g])).getD v false
        rw [h1 v (by rw [hlen]; omega), getD_snoc_lt _ _ _ (by omega)]
      | succ j =>
        have := h2 j (by simpa using hj)
        have e : (x ++ [value x g]).length + j = x.length + (j + 1) := by rw [hlen]; omega
        rw [e] at this
        exact this

lemma Cons.left {V : ℕ → Bool} {base : ℕ} {A B : List Gate} (h : Cons V base (A ++ B)) :
    Cons V base A := by
  intro j hj
  have := h j (by simp; omega)
  simp only [List.getElem_append_left hj] at this
  exact this

lemma Cons.right {V : ℕ → Bool} {base : ℕ} {A B : List Gate} (h : Cons V base (A ++ B)) :
    Cons V (base + A.length) B := by
  intro j hj
  have := h (A.length + j) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  rw [Nat.add_assoc]; exact this

lemma Cons.single {V : ℕ → Bool} {base : ℕ} {g : Gate} (h : Cons V base [g]) :
    V base = g.op.eval (g.inputs.map V) := by
  simpa using h 0 (by simp)

lemma Cons.ofFn {V : ℕ → Bool} {base M : ℕ} {f : Fin M → Gate} (h : Cons V base (List.ofFn f))
    (r : Fin M) : V (base + r) = (f r).op.eval ((f r).inputs.map V) := by
  have := h r (by simp)
  simpa using this

lemma RB.append {base : ℕ} {A B : List Gate} (hA : RB base A) (hB : RB (base + A.length) B) :
    RB base (A ++ B) := by
  intro j hj v hv
  by_cases hjA : j < A.length
  · rw [List.getElem_append_left hjA] at hv; exact hA j hjA v hv
  · rw [List.getElem_append_right (by omega)] at hv
    have := hB (j - A.length) (by simp at hj; omega) v hv
    omega

lemma RB.single {base : ℕ} {g : Gate} (h : ∀ v ∈ g.inputs, v < base) : RB base [g] := by
  intro j hj v hv
  simp at hj; subst hj
  simpa using h v (by simpa using hv)

lemma RB.ofFn {base M : ℕ} {f : Fin M → Gate} (h : ∀ r : Fin M, ∀ v ∈ (f r).inputs, v < base + r) :
    RB base (List.ofFn f) := by
  intro j hj v hv
  simp at hj
  simp only [List.getElem_ofFn] at hv
  exact h ⟨j, hj⟩ v hv

lemma getD_inp {n : ℕ} (f : Fin n → Bool) (p : ℕ) :
    (List.ofFn f ++ [false, true]).getD p false = if h : p < n then f ⟨p, h⟩ else decide (p = n + 1) := by
  by_cases h : p < n
  · rw [dif_pos h, List.getD_append _ _ _ _ (by simpa using h),
      List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [dif_neg h, List.getD_append_right _ _ _ _ (by simpa using h)]
    simp only [List.length_ofFn]
    rcases (by omega : p = n ∨ p = n + 1 ∨ n + 1 < p) with rfl | rfl | hp
    · simp
    · simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp; omega

lemma getD_ofFn_dec {n : ℕ} (Q : Fin n → Prop) (dq : ∀ v, Decidable (Q v)) (p : ℕ) (hp : p < n) :
    (List.ofFn (fun v : Fin n => @decide (Q v) (dq v)) ++ [false, true]).getD p false = true ↔
      Q ⟨p, hp⟩ := by
  rw [getD_inp, dif_pos hp, decide_eq_true_iff]

/-! ## Falls along a chain of inputs -/

noncomputable def falls (X : ℕ → List Bool) (k : ℕ) : Finset ℕ := by
  classical exact Finset.filter (fun j => ∃ p, (X j).getD p false = true ∧ (X (j+1)).getD p false = false) (Finset.range k)

lemma mem_falls {X : ℕ → List Bool} {k j : ℕ} : j ∈ falls X k ↔
    j < k ∧ ∃ p, (X j).getD p false = true ∧ (X (j+1)).getD p false = false := by
  unfold falls; simp

lemma rise_fall_sum (u : ℕ → Bool) (k : ℕ) :
    (∑ j ∈ Finset.range k, if (u j = false ∧ u (j+1) = true) then 1 else 0) +
      (if u 0 = true then 1 else 0) =
    (∑ j ∈ Finset.range k, if (u j = true ∧ u (j+1) = false) then 1 else 0) +
      (if u k = true then 1 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    cases h1 : u k <;> cases h2 : u (k+1) <;> simp only [h1, h2] at ih ⊢ <;> simp at ih ⊢ <;> omega

lemma rise_le_fall (u : ℕ → Bool) (k : ℕ) :
    ((Finset.range k).filter (fun j => u j = false ∧ u (j+1) = true)).card ≤
    ((Finset.range k).filter (fun j => u j = true ∧ u (j+1) = false)).card + 1 := by
  rw [Finset.card_filter, Finset.card_filter]
  have := rise_fall_sum u k
  split_ifs at this <;> omega

lemma falls_step (X : ℕ → List Bool) (k L : ℕ) (hL : ∀ j, j ≤ k → (X j).length = L) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (g.op ≠ GateOp.not → (falls (fun j => X j ++ [value (X j) g]) k).card ≤ (falls X k).card) ∧
    (falls (fun j => X j ++ [value (X j) g]) k).card ≤ 2 * (falls X k).card + 1 := by
  classical
  set nf := (Finset.range k).filter (fun j => value (X j) g = true ∧ value (X (j+1)) g = false)
    with hnf
  have hsub : falls (fun j => X j ++ [value (X j) g]) k ⊆ falls X k ∪ nf := by
    intro j hj
    rw [mem_falls] at hj
    obtain ⟨hjk, p, hp1, hp2⟩ := hj
    have hl1 := hL j (by omega)
    have hl2 := hL (j+1) (by omega)
    rcases lt_trichotomy p L with hp | rfl | hp
    · rw [getD_snoc_lt _ _ _ (by omega)] at hp1 hp2
      exact Finset.mem_union_left _ (mem_falls.2 ⟨hjk, p, hp1, hp2⟩)
    · have e1 := getD_snoc_eq (X j) (value (X j) g)
      have e2 := getD_snoc_eq (X (j+1)) (value (X (j+1)) g)
      rw [hl1] at e1; rw [hl2] at e2
      rw [e1] at hp1; rw [e2] at hp2
      exact Finset.mem_union_right _ (by rw [hnf]; simp [hjk, hp1, hp2])
    · rw [getD_snoc_gt _ _ _ (by omega)] at hp1
      exact absurd hp1 (by simp)
  have hAO : g.op ≠ GateOp.not → nf ⊆ falls X k := by
    intro hn j hj
    rw [hnf, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjk, h1, h2⟩ := hj
    rw [mem_falls]
    refine ⟨hjk, ?_⟩
    unfold value at h1 h2
    rcases hg with ho | ho | ho
    · rw [ho] at h1 h2
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h1 h2
      simp only [Bool.eq_false_iff, ne_eq, List.all_eq_true, List.mem_map, id] at h2
      push Not at h2
      obtain ⟨b, ⟨v, hv, rfl⟩, hb⟩ := h2
      exact ⟨v, h1 _ ⟨v, hv, rfl⟩, by simpa using hb⟩
    · rw [ho] at h1 h2
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h1
      simp only [GateOp.eval, Bool.eq_false_iff, ne_eq, List.any_eq_true, List.mem_map, id] at h2
      obtain ⟨b, ⟨v, hv, rfl⟩, hb⟩ := h1
      refine ⟨v, hb, ?_⟩
      by_contra hc
      exact h2 ⟨_, ⟨v, hv, rfl⟩, by simpa using hc⟩
    · exact absurd ho hn
  have hN : nf.card ≤ (falls X k).card + 1 := by
    rcases hins : g.inputs with _ | ⟨v, rest⟩
    · have : nf = ∅ := by
        rw [hnf]; apply Finset.filter_false_of_mem
        intro j _ ⟨h1, h2⟩
        unfold value at h1 h2
        rw [hins] at h1 h2
        rcases hg with ho | ho | ho <;> rw [ho] at h1 h2 <;> simp [GateOp.eval] at h1 h2
      rw [this]; simp
    · by_cases ho : g.op = GateOp.not
      · let u : ℕ → Bool := fun j => (X j).getD v false
        have e1 : nf = (Finset.range k).filter (fun j => u j = false ∧ u (j+1) = true) := by
          rw [hnf]; apply Finset.filter_congr
          intro j _
          unfold value; rw [hins, ho]
          simp [GateOp.eval, u]
        have e2 : (Finset.range k).filter (fun j => u j = true ∧ u (j+1) = false) ⊆ falls X k := by
          intro j hj
          rw [Finset.mem_filter, Finset.mem_range] at hj
          exact mem_falls.2 ⟨hj.1, v, hj.2.1, hj.2.2⟩
        rw [e1]
        exact (rise_le_fall u k).trans (Nat.add_le_add_right (Finset.card_le_card e2) 1)
      · exact (Finset.card_le_card (hAO ho)).trans (Nat.le_succ _)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  refine ⟨fun hn => ?_, by omega⟩
  have := Finset.card_le_card (Finset.union_subset (le_refl (falls X k)) (hAO hn))
  have h3 := (Finset.card_le_card hsub).trans this
  exact h3

lemma nc_cons_not (l : List Gate) (g : Gate) (h : g.op = GateOp.not) :
    notCount ⟨g :: l, 0⟩ = notCount ⟨l, 0⟩ + 1 := by
  simp [notCount, h]

lemma nc_cons_ne (l : List Gate) (g : Gate) (h : g.op ≠ GateOp.not) :
    notCount ⟨g :: l, 0⟩ = notCount ⟨l, 0⟩ := by
  simp [notCount, h]

lemma falls_run (k : ℕ) : ∀ (gs : List Gate) (X : ℕ → List Bool) (L r : ℕ),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    (∀ j, j ≤ k → (X j).length = L) →
    (falls X k).card + 1 ≤ 2 ^ r →
    (falls (fun j => run gs (X j)) k).card + 1 ≤ 2 ^ (r + notCount ⟨gs, 0⟩) := by
  intro gs
  induction gs with
  | nil => intro X L r _ _ h; simpa [run, notCount] using h
  | cons g gs ih =>
    intro X L r hops hL hc
    have hg := hops g (by simp)
    obtain ⟨hA, hB⟩ := falls_step X k L hL g hg
    have hL' : ∀ j, j ≤ k → (X j ++ [value (X j) g]).length = L + 1 := by
      intro j hj; simp [hL j hj]
    have hops' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not :=
      fun g' hg' => hops g' (by simp [hg'])
    show (falls (fun j => run gs (X j ++ [value (X j) g])) k).card + 1 ≤ _
    by_cases hn : g.op = GateOp.not
    · have hc' : (falls (fun j => X j ++ [value (X j) g]) k).card + 1 ≤ 2 ^ (r + 1) := by
        rw [pow_succ]; omega
      have := ih _ _ _ hops' hL' hc'
      rw [nc_cons_not gs g hn, show r + (notCount ⟨gs, 0⟩ + 1) = r + 1 + notCount ⟨gs, 0⟩ by omega]
      exact this
    · have hc' : (falls (fun j => X j ++ [value (X j) g]) k).card + 1 ≤ 2 ^ r := by
        have := hA hn; omega
      have := ih _ _ _ hops' hL' hc'
      rw [nc_cons_ne gs g hn]
      exact this

/-- A fall of a toggling sequence between two toggles. -/
lemma fall_between (u : ℕ → Bool) : ∀ (d a : ℕ), u a = true → u (a + d) = false →
    ∃ j, a ≤ j ∧ j < a + d ∧ u j = true ∧ u (j+1) = false := by
  intro d
  induction d with
  | zero => intro a h1 h2; simp at h2; rw [h1] at h2; exact absurd h2 (by simp)
  | succ d ih =>
    intro a h1 h2
    cases h : u (a + 1)
    · exact ⟨a, le_refl _, by omega, h1, h⟩
    · obtain ⟨j, hj1, hj2, hj3, hj4⟩ := ih (a+1) h (by rw [show a + 1 + d = a + (d+1) by omega]; exact h2)
      exact ⟨j, by omega, by omega, hj3, hj4⟩

lemma fall_in (u : ℕ → Bool) (lo hi : ℕ) (hlh : lo < hi) (h1 : u lo ≠ u (lo+1))
    (h2 : u hi ≠ u (hi+1)) : ∃ j, lo ≤ j ∧ j ≤ hi ∧ u j = true ∧ u (j+1) = false := by
  cases hl : u lo
  · have hl1 : u (lo + 1) = true := by rw [hl] at h1; cases h : u (lo+1) <;> simp_all
    cases hh : u hi
    · obtain ⟨j, hj1, hj2, hj3, hj4⟩ := fall_between u (hi - (lo+1)) (lo+1) hl1
        (by rw [show lo + 1 + (hi - (lo + 1)) = hi by omega]; exact hh)
      exact ⟨j, by omega, by omega, hj3, hj4⟩
    · have : u (hi+1) = false := by rw [hh] at h2; cases h : u (hi+1) <;> simp_all
      exact ⟨hi, by omega, le_refl _, hh, this⟩
  · have : u (lo+1) = false := by rw [hl] at h1; cases h : u (lo+1) <;> simp_all
    exact ⟨lo, le_refl _, by omega, hl, this⟩

/-- Locality: two inputs agreeing on every read position give the same gate values. -/
lemma run_local (gs : List Gate) : ∀ (x x' E0 : List Bool), x.length = x'.length →
    (∀ g ∈ gs, ∀ v ∈ g.inputs, v < x.length → x.getD v false = x'.getD v false) →
    ∃ E, run gs (x ++ E0) = x ++ E ∧ run gs (x' ++ E0) = x' ++ E := by
  induction gs with
  | nil => intro x x' E0 _ _; exact ⟨E0, rfl, rfl⟩
  | cons g gs ih =>
    intro x x' E0 hl hag
    have hv : value (x ++ E0) g = value (x' ++ E0) g := by
      unfold value; congr 1
      apply List.map_congr_left
      intro v hv
      by_cases hvl : v < x.length
      · rw [List.getD_append _ _ _ _ hvl, List.getD_append _ _ _ _ (by omega)]
        exact hag g (by simp) v hv hvl
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    obtain ⟨E, h1, h2⟩ := ih x x' (E0 ++ [value (x ++ E0) g]) hl
      (fun g' hg' => hag g' (by simp [hg']))
    refine ⟨E, ?_, ?_⟩
    · rw [run_cons, List.append_assoc]; exact h1
    · rw [run_cons, List.append_assoc, ← hv]; exact h2

lemma run_local_getD (gs : List Gate) (x x' : List Bool) (hl : x.length = x'.length)
    (hag : ∀ g ∈ gs, ∀ v ∈ g.inputs, v < x.length → x.getD v false = x'.getD v false)
    (p : ℕ) (hp : p < x.length → x.getD p false = x'.getD p false) :
    (run gs x).getD p false = (run gs x').getD p false := by
  obtain ⟨E, h1, h2⟩ := run_local gs x x' [] hl hag
  simp only [List.append_nil] at h1 h2
  rw [h1, h2]
  by_cases hpl : p < x.length
  · rw [List.getD_append _ _ _ _ hpl, List.getD_append _ _ _ _ (by omega)]; exact hp hpl
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]


/-! ## Greedy runs -/

def st (nm : ℕ → ℕ) : ℕ → Finset ℕ × ℕ
  | 0 => (∅, 0)
  | j+1 => if nm j ∈ (st nm j).1 then (∅, (st nm j).2 + 1)
    else (insert (nm j) (st nm j).1, (st nm j).2)

def isEnd (nm : ℕ → ℕ) (j : ℕ) : Prop := nm j ∈ (st nm j).1

instance (nm : ℕ → ℕ) (j : ℕ) : Decidable (isEnd nm j) := by unfold isEnd; infer_instance

def R (nm : ℕ → ℕ) (j : ℕ) : ℕ := (st nm j).2

lemma R_zero (nm : ℕ → ℕ) : R nm 0 = 0 := rfl

lemma R_succ_end {nm : ℕ → ℕ} {j : ℕ} (h : isEnd nm j) : R nm (j+1) = R nm j + 1 := by
  unfold isEnd at h; simp [R, st, h]

lemma R_succ_not {nm : ℕ → ℕ} {j : ℕ} (h : ¬ isEnd nm j) : R nm (j+1) = R nm j := by
  unfold isEnd at h; simp [R, st, h]

lemma R_succ_le (nm : ℕ → ℕ) (j : ℕ) : R nm (j+1) ≤ R nm j + 1 := by
  by_cases h : isEnd nm j
  · rw [R_succ_end h]
  · rw [R_succ_not h]; omega

lemma R_mono (nm : ℕ → ℕ) {j j' : ℕ} (h : j ≤ j') : R nm j ≤ R nm j' := by
  induction j' with
  | zero => have : j = 0 := by omega
            subst this; exact le_refl _
  | succ j' ih =>
    rcases Nat.lt_or_ge j (j'+1) with hj | hj
    · have := ih (by omega)
      by_cases he : isEnd nm j'
      · rw [R_succ_end he]; omega
      · rw [R_succ_not he]; omega
    · have : j = j' + 1 := by omega
      subst this; exact le_refl _

lemma mem_S (nm : ℕ → ℕ) : ∀ j a, a ∈ (st nm j).1 ↔ ∃ i < j, nm i = a ∧ R nm i = R nm j := by
  intro j
  induction j with
  | zero => intro a; simp [st]
  | succ j ih =>
    intro a
    by_cases h : nm j ∈ (st nm j).1
    · have hR : R nm (j+1) = R nm j + 1 := R_succ_end h
      have e : (st nm (j+1)).1 = ∅ := by simp [st, h]
      rw [e, hR]
      simp only [Finset.notMem_empty, false_iff, not_exists, not_and]
      intro i hi _ hRi
      have := R_mono nm (show i ≤ j by omega)
      omega
    · have hR : R nm (j+1) = R nm j := R_succ_not h
      have e : (st nm (j+1)).1 = insert (nm j) (st nm j).1 := by simp [st, h]
      rw [e, hR, Finset.mem_insert, ih a]
      constructor
      · rintro (rfl | ⟨i, hi, h1, h2⟩)
        · exact ⟨j, by omega, rfl, rfl⟩
        · exact ⟨i, by omega, h1, h2⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_or_ge i j with hij | hij
        · exact Or.inr ⟨i, hij, h1, h2⟩
        · have : i = j := by omega
          subst this; exact Or.inl h1.symm

lemma isEnd_iff (nm : ℕ → ℕ) (j : ℕ) :
    isEnd nm j ↔ ∃ i < j, nm i = nm j ∧ R nm i = R nm j := mem_S nm j (nm j)

lemma two_R_le (nm : ℕ → ℕ) : ∀ j, 2 * R nm j ≤ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => simp [R_zero]
    | succ j =>
      by_cases he : isEnd nm j
      · rw [R_succ_end he]
        obtain ⟨i, hi, _, hR⟩ := (isEnd_iff nm j).1 he
        have := ih i (by omega)
        omega
      · rw [R_succ_not he]
        have := ih j (by omega)
        omega

lemma exists_end (nm : ℕ → ℕ) : ∀ j r, r < R nm j → ∃ i < j, isEnd nm i ∧ R nm i = r := by
  intro j
  induction j with
  | zero => intro r hr; simp [R_zero] at hr
  | succ j ih =>
    intro r hr
    by_cases he : isEnd nm j
    · rw [R_succ_end he] at hr
      rcases Nat.lt_or_ge r (R nm j) with h | h
      · obtain ⟨i, hi, h1, h2⟩ := ih r h; exact ⟨i, by omega, h1, h2⟩
      · exact ⟨j, by omega, he, by omega⟩
    · rw [R_succ_not he] at hr
      obtain ⟨i, hi, h1, h2⟩ := ih r hr; exact ⟨i, by omega, h1, h2⟩

open Classical in
noncomputable def eEnd (nm : ℕ → ℕ) (K r : ℕ) : ℕ :=
  if h : ∃ i, i < K ∧ isEnd nm i ∧ R nm i = r then Classical.choose h else 0

lemma eEnd_spec (nm : ℕ → ℕ) (K r : ℕ) (hr : r < R nm K) :
    eEnd nm K r < K ∧ isEnd nm (eEnd nm K r) ∧ R nm (eEnd nm K r) = r := by
  have h : ∃ i, i < K ∧ isEnd nm i ∧ R nm i = r := by
    obtain ⟨i, hi, h1, h2⟩ := exists_end nm K r hr; exact ⟨i, hi, h1, h2⟩
  unfold eEnd; rw [dif_pos h]; exact Classical.choose_spec h

lemma R_le_of_le_end (nm : ℕ → ℕ) (K r j : ℕ) (hr : r < R nm K) (hj : j ≤ eEnd nm K r) :
    R nm j ≤ r := by
  have := R_mono nm hj
  rw [(eEnd_spec nm K r hr).2.2] at this
  exact this

lemma end_ge (nm : ℕ → ℕ) (K i : ℕ) (hr : R nm i < R nm K) : i ≤ eEnd nm K (R nm i) := by
  obtain ⟨_, he, hR⟩ := eEnd_spec nm K (R nm i) hr
  by_contra hlt
  push Not at hlt
  have h1 := R_succ_end he
  have h2 := R_mono nm (show eEnd nm K (R nm i) + 1 ≤ i by omega)
  omega

lemma eEnd_mono (nm : ℕ → ℕ) (K r r' : ℕ) (hrr : r ≤ r') (hr' : r' < R nm K) :
    eEnd nm K r ≤ eEnd nm K r' := by
  rcases Nat.eq_or_lt_of_le hrr with rfl | hlt
  · exact le_refl _
  · by_contra h
    push Not at h
    have := R_mono nm h.le
    rw [(eEnd_spec nm K r (by omega)).2.2, (eEnd_spec nm K r' hr').2.2] at this
    omega

/-- The value a tap takes at chain point `j`. -/
def Tval (nm : ℕ → ℕ) (K j a : ℕ) : Prop :=
  ∃ i < K, nm i = a ∧ i < j ∧ (R nm i < R nm K → j ≤ eEnd nm K (R nm i))

lemma Tval_notEnd (nm : ℕ → ℕ) (K i : ℕ) (hi : i < K) (he : ¬ isEnd nm i) :
    ¬ Tval nm K i (nm i) ∧ Tval nm K (i+1) (nm i) := by
  have hRK : R nm i ≤ R nm K := R_mono nm hi.le
  constructor
  · rintro ⟨i', _, hnm, hlt, hle⟩
    have hRi' := R_mono nm hlt.le
    rcases Nat.eq_or_lt_of_le hRi' with heq | hlt'
    · exact he ((isEnd_iff nm i).2 ⟨i', hlt, hnm, heq⟩)
    · have h1 := hle (by omega)
      have := R_le_of_le_end nm K (R nm i') i (by omega) h1
      omega
  · refine ⟨i, hi, rfl, by omega, fun hr => ?_⟩
    have h1 := end_ge nm K i hr
    have h2 := (eEnd_spec nm K (R nm i) hr).2.1
    rcases Nat.eq_or_lt_of_le h1 with heq | hlt
    · rw [← heq] at h2; exact absurd h2 he
    · omega

lemma Tval_end (nm : ℕ → ℕ) (K i : ℕ) (hi : i < K) (he : isEnd nm i) :
    Tval nm K i (nm i) ∧ ¬ Tval nm K (i+1) (nm i) := by
  have hRK : R nm (i+1) ≤ R nm K := R_mono nm (by omega)
  have hRs := R_succ_end he
  constructor
  · obtain ⟨i', hi', hnm, hR⟩ := (isEnd_iff nm i).1 he
    refine ⟨i', by omega, hnm, hi', fun hr => ?_⟩
    rw [hR] at hr ⊢
    exact end_ge nm K i hr
  · rintro ⟨i', _, _, hlt, hle⟩
    have hRi' := R_mono nm (show i' ≤ i by omega)
    have h1 := hle (by omega)
    have := R_le_of_le_end nm K (R nm i') (i+1) (by omega) h1
    omega

/-- `last nm a j`: the last step before `j` named `a`. -/
def last (nm : ℕ → ℕ) (a : ℕ) : ℕ → Option ℕ
  | 0 => none
  | j+1 => if nm j = a then some j else last nm a j

lemma last_some (nm : ℕ → ℕ) (a : ℕ) : ∀ j p, last nm a j = some p →
    p < j ∧ nm p = a ∧ ∀ q, p < q → q < j → nm q ≠ a := by
  intro j
  induction j with
  | zero => intro p h; simp [last] at h
  | succ j ih =>
    intro p h
    by_cases hj : nm j = a
    · simp only [last, hj, if_true, Option.some.injEq] at h
      subst h
      exact ⟨by omega, hj, fun q h1 h2 => by omega⟩
    · simp only [last, hj, if_false] at h
      obtain ⟨h1, h2, h3⟩ := ih p h
      refine ⟨by omega, h2, fun q hq1 hq2 => ?_⟩
      rcases Nat.lt_or_ge q j with hq | hq
      · exact h3 q hq1 hq
      · have : q = j := by omega
        subst this; exact hj

lemma last_none (nm : ℕ → ℕ) (a : ℕ) : ∀ j, last nm a j = none → ∀ q < j, nm q ≠ a := by
  intro j
  induction j with
  | zero => intro _ q hq; omega
  | succ j ih =>
    intro h q hq
    by_cases hj : nm j = a
    · simp [last, hj] at h
    · simp only [last, hj, if_false] at h
      rcases Nat.lt_or_ge q j with hq' | hq'
      · exact ih h q hq'
      · have : q = j := by omega
        subst this; exact hj

def optW (o : Option ℕ) (base dflt : ℕ) : ℕ :=
  match o with
  | some p => base + p
  | none => dflt

/-- The OR chains: the wire of step `i` collects every earlier step with the same name. -/
lemma orchain (nm : ℕ → ℕ) (V : ℕ → Bool) (K B A n : ℕ) (hn : V n = false)
    (hOr : ∀ i < K, V (B + i) = (V (optW (last nm (nm i) i) B n) || V (A + i))) :
    ∀ i < K, (V (B + i) = true ↔ ∃ i' ≤ i, nm i' = nm i ∧ V (A + i') = true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rw [hOr i hi]
    rcases hl : last nm (nm i) i with _ | p
    · have hno := last_none nm (nm i) i hl
      simp only [optW, hn, Bool.false_or]
      constructor
      · intro h; exact ⟨i, le_refl _, rfl, h⟩
      · rintro ⟨i', hi', hnm, hv⟩
        rcases Nat.eq_or_lt_of_le hi' with rfl | hlt
        · exact hv
        · exact absurd hnm (hno i' hlt)
    · obtain ⟨hp, hnp, hq⟩ := last_some nm (nm i) i p hl
      simp only [optW, Bool.or_eq_true]
      rw [ih p hp (by omega), hnp]
      constructor
      · rintro (⟨i', hi', hnm, hv⟩ | h)
        · exact ⟨i', by omega, hnm, hv⟩
        · exact ⟨i, le_refl _, rfl, h⟩
      · rintro ⟨i', hi', hnm, hv⟩
        rcases Nat.eq_or_lt_of_le hi' with rfl | hlt
        · exact Or.inr hv
        · left
          refine ⟨i', ?_, hnm, hv⟩
          by_contra hc
          exact hq i' (by omega) hlt hnm

lemma tapval (nm : ℕ → ℕ) (V : ℕ → Bool) (K B A n : ℕ) (hn : V n = false)
    (hOr : ∀ i < K, V (B + i) = (V (optW (last nm (nm i) i) B n) || V (A + i))) (a : ℕ) :
    V (optW (last nm a K) B n) = true ↔ ∃ i' < K, nm i' = a ∧ V (A + i') = true := by
  rcases hl : last nm a K with _ | p
  · have hno := last_none nm a K hl
    simp only [optW, hn, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro i' hi' hnm; exact absurd hnm (hno i' hi')
  · obtain ⟨hp, hnp, hq⟩ := last_some nm a K p hl
    simp only [optW]
    rw [orchain nm V K B A n hn hOr p hp, hnp]
    constructor
    · rintro ⟨i', hi', hnm, hv⟩; exact ⟨i', by omega, hnm, hv⟩
    · rintro ⟨i', hi', hnm, hv⟩
      refine ⟨i', ?_, hnm, hv⟩
      by_contra hc
      exact hq i' (by omega) hi' hnm

/-! ## The halving network: negating a sorted list of wires -/

def gAnd (a b : ℕ) : Gate := ⟨GateOp.and, [a, b]⟩
def gOr (a b : ℕ) : Gate := ⟨GateOp.or, [a, b]⟩
def gNot (a : ℕ) : Gate := ⟨GateOp.not, [a]⟩

@[simp] lemma eval_gAnd (V : ℕ → Bool) (a b : ℕ) :
    (gAnd a b).op.eval ((gAnd a b).inputs.map V) = (V a && V b) := by
  simp [gAnd, GateOp.eval]

@[simp] lemma eval_gOr (V : ℕ → Bool) (a b : ℕ) :
    (gOr a b).op.eval ((gOr a b).inputs.map V) = (V a || V b) := by
  simp [gOr, GateOp.eval]

@[simp] lemma eval_gNot (V : ℕ → Bool) (a : ℕ) :
    (gNot a).op.eval ((gNot a).inputs.map V) = !V a := by
  simp [gNot, GateOp.eval]

def negG (f0 : ℕ) : ℕ → ℕ → ℕ → (ℕ → ℕ) → List Gate × (ℕ → ℕ)
  | 0, _, _, _ => ([], fun _ => 0)
  | fuel+1, base, m, u =>
    if m = 0 then ([], fun _ => 0) else
    ([gNot (u (m/2))] ++ List.ofFn (fun r : Fin (m/2) => gAnd (u r) base)
       ++ List.ofFn (fun r : Fin (m/2) =>
            gOr (base + 1 + r) (if m/2 + 1 + r < m then u (m/2 + 1 + r) else f0))
       ++ (negG f0 fuel (base + 1 + 2*(m/2)) (m/2) (fun r => base + 1 + m/2 + r)).1
       ++ List.ofFn (fun r : Fin (m/2) =>
            gAnd base ((negG f0 fuel (base + 1 + 2*(m/2)) (m/2) (fun r => base + 1 + m/2 + r)).2 r))
       ++ List.ofFn (fun r : Fin (m - 1 - m/2) =>
            gOr base ((negG f0 fuel (base + 1 + 2*(m/2)) (m/2) (fun r => base + 1 + m/2 + r)).2 r)),
     fun r => if r < m/2 then base + 1 + 2*(m/2) +
         (negG f0 fuel (base + 1 + 2*(m/2)) (m/2) (fun r => base + 1 + m/2 + r)).1.length + r
       else if r = m/2 then base
       else base + 1 + 2*(m/2) +
         (negG f0 fuel (base + 1 + 2*(m/2)) (m/2) (fun r => base + 1 + m/2 + r)).1.length + m/2 +
           (r - m/2 - 1))

def negSub (f0 fuel base m : ℕ) : List Gate × (ℕ → ℕ) :=
  negG f0 fuel (base + 1 + 2*(m/2)) (m/2) (fun r => base + 1 + m/2 + r)

lemma negG_succ (f0 fuel base m : ℕ) (u : ℕ → ℕ) (hm : m ≠ 0) :
    negG f0 (fuel+1) base m u =
    ([gNot (u (m/2))] ++ List.ofFn (fun r : Fin (m/2) => gAnd (u r) base)
       ++ List.ofFn (fun r : Fin (m/2) =>
            gOr (base + 1 + r) (if m/2 + 1 + r < m then u (m/2 + 1 + r) else f0))
       ++ (negSub f0 fuel base m).1
       ++ List.ofFn (fun r : Fin (m/2) => gAnd base ((negSub f0 fuel base m).2 r))
       ++ List.ofFn (fun r : Fin (m - 1 - m/2) => gOr base ((negSub f0 fuel base m).2 r)),
     fun r => if r < m/2 then base + 1 + 2*(m/2) + (negSub f0 fuel base m).1.length + r
       else if r = m/2 then base
       else base + 1 + 2*(m/2) + (negSub f0 fuel base m).1.length + m/2 + (r - m/2 - 1)) := by
  rw [negG, if_neg hm]; rfl

lemma nc_append (A B : List Gate) :
    notCount ⟨A ++ B, 0⟩ = notCount ⟨A, 0⟩ + notCount ⟨B, 0⟩ := by
  simp [notCount, List.filter_append]

lemma nc_ofFn_zero {M : ℕ} (f : Fin M → Gate) (h : ∀ r, (f r).op ≠ GateOp.not) :
    notCount ⟨List.ofFn f, 0⟩ = 0 := by
  unfold notCount
  simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, List.mem_ofFn, decide_eq_true_eq]
  rintro g ⟨r, rfl⟩
  exact h r

lemma nc_gNot (a : ℕ) : notCount ⟨[gNot a], 0⟩ = 1 := by
  simp [notCount, gNot]

lemma negG_len (f0 : ℕ) : ∀ fuel base m u, (negG f0 fuel base m u).1.length ≤ 4 * m := by
  intro fuel
  induction fuel with
  | zero => intro base m u; simp [negG]
  | succ fuel ih =>
    intro base m u
    by_cases hm : m = 0
    · simp [negG, hm]
    · rw [negG_succ f0 fuel base m u hm]
      have ih' : (negSub f0 fuel base m).1.length ≤ 4 * (m/2) := ih _ _ _
      simp only [List.length_append, List.length_ofFn, List.length_singleton]
      omega

lemma negG_nots (f0 : ℕ) : ∀ fuel base m u c, m < 2 ^ c →
    notCount ⟨(negG f0 fuel base m u).1, 0⟩ ≤ c := by
  intro fuel
  induction fuel with
  | zero => intro base m u c _; simp [negG, notCount]
  | succ fuel ih =>
    intro base m u c hc
    by_cases hm : m = 0
    · simp [negG, hm, notCount]
    · rw [negG_succ f0 fuel base m u hm]
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := by
        rcases c with _ | c'
        · simp at hc; omega
        · exact ⟨c', rfl⟩
      have ih' : notCount ⟨(negSub f0 fuel base m).1, 0⟩ ≤ c' :=
        ih _ _ _ _ (by rw [pow_succ] at hc; omega)
      simp only [nc_append, nc_gNot]
      rw [nc_ofFn_zero _ (fun r => by simp [gAnd]), nc_ofFn_zero _ (fun r => by simp [gOr]),
        nc_ofFn_zero _ (fun r => by simp [gAnd]), nc_ofFn_zero _ (fun r => by simp [gOr])]
      omega

lemma negG_ops (f0 : ℕ) : ∀ fuel base m u, ∀ g ∈ (negG f0 fuel base m u).1,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  intro fuel
  induction fuel with
  | zero => intro base m u g hg; simp [negG] at hg
  | succ fuel ih =>
    intro base m u g hg
    by_cases hm : m = 0
    · simp [negG, hm] at hg
    · rw [negG_succ f0 fuel base m u hm] at hg
      simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hg
      rcases hg with ((((rfl | ⟨r, rfl⟩) | ⟨r, rfl⟩) | hg) | ⟨r, rfl⟩) | ⟨r, rfl⟩
      · simp [gNot]
      · simp [gAnd]
      · simp [gOr]
      · exact ih _ _ _ g hg
      · simp [gAnd]
      · simp [gOr]

lemma negG_outs (f0 : ℕ) : ∀ fuel base m u, m ≤ fuel → ∀ r < m,
    base ≤ (negG f0 fuel base m u).2 r ∧
      (negG f0 fuel base m u).2 r < base + (negG f0 fuel base m u).1.length := by
  intro fuel
  cases fuel with
  | zero => intro base m u hm r hr; omega
  | succ fuel =>
    intro base m u _ r hr
    have hm : m ≠ 0 := by omega
    rw [negG_succ f0 fuel base m u hm]
    simp only [List.length_append, List.length_ofFn, List.length_singleton]
    split_ifs <;> omega

lemma negG_inputs (f0 : ℕ) : ∀ fuel base m u, m ≤ fuel → ∀ g ∈ (negG f0 fuel base m u).1,
    ∀ v ∈ g.inputs, (∃ r < m, v = u r) ∨ v = f0 ∨ base ≤ v := by
  intro fuel
  induction fuel with
  | zero => intro base m u _ g hg; simp [negG] at hg
  | succ fuel ih =>
    intro base m u hmf g hg v hv
    by_cases hm : m = 0
    · simp [negG, hm] at hg
    · rw [negG_succ f0 fuel base m u hm] at hg
      have hso : ∀ r < m/2, base ≤ (negSub f0 fuel base m).2 r := fun r hr =>
        le_trans (by omega) (negG_outs f0 fuel _ _ _ (by omega) r hr).1
      simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hg
      rcases hg with ((((rfl | ⟨r, rfl⟩) | ⟨r, rfl⟩) | hg) | ⟨r, rfl⟩) | ⟨r, rfl⟩
      · simp only [gNot, List.mem_singleton] at hv
        exact Or.inl ⟨m/2, by omega, hv⟩
      · simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact Or.inl ⟨r, by omega, rfl⟩
        · exact Or.inr (Or.inr (le_refl _))
      · simp only [gOr, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact Or.inr (Or.inr (by omega))
        · split_ifs with h
          · exact Or.inl ⟨_, h, rfl⟩
          · exact Or.inr (Or.inl rfl)
      · rcases ih _ _ _ (by omega) g hg v hv with ⟨r, hr, rfl⟩ | h | h
        · exact Or.inr (Or.inr (by omega))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by omega))
      · simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact Or.inr (Or.inr (le_refl _))
        · exact Or.inr (Or.inr (hso r (by omega)))
      · simp only [gOr, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact Or.inr (Or.inr (le_refl _))
        · exact Or.inr (Or.inr (hso r (by omega)))

lemma RB.append' {base b2 : ℕ} {A B : List Gate} (hA : RB base A) (hB : RB b2 B)
    (hb : b2 = base + A.length) : RB base (A ++ B) := by
  subst hb; exact RB.append hA hB

lemma negG_rb (f0 : ℕ) : ∀ fuel base m u, m ≤ fuel → (∀ r < m, u r < base) → f0 < base →
    RB base (negG f0 fuel base m u).1 := by
  intro fuel
  induction fuel with
  | zero => intro base m u _ _ _; intro j hj; simp [negG] at hj
  | succ fuel ih =>
    intro base m u hmf hu hf
    by_cases hm : m = 0
    · intro j hj; simp [negG, hm] at hj
    · rw [negG_succ f0 fuel base m u hm]
      have hso : ∀ r < m/2, (negSub f0 fuel base m).2 r <
          base + 1 + 2*(m/2) + (negSub f0 fuel base m).1.length := fun r hr =>
        (negG_outs f0 fuel _ _ _ (by omega) r hr).2
      have hS : RB (base + 1 + 2*(m/2)) (negSub f0 fuel base m).1 :=
        ih _ _ _ (by omega) (fun r hr => by omega) (by omega)
      refine RB.append' (RB.append' (RB.append' (RB.append' (RB.append' ?_ ?_ rfl) ?_ rfl) hS ?_)
        ?_ rfl) ?_ rfl
      · exact RB.single (fun v hv => by
          simp only [gNot, List.mem_singleton] at hv; subst hv; exact hu _ (by omega))
      · refine RB.ofFn (fun r v hv => ?_)
        simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hv
        simp only [List.length_singleton]
        rcases hv with rfl | rfl
        · have := hu r (by omega); omega
        · omega
      · refine RB.ofFn (fun r v hv => ?_)
        simp only [gOr, List.mem_cons, List.not_mem_nil, or_false] at hv
        simp only [List.length_append, List.length_singleton, List.length_ofFn]
        rcases hv with rfl | rfl
        · have := r.isLt; omega
        · split_ifs with h
          · have := hu _ h; omega
          · omega
      · simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega
      · refine RB.ofFn (fun r v hv => ?_)
        simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hv
        simp only [List.length_append, List.length_singleton, List.length_ofFn]
        rcases hv with rfl | rfl
        · omega
        · have := hso r r.isLt; omega
      · refine RB.ofFn (fun r v hv => ?_)
        simp only [gOr, List.mem_cons, List.not_mem_nil, or_false] at hv
        simp only [List.length_append, List.length_singleton, List.length_ofFn]
        rcases hv with rfl | rfl
        · omega
        · have := hso r (by have := r.isLt; omega); omega

lemma Cons.right' {V : ℕ → Bool} {base b2 : ℕ} {A B : List Gate} (h : Cons V base (A ++ B))
    (hb : base + A.length = b2) : Cons V b2 B := by
  subst hb; exact h.right

lemma Cons.ofFn' {V : ℕ → Bool} {b M : ℕ} {f : Fin M → Gate} (h : Cons V b (List.ofFn f))
    (r : ℕ) (hr : r < M) (p : ℕ) (hp : b + r = p) :
    V p = (f ⟨r, hr⟩).op.eval ((f ⟨r, hr⟩).inputs.map V) := by
  subst hp; exact h.ofFn ⟨r, hr⟩

lemma negG_correct (f0 : ℕ) : ∀ fuel base m u, m ≤ fuel → ∀ V : ℕ → Bool,
    Cons V base (negG f0 fuel base m u).1 → V f0 = false →
    (∀ r r', r ≤ r' → r' < m → V (u r') = true → V (u r) = true) →
    ∀ r < m, V ((negG f0 fuel base m u).2 r) = !V (u r) := by
  intro fuel
  induction fuel with
  | zero => intro base m u hm V _ _ _ r hr; omega
  | succ fuel ih =>
    intro base m u hmf V hC hf0 hth r hr
    have hm : m ≠ 0 := by omega
    rw [negG_succ f0 fuel base m u hm] at hC ⊢
    set M := m / 2 with hM
    set S := negSub f0 fuel base m with hSdef
    set B := base + 1 + 2*M + S.1.length with hB
    have hU := hC.right' (b2 := B + M) (by
      simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega)
    have h5 := hC.left
    have hL := h5.right' (b2 := B) (by
      simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega)
    have h4 := h5.left
    have hS := h4.right' (b2 := base + 1 + 2*M) (by
      simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega)
    have h3 := h4.left
    have hO := h3.right' (b2 := base + 1 + M) (by
      simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega)
    have h2 := h3.left
    have hA := h2.right' (b2 := base + 1) (by simp only [List.length_singleton])
    have hN := h2.left.single
    simp only [eval_gNot] at hN
    have hAv : ∀ r < M, V (base + 1 + r) = (V (u r) && V base) := fun r hr' => by
      have := hA.ofFn' r hr' _ rfl; simpa using this
    have hOv : ∀ r < M, V (base + 1 + M + r) =
        (V (base + 1 + r) || V (if M + 1 + r < m then u (M + 1 + r) else f0)) := fun r hr' => by
      have := hO.ofFn' r hr' _ rfl; simpa using this
    have hLv : ∀ r < M, V (B + r) = (V base && V (S.2 r)) := fun r hr' => by
      have := hL.ofFn' r hr' _ rfl; simpa using this
    have hUv : ∀ r < m - 1 - M, V (B + M + r) = (V base || V (S.2 r)) := fun r hr' => by
      have := hU.ofFn' r hr' _ rfl; simpa using this
    -- values of the merged list
    have hvT : V base = true → ∀ r < M, V (base + 1 + M + r) = V (u r) := by
      intro hz r hr'
      have huM : V (u M) = false := by rw [hz] at hN; cases h : V (u M) <;> simp_all
      rw [hOv r hr', hAv r hr', hz]
      split_ifs with h
      · have : V (u (M + 1 + r)) = false := by
          cases h' : V (u (M + 1 + r))
          · rfl
          · have := hth M (M + 1 + r) (by omega) h h'; rw [huM] at this; exact absurd this (by simp)
        rw [this]; simp
      · rw [hf0]; simp
    have hvF : V base = false → ∀ r < M, V (base + 1 + M + r) =
        (decide (M + 1 + r < m) && V (u (M + 1 + r))) := by
      intro hz r hr'
      rw [hOv r hr', hAv r hr', hz]
      split_ifs with h
      · simp [h]
      · simp [h, hf0]
    have hthv : ∀ r r', r ≤ r' → r' < M → V (base + 1 + M + r') = true →
        V (base + 1 + M + r) = true := by
      intro r1 r2 h12 h2M hv
      cases hz : V base
      · rw [hvF hz r2 h2M] at hv
        rw [hvF hz r1 (by omega)]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
        exact ⟨by omega, hth _ _ (by omega) hv.1 hv.2⟩
      · rw [hvT hz r2 h2M] at hv
        rw [hvT hz r1 (by omega)]
        exact hth _ _ h12 (by omega) hv
    have hSc : ∀ r < M, V (S.2 r) = !V (base + 1 + M + r) := fun r hr' =>
      ih (base + 1 + 2*M) M (fun r => base + 1 + M + r) (by omega) V hS hf0 hthv r hr'
    show V (if r < M then B + r else if r = M then base else B + M + (r - M - 1)) = !V (u r)
    split_ifs with h1 h2
    · rw [hLv r h1, hSc r h1]
      cases hz : V base
      · have huM : V (u M) = true := by rw [hz] at hN; cases h : V (u M) <;> simp_all
        have := hth r M (by omega) (by omega) huM
        rw [this]; simp
      · rw [hvT hz r h1]; simp
    · subst h2; exact hN
    · have hr' : r - M - 1 < m - 1 - M := by omega
      rw [hUv _ hr', hSc _ (by omega)]
      cases hz : V base
      · rw [hvF hz _ (by omega)]
        have e : M + 1 + (r - M - 1) = r := by omega
        rw [e]; simp [hr]
      · have huM : V (u M) = false := by rw [hz] at hN; cases h : V (u M) <;> simp_all
        have : V (u r) = false := by
          cases h' : V (u r)
          · rfl
          · have := hth M r (by omega) hr h'; rw [huM] at this; exact absurd this (by simp)
        rw [this]; simp

/-! ## The lower bound -/

theorem lower (t k b n : ℕ) (name : Fin k → Fin t) (addr : Fin k → Fin t → Bool → ℕ)
    (raw : Fin k → (Fin t → Bool) → List Bool)
    (haddr_lt : ∀ h a s (j : ℕ), addr h a s < 2 * t * j ↔ h.val < j)
    (hraw_len : ∀ i w, (raw i w).length = n + 2)
    (hraw_n : ∀ i w, (raw i w).getD n false = false)
    (hraw_n1 : ∀ i w, (raw i w).getD (n+1) false = true)
    (hraw_addr : ∀ i w h a s, (raw i w).getD (addr h a s) false = true ↔
      (h < i ∨ (h = i ∧ w a = s)))
    (C : Circuit) (tap : Fin t → ℕ) (side : Fin k → Bool)
    (hf : FanInTwo C) (hnot : notCount C ≤ b)
    (hreads : ∀ v, v < n → ((∃ g ∈ C.gates, v ∈ g.inputs) ∨ (∃ a, tap a = v) ∨ C.output = v) →
        ∃ i, v = addr i (name i) (side i))
    (hfit : ∀ (i : Fin k) (w : Fin t → Bool), ∃ a, (C.wires (raw i w)).getD (tap a) false ≠ w a) :
    ¬ ∃ lo hi : Fin (2^b) → Fin k, (∀ j, lo j < hi j ∧ name (lo j) = name (hi j)) ∧
        (∀ j h, j < h → hi j < lo h) := by
  rintro ⟨lo, hi, hpair, hord⟩
  let Z : ℕ → List Bool := fun j =>
    List.ofFn (fun v : Fin n => decide (v.val < 2*t*j)) ++ [false, true]
  have hZlen : ∀ j, (Z j).length = n + 2 := fun j => by simp [Z]
  have hZget : ∀ j p, (Z j).getD p false =
      if h : p < n then decide (p < 2*t*j) else decide (p = n+1) := fun j p => getD_inp _ p
  have hZmono : falls Z k = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    obtain ⟨_, p, h1, h2⟩ := mem_falls.1 hj
    rw [hZget] at h1 h2
    by_cases hp : p < n
    · rw [dif_pos hp] at h1 h2
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_lt] at h1 h2
      have : 2*t*j ≤ 2*t*(j+1) := Nat.mul_le_mul_left _ (by omega)
      omega
    · rw [dif_neg hp] at h1 h2
      rw [h1] at h2; exact absurd h2 (by simp)
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    have := (hf g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    exact this
  have hcard := falls_run k C.gates Z (n+2) 0 hops (fun j _ => hZlen j) (by rw [hZmono]; simp)
  have hcard' : (falls (fun j => run C.gates (Z j)) k).card + 1 ≤ 2 ^ b := by
    refine hcard.trans ?_
    apply Nat.pow_le_pow_right (by norm_num)
    rw [Nat.zero_add]
    exact hnot
  have hpos : ∀ (i : Fin k) (w : Fin t → Bool) (v : ℕ), v < n + 2 →
      (v < n → ∃ h, v = addr h (name h) (side h)) →
      (raw i w).getD v false =
        (Z (if w (name i) = side i then i.val + 1 else i.val)).getD v false := by
    intro i w v hv hrail
    rw [hZget]
    by_cases hvn : v < n
    · rw [dif_pos hvn]
      obtain ⟨h, rfl⟩ := hrail hvn
      apply Bool.eq_iff_iff.2
      rw [hraw_addr, decide_eq_true_iff, haddr_lt, Fin.lt_def]
      split_ifs with hw
      · constructor
        · rintro (hlt | ⟨rfl, _⟩)
          · omega
          · omega
        · intro hlt
          rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
          · exact Or.inl hlt
          · have : h = i := Fin.ext heq
            subst this; exact Or.inr ⟨rfl, hw⟩
      · constructor
        · rintro (hlt | ⟨rfl, hws⟩)
          · exact hlt
          · exact absurd hws hw
        · intro hlt; exact Or.inl hlt
    · rw [dif_neg hvn]
      rcases (by omega : v = n ∨ v = n + 1) with rfl | rfl
      · rw [hraw_n]; simp
      · rw [hraw_n1]; simp
  let T : ℕ → Fin t → Bool := fun j a => (run C.gates (Z j)).getD (tap a) false
  have hagree : ∀ (i : Fin k) (w : Fin t → Bool) a, (C.wires (raw i w)).getD (tap a) false =
      T (if w (name i) = side i then i.val + 1 else i.val) a := by
    intro i w a
    rw [wires_eq]
    show (run C.gates (raw i w)).getD (tap a) false =
      (run C.gates (Z (if w (name i) = side i then i.val + 1 else i.val))).getD (tap a) false
    apply run_local_getD
    · rw [hraw_len, hZlen]
    · intro g hg v hv hvl
      rw [hraw_len] at hvl
      exact hpos i w v hvl (fun hvn => hreads v hvn (Or.inl ⟨g, hg, hv⟩))
    · intro hp
      rw [hraw_len] at hp
      exact hpos i w _ hp (fun hvn => hreads _ hvn (Or.inr (Or.inl ⟨a, rfl⟩)))
  have htog : ∀ i : Fin k, T i.val (name i) ≠ T (i.val + 1) (name i) := by
    intro i heq
    let c := T i.val (name i)
    let j0 := if c = side i then i.val + 1 else i.val
    let w : Fin t → Bool := fun a => T j0 a
    have hw : w (name i) = c := by
      show T j0 (name i) = c
      by_cases h : c = side i
      · simp only [j0, if_pos h]; exact heq.symm
      · simp only [j0, if_neg h]; rfl
    have hj : (if w (name i) = side i then i.val + 1 else i.val) = j0 := by rw [hw]
    obtain ⟨a, ha⟩ := hfit i w
    rw [hagree, hj] at ha
    exact ha rfl
  have hfall : ∀ d : Fin (2^b), ∃ j, (lo d).val ≤ j ∧ j ≤ (hi d).val ∧
      j ∈ falls (fun j => run C.gates (Z j)) k := by
    intro d
    obtain ⟨hlh, hnm⟩ := hpair d
    let u : ℕ → Bool := fun j => T j (name (lo d))
    have h1 : u (lo d).val ≠ u ((lo d).val + 1) := htog (lo d)
    have h2 : u (hi d).val ≠ u ((hi d).val + 1) := by
      show T _ (name (lo d)) ≠ T _ (name (lo d)); rw [hnm]; exact htog (hi d)
    obtain ⟨j, hj1, hj2, hj3, hj4⟩ := fall_in u _ _ (Fin.lt_def.1 hlh) h1 h2
    exact ⟨j, hj1, hj2, mem_falls.2 ⟨by have := (hi d).isLt; omega, tap (name (lo d)), hj3, hj4⟩⟩
  choose f hf1 hf2 hf3 using hfall
  have hinj : Function.Injective f := by
    intro d d' hdd
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := Fin.lt_def.1 (hord d d' hlt)
      have := hf2 d; have := hf1 d'
      omega
    · have h1 := Fin.lt_def.1 (hord d' d hlt)
      have := hf2 d'; have := hf1 d
      omega
  have hsub : Finset.univ.image f ⊆ falls (fun j => run C.gates (Z j)) k := by
    intro x hx
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.1 hx
    exact hf3 d
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at this
  omega

/-! ## The upper bound: the explicit circuit -/

lemma rb_readsBack {base : ℕ} {C : Circuit} (h : RB base C.gates) : ReadsBack base C := by
  intro j hj i hi
  unfold gateAt at hi
  rw [List.getD_eq_getElem _ _ hj] at hi
  exact h j hj i hi

lemma optW_ge (o : Option ℕ) (B d : ℕ) (h : d ≤ B) : d ≤ optW o B d := by
  cases o with
  | none => exact le_refl _
  | some p => simp only [optW]; omega

theorem upper (t k b n : ℕ) (name : Fin k → Fin t) (addr : Fin k → Fin t → Bool → ℕ)
    (raw : Fin k → (Fin t → Bool) → List Bool)
    (haddr_lt : ∀ h a s, addr h a s < n)
    (hraw_len : ∀ i w, (raw i w).length = n + 2)
    (hraw_n : ∀ i w, (raw i w).getD n false = false)
    (hraw_n1 : ∀ i w, (raw i w).getD (n+1) false = true)
    (hraw_addr : ∀ i w h a s, (raw i w).getD (addr h a s) false = true ↔
      (h < i ∨ (h = i ∧ w a = s)))
    (hpack : ¬ ∃ lo hi : Fin (2^b) → Fin k, (∀ j, lo j < hi j ∧ name (lo j) = name (hi j)) ∧
        (∀ j h, j < h → hi j < lo h)) :
    ∃ (C : Circuit) (tap : Fin t → ℕ) (side : Fin k → Bool),
      FanInTwo C ∧ ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ notCount C ≤ b ∧ C.size ≤ 4*k ∧
      (∀ v, v < n → ((∃ g ∈ C.gates, v ∈ g.inputs) ∨ (∃ a, tap a = v) ∨ C.output = v) →
        ∃ i, v = addr i (name i) (side i)) ∧
      ∀ (i : Fin k) (w : Fin t → Bool), ∃ a, (C.wires (raw i w)).getD (tap a) false ≠ w a := by
  let nm : ℕ → ℕ := fun i => if h : i < k then (name ⟨i, h⟩).val else 0
  have hnm : ∀ i : Fin k, nm i.val = (name i).val := fun i => by simp [nm, i.isLt]
  let m := R nm k
  have hm2 : m < 2 ^ b := by
    by_contra hge
    push Not at hge
    apply hpack
    have hex : ∀ d : Fin (2^b), ∃ i', i' < eEnd nm k d.val ∧ nm i' = nm (eEnd nm k d.val) ∧
        R nm i' = d.val := by
      intro d
      obtain ⟨_, he, hR⟩ := eEnd_spec nm k d.val (by have := d.isLt; omega)
      obtain ⟨i', hi', h1, h2⟩ := (isEnd_iff nm _).1 he
      exact ⟨i', hi', h1, by rw [h2, hR]⟩
    choose lo' hlo1 hlo2 hlo3 using hex
    have hek : ∀ d : Fin (2^b), eEnd nm k d.val < k :=
      fun d => (eEnd_spec nm k d.val (by have := d.isLt; omega)).1
    refine ⟨fun d => ⟨lo' d, by have := hlo1 d; have := hek d; omega⟩,
      fun d => ⟨eEnd nm k d.val, hek d⟩, fun d => ⟨?_, ?_⟩, fun d d' hdd => ?_⟩
    · exact Fin.lt_def.2 (hlo1 d)
    · have e1 := hnm ⟨lo' d, by have := hlo1 d; have := hek d; omega⟩
      have e2 := hnm ⟨eEnd nm k d.val, hek d⟩
      exact Fin.ext (e1.symm.trans ((hlo2 d).trans e2))
    · show eEnd nm k d.val < lo' d'
      by_contra hc
      push Not at hc
      have := R_mono nm hc
      rw [hlo3 d', (eEnd_spec nm k d.val (by have := d.isLt; omega)).2.2] at this
      have := Fin.lt_def.1 hdd
      omega
  have hmk : 2 * m ≤ k := two_R_le nm k
  let e := eEnd nm k
  have he_lt : ∀ r < m, e r < k := fun r hr => (eEnd_spec nm k r hr).1
  let side : Fin k → Bool := fun i => decide (isEnd nm i.val)
  let rail : ℕ → ℕ := fun i => if h : i < k then addr ⟨i, h⟩ (name ⟨i, h⟩) (side ⟨i, h⟩) else 0
  have hrail_eq : ∀ i : Fin k, rail i.val = addr i (name i) (side i) := fun i => by
    simp [rail, i.isLt]
  have hrail_lt : ∀ i < k, rail i < n := fun i hi => by
    have := hrail_eq ⟨i, hi⟩; simp only at this; rw [this]; exact haddr_lt _ _ _
  obtain ⟨G, hG⟩ : ∃ G, G = negG n m (n+2) m (fun r => rail (e r)) := ⟨_, rfl⟩
  have hGlen : G.1.length ≤ 4 * m := by rw [hG]; exact negG_len n m (n+2) m _
  have hGnots : notCount ⟨G.1, 0⟩ ≤ b := by rw [hG]; exact negG_nots n m (n+2) m _ b hm2
  have hGops : ∀ g ∈ G.1, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by rw [hG]; exact negG_ops n m (n+2) m _
  have hGin : ∀ g ∈ G.1, ∀ v ∈ g.inputs, (∃ r < m, v = rail (e r)) ∨ v = n ∨ n + 2 ≤ v := by
    rw [hG]; exact negG_inputs n m (n+2) m _ (le_refl _)
  have hGout : ∀ r < m, n + 2 ≤ G.2 r ∧ G.2 r < n + 2 + G.1.length := by
    rw [hG]; exact negG_outs n m (n+2) m _ (le_refl _)
  have hGrb : RB (n+2) G.1 := by
    rw [hG]
    exact negG_rb n m (n+2) m (fun r => rail (e r)) (le_refl _)
      (fun r hr => by have := hrail_lt (e r) (he_lt r hr); omega) (by omega)
  have hGcor : ∀ V : ℕ → Bool, Cons V (n+2) G.1 → V n = false →
      (∀ r r', r ≤ r' → r' < m → V (rail (e r')) = true → V (rail (e r)) = true) →
      ∀ r < m, V (G.2 r) = !V (rail (e r)) := by
    rw [hG]; exact negG_correct n m (n+2) m _ (le_refl _)
  obtain ⟨bT, hbT⟩ : ∃ x, x = n + 2 + G.1.length := ⟨_, rfl⟩
  let negw : ℕ → ℕ := fun i => if R nm i < m then G.2 (R nm i) else n + 1
  obtain ⟨ands, hands⟩ : ∃ l : List Gate,
      l = List.ofFn (fun i : Fin k => gAnd (rail i) (negw i)) := ⟨_, rfl⟩
  obtain ⟨ors, hors⟩ : ∃ l : List Gate,
      l = List.ofFn (fun i : Fin k => gOr (optW (last nm (nm i) i) (bT + k) n) (bT + i)) :=
    ⟨_, rfl⟩
  have hands_len : ands.length = k := by rw [hands]; simp
  have hors_len : ors.length = k := by rw [hors]; simp
  let C : Circuit := ⟨G.1 ++ ands ++ ors, n⟩
  let tap : Fin t → ℕ := fun a => optW (last nm a.val k) (bT + k) n
  have hsize : C.size = G.1.length + k + k := by
    show (G.1 ++ ands ++ ors).length = _
    rw [List.length_append, List.length_append, hands_len, hors_len]
  have hmem : ∀ g ∈ C.gates, g ∈ G.1 ∨ (∃ i : Fin k, g = gAnd (rail i) (negw i)) ∨
      (∃ i : Fin k, g = gOr (optW (last nm (nm i) i) (bT + k) n) (bT + i)) := by
    intro g hg
    have h1 : g ∈ G.1 ++ ands ++ ors := hg
    simp only [List.mem_append] at h1
    rcases h1 with (h1 | h1) | h1
    · exact Or.inl h1
    · rw [hands, List.mem_ofFn] at h1
      obtain ⟨i, rfl⟩ := h1
      exact Or.inr (Or.inl ⟨i, rfl⟩)
    · rw [hors, List.mem_ofFn] at h1
      obtain ⟨i, rfl⟩ := h1
      exact Or.inr (Or.inr ⟨i, rfl⟩)
  have hRB : RB (n+2) C.gates := by
    refine RB.append' (b2 := bT + k) (RB.append' (b2 := bT) hGrb ?_ hbT) ?_ ?_
    · rw [hands]
      refine RB.ofFn (fun i v hv => ?_)
      simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · have := hrail_lt i i.isLt; omega
      · simp only [negw]
        split_ifs with h
        · have := (hGout (R nm i) h).2; omega
        · omega
    · rw [hors]
      refine RB.ofFn (fun i v hv => ?_)
      simp only [gOr, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · rcases hl : last nm (nm i) i with _ | p
        · simp only [optW]; omega
        · have := (last_some nm _ _ p hl).1
          simp only [optW]; omega
      · have := i.isLt; omega
    · rw [List.length_append, hands_len]; omega
  refine ⟨C, tap, side, ?_, rb_readsBack hRB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- fan-in two
    intro g hg
    rcases hmem g hg with hg | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨h1, h2⟩ := hGops g hg
      refine ⟨?_, h2⟩
      rcases h1 with h | h | h <;> simp [h]
    · simp [gAnd]
    · simp [gOr]
  · -- output
    show n < n + 2 + C.size; omega
  · -- taps
    intro a
    rw [hsize]
    show optW (last nm a.val k) (bT + k) n < _
    rcases hl : last nm a.val k with _ | p
    · simp only [optW]; omega
    · have := (last_some nm _ _ p hl).1
      simp only [optW]; omega
  · -- NOT gates
    show notCount ⟨G.1 ++ ands ++ ors, 0⟩ ≤ b
    rw [nc_append, nc_append, hands, hors, nc_ofFn_zero _ (fun r => by simp [gAnd]),
      nc_ofFn_zero _ (fun r => by simp [gOr])]
    simpa using hGnots
  · -- size
    rw [hsize]; omega
  · -- reads only the chosen rails
    intro v hv hrd
    have hbig : ∀ (o : Option ℕ), n ≤ optW o (bT + k) n := fun o => optW_ge o _ _ (by omega)
    rcases hrd with ⟨g, hg, hvg⟩ | ⟨a, rfl⟩ | hout
    · rcases hmem g hg with hg | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rcases hGin g hg v hvg with ⟨r, hr, rfl⟩ | rfl | h
        · exact ⟨⟨e r, he_lt r hr⟩, hrail_eq ⟨e r, he_lt r hr⟩⟩
        · omega
        · omega
      · simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hvg
        rcases hvg with rfl | rfl
        · exact ⟨i, hrail_eq i⟩
        · simp only [negw] at hv
          split_ifs at hv with h
          · have := (hGout (R nm i) h).1; omega
          · omega
      · simp only [gOr, List.mem_cons, List.not_mem_nil, or_false] at hvg
        rcases hvg with rfl | rfl
        · have := hbig (last nm (nm i) i); omega
        · omega
    · have := hbig (last nm a.val k); simp only [tap] at hv; omega
    · simp only [C] at hout; omega
  · -- correctness
    intro i0 w
    obtain ⟨hpre, hcons⟩ := run_spec C.gates (raw i0 w) (by rw [hraw_len]; exact hRB)
    rw [hraw_len] at hcons
    set V : ℕ → Bool := fun p => (run C.gates (raw i0 w)).getD p false with hV
    let j := if w (name i0) = side i0 then i0.val + 1 else i0.val
    have hVrail : ∀ h : Fin k, V (rail h.val) = decide (h.val < j) := by
      intro h
      have hlt := hrail_lt h.val h.isLt
      show (run C.gates (raw i0 w)).getD (rail h.val) false = _
      rw [hpre _ (by rw [hraw_len]; omega), hrail_eq]
      apply Bool.eq_iff_iff.2
      rw [hraw_addr, decide_eq_true_iff, Fin.lt_def]
      simp only [j]
      split_ifs with hw
      · constructor
        · rintro (hlt | ⟨rfl, _⟩)
          · omega
          · omega
        · intro hlt
          rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
          · exact Or.inl hlt
          · have : h = i0 := Fin.ext heq
            subst this; exact Or.inr ⟨rfl, hw⟩
      · constructor
        · rintro (hlt | ⟨rfl, hws⟩)
          · exact hlt
          · exact absurd hws hw
        · intro hlt; exact Or.inl hlt
    have hVn : V n = false := by
      show (run C.gates (raw i0 w)).getD n false = _
      rw [hpre _ (by rw [hraw_len]; omega), hraw_n]
    have hVn1 : V (n+1) = true := by
      show (run C.gates (raw i0 w)).getD (n+1) false = _
      rw [hpre _ (by rw [hraw_len]; omega), hraw_n1]
    have hcG : Cons V (n+2) G.1 := hcons.left.left
    have hcA : Cons V bT ands := hcons.left.right' hbT.symm
    have hcO : Cons V (bT + k) ors := hcons.right' (by rw [List.length_append, hands_len]; omega)
    rw [hands] at hcA
    rw [hors] at hcO
    have hneg := hGcor V hcG hVn
      (fun r r' hrr hr' hv => by
        have h1 := hVrail ⟨e r', he_lt r' hr'⟩
        have h2 := hVrail ⟨e r, he_lt r (by omega)⟩
        simp only at h1 h2
        rw [h1] at hv; rw [h2]
        simp only [decide_eq_true_eq] at hv ⊢
        have : e r ≤ e r' := eEnd_mono nm k r r' hrr hr'
        omega)
    have hAnd : ∀ i < k, V (bT + i) =
        (decide (i < j) && (if R nm i < m then decide (j ≤ e (R nm i)) else true)) := by
      intro i hi
      have := hcA.ofFn' i hi _ rfl
      simp only [eval_gAnd] at this
      rw [this, hVrail ⟨i, hi⟩]
      simp only [negw]
      split_ifs with h
      · rw [hneg (R nm i) h, hVrail ⟨e (R nm i), he_lt _ h⟩]
        congr 1
        exact Bool.eq_iff_iff.2 (by simp)
      · rw [hVn1]
    have hOr : ∀ i < k, V (bT + k + i) =
        (V (optW (last nm (nm i) i) (bT + k) n) || V (bT + i)) := by
      intro i hi
      have := hcO.ofFn' i hi _ rfl
      simpa using this
    have htap : ∀ a : Fin t, V (tap a) = true ↔ Tval nm k j a.val := by
      intro a
      show V (optW (last nm a.val k) (bT + k) n) = true ↔ _
      rw [tapval nm V k (bT + k) bT n hVn hOr a.val]
      constructor
      · rintro ⟨i', hi', hnmi, hv⟩
        rw [hAnd i' hi'] at hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        refine ⟨i', hi', hnmi, hv.1, fun hr => ?_⟩
        have := hv.2
        rw [if_pos hr] at this
        simpa using this
      · rintro ⟨i', hi', hnmi, hlt, hle⟩
        refine ⟨i', hi', hnmi, ?_⟩
        rw [hAnd i' hi']
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨hlt, ?_⟩
        split_ifs with hr
        · simpa using hle hr
        · rfl
    refine ⟨name i0, ?_⟩
    show V (tap (name i0)) ≠ w (name i0)
    have hnm0 : nm i0.val = (name i0).val := hnm i0
    by_cases hw : w (name i0) = side i0
    · have hj : j = i0.val + 1 := by simp only [j]; rw [if_pos hw]
      rw [hw]
      by_cases he : isEnd nm i0.val
      · have := (Tval_end nm k i0.val i0.isLt he).2
        rw [hnm0, ← hj, ← htap] at this
        have hs : side i0 = true := by simp [side, he]
        rw [hs]; simpa using this
      · have := (Tval_notEnd nm k i0.val i0.isLt he).2
        rw [hnm0, ← hj, ← htap] at this
        have hs : side i0 = false := by simp [side, he]
        rw [hs, this]; simp
    · have hj : j = i0.val := by simp only [j]; rw [if_neg hw]
      by_cases he : isEnd nm i0.val
      · have := (Tval_end nm k i0.val i0.isLt he).1
        rw [hnm0, ← hj, ← htap] at this
        have hs : side i0 = true := by simp [side, he]
        rw [hs] at hw
        rw [this]; intro h; exact hw h.symm
      · have := (Tval_notEnd nm k i0.val i0.isLt he).1
        rw [hnm0, ← hj, ← htap] at this
        have hs : side i0 = false := by simp [side, he]
        rw [hs] at hw
        simp only [Bool.not_eq_true] at this
        rw [this]; intro h; exact hw h.symm

end PEqualNP.Outside.L_lib_1321_aux

theorem PEqualNP.Outside.L_lib_1321 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (t k b : Nat) (name : Fin k → Fin t), 1 ≤ t →
  let n := 2*t*k
  let addr := fun (i : Fin k) (a : Fin t) (s : Bool) => 2*(t*i.val+a.val)+(if s then 1 else 0)
  let raw := fun (i : Fin k) (w : Fin t → Bool) => List.ofFn (fun v : Fin n =>
    decide (∃ (h : Fin k) (a : Fin t) (s : Bool), v.val = addr h a s ∧ (h < i ∨ (h = i ∧ w a = s)))) ++ [false,true]
  let fits := fun (cost : Nat → Prop) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat) (side : Fin k → Bool),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ cost C.size ∧
      (∀ v, v < n → ((∃ g ∈ C.gates, v ∈ g.inputs) ∨ (∃ a, tap a = v) ∨ C.output = v) →
        ∃ i, v = addr i (name i) (side i)) ∧
      ∀ (i : Fin k) (w : Fin t → Bool), ∃ a, (C.wires (raw i w)).getD (tap a) false ≠ w a
  let pack := fun d : Nat => ∃ lo hi : Fin d → Fin k,
    (∀ j, lo j < hi j ∧ name (lo j) = name (hi j)) ∧ (∀ j h, j < h → hi j < lo h)
  (fits (fun _ => True) ↔ ¬ pack (2^b)) ∧ (¬ pack (2^b) → fits (fun gates => gates ≤ 4*k)) := by
  intro t k b name ht n addr raw fits pack
  have hA : ∀ (h : Fin k) (a : Fin t) (s : Bool),
      addr h a s = 2*(t*h.val+a.val) + (if s = true then 1 else 0) := by
    intro h a s; cases s <;> simp [addr]
  have hA_lt : ∀ (h : Fin k) (a : Fin t) (s : Bool) (j : ℕ), addr h a s < 2*t*j ↔ h.val < j := by
    intro h a s j
    rw [hA]
    have ha := a.isLt
    have e1 : 2*t*j = 2*(t*j) := by ring
    constructor
    · intro hlt
      by_contra hc
      push Not at hc
      have : t * j ≤ t * h.val := Nat.mul_le_mul_left _ hc
      split_ifs at hlt <;> omega
    · intro hlt
      have : t * (h.val + 1) ≤ t * j := Nat.mul_le_mul_left _ hlt
      have : t * (h.val+1) = t * h.val + t := by ring
      split_ifs <;> omega
  have hA_inj : ∀ h a s h' a' s', addr h a s = addr h' a' s' → h = h' ∧ a = a' ∧ s = s' := by
    intro h a s h' a' s' heq
    rw [hA, hA] at heq
    have hs : s = s' := by
      cases s <;> cases s' <;> first | rfl | (exfalso; simp at heq <;> omega)
    subst hs
    have e : t*h.val + a.val = t*h'.val + a'.val := by split_ifs at heq <;> omega
    have hh : h.val = h'.val := by
      by_contra hc
      rcases Nat.lt_or_gt_of_ne hc with hlt | hlt
      · have : t * (h.val+1) ≤ t * h'.val := Nat.mul_le_mul_left _ hlt
        have : t * (h.val+1) = t*h.val + t := by ring
        have := a.isLt; omega
      · have : t * (h'.val+1) ≤ t * h.val := Nat.mul_le_mul_left _ hlt
        have : t * (h'.val+1) = t*h'.val + t := by ring
        have := a'.isLt; omega
    have ha : a.val = a'.val := by
      have : t * h.val = t * h'.val := by rw [hh]
      omega
    exact ⟨Fin.ext hh, Fin.ext ha, rfl⟩
  have hn : n = 2*t*k := rfl
  have haddr_lt : ∀ h a s, addr h a s < n := fun h a s => by rw [hn]; exact (hA_lt h a s k).2 h.isLt
  have hraw_len : ∀ i w, (raw i w).length = n + 2 := by intro i w; simp [raw]
  have hraw_n : ∀ i w, (raw i w).getD n false = false := by
    intro i w; simp only [raw]; rw [PEqualNP.Outside.L_lib_1321_aux.getD_inp]; simp
  have hraw_n1 : ∀ i w, (raw i w).getD (n+1) false = true := by
    intro i w; simp only [raw]; rw [PEqualNP.Outside.L_lib_1321_aux.getD_inp]; simp
  have hraw_addr : ∀ i w h a s, (raw i w).getD (addr h a s) false = true ↔
      (h < i ∨ (h = i ∧ w a = s)) := by
    intro i w h a s
    have hlt : addr h a s < n := haddr_lt h a s
    refine (PEqualNP.Outside.L_lib_1321_aux.getD_ofFn_dec _ _ (addr h a s) hlt).trans ?_
    constructor
    · rintro ⟨h', a', s', heq, hc⟩
      obtain ⟨rfl, rfl, rfl⟩ := hA_inj _ _ _ _ _ _ heq
      exact hc
    · intro hc; exact ⟨h, a, s, rfl, hc⟩
  refine ⟨⟨fun hfits => ?_, fun hp => ?_⟩, fun hp => ?_⟩
  · simp only [fits] at hfits
    obtain ⟨C, tap, side, hf, _, _, _, hnot, _, hreads, hfit⟩ := hfits
    exact PEqualNP.Outside.L_lib_1321_aux.lower t k b n name addr raw hA_lt hraw_len hraw_n hraw_n1 hraw_addr C tap side hf hnot
      hreads hfit
  · obtain ⟨C, tap, side, h1, h2, h3, h4, h5, _, h7, h8⟩ :=
      PEqualNP.Outside.L_lib_1321_aux.upper t k b n name addr raw haddr_lt hraw_len hraw_n hraw_n1 hraw_addr hp
    simp only [fits]
    exact ⟨C, tap, side, h1, h2, h3, h4, h5, trivial, h7, h8⟩
  · simp only [fits]
    exact PEqualNP.Outside.L_lib_1321_aux.upper t k b n name addr raw haddr_lt hraw_len hraw_n hraw_n1 hraw_addr hp
