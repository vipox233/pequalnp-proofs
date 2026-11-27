import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_071

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

def evalWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def evalDepths (gs : List Gate) (d : List ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1]) d

lemma evalWires_nil (x : List Bool) : evalWires [] x = x := rfl

lemma evalWires_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    evalWires (gs₁ ++ gs₂) x = evalWires gs₂ (evalWires gs₁ x) := by
  unfold evalWires
  rw [List.foldl_append]

lemma evalWires_length (gs : List Gate) (x : List Bool) :
    (evalWires gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [evalWires]
  | cons g tl ih =>
    simp only [evalWires, List.foldl_cons]
    have h := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    unfold evalWires at h
    rw [h, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma evalDepths_append (gs₁ gs₂ : List Gate) (d : List ℕ) :
    evalDepths (gs₁ ++ gs₂) d = evalDepths gs₂ (evalDepths gs₁ d) := by
  unfold evalDepths
  rw [List.foldl_append]

lemma evalDepths_length (gs : List Gate) (d : List ℕ) :
    (evalDepths gs d).length = d.length + gs.length := by
  induction gs generalizing d with
  | nil => simp [evalDepths]
  | cons g tl ih =>
    simp only [evalDepths, List.foldl_cons]
    have h := ih (d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1])
    unfold evalDepths at h
    rw [h, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ} (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
    List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]

lemma getD_append_right {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ} (hi : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  by_cases h : i < l₁.length + l₂.length
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
      List.getD_eq_getElem _ _ (by omega), List.getElem_append_right hi]
  · rw [List.getD_eq_default _ _ (by rw [List.length_append]; omega),
      List.getD_eq_default _ _ (by omega)]

lemma evalWires_prefix_getD (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (evalWires gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g tl ih =>
    simp only [evalWires, List.foldl_cons]
    have h := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
      (by rw [List.length_append, List.length_singleton]; omega)
    unfold evalWires at h
    rw [h, getD_append_left _ _ _ hi]

lemma evalWires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (evalWires (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false) := by
  rw [evalWires_append]
  set w := evalWires gs x
  have hlen : w.length = x.length + gs.length := evalWires_length gs x
  rw [← hlen]
  unfold evalWires
  simp only [List.foldl_cons, List.foldl_nil]
  rw [getD_append_right w _ false (le_refl _), Nat.sub_self]
  rfl

lemma evalWires_layer_getD (L : List Gate) (w : List Bool)
    (hL : ∀ g ∈ L, ∀ i ∈ g.inputs, i < w.length)
    {k : ℕ} (hk : k < L.length) :
    (evalWires L w).getD (w.length + k) false =
      (L[k]'hk).op.eval ((L[k]'hk).inputs.map fun i => w.getD i false) := by
  induction L generalizing w k with
  | nil => cases hk
  | cons g tl ih =>
    simp only [evalWires, List.foldl_cons]
    set w' := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hw'len : w'.length = w.length + 1 := by simp [w']
    cases k with
    | zero =>
      have h1 := evalWires_prefix_getD tl w' (i := w.length) (by omega)
      unfold evalWires at h1
      rw [Nat.add_zero, h1]
      simp [w']
    | succ k' =>
      have hk' : k' < tl.length := by simpa using hk
      have htl : ∀ g' ∈ tl, ∀ i ∈ g'.inputs, i < w'.length := by
        intro g' hg' i hi
        have := hL g' (List.mem_cons_of_mem g hg') i hi
        omega
      have h1 := ih w' htl hk'
      unfold evalWires at h1
      have heq : w.length + (k' + 1) = w'.length + k' := by omega
      rw [heq, h1]
      simp only [List.getElem_cons_succ]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hlt := hL (tl[k']'hk') (List.mem_cons_of_mem g (List.getElem_mem hk')) i hi
      exact getD_append_left w _ false hlt

lemma foldr_max_le (l : List ℕ) (D : ℕ) (h : ∀ a ∈ l, a ≤ D) : l.foldr max 0 ≤ D := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h a (List.mem_cons_self), ih (fun b hb => h b (List.mem_cons_of_mem a hb))⟩

lemma evalDepths_prefix_getD (gs : List Gate) (d : List ℕ) {i : ℕ} (hi : i < d.length) :
    (evalDepths gs d).getD i 0 = d.getD i 0 := by
  induction gs generalizing d with
  | nil => rfl
  | cons g tl ih =>
    simp only [evalDepths, List.foldl_cons]
    have h := ih (d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1])
      (by rw [List.length_append, List.length_singleton]; omega)
    unfold evalDepths at h
    rw [h, getD_append_left _ _ _ hi]

lemma evalDepths_snoc_le (gs : List Gate) (g : Gate) (d : List ℕ) (D : ℕ)
    (hprev : ∀ i ∈ g.inputs, (evalDepths gs d).getD i 0 ≤ D) :
    (evalDepths (gs ++ [g]) d).getD (d.length + gs.length) 0 ≤ D + 1 := by
  rw [evalDepths_append]
  set ds := evalDepths gs d
  have hlen : ds.length = d.length + gs.length := evalDepths_length gs d
  rw [← hlen]
  unfold evalDepths
  simp only [List.foldl_cons, List.foldl_nil]
  rw [getD_append_right ds _ 0 (le_refl _), Nat.sub_self]
  simp only [List.getD_cons_zero]
  have hmax : (g.inputs.map fun i => ds.getD i 0).foldr max 0 ≤ D := by
    apply foldr_max_le
    intro a ha
    rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
    exact hprev i hi
  omega

lemma evalDepths_layer_le (L : List Gate) (d : List ℕ) (D : ℕ)
    (hd : ∀ i < d.length, d.getD i 0 ≤ D)
    (hL : ∀ g ∈ L, ∀ i ∈ g.inputs, i < d.length) :
    ∀ i < (evalDepths L d).length, (evalDepths L d).getD i 0 ≤ D + 1 := by
  have hmain : ∀ L' : List Gate, (∀ g ∈ L', ∀ i ∈ g.inputs, i < d.length) →
      ∀ d' : List ℕ, d.length ≤ d'.length →
      (∀ i < d.length, d'.getD i 0 = d.getD i 0) →
      (∀ i < d'.length, d'.getD i 0 ≤ D + 1) →
      ∀ i < (evalDepths L' d').length, (evalDepths L' d').getD i 0 ≤ D + 1 := by
    intro L'
    induction L' with
    | nil =>
      intro _ d' _ _ hd' i hi
      exact hd' i hi
    | cons g tl ih =>
      intro hL' d' hlen hagree hd'
      simp only [evalDepths, List.foldl_cons]
      set v := (g.inputs.map fun i => d'.getD i 0).foldr max 0 + 1
      have hv : v ≤ D + 1 := by
        have hmax : (g.inputs.map fun i => d'.getD i 0).foldr max 0 ≤ D := by
          apply foldr_max_le
          intro a ha
          rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
          have hlt := hL' g (List.mem_cons_self) i hi
          rw [hagree i hlt]
          exact hd i hlt
        omega
      apply ih (fun g' hg' => hL' g' (List.mem_cons_of_mem g hg')) (d' ++ [v])
      · rw [List.length_append, List.length_singleton]; omega
      · intro i hi
        rw [getD_append_left _ _ _ (by omega), hagree i hi]
      · intro i hi
        rw [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < d'.length
        · rw [getD_append_left _ _ _ hlt]
          exact hd' i hlt
        · have heq : i = d'.length := by omega
          subst heq
          rw [getD_append_right _ _ _ (le_refl _), Nat.sub_self]
          simpa using hv
  exact hmain L hL d (le_refl _) (fun _ _ => rfl) (fun i hi => Nat.le_succ_of_le (hd i hi))

lemma evalDepths_layer_le_from (L : List Gate) (d : List ℕ) (B D : ℕ)
    (hB : B ≤ d.length)
    (hd : ∀ i < B, d.getD i 0 ≤ D)
    (hL : ∀ g ∈ L, ∀ i ∈ g.inputs, i < B) :
    ∀ k < L.length, (evalDepths L d).getD (d.length + k) 0 ≤ D + 1 := by
  have hmain : ∀ L' : List Gate, (∀ g ∈ L', ∀ i ∈ g.inputs, i < B) →
      ∀ d' : List ℕ, d.length ≤ d'.length →
      (∀ i < B, d'.getD i 0 = d.getD i 0) →
      ∀ k < L'.length, (evalDepths L' d').getD (d'.length + k) 0 ≤ D + 1 := by
    intro L'
    induction L' with
    | nil => intro _ _ _ _ k hk; cases hk
    | cons g tl ih =>
      intro hL' d' hlen hagree k hk
      simp only [evalDepths, List.foldl_cons]
      set v := (g.inputs.map fun i => d'.getD i 0).foldr max 0 + 1
      have hv : v ≤ D + 1 := by
        have hmax : (g.inputs.map fun i => d'.getD i 0).foldr max 0 ≤ D := by
          apply foldr_max_le
          intro a ha
          rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
          have hlt := hL' g (List.mem_cons_self) i hi
          rw [hagree i hlt]
          exact hd i hlt
        omega
      cases k with
      | zero =>
        have h1 := evalDepths_prefix_getD tl (d' ++ [v]) (i := d'.length) (by simp)
        unfold evalDepths at h1
        rw [Nat.add_zero, h1, getD_append_right _ _ _ (le_refl _), Nat.sub_self]
        simpa using hv
      | succ k' =>
        have hk' : k' < tl.length := by simpa using hk
        have h1 := ih (fun g' hg' => hL' g' (List.mem_cons_of_mem g hg')) (d' ++ [v])
          (by simp; omega)
          (fun i hi => by rw [getD_append_left _ _ _ (by omega), hagree i hi])
          k' hk'
        unfold evalDepths at h1
        have heq : d'.length + (k' + 1) = (d' ++ [v]).length + k' := by simp; omega
        rw [heq]
        exact h1
  exact hmain L hL d (le_refl _) (fun _ _ => rfl)

lemma readsBack_append_layer (N : ℕ) (gs L : List Gate) (out : ℕ)
    (hgs : ReadsBack N ⟨gs, out⟩)
    (hL : ∀ g ∈ L, ∀ i ∈ g.inputs, i < N + gs.length) :
    ReadsBack N ⟨gs ++ L, out⟩ := by
  intro j hj i hi
  rw [List.length_append] at hj
  by_cases h1 : j < gs.length
  · have hg : gateAt ⟨gs ++ L, out⟩ j = gateAt ⟨gs, out⟩ j := by
      unfold gateAt; exact getD_append_left gs L _ h1
    rw [hg] at hi
    exact hgs j h1 i hi
  · have hge : gs.length ≤ j := by omega
    have hlt : j - gs.length < L.length := by omega
    have hg : gateAt ⟨gs ++ L, out⟩ j = L[j - gs.length]'hlt := by
      unfold gateAt
      rw [getD_append_right gs L _ hge, List.getD_eq_getElem _ _ hlt]
    rw [hg] at hi
    have h2 := hL (L[j - gs.length]'hlt) (List.getElem_mem hlt) i hi
    omega

lemma readsBack_append_snoc (N : ℕ) (gs : List Gate) (g : Gate) (out : ℕ)
    (hgs : ReadsBack N ⟨gs, out⟩)
    (hg : ∀ i ∈ g.inputs, i < N + gs.length) :
    ReadsBack N ⟨gs ++ [g], out⟩ :=
  readsBack_append_layer N gs [g] out hgs (fun g' hg' => by simp at hg'; subst hg'; exact hg)

def pairIdx (a b : Bool) : ℕ :=
  match a, b with
  | false, false => 0
  | true, false => 1
  | false, true => 2
  | true, true => 3

lemma pairIdx_lt (a b : Bool) : pairIdx a b < 4 := by
  cases a <;> cases b <;> decide

def tableInput {n : ℕ} (T : Fin n → Bool → Bool → Bool) : List Bool :=
  (List.ofFn (fun i : Fin n =>
    [T i false false, T i true false, T i false true, T i true true])).flatten

lemma tableInput_length {n : ℕ} (T : Fin n → Bool → Bool → Bool) :
    (tableInput T).length = 4 * n := by
  unfold tableInput
  rw [List.length_flatten]
  have hmap : (List.ofFn (fun i : Fin n =>
      [T i false false, T i true false, T i false true, T i true true])).map List.length =
      List.replicate n 4 := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  rw [hmap, List.sum_replicate, smul_eq_mul, Nat.mul_comm]

lemma tableInput_getD {n : ℕ} (T : Fin n → Bool → Bool → Bool)
    (i : Fin n) (a b : Bool) :
    (tableInput T).getD (4 * i.val + pairIdx a b) false = T i a b := by
  have h4 : ∀ (m : ℕ) (f : Fin m → List Bool), (∀ j, (f j).length = 4) →
      ∀ (j : Fin m) (r : ℕ) (hr : r < 4),
        ((List.ofFn f).flatten).getD (4 * j.val + r) false = (f j).getD r false := by
    intro m
    induction m with
    | zero => intro _ _ j; exact Fin.elim0 j
    | succ m ih =>
      intro f hf j r hr
      rw [List.ofFn_succ, List.flatten_cons]
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add]
        rw [getD_append_left _ _ _ (by rw [hf 0]; exact hr)]
      | succ j' =>
        simp only [Fin.val_succ]
        have hlen : (f 0).length = 4 := hf 0
        have hge : (f 0).length ≤ 4 * (j'.val + 1) + r := by omega
        rw [getD_append_right _ _ _ hge]
        have hsub : 4 * (j'.val + 1) + r - (f 0).length = 4 * j'.val + r := by omega
        rw [hsub]
        exact ih (fun k => f k.succ) (fun k => hf k.succ) j' r hr
  have hres := h4 n (fun j : Fin n =>
    [T j false false, T j true false, T j false true, T j true true])
    (fun _ => rfl) i (pairIdx a b) (pairIdx_lt a b)
  unfold tableInput
  rw [hres]
  cases a <;> cases b <;> rfl

def crossRow {n : ℕ} (T : Fin n → Bool → Bool → Bool) (i : ℕ) : Bool :=
  if h : i < n then T ⟨i, h⟩ true false && T ⟨i, h⟩ false true else false

def prefXor {n : ℕ} (T : Fin n → Bool → Bool → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => xor (prefXor T k) (crossRow T k)

lemma count_range_crossRow {n : ℕ} (T : Fin n → Bool → Bool → Bool) (k : ℕ) :
    ((List.range k).map (crossRow T)).count true % 2 = if prefXor T k then 1 else 0 := by
  induction k with
  | zero => simp [prefXor]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.count_append]
    simp only [List.count_singleton, prefXor]
    have hmod : (((List.range k).map (crossRow T)).count true +
        if (crossRow T k == true) = true then 1 else 0) % 2 =
        ((((List.range k).map (crossRow T)).count true % 2) +
        if (crossRow T k == true) = true then 1 else 0) % 2 := by
      omega
    rw [hmod, ih]
    have hb : ∀ x y : Bool,
        ((if x = true then 1 else 0) + if (y == true) = true then 1 else 0) % 2 =
          if (x ^^ y) = true then 1 else 0 := by decide
    exact hb _ _

def relabT {n : ℕ} (T : Fin n → Bool → Bool → Bool) (i : ℕ) (a b : Bool) : Bool :=
  if h : i < n then
    T ⟨i, h⟩ (xor a (prefXor T i)) (xor b (prefXor T (i + 1)))
  else false

def rowNonEmpty {n : ℕ} (T : Fin n → Bool → Bool → Bool) (i : ℕ) : Bool :=
  relabT T i false false || relabT T i true false || relabT T i false true || relabT T i true true

def rowStay {n : ℕ} (T : Fin n → Bool → Bool → Bool) (i : ℕ) : Bool :=
  relabT T i false false && relabT T i true true

def rowBlock {n : ℕ} (T : Fin n → Bool → Bool → Bool) (i : ℕ) (a : Bool) : Bool :=
  rowStay T i && !(relabT T i a (!a))

def leftOnly {n : ℕ} (T : Fin n → Bool → Bool → Bool) (b0 : Bool) (l : ℕ) (a : Bool) : Bool :=
  if l = 0 then decide (a = b0)
  else !(relabT T (l - 1) false (!a)) && !(relabT T (l - 1) true (!a))

def rightOnly {n : ℕ} (T : Fin n → Bool → Bool → Bool) (b0 : Bool) (r : ℕ) (b : Bool) : Bool :=
  if r = n then decide (b = xor b0 (prefXor T n))
  else !(relabT T r (!b) false) && !(relabT T r (!b) true)

lemma cut_not_both_cross {n : ℕ} (T : Fin n → Bool → Bool → Bool) {i : ℕ} (hi : i < n)
    (hcut : rowStay T i = false) :
    !(relabT T i false true && relabT T i true false) = true := by
  have hp : prefXor T (i + 1) = xor (prefXor T i) (T ⟨i, hi⟩ true false && T ⟨i, hi⟩ false true) := by
    simp [prefXor, crossRow, hi]
  unfold rowStay at hcut
  unfold relabT at hcut ⊢
  simp only [hi, ↓reduceDIte, hp] at hcut ⊢
  generalize prefXor T i = p at hcut ⊢
  cases p <;>
    cases h00 : T ⟨i, hi⟩ false false <;> cases h10 : T ⟨i, hi⟩ true false <;>
    cases h01 : T ⟨i, hi⟩ false true <;> cases h11 : T ⟨i, hi⟩ true true <;>
    simp_all

lemma cut_is_rect {n : ℕ} (T : Fin n → Bool → Bool → Bool) {i : ℕ} (hi : i < n)
    (hcut : rowStay T i = false) {a b : Bool}
    (ha : ∃ y, relabT T i a y = true) (hb : ∃ x, relabT T i x b = true) :
    relabT T i a b = true := by
  have hnc := cut_not_both_cross T hi hcut
  rcases ha with ⟨y, hy⟩
  rcases hb with ⟨x, hx⟩
  unfold rowStay at hcut
  cases a <;> cases b <;> cases x <;> cases y <;> simp_all

lemma comb_char {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) :
    (∃ w : Fin n → Bool, ∀ i : Fin n,
      T i (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true) ↔
    ∃ b0 : Bool,
      (∀ i < n, rowNonEmpty T i = true) ∧
      ∀ a : Bool, ∀ l r : ℕ, l ≤ r → r ≤ n →
        ¬ (leftOnly T b0 l a = true ∧ rightOnly T b0 r (!a) = true ∧
           ∀ k, l ≤ k → k < r → rowBlock T k a = true) := by
  constructor
  · rintro ⟨w, hw⟩
    let u : ℕ → Bool := fun k => xor (w ⟨k % n, Nat.mod_lt k hn⟩) (prefXor T k)
    have hu_step : ∀ i < n, relabT T i (u i) (u (i + 1)) = true := by
      intro i hi
      unfold relabT
      simp only [hi, ↓reduceDIte, u]
      have h1 : xor (xor (w ⟨i % n, Nat.mod_lt i hn⟩) (prefXor T i)) (prefXor T i) =
          w ⟨i, hi⟩ := by
        have hmod : (⟨i % n, Nat.mod_lt i hn⟩ : Fin n) = ⟨i, hi⟩ := by
          ext; exact Nat.mod_eq_of_lt hi
        rw [hmod]
        cases w ⟨i, hi⟩ <;> cases prefXor T i <;> rfl
      have h2 : xor (xor (w ⟨(i + 1) % n, Nat.mod_lt (i + 1) hn⟩) (prefXor T (i + 1)))
          (prefXor T (i + 1)) = w ⟨(i + 1) % n, Nat.mod_lt (i + 1) hn⟩ := by
        cases w ⟨(i + 1) % n, Nat.mod_lt (i + 1) hn⟩ <;> cases prefXor T (i + 1) <;> rfl
      rw [h1, h2]
      exact hw ⟨i, hi⟩
    refine ⟨u 0, ?_, ?_⟩
    · intro i hi
      have h := hu_step i hi
      unfold rowNonEmpty
      cases h1 : u i <;> cases h2 : u (i + 1) <;> rw [h1, h2] at h <;> simp [h]
    · intro a l r hlr hrn ⟨hL, hR, hBlk⟩
      have hul : u l = a := by
        unfold leftOnly at hL
        split_ifs at hL with hl0
        · subst hl0
          have : a = u 0 := by simpa using hL
          exact this.symm
        · have hlpos : 0 < l := by omega
          have hlt : l - 1 < n := by omega
          have hstep := hu_step (l - 1) hlt
          have hsucc : l - 1 + 1 = l := by omega
          rw [hsucc] at hstep
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hL
          cases h1 : u (l - 1) <;> cases h2 : u l <;> cases a <;> simp_all
      have hur : u r = !a := by
        unfold rightOnly at hR
        split_ifs at hR with hrn'
        · subst hrn'
          have hba : (!a) = xor (u 0) (prefXor T r) := of_decide_eq_true hR
          rw [hba]
          dsimp only [u]
          have h0 : (⟨0 % r, Nat.mod_lt 0 hn⟩ : Fin r) = ⟨r % r, Nat.mod_lt r hn⟩ := by
            ext; simp
          rw [h0, prefXor]
          cases w ⟨r % r, Nat.mod_lt r hn⟩ <;> cases prefXor T r <;> rfl
        · have hlt : r < n := by omega
          have hstep := hu_step r hlt
          simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.not_not] at hR
          cases h1 : u r <;> cases h2 : u (r + 1) <;> cases a <;> simp_all
      have hind : ∀ d : ℕ, l + d ≤ r → u (l + d) = a := by
        intro d
        induction d with
        | zero => intro _; simpa using hul
        | succ d ih =>
          intro hle
          have huk : u (l + d) = a := ih (by omega)
          have hbk := hBlk (l + d) (by omega) (by omega)
          have hstep := hu_step (l + d) (by omega)
          unfold rowBlock at hbk
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hbk
          have hsucc : l + d + 1 = l + (d + 1) := by omega
          rw [hsucc] at hstep
          rw [huk] at hstep
          cases hnext : u (l + (d + 1)) <;> cases a <;> simp_all
      have hbad := hind (r - l) (by omega)
      rw [Nat.add_sub_cancel' hlr, hur] at hbad
      cases a <;> simp_all
  · rintro ⟨b0, hNE, hNoBad⟩
    let PL : ℕ → Prop := fun k =>
      ∃ l ≤ k, leftOnly T b0 l true = true ∧ ∀ j, l ≤ j → j < k → rowBlock T j true = true
    let PR : ℕ → Prop := fun k =>
      ∃ r, k ≤ r ∧ r ≤ n ∧ rightOnly T b0 r true = true ∧
        ∀ j, k ≤ j → j < r → rowBlock T j false = true
    classical
    let u : ℕ → Bool := fun k => decide (PL k ∨ PR k)
    have hu_iff : ∀ k, u k = true ↔ PL k ∨ PR k := fun k => by
      simp [u]
    have hu0 : u 0 = b0 := by
      cases hb0 : b0
      · cases h : u 0
        · rfl
        · rw [hu_iff] at h
          rcases h with ⟨l, hl0, hL, _⟩ | ⟨r, _, hrn, hR, hB⟩
          · have : l = 0 := by omega
            subst this
            simp [leftOnly, hb0] at hL
          · exfalso
            apply hNoBad false 0 r (Nat.zero_le r) hrn
            exact ⟨by simp [leftOnly, hb0], hR, hB⟩
      · rw [hu_iff]
        left
        refine ⟨0, le_refl 0, by simp [leftOnly, hb0], fun j h1 h2 => by omega⟩
    have hun : u n = xor b0 (prefXor T n) := by
      cases hbn : xor b0 (prefXor T n)
      · cases h : u n
        · rfl
        · rw [hu_iff] at h
          rcases h with ⟨l, hln, hL, hB⟩ | ⟨r, hr1, hr2, hR, _⟩
          · exfalso
            apply hNoBad true l n hln (le_refl n)
            exact ⟨hL, by simp [rightOnly, hbn], hB⟩
          · have : r = n := by omega
            subst this
            simp [rightOnly, hbn] at hR
      · rw [hu_iff]
        right
        refine ⟨n, le_refl n, le_refl n, by simp [rightOnly, hbn], fun j h1 h2 => by omega⟩
    have hstep : ∀ i < n, relabT T i (u i) (u (i + 1)) = true := by
      intro i hi
      cases hstay : rowStay T i
      · apply cut_is_rect T hi hstay
        · by_contra hno
          have hall : ∀ y, relabT T i (u i) y = false := by
            intro y
            cases hval : relabT T i (u i) y
            · rfl
            · exfalso; exact hno ⟨y, hval⟩
          have hR : rightOnly T b0 i (!(u i)) = true := by
            unfold rightOnly
            have hne : i ≠ n := by omega
            simp only [hne, ↓reduceIte, Bool.not_not, Bool.and_eq_true, Bool.not_eq_true']
            exact ⟨hall false, hall true⟩
          cases hui : u i
          · rw [hui] at hR
            have hpr : PR i := ⟨i, le_refl i, by omega, hR, fun j h1 h2 => by omega⟩
            have : u i = true := (hu_iff i).mpr (Or.inr hpr)
            rw [hui] at this; cases this
          · rw [hui] at hR
            have hdisj := (hu_iff i).mp hui
            rcases hdisj with ⟨l, hli, hL, hB⟩ | ⟨r, hir, hrn, hRr, hB⟩
            · exact hNoBad true l i hli (by omega) ⟨hL, hR, hB⟩
            · by_cases heq : r = i
              · rw [heq] at hRr
                have hne := hNE i hi
                unfold rightOnly at hR hRr
                have hni : i ≠ n := by omega
                simp only [hni, ↓reduceIte, Bool.not_false, Bool.not_true, Bool.and_eq_true,
                  Bool.not_eq_true'] at hR hRr
                unfold rowNonEmpty at hne
                rw [hR.1, hR.2, hRr.1, hRr.2] at hne
                cases hne
              · have hbi := hB i (le_refl i) (by omega)
                unfold rowBlock at hbi
                simp only [Bool.and_eq_true] at hbi
                rw [hstay] at hbi
                cases hbi.1
        · by_contra hno
          have hall : ∀ x, relabT T i x (u (i + 1)) = false := by
            intro x
            cases hval : relabT T i x (u (i + 1))
            · rfl
            · exfalso; exact hno ⟨x, hval⟩
          have hL : leftOnly T b0 (i + 1) (!(u (i + 1))) = true := by
            unfold leftOnly
            simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
              Nat.add_sub_cancel, Bool.not_not, Bool.and_eq_true, Bool.not_eq_true']
            exact ⟨hall false, hall true⟩
          cases hui1 : u (i + 1)
          · rw [hui1] at hL
            have hpl : PL (i + 1) := ⟨i + 1, le_refl _, hL, fun j h1 h2 => by omega⟩
            have : u (i + 1) = true := (hu_iff (i + 1)).mpr (Or.inl hpl)
            rw [hui1] at this; cases this
          · rw [hui1] at hL
            have hdisj := (hu_iff (i + 1)).mp hui1
            rcases hdisj with ⟨l, hli, hLl, hB⟩ | ⟨r, hir, hrn, hRr, hB⟩
            · by_cases heq : l = i + 1
              · rw [heq] at hLl
                have hne := hNE i hi
                unfold leftOnly at hL hLl
                simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
                  Nat.add_sub_cancel, Bool.not_false, Bool.not_true, Bool.and_eq_true,
                  Bool.not_eq_true'] at hL hLl
                unfold rowNonEmpty at hne
                rw [hL.1, hL.2, hLl.1, hLl.2] at hne
                cases hne
              · have hbi := hB i (by omega) (by omega)
                unfold rowBlock at hbi
                simp only [Bool.and_eq_true] at hbi
                rw [hstay] at hbi
                cases hbi.1
            · exact hNoBad false (i + 1) r hir hrn ⟨hL, hRr, hB⟩
      · have hst : relabT T i false false = true ∧ relabT T i true true = true := by
          unfold rowStay at hstay
          simpa [Bool.and_eq_true] using hstay
        cases hui : u i <;> cases hui1 : u (i + 1)
        · exact hst.1
        · have hnoti : ¬ PL i ∧ ¬ PR i := by
            have := mt (hu_iff i).mpr
            rw [hui] at this
            simpa [not_or] using this
          have hdisj := (hu_iff (i + 1)).mp hui1
          rcases hdisj with ⟨l, hli, hL, hB⟩ | ⟨r, hir, hrn, hR, hB⟩
          · by_cases heq : l = i + 1
            · rw [heq] at hL
              unfold leftOnly at hL
              simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
                Nat.add_sub_cancel, Bool.not_true, Bool.and_eq_true, Bool.not_eq_true'] at hL
              rw [hst.1] at hL
              cases hL.1
            · exfalso
              exact hnoti.1 ⟨l, by omega, hL, fun j h1 h2 => hB j h1 (by omega)⟩
          · cases hft : relabT T i false true
            · exfalso
              apply hnoti.2
              refine ⟨r, by omega, hrn, hR, ?_⟩
              intro j h1 h2
              by_cases hji : j = i
              · subst hji
                unfold rowBlock
                simp [hstay, hft]
              · exact hB j (by omega) h2
            · rfl
        · have hnoti1 : ¬ PL (i + 1) ∧ ¬ PR (i + 1) := by
            have := mt (hu_iff (i + 1)).mpr
            rw [hui1] at this
            simpa [not_or] using this
          have hdisj := (hu_iff i).mp hui
          rcases hdisj with ⟨l, hli, hL, hB⟩ | ⟨r, hir, hrn, hR, hB⟩
          · cases htf : relabT T i true false
            · exfalso
              apply hnoti1.1
              refine ⟨l, by omega, hL, ?_⟩
              intro j h1 h2
              by_cases hji : j = i
              · subst hji
                unfold rowBlock
                simp [hstay, htf]
              · exact hB j h1 (by omega)
            · rfl
          · by_cases heq : r = i
            · rw [heq] at hR
              unfold rightOnly at hR
              have hni : i ≠ n := by omega
              simp only [hni, ↓reduceIte, Bool.not_true, Bool.and_eq_true, Bool.not_eq_true'] at hR
              rw [hst.1] at hR
              cases hR.1
            · exfalso
              exact hnoti1.2 ⟨r, by omega, hrn, hR, fun j h1 h2 => hB j (by omega) h2⟩
        · exact hst.2
    refine ⟨fun i => xor (u i.val) (prefXor T i.val), ?_⟩
    intro i
    have hs := hstep i.val i.isLt
    unfold relabT at hs
    simp only [i.isLt, ↓reduceDIte] at hs
    by_cases hlast : i.val + 1 = n
    · have hmod : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨0, hn⟩ := by
        ext; simp [hlast]
      rw [hmod]
      dsimp only
      rw [hlast] at hs
      rw [hun] at hs
      rw [hu0, prefXor]
      have hxeq : xor (xor b0 (prefXor T n)) (prefXor T n) = xor b0 false := by
        cases b0 <;> cases prefXor T n <;> rfl
      rw [hxeq] at hs
      exact hs
    · have hlt : i.val + 1 < n := by omega
      have hmod : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨i.val + 1, hlt⟩ := by
        ext; exact Nat.mod_eq_of_lt hlt
      rw [hmod]
      exact hs

def splits : ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ)
  | 0, _, _ => []
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      (lo, mid, hi) :: (splits fuel lo mid ++ splits fuel (mid + 1) hi)
    else []

lemma splits_bounds (fuel lo hi : ℕ) :
    ∀ s ∈ splits fuel lo hi, lo ≤ s.1 ∧ s.1 ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ hi := by
  induction fuel generalizing lo hi with
  | zero => intro s hs; simp [splits] at hs
  | succ fuel ih =>
    intro s hs
    unfold splits at hs
    split_ifs at hs with hlt
    · simp only [List.mem_cons, List.mem_append] at hs
      rcases hs with rfl | h1 | h2
      · dsimp only; omega
      · have := ih lo ((lo + hi) / 2) s h1; omega
      · have := ih ((lo + hi) / 2 + 1) hi s h2; omega
    · simp at hs

lemma splits_cover (fuel lo hi l r : ℕ) (hfuel : hi - lo ≤ fuel)
    (hl : lo ≤ l) (hlr : l < r) (hr : r ≤ hi) :
    ∃ s ∈ splits fuel lo hi, s.1 ≤ l ∧ l ≤ s.2.1 ∧ s.2.1 + 1 ≤ r ∧ r ≤ s.2.2 := by
  induction fuel generalizing lo hi with
  | zero => omega
  | succ fuel ih =>
    unfold splits
    have hlt : lo < hi := by omega
    simp only [hlt, ↓reduceIte]
    set mid := (lo + hi) / 2
    by_cases h1 : r ≤ mid
    · rcases ih lo mid (by omega) hl h1 with ⟨s, hs, hcond⟩
      exact ⟨s, List.mem_cons_of_mem _ (List.mem_append_left _ hs), hcond⟩
    · by_cases h2 : mid + 1 ≤ l
      · rcases ih (mid + 1) hi (by omega) h2 hr with ⟨s, hs, hcond⟩
        exact ⟨s, List.mem_cons_of_mem _ (List.mem_append_right _ hs), hcond⟩
      · refine ⟨(lo, mid, hi), List.mem_cons_self, ?_⟩
        dsimp only
        omega

lemma splits_length_le (fuel lo hi : ℕ) :
    (splits fuel lo hi).length ≤ hi - lo := by
  induction fuel generalizing lo hi with
  | zero => simp [splits]
  | succ fuel ih =>
    unfold splits
    split_ifs with hlt
    · simp only [List.length_cons, List.length_append]
      have h1 := ih lo ((lo + hi) / 2)
      have h2 := ih ((lo + hi) / 2 + 1) hi
      omega
    · simp

lemma log2_mono {a b : ℕ} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right h

lemma splits_span_sum_le (fuel lo hi : ℕ) :
    ((splits fuel lo hi).map (fun s => s.2.2 - s.1 + 1)).sum ≤
      2 * (hi - lo) * (Nat.log2 (hi - lo) + 1) := by
  have hmain : ∀ d : ℕ, ∀ fuel lo hi : ℕ, hi - lo = d →
      ((splits fuel lo hi).map (fun s => s.2.2 - s.1 + 1)).sum ≤
        2 * d * (Nat.log2 d + 1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro fuel lo hi hd
      cases fuel with
      | zero => simp [splits]
      | succ fuel =>
        unfold splits
        split_ifs with hlt
        · simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
          set mid := (lo + hi) / 2
          set d1 := mid - lo
          set d2 := hi - (mid + 1)
          have hd1 : d1 < d := by omega
          have hd2 : d2 < d := by omega
          have h1 := ih d1 hd1 fuel lo mid rfl
          have h2 := ih d2 hd2 fuel (mid + 1) hi rfl
          by_cases hd1eq : d = 1
          · subst hd1eq
            have hd1z : d1 = 0 := by omega
            have hd2z : d2 = 0 := by omega
            rw [hd1z] at h1
            rw [hd2z] at h2
            simp only [Nat.mul_zero, Nat.zero_mul] at h1 h2
            have hlog1 : Nat.log2 1 = 0 := by decide
            rw [hlog1]
            omega
          · have hdge2 : 2 ≤ d := by omega
            have hlog_div : Nat.log2 (d / 2) + 1 = Nat.log2 d := by
              rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
              have := Nat.log_div_base 2 d
              have hpos : 1 ≤ Nat.log 2 d := by
                have := Nat.log_mono_right (b := 2) hdge2
                have h2 : Nat.log 2 2 = 1 := by decide
                omega
              omega
            have hl1 : Nat.log2 d1 + 1 ≤ Nat.log2 d := by
              have : d1 = d / 2 := by omega
              rw [this]; omega
            have hl2 : Nat.log2 d2 + 1 ≤ Nat.log2 d := by
              have hle : d2 ≤ d / 2 := by omega
              have hmono := log2_mono hle
              omega
            have hmul1 : 2 * d1 * (Nat.log2 d1 + 1) ≤ 2 * d1 * Nat.log2 d :=
              Nat.mul_le_mul_left _ hl1
            have hmul2 : 2 * d2 * (Nat.log2 d2 + 1) ≤ 2 * d2 * Nat.log2 d :=
              Nat.mul_le_mul_left _ hl2
            have hsumd : d1 + d2 = d - 1 := by omega
            have hcomb : 2 * d1 * Nat.log2 d + 2 * d2 * Nat.log2 d ≤ 2 * d * Nat.log2 d := by
              have : 2 * d1 * Nat.log2 d + 2 * d2 * Nat.log2 d =
                  2 * (d1 + d2) * Nat.log2 d := by
                rw [← Nat.add_mul, ← Nat.mul_add]
              rw [this]
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by omega))
            have hstep : d + 1 + 2 * d * Nat.log2 d ≤ 2 * d * (Nat.log2 d + 1) := by
              rw [Nat.mul_add, Nat.mul_one]; omega
            omega
        · simp
  exact hmain (hi - lo) fuel lo hi rfl

lemma splits_sq_sum_le (fuel lo hi : ℕ) :
    ((splits fuel lo hi).map (fun s => (s.2.2 - s.1 + 1) ^ 2)).sum ≤ 4 * (hi - lo) ^ 2 := by
  have hmain : ∀ d : ℕ, ∀ fuel lo hi : ℕ, hi - lo = d →
      ((splits fuel lo hi).map (fun s => (s.2.2 - s.1 + 1) ^ 2)).sum ≤ 4 * d ^ 2 := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro fuel lo hi hd
      cases fuel with
      | zero => simp [splits]
      | succ fuel =>
        unfold splits
        split_ifs with hlt
        · simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
          set mid := (lo + hi) / 2
          set d1 := mid - lo
          set d2 := hi - (mid + 1)
          have h1 := ih d1 (by omega) fuel lo mid rfl
          have h2 := ih d2 (by omega) fuel (mid + 1) hi rfl
          have hsq : (d + 1) ^ 2 + 4 * d1 ^ 2 + 4 * d2 ^ 2 ≤ 4 * d ^ 2 := by
            have hd1 : d1 = d / 2 := by omega
            have hd2 : d2 ≤ d / 2 := by omega
            have hle : d2 ^ 2 ≤ (d / 2) ^ 2 := Nat.pow_le_pow_left hd2 2
            have h2d : 2 * (d / 2) ≤ d := Nat.mul_div_le d 2
            have h4sq : 4 * (d / 2) ^ 2 ≤ d ^ 2 := by
              have hpow : (2 * (d / 2)) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left h2d 2
              have heq : (2 * (d / 2)) ^ 2 = 4 * (d / 2) ^ 2 := by
                rw [Nat.mul_pow]
              omega
            by_cases hsmall : d ≤ 2
            · have hpos : 1 ≤ d := by omega
              interval_cases d
              · have : d1 = 0 := by omega
                have : d2 = 0 := by omega
                rw [‹d1 = 0›, ‹d2 = 0›]; norm_num
              · have : d1 = 1 := by omega
                have : d2 = 0 := by omega
                rw [‹d1 = 1›, ‹d2 = 0›]; norm_num
            · have h3 : 3 ≤ d := by omega
              have hdp : (d + 1) ^ 2 ≤ 2 * d ^ 2 := by
                have h3d : 3 * d ≤ d * d := Nat.mul_le_mul_right d h3
                have hexp : (d + 1) ^ 2 = d * d + 2 * d + 1 := by
                  rw [Nat.pow_two, Nat.add_mul, Nat.mul_add]; omega
                have hsq2 : d ^ 2 = d * d := Nat.pow_two d
                omega
              have hcomb : 4 * d1 ^ 2 + 4 * d2 ^ 2 ≤ 2 * d ^ 2 := by
                rw [hd1]
                omega
              omega
          rw [hd]
          omega
        · simp
  exact hmain (hi - lo) fuel lo hi rfl

def boolIdx (b : Bool) : ℕ := if b then 1 else 0

def wireFalse (n : ℕ) : ℕ := 6 * n
def wireTrue (n : ℕ) : ℕ := 6 * n + 1
def wireS (n k : ℕ) : ℕ := if k = 0 then wireFalse n else 6 * n + 2 + (k - 1)
def wireNS (n k : ℕ) : ℕ := if k = 0 then wireTrue n else 5 * n + (k - 1)
def wireT4 (n i : ℕ) (a b u v : Bool) : ℕ :=
  7 * n + 2 + 16 * i + 4 * pairIdx a b + pairIdx u v
def wireT' (n i : ℕ) (a b : Bool) : ℕ := 23 * n + 2 + 4 * i + pairIdx a b
def wireNT' (n i : ℕ) (a b : Bool) : ℕ := 27 * n + 2 + 4 * i + pairIdx a b
def wireNE (n i : ℕ) : ℕ := 31 * n + 2 + i
def wireBlock (n i : ℕ) (a : Bool) : ℕ := 32 * n + 2 + 2 * i + boolIdx a
def wireLeftMid (n i : ℕ) (a : Bool) : ℕ := 34 * n + 2 + 2 * i + boolIdx a
def wireRightMid (n i : ℕ) (b : Bool) : ℕ := 36 * n + 2 + 2 * i + boolIdx b

def wireLeft (n : ℕ) (b0 : Bool) (l : ℕ) (a : Bool) : ℕ :=
  if l = 0 then (if a = b0 then wireTrue n else wireFalse n)
  else wireLeftMid n (l - 1) a

def wireRight (n : ℕ) (b0 : Bool) (r : ℕ) (b : Bool) : ℕ :=
  if r = n then (if b = b0 then wireNS n n else wireS n n)
  else wireRightMid n r b

def base7 (n : ℕ) : ℕ := 38 * n + 2

def layer1 (n : ℕ) : List Gate :=
  (List.range n).map (fun i => ⟨.and, [4 * i + 1, 4 * i + 2]⟩)

def layer2 (n : ℕ) : List Gate :=
  (List.range n).map (fun j => ⟨.mod 2, (List.range (j + 1)).map (fun i => 4 * n + i)⟩)

def layer3 (n : ℕ) : List Gate :=
  [⟨.or, []⟩, ⟨.and, []⟩] ++ (List.range n).map (fun j => ⟨.not, [5 * n + j]⟩)

def boolPairs : List (Bool × Bool) :=
  [(false, false), (true, false), (false, true), (true, true)]

def layer4 (n : ℕ) : List Gate :=
  (List.range n).flatMap fun i =>
    boolPairs.flatMap fun ab =>
      boolPairs.map fun uv =>
        ⟨.and, [if uv.1 then wireS n i else wireNS n i,
                if uv.2 then wireS n (i + 1) else wireNS n (i + 1),
                4 * i + pairIdx (xor ab.1 uv.1) (xor ab.2 uv.2)]⟩

def layer5 (n : ℕ) : List Gate :=
  (List.range n).flatMap fun i =>
    boolPairs.map fun ab =>
      ⟨.or, boolPairs.map fun uv => wireT4 n i ab.1 ab.2 uv.1 uv.2⟩

def layer6 (n : ℕ) : List Gate :=
  ((List.range n).flatMap fun i =>
    boolPairs.map fun ab => ⟨.not, [wireT' n i ab.1 ab.2]⟩) ++
  (List.range n).map fun i =>
    ⟨.or, boolPairs.map fun ab => wireT' n i ab.1 ab.2⟩

def layer7 (n : ℕ) : List Gate :=
  ((List.range n).flatMap fun i =>
    [false, true].map fun a =>
      ⟨.and, [wireT' n i false false, wireT' n i true true, wireNT' n i a (!a)]⟩) ++
  ((List.range n).flatMap fun i =>
    [false, true].map fun a =>
      ⟨.and, [wireNT' n i false (!a), wireNT' n i true (!a)]⟩) ++
  ((List.range n).flatMap fun i =>
    [false, true].map fun b =>
      ⟨.and, [wireNT' n i (!b) false, wireNT' n i (!b) true]⟩)

def prefix7 (n : ℕ) : List Gate :=
  layer1 n ++ layer2 n ++ layer3 n ++ layer4 n ++ layer5 n ++ layer6 n ++ layer7 n

def diagGates (n : ℕ) (b0 : Bool) : List Gate :=
  [false, true].flatMap fun a =>
    (List.range (n + 1)).map fun l =>
      ⟨.and, [wireLeft n b0 l a, wireRight n b0 l (!a)]⟩

def splitGadget (n : ℕ) (b0 a : Bool) (base : ℕ) (s : ℕ × ℕ × ℕ) : List Gate :=
  let lo := s.1
  let mid := s.2.1
  let hi := s.2.2
  let kL := mid + 1 - lo
  let kR := hi - mid
  let lGates := (List.range kL).map fun idx =>
    let l := lo + idx
    ⟨.and, wireLeft n b0 l a :: (List.range (mid + 1 - l)).map (fun t => wireBlock n (l + t) a)⟩
  let rGates := (List.range kR).map fun idx =>
    let r := mid + 1 + idx
    ⟨.and, wireRight n b0 r (!a) :: (List.range (r - (mid + 1))).map (fun t => wireBlock n (mid + 1 + t) a)⟩
  let hasL : Gate := ⟨.or, (List.range kL).map (fun idx => base + idx)⟩
  let hasR : Gate := ⟨.or, (List.range kR).map (fun idx => base + kL + idx)⟩
  let badS : Gate := ⟨.and, [base + kL + kR, base + kL + kR + 1]⟩
  lGates ++ rGates ++ [hasL, hasR, badS]

def appendSplitGadgets (n : ℕ) (b0 a : Bool) (S : List (ℕ × ℕ × ℕ))
    (gs : List Gate) (outs : List ℕ) : List Gate × List ℕ :=
  S.foldl (fun acc s =>
    let base := 4 * n + acc.1.length
    let gad := splitGadget n b0 a base s
    (acc.1 ++ gad, acc.2 ++ [base + gad.length - 1])) (gs, outs)

def buildForB0 (n : ℕ) (b0 : Bool) (gs : List Gate) : List Gate × ℕ :=
  let baseDiag := 4 * n + gs.length
  let dg := diagGates n b0
  let diagOuts := (List.range dg.length).map (fun i => baseDiag + i)
  let gs1 := gs ++ dg
  let S := splits (n + 1) 0 n
  let (gs2, outs2) := appendSplitGadgets n b0 false S gs1 diagOuts
  let (gs3, outs3) := appendSplitGadgets n b0 true S gs2 outs2
  let wAnyBad := 4 * n + gs3.length
  let gAnyBad : Gate := ⟨.or, outs3⟩
  let wNoBad := wAnyBad + 1
  let gNoBad : Gate := ⟨.not, [wAnyBad]⟩
  let wOk := wAnyBad + 2
  let gOk : Gate := ⟨.and, wNoBad :: (List.range n).map (fun i => wireNE n i)⟩
  (gs3 ++ [gAnyBad, gNoBad, gOk], wOk)

def buildCircuit (n : ℕ) : Circuit :=
  let gs0 := prefix7 n
  let (gs1, wOk0) := buildForB0 n false gs0
  let (gs2, wOk1) := buildForB0 n true gs1
  let wOut := 4 * n + gs2.length
  { gates := gs2 ++ [⟨.or, [wOk0, wOk1]⟩], output := wOut }

lemma layer1_len (n : ℕ) : (layer1 n).length = n := by simp [layer1]
lemma layer2_len (n : ℕ) : (layer2 n).length = n := by simp [layer2]
lemma layer3_len (n : ℕ) : (layer3 n).length = n + 2 := by
  simp only [layer3, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  omega
lemma layer4_len (n : ℕ) : (layer4 n).length = 16 * n := by
  simp [layer4, boolPairs, List.length_flatMap]; omega
lemma layer5_len (n : ℕ) : (layer5 n).length = 4 * n := by
  simp [layer5, boolPairs, List.length_flatMap]; omega
lemma layer6_len (n : ℕ) : (layer6 n).length = 5 * n := by
  simp [layer6, boolPairs, List.length_flatMap]; omega
lemma layer7_len (n : ℕ) : (layer7 n).length = 6 * n := by
  simp [layer7, List.length_flatMap]; omega

lemma prefix7_len (n : ℕ) : (prefix7 n).length = 34 * n + 2 := by
  unfold prefix7
  simp only [List.length_append, layer1_len, layer2_len, layer3_len, layer4_len,
    layer5_len, layer6_len, layer7_len]
  omega

lemma base7_eq (n : ℕ) : base7 n = 4 * n + (prefix7 n).length := by
  rw [base7, prefix7_len]; omega

lemma wireS_lt (n k : ℕ) (hk : k ≤ n) : wireS n k < 7 * n + 2 := by
  unfold wireS wireFalse; split_ifs <;> omega

lemma wireNS_lt (n k : ℕ) (hk : k ≤ n) : wireNS n k < 7 * n + 2 := by
  unfold wireNS wireTrue; split_ifs <;> omega

lemma wireT4_lt (n i : ℕ) (hi : i < n) (a b u v : Bool) : wireT4 n i a b u v < 23 * n + 2 := by
  unfold wireT4
  have := pairIdx_lt a b
  have := pairIdx_lt u v
  omega

lemma wireT'_lt (n i : ℕ) (hi : i < n) (a b : Bool) : wireT' n i a b < 27 * n + 2 := by
  unfold wireT'
  have := pairIdx_lt a b
  omega

lemma wireNT'_lt (n i : ℕ) (hi : i < n) (a b : Bool) : wireNT' n i a b < 32 * n + 2 := by
  unfold wireNT'
  have := pairIdx_lt a b
  omega

lemma wireNE_lt (n i : ℕ) (hi : i < n) : wireNE n i < base7 n := by
  unfold wireNE base7; omega

lemma wireBlock_lt (n i : ℕ) (hi : i < n) (a : Bool) : wireBlock n i a < base7 n := by
  unfold wireBlock boolIdx base7; split_ifs <;> omega

lemma wireLeft_lt (n : ℕ) (b0 : Bool) (l : ℕ) (hl : l ≤ n) (a : Bool) :
    wireLeft n b0 l a < base7 n := by
  unfold wireLeft wireTrue wireFalse wireLeftMid boolIdx base7
  split_ifs <;> omega

lemma wireRight_lt (n : ℕ) (b0 : Bool) (r : ℕ) (hr : r ≤ n) (b : Bool) :
    wireRight n b0 r b < base7 n := by
  unfold wireRight wireNS wireS wireTrue wireFalse wireRightMid boolIdx base7
  split_ifs <;> omega

lemma layer1_inputs_lt (n : ℕ) : ∀ g ∈ layer1 n, ∀ i ∈ g.inputs, i < 4 * n := by
  intro g hg i hi
  simp only [layer1, List.mem_map, List.mem_range] at hg
  rcases hg with ⟨j, hj, rfl⟩
  simp at hi
  omega

lemma layer2_inputs_lt (n : ℕ) : ∀ g ∈ layer2 n, ∀ i ∈ g.inputs, i < 5 * n := by
  intro g hg i hi
  simp only [layer2, List.mem_map, List.mem_range] at hg
  rcases hg with ⟨j, hj, rfl⟩
  simp only [List.mem_map, List.mem_range] at hi
  rcases hi with ⟨k, hk, rfl⟩
  omega

lemma layer3_inputs_lt (n : ℕ) : ∀ g ∈ layer3 n, ∀ i ∈ g.inputs, i < 6 * n := by
  intro g hg i hi
  simp only [layer3, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range] at hg
  rcases hg with (rfl | rfl) | ⟨j, hj, rfl⟩
  · simp at hi
  · simp at hi
  · simp at hi; omega

lemma layer4_inputs_lt (n : ℕ) : ∀ g ∈ layer4 n, ∀ i ∈ g.inputs, i < 7 * n + 2 := by
  intro g hg i hi
  simp only [layer4, List.mem_flatMap, List.mem_range, List.mem_map] at hg
  rcases hg with ⟨idx, hidx, ab, _, uv, _, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · split_ifs
    · exact wireS_lt n idx (by omega)
    · exact wireNS_lt n idx (by omega)
  · split_ifs
    · exact wireS_lt n (idx + 1) (by omega)
    · exact wireNS_lt n (idx + 1) (by omega)
  · have := pairIdx_lt (xor ab.1 uv.1) (xor ab.2 uv.2); omega

lemma layer5_inputs_lt (n : ℕ) : ∀ g ∈ layer5 n, ∀ i ∈ g.inputs, i < 23 * n + 2 := by
  intro g hg i hi
  simp only [layer5, List.mem_flatMap, List.mem_range, List.mem_map] at hg
  rcases hg with ⟨idx, hidx, ab, _, rfl⟩
  simp only [List.mem_map] at hi
  rcases hi with ⟨uv, _, rfl⟩
  exact wireT4_lt n idx hidx ab.1 ab.2 uv.1 uv.2

lemma layer6_inputs_lt (n : ℕ) : ∀ g ∈ layer6 n, ∀ i ∈ g.inputs, i < 27 * n + 2 := by
  intro g hg i hi
  simp only [layer6, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map] at hg
  rcases hg with ⟨idx, hidx, ab, _, rfl⟩ | ⟨idx, hidx, rfl⟩
  · simp at hi; subst hi; exact wireT'_lt n idx hidx ab.1 ab.2
  · simp only [List.mem_map] at hi
    rcases hi with ⟨ab, _, rfl⟩
    exact wireT'_lt n idx hidx ab.1 ab.2

lemma layer7_inputs_lt (n : ℕ) : ∀ g ∈ layer7 n, ∀ i ∈ g.inputs, i < 32 * n + 2 := by
  intro g hg i hi
  simp only [layer7, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map] at hg
  rcases hg with (⟨idx, hidx, a, _, rfl⟩ | ⟨idx, hidx, a, _, rfl⟩) | ⟨idx, hidx, b, _, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact Nat.lt_trans (wireT'_lt n idx hidx false false) (by omega)
    · exact Nat.lt_trans (wireT'_lt n idx hidx true true) (by omega)
    · exact wireNT'_lt n idx hidx a (!a)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact wireNT'_lt n idx hidx false (!a)
    · exact wireNT'_lt n idx hidx true (!a)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact wireNT'_lt n idx hidx (!b) false
    · exact wireNT'_lt n idx hidx (!b) true

lemma prefix7_readsBack (n out : ℕ) : ReadsBack (4 * n) ⟨prefix7 n, out⟩ := by
  unfold prefix7
  have h0 : ReadsBack (4 * n) ⟨[], out⟩ := fun j hj => by simp at hj
  have h1 := readsBack_append_layer (4 * n) [] (layer1 n) out h0
    (fun g hg i hi => by simpa using layer1_inputs_lt n g hg i hi)
  simp only [List.nil_append] at h1
  have h2 := readsBack_append_layer (4 * n) (layer1 n) (layer2 n) out h1
    (fun g hg i hi => by rw [layer1_len]; have := layer2_inputs_lt n g hg i hi; omega)
  have h3 := readsBack_append_layer (4 * n) _ (layer3 n) out h2
    (fun g hg i hi => by simp only [List.length_append, layer1_len, layer2_len]; have := layer3_inputs_lt n g hg i hi; omega)
  have h4 := readsBack_append_layer (4 * n) _ (layer4 n) out h3
    (fun g hg i hi => by simp only [List.length_append, layer1_len, layer2_len, layer3_len]; have := layer4_inputs_lt n g hg i hi; omega)
  have h5 := readsBack_append_layer (4 * n) _ (layer5 n) out h4
    (fun g hg i hi => by simp only [List.length_append, layer1_len, layer2_len, layer3_len, layer4_len]; have := layer5_inputs_lt n g hg i hi; omega)
  have h6 := readsBack_append_layer (4 * n) _ (layer6 n) out h5
    (fun g hg i hi => by simp only [List.length_append, layer1_len, layer2_len, layer3_len, layer4_len, layer5_len]; have := layer6_inputs_lt n g hg i hi; omega)
  have h7 := readsBack_append_layer (4 * n) _ (layer7 n) out h6
    (fun g hg i hi => by simp only [List.length_append, layer1_len, layer2_len, layer3_len, layer4_len, layer5_len, layer6_len]; have := layer7_inputs_lt n g hg i hi; omega)
  exact h7

lemma prefix7_depth_le (n : ℕ) :
    ∀ i < base7 n, (evalDepths (prefix7 n) (List.replicate (4 * n) 0)).getD i 0 ≤ 7 := by
  unfold prefix7
  set d0 := List.replicate (4 * n) 0
  have hd0_len : d0.length = 4 * n := by simp [d0]
  have hd0 : ∀ i < d0.length, d0.getD i 0 ≤ 0 := by
    intro i hi; simp [d0, List.getD_eq_getElem _ _ hi]
  set d1 := evalDepths (layer1 n) d0
  have hd1_len : d1.length = 5 * n := by rw [evalDepths_length, hd0_len, layer1_len]; omega
  have hd1 := evalDepths_layer_le (layer1 n) d0 0 hd0
    (fun g hg i hi => by rw [hd0_len]; exact layer1_inputs_lt n g hg i hi)
  set d2 := evalDepths (layer2 n) d1
  have hd2_len : d2.length = 6 * n := by rw [evalDepths_length, hd1_len, layer2_len]; omega
  have hd2 := evalDepths_layer_le (layer2 n) d1 1 hd1
    (fun g hg i hi => by rw [hd1_len]; exact layer2_inputs_lt n g hg i hi)
  set d3 := evalDepths (layer3 n) d2
  have hd3_len : d3.length = 7 * n + 2 := by rw [evalDepths_length, hd2_len, layer3_len]; omega
  have hd3 := evalDepths_layer_le (layer3 n) d2 2 hd2
    (fun g hg i hi => by rw [hd2_len]; exact layer3_inputs_lt n g hg i hi)
  set d4 := evalDepths (layer4 n) d3
  have hd4_len : d4.length = 23 * n + 2 := by rw [evalDepths_length, hd3_len, layer4_len]; omega
  have hd4 := evalDepths_layer_le (layer4 n) d3 3 hd3
    (fun g hg i hi => by rw [hd3_len]; exact layer4_inputs_lt n g hg i hi)
  set d5 := evalDepths (layer5 n) d4
  have hd5_len : d5.length = 27 * n + 2 := by rw [evalDepths_length, hd4_len, layer5_len]; omega
  have hd5 := evalDepths_layer_le (layer5 n) d4 4 hd4
    (fun g hg i hi => by rw [hd4_len]; exact layer5_inputs_lt n g hg i hi)
  set d6 := evalDepths (layer6 n) d5
  have hd6_len : d6.length = 32 * n + 2 := by rw [evalDepths_length, hd5_len, layer6_len]; omega
  have hd6 := evalDepths_layer_le (layer6 n) d5 5 hd5
    (fun g hg i hi => by rw [hd5_len]; exact layer6_inputs_lt n g hg i hi)
  set d7 := evalDepths (layer7 n) d6
  have hd7_len : d7.length = base7 n := by rw [evalDepths_length, hd6_len, layer7_len, base7]; omega
  have hd7 := evalDepths_layer_le (layer7 n) d6 6 hd6
    (fun g hg i hi => by rw [hd6_len]; exact layer7_inputs_lt n g hg i hi)
  have heq : evalDepths (layer1 n ++ layer2 n ++ layer3 n ++ layer4 n ++ layer5 n ++ layer6 n ++ layer7 n) d0 = d7 := by
    simp only [d7, d6, d5, d4, d3, d2, d1, evalDepths_append]
  rw [heq]
  intro i hi
  exact hd7 i (by rw [hd7_len]; exact hi)

def IsAON (g : Gate) : Prop := g.op = .and ∨ g.op = .or ∨ g.op = .not

lemma layer3_aon (n : ℕ) : ∀ g ∈ layer3 n, IsAON g := by
  intro g hg
  simp only [layer3, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hg
  rcases hg with (rfl | rfl) | ⟨_, _, rfl⟩ <;> simp [IsAON]

lemma layer4_aon (n : ℕ) : ∀ g ∈ layer4 n, IsAON g := by
  intro g hg
  simp only [layer4, List.mem_flatMap, List.mem_map] at hg
  rcases hg with ⟨_, _, _, _, _, _, rfl⟩; simp [IsAON]

lemma layer5_aon (n : ℕ) : ∀ g ∈ layer5 n, IsAON g := by
  intro g hg
  simp only [layer5, List.mem_flatMap, List.mem_map] at hg
  rcases hg with ⟨_, _, _, _, rfl⟩; simp [IsAON]

lemma layer6_aon (n : ℕ) : ∀ g ∈ layer6 n, IsAON g := by
  intro g hg
  simp only [layer6, List.mem_append, List.mem_flatMap, List.mem_map] at hg
  rcases hg with ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> simp [IsAON]

lemma layer7_aon (n : ℕ) : ∀ g ∈ layer7 n, IsAON g := by
  intro g hg
  simp only [layer7, List.mem_append, List.mem_flatMap, List.mem_map] at hg
  rcases hg with (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) | ⟨_, _, _, _, rfl⟩ <;> simp [IsAON]

lemma list_sum_map_le {α : Type*} (l : List α) (f : α → ℕ) (B : ℕ) (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    rw [Nat.add_mul, Nat.one_mul]
    omega

lemma prefix7_fanin_le (n : ℕ) :
    ((prefix7 n).map (fun g => g.inputs.length)).sum ≤ n * n + 105 * n := by
  have h1 : ((layer1 n).map (fun g => g.inputs.length)).sum ≤ n * 2 := by
    have h := list_sum_map_le (layer1 n) (fun g => g.inputs.length) 2 (fun g hg => by
      simp only [layer1, List.mem_map] at hg; rcases hg with ⟨_, _, rfl⟩; simp)
    rw [layer1_len] at h; exact h
  have h2 : ((layer2 n).map (fun g => g.inputs.length)).sum ≤ n * n := by
    have h := list_sum_map_le (layer2 n) (fun g => g.inputs.length) n (fun g hg => by
      simp only [layer2, List.mem_map, List.mem_range] at hg
      rcases hg with ⟨j, hj, rfl⟩; simp; omega)
    rw [layer2_len] at h; exact h
  have h3 : ((layer3 n).map (fun g => g.inputs.length)).sum ≤ n := by
    have h := list_sum_map_le ((List.range n).map (fun j => (⟨.not, [5 * n + j]⟩ : Gate)))
      (fun g => g.inputs.length) 1 (fun g hg => by
        simp only [List.mem_map] at hg; rcases hg with ⟨_, _, rfl⟩; simp)
    simp only [List.length_map, List.length_range, Nat.mul_one] at h
    unfold layer3
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_nil, Nat.zero_add]
    exact h
  have h4 : ((layer4 n).map (fun g => g.inputs.length)).sum ≤ (16 * n) * 3 := by
    have h := list_sum_map_le (layer4 n) (fun g => g.inputs.length) 3 (fun g hg => by
      simp only [layer4, List.mem_flatMap, List.mem_map] at hg
      rcases hg with ⟨_, _, _, _, _, _, rfl⟩; simp)
    rw [layer4_len] at h; exact h
  have h5 : ((layer5 n).map (fun g => g.inputs.length)).sum ≤ (4 * n) * 4 := by
    have h := list_sum_map_le (layer5 n) (fun g => g.inputs.length) 4 (fun g hg => by
      simp only [layer5, List.mem_flatMap, List.mem_map] at hg
      rcases hg with ⟨_, _, _, _, rfl⟩; simp [boolPairs])
    rw [layer5_len] at h; exact h
  have h6 : ((layer6 n).map (fun g => g.inputs.length)).sum ≤ (5 * n) * 4 := by
    have h := list_sum_map_le (layer6 n) (fun g => g.inputs.length) 4 (fun g hg => by
      simp only [layer6, List.mem_append, List.mem_flatMap, List.mem_map] at hg
      rcases hg with ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩
      · simp
      · simp [boolPairs])
    rw [layer6_len] at h; exact h
  have h7 : ((layer7 n).map (fun g => g.inputs.length)).sum ≤ (6 * n) * 3 := by
    have h := list_sum_map_le (layer7 n) (fun g => g.inputs.length) 3 (fun g hg => by
      simp only [layer7, List.mem_append, List.mem_flatMap, List.mem_map] at hg
      rcases hg with (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) | ⟨_, _, _, _, rfl⟩ <;> simp)
    rw [layer7_len] at h; exact h
  unfold prefix7
  simp only [List.map_append, List.sum_append]
  omega

lemma getElem_idx {α : Type*} {l : List α} {i j : ℕ} (h : i = j) (hi : i < l.length) :
    l[i]'hi = l[j]'(h ▸ hi) := by
  subst h; rfl

lemma flatMap_const_len_getElem {α β : Type*} (l : List α) (f : α → List β) (c : ℕ)
    (hc : ∀ a ∈ l, (f a).length = c) (i j : ℕ) (hi : i < l.length) (hj : j < c)
    (hidx : i * c + j < (l.flatMap f).length) :
    (l.flatMap f)[i * c + j]'hidx = (f (l[i]'hi))[j]'(by rw [hc _ (List.getElem_mem hi)]; exact hj) := by
  induction l generalizing i with
  | nil => cases hi
  | cons a tl ih =>
    simp only [List.flatMap_cons]
    have ha : (f a).length = c := hc a List.mem_cons_self
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem_append_left (by omega)]
    | succ i' =>
      have hi' : i' < tl.length := by simpa using hi
      have hge : (f a).length ≤ (i' + 1) * c + j := by rw [ha, Nat.add_mul, Nat.one_mul]; omega
      rw [List.getElem_append_right hge]
      have hsub : (i' + 1) * c + j - (f a).length = i' * c + j := by
        rw [ha, Nat.add_mul, Nat.one_mul]; omega
      have hlen_tl : i' * c + j < (tl.flatMap f).length := by
        rw [List.flatMap_cons, List.length_append] at hidx
        omega
      rw [getElem_idx hsub]
      simp only [List.getElem_cons_succ]
      exact ih (fun b hb => hc b (List.mem_cons_of_mem a hb)) i' hi' hlen_tl

lemma boolPairs_getElem (a b : Bool) :
    boolPairs[pairIdx a b]'(by have := pairIdx_lt a b; simpa [boolPairs] using this) = (a, b) := by
  cases a <;> cases b <;> rfl

lemma layer4_getElem (n i : ℕ) (hi : i < n) (a b u v : Bool)
    (hk : 16 * i + 4 * pairIdx a b + pairIdx u v < (layer4 n).length) :
    (layer4 n)[16 * i + 4 * pairIdx a b + pairIdx u v]'hk =
      ⟨.and, [if u then wireS n i else wireNS n i,
              if v then wireS n (i + 1) else wireNS n (i + 1),
              4 * i + pairIdx (xor a u) (xor b v)]⟩ := by
  have hpa := pairIdx_lt a b
  have hpu := pairIdx_lt u v
  have hidx1 : 16 * i + 4 * pairIdx a b + pairIdx u v = i * 16 + (pairIdx a b * 4 + pairIdx u v) := by omega
  rw [getElem_idx hidx1]
  unfold layer4
  rw [flatMap_const_len_getElem (List.range n) _ 16
    (fun _ _ => by simp [boolPairs, List.length_flatMap]) i (pairIdx a b * 4 + pairIdx u v)
    (by simp [hi]) (by omega)]
  simp only [List.getElem_range]
  rw [flatMap_const_len_getElem boolPairs _ 4
    (fun _ _ => by simp [boolPairs]) (pairIdx a b) (pairIdx u v)
    (by simpa [boolPairs] using hpa) hpu]
  rw [boolPairs_getElem, List.getElem_map, boolPairs_getElem]

lemma layer5_getElem (n i : ℕ) (hi : i < n) (a b : Bool)
    (hk : 4 * i + pairIdx a b < (layer5 n).length) :
    (layer5 n)[4 * i + pairIdx a b]'hk =
      ⟨.or, boolPairs.map fun uv => wireT4 n i a b uv.1 uv.2⟩ := by
  have hpa := pairIdx_lt a b
  have hidx : 4 * i + pairIdx a b = i * 4 + pairIdx a b := by omega
  rw [getElem_idx hidx]
  unfold layer5
  rw [flatMap_const_len_getElem (List.range n) _ 4
    (fun _ _ => by simp [boolPairs]) i (pairIdx a b) (by simp [hi]) hpa]
  simp only [List.getElem_range, List.getElem_map, boolPairs_getElem]

lemma layer6_getElem_not (n i : ℕ) (hi : i < n) (a b : Bool)
    (hk : 4 * i + pairIdx a b < (layer6 n).length) :
    (layer6 n)[4 * i + pairIdx a b]'hk = ⟨.not, [wireT' n i a b]⟩ := by
  have hpa := pairIdx_lt a b
  set l1 := (List.range n).flatMap fun i =>
      boolPairs.map fun ab => (⟨.not, [wireT' n i ab.1 ab.2]⟩ : Gate)
  set l2 := (List.range n).map fun i =>
      (⟨.or, boolPairs.map fun ab => wireT' n i ab.1 ab.2⟩ : Gate)
  have hlen1 : l1.length = 4 * n := by simp [l1, boolPairs, List.length_flatMap]; omega
  have hk' : 4 * i + pairIdx a b < (l1 ++ l2).length := hk
  change (l1 ++ l2)[4 * i + pairIdx a b]'hk' = _
  rw [List.getElem_append_left (by omega)]
  have hidx : 4 * i + pairIdx a b = i * 4 + pairIdx a b := by omega
  rw [getElem_idx hidx]
  dsimp only [l1]
  rw [flatMap_const_len_getElem (List.range n) _ 4
    (fun _ _ => by simp [boolPairs]) i (pairIdx a b) (by simp [hi]) hpa]
  simp only [List.getElem_range, List.getElem_map, boolPairs_getElem]

lemma layer6_getElem_ne (n i : ℕ) (hi : i < n)
    (hk : 4 * n + i < (layer6 n).length) :
    (layer6 n)[4 * n + i]'hk = ⟨.or, boolPairs.map fun ab => wireT' n i ab.1 ab.2⟩ := by
  set l1 := (List.range n).flatMap fun i =>
      boolPairs.map fun ab => (⟨.not, [wireT' n i ab.1 ab.2]⟩ : Gate)
  set l2 := (List.range n).map fun i =>
      (⟨.or, boolPairs.map fun ab => wireT' n i ab.1 ab.2⟩ : Gate)
  have hlen1 : l1.length = 4 * n := by simp [l1, boolPairs, List.length_flatMap]; omega
  have hk' : 4 * n + i < (l1 ++ l2).length := hk
  change (l1 ++ l2)[4 * n + i]'hk' = _
  rw [List.getElem_append_right (by omega)]
  have hsub : 4 * n + i - l1.length = i := by omega
  rw [getElem_idx hsub]
  simp only [l2, List.getElem_map, List.getElem_range]

lemma boolList_getElem (a : Bool) :
    ([false, true] : List Bool)[boolIdx a]'(by cases a <;> decide) = a := by
  cases a <;> rfl

lemma layer7_getElem_block (n i : ℕ) (hi : i < n) (a : Bool)
    (hk : 2 * i + boolIdx a < (layer7 n).length) :
    (layer7 n)[2 * i + boolIdx a]'hk =
      ⟨.and, [wireT' n i false false, wireT' n i true true, wireNT' n i a (!a)]⟩ := by
  have hba : boolIdx a < 2 := by cases a <;> decide
  set l1 := (List.range n).flatMap fun i => [false, true].map fun a =>
      (⟨.and, [wireT' n i false false, wireT' n i true true, wireNT' n i a (!a)]⟩ : Gate)
  set l2 := (List.range n).flatMap fun i => [false, true].map fun a =>
      (⟨.and, [wireNT' n i false (!a), wireNT' n i true (!a)]⟩ : Gate)
  set l3 := (List.range n).flatMap fun i => [false, true].map fun b =>
      (⟨.and, [wireNT' n i (!b) false, wireNT' n i (!b) true]⟩ : Gate)
  have hl1 : l1.length = 2 * n := by simp [l1, List.length_flatMap]; omega
  have hk' : 2 * i + boolIdx a < ((l1 ++ l2) ++ l3).length := hk
  change ((l1 ++ l2) ++ l3)[2 * i + boolIdx a]'hk' = _
  rw [List.getElem_append_left (by simp [List.length_append, hl1]; omega)]
  rw [List.getElem_append_left (by omega)]
  have hidx : 2 * i + boolIdx a = i * 2 + boolIdx a := by omega
  rw [getElem_idx hidx]
  dsimp only [l1]
  rw [flatMap_const_len_getElem (List.range n) _ 2
    (fun _ _ => by simp) i (boolIdx a) (by simp [hi]) hba]
  simp only [List.getElem_range, List.getElem_map, boolList_getElem]

lemma layer7_getElem_leftMid (n i : ℕ) (hi : i < n) (a : Bool)
    (hk : 2 * n + 2 * i + boolIdx a < (layer7 n).length) :
    (layer7 n)[2 * n + 2 * i + boolIdx a]'hk =
      ⟨.and, [wireNT' n i false (!a), wireNT' n i true (!a)]⟩ := by
  have hba : boolIdx a < 2 := by cases a <;> decide
  set l1 := (List.range n).flatMap fun i => [false, true].map fun a =>
      (⟨.and, [wireT' n i false false, wireT' n i true true, wireNT' n i a (!a)]⟩ : Gate)
  set l2 := (List.range n).flatMap fun i => [false, true].map fun a =>
      (⟨.and, [wireNT' n i false (!a), wireNT' n i true (!a)]⟩ : Gate)
  set l3 := (List.range n).flatMap fun i => [false, true].map fun b =>
      (⟨.and, [wireNT' n i (!b) false, wireNT' n i (!b) true]⟩ : Gate)
  have hl1 : l1.length = 2 * n := by simp [l1, List.length_flatMap]; omega
  have hl2 : l2.length = 2 * n := by simp [l2, List.length_flatMap]; omega
  have hk' : 2 * n + 2 * i + boolIdx a < ((l1 ++ l2) ++ l3).length := hk
  change ((l1 ++ l2) ++ l3)[2 * n + 2 * i + boolIdx a]'hk' = _
  rw [List.getElem_append_left (by simp [List.length_append, hl1, hl2]; omega)]
  rw [List.getElem_append_right (by omega)]
  have hidx : 2 * n + 2 * i + boolIdx a - l1.length = i * 2 + boolIdx a := by omega
  rw [getElem_idx hidx]
  dsimp only [l2]
  rw [flatMap_const_len_getElem (List.range n) _ 2
    (fun _ _ => by simp) i (boolIdx a) (by simp [hi]) hba]
  simp only [List.getElem_range, List.getElem_map, boolList_getElem]

lemma layer7_getElem_rightMid (n i : ℕ) (hi : i < n) (b : Bool)
    (hk : 4 * n + 2 * i + boolIdx b < (layer7 n).length) :
    (layer7 n)[4 * n + 2 * i + boolIdx b]'hk =
      ⟨.and, [wireNT' n i (!b) false, wireNT' n i (!b) true]⟩ := by
  have hba : boolIdx b < 2 := by cases b <;> decide
  set l1 := (List.range n).flatMap fun i => [false, true].map fun a =>
      (⟨.and, [wireT' n i false false, wireT' n i true true, wireNT' n i a (!a)]⟩ : Gate)
  set l2 := (List.range n).flatMap fun i => [false, true].map fun a =>
      (⟨.and, [wireNT' n i false (!a), wireNT' n i true (!a)]⟩ : Gate)
  set l3 := (List.range n).flatMap fun i => [false, true].map fun b =>
      (⟨.and, [wireNT' n i (!b) false, wireNT' n i (!b) true]⟩ : Gate)
  have hl1 : l1.length = 2 * n := by simp [l1, List.length_flatMap]; omega
  have hl2 : l2.length = 2 * n := by simp [l2, List.length_flatMap]; omega
  have hk' : 4 * n + 2 * i + boolIdx b < ((l1 ++ l2) ++ l3).length := hk
  change ((l1 ++ l2) ++ l3)[4 * n + 2 * i + boolIdx b]'hk' = _
  rw [List.getElem_append_right (by rw [List.length_append, hl1, hl2]; omega)]
  have hidx : 4 * n + 2 * i + boolIdx b - (l1 ++ l2).length = i * 2 + boolIdx b := by
    rw [List.length_append, hl1, hl2]; omega
  rw [getElem_idx hidx]
  dsimp only [l3]
  rw [flatMap_const_len_getElem (List.range n) _ 2
    (fun _ _ => by simp) i (boolIdx b) (by simp [hi]) hba]
  simp only [List.getElem_range, List.getElem_map, boolList_getElem]

lemma prefix7_eval {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) :
    let w7 := evalWires (prefix7 n) (tableInput T)
    (∀ i < n, w7.getD (wireNE n i) false = rowNonEmpty T i) ∧
    (∀ i < n, ∀ a, w7.getD (wireBlock n i a) false = rowBlock T i a) ∧
    (∀ b0 l a, l ≤ n → w7.getD (wireLeft n b0 l a) false = leftOnly T b0 l a) ∧
    (∀ b0 r b, r ≤ n → w7.getD (wireRight n b0 r b) false = rightOnly T b0 r b) := by
  set x := tableInput T
  have hxlen : x.length = 4 * n := tableInput_length T
  set w1 := evalWires (layer1 n) x
  have hw1len : w1.length = 5 * n := by rw [evalWires_length, hxlen, layer1_len]; omega
  have hw1_in : ∀ i < 4 * n, w1.getD i false = x.getD i false :=
    fun i hi => evalWires_prefix_getD (layer1 n) x (by omega)
  have hw1_val : ∀ i < n, w1.getD (4 * n + i) false = crossRow T i := by
    intro i hi
    have h := evalWires_layer_getD (layer1 n) x
      (fun g hg j hj => by rw [hxlen]; exact layer1_inputs_lt n g hg j hj)
      (k := i) (by rw [layer1_len]; exact hi)
    rw [hxlen] at h
    rw [h]
    simp only [layer1, List.getElem_map, List.getElem_range, GateOp.eval, List.map_cons,
      List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    have h1 := tableInput_getD T ⟨i, hi⟩ true false
    have h2 := tableInput_getD T ⟨i, hi⟩ false true
    simp only [pairIdx] at h1 h2
    rw [h1, h2]
    simp [crossRow, hi]
  set w2 := evalWires (layer2 n) w1
  have hw2len : w2.length = 6 * n := by rw [evalWires_length, hw1len, layer2_len]; omega
  have hw2_pre : ∀ i < 5 * n, w2.getD i false = w1.getD i false :=
    fun i hi => evalWires_prefix_getD (layer2 n) w1 (by omega)
  have hw2_val : ∀ j < n, w2.getD (5 * n + j) false = !(prefXor T (j + 1)) := by
    intro j hj
    have h := evalWires_layer_getD (layer2 n) w1
      (fun g hg k hk => by rw [hw1len]; exact layer2_inputs_lt n g hg k hk)
      (k := j) (by rw [layer2_len]; exact hj)
    rw [hw1len] at h
    rw [h]
    simp only [layer2, List.getElem_map, List.getElem_range, GateOp.eval, List.map_map]
    have hmap' : List.map ((fun i => w1.getD i false) ∘ fun i => 4 * n + i) (List.range (j + 1)) =
        (List.range (j + 1)).map (crossRow T) := by
      apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      exact hw1_val i (by omega)
    rw [hmap', count_range_crossRow]
    cases prefXor T (j + 1) <;> rfl
  set w3 := evalWires (layer3 n) w2
  have hw3len : w3.length = 7 * n + 2 := by rw [evalWires_length, hw2len, layer3_len]; omega
  have hw3_pre : ∀ i < 6 * n, w3.getD i false = w2.getD i false :=
    fun i hi => evalWires_prefix_getD (layer3 n) w2 (by omega)
  have hw3_false : w3.getD (wireFalse n) false = false := by
    have h := evalWires_layer_getD (layer3 n) w2
      (fun g hg k hk => by rw [hw2len]; exact layer3_inputs_lt n g hg k hk)
      (k := 0) (by rw [layer3_len]; omega)
    rw [hw2len, Nat.add_zero] at h
    rw [wireFalse, h]; rfl
  have hw3_true : w3.getD (wireTrue n) false = true := by
    have h := evalWires_layer_getD (layer3 n) w2
      (fun g hg k hk => by rw [hw2len]; exact layer3_inputs_lt n g hg k hk)
      (k := 1) (by rw [layer3_len]; omega)
    rw [hw2len] at h
    rw [wireTrue, h]; rfl
  have hw3_S : ∀ k ≤ n, w3.getD (wireS n k) false = prefXor T k := by
    intro k hk
    unfold wireS
    split_ifs with hk0
    · subst hk0; exact hw3_false
    · have hlt : k - 1 < n := by omega
      have h := evalWires_layer_getD (layer3 n) w2
        (fun g hg m hm => by rw [hw2len]; exact layer3_inputs_lt n g hg m hm)
        (k := 2 + (k - 1)) (by rw [layer3_len]; omega)
      rw [hw2len] at h
      have heq : 6 * n + 2 + (k - 1) = 6 * n + (2 + (k - 1)) := by omega
      rw [heq, h]
      simp only [layer3]
      rw [List.getElem_append_right (by simp)]
      simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left,
        List.getElem_map, List.getElem_range, GateOp.eval, List.map_cons, List.map_nil,
        List.headD_cons]
      rw [hw2_val (k - 1) hlt]
      have hsucc : k - 1 + 1 = k := by omega
      rw [hsucc, Bool.not_not]
  have hw3_NS : ∀ k ≤ n, w3.getD (wireNS n k) false = !(prefXor T k) := by
    intro k hk
    unfold wireNS
    split_ifs with hk0
    · subst hk0; exact hw3_true
    · have hlt : k - 1 < n := by omega
      rw [hw3_pre _ (by omega), hw2_val (k - 1) hlt]
      have hsucc : k - 1 + 1 = k := by omega
      rw [hsucc]
  set w4 := evalWires (layer4 n) w3
  have hw4len : w4.length = 23 * n + 2 := by rw [evalWires_length, hw3len, layer4_len]; omega
  have hw4_pre : ∀ i < 7 * n + 2, w4.getD i false = w3.getD i false :=
    fun i hi => evalWires_prefix_getD (layer4 n) w3 (by omega)
  have hw4_val : ∀ i < n, ∀ a b u v, w4.getD (wireT4 n i a b u v) false =
      (decide (prefXor T i = u) && decide (prefXor T (i + 1) = v) &&
        relabT T i a b) := by
    intro i hi a b u v
    have hpa := pairIdx_lt a b
    have hpu := pairIdx_lt u v
    have hk : 16 * i + 4 * pairIdx a b + pairIdx u v < (layer4 n).length := by
      rw [layer4_len]; omega
    have h := evalWires_layer_getD (layer4 n) w3
      (fun g hg m hm => by rw [hw3len]; exact layer4_inputs_lt n g hg m hm) hk
    rw [hw3len] at h
    have heq : wireT4 n i a b u v = 7 * n + 2 + (16 * i + 4 * pairIdx a b + pairIdx u v) := by
      unfold wireT4; omega
    rw [heq, h, layer4_getElem n i hi a b u v hk]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    have h1 : w3.getD (if u then wireS n i else wireNS n i) false = decide (prefXor T i = u) := by
      cases u
      · simp only [Bool.false_eq_true, ↓reduceIte, hw3_NS i (by omega)]
        cases prefXor T i <;> rfl
      · simp only [↓reduceIte, hw3_S i (by omega)]
        cases prefXor T i <;> rfl
    have h2 : w3.getD (if v then wireS n (i + 1) else wireNS n (i + 1)) false =
        decide (prefXor T (i + 1) = v) := by
      cases v
      · simp only [Bool.false_eq_true, ↓reduceIte, hw3_NS (i + 1) (by omega)]
        cases prefXor T (i + 1) <;> rfl
      · simp only [↓reduceIte, hw3_S (i + 1) (by omega)]
        cases prefXor T (i + 1) <;> rfl
    have h3 : w3.getD (4 * i + pairIdx (xor a u) (xor b v)) false =
        T ⟨i, hi⟩ (xor a u) (xor b v) := by
      have hlt : 4 * i + pairIdx (xor a u) (xor b v) < 4 * n := by
        have := pairIdx_lt (xor a u) (xor b v); omega
      rw [hw3_pre _ (by omega), hw2_pre _ (by omega), hw1_in _ hlt]
      exact tableInput_getD T ⟨i, hi⟩ (xor a u) (xor b v)
    rw [h1, h2, h3]
    unfold relabT
    simp only [hi, ↓reduceDIte]
    cases prefXor T i <;> cases prefXor T (i + 1) <;> cases u <;> cases v <;> simp
  set w5 := evalWires (layer5 n) w4
  have hw5len : w5.length = 27 * n + 2 := by rw [evalWires_length, hw4len, layer5_len]; omega
  have hw5_pre : ∀ i < 23 * n + 2, w5.getD i false = w4.getD i false :=
    fun i hi => evalWires_prefix_getD (layer5 n) w4 (by omega)
  have hw5_val : ∀ i < n, ∀ a b, w5.getD (wireT' n i a b) false = relabT T i a b := by
    intro i hi a b
    have hpa := pairIdx_lt a b
    have hk : 4 * i + pairIdx a b < (layer5 n).length := by rw [layer5_len]; omega
    have h := evalWires_layer_getD (layer5 n) w4
      (fun g hg m hm => by rw [hw4len]; exact layer5_inputs_lt n g hg m hm) hk
    rw [hw4len] at h
    have heq : wireT' n i a b = 23 * n + 2 + (4 * i + pairIdx a b) := by unfold wireT'; omega
    rw [heq, h, layer5_getElem n i hi a b hk]
    simp only [GateOp.eval, boolPairs, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, hw4_val i hi a b]
    cases prefXor T i <;> cases prefXor T (i + 1) <;> cases relabT T i a b <;> rfl
  set w6 := evalWires (layer6 n) w5
  have hw6len : w6.length = 32 * n + 2 := by rw [evalWires_length, hw5len, layer6_len]; omega
  have hw6_pre : ∀ i < 27 * n + 2, w6.getD i false = w5.getD i false :=
    fun i hi => evalWires_prefix_getD (layer6 n) w5 (by omega)
  have hw6_not : ∀ i < n, ∀ a b, w6.getD (wireNT' n i a b) false = !(relabT T i a b) := by
    intro i hi a b
    have hpa := pairIdx_lt a b
    have hk : 4 * i + pairIdx a b < (layer6 n).length := by rw [layer6_len]; omega
    have h := evalWires_layer_getD (layer6 n) w5
      (fun g hg m hm => by rw [hw5len]; exact layer6_inputs_lt n g hg m hm) hk
    rw [hw5len] at h
    have heq : wireNT' n i a b = 27 * n + 2 + (4 * i + pairIdx a b) := by unfold wireNT'; omega
    rw [heq, h, layer6_getElem_not n i hi a b hk]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hw5_val i hi a b]
  have hw6_ne : ∀ i < n, w6.getD (wireNE n i) false = rowNonEmpty T i := by
    intro i hi
    have hk : 4 * n + i < (layer6 n).length := by rw [layer6_len]; omega
    have h := evalWires_layer_getD (layer6 n) w5
      (fun g hg m hm => by rw [hw5len]; exact layer6_inputs_lt n g hg m hm) hk
    rw [hw5len] at h
    have heq : wireNE n i = 27 * n + 2 + (4 * n + i) := by unfold wireNE; omega
    rw [heq, h, layer6_getElem_ne n i hi hk]
    simp only [GateOp.eval, boolPairs, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false, hw5_val i hi, rowNonEmpty, Bool.or_assoc]
  set w7 := evalWires (layer7 n) w6
  have hw7_eq : evalWires (prefix7 n) x = w7 := by
    unfold prefix7
    simp only [w7, w6, w5, w4, w3, w2, w1, evalWires_append]
  have hw7_pre : ∀ i < 32 * n + 2, w7.getD i false = w6.getD i false :=
    fun i hi => evalWires_prefix_getD (layer7 n) w6 (by omega)
  dsimp only
  rw [hw7_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hw7_pre _ (by unfold wireNE; omega), hw6_ne i hi]
  · intro i hi a
    have hba : boolIdx a < 2 := by cases a <;> decide
    have hk : 2 * i + boolIdx a < (layer7 n).length := by rw [layer7_len]; omega
    have h := evalWires_layer_getD (layer7 n) w6
      (fun g hg m hm => by rw [hw6len]; exact layer7_inputs_lt n g hg m hm) hk
    rw [hw6len] at h
    have heq : wireBlock n i a = 32 * n + 2 + (2 * i + boolIdx a) := by unfold wireBlock; omega
    rw [heq, h, layer7_getElem_block n i hi a hk]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [hw6_pre _ (wireT'_lt n i hi false false), hw5_val i hi false false,
      hw6_pre _ (wireT'_lt n i hi true true), hw5_val i hi true true,
      hw6_not i hi a (!a)]
    simp [rowBlock, rowStay, Bool.and_assoc]
  · intro b0 l a hl
    unfold wireLeft leftOnly
    split_ifs with hl0 hab
    · rw [hw7_pre _ (by unfold wireTrue; omega), hw6_pre _ (by unfold wireTrue; omega),
        hw5_pre _ (by unfold wireTrue; omega), hw4_pre _ (by unfold wireTrue; omega), hw3_true]
      simp [hab]
    · rw [hw7_pre _ (by unfold wireFalse; omega), hw6_pre _ (by unfold wireFalse; omega),
        hw5_pre _ (by unfold wireFalse; omega), hw4_pre _ (by unfold wireFalse; omega), hw3_false]
      simp [hab]
    · have hlt : l - 1 < n := by omega
      have hba : boolIdx a < 2 := by cases a <;> decide
      have hk : 2 * n + 2 * (l - 1) + boolIdx a < (layer7 n).length := by rw [layer7_len]; omega
      have h := evalWires_layer_getD (layer7 n) w6
        (fun g hg m hm => by rw [hw6len]; exact layer7_inputs_lt n g hg m hm) hk
      rw [hw6len] at h
      have heq : wireLeftMid n (l - 1) a = 32 * n + 2 + (2 * n + 2 * (l - 1) + boolIdx a) := by
        unfold wireLeftMid; omega
      rw [heq, h, layer7_getElem_leftMid n (l - 1) hlt a hk]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      rw [hw6_not (l - 1) hlt false (!a), hw6_not (l - 1) hlt true (!a)]
  · intro b0 r b hr
    unfold wireRight rightOnly
    split_ifs with hrn hbb
    · have hlt := wireNS_lt n n (le_refl n)
      rw [hw7_pre _ (by omega), hw6_pre _ (by omega), hw5_pre _ (by omega),
        hw4_pre _ hlt, hw3_NS n (le_refl n)]
      subst hbb; cases b <;> cases prefXor T n <;> rfl
    · have hlt := wireS_lt n n (le_refl n)
      rw [hw7_pre _ (by omega), hw6_pre _ (by omega), hw5_pre _ (by omega),
        hw4_pre _ hlt, hw3_S n (le_refl n)]
      cases b <;> cases b0 <;> cases prefXor T n <;> simp_all
    · have hlt : r < n := by omega
      have hba : boolIdx b < 2 := by cases b <;> decide
      have hk : 4 * n + 2 * r + boolIdx b < (layer7 n).length := by rw [layer7_len]; omega
      have h := evalWires_layer_getD (layer7 n) w6
        (fun g hg m hm => by rw [hw6len]; exact layer7_inputs_lt n g hg m hm) hk
      rw [hw6len] at h
      have heq : wireRightMid n r b = 32 * n + 2 + (4 * n + 2 * r + boolIdx b) := by
        unfold wireRightMid; omega
      rw [heq, h, layer7_getElem_rightMid n r hlt b hk]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      rw [hw6_not r hlt (!b) false, hw6_not r hlt (!b) true]

lemma diagGates_len (n : ℕ) (b0 : Bool) : (diagGates n b0).length = 2 * (n + 1) := by
  simp [diagGates, List.length_flatMap]; omega

lemma diagGates_aon (n : ℕ) (b0 : Bool) : ∀ g ∈ diagGates n b0, IsAON g := by
  intro g hg
  simp only [diagGates, List.mem_flatMap, List.mem_map] at hg
  rcases hg with ⟨_, _, _, _, rfl⟩; simp [IsAON]

lemma diagGates_inputs_lt (n : ℕ) (b0 : Bool) :
    ∀ g ∈ diagGates n b0, ∀ i ∈ g.inputs, i < base7 n := by
  intro g hg i hi
  simp only [diagGates, List.mem_flatMap, List.mem_map, List.mem_range] at hg
  rcases hg with ⟨a, _, l, hl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact wireLeft_lt n b0 l (by omega) a
  · exact wireRight_lt n b0 l (by omega) (!a)

lemma diagGates_fanin_le (n : ℕ) (b0 : Bool) :
    ((diagGates n b0).map (fun g => g.inputs.length)).sum ≤ 4 * (n + 1) := by
  have h := list_sum_map_le (diagGates n b0) (fun g => g.inputs.length) 2 (fun g hg => by
    simp only [diagGates, List.mem_flatMap, List.mem_map] at hg
    rcases hg with ⟨_, _, _, _, rfl⟩; simp)
  rw [diagGates_len] at h; omega

lemma splitGadget_len (n : ℕ) (b0 a : Bool) (base : ℕ) (s : ℕ × ℕ × ℕ)
    (hs : s.1 ≤ s.2.1 ∧ s.2.1 < s.2.2) :
    (splitGadget n b0 a base s).length = (s.2.2 - s.1 + 1) + 3 := by
  unfold splitGadget
  simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
    List.length_nil]
  omega

lemma splitGadget_aon (n : ℕ) (b0 a : Bool) (base : ℕ) (s : ℕ × ℕ × ℕ) :
    ∀ g ∈ splitGadget n b0 a base s, IsAON g := by
  intro g hg
  unfold splitGadget at hg
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl | rfl | rfl <;> simp [IsAON]

lemma splitGadget_readsBack (n : ℕ) (b0 a : Bool) (gs : List Gate) (out : ℕ) (s : ℕ × ℕ × ℕ)
    (hgs : ReadsBack (4 * n) ⟨gs, out⟩)
    (hbase : base7 n ≤ 4 * n + gs.length)
    (hs : s.1 ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ n) :
    ReadsBack (4 * n) ⟨gs ++ splitGadget n b0 a (4 * n + gs.length) s, out⟩ := by
  set base := 4 * n + gs.length
  set kL := s.2.1 + 1 - s.1
  set kR := s.2.2 - s.2.1
  set lGates := (List.range kL).map fun idx =>
    let l := s.1 + idx
    (⟨.and, wireLeft n b0 l a :: (List.range (s.2.1 + 1 - l)).map (fun t => wireBlock n (l + t) a)⟩ : Gate)
  set rGates := (List.range kR).map fun idx =>
    let r := s.2.1 + 1 + idx
    (⟨.and, wireRight n b0 r (!a) :: (List.range (r - (s.2.1 + 1))).map (fun t => wireBlock n (s.2.1 + 1 + t) a)⟩ : Gate)
  set hasL : Gate := ⟨.or, (List.range kL).map (fun idx => base + idx)⟩
  set hasR : Gate := ⟨.or, (List.range kR).map (fun idx => base + kL + idx)⟩
  set badS : Gate := ⟨.and, [base + kL + kR, base + kL + kR + 1]⟩
  have h1 : ReadsBack (4 * n) ⟨gs ++ (lGates ++ rGates), out⟩ := by
    apply readsBack_append_layer _ _ _ _ hgs
    intro g hg i hi
    simp only [List.mem_append, lGates, rGates, List.mem_map, List.mem_range] at hg
    rcases hg with ⟨idx, hidx, rfl⟩ | ⟨idx, hidx, rfl⟩
    · simp only [List.mem_cons, List.mem_map, List.mem_range] at hi
      rcases hi with rfl | ⟨t, ht, rfl⟩
      · exact Nat.lt_of_lt_of_le (wireLeft_lt n b0 (s.1 + idx) (by omega) a) hbase
      · exact Nat.lt_of_lt_of_le (wireBlock_lt n (s.1 + idx + t) (by omega) a) hbase
    · simp only [List.mem_cons, List.mem_map, List.mem_range] at hi
      rcases hi with rfl | ⟨t, ht, rfl⟩
      · exact Nat.lt_of_lt_of_le (wireRight_lt n b0 (s.2.1 + 1 + idx) (by omega) (!a)) hbase
      · exact Nat.lt_of_lt_of_le (wireBlock_lt n (s.2.1 + 1 + t) (by omega) a) hbase
  have hlen1 : (gs ++ (lGates ++ rGates)).length = gs.length + kL + kR := by
    simp [lGates, rGates]; omega
  have h2 : ReadsBack (4 * n) ⟨(gs ++ (lGates ++ rGates)) ++ [hasL, hasR], out⟩ := by
    apply readsBack_append_layer _ _ _ _ h1
    intro g hg i hi
    rw [hlen1]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · simp only [hasL, List.mem_map, List.mem_range] at hi
      rcases hi with ⟨idx, hidx, rfl⟩; omega
    · simp only [hasR, List.mem_map, List.mem_range] at hi
      rcases hi with ⟨idx, hidx, rfl⟩; omega
  have h3 : ReadsBack (4 * n) ⟨((gs ++ (lGates ++ rGates)) ++ [hasL, hasR]) ++ [badS], out⟩ := by
    apply readsBack_append_snoc _ _ _ _ h2
    intro i hi
    simp only [List.length_append, hlen1, List.length_cons, List.length_nil]
    simp only [badS, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  have heq : gs ++ splitGadget n b0 a base s =
      ((gs ++ (lGates ++ rGates)) ++ [hasL, hasR]) ++ [badS] := by
    unfold splitGadget
    change gs ++ (lGates ++ rGates ++ [hasL, hasR, badS]) =
      ((gs ++ (lGates ++ rGates)) ++ [hasL, hasR]) ++ [badS]
    simp [List.append_assoc]
  rw [heq]
  exact h3

lemma splitGadget_depth_le (n : ℕ) (b0 a : Bool) (d : List ℕ) (s : ℕ × ℕ × ℕ)
    (hbase : base7 n ≤ d.length)
    (hd : ∀ i < base7 n, d.getD i 0 ≤ 7)
    (hs : s.1 ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ n) :
    let gad := splitGadget n b0 a d.length s
    (evalDepths gad d).getD (d.length + gad.length - 1) 0 ≤ 10 := by
  set base := d.length
  set kL := s.2.1 + 1 - s.1
  set kR := s.2.2 - s.2.1
  set lGates := (List.range kL).map fun idx =>
    let l := s.1 + idx
    (⟨.and, wireLeft n b0 l a :: (List.range (s.2.1 + 1 - l)).map (fun t => wireBlock n (l + t) a)⟩ : Gate)
  set rGates := (List.range kR).map fun idx =>
    let r := s.2.1 + 1 + idx
    (⟨.and, wireRight n b0 r (!a) :: (List.range (r - (s.2.1 + 1))).map (fun t => wireBlock n (s.2.1 + 1 + t) a)⟩ : Gate)
  set hasL : Gate := ⟨.or, (List.range kL).map (fun idx => base + idx)⟩
  set hasR : Gate := ⟨.or, (List.range kR).map (fun idx => base + kL + idx)⟩
  set badS : Gate := ⟨.and, [base + kL + kR, base + kL + kR + 1]⟩
  have hLR_lt : ∀ g ∈ lGates ++ rGates, ∀ i ∈ g.inputs, i < base7 n := by
    intro g hg i hi
    simp only [List.mem_append, lGates, rGates, List.mem_map, List.mem_range] at hg
    rcases hg with ⟨idx, hidx, rfl⟩ | ⟨idx, hidx, rfl⟩
    · simp only [List.mem_cons, List.mem_map, List.mem_range] at hi
      rcases hi with rfl | ⟨t, ht, rfl⟩
      · exact wireLeft_lt n b0 (s.1 + idx) (by omega) a
      · exact wireBlock_lt n (s.1 + idx + t) (by omega) a
    · simp only [List.mem_cons, List.mem_map, List.mem_range] at hi
      rcases hi with rfl | ⟨t, ht, rfl⟩
      · exact wireRight_lt n b0 (s.2.1 + 1 + idx) (by omega) (!a)
      · exact wireBlock_lt n (s.2.1 + 1 + t) (by omega) a
  set d1 := evalDepths (lGates ++ rGates) d
  have hd1_len : d1.length = base + kL + kR := by
    rw [evalDepths_length, List.length_append]; simp [lGates, rGates]; omega
  have hd1_val : ∀ k < kL + kR, d1.getD (base + k) 0 ≤ 8 := by
    intro k hk
    have := evalDepths_layer_le_from (lGates ++ rGates) d (base7 n) 7 hbase hd hLR_lt k
      (by simp [lGates, rGates]; omega)
    exact this
  set d2 := evalDepths [hasL, hasR] d1
  have hd2_len : d2.length = base + kL + kR + 2 := by
    rw [evalDepths_length, hd1_len]; simp
  have hhasL_le : d2.getD (base + kL + kR) 0 ≤ 9 := by
    have h1 := evalDepths_snoc_le [] hasL d1 8 (fun i hi => by
      simp only [hasL, List.mem_map, List.mem_range] at hi
      rcases hi with ⟨idx, hidx, rfl⟩
      exact hd1_val idx (by omega))
    have h2 : d2 = evalDepths [hasR] (evalDepths [hasL] d1) := by
      simpa [d2] using evalDepths_append [hasL] [hasR] d1
    rw [h2, evalDepths_prefix_getD [hasR] _ (by rw [evalDepths_length, hd1_len]; simp)]
    simpa [evalDepths, hd1_len] using h1
  have hhasR_le : d2.getD (base + kL + kR + 1) 0 ≤ 9 := by
    have h2 : d2 = evalDepths ([hasL] ++ [hasR]) d1 := rfl
    rw [h2]
    have h1 := evalDepths_snoc_le [hasL] hasR d1 8 (fun i hi => by
      simp only [hasR, List.mem_map, List.mem_range] at hi
      rcases hi with ⟨idx, hidx, rfl⟩
      rw [evalDepths_prefix_getD [hasL] d1 (by rw [hd1_len]; omega)]
      have heq : base + kL + idx = base + (kL + idx) := by omega
      rw [heq]
      exact hd1_val (kL + idx) (by omega))
    simpa [hd1_len] using h1
  have hgad_eq : splitGadget n b0 a base s = ((lGates ++ rGates) ++ [hasL, hasR]) ++ [badS] := by
    unfold splitGadget
    change lGates ++ rGates ++ [hasL, hasR, badS] = ((lGates ++ rGates) ++ [hasL, hasR]) ++ [badS]
    simp [List.append_assoc]
  have hgad_len : (splitGadget n b0 a base s).length = kL + kR + 3 := by
    rw [hgad_eq]; simp [lGates, rGates]; omega
  dsimp only
  rw [hgad_len, hgad_eq, evalDepths_append]
  have hsub : base + (kL + kR + 3) - 1 = base + ((lGates ++ rGates) ++ [hasL, hasR]).length := by
    simp [lGates, rGates]; omega
  rw [hsub]
  have hlast := evalDepths_snoc_le ((lGates ++ rGates) ++ [hasL, hasR]) badS d 9 (fun i hi => by
    rw [evalDepths_append]
    simp only [badS, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hhasL_le
    · exact hhasR_le)
  rw [evalDepths_append] at hlast
  exact hlast

lemma splitGadget_fanin_le (n : ℕ) (b0 a : Bool) (base : ℕ) (s : ℕ × ℕ × ℕ)
    (hs : s.1 ≤ s.2.1 ∧ s.2.1 < s.2.2) :
    ((splitGadget n b0 a base s).map (fun g => g.inputs.length)).sum ≤
      3 * (s.2.2 - s.1 + 1) ^ 2 := by
  set kL := s.2.1 + 1 - s.1
  set kR := s.2.2 - s.2.1
  set L := s.2.2 - s.1 + 1
  have hL : L = kL + kR := by omega
  have hL2 : 2 ≤ L := by omega
  unfold splitGadget
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_map, List.length_range, List.length_cons, List.length_nil]
  have h1 : (((List.range (s.2.1 + 1 - s.1)).map fun idx =>
      (⟨.and, wireLeft n b0 (s.1 + idx) a :: (List.range (s.2.1 + 1 - (s.1 + idx))).map
        (fun t => wireBlock n (s.1 + idx + t) a)⟩ : Gate)).map fun g => g.inputs.length).sum ≤
      kL * (L + 1) := by
    have h := list_sum_map_le ((List.range (s.2.1 + 1 - s.1)).map fun idx =>
      (⟨.and, wireLeft n b0 (s.1 + idx) a :: (List.range (s.2.1 + 1 - (s.1 + idx))).map
        (fun t => wireBlock n (s.1 + idx + t) a)⟩ : Gate)) (fun g => g.inputs.length) (L + 1)
      (fun g hg => by
        simp only [List.mem_map, List.mem_range] at hg
        rcases hg with ⟨idx, hidx, rfl⟩
        simp; omega)
    simpa [kL] using h
  have h2 : (((List.range (s.2.2 - s.2.1)).map fun idx =>
      (⟨.and, wireRight n b0 (s.2.1 + 1 + idx) (!a) :: (List.range (s.2.1 + 1 + idx - (s.2.1 + 1))).map
        (fun t => wireBlock n (s.2.1 + 1 + t) a)⟩ : Gate)).map fun g => g.inputs.length).sum ≤
      kR * (L + 1) := by
    have h := list_sum_map_le ((List.range (s.2.2 - s.2.1)).map fun idx =>
      (⟨.and, wireRight n b0 (s.2.1 + 1 + idx) (!a) :: (List.range (s.2.1 + 1 + idx - (s.2.1 + 1))).map
        (fun t => wireBlock n (s.2.1 + 1 + t) a)⟩ : Gate)) (fun g => g.inputs.length) (L + 1)
      (fun g hg => by
        simp only [List.mem_map, List.mem_range] at hg
        rcases hg with ⟨idx, hidx, rfl⟩
        simp; omega)
    simpa [kR] using h
  have hsum : kL * (L + 1) + kR * (L + 1) = L * (L + 1) := by
    rw [← Nat.add_mul, ← hL]
  have hbound : L * (L + 1) + kL + kR + 2 ≤ 3 * L ^ 2 := by
    rw [Nat.pow_two, Nat.mul_add, Nat.mul_one]
    have : 2 * L ≤ L * L := Nat.mul_le_mul_right L hL2
    omega
  omega

lemma splitGadget_eval {n : ℕ} (T : Fin n → Bool → Bool → Bool) (b0 a : Bool)
    (w : List Bool) (s : ℕ × ℕ × ℕ)
    (hbase : base7 n ≤ w.length)
    (hLval : ∀ l ≤ n, w.getD (wireLeft n b0 l a) false = leftOnly T b0 l a)
    (hRval : ∀ r ≤ n, w.getD (wireRight n b0 r (!a)) false = rightOnly T b0 r (!a))
    (hBval : ∀ k < n, w.getD (wireBlock n k a) false = rowBlock T k a)
    (hs : s.1 ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ n) :
    let gad := splitGadget n b0 a w.length s
    (evalWires gad w).getD (w.length + gad.length - 1) false = true ↔
      ∃ l r, s.1 ≤ l ∧ l ≤ s.2.1 ∧ s.2.1 + 1 ≤ r ∧ r ≤ s.2.2 ∧
        leftOnly T b0 l a = true ∧ rightOnly T b0 r (!a) = true ∧
        ∀ k, l ≤ k → k < r → rowBlock T k a = true := by
  set base := w.length
  set kL := s.2.1 + 1 - s.1
  set kR := s.2.2 - s.2.1
  set lGates := (List.range kL).map fun idx =>
    let l := s.1 + idx
    (⟨.and, wireLeft n b0 l a :: (List.range (s.2.1 + 1 - l)).map (fun t => wireBlock n (l + t) a)⟩ : Gate)
  set rGates := (List.range kR).map fun idx =>
    let r := s.2.1 + 1 + idx
    (⟨.and, wireRight n b0 r (!a) :: (List.range (r - (s.2.1 + 1))).map (fun t => wireBlock n (s.2.1 + 1 + t) a)⟩ : Gate)
  set hasL : Gate := ⟨.or, (List.range kL).map (fun idx => base + idx)⟩
  set hasR : Gate := ⟨.or, (List.range kR).map (fun idx => base + kL + idx)⟩
  set badS : Gate := ⟨.and, [base + kL + kR, base + kL + kR + 1]⟩
  have hLR_lt : ∀ g ∈ lGates ++ rGates, ∀ i ∈ g.inputs, i < w.length := by
    intro g hg i hi
    simp only [List.mem_append, lGates, rGates, List.mem_map, List.mem_range] at hg
    rcases hg with ⟨idx, hidx, rfl⟩ | ⟨idx, hidx, rfl⟩
    · simp only [List.mem_cons, List.mem_map, List.mem_range] at hi
      rcases hi with rfl | ⟨t, ht, rfl⟩
      · exact Nat.lt_of_lt_of_le (wireLeft_lt n b0 (s.1 + idx) (by omega) a) hbase
      · exact Nat.lt_of_lt_of_le (wireBlock_lt n (s.1 + idx + t) (by omega) a) hbase
    · simp only [List.mem_cons, List.mem_map, List.mem_range] at hi
      rcases hi with rfl | ⟨t, ht, rfl⟩
      · exact Nat.lt_of_lt_of_le (wireRight_lt n b0 (s.2.1 + 1 + idx) (by omega) (!a)) hbase
      · exact Nat.lt_of_lt_of_le (wireBlock_lt n (s.2.1 + 1 + t) (by omega) a) hbase
  set w1 := evalWires (lGates ++ rGates) w
  have hw1len : w1.length = base + kL + kR := by
    rw [evalWires_length, List.length_append]; simp [lGates, rGates]; omega
  have hw1L : ∀ idx < kL, w1.getD (base + idx) false = true ↔
      leftOnly T b0 (s.1 + idx) a = true ∧
      ∀ k, s.1 + idx ≤ k → k ≤ s.2.1 → rowBlock T k a = true := by
    intro idx hidx
    have hk : idx < (lGates ++ rGates).length := by simp [lGates, rGates]; omega
    have h := evalWires_layer_getD (lGates ++ rGates) w hLR_lt hk
    rw [h, List.getElem_append_left (by simp [lGates]; exact hidx)]
    simp only [lGates, List.getElem_map, List.getElem_range, GateOp.eval, List.map_cons,
      List.all_cons, id_eq, Bool.and_eq_true, List.all_eq_true, List.mem_map, List.mem_range]
    rw [hLval (s.1 + idx) (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k hk1 hk2 => ?_⟩
      have := h2 (w.getD (wireBlock n k a) false)
        ⟨wireBlock n k a, ⟨k - (s.1 + idx), by omega, by congr 1; omega⟩, rfl⟩
      rw [hBval k (by omega)] at this
      exact this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro b ⟨j, ⟨t, ht, rfl⟩, rfl⟩
      rw [hBval (s.1 + idx + t) (by omega)]
      exact h2 (s.1 + idx + t) (by omega) (by omega)
  have hw1R : ∀ idx < kR, w1.getD (base + kL + idx) false = true ↔
      rightOnly T b0 (s.2.1 + 1 + idx) (!a) = true ∧
      ∀ k, s.2.1 + 1 ≤ k → k < s.2.1 + 1 + idx → rowBlock T k a = true := by
    intro idx hidx
    have hk : kL + idx < (lGates ++ rGates).length := by simp [lGates, rGates]; omega
    have h := evalWires_layer_getD (lGates ++ rGates) w hLR_lt hk
    have hadd : base + kL + idx = w.length + (kL + idx) := by omega
    rw [hadd, h, List.getElem_append_right (by simp [lGates])]
    have hlL : lGates.length = kL := by simp [lGates]
    simp only [hlL, Nat.add_sub_cancel_left, rGates, List.getElem_map, List.getElem_range,
      GateOp.eval, List.map_cons, List.all_cons, id_eq, Bool.and_eq_true, List.all_eq_true,
      List.mem_map, List.mem_range]
    rw [hRval (s.2.1 + 1 + idx) (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k hk1 hk2 => ?_⟩
      have := h2 (w.getD (wireBlock n k a) false)
        ⟨wireBlock n k a, ⟨k - (s.2.1 + 1), by omega, by congr 1; omega⟩, rfl⟩
      rw [hBval k (by omega)] at this
      exact this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro b ⟨j, ⟨t, ht, rfl⟩, rfl⟩
      rw [hBval (s.2.1 + 1 + t) (by omega)]
      exact h2 (s.2.1 + 1 + t) (by omega) (by omega)
  set w2 := evalWires [hasL, hasR] w1
  have hw2L : w2.getD (base + kL + kR) false = true ↔
      ∃ idx < kL, w1.getD (base + idx) false = true := by
    have h2 : w2 = evalWires [hasR] (evalWires [hasL] w1) := by
      simpa [w2] using evalWires_append [hasL] [hasR] w1
    rw [h2, evalWires_prefix_getD [hasR] _ (by rw [evalWires_length, hw1len]; simp)]
    have hsn := evalWires_snoc [] hasL w1
    simp only [List.nil_append, evalWires_nil, List.length_nil, Nat.add_zero, hw1len] at hsn
    rw [hsn]
    simp only [hasL, GateOp.eval, List.any_eq_true, List.mem_map, List.mem_range, id_eq]
    constructor
    · rintro ⟨_, ⟨_, ⟨idx, hidx, rfl⟩, rfl⟩, htrue⟩; exact ⟨idx, hidx, htrue⟩
    · rintro ⟨idx, hidx, htrue⟩; exact ⟨true, ⟨base + idx, ⟨idx, hidx, rfl⟩, htrue⟩, rfl⟩
  have hw2R : w2.getD (base + kL + kR + 1) false = true ↔
      ∃ idx < kR, w1.getD (base + kL + idx) false = true := by
    have hsn := evalWires_snoc [hasL] hasR w1
    have heq : w1.length + ([hasL] : List Gate).length = base + kL + kR + 1 := by
      rw [hw1len]; simp
    rw [heq] at hsn
    change (evalWires ([hasL] ++ [hasR]) w1).getD (base + kL + kR + 1) false = true ↔ _
    rw [hsn]
    simp only [hasR, GateOp.eval, List.any_eq_true, List.mem_map, List.mem_range, id_eq]
    constructor
    · rintro ⟨_, ⟨_, ⟨idx, hidx, rfl⟩, rfl⟩, htrue⟩
      rw [evalWires_prefix_getD [hasL] w1 (by rw [hw1len]; omega)] at htrue
      exact ⟨idx, hidx, htrue⟩
    · rintro ⟨idx, hidx, htrue⟩
      refine ⟨true, ⟨base + kL + idx, ⟨idx, hidx, rfl⟩, ?_⟩, rfl⟩
      rw [evalWires_prefix_getD [hasL] w1 (by rw [hw1len]; omega)]
      exact htrue
  have hgad_eq : splitGadget n b0 a base s = ((lGates ++ rGates) ++ [hasL, hasR]) ++ [badS] := by
    unfold splitGadget
    change lGates ++ rGates ++ [hasL, hasR, badS] = ((lGates ++ rGates) ++ [hasL, hasR]) ++ [badS]
    simp [List.append_assoc]
  have hgad_len : (splitGadget n b0 a base s).length = kL + kR + 3 := by
    rw [hgad_eq]; simp [lGates, rGates]; omega
  dsimp only
  rw [hgad_len, hgad_eq]
  have hsub : base + (kL + kR + 3) - 1 = w.length + ((lGates ++ rGates) ++ [hasL, hasR]).length := by
    simp [lGates, rGates]; omega
  rw [hsub, evalWires_snoc, evalWires_append]
  simp only [badS, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, Bool.and_eq_true]
  change (w2.getD (base + kL + kR) false = true ∧ w2.getD (base + kL + kR + 1) false = true) ↔ _
  rw [hw2L, hw2R]
  have hkL_def : kL = s.2.1 + 1 - s.1 := rfl
  have hkR_def : kR = s.2.2 - s.2.1 := rfl
  constructor
  · rintro ⟨⟨idxL, hidxL, hL⟩, ⟨idxR, hidxR, hR⟩⟩
    rw [hw1L idxL hidxL] at hL
    rw [hw1R idxR hidxR] at hR
    have hl_le : s.1 + idxL ≤ s.2.1 := by
      have h1 : idxL + 1 ≤ s.2.1 + 1 - s.1 := hidxL
      have h2 := Nat.add_le_of_le_sub (Nat.le_trans hs.1 (Nat.le_succ _)) h1
      have h3 : (s.1 + idxL).succ = idxL + 1 + s.1 := by
        rw [Nat.succ_eq_add_one, Nat.add_comm s.1 idxL, Nat.add_right_comm]
      exact Nat.le_of_succ_le_succ (h3 ▸ h2)
    have hr_le : s.2.1 + 1 + idxR ≤ s.2.2 := by
      have h1 : idxR + 1 ≤ s.2.2 - s.2.1 := hidxR
      have h2 := Nat.add_le_of_le_sub (Nat.le_of_lt hs.2.1) h1
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h2
    refine ⟨s.1 + idxL, s.2.1 + 1 + idxR, Nat.le_add_right _ _, hl_le, Nat.le_add_right _ _, hr_le,
      hL.1, hR.1, ?_⟩
    intro k hk1 hk2
    by_cases hkm : k ≤ s.2.1
    · exact hL.2 k hk1 hkm
    · exact hR.2 k (Nat.lt_of_not_ge hkm) hk2
  · rintro ⟨l, r, hl1, hl2, hr1, hr2, hL, hR, hBlk⟩
    have hidxL : l - s.1 < kL := by
      rw [hkL_def]
      exact Nat.sub_lt_sub_right hl1 (Nat.lt_succ_of_le hl2)
    have hidxR : r - (s.2.1 + 1) < kR := by
      rw [hkR_def]
      have hlt : r - (s.2.1 + 1) + 1 ≤ s.2.2 - s.2.1 := by
        have h1 : r - (s.2.1 + 1) + 1 = r - s.2.1 := by
          rw [← Nat.sub_sub]
          exact Nat.sub_add_cancel (Nat.sub_pos_of_lt hr1)
        rw [h1]
        exact Nat.sub_le_sub_right hr2 s.2.1
      exact hlt
    refine ⟨⟨l - s.1, hidxL, ?_⟩, ⟨r - (s.2.1 + 1), hidxR, ?_⟩⟩
    · rw [hw1L (l - s.1) hidxL]
      have heql : s.1 + (l - s.1) = l := Nat.add_sub_cancel' hl1
      rw [heql]
      exact ⟨hL, fun k hk1 hk2 => hBlk k hk1 (Nat.lt_of_le_of_lt hk2 hr1)⟩
    · rw [hw1R (r - (s.2.1 + 1)) hidxR]
      have heqr : s.2.1 + 1 + (r - (s.2.1 + 1)) = r := Nat.add_sub_cancel' hr1
      rw [heqr]
      exact ⟨hR, fun k hk1 hk2 => hBlk k (Nat.le_trans hl2 (Nat.le_of_succ_le hk1)) hk2⟩

lemma appendSplitGadgets_props {n : ℕ} (T : Fin n → Bool → Bool → Bool) (b0 a : Bool)
    (S : List (ℕ × ℕ × ℕ)) (gs : List Gate) (outs : List ℕ)
    (hS : ∀ s ∈ S, s.1 ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ n)
    (hgs_rb : ReadsBack (4 * n) ⟨gs, 0⟩)
    (hgs_base : base7 n ≤ 4 * n + gs.length)
    (hd : ∀ i < base7 n, (evalDepths gs (List.replicate (4 * n) 0)).getD i 0 ≤ 7)
    (houts_lt : ∀ o ∈ outs, o < 4 * n + gs.length)
    (houts_d : ∀ o ∈ outs, (evalDepths gs (List.replicate (4 * n) 0)).getD o 0 ≤ 10)
    (hw_L : ∀ l ≤ n, (evalWires gs (tableInput T)).getD (wireLeft n b0 l a) false = leftOnly T b0 l a)
    (hw_R : ∀ r ≤ n, (evalWires gs (tableInput T)).getD (wireRight n b0 r (!a)) false = rightOnly T b0 r (!a))
    (hw_B : ∀ k < n, (evalWires gs (tableInput T)).getD (wireBlock n k a) false = rowBlock T k a) :
    let res := appendSplitGadgets n b0 a S gs outs
    (∃ extra : List Gate, res.1 = gs ++ extra ∧
      (∀ g ∈ extra, IsAON g) ∧
      extra.length = (S.map (fun s => s.2.2 - s.1 + 1)).sum + 3 * S.length ∧
      (extra.map (fun g => g.inputs.length)).sum ≤ 3 * (S.map (fun s => (s.2.2 - s.1 + 1) ^ 2)).sum) ∧
    ReadsBack (4 * n) ⟨res.1, 0⟩ ∧
    res.2.length = outs.length + S.length ∧
    (∀ o ∈ res.2, o < 4 * n + res.1.length ∧
      (evalDepths res.1 (List.replicate (4 * n) 0)).getD o 0 ≤ 10) ∧
    ((∃ o ∈ res.2, (evalWires res.1 (tableInput T)).getD o false = true) ↔
      (∃ o ∈ outs, (evalWires gs (tableInput T)).getD o false = true) ∨
      ∃ s ∈ S, ∃ l r, s.1 ≤ l ∧ l ≤ s.2.1 ∧ s.2.1 + 1 ≤ r ∧ r ≤ s.2.2 ∧
        leftOnly T b0 l a = true ∧ rightOnly T b0 r (!a) = true ∧
        ∀ k, l ≤ k → k < r → rowBlock T k a = true) := by
  induction S generalizing gs outs with
  | nil =>
    simp only [appendSplitGadgets, List.foldl_nil, List.map_nil, List.sum_nil, List.length_nil,
      Nat.mul_zero, Nat.add_zero, List.not_mem_nil, false_and, exists_false, or_false]
    exact ⟨⟨[], by simp, by simp, rfl, by simp⟩, hgs_rb, trivial,
      fun o ho => ⟨houts_lt o ho, houts_d o ho⟩, trivial⟩
  | cons s tl ih =>
    have hs := hS s List.mem_cons_self
    have htl : ∀ s' ∈ tl, s'.1 ≤ s'.2.1 ∧ s'.2.1 < s'.2.2 ∧ s'.2.2 ≤ n :=
      fun s' hs' => hS s' (List.mem_cons_of_mem s hs')
    set base := 4 * n + gs.length
    set gad := splitGadget n b0 a base s
    set gs1 := gs ++ gad
    set oNew := base + gad.length - 1
    set outs1 := outs ++ [oNew]
    have hgad_len : gad.length = (s.2.2 - s.1 + 1) + 3 :=
      splitGadget_len n b0 a base s ⟨hs.1, hs.2.1⟩
    have hgs1_rb : ReadsBack (4 * n) ⟨gs1, 0⟩ :=
      splitGadget_readsBack n b0 a gs 0 s hgs_rb hgs_base hs
    have hgs1_base : base7 n ≤ 4 * n + gs1.length := by
      simp [gs1]; omega
    have hd_len : (evalDepths gs (List.replicate (4 * n) 0)).length = base := by
      rw [evalDepths_length]; simp [base]
    have hd1 : ∀ i < base7 n, (evalDepths gs1 (List.replicate (4 * n) 0)).getD i 0 ≤ 7 := by
      intro i hi
      rw [show gs1 = gs ++ gad from rfl, evalDepths_append,
        evalDepths_prefix_getD gad _ (by rw [hd_len]; omega)]
      exact hd i hi
    have houts1_lt : ∀ o ∈ outs1, o < 4 * n + gs1.length := by
      intro o ho
      simp only [outs1, List.mem_append, List.mem_singleton] at ho
      rcases ho with ho | rfl
      · have := houts_lt o ho; simp [gs1]; omega
      · simp [oNew, gs1, base]; omega
    have houts1_d : ∀ o ∈ outs1, (evalDepths gs1 (List.replicate (4 * n) 0)).getD o 0 ≤ 10 := by
      intro o ho
      simp only [outs1, List.mem_append, List.mem_singleton] at ho
      rw [show gs1 = gs ++ gad from rfl, evalDepths_append]
      rcases ho with ho | rfl
      · rw [evalDepths_prefix_getD gad _ (by rw [hd_len]; exact houts_lt o ho)]
        exact houts_d o ho
      · have hsd := splitGadget_depth_le n b0 a (evalDepths gs (List.replicate (4 * n) 0)) s
          (by rw [hd_len]; exact hgs_base) hd hs
        simpa [oNew, gad, base, hd_len] using hsd
    have hw_len : (evalWires gs (tableInput T)).length = base := by
      rw [evalWires_length, tableInput_length]
    have hw1_pre : ∀ i < base, (evalWires gs1 (tableInput T)).getD i false =
        (evalWires gs (tableInput T)).getD i false := by
      intro i hi
      rw [show gs1 = gs ++ gad from rfl, evalWires_append]
      exact evalWires_prefix_getD gad _ (by rw [hw_len]; exact hi)
    have hw1_L : ∀ l ≤ n, (evalWires gs1 (tableInput T)).getD (wireLeft n b0 l a) false =
        leftOnly T b0 l a := fun l hl => by
      rw [hw1_pre _ (Nat.lt_of_lt_of_le (wireLeft_lt n b0 l hl a) hgs_base)]
      exact hw_L l hl
    have hw1_R : ∀ r ≤ n, (evalWires gs1 (tableInput T)).getD (wireRight n b0 r (!a)) false =
        rightOnly T b0 r (!a) := fun r hr => by
      rw [hw1_pre _ (Nat.lt_of_lt_of_le (wireRight_lt n b0 r hr (!a)) hgs_base)]
      exact hw_R r hr
    have hw1_B : ∀ k < n, (evalWires gs1 (tableInput T)).getD (wireBlock n k a) false =
        rowBlock T k a := fun k hk => by
      rw [hw1_pre _ (Nat.lt_of_lt_of_le (wireBlock_lt n k hk a) hgs_base)]
      exact hw_B k hk
    have hrec := ih gs1 outs1 htl hgs1_rb hgs1_base hd1 houts1_lt houts1_d hw1_L hw1_R hw1_B
    rcases hrec with ⟨⟨extra2, hres1, haon2, hlen2, hfan2⟩, hrb, hlenO, houtProp, heval⟩
    have hres_eq : appendSplitGadgets n b0 a (s :: tl) gs outs =
        appendSplitGadgets n b0 a tl gs1 outs1 := rfl
    dsimp only
    rw [hres_eq]
    refine ⟨?_, hrb, ?_, houtProp, ?_⟩
    · refine ⟨gad ++ extra2, by rw [hres1, List.append_assoc], ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact splitGadget_aon n b0 a base s g hg
        · exact haon2 g hg
      · simp only [List.length_append, hgad_len, hlen2, List.map_cons, List.sum_cons,
          List.length_cons]
        omega
      · simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
        have hf1 : (gad.map (fun g => g.inputs.length)).sum ≤ 3 * (s.2.2 - s.1 + 1) ^ 2 :=
          splitGadget_fanin_le n b0 a base s ⟨hs.1, hs.2.1⟩
        omega
    · rw [hlenO]; simp [outs1]; omega
    · rw [heval]
      have hoNew_eval : (evalWires gs1 (tableInput T)).getD oNew false = true ↔
          ∃ l r, s.1 ≤ l ∧ l ≤ s.2.1 ∧ s.2.1 + 1 ≤ r ∧ r ≤ s.2.2 ∧
            leftOnly T b0 l a = true ∧ rightOnly T b0 r (!a) = true ∧
            ∀ k, l ≤ k → k < r → rowBlock T k a = true := by
        rw [show gs1 = gs ++ gad from rfl, evalWires_append]
        have := splitGadget_eval T b0 a (evalWires gs (tableInput T)) s
          (by rw [hw_len]; exact hgs_base) hw_L hw_R hw_B hs
        simpa [oNew, gad, base, hw_len] using this
      have houts1_iff : (∃ o ∈ outs1, (evalWires gs1 (tableInput T)).getD o false = true) ↔
          (∃ o ∈ outs, (evalWires gs (tableInput T)).getD o false = true) ∨
          (evalWires gs1 (tableInput T)).getD oNew false = true := by
        simp only [outs1, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨o, ho | rfl, hval⟩
          · left; exact ⟨o, ho, by rw [← hw1_pre o (houts_lt o ho)]; exact hval⟩
          · right; exact hval
        · rintro (⟨o, ho, hval⟩ | hval)
          · exact ⟨o, Or.inl ho, by rw [hw1_pre o (houts_lt o ho)]; exact hval⟩
          · exact ⟨oNew, Or.inr rfl, hval⟩
      rw [houts1_iff, hoNew_eval]
      simp only [List.mem_cons]
      constructor
      · rintro ((h1 | h2) | ⟨s', hs', h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨s, Or.inl rfl, h2⟩
        · exact Or.inr ⟨s', Or.inr hs', h3⟩
      · rintro (h1 | ⟨s', rfl | hs', h2⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨s', hs', h2⟩

lemma buildForB0_props {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (b0 : Bool) (gs : List Gate)
    (hgs_rb : ReadsBack (4 * n) ⟨gs, 0⟩)
    (hgs_base : base7 n ≤ 4 * n + gs.length)
    (hd : ∀ i < base7 n, (evalDepths gs (List.replicate (4 * n) 0)).getD i 0 ≤ 7)
    (hw_NE : ∀ i < n, (evalWires gs (tableInput T)).getD (wireNE n i) false = rowNonEmpty T i)
    (hw_B : ∀ k < n, ∀ a, (evalWires gs (tableInput T)).getD (wireBlock n k a) false = rowBlock T k a)
    (hw_L : ∀ l a, l ≤ n → (evalWires gs (tableInput T)).getD (wireLeft n b0 l a) false = leftOnly T b0 l a)
    (hw_R : ∀ r b, r ≤ n → (evalWires gs (tableInput T)).getD (wireRight n b0 r b) false = rightOnly T b0 r b) :
    let res := buildForB0 n b0 gs
    (∃ extra : List Gate, res.1 = gs ++ extra ∧
      (∀ g ∈ extra, IsAON g) ∧
      extra.length ≤ 2 * (n + 1) + 4 * n * (Nat.log2 n + 1) + 6 * n + 3 ∧
      (extra.map (fun g => g.inputs.length)).sum ≤ 24 * n ^ 2 + 9 * n + 8) ∧
    ReadsBack (4 * n) ⟨res.1, 0⟩ ∧
    res.2 < 4 * n + res.1.length ∧
    (evalDepths res.1 (List.replicate (4 * n) 0)).getD res.2 0 ≤ 13 ∧
    ((evalWires res.1 (tableInput T)).getD res.2 false = true ↔
      (∀ i < n, rowNonEmpty T i = true) ∧
      ∀ a : Bool, ∀ l r : ℕ, l ≤ r → r ≤ n →
        ¬ (leftOnly T b0 l a = true ∧ rightOnly T b0 r (!a) = true ∧
           ∀ k, l ≤ k → k < r → rowBlock T k a = true)) := by
  set baseDiag := 4 * n + gs.length
  set dg := diagGates n b0
  set diagOuts := (List.range dg.length).map (fun i => baseDiag + i)
  set gs1 := gs ++ dg
  set S := splits (n + 1) 0 n
  have hS_b : ∀ s ∈ S, s.1 ≤ s.2.1 ∧ s.2.1 < s.2.2 ∧ s.2.2 ≤ n := fun s hs => by
    have := splits_bounds (n + 1) 0 n s hs; omega
  have hgs1_rb : ReadsBack (4 * n) ⟨gs1, 0⟩ :=
    readsBack_append_layer (4 * n) gs dg 0 hgs_rb
      (fun g hg i hi => Nat.lt_of_lt_of_le (diagGates_inputs_lt n b0 g hg i hi) hgs_base)
  have hgs1_base : base7 n ≤ 4 * n + gs1.length := by simp [gs1]; omega
  have hd_len : (evalDepths gs (List.replicate (4 * n) 0)).length = baseDiag := by
    rw [evalDepths_length]; simp [baseDiag]
  have hd1_base : ∀ i < base7 n, (evalDepths gs1 (List.replicate (4 * n) 0)).getD i 0 ≤ 7 := by
    intro i hi
    rw [show gs1 = gs ++ dg from rfl, evalDepths_append,
      evalDepths_prefix_getD dg _ (by rw [hd_len]; omega)]
    exact hd i hi
  have hdiag_lt : ∀ o ∈ diagOuts, o < 4 * n + gs1.length := by
    intro o ho
    simp only [diagOuts, List.mem_map, List.mem_range] at ho
    rcases ho with ⟨i, hi, rfl⟩; simp [gs1, baseDiag]; omega
  have hdiag_d : ∀ o ∈ diagOuts, (evalDepths gs1 (List.replicate (4 * n) 0)).getD o 0 ≤ 10 := by
    intro o ho
    simp only [diagOuts, List.mem_map, List.mem_range] at ho
    rcases ho with ⟨i, hi, rfl⟩
    rw [show gs1 = gs ++ dg from rfl, evalDepths_append]
    have := evalDepths_layer_le_from dg (evalDepths gs (List.replicate (4 * n) 0)) (base7 n) 7
      (by rw [hd_len]; exact hgs_base) hd (diagGates_inputs_lt n b0) i hi
    rw [hd_len] at this; omega
  have hw_len : (evalWires gs (tableInput T)).length = baseDiag := by
    rw [evalWires_length, tableInput_length]
  have hw1_pre : ∀ i < baseDiag, (evalWires gs1 (tableInput T)).getD i false =
      (evalWires gs (tableInput T)).getD i false := fun i hi => by
    rw [show gs1 = gs ++ dg from rfl, evalWires_append]
    exact evalWires_prefix_getD dg _ (by rw [hw_len]; exact hi)
  have hdiag_eval : (∃ o ∈ diagOuts, (evalWires gs1 (tableInput T)).getD o false = true) ↔
      ∃ a : Bool, ∃ l ≤ n, leftOnly T b0 l a = true ∧ rightOnly T b0 l (!a) = true := by
    have hdg_lt : ∀ g ∈ dg, ∀ i ∈ g.inputs, i < (evalWires gs (tableInput T)).length :=
      fun g hg i hi => by
        rw [hw_len]
        exact Nat.lt_of_lt_of_le (diagGates_inputs_lt n b0 g hg i hi) hgs_base
    constructor
    · rintro ⟨o, ho, hval⟩
      simp only [diagOuts, List.mem_map, List.mem_range] at ho
      rcases ho with ⟨k, hk, rfl⟩
      rw [show gs1 = gs ++ dg from rfl, evalWires_append] at hval
      have he := evalWires_layer_getD dg (evalWires gs (tableInput T)) hdg_lt hk
      rw [hw_len] at he
      rw [he] at hval
      have hlen_dg : dg.length = 2 * (n + 1) := diagGates_len n b0
      by_cases h1 : k < n + 1
      · have hgate : dg[k]'hk = ⟨.and, [wireLeft n b0 k false, wireRight n b0 k true]⟩ := by
          unfold dg diagGates
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [List.getElem_append_left (by simp; omega)]
          simp
        rw [hgate] at hval
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true] at hval
        rw [hw_L k false (by omega), hw_R k true (by omega)] at hval
        exact ⟨false, k, by omega, hval⟩
      · have hgate : dg[k]'hk = ⟨.and, [wireLeft n b0 (k - (n + 1)) true, wireRight n b0 (k - (n + 1)) false]⟩ := by
          unfold dg diagGates
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [List.getElem_append_right (by simp; omega)]
          simp
        rw [hgate] at hval
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true] at hval
        rw [hw_L (k - (n + 1)) true (by omega), hw_R (k - (n + 1)) false (by omega)] at hval
        exact ⟨true, k - (n + 1), by omega, hval⟩
    · rintro ⟨a, l, hl, hL, hR⟩
      set k := boolIdx a * (n + 1) + l
      have hk : k < dg.length := by rw [diagGates_len]; cases a <;> simp [boolIdx, k] <;> omega
      refine ⟨baseDiag + k, by simp only [diagOuts, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩, ?_⟩
      rw [show gs1 = gs ++ dg from rfl, evalWires_append]
      have he := evalWires_layer_getD dg (evalWires gs (tableInput T)) hdg_lt hk
      rw [hw_len] at he
      rw [he]
      cases a
      · have hgate : dg[k]'hk = ⟨.and, [wireLeft n b0 l false, wireRight n b0 l true]⟩ := by
          unfold dg diagGates
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          have hk0 : k = l := by simp [k, boolIdx]
          rw [getElem_idx hk0]
          rw [List.getElem_append_left (by simp; omega)]
          simp
        rw [hgate]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true]
        rw [hw_L l false hl, hw_R l true hl]
        exact ⟨hL, hR⟩
      · have hgate : dg[k]'hk = ⟨.and, [wireLeft n b0 l true, wireRight n b0 l false]⟩ := by
          unfold dg diagGates
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
          have hk1 : k = n + 1 + l := by simp [k, boolIdx]
          rw [getElem_idx hk1]
          rw [List.getElem_append_right (by simp)]
          simp
        rw [hgate]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Bool.and_eq_true]
        rw [hw_L l true hl, hw_R l false hl]
        exact ⟨hL, hR⟩
  set gs2 := (appendSplitGadgets n b0 false S gs1 diagOuts).1
  set outs2 := (appendSplitGadgets n b0 false S gs1 diagOuts).2
  have hp2 := appendSplitGadgets_props T b0 false S gs1 diagOuts hS_b hgs1_rb hgs1_base hd1_base
    hdiag_lt hdiag_d
    (fun l hl => by rw [hw1_pre _ (Nat.lt_of_lt_of_le (wireLeft_lt n b0 l hl false) hgs_base)]; exact hw_L l false hl)
    (fun r hr => by simp only [Bool.not_false]; rw [hw1_pre _ (Nat.lt_of_lt_of_le (wireRight_lt n b0 r hr true) hgs_base)]; exact hw_R r true hr)
    (fun k hk => by rw [hw1_pre _ (Nat.lt_of_lt_of_le (wireBlock_lt n k hk false) hgs_base)]; exact hw_B k hk false)
  rcases hp2 with ⟨⟨ex2, hgs2_eq, haon2, hlen2, hfan2⟩, hgs2_rb, houts2_len, houts2_prop, heval2⟩
  change gs2 = gs1 ++ ex2 at hgs2_eq
  change outs2.length = diagOuts.length + S.length at houts2_len
  have hgs2_base : base7 n ≤ 4 * n + gs2.length := by rw [hgs2_eq]; simp [gs1]; omega
  have hd1_len : (evalDepths gs1 (List.replicate (4 * n) 0)).length = 4 * n + gs1.length := by
    rw [evalDepths_length]; simp
  have hd2_base : ∀ i < base7 n, (evalDepths gs2 (List.replicate (4 * n) 0)).getD i 0 ≤ 7 := by
    intro i hi
    rw [hgs2_eq, evalDepths_append, evalDepths_prefix_getD ex2 _ (by rw [hd1_len]; omega)]
    exact hd1_base i hi
  have hw1_len : (evalWires gs1 (tableInput T)).length = 4 * n + gs1.length := by
    rw [evalWires_length, tableInput_length]
  have hw2_pre : ∀ i < base7 n, (evalWires gs2 (tableInput T)).getD i false =
      (evalWires gs (tableInput T)).getD i false := fun i hi => by
    rw [hgs2_eq, evalWires_append, evalWires_prefix_getD ex2 _ (by rw [hw1_len]; omega)]
    exact hw1_pre i (by omega)
  set gs3 := (appendSplitGadgets n b0 true S gs2 outs2).1
  set outs3 := (appendSplitGadgets n b0 true S gs2 outs2).2
  have hp3 := appendSplitGadgets_props T b0 true S gs2 outs2 hS_b hgs2_rb hgs2_base hd2_base
    (fun o ho => (houts2_prop o ho).1) (fun o ho => (houts2_prop o ho).2)
    (fun l hl => by rw [hw2_pre _ (wireLeft_lt n b0 l hl true)]; exact hw_L l true hl)
    (fun r hr => by simp only [Bool.not_true]; rw [hw2_pre _ (wireRight_lt n b0 r hr false)]; exact hw_R r false hr)
    (fun k hk => by rw [hw2_pre _ (wireBlock_lt n k hk true)]; exact hw_B k hk true)
  rcases hp3 with ⟨⟨ex3, hgs3_eq, haon3, hlen3, hfan3⟩, hgs3_rb, houts3_len, houts3_prop, heval3⟩
  change gs3 = gs2 ++ ex3 at hgs3_eq
  change outs3.length = outs2.length + S.length at houts3_len
  set wAnyBad := 4 * n + gs3.length
  set gAnyBad : Gate := ⟨.or, outs3⟩
  set wNoBad := wAnyBad + 1
  set gNoBad : Gate := ⟨.not, [wAnyBad]⟩
  set wOk := wAnyBad + 2
  set gOk : Gate := ⟨.and, wNoBad :: (List.range n).map (fun i => wireNE n i)⟩
  have hgs3_base : base7 n ≤ 4 * n + gs3.length := by rw [hgs3_eq]; simp; omega
  have hS_len : S.length ≤ n := by simpa [S] using splits_length_le (n + 1) 0 n
  have hS_span : (S.map (fun s => s.2.2 - s.1 + 1)).sum ≤ 2 * n * (Nat.log2 n + 1) := by
    simpa [S] using splits_span_sum_le (n + 1) 0 n
  have hS_sq : (S.map (fun s => (s.2.2 - s.1 + 1) ^ 2)).sum ≤ 4 * n ^ 2 := by
    simpa [S] using splits_sq_sum_le (n + 1) 0 n
  have hdg_len : dg.length = 2 * (n + 1) := diagGates_len n b0
  have houts3_len_le : outs3.length ≤ 4 * n + 2 := by
    rw [houts3_len, houts2_len]
    simp only [diagOuts, List.length_map, List.length_range]
    omega
  have hrb1 : ReadsBack (4 * n) ⟨gs3 ++ [gAnyBad], 0⟩ :=
    readsBack_append_snoc (4 * n) gs3 gAnyBad 0 hgs3_rb (fun o ho => (houts3_prop o ho).1)
  have hrb2 : ReadsBack (4 * n) ⟨(gs3 ++ [gAnyBad]) ++ [gNoBad], 0⟩ :=
    readsBack_append_snoc (4 * n) (gs3 ++ [gAnyBad]) gNoBad 0 hrb1 (fun i hi => by
      simp [gNoBad] at hi; subst hi; simp [wAnyBad])
  have hrb3 : ReadsBack (4 * n) ⟨((gs3 ++ [gAnyBad]) ++ [gNoBad]) ++ [gOk], 0⟩ :=
    readsBack_append_snoc (4 * n) ((gs3 ++ [gAnyBad]) ++ [gNoBad]) gOk 0 hrb2 (fun i hi => by
      simp only [gOk, List.mem_cons, List.mem_map, List.mem_range] at hi
      simp only [List.length_append, List.length_singleton]
      rcases hi with rfl | ⟨j, hj, rfl⟩
      · omega
      · exact Nat.lt_of_lt_of_le (wireNE_lt n j hj) (by omega))
  have hfinal_eq : gs3 ++ [gAnyBad, gNoBad, gOk] =
      ((gs3 ++ [gAnyBad]) ++ [gNoBad]) ++ [gOk] := by simp [List.append_assoc]
  have hd3_len : (evalDepths gs3 (List.replicate (4 * n) 0)).length = wAnyBad := by
    rw [evalDepths_length]; simp [wAnyBad]
  have hd3_base : ∀ i < base7 n, (evalDepths gs3 (List.replicate (4 * n) 0)).getD i 0 ≤ 7 := by
    intro i hi
    rw [hgs3_eq, evalDepths_append, evalDepths_prefix_getD ex3 _ (by rw [evalDepths_length]; simp; omega)]
    exact hd2_base i hi
  have hd_any : (evalDepths (gs3 ++ [gAnyBad]) (List.replicate (4 * n) 0)).getD wAnyBad 0 ≤ 11 := by
    have h := evalDepths_snoc_le gs3 gAnyBad (List.replicate (4 * n) 0) 10
      (fun o ho => (houts3_prop o ho).2)
    rw [List.length_replicate] at h
    exact h
  have hd_no : (evalDepths ((gs3 ++ [gAnyBad]) ++ [gNoBad]) (List.replicate (4 * n) 0)).getD wNoBad 0 ≤ 12 := by
    have h := evalDepths_snoc_le (gs3 ++ [gAnyBad]) gNoBad (List.replicate (4 * n) 0) 11 (fun i hi => by
      simp [gNoBad] at hi; subst hi; exact hd_any)
    rw [List.length_replicate, List.length_append, List.length_singleton] at h
    have hidx : 4 * n + (gs3.length + 1) = wNoBad := by omega
    rw [hidx] at h
    exact h
  have hd_ok : (evalDepths (gs3 ++ [gAnyBad, gNoBad, gOk]) (List.replicate (4 * n) 0)).getD wOk 0 ≤ 13 := by
    rw [hfinal_eq]
    have h := evalDepths_snoc_le ((gs3 ++ [gAnyBad]) ++ [gNoBad]) gOk (List.replicate (4 * n) 0) 12
      (fun i hi => by
        simp only [gOk, List.mem_cons, List.mem_map, List.mem_range] at hi
        rcases hi with rfl | ⟨j, hj, rfl⟩
        · exact hd_no
        · rw [evalDepths_append, evalDepths_prefix_getD [gNoBad] _
              (by rw [evalDepths_length]; simp; have := wireNE_lt n j hj; omega),
            evalDepths_append, evalDepths_prefix_getD [gAnyBad] _
              (by rw [hd3_len]; exact Nat.lt_of_lt_of_le (wireNE_lt n j hj) hgs3_base)]
          exact Nat.le_trans (hd3_base _ (wireNE_lt n j hj)) (by omega))
    rw [List.length_replicate, List.length_append, List.length_append,
      List.length_singleton, List.length_singleton] at h
    have hidx : 4 * n + (gs3.length + 1 + 1) = wOk := by omega
    rw [hidx] at h
    exact h
  change (∃ extra : List Gate, gs3 ++ [gAnyBad, gNoBad, gOk] = gs ++ extra ∧
      (∀ g ∈ extra, IsAON g) ∧
      extra.length ≤ 2 * (n + 1) + 4 * n * (Nat.log2 n + 1) + 6 * n + 3 ∧
      (extra.map (fun g => g.inputs.length)).sum ≤ 24 * n ^ 2 + 9 * n + 8) ∧
    ReadsBack (4 * n) ⟨gs3 ++ [gAnyBad, gNoBad, gOk], 0⟩ ∧
    wOk < 4 * n + (gs3 ++ [gAnyBad, gNoBad, gOk]).length ∧
    (evalDepths (gs3 ++ [gAnyBad, gNoBad, gOk]) (List.replicate (4 * n) 0)).getD wOk 0 ≤ 13 ∧
    ((evalWires (gs3 ++ [gAnyBad, gNoBad, gOk]) (tableInput T)).getD wOk false = true ↔ _)
  refine ⟨?_, by rw [hfinal_eq]; exact hrb3, by simp only [List.length_append, List.length_cons, List.length_nil, wOk, wAnyBad]; omega, hd_ok, ?_⟩
  · refine ⟨dg ++ ex2 ++ ex3 ++ [gAnyBad, gNoBad, gOk], ?_, ?_, ?_, ?_⟩
    · rw [hgs3_eq, hgs2_eq]; simp [gs1, List.append_assoc]
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with ((hg | hg) | hg) | rfl | rfl | rfl
      · exact diagGates_aon n b0 g hg
      · exact haon2 g hg
      · exact haon3 g hg
      · simp [IsAON, gAnyBad]
      · simp [IsAON, gNoBad]
      · simp [IsAON, gOk]
    · simp only [List.length_append, hlen2, hlen3, List.length_cons, List.length_nil]
      have h4n : 2 * (2 * n * (Nat.log2 n + 1)) = 4 * n * (Nat.log2 n + 1) := by
        rw [← Nat.mul_assoc, ← Nat.mul_assoc]
      omega
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      have hfd : (dg.map (fun g => g.inputs.length)).sum ≤ 4 * (n + 1) := diagGates_fanin_le n b0
      have hfg1 : gAnyBad.inputs.length ≤ 4 * n + 2 := houts3_len_le
      have hfg2 : gNoBad.inputs.length = 1 := rfl
      have hfg3 : gOk.inputs.length = n + 1 := by simp [gOk]
      omega
  · rw [hfinal_eq]
    have hw3_len : (evalWires gs3 (tableInput T)).length = wAnyBad := by
      rw [evalWires_length, tableInput_length]
    have hw3_pre : ∀ i < base7 n, (evalWires gs3 (tableInput T)).getD i false =
        (evalWires gs (tableInput T)).getD i false := fun i hi => by
      rw [hgs3_eq, evalWires_append,
        evalWires_prefix_getD ex3 _ (by rw [evalWires_length, tableInput_length]; omega)]
      exact hw2_pre i hi
    have hok_sn := evalWires_snoc ((gs3 ++ [gAnyBad]) ++ [gNoBad]) gOk (tableInput T)
    have hok_idx : (tableInput T).length + ((gs3 ++ [gAnyBad]) ++ [gNoBad]).length = wOk := by
      rw [tableInput_length]; simp [wOk, wAnyBad]; omega
    rw [hok_idx] at hok_sn
    rw [hok_sn]
    simp only [gOk, GateOp.eval, List.map_cons, List.all_cons, id_eq, Bool.and_eq_true]
    have hno_val : (evalWires ((gs3 ++ [gAnyBad]) ++ [gNoBad]) (tableInput T)).getD wNoBad false =
        !((evalWires (gs3 ++ [gAnyBad]) (tableInput T)).getD wAnyBad false) := by
      have hsn := evalWires_snoc (gs3 ++ [gAnyBad]) gNoBad (tableInput T)
      have hidx : (tableInput T).length + (gs3 ++ [gAnyBad]).length = wNoBad := by
        rw [tableInput_length]; simp [wNoBad, wAnyBad]; omega
      rw [hidx] at hsn
      rw [hsn]; rfl
    have hany_val : (evalWires (gs3 ++ [gAnyBad]) (tableInput T)).getD wAnyBad false = true ↔
        ∃ o ∈ outs3, (evalWires gs3 (tableInput T)).getD o false = true := by
      have hsn := evalWires_snoc gs3 gAnyBad (tableInput T)
      have hidx : (tableInput T).length + gs3.length = wAnyBad := by
        rw [tableInput_length]
      rw [hidx] at hsn
      rw [hsn]
      simp only [gAnyBad, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      constructor
      · rintro ⟨_, ⟨o, ho, rfl⟩, htrue⟩; exact ⟨o, ho, htrue⟩
      · rintro ⟨o, ho, htrue⟩; exact ⟨true, ⟨o, ho, htrue⟩, rfl⟩
    have hne_val : (List.map (fun i =>
        (evalWires ((gs3 ++ [gAnyBad]) ++ [gNoBad]) (tableInput T)).getD i false)
        ((List.range n).map (fun i => wireNE n i))).all id = true ↔
        ∀ i < n, rowNonEmpty T i = true := by
      simp only [List.all_eq_true, List.mem_map, List.mem_range, id_eq]
      constructor
      · intro h i hi
        have hv := h _ ⟨wireNE n i, ⟨i, hi, rfl⟩, rfl⟩
        rw [evalWires_append, evalWires_prefix_getD [gNoBad] _
            (by rw [evalWires_length, tableInput_length]; simp; have := wireNE_lt n i hi; omega),
          evalWires_append, evalWires_prefix_getD [gAnyBad] _
            (by rw [hw3_len]; exact Nat.lt_of_lt_of_le (wireNE_lt n i hi) hgs3_base),
          hw3_pre _ (wireNE_lt n i hi), hw_NE i hi] at hv
        exact hv
      · rintro h b ⟨j, ⟨i, hi, rfl⟩, rfl⟩
        rw [evalWires_append, evalWires_prefix_getD [gNoBad] _
            (by rw [evalWires_length, tableInput_length]; simp; have := wireNE_lt n i hi; omega),
          evalWires_append, evalWires_prefix_getD [gAnyBad] _
            (by rw [hw3_len]; exact Nat.lt_of_lt_of_le (wireNE_lt n i hi) hgs3_base),
          hw3_pre _ (wireNE_lt n i hi), hw_NE i hi]
        exact h i hi
    rw [hno_val, Bool.not_eq_true', hne_val]
    have hany_iff : (evalWires (gs3 ++ [gAnyBad]) (tableInput T)).getD wAnyBad false = true ↔
        ∃ a : Bool, ∃ l r : ℕ, l ≤ r ∧ r ≤ n ∧
          leftOnly T b0 l a = true ∧ rightOnly T b0 r (!a) = true ∧
          ∀ k, l ≤ k → k < r → rowBlock T k a = true := by
      rw [hany_val, heval3, heval2, hdiag_eval]
      constructor
      · rintro ((⟨a, l, hl, hL, hR⟩ | ⟨s, hs, l, r, hl1, hl2, hr1, hr2, hL, hR, hB⟩) |
            ⟨s, hs, l, r, hl1, hl2, hr1, hr2, hL, hR, hB⟩)
        · exact ⟨a, l, l, le_refl l, hl, hL, hR, fun k h1 h2 => by omega⟩
        · have hb := hS_b s hs
          exact ⟨false, l, r, by omega, by omega, hL, hR, hB⟩
        · have hb := hS_b s hs
          exact ⟨true, l, r, by omega, by omega, hL, hR, hB⟩
      · rintro ⟨a, l, r, hlr, hrn, hL, hR, hB⟩
        by_cases heq : l = r
        · subst heq
          exact Or.inl (Or.inl ⟨a, l, hrn, hL, hR⟩)
        · rcases splits_cover (n + 1) 0 n l r (by omega) (Nat.zero_le l) (by omega) hrn with
            ⟨s, hs, hl1, hl2, hr1, hr2⟩
          cases a
          · exact Or.inl (Or.inr ⟨s, hs, l, r, hl1, hl2, hr1, hr2, hL, hR, hB⟩)
          · exact Or.inr ⟨s, hs, l, r, hl1, hl2, hr1, hr2, hL, hR, hB⟩
    have hfalse_iff : (evalWires (gs3 ++ [gAnyBad]) (tableInput T)).getD wAnyBad false = false ↔
        ∀ a : Bool, ∀ l r : ℕ, l ≤ r → r ≤ n →
          ¬ (leftOnly T b0 l a = true ∧ rightOnly T b0 r (!a) = true ∧
             ∀ k, l ≤ k → k < r → rowBlock T k a = true) := by
      rw [← Bool.not_eq_true, hany_iff]
      push Not
      rfl
    rw [hfalse_iff, and_comm]

end PEqualNP.Outside.L_clb_071

theorem PEqualNP.Outside.L_clb_071 : (∀ (n : ℕ) (hn : 0 < n),
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (4 * n) C ∧
    C.output < 4 * n + C.size ∧ 2 * n ≤ C.size ∧
    (∀ i < n, (gate i).op = .and ∧ (gate i).inputs = [4 * i + 1, 4 * i + 2]) ∧
    (∀ j < n, (gate (n + j)).op = .mod 2 ∧
      (gate (n + j)).inputs = (List.range (j + 1)).map (fun i => 4 * n + i)) ∧
    (∀ k < C.size, 2 * n ≤ k →
      (gate k).op = .and ∨ (gate k).op = .or ∨ (gate k).op = .not) ∧
    C.depth (4 * n) ≤ 24 ∧ C.size ≤ 256 * (n + 2) * (Nat.log2 (n + 2) + 1) ∧
    (C.gates.map (fun g => g.inputs.length)).sum ≤ 512 * (n + 2) ^ 2 ∧
    ∀ T : Fin n → Bool → Bool → Bool,
      let x := (List.ofFn (fun i : Fin n =>
        [T i false false, T i true false, T i false true, T i true true])).flatten
      C.eval x = true ↔ ∃ w : Fin n → Bool, ∀ i : Fin n,
        T i (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true) := by
  intro n hn
  open PEqualNP.Outside.L_clb_071 in
  refine ⟨buildCircuit n, ?_⟩
  set gs0 := prefix7 n
  set r1 := buildForB0 n false gs0
  set gs1 := r1.1
  set wOk0 := r1.2
  set r2 := buildForB0 n true gs1
  set gs2 := r2.1
  set wOk1 := r2.2
  set gOut : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [wOk0, wOk1]⟩
  set C := buildCircuit n
  have hC_gates : C.gates = gs2 ++ [gOut] := rfl
  have hC_out : C.output = 4 * n + gs2.length := rfl
  have h0_rb := prefix7_readsBack n 0
  have h0_base : base7 n ≤ 4 * n + gs0.length := by rw [base7_eq]
  have h0_d := prefix7_depth_le n
  let T0 : Fin n → Bool → Bool → Bool := fun _ _ _ => false
  have hp0 := prefix7_eval hn T0
  have h1 := buildForB0_props hn T0 false gs0 h0_rb h0_base h0_d hp0.1 hp0.2.1
    (fun l a hl => hp0.2.2.1 false l a hl) (fun r b hr => hp0.2.2.2 false r b hr)
  rcases h1 with ⟨⟨ex1, hgs1_eq, haon1, hlen1, hfan1⟩, h1_rb, hwOk0_lt, hd_wOk0, _⟩
  change gs1 = gs0 ++ ex1 at hgs1_eq
  change PEqualNP.MetaComplexity.NestedCover.ReadsBack (4 * n) ⟨gs1, 0⟩ at h1_rb
  change wOk0 < 4 * n + gs1.length at hwOk0_lt
  change (evalDepths gs1 (List.replicate (4 * n) 0)).getD wOk0 0 ≤ 13 at hd_wOk0
  have h1_base : base7 n ≤ 4 * n + gs1.length := by rw [hgs1_eq]; simp; omega
  have h1_d : ∀ i < base7 n, (evalDepths gs1 (List.replicate (4 * n) 0)).getD i 0 ≤ 7 := by
    intro i hi
    rw [hgs1_eq, evalDepths_append, evalDepths_prefix_getD ex1 _ (by rw [evalDepths_length]; simp; rw [← base7_eq]; exact hi)]
    exact h0_d i hi
  have hw1_pre0 : ∀ i < base7 n, (evalWires gs1 (tableInput T0)).getD i false =
      (evalWires gs0 (tableInput T0)).getD i false := fun i hi => by
    rw [hgs1_eq, evalWires_append, evalWires_prefix_getD ex1 _ (by rw [evalWires_length, tableInput_length, ← base7_eq]; exact hi)]
  have h2 := buildForB0_props hn T0 true gs1 h1_rb h1_base h1_d
    (fun i hi => by rw [hw1_pre0 _ (wireNE_lt n i hi)]; exact hp0.1 i hi)
    (fun k hk a => by rw [hw1_pre0 _ (wireBlock_lt n k hk a)]; exact hp0.2.1 k hk a)
    (fun l a hl => by rw [hw1_pre0 _ (wireLeft_lt n true l hl a)]; exact hp0.2.2.1 true l a hl)
    (fun r b hr => by rw [hw1_pre0 _ (wireRight_lt n true r hr b)]; exact hp0.2.2.2 true r b hr)
  rcases h2 with ⟨⟨ex2, hgs2_eq, haon2, hlen2, hfan2⟩, h2_rb, hwOk1_lt, hd_wOk1, _⟩
  change gs2 = gs1 ++ ex2 at hgs2_eq
  change PEqualNP.MetaComplexity.NestedCover.ReadsBack (4 * n) ⟨gs2, 0⟩ at h2_rb
  change wOk1 < 4 * n + gs2.length at hwOk1_lt
  change (evalDepths gs2 (List.replicate (4 * n) 0)).getD wOk1 0 ≤ 13 at hd_wOk1
  have hrb_C : PEqualNP.MetaComplexity.NestedCover.ReadsBack (4 * n) C := by
    have hrb := readsBack_append_snoc (4 * n) gs2 gOut C.output h2_rb (fun i hi => by
      simp only [gOut, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rw [hgs2_eq]; simp; omega
      · exact hwOk1_lt)
    exact hrb
  have hgs_all : C.gates = gs0 ++ (ex1 ++ ex2 ++ [gOut]) := by
    rw [hC_gates, hgs2_eq, hgs1_eq]; simp [List.append_assoc]
  have hC_size : C.size = gs2.length + 1 := by simp [PEqualNP.CircuitLowerBounds.Circuit.size, hC_gates]
  have hgs2_len_ge : 34 * n + 2 ≤ gs2.length := by
    rw [hgs2_eq, hgs1_eq]; simp [gs0, prefix7_len]
  refine ⟨hrb_C, by rw [hC_out, hC_size]; omega, by rw [hC_size]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hpre : PEqualNP.MetaComplexity.NestedCover.gateAt C i =
        (layer1 n)[i]'(by rw [layer1_len]; exact hi) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [hgs_all]
      unfold gs0 prefix7
      simp only [List.append_assoc]
      rw [getD_append_left (layer1 n) _ _ (by rw [layer1_len]; exact hi),
        List.getD_eq_getElem _ _ (by rw [layer1_len]; exact hi)]
    rw [hpre]
    simp [layer1]
  · intro j hj
    have hpre : PEqualNP.MetaComplexity.NestedCover.gateAt C (n + j) =
        (layer2 n)[j]'(by rw [layer2_len]; exact hj) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [hgs_all]
      unfold gs0 prefix7
      simp only [List.append_assoc]
      rw [getD_append_right (layer1 n) _ _ (by rw [layer1_len]; omega)]
      rw [layer1_len, Nat.add_sub_cancel_left]
      rw [getD_append_left (layer2 n) _ _ (by rw [layer2_len]; exact hj),
        List.getD_eq_getElem _ _ (by rw [layer2_len]; exact hj)]
    rw [hpre]
    simp [layer2]
  · intro k hk hge
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k]'hk := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      exact List.getD_eq_getElem _ _ hk
    rw [hgate]
    have htail : C.gates = (layer1 n ++ layer2 n) ++
        (layer3 n ++ layer4 n ++ layer5 n ++ layer6 n ++ layer7 n ++ ex1 ++ ex2 ++ [gOut]) := by
      rw [hgs_all]; unfold gs0 prefix7; simp [List.append_assoc]
    have hlen12 : (layer1 n ++ layer2 n).length = 2 * n := by
      rw [List.length_append, layer1_len, layer2_len]; omega
    have hmem : C.gates[k]'hk ∈
        layer3 n ++ layer4 n ++ layer5 n ++ layer6 n ++ layer7 n ++ ex1 ++ ex2 ++ [gOut] := by
      have hk' : k < ((layer1 n ++ layer2 n) ++
          (layer3 n ++ layer4 n ++ layer5 n ++ layer6 n ++ layer7 n ++ ex1 ++ ex2 ++ [gOut])).length := by
        rw [← htail]; exact hk
      have heq : C.gates[k]'hk =
          ((layer1 n ++ layer2 n) ++
            (layer3 n ++ layer4 n ++ layer5 n ++ layer6 n ++ layer7 n ++ ex1 ++ ex2 ++ [gOut]))[k]'hk' := by
        congr 1
      rw [heq, List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with ((((((h | h) | h) | h) | h) | h) | h) | h
    · exact layer3_aon n _ h
    · exact layer4_aon n _ h
    · exact layer5_aon n _ h
    · exact layer6_aon n _ h
    · exact layer7_aon n _ h
    · exact haon1 _ h
    · exact haon2 _ h
    · rw [h]; simp [gOut]
  · unfold PEqualNP.CircuitLowerBounds.Circuit.depth PEqualNP.CircuitLowerBounds.Circuit.depths
    change (evalDepths C.gates (List.replicate (4 * n) 0)).getD C.output 0 ≤ 24
    rw [hC_gates, hC_out]
    have hsn := evalDepths_snoc_le gs2 gOut (List.replicate (4 * n) 0) 13 (fun i hi => by
      simp only [gOut, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rw [hgs2_eq, evalDepths_append, evalDepths_prefix_getD ex2 _ (by rw [evalDepths_length]; simp; exact hwOk0_lt)]
        exact hd_wOk0
      · exact hd_wOk1)
    simp only [List.length_replicate] at hsn
    omega
  · rw [hC_size, hgs2_eq, hgs1_eq]
    simp only [List.length_append, gs0, prefix7_len]
    have hlog : Nat.log2 n ≤ Nat.log2 (n + 2) := log2_mono (by omega)
    have h8 : 2 * (4 * n * (Nat.log2 n + 1)) = 8 * n * (Nat.log2 n + 1) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    have hmul : 8 * n * (Nat.log2 n + 1) ≤ 8 * (n + 2) * (Nat.log2 (n + 2) + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hlin : 50 * n + 13 ≤ 50 * (n + 2) * (Nat.log2 (n + 2) + 1) := by
      have : 1 ≤ Nat.log2 (n + 2) + 1 := by omega
      have h1 := Nat.mul_le_mul_left (50 * (n + 2)) this
      omega
    have hcomb : 50 * (n + 2) * (Nat.log2 (n + 2) + 1) + 8 * (n + 2) * (Nat.log2 (n + 2) + 1) ≤
        256 * (n + 2) * (Nat.log2 (n + 2) + 1) := by
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [hgs_all]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have hf0 : (gs0.map (fun g => g.inputs.length)).sum ≤ n * n + 105 * n := prefix7_fanin_le n
    have hfg : gOut.inputs.length = 2 := rfl
    have hnsq : n ^ 2 = n * n := Nat.pow_two n
    have hn2sq : (n + 2) ^ 2 = n * n + 4 * n + 4 := by
      rw [Nat.pow_two, Nat.add_mul, Nat.mul_add]; omega
    rw [hnsq] at hfan1 hfan2
    rw [hn2sq]
    omega
  · intro T
    have hT0 := prefix7_eval hn T
    have hT1 := buildForB0_props hn T false gs0 h0_rb h0_base h0_d hT0.1 hT0.2.1
      (fun l a hl => hT0.2.2.1 false l a hl) (fun r b hr => hT0.2.2.2 false r b hr)
    rcases hT1 with ⟨_, _, _, _, heval_ok0⟩
    change (evalWires gs1 (tableInput T)).getD wOk0 false = true ↔ _ at heval_ok0
    have hw1_preT : ∀ i < base7 n, (evalWires gs1 (tableInput T)).getD i false =
        (evalWires gs0 (tableInput T)).getD i false := fun i hi => by
      rw [hgs1_eq, evalWires_append,
        evalWires_prefix_getD ex1 _ (by rw [evalWires_length, tableInput_length, ← base7_eq]; exact hi)]
    have hT2 := buildForB0_props hn T true gs1 h1_rb h1_base h1_d
      (fun i hi => by rw [hw1_preT _ (wireNE_lt n i hi)]; exact hT0.1 i hi)
      (fun k hk a => by rw [hw1_preT _ (wireBlock_lt n k hk a)]; exact hT0.2.1 k hk a)
      (fun l a hl => by rw [hw1_preT _ (wireLeft_lt n true l hl a)]; exact hT0.2.2.1 true l a hl)
      (fun r b hr => by rw [hw1_preT _ (wireRight_lt n true r hr b)]; exact hT0.2.2.2 true r b hr)
    rcases hT2 with ⟨_, _, _, _, heval_ok1⟩
    change (evalWires gs2 (tableInput T)).getD wOk1 false = true ↔ _ at heval_ok1
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    change (evalWires C.gates (tableInput T)).getD C.output false = true ↔ _
    rw [hC_gates, hC_out]
    have hsn := evalWires_snoc gs2 gOut (tableInput T)
    rw [tableInput_length] at hsn
    rw [hsn]
    simp only [gOut, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
    have hpre0 : (evalWires gs2 (tableInput T)).getD wOk0 false =
        (evalWires gs1 (tableInput T)).getD wOk0 false := by
      rw [hgs2_eq, evalWires_append,
        evalWires_prefix_getD ex2 _ (by rw [evalWires_length, tableInput_length]; exact hwOk0_lt)]
    rw [hpre0, heval_ok0, heval_ok1, comb_char hn T]
    constructor
    · rintro (h | h)
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    · rintro ⟨b0, h⟩
      cases b0
      · exact Or.inl h
      · exact Or.inr h
