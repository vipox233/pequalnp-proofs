import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1359_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl step x

lemma wires_eq_run (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_append (gs1 gs2 : List Gate) (x : List Bool) :
    run (gs1 ++ gs2) x = run gs2 (run gs1 x) :=
  List.foldl_append

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = step (run gs x) g := by
  rw [run_append, run, List.foldl_cons, List.foldl_nil]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, step, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
    omega

lemma getD_append_lt {α : Type*} (l : List α) (b dft : α) (t : ℕ) (ht : t < l.length) :
    (l ++ [b]).getD t dft = l.getD t dft := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]

lemma getD_append_eq {α : Type*} (l : List α) (b dft : α) :
    (l ++ [b]).getD l.length dft = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
  simp

lemma run_prefix (gs1 gs2 : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs1.length) :
    (run (gs1 ++ gs2) x).getD w false = (run gs1 x).getD w false := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    rw [← List.append_assoc, run_snoc, step, getD_append_lt]
    · exact ih
    · rw [run_length, List.length_append]
      omega

lemma run_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (run (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (run gs x).getD i false) := by
  rw [run_snoc, step, ← run_length gs x, getD_append_eq]

def prefixInp (n : ℕ) (t : Fin (n + 1)) : List Bool :=
  List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false, true]

lemma prefixInp_length (n : ℕ) (t : Fin (n + 1)) : (prefixInp n t).length = n + 2 := by
  simp [prefixInp]

lemma prefixInp_getD_lt (n : ℕ) (t : Fin (n + 1)) (j : ℕ) (hj : j < n) :
    (prefixInp n t).getD j false = decide (j < t.val) := by
  unfold prefixInp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hj])]
  rw [List.getElem?_eq_getElem (by simp [hj]), Option.getD_some, List.getElem_ofFn]

lemma prefixInp_getD_n (n : ℕ) (t : Fin (n + 1)) :
    (prefixInp n t).getD n false = false := by
  unfold prefixInp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

lemma prefixInp_getD_n1 (n : ℕ) (t : Fin (n + 1)) :
    (prefixInp n t).getD (n + 1) false = true := by
  unfold prefixInp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  have h1 : n + 1 - (List.ofFn (fun j : Fin n => decide (j.val < t.val))).length = 1 := by
    simp
  rw [h1]
  rfl

lemma prefixInp_getD_ge (n : ℕ) (t : Fin (n + 1)) (w : ℕ) (hw : n + 2 ≤ w) :
    (prefixInp n t).getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [prefixInp_length]; exact hw)]
  rfl

lemma prefixInp_mono (n : ℕ) {t1 t2 : Fin (n + 1)} (ht : t1.val ≤ t2.val) (w : ℕ) :
    (prefixInp n t1).getD w false = true → (prefixInp n t2).getD w false = true := by
  by_cases h1 : w < n
  · rw [prefixInp_getD_lt n t1 w h1, prefixInp_getD_lt n t2 w h1]
    simp only [decide_eq_true_eq]
    omega
  · by_cases h2 : w = n
    · subst h2
      rw [prefixInp_getD_n, prefixInp_getD_n]
      exact id
    · by_cases h3 : w = n + 1
      · subst h3
        rw [prefixInp_getD_n1, prefixInp_getD_n1]
        exact id
      · have h4 : n + 2 ≤ w := by omega
        rw [prefixInp_getD_ge n t1 w h4, prefixInp_getD_ge n t2 w h4]
        exact id

def ValidGates (n : ℕ) (gs : List Gate) : Prop :=
  FanInTwo ⟨gs, 0⟩ ∧ ReadsBack (n + 2) ⟨gs, 0⟩

def nc (gs : List Gate) : ℕ :=
  notCount ⟨gs, 0⟩

lemma nc_eq_notCount (C : Circuit) : nc C.gates = notCount C := rfl

lemma nc_nil : nc [] = 0 := rfl

lemma nc_snoc_ne (gs : List Gate) (g : Gate) (h : g.op ≠ GateOp.not) :
    nc (gs ++ [g]) = nc gs := by
  unfold nc notCount
  dsimp only
  simp only [List.filter_append, List.length_append, List.filter_cons, List.filter_nil,
    decide_eq_true_eq, h, ↓reduceIte, List.length_nil, Nat.add_zero]

lemma nc_snoc_not (gs : List Gate) (g : Gate) (h : g.op = GateOp.not) :
    nc (gs ++ [g]) = nc gs + 1 := by
  unfold nc notCount
  dsimp only
  simp only [List.filter_append, List.length_append, List.filter_cons, List.filter_nil,
    decide_eq_true_eq, h, ↓reduceIte, List.length_singleton]

lemma valid_nil (n : ℕ) : ValidGates n [] := by
  refine ⟨?_, ?_⟩
  · intro g hg
    simp at hg
  · intro j hj
    simp at hj

lemma valid_snoc (n : ℕ) (gs : List Gate) (g : Gate)
    (hv : ValidGates n gs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < n + 2 + gs.length) :
    ValidGates n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hv.1 g' hg'
    · refine ⟨?_, hlen⟩
      rcases hop with h | h | h <;> simp [h]
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hga : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        unfold gateAt
        exact getD_append_lt gs g ⟨GateOp.or, []⟩ j hlt
      rw [hga] at hi
      exact hv.2 j hlt i hi
    · have hj_eq : j = gs.length := by omega
      subst hj_eq
      have hga : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        unfold gateAt
        exact getD_append_eq gs g ⟨GateOp.or, []⟩
      rw [hga] at hi
      exact hrb i hi

lemma valid_prefix (n : ℕ) (gs : List Gate) (g : Gate) (hv : ValidGates n (gs ++ [g])) :
    ValidGates n gs := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    exact hv.1 g' (List.mem_append_left _ hg')
  · intro j hj i hi
    have hj' : j < gs.length := hj
    have hga : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
      unfold gateAt
      exact getD_append_lt gs g ⟨GateOp.or, []⟩ j hj'
    have hlt : j < (gs ++ [g]).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    exact hv.2 j hlt i (by rw [hga]; exact hi)

abbrev St (b a : ℕ) : Type := Fin (2 ^ b) × (Fin a → Bool)

def StLe {b a : ℕ} (x y : St b a) : Prop :=
  x.1.val < y.1.val ∨ (x.1 = y.1 ∧ ∀ i : Fin a, x.2 i = true → y.2 i = true)

lemma stLe_refl {b a : ℕ} (x : St b a) : StLe x x :=
  Or.inr ⟨rfl, fun _ h => h⟩

lemma stLe_trans {b a : ℕ} {x y z : St b a} (h1 : StLe x y) (h2 : StLe y z) : StLe x z := by
  rcases h1 with hlt | ⟨heq, hm⟩
  · rcases h2 with hlt2 | ⟨heq2, _⟩
    · exact Or.inl (lt_trans hlt hlt2)
    · exact Or.inl (by rw [← heq2]; exact hlt)
  · rcases h2 with hlt2 | ⟨heq2, hm2⟩
    · exact Or.inl (by rw [heq]; exact hlt2)
    · exact Or.inr ⟨heq.trans heq2, fun i hi => hm2 i (hm i hi)⟩

lemma gates_seg (n : ℕ) (gs : List Gate) (hfan : FanInTwo ⟨gs, 0⟩) :
    ∃ seg : Fin (n + 1) → Fin (2 ^ nc gs),
      (∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → (seg t1).val ≤ (seg t2).val) ∧
      ∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → seg t1 = seg t2 →
        ∀ w : ℕ, (run gs (prefixInp n t1)).getD w false = true →
          (run gs (prefixInp n t2)).getD w false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun _ => ⟨0, by simp [nc_nil]⟩, fun _ _ _ => le_rfl, fun t1 t2 ht _ w hw => ?_⟩
    exact prefixInp_mono n ht w hw
  | append_singleton gs g ih =>
    have hfan_gs : FanInTwo ⟨gs, 0⟩ := fun g' hg' => hfan g' (List.mem_append_left _ hg')
    obtain ⟨seg, hseg_mono, hwire_mono⟩ := ih hfan_gs
    have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      have hmem := (hfan g (by simp)).1
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    rcases hg_op with hop | hop | hop
    · have hnc : nc (gs ++ [g]) = nc gs := nc_snoc_ne gs g (by rw [hop]; intro h; cases h)
      refine ⟨fun t => ⟨(seg t).val, by rw [hnc]; exact (seg t).isLt⟩,
        fun t1 t2 ht => hseg_mono t1 t2 ht, fun t1 t2 ht hse w hw => ?_⟩
      have hse' : seg t1 = seg t2 := Fin.ext (by simpa using congrArg Fin.val hse)
      by_cases hlt : w < n + 2 + gs.length
      · have h1 := run_prefix gs [g] (prefixInp n t1) w (by rw [prefixInp_length]; exact hlt)
        have h2 := run_prefix gs [g] (prefixInp n t2) w (by rw [prefixInp_length]; exact hlt)
        rw [h1] at hw
        rw [h2]
        exact hwire_mono t1 t2 ht hse' w hw
      · by_cases heq : w = n + 2 + gs.length
        · subst heq
          have h1 := run_snoc_last gs g (prefixInp n t1)
          have h2 := run_snoc_last gs g (prefixInp n t2)
          rw [prefixInp_length] at h1 h2
          rw [h1, hop] at hw
          rw [h2, hop]
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hw ⊢
          rintro b ⟨i, hi, rfl⟩
          exact hwire_mono t1 t2 ht hse' i (hw _ ⟨i, hi, rfl⟩)
        · have hge : (run (gs ++ [g]) (prefixInp n t1)).length ≤ w := by
            rw [run_length, prefixInp_length, List.length_append, List.length_singleton]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hw
          cases hw
    · have hnc : nc (gs ++ [g]) = nc gs := nc_snoc_ne gs g (by rw [hop]; intro h; cases h)
      refine ⟨fun t => ⟨(seg t).val, by rw [hnc]; exact (seg t).isLt⟩,
        fun t1 t2 ht => hseg_mono t1 t2 ht, fun t1 t2 ht hse w hw => ?_⟩
      have hse' : seg t1 = seg t2 := Fin.ext (by simpa using congrArg Fin.val hse)
      by_cases hlt : w < n + 2 + gs.length
      · have h1 := run_prefix gs [g] (prefixInp n t1) w (by rw [prefixInp_length]; exact hlt)
        have h2 := run_prefix gs [g] (prefixInp n t2) w (by rw [prefixInp_length]; exact hlt)
        rw [h1] at hw
        rw [h2]
        exact hwire_mono t1 t2 ht hse' w hw
      · by_cases heq : w = n + 2 + gs.length
        · subst heq
          have h1 := run_snoc_last gs g (prefixInp n t1)
          have h2 := run_snoc_last gs g (prefixInp n t2)
          rw [prefixInp_length] at h1 h2
          rw [h1, hop] at hw
          rw [h2, hop]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hw ⊢
          rcases hw with ⟨_, ⟨i, hi, rfl⟩, hbi⟩
          exact ⟨_, ⟨i, hi, rfl⟩, hwire_mono t1 t2 ht hse' i hbi⟩
        · have hge : (run (gs ++ [g]) (prefixInp n t1)).length ≤ w := by
            rw [run_length, prefixInp_length, List.length_append, List.length_singleton]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hw
          cases hw
    · have hnc : nc (gs ++ [g]) = nc gs + 1 := nc_snoc_not gs g hop
      let inpVal : Fin (n + 1) → Bool := fun t =>
        (g.inputs.map fun i => (run gs (prefixInp n t)).getD i false).headD false
      have hinp_mono : ∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → seg t1 = seg t2 →
          inpVal t1 = true → inpVal t2 = true := by
        intro t1 t2 ht hse h1
        dsimp only [inpVal] at h1 ⊢
        cases hins : g.inputs with
        | nil => simp [hins] at h1
        | cons i tl =>
          simp only [hins, List.map_cons, List.headD_cons] at h1 ⊢
          exact hwire_mono t1 t2 ht hse i h1
      let seg' : Fin (n + 1) → Fin (2 ^ nc (gs ++ [g])) := fun t =>
        ⟨2 * (seg t).val + if inpVal t then 1 else 0, by
          rw [hnc, pow_succ]
          have hlt := (seg t).isLt
          split_ifs <;> omega⟩
      refine ⟨seg', ?_, ?_⟩
      · intro t1 t2 ht
        dsimp only [seg']
        have hm := hseg_mono t1 t2 ht
        by_cases heq : (seg t1).val = (seg t2).val
        · have hse : seg t1 = seg t2 := Fin.ext heq
          rw [heq]
          cases hb1 : inpVal t1
          · simp
          · have hb2 := hinp_mono t1 t2 ht hse hb1
            rw [hb2]
        · split_ifs <;> omega
      · intro t1 t2 ht hse' w hw
        have hval : 2 * (seg t1).val + (if inpVal t1 then 1 else 0) =
            2 * (seg t2).val + (if inpVal t2 then 1 else 0) := congrArg Fin.val hse'
        have hseg_eq : seg t1 = seg t2 := by
          apply Fin.ext
          split_ifs at hval <;> omega
        have hinp_eq : inpVal t1 = inpVal t2 := by
          cases hb1 : inpVal t1 <;> cases hb2 : inpVal t2
          · rfl
          · rw [hb1, hb2] at hval; simp at hval; omega
          · rw [hb1, hb2] at hval; simp at hval; omega
          · rfl
        by_cases hlt : w < n + 2 + gs.length
        · have h1 := run_prefix gs [g] (prefixInp n t1) w (by rw [prefixInp_length]; exact hlt)
          have h2 := run_prefix gs [g] (prefixInp n t2) w (by rw [prefixInp_length]; exact hlt)
          rw [h1] at hw
          rw [h2]
          exact hwire_mono t1 t2 ht hseg_eq w hw
        · by_cases heq : w = n + 2 + gs.length
          · subst heq
            have h1 := run_snoc_last gs g (prefixInp n t1)
            have h2 := run_snoc_last gs g (prefixInp n t2)
            rw [prefixInp_length] at h1 h2
            rw [h1, hop] at hw
            rw [h2, hop]
            change !inpVal t1 = true at hw
            change !inpVal t2 = true
            rw [← hinp_eq]
            exact hw
          · have hge : (run (gs ++ [g]) (prefixInp n t1)).length ≤ w := by
              rw [run_length, prefixInp_length, List.length_append, List.length_singleton]; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hw
            cases hw

lemma circuit_to_chain (a n b : ℕ) (C : Circuit) (tap : Fin a → ℕ)
    (hfan : FanInTwo C) (hnc : notCount C ≤ b) :
    ∃ φ : Fin (n + 1) → St b a,
      (∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → StLe (φ t1) (φ t2)) ∧
      ∀ t i, (φ t).2 i = (C.wires (prefixInp n t)).getD (tap i) false := by
  have hfan' : FanInTwo ⟨C.gates, 0⟩ := hfan
  obtain ⟨seg, hseg_mono, hwire_mono⟩ := gates_seg n C.gates hfan'
  have hpow : 2 ^ nc C.gates ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hnc
  let φ : Fin (n + 1) → St b a := fun t =>
    (⟨(seg t).val, lt_of_lt_of_le (seg t).isLt hpow⟩,
      fun i => (C.wires (prefixInp n t)).getD (tap i) false)
  refine ⟨φ, ?_, fun t i => rfl⟩
  intro t1 t2 ht
  have hm := hseg_mono t1 t2 ht
  by_cases heq : (seg t1).val = (seg t2).val
  · refine Or.inr ⟨Fin.ext heq, fun i hi => ?_⟩
    exact hwire_mono t1 t2 ht (Fin.ext heq) (tap i) hi
  · exact Or.inl (by dsimp [φ]; omega)

lemma mono_on_subset_wire (n : ℕ) (P : Fin (n + 1) → Prop) (f : Fin (n + 1) → Bool)
    (hf : ∀ t1 t2 : Fin (n + 1), P t1 → P t2 → t1.val ≤ t2.val → f t1 = true → f t2 = true) :
    ∃ w < n + 2, ∀ t : Fin (n + 1), P t → (prefixInp n t).getD w false = f t := by
  classical
  by_cases hex : ∃ k : ℕ, ∃ hk : k < n + 1, P ⟨k, hk⟩ ∧ f ⟨k, hk⟩ = true
  · let k0 := Nat.find hex
    have hk0_spec : ∃ hk : k0 < n + 1, P ⟨k0, hk⟩ ∧ f ⟨k0, hk⟩ = true := Nat.find_spec hex
    obtain ⟨hk0_lt, hk0_P, hk0_f⟩ := hk0_spec
    by_cases h0 : k0 = 0
    · refine ⟨n + 1, by omega, fun t ht => ?_⟩
      rw [prefixInp_getD_n1]
      exact (hf ⟨k0, hk0_lt⟩ t hk0_P ht (by dsimp; omega) hk0_f).symm
    · refine ⟨k0 - 1, by omega, fun t ht => ?_⟩
      rw [prefixInp_getD_lt n t (k0 - 1) (by omega)]
      by_cases hle : k0 ≤ t.val
      · have hlt : k0 - 1 < t.val := by omega
        rw [decide_eq_true hlt]
        exact (hf ⟨k0, hk0_lt⟩ t hk0_P ht hle hk0_f).symm
      · have hnot : ¬ (k0 - 1 < t.val) := by omega
        rw [decide_eq_false hnot]
        cases hft : f t
        · rfl
        · exfalso
          have hmin := Nat.find_min hex (show t.val < k0 by omega)
          exact hmin ⟨t.isLt, ht, hft⟩
  · refine ⟨n, by omega, fun t ht => ?_⟩
    rw [prefixInp_getD_n]
    cases hft : f t
    · rfl
    · exfalso
      exact hex ⟨t.val, t.isLt, ht, hft⟩

lemma build_or_and_pairs (n : ℕ) (gs : List Gate) (hv : ValidGates n gs)
    (ps : List (ℕ × ℕ))
    (hps : ∀ p ∈ ps, p.1 < n + 2 + gs.length ∧ p.2 < n + 2 + gs.length) :
    ∃ (gs' : List Gate) (out : ℕ),
      ValidGates n (gs ++ gs') ∧
      nc (gs ++ gs') = nc gs ∧
      out < n + 2 + (gs ++ gs').length ∧
      ∀ t : Fin (n + 1),
        (run (gs ++ gs') (prefixInp n t)).getD out false =
          ps.any fun p =>
            (run gs (prefixInp n t)).getD p.1 false && (run gs (prefixInp n t)).getD p.2 false := by
  induction ps with
  | nil =>
    refine ⟨[], n, by simpa using hv, by simp, by simp; omega, fun t => ?_⟩
    simp only [List.append_nil, List.any_nil]
    rw [show gs = [] ++ gs by rfl]
    rw [run_prefix [] gs (prefixInp n t) n (by rw [prefixInp_length]; omega)]
    exact prefixInp_getD_n n t
  | cons p tl ih =>
    have htl : ∀ q ∈ tl, q.1 < n + 2 + gs.length ∧ q.2 < n + 2 + gs.length :=
      fun q hq => hps q (List.mem_cons_of_mem p hq)
    obtain ⟨gs1, out1, hv1, hnc1, hout1, hev1⟩ := ih htl
    have hp := hps p (List.mem_cons_self ..)
    let gAnd : Gate := ⟨GateOp.and, [p.1, p.2]⟩
    let wAnd : ℕ := n + 2 + (gs ++ gs1).length
    let gOr : Gate := ⟨GateOp.or, [wAnd, out1]⟩
    let wOr : ℕ := n + 2 + (gs ++ gs1).length + 1
    have hv2 : ValidGates n ((gs ++ gs1) ++ [gAnd]) := by
      refine valid_snoc n (gs ++ gs1) gAnd hv1 (Or.inl rfl) (by simp [gAnd]) ?_
      intro i hi
      simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> simp only [List.length_append] <;> omega
    have hv3 : ValidGates n (((gs ++ gs1) ++ [gAnd]) ++ [gOr]) := by
      refine valid_snoc n ((gs ++ gs1) ++ [gAnd]) gOr hv2 (Or.inr (Or.inl rfl)) (by simp [gOr]) ?_
      intro i hi
      simp only [gOr, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> simp only [List.length_append, List.length_singleton, wAnd] at hout1 ⊢ <;> omega
    refine ⟨gs1 ++ [gAnd, gOr], wOr, ?_, ?_, ?_, ?_⟩
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using hv3
    · have h1 : nc ((gs ++ gs1) ++ [gAnd]) = nc (gs ++ gs1) := nc_snoc_ne _ gAnd (by intro h; cases h)
      have h2 : nc (((gs ++ gs1) ++ [gAnd]) ++ [gOr]) = nc ((gs ++ gs1) ++ [gAnd]) :=
        nc_snoc_ne _ gOr (by intro h; cases h)
      have hassoc : gs ++ (gs1 ++ [gAnd, gOr]) = ((gs ++ gs1) ++ [gAnd]) ++ [gOr] := by simp
      rw [hassoc, h2, h1, hnc1]
    · simp only [List.length_append, List.length_cons, List.length_nil, wOr]
      omega
    · intro t
      have hassoc : gs ++ (gs1 ++ [gAnd, gOr]) = ((gs ++ gs1) ++ [gAnd]) ++ [gOr] := by simp
      rw [hassoc]
      have hwOr_eq : wOr = (prefixInp n t).length + ((gs ++ gs1) ++ [gAnd]).length := by
        rw [prefixInp_length, List.length_append, List.length_singleton]
        dsimp only [wOr]
        omega
      rw [hwOr_eq, run_snoc_last]
      simp only [gOr, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      have hwAnd_val : (run ((gs ++ gs1) ++ [gAnd]) (prefixInp n t)).getD wAnd false =
          ((run gs (prefixInp n t)).getD p.1 false && (run gs (prefixInp n t)).getD p.2 false) := by
        have hwAnd_eq : wAnd = (prefixInp n t).length + (gs ++ gs1).length := by
          rw [prefixInp_length]
        rw [hwAnd_eq, run_snoc_last]
        simp only [gAnd, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
          Bool.and_true]
        rw [run_prefix gs gs1 (prefixInp n t) p.1 (by rw [prefixInp_length]; exact hp.1)]
        rw [run_prefix gs gs1 (prefixInp n t) p.2 (by rw [prefixInp_length]; exact hp.2)]
      have hout1_val : (run ((gs ++ gs1) ++ [gAnd]) (prefixInp n t)).getD out1 false =
          (run (gs ++ gs1) (prefixInp n t)).getD out1 false :=
        run_prefix (gs ++ gs1) [gAnd] (prefixInp n t) out1 (by rw [prefixInp_length]; exact hout1)
      rw [hwAnd_val, hout1_val, hev1 t]

lemma build_indicators (n b : ℕ) (seg : Fin (n + 1) → Fin (2 ^ b))
    (hseg : ∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → (seg t1).val ≤ (seg t2).val) :
    ∃ (gs : List Gate) (ind : Fin (2 ^ b) → ℕ),
      ValidGates n gs ∧
      nc gs ≤ b ∧
      (∀ r, ind r < n + 2 + gs.length) ∧
      ∀ (r : Fin (2 ^ b)) (t : Fin (n + 1)),
        (run gs (prefixInp n t)).getD (ind r) false = decide (seg t = r) := by
  induction b with
  | zero =>
    refine ⟨[], fun _ => n + 1, valid_nil n, le_rfl, fun _ => by simp, fun r t => ?_⟩
    rw [run_nil, prefixInp_getD_n1]
    have heq : seg t = r := Fin.ext (by
      have h1 := (seg t).isLt
      have h2 := r.isLt
      simp at h1 h2
      omega)
    simp [heq]
  | succ b ih =>
    let high : Fin (n + 1) → Fin (2 ^ b) := fun t =>
      ⟨(seg t).val / 2, by have hlt := (seg t).isLt; have hpow : 2 ^ (b + 1) = 2 ^ b * 2 := pow_succ 2 b; omega⟩
    have hhigh_mono : ∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → (high t1).val ≤ (high t2).val :=
      fun t1 t2 ht => Nat.div_le_div_right (hseg t1 t2 ht)
    obtain ⟨gs0, indH, hv0, hnc0, hindH_lt, hindH_ev⟩ := ih high hhigh_mono
    let low : Fin (n + 1) → Bool := fun t => decide ((seg t).val % 2 = 1)
    have hlow_mono : ∀ r : Fin (2 ^ b), ∃ w < n + 2,
        ∀ t : Fin (n + 1), high t = r → (prefixInp n t).getD w false = low t := by
      intro r
      apply mono_on_subset_wire n (fun t => high t = r) low
      intro t1 t2 hr1 hr2 ht hl1
      have hdiv : (seg t1).val / 2 = (seg t2).val / 2 := by
        have := hr1.trans hr2.symm
        exact congrArg Fin.val this
      have hle := hseg t1 t2 ht
      dsimp only [low] at hl1 ⊢
      simp only [decide_eq_true_eq] at hl1 ⊢
      omega
    choose lowW hlowW_lt hlowW_ev using hlow_mono
    let ps : List (ℕ × ℕ) := (List.finRange (2 ^ b)).map fun r => (indH r, lowW r)
    have hps_lt : ∀ p ∈ ps, p.1 < n + 2 + gs0.length ∧ p.2 < n + 2 + gs0.length := by
      intro p hp
      simp only [ps, List.mem_map, List.mem_finRange, true_and] at hp
      rcases hp with ⟨r, rfl⟩
      exact ⟨hindH_lt r, lt_of_lt_of_le (hlowW_lt r) (by omega)⟩
    obtain ⟨gs1, wLow, hv1, hnc1, hwLow_lt, hwLow_ev⟩ := build_or_and_pairs n gs0 hv0 ps hps_lt
    have hwLow_eq : ∀ t : Fin (n + 1),
        (run (gs0 ++ gs1) (prefixInp n t)).getD wLow false = low t := by
      intro t
      rw [hwLow_ev t]
      apply Bool.eq_iff_iff.2
      simp only [ps, List.any_map, List.any_eq_true, List.mem_finRange, true_and,
        Function.comp_apply, Bool.and_eq_true]
      constructor
      · rintro ⟨r, hr, hw⟩
        rw [hindH_ev r t, decide_eq_true_eq] at hr
        have hpr : (run gs0 (prefixInp n t)).getD (lowW r) false = (prefixInp n t).getD (lowW r) false := by
          rw [show gs0 = [] ++ gs0 by rfl, run_prefix [] gs0 (prefixInp n t) (lowW r) (by rw [prefixInp_length]; exact hlowW_lt r)]
          rfl
        rw [hpr, hlowW_ev r t hr] at hw
        exact hw
      · intro hl
        refine ⟨high t, ?_, ?_⟩
        · rw [hindH_ev (high t) t, decide_eq_true rfl]
        · have hpr : (run gs0 (prefixInp n t)).getD (lowW (high t)) false =
              (prefixInp n t).getD (lowW (high t)) false := by
            rw [show gs0 = [] ++ gs0 by rfl, run_prefix [] gs0 (prefixInp n t) (lowW (high t)) (by rw [prefixInp_length]; exact hlowW_lt (high t))]
            rfl
          rw [hpr, hlowW_ev (high t) t rfl]
          exact hl
    let gNot : Gate := ⟨GateOp.not, [wLow]⟩
    let wNot : ℕ := n + 2 + (gs0 ++ gs1).length
    have hv2 : ValidGates n ((gs0 ++ gs1) ++ [gNot]) := by
      refine valid_snoc n (gs0 ++ gs1) gNot hv1 (Or.inr (Or.inr rfl)) (by simp [gNot]) ?_
      intro i hi
      simp only [gNot, List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi
      exact hwLow_lt
    have hnc2 : nc ((gs0 ++ gs1) ++ [gNot]) ≤ b + 1 := by
      rw [nc_snoc_not _ gNot rfl, hnc1]
      omega
    let gs2 := (gs0 ++ gs1) ++ [gNot]
    have hnot_ev : ∀ t : Fin (n + 1),
        (run gs2 (prefixInp n t)).getD wNot false = !(low t) := by
      intro t
      have hw : wNot = (prefixInp n t).length + (gs0 ++ gs1).length := by rw [prefixInp_length]
      dsimp only [gs2]
      rw [hw, run_snoc_last]
      simp only [gNot, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, hwLow_eq t]
    have hlow_ev2 : ∀ t : Fin (n + 1),
        (run gs2 (prefixInp n t)).getD wLow false = low t := by
      intro t
      dsimp only [gs2]
      rw [run_prefix (gs0 ++ gs1) [gNot] (prefixInp n t) wLow (by rw [prefixInp_length]; exact hwLow_lt)]
      exact hwLow_eq t
    have hindH_ev2 : ∀ (r : Fin (2 ^ b)) (t : Fin (n + 1)),
        (run gs2 (prefixInp n t)).getD (indH r) false = decide (high t = r) := by
      intro r t
      dsimp only [gs2]
      rw [List.append_assoc, run_prefix gs0 (gs1 ++ [gNot]) (prefixInp n t) (indH r)
        (by rw [prefixInp_length]; exact hindH_lt r)]
      exact hindH_ev r t
    let mkAnd : Fin (2 ^ (b + 1)) → Gate := fun r' =>
      let r : Fin (2 ^ b) := ⟨r'.val / 2, by have := r'.isLt; have hpow : 2 ^ (b + 1) = 2 ^ b * 2 := pow_succ 2 b; omega⟩
      ⟨GateOp.and, [indH r, if r'.val % 2 = 1 then wLow else wNot]⟩
    let gsAnd : List Gate := (List.finRange (2 ^ (b + 1))).map mkAnd
    have hgsAnd_len : gsAnd.length = 2 ^ (b + 1) := by simp [gsAnd]
    have hbuild : ∀ (k : ℕ) (hk : k ≤ 2 ^ (b + 1)),
        ValidGates n (gs2 ++ gsAnd.take k) ∧ nc (gs2 ++ gsAnd.take k) = nc gs2 := by
      intro k hk
      induction k with
      | zero =>
        simp only [List.take_zero, List.append_nil, and_true]
        exact hv2
      | succ k ihk =>
        obtain ⟨hvk, hnck⟩ := ihk (by omega)
        have hlt : k < gsAnd.length := by rw [hgsAnd_len]; omega
        rw [List.take_succ_eq_append_getElem hlt, ← List.append_assoc]
        have hget : gsAnd[k] = mkAnd ⟨k, by omega⟩ := by
          simp [gsAnd]
        rw [hget]
        refine ⟨valid_snoc n (gs2 ++ gsAnd.take k) (mkAnd ⟨k, by omega⟩) hvk (Or.inl rfl) (by simp [mkAnd]) ?_, ?_⟩
        · intro i hi
          simp only [mkAnd, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · have h1 := hindH_lt ⟨k / 2, by rw [pow_succ] at hk; omega⟩
            simp only [List.length_append, List.length_singleton, gs2]
            omega
          · split_ifs
            · simp only [List.length_append, List.length_singleton, gs2] at hwLow_lt ⊢
              omega
            · simp only [List.length_append, List.length_singleton, wNot, gs2]
              omega
        · rw [nc_snoc_ne _ _ (by intro h; cases h), hnck]
    obtain ⟨hvF, hncF⟩ := hbuild (2 ^ (b + 1)) le_rfl
    have htake : gsAnd.take (2 ^ (b + 1)) = gsAnd := List.take_of_length_le (by rw [hgsAnd_len])
    rw [htake] at hvF hncF
    refine ⟨gs2 ++ gsAnd, fun r' => n + 2 + gs2.length + r'.val, hvF, by rw [hncF]; exact hnc2, ?_, ?_⟩
    · intro r'
      dsimp only
      have hlen : (gs2 ++ gsAnd).length = gs2.length + 2 ^ (b + 1) := by
        rw [List.length_append, hgsAnd_len]
      rw [hlen]
      simp only [gs2, List.length_append, List.length_singleton]
      omega
    · intro r' t
      have hsplit : gsAnd = gsAnd.take r'.val ++ [gsAnd[r'.val]'(by rw [hgsAnd_len]; exact r'.isLt)] ++ gsAnd.drop (r'.val + 1) := by
        simp
      have hpref_len : (gs2 ++ gsAnd.take r'.val).length = gs2.length + r'.val := by
        rw [List.length_append, List.length_take, hgsAnd_len, Nat.min_eq_left (le_of_lt r'.isLt)]
      have hget : gsAnd[r'.val]'(by rw [hgsAnd_len]; exact r'.isLt) = mkAnd r' := by
        simp [gsAnd]
      have hrew : gs2 ++ gsAnd = ((gs2 ++ gsAnd.take r'.val) ++ [mkAnd r']) ++ gsAnd.drop (r'.val + 1) := by
        conv_lhs => rw [hsplit]
        rw [hget]
        simp [List.append_assoc]
      rw [hrew]
      rw [run_prefix ((gs2 ++ gsAnd.take r'.val) ++ [mkAnd r']) (gsAnd.drop (r'.val + 1)) (prefixInp n t)
        (n + 2 + gs2.length + r'.val)
        (by
          have hlen : ((gs2 ++ gsAnd.take r'.val) ++ [mkAnd r']).length = gs2.length + r'.val + 1 := by
            rw [List.length_append, List.length_singleton, hpref_len]
          rw [prefixInp_length, hlen]
          simp only [gs2, List.length_append, List.length_singleton]
          omega)]
      have hidx : n + 2 + gs2.length + r'.val = (prefixInp n t).length + (gs2 ++ gsAnd.take r'.val).length := by
        rw [prefixInp_length, hpref_len]; omega
      rw [hidx, run_snoc_last]
      simp only [mkAnd, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      let r : Fin (2 ^ b) := ⟨r'.val / 2, by have := r'.isLt; have hpow : 2 ^ (b + 1) = 2 ^ b * 2 := pow_succ 2 b; omega⟩
      have h1 : (run (gs2 ++ gsAnd.take r'.val) (prefixInp n t)).getD (indH r) false =
          decide (high t = r) := by
        rw [run_prefix gs2 (gsAnd.take r'.val) (prefixInp n t) (indH r)
          (by rw [prefixInp_length]; simp only [gs2, List.length_append, List.length_singleton]; have := hindH_lt r; omega)]
        exact hindH_ev2 r t
      have h2 : (run (gs2 ++ gsAnd.take r'.val) (prefixInp n t)).getD
          (if r'.val % 2 = 1 then wLow else wNot) false =
          decide ((seg t).val % 2 = r'.val % 2) := by
        split_ifs with hmod
        · rw [run_prefix gs2 (gsAnd.take r'.val) (prefixInp n t) wLow
            (by rw [prefixInp_length]; have hlt := hwLow_lt; simp only [gs2, List.length_append, List.length_singleton] at hlt ⊢; omega)]
          rw [hlow_ev2 t, hmod]
        · rw [run_prefix gs2 (gsAnd.take r'.val) (prefixInp n t) wNot
            (by rw [prefixInp_length]; simp only [gs2, wNot, List.length_append, List.length_singleton]; omega)]
          rw [hnot_ev t]
          dsimp only [low]
          have hmod0 : r'.val % 2 = 0 := by omega
          rw [hmod0]
          have hseg2 : (seg t).val % 2 = 0 ∨ (seg t).val % 2 = 1 := by omega
          rcases hseg2 with h0 | h1' <;> simp [*]
      rw [h1, h2]
      apply Bool.eq_iff_iff.2
      simp only [Bool.and_eq_true, decide_eq_true_eq, Fin.ext_iff]
      dsimp only [high, r]
      omega

lemma chain_to_circuit (a n b : ℕ) (φ : Fin (n + 1) → St b a)
    (hφ : ∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → StLe (φ t1) (φ t2)) :
    ∃ (C : Circuit) (tap : Fin a → ℕ),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧ notCount C ≤ b ∧
      C.output < n + 2 + C.size ∧ (∀ i, tap i < n + 2 + C.size) ∧
      ∀ t i, (C.wires (prefixInp n t)).getD (tap i) false = (φ t).2 i := by
  let seg : Fin (n + 1) → Fin (2 ^ b) := fun t => (φ t).1
  have hseg : ∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → (seg t1).val ≤ (seg t2).val := by
    intro t1 t2 ht
    rcases hφ t1 t2 ht with hlt | ⟨heq, _⟩
    · exact le_of_lt hlt
    · exact le_of_eq (congrArg Fin.val heq)
  obtain ⟨gs0, ind, hv0, hnc0, hind_lt, hind_ev⟩ := build_indicators n b seg hseg
  have hstep : ∀ (k : ℕ) (hk : k ≤ a),
      ∃ (gs : List Gate) (tap : Fin k → ℕ),
        ValidGates n (gs0 ++ gs) ∧
        nc (gs0 ++ gs) = nc gs0 ∧
        (∀ i : Fin k, tap i < n + 2 + (gs0 ++ gs).length) ∧
        ∀ (t : Fin (n + 1)) (i : Fin k),
          (run (gs0 ++ gs) (prefixInp n t)).getD (tap i) false = (φ t).2 ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨[], Fin.elim0, by simpa using hv0, by simp, fun i => i.elim0, fun _ i => i.elim0⟩
    | succ k ihk =>
      obtain ⟨gs1, tap1, hv1, hnc1, htap1_lt, htap1_ev⟩ := ihk (by omega)
      let idx : Fin a := ⟨k, hk⟩
      have hcoord : ∀ r : Fin (2 ^ b), ∃ w < n + 2,
          ∀ t : Fin (n + 1), seg t = r → (prefixInp n t).getD w false = (φ t).2 idx := by
        intro r
        apply mono_on_subset_wire n (fun t => seg t = r) (fun t => (φ t).2 idx)
        intro t1 t2 hr1 hr2 ht h1
        rcases hφ t1 t2 ht with hlt | ⟨_, hm⟩
        · exfalso
          have : (seg t1).val = (seg t2).val := congrArg Fin.val (hr1.trans hr2.symm)
          dsimp only [seg] at this
          omega
        · exact hm idx h1
      choose uW huW_lt huW_ev using hcoord
      let ps : List (ℕ × ℕ) := (List.finRange (2 ^ b)).map fun r => (ind r, uW r)
      have hps_lt : ∀ p ∈ ps, p.1 < n + 2 + (gs0 ++ gs1).length ∧ p.2 < n + 2 + (gs0 ++ gs1).length := by
        intro p hp
        simp only [ps, List.mem_map, List.mem_finRange, true_and] at hp
        rcases hp with ⟨r, rfl⟩
        exact ⟨lt_of_lt_of_le (hind_lt r) (by simp), lt_of_lt_of_le (huW_lt r) (by omega)⟩
      obtain ⟨gs2, wOut, hv2, hnc2, hwOut_lt, hwOut_ev⟩ := build_or_and_pairs n (gs0 ++ gs1) hv1 ps hps_lt
      let tap2 : Fin (k + 1) → ℕ := fun i =>
        if hi : i.val < k then tap1 ⟨i.val, hi⟩ else wOut
      refine ⟨gs1 ++ gs2, tap2, ?_, ?_, ?_, ?_⟩
      · simpa only [List.append_assoc] using hv2
      · rw [← List.append_assoc, hnc2, hnc1]
      · intro i
        dsimp only [tap2]
        split_ifs with hi
        · have := htap1_lt ⟨i.val, hi⟩
          simp only [List.length_append] at this ⊢
          omega
        · simpa only [List.append_assoc] using hwOut_lt
      · intro t i
        rw [← List.append_assoc]
        dsimp only [tap2]
        split_ifs with hi
        · rw [run_prefix (gs0 ++ gs1) gs2 (prefixInp n t) (tap1 ⟨i.val, hi⟩)
            (by rw [prefixInp_length]; exact htap1_lt ⟨i.val, hi⟩)]
          exact htap1_ev t ⟨i.val, hi⟩
        · have hik : (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin a) = idx :=
            Fin.ext (by dsimp only [idx]; have := i.isLt; omega)
          rw [hik, hwOut_ev t]
          apply Bool.eq_iff_iff.2
          simp only [ps, List.any_map, List.any_eq_true, List.mem_finRange, true_and,
            Function.comp_apply, Bool.and_eq_true]
          constructor
          · rintro ⟨r, hr, hu⟩
            rw [run_prefix gs0 gs1 (prefixInp n t) (ind r) (by rw [prefixInp_length]; exact hind_lt r),
              hind_ev r t, decide_eq_true_eq] at hr
            have hpr : (run (gs0 ++ gs1) (prefixInp n t)).getD (uW r) false = (prefixInp n t).getD (uW r) false := by
              rw [show gs0 ++ gs1 = [] ++ (gs0 ++ gs1) by rfl,
                run_prefix [] (gs0 ++ gs1) (prefixInp n t) (uW r) (by rw [prefixInp_length]; exact huW_lt r)]
              rfl
            rw [hpr, huW_ev r t hr] at hu
            exact hu
          · intro hval
            refine ⟨seg t, ?_, ?_⟩
            · rw [run_prefix gs0 gs1 (prefixInp n t) (ind (seg t)) (by rw [prefixInp_length]; exact hind_lt (seg t)),
                hind_ev (seg t) t, decide_eq_true rfl]
            · have hpr : (run (gs0 ++ gs1) (prefixInp n t)).getD (uW (seg t)) false = (prefixInp n t).getD (uW (seg t)) false := by
                rw [show gs0 ++ gs1 = [] ++ (gs0 ++ gs1) by rfl,
                  run_prefix [] (gs0 ++ gs1) (prefixInp n t) (uW (seg t)) (by rw [prefixInp_length]; exact huW_lt (seg t))]
                rfl
              rw [hpr, huW_ev (seg t) t rfl]
              exact hval
  obtain ⟨gs, tap, hv, hnc, htap_lt, htap_ev⟩ := hstep a le_rfl
  refine ⟨⟨gs0 ++ gs, 0⟩, tap, hv.1, hv.2, ?_, by simp only [Circuit.size]; omega, htap_lt, fun t i => ?_⟩
  · rw [← nc_eq_notCount]
    dsimp only
    rw [hnc]
    exact hnc0
  · exact htap_ev t i

def Fit (a n b e : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (S : Finset (Fin (n + 1))) : Prop :=
  ∃ (C : Circuit) (tap : Fin a → ℕ),
    FanInTwo C ∧ ReadsBack (n + 2) C ∧ notCount C ≤ b ∧
    C.output < n + 2 + C.size ∧ (∀ i, tap i < n + 2 + C.size) ∧
    S.sum (fun t => cost t (fun i => (C.wires (prefixInp n t)).getD (tap i) false)) ≤ e

lemma fit_iff_chain (a n b e : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) (S : Finset (Fin (n + 1))) :
    Fit a n b e cost S ↔
      ∃ φ : Fin (n + 1) → St b a,
        (∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → StLe (φ t1) (φ t2)) ∧
        S.sum (fun t => cost t (φ t).2) ≤ e := by
  constructor
  · rintro ⟨C, tap, hfan, _, hnc, _, _, hsum⟩
    obtain ⟨φ, hmono, hval⟩ := circuit_to_chain a n b C tap hfan hnc
    refine ⟨φ, hmono, ?_⟩
    have heq : ∀ t, (φ t).2 = fun i => (C.wires (prefixInp n t)).getD (tap i) false :=
      fun t => funext (hval t)
    simpa only [heq] using hsum
  · rintro ⟨φ, hmono, hsum⟩
    obtain ⟨C, tap, hfan, hrb, hnc, hout, htap, hval⟩ := chain_to_circuit a n b φ hmono
    refine ⟨C, tap, hfan, hrb, hnc, hout, htap, ?_⟩
    have heq : ∀ t, (fun i => (C.wires (prefixInp n t)).getD (tap i) false) = (φ t).2 :=
      fun t => funext (hval t)
    simpa only [heq] using hsum

lemma fit_zero_iff (n b e : ℕ) (cost : Fin (n + 1) → (Fin 0 → Bool) → ℕ) (S : Finset (Fin (n + 1))) :
    Fit 0 n b e cost S ↔ S.sum (fun t => cost t Fin.elim0) ≤ e := by
  rw [fit_iff_chain]
  constructor
  · rintro ⟨φ, _, hsum⟩
    have heq : ∀ t, (φ t).2 = Fin.elim0 := fun t => funext fun i => i.elim0
    simpa only [heq] using hsum
  · intro hsum
    refine ⟨fun _ => (⟨0, Nat.two_pow_pos b⟩, Fin.elim0), fun _ _ _ => stLe_refl _, hsum⟩

lemma part1_zero (n B E : ℕ) (cost : Fin (n + 1) → (Fin 0 → Bool) → ℕ) :
    ∃ S : Finset (Fin (n + 1)), S.card ≤ (E + 1) * 1 ∧
      ∀ b ≤ B, ∀ e ≤ E, Fit 0 n b e cost Finset.univ ↔ Fit 0 n b e cost S := by
  classical
  let P := (Finset.univ : Finset (Fin (n + 1))).filter (fun t => 0 < cost t Fin.elim0)
  by_cases hcard : P.card ≤ E + 1
  · refine ⟨P, by omega, fun b _ e _ => ?_⟩
    rw [fit_zero_iff, fit_zero_iff]
    have hsum_eq : Finset.univ.sum (fun t => cost t Fin.elim0) = P.sum (fun t => cost t Fin.elim0) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ P)
      intro t _ ht
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Nat.le_zero] at ht
      exact ht
    rw [hsum_eq]
  · have hge : E + 1 ≤ P.card := by omega
    obtain ⟨S, hSP, hScard⟩ := Finset.exists_subset_card_eq hge
    refine ⟨S, by omega, fun b _ e he => ?_⟩
    rw [fit_zero_iff, fit_zero_iff]
    have hS_sum : E + 1 ≤ S.sum (fun t => cost t Fin.elim0) := by
      calc E + 1 = S.card := hScard.symm
        _ = S.sum (fun _ => 1) := by simp
        _ ≤ S.sum (fun t => cost t Fin.elim0) := by
          apply Finset.sum_le_sum
          intro t ht
          have htP := hSP ht
          simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at htP
          omega
    have hU_sum : S.sum (fun t => cost t Fin.elim0) ≤ Finset.univ.sum (fun t => cost t Fin.elim0) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    constructor <;> intro h <;> omega

noncomputable def dpStep {B a : ℕ} (E : ℕ) (c : (Fin a → Bool) → ℕ)
    (prev : St B a → ℕ) (s : St B a) : ℕ := by
  classical
  exact min (E + 1)
    (((Finset.univ : Finset (St B a)).filter (fun s' => StLe s' s)).inf'
      ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ s, stLe_refl s⟩⟩
      (fun s' => prev s' + c s'.2))

lemma dpStep_le_cap {B a : ℕ} (E : ℕ) (c : (Fin a → Bool) → ℕ) (prev : St B a → ℕ) (s : St B a) :
    dpStep E c prev s ≤ E + 1 := by
  unfold dpStep
  exact Nat.min_le_left _ _

lemma dpStep_le_of_stLe {B a : ℕ} (E : ℕ) (c : (Fin a → Bool) → ℕ) (prev : St B a → ℕ)
    {s' s : St B a} (h : StLe s' s) :
    dpStep E c prev s ≤ prev s' + c s'.2 := by
  classical
  unfold dpStep
  exact le_trans (Nat.min_le_right _ _)
    (Finset.inf'_le (f := fun x => prev x + c x.2) (Finset.mem_filter.2 ⟨Finset.mem_univ s', h⟩))

lemma dpStep_exists {B a : ℕ} (E : ℕ) (c : (Fin a → Bool) → ℕ) (prev : St B a → ℕ)
    (s : St B a) {e : ℕ} (he : e ≤ E) (h : dpStep E c prev s ≤ e) :
    ∃ s' : St B a, StLe s' s ∧ prev s' + c s'.2 ≤ e := by
  classical
  unfold dpStep at h
  have hlt : min (E + 1)
      (((Finset.univ : Finset (St B a)).filter (fun s' => StLe s' s)).inf'
        ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ s, stLe_refl s⟩⟩
        (fun s' => prev s' + c s'.2)) < E + 1 := by omega
  have hinf : (((Finset.univ : Finset (St B a)).filter (fun s' => StLe s' s)).inf'
        ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ s, stLe_refl s⟩⟩
        (fun s' => prev s' + c s'.2)) ≤ e := by
    by_contra hgt
    have hge : E + 1 ≤ (((Finset.univ : Finset (St B a)).filter (fun s' => StLe s' s)).inf'
        ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ s, stLe_refl s⟩⟩
        (fun s' => prev s' + c s'.2)) := by omega
    rw [Nat.min_eq_left hge] at h
    omega
  obtain ⟨s', hs'_mem, hs'_eq⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (St B a)).filter (fun s' => StLe s' s))
    ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ s, stLe_refl s⟩⟩
    (fun s' => prev s' + c s'.2)
  rw [Finset.mem_filter] at hs'_mem
  refine ⟨s', hs'_mem.2, ?_⟩
  omega

lemma dpStep_antitone {B a : ℕ} (E : ℕ) (c : (Fin a → Bool) → ℕ) (prev : St B a → ℕ)
    {s1 s2 : St B a} (h : StLe s1 s2) :
    dpStep E c prev s2 ≤ dpStep E c prev s1 := by
  classical
  unfold dpStep
  apply min_le_min_left
  apply Finset.le_inf'
  intro s' hs'
  rw [Finset.mem_filter] at hs'
  have hmem : s' ∈ (Finset.univ : Finset (St B a)).filter (fun x => StLe x s2) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ s', stLe_trans hs'.2 h⟩
  exact Finset.inf'_le (f := fun x => prev x + c x.2) hmem

lemma dpStep_ge_prev {B a : ℕ} (E : ℕ) (c : (Fin a → Bool) → ℕ) (prev : St B a → ℕ)
    (hanti : ∀ s1 s2 : St B a, StLe s1 s2 → prev s2 ≤ prev s1)
    (hcap : ∀ s : St B a, prev s ≤ E + 1) (s : St B a) :
    prev s ≤ dpStep E c prev s := by
  classical
  unfold dpStep
  apply le_min (hcap s)
  apply Finset.le_inf'
  intro s' hs'
  rw [Finset.mem_filter] at hs'
  exact le_trans (hanti s' s hs'.2) (Nat.le_add_right _ _)

noncomputable def dp (n a B E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ)
    (T : Finset (Fin (n + 1))) : ℕ → St B a → ℕ
  | 0, _ => 0
  | k + 1, s =>
    if h : k < n + 1 then
      if ⟨k, h⟩ ∈ T then dpStep E (cost ⟨k, h⟩) (dp n a B E cost T k) s
      else dp n a B E cost T k s
    else dp n a B E cost T k s

lemma dp_le_cap (n a B E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ)
    (T : Finset (Fin (n + 1))) (k : ℕ) (s : St B a) :
    dp n a B E cost T k s ≤ E + 1 := by
  induction k generalizing s with
  | zero => simp [dp]
  | succ k ih =>
    unfold dp
    split_ifs
    · exact dpStep_le_cap E _ _ s
    · exact ih s
    · exact ih s

lemma dp_antitone (n a B E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ)
    (T : Finset (Fin (n + 1))) (k : ℕ) {s1 s2 : St B a} (h : StLe s1 s2) :
    dp n a B E cost T k s2 ≤ dp n a B E cost T k s1 := by
  induction k generalizing s1 s2 with
  | zero => simp [dp]
  | succ k ih =>
    unfold dp
    split_ifs
    · exact dpStep_antitone E _ _ h
    · exact ih h
    · exact ih h

lemma dp_mono_k (n a B E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ)
    (T : Finset (Fin (n + 1))) (k : ℕ) (s : St B a) :
    dp n a B E cost T k s ≤ dp n a B E cost T (k + 1) s := by
  conv_rhs => unfold dp
  split_ifs
  · exact dpStep_ge_prev E _ _ (fun _ _ h => dp_antitone n a B E cost T k h)
      (dp_le_cap n a B E cost T k) s
  · exact le_rfl
  · exact le_rfl

lemma dp_iff_chain (n a B E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ)
    (T : Finset (Fin (n + 1))) :
    ∀ (k : ℕ) (hk : k ≤ n + 1) (s : St B a) (e : ℕ), e ≤ E →
      (dp n a B E cost T k s ≤ e ↔
        ∃ φ : Fin k → St B a,
          (∀ i j : Fin k, i.val ≤ j.val → StLe (φ i) (φ j)) ∧
          (∀ i : Fin k, StLe (φ i) s) ∧
          (Finset.univ.filter (fun i : Fin k => (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin (n + 1)) ∈ T)).sum
            (fun i => cost ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ (φ i).2) ≤ e) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _ s e _
    simp only [dp, Nat.zero_le, true_iff]
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | succ k ih =>
    intro hk s e he
    have hk_lt : k < n + 1 := by omega
    have hk_le : k ≤ n + 1 := by omega
    let tk : Fin (n + 1) := ⟨k, hk_lt⟩
    have hsplit_sum : ∀ (φ : Fin (k + 1) → St B a),
        (Finset.univ.filter (fun i : Fin (k + 1) => (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin (n + 1)) ∈ T)).sum
          (fun i => cost ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ (φ i).2) =
        (Finset.univ.filter (fun i : Fin k => (⟨i.val, lt_of_lt_of_le i.isLt hk_le⟩ : Fin (n + 1)) ∈ T)).sum
          (fun i => cost ⟨i.val, lt_of_lt_of_le i.isLt hk_le⟩ (φ i.castSucc).2) +
        (if tk ∈ T then cost tk (φ (Fin.last k)).2 else 0) := by
      intro φ
      have h1 : ∀ (F : Fin (k + 1) → ℕ),
          (Finset.univ.filter (fun i : Fin (k + 1) => (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin (n + 1)) ∈ T)).sum F =
          Finset.univ.sum (fun i : Fin (k + 1) => if (⟨i.val, lt_of_lt_of_le i.isLt hk⟩ : Fin (n + 1)) ∈ T then F i else 0) :=
        fun F => Finset.sum_filter _ _
      rw [h1, Fin.sum_univ_castSucc]
      congr 1
      rw [← Finset.sum_filter]
      simp only [Fin.val_castSucc]
    by_cases hmem : tk ∈ T
    · have hdp : dp n a B E cost T (k + 1) s = dpStep E (cost tk) (dp n a B E cost T k) s := by
        conv_lhs => unfold dp
        simp only [hk_lt, ↓reduceDIte]
        have hmem' : (⟨k, hk_lt⟩ : Fin (n + 1)) ∈ T := hmem
        simp only [hmem', ↓reduceIte]
        rfl
      rw [hdp]
      constructor
      · intro hle
        obtain ⟨s', hs'_le, hsum_le⟩ := dpStep_exists E (cost tk) (dp n a B E cost T k) s he hle
        have he' : e - cost tk s'.2 ≤ E := by omega
        have hprev_le : dp n a B E cost T k s' ≤ e - cost tk s'.2 := by omega
        obtain ⟨φ0, hφ0_mono, hφ0_le, hφ0_sum⟩ := (ih hk_le s' (e - cost tk s'.2) he').1 hprev_le
        let φ : Fin (k + 1) → St B a := Fin.snoc φ0 s'
        refine ⟨φ, ?_, ?_, ?_⟩
        · intro i j hij
          cases i using Fin.lastCases with
          | last =>
            have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last] at hij ⊢; omega)
            subst hj
            exact stLe_refl _
          | cast i =>
            cases j using Fin.lastCases with
            | last =>
              simp only [φ, Fin.snoc_castSucc, Fin.snoc_last]
              exact hφ0_le i
            | cast j =>
              simp only [φ, Fin.snoc_castSucc]
              exact hφ0_mono i j hij
        · intro i
          cases i using Fin.lastCases with
          | last =>
            simp only [φ, Fin.snoc_last]
            exact hs'_le
          | cast i =>
            simp only [φ, Fin.snoc_castSucc]
            exact stLe_trans (hφ0_le i) hs'_le
        · rw [hsplit_sum φ]
          simp only [hmem, ↓reduceIte, φ, Fin.snoc_castSucc, Fin.snoc_last]
          omega
      · rintro ⟨φ, hφ_mono, hφ_le, hφ_sum⟩
        rw [hsplit_sum φ] at hφ_sum
        simp only [hmem, ↓reduceIte] at hφ_sum
        let s' := φ (Fin.last k)
        have he' : e - cost tk s'.2 ≤ E := by omega
        have hprev : dp n a B E cost T k s' ≤ e - cost tk s'.2 := by
          refine (ih hk_le s' (e - cost tk s'.2) he').2 ⟨fun i => φ i.castSucc, ?_, ?_, ?_⟩
          · intro i j hij
            exact hφ_mono i.castSucc j.castSucc hij
          · intro i
            exact hφ_mono i.castSucc (Fin.last k) (by have := i.isLt; simp only [Fin.val_castSucc, Fin.val_last]; omega)
          · dsimp only [s']
            omega
        exact le_trans (dpStep_le_of_stLe E (cost tk) (dp n a B E cost T k) (hφ_le (Fin.last k))) (by dsimp only [s'] at hprev; omega)
    · have hdp : dp n a B E cost T (k + 1) s = dp n a B E cost T k s := by
        conv_lhs => unfold dp
        simp only [hk_lt, ↓reduceDIte]
        have hmem' : (⟨k, hk_lt⟩ : Fin (n + 1)) ∉ T := hmem
        simp only [hmem', ↓reduceIte]
      rw [hdp]
      constructor
      · intro hle
        obtain ⟨φ0, hφ0_mono, hφ0_le, hφ0_sum⟩ := (ih hk_le s e he).1 hle
        let φ : Fin (k + 1) → St B a := Fin.snoc φ0 s
        refine ⟨φ, ?_, ?_, ?_⟩
        · intro i j hij
          cases i using Fin.lastCases with
          | last =>
            have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last] at hij ⊢; omega)
            subst hj
            exact stLe_refl _
          | cast i =>
            cases j using Fin.lastCases with
            | last =>
              simp only [φ, Fin.snoc_castSucc, Fin.snoc_last]
              exact hφ0_le i
            | cast j =>
              simp only [φ, Fin.snoc_castSucc]
              exact hφ0_mono i j hij
        · intro i
          cases i using Fin.lastCases with
          | last =>
            simp only [φ, Fin.snoc_last]
            exact stLe_refl s
          | cast i =>
            simp only [φ, Fin.snoc_castSucc]
            exact hφ0_le i
        · rw [hsplit_sum φ]
          simp only [hmem, ↓reduceIte, Nat.add_zero, φ, Fin.snoc_castSucc]
          exact hφ0_sum
      · rintro ⟨φ, hφ_mono, hφ_le, hφ_sum⟩
        rw [hsplit_sum φ] at hφ_sum
        simp only [hmem, ↓reduceIte, Nat.add_zero] at hφ_sum
        refine (ih hk_le s e he).2 ⟨fun i => φ i.castSucc, ?_, ?_, hφ_sum⟩
        · intro i j hij
          exact hφ_mono i.castSucc j.castSucc hij
        · intro i
          exact hφ_le i.castSucc

lemma fit_iff_dp (n a B E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ)
    (T : Finset (Fin (n + 1))) (b : ℕ) (hb : b ≤ B) (e : ℕ) (he : e ≤ E) :
    Fit a n b e cost T ↔
      dp n a B E cost T (n + 1) (⟨2 ^ b - 1, lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos b) (by omega))
        (Nat.pow_le_pow_right (by omega) hb)⟩, fun _ => true) ≤ e := by
  let topB : St B a := (⟨2 ^ b - 1, lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos b) (by omega))
    (Nat.pow_le_pow_right (by omega) hb)⟩, fun _ => true)
  have htop_iff : ∀ s : St B a, StLe s topB ↔ s.1.val < 2 ^ b := by
    intro s
    have hpos := Nat.two_pow_pos b
    constructor
    · rintro (hlt | ⟨heq, _⟩)
      · dsimp only [topB] at hlt; omega
      · have := congrArg Fin.val heq; dsimp only [topB] at this; omega
    · intro hlt
      by_cases heq : s.1.val = 2 ^ b - 1
      · exact Or.inr ⟨Fin.ext heq, fun _ _ => rfl⟩
      · exact Or.inl (by dsimp only [topB]; omega)
  rw [fit_iff_chain, dp_iff_chain n a B E cost T (n + 1) le_rfl topB e he]
  have hfilt : ∀ (g : Fin (n + 1) → ℕ),
      (Finset.univ.filter (fun i : Fin (n + 1) => (⟨i.val, i.isLt⟩ : Fin (n + 1)) ∈ T)).sum g =
      T.sum g := by
    intro g
    congr 1
    ext i
    simp
  have hpow : 2 ^ b ≤ 2 ^ B := Nat.pow_le_pow_right (by omega) hb
  constructor
  · rintro ⟨φ, hmono, hsum⟩
    let ψ : Fin (n + 1) → St B a := fun t => (⟨(φ t).1.val, lt_of_lt_of_le (φ t).1.isLt hpow⟩, (φ t).2)
    refine ⟨ψ, ?_, ?_, ?_⟩
    · intro t1 t2 ht
      rcases hmono t1 t2 ht with hlt | ⟨heq, hm⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨Fin.ext (by simpa [ψ] using congrArg Fin.val heq), hm⟩
    · intro t
      rw [htop_iff]
      exact (φ t).1.isLt
    · rw [hfilt]
      exact hsum
  · rintro ⟨ψ, hmono, hle, hsum⟩
    rw [hfilt] at hsum
    let φ : Fin (n + 1) → St b a := fun t => (⟨(ψ t).1.val, (htop_iff (ψ t)).1 (hle t)⟩, (ψ t).2)
    refine ⟨φ, ?_, hsum⟩
    intro t1 t2 ht
    rcases hmono t1 t2 ht with hlt | ⟨heq, hm⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨Fin.ext (by simpa [φ] using congrArg Fin.val heq), hm⟩

lemma part1_pos (n a B E : ℕ) (cost : Fin (n + 1) → (Fin a → Bool) → ℕ) :
    ∃ S : Finset (Fin (n + 1)), S.card ≤ (E + 1) * (2 ^ B * 2 ^ a) ∧
      ∀ b ≤ B, ∀ e ≤ E, Fit a n b e cost Finset.univ ↔ Fit a n b e cost S := by
  classical
  let U := dp n a B E cost Finset.univ
  let S : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun t : Fin (n + 1) => U (t.val + 1) ≠ U t.val)
  have hdp_eq : ∀ k ≤ n + 1, dp n a B E cost S k = U k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk_lt : k < n + 1 := by omega
      have ih' := ih (by omega)
      by_cases hmem : (⟨k, hk_lt⟩ : Fin (n + 1)) ∈ S
      · funext s
        conv_lhs => unfold dp
        conv_rhs => dsimp only [U]; unfold dp
        simp only [hk_lt, hmem, Finset.mem_univ, ↓reduceDIte, ↓reduceIte, ih']
        rfl
      · have hsame : U (k + 1) = U k := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hmem
          exact hmem
        funext s
        conv_lhs => unfold dp
        simp only [hk_lt, hmem, ↓reduceDIte, ↓reduceIte, ih', ← hsame]
  have hcard_k : ∀ k ≤ n + 1,
      (Finset.univ.filter (fun t : Fin (n + 1) => t.val < k ∧ U (t.val + 1) ≠ U t.val)).card ≤
        (Finset.univ : Finset (St B a)).sum (fun s => U k s) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk_lt : k < n + 1 := by omega
      have ih' := ih (by omega)
      have hsub : (Finset.univ.filter (fun t : Fin (n + 1) => t.val < k + 1 ∧ U (t.val + 1) ≠ U t.val)) =
          if U (k + 1) ≠ U k then
            insert ⟨k, hk_lt⟩ (Finset.univ.filter (fun t : Fin (n + 1) => t.val < k ∧ U (t.val + 1) ≠ U t.val))
          else
            Finset.univ.filter (fun t : Fin (n + 1) => t.val < k ∧ U (t.val + 1) ≠ U t.val) := by
        split_ifs with hne
        · ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          constructor
          · rintro ⟨hlt, hne_t⟩
            by_cases heq : t.val = k
            · exact Or.inl heq
            · exact Or.inr ⟨by omega, hne_t⟩
          · rintro (rfl | ⟨hlt, hne_t⟩)
            · exact ⟨by omega, hne⟩
            · exact ⟨by omega, hne_t⟩
        · ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hne_t⟩
            refine ⟨?_, hne_t⟩
            by_contra hge
            have heq : t.val = k := by omega
            rw [heq] at hne_t
            exact hne hne_t
          · rintro ⟨hlt, hne_t⟩
            exact ⟨by omega, hne_t⟩
      rw [hsub]
      split_ifs with hne
      · have hnotmem : (⟨k, hk_lt⟩ : Fin (n + 1)) ∉
            Finset.univ.filter (fun t : Fin (n + 1) => t.val < k ∧ U (t.val + 1) ≠ U t.val) := by
          simp
        rw [Finset.card_insert_of_notMem hnotmem]
        have hex : ∃ s0 : St B a, U k s0 < U (k + 1) s0 := by
          by_contra hall
          push Not at hall
          apply hne
          funext s
          exact le_antisymm (hall s) (dp_mono_k n a B E cost Finset.univ k s)
        obtain ⟨s0, hs0⟩ := hex
        have hsum_lt : (Finset.univ : Finset (St B a)).sum (fun s => U k s) <
            (Finset.univ : Finset (St B a)).sum (fun s => U (k + 1) s) := by
          apply Finset.sum_lt_sum
          · intro s _
            exact dp_mono_k n a B E cost Finset.univ k s
          · exact ⟨s0, Finset.mem_univ s0, hs0⟩
        omega
      · exact le_trans ih' (Finset.sum_le_sum fun s _ => dp_mono_k n a B E cost Finset.univ k s)
  have hS_card : S.card ≤ (E + 1) * (2 ^ B * 2 ^ a) := by
    have h1 := hcard_k (n + 1) le_rfl
    have hfilt_eq : Finset.univ.filter (fun t : Fin (n + 1) => t.val < n + 1 ∧ U (t.val + 1) ≠ U t.val) = S := by
      ext t
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro _
      exact t.isLt
    rw [hfilt_eq] at h1
    have h2 : (Finset.univ : Finset (St B a)).sum (fun s => U (n + 1) s) ≤
        (Finset.univ : Finset (St B a)).sum (fun _ => E + 1) :=
      Finset.sum_le_sum fun s _ => dp_le_cap n a B E cost Finset.univ (n + 1) s
    have h3 : (Finset.univ : Finset (St B a)).sum (fun _ => E + 1) = (E + 1) * (2 ^ B * 2 ^ a) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      have hcard_st : Fintype.card (St B a) = 2 ^ B * 2 ^ a := by
        unfold St
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      rw [hcard_st, mul_comm]
    omega
  refine ⟨S, hS_card, fun b hb e he => ?_⟩
  rw [fit_iff_dp n a B E cost Finset.univ b hb e he, fit_iff_dp n a B E cost S b hb e he]
  rw [hdp_eq (n + 1) le_rfl]

def wordVal {a : ℕ} (w : Fin a → Bool) : ℕ :=
  Finset.univ.sum fun i : Fin a => if w i then 2 ^ i.val else 0

def valWord (a k : ℕ) : Fin a → Bool :=
  fun i => k.testBit i.val

lemma wordVal_lt {a : ℕ} (w : Fin a → Bool) : wordVal w < 2 ^ a := by
  induction a with
  | zero => simp [wordVal]
  | succ a ih =>
    unfold wordVal
    rw [Fin.sum_univ_castSucc]
    have h1 : (∑ x : Fin a, if w x.castSucc then 2 ^ (x.castSucc : ℕ) else 0) < 2 ^ a :=
      ih (fun x => w x.castSucc)
    simp only [Fin.val_last]
    rw [pow_succ]
    split_ifs <;> omega

lemma wordVal_mono {a : ℕ} {w1 w2 : Fin a → Bool} (h : ∀ i, w1 i = true → w2 i = true) :
    wordVal w1 ≤ wordVal w2 := by
  unfold wordVal
  apply Finset.sum_le_sum
  intro i _
  cases h1 : w1 i
  · simp
  · rw [h i h1]

lemma wordVal_valWord (a k : ℕ) (hk : k < 2 ^ a) : wordVal (valWord a k) = k := by
  induction a generalizing k with
  | zero =>
    simp only [pow_zero] at hk
    simp [wordVal, show k = 0 by omega]
  | succ a ih =>
    unfold wordVal
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    have hmod_lt : k % 2 ^ a < 2 ^ a := Nat.mod_lt k (Nat.two_pow_pos a)
    have hbits : ∀ x : Fin a, valWord (a + 1) k x.castSucc = valWord a (k % 2 ^ a) x := by
      intro x
      simp only [valWord, Fin.val_castSucc]
      rw [Nat.testBit_mod_two_pow, decide_eq_true x.isLt, Bool.true_and]
    have hsum_eq : (∑ x : Fin a, if valWord (a + 1) k x.castSucc then 2 ^ x.val else 0) = k % 2 ^ a := by
      calc (∑ x : Fin a, if valWord (a + 1) k x.castSucc then 2 ^ x.val else 0)
          = (∑ x : Fin a, if valWord a (k % 2 ^ a) x then 2 ^ x.val else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [hbits x]
        _ = k % 2 ^ a := ih (k % 2 ^ a) hmod_lt
    rw [hsum_eq]
    have hdiv : k / 2 ^ a < 2 := Nat.div_lt_of_lt_mul (by simpa [pow_succ, mul_comm] using hk)
    have h01 : k / 2 ^ a = 0 ∨ k / 2 ^ a = 1 := by
      match hq : k / 2 ^ a with
      | 0 => exact Or.inl rfl
      | 1 => exact Or.inr rfl
      | q + 2 => exfalso; rw [hq] at hdiv; exact Nat.not_lt_of_ge (Nat.le_add_left 2 q) hdiv
    have htop : valWord (a + 1) k (Fin.last a) = decide (k / 2 ^ a = 1) := by
      simp only [valWord, Fin.val_last, Nat.testBit, Nat.shiftRight_eq_div_pow]
      rcases h01 with h0 | h1 <;> simp [*]
    rw [htop]
    have hdiv_mod := (Nat.div_add_mod k (2 ^ a)).symm
    rcases h01 with h0 | h1
    · rw [h0] at hdiv_mod ⊢
      simp at hdiv_mod ⊢
      omega
    · rw [h1] at hdiv_mod ⊢
      simp at hdiv_mod ⊢
      omega

lemma valWord_wordVal {a : ℕ} (w : Fin a → Bool) : valWord a (wordVal w) = w := by
  induction a with
  | zero => funext i; exact i.elim0
  | succ a ih =>
    let w' : Fin a → Bool := fun x => w x.castSucc
    have hdecomp : wordVal w = wordVal w' + if w (Fin.last a) then 2 ^ a else 0 := by
      unfold wordVal
      rw [Fin.sum_univ_castSucc]
      rfl
    have hw'_lt : wordVal w' < 2 ^ a := wordVal_lt w'
    funext i
    cases i using Fin.lastCases with
    | last =>
      dsimp only [valWord]
      rw [Fin.val_last, hdecomp, Nat.testBit, Nat.shiftRight_eq_div_pow]
      cases hlast : w (Fin.last a)
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        rw [Nat.div_eq_of_lt hw'_lt]
        rfl
      · simp only [↓reduceIte]
        have hq : (wordVal w' + 2 ^ a) / 2 ^ a = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos a), Nat.div_eq_of_lt hw'_lt]
        rw [hq]
        rfl
    | cast i =>
      dsimp only [valWord]
      rw [Fin.val_castSucc, hdecomp]
      have hmod : (wordVal w' + if w (Fin.last a) then 2 ^ a else 0) % 2 ^ a = wordVal w' := by
        split_ifs
        · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hw'_lt]
        · rw [Nat.add_zero, Nat.mod_eq_of_lt hw'_lt]
      have htb : (wordVal w' + if w (Fin.last a) then 2 ^ a else 0).testBit i.val =
          ((wordVal w' + if w (Fin.last a) then 2 ^ a else 0) % 2 ^ a).testBit i.val := by
        rw [Nat.testBit_mod_two_pow, decide_eq_true i.isLt, Bool.true_and]
      rw [htb, hmod]
      exact congrFun (ih w') i

lemma valWord_zero (a : ℕ) : valWord a 0 = fun _ => false := by
  funext i
  simp [valWord]

lemma valWord_max (a : ℕ) : valWord a (2 ^ a - 1) = fun _ => true := by
  funext i
  dsimp only [valWord]
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true i.isLt

def stateIdx {b a : ℕ} (s : St b a) : ℕ :=
  s.1.val * 2 ^ a + wordVal s.2

lemma stateIdx_lt {b a : ℕ} (s : St b a) : stateIdx s < 2 ^ b * 2 ^ a := by
  unfold stateIdx
  have h1 := s.1.isLt
  have h2 := wordVal_lt s.2
  have h3 : (s.1.val + 1) * 2 ^ a ≤ 2 ^ b * 2 ^ a := Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, Nat.one_mul] at h3
  omega

lemma stateIdx_mono {b a : ℕ} {s1 s2 : St b a} (h : StLe s1 s2) :
    stateIdx s1 ≤ stateIdx s2 := by
  unfold stateIdx
  rcases h with hlt | ⟨heq, hm⟩
  · have h1 := wordVal_lt s1.2
    have h2 : (s1.1.val + 1) * 2 ^ a ≤ s2.1.val * 2 ^ a := Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega
  · rw [heq]
    exact Nat.add_le_add_left (wordVal_mono hm) _

lemma part2_zero (b e n : ℕ) (hn : n + 1 = (e + 1) * 1) :
    ∃ banned : Fin (n + 1) → (Fin 0 → Bool),
      let cost := fun t (word : Fin 0 → Bool) => if word = banned t then 1 else 0
      (¬ Fit 0 n b e cost Finset.univ) ∧
        ∀ S : Finset (Fin (n + 1)), S ≠ Finset.univ → Fit 0 n b e cost S := by
  refine ⟨fun _ => Fin.elim0, ?_, ?_⟩
  · rw [fit_zero_iff]
    simp only [↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  · intro S hS
    rw [fit_zero_iff]
    simp only [↓reduceIte, Finset.sum_const, smul_eq_mul, mul_one]
    have hlt : S.card < (Finset.univ : Finset (Fin (n + 1))).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ S, hS⟩)
    simp only [Finset.card_univ, Fintype.card_fin] at hlt
    omega

lemma part2_pos (a b e n : ℕ) (ha : 0 < a) (hn : n + 1 = (e + 1) * (2 ^ b * 2 ^ a)) :
    ∃ banned : Fin (n + 1) → (Fin a → Bool),
      let cost := fun t (word : Fin a → Bool) => if word = banned t then 1 else 0
      (¬ Fit a n b e cost Finset.univ) ∧
        ∀ S : Finset (Fin (n + 1)), S ≠ Finset.univ → Fit a n b e cost S := by
  classical
  let M := 2 ^ b * 2 ^ a
  have hM_pos : 0 < M := Nat.mul_pos (Nat.two_pow_pos b) (Nat.two_pow_pos a)
  have h2a_ge2 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
  let banned : Fin (n + 1) → (Fin a → Bool) := fun t => valWord a ((t.val / (e + 1)) % 2 ^ a)
  let cost : Fin (n + 1) → (Fin a → Bool) → ℕ := fun t word => if word = banned t then 1 else 0
  refine ⟨banned, ?_, ?_⟩
  · rw [fit_iff_chain]
    rintro ⟨φ, hmono, hsum⟩
    have hblock_good : ∀ m < M, ∃ t : Fin (n + 1), t.val / (e + 1) = m ∧ stateIdx (φ t) ≠ m := by
      intro m hm
      by_contra hnone
      push Not at hnone
      let B : Finset (Fin (n + 1)) := Finset.univ.filter (fun t => t.val / (e + 1) = m)
      have hB_card : B.card = e + 1 := by
        let f : Fin (e + 1) → Fin (n + 1) := fun j =>
          ⟨m * (e + 1) + j.val, by
            have hj := j.isLt
            have hmul : (m + 1) * (e + 1) ≤ M * (e + 1) := Nat.mul_le_mul_right _ hm
            rw [Nat.add_mul, Nat.one_mul] at hmul
            have hMeq : M * (e + 1) = n + 1 := by rw [hn, mul_comm]
            omega⟩
        have hB_eq : B = Finset.univ.image f := by
          ext t
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Fin.ext_iff]
          constructor
          · intro hdiv
            refine ⟨⟨t.val % (e + 1), Nat.mod_lt _ (by omega)⟩, ?_⟩
            dsimp only [f]
            have := (Nat.div_add_mod t.val (e + 1)).symm
            rw [hdiv, mul_comm] at this
            omega
          · rintro ⟨j, hj⟩
            rw [← hj]
            dsimp only [f]
            rw [mul_comm m (e + 1), Nat.mul_add_div (by omega), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
        rw [hB_eq, Finset.card_image_of_injective]
        · simp
        · intro j1 j2 hj
          apply Fin.ext
          have := congrArg Fin.val hj
          dsimp only [f] at this
          omega
      have hB_sum : B.sum (fun t => cost t (φ t).2) = e + 1 := by
        calc B.sum (fun t => cost t (φ t).2)
            = B.sum (fun _ => 1) := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [Finset.mem_filter] at ht
              have hidx := hnone t ht.2
              have hword : (φ t).2 = banned t := by
                dsimp only [banned]
                rw [ht.2, ← hidx]
                unfold stateIdx
                have hmod : ((φ t).1.val * 2 ^ a + wordVal (φ t).2) % 2 ^ a = wordVal (φ t).2 := by
                  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (wordVal_lt _)]
                rw [hmod, valWord_wordVal]
              simp [cost, hword]
          _ = B.card := by simp
          _ = e + 1 := hB_card
      have hle : B.sum (fun t => cost t (φ t).2) ≤ Finset.univ.sum (fun t => cost t (φ t).2) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ B)
      have hsum' : Finset.univ.sum (fun t => cost t (φ t).2) ≤ e := hsum
      omega
    have hind : ∀ m < M, ∃ t : Fin (n + 1), t.val / (e + 1) = m ∧ m + 1 ≤ stateIdx (φ t) := by
      intro m
      induction m with
      | zero =>
        intro hm
        obtain ⟨t, ht_div, ht_ne⟩ := hblock_good 0 hm
        exact ⟨t, ht_div, by omega⟩
      | succ m ih =>
        intro hm
        obtain ⟨t1, ht1_div, ht1_ge⟩ := ih (by omega)
        obtain ⟨t2, ht2_div, ht2_ne⟩ := hblock_good (m + 1) hm
        have ht12 : t1.val ≤ t2.val := by
          have h1 : t1.val < (m + 1) * (e + 1) := by
            have := (Nat.div_add_mod t1.val (e + 1)).symm
            have hmod := Nat.mod_lt t1.val (show 0 < e + 1 by omega)
            rw [ht1_div, mul_comm] at this
            rw [Nat.add_mul, Nat.one_mul]
            omega
          have h2 : (m + 1) * (e + 1) ≤ t2.val := by
            have := (Nat.div_add_mod t2.val (e + 1)).symm
            rw [ht2_div, mul_comm] at this
            omega
          omega
        have hle := stateIdx_mono (hmono t1 t2 ht12)
        exact ⟨t2, ht2_div, by omega⟩
    obtain ⟨t, _, hge⟩ := hind (M - 1) (by omega)
    have hlt := stateIdx_lt (φ t)
    dsimp only [M] at hge hlt
    omega
  · intro S hS
    rw [fit_iff_chain]
    have hex_miss : ∃ t0 : Fin (n + 1), t0 ∉ S := by
      by_contra hall
      push Not at hall
      apply hS
      ext t
      exact ⟨fun _ => Finset.mem_univ t, fun _ => hall t⟩
    obtain ⟨t0, ht0_nS⟩ := hex_miss
    let m0 := t0.val / (e + 1)
    have hm0_lt : m0 < M := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq t0.isLt hn)
    let r0 := m0 / 2 ^ a
    let k0 := m0 % 2 ^ a
    have hr0_lt : r0 < 2 ^ b := Nat.div_lt_of_lt_mul (by simpa only [M, mul_comm] using hm0_lt)
    have hk0_lt : k0 < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos a)
    let w0 : Fin a → Bool := valWord a k0
    let wFalse : Fin a → Bool := fun _ => false
    let wTrue : Fin a → Bool := fun _ => true
    let phiBlock : (m : ℕ) → m < M → St b a := fun m hm =>
      let r := m / 2 ^ a
      let k := m % 2 ^ a
      have hr : r < 2 ^ b := Nat.div_lt_of_lt_mul (by simpa only [M, mul_comm] using hm)
      if hlt : r < r0 then
        if hk : k < 2 ^ a - 1 then (⟨r, hr⟩, wTrue)
        else (⟨r + 1, by omega⟩, wFalse)
      else if heq : r = r0 then
        (⟨r0, hr0_lt⟩, w0)
      else
        if hk : k = 0 then (⟨r - 1, Nat.lt_of_le_of_lt (Nat.sub_le r 1) hr⟩, wTrue)
        else (⟨r, hr⟩, wFalse)
    have hphi_succ : ∀ (m : ℕ) (hm : m + 1 < M), StLe (phiBlock m (by omega)) (phiBlock (m + 1) hm) := by
      intro m hm
      have hpos := Nat.two_pow_pos a
      set r := m / 2 ^ a
      set k := m % 2 ^ a
      have hr_def : m / 2 ^ a = r := rfl
      have hk_def : m % 2 ^ a = k := rfl
      have hk_lt : k < 2 ^ a := Nat.mod_lt m hpos
      have hm_eq : m = 2 ^ a * r + k := (Nat.div_add_mod m (2 ^ a)).symm
      by_cases hk_last : k = 2 ^ a - 1
      · have hr' : (m + 1) / 2 ^ a = r + 1 := by
          have hm1 : m + 1 = 2 ^ a * (r + 1) := by rw [hm_eq, hk_last, mul_add, mul_one]; omega
          rw [hm1, Nat.mul_div_right _ hpos]
        have hk' : (m + 1) % 2 ^ a = 0 := by
          have hm1 : m + 1 = 2 ^ a * (r + 1) := by rw [hm_eq, hk_last, mul_add, mul_one]; omega
          rw [hm1, Nat.mul_mod_right]
        dsimp only [phiBlock]
        simp only [hr_def, hk_def, hr', hk']
        have hk_not_lt : ¬ k < 2 ^ a - 1 := by omega
        have hk0_lt' : 0 < 2 ^ a - 1 := by omega
        by_cases h1 : r < r0
        · by_cases h2 : r + 1 < r0
          · simp only [h1, hk_not_lt, h2, hk0_lt', ↓reduceDIte]
            exact Or.inr ⟨rfl, fun _ h => by simp [wFalse] at h⟩
          · have h2eq : r + 1 = r0 := by omega
            simp only [h1, hk_not_lt, h2eq, Nat.lt_irrefl, ↓reduceDIte]
            exact Or.inr ⟨rfl, fun _ h => by simp [wFalse] at h⟩
        · by_cases h1eq : r = r0
          · have h2lt : ¬ r0 + 1 < r0 := by omega
            have h2eq : ¬ r0 + 1 = r0 := by omega
            simp only [h1eq, Nat.lt_irrefl, h2lt, h2eq, ↓reduceDIte]
            exact Or.inr ⟨rfl, fun _ _ => rfl⟩
          · have h2lt : ¬ r + 1 < r0 := by omega
            have h2eq : ¬ r + 1 = r0 := by omega
            have hk_ne0 : ¬ k = 0 := by omega
            simp only [h1, h1eq, hk_ne0, h2lt, h2eq, ↓reduceDIte]
            exact Or.inr ⟨rfl, fun _ h => by simp [wFalse] at h⟩
      · have hr' : (m + 1) / 2 ^ a = r := by
          have hm1 : m + 1 = 2 ^ a * r + (k + 1) := by omega
          rw [hm1, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega), Nat.add_zero]
        have hk' : (m + 1) % 2 ^ a = k + 1 := by
          have hm1 : m + 1 = 2 ^ a * r + (k + 1) := by omega
          rw [hm1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        dsimp only [phiBlock]
        simp only [hr_def, hk_def, hr', hk']
        have hk_lt1 : k < 2 ^ a - 1 := by omega
        have hk1_ne0 : ¬ k + 1 = 0 := by omega
        by_cases h1 : r < r0
        · by_cases h2 : k + 1 < 2 ^ a - 1
          · simp only [h1, hk_lt1, h2, ↓reduceDIte]
            exact stLe_refl _
          · simp only [h1, hk_lt1, h2, ↓reduceDIte]
            exact Or.inl (by dsimp; omega)
        · by_cases h1eq : r = r0
          · simp only [h1eq, Nat.lt_irrefl, ↓reduceDIte]
            exact stLe_refl _
          · by_cases h0 : k = 0
            · simp only [h1, h1eq, h0, ↓reduceDIte]
              have hr_pos : 0 < r :=
                Nat.lt_of_le_of_lt (Nat.zero_le r0) (Nat.lt_of_le_of_ne (Nat.not_lt.1 h1) (Ne.symm h1eq))
              exact Or.inl (Nat.sub_lt hr_pos Nat.one_pos)
            · simp only [h1, h1eq, h0, hk1_ne0, ↓reduceDIte]
              exact stLe_refl _
    have hphi_mono_m : ∀ (m1 m2 : ℕ) (h1 : m1 < M) (h2 : m2 < M), m1 ≤ m2 →
        StLe (phiBlock m1 h1) (phiBlock m2 h2) := by
      intro m1 m2 h1 h2 hle
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      induction d with
      | zero => exact stLe_refl _
      | succ d ih =>
        exact stLe_trans (ih (by omega) (by omega)) (hphi_succ (m1 + d) h2)
    let φ : Fin (n + 1) → St b a := fun t =>
      phiBlock (t.val / (e + 1)) (Nat.div_lt_of_lt_mul (lt_of_lt_of_eq t.isLt hn))
    have hφ_mono : ∀ t1 t2 : Fin (n + 1), t1.val ≤ t2.val → StLe (φ t1) (φ t2) :=
      fun t1 t2 ht => hphi_mono_m _ _ (Nat.div_lt_of_lt_mul (lt_of_lt_of_eq t1.isLt hn))
        (Nat.div_lt_of_lt_mul (lt_of_lt_of_eq t2.isLt hn)) (Nat.div_le_div_right ht)
    refine ⟨φ, hφ_mono, ?_⟩
    let B0 : Finset (Fin (n + 1)) := Finset.univ.filter (fun t => t.val / (e + 1) = m0)
    have hcost_zero : ∀ t : Fin (n + 1), t ∉ B0 → cost t (φ t).2 = 0 := by
      intro t ht
      simp only [B0, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have hne_word : (φ t).2 ≠ banned t := by
        set m := t.val / (e + 1)
        set r := m / 2 ^ a
        set k := m % 2 ^ a
        have hm_def : t.val / (e + 1) = m := rfl
        have hr_def : m / 2 ^ a = r := rfl
        have hk_def : m % 2 ^ a = k := rfl
        have hk_lt : k < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos a)
        have hban : banned t = valWord a k := rfl
        rw [hban]
        dsimp only [φ, phiBlock]
        simp only [hm_def, hr_def, hk_def]
        split_ifs with hlt hk heq hk0 <;> dsimp only
        · intro heqw
          have := congrArg wordVal heqw
          rw [wordVal_valWord a k hk_lt] at this
          have hmax : wordVal wTrue = 2 ^ a - 1 := by
            have := wordVal_valWord a (2 ^ a - 1) (Nat.sub_lt (Nat.two_pow_pos a) (by omega))
            rw [valWord_max] at this
            exact this
          rw [hmax] at this
          omega
        · intro heqw
          have := congrArg wordVal heqw
          rw [wordVal_valWord a k hk_lt] at this
          have hzero : wordVal wFalse = 0 := by
            simp [wordVal, wFalse]
          rw [hzero] at this
          omega
        · intro heqw
          have := congrArg wordVal heqw
          dsimp only [w0] at this
          rw [wordVal_valWord a k0 hk0_lt, wordVal_valWord a k hk_lt] at this
          have h1 := (Nat.div_add_mod m (2 ^ a)).symm
          have h2 := (Nat.div_add_mod m0 (2 ^ a)).symm
          have hm1 : r * 2 ^ a + k = m := by rw [mul_comm]; exact h1.symm
          have hm2 : r0 * 2 ^ a + k0 = m0 := by rw [mul_comm]; exact h2.symm
          rw [heq, ← this] at hm1
          exact ht (hm1.symm.trans hm2)
        · intro heqw
          have := congrArg wordVal heqw
          rw [wordVal_valWord a k hk_lt, hk0] at this
          have hmax : wordVal wTrue = 2 ^ a - 1 := by
            have := wordVal_valWord a (2 ^ a - 1) (Nat.sub_lt (Nat.two_pow_pos a) (by omega))
            rw [valWord_max] at this
            exact this
          rw [hmax] at this
          omega
        · intro heqw
          have := congrArg wordVal heqw
          rw [wordVal_valWord a k hk_lt] at this
          have hzero : wordVal wFalse = 0 := by
            simp [wordVal, wFalse]
          rw [hzero] at this
          omega
      simp [cost, hne_word]
    have hB0_card : B0.card = e + 1 := by
      let f : Fin (e + 1) → Fin (n + 1) := fun j =>
        ⟨m0 * (e + 1) + j.val, by
          have hj := j.isLt
          have hmul : (m0 + 1) * (e + 1) ≤ M * (e + 1) := Nat.mul_le_mul_right _ hm0_lt
          rw [Nat.add_mul, Nat.one_mul] at hmul
          have hMeq : M * (e + 1) = n + 1 := by rw [hn, mul_comm]
          omega⟩
      have hB_eq : B0 = Finset.univ.image f := by
        ext t
        simp only [B0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Fin.ext_iff]
        constructor
        · intro hdiv
          refine ⟨⟨t.val % (e + 1), Nat.mod_lt _ (by omega)⟩, ?_⟩
          dsimp only [f]
          have := (Nat.div_add_mod t.val (e + 1)).symm
          rw [hdiv, mul_comm] at this
          omega
        · rintro ⟨j, hj⟩
          rw [← hj]
          dsimp only [f]
          rw [mul_comm m0 (e + 1), Nat.mul_add_div (by omega), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
      rw [hB_eq, Finset.card_image_of_injective]
      · simp
      · intro j1 j2 hj
        apply Fin.ext
        have := congrArg Fin.val hj
        dsimp only [f] at this
        omega
    have ht0_B0 : t0 ∈ B0 := by simp [B0, m0]
    have hsum_le : S.sum (fun t => cost t (φ t).2) ≤ (B0.erase t0).sum (fun _ => 1) := by
      calc S.sum (fun t => cost t (φ t).2)
          = (S ∩ B0).sum (fun t => cost t (φ t).2) := by
            symm
            apply Finset.sum_subset Finset.inter_subset_left
            intro t htS hnot
            have htB : t ∉ B0 := fun hb => hnot (Finset.mem_inter.2 ⟨htS, hb⟩)
            exact hcost_zero t htB
        _ ≤ (B0.erase t0).sum (fun t => cost t (φ t).2) := by
            apply Finset.sum_le_sum_of_subset
            intro t ht
            rw [Finset.mem_inter] at ht
            rw [Finset.mem_erase]
            exact ⟨fun heq => ht0_nS (heq ▸ ht.1), ht.2⟩
        _ ≤ (B0.erase t0).sum (fun _ => 1) := by
            apply Finset.sum_le_sum
            intro t _
            dsimp only [cost]
            split_ifs <;> omega
    have herase_card : (B0.erase t0).card = e := by
      rw [Finset.card_erase_of_mem ht0_B0, hB0_card]
      omega
    simp only [Finset.sum_const, herase_card, smul_eq_mul, mul_one] at hsum_le
    exact hsum_le

end PEqualNP.Outside.L_lib_1359_aux

theorem PEqualNP.Outside.L_lib_1359 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let fit := fun (a n b e : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat)
    (S : Finset (Fin (n+1))) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
    S.sum (fun t => cost t (fun i => (C.wires
      (List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false,true])).getD (tap i) false)) ≤ e
let scale := fun (a b : Nat) => if a = 0 then 1 else 2^b * 2^a
(∀ (n a B E : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat),
  ∃ S : Finset (Fin (n+1)), S.card ≤ (E+1)*scale a B ∧
    ∀ b ≤ B, ∀ e ≤ E, fit a n b e cost Finset.univ ↔ fit a n b e cost S) ∧
∀ (a b e n : Nat), n+1 = (e+1)*scale a b →
  ∃ banned : Fin (n+1) → (Fin a → Bool),
    let cost := fun t (word : Fin a → Bool) => if word = banned t then 1 else 0
    (¬ fit a n b e cost Finset.univ) ∧
      ∀ S : Finset (Fin (n+1)), S ≠ Finset.univ → fit a n b e cost S) := by
  intro fit scale
  have hinp : ∀ (n : ℕ) (t : Fin (n + 1)),
      (List.ofFn (fun j : Fin n => @decide (j.val < t.val) (Classical.propDecidable _)) ++ [false, true]) =
      PEqualNP.Outside.L_lib_1359_aux.prefixInp n t := by
    intro n t
    unfold PEqualNP.Outside.L_lib_1359_aux.prefixInp
    congr 1
    apply List.ext_getElem (by simp)
    intro j hj _
    simp only [List.getElem_ofFn]
    exact congrArg (@decide _) (Subsingleton.elim _ _)
  have hfit_eq : ∀ a n b e cost1 cost2 S, (∀ t w, cost1 t w = cost2 t w) →
      (fit a n b e cost1 S ↔ PEqualNP.Outside.L_lib_1359_aux.Fit a n b e cost2 S) := by
    intro a n b e cost1 cost2 S hceq
    have hcfun : cost1 = cost2 := funext fun t => funext fun w => hceq t w
    subst hcfun
    dsimp only [fit, PEqualNP.Outside.L_lib_1359_aux.Fit]
    simp only [hinp]
  have hiff_cost : ∀ (a n b e : ℕ) (banned : Fin (n + 1) → (Fin a → Bool)) (S : Finset (Fin (n + 1))),
      fit a n b e (fun t word => @ite ℕ (word = banned t) (Classical.propDecidable _) 1 0) S ↔
      PEqualNP.Outside.L_lib_1359_aux.Fit a n b e (fun t word => if word = banned t then 1 else 0) S := by
    intro a n b e banned S
    have hceq : (fun t (word : Fin a → Bool) => @ite ℕ (word = banned t) (Classical.propDecidable _) 1 0) =
        (fun t (word : Fin a → Bool) => if word = banned t then 1 else 0) := by
      funext t w
      by_cases heq : w = banned t <;> simp [heq]
    rw [hceq]
    dsimp only [fit, PEqualNP.Outside.L_lib_1359_aux.Fit]
    simp only [hinp]
  constructor
  · intro n a B E cost
    by_cases ha : a = 0
    · subst ha
      obtain ⟨S, hcard, hiff⟩ := PEqualNP.Outside.L_lib_1359_aux.part1_zero n B E cost
      refine ⟨S, by simpa only [scale, ↓reduceIte] using hcard, fun b hb e he => ?_⟩
      rw [hfit_eq 0 n b e cost cost Finset.univ (fun _ _ => rfl),
        hfit_eq 0 n b e cost cost S (fun _ _ => rfl)]
      exact hiff b hb e he
    · obtain ⟨S, hcard, hiff⟩ := PEqualNP.Outside.L_lib_1359_aux.part1_pos n a B E cost
      refine ⟨S, by simpa only [scale, ha, ↓reduceIte] using hcard, fun b hb e he => ?_⟩
      rw [hfit_eq a n b e cost cost Finset.univ (fun _ _ => rfl),
        hfit_eq a n b e cost cost S (fun _ _ => rfl)]
      exact hiff b hb e he
  · intro a b e n hn
    by_cases ha : a = 0
    · subst ha
      have hn' : n + 1 = (e + 1) * 1 := by simpa only [scale, ↓reduceIte] using hn
      obtain ⟨banned, hnot, hall⟩ := PEqualNP.Outside.L_lib_1359_aux.part2_zero b e n hn'
      refine ⟨banned, ?_, ?_⟩
      · intro h
        exact hnot ((hiff_cost 0 n b e banned Finset.univ).1 h)
      · intro S hS
        exact (hiff_cost 0 n b e banned S).2 (hall S hS)
    · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
      have hn' : n + 1 = (e + 1) * (2 ^ b * 2 ^ a) := by simpa only [scale, ha, ↓reduceIte] using hn
      obtain ⟨banned, hnot, hall⟩ := PEqualNP.Outside.L_lib_1359_aux.part2_pos a b e n ha_pos hn'
      refine ⟨banned, ?_, ?_⟩
      · intro h
        exact hnot ((hiff_cost a n b e banned Finset.univ).1 h)
      · intro S hS
        exact (hiff_cost a n b e banned S).2 (hall S hS)
