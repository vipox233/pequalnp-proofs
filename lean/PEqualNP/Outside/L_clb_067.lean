import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_067_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

def evalWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

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
    have := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    unfold evalWires at this
    rw [this, List.length_append, List.length_singleton, List.length_cons]
    omega

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ} (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
    List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]

lemma getD_append_singleton_last {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
  simp

lemma getD_of_le {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none hi]

lemma evalWires_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (evalWires (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false) := by
  rw [evalWires_append]
  unfold evalWires
  simp only [List.foldl_cons, List.foldl_nil]
  rw [← evalWires_length gs x]
  exact getD_append_singleton_last (evalWires gs x) _ false

lemma evalWires_snoc_old (gs : List Gate) (g : Gate) (x : List Bool) {i : ℕ}
    (hi : i < x.length + gs.length) :
    (evalWires (gs ++ [g]) x).getD i false = (evalWires gs x).getD i false := by
  rw [evalWires_append]
  change (evalWires gs x ++ [g.op.eval (g.inputs.map fun k => (evalWires gs x).getD k false)]).getD i false = _
  apply getD_append_left
  rw [evalWires_length]
  exact hi

lemma gateOp_eval_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {l₁ l₂ : List Bool} (hlen : l₁.length = l₂.length)
    (hle : ∀ i (hi : i < l₁.length), l₁[i] = true → l₂[i]'(hlen ▸ hi) = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h1 b hb
    rcases List.mem_iff_getElem.mp hb with ⟨i, hi, rfl⟩
    have hi1 : i < l₁.length := hlen ▸ hi
    exact hle i hi1 (h1 l₁[i] (List.getElem_mem hi1))
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    rcases List.mem_iff_getElem.mp hb with ⟨i, hi, heq⟩
    exact ⟨l₂[i]'(hlen ▸ hi), List.getElem_mem _, hle i hi heq⟩

lemma exists_rise_between {L : ℕ} (v : Fin (L + 1) → Bool)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ L)
    (ha0 : v ⟨a, by omega⟩ = false) (hb1 : v ⟨b, by omega⟩ = true) :
    ∃ s : Fin L, a ≤ s.val ∧ s.val < b ∧ v s.castSucc = false ∧ v s.succ = true := by
  induction b with
  | zero =>
    have ha' : a = 0 := by omega
    subst ha'
    rw [ha0] at hb1
    exact Bool.noConfusion hb1
  | succ b' ih =>
    by_cases heq : a = b' + 1
    · subst heq
      rw [ha0] at hb1
      exact Bool.noConfusion hb1
    · have hab' : a ≤ b' := by omega
      cases hvb' : v ⟨b', by omega⟩
      · refine ⟨⟨b', by omega⟩, hab', by dsimp; omega, hvb', hb1⟩
      · rcases ih hab' (by omega) ha0 hvb' with ⟨s, hs1, hs2, hs3, hs4⟩
        exact ⟨s, hs1, by omega, hs3, hs4⟩

lemma card_le_of_between {L : ℕ} (A D : Finset (Fin L))
    (hbet : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁.val < a₂.val → ∃ d ∈ D, a₁.val < d.val ∧ d.val < a₂.val) :
    A.card ≤ D.card + 1 := by
  by_cases hA : A.Nonempty
  · set m := A.max' hA
    have hm : m ∈ A := Finset.max'_mem A hA
    set A' := A.erase m
    have hcardA : A'.card + 1 = A.card := Finset.card_erase_add_one hm
    have hex : ∀ a ∈ A', ∃ d ∈ D, a.val < d.val ∧ d.val < m.val := by
      intro a ha
      have hne : a ≠ m := (Finset.mem_erase.mp ha).1
      have haA : a ∈ A := Finset.mem_of_mem_erase ha
      have hle : a ≤ m := Finset.le_max' A a haA
      have hlt : a.val < m.val := lt_of_le_of_ne hle (fun h => hne (Fin.ext h))
      exact hbet a haA m hm hlt
    let f : Fin L → Fin L := fun a =>
      if h : (D.filter (fun d => a.val < d.val)).Nonempty then
        (D.filter (fun d => a.val < d.val)).min' h
      else a
    have hf_mem : ∀ a ∈ A', f a ∈ D := by
      intro a ha
      rcases hex a ha with ⟨d, hd, hlt, _⟩
      have hne : (D.filter (fun d => a.val < d.val)).Nonempty :=
        ⟨d, Finset.mem_filter.mpr ⟨hd, hlt⟩⟩
      simp only [f, hne, ↓reduceDIte]
      exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
    have hf_lt : ∀ a₁ ∈ A', ∀ a₂ ∈ A', a₁.val < a₂.val → (f a₁).val < (f a₂).val := by
      intro a₁ ha₁ a₂ ha₂ hlt
      rcases hbet a₁ (Finset.mem_of_mem_erase ha₁) a₂ (Finset.mem_of_mem_erase ha₂) hlt with
        ⟨d, hd, hd1, hd2⟩
      have hne1 : (D.filter (fun x => a₁.val < x.val)).Nonempty :=
        ⟨d, Finset.mem_filter.mpr ⟨hd, hd1⟩⟩
      rcases hex a₂ ha₂ with ⟨d₂, hd₂, hd₂1, _⟩
      have hne2 : (D.filter (fun x => a₂.val < x.val)).Nonempty :=
        ⟨d₂, Finset.mem_filter.mpr ⟨hd₂, hd₂1⟩⟩
      have h1 : (f a₁).val ≤ d.val := by
        simp only [f, hne1, ↓reduceDIte]
        exact Finset.min'_le _ d (Finset.mem_filter.mpr ⟨hd, hd1⟩)
      have h2 : a₂.val < (f a₂).val := by
        simp only [f, hne2, ↓reduceDIte]
        exact (Finset.mem_filter.mp (Finset.min'_mem _ hne2)).2
      omega
    have hf_inj : Set.InjOn f (A' : Set (Fin L)) := by
      intro a₁ ha₁ a₂ ha₂ hfeq
      by_contra hne
      have ha₁' : a₁ ∈ A' := Finset.mem_coe.mp ha₁
      have ha₂' : a₂ ∈ A' := Finset.mem_coe.mp ha₂
      have hne_val : a₁.val ≠ a₂.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne_val with hlt | hlt
      · have := hf_lt a₁ ha₁' a₂ ha₂' hlt; rw [hfeq] at this; omega
      · have := hf_lt a₂ ha₂' a₁ ha₁' hlt; rw [hfeq] at this; omega
    have hle : A'.card ≤ D.card := by
      calc A'.card = (A'.image f).card := (Finset.card_image_of_injOn hf_inj).symm
        _ ≤ D.card := Finset.card_le_card (Finset.image_subset_iff.mpr hf_mem)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

def drops {I L : ℕ} (xs : Fin (L + 1) → List Bool) (gs : List Gate) : Finset (Fin L) :=
  Finset.univ.filter (fun t : Fin L =>
    ∃ w < I + gs.length,
      (evalWires gs (xs t.castSucc)).getD w false = true ∧
      (evalWires gs (xs t.succ)).getD w false = false)

lemma markov_drops_bound {I L : ℕ} (xs : Fin (L + 1) → List Bool)
    (hlen : ∀ t : Fin (L + 1), (xs t).length = I)
    (hmono : ∀ t : Fin L, ∀ w < I,
      (xs t.castSucc).getD w false = true → (xs t.succ).getD w false = true) :
    ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) →
      (drops (I := I) xs gs).card + 1 ≤ 2 ^ notCount ⟨gs, 0⟩ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    have hemp : drops (I := I) xs [] = ∅ := by
      ext t
      simp only [drops, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_exists, List.length_nil, Nat.add_zero]
      rintro w ⟨hw, h1, h2⟩
      exact Bool.noConfusion ((hmono t w hw h1).symm.trans h2)
    rw [hemp]
    simp [notCount]
  | append_singleton gs g ih =>
    intro hfan
    have hfan_pre : ∀ g' ∈ gs, (g'.op = .and ∨ g'.op = .or ∨ g'.op = .not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_append_left _ hg')
    have hg_fan := hfan g (List.mem_append_right _ (List.mem_singleton_self g))
    have hih := ih hfan_pre
    set D := drops (I := I) xs gs
    set v : Fin (L + 1) → Bool := fun t => (evalWires (gs ++ [g]) (xs t)).getD (I + gs.length) false
    set newD : Finset (Fin L) := Finset.univ.filter (fun t : Fin L => v t.castSucc = true ∧ v t.succ = false)
    have hsplit : drops (I := I) xs (gs ++ [g]) = D ∪ newD := by
      ext t
      simp only [drops, D, newD, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        List.length_append, List.length_singleton]
      constructor
      · rintro ⟨w, hw, h1, h2⟩
        by_cases hlt : w < I + gs.length
        · left
          refine ⟨w, hlt, ?_, ?_⟩
          · rwa [evalWires_snoc_old gs g (xs t.castSucc) (by rw [hlen]; exact hlt)] at h1
          · rwa [evalWires_snoc_old gs g (xs t.succ) (by rw [hlen]; exact hlt)] at h2
        · have heq : w = I + gs.length := by omega
          subst heq
          exact Or.inr ⟨h1, h2⟩
      · rintro (⟨w, hw, h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨w, by omega, ?_, ?_⟩
          · rw [evalWires_snoc_old gs g (xs t.castSucc) (by rw [hlen]; exact hw)]; exact h1
          · rw [evalWires_snoc_old gs g (xs t.succ) (by rw [hlen]; exact hw)]; exact h2
        · exact ⟨I + gs.length, by omega, h1, h2⟩
    have hv_eq : ∀ t : Fin (L + 1),
        v t = g.op.eval (g.inputs.map fun i => (evalWires gs (xs t)).getD i false) := by
      intro t
      dsimp only [v]
      rw [← hlen t]
      exact evalWires_snoc_last gs g (xs t)
    rcases hg_fan.1 with hop | hop | hop
    · have hnc : notCount ⟨gs ++ [g], 0⟩ = notCount ⟨gs, 0⟩ := by
        unfold notCount
        simp [List.filter_append, hop]
      have hsub : newD ⊆ D := by
        intro t ht
        simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        by_contra hnd
        have hnondec : ∀ i : ℕ, (evalWires gs (xs t.castSucc)).getD i false = true →
            (evalWires gs (xs t.succ)).getD i false = true := by
          intro i hi
          by_cases hilt : i < I + gs.length
          · cases h2 : (evalWires gs (xs t.succ)).getD i false
            · exfalso
              apply hnd
              simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨i, hilt, hi, h2⟩
            · rfl
          · rw [getD_of_le _ _ (by rw [evalWires_length, hlen]; omega)] at hi
            exact Bool.noConfusion hi
        have htrue : v t.succ = true := by
          have h1 := ht.1
          rw [hv_eq] at h1 ⊢
          refine gateOp_eval_mono (Or.inl hop) (by simp) (fun idx hidx hval => ?_) h1
          simp only [List.length_map] at hidx
          simp only [List.getElem_map] at hval ⊢
          exact hnondec g.inputs[idx] hval
        rw [ht.2] at htrue
        exact Bool.noConfusion htrue
      rw [hsplit, Finset.union_eq_left.mpr hsub, hnc]
      exact hih
    · have hnc : notCount ⟨gs ++ [g], 0⟩ = notCount ⟨gs, 0⟩ := by
        unfold notCount
        simp [List.filter_append, hop]
      have hsub : newD ⊆ D := by
        intro t ht
        simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        by_contra hnd
        have hnondec : ∀ i : ℕ, (evalWires gs (xs t.castSucc)).getD i false = true →
            (evalWires gs (xs t.succ)).getD i false = true := by
          intro i hi
          by_cases hilt : i < I + gs.length
          · cases h2 : (evalWires gs (xs t.succ)).getD i false
            · exfalso
              apply hnd
              simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨i, hilt, hi, h2⟩
            · rfl
          · rw [getD_of_le _ _ (by rw [evalWires_length, hlen]; omega)] at hi
            exact Bool.noConfusion hi
        have htrue : v t.succ = true := by
          have h1 := ht.1
          rw [hv_eq] at h1 ⊢
          refine gateOp_eval_mono (Or.inr hop) (by simp) (fun idx hidx hval => ?_) h1
          simp only [List.length_map] at hidx
          simp only [List.getElem_map] at hval ⊢
          exact hnondec g.inputs[idx] hval
        rw [ht.2] at htrue
        exact Bool.noConfusion htrue
      rw [hsplit, Finset.union_eq_left.mpr hsub, hnc]
      exact hih
    · have hnc : notCount ⟨gs ++ [g], 0⟩ = notCount ⟨gs, 0⟩ + 1 := by
        unfold notCount
        simp [List.filter_append, hop]
      set A := newD \ D
      have hbet : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁.val < a₂.val → ∃ d ∈ D, a₁.val < d.val ∧ d.val < a₂.val := by
        intro a₁ ha₁ a₂ ha₂ hlt
        have ha₁' := Finset.mem_filter.mp (Finset.mem_sdiff.mp ha₁).1
        have ha₂' := Finset.mem_filter.mp (Finset.mem_sdiff.mp ha₂).1
        rcases exists_rise_between v (a := a₁.val + 1) (b := a₂.val) (by omega) (by omega)
            ha₁'.2.2 ha₂'.2.1 with ⟨s, hs1, hs2, hsf, hst⟩
        refine ⟨s, ?_, by omega, hs2⟩
        rw [hv_eq, hop] at hsf hst
        cases hin : g.inputs with
        | nil =>
          simp [hin, GateOp.eval] at hsf
        | cons w0 _ =>
          simp only [hin, List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_false',
            Bool.not_eq_true'] at hsf hst
          have hw0_lt : w0 < I + gs.length := by
            by_contra hge
            rw [getD_of_le _ _ (by rw [evalWires_length, hlen]; omega)] at hsf
            exact Bool.noConfusion hsf
          simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w0, hw0_lt, hsf, hst⟩
      have hA_le : A.card ≤ D.card + 1 := card_le_of_between A D hbet
      have hunion : D ∪ newD = D ∪ A := by
        ext x; simp only [A, Finset.mem_union, Finset.mem_sdiff]; tauto
      have hcard_u : (D ∪ newD).card ≤ D.card + A.card := by
        rw [hunion]; exact Finset.card_union_le D A
      rw [hsplit, hnc, Nat.pow_succ]
      omega

lemma exists_bit_drop_of_lt {a b : ℕ} (h : a < b) :
    ∃ j : ℕ, b.testBit j = true ∧ a.testBit j = false := by
  by_contra hall
  push Not at hall
  have hle : b ≤ a := by
    have hstep : ∀ n : ℕ, ∀ x y : ℕ, x < 2 ^ n → y < 2 ^ n →
        (∀ j, x.testBit j = true → y.testBit j = true) → x ≤ y := by
      intro n
      induction n with
      | zero => intro x y hx hy _; omega
      | succ n ih =>
        intro x y hx hy hbit
        have hx' : x / 2 < 2 ^ n := by rw [Nat.pow_succ] at hx; omega
        have hy' : y / 2 < 2 ^ n := by rw [Nat.pow_succ] at hy; omega
        have hdiv : x / 2 ≤ y / 2 := by
          apply ih (x / 2) (y / 2) hx' hy'
          intro j hj
          have h1 := hbit (j + 1)
          rw [Nat.testBit_succ, Nat.testBit_succ] at h1
          exact h1 hj
        have h0 := hbit 0
        rw [Nat.testBit_zero, Nat.testBit_zero] at h0
        by_cases hmod : x % 2 = 1
        · have hy1 : y % 2 = 1 := by simpa [hmod] using h0
          omega
        · omega
    have hlt : b < 2 ^ (b + a + 1) := lt_trans (by omega : b < b + a + 1) Nat.lt_two_pow_self
    have hlt2 : a < 2 ^ (b + a + 1) := lt_trans (by omega : a < b + a + 1) Nat.lt_two_pow_self
    apply hstep (b + a + 1) b a hlt hlt2
    intro j hj
    cases hja : a.testBit j
    · exact absurd hja (hall j hj)
    · rfl
  omega

lemma flatten_list_mono :
    ∀ (l₁ l₂ : List (List Bool)) (hlen : l₁.length = l₂.length),
      (∀ i (hi : i < l₁.length), l₁[i].length = (l₂[i]'(hlen ▸ hi)).length) →
      (∀ i (hi : i < l₁.length) (j : ℕ), l₁[i].getD j false = true → (l₂[i]'(hlen ▸ hi)).getD j false = true) →
      l₁.flatten.length = l₂.flatten.length ∧
      ∀ idx, l₁.flatten.getD idx false = true → l₂.flatten.getD idx false = true := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ hlen _ _
    cases l₂ with
    | nil => exact ⟨rfl, fun _ h => h⟩
    | cons _ _ => simp at hlen
  | cons a₁ t₁ ih =>
    intro l₂ hlen heach_len heach_val
    cases l₂ with
    | nil => simp at hlen
    | cons a₂ t₂ =>
      have hlen_t : t₁.length = t₂.length := by simp at hlen; exact hlen
      have ha_len : a₁.length = a₂.length := heach_len 0 (by simp)
      have ha_val : ∀ j, a₁.getD j false = true → a₂.getD j false = true :=
        fun j hj => heach_val 0 (by simp) j hj
      have ht := ih t₂ hlen_t
        (fun i hi => heach_len (i + 1) (by simp; omega))
        (fun i hi j hj => heach_val (i + 1) (by simp; omega) j hj)
      refine ⟨by simp [ha_len, ht.1], fun idx hidx => ?_⟩
      simp only [List.flatten_cons] at hidx ⊢
      by_cases hlt : idx < a₁.length
      · rw [getD_append_left a₁ _ false hlt] at hidx
        rw [getD_append_left a₂ _ false (by omega)]
        exact ha_val idx hidx
      · have hge : a₁.length ≤ idx := by omega
        have h1 : (a₁ ++ t₁.flatten).getD idx false = t₁.flatten.getD (idx - a₁.length) false := by
          by_cases hlt2 : idx < (a₁ ++ t₁.flatten).length
          · rw [List.getD_eq_getElem _ _ hlt2, List.getElem_append_right hge,
              List.getD_eq_getElem _ _ (by rw [List.length_append] at hlt2; omega)]
          · rw [getD_of_le _ _ (by omega), getD_of_le _ _ (by rw [List.length_append] at hlt2; omega)]
        have h2 : (a₂ ++ t₂.flatten).getD idx false = t₂.flatten.getD (idx - a₂.length) false := by
          by_cases hlt2 : idx < (a₂ ++ t₂.flatten).length
          · rw [List.getD_eq_getElem _ _ hlt2, List.getElem_append_right (by omega),
              List.getD_eq_getElem _ _ (by rw [List.length_append] at hlt2; omega)]
          · rw [getD_of_le _ _ (by omega), getD_of_le _ _ (by rw [List.length_append] at hlt2; omega)]
        rw [h1] at hidx
        rw [h2, ← ha_len]
        exact ht.2 (idx - a₁.length) hidx

lemma length_flatten_ofFn (n m : ℕ) (f : Fin n → Fin m → Bool) :
    ((List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin m => f i j))).flatten).length = n * m := by
  rw [List.length_flatten]
  have hmap : (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin m => f i j))).map List.length =
      List.replicate n m := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  rw [hmap, List.sum_replicate, smul_eq_mul]

lemma testBit_foldl_or_bit (p : ℕ → Bool) (xs : List ℕ) (acc i : ℕ) :
    (xs.foldl (fun a j => a ||| ((p j).toNat <<< j)) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst j
      cases p i <;> simp
    · by_cases hle : j ≤ i
      · have hsub : 1 ≤ i - j := by omega
        have hbt : (p j).toNat.testBit (i - j) = false := by
          cases p j
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hji]
      · simp [hle, Ne.symm hji]

def patToNum {w : ℕ} (k : ℕ) (hkw : k ≤ w + 1) (pat : Fin (w + 1) → Bool) : ℕ :=
  (List.range k).foldl (fun acc r => acc ||| ((pat ⟨k - 1 - r, by omega⟩).toNat <<< r)) 0

lemma testBit_patToNum {w : ℕ} (k : ℕ) (hkw : k ≤ w + 1) (pat : Fin (w + 1) → Bool) (r : ℕ) :
    (patToNum k hkw pat).testBit r =
      if hr : r < k then pat ⟨k - 1 - r, by omega⟩ else false := by
  unfold patToNum
  have h := testBit_foldl_or_bit (fun r => if hr : r < k then pat ⟨k - 1 - r, by omega⟩ else false)
    (List.range k) 0 r
  have hfold : (List.range k).foldl (fun acc r => acc ||| ((pat ⟨k - 1 - r, by omega⟩).toNat <<< r)) 0 =
      (List.range k).foldl (fun acc r => acc |||
        ((if hr : r < k then pat ⟨k - 1 - r, by omega⟩ else false).toNat <<< r)) 0 := by
    have hgen : ∀ (L : List ℕ) (acc : ℕ), (∀ x ∈ L, x < k) →
        L.foldl (fun a r => a ||| ((pat ⟨k - 1 - r, by omega⟩).toNat <<< r)) acc =
        L.foldl (fun a r => a ||| ((if hr : r < k then pat ⟨k - 1 - r, by omega⟩ else false).toNat <<< r)) acc := by
      intro L
      induction L with
      | nil => intro _ _; rfl
      | cons x tl ih =>
        intro acc hlt
        have hx : x < k := hlt x (List.mem_cons_self ..)
        simp only [List.foldl_cons, hx, ↓reduceDIte]
        exact ih _ (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
    exact hgen (List.range k) 0 (fun x hx => List.mem_range.mp hx)
  rw [hfold, h]
  by_cases hr : r < k
  · simp [hr]
  · simp [hr]

lemma patToNum_lt {w : ℕ} (k : ℕ) (hkw : k ≤ w + 1) (pat : Fin (w + 1) → Bool) :
    patToNum k hkw pat < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro r hr
  rw [testBit_patToNum]
  have hnot : ¬ r < k := by omega
  simp [hnot]

lemma testBit_add_mul_pow2 {a q s p : ℕ} (ha : a < 2 ^ s) :
    (a + q * 2 ^ s).testBit p = if p < s then a.testBit p else q.testBit (p - s) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hp : p < s
  · simp only [hp, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ s = 2 ^ (s - p) * 2 ^ p := by rw [← Nat.pow_add]; congr 1; omega
    have hmul : q * 2 ^ s = (q * 2 ^ (s - p)) * 2 ^ p := by rw [hpow, Nat.mul_assoc]
    rw [hmul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos p)]
    have heven : (q * 2 ^ (s - p)) % 2 = 0 := by
      have h2 : 2 ∣ 2 ^ (s - p) := dvd_pow_self 2 (by omega)
      exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right h2 q)
    rw [Nat.add_mod, heven, Nat.add_zero, Nat.mod_mod]
  · simp only [hp, ↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ p = 2 ^ s * 2 ^ (p - s) := by rw [← Nat.pow_add]; congr 1; omega
    rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos s),
      Nat.div_eq_of_lt ha, Nat.zero_add]

lemma testBit_mul_pow2 (q s p : ℕ) :
    (q * 2 ^ s).testBit p = if p < s then false else q.testBit (p - s) := by
  have h := testBit_add_mul_pow2 (a := 0) (q := q) (s := s) (p := p) (Nat.two_pow_pos s)
  simpa using h

lemma testBit_sum_blocks {n k b G : ℕ} (hGk : G * k + b ≤ n)
    (d : Fin G → Fin (2 ^ k)) (tail : Fin (2 ^ b)) :
    let val := (∑ g : Fin G, (d g).val * 2 ^ (n - (g.val + 1) * k)) + tail.val
    val < 2 ^ n ∧
    (∀ p < b, val.testBit p = tail.val.testBit p) ∧
    (∀ p, b ≤ p → p < n - G * k → val.testBit p = false) ∧
    (∀ (g : Fin G) (r : ℕ), r < k →
      val.testBit (n - (g.val + 1) * k + r) = (d g).val.testBit r) := by
  have hpart : ∀ (m : ℕ) (hm : m ≤ G),
      let S := ∑ g : Fin G, if g.val < m then (d g).val * 2 ^ (n - (g.val + 1) * k) else 0
      (∃ q : ℕ, S = q * 2 ^ (n - m * k)) ∧
      S < 2 ^ n ∧
      (∀ p < n - m * k, S.testBit p = false) ∧
      (∀ (g : Fin G) (r : ℕ), g.val < m → r < k →
        S.testBit (n - (g.val + 1) * k + r) = (d g).val.testBit r) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : (∑ g : Fin G, if g.val < 0 then (d g).val * 2 ^ (n - (g.val + 1) * k) else 0) = 0 := by
        simp
      refine ⟨⟨0, by simp⟩, by rw [h0]; exact Nat.two_pow_pos n,
        fun p _ => by simp, fun g _ hg => by omega⟩
    | succ m ih =>
      intro hm
      rcases ih (by omega) with ⟨⟨q, hq⟩, _, hzero, hbits⟩
      let gm : Fin G := ⟨m, by omega⟩
      have hsplit : (∑ g : Fin G, if g.val < m + 1 then (d g).val * 2 ^ (n - (g.val + 1) * k) else 0) =
          (∑ g : Fin G, if g.val < m then (d g).val * 2 ^ (n - (g.val + 1) * k) else 0) +
          (d gm).val * 2 ^ (n - (m + 1) * k) := by
        have hdiff : ∀ g : Fin G,
            (if g.val < m + 1 then (d g).val * 2 ^ (n - (g.val + 1) * k) else 0) =
            (if g.val < m then (d g).val * 2 ^ (n - (g.val + 1) * k) else 0) +
            (if g = gm then (d gm).val * 2 ^ (n - (m + 1) * k) else 0) := by
          intro g
          by_cases h1 : g.val < m
          · have h2 : g.val < m + 1 := by omega
            have h3 : g ≠ gm := fun h => by rw [h] at h1; simp [gm] at h1
            simp [h1, h2, h3]
          · by_cases h2 : g = gm
            · subst h2; simp [gm]
            · have h3 : ¬ g.val < m + 1 := by
                intro hlt; apply h2; apply Fin.ext; simp [gm]; omega
              simp [h1, h2, h3]
        simp_rw [hdiff]
        rw [Finset.sum_add_distrib]
        simp
      set S_prev := ∑ g : Fin G, if g.val < m then (d g).val * 2 ^ (n - (g.val + 1) * k) else 0
      set term := (d gm).val * 2 ^ (n - (m + 1) * k)
      have hmul_pow : 2 ^ (n - m * k) = 2 ^ k * 2 ^ (n - (m + 1) * k) := by
        rw [← Nat.pow_add]
        congr 1
        have hle1 : (m + 1) * k ≤ G * k := Nat.mul_le_mul_right k hm
        rw [Nat.add_mul, Nat.one_mul] at hle1 ⊢
        omega
      have hterm_lt : term < 2 ^ (n - m * k) := by
        dsimp only [term]
        rw [hmul_pow]
        exact Nat.mul_lt_mul_of_pos_right (d gm).isLt (Nat.two_pow_pos _)
      have hadd_eq : S_prev + term = (q * 2 ^ k + (d gm).val) * 2 ^ (n - (m + 1) * k) := by
        dsimp only [term]
        rw [hq, hmul_pow, ← Nat.mul_assoc, ← Nat.add_mul]
      have htest_add : ∀ p : ℕ, (S_prev + term).testBit p =
          if p < n - m * k then term.testBit p else S_prev.testBit p := by
        intro p
        rw [hq, Nat.add_comm, testBit_add_mul_pow2 hterm_lt]
        by_cases hp : p < n - m * k
        · simp [hp]
        · simp only [testBit_mul_pow2, hp, ↓reduceIte]
      have hlt_n : S_prev + term < 2 ^ n := by
        apply Nat.lt_pow_two_of_testBit
        intro p hp
        rw [htest_add]
        have hnot : ¬ p < n - m * k := by omega
        simp only [hnot, ↓reduceIte]
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by
          rcases ih (by omega) with ⟨_, hltp, _, _⟩; exact hltp)
          (Nat.pow_le_pow_right Nat.zero_lt_two hp))
      rw [hsplit]
      refine ⟨⟨q * 2 ^ k + (d gm).val, hadd_eq⟩, hlt_n, ?_, ?_⟩
      · intro p hp
        rw [htest_add]
        have hlt1 : p < n - m * k := by
          have : m * k ≤ (m + 1) * k := Nat.mul_le_mul_right k (by omega)
          omega
        simp only [hlt1, ↓reduceIte, term, testBit_mul_pow2, hp]
      · intro g r hg hr
        rw [htest_add]
        by_cases hgm : g.val < m
        · have hge : ¬ n - (g.val + 1) * k + r < n - m * k := by
            have : (g.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k (by omega)
            omega
          simp only [hge, ↓reduceIte]
          exact hbits g r hgm hr
        · have hgeq : g = gm := Fin.ext (by simp [gm]; omega)
          subst hgeq
          have hlt1 : n - (m + 1) * k + r < n - m * k := by
            have hle1 : (m + 1) * k ≤ G * k := Nat.mul_le_mul_right k hm
            rw [Nat.add_mul, Nat.one_mul] at hle1 ⊢
            omega
          simp only [gm, hlt1, ↓reduceIte, term, testBit_mul_pow2]
          have hnot : ¬ n - (m + 1) * k + r < n - (m + 1) * k := by omega
          simp [hnot]
  rcases hpart G le_rfl with ⟨⟨q, hq⟩, hS_lt, hS_zero, hS_bits⟩
  have hsum_eq : (∑ g : Fin G, (d g).val * 2 ^ (n - (g.val + 1) * k)) =
      ∑ g : Fin G, if g.val < G then (d g).val * 2 ^ (n - (g.val + 1) * k) else 0 := by
    apply Finset.sum_congr rfl
    intro g _; simp [g.isLt]
  set S := ∑ g : Fin G, (d g).val * 2 ^ (n - (g.val + 1) * k)
  rw [← hsum_eq] at hq hS_lt hS_zero hS_bits
  have htail_lt : tail.val < 2 ^ (n - G * k) :=
    lt_of_lt_of_le tail.isLt (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have htest_val : ∀ p : ℕ, (S + tail.val).testBit p =
      if p < n - G * k then tail.val.testBit p else S.testBit p := by
    intro p
    rw [hq, Nat.add_comm, testBit_add_mul_pow2 htail_lt, testBit_mul_pow2]
    by_cases hp : p < n - G * k
    · simp [hp]
    · simp [hp]
  have hval_lt : S + tail.val < 2 ^ n := by
    apply Nat.lt_pow_two_of_testBit
    intro p hp
    rw [htest_val]
    have hnot : ¬ p < n - G * k := by omega
    simp only [hnot, ↓reduceIte]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hS_lt (Nat.pow_le_pow_right Nat.zero_lt_two hp))
  refine ⟨hval_lt, ?_, ?_, ?_⟩
  · intro p hp
    rw [htest_val]
    have hlt : p < n - G * k := by omega
    simp [hlt]
  · intro p hp1 hp2
    rw [htest_val]
    simp only [hp2, ↓reduceIte]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le tail.isLt (Nat.pow_le_pow_right Nat.zero_lt_two hp1))
  · intro g r hr
    rw [htest_val]
    have hge : ¬ n - (g.val + 1) * k + r < n - G * k := by
      have : (g.val + 1) * k ≤ G * k := Nat.mul_le_mul_right k (by omega)
      omega
    simp only [hge, ↓reduceIte]
    exact hS_bits g r g.isLt hr

lemma pack_lt_iff {n k b G : ℕ} (hGpos : 0 < G) (hGk : G * k + b ≤ n)
    (d₁ d₂ : Fin G → Fin (2 ^ k)) (t₁ t₂ : Fin (2 ^ b)) :
    let p1 := (∑ g : Fin G, (d₁ g).val * 2 ^ (n - (g.val + 1) * k)) + t₁.val
    let p2 := (∑ g : Fin G, (d₂ g).val * 2 ^ (n - (g.val + 1) * k)) + t₂.val
    (∀ g : Fin G, g.val + 1 < G → d₁ g = d₂ g) →
    (p1 < p2 ↔
      (∃ gL : Fin G, gL.val + 1 = G ∧
        ((d₁ gL).val < (d₂ gL).val ∨ ((d₁ gL).val = (d₂ gL).val ∧ t₁.val < t₂.val)))) := by
  intro p1 p2 heq
  let gL : Fin G := ⟨G - 1, by omega⟩
  have hgL : gL.val + 1 = G := by simp [gL]; omega
  have hsplit : ∀ d : Fin G → Fin (2 ^ k),
      (∑ g : Fin G, (d g).val * 2 ^ (n - (g.val + 1) * k)) =
      (∑ g ∈ Finset.univ.erase gL, (d g).val * 2 ^ (n - (g.val + 1) * k)) +
      (d gL).val * 2 ^ (n - G * k) := by
    intro d
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ gL)]
    simp [gL, hgL]
  have hpre_eq : (∑ g ∈ Finset.univ.erase gL, (d₁ g).val * 2 ^ (n - (g.val + 1) * k)) =
      (∑ g ∈ Finset.univ.erase gL, (d₂ g).val * 2 ^ (n - (g.val + 1) * k)) := by
    apply Finset.sum_congr rfl
    intro g hg
    have hne : g ≠ gL := (Finset.mem_erase.mp hg).1
    have hlt : g.val + 1 < G := by
      have := g.isLt
      have : g.val ≠ G - 1 := fun h => hne (Fin.ext h)
      omega
    rw [heq g hlt]
  have hp1 : p1 = (∑ g ∈ Finset.univ.erase gL, (d₁ g).val * 2 ^ (n - (g.val + 1) * k)) +
      ((d₁ gL).val * 2 ^ (n - G * k) + t₁.val) := by
    dsimp only [p1]; rw [hsplit d₁, Nat.add_assoc]
  have hp2 : p2 = (∑ g ∈ Finset.univ.erase gL, (d₁ g).val * 2 ^ (n - (g.val + 1) * k)) +
      ((d₂ gL).val * 2 ^ (n - G * k) + t₂.val) := by
    dsimp only [p2]; rw [hsplit d₂, ← hpre_eq, Nat.add_assoc]
  rw [hp1, hp2, Nat.add_lt_add_iff_left]
  have ht1 : t₁.val < 2 ^ (n - G * k) :=
    lt_of_lt_of_le t₁.isLt (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  have ht2 : t₂.val < 2 ^ (n - G * k) :=
    lt_of_lt_of_le t₂.isLt (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
  constructor
  · intro hlt
    refine ⟨gL, hgL, ?_⟩
    by_cases h1 : (d₁ gL).val < (d₂ gL).val
    · exact Or.inl h1
    · by_cases h2 : (d₁ gL).val = (d₂ gL).val
      · rw [h2] at hlt; exact Or.inr ⟨h2, by omega⟩
      · have hgt : (d₂ gL).val + 1 ≤ (d₁ gL).val := by omega
        have hmul : ((d₂ gL).val + 1) * 2 ^ (n - G * k) ≤ (d₁ gL).val * 2 ^ (n - G * k) :=
          Nat.mul_le_mul_right _ hgt
        rw [Nat.add_mul, Nat.one_mul] at hmul
        omega
  · rintro ⟨g', hg', hdisj⟩
    have heqg : g' = gL := Fin.ext (by simp [gL]; omega)
    subst heqg
    rcases hdisj with hlt | ⟨heqv, hltt⟩
    · have hmul : ((d₁ gL).val + 1) * 2 ^ (n - G * k) ≤ (d₂ gL).val * 2 ^ (n - G * k) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega
    · rw [heqv]; omega

lemma pack_gt_of_prefix_gt {n k b G : ℕ} (hGk : G * k + b ≤ n)
    (d₁ d₂ : Fin G → Fin (2 ^ k)) (t₁ t₂ : Fin (2 ^ b))
    (hle : ∀ g : Fin G, g.val + 1 < G → (d₁ g).val ≤ (d₂ g).val)
    (hex : ∃ g : Fin G, g.val + 1 < G ∧ (d₁ g).val < (d₂ g).val) :
    (∑ g : Fin G, (d₁ g).val * 2 ^ (n - (g.val + 1) * k)) + t₁.val <
      (∑ g : Fin G, (d₂ g).val * 2 ^ (n - (g.val + 1) * k)) + t₂.val := by
  rcases hex with ⟨g0, hg0, hlt0⟩
  have hGpos : 0 < G := by omega
  let gL : Fin G := ⟨G - 1, by omega⟩
  have hgL : gL.val + 1 = G := by simp [gL]; omega
  have hg0_ne : g0 ≠ gL := fun h => by rw [h] at hg0; simp [gL] at hg0; omega
  have hsum_diff :
      (∑ g ∈ Finset.univ.erase gL, (d₁ g).val * 2 ^ (n - (g.val + 1) * k)) +
        2 ^ (n - (g0.val + 1) * k) ≤
      ∑ g ∈ Finset.univ.erase gL, (d₂ g).val * 2 ^ (n - (g.val + 1) * k) := by
    have hmem : g0 ∈ Finset.univ.erase gL := Finset.mem_erase.mpr ⟨hg0_ne, Finset.mem_univ _⟩
    rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem]
    have hrest : ∑ x ∈ (Finset.univ.erase gL).erase g0, (d₁ x).val * 2 ^ (n - (x.val + 1) * k) ≤
        ∑ x ∈ (Finset.univ.erase gL).erase g0, (d₂ x).val * 2 ^ (n - (x.val + 1) * k) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxne : x ≠ gL := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
      have hxlt : x.val + 1 < G := by
        have := x.isLt
        have : x.val ≠ G - 1 := fun h => hxne (Fin.ext h)
        omega
      exact Nat.mul_le_mul_right _ (hle x hxlt)
    have hterm : (d₁ g0).val * 2 ^ (n - (g0.val + 1) * k) + 2 ^ (n - (g0.val + 1) * k) ≤
        (d₂ g0).val * 2 ^ (n - (g0.val + 1) * k) := by
      have : ((d₁ g0).val + 1) * 2 ^ (n - (g0.val + 1) * k) ≤
          (d₂ g0).val * 2 ^ (n - (g0.val + 1) * k) := Nat.mul_le_mul_right _ (by omega)
      rwa [Nat.add_mul, Nat.one_mul] at this
    omega
  have htail_bound : (d₁ gL).val * 2 ^ (n - G * k) + t₁.val < 2 ^ (n - (g0.val + 1) * k) := by
    have ht1 : t₁.val < 2 ^ (n - G * k) :=
      lt_of_lt_of_le t₁.isLt (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
    have h1 : (d₁ gL).val * 2 ^ (n - G * k) + t₁.val < ((d₁ gL).val + 1) * 2 ^ (n - G * k) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 : ((d₁ gL).val + 1) * 2 ^ (n - G * k) ≤ 2 ^ k * 2 ^ (n - G * k) :=
      Nat.mul_le_mul_right _ (d₁ gL).isLt
    have h3 : 2 ^ k * 2 ^ (n - G * k) ≤ 2 ^ (n - (g0.val + 1) * k) := by
      rw [← Nat.pow_add]
      apply Nat.pow_le_pow_right Nat.zero_lt_two
      have hle2 : (g0.val + 1) * k + k ≤ G * k := by
        calc (g0.val + 1) * k + k = (g0.val + 2) * k := by rw [← Nat.succ_mul]
          _ ≤ G * k := Nat.mul_le_mul_right k (by omega)
      omega
    omega
  have hs1 : (∑ g : Fin G, (d₁ g).val * 2 ^ (n - (g.val + 1) * k)) =
      (∑ g ∈ Finset.univ.erase gL, (d₁ g).val * 2 ^ (n - (g.val + 1) * k)) +
        (d₁ gL).val * 2 ^ (n - G * k) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ gL), hgL]
  have hs2 : (∑ g : Fin G, (d₂ g).val * 2 ^ (n - (g.val + 1) * k)) =
      (∑ g ∈ Finset.univ.erase gL, (d₂ g).val * 2 ^ (n - (g.val + 1) * k)) +
        (d₂ gL).val * 2 ^ (n - G * k) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ gL), hgL]
  rw [hs1, hs2]
  omega

lemma main_proof (n w : ℕ) (hn : 0 < n) (q : Fin (2 ^ n)) :
    let I := n * 2 ^ (w + 1)
    ∀ (C : Circuit) (outBit : Fin n → Fin (I + C.size)),
      FanInTwo C →
      ReadsBack I C →
      (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        let inputs := (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
          table i (fun j => pat.val.testBit j.val)))).flatten
        let sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z => ∀ i : Fin n,
          table i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
        q.val < sols.card → ∃ z ∈ sols,
          (sols.filter (fun y => y.val < z.val)).card = q.val ∧
          ∀ pos : Fin n, (C.wires inputs).getD (outBit pos).val false =
            z.val.testBit (n - 1 - pos.val)) →
      ∀ k b : ℕ, 0 < k → k ≤ w + 1 → k + b ≤ n → q.val < 2 ^ (k + b) →
        1 + ((n - b) / k) * (2 ^ k - 1) - q.val / 2 ^ b ≤ 2 ^ notCount C := by
  intro I C outBit hfan _hreads hrank k b hk0 hkw hkb hqlt
  set G := (n - b) / k
  have hGpos : 0 < G := Nat.div_pos (by omega) hk0
  have hGk_le : G * k ≤ n - b := Nat.div_mul_le_self (n - b) k
  have hGkb : G * k + b ≤ n := by omega
  set K1 := 2 ^ k - 1
  have hK1_pos : 0 < K1 := by
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by simp
        _ ≤ 2 ^ k := Nat.pow_le_pow_right Nat.zero_lt_two hk0
    omega
  set j0 := q.val / 2 ^ b
  set r0 := q.val % 2 ^ b
  have hj0_lt : j0 < 2 ^ k := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hqlt
  have hr0_lt : r0 < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  set L := G * K1 - j0
  have hj0_le_GK1 : j0 ≤ G * K1 := by
    have : 1 * K1 ≤ G * K1 := Nat.mul_le_mul_right K1 hGpos
    omega
  have hgoal_eq : 1 + G * K1 - j0 = L + 1 := by omega
  let stepInBlock : ℕ → ℕ → ℕ := fun t g => min K1 (t - g * K1)
  let A : ℕ → Fin G → Finset (Fin (2 ^ k)) := fun t g =>
    if g.val + 1 < G then
      Finset.univ.filter (fun x : Fin (2 ^ k) => K1 - stepInBlock t g.val ≤ x.val)
    else
      Finset.univ.filter (fun x : Fin (2 ^ k) => x.val < j0 ∨ K1 - stepInBlock t g.val ≤ x.val)
  let mkTable : ℕ → Fin n → (Fin (w + 1) → Bool) → Bool := fun t i pat =>
    if h : i.val % k = 0 ∧ i.val / k < G then
      decide (⟨patToNum k hkw pat, patToNum_lt k hkw pat⟩ ∈ A t ⟨i.val / k, h.2⟩)
    else if G * k ≤ i.val ∧ i.val < n - b then
      !(pat ⟨0, by omega⟩)
    else true
  let mkInputs : ℕ → List Bool := fun t =>
    (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
      mkTable t i (fun j => pat.val.testBit j.val)))).flatten
  let solsOf : ℕ → Finset (Fin (2 ^ n)) := fun t =>
    (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z => ∀ i : Fin n,
      mkTable t i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
  let pack : (Fin G → Fin (2 ^ k)) → Fin (2 ^ b) → Fin (2 ^ n) := fun d tail =>
    ⟨(∑ g : Fin G, (d g).val * 2 ^ (n - (g.val + 1) * k)) + tail.val,
      (testBit_sum_blocks hGkb d tail).1⟩
  let unpackD : Fin (2 ^ n) → Fin G → Fin (2 ^ k) := fun z g =>
    ⟨(z.val >>> (n - (g.val + 1) * k)) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
  let unpackT : Fin (2 ^ n) → Fin (2 ^ b) := fun z =>
    ⟨z.val % 2 ^ b, Nat.mod_lt _ (Nat.two_pow_pos b)⟩
  have hpat_eq_block : ∀ (z : Fin (2 ^ n)) (g : Fin G),
      patToNum k hkw (fun j => z.val.testBit (n - 1 - ((g.val * k + j.val) % n))) =
        (unpackD z g).val := by
    intro z g
    apply Nat.eq_of_testBit_eq
    intro r
    rw [testBit_patToNum]
    dsimp only [unpackD]
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    by_cases hr : r < k
    · simp only [hr, ↓reduceDIte, decide_true, Bool.true_and]
      have hlt_n : g.val * k + (k - 1 - r) < n := by
        have : (g.val + 1) * k ≤ G * k := Nat.mul_le_mul_right k g.isLt
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      rw [Nat.mod_eq_of_lt hlt_n]
      congr 1
      have : (g.val + 1) * k ≤ n := le_trans (Nat.mul_le_mul_right k g.isLt) (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this ⊢
      omega
    · simp [hr]
  have hsols_iff : ∀ (t : ℕ) (z : Fin (2 ^ n)),
      z ∈ solsOf t ↔
        (∀ g : Fin G, unpackD z g ∈ A t g) ∧
        (∀ p, b ≤ p → p < n - G * k → z.val.testBit p = false) := by
    intro t z
    simp only [solsOf, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz
      refine ⟨fun g => ?_, fun p hp1 hp2 => ?_⟩
      · have hgk_lt : g.val * k < n := by
          have : (g.val + 1) * k ≤ G * k := Nat.mul_le_mul_right k g.isLt
          rw [Nat.add_mul, Nat.one_mul] at this; omega
        let i0 : Fin n := ⟨g.val * k, hgk_lt⟩
        have hzi := hz i0
        have hc : i0.val % k = 0 ∧ i0.val / k < G :=
          ⟨Nat.mul_mod_left g.val k, by rw [Nat.mul_div_cancel g.val hk0]; exact g.isLt⟩
        dsimp only [mkTable] at hzi
        simp only [hc, and_self, ↓reduceDIte, decide_eq_true_eq] at hzi
        have hfg : (⟨i0.val / k, hc.2⟩ : Fin G) = g := Fin.ext (Nat.mul_div_cancel g.val hk0)
        rw [hfg] at hzi
        have hpeq : (⟨patToNum k hkw (fun j => z.val.testBit (n - 1 - ((i0.val + j.val) % n))),
            patToNum_lt k hkw _⟩ : Fin (2 ^ k)) = unpackD z g :=
          Fin.ext (hpat_eq_block z g)
        rwa [hpeq] at hzi
      · let i0 : Fin n := ⟨n - 1 - p, by omega⟩
        have hzi := hz i0
        have hnot1 : ¬ (i0.val % k = 0 ∧ i0.val / k < G) := by
          rintro ⟨_, hlt⟩
          have hdm : (i0.val / k) * k + i0.val % k = i0.val := by
            rw [Nat.mul_comm]; exact Nat.div_add_mod i0.val k
          have hmlt := Nat.mod_lt i0.val hk0
          have hle1 : (i0.val / k + 1) * k ≤ G * k := Nat.mul_le_mul_right k hlt
          rw [Nat.add_mul, Nat.one_mul] at hle1
          have hi0_val : i0.val = n - 1 - p := rfl
          omega
        have hc2 : G * k ≤ i0.val ∧ i0.val < n - b := by simp [i0]; omega
        dsimp only [mkTable] at hzi
        simp only [hnot1, ↓reduceDIte, hc2, and_self, ↓reduceIte, Bool.not_eq_true'] at hzi
        have hmod : (i0.val + 0) % n = i0.val := Nat.mod_eq_of_lt i0.isLt
        have hidx : n - 1 - (i0.val + 0) % n = p := by rw [hmod]; simp [i0]; omega
        rwa [hidx] at hzi
    · rintro ⟨hD, hgap⟩ i
      dsimp only [mkTable]
      by_cases hc1 : i.val % k = 0 ∧ i.val / k < G
      · simp only [hc1, and_self, ↓reduceDIte, decide_eq_true_eq]
        let g : Fin G := ⟨i.val / k, hc1.2⟩
        have hi_eq : i.val = g.val * k := by
          have := (Nat.div_add_mod i.val k).symm
          rw [hc1.1, Nat.add_zero, Nat.mul_comm] at this
          exact this
        have hpeq : (⟨patToNum k hkw (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))),
            patToNum_lt k hkw _⟩ : Fin (2 ^ k)) = unpackD z g := by
          apply Fin.ext
          dsimp only
          conv_lhs => rw [hi_eq]
          exact hpat_eq_block z g
        rw [hpeq]
        exact hD g
      · simp only [hc1, ↓reduceDIte]
        by_cases hc2 : G * k ≤ i.val ∧ i.val < n - b
        · simp only [hc2, and_self, ↓reduceIte, Bool.not_eq_true']
          have hmod : (i.val + 0) % n = i.val := Nat.mod_eq_of_lt i.isLt
          rw [hmod]
          exact hgap (n - 1 - i.val) (by omega) (by omega)
        · simp [hc2]
  have hpack_unpack : ∀ (z : Fin (2 ^ n)),
      (∀ p, b ≤ p → p < n - G * k → z.val.testBit p = false) →
      pack (unpackD z) (unpackT z) = z := by
    intro z hgap
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro p
    rcases testBit_sum_blocks hGkb (unpackD z) (unpackT z) with ⟨hval_lt, hb_bits, hgap_bits, hblk_bits⟩
    by_cases hp_n : n ≤ p
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hval_lt (Nat.pow_le_pow_right Nat.zero_lt_two hp_n)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le z.isLt (Nat.pow_le_pow_right Nat.zero_lt_two hp_n))]
    · by_cases hpb : p < b
      · rw [hb_bits p hpb]
        dsimp only [unpackT]
        rw [Nat.testBit_mod_two_pow]; simp [hpb]
      · by_cases hpg : p < n - G * k
        · rw [hgap_bits p (by omega) hpg, hgap p (by omega) hpg]
        · set q_pos := n - 1 - p
          have hq_lt : q_pos < G * k := by omega
          let g : Fin G := ⟨q_pos / k, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩
          set r := k - 1 - q_pos % k
          have hr_lt : r < k := by have := Nat.mod_lt q_pos hk0; omega
          have hp_eq : n - (g.val + 1) * k + r = p := by
            have hdm := Nat.div_add_mod q_pos k
            have hmod_lt := Nat.mod_lt q_pos hk0
            have : (g.val + 1) * k ≤ G * k := Nat.mul_le_mul_right k g.isLt
            dsimp only [g, r, q_pos] at this hdm hmod_lt ⊢
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm] at this ⊢
            omega
          have hbit := hblk_bits g r hr_lt
          rw [hp_eq] at hbit
          rw [hbit]
          dsimp only [unpackD]
          rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
          simp only [hr_lt, decide_true, Bool.true_and, hp_eq]
  have hunpack_pack : ∀ (d : Fin G → Fin (2 ^ k)) (tail : Fin (2 ^ b)),
      unpackD (pack d tail) = d ∧ unpackT (pack d tail) = tail := by
    intro d tail
    rcases testBit_sum_blocks hGkb d tail with ⟨_, hb_bits, _, hblk_bits⟩
    refine ⟨?_, ?_⟩
    · funext g
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro r
      dsimp only [unpackD]
      rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      by_cases hr : r < k
      · simp only [hr, decide_true, Bool.true_and]
        exact hblk_bits g r hr
      · simp only [hr, decide_false, Bool.false_and]
        exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le (d g).isLt
          (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))).symm
    · apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro p
      dsimp only [unpackT]
      rw [Nat.testBit_mod_two_pow]
      by_cases hp : p < b
      · simp only [hp, decide_true, Bool.true_and]
        exact hb_bits p hp
      · simp only [hp, decide_false, Bool.false_and]
        exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le tail.isLt
          (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))).symm
  let dTarget : ℕ → Fin G → Fin (2 ^ k) := fun t g =>
    ⟨K1 - stepInBlock t g.val, by omega⟩
  let tTarget : Fin (2 ^ b) := ⟨r0, hr0_lt⟩
  let zTarget : ℕ → Fin (2 ^ n) := fun t => pack (dTarget t) tTarget
  have htarget_rank : ∀ t ≤ L,
      zTarget t ∈ solsOf t ∧
      (solsOf t |>.filter (fun y => y.val < (zTarget t).val)).card = q.val := by
    intro t ht
    have hstep_last : stepInBlock t (G - 1) ≤ K1 - j0 := by
      dsimp only [stepInBlock]
      have : (G - 1) * K1 + K1 = G * K1 := by
        have := Nat.sub_add_cancel hGpos
        calc (G - 1) * K1 + K1 = (G - 1 + 1) * K1 := by rw [Nat.add_mul, Nat.one_mul]
          _ = G * K1 := by rw [this]
      omega
    have hmem : zTarget t ∈ solsOf t := by
      rw [hsols_iff]
      rcases hunpack_pack (dTarget t) tTarget with ⟨hd, _⟩
      refine ⟨fun g => ?_, (testBit_sum_blocks hGkb (dTarget t) tTarget).2.2.1⟩
      rw [hd]
      dsimp only [A, dTarget]
      by_cases hg : g.val + 1 < G
      · simp only [hg, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
        exact le_rfl
      · simp only [hg, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr le_rfl
    refine ⟨hmem, ?_⟩
    let gL : Fin G := ⟨G - 1, by omega⟩
    have hgL : gL.val + 1 = G := by simp [gL]; omega
    have hj0_le_dL : j0 ≤ (dTarget t gL).val := by
      dsimp only [dTarget, gL]; omega
    have hfilt_card : ((solsOf t).filter (fun y => y.val < (zTarget t).val)).card =
        (Finset.range q.val).card := by
      apply Finset.card_bij (fun y _ =>
        (if (unpackD y gL).val < j0 then (unpackD y gL).val else j0) * 2 ^ b + (unpackT y).val)
      · intro y hy
        rw [Finset.mem_filter] at hy
        rcases hy with ⟨hysol, hylt⟩
        rw [hsols_iff] at hysol
        rcases hysol with ⟨hD, hgap⟩
        have hy_eq : pack (unpackD y) (unpackT y) = y := hpack_unpack y hgap
        rw [← hy_eq] at hylt
        have hle_pre : ∀ g : Fin G, g.val + 1 < G → (dTarget t g).val ≤ (unpackD y g).val := by
          intro g hg
          have hmem_g := hD g
          simp only [A, hg, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hmem_g
          exact hmem_g
        have heq_pre : ∀ g : Fin G, g.val + 1 < G → unpackD y g = dTarget t g := by
          intro g hg
          by_contra hne
          have hgt : (dTarget t g).val < (unpackD y g).val :=
            lt_of_le_of_ne (hle_pre g hg) (fun h => hne (Fin.ext h.symm))
          have hbad := pack_gt_of_prefix_gt hGkb (dTarget t) (unpackD y) tTarget (unpackT y)
            hle_pre ⟨g, hg, hgt⟩
          exact Nat.lt_asymm hylt hbad
        have hiff := pack_lt_iff hGpos hGkb (unpackD y) (dTarget t) (unpackT y) tTarget heq_pre
        rcases hiff.mp hylt with ⟨g', hg', hdisj⟩
        have heqg : g' = gL := Fin.ext (by simp [gL]; omega)
        subst heqg
        have hmem_L := hD gL
        have hnot_lt : ¬ gL.val + 1 < G := by omega
        simp only [A, hnot_lt, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hmem_L
        rw [Finset.mem_range]
        have hdiv := Nat.div_add_mod q.val (2 ^ b)
        rcases hdisj with hlt_L | ⟨heq_L, hlt_T⟩
        · have hj_lt : (unpackD y gL).val < j0 := by
            rcases hmem_L with h1 | h2
            · exact h1
            · dsimp only [dTarget] at hlt_L; omega
          simp only [hj_lt, ↓reduceIte]
          have hmul : ((unpackD y gL).val + 1) * 2 ^ b ≤ j0 * 2 ^ b :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at hmul
          have ht_lt : (unpackT y).val < 2 ^ b := (unpackT y).isLt
          dsimp only [j0, r0] at hmul ⊢
          rw [Nat.mul_comm] at hdiv
          omega
        · have hj_ge : ¬ (unpackD y gL).val < j0 := by omega
          simp only [hj_ge, ↓reduceIte]
          dsimp only [j0, r0, tTarget] at hlt_T ⊢
          rw [Nat.mul_comm] at hdiv
          omega
      · intro y₁ hy₁ y₂ hy₂ heq_val
        rw [Finset.mem_filter] at hy₁ hy₂
        rcases (hsols_iff t y₁).mp hy₁.1 with ⟨hD1, hgap1⟩
        rcases (hsols_iff t y₂).mp hy₂.1 with ⟨hD2, hgap2⟩
        have hpre : ∀ y, y ∈ solsOf t → y.val < (zTarget t).val →
            (∀ g : Fin G, g.val + 1 < G → unpackD y g = dTarget t g) ∧
            ((unpackD y gL).val < j0 ∨ (unpackD y gL).val = (dTarget t gL).val) := by
          intro y hys hylt
          rcases (hsols_iff t y).mp hys with ⟨hD, hgap⟩
          have hle_pre : ∀ g' : Fin G, g'.val + 1 < G → (dTarget t g').val ≤ (unpackD y g').val := by
            intro g' hg'
            have hm := hD g'
            simp only [A, hg', ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hm
            exact hm
          have hpeq : ∀ g' : Fin G, g'.val + 1 < G → unpackD y g' = dTarget t g' := by
            intro g' hg'
            by_contra hne
            have hgt : (dTarget t g').val < (unpackD y g').val :=
              lt_of_le_of_ne (hle_pre g' hg') (fun h => hne (Fin.ext h.symm))
            have hbad : (zTarget t).val < (pack (unpackD y) (unpackT y)).val :=
              pack_gt_of_prefix_gt hGkb (dTarget t) (unpackD y) tTarget (unpackT y)
                hle_pre ⟨g', hg', hgt⟩
            rw [hpack_unpack y hgap] at hbad
            exact Nat.lt_asymm hylt hbad
          refine ⟨hpeq, ?_⟩
          have hy_eq : pack (unpackD y) (unpackT y) = y := hpack_unpack y hgap
          rw [← hy_eq] at hylt
          have hiff := pack_lt_iff hGpos hGkb (unpackD y) (dTarget t) (unpackT y) tTarget hpeq
          rcases hiff.mp hylt with ⟨g', hg', hdisj⟩
          have heqg : g' = gL := Fin.ext (by simp [gL]; omega)
          subst heqg
          have hmem_L := hD gL
          have hnot_lt : ¬ gL.val + 1 < G := by omega
          simp only [A, hnot_lt, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hmem_L
          rcases hdisj with hlt_L | ⟨heq_L, _⟩
          · left
            rcases hmem_L with h1 | h2
            · exact h1
            · dsimp only [dTarget] at hlt_L; omega
          · exact Or.inr heq_L
        rcases hpre y₁ hy₁.1 hy₁.2 with ⟨h1_pre, h1_L⟩
        rcases hpre y₂ hy₂.1 hy₂.2 with ⟨h2_pre, h2_L⟩
        have ht1 := (unpackT y₁).isLt
        have ht2 := (unpackT y₂).isLt
        set c1 := if (unpackD y₁ gL).val < j0 then (unpackD y₁ gL).val else j0
        set c2 := if (unpackD y₂ gL).val < j0 then (unpackD y₂ gL).val else j0
        have hc_eq : c1 = c2 := by
          have h1 : (c1 * 2 ^ b + (unpackT y₁).val) / 2 ^ b = c1 := by
            rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos b), Nat.div_eq_of_lt ht1, Nat.add_zero]
          have h2 : (c2 * 2 ^ b + (unpackT y₂).val) / 2 ^ b = c2 := by
            rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos b), Nat.div_eq_of_lt ht2, Nat.add_zero]
          rw [← h1, ← h2]
          exact congrArg (· / 2 ^ b) heq_val
        have ht_eq : unpackT y₁ = unpackT y₂ := Fin.ext (by
          have : c1 * 2 ^ b + (unpackT y₁).val = c2 * 2 ^ b + (unpackT y₂).val := heq_val
          rw [hc_eq] at this; omega)
        have hdL : (unpackD y₁ gL).val = (unpackD y₂ gL).val := by
          dsimp only [c1, c2] at hc_eq
          by_cases h1 : (unpackD y₁ gL).val < j0 <;> by_cases h2 : (unpackD y₂ gL).val < j0
          · simp only [h1, h2, ↓reduceIte] at hc_eq; exact hc_eq
          · simp only [h1, h2, ↓reduceIte] at hc_eq; omega
          · simp only [h1, h2, ↓reduceIte] at hc_eq; omega
          · rcases h1_L with ha | ha <;> rcases h2_L with hb | hb
            · omega
            · omega
            · omega
            · rw [ha, hb]
        have hd_eq : unpackD y₁ = unpackD y₂ := by
          funext g
          by_cases hg : g.val + 1 < G
          · rw [h1_pre g hg, h2_pre g hg]
          · have : g = gL := Fin.ext (by simp [gL]; have := g.isLt; omega)
            subst this; exact Fin.ext hdL
        rw [← hpack_unpack y₁ hgap1, ← hpack_unpack y₂ hgap2, hd_eq, ht_eq]
      · intro v hv
        rw [Finset.mem_range] at hv
        set d_v := v / 2 ^ b
        set t_v := v % 2 ^ b
        have ht_v : t_v < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
        have hd_v_le : d_v ≤ j0 := Nat.div_le_div_right (le_of_lt hv)
        let d_fn : Fin G → Fin (2 ^ k) := fun g =>
          if g.val + 1 < G then dTarget t g
          else if d_v < j0 then ⟨d_v, by omega⟩
          else dTarget t gL
        let y := pack d_fn ⟨t_v, ht_v⟩
        have hy_sol : y ∈ solsOf t := by
          rw [hsols_iff]
          rcases hunpack_pack d_fn ⟨t_v, ht_v⟩ with ⟨hd, _⟩
          refine ⟨fun g => ?_, (testBit_sum_blocks hGkb d_fn ⟨t_v, ht_v⟩).2.2.1⟩
          rw [hd]
          dsimp only [A, d_fn, dTarget]
          by_cases hg : g.val + 1 < G
          · simp only [hg, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
            exact le_rfl
          · simp only [hg, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases hdv : d_v < j0
            · simp only [hdv, ↓reduceIte, true_or]
            · simp only [hdv, ↓reduceIte, gL, show g.val = G - 1 by have := g.isLt; omega]
              exact Or.inr le_rfl
        have hy_lt : y.val < (zTarget t).val := by
          have hiff := pack_lt_iff hGpos hGkb d_fn (dTarget t) ⟨t_v, ht_v⟩ tTarget
            (fun g hg => by simp [d_fn, hg])
          rw [hiff]
          refine ⟨gL, hgL, ?_⟩
          have hnot : ¬ gL.val + 1 < G := by omega
          by_cases hdv : d_v < j0
          · left; simp only [d_fn, hnot, ↓reduceIte, hdv]; omega
          · right
            have hdv_eq : d_v = j0 := by omega
            have htv_lt : t_v < r0 := by
              have h1 : 2 ^ b * d_v + t_v = v := Nat.div_add_mod v (2 ^ b)
              have h2 : 2 ^ b * j0 + r0 = q.val := Nat.div_add_mod q.val (2 ^ b)
              rw [hdv_eq] at h1
              omega
            simp only [d_fn, hnot, ↓reduceIte, hdv, true_and]
            exact htv_lt
        have hy_map : (if (unpackD y gL).val < j0 then (unpackD y gL).val else j0) * 2 ^ b +
            (unpackT y).val = v := by
          rcases hunpack_pack d_fn ⟨t_v, ht_v⟩ with ⟨hd, ht_u⟩
          rw [hd, ht_u]
          have hnot : ¬ gL.val + 1 < G := by omega
          by_cases hdv : d_v < j0
          · simp only [d_fn, hnot, ↓reduceIte, hdv]
            rw [Nat.mul_comm]; exact Nat.div_add_mod v (2 ^ b)
          · have hge : ¬ (dTarget t gL).val < j0 := by omega
            have hdv_eq : d_v = j0 := by omega
            simp only [d_fn, hnot, ↓reduceIte, hdv, hge]
            rw [← hdv_eq, Nat.mul_comm]; exact Nat.div_add_mod v (2 ^ b)
        exact ⟨y, Finset.mem_filter.mpr ⟨hy_sol, hy_lt⟩, hy_map⟩
    rw [hfilt_card, Finset.card_range]
  have huniq_rank : ∀ t ≤ L, ∀ z ∈ solsOf t,
      ((solsOf t).filter (fun y => y.val < z.val)).card = q.val → z = zTarget t := by
    intro t ht z hz hcard_z
    rcases htarget_rank t ht with ⟨ht_mem, ht_card⟩
    by_contra hne
    have hne_val : z.val ≠ (zTarget t).val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne_val with hlt | hgt
    · have hssub : (solsOf t).filter (fun y => y.val < z.val) ⊂
          (solsOf t).filter (fun y => y.val < (zTarget t).val) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun y hy => ?_, fun heq => ?_⟩
        · rw [Finset.mem_filter] at hy ⊢; exact ⟨hy.1, lt_trans hy.2 hlt⟩
        · have hmem : z ∈ (solsOf t).filter (fun y => y.val < (zTarget t).val) :=
            Finset.mem_filter.mpr ⟨hz, hlt⟩
          rw [← heq, Finset.mem_filter] at hmem
          exact lt_irrefl _ hmem.2
      have := Finset.card_lt_card hssub
      omega
    · have hssub : (solsOf t).filter (fun y => y.val < (zTarget t).val) ⊂
          (solsOf t).filter (fun y => y.val < z.val) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun y hy => ?_, fun heq => ?_⟩
        · rw [Finset.mem_filter] at hy ⊢; exact ⟨hy.1, lt_trans hy.2 hgt⟩
        · have hmem : zTarget t ∈ (solsOf t).filter (fun y => y.val < z.val) :=
            Finset.mem_filter.mpr ⟨ht_mem, hgt⟩
          rw [← heq, Finset.mem_filter] at hmem
          exact lt_irrefl _ hmem.2
      have := Finset.card_lt_card hssub
      omega
  have hcircuit_eq : ∀ t ≤ L, ∀ pos : Fin n,
      (C.wires (mkInputs t)).getD (outBit pos).val false =
        (zTarget t).val.testBit (n - 1 - pos.val) := by
    intro t ht pos
    rcases htarget_rank t ht with ⟨ht_mem, ht_card⟩
    have hcard_lt : q.val < (solsOf t).card := by
      have hssub : (solsOf t).filter (fun y => y.val < (zTarget t).val) ⊂ solsOf t := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
        have hm := ht_mem
        rw [← heq, Finset.mem_filter] at hm
        exact lt_irrefl _ hm.2
      have := Finset.card_lt_card hssub
      omega
    rcases hrank (mkTable t) hcard_lt with ⟨z, hz, hzc, hzw⟩
    have heq_z : z = zTarget t := huniq_rank t ht z hz hzc
    rw [← heq_z]
    exact hzw pos
  let xs : Fin (L + 1) → List Bool := fun t => mkInputs t.val
  have hxs_len : ∀ t : Fin (L + 1), (xs t).length = I := by
    intro t
    exact length_flatten_ofFn n (2 ^ (w + 1)) _
  have hxs_mono : ∀ t : Fin L, ∀ idx < I,
      (xs t.castSucc).getD idx false = true → (xs t.succ).getD idx false = true := by
    intro t idx _ hidx
    have hfl := flatten_list_mono
      (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
        mkTable t.castSucc.val i (fun j => pat.val.testBit j.val))))
      (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
        mkTable t.succ.val i (fun j => pat.val.testBit j.val))))
      (by simp)
      (fun i hi => by simp)
      (fun i hi j hj => by
        simp only [List.length_ofFn] at hi
        simp only [List.getElem_ofFn] at hj ⊢
        by_cases hjlt : j < 2 ^ (w + 1)
        · rw [List.getD_eq_getElem _ _ (by simp [hjlt]), List.getElem_ofFn] at hj
          rw [List.getD_eq_getElem _ _ (by simp [hjlt]), List.getElem_ofFn]
          dsimp only [mkTable] at hj ⊢
          split_ifs at hj ⊢ with hc1 hc2
          · simp only [decide_eq_true_eq] at hj ⊢
            dsimp only [A] at hj ⊢
            split_ifs at hj ⊢ with hglt
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, stepInBlock] at hj ⊢
              simp only [Fin.val_castSucc, Fin.val_succ] at hj ⊢
              omega
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, stepInBlock] at hj ⊢
              simp only [Fin.val_castSucc, Fin.val_succ] at hj ⊢
              rcases hj with h1 | h2
              · exact Or.inl h1
              · right; omega
          · exact hj
          · rfl
        · rw [getD_of_le _ _ (by simp; omega)] at hj
          exact Bool.noConfusion hj)
    exact hfl.2 idx hidx
  have hdrops_all : drops (I := I) xs C.gates = Finset.univ := by
    ext t
    simp only [drops, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have ht_lt : t.val < L := t.isLt
    have hlt_z : (zTarget (t.val + 1)).val < (zTarget t.val).val := by
      dsimp only [zTarget, pack]
      set g0_idx := t.val / K1
      have hg0_lt : g0_idx < G := Nat.div_lt_of_lt_mul (by
        have : L ≤ G * K1 := Nat.sub_le _ _
        rw [Nat.mul_comm]; omega)
      let g0 : Fin G := ⟨g0_idx, hg0_lt⟩
      have hterm_le : ∀ g : Fin G,
          (dTarget (t.val + 1) g).val * 2 ^ (n - (g.val + 1) * k) ≤
            (dTarget t.val g).val * 2 ^ (n - (g.val + 1) * k) := by
        intro g
        apply Nat.mul_le_mul_right
        dsimp only [dTarget, stepInBlock]
        omega
      have hterm_lt : (dTarget (t.val + 1) g0).val * 2 ^ (n - (g0.val + 1) * k) <
          (dTarget t.val g0).val * 2 ^ (n - (g0.val + 1) * k) := by
        apply Nat.mul_lt_mul_of_pos_right _ (Nat.two_pow_pos _)
        dsimp only [dTarget, stepInBlock, g0, g0_idx]
        have hdm := Nat.div_add_mod t.val K1
        have hmlt := Nat.mod_lt t.val hK1_pos
        rw [Nat.mul_comm] at hdm
        omega
      have hsum_lt : (∑ g : Fin G, (dTarget (t.val + 1) g).val * 2 ^ (n - (g.val + 1) * k)) <
          ∑ g : Fin G, (dTarget t.val g).val * 2 ^ (n - (g.val + 1) * k) :=
        Finset.sum_lt_sum (fun g _ => hterm_le g) ⟨g0, Finset.mem_univ g0, hterm_lt⟩
      omega
    rcases exists_bit_drop_of_lt hlt_z with ⟨p, hpt, hpf⟩
    have hp_lt : p < n := by
      by_contra hge
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (zTarget t.val).isLt
        (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))] at hpt
      exact Bool.noConfusion hpt
    let pos : Fin n := ⟨n - 1 - p, by omega⟩
    have hpos_eq : n - 1 - pos.val = p := by simp [pos]; omega
    refine ⟨(outBit pos).val, (outBit pos).isLt, ?_, ?_⟩
    · change (C.wires (mkInputs t.castSucc.val)).getD (outBit pos).val false = true
      rw [hcircuit_eq t.castSucc.val (by simp only [Fin.val_castSucc]; omega) pos, hpos_eq]
      exact hpt
    · change (C.wires (mkInputs t.succ.val)).getD (outBit pos).val false = false
      rw [hcircuit_eq t.succ.val (by simp only [Fin.val_succ]; omega) pos, hpos_eq]
      exact hpf
  have hfan' : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rcases hfan g hg with ⟨hop, hlen⟩
    exact ⟨by simpa using hop, hlen⟩
  have hbound := markov_drops_bound xs hxs_len hxs_mono C.gates hfan'
  rw [hdrops_all, Finset.card_univ, Fintype.card_fin] at hbound
  have hnc_eq : notCount ⟨C.gates, 0⟩ = notCount C := rfl
  rw [hnc_eq] at hbound
  omega

end PEqualNP.Outside.L_clb_067_aux

theorem PEqualNP.Outside.L_clb_067 :
∀ (n w : ℕ) (hn : 0 < n) (q : Fin (2 ^ n)),
  let I := n * 2 ^ (w + 1)
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin n → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C →
    (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := (List.ofFn (fun i : Fin n => List.ofFn (fun pat : Fin (2 ^ (w + 1)) =>
        table i (fun j => pat.val.testBit j.val)))).flatten
      let sols := (Finset.univ : Finset (Fin (2 ^ n))).filter (fun z => ∀ i : Fin n,
        table i (fun j => z.val.testBit (n - 1 - ((i.val + j.val) % n))) = true)
      q.val < sols.card → ∃ z ∈ sols,
        (sols.filter (fun y => y.val < z.val)).card = q.val ∧
        ∀ pos : Fin n, (C.wires inputs).getD (outBit pos).val false =
          z.val.testBit (n - 1 - pos.val)) →
    ∀ k b : ℕ, 0 < k → k ≤ w + 1 → k + b ≤ n → q.val < 2 ^ (k + b) →
      1 + ((n - b) / k) * (2 ^ k - 1) - q.val / 2 ^ b ≤
        2 ^ PEqualNP.NotBracket.notCount C :=
  PEqualNP.Outside.L_clb_067_aux.main_proof
