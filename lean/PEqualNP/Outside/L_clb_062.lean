import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_062_aux

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

lemma evalWires_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (evalWires (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false) := by
  rw [evalWires_append]
  unfold evalWires
  simp only [List.foldl_cons, List.foldl_nil]
  rw [← evalWires_length gs x]
  exact getD_append_singleton_last (evalWires gs x) _ false

lemma getD_of_le {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD, List.getElem?_eq_none hi]

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

def Mid (k : ℕ) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun u : Fin k → Bool =>
    (Finset.univ.filter (fun j : Fin k => u j = true)).card = k / 2)

lemma card_Mid (k : ℕ) : (Mid k).card = Nat.choose k (k / 2) := by
  have hbij : (Mid k).card = (Finset.powersetCard (k / 2) (Finset.univ : Finset (Fin k))).card := by
    apply Finset.card_bij (fun u _ => Finset.univ.filter (fun j : Fin k => u j = true))
    · intro u hu
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hu).2⟩
    · intro u₁ _ u₂ _ heq
      funext j
      have hj := Finset.ext_iff.mp heq j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      cases h1 : u₁ j <;> cases h2 : u₂ j <;> simp_all
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      refine ⟨fun j => decide (j ∈ S), ?_, ?_⟩
      · simp only [Mid, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
        have heq : Finset.univ.filter (fun j : Fin k => j ∈ S) = S := by ext j; simp
        rw [heq]; exact hS.2
      · ext j; simp
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma Mid_incomparable {k : ℕ} {u v : Fin k → Bool}
    (hu : u ∈ Mid k) (hv : v ∈ Mid k) (hne : u ≠ v) :
    ∃ j : Fin k, v j = true ∧ u j = false := by
  by_contra hall
  push Not at hall
  have hsub : Finset.univ.filter (fun j : Fin k => v j = true) ⊆
      Finset.univ.filter (fun j : Fin k => u j = true) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    cases h : u j
    · exact absurd h (hall j hj)
    · rfl
  have hcu : (Finset.univ.filter (fun j : Fin k => u j = true)).card = k / 2 :=
    (Finset.mem_filter.mp hu).2
  have hcv : (Finset.univ.filter (fun j : Fin k => v j = true)).card = k / 2 :=
    (Finset.mem_filter.mp hv).2
  have heq_set : Finset.univ.filter (fun j : Fin k => v j = true) =
      Finset.univ.filter (fun j : Fin k => u j = true) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  apply hne
  funext j
  have hj := Finset.ext_iff.mp heq_set j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  cases h1 : u j <;> cases h2 : v j <;> simp_all

lemma main_proof (n w k : ℕ) (hn : 0 < n) (hk0 : 0 < k) (hkn : k ≤ n) (hkw : k ≤ w + 1) :
    let stride := 2 ^ (w + 1)
    let I := n * stride
    ∀ (C : Circuit) (outBit : Fin n → Fin (I + C.size)),
      FanInTwo C →
      ReadsBack I C →
      (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        let inputs := List.ofFn (fun addr : Fin I =>
          table ⟨(addr.val / stride) % n, Nat.mod_lt _ hn⟩ (fun b => addr.val.testBit b.val))
        let valid := fun (word : Fin n → Bool) => ∀ i : Fin n,
          table i (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true
        (∃ word, valid word) →
          valid (fun pos => (C.wires inputs).getD (outBit pos).val false)) →
      1 + (n / k) * (Nat.choose k (k / 2) - 1) ≤ 2 ^ notCount C := by
  intro stride I C outBit hfan _hreads hsel
  set B := n / k
  set M := Nat.choose k (k / 2)
  have hM_pos : 0 < M := Nat.choose_pos (Nat.div_le_self k 2)
  by_cases hM1 : M ≤ 1
  · have hsub : M - 1 = 0 := by omega
    rw [hsub, Nat.mul_zero, Nat.add_zero]
    exact Nat.one_le_two_pow
  · have hM2 : 2 ≤ M := by omega
    have hBk_le : B * k ≤ n := Nat.div_mul_le_self n k
    let mkTable : (Fin B → Finset (Fin k → Bool)) → Fin n → (Fin (w + 1) → Bool) → Bool :=
      fun S i pat =>
        if h : i.val % k = 0 ∧ i.val / k < B then
          decide ((fun j : Fin k => pat ⟨j.val, by have := j.isLt; omega⟩) ∈ S ⟨i.val / k, h.2⟩)
        else true
    let mkInputs : (Fin B → Finset (Fin k → Bool)) → List Bool := fun S =>
      List.ofFn (fun addr : Fin I =>
        mkTable S ⟨(addr.val / stride) % n, Nat.mod_lt _ hn⟩ (fun b => addr.val.testBit b.val))
    let outWord : (Fin B → Finset (Fin k → Bool)) → Fin n → Bool := fun S pos =>
      (C.wires (mkInputs S)).getD (outBit pos).val false
    let slice : (Fin n → Bool) → Fin B → (Fin k → Bool) := fun word b j =>
      word ⟨b.val * k + j.val, by
        have hb := b.isLt; have hj := j.isLt
        have : (b.val + 1) * k ≤ B * k := Nat.mul_le_mul_right k (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega⟩
    have hmk_sat : ∀ S : Fin B → Finset (Fin k → Bool),
        (∀ b, (S b).Nonempty) →
        ∃ word : Fin n → Bool, ∀ i : Fin n,
          mkTable S i (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true := by
      intro S hne
      choose pick hpick using hne
      refine ⟨fun pos =>
        if h : pos.val / k < B then
          pick ⟨pos.val / k, h⟩ ⟨pos.val % k, Nat.mod_lt _ hk0⟩
        else false, fun i => ?_⟩
      dsimp only [mkTable]
      by_cases hi : i.val % k = 0 ∧ i.val / k < B
      · simp only [hi, and_self, ↓reduceDIte, decide_eq_true_eq]
        have heq_fn : (fun j : Fin k =>
            if h : ((i.val + j.val) % n) / k < B then
              pick ⟨((i.val + j.val) % n) / k, h⟩ ⟨((i.val + j.val) % n) % k, Nat.mod_lt _ hk0⟩
            else false) = pick ⟨i.val / k, hi.2⟩ := by
          funext j
          have hj := j.isLt
          have hib : i.val = (i.val / k) * k := by
            have := (Nat.div_add_mod i.val k).symm
            rw [hi.1, Nat.add_zero, Nat.mul_comm] at this
            exact this
          have hlt_n : i.val + j.val < n := by
            have : (i.val / k + 1) * k ≤ B * k := Nat.mul_le_mul_right k (by omega)
            rw [Nat.add_mul, Nat.one_mul] at this
            omega
          have hmod_n : (i.val + j.val) % n = k * (i.val / k) + j.val := by
            rw [Nat.mod_eq_of_lt hlt_n]
            conv_lhs => rw [hib, Nat.mul_comm]
          have hdiv_k : ((i.val + j.val) % n) / k = i.val / k := by
            rw [hmod_n, Nat.mul_add_div hk0, Nat.div_eq_of_lt hj, Nat.add_zero]
          have hmod_k : ((i.val + j.val) % n) % k = j.val := by
            rw [hmod_n, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
          have hlt_B : ((i.val + j.val) % n) / k < B := by rw [hdiv_k]; exact hi.2
          simp only [hlt_B, ↓reduceDIte]
          have h1 : (⟨((i.val + j.val) % n) / k, hlt_B⟩ : Fin B) = ⟨i.val / k, hi.2⟩ :=
            Fin.ext hdiv_k
          have h2 : (⟨((i.val + j.val) % n) % k, Nat.mod_lt _ hk0⟩ : Fin k) = j :=
            Fin.ext hmod_k
          rw [h1, h2]
        have hgoal : (fun j : Fin k =>
            (fun pos : Fin n =>
              if h : pos.val / k < B then
                pick ⟨pos.val / k, h⟩ ⟨pos.val % k, Nat.mod_lt _ hk0⟩
              else false) ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) ∈ S ⟨i.val / k, hi.2⟩ := by
          dsimp only
          rw [heq_fn]
          exact hpick ⟨i.val / k, hi.2⟩
        exact hgoal
      · simp [hi]
    have hslice_mem : ∀ S : Fin B → Finset (Fin k → Bool),
        (∀ b, (S b).Nonempty) → ∀ b : Fin B, slice (outWord S) b ∈ S b := by
      intro S hne b
      have hvalid := hsel (mkTable S) (hmk_sat S hne)
      have hb := b.isLt
      have hbk_lt : b.val * k < n := by
        have : (b.val + 1) * k ≤ B * k := Nat.mul_le_mul_right k (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      let i0 : Fin n := ⟨b.val * k, hbk_lt⟩
      have hv0 := hvalid i0
      have hi0_mod : i0.val % k = 0 := Nat.mul_mod_left b.val k
      have hi0_div : i0.val / k = b.val := Nat.mul_div_cancel b.val hk0
      have hi0_cond : i0.val % k = 0 ∧ i0.val / k < B := ⟨hi0_mod, by rw [hi0_div]; exact hb⟩
      dsimp only [mkTable] at hv0
      simp only [hi0_cond, and_self, ↓reduceDIte, decide_eq_true_eq] at hv0
      have hfb : (⟨i0.val / k, hi0_cond.2⟩ : Fin B) = b := Fin.ext hi0_div
      rw [hfb] at hv0
      have heq_sl : slice (outWord S) b =
          fun j : Fin k => outWord S ⟨(i0.val + j.val) % n, Nat.mod_lt _ hn⟩ := by
        funext j
        dsimp only [slice]
        congr 1
        apply Fin.ext
        have hj := j.isLt
        have hlt_n : b.val * k + j.val < n := by
          have : (b.val + 1) * k ≤ B * k := Nat.mul_le_mul_right k (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        exact (Nat.mod_eq_of_lt hlt_n).symm
      rw [heq_sl]
      exact hv0
    set L := B * (M - 1)
    let nextS : ℕ → (Fin B → Finset (Fin k → Bool)) → (Fin B → Finset (Fin k → Bool)) :=
      fun t S =>
        if h : t / (M - 1) < B then
          let b : Fin B := ⟨t / (M - 1), h⟩
          fun b' => if b' = b then (S b).erase (slice (outWord S) b) else S b'
        else S
    let chain : ℕ → (Fin B → Finset (Fin k → Bool)) :=
      Nat.rec (fun _ => Mid k) nextS
    have hchain_spec : ∀ t : ℕ, t ≤ L →
        (∀ b : Fin B, chain t b ⊆ Mid k) ∧
        (∀ b : Fin B, (chain t b).card =
          if b.val < t / (M - 1) then 1
          else if b.val = t / (M - 1) then M - t % (M - 1)
          else M) := by
      intro t
      induction t with
      | zero =>
        intro _
        refine ⟨fun _ => Finset.Subset.rfl, fun b => ?_⟩
        have h0 : 0 / (M - 1) = 0 := Nat.zero_div _
        have hm0 : 0 % (M - 1) = 0 := Nat.zero_mod _
        simp only [chain, h0, hm0, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
        split_ifs <;> exact card_Mid k
      | succ t ih =>
        intro ht
        rcases ih (by omega) with ⟨hsub, hcard⟩
        have ht_lt : t < L := by omega
        have hM1_pos : 0 < M - 1 := by omega
        have hdiv_lt : t / (M - 1) < B := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        let b0 : Fin B := ⟨t / (M - 1), hdiv_lt⟩
        have hne_t : ∀ b : Fin B, (chain t b).Nonempty := by
          intro b
          apply Finset.card_pos.mp
          rw [hcard b]
          have hmod_lt := Nat.mod_lt t hM1_pos
          split_ifs <;> omega
        have hstep_eq : chain (t + 1) =
            fun b' => if b' = b0 then (chain t b0).erase (slice (outWord (chain t)) b0) else chain t b' := by
          change nextS t (chain t) = _
          simp only [nextS, hdiv_lt, ↓reduceDIte, b0]
        refine ⟨?_, ?_⟩
        · intro b
          rw [hstep_eq]
          by_cases hbb : b = b0
          · subst hbb; simp only [↓reduceIte]; exact Finset.Subset.trans (Finset.erase_subset _ _) (hsub b0)
          · simp only [hbb, ↓reduceIte]; exact hsub b
        · intro b
          rw [hstep_eq]
          have hmem_sl : slice (outWord (chain t)) b0 ∈ chain t b0 := hslice_mem (chain t) hne_t b0
          have hmod_lt := Nat.mod_lt t hM1_pos
          by_cases hwrap : t % (M - 1) + 1 = M - 1
          · have hdiv_s : (t + 1) / (M - 1) = t / (M - 1) + 1 := by
              have hdm : t + 1 = (t / (M - 1) + 1) * (M - 1) := by
                have := (Nat.div_add_mod t (M - 1)).symm
                rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (t / (M - 1))]
                omega
              rw [hdm, Nat.mul_div_cancel _ hM1_pos]
            have hmod_s : (t + 1) % (M - 1) = 0 := by
              have hdm : t + 1 = (t / (M - 1) + 1) * (M - 1) := by
                have := (Nat.div_add_mod t (M - 1)).symm
                rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (t / (M - 1))]
                omega
              rw [hdm, Nat.mul_mod_left]
            by_cases hbb : b = b0
            · subst hbb
              simp only [↓reduceIte, Finset.card_erase_of_mem hmem_sl, hcard b0, b0,
                lt_irrefl, hdiv_s, hmod_s]
              have : t / (M - 1) < t / (M - 1) + 1 := by omega
              simp only [this, ↓reduceIte]
              omega
            · simp only [hbb, ↓reduceIte, hcard b, hdiv_s, hmod_s]
              have hne_val : b.val ≠ t / (M - 1) := fun h => hbb (Fin.ext h)
              split_ifs <;> omega
          · have hdiv_s : (t + 1) / (M - 1) = t / (M - 1) := by
              have hdm : t + 1 = (M - 1) * (t / (M - 1)) + (t % (M - 1) + 1) := by
                have := (Nat.div_add_mod t (M - 1)).symm; omega
              have hlt' : t % (M - 1) + 1 < M - 1 := by omega
              rw [hdm, Nat.mul_add_div hM1_pos, Nat.div_eq_of_lt hlt', Nat.add_zero]
            have hmod_s : (t + 1) % (M - 1) = t % (M - 1) + 1 := by
              have hdm : t + 1 = (M - 1) * (t / (M - 1)) + (t % (M - 1) + 1) := by
                have := (Nat.div_add_mod t (M - 1)).symm; omega
              have hlt' : t % (M - 1) + 1 < M - 1 := by omega
              rw [hdm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt']
            by_cases hbb : b = b0
            · subst hbb
              simp only [↓reduceIte, Finset.card_erase_of_mem hmem_sl, hcard b0, b0,
                lt_irrefl, hdiv_s, hmod_s]
              omega
            · simp only [hbb, ↓reduceIte, hcard b, hdiv_s, hmod_s]
              have hne_val : b.val ≠ t / (M - 1) := fun h => hbb (Fin.ext h)
              split_ifs <;> omega
    let xs : Fin (L + 1) → List Bool := fun r => mkInputs (chain (L - r.val))
    have hxs_len : ∀ r : Fin (L + 1), (xs r).length = I := by
      intro r; simp [xs, mkInputs]
    have hxs_mono : ∀ r : Fin L, ∀ idx < I,
        (xs r.castSucc).getD idx false = true → (xs r.succ).getD idx false = true := by
      intro r idx hidx htr
      have hr := r.isLt
      set t := L - 1 - r.val
      have ht_lt : t < L := by omega
      have heq1 : L - r.castSucc.val = t + 1 := by simp only [Fin.val_castSucc]; omega
      have heq2 : L - r.succ.val = t := by simp only [Fin.val_succ]; omega
      have hsub_chain : ∀ b : Fin B, chain (t + 1) b ⊆ chain t b := by
        intro b
        change nextS t (chain t) b ⊆ chain t b
        dsimp only [nextS]
        by_cases h1 : t / (M - 1) < B
        · simp only [h1, ↓reduceDIte]
          by_cases h2 : b = ⟨t / (M - 1), h1⟩
          · simp only [h2, ↓reduceIte]; exact Finset.erase_subset _ _
          · simp only [h2, ↓reduceIte]; exact Finset.Subset.rfl
        · simp only [h1, ↓reduceDIte]; exact Finset.Subset.rfl
      dsimp only [xs, mkInputs] at htr ⊢
      rw [heq1] at htr
      rw [heq2]
      rw [List.getD_eq_getElem _ _ (by simp [hidx]), List.getElem_ofFn] at htr
      rw [List.getD_eq_getElem _ _ (by simp [hidx]), List.getElem_ofFn]
      dsimp only [mkTable] at htr ⊢
      split_ifs at htr ⊢ with hc
      · simp only [decide_eq_true_eq] at htr ⊢
        exact hsub_chain _ htr
      · rfl
    have hdrops_all : drops (I := I) xs C.gates = Finset.univ := by
      ext r
      simp only [drops, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have hr := r.isLt
      set t := L - 1 - r.val
      have ht_lt : t < L := by omega
      have hM1_pos : 0 < M - 1 := by omega
      have hdiv_lt : t / (M - 1) < B := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      let b0 : Fin B := ⟨t / (M - 1), hdiv_lt⟩
      have hne_t : ∀ b : Fin B, (chain t b).Nonempty := by
        intro b
        apply Finset.card_pos.mp
        rw [(hchain_spec t (by omega)).2 b]
        have := Nat.mod_lt t hM1_pos
        split_ifs <;> omega
      have hne_ts : ∀ b : Fin B, (chain (t + 1) b).Nonempty := by
        intro b
        apply Finset.card_pos.mp
        rw [(hchain_spec (t + 1) (by omega)).2 b]
        have := Nat.mod_lt (t + 1) hM1_pos
        split_ifs <;> omega
      set u0 := slice (outWord (chain t)) b0
      set u1 := slice (outWord (chain (t + 1))) b0
      have hu0_mem : u0 ∈ chain t b0 := hslice_mem (chain t) hne_t b0
      have hu1_mem : u1 ∈ chain (t + 1) b0 := hslice_mem (chain (t + 1)) hne_ts b0
      have hu0_mid : u0 ∈ Mid k := (hchain_spec t (by omega)).1 b0 hu0_mem
      have hu1_mid : u1 ∈ Mid k := (hchain_spec (t + 1) (by omega)).1 b0 hu1_mem
      have hne_u : u0 ≠ u1 := by
        intro heq
        have hstep : chain (t + 1) b0 = (chain t b0).erase u0 := by
          change nextS t (chain t) b0 = _
          simp only [nextS, hdiv_lt, ↓reduceDIte, b0, ↓reduceIte, u0]
        rw [hstep, ← heq] at hu1_mem
        exact (Finset.mem_erase.mp hu1_mem).1 rfl
      rcases Mid_incomparable hu0_mid hu1_mid hne_u with ⟨j, hj1, hj0⟩
      let pos : Fin n := ⟨b0.val * k + j.val, by
        have hb := b0.isLt; have hj := j.isLt
        have : (b0.val + 1) * k ≤ B * k := Nat.mul_le_mul_right k (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega⟩
      have heq1 : L - r.castSucc.val = t + 1 := by simp only [Fin.val_castSucc]; omega
      have heq2 : L - r.succ.val = t := by simp only [Fin.val_succ]; omega
      refine ⟨(outBit pos).val, (outBit pos).isLt, ?_, ?_⟩
      · change (C.wires (mkInputs (chain (L - r.castSucc.val)))).getD (outBit pos).val false = true
        rw [heq1]
        exact hj1
      · change (C.wires (mkInputs (chain (L - r.succ.val)))).getD (outBit pos).val false = false
        rw [heq2]
        exact hj0
    have hfan' : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      rcases hfan g hg with ⟨hop, hlen⟩
      exact ⟨by simpa using hop, hlen⟩
    have hbound := markov_drops_bound xs hxs_len hxs_mono C.gates hfan'
    rw [hdrops_all, Finset.card_univ, Fintype.card_fin] at hbound
    have hnc_eq : notCount ⟨C.gates, 0⟩ = notCount C := rfl
    rw [hnc_eq] at hbound
    omega

end PEqualNP.Outside.L_clb_062_aux

theorem PEqualNP.Outside.L_clb_062 :
∀ (n w k : ℕ) (hn : 0 < n), 0 < k → k ≤ n → k ≤ w + 1 →
  let stride := 2 ^ (w + 1)
  let I := n * stride
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (outBit : Fin n → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C →
    (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun addr : Fin I =>
        table ⟨(addr.val / stride) % n, Nat.mod_lt _ hn⟩ (fun b => addr.val.testBit b.val))
      let valid := fun (word : Fin n → Bool) => ∀ i : Fin n,
        table i (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true
      (∃ word, valid word) →
        valid (fun pos => (C.wires inputs).getD (outBit pos).val false)) →
    1 + (n / k) * (Nat.choose k (k / 2) - 1) ≤ 2 ^ PEqualNP.NotBracket.notCount C :=
  PEqualNP.Outside.L_clb_062_aux.main_proof
