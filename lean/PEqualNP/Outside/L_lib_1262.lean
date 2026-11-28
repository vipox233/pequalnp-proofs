import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1262

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

def nc (gs : List Gate) : ℕ := notCount ⟨gs, 0⟩

lemma nc_append (a b : List Gate) : nc (a ++ b) = nc a + nc b := by
  simp [nc, notCount, List.filter_append]

lemma nc_and (l : List ℕ) : nc [⟨GateOp.and, l⟩] = 0 := by simp [nc, notCount]
lemma nc_or (l : List ℕ) : nc [⟨GateOp.or, l⟩] = 0 := by simp [nc, notCount]
lemma nc_not (l : List ℕ) : nc [⟨GateOp.not, l⟩] = 1 := by simp [nc, notCount]

def Ok (I : ℕ) (gs : List Gate) : Prop := FanInTwo ⟨gs, 0⟩ ∧ ReadsBack I ⟨gs, 0⟩

lemma ok_nil (I : ℕ) : Ok I [] := by
  refine ⟨?_, ?_⟩
  · intro g hg; simp at hg
  · intro j hj; simp at hj

lemma ok_snoc {I : ℕ} {gs : List Gate} {g : Gate} (h : Ok I gs)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < I + gs.length) : Ok I (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact h.1 g' hg'
    · refine ⟨?_, hlen⟩
      rcases hop with hop | hop | hop <;> simp [hop]
  · intro j hj i hi
    have h2 := h.2
    simp only [List.length_append, List.length_singleton] at hj
    unfold gateAt at hi
    by_cases hjl : j < gs.length
    · have : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
        getD_append_left _ _ _ hjl
      rw [this] at hi
      exact h2 j hjl i hi
    · have hj' : j = gs.length := by omega
      subst hj'
      have : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := getD_append_singleton_last _ _ _
      rw [this] at hi
      exact hin i hi

lemma evalWires_getD_lt (hs : List Gate) (y : List Bool) {i : ℕ} (hi : i < y.length) :
    (evalWires hs y).getD i false = y.getD i false := by
  induction hs generalizing y with
  | nil => rfl
  | cons g hs ih =>
    simp only [evalWires, List.foldl_cons]
    have := ih (y ++ [g.op.eval (g.inputs.map fun k => y.getD k false)]) (by simp; omega)
    unfold evalWires at this
    rw [this]
    exact getD_append_left _ _ _ hi

section Build
variable {X : Type*} {I : ℕ} {inp : X → List Bool}

def V (inp : X → List Bool) (gs : List Gate) (x : X) (w : ℕ) : Bool :=
  (evalWires gs (inp x)).getD w false

def Carries (I : ℕ) (inp : X → List Bool) (gs : List Gate) (w : ℕ) (φ : X → Bool) : Prop :=
  w < I + gs.length ∧ ∀ x, V inp gs x w = φ x

lemma carries_congr {gs : List Gate} {w : ℕ} {φ ψ : X → Bool} (h : Carries I inp gs w φ)
    (he : ∀ x, φ x = ψ x) : Carries I inp gs w ψ :=
  ⟨h.1, fun x => (h.2 x).trans (he x)⟩

lemma carries_ext (hI : ∀ x, (inp x).length = I) {gs : List Gate} {w : ℕ} {φ : X → Bool}
    (h : Carries I inp gs w φ) (hs : List Gate) : Carries I inp (gs ++ hs) w φ := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  unfold V
  rw [evalWires_append, evalWires_getD_lt _ _ (by rw [evalWires_length, hI]; exact h.1)]
  exact h.2 x

lemma carries_pre (hI : ∀ x, (inp x).length = I) {gs gs' : List Gate} {w : ℕ} {φ : X → Bool}
    (h : Carries I inp gs w φ) (hp : gs <+: gs') : Carries I inp gs' w φ := by
  obtain ⟨hs, rfl⟩ := hp
  exact carries_ext hI h hs

lemma carries_input (hI : ∀ x, (inp x).length = I) (gs : List Gate) {i : ℕ} (hi : i < I) :
    Carries I inp gs i (fun x => (inp x).getD i false) := by
  refine ⟨by omega, fun x => ?_⟩
  unfold V
  rw [evalWires_getD_lt _ _ (by rw [hI]; exact hi)]

lemma V_snoc (hI : ∀ x, (inp x).length = I) (gs : List Gate) (g : Gate) (x : X) :
    V inp (gs ++ [g]) x (I + gs.length) = g.op.eval (g.inputs.map (V inp gs x)) := by
  unfold V
  rw [← hI x]
  exact evalWires_snoc_last gs g (inp x)

lemma add2 (hI : ∀ x, (inp x).length = I) {gs : List Gate} {p q : ℕ} {φ ψ : X → Bool}
    {op : GateOp} (hop : op = .and ∨ op = .or) (hok : Ok I gs)
    (hp : Carries I inp gs p φ) (hq : Carries I inp gs q ψ) :
    Ok I (gs ++ [⟨op, [p, q]⟩]) ∧ nc [⟨op, [p, q]⟩] = 0 ∧
      Carries I inp (gs ++ [⟨op, [p, q]⟩]) (I + gs.length) (fun x => op.eval [φ x, ψ x]) := by
  refine ⟨ok_snoc hok (by rcases hop with h | h <;> simp [h]) (by simp) ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hp.1
    · exact hq.1
  · rcases hop with rfl | rfl
    · exact nc_and _
    · exact nc_or _
  · simp
  · intro x
    rw [V_snoc hI]
    simp [hp.2 x, hq.2 x]

lemma addNot (hI : ∀ x, (inp x).length = I) {gs : List Gate} {p : ℕ} {φ : X → Bool}
    (hok : Ok I gs) (hp : Carries I inp gs p φ) :
    Ok I (gs ++ [⟨GateOp.not, [p]⟩]) ∧ nc [⟨GateOp.not, [p]⟩] = 1 ∧
      Carries I inp (gs ++ [⟨GateOp.not, [p]⟩]) (I + gs.length) (fun x => !φ x) := by
  refine ⟨ok_snoc hok (by simp) (by simp) ?_, nc_not _, by simp, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi; exact hp.1
  · intro x
    rw [V_snoc hI]
    simp [hp.2 x, GateOp.eval]

lemma chain (hI : ∀ x, (inp x).length = I) {β : Type*} (op : GateOp) (hop : op = .and ∨ op = .or)
    (wf : β → ℕ) (ψ : β → X → Bool) :
    ∀ (l : List β) (gs : List Gate) (acc : ℕ) (φ0 : X → Bool), Ok I gs →
      Carries I inp gs acc φ0 → (∀ b ∈ l, Carries I inp gs (wf b) (ψ b)) →
      ∃ hs, Ok I (gs ++ hs) ∧ nc hs = 0 ∧ hs.length = l.length ∧ ∃ w,
        Carries I inp (gs ++ hs) w (fun x => l.foldl (fun a b => op.eval [a, ψ b x]) (φ0 x)) := by
  intro l
  induction l with
  | nil =>
    intro gs acc φ0 hok hacc _
    exact ⟨[], by simpa using hok, rfl, rfl, acc, by simpa using hacc⟩
  | cons b l ih =>
    intro gs acc φ0 hok hacc hl
    obtain ⟨hok1, hnc1, hw1⟩ := add2 hI hop hok hacc (hl b (List.mem_cons_self ..))
    obtain ⟨hs, hok2, hnc2, hlen2, w, hw⟩ := ih (gs ++ [⟨op, [acc, wf b]⟩]) (I + gs.length) _ hok1
      hw1 (fun b' hb' => carries_ext hI (hl b' (List.mem_cons_of_mem _ hb')) _)
    refine ⟨[⟨op, [acc, wf b]⟩] ++ hs, ?_, ?_, by simp [hlen2], w, ?_⟩
    · rw [← List.append_assoc]; exact hok2
    · rw [nc_append, hnc1, hnc2]
    · rw [← List.append_assoc]; exact hw

lemma foldl_and {β : Type*} (ψ : β → Bool) :
    ∀ (l : List β) (a : Bool), l.foldl (fun a b => GateOp.and.eval [a, ψ b]) a = (a && l.all ψ)
  | [], a => by simp
  | b :: l, a => by
    rw [List.foldl_cons, foldl_and ψ l]
    simp [GateOp.eval, Bool.and_assoc]

lemma foldl_or {β : Type*} (ψ : β → Bool) :
    ∀ (l : List β) (a : Bool), l.foldl (fun a b => GateOp.or.eval [a, ψ b]) a = (a || l.any ψ)
  | [], a => by simp
  | b :: l, a => by
    rw [List.foldl_cons, foldl_or ψ l]
    simp [GateOp.eval, Bool.or_assoc]

lemma many (hI : ∀ x, (inp x).length = I) {β : Type*} (c : ℕ) (φ : β → X → Bool)
    (gs : List Gate) (hok : Ok I gs) :
    ∀ (L : List β), (∀ hs0, Ok I (gs ++ hs0) → ∀ b ∈ L, ∃ hs, Ok I (gs ++ hs0 ++ hs) ∧ nc hs = 0 ∧
      hs.length ≤ c ∧ ∃ w, Carries I inp (gs ++ hs0 ++ hs) w (φ b)) →
    ∃ hs, Ok I (gs ++ hs) ∧ nc hs = 0 ∧ hs.length ≤ c * L.length ∧
      ∃ wf : β → ℕ, ∀ b ∈ L, Carries I inp (gs ++ hs) (wf b) (φ b) := by
  classical
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨[], by simpa using hok, rfl, by simp, fun _ => 0, by simp⟩
  | cons b L ih =>
    intro hstep
    obtain ⟨hs1, ok1, nc1, len1, wf, hwf⟩ :=
      ih (fun hs0 h b' hb' => hstep hs0 h b' (List.mem_cons_of_mem _ hb'))
    obtain ⟨hs2, ok2, nc2, len2, w, hw⟩ := hstep hs1 ok1 b (List.mem_cons_self ..)
    refine ⟨hs1 ++ hs2, by rw [← List.append_assoc]; exact ok2, by rw [nc_append, nc1, nc2],
      ?_, fun b' => if b' = b then w else wf b', ?_⟩
    · simp only [List.length_append, List.length_cons, Nat.mul_succ]; omega
    · intro b' hb'
      by_cases hbb : b' = b
      · subst hbb; simp only [ite_true]; rw [← List.append_assoc]; exact hw
      · simp only [hbb, ite_false]
        have hb'' : b' ∈ L := by
          rcases List.mem_cons.mp hb' with h | h
          · exact absurd h hbb
          · exact h
        rw [← List.append_assoc]
        exact carries_ext hI (hwf b' hb'') _

end Build

def nb : ℕ → ℕ
  | 0 => 0
  | m + 1 => nb ((m + 1) / 2) + 1
decreasing_by omega

lemma nb_succ (m : ℕ) : nb (m + 1) = nb ((m + 1) / 2) + 1 := by
  rw [nb]

lemma nb_le : ∀ r m : ℕ, m < 2 ^ r → nb m ≤ r
  | 0, m, h => by
    have : m = 0 := by simpa using h
    subst this; simp [nb]
  | r + 1, m, h => by
    rcases m with _ | m
    · simp [nb]
    · rw [nb_succ]
      have := nb_le r ((m + 1) / 2) (by rw [pow_succ] at h; omega)
      omega

section Inv
variable {X : Type*} {I : ℕ} {inp : X → List Bool}

lemma inv (hI : ∀ x, (inp x).length = I) (z : ℕ) :
    ∀ (m : ℕ) (gs : List Gate) (a : ℕ → ℕ) (ρ : X → ℕ), Ok I gs →
      Carries I inp gs z (fun _ => false) → (∀ x, ρ x ≤ m) →
      (∀ i < m, Carries I inp gs (a i) (fun x => decide (i < ρ x))) →
      ∃ hs, Ok I (gs ++ hs) ∧ nc hs ≤ nb m ∧ hs.length ≤ nc hs + 4 * m ∧
        ∃ b : ℕ → ℕ, ∀ i < m, Carries I inp (gs ++ hs) (b i) (fun x => decide (ρ x ≤ i)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro gs a ρ hok hz hρ ha
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨[], by simpa using hok, by simp [nc, notCount], by simp, a, fun i hi => absurd hi (by omega)⟩
  set h := m / 2 with hh
  have hhm : h < m := by omega

  obtain ⟨ok1, nc1, hc⟩ := addNot hI hok (ha h hhm)
  set gs1 := gs ++ [⟨GateOp.not, [a h]⟩] with hgs1
  set c := I + gs.length with hcdef
  have hc' : Carries I inp gs1 c (fun x => decide (ρ x ≤ h)) :=
    carries_congr hc (fun x => Bool.eq_iff_iff.mpr (by simp))

  set ρ' : X → ℕ := fun x => if ρ x ≤ h then ρ x else ρ x - h - 1 with hρ'
  obtain ⟨hs2, ok2, nc2, len2, d, hd⟩ := many hI 2 (fun i x => decide (i < ρ' x)) gs1 ok1
    (List.range h) (by
      intro hs0 hok0 i hi
      have hi' : i < h := List.mem_range.mp hi
      have hai : Carries I inp (gs1 ++ hs0) (a i) (fun x => decide (i < ρ x)) :=
        carries_ext hI (carries_ext hI (ha i (by omega)) _) _
      have hc0 : Carries I inp (gs1 ++ hs0) c (fun x => decide (ρ x ≤ h)) := carries_ext hI hc' _
      have hpad : Carries I inp (gs1 ++ hs0) (if h + 1 + i < m then a (h + 1 + i) else z)
          (fun x => decide (h + 1 + i < ρ x)) := by
        split_ifs with hlt
        · exact carries_ext hI (carries_ext hI (ha _ hlt) _) _
        · refine carries_congr (carries_ext hI (carries_ext hI hz _) _) (fun x => ?_)
          have := hρ x
          simp only [Bool.false_eq, decide_eq_false_iff_not, not_lt]
          omega
      obtain ⟨okA, ncA, hA⟩ := add2 hI (Or.inl rfl) hok0 hai hc0
      obtain ⟨okB, ncB, hB⟩ := add2 hI (Or.inr rfl) okA hA (carries_ext hI hpad _)
      refine ⟨[⟨GateOp.and, [a i, c]⟩] ++ [⟨GateOp.or, [I + (gs1 ++ hs0).length,
        if h + 1 + i < m then a (h + 1 + i) else z]⟩], ?_, ?_, by simp,
        I + (gs1 ++ hs0 ++ [(⟨GateOp.and, [a i, c]⟩ : Gate)]).length, ?_⟩
      · rw [← List.append_assoc]; exact okB
      · rw [nc_append, ncA, ncB]
      · rw [← List.append_assoc]
        refine carries_congr hB (fun x => ?_)
        have := hρ x
        by_cases hx : ρ x ≤ h
        · simp only [hρ', hx, ite_true]
          simp [GateOp.eval]
          omega
        · simp only [hρ', hx, ite_false]
          simp [GateOp.eval]
          omega)

  have hh2 : h < m := hhm
  obtain ⟨hs3, ok3, nc3, len3, nd, hnd⟩ := ih h hh2 (gs1 ++ hs2) d ρ' ok2
    (carries_ext hI (carries_ext hI hz _) _)
    (fun x => by
      have := hρ x
      simp only [hρ']
      split_ifs <;> omega)
    (fun i hi => hd i (List.mem_range.mpr hi))

  set gs3 := gs1 ++ hs2 ++ hs3 with hgs3
  obtain ⟨hs4, ok4, nc4, len4, b, hb⟩ := many hI 1 (fun i x => decide (ρ x ≤ i)) gs3 ok3
    (List.range m) (by
      intro hs0 hok0 i hi
      have hi' : i < m := List.mem_range.mp hi
      have hc0 : Carries I inp (gs3 ++ hs0) c (fun x => decide (ρ x ≤ h)) :=
        carries_ext hI (carries_ext hI (carries_ext hI hc' _) _) _
      rcases lt_trichotomy i h with hlt | heq | hgt
      · have hn : Carries I inp (gs3 ++ hs0) (nd i) (fun x => decide (ρ' x ≤ i)) :=
          carries_ext hI (hnd i hlt) _
        obtain ⟨okA, ncA, hA⟩ := add2 hI (Or.inl rfl) hok0 hc0 hn
        refine ⟨_, okA, ncA, by simp, _, carries_congr hA (fun x => ?_)⟩
        have := hρ x
        by_cases hx : ρ x ≤ h
        · simp only [hρ', hx, ite_true]; simp [GateOp.eval]
        · simp only [hρ', hx, ite_false]; simp [GateOp.eval]; omega
      · subst heq
        obtain ⟨okA, ncA, hA⟩ := add2 hI (Or.inl rfl) hok0 hc0 hc0
        exact ⟨_, okA, ncA, by simp, _, carries_congr hA (fun x => by simp [GateOp.eval])⟩
      · have hn : Carries I inp (gs3 ++ hs0) (nd (i - h - 1)) (fun x => decide (ρ' x ≤ i - h - 1)) :=
          carries_ext hI (hnd (i - h - 1) (by omega)) _
        obtain ⟨okA, ncA, hA⟩ := add2 hI (Or.inr rfl) hok0 hc0 hn
        refine ⟨_, okA, ncA, by simp, _, carries_congr hA (fun x => ?_)⟩
        have := hρ x
        by_cases hx : ρ x ≤ h
        · simp only [hρ', hx, ite_true]; simp [GateOp.eval]; omega
        · simp only [hρ', hx, ite_false]; simp [GateOp.eval]; omega)
  refine ⟨[⟨GateOp.not, [a h]⟩] ++ hs2 ++ hs3 ++ hs4, ?_, ?_, ?_, b, ?_⟩
  · have : gs ++ ([⟨GateOp.not, [a h]⟩] ++ hs2 ++ hs3 ++ hs4) = gs3 ++ hs4 := by
      simp [hgs3, hgs1]
    rw [this]; exact ok4
  · rw [nc_append, nc_append, nc_append, nc1, nc2, nc4]
    have : nb m = nb h + 1 := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [nb_succ]
    omega
  · simp only [List.length_append, List.length_singleton, List.length_range] at len2 len4 ⊢
    rw [nc_append, nc_append, nc_append, nc1, nc2, nc4]
    omega
  · intro i hi
    have : gs ++ ([⟨GateOp.not, [a h]⟩] ++ hs2 ++ hs3 ++ hs4) = gs3 ++ hs4 := by
      simp [hgs3, hgs1]
    rw [this]
    exact hb i (List.mem_range.mpr hi)

end Inv

section Matroid
variable {n : ℕ} [DecidableEq (Fin n)] (rk : Finset (Fin n) → ℕ)

lemma rk_insert_le (hcard : ∀ x, rk x ≤ x.card)
    (hsub : ∀ x y, rk (x ∪ y) + rk (x ∩ y) ≤ rk x + rk y) (x : Finset (Fin n)) (j : Fin n) :
    rk (insert j x) ≤ rk x + 1 := by
  have h := hsub x {j}
  have h1 : rk {j} ≤ 1 := by simpa using hcard {j}
  have h2 : x ∪ {j} = insert j x := by
    ext a; simp [or_comm]
  rw [h2] at h
  omega

lemma stay_mono (hmono : Monotone rk) (hsub : ∀ x y, rk (x ∪ y) + rk (x ∩ y) ≤ rk x + rk y)
    {x y : Finset (Fin n)} (hxy : x ⊆ y) (j : Fin n) (h : rk (insert j x) = rk x) :
    rk (insert j y) = rk y := by
  have h1 := hsub (insert j x) y
  have hu : insert j x ∪ y = insert j y := by
    ext a
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (hxy h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  have hi : x ⊆ insert j x ∩ y := fun a ha =>
    Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem ha, hxy ha⟩
  have h2 := hmono hi
  have h3 := hmono (Finset.subset_insert j y)
  rw [hu] at h1
  omega

def cl (x : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => rk (insert i x) = rk x)

lemma subset_cl (x : Finset (Fin n)) : x ⊆ cl rk x := by
  intro i hi
  simp [cl, Finset.insert_eq_of_mem hi]

lemma rk_union_cl (hmono : Monotone rk) (hsub : ∀ x y, rk (x ∪ y) + rk (x ∩ y) ≤ rk x + rk y)
    (x : Finset (Fin n)) : ∀ S : Finset (Fin n), S ⊆ cl rk x → rk (x ∪ S) = rk x := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | insert a S ha ih =>
    intro hS
    have hS' : S ⊆ cl rk x := subset_trans (Finset.subset_insert _ _) hS
    have ha' : rk (insert a x) = rk x := by
      have := hS (Finset.mem_insert_self a S)
      simpa [cl] using this
    have h1 := stay_mono rk hmono hsub (Finset.subset_union_left (s₂ := S)) a ha'
    have h2 : x ∪ insert a S = insert a (x ∪ S) := by
      ext b; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [h2, h1, ih hS']

lemma rk_cl (hmono : Monotone rk) (hsub : ∀ x y, rk (x ∪ y) + rk (x ∩ y) ≤ rk x + rk y)
    (x : Finset (Fin n)) : rk (cl rk x) = rk x := by
  have := rk_union_cl rk hmono hsub x (cl rk x) subset_rfl
  rwa [Finset.union_eq_right.mpr (subset_cl rk x)] at this

lemma cl_flat (hmono : Monotone rk) (hsub : ∀ x y, rk (x ∪ y) + rk (x ∩ y) ≤ rk x + rk y)
    (x : Finset (Fin n)) : ∀ i, rk (insert i (cl rk x)) = rk (cl rk x) → i ∈ cl rk x := by
  intro i h
  rw [rk_cl rk hmono hsub] at h
  simp only [cl, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 := hmono (Finset.insert_subset_insert i (subset_cl rk x))
  have h2 := hmono (Finset.subset_insert i x)
  omega

lemma exists_raise (hmono : Monotone rk) (hsub : ∀ x y, rk (x ∪ y) + rk (x ∩ y) ≤ rk x + rk y)
    (x : Finset (Fin n)) (hD : rk x < rk Finset.univ) : ∃ j, rk x < rk (insert j x) := by
  by_contra hne
  push_neg at hne
  have : cl rk x = Finset.univ := by
    ext i
    simp only [cl, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact le_antisymm (hne i) (hmono (Finset.subset_insert i x))
  have h := rk_cl rk hmono hsub x
  rw [this] at h
  omega

lemma step_iff (hmono : Monotone rk) (hsub : ∀ x y, rk (x ∪ y) + rk (x ∩ y) ≤ rk x + rk y)
    (Fl : Finset (Finset (Fin n))) (hFl : ∀ y, y ∈ Fl ↔ ∀ i, rk (insert i y) = rk y → i ∈ y)
    (x : Finset (Fin n)) (k : ℕ) :
    (k ≤ rk x ∧ ∀ Y ∈ Fl, rk Y = k → ¬ x ⊆ Y) ↔ k + 1 ≤ rk x := by
  constructor
  · rintro ⟨h1, h2⟩
    by_contra h3
    have hk : rk x = k := by omega
    exact h2 (cl rk x) ((hFl _).mpr (cl_flat rk hmono hsub x)) (by rw [rk_cl rk hmono hsub]; exact hk)
      (subset_cl rk x)
  · intro h
    refine ⟨by omega, fun Y _ hY hxY => ?_⟩
    have := hmono hxY
    omega

lemma test_iff (hmono : Monotone rk) (hsub : ∀ x y, rk (x ∪ y) + rk (x ∩ y) ≤ rk x + rk y)
    (Fl : Finset (Finset (Fin n))) (hFl : ∀ y, y ∈ Fl ↔ ∀ i, rk (insert i y) = rk y → i ∈ y)
    (x : Finset (Fin n)) (k : ℕ) (j : Fin n) :
    (rk x = k ∧ ∀ Y ∈ Fl, rk Y = k ∧ j ∈ Y → ¬ x ⊆ Y) ↔ (rk x = k ∧ rk x < rk (insert j x)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra h3
    have h4 := hmono (Finset.subset_insert j x)
    have hj : j ∈ cl rk x := by
      simp only [cl, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    exact h2 (cl rk x) ((hFl _).mpr (cl_flat rk hmono hsub x))
      ⟨by rw [rk_cl rk hmono hsub]; exact h1, hj⟩ (subset_cl rk x)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun Y _ hY hxY => ?_⟩
    have hs : insert j x ⊆ Y := Finset.insert_subset hY.2 hxY
    have := hmono hs
    omega

end Matroid

lemma card_split {α : Type*} (s : Finset α) (g : α → ℕ) (P : α → Prop) [DecidablePred P] (k : ℕ) :
    (s.filter (fun Y => g Y < k + 1 ∧ P Y)).card =
      (s.filter (fun Y => g Y < k ∧ P Y)).card + (s.filter (fun Y => g Y = k ∧ P Y)).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext Y
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases h : g Y < k
      · exact Or.inl ⟨h1, h, h3⟩
      · exact Or.inr ⟨h1, by omega, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, by omega, h3⟩
      · exact ⟨h1, by omega, h3⟩
  · rw [Finset.disjoint_filter]
    intro Y _ h1 h2
    omega

lemma all_filter_toList {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (ψ : α → Bool) :
    (s.filter P).toList.all ψ = true ↔ ∀ Y ∈ s, P Y → ψ Y = true := by
  simp only [List.all_eq_true, Finset.mem_toList, Finset.mem_filter]
  constructor
  · intro h Y h1 h2; exact h Y ⟨h1, h2⟩
  · rintro h Y ⟨h1, h2⟩; exact h Y h1 h2

lemma dec_eq_of_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : decide p = decide q :=
  decide_eq_decide.mpr h

theorem construct {n : ℕ} [DecidableEq (Fin n)] (rk : Finset (Fin n) → ℕ)
    (hmono : Monotone rk) (hsub : ∀ x y, rk (x ∪ y) + rk (x ∩ y) ≤ rk x + rk y)
    (Fl : Finset (Finset (Fin n))) (hFl : ∀ y, y ∈ Fl ↔ ∀ i, rk (insert i y) = rk y → i ∈ y)
    (inp : Finset (Fin n) → List Bool) (hI : ∀ x, (inp x).length = n + 2)
    (hin : ∀ x (i : Fin n), (inp x).getD i false = decide (i ∈ x))
    (hfalse : ∀ x, (inp x).getD n false = false) (htrue : ∀ x, (inp x).getD (n+1) false = true) :
    ∃ gs : List Gate, Ok (n+2) gs ∧ nc gs ≤ nb (rk Finset.univ) ∧
      gs.length ≤ nc gs + ((2*n+1) * Fl.card + (n+5) * rk Finset.univ) ∧
      ∃ out : Fin n → ℕ, ∀ j, Carries (n+2) inp gs (out j)
        (fun x => decide (rk x < rk (insert j x))) := by
  classical
  set D := rk Finset.univ with hD
  have hz : ∀ gs, Carries (n+2) inp gs n (fun _ => false) := fun gs =>
    carries_congr (carries_input hI gs (by omega)) hfalse
  have ht : ∀ gs, Carries (n+2) inp gs (n+1) (fun _ => true) := fun gs =>
    carries_congr (carries_input hI gs (by omega)) htrue
  have hx : ∀ gs (i : Fin n), Carries (n+2) inp gs i.val (fun x => decide (i ∈ x)) := fun gs i =>
    carries_congr (carries_input hI gs (by omega)) (fun x => hin x i)
  have hrkD : ∀ x, rk x ≤ D := fun x => hmono (Finset.subset_univ x)

  obtain ⟨hs1, ok1, nc1, len1, sw, hsw⟩ := many hI n
    (fun (Y : Finset (Fin n)) x => decide (¬ x ⊆ Y)) [] (ok_nil _) Fl.toList (by
      intro hs0 hok0 Y _
      obtain ⟨hs, ok, hnc, hlen, w, hw⟩ := chain hI GateOp.or (Or.inr rfl) (fun i : Fin n => i.val)
        (fun i x => decide (i ∈ x)) (Finset.univ.filter (fun i => i ∉ Y)).toList ([] ++ hs0) n
        (fun _ => false) hok0 (hz _) (fun i _ => hx _ i)
      refine ⟨hs, ok, hnc, ?_, w, carries_congr hw (fun x => ?_)⟩
      · rw [hlen, Finset.length_toList]
        exact (Finset.card_le_univ _).trans (by simp)
      · simp only [foldl_or, Bool.false_or]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
          true_and, decide_eq_true_eq, Finset.subset_iff, not_forall]
        constructor
        · rintro ⟨a, h1, h2⟩; exact ⟨a, h2, h1⟩
        · rintro ⟨a, h1, h2⟩; exact ⟨a, h2, h1⟩)
  simp only [List.nil_append] at ok1 hsw
  have hsw' : ∀ Y ∈ Fl, Carries (n+2) inp hs1 (sw Y) (fun x => decide (¬ x ⊆ Y)) :=
    fun Y hY => hsw Y (Finset.mem_toList.mpr hY)

  have stage2 : ∀ k, k ≤ D → ∃ hs, Ok (n+2) (hs1 ++ hs) ∧ nc hs = 0 ∧
      hs.length ≤ (Fl.filter (fun Y => rk Y < k ∧ True)).card ∧
      ∃ u : ℕ → ℕ, ∀ k' ≤ k, Carries (n+2) inp (hs1 ++ hs) (u k') (fun x => decide (k' ≤ rk x)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], by simpa using ok1, rfl, by simp, fun _ => n+1, fun k' hk' => ?_⟩
      refine carries_congr (ht _) (fun x => ?_)
      have : k' = 0 := by omega
      subst this; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, ok, hnc, hlen, u, hu⟩ := ih (by omega)
      obtain ⟨hs', ok', hnc', hlen', w, hw⟩ := chain hI GateOp.and (Or.inl rfl) sw
        (fun Y x => decide (¬ x ⊆ Y)) (Fl.filter (fun Y => rk Y = k ∧ True)).toList (hs1 ++ hs) (u k)
        (fun x => decide (k ≤ rk x)) ok (hu k le_rfl)
        (fun Y hY => carries_ext hI (hsw' Y (Finset.mem_filter.mp (Finset.mem_toList.mp hY)).1) _)
      refine ⟨hs ++ hs', by rw [← List.append_assoc]; exact ok', by rw [nc_append, hnc, hnc'], ?_,
        fun k' => if k' = k + 1 then w else u k', fun k' hk' => ?_⟩
      · rw [List.length_append, hlen', Finset.length_toList, card_split]; omega
      · by_cases hkk : k' = k + 1
        · subst hkk
          simp only [ite_true]
          rw [← List.append_assoc]
          refine carries_congr hw (fun x => ?_)
          simp only [foldl_and]
          apply Bool.eq_iff_iff.mpr
          rw [Bool.and_eq_true, all_filter_toList, decide_eq_true_iff, decide_eq_true_iff,
            ← step_iff rk hmono hsub Fl hFl x k]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun Y hY hYk => by simpa using h2 Y hY ⟨hYk, trivial⟩⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun Y hY hYk => by simpa using h2 Y hY hYk.1⟩
        · simp only [hkk, ite_false]
          rw [← List.append_assoc]
          exact carries_ext hI (hu k' (by omega)) _
  obtain ⟨hs2, ok2, nc2, len2, u, hu⟩ := stage2 D le_rfl

  obtain ⟨hs3, ok3, nc3, len3, neg, hneg⟩ := inv hI n D (hs1 ++ hs2) (fun i => u (i + 1)) rk ok2
    (hz _) hrkD (fun i hi => carries_congr (hu (i + 1) (by omega))
      (fun x => dec_eq_of_iff ⟨fun h => by omega, fun h => by omega⟩))

  obtain ⟨hs4, ok4, nc4, len4, e, he⟩ := many hI 1 (fun k x => decide (rk x = k))
    (hs1 ++ hs2 ++ hs3) ok3 (List.range D) (by
      intro hs0 hok0 k hk
      have hk' : k < D := List.mem_range.mp hk
      have h1 := carries_ext hI (carries_ext hI (hu k (by omega)) hs3) hs0
      have h2 := carries_ext hI (hneg k hk') hs0
      obtain ⟨okA, ncA, hA⟩ := add2 hI (Or.inl rfl) hok0 h1 h2
      refine ⟨_, okA, ncA, by simp, _, carries_congr hA (fun x => ?_)⟩
      apply Bool.eq_iff_iff.mpr
      simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq]
      constructor <;> intro h <;> omega)
  set G4 := hs1 ++ hs2 ++ hs3 ++ hs4 with hG4

  obtain ⟨hs5, ok5, nc5, len5, out, hout⟩ := many hI (Fl.card + D)
    (fun j x => decide (rk x < rk (insert j x))) G4 ok4 (List.finRange n) (by
      intro hs0 hok0 j _
      have per : ∀ k, k ≤ D → ∃ hs, Ok (n+2) (G4 ++ hs0 ++ hs) ∧ nc hs = 0 ∧
          hs.length ≤ (Fl.filter (fun Y => rk Y < k ∧ j ∈ Y)).card + k ∧ ∃ w,
            Carries (n+2) inp (G4 ++ hs0 ++ hs) w
              (fun x => decide (rk x < k ∧ rk x < rk (insert j x))) := by
        intro k
        induction k with
        | zero =>
          intro _
          exact ⟨[], by simpa using hok0, rfl, by simp, n,
            carries_congr (hz _) (fun x => by simp)⟩
        | succ k ih =>
          intro hk
          obtain ⟨hs, ok, hnc, hlen, wp, hwp⟩ := ih (by omega)
          have hek : Carries (n+2) inp (G4 ++ hs0 ++ hs) (e k) (fun x => decide (rk x = k)) :=
            carries_ext hI (carries_ext hI (he k (List.mem_range.mpr (by omega))) hs0) hs
          obtain ⟨hs', ok', hnc', hlen', w, hw⟩ := chain hI GateOp.and (Or.inl rfl) sw
            (fun Y x => decide (¬ x ⊆ Y)) (Fl.filter (fun Y => rk Y = k ∧ j ∈ Y)).toList
            (G4 ++ hs0 ++ hs) (e k) (fun x => decide (rk x = k)) ok hek
            (fun Y hY => carries_pre hI (hsw' Y (Finset.mem_filter.mp (Finset.mem_toList.mp hY)).1)
              (by simp [hG4]))
          obtain ⟨okB, ncB, hB⟩ := add2 hI (Or.inr rfl) ok' (carries_ext hI hwp hs') hw
          refine ⟨hs ++ hs' ++ [⟨GateOp.or, [wp, w]⟩], ?_, ?_, ?_,
            n + 2 + (G4 ++ hs0 ++ hs ++ hs').length, ?_⟩
          · simpa [List.append_assoc] using okB
          · rw [nc_append, nc_append, hnc, hnc', ncB]
          · simp only [List.length_append, List.length_singleton]
            rw [hlen', Finset.length_toList, card_split]; omega
          · rw [show G4 ++ hs0 ++ (hs ++ hs' ++ [⟨GateOp.or, [wp, w]⟩]) =
                G4 ++ hs0 ++ hs ++ hs' ++ [⟨GateOp.or, [wp, w]⟩] by simp]
            refine carries_congr hB (fun x => ?_)
            · show _ = decide (rk x < k + 1 ∧ rk x < rk (insert j x))
              simp only [foldl_and]
              apply Bool.eq_iff_iff.mpr
              simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false,
                Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
              rw [all_filter_toList]
              have key := test_iff rk hmono hsub Fl hFl x k j
              constructor
              · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
                · exact ⟨by omega, h2⟩
                · have := key.mp ⟨h1, fun Y hY hYk => by simpa using h2 Y hY hYk⟩
                  exact ⟨by omega, this.2⟩
              · rintro ⟨h1, h2⟩
                by_cases hlt : rk x < k
                · exact Or.inl ⟨hlt, h2⟩
                · have hk2 : rk x = k := by omega
                  have := key.mpr ⟨hk2, h2⟩
                  exact Or.inr ⟨hk2, fun Y hY hYk => by simpa using this.2 Y hY hYk⟩
      obtain ⟨hs, ok, hnc, hlen, w, hw⟩ := per D le_rfl
      refine ⟨hs, ok, hnc, ?_, w, carries_congr hw (fun x => ?_)⟩
      · have := Finset.card_filter_le Fl (fun Y => rk Y < D ∧ j ∈ Y)
        omega
      · apply dec_eq_of_iff
        constructor
        · exact fun h => h.2
        · intro h
          refine ⟨?_, h⟩
          have := hrkD (insert j x)
          omega)
  refine ⟨G4 ++ hs5, ok5, ?_, ?_, fun j => out j, fun j => hout j (List.mem_finRange j)⟩
  · simp only [hG4, nc_append, nc1, nc2, nc4, nc5]
    omega
  · have hF2 := Finset.card_filter_le Fl (fun Y => rk Y < D ∧ True)
    simp only [hG4, nc_append, nc1, nc2, nc4, nc5, List.length_append, List.length_finRange,
      Finset.length_toList] at len1 len4 len5 ⊢
    simp only [List.length_range] at len4
    have e1 : (Fl.card + D) * n = n * Fl.card + n * D := by ring
    have e2 : (2 * n + 1) * Fl.card = 2 * (n * Fl.card) + Fl.card := by ring
    have e3 : (n + 5) * D = n * D + 5 * D := by ring
    rw [e1] at len5
    rw [e2, e3]
    omega

theorem lower {n : ℕ} [DecidableEq (Fin n)] (rk : Finset (Fin n) → ℕ) (h0 : rk ∅ = 0)
    (hmono : Monotone rk) (hcard : ∀ x, rk x ≤ x.card)
    (hsub : ∀ x y, rk (x ∪ y) + rk (x ∩ y) ≤ rk x + rk y)
    (inp : Finset (Fin n) → List Bool) (hI : ∀ x, (inp x).length = n + 2)
    (hinpmono : ∀ x y, x ⊆ y → ∀ w, (inp x).getD w false = true → (inp y).getD w false = true)
    (C : Circuit) (hfan : FanInTwo C) (tap : Fin n → Fin (n + 2 + C.size))
    (htap : ∀ x j, (C.wires (inp x)).getD (tap j).val false = true ↔ rk x < rk (insert j x)) :
    rk Finset.univ < 2 ^ notCount C := by
  classical
  set D := rk Finset.univ with hD
  let step : Finset (Fin n) → Finset (Fin n) := fun x =>
    if h : ∃ j, rk x < rk (insert j x) then insert (Classical.choose h) x else x
  let ch : ℕ → Finset (Fin n) := fun t => step^[t] ∅
  have hch : ∀ t, ch (t + 1) = step (ch t) := fun t => Function.iterate_succ_apply' step t ∅
  have hsubset : ∀ t, ch t ⊆ ch (t + 1) := by
    intro t
    rw [hch]
    dsimp only [step]
    split_ifs
    · exact Finset.subset_insert _ _
    · exact subset_rfl
  have hrk : ∀ t, t ≤ D → rk (ch t) = t := by
    intro t
    induction t with
    | zero => intro _; simpa [ch] using h0
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have hex := exists_raise rk hmono hsub (ch t) (by omega)
      rw [hch]
      dsimp only [step]
      rw [dite_cond_eq_true (eq_true hex)]
      have h2 := Classical.choose_spec hex
      have h3 := rk_insert_le rk hcard hsub (ch t) (Classical.choose hex)
      omega
  have hdrop : ∀ t, t < D → ∃ j, rk (ch t) < rk (insert j (ch t)) ∧
      ch (t + 1) = insert j (ch t) := by
    intro t ht
    have hex := exists_raise rk hmono hsub (ch t) (by rw [hrk t (by omega)]; omega)
    refine ⟨Classical.choose hex, Classical.choose_spec hex, ?_⟩
    rw [hch]
    dsimp only [step]
    rw [dite_cond_eq_true (eq_true hex)]
  let xs : Fin (D + 1) → List Bool := fun t => inp (ch t.val)
  have hfan' : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    refine ⟨?_, h2⟩
    simpa using h1
  have hm := markov_drops_bound (I := n + 2) xs (fun t => hI _)
    (fun t w _ h => hinpmono _ _ (hsubset t.val) w h) C.gates hfan'
  have hall : drops (I := n + 2) xs C.gates = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro t
    obtain ⟨j, hj1, hj2⟩ := hdrop t.val t.isLt
    simp only [drops, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(tap j).val, (tap j).isLt, ?_, ?_⟩
    · show (C.wires (inp (ch t.val))).getD _ false = true
      exact (htap _ j).mpr hj1
    · show (C.wires (inp (ch (t.val + 1)))).getD _ false = false
      cases hv : (C.wires (inp (ch (t.val + 1)))).getD (tap j).val false
      · rfl
      · have := (htap _ j).mp hv
        rw [hj2, Finset.insert_idem] at this
        omega
  rw [hall, Finset.card_univ, Fintype.card_fin] at hm
  have : notCount ⟨C.gates, 0⟩ = notCount C := rfl
  rw [this] at hm
  omega

lemma inp_getD (n : ℕ) (P : Fin n → Bool) (w : ℕ) :
    (List.ofFn P ++ [false, true]).getD w false =
      if h : w < n then P ⟨w, h⟩ else decide (w = n + 1) := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    rcases Nat.lt_or_ge w (n + 2) with h2 | h2
    · by_cases h3 : w = n + 1
      · subst h3; simp
      · have : w = n := by omega
        subst this; simp
    · rw [List.getElem?_eq_none (by simp; omega)]
      simp; omega

end PEqualNP.Outside.L_lib_1262

theorem PEqualNP.Outside.L_lib_1262 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n : Nat) (rk : Finset (Fin n) → Nat),
  rk ∅=0 → Monotone rk → (∀ x, rk x ≤ x.card) →
  (∀ x y, rk (x∪y)+rk (x∩y) ≤ rk x+rk y) →
  let f := fun (x : Finset (Fin n)) (j : Fin n) => decide (rk x < rk (insert j x))
  let computes := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : Finset (Fin n) → Fin n → Bool) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ ∃ tap : Fin n → Fin (n+2+C.size),
      ∀ x j, let input := List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]
             (C.wires input).getD (tap j).val false = g x j
  let D := rk Finset.univ
  let F := ((Finset.univ : Finset (Finset (Fin n))).filter
    (fun y => ∀ i, rk (insert i y)=rk y → i∈y)).card
  (∀ C, computes C f → D < 2^(PEqualNP.NotBracket.notCount C)) ∧
    ∀ r : Nat, D < 2^r → ∃ C, computes C f ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ (2*n+1)*F+(2*n+4)*D) := by
  intro n rk h0 hmono hcard hsub f computes D F
  let inp : Finset (Fin n) → List Bool := fun x =>
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]
  have hI : ∀ x, (inp x).length = n + 2 := fun x => by simp [inp]
  have hget : ∀ x w, (inp x).getD w false = true ↔
      (∃ h : w < n, (⟨w, h⟩ : Fin n) ∈ x) ∨ w = n + 1 := by
    intro x w
    have := PEqualNP.Outside.L_lib_1262.inp_getD n
      (fun i : Fin n => @decide (i ∈ x) (Classical.propDecidable _)) w
    rw [show (inp x).getD w false = (if h : w < n then
      @decide ((⟨w, h⟩ : Fin n) ∈ x) (Classical.propDecidable _) else decide (w = n + 1)) from this]
    split_ifs with h
    · simp only [decide_eq_true_eq]
      constructor
      · intro hm; exact Or.inl ⟨h, hm⟩
      · rintro (⟨_, hm⟩ | h2)
        · exact hm
        · omega
    · simp only [decide_eq_true_eq]
      constructor
      · intro h2; exact Or.inr h2
      · rintro (⟨h3, _⟩ | h2)
        · exact absurd h3 h
        · exact h2
  refine ⟨fun C hC => ?_, fun r hr => ?_⟩
  · obtain ⟨hfan, _, _, tap, htap⟩ := hC
    refine @PEqualNP.Outside.L_lib_1262.lower n (fun a b => Classical.propDecidable (a = b)) rk h0 hmono hcard hsub inp hI ?_ C hfan tap ?_
    · intro x y hxy w hw
      rw [hget] at hw ⊢
      rcases hw with ⟨h, hm⟩ | h
      · exact Or.inl ⟨h, hxy hm⟩
      · exact Or.inr h
    · intro x j
      have := htap x j
      simp only [f] at this
      rw [this]
      simp
  · let Fl : Finset (Finset (Fin n)) :=
      letI : ∀ P : Prop, Decidable P := Classical.propDecidable
      (Finset.univ : Finset (Finset (Fin n))).filter (fun y => ∀ i, rk (insert i y)=rk y → i∈y)
    have hFl : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
        ∀ y, y ∈ Fl ↔ ∀ i, rk (insert i y) = rk y → i ∈ y := fun y => by simp [Fl]
    obtain ⟨gs, hok, hnc, hlen, out, hout⟩ :=
      @PEqualNP.Outside.L_lib_1262.construct n (fun a b => Classical.propDecidable (a = b)) rk hmono hsub Fl hFl inp hI
        (fun x i => by
          apply Bool.eq_iff_iff.mpr
          rw [hget]; simp only [decide_eq_true_eq]
          constructor
          · rintro (⟨_, hm⟩ | h2)
            · exact hm
            · have := i.isLt; omega
          · intro hm; exact Or.inl ⟨i.isLt, hm⟩)
        (fun x => by
          cases hv : (inp x).getD n false
          · rfl
          · rcases (hget x n).mp hv with ⟨h, _⟩ | h <;> omega)
        (fun x => (hget x (n + 1)).mpr (Or.inr rfl))
    have hDn : D ≤ n := by
      have := hcard Finset.univ
      simpa using this
    have hFF : F = Fl.card := rfl
    refine ⟨⟨gs, 0⟩, ⟨hok.1, hok.2, by simp [PEqualNP.CircuitLowerBounds.Circuit.size],
      fun j => ⟨out j, (hout j).1⟩, fun x j => ?_⟩, ?_, ?_⟩
    · have h1 := (hout j).2 x
      unfold PEqualNP.Outside.L_lib_1262.V at h1
      show (PEqualNP.Outside.L_lib_1262.evalWires gs (inp x)).getD (out j) false = f x j
      rw [h1]
      simp only [f]
      exact Bool.eq_iff_iff.mpr (by simp)
    · exact hnc.trans (PEqualNP.Outside.L_lib_1262.nb_le r _ hr)
    · have hsz : (⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = gs.length := rfl
      have hnn : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ = PEqualNP.Outside.L_lib_1262.nc gs := rfl
      rw [hsz, hnn, hFF]
      have hmul : (n + 5) * rk Finset.univ ≤ (2 * n + 4) * rk Finset.univ := by
        rcases Nat.eq_zero_or_pos (rk Finset.univ) with hD0 | hD0
        · rw [hD0]; simp
        · exact Nat.mul_le_mul_right _ (by omega)
      show gs.length - PEqualNP.Outside.L_lib_1262.nc gs ≤
        (2 * n + 1) * Fl.card + (2 * n + 4) * rk Finset.univ
      omega
