import PEqualNP.Defs
import Mathlib.Logic.Equiv.Fintype

namespace PEqualNP.Outside.L_meta_50576

open PEqualNP.CircuitLowerBounds

section CircuitDSL

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepW x

lemma W_eq_wires (gs : List Gate) (out : ℕ) (x : List Bool) :
    (⟨gs, out⟩ : Circuit).wires x = W gs x := rfl

lemma W_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = stepW (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) :
    (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_append_singleton]
    simp [stepW, ih]
    omega

lemma W_getD_lt (gs : List Gate) (g : Gate) (x : List Bool) (k : ℕ)
    (hk : k < (W gs x).length) :
    (W (gs ++ [g]) x).getD k false = (W gs x).getD k false := by
  rw [W_append_singleton, stepW]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma W_getD_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (W (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (W gs x).getD i false) := by
  rw [W_append_singleton, stepW]
  have hlen := W_length gs x
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hlen]

lemma W_getD_of_le (gs : List Gate) (x : List Bool) (k : ℕ)
    (hk : x.length + gs.length ≤ k) :
    (W gs x).getD k false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [W_length]; omega)]
  rfl

lemma W_extend (as bs : List Gate) (x : List Bool) (k : ℕ)
    (hk : k < x.length + as.length) :
    (W (as ++ bs) x).getD k false = (W as x).getD k false := by
  induction bs using List.reverseRecOn with
  | nil => simp
  | append_singleton bs g ih =>
    rw [← List.append_assoc, W_getD_lt _ _ _ _ (by rw [W_length]; simp; omega), ih]

def OKg (g : Gate) (b : ℕ) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
  g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < b

def Good (N : ℕ) (gs : List Gate) : Prop :=
  ∀ j (h : j < gs.length), OKg gs[j] (N + j)

lemma Good_nil (N : ℕ) : Good N [] := by
  intro j hj; simp at hj

lemma Good_snoc {N : ℕ} {gs : List Gate} {g : Gate}
    (h : Good N gs) (hg : OKg g (N + gs.length)) :
    Good N (gs ++ [g]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hj' : j < gs.length
  · rw [List.getElem_append_left hj']; exact h j hj'
  · have heq : j = gs.length := by omega
    subst heq
    simpa using hg

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

def nc (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNot g.op).length

lemma nc_nil : nc [] = 0 := rfl

lemma nc_append (a b : List Gate) : nc (a ++ b) = nc a + nc b := by
  simp [nc, List.filter_append]

lemma nc_and (l : List ℕ) : nc [⟨GateOp.and, l⟩] = 0 := by simp [nc, isNot]

lemma nc_or (l : List ℕ) : nc [⟨GateOp.or, l⟩] = 0 := by simp [nc, isNot]

lemma nc_not (l : List ℕ) : nc [⟨GateOp.not, l⟩] = 1 := by simp [nc, isNot]

lemma notCount_eq_nc (gs : List Gate) (out : ℕ) :
    PEqualNP.NotBracket.notCount ⟨gs, out⟩ = nc gs := by
  unfold PEqualNP.NotBracket.notCount nc
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> simp [isNot]

lemma good_fanInTwo {N : ℕ} {gs : List Gate} (hG : Good N gs) (out : ℕ) :
    PEqualNP.MetaComplexity.FanInTwo ⟨gs, out⟩ := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
  obtain ⟨h1, h2, _⟩ := hG k hk
  refine ⟨?_, h2⟩
  rcases h1 with h | h | h <;> simp [h]

lemma good_readsBack {N : ℕ} {gs : List Gate} (hG : Good N gs) (out : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, out⟩ := by
  intro k hk i hi
  simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hk] at hi
  exact (hG k hk).2.2 i hi

end CircuitDSL

section LowerBound

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

lemma exists_drop_between {L : ℕ} (u : Fin (L + 1) → Bool)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ L)
    (ha1 : u ⟨a, by omega⟩ = true) (hb0 : u ⟨b, by omega⟩ = false) :
    ∃ d : Fin L, a ≤ d.val ∧ d.val < b ∧ u d.castSucc = true ∧ u d.succ = false := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    rw [ha1] at hb0
    exact Bool.noConfusion hb0
  | succ b' ih =>
    by_cases heq : a = b' + 1
    · subst heq
      rw [ha1] at hb0
      exact Bool.noConfusion hb0
    · have hab' : a ≤ b' := by omega
      cases hub' : u ⟨b', by omega⟩
      · rcases ih hab' (by omega) ha1 hub' with ⟨d, hd1, hd2, hd3, hd4⟩
        exact ⟨d, hd1, by omega, hd3, hd4⟩
      · exact ⟨⟨b', by omega⟩, hab', by dsimp; omega, hub', hb0⟩

lemma card_le_of_between {L : ℕ} (A D : Finset (Fin L))
    (hbet : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁.val < a₂.val →
      ∃ d ∈ D, a₁.val < d.val ∧ d.val < a₂.val) :
    A.card ≤ D.card + 1 := by
  by_cases hA : A.Nonempty
  · set m := A.max' hA
    have hm : m ∈ A := Finset.max'_mem A hA
    set A' := A.erase m
    have hcardA : A'.card + 1 = A.card := Finset.card_erase_add_one hm
    have hex : ∀ a : Fin L, a ∈ A' → ∃ d ∈ D, a.val < d.val ∧ d.val < m.val := by
      intro a ha
      have hne : a ≠ m := (Finset.mem_erase.mp ha).1
      have haA : a ∈ A := Finset.mem_of_mem_erase ha
      have hle : a ≤ m := Finset.le_max' A a haA
      have hlt : a.val < m.val := by
        have : a < m := lt_of_le_of_ne hle hne
        exact this
      exact hbet a haA m hm hlt
    have hnext_ne : ∀ a, a ∈ A' → (A.filter (fun b => a.val < b.val)).Nonempty := by
      intro a ha
      refine ⟨m, Finset.mem_filter.mpr ⟨hm, ?_⟩⟩
      have hne : a ≠ m := (Finset.mem_erase.mp ha).1
      have hle : a ≤ m := Finset.le_max' A a (Finset.mem_of_mem_erase ha)
      exact (lt_of_le_of_ne hle hne : a < m)
    let nextA : Fin L → Fin L := fun a =>
      if ha : a ∈ A' then
        (A.filter (fun b => a.val < b.val)).min' (hnext_ne a ha)
      else a
    have hnext_mem : ∀ a (ha : a ∈ A'), nextA a ∈ A ∧ a.val < (nextA a).val := by
      intro a ha
      dsimp only [nextA]
      simp only [ha, ↓reduceDIte]
      have hmem := Finset.min'_mem (A.filter (fun b => a.val < b.val)) (hnext_ne a ha)
      exact Finset.mem_filter.mp hmem
    have hnext_le : ∀ a (ha : a ∈ A'), ∀ b ∈ A, a.val < b.val → (nextA a).val ≤ b.val := by
      intro a ha b hb hlt
      dsimp only [nextA]
      simp only [ha, ↓reduceDIte]
      exact Finset.min'_le _ b (Finset.mem_filter.mpr ⟨hb, hlt⟩)
    have hstep : ∀ a ∈ A', ∃ d ∈ D, a.val < d.val ∧ d.val < (nextA a).val := by
      intro a ha
      have hnm := hnext_mem a ha
      exact hbet a (Finset.mem_of_mem_erase ha) (nextA a) hnm.1 hnm.2
    let f : Fin L → Fin L := fun a =>
      if h : a ∈ A' then Classical.choose (hstep a h) else a
    have hf_mem : ∀ a ∈ A', f a ∈ D := by
      intro a ha
      dsimp only [f]
      simp only [ha, ↓reduceDIte]
      exact (Classical.choose_spec (hstep a ha)).1
    have hf_bounds : ∀ a ∈ A', a.val < (f a).val ∧ (f a).val < (nextA a).val := by
      intro a ha
      dsimp only [f]
      simp only [ha, ↓reduceDIte]
      exact (Classical.choose_spec (hstep a ha)).2
    have hf_inj : Set.InjOn f A' := by
      intro a₁ ha₁ a₂ ha₂ hfeq
      by_contra hne
      have hne_val : a₁.val ≠ a₂.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne_val with hlt | hlt
      · have h1 := (hf_bounds a₁ ha₁).2
        have h2 := hnext_le a₁ ha₁ a₂ (Finset.mem_of_mem_erase ha₂) hlt
        have h3 := (hf_bounds a₂ ha₂).1
        rw [hfeq] at h1
        omega
      · have h1 := (hf_bounds a₂ ha₂).2
        have h2 := hnext_le a₂ ha₂ a₁ (Finset.mem_of_mem_erase ha₁) hlt
        have h3 := (hf_bounds a₁ ha₁).1
        rw [← hfeq] at h1
        omega
    have hle : A'.card ≤ D.card := by
      calc A'.card = (A'.image f).card := (Finset.card_image_of_injOn hf_inj).symm
        _ ≤ D.card := Finset.card_le_card (Finset.image_subset_iff.mpr hf_mem)
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

def drops {I L : ℕ} (xs : Fin (L + 1) → List Bool) (gs : List Gate) :
    Finset (Fin L) :=
  Finset.univ.filter (fun t : Fin L =>
    ∃ w < I + gs.length,
      (W gs (xs t.castSucc)).getD w false = true ∧
      (W gs (xs t.succ)).getD w false = false)

lemma markov_drops_bound {I L : ℕ} (xs : Fin (L + 1) → List Bool)
    (hlen : ∀ t : Fin (L + 1), (xs t).length = I)
    (hmono : ∀ t : Fin L, ∀ w < I,
      (xs t.castSucc).getD w false = true → (xs t.succ).getD w false = true) :
    ∀ gs : List Gate,
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      (drops (I := I) xs gs).card + 1 ≤ 2 ^ nc gs := by
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
    simp [nc]
  | append_singleton gs g ih =>
    intro hfan
    have hfan_pre : ∀ g' ∈ gs,
        (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_append_left _ hg')
    have hg_fan := hfan g (List.mem_append_right _ (List.mem_singleton_self g))
    have hih := ih hfan_pre
    set D := drops (I := I) xs gs
    set v : Fin (L + 1) → Bool := fun t => (W (gs ++ [g]) (xs t)).getD (I + gs.length) false
    set newD : Finset (Fin L) :=
      Finset.univ.filter (fun t : Fin L => v t.castSucc = true ∧ v t.succ = false)
    have hsplit : drops (I := I) xs (gs ++ [g]) = D ∪ newD := by
      ext t
      simp only [drops, D, newD, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        List.length_append, List.length_singleton]
      constructor
      · rintro ⟨w, hw, h1, h2⟩
        by_cases hlt : w < I + gs.length
        · left
          refine ⟨w, hlt, ?_, ?_⟩
          · rwa [W_getD_lt gs g (xs t.castSucc) w (by rw [W_length, hlen]; exact hlt)] at h1
          · rwa [W_getD_lt gs g (xs t.succ) w (by rw [W_length, hlen]; exact hlt)] at h2
        · have heq : w = I + gs.length := by omega
          subst heq
          exact Or.inr ⟨h1, h2⟩
      · rintro (⟨w, hw, h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨w, by omega, ?_, ?_⟩
          · rw [W_getD_lt gs g (xs t.castSucc) w (by rw [W_length, hlen]; exact hw)]; exact h1
          · rw [W_getD_lt gs g (xs t.succ) w (by rw [W_length, hlen]; exact hw)]; exact h2
        · exact ⟨I + gs.length, by omega, h1, h2⟩
    have hv_eq : ∀ t : Fin (L + 1),
        v t = g.op.eval (g.inputs.map fun i => (W gs (xs t)).getD i false) := by
      intro t
      dsimp only [v]
      rw [← hlen t]
      exact W_getD_last gs g (xs t)
    rcases hg_fan.1 with hop | hop | hop
    · have hnc : nc (gs ++ [g]) = nc gs := by
        rw [nc_append]; simp [nc, isNot, hop]
      have hsub : newD ⊆ D := by
        intro t ht
        simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        by_contra hnd
        have hnondec : ∀ i : ℕ, (W gs (xs t.castSucc)).getD i false = true →
            (W gs (xs t.succ)).getD i false = true := by
          intro i hi
          by_cases hilt : i < I + gs.length
          · cases h2 : (W gs (xs t.succ)).getD i false
            · exfalso
              apply hnd
              simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨i, hilt, hi, h2⟩
            · rfl
          · rw [W_getD_of_le gs (xs t.castSucc) i (by rw [hlen]; omega)] at hi
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
    · have hnc : nc (gs ++ [g]) = nc gs := by
        rw [nc_append]; simp [nc, isNot, hop]
      have hsub : newD ⊆ D := by
        intro t ht
        simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        by_contra hnd
        have hnondec : ∀ i : ℕ, (W gs (xs t.castSucc)).getD i false = true →
            (W gs (xs t.succ)).getD i false = true := by
          intro i hi
          by_cases hilt : i < I + gs.length
          · cases h2 : (W gs (xs t.succ)).getD i false
            · exfalso
              apply hnd
              simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨i, hilt, hi, h2⟩
            · rfl
          · rw [W_getD_of_le gs (xs t.castSucc) i (by rw [hlen]; omega)] at hi
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
    · have hnc : nc (gs ++ [g]) = nc gs + 1 := by
        rw [nc_append]; simp [nc, isNot, hop]
      have hnew_le : newD.card ≤ D.card + 1 := by
        cases hgin : g.inputs with
        | nil =>
          have hemp : newD = ∅ := by
            ext t
            simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, not_and]
            intro _
            rw [hv_eq, hop, hgin]
            simp [GateOp.eval]
          rw [hemp]; simp
        | cons a tl =>
          set u : Fin (L + 1) → Bool := fun t => (W gs (xs t)).getD a false
          have hvu : ∀ t, v t = !(u t) := by
            intro t
            rw [hv_eq, hop, hgin]
            simp [GateOp.eval, u]
          apply card_le_of_between newD D
          intro t₁ ht₁ t₂ ht₂ hlt
          simp only [newD, Finset.mem_filter, Finset.mem_univ, true_and, hvu] at ht₁ ht₂
          have hu1 : u t₁.succ = true := by
            cases h : u t₁.succ <;> simp [h] at ht₁
            rfl
          have hu2 : u t₂.castSucc = false := by
            cases h : u t₂.castSucc <;> simp [h] at ht₂
            rfl
          obtain ⟨d, hd1, hd2, hd3, hd4⟩ :=
            exists_drop_between u (a := t₁.val + 1) (b := t₂.val) (by omega) (by omega) hu1 hu2
          refine ⟨d, ?_, by omega, hd2⟩
          simp only [D, drops, Finset.mem_filter, Finset.mem_univ, true_and]
          have halt : a < I + gs.length := by
            by_contra hge
            have hfalse := W_getD_of_le gs (xs d.castSucc) a (by rw [hlen]; omega)
            dsimp only [u] at hd3
            rw [hfalse] at hd3
            exact Bool.noConfusion hd3
          exact ⟨a, halt, hd3, hd4⟩
      have hunion : (D ∪ newD).card ≤ D.card + newD.card := Finset.card_union_le D newD
      rw [hsplit, hnc, Nat.pow_succ]
      omega

lemma card_filter_lt (n m : ℕ) (hm : m ≤ n) :
    (Finset.univ.filter (fun u : Fin n => u.val < m)).card = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : Finset.univ.filter (fun u : Fin n => u.val < m + 1) =
        insert ⟨m, hm⟩ (Finset.univ.filter (fun u : Fin n => u.val < m)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [hsplit, Finset.card_insert_of_notMem (by simp), ih (by omega)]

end LowerBound

section Construction

def env (n : ℕ) (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

lemma env_len (n : ℕ) (x : Finset (Fin n)) : (env n x).length = n + 2 := by
  simp [env]

lemma env_getD_lt (n : ℕ) (x : Finset (Fin n)) (i : Fin n) :
    (env n x).getD i.val false = decide (i ∈ x) := by
  simp only [env, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp)]
  simp

lemma env_getD_false (n : ℕ) (x : Finset (Fin n)) :
    (env n x).getD n false = false := by
  simp only [env, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

lemma env_getD_true (n : ℕ) (x : Finset (Fin n)) :
    (env n x).getD (n + 1) false = true := by
  simp only [env, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  have hsub : n + 1 - n = 1 := by omega
  simp [hsub]

lemma env_mono (n : ℕ) {x y : Finset (Fin n)} (hxy : x ⊆ y) (w : ℕ) (hw : w < n + 2) :
    (env n x).getD w false = true → (env n y).getD w false = true := by
  intro h
  by_cases hwn : w < n
  · have h1 := env_getD_lt n x ⟨w, hwn⟩
    have h2 := env_getD_lt n y ⟨w, hwn⟩
    rw [h1] at h
    rw [h2]
    exact decide_eq_true (hxy (of_decide_eq_true h))
  · by_cases hweq : w = n
    · subst hweq; rw [env_getD_false] at h; exact Bool.noConfusion h
    · have hweq2 : w = n + 1 := by omega
      subst hweq2; exact env_getD_true n y

def Rep (n : ℕ) (gs : List Gate) (w : ℕ) (P : Finset (Fin n) → Prop) : Prop :=
  w < n + 2 + gs.length ∧ ∀ x, ((W gs (env n x)).getD w false = true ↔ P x)

lemma Rep_ext {n : ℕ} {gs : List Gate} {w : ℕ} {P : Finset (Fin n) → Prop}
    (h : Rep n gs w P) (hs : List Gate) : Rep n (gs ++ hs) w P := by
  refine ⟨by simp; have := h.1; omega, fun x => ?_⟩
  rw [W_extend gs hs (env n x) w (by rw [env_len]; exact h.1)]
  exact h.2 x

lemma Rep_congr {n : ℕ} {gs : List Gate} {w : ℕ} {P Q : Finset (Fin n) → Prop}
    (h : Rep n gs w P) (hPQ : ∀ x, P x ↔ Q x) : Rep n gs w Q :=
  ⟨h.1, fun x => (h.2 x).trans (hPQ x)⟩

lemma Rep_gate {n : ℕ} (gs : List Gate) (g : Gate) (x : Finset (Fin n)) :
    (W (gs ++ [g]) (env n x)).getD (n + 2 + gs.length) false =
      g.op.eval (g.inputs.map fun i => (W gs (env n x)).getD i false) := by
  have h := W_getD_last gs g (env n x)
  rwa [env_len] at h

lemma rep_false (n : ℕ) (gs : List Gate) : Rep n gs n (fun _ => False) := by
  have h0 : Rep n [] n (fun _ => False) := by
    refine ⟨by simp, fun x => ?_⟩
    simp only [W, List.foldl_nil, env_getD_false, Bool.false_eq_true]
  simpa using Rep_ext h0 gs

lemma rep_true (n : ℕ) (gs : List Gate) : Rep n gs (n + 1) (fun _ => True) := by
  have h0 : Rep n [] (n + 1) (fun _ => True) := by
    refine ⟨by simp, fun x => ?_⟩
    simp only [W, List.foldl_nil, env_getD_true]
  simpa using Rep_ext h0 gs

lemma rep_input (n : ℕ) (gs : List Gate) (i : Fin n) :
    Rep n gs i.val (fun x => i ∈ x) := by
  have h0 : Rep n [] i.val (fun x => i ∈ x) := by
    refine ⟨by simp; omega, fun x => ?_⟩
    simp only [W, List.foldl_nil, env_getD_lt, decide_eq_true_iff]
  simpa using Rep_ext h0 gs

def Ext (n : ℕ) (gs : List Gate) (c : ℕ) (Φ : List Gate → ℕ → Prop) : Prop :=
  ∃ hs w, Good (n + 2) (gs ++ hs) ∧ nc hs = 0 ∧ hs.length ≤ c ∧ Φ (gs ++ hs) w

lemma ext_and2 {n : ℕ} {gs : List Gate} (hG : Good (n + 2) gs) {a b : ℕ}
    {P Q : Finset (Fin n) → Prop} (ha : Rep n gs a P) (hb : Rep n gs b Q) :
    Ext n gs 1 (fun gs' w => Rep n gs' w (fun x => P x ∧ Q x)) := by
  refine ⟨[⟨GateOp.and, [a, b]⟩], n + 2 + gs.length,
    Good_snoc hG ⟨by simp, by simp, ?_⟩, nc_and _, by simp, by simp, fun x => ?_⟩
  · intro i hi; simp at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1
  · have h1 := ha.2 x
    have h2 := hb.2 x
    rw [Rep_gate]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true, h1, h2]

lemma ext_or2 {n : ℕ} {gs : List Gate} (hG : Good (n + 2) gs) {a b : ℕ}
    {P Q : Finset (Fin n) → Prop} (ha : Rep n gs a P) (hb : Rep n gs b Q) :
    Ext n gs 1 (fun gs' w => Rep n gs' w (fun x => P x ∨ Q x)) := by
  refine ⟨[⟨GateOp.or, [a, b]⟩], n + 2 + gs.length,
    Good_snoc hG ⟨by simp, by simp, ?_⟩, nc_or _, by simp, by simp, fun x => ?_⟩
  · intro i hi; simp at hi; rcases hi with rfl | rfl; exact ha.1; exact hb.1
  · have h1 := ha.2 x
    have h2 := hb.2 x
    rw [Rep_gate]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false, Bool.or_eq_true, h1, h2]

lemma rep_not {n : ℕ} {gs : List Gate} (hG : Good (n + 2) gs) {a : ℕ}
    {P : Finset (Fin n) → Prop} (ha : Rep n gs a P) :
    Good (n + 2) (gs ++ [⟨GateOp.not, [a]⟩]) ∧ nc [⟨GateOp.not, [a]⟩] = 1 ∧
      Rep n (gs ++ [⟨GateOp.not, [a]⟩]) (n + 2 + gs.length) (fun x => ¬ P x) := by
  refine ⟨Good_snoc hG ⟨by simp, by simp, ?_⟩, nc_not _, by simp, fun x => ?_⟩
  · intro i hi; simp at hi; subst hi; exact ha.1
  · have h1 := ha.2 x
    rw [Rep_gate]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_eq_true']
    rw [← h1]
    cases (W gs (env n x)).getD a false <;> simp

lemma bigOr {n : ℕ} {gs : List Gate} (hG : Good (n + 2) gs) (L : List ℕ)
    (f : ℕ → ℕ) (P : ℕ → Finset (Fin n) → Prop)
    (h : ∀ i ∈ L, Rep n gs (f i) (P i)) :
    Ext n gs L.length (fun gs' w => Rep n gs' w (fun x => ∃ i ∈ L, P i x)) := by
  induction L with
  | nil =>
    exact ⟨[], n, by simpa using hG, nc_nil, by simp,
      Rep_congr (by simpa using rep_false n gs) (by simp)⟩
  | cons i0 L ih =>
    obtain ⟨hs, w, hG1, hn1, hl1, hR⟩ := ih (fun i hi => h i (by simp [hi]))
    obtain ⟨hs', w', hG2, hn2, hl2, hR'⟩ :=
      ext_or2 hG1 hR (Rep_ext (h i0 (by simp)) hs)
    refine ⟨hs ++ hs', w', by simpa using hG2, by rw [nc_append]; omega, by simp; omega, ?_⟩
    simp only [← List.append_assoc]
    exact Rep_congr hR' (fun x => by simp; exact or_comm)

lemma family {n : ℕ} (L : List ℕ) (c : ℕ → ℕ) (Q : ℕ → Finset (Fin n) → Prop)
    (Pre : List Gate → Prop) (hPre : ∀ gs hs, Pre gs → Pre (gs ++ hs))
    (step : ∀ i ∈ L, ∀ gs, Good (n + 2) gs → Pre gs →
      Ext n gs (c i) (fun gs' w => Rep n gs' w (Q i))) :
    ∀ gs, Good (n + 2) gs → Pre gs →
      ∃ hs, ∃ f : ℕ → ℕ, Good (n + 2) (gs ++ hs) ∧ nc hs = 0 ∧
        hs.length ≤ (L.map c).sum ∧ ∀ i ∈ L, Rep n (gs ++ hs) (f i) (Q i) := by
  induction L with
  | nil =>
    intro gs hG _
    exact ⟨[], fun _ => n, by simpa using hG, nc_nil, by simp, by simp⟩
  | cons i0 L ih =>
    intro gs hG hP
    obtain ⟨hs, f, hG1, hn1, hl1, hR⟩ := ih (fun i hi => step i (by simp [hi])) gs hG hP
    obtain ⟨hs', w, hG2, hn2, hl2, hR'⟩ :=
      step i0 (by simp) (gs ++ hs) hG1 (hPre _ _ hP)
    refine ⟨hs ++ hs', Function.update f i0 w, by simpa using hG2,
      by rw [nc_append]; omega, by simp; omega, ?_⟩
    intro i hi
    by_cases e : i = i0
    · subst e
      simpa using hR'
    · rw [Function.update_of_ne e]
      have hi' : i ∈ L := by simpa [e] using hi
      simpa using Rep_ext (hR i hi') hs'

def cntL {n : ℕ} (L : List (Fin n)) (x : Finset (Fin n)) : ℕ :=
  (L.filter (fun i => decide (i ∈ x))).length

lemma cntL_le_length {n : ℕ} (L : List (Fin n)) (x : Finset (Fin n)) :
    cntL L x ≤ L.length := List.length_filter_le _ _

lemma cntL_cons {n : ℕ} (a : Fin n) (tl : List (Fin n)) (x : Finset (Fin n)) :
    cntL (a :: tl) x = (if a ∈ x then 1 else 0) + cntL tl x := by
  unfold cntL
  by_cases ha : a ∈ x
  · simp [ha, Nat.add_comm]
  · simp [ha]

lemma cntL_eq_card_inter {n : ℕ} (L : List (Fin n)) (hnd : L.Nodup) (x : Finset (Fin n)) :
    cntL L x = (L.toFinset ∩ x).card := by
  induction L with
  | nil => simp [cntL]
  | cons a tl ih =>
    rw [List.nodup_cons] at hnd
    rw [cntL_cons, ih hnd.2]
    simp only [List.toFinset_cons]
    by_cases ha : a ∈ x
    · have hEq : insert a tl.toFinset ∩ x = insert a (tl.toFinset ∩ x) := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hu, hux⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hu, hux⟩
        · rintro (rfl | ⟨hu, hux⟩)
          · exact ⟨Or.inl rfl, ha⟩
          · exact ⟨Or.inr hu, hux⟩
      have hnot : a ∉ tl.toFinset ∩ x := by
        intro hmem
        exact hnd.1 (List.mem_toFinset.mp (Finset.mem_inter.mp hmem).1)
      simp only [ha, ↓reduceIte]
      rw [hEq, Finset.card_insert_of_notMem hnot, Nat.add_comm]
    · have hEq : insert a tl.toFinset ∩ x = tl.toFinset ∩ x := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hu, hux⟩
          · exact absurd hux ha
          · exact ⟨hu, hux⟩
        · rintro ⟨hu, hux⟩
          exact ⟨Or.inr hu, hux⟩
      simp only [ha, ↓reduceIte]
      rw [hEq, Nat.zero_add]

lemma cntL_finRange (n : ℕ) (x : Finset (Fin n)) :
    cntL (List.finRange n) x = x.card := by
  rw [cntL_eq_card_inter _ (List.nodup_finRange n) x]
  have hto : (List.finRange n).toFinset = Finset.univ := by
    ext i; simp
  rw [hto, Finset.univ_inter]

lemma cntL_finRange_erase (n : ℕ) (j : Fin n) (x : Finset (Fin n)) :
    cntL ((List.finRange n).erase j) x = (x.erase j).card := by
  rw [cntL_eq_card_inter _ ((List.nodup_finRange n).erase j) x]
  have hto : ((List.finRange n).erase j).toFinset ∩ x = x.erase j := by
    ext i
    simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_erase,
      (List.nodup_finRange n).mem_erase_iff, List.mem_finRange, and_true]
  rw [hto]

lemma unaryCounter {n : ℕ} (L : List (Fin n)) (gs : List Gate) (hG : Good (n + 2) gs) :
    ∃ hs, ∃ u : ℕ → ℕ, Good (n + 2) (gs ++ hs) ∧ nc hs = 0 ∧
      hs.length ≤ 2 * L.length * (L.length + 1) ∧
      ∀ k : ℕ, Rep n (gs ++ hs) (u k) (fun x => k ≤ cntL L x) := by
  induction L with
  | nil =>
    refine ⟨[], fun k => if k = 0 then n + 1 else n, by simpa using hG, nc_nil, by simp, ?_⟩
    intro k
    by_cases hk : k = 0
    · subst hk; simpa using Rep_congr (rep_true n gs) (fun x => by simp)
    · simp only [hk, ↓reduceIte, List.append_nil]
      exact Rep_congr (rep_false n gs) (fun x => by simp [cntL]; omega)
  | cons a tl ih =>
    obtain ⟨hs₁, u₁, hG₁, hn₁, hl₁, hR₁⟩ := ih
    set m := tl.length
    have hstep : ∀ k ∈ (List.range (m + 1)).map (· + 1),
        ∀ gs', Good (n + 2) gs' →
          (∀ j : ℕ, Rep n gs' (u₁ j) (fun x => j ≤ cntL tl x)) →
          Ext n gs' 2 (fun gs'' w => Rep n gs'' w (fun x => k ≤ cntL (a :: tl) x)) := by
      intro k hk gs' hG' hRu
      have hk1 : 1 ≤ k := by
        simp only [List.mem_map, List.mem_range] at hk
        rcases hk with ⟨r, _, rfl⟩; omega
      obtain ⟨hsa, wa, hGa, hna, hla, hRa⟩ := ext_and2 hG' (hRu (k - 1)) (rep_input n gs' a)
      obtain ⟨hsb, wb, hGb, hnb, hlb, hRb⟩ := ext_or2 hGa (Rep_ext (hRu k) hsa) hRa
      refine ⟨hsa ++ hsb, wb, by simpa using hGb, by rw [nc_append]; omega, by simp; omega, ?_⟩
      simp only [← List.append_assoc]
      refine Rep_congr hRb (fun x => ?_)
      rw [cntL_cons]
      by_cases ha : a ∈ x <;> simp [ha] <;> omega
    obtain ⟨hs₂, f₂, hG₂, hn₂, hl₂, hR₂⟩ :=
      family ((List.range (m + 1)).map (· + 1)) (fun _ => 2)
        (fun k x => k ≤ cntL (a :: tl) x)
        (fun gs' => ∀ j : ℕ, Rep n gs' (u₁ j) (fun x => j ≤ cntL tl x))
        (fun gs' hs' h j => Rep_ext (h j) hs')
        hstep (gs ++ hs₁) hG₁ hR₁
    have hsum2 : (((List.range (m + 1)).map (· + 1)).map (fun _ => 2)).sum = 2 * (m + 1) := by
      rw [List.map_map]
      change ((List.range (m + 1)).map (fun _ => 2)).sum = 2 * (m + 1)
      simp [Nat.mul_comm]
    rw [hsum2] at hl₂
    let u₂ : ℕ → ℕ := fun k =>
      if k = 0 then n + 1 else if k ≤ m + 1 then f₂ k else n
    refine ⟨hs₁ ++ hs₂, u₂, by simpa using hG₂, by rw [nc_append]; omega, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]
      change hs₁.length + hs₂.length ≤ 2 * (m + 1) * (m + 1 + 1)
      have : 2 * m * (m + 1) + 2 * (m + 1) ≤ 2 * (m + 1) * (m + 1 + 1) := by
        calc 2 * m * (m + 1) + 2 * (m + 1)
            = 2 * (m + 1) * (m + 1) := by ring
          _ ≤ 2 * (m + 1) * (m + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    · intro k
      simp only [u₂, ← List.append_assoc]
      by_cases hk0 : k = 0
      · subst hk0
        simpa using Rep_congr (rep_true n (gs ++ hs₁ ++ hs₂)) (fun x => by simp)
      · simp only [hk0, ↓reduceIte]
        by_cases hkm : k ≤ m + 1
        · simp only [hkm, ↓reduceIte]
          apply hR₂ k
          simp only [List.mem_map, List.mem_range]
          exact ⟨k - 1, by omega, by omega⟩
        · simp only [hkm, ↓reduceIte]
          refine Rep_congr (rep_false n (gs ++ hs₁ ++ hs₂)) (fun x => ?_)
          have hle := cntL_le_length (a :: tl) x
          simp only [List.length_cons] at hle
          simp only [false_iff]
          omega

lemma allOmissionCounters (n : ℕ) (gs : List Gate) (hG : Good (n + 2) gs) :
    ∃ hs, ∃ om : Fin n → ℕ → ℕ, Good (n + 2) (gs ++ hs) ∧ nc hs = 0 ∧
      hs.length ≤ 2 * n * n * (n + 1) ∧
      ∀ j : Fin n, ∀ k : ℕ, Rep n (gs ++ hs) (om j k) (fun x => k ≤ (x.erase j).card) := by
  have hrec : ∀ m (hm : m ≤ n),
      ∃ hs, ∃ om : ℕ → ℕ → ℕ, Good (n + 2) (gs ++ hs) ∧ nc hs = 0 ∧
        hs.length ≤ m * (2 * n * (n + 1)) ∧
        ∀ j : Fin n, j.val < m → ∀ k : ℕ,
          Rep n (gs ++ hs) (om j.val k) (fun x => k ≤ (x.erase j).card) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨[], fun _ _ => n, by simpa using hG, nc_nil, by simp, fun j hj => by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs₁, om₁, hG₁, hn₁, hl₁, hR₁⟩ := ih (by omega)
      let j0 : Fin n := ⟨m, hm⟩
      obtain ⟨hs₂, u₂, hG₂, hn₂, hl₂, hR₂⟩ :=
        unaryCounter ((List.finRange n).erase j0) (gs ++ hs₁) hG₁
      have hlen_er : ((List.finRange n).erase j0).length ≤ n := by
        have h1 := List.length_erase_le (l := List.finRange n) (a := j0)
        simp only [List.length_finRange] at h1
        exact h1
      have hhl2 : hs₂.length ≤ 2 * n * (n + 1) := by
        calc hs₂.length
            ≤ 2 * ((List.finRange n).erase j0).length *
                (((List.finRange n).erase j0).length + 1) := hl₂
          _ ≤ 2 * n * (n + 1) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left 2 hlen_er) (by omega)
      refine ⟨hs₁ ++ hs₂, Function.update om₁ m u₂, by simpa using hG₂,
        by rw [nc_append]; omega, ?_, ?_⟩
      · simp only [List.length_append]
        have : m * (2 * n * (n + 1)) + 2 * n * (n + 1) = (m + 1) * (2 * n * (n + 1)) := by ring
        omega
      · intro j hj k
        by_cases heq : j.val = m
        · have hj0 : j = j0 := Fin.ext heq
          subst hj0
          simp only [j0, Function.update_self, ← List.append_assoc]
          exact Rep_congr (hR₂ k) (fun x => by rw [cntL_finRange_erase])
        · rw [Function.update_of_ne heq, ← List.append_assoc]
          exact Rep_ext (hR₁ j (by omega) k) hs₂
  obtain ⟨hs, om, hG', hn', hl', hR'⟩ := hrec n le_rfl
  refine ⟨hs, fun j k => om j.val k, hG', hn', ?_, fun j k => hR' j j.isLt k⟩
  calc hs.length ≤ n * (2 * n * (n + 1)) := hl'
    _ = 2 * n * n * (n + 1) := by ring

lemma decodePow {n : ℕ} :
    ∀ (d M : ℕ) (g : Finset (Fin n) → ℕ),
      (∀ x, g x ≤ M) → M < 2 ^ d →
      ∀ (gs : List Gate), Good (n + 2) gs →
      ∀ (T : ℕ → ℕ), (∀ v : ℕ, Rep n gs (T v) (fun x => v ≤ g x)) →
      ∃ hs, ∃ E : ℕ → ℕ, Good (n + 2) (gs ++ hs) ∧ nc hs ≤ d ∧
        hs.length ≤ d * (4 * M + 6) ∧
        ∀ u ≤ M, Rep n (gs ++ hs) (E u) (fun x => g x = u) := by
  intro d
  induction d with
  | zero =>
    intro M g hg hMd gs hG _ _
    have hM0 : M = 0 := by simp at hMd; omega
    subst hM0
    refine ⟨[], fun _ => n + 1, by simpa using hG, by simp [nc_nil], by simp, ?_⟩
    intro u hu
    have hu0 : u = 0 := by omega
    subst hu0
    simpa using Rep_congr (rep_true n gs) (fun x => by have := hg x; simp; omega)
  | succ d ih =>
    intro M g hg hMd gs hG T hT
    set M' := M / 2
    have hg' : ∀ x, g x / 2 ≤ M' := fun x => Nat.div_le_div_right (hg x)
    have hM'd : M' < 2 ^ d := by
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega
    have hT' : ∀ v : ℕ, Rep n gs (T (2 * v)) (fun x => v ≤ g x / 2) := fun v =>
      Rep_congr (hT (2 * v)) (fun x => by
        rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm])
    obtain ⟨hs₁, E', hG₁, hn₁, hl₁, hRE'⟩ := ih M' (fun x => g x / 2) hg' hM'd gs hG _ hT'
    have hT1 : ∀ v : ℕ, Rep n (gs ++ hs₁) (T v) (fun x => v ≤ g x) := fun v =>
      Rep_ext (hT v) hs₁
    
    have hstepA : ∀ u ∈ List.range (M' + 1),
        ∀ gs', Good (n + 2) gs' →
          ((∀ u' ≤ M', Rep n gs' (E' u') (fun x => g x / 2 = u')) ∧
           (∀ v, Rep n gs' (T v) (fun x => v ≤ g x))) →
          Ext n gs' 1 (fun gs'' w => Rep n gs'' w (fun x => g x / 2 = u ∧ 2 * u + 1 ≤ g x)) := by
      intro u hu gs' hG' ⟨hE', hTv⟩
      have huM : u ≤ M' := by simp at hu; omega
      exact ext_and2 hG' (hE' u huM) (hTv (2 * u + 1))
    obtain ⟨hs₂, A, hG₂, hn₂, hl₂, hRA⟩ :=
      family (List.range (M' + 1)) (fun _ => 1)
        (fun u x => g x / 2 = u ∧ 2 * u + 1 ≤ g x)
        (fun gs' => (∀ u' ≤ M', Rep n gs' (E' u') (fun x => g x / 2 = u')) ∧
          (∀ v, Rep n gs' (T v) (fun x => v ≤ g x)))
        (fun gs' hs' ⟨h1, h2⟩ => ⟨fun u' hu' => Rep_ext (h1 u' hu') hs', fun v => Rep_ext (h2 v) hs'⟩)
        hstepA (gs ++ hs₁) hG₁ ⟨hRE', hT1⟩
    have hsumA : ((List.range (M' + 1)).map (fun _ => 1)).sum = M' + 1 := by
      simp [List.sum_replicate]
    rw [hsumA] at hl₂
    
    obtain ⟨hs₃, bitW, hG₃, hn₃, hl₃, hRbit_raw⟩ :=
      bigOr hG₂ (List.range (M' + 1)) A
        (fun u x => g x / 2 = u ∧ 2 * u + 1 ≤ g x) hRA
    have hRbit : Rep n (gs ++ hs₁ ++ hs₂ ++ hs₃) bitW (fun x => g x % 2 = 1) := by
      refine Rep_congr hRbit_raw (fun x => ?_)
      constructor
      · rintro ⟨u, _, h1, h2⟩; omega
      · intro hmod
        refine ⟨g x / 2, ?_, rfl, by omega⟩
        have := hg' x
        simp only [List.mem_range]; omega
    
    obtain ⟨hG₄, hn₄, hRnbit_raw⟩ := rep_not hG₃ hRbit
    set nbitG : Gate := ⟨GateOp.not, [bitW]⟩
    set nbitW : ℕ := n + 2 + (gs ++ hs₁ ++ hs₂ ++ hs₃).length
    have hRnbit : Rep n (gs ++ hs₁ ++ hs₂ ++ hs₃ ++ [nbitG]) nbitW (fun x => g x % 2 = 0) :=
      Rep_congr hRnbit_raw (fun x => by omega)
    have hRbit4 : Rep n (gs ++ hs₁ ++ hs₂ ++ hs₃ ++ [nbitG]) bitW (fun x => g x % 2 = 1) :=
      Rep_ext hRbit [nbitG]
    have hRE'4 : ∀ u' ≤ M',
        Rep n (gs ++ hs₁ ++ hs₂ ++ hs₃ ++ [nbitG]) (E' u') (fun x => g x / 2 = u') := by
      intro u' hu'
      have := Rep_ext (hRE' u' hu') (hs₂ ++ hs₃ ++ [nbitG])
      simpa only [List.append_assoc] using this
    
    have hstepE : ∀ w ∈ List.range (M + 1),
        ∀ gs', Good (n + 2) gs' →
          ((∀ u' ≤ M', Rep n gs' (E' u') (fun x => g x / 2 = u')) ∧
           Rep n gs' bitW (fun x => g x % 2 = 1) ∧
           Rep n gs' nbitW (fun x => g x % 2 = 0)) →
          Ext n gs' 1 (fun gs'' ow => Rep n gs'' ow (fun x => g x = w)) := by
      intro w hw gs' hG' ⟨hE', hb1, hb0⟩
      have hwM : w / 2 ≤ M' := by simp at hw; omega
      by_cases hmod : w % 2 = 0
      · obtain ⟨hs', ow, hGo, hno, hlo, hRo⟩ := ext_and2 hG' (hE' (w / 2) hwM) hb0
        exact ⟨hs', ow, hGo, hno, hlo, Rep_congr hRo (fun x => by omega)⟩
      · obtain ⟨hs', ow, hGo, hno, hlo, hRo⟩ := ext_and2 hG' (hE' (w / 2) hwM) hb1
        exact ⟨hs', ow, hGo, hno, hlo, Rep_congr hRo (fun x => by omega)⟩
    obtain ⟨hs₅, E, hG₅, hn₅, hl₅, hRE⟩ :=
      family (List.range (M + 1)) (fun _ => 1) (fun w x => g x = w)
        (fun gs' => (∀ u' ≤ M', Rep n gs' (E' u') (fun x => g x / 2 = u')) ∧
          Rep n gs' bitW (fun x => g x % 2 = 1) ∧
          Rep n gs' nbitW (fun x => g x % 2 = 0))
        (fun gs' hs' ⟨h1, h2, h3⟩ =>
          ⟨fun u' hu' => Rep_ext (h1 u' hu') hs', Rep_ext h2 hs', Rep_ext h3 hs'⟩)
        hstepE (gs ++ hs₁ ++ hs₂ ++ hs₃ ++ [nbitG]) hG₄ ⟨hRE'4, hRbit4, hRnbit⟩
    have hsumE : ((List.range (M + 1)).map (fun _ => 1)).sum = M + 1 := by
      simp [List.sum_replicate]
    rw [hsumE] at hl₅
    refine ⟨hs₁ ++ hs₂ ++ hs₃ ++ [nbitG] ++ hs₅, E, ?_, ?_, ?_, ?_⟩
    · simpa only [List.append_assoc] using hG₅
    · simp only [nc_append]
      omega
    · simp only [List.length_append, List.length_singleton, List.length_range] at hl₃ ⊢
      have hM'le : M' ≤ M := Nat.div_le_self M 2
      have hih_le : d * (4 * M' + 6) ≤ d * (4 * M + 6) :=
        Nat.mul_le_mul_left d (by omega)
      have hsucc : (d + 1) * (4 * M + 6) = d * (4 * M + 6) + (4 * M + 6) := by ring
      omega
    · intro u hu
      have := hRE u (by simp only [List.mem_range]; omega)
      simpa only [List.append_assoc] using this

lemma nat_lt_two_pow (m : ℕ) : m < 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.pow_succ]
    omega

def sortedList (n : ℕ) (S : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun k => decide (k ∈ S))

lemma sortedList_pairwise (n : ℕ) (S : Finset (Fin n)) :
    (sortedList n S).Pairwise (· < ·) := by
  unfold sortedList
  apply List.Pairwise.filter
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_finRange]
  exact hij

lemma sortedList_nodup (n : ℕ) (S : Finset (Fin n)) :
    (sortedList n S).Nodup :=
  (sortedList_pairwise n S).imp (fun h => ne_of_lt h)

lemma mem_sortedList (n : ℕ) (S : Finset (Fin n)) (k : Fin n) :
    k ∈ sortedList n S ↔ k ∈ S := by
  simp [sortedList, List.mem_finRange]

lemma sortedList_length (n : ℕ) (S : Finset (Fin n)) :
    (sortedList n S).length = S.card := by
  have hto : (sortedList n S).toFinset = S := by
    ext k; simp [mem_sortedList]
  calc (sortedList n S).length
      = (sortedList n S).toFinset.card := (List.toFinset_card_of_nodup (sortedList_nodup n S)).symm
    _ = S.card := congrArg Finset.card hto

end Construction
end PEqualNP.Outside.L_meta_50576

namespace PEqualNP.Outside.L_meta_50576
open PEqualNP.CircuitLowerBounds
lemma weightedSlot (n b p : ℕ) (S : Finset (Fin n)) (hn : 0 < n) (hS : S.card ≤ 2 ^ b - 1) :
    ∃ (C : Circuit) (tap : Fin n → Fin (n + 2 + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧
      PEqualNP.NotBracket.notCount C ≤ b ∧
      C.size ≤ 32 * (n + 1) ^ 3 ∧
      ∀ (x : Finset (Fin n)) (j k : Fin n), j ∉ x → x.card = k.val →
        (C.wires (env n x)).getD (tap j).val false = decide (k ∈ S ∨ p ≤ k.val) ∧
        (C.wires (env n (insert j x))).getD (tap j).val false = decide (k ∉ S ∧ p ≤ k.val) := by
    set M := S.card
    have hMn : M ≤ n := by
      calc M = S.card := rfl
        _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ S
        _ = n := by simp
    have hpowb : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by omega)
    have hMb : M < 2 ^ b := by omega
    set d := min b M
    have hdb : d ≤ b := min_le_left _ _
    have hdM : d ≤ M := min_le_right _ _
    have hMd : M < 2 ^ d := by rcases le_total b M with h | h <;> simp [d, h, hMb, nat_lt_two_pow]
    set L := sortedList n S
    have hLlen : L.length = M := sortedList_length n S
    let r : ℕ → ℕ := fun i => if h : i < M then (L[i]'(by omega)).val else 0
    have hr_mono : ∀ i₁ i₂, i₁ < i₂ → i₂ < M → r i₁ < r i₂ := by
      intro i₁ i₂ h12 h2M
      have h1M : i₁ < M := by omega
      have h1L : i₁ < (sortedList n S).length := by rw [sortedList_length]; exact h1M
      have h2L : i₂ < (sortedList n S).length := by rw [sortedList_length]; exact h2M
      simp only [r, h1M, h2M, ↓reduceDIte]
      exact (List.pairwise_iff_getElem.mp (sortedList_pairwise n S)) i₁ i₂ h1L h2L h12
    have hr_mem : ∀ i (hi : i < M), L[i]'(by omega) ∈ S := by
      intro i hi
      exact (mem_sortedList n S _).mp (List.getElem_mem _)
    have hmem_r : ∀ k : Fin n, k ∈ S ↔ ∃ i < M, r i = k.val := by
      intro k
      constructor
      · intro hk
        have hkm : k ∈ L := (mem_sortedList n S k).mpr hk
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hkm
        refine ⟨i, by omega, ?_⟩
        simp only [r, show i < M by omega, ↓reduceDIte]
        exact congrArg Fin.val heq
      · rintro ⟨i, hi, heq⟩
        have hmem := hr_mem i hi
        have hkeq : L[i]'(by omega) = k := by
          apply Fin.ext
          simp only [r, hi, ↓reduceDIte] at heq
          exact heq
        rwa [hkeq] at hmem
    let stage : Finset (Fin n) → ℕ := fun x =>
      (S.filter (fun k => k.val < x.card)).card
    have hstage_le : ∀ x, stage x ≤ M := fun x => Finset.card_le_card (Finset.filter_subset _ _)
    have hstage_thresh : ∀ (v : ℕ) (x : Finset (Fin n)),
        v ≤ stage x ↔ (if v = 0 then True else if v ≤ M then r (v - 1) + 1 ≤ x.card else False) := by
      intro v x
      by_cases hv0 : v = 0
      · subst hv0; simp
      · simp only [hv0, ↓reduceIte]
        by_cases hvM : v ≤ M
        · simp only [hvM, ↓reduceIte]
          constructor
          · intro hv
            by_contra hlt
            have hle : x.card ≤ r (v - 1) := by omega
            have hsub : S.filter (fun k => k.val < x.card) ⊆
                (Finset.range (v - 1)).image (fun i => if h : i < M then L[i]'(by omega) else ⟨0, hn⟩) := by
              intro k hk
              obtain ⟨hkS, hkx⟩ := Finset.mem_filter.mp hk
              obtain ⟨i, hiM, hir⟩ := (hmem_r k).mp hkS
              have hiv : i < v - 1 := by
                by_contra hge
                by_cases heq : i = v - 1
                · subst heq; omega
                · have := hr_mono (v - 1) i (by omega) hiM
                  omega
              refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hiv, ?_⟩
              simp only [hiM, ↓reduceDIte]
              apply Fin.ext
              simp only [r, hiM, ↓reduceDIte] at hir
              exact hir
            have hcard : stage x ≤ v - 1 := by
              calc stage x ≤ ((Finset.range (v - 1)).image _).card := Finset.card_le_card hsub
                _ ≤ (Finset.range (v - 1)).card := Finset.card_image_le
                _ = v - 1 := Finset.card_range _
            omega
          · intro hge
            let f : ℕ → Fin n := fun i => if h : i < M then L[i]'(by omega) else ⟨0, hn⟩
            have hf_inj : Set.InjOn f (Finset.range v) := by
              intro i₁ hi₁ i₂ hi₂ hfeq
              simp only [Finset.coe_range, Set.mem_Iio] at hi₁ hi₂
              have h1M : i₁ < M := by omega
              have h2M : i₂ < M := by omega
              dsimp only [f] at hfeq
              simp only [h1M, h2M, ↓reduceDIte] at hfeq
              by_contra hne
              rcases lt_or_gt_of_ne hne with hlt | hlt
              · have := hr_mono i₁ i₂ hlt h2M
                simp only [r, h1M, h2M, ↓reduceDIte] at this
                rw [hfeq] at this; omega
              · have := hr_mono i₂ i₁ hlt h1M
                simp only [r, h1M, h2M, ↓reduceDIte] at this
                rw [hfeq] at this; omega
            have hsub : (Finset.range v).image f ⊆ S.filter (fun k => k.val < x.card) := by
              intro k hk
              obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
              have hiv : i < v := Finset.mem_range.mp hi
              have hiM : i < M := by omega
              simp only [f, hiM, ↓reduceDIte, Finset.mem_filter]
              refine ⟨hr_mem i hiM, ?_⟩
              by_cases heq : i = v - 1
              · subst heq
                simp only [r, hiM, ↓reduceDIte] at hge
                omega
              · have hlt := hr_mono i (v - 1) (by omega) (by omega)
                simp only [r, hiM, show v - 1 < M by omega, ↓reduceDIte] at hlt hge
                omega
            calc v = (Finset.range v).card := (Finset.card_range v).symm
              _ = ((Finset.range v).image f).card := (Finset.card_image_of_injOn hf_inj).symm
              _ ≤ stage x := Finset.card_le_card hsub
        · simp only [hvM, ↓reduceIte, iff_false]
          have := hstage_le x; omega
    let lo (i : ℕ) := if i = 0 then 0 else r (i-1)+1
    let hi (i : ℕ) := if i < M then r i else n
    let cut (i : ℕ) := max (lo i) (min p (hi i))
    have hbelow (x : Finset (Fin n)) : lo (stage x) ≤ x.card := by
      have H := (hstage_thresh (stage x) x).mp le_rfl
      by_cases hz : stage x = 0
      · simp [lo,hz]
      · simpa [lo,hz,hstage_le] using H
    have habove (x : Finset (Fin n)) : x.card ≤ hi (stage x) := by
      have H := (hstage_thresh (stage x+1) x).not.mp (by omega)
      by_cases h : stage x < M
      · simp [hi,h,show stage x+1 ≤ M by omega] at *; omega
      · simpa [hi,h] using Finset.card_le_univ x
    have upper_eq (x : Finset (Fin n)) (k : Fin n) (hx : x.card = k.val) : hi (stage x) = k.val ↔ k ∈ S := by
      constructor
      · intro H
        by_cases h : stage x < M
        · exact (hmem_r k).2 ⟨_,h,by simpa [hi,h] using H⟩
        · simp [hi,h] at H; omega
      · intro hk
        obtain ⟨i,hiM,hr⟩ := (hmem_r k).1 hk
        have hs : stage x = i := by
          apply Nat.le_antisymm
          · have H := (hstage_thresh (i+1) x).not.mpr (by simp [show i+1 ≤ M by omega,hr,hx]); omega
          · rw [hstage_thresh]; by_cases hz : i = 0
            · simp [hz]
            · have := hr_mono (i-1) i (by omega) hiM
              simp [hz,show i ≤ M by omega]; omega
        simp [hi,hs,hiM,hr]
    have lower_eq (x : Finset (Fin n)) (k : Fin n) (hx : x.card = k.val+1) : lo (stage x) = k.val+1 ↔ k ∈ S := by
      constructor
      · intro H; by_cases hz : stage x = 0
        · simp [lo,hz] at H
        · have hs := hstage_le x
          exact (hmem_r k).2 ⟨stage x-1, by omega, by simpa [lo,hz] using H⟩
      · intro hk
        obtain ⟨i,hiM,hr⟩ := (hmem_r k).1 hk
        have hs : stage x = i+1 := by
          have hge := (hstage_thresh (i+1) x).2 (by simp [show i+1 ≤ M by omega,hr,hx])
          by_contra hne
          have hlt : i+2 ≤ stage x := by omega
          have hle := hstage_le x
          have H := (hstage_thresh (i+2) x).1 hlt
          simp [show i+2 ≤ M by omega] at H
          have := hr_mono i (i+1) (by omega) (by omega); omega
        simp [lo,hs,hr]
    
    obtain ⟨gs₁, glob, hG₁, hn₁, hl₁, hRglob⟩ :=
      unaryCounter (List.finRange n) [] (Good_nil (n + 2))
    simp only [List.nil_append, List.length_finRange] at hG₁ hl₁ hRglob
    
    obtain ⟨hs₂, om, hG₂, hn₂, hl₂, hRom⟩ := allOmissionCounters n gs₁ hG₁
    set gs₂ := gs₁ ++ hs₂
    have hRglob2 : ∀ k, Rep n gs₂ (glob k) (fun x => k ≤ x.card) := fun k =>
      Rep_congr (Rep_ext (hRglob k) hs₂) (fun x => by rw [cntL_finRange])
    
    let T : ℕ → ℕ := fun v =>
      if v = 0 then n + 1 else if v ≤ M then glob (r (v - 1) + 1) else n
    have hRT : ∀ v, Rep n gs₂ (T v) (fun x => v ≤ stage x) := by
      intro v
      refine Rep_congr ?_ (fun x => (hstage_thresh v x).symm)
      dsimp only [T]
      by_cases hv0 : v = 0
      · simp only [hv0, ↓reduceIte]; exact rep_true n gs₂
      · simp only [hv0, ↓reduceIte]
        by_cases hvM : v ≤ M
        · simp only [hvM, ↓reduceIte]; exact hRglob2 (r (v - 1) + 1)
        · simp only [hvM, ↓reduceIte]; exact rep_false n gs₂
    obtain ⟨hs₃, E, hG₃, hn₃, hl₃, hRE⟩ := decodePow d M stage hstage_le hMd gs₂ hG₂ T hRT
    set gs₃ := gs₂ ++ hs₃
    have hRom3 : ∀ j : Fin n, ∀ k, Rep n gs₃ (om j k) (fun x => k ≤ (x.erase j).card) :=
      fun j k => Rep_ext (hRom j k) hs₃
    
    have hstepJ : ∀ jv ∈ List.range n,
        ∀ gs', Good (n + 2) gs' →
          ((∀ u ≤ M, Rep n gs' (E u) (fun x => stage x = u)) ∧
           (∀ j : Fin n, ∀ k, Rep n gs' (om j k) (fun x => k ≤ (x.erase j).card))) →
          Ext n gs' (2 * (M+1)) (fun gs'' w =>
            Rep n gs'' w (fun x =>
              if hj : jv < n then
                ∃ i ∈ List.range (M+1), stage x = i ∧ cut i ≤ (x.erase ⟨jv, hj⟩).card
              else False)) := by
      intro jv hjv gs' hG' ⟨hE', hom'⟩
      have hjlt : jv < n := List.mem_range.mp hjv
      let jf : Fin n := ⟨jv, hjlt⟩
      have hstepI : ∀ i ∈ List.range (M+1),
          ∀ gs1, Good (n + 2) gs1 →
            ((∀ u ≤ M, Rep n gs1 (E u) (fun x => stage x = u)) ∧
             (∀ k, Rep n gs1 (om jf k) (fun x => k ≤ (x.erase jf).card))) →
            Ext n gs1 1 (fun gs2 w =>
              Rep n gs2 w (fun x => stage x = i ∧ cut i ≤ (x.erase jf).card)) := by
        intro i hi gs1 hG1 ⟨hE1, hom1⟩
        have hiM : i < M+1 := List.mem_range.mp hi
        exact ext_and2 hG1 (hE1 i (by omega)) (hom1 (cut i))
      obtain ⟨hsa, B, hGa, hna, hla, hRB⟩ :=
        family (List.range (M+1)) (fun _ => 1)
          (fun i x => stage x = i ∧ cut i ≤ (x.erase jf).card)
          (fun gs1 => (∀ u ≤ M, Rep n gs1 (E u) (fun x => stage x = u)) ∧
            (∀ k, Rep n gs1 (om jf k) (fun x => k ≤ (x.erase jf).card)))
          (fun gs1 hs1 ⟨h1, h2⟩ => ⟨fun u hu => Rep_ext (h1 u hu) hs1, fun k => Rep_ext (h2 k) hs1⟩)
          hstepI gs' hG' ⟨hE', hom' jf⟩
      have hsumI : ((List.range (M+1)).map (fun _ => 1)).sum = M+1 := by simp [List.sum_replicate]
      rw [hsumI] at hla
      obtain ⟨hsb, w, hGb, hnb, hlb, hRw⟩ :=
        bigOr hGa (List.range (M+1)) B (fun i x => stage x = i ∧ cut i ≤ (x.erase jf).card) hRB
      simp only [List.length_range] at hlb
      refine ⟨hsa ++ hsb, w, by simpa using hGb, by rw [nc_append]; omega, by simp; omega, ?_⟩
      simp only [← List.append_assoc]
      exact Rep_congr hRw (fun x => by simp [hjlt, jf])
    obtain ⟨hs₄, tapW, hG₄, hn₄, hl₄, hRtap⟩ :=
      family (List.range n) (fun _ => 2 * (M+1))
        (fun jv x =>
          if hj : jv < n then
            ∃ i ∈ List.range (M+1), stage x = i ∧ cut i ≤ (x.erase ⟨jv, hj⟩).card
          else False)
        (fun gs' => (∀ u ≤ M, Rep n gs' (E u) (fun x => stage x = u)) ∧
          (∀ j : Fin n, ∀ k, Rep n gs' (om j k) (fun x => k ≤ (x.erase j).card)))
        (fun gs' hs' ⟨h1, h2⟩ =>
          ⟨fun u hu => Rep_ext (h1 u hu) hs', fun j k => Rep_ext (h2 j k) hs'⟩)
        hstepJ gs₃ hG₃ ⟨hRE, hRom3⟩
    have hsumJ : ((List.range n).map (fun _ => 2 * (M+1))).sum = n * (2 * (M+1)) := by
      simp [List.sum_replicate]
    rw [hsumJ] at hl₄
    set gs₄ := gs₃ ++ hs₄
    have hRtap' : ∀ j : Fin n,
        Rep n gs₄ (tapW j.val) (fun x => cut (stage x) ≤ (x.erase j).card) := by
      intro j
      refine Rep_congr (hRtap j.val (List.mem_range.mpr j.isLt)) (fun x => ?_)
      simp only [j.isLt, ↓reduceDIte, Fin.eta, List.mem_range]
      constructor
      · rintro ⟨i,_,rfl,h⟩; exact h
      · intro h; exact ⟨_, Nat.lt_succ_of_le (hstage_le x),rfl,h⟩
    refine ⟨⟨gs₄, 0⟩, fun j => ⟨tapW j.val, (hRtap' j).1⟩,
      good_fanInTwo hG₄ 0, good_readsBack hG₄ 0,
      by simp [Circuit.size], ?_, ?_, ?_⟩
    · rw [notCount_eq_nc]
      simp only [gs₄, gs₃, gs₂, nc_append]
      omega
    · show gs₄.length ≤ 32 * (n + 1) ^ 3
      have hlen_tot : gs₄.length = gs₁.length + hs₂.length + hs₃.length + hs₄.length := by
        simp [gs₄, gs₃, gs₂, Nat.add_assoc]
      have h1 : d * (4 * M + 6) ≤ n * (4 * n + 6) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : n * (2 * (M+1)) ≤ n * (2 * (n+1)) := Nat.mul_le_mul_left n (by omega)
      have hpoly : 2 * n * (n + 1) + 2 * n * n * (n + 1) + n * (4 * n + 6) + n * (2 * (n+1)) ≤
          32 * (n + 1) ^ 3 := by
        have hexp : 32 * (n + 1) ^ 3 = 32 * n ^ 3 + 96 * n ^ 2 + 96 * n + 32 := by ring
        have hlhs : 2 * n * (n + 1) + 2 * n * n * (n + 1) + n * (4 * n + 6) + n * (2 * (n+1)) =
            2 * n ^ 3 + 10 * n ^ 2 + 10 * n := by ring
        rw [hexp, hlhs]
        omega
      omega
    · intro x j k hj hx
      have hxi : (insert j x).card = k.val+1 := by simp [Finset.card_insert_of_notMem hj,hx]
      have U := upper_eq x k hx
      have L := lower_eq (insert j x) k hxi
      have B := hbelow x
      have A := habove x
      have B' := hbelow (insert j x)
      have A' := habove (insert j x)
      have ex := (hRtap' j).2 x
      have ei := (hRtap' j).2 (insert j x)
      dsimp only at ex ei
      rw [Finset.erase_eq_of_notMem hj,hx] at ex
      rw [Finset.erase_insert hj,hx] at ei
      change (W gs₄ (env n x)).getD (tapW j.val) false = _ ∧ (W gs₄ (env n (insert j x))).getD (tapW j.val) false = _
      constructor <;> apply Bool.eq_iff_iff.mpr <;> rw [decide_eq_true_eq]
      · rw [ex, ← U]; simp only [cut, max_le_iff, min_le_iff]; omega
      · rw [ei]; simp only [cut, max_le_iff, min_le_iff, ← L]; omega

end PEqualNP.Outside.L_meta_50576

namespace PEqualNP.Outside.L_meta_50576
open Finset
abbrev X (n : ℕ) := Finset (Fin n)
abbrev PEdge (n : ℕ) := X n × Fin n
def layer {n : ℕ} (k : Fin n) : Finset (PEdge n) :=
  ((univ.powersetCard k.val : Finset (X n)) ×ˢ univ).filter (fun e => e.2 ∉ e.1)
lemma mem_layer {n} (k : Fin n) (x : X n) (j : Fin n) : (x,j) ∈ layer k ↔ x.card = k.val ∧ j ∉ x := by simp [layer]
lemma sum_layer {n} (k : Fin n) (f : PEdge n → Nat) :
    ∑ e ∈ layer k, f e = ∑ x ∈ (univ.powersetCard k.val : Finset (X n)), ∑ j ∈ xᶜ, f (x,j) := by
  simp only [layer, Finset.compl_eq_univ_sdiff, Finset.sdiff_eq_filter, Finset.sum_filter, Finset.sum_product]
lemma card_layer {n} (k : Fin n) : (layer k).card = (n-k.val)*Nat.choose n k.val := by
  rw [Finset.card_eq_sum_ones, sum_layer]
  calc _ = ∑ _x ∈ (univ.powersetCard k.val : Finset (X n)), (n-k.val) := by
            apply Finset.sum_congr rfl; intro x hx
            simp [Finset.card_compl, (Finset.mem_powersetCard.mp hx).2]
       _ = _ := by simp [Nat.mul_comm]

def costNat {n} (w : ℕ → ℕ) (f : X n → Fin n → Bool) :=
  ∑ x : X n, w x.card * (univ.filter (fun j : Fin n => f x j ≠ decide (j ∉ x))).card

def edgeErr {n} (w : ℕ → ℕ) (f : X n → Fin n → Bool) (e : PEdge n) :=
  (if f e.1 e.2 = false then w e.1.card else 0) + (if f (insert e.2 e.1) e.2 = true then w (e.1.card+1) else 0)

lemma cost_edges {n} (w : ℕ → ℕ) (f : X n → Fin n → Bool) :
    costNat w f = ∑ k : Fin n, ∑ e ∈ layer k, edgeErr w f e := by
  classical
  let lo (x : X n) (j : Fin n) := if f x j = false then w x.card else 0
  let hi (x : X n) (j : Fin n) := if f x j = true then w x.card else 0
  have splitCost : costNat w f = ∑ j : Fin n, ((∑ x ∈ univ.filter (fun x : X n => j ∉ x), lo x j) +
      ∑ x ∈ univ.filter (fun x : X n => j ∈ x), hi x j) := by
    simp only [costNat,Finset.card_filter,Finset.mul_sum,Finset.sum_filter,← Finset.sum_add_distrib]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro x _
    by_cases h : j ∈ x <;> cases hv : f x j <;> simp [lo,hi,h,hv]
  have swap (j : Fin n) : (∑ x ∈ univ.filter (fun x : X n => j ∈ x), hi x j) =
      ∑ x ∈ univ.filter (fun x : X n => j ∉ x), hi (insert j x) j := by
    apply Finset.sum_bij' (fun x _ => x.erase j) (fun x _ => insert j x) <;> simp_all
  let amt (x : X n) := ∑ j ∈ xᶜ, edgeErr w f (x,j)
  have total : costNat w f = ∑ x : X n, amt x := by
    rw [splitCost]; simp_rw [swap,← Finset.sum_add_distrib, Finset.sum_filter]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _
    simp only [amt, Finset.compl_eq_univ_sdiff, Finset.sdiff_eq_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro j _
    by_cases h : j ∈ x <;> simp [h,lo,hi,edgeErr, Finset.card_insert_of_notMem]
  rw [total]; simp_rw [sum_layer]
  have group := Finset.sum_fiberwise_of_maps_to (s := (univ : Finset (X n))) (t := Finset.range (n+1)) (g := fun x => x.card)
    (fun x _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa using Finset.card_le_univ x))) amt
  rw [← group, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range]
  have hzero : (∑ x ∈ univ.filter (fun x : X n => x.card = n), amt x) = 0 := by
    apply Finset.sum_eq_zero; intro x hx
    have he : x = univ := Finset.eq_univ_of_card x (by simpa using (Finset.mem_filter.mp hx).2)
    simp [he,amt]
  rw [hzero, Nat.add_zero]; apply Finset.sum_congr rfl; intro k _
  congr 1; ext x; simp
end PEqualNP.Outside.L_meta_50576

namespace PEqualNP.Outside.L_meta_50576
open Finset
abbrev PermN (n : ℕ) := Equiv.Perm (Fin n)
def emap {n} (σ : PermN n) (e : PEdge n) : PEdge n := (e.1.map σ.toEmbedding, σ e.2)
lemma emap_trans {n} (σ τ : PermN n) (e : PEdge n) : emap τ (emap σ e) = emap (σ.trans τ) e := by simp [emap,Finset.map_map]
lemma emap_back {n} (σ : PermN n) (e : PEdge n) : emap σ.symm (emap σ e) = e := by rw [emap_trans]; simp [emap]
lemma emap_layer {n} (σ : PermN n) (e : PEdge n) (k : Fin n) : emap σ e ∈ layer k ↔ e ∈ layer k := by rcases e with ⟨x,j⟩; simp [emap,mem_layer]
lemma trans_layer {n} {k : Fin n} {a c : PEdge n} (ha : a ∈ layer k) (hc : c ∈ layer k) : ∃ ρ : PermN n, emap ρ a = c := by
  rcases a with ⟨s,j⟩; rcases c with ⟨t,l⟩
  rw [mem_layer] at ha hc
  obtain ⟨σ,H⟩ := Equiv.Perm.exists_map_finset_eq s t (ha.1.trans hc.1.symm)
  have nh : σ j ∉ t := by simpa [← H] using ha.2
  let τ := Equiv.swap (σ j) l
  refine ⟨σ.trans τ, ?_⟩
  rw [← emap_trans]; simp only [emap,H]; apply Prod.ext
  · apply Finset.eq_of_subset_of_card_le _ (by simp)
    intro u hu; obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hu
    have h1 : v ≠ σ j := fun h => nh (h ▸ hv)
    have h2 : v ≠ l := fun h => hc.2 (h ▸ hv)
    simpa [τ,Equiv.swap_apply_of_ne_of_ne h1 h2] using hv
  · simp [τ]

def prefixN {n} (t : ℕ) : X n := univ.filter (fun i : Fin n => i.val < t)
def edgeAt {n} (k : Fin n) : PEdge n := (prefixN k.val,k)
lemma edgeAt_mem {n} (k : Fin n) : edgeAt k ∈ layer k := (mem_layer ..).2 ⟨card_filter_lt n k.val (by omega),by simp [prefixN]⟩
lemma orbit_sum {n} (k : Fin n) (F : PEdge n → ℕ) :
  ∑ σ : PermN n, (layer k).card * F (emap σ (edgeAt k)) = Fintype.card (PermN n) * ∑ e ∈ layer k, F e := by
  classical
  have same (e : PEdge n) (he : e ∈ layer k) : (∑ σ : PermN n, F (emap σ e)) = ∑ σ : PermN n, F (emap σ (edgeAt k)) := by
    obtain ⟨ρ,rfl⟩ := trans_layer (edgeAt_mem k) he
    simp_rw [emap_trans]
    let E : PermN n ≃ PermN n := ⟨fun σ => ρ.trans σ, fun σ => ρ.symm.trans σ, by intro σ; ext; simp, by intro σ; ext; simp⟩
    exact Fintype.sum_equiv E _ _ (fun _ => rfl)
  have reindex (σ : PermN n) : (∑ e ∈ layer k, F (emap σ e)) = ∑ e ∈ layer k, F e := by
    apply Finset.sum_bij' (fun e _ => emap σ e) (fun e _ => emap σ.symm e)
    · exact fun a h => (emap_layer ..).2 h
    · exact fun a h => (emap_layer ..).2 h
    · exact fun a _ => emap_back σ a
    · exact fun a _ => emap_back σ.symm a
    · intros; rfl
  rw [← Finset.mul_sum]; calc
    _ = ∑ _e ∈ layer k, ∑ σ : PermN n, F (emap σ (edgeAt k)) := by simp
    _ = ∑ e ∈ layer k, ∑ σ : PermN n, F (emap σ e) := Finset.sum_congr rfl fun e h => (same e h).symm
    _ = ∑ σ : PermN n, ∑ e ∈ layer k, F (emap σ e) := Finset.sum_comm
    _ = _ := by simp_rw [reindex]; simp
end PEqualNP.Outside.L_meta_50576

namespace PEqualNP.Outside.L_meta_50576
open Finset PEqualNP.CircuitLowerBounds

def tariff {n} (w : ℕ → ℕ) (k : Fin n) := (n-k.val) * Nat.choose n k.val * min (w k.val) (w (k.val+1))
def validW (n b : ℕ) (C : Circuit) := PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b
def reported {n : ℕ} (C : Circuit) (tap : Fin n → Fin (n+2+C.size)) (x : X n) (j : Fin n) := (C.wires (env n x)).getD (tap j).val false
lemma lowerW {n b} (w : ℕ → ℕ) (C : Circuit) (tap : Fin n → Fin (n+2+C.size)) (hv : validW n b C) :
  ∃ S : Finset (Fin n), S.card < 2^b ∧ (univ \ S).sum (tariff w) ≤ costNat w (reported C tap) := by
  classical
  let f := reported C tap
  let F := edgeErr w f
  let pay (σ : PermN n) := ∑ k : Fin n, (layer k).card * F (emap σ (edgeAt k))
  have exactMean : (∑ σ : PermN n, pay σ) = Fintype.card (PermN n) * costNat w f := by
    dsimp only [pay]; rw [Finset.sum_comm,cost_edges,Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => orbit_sum k F
  obtain ⟨σ, cheap⟩ : ∃ σ : PermN n, pay σ ≤ costNat w f := by
    by_contra! h
    have H := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := PermN n)) (fun σ _ => h σ)
    simp [exactMean] at H
  let chain (t : Fin (n+1)) := (prefixN t.val : X n).map σ.toEmbedding
  have ins (k : Fin n) : insert (σ k) (chain k.castSucc) = chain k.succ := by
    have eq : insert k (prefixN k.val) = prefixN (k.val+1) := by ext i; simp [prefixN,Fin.ext_iff]; omega
    simpa [chain] using congrArg (Finset.map σ.toEmbedding) eq
  let xs (t : Fin (n+1)) := env n (chain t)
  let S := drops (I := n+2) xs C.gates
  have lepow := markov_drops_bound xs (fun t => env_len n _) (fun k i hi => env_mono n (ins k ▸ Finset.subset_insert _ _) i hi) C.gates hv.1
  have hn := notCount_eq_nc C.gates C.output
  have hc : nc C.gates ≤ b := by rw [← hn]; exact hv.2.2.2
  refine ⟨S, Nat.lt_of_lt_of_le (Nat.lt_of_succ_le lepow) (Nat.pow_le_pow_right (by decide) hc), le_trans ?_ cheap⟩
  dsimp only [pay]; rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  apply Finset.sum_le_sum; intro k _
  by_cases hk : k ∈ S
  · simp [hk]
  · simp only [hk,not_false_eq_true,ite_true]
    rw [tariff,← card_layer]; apply Nat.mul_le_mul_left
    have hbad : ¬ (f (chain k.castSucc) (σ k) = true ∧ f (chain k.succ) (σ k) = false) := by
      intro h; apply hk; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (tap (σ k)).val,(tap (σ k)).isLt,h⟩
    have hcard : (chain k.castSucc).card = k.val := by simp only [chain,Finset.card_map, Fin.val_castSucc]; exact card_filter_lt n k.val (by omega)
    change min _ _ ≤ (if f (chain k.castSucc) (σ k) = false then w (chain k.castSucc).card else 0) + (if f (insert (σ k) (chain k.castSucc)) (σ k) = true then w ((chain k.castSucc).card+1) else 0)
    rw [ins,hcard]; cases h₁ : f (chain k.castSucc) (σ k) <;> cases h₂ : f (chain k.succ) (σ k) <;> simp_all

lemma upperW {n b} (w : ℕ → ℕ) (p : ℕ) (hinc : ∀ k, k < p → w k ≤ w (k+1)) (hdec : ∀ k, p ≤ k → k < n → w (k+1) ≤ w k) (S : Finset (Fin n)) (hs : S.card < 2^b) :
  ∃ (C : Circuit) (tap : Fin n → Fin (n+2+C.size)), validW n b C ∧ C.size ≤ 32*(n+1)^3 ∧ costNat w (reported C tap) = (univ \ S).sum (tariff w) := by
  classical
  by_cases hn : n=0
  · subst n; refine ⟨⟨[],0⟩, Fin.elim0, ?_,by decide,?_⟩
    · exact ⟨good_fanInTwo (Good_nil 2) 0,good_readsBack (Good_nil 2) 0,by decide, by simp [notCount_eq_nc,nc_nil]⟩
    · simp [costNat]
  obtain ⟨C,tap,hf,hr,ho,hb,hlen,he⟩ := weightedSlot n b p S (by omega) (by omega)
  refine ⟨C,tap,⟨hf,hr,ho,hb⟩,hlen,?_⟩
  rw [cost_edges,Finset.sdiff_eq_filter,Finset.sum_filter]; apply Finset.sum_congr rfl; intro k _
  have entry (e : PEdge n) (hm : e ∈ layer k) : edgeErr w (reported C tap) e = if k ∈ S then 0 else min (w k.val) (w (k.val+1)) := by
    rcases e with ⟨x,j⟩; rw [mem_layer] at hm
    obtain ⟨l,u⟩ := he x j k hm.2 hm.1
    simp only [edgeErr,reported,l,u,hm.1]
    by_cases hk : k ∈ S <;> by_cases hp : p ≤ k.val <;> simp [hk,hp] <;> first | exact hinc _ (by omega) | exact hdec _ hp k.isLt
  rw [Finset.sum_congr rfl entry]; by_cases hk : k ∈ S <;> simp [hk,card_layer,tariff]
end PEqualNP.Outside.L_meta_50576

open PEqualNP.Outside.L_meta_50576 in
theorem PEqualNP.Outside.L_meta_50576 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n b : Nat) (w : Nat → Nat) (p : Nat), p ≤ n →
  (∀ k, k < p → w k ≤ w (k+1)) → (∀ k, p ≤ k → k < n → w (k+1) ≤ w k) →
  let X := Finset (Fin n)
  let input := fun (x : X) => List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
  let price := fun (k : Fin n) => (n-k.val)*Nat.choose n k.val * min (w k.val) (w (k.val+1))
  let cost := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Fin (n+2+C.size)) =>
    (Finset.univ : Finset X).sum (fun x => w x.card *
      ((Finset.univ : Finset (Fin n)).filter (fun j =>
        (C.wires (input x)).getD (tap j).val false ≠ decide (j ∉ x))).card)
  let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b
  (∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Fin (n+2+C.size)),
    valid C → ∃ s : Finset (Fin n), s.card < 2^b ∧ (Finset.univ \ s).sum price ≤ cost C tap) ∧
  ∀ s : Finset (Fin n), s.card < 2^b →
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Fin (n+2+C.size)),
      valid C ∧ C.size ≤ 32*(n+1)^3 ∧ cost C tap = (Finset.univ \ s).sum price) := by
  intro n b w p _ hinc hdec X input price cost valid
  have hin : ∀ x : X, input x = env n x := by
    intro x
    dsimp only [input, env]
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_ofFn]
    exact congrArg (@decide _) (Subsingleton.elim _ _)
  have he (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Fin (n+2+C.size)) : cost C tap = costNat w (reported C tap) := by
    simp only [cost,costNat,reported,hin]
    congr!
    funext a
    ext j
    constructor <;> intro H <;> obtain ⟨hm,hv⟩ := Finset.mem_filter.mp H <;>
      apply Finset.mem_filter.mpr <;> refine ⟨hm,?_⟩ <;> convert hv using 2
  constructor
  · intro C tap hv
    obtain ⟨s,hs,H⟩ := lowerW w C tap hv
    refine ⟨s,hs,?_⟩
    rw [he]; convert H using 1 <;> dsimp only [price,tariff] <;> congr!
  · intro S hs
    obtain ⟨C,tap,hv,hsize,heq⟩ := upperW w p hinc hdec S hs
    refine ⟨C,tap,hv,hsize,?_⟩
    rw [he,heq]; dsimp only [price,tariff]; congr!
