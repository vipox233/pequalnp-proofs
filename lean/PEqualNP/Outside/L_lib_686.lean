import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_686_aux

variable {α : Type} [DecidableEq α]

def gsupp (s : List (Finset α)) (ins : List ℕ) : Finset α :=
  ins.foldr (fun i acc => s.getD i ∅ ∪ acc) ∅

def sfold (s : List (Finset α)) (gs : List (List ℕ)) : List (Finset α) :=
  gs.foldl (fun s ins => s ++ [gsupp s ins]) s

def gl (s : List (Finset α)) (gs : List (List ℕ)) : List (Finset α) :=
  (sfold s gs).drop s.length

theorem mem_gsupp (s : List (Finset α)) (ins : List ℕ) (e : α) :
    e ∈ gsupp s ins ↔ ∃ i ∈ ins, e ∈ s.getD i ∅ := by
  induction ins with
  | nil => simp [gsupp]
  | cons i t ih =>
    simp only [gsupp, List.foldr_cons, Finset.mem_union, List.mem_cons] at ih ⊢
    rw [ih]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨i, Or.inl rfl, h⟩
      · exact ⟨j, Or.inr hj, h⟩
    · rintro ⟨j, hj | hj, h⟩
      · subst hj; exact Or.inl h
      · exact Or.inr ⟨j, hj, h⟩

theorem sfold_snoc (s : List (Finset α)) (gs : List (List ℕ)) (ins : List ℕ) :
    sfold s (gs ++ [ins]) = sfold s gs ++ [gsupp (sfold s gs) ins] := by
  simp [sfold, List.foldl_append]

theorem sfold_append (s : List (Finset α)) (gs hs : List (List ℕ)) :
    sfold s (gs ++ hs) = sfold (sfold s gs) hs := by
  simp [sfold, List.foldl_append]

theorem length_sfold (s : List (Finset α)) (gs : List (List ℕ)) :
    (sfold s gs).length = s.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [sfold]
  | append_singleton gs ins ih => simp [sfold_snoc, ih]; omega

theorem prefix_sfold (s : List (Finset α)) (gs : List (List ℕ)) : s <+: sfold s gs := by
  induction gs using List.reverseRecOn with
  | nil => simp [sfold]
  | append_singleton gs ins ih =>
    rw [sfold_snoc]; exact ih.trans (List.prefix_append _ _)

theorem gl_snoc (s : List (Finset α)) (gs : List (List ℕ)) (ins : List ℕ) :
    gl s (gs ++ [ins]) = gl s gs ++ [gsupp (sfold s gs) ins] := by
  unfold gl
  rw [sfold_snoc, List.drop_append_of_le_length]
  rw [length_sfold]; omega

theorem length_gl (s : List (Finset α)) (gs : List (List ℕ)) : (gl s gs).length = gs.length := by
  simp [gl, length_sfold]

theorem gsupp_sdiff (s : List (Finset α)) (ins : List ℕ) (A : Finset α) :
    gsupp (s.map (· \ A)) ins = gsupp s ins \ A := by
  ext e
  simp only [mem_gsupp, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hl : i < s.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hl)] at h
      simp only [List.getElem_map, Finset.mem_sdiff] at h
      refine ⟨⟨i, hi, ?_⟩, h.2⟩
      rw [List.getD_eq_getElem _ _ hl]; exact h.1
    · rw [List.getD_eq_default _ _ (by simpa using hl)] at h; simp at h
  · rintro ⟨⟨i, hi, h⟩, hA⟩
    by_cases hl : i < s.length
    · refine ⟨i, hi, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simpa using hl)]
      rw [List.getD_eq_getElem _ _ hl] at h
      simp [h, hA]
    · rw [List.getD_eq_default _ _ (by simpa using hl)] at h; simp at h

theorem sfold_sdiff (s : List (Finset α)) (gs : List (List ℕ)) (A : Finset α) :
    sfold (s.map (· \ A)) gs = (sfold s gs).map (· \ A) := by
  induction gs using List.reverseRecOn with
  | nil => simp [sfold]
  | append_singleton gs ins ih => rw [sfold_snoc, sfold_snoc, ih, gsupp_sdiff]; simp

theorem gl_sdiff (s : List (Finset α)) (gs : List (List ℕ)) (A : Finset α) :
    gl (s.map (· \ A)) gs = (gl s gs).map (· \ A) := by
  simp [gl, sfold_sdiff, List.map_drop]

def wt (T X : Finset α) : ℕ := if X.Nonempty ∧ X ⊆ T then 2 ^ X.card else 0

def cost (T : Finset α) (L : List (Finset α)) : ℕ := (L.map (wt T)).sum

def cnt (T : Finset α) (L : List (Finset α)) : ℕ := L.countP (fun X => X.Nonempty ∧ X ⊆ T)

def fam (T : Finset α) (L : List (Finset α)) : List (Finset α) := L.filter (fun X => X.Nonempty ∧ X ⊆ T)

def Lam (F : List (Finset α)) : Prop := ∀ X ∈ F, ∀ Y ∈ F, Disjoint X Y ∨ X ⊆ Y ∨ Y ⊆ X

inductive Cost : ℕ → ℕ → Prop
  | one : Cost 1 0
  | split {a b ca cb : ℕ} : Cost a ca → Cost b cb → Cost (a + b) (2 ^ (a + b) + ca + cb)

theorem wt_split {A T : Finset α} (hAT : A ⊆ T) (X : Finset α) :
    wt A X + wt (T \ A) (X \ A) ≤ wt T X := by
  unfold wt
  by_cases hX : X.Nonempty ∧ X ⊆ T
  · rw [if_pos hX]
    by_cases hA : X ⊆ A
    · rw [if_pos ⟨hX.1, hA⟩, if_neg]
      · simp
      · rintro ⟨hne, -⟩
        obtain ⟨e, he⟩ := hne
        rw [Finset.mem_sdiff] at he
        exact he.2 (hA he.1)
    · rw [if_neg (fun h => hA h.2), zero_add]
      split_ifs
      · exact Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card Finset.sdiff_subset)
      · exact Nat.zero_le _
  · rw [if_neg hX, if_neg (fun h => hX ⟨h.1, h.2.trans hAT⟩), if_neg]
    rintro ⟨hne, hsub⟩
    apply hX
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he⟩ := hne; exact ⟨e, (Finset.mem_sdiff.1 he).1⟩
    · intro e he
      by_cases heA : e ∈ A
      · exact hAT heA
      · exact (Finset.mem_sdiff.1 (hsub (Finset.mem_sdiff.2 ⟨he, heA⟩))).1

theorem cnt_split_pt {A T : Finset α} (hAT : A ⊆ T) (X : Finset α) :
    (if X.Nonempty ∧ X ⊆ T then 1 else 0) =
      (if X.Nonempty ∧ X ⊆ A then 1 else 0) + (if (X \ A).Nonempty ∧ X \ A ⊆ T \ A then 1 else 0) := by
  by_cases hX : X.Nonempty ∧ X ⊆ T
  · rw [if_pos hX]
    by_cases hA : X ⊆ A
    · rw [if_pos ⟨hX.1, hA⟩, if_neg]
      rintro ⟨⟨e, he⟩, -⟩
      exact (Finset.mem_sdiff.1 he).2 (hA (Finset.mem_sdiff.1 he).1)
    · rw [if_neg (fun h => hA h.2), if_pos]
      refine ⟨?_, Finset.sdiff_subset_sdiff hX.2 le_rfl⟩
      obtain ⟨e, he, heA⟩ := Finset.not_subset.1 hA
      exact ⟨e, Finset.mem_sdiff.2 ⟨he, heA⟩⟩
  · rw [if_neg hX, if_neg (fun h => hX ⟨h.1, h.2.trans hAT⟩), if_neg]
    rintro ⟨hne, hsub⟩
    apply hX
    refine ⟨?_, ?_⟩
    · obtain ⟨e, he⟩ := hne; exact ⟨e, (Finset.mem_sdiff.1 he).1⟩
    · intro e he
      by_cases heA : e ∈ A
      · exact hAT heA
      · exact (Finset.mem_sdiff.1 (hsub (Finset.mem_sdiff.2 ⟨he, heA⟩))).1

theorem cost_split {A T : Finset α} (hAT : A ⊆ T) (L : List (Finset α)) :
    cost A L + cost (T \ A) (L.map (· \ A)) ≤ cost T L := by
  induction L with
  | nil => simp [cost]
  | cons X L ih =>
    simp only [cost, List.map_cons, List.sum_cons] at ih ⊢
    have := wt_split hAT X
    omega

theorem cnt_eq_sum (T : Finset α) (L : List (Finset α)) :
    cnt T L = (L.map (fun X => if X.Nonempty ∧ X ⊆ T then 1 else 0)).sum := by
  induction L with
  | nil => simp [cnt]
  | cons X L ih =>
    simp only [cnt, List.countP_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; split_ifs <;> simp_all <;> omega

theorem cnt_split {A T : Finset α} (hAT : A ⊆ T) (L : List (Finset α)) :
    cnt T L = cnt A L + cnt (T \ A) (L.map (· \ A)) := by
  rw [cnt_eq_sum, cnt_eq_sum, cnt_eq_sum]
  induction L with
  | nil => simp
  | cons X L ih =>
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def] at ih ⊢
    rw [cnt_split_pt hAT X, ih]; ring

theorem cost_snoc (T : Finset α) (L : List (Finset α)) (X : Finset α) :
    cost T (L ++ [X]) = cost T L + wt T X := by simp [cost]

theorem cnt_snoc (T : Finset α) (L : List (Finset α)) (X : Finset α) :
    cnt T (L ++ [X]) = cnt T L + (if X.Nonempty ∧ X ⊆ T then 1 else 0) := by
  simp [cnt, List.countP_append]

theorem cost_zero {T : Finset α} {L : List (Finset α)} (h : cost T L = 0) : cnt T L = 0 := by
  induction L with
  | nil => simp [cnt]
  | cons X L ih =>
    simp only [cost, List.map_cons, List.sum_cons, Nat.add_eq_zero_iff] at h
    simp only [cnt, List.countP_cons] at ih ⊢
    rw [ih h.2]
    have : ¬ (X.Nonempty ∧ X ⊆ T) := by
      intro hX; have := h.1; simp only [wt, if_pos hX] at this; exact absurd this (by positivity)
    simp [this]

theorem fam_nil_of_cost_zero {T : Finset α} {L : List (Finset α)} (h : cost T L = 0) : fam T L = [] := by
  have h0 := cost_zero h
  simp only [cnt, List.countP_eq_zero] at h0
  simp only [fam, List.filter_eq_nil_iff]
  intro X hX; simpa using h0 X hX

theorem pt_eq_of_sum_eq {L : List (Finset α)} {f g : Finset α → ℕ} (hle : ∀ X ∈ L, f X ≤ g X)
    (hs : (L.map f).sum = (L.map g).sum) : ∀ X ∈ L, f X = g X := by
  induction L with
  | nil => simp
  | cons Y L ih =>
    simp only [List.map_cons, List.sum_cons] at hs
    have h1 := hle Y (by simp)
    have h2 : (L.map f).sum ≤ (L.map g).sum := List.sum_le_sum (fun X hX => hle X (by simp [hX]))
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · omega
    · exact ih (fun Z hZ => hle Z (by simp [hZ])) (by omega) X hX

theorem getD_mem_of_nonempty {l : List (Finset α)} {i : ℕ} (h : (l.getD i ∅).Nonempty) : l.getD i ∅ ∈ l := by
  by_cases hl : i < l.length
  · rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  · rw [List.getD_eq_default _ _ (by omega)] at h; simp at h

theorem fam_snoc (T : Finset α) (L : List (Finset α)) (X : Finset α) :
    fam T (L ++ [X]) = fam T L ++ (if X.Nonempty ∧ X ⊆ T then [X] else []) := by
  simp only [fam, List.filter_append]
  congr 1
  by_cases h : X.Nonempty ∧ X ⊆ T
  · simp [List.filter_cons, h]
  · simp [List.filter_cons, h]

theorem mem_fam {T X : Finset α} {L : List (Finset α)} : X ∈ fam T L ↔ X ∈ L ∧ X.Nonempty ∧ X ⊆ T := by
  simp [fam]

theorem core : ∀ n : ℕ, ∀ (s : List (Finset α)) (gs : List (List ℕ)) (T : Finset α),
    (∀ X ∈ s, X.card ≤ 1) → (∀ ins ∈ gs, ins.length ≤ 2) → T.card = n → 0 < n → T ∈ sfold s gs →
    ∃ c, Cost n c ∧ c ≤ cost T (gl s gs) ∧
      ((∀ c', Cost n c' → cost T (gl s gs) ≤ c') →
        cnt T (gl s gs) + 1 = n ∧ Lam (fam T (gl s gs))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro s gs T hs hgs hT hn hmem
  by_cases h1 : n = 1
  · subst h1
    refine ⟨0, Cost.one, Nat.zero_le _, fun ht => ?_⟩
    have h0 : cost T (gl s gs) = 0 := Nat.le_zero.1 (ht 0 Cost.one)
    refine ⟨by rw [cost_zero h0], ?_⟩
    rw [fam_nil_of_cost_zero h0]; intro X hX; simp at hX
  have hn2 : 2 ≤ n := by omega
  have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
  induction gs using List.reverseRecOn with
  | nil =>
    exfalso
    simp only [sfold, List.foldl_nil] at hmem
    have := hs T hmem; omega
  | append_singleton gs ins ihg =>
    have hgs' : ∀ ins ∈ gs, ins.length ≤ 2 := fun i hi => hgs i (by simp [hi])
    have hins : ins.length ≤ 2 := hgs ins (by simp)
    rw [sfold_snoc] at hmem
    rw [gl_snoc]
    set L0 := sfold s gs with hL0
    set L := gl s gs with hL
    set Xn := gsupp L0 ins with hXn
    by_cases hold : T ∈ L0
    · obtain ⟨c, hc, hcle, htight⟩ := ihg hgs' hold
      refine ⟨c, hc, ?_, fun ht => ?_⟩
      · rw [cost_snoc]; omega
      · have hw : wt T Xn = 0 := by
          have := ht c hc; rw [cost_snoc] at this; omega
        have hnot : ¬ (Xn.Nonempty ∧ Xn ⊆ T) := by
          intro h; simp only [wt, if_pos h] at hw; exact absurd hw (by positivity)
        have ht' : ∀ c', Cost n c' → cost T L ≤ c' := by
          intro c' hc'; have := ht c' hc'; rw [cost_snoc] at this; omega
        obtain ⟨h1, h2⟩ := htight ht'
        refine ⟨?_, ?_⟩
        · rw [cnt_snoc, if_neg hnot]; exact h1
        · rw [fam_snoc, if_neg hnot, List.append_nil]; exact h2
    · have hTX : T = Xn := by
        simp only [List.mem_append, List.mem_singleton] at hmem; tauto

      have key : ∃ i j, T = L0.getD i ∅ ∪ L0.getD j ∅ := by
        match ins, hins with
        | [], _ => exact absurd (hTX ▸ hTne) (by simp [hXn, gsupp])
        | [i], _ =>
          exfalso; apply hold
          have : T = L0.getD i ∅ := by rw [hTX]; simp [hXn, gsupp]
          rw [this]; exact getD_mem_of_nonempty (this ▸ hTne)
        | [i, j], _ => exact ⟨i, j, by rw [hTX]; simp [hXn, gsupp]⟩
      obtain ⟨i, j, hij⟩ := key
      set A := L0.getD i ∅ with hA
      set B := L0.getD j ∅ with hB
      have hAT : A ⊆ T := hij ▸ Finset.subset_union_left
      have hBT : B ⊆ T := hij ▸ Finset.subset_union_right
      have hAne' : A ≠ T := by
        intro h; apply hold; rw [← h]; exact getD_mem_of_nonempty (by rw [← hA, h]; exact hTne)
      have hBne' : B ≠ T := by
        intro h; apply hold; rw [← h]; exact getD_mem_of_nonempty (by rw [← hB, h]; exact hTne)
      have hAne : A.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h0; apply hBne'; rw [hij, h0, Finset.empty_union]
      have hTA : T \ A = B \ A := by
        ext e; simp only [Finset.mem_sdiff]; rw [hij]; simp only [Finset.mem_union]; tauto
      have hTAne : (T \ A).Nonempty := by
        obtain ⟨e, he, heA⟩ := Finset.not_subset.1 (fun h : T ⊆ A => hAne' (Finset.Subset.antisymm hAT h))
        exact ⟨e, Finset.mem_sdiff.2 ⟨he, heA⟩⟩
      have hBne : B.Nonempty := by
        obtain ⟨e, he⟩ := hTAne; rw [hTA] at he; exact ⟨e, (Finset.mem_sdiff.1 he).1⟩
      have hAmem : A ∈ L0 := getD_mem_of_nonempty hAne
      have hBmem : B ∈ L0 := getD_mem_of_nonempty hBne
      have hss : A ⊂ T := Finset.ssubset_iff_subset_ne.2 ⟨hAT, hAne'⟩
      have hacard : A.card < n := hT ▸ Finset.card_lt_card hss
      have hapos : 0 < A.card := Finset.card_pos.2 hAne
      have hTAcard : (T \ A).card = n - A.card := by
        have := Finset.card_sdiff_add_card_eq_card hAT; omega
      obtain ⟨ca, hca, hcale, htA⟩ := IH A.card hacard s gs A hs hgs' rfl hapos hAmem
      rw [← hL] at hcale htA
      have hs' : ∀ X ∈ s.map (· \ A), X.card ≤ 1 := by
        intro X hX; obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        exact (Finset.card_le_card Finset.sdiff_subset).trans (hs Y hY)
      have hmemB : T \ A ∈ sfold (s.map (· \ A)) gs := by
        rw [sfold_sdiff, hTA]; exact List.mem_map.2 ⟨B, hBmem, rfl⟩
      obtain ⟨cb, hcb, hcble, htB⟩ :=
        IH (n - A.card) (by omega) (s.map (· \ A)) gs (T \ A) hs' hgs' hTAcard (by omega) hmemB
      rw [gl_sdiff, ← hL] at hcble htB
      have hcast : ∀ {x y : ℕ}, Cost A.card x → Cost (n - A.card) y → Cost n (2 ^ n + x + y) := by
        intro x y hx hy
        have := Cost.split hx hy
        rwa [show A.card + (n - A.card) = n by omega] at this
      have hwT : wt T T = 2 ^ n := by simp [wt, hTne, hT]
      have hsplit := cost_split hAT L
      have hXnT : Xn = T := hTX.symm
      rw [hXnT]
      refine ⟨2 ^ n + ca + cb, hcast hca hcb, ?_, fun ht => ?_⟩
      · rw [cost_snoc, hwT]; omega
      · simp only [cost_snoc, hwT] at ht
        have tA : ∀ c', Cost A.card c' → cost A L ≤ c' := by
          intro c' hc'; have := ht _ (hcast hc' hcb); omega
        have tB : ∀ c', Cost (n - A.card) c' → cost (T \ A) (L.map (· \ A)) ≤ c' := by
          intro c' hc'; have := ht _ (hcast hca hc'); omega
        obtain ⟨cA, lA⟩ := htA tA
        obtain ⟨cB, lB⟩ := htB tB
        have heq : cost A L + cost (T \ A) (L.map (· \ A)) = cost T L := by
          have := ht _ (hcast hca hcb); omega
        have hpt : ∀ X ∈ L, wt A X + wt (T \ A) (X \ A) = wt T X := by
          apply pt_eq_of_sum_eq (fun X _ => wt_split hAT X)
          have e1 : (L.map (fun X => wt A X + wt (T \ A) (X \ A))).sum = cost A L + cost (T \ A) (L.map (· \ A)) := by
            simp [cost, List.sum_map_add, List.map_map, Function.comp_def]
          rw [e1, heq]; rfl
        have hdisj : ∀ X ∈ L, X.Nonempty → X ⊆ T → ¬ X ⊆ A → Disjoint X A := by
          intro X hX hne hsub hnA
          have h := hpt X hX
          have hXA : (X \ A).Nonempty ∧ X \ A ⊆ T \ A := by
            refine ⟨?_, Finset.sdiff_subset_sdiff hsub le_rfl⟩
            obtain ⟨e, he, heA⟩ := Finset.not_subset.1 hnA
            exact ⟨e, Finset.mem_sdiff.2 ⟨he, heA⟩⟩
          have hTX' : X.Nonempty ∧ X ⊆ T := ⟨hne, hsub⟩
          have hnA' : ¬ (X.Nonempty ∧ X ⊆ A) := fun h' => hnA h'.2
          unfold wt at h
          rw [if_pos hTX', if_neg hnA', if_pos hXA, zero_add] at h
          have hc : (X \ A).card = X.card := Nat.pow_right_injective (le_refl 2) h
          have : X \ A = X := Finset.eq_of_subset_of_card_le Finset.sdiff_subset (by omega)
          exact Finset.disjoint_iff_ne.2 (fun a ha b hb hab => by
            rw [← this] at ha; exact (Finset.mem_sdiff.1 ha).2 (hab ▸ hb))
        refine ⟨?_, ?_⟩
        · rw [cnt_snoc, if_pos ⟨hTne, le_rfl⟩, cnt_split hAT L]; omega
        · rw [fam_snoc, if_pos ⟨hTne, le_rfl⟩]
          have cls : ∀ X ∈ fam T L ++ [T], X = T ∨ (X ∈ fam A L) ∨ (Disjoint X A ∧ X ∈ fam (T \ A) (L.map (· \ A))) := by
            intro X hX
            rcases List.mem_append.1 hX with hX | hX
            · obtain ⟨hXL, hne, hsub⟩ := mem_fam.1 hX
              by_cases hXA : X ⊆ A
              · exact Or.inr (Or.inl (mem_fam.2 ⟨hXL, hne, hXA⟩))
              · have hd := hdisj X hXL hne hsub hXA
                refine Or.inr (Or.inr ⟨hd, mem_fam.2 ⟨?_, ?_, ?_⟩⟩)
                · rw [← Finset.sdiff_eq_self_of_disjoint hd]; exact List.mem_map.2 ⟨X, hXL, rfl⟩
                · exact hne
                · intro e he; rw [Finset.mem_sdiff]
                  exact ⟨hsub he, Finset.disjoint_left.1 hd he⟩
            · exact Or.inl (List.mem_singleton.1 hX)
          have subT : ∀ X ∈ fam T L ++ [T], X ⊆ T := by
            intro X hX
            rcases List.mem_append.1 hX with hX | hX
            · exact (mem_fam.1 hX).2.2
            · rw [List.mem_singleton.1 hX]
          intro X hX Y hY
          rcases cls X hX with rfl | hXa | ⟨hXd, hXb⟩
          · exact Or.inr (Or.inr (subT Y hY))
          · rcases cls Y hY with rfl | hYa | ⟨hYd, hYb⟩
            · exact Or.inr (Or.inl (subT X hX))
            · exact lA X hXa Y hYa
            · exact Or.inl (Finset.disjoint_of_subset_left (mem_fam.1 hXa).2.2 hYd.symm)
          · rcases cls Y hY with rfl | hYa | ⟨hYd, hYb⟩
            · exact Or.inr (Or.inl (subT X hX))
            · exact Or.inl (Finset.disjoint_of_subset_left (mem_fam.1 hYa).2.2 hXd.symm).symm
            · exact lB X hXb Y hYb

open PEqualNP.CircuitLowerBounds in
theorem foldl_wires (i : α) : ∀ (gates : List Gate) (w : List Bool) (s : List (Finset α)),
    (∀ g ∈ gates, g.op = GateOp.or) → w = s.map (fun X => decide (i ∈ X)) →
    gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w =
      (sfold s (gates.map Gate.inputs)).map (fun X => decide (i ∈ X)) := by
  intro gates
  induction gates with
  | nil => intro w s _ hw; simpa [sfold] using hw
  | cons g gs ih =>
    intro w s hor hw
    simp only [List.foldl_cons, List.map_cons]
    have hg : g.op = GateOp.or := hor g (by simp)
    have : sfold s (g.inputs :: gs.map Gate.inputs) = sfold (s ++ [gsupp s g.inputs]) (gs.map Gate.inputs) := rfl
    rw [this]
    apply ih _ _ (fun g' hg' => hor g' (by simp [hg']))
    rw [hw, hg, List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.cons.injEq, and_true]
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff, mem_gsupp]
    simp only [List.mem_map, id_eq]
    constructor
    · rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      refine ⟨j, hj, ?_⟩
      by_cases hl : j < s.length
      · rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map] at hb
        rw [List.getD_eq_getElem _ _ hl]; simpa using hb
      · rw [List.getD_eq_default _ _ (by simpa using hl)] at hb; simp at hb
    · rintro ⟨j, hj, hjs⟩
      refine ⟨_, ⟨j, hj, rfl⟩, ?_⟩
      by_cases hl : j < s.length
      · rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map]
        rw [List.getD_eq_getElem _ _ hl] at hjs; simpa using hjs
      · rw [List.getD_eq_default _ _ (by omega)] at hjs; simp at hjs

open PEqualNP.CircuitLowerBounds in

theorem supp_eq {r : ℕ} (C : Circuit) (hor : ∀ g ∈ C.gates, g.op = GateOp.or) (w : ℕ) :
    Finset.univ.filter (fun i : Fin (2 * r) =>
      (C.wires (List.ofFn (fun h : Fin (2 * r) => decide (h = i)))).getD w false = true) =
    (sfold (List.ofFn (fun h : Fin (2 * r) => ({h} : Finset (Fin (2 * r))))) (C.gates.map Gate.inputs)).getD w ∅ := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hw : C.wires (List.ofFn (fun h : Fin (2 * r) => decide (h = i))) =
      (sfold (List.ofFn (fun h : Fin (2 * r) => ({h} : Finset (Fin (2 * r))))) (C.gates.map Gate.inputs)).map
        (fun X => decide (i ∈ X)) := by
    unfold Circuit.wires
    apply foldl_wires i C.gates _ _ hor
    rw [List.map_ofFn]; congr 1; funext h; simp [eq_comm]
  rw [hw]
  set l := sfold (List.ofFn (fun h : Fin (2 * r) => ({h} : Finset (Fin (2 * r))))) (C.gates.map Gate.inputs)
  by_cases hl : w < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getD_eq_getElem _ _ hl]; simp
  · rw [List.getD_eq_default _ _ (by simpa using hl), List.getD_eq_default _ _ (by omega)]; simp

def nm (r : ℕ) (x : Fin (2 ^ r)) : Finset (Fin (2 * r)) :=
  Finset.univ.filter (fun i : Fin (2 * r) => Nat.testBit x.val (i.val / 2) = decide (i.val % 2 = 1))

theorem count_bound (r : ℕ) (X : Finset (Fin (2 * r))) :
    (Finset.univ.filter (fun x : Fin (2 ^ r) => X ⊆ nm r x)).card * 2 ^ X.card ≤ 2 ^ r := by
  set N := Finset.univ.filter (fun x : Fin (2 ^ r) => X ⊆ nm r x) with hN
  by_cases h0 : N = ∅
  · rw [h0]; simp
  obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.2 h0
  have hx0' : X ⊆ nm r x0 := (Finset.mem_filter.1 hx0).2
  have bitOf : ∀ (x : Fin (2 ^ r)) (i : Fin (2 * r)), i ∈ nm r x →
      Nat.testBit x.val (i.val / 2) = decide (i.val % 2 = 1) := by
    intro x i hi; simpa [nm] using hi
  set P := X.image (fun i : Fin (2 * r) => i.val / 2) with hP
  have hinj : Set.InjOn (fun i : Fin (2 * r) => i.val / 2) X := by
    intro i hi j hj hij
    simp only at hij
    have h1 := bitOf x0 i (hx0' hi)
    have h2 := bitOf x0 j (hx0' hj)
    rw [hij] at h1
    have hm : i.val % 2 = j.val % 2 := by
      rw [h1] at h2
      have := Nat.mod_lt i.val (by norm_num : 0 < 2)
      have := Nat.mod_lt j.val (by norm_num : 0 < 2)
      by_cases hi1 : i.val % 2 = 1 <;> by_cases hj1 : j.val % 2 = 1 <;> simp_all <;> omega
    apply Fin.ext
    have := Nat.div_add_mod i.val 2
    have := Nat.div_add_mod j.val 2
    omega
  have hPcard : P.card = X.card := Finset.card_image_of_injOn hinj
  have hPsub : P ⊆ Finset.range r := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_range]; have := i.isLt; omega
  have hXr : X.card ≤ r := by
    rw [← hPcard]; simpa using Finset.card_le_card hPsub
  set Q := Finset.range r \ P with hQ
  have hQcard : Q.card = r - X.card := by
    have h := Finset.card_sdiff_add_card_eq_card hPsub
    rw [Finset.card_range, hPcard] at h
    change Q.card + X.card = r at h
    omega
  have hle : N.card ≤ 2 ^ (r - X.card) := by
    rw [← hQcard, ← Finset.card_powerset]
    apply Finset.card_le_card_of_injOn (fun x : Fin (2 ^ r) => Q.filter (fun j => Nat.testBit x.val j = true))
    · intro x _; simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
      exact Finset.filter_subset _ _
    · intro x hx x' hx' hxx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, hN] at hx hx'
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hjr : j < r
      · by_cases hjP : j ∈ P
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hjP
          rw [bitOf x i (hx hi), bitOf x' i (hx' hi)]
        · have hjQ : j ∈ Q := Finset.mem_sdiff.2 ⟨Finset.mem_range.2 hjr, hjP⟩
          have := congrArg (fun F : Finset ℕ => j ∈ F) hxx
          simp only [Finset.mem_filter, hjQ, true_and] at this
          rw [Bool.eq_iff_iff]; simpa using this
      · have h1 : x.val < 2 ^ j := lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
        have h2 : x'.val < 2 ^ j := lt_of_lt_of_le x'.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  calc N.card * 2 ^ X.card ≤ 2 ^ (r - X.card) * 2 ^ X.card := Nat.mul_le_mul_right _ hle
    _ = 2 ^ r := by rw [← pow_add]; congr 1; omega

theorem sum_wt_le (r : ℕ) (X : Finset (Fin (2 * r))) :
    ∑ x : Fin (2 ^ r), wt (nm r x) X ≤ 2 ^ r * (if X.Nonempty then 1 else 0) := by
  by_cases hX : X.Nonempty
  · rw [if_pos hX, mul_one]
    have : ∀ x : Fin (2 ^ r), wt (nm r x) X = if X ⊆ nm r x then 2 ^ X.card else 0 := by
      intro x; simp [wt, hX]
    simp only [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    exact count_bound r X
  · rw [if_neg hX, mul_zero, Nat.le_zero, Finset.sum_eq_zero_iff]
    intro x _; simp [wt, hX]

theorem sum_cost_le (r : ℕ) (L : List (Finset (Fin (2 * r)))) :
    ∑ x : Fin (2 ^ r), cost (nm r x) L ≤ 2 ^ r * L.countP (fun X => X.Nonempty) := by
  induction L with
  | nil => simp [cost]
  | cons X L ih =>
    have e : ∀ x : Fin (2 ^ r), cost (nm r x) (X :: L) = wt (nm r x) X + cost (nm r x) L := by
      intro x; simp [cost]
    simp only [e, Finset.sum_add_distrib, List.countP_cons]
    have := sum_wt_le r X
    by_cases hX : X.Nonempty
    · simp only [hX, decide_true, if_true, mul_one] at this ⊢
      rw [mul_add, mul_one]; linarith
    · simp only [hX, decide_false, Bool.false_eq_true, if_false, mul_zero, add_zero] at this ⊢
      linarith

theorem gsupp_append_of_lt (s t : List (Finset α)) (ins : List ℕ) (h : ∀ j ∈ ins, j < s.length) :
    gsupp (s ++ t) ins = gsupp s ins := by
  ext e
  simp only [mem_gsupp]
  constructor
  · rintro ⟨j, hj, he⟩
    refine ⟨j, hj, ?_⟩
    have hl := h j hj
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hl] at he
    rw [List.getD_eq_getElem _ _ hl]; exact he
  · rintro ⟨j, hj, he⟩
    refine ⟨j, hj, ?_⟩
    have hl := h j hj
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hl]
    rw [List.getD_eq_getElem _ _ hl] at he; exact he

theorem sfold_of_base (s : List (Finset α)) (gs : List (List ℕ)) (h : ∀ ins ∈ gs, ∀ j ∈ ins, j < s.length) :
    sfold s gs = s ++ gs.map (gsupp s) := by
  induction gs using List.reverseRecOn with
  | nil => simp [sfold]
  | append_singleton gs ins ih =>
    rw [sfold_snoc, ih (fun i hi => h i (by simp [hi])), gsupp_append_of_lt _ _ _ (h ins (by simp))]
    simp

def lits (r : ℕ) (P Q : Finset ℕ) : Finset (Fin (2 * r)) :=
  Finset.univ.filter (fun i : Fin (2 * r) => i.val / 2 ∈ P ∧ (i.val % 2 = 1 ↔ i.val / 2 ∈ Q))

theorem block (r : ℕ) : ∀ n c, Cost n c → ∀ (P : Finset ℕ), P.card = n → P ⊆ Finset.range r →
    ∀ (s : List (Finset (Fin (2 * r)))), (∀ i : Fin (2 * r), {i} ∈ s) →
    ∃ gs : List (List ℕ), gs.length ≤ c ∧ (∀ ins ∈ gs, ins.length ≤ 2) ∧
      ∀ Q ⊆ P, lits r P Q ∈ sfold s gs := by
  intro n c hc
  induction hc with
  | one =>
    intro P hP hPr s hs1
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hP
    refine ⟨[], by simp, by simp, ?_⟩
    intro Q _
    have hj : j < r := Finset.mem_range.1 (hPr (Finset.mem_singleton_self j))
    have hlt : 2 * j + (if j ∈ Q then 1 else 0) < 2 * r := by split_ifs <;> omega
    have : lits r {j} Q = {⟨2 * j + (if j ∈ Q then 1 else 0), hlt⟩} := by
      ext i
      simp only [lits, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
      have hd := Nat.div_add_mod i.val 2
      have hm := Nat.mod_lt i.val (by norm_num : 0 < 2)
      constructor
      · rintro ⟨h1, h2⟩
        rw [h1] at h2
        by_cases hq : j ∈ Q
        · rw [if_pos hq]; have : i.val % 2 = 1 := h2.2 hq; omega
        · rw [if_neg hq]; have : i.val % 2 ≠ 1 := fun h => hq (h2.1 h); omega
      · intro h
        by_cases hq : j ∈ Q
        · rw [if_pos hq] at h
          have hj2 : i.val / 2 = j := by omega
          refine ⟨hj2, ?_⟩; rw [hj2]
          exact ⟨fun _ => hq, fun _ => by omega⟩
        · rw [if_neg hq] at h
          have hj2 : i.val / 2 = j := by omega
          refine ⟨hj2, ?_⟩; rw [hj2]
          exact ⟨fun hh => by omega, fun hh => absurd hh hq⟩
    rw [this]; simpa [sfold] using hs1 _
  | @split a b ca cb ha hb iha ihb =>
    intro P hP hPr s hs1
    obtain ⟨P1, hP1sub, hP1card⟩ := Finset.exists_subset_card_eq (show a ≤ P.card by omega)
    set P2 := P \ P1 with hP2
    have hP2card : P2.card = b := by
      have := Finset.card_sdiff_add_card_eq_card hP1sub
      change P2.card + P1.card = P.card at this; omega
    obtain ⟨gs1, hl1, hf1, hm1⟩ := iha P1 hP1card (hP1sub.trans hPr) s hs1
    set s1 := sfold s gs1 with hs1d
    have hs1' : ∀ i : Fin (2 * r), {i} ∈ s1 := fun i => (prefix_sfold s gs1).subset (hs1 i)
    obtain ⟨gs2, hl2, hf2, hm2⟩ := ihb P2 hP2card (Finset.sdiff_subset.trans hPr) s1 hs1'
    set s2 := sfold s1 gs2 with hs2d
    have hm1' : ∀ Q1 ⊆ P1, lits r P1 Q1 ∈ s2 := fun Q1 h => (prefix_sfold s1 gs2).subset (hm1 Q1 h)
    set gate := fun Q : Finset ℕ => [s2.idxOf (lits r P1 (Q ∩ P1)), s2.idxOf (lits r P2 (Q ∩ P2))] with hgate
    set gs3 := P.powerset.toList.map gate with hgs3
    have hidx : ∀ Q ∈ P.powerset.toList, ∀ j ∈ gate Q, j < s2.length := by
      intro Q hQ j hj
      have hQP : Q ⊆ P := Finset.mem_powerset.1 (Finset.mem_toList.1 hQ)
      simp only [hgate, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact List.idxOf_lt_length_of_mem (hm1' _ Finset.inter_subset_right)
      · exact List.idxOf_lt_length_of_mem (hm2 _ Finset.inter_subset_right)
    have hsupp : ∀ Q ⊆ P, gsupp s2 (gate Q) = lits r P Q := by
      intro Q hQP
      have e1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hm1' (Q ∩ P1) Finset.inter_subset_right))
      have e2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hm2 (Q ∩ P2) Finset.inter_subset_right))
      simp only [gsupp, hgate, List.foldr_cons, List.foldr_nil, Finset.union_empty]
      rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem (hm1' (Q ∩ P1) Finset.inter_subset_right)), e1,
        List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem (hm2 (Q ∩ P2) Finset.inter_subset_right)), e2]
      ext i
      simp only [lits, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, hP2,
        Finset.mem_sdiff]
      by_cases h1 : i.val / 2 ∈ P1
      · have := hP1sub h1; tauto
      · tauto
    refine ⟨gs1 ++ gs2 ++ gs3, ?_, ?_, ?_⟩
    · simp only [List.length_append, hgs3, List.length_map, Finset.length_toList, Finset.card_powerset, hP]
      omega
    · intro ins hins
      simp only [List.mem_append] at hins
      rcases hins with (h | h) | h
      · exact hf1 ins h
      · exact hf2 ins h
      · obtain ⟨Q, -, rfl⟩ := List.mem_map.1 h; simp [hgate]
    · intro Q hQP
      rw [sfold_append, sfold_append, ← hs1d, ← hs2d, sfold_of_base s2 gs3 ?_]
      · apply List.mem_append_right
        refine List.mem_map.2 ⟨gate Q, List.mem_map.2 ⟨Q, Finset.mem_toList.2 (Finset.mem_powerset.2 hQP), rfl⟩, ?_⟩
        exact hsupp Q hQP
      · intro ins hins
        obtain ⟨Q', hQ', rfl⟩ := List.mem_map.1 hins
        exact hidx Q' hQ'

theorem nm_card (r : ℕ) (x : Fin (2 ^ r)) : (nm r x).card = r := by
  have hlt : ∀ j : Fin r, 2 * j.val + (if Nat.testBit x.val j.val then 1 else 0) < 2 * r := by
    intro j; have := j.isLt; split_ifs <;> omega
  let f : Fin r → Fin (2 * r) := fun j => ⟨2 * j.val + (if Nat.testBit x.val j.val then 1 else 0), hlt j⟩
  have hf : Function.Injective f := by
    intro j j' h
    simp only [f, Fin.mk.injEq] at h
    apply Fin.ext
    split_ifs at h <;> omega
  have : nm r x = Finset.univ.image f := by
    ext i
    simp only [nm, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    have hd := Nat.div_add_mod i.val 2
    have hm := Nat.mod_lt i.val (by norm_num : 0 < 2)
    constructor
    · intro h
      refine ⟨⟨i.val / 2, by have := i.isLt; omega⟩, ?_⟩
      apply Fin.ext; simp only [f]
      rw [h]
      by_cases h1 : i.val % 2 = 1 <;> simp [h1] <;> omega
    · rintro ⟨j, rfl⟩
      simp only [f]
      have e1 : (2 * j.val + (if Nat.testBit x.val j.val then 1 else 0)) / 2 = j.val := by split_ifs <;> omega
      have e2 : (2 * j.val + (if Nat.testBit x.val j.val then 1 else 0)) % 2 =
          (if Nat.testBit x.val j.val then 1 else 0) := by split_ifs <;> omega
      rw [e1, e2]
      cases Nat.testBit x.val j.val <;> simp
  rw [this, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

theorem nm_eq_lits (r : ℕ) (x : Fin (2 ^ r)) :
    nm r x = lits r (Finset.range r) ((Finset.range r).filter (fun j => Nat.testBit x.val j = true)) := by
  ext i
  have hi : i.val / 2 < r := by have := i.isLt; omega
  simp only [nm, lits, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range, hi]
  cases h : Nat.testBit x.val (i.val / 2) <;> by_cases h1 : i.val % 2 = 1 <;> simp [h1]

theorem countP_eq_sum' {β : Type} (p : β → Prop) [DecidablePred p] (L : List β) :
    L.countP (fun b => p b) = (L.map (fun b => if p b then 1 else 0)).sum := by
  induction L with
  | nil => simp
  | cons b L ih => simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]; split_ifs <;> simp_all <;> omega

theorem card_filter_getD {β : Type} (p : β → Prop) [DecidablePred p] (L : List β) (d : β) (n : ℕ)
    (hn : L.length = n) : (Finset.univ.filter (fun g : Fin n => p (L.getD g.val d))).card = L.countP (fun b => p b) := by
  subst hn
  rw [Finset.card_filter, countP_eq_sum']
  rw [← Fin.sum_univ_fun_getElem L (fun b => if p b then 1 else 0)]
  apply Finset.sum_congr rfl
  intro g _
  rw [List.getD_eq_getElem _ _ g.isLt]

theorem getD_gl (s : List (Finset α)) (gs : List (List ℕ)) (g : ℕ) :
    (sfold s gs).getD (s.length + g) ∅ = (gl s gs).getD g ∅ := by
  unfold gl
  by_cases h : s.length + g < (sfold s gs).length
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_drop]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_lib_686_aux

open PEqualNP.Outside.L_lib_686_aux in
theorem PEqualNP.Outside.L_lib_686 : (∀ r : ℕ, 2 ≤ r →
  let S := Fin (2 * r)
  let names := fun (x : Fin (2 ^ r)) =>
    Finset.univ.filter (fun i : S => Nat.testBit x.val (i.val / 2) = decide (i.val % 2 = 1))
  let supp := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ) =>
    Finset.univ.filter (fun i : S =>
      (D.wires (List.ofFn (fun h : S => decide (h = i)))).getD w false = true)
  let realizes := fun (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧
    ∀ x : Fin (2 ^ r), ∃ w : ℕ, supp D w = names x
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, realizes C →
    (∀ D : PEqualNP.CircuitLowerBounds.Circuit, realizes D → C.size ≤ D.size) →
    ∀ x : Fin (2 ^ r),
      let support := fun (g : Fin C.size) => supp C (2 * r + g.val)
      let I := Finset.univ.filter (fun g : Fin C.size => support g ⊆ names x)
      I.card + 1 = r ∧ ∀ p ∈ I, ∀ q ∈ I,
        Disjoint (support p) (support q) ∨ support p ⊆ support q ∨ support q ⊆ support p) := by
  intro r hr
  dsimp only
  intro C hC hmin x0
  obtain ⟨hgate, hreal⟩ := hC
  have hor : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => (hgate g hg).1
  have hnm : ∀ x : Fin (2 ^ r), Finset.univ.filter (fun i : Fin (2 * r) =>
      Nat.testBit x.val (i.val / 2) = decide (i.val % 2 = 1)) = nm r x := fun x => rfl
  simp only [supp_eq C hor, hnm] at hreal ⊢
  set init : List (Finset (Fin (2 * r))) := List.ofFn (fun h : Fin (2 * r) => ({h} : Finset (Fin (2 * r)))) with hinit
  set gsC := C.gates.map PEqualNP.CircuitLowerBounds.Gate.inputs with hgsC
  set L := gl init gsC with hL
  have hinit1 : ∀ X ∈ init, X.card ≤ 1 := by
    intro X hX; rw [hinit, List.mem_ofFn] at hX; obtain ⟨h, rfl⟩ := hX; simp
  have hsing : ∀ i : Fin (2 * r), {i} ∈ init := by
    intro i; rw [hinit, List.mem_ofFn]; exact ⟨i, rfl⟩
  have hinitlen : init.length = 2 * r := by simp [hinit]
  have hfan : ∀ ins ∈ gsC, ins.length ≤ 2 := by
    intro ins hins; obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hins; exact (hgate g hg).2
  have hLlen : L.length = C.size := by simp [hL, length_gl, hgsC, PEqualNP.CircuitLowerBounds.Circuit.size]
  have hr0 : 0 < r := by omega

  have hmemx : ∀ x : Fin (2 ^ r), nm r x ∈ sfold init gsC := by
    intro x
    obtain ⟨w, hw⟩ := hreal x
    rw [← hw]; apply getD_mem_of_nonempty; rw [hw]
    exact Finset.card_pos.1 (by rw [nm_card]; omega)

  have hsize : ∀ c, Cost r c → C.size ≤ c := by
    intro c hc
    obtain ⟨gs, hlen, hgs2, hm⟩ := block r r c hc (Finset.range r) (Finset.card_range r) le_rfl init hsing
    let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨gs.map (fun ins => ⟨PEqualNP.CircuitLowerBounds.GateOp.or, ins⟩), 0⟩
    have hDor : ∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro g hg; obtain ⟨ins, -, rfl⟩ := List.mem_map.1 hg; rfl
    have hDg : D.gates.map PEqualNP.CircuitLowerBounds.Gate.inputs = gs := by
      simp [D, List.map_map, Function.comp_def]
    have hD := hmin D ⟨fun g hg => ⟨hDor g hg, by obtain ⟨ins, hins, rfl⟩ := List.mem_map.1 hg; exact hgs2 ins hins⟩,
      fun x => by
        refine ⟨(sfold init gs).idxOf (nm r x), ?_⟩
        rw [supp_eq D hDor, hnm, hDg]
        have hx : nm r x ∈ sfold init gs := by
          rw [nm_eq_lits]; exact hm _ (Finset.filter_subset _ _)
        rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hx), List.getElem_idxOf]⟩
    have : D.size = gs.length := by simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
    omega

  have hlb : ∀ x : Fin (2 ^ r), C.size ≤ cost (nm r x) L := by
    intro x
    obtain ⟨c, hc, hcle, -⟩ := core r init gsC (nm r x) hinit1 hfan (nm_card r x) hr0 (hmemx x)
    exact (hsize c hc).trans hcle
  have hsum := sum_cost_le r L
  have hcp : L.countP (fun X => X.Nonempty) ≤ C.size := hLlen ▸ List.countP_le_length
  have hconst : ∑ _x : Fin (2 ^ r), C.size = 2 ^ r * C.size := by simp
  have hge : 2 ^ r * C.size ≤ ∑ x : Fin (2 ^ r), cost (nm r x) L :=
    hconst ▸ Finset.sum_le_sum (fun x _ => hlb x)
  have hpow : 0 < 2 ^ r := by positivity
  have hcp' : L.countP (fun X => X.Nonempty) = L.length := by
    have : 2 ^ r * C.size ≤ 2 ^ r * L.countP (fun X => X.Nonempty) := hge.trans hsum
    have := Nat.le_of_mul_le_mul_left this hpow
    omega
  have hne : ∀ X ∈ L, X.Nonempty := by
    have := List.countP_eq_length.1 hcp'; simpa using this
  have hall : ∀ x : Fin (2 ^ r), cost (nm r x) L = C.size := by
    have heq : ∑ _x : Fin (2 ^ r), C.size = ∑ x : Fin (2 ^ r), cost (nm r x) L := by
      have : ∑ x : Fin (2 ^ r), cost (nm r x) L ≤ 2 ^ r * C.size := by
        calc _ ≤ 2 ^ r * L.countP (fun X => X.Nonempty) := hsum
          _ ≤ 2 ^ r * C.size := Nat.mul_le_mul_left _ hcp
      omega
    intro x
    exact ((Finset.sum_eq_sum_iff_of_le (fun x _ => hlb x)).1 heq x (Finset.mem_univ x)).symm
  obtain ⟨c, hc, -, htight⟩ := core r init gsC (nm r x0) hinit1 hfan (nm_card r x0) hr0 (hmemx x0)
  obtain ⟨hcnt, hlam⟩ := htight (fun c' hc' => (hall x0).trans_le (hsize c' hc'))
  rw [← hL] at hcnt hlam
  have hsg : ∀ g : Fin C.size, (sfold init gsC).getD (2 * r + g.val) ∅ = L.getD g.val ∅ := by
    intro g; have := getD_gl init gsC g.val; rw [hinitlen] at this; exact this
  simp only [hsg]
  refine ⟨?_, ?_⟩
  · rw [card_filter_getD (fun X => X ⊆ nm r x0) L ∅ C.size hLlen]
    have : L.countP (fun X => decide (X ⊆ nm r x0)) = cnt (nm r x0) L := by
      unfold cnt; apply List.countP_congr; intro X hX; simp [hne X hX]
    rw [this, hcnt]
  · intro p hp q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have hpl : p.val < L.length := by rw [hLlen]; exact p.isLt
    have hql : q.val < L.length := by rw [hLlen]; exact q.isLt
    rw [List.getD_eq_getElem _ _ hpl] at hp ⊢
    rw [List.getD_eq_getElem _ _ hql] at hq ⊢
    apply hlam
    · exact mem_fam.2 ⟨List.getElem_mem hpl, hne _ (List.getElem_mem hpl), hp⟩
    · exact mem_fam.2 ⟨List.getElem_mem hql, hne _ (List.getElem_mem hql), hq⟩
