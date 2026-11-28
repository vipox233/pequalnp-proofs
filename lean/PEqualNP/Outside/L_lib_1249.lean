import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_1249_aux

private def need {n m : ℕ} (a c : Fin m → Finset (Fin n)) (js : List (Fin m)) : Finset (Fin n) :=
  js.foldr (fun j acc => a j ∪ c j ∪ acc) ∅

private lemma subset_need_of_mem {n m : ℕ} (a c : Fin m → Finset (Fin n))
    {js : List (Fin m)} {i : Fin m} (hi : i ∈ js) :
    a i ∪ c i ⊆ need a c js := by
  induction js with
  | nil => cases hi
  | cons j rest ih =>
    simp only [need, List.foldr_cons]
    rcases List.mem_cons.mp hi with rfl | hmem
    · exact Finset.subset_union_left
    · exact (ih hmem).trans Finset.subset_union_right

private lemma need_subset_iff {n m : ℕ} (a c : Fin m → Finset (Fin n))
    (js : List (Fin m)) (y : Finset (Fin n)) :
    need a c js ⊆ y ↔ ∀ i ∈ js, a i ∪ c i ⊆ y := by
  induction js with
  | nil => simp [need]
  | cons j rest ih =>
    change (a j ∪ c j) ∪ need a c rest ⊆ y ↔ _
    rw [Finset.union_subset_iff, ih]
    simp

private lemma namedRec_iff {n m : ℕ} (a b c d : Fin m → Finset (Fin n)) :
    let valid := fun i => a i ⊆ b i ∧ a i ⊆ d i ∧ c i ⊆ d i
    let conf := fun i j => valid i ∧ valid j ∧ ¬ (a i ∪ c i) ⊆ (b j ∩ d j)
    ∀ (js : List (Fin m)) (y : Finset (Fin n)),
      List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
        (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
          a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js y ↔
      ((∀ j ∈ js, valid j) ∧ js.Pairwise (fun j i => ¬ conf i j) ∧ need a c js ⊆ y) := by
  intro valid conf js
  induction js with
  | nil =>
    intro y
    simp [need]
  | cons j rest ih =>
    intro y
    dsimp only
    constructor
    · rintro ⟨u, v, hprev, huv, hvy, hau, hub, hcv, hvd⟩
      rcases (ih u).mp hprev with ⟨hval_r, hpw_r, hneed_r⟩
      have hvj : valid j := ⟨hau.trans hub, (hau.trans huv).trans hvd, hcv.trans hvd⟩
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact hvj
        · exact hval_r x hmem
      · rw [List.pairwise_cons]
        refine ⟨fun i hi hconf => ?_, hpw_r⟩
        have hsub_u : a i ∪ c i ⊆ u := (subset_need_of_mem a c hi).trans hneed_r
        have hsub_bd : a i ∪ c i ⊆ b j ∩ d j :=
          Finset.subset_inter (hsub_u.trans hub) ((hsub_u.trans huv).trans hvd)
        exact hconf.2.2 hsub_bd
      · rw [need_subset_iff]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact Finset.union_subset ((hau.trans huv).trans hvy) (hcv.trans hvy)
        · exact (((subset_need_of_mem a c hmem).trans hneed_r).trans huv).trans hvy
    · rintro ⟨hval, hpw, hneed⟩
      have hvj : valid j := hval j (List.mem_cons_self ..)
      have hval_r : ∀ i ∈ rest, valid i := fun i hi => hval i (List.mem_cons_of_mem j hi)
      rw [List.pairwise_cons] at hpw
      let u := need a c rest ∪ a j
      let v := u ∪ c j
      have hneed_bd : need a c rest ⊆ b j ∩ d j := by
        rw [need_subset_iff]
        intro i hi
        have hnc := hpw.1 i hi
        by_contra hnot
        exact hnc ⟨hval_r i hi, hvj, hnot⟩
      have hprev : List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
          (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
            a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) rest u :=
        (ih u).mpr ⟨hval_r, hpw.2, Finset.subset_union_left⟩
      refine ⟨u, v, hprev, Finset.subset_union_left, ?_, Finset.subset_union_right, ?_,
        Finset.subset_union_right, ?_⟩
      · have hnr : need a c rest ⊆ y := by
          rw [need_subset_iff] at hneed ⊢
          exact fun i hi => hneed i (List.mem_cons_of_mem j hi)
        have hnj : a j ∪ c j ⊆ y := (need_subset_iff a c (j :: rest) y).mp hneed j (List.mem_cons_self ..)
        exact Finset.union_subset (Finset.union_subset hnr (Finset.subset_union_left.trans hnj))
          (Finset.subset_union_right.trans hnj)
      · exact Finset.union_subset (hneed_bd.trans Finset.inter_subset_left) hvj.1
      · exact Finset.union_subset
          (Finset.union_subset (hneed_bd.trans Finset.inter_subset_right) hvj.2.1) hvj.2.2

private lemma list_filter_eq_append {α : Type*} (p : α → Bool) :
    ∀ (js L1 L2 : List α), js.filter p = L1 ++ L2 →
      ∃ js1 js2, js = js1 ++ js2 ∧ js1.filter p = L1 ∧ js2.filter p = L2 := by
  intro js
  induction js with
  | nil =>
    intro L1 L2 h
    simp only [List.filter_nil] at h
    have h1 : L1 = [] := by cases L1 <;> simp at h ⊢
    have h2 : L2 = [] := by subst h1; simpa using h.symm
    exact ⟨[], [], rfl, by simp [h1], by simp [h2]⟩
  | cons x xs ih =>
    intro L1 L2 h
    cases hpx : p x
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte] at h
      rcases ih L1 L2 h with ⟨js1, js2, rfl, h1, h2⟩
      exact ⟨x :: js1, js2, rfl, by simp [hpx, h1], h2⟩
    · simp only [List.filter_cons, hpx, ↓reduceIte] at h
      cases L1 with
      | nil =>
        simp only [List.nil_append] at h
        exact ⟨[], x :: xs, rfl, rfl, by simp [hpx, h]⟩
      | cons y ys =>
        simp only [List.cons_append, List.cons.injEq] at h
        rcases h with ⟨rfl, htail⟩
        rcases ih ys L2 htail with ⟨js1, js2, rfl, h1, h2⟩
        exact ⟨x :: js1, js2, rfl, by simp [hpx, h1], h2⟩

private lemma card_nodup_lists_in_finset {α : Type*} [DecidableEq α] (F : Finset α) :
    ∃ (W : ℕ), W = (Finset.range (F.card + 1)).sum (fun t => F.card.descFactorial t) ∧
    ∃ (enc : {L : List α // L.Nodup ∧ ∀ x ∈ L, x ∈ F} ↪ Fin W), True := by
  let S := {L : List α // L.Nodup ∧ ∀ x ∈ L, x ∈ F}
  let T := Σ t : Fin (F.card + 1), (Fin t.val ↪ ↥F)
  have hcardT : Fintype.card T = (Finset.range (F.card + 1)).sum (fun t => F.card.descFactorial t) := by
    rw [Fintype.card_sigma, ← Fin.sum_univ_eq_sum_range]
    congr 1; ext t
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
  let toT : S → T := fun ⟨L, hnd, hmem⟩ =>
    have hlen : L.length < F.card + 1 := by
      have hsub : L.toFinset ⊆ F := fun x hx => hmem x (List.mem_toFinset.mp hx)
      have hle : L.length ≤ F.card := by
        rw [← List.toFinset_card_of_nodup hnd]
        exact Finset.card_le_card hsub
      omega
    let f : Fin L.length ↪ ↥F :=
      ⟨fun i => ⟨L.get i, hmem _ (List.get_mem L i)⟩, fun i j h => by
        have h1 : L.get i = L.get j := congrArg Subtype.val h
        exact (List.nodup_iff_injective_get.mp hnd) h1⟩
    ⟨⟨L.length, hlen⟩, f⟩
  have htoT_inj : Function.Injective toT := by
    intro ⟨L1, hnd1, hmem1⟩ ⟨L2, hnd2, hmem2⟩ h
    apply Subtype.ext
    have h1 := congrArg (fun x : T => List.ofFn (fun k : Fin x.1.val => (x.2 k).1)) h
    simpa [toT, List.ofFn_get] using h1
  let eFin : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let enc : S ↪ Fin ((Finset.range (F.card + 1)).sum (fun t => F.card.descFactorial t)) :=
    ⟨fun s => (finCongr hcardT) (eFin (toT s)),
      (finCongr hcardT).injective.comp (eFin.injective.comp htoT_inj)⟩
  exact ⟨_, rfl, enc, trivial⟩

private lemma descFactorial_mono {a b : ℕ} (hab : a ≤ b) :
    ∀ t : ℕ, a.descFactorial t ≤ b.descFactorial t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [Nat.descFactorial_succ]
    exact Nat.mul_le_mul (by omega) ih

private lemma sum_descFactorial_mono {a b : ℕ} (hab : a ≤ b) :
    (Finset.range (a + 1)).sum (fun t => a.descFactorial t) ≤
    (Finset.range (b + 1)).sum (fun t => b.descFactorial t) := by
  calc (Finset.range (a + 1)).sum (fun t => a.descFactorial t)
      ≤ (Finset.range (a + 1)).sum (fun t => b.descFactorial t) :=
        Finset.sum_le_sum (fun t _ => descFactorial_mono hab t)
    _ ≤ (Finset.range (b + 1)).sum (fun t => b.descFactorial t) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))

private lemma descFactorial_sum_pos (w : ℕ) :
    0 < (Finset.range (w + 1)).sum (fun t => w.descFactorial t) := by
  have hmem : 0 ∈ Finset.range (w + 1) := Finset.mem_range.mpr (Nat.succ_pos w)
  have hle : w.descFactorial 0 ≤ (Finset.range (w + 1)).sum (fun t => w.descFactorial t) :=
    Finset.single_le_sum (f := fun t => w.descFactorial t) (fun _ _ => Nat.zero_le _) hmem
  simp only [Nat.descFactorial_zero] at hle
  omega

private def insertAt {α : Type*} (x : α) (L : List α) (p : ℕ) : List α :=
  L.take p ++ [x] ++ L.drop p

open scoped Classical in
private lemma main_proof (n m w : ℕ) (a b c d : Fin m → Finset (Fin n)) :
    let named := fun (js : List (Fin m)) =>
      List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
        (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
          a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js Finset.univ
    let feasible := fun (S : Finset (Fin m)) =>
      ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ named js
    let recognizes := fun (W : Nat) (start : Fin W) (finals : Finset (Fin W))
        (edge : Fin m → Fin W → Bool → Fin W → Prop) =>
      ∀ S : Finset (Fin m), feasible S ↔
        ∃ st : Fin (m+1) → Fin W, st 0 = start ∧ st (Fin.last m) ∈ finals ∧
          ∀ i : Fin m, edge i (st i.castSucc) (decide (i ∈ S)) (st i.succ)
    let cost := fun (W : Nat) (edge : Fin m → Fin W → Bool → Fin W → Prop) =>
      (Finset.univ : Finset (Fin m × Fin W × Bool × Fin W)).filter
        (fun v => edge v.1 v.2.1 v.2.2.1 v.2.2.2)
    let valid := fun i => a i ⊆ b i ∧ a i ⊆ d i ∧ c i ⊆ d i
    let conf := fun i j => valid i ∧ valid j ∧ ¬ (a i ∪ c i) ⊆ (b j ∩ d j)
    let live := fun (k : Nat) => (Finset.univ : Finset (Fin m)).filter
      (fun i => i.val < k ∧ ∃ j : Fin m, k ≤ j.val ∧ (conf i j ∨ conf j i))
    (∀ k, (live k).card ≤ w) →
    let W := (Finset.range (w+1)).sum (fun t => w.descFactorial t)
    ∃ (start : Fin W) (finals : Finset (Fin W)) (edge : Fin m → Fin W → Bool → Fin W → Prop),
      recognizes W start finals edge ∧ (cost W edge).card ≤ m*(w+2)*W := by
  classical
  intro named feasible recognizes cost valid conf live hlive W
  have hnamed_iff : ∀ js : List (Fin m),
      named js ↔ (∀ j ∈ js, valid j) ∧ js.Pairwise (fun j i => ¬ conf i j) := by
    intro js
    have h := namedRec_iff a b c d js Finset.univ
    simp only [Finset.subset_univ, and_true] at h
    exact h
  let ok : List (Fin m) → Prop := fun js =>
    js.Nodup ∧ (∀ j ∈ js, valid j) ∧ js.Pairwise (fun j i => ¬ conf i j)
  have hfeas_iff : ∀ S : Finset (Fin m), feasible S ↔ ∃ js, ok js ∧ js.toFinset = S := by
    intro S
    constructor
    · rintro ⟨js, hnd, hfs, hnm⟩
      rcases (hnamed_iff js).mp hnm with ⟨hv, hpw⟩
      exact ⟨js, ⟨hnd, hv, hpw⟩, hfs⟩
    · rintro ⟨js, ⟨hnd, hv, hpw⟩, hfs⟩
      exact ⟨js, hnd, hfs, (hnamed_iff js).mpr ⟨hv, hpw⟩⟩
  let State : ℕ → Type := fun k => {L : List (Fin m) // L.Nodup ∧ ∀ x ∈ L, x ∈ live k}
  have hex_enc : ∀ k : ℕ, ∃ enc : State k ↪ Fin W, True := by
    intro k
    rcases card_nodup_lists_in_finset (live k) with ⟨Wk, hWk, enc0, _⟩
    have hle : Wk ≤ W := by
      rw [hWk]
      exact sum_descFactorial_mono (hlive k)
    exact ⟨enc0.trans (Fin.castLEEmb hle), trivial⟩
  let enc : ∀ k : ℕ, State k ↪ Fin W := fun k => Classical.choose (hex_enc k)
  let emptyState : ∀ k : ℕ, State k := fun _ => ⟨[], List.nodup_nil, fun _ h => by cases h⟩
  let start : Fin W := enc 0 (emptyState 0)
  let finals : Finset (Fin W) := Finset.univ
  have hlive_mono : ∀ (k : ℕ) (x : Fin m), x.val < k → x ∈ live (k + 1) → x ∈ live k := by
    intro k x hxk hx
    simp only [live, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx.2 with ⟨j, hj, hc⟩
    exact ⟨hxk, j, by omega, hc⟩
  let step : ∀ (i : Fin m), State i.val → Bool → State (i.val + 1) → Prop :=
    fun i L take L' =>
      if take = false then
        L'.1 = L.1.filter (fun x => decide (x ∈ live (i.val + 1)))
      else
        valid i ∧ ∃ p : Fin (L.1.length + 1),
          (∀ x ∈ L.1.take p.val, ¬ conf i x) ∧
          (∀ y ∈ L.1.drop p.val, ¬ conf y i) ∧
          L'.1 = (insertAt i L.1 p.val).filter (fun x => decide (x ∈ live (i.val + 1)))
  let edge : Fin m → Fin W → Bool → Fin W → Prop := fun i s take s' =>
    ∃ (L : State i.val) (L' : State (i.val + 1)),
      enc i.val L = s ∧ enc (i.val + 1) L' = s' ∧ step i L take L'
  refine ⟨start, finals, edge, ?_, ?_⟩
  · intro S
    rw [hfeas_iff S]
    constructor
    · rintro ⟨js, hok, hfs⟩
      let stL : ∀ k : Fin (m + 1), State k.val := fun k =>
        ⟨js.filter (fun x => decide (x ∈ live k.val)),
          hok.1.filter _,
          fun x hx => by
            have h := (List.mem_filter.mp hx).2
            exact of_decide_eq_true h⟩
      refine ⟨fun k => enc k.val (stL k), ?_, Finset.mem_univ _, ?_⟩
      · change enc 0 (stL 0) = enc 0 (emptyState 0)
        congr 1; apply Subtype.ext
        change js.filter (fun x => decide (x ∈ live 0)) = []
        apply List.filter_eq_nil_iff.mpr
        intro x _
        simp [live]
      · intro i
        refine ⟨stL i.castSucc, stL i.succ, rfl, rfl, ?_⟩
        dsimp only [step]
        by_cases hiS : i ∈ S
        · simp only [hiS, decide_true, Bool.true_eq_false, ↓reduceIte]
          have hi_js : i ∈ js := by rw [← List.mem_toFinset, hfs]; exact hiS
          have hvi : valid i := hok.2.1 i hi_js
          rcases List.append_of_mem hi_js with ⟨js1, js2, hjs_eq⟩
          have hi_not_live : i ∉ live i.val := by
            simp [live]
          let L1 := js1.filter (fun x => decide (x ∈ live i.val))
          let L2 := js2.filter (fun x => decide (x ∈ live i.val))
          have hL_split : (stL i.castSucc).1 = L1 ++ L2 := by
            change js.filter (fun x => decide (x ∈ live i.val)) = _
            rw [hjs_eq, List.filter_append, List.filter_cons_of_neg (by simp [hi_not_live])]
          have hp_lt : L1.length < (stL i.castSucc).1.length + 1 := by
            rw [hL_split, List.length_append]; omega
          refine ⟨hvi, ⟨L1.length, hp_lt⟩, ?_, ?_, ?_⟩
          · intro x hx
            have hx' : x ∈ (L1 ++ L2).take L1.length := by rwa [← hL_split]
            rw [List.take_left] at hx'
            have hx1 : x ∈ js1 := (List.mem_filter.mp hx').1
            have hpw := hok.2.2
            rw [hjs_eq, List.pairwise_append] at hpw
            exact hpw.2.2 x hx1 i (List.mem_cons_self ..)
          · intro y hy
            have hy' : y ∈ (L1 ++ L2).drop L1.length := by rwa [← hL_split]
            rw [List.drop_left] at hy'
            have hy2 : y ∈ js2 := (List.mem_filter.mp hy').1
            have hpw := hok.2.2
            rw [hjs_eq, List.pairwise_append] at hpw
            rw [List.pairwise_cons] at hpw
            exact hpw.2.1.1 y hy2
          · change js.filter (fun x => decide (x ∈ live (i.val + 1))) =
              (insertAt i (stL i.castSucc).1 L1.length).filter (fun x => decide (x ∈ live (i.val + 1)))
            have hins : insertAt i (stL i.castSucc).1 L1.length = L1 ++ [i] ++ L2 := by
              unfold insertAt
              rw [hL_split, List.take_left, List.drop_left]
            rw [hins, hjs_eq]
            simp only [List.filter_append]
            have hfilt_sub : ∀ l : List (Fin m), i ∉ l →
                l.filter (fun x => decide (x ∈ live (i.val + 1))) =
                (l.filter (fun x => decide (x ∈ live i.val))).filter (fun x => decide (x ∈ live (i.val + 1))) := by
              intro l hil
              rw [List.filter_filter]
              apply List.filter_congr
              intro x hx
              have hne : x ≠ i := fun h => hil (h ▸ hx)
              by_cases hx1 : x ∈ live (i.val + 1)
              · have hxlt : x.val < i.val := by
                  have hlt : x.val < i.val + 1 := (Finset.mem_filter.mp hx1).2.1
                  have hvalne : x.val ≠ i.val := fun h => hne (Fin.ext h)
                  omega
                have hx0 : x ∈ live i.val := hlive_mono i.val x hxlt hx1
                simp [hx1, hx0]
              · simp [hx1]
            have hnd := hok.1
            rw [hjs_eq, List.nodup_append] at hnd
            have hi1 : i ∉ js1 := fun h => hnd.2.2 i h i (List.mem_cons_self ..) rfl
            have hi2 : i ∉ js2 := (List.nodup_cons.mp hnd.2.1).1
            rw [← hfilt_sub js1 hi1, ← hfilt_sub js2 hi2]
            by_cases hil1 : i ∈ live (i.val + 1) <;> simp [hil1]
        · simp only [hiS, decide_false, ↓reduceIte]
          change js.filter (fun x => decide (x ∈ live (i.val + 1))) =
            (js.filter (fun x => decide (x ∈ live i.val))).filter (fun x => decide (x ∈ live (i.val + 1)))
          rw [List.filter_filter]
          apply List.filter_congr
          intro x hx
          have hne : x ≠ i := fun h => hiS (h ▸ hfs ▸ List.mem_toFinset.mpr hx)
          by_cases hx1 : x ∈ live (i.val + 1)
          · have hxlt : x.val < i.val := by
              have hlt : x.val < i.val + 1 := (Finset.mem_filter.mp hx1).2.1
              have hvalne : x.val ≠ i.val := fun h => hne (Fin.ext h)
              omega
            have hx0 : x ∈ live i.val := hlive_mono i.val x hxlt hx1
            simp [hx1, hx0]
          · simp [hx1]
    · rintro ⟨st, hst0, _, hedge⟩
      have hinv : ∀ k : ℕ, (hk : k ≤ m) →
          ∃ (L : State k) (js : List (Fin m)),
            enc k L = st ⟨k, Nat.lt_succ_of_le hk⟩ ∧
            ok js ∧
            js.toFinset = S.filter (fun i => i.val < k) ∧
            js.filter (fun x => decide (x ∈ live k)) = L.1 := by
        intro k
        induction k with
        | zero =>
          intro _
          refine ⟨emptyState 0, [], hst0.symm, ⟨List.nodup_nil, (fun _ h => by cases h), List.Pairwise.nil⟩, ?_, rfl⟩
          ext x; simp
        | succ k ih =>
          intro hk
          rcases ih (Nat.le_of_succ_le hk) with ⟨Lk, js, hLk_enc, hok_js, hjs_S, hjs_filt⟩
          let i : Fin m := ⟨k, hk⟩
          have hiv : i.val = k := rfl
          rcases hedge i with ⟨Li, Li', hLi_enc, hLi'_enc, hstep⟩
          have hLi_eq : Li = Lk := (enc k).injective (hLi_enc.trans hLk_enc.symm)
          subst hLi_eq
          dsimp only [step] at hstep
          have hfilt_sub : ∀ l : List (Fin m), (∀ x ∈ l, x.val < k) →
              l.filter (fun x => decide (x ∈ live (k + 1))) =
              (l.filter (fun x => decide (x ∈ live k))).filter (fun x => decide (x ∈ live (k + 1))) := by
            intro l hl
            rw [List.filter_filter]
            apply List.filter_congr
            intro x hx
            by_cases hx1 : x ∈ live (k + 1)
            · have hx0 : x ∈ live k := hlive_mono k x (hl x hx) hx1
              simp [hx1, hx0]
            · simp [hx1]
          have hjs_lt : ∀ x ∈ js, x.val < k := by
            intro x hx
            have hxS : x ∈ S.filter (fun j => j.val < k) := hjs_S ▸ List.mem_toFinset.mpr hx
            exact (Finset.mem_filter.mp hxS).2
          by_cases hiS : i ∈ S
          · simp only [hiS, decide_true, Bool.true_eq_false, ↓reduceIte] at hstep
            rcases hstep with ⟨hvi, p, hbefore, hafter, hL'eq⟩
            have hsplit_L : js.filter (fun x => decide (x ∈ live k)) =
                Li.1.take p.val ++ Li.1.drop p.val := by
              rw [hjs_filt, List.take_append_drop]
            rcases list_filter_eq_append _ js (Li.1.take p.val) (Li.1.drop p.val) hsplit_L with
              ⟨js1, js2, hjs_eq, hjs1_f, hjs2_f⟩
            let js' := js1 ++ [i] ++ js2
            have hi_not_js : i ∉ js := fun h => by
              have := hjs_lt i h; omega
            have hnd' : js'.Nodup := by
              have hnd := hok_js.1
              rw [hjs_eq, List.nodup_append] at hnd
              simp only [js', List.append_assoc, List.cons_append, List.nil_append, List.nodup_append,
                List.nodup_cons]
              refine ⟨hnd.1, ⟨fun h => hi_not_js (hjs_eq ▸ List.mem_append_right _ h), hnd.2.1⟩, ?_⟩
              intro x hx y hy
              rcases List.mem_cons.mp hy with rfl | hy2
              · intro h; exact hi_not_js (hjs_eq ▸ List.mem_append_left _ (h ▸ hx))
              · exact hnd.2.2 x hx y hy2
            have hval' : ∀ x ∈ js', valid x := by
              intro x hx
              simp only [js', List.mem_append, List.mem_singleton] at hx
              rcases hx with (hx1 | rfl) | hx2
              · exact hok_js.2.1 x (hjs_eq ▸ List.mem_append_left _ hx1)
              · exact hvi
              · exact hok_js.2.1 x (hjs_eq ▸ List.mem_append_right _ hx2)
            have hpw' : js'.Pairwise (fun a b => ¬ conf b a) := by
              have hpw := hok_js.2.2
              rw [hjs_eq, List.pairwise_append] at hpw
              simp only [js', List.append_assoc, List.cons_append, List.nil_append,
                List.pairwise_append, List.pairwise_cons]
              refine ⟨hpw.1, ⟨?_, hpw.2.1⟩, ?_⟩
              · intro y hy
                by_cases hyl : y ∈ live k
                · exact hafter y (hjs2_f ▸ List.mem_filter.mpr ⟨hy, decide_eq_true hyl⟩)
                · intro hcyi
                  apply hyl
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                    hjs_lt y (hjs_eq ▸ List.mem_append_right _ hy), i, le_refl k, Or.inl hcyi⟩
              · intro x hx y hy
                rcases List.mem_cons.mp hy with rfl | hy2
                · by_cases hxl : x ∈ live k
                  · exact hbefore x (hjs1_f ▸ List.mem_filter.mpr ⟨hx, decide_eq_true hxl⟩)
                  · intro hcix
                    apply hxl
                    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                      hjs_lt x (hjs_eq ▸ List.mem_append_left _ hx), i, le_refl k, Or.inr hcix⟩
                · exact hpw.2.2 x hx y hy2
            have hfs' : js'.toFinset = S.filter (fun j => j.val < k + 1) := by
              ext x
              simp only [js', List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
                Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false, Finset.mem_filter]
              have hxjs : x ∈ js1.toFinset ∨ x ∈ js2.toFinset ↔ x ∈ S ∧ x.val < k := by
                rw [← Finset.mem_union, ← List.toFinset_append, ← hjs_eq, hjs_S, Finset.mem_filter]
              constructor
              · rintro ((hx1 | rfl) | hx2)
                · have h := hxjs.mp (Or.inl hx1); exact ⟨h.1, Nat.lt_succ_of_lt h.2⟩
                · exact ⟨hiS, Nat.lt_succ_self k⟩
                · have h := hxjs.mp (Or.inr hx2); exact ⟨h.1, Nat.lt_succ_of_lt h.2⟩
              · rintro ⟨hxS, hxlt⟩
                by_cases hxk : x.val < k
                · rcases hxjs.mpr ⟨hxS, hxk⟩ with h1 | h2
                  · exact Or.inl (Or.inl h1)
                  · exact Or.inr h2
                · have hxeqi : x = i := Fin.ext (by omega)
                  exact Or.inl (Or.inr hxeqi)
            have hfilt' : js'.filter (fun x => decide (x ∈ live (k + 1))) = Li'.1 := by
              rw [hL'eq]
              simp only [js', insertAt, List.filter_append]
              rw [hfilt_sub js1 (fun x hx => hjs_lt x (hjs_eq ▸ List.mem_append_left _ hx)),
                hfilt_sub js2 (fun x hx => hjs_lt x (hjs_eq ▸ List.mem_append_right _ hx)),
                hjs1_f, hjs2_f]
            exact ⟨Li', js', hLi'_enc, ⟨hnd', hval', hpw'⟩, hfs', hfilt'⟩
          · simp only [hiS, decide_false, ↓reduceIte] at hstep
            have hfs' : js.toFinset = S.filter (fun j => j.val < k + 1) := by
              rw [hjs_S]
              ext x
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨hxS, hxk⟩; exact ⟨hxS, Nat.lt_succ_of_lt hxk⟩
              · rintro ⟨hxS, hxlt⟩
                refine ⟨hxS, ?_⟩
                by_contra hnot
                have hxeqi : x = i := Fin.ext (by omega)
                exact hiS (hxeqi ▸ hxS)
            have hfilt' : js.filter (fun x => decide (x ∈ live (k + 1))) = Li'.1 := by
              rw [hstep, ← hjs_filt, ← hfilt_sub js hjs_lt]
            exact ⟨Li', js, hLi'_enc, hok_js, hfs', hfilt'⟩
      rcases hinv m (le_refl m) with ⟨_, js, _, hok, hfs, _⟩
      refine ⟨js, hok, ?_⟩
      rw [hfs]
      ext x; simp [x.isLt]
  ·
    have hfiber : ∀ (i : Fin m) (s : Fin W),
        ((Finset.univ : Finset (Bool × Fin W)).filter (fun p => edge i s p.1 p.2)).card ≤ w + 2 := by
      intro i s
      by_cases hs : ∃ L : State i.val, enc i.val L = s
      · rcases hs with ⟨L, rfl⟩
        have hlen_le : L.1.length ≤ w := by
          have hsub : L.1.toFinset ⊆ live i.val := fun x hx => L.2.2 x (List.mem_toFinset.mp hx)
          have h1 : L.1.length = L.1.toFinset.card := (List.toFinset_card_of_nodup L.2.1).symm
          exact h1 ▸ (Finset.card_le_card hsub).trans (hlive i.val)
        let fFalse : State (i.val + 1) :=
          ⟨L.1.filter (fun x => decide (x ∈ live (i.val + 1))),
            L.2.1.filter _,
            fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2⟩
        let targets : Finset (Bool × Fin W) :=
          insert (false, enc (i.val + 1) fFalse)
            ((Finset.univ : Finset (Fin (L.1.length + 1))).image (fun p =>
              (true, enc (i.val + 1)
                ⟨(insertAt i L.1 p.val).filter (fun x => decide (x ∈ live (i.val + 1))),
                  by
                    have hi_not_L : i ∉ L.1 := fun h => by
                      have := (Finset.mem_filter.mp (L.2.2 i h)).2.1; omega
                    have hnd_ins : (insertAt i L.1 p.val).Nodup := by
                      have hnd := L.2.1
                      rw [← List.take_append_drop p.val L.1, List.nodup_append] at hnd
                      simp only [insertAt, List.append_assoc, List.cons_append, List.nil_append,
                        List.nodup_append, List.nodup_cons]
                      refine ⟨hnd.1, ⟨fun h => hi_not_L (List.mem_of_mem_drop h), hnd.2.1⟩, ?_⟩
                      intro x hx y hy
                      rcases List.mem_cons.mp hy with rfl | hy2
                      · intro h; exact hi_not_L (List.mem_of_mem_take (h ▸ hx))
                      · exact hnd.2.2 x hx y hy2
                    exact hnd_ins.filter _,
                  fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2⟩)))
        have hsub : (Finset.univ : Finset (Bool × Fin W)).filter (fun p => edge i (enc i.val L) p.1 p.2) ⊆
            targets := by
          intro ⟨take, s'⟩ hp
          have he : edge i (enc i.val L) take s' := (Finset.mem_filter.mp hp).2
          rcases he with ⟨L1, L', hL1, rfl, hstep⟩
          have hLeq : L1 = L := (enc i.val).injective hL1
          subst hLeq
          dsimp only [step] at hstep
          cases take
          · simp only [↓reduceIte] at hstep
            have hL'eq : L' = fFalse := Subtype.ext hstep
            rw [hL'eq]
            exact Finset.mem_insert_self _ _
          · simp only [Bool.true_eq_false, ↓reduceIte] at hstep
            rcases hstep with ⟨_, p, _, _, hL'eq⟩
            apply Finset.mem_insert_of_mem
            refine Finset.mem_image.mpr ⟨p, Finset.mem_univ _, ?_⟩
            congr 1; congr 1
            exact Subtype.ext hL'eq.symm
        calc ((Finset.univ : Finset (Bool × Fin W)).filter (fun p => edge i (enc i.val L) p.1 p.2)).card
            ≤ targets.card := Finset.card_le_card hsub
          _ ≤ ((Finset.univ : Finset (Fin (L.1.length + 1))).image _).card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ (Finset.univ : Finset (Fin (L.1.length + 1))).card + 1 :=
              Nat.add_le_add_right Finset.card_image_le 1
          _ = (L.1.length + 1) + 1 := by simp
          _ ≤ w + 2 := by omega
      · have hemp : (Finset.univ : Finset (Bool × Fin W)).filter (fun p => edge i s p.1 p.2) = ∅ := by
          ext ⟨take, s'⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨L, _, hL, _⟩
          exact hs ⟨L, hL⟩
        rw [hemp, Finset.card_empty]
        exact Nat.zero_le _
    have hcard_eq : (cost W edge).card =
        ∑ p : Fin m × Fin W, ((Finset.univ : Finset (Bool × Fin W)).filter (fun q => edge p.1 p.2 q.1 q.2)).card := by
      have hmaps : ∀ v ∈ cost W edge, (v.1, v.2.1) ∈ (Finset.univ : Finset (Fin m × Fin W)) :=
        fun _ _ => Finset.mem_univ _
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      congr 1; ext ⟨i, s⟩
      refine Finset.card_bij (fun v _ => (v.2.2.1, v.2.2.2)) ?_ ?_ ?_
      · intro v hv
        simp only [Finset.mem_filter, cost, Finset.mem_univ, true_and] at hv ⊢
        rcases hv with ⟨he, hp⟩
        have h1 : v.1 = i := congrArg Prod.fst hp
        have h2 : v.2.1 = s := congrArg Prod.snd hp
        rw [← h1, ← h2]
        exact he
      · intro v1 hv1 v2 hv2 heq
        have hp1 := (Finset.mem_filter.mp hv1).2
        have hp2 := (Finset.mem_filter.mp hv2).2
        rcases v1 with ⟨i1, s1, t1, s1'⟩
        rcases v2 with ⟨i2, s2, t2, s2'⟩
        have h1 : i1 = i2 := (congrArg Prod.fst hp1).trans (congrArg Prod.fst hp2).symm
        have h2 : s1 = s2 := (congrArg Prod.snd hp1).trans (congrArg Prod.snd hp2).symm
        have h3 : t1 = t2 := congrArg Prod.fst heq
        have h4 : s1' = s2' := congrArg Prod.snd heq
        subst h1; subst h2; subst h3; subst h4; rfl
      · intro ⟨take, s'⟩ hq
        refine ⟨(i, s, take, s'), ?_, rfl⟩
        simp only [Finset.mem_filter, cost, Finset.mem_univ, true_and] at hq ⊢
        exact ⟨hq, trivial⟩
    rw [hcard_eq]
    calc ∑ p : Fin m × Fin W,
          ((Finset.univ : Finset (Bool × Fin W)).filter (fun q => edge p.1 p.2 q.1 q.2)).card
        ≤ ∑ _p : Fin m × Fin W, (w + 2) := Finset.sum_le_sum (fun p _ => hfiber p.1 p.2)
      _ = (Finset.univ : Finset (Fin m × Fin W)).card * (w + 2) := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
      _ = m * (w + 2) * W := by simp [Finset.card_univ]; ring

end PEqualNP.Outside.L_lib_1249_aux

theorem PEqualNP.Outside.L_lib_1249 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m w : Nat) (a b c d : Fin m → Finset (Fin n)),
  let named := fun (js : List (Fin m)) =>
    List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
      (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧
        a j ⊆ u ∧ u ⊆ b j ∧ c j ⊆ v ∧ v ⊆ d j) js Finset.univ
  let feasible := fun (S : Finset (Fin m)) =>
    ∃ js : List (Fin m), js.Nodup ∧ js.toFinset = S ∧ named js
  let recognizes := fun (W : Nat) (start : Fin W) (finals : Finset (Fin W))
      (edge : Fin m → Fin W → Bool → Fin W → Prop) =>
    ∀ S : Finset (Fin m), feasible S ↔
      ∃ st : Fin (m+1) → Fin W, st 0 = start ∧ st (Fin.last m) ∈ finals ∧
        ∀ i : Fin m, edge i (st i.castSucc) (decide (i ∈ S)) (st i.succ)
  let cost := fun (W : Nat) (edge : Fin m → Fin W → Bool → Fin W → Prop) =>
    (Finset.univ : Finset (Fin m × Fin W × Bool × Fin W)).filter
      (fun v => edge v.1 v.2.1 v.2.2.1 v.2.2.2)
  let valid := fun i => a i ⊆ b i ∧ a i ⊆ d i ∧ c i ⊆ d i
  let conf := fun i j => valid i ∧ valid j ∧ ¬ (a i ∪ c i) ⊆ (b j ∩ d j)
  let live := fun (k : Nat) => (Finset.univ : Finset (Fin m)).filter
    (fun i => i.val < k ∧ ∃ j : Fin m, k ≤ j.val ∧ (conf i j ∨ conf j i))
  (∀ k, (live k).card ≤ w) →
  let W := (Finset.range (w+1)).sum (fun t => w.descFactorial t)
  ∃ (start : Fin W) (finals : Finset (Fin W)) (edge : Fin m → Fin W → Bool → Fin W → Prop),
    recognizes W start finals edge ∧ (cost W edge).card ≤ m*(w+2)*W) := by
  intro n m w a b c d named feasible recognizes cost valid conf live hlive
  have hdeqn : (instDecidableEqFin n) = (fun x y => Classical.propDecidable (x = y)) :=
    Subsingleton.elim _ _
  have hdeqm : (instDecidableEqFin m) = (fun x y => Classical.propDecidable (x = y)) :=
    Subsingleton.elim _ _
  rcases PEqualNP.Outside.L_lib_1249_aux.main_proof n m w a b c d (by
    intro k
    convert hlive k using 2
    ext i
    simp only [live, conf, valid, Finset.mem_filter, Finset.mem_univ, true_and]
    convert Iff.rfl) with
    ⟨start, finals, edge, hrec, hcost⟩
  refine ⟨start, finals, edge, ?_, ?_⟩
  · intro S
    have h1 := hrec S
    have hdec : ∀ i : Fin m, @decide (i ∈ S) (Classical.propDecidable _) =
        @decide (i ∈ S) (Finset.decidableMem i S) := fun i => by
      by_cases h : i ∈ S <;> simp [h]
    convert h1 using 1
    · simp only [feasible, named]
      convert Iff.rfl
    · exact exists_congr fun st =>
        and_congr_right fun _ => and_congr_right fun _ =>
          forall_congr' fun i => by rw [hdec i]
  · convert hcost using 2
