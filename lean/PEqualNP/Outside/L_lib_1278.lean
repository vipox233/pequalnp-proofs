import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1278_aux

open scoped Classical

lemma even_card_of_involution {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → α)
    (hmem : ∀ x ∈ s, f x ∈ s)
    (hinv : ∀ x ∈ s, f (f x) = x)
    (hne : ∀ x ∈ s, f x ≠ x) : Even s.card := by
  classical
  induction h : s.card using Nat.strong_induction_on generalizing s with
  | ind n ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · rw [← h, Finset.card_empty]; exact Even.zero
    · have hfx : f x ∈ s := hmem x hx
      have hne_x : f x ≠ x := hne x hx
      let t := (s.erase x).erase (f x)
      have ht_card : s.card = t.card + 2 := by
        have h1 : f x ∈ s.erase x := Finset.mem_erase.mpr ⟨hne_x, hfx⟩
        have h2 : (s.erase x).card = t.card + 1 := (Finset.card_erase_add_one h1).symm
        have h3 : s.card = (s.erase x).card + 1 := (Finset.card_erase_add_one hx).symm
        omega
      have ht_lt : t.card < n := by omega
      have ht_mem : ∀ y ∈ t, f y ∈ t := by
        intro y hy
        have hy1 : y ≠ f x := (Finset.mem_erase.mp hy).1
        have hy2 : y ∈ s.erase x := (Finset.mem_erase.mp hy).2
        have hy3 : y ≠ x := (Finset.mem_erase.mp hy2).1
        have hy4 : y ∈ s := (Finset.mem_erase.mp hy2).2
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmem y hy4⟩⟩
        · intro heq
          apply hy3
          calc y = f (f y) := (hinv y hy4).symm
            _ = f (f x) := congrArg f heq
            _ = x := hinv x hx
        · intro heq
          apply hy1
          calc y = f (f y) := (hinv y hy4).symm
            _ = f x := congrArg f heq
      have ht_even : Even t.card :=
        ih t.card ht_lt t ht_mem
          (fun y hy => hinv y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)))
          (fun y hy => hne y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)))
          rfl
      rw [← h, ht_card]
      exact ht_even.add (even_two)

def altBool (s : Bool) (i : ℕ) : Bool := if i % 2 = 0 then s else !s

def delFin {n : ℕ} (k : Fin (n + 1)) (i : Fin n) : Fin (n + 1) := k.succAbove i

lemma delFin_lt {n : ℕ} (k : Fin (n + 1)) (i : Fin n) (h : i.val < k.val) :
    (delFin k i).val = i.val := by
  simp only [delFin, Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  rw [if_pos h]; rfl

lemma delFin_ge {n : ℕ} (k : Fin (n + 1)) (i : Fin n) (h : k.val ≤ i.val) :
    (delFin k i).val = i.val + 1 := by
  simp only [delFin, Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  rw [if_neg (not_lt.mpr h)]; rfl

lemma altBool_succ (s : Bool) (i : ℕ) : altBool s (i + 1) = !(altBool s i) := by
  unfold altBool
  by_cases h : i % 2 = 0
  · have h1 : (i + 1) % 2 ≠ 0 := by omega
    simp [h, h1]
  · have h1 : (i + 1) % 2 = 0 := by omega
    simp [h, h1]

lemma del_alt_parity {n : ℕ} (sgn : Fin (n + 1) → Bool) :
    Odd (Finset.univ.filter (fun k : Fin (n + 1) =>
      ∀ i : Fin n, sgn (delFin k i) = altBool true i.val)).card ↔
    ((∀ i : Fin (n + 1), sgn i = altBool true i.val) ∨
     (∀ i : Fin (n + 1), sgn i = altBool false i.val)) := by
  classical
  let P : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => sgn j = altBool true j.val)
  let Q : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => sgn j ≠ altBool true j.val)
  set G : Finset (Fin (n + 1)) := Finset.univ.filter (fun k : Fin (n + 1) =>
    ∀ i : Fin n, sgn (delFin k i) = altBool true i.val)
  have hG_iff : ∀ k : Fin (n + 1), k ∈ G ↔ (∀ j : Fin (n + 1), j < k → j ∈ P) ∧
      (∀ j : Fin (n + 1), k < j → j ∈ Q) := by
    intro k
    simp only [G, P, Q, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hk
      constructor
      · intro j hj
        let i : Fin n := ⟨j.val, by omega⟩
        have hdel : delFin k i = j := Fin.ext (delFin_lt k i hj)
        simpa [hdel, i] using hk i
      · intro j hj
        let i : Fin n := ⟨j.val - 1, by omega⟩
        have hi_val : i.val = j.val - 1 := rfl
        have hle : k.val ≤ i.val := by omega
        have hdel : delFin k i = j := Fin.ext (by rw [delFin_ge k i hle]; omega)
        have h1 := hk i
        rw [hdel] at h1
        have hne : altBool true i.val ≠ altBool true j.val := by
          have hj_eq : j.val = i.val + 1 := by omega
          rw [hj_eq, altBool_succ]
          cases altBool true i.val <;> decide
        rw [h1]; exact hne
    · rintro ⟨hP, hQ⟩ i
      by_cases hlt : i.val < k.val
      · have h1 := hP (delFin k i) (by rw [Fin.lt_def, delFin_lt k i hlt]; exact hlt)
        rw [delFin_lt k i hlt] at h1
        exact h1
      · have hle : k.val ≤ i.val := not_lt.mp hlt
        have h1 := hQ (delFin k i) (by rw [Fin.lt_def, delFin_ge k i hle]; omega)
        rw [delFin_ge k i hle, altBool_succ] at h1
        cases hs : sgn (delFin k i) <;> cases ha : altBool true i.val <;> simp_all
  have hQ_empty : Q = ∅ ↔ ∀ i : Fin (n + 1), sgn i = altBool true i.val := by
    simp [Q, Finset.filter_eq_empty_iff]
  have hP_empty : P = ∅ ↔ ∀ i : Fin (n + 1), sgn i = altBool false i.val := by
    rw [Finset.eq_empty_iff_forall_notMem]
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h i
    · have hi := h i
      unfold altBool at hi ⊢
      by_cases hm : i.val % 2 = 0 <;> cases hs : sgn i <;> simp_all
    · have hi := h i
      unfold altBool at hi ⊢
      by_cases hm : i.val % 2 = 0 <;> cases hs : sgn i <;> simp_all
  by_cases hQe : Q = ∅
  · have hGeq : G = {Fin.last n} := by
      ext k
      rw [hG_iff, Finset.mem_singleton, hQe]
      constructor
      · rintro ⟨_, hQ⟩
        by_contra hne
        have hlt : k < Fin.last n := lt_of_le_of_ne (Fin.le_last k) hne
        exact Finset.notMem_empty _ (hQ (Fin.last n) hlt)
      · rintro rfl
        refine ⟨fun j _ => ?_, fun j hj => (not_lt_of_ge (Fin.le_last j) hj).elim⟩
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hQ_empty.mp hQe j
    rw [hGeq, Finset.card_singleton]
    exact ⟨fun _ => Or.inl (hQ_empty.mp hQe), fun _ => odd_one⟩
  · by_cases hPe : P = ∅
    · have hGeq : G = {0} := by
        ext k
        rw [hG_iff, Finset.mem_singleton, hPe]
        constructor
        · rintro ⟨hP, _⟩
          by_contra hne
          have hpos : (0 : Fin (n + 1)) < k := Fin.pos_iff_ne_zero.mpr hne
          exact Finset.notMem_empty _ (hP 0 hpos)
        · rintro rfl
          refine ⟨fun j hj => (Fin.not_lt_zero j hj).elim, fun j _ => ?_⟩
          simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
          have hj := hP_empty.mp hPe j
          unfold altBool at hj ⊢
          by_cases hm : j.val % 2 = 0 <;> cases hs : sgn j <;> simp_all
      rw [hGeq, Finset.card_singleton]
      exact ⟨fun _ => Or.inr (hP_empty.mp hPe), fun _ => odd_one⟩
    · have hPne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPe
      have hQne : Q.Nonempty := Finset.nonempty_iff_ne_empty.mpr hQe
      let pmax := P.max' hPne
      let qmin := Q.min' hQne
      have hp_mem : pmax ∈ P := Finset.max'_mem P hPne
      have hq_mem : qmin ∈ Q := Finset.min'_mem Q hQne
      have hpq_ne : pmax ≠ qmin := by
        intro heq
        rw [heq] at hp_mem
        simp only [P, Q, Finset.mem_filter] at hp_mem hq_mem
        exact hq_mem.2 hp_mem.2
      have hG_even : Even G.card := by
        by_cases hlt : qmin < pmax
        · have hGe : G = ∅ := by
            ext k; simp only [Finset.notMem_empty, iff_false]
            rw [hG_iff]; rintro ⟨hP, hQ⟩
            have h1 : k ≤ qmin := by
              by_contra h; push Not at h
              have := hP qmin h
              simp only [P, Q, Finset.mem_filter] at this hq_mem
              exact hq_mem.2 this.2
            have h2 : pmax ≤ k := by
              by_contra h; push Not at h
              have := hQ pmax h
              simp only [P, Q, Finset.mem_filter] at this hp_mem
              exact this.2 hp_mem.2
            exact not_lt_of_ge (le_trans h2 h1) hlt
          rw [hGe]; exact (Even.zero : Even 0)
        · have hpq : pmax < qmin := lt_of_le_of_ne (not_lt.mp hlt) hpq_ne
          have hstep : qmin.val = pmax.val + 1 := by
            by_contra hne
            have hmid_lt : pmax.val + 1 < qmin.val := by omega
            let m : Fin (n + 1) := ⟨pmax.val + 1, by omega⟩
            by_cases hmP : m ∈ P
            · have := Finset.le_max' P m hmP
              change pmax.val + 1 ≤ pmax.val at this; omega
            · have hmQ : m ∈ Q := by
                simp only [P, Q, Finset.mem_filter, Finset.mem_univ, true_and] at hmP ⊢
                exact hmP
              have := Finset.min'_le Q m hmQ
              change qmin.val ≤ pmax.val + 1 at this; omega
          have hGeq : G = {pmax, qmin} := by
            ext k
            rw [hG_iff, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨hP, hQ⟩
              have h1 : k ≤ qmin := by
                by_contra h; push Not at h
                have := hP qmin h
                simp only [P, Q, Finset.mem_filter] at this hq_mem
                exact hq_mem.2 this.2
              have h2 : pmax ≤ k := by
                by_contra h; push Not at h
                have := hQ pmax h
                simp only [P, Q, Finset.mem_filter] at this hp_mem
                exact this.2 hp_mem.2
              have hkval : k.val = pmax.val ∨ k.val = qmin.val := by
                change pmax.val ≤ k.val at h2
                change k.val ≤ qmin.val at h1
                omega
              rcases hkval with h | h
              · exact Or.inl (Fin.ext h)
              · exact Or.inr (Fin.ext h)
            · rintro (rfl | rfl)
              · refine ⟨fun j hj => ?_, fun j hj => ?_⟩
                · by_contra hjP
                  have hjQ : j ∈ Q := by
                    simp only [P, Q, Finset.mem_filter, Finset.mem_univ, true_and] at hjP ⊢; exact hjP
                  have := Finset.min'_le Q j hjQ
                  exact not_lt_of_ge this (lt_trans hj hpq)
                · by_contra hjQ
                  have hjP : j ∈ P := by
                    simp only [P, Q, Finset.mem_filter, Finset.mem_univ, true_and] at hjQ ⊢
                    exact not_not.mp hjQ
                  exact not_lt_of_ge (Finset.le_max' P j hjP) hj
              · refine ⟨fun j hj => ?_, fun j hj => ?_⟩
                · by_contra hjP
                  have hjQ : j ∈ Q := by
                    simp only [P, Q, Finset.mem_filter, Finset.mem_univ, true_and] at hjP ⊢; exact hjP
                  exact not_lt_of_ge (Finset.min'_le Q j hjQ) hj
                · by_contra hjQ
                  have hjP : j ∈ P := by
                    simp only [P, Q, Finset.mem_filter, Finset.mem_univ, true_and] at hjQ ⊢
                    exact not_not.mp hjQ
                  exact not_lt_of_ge (Finset.le_max' P j hjP) (lt_trans hpq hj)
          rw [hGeq, Finset.card_pair hpq_ne]; exact even_two
      constructor
      · intro hodd; exact (Nat.not_even_iff_odd.mpr hodd hG_even).elim
      · rintro (h1 | h2)
        · exact (hQe (hQ_empty.mpr h1)).elim
        · exact (hPe (hP_empty.mpr h2)).elim

def IsAlt (s : Bool) (S : Finset ℤ) (m : ℕ) : Prop :=
  S.card = m ∧ ∃ f : Fin m → ℤ,
    (∀ i, f i ∈ S) ∧
    (∀ i j : Fin m, i < j → (f i).natAbs < (f j).natAbs) ∧
    (∀ i : Fin m, decide (0 < f i) = altBool s i.val)

lemma isAlt_neg_iff (s : Bool) (S : Finset ℤ) (m : ℕ)
    (hnz : ∀ z ∈ S, z ≠ 0) :
    IsAlt s (S.image Neg.neg) m ↔ IsAlt (!s) S m := by
  have hcard : (S.image Neg.neg).card = S.card :=
    Finset.card_image_of_injective S neg_injective
  have hneg_pos : ∀ z : ℤ, z ≠ 0 → decide (0 < -z) = !decide (0 < z) := by
    intro z hz; by_cases h : 0 < z <;> simp [h] <;> omega
  have halt_neg : ∀ (b : Bool) (i : ℕ), altBool (!b) i = !(altBool b i) := by
    intro b i; unfold altBool; by_cases h : i % 2 = 0 <;> cases b <;> simp [h]
  constructor
  · rintro ⟨hc, f, hmem, hinc, hsgn⟩
    refine ⟨by omega, fun i => -(f i), ?_, ?_, ?_⟩
    · intro i
      obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp (hmem i)
      have : -(f i) = z := by omega
      dsimp only; rwa [this]
    · intro i j hij; simpa using hinc i j hij
    · intro i
      obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp (hmem i)
      have hfz : f i ≠ 0 := by have := hnz z hz; omega
      rw [hneg_pos (f i) hfz, hsgn i, halt_neg]
  · rintro ⟨hc, f, hmem, hinc, hsgn⟩
    refine ⟨by omega, fun i => -(f i), ?_, ?_, ?_⟩
    · intro i; exact Finset.mem_image.mpr ⟨f i, hmem i, rfl⟩
    · intro i j hij; simpa using hinc i j hij
    · intro i
      rw [hneg_pos (f i) (hnz (f i) (hmem i)), hsgn i, halt_neg, Bool.not_not]

lemma exists_sort_natAbs' (S : Finset ℤ) (m : ℕ) (hcard : S.card = m)
    (hdist : ∀ x ∈ S, ∀ y ∈ S, x.natAbs = y.natAbs → x = y) :
    ∃ f : Fin m → ℤ, Finset.univ.image f = S ∧ Function.Injective f ∧
      ∀ i j : Fin m, i < j → (f i).natAbs < (f j).natAbs := by
  classical
  let A : Finset ℕ := S.image Int.natAbs
  have hAcard : A.card = m := by
    rw [Finset.card_image_of_injOn (fun x hx y hy h => hdist x hx y hy h), hcard]
  let g : Fin m ≃o A := A.orderIsoOfFin hAcard
  have hex : ∀ i : Fin m, ∃ z ∈ S, z.natAbs = (g i).val :=
    fun i => Finset.mem_image.mp (g i).property
  choose f hf_mem hf_abs using hex
  have hinc : ∀ i j : Fin m, i < j → (f i).natAbs < (f j).natAbs := by
    intro i j hij; rw [hf_abs i, hf_abs j]; exact g.strictMono hij
  have hinj : Function.Injective f := by
    intro i j hij; by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact ne_of_lt (hinc i j h) (congrArg Int.natAbs hij)
    · exact ne_of_gt (hinc j i h) (congrArg Int.natAbs hij)
  have himg : Finset.univ.image f = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz; exact hf_mem i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_fin, hcard]
  exact ⟨f, himg, hinj, hinc⟩

lemma sort_natAbs_unique {m : ℕ} {S : Finset ℤ} {f g : Fin m → ℤ}
    (hf_img : Finset.univ.image f = S) (hg_img : Finset.univ.image g = S)
    (hf_inc : ∀ i j : Fin m, i < j → (f i).natAbs < (f j).natAbs)
    (hg_inc : ∀ i j : Fin m, i < j → (g i).natAbs < (g j).natAbs) : f = g := by
  have hdist : ∀ x ∈ S, ∀ y ∈ S, x.natAbs = y.natAbs → x = y := by
    intro x hx y hy habs
    rw [← hf_img] at hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    by_contra hne
    have hij : i ≠ j := fun e => hne (congrArg f e)
    rcases lt_or_gt_of_ne hij with h | h
    · exact ne_of_lt (hf_inc i j h) habs
    · exact ne_of_gt (hf_inc j i h) habs
  have hf_abs : Finset.univ.image (fun i => (f i).natAbs) = S.image Int.natAbs := by
    rw [← hf_img, Finset.image_image]; rfl
  have hg_abs : Finset.univ.image (fun i => (g i).natAbs) = S.image Int.natAbs := by
    rw [← hg_img, Finset.image_image]; rfl
  have hlt_eq : ∀ i : Fin m, (f i).natAbs = (g i).natAbs := by
    intro i
    induction hi : i.val using Nat.strong_induction_on generalizing i with
    | ind k ih =>
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hmem : (f i).natAbs ∈ Finset.univ.image (fun j => (g j).natAbs) := by
          rw [hg_abs, ← hf_abs]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
        have hji : j < i := by
          by_contra hge
          have hle : i ≤ j := not_lt.mp hge
          rcases eq_or_lt_of_le hle with rfl | h
          · omega
          · have := hg_inc i j h; omega
        have hprev := ih j.val (by omega) j rfl
        have := hf_inc j i hji
        omega
      · have hmem : (g i).natAbs ∈ Finset.univ.image (fun j => (f j).natAbs) := by
          rw [hf_abs, ← hg_abs]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
        have hji : j < i := by
          by_contra hge
          have hle : i ≤ j := not_lt.mp hge
          rcases eq_or_lt_of_le hle with rfl | h
          · omega
          · have := hf_inc i j h; omega
        have hprev := ih j.val (by omega) j rfl
        have := hg_inc j i hji
        omega
  funext i
  exact hdist (f i) (hf_img ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    (g i) (hg_img ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) (hlt_eq i)

lemma good_facets_parity {n : ℕ} (v : Fin (n + 1) → ℤ)
    (hnz : ∀ i, v i ≠ 0)
    (hnoop : ∀ i j, v i ≠ -v j) :
    Odd (Finset.univ.filter (fun r : Fin (n + 1) =>
      IsAlt true ((Finset.univ.erase r).image v) n)).card ↔
    (IsAlt true (Finset.univ.image v) (n + 1) ∨ IsAlt false (Finset.univ.image v) (n + 1)) := by
  classical
  let S := Finset.univ.image v
  set G := Finset.univ.filter (fun r : Fin (n + 1) =>
    IsAlt true ((Finset.univ.erase r).image v) n)
  have hS_le : S.card ≤ n + 1 := by
    calc S.card ≤ (Finset.univ : Finset (Fin (n + 1))).card := Finset.card_image_le
      _ = n + 1 := Finset.card_fin (n + 1)
  by_cases hlt : S.card < n
  · have hGe : G = ∅ := by
      ext r; simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hA
      have hsub : (Finset.univ.erase r).image v ⊆ S := Finset.image_subset_image (Finset.subset_univ _)
      have hle := Finset.card_le_card hsub
      rw [hA.1] at hle; omega
    rw [hGe, Finset.card_empty]
    constructor
    · intro h; exact (Nat.not_odd_zero h).elim
    · rintro (h | h) <;> (have h1 : S.card = n + 1 := h.1; omega)
  · by_cases heq : S.card = n
    ·
      have hnot_inj : ¬ Function.Injective v := by
        intro hinj
        have := Finset.card_image_of_injective Finset.univ hinj
        rw [Finset.card_fin] at this
        change S.card = n + 1 at this; omega
      have hex_dup : ∃ i0 j0, v i0 = v j0 ∧ i0 ≠ j0 := by
        unfold Function.Injective at hnot_inj; push Not at hnot_inj; exact hnot_inj
      obtain ⟨i0, j0, hvij, hne⟩ := hex_dup
      have herase_eq : ∀ r : Fin (n + 1), ((Finset.univ.erase r).image v = S) ↔ (r = i0 ∨ r = j0) := by
        intro r
        constructor
        · intro heqS
          by_contra hnor
          push Not at hnor
          have hcard_lt : ((Finset.univ.erase r).image v).card < n := by

            have hi0 : i0 ∈ Finset.univ.erase r := Finset.mem_erase.mpr ⟨Ne.symm hnor.1, Finset.mem_univ _⟩
            have hj0 : j0 ∈ Finset.univ.erase r := Finset.mem_erase.mpr ⟨Ne.symm hnor.2, Finset.mem_univ _⟩
            have hsub : (Finset.univ.erase r).image v ⊆ ((Finset.univ.erase r).erase j0).image v := by
              intro z hz
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
              by_cases hxj : x = j0
              · subst hxj; exact Finset.mem_image.mpr ⟨i0, Finset.mem_erase.mpr ⟨hne, hi0⟩, hvij⟩
              · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxj, hx⟩, rfl⟩
            have hle := le_trans (Finset.card_le_card hsub) Finset.card_image_le
            have h1 : ((Finset.univ.erase r).erase j0).card + 1 = (Finset.univ.erase r).card :=
              Finset.card_erase_add_one hj0
            have h2 : (Finset.univ.erase r).card + 1 = n + 1 := by
              have hc := Finset.card_erase_add_one (Finset.mem_univ r)
              simpa [Finset.card_fin] using hc
            omega
          rw [heqS, heq] at hcard_lt; omega
        · rintro (hr | hr)
          · rw [hr]
            apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.subset_univ _))
            intro z hz; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
            by_cases hx : x = i0
            · subst hx; exact Finset.mem_image.mpr ⟨j0, Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩, hvij.symm⟩
            · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩, rfl⟩
          · rw [hr]
            apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.subset_univ _))
            intro z hz; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
            by_cases hx : x = j0
            · subst hx; exact Finset.mem_image.mpr ⟨i0, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩, hvij⟩
            · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩, rfl⟩
      have hG_even : Even G.card := by
        by_cases hA : IsAlt true S n
        · have hGeq : G = {i0, j0} := by
            ext r; simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · intro hAr
              have hsub : (Finset.univ.erase r).image v ⊆ S := Finset.image_subset_image (Finset.subset_univ _)
              have hseq : (Finset.univ.erase r).image v = S :=
                Finset.eq_of_subset_of_card_le hsub (by rw [hAr.1, heq])
              exact (herase_eq r).mp hseq
            · intro hr; rw [(herase_eq r).mpr hr]; exact hA
          rw [hGeq, Finset.card_pair hne]; exact even_two
        · have hGe : G = ∅ := by
            ext r; simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            intro hAr
            have hsub : (Finset.univ.erase r).image v ⊆ S := Finset.image_subset_image (Finset.subset_univ _)
            have hseq : (Finset.univ.erase r).image v = S :=
              Finset.eq_of_subset_of_card_le hsub (by rw [hAr.1, heq])
            rw [hseq] at hAr; exact hA hAr
          rw [hGe]; exact (Even.zero : Even 0)
      constructor
      · intro hodd; exact (Nat.not_even_iff_odd.mpr hodd hG_even).elim
      · rintro (h | h) <;> (have h1 : S.card = n + 1 := h.1; omega)
    ·
      have hScard : S.card = n + 1 := by omega
      have hvinj : Function.Injective v := by
        have h1 : (Finset.univ.image v).card = (Finset.univ : Finset (Fin (n + 1))).card := by
          rw [Finset.card_fin]; exact hScard
        intro a b hab
        exact Finset.injOn_of_card_image_eq h1 (Finset.mem_univ a) (Finset.mem_univ b) hab
      have hdist : ∀ x ∈ S, ∀ y ∈ S, x.natAbs = y.natAbs → x = y := by
        intro x hx y hy habs
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
        rcases Int.natAbs_eq_natAbs_iff.mp habs with h | h
        · exact h
        · exact (hnoop i j h).elim
      obtain ⟨f, hf_img, hf_inj, hf_inc⟩ := exists_sort_natAbs' S (n + 1) hScard hdist

      have hex_e : ∀ k : Fin (n + 1), ∃ r : Fin (n + 1), v r = f k := by
        intro k
        have hmem : f k ∈ S := hf_img ▸ Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
        obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hmem
        exact ⟨r, hr⟩
      choose e_fn he_eq using hex_e
      have he_inj : Function.Injective e_fn := by
        intro a b hab
        exact hf_inj (by rw [← he_eq a, ← he_eq b, hab])
      let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.ofBijective e_fn (Finite.injective_iff_bijective.mp he_inj)
      let sgn : Fin (n + 1) → Bool := fun k => decide (0 < f k)
      have hfacet_iff : ∀ k : Fin (n + 1),
          IsAlt true ((Finset.univ.erase (e k)).image v) n ↔
          ∀ i : Fin n, sgn (delFin k i) = altBool true i.val := by
        intro k
        have himg_del : Finset.univ.image (fun i : Fin n => f (delFin k i)) = (Finset.univ.erase (e k)).image v := by
          ext z; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase]
          constructor
          · rintro ⟨i, rfl⟩
            refine ⟨e (delFin k i), ⟨?_, trivial⟩, he_eq (delFin k i)⟩
            intro heq
            exact Fin.succAbove_ne k i (e.injective heq)
          · rintro ⟨r, hrne, rfl⟩
            have hne' : e.symm r ≠ k := fun h => hrne.1 (by rw [← h, e.apply_symm_apply])
            obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne'
            refine ⟨i, ?_⟩
            change f (k.succAbove i) = v r
            rw [hi, ← he_eq (e.symm r)]
            exact congrArg v (e.apply_symm_apply r)
        have hinc_del : ∀ i j : Fin n, i < j → (f (delFin k i)).natAbs < (f (delFin k j)).natAbs :=
          fun i j hij => hf_inc _ _ (Fin.succAbove_lt_succAbove_iff.mpr hij)
        have hcard_del : ((Finset.univ.erase (e k)).image v).card = n := by
          rw [Finset.card_image_of_injective _ hvinj, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
          omega
        constructor
        · rintro ⟨_, g, hg_mem, hg_inc, hg_sgn⟩
          have hg_inj : Function.Injective g := by
            intro a b hab; by_contra hne
            rcases lt_or_gt_of_ne hne with h | h
            · exact ne_of_lt (hg_inc a b h) (congrArg Int.natAbs hab)
            · exact ne_of_gt (hg_inc b a h) (congrArg Int.natAbs hab)
          have hg_img : Finset.univ.image g = (Finset.univ.erase (e k)).image v := by
            apply Finset.eq_of_subset_of_card_le
            · intro z hz; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz; exact hg_mem i
            · rw [Finset.card_image_of_injective _ hg_inj, Finset.card_fin, hcard_del]
          have hfg : (fun i : Fin n => f (delFin k i)) = g :=
            sort_natAbs_unique himg_del hg_img hinc_del hg_inc
          intro i
          change decide (0 < f (delFin k i)) = altBool true i.val
          rw [congrFun hfg i]
          exact hg_sgn i
        · intro hall
          refine ⟨hcard_del, fun i => f (delFin k i), ?_, hinc_del, hall⟩
          intro i; rw [← himg_del]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      have hG_card : G.card = (Finset.univ.filter (fun k : Fin (n + 1) =>
          ∀ i : Fin n, sgn (delFin k i) = altBool true i.val)).card := by
        apply Finset.card_bij (fun r _ => e.symm r)
        · intro r hr
          simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          rw [← hfacet_iff (e.symm r), e.apply_symm_apply]
          exact hr
        · intro a _ b _ hab; exact e.symm.injective hab
        · intro k hk
          refine ⟨e k, ?_, e.symm_apply_apply k⟩
          simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          exact (hfacet_iff k).mpr hk
      have halt_iff : ∀ s : Bool, IsAlt s S (n + 1) ↔ ∀ i : Fin (n + 1), sgn i = altBool s i.val := by
        intro s
        constructor
        · rintro ⟨_, g, hg_mem, hg_inc, hg_sgn⟩
          have hg_inj : Function.Injective g := by
            intro a b hab; by_contra hne
            rcases lt_or_gt_of_ne hne with h | h
            · exact ne_of_lt (hg_inc a b h) (congrArg Int.natAbs hab)
            · exact ne_of_gt (hg_inc b a h) (congrArg Int.natAbs hab)
          have hg_img : Finset.univ.image g = S := by
            apply Finset.eq_of_subset_of_card_le
            · intro z hz; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz; exact hg_mem i
            · rw [Finset.card_image_of_injective _ hg_inj, Finset.card_fin, hScard]
          have hfg : f = g := sort_natAbs_unique hf_img hg_img hf_inc hg_inc
          intro i; change decide (0 < f i) = _; rw [hfg]; exact hg_sgn i
        · intro hall
          refine ⟨hScard, f, ?_, hf_inc, hall⟩
          intro i; rw [← hf_img]; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      rw [hG_card, halt_iff true, halt_iff false]
      exact del_alt_parity sgn

abbrev SP (d : ℕ) := { p : Finset (Fin d) × Finset (Fin d) // Disjoint p.1 p.2 ∧ (p.1 ∪ p.2).Nonempty }

def spSwap {d : ℕ} (p : SP d) : SP d :=
  ⟨(p.val.2, p.val.1), p.property.1.symm, by dsimp; rw [Finset.union_comm]; exact p.property.2⟩

@[simp] lemma spSwap_swap {d : ℕ} (p : SP d) : spSwap (spSwap p) = p := by
  ext <;> rfl

abbrev SChain (d : ℕ) := Equiv.Perm (Fin d) × (Fin d → Bool)

def negChain {d : ℕ} (σ : SChain d) : SChain d := (σ.1, fun j => !(σ.2 j))

@[simp] lemma negChain_neg {d : ℕ} (σ : SChain d) : negChain (negChain σ) = σ := by
  ext i <;> simp [negChain]

def pref {d : ℕ} (σ : SChain d) (i : Fin d) : SP d :=
  ⟨((Finset.univ.filter (fun j : Fin d => j.val ≤ i.val ∧ σ.2 j = true)).image σ.1,
    (Finset.univ.filter (fun j : Fin d => j.val ≤ i.val ∧ σ.2 j = false)).image σ.1),
   by
     rw [Finset.disjoint_left]
     intro x hx1 hx2
     obtain ⟨j1, hj1, rfl⟩ := Finset.mem_image.mp hx1
     obtain ⟨j2, hj2, heq⟩ := Finset.mem_image.mp hx2
     have hjj : j2 = j1 := σ.1.injective heq
     subst hjj
     simp only [Finset.mem_filter] at hj1 hj2
     rw [hj1.2.2] at hj2; exact Bool.noConfusion hj2.2.2,
   by
     cases hb : σ.2 i
     · refine ⟨σ.1 i, Finset.mem_union_right _ ?_⟩
       exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hb⟩, rfl⟩
     · refine ⟨σ.1 i, Finset.mem_union_left _ ?_⟩
       exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hb⟩, rfl⟩⟩

lemma pref_mono {d : ℕ} (σ : SChain d) {i j : Fin d} (hij : i ≤ j) :
    (pref σ i).val.1 ⊆ (pref σ j).val.1 ∧ (pref σ i).val.2 ⊆ (pref σ j).val.2 := by
  constructor
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_filter] at ha
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans ha.2.1 hij, ha.2.2⟩, rfl⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_filter] at ha
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans ha.2.1 hij, ha.2.2⟩, rfl⟩

lemma pref_negChain {d : ℕ} (σ : SChain d) (i : Fin d) :
    pref (negChain σ) i = spSwap (pref σ i) := by
  apply Subtype.ext; apply Prod.ext <;> (ext x; simp [pref, negChain, spSwap])

def chainLabels {d : ℕ} (lam : SP d → ℤ) (σ : SChain d) : Finset ℤ :=
  Finset.univ.image (fun i : Fin d => lam (pref σ i))

lemma chainLabels_neg {d : ℕ} (lam : SP d → ℤ) (hanti : ∀ p, lam (spSwap p) = -lam p) (σ : SChain d) :
    chainLabels lam (negChain σ) = (chainLabels lam σ).image Neg.neg := by
  ext z; simp only [chainLabels, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨lam (pref σ i), ⟨i, rfl⟩, by rw [pref_negChain, hanti]⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rw [pref_negChain, hanti]⟩

def embSP {d : ℕ} (p : SP d) : SP (d + 1) :=
  ⟨(p.val.1.image Fin.castSucc, p.val.2.image Fin.castSucc),
   Finset.disjoint_left.mpr (fun _ h1 h2 => by
     obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h1
     obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp h2
     have := Fin.castSucc_injective _ heq; subst this
     exact Finset.disjoint_left.mp p.property.1 ha hb),
   by
     obtain ⟨x, hx⟩ := p.property.2
     rcases Finset.mem_union.mp hx with h | h
     · exact ⟨x.castSucc, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, h, rfl⟩)⟩
     · exact ⟨x.castSucc, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, h, rfl⟩)⟩⟩

lemma embSP_swap {d : ℕ} (p : SP d) : embSP (spSwap p) = spSwap (embSP p) := by
  apply Subtype.ext; apply Prod.ext <;> rfl

lemma embSP_mono {d : ℕ} {p q : SP d} (h1 : p.val.1 ⊆ q.val.1) (h2 : p.val.2 ⊆ q.val.2) :
    (embSP p).val.1 ⊆ (embSP q).val.1 ∧ (embSP p).val.2 ⊆ (embSP q).val.2 :=
  ⟨Finset.image_subset_image h1, Finset.image_subset_image h2⟩

theorem ky_fan_odd : ∀ (d : ℕ), 0 < d →
    ∀ (lam : SP d → ℤ),
      (∀ p, lam p ≠ 0) →
      (∀ p, lam (spSwap p) = -lam p) →
      (∀ p q : SP d, p.val.1 ⊆ q.val.1 → p.val.2 ⊆ q.val.2 → lam p ≠ -lam q) →
      Odd (Finset.univ.filter (fun σ : SChain d => IsAlt true (chainLabels lam σ) d)).card := by
  intro d
  induction d with
  | zero => intro h0; omega
  | succ n ih =>
    cases n with
    | zero =>

      intro _ lam hnz hanti _
      let p0 : SP 1 := ⟨({0}, ∅), by simp, by simp⟩
      have hcard_all : ∀ σ : SChain 1,
          IsAlt true (chainLabels lam σ) 1 ↔ 0 < lam (pref σ 0) := by
        intro σ
        have himg : chainLabels lam σ = {lam (pref σ 0)} := by
          ext z; simp [chainLabels, Fin.eq_zero]
        rw [himg]
        constructor
        · rintro ⟨_, f, hmem, _, hsgn⟩
          have hf0 : f 0 = lam (pref σ 0) := Finset.mem_singleton.mp (hmem 0)
          have h1 := hsgn 0
          rw [hf0] at h1; simpa [altBool] using h1
        · intro hpos
          refine ⟨Finset.card_singleton _, fun _ => lam (pref σ 0), fun _ => Finset.mem_singleton_self _,
            fun i j hij => by omega, fun i => by simp [Fin.eq_zero i, altBool, hpos]⟩
      let σT : SChain 1 := (1, fun _ => true)
      let σF : SChain 1 := (1, fun _ => false)
      have hne_TF : σT ≠ σF := by
        intro h; have := congrFun (congrArg Prod.snd h) 0; simp [σT, σF] at this
      have hall : ∀ σ : SChain 1, σ = σT ∨ σ = σF := by
        intro σ
        have h1 : σ.1 = 1 := Subsingleton.elim _ _
        cases hb : σ.2 0
        · right; apply Prod.ext h1; funext i; rw [Fin.eq_zero i, hb]
        · left; apply Prod.ext h1; funext i; rw [Fin.eq_zero i, hb]
      have hneg : σF = negChain σT := by
        apply Prod.ext rfl; funext i; simp [σF, σT, negChain]
      have hlam_neg : lam (pref σF 0) = -lam (pref σT 0) := by
        rw [hneg, pref_negChain, hanti]
      have hnzT : lam (pref σT 0) ≠ 0 := hnz _
      by_cases hpos : 0 < lam (pref σT 0)
      · have hflt : Finset.univ.filter (fun σ : SChain 1 => IsAlt true (chainLabels lam σ) 1) = {σT} := by
          ext σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hcard_all]
          rcases hall σ with rfl | rfl
          · simp [hpos]
          · exact ⟨fun h => by omega, fun h => (hne_TF h.symm).elim⟩
        rw [hflt, Finset.card_singleton]; exact odd_one
      · have hposF : 0 < lam (pref σF 0) := by omega
        have hflt : Finset.univ.filter (fun σ : SChain 1 => IsAlt true (chainLabels lam σ) 1) = {σF} := by
          ext σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hcard_all]
          rcases hall σ with rfl | rfl
          · exact ⟨fun h => (hpos h).elim, fun h => (hne_TF h).elim⟩
          · simp [hposF]
        rw [hflt, Finset.card_singleton]; exact odd_one
    | succ m =>

      let n := m + 1
      intro _ lam hnz hanti hnoop
      let inNorth : SChain (n + 1) → Bool := fun σ => σ.2 (σ.1.symm (Fin.last n))
      let Hpos : Finset (SChain (n + 1)) := Finset.univ.filter (fun σ => inNorth σ = true)

      let isGood : SChain (n + 1) × Fin (n + 1) → Prop := fun sr =>
        IsAlt true ((Finset.univ.erase sr.2).image (fun i => lam (pref sr.1 i))) n
      let isBdry : SChain (n + 1) × Fin (n + 1) → Prop := fun sr =>
        sr.2 = Fin.last n ∧ sr.1.1 (Fin.last n) = Fin.last n
      let AllGood : Finset (SChain (n + 1) × Fin (n + 1)) :=
        (Hpos ×ˢ (Finset.univ : Finset (Fin (n + 1)))).filter isGood
      let IntGood := AllGood.filter (fun sr => ¬ isBdry sr)
      let BdryGood := AllGood.filter isBdry

      let mate : SChain (n + 1) × Fin (n + 1) → SChain (n + 1) × Fin (n + 1) := fun sr =>
        if hlt : sr.2.val < n then
          let r' : Fin (n + 1) := ⟨sr.2.val + 1, by omega⟩
          let sw := Equiv.swap sr.2 r'
          ((sr.1.1 * sw, sr.1.2 ∘ sw), sr.2)
        else
          ((sr.1.1, Function.update sr.1.2 (Fin.last n) (!(sr.1.2 (Fin.last n)))), sr.2)
      have hmate_pref : ∀ (sr : SChain (n + 1) × Fin (n + 1)) (i : Fin (n + 1)),
          i ≠ sr.2 → pref (mate sr).1 i = pref sr.1 i := by
        intro ⟨σ, r⟩ i hi
        dsimp only at hi
        dsimp only [mate]
        split_ifs with hlt
        · let r' : Fin (n + 1) := ⟨r.val + 1, by omega⟩
          have hr'_val : r'.val = r.val + 1 := rfl
          let sw := Equiv.swap r r'
          have hine : i.val ≠ r.val := fun h => hi (Fin.ext h)
          apply Subtype.ext; apply Prod.ext <;>
          · ext x; simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨j, ⟨hjle, hjb⟩, rfl⟩
              refine ⟨sw j, ⟨?_, hjb⟩, rfl⟩
              by_cases hjr : j = r
              · subst hjr; rw [Equiv.swap_apply_left]; omega
              · by_cases hjr' : j = r'
                · subst hjr'; rw [Equiv.swap_apply_right]; omega
                · rw [Equiv.swap_apply_of_ne_of_ne hjr hjr']; exact hjle
            · rintro ⟨j, ⟨hjle, hjb⟩, rfl⟩
              have hsw2 : sw (sw j) = j := Equiv.swap_apply_self r r' j
              refine ⟨sw j, ⟨?_, by change σ.2 (sw (sw j)) = _; rw [hsw2]; exact hjb⟩,
                by change σ.1 (sw (sw j)) = σ.1 j; rw [hsw2]⟩
              by_cases hjr : j = r
              · subst hjr; rw [Equiv.swap_apply_left]; omega
              · by_cases hjr' : j = r'
                · subst hjr'; rw [Equiv.swap_apply_right]; omega
                · rw [Equiv.swap_apply_of_ne_of_ne hjr hjr']; exact hjle
        · have hr_last : r = Fin.last n := Fin.ext (by simp; have := r.isLt; omega)
          have hine : i.val ≠ r.val := fun h => hi (Fin.ext h)
          have hilt : i.val < n := by have := i.isLt; have := r.isLt; omega
          apply Subtype.ext; apply Prod.ext <;>
          · ext x; simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨j, ⟨hjle, hjb⟩, rfl⟩
              refine ⟨j, ⟨hjle, ?_⟩, rfl⟩
              have hjne : j ≠ Fin.last n := by intro heq; subst heq; simp at hjle; omega
              simpa [Function.update, hjne] using hjb
            · rintro ⟨j, ⟨hjle, hjb⟩, rfl⟩
              refine ⟨j, ⟨hjle, ?_⟩, rfl⟩
              have hjne : j ≠ Fin.last n := by intro heq; subst heq; simp at hjle; omega
              simpa [Function.update, hjne] using hjb
      have hmate_north : ∀ sr : SChain (n + 1) × Fin (n + 1), ¬ isBdry sr →
          inNorth (mate sr).1 = inNorth sr.1 := by
        intro ⟨σ, r⟩ hnb
        dsimp only [mate, inNorth]
        split_ifs with hlt
        · simp [Equiv.Perm.mul_def]
        · have hr_last : r = Fin.last n := Fin.ext (by simp; have := r.isLt; omega)
          have hne_last : σ.1 (Fin.last n) ≠ Fin.last n := fun h => hnb ⟨hr_last, h⟩
          have hsymm_ne : σ.1.symm (Fin.last n) ≠ Fin.last n := by
            intro h; apply hne_last
            calc σ.1 (Fin.last n) = σ.1 (σ.1.symm (Fin.last n)) := congrArg σ.1 h.symm
              _ = Fin.last n := σ.1.apply_symm_apply _
          dsimp only
          rw [Function.update_of_ne hsymm_ne]
      have hmate_inv : ∀ sr : SChain (n + 1) × Fin (n + 1), mate (mate sr) = sr := by
        intro ⟨σ, r⟩
        dsimp only [mate]
        split_ifs with hlt
        · refine Prod.ext (Prod.ext ?_ ?_) rfl
          · ext x; simp [Equiv.Perm.mul_def]
          · funext x; change σ.2 (Equiv.swap r ⟨r.val + 1, _⟩ (Equiv.swap r ⟨r.val + 1, _⟩ x)) = σ.2 x
            rw [Equiv.swap_apply_self]
        · refine Prod.ext (Prod.ext rfl ?_) rfl
          funext x
          by_cases hx : x = Fin.last n
          · subst hx; simp [Function.update]
          · simp [Function.update, hx]
      have hmate_ne : ∀ sr : SChain (n + 1) × Fin (n + 1), mate sr ≠ sr := by
        intro ⟨σ, r⟩ h
        dsimp only [mate] at h
        split_ifs at h with hlt
        · let r' : Fin (n + 1) := ⟨r.val + 1, by omega⟩
          have h1 := congrArg (fun p => p.1.1 r) h
          simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left] at h1
          have := σ.1.injective h1
          have : r'.val = r.val := congrArg Fin.val this
          simp [r'] at this
        · have h1 := congrArg (fun p => p.1.2 (Fin.last n)) h
          simp only [Function.update_self] at h1
          cases hb : σ.2 (Fin.last n) <;> simp [hb] at h1
      have hmate_nb : ∀ sr : SChain (n + 1) × Fin (n + 1), ¬ isBdry sr → ¬ isBdry (mate sr) := by
        intro ⟨σ, r⟩ hnb
        dsimp only [mate, isBdry]
        split_ifs with hlt
        · rintro ⟨hr, _⟩; dsimp only at hr; rw [hr] at hlt; simp at hlt
        · exact hnb
      have hInt_even : Even IntGood.card := by
        apply even_card_of_involution IntGood mate
        · intro sr hsr
          simp only [IntGood, AllGood, Finset.mem_filter, Finset.mem_product, Hpos,
            Finset.mem_univ, true_and, and_true] at hsr ⊢
          refine ⟨⟨?_, ?_⟩, hmate_nb sr hsr.2⟩
          · rw [hmate_north sr hsr.2]; exact hsr.1.1
          · have hreq : (mate sr).2 = sr.2 := by dsimp only [mate]; split_ifs <;> rfl
            have himg : (Finset.univ.erase (mate sr).2).image (fun i => lam (pref (mate sr).1 i)) =
                (Finset.univ.erase sr.2).image (fun i => lam (pref sr.1 i)) := by
              rw [hreq]
              apply Finset.image_congr
              intro i hi
              dsimp only
              rw [hmate_pref sr i (Finset.mem_erase.mp hi).1]
            change IsAlt true _ n
            rw [himg]; exact hsr.1.2
        · intro sr _; exact hmate_inv sr
        · intro sr _; exact hmate_ne sr

      let lam' : SP n → ℤ := fun p => lam (embSP p)
      have hBdry_odd : Odd BdryGood.card := by
        have hIH := ih (Nat.succ_pos m) lam' (fun p => hnz (embSP p))
          (fun p => by simp [lam', embSP_swap, hanti])
          (fun p q h1 h2 => hnoop (embSP p) (embSP q) (embSP_mono h1 h2).1 (embSP_mono h1 h2).2)

        let liftPerm : Equiv.Perm (Fin n) → Equiv.Perm (Fin (n + 1)) := fun π =>
          { toFun := Fin.lastCases (Fin.last n) (fun i => (π i).castSucc)
            invFun := Fin.lastCases (Fin.last n) (fun i => (π.symm i).castSucc)
            left_inv := fun x => by
              refine Fin.lastCases ?_ ?_ x
              · simp
              · intro i; simp
            right_inv := fun x => by
              refine Fin.lastCases ?_ ?_ x
              · simp
              · intro i; simp }
        let liftChain : SChain n → SChain (n + 1) := fun τ =>
          (liftPerm τ.1, Fin.lastCases true τ.2)
        have hlift_pref : ∀ (τ : SChain n) (i : Fin n),
            pref (liftChain τ) i.castSucc = embSP (pref τ i) := by
          intro τ i
          apply Subtype.ext; apply Prod.ext <;>
          · ext x; simp only [pref, embSP, liftChain, liftPerm, Finset.mem_image, Finset.mem_filter,
              Finset.mem_univ, true_and, Equiv.coe_fn_mk]
            constructor
            · rintro ⟨j, ⟨hjle, hjb⟩, rfl⟩
              have hjlt : j.val < n := by simp at hjle; omega
              let j' : Fin n := ⟨j.val, hjlt⟩
              have hj_eq : j = j'.castSucc := Fin.ext rfl
              rw [hj_eq] at hjb ⊢
              simp only [Fin.lastCases_castSucc] at hjb ⊢
              exact ⟨τ.1 j', ⟨j', ⟨by change j'.val ≤ i.val; simpa [j'] using hjle, hjb⟩, rfl⟩, rfl⟩
            · rintro ⟨_, ⟨j', ⟨hjle, hjb⟩, rfl⟩, rfl⟩
              refine ⟨j'.castSucc, ⟨by simpa using hjle, by simp [hjb]⟩, by simp⟩
        have hBdry_eq : BdryGood.card =
            (Finset.univ.filter (fun τ : SChain n => IsAlt true (chainLabels lam' τ) n)).card := by
          symm
          apply Finset.card_bij (fun τ _ => (liftChain τ, Fin.last n))
          · intro τ hτ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
            simp only [BdryGood, AllGood, Hpos, Finset.mem_filter, Finset.mem_product,
              Finset.mem_univ, true_and, and_true, isBdry, inNorth]
            refine ⟨⟨?_, ?_⟩, by simp [liftChain, liftPerm]⟩
            · have hs : (liftPerm τ.1).symm (Fin.last n) = Fin.last n := by simp [liftPerm]
              dsimp only [liftChain]; rw [hs]; simp
            · have himg : (Finset.univ.erase (Fin.last n)).image (fun i => lam (pref (liftChain τ) i)) =
                  chainLabels lam' τ := by
                ext z; simp only [chainLabels, lam', Finset.mem_image, Finset.mem_erase,
                  Finset.mem_univ, true_and, and_true]
                constructor
                · rintro ⟨i, hine, rfl⟩
                  let i' : Fin n := ⟨i.val, lt_of_le_of_ne (Fin.is_le i) (fun h => hine (Fin.ext h))⟩
                  have hi_eq : i = i'.castSucc := Fin.ext rfl
                  exact ⟨i', by rw [hi_eq, hlift_pref]⟩
                · rintro ⟨i', rfl⟩
                  exact ⟨i'.castSucc, Fin.castSucc_ne_last i', congrArg lam (hlift_pref τ i')⟩
              change IsAlt true _ n
              rw [himg]; exact hτ
          · intro τ1 _ τ2 _ heq
            have h1 := congrArg Prod.fst heq
            apply Prod.ext
            · ext i
              have := congrArg (fun c => (c.1 i.castSucc).val) h1
              simpa [liftChain, liftPerm] using this
            · funext i
              have := congrArg (fun c => c.2 i.castSucc) h1
              simpa [liftChain] using this
          · intro ⟨σ, r⟩ hsr
            simp only [BdryGood, AllGood, Hpos, Finset.mem_filter, Finset.mem_product,
              Finset.mem_univ, true_and, and_true, isBdry, inNorth] at hsr
            obtain ⟨⟨hnorth, hgood⟩, rfl, hfix⟩ := hsr
            have hfix_symm : σ.1.symm (Fin.last n) = Fin.last n := by
              rw [Equiv.symm_apply_eq]; exact hfix.symm
            have hne_last : ∀ i : Fin n, σ.1 i.castSucc ≠ Fin.last n := fun i h =>
              Fin.castSucc_ne_last i (σ.1.injective (h.trans hfix.symm))
            have hne_last_symm : ∀ i : Fin n, σ.1.symm i.castSucc ≠ Fin.last n := fun i h =>
              Fin.castSucc_ne_last i (σ.1.symm.injective (h.trans hfix_symm.symm))
            let π : Equiv.Perm (Fin n) :=
              { toFun := fun i => ⟨(σ.1 i.castSucc).val, lt_of_le_of_ne (Fin.is_le _) (fun h => hne_last i (Fin.ext h))⟩
                invFun := fun i => ⟨(σ.1.symm i.castSucc).val, lt_of_le_of_ne (Fin.is_le _) (fun h => hne_last_symm i (Fin.ext h))⟩
                left_inv := fun i => by
                  apply Fin.ext; dsimp only
                  have hcast : (⟨(σ.1 i.castSucc).val, lt_of_le_of_ne (Fin.is_le _) (fun h => hne_last i (Fin.ext h))⟩ : Fin n).castSucc = σ.1 i.castSucc := Fin.ext rfl
                  rw [hcast, σ.1.symm_apply_apply]; rfl
                right_inv := fun i => by
                  apply Fin.ext; dsimp only
                  have hcast : (⟨(σ.1.symm i.castSucc).val, lt_of_le_of_ne (Fin.is_le _) (fun h => hne_last_symm i (Fin.ext h))⟩ : Fin n).castSucc = σ.1.symm i.castSucc := Fin.ext rfl
                  rw [hcast, σ.1.apply_symm_apply]; rfl }
            let τ : SChain n := (π, fun i => σ.2 i.castSucc)
            have hlift_eq : liftChain τ = σ := by
              apply Prod.ext
              · ext x
                refine Fin.lastCases ?_ ?_ x
                · simp [liftChain, liftPerm, hfix]
                · intro i; simp [liftChain, liftPerm, τ, π]
              · funext x
                refine Fin.lastCases ?_ ?_ x
                · simp only [liftChain, Fin.lastCases_last]
                  rw [← hfix_symm]; exact hnorth.symm
                · intro i; simp [liftChain, τ]
            refine ⟨τ, ?_, by rw [hlift_eq]⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have himg : chainLabels lam' τ = (Finset.univ.erase (Fin.last n)).image (fun i => lam (pref σ i)) := by
              rw [← hlift_eq]
              ext z; simp only [chainLabels, lam', Finset.mem_image, Finset.mem_erase,
                Finset.mem_univ, true_and, and_true]
              constructor
              · rintro ⟨i', rfl⟩
                exact ⟨i'.castSucc, Fin.castSucc_ne_last i', congrArg lam (hlift_pref τ i')⟩
              · rintro ⟨i, hine, rfl⟩
                let i' : Fin n := ⟨i.val, lt_of_le_of_ne (Fin.is_le i) (fun h => hine (Fin.ext h))⟩
                have hi_eq : i = i'.castSucc := Fin.ext rfl
                exact ⟨i', by rw [hi_eq, hlift_pref]⟩
            rw [himg]; exact hgood
        rw [hBdry_eq]; exact hIH

      have hAll_odd : Odd AllGood.card := by
        have hpart : AllGood.card = BdryGood.card + IntGood.card := by
          have hu : BdryGood ∪ IntGood = AllGood := by
            ext x; simp only [BdryGood, IntGood, Finset.mem_union, Finset.mem_filter]; tauto
          have hd : Disjoint BdryGood IntGood := by
            rw [Finset.disjoint_left]; intro x h1 h2
            exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
          rw [← hu, Finset.card_union_of_disjoint hd]
        rw [hpart]; exact hBdry_odd.add_even hInt_even

      have hfiber_sum : AllGood.card = ∑ σ ∈ Hpos,
          (Finset.univ.filter (fun r : Fin (n + 1) => isGood (σ, r))).card := by
        have h1 : AllGood = Hpos.biUnion (fun σ =>
            (Finset.univ.filter (fun r : Fin (n + 1) => isGood (σ, r))).image (fun r => (σ, r))) := by
          ext ⟨σ, r⟩
          simp only [AllGood, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
            and_true, Finset.mem_biUnion, Finset.mem_image]
          constructor
          · rintro ⟨hσ, hg⟩; exact ⟨σ, hσ, r, hg, rfl⟩
          · rintro ⟨σ', hσ', r', hg', heq⟩
            rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact ⟨hσ', hg'⟩
        rw [h1, Finset.card_biUnion]
        · apply Finset.sum_congr rfl
          intro σ _
          exact Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)
        · intro σ1 _ σ2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          obtain ⟨r1, _, rfl⟩ := Finset.mem_image.mp hx1
          obtain ⟨r2, _, heq⟩ := Finset.mem_image.mp hx2
          exact hne (Prod.mk.inj heq).1.symm

      have hsum_odd_iff : ∀ (s : Finset (SChain (n + 1))) (g : SChain (n + 1) → ℕ),
          Odd (∑ a ∈ s, g a) ↔ Odd (s.filter (fun a => Odd (g a))).card := by
        intro s g
        induction s using Finset.cons_induction with
        | empty => simp
        | cons a s ha ih =>
          rw [Finset.sum_cons, Finset.filter_cons]
          by_cases ho : Odd (g a)
          · rw [if_pos ho, Finset.card_cons]
            constructor
            · intro h
              have hs_even : Even (∑ x ∈ s, g x) := by
                rcases ho with ⟨k1, hk1⟩; rcases h with ⟨k2, hk2⟩
                exact ⟨k2 - k1, by omega⟩
              have hc_even : Even (s.filter (fun x => Odd (g x))).card :=
                Nat.not_odd_iff_even.mp (fun ho2 => Nat.not_even_iff_odd.mpr (ih.mpr ho2) hs_even)
              rcases hc_even with ⟨k, hk⟩; exact ⟨k, by omega⟩
            · intro h
              have hc_even : Even (s.filter (fun x => Odd (g x))).card := by
                rcases h with ⟨k, hk⟩; exact ⟨k, by omega⟩
              have hs_even : Even (∑ x ∈ s, g x) :=
                Nat.not_odd_iff_even.mp (fun ho2 => Nat.not_even_iff_odd.mpr (ih.mp ho2) hc_even)
              exact ho.add_even hs_even
          · rw [if_neg ho]
            have he : Even (g a) := Nat.not_odd_iff_even.mp ho
            rw [← ih]
            constructor
            · intro h
              rcases he with ⟨k1, hk1⟩; rcases h with ⟨k2, hk2⟩
              exact ⟨k2 - k1, by omega⟩
            · intro h; exact he.add_odd h
      have hHpos_odd : Odd (Hpos.filter (fun σ =>
          IsAlt true (chainLabels lam σ) (n + 1) ∨ IsAlt false (chainLabels lam σ) (n + 1))).card := by
        have h1 := (hsum_odd_iff Hpos (fun σ => (Finset.univ.filter (fun r => isGood (σ, r))).card)).mp
          (hfiber_sum ▸ hAll_odd)
        have hflt_eq : Hpos.filter (fun σ => Odd (Finset.univ.filter (fun r => isGood (σ, r))).card) =
            Hpos.filter (fun σ => IsAlt true (chainLabels lam σ) (n + 1) ∨ IsAlt false (chainLabels lam σ) (n + 1)) := by
          apply Finset.filter_congr
          intro σ _
          apply good_facets_parity (fun i => lam (pref σ i)) (fun i => hnz _)
          intro i j
          rcases le_total i j with hij | hji
          · exact hnoop _ _ (pref_mono σ hij).1 (pref_mono σ hij).2
          · intro heq
            exact hnoop _ _ (pref_mono σ hji).1 (pref_mono σ hji).2 (by omega)
        rwa [← hflt_eq]

      let PosAll := Finset.univ.filter (fun σ : SChain (n + 1) => IsAlt true (chainLabels lam σ) (n + 1))
      let PosN := Hpos.filter (fun σ => IsAlt true (chainLabels lam σ) (n + 1))
      let NegN := Hpos.filter (fun σ => IsAlt false (chainLabels lam σ) (n + 1))
      let PosS := (Finset.univ.filter (fun σ : SChain (n + 1) => inNorth σ = false)).filter
        (fun σ => IsAlt true (chainLabels lam σ) (n + 1))
      have hdisj_PN : Disjoint PosN NegN := by
        rw [Finset.disjoint_left]
        intro σ h1 h2
        simp only [PosN, NegN, Finset.mem_filter] at h1 h2
        obtain ⟨_, f1, hf1m, hf1i, hf1s⟩ := h1.2
        obtain ⟨_, f2, hf2m, hf2i, hf2s⟩ := h2.2
        have hf1_inj : Function.Injective f1 := by
          intro a b hab; by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact ne_of_lt (hf1i a b h) (congrArg Int.natAbs hab)
          · exact ne_of_gt (hf1i b a h) (congrArg Int.natAbs hab)
        have hf2_inj : Function.Injective f2 := by
          intro a b hab; by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact ne_of_lt (hf2i a b h) (congrArg Int.natAbs hab)
          · exact ne_of_gt (hf2i b a h) (congrArg Int.natAbs hab)
        have h1img : Finset.univ.image f1 = chainLabels lam σ :=
          Finset.eq_of_subset_of_card_le
            (fun z hz => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz; exact hf1m i)
            (by rw [Finset.card_image_of_injective _ hf1_inj, Finset.card_fin, h1.2.1])
        have h2img : Finset.univ.image f2 = chainLabels lam σ :=
          Finset.eq_of_subset_of_card_le
            (fun z hz => by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz; exact hf2m i)
            (by rw [Finset.card_image_of_injective _ hf2_inj, Finset.card_fin, h2.2.1])
        have heq := sort_natAbs_unique h1img h2img hf1i hf2i
        have hs1 := hf1s 0
        have hs2 := hf2s 0
        rw [heq, hs2] at hs1; simp [altBool] at hs1
      have hNegN_eq_PosS : NegN.card = PosS.card := by
        apply Finset.card_bij (fun σ _ => negChain σ)
        · intro σ hσ
          simp only [NegN, PosS, Hpos, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
          refine ⟨by simp [inNorth, negChain, hσ.1], ?_⟩
          rw [chainLabels_neg lam hanti σ, isAlt_neg_iff true _ _ (fun z hz => by
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz; exact hnz _)]
          exact hσ.2
        · intro a _ b _ hab; rw [← negChain_neg a, ← negChain_neg b, hab]
        · intro σ hσ
          simp only [NegN, PosS, Hpos, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
          refine ⟨negChain σ, ⟨by simp [inNorth, negChain, hσ.1], ?_⟩, negChain_neg σ⟩
          rw [chainLabels_neg lam hanti σ, isAlt_neg_iff false _ _ (fun z hz => by
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz; exact hnz _)]
          exact hσ.2
      have hPosAll_eq : PosAll.card = PosN.card + PosS.card := by
        have hun : PosAll = PosN ∪ PosS := by
          ext σ; simp only [PosAll, PosN, PosS, Hpos, Finset.mem_union, Finset.mem_filter,
            Finset.mem_univ, true_and]
          cases inNorth σ <;> simp
        have hdj : Disjoint PosN PosS := by
          rw [Finset.disjoint_left]; intro σ h1 h2
          simp only [PosN, PosS, Hpos, Finset.mem_filter] at h1 h2
          rw [h1.1.2] at h2; exact Bool.noConfusion h2.1.2
        rw [hun, Finset.card_union_of_disjoint hdj]
      have hUnion_eq : (Hpos.filter (fun σ =>
          IsAlt true (chainLabels lam σ) (n + 1) ∨ IsAlt false (chainLabels lam σ) (n + 1))).card =
          PosN.card + NegN.card := by
        have hun : Hpos.filter (fun σ =>
            IsAlt true (chainLabels lam σ) (n + 1) ∨ IsAlt false (chainLabels lam σ) (n + 1)) =
            PosN ∪ NegN := by
          ext σ; simp only [PosN, NegN, Finset.mem_union, Finset.mem_filter]; tauto
        rw [hun, Finset.card_union_of_disjoint hdisj_PN]
      rw [hPosAll_eq, ← hNegN_eq_PosS, ← hUnion_eq]
      exact hHpos_odd

theorem octahedral_tucker {d : ℕ} (hd : 0 < d) (lam : SP d → ℤ)
    (hnz : ∀ p, lam p ≠ 0)
    (hbnd : ∀ p, (lam p).natAbs < d)
    (hanti : ∀ p, lam (spSwap p) = -lam p) :
    ∃ p q : SP d, p.val.1 ⊆ q.val.1 ∧ p.val.2 ⊆ q.val.2 ∧ lam p = -lam q := by
  by_contra hno
  push Not at hno
  have hodd := ky_fan_odd d hd lam hnz hanti hno
  have hne : (Finset.univ.filter (fun σ : SChain d => IsAlt true (chainLabels lam σ) d)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he; rw [he, Finset.card_empty] at hodd; exact Nat.not_odd_zero hodd
  obtain ⟨σ, hσ⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  obtain ⟨_, f, hf_mem, hf_inc, _⟩ := hσ

  have hge : ∀ i : Fin d, i.val + 1 ≤ (f i).natAbs := by
    intro i
    induction hi : i.val using Nat.strong_induction_on generalizing i with
    | ind k ih =>
      obtain ⟨j, _, hfj⟩ := Finset.mem_image.mp (hf_mem i)
      have hpos : 1 ≤ (f i).natAbs := Int.natAbs_pos.mpr (hfj ▸ hnz (pref σ j))
      cases k with
      | zero => exact hpos
      | succ k' =>
        let i' : Fin d := ⟨k', by omega⟩
        have hlt : i' < i := by change k' < i.val; omega
        have hprev := ih k' (by omega) i' rfl
        have hstep := hf_inc i' i hlt
        omega
  have hlast := hge ⟨d - 1, by omega⟩
  dsimp only at hlast
  obtain ⟨j, _, hfj⟩ := Finset.mem_image.mp (hf_mem ⟨d - 1, by omega⟩)
  have hlt := hbnd (pref σ j)
  rw [hfj] at hlt
  omega

def stahlStep {d k : ℕ} (hk : 2 ≤ k) (hd : 2 * k ≤ d)
    (j : { s : Finset (Fin d) // s.card = k }) :
    { s : Finset (Fin (d - 2)) // s.card = k - 1 } := by
  classical
  let u : Fin d := ⟨d - 2, by omega⟩
  let v : Fin d := ⟨d - 1, by omega⟩
  let P : Finset (Fin d) := Finset.univ.filter (fun x : Fin d => x.val < d - 2)
  let emb : Fin (d - 2) ↪ Fin d := ⟨fun x => ⟨x.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
  let proj : Finset (Fin d) → Finset (Fin (d - 2)) := fun s =>
    Finset.univ.filter (fun x : Fin (d - 2) => emb x ∈ s)
  have hproj_card : ∀ s : Finset (Fin d), s ⊆ P → (proj s).card = s.card := by
    intro s hs
    apply Finset.card_bij (fun x _ => emb x)
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro a _ b _ h; exact emb.injective h
    · intro y hy
      have hylt : y.val < d - 2 := (Finset.mem_filter.mp (hs hy)).2
      exact ⟨⟨y.val, hylt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, Fin.ext rfl⟩
  let jP : Finset (Fin d) := j.val ∩ P
  have hjP_sub : jP ⊆ P := Finset.inter_subset_right
  have hj_split : j.val \ P ⊆ {u, v} := by
    intro x hx
    have hge : d - 2 ≤ x.val := not_lt.mp (by simpa [P] using (Finset.mem_sdiff.mp hx).2)
    have hlt : x.val < d := x.isLt
    have : x.val = d - 2 ∨ x.val = d - 1 := by omega
    rcases this with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Fin.ext (by simpa [u] using h)))
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Fin.ext (by simpa [v] using h)))
  have huv_ne : u ≠ v := fun h => by have := congrArg Fin.val h; simp [u, v] at this; omega
  have hcard_jP : jP.card = k ∨ jP.card = k - 1 ∨ jP.card = k - 2 := by
    have h1 : jP.card + (j.val \ P).card = k := by
      have hjk := j.property
      have hsum := Finset.card_inter_add_card_sdiff j.val P
      change (j.val ∩ P).card + (j.val \ P).card = k
      omega
    have h2 : (j.val \ P).card ≤ 2 := by
      calc (j.val \ P).card ≤ ({u, v} : Finset (Fin d)).card := Finset.card_le_card hj_split
        _ = 2 := Finset.card_pair huv_ne
    omega
  by_cases h1 : jP.card = k
  ·
    have hne : jP.Nonempty := Finset.card_pos.mp (by omega)
    let s' := jP.erase (jP.max' hne)
    refine ⟨proj s', ?_⟩
    rw [hproj_card s' (Finset.Subset.trans (Finset.erase_subset _ _) hjP_sub),
      Finset.card_erase_of_mem (Finset.max'_mem jP hne), h1]
  · by_cases h2 : jP.card = k - 1
    ·
      exact ⟨proj jP, by rw [hproj_card jP hjP_sub, h2]⟩
    ·
      have h3 : jP.card = k - 2 := by omega
      have hP_card : P.card = d - 2 := by
        have hbij : P.card = (Finset.univ : Finset (Fin (d - 2))).card := by
          symm
          apply Finset.card_bij (fun x _ => emb x)
          · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.isLt⟩
          · intro a _ b _ h; exact emb.injective h
          · intro y hy; exact ⟨⟨y.val, (Finset.mem_filter.mp hy).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
        rw [hbij, Finset.card_fin]
      have hrem_ne : (P \ j.val).Nonempty := by
        apply Finset.card_pos.mp
        have hs : P \ j.val = P \ jP := by ext x; simp [jP]
        rw [hs, Finset.card_sdiff, Finset.inter_eq_left.mpr hjP_sub, hP_card, h3]; omega
      let w := (P \ j.val).max' hrem_ne
      have hw_mem : w ∈ P \ j.val := Finset.max'_mem _ hrem_ne
      have hw_not : w ∉ jP := fun h => (Finset.mem_sdiff.mp hw_mem).2 (Finset.mem_inter.mp h).1
      let s' := insert w jP
      refine ⟨proj s', ?_⟩
      rw [hproj_card s' (Finset.insert_subset (Finset.mem_sdiff.mp hw_mem).1 hjP_sub),
        Finset.card_insert_of_notMem hw_not, h3]; omega

lemma stahlStep_disjoint {d k : ℕ} (hk : 2 ≤ k) (hd : 2 * k ≤ d)
    (i j : { s : Finset (Fin d) // s.card = k }) (hdisj : Disjoint i.val j.val) :
    Disjoint (stahlStep hk hd i).val (stahlStep hk hd j).val := by
  classical
  let u : Fin d := ⟨d - 2, by omega⟩
  let v : Fin d := ⟨d - 1, by omega⟩
  let P : Finset (Fin d) := Finset.univ.filter (fun x : Fin d => x.val < d - 2)
  let emb : Fin (d - 2) ↪ Fin d := ⟨fun x => ⟨x.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

  have hmem_emb : ∀ (a : { s : Finset (Fin d) // s.card = k }) (x : Fin (d - 2)),
      x ∈ (stahlStep hk hd a).val →
      (emb x ∈ a.val ∧
        ∀ hkP : (a.val ∩ P).card = k,
          emb x ≠ (a.val ∩ P).max' (Finset.card_pos.mp (by omega))) ∨
      ((a.val ∩ P).card = k - 2 ∧ u ∈ a.val ∧ v ∈ a.val ∧
        ∃ hne : (P \ a.val).Nonempty, emb x = (P \ a.val).max' hne) := by
    intro a x hx
    dsimp only [stahlStep] at hx
    split_ifs at hx with h1 h2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hx
      left
      exact ⟨(Finset.mem_inter.mp hx.2).1, fun _ => hx.1⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      left
      exact ⟨(Finset.mem_inter.mp hx).1, fun hc => (h1 hc).elim⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hx
      rcases hx with heq | hmem
      · right
        have hsplit : a.val \ P ⊆ {u, v} := by
          intro y hy
          have hge : d - 2 ≤ y.val := not_lt.mp (by simpa [P] using (Finset.mem_sdiff.mp hy).2)
          have : y.val = d - 2 ∨ y.val = d - 1 := by omega
          rcases this with h | h
          · exact Finset.mem_insert.mpr (Or.inl (Fin.ext h))
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Fin.ext h))
        have huv_ne : u ≠ v := fun h => by have := congrArg Fin.val h; simp [u, v] at this; omega
        have hsum : (a.val ∩ P).card + (a.val \ P).card = k := by
          have hak := a.property
          have h0 := Finset.card_inter_add_card_sdiff a.val P
          omega
        have hle2 : (a.val \ P).card ≤ 2 :=
          le_trans (Finset.card_le_card hsplit) (by rw [Finset.card_pair huv_ne])
        have h1' : (a.val ∩ P).card ≠ k := h1
        have h2' : (a.val ∩ P).card ≠ k - 1 := h2
        have h3 : (a.val ∩ P).card = k - 2 := by omega
        have h2eq : (a.val \ P).card = 2 := by omega
        have heq_uv : a.val \ P = {u, v} :=
          Finset.eq_of_subset_of_card_le hsplit (by rw [Finset.card_pair huv_ne, h2eq])
        have hu : u ∈ a.val := (Finset.mem_sdiff.mp (heq_uv ▸ Finset.mem_insert_self u {v})).1
        have hv : v ∈ a.val := (Finset.mem_sdiff.mp (heq_uv ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v))).1
        exact ⟨h3, hu, hv, ⟨_, heq⟩⟩
      · left
        exact ⟨(Finset.mem_inter.mp hmem).1, fun hc => (h1 hc).elim⟩
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rcases hmem_emb i x hxi with ⟨hi_mem, hi_notmax⟩ | ⟨hi3, hiu, hiv, hne_i, hi_max⟩
  · rcases hmem_emb j x hxj with ⟨hj_mem, _⟩ | ⟨hj3, hju, hjv, hne_j, hj_max⟩
    · exact Finset.disjoint_left.mp hdisj hi_mem hj_mem
    ·
      have hi_sub_P : i.val ⊆ P := by
        intro y hy
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
        have hyu : y ≠ u := fun h => Finset.disjoint_left.mp hdisj (h ▸ hy) hju
        have hyv : y ≠ v := fun h => Finset.disjoint_left.mp hdisj (h ▸ hy) hjv
        have h1 : y.val ≠ d - 2 := fun h => hyu (Fin.ext (by simpa [u] using h))
        have h2 : y.val ≠ d - 1 := fun h => hyv (Fin.ext (by simpa [v] using h))
        have hlt := y.isLt
        omega
      have hi_inter : i.val ∩ P = i.val := Finset.inter_eq_left.mpr hi_sub_P
      have hi_k : (i.val ∩ P).card = k := by rw [hi_inter, i.property]
      have hne_max := hi_notmax hi_k

      have hsub_sdiff : i.val ∩ P ⊆ P \ j.val := by
        intro y hy
        refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hy).2, ?_⟩
        exact fun hyj => Finset.disjoint_left.mp hdisj (Finset.mem_inter.mp hy).1 hyj
      have hmax_le : (i.val ∩ P).max' (Finset.card_pos.mp (by omega)) ≤ emb x := by
        rw [hj_max]
        exact Finset.le_max' (P \ j.val) _ (hsub_sdiff (Finset.max'_mem _ _))
      have hx_le : emb x ≤ (i.val ∩ P).max' (Finset.card_pos.mp (by omega)) :=
        Finset.le_max' (i.val ∩ P) (emb x) (Finset.mem_inter.mpr ⟨hi_mem, hi_sub_P hi_mem⟩)
      exact hne_max (le_antisymm hx_le hmax_le)
  · rcases hmem_emb j x hxj with ⟨hj_mem, hj_notmax⟩ | ⟨_, hju, _, _, _⟩
    · have hj_sub_P : j.val ⊆ P := by
        intro y hy
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
        have hyu : y ≠ u := fun h => Finset.disjoint_left.mp hdisj hiu (h ▸ hy)
        have hyv : y ≠ v := fun h => Finset.disjoint_left.mp hdisj hiv (h ▸ hy)
        have h1 : y.val ≠ d - 2 := fun h => hyu (Fin.ext (by simpa [u] using h))
        have h2 : y.val ≠ d - 1 := fun h => hyv (Fin.ext (by simpa [v] using h))
        have hlt := y.isLt
        omega
      have hj_inter : j.val ∩ P = j.val := Finset.inter_eq_left.mpr hj_sub_P
      have hj_k : (j.val ∩ P).card = k := by rw [hj_inter, j.property]
      have hne_max := hj_notmax hj_k
      have hsub_sdiff : j.val ∩ P ⊆ P \ i.val := by
        intro y hy
        refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hy).2, ?_⟩
        exact fun hyi => Finset.disjoint_left.mp hdisj hyi (Finset.mem_inter.mp hy).1
      have hmax_le : (j.val ∩ P).max' (Finset.card_pos.mp (by omega)) ≤ emb x := by
        rw [hi_max]
        exact Finset.le_max' (P \ i.val) _ (hsub_sdiff (Finset.max'_mem _ _))
      have hx_le : emb x ≤ (j.val ∩ P).max' (Finset.card_pos.mp (by omega)) :=
        Finset.le_max' (j.val ∩ P) (emb x) (Finset.mem_inter.mpr ⟨hj_mem, hj_sub_P hj_mem⟩)
      exact hne_max (le_antisymm hx_le hmax_le)
    · exact Finset.disjoint_left.mp hdisj hiu hju

lemma exists_stahl_iter : ∀ (r d k : ℕ), r < k → 2 * k ≤ d →
    ∃ φ : { s : Finset (Fin d) // s.card = k } →
          { s : Finset (Fin (d - 2 * r)) // s.card = k - r },
      ∀ i j, Disjoint i.val j.val → Disjoint (φ i).val (φ j).val := by
  intro r
  induction r with
  | zero =>
    intro d k _ _
    exact ⟨id, fun _ _ h => h⟩
  | succ r ih =>
    intro d k hr hd
    have hk2 : 2 ≤ k := by omega
    obtain ⟨φ', hφ'⟩ := ih (d - 2) (k - 1) (by omega) (by omega)
    have hd_eq : d - 2 - 2 * r = d - 2 * (r + 1) := by omega
    have hk_eq : k - 1 - r = k - (r + 1) := by omega
    refine ⟨fun j =>
      let y := φ' (stahlStep hk2 hd j)
      ⟨y.val.map ⟨Fin.cast hd_eq, Fin.cast_injective hd_eq⟩, by rw [Finset.card_map, y.property, hk_eq]⟩,
      ?_⟩
    intro i j hij
    have h1 := hφ' (stahlStep hk2 hd i) (stahlStep hk2 hd j) (stahlStep_disjoint hk2 hd i j hij)
    exact Finset.disjoint_left.mpr (fun _ h1m h2m => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp h1m
      obtain ⟨b, hb, heq⟩ := Finset.mem_map.mp h2m
      have := Fin.cast_injective hd_eq heq; subst this
      exact Finset.disjoint_left.mp h1 ha hb)

lemma sum_sub_telescope {l : ℕ} (u : Fin (l + 1) → ℕ) (hmono : ∀ i : Fin l, u i.castSucc ≤ u i.succ) :
    Finset.univ.sum (fun i : Fin l => u i.succ - u i.castSucc) = u (Fin.last l) - u 0 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    have ih' := ih (fun i => u i.castSucc) (fun i => hmono i.castSucc)
    change (∑ x : Fin l, (u x.succ.castSucc - u x.castSucc.castSucc)) +
        (u (Fin.last (l + 1)) - u (Fin.last l).castSucc) = u (Fin.last (l + 1)) - u 0
    have h0 : u 0 ≤ u (Fin.last l).castSucc := by
      clear ih ih'
      suffices ∀ m (hm : m ≤ l), u 0 ≤ u ⟨m, by omega⟩ from this l le_rfl
      intro m hm
      induction m with
      | zero => exact le_rfl
      | succ m ihm =>
        exact le_trans (ihm (by omega)) (hmono ⟨m, by omega⟩)
    have hlast := hmono (Fin.last l)
    change u (Fin.last l).castSucc ≤ u (Fin.last (l + 1)) at hlast
    rw [ih']
    change (u (Fin.last l).castSucc - u 0) + (u (Fin.last (l + 1)) - u (Fin.last l).castSucc) =
      u (Fin.last (l + 1)) - u 0
    omega

end PEqualNP.Outside.L_lib_1278_aux

theorem PEqualNP.Outside.L_lib_1278 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (d k : Nat), 0 < k → 2*k ≤ d → d < 3*k →
  let K := {s : Finset (Fin d) // s.card = k}
  let X := Finset K
  let bank := fun (a : Finset (Fin d)) => (Finset.univ : X).filter (fun j => j.val ⊆ a)
  let meets := fun (x : X) => x.Nonempty ∧
    ∀ i ∈ x, ∀ j ∈ x, ¬ Disjoint i.val j.val
  let fit := fun (D : Nat) (f : X → K → Nat) =>
    (∀ x j, f x j ≤ D) ∧ (∀ x j, (∀ i ∈ x, Disjoint i.val j.val) → f x j = D) ∧
    (∀ x j, j ∈ x → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j)
  let pays := fun (f : X → K → Nat) (x : X) (c : Nat) =>
    ∃ (l : Nat) (p : Fin (l+1) → X) (a : Fin l → K),
      p 0 = ∅ ∧ p (Fin.last l) ⊆ x ∧
      (∀ i : Fin l, p i.castSucc ⊆ p i.succ) ∧
      c ≤ Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i))
  (∀ D : Nat, 0 < D → ∀ f, fit D f →
    ∃ a b : Finset (Fin d), Disjoint a b ∧ a ∪ b = Finset.univ ∧
      meets (bank a) ∧ meets (bank b) ∧
      pays f (bank a) (D+(d-2*k+1)/2) ∧ pays f (bank b) (D+(d-2*k)/2)) ∧
  ∀ D : Nat, 0 < D → D ≤ k → ∃ F, fit D F ∧
    ∀ a b : Finset (Fin d), Disjoint a b →
      ∀ u v : Nat, pays F (bank a) u → pays F (bank b) v → u+v ≤ 2*D+(d-2*k)) := by
  classical
  open PEqualNP.Outside.L_lib_1278_aux in
  intro d k hk h2k h3k K X bank meets fit pays
  have hmem_bank : ∀ (S : Finset (Fin d)) (j : K), j ∈ bank S ↔ j.val ⊆ S := by
    intro S j; dsimp only [bank]
    exact (@Finset.mem_filter K (fun j : K => j.val ⊆ S) (fun j => Classical.propDecidable (j.val ⊆ S)) _ j).trans
      ⟨And.right, fun h => ⟨by convert Finset.mem_univ j, h⟩⟩
  constructor
  ·
    intro D hD f hfit
    obtain ⟨hf_le, hf_disj, hf_mem, hf_anti⟩ := hfit

    let hasFall : ℕ → Finset (Fin d) → Prop := fun r S =>
      ∃ (p : Fin (r + 1) → X) (t : Fin r → K),
        p 0 = ∅ ∧ p (Fin.last r) ⊆ bank S ∧
        (∀ i : Fin r, p i.castSucc ⊆ p i.succ) ∧
        (∀ i : Fin r, 0 < f (p i.castSucc) (t i) ∧ f (p i.succ) (t i) = 0)

    let killSet : X → Finset K := fun x => Finset.univ.filter (fun j : K => f x j = 0)
    have hkill_mono : ∀ {x y : X}, x ⊆ y → killSet x ⊆ killSet y := by
      intro x y hxy j hj
      simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact Nat.le_zero.mp (hj ▸ hf_anti x y hxy j)
    have hfall_bd : ∀ r S, hasFall r S → r ≤ (Finset.univ : Finset K).card := by
      intro r S ⟨p, t, _, _, hsub, hdrop⟩
      have hcard_inc : ∀ i : Fin r, (killSet (p i.castSucc)).card + 1 ≤ (killSet (p i.succ)).card := by
        intro i
        have hss : killSet (p i.castSucc) ⊂ killSet (p i.succ) := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨hkill_mono (hsub i), fun heq => ?_⟩
          have hmem : t i ∈ killSet (p i.succ) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hdrop i).2⟩
          rw [← heq] at hmem
          have h0 : f (p i.castSucc) (t i) = 0 := (Finset.mem_filter.mp hmem).2
          have hpos := (hdrop i).1
          omega
        exact Finset.card_lt_card hss
      have hle : ∀ m (hm : m ≤ r), m ≤ (killSet (p ⟨m, by omega⟩)).card := by
        intro m hm
        induction m with
        | zero => exact Nat.zero_le _
        | succ m ihm =>
          have h1 := ihm (by omega)
          have h2 := hcard_inc ⟨m, by omega⟩
          change (killSet (p ⟨m, by omega⟩)).card + 1 ≤ (killSet (p ⟨m + 1, by omega⟩)).card at h2
          omega
      exact le_trans (hle r le_rfl) (Finset.card_le_card (Finset.subset_univ _))
    have hfall_zero : ∀ S, hasFall 0 S := by
      intro S
      exact ⟨fun _ => ∅, fun i => i.elim0, rfl, Finset.empty_subset _, fun i => i.elim0, fun i => i.elim0⟩

    let M : ℕ := (Finset.univ : Finset K).card + 1
    let hS : Finset (Fin d) → ℕ := fun S =>
      ((Finset.range M).filter (fun r => hasFall r S)).max'
        ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hfall_zero S⟩⟩
    have hh_has : ∀ S, hasFall (hS S) S := by
      intro S
      have hm := Finset.max'_mem ((Finset.range M).filter (fun r => hasFall r S))
        ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hfall_zero S⟩⟩
      exact (Finset.mem_filter.mp hm).2
    have hh_le : ∀ r S, hasFall r S → r ≤ hS S := by
      intro r S hr
      apply Finset.le_max'
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hfall_bd r S hr)), hr⟩
    have hh_mono : ∀ {S T : Finset (Fin d)}, S ⊆ T → hS S ≤ hS T := by
      intro S T hST
      apply hh_le
      obtain ⟨p, t, hp0, hplast, hsub, hdrop⟩ := hh_has S
      have hbank : bank S ⊆ bank T := by
        intro j hj; rw [hmem_bank] at hj ⊢
        exact Finset.Subset.trans hj hST
      exact ⟨p, t, hp0, Finset.Subset.trans hplast hbank, hsub, hdrop⟩

    have hkill_eq : ∀ {S T : Finset (Fin d)}, S ⊆ T → hS S = hS T →
        killSet (bank S) = killSet (bank T) := by
      intro S T hST heq
      have hbank : bank S ⊆ bank T := by
        intro j hj; rw [hmem_bank] at hj ⊢
        exact Finset.Subset.trans hj hST
      apply Finset.Subset.antisymm (hkill_mono hbank)
      intro j hj
      by_contra hjS
      simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj hjS
      have hpos : 0 < f (bank S) j := Nat.pos_of_ne_zero hjS

      obtain ⟨p, t, hp0, hplast, hsub, hdrop⟩ := hh_has S
      let r := hS S
      let p' : Fin (r + 1 + 1) → X := fun i =>
        if hi : i.val ≤ r then p ⟨i.val, by omega⟩ else bank T
      let t' : Fin (r + 1) → K := fun i =>
        if hi : i.val < r then t ⟨i.val, hi⟩ else j
      have hnext : hasFall (r + 1) T := by
        refine ⟨p', t', ?_, ?_, ?_, ?_⟩
        · dsimp only [p']; simp [hp0]
        · dsimp only [p']; simp
        · intro i
          dsimp only [p']
          by_cases hi : i.val < r
          · have h1 : i.castSucc.val ≤ r := by simp; omega
            have h2 : i.succ.val ≤ r := by simp; omega
            rw [dif_pos h1, dif_pos h2]
            exact hsub ⟨i.val, hi⟩
          · have hi_eq : i.val = r := by have := i.isLt; omega
            have h1 : i.castSucc.val ≤ r := by simp; omega
            have h2 : ¬(i.succ.val ≤ r) := by simp; omega
            rw [dif_pos h1, dif_neg h2]
            have hlast_eq : (⟨i.castSucc.val, by omega⟩ : Fin (r + 1)) = Fin.last r :=
              Fin.ext (by simp [hi_eq])
            rw [hlast_eq]
            exact Finset.Subset.trans hplast hbank
        · intro i
          dsimp only [p', t']
          by_cases hi : i.val < r
          · have h1 : i.castSucc.val ≤ r := by simp; omega
            have h2 : i.succ.val ≤ r := by simp; omega
            rw [dif_pos h1, dif_pos h2, dif_pos hi]
            exact hdrop ⟨i.val, hi⟩
          · have hi_eq : i.val = r := by have := i.isLt; omega
            have h1 : i.castSucc.val ≤ r := by simp; omega
            have h2 : ¬(i.succ.val ≤ r) := by simp; omega
            rw [dif_pos h1, dif_neg h2, dif_neg hi]
            have hlast_eq : (⟨i.castSucc.val, by omega⟩ : Fin (r + 1)) = Fin.last r :=
              Fin.ext (by simp [hi_eq])
            rw [hlast_eq]
            exact ⟨lt_of_lt_of_le hpos (hf_anti _ _ hplast j), hj⟩
      have := hh_le (r + 1) T hnext
      omega

    have hkill_ne : ∀ {S T : Finset (Fin d)}, Disjoint S T → k ≤ S.card → k ≤ T.card →
        killSet (bank S) ≠ killSet (bank T) := by
      intro S T hdisj _ hTk heq
      obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hTk
      let j : K := ⟨t, ht_card⟩
      have hjT : j ∈ bank T := (hmem_bank T j).mpr ht_sub
      have hj_killT : j ∈ killSet (bank T) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf_mem (bank T) j hjT⟩
      rw [← heq] at hj_killT
      have h0 : f (bank S) j = 0 := (Finset.mem_filter.mp hj_killT).2
      have hD_eq : f (bank S) j = D := by
        apply hf_disj
        intro i hi
        have hiS : i.val ⊆ S := (hmem_bank S i).mp hi
        exact Disjoint.mono hiS ht_sub hdisj
      omega

    have hh_pos : ∀ {S : Finset (Fin d)}, k ≤ S.card → 1 ≤ hS S := by
      intro S hSk
      obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hSk
      let j : K := ⟨t, ht_card⟩
      have hjS : j ∈ bank S := (hmem_bank S j).mpr ht_sub
      apply hh_le 1 S
      refine ⟨fun i => if i.val = 0 then ∅ else bank S, fun _ => j, by simp,
        by simp, fun i => ?_, fun i => ?_⟩
      · rw [Fin.eq_zero i]
        have h00 : ((0 : Fin 1).castSucc).val = 0 := rfl
        dsimp only
        rw [if_pos h00]
        exact Finset.empty_subset _
      · rw [Fin.eq_zero i]
        have h00 : ((0 : Fin 1).castSucc).val = 0 := rfl
        have h01 : ((0 : Fin 1).succ).val ≠ 0 := by decide
        dsimp only
        rw [if_pos h00, if_neg h01]
        exact ⟨by rw [hf_disj ∅ j (fun x hx => (Finset.notMem_empty x hx).elim)]; exact hD, hf_mem (bank S) j hjS⟩
    have hh_zero_of_lt : ∀ {S : Finset (Fin d)}, S.card < k → hS S = 0 := by
      intro S hSlt
      by_contra hne
      have h1 : hasFall (hS S) S := hh_has S
      obtain ⟨p, t, hp0, hplast, hsub, hdrop⟩ := h1
      have hbank_e : bank S = ∅ := by
        ext j; rw [hmem_bank]; simp only [Finset.notMem_empty, iff_false]
        intro hj; have := Finset.card_le_card hj; rw [j.property] at this; omega
      have hp1 : p ⟨1, by omega⟩ = ∅ := by
        have hle : p ⟨1, by omega⟩ ⊆ p (Fin.last (hS S)) := by
          suffices ∀ m (hm : 1 ≤ m) (hm2 : m ≤ hS S), p ⟨1, by omega⟩ ⊆ p ⟨m, by omega⟩ from
            this (hS S) (by omega) le_rfl
          intro m hm hm2
          induction m with
          | zero => omega
          | succ m ihm =>
            by_cases hm0 : m = 0
            · subst hm0; exact Finset.Subset.refl _
            · exact Finset.Subset.trans (ihm (by omega) (by omega)) (hsub ⟨m, by omega⟩)
        exact Finset.subset_empty.mp (hbank_e ▸ Finset.Subset.trans hle hplast)
      have hd0 := hdrop ⟨0, by omega⟩
      change 0 < f (p 0) (t ⟨0, by omega⟩) ∧ f (p ⟨1, by omega⟩) (t ⟨0, by omega⟩) = 0 at hd0
      rw [hp0, hp1] at hd0
      omega

    have hpays_of_fall : ∀ {m : ℕ} {S : Finset (Fin d)}, hasFall (m + 1) S →
        pays f (bank S) (D + m) := by
      intro m S ⟨p, t, hp0, hplast, hsub, hdrop⟩
      refine ⟨m + 1, p, t, hp0, hplast, hsub, ?_⟩
      rw [Fin.sum_univ_succ]
      have h0 : f (p 0) (t 0) - f (p 1) (t 0) = D := by
        have h1 : f (p 0) (t 0) = D := by rw [hp0]; exact hf_disj ∅ (t 0) (fun i hi => (Finset.notMem_empty i hi).elim)
        have h2 : f (p 1) (t 0) = 0 := (hdrop 0).2
        omega
      have hrest : m ≤ ∑ i : Fin m, (f (p i.succ.castSucc) (t i.succ) - f (p i.succ.succ) (t i.succ)) := by
        have h1 : ∀ i : Fin m, 1 ≤ f (p i.succ.castSucc) (t i.succ) - f (p i.succ.succ) (t i.succ) := by
          intro i
          have hd := hdrop i.succ
          change 0 < f (p i.succ.castSucc) (t i.succ) ∧ f (p i.succ.succ) (t i.succ) = 0 at hd
          omega
        calc m = ∑ _i : Fin m, 1 := by simp
          _ ≤ ∑ i : Fin m, (f (p i.succ.castSucc) (t i.succ) - f (p i.succ.succ) (t i.succ)) :=
            Finset.sum_le_sum (fun i _ => h1 i)
      change D + m ≤ (f (p 0) (t 0) - f (p 1) (t 0)) +
        ∑ i : Fin m, (f (p i.succ.castSucc) (t i.succ) - f (p i.succ.succ) (t i.succ))
      omega

    have hmeets_of_card : ∀ {a : Finset (Fin d)}, k ≤ a.card → a.card < 2 * k → meets (bank a) := by
      intro a hak ha2k
      constructor
      · obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hak
        exact ⟨⟨t, ht_card⟩, (hmem_bank a ⟨t, ht_card⟩).mpr ht_sub⟩
      · intro i hi j hj hdisj
        have hi_sub : i.val ⊆ a := (hmem_bank a i).mp hi
        have hj_sub : j.val ⊆ a := (hmem_bank a j).mp hj
        have hle := Finset.card_le_card (Finset.union_subset hi_sub hj_sub)
        rw [Finset.card_union_of_disjoint hdisj, i.property, j.property] at hle
        omega

    let t1 := (d - 2 * k + 1) / 2 + 1
    let t2 := (d - 2 * k) / 2 + 1
    have hex_pair : ∃ a b : Finset (Fin d), Disjoint a b ∧ a ∪ b = Finset.univ ∧
        t1 ≤ hS a ∧ t2 ≤ hS b := by
      by_contra hno

      have hforb : ∀ A B : Finset (Fin d), Disjoint A B →
          ¬ (t1 ≤ hS A ∧ t2 ≤ hS B) ∧ ¬ (t2 ≤ hS A ∧ t1 ≤ hS B) := by
        intro A B hdisj
        have hsub : A ⊆ Bᶜ := Finset.subset_compl_iff_disjoint_right.mpr hdisj
        have hpart : Disjoint Bᶜ B ∧ Bᶜ ∪ B = Finset.univ :=
          ⟨disjoint_compl_left, compl_sup_eq_top⟩
        have hpart2 : Disjoint B Bᶜ ∧ B ∪ Bᶜ = Finset.univ :=
          ⟨disjoint_compl_right, sup_compl_eq_top⟩
        constructor
        · rintro ⟨hA, hB⟩
          exact hno ⟨Bᶜ, B, hpart.1, hpart.2, le_trans hA (hh_mono hsub), hB⟩
        · rintro ⟨hA, hB⟩
          exact hno ⟨B, Bᶜ, hpart2.1, hpart2.2, hB, le_trans hA (hh_mono hsub)⟩

      let rkK : Finset K → ℕ := fun Z => (Fintype.equivFin (Finset K) Z).val
      have hrk_inj : Function.Injective rkK := fun a b h =>
        (Fintype.equivFin (Finset K)).injective (Fin.ext h)
      let q : ℕ := 2 * k - 2

      let lam : SP d → ℤ := fun p =>
        let A := p.val.1; let B := p.val.2
        if hsz : A.card + B.card ≤ q then
          let sz : ℤ := (A.card + B.card : ℕ)
          if A.card > B.card then sz
          else if B.card > A.card then -sz
          else if (A ∪ B).min' p.property.2 ∈ A then sz else -sz
        else
          if hS A > hS B then ((q + 2 * hS B + 1 : ℕ) : ℤ)
          else if hS B > hS A then -((q + 2 * hS A + 1 : ℕ) : ℤ)
          else if rkK (killSet (bank A)) < rkK (killSet (bank B)) then ((q + 2 * hS A : ℕ) : ℤ)
          else -((q + 2 * hS A : ℕ) : ℤ)
      have hlam_nz : ∀ p : SP d, lam p ≠ 0 := by
        intro p
        have hne : 0 < p.val.1.card + p.val.2.card := by
          rw [← Finset.card_union_of_disjoint p.property.1]
          exact Finset.card_pos.mpr p.property.2
        dsimp only [lam]
        split_ifs with hsz
        all_goals try omega
        ·
          have hmax : k ≤ p.val.1.card ∨ k ≤ p.val.2.card := by omega
          have hpos : 1 ≤ hS p.val.1 := by
            rcases hmax with h | h
            · exact hh_pos h
            · have := hh_pos h; omega
          omega
        · have hmax : k ≤ p.val.1.card ∨ k ≤ p.val.2.card := by omega
          have hpos : 1 ≤ hS p.val.1 := by
            rcases hmax with h | h
            · exact hh_pos h
            · have := hh_pos h; omega
          omega
      have hlam_bnd : ∀ p : SP d, (lam p).natAbs < d := by
        intro p
        dsimp only [lam]
        have hf := hforb p.val.1 p.val.2 p.property.1
        split_ifs with hsz hgt1 hgt2 hmin hgtA hgtB hrk
        · have : ((p.val.1.card + p.val.2.card : ℕ) : ℤ).natAbs = p.val.1.card + p.val.2.card := Int.natAbs_natCast _
          omega
        · have : (-((p.val.1.card + p.val.2.card : ℕ) : ℤ)).natAbs = p.val.1.card + p.val.2.card := by
            rw [Int.natAbs_neg, Int.natAbs_natCast]
          omega
        · have : ((p.val.1.card + p.val.2.card : ℕ) : ℤ).natAbs = p.val.1.card + p.val.2.card := Int.natAbs_natCast _
          omega
        · have : (-((p.val.1.card + p.val.2.card : ℕ) : ℤ)).natAbs = p.val.1.card + p.val.2.card := by
            rw [Int.natAbs_neg, Int.natAbs_natCast]
          omega
        ·
          have hB_lt : hS p.val.2 < t2 := by
            by_contra hge; push Not at hge
            have hA_ge : t1 ≤ hS p.val.1 := by omega
            exact hf.1 ⟨hA_ge, hge⟩
          simp only [Int.natAbs_natCast]; omega
        · have hA_lt : hS p.val.1 < t2 := by
            by_contra hge; push Not at hge
            have hB_ge : t1 ≤ hS p.val.2 := by omega
            exact hf.2 ⟨hge, hB_ge⟩
          simp only [Int.natAbs_neg, Int.natAbs_natCast]; omega
        ·
          have hA_lt : hS p.val.1 < t1 := by
            by_contra hge; push Not at hge
            have hB_ge : t2 ≤ hS p.val.2 := by omega
            exact hf.1 ⟨hge, hB_ge⟩
          simp only [Int.natAbs_natCast]; omega
        · have hA_lt : hS p.val.1 < t1 := by
            by_contra hge; push Not at hge
            have hB_ge : t2 ≤ hS p.val.2 := by omega
            exact hf.1 ⟨hge, hB_ge⟩
          simp only [Int.natAbs_neg, Int.natAbs_natCast]; omega
      have hlam_anti : ∀ p : SP d, lam (spSwap p) = -lam p := by
        intro p
        dsimp only [lam, spSwap]
        have hcomm : p.val.2.card + p.val.1.card = p.val.1.card + p.val.2.card := Nat.add_comm _ _
        rw [hcomm]
        by_cases hsz : p.val.1.card + p.val.2.card ≤ q
        · rw [dif_pos hsz, dif_pos hsz]
          by_cases h1 : p.val.1.card > p.val.2.card
          · have h2 : ¬(p.val.2.card > p.val.1.card) := by omega
            rw [if_neg h2, if_pos h1, if_pos h1]
          · by_cases h2 : p.val.2.card > p.val.1.card
            · rw [if_pos h2, if_neg h1, if_pos h2, neg_neg]
            · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]
              have hmin_eq : (p.val.2 ∪ p.val.1).min' (by rw [Finset.union_comm]; exact p.property.2) =
                  (p.val.1 ∪ p.val.2).min' p.property.2 := by
                congr 1; exact Finset.union_comm _ _
              have hm_mem : (p.val.1 ∪ p.val.2).min' p.property.2 ∈ p.val.1 ∪ p.val.2 :=
                Finset.min'_mem _ _
              by_cases hmA : (p.val.1 ∪ p.val.2).min' p.property.2 ∈ p.val.1
              · have hmB : (p.val.1 ∪ p.val.2).min' p.property.2 ∉ p.val.2 :=
                  Finset.disjoint_left.mp p.property.1 hmA
                rw [hmin_eq, if_neg hmB, if_pos hmA]
              · have hmB : (p.val.1 ∪ p.val.2).min' p.property.2 ∈ p.val.2 :=
                  (Finset.mem_union.mp hm_mem).resolve_left hmA
                rw [hmin_eq, if_pos hmB, if_neg hmA, neg_neg]
        · rw [dif_neg hsz, dif_neg hsz]
          by_cases h1 : hS p.val.1 > hS p.val.2
          · have h2 : ¬(hS p.val.2 > hS p.val.1) := by omega
            rw [if_neg h2, if_pos h1, if_pos h1]
          · by_cases h2 : hS p.val.2 > hS p.val.1
            · rw [if_pos h2, if_neg h1, if_pos h2, neg_neg]
            · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]
              have heq : hS p.val.1 = hS p.val.2 := by omega
              have hmax : k ≤ p.val.1.card ∨ k ≤ p.val.2.card := by omega
              have hpos : 1 ≤ hS p.val.1 := by
                rcases hmax with h | h
                · exact hh_pos h
                · rw [heq]; exact hh_pos h
              have hkA : k ≤ p.val.1.card := by
                by_contra hlt; have := hh_zero_of_lt (not_le.mp hlt); omega
              have hkB : k ≤ p.val.2.card := by
                by_contra hlt; have := hh_zero_of_lt (not_le.mp hlt); omega
              have hkne : killSet (bank p.val.1) ≠ killSet (bank p.val.2) :=
                hkill_ne p.property.1 hkA hkB
              have hrk_ne : rkK (killSet (bank p.val.1)) ≠ rkK (killSet (bank p.val.2)) :=
                fun h => hkne (hrk_inj h)
              by_cases hlt : rkK (killSet (bank p.val.1)) < rkK (killSet (bank p.val.2))
              · have hgt : ¬(rkK (killSet (bank p.val.2)) < rkK (killSet (bank p.val.1))) := by omega
                rw [if_neg hgt, if_pos hlt, heq]
              · have hgt : rkK (killSet (bank p.val.2)) < rkK (killSet (bank p.val.1)) := by omega
                rw [if_pos hgt, if_neg hlt, heq, neg_neg]

      obtain ⟨p, p', hp1, hp2, hcomp⟩ := octahedral_tucker (by omega) lam hlam_nz hlam_bnd hlam_anti

      have habs_eq : (lam p).natAbs = (lam p').natAbs := by rw [hcomp, Int.natAbs_neg]
      have hA_mono : hS p.val.1 ≤ hS p'.val.1 := hh_mono hp1
      have hB_mono : hS p.val.2 ≤ hS p'.val.2 := hh_mono hp2
      by_cases hsz : p.val.1.card + p.val.2.card ≤ q
      ·
        have hlp_abs : (lam p).natAbs = p.val.1.card + p.val.2.card := by
          dsimp only [lam]; rw [dif_pos hsz]
          split_ifs <;> first | exact Int.natAbs_natCast _ | (rw [Int.natAbs_neg, Int.natAbs_natCast])
        have hsz' : p'.val.1.card + p'.val.2.card ≤ q := by
          by_contra hgt
          have hlp'_gt : q < (lam p').natAbs := by
            dsimp only [lam]; rw [dif_neg hgt]
            have hmax : k ≤ p'.val.1.card ∨ k ≤ p'.val.2.card := by omega
            split_ifs with h1 h2
            · simp; omega
            · simp; omega
            · have hpos : 1 ≤ hS p'.val.1 := by
                rcases hmax with h | h; exact hh_pos h; have := hh_pos h; omega
              simp; omega
            · have hpos : 1 ≤ hS p'.val.1 := by
                rcases hmax with h | h; exact hh_pos h; have := hh_pos h; omega
              simp; omega
          omega
        have hlp'_abs : (lam p').natAbs = p'.val.1.card + p'.val.2.card := by
          dsimp only [lam]; rw [dif_pos hsz']
          split_ifs <;> first | exact Int.natAbs_natCast _ | (rw [Int.natAbs_neg, Int.natAbs_natCast])
        have hcard_eq : p.val.1.card + p.val.2.card = p'.val.1.card + p'.val.2.card := by omega
        have h1eq : p.val.1 = p'.val.1 :=
          Finset.eq_of_subset_of_card_le hp1 (by have := Finset.card_le_card hp2; omega)
        have h2eq : p.val.2 = p'.val.2 :=
          Finset.eq_of_subset_of_card_le hp2 (by have := Finset.card_le_card hp1; omega)
        have hpeq : p = p' := Subtype.ext (Prod.ext h1eq h2eq)
        rw [hpeq] at hcomp
        exact hlam_nz p' (by omega)
      ·
        have hsz' : ¬(p'.val.1.card + p'.val.2.card ≤ q) := by
          have := Finset.card_le_card hp1; have := Finset.card_le_card hp2; omega
        dsimp only [lam] at hcomp
        rw [dif_neg hsz, dif_neg hsz'] at hcomp
        by_cases h1 : hS p.val.1 > hS p.val.2
        · rw [if_pos h1] at hcomp
          by_cases h1' : hS p'.val.1 > hS p'.val.2
          · rw [if_pos h1'] at hcomp; omega
          · rw [if_neg h1'] at hcomp
            by_cases h2' : hS p'.val.2 > hS p'.val.1
            · rw [if_pos h2'] at hcomp; omega
            · rw [if_neg h2'] at hcomp; split_ifs at hcomp <;> omega
        · rw [if_neg h1] at hcomp
          by_cases h2 : hS p.val.2 > hS p.val.1
          · rw [if_pos h2] at hcomp
            by_cases h1' : hS p'.val.1 > hS p'.val.2
            · rw [if_pos h1'] at hcomp; omega
            · rw [if_neg h1'] at hcomp
              by_cases h2' : hS p'.val.2 > hS p'.val.1
              · rw [if_pos h2'] at hcomp; omega
              · rw [if_neg h2'] at hcomp; split_ifs at hcomp <;> omega
          · rw [if_neg h2] at hcomp
            by_cases h1' : hS p'.val.1 > hS p'.val.2
            · rw [if_pos h1'] at hcomp; split_ifs at hcomp <;> omega
            · rw [if_neg h1'] at hcomp
              by_cases h2' : hS p'.val.2 > hS p'.val.1
              · rw [if_pos h2'] at hcomp; split_ifs at hcomp <;> omega
              · rw [if_neg h2'] at hcomp
                have hpos_p : 1 ≤ hS p.val.1 := by
                  have hmax : k ≤ p.val.1.card ∨ k ≤ p.val.2.card := by omega
                  rcases hmax with h | h; exact hh_pos h; have := hh_pos h; omega
                have hpos_p' : 1 ≤ hS p'.val.1 := by
                  have hle1 : hS p.val.1 ≤ hS p'.val.1 := hh_mono hp1
                  omega
                by_cases h3 : rkK (killSet (bank p.val.1)) < rkK (killSet (bank p.val.2))
                · rw [if_pos h3] at hcomp
                  by_cases h3' : rkK (killSet (bank p'.val.1)) < rkK (killSet (bank p'.val.2))
                  · rw [if_pos h3'] at hcomp; omega
                  · rw [if_neg h3'] at hcomp
                    have heqA : hS p.val.1 = hS p'.val.1 := by omega
                    have heqB : hS p.val.2 = hS p'.val.2 := by omega
                    rw [hkill_eq hp1 heqA, hkill_eq hp2 heqB] at h3; omega
                · rw [if_neg h3] at hcomp
                  by_cases h3' : rkK (killSet (bank p'.val.1)) < rkK (killSet (bank p'.val.2))
                  · rw [if_pos h3'] at hcomp
                    have heqA : hS p.val.1 = hS p'.val.1 := by omega
                    have heqB : hS p.val.2 = hS p'.val.2 := by omega
                    rw [hkill_eq hp1 heqA, hkill_eq hp2 heqB] at h3; omega
                  · rw [if_neg h3'] at hcomp; omega
    obtain ⟨a, b, hdisj, hunion, ha, hb⟩ := hex_pair
    have hcard_sum : a.card + b.card = d := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    have hak : k ≤ a.card := by
      by_contra hlt; have := hh_zero_of_lt (not_le.mp hlt); omega
    have hbk : k ≤ b.card := by
      by_contra hlt; have := hh_zero_of_lt (not_le.mp hlt); omega
    have ha2k : a.card < 2 * k := by omega
    have hb2k : b.card < 2 * k := by omega
    have hfall_a : hasFall ((d - 2 * k + 1) / 2 + 1) a := by
      have h1 := hh_has a
      obtain ⟨p, t, hp0, hplast, hsub, hdrop⟩ := h1
      let r := (d - 2 * k + 1) / 2 + 1
      have hrle : r ≤ hS a := ha
      refine ⟨fun i => p ⟨i.val, by omega⟩, fun i => t ⟨i.val, by omega⟩, hp0, ?_, ?_, ?_⟩
      · have hle : p ⟨r, by omega⟩ ⊆ p (Fin.last (hS a)) := by
          suffices ∀ m (hm1 : r ≤ m) (hm2 : m ≤ hS a), p ⟨r, by omega⟩ ⊆ p ⟨m, by omega⟩ from
            this (hS a) hrle le_rfl
          intro m hm1 hm2
          induction m with
          | zero => omega
          | succ m ihm =>
            by_cases hm : m < r
            · have hmr : m + 1 = r := by omega
              have : (⟨m + 1, by omega⟩ : Fin (hS a + 1)) = ⟨r, by omega⟩ := Fin.ext hmr
              rw [this]
            · exact Finset.Subset.trans (ihm (by omega) (by omega)) (hsub ⟨m, by omega⟩)
        exact Finset.Subset.trans hle hplast
      · intro i; exact hsub ⟨i.val, by omega⟩
      · intro i; exact hdrop ⟨i.val, by omega⟩
    have hfall_b : hasFall ((d - 2 * k) / 2 + 1) b := by
      have h1 := hh_has b
      obtain ⟨p, t, hp0, hplast, hsub, hdrop⟩ := h1
      let r := (d - 2 * k) / 2 + 1
      have hrle : r ≤ hS b := hb
      refine ⟨fun i => p ⟨i.val, by omega⟩, fun i => t ⟨i.val, by omega⟩, hp0, ?_, ?_, ?_⟩
      · have hle : p ⟨r, by omega⟩ ⊆ p (Fin.last (hS b)) := by
          suffices ∀ m (hm1 : r ≤ m) (hm2 : m ≤ hS b), p ⟨r, by omega⟩ ⊆ p ⟨m, by omega⟩ from
            this (hS b) hrle le_rfl
          intro m hm1 hm2
          induction m with
          | zero => omega
          | succ m ihm =>
            by_cases hm : m < r
            · have hmr : m + 1 = r := by omega
              have : (⟨m + 1, by omega⟩ : Fin (hS b + 1)) = ⟨r, by omega⟩ := Fin.ext hmr
              rw [this]
            · exact Finset.Subset.trans (ihm (by omega) (by omega)) (hsub ⟨m, by omega⟩)
        exact Finset.Subset.trans hle hplast
      · intro i; exact hsub ⟨i.val, by omega⟩
      · intro i; exact hdrop ⟨i.val, by omega⟩
    exact ⟨a, b, hdisj, by convert hunion, hmeets_of_card hak ha2k, hmeets_of_card hbk hb2k,
      hpays_of_fall hfall_a, hpays_of_fall hfall_b⟩
  ·
    intro D hD hDk
    let r := k - D
    have hrk : r < k := by omega
    obtain ⟨φ, hφ⟩ := exists_stahl_iter r d k hrk h2k
    have hpal_eq : d - 2 * r = 2 * D + (d - 2 * k) := by omega
    have hD_eq : k - r = D := by omega
    let col : K → Finset (Fin (d - 2 * r)) := fun j => (φ j).val
    have hcol_card : ∀ j : K, (col j).card = D := fun j => (φ j).property.trans hD_eq
    have hcol_disj : ∀ i j : K, Disjoint i.val j.val → Disjoint (col i) (col j) := hφ
    let F : X → K → Nat := fun x j => (col j \ x.biUnion col).card
    refine ⟨F, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    ·
      intro x j
      exact le_trans (Finset.card_le_card Finset.sdiff_subset) (by rw [hcol_card j])
    ·
      intro x j hdisj
      have hd_bi : Disjoint (col j) (x.biUnion col) := by
        rw [Finset.disjoint_biUnion_right]
        intro i hi; exact (hcol_disj i j (hdisj i hi)).symm
      dsimp only [F]; rw [Finset.sdiff_eq_self_of_disjoint hd_bi, hcol_card j]
    ·
      intro x j hj
      have hsub : col j ⊆ x.biUnion col := Finset.subset_biUnion_of_mem col hj
      dsimp only [F]; rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty]
    ·
      intro x y hxy j
      exact Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (Finset.biUnion_subset_biUnion_of_subset_left col hxy))
    ·
      intro a b hab u v hu hv
      have hpays_le : ∀ (S : Finset (Fin d)) (c : ℕ), pays F (bank S) c →
          c ≤ ((bank S).biUnion col).card := by
        intro S c ⟨l, p, t, hp0, hplast, hsub, hc⟩
        let U : Fin (l + 1) → Finset (Fin (d - 2 * r)) := fun i => (p i).biUnion col
        have hU_mono : ∀ i : Fin l, U i.castSucc ⊆ U i.succ := fun i =>
          Finset.biUnion_subset_biUnion_of_subset_left col (hsub i)
        have hstep : ∀ i : Fin l, F (p i.castSucc) (t i) - F (p i.succ) (t i) ≤
            (U i.succ).card - (U i.castSucc).card := by
          intro i
          dsimp only [F]
          have hsub_sdiff : col (t i) \ U i.succ ⊆ col (t i) \ U i.castSucc :=
            Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (hU_mono i)
          have hdiff_sub : (col (t i) \ U i.castSucc) \ (col (t i) \ U i.succ) ⊆ U i.succ \ U i.castSucc := by
            intro z hz
            simp only [Finset.mem_sdiff, not_and, not_not] at hz ⊢
            exact ⟨hz.2 hz.1.1, hz.1.2⟩
          have h1 : ((col (t i) \ U i.castSucc) \ (col (t i) \ U i.succ)).card =
              (col (t i) \ U i.castSucc).card - (col (t i) \ U i.succ).card := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub_sdiff]
          have h2 : (U i.succ \ U i.castSucc).card = (U i.succ).card - (U i.castSucc).card := by
            rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hU_mono i)]
          have h3 := Finset.card_le_card hdiff_sub
          change (col (t i) \ U i.castSucc).card - (col (t i) \ U i.succ).card ≤ (U i.succ).card - (U i.castSucc).card
          omega
        have hsum_le : ∑ i : Fin l, (F (p i.castSucc) (t i) - F (p i.succ) (t i)) ≤
            ∑ i : Fin l, ((U i.succ).card - (U i.castSucc).card) :=
          Finset.sum_le_sum (fun i _ => hstep i)
        have htel := sum_sub_telescope (fun i => (U i).card) (fun i => Finset.card_le_card (hU_mono i))
        have hU0 : (U 0).card = 0 := by
          dsimp only [U]; rw [hp0, Finset.card_eq_zero]; ext x; simp; intro y hy; exact (Finset.notMem_empty y hy).elim
        have hUl : (U (Fin.last l)).card ≤ ((bank S).biUnion col).card :=
          Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left col hplast)
        omega
      have hu_le := hpays_le a u hu
      have hv_le := hpays_le b v hv
      have hdisj_bi : Disjoint ((bank a).biUnion col) ((bank b).biUnion col) := by
        rw [Finset.disjoint_biUnion_left]
        intro i hi
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hcol_disj i j (Disjoint.mono ((hmem_bank a i).mp hi) ((hmem_bank b j).mp hj) hab)
      have htot : ((bank a).biUnion col).card + ((bank b).biUnion col).card ≤ d - 2 * r := by
        rw [← Finset.card_union_of_disjoint hdisj_bi]
        exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
      omega
