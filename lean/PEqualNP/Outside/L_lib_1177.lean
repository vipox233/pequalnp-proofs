import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1177_aux

lemma list_count_map_bool {α : Type*} (l : List α) (f : α → Bool) (b : Bool) :
    (l.map f).count b = (l.filter (fun a => f a == b)).length := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.map_cons, List.count_cons, List.filter_cons, ih]
    cases b <;> cases hfa : f a <;> simp [hfa]

lemma list_bool_count_true_add_false (l : List Bool) :
    l.count true + l.count false = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases x <;> simp [List.count_cons] <;> omega

lemma finRange_map_count_eq_card {k : Nat} (tr : Fin k → Bool) (b : Bool) :
    ((List.finRange k).map tr).count b =
      ((Finset.univ : Finset (Fin k)).filter (fun i => tr i = b)).card := by
  rw [list_count_map_bool]
  have hnd : ((List.finRange k).filter (fun i => tr i == b)).Nodup :=
    (List.nodup_finRange k).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext i
  simp [List.mem_toFinset, List.mem_filter, List.mem_finRange, beq_iff_eq]

lemma finRange_map_take_replicate_false {k m : Nat} (tr : Fin k → Bool)
    (hm : m ≤ k) (hzero : ∀ j : Fin k, j.val < m → tr j = false) :
    ((List.finRange k).map tr).take m = List.replicate m false := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_map, List.length_finRange, Nat.min_eq_left hm]
  · intro j hj1 hj2
    have hjm : j < m := by simpa [List.length_replicate] using hj2
    have hjk : j < k := lt_of_lt_of_le hjm hm
    simp [List.getElem_take, List.getElem_map, List.getElem_finRange, List.getElem_replicate]
    exact hzero ⟨j, hjk⟩ hjm

lemma list_take_succ_count_false :
    ∀ (l : List Bool) (m : Nat) (hm : m < l.length),
      (l.take (m + 1)).count false =
        (l.take m).count false + if l[m] = false then 1 else 0
  | [], _, hm => by simp at hm
  | x :: xs, 0, _ => by
    cases x <;> simp
  | x :: xs, m + 1, hm => by
    have hm' : m < xs.length := by simpa using hm
    have ih := list_take_succ_count_false xs m hm'
    cases x <;> simp [List.take_succ_cons, List.count_cons] at ih ⊢ <;> omega

lemma exists_jump (g : Nat → Nat) (h0 : g 0 = 0)
    (hstep : ∀ m, g (m + 1) ≤ g m + 1) :
    ∀ (k j : Nat), j < g k → ∃ m < k, g m = j ∧ g (m + 1) = j + 1
  | 0, _, hj => by omega
  | k + 1, j, hj => by
    by_cases hlt : j < g k
    · rcases exists_jump g h0 hstep k j hlt with ⟨m, hm, h1, h2⟩
      exact ⟨m, by omega, h1, h2⟩
    · have hs := hstep k
      exact ⟨k, by omega, by omega, by omega⟩

lemma exists_first_ge (f : Nat → Nat) (h0 : f 0 = 0) :
    ∀ (k b : Nat), 0 < b → b ≤ f k → ∃ m, 0 < m ∧ m ≤ k ∧ b ≤ f m ∧ f (m - 1) < b
  | 0, b, hb, hle => by omega
  | k + 1, b, hb, hle => by
    by_cases hk : b ≤ f k
    · rcases exists_first_ge f h0 k b hb hk with ⟨m, hm1, hm2, hm3, hm4⟩
      exact ⟨m, hm1, by omega, hm3, hm4⟩
    · exact ⟨k + 1, by omega, le_rfl, hle, by simpa using Nat.lt_of_not_ge hk⟩

lemma card_filter_ge_fin {k a : Nat} (ha : a ≤ k) :
    ((Finset.univ : Finset (Fin k)).filter (fun i => a ≤ i.val)).card = k - a := by
  have hbij :
      ((Finset.univ : Finset (Fin k)).filter (fun i => a ≤ i.val)).card =
        (Finset.univ : Finset (Fin (k - a))).card := by
    refine Finset.card_bij
      (fun (i : Fin k) (hi : i ∈ (Finset.univ : Finset (Fin k)).filter (fun i => a ≤ i.val)) =>
        (⟨i.val - a, by
          have h1 : a ≤ i.val := (Finset.mem_filter.mp hi).2
          omega⟩ : Fin (k - a)))
      (fun _ _ => Finset.mem_univ _)
      (fun i1 hi1 i2 hi2 heq => by
        have h1 : a ≤ i1.val := (Finset.mem_filter.mp hi1).2
        have h2 : a ≤ i2.val := (Finset.mem_filter.mp hi2).2
        have hv : i1.val - a = i2.val - a := congrArg Fin.val heq
        exact Fin.ext (by omega))
      (fun j _ => by
        refine ⟨⟨j.val + a, by omega⟩, ?_, ?_⟩
        · simp
        · exact Fin.ext (by simp))
  simpa using hbij

lemma pass_eq_true_iff {n t d : Nat} (scope : Fin t → Finset (Fin n))
    (s : Fin t → (Fin n → Fin (d + 2))) (x : Fin n → Fin (d + 2)) :
    ((List.finRange t).all (fun j =>
      (scope j).toList.any (fun v => x v != s j v)) = true) ↔
    (∀ j : Fin t, ∃ v ∈ scope j, x v ≠ s j v) := by
  simp [List.all_eq_true, List.any_eq_true, List.mem_finRange, Finset.mem_toList, bne_iff_ne]

lemma reply_eq_true_iff {n t d : Nat} (scope : Fin t → Finset (Fin n))
    (A : Finset (Fin n → Fin (d + 2))) (s : Fin t → (Fin n → Fin (d + 2))) :
    (A.toList.any (fun x => (List.finRange t).all (fun j =>
      (scope j).toList.any (fun v => x v != s j v))) = true) ↔
    (∃ x ∈ A, (List.finRange t).all (fun j =>
      (scope j).toList.any (fun v => x v != s j v)) = true) := by
  simp [List.any_eq_true, Finset.mem_toList]

lemma reply_singleton {n t d : Nat} (scope : Fin t → Finset (Fin n))
    (x : Fin n → Fin (d + 2)) (s : Fin t → (Fin n → Fin (d + 2))) :
    (({x} : Finset (Fin n → Fin (d + 2))).toList.any (fun y => (List.finRange t).all (fun j =>
      (scope j).toList.any (fun v => y v != s j v)))) =
    ((List.finRange t).all (fun j =>
      (scope j).toList.any (fun v => x v != s j v))) := by
  apply Bool.eq_iff_iff.mpr
  rw [reply_eq_true_iff]
  simp

lemma admissible_of_signing {n t d : Nat} (scope : Fin t → Finset (Fin n))
    (P : Finset (Fin n → Fin (d + 2))) (s : Fin t → (Fin n → Fin (d + 2))) :
    let X := P.filter (fun x => (List.finRange t).all (fun j =>
      (scope j).toList.any (fun v => x v != s j v)) = true)
    X ⊆ P ∧ ∀ j : Fin t, ∃ z : Fin n → Fin (d + 2), ∀ x ∈ X, ∃ v ∈ scope j, x v ≠ z v := by
  refine ⟨Finset.filter_subset _ _, fun j => ⟨s j, fun x hx => ?_⟩⟩
  have hp := (Finset.mem_filter.mp hx).2
  exact (pass_eq_true_iff scope s x).mp hp j

lemma signing_of_admissible {n t d : Nat} (scope : Fin t → Finset (Fin n))
    (X : Finset (Fin n → Fin (d + 2)))
    (hX : ∀ j : Fin t, ∃ z : Fin n → Fin (d + 2), ∀ x ∈ X, ∃ v ∈ scope j, x v ≠ z v) :
    ∃ s : Fin t → (Fin n → Fin (d + 2)), ∀ x ∈ X,
      (List.finRange t).all (fun j =>
        (scope j).toList.any (fun v => x v != s j v)) = true := by
  refine ⟨fun j => Classical.choose (hX j), fun x hx => ?_⟩
  rw [pass_eq_true_iff]
  intro j
  exact Classical.choose_spec (hX j) x hx

theorem main (n t d : Nat) (scope : Fin t → Finset (Fin n))
    (P : Finset (Fin n → Fin (d + 2))) (u v k : Nat) (hP : P.Nonempty) :
    let Word := Fin n → Fin (d + 2)
    let Signing := Fin t → Word
    let pass := fun (s : Signing) (x : Word) => (List.finRange t).all (fun j =>
      (scope j).toList.any (fun v => x v != s j v))
    let reply := fun (A : Finset Word) (s : Signing) => A.toList.any (pass s)
    let admissible := fun (X : Finset Word) => ∀ j : Fin t,
      ∃ z : Word, ∀ x ∈ X, ∃ v ∈ scope j, x v ≠ z v
    let cover := fun (b l : Nat) => ∃ X : Fin l → Finset Word,
      (∀ i, X i ⊆ P ∧ admissible (X i)) ∧
      ∀ x ∈ P, b ≤ ((Finset.univ : Finset (Fin l)).filter (fun i => x ∈ X i)).card
    let valid := fun (ask : Fin k → List Bool → Signing) (answer : List Bool → Bool) =>
      ∀ (A : Finset Word), A ⊆ P → ∀ tr : Fin k → Bool,
        let idx := (Finset.univ : Finset (Fin k))
        let history := (List.finRange k).map tr
        let missed := idx.filter (fun i => !tr i && reply A (ask i (history.take i.val)))
        (if A.Nonempty then missed.card ≤ v else (idx.filter (fun i => tr i)).card ≤ u) →
          answer history = decide A.Nonempty
    ((∃ ask : Fin k → List Bool → Signing, ∃ answer, valid ask answer) ↔
      ∃ l, l + u ≤ k ∧ cover (v + 1) l) ∧
    ((∃ ask : Fin k → Signing, ∃ answer, valid (fun i _ => ask i) answer) ↔
      cover (u + v + 1) k) := by
  dsimp only
  constructor
  · -- Adaptive equivalence
    constructor
    · -- Adaptive forward
      rintro ⟨ask, answer, hval⟩
      let s0 : Fin k → (Fin t → (Fin n → Fin (d + 2))) :=
        fun i => ask i (List.replicate i.val false)
      let X0 : Fin k → Finset (Fin n → Fin (d + 2)) :=
        fun i => P.filter (fun x => (List.finRange t).all (fun j =>
          (scope j).toList.any (fun w => x w != s0 i j w)) = true)
      let cnt : (Fin n → Fin (d + 2)) → Nat → Nat :=
        fun x m => ((Finset.univ : Finset (Fin k)).filter (fun i => i.val < m ∧ x ∈ X0 i)).card
      have hcnt_all : ∀ x ∈ P, v + 1 ≤ cnt x k := by
        intro x hx
        by_contra hlt
        push_neg at hlt
        let tr : Fin k → Bool := fun _ => false
        have hhist : ∀ i : Fin k, ((List.finRange k).map tr).take i.val =
            List.replicate i.val false :=
          fun i => finRange_map_take_replicate_false tr (le_of_lt i.isLt) (fun _ _ => rfl)
        have h0 := hval ∅ (Finset.empty_subset P) tr
        have hempty_cond :
            ((Finset.univ : Finset (Fin k)).filter (fun i => tr i = true)).card ≤ u := by
          simp [tr]
        have hans0 : answer ((List.finRange k).map tr) = false := by
          simpa using h0 (by simpa using hempty_cond)
        have h1 := hval {x} (Finset.singleton_subset_iff.mpr hx) tr
        have hmissed_eq :
            ((Finset.univ : Finset (Fin k)).filter (fun i =>
              (!tr i && ({x} : Finset (Fin n → Fin (d + 2))).toList.any (fun y =>
                (List.finRange t).all (fun j =>
                  (scope j).toList.any (fun w =>
                    y w != ask i (((List.finRange k).map tr).take i.val) j w)))) = true)) =
            ((Finset.univ : Finset (Fin k)).filter (fun i => i.val < k ∧ x ∈ X0 i)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, i.isLt, tr, Bool.not_false,
            Bool.true_and, hhist i]
          rw [reply_singleton]
          simp [X0, s0, hx]
        have hmiss_le :
            ((Finset.univ : Finset (Fin k)).filter (fun i =>
              (!tr i && ({x} : Finset (Fin n → Fin (d + 2))).toList.any (fun y =>
                (List.finRange t).all (fun j =>
                  (scope j).toList.any (fun w =>
                    y w != ask i (((List.finRange k).map tr).take i.val) j w)))) = true)).card ≤ v := by
          rw [hmissed_eq]
          change cnt x k ≤ v
          omega
        have hans1 : answer ((List.finRange k).map tr) = true := by
          simpa [Finset.singleton_nonempty] using h1 (by simpa [Finset.singleton_nonempty] using hmiss_le)
        rw [hans0] at hans1
        exact Bool.false_ne_true hans1
      have hmx_ex : ∀ x ∈ P, ∃ m, 0 < m ∧ m ≤ k ∧ v + 1 ≤ cnt x m ∧ cnt x (m - 1) < v + 1 := by
        intro x hx
        exact exists_first_ge (cnt x) (by simp [cnt]) k (v + 1) (by omega) (hcnt_all x hx)
      classical
      let mfun : (Fin n → Fin (d + 2)) → Nat :=
        fun x => if hx : x ∈ P then Classical.choose (hmx_ex x hx) else 0
      rcases Finset.exists_max_image P mfun hP with ⟨xstar, hxstar, hmax⟩
      let l : Nat := mfun xstar
      have hxstar_spec : 0 < l ∧ l ≤ k ∧ v + 1 ≤ cnt xstar l ∧ cnt xstar (l - 1) < v + 1 := by
        simpa [l, mfun, hxstar] using Classical.choose_spec (hmx_ex xstar hxstar)
      have hl_pos : 0 < l := hxstar_spec.1
      have hl_le : l ≤ k := hxstar_spec.2.1
      have hl_prev : cnt xstar (l - 1) ≤ v := by omega
      have hlu : l + u ≤ k := by
        by_contra hgt
        push_neg at hgt
        let tr : Fin k → Bool := fun i => decide (l - 1 ≤ i.val)
        have hhist : ∀ i : Fin k, i.val < l - 1 →
            ((List.finRange k).map tr).take i.val = List.replicate i.val false := by
          intro i hi
          refine finRange_map_take_replicate_false tr (le_of_lt i.isLt) (fun j hj => ?_)
          simp only [tr, decide_eq_false_iff_not]
          omega
        have h0 := hval ∅ (Finset.empty_subset P) tr
        have htrue_card :
            ((Finset.univ : Finset (Fin k)).filter (fun i => tr i = true)).card ≤ u := by
          have heq :
              ((Finset.univ : Finset (Fin k)).filter (fun i => tr i = true)) =
              ((Finset.univ : Finset (Fin k)).filter (fun i => l - 1 ≤ i.val)) := by
            ext i
            simp [tr]
          rw [heq, card_filter_ge_fin (by omega)]
          omega
        have hans0 : answer ((List.finRange k).map tr) = false := by
          simpa using h0 (by simpa using htrue_card)
        have h1 := hval {xstar} (Finset.singleton_subset_iff.mpr hxstar) tr
        have hmiss_sub :
            ((Finset.univ : Finset (Fin k)).filter (fun i =>
              (!tr i && ({xstar} : Finset (Fin n → Fin (d + 2))).toList.any (fun y =>
                (List.finRange t).all (fun j =>
                  (scope j).toList.any (fun w =>
                    y w != ask i (((List.finRange k).map tr).take i.val) j w)))) = true)) ⊆
            ((Finset.univ : Finset (Fin k)).filter (fun i => i.val < l - 1 ∧ xstar ∈ X0 i)) := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
            Bool.not_eq_true'] at hi ⊢
          have hilt : i.val < l - 1 := by
            have htf : ¬ (l - 1 ≤ i.val) := by
              simpa [tr, decide_eq_false_iff_not] using hi.1
            omega
          refine ⟨hilt, ?_⟩
          have hrep := hi.2
          rw [hhist i hilt, reply_singleton] at hrep
          exact Finset.mem_filter.mpr ⟨hxstar, hrep⟩
        have hmiss_le :
            ((Finset.univ : Finset (Fin k)).filter (fun i =>
              (!tr i && ({xstar} : Finset (Fin n → Fin (d + 2))).toList.any (fun y =>
                (List.finRange t).all (fun j =>
                  (scope j).toList.any (fun w =>
                    y w != ask i (((List.finRange k).map tr).take i.val) j w)))) = true)).card ≤ v := by
          exact le_trans (Finset.card_le_card hmiss_sub) hl_prev
        have hans1 : answer ((List.finRange k).map tr) = true := by
          simpa [Finset.singleton_nonempty] using
            h1 (by simpa [Finset.singleton_nonempty] using hmiss_le)
        rw [hans0] at hans1
        exact Bool.false_ne_true hans1
      refine ⟨l, hlu, fun j => X0 ⟨j.val, lt_of_lt_of_le j.isLt hl_le⟩, ?_, ?_⟩
      · intro j
        exact admissible_of_signing scope P (s0 ⟨j.val, lt_of_lt_of_le j.isLt hl_le⟩)
      · intro x hx
        have hmx_le : mfun x ≤ l := hmax x hx
        have hmx_spec := Classical.choose_spec (hmx_ex x hx)
        have hv_le_mx : v + 1 ≤ cnt x (mfun x) := by
          simpa [mfun, hx] using hmx_spec.2.2.1
        have hmono : cnt x (mfun x) ≤ cnt x l := by
          refine Finset.card_le_card (fun i hi => ?_)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact ⟨lt_of_lt_of_le hi.1 hmx_le, hi.2⟩
        have hbij :
            ((Finset.univ : Finset (Fin l)).filter
              (fun j => x ∈ X0 ⟨j.val, lt_of_lt_of_le j.isLt hl_le⟩)).card = cnt x l := by
          refine Finset.card_bij
            (fun (j : Fin l) _ => (⟨j.val, lt_of_lt_of_le j.isLt hl_le⟩ : Fin k))
            (fun j hj => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
              exact ⟨j.isLt, hj⟩)
            (fun j1 _ j2 _ heq => Fin.ext (congrArg (Fin.val : Fin k → Nat) heq))
            (fun i hi => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
              refine ⟨⟨i.val, hi.1⟩, ?_, Fin.ext rfl⟩
              simpa [Finset.mem_filter] using hi.2)
        rw [hbij]
        exact le_trans hv_le_mx hmono
    · -- Adaptive backward
      rintro ⟨l, hlu, X, hXadm, hXcov⟩
      rcases hP with ⟨x0, hx0⟩
      have hl_pos : 0 < l := by
        have hc := hXcov x0 hx0
        have hle : ((Finset.univ : Finset (Fin l)).filter (fun i => x0 ∈ X i)).card ≤ l := by
          calc
            ((Finset.univ : Finset (Fin l)).filter (fun i => x0 ∈ X i)).card
                ≤ (Finset.univ : Finset (Fin l)).card := Finset.card_filter_le _ _
            _ = l := by simp
        omega
      have hs_ex : ∀ j : Fin l, ∃ s : Fin t → (Fin n → Fin (d + 2)), ∀ x ∈ X j,
          (List.finRange t).all (fun q =>
            (scope q).toList.any (fun w => x w != s q w)) = true :=
        fun j => signing_of_admissible scope (X j) (hXadm j).2
      let s : Fin l → (Fin t → (Fin n → Fin (d + 2))) := fun j => Classical.choose (hs_ex j)
      have hs_pass : ∀ (j : Fin l) (x : Fin n → Fin (d + 2)), x ∈ X j →
          (List.finRange t).all (fun q =>
            (scope q).toList.any (fun w => x w != s j q w)) = true :=
        fun j => Classical.choose_spec (hs_ex j)
      let ask : Fin k → List Bool → (Fin t → (Fin n → Fin (d + 2))) :=
        fun _ h => if hlt : h.count false < l then s ⟨h.count false, hlt⟩ else s ⟨0, hl_pos⟩
      let answer : List Bool → Bool := fun h => decide (u < h.count true)
      refine ⟨ask, answer, ?_⟩
      intro A hAP tr hcond
      let history := (List.finRange k).map tr
      have hcnt_true : history.count true =
          ((Finset.univ : Finset (Fin k)).filter (fun i => tr i = true)).card :=
        finRange_map_count_eq_card tr true
      by_cases hAne : A.Nonempty
      · simp only [hAne, ↓reduceIte, decide_true] at hcond ⊢
        simp only [answer, decide_eq_true_eq]
        by_contra hle
        push Not at hle
        change history.count true ≤ u at hle
        have hlen : history.length = k := by
          simp [history, List.length_map, List.length_finRange]
        have hsum := list_bool_count_true_add_false history
        rw [hlen] at hsum
        have hfalse_ge : l ≤ history.count false := by omega
        let g : Nat → Nat := fun m => (history.take m).count false
        have hg0 : g 0 = 0 := by simp [g]
        have hgstep : ∀ m, g (m + 1) ≤ g m + 1 := by
          intro m
          by_cases hm : m < history.length
          · have h1 := list_take_succ_count_false history m hm
            dsimp only [g]
            split_ifs at h1 <;> omega
          · have hle_m : history.length ≤ m := Nat.le_of_not_lt hm
            have h1 : history.take (m + 1) = history := List.take_of_length_le (by omega)
            have h2 : history.take m = history := List.take_of_length_le hle_m
            simp [g, h1, h2]
        have hgk : g k = history.count false := by
          have hk : history.take k = history := List.take_of_length_le (by omega)
          simp [g, hk]
        have hj_ex : ∀ j : Fin l, ∃ i : Fin k,
            (history.take i.val).count false = j.val ∧ tr i = false := by
          intro j
          have hjlt : j.val < g k := by rw [hgk]; exact lt_of_lt_of_le j.isLt hfalse_ge
          rcases exists_jump g hg0 hgstep k j.val hjlt with ⟨m, hmk, hgm, hgm1⟩
          have hmlen : m < history.length := by omega
          have hstepm := list_take_succ_count_false history m hmlen
          have hget : history[m]'hmlen = false := by
            dsimp only [g] at hgm hgm1
            by_cases hb : history[m]'hmlen = false
            · exact hb
            · simp [hb] at hstepm
              omega
          have htrm : tr ⟨m, hmk⟩ = false := by
            have hval_get : history[m]'hmlen = tr ⟨m, hmk⟩ := by
              simp [history, List.getElem_map, List.getElem_finRange]
            rw [← hval_get]
            exact hget
          exact ⟨⟨m, hmk⟩, hgm, htrm⟩
        let f : Fin l → Fin k := fun j => Classical.choose (hj_ex j)
        have hf_spec : ∀ j : Fin l, (history.take (f j).val).count false = j.val ∧ tr (f j) = false :=
          fun j => Classical.choose_spec (hj_ex j)
        have hf_inj : Function.Injective f := by
          intro j1 j2 heq
          have h1 := (hf_spec j1).1
          have h2 := (hf_spec j2).1
          rw [heq] at h1
          exact Fin.ext (by omega)
        rcases hAne with ⟨x, hxA⟩
        have hxP : x ∈ P := hAP hxA
        let J : Finset (Fin l) := (Finset.univ : Finset (Fin l)).filter (fun j => x ∈ X j)
        have hJ_card : v + 1 ≤ J.card := hXcov x hxP
        have hsub : J.image f ⊆
            ((Finset.univ : Finset (Fin k)).filter (fun i =>
              (!tr i && A.toList.any (fun y => (List.finRange t).all (fun q =>
                (scope q).toList.any (fun w =>
                  y w != ask i (history.take i.val) q w)))) = true)) := by
          intro i hi
          rcases Finset.mem_image.mp hi with ⟨j, hjJ, rfl⟩
          have hxj : x ∈ X j := (Finset.mem_filter.mp hjJ).2
          have hfs := hf_spec j
          have hask : ask (f j) (history.take (f j).val) = s j := by
            dsimp only [ask]
            rw [dif_pos (by rw [hfs.1]; exact j.isLt)]
            congr 1
            exact Fin.ext hfs.1
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
            Bool.not_eq_true']
          refine ⟨hfs.2, ?_⟩
          rw [hask, reply_eq_true_iff]
          exact ⟨x, hxA, hs_pass j x hxj⟩
        have hle_v : v + 1 ≤ v := by
          calc
            v + 1 ≤ J.card := hJ_card
            _ = (J.image f).card := (Finset.card_image_of_injective J hf_inj).symm
            _ ≤ ((Finset.univ : Finset (Fin k)).filter (fun i =>
              (!tr i && A.toList.any (fun y => (List.finRange t).all (fun q =>
                (scope q).toList.any (fun w =>
                  y w != ask i (history.take i.val) q w)))) = true)).card :=
              Finset.card_le_card hsub
            _ ≤ v := hcond
        omega
      · simp only [hAne, ↓reduceIte, decide_false] at hcond ⊢
        simp only [answer, decide_eq_false_iff_not]
        rw [hcnt_true]
        omega
  · -- Non-adaptive equivalence
    constructor
    · -- Non-adaptive forward
      rintro ⟨ask, answer, hval⟩
      let X : Fin k → Finset (Fin n → Fin (d + 2)) :=
        fun i => P.filter (fun x => (List.finRange t).all (fun j =>
          (scope j).toList.any (fun w => x w != ask i j w)) = true)
      refine ⟨X, fun i => admissible_of_signing scope P (ask i), ?_⟩
      intro x hx
      by_contra hlt
      push Not at hlt
      let H : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun i => x ∈ X i)
      change H.card < u + v + 1 at hlt
      have hH_le : H.card ≤ u + v := by omega
      have hS_ex : ∃ S : Finset (Fin k), S ⊆ H ∧ S.card ≤ u ∧ (H \ S).card ≤ v := by
        by_cases hHu : H.card ≤ u
        · refine ⟨H, Finset.Subset.refl H, hHu, ?_⟩
          simp
        · push_neg at hHu
          rcases Finset.exists_subset_card_eq (le_of_lt hHu) with ⟨S, hSH, hSc⟩
          refine ⟨S, hSH, by omega, ?_⟩
          have hcs := Finset.card_sdiff_add_card_inter H S
          rw [Finset.inter_eq_right.mpr hSH] at hcs
          omega
      rcases hS_ex with ⟨S, hSH, hSc, hdiffc⟩
      let tr : Fin k → Bool := fun i => decide (i ∈ S)
      have h0 := hval ∅ (Finset.empty_subset P) tr
      have htrue_le : ((Finset.univ : Finset (Fin k)).filter (fun i => tr i = true)).card ≤ u := by
        have heq : ((Finset.univ : Finset (Fin k)).filter (fun i => tr i = true)) = S := by
          ext i
          simp [tr]
        rw [heq]
        exact hSc
      have hans0 : answer ((List.finRange k).map tr) = false := by
        simpa using h0 (by simpa using htrue_le)
      have h1 := hval {x} (Finset.singleton_subset_iff.mpr hx) tr
      have hmiss_eq :
          ((Finset.univ : Finset (Fin k)).filter (fun i =>
            (!tr i && ({x} : Finset (Fin n → Fin (d + 2))).toList.any (fun y =>
              (List.finRange t).all (fun j =>
                (scope j).toList.any (fun w => y w != ask i j w)))) = true)) = H \ S := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
          Bool.and_eq_true, Bool.not_eq_true', tr, decide_eq_false_iff_not]
        rw [reply_singleton]
        simp [H, X, hx, and_comm]
      have hmiss_le :
          ((Finset.univ : Finset (Fin k)).filter (fun i =>
            (!tr i && ({x} : Finset (Fin n → Fin (d + 2))).toList.any (fun y =>
              (List.finRange t).all (fun j =>
                (scope j).toList.any (fun w => y w != ask i j w)))) = true)).card ≤ v := by
        rw [hmiss_eq]
        exact hdiffc
      have hans1 : answer ((List.finRange k).map tr) = true := by
        simpa [Finset.singleton_nonempty] using
          h1 (by simpa [Finset.singleton_nonempty] using hmiss_le)
      rw [hans0] at hans1
      exact Bool.false_ne_true hans1
    · -- Non-adaptive backward
      rintro ⟨X, hXadm, hXcov⟩
      have hs_ex : ∀ i : Fin k, ∃ s : Fin t → (Fin n → Fin (d + 2)), ∀ x ∈ X i,
          (List.finRange t).all (fun q =>
            (scope q).toList.any (fun w => x w != s q w)) = true :=
        fun i => signing_of_admissible scope (X i) (hXadm i).2
      let ask : Fin k → (Fin t → (Fin n → Fin (d + 2))) := fun i => Classical.choose (hs_ex i)
      have hask_pass : ∀ (i : Fin k) (x : Fin n → Fin (d + 2)), x ∈ X i →
          (List.finRange t).all (fun q =>
            (scope q).toList.any (fun w => x w != ask i q w)) = true :=
        fun i => Classical.choose_spec (hs_ex i)
      let answer : List Bool → Bool := fun h => decide (u < h.count true)
      refine ⟨ask, answer, ?_⟩
      intro A hAP tr hcond
      have hcnt_true : ((List.finRange k).map tr).count true =
          ((Finset.univ : Finset (Fin k)).filter (fun i => tr i = true)).card :=
        finRange_map_count_eq_card tr true
      by_cases hAne : A.Nonempty
      · simp only [hAne, ↓reduceIte, decide_true] at hcond ⊢
        simp only [answer, decide_eq_true_eq]
        rw [hcnt_true]
        rcases hAne with ⟨x, hxA⟩
        have hxP : x ∈ P := hAP hxA
        let H : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun i => x ∈ X i)
        let T : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun i => tr i = true)
        let M : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun i =>
          (!tr i && A.toList.any (fun y => (List.finRange t).all (fun q =>
            (scope q).toList.any (fun w => y w != ask i q w)))) = true)
        have hH_sub : H ⊆ T ∪ M := by
          intro i hi
          have hxi : x ∈ X i := (Finset.mem_filter.mp hi).2
          by_cases htr : tr i = true
          · exact Finset.mem_union_left M (Finset.mem_filter.mpr ⟨Finset.mem_univ i, htr⟩)
          · have htrf : tr i = false := Bool.eq_false_iff.mpr htr
            refine Finset.mem_union_right T ?_
            simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
              Bool.not_eq_true']
            refine ⟨htrf, ?_⟩
            rw [reply_eq_true_iff]
            exact ⟨x, hxA, hask_pass i x hxi⟩
        have hH_card : u + v + 1 ≤ H.card := hXcov x hxP
        have hTM : H.card ≤ T.card + M.card :=
          le_trans (Finset.card_le_card hH_sub) (Finset.card_union_le T M)
        have hM_le : M.card ≤ v := hcond
        change u < T.card
        omega
      · simp only [hAne, ↓reduceIte, decide_false] at hcond ⊢
        simp only [answer, decide_eq_false_iff_not]
        rw [hcnt_true]
        omega

end PEqualNP.Outside.L_lib_1177_aux

theorem PEqualNP.Outside.L_lib_1177 :
∀ (n t d : Nat) (scope : Fin t → Finset (Fin n)),
  let Word := Fin n → Fin (d + 2)
  let Signing := Fin t → Word
  let pass := fun (s : Signing) (x : Word) => (List.finRange t).all (fun j =>
    (scope j).toList.any (fun v => x v != s j v))
  let reply := fun (A : Finset Word) (s : Signing) => A.toList.any (pass s)
  let admissible := fun (X : Finset Word) => ∀ j : Fin t,
    ∃ z : Word, ∀ x ∈ X, ∃ v ∈ scope j, x v ≠ z v
  ∀ (P : Finset Word) (u v k : Nat), P.Nonempty →
    let cover := fun (b l : Nat) => ∃ X : Fin l → Finset Word,
      (∀ i, X i ⊆ P ∧ admissible (X i)) ∧
      ∀ x ∈ P, b ≤ ((Finset.univ : Finset (Fin l)).filter (fun i => x ∈ X i)).card
    let valid := fun (ask : Fin k → List Bool → Signing) (answer : List Bool → Bool) =>
      ∀ (A : Finset Word), A ⊆ P → ∀ tr : Fin k → Bool,
        let idx := (Finset.univ : Finset (Fin k))
        let history := (List.finRange k).map tr
        let missed := idx.filter (fun i => !tr i && reply A (ask i (history.take i.val)))
        (if A.Nonempty then missed.card ≤ v else (idx.filter (fun i => tr i)).card ≤ u) →
          answer history = decide A.Nonempty
    ((∃ ask : Fin k → List Bool → Signing, ∃ answer, valid ask answer) ↔
      ∃ l, l + u ≤ k ∧ cover (v + 1) l) ∧
    ((∃ ask : Fin k → Signing, ∃ answer, valid (fun i _ => ask i) answer) ↔
      cover (u + v + 1) k) := by
  intro n t d scope Word Signing pass reply admissible P u v k hP cover valid
  exact PEqualNP.Outside.L_lib_1177_aux.main n t d scope P u v k hP
