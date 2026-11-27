import Mathlib
import PEqualNP.Defs

-- L-lib-414: if a pattern on a set S of at most d+1 bits is missed by the pool, a star at c in S
-- (rows c=pat c implies l=pat l) and the single row c differs from pat c agree on the pool, but the
-- first accepts strictly more than half and the second exactly half. Counting: distinct patterns
-- give distinct pool words; fixing d-1 bits, the columns and their complements are 2(n-d+1)+2 distinct vectors.

namespace PEqualNP.Outside.L_lib_414_aux

theorem exists_c (n d : ℕ) (hn : 0 < n) (S : Finset (Fin n)) (hS : S.card ≤ d + 1) :
    ∃ c : Fin n, (S.erase c).card ≤ d := by
  rcases S.eq_empty_or_nonempty with h | ⟨c, hc⟩
  · exact ⟨⟨0, hn⟩, by simp [h]⟩
  · refine ⟨c, ?_⟩
    rw [Finset.card_erase_of_mem hc]; omega

theorem half_count (n : ℕ) (c : Fin n) (b : Bool) :
    2 * (Finset.univ.filter (fun z : Fin n → Bool => z c ≠ b)).card = 2 ^ n := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → Bool))) (fun z : Fin n → Bool => z c ≠ b)
  have h2 : (Finset.univ.filter (fun z : Fin n → Bool => z c ≠ b)).card =
      (Finset.univ.filter (fun z : Fin n → Bool => ¬ z c ≠ b)).card := by
    apply Finset.card_bij' (fun z _ => Function.update z c (!z c))
      (fun z _ => Function.update z c (!z c))
    · intro z _
      funext j
      by_cases hj : j = c
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    · intro z _
      funext j
      by_cases hj : j = c
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      simp only [Function.update_self]
      cases h : z c <;> cases b <;> simp_all
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      simp only [Function.update_self]
      cases h : z c <;> cases b <;> simp_all
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h1
  omega

theorem cover (n d : ℕ) (hd : 0 < d) (hdn : d < n) (pool : Finset (Fin n → Bool))
    (classify : (↥pool → Bool) → Bool)
    (H : ∀ f : (Fin n → Bool) → Bool,
      (∃ (m : ℕ) (scope : Fin m → Finset (Fin n)) (row : Fin m → (Fin n → Bool) → Bool),
        (∀ i, (scope i).card ≤ 2) ∧
        (∀ bit : Fin n, (Finset.univ.filter (fun i => bit ∈ scope i)).card ≤ d) ∧
        (∀ i x y, (∀ j ∈ scope i, x j = y j) → row i x = row i y) ∧
        (∀ z, f z = true ↔ ∀ i, row i z = true)) →
      2 ^ n ≤ 2 * (Finset.univ.filter (fun w => f w = true)).card →
        (classify (fun q => f q.val) = true ↔
          2 ^ n < 2 * (Finset.univ.filter (fun w => f w = true)).card)) :
    ∀ S : Finset (Fin n), S.card ≤ d + 1 → ∀ pat : Fin n → Bool,
      ∃ word ∈ pool, ∀ j ∈ S, word j = pat j := by
  intro S hS pat
  by_contra hno
  push Not at hno
  obtain ⟨c, hc⟩ := exists_c n d (by omega) S hS
  let b := pat c
  let f2 : (Fin n → Bool) → Bool := fun z => decide (z c ≠ b)
  let row1 : Fin n → (Fin n → Bool) → Bool := fun l z =>
    if l ∈ S.erase c then decide (z c ≠ b ∨ z l = pat l) else true
  let f1 : (Fin n → Bool) → Bool := fun z => decide (∀ l, row1 l z = true)
  have hN2 : Finset.univ.filter (fun w => f2 w = true) =
      Finset.univ.filter (fun z : Fin n → Bool => z c ≠ b) :=
    Finset.filter_congr (fun z _ => by simp only [f2]; exact decide_eq_true_iff)
  have hcount2 : 2 * (Finset.univ.filter (fun w => f2 w = true)).card = 2 ^ n := by
    rw [hN2]; exact half_count n c b
  have hsub : Finset.univ.filter (fun w => f2 w = true) ⊂
      Finset.univ.filter (fun w => f1 w = true) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨pat, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, f1, decide_eq_true_iff]
        intro l
        simp only [row1]
        split_ifs <;> simp
      · simp [f2, b]
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f1, f2,
        decide_eq_true_iff] at hz ⊢
      intro l
      simp only [row1]
      split_ifs <;> simp [hz]
  have hlt := Finset.card_lt_card hsub
  have hlab : (fun q : ↥pool => f1 q.val) = (fun q : ↥pool => f2 q.val) := by
    funext q
    obtain ⟨q, hq⟩ := q
    obtain ⟨j, hjS, hj⟩ := hno q hq
    simp only
    by_cases hqc : q c = b
    · have e2 : f2 q = false := by simp [f2, hqc]
      have hjc : j ≠ c := by
        intro h; subst h; exact hj hqc
      have e1 : f1 q = false := by
        simp only [f1, decide_eq_false_iff_not, not_forall]
        refine ⟨j, ?_⟩
        simp only [row1, Finset.mem_erase, hjc, ne_eq, not_false_eq_true, hjS, and_self, ite_true]
        simp [hqc, hj]
      rw [e1, e2]
    · have e2 : f2 q = true := by simp [f2, hqc]
      have e1 : f1 q = true := by
        simp only [f1, decide_eq_true_iff]
        intro l; simp only [row1]; split_ifs <;> simp [hqc]
      rw [e1, e2]
  have e2 := H f2 ⟨1, fun _ => {c}, fun _ z => decide (z c ≠ b), fun _ => by simp,
    fun bit => (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp; omega),
    fun i x y hxy => by simp [hxy c (by simp)], fun z => by simp [f2]⟩ (by omega)
  have e1 := H f1 ⟨n, fun l => if l ∈ S.erase c then {c, l} else ∅, row1, ?_, ?_, ?_,
    fun z => by simp only [f1]; exact decide_eq_true_iff⟩ (by omega)
  · rw [hlab] at e1
    have := e2.mp (e1.mpr (by omega))
    omega
  · intro l
    dsimp only
    split_ifs
    · exact Finset.card_le_two
    · simp
  · intro bit
    by_cases hbit : bit = c
    · subst hbit
      refine (Finset.card_le_card ?_).trans hc
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      split_ifs at hl with h
      · exact h
      · simp at hl
    · refine (Finset.card_le_card (t := {bit}) ?_).trans (by simp; omega)
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      split_ifs at hl with h
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with hl | hl
        · exact absurd hl hbit
        · simp [hl]
      · simp at hl
  · intro l x y hxy
    by_cases h : l ∈ S.erase c
    · simp only [h, ite_true] at hxy
      have hx1 : x c = y c := hxy c (by simp)
      have hx2 : x l = y l := hxy l (by simp)
      simp only [row1, h, ite_true, hx1, hx2]
    · simp only [row1, h, ite_false]

theorem fiber_bound (n k : ℕ) (hkn : k + 1 < n) (pool : Finset (Fin n → Bool))
    (hc : ∀ S : Finset (Fin n), S.card ≤ k + 1 + 1 → ∀ pat : Fin n → Bool,
      ∃ word ∈ pool, ∀ j ∈ S, word j = pat j)
    (r : Fin k → Bool) :
    Nat.clog 2 (2 * (n - k) + 2) ≤
      (pool.filter (fun q => (fun i : Fin k => q ⟨i.val, by have := i.isLt; omega⟩) = r)).card := by
  have pick : ∀ (a b : Fin n), k ≤ a.val → k ≤ b.val → ∀ va vb : Bool, (a = b → va = vb) →
      ∃ q ∈ pool.filter (fun q => (fun i : Fin k => q ⟨i.val, by have := i.isLt; omega⟩) = r),
        q a = va ∧ q b = vb := by
    intro a b ha hb va vb hab
    let pat : Fin n → Bool := fun j =>
      if h : j.val < k then r ⟨j.val, h⟩ else if j = a then va else vb
    let emb : Fin k ↪ Fin n := ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩,
      fun i j h => by ext; simpa using congrArg Fin.val h⟩
    let S : Finset (Fin n) := (Finset.univ.map emb) ∪ {a, b}
    have hS : S.card ≤ k + 1 + 1 := by
      calc S.card ≤ (Finset.univ.map emb).card + ({a, b} : Finset (Fin n)).card :=
            Finset.card_union_le _ _
        _ ≤ k + 2 := by
            have := (Finset.card_le_two : ({a, b} : Finset (Fin n)).card ≤ 2)
            simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]; omega
        _ = k + 1 + 1 := by omega
    obtain ⟨q, hq, hqS⟩ := hc S hS pat
    refine ⟨q, ?_, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      refine ⟨hq, ?_⟩
      funext i
      have hm : (⟨i.val, by have := i.isLt; omega⟩ : Fin n) ∈ S :=
        Finset.mem_union_left _ (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      rw [hqS _ hm]
      simp [pat]
    · rw [hqS a (Finset.mem_union_right _ (by simp))]
      simp [pat, show ¬ a.val < k by omega]
    · rw [hqS b (Finset.mem_union_right _ (by simp))]
      by_cases hba : b = a
      · subst hba; simp [pat, show ¬ b.val < k by omega, hab rfl]
      · simp [pat, show ¬ b.val < k by omega, hba]
  set P := pool.filter (fun q => (fun i : Fin k => q ⟨i.val, by have := i.isLt; omega⟩) = r)
    with hP
  let φ : (Fin (n - k) × Bool) ⊕ Bool → (↥P → Bool) := fun x =>
    match x with
    | Sum.inl (j, f) => fun q => xor (q.val ⟨k + j.val, by have := j.isLt; omega⟩) f
    | Sum.inr c => fun _ => c
  have hφ : Function.Injective φ := by
    intro x y hxy
    rcases x with ⟨j, f⟩ | c <;> rcases y with ⟨j', f'⟩ | c'
    · by_cases hj : j = j'
      · subst hj
        obtain ⟨q, hq, h1, -⟩ := pick ⟨k + j.val, by have := j.isLt; omega⟩
          ⟨k + j.val, by have := j.isLt; omega⟩ (by simp) (by simp) false false (fun _ => rfl)
        have := congrFun hxy ⟨q, hq⟩
        simp only [φ] at this
        rw [h1] at this
        cases f <;> cases f' <;> simp_all
      · exfalso
        obtain ⟨q, hq, h1, h2⟩ := pick ⟨k + j.val, by have := j.isLt; omega⟩
          ⟨k + j'.val, by have := j'.isLt; omega⟩ (by simp) (by simp) f (!f')
          (fun h => absurd (Fin.ext (by simpa using congrArg Fin.val h)) hj)
        have := congrFun hxy ⟨q, hq⟩
        simp only [φ] at this
        rw [h1, h2] at this
        cases f <;> cases f' <;> simp_all
    · exfalso
      obtain ⟨q, hq, h1, -⟩ := pick ⟨k + j.val, by have := j.isLt; omega⟩
        ⟨k + j.val, by have := j.isLt; omega⟩ (by simp) (by simp) (xor (!c') f) (xor (!c') f)
        (fun _ => rfl)
      have := congrFun hxy ⟨q, hq⟩
      simp only [φ] at this
      rw [h1] at this
      cases f <;> cases c' <;> simp_all
    · exfalso
      obtain ⟨q, hq, h1, -⟩ := pick ⟨k + j'.val, by have := j'.isLt; omega⟩
        ⟨k + j'.val, by have := j'.isLt; omega⟩ (by simp) (by simp) (xor (!c) f') (xor (!c) f')
        (fun _ => rfl)
      have := congrFun hxy ⟨q, hq⟩
      simp only [φ] at this
      rw [h1] at this
      revert this
      cases f' <;> cases c <;> decide
    · obtain ⟨q, hq, -, -⟩ := pick ⟨k, by omega⟩ ⟨k, by omega⟩ (le_refl _) (le_refl _)
        false false (fun _ => rfl)
      have := congrFun hxy ⟨q, hq⟩
      simp only [φ] at this
      rw [this]
  have key := Fintype.card_le_of_injective φ hφ
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_fun, Fintype.card_coe] at key
  apply Nat.clog_le_of_le_pow
  linarith

end PEqualNP.Outside.L_lib_414_aux

open PEqualNP.Outside.L_lib_414_aux in
theorem PEqualNP.Outside.L_lib_414 :
    ∀ (n d : ℕ), 0 < d → d < n →
      let W := Fin n → Bool
      let hasRows := fun (f : W → Bool) =>
        ∃ (m : ℕ) (scope : Fin m → Finset (Fin n)) (row : Fin m → W → Bool),
          (∀ i, (scope i).card ≤ 2) ∧
          (∀ bit : Fin n, (Finset.univ.filter (fun i => bit ∈ scope i)).card ≤ d) ∧
          (∀ i x y, (∀ j ∈ scope i, x j = y j) → row i x = row i y) ∧
          (∀ z, f z = true ↔ ∀ i, row i z = true)
      ∀ (pool : Finset W) (classify : (↥pool → Bool) → Bool),
        (∀ f : W → Bool, hasRows f →
          let N := (Finset.univ.filter (fun w => f w = true)).card
          2 ^ n ≤ 2 * N →
            (classify (fun q => f q.val) = true ↔ 2 ^ n < 2 * N)) →
        (∀ S : Finset (Fin n), S.card ≤ d + 1 → ∀ pat : W,
          ∃ word ∈ pool, ∀ j ∈ S, word j = pat j) ∧
        2 ^ (d + 1) ≤ pool.card ∧
        2 ^ (d - 1) * Nat.clog 2 (2 * (n - (d - 1)) + 2) ≤ pool.card := by
  intro n d hd hdn W hasRows pool classify H
  have hc := cover n d hd hdn pool classify H
  refine ⟨hc, ?_, ?_⟩
  · -- distinct patterns on the first d+1 bits need distinct pool words
    let emb : Fin (d + 1) ↪ Fin n := ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩,
      fun i j h => by ext; simpa using congrArg Fin.val h⟩
    have hS : (Finset.univ.map emb).card ≤ d + 1 := by simp
    let g : (Fin (d + 1) → Bool) → ↥pool := fun r =>
      ⟨(hc _ hS (fun j => if h : j.val < d + 1 then r ⟨j.val, h⟩ else false)).choose,
        (hc _ hS (fun j => if h : j.val < d + 1 then r ⟨j.val, h⟩ else false)).choose_spec.1⟩
    have hg : Function.Injective g := by
      intro r r' h
      funext i
      have hm : emb i ∈ Finset.univ.map emb := Finset.mem_map_of_mem _ (Finset.mem_univ _)
      have e1 := (hc _ hS (fun j => if h : j.val < d + 1 then r ⟨j.val, h⟩ else false)).choose_spec.2
        _ hm
      have e2 := (hc _ hS (fun j => if h : j.val < d + 1 then r' ⟨j.val, h⟩ else false)).choose_spec.2
        _ hm
      have h' := congrArg Subtype.val h
      simp only [g] at h'
      rw [h'] at e1
      rw [e1] at e2
      have hi : (emb i).val < d + 1 := i.isLt
      simp only [dite_eq_left, hi] at e2
      exact e2
    have := Fintype.card_le_of_injective g hg
    simpa using this
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hcard : pool.card = ∑ r : Fin k → Bool,
        (pool.filter (fun q => (fun i : Fin k => q ⟨i.val, by have := i.isLt; omega⟩) = r)).card :=
      Finset.card_eq_sum_card_fiberwise (fun q _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    rw [hcard]
    calc 2 ^ k * Nat.clog 2 (2 * (n - k) + 2)
        = ∑ _r : Fin k → Bool, Nat.clog 2 (2 * (n - k) + 2) := by
          simp [Finset.sum_const, Finset.card_univ]
      _ ≤ _ := Finset.sum_le_sum (fun r _ => fiber_bound n k hdn pool hc r)
