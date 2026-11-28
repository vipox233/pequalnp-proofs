import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace PEqualNP.Outside.L_lib_1178_aux

open scoped BigOperators

section Farkas

theorem fm_farkas : ∀ (c : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Fin c → ℚ) (b : ι → ℚ),
    (∃ x : Fin c → ℚ, ∀ i, ∑ j, A i j * x j ≤ b i) ∨
    (∃ u : ι → ℚ, (∀ i, 0 ≤ u i) ∧ (∀ j, ∑ i, u i * A i j = 0) ∧ ∑ i, u i * b i < 0) := by
  intro c
  induction c with
  | zero =>
    intro ι _ _ A b
    by_cases h : ∀ i : ι, 0 ≤ b i
    · left
      exact ⟨Fin.elim0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i0, hi0⟩ := h
      refine ⟨fun i => if i = i0 then 1 else 0, ?_, ?_, ?_⟩
      · intro i; dsimp only; split_ifs <;> norm_num
      · intro j; exact j.elim0
      · simpa using hi0
  | succ c ih =>
    intro ι _ _ A b
    let a : ι → ℚ := fun i => A i 0
    let A' : ι → Fin c → ℚ := fun i j => A i j.succ
    let P := { i : ι // 0 < a i }
    let N := { i : ι // a i < 0 }
    let Z := { i : ι // a i = 0 }
    let ι' := Z ⊕ (P × N)
    let Anew : ι' → Fin c → ℚ := fun e j =>
      match e with
      | Sum.inl i => A' i.1 j
      | Sum.inr (i, k) => (-a k.1) * A' i.1 j + a i.1 * A' k.1 j
    let bnew : ι' → ℚ := fun e =>
      match e with
      | Sum.inl i => b i.1
      | Sum.inr (i, k) => (-a k.1) * b i.1 + a i.1 * b k.1
    rcases ih Anew bnew with ⟨x', hx'⟩ | ⟨u', hu'_nn, hu'_col, hu'_rhs⟩
    · left
      let U : P → ℚ := fun i => (b i.1 - ∑ j, A' i.1 j * x' j) / a i.1
      let L : N → ℚ := fun k => (b k.1 - ∑ j, A' k.1 j * x' j) / a k.1
      have hLU : ∀ (i : P) (k : N), L k ≤ U i := by
        intro i k
        have hpair := hx' (Sum.inr (i, k))
        simp only [Anew, bnew, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hpair
        have hai : 0 < a i.1 := i.2
        have hak : 0 < -a k.1 := by linarith [k.2]
        have hcross : (-a k.1) * (∑ j, A' i.1 j * x' j - b i.1) + a i.1 * (∑ j, A' k.1 j * x' j - b k.1) ≤ 0 := by
          linarith
        have h1 : L k = (∑ j, A' k.1 j * x' j - b k.1) / (-a k.1) := by
          dsimp [L]
          field_simp [ne_of_lt k.2, ne_of_gt hak]
          ring
        rw [h1]
        dsimp [U]
        rw [div_le_div_iff₀ hak hai]
        linarith
      have hx0 : ∃ x0 : ℚ, (∀ i : P, x0 ≤ U i) ∧ (∀ k : N, L k ≤ x0) := by
        by_cases hP : (Finset.univ : Finset P).Nonempty
        · obtain ⟨i0, _, hi0⟩ := Finset.exists_min_image (Finset.univ : Finset P) U hP
          exact ⟨U i0, fun i => hi0 i (Finset.mem_univ i), fun k => hLU i0 k⟩
        · by_cases hN : (Finset.univ : Finset N).Nonempty
          · obtain ⟨k0, _, hk0⟩ := Finset.exists_max_image (Finset.univ : Finset N) L hN
            refine ⟨L k0, fun i => (hP ⟨i, Finset.mem_univ i⟩).elim, fun k => hk0 k (Finset.mem_univ k)⟩
          · exact ⟨0, fun i => (hP ⟨i, Finset.mem_univ i⟩).elim, fun k => (hN ⟨k, Finset.mem_univ k⟩).elim⟩
      obtain ⟨x0, hx0U, hx0L⟩ := hx0
      refine ⟨Fin.cons x0 x', fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      change a i * x0 + ∑ j : Fin c, A' i j * x' j ≤ b i
      rcases lt_trichotomy (a i) 0 with hneg | hzero | hpos
      · have hle := hx0L ⟨i, hneg⟩
        dsimp [L] at hle
        have hmul := mul_le_mul_of_nonpos_left hle (le_of_lt hneg)
        have hne : a i ≠ 0 := ne_of_lt hneg
        have hcancel : a i * ((b i - ∑ j, A' i j * x' j) / a i) = b i - ∑ j, A' i j * x' j :=
          mul_div_cancel₀ _ hne
        linarith
      · have hz := hx' (Sum.inl ⟨i, hzero⟩)
        dsimp [Anew, bnew] at hz
        rw [hzero, zero_mul, zero_add]
        exact hz
      · have hle := hx0U ⟨i, hpos⟩
        dsimp [U] at hle
        have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hpos)
        have hne : a i ≠ 0 := ne_of_gt hpos
        have hcancel : a i * ((b i - ∑ j, A' i j * x' j) / a i) = b i - ∑ j, A' i j * x' j :=
          mul_div_cancel₀ _ hne
        linarith
    · right
      let u : ι → ℚ := fun i =>
        if h0 : a i = 0 then u' (Sum.inl ⟨i, h0⟩)
        else if hp : 0 < a i then ∑ k : N, (-a k.1) * u' (Sum.inr (⟨i, hp⟩, k))
        else ∑ p : P, a p.1 * u' (Sum.inr (p, ⟨i, lt_of_le_of_ne (not_lt.mp hp) h0⟩))
      have hu_nn : ∀ i, 0 ≤ u i := by
        intro i
        dsimp [u]
        split_ifs with h0 hp
        · exact hu'_nn _
        · exact Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [k.2]) (hu'_nn _)
        · exact Finset.sum_nonneg fun p _ => mul_nonneg (le_of_lt p.2) (hu'_nn _)
      have hsplit : ∀ f : ι → ℚ,
          ∑ i : ι, u i * f i =
            (∑ i : Z, u' (Sum.inl i) * f i.1) +
            (∑ p : P, ∑ k : N, u' (Sum.inr (p, k)) * ((-a k.1) * f p.1 + a p.1 * f k.1)) := by
        intro f
        have hpart :
            ∑ i : ι, u i * f i =
              (∑ i ∈ Finset.univ.filter (fun i : ι => a i = 0), u i * f i) +
              (∑ i ∈ Finset.univ.filter (fun i : ι => 0 < a i), u i * f i) +
              (∑ i ∈ Finset.univ.filter (fun i : ι => a i < 0), u i * f i) := by
          have h1 := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ι)
            (fun i => a i = 0) (fun i => u i * f i)).symm
          rw [h1]
          have h2 := (Finset.sum_filter_add_sum_filter_not
            (Finset.univ.filter (fun i : ι => ¬a i = 0))
            (fun i => 0 < a i) (fun i => u i * f i)).symm
          rw [h2, ← add_assoc]
          congr 1
          · congr 1
            refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨ne_of_gt h, h⟩⟩
          · refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨fun ⟨h1, h2⟩ => lt_of_le_of_ne (not_lt.mp h2) h1, fun h => ⟨ne_of_lt h, not_lt.mpr (le_of_lt h)⟩⟩
        rw [hpart]
        have hZ : ∑ i ∈ Finset.univ.filter (fun i : ι => a i = 0), u i * f i =
            ∑ i : Z, u' (Sum.inl i) * f i.1 := by
          rw [Finset.sum_subtype (Finset.univ.filter (fun i : ι => a i = 0))
            (p := fun i => a i = 0) (fun i => by simp)]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [u, i.2, ↓reduceDIte]
        have hP : ∑ i ∈ Finset.univ.filter (fun i : ι => 0 < a i), u i * f i =
            ∑ p : P, ∑ k : N, u' (Sum.inr (p, k)) * ((-a k.1) * f p.1) := by
          rw [Finset.sum_subtype (Finset.univ.filter (fun i : ι => 0 < a i))
            (p := fun i => 0 < a i) (fun i => by simp)]
          refine Finset.sum_congr rfl fun p _ => ?_
          simp only [u, ne_of_gt p.2, p.2, ↓reduceDIte, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => by ring
        have hN : ∑ i ∈ Finset.univ.filter (fun i : ι => a i < 0), u i * f i =
            ∑ p : P, ∑ k : N, u' (Sum.inr (p, k)) * (a p.1 * f k.1) := by
          rw [Finset.sum_subtype (Finset.univ.filter (fun i : ι => a i < 0))
            (p := fun i => a i < 0) (fun i => by simp), Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [u, ne_of_lt k.2, not_lt.mpr (le_of_lt k.2), ↓reduceDIte, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => by ring
        rw [hZ, hP, hN, add_assoc]
        congr 1
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      have hcol : ∀ j : Fin (c + 1), ∑ i : ι, u i * A i j = 0 := by
        intro j
        refine Fin.cases ?_ ?_ j
        · rw [hsplit (fun i => A i 0)]
          have hz0 : ∑ i : Z, u' (Sum.inl i) * a i.1 = 0 :=
            Finset.sum_eq_zero fun i _ => by rw [i.2, mul_zero]
          have hpn0 : ∑ p : P, ∑ k : N, u' (Sum.inr (p, k)) * ((-a k.1) * a p.1 + a p.1 * a k.1) = 0 :=
            Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun k _ => by ring
          change (∑ i : Z, u' (Sum.inl i) * a i.1) +
            (∑ p : P, ∑ k : N, u' (Sum.inr (p, k)) * ((-a k.1) * a p.1 + a p.1 * a k.1)) = 0
          rw [hz0, hpn0, add_zero]
        · intro j'
          rw [hsplit (fun i => A i j'.succ)]
          have heq := hu'_col j'
          rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at heq
          exact heq
      have hrhs : ∑ i : ι, u i * b i < 0 := by
        rw [hsplit b]
        have hlt := hu'_rhs
        rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at hlt
        exact hlt
      exact ⟨u, hu_nn, hcol, hrhs⟩

theorem rational_minimax {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Nonempty β] (M : β → α → ℚ) (c : ℚ)
    (h : ∀ w : α → ℚ, (∀ x, 0 ≤ w x) → ∃ m : β, ∑ x, w x * M m x ≤ c * ∑ x, w x) :
    ∃ p : β → ℚ, (∀ m, 0 ≤ p m) ∧ (∑ m, p m = 1) ∧ ∀ x, ∑ m, p m * M m x ≤ c := by
  let e := Fintype.equivFin β
  let ι := α ⊕ β ⊕ Bool
  let A : ι → Fin (Fintype.card β) → ℚ := fun i j =>
    match i with
    | Sum.inl x => M (e.symm j) x
    | Sum.inr (Sum.inl m) => if e m = j then -1 else 0
    | Sum.inr (Sum.inr false) => 1
    | Sum.inr (Sum.inr true) => -1
  let b : ι → ℚ := fun i =>
    match i with
    | Sum.inl _ => c
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr false) => 1
    | Sum.inr (Sum.inr true) => -1
  rcases fm_farkas (Fintype.card β) A b with ⟨x, hx⟩ | ⟨u, hu_nn, hu_col, hu_rhs⟩
  · let p : β → ℚ := fun m => x (e m)
    refine ⟨p, ?_, ?_, ?_⟩
    · intro m
      have h1 := hx (Sum.inr (Sum.inl m))
      simp only [A, b, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at h1
      linarith
    · have h1 := hx (Sum.inr (Sum.inr false))
      have h2 := hx (Sum.inr (Sum.inr true))
      simp only [A, b, one_mul, neg_mul, Finset.sum_neg_distrib] at h1 h2
      have hsum : ∑ m : β, p m = ∑ j : Fin (Fintype.card β), x j :=
        Fintype.sum_equiv e p x (fun m => rfl)
      linarith
    · intro a
      have h1 := hx (Sum.inl a)
      dsimp [A, b] at h1
      have hsum : ∑ m : β, p m * M m a = ∑ j : Fin (Fintype.card β), M (e.symm j) a * x j :=
        Fintype.sum_equiv e (fun m => p m * M m a) (fun j => M (e.symm j) a * x j) (fun m => by
          dsimp [p]; rw [e.symm_apply_apply]; ring)
      linarith
  · exfalso
    let w : α → ℚ := fun x => u (Sum.inl x)
    have hw_nn : ∀ x, 0 ≤ w x := fun x => hu_nn (Sum.inl x)
    obtain ⟨m0, hm0⟩ := h w hw_nn
    have hcol := hu_col (e m0)
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_bool] at hcol
    simp only [A, e.apply_eq_iff_eq, mul_ite, mul_neg, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, e.symm_apply_apply] at hcol
    have hlam : 0 ≤ u (Sum.inr (Sum.inl m0)) := hu_nn _
    have hlb : u (Sum.inr (Sum.inr true)) - u (Sum.inr (Sum.inr false)) ≤ ∑ x : α, w x * M m0 x := by
      dsimp [w]; linarith
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_bool] at hu_rhs
    simp only [b, mul_zero, Finset.sum_const_zero, zero_add, mul_one, mul_neg] at hu_rhs
    have hub : c * ∑ x : α, w x < u (Sum.inr (Sum.inr true)) - u (Sum.inr (Sum.inr false)) := by
      rw [Finset.mul_sum]
      have hsw : ∑ x : α, c * w x = ∑ x : α, u (Sum.inl x) * c :=
        Finset.sum_congr rfl fun x _ => by dsimp [w]; ring
      linarith
    linarith

end Farkas

section Protocol

variable {n t d : ℕ} (scope : Fin t → Finset (Fin n))

abbrev Word (n d : ℕ) := Fin n → Fin (d + 2)
abbrev Signing (n t d : ℕ) := Fin t → Word n d

noncomputable def pass (s : Signing n t d) (x : Word n d) : Bool :=
  (List.finRange t).all (fun j => (scope j).toList.any (fun v => x v != s j v))

noncomputable def reply (A : Finset (Word n d)) (s : Signing n t d) : Bool :=
  A.toList.any (pass scope s)

def admissible (X : Finset (Word n d)) : Prop :=
  ∀ j : Fin t, ∃ z : Word n d, ∀ x ∈ X, ∃ v ∈ scope j, x v ≠ z v

lemma pass_eq_true_iff (s : Signing n t d) (x : Word n d) :
    pass scope s x = true ↔ ∀ j : Fin t, ∃ v ∈ scope j, x v ≠ s j v := by
  simp only [pass, List.all_eq_true, List.mem_finRange, true_implies,
    List.any_eq_true, Finset.mem_toList, bne_iff_ne, ne_eq]

lemma reply_eq_true_iff (A : Finset (Word n d)) (s : Signing n t d) :
    reply scope A s = true ↔ ∃ x ∈ A, pass scope s x = true := by
  simp only [reply, List.any_eq_true, Finset.mem_toList]

lemma reply_empty (s : Signing n t d) : reply scope ∅ s = false := by
  cases h : reply scope ∅ s
  · rfl
  · obtain ⟨x, hx, _⟩ := (reply_eq_true_iff scope ∅ s).mp h
    exact (Finset.notMem_empty x hx).elim

lemma reply_singleton (x : Word n d) (s : Signing n t d) :
    reply scope {x} s = pass scope s x := by
  cases hp : pass scope s x
  · cases hr : reply scope {x} s
    · rfl
    · obtain ⟨y, hy, hpy⟩ := (reply_eq_true_iff scope {x} s).mp hr
      rw [Finset.mem_singleton] at hy
      subst hy; rw [hp] at hpy; contradiction
  · exact (reply_eq_true_iff scope {x} s).mpr ⟨x, Finset.mem_singleton_self x, hp⟩

lemma admissible_empty : admissible scope (∅ : Finset (Word n d)) := by
  intro j
  exact ⟨fun _ => 0, fun x hx => (Finset.notMem_empty x hx).elim⟩

lemma card_filter_add_not {α : Type} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ hp hnp => hnp hp)]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  by_cases hp : p x <;> simp [hp]

lemma admissible_of_signing (s : Signing n t d) (P : Finset (Word n d)) :
    admissible scope (P.filter (fun x => pass scope s x = true)) := by
  intro j
  refine ⟨s j, fun x hx => ?_⟩
  have hp : pass scope s x = true := (Finset.mem_filter.mp hx).2
  exact (pass_eq_true_iff scope s x).mp hp j

lemma exists_signing_of_admissible {X : Finset (Word n d)} (h : admissible scope X) :
    ∃ s : Signing n t d, ∀ x ∈ X, pass scope s x = true := by
  classical
  refine ⟨fun j => Classical.choose (h j), fun x hx => ?_⟩
  rw [pass_eq_true_iff]
  intro j
  exact Classical.choose_spec (h j) x hx

lemma foldl_all_false {k : ℕ} (f : Fin k → List Bool → Bool) :
    ∀ (l : List (Fin k)) (init : List Bool),
      (∀ (idx : ℕ) (h : idx < l.length), f l[idx] (init ++ List.replicate idx false) = false) →
      l.foldl (fun acc j => acc ++ [f j acc]) init = init ++ List.replicate l.length false := by
  intro l
  induction l with
  | nil => intro init _; simp
  | cons a tl ih =>
    intro init h
    simp only [List.foldl_cons, List.length_cons]
    have h0 : f a init = false := by
      have := h 0 (by simp)
      simpa using this
    rw [h0]
    have htl := ih (init ++ [false]) (fun idx hidx => by
      have := h (idx + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, List.replicate_succ, List.append_assoc] at this ⊢
      exact this)
    rw [htl]
    simp [List.replicate_succ, List.append_assoc]

lemma foldl_finRange_all_false {k : ℕ} (f : Fin k → List Bool → Bool)
    (hf : ∀ j : Fin k, f j (List.replicate j.val false) = false) :
    (List.finRange k).foldl (fun acc j => acc ++ [f j acc]) [] = List.replicate k false := by
  have h := foldl_all_false f (List.finRange k) [] (fun idx hidx => by
    simp only [List.length_finRange] at hidx
    simp only [List.nil_append, List.getElem_finRange]
    exact hf ⟨idx, hidx⟩)
  simpa using h

lemma foldl_any_false_of_all_false {k : ℕ} (f : Fin k → List Bool → Bool)
    (h : ((List.finRange k).foldl (fun acc j => acc ++ [f j acc]) []).any id = false) :
    ∀ j : Fin k, f j (List.replicate j.val false) = false := by
  have aux : ∀ (l : List (Fin k)) (init : List Bool),
      init.any id = false →
      (l.foldl (fun acc j => acc ++ [f j acc]) init).any id = false →
      ∀ (idx : ℕ) (hidx : idx < l.length), f l[idx] (init ++ List.replicate idx false) = false := by
    intro l
    induction l with
    | nil => intro _ _ _ _ hidx; simp at hidx
    | cons a tl ih =>
      intro init hinit hfold idx hidx
      simp only [List.foldl_cons] at hfold
      have hpref : ∀ (m : List (Fin k)) (acc : List Bool),
          acc.any id = true → (m.foldl (fun acc j => acc ++ [f j acc]) acc).any id = true := by
        intro m
        induction m with
        | nil => intro acc ha; exact ha
        | cons b m ihm =>
          intro acc ha
          simp only [List.foldl_cons]
          exact ihm _ (by simp [ha])
      have ha0 : f a init = false := by
        cases hfa : f a init
        · rfl
        · have ht : (init ++ [f a init]).any id = true := by simp [hfa]
          have := hpref tl (init ++ [f a init]) ht
          rw [this] at hfold; contradiction
      cases idx with
      | zero => simpa using ha0
      | succ idx' =>
        have hstep : (init ++ [f a init]).any id = false := by simp [hinit, ha0]
        have := ih (init ++ [f a init]) hstep hfold idx' (by simpa using hidx)
        rw [ha0] at this
        simpa [List.replicate_succ, List.append_assoc] using this
  intro j
  have h1 := aux (List.finRange k) [] rfl h j.val (by simp)
  simpa using h1

lemma fin_partition_exists {α : Type} [Fintype α] [DecidableEq α]
    (cnt : α → ℕ) (D : ℕ) (hsum : ∑ m : α, cnt m = D) :
    ∃ assign : Fin D → α, ∀ m : α, (Finset.univ.filter (fun u : Fin D => assign u = m)).card = cnt m := by
  classical
  have aux : ∀ (s : Finset α) (M : ℕ), s.sum cnt = M →
      ∃ assign : Fin M → α, (∀ m ∈ s, (Finset.univ.filter (fun u : Fin M => assign u = m)).card = cnt m) ∧
        (∀ u : Fin M, assign u ∈ s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro M hM
      simp only [Finset.sum_empty] at hM
      subst hM
      exact ⟨Fin.elim0, fun m hm => (Finset.notMem_empty m hm).elim, fun u => u.elim0⟩
    | insert a s ha ih =>
      intro M hM
      rw [Finset.sum_insert ha] at hM
      obtain ⟨assign', hcard', hmem'⟩ := ih (s.sum cnt) rfl
      let e : Fin M ≃ Fin (cnt a) ⊕ Fin (s.sum cnt) :=
        (finCongr hM.symm).trans finSumFinEquiv.symm
      let assign : Fin M → α := fun u =>
        match e u with
        | Sum.inl _ => a
        | Sum.inr v => assign' v
      refine ⟨assign, ?_, ?_⟩
      · intro m hm
        have hcard : (Finset.univ.filter (fun u : Fin M => assign u = m)).card =
            (Finset.univ.filter (fun z : Fin (cnt a) ⊕ Fin (s.sum cnt) =>
              (match z with | Sum.inl _ => a | Sum.inr v => assign' v) = m)).card := by
          refine Finset.card_bij (fun u _ => e u) ?_ ?_ ?_
          · intro u hu
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            exact hu
          · intro u1 _ u2 _ heq; exact e.injective heq
          · intro z hz
            refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
            simpa [assign] using hz
        rw [hcard]
        have hsum_card :
            (Finset.univ.filter (fun z : Fin (cnt a) ⊕ Fin (s.sum cnt) =>
              (match z with | Sum.inl _ => a | Sum.inr v => assign' v) = m)).card =
            (Finset.univ.filter (fun _ : Fin (cnt a) => a = m)).card +
            (Finset.univ.filter (fun v : Fin (s.sum cnt) => assign' v = m)).card := by
          let S1 : Finset (Fin (cnt a) ⊕ Fin (s.sum cnt)) :=
            (Finset.univ.filter (fun _ : Fin (cnt a) => a = m)).map ⟨Sum.inl, Sum.inl_injective⟩
          let S2 : Finset (Fin (cnt a) ⊕ Fin (s.sum cnt)) :=
            (Finset.univ.filter (fun v : Fin (s.sum cnt) => assign' v = m)).map ⟨Sum.inr, Sum.inr_injective⟩
          have h1 : S1.card = (Finset.univ.filter (fun _ : Fin (cnt a) => a = m)).card := Finset.card_map _
          have h2 : S2.card = (Finset.univ.filter (fun v : Fin (s.sum cnt) => assign' v = m)).card := Finset.card_map _
          rw [← h1, ← h2, ← Finset.card_union_of_disjoint]
          · congr 1
            ext z
            cases z with
            | inl x => by_cases ham : a = m <;> simp [S1, S2, ham]
            | inr y => simp [S1, S2]
          · rw [Finset.disjoint_left]
            intro z hz1 hz2
            simp only [S1, S2, Finset.mem_map, Function.Embedding.coeFn_mk] at hz1 hz2
            obtain ⟨_, _, rfl⟩ := hz1
            obtain ⟨_, _, hne⟩ := hz2
            exact Sum.inl_ne_inr hne.symm
        rw [hsum_card]
        rcases Finset.mem_insert.mp hm with rfl | hms
        · have hzero : (Finset.univ.filter (fun v : Fin (s.sum cnt) => assign' v = m)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro v _ heq
            exact ha (heq ▸ hmem' v)
          simp [hzero]
        · have hne : a ≠ m := fun heq => ha (heq ▸ hms)
          simp [hne, hcard' m hms]
      · intro u
        dsimp [assign]
        cases e u with
        | inl _ => exact Finset.mem_insert_self a s
        | inr v => exact Finset.mem_insert_of_mem (hmem' v)
  obtain ⟨assign, hcard, _⟩ := aux Finset.univ D hsum
  exact ⟨assign, fun m => hcard m (Finset.mem_univ m)⟩

lemma main_thm (P : Finset (Word n d)) (k a b q : ℕ) (hq : 0 < q) (ha : a ≤ q) (hb : b ≤ q) :
    ((∃ N : ℕ, 0 < N ∧
      ∃ ask : Fin N → Fin k → List Bool → Signing n t d, ∃ answer : Fin N → List Bool → Bool,
        ∀ A : Finset (Word n d), A ⊆ P →
          let yes := ((Finset.univ : Finset (Fin N)).filter (fun seed =>
            answer seed ((List.finRange k).foldl (fun h j =>
              h ++ [reply scope A (ask seed j h)]) ([] : List Bool)))).card
          if A.Nonempty then q * (N - yes) ≤ b * N else q * yes ≤ a * N) ↔
    ∀ w : Word n d → ℕ, ∃ X : Fin k → Finset (Word n d),
      (∀ i, X i ⊆ P ∧ admissible scope (X i)) ∧
      (q - a) * ((P.filter (fun x => ∀ i, x ∉ X i)).sum w) ≤ b * (P.sum w)) := by
  classical
  constructor
  · rintro ⟨N, hN, ask, answer, hproto⟩ w
    by_cases haq : a = q
    · refine ⟨fun _ => ∅, fun _ => ⟨Finset.empty_subset P, admissible_empty scope⟩, ?_⟩
      simp [haq]
    have ha_lt : a < q := lt_of_le_of_ne ha haq
    let run : Fin N → Finset (Word n d) → Bool := fun seed A =>
      answer seed ((List.finRange k).foldl (fun h j => h ++ [reply scope A (ask seed j h)]) [])
    let R : Finset (Fin N) := Finset.univ.filter (fun seed => run seed ∅ = false)
    have hempty := hproto ∅ (Finset.empty_subset P)
    simp only [Finset.not_nonempty_empty, ↓reduceIte] at hempty
    have hR_comp : ((Finset.univ : Finset (Fin N)).filter (fun seed => run seed ∅ = true)).card + R.card = N := by
      have := card_filter_add_not (Finset.univ : Finset (Fin N)) (fun seed => run seed ∅ = true)
      simpa [R, Bool.not_eq_true] using this
    have hR_bound : (q - a) * N ≤ q * R.card := by
      have h1 : q * ((Finset.univ : Finset (Fin N)).filter (fun seed => run seed ∅ = true)).card ≤ a * N := by
        simpa [run] using hempty
      have h2 : q * ((Finset.univ : Finset (Fin N)).filter (fun seed => run seed ∅ = true)).card + q * R.card = q * N := by
        rw [← mul_add, hR_comp]
      have h3 : (q - a) * N + a * N = q * N := by
        rw [← add_mul, Nat.sub_add_cancel ha]
      omega
    have hR_ne : R.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hRe
      rw [hRe, Finset.card_empty, mul_zero] at hR_bound
      have hpos : 0 < (q - a) * N := Nat.mul_pos (Nat.sub_pos_of_lt ha_lt) hN
      omega
    let menu : Fin N → Fin k → Finset (Word n d) := fun seed i =>
      P.filter (fun x => pass scope (ask seed i (List.replicate i.val false)) x = true)
    let missSum : Fin N → ℕ := fun seed => (P.filter (fun x => ∀ i, x ∉ menu seed i)).sum w
    have hseed_miss : ∀ x ∈ P, ∀ seed ∈ R, (∀ i, x ∉ menu seed i) → run seed {x} = false := by
      intro x hxP seed hseed hmiss
      have h0 : (List.finRange k).foldl (fun h j => h ++ [reply scope ∅ (ask seed j h)]) [] =
          List.replicate k false :=
        foldl_finRange_all_false _ (fun j => reply_empty scope _)
      have hx_path : (List.finRange k).foldl (fun h j => h ++ [reply scope {x} (ask seed j h)]) [] =
          List.replicate k false := by
        refine foldl_finRange_all_false _ (fun j => ?_)
        rw [reply_singleton]
        have hm := hmiss j
        simp only [menu, Finset.mem_filter, hxP, true_and] at hm
        cases hp : pass scope (ask seed j (List.replicate j.val false)) x
        · rfl
        · exact (hm hp).elim
      have hr0 : run seed ∅ = false := (Finset.mem_filter.mp hseed).2
      dsimp [run] at hr0 ⊢
      rw [hx_path, ← h0]
      exact hr0
    have hpoint : ∀ x ∈ P,
        q * (R.filter (fun seed => ∀ i, x ∉ menu seed i)).card ≤ b * N := by
      intro x hxP
      have hsing := hproto {x} (Finset.singleton_subset_iff.mpr hxP)
      simp only [Finset.singleton_nonempty, ↓reduceIte] at hsing
      have hcard_le : (R.filter (fun seed => ∀ i, x ∉ menu seed i)).card ≤
          N - ((Finset.univ : Finset (Fin N)).filter (fun seed => run seed {x} = true)).card := by
        have hcomp : ((Finset.univ : Finset (Fin N)).filter (fun seed => run seed {x} = true)).card +
            ((Finset.univ : Finset (Fin N)).filter (fun seed => run seed {x} = false)).card = N := by
          have := card_filter_add_not (Finset.univ : Finset (Fin N)) (fun seed => run seed {x} = true)
          simpa [Bool.not_eq_true] using this
        have hsub : R.filter (fun seed => ∀ i, x ∉ menu seed i) ⊆
            Finset.univ.filter (fun seed => run seed {x} = false) := by
          intro seed hseed
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hseed ⊢
          exact hseed_miss x hxP seed hseed.1 hseed.2
        have hle := Finset.card_le_card hsub
        omega
      calc q * (R.filter (fun seed => ∀ i, x ∉ menu seed i)).card
          ≤ q * (N - ((Finset.univ : Finset (Fin N)).filter (fun seed => run seed {x} = true)).card) :=
            Nat.mul_le_mul_left q hcard_le
        _ ≤ b * N := by simpa [run] using hsing
    have hsum_swap : R.sum missSum =
        P.sum (fun x => (R.filter (fun seed => ∀ i, x ∉ menu seed i)).card * w x) := by
      dsimp [missSum]
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [Finset.sum_ite, Finset.sum_const, smul_eq_mul]
    have havg : q * R.sum missSum ≤ b * N * P.sum w := by
      rw [hsum_swap, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x hxP => ?_
      have hx := hpoint x hxP
      calc q * ((R.filter (fun seed => ∀ i, x ∉ menu seed i)).card * w x)
          = (q * (R.filter (fun seed => ∀ i, x ∉ menu seed i)).card) * w x := by ring
        _ ≤ (b * N) * w x := Nat.mul_le_mul_right (w x) hx
    obtain ⟨seed0, hseed0R, hmin⟩ := Finset.exists_min_image R missSum hR_ne
    have hmin_sum : R.card * missSum seed0 ≤ R.sum missSum := by
      calc R.card * missSum seed0 = R.sum (fun _ => missSum seed0) := by simp
        _ ≤ R.sum missSum := Finset.sum_le_sum fun s hs => hmin s hs
    have hmul : (q - a) * N * missSum seed0 ≤ b * N * P.sum w := by
      calc (q - a) * N * missSum seed0
          ≤ (q * R.card) * missSum seed0 := Nat.mul_le_mul_right _ hR_bound
        _ = q * (R.card * missSum seed0) := by ring
        _ ≤ q * R.sum missSum := Nat.mul_le_mul_left q hmin_sum
        _ ≤ b * N * P.sum w := havg
    have hfinal : (q - a) * missSum seed0 ≤ b * P.sum w := by
      have hmul' : N * ((q - a) * missSum seed0) ≤ N * (b * P.sum w) := by
        linarith
      exact Nat.le_of_mul_le_mul_left hmul' hN
    refine ⟨menu seed0, fun i => ⟨Finset.filter_subset _ P, admissible_of_signing scope _ P⟩, hfinal⟩
  · intro hcov
    by_cases haq : a = q
    · refine ⟨1, Nat.one_pos, fun _ _ _ => fun _ _ => 0, fun _ _ => true, fun A _ => ?_⟩
      split_ifs
      · simp
      · simp [haq]
    have ha_lt : a < q := lt_of_le_of_ne ha haq
    by_cases hPe : P = ∅
    · refine ⟨1, Nat.one_pos, fun _ _ _ => fun _ _ => 0, fun _ _ => false, fun A hAP => ?_⟩
      have hAe : A = ∅ := Finset.subset_empty.mp (hPe ▸ hAP)
      subst hAe
      simp
    let Menu := { X : Fin k → Finset (Word n d) // ∀ i, X i ⊆ P ∧ admissible scope (X i) }
    have : Nonempty Menu := ⟨⟨fun _ => ∅, fun _ => ⟨Finset.empty_subset P, admissible_empty scope⟩⟩⟩
    let α := { x : Word n d // x ∈ P }
    let M : Menu → α → ℚ := fun m x => if ∀ i, x.1 ∉ m.1 i then 1 else 0
    let c : ℚ := (b : ℚ) / ((q - a : ℕ) : ℚ)
    have hqa_pos : (0 : ℚ) < ((q - a : ℕ) : ℚ) := by
      exact_mod_cast Nat.sub_pos_of_lt ha_lt
    have hminimax_hyp : ∀ w : α → ℚ, (∀ x, 0 ≤ w x) → ∃ m : Menu, ∑ x, w x * M m x ≤ c * ∑ x, w x := by
      intro w hw_nn
      let D : ℕ := ∏ x : α, (w x).den
      have hD_pos : 0 < D := Finset.prod_pos fun x _ => (w x).pos
      have hD_pos_q : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD_pos
      have hdiv : ∀ x : α, (w x).den ∣ D := fun x =>
        Finset.dvd_prod_of_mem (fun y : α => (w y).den) (Finset.mem_univ x)
      let W : Word n d → ℕ := fun z =>
        if hz : z ∈ P then (w ⟨z, hz⟩).num.toNat * (D / (w ⟨z, hz⟩).den) else 0
      have hW_eq : ∀ x : α, (W x.1 : ℚ) = (D : ℚ) * w x := by
        intro x
        have hW_val : W x.1 = (w x).num.toNat * (D / (w x).den) := by
          simp only [W, x.2, ↓reduceDIte]
          rfl
        have hnum_nn : 0 ≤ (w x).num := Rat.num_nonneg.mpr (hw_nn x)
        have hcast : ((w x).num.toNat : ℚ) = ((w x).num : ℚ) := by
          exact_mod_cast Int.toNat_of_nonneg hnum_nn
        have hmul_den : ((D / (w x).den : ℕ) : ℚ) * ((w x).den : ℚ) = (D : ℚ) := by
          exact_mod_cast Nat.div_mul_cancel (hdiv x)
        have hden_ne : ((w x).den : ℚ) ≠ 0 := by exact_mod_cast (w x).den_nz
        calc (W x.1 : ℚ)
            = ((w x).num.toNat : ℚ) * ((D / (w x).den : ℕ) : ℚ) := by rw [hW_val]; push_cast; rfl
          _ = ((w x).num : ℚ) * ((D / (w x).den : ℕ) : ℚ) := by rw [hcast]
          _ = ((w x).num : ℚ) / ((w x).den : ℚ) * (((D / (w x).den : ℕ) : ℚ) * ((w x).den : ℚ)) := by
                field_simp [hden_ne]
          _ = w x * (D : ℚ) := by rw [Rat.num_div_den, hmul_den]
          _ = (D : ℚ) * w x := mul_comm _ _
      obtain ⟨X, hX_ok, hX_ineq⟩ := hcov W
      refine ⟨⟨X, hX_ok⟩, ?_⟩
      have h1 : ((q - a : ℕ) : ℚ) * (((P.filter (fun x => ∀ i, x ∉ X i)).sum W : ℕ) : ℚ) ≤
          (b : ℚ) * ((P.sum W : ℕ) : ℚ) := by exact_mod_cast hX_ineq
      have hsumP : ((P.sum W : ℕ) : ℚ) = (D : ℚ) * ∑ x : α, w x := by
        rw [Nat.cast_sum, Finset.sum_subtype P (p := fun x => x ∈ P) (fun _ => Iff.rfl), Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => hW_eq x
      have hsumF : (((P.filter (fun x => ∀ i, x ∉ X i)).sum W : ℕ) : ℚ) =
          (D : ℚ) * ∑ x : α, w x * M ⟨X, hX_ok⟩ x := by
        rw [Finset.sum_filter, Nat.cast_sum, Finset.sum_subtype P (p := fun x => x ∈ P) (fun _ => Iff.rfl), Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        dsimp [M]
        by_cases hm : ∀ i, x.1 ∉ X i
        · rw [ite_cond_eq_true _ _ (eq_true hm), ite_cond_eq_true _ _ (eq_true hm), mul_one]
          exact hW_eq x
        · rw [ite_cond_eq_false _ _ (eq_false hm), ite_cond_eq_false _ _ (eq_false hm),
            Nat.cast_zero, mul_zero, mul_zero]
      rw [hsumP, hsumF] at h1
      have h2 : ((q - a : ℕ) : ℚ) * (∑ x : α, w x * M ⟨X, hX_ok⟩ x) ≤ (b : ℚ) * ∑ x : α, w x := by
        have h1' : (D : ℚ) * (((q - a : ℕ) : ℚ) * ∑ x : α, w x * M ⟨X, hX_ok⟩ x) ≤
            (D : ℚ) * ((b : ℚ) * ∑ x : α, w x) := by linarith
        exact le_of_mul_le_mul_left h1' hD_pos_q
      dsimp [c]
      rw [div_mul_eq_mul_div, le_div_iff₀ hqa_pos]
      linarith
    obtain ⟨p, hp_nn, hp_sum, hp_cov⟩ := rational_minimax M c hminimax_hyp
    let D : ℕ := ∏ m : Menu, (p m).den
    have hD_pos : 0 < D := Finset.prod_pos fun m _ => (p m).pos
    have hD_pos_q : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD_pos
    have hdiv : ∀ m : Menu, (p m).den ∣ D := fun m =>
      Finset.dvd_prod_of_mem (fun y : Menu => (p y).den) (Finset.mem_univ m)
    let cnt : Menu → ℕ := fun m => (p m).num.toNat * (D / (p m).den)
    have hcnt_eq : ∀ m : Menu, (cnt m : ℚ) = (D : ℚ) * p m := by
      intro m
      have hnum_nn : 0 ≤ (p m).num := Rat.num_nonneg.mpr (hp_nn m)
      have hcast : ((p m).num.toNat : ℚ) = ((p m).num : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg hnum_nn
      have hmul_den : ((D / (p m).den : ℕ) : ℚ) * ((p m).den : ℚ) = (D : ℚ) := by
        exact_mod_cast Nat.div_mul_cancel (hdiv m)
      have hden_ne : ((p m).den : ℚ) ≠ 0 := by exact_mod_cast (p m).den_nz
      calc (cnt m : ℚ)
          = ((p m).num.toNat : ℚ) * ((D / (p m).den : ℕ) : ℚ) := by dsimp [cnt]; push_cast; rfl
        _ = ((p m).num : ℚ) * ((D / (p m).den : ℕ) : ℚ) := by rw [hcast]
        _ = ((p m).num : ℚ) / ((p m).den : ℚ) * (((D / (p m).den : ℕ) : ℚ) * ((p m).den : ℚ)) := by
              field_simp [hden_ne]
        _ = p m * (D : ℚ) := by rw [Rat.num_div_den, hmul_den]
        _ = (D : ℚ) * p m := mul_comm _ _
    have hcnt_sum : ∑ m : Menu, cnt m = D := by
      have hq_eq : ((∑ m : Menu, cnt m : ℕ) : ℚ) = (D : ℚ) := by
        rw [Nat.cast_sum]
        calc ∑ m : Menu, (cnt m : ℚ) = ∑ m : Menu, (D : ℚ) * p m :=
              Finset.sum_congr rfl fun m _ => hcnt_eq m
          _ = (D : ℚ) * ∑ m : Menu, p m := (Finset.mul_sum _ _ _).symm
          _ = (D : ℚ) := by rw [hp_sum, mul_one]
      exact_mod_cast hq_eq
    have hcnt_cov : ∀ x : α,
        (q - a) * (∑ m : Menu, if ∀ i, x.1 ∉ m.1 i then cnt m else 0) ≤ b * D := by
      intro x
      have hx := hp_cov x
      dsimp [c] at hx
      rw [le_div_iff₀ hqa_pos] at hx
      have hxD : (D : ℚ) * ((∑ m : Menu, p m * M m x) * ((q - a : ℕ) : ℚ)) ≤ (D : ℚ) * (b : ℚ) :=
        mul_le_mul_of_nonneg_left hx (le_of_lt hD_pos_q)
      have hsumM : (D : ℚ) * ∑ m : Menu, p m * M m x =
          ((∑ m : Menu, if ∀ i, x.1 ∉ m.1 i then cnt m else 0 : ℕ) : ℚ) := by
        rw [Finset.mul_sum, Nat.cast_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        dsimp [M]
        split_ifs with hm
        · rw [mul_one, hcnt_eq m]
        · simp
      have hq_ineq : ((q - a : ℕ) : ℚ) * ((∑ m : Menu, if ∀ i, x.1 ∉ m.1 i then cnt m else 0 : ℕ) : ℚ) ≤
          (b : ℚ) * (D : ℚ) := by
        rw [← hsumM]
        calc ((q - a : ℕ) : ℚ) * ((D : ℚ) * ∑ m : Menu, p m * M m x)
            = (D : ℚ) * ((∑ m : Menu, p m * M m x) * ((q - a : ℕ) : ℚ)) := by ring
          _ ≤ (D : ℚ) * (b : ℚ) := hxD
          _ = (b : ℚ) * (D : ℚ) := mul_comm _ _
      exact_mod_cast hq_ineq
    obtain ⟨assign, hassign⟩ := fin_partition_exists cnt D hcnt_sum
    have hsig_ex : ∀ m : Menu, ∀ i : Fin k, ∃ s : Signing n t d, ∀ x ∈ m.1 i, pass scope s x = true :=
      fun m i => exists_signing_of_admissible scope (m.2 i).2
    let sig : Menu → Fin k → Signing n t d := fun m i => Classical.choose (hsig_ex m i)
    have hsig_ok : ∀ m i x, x ∈ m.1 i → pass scope (sig m i) x = true :=
      fun m i x hx => Classical.choose_spec (hsig_ex m i) x hx
    let N := q * D
    have hN_pos : 0 < N := Nat.mul_pos hq hD_pos
    let eN : Fin N ≃ Fin q × Fin D := finProdFinEquiv.symm
    let ask : Fin N → Fin k → List Bool → Signing n t d := fun seed j _ => sig (assign (eN seed).2) j
    let answer : Fin N → List Bool → Bool := fun seed h =>
      if h.any id then true else decide ((eN seed).1.val < a)
    refine ⟨N, hN_pos, ask, answer, fun A hAP => ?_⟩
    split_ifs with hAne
    · obtain ⟨x, hxA⟩ := hAne
      have hxP : x ∈ P := hAP hxA
      let runA : Fin N → Bool := fun seed =>
        answer seed ((List.finRange k).foldl (fun h j => h ++ [reply scope A (ask seed j h)]) [])
      have hcomp : ((Finset.univ : Finset (Fin N)).filter (fun seed => runA seed = true)).card +
          ((Finset.univ : Finset (Fin N)).filter (fun seed => runA seed = false)).card = N := by
        have := card_filter_add_not (Finset.univ : Finset (Fin N)) (fun seed => runA seed = true)
        simpa [Bool.not_eq_true] using this
      have hrej_sub : (Finset.univ.filter (fun seed : Fin N => runA seed = false)) ⊆
          Finset.univ.filter (fun seed : Fin N => a ≤ (eN seed).1.val ∧ ∀ i, x ∉ (assign (eN seed).2).1 i) := by
        intro seed hseed
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hseed ⊢
        dsimp [runA, answer] at hseed
        cases hany : ((List.finRange k).foldl (fun h j => h ++ [reply scope A (ask seed j h)]) []).any id
        · rw [hany] at hseed
          simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not, not_lt] at hseed
          refine ⟨hseed, fun i hi => ?_⟩
          have hstep := foldl_any_false_of_all_false (fun j h => reply scope A (ask seed j h)) hany i
          dsimp [ask] at hstep
          have hpass : pass scope (sig (assign (eN seed).2) i) x = true := hsig_ok _ i x hi
          have hrep : reply scope A (sig (assign (eN seed).2) i) = true :=
            (reply_eq_true_iff scope A _).mpr ⟨x, hxA, hpass⟩
          rw [hrep] at hstep; contradiction
        · rw [hany] at hseed; simp at hseed
      have hcard_prod :
          (Finset.univ.filter (fun seed : Fin N => a ≤ (eN seed).1.val ∧ ∀ i, x ∉ (assign (eN seed).2).1 i)).card =
          (Finset.univ.filter (fun r : Fin q => a ≤ r.val)).card *
          (Finset.univ.filter (fun u : Fin D => ∀ i, x ∉ (assign u).1 i)).card := by
        rw [← Finset.card_product]
        refine Finset.card_bij (fun seed _ => eN seed) ?_ ?_ ?_
        · intro seed hseed
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hseed ⊢
          exact hseed
        · intro s1 _ s2 _ h; exact eN.injective h
        · intro p hp
          refine ⟨eN.symm p, ?_, eN.apply_symm_apply p⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
          simpa using hp
      have hcard_r : (Finset.univ.filter (fun r : Fin q => a ≤ r.val)).card = q - a := by
        have hcomp_r := card_filter_add_not (Finset.univ : Finset (Fin q)) (fun r : Fin q => r.val < a)
        have hlt_card : (Finset.univ.filter (fun r : Fin q => r.val < a)).card = a := by
          calc (Finset.univ.filter (fun r : Fin q => r.val < a)).card
              = (Finset.univ : Finset (Fin a)).card := by
                refine Finset.card_bij (fun (r : Fin q) hr => (⟨r.val, (Finset.mem_filter.mp hr).2⟩ : Fin a)) ?_ ?_ ?_
                · intro _ _; exact Finset.mem_univ _
                · intro r1 _ r2 _ h; exact Fin.ext (congrArg (Fin.val : Fin a → ℕ) h)
                · intro y _
                  refine ⟨⟨y.val, lt_of_lt_of_le y.2 ha⟩, ?_, Fin.ext rfl⟩
                  simp [y.2]
            _ = a := by simp
        have hneg : (Finset.univ.filter (fun r : Fin q => ¬r.val < a)) =
            Finset.univ.filter (fun r : Fin q => a ≤ r.val) := by
          ext r; simp [not_lt]
        rw [hlt_card, hneg, Finset.card_univ, Fintype.card_fin] at hcomp_r
        omega
      have hcard_u : (Finset.univ.filter (fun u : Fin D => ∀ i, x ∉ (assign u).1 i)).card =
          ∑ m : Menu, if ∀ i, x ∉ m.1 i then cnt m else 0 := by
        have hfib : (Finset.univ.filter (fun u : Fin D => ∀ i, x ∉ (assign u).1 i)).card =
            ∑ m ∈ Finset.univ.filter (fun m : Menu => ∀ i, x ∉ m.1 i),
              (Finset.univ.filter (fun u : Fin D => assign u = m)).card := by
          rw [← Finset.card_biUnion]
          · congr 1
            ext u
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
            exact ⟨fun hu => ⟨assign u, hu, rfl⟩, fun ⟨m, hm, heq⟩ => heq ▸ hm⟩
          · intro m1 _ m2 _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro u hu1 hu2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
            exact hne (hu1.symm.trans hu2)
        rw [hfib, Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        split_ifs
        · exact hassign m
        · rfl
      have hrej_le : N - ((Finset.univ : Finset (Fin N)).filter (fun seed => runA seed = true)).card ≤
          (q - a) * (∑ m : Menu, if ∀ i, x ∉ m.1 i then cnt m else 0) := by
        have hsub_le := Finset.card_le_card hrej_sub
        rw [hcard_prod, hcard_r, hcard_u] at hsub_le
        omega
      have hcov_x := hcnt_cov ⟨x, hxP⟩
      calc q * (N - ((Finset.univ : Finset (Fin N)).filter (fun seed => runA seed = true)).card)
          ≤ q * ((q - a) * (∑ m : Menu, if ∀ i, x ∉ m.1 i then cnt m else 0)) :=
            Nat.mul_le_mul_left q hrej_le
        _ ≤ q * (b * D) := Nat.mul_le_mul_left q hcov_x
        _ = b * N := by dsimp [N]; ring
    · have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAne
      subst hAe
      have hpath : ∀ seed : Fin N,
          ((List.finRange k).foldl (fun h j => h ++ [reply scope ∅ (ask seed j h)]) []) =
          List.replicate k false := fun seed =>
        foldl_finRange_all_false _ (fun j => reply_empty scope _)
      have hyes_eq : ((Finset.univ : Finset (Fin N)).filter (fun seed =>
          answer seed ((List.finRange k).foldl (fun h j =>
            h ++ [reply scope ∅ (ask seed j h)]) ([] : List Bool)) = true)).card =
          a * D := by
        have hfilt : (Finset.univ.filter (fun seed : Fin N =>
            answer seed ((List.finRange k).foldl (fun h j =>
              h ++ [reply scope ∅ (ask seed j h)]) ([] : List Bool)) = true)) =
            Finset.univ.filter (fun seed : Fin N => (eN seed).1.val < a) := by
          ext seed
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpath, answer]
          have hany : (List.replicate k false).any id = false := by
            simp
          rw [hany]
          simp
        rw [hfilt]
        have hbij : (Finset.univ.filter (fun seed : Fin N => (eN seed).1.val < a)).card =
            (Finset.univ.filter (fun r : Fin q => r.val < a)).card * D := by
          have h1 : (Finset.univ.filter (fun r : Fin q => r.val < a)).card * D =
              ((Finset.univ.filter (fun r : Fin q => r.val < a)) ×ˢ (Finset.univ : Finset (Fin D))).card := by
            simp [Finset.card_product]
          rw [h1]
          refine Finset.card_bij (fun seed _ => eN seed) ?_ ?_ ?_
          · intro seed hseed
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true] at hseed ⊢
            exact hseed
          · intro s1 _ s2 _ h; exact eN.injective h
          · intro p hp
            refine ⟨eN.symm p, ?_, eN.apply_symm_apply p⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true] at hp ⊢
            simpa using hp
        rw [hbij]
        have hlt_card : (Finset.univ.filter (fun r : Fin q => r.val < a)).card = a := by
          calc (Finset.univ.filter (fun r : Fin q => r.val < a)).card
              = (Finset.univ : Finset (Fin a)).card := by
                refine Finset.card_bij (fun (r : Fin q) hr => (⟨r.val, (Finset.mem_filter.mp hr).2⟩ : Fin a)) ?_ ?_ ?_
                · intro _ _; exact Finset.mem_univ _
                · intro r1 _ r2 _ h; exact Fin.ext (congrArg (Fin.val : Fin a → ℕ) h)
                · intro y _
                  refine ⟨⟨y.val, lt_of_lt_of_le y.2 ha⟩, ?_, Fin.ext rfl⟩
                  simp [y.2]
            _ = a := by simp
        rw [hlt_card]
      rw [hyes_eq]
      dsimp [N]
      have : q * (a * D) = a * (q * D) := by ring
      exact le_of_eq this

end Protocol

end PEqualNP.Outside.L_lib_1178_aux

theorem PEqualNP.Outside.L_lib_1178 : (∀ (n t d : Nat) (scope : Fin t → Finset (Fin n)),
  let Word := Fin n → Fin (d + 2)
  let Signing := Fin t → Word
  let pass := fun (s : Signing) (x : Word) => (List.finRange t).all (fun j =>
    (scope j).toList.any (fun v => x v != s j v))
  let reply := fun (A : Finset Word) (s : Signing) => A.toList.any (pass s)
  let admissible := fun (X : Finset Word) => ∀ j : Fin t,
    ∃ z : Word, ∀ x ∈ X, ∃ v ∈ scope j, x v ≠ z v
  ∀ (P : Finset Word) (k a b q : Nat), 0 < q → a ≤ q → b ≤ q →
    ((∃ N : Nat, 0 < N ∧
      ∃ ask : Fin N → Fin k → List Bool → Signing, ∃ answer : Fin N → List Bool → Bool,
        ∀ A : Finset Word, A ⊆ P →
          let yes := ((Finset.univ : Finset (Fin N)).filter (fun seed =>
            answer seed ((List.finRange k).foldl (fun h j =>
              h ++ [reply A (ask seed j h)]) ([] : List Bool)))).card
          if A.Nonempty then q * (N - yes) ≤ b * N else q * yes ≤ a * N) ↔
    ∀ w : Word → Nat, ∃ X : Fin k → Finset Word,
      (∀ i, X i ⊆ P ∧ admissible (X i)) ∧
      (q - a) * ((P.filter (fun x => ∀ i, x ∉ X i)).sum w) ≤ b * (P.sum w))) :=
  fun _ _ _ scope P k a b q hq ha hb =>
    PEqualNP.Outside.L_lib_1178_aux.main_thm scope P k a b q hq ha hb
