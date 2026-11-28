import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1014_aux

def reg (N t : ℕ) (T : Fin N → Fin N → Bool) : Prop :=
  (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
  (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)

def value (N : ℕ) (B : Fin N → Fin N → ℝ) (T : Fin N → Fin N → Bool) : ℝ :=
  ∑ x : Fin N, ∑ y : Fin N, if T x y then B x y else 0

def flat (N t : ℕ) (B : Fin N → Fin N → ℝ) : Prop :=
  ∀ T U, reg N t T → reg N t U → value N B T = value N B U

def profile (N M : ℕ) (R S : Fin M → Finset (Fin N)) (x y : Fin N) : ℝ :=
  ∑ i : Fin M, if x ∈ R i ∧ y ∈ S i then (1 : ℝ) else 0

def dims (N r s M : ℕ) (R S : Fin M → Finset (Fin N)) : Prop :=
  ∀ i, (R i).card = r ∧ (S i).card = s

def possible (N t r s M : ℕ) : Prop :=
  ∃ R S, dims N r s M R S ∧ flat N t (profile N M R S)

lemma value_of_add {N t : ℕ} {B : Fin N → Fin N → ℝ} {a b : Fin N → ℝ}
    (hB : ∀ x y, B x y = a x + b y) {T : Fin N → Fin N → Bool} (hT : reg N t T) :
    value N B T = (∑ x : Fin N, (t : ℝ) * a x) + (∑ y : Fin N, (t : ℝ) * b y) := by
  unfold value
  have h1 : ∀ x y : Fin N,
      (if T x y then B x y else 0) =
      (if T x y then a x else 0) + (if T x y then b y else 0) := by
    intro x y
    rw [hB x y]
    split_ifs <;> ring
  simp_rw [h1, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, hT.1 x, nsmul_eq_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, hT.2 y, nsmul_eq_mul]

lemma flat_of_add {N t : ℕ} {B : Fin N → Fin N → ℝ}
    (h : ∃ a b : Fin N → ℝ, ∀ x y, B x y = a x + b y) : flat N t B := by
  rcases h with ⟨a, b, hB⟩
  intro T U hT hU
  rw [value_of_add hB hT, value_of_add hB hU]

lemma reg_comp_perm {N t : ℕ} {T : Fin N → Fin N → Bool}
    (hT : reg N t T) (p q : Equiv.Perm (Fin N)) :
    reg N t (fun x y => T (p.symm x) (q.symm y)) := by
  constructor
  · intro x
    have hcard :
        (Finset.univ.filter (fun y : Fin N => T (p.symm x) (q.symm y))).card =
        (Finset.univ.filter (fun y : Fin N => T (p.symm x) y)).card := by
      refine Finset.card_bij (fun y _ => q.symm y) ?_ ?_ ?_
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact hy
      · intro y₁ _ y₂ _ h
        exact q.symm.injective h
      · intro y hy
        refine ⟨q y, ?_, q.symm_apply_apply y⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        simpa using hy
    rw [hcard, hT.1 (p.symm x)]
  · intro y
    have hcard :
        (Finset.univ.filter (fun x : Fin N => T (p.symm x) (q.symm y))).card =
        (Finset.univ.filter (fun x : Fin N => T x (q.symm y))).card := by
      refine Finset.card_bij (fun x _ => p.symm x) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx
      · intro x₁ _ x₂ _ h
        exact p.symm.injective h
      · intro x hx
        refine ⟨p x, ?_, p.symm_apply_apply x⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        simpa using hx
    rw [hcard, hT.2 (q.symm y)]

lemma value_comp_perm {N : ℕ} (B : Fin N → Fin N → ℝ) (T : Fin N → Fin N → Bool)
    (p q : Equiv.Perm (Fin N)) :
    value N (fun x y => B (p x) (q y)) T =
    value N B (fun x y => T (p.symm x) (q.symm y)) := by
  unfold value
  refine (Equiv.sum_comp p.symm (fun x => ∑ y : Fin N, if T x y then B (p x) (q y) else 0)).symm.trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  refine (Equiv.sum_comp q.symm (fun y => if T (p.symm x) y then B (p (p.symm x)) (q y) else 0)).symm.trans ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  simp

lemma flat_comp_perm {N t : ℕ} {B : Fin N → Fin N → ℝ}
    (hB : flat N t B) (p q : Equiv.Perm (Fin N)) :
    flat N t (fun x y => B (p x) (q y)) := by
  intro T U hT hU
  rw [value_comp_perm, value_comp_perm]
  exact hB _ _ (reg_comp_perm hT p q) (reg_comp_perm hU p q)

lemma exists_perm_01 {N : ℕ} (hN : 2 ≤ N) {x₁ x₂ : Fin N} (hx : x₁ ≠ x₂) :
    ∃ p : Equiv.Perm (Fin N), p ⟨0, by omega⟩ = x₁ ∧ p ⟨1, by omega⟩ = x₂ := by
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  let p₁ : Equiv.Perm (Fin N) := Equiv.swap i0 x₁
  let z : Fin N := p₁ x₂
  have hz0 : z ≠ i0 := by
    intro h
    have h2 : x₂ = p₁ i0 := by
      calc
        x₂ = p₁ (p₁ x₂) := by simp [p₁]
        _ = p₁ i0 := congrArg p₁ h
    rw [Equiv.swap_apply_left] at h2
    exact hx h2.symm
  have hi01 : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval
  let p₂ : Equiv.Perm (Fin N) := Equiv.swap i1 z
  refine ⟨p₂.trans p₁, ?_, ?_⟩
  · change p₁ (p₂ i0) = x₁
    have hp2 : p₂ i0 = i0 := Equiv.swap_apply_of_ne_of_ne hi01 hz0.symm
    rw [hp2]
    exact Equiv.swap_apply_left i0 x₁
  · change p₁ (p₂ i1) = x₂
    rw [Equiv.swap_apply_left]
    simp [z, p₁]

lemma card_erase_insert_eq {α : Type*} [DecidableEq α] (s : Finset α) {a b : α}
    (ha : a ∈ s) (hb : b ∉ s) :
    (insert b (s.erase a)).card = s.card := by
  have hb' : b ∉ s.erase a := by
    intro h
    exact hb (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hb', Finset.card_erase_add_one ha]

lemma exists_canonical_T0 {N t : ℕ} (ht0 : 0 < t) (htN : t < N) :
    ∃ T₀ : Fin N → Fin N → Bool,
      reg N t T₀ ∧
      T₀ ⟨0, by omega⟩ ⟨0, by omega⟩ = true ∧
      T₀ ⟨1, by omega⟩ ⟨1, by omega⟩ = true ∧
      T₀ ⟨0, by omega⟩ ⟨1, by omega⟩ = false ∧
      T₀ ⟨1, by omega⟩ ⟨0, by omega⟩ = false := by
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval
  by_cases htop : t = N - 1
  · let π : Equiv.Perm (Fin N) := Equiv.swap i0 i1
    refine ⟨fun x y => decide (y ≠ π x), ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro x
        have heq : Finset.univ.filter (fun y : Fin N => decide (y ≠ π x) = true) =
            Finset.univ.erase (π x) := by
          ext y
          simp
        rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
        omega
      · intro y
        have heq : Finset.univ.filter (fun x : Fin N => decide (y ≠ π x) = true) =
            Finset.univ.erase (π.symm y) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
            Finset.mem_erase, and_true]
          constructor
          · intro h h2
            apply h
            rw [h2]
            simp
          · intro h h2
            apply h
            have h3 := congrArg π.symm h2
            simpa using h3.symm
        rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
        omega
    · simp [π, i0, i1, hi01]
    · simp [π, i0, i1, hi01.symm]
    · simp [π, i0, i1]
    · simp [π, i0, i1]
  · have ht2 : t ≤ N - 2 := by omega
    have hN3 : 3 ≤ N := by omega
    let diff : Fin N → Fin N → ℕ := fun x y => (y.val + N - x.val) % N
    let P : ℕ → Prop := fun k => k = 0 ∨ (2 ≤ k ∧ k ≤ t)
    have hPcard : (Finset.univ.filter (fun k : Fin N => P k.val)).card = t := by
      have hbij : (Finset.univ : Finset (Fin t)).card =
          (Finset.univ.filter (fun k : Fin N => P k.val)).card := by
        refine Finset.card_bij
          (fun j _ => if j.val = 0 then (⟨0, by omega⟩ : Fin N) else ⟨j.val + 1, by omega⟩)
          ?_ ?_ ?_
        · intro j _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]
          split_ifs with hj
          · left; rfl
          · right; dsimp only; omega
        · intro j₁ _ j₂ _ h
          split_ifs at h with h1 h2
          · exact Fin.ext (by omega)
          · have hv := congrArg Fin.val h
            dsimp only at hv
            omega
          · have hv := congrArg Fin.val h
            dsimp only at hv
            omega
          · have hv := congrArg Fin.val h
            dsimp only at hv
            exact Fin.ext (by omega)
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, P] at hk
          rcases hk with hk0 | ⟨hk2, hkt⟩
          · refine ⟨⟨0, ht0⟩, Finset.mem_univ _, ?_⟩
            apply Fin.ext
            simp [hk0]
          · refine ⟨⟨k.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
            apply Fin.ext
            have hne : k.val - 1 ≠ 0 := by omega
            simp [hne]
            omega
      rw [← hbij, Finset.card_fin]
    have hdiff_lt : ∀ x y : Fin N, diff x y < N := fun x y => Nat.mod_lt _ (by omega)
    have hdiff_row_inv : ∀ x k : Fin N, diff x ⟨(x.val + k.val) % N, Nat.mod_lt _ (by omega)⟩ = k.val := by
      intro x k
      simp only [diff]
      by_cases hxk : x.val + k.val < N
      · rw [Nat.mod_eq_of_lt hxk]
        have h1 : x.val + k.val + N - x.val = k.val + N := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
      · have hmod : (x.val + k.val) % N = x.val + k.val - N := by
          have h1 : x.val + k.val = (x.val + k.val - N) + N := by omega
          conv_lhs => rw [h1]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        have h1 : x.val + k.val - N + N - x.val = k.val := by omega
        rw [h1, Nat.mod_eq_of_lt k.isLt]
    have hdiff_row_inj : ∀ x y₁ y₂ : Fin N, diff x y₁ = diff x y₂ → y₁ = y₂ := by
      intro x y₁ y₂ h
      have hform : ∀ y : Fin N, (x.val + diff x y) % N = y.val := by
        intro y
        simp only [diff]
        by_cases hxy : x.val ≤ y.val
        · have h1 : y.val + N - x.val = (y.val - x.val) + N := by omega
          have hm : (y.val - x.val) % N = y.val - x.val := Nat.mod_eq_of_lt (by omega)
          rw [h1, Nat.add_mod_right, hm]
          have h2 : x.val + (y.val - x.val) = y.val := by omega
          rw [h2, Nat.mod_eq_of_lt y.isLt]
        · have hm : (y.val + N - x.val) % N = y.val + N - x.val := Nat.mod_eq_of_lt (by omega)
          rw [hm]
          have h2 : x.val + (y.val + N - x.val) = y.val + N := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]
      apply Fin.ext
      rw [← hform y₁, ← hform y₂, h]
    have hdiff_col_inv : ∀ y k : Fin N, diff ⟨(y.val + N - k.val) % N, Nat.mod_lt _ (by omega)⟩ y = k.val := by
      intro y k
      simp only [diff]
      by_cases hky : k.val ≤ y.val
      · have h1 : y.val + N - k.val = (y.val - k.val) + N := by omega
        have hm : (y.val - k.val) % N = y.val - k.val := Nat.mod_eq_of_lt (by omega)
        rw [h1, Nat.add_mod_right, hm]
        have h2 : y.val + N - (y.val - k.val) = k.val + N := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
      · have hm : (y.val + N - k.val) % N = y.val + N - k.val := Nat.mod_eq_of_lt (by omega)
        rw [hm]
        have h2 : y.val + N - (y.val + N - k.val) = k.val := by omega
        rw [h2, Nat.mod_eq_of_lt k.isLt]
    have hdiff_col_inj : ∀ y x₁ x₂ : Fin N, diff x₁ y = diff x₂ y → x₁ = x₂ := by
      intro y x₁ x₂ h
      have hform : ∀ x : Fin N, (y.val + N - diff x y) % N = x.val := by
        intro x
        simp only [diff]
        by_cases hxy : x.val ≤ y.val
        · have h1 : y.val + N - x.val = (y.val - x.val) + N := by omega
          have hm : (y.val - x.val) % N = y.val - x.val := Nat.mod_eq_of_lt (by omega)
          rw [h1, Nat.add_mod_right, hm]
          have h2 : y.val + N - (y.val - x.val) = x.val + N := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
        · have hm : (y.val + N - x.val) % N = y.val + N - x.val := Nat.mod_eq_of_lt (by omega)
          rw [hm]
          have h2 : y.val + N - (y.val + N - x.val) = x.val := by omega
          rw [h2, Nat.mod_eq_of_lt x.isLt]
      apply Fin.ext
      rw [← hform x₁, ← hform x₂, h]
    refine ⟨fun x y => decide (P (diff x y)), ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro x
        have hcard :
            (Finset.univ.filter (fun y : Fin N => decide (P (diff x y)) = true)).card =
            (Finset.univ.filter (fun k : Fin N => P k.val)).card := by
          refine Finset.card_bij (fun y _ => ⟨diff x y, hdiff_lt x y⟩) ?_ ?_ ?_
          · intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hy ⊢
            exact hy
          · intro y₁ _ y₂ _ h
            exact hdiff_row_inj x y₁ y₂ (congrArg Fin.val h)
          · intro k hk
            refine ⟨⟨(x.val + k.val) % N, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hk ⊢
              rw [hdiff_row_inv x k]
              exact hk
            · exact Fin.ext (hdiff_row_inv x k)
        rw [hcard, hPcard]
      · intro y
        have hcard :
            (Finset.univ.filter (fun x : Fin N => decide (P (diff x y)) = true)).card =
            (Finset.univ.filter (fun k : Fin N => P k.val)).card := by
          refine Finset.card_bij (fun x _ => ⟨diff x y, hdiff_lt x y⟩) ?_ ?_ ?_
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hx ⊢
            exact hx
          · intro x₁ _ x₂ _ h
            exact hdiff_col_inj y x₁ x₂ (congrArg Fin.val h)
          · intro k hk
            refine ⟨⟨(y.val + N - k.val) % N, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hk ⊢
              rw [hdiff_col_inv y k]
              exact hk
            · exact Fin.ext (hdiff_col_inv y k)
        rw [hcard, hPcard]
    · simp only [decide_eq_true_eq, P, diff]
      left
      simp
    · simp only [decide_eq_true_eq, P, diff]
      left
      have h1 : 1 + N - 1 = N := by omega
      rw [h1, Nat.mod_self]
    · simp only [decide_eq_false_iff_not, P, diff]
      have h1 : (1 + N - 0) % N = 1 := by
        have h2 : 1 + N - 0 = 1 + N := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1]
      omega
    · simp only [decide_eq_false_iff_not, P, diff]
      have h1 : (0 + N - 1) % N = N - 1 := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      rw [h1]
      omega

lemma canonical_square_eq {N t : ℕ} (ht0 : 0 < t) (htN : t < N)
    {B : Fin N → Fin N → ℝ} (hflat : flat N t B) :
    B ⟨0, by omega⟩ ⟨0, by omega⟩ + B ⟨1, by omega⟩ ⟨1, by omega⟩ =
    B ⟨0, by omega⟩ ⟨1, by omega⟩ + B ⟨1, by omega⟩ ⟨0, by omega⟩ := by
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval
  rcases exists_canonical_T0 ht0 htN with ⟨T₀, hT₀, h00, h11, h01, h10⟩
  change T₀ i0 i0 = true at h00
  change T₀ i1 i1 = true at h11
  change T₀ i0 i1 = false at h01
  change T₀ i1 i0 = false at h10
  let U₀ : Fin N → Fin N → Bool := fun x y =>
    if x = i0 ∧ y = i0 then false
    else if x = i1 ∧ y = i1 then false
    else if x = i0 ∧ y = i1 then true
    else if x = i1 ∧ y = i0 then true
    else T₀ x y
  have hU₀ : reg N t U₀ := by
    constructor
    · intro x
      by_cases hx0 : x = i0
      · subst hx0
        have heq : Finset.univ.filter (fun y : Fin N => U₀ i0 y = true) =
            insert i1 ((Finset.univ.filter (fun y : Fin N => T₀ i0 y = true)).erase i0) := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_erase, U₀]
          by_cases hy0 : y = i0
          · subst hy0
            simp [hi01]
          · by_cases hy1 : y = i1
            · subst hy1
              simp [hi01, hi01.symm]
            · simp [hy0, hy1, hi01]
        rw [heq, card_erase_insert_eq _ (by simp [h00]) (by simp [h01]), hT₀.1 i0]
      · by_cases hx1 : x = i1
        · subst hx1
          have heq : Finset.univ.filter (fun y : Fin N => U₀ i1 y = true) =
              insert i0 ((Finset.univ.filter (fun y : Fin N => T₀ i1 y = true)).erase i1) := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_erase, U₀]
            by_cases hy0 : y = i0
            · subst hy0
              simp [hi01, hi01.symm]
            · by_cases hy1 : y = i1
              · subst hy1
                simp [hi01.symm]
              · simp [hy0, hy1, hi01.symm]
          rw [heq, card_erase_insert_eq _ (by simp [h11]) (by simp [h10]), hT₀.1 i1]
        · have heq : Finset.univ.filter (fun y : Fin N => U₀ x y = true) =
              Finset.univ.filter (fun y : Fin N => T₀ x y = true) := by
            ext y
            simp [U₀, hx0, hx1]
          rw [heq, hT₀.1 x]
    · intro y
      by_cases hy0 : y = i0
      · subst hy0
        have heq : Finset.univ.filter (fun x : Fin N => U₀ x i0 = true) =
            insert i1 ((Finset.univ.filter (fun x : Fin N => T₀ x i0 = true)).erase i0) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_erase, U₀]
          by_cases hx0 : x = i0
          · subst hx0
            simp [hi01]
          · by_cases hx1 : x = i1
            · subst hx1
              simp [hi01, hi01.symm]
            · simp [hx0, hx1, hi01]
        rw [heq, card_erase_insert_eq _ (by simp [h00]) (by simp [h10]), hT₀.2 i0]
      · by_cases hy1 : y = i1
        · subst hy1
          have heq : Finset.univ.filter (fun x : Fin N => U₀ x i1 = true) =
              insert i0 ((Finset.univ.filter (fun x : Fin N => T₀ x i1 = true)).erase i1) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_erase, U₀]
            by_cases hx0 : x = i0
            · subst hx0
              simp [hi01, hi01.symm]
            · by_cases hx1 : x = i1
              · subst hx1
                simp [hi01.symm]
              · simp [hx0, hx1, hi01.symm]
          rw [heq, card_erase_insert_eq _ (by simp [h11]) (by simp [h01]), hT₀.2 i1]
        · have heq : Finset.univ.filter (fun x : Fin N => U₀ x y = true) =
              Finset.univ.filter (fun x : Fin N => T₀ x y = true) := by
            ext x
            simp [U₀, hy0, hy1]
          rw [heq, hT₀.2 y]
  have hval : value N B T₀ - value N B U₀ = 0 := sub_eq_zero.mpr (hflat T₀ U₀ hT₀ hU₀)
  let D : Fin N → Fin N → ℝ := fun x y =>
    (if T₀ x y then B x y else 0) - (if U₀ x y then B x y else 0)
  have hsum : value N B T₀ - value N B U₀ = ∑ x : Fin N, ∑ y : Fin N, D x y := by
    unfold value
    simp_rw [← Finset.sum_sub_distrib, D]
  have hD_other_x : ∀ x : Fin N, x ≠ i0 → x ≠ i1 → ∑ y : Fin N, D x y = 0 := by
    intro x hx0 hx1
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [D, U₀, hx0, hx1]
  have hD_i0 : ∑ y : Fin N, D i0 y = B i0 i0 - B i0 i1 := by
    have hsub : ∑ y : Fin N, D i0 y = ∑ y ∈ ({i0, i1} : Finset (Fin N)), D i0 y := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      simp [D, U₀, hy.1, hy.2]
    rw [hsub, Finset.sum_pair hi01]
    simp [D, U₀, h00, h01, hi01, hi01.symm]
    ring
  have hD_i1 : ∑ y : Fin N, D i1 y = B i1 i1 - B i1 i0 := by
    have hsub : ∑ y : Fin N, D i1 y = ∑ y ∈ ({i0, i1} : Finset (Fin N)), D i1 y := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      simp [D, U₀, hy.1, hy.2]
    rw [hsub, Finset.sum_pair hi01]
    simp [D, U₀, h11, h10, hi01, hi01.symm]
    ring
  have htot : ∑ x : Fin N, ∑ y : Fin N, D x y = (B i0 i0 - B i0 i1) + (B i1 i1 - B i1 i0) := by
    have hsub : ∑ x : Fin N, ∑ y : Fin N, D x y =
        ∑ x ∈ ({i0, i1} : Finset (Fin N)), ∑ y : Fin N, D x y := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact hD_other_x x hx.1 hx.2
    rw [hsub, Finset.sum_pair hi01, hD_i0, hD_i1]
  linarith

lemma add_of_flat {N t : ℕ} (ht0 : 0 < t) (htN : t < N)
    {B : Fin N → Fin N → ℝ} (hflat : flat N t B) :
    ∃ a b : Fin N → ℝ, ∀ x y, B x y = a x + b y := by
  let i0 : Fin N := ⟨0, by omega⟩
  refine ⟨fun x => B x i0, fun y => B i0 y - B i0 i0, fun x y => ?_⟩
  by_cases hx : x = i0
  · subst hx
    ring
  · by_cases hy : y = i0
    · subst hy
      ring
    · rcases exists_perm_01 (by omega : 2 ≤ N) (Ne.symm hx) with ⟨p, hp0, hp1⟩
      rcases exists_perm_01 (by omega : 2 ≤ N) (Ne.symm hy) with ⟨q, hq0, hq1⟩
      have hsq := canonical_square_eq ht0 htN (flat_comp_perm hflat p q)
      simp only [hp0, hp1, hq0, hq1] at hsq
      linarith

lemma flat_iff {N t : ℕ} (ht0 : 0 < t) (htN : t < N) (B : Fin N → Fin N → ℝ) :
    flat N t B ↔ ∃ a b : Fin N → ℝ, ∀ x y, B x y = a x + b y :=
  ⟨add_of_flat ht0 htN, flat_of_add⟩

lemma flat_transpose {N t : ℕ} (ht0 : 0 < t) (htN : t < N)
    {B : Fin N → Fin N → ℝ} (hflat : flat N t B) :
    flat N t (fun y x => B x y) := by
  rcases (flat_iff ht0 htN B).mp hflat with ⟨a, b, hB⟩
  refine (flat_iff ht0 htN _).mpr ⟨b, a, fun y x => ?_⟩
  rw [hB x y, add_comm]

lemma profile_transpose (N M : ℕ) (R S : Fin M → Finset (Fin N)) (y x : Fin N) :
    profile N M S R y x = profile N M R S x y := by
  unfold profile
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : x ∈ R i <;> by_cases h2 : y ∈ S i <;> simp [h1, h2]

lemma dims_transpose {N r s M : ℕ} {R S : Fin M → Finset (Fin N)}
    (h : dims N r s M R S) : dims N s r M S R :=
  fun i => ⟨(h i).2, (h i).1⟩

lemma flat_profile_lt_ds {N t r s M : ℕ}
    (ht0 : 0 < t) (htN : t < N)
    {R S : Fin M → Finset (Fin N)}
    (hdims : dims N r s M R S) (hflat : flat N t (profile N M R S))
    (hM : M < N / Nat.gcd N s) :
    (∀ x z y, profile N M R S x y = profile N M R S z y) ∧ (N / Nat.gcd N r) ∣ M := by
  have hN0 : 0 < N := by omega
  let P : Fin N → Fin N → ℕ := fun x y =>
    (Finset.univ.filter (fun i : Fin M => x ∈ R i ∧ y ∈ S i)).card
  let cR : Fin N → ℕ := fun x =>
    (Finset.univ.filter (fun i : Fin M => x ∈ R i)).card
  have hprof_eq : ∀ x y, profile N M R S x y = (P x y : ℝ) := by
    intro x y
    unfold profile
    simp only [P]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hrow_sum : ∀ x, ∑ y : Fin N, P x y = s * cR x := by
    intro x
    have h1 : ∀ y : Fin N, P x y = ∑ i : Fin M, if x ∈ R i ∧ y ∈ S i then 1 else 0 := by
      intro y
      simp only [P]
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ i : Fin M,
        (∑ y : Fin N, if x ∈ R i ∧ y ∈ S i then 1 else 0) = if x ∈ R i then s else 0 := by
      intro i
      by_cases hx : x ∈ R i
      · simp only [hx, true_and, ite_true]
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        have hfilt : Finset.univ.filter (fun y : Fin N => y ∈ S i) = S i := by
          ext y
          simp
        rw [hfilt, (hdims i).2]
      · simp [hx]
    simp_rw [h2]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcR_sum : ∑ x : Fin N, cR x = M * r := by
    have h1 : ∀ x : Fin N, cR x = ∑ i : Fin M, if x ∈ R i then 1 else 0 := by
      intro x
      simp only [cR]
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ i : Fin M, (∑ x : Fin N, if x ∈ R i then 1 else 0) = r := by
      intro i
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      have hfilt : Finset.univ.filter (fun x : Fin N => x ∈ R i) = R i := by
        ext x
        simp
      rw [hfilt, (hdims i).1]
    simp_rw [h2]
    rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]
  rcases (flat_iff ht0 htN _).mp hflat with ⟨a, b, hab⟩
  have hP_diff_const : ∀ x z y₀ y : Fin N,
      (P x y : ℤ) - (P z y : ℤ) = (P x y₀ : ℤ) - (P z y₀ : ℤ) := by
    intro x z y₀ y
    have hreal : ((P x y : ℤ) - (P z y : ℤ) : ℝ) = ((P x y₀ : ℤ) - (P z y₀ : ℤ) : ℝ) := by
      push_cast
      rw [← hprof_eq, ← hprof_eq, ← hprof_eq, ← hprof_eq, hab, hab, hab, hab]
      ring
    exact_mod_cast hreal
  have hmul_eq : ∀ x z y₀ : Fin N,
      (N : ℤ) * ((P x y₀ : ℤ) - (P z y₀ : ℤ)) = (s : ℤ) * ((cR x : ℤ) - (cR z : ℤ)) := by
    intro x z y₀
    have hL : ∑ y : Fin N, ((P x y : ℤ) - (P z y : ℤ)) =
        (N : ℤ) * ((P x y₀ : ℤ) - (P z y₀ : ℤ)) := by
      simp_rw [hP_diff_const x z y₀]
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hR : ∑ y : Fin N, ((P x y : ℤ) - (P z y : ℤ)) =
        (s : ℤ) * ((cR x : ℤ) - (cR z : ℤ)) := by
      rw [Finset.sum_sub_distrib]
      have hx : ∑ y : Fin N, (P x y : ℤ) = (s : ℤ) * (cR x : ℤ) := by
        exact_mod_cast hrow_sum x
      have hz : ∑ y : Fin N, (P z y : ℤ) = (s : ℤ) * (cR z : ℤ) := by
        exact_mod_cast hrow_sum z
      rw [hx, hz]
      ring
    linarith
  have hcR_const : ∀ x z : Fin N, cR x = cR z := by
    intro x z
    let gs := Nat.gcd N s
    let ds := N / gs
    let s' := s / gs
    have hgs0 : 0 < gs := Nat.gcd_pos_of_pos_left s hN0
    have hN_eq : gs * ds = N := Nat.mul_div_cancel' (Nat.gcd_dvd_left N s)
    have hs_eq : gs * s' = s := Nat.mul_div_cancel' (Nat.gcd_dvd_right N s)
    have hcop : Nat.Coprime ds s' := Nat.coprime_div_gcd_div_gcd hgs0
    let y₀ : Fin N := ⟨0, hN0⟩
    have h1 := hmul_eq x z y₀
    have h2 : (gs : ℤ) * ((ds : ℤ) * ((P x y₀ : ℤ) - (P z y₀ : ℤ))) =
        (gs : ℤ) * ((s' : ℤ) * ((cR x : ℤ) - (cR z : ℤ))) := by
      have hN' : (N : ℤ) = (gs : ℤ) * (ds : ℤ) := by exact_mod_cast hN_eq.symm
      have hs' : (s : ℤ) = (gs : ℤ) * (s' : ℤ) := by exact_mod_cast hs_eq.symm
      rw [hN', hs'] at h1
      linarith
    have hgs_ne : (gs : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgs0)
    have h3 : (ds : ℤ) * ((P x y₀ : ℤ) - (P z y₀ : ℤ)) =
        (s' : ℤ) * ((cR x : ℤ) - (cR z : ℤ)) := mul_left_cancel₀ hgs_ne h2
    have hdvd_mul : (ds : ℤ) ∣ (s' : ℤ) * ((cR x : ℤ) - (cR z : ℤ)) :=
      ⟨(P x y₀ : ℤ) - (P z y₀ : ℤ), h3.symm⟩
    have hiscop : IsCoprime (ds : ℤ) (s' : ℤ) := (Nat.isCoprime_iff_coprime).mpr hcop
    have hdvd : (ds : ℤ) ∣ (cR x : ℤ) - (cR z : ℤ) := hiscop.dvd_of_dvd_mul_left hdvd_mul
    rcases hdvd with ⟨k, hk⟩
    have hxle : cR x ≤ M := by
      simpa [cR] using Finset.card_filter_le (Finset.univ : Finset (Fin M)) (fun i => x ∈ R i)
    have hzle : cR z ≤ M := by
      simpa [cR] using Finset.card_filter_le (Finset.univ : Finset (Fin M)) (fun i => z ∈ R i)
    have hds_gt : (M : ℤ) < (ds : ℤ) := by exact_mod_cast hM
    have hxle' : (cR x : ℤ) ≤ (M : ℤ) := by exact_mod_cast hxle
    have hzle' : (cR z : ℤ) ≤ (M : ℤ) := by exact_mod_cast hzle
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with hklt | hkzero | hkgt
      · have : (ds : ℤ) * k ≤ -(ds : ℤ) := by nlinarith
        omega
      · exact hkzero
      · have : (ds : ℤ) ≤ (ds : ℤ) * k := by nlinarith
        omega
    rw [hk0, mul_zero] at hk
    omega
  constructor
  · intro x z y
    rw [hprof_eq, hprof_eq]
    have h1 := hmul_eq x z y
    rw [hcR_const x z, sub_self, mul_zero] at h1
    have hN_ne : (N : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN0)
    have h2 : (P x y : ℤ) - (P z y : ℤ) = 0 := (mul_eq_zero.mp h1).resolve_left hN_ne
    have h3 : P x y = P z y := by omega
    rw [h3]
  · let x₀ : Fin N := ⟨0, hN0⟩
    have hsum_const : ∑ x : Fin N, cR x = N * cR x₀ := by
      simp_rw [hcR_const _ x₀]
      rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]
    have hMr : N * cR x₀ = M * r := by
      rw [← hsum_const, hcR_sum]
    let gr := Nat.gcd N r
    let dr := N / gr
    let r' := r / gr
    have hgr0 : 0 < gr := Nat.gcd_pos_of_pos_left r hN0
    have hN_eq : gr * dr = N := Nat.mul_div_cancel' (Nat.gcd_dvd_left N r)
    have hr_eq : gr * r' = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right N r)
    have hcop : Nat.Coprime dr r' := Nat.coprime_div_gcd_div_gcd hgr0
    have h1 : gr * (dr * cR x₀) = gr * (M * r') := by
      calc
        gr * (dr * cR x₀) = (gr * dr) * cR x₀ := by ring
        _ = N * cR x₀ := by rw [hN_eq]
        _ = M * r := hMr
        _ = M * (gr * r') := by rw [hr_eq]
        _ = gr * (M * r') := by ring
    have h2 : dr * cR x₀ = M * r' := Nat.eq_of_mul_eq_mul_left hgr0 h1
    have hdvd_mul : dr ∣ M * r' := ⟨cR x₀, h2.symm⟩
    exact hcop.dvd_of_dvd_mul_right hdvd_mul

lemma possible_of_dvd_dr {N t r s M : ℕ}
    (hr0 : 0 < r) (hrN : r ≤ N) (hsN : s ≤ N)
    (hdr : (N / Nat.gcd N r) ∣ M) :
    possible N t r s M := by
  have hN0 : 0 < N := by omega
  let gr := Nat.gcd N r
  let dr := N / gr
  let r' := r / gr
  have hN_eq : gr * dr = N := Nat.mul_div_cancel' (Nat.gcd_dvd_left N r)
  have hr_eq : gr * r' = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right N r)
  rcases hdr with ⟨k, hk⟩
  let q := k * r'
  have hMr_eq : M * r = q * N := by
    calc
      M * r = (dr * k) * (gr * r') := by rw [hk, hr_eq]
      _ = (k * r') * (gr * dr) := by ring
      _ = q * N := by rw [hN_eq]
  let S₀ : Finset (Fin N) := Finset.univ.filter (fun y : Fin N => y.val < s)
  have hS₀_card : S₀.card = s := by
    have hbij : (Finset.univ : Finset (Fin s)).card = S₀.card := by
      refine Finset.card_bij (fun j _ => (⟨j.val, by omega⟩ : Fin N)) ?_ ?_ ?_
      · intro j _
        simp [S₀, j.isLt]
      · intro j₁ _ j₂ _ h
        have hv := congrArg Fin.val h
        exact Fin.ext hv
      · intro y hy
        simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨⟨y.val, hy⟩, Finset.mem_univ _, Fin.ext rfl⟩
    rw [← hbij, Finset.card_fin]
  let R : Fin M → Finset (Fin N) := fun i =>
    Finset.univ.image (fun j : Fin r => (⟨(i.val * r + j.val) % N, Nat.mod_lt _ hN0⟩ : Fin N))
  let S : Fin M → Finset (Fin N) := fun _ => S₀
  have hR_card : ∀ i : Fin M, (R i).card = r := by
    intro i
    have hinj : Function.Injective
        (fun j : Fin r => (⟨(i.val * r + j.val) % N, Nat.mod_lt _ hN0⟩ : Fin N)) := by
      intro j₁ j₂ h
      have hmod : (i.val * r + j₁.val) % N = (i.val * r + j₂.val) % N := congrArg Fin.val h
      have h1 := Nat.div_add_mod (i.val * r + j₁.val) N
      have h2 := Nat.div_add_mod (i.val * r + j₂.val) N
      have hj1 : j₁.val < N := lt_of_lt_of_le j₁.isLt hrN
      have hj2 : j₂.val < N := lt_of_lt_of_le j₂.isLt hrN
      have hq : (i.val * r + j₁.val) / N = (i.val * r + j₂.val) / N := by
        rcases lt_trichotomy ((i.val * r + j₁.val) / N) ((i.val * r + j₂.val) / N) with hlt | heq | hgt
        · have hle : N * ((i.val * r + j₁.val) / N + 1) ≤ N * ((i.val * r + j₂.val) / N) :=
            Nat.mul_le_mul_left N hlt
          have hstep : N * ((i.val * r + j₁.val) / N + 1) = N * ((i.val * r + j₁.val) / N) + N := by ring
          omega
        · exact heq
        · have hle : N * ((i.val * r + j₂.val) / N + 1) ≤ N * ((i.val * r + j₁.val) / N) :=
            Nat.mul_le_mul_left N hgt
          have hstep : N * ((i.val * r + j₂.val) / N + 1) = N * ((i.val * r + j₂.val) / N) + N := by ring
          omega
      rw [hq] at h1
      exact Fin.ext (by omega)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have hcR_eq : ∀ x : Fin N, (Finset.univ.filter (fun i : Fin M => x ∈ R i)).card = q := by
    intro x
    have hbij : (Finset.univ : Finset (Fin q)).card =
        (Finset.univ.filter (fun i : Fin M => x ∈ R i)).card := by
      have hu_lt : ∀ m : Fin q, (m.val * N + x.val) / r < M := by
        intro m
        refine (Nat.div_lt_iff_lt_mul hr0).mpr ?_
        have h1 : (m.val + 1) * N ≤ q * N := Nat.mul_le_mul_right N m.isLt
        have h2 : m.val * N + x.val < (m.val + 1) * N := by
          have : (m.val + 1) * N = m.val * N + N := by ring
          omega
        omega
      refine Finset.card_bij (fun m _ => (⟨(m.val * N + x.val) / r, hu_lt m⟩ : Fin M)) ?_ ?_ ?_
      · intro m _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, R, Finset.mem_image]
        refine ⟨⟨(m.val * N + x.val) % r, Nat.mod_lt _ hr0⟩, ?_⟩
        apply Fin.ext
        simp only
        have hdm : (m.val * N + x.val) / r * r + (m.val * N + x.val) % r = m.val * N + x.val := by
          rw [mul_comm]
          exact Nat.div_add_mod (m.val * N + x.val) r
        rw [hdm, mul_comm m.val N, Nat.mul_add_mod, Nat.mod_eq_of_lt x.isLt]
      · intro m₁ _ m₂ _ h
        have hdiv : (m₁.val * N + x.val) / r = (m₂.val * N + x.val) / r := congrArg Fin.val h
        have h1 := Nat.div_add_mod (m₁.val * N + x.val) r
        have h2 := Nat.div_add_mod (m₂.val * N + x.val) r
        rw [hdiv] at h1
        have hm1 : (m₁.val * N + x.val) % r < r := Nat.mod_lt _ hr0
        have hm2 : (m₂.val * N + x.val) % r < r := Nat.mod_lt _ hr0
        apply Fin.ext
        rcases lt_trichotomy m₁.val m₂.val with hlt | heq | hgt
        · have hle : (m₁.val + 1) * N ≤ m₂.val * N := Nat.mul_le_mul_right N hlt
          have hstep : (m₁.val + 1) * N = m₁.val * N + N := by ring
          omega
        · exact heq
        · have hle : (m₂.val + 1) * N ≤ m₁.val * N := Nat.mul_le_mul_right N hgt
          have hstep : (m₂.val + 1) * N = m₂.val * N + N := by ring
          omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, R, Finset.mem_image] at hi
        rcases hi with ⟨j, hj⟩
        have hmod : (i.val * r + j.val) % N = x.val := congrArg Fin.val hj
        let u := i.val * r + j.val
        have hu : u < q * N := by
          have h1 : (i.val + 1) * r ≤ M * r := Nat.mul_le_mul_right r i.isLt
          have h2 : (i.val + 1) * r = i.val * r + r := by ring
          have h3 : j.val < r := j.isLt
          omega
        have hm_lt : u / N < q := (Nat.div_lt_iff_lt_mul hN0).mpr hu
        refine ⟨⟨u / N, hm_lt⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        simp only
        have hu_eq : (u / N) * N + x.val = u := by
          rw [← hmod, mul_comm]
          exact Nat.div_add_mod u N
        rw [hu_eq]
        have hdiv_r : (j.val + r * i.val) / r = j.val / r + i.val :=
          Nat.add_mul_div_left j.val i.val hr0
        have hcomm : u = j.val + r * i.val := by
          dsimp [u]
          ring
        rw [hcomm, hdiv_r, Nat.div_eq_of_lt j.isLt, zero_add]
    rw [← hbij, Finset.card_fin]
  refine ⟨R, S, fun i => ⟨hR_card i, hS₀_card⟩, ?_⟩
  refine flat_of_add ⟨fun _ => 0, fun y => if y ∈ S₀ then (q : ℝ) else 0, fun x y => ?_⟩
  unfold profile
  simp only [S, zero_add]
  by_cases hy : y ∈ S₀
  · simp only [hy, and_true, ite_true]
    rw [← Finset.sum_filter, Finset.sum_const, hcR_eq x, nsmul_eq_mul, mul_one]
  · simp [hy]

lemma possible_of_dvd_ds {N t r s M : ℕ}
    (ht0 : 0 < t) (htN : t < N) (hrN : r ≤ N) (hs0 : 0 < s) (hsN : s ≤ N)
    (hds : (N / Nat.gcd N s) ∣ M) :
    possible N t r s M := by
  rcases possible_of_dvd_dr hs0 hsN hrN hds with ⟨S, R, hdims, hflat⟩
  refine ⟨R, S, dims_transpose hdims, ?_⟩
  have htr := flat_transpose ht0 htN hflat
  have heq : (fun y x => profile N M S R x y) = profile N M R S := by
    funext x y
    exact profile_transpose N M R S y x
  rwa [heq] at htr

theorem main : ∀ (N t r s : ℕ), 0 < t → t < N → 0 < r → r ≤ N → 0 < s → s ≤ N →
    let X := Fin N
    let reg := fun (T : X → X → Bool) =>
      (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
      (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
    let value := fun (B : X → X → ℝ) (T : X → X → Bool) =>
      ∑ x, ∑ y, if T x y then B x y else 0
    let flat := fun (B : X → X → ℝ) =>
      ∀ T U, reg T → reg U → value B T = value B U
    let profile := fun (M : ℕ) (R S : Fin M → Finset X) (x y : X) =>
      (∑ i : Fin M, if x ∈ R i ∧ y ∈ S i then (1 : ℝ) else 0)
    let dims := fun (M : ℕ) (R S : Fin M → Finset X) =>
      ∀ i, (R i).card = r ∧ (S i).card = s
    let possible := fun (M : ℕ) => ∃ R S, dims M R S ∧ flat (profile M R S)
    let dr := N / Nat.gcd N r
    let ds := N / Nat.gcd N s
    (∀ B, flat B ↔ ∃ a b : X → ℝ, ∀ x y, B x y = a x + b y) ∧
    possible (min dr ds) ∧
    (∀ M : ℕ, 0 < M → possible M → min dr ds ≤ M) ∧
    (∀ M : ℕ, M < max dr ds → (possible M ↔ dr ∣ M ∨ ds ∣ M)) ∧
    ∀ (M : ℕ) (R S : Fin M → Finset X), dims M R S → flat (profile M R S) →
      (M < ds → ∀ x z y, profile M R S x y = profile M R S z y) ∧
      (M < dr → ∀ x y z, profile M R S x y = profile M R S x z) := by
  intro N t r s ht0 htN hr0 hrN hs0 hsN
  dsimp only
  let dr := N / Nat.gcd N r
  let ds := N / Nat.gcd N s
  have h1 : ∀ B, flat N t B ↔ ∃ a b : Fin N → ℝ, ∀ x y, B x y = a x + b y :=
    flat_iff ht0 htN
  have h2 : possible N t r s (min dr ds) := by
    rcases min_cases dr ds with ⟨hmin, _⟩ | ⟨hmin, _⟩
    · rw [hmin]
      exact possible_of_dvd_dr hr0 hrN hsN (dvd_refl dr)
    · rw [hmin]
      exact possible_of_dvd_ds ht0 htN hrN hs0 hsN (dvd_refl ds)
  have h5_row : ∀ (M : ℕ) (R S : Fin M → Finset (Fin N)),
      dims N r s M R S → flat N t (profile N M R S) → M < ds →
      (∀ x z y, profile N M R S x y = profile N M R S z y) ∧ dr ∣ M :=
    fun M R S hdims hflat hM => flat_profile_lt_ds ht0 htN hdims hflat hM
  have h5_col : ∀ (M : ℕ) (R S : Fin M → Finset (Fin N)),
      dims N r s M R S → flat N t (profile N M R S) → M < dr →
      (∀ x y z, profile N M R S x y = profile N M R S x z) ∧ ds ∣ M := by
    intro M R S hdims hflat hM
    have htr : flat N t (profile N M S R) := by
      have h := flat_transpose ht0 htN hflat
      have heq : (fun y x => profile N M R S x y) = profile N M S R := by
        funext y x
        exact (profile_transpose N M R S y x).symm
      rwa [heq] at h
    rcases flat_profile_lt_ds ht0 htN (dims_transpose hdims) htr hM with
      ⟨hconst, hdvd⟩
    refine ⟨fun x y z => ?_, hdvd⟩
    rw [← profile_transpose N M R S y x, ← profile_transpose N M R S z x]
    exact hconst y z x
  have h3 : ∀ M : ℕ, 0 < M → possible N t r s M → min dr ds ≤ M := by
    intro M hM0 ⟨R, S, hdims, hflat⟩
    by_contra hlt
    have hlt' : M < min dr ds := Nat.lt_of_not_ge hlt
    have hMdr : M < dr := lt_of_lt_of_le hlt' (min_le_left dr ds)
    have hMds : M < ds := lt_of_lt_of_le hlt' (min_le_right dr ds)
    have hdr : dr ∣ M := (h5_row M R S hdims hflat hMds).2
    have hle : dr ≤ M := Nat.le_of_dvd hM0 hdr
    omega
  have h4 : ∀ M : ℕ, M < max dr ds → (possible N t r s M ↔ dr ∣ M ∨ ds ∣ M) := by
    intro M hMmax
    constructor
    · rintro ⟨R, S, hdims, hflat⟩
      rcases lt_max_iff.mp hMmax with hMdr | hMds
      · exact Or.inr (h5_col M R S hdims hflat hMdr).2
      · exact Or.inl (h5_row M R S hdims hflat hMds).2
    · rintro (hdr | hds)
      · exact possible_of_dvd_dr hr0 hrN hsN hdr
      · exact possible_of_dvd_ds ht0 htN hrN hs0 hsN hds
  refine ⟨h1, h2, h3, h4, fun M R S hdims hflat => ?_⟩
  exact ⟨fun hM => (h5_row M R S hdims hflat hM).1, fun hM => (h5_col M R S hdims hflat hM).1⟩

end PEqualNP.Outside.L_lib_1014_aux

theorem PEqualNP.Outside.L_lib_1014 : (∀ (N t r s : ℕ), 0 < t → t < N → 0 < r → r ≤ N → 0 < s → s ≤ N →
  let X := Fin N
  let reg := fun (T : X → X → Bool) =>
    (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
  let value := fun (B : X → X → ℝ) (T : X → X → Bool) =>
    ∑ x, ∑ y, if T x y then B x y else 0
  let flat := fun (B : X → X → ℝ) =>
    ∀ T U, reg T → reg U → value B T = value B U
  let profile := fun (M : ℕ) (R S : Fin M → Finset X) (x y : X) =>
    (∑ i : Fin M, if x ∈ R i ∧ y ∈ S i then (1 : ℝ) else 0)
  let dims := fun (M : ℕ) (R S : Fin M → Finset X) =>
    ∀ i, (R i).card = r ∧ (S i).card = s
  let possible := fun (M : ℕ) => ∃ R S, dims M R S ∧ flat (profile M R S)
  let dr := N / Nat.gcd N r
  let ds := N / Nat.gcd N s
  (∀ B, flat B ↔ ∃ a b : X → ℝ, ∀ x y, B x y = a x + b y) ∧
  possible (min dr ds) ∧
  (∀ M : ℕ, 0 < M → possible M → min dr ds ≤ M) ∧
  (∀ M : ℕ, M < max dr ds → (possible M ↔ dr ∣ M ∨ ds ∣ M)) ∧
  ∀ (M : ℕ) (R S : Fin M → Finset X), dims M R S → flat (profile M R S) →
    (M < ds → ∀ x z y, profile M R S x y = profile M R S z y) ∧
    (M < dr → ∀ x y z, profile M R S x y = profile M R S x z)) := by
  exact PEqualNP.Outside.L_lib_1014_aux.main
