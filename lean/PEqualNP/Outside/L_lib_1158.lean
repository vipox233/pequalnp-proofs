import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_1158_aux

open Finset

variable {n m : ℕ}

def cutS (u v : Fin m → Fin n) (S : Finset (Fin n)) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => decide (u i ∈ S) != decide (v i ∈ S))

theorem mem_cut {u v : Fin m → Fin n} {S : Finset (Fin n)} {i : Fin m} :
    i ∈ cutS u v S ↔ ¬ (u i ∈ S ↔ v i ∈ S) := by
  unfold cutS
  simp only [mem_filter, mem_univ, true_and]
  by_cases h1 : u i ∈ S <;> by_cases h2 : v i ∈ S <;> simp [h1, h2]

theorem cut_card_zero {u v : Fin m → Fin n} {S : Finset (Fin n)} :
    (cutS u v S).card = 0 ↔ ∀ i, (u i ∈ S ↔ v i ∈ S) := by
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  simp only [mem_cut, not_not]

def E (u v : Fin m → Fin n) (X : Finset (Fin n)) : Finset (Fin m) :=
  univ.filter (fun i => u i ∈ X ∧ v i ∈ X)

theorem mem_E {u v : Fin m → Fin n} {X : Finset (Fin n)} {i : Fin m} :
    i ∈ E u v X ↔ u i ∈ X ∧ v i ∈ X := by
  simp [E]

structure IsComp (u v : Fin m → Fin n) (C : Finset (Fin n)) : Prop where
  ne : C.Nonempty
  closed : ∀ i, (u i ∈ C ↔ v i ∈ C)
  minimal : ∀ D ⊆ C, D.Nonempty → (∀ i, (u i ∈ D ↔ v i ∈ D)) → D = C

theorem comp_eq {u v : Fin m → Fin n} {C D : Finset (Fin n)} (hC : IsComp u v C)
    (hD : IsComp u v D) {x : Fin n} (hxC : x ∈ C) (hxD : x ∈ D) : C = D := by
  have hcl : ∀ i, (u i ∈ C ∩ D ↔ v i ∈ C ∩ D) := by
    intro i; simp only [mem_inter, hC.closed i, hD.closed i]
  have h1 := hC.minimal (C ∩ D) inter_subset_left ⟨x, mem_inter.2 ⟨hxC, hxD⟩⟩ hcl
  have h2 := hD.minimal (C ∩ D) inter_subset_right ⟨x, mem_inter.2 ⟨hxC, hxD⟩⟩ hcl
  rw [← h1, h2]

theorem exists_comp (u v : Fin m → Fin n) (x : Fin n) : ∃ C, IsComp u v C ∧ x ∈ C := by
  classical
  set S := (univ : Finset (Finset (Fin n))).filter
    (fun D => x ∈ D ∧ ∀ i, (u i ∈ D ↔ v i ∈ D)) with hS
  have hne : S.Nonempty := ⟨univ, by simp [hS]⟩
  obtain ⟨D, hD, hmin⟩ := S.exists_min_image card hne
  simp only [hS, mem_filter, mem_univ, true_and] at hD hmin
  refine ⟨D, ⟨⟨x, hD.1⟩, hD.2, ?_⟩, hD.1⟩
  intro D' hD' hne' hcl'
  by_cases hx : x ∈ D'
  · exact eq_of_subset_of_card_le hD' (hmin D' ⟨hx, hcl'⟩)
  · exfalso
    have h1 := hmin (D \ D') ⟨mem_sdiff.2 ⟨hD.1, hx⟩, by
      intro i; simp only [mem_sdiff, hD.2 i, hcl' i]⟩
    have h2 := card_sdiff_add_card_eq_card hD'
    have h3 : 0 < D'.card := card_pos.2 hne'
    omega

theorem superdense_aux {u v : Fin m → Fin n} {C : Finset (Fin n)} (hC : IsComp u v C) :
    ∀ k : ℕ, ∀ X : Finset (Fin n), X ⊆ C → X.Nonempty → (C \ X).card = k →
      (E u v X).card + k ≤ (E u v C).card := by
  intro k
  induction k with
  | zero =>
    intro X hX _ hk
    have hCX : C ⊆ X := by
      intro w hw; by_contra h
      have hw' : w ∈ C \ X := mem_sdiff.2 ⟨hw, h⟩
      rw [card_eq_zero] at hk; rw [hk] at hw'; simp at hw'
    have hXC : X = C := Subset.antisymm hX hCX
    subst hXC; simp
  | succ k ih =>
    intro X hX hne hk
    have hXC : X ≠ C := by
      rintro rfl; simp at hk
    obtain ⟨i, hi⟩ : ∃ i, ¬ (u i ∈ X ↔ v i ∈ X) := by
      by_contra h; push Not at h; exact hXC (hC.minimal X hX hne h)
    obtain ⟨w, hwX, hwC, huw, hvw⟩ : ∃ w, w ∉ X ∧ w ∈ C ∧ u i ∈ insert w X ∧
        v i ∈ insert w X := by
      by_cases hu : u i ∈ X
      · have hv : v i ∉ X := fun hv => hi ⟨fun _ => hv, fun _ => hu⟩
        exact ⟨v i, hv, (hC.closed i).1 (hX hu), mem_insert_of_mem hu, mem_insert_self _ _⟩
      · have hv : v i ∈ X := by
          by_contra hv; exact hi ⟨fun h => absurd h hu, fun h => absurd h hv⟩
        exact ⟨u i, hu, (hC.closed i).2 (hX hv), mem_insert_self _ _, mem_insert_of_mem hv⟩
    have hX' : insert w X ⊆ C := insert_subset hwC hX
    have hk' : (C \ insert w X).card = k := by
      have : C \ insert w X = (C \ X).erase w := by
        ext y; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
      rw [this, card_erase_of_mem (mem_sdiff.2 ⟨hwC, hwX⟩), hk]; rfl
    have h1 := ih (insert w X) hX' (insert_nonempty _ _) hk'
    have hsub : insert i (E u v X) ⊆ E u v (insert w X) := by
      intro j hj
      rw [mem_insert] at hj
      rcases hj with rfl | hj
      · exact mem_E.2 ⟨huw, hvw⟩
      · rw [mem_E] at hj ⊢
        exact ⟨mem_insert_of_mem hj.1, mem_insert_of_mem hj.2⟩
    have hiE : i ∉ E u v X := by
      rw [mem_E]; intro h; exact hi ⟨fun _ => h.2, fun _ => h.1⟩
    have h2 := card_le_card hsub
    rw [card_insert_of_notMem hiE] at h2
    omega

theorem L1 {u v : Fin m → Fin n} {C X : Finset (Fin n)} (hC : IsComp u v C) (hX : X ⊆ C)
    (hne : X.Nonempty) : (E u v X).card + (C \ X).card ≤ (E u v C).card :=
  superdense_aux hC _ X hX hne rfl

theorem superdense {u v : Fin m → Fin n} {C X : Finset (Fin n)} (hC : IsComp u v C)
    (hle : (E u v C).card ≤ C.card) (hX : X ⊆ C) (hd : X.card + 1 ≤ (E u v X).card) : False := by
  have hne : X.Nonempty := by
    obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < (E u v X).card)
    exact ⟨u i, (mem_E.1 hi).1⟩
  have h1 := L1 hC hX hne
  have h2 := card_sdiff_add_card_eq_card hX
  omega

theorem dense_eq {u v : Fin m → Fin n} {C X : Finset (Fin n)} (hC : IsComp u v C)
    (hle : (E u v C).card ≤ C.card) (hX : X ⊆ C) (hne : X.Nonempty)
    (hd : X.card ≤ (E u v X).card) : (E u v C).card = C.card := by
  have h1 := L1 hC hX hne
  have h2 := card_sdiff_add_card_eq_card hX
  omega

theorem DD_step {u v : Fin m → Fin n} {C X Y : Finset (Fin n)} (hC : IsComp u v C)
    (hle : (E u v C).card ≤ C.card) (hX : X ⊆ C) (hY : Y ⊆ C) (hXne : X.Nonempty)
    (hYne : Y.Nonempty) (hXY : Disjoint X Y) (hdX : X.card ≤ (E u v X).card)
    (hdY : Y.card ≤ (E u v Y).card) :
    ∃ w, w ∈ C ∧ w ∉ X ∧ w ∉ Y ∧ (insert w X).card ≤ (E u v (insert w X)).card := by
  have hXC : X ≠ C := by
    rintro rfl
    obtain ⟨y, hy⟩ := hYne
    exact disjoint_left.1 hXY (hY hy) hy
  obtain ⟨i, hi⟩ : ∃ i, ¬ (u i ∈ X ↔ v i ∈ X) := by
    by_contra h; push Not at h; exact hXC (hC.minimal X hX hXne h)
  obtain ⟨w, x0, hwX, hwC, hx0, hend⟩ : ∃ w x0, w ∉ X ∧ w ∈ C ∧ x0 ∈ X ∧
      ((u i = w ∧ v i = x0) ∨ (u i = x0 ∧ v i = w)) := by
    by_cases hu : u i ∈ X
    · have hv : v i ∉ X := fun hv => hi ⟨fun _ => hv, fun _ => hu⟩
      exact ⟨v i, u i, hv, (hC.closed i).1 (hX hu), hu, Or.inr ⟨rfl, rfl⟩⟩
    · have hv : v i ∈ X := by
        by_contra hv; exact hi ⟨fun h => absurd h hu, fun h => absurd h hv⟩
      exact ⟨u i, v i, hu, (hC.closed i).2 (hX hv), hv, Or.inl ⟨rfl, rfl⟩⟩
  have hiE : i ∉ E u v X := by
    rw [mem_E]; intro h; exact hi ⟨fun _ => h.2, fun _ => h.1⟩
  by_cases hwY : w ∈ Y
  · exfalso
    have hsub : insert i (E u v X ∪ E u v Y) ⊆ E u v (X ∪ Y) := by
      intro j hj
      rw [mem_insert, mem_union] at hj
      rw [mem_E, mem_union, mem_union]
      rcases hj with rfl | hj | hj
      · rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp [hwY, hx0]
      · rw [mem_E] at hj; exact ⟨Or.inl hj.1, Or.inl hj.2⟩
      · rw [mem_E] at hj; exact ⟨Or.inr hj.1, Or.inr hj.2⟩
    have hdisj : Disjoint (E u v X) (E u v Y) := by
      rw [disjoint_left]; intro j hjX hjY
      exact disjoint_left.1 hXY (mem_E.1 hjX).1 (mem_E.1 hjY).1
    have hiY : i ∉ E u v Y := by
      rw [mem_E]; intro h
      rcases hend with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact disjoint_left.1 hXY hx0 (h2 ▸ h.2)
      · exact disjoint_left.1 hXY hx0 (h1 ▸ h.1)
    have hiU : i ∉ E u v X ∪ E u v Y := by
      rw [mem_union]; rintro (h | h)
      · exact hiE h
      · exact hiY h
    have h1 := card_le_card hsub
    rw [card_insert_of_notMem hiU, card_union_of_disjoint hdisj] at h1
    have h2 : (X ∪ Y).card = X.card + Y.card := card_union_of_disjoint hXY
    exact superdense hC hle (union_subset hX hY) (by omega)
  · refine ⟨w, hwC, hwX, hwY, ?_⟩
    have hsub : insert i (E u v X) ⊆ E u v (insert w X) := by
      intro j hj
      rw [mem_insert] at hj
      rcases hj with rfl | hj
      · rw [mem_E]
        rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp [hx0]
      · rw [mem_E] at hj ⊢
        exact ⟨mem_insert_of_mem hj.1, mem_insert_of_mem hj.2⟩
    have h2 := card_le_card hsub
    rw [card_insert_of_notMem hiE] at h2
    rw [card_insert_of_notMem hwX]
    omega

theorem DD_aux {u v : Fin m → Fin n} {C : Finset (Fin n)} (hC : IsComp u v C)
    (hle : (E u v C).card ≤ C.card) : ∀ k : ℕ, ∀ X Y : Finset (Fin n), X ⊆ C → Y ⊆ C →
      X.Nonempty → Y.Nonempty → Disjoint X Y → X.card ≤ (E u v X).card →
      Y.card ≤ (E u v Y).card → (C \ (X ∪ Y)).card = k → False := by
  intro k
  induction k with
  | zero =>
    intro X Y hX hY hXne hYne hXY hdX hdY hk
    obtain ⟨w, hwC, hwX, hwY, _⟩ := DD_step hC hle hX hY hXne hYne hXY hdX hdY
    have : w ∈ C \ (X ∪ Y) := by simp [hwC, hwX, hwY]
    rw [card_eq_zero] at hk; rw [hk] at this; simp at this
  | succ k ih =>
    intro X Y hX hY hXne hYne hXY hdX hdY hk
    obtain ⟨w, hwC, hwX, hwY, hd⟩ := DD_step hC hle hX hY hXne hYne hXY hdX hdY
    refine ih (insert w X) Y (insert_subset hwC hX) hY (insert_nonempty _ _) hYne ?_ hd hdY ?_
    · rw [disjoint_insert_left]; exact ⟨hwY, hXY⟩
    · have : C \ (insert w X ∪ Y) = (C \ (X ∪ Y)).erase w := by
        ext y; simp only [mem_sdiff, mem_union, mem_insert, mem_erase]; tauto
      rw [this, card_erase_of_mem (by simp [hwC, hwX, hwY]), hk]; rfl

theorem DD {u v : Fin m → Fin n} {C X Y : Finset (Fin n)} (hC : IsComp u v C)
    (hle : (E u v C).card ≤ C.card) (hX : X ⊆ C) (hY : Y ⊆ C) (hXne : X.Nonempty)
    (hYne : Y.Nonempty) (hXY : Disjoint X Y) (hdX : X.card ≤ (E u v X).card)
    (hdY : Y.card ≤ (E u v Y).card) : False :=
  DD_aux hC hle _ X Y hX hY hXne hYne hXY hdX hdY rfl

/-! ## Probe reformulation -/

def Sol (u v : Fin m → Fin n) (p : Fin m → Bool × Bool) (x : Finset (Fin n)) : Prop :=
  ∀ i, (decide (u i ∈ x), decide (v i ∈ x)) ≠ p i

def sh (y x : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun w => decide (w ∈ x) != decide (w ∈ y))

theorem decide_mem_sh (y x : Finset (Fin n)) (w : Fin n) :
    decide (w ∈ sh y x) = (decide (w ∈ x) != decide (w ∈ y)) := by
  by_cases h1 : w ∈ x <;> by_cases h2 : w ∈ y <;> simp [sh, h1, h2]

theorem mem_sh {y x : Finset (Fin n)} {w : Fin n} : w ∈ sh y x ↔ ¬ (w ∈ x ↔ w ∈ y) := by
  by_cases h1 : w ∈ x <;> by_cases h2 : w ∈ y <;> simp [sh, h1, h2]

theorem sh_parity (x y H : Finset (Fin n)) :
    (sh y x ∩ H).card % 2 = ((x ∩ H).card + (y ∩ H).card) % 2 := by
  have h1 : sh y x ∩ H = ((x ∩ H) \ (y ∩ H)) ∪ ((y ∩ H) \ (x ∩ H)) := by
    ext w; simp only [mem_inter, mem_sdiff, mem_union, mem_sh]; tauto
  have h2 : Disjoint ((x ∩ H) \ (y ∩ H)) ((y ∩ H) \ (x ∩ H)) := by
    rw [disjoint_left]; intro a ha hb; simp only [mem_sdiff] at ha hb; exact ha.2 hb.1
  have h3 := card_sdiff_add_card_inter (x ∩ H) (y ∩ H)
  have h4 := card_sdiff_add_card_inter (y ∩ H) (x ∩ H)
  rw [h1, card_union_of_disjoint h2]
  rw [inter_comm (y ∩ H) (x ∩ H)] at h4
  omega

theorem bool_key1 : ∀ a c q1 b d q2 : Bool,
    ((a != c, b != d) ≠ (q1, q2)) ↔ ((a, b) ≠ (xor q1 c, xor q2 d)) := by decide

theorem bool_key2 : ∀ c d q1 q2 : Bool, (q1, q2) ≠ (false, false) →
    (c, d) ≠ (xor q1 c, xor q2 d) := by decide

theorem one_dir {u v : Fin m → Fin n} {r : ℕ} {H : Fin r → Finset (Fin n)}
    (q : Fin m → Bool × Bool) (hq : ∀ i, q i ≠ (false, false))
    (hev : ∀ z, Sol u v q z → ∀ j, (z ∩ H j).card % 2 = 0)
    (A B : Finset (Finset (Fin n)))
    (hAB : ∀ p, (∃ x ∈ A, Sol u v p x) → (∃ x ∈ B, Sol u v p x)) (z : Finset (Fin n)) :
    (∃ x ∈ A, ∀ j, (x ∩ H j).card % 2 = (z ∩ H j).card % 2) →
    (∃ x ∈ B, ∀ j, (x ∩ H j).card % 2 = (z ∩ H j).card % 2) := by
  rintro ⟨x, hxA, hxz⟩
  let p : Fin m → Bool × Bool :=
    fun i => (xor (q i).1 (decide (u i ∈ x)), xor (q i).2 (decide (v i ∈ x)))
  have hpx : Sol u v p x := by
    intro i
    exact bool_key2 _ _ _ _ (hq i)
  obtain ⟨x', hx'B, hx'⟩ := hAB p ⟨x, hxA, hpx⟩
  refine ⟨x', hx'B, fun j => ?_⟩
  have hsol : Sol u v q (sh x x') := by
    intro i
    rw [decide_mem_sh, decide_mem_sh]
    exact (bool_key1 _ _ (q i).1 _ _ (q i).2).2 (hx' i)
  have h1 := hev _ hsol j
  have h2 := sh_parity x' x (H j)
  have h3 := hxz j
  omega

theorem Q_to_LHS {u v : Fin m → Fin n} {r : ℕ} {H : Fin r → Finset (Fin n)}
    (hQ : ∃ q : Fin m → Bool × Bool, (∀ i, q i ≠ (false, false)) ∧
      ∀ z, Sol u v q z → ∀ j, (z ∩ H j).card % 2 = 0) :
    ∀ A B : Finset (Finset (Fin n)), (∀ p, (∃ x ∈ A, Sol u v p x) ↔ (∃ x ∈ B, Sol u v p x)) →
      ∀ z : Finset (Fin n), ((∃ x ∈ A, ∀ j, (x ∩ H j).card % 2 = (z ∩ H j).card % 2) ↔
        ∃ x ∈ B, ∀ j, (x ∩ H j).card % 2 = (z ∩ H j).card % 2) := by
  obtain ⟨q, hq, hev⟩ := hQ
  intro A B hAB z
  exact ⟨one_dir q hq hev A B (fun p => (hAB p).1) z, one_dir q hq hev B A (fun p => (hAB p).2) z⟩

theorem LHS_to_Q {u v : Fin m → Fin n} {r : ℕ} {H : Fin r → Finset (Fin n)}
    (hL : ∀ A B : Finset (Finset (Fin n)),
      (∀ p, (∃ x ∈ A, Sol u v p x) ↔ (∃ x ∈ B, Sol u v p x)) →
      ∀ z : Finset (Fin n), ((∃ x ∈ A, ∀ j, (x ∩ H j).card % 2 = (z ∩ H j).card % 2) ↔
        ∃ x ∈ B, ∀ j, (x ∩ H j).card % 2 = (z ∩ H j).card % 2)) :
    ∃ q : Fin m → Bool × Bool, (∀ i, q i ≠ (false, false)) ∧
      ∀ z, Sol u v q z → ∀ j, (z ∩ H j).card % 2 = 0 := by
  by_contra hne
  push Not at hne
  let A := (univ : Finset (Finset (Fin n))).filter
    (fun x => ¬ ∀ j, (x ∩ H j).card % 2 = ((∅ : Finset (Fin n)) ∩ H j).card % 2)
  have hprof : ∀ p, (∃ x ∈ A, Sol u v p x) ↔ (∃ x ∈ insert ∅ A, Sol u v p x) := by
    intro p
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, mem_insert_of_mem hx, h⟩
    · rintro ⟨x, hx, h⟩
      rw [mem_insert] at hx
      rcases hx with rfl | hx
      · have hv : ∀ i, p i ≠ (false, false) := fun i heq => h i (by rw [heq]; simp)
        obtain ⟨z, hz, j, hj⟩ := hne p hv
        refine ⟨z, mem_filter.2 ⟨mem_univ _, fun hall => hj ?_⟩, hz⟩
        have := hall j
        simpa using this
      · exact ⟨x, hx, h⟩
  have h := (hL A (insert ∅ A) hprof ∅).2 ⟨∅, mem_insert_self _ _, fun j => rfl⟩
  obtain ⟨x, hx, hxs⟩ := h
  exact (mem_filter.1 hx).2 hxs

/-! ## Hall orientation -/

theorem global_pf {u v : Fin m → Fin n} (hpf : ∀ C, IsComp u v C → (E u v C).card ≤ C.card) :
    ∀ k, ∀ X : Finset (Fin n), X.card = k → (E u v X).card ≤ X.card := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro X hXk
  rcases X.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp [E]
  obtain ⟨C, hC, hxC⟩ := exists_comp u v x
  have hlt : (X \ C).card < k := by
    have h1 := card_sdiff_add_card_inter X C
    have h2 : 0 < (X ∩ C).card := card_pos.2 ⟨x, mem_inter.2 ⟨hx, hxC⟩⟩
    omega
  have h1 : (E u v (X \ C)).card ≤ (X \ C).card := ih _ hlt _ rfl
  have h2 : (E u v (X ∩ C)).card ≤ (X ∩ C).card := by
    have h3 := L1 hC inter_subset_right ⟨x, mem_inter.2 ⟨hx, hxC⟩⟩
    have h4 := hpf C hC
    have h5 : (C \ (X ∩ C)).card + (X ∩ C).card = C.card :=
      card_sdiff_add_card_eq_card inter_subset_right
    omega
  have h3 : E u v X ⊆ E u v (X ∩ C) ∪ E u v (X \ C) := by
    intro i hi; rw [mem_E] at hi; rw [mem_union, mem_E, mem_E]
    by_cases h : u i ∈ C
    · left; exact ⟨mem_inter.2 ⟨hi.1, h⟩, mem_inter.2 ⟨hi.2, (hC.closed i).1 h⟩⟩
    · right; exact ⟨mem_sdiff.2 ⟨hi.1, h⟩, mem_sdiff.2 ⟨hi.2, fun h' => h ((hC.closed i).2 h')⟩⟩
  have h4 := card_le_card h3
  have h5 := card_union_le (E u v (X ∩ C)) (E u v (X \ C))
  have h6 := card_inter_add_card_sdiff X C
  omega

theorem exists_orient {u v : Fin m → Fin n}
    (hpf : ∀ C, IsComp u v C → (E u v C).card ≤ C.card) :
    ∃ τ : Fin m → Fin n, Function.Injective τ ∧ ∀ i, τ i = u i ∨ τ i = v i := by
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun i => ({u i, v i} : Finset (Fin n)))).1 (by
      intro K
      have hK : K ⊆ E u v (K.biUnion (fun i => ({u i, v i} : Finset (Fin n)))) := by
        intro i hi; rw [mem_E]; constructor <;> (rw [mem_biUnion]; exact ⟨i, hi, by simp⟩)
      exact (card_le_card hK).trans (global_pf hpf _ _ rfl))
  exact ⟨f, hf, fun i => by have := hmem i; simpa using this⟩

/-! ## Functional orientation -/

section Orient

variable {u v : Fin m → Fin n} {τ : Fin m → Fin n}

def hd (u v τ : Fin m → Fin n) (i : Fin m) : Fin n := if τ i = u i then v i else u i

theorem ends (hτ : ∀ i, τ i = u i ∨ τ i = v i) (i : Fin m) :
    (u i = τ i ∧ v i = hd u v τ i) ∨ (u i = hd u v τ i ∧ v i = τ i) := by
  unfold hd
  by_cases h : τ i = u i
  · left; simp [h]
  · right; rw [if_neg h]; exact ⟨rfl, ((hτ i).resolve_left h).symm⟩

theorem hd_ne (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i) (i : Fin m) :
    τ i ≠ hd u v τ i := by
  rcases ends hτ i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact huv i
  · rw [← h1, ← h2]; exact (huv i).symm

theorem cross_iff (hτ : ∀ i, τ i = u i ∨ τ i = v i) (i : Fin m) (W : Finset (Fin n)) :
    (u i ∈ W ↔ v i ∈ W) ↔ (τ i ∈ W ↔ hd u v τ i ∈ W) := by
  rcases ends hτ i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact iff_comm

theorem both_iff (hτ : ∀ i, τ i = u i ∨ τ i = v i) (i : Fin m) (W : Finset (Fin n)) :
    (u i ∈ W ∧ v i ∈ W) ↔ (τ i ∈ W ∧ hd u v τ i ∈ W) := by
  rcases ends hτ i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact and_comm

noncomputable def Fs (u v τ : Fin m → Fin n) (x : Fin n) : Fin n :=
  if hx : ∃ i, τ i = x then hd u v τ (Classical.choose hx) else x

theorem Fs_tau (hinj : Function.Injective τ) (i : Fin m) : Fs u v τ (τ i) = hd u v τ i := by
  have h : ∃ j, τ j = τ i := ⟨i, rfl⟩
  unfold Fs
  rw [dif_pos h, hinj (Classical.choose_spec h)]

theorem Fs_of_not (x : Fin n) (hx : ¬ ∃ i, τ i = x) : Fs u v τ x = x := by
  unfold Fs; rw [dif_neg hx]

def PerP (u v τ : Fin m → Fin n) (x : Fin n) : Prop := ∃ k, 0 < k ∧ (Fs u v τ)^[k] x = x

def Per (u v τ : Fin m → Fin n) (x : Fin n) : Prop := (∃ i, τ i = x) ∧ PerP u v τ x

theorem iter_mul {f : Fin n → Fin n} {x : Fin n} {k : ℕ} (h : f^[k] x = x) :
    ∀ c, f^[k * c] x = x := by
  intro c
  induction c with
  | zero => simp
  | succ c ih => rw [Nat.mul_succ, Function.iterate_add_apply, h, ih]

theorem perP_hd (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {i : Fin m} (hp : PerP u v τ (τ i)) :
    Per u v τ (hd u v τ i) := by
  obtain ⟨k, hk, hkx⟩ := hp
  have hper : (Fs u v τ)^[k] (hd u v τ i) = hd u v τ i := by
    rw [← Fs_tau hinj i, ← Function.iterate_succ_apply, Function.iterate_succ_apply', hkx]
  refine ⟨?_, k, hk, hper⟩
  by_contra hno
  have hfix : Fs u v τ (hd u v τ i) = hd u v τ i := Fs_of_not _ hno
  have h2 : (Fs u v τ)^[k] (τ i) = hd u v τ i := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Function.iterate_succ_apply, Fs_tau hinj i, Function.iterate_fixed hfix]
  rw [hkx] at h2
  exact hd_ne huv hτ i h2

theorem per_Fs (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {x : Fin n} (hx : Per u v τ x) : Per u v τ (Fs u v τ x) := by
  obtain ⟨⟨i, rfl⟩, hp⟩ := hx
  rw [Fs_tau hinj i]
  exact perP_hd huv hτ hinj hp

theorem per_iter (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {x : Fin n} (hx : Per u v τ x) :
    ∀ l, Per u v τ ((Fs u v τ)^[l] x) := by
  intro l
  induction l with
  | zero => exact hx
  | succ l ih => rw [Function.iterate_succ_apply']; exact per_Fs huv hτ hinj ih

open Classical in
noncomputable def Orb (u v τ : Fin m → Fin n) (x : Fin n) : Finset (Fin n) :=
  univ.filter (fun w => ∃ l, (Fs u v τ)^[l] x = w)

theorem mem_Orb {x w : Fin n} : w ∈ Orb u v τ x ↔ ∃ l, (Fs u v τ)^[l] x = w := by
  simp [Orb]

theorem self_mem_Orb (x : Fin n) : x ∈ Orb u v τ x := mem_Orb.2 ⟨0, rfl⟩

theorem dense_orb (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {x : Fin n} (hx : Per u v τ x) :
    (Orb u v τ x).card ≤ (E u v (Orb u v τ x)).card := by
  have hsub : Orb u v τ x ⊆ (E u v (Orb u v τ x)).image τ := by
    intro w hw
    obtain ⟨l, rfl⟩ := mem_Orb.1 hw
    obtain ⟨⟨i, hi⟩, _⟩ := per_iter huv hτ hinj hx l
    rw [mem_image]
    refine ⟨i, ?_, hi⟩
    rw [mem_E, both_iff hτ i]
    refine ⟨hi ▸ hw, mem_Orb.2 ⟨l + 1, ?_⟩⟩
    rw [Function.iterate_succ_apply', ← hi, Fs_tau hinj i]
  exact (card_le_card hsub).trans card_image_le

theorem Fs_mem (hτ : ∀ i, τ i = u i ∨ τ i = v i) (hinj : Function.Injective τ)
    {C : Finset (Fin n)} (hC : IsComp u v C) {w : Fin n} (hw : w ∈ C) : Fs u v τ w ∈ C := by
  by_cases h : ∃ i, τ i = w
  · obtain ⟨i, rfl⟩ := h
    rw [Fs_tau hinj i]
    exact ((cross_iff hτ i C).1 (hC.closed i)).1 hw
  · rw [Fs_of_not w h]; exact hw

theorem iter_mem (hτ : ∀ i, τ i = u i ∨ τ i = v i) (hinj : Function.Injective τ)
    {C : Finset (Fin n)} (hC : IsComp u v C) {w : Fin n} (hw : w ∈ C) :
    ∀ l, (Fs u v τ)^[l] w ∈ C := by
  intro l
  induction l with
  | zero => exact hw
  | succ l ih => rw [Function.iterate_succ_apply']; exact Fs_mem hτ hinj hC ih

theorem orb_sub (hτ : ∀ i, τ i = u i ∨ τ i = v i) (hinj : Function.Injective τ)
    {C : Finset (Fin n)} (hC : IsComp u v C) {x : Fin n} (hx : x ∈ C) : Orb u v τ x ⊆ C := by
  intro w hw
  obtain ⟨l, rfl⟩ := mem_Orb.1 hw
  exact iter_mem hτ hinj hC hx l

theorem per_uniq (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {C : Finset (Fin n)} (hC : IsComp u v C)
    (hle : (E u v C).card ≤ C.card) {x y : Fin n} (hx : Per u v τ x) (hy : Per u v τ y)
    (hxC : x ∈ C) (hyC : y ∈ C) : ∃ c, (Fs u v τ)^[c] x = y := by
  by_contra hno
  push Not at hno
  refine DD hC hle (orb_sub hτ hinj hC hxC) (orb_sub hτ hinj hC hyC) ⟨x, self_mem_Orb x⟩
    ⟨y, self_mem_Orb y⟩ ?_ (dense_orb huv hτ hinj hx) (dense_orb huv hτ hinj hy)
  rw [disjoint_left]
  intro w hwx hwy
  obtain ⟨a, rfl⟩ := mem_Orb.1 hwx
  obtain ⟨b, hb⟩ := mem_Orb.1 hwy
  obtain ⟨k, hk, hky⟩ := hy.2
  have hbk : b ≤ k * b := Nat.le_mul_of_pos_left b hk
  apply hno (k * b - b + a)
  rw [Function.iterate_add_apply, ← hb, ← Function.iterate_add_apply, Nat.sub_add_cancel hbk,
    iter_mul hky b]

open Classical in
noncomputable def IT (u v τ : Fin m → Fin n) (y : Fin n) : Finset (Fin n) :=
  univ.filter (fun w => ∃ k, (Fs u v τ)^[k] w = y)

theorem mem_IT {y w : Fin n} : w ∈ IT u v τ y ↔ ∃ k, (Fs u v τ)^[k] w = y := by
  simp [IT]

theorem cut_IT (hτ : ∀ i, τ i = u i ∨ τ i = v i) (hinj : Function.Injective τ) (i : Fin m)
    (hnp : ¬ PerP u v τ (τ i)) : cutS u v (IT u v τ (τ i)) = {i} := by
  ext j
  rw [mem_cut, mem_singleton, cross_iff hτ j, mem_IT, mem_IT]
  constructor
  · intro hj
    by_contra hji
    apply hj
    have hne : τ j ≠ τ i := fun h => hji (hinj h)
    constructor
    · rintro ⟨k, hk⟩
      cases k with
      | zero => exact absurd hk hne
      | succ k =>
        refine ⟨k, ?_⟩
        rw [← Fs_tau hinj j, ← Function.iterate_succ_apply]
        exact hk
    · rintro ⟨k, hk⟩
      exact ⟨k + 1, by rw [Function.iterate_succ_apply, Fs_tau hinj j]; exact hk⟩
  · intro hji h
    rw [hji] at h
    obtain ⟨k, hk⟩ := h.1 ⟨0, rfl⟩
    apply hnp
    exact ⟨k + 1, Nat.succ_pos _, by rw [Function.iterate_succ_apply, Fs_tau hinj i]; exact hk⟩

theorem not_cut_single (hτ : ∀ i, τ i = u i ∨ τ i = v i) (hinj : Function.Injective τ)
    (i : Fin m) (hp : PerP u v τ (τ i)) (W : Finset (Fin n)) : cutS u v W ≠ {i} := by
  intro hW
  have hcross : ∀ j, j ≠ i → (τ j ∈ W ↔ hd u v τ j ∈ W) := by
    intro j hj
    have h1 : j ∉ cutS u v W := by rw [hW, mem_singleton]; exact hj
    rw [mem_cut, not_not, cross_iff hτ j] at h1
    exact h1
  have hi : ¬ (τ i ∈ W ↔ hd u v τ i ∈ W) := by
    have h1 : i ∈ cutS u v W := by rw [hW]; exact mem_singleton_self i
    rw [mem_cut, cross_iff hτ i] at h1; exact h1
  have hstep : ∀ w, w ≠ τ i → (w ∈ W ↔ Fs u v τ w ∈ W) := by
    intro w hw
    by_cases h : ∃ j, τ j = w
    · obtain ⟨j, rfl⟩ := h
      rw [Fs_tau hinj j]
      exact hcross j (fun h => hw (by rw [h]))
    · rw [Fs_of_not w h]
  classical
  have hk0 : 0 < Nat.find hp ∧ (Fs u v τ)^[Nat.find hp] (τ i) = τ i := Nat.find_spec hp
  have hmin : ∀ l, 0 < l → l < Nat.find hp → (Fs u v τ)^[l] (τ i) ≠ τ i :=
    fun l hl hlk h => Nat.find_min hp hlk ⟨hl, h⟩
  have key : ∀ l, 1 ≤ l → l ≤ Nat.find hp →
      ((Fs u v τ)^[1] (τ i) ∈ W ↔ (Fs u v τ)^[l] (τ i) ∈ W) := by
    intro l
    induction l with
    | zero => intro h; omega
    | succ l ih =>
      intro _ hlk
      rcases Nat.eq_zero_or_pos l with rfl | hl'
      · exact Iff.rfl
      · rw [ih hl' (by omega), Function.iterate_succ_apply']
        exact hstep _ (hmin l hl' (by omega))
  have h1 := key (Nat.find hp) hk0.1 le_rfl
  rw [hk0.2, Function.iterate_one, Fs_tau hinj i] at h1
  exact hi h1.symm

end Orient

/-! ## Constructions -/

section Constr

variable {u v : Fin m → Fin n} {τ : Fin m → Fin n}

theorem u_mem_of_tau (hτ : ∀ i, τ i = u i ∨ τ i = v i) {C : Finset (Fin n)} (hC : IsComp u v C)
    {i : Fin m} (h : τ i ∈ C) : u i ∈ C :=
  (hτ i).elim (fun e => e ▸ h) (fun e => (hC.closed i).2 (e ▸ h))

theorem walk (hτ : ∀ i, τ i = u i ∨ τ i = v i) (hinj : Function.Injective τ)
    {C : Finset (Fin n)} (hC : IsComp u v C) (z : Finset (Fin n)) (P : Fin m → Prop)
    (hz : ∀ i, u i ∈ C → P i → τ i ∈ z → hd u v τ i ∈ z) {x : Fin n} (hxC : x ∈ C)
    (hxz : x ∈ z) : ∀ L : ℕ, (∀ l < L, ∃ i, τ i = (Fs u v τ)^[l] x ∧ P i) →
      (Fs u v τ)^[L] x ∈ z := by
  intro L
  induction L with
  | zero => intro _; exact hxz
  | succ L ih =>
    intro hL
    have h1 := ih (fun l hl => hL l (by omega))
    obtain ⟨i, hi, hP⟩ := hL L (by omega)
    rw [Function.iterate_succ_apply', ← hi, Fs_tau hinj i]
    have hiC : τ i ∈ C := hi ▸ iter_mem hτ hinj hC hxC L
    exact hz i (u_mem_of_tau hτ hC hiC) hP (hi ▸ h1)

theorem B_constr (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {C : Finset (Fin n)} (hC : IsComp u v C)
    (hle : (E u v C).card ≤ C.card) (Hj cyc : Finset (Fin n))
    (hcyc : ∀ x ∈ cyc, Per u v τ x) (hB : Hj ∩ C ⊆ cyc ∧ Even (Hj ∩ C).card)
    (z : Finset (Fin n)) (hz : ∀ i, u i ∈ C → τ i ∈ z → hd u v τ i ∈ z) :
    Even (z ∩ Hj ∩ C).card := by
  by_cases hex : ∃ x ∈ C, Per u v τ x ∧ x ∈ z
  · obtain ⟨x, hxC, hxp, hxz⟩ := hex
    have hsub : Hj ∩ C ⊆ z := by
      intro y hy
      have hyp := hcyc y (hB.1 hy)
      obtain ⟨c, rfl⟩ := per_uniq huv hτ hinj hC hle hxp hyp hxC (mem_inter.1 hy).2
      refine walk hτ hinj hC z (fun _ => True) (fun i h1 _ h2 => hz i h1 h2) hxC hxz c ?_
      intro l _
      obtain ⟨⟨i, hi⟩, _⟩ := per_iter huv hτ hinj hxp l
      exact ⟨i, hi, trivial⟩
    have heq : z ∩ Hj ∩ C = Hj ∩ C := by
      ext y; simp only [mem_inter]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩
      · intro h; exact ⟨⟨hsub (mem_inter.2 h), h.1⟩, h.2⟩
    rw [heq]; exact hB.2
  · have heq : z ∩ Hj ∩ C = ∅ := by
      ext y; simp only [mem_inter, notMem_empty, iff_false]
      rintro ⟨⟨hyz, hyH⟩, hyC⟩
      exact hex ⟨y, hyC, hcyc y (hB.1 (mem_inter.2 ⟨hyH, hyC⟩)), hyz⟩
    rw [heq]; simp

theorem range_of_tight (hτ : ∀ i, τ i = u i ∨ τ i = v i) (hinj : Function.Injective τ)
    {C : Finset (Fin n)} (hC : IsComp u v C) (heq : (E u v C).card = C.card) :
    ∀ x ∈ C, ∃ i, τ i = x := by
  have hsub : (E u v C).image τ ⊆ C := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    rw [mem_E] at hi
    rcases hτ i with h | h <;> rw [h]
    · exact hi.1
    · exact hi.2
  have himg : (E u v C).image τ = C :=
    eq_of_subset_of_card_le hsub (by rw [card_image_of_injective _ hinj, heq])
  intro x hx
  rw [← himg] at hx
  obtain ⟨i, _, hi⟩ := mem_image.1 hx
  exact ⟨i, hi⟩

theorem ev_per (hτ : ∀ i, τ i = u i ∨ τ i = v i) (hinj : Function.Injective τ)
    {C : Finset (Fin n)} (hC : IsComp u v C) (hrange : ∀ x ∈ C, ∃ i, τ i = x)
    {x : Fin n} (hx : x ∈ C) : ∃ l, Per u v τ ((Fs u v τ)^[l] x) := by
  obtain ⟨a, b, hab, he0⟩ := Finite.exists_ne_map_eq_of_infinite (fun l : ℕ => (Fs u v τ)^[l] x)
  have he : (Fs u v τ)^[a] x = (Fs u v τ)^[b] x := he0
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, hrange _ (iter_mem hτ hinj hC hx a), b - a, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le, he]
  · refine ⟨b, hrange _ (iter_mem hτ hinj hC hx b), a - b, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le, he]

theorem A_constr (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {C : Finset (Fin n)} (hC : IsComp u v C)
    (heq : (E u v C).card = C.card) (Mk : Finset (Fin n)) (br : Finset (Fin m))
    (hbr : ∀ i ∈ br, ¬ PerP u v τ (τ i))
    (hA : ∀ a ∈ Mk ∩ C, ∀ b ∈ Mk ∩ C, ∀ U : Finset (Fin n), a ∈ U → b ∉ U →
      (br ∩ cutS u v U).Nonempty)
    (a0 : Fin n) (ha0 : a0 ∈ Mk ∩ C) :
    ∃ j, u j ∈ C ∧ ∀ z : Finset (Fin n), (∀ i, u i ∈ C → i ≠ j → τ i ∈ z → hd u v τ i ∈ z) →
      ¬ (u j ∈ z ∧ v j ∈ z) → ∀ x ∈ Mk ∩ C, x ∉ z := by
  classical
  have hrange := range_of_tight hτ hinj hC heq
  have ha0C : a0 ∈ C := (mem_inter.1 ha0).2
  have hex : ∃ l, Per u v τ ((Fs u v τ)^[l] a0) := ev_per hτ hinj hC hrange ha0C
  set c := (Fs u v τ)^[Nat.find hex] a0 with hcdef
  have hc : Per u v τ c := Nat.find_spec hex
  have hcC : c ∈ C := iter_mem hτ hinj hC ha0C _
  let U := C.filter (fun x => ∃ l, (Fs u v τ)^[l] x = c ∧ ∀ l' < l, ¬ Per u v τ ((Fs u v τ)^[l'] x))
  have ha0U : a0 ∈ U := mem_filter.2 ⟨ha0C, Nat.find hex, rfl, fun l' hl' => Nat.find_min hex hl'⟩
  have hstepU : ∀ x ∈ C, ¬ Per u v τ x → (x ∈ U ↔ Fs u v τ x ∈ U) := by
    intro x hxC hxp
    simp only [U, mem_filter]
    constructor
    · rintro ⟨_, l, hl, hl'⟩
      cases l with
      | zero =>
        exact (hxp (by rw [Function.iterate_zero_apply] at hl; rw [hl]; exact hc)).elim
      | succ l =>
        refine ⟨Fs_mem hτ hinj hC hxC, l, ?_, fun l'' hl'' => ?_⟩
        · rw [← Function.iterate_succ_apply]; exact hl
        · rw [← Function.iterate_succ_apply]; exact hl' (l'' + 1) (by omega)
    · rintro ⟨_, l, hl, hl'⟩
      refine ⟨hxC, l + 1, ?_, fun l'' hl'' => ?_⟩
      · rw [Function.iterate_succ_apply]; exact hl
      · cases l'' with
        | zero => exact hxp
        | succ l'' => rw [Function.iterate_succ_apply]; exact hl' l'' (by omega)
  have hcutU : br ∩ cutS u v U = ∅ := by
    ext i
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    intro hib hic
    rw [mem_cut, cross_iff hτ i] at hic
    have hτC : τ i ∈ C := by
      by_cases h : τ i ∈ U
      · exact (mem_filter.1 h).1
      · have h2 : hd u v τ i ∈ U := by
          by_contra h2; exact hic ⟨fun h' => absurd h' h, fun h' => absurd h' h2⟩
        have h3 := (mem_filter.1 h2).1
        rcases ends hτ i with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [← e1]; exact (hC.closed i).2 (e2 ▸ h3)
        · rw [← e2]; exact (hC.closed i).1 (e1 ▸ h3)
    have hnp : ¬ Per u v τ (τ i) := fun h => hbr i hib h.2
    apply hic
    rw [hstepU _ hτC hnp, Fs_tau hinj i]
  have hallU : ∀ x ∈ Mk ∩ C, x ∈ U := by
    intro x hx
    by_contra hxU
    obtain ⟨i, hi⟩ := hA a0 ha0 x hx U ha0U hxU
    rw [hcutU] at hi
    simp at hi
  have hcyc : ∃ l, (Fs u v τ)^[l + 1] c = c := by
    obtain ⟨k, hk, hkc⟩ := hc.2
    exact ⟨k - 1, by rw [Nat.sub_add_cancel hk]; exact hkc⟩
  set c' := (Fs u v τ)^[Nat.find hcyc] c with hc'def
  have hFc' : Fs u v τ c' = c := by
    rw [hc'def, ← Function.iterate_succ_apply' (f := Fs u v τ) (Nat.find hcyc) c]
    exact Nat.find_spec hcyc
  have hc'p : Per u v τ c' := per_iter huv hτ hinj hc _
  obtain ⟨j, hj⟩ := hc'p.1
  have hc'C : c' ∈ C := iter_mem hτ hinj hC hcC _
  refine ⟨j, u_mem_of_tau hτ hC (hj ▸ hc'C), ?_⟩
  intro z hz hnand x hx hxz
  obtain ⟨_, l, hl, hl'⟩ := mem_filter.1 (hallU x hx)
  have hxC : x ∈ C := (mem_inter.1 hx).2
  have hcz : c ∈ z := by
    rw [← hl]
    refine walk hτ hinj hC z (fun i => i ≠ j) hz hxC hxz l ?_
    intro l' hl''
    obtain ⟨i, hi⟩ := hrange _ (iter_mem hτ hinj hC hxC l')
    refine ⟨i, hi, ?_⟩
    intro hij
    apply hl' l' hl''
    rw [← hi, hij, hj]; exact hc'p
  have hc'z : c' ∈ z := by
    rw [hc'def]
    refine walk hτ hinj hC z (fun i => i ≠ j) hz hcC hcz _ ?_
    intro l' hl''
    obtain ⟨⟨i, hi⟩, _⟩ := per_iter huv hτ hinj hc l'
    refine ⟨i, hi, ?_⟩
    intro hij
    apply Nat.find_min hcyc hl''
    rw [Function.iterate_succ_apply', ← hi, hij, hj, hFc']
  apply hnand
  rw [both_iff hτ j, ← Fs_tau hinj j, hj, hFc']
  exact ⟨hc'z, hcz⟩

end Constr

theorem RHS_to_Q {u v : Fin m → Fin n} (huv : ∀ i, u i ≠ v i) {r : ℕ}
    (H : Fin r → Finset (Fin n)) (hpf : ∀ C, IsComp u v C → (E u v C).card ≤ C.card)
    (br : Finset (Fin m)) (hbr : ∀ i, i ∈ br ↔ ∃ U : Finset (Fin n), cutS u v U = {i})
    (cyc : Finset (Fin n)) (hcyc : ∀ x ∈ cyc, ∃ i, i ∉ br ∧ (x = u i ∨ x = v i))
    (Mk : Finset (Fin n)) (hMk : ∀ j, H j ⊆ Mk)
    (hR : ∀ C, IsComp u v C → (((E u v C).card = C.card ∧ ∀ a ∈ Mk ∩ C, ∀ b ∈ Mk ∩ C,
      ∀ U : Finset (Fin n), a ∈ U → b ∉ U → (br ∩ cutS u v U).Nonempty) ∨
      (∀ j, H j ∩ C ⊆ cyc ∧ Even (H j ∩ C).card))) :
    ∃ q : Fin m → Bool × Bool, (∀ i, q i ≠ (false, false)) ∧
      ∀ z, Sol u v q z → ∀ j, (z ∩ H j).card % 2 = 0 := by
  classical
  obtain ⟨τ, hinj, hτ⟩ := exists_orient hpf
  have hbrP : ∀ i ∈ br, ¬ PerP u v τ (τ i) := by
    intro i hi hp
    obtain ⟨U, hU⟩ := (hbr i).1 hi
    exact not_cut_single hτ hinj i hp U hU
  have hcycP : ∀ x ∈ cyc, Per u v τ x := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hcyc x hx
    have hp : PerP u v τ (τ i) := by
      by_contra hnp
      exact hi ((hbr i).2 ⟨_, cut_IT hτ hinj i hnp⟩)
    have h1 : Per u v τ (τ i) := ⟨⟨i, rfl⟩, hp⟩
    have h2 : Per u v τ (hd u v τ i) := perP_hd huv hτ hinj hp
    rcases ends hτ i with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hxi with rfl | rfl
    · rw [e1]; exact h1
    · rw [e2]; exact h2
    · rw [e1]; exact h2
    · rw [e2]; exact h1
  have hloc : ∀ C, ∃ jo : Option (Fin m), IsComp u v C →
      (∀ j, jo = some j → u j ∈ C) ∧
      ∀ z : Finset (Fin n), (∀ i, u i ∈ C → jo ≠ some i → τ i ∈ z → hd u v τ i ∈ z) →
        (∀ j, jo = some j → ¬ (u j ∈ z ∧ v j ∈ z)) → ∀ k, Even (z ∩ H k ∩ C).card := by
    intro C
    by_cases hC : IsComp u v C
    · rcases hR C hC with ⟨heq, hA⟩ | hB
      · by_cases hmk : ∃ a0, a0 ∈ Mk ∩ C
        · obtain ⟨a0, ha0⟩ := hmk
          obtain ⟨j, hjC, hj⟩ := A_constr huv hτ hinj hC heq Mk br hbrP hA a0 ha0
          refine ⟨some j, fun _ => ⟨fun j' hj' => (by rw [← Option.some_injective _ hj']; exact hjC),
            ?_⟩⟩
          intro z hz hn k
          have hz' : ∀ x ∈ Mk ∩ C, x ∉ z :=
            hj z (fun i hi hij => hz i hi (fun h => hij (Option.some_injective _ h).symm)) (hn j rfl)
          have h0 : z ∩ H k ∩ C = ∅ := by
            ext y; simp only [mem_inter, notMem_empty, iff_false]
            rintro ⟨⟨hyz, hyH⟩, hyC⟩
            exact hz' y (mem_inter.2 ⟨hMk k hyH, hyC⟩) hyz
          rw [h0]; simp
        · refine ⟨none, fun _ => ⟨fun j hj => (by cases hj), ?_⟩⟩
          intro z _ _ k
          have h0 : z ∩ H k ∩ C = ∅ := by
            ext y; simp only [mem_inter, notMem_empty, iff_false]
            rintro ⟨⟨_, hyH⟩, hyC⟩
            exact hmk ⟨y, mem_inter.2 ⟨hMk k hyH, hyC⟩⟩
          rw [h0]; simp
      · refine ⟨none, fun _ => ⟨fun j hj => (by cases hj), ?_⟩⟩
        intro z hz _ k
        exact B_constr huv hτ hinj hC (hpf C hC) (H k) cyc hcycP (hB k) z
          (fun i hi h => hz i hi (by simp) h)
    · exact ⟨none, fun h => absurd h hC⟩
  choose g hg using hloc
  let J : Finset (Fin m) := univ.filter (fun i => ∃ C, IsComp u v C ∧ g C = some i)
  let q : Fin m → Bool × Bool := fun i =>
    if i ∈ J then (true, true) else if τ i = u i then (true, false) else (false, true)
  refine ⟨q, ?_, ?_⟩
  · intro i
    simp only [q]
    split_ifs <;> simp
  · intro z hz k
    have hdec : ∀ i, (i ∈ J → ¬ (u i ∈ z ∧ v i ∈ z)) ∧ (i ∉ J → τ i ∈ z → hd u v τ i ∈ z) := by
      intro i
      have hzi := hz i
      simp only [q] at hzi
      by_cases hiJ : i ∈ J
      · rw [if_pos hiJ] at hzi
        exact ⟨fun _ h => hzi (by simp [h.1, h.2]), fun h => absurd hiJ h⟩
      · rw [if_neg hiJ] at hzi
        refine ⟨fun h => absurd h hiJ, fun _ ht => ?_⟩
        by_cases h2 : τ i = u i
        · rw [if_pos h2] at hzi
          have hh : hd u v τ i = v i := by unfold hd; rw [if_pos h2]
          rw [hh]; rw [h2] at ht
          by_contra hv; exact hzi (by simp [ht, hv])
        · rw [if_neg h2] at hzi
          have hh : hd u v τ i = u i := by unfold hd; rw [if_neg h2]
          have h3 : τ i = v i := (hτ i).resolve_left h2
          rw [hh]; rw [h3] at ht
          by_contra hu; exact hzi (by simp [ht, hu])
    have hcomp : ∀ C, IsComp u v C → Even (z ∩ H k ∩ C).card := by
      intro C hC
      obtain ⟨_, hgC2⟩ := hg C hC
      refine hgC2 z ?_ ?_ k
      · intro i hi hne ht
        refine (hdec i).2 ?_ ht
        intro hiJ
        obtain ⟨C', hC', hgC'⟩ := (mem_filter.1 hiJ).2
        have hiC' : u i ∈ C' := (hg C' hC').1 i hgC'
        have hCC := comp_eq hC hC' hi hiC'
        subst hCC
        exact hne hgC'
      · intro j hj
        exact (hdec j).1 (mem_filter.2 ⟨mem_univ _, C, hC, hj⟩)
    let CS := (univ : Finset (Finset (Fin n))).filter (fun C => IsComp u v C)
    have hcover : z ∩ H k = CS.biUnion (fun C => z ∩ H k ∩ C) := by
      ext y
      simp only [mem_biUnion, mem_inter, mem_filter, mem_univ, true_and, CS]
      constructor
      · intro hy
        obtain ⟨C, hC, hyC⟩ := exists_comp u v y
        exact ⟨C, hC, hy, hyC⟩
      · rintro ⟨C, _, hy, _⟩; exact hy
    have hdisj : (CS : Set (Finset (Fin n))).PairwiseDisjoint (fun C => z ∩ H k ∩ C) := by
      intro C hC D hD hCD
      simp only [Function.onFun]
      rw [disjoint_left]
      intro y hy1 hy2
      have hC' : IsComp u v C := (mem_filter.1 (mem_coe.1 hC)).2
      have hD' : IsComp u v D := (mem_filter.1 (mem_coe.1 hD)).2
      exact hCD (comp_eq hC' hD' (mem_inter.1 hy1).2 (mem_inter.1 hy2).2)
    rw [hcover, card_biUnion hdisj]
    apply Nat.even_iff.1
    apply Finset.sum_induction _ Even (fun a b ha hb => ha.add hb) ⟨0, rfl⟩
    intro C hC
    exact hcomp C (mem_filter.1 hC).2

/-! ## Probes: closures and strong components -/

section Probe

variable {u v : Fin m → Fin n} {q : Fin m → Bool × Bool}

abbrev nd (q : Fin m → Bool × Bool) (i : Fin m) : Prop := q i = (true, true)

def tl (u v : Fin m → Fin n) (q : Fin m → Bool × Bool) (i : Fin m) : Fin n :=
  if q i = (false, true) then v i else u i

def hq (u v : Fin m → Fin n) (q : Fin m → Bool × Bool) (i : Fin m) : Fin n :=
  if q i = (false, true) then u i else v i

theorem ends_q (i : Fin m) :
    (u i = tl u v q i ∧ v i = hq u v q i) ∨ (u i = hq u v q i ∧ v i = tl u v q i) := by
  unfold tl hq
  by_cases h : q i = (false, true)
  · right; simp [h]
  · left; simp [h]

theorem cross_q (i : Fin m) (W : Finset (Fin n)) :
    (u i ∈ W ↔ v i ∈ W) ↔ (tl u v q i ∈ W ↔ hq u v q i ∈ W) := by
  rcases ends_q (u := u) (v := v) (q := q) i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact iff_comm

theorem both_q (i : Fin m) (W : Finset (Fin n)) :
    (u i ∈ W ∧ v i ∈ W) ↔ (tl u v q i ∈ W ∧ hq u v q i ∈ W) := by
  rcases ends_q (u := u) (v := v) (q := q) i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact and_comm

def Closed (u v : Fin m → Fin n) (q : Fin m → Bool × Bool) (Z : Finset (Fin n)) : Prop :=
  ∀ i, ¬ nd q i → tl u v q i ∈ Z → hq u v q i ∈ Z

open Classical in
noncomputable def Clo (u v : Fin m → Fin n) (q : Fin m → Bool × Bool) (w : Fin n) :
    Finset (Fin n) :=
  univ.filter (fun x => ∀ Z : Finset (Fin n), Closed u v q Z → w ∈ Z → x ∈ Z)

theorem mem_Clo {w x : Fin n} :
    x ∈ Clo u v q w ↔ ∀ Z : Finset (Fin n), Closed u v q Z → w ∈ Z → x ∈ Z := by
  simp [Clo]

theorem self_mem_Clo (w : Fin n) : w ∈ Clo u v q w := mem_Clo.2 (fun _ _ h => h)

theorem Clo_closed (w : Fin n) : Closed u v q (Clo u v q w) := by
  intro i hi ht
  rw [mem_Clo] at ht ⊢
  intro Z hZ hw
  exact hZ i hi (ht Z hZ hw)

theorem Clo_min {w : Fin n} {Z : Finset (Fin n)} (hZ : Closed u v q Z) (hw : w ∈ Z) :
    Clo u v q w ⊆ Z :=
  fun _ hx => mem_Clo.1 hx Z hZ hw

theorem Clo_trans {w x : Fin n} (hx : x ∈ Clo u v q w) : Clo u v q x ⊆ Clo u v q w :=
  Clo_min (Clo_closed w) hx

theorem hq_mem_Clo {i : Fin m} (hi : ¬ nd q i) : hq u v q i ∈ Clo u v q (tl u v q i) :=
  Clo_closed _ i hi (self_mem_Clo _)

theorem sol_of_closed (hqv : ∀ i, q i ≠ (false, false)) {Z : Finset (Fin n)}
    (hZ : Closed u v q Z) (hnf : ∀ i, nd q i → ¬ (u i ∈ Z ∧ v i ∈ Z)) : Sol u v q Z := by
  intro i heq
  have h1 : ¬ nd q i → tl u v q i ∈ Z → hq u v q i ∈ Z := hZ i
  have h2 := hnf i
  have h3 := hqv i
  simp only [nd, tl, hq] at h1 h2
  rcases hqi : q i with ⟨a, b⟩
  rw [hqi] at heq h1 h2 h3
  cases a <;> cases b <;> by_cases hu : u i ∈ Z <;> by_cases hv : v i ∈ Z <;> simp_all

def Live (u v : Fin m → Fin n) (q : Fin m → Bool × Bool) (w : Fin n) : Prop :=
  ∀ i, nd q i → ¬ (u i ∈ Clo u v q w ∧ v i ∈ Clo u v q w)

open Classical in
noncomputable def SC (u v : Fin m → Fin n) (q : Fin m → Bool × Bool) (w : Fin n) :
    Finset (Fin n) :=
  (Clo u v q w).filter (fun x => w ∈ Clo u v q x)

theorem mem_SC {w x : Fin n} : x ∈ SC u v q w ↔ x ∈ Clo u v q w ∧ w ∈ Clo u v q x := by
  simp [SC]

theorem self_mem_SC (w : Fin n) : w ∈ SC u v q w := mem_SC.2 ⟨self_mem_Clo w, self_mem_Clo w⟩

theorem out_edge {w x : Fin n} (hx : x ∈ Clo u v q w) (hxw : x ≠ w) :
    ∃ i, ¬ nd q i ∧ tl u v q i = w ∧ x ∈ Clo u v q (hq u v q i) := by
  classical
  let Z := insert w (univ.filter
    (fun y => ∃ i, ¬ nd q i ∧ tl u v q i = w ∧ y ∈ Clo u v q (hq u v q i)))
  have hZ : Closed u v q Z := by
    intro i hi ht
    simp only [Z, mem_insert, mem_filter, mem_univ, true_and] at ht ⊢
    right
    rcases ht with ht | ⟨i', hi', ht', hmem⟩
    · exact ⟨i, hi, ht, self_mem_Clo _⟩
    · exact ⟨i', hi', ht', Clo_closed _ i hi hmem⟩
  have h1 := Clo_min hZ (mem_insert_self w _) hx
  simp only [Z, mem_insert, mem_filter, mem_univ, true_and] at h1
  rcases h1 with h | h
  · exact absurd h hxw
  · exact h

theorem in_edge {w x : Fin n} (hx : x ∈ Clo u v q w) (hxw : x ≠ w) :
    ∃ i, ¬ nd q i ∧ hq u v q i = x ∧ tl u v q i ∈ Clo u v q w := by
  by_contra hno
  push Not at hno
  have hZ : Closed u v q ((Clo u v q w).erase x) := by
    intro i hi ht
    rw [mem_erase] at ht ⊢
    exact ⟨fun h => hno i hi h ht.2, Clo_closed w i hi ht.2⟩
  have h1 := Clo_min hZ (mem_erase.2 ⟨hxw.symm, self_mem_Clo w⟩) hx
  simp at h1

theorem live_even {r : ℕ} {H : Fin r → Finset (Fin n)} (hqv : ∀ i, q i ≠ (false, false))
    (hev : ∀ z, Sol u v q z → ∀ j, (z ∩ H j).card % 2 = 0) {w : Fin n} (hw : Live u v q w)
    (j : Fin r) : (SC u v q w ∩ H j).card % 2 = 0 := by
  have h1 := hev _ (sol_of_closed hqv (Clo_closed w) hw) j
  have hcl : Closed u v q (Clo u v q w \ SC u v q w) := by
    intro i hi ht
    rw [mem_sdiff] at ht ⊢
    refine ⟨Clo_closed w i hi ht.1, fun hs => ht.2 ?_⟩
    rw [mem_SC] at hs ⊢
    exact ⟨ht.1, Clo_trans (hq_mem_Clo hi) hs.2⟩
  have hnf : ∀ i, nd q i →
      ¬ (u i ∈ Clo u v q w \ SC u v q w ∧ v i ∈ Clo u v q w \ SC u v q w) := by
    intro i hi h
    exact hw i hi ⟨(mem_sdiff.1 h.1).1, (mem_sdiff.1 h.2).1⟩
  have h2 := hev _ (sol_of_closed hqv hcl hnf) j
  have hsub : SC u v q w ⊆ Clo u v q w := fun y hy => (mem_SC.1 hy).1
  have h3 : Clo u v q w ∩ H j = (SC u v q w ∩ H j) ∪ ((Clo u v q w \ SC u v q w) ∩ H j) := by
    ext y; simp only [mem_inter, mem_union, mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : y ∈ SC u v q w
      · left; exact ⟨h, h2⟩
      · right; exact ⟨⟨h1, h⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, _⟩, h2⟩)
      · exact ⟨hsub h1, h2⟩
      · exact ⟨h1, h2⟩
  have h4 : Disjoint (SC u v q w ∩ H j) ((Clo u v q w \ SC u v q w) ∩ H j) := by
    rw [disjoint_left]; intro y hy1 hy2
    exact (mem_sdiff.1 (mem_inter.1 hy2).1).2 (mem_inter.1 hy1).1
  rw [h3, card_union_of_disjoint h4] at h1
  omega

theorem side_closed {U : Finset (Fin n)} {i : Fin m}
    (hU : ∀ i', i' ≠ i → (u i' ∈ U ↔ v i' ∈ U)) (ht : tl u v q i ∉ U) : Closed u v q U := by
  intro i' _ ht'
  have hne : i' ≠ i := fun h => ht (h ▸ ht')
  exact ((cross_q i' U).1 (hU i' hne)).1 ht'

theorem nb_of_sc {w x : Fin n} (hx : x ∈ Clo u v q w) (hw : w ∈ Clo u v q x) (hxw : x ≠ w) :
    ∃ i, (¬ ∃ U : Finset (Fin n), cutS u v U = {i}) ∧ (u i = w ∨ v i = w) := by
  obtain ⟨i, hi, hti, hxi⟩ := out_edge hx hxw
  have hwi : w ∈ Clo u v q (hq u v q i) := Clo_trans hxi hw
  refine ⟨i, ?_, ?_⟩
  · rintro ⟨U, hU⟩
    have hother : ∀ i', i' ≠ i → (u i' ∈ U ↔ v i' ∈ U) := by
      intro i' hne
      have h1 : i' ∉ cutS u v U := by rw [hU, mem_singleton]; exact hne
      rw [mem_cut, not_not] at h1; exact h1
    have hcr : ¬ (tl u v q i ∈ U ↔ hq u v q i ∈ U) := by
      have h1 : i ∈ cutS u v U := by rw [hU]; exact mem_singleton_self i
      rw [mem_cut, cross_q i U] at h1; exact h1
    by_cases hh : hq u v q i ∈ U
    · have htU : tl u v q i ∉ U := fun h => hcr ⟨fun _ => hh, fun _ => h⟩
      have h1 := Clo_min (side_closed hother htU) hh hwi
      exact htU (by rw [hti]; exact h1)
    · have htU : tl u v q i ∈ U := by
        by_contra h; exact hcr ⟨fun h' => absurd h' h, fun h' => absurd h' hh⟩
      have hother' : ∀ i', i' ≠ i → (u i' ∈ univ \ U ↔ v i' ∈ univ \ U) := by
        intro i' hne; simp only [mem_sdiff, mem_univ, true_and]; exact not_congr (hother i' hne)
      have htU' : tl u v q i ∉ univ \ U := by simp [htU]
      have h1 := Clo_min (side_closed hother' htU') (by simp [hh]) hwi
      exact htU' (by rw [hti]; exact h1)
  · rcases ends_q (u := u) (v := v) (q := q) i with ⟨h1, _⟩ | ⟨_, h2⟩
    · left; rw [h1, hti]
    · right; rw [h2, hti]

theorem clo_sub {C : Finset (Fin n)} (hC : IsComp u v C) {w : Fin n} (hw : w ∈ C) :
    Clo u v q w ⊆ C := by
  refine Clo_min ?_ hw
  intro i _ ht
  exact ((cross_q i C).1 (hC.closed i)).1 ht

theorem dense_sc {w x : Fin n} (hx : x ∈ SC u v q w) (hxw : x ≠ w) :
    (SC u v q w).card ≤ (E u v (SC u v q w)).card := by
  classical
  have hsub : SC u v q w ⊆
      ((E u v (SC u v q w)).filter (fun i => ¬ nd q i)).image (tl u v q) := by
    intro y hy
    obtain ⟨x', hx'y, hx'ne, hwx'⟩ : ∃ x', x' ∈ Clo u v q y ∧ x' ≠ y ∧ w ∈ Clo u v q x' := by
      by_cases hyw : y = w
      · rw [hyw]; exact ⟨x, (mem_SC.1 hx).1, hxw, (mem_SC.1 hx).2⟩
      · exact ⟨w, (mem_SC.1 hy).2, fun h => hyw h.symm, self_mem_Clo w⟩
    obtain ⟨i, hi, hti, hxi⟩ := out_edge hx'y hx'ne
    rw [mem_image]
    refine ⟨i, mem_filter.2 ⟨?_, hi⟩, hti⟩
    rw [mem_E, both_q i]
    refine ⟨by rw [hti]; exact hy, mem_SC.2 ⟨?_, ?_⟩⟩
    · exact Clo_trans (mem_SC.1 hy).1 (by rw [← hti]; exact hq_mem_Clo hi)
    · exact Clo_trans hxi hwx'
  exact (card_le_card hsub).trans (card_image_le.trans (card_le_card (filter_subset _ _)))

theorem dead_count {w : Fin n} (hd : ¬ Live u v q w) :
    ∃ k, k ∈ E u v (Clo u v q w) ∧ nd q k := by
  unfold Live at hd
  push Not at hd
  obtain ⟨k, hk, h1, h2⟩ := hd
  exact ⟨k, mem_E.2 ⟨h1, h2⟩, hk⟩

theorem dense_dead {w : Fin n} (hd : ¬ Live u v q w) :
    (Clo u v q w).card ≤ (E u v (Clo u v q w)).card := by
  classical
  set X := Clo u v q w with hX
  set In := (E u v X).filter (fun i => ¬ nd q i) with hIn
  have hcov : X.erase w ⊆ In.image (hq u v q) := by
    intro x hx
    obtain ⟨hxw, hxX⟩ := mem_erase.1 hx
    obtain ⟨i, hi, hqi, hti⟩ := in_edge hxX hxw
    rw [mem_image]
    refine ⟨i, mem_filter.2 ⟨?_, hi⟩, hqi⟩
    rw [mem_E, both_q i]; exact ⟨hti, by rw [hqi]; exact hxX⟩
  obtain ⟨k, hkE, hkn⟩ := dead_count hd
  have hkIn : k ∉ In := fun h => (mem_filter.1 h).2 hkn
  have h0 : insert k In ⊆ E u v X := insert_subset hkE (filter_subset _ _)
  have h1 := card_le_card h0
  rw [card_insert_of_notMem hkIn] at h1
  have h2 := (card_le_card hcov).trans card_image_le
  have h3 : (X.erase w).card + 1 = X.card := card_erase_add_one (self_mem_Clo w)
  omega

theorem tight {C : Finset (Fin n)} (hC : IsComp u v C) (hle : (E u v C).card ≤ C.card)
    {w : Fin n} (hwC : w ∈ C) (hd : ¬ Live u v q w) :
    (∀ i, ¬ nd q i → tl u v q i ∈ Clo u v q w → hq u v q i ≠ w) ∧
    (∀ i1 i2, ¬ nd q i1 → ¬ nd q i2 → tl u v q i1 ∈ Clo u v q w → tl u v q i2 ∈ Clo u v q w →
      hq u v q i1 = hq u v q i2 → i1 = i2) := by
  classical
  set X := Clo u v q w with hX
  have hXC : X ⊆ C := clo_sub hC hwC
  set In := (E u v X).filter (fun i => ¬ nd q i) with hIn
  have hcov : X.erase w ⊆ In.image (hq u v q) := by
    intro x hx
    obtain ⟨hxw, hxX⟩ := mem_erase.1 hx
    obtain ⟨i, hi, hqi, hti⟩ := in_edge hxX hxw
    rw [mem_image]
    refine ⟨i, mem_filter.2 ⟨?_, hi⟩, hqi⟩
    rw [mem_E, both_q i]; exact ⟨hti, by rw [hqi]; exact hxX⟩
  obtain ⟨k, hkE, hkn⟩ := dead_count hd
  have hkIn : k ∉ In := fun h => (mem_filter.1 h).2 hkn
  have hE : In.card + 1 ≤ (E u v X).card := by
    have h0 : insert k In ⊆ E u v X := insert_subset hkE (filter_subset _ _)
    have h1 := card_le_card h0
    rwa [card_insert_of_notMem hkIn] at h1
  have hXw : (X.erase w).card + 1 = X.card := card_erase_add_one (self_mem_Clo w)
  have hmem : ∀ i, ¬ nd q i → tl u v q i ∈ X → i ∈ In := by
    intro i hi hti
    refine mem_filter.2 ⟨?_, hi⟩
    rw [mem_E, both_q i]; exact ⟨hti, Clo_closed w i hi hti⟩
  constructor
  · intro i hi hti hqi
    have hiIn : i ∈ In := hmem i hi hti
    have hcov' : X ⊆ In.image (hq u v q) := by
      intro x hx
      by_cases hxw : x = w
      · rw [mem_image]; exact ⟨i, hiIn, hqi.trans hxw.symm⟩
      · exact hcov (mem_erase.2 ⟨hxw, hx⟩)
    have h1 := (card_le_card hcov').trans card_image_le
    exact superdense hC hle hXC (by omega)
  · intro i1 i2 hi1 hi2 ht1 ht2 hq12
    by_contra hne
    have hsub : In.image (hq u v q) ⊆ (In.erase i2).image (hq u v q) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      by_cases h : i = i2
      · rw [h, mem_image]; exact ⟨i1, mem_erase.2 ⟨hne, hmem i1 hi1 ht1⟩, hq12⟩
      · rw [mem_image]; exact ⟨i, mem_erase.2 ⟨h, hi⟩, rfl⟩
    have h1 := (card_le_card (hcov.trans hsub)).trans card_image_le
    have h2 : (In.erase i2).card + 1 = In.card := card_erase_add_one (hmem i2 hi2 ht2)
    exact superdense hC hle hXC (by omega)

theorem sc_in {w s : Fin n} (hs : s ∈ SC u v q w) (hnt : ∃ y ∈ SC u v q w, y ≠ w) :
    ∃ i, ¬ nd q i ∧ hq u v q i = s ∧ tl u v q i ∈ SC u v q w := by
  obtain ⟨s', hs', hs's⟩ : ∃ s' ∈ SC u v q w, s' ≠ s := by
    obtain ⟨y, hy, hyw⟩ := hnt
    by_cases h : y = s
    · exact ⟨w, self_mem_SC w, fun h' => hyw (h.trans h'.symm)⟩
    · exact ⟨y, hy, h⟩
  have hss' : s ∈ Clo u v q s' := Clo_trans (mem_SC.1 hs').2 (mem_SC.1 hs).1
  obtain ⟨i, hi, hqi, hti⟩ := in_edge hss' (fun h => hs's h.symm)
  refine ⟨i, hi, hqi, mem_SC.2 ⟨Clo_trans (mem_SC.1 hs').1 hti, ?_⟩⟩
  have h1 : s ∈ Clo u v q (tl u v q i) := by rw [← hqi]; exact hq_mem_Clo hi
  exact Clo_trans h1 (mem_SC.1 hs).2

theorem CR {a x : Fin n} {W : Finset (Fin n)} (haW : a ∈ W) (hx : x ∈ Clo u v q a)
    (hxW : x ∉ W) :
    ∃ i, ¬ nd q i ∧ tl u v q i ∈ Clo u v q a ∧ tl u v q i ∈ W ∧ hq u v q i ∉ W := by
  by_contra hno
  push Not at hno
  have hZ : Closed u v q (Clo u v q a ∩ W) := by
    intro i hi ht
    rw [mem_inter] at ht ⊢
    exact ⟨Clo_closed a i hi ht.1, hno i hi ht.1 ht.2⟩
  have h1 := Clo_min hZ (mem_inter.2 ⟨self_mem_Clo a, haW⟩) hx
  exact hxW (mem_inter.1 h1).2

end Probe

/-! ## Forced forks -/

section Fork

variable {u v : Fin m → Fin n} {q : Fin m → Bool × Bool} {τ : Fin m → Fin n}

theorem tl_cases (hτ : ∀ i, τ i = u i ∨ τ i = v i) (i : Fin m) :
    (tl u v q i = τ i ∧ hq u v q i = hd u v τ i) ∨
      (tl u v q i = hd u v τ i ∧ hq u v q i = τ i) := by
  rcases ends_q (u := u) (v := v) (q := q) i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases ends hτ i with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · left; exact ⟨h1.symm.trans h3, h2.symm.trans h4⟩
  · right; exact ⟨h1.symm.trans h3, h2.symm.trans h4⟩
  · right; exact ⟨h2.symm.trans h4, h1.symm.trans h3⟩
  · left; exact ⟨h2.symm.trans h4, h1.symm.trans h3⟩

theorem E_mono {X Y : Finset (Fin n)} (h : X ⊆ Y) : E u v X ⊆ E u v Y := by
  intro i hi; rw [mem_E] at hi ⊢; exact ⟨h hi.1, h hi.2⟩

theorem orb_Fs {o w : Fin n} (hw : w ∈ Orb u v τ o) : Fs u v τ w ∈ Orb u v τ o := by
  obtain ⟨l, rfl⟩ := mem_Orb.1 hw
  exact mem_Orb.2 ⟨l + 1, Function.iterate_succ_apply' (f := Fs u v τ) l o⟩

theorem orb_iter {o w : Fin n} (hw : w ∈ Orb u v τ o) (c : ℕ) :
    (Fs u v τ)^[c] w ∈ Orb u v τ o := by
  obtain ⟨l, rfl⟩ := mem_Orb.1 hw
  exact mem_Orb.2 ⟨c + l, Function.iterate_add_apply (f := Fs u v τ) c l o⟩

theorem K1 (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {C : Finset (Fin n)} (hC : IsComp u v C)
    (hle : (E u v C).card ≤ C.card) {a o : Fin n} (haC : a ∈ C) (hdA : ¬ Live u v q a)
    (hoC : o ∈ C) (ho : Per u v τ o) : o ∈ Clo u v q a := by
  classical
  have hXC : Clo u v q a ⊆ C := clo_sub hC haC
  have hOC : Orb u v τ o ⊆ C := orb_sub hτ hinj hC hoC
  by_cases hdisj : Disjoint (Clo u v q a) (Orb u v τ o)
  · exact (DD hC hle hXC hOC ⟨a, self_mem_Clo a⟩ ⟨o, self_mem_Orb o⟩ hdisj (dense_dead hdA)
      (dense_orb huv hτ hinj ho)).elim
  by_contra hoX
  rw [not_disjoint_iff] at hdisj
  obtain ⟨o', ho'X, ho'O⟩ := hdisj
  have ho'p : Per u v τ o' := by
    obtain ⟨a1, rfl⟩ := mem_Orb.1 ho'O; exact per_iter huv hτ hinj ho a1
  obtain ⟨c, hc⟩ := per_uniq huv hτ hinj hC hle ho'p ho (hOC ho'O) hoC
  have hex : ∃ c, (Fs u v τ)^[c] o' ∉ Clo u v q a := ⟨c, by rw [hc]; exact hoX⟩
  have hc0 : (Fs u v τ)^[Nat.find hex] o' ∉ Clo u v q a := Nat.find_spec hex
  obtain ⟨c1, hc1⟩ : ∃ c1, Nat.find hex = c1 + 1 := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h] at hc0; exact absurd ho'X hc0
    · exact ⟨Nat.find hex - 1, by omega⟩
  have hpX : (Fs u v τ)^[c1] o' ∈ Clo u v q a := by
    by_contra h; exact Nat.find_min hex (by omega : c1 < Nat.find hex) h
  have hFp : Fs u v τ ((Fs u v τ)^[c1] o') ∉ Clo u v q a := by
    rw [← Function.iterate_succ_apply' (f := Fs u v τ) c1 o']
    have : c1.succ = Nat.find hex := by rw [hc1]
    rw [this]; exact hc0
  have hpO : (Fs u v τ)^[c1] o' ∈ Orb u v τ o := orb_iter ho'O c1
  obtain ⟨⟨i0, hi0⟩, _⟩ := per_iter huv hτ hinj ho'p c1
  have hYT : Orb u v τ o \ Clo u v q a ⊆
      ((univ : Finset (Fin m)).filter (fun i => τ i ∈ Orb u v τ o \ Clo u v q a)).image τ := by
    intro y hy
    have hyO := (mem_sdiff.1 hy).1
    obtain ⟨l, rfl⟩ := mem_Orb.1 hyO
    obtain ⟨⟨i, hi⟩, _⟩ := per_iter huv hτ hinj ho l
    rw [mem_image]; exact ⟨i, mem_filter.2 ⟨mem_univ _, by rw [hi]; exact hy⟩, hi⟩
  have hTE : (univ : Finset (Fin m)).filter (fun i => τ i ∈ Orb u v τ o \ Clo u v q a) ⊆
      E u v (Clo u v q a ∪ Orb u v τ o) := by
    intro i hi
    have hiY := (mem_filter.1 hi).2
    rw [mem_E, both_iff hτ i, mem_union, mem_union]
    refine ⟨Or.inr (mem_sdiff.1 hiY).1, Or.inr ?_⟩
    rw [← Fs_tau hinj i]; exact orb_Fs (mem_sdiff.1 hiY).1
  have hi0E : i0 ∈ E u v (Clo u v q a ∪ Orb u v τ o) := by
    rw [mem_E, both_iff hτ i0, mem_union, mem_union, ← Fs_tau hinj i0, hi0]
    exact ⟨Or.inl hpX, Or.inr (orb_Fs hpO)⟩
  have hsub : insert i0 (E u v (Clo u v q a) ∪
      (univ : Finset (Fin m)).filter (fun i => τ i ∈ Orb u v τ o \ Clo u v q a)) ⊆
      E u v (Clo u v q a ∪ Orb u v τ o) :=
    insert_subset hi0E (union_subset (E_mono subset_union_left) hTE)
  have hdisj : Disjoint (E u v (Clo u v q a))
      ((univ : Finset (Fin m)).filter (fun i => τ i ∈ Orb u v τ o \ Clo u v q a)) := by
    rw [disjoint_left]; intro i hiE hiT
    have h1 := (mem_sdiff.1 (mem_filter.1 hiT).2).2
    rw [mem_E, both_iff hτ i] at hiE
    exact h1 hiE.1
  have hi0n : i0 ∉ E u v (Clo u v q a) ∪
      (univ : Finset (Fin m)).filter (fun i => τ i ∈ Orb u v τ o \ Clo u v q a) := by
    rw [mem_union]; rintro (h | h)
    · rw [mem_E, both_iff hτ i0, ← Fs_tau hinj i0, hi0] at h; exact hFp h.2
    · have h1 := (mem_sdiff.1 (mem_filter.1 h).2).2; rw [hi0] at h1; exact h1 hpX
  have h1 := card_le_card hsub
  rw [card_insert_of_notMem hi0n, card_union_of_disjoint hdisj] at h1
  have h2 := (card_le_card hYT).trans card_image_le
  have h3 := dense_dead (u := u) (v := v) (q := q) hdA
  have h4 : (Clo u v q a ∪ Orb u v τ o).card =
      (Clo u v q a).card + (Orb u v τ o \ Clo u v q a).card := by
    rw [← union_sdiff_self_eq_union, card_union_of_disjoint disjoint_sdiff]
  exact superdense hC hle (union_subset hXC hOC) (by omega)

theorem K2 (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {C : Finset (Fin n)} (hC : IsComp u v C)
    (hle : (E u v C).card ≤ C.card) (hrange : ∀ x ∈ C, ∃ i, τ i = x) {a : Fin n}
    (haC : a ∈ C) (hdA : ¬ Live u v q a) {la : ℕ}
    (hla : Per u v τ ((Fs u v τ)^[la] a)) (hla' : ∀ l < la, ¬ Per u v τ ((Fs u v τ)^[l] a))
    (hpos : 0 < la) :
    ∃ i, ¬ nd q i ∧ hq u v q i = (Fs u v τ)^[la] a ∧ tl u v q i ∈ Clo u v q a ∧
      ¬ Per u v τ (tl u v q i) := by
  obtain ⟨l1, rfl⟩ : ∃ l1, la = l1 + 1 := ⟨la - 1, by omega⟩
  have hx'np : ¬ Per u v τ ((Fs u v τ)^[l1] a) := hla' l1 (by omega)
  obtain ⟨i0, hi0⟩ := hrange _ (iter_mem hτ hinj hC haC l1)
  have hnpp : ¬ PerP u v τ (τ i0) := fun h => hx'np (by rw [← hi0]; exact ⟨⟨i0, rfl⟩, h⟩)
  have hcut := cut_IT hτ hinj i0 hnpp
  have haW : a ∈ IT u v τ (τ i0) := mem_IT.2 ⟨l1, hi0.symm⟩
  have hoa : (Fs u v τ)^[l1 + 1] a = hd u v τ i0 := by
    rw [Function.iterate_succ_apply', ← hi0, Fs_tau hinj i0]
  have hoaW : (Fs u v τ)^[l1 + 1] a ∉ IT u v τ (τ i0) := by
    intro h
    obtain ⟨k, hk⟩ := mem_IT.1 h
    apply hx'np
    rw [← hi0, ← hk]
    exact per_iter huv hτ hinj hla k
  have hoaX := K1 (q := q) huv hτ hinj hC hle haC hdA (iter_mem hτ hinj hC haC (l1 + 1)) hla
  obtain ⟨i, hi, hti, htW, hqW⟩ := CR haW hoaX hoaW
  have hicut : i ∈ cutS u v (IT u v τ (τ i0)) := by
    rw [mem_cut, cross_q (q := q) i _]; intro h; exact hqW (h.1 htW)
  rw [hcut, mem_singleton] at hicut
  subst hicut
  rcases tl_cases (q := q) hτ i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨i, hi, by rw [h2, hoa], hti, ?_⟩
    rw [h1, hi0]; exact hx'np
  · exfalso
    rw [h1, ← hoa] at htW
    exact hoaW htW

theorem K3 (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {a : Fin n} {la : ℕ}
    (hla : Per u v τ ((Fs u v τ)^[la] a)) (hla' : ∀ l < la, ¬ Per u v τ ((Fs u v τ)^[l] a))
    {o : Fin n} (ho : Per u v τ o) (hne : o ≠ (Fs u v τ)^[la] a) {i : Fin m}
    (hqi : hq u v q i = o) (hti : tl u v q i ∈ Clo u v q a) : Per u v τ (tl u v q i) := by
  by_contra hnp
  rcases tl_cases (q := q) hτ i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hnpp : ¬ PerP u v τ (τ i) := fun h => hnp (by rw [h1]; exact ⟨⟨i, rfl⟩, h⟩)
    have hcut := cut_IT hτ hinj i hnpp
    have hτW : τ i ∈ IT u v τ (τ i) := mem_IT.2 ⟨0, rfl⟩
    have haW : a ∈ IT u v τ (τ i) := by
      by_contra haW
      have hZ : Closed u v q (Clo u v q a \ IT u v τ (τ i)) := by
        intro i' hi' ht'
        rw [mem_sdiff] at ht' ⊢
        refine ⟨Clo_closed a i' hi' ht'.1, fun hqW => ?_⟩
        have hc : i' ∈ cutS u v (IT u v τ (τ i)) := by
          rw [mem_cut, cross_q (q := q) i' _]; intro h; exact ht'.2 (h.2 hqW)
        rw [hcut, mem_singleton] at hc
        rw [hc, h1] at ht'
        exact ht'.2 hτW
      have h3 := Clo_min hZ (mem_sdiff.2 ⟨self_mem_Clo a, haW⟩) hti
      rw [h1] at h3
      exact (mem_sdiff.1 h3).2 hτW
    obtain ⟨l, hl⟩ := mem_IT.1 haW
    have hFl : (Fs u v τ)^[l + 1] a = o := by
      rw [Function.iterate_succ_apply', hl, Fs_tau hinj i, ← h2, hqi]
    have hle1 : ¬ (l + 1 < la) := fun h => hla' (l + 1) h (by rw [hFl]; exact ho)
    have hle2 : ¬ (la ≤ l) := by
      intro h
      apply hnpp
      have h3 := per_iter huv hτ hinj hla (l - la)
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel h, hl] at h3
      exact h3.2
    have h4 : la = l + 1 := by omega
    apply hne; rw [h4, hFl]
  · apply hnp
    rw [h1, ← Fs_tau hinj i, ← h2, hqi]
    exact per_Fs huv hτ hinj ho

theorem fork_eq (huv : ∀ i, u i ≠ v i) (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {C : Finset (Fin n)} (hC : IsComp u v C)
    (hle : (E u v C).card ≤ C.card) (hrange : ∀ x ∈ C, ∃ i, τ i = x) {a b : Fin n}
    (haC : a ∈ C) (hbC : b ∈ C) (hda : ¬ Live u v q a) (hdb : ¬ Live u v q b) {la lb : ℕ}
    (hla : Per u v τ ((Fs u v τ)^[la] a)) (hla' : ∀ l < la, ¬ Per u v τ ((Fs u v τ)^[l] a))
    (hlb : Per u v τ ((Fs u v τ)^[lb] b)) (hlb' : ∀ l < lb, ¬ Per u v τ ((Fs u v τ)^[l] b)) :
    (Fs u v τ)^[la] a = (Fs u v τ)^[lb] b := by
  by_contra hne
  have hobC : (Fs u v τ)^[lb] b ∈ C := iter_mem hτ hinj hC hbC lb
  have hobX : (Fs u v τ)^[lb] b ∈ Clo u v q a := K1 huv hτ hinj hC hle haC hda hobC hlb
  have hoba : (Fs u v τ)^[lb] b ≠ a := by
    intro h
    apply hne
    have hap : Per u v τ a := by rw [← h]; exact hlb
    have h0 : la = 0 := by
      by_contra h0
      exact hla' 0 (Nat.pos_of_ne_zero h0) hap
    rw [h0, Function.iterate_zero_apply, h]
  obtain ⟨g, hg, hqg, htg⟩ := in_edge hobX hoba
  have htgp : Per u v τ (tl u v q g) := K3 huv hτ hinj hla hla' hlb (Ne.symm hne) hqg htg
  have htgC : tl u v q g ∈ C := clo_sub hC haC htg
  have htgY : tl u v q g ∈ Clo u v q b := K1 huv hτ hinj hC hle hbC hdb htgC htgp
  obtain ⟨T2, T1⟩ := tight hC hle hbC hdb
  rcases Nat.eq_zero_or_pos lb with h0 | hpos
  · subst h0
    exact T2 g hg htgY hqg
  · obtain ⟨i, hi, hqi, hti, hnp⟩ := K2 huv hτ hinj hC hle hrange hbC hdb hlb hlb' hpos
    have h5 := T1 i g hi hg hti htgY (hqi.trans hqg.symm)
    subst h5
    exact hnp htgp

end Fork

/-! ## The probe direction -/

theorem iter_U {u v τ : Fin m → Fin n} (hτ : ∀ i, τ i = u i ∨ τ i = v i)
    (hinj : Function.Injective τ) {C : Finset (Fin n)} (hC : IsComp u v C) {U : Finset (Fin n)}
    (hstep : ∀ x ∈ C, ¬ Per u v τ x → (x ∈ U ↔ Fs u v τ x ∈ U)) {x : Fin n} (hxC : x ∈ C) :
    ∀ L, (∀ l < L, ¬ Per u v τ ((Fs u v τ)^[l] x)) → (x ∈ U ↔ (Fs u v τ)^[L] x ∈ U) := by
  intro L
  induction L with
  | zero => intro _; exact Iff.rfl
  | succ L ih =>
    intro hL
    rw [ih (fun l hl => hL l (by omega)), Function.iterate_succ_apply']
    exact hstep _ (iter_mem hτ hinj hC hxC L) (hL L (by omega))

theorem Q_to_RHS_comp {u v : Fin m → Fin n} {q : Fin m → Bool × Bool} (huv : ∀ i, u i ≠ v i)
    {r : ℕ} (H : Fin r → Finset (Fin n))
    (hpf : ∀ C, IsComp u v C → (E u v C).card ≤ C.card)
    (hqv : ∀ i, q i ≠ (false, false)) (hev : ∀ z, Sol u v q z → ∀ j, (z ∩ H j).card % 2 = 0)
    (br : Finset (Fin m)) (hbr : ∀ i, i ∈ br ↔ ∃ U : Finset (Fin n), cutS u v U = {i})
    (cyc : Finset (Fin n)) (hcyc : ∀ i, i ∉ br → u i ∈ cyc ∧ v i ∈ cyc)
    (Mk : Finset (Fin n)) (hMk : ∀ x, x ∈ Mk ↔ ∃ j, x ∈ H j)
    {C : Finset (Fin n)} (hC : IsComp u v C) :
    ((E u v C).card = C.card ∧ ∀ a ∈ Mk ∩ C, ∀ b ∈ Mk ∩ C, ∀ U : Finset (Fin n), a ∈ U →
      b ∉ U → (br ∩ cutS u v U).Nonempty) ∨ (∀ j, H j ∩ C ⊆ cyc ∧ Even (H j ∩ C).card) := by
  classical
  have hle := hpf C hC
  have hnt : ∀ x j, x ∈ H j → Live u v q x → ∃ y ∈ SC u v q x, y ≠ x := by
    intro x j hxH hlive
    by_contra hno
    push Not at hno
    have h1 := live_even hqv hev hlive j
    have h2 : SC u v q x ∩ H j = {x} := by
      ext y; simp only [mem_inter, mem_singleton]
      constructor
      · rintro ⟨hy, _⟩; exact hno y hy
      · rintro rfl; exact ⟨self_mem_SC y, hxH⟩
    rw [h2] at h1; simp at h1
  by_cases hdead : ∃ w ∈ Mk ∩ C, ¬ Live u v q w
  · left
    obtain ⟨w0, hw0, hw0d⟩ := hdead
    have hw0C : w0 ∈ C := (mem_inter.1 hw0).2
    have heq : (E u v C).card = C.card :=
      dense_eq hC hle (clo_sub hC hw0C) ⟨w0, self_mem_Clo w0⟩ (dense_dead hw0d)
    obtain ⟨T2, T1⟩ := tight hC hle hw0C hw0d
    have halldead : ∀ x ∈ Mk ∩ C, ¬ Live u v q x := by
      intro x hx hlive
      obtain ⟨j, hxH⟩ := (hMk x).1 (mem_inter.1 hx).1
      have hxC := (mem_inter.1 hx).2
      obtain ⟨y, hy, hyx⟩ := hnt x j hxH hlive
      have hSCC : SC u v q x ⊆ C := fun s hs => clo_sub hC hxC (mem_SC.1 hs).1
      by_cases hdisj : Disjoint (SC u v q x) (Clo u v q w0)
      · exact DD hC hle hSCC (clo_sub hC hw0C) ⟨x, self_mem_SC x⟩ ⟨w0, self_mem_Clo w0⟩ hdisj
          (dense_sc hy hyx) (dense_dead hw0d)
      · rw [not_disjoint_iff] at hdisj
        obtain ⟨s0, hs0, hs0X⟩ := hdisj
        have hSCX : SC u v q x ⊆ Clo u v q w0 := by
          intro s hs
          exact Clo_trans (Clo_trans hs0X (mem_SC.1 hs0).2) (mem_SC.1 hs).1
        have hw0SC : w0 ∉ SC u v q x := by
          intro hw
          obtain ⟨i, hi, hqi, hti⟩ := sc_in hw ⟨y, hy, hyx⟩
          exact T2 i hi (hSCX hti) hqi
        have hZ : Closed u v q (Clo u v q w0 \ SC u v q x) := by
          intro i hi ht
          rw [mem_sdiff] at ht ⊢
          refine ⟨Clo_closed w0 i hi ht.1, fun hqs => ?_⟩
          obtain ⟨i', hi', hqi', hti'⟩ := sc_in hqs ⟨y, hy, hyx⟩
          have h5 := T1 i i' hi hi' ht.1 (hSCX hti') hqi'.symm
          subst h5
          exact ht.2 hti'
        have hxX : x ∈ Clo u v q w0 := hSCX (self_mem_SC x)
        have h6 := Clo_min hZ (mem_sdiff.2 ⟨self_mem_Clo w0, hw0SC⟩) hxX
        exact (mem_sdiff.1 h6).2 (self_mem_SC x)
    refine ⟨heq, ?_⟩
    intro a ha b hb U haU hbU
    rw [Finset.nonempty_iff_ne_empty]
    intro hU
    obtain ⟨τ, hinj, hτ⟩ := exists_orient hpf
    have hrange := range_of_tight hτ hinj hC heq
    have hstep : ∀ x ∈ C, ¬ Per u v τ x → (x ∈ U ↔ Fs u v τ x ∈ U) := by
      intro x hxC hxp
      obtain ⟨i, rfl⟩ := hrange x hxC
      have hnpp : ¬ PerP u v τ (τ i) := fun h => hxp ⟨⟨i, rfl⟩, h⟩
      have hib : i ∈ br := (hbr i).2 ⟨_, cut_IT hτ hinj i hnpp⟩
      have hic : i ∉ cutS u v U := by
        intro h
        have h7 : i ∈ br ∩ cutS u v U := mem_inter.2 ⟨hib, h⟩
        rw [hU] at h7; simp at h7
      rw [mem_cut, not_not, cross_iff hτ i] at hic
      rw [Fs_tau hinj i]; exact hic
    have haC := (mem_inter.1 ha).2
    have hbC := (mem_inter.1 hb).2
    have hexa := ev_per hτ hinj hC hrange haC
    have hexb := ev_per hτ hinj hC hrange hbC
    have hfork := fork_eq huv hτ hinj hC hle hrange haC hbC (halldead a ha) (halldead b hb)
      (Nat.find_spec hexa) (fun l hl => Nat.find_min hexa hl) (Nat.find_spec hexb)
      (fun l hl => Nat.find_min hexb hl)
    have h1 := iter_U hτ hinj hC hstep haC (Nat.find hexa) (fun l hl => Nat.find_min hexa hl)
    have h2 := iter_U hτ hinj hC hstep hbC (Nat.find hexb) (fun l hl => Nat.find_min hexb hl)
    rw [hfork] at h1
    exact hbU (h2.2 (h1.1 haU))
  · right
    push Not at hdead
    intro j
    have hlive : ∀ x ∈ H j ∩ C, Live u v q x := fun x hx =>
      hdead x (mem_inter.2 ⟨(hMk x).2 ⟨j, (mem_inter.1 hx).1⟩, (mem_inter.1 hx).2⟩)
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := hnt x j (mem_inter.1 hx).1 (hlive x hx)
      obtain ⟨i, hib, hxi⟩ := nb_of_sc (mem_SC.1 hy).1 (mem_SC.1 hy).2 hyx
      have hi : i ∉ br := fun h => hib ((hbr i).1 h)
      rcases hxi with h | h
      · rw [← h]; exact (hcyc i hi).1
      · rw [← h]; exact (hcyc i hi).2
    · rcases (H j ∩ C).eq_empty_or_nonempty with h0 | ⟨w0, hw0⟩
      · rw [h0]; simp
      · have hw0C := (mem_inter.1 hw0).2
        obtain ⟨y0, hy0, hy0w⟩ := hnt w0 j (mem_inter.1 hw0).1 (hlive w0 hw0)
        have hsub : H j ∩ C ⊆ SC u v q w0 := by
          intro x hx
          have hxC := (mem_inter.1 hx).2
          obtain ⟨y, hy, hyx⟩ := hnt x j (mem_inter.1 hx).1 (hlive x hx)
          by_cases hdisj : Disjoint (SC u v q x) (SC u v q w0)
          · exact (DD hC hle (fun s hs => clo_sub hC hxC (mem_SC.1 hs).1)
              (fun s hs => clo_sub hC hw0C (mem_SC.1 hs).1) ⟨x, self_mem_SC x⟩
              ⟨w0, self_mem_SC w0⟩ hdisj (dense_sc hy hyx) (dense_sc hy0 hy0w)).elim
          · rw [not_disjoint_iff] at hdisj
            obtain ⟨s, hs1, hs2⟩ := hdisj
            rw [mem_SC] at hs1 hs2 ⊢
            exact ⟨Clo_trans hs2.1 hs1.2, Clo_trans hs1.1 hs2.2⟩
        have heq : H j ∩ C = SC u v q w0 ∩ H j := by
          ext x; simp only [mem_inter]
          constructor
          · intro hx; exact ⟨hsub (mem_inter.2 hx), hx.1⟩
          · rintro ⟨hx1, hx2⟩; exact ⟨hx2, clo_sub hC hw0C (mem_SC.1 hx1).1⟩
        rw [heq, Nat.even_iff]
        exact live_even hqv hev (hlive w0 hw0) j

theorem main : ∀ (n m t : Nat) (u v : Fin m → Fin n) (H : Fin t → Finset (Fin n)),
  (∀ i, u i ≠ v i) →
  let Bits := Finset (Fin n)
  let cube := (Finset.univ : Finset Bits)
  let labels := (Finset.univ : Finset (Fin m))
  let rows := (Finset.univ : Finset (Fin t))
  let cut := fun (S : Bits) => labels.filter
    (fun i => decide (u i ∈ S) != decide (v i ∈ S))
  let comps := cube.filter (fun C => C.Nonempty ∧ (cut C).card = 0 ∧
    ∀ D ∈ C.powerset, D.Nonempty → (cut D).card = 0 → D = C)
  let edges := fun (C : Bits) => labels.filter (fun i => u i ∈ C)
  let bridges := labels.filter (fun i => ∃ U ∈ cube, cut U = {i})
  let cyclic := (labels \ bridges).biUnion (fun i => ({u i, v i} : Bits))
  let marked := rows.biUnion H
  (∀ C ∈ comps, (edges C).card ≤ C.card) →
  let Signing := Fin m → Bool × Bool
  let sat := fun (A : Finset Bits) (p : Signing) =>
    ∃ x ∈ A, ∀ i, (decide (u i ∈ x), decide (v i ∈ x)) ≠ p i
  let same := fun (x z : Bits) =>
    ∀ j : Fin t, (x ∩ H j).card % 2 = (z ∩ H j).card % 2
  (∀ A B : Finset Bits, (∀ p, sat A p ↔ sat B p) →
    ∀ z : Bits, ((∃ x ∈ A, same x z) ↔ ∃ x ∈ B, same x z)) ↔
    ∀ C ∈ comps,
      (((edges C).card = C.card) ∧
        ∀ a ∈ marked ∩ C, ∀ b ∈ marked ∩ C, ∀ U ∈ cube,
          a ∈ U → b ∉ U → (bridges ∩ cut U).Nonempty) ∨
      (∀ j : Fin t, H j ∩ C ⊆ cyclic ∧ Even (H j ∩ C).card) := by
  intro n m t u v H huv Bits cube labels rows cut comps edges bridges cyclic marked hpf Signing
    sat same
  have hcomps : ∀ C, C ∈ comps ↔ IsComp u v C := by
    intro C
    simp only [comps, cube, mem_filter, mem_univ, true_and, mem_powerset]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, (cut_card_zero (u := u) (v := v) (S := C)).1 h2,
        fun D hD hne hcl => h3 D hD hne ((cut_card_zero (u := u) (v := v) (S := D)).2 hcl)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, (cut_card_zero (u := u) (v := v) (S := C)).2 h2,
        fun D hD hne hcl => h3 D hD hne ((cut_card_zero (u := u) (v := v) (S := D)).1 hcl)⟩
  have hedges : ∀ C, IsComp u v C → edges C = E u v C := by
    intro C hC
    ext i
    simp only [edges, labels, mem_filter, mem_univ, true_and, mem_E]
    exact ⟨fun h => ⟨h, (hC.closed i).1 h⟩, fun h => h.1⟩
  have hbr : ∀ i, i ∈ bridges ↔ ∃ U : Finset (Fin n), cutS u v U = {i} := by
    intro i
    simp only [bridges, labels, cube, mem_filter, mem_univ, true_and]
    exact Iff.rfl
  have hcyc : ∀ i, i ∉ bridges → u i ∈ cyclic ∧ v i ∈ cyclic := by
    intro i hi
    simp only [cyclic, mem_biUnion, mem_sdiff, labels, mem_univ, true_and]
    exact ⟨⟨i, hi, mem_insert_self _ _⟩, ⟨i, hi, mem_insert_of_mem (mem_singleton_self _)⟩⟩
  have hcyc' : ∀ x ∈ cyclic, ∃ i, i ∉ bridges ∧ (x = u i ∨ x = v i) := by
    intro x hx
    simp only [cyclic, mem_biUnion, mem_sdiff, labels, mem_univ, true_and] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    have h' : x ∈ ({u a, v a} : Finset (Fin n)) := hxa
    rw [mem_insert, mem_singleton] at h'
    exact ⟨a, ha, h'⟩
  have hMk : ∀ x, x ∈ marked ↔ ∃ j, x ∈ H j := by
    intro x
    simp [marked, rows]
  have hMk' : ∀ j, H j ⊆ marked := fun j x hx => (hMk x).2 ⟨j, hx⟩
  have hpf' : ∀ C, IsComp u v C → (E u v C).card ≤ C.card := fun C hC => by
    have h := hpf C ((hcomps C).2 hC); rwa [hedges C hC] at h
  constructor
  · intro hL
    obtain ⟨q, hqv, hev⟩ := LHS_to_Q (u := u) (v := v) (H := H) hL
    intro C hC
    have hC' := (hcomps C).1 hC
    rw [hedges C hC']
    rcases Q_to_RHS_comp huv H hpf' hqv hev bridges hbr cyclic hcyc marked hMk hC' with
      ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, fun a ha b hb U _ haU hbU => h2 a ha b hb U haU hbU⟩
    · exact Or.inr h
  · intro hR
    apply Q_to_LHS
    refine RHS_to_Q huv H hpf' bridges hbr cyclic hcyc' marked hMk' ?_
    intro C hC
    have h := hR C ((hcomps C).2 hC)
    rw [hedges C hC] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, fun a ha b hb U haU hbU => h2 a ha b hb U (mem_univ _) haU hbU⟩
    · exact Or.inr h

end PEqualNP.Outside.L_lib_1158_aux

theorem PEqualNP.Outside.L_lib_1158 : ∀ (n m t : Nat) (u v : Fin m → Fin n) (H : Fin t → Finset (Fin n)),
  (∀ i, u i ≠ v i) →
  let Bits := Finset (Fin n)
  let cube := (Finset.univ : Finset Bits)
  let labels := (Finset.univ : Finset (Fin m))
  let rows := (Finset.univ : Finset (Fin t))
  let cut := fun (S : Bits) => labels.filter
    (fun i => decide (u i ∈ S) != decide (v i ∈ S))
  let comps := cube.filter (fun C => C.Nonempty ∧ (cut C).card = 0 ∧
    ∀ D ∈ C.powerset, D.Nonempty → (cut D).card = 0 → D = C)
  let edges := fun (C : Bits) => labels.filter (fun i => u i ∈ C)
  let bridges := labels.filter (fun i => ∃ U ∈ cube, cut U = {i})
  let cyclic := (labels \ bridges).biUnion (fun i => ({u i, v i} : Bits))
  let marked := rows.biUnion H
  (∀ C ∈ comps, (edges C).card ≤ C.card) →
  let Signing := Fin m → Bool × Bool
  let sat := fun (A : Finset Bits) (p : Signing) =>
    ∃ x ∈ A, ∀ i, (decide (u i ∈ x), decide (v i ∈ x)) ≠ p i
  let same := fun (x z : Bits) =>
    ∀ j : Fin t, (x ∩ H j).card % 2 = (z ∩ H j).card % 2
  (∀ A B : Finset Bits, (∀ p, sat A p ↔ sat B p) →
    ∀ z : Bits, ((∃ x ∈ A, same x z) ↔ ∃ x ∈ B, same x z)) ↔
    ∀ C ∈ comps,
      (((edges C).card = C.card) ∧
        ∀ a ∈ marked ∩ C, ∀ b ∈ marked ∩ C, ∀ U ∈ cube,
          a ∈ U → b ∉ U → (bridges ∩ cut U).Nonempty) ∨
      (∀ j : Fin t, H j ∩ C ⊆ cyclic ∧ Even (H j ∩ C).card) :=
  PEqualNP.Outside.L_lib_1158_aux.main
