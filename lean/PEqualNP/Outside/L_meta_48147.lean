import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48147_aux

theorem ca_card_succ {r : ℕ} (p : Fin (r+1) → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin (r+1))).filter p).card =
      (if p 0 then 1 else 0) + ((Finset.univ : Finset (Fin r)).filter (fun a => p a.succ)).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]

theorem ca_split {r : ℕ} (P : (Fin (r+1) → Bool) → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin (r+1) → Bool)).filter P).card =
      ((Finset.univ : Finset (Fin r → Bool)).filter (fun c => P (Fin.cons true c))).card +
      ((Finset.univ : Finset (Fin r → Bool)).filter (fun c => P (Fin.cons false c))).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

theorem ca_const {r : ℕ} (φ : Fin (r+1) → (Fin (r+1) → Bool) → Bool)
    (hφ : ∀ a c c', (∀ b, b < a → c b = c' b) → φ a c = φ a c') (c : Fin (r+1) → Bool) :
    φ 0 c = φ 0 (fun _ => false) :=
  hφ 0 _ _ (fun b hb => absurd hb (Fin.not_lt_zero b))

theorem ca_shift {r : ℕ} (φ : Fin (r+1) → (Fin (r+1) → Bool) → Bool)
    (hφ : ∀ a c c', (∀ b, b < a → c b = c' b) → φ a c = φ a c') (x : Bool) :
    ∀ (a : Fin r) (c c' : Fin r → Bool), (∀ b, b < a → c b = c' b) →
      φ a.succ (Fin.cons x c) = φ a.succ (Fin.cons x c') := by
  intro a c c' h
  apply hφ
  intro b hb
  cases b using Fin.cases with
  | zero => rfl
  | succ b => simpa using h b (Fin.succ_lt_succ_iff.mp hb)

theorem ca_pascal (s e : ℕ) :
    ∑ i ∈ Finset.range (e+1), Nat.choose (s+1) i =
      ∑ i ∈ Finset.range e, Nat.choose s i + ∑ i ∈ Finset.range (e+1), Nat.choose s i := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (e+1), Finset.sum_range_succ _ e,
      Nat.choose_succ_succ]
    ring

theorem count_adapt (r s e : ℕ) (φ ρ : Fin r → (Fin r → Bool) → Bool)
    (hφ : ∀ a c c', (∀ b, b < a → c b = c' b) → φ a c = φ a c')
    (hρ : ∀ a c c', (∀ b, b < a → c b = c' b) → ρ a c = ρ a c')
    (hm : ∀ c, ((Finset.univ : Finset (Fin r)).filter (fun a => φ a c = true ∧ c a = ρ a c)).card ≤ e) :
    ((Finset.univ : Finset (Fin r → Bool)).filter
      (fun c => s < ((Finset.univ : Finset (Fin r)).filter (fun a => φ a c = true)).card)).card ≤
      2 ^ (r - s) * ∑ i ∈ Finset.range e, Nat.choose s i := by
  induction r generalizing s e with
  | zero => simp
  | succ r ih =>
    obtain ⟨v, hv⟩ : ∃ v, ∀ c, φ 0 c = v := ⟨_, ca_const φ hφ⟩
    obtain ⟨w, hw⟩ : ∃ w, ∀ c, ρ 0 c = w := ⟨_, ca_const ρ hρ⟩
    have key : ∀ b s e, (∀ c', ((Finset.univ : Finset (Fin r)).filter (fun a =>
        φ a.succ (Fin.cons b c') = true ∧ c' a = ρ a.succ (Fin.cons b c'))).card ≤ e) →
        ((Finset.univ : Finset (Fin r → Bool)).filter (fun c' => s <
          ((Finset.univ : Finset (Fin r)).filter (fun a => φ a.succ (Fin.cons b c') = true)).card)).card
          ≤ 2 ^ (r - s) * ∑ i ∈ Finset.range e, Nat.choose s i :=
      fun b s e h => ih s e _ _ (ca_shift φ hφ b) (ca_shift ρ hρ b) h
    have hm' : ∀ b c', (if v = true ∧ b = w then 1 else 0) + ((Finset.univ : Finset (Fin r)).filter (fun a =>
        φ a.succ (Fin.cons b c') = true ∧ c' a = ρ a.succ (Fin.cons b c'))).card ≤ e := by
      intro b c'
      have := hm (Fin.cons b c')
      rw [ca_card_succ] at this
      simpa [hv, hw] using this
    rcases Nat.lt_or_ge r s with hs | hs
    · refine le_trans (le_of_eq (Finset.card_eq_zero.mpr
        (Finset.filter_eq_empty_iff.mpr fun c _ => ?_))) (Nat.zero_le _)
      have := Finset.card_le_univ ((Finset.univ : Finset (Fin (r+1))).filter fun a => φ a c = true)
      simp only [Fintype.card_fin] at this
      omega
    rw [ca_split]
    simp only [ca_card_succ, hv]
    cases v
    · simp only [Bool.false_eq_true, ite_false, zero_add]
      rw [Nat.succ_sub hs, pow_succ]
      have h1 := key true s e (fun c' => by simpa using hm' true c')
      have h2 := key false s e (fun c' => by simpa using hm' false c')
      linarith
    · cases e with
      | zero => exact absurd (hm' w fun _ => false) (by simp)
      | succ e =>
        cases s with
        | zero =>
          refine (add_le_add (Finset.card_filter_le _ _) (Finset.card_filter_le _ _)).trans ?_
          simp [Finset.sum_range_succ', pow_succ]
          omega
        | succ s =>
          rw [show r + 1 - (s + 1) = r - s by omega, ca_pascal]
          have e1 : ∀ x, (s + 1 < 1 + x) = (s < x) := fun x => propext (by omega)
          simp only [ite_true, e1]
          cases w
          · have h1 := key false s e (fun c' => by have := hm' false c'; simp at this; omega)
            have h2 := key true s (e + 1) (fun c' => by have := hm' true c'; simp at this; omega)
            linarith
          · have h1 := key true s e (fun c' => by have := hm' true c'; simp at this; omega)
            have h2 := key false s (e + 1) (fun c' => by have := hm' false c'; simp at this; omega)
            linarith

noncomputable def up_pack {r n : ℕ} (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool) :
    ℕ → Finset (Fin r × Fin n) → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin r × Fin n) → Prop) (fun _ => True)
    (fun _ prev y => ∃ (u v : Finset (Fin r × Fin n)) (k : Fin r × Fin n),
      prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u k = true ∧ f v k = false)

def up_alpha {r n : ℕ} (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r) (u : Finset (Fin n)) : ℕ :=
  (u.powerset.filter (fun z => ∀ i ∈ z, ∀ k ∈ z, edge a i k = false)).sup Finset.card

def up_gain {r n : ℕ} (edge : Fin r → Fin n → Fin n → Bool) (x : Fin r → Finset (Fin n))
    (j : Fin r → Fin n) (a : Fin r) : Bool :=
  decide (up_alpha edge a (insert (j a) (x a)) = up_alpha edge a (x a) + 1)

def up_query {r n : ℕ} (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) (c : Fin r → Bool)
    (a : Fin r) : Finset (Fin r × Fin n) :=
  Finset.univ.filter (fun p : Fin r × Fin n =>
    (p.1 < a ∧ (p.2 ∈ x p.1 ∨ (c p.1 = true ∧ p.2 = j p.1))) ∨ (p.1 = a ∧ p.2 ∈ x a))

def up_P {r n : ℕ} (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) (c : Fin r → Bool)
    (m : ℕ) : Finset (Fin r × Fin n) :=
  Finset.univ.filter (fun p : Fin r × Fin n =>
    p.1.val < m ∧ (p.2 ∈ x p.1 ∨ (c p.1 = true ∧ p.2 = j p.1)))

def up_F {r n : ℕ} (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) (c : Fin r → Bool)
    (a : Fin r) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ∈ x a ∨ (c a = true ∧ i = j a))

theorem up_pack_mono {r n : ℕ} (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool) :
    ∀ (t : ℕ) (u y : Finset (Fin r × Fin n)), up_pack f t u → u ⊆ y → up_pack f t y
  | 0, _, _, _, _ => trivial
  | t + 1, u, y, h, huy => by
    obtain ⟨u', v, k, h1, h2, h3, h4, h5⟩ := h
    exact ⟨u', v, k, h1, h2, h3.trans huy, h4, h5⟩

theorem up_pack_pred {r n : ℕ} (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool) :
    ∀ (t : ℕ) (y : Finset (Fin r × Fin n)), up_pack f (t + 1) y → up_pack f t y
  | 0, _, _ => trivial
  | t + 1, y, h => by
    obtain ⟨u, v, k, h1, h2, h3, h4, h5⟩ := h
    exact ⟨u, v, k, up_pack_pred f t u h1, h2, h3, h4, h5⟩

theorem up_pack_le {r n : ℕ} (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool) (m d : ℕ)
    (y : Finset (Fin r × Fin n)) (h : up_pack f (m + d) y) : up_pack f m y := by
  induction d with
  | zero => exact h
  | succ d ih => exact ih (up_pack_pred f _ _ h)

theorem up_chain {r n : ℕ} (edge : Fin r → Fin n → Fin n → Bool)
    (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
    (h3 : ∀ y a i, (a, i) ∉ y → (∀ k, (a, k) ∈ y → edge a k i = false) → f y (a, i) = true)
    (h4 : ∀ y a i, (a, i) ∈ y → f y (a, i) = false)
    (a : Fin r) (u0 : Finset (Fin r × Fin n)) (hu0 : ∀ i, (a, i) ∉ u0) (t : ℕ) (hp : up_pack f t u0)
    (I : Finset (Fin n)) (hI : ∀ i ∈ I, ∀ k ∈ I, edge a i k = false) :
    up_pack f (t + I.card) (u0 ∪ I.image (fun i => (a, i))) := by
  induction I using Finset.induction_on with
  | empty => simpa using hp
  | insert i J hiJ ih =>
    have hJ := ih (fun p hp q hq => hI p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq))
    rw [Finset.card_insert_of_notMem hiJ, ← Nat.add_assoc]
    refine ⟨_, _, (a, i), hJ, ?_, subset_rfl, ?_, ?_⟩
    · exact Finset.union_subset_union subset_rfl (Finset.image_subset_image (Finset.subset_insert i J))
    · apply h3
      · simp [hu0, hiJ]
      · intro k hk
        simp only [Finset.mem_union, hu0, false_or, Finset.mem_image, Prod.mk.injEq] at hk
        obtain ⟨k', hk', -, rfl⟩ := hk
        exact hI k' (Finset.mem_insert_of_mem hk') i (Finset.mem_insert_self i J)
    · apply h4
      simp

theorem up_alpha_spec {r n : ℕ} (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r) (u : Finset (Fin n)) :
    ∃ I ⊆ u, (∀ i ∈ I, ∀ k ∈ I, edge a i k = false) ∧ I.card = up_alpha edge a u := by
  obtain ⟨I, hI, he⟩ := Finset.exists_mem_eq_sup
    (u.powerset.filter (fun z => ∀ i ∈ z, ∀ k ∈ z, edge a i k = false)) ⟨∅, by simp⟩ Finset.card
  simp only [Finset.mem_filter, Finset.mem_powerset] at hI
  exact ⟨I, hI.1, hI.2, he.symm⟩

theorem up_alpha_ge {r n : ℕ} (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r) (u I : Finset (Fin n))
    (hIu : I ⊆ u) (hI : ∀ i ∈ I, ∀ k ∈ I, edge a i k = false) : I.card ≤ up_alpha edge a u :=
  Finset.le_sup (f := Finset.card) (by simp only [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hIu, hI⟩)

theorem up_alpha_insert {r n : ℕ} (edge : Fin r → Fin n → Fin n → Bool) (a : Fin r) (u : Finset (Fin n))
    (i : Fin n) : up_alpha edge a (insert i u) ≤ up_alpha edge a u + 1 := by
  obtain ⟨I, hIu, hI, hc⟩ := up_alpha_spec edge a (insert i u)
  have h1 := up_alpha_ge edge a u (I.erase i) (Finset.subset_insert_iff.mp hIu)
    (fun p hp q hq => hI p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq))
  have h2 := Finset.pred_card_le_card_erase (s := I) (a := i)
  omega

theorem up_sum_succ {r : ℕ} (g : Fin r → ℕ) (m : ℕ) (hm : m < r) :
    ∑ b : Fin r, (if b.val < m + 1 then g b else 0) =
      (∑ b : Fin r, if b.val < m then g b else 0) + g ⟨m, hm⟩ := by
  have h : ∀ b : Fin r, (if b.val < m + 1 then g b else 0) =
      (if b.val < m then g b else 0) + (if (⟨m, hm⟩ : Fin r) = b then g b else 0) := by
    intro b
    by_cases h1 : b.val < m
    · have h2 : (⟨m, hm⟩ : Fin r) ≠ b := by
        intro h
        subst h
        simp at h1
      simp [h1, h2, show b.val < m + 1 by omega]
    · by_cases h2 : (⟨m, hm⟩ : Fin r) = b
      · subst h2
        simp
      · have h3 : ¬ b.val < m + 1 := by
          intro h
          apply h2
          ext
          simp only
          omega
        simp [h1, h2, h3]
  rw [Finset.sum_congr rfl (fun b _ => h b), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem up_P_zero {r n : ℕ} (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) (c : Fin r → Bool)
    (a : Fin r) (i : Fin n) : (a, i) ∉ up_P x j c a.val := by
  simp [up_P]

theorem up_sub1 {r n : ℕ} (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) (c : Fin r → Bool)
    (a : Fin r) (I : Finset (Fin n)) (hI : I ⊆ up_F x j c a) :
    up_P x j c a.val ∪ I.image (fun i => (a, i)) ⊆ up_P x j c (a.val + 1) := by
  intro p hp
  simp only [up_P, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hp ⊢
  rcases hp with ⟨h1, h2⟩ | ⟨i, hi, rfl⟩
  · exact ⟨by omega, h2⟩
  · have := hI hi
    simp only [up_F, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact ⟨by simp, this⟩

theorem up_sub2 {r n : ℕ} (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) (c : Fin r → Bool)
    (a : Fin r) (I : Finset (Fin n)) (hI : I ⊆ x a) :
    up_P x j c a.val ∪ I.image (fun i => (a, i)) ⊆ up_query x j c a := by
  intro p hp
  simp only [up_P, up_query, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image] at hp ⊢
  rcases hp with ⟨h1, h2⟩ | ⟨i, hi, rfl⟩
  · exact Or.inl ⟨Fin.lt_def.mpr h1, h2⟩
  · exact Or.inr ⟨rfl, hI hi⟩

theorem up_sub3 {r n : ℕ} (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) (c : Fin r → Bool)
    (a : Fin r) : up_query x j c a ⊆ up_P x j c (a.val + 1) := by
  intro p hp
  simp only [up_P, up_query, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by have := Fin.lt_def.mp h1; omega, h2⟩
  · subst h1
    exact ⟨by omega, Or.inl h2⟩

theorem up_sub4 {r n : ℕ} (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) (c : Fin r → Bool)
    (a : Fin r) (hc : c a = false) : up_P x j c (a.val + 1) ⊆ up_query x j c a := by
  intro p hp
  simp only [up_P, up_query, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨h1, h2⟩ := hp
  by_cases h : p.1.val < a.val
  · exact Or.inl ⟨Fin.lt_def.mpr h, h2⟩
  · have hp1 : p.1 = a := Fin.ext (by omega)
    subst hp1
    rw [hc] at h2
    simp only [Bool.false_eq_true, false_and, or_false] at h2
    exact Or.inr ⟨rfl, h2⟩

theorem up_step {r n : ℕ} (edge : Fin r → Fin n → Fin n → Bool)
    (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool) (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n)
    (c : Fin r → Bool)
    (h3 : ∀ y a i, (a, i) ∉ y → (∀ k, (a, k) ∈ y → edge a k i = false) → f y (a, i) = true)
    (h4 : ∀ y a i, (a, i) ∈ y → f y (a, i) = false)
    (a : Fin r) (t : ℕ) (hp : up_pack f t (up_P x j c a.val)) :
    up_pack f (t + (up_alpha edge a (up_F x j c a) +
      if (f (up_query x j c a) (a, j a) ≠ up_gain edge x j a ∧ c a = f (up_query x j c a) (a, j a))
      then 1 else 0)) (up_P x j c (a.val + 1)) := by
  split_ifs with hm
  · obtain ⟨hne, hc⟩ := hm
    cases hca : c a
    · rw [hca] at hc
      have hG : up_gain edge x j a = true := by
        revert hne
        rw [← hc]
        cases up_gain edge x j a <;> simp
      have hF : up_F x j c a = x a := by
        ext i
        simp [up_F, hca]
      unfold up_gain at hG
      simp only [decide_eq_true_eq] at hG
      obtain ⟨I, hIu, hI, hIc⟩ := up_alpha_spec edge a (insert (j a) (x a))
      have hjI : j a ∈ I := by
        by_contra hj
        have := up_alpha_ge edge a (x a) I ((Finset.subset_insert_iff_of_notMem hj).mp hIu) hI
        omega
      have hI'u : I.erase (j a) ⊆ x a := Finset.subset_insert_iff.mp hIu
      have hI' : ∀ i ∈ I.erase (j a), ∀ k ∈ I.erase (j a), edge a i k = false :=
        fun p hp q hq => hI p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq)
      have hI'c : (I.erase (j a)).card = up_alpha edge a (x a) := by
        rw [Finset.card_erase_of_mem hjI]
        omega
      have hch := up_chain edge f h3 h4 a _ (up_P_zero x j c a) t hp (I.erase (j a)) hI'
      rw [hI'c] at hch
      rw [hF, ← Nat.add_assoc]
      refine ⟨_, up_query x j c a, (a, j a), hch, up_sub2 x j c a _ hI'u, up_sub3 x j c a, ?_, hc.symm⟩
      apply h3
      · simp only [Finset.mem_union, up_P_zero, false_or, Finset.mem_image, Prod.mk.injEq, not_exists,
          not_and]
        intro k hk _ hkj
        subst hkj
        exact Finset.notMem_erase _ _ hk
      · intro k hk
        simp only [Finset.mem_union, up_P_zero, false_or, Finset.mem_image, Prod.mk.injEq] at hk
        obtain ⟨k', hk', -, rfl⟩ := hk
        exact hI k' (Finset.mem_of_mem_erase hk') (j a) hjI
    · rw [hca] at hc
      have hG : up_gain edge x j a = false := by
        revert hne
        rw [← hc]
        cases up_gain edge x j a <;> simp
      have hF : up_F x j c a = insert (j a) (x a) := by
        ext i
        simp [up_F, hca, or_comm]
      unfold up_gain at hG
      simp only [decide_eq_false_iff_not] at hG
      have hle := up_alpha_insert edge a (x a) (j a)
      obtain ⟨I, hIu, hI, hIc⟩ := up_alpha_spec edge a (x a)
      have hch := up_chain edge f h3 h4 a _ (up_P_zero x j c a) t hp I hI
      rw [hIc] at hch
      have hq := up_pack_mono f _ _ _ hch (up_sub2 x j c a I hIu)
      have hfin : up_pack f (t + up_alpha edge a (x a) + 1) (up_P x j c (a.val + 1)) := by
        refine ⟨_, _, (a, j a), hq, up_sub3 x j c a, subset_rfl, hc.symm, h4 _ _ _ ?_⟩
        simp [up_P, hca]
      rw [hF]
      refine up_pack_le f _ (up_alpha edge a (x a) - up_alpha edge a (insert (j a) (x a))) _ ?_
      have heq : t + (up_alpha edge a (insert (j a) (x a)) + 1) +
          (up_alpha edge a (x a) - up_alpha edge a (insert (j a) (x a))) =
          t + up_alpha edge a (x a) + 1 := by omega
      rw [heq]
      exact hfin
  · rw [Nat.add_zero]
    obtain ⟨I, hIu, hI, hIc⟩ := up_alpha_spec edge a (up_F x j c a)
    have hch := up_chain edge f h3 h4 a _ (up_P_zero x j c a) t hp I hI
    rw [hIc] at hch
    exact up_pack_mono f _ _ _ hch (up_sub1 x j c a I hIu)

theorem up_main {r n : ℕ} (e : ℕ) (edge : Fin r → Fin n → Fin n → Bool)
    (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool) (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n)
    (h3 : ∀ y a i, (a, i) ∉ y → (∀ k, (a, k) ∈ y → edge a k i = false) → f y (a, i) = true)
    (h4 : ∀ y a i, (a, i) ∈ y → f y (a, i) = false)
    (h5 : ∀ y, ¬ up_pack f (∑ a, up_alpha edge a (Finset.univ.filter (fun i => (a, i) ∈ y)) + e + 1) y)
    (c : Fin r → Bool) :
    (Finset.univ.filter (fun a => f (up_query x j c a) (a, j a) ≠ up_gain edge x j a ∧
      c a = f (up_query x j c a) (a, j a))).card ≤ e := by
  have key : ∀ m, m ≤ r → up_pack f (∑ b : Fin r, if b.val < m then
      (up_alpha edge b (up_F x j c b) +
        if (f (up_query x j c b) (b, j b) ≠ up_gain edge x j b ∧ c b = f (up_query x j c b) (b, j b))
        then 1 else 0) else 0) (up_P x j c m) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.not_lt_zero, ite_false, Finset.sum_const_zero]
      trivial
    | succ m ih =>
      intro hm
      rw [up_sum_succ _ m hm]
      exact up_step edge f x j c h3 h4 ⟨m, hm⟩ _ (ih (by omega))
  have hr := key r le_rfl
  simp only [Fin.is_lt, ite_true, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at hr
  have hb : ∀ b : Fin r, Finset.univ.filter (fun i => (b, i) ∈ up_P x j c r) = up_F x j c b := by
    intro b
    ext i
    simp [up_P, up_F]
  have h5' := h5 (up_P x j c r)
  simp only [hb] at h5'
  by_contra hcon
  apply h5'
  refine up_pack_le f _ ((Finset.univ.filter (fun a => f (up_query x j c a) (a, j a) ≠ up_gain edge x j a ∧
      c a = f (up_query x j c a) (a, j a))).card - (e + 1)) _ ?_
  convert hr using 1
  omega

theorem upper : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ r e s : Nat, s < r →
  let test := fun (n : Nat) (edge : Fin r → Fin n → Fin n → Bool)
      (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
      (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) =>
    let Y := Finset (Fin r × Fin n)
    let block := fun (y : Y) (a : Fin r) =>
      Finset.univ.filter (fun i : Fin n => (a,i) ∈ y)
    let alpha := fun a (u : Finset (Fin n)) =>
      (u.powerset.filter (fun z => ∀ i ∈ z, ∀ k ∈ z, edge a i k = false)).sup Finset.card
    let rank := fun (y : Y) => ∑ a : Fin r, alpha a (block y a)
    let pack := Nat.rec (motive := fun _ => Y → Prop) (fun _ => True)
      (fun _ prev y => ∃ (u v : Y) (k : Fin r × Fin n),
        prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u k = true ∧ f v k = false)
    let legal := (∀ a i, edge a i i = false) ∧ (∀ a i k, edge a i k = edge a k i) ∧
      (∀ y a i, ((a,i) ∉ y ∧ ∀ k ∈ block y a, edge a k i = false) →
        f y (a,i) = true) ∧ (∀ y a i, (a,i) ∈ y → f y (a,i) = false) ∧
      ∀ y, ¬ pack (rank y + e + 1) y
    let gain := fun a => decide (alpha a (insert (j a) (x a)) = alpha a (x a)+1)
    let query := fun (c : Fin r → Bool) (a : Fin r) =>
      (Finset.univ : Y).filter (fun p =>
        (p.1 < a ∧ (p.2 ∈ x p.1 ∨ (c p.1 = true ∧ p.2 = j p.1))) ∨
        (p.1 = a ∧ p.2 ∈ x a))
    let errors := fun c =>
      (Finset.univ.filter (fun a : Fin r => f (query c a) (a,j a) ≠ gain a)).card
    (legal, (Finset.univ.filter (fun c : Fin r → Bool => s < errors c)).card)
  let bound := 2^(r-s) * (∑ i ∈ Finset.range e, Nat.choose s i)
  ∀ n edge f x j, (test n edge f x j).1 → (test n edge f x j).2 ≤ bound) := by
  intro r e s hs test bound n edge f x j hl
  dsimp only [test, bound] at hl ⊢
  obtain ⟨-, -, h3, h4, h5⟩ := hl
  clear test
  have hq : ∀ a c c', (∀ b, b < a → c b = c' b) → up_query x j c a = up_query x j c' a := by
    intro a c c' hc
    unfold up_query
    refine Finset.filter_congr (fun p _ => ?_)
    by_cases hp : p.1 < a
    · simp [hp, hc _ hp]
    · simp [hp]
  have key := count_adapt r s e (fun a c => decide (f (up_query x j c a) (a, j a) ≠ up_gain edge x j a))
    (fun a c => f (up_query x j c a) (a, j a)) ?_ ?_ ?_
  · unfold up_query up_gain up_alpha at key
    simp only [decide_eq_true_eq] at key
    convert key
  · intro a c c' hc
    simp only [hq a c c' hc]
  · intro a c c' hc
    simp only [hq a c c' hc]
  · intro c
    simp only [decide_eq_true_eq]
    refine up_main e edge f x j (fun y a i hn hk => h3 y a i ⟨hn, fun k hk' => hk k (by simpa using hk')⟩)
      h4 ?_ c
    intro y hp
    apply h5 y
    show up_pack f (_ + e + 1) y
    unfold up_alpha at hp
    convert hp

def wi_D {r : ℕ} (y : Finset (Fin r × Fin 2)) : Finset (Fin r) :=
  Finset.univ.filter (fun a : Fin r => (a, 0) ∈ y ∧ (a, 1) ∈ y)

def wi_h {r : ℕ} (e : ℕ) (y : Finset (Fin r × Fin 2)) : ℕ :=
  (y.image Prod.fst).card + min e (wi_D y).card

theorem wi_D_mono {r : ℕ} {u v : Finset (Fin r × Fin 2)} (h : u ⊆ v) : wi_D u ⊆ wi_D v := by
  intro a
  simp only [wi_D, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun hh => ⟨h hh.1, h hh.2⟩

theorem wi_h_mono {r e : ℕ} {u v : Finset (Fin r × Fin 2)} (h : u ⊆ v) : wi_h e u ≤ wi_h e v := by
  unfold wi_h
  have h1 := Finset.card_le_card (Finset.image_subset_image (f := Prod.fst) h)
  have h2 := Finset.card_le_card (wi_D_mono h)
  omega

theorem wi_D_ins {r : ℕ} (y : Finset (Fin r × Fin 2)) (k : Fin r × Fin 2) :
    wi_D (insert k y) ⊆ insert k.1 (wi_D y) := by
  intro a
  simp only [wi_D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  rintro ⟨h0, h1⟩
  by_cases ha : a = k.1
  · exact Or.inl ha
  · right
    refine ⟨h0.resolve_left ?_, h1.resolve_left ?_⟩ <;> rintro rfl <;> exact ha rfl

theorem wi_D_new {r : ℕ} (y : Finset (Fin r × Fin 2)) (a : Fin r) (i : Fin 2)
    (ha : ∀ k, (a, k) ∉ y) : wi_D (insert (a, i) y) = wi_D y := by
  ext b
  simp only [wi_D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Prod.mk.injEq]
  constructor
  · rintro ⟨h0, h1⟩
    rcases h0 with ⟨rfl, h0⟩ | h0
    · rcases h1 with ⟨-, h1⟩ | h1
      · exact absurd (h0.trans h1.symm) (by decide)
      · exact absurd h1 (ha 1)
    · rcases h1 with ⟨rfl, -⟩ | h1
      · exact absurd h0 (ha 0)
      · exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨Or.inr h0, Or.inr h1⟩

theorem wi_h_ins {r e : ℕ} (y : Finset (Fin r × Fin 2)) (k : Fin r × Fin 2) :
    wi_h e (insert k y) ≤ wi_h e y + 1 := by
  unfold wi_h
  rw [Finset.image_insert]
  by_cases hk : k.1 ∈ y.image Prod.fst
  · rw [Finset.insert_eq_of_mem hk]
    have := (Finset.card_le_card (wi_D_ins y k)).trans (Finset.card_insert_le _ _)
    omega
  · obtain ⟨a, i⟩ := k
    rw [wi_D_new y a i (fun k hk' => hk (Finset.mem_image.2 ⟨_, hk', rfl⟩))]
    have := Finset.card_insert_le (a, i).1 (y.image Prod.fst)
    omega

theorem wi_h_new {r e : ℕ} (y : Finset (Fin r × Fin 2)) (a : Fin r) (i : Fin 2)
    (ha : ∀ k, (a, k) ∉ y) : wi_h e (insert (a, i) y) = wi_h e y + 1 := by
  have hn : a ∉ y.image Prod.fst := fun h => by
    obtain ⟨⟨b, k⟩, hk, rfl⟩ := Finset.mem_image.1 h
    exact ha k hk
  unfold wi_h
  simp only [wi_D_new y a i ha, Finset.image_insert, Finset.card_insert_of_notMem hn]
  omega

theorem wi_D_q {r : ℕ} (Q : Finset (Fin r × Fin 2)) (a : Fin r) (h0 : (a, 0) ∈ Q) :
    wi_D (insert (a, 1) Q) = insert a (wi_D Q) := by
  ext b
  simp only [wi_D, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Prod.mk.injEq]
  by_cases hb : b = a
  · subst hb
    simp [h0]
  · simp [hb]

theorem wi_h_q {r e : ℕ} (Q : Finset (Fin r × Fin 2)) (a : Fin r) (h0 : (a, 0) ∈ Q)
    (h1 : (a, 1) ∉ Q) : wi_h e (insert (a, 1) Q) = wi_h e Q + 1 ↔ (wi_D Q).card < e := by
  have hm : a ∉ wi_D Q := by simp [wi_D, h1]
  have hi : a ∈ Q.image Prod.fst := Finset.mem_image.2 ⟨_, h0, rfl⟩
  unfold wi_h
  rw [wi_D_q Q a h0, Finset.card_insert_of_notMem hm, Finset.image_insert, Finset.insert_eq_of_mem hi]
  omega

noncomputable def wi_pack {r : ℕ} (f : Finset (Fin r × Fin 2) → Fin r × Fin 2 → Bool) :
    ℕ → Finset (Fin r × Fin 2) → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin r × Fin 2) → Prop) (fun _ => True)
    (fun _ prev y => ∃ (u v : Finset (Fin r × Fin 2)) (k : Fin r × Fin 2),
      prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u k = true ∧ f v k = false)

theorem wi_pack_le {r e : ℕ} (f : Finset (Fin r × Fin 2) → Fin r × Fin 2 → Bool)
    (hf : ∀ y k, f y k = true ↔ wi_h e (insert k y) = wi_h e y + 1) :
    ∀ t y, wi_pack f t y → t ≤ wi_h e y := by
  intro t
  induction t with
  | zero => intros; omega
  | succ t ih =>
    rintro y ⟨u, v, k, hu, huv, hvy, hfu, hfv⟩
    have h1 := ih u hu
    have h2 := (hf u k).1 hfu
    have h3 : wi_h e (insert k v) ≠ wi_h e v + 1 := fun h => by simp [(hf v k).2 h] at hfv
    have h4 := wi_h_ins (e := e) v k
    have h5 := wi_h_mono (e := e) (Finset.subset_insert k v)
    have h6 := wi_h_mono (e := e) (Finset.insert_subset_insert k huv)
    have h7 := wi_h_mono (e := e) hvy
    omega

theorem wi_alpha_pos {β : Type*} (u : Finset β) (P : Finset β → Prop) [DecidablePred P] (i : β)
    (hi : i ∈ u) (hP : P {i}) : 1 ≤ (u.powerset.filter P).sup Finset.card := by
  have hm : ({i} : Finset β) ∈ u.powerset.filter P :=
    Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 hi), hP⟩
  simpa using Finset.le_sup (f := Finset.card) hm

theorem wi_alpha_le {β : Type*} (u : Finset β) (P : Finset β → Prop) [DecidablePred P]
    (hP : ∀ z, P z → z.card ≤ 1) : (u.powerset.filter P).sup Finset.card ≤ 1 :=
  Finset.sup_le (fun z hz => hP z (Finset.mem_filter.1 hz).2)

theorem wi_rank {r : ℕ} (y : Finset (Fin r × Fin 2)) (g : Fin r → ℕ)
    (hg : ∀ a i, (a, i) ∈ y → 1 ≤ g a) : (y.image Prod.fst).card ≤ ∑ a, g a := by
  rw [Finset.card_eq_sum_ones]
  calc ∑ a ∈ y.image Prod.fst, 1 ≤ ∑ a ∈ y.image Prod.fst, g a :=
        Finset.sum_le_sum (fun a ha => by
          obtain ⟨⟨b, i⟩, hb, rfl⟩ := Finset.mem_image.1 ha
          exact hg b i hb)
    _ ≤ ∑ a, g a := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def wi_N {r : ℕ} (c : Fin r → Bool) (a : Fin r) : ℕ :=
  (Finset.univ.filter (fun b => b < a ∧ c b = true)).card

theorem wi_N_mono {r : ℕ} (c : Fin r → Bool) {a a' : Fin r} (h : a ≤ a') : wi_N c a ≤ wi_N c a' :=
  Finset.card_le_card (fun b => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun hb => ⟨lt_of_lt_of_le hb.1 h, hb.2⟩)

theorem wi_err {r s e : ℕ} (hs : s < r) (c : Fin r → Bool) :
    s < (Finset.univ.filter (fun a => wi_N c a < e)).card ↔ wi_N c ⟨s, hs⟩ < e := by
  constructor
  · intro h
    by_contra hn
    have hsub : Finset.univ.filter (fun a => wi_N c a < e) ⊆ Finset.Iio ⟨s, hs⟩ := by
      intro a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      intro ha
      by_contra hle
      have := wi_N_mono c (not_lt.1 hle)
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    simp only at this
    omega
  · intro h
    have hsub : Finset.Iic (⟨s, hs⟩ : Fin r) ⊆ Finset.univ.filter (fun a => wi_N c a < e) := by
      intro a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
      intro ha
      have := wi_N_mono c ha
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    simp only at this
    omega

theorem wi_cnt_pow {α : Type*} [DecidableEq α] (L : Finset α) (e : ℕ) :
    (L.powerset.filter (fun T => T.card < e)).card = ∑ i ∈ Finset.range e, L.card.choose i := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, ← ih, ← Finset.card_powersetCard, Finset.powersetCard_eq_filter,
      ← Finset.card_union_of_disjoint, ← Finset.filter_or]
    · congr 1
      apply Finset.filter_congr
      intro T _
      omega
    · rw [Finset.disjoint_filter]
      intro T _ h1 h2
      omega

theorem wi_un {α : Type*} [Fintype α] [DecidableEq α] {L T R : Finset α} (hT : T ⊆ L)
    (hR : R ⊆ Lᶜ) : (T ∪ R) ∩ L = T ∧ (T ∪ R) ∩ Lᶜ = R := by
  constructor <;> ext x <;> have h1 := @hT x <;> have h2 := @hR x <;>
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_compl] at h1 h2 ⊢ <;> tauto

theorem wi_cnt_fin {α : Type*} [Fintype α] [DecidableEq α] (L : Finset α) (e : ℕ) :
    (Finset.univ.filter (fun S : Finset α => (S ∩ L).card < e)).card =
      2 ^ (Fintype.card α - L.card) * ∑ i ∈ Finset.range e, L.card.choose i := by
  rw [← wi_cnt_pow L e, mul_comm, ← Finset.card_compl, ← Finset.card_powerset Lᶜ,
    ← Finset.card_product]
  apply Finset.card_nbij' (fun S => (S ∩ L, S ∩ Lᶜ)) (fun p => p.1 ∪ p.2)
  · intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨Finset.inter_subset_right, hS⟩, Finset.inter_subset_right⟩
  · rintro ⟨T, R⟩ hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [(wi_un hp.1.1 hp.2).1]
    exact hp.1.2
  · intro S _
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]
    tauto
  · rintro ⟨T, R⟩ hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp
    simp only [(wi_un hp.1.1 hp.2).1, (wi_un hp.1.1 hp.2).2]

theorem wi_cnt {r s e : ℕ} (hs : s < r) :
    (Finset.univ.filter (fun c : Fin r → Bool => wi_N c ⟨s, hs⟩ < e)).card =
      2 ^ (r - s) * ∑ i ∈ Finset.range e, s.choose i := by
  have hL : (Finset.Iio (⟨s, hs⟩ : Fin r)).card = s := by simp
  have h := wi_cnt_fin (Finset.Iio (⟨s, hs⟩ : Fin r)) e
  rw [hL, Fintype.card_fin] at h
  rw [← h]
  apply Finset.card_nbij' (fun c => Finset.univ.filter (fun b => c b = true))
    (fun S b => decide (b ∈ S))
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter] at hc
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h2 := hc.2
    unfold wi_N at h2
    convert h2 using 2
    ext b
    simp [and_comm]
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter] at hS
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold wi_N
    convert hS.2 using 2
    ext b
    simp [and_comm]
  · intro c _
    funext b
    simp
  · intro S _
    ext b
    simp

theorem wi_ne2 (b : Bool) (A B : ℕ) [Decidable (A = B + 1)] (hA : A ≤ 1) (hB : 1 ≤ B) :
    (b ≠ decide (A = B + 1)) ↔ b = true := by
  have : ¬ (A = B + 1) := by omega
  simp [this]

theorem witness : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ r e s : Nat, s < r →
  let test := fun (n : Nat) (edge : Fin r → Fin n → Fin n → Bool)
      (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
      (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) =>
    let Y := Finset (Fin r × Fin n)
    let block := fun (y : Y) (a : Fin r) =>
      Finset.univ.filter (fun i : Fin n => (a,i) ∈ y)
    let alpha := fun a (u : Finset (Fin n)) =>
      (u.powerset.filter (fun z => ∀ i ∈ z, ∀ k ∈ z, edge a i k = false)).sup Finset.card
    let rank := fun (y : Y) => ∑ a : Fin r, alpha a (block y a)
    let pack := Nat.rec (motive := fun _ => Y → Prop) (fun _ => True)
      (fun _ prev y => ∃ (u v : Y) (k : Fin r × Fin n),
        prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u k = true ∧ f v k = false)
    let legal := (∀ a i, edge a i i = false) ∧ (∀ a i k, edge a i k = edge a k i) ∧
      (∀ y a i, ((a,i) ∉ y ∧ ∀ k ∈ block y a, edge a k i = false) →
        f y (a,i) = true) ∧ (∀ y a i, (a,i) ∈ y → f y (a,i) = false) ∧
      ∀ y, ¬ pack (rank y + e + 1) y
    let gain := fun a => decide (alpha a (insert (j a) (x a)) = alpha a (x a)+1)
    let query := fun (c : Fin r → Bool) (a : Fin r) =>
      (Finset.univ : Y).filter (fun p =>
        (p.1 < a ∧ (p.2 ∈ x p.1 ∨ (c p.1 = true ∧ p.2 = j p.1))) ∨
        (p.1 = a ∧ p.2 ∈ x a))
    let errors := fun c =>
      (Finset.univ.filter (fun a : Fin r => f (query c a) (a,j a) ≠ gain a)).card
    (legal, (Finset.univ.filter (fun c : Fin r → Bool => s < errors c)).card)
  let bound := 2^(r-s) * (∑ i ∈ Finset.range e, Nat.choose s i)
  let height := fun (y : Finset (Fin r × Fin 2)) =>
    (y.image Prod.fst).card +
      min e (Finset.univ.filter (fun a : Fin r => (a,0) ∈ y ∧ (a,1) ∈ y)).card
  let f := fun y j => decide (height (insert j y) = height y + 1)
  let witness := test 2 (fun _ i k => decide (i ≠ k)) f (fun _ => {0}) (fun _ => 1)
  witness.1 ∧ witness.2 = bound) := by
  intro r e s hs test bound height f witness
  have hh : ∀ y, height y = wi_h e y := by
    intro y
    simp only [height, wi_h, wi_D]
    congr
    exact Subsingleton.elim _ _
  have hf : ∀ y k, f y k = true ↔ wi_h e (insert k y) = wi_h e y + 1 := by
    intro y k
    simp only [f, decide_eq_true_iff, hh]
    convert Iff.rfl
  simp only [witness, test]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a i
    simp
  · intro a i k
    simp [eq_comm]
  · rintro y a i ⟨h1, h2⟩
    rw [hf]
    apply wi_h_new
    intro k hk
    have := h2 k (by simp [hk])
    simp at this
    subst this
    exact h1 hk
  · intro y a i h
    have : ¬ (f y (a, i) = true) := by
      rw [hf, Finset.insert_eq_of_mem h]
      omega
    simpa using this
  · intro y hp
    have h1 := wi_pack_le f hf (_ + e + 1) y hp
    refine absurd h1 (not_le.2 (lt_of_le_of_lt (b := (y.image Prod.fst).card + e) ?_ ?_))
    · unfold wi_h
      omega
    · apply Nat.lt_succ_of_le
      apply Nat.add_le_add_right
      apply wi_rank
      intro a i hai
      apply wi_alpha_pos _ _ i
      · simp [hai]
      · simp
  · show _ = 2 ^ (r - s) * ∑ i ∈ Finset.range e, s.choose i
    rw [← wi_cnt hs]
    apply congrArg Finset.card
    ext c
    rw [Finset.mem_filter, Finset.mem_filter, ← wi_err hs c]
    simp only [Finset.mem_univ, true_and]
    apply iff_of_eq
    apply congrArg (s < ·)
    apply congrArg Finset.card
    ext a
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [wi_ne2]
    · rw [hf, wi_h_q _ a (by simp) (by simp)]
      unfold wi_D wi_N
      apply iff_of_eq
      congr 2
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp
      exact fun h _ => Or.inl h
    · apply wi_alpha_le
      intro z hz
      exact Finset.card_le_one.2 (fun i hi k hk => by simpa using hz i hi k hk)
    · exact wi_alpha_pos _ _ 0 (by simp) (by simp)

end PEqualNP.Outside.L_meta_48147_aux

theorem PEqualNP.Outside.L_meta_48147 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ r e s : Nat, s < r →
  let test := fun (n : Nat) (edge : Fin r → Fin n → Fin n → Bool)
      (f : Finset (Fin r × Fin n) → Fin r × Fin n → Bool)
      (x : Fin r → Finset (Fin n)) (j : Fin r → Fin n) =>
    let Y := Finset (Fin r × Fin n)
    let block := fun (y : Y) (a : Fin r) =>
      Finset.univ.filter (fun i : Fin n => (a,i) ∈ y)
    let alpha := fun a (u : Finset (Fin n)) =>
      (u.powerset.filter (fun z => ∀ i ∈ z, ∀ k ∈ z, edge a i k = false)).sup Finset.card
    let rank := fun (y : Y) => ∑ a : Fin r, alpha a (block y a)
    let pack := Nat.rec (motive := fun _ => Y → Prop) (fun _ => True)
      (fun _ prev y => ∃ (u v : Y) (k : Fin r × Fin n),
        prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u k = true ∧ f v k = false)
    let legal := (∀ a i, edge a i i = false) ∧ (∀ a i k, edge a i k = edge a k i) ∧
      (∀ y a i, ((a,i) ∉ y ∧ ∀ k ∈ block y a, edge a k i = false) →
        f y (a,i) = true) ∧ (∀ y a i, (a,i) ∈ y → f y (a,i) = false) ∧
      ∀ y, ¬ pack (rank y + e + 1) y
    let gain := fun a => decide (alpha a (insert (j a) (x a)) = alpha a (x a)+1)
    let query := fun (c : Fin r → Bool) (a : Fin r) =>
      (Finset.univ : Y).filter (fun p =>
        (p.1 < a ∧ (p.2 ∈ x p.1 ∨ (c p.1 = true ∧ p.2 = j p.1))) ∨
        (p.1 = a ∧ p.2 ∈ x a))
    let errors := fun c =>
      (Finset.univ.filter (fun a : Fin r => f (query c a) (a,j a) ≠ gain a)).card
    (legal, (Finset.univ.filter (fun c : Fin r → Bool => s < errors c)).card)
  let bound := 2^(r-s) * (∑ i ∈ Finset.range e, Nat.choose s i)
  (∀ n edge f x j, (test n edge f x j).1 → (test n edge f x j).2 ≤ bound) ∧
  let height := fun (y : Finset (Fin r × Fin 2)) =>
    (y.image Prod.fst).card +
      min e (Finset.univ.filter (fun a : Fin r => (a,0) ∈ y ∧ (a,1) ∈ y)).card
  let f := fun y j => decide (height (insert j y) = height y + 1)
  let witness := test 2 (fun _ i k => decide (i ≠ k)) f (fun _ => {0}) (fun _ => 1)
  witness.1 ∧ witness.2 = bound) := by
  intro r e s hs
  exact ⟨PEqualNP.Outside.L_meta_48147_aux.upper r e s hs, PEqualNP.Outside.L_meta_48147_aux.witness r e s hs⟩
