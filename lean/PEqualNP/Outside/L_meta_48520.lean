import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48520

def step {n : ℕ} (u v : Finset (Fin n)) : Prop :=
  ∃ i : Fin n, i ∉ u ∧ v = insert i u

def adj {n : ℕ} (u v : Finset (Fin n)) : Prop :=
  step u v ∨ step v u

def wcost {n : ℕ} (r : Finset (Fin n) → ℕ) {l : ℕ} (p : Fin (l + 1) → Finset (Fin n)) : ℕ :=
  Finset.univ.sum (fun i : Fin l => r (p i.succ) - r (p i.castSucc))

lemma sum_telescope_int {l : ℕ} (g : Fin (l + 1) → ℤ) :
    Finset.univ.sum (fun i : Fin l => g i.castSucc - g i.succ) = g 0 - g (Fin.last l) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun k => g k.castSucc)
    simp only [Fin.castSucc_zero] at hih
    have h1 : (∑ i : Fin l, (g i.castSucc.castSucc - g i.castSucc.succ)) = g 0 - g (Fin.last l).castSucc := by
      convert hih using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.succ_castSucc]
    rw [h1, Fin.succ_last]
    ring

lemma sum_telescope_nat_mono {l : ℕ} (g : Fin (l + 1) → ℕ)
    (hmono : ∀ i : Fin l, g i.castSucc ≤ g i.succ) :
    Finset.univ.sum (fun i : Fin l => g i.succ - g i.castSucc) = g (Fin.last l) - g 0 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    have hmono' : ∀ i : Fin l, g i.castSucc.castSucc ≤ g i.succ.castSucc := fun i => by
      rw [← Fin.succ_castSucc]
      exact hmono i.castSucc
    have hih := ih (fun k => g k.castSucc) hmono'
    simp only [Fin.castSucc_zero] at hih
    have h1 : (∑ i : Fin l, (g i.castSucc.succ - g i.castSucc.castSucc)) = g (Fin.last l).castSucc - g 0 := by
      convert hih using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.succ_castSucc]
    rw [h1]
    have h0_le : g 0 ≤ g (Fin.last l).castSucc := by
      have hgen : ∀ k : Fin (l + 1), g 0 ≤ g k.castSucc := by
        intro k
        induction k using Fin.induction with
        | zero => simp
        | succ k ihk => exact ihk.trans (hmono k.castSucc)
      exact hgen (Fin.last l)
    have hlast_le : g (Fin.last l).castSucc ≤ g (Fin.last l.succ) := by
      have := hmono (Fin.last l)
      rwa [Fin.succ_last] at this
    rw [Fin.succ_last]
    change g (Fin.last l).castSucc - g 0 + (g (Fin.last l.succ) - g (Fin.last l).castSucc) = g (Fin.last l.succ) - g 0
    omega

lemma forward_dir {n t D : ℕ} (P Z : Finset (Fin n) → Fin t → Prop) (B : Finset (Fin n) → ℕ)
    (hf : ∃ f : Finset (Fin n) → Fin t → ℕ,
      (∀ x j, f x j ≤ D) ∧ (∀ x j, P x j → f x j = D) ∧
      (∀ x j, Z x j → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j) ∧
      ∀ (l : ℕ) (p : Fin (l + 1) → Finset (Fin n)) (a : Fin l → Fin t),
        (∀ i : Fin l, p i.castSucc ⊆ p i.succ) →
        (Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i))) ≤
          B (p (Fin.last l))) :
    ∃ r : Finset (Fin n) → ℕ,
      r ∅ = 0 ∧ (∀ x, r x ≤ B x) ∧ (∀ x y, x ⊆ y → r x ≤ r y) ∧
      ∀ (j : Fin t) (l : ℕ) (p : Fin (l + 1) → Finset (Fin n)),
        l < 2 ^ n → Function.Injective p →
        P (p 0) j → Z (p (Fin.last l)) j →
        (∀ i : Fin l, step (p i.castSucc) (p i.succ) ∨ step (p i.succ) (p i.castSucc)) →
        D ≤ Finset.univ.sum (fun i : Fin l => r (p i.succ) - r (p i.castSucc)) := by
  by_cases ht : t = 0
  · subst ht
    refine ⟨fun _ => 0, rfl, fun _ => Nat.zero_le _, fun _ _ _ => le_refl 0, fun j => j.elim0⟩
  obtain ⟨f, hfle, hfP, hfZ, hfanti, hfbudget⟩ := hf
  let S (x : Finset (Fin n)) : Set ℕ :=
    { c : ℕ | ∃ (l : ℕ) (p : Fin (l + 1) → Finset (Fin n)) (a : Fin l → Fin t),
      (∀ i : Fin l, p i.castSucc ⊆ p i.succ) ∧ p (Fin.last l) = x ∧
      c = Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i)) }
  have hSne : ∀ x, (S x).Nonempty := fun x =>
    ⟨0, 0, fun _ => x, fun i => i.elim0, fun i => i.elim0, rfl, by simp⟩
  have hSbdd : ∀ x, BddAbove (S x) := by
    intro x
    refine ⟨B x, ?_⟩
    rintro c ⟨l, p, a, hsub, hlast, rfl⟩
    rw [← hlast]
    exact hfbudget l p a hsub
  let r (x : Finset (Fin n)) : ℕ := sSup (S x)
  have hr_mem : ∀ x, r x ∈ S x := fun x => Nat.sSup_mem (hSne x) (hSbdd x)
  have hr_le_B : ∀ x, r x ≤ B x := fun x => csSup_le (hSne x) (by
    rintro c ⟨l, p, a, hsub, hlast, rfl⟩
    rw [← hlast]
    exact hfbudget l p a hsub)
  have hr_empty : r ∅ = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply csSup_le (hSne ∅)
    rintro c ⟨l, p, a, hsub, hlast, rfl⟩
    have hall : ∀ k : Fin (l + 1), p k = ∅ := by
      have hsub_last : ∀ k : Fin (l + 1), p k ⊆ p (Fin.last l) := by
        intro k
        have hstep : ∀ d : ℕ, ∀ k : Fin (l + 1), k.val + d = l → p k ⊆ p (Fin.last l) := by
          intro d
          induction d with
          | zero =>
            intro k hk
            have : k = Fin.last l := Fin.ext hk
            rw [this]
          | succ d ih =>
            intro k hk
            have hk_lt : k.val < l := by omega
            let k' : Fin l := ⟨k.val, hk_lt⟩
            have h1 : p k ⊆ p k'.succ := by
              have : k'.castSucc = k := Fin.ext rfl
              rw [← this]
              exact hsub k'
            exact h1.trans (ih k'.succ (by simp [k']; omega))
        exact hstep (l - k.val) k (by omega)
      intro k
      exact Finset.subset_empty.mp (hlast ▸ hsub_last k)
    simp [hall]
  have hr_step : ∀ x y : Finset (Fin n), x ⊆ y → ∀ j : Fin t, r x + (f x j - f y j) ≤ r y := by
    intro x y hxy j
    obtain ⟨l, p, a, hsub, hlast, hsum⟩ := hr_mem x
    let p' : Fin (l + 2) → Finset (Fin n) := Fin.snoc p y
    let a' : Fin (l + 1) → Fin t := Fin.snoc a j
    have hsub' : ∀ i : Fin (l + 1), p' i.castSucc ⊆ p' i.succ := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [p', Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last]
        rw [hlast]
        exact hxy
      · intro k
        simp only [p', Fin.succ_castSucc, Fin.snoc_castSucc]
        exact hsub k
    have hlast' : p' (Fin.last (l + 1)) = y := by simp [p']
    have hsum' : Finset.univ.sum (fun i : Fin (l + 1) => f (p' i.castSucc) (a' i) - f (p' i.succ) (a' i)) =
        r x + (f x j - f y j) := by
      rw [Fin.sum_univ_castSucc]
      have h1 : Finset.univ.sum (fun i : Fin l => f (p' i.castSucc.castSucc) (a' i.castSucc) - f (p' i.castSucc.succ) (a' i.castSucc)) =
          Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [p', a', Fin.succ_castSucc, Fin.snoc_castSucc]
      rw [h1, ← hsum]
      simp only [p', a', Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last, hlast]
    exact le_csSup (hSbdd y) ⟨l + 1, p', a', hsub', hlast', hsum'.symm⟩
  have hr_mono : ∀ x y : Finset (Fin n), x ⊆ y → r x ≤ r y := by
    intro x y hxy
    have h0 := hr_step x y hxy ⟨0, Nat.pos_of_ne_zero ht⟩
    omega
  refine ⟨r, hr_empty, hr_le_B, hr_mono, ?_⟩
  intro j l p _ _ hP hZ hadj
  have hedge : ∀ i : Fin l, (f (p i.castSucc) j : ℤ) - (f (p i.succ) j : ℤ) ≤
      ((r (p i.succ) - r (p i.castSucc) : ℕ) : ℤ) := by
    intro i
    rcases hadj i with ⟨k, _, hk⟩ | ⟨k, _, hk⟩
    · have hsub : p i.castSucc ⊆ p i.succ := by rw [hk]; exact Finset.subset_insert k _
      have h1 := hr_step (p i.castSucc) (p i.succ) hsub j
      have h2 := hfanti (p i.castSucc) (p i.succ) hsub j
      have h3 := hr_mono (p i.castSucc) (p i.succ) hsub
      omega
    · have hsub : p i.succ ⊆ p i.castSucc := by rw [hk]; exact Finset.subset_insert k _
      have h2 := hfanti (p i.succ) (p i.castSucc) hsub j
      omega
  have hsum_int : (D : ℤ) ≤ ∑ i : Fin l, ((r (p i.succ) - r (p i.castSucc) : ℕ) : ℤ) := by
    have htel := sum_telescope_int (fun k : Fin (l + 1) => (f (p k) j : ℤ))
    rw [hfP (p 0) j hP, hfZ (p (Fin.last l)) j hZ] at htel
    calc (D : ℤ) = (D : ℤ) - (0 : ℕ) := by simp
      _ = ∑ i : Fin l, ((f (p i.castSucc) j : ℤ) - (f (p i.succ) j : ℤ)) := htel.symm
      _ ≤ ∑ i : Fin l, ((r (p i.succ) - r (p i.castSucc) : ℕ) : ℤ) := Finset.sum_le_sum fun i _ => hedge i
  exact_mod_cast hsum_int

lemma remove_loops {n : ℕ} (r : Finset (Fin n) → ℕ) :
    ∀ (l : ℕ) (p : Fin (l + 1) → Finset (Fin n)),
      (∀ i : Fin l, adj (p i.castSucc) (p i.succ)) →
      ∃ (l' : ℕ) (p' : Fin (l' + 1) → Finset (Fin n)),
        l' < 2 ^ n ∧ Function.Injective p' ∧
        (∀ i : Fin l', adj (p' i.castSucc) (p' i.succ)) ∧
        p' 0 = p 0 ∧ p' (Fin.last l') = p (Fin.last l) ∧
        wcost r p' ≤ wcost r p := by
  intro l
  induction l using Nat.strong_induction_on with
  | ind l ih =>
    intro p hadj
    by_cases hinj : Function.Injective p
    · have hcard : l + 1 ≤ 2 ^ n := by
        have h1 := Fintype.card_le_of_injective p hinj
        simp [Fintype.card_fin] at h1
        exact h1
      exact ⟨l, p, by omega, hinj, hadj, rfl, rfl, le_refl _⟩
    · simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i1, i2, heq, hne⟩ := hinj
      have hpair : ∃ a b : Fin (l + 1), a.val < b.val ∧ p a = p b := by
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
        · exact ⟨i1, i2, hlt, heq⟩
        · exact ⟨i2, i1, hgt, heq.symm⟩
      obtain ⟨a, b, hab, hpab⟩ := hpair
      let d := b.val - a.val
      have hd_pos : 0 < d := by omega
      have hd_le : d ≤ l := by omega
      let l1 := l - d
      have hl1_lt : l1 < l := by omega
      let idx : Fin (l1 + 1) → Fin (l + 1) := fun k =>
        if h : k.val ≤ a.val then ⟨k.val, by omega⟩
        else ⟨k.val + d, by omega⟩
      let q : Fin (l1 + 1) → Finset (Fin n) := fun k => p (idx k)
      have hq0 : q 0 = p 0 := by
        simp [q, idx]
      have hqlast : q (Fin.last l1) = p (Fin.last l) := by
        simp only [q, idx, Fin.val_last]
        split_ifs with h
        · have ha_eq : a.val = l1 := by omega
          have hb_eq : b = Fin.last l := Fin.ext (by dsimp only [Fin.val_last]; omega)
          have h1 : (⟨l1, by omega⟩ : Fin (l + 1)) = a := Fin.ext ha_eq.symm
          rw [h1, hpab, hb_eq]
        · congr 1
          exact Fin.ext (by dsimp only [Fin.val_last]; omega)
      have hq_edge : ∀ i : Fin l1,
          ∃ j : Fin l, (q i.castSucc = p j.castSucc ∧ q i.succ = p j.succ) ∧
            j.val = if i.val < a.val then i.val else i.val + d := by
        intro i
        by_cases hi : i.val < a.val
        · refine ⟨⟨i.val, by omega⟩, ⟨?_, ?_⟩, by simp [hi]⟩
          · simp only [q, idx, Fin.val_castSucc, show i.val ≤ a.val by omega, dite_true]; rfl
          · simp only [q, idx, Fin.val_succ, show i.val + 1 ≤ a.val by omega, dite_true]; rfl
        · refine ⟨⟨i.val + d, by omega⟩, ⟨?_, ?_⟩, by simp [hi]⟩
          · simp only [q, idx, Fin.val_castSucc]
            split_ifs with h
            · have hia : i.val = a.val := by omega
              have h1 : (⟨i.val, by omega⟩ : Fin (l + 1)) = a := Fin.ext hia
              rw [h1, hpab]
              congr 1; exact Fin.ext (by dsimp only [Fin.val_castSucc]; omega)
            · rfl
          · simp only [q, idx, Fin.val_succ, show ¬ (i.val + 1 ≤ a.val) by omega, dite_false]
            congr 1; exact Fin.ext (by dsimp only [Fin.val_succ]; omega)
      have hq_adj : ∀ i : Fin l1, adj (q i.castSucc) (q i.succ) := by
        intro i
        obtain ⟨j, ⟨h1, h2⟩, _⟩ := hq_edge i
        rw [h1, h2]
        exact hadj j
      have hq_cost : wcost r q ≤ wcost r p := by
        let emb : Fin l1 → Fin l := fun i =>
          if h : i.val < a.val then ⟨i.val, by omega⟩ else ⟨i.val + d, by omega⟩
        have hemb_inj : Function.Injective emb := by
          intro x y hxy
          have hv := congrArg Fin.val hxy
          simp only [emb] at hv
          split_ifs at hv <;> (dsimp only at hv; exact Fin.ext (by omega))
        have hterm : ∀ i : Fin l1, r (q i.succ) - r (q i.castSucc) = r (p (emb i).succ) - r (p (emb i).castSucc) := by
          intro i
          obtain ⟨j, ⟨h1, h2⟩, hj⟩ := hq_edge i
          have hjeq : j = emb i := Fin.ext (by simp [emb]; split_ifs at hj ⊢ <;> omega)
          rw [h1, h2, hjeq]
        calc wcost r q
            = ∑ i : Fin l1, (r (p (emb i).succ) - r (p (emb i).castSucc)) := Finset.sum_congr rfl fun i _ => hterm i
          _ = ∑ j ∈ Finset.univ.image emb, (r (p j.succ) - r (p j.castSucc)) :=
              (Finset.sum_image (f := fun j : Fin l => r (p j.succ) - r (p j.castSucc)) (fun x _ y _ h => hemb_inj h)).symm
          _ ≤ ∑ j : Fin l, (r (p j.succ) - r (p j.castSucc)) :=
              Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      obtain ⟨l', p', hl', hinj', hadj', hp'0, hp'last, hcost'⟩ := ih l1 hl1_lt q hq_adj
      exact ⟨l', p', hl', hinj', hadj', hp'0.trans hq0, hp'last.trans hqlast, hcost'.trans hq_cost⟩

lemma backward_dir {n t D : ℕ} (P Z : Finset (Fin n) → Fin t → Prop) (B : Finset (Fin n) → ℕ)
    (hr : ∃ r : Finset (Fin n) → ℕ,
      r ∅ = 0 ∧ (∀ x, r x ≤ B x) ∧ (∀ x y, x ⊆ y → r x ≤ r y) ∧
      ∀ (j : Fin t) (l : ℕ) (p : Fin (l + 1) → Finset (Fin n)),
        l < 2 ^ n → Function.Injective p →
        P (p 0) j → Z (p (Fin.last l)) j →
        (∀ i : Fin l, step (p i.castSucc) (p i.succ) ∨ step (p i.succ) (p i.castSucc)) →
        D ≤ Finset.univ.sum (fun i : Fin l => r (p i.succ) - r (p i.castSucc))) :
    ∃ f : Finset (Fin n) → Fin t → ℕ,
      (∀ x j, f x j ≤ D) ∧ (∀ x j, P x j → f x j = D) ∧
      (∀ x j, Z x j → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j) ∧
      ∀ (l : ℕ) (p : Fin (l + 1) → Finset (Fin n)) (a : Fin l → Fin t),
        (∀ i : Fin l, p i.castSucc ⊆ p i.succ) →
        (Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i))) ≤
          B (p (Fin.last l)) := by
  classical
  obtain ⟨r, _, hrB, hrmono, hrwalk⟩ := hr
  let W (x : Finset (Fin n)) (j : Fin t) : Set ℕ :=
    { c : ℕ | ∃ (l : ℕ) (p : Fin (l + 1) → Finset (Fin n)),
      (∀ i : Fin l, adj (p i.castSucc) (p i.succ)) ∧
      p 0 = x ∧ Z (p (Fin.last l)) j ∧ c = wcost r p }
  let f (x : Finset (Fin n)) (j : Fin t) : ℕ :=
    if (W x j).Nonempty then min D (sInf (W x j)) else D
  have hfle : ∀ x j, f x j ≤ D := by
    intro x j
    simp only [f]
    split_ifs
    · exact min_le_left _ _
    · exact le_refl D
  have hfP : ∀ x j, P x j → f x j = D := by
    intro x j hP
    simp only [f]
    split_ifs with hne
    · have hmem : sInf (W x j) ∈ W x j := Nat.sInf_mem hne
      obtain ⟨l, p, hadj, hp0, hpZ, hcost⟩ := hmem
      obtain ⟨l', p', hl', hinj', hadj', hp'0, hp'last, hcost'⟩ := remove_loops r l p hadj
      have hDle : D ≤ wcost r p' := hrwalk j l' p' hl' hinj' (by rw [hp'0, hp0]; exact hP)
        (by rw [hp'last]; exact hpZ) hadj'
      have hDle2 : D ≤ sInf (W x j) := by omega
      exact min_eq_left hDle2
    · rfl
  have hfZ : ∀ x j, Z x j → f x j = 0 := by
    intro x j hZ
    have h0 : 0 ∈ W x j := ⟨0, fun _ => x, fun i => i.elim0, rfl, hZ, by simp [wcost]⟩
    have hne : (W x j).Nonempty := ⟨0, h0⟩
    have hinf0 : sInf (W x j) = 0 := Nat.eq_zero_of_le_zero (Nat.sInf_le h0)
    simp only [f, hne, ite_true, hinf0, Nat.min_zero]
  have htri : ∀ u v : Finset (Fin n), adj u v → ∀ j : Fin t, f u j ≤ f v j + (r v - r u) := by
    intro u v huv j
    by_cases hnev : (W v j).Nonempty
    · have hmem : sInf (W v j) ∈ W v j := Nat.sInf_mem hnev
      obtain ⟨l, p, hadj, hp0, hpZ, hcost⟩ := hmem
      let p' : Fin (l + 2) → Finset (Fin n) := Fin.cons u p
      have hadj' : ∀ i : Fin (l + 1), adj (p' i.castSucc) (p' i.succ) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · simp only [p', Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_zero, Fin.cons_one, hp0]
          exact huv
        · intro k
          simp only [p', Fin.castSucc_succ, Fin.cons_succ]
          exact hadj k
      have hcost' : wcost r p' = (r v - r u) + wcost r p := by
        simp only [wcost]
        rw [Fin.sum_univ_succ]
        simp only [p', Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.cons_zero, Fin.cons_one, hp0,
          Fin.castSucc_succ, Fin.cons_succ]
      have hmem_u : (r v - r u) + sInf (W v j) ∈ W u j :=
        ⟨l + 1, p', hadj', rfl, by simpa [p'] using hpZ, by rw [hcost', hcost]⟩
      have hneu : (W u j).Nonempty := ⟨_, hmem_u⟩
      have hle_inf : sInf (W u j) ≤ (r v - r u) + sInf (W v j) := Nat.sInf_le hmem_u
      simp only [f, hneu, hnev, ite_true]
      omega
    · simp only [f, hnev, ite_false]
      have := hfle u j
      simp only [f] at this
      omega
  have hsub_bounds : ∀ (k : ℕ) (x y : Finset (Fin n)), x ⊆ y → (y \ x).card = k →
      ∀ j : Fin t, f y j ≤ f x j ∧ f x j - f y j ≤ r y - r x := by
    intro k
    induction k with
    | zero =>
      intro x y hxy hcard j
      have heq : x = y := by
        have h1 : y \ x = ∅ := Finset.card_eq_zero.mp hcard
        exact Finset.Subset.antisymm hxy (Finset.sdiff_eq_empty_iff_subset.mp h1)
      subst heq
      exact ⟨le_refl _, by simp⟩
    | succ k ih =>
      intro x y hxy hcard j
      have hne : (y \ x).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i, hi⟩ := hne
      have hiy : i ∈ y := (Finset.mem_sdiff.mp hi).1
      have hix : i ∉ x := (Finset.mem_sdiff.mp hi).2
      let x' := insert i x
      have hx'y : x' ⊆ y := Finset.insert_subset_iff.mpr ⟨hiy, hxy⟩
      have hcard' : (y \ x').card = k := by
        have h1 : y \ x' = (y \ x).erase i := by
          ext z; simp only [Finset.mem_sdiff, Finset.mem_erase, x', Finset.mem_insert]
          tauto
        rw [h1, Finset.card_erase_of_mem hi, hcard]
        omega
      obtain ⟨hanti', hdrop'⟩ := ih x' y hx'y hcard' j
      have hst : step x x' := ⟨i, hix, rfl⟩
      have h1 : f x' j ≤ f x j + (r x - r x') := htri x' x (Or.inr hst) j
      have h2 : f x j ≤ f x' j + (r x' - r x) := htri x x' (Or.inl hst) j
      have hr1 : r x ≤ r x' := hrmono x x' (Finset.subset_insert i x)
      have hr2 : r x' ≤ r y := hrmono x' y hx'y
      refine ⟨by omega, by omega⟩
  have hfanti : ∀ x y : Finset (Fin n), x ⊆ y → ∀ j : Fin t, f y j ≤ f x j :=
    fun x y hxy j => (hsub_bounds (y \ x).card x y hxy rfl j).1
  have hdrop : ∀ x y : Finset (Fin n), x ⊆ y → ∀ j : Fin t, f x j - f y j ≤ r y - r x :=
    fun x y hxy j => (hsub_bounds (y \ x).card x y hxy rfl j).2
  refine ⟨f, hfle, hfP, hfZ, hfanti, ?_⟩
  intro l p a hsub
  calc Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i))
      ≤ Finset.univ.sum (fun i : Fin l => r (p i.succ) - r (p i.castSucc)) :=
        Finset.sum_le_sum fun i _ => hdrop (p i.castSucc) (p i.succ) (hsub i) (a i)
    _ = r (p (Fin.last l)) - r (p 0) :=
        sum_telescope_nat_mono (fun k => r (p k)) (fun i => hrmono _ _ (hsub i))
    _ ≤ r (p (Fin.last l)) := Nat.sub_le _ _
    _ ≤ B (p (Fin.last l)) := hrB (p (Fin.last l))

end PEqualNP.Outside.L_meta_48520

theorem PEqualNP.Outside.L_meta_48520 : (∀ (n t D : Nat),
  let X := Finset (Fin n)
  let step := fun (u v : X) => ∃ i : Fin n, i ∉ u ∧ v = insert i u
  ∀ (P Z : X → Fin t → Prop) (B : X → Nat),
    (∃ f : X → Fin t → Nat,
      (∀ x j, f x j ≤ D) ∧ (∀ x j, P x j → f x j = D) ∧
      (∀ x j, Z x j → f x j = 0) ∧ (∀ x y, x ⊆ y → ∀ j, f y j ≤ f x j) ∧
      ∀ (l : Nat) (p : Fin (l+1) → X) (a : Fin l → Fin t),
        (∀ i : Fin l, p i.castSucc ⊆ p i.succ) →
        (Finset.univ.sum (fun i : Fin l => f (p i.castSucc) (a i) - f (p i.succ) (a i))) ≤
          B (p (Fin.last l))) ↔
    ∃ r : X → Nat,
      r ∅ = 0 ∧ (∀ x, r x ≤ B x) ∧ (∀ x y, x ⊆ y → r x ≤ r y) ∧
      ∀ (j : Fin t) (l : Nat) (p : Fin (l+1) → X),
        l < 2^n → Function.Injective p →
        P (p 0) j → Z (p (Fin.last l)) j →
        (∀ i : Fin l, step (p i.castSucc) (p i.succ) ∨ step (p i.succ) (p i.castSucc)) →
        D ≤ Finset.univ.sum (fun i : Fin l => r (p i.succ) - r (p i.castSucc))) := by
  intro n t D
  dsimp only
  intro P Z B
  exact ⟨PEqualNP.Outside.L_meta_48520.forward_dir P Z B,
    PEqualNP.Outside.L_meta_48520.backward_dir P Z B⟩
