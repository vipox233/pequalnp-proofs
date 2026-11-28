import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_367_aux

def bounded (d n : ℕ) (M : Fin 3 → Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, ∃ t : ℕ, 0 < t ∧ t ≤ d ∧ (((M 0).trans (M 1).symm)^t) i = i

def cost {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (y : Bool × Fin n → Bool) (j : Fin 3) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, M j i))).card

def works (n : ℕ) (M : Fin 3 → Equiv.Perm (Fin n)) (partialPins scoreOnly : Bool) (H P Q : ℕ) : Prop :=
  ∀ pin : Bool × Fin n → Option Bool,
    (partialPins = true ∨ ∀ (i : Fin n) (j : Fin 2),
      (pin (false, i)).isSome = (pin (true, M j.castSucc i)).isSome) →
    let ok := fun y : Bool × Fin n → Bool => ∀ v, pin v = none ∨ pin v = some (y v)
    (∃ z : Bool × Fin n → Bool, ok z ∧ cost M z 0 = 0 ∧ cost M z 1 = 0) →
    ∀ y : Bool × Fin n → Bool, ok y → ∃ z : Bool × Fin n → Bool, ok z ∧ cost M z 0 = 0 ∧ cost M z 1 = 0 ∧
      if scoreOnly then H * cost M y 2 ≤ H * cost M z 2 + P * cost M y 0 + Q * cost M y 1
      else H * (Finset.univ.filter (fun v : Bool × Fin n => y v ≠ z v)).card ≤
        P * cost M y 0 + Q * cost M y 1

lemma cost2_le_add_dist {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (y z : Bool × Fin n → Bool) :
    cost M y 2 ≤ cost M z 2 + (Finset.univ.filter (fun v : Bool × Fin n => y v ≠ z v)).card := by
  have h1 : (Finset.univ.filter (fun v : Bool × Fin n => y v ≠ z v)).card =
      (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ z (false, i))).card +
      (Finset.univ.filter (fun i : Fin n => y (true, M 2 i) ≠ z (true, M 2 i))).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    congr 1
    exact (Equiv.sum_comp (M 2) (fun i => if y (true, i) ≠ z (true, i) then 1 else 0)).symm
  rw [h1, cost, cost, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  cases hya : y (false, i) <;> cases hyb : y (true, M 2 i) <;>
    cases hza : z (false, i) <;> cases hzb : z (true, M 2 i) <;> decide

lemma works_false_imp_true {n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} {partialPins : Bool} {H P Q : ℕ}
    (hw : works n M partialPins false H P Q) : works n M partialPins true H P Q := by
  intro pin hpin ok hex y hy
  obtain ⟨z, hok, hc0, hc1, hdist⟩ := hw pin hpin hex y hy
  refine ⟨z, hok, hc0, hc1, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte] at hdist
  simp only [↓reduceIte]
  have h2 := cost2_le_add_dist M y z
  have h3 : H * cost M y 2 ≤ H * cost M z 2 + H * (Finset.univ.filter (fun v : Bool × Fin n => y v ≠ z v)).card := by
    calc H * cost M y 2 ≤ H * (cost M z 2 + (Finset.univ.filter (fun v : Bool × Fin n => y v ≠ z v)).card) :=
          Nat.mul_le_mul_left H h2
      _ = _ := Nat.mul_add _ _ _
  omega

lemma run_bound_even {L H P Q r : ℕ}
    (hP : H * (2 * (L / 2)) ≤ 2 * P) (hQ : H * (2 * (L / 2)) ≤ 2 * Q)
    (hr : r ≤ L) (he : r % 2 = 0) : H * r ≤ 2 * P ∧ H * r ≤ 2 * Q := by
  have hle : r ≤ 2 * (L / 2) := by omega
  exact ⟨le_trans (Nat.mul_le_mul_left H hle) hP, le_trans (Nat.mul_le_mul_left H hle) hQ⟩

lemma run_bound_odd {L H P Q r : ℕ}
    (hPQ : H * (2 * ((L - 1) / 2) + 1) ≤ P + Q)
    (hr : r ≤ L) (ho : r % 2 = 1) : H * r ≤ P + Q := by
  have hle : r ≤ 2 * ((L - 1) / 2) + 1 := by omega
  exact le_trans (Nat.mul_le_mul_left H hle) hPQ

lemma interval_charge {L H P Q : ℕ}
    (hP : H * (2 * (L / 2)) ≤ 2 * P) (hQ : H * (2 * (L / 2)) ≤ 2 * Q)
    (hPQ : H * (2 * ((L - 1) / 2) + 1) ≤ P + Q) :
    ∀ N : ℕ, ∀ (f : ℕ → Bool) (c : ℕ),
      f 0 = false → f N = false →
      ((Finset.range N).filter (fun k => f k = true)).card ≤ L →
      H * ((Finset.range N).filter (fun k => f k = true)).card ≤
        P * ((Finset.range N).filter (fun k => f k ≠ f (k + 1) ∧ (c + k) % 2 = 0)).card +
        Q * ((Finset.range N).filter (fun k => f k ≠ f (k + 1) ∧ (c + k) % 2 = 1)).card := by
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro f c hf0 hfN hcard
    by_cases hall : ∀ k < N, f k = false
    · have hzero : ((Finset.range N).filter (fun k => f k = true)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k hk
        rw [Finset.mem_range] at hk
        simp [hall k hk]
      rw [hzero, mul_zero]
      exact Nat.zero_le _
    · push Not at hall
      classical
      have hexA : ∃ k, k < N ∧ f k = true := by
        obtain ⟨k, hk, hfk⟩ := hall
        exact ⟨k, hk, Bool.eq_true_of_not_eq_false hfk⟩
      let a := Nat.find hexA
      have ha_spec : a < N ∧ f a = true := Nat.find_spec hexA
      have ha_min : ∀ k < a, f k = false := by
        intro k hk
        by_contra h
        exact Nat.find_min hexA hk ⟨lt_trans hk ha_spec.1, Bool.eq_true_of_not_eq_false h⟩
      have ha_pos : 0 < a := by
        by_contra h
        have ha0 : a = 0 := by omega
        rw [ha0, hf0] at ha_spec
        exact Bool.false_ne_true ha_spec.2
      have hexB : ∃ k, a < k ∧ f k = false := ⟨N, ha_spec.1, hfN⟩
      let b := Nat.find hexB
      have hb_spec : a < b ∧ f b = false := Nat.find_spec hexB
      have hb_le : b ≤ N := Nat.find_min' hexB ⟨ha_spec.1, hfN⟩
      have hb_true : ∀ k, a ≤ k → k < b → f k = true := by
        intro k hka hkb
        rcases eq_or_lt_of_le hka with rfl | hlt
        · exact ha_spec.2
        · by_contra h
          exact Nat.find_min hexB hkb ⟨hlt, Bool.eq_false_of_not_eq_true h⟩
      have hsplit_card : ∀ (p : ℕ → Prop) [DecidablePred p],
          ((Finset.range N).filter p).card =
            ((Finset.range b).filter p).card +
            ((Finset.range (N - b)).filter (fun k => p (b + k))).card := by
        intro p _
        let addB : ℕ ↪ ℕ := ⟨fun x => b + x, fun _ _ h => Nat.add_left_cancel h⟩
        have haddB : ∀ x, addB x = b + x := fun _ => rfl
        have h1 : Finset.range N = Finset.range b ∪ (Finset.range (N - b)).map addB := by
          ext k
          simp only [Finset.mem_range, Finset.mem_union, Finset.mem_map, haddB]
          constructor
          · intro hk
            by_cases hkb : k < b
            · exact Or.inl hkb
            · exact Or.inr ⟨k - b, by omega, by omega⟩
          · rintro (hk | ⟨j, hj, rfl⟩) <;> omega
        rw [h1, Finset.filter_union, Finset.card_union_of_disjoint]
        · congr 1
          rw [Finset.filter_map, Finset.card_map]
          rfl
        · rw [Finset.disjoint_left]
          intro k hk1 hk2
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, haddB] at hk1 hk2
          obtain ⟨⟨j, _, rfl⟩, _⟩ := hk2
          omega
      have hleft_ones : ((Finset.range b).filter (fun k => f k = true)).card = b - a := by
        have hset : (Finset.range b).filter (fun k => f k = true) = Finset.Ico a b := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
          constructor
          · intro ⟨hkb, hfk⟩
            refine ⟨?_, hkb⟩
            by_contra h
            have := ha_min k (by omega)
            rw [this] at hfk
            exact Bool.false_ne_true hfk
          · intro ⟨hak, hkb⟩
            exact ⟨hkb, hb_true k hak hkb⟩
        rw [hset, Nat.card_Ico]
      have htrans_a : a - 1 < b ∧ f (a - 1) ≠ f ((a - 1) + 1) := by
        refine ⟨by omega, ?_⟩
        rw [ha_min (a - 1) (by omega), show a - 1 + 1 = a by omega, ha_spec.2]
        decide
      have htrans_b : b - 1 < b ∧ f (b - 1) ≠ f ((b - 1) + 1) := by
        refine ⟨by omega, ?_⟩
        rw [hb_true (b - 1) (by omega) (by omega), show b - 1 + 1 = b by omega, hb_spec.2]
        decide
      have hab_ne : a - 1 ≠ b - 1 := by omega
      let r := b - a
      have hr_le : r ≤ L := by
        have hle1 : ((Finset.range b).filter (fun k => f k = true)).card ≤
            ((Finset.range N).filter (fun k => f k = true)).card := by
          rw [hsplit_card]
          exact Nat.le_add_right _ _
        omega
      have hleft_bound : H * r ≤
          P * ((Finset.range b).filter (fun k => f k ≠ f (k + 1) ∧ (c + k) % 2 = 0)).card +
          Q * ((Finset.range b).filter (fun k => f k ≠ f (k + 1) ∧ (c + k) % 2 = 1)).card := by
        let S0 := (Finset.range b).filter (fun k => f k ≠ f (k + 1) ∧ (c + k) % 2 = 0)
        let S1 := (Finset.range b).filter (fun k => f k ≠ f (k + 1) ∧ (c + k) % 2 = 1)
        change H * r ≤ P * S0.card + Q * S1.card
        by_cases he : r % 2 = 0
        · have hpar : (c + (a - 1)) % 2 = (c + (b - 1)) % 2 := by omega
          have hbe := run_bound_even hP hQ hr_le he
          by_cases h0 : (c + (a - 1)) % 2 = 0
          · have hsub : ({a - 1, b - 1} : Finset ℕ) ⊆ S0 := by
              intro k hk
              simp only [Finset.mem_insert, Finset.mem_singleton] at hk
              rcases hk with rfl | rfl
              · simp [S0, htrans_a.1, htrans_a.2, h0]
              · simp [S0, htrans_b.1, htrans_b.2, ← hpar, h0]
            have h2 : 2 ≤ S0.card := by
              have hc := Finset.card_le_card hsub
              rw [Finset.card_pair hab_ne] at hc
              exact hc
            have hmul : 2 * P ≤ P * S0.card := by
              rw [mul_comm 2 P]
              exact Nat.mul_le_mul_left P h2
            omega
          · have h1 : (c + (a - 1)) % 2 = 1 := by omega
            have hsub : ({a - 1, b - 1} : Finset ℕ) ⊆ S1 := by
              intro k hk
              simp only [Finset.mem_insert, Finset.mem_singleton] at hk
              rcases hk with rfl | rfl
              · simp [S1, htrans_a.1, htrans_a.2, h1]
              · simp [S1, htrans_b.1, htrans_b.2, ← hpar, h1]
            have h2 : 2 ≤ S1.card := by
              have hc := Finset.card_le_card hsub
              rw [Finset.card_pair hab_ne] at hc
              exact hc
            have hmul : 2 * Q ≤ Q * S1.card := by
              rw [mul_comm 2 Q]
              exact Nat.mul_le_mul_left Q h2
            omega
        · have ho : r % 2 = 1 := by omega
          have hbo := run_bound_odd hPQ hr_le ho
          have h10 : 1 ≤ S0.card ∧ 1 ≤ S1.card := by
            by_cases h0 : (c + (a - 1)) % 2 = 0
            · have h1 : (c + (b - 1)) % 2 = 1 := by omega
              refine ⟨Finset.card_pos.2 ⟨a - 1, ?_⟩, Finset.card_pos.2 ⟨b - 1, ?_⟩⟩
              · simp [S0, htrans_a.1, htrans_a.2, h0]
              · simp [S1, htrans_b.1, htrans_b.2, h1]
            · have h1 : (c + (a - 1)) % 2 = 1 := by omega
              have h2 : (c + (b - 1)) % 2 = 0 := by omega
              refine ⟨Finset.card_pos.2 ⟨b - 1, ?_⟩, Finset.card_pos.2 ⟨a - 1, ?_⟩⟩
              · simp [S0, htrans_b.1, htrans_b.2, h2]
              · simp [S1, htrans_a.1, htrans_a.2, h1]
          have hP1 : P ≤ P * S0.card := Nat.le_mul_of_pos_right P h10.1
          have hQ1 : Q ≤ Q * S1.card := Nat.le_mul_of_pos_right Q h10.2
          omega
      have hright_card : ((Finset.range (N - b)).filter (fun k => f (b + k) = true)).card ≤ L := by
        have hle2 : ((Finset.range (N - b)).filter (fun k => f (b + k) = true)).card ≤
            ((Finset.range N).filter (fun k => f k = true)).card := by
          rw [hsplit_card (fun k => f k = true)]
          exact Nat.le_add_left _ _
        exact le_trans hle2 hcard
      have hright_bound := ih (N - b) (by omega) (fun k => f (b + k)) (c + b)
        (by simpa using hb_spec.2) (by rw [Nat.add_sub_of_le hb_le]; exact hfN) hright_card
      have hr0 : ((Finset.range (N - b)).filter (fun k => f (b + k) ≠ f (b + (k + 1)) ∧ (c + b + k) % 2 = 0)).card =
          ((Finset.range (N - b)).filter (fun k => f (b + k) ≠ f ((b + k) + 1) ∧ (c + (b + k)) % 2 = 0)).card := by
        congr 1
        ext k
        simp only [Finset.mem_filter, Nat.add_assoc]
      have hr1 : ((Finset.range (N - b)).filter (fun k => f (b + k) ≠ f (b + (k + 1)) ∧ (c + b + k) % 2 = 1)).card =
          ((Finset.range (N - b)).filter (fun k => f (b + k) ≠ f ((b + k) + 1) ∧ (c + (b + k)) % 2 = 1)).card := by
        congr 1
        ext k
        simp only [Finset.mem_filter, Nat.add_assoc]
      rw [hr0, hr1] at hright_bound
      rw [hsplit_card (fun k => f k = true), hleft_ones,
        hsplit_card (fun k => f k ≠ f (k + 1) ∧ (c + k) % 2 = 0),
        hsplit_card (fun k => f k ≠ f (k + 1) ∧ (c + k) % 2 = 1)]
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]
      dsimp only [r] at hleft_bound
      omega

lemma cycle_charge {L H P Q m : ℕ} (hm : 0 < m)
    (hP : H * (2 * (L / 2)) ≤ 2 * P) (hQ : H * (2 * (L / 2)) ≤ 2 * Q)
    (hPQ : H * (2 * ((L - 1) / 2) + 1) ≤ P + Q)
    (g : Fin (2 * m) → Bool) (hcard : (Finset.univ.filter (fun j : Fin (2 * m) => g j = true)).card ≤ L)
    (hzero : ∃ s0 : Fin (2 * m), g s0 = false) :
    H * (Finset.univ.filter (fun j : Fin (2 * m) => g j = true)).card ≤
      P * (Finset.univ.filter (fun j : Fin (2 * m) =>
        g j ≠ g ⟨(j.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ ∧ j.val % 2 = 0)).card +
      Q * (Finset.univ.filter (fun j : Fin (2 * m) =>
        g j ≠ g ⟨(j.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ ∧ j.val % 2 = 1)).card := by
  obtain ⟨s0, hs0⟩ := hzero
  let shift : ℕ → Fin (2 * m) := fun k => ⟨(s0.val + k) % (2 * m), Nat.mod_lt _ (by omega)⟩
  let f : ℕ → Bool := fun k => g (shift k)
  have hbij : ∀ p : Fin (2 * m) → Prop, [DecidablePred p] →
      ((Finset.range (2 * m)).filter (fun k => p (shift k))).card =
      (Finset.univ.filter p).card := by
    intro p _
    apply Finset.card_nbij' shift (fun j => (j.val + 2 * m - s0.val) % (2 * m))
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hk ⊢
      exact hk.2
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hj ⊢
      refine ⟨Nat.mod_lt _ (by omega), ?_⟩
      have heq : shift ((j.val + 2 * m - s0.val) % (2 * m)) = j := by
        ext
        simp only [shift, Nat.add_mod_mod]
        have h1 : s0.val + (j.val + 2 * m - s0.val) = j.val + 2 * m := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
      rw [heq]
      exact hj
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
      simp only [shift]
      by_cases h : s0.val + k < 2 * m
      · rw [Nat.mod_eq_of_lt h]
        have h1 : s0.val + k + 2 * m - s0.val = k + 2 * m := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hk.1]
      · have h2 : (s0.val + k) % (2 * m) = s0.val + k - 2 * m := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [h2]
        have h3 : s0.val + k - 2 * m + 2 * m - s0.val = k := by omega
        rw [h3, Nat.mod_eq_of_lt hk.1]
    · intro j _
      ext
      simp only [shift, Nat.add_mod_mod]
      have h1 : s0.val + (j.val + 2 * m - s0.val) = j.val + 2 * m := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
  have hf0 : f 0 = false := by
    simp only [f, shift, Nat.add_zero, Nat.mod_eq_of_lt s0.isLt, Fin.eta]
    exact hs0
  have hfN : f (2 * m) = false := by
    simp only [f, shift, Nat.add_mod_right, Nat.mod_eq_of_lt s0.isLt, Fin.eta]
    exact hs0
  have h1 := hbij (fun j => g j = true)
  have hstep : ∀ k, shift (k + 1) = ⟨((shift k).val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ := by
    intro k
    ext
    simp only [shift, Nat.mod_add_mod, Nat.add_assoc]
  have hpar : ∀ k, (shift k).val % 2 = (s0.val + k) % 2 := by
    intro k
    simp only [shift]
    have hdiv : 2 ∣ 2 * m := ⟨m, rfl⟩
    exact Nat.mod_mod_of_dvd (s0.val + k) hdiv
  have h2 : ((Finset.range (2 * m)).filter (fun k => f k ≠ f (k + 1) ∧ (s0.val + k) % 2 = 0)).card =
      (Finset.univ.filter (fun j : Fin (2 * m) =>
        g j ≠ g ⟨(j.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ ∧ j.val % 2 = 0)).card := by
    rw [← hbij (fun j => g j ≠ g ⟨(j.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ ∧ j.val % 2 = 0)]
    congr 1
    ext k
    simp only [Finset.mem_filter, f, hstep, hpar]
  have h3 : ((Finset.range (2 * m)).filter (fun k => f k ≠ f (k + 1) ∧ (s0.val + k) % 2 = 1)).card =
      (Finset.univ.filter (fun j : Fin (2 * m) =>
        g j ≠ g ⟨(j.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ ∧ j.val % 2 = 1)).card := by
    rw [← hbij (fun j => g j ≠ g ⟨(j.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ ∧ j.val % 2 = 1)]
    congr 1
    ext k
    simp only [Finset.mem_filter, f, hstep, hpar]
  rw [← h1, ← h2, ← h3]
  exact interval_charge hP hQ hPQ (2 * m) f s0.val hf0 hfN (by rw [h1]; exact hcard)

noncomputable def period {d n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (hb : bounded d n M) (i : Fin n) : ℕ :=
  Nat.find (hb i)

lemma period_pos {d n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} (hb : bounded d n M) (i : Fin n) :
    0 < period M hb i := (Nat.find_spec (hb i)).1

lemma period_le {d n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} (hb : bounded d n M) (i : Fin n) :
    period M hb i ≤ d := (Nat.find_spec (hb i)).2.1

lemma period_pow {d n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} (hb : bounded d n M) (i : Fin n) :
    ((((M 0).trans (M 1).symm)^(period M hb i)) i) = i := (Nat.find_spec (hb i)).2.2

lemma period_min {d n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} (hb : bounded d n M) (i : Fin n)
    {t : ℕ} (ht0 : 0 < t) (ht : t < period M hb i) :
    (((M 0).trans (M 1).symm)^t) i ≠ i := by
  intro h
  exact Nat.find_min (hb i) ht ⟨ht0, le_trans (le_of_lt ht) (period_le hb i), h⟩

noncomputable def orb {d n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (hb : bounded d n M) (i : Fin n) :
    Finset (Fin n) :=
  (Finset.range (period M hb i)).image (fun k => (((M 0).trans (M 1).symm)^k) i)

lemma mem_orb_iff {d n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} (hb : bounded d n M) (i x : Fin n) :
    x ∈ orb M hb i ↔ ∃ k : ℕ, (((M 0).trans (M 1).symm)^k) i = x := by
  let π := (M 0).trans (M 1).symm
  have hmod : ∀ k : ℕ, (π^k) i = (π^(k % period M hb i)) i := by
    intro k
    have hdiv : k = period M hb i * (k / period M hb i) + k % period M hb i :=
      (Nat.div_add_mod k (period M hb i)).symm
    conv_lhs => rw [hdiv, add_comm, pow_add, Equiv.Perm.mul_apply]
    have hmul : ∀ q : ℕ, (π^(period M hb i * q)) i = i := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, period_pow hb i, ih]
    rw [hmul]
  constructor
  · intro hx
    rw [orb, Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    rw [orb, Finset.mem_image]
    exact ⟨k % period M hb i, Finset.mem_range.2 (Nat.mod_lt _ (period_pos hb i)), (hmod k).symm⟩

lemma self_mem_orb {d n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} (hb : bounded d n M) (i : Fin n) :
    i ∈ orb M hb i := (mem_orb_iff hb i i).2 ⟨0, rfl⟩

lemma orb_eq_of_mem {d n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} (hb : bounded d n M) {i j : Fin n}
    (hij : j ∈ orb M hb i) : orb M hb j = orb M hb i := by
  let π := (M 0).trans (M 1).symm
  obtain ⟨k, rfl⟩ := (mem_orb_iff hb i j).1 hij
  ext x
  rw [mem_orb_iff, mem_orb_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + k, by rw [pow_add, Equiv.Perm.mul_apply]⟩
  · rintro ⟨t, rfl⟩
    let m := period M hb i
    have hm : 0 < m := period_pos hb i
    have hpow_m : ∀ q : ℕ, (π^(m * q)) i = i := by
      intro q
      induction q with
      | zero => simp
      | succ q ih => rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, period_pow hb i, ih]
    let r := (t + m * (k + 1) - k)
    refine ⟨r, ?_⟩
    rw [← Equiv.Perm.mul_apply, ← pow_add]
    have hsum : r + k = t + m * (k + 1) := by
      have : k ≤ m * (k + 1) := by
        calc k ≤ k + 1 := Nat.le_succ k
          _ = 1 * (k + 1) := (Nat.one_mul _).symm
          _ ≤ m * (k + 1) := Nat.mul_le_mul_right _ hm
      omega
    rw [hsum, pow_add, Equiv.Perm.mul_apply, hpow_m]

lemma orb_disjoint_or_eq {d n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} (hb : bounded d n M) (i j : Fin n) :
    orb M hb i = orb M hb j ∨ Disjoint (orb M hb i) (orb M hb j) := by
  by_cases h : (orb M hb i ∩ orb M hb j).Nonempty
  · obtain ⟨x, hx⟩ := h
    rw [Finset.mem_inter] at hx
    left
    rw [← orb_eq_of_mem hb hx.1, orb_eq_of_mem hb hx.2]
  · right
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.not_nonempty_iff_eq_empty.1 h

lemma pow_inj_on_period {d n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} (hb : bounded d n M) (i : Fin n)
    {a b : ℕ} (ha : a < period M hb i) (hb' : b < period M hb i)
    (heq : (((M 0).trans (M 1).symm)^a) i = (((M 0).trans (M 1).symm)^b) i) : a = b := by
  let π := (M 0).trans (M 1).symm
  wlog hle : a ≤ b generalizing a b
  · exact (this hb' ha heq.symm (by omega)).symm
  by_contra hne
  have hlt : a < b := by omega
  have hsub : (π^(b - a)) i = i := by
    apply (π^a).injective
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_of_le hle]
    exact heq.symm
  exact period_min hb i (by omega) (by omega) hsub

lemma cost01_zero_iff_const_orb {d n : ℕ} {M : Fin 3 → Equiv.Perm (Fin n)} (hb : bounded d n M)
    (z : Bool × Fin n → Bool) :
    (cost M z 0 = 0 ∧ cost M z 1 = 0) ↔
      (∀ i, z (false, i) = z (true, M 0 i)) ∧
      (∀ i j, j ∈ orb M hb i → z (false, j) = z (false, i)) := by
  have hc0 : cost M z 0 = 0 ↔ ∀ i, z (false, i) = z (true, M 0 i) := by
    rw [cost, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp
  have hc1 : cost M z 1 = 0 ↔ ∀ i, z (false, i) = z (true, M 1 i) := by
    rw [cost, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp
  rw [hc0, hc1]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    intro i j hj
    obtain ⟨k, rfl⟩ := (mem_orb_iff hb i j).1 hj
    clear hj
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      have hstep : z (false, ((M 0).trans (M 1).symm) ((((M 0).trans (M 1).symm)^k) i)) =
          z (false, (((M 0).trans (M 1).symm)^k) i) := by
        rw [h1, Equiv.trans_apply, Equiv.apply_symm_apply, ← h0]
      rw [hstep, ih]
  · rintro ⟨h0, horb⟩
    refine ⟨h0, ?_⟩
    intro i
    have hmem : ((M 0).trans (M 1).symm) ((M 0).symm (M 1 i)) ∈ orb M hb ((M 0).symm (M 1 i)) :=
      (mem_orb_iff hb _ _).2 ⟨1, by simp⟩
    have heq : ((M 0).trans (M 1).symm) ((M 0).symm (M 1 i)) = i := by
      simp [Equiv.trans_apply]
    rw [heq] at hmem
    rw [horb _ _ hmem, h0, Equiv.apply_symm_apply]

lemma suff_works {d n : ℕ} (hd : 0 < d) (M : Fin 3 → Equiv.Perm (Fin n)) (hb : bounded d n M)
    (partialPins : Bool) (H P Q : ℕ)
    (hP : H * (2 * ((if partialPins then 2 * d - 1 else d) / 2)) ≤ 2 * P)
    (hQ : H * (2 * ((if partialPins then 2 * d - 1 else d) / 2)) ≤ 2 * Q)
    (hPQ : H * (2 * (((if partialPins then 2 * d - 1 else d) - 1) / 2) + 1) ≤ P + Q) :
    works n M partialPins false H P Q := by
  intro pin hpin ok hex y hy
  obtain ⟨z0, hz0_ok, hz0_0, hz0_1⟩ := hex
  have hz0_const := (cost01_zero_iff_const_orb hb z0).1 ⟨hz0_0, hz0_1⟩
  let L := if partialPins then 2 * d - 1 else d
  let π := (M 0).trans (M 1).symm
  let cycV : Fin n → Finset (Bool × Fin n) := fun i =>
    (orb M hb i).image (fun j => (false, j)) ∪ (orb M hb i).image (fun j => (true, M 0 j))
  have hcycV_eq : ∀ i j, j ∈ orb M hb i → cycV j = cycV i := by
    intro i j hj
    simp only [cycV, orb_eq_of_mem hb hj]
  let hasPin : Fin n → Prop := fun i => ∃ v ∈ cycV i, (pin v).isSome
  classical
  let bitOf : Fin n → Bool := fun i =>
    if hasPin i then z0 (false, i)
    else decide (((cycV i).filter (fun v => y v = false)).card <
      ((cycV i).filter (fun v => y v = true)).card)
  have hbit_eq : ∀ i j, j ∈ orb M hb i → bitOf j = bitOf i := by
    intro i j hj
    simp only [bitOf, hasPin, hcycV_eq i j hj, hz0_const.2 i j hj]
  let z : Bool × Fin n → Bool := fun v =>
    match v.1 with
    | false => bitOf v.2
    | true => bitOf ((M 0).symm v.2)
  have hz_const : (∀ i, z (false, i) = z (true, M 0 i)) ∧
      (∀ i j, j ∈ orb M hb i → z (false, j) = z (false, i)) := by
    constructor
    · intro i
      simp [z]
    · intro i j hj
      exact hbit_eq i j hj
  have hz01 : cost M z 0 = 0 ∧ cost M z 1 = 0 := (cost01_zero_iff_const_orb hb z).2 hz_const
  have hz_ok : ∀ v, pin v = none ∨ pin v = some (z v) := by
    intro v
    cases hv : pin v with
    | none => exact Or.inl rfl
    | some b =>
      right
      have hv0 : z0 v = b := by
        rcases hz0_ok v with h | h
        · rw [hv] at h; cases h
        · rw [hv] at h; exact (Option.some.inj h).symm
      rcases v with ⟨side, idx⟩
      cases side
      · have hmem : (false, idx) ∈ cycV idx :=
          Finset.mem_union_left _ (Finset.mem_image.2 ⟨idx, self_mem_orb hb idx, rfl⟩)
        have hp : hasPin idx := ⟨(false, idx), hmem, by simp [hv]⟩
        simp only [z, bitOf, hp, ite_true]
        rw [hv0]
      · let i0 := (M 0).symm idx
        have hmem : (true, idx) ∈ cycV i0 :=
          Finset.mem_union_right _ (Finset.mem_image.2 ⟨i0, self_mem_orb hb i0, by simp [i0]⟩)
        have hp : hasPin i0 := ⟨(true, idx), hmem, by simp [hv]⟩
        have hzval : z (true, idx) = z0 (false, i0) := by
          show bitOf i0 = z0 (false, i0)
          simp only [bitOf, hp, ite_true]
        have hzeq : z0 (false, i0) = z0 (true, idx) := by
          have := hz0_const.1 i0
          simpa [i0] using this
        rw [hzval, hzeq, hv0]
  refine ⟨z, hz_ok, hz01.1, hz01.2, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  let Orbs : Finset (Finset (Fin n)) := Finset.univ.image (orb M hb)
  have hpart : ∀ O1 ∈ Orbs, ∀ O2 ∈ Orbs, O1 ≠ O2 → Disjoint O1 O2 := by
    intro O1 h1 O2 h2 hne
    rw [Finset.mem_image] at h1 h2
    obtain ⟨i1, _, rfl⟩ := h1
    obtain ⟨i2, _, rfl⟩ := h2
    rcases orb_disjoint_or_eq hb i1 i2 with h | h
    · exact absurd h hne
    · exact h
  have hcover : Orbs.biUnion id = Finset.univ := by
    ext x
    simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
    exact ⟨orb M hb x, Finset.mem_image.2 ⟨x, Finset.mem_univ _, rfl⟩, self_mem_orb hb x⟩
  have hsum_orb : ∀ f : Fin n → ℕ, ∑ i : Fin n, f i = ∑ O ∈ Orbs, ∑ i ∈ O, f i := by
    intro f
    have := Finset.sum_biUnion (s := Orbs) (t := id) (f := f) (fun O1 h1 O2 h2 hne => hpart O1 h1 O2 h2 hne)
    rw [hcover] at this
    exact this
  have hdist_split : (Finset.univ.filter (fun v : Bool × Fin n => y v ≠ z v)).card =
      ∑ O ∈ Orbs, ∑ i ∈ O,
        ((if y (false, i) ≠ z (false, i) then 1 else 0) +
         (if y (true, M 0 i) ≠ z (true, M 0 i) then 1 else 0)) := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    rw [← Equiv.sum_comp (M 0) (fun i => if y (true, i) ≠ z (true, i) then 1 else 0),
      ← Finset.sum_add_distrib]
    exact hsum_orb _
  have hc0_split : cost M y 0 = ∑ O ∈ Orbs, ∑ i ∈ O, (if y (false, i) ≠ y (true, M 0 i) then 1 else 0) := by
    rw [cost, Finset.card_filter]
    exact hsum_orb _
  have hc1_split : cost M y 1 = ∑ O ∈ Orbs, ∑ i ∈ O, (if y (false, i) ≠ y (true, M 1 i) then 1 else 0) := by
    rw [cost, Finset.card_filter]
    exact hsum_orb _
  rw [hdist_split, hc0_split, hc1_split, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro O hO
  rw [Finset.mem_image] at hO
  obtain ⟨i0, _, rfl⟩ := hO
  let m := period M hb i0
  have hm_pos : 0 < m := period_pos hb i0
  have hm_le : m ≤ d := period_le hb i0
  let pos : Fin m → Fin n := fun k => (π^k.val) i0
  have hpos_inj : Function.Injective pos := by
    intro a b hab
    ext
    exact pow_inj_on_period hb i0 a.isLt b.isLt hab
  have hpos_orb : (Finset.univ : Finset (Fin m)).image pos = orb M hb i0 := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, orb, Finset.mem_range]
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  let vert : Fin (2 * m) → Bool × Fin n := fun j =>
    if j.val % 2 = 0 then (false, (π^(j.val / 2)) i0)
    else (true, M 0 ((π^(j.val / 2)) i0))
  have hvert_inj : Function.Injective vert := by
    intro j1 j2 h
    by_cases h1 : j1.val % 2 = 0 <;> by_cases h2 : j2.val % 2 = 0
    · simp only [vert, h1, h2, ite_true, Prod.mk.injEq, true_and] at h
      have hdiv : j1.val / 2 = j2.val / 2 := pow_inj_on_period hb i0 (by omega) (by omega) h
      ext; omega
    · simp [vert, h1, h2] at h
    · simp [vert, h1, h2] at h
    · simp only [vert, h1, h2, ite_false, Prod.mk.injEq, true_and] at h
      have h' := (M 0).injective h
      have hdiv : j1.val / 2 = j2.val / 2 := pow_inj_on_period hb i0 (by omega) (by omega) h'
      ext; omega
  have hvert_img : (Finset.univ : Finset (Fin (2 * m))).image vert = cycV i0 := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and, cycV, Finset.mem_union, ← hpos_orb]
    constructor
    · rintro ⟨j, rfl⟩
      by_cases h : j.val % 2 = 0
      · left
        refine ⟨(π^(j.val / 2)) i0, ⟨⟨j.val / 2, by omega⟩, rfl⟩, by simp [vert, h]⟩
      · right
        refine ⟨(π^(j.val / 2)) i0, ⟨⟨j.val / 2, by omega⟩, rfl⟩, by simp [vert, h]⟩
    · rintro (⟨x, ⟨k, rfl⟩, rfl⟩ | ⟨x, ⟨k, rfl⟩, rfl⟩)
      · refine ⟨⟨2 * k.val, by omega⟩, ?_⟩
        simp [vert, pos]
      · refine ⟨⟨2 * k.val + 1, by omega⟩, ?_⟩
        have hmod : (2 * k.val + 1) % 2 = 1 := by omega
        have hdiv : (2 * k.val + 1) / 2 = k.val := by omega
        simp [vert, pos, hmod, hdiv]
  let g : Fin (2 * m) → Bool := fun j => decide (y (vert j) ≠ z (vert j))
  have hsum_pos : ∀ f : Fin n → ℕ, ∑ i ∈ orb M hb i0, f i = ∑ k : Fin m, f (pos k) := by
    intro f
    rw [← hpos_orb, Finset.sum_image (fun a _ b _ h => hpos_inj h)]
  have hdist_O : ∑ i ∈ orb M hb i0,
      ((if y (false, i) ≠ z (false, i) then 1 else 0) +
       (if y (true, M 0 i) ≠ z (true, M 0 i) then 1 else 0)) =
      (Finset.univ.filter (fun j : Fin (2 * m) => g j = true)).card := by
    rw [hsum_pos, Finset.card_filter]
    have hsplit2 : ∑ j : Fin (2 * m), (if g j = true then 1 else 0) =
        ∑ k : Fin m, ((if g ⟨2 * k.val, by omega⟩ = true then 1 else 0) +
          (if g ⟨2 * k.val + 1, by omega⟩ = true then 1 else 0)) := by
      have hbi : (Finset.univ : Finset (Fin (2 * m))) =
          (Finset.univ : Finset (Fin m × Bool)).image
            (fun kb => ⟨2 * kb.1.val + if kb.2 then 1 else 0, by
              have := kb.1.isLt; cases kb.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩) := by
        ext j
        simp only [Finset.mem_univ, Finset.mem_image, true_and, true_iff]
        refine ⟨(⟨j.val / 2, by omega⟩, decide (j.val % 2 = 1)), ?_⟩
        ext
        by_cases h : j.val % 2 = 1 <;> simp [h] <;> omega
      rw [hbi, Finset.sum_image]
      · rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro k _
        rw [Fintype.sum_bool, add_comm]
        simp
      · intro a _ b _ h
        rw [Fin.ext_iff] at h
        cases ha : a.2 <;> cases hb : b.2 <;> simp [ha, hb] at h
        · exact Prod.ext (Fin.ext (by omega)) (by rw [ha, hb])
        · omega
        · omega
        · exact Prod.ext (Fin.ext (by omega)) (by rw [ha, hb])
    rw [hsplit2]
    apply Finset.sum_congr rfl
    intro k _
    have h1 : vert ⟨2 * k.val, by omega⟩ = (false, pos k) := by
      simp [vert, pos]
    have h2 : vert ⟨2 * k.val + 1, by omega⟩ = (true, M 0 (pos k)) := by
      have hmod : (2 * k.val + 1) % 2 = 1 := by omega
      have hdiv : (2 * k.val + 1) / 2 = k.val := by omega
      simp [vert, pos, hmod, hdiv]
    simp [g, h1, h2]
  have hz_vert : ∀ j : Fin (2 * m), z (vert j) = bitOf i0 := by
    intro j
    have hmem : (π^(j.val / 2)) i0 ∈ orb M hb i0 := (mem_orb_iff hb i0 _).2 ⟨j.val / 2, rfl⟩
    by_cases h : j.val % 2 = 0
    · simp only [vert, h, ite_true]
      exact hz_const.2 i0 _ hmem
    · simp only [vert, h, ite_false]
      rw [← hz_const.1]
      exact hz_const.2 i0 _ hmem
  have hg_ne : ∀ j1 j2 : Fin (2 * m), g j1 ≠ g j2 ↔ y (vert j1) ≠ y (vert j2) := by
    intro j1 j2
    simp only [g, hz_vert]
    cases y (vert j1) <;> cases y (vert j2) <;> cases bitOf i0 <;> decide
  have hc0_O : ∑ i ∈ orb M hb i0, (if y (false, i) ≠ y (true, M 0 i) then 1 else 0) =
      (Finset.univ.filter (fun j : Fin (2 * m) =>
        g j ≠ g ⟨(j.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ ∧ j.val % 2 = 0)).card := by
    rw [hsum_pos, ← Finset.card_filter]
    apply Finset.card_nbij' (fun k : Fin m => (⟨2 * k.val, by omega⟩ : Fin (2 * m)))
      (fun j : Fin (2 * m) => (⟨j.val / 2, by omega⟩ : Fin m))
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      refine ⟨?_, by omega⟩
      rw [hg_ne]
      have h1 : vert ⟨2 * k.val, by omega⟩ = (false, pos k) := by simp [vert, pos]
      have h2 : vert ⟨(2 * k.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ = (true, M 0 (pos k)) := by
        have hlt : 2 * k.val + 1 < 2 * m := by omega
        have hmod : (2 * k.val + 1) % (2 * m) = 2 * k.val + 1 := Nat.mod_eq_of_lt hlt
        have hmod2 : (2 * k.val + 1) % 2 = 1 := by omega
        have hdiv2 : (2 * k.val + 1) / 2 = k.val := by omega
        simp [vert, hmod, hmod2, hdiv2, pos]
      rw [h1, h2]
      exact hk
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have hne := (hg_ne _ _).1 hj.1
      have h1 : vert j = (false, pos ⟨j.val / 2, by omega⟩) := by simp [vert, hj.2, pos]
      have h2 : vert ⟨(j.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ =
          (true, M 0 (pos ⟨j.val / 2, by omega⟩)) := by
        have hlt : j.val + 1 < 2 * m := by omega
        have hmod : (j.val + 1) % (2 * m) = j.val + 1 := Nat.mod_eq_of_lt hlt
        have hmod2 : (j.val + 1) % 2 = 1 := by omega
        have hdiv2 : (j.val + 1) / 2 = j.val / 2 := by omega
        simp [vert, hmod, hmod2, hdiv2, pos]
      rw [h1, h2] at hne
      exact hne
    · intro k _
      ext; simp
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter] at hj
      ext; dsimp only; omega
  have hc1_O : ∑ i ∈ orb M hb i0, (if y (false, i) ≠ y (true, M 1 i) then 1 else 0) =
      (Finset.univ.filter (fun j : Fin (2 * m) =>
        g j ≠ g ⟨(j.val + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ ∧ j.val % 2 = 1)).card := by
    rw [hsum_pos]
    let step : Equiv.Perm (Fin m) := finRotate m
    rw [← Equiv.sum_comp step (fun k => if y (false, pos k) ≠ y (true, M 1 (pos k)) then 1 else 0)]
    rw [← Finset.card_filter]
    have hstep_val : ∀ k : Fin m, (step k).val = (k.val + 1) % m := by
      have hgen : ∀ n : ℕ, 0 < n → ∀ k : Fin n, (finRotate n k).val = (k.val + 1) % n := by
        intro n hn k
        cases n with
        | zero => omega
        | succ n' =>
          by_cases hk : k = Fin.last n'
          · rw [hk, finRotate_last]
            simp
          · rw [coe_finRotate_of_ne_last hk]
            have hne : k.val ≠ n' := by
              intro h; apply hk; ext; exact h
            have hlt : k.val + 1 < n' + 1 := by omega
            exact (Nat.mod_eq_of_lt hlt).symm
      exact hgen m hm_pos
    have hrot : ∀ k : Fin m, pos (step k) = π (pos k) := by
      intro k
      by_cases hlast : k.val + 1 < m
      · have hv : (step k).val = k.val + 1 := by rw [hstep_val, Nat.mod_eq_of_lt hlast]
        simp only [pos, hv, pow_succ', Equiv.Perm.mul_apply]
      · have hv : (step k).val = 0 := by
          rw [hstep_val, show k.val + 1 = m by omega, Nat.mod_self]
        simp only [pos, hv, pow_zero, Equiv.Perm.coe_one, id_eq]
        rw [← Equiv.Perm.mul_apply, ← pow_succ', show k.val + 1 = m by omega, period_pow hb i0]
    have hM1 : ∀ k : Fin m, M 1 (pos (step k)) = M 0 (pos k) := by
      intro k
      rw [hrot k]
      simp [π]
    have hvert_next : ∀ k : Fin m,
        vert ⟨((2 * k.val + 1) + 1) % (2 * m), Nat.mod_lt _ (by omega)⟩ = (false, pos (step k)) := by
      intro k
      by_cases hlast : k.val + 1 < m
      · have hmod : (2 * k.val + 1 + 1) % (2 * m) = 2 * (k.val + 1) := by
          rw [show 2 * k.val + 1 + 1 = 2 * (k.val + 1) by omega]
          exact Nat.mod_eq_of_lt (by omega)
        have hv : (step k).val = k.val + 1 := by rw [hstep_val, Nat.mod_eq_of_lt hlast]
        simp [vert, pos, hmod, hv]
      · have hmod : (2 * k.val + 1 + 1) % (2 * m) = 0 := by
          rw [show 2 * k.val + 1 + 1 = 2 * m by omega, Nat.mod_self]
        have hv : (step k).val = 0 := by
          rw [hstep_val, show k.val + 1 = m by omega, Nat.mod_self]
        simp [vert, pos, hmod, hv]
    apply Finset.card_nbij' (fun k : Fin m => (⟨2 * k.val + 1, by omega⟩ : Fin (2 * m)))
      (fun j : Fin (2 * m) => (⟨j.val / 2, by omega⟩ : Fin m))
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      refine ⟨?_, by omega⟩
      rw [hg_ne]
      have h1 : vert ⟨2 * k.val + 1, by omega⟩ = (true, M 0 (pos k)) := by
        have hmod2 : (2 * k.val + 1) % 2 = 1 := by omega
        have hdiv2 : (2 * k.val + 1) / 2 = k.val := by omega
        simp [vert, pos, hmod2, hdiv2]
      rw [h1, hvert_next k, ← hM1 k]
      exact hk.symm
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have hne := (hg_ne _ _).1 hj.1
      let k : Fin m := ⟨j.val / 2, by omega⟩
      have hjeq : j = ⟨2 * k.val + 1, by omega⟩ := by ext; simp [k]; omega
      rw [hjeq] at hne
      have h1 : vert ⟨2 * k.val + 1, by omega⟩ = (true, M 0 (pos k)) := by
        have hmod2 : (2 * k.val + 1) % 2 = 1 := by omega
        have hdiv2 : (2 * k.val + 1) / 2 = k.val := by omega
        simp [vert, pos, hmod2, hdiv2]
      rw [h1, hvert_next k, ← hM1 k] at hne
      exact hne.symm
    · intro k _
      ext; simp; omega
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter] at hj
      ext; dsimp only; omega
  rw [hdist_O, hc0_O, hc1_O]
  have hcard_zero : (Finset.univ.filter (fun j : Fin (2 * m) => g j = true)).card ≤ L ∧
      ∃ s0 : Fin (2 * m), g s0 = false := by
    by_cases hp : hasPin i0
    · obtain ⟨v0, hv0_mem, hv0_pin⟩ := hp
      rw [← hvert_img, Finset.mem_image] at hv0_mem
      obtain ⟨s0, _, rfl⟩ := hv0_mem
      have hs0_eq : y (vert s0) = z (vert s0) := by
        cases hps : pin (vert s0) with
        | none => simp [hps] at hv0_pin
        | some b =>
          have hyb : y (vert s0) = b := by
            rcases hy (vert s0) with h | h
            · rw [hps] at h; cases h
            · rw [hps] at h; exact (Option.some.inj h).symm
          have hzb : z (vert s0) = b := by
            rcases hz_ok (vert s0) with h | h
            · rw [hps] at h; cases h
            · rw [hps] at h; exact (Option.some.inj h).symm
          rw [hyb, hzb]
      have hs0 : g s0 = false := by simp [g, hs0_eq]
      refine ⟨?_, ⟨s0, hs0⟩⟩
      cases hpart_eq : partialPins
      · have hall_pin : ∀ j : Fin (2 * m), (pin (vert j)).isSome = true := by
          have hfp : ∀ (i : Fin n) (j : Fin 2),
              (pin (false, i)).isSome = (pin (true, M j.castSucc i)).isSome := by
            rcases hpin with h | h
            · rw [hpart_eq] at h; cases h
            · exact h
          have hconst_p : ∀ i j, j ∈ orb M hb i → (pin (false, j)).isSome = (pin (false, i)).isSome := by
            intro i j hj
            obtain ⟨k, rfl⟩ := (mem_orb_iff hb i j).1 hj
            clear hj
            induction k with
            | zero => rfl
            | succ k ih =>
              rw [pow_succ', Equiv.Perm.mul_apply]
              have hstep : (pin (false, π ((π^k) i))).isSome = (pin (false, (π^k) i)).isSome := by
                have h1 := hfp (π ((π^k) i)) 1
                have h0 := hfp ((π^k) i) 0
                simp only [Fin.castSucc_one, Fin.castSucc_zero] at h1 h0
                rw [h1]
                have heq : M 1 (π ((π^k) i)) = M 0 ((π^k) i) := by simp [π]
                rw [heq, ← h0]
              rw [hstep, ih]
          have hv_isSome : ∀ j : Fin (2 * m), (pin (vert j)).isSome = (pin (false, i0)).isSome := by
            intro j
            have hmem : (π^(j.val / 2)) i0 ∈ orb M hb i0 := (mem_orb_iff hb i0 _).2 ⟨j.val / 2, rfl⟩
            by_cases h : j.val % 2 = 0
            · simp only [vert, h, ite_true]
              exact hconst_p i0 _ hmem
            · simp only [vert, h, ite_false]
              have h0 := hfp ((π^(j.val / 2)) i0) 0
              simp only [Fin.castSucc_zero] at h0
              rw [← h0]
              exact hconst_p i0 _ hmem
          intro j
          rw [hv_isSome j, ← hv_isSome s0]
          exact hv0_pin
        have hzero_all : (Finset.univ.filter (fun j : Fin (2 * m) => g j = true)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j _
          have hjp := hall_pin j
          have heq : y (vert j) = z (vert j) := by
            cases hps : pin (vert j) with
            | none => simp [hps] at hjp
            | some b =>
              have hyb : y (vert j) = b := by
                rcases hy (vert j) with h | h
                · rw [hps] at h; cases h
                · rw [hps] at h; exact (Option.some.inj h).symm
              have hzb : z (vert j) = b := by
                rcases hz_ok (vert j) with h | h
                · rw [hps] at h; cases h
                · rw [hps] at h; exact (Option.some.inj h).symm
              rw [hyb, hzb]
          simp [g, heq]
        rw [hzero_all]
        exact Nat.zero_le _
      · have hsub : Finset.univ.filter (fun j : Fin (2 * m) => g j = true) ⊆ Finset.univ.erase s0 := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ _⟩
          rintro rfl
          rw [hs0] at hj
          exact Bool.false_ne_true hj
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hc
        simp only [L, hpart_eq, ite_true]
        omega
    · have hF : (Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = false)).card =
          ((cycV i0).filter (fun v => y v = false)).card := by
        rw [← hvert_img, Finset.filter_image, Finset.card_image_of_injective _ hvert_inj]
      have hT : (Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = true)).card =
          ((cycV i0).filter (fun v => y v = true)).card := by
        rw [← hvert_img, Finset.filter_image, Finset.card_image_of_injective _ hvert_inj]
      have hsumFT : (Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = false)).card +
          (Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = true)).card = 2 * m := by
        have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * m))))
          (fun j => y (vert j) = false)
        have hnot : (Finset.univ.filter (fun j : Fin (2 * m) => ¬ y (vert j) = false)) =
            Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = true) := by
          ext j
          simp
        rw [hnot, Finset.card_univ, Fintype.card_fin] at h
        exact h
      have hLge : d ≤ L := by
        cases partialPins <;> simp [L] <;> omega
      by_cases hlt : ((cycV i0).filter (fun v => y v = false)).card <
          ((cycV i0).filter (fun v => y v = true)).card
      · have hbit : bitOf i0 = true := by simp [bitOf, hp, hlt]
        have hgeq : Finset.univ.filter (fun j : Fin (2 * m) => g j = true) =
            Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = false) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, g, hz_vert, hbit]
          cases y (vert j) <;> decide
        rw [hgeq]
        have hcle : (Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = false)).card ≤ m := by omega
        have hposT : 0 < (Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = true)).card := by omega
        obtain ⟨s0, hs0⟩ := Finset.card_pos.1 hposT
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs0
        refine ⟨by omega, ⟨s0, ?_⟩⟩
        simp [g, hz_vert, hbit, hs0]
      · have hbit : bitOf i0 = false := by simp [bitOf, hp, hlt]
        have hgeq : Finset.univ.filter (fun j : Fin (2 * m) => g j = true) =
            Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = true) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, g, hz_vert, hbit]
          cases y (vert j) <;> decide
        rw [hgeq]
        have hcle : (Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = true)).card ≤ m := by omega
        have hposF : 0 < (Finset.univ.filter (fun j : Fin (2 * m) => y (vert j) = false)).card := by omega
        obtain ⟨s0, hs0⟩ := Finset.card_pos.1 hposF
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs0
        refine ⟨by omega, ⟨s0, ?_⟩⟩
        simp [g, hz_vert, hbit, hs0]
  exact cycle_charge hm_pos hP hQ hPQ g hcard_zero.1 hcard_zero.2

abbrev Idx (d : ℕ) := (Bool × Bool) × Fin d

lemma card_Idx (d : ℕ) : Fintype.card (Idx d) = 4 * d := by
  simp only [Idx, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]

noncomputable def e4 (d : ℕ) : Fin (4 * d) ≃ Idx d :=
  (Fintype.equivFinOfCardEq (card_Idx d)).symm

def m0I (d : ℕ) : Equiv.Perm (Idx d) := 1

def m1I (d : ℕ) : Equiv.Perm (Idx d) where
  toFun p := if p.1.2 then p else (p.1, (finRotate d).symm p.2)
  invFun p := if p.1.2 then p else (p.1, finRotate d p.2)
  left_inv := by
    rintro ⟨⟨r, _ | _⟩, k⟩
    · exact Prod.ext rfl (Equiv.apply_symm_apply (finRotate d) k)
    · rfl
  right_inv := by
    rintro ⟨⟨r, _ | _⟩, k⟩
    · exact Prod.ext rfl (Equiv.symm_apply_apply (finRotate d) k)
    · rfl

def m2I (d : ℕ) : Equiv.Perm (Idx d) where
  toFun p := match p.1 with
    | (false, false) => ((false, true), p.2)
    | (false, true) => ((true, false), Fin.rev p.2)
    | (true, false) => ((true, true), Fin.rev p.2)
    | (true, true) => ((false, false), p.2)
  invFun p := match p.1 with
    | (false, true) => ((false, false), p.2)
    | (true, false) => ((false, true), Fin.rev p.2)
    | (true, true) => ((true, false), Fin.rev p.2)
    | (false, false) => ((true, true), p.2)
  left_inv := by rintro ⟨⟨_ | _, _ | _⟩, k⟩ <;> simp
  right_inv := by rintro ⟨⟨_ | _, _ | _⟩, k⟩ <;> simp

noncomputable def liftP (d : ℕ) (π : Equiv.Perm (Idx d)) : Equiv.Perm (Fin (4 * d)) :=
  (e4 d).trans (π.trans (e4 d).symm)

noncomputable def Mstar (d : ℕ) : Fin 3 → Equiv.Perm (Fin (4 * d)) :=
  fun j => if j = 0 then liftP d (m0I d) else if j = 1 then liftP d (m1I d) else liftP d (m2I d)

lemma finRotate_pow_apply (d : ℕ) : ∀ (t : ℕ) (k : Fin d), ((finRotate d)^t) k =
    ⟨(k.val + t) % d, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) k.isLt)⟩ := by
  intro t
  induction t with
  | zero =>
    intro k
    ext
    simp [Nat.mod_eq_of_lt k.isLt]
  | succ t ih =>
    intro k
    rw [pow_succ', Equiv.Perm.mul_apply, ih k]
    cases d with
    | zero => exact Fin.elim0 k
    | succ d' =>
      let u : Fin (d' + 1) := ⟨(k.val + t) % (d' + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
      change finRotate (d' + 1) u = _
      have hmod_step : (k.val + (t + 1)) % (d' + 1) = ((k.val + t) % (d' + 1) + 1) % (d' + 1) := by
        rw [← Nat.add_assoc, Nat.mod_add_mod]
      by_cases hu : u = Fin.last d'
      · have hval : (k.val + t) % (d' + 1) = d' := by
          have := congrArg Fin.val hu
          simpa [u] using this
        rw [hu, finRotate_last, Fin.ext_iff]
        simp only [Fin.val_zero]
        rw [hmod_step, hval, Nat.mod_self]
      · rw [Fin.ext_iff, coe_finRotate_of_ne_last hu]
        have hne : (k.val + t) % (d' + 1) ≠ d' := by
          intro h
          apply hu
          ext
          simpa [u] using h
        have hlt2 := Nat.mod_lt (k.val + t) (by omega : 0 < d' + 1)
        have hlt : (k.val + t) % (d' + 1) + 1 < d' + 1 := by omega
        change (k.val + t) % (d' + 1) + 1 = (k.val + (t + 1)) % (d' + 1)
        rw [hmod_step, Nat.mod_eq_of_lt hlt]

lemma bounded_Mstar {d : ℕ} (hd : 0 < d) : bounded d (4 * d) (Mstar d) := by
  intro i
  refine ⟨d, hd, le_refl d, ?_⟩
  have hM0 : Mstar d 0 = liftP d (m0I d) := rfl
  have hM1 : Mstar d 1 = liftP d (m1I d) := rfl
  have hπ : (Mstar d 0).trans (Mstar d 1).symm = liftP d ((m1I d).symm) := by
    rw [hM0, hM1]
    ext x
    simp [liftP, m0I]
  rw [hπ]
  have hpow : ∀ t : ℕ, (liftP d ((m1I d).symm))^t = liftP d (((m1I d).symm)^t) := by
    intro t
    induction t with
    | zero =>
      ext x
      simp [liftP]
    | succ t ih =>
      rw [pow_succ, pow_succ, ih]
      ext x
      simp [liftP]
  rw [hpow d]
  have hpowI : ∀ t : ℕ, ∀ p : Idx d, (((m1I d).symm)^t) p =
      if p.1.2 then p else (p.1, ((finRotate d)^t) p.2) := by
    intro t
    induction t with
    | zero =>
      intro p
      cases p.1.2 <;> simp
    | succ t ih =>
      intro p
      rw [pow_succ', Equiv.Perm.mul_apply, ih p]
      rcases p with ⟨⟨r, _ | _⟩, k⟩
      · simp [m1I, pow_succ', Equiv.Perm.mul_apply]
      · simp [m1I]
  simp only [liftP, Equiv.trans_apply, hpowI]
  rcases h : e4 d i with ⟨⟨r, a⟩, k⟩
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte, finRotate_pow_apply, Nat.add_mod_right,
      Nat.mod_eq_of_lt k.isLt, Fin.eta]
    rw [← h, Equiv.symm_apply_apply]
  · simp only [↓reduceIte]
    rw [← h, Equiv.symm_apply_apply]

lemma finRotate_symm_rev {d : ℕ} (k : Fin d) :
    (finRotate d).symm (Fin.rev k) = Fin.rev (finRotate d k) := by
  apply (finRotate d).injective
  rw [Equiv.apply_symm_apply]
  cases d with
  | zero => exact Fin.elim0 k
  | succ d' =>
    have h1 : ∀ u : Fin (d' + 1), (finRotate (d' + 1) u).val = (u.val + 1) % (d' + 1) := by
      intro u
      have := finRotate_pow_apply (d' + 1) 1 u
      simpa using congrArg Fin.val this
    ext
    rw [Fin.val_rev, h1, Fin.val_rev, h1]
    by_cases hk : k.val = d'
    · rw [hk]
      simp
    · have hlt : k.val + 1 < d' + 1 := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have hlt2 : d' + 1 - (k.val + 1 + 1) + 1 < d' + 1 := by omega
      rw [Nat.mod_eq_of_lt hlt2]
      omega

lemma sharpness_test {d : ℕ} (hd : 0 < d) {partialPins : Bool} {H P Q : ℕ}
    (hw : works (4 * d) (Mstar d) partialPins true H P Q)
    (f : Fin (2 * d) → Bool) (j0 : Fin (2 * d)) (hj0 : f j0 = false)
    (hsize : partialPins = true ∨ (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card ≤ d) :
    H * (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card ≤
      P * (Finset.univ.filter (fun k : Fin d =>
        f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩)).card +
      Q * (Finset.univ.filter (fun k : Fin d =>
        f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩)).card := by
  let idxOf : Bool → Bool → Fin d → Fin (2 * d) := fun side r k =>
    match r, side with
    | false, false => ⟨2 * k.val, by omega⟩
    | false, true => ⟨2 * k.val + 1, by omega⟩
    | true, false => ⟨2 * (Fin.rev k).val + 1, by omega⟩
    | true, true => ⟨2 * (Fin.rev k).val, by omega⟩
  let pinI : Bool × Idx d → Option Bool := fun v =>
    match v.2.1 with
    | (r, false) =>
      if partialPins ∧ idxOf v.1 r v.2.2 = j0 then some false else none
    | (false, true) => some (!f ⟨2 * v.2.2.val, by omega⟩)
    | (true, true) => some (!f ⟨2 * v.2.2.val + 1, by omega⟩)
  let pin : Bool × Fin (4 * d) → Option Bool := fun v => pinI (v.1, e4 d v.2)
  have hM0 : Mstar d 0 = liftP d (m0I d) := rfl
  have hM1 : Mstar d 1 = liftP d (m1I d) := rfl
  have hM2 : Mstar d 2 = liftP d (m2I d) := rfl
  have hpin : partialPins = true ∨ ∀ (i : Fin (4 * d)) (j : Fin 2),
      (pin (false, i)).isSome = (pin (true, (Mstar d j.castSucc) i)).isSome := by
    cases hpp : partialPins
    · right
      intro i j
      fin_cases j
      · simp only [Fin.zero_eta, Fin.castSucc_zero, hM0, pin, liftP, Equiv.trans_apply,
          Equiv.apply_symm_apply, m0I, Equiv.Perm.coe_one, id_eq]
        rcases e4 d i with ⟨⟨_ | _, _ | _⟩, k⟩ <;> simp [pinI, hpp]
      · simp only [Fin.mk_one, Fin.castSucc_one, hM1, pin, liftP, Equiv.trans_apply,
          Equiv.apply_symm_apply]
        rcases e4 d i with ⟨⟨_ | _, _ | _⟩, k⟩ <;> simp [pinI, m1I, hpp]
    · exact Or.inl rfl
  let z0I : Bool × Idx d → Bool := fun v =>
    match v.2.1 with
    | (_, false) => false
    | (false, true) => !f ⟨2 * v.2.2.val, by omega⟩
    | (true, true) => !f ⟨2 * v.2.2.val + 1, by omega⟩
  let z0 : Bool × Fin (4 * d) → Bool := fun v => z0I (v.1, e4 d v.2)
  have hz0_ok : ∀ v, pin v = none ∨ pin v = some (z0 v) := by
    intro v
    rcases v with ⟨side, i⟩
    simp only [pin, z0]
    rcases e4 d i with ⟨⟨_ | _, _ | _⟩, k⟩
    · by_cases h : partialPins ∧ idxOf side false k = j0 <;> simp [pinI, z0I, h]
    · simp [pinI, z0I]
    · by_cases h : partialPins ∧ idxOf side true k = j0 <;> simp [pinI, z0I, h]
    · simp [pinI, z0I]
  have hz0_0 : cost (Mstar d) z0 0 = 0 := by
    rw [cost, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    simp only [hM0, z0, liftP, Equiv.trans_apply, Equiv.apply_symm_apply, m0I, Equiv.Perm.coe_one, id_eq, not_not]
    rcases e4 d i with ⟨⟨_ | _, _ | _⟩, k⟩ <;> rfl
  have hz0_1 : cost (Mstar d) z0 1 = 0 := by
    rw [cost, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    simp only [hM1, z0, liftP, Equiv.trans_apply, Equiv.apply_symm_apply, not_not]
    rcases e4 d i with ⟨⟨_ | _, _ | _⟩, k⟩ <;> simp [z0I, m1I]
  let yI : Bool × Idx d → Bool := fun v =>
    match v.2.1 with
    | (r, false) => f (idxOf v.1 r v.2.2)
    | (false, true) => !f ⟨2 * v.2.2.val, by omega⟩
    | (true, true) => !f ⟨2 * v.2.2.val + 1, by omega⟩
  let y : Bool × Fin (4 * d) → Bool := fun v => yI (v.1, e4 d v.2)
  have hy_ok : ∀ v, pin v = none ∨ pin v = some (y v) := by
    intro v
    rcases v with ⟨side, i⟩
    simp only [pin, y]
    rcases e4 d i with ⟨⟨_ | _, _ | _⟩, k⟩
    · by_cases h : partialPins ∧ idxOf side false k = j0
      · right; simp [pinI, yI, h, hj0]
      · left; simp [pinI, h]
    · right; simp [pinI, yI]
    · by_cases h : partialPins ∧ idxOf side true k = j0
      · right; simp [pinI, yI, h, hj0]
      · left; simp [pinI, h]
    · right; simp [pinI, yI]
  obtain ⟨z, hz_ok, hz_0, hz_1, hineq⟩ := hw pin hpin ⟨z0, hz0_ok, hz0_0, hz0_1⟩ y hy_ok
  simp only [ite_true] at hineq
  have hcost_eq : ∀ (w : Bool × Fin (4 * d) → Bool) (π : Equiv.Perm (Idx d)),
      (Finset.univ.filter (fun i : Fin (4 * d) => w (false, i) ≠ w (true, liftP d π i))).card =
      (Finset.univ.filter (fun p : Idx d =>
        w (false, (e4 d).symm p) ≠ w (true, (e4 d).symm (π p)))).card := by
    intro w π
    rw [Finset.card_filter, Finset.card_filter]
    rw [← Equiv.sum_comp (e4 d).symm]
    apply Finset.sum_congr rfl
    intro p _
    simp [liftP]
  have hne_ite : ∀ a b : Bool, (if a ≠ b then (1 : ℕ) else 0) = if b ≠ a then 1 else 0 := by decide
  have hy2 : cost (Mstar d) y 2 = 4 * d := by
    rw [cost, hM2, hcost_eq]
    have hall : ∀ p : Idx d, y (false, (e4 d).symm p) ≠ y (true, (e4 d).symm (m2I d p)) := by
      rintro ⟨⟨_ | _, _ | _⟩, k⟩
      · simp only [y, yI, m2I, idxOf, Equiv.apply_symm_apply, Equiv.coe_fn_mk]; cases f ⟨2 * k.val, by omega⟩ <;> simp
      · simp only [y, yI, m2I, idxOf, Equiv.apply_symm_apply, Equiv.coe_fn_mk, Fin.rev_rev]; cases f ⟨2 * k.val, by omega⟩ <;> simp
      · simp only [y, yI, m2I, idxOf, Equiv.apply_symm_apply, Equiv.coe_fn_mk]; cases f ⟨2 * (Fin.rev k).val + 1, by omega⟩ <;> simp
      · simp only [y, yI, m2I, idxOf, Equiv.apply_symm_apply, Equiv.coe_fn_mk]; cases f ⟨2 * k.val + 1, by omega⟩ <;> simp
    rw [Finset.filter_true_of_mem (fun p _ => hall p), Finset.card_univ, card_Idx]
  have hsum4 : ∀ F : Idx d → ℕ, ∑ p : Idx d, F p =
      (∑ k : Fin d, F ((false, false), k)) + (∑ k : Fin d, F ((false, true), k)) +
      (∑ k : Fin d, F ((true, false), k)) + (∑ k : Fin d, F ((true, true), k)) := by
    intro F
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    ring
  have hy0 : cost (Mstar d) y 0 = 2 * (Finset.univ.filter (fun k : Fin d =>
      f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩)).card := by
    rw [cost, hM0, hcost_eq, Finset.card_filter, Finset.card_filter, hsum4]
    have h00 : ∑ k : Fin d, (if y (false, (e4 d).symm ((false, false), k)) ≠
        y (true, (e4 d).symm (m0I d ((false, false), k))) then 1 else 0) =
        ∑ k : Fin d, (if f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩ then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      simp [y, yI, m0I, idxOf]
    have h01 : ∑ k : Fin d, (if y (false, (e4 d).symm ((false, true), k)) ≠
        y (true, (e4 d).symm (m0I d ((false, true), k))) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      simp [y, yI, m0I]
    have h10 : ∑ k : Fin d, (if y (false, (e4 d).symm ((true, false), k)) ≠
        y (true, (e4 d).symm (m0I d ((true, false), k))) then 1 else 0) =
        ∑ k : Fin d, (if f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩ then 1 else 0) := by
      rw [← Equiv.sum_comp Fin.revPerm]
      apply Finset.sum_congr rfl
      intro k _
      simp only [y, yI, m0I, idxOf, Equiv.apply_symm_apply, Equiv.Perm.coe_one, id_eq,
        Fin.revPerm_apply, Fin.rev_rev]
      exact hne_ite _ _
    have h11 : ∑ k : Fin d, (if y (false, (e4 d).symm ((true, true), k)) ≠
        y (true, (e4 d).symm (m0I d ((true, true), k))) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      simp [y, yI, m0I]
    rw [h00, h01, h10, h11]
    ring
  have hy1 : cost (Mstar d) y 1 = 2 * (Finset.univ.filter (fun k : Fin d =>
      f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩)).card := by
    rw [cost, hM1, hcost_eq, Finset.card_filter, Finset.card_filter, hsum4]
    have h00 : ∑ k : Fin d, (if y (false, (e4 d).symm ((false, false), k)) ≠
        y (true, (e4 d).symm (m1I d ((false, false), k))) then 1 else 0) =
        ∑ k : Fin d, (if f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩ then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      simp [y, yI, m1I, idxOf]
    have h01 : ∑ k : Fin d, (if y (false, (e4 d).symm ((false, true), k)) ≠
        y (true, (e4 d).symm (m1I d ((false, true), k))) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      simp [y, yI, m1I]
    have h10 : ∑ k : Fin d, (if y (false, (e4 d).symm ((true, false), k)) ≠
        y (true, (e4 d).symm (m1I d ((true, false), k))) then 1 else 0) =
        ∑ k : Fin d, (if f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩ then 1 else 0) := by
      rw [← Equiv.sum_comp ((finRotate d).symm.trans Fin.revPerm)]
      apply Finset.sum_congr rfl
      intro k _
      simp only [y, yI, m1I, idxOf, Equiv.apply_symm_apply, Equiv.trans_apply, Equiv.coe_fn_mk,
        Fin.revPerm_apply, Bool.false_eq_true, ↓reduceIte, Fin.rev_rev, finRotate_symm_rev]
      exact hne_ite _ _
    have h11 : ∑ k : Fin d, (if y (false, (e4 d).symm ((true, true), k)) ≠
        y (true, (e4 d).symm (m1I d ((true, true), k))) then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      simp [y, yI, m1I]
    rw [h00, h01, h10, h11]
    ring
  have hz_anchor0 : ∀ side : Bool, ∀ k : Fin d,
      z (side, (e4 d).symm ((false, true), k)) = !f ⟨2 * k.val, by omega⟩ := by
    intro side k
    rcases hz_ok (side, (e4 d).symm ((false, true), k)) with h | h
    · simp [pin, pinI] at h
    · simp only [pin, pinI, Equiv.apply_symm_apply, Option.some.injEq] at h
      exact h.symm
  have hz_anchor1 : ∀ side : Bool, ∀ k : Fin d,
      z (side, (e4 d).symm ((true, true), k)) = !f ⟨2 * k.val + 1, by omega⟩ := by
    intro side k
    rcases hz_ok (side, (e4 d).symm ((true, true), k)) with h | h
    · simp [pin, pinI] at h
    · simp only [pin, pinI, Equiv.apply_symm_apply, Option.some.injEq] at h
      exact h.symm
  have hz_eq0 : ∀ p : Idx d, z (false, (e4 d).symm p) = z (true, (e4 d).symm p) := by
    have hz_0' : (Finset.univ.filter (fun p : Idx d =>
        z (false, (e4 d).symm p) ≠ z (true, (e4 d).symm (m0I d p)))).card = 0 := by
      rw [← hcost_eq]
      exact hz_0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hz_0'
    intro p
    have := hz_0' (Finset.mem_univ p)
    simpa [m0I] using this
  have hz_eq1 : ∀ p : Idx d, z (false, (e4 d).symm p) = z (true, (e4 d).symm (m1I d p)) := by
    have hz_1' : (Finset.univ.filter (fun p : Idx d =>
        z (false, (e4 d).symm p) ≠ z (true, (e4 d).symm (m1I d p)))).card = 0 := by
      rw [← hcost_eq]
      exact hz_1
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hz_1'
    intro p
    have := hz_1' (Finset.mem_univ p)
    simpa using this
  have hz_const_ring : ∀ r : Bool, ∀ side : Bool, ∀ k : Fin d,
      z (side, (e4 d).symm ((r, false), k)) = z (false, (e4 d).symm ((r, false), ⟨0, hd⟩)) := by
    intro r side k
    have hside : z (side, (e4 d).symm ((r, false), k)) = z (false, (e4 d).symm ((r, false), k)) := by
      cases side
      · rfl
      · exact (hz_eq0 _).symm
    rw [hside]
    have hstep : ∀ u : Fin d, z (false, (e4 d).symm ((r, false), finRotate d u)) =
        z (false, (e4 d).symm ((r, false), u)) := by
      intro u
      have h1 := hz_eq1 ((r, false), finRotate d u)
      have hm1 : m1I d ((r, false), finRotate d u) = ((r, false), u) :=
        Prod.ext rfl (Equiv.symm_apply_apply (finRotate d) u)
      rw [hm1] at h1
      rw [h1, ← hz_eq0]
    have hpow : ∀ t : ℕ, z (false, (e4 d).symm ((r, false), ((finRotate d)^t) ⟨0, hd⟩)) =
        z (false, (e4 d).symm ((r, false), ⟨0, hd⟩)) := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih]
    have hk : ((finRotate d)^k.val) ⟨0, hd⟩ = k := by
      rw [finRotate_pow_apply]
      ext
      simp [Nat.mod_eq_of_lt k.isLt]
    rw [← hk, hpow]
  let b0 : Bool := z (false, (e4 d).symm ((false, false), ⟨0, hd⟩))
  let b1 : Bool := z (false, (e4 d).symm ((true, false), ⟨0, hd⟩))
  have hcount_b : ∀ b : Bool,
      (∑ k : Fin d, (if b ≠ !(f ⟨2 * k.val, by omega⟩) then 1 else 0)) +
      (∑ k : Fin d, (if (!(f ⟨2 * k.val + 1, by omega⟩)) ≠ b then 1 else 0)) =
      (Finset.univ.filter (fun j : Fin (2 * d) => f j = b)).card := by
    intro b
    rw [Finset.card_filter]
    have hbi : (Finset.univ : Finset (Fin (2 * d))) =
        (Finset.univ : Finset (Fin d × Bool)).image
          (fun kb => ⟨2 * kb.1.val + if kb.2 then 1 else 0, by
            have := kb.1.isLt; cases kb.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_image, true_and, true_iff]
      refine ⟨(⟨j.val / 2, by omega⟩, decide (j.val % 2 = 1)), ?_⟩
      ext
      by_cases h : j.val % 2 = 1 <;> simp [h] <;> omega
    rw [hbi, Finset.sum_image]
    · rw [Fintype.sum_prod_type]
      have hs : ∑ k : Fin d, ∑ s : Bool,
          (if f ⟨2 * k.val + if s then 1 else 0, by
            have := k.isLt; cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩ = b then 1 else 0) =
          (∑ k : Fin d, (if f ⟨2 * k.val, by omega⟩ = b then 1 else 0)) +
          (∑ k : Fin d, (if f ⟨2 * k.val + 1, by omega⟩ = b then 1 else 0)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Fintype.sum_bool, add_comm]
        simp
      rw [hs]
      congr 1
      · apply Finset.sum_congr rfl
        intro k _
        cases b <;> cases f ⟨2 * k.val, by omega⟩ <;> decide
      · apply Finset.sum_congr rfl
        intro k _
        cases b <;> cases f ⟨2 * k.val + 1, by omega⟩ <;> decide
    · intro a _ c _ h
      rw [Fin.ext_iff] at h
      cases ha : a.2 <;> cases hc : c.2 <;> simp [ha, hc] at h
      · exact Prod.ext (Fin.ext (by omega)) (by rw [ha, hc])
      · omega
      · omega
      · exact Prod.ext (Fin.ext (by omega)) (by rw [ha, hc])
  have hz2 : cost (Mstar d) z 2 =
      (Finset.univ.filter (fun j : Fin (2 * d) => f j = b0)).card +
      (Finset.univ.filter (fun j : Fin (2 * d) => f j = b1)).card := by
    rw [cost, hM2, hcost_eq, Finset.card_filter, hsum4]
    have h00 : ∑ k : Fin d, (if z (false, (e4 d).symm ((false, false), k)) ≠
        z (true, (e4 d).symm (m2I d ((false, false), k))) then 1 else 0) =
        ∑ k : Fin d, (if b0 ≠ !f ⟨2 * k.val, by omega⟩ then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [m2I, Equiv.coe_fn_mk, hz_const_ring, hz_anchor0, b0]
    have h01 : ∑ k : Fin d, (if z (false, (e4 d).symm ((false, true), k)) ≠
        z (true, (e4 d).symm (m2I d ((false, true), k))) then 1 else 0) =
        ∑ k : Fin d, (if b1 ≠ !f ⟨2 * k.val, by omega⟩ then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [m2I, Equiv.coe_fn_mk, hz_const_ring, hz_anchor0, b1]
      exact hne_ite _ _
    have h10 : ∑ k : Fin d, (if z (false, (e4 d).symm ((true, false), k)) ≠
        z (true, (e4 d).symm (m2I d ((true, false), k))) then 1 else 0) =
        ∑ k : Fin d, (if (!(f ⟨2 * k.val + 1, by omega⟩)) ≠ b1 then 1 else 0) := by
      rw [← Equiv.sum_comp Fin.revPerm]
      apply Finset.sum_congr rfl
      intro k _
      have hm2 : m2I d ((true, false), Fin.revPerm k) = ((true, true), k) := by
        simp [m2I]
      rw [hm2, hz_const_ring, hz_anchor1]
      exact hne_ite _ _
    have h11 : ∑ k : Fin d, (if z (false, (e4 d).symm ((true, true), k)) ≠
        z (true, (e4 d).symm (m2I d ((true, true), k))) then 1 else 0) =
        ∑ k : Fin d, (if (!(f ⟨2 * k.val + 1, by omega⟩)) ≠ b0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      have hm2 : m2I d ((true, true), k) = ((false, false), k) := rfl
      rw [hm2, hz_const_ring, hz_anchor1]
    rw [h00, h01, h10, h11, ← hcount_b b0, ← hcount_b b1]
    ring
  have hsum_f : (Finset.univ.filter (fun j : Fin (2 * d) => f j = false)).card +
      (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card = 2 * d := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * d))))
      (fun j => f j = false)
    have hnot : (Finset.univ.filter (fun j : Fin (2 * d) => ¬ f j = false)) =
        Finset.univ.filter (fun j : Fin (2 * d) => f j = true) := by
      ext j; simp
    rw [hnot, Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hz2_le : cost (Mstar d) z 2 ≤ 4 * d - 2 * (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card := by
    rw [hz2]
    rcases hsize with hpp | hsd
    · have hb0 : b0 = false := by
        let k0 : Fin d := ⟨j0.val / 2, by omega⟩
        let s0 : Bool := decide (j0.val % 2 = 1)
        have hidx : idxOf s0 false k0 = j0 := by
          cases hs0 : s0
          · have hmod : j0.val % 2 ≠ 1 := by simpa [s0] using hs0
            ext; simp only [idxOf, k0]; omega
          · have hmod : j0.val % 2 = 1 := by simpa [s0] using hs0
            ext; simp only [idxOf, k0]; omega
        have hok0 := hz_ok (s0, (e4 d).symm ((false, false), k0))
        rw [hz_const_ring false s0 k0] at hok0
        simp only [pin, pinI, Equiv.apply_symm_apply, hpp, hidx, true_and, ite_true] at hok0
        rcases hok0 with h | h
        · cases h
        · exact (Option.some.inj h).symm
      have hb1 : b1 = false := by
        let k0 : Fin d := Fin.rev ⟨j0.val / 2, by omega⟩
        let s0 : Bool := decide (j0.val % 2 = 0)
        have hidx : idxOf s0 true k0 = j0 := by
          cases hs0 : s0
          · have hmod : j0.val % 2 ≠ 0 := by simpa [s0] using hs0
            ext; simp only [idxOf, k0, Fin.rev_rev]; omega
          · have hmod : j0.val % 2 = 0 := by simpa [s0] using hs0
            ext; simp only [idxOf, k0, Fin.rev_rev]; omega
        have hok1 := hz_ok (s0, (e4 d).symm ((true, false), k0))
        rw [hz_const_ring true s0 k0] at hok1
        simp only [pin, pinI, Equiv.apply_symm_apply, hpp, hidx, true_and, ite_true] at hok1
        rcases hok1 with h | h
        · cases h
        · exact (Option.some.inj h).symm
      rw [hb0, hb1]
      omega
    · cases b0 <;> cases b1 <;> omega
  rw [hy2] at hineq
  rw [hy0, hy1] at hineq
  have hle_s : 2 * (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card ≤ 4 * d := by omega
  have hmul : H * (4 * d) ≤ H * (4 * d - 2 * (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card) +
      P * (2 * (Finset.univ.filter (fun k : Fin d =>
        f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩)).card) +
      Q * (2 * (Finset.univ.filter (fun k : Fin d =>
        f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩)).card) :=
    le_trans hineq (by gcongr)
  have hdiff : H * (4 * d) =
      H * (4 * d - 2 * (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card) +
      2 * (H * (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card) := by
    have h1 : H * (4 * d) =
        H * (4 * d - 2 * (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card) +
        H * (2 * (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hle_s]
    linarith
  have hmul2 : 2 * (H * (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card) ≤
      2 * (P * (Finset.univ.filter (fun k : Fin d =>
        f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩)).card +
      Q * (Finset.univ.filter (fun k : Fin d =>
        f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩)).card) := by
    linarith
  omega

lemma nec_works {d : ℕ} (hd : 0 < d) {partialPins : Bool} {H P Q : ℕ}
    (hw : works (4 * d) (Mstar d) partialPins true H P Q) :
    let L := if partialPins then 2 * d - 1 else d
    H * (2 * (L / 2)) ≤ 2 * P ∧ H * (2 * (L / 2)) ≤ 2 * Q ∧
      H * (2 * ((L - 1) / 2) + 1) ≤ P + Q := by
  intro L
  have hL_le : L ≤ 2 * d - 1 := by
    cases partialPins <;> simp [L] <;> omega
  have hL_pos : 1 ≤ L := by
    cases partialPins <;> simp [L] <;> omega
  have hrot_symm : ∀ k : Fin d, ((finRotate d).symm k).val = if k.val = 0 then d - 1 else k.val - 1 := by
    intro k
    have h1 : finRotate d ⟨if k.val = 0 then d - 1 else k.val - 1, by split_ifs <;> omega⟩ = k := by
      have hp := finRotate_pow_apply d 1 ⟨if k.val = 0 then d - 1 else k.val - 1, by split_ifs <;> omega⟩
      simp only [pow_one] at hp
      rw [hp]
      ext
      split_ifs with h0
      · simp [show d - 1 + 1 = d by omega, h0]
      · simp [show k.val - 1 + 1 = k.val by omega, Nat.mod_eq_of_lt k.isLt]
    have h2 := congrArg ((finRotate d).symm) h1
    rw [Equiv.symm_apply_apply] at h2
    rw [← h2]
  refine ⟨?_, ?_, ?_⟩
  · let s := 2 * (L / 2)
    by_cases hs0 : s = 0
    · simp [s, hs0]
    · have hs_ge : 2 ≤ s := by omega
      have hs_lt : s + 1 < 2 * d := by omega
      let f : Fin (2 * d) → Bool := fun j => decide (1 ≤ j.val ∧ j.val ≤ s)
      have hcard : (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card = s := by
        have hbi : (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card =
            (Finset.Icc 1 s).card := by
          apply Finset.card_nbij' (fun j : Fin (2 * d) => j.val)
            (fun k => if h : k < 2 * d then ⟨k, h⟩ else ⟨0, by omega⟩)
          · intro j hj; simp [f] at hj; simp [hj]
          · intro k hk
            simp only [Finset.mem_coe, Finset.mem_Icc] at hk
            have hklt : k < 2 * d := by omega
            simp [hklt, f, hk]
          · intro j _; simp [j.isLt]
          · intro k hk
            simp only [Finset.mem_coe, Finset.mem_Icc] at hk
            have hklt : k < 2 * d := by omega
            simp [hklt]
        rw [hbi, Nat.card_Icc]
        omega
      have hc0 : (Finset.univ.filter (fun k : Fin d =>
          f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩)).card ≤ 2 := by
        have hsub : Finset.univ.filter (fun k : Fin d =>
            f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩) ⊆
            {⟨0, hd⟩, ⟨s / 2, by omega⟩} := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, ne_eq, decide_eq_decide] at hk
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          omega
        exact le_trans (Finset.card_le_card hsub) (Finset.card_le_two)
      have hc1 : (Finset.univ.filter (fun k : Fin d =>
          f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _
        simp only [f, ne_eq, decide_eq_decide, not_not, hrot_symm]
        split_ifs <;> omega
      have htest := sharpness_test hd hw f ⟨0, by omega⟩ (by simp [f])
        (by rw [hcard]; cases partialPins <;> simp [L, s] <;> omega)
      rw [hcard, hc1, mul_zero, add_zero] at htest
      have hmul : P * (Finset.univ.filter (fun k : Fin d =>
          f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩)).card ≤ 2 * P := by
        rw [mul_comm 2 P]
        exact Nat.mul_le_mul_left P hc0
      exact le_trans htest hmul
  · let s := 2 * (L / 2)
    by_cases hs0 : s = 0
    · simp [s, hs0]
    · have hs_ge : 2 ≤ s := by omega
      have hs_lt : s < 2 * d := by omega
      let f : Fin (2 * d) → Bool := fun j => decide (j.val < s)
      have hcard : (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card = s := by
        have hbi : (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card =
            (Finset.range s).card := by
          apply Finset.card_nbij' (fun j : Fin (2 * d) => j.val)
            (fun k => if h : k < 2 * d then ⟨k, h⟩ else ⟨0, by omega⟩)
          · intro j hj; simp [f] at hj; simp [hj]
          · intro k hk
            simp only [Finset.mem_coe, Finset.mem_range] at hk
            have hklt : k < 2 * d := by omega
            simp [hklt, f, hk]
          · intro j _; simp [j.isLt]
          · intro k hk
            simp only [Finset.mem_coe, Finset.mem_range] at hk
            have hklt : k < 2 * d := by omega
            simp [hklt]
        rw [hbi, Finset.card_range]
      have hc0 : (Finset.univ.filter (fun k : Fin d =>
          f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _
        simp only [f, ne_eq, decide_eq_decide, not_not]
        omega
      have hc1 : (Finset.univ.filter (fun k : Fin d =>
          f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩)).card ≤ 2 := by
        have hsub : Finset.univ.filter (fun k : Fin d =>
            f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩) ⊆
            {⟨0, hd⟩, ⟨s / 2, by omega⟩} := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, ne_eq, decide_eq_decide, hrot_symm] at hk
          simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          split_ifs at hk <;> omega
        exact le_trans (Finset.card_le_card hsub) (Finset.card_le_two)
      have htest := sharpness_test hd hw f ⟨2 * d - 1, by omega⟩ (by simp [f]; omega)
        (by rw [hcard]; cases partialPins <;> simp [L, s] <;> omega)
      rw [hcard, hc0, mul_zero, zero_add] at htest
      have hmul : Q * (Finset.univ.filter (fun k : Fin d =>
          f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩)).card ≤ 2 * Q := by
        rw [mul_comm 2 Q]
        exact Nat.mul_le_mul_left Q hc1
      exact le_trans htest hmul
  · let s := 2 * ((L - 1) / 2) + 1
    have hs_lt : s < 2 * d := by omega
    let f : Fin (2 * d) → Bool := fun j => decide (j.val < s)
    have hcard : (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card = s := by
      have hbi : (Finset.univ.filter (fun j : Fin (2 * d) => f j = true)).card =
          (Finset.range s).card := by
        apply Finset.card_nbij' (fun j : Fin (2 * d) => j.val)
          (fun k => if h : k < 2 * d then ⟨k, h⟩ else ⟨0, by omega⟩)
        · intro j hj; simp [f] at hj; simp [hj]
        · intro k hk
          simp only [Finset.mem_coe, Finset.mem_range] at hk
          have hklt : k < 2 * d := by omega
          simp [hklt, f, hk]
        · intro j _; simp [j.isLt]
        · intro k hk
          simp only [Finset.mem_coe, Finset.mem_range] at hk
          have hklt : k < 2 * d := by omega
          simp [hklt]
      rw [hbi, Finset.card_range]
    have hc0 : (Finset.univ.filter (fun k : Fin d =>
        f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩)).card ≤ 1 := by
      have hsub : Finset.univ.filter (fun k : Fin d =>
          f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩) ⊆
          {⟨(L - 1) / 2, by omega⟩} := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, ne_eq, decide_eq_decide] at hk
        simp only [Finset.mem_singleton, Fin.ext_iff]
        omega
      exact le_trans (Finset.card_le_card hsub) (by simp)
    have hc1 : (Finset.univ.filter (fun k : Fin d =>
        f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩)).card ≤ 1 := by
      have hsub : Finset.univ.filter (fun k : Fin d =>
          f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩) ⊆
          {⟨0, hd⟩} := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, ne_eq, decide_eq_decide, hrot_symm] at hk
        simp only [Finset.mem_singleton, Fin.ext_iff]
        split_ifs at hk <;> omega
      exact le_trans (Finset.card_le_card hsub) (by simp)
    have htest := sharpness_test hd hw f ⟨2 * d - 1, by omega⟩ (by simp [f]; omega)
      (by rw [hcard]; cases partialPins <;> simp [L, s] <;> omega)
    rw [hcard] at htest
    have hmul0 : P * (Finset.univ.filter (fun k : Fin d =>
        f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * k.val + 1, by omega⟩)).card ≤ P := by
      simpa using Nat.mul_le_mul_left P hc0
    have hmul1 : Q * (Finset.univ.filter (fun k : Fin d =>
        f ⟨2 * k.val, by omega⟩ ≠ f ⟨2 * ((finRotate d).symm k).val + 1, by omega⟩)).card ≤ Q := by
      simpa using Nat.mul_le_mul_left Q hc1
    exact le_trans htest (Nat.add_le_add hmul0 hmul1)

end PEqualNP.Outside.L_pcx_367_aux

theorem PEqualNP.Outside.L_pcx_367 : ∀ d : ℕ, 0 < d →
  let bounded := fun (n : ℕ) (M : Fin 3 → Equiv.Perm (Fin n)) =>
    ∀ i : Fin n, ∃ t : ℕ, 0 < t ∧ t ≤ d ∧
      (((M 0).trans (M 1).symm)^t) i = i
  let works := fun (n : ℕ) (M : Fin 3 → Equiv.Perm (Fin n))
      (partialPins scoreOnly : Bool) (H P Q : ℕ) =>
    let V := Bool × Fin n
    let X := V → Bool
    let cost := fun (y : X) (j : Fin 3) =>
      (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,M j i))).card
    ∀ pin : V → Option Bool,
      (partialPins = true ∨ ∀ (i : Fin n) (j : Fin 2),
        (pin (false,i)).isSome = (pin (true,M j.castSucc i)).isSome) →
      let ok := fun y : X => ∀ v, pin v = none ∨ pin v = some (y v)
      (∃ z : X, ok z ∧ cost z 0 = 0 ∧ cost z 1 = 0) →
      ∀ y : X, ok y → ∃ z : X, ok z ∧ cost z 0 = 0 ∧ cost z 1 = 0 ∧
        if scoreOnly then H*cost y 2 ≤ H*cost z 2 + P*cost y 0 + Q*cost y 1
        else H*(Finset.univ.filter (fun v : V => y v ≠ z v)).card ≤ P*cost y 0 + Q*cost y 1
  ∃ Mstar : Fin 3 → Equiv.Perm (Fin (4*d)), bounded (4*d) Mstar ∧
    ∀ (partialPins : Bool) (H P Q : ℕ),
      let L := if partialPins then 2*d-1 else d
      let region := H*(2*(L/2)) ≤ 2*P ∧ H*(2*(L/2)) ≤ 2*Q ∧
        H*(2*((L-1)/2)+1) ≤ P+Q
      (region ↔ ∀ (n : ℕ) (M : Fin 3 → Equiv.Perm (Fin n)),
        bounded n M → works n M partialPins false H P Q) ∧
      (region ↔ works (4*d) Mstar partialPins true H P Q) := by
  intro d hd
  refine ⟨PEqualNP.Outside.L_pcx_367_aux.Mstar d, PEqualNP.Outside.L_pcx_367_aux.bounded_Mstar hd, ?_⟩
  intro partialPins H P Q
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨hP, hQ, hPQ⟩ n M hb
    exact PEqualNP.Outside.L_pcx_367_aux.suff_works hd M hb partialPins H P Q hP hQ hPQ
  · intro hall
    exact PEqualNP.Outside.L_pcx_367_aux.nec_works hd
      (PEqualNP.Outside.L_pcx_367_aux.works_false_imp_true
        (hall (4 * d) (PEqualNP.Outside.L_pcx_367_aux.Mstar d)
          (PEqualNP.Outside.L_pcx_367_aux.bounded_Mstar hd)))
  · rintro ⟨hP, hQ, hPQ⟩
    exact PEqualNP.Outside.L_pcx_367_aux.works_false_imp_true
      (PEqualNP.Outside.L_pcx_367_aux.suff_works hd
        (PEqualNP.Outside.L_pcx_367_aux.Mstar d)
        (PEqualNP.Outside.L_pcx_367_aux.bounded_Mstar hd)
        partialPins H P Q hP hQ hPQ)
  · intro hw
    exact PEqualNP.Outside.L_pcx_367_aux.nec_works hd hw
