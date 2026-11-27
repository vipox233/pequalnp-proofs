import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

namespace PEqualNP.Outside.L_lib_678

private abbrev Word (n : ℕ) := Fin n → Bool
private abbrev Lit (n : ℕ) := Fin n × Bool
private abbrev CNF (n : ℕ) := Finset (Lit n × Lit n)
private abbrev B4 := Bool × Bool × Bool × Bool

private def sat {n : ℕ} (C : CNF n) (w : Word n) : Bool :=
  decide (∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)

private def negW {n : ℕ} (w : Word n) : Word n :=
  fun i => !(w i)

private lemma negW_negW {n : ℕ} (w : Word n) : negW (negW w) = w := by
  funext i
  simp [negW]

private lemma card_word (n : ℕ) : Fintype.card (Word n) = 2 ^ n := by
  simp [Word]

private lemma card_filter_add_not {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (s.filter P).card + (s.filter (fun x => ¬ P x)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  calc
    ∑ x ∈ s, ((if P x then (1 : ℕ) else 0) + if ¬ P x then 1 else 0) = ∑ _x ∈ s, (1 : ℕ) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : P x <;> simp [hx]
    _ = s.card := by simp

private lemma involution_two_mul_card_le {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P]
    (f : α → α) (hinv : ∀ x, f (f x) = x) (hdisj : ∀ x, P x → ¬ P (f x)) :
    2 * (Finset.univ.filter P).card ≤ Fintype.card α := by
  have hle : (Finset.univ.filter P).card ≤ (Finset.univ.filter (fun x => ¬ P x)).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hdisj x hx
    · intro x _ y _ hxy
      have := congrArg f hxy
      rwa [hinv x, hinv y] at this
  have htot := card_filter_add_not (Finset.univ : Finset α) P
  rw [Finset.card_univ] at htot
  omega

private lemma count_pairs_ident {n : ℕ} (g : Word n → Bool) :
    let N := (Finset.univ.filter (fun w => g w = true)).card
    let U := (Finset.univ.filter (fun w => g w = true ∧ g (negW w) = true)).card
    let V := (Finset.univ.filter (fun w => g w = false ∧ g (negW w) = false)).card
    2 * N + V = 2 ^ n + U ∧ U + V ≤ 2 ^ n := by
  intro N U V
  let M1 := (Finset.univ.filter (fun w => g w = true ∧ g (negW w) = false)).card
  let M2 := (Finset.univ.filter (fun w => g w = false ∧ g (negW w) = true)).card
  have hM : M1 = M2 := by
    refine Finset.card_bij (fun w _ => negW w) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, negW_negW] at hw ⊢
      exact ⟨hw.2, hw.1⟩
    · intro w1 _ w2 _ h
      have := congrArg negW h
      rwa [negW_negW, negW_negW] at this
    · intro w hw
      refine ⟨negW w, ?_, negW_negW w⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, negW_negW] at hw ⊢
      exact ⟨hw.2, hw.1⟩
  have hN : N = U + M1 := by
    have h1 := card_filter_add_not (Finset.univ.filter (fun w => g w = true))
      (fun w => g (negW w) = true)
    have hU : ((Finset.univ.filter (fun w => g w = true)).filter (fun w => g (negW w) = true)).card = U := by
      congr 1; ext w; simp [Finset.mem_filter]
    have hM1 : ((Finset.univ.filter (fun w => g w = true)).filter (fun w => ¬ g (negW w) = true)).card = M1 := by
      congr 1; ext w; simp [Finset.mem_filter]
    omega
  have hF : (Finset.univ.filter (fun w => g w = false)).card = M2 + V := by
    have h1 := card_filter_add_not (Finset.univ.filter (fun w => g w = false))
      (fun w => g (negW w) = true)
    have hM2 : ((Finset.univ.filter (fun w => g w = false)).filter (fun w => g (negW w) = true)).card = M2 := by
      congr 1; ext w; simp [Finset.mem_filter]
    have hV : ((Finset.univ.filter (fun w => g w = false)).filter (fun w => ¬ g (negW w) = true)).card = V := by
      congr 1; ext w; simp [Finset.mem_filter]
    omega
  have hTot : N + (Finset.univ.filter (fun w => g w = false)).card = 2 ^ n := by
    have h1 := card_filter_add_not (Finset.univ : Finset (Word n)) (fun w => g w = true)
    rw [Finset.card_univ, card_word] at h1
    have h2 : (Finset.univ.filter (fun w => ¬ g w = true)).card =
        (Finset.univ.filter (fun w => g w = false)).card := by
      apply congrArg Finset.card
      ext w
      simp [Finset.mem_filter]
    omega
  omega

private def toggle4 {n : ℕ} (k1 k2 k3 k4 : Fin n) (t : B4) (w : Word n) : Word n :=
  fun i =>
    if i = k1 then xor (w i) t.1
    else if i = k2 then xor (w i) t.2.1
    else if i = k3 then xor (w i) t.2.2.1
    else if i = k4 then xor (w i) t.2.2.2
    else w i

private lemma toggle4_invol {n : ℕ} (k1 k2 k3 k4 : Fin n) (t : B4) (w : Word n) :
    toggle4 k1 k2 k3 k4 t (toggle4 k1 k2 k3 k4 t w) = w := by
  funext i
  simp only [toggle4]
  split_ifs <;> simp

private lemma card_pred4 {n : ℕ} (k1 k2 k3 k4 : Fin n)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h14 : k1 ≠ k4)
    (h23 : k2 ≠ k3) (h24 : k2 ≠ k4) (h34 : k3 ≠ k4)
    (P : B4 → Bool) :
    16 * (Finset.univ.filter (fun w : Word n => P (w k1, w k2, w k3, w k4) = true)).card =
      (Finset.univ.filter (fun t : B4 => P t = true)).card * 2 ^ n := by
  let proj : Word n → B4 := fun w => (w k1, w k2, w k3, w k4)
  let fib : B4 → Finset (Word n) := fun t => Finset.univ.filter (fun w => proj w = t)
  have hfib : ∀ t : B4, (fib t).card = (fib (false, false, false, false)).card := by
    rintro ⟨t1, t2, t3, t4⟩
    refine Finset.card_bij (fun w _ => toggle4 k1 k2 k3 k4 (t1, t2, t3, t4) w) ?_ ?_ ?_
    · intro w hw
      simp only [fib, proj, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hw ⊢
      rcases hw with ⟨hw1, hw2, hw3, hw4⟩
      simp [toggle4, h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm,
        hw1, hw2, hw3, hw4]
    · intro w1 _ w2 _ h
      have := congrArg (toggle4 k1 k2 k3 k4 (t1, t2, t3, t4)) h
      rwa [toggle4_invol, toggle4_invol] at this
    · intro w hw
      refine ⟨toggle4 k1 k2 k3 k4 (t1, t2, t3, t4) w, ?_,
        toggle4_invol k1 k2 k3 k4 (t1, t2, t3, t4) w⟩
      simp only [fib, proj, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hw ⊢
      rcases hw with ⟨hw1, hw2, hw3, hw4⟩
      simp [toggle4, h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm,
        hw1, hw2, hw3, hw4]
  have hcount : ∀ Q : B4 → Bool,
      (Finset.univ.filter (fun w : Word n => Q (proj w) = true)).card =
        (Finset.univ.filter (fun t : B4 => Q t = true)).card *
          (fib (false, false, false, false)).card := by
    intro Q
    rw [Finset.card_eq_sum_card_fiberwise (f := proj)
      (t := Finset.univ.filter (fun t : B4 => Q t = true))]
    · calc
        ∑ t ∈ Finset.univ.filter (fun t : B4 => Q t = true),
            ((Finset.univ.filter (fun w : Word n => Q (proj w) = true)).filter
              (fun w => proj w = t)).card
          = ∑ t ∈ Finset.univ.filter (fun t : B4 => Q t = true), (fib t).card := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
              congr 1
              ext w
              simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h; exact h.2
              · intro h; exact ⟨h ▸ ht, h⟩
        _ = ∑ _t ∈ Finset.univ.filter (fun t : B4 => Q t = true),
              (fib (false, false, false, false)).card := by
              refine Finset.sum_congr rfl ?_
              intro t _; exact hfib t
        _ = (Finset.univ.filter (fun t : B4 => Q t = true)).card *
              (fib (false, false, false, false)).card := by
              rw [Finset.sum_const, smul_eq_mul]
    · intro w hw
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw
  have htot := hcount (fun _ => true)
  simp only [Finset.filter_true, Finset.card_univ, card_word] at htot
  have hB4' : Fintype.card B4 = 16 := by decide
  rw [hB4'] at htot
  rw [hcount P, htot]
  ac_rfl

private def nontaut {n : ℕ} (c : Lit n × Lit n) : Prop :=
  ¬ (c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2)

private lemma sat_iff_nontaut {n : ℕ} (A : CNF n) (w : Word n) :
    sat A w = true ↔ ∀ c ∈ A, nontaut c → w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2 := by
  simp only [sat, decide_eq_true_eq]
  constructor
  · intro h c hc _; exact h c hc
  · intro h c hc
    by_cases hnt : nontaut c
    · exact h c hc hnt
    · simp only [nontaut, not_not] at hnt
      rcases hnt with ⟨h1, h2⟩
      rw [← h1]
      cases hw : w c.1.1 <;> cases hb1 : c.1.2 <;> cases hb2 : c.2.2 <;> simp_all

private lemma no_unit_of_above_half {n : ℕ} (A : CNF n)
    (hN : 2 ^ n < 2 * (Finset.univ.filter (fun w => sat A w = true)).card)
    (c : Lit n × Lit n) (hc : c ∈ A) (hnt : nontaut c) : c.1.1 ≠ c.2.1 := by
  intro heq
  have hb : c.1.2 = c.2.2 := by
    by_contra hne
    exact hnt ⟨heq, hne⟩
  let f : Word n → Word n := fun w i => if i = c.1.1 then !(w i) else w i
  have hinv : ∀ w, f (f w) = w := by
    intro w; funext i; simp only [f]; split_ifs <;> simp
  have hdisj : ∀ w, sat A w = true → ¬ sat A (f w) = true := by
    intro w hw hfw
    have h1 := (sat_iff_nontaut A w).mp hw c hc hnt
    have h2 := (sat_iff_nontaut A (f w)).mp hfw c hc hnt
    simp [f, ← heq, ← hb] at h1 h2
    cases hwi : w c.1.1 <;> cases hc1 : c.1.2 <;> simp_all
  have hle := involution_two_mul_card_le (fun w => sat A w = true) f hinv hdisj
  rw [card_word] at hle
  omega

private lemma no_shared_var_opp {n : ℕ} (A : CNF n)
    (hN : 2 ^ n < 2 * (Finset.univ.filter (fun w => sat A w = true)).card)
    (i j1 j2 : Fin n) (b1 d1 d2 : Bool) (hj1 : j1 ≠ i) (hj2 : j2 ≠ i)
    (h1 : ∀ w, sat A w = true → w i ≠ b1 ∨ w j1 ≠ d1)
    (h2 : ∀ w, sat A w = true → w i ≠ !b1 ∨ w j2 ≠ d2) : False := by
  let f : Word n → Word n := fun w k =>
    if w i = b1 then (if k = j1 then !(w k) else w k)
    else (if k = j2 then !(w k) else w k)
  have hfi : ∀ w, f w i = w i := by
    intro w
    simp only [f]
    split_ifs <;> simp_all [hj1.symm, hj2.symm]
  have hinv : ∀ w, f (f w) = w := by
    intro w
    funext k
    simp only [f, hfi w]
    split_ifs <;> simp
  have hdisj : ∀ w, sat A w = true → ¬ sat A (f w) = true := by
    intro w hw hfw
    by_cases hwi : w i = b1
    · have h1w := h1 w hw
      have h1f := h1 (f w) hfw
      have hfwi : f w i = b1 := by rw [hfi, hwi]
      have hfwj : f w j1 = !(w j1) := by simp [f, hwi]
      rw [hwi] at h1w
      rw [hfwi, hfwj] at h1f
      cases hwj : w j1 <;> cases d1 <;> simp_all
    · have hwi' : w i = !b1 := by cases h : w i <;> cases b1 <;> simp_all
      have h2w := h2 w hw
      have h2f := h2 (f w) hfw
      have hfwi : f w i = !b1 := by rw [hfi, hwi']
      have hfwj : f w j2 = !(w j2) := by simp [f, hwi]
      rw [hwi'] at h2w
      rw [hfwi, hfwj] at h2f
      cases hwj : w j2 <;> cases d2 <;> simp_all
  have hle := involution_two_mul_card_le (fun w => sat A w = true) f hinv hdisj
  rw [card_word] at hle
  omega

private def sameClause {n : ℕ} (c d : Lit n × Lit n) : Prop :=
  (c.1 = d.1 ∧ c.2 = d.2) ∨ (c.1 = d.2 ∧ c.2 = d.1)

private def predC1C2 (b1 b2 b3 b4 : Bool) (t : B4) : Bool :=
  (t.1 != b1 || t.2.1 != b2) && (t.2.2.1 != b3 || t.2.2.2 != b4)

private lemma card_predC1C2 (b1 b2 b3 b4 : Bool) :
    (Finset.univ.filter (fun t : B4 => predC1C2 b1 b2 b3 b4 t = true)).card = 9 := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

private lemma card_predEq (v1 v2 v3 v4 : Bool) :
    (Finset.univ.filter (fun t : B4 =>
      ((t.1 == v1) && (t.2.1 == v2) && (t.2.2.1 == v3) && (t.2.2.2 == v4)) = true)).card = 1 := by
  cases v1 <;> cases v2 <;> cases v3 <;> cases v4 <;> decide

private lemma card_predBothTrue (b1 b2 b3 b4 : Bool) :
    (Finset.univ.filter (fun t : B4 =>
      (predC1C2 b1 b2 b3 b4 t && predC1C2 b1 b2 b3 b4 (!t.1, !t.2.1, !t.2.2.1, !t.2.2.2)) = true)).card = 4 := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

private lemma card_predBothFalse (b1 b2 b3 b4 : Bool) :
    (Finset.univ.filter (fun t : B4 =>
      (!(predC1C2 b1 b2 b3 b4 t) && !(predC1C2 b1 b2 b3 b4 (!t.1, !t.2.1, !t.2.2.1, !t.2.2.2))) = true)).card = 2 := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

private lemma exists_fix_one_in {n : ℕ}
    (i1 i2 i3 i4 ja jb : Fin n) (b1 b2 b3 b4 da db : Bool)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h14 : i1 ≠ i4)
    (h23 : i2 ≠ i3) (_h24 : i2 ≠ i4) (h34 : i3 ≠ i4)
    (hja : ja = i1 ∨ ja = i2 ∨ ja = i3 ∨ ja = i4)
    (hjb1 : jb ≠ i1) (hjb2 : jb ≠ i2) (hjb3 : jb ≠ i3) (hjb4 : jb ≠ i4) :
    ∃ (k1 k2 k3 k4 : Fin n) (v1 v2 v3 v4 : Bool),
      k1 ≠ k2 ∧ k1 ≠ k3 ∧ k1 ≠ k4 ∧ k2 ≠ k3 ∧ k2 ≠ k4 ∧ k3 ≠ k4 ∧
      ∀ w : Word n, w k1 = v1 → w k2 = v2 → w k3 = v3 → w k4 = v4 →
        (w i1 ≠ b1 ∨ w i2 ≠ b2) ∧ (w i3 ≠ b3 ∨ w i4 ≠ b4) ∧ w ja = da ∧ w jb = db := by
  rcases hja with hja | hja | hja | hja
  · rw [hja]
    refine ⟨i1, i2, i3, jb, da, !b2, !b3, db,
      h12, h13, hjb1.symm, h23, hjb2.symm, hjb3.symm, ?_⟩
    intro w h1 h2 h3 h4
    exact ⟨Or.inr (by rw [h2]; cases b2 <;> decide),
      Or.inl (by rw [h3]; cases b3 <;> decide), h1, h4⟩
  · rw [hja]
    refine ⟨i1, i2, i3, jb, !b1, da, !b3, db,
      h12, h13, hjb1.symm, h23, hjb2.symm, hjb3.symm, ?_⟩
    intro w h1 h2 h3 h4
    exact ⟨Or.inl (by rw [h1]; cases b1 <;> decide),
      Or.inl (by rw [h3]; cases b3 <;> decide), h2, h4⟩
  · rw [hja]
    refine ⟨i1, i3, i4, jb, !b1, da, !b4, db,
      h13, h14, hjb1.symm, h34, hjb3.symm, hjb4.symm, ?_⟩
    intro w h1 h2 h3 h4
    exact ⟨Or.inl (by rw [h1]; cases b1 <;> decide),
      Or.inr (by rw [h3]; cases b4 <;> decide), h2, h4⟩
  · rw [hja]
    refine ⟨i1, i3, i4, jb, !b1, !b3, da, db,
      h13, h14, hjb1.symm, h34, hjb3.symm, hjb4.symm, ?_⟩
    intro w h1 h2 h3 h4
    exact ⟨Or.inl (by rw [h1]; cases b1 <;> decide),
      Or.inl (by rw [h2]; cases b3 <;> decide), h3, h4⟩

private lemma exists_fix_third_clause {n : ℕ}
    (i1 i2 i3 i4 j1 j2 : Fin n) (b1 b2 b3 b4 d1 d2 : Bool)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h14 : i1 ≠ i4)
    (h23 : i2 ≠ i3) (h24 : i2 ≠ i4) (h34 : i3 ≠ i4)
    (hj12 : j1 ≠ j2)
    (hns1 : ¬ sameClause ((j1, d1), (j2, d2)) ((i1, b1), (i2, b2)))
    (hns2 : ¬ sameClause ((j1, d1), (j2, d2)) ((i3, b3), (i4, b4))) :
    ∃ (k1 k2 k3 k4 : Fin n) (v1 v2 v3 v4 : Bool),
      k1 ≠ k2 ∧ k1 ≠ k3 ∧ k1 ≠ k4 ∧ k2 ≠ k3 ∧ k2 ≠ k4 ∧ k3 ≠ k4 ∧
      ∀ w : Word n, w k1 = v1 → w k2 = v2 → w k3 = v3 → w k4 = v4 →
        (w i1 ≠ b1 ∨ w i2 ≠ b2) ∧ (w i3 ≠ b3 ∨ w i4 ≠ b4) ∧ w j1 = d1 ∧ w j2 = d2 := by
  by_cases hj1 : j1 = i1 ∨ j1 = i2 ∨ j1 = i3 ∨ j1 = i4
  · by_cases hj2 : j2 = i1 ∨ j2 = i2 ∨ j2 = i3 ∨ j2 = i4
    · let v1 : Bool := if j1 = i1 then d1 else if j2 = i1 then d2 else !b1
      let v2 : Bool := if j1 = i2 then d1 else if j2 = i2 then d2 else !b2
      let v3 : Bool := if j1 = i3 then d1 else if j2 = i3 then d2 else !b3
      let v4 : Bool := if j1 = i4 then d1 else if j2 = i4 then d2 else !b4
      refine ⟨i1, i2, i3, i4, v1, v2, v3, v4, h12, h13, h14, h23, h24, h34, ?_⟩
      intro w hw1 hw2 hw3 hw4
      have hsat1 : v1 ≠ b1 ∨ v2 ≠ b2 := by
        by_contra h
        push Not at h
        rcases h with ⟨hv1, hv2⟩
        by_cases ha1 : j1 = i1
        · subst ha1
          have h1d : d1 = b1 := by simpa [v1] using hv1
          by_cases hb2 : j2 = i2
          · subst hb2
            have h2d : d2 = b2 := by simpa [v2, hj12] using hv2
            exact hns1 (Or.inl ⟨by simp [h1d], by simp [h2d]⟩)
          · simp [v2, h12, hb2] at hv2
        · by_cases hb1 : j2 = i1
          · subst hb1
            have h2d : d2 = b1 := by simpa [v1, ha1] using hv1
            by_cases ha2 : j1 = i2
            · subst ha2
              have h1d : d1 = b2 := by simpa [v2] using hv2
              exact hns1 (Or.inr ⟨by simp [h1d], by simp [h2d]⟩)
            · simp [v2, ha2, h12] at hv2
          · simp [v1, ha1, hb1] at hv1
      have hsat2 : v3 ≠ b3 ∨ v4 ≠ b4 := by
        by_contra h
        push Not at h
        rcases h with ⟨hv3, hv4⟩
        by_cases ha3 : j1 = i3
        · subst ha3
          have h1d : d1 = b3 := by simpa [v3] using hv3
          by_cases hb4 : j2 = i4
          · subst hb4
            have h2d : d2 = b4 := by simpa [v4, hj12] using hv4
            exact hns2 (Or.inl ⟨by simp [h1d], by simp [h2d]⟩)
          · simp [v4, h34, hb4] at hv4
        · by_cases hb3 : j2 = i3
          · subst hb3
            have h2d : d2 = b3 := by simpa [v3, ha3] using hv3
            by_cases ha4 : j1 = i4
            · subst ha4
              have h1d : d1 = b4 := by simpa [v4] using hv4
              exact hns2 (Or.inr ⟨by simp [h1d], by simp [h2d]⟩)
            · simp [v4, ha4, h34] at hv4
          · simp [v3, ha3, hb3] at hv3
      have hwj1 : w j1 = d1 := by
        rcases hj1 with rfl | rfl | rfl | rfl
        · simpa [v1] using hw1
        · simpa [v2] using hw2
        · simpa [v3] using hw3
        · simpa [v4] using hw4
      have hwj2 : w j2 = d2 := by
        rcases hj2 with rfl | rfl | rfl | rfl
        · simpa [v1, hj12] using hw1
        · simpa [v2, hj12] using hw2
        · simpa [v3, hj12] using hw3
        · simpa [v4, hj12] using hw4
      exact ⟨by rwa [hw1, hw2], by rwa [hw3, hw4], hwj1, hwj2⟩
    · push Not at hj2
      exact exists_fix_one_in i1 i2 i3 i4 j1 j2 b1 b2 b3 b4 d1 d2
        h12 h13 h14 h23 h24 h34 hj1 hj2.1 hj2.2.1 hj2.2.2.1 hj2.2.2.2
  · push Not at hj1
    by_cases hj2 : j2 = i1 ∨ j2 = i2 ∨ j2 = i3 ∨ j2 = i4
    · rcases exists_fix_one_in i1 i2 i3 i4 j2 j1 b1 b2 b3 b4 d2 d1
        h12 h13 h14 h23 h24 h34 hj2 hj1.1 hj1.2.1 hj1.2.2.1 hj1.2.2.2 with
        ⟨k1, k2, k3, k4, v1, v2, v3, v4, hk12, hk13, hk14, hk23, hk24, hk34, h⟩
      refine ⟨k1, k2, k3, k4, v1, v2, v3, v4, hk12, hk13, hk14, hk23, hk24, hk34, ?_⟩
      intro w h1 h2 h3 h4
      rcases h w h1 h2 h3 h4 with ⟨hs1, hs2, hwb, hwa⟩
      exact ⟨hs1, hs2, hwa, hwb⟩
    · push Not at hj2
      refine ⟨i1, i3, j1, j2, !b1, !b3, d1, d2,
        h13, hj1.1.symm, hj2.1.symm, hj1.2.2.1.symm, hj2.2.2.1.symm, hj12, ?_⟩
      intro w h1 h2 h3 h4
      exact ⟨Or.inl (by rw [h1]; cases b1 <;> decide),
        Or.inl (by rw [h2]; cases b3 <;> decide), h3, h4⟩

private lemma two_mul_V_le_U {n : ℕ} (A : CNF n)
    (hN : 2 ^ n < 2 * (Finset.univ.filter (fun w => sat A w = true)).card) :
    2 * (Finset.univ.filter (fun w => sat A w = false ∧ sat A (negW w) = false)).card ≤
      (Finset.univ.filter (fun w => sat A w = true ∧ sat A (negW w) = true)).card := by
  by_cases hempty : ∀ c ∈ A, ¬ nontaut c
  · have hV0 : (Finset.univ.filter (fun w => sat A w = false ∧ sat A (negW w) = false)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _ hw
      have htrue : sat A w = true := (sat_iff_nontaut A w).mpr (fun c hc hnt => (hempty c hc hnt).elim)
      rw [htrue] at hw
      exact Bool.noConfusion hw.1
    omega
  by_cases hstar : ∃ L0 : Lit n, ∀ c ∈ A, nontaut c → c.1 = L0 ∨ c.2 = L0
  · rcases hstar with ⟨⟨i0, b0⟩, hL0⟩
    have hV0 : (Finset.univ.filter (fun w => sat A w = false ∧ sat A (negW w) = false)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _ hw
      by_cases hwi : w i0 = b0
      · have htrue : sat A (negW w) = true := by
          refine (sat_iff_nontaut A (negW w)).mpr ?_
          intro c hc hnt
          rcases hL0 c hc hnt with h1 | h2
          · left; rw [h1]; simp only [negW, hwi]; cases b0 <;> decide
          · right; rw [h2]; simp only [negW, hwi]; cases b0 <;> decide
        rw [htrue] at hw
        exact Bool.noConfusion hw.2
      · have htrue : sat A w = true := by
          refine (sat_iff_nontaut A w).mpr ?_
          intro c hc hnt
          rcases hL0 c hc hnt with h1 | h2
          · left; rw [h1]; exact hwi
          · right; rw [h2]; exact hwi
        rw [htrue] at hw
        exact Bool.noConfusion hw.1
    omega
  have hnounit : ∀ c ∈ A, nontaut c → c.1.1 ≠ c.2.1 := no_unit_of_above_half A hN
  by_cases hdisj : ∃ c1 ∈ A, ∃ c2 ∈ A, nontaut c1 ∧ nontaut c2 ∧
      c1.1 ≠ c2.1 ∧ c1.1 ≠ c2.2 ∧ c1.2 ≠ c2.1 ∧ c1.2 ≠ c2.2
  · rcases hdisj with ⟨c1, hc1, c2, hc2, hnt1, hnt2, hd11, hd12, hd21, hd22⟩
    have h12 : c1.1.1 ≠ c1.2.1 := hnounit c1 hc1 hnt1
    have h34 : c2.1.1 ≠ c2.2.1 := hnounit c2 hc2 hnt2
    have h13 : c1.1.1 ≠ c2.1.1 := by
      intro heq
      have hb : c2.1.2 = !c1.1.2 := by
        cases h1 : c1.1.2 <;> cases h2 : c2.1.2
        · exfalso; exact hd11 (Prod.ext heq (h1.trans h2.symm))
        · rfl
        · rfl
        · exfalso; exact hd11 (Prod.ext heq (h1.trans h2.symm))
      exact no_shared_var_opp A hN c1.1.1 c1.2.1 c2.2.1 c1.1.2 c1.2.2 c2.2.2
        h12.symm (heq ▸ h34.symm)
        (fun w hw => (sat_iff_nontaut A w).mp hw c1 hc1 hnt1)
        (fun w hw => by
          have := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
          rwa [← heq, hb] at this)
    have h14 : c1.1.1 ≠ c2.2.1 := by
      intro heq
      have hb : c2.2.2 = !c1.1.2 := by
        cases h1 : c1.1.2 <;> cases h2 : c2.2.2
        · exfalso; exact hd12 (Prod.ext heq (h1.trans h2.symm))
        · rfl
        · rfl
        · exfalso; exact hd12 (Prod.ext heq (h1.trans h2.symm))
      exact no_shared_var_opp A hN c1.1.1 c1.2.1 c2.1.1 c1.1.2 c1.2.2 c2.1.2
        h12.symm (heq ▸ h34)
        (fun w hw => (sat_iff_nontaut A w).mp hw c1 hc1 hnt1)
        (fun w hw => by
          have := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
          rw [← heq, hb] at this
          exact this.symm)
    have h23 : c1.2.1 ≠ c2.1.1 := by
      intro heq
      have hb : c2.1.2 = !c1.2.2 := by
        cases h1 : c1.2.2 <;> cases h2 : c2.1.2
        · exfalso; exact hd21 (Prod.ext heq (h1.trans h2.symm))
        · rfl
        · rfl
        · exfalso; exact hd21 (Prod.ext heq (h1.trans h2.symm))
      exact no_shared_var_opp A hN c1.2.1 c1.1.1 c2.2.1 c1.2.2 c1.1.2 c2.2.2
        h12 (heq ▸ h34.symm)
        (fun w hw => ((sat_iff_nontaut A w).mp hw c1 hc1 hnt1).symm)
        (fun w hw => by
          have := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
          rwa [← heq, hb] at this)
    have h24 : c1.2.1 ≠ c2.2.1 := by
      intro heq
      have hb : c2.2.2 = !c1.2.2 := by
        cases h1 : c1.2.2 <;> cases h2 : c2.2.2
        · exfalso; exact hd22 (Prod.ext heq (h1.trans h2.symm))
        · rfl
        · rfl
        · exfalso; exact hd22 (Prod.ext heq (h1.trans h2.symm))
      exact no_shared_var_opp A hN c1.2.1 c1.1.1 c2.1.1 c1.2.2 c1.1.2 c2.1.2
        h12 (heq ▸ h34)
        (fun w hw => ((sat_iff_nontaut A w).mp hw c1 hc1 hnt1).symm)
        (fun w hw => by
          have := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
          rw [← heq, hb] at this
          exact this.symm)
    have hall : ∀ c3 ∈ A, nontaut c3 → sameClause c3 c1 ∨ sameClause c3 c2 := by
      intro c3 hc3 hnt3
      by_contra hno
      push Not at hno
      rcases exists_fix_third_clause c1.1.1 c1.2.1 c2.1.1 c2.2.1 c3.1.1 c3.2.1
        c1.1.2 c1.2.2 c2.1.2 c2.2.2 c3.1.2 c3.2.2
        h12 h13 h14 h23 h24 h34 (hnounit c3 hc3 hnt3) hno.1 hno.2 with
        ⟨k1, k2, k3, k4, v1, v2, v3, v4, hk12, hk13, hk14, hk23, hk24, hk34, hfix⟩
      let S_sat := Finset.univ.filter (fun w : Word n => sat A w = true)
      let S_c12 := Finset.univ.filter (fun w : Word n =>
        predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2 (w c1.1.1, w c1.2.1, w c2.1.1, w c2.2.1) = true)
      let S_fix := Finset.univ.filter (fun w : Word n =>
        ((w k1 == v1) && (w k2 == v2) && (w k3 == v3) && (w k4 == v4)) = true)
      have hsub1 : S_sat ⊆ S_c12 := by
        intro w hw
        simp only [S_sat, S_c12, Finset.mem_filter, Finset.mem_univ, true_and, predC1C2,
          Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at hw ⊢
        exact ⟨(sat_iff_nontaut A w).mp hw c1 hc1 hnt1, (sat_iff_nontaut A w).mp hw c2 hc2 hnt2⟩
      have hsub2 : S_fix ⊆ S_c12 := by
        intro w hw
        simp only [S_fix, S_c12, Finset.mem_filter, Finset.mem_univ, true_and, predC1C2,
          Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hw ⊢
        rcases hw with ⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩
        have hf := hfix w hw1 hw2 hw3 hw4
        exact ⟨hf.1, hf.2.1⟩
      have hdisjS : Disjoint S_sat S_fix := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        simp only [S_sat, Finset.mem_filter, Finset.mem_univ, true_and] at hw1
        simp only [S_fix, Finset.mem_filter, Finset.mem_univ, true_and,
          Bool.and_eq_true, beq_iff_eq] at hw2
        rcases hw2 with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        have hf := hfix w h1 h2 h3 h4
        have hc3s := (sat_iff_nontaut A w).mp hw1 c3 hc3 hnt3
        rcases hc3s with ha | hb
        · exact ha hf.2.2.1
        · exact hb hf.2.2.2
      have hcard_le : S_sat.card + S_fix.card ≤ S_c12.card := by
        rw [← Finset.card_union_of_disjoint hdisjS]
        exact Finset.card_le_card (Finset.union_subset hsub1 hsub2)
      have hS_sat : S_sat.card = (Finset.univ.filter (fun w => sat A w = true)).card := rfl
      have hS_c12 : 16 * S_c12.card = 9 * 2 ^ n := by
        have := card_pred4 c1.1.1 c1.2.1 c2.1.1 c2.2.1 h12 h13 h14 h23 h24 h34
          (predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2)
        rw [card_predC1C2] at this
        exact this
      have hS_fix : 16 * S_fix.card = 1 * 2 ^ n := by
        have := card_pred4 k1 k2 k3 k4 hk12 hk13 hk14 hk23 hk24 hk34
          (fun t : B4 => (t.1 == v1) && (t.2.1 == v2) && (t.2.2.1 == v3) && (t.2.2.2 == v4))
        rw [card_predEq] at this
        exact this
      omega
    have hsat_eq : ∀ w : Word n,
        sat A w = predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2 (w c1.1.1, w c1.2.1, w c2.1.1, w c2.2.1) := by
      intro w
      apply Bool.eq_iff_iff.mpr
      rw [sat_iff_nontaut]
      simp only [predC1C2, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
      constructor
      · intro h
        exact ⟨h c1 hc1 hnt1, h c2 hc2 hnt2⟩
      · rintro ⟨hs1, hs2⟩ c hc hnt
        rcases hall c hc hnt with (⟨e1, e2⟩ | ⟨e1, e2⟩) | (⟨e1, e2⟩ | ⟨e1, e2⟩)
        · rw [e1, e2]; exact hs1
        · rw [e1, e2]; exact hs1.symm
        · rw [e1, e2]; exact hs2
        · rw [e1, e2]; exact hs2.symm
    have hU : 16 * (Finset.univ.filter (fun w => sat A w = true ∧ sat A (negW w) = true)).card =
        4 * 2 ^ n := by
      have h1 := card_pred4 c1.1.1 c1.2.1 c2.1.1 c2.2.1 h12 h13 h14 h23 h24 h34
        (fun t : B4 => predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2 t &&
          predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2 (!t.1, !t.2.1, !t.2.2.1, !t.2.2.2))
      rw [card_predBothTrue] at h1
      convert h1 using 2
      congr 1
      ext w
      simp [Finset.mem_filter, hsat_eq, negW]
    have hV : 16 * (Finset.univ.filter (fun w => sat A w = false ∧ sat A (negW w) = false)).card =
        2 * 2 ^ n := by
      have h1 := card_pred4 c1.1.1 c1.2.1 c2.1.1 c2.2.1 h12 h13 h14 h23 h24 h34
        (fun t : B4 => !(predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2 t) &&
          !(predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2 (!t.1, !t.2.1, !t.2.2.1, !t.2.2.2)))
      rw [card_predBothFalse] at h1
      convert h1 using 2
      congr 1
      ext w
      simp [Finset.mem_filter, hsat_eq, negW]
    omega
  · exfalso
    push Not at hempty hstar hdisj
    rcases hempty with ⟨c1, hc1, hnt1⟩
    rcases hstar c1.1 with ⟨c2, hc2, hnt2, h21, h22⟩
    have h12_share : c1.2 = c2.1 ∨ c1.2 = c2.2 := by
      by_contra h
      push Not at h
      exact h.2 (hdisj c1 hc1 c2 hc2 hnt1 hnt2 h21.symm h22.symm h.1)
    let L1 := c1.1
    let L2 := c1.2
    let L3 := if c2.1 = L2 then c2.2 else c2.1
    have hc2_eq : (c2.1 = L2 ∧ c2.2 = L3) ∨ (c2.1 = L3 ∧ c2.2 = L2) := by
      rcases h12_share with h | h
      · left; exact ⟨h.symm, by simp [L3, L2, h.symm]⟩
      · by_cases h' : c2.1 = L2
        · left; exact ⟨h', by simp [L3, h']⟩
        · right; exact ⟨by simp [L3, h'], h.symm⟩
    have hL3neL1 : L3 ≠ L1 := by
      rcases hc2_eq with ⟨_, e2⟩ | ⟨e1, _⟩
      · rw [← e2]; exact h22
      · rw [← e1]; exact h21
    rcases hstar L2 with ⟨c3, hc3, hnt3, h31, h32⟩
    have hL1_in_c3 : L1 = c3.1 ∨ L1 = c3.2 := by
      by_contra h
      push Not at h
      exact h32.symm (hdisj c1 hc1 c3 hc3 hnt1 hnt3 h.1 h.2 h31.symm)
    have hL3_in_c3 : L3 = c3.1 ∨ L3 = c3.2 := by
      by_contra h
      push Not at h
      rcases hc2_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact h.2 (e2 ▸ hdisj c2 hc2 c3 hc3 hnt2 hnt3 (e1.symm ▸ h31.symm) (e1.symm ▸ h32.symm) (e2.symm ▸ h.1))
      · exact h32.symm (e2 ▸ hdisj c2 hc2 c3 hc3 hnt2 hnt3 (e1.symm ▸ h.1) (e1.symm ▸ h.2) (e2.symm ▸ h31.symm))
    have hc3_eq : (c3.1 = L1 ∧ c3.2 = L3) ∨ (c3.1 = L3 ∧ c3.2 = L1) := by
      rcases hL1_in_c3 with h1 | h1 <;> rcases hL3_in_c3 with h3 | h3
      · exfalso; exact hL3neL1 (h3.trans h1.symm)
      · left; exact ⟨h1.symm, h3.symm⟩
      · right; exact ⟨h3.symm, h1.symm⟩
      · exfalso; exact hL3neL1 (h3.trans h1.symm)
    let f : Word n → Word n := fun w i =>
      if i = L1.1 ∨ i = L2.1 ∨ i = L3.1 then !(w i) else w i
    have hinv : ∀ w, f (f w) = w := by
      intro w; funext i; simp only [f]; split_ifs <;> simp
    have hnot_ne : ∀ (a b : Bool), ((!a) ≠ b) ↔ a = b := by decide
    have hdisj3 : ∀ w, sat A w = true → ¬ sat A (f w) = true := by
      intro w hw hfw
      have hs1 : w L1.1 ≠ L1.2 ∨ w L2.1 ≠ L2.2 := (sat_iff_nontaut A w).mp hw c1 hc1 hnt1
      have hs2 := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
      have hs3 := (sat_iff_nontaut A w).mp hw c3 hc3 hnt3
      have hf1 : f w L1.1 ≠ L1.2 ∨ f w L2.1 ≠ L2.2 := (sat_iff_nontaut A (f w)).mp hfw c1 hc1 hnt1
      have hf2 := (sat_iff_nontaut A (f w)).mp hfw c2 hc2 hnt2
      have hf3 := (sat_iff_nontaut A (f w)).mp hfw c3 hc3 hnt3
      have hfw1 : f w L1.1 = !(w L1.1) := by simp [f]
      have hfw2 : f w L2.1 = !(w L2.1) := by simp [f]
      have hfw3 : f w L3.1 = !(w L3.1) := by simp [f]
      have hs2' : w L2.1 ≠ L2.2 ∨ w L3.1 ≠ L3.2 := by
        rcases hc2_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rwa [e1, e2] at hs2
        · rw [e1, e2] at hs2; exact hs2.symm
      have hs3' : w L1.1 ≠ L1.2 ∨ w L3.1 ≠ L3.2 := by
        rcases hc3_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rwa [e1, e2] at hs3
        · rw [e1, e2] at hs3; exact hs3.symm
      have hf2' : f w L2.1 ≠ L2.2 ∨ f w L3.1 ≠ L3.2 := by
        rcases hc2_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rwa [e1, e2] at hf2
        · rw [e1, e2] at hf2; exact hf2.symm
      have hf3' : f w L1.1 ≠ L1.2 ∨ f w L3.1 ≠ L3.2 := by
        rcases hc3_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rwa [e1, e2] at hf3
        · rw [e1, e2] at hf3; exact hf3.symm
      rw [hfw1, hfw2, hnot_ne, hnot_ne] at hf1
      rw [hfw2, hfw3, hnot_ne, hnot_ne] at hf2'
      rw [hfw1, hfw3, hnot_ne, hnot_ne] at hf3'
      by_cases h1 : w L1.1 = L1.2
      · have h2 : w L2.1 ≠ L2.2 := hs1.resolve_left (not_not.mpr h1)
        have h3 : w L3.1 ≠ L3.2 := hs3'.resolve_left (not_not.mpr h1)
        exact hf2'.elim h2 h3
      · have h2 : w L2.1 = L2.2 := hf1.resolve_left h1
        have h3 : w L3.1 = L3.2 := hf3'.resolve_left h1
        exact hs2'.elim (fun hn => hn h2) (fun hn => hn h3)
    have hle := involution_two_mul_card_le (fun w => sat A w = true) f hinv hdisj3
    rw [card_word] at hle
    omega

private def finSuccEquiv {α : Type*} (k : ℕ) : (Fin (k + 1) → α) ≃ α × (Fin k → α) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j; rfl
  right_inv p := by
    cases p with
    | mk a g => exact Prod.ext rfl (funext fun _ => rfl)

private def voteStep {n : ℕ} (g : Word n → Bool) (z : Word n) (rest : Bool) : Bool :=
  let b := g z
  if b = g (negW z) then b else rest

private def voteK {n : ℕ} (g : Word n → Bool) (k : ℕ) (batch : Fin k → Word n) : Bool :=
  (List.ofFn batch).foldr (voteStep g) false

private lemma vote_count_ident {n : ℕ} (g : Word n → Bool) (k : ℕ) :
    let U := (Finset.univ.filter (fun w => g w = true ∧ g (negW w) = true)).card
    let V := (Finset.univ.filter (fun w => g w = false ∧ g (negW w) = false)).card
    let M := 2 ^ n - (U + V)
    let P := (Finset.univ.filter (fun batch : Fin k → Word n => voteK g k batch = true)).card
    (U + V) * P + U * M ^ k = U * (2 ^ n) ^ k ∧ (U = 0 → P = 0) := by
  intro U V M
  have hUV_le : U + V ≤ 2 ^ n := (count_pairs_ident g).2
  have hUVM : U + V + M = 2 ^ n := Nat.add_sub_cancel' hUV_le
  have hM_card : (Finset.univ.filter (fun w : Word n => g w ≠ g (negW w))).card = M := by
    have h1 := card_filter_add_not (Finset.univ : Finset (Word n)) (fun w => g w = g (negW w))
    rw [Finset.card_univ, card_word] at h1
    have hUV : (Finset.univ.filter (fun w : Word n => g w = g (negW w))).card = U + V := by
      have h2 := card_filter_add_not (Finset.univ.filter (fun w => g w = g (negW w)))
        (fun w => g w = true)
      have hU' : ((Finset.univ.filter (fun w => g w = g (negW w))).filter (fun w => g w = true)).card = U := by
        congr 1; ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        cases g w <;> cases g (negW w) <;> simp
      have hV' : ((Finset.univ.filter (fun w => g w = g (negW w))).filter (fun w => ¬ g w = true)).card = V := by
        congr 1; ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        cases g w <;> cases g (negW w) <;> simp
      omega
    have hM_eq : (Finset.univ.filter (fun w : Word n => ¬ g w = g (negW w))).card =
        (Finset.univ.filter (fun w : Word n => g w ≠ g (negW w))).card := rfl
    omega
  induction k with
  | zero =>
    have hP0 : (Finset.univ.filter (fun batch : Fin 0 → Word n => voteK g 0 batch = true)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro batch _
      simp [voteK]
    rw [hP0]
    exact ⟨by simp, fun _ => rfl⟩
  | succ k ih =>
    rcases ih with ⟨ih_eq, ih_zero⟩
    let Pk := (Finset.univ.filter (fun batch : Fin k → Word n => voteK g k batch = true)).card
    let Pk1 := (Finset.univ.filter (fun batch : Fin (k + 1) → Word n => voteK g (k + 1) batch = true)).card
    have hrec : Pk1 = U * (2 ^ n) ^ k + M * Pk := by
      have hstep : Pk1 = ∑ z : Word n,
          ∑ tail : Fin k → Word n, if voteStep g z (voteK g k tail) = true then (1 : ℕ) else 0 := by
        dsimp only [Pk1]
        rw [Finset.card_filter]
        rw [Fintype.sum_equiv (finSuccEquiv k) _
          (fun p => if voteStep g p.1 (voteK g k p.2) = true then (1 : ℕ) else 0)]
        · exact Fintype.sum_prod_type _
        · intro f
          have hof : voteK g (k + 1) f = voteStep g (f 0) (voteK g k (fun i => f i.succ)) := by
            simp only [voteK, List.ofFn_succ, List.foldr_cons]
          change (if voteK g (k + 1) f = true then (1 : ℕ) else 0) =
            if voteStep g (f 0) (voteK g k fun i => f i.succ) = true then (1 : ℕ) else 0
          rw [hof]
      rw [hstep]
      have hinner : ∀ z : Word n,
          (∑ tail : Fin k → Word n, if voteStep g z (voteK g k tail) = true then (1 : ℕ) else 0) =
          (if g z = true ∧ g (negW z) = true then (2 ^ n) ^ k else 0) +
          (if g z ≠ g (negW z) then Pk else 0) := by
        intro z
        cases hgz : g z <;> cases hgn : g (negW z)
        · simp [voteStep, hgz, hgn]
        · simp only [voteStep, hgz, hgn, Bool.false_eq_true, ↓reduceIte, ne_eq, not_false_eq_true,
            false_and, zero_add]
          exact (Finset.card_filter _ _).symm
        · simp only [voteStep, hgz, hgn, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte, ne_eq,
            not_false_eq_true, and_false, zero_add]
          exact (Finset.card_filter _ _).symm
        · simp only [voteStep, hgz, hgn, ↓reduceIte, and_self, ne_eq, not_true_eq_false, add_zero]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, card_word, Fintype.card_fin,
            smul_eq_mul, mul_one]
      calc
        ∑ z : Word n, ∑ tail : Fin k → Word n,
            (if voteStep g z (voteK g k tail) = true then (1 : ℕ) else 0)
          = ∑ z : Word n, ((if g z = true ∧ g (negW z) = true then (2 ^ n) ^ k else 0) +
              (if g z ≠ g (negW z) then Pk else 0)) :=
              Finset.sum_congr rfl (fun z _ => hinner z)
        _ = (∑ z : Word n, if g z = true ∧ g (negW z) = true then (2 ^ n) ^ k else 0) +
              (∑ z : Word n, if g z ≠ g (negW z) then Pk else 0) := Finset.sum_add_distrib
        _ = U * (2 ^ n) ^ k + M * Pk := by
              rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
                Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
                hM_card]
    constructor
    · calc
        (U + V) * Pk1 + U * M ^ (k + 1)
          = (U + V) * (U * (2 ^ n) ^ k + M * Pk) + U * (M * M ^ k) := by rw [hrec, pow_succ']
        _ = (U + V) * (U * (2 ^ n) ^ k) + M * ((U + V) * Pk + U * M ^ k) := by
              rw [mul_add, mul_left_comm (U + V) M Pk, ← mul_assoc U M (M ^ k),
                mul_comm U M, mul_assoc M U (M ^ k), add_assoc, ← mul_add]
        _ = (U + V) * (U * (2 ^ n) ^ k) + M * (U * (2 ^ n) ^ k) := by rw [ih_eq]
        _ = (U + V + M) * (U * (2 ^ n) ^ k) := (Nat.add_mul (U + V) M _).symm
        _ = 2 ^ n * (U * (2 ^ n) ^ k) := by rw [hUVM]
        _ = U * (2 ^ n) ^ (k + 1) := by rw [pow_succ', mul_left_comm]
    · intro hU0
      have hPk0 : Pk = 0 := ih_zero hU0
      change Pk1 = 0
      rw [hrec, hU0, hPk0]
      simp

private lemma pow_succ_bernoulli (m : ℕ) : ∀ k : ℕ, m ^ (k + 1) + (k + 1) * m ^ k ≤ (m + 1) ^ (k + 1)
  | 0 => by simp
  | k + 1 => by
    have ih := pow_succ_bernoulli m k
    have hmul : (m + 1) * (m ^ (k + 1) + (k + 1) * m ^ k) ≤ (m + 1) ^ (k + 1 + 1) := by
      rw [pow_succ' (m + 1) (k + 1)]
      exact Nat.mul_le_mul_left (m + 1) ih
    have hexp : (m + 1) * (m ^ (k + 1) + (k + 1) * m ^ k) =
        m ^ (k + 1 + 1) + (k + 1 + 1) * m ^ (k + 1) + (k + 1) * m ^ k := by
      have h1 : (m + 1) * (m ^ (k + 1) + (k + 1) * m ^ k) =
          m * m ^ (k + 1) + m * ((k + 1) * m ^ k) + m ^ (k + 1) + (k + 1) * m ^ k := by
        rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]
        omega
      have h2 : m * m ^ (k + 1) = m ^ (k + 1 + 1) := (pow_succ' m (k + 1)).symm
      have h3 : m * ((k + 1) * m ^ k) = (k + 1) * m ^ (k + 1) := by
        rw [mul_left_comm, ← pow_succ']
      have h4 : (k + 1) * m ^ (k + 1) + m ^ (k + 1) = (k + 1 + 1) * m ^ (k + 1) := by
        rw [Nat.add_mul (k + 1) 1 (m ^ (k + 1)), Nat.one_mul]
      omega
    omega

private lemma sixteen_mul_pow_le (t Q M : ℕ) (ht : 1 ≤ t) (hM : t * M ≤ (t - 1) * Q) :
    16 * M ^ (4 * t) ≤ Q ^ (4 * t) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' ht
  have hbern : 2 * m ^ (m + 1) ≤ (m + 1) ^ (m + 1) := by
    have h1 := pow_succ_bernoulli m m
    have h2 : (m + 1) * m ^ m = m ^ (m + 1) + m ^ m := by
      rw [Nat.add_mul, Nat.one_mul, ← pow_succ']
    omega
  have h4 : 16 * m ^ (4 * (m + 1)) ≤ (m + 1) ^ (4 * (m + 1)) := by
    have hpow := Nat.pow_le_pow_left hbern 4
    rw [mul_pow, ← pow_mul, ← pow_mul] at hpow
    have h24 : (2 : ℕ) ^ 4 = 16 := by decide
    rw [h24, mul_comm (m + 1) 4] at hpow
    exact hpow
  have hM' : (m + 1) * M ≤ m * Q := by simpa using hM
  have hpowM : ((m + 1) * M) ^ (4 * (m + 1)) ≤ (m * Q) ^ (4 * (m + 1)) :=
    Nat.pow_le_pow_left hM' (4 * (m + 1))
  rw [mul_pow, mul_pow] at hpowM
  have hcomb : (m + 1) ^ (4 * (m + 1)) * (16 * M ^ (4 * (m + 1))) ≤
      (m + 1) ^ (4 * (m + 1)) * Q ^ (4 * (m + 1)) :=
    calc
      (m + 1) ^ (4 * (m + 1)) * (16 * M ^ (4 * (m + 1)))
        = 16 * ((m + 1) ^ (4 * (m + 1)) * M ^ (4 * (m + 1))) := by ac_rfl
      _ ≤ 16 * (m ^ (4 * (m + 1)) * Q ^ (4 * (m + 1))) := Nat.mul_le_mul_left 16 hpowM
      _ = (16 * m ^ (4 * (m + 1))) * Q ^ (4 * (m + 1)) := by ac_rfl
      _ ≤ (m + 1) ^ (4 * (m + 1)) * Q ^ (4 * (m + 1)) := Nat.mul_le_mul_right _ h4
  exact Nat.le_of_mul_le_mul_left hcomb (Nat.pow_pos (Nat.succ_pos m))

private lemma variance_sum_ident {α : Type*} [Fintype α] (v : α → Bool) (m : ℕ) :
    let T : ℤ := Fintype.card α
    let P : ℤ := (Finset.univ.filter (fun a => v a = true)).card
    let X : α → ℤ := fun a => if v a = true then T - P else -P
    (∑ f : Fin m → α, ∑ i : Fin m, X (f i)) = 0 ∧
      (∑ f : Fin m → α, (∑ i : Fin m, X (f i)) ^ 2) =
        (m : ℤ) * P * (T - P) * T ^ m := by
  intro T P X
  have hXsum : ∑ a : α, X a = 0 := by
    have hsplit : ∑ a : α, X a =
        (∑ a : α, if v a = true then T else 0) - ∑ _a : α, P := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro a _
      dsimp only [X]
      split_ifs <;> omega
    rw [hsplit, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    dsimp only [T, P]
    rw [mul_comm]
    exact sub_self _
  have hXsq : ∑ a : α, (X a) ^ 2 = P * (T - P) * T := by
    have hsplit : ∑ a : α, (X a) ^ 2 =
        (∑ a : α, if v a = true then (T - P) ^ 2 else 0) +
        (∑ a : α, if v a = true then 0 else P ^ 2) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro a _
      dsimp only [X]
      split_ifs <;> simp [sq]
    rw [hsplit, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hcompl : ((Finset.univ.filter (fun a : α => ¬ v a = true)).card : ℤ) = T - P := by
      have h1 := card_filter_add_not (Finset.univ : Finset α) (fun a => v a = true)
      rw [Finset.card_univ] at h1
      dsimp only [T, P]
      omega
    rw [hcompl]
    dsimp only [P]
    have hstep1 : P * (T - P) ^ 2 + (T - P) * P ^ 2 = P * (T - P) * ((T - P) + P) := by
      rw [sq, sq, mul_add]
      congr 1
      · ac_rfl
      · ac_rfl
    rw [hstep1, sub_add_cancel]
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rcases ih with ⟨ih_sum, ih_sq⟩
    have hcard_m : ((Finset.univ : Finset (Fin m → α)).card : ℤ) = T ^ m := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
      simp [T]
    have hsum1 : (∑ f : Fin (m + 1) → α, ∑ i : Fin (m + 1), X (f i)) = 0 := by
      rw [Fintype.sum_equiv (finSuccEquiv m) _
        (fun p => X p.1 + ∑ i : Fin m, X (p.2 i))]
      · rw [Fintype.sum_prod_type]
        simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard_m, ih_sum,
          mul_zero, add_zero]
        rw [← Finset.mul_sum, hXsum, mul_zero]
      · intro f
        exact Fin.sum_univ_succ (fun i => X (f i))
    have hsq1 : (∑ f : Fin (m + 1) → α, (∑ i : Fin (m + 1), X (f i)) ^ 2) =
        ((m + 1 : ℕ) : ℤ) * P * (T - P) * T ^ (m + 1) := by
      rw [Fintype.sum_equiv (finSuccEquiv m) _
        (fun p => (X p.1 + ∑ i : Fin m, X (p.2 i)) ^ 2)]
      · rw [Fintype.sum_prod_type]
        have hexp : ∀ a : α, ∀ g : Fin m → α,
            (X a + ∑ i : Fin m, X (g i)) ^ 2 =
            (X a) ^ 2 + 2 * X a * (∑ i : Fin m, X (g i)) + (∑ i : Fin m, X (g i)) ^ 2 := by
          intro a g
          rw [sq, sq, sq, mul_add, add_mul, add_mul, mul_comm (∑ i : Fin m, X (g i)) (X a),
            two_mul, add_mul]
          omega
        simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, ih_sum, mul_zero,
          Finset.sum_const_zero, add_zero, ih_sq, Finset.sum_const, nsmul_eq_mul, hcard_m,
          Finset.card_univ]
        rw [← Finset.mul_sum, hXsq]
        have hT : (Fintype.card α : ℤ) = T := rfl
        rw [hT]
        have hcomb : T ^ m * (P * (T - P) * T) + T * ((m : ℤ) * P * (T - P) * T ^ m) =
            ((m + 1 : ℕ) : ℤ) * P * (T - P) * T ^ (m + 1) := by
          rw [pow_succ', Nat.cast_add, Nat.cast_one]
          have h1 : T ^ m * (P * (T - P) * T) = 1 * (P * (T - P) * (T * T ^ m)) := by
            rw [one_mul]; ac_rfl
          have h2 : T * ((m : ℤ) * P * (T - P) * T ^ m) = (m : ℤ) * (P * (T - P) * (T * T ^ m)) := by
            ac_rfl
          rw [h1, h2, ← add_mul, add_comm (1 : ℤ) (m : ℤ)]
          ac_rfl
        exact hcomb
      · intro f
        rw [Fin.sum_univ_succ (fun i => X (f i))]
        rfl
    exact ⟨hsum1, hsq1⟩

private lemma int_sq_nonneg (x : ℤ) : 0 ≤ x ^ 2 := by
  rw [sq]
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · have hneg : 0 ≤ -x := by omega
    have h := Int.mul_nonneg hneg hneg
    rwa [neg_mul_neg] at h

private lemma int_pow_nonneg {x : ℤ} (hx : 0 ≤ x) : ∀ k : ℕ, 0 ≤ x ^ k
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ']
    exact Int.mul_nonneg hx (int_pow_nonneg hx k)

private lemma int_sq_le_sq {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  rw [sq, sq]
  exact Int.le_trans (Int.mul_le_mul_of_nonneg_left hab ha)
    (Int.mul_le_mul_of_nonneg_right hab (Int.le_trans ha hab))

private lemma chebyshev_bounds {α : Type*} [Fintype α] (v : α → Bool)
    (hTpos : 0 < Fintype.card α) :
    let T := Fintype.card α
    let P := (Finset.univ.filter (fun a => v a = true)).card
    let hits := (Finset.univ.filter (fun f : Fin 256 → α =>
      144 ≤ (Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card)).card
    (2 * P ≤ T → 4 * hits ≤ T ^ 256) ∧
      (5 * T ≤ 8 * P → 3 * T ^ 256 ≤ 4 * hits) := by
  intro T P hits
  let Ti : ℤ := T
  let Pi : ℤ := P
  let X : α → ℤ := fun a => if v a = true then Ti - Pi else -Pi
  have hTi_pos : (0 : ℤ) < Ti := Int.natCast_pos.mpr hTpos
  have hTi_nonneg : (0 : ℤ) ≤ Ti := Int.le_of_lt hTi_pos
  have hD_eq : ∀ f : Fin 256 → α,
      (∑ i : Fin 256, X (f i)) =
        Ti * ((Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card : ℤ) - 256 * Pi := by
    intro f
    have hsplit : ∑ i : Fin 256, X (f i) =
        (∑ i : Fin 256, if v (f i) = true then Ti else 0) - ∑ _i : Fin 256, Pi := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      dsimp only [X]
      split_ifs <;> omega
    rw [hsplit, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, nsmul_eq_mul, mul_comm _ Ti]
    rfl
  have hvar : (∑ f : Fin 256 → α, (∑ i : Fin 256, X (f i)) ^ 2) ≤ 64 * Ti ^ 2 * Ti ^ 256 := by
    have hv := (variance_sum_ident v 256).2
    rw [hv]
    have h4 : 4 * Pi * (Ti - Pi) ≤ Ti ^ 2 := by
      have hsq : 0 ≤ (Ti - 2 * Pi) ^ 2 := int_sq_nonneg _
      have hexp : (Ti - 2 * Pi) ^ 2 = Ti ^ 2 - 4 * Pi * (Ti - Pi) := by
        rw [sq, sq, mul_sub, sub_mul, sub_mul, mul_sub]
        have h1 : Ti * (2 * Pi) = 2 * (Pi * Ti) := by ac_rfl
        have h2 : 2 * Pi * Ti = 2 * (Pi * Ti) := by ac_rfl
        have h3 : 2 * Pi * (2 * Pi) = 4 * (Pi * Pi) := by
          have h22 : (2 : ℤ) * 2 = 4 := by decide
          calc
            2 * Pi * (2 * Pi) = (2 * 2) * (Pi * Pi) := by ac_rfl
            _ = 4 * (Pi * Pi) := by rw [h22]
        have h4a : 4 * Pi * Ti = 4 * (Pi * Ti) := by ac_rfl
        have h5 : 4 * Pi * Pi = 4 * (Pi * Pi) := by ac_rfl
        omega
      omega
    have hTn : (0 : ℤ) ≤ Ti ^ 256 := int_pow_nonneg hTi_nonneg 256
    have hmul : 64 * (4 * Pi * (Ti - Pi)) * Ti ^ 256 ≤ 64 * Ti ^ 2 * Ti ^ 256 :=
      Int.mul_le_mul_of_nonneg_right (Int.mul_le_mul_of_nonneg_left h4 (by decide)) hTn
    have h256 : ((256 : ℕ) : ℤ) * Pi * (Ti - Pi) * Ti ^ 256 =
        64 * (4 * Pi * (Ti - Pi)) * Ti ^ 256 := by
      have : ((256 : ℕ) : ℤ) = 64 * 4 := by decide
      rw [this]
      ac_rfl
    rw [h256]
    exact hmul
  have h64_pos : (0 : ℤ) < 64 * Ti ^ 2 := by
    rw [sq]
    exact Int.mul_pos (by decide) (Int.mul_pos hTi_pos hTi_pos)
  constructor
  · intro hlow
    have hPi : 2 * Pi ≤ Ti := by dsimp only [Ti, Pi]; omega
    let H := Finset.univ.filter (fun f : Fin 256 → α =>
      144 ≤ (Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card)
    have hterm : ∀ f ∈ H, 256 * Ti ^ 2 ≤ (∑ i : Fin 256, X (f i)) ^ 2 := by
      intro f hf
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      rw [hD_eq f]
      have hS : (144 : ℤ) ≤ ((Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card : ℤ) := by
        omega
      have hdiff : 16 * Ti ≤
          Ti * ((Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card : ℤ) - 256 * Pi := by
        have h1 : 144 * Ti ≤ Ti * ((Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card : ℤ) := by
          rw [mul_comm Ti]
          exact Int.mul_le_mul_of_nonneg_right hS hTi_nonneg
        omega
      have hsq := int_sq_le_sq (Int.mul_nonneg (by decide) hTi_nonneg) hdiff
      have h16 : (16 * Ti) ^ 2 = 256 * Ti ^ 2 := by
        rw [sq, sq]
        have : (16 : ℤ) * 16 = 256 := by decide
        calc
          (16 * Ti) * (16 * Ti) = (16 * 16) * (Ti * Ti) := by ac_rfl
          _ = 256 * (Ti * Ti) := by rw [this]
      rwa [h16] at hsq
    have hsum_le : (hits : ℤ) * (256 * Ti ^ 2) ≤ 64 * Ti ^ 2 * Ti ^ 256 :=
      calc
        (hits : ℤ) * (256 * Ti ^ 2)
          = ∑ _f ∈ H, (256 * Ti ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ f ∈ H, (∑ i : Fin 256, X (f i)) ^ 2 := Finset.sum_le_sum hterm
        _ ≤ ∑ f : Fin 256 → α, (∑ i : Fin 256, X (f i)) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg (fun f => int_sq_nonneg _)
        _ ≤ 64 * Ti ^ 2 * Ti ^ 256 := hvar
    have hmul_le : (64 * Ti ^ 2) * (4 * (hits : ℤ)) ≤ (64 * Ti ^ 2) * Ti ^ 256 := by
      have hl : (hits : ℤ) * (256 * Ti ^ 2) = (64 * Ti ^ 2) * (4 * (hits : ℤ)) := by
        have : (256 : ℤ) = 64 * 4 := by decide
        rw [this]; ac_rfl
      rwa [← hl]
    have hfin : 4 * (hits : ℤ) ≤ Ti ^ 256 := (Int.mul_le_mul_left h64_pos).mp hmul_le
    have hfin' : ((4 * hits : ℕ) : ℤ) ≤ ((T ^ 256 : ℕ) : ℤ) := by
      simpa [Ti] using hfin
    exact Int.ofNat_le.mp hfin'
  · intro hhigh
    have hPi : 5 * Ti ≤ 8 * Pi := by dsimp only [Ti, Pi]; omega
    let H := Finset.univ.filter (fun f : Fin 256 → α =>
      ¬ 144 ≤ (Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card)
    have hterm : ∀ f ∈ H, 256 * Ti ^ 2 ≤ (∑ i : Fin 256, X (f i)) ^ 2 := by
      intro f hf
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hf
      rw [hD_eq f]
      have hS : ((Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card : ℤ) ≤ 144 := by
        omega
      have hdiff : 16 * Ti ≤
          -(Ti * ((Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card : ℤ) - 256 * Pi) := by
        have h1 : Ti * ((Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card : ℤ) ≤ 144 * Ti := by
          rw [mul_comm Ti]
          exact Int.mul_le_mul_of_nonneg_right hS hTi_nonneg
        omega
      have hsq := int_sq_le_sq (Int.mul_nonneg (by decide) hTi_nonneg) hdiff
      have h16 : (16 * Ti) ^ 2 = 256 * Ti ^ 2 := by
        rw [sq, sq]
        have : (16 : ℤ) * 16 = 256 := by decide
        calc
          (16 * Ti) * (16 * Ti) = (16 * 16) * (Ti * Ti) := by ac_rfl
          _ = 256 * (Ti * Ti) := by rw [this]
      rwa [h16, neg_sq] at hsq
    have hsum_le : (H.card : ℤ) * (256 * Ti ^ 2) ≤ 64 * Ti ^ 2 * Ti ^ 256 :=
      calc
        (H.card : ℤ) * (256 * Ti ^ 2)
          = ∑ _f ∈ H, (256 * Ti ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ f ∈ H, (∑ i : Fin 256, X (f i)) ^ 2 := Finset.sum_le_sum hterm
        _ ≤ ∑ f : Fin 256 → α, (∑ i : Fin 256, X (f i)) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg (fun f => int_sq_nonneg _)
        _ ≤ 64 * Ti ^ 2 * Ti ^ 256 := hvar
    have hmul_le : (64 * Ti ^ 2) * (4 * (H.card : ℤ)) ≤ (64 * Ti ^ 2) * Ti ^ 256 := by
      have hl : (H.card : ℤ) * (256 * Ti ^ 2) = (64 * Ti ^ 2) * (4 * (H.card : ℤ)) := by
        have : (256 : ℤ) = 64 * 4 := by decide
        rw [this]; ac_rfl
      rwa [← hl]
    have hH_le : 4 * H.card ≤ T ^ 256 := by
      have hfin : 4 * (H.card : ℤ) ≤ Ti ^ 256 := (Int.mul_le_mul_left h64_pos).mp hmul_le
      have hfin' : ((4 * H.card : ℕ) : ℤ) ≤ ((T ^ 256 : ℕ) : ℤ) := by
        simpa [Ti] using hfin
      exact Int.ofNat_le.mp hfin'
    have htot := card_filter_add_not (Finset.univ : Finset (Fin 256 → α))
      (fun f : Fin 256 → α => 144 ≤ (Finset.univ.filter (fun i : Fin 256 => v (f i) = true)).card)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at htot
    change hits + H.card = T ^ 256 at htot
    omega

end PEqualNP.Outside.L_lib_678

theorem PEqualNP.Outside.L_lib_678 : ∀ (n s : ℕ), 3 ≤ s → s ≤ n →
  let W := Fin n → Bool
  let Lit := Fin n × Bool
  let F := Finset (Lit × Lit)
  let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
    w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
  let Q := 2 ^ n
  let B := 4 * 2 ^ (s - 1)
  ∀ A : F,
    let N := (Finset.univ.filter (fun x => sat A x = true)).card
    let vote := fun (batch : Fin B → W) =>
      (List.ofFn batch).foldr (fun z rest =>
        let b := sat A z
        if b = sat A (fun i => !(z i)) then b else rest) false
    let hits := (Finset.univ.filter (fun tape : Fin 256 → Fin B → W =>
      144 ≤ (Finset.univ.filter (fun col : Fin 256 => vote (tape col) = true)).card)).card
    let total := Q ^ (256 * B)
    (2 * N ≤ Q → 4 * hits ≤ total) ∧
      (Q * (2 ^ (s - 1) + 1) ≤ 2 ^ s * N → 3 * total ≤ 4 * hits) := by
  intro n s hs hsn W Lit F sat_loc Q B A N vote hits total
  have hTcard : Fintype.card (Fin B → W) = Q ^ B := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact congrArg (· ^ B) (PEqualNP.Outside.L_lib_678.card_word n)
  have hTpos : 0 < Fintype.card (Fin B → W) := by
    rw [hTcard]
    exact Nat.pow_pos (Nat.pow_pos (by decide))
  have htot_eq : (Q ^ B) ^ 256 = total := by
    rw [← pow_mul, mul_comm B 256]
  have hcheb := PEqualNP.Outside.L_lib_678.chebyshev_bounds vote hTpos
  dsimp only at hcheb
  rw [hTcard, htot_eq] at hcheb
  let U := (Finset.univ.filter (fun w : W =>
    PEqualNP.Outside.L_lib_678.sat A w = true ∧
    PEqualNP.Outside.L_lib_678.sat A (PEqualNP.Outside.L_lib_678.negW w) = true)).card
  let V := (Finset.univ.filter (fun w : W =>
    PEqualNP.Outside.L_lib_678.sat A w = false ∧
    PEqualNP.Outside.L_lib_678.sat A (PEqualNP.Outside.L_lib_678.negW w) = false)).card
  let M := Q - (U + V)
  let P := (Finset.univ.filter (fun batch : Fin B → W => vote batch = true)).card
  have hpair := PEqualNP.Outside.L_lib_678.count_pairs_ident (PEqualNP.Outside.L_lib_678.sat A)
  have hvc := PEqualNP.Outside.L_lib_678.vote_count_ident (PEqualNP.Outside.L_lib_678.sat A) B
  change 2 * N + V = Q + U ∧ U + V ≤ Q at hpair
  change (U + V) * P + U * M ^ B = U * Q ^ B ∧ (U = 0 → P = 0) at hvc
  constructor
  · intro hlow
    apply hcheb.1
    by_cases hU0 : U = 0
    · change 2 * P ≤ Q ^ B
      rw [hvc.2 hU0]
      exact Nat.zero_le _
    · have hUV_pos : 0 < U + V := by omega
      have hUV_le : 2 * U ≤ U + V := by omega
      have h1 : (U + V) * (2 * P) ≤ (U + V) * Q ^ B :=
        calc
          (U + V) * (2 * P) = 2 * ((U + V) * P) := by ac_rfl
          _ ≤ 2 * (U * Q ^ B) := Nat.mul_le_mul_left 2 (by omega)
          _ = (2 * U) * Q ^ B := by ac_rfl
          _ ≤ (U + V) * Q ^ B := Nat.mul_le_mul_right _ hUV_le
      exact Nat.le_of_mul_le_mul_left h1 hUV_pos
  · intro hhigh
    apply hcheb.2
    let t := 2 ^ (s - 1)
    have ht_pos : 1 ≤ t := Nat.one_le_pow _ _ (by decide)
    have h2s : 2 ^ s = 2 * t := by
      have hs1 : s = (s - 1) + 1 := by omega
      conv_lhs => rw [hs1, pow_succ']
    have hQpos : 0 < Q := Nat.pow_pos (by decide)
    have hN_gt : Q < 2 * N := by
      have h1 : t * Q + Q ≤ t * (2 * N) := by
        have h2 : Q * (t + 1) ≤ (2 * t) * N := by rwa [h2s] at hhigh
        have hl : Q * (t + 1) = t * Q + Q := by rw [Nat.mul_add, Nat.mul_one, mul_comm]
        have hr : (2 * t) * N = t * (2 * N) := by ac_rfl
        omega
      have h2 : t * Q < t * (2 * N) := by omega
      exact Nat.lt_of_mul_lt_mul_left h2
    have h2VU : 2 * V ≤ U := PEqualNP.Outside.L_lib_678.two_mul_V_le_U A hN_gt
    have htU : Q + t * V ≤ t * U := by
      have h1 : t * Q + Q ≤ t * (2 * N) := by
        have h2 : Q * (t + 1) ≤ (2 * t) * N := by rwa [h2s] at hhigh
        have hl : Q * (t + 1) = t * Q + Q := by rw [Nat.mul_add, Nat.mul_one, mul_comm]
        have hr : (2 * t) * N = t * (2 * N) := by ac_rfl
        omega
      have h2 : t * (2 * N) + t * V = t * Q + t * U := by
        rw [← Nat.mul_add, hpair.1, Nat.mul_add]
      omega
    have htUV : Q ≤ t * (U + V) := by
      rw [Nat.mul_add]; omega
    have hUV_pos : 0 < U + V := by
      by_contra h0
      simp only [not_lt, Nat.le_zero] at h0
      rw [h0, mul_zero] at htUV
      omega
    have htM : t * M ≤ (t - 1) * Q := by
      have h1 : t * M + t * (U + V) = t * Q := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hpair.2]
      have h2 : (t - 1) * Q + Q = t * Q := by
        have : (t - 1) + 1 = t := by omega
        calc
          (t - 1) * Q + Q = (t - 1) * Q + 1 * Q := by rw [Nat.one_mul]
          _ = ((t - 1) + 1) * Q := (Nat.add_mul (t - 1) 1 Q).symm
          _ = t * Q := by rw [this]
      omega
    have h16M : 16 * M ^ B ≤ Q ^ B :=
      PEqualNP.Outside.L_lib_678.sixteen_mul_pow_le t Q M ht_pos htM
    have h15U : 15 * U * Q ^ B ≤ 16 * ((U + V) * P) := by
      have h1 : 16 * ((U + V) * P) + U * (16 * M ^ B) = 16 * (U * Q ^ B) := by
        have := congrArg (16 * ·) hvc.1
        rw [Nat.mul_add] at this
        have hswap : 16 * (U * M ^ B) = U * (16 * M ^ B) := by ac_rfl
        rwa [hswap] at this
      have h2 : U * (16 * M ^ B) ≤ U * Q ^ B := Nat.mul_le_mul_left U h16M
      have h3 : 16 * (U * Q ^ B) = 15 * U * Q ^ B + U * Q ^ B := by
        have : 16 * U = 15 * U + U := by omega
        calc
          16 * (U * Q ^ B) = (16 * U) * Q ^ B := by ac_rfl
          _ = (15 * U + U) * Q ^ B := by rw [this]
          _ = 15 * U * Q ^ B + U * Q ^ B := Nat.add_mul (15 * U) U (Q ^ B)
      omega
    have h10 : 10 * (U + V) ≤ 15 * U := by omega
    have hmul : (2 * (U + V)) * (5 * Q ^ B) ≤ (2 * (U + V)) * (8 * P) :=
      calc
        (2 * (U + V)) * (5 * Q ^ B) = (10 * (U + V)) * Q ^ B := by
          have h25 : 2 * 5 = 10 := rfl
          rw [← h25]; ac_rfl
        _ ≤ (15 * U) * Q ^ B := Nat.mul_le_mul_right _ h10
        _ ≤ 16 * ((U + V) * P) := h15U
        _ = (2 * (U + V)) * (8 * P) := by
          have h28 : 2 * 8 = 16 := rfl
          rw [← h28]; ac_rfl
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
