import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1138_aux

def litSat {n : ℕ} (d e h : Finset (Fin n)) (l : (Fin n × Bool) × Bool) : Bool :=
  (decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) == l.2

lemma litSat_eq_true_iff {n : ℕ} (d e h : Finset (Fin n)) (l : (Fin n × Bool) × Bool) :
    ((decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2) ↔
    decide (l.1.1 ∈ h) ≠ (decide (l.1.1 ∈ (if l.1.2 then e else d)) == l.2) := by
  cases decide (l.1.1 ∈ h) <;> cases decide (l.1.1 ∈ (if l.1.2 then e else d)) <;> cases l.2 <;> decide

lemma not_litSat_iff {n : ℕ} (d e h : Finset (Fin n)) (l : (Fin n × Bool) × Bool) :
    ¬ ((decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2) ↔
    decide (l.1.1 ∈ h) = (decide (l.1.1 ∈ (if l.1.2 then e else d)) == l.2) := by
  rw [litSat_eq_true_iff, not_not]

def okBits {n : ℕ} (d e : Finset (Fin n)) (C : Finset ((Fin n × Bool) × Bool)) (i : Fin n) :
    Finset Bool :=
  Finset.univ.filter (fun b =>
    ∀ side : Bool, ∀ p : Bool, ((i, side), p) ∈ C →
      b = (decide (i ∈ (if side then e else d)) == p))

lemma falsified_card_eq_prod {n : ℕ} (d e : Finset (Fin n)) (C : Finset ((Fin n × Bool) × Bool)) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun h =>
      ∀ l ∈ C, ¬ ((decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2))).card =
    ∏ i : Fin n, (okBits d e C i).card := by
  rw [← Fintype.card_piFinset]
  let S := (Finset.univ : Finset (Finset (Fin n))).filter (fun h =>
    ∀ l ∈ C, ¬ ((decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2))
  let T := Fintype.piFinset (fun i : Fin n => okBits d e C i)
  change S.card = T.card
  refine Finset.card_bij (fun h _ i => decide (i ∈ h)) ?_ ?_ ?_
  · intro h hh
    have hh' := (Finset.mem_filter.mp hh).2
    rw [Fintype.mem_piFinset]
    intro i
    simp only [okBits, Finset.mem_filter, Finset.mem_univ, true_and]
    intro side p hmem
    have hnot := hh' ((i, side), p) hmem
    exact (not_litSat_iff d e h ((i, side), p)).mp hnot
  · intro h₁ _ h₂ _ heq
    ext i
    have hi := congrFun heq i
    simpa [decide_eq_decide] using hi
  · intro f hf
    rw [Fintype.mem_piFinset] at hf
    refine ⟨Finset.univ.filter (fun i => f i = true), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l hl => ?_⟩
      rw [not_litSat_iff]
      have hfi := (Finset.mem_filter.mp (hf l.1.1)).2 l.1.2 l.2 hl
      have hdec : decide (l.1.1 ∈ Finset.univ.filter (fun i => f i = true)) = f l.1.1 := by
        cases hval : f l.1.1 <;> simp [hval]
      rw [hdec]
      exact hfi
    · funext i
      cases hval : f i <;> simp [hval]

lemma mass_add_falsified {n : ℕ} (d e : Finset (Fin n)) (C : Finset ((Fin n × Bool) × Bool)) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun h =>
      ∃ l ∈ C, (decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2)).card +
    ∏ i : Fin n, (okBits d e C i).card = 2 ^ n := by
  rw [← falsified_card_eq_prod d e C]
  have hdisj : Disjoint
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun h =>
        ∃ l ∈ C, (decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2))
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun h =>
        ∀ l ∈ C, ¬ ((decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2))) := by
    rw [Finset.disjoint_left]
    intro h h1 h2
    obtain ⟨l, hl, hsat⟩ := (Finset.mem_filter.mp h1).2
    exact (Finset.mem_filter.mp h2).2 l hl hsat
  rw [← Finset.card_union_of_disjoint hdisj]
  have hunion :
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun h =>
        ∃ l ∈ C, (decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2)) ∪
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun h =>
        ∀ l ∈ C, ¬ ((decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2))) =
      Finset.univ := by
    ext h
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases hex : ∃ l ∈ C, (decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2
    · exact Or.inl hex
    · push Not at hex; exact Or.inr hex
  rw [hunion, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

lemma prod_okBits_taut {n : ℕ} (d e : Finset (Fin n)) (C : Finset ((Fin n × Bool) × Bool))
    (htaut : ∃ wire, (wire, true) ∈ C ∧ (wire, false) ∈ C) :
    ∏ i : Fin n, (okBits d e C i).card = 0 := by
  rcases htaut with ⟨⟨i, side⟩, ht, hf⟩
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [Finset.card_eq_zero, okBits, Finset.filter_eq_empty_iff]
  intro b _ h
  have h1 := h side true ht
  have h2 := h side false hf
  rw [h1] at h2
  cases decide (i ∈ (if side then e else d)) <;> simp at h2

def shiftSet {n : ℕ} (C : Finset ((Fin n × Bool) × Bool)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    ((∃ p : Bool, ((i, false), p) ∈ C) ∧ (∃ q : Bool, ((i, true), q) ∈ C)) ∧
    (((i, false), true) ∈ C ↔ ((i, true), false) ∈ C))

def unoccSet {n : ℕ} (C : Finset ((Fin n × Bool) × Bool)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∀ side p, ((i, side), p) ∉ C)

lemma prod_okBits_not_taut {n : ℕ} (d e : Finset (Fin n)) (C : Finset ((Fin n × Bool) × Bool))
    (hnt : ¬ ∃ wire, (wire, true) ∈ C ∧ (wire, false) ∈ C) :
    let paired := (Finset.univ : Finset (Fin n)).filter (fun i =>
      (∃ p : Bool, ((i, false), p) ∈ C) ∧ (∃ q : Bool, ((i, true), q) ∈ C))
    ∏ i : Fin n, (okBits d e C i).card =
      if d ∩ paired = symmDiff (e ∩ paired) (shiftSet C) then 2 ^ (unoccSet C).card else 0 := by
  intro paired
  have huniq : ∀ (i : Fin n) (side p q : Bool),
      ((i, side), p) ∈ C → ((i, side), q) ∈ C → p = q := by
    intro i side p q hp hq
    cases p <;> cases q
    · rfl
    · exfalso; exact hnt ⟨(i, side), hq, hp⟩
    · exfalso; exact hnt ⟨(i, side), hp, hq⟩
    · rfl
  have hshift_sub : shiftSet C ⊆ paired := by
    intro i hi
    simp only [shiftSet, paired, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.1
  have hmatch_iff :
      (d ∩ paired = symmDiff (e ∩ paired) (shiftSet C)) ↔
      ∀ i ∈ paired, ∀ p q : Bool, ((i, false), p) ∈ C → ((i, true), q) ∈ C →
        (decide (i ∈ d) == p) = (decide (i ∈ e) == q) := by
    constructor
    · intro heq i hi p q hp hq
      have hmem : (i ∈ d ∩ paired) ↔ (i ∈ symmDiff (e ∩ paired) (shiftSet C)) := by rw [heq]
      simp only [Finset.mem_inter, hi, and_true, Finset.mem_symmDiff, shiftSet,
        Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hshift_iff : (((i, false), true) ∈ C ↔ ((i, true), false) ∈ C) ↔ (p != q) = true := by
        cases p <;> cases q
        · constructor
          · intro hiff; exfalso; exact hnt ⟨(i, false), hiff.mpr hq, hp⟩
          · intro h; simp at h
        · constructor
          · intro _; rfl
          · intro _; exact ⟨fun ht => absurd ⟨(i, false), ht, hp⟩ hnt, fun hf => absurd ⟨(i, true), hq, hf⟩ hnt⟩
        · constructor
          · intro _; rfl
          · intro _; exact ⟨fun _ => hq, fun _ => hp⟩
        · constructor
          · intro hiff; exfalso; exact hnt ⟨(i, true), hq, hiff.mp hp⟩
          · intro h; simp at h
      have hhip := (Finset.mem_filter.mp hi).2
      have hiff2 : (i ∈ d) ↔ ((i ∈ e ∧ ¬ (p != q) = true) ∨ ((p != q) = true ∧ i ∉ e)) := by
        rw [hmem]
        simp only [hhip, true_and, hshift_iff]
      by_cases hd : i ∈ d <;> by_cases he : i ∈ e <;> cases p <;> cases q <;>
        simp [hd, he] at hiff2 ⊢
    · intro hall
      ext i
      simp only [Finset.mem_inter, Finset.mem_symmDiff]
      by_cases hi : i ∈ paired
      · obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := (Finset.mem_filter.mp hi).2
        have hpeq := hall i hi p q hp hq
        have hsh : i ∈ shiftSet C ↔ (p != q) = true := by
          simp only [shiftSet, Finset.mem_filter, Finset.mem_univ, true_and,
            (Finset.mem_filter.mp hi).2, true_and]
          cases p <;> cases q
          · exact ⟨fun hiff => absurd ⟨(i, false), hiff.mpr hq, hp⟩ hnt, by simp⟩
          · exact ⟨fun _ => rfl, fun _ => ⟨fun ht => absurd ⟨(i, false), ht, hp⟩ hnt, fun hf => absurd ⟨(i, true), hq, hf⟩ hnt⟩⟩
          · exact ⟨fun _ => rfl, fun _ => ⟨fun _ => hq, fun _ => hp⟩⟩
          · exact ⟨fun hiff => absurd ⟨(i, true), hq, hiff.mp hp⟩ hnt, by simp⟩
        simp only [hi, and_true, hsh]
        by_cases hd : i ∈ d <;> by_cases he : i ∈ e <;> cases p <;> cases q <;>
          simp [hd, he] at hpeq ⊢
      · have hns : i ∉ shiftSet C := fun h => hi (hshift_sub h)
        simp [hi, hns]
  split_ifs with hmatch
  · have hall := hmatch_iff.mp hmatch
    have hcard_i : ∀ i : Fin n, (okBits d e C i).card = if i ∈ unoccSet C then 2 else 1 := by
      intro i
      split_ifs with hu
      · have hno := (Finset.mem_filter.mp hu).2
        have heq : okBits d e C i = Finset.univ := by
          ext b; simp only [okBits, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          intro side p hmem; exact absurd hmem (hno side p)
        rw [heq]; decide
      · simp only [unoccSet, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hu
        rcases hu with ⟨side₀, p₀, hmem₀⟩
        let b₀ : Bool := decide (i ∈ (if side₀ then e else d)) == p₀
        have heq : okBits d e C i = {b₀} := by
          ext b
          simp only [okBits, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro h; exact h side₀ p₀ hmem₀
          · rintro rfl side p hmem
            cases side₀ <;> cases side
            · dsimp only [b₀]; rw [huniq i false p₀ p hmem₀ hmem]
            · have hip : i ∈ paired := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p₀, hmem₀⟩, ⟨p, hmem⟩⟩
              exact hall i hip p₀ p hmem₀ hmem
            · have hip : i ∈ paired := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hmem⟩, ⟨p₀, hmem₀⟩⟩
              exact (hall i hip p p₀ hmem hmem₀).symm
            · dsimp only [b₀]; rw [huniq i true p₀ p hmem₀ hmem]
        rw [heq, Finset.card_singleton]
    simp_rw [hcard_i]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hfilt : (Finset.univ.filter (fun i : Fin n => i ∈ unoccSet C)) = unoccSet C := by
      ext i; simp
    rw [hfilt]
  · have hnot : ¬ ∀ i ∈ paired, ∀ p q : Bool, ((i, false), p) ∈ C → ((i, true), q) ∈ C →
        (decide (i ∈ d) == p) = (decide (i ∈ e) == q) := fun h => hmatch (hmatch_iff.mpr h)
    push Not at hnot
    rcases hnot with ⟨i, _, p, q, hp, hq, hne⟩
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [Finset.card_eq_zero, okBits, Finset.filter_eq_empty_iff]
    intro b _ h
    have h1 := h false p hp
    have h2 := h true q hq
    exact hne (h1.symm.trans h2)

lemma mass_not_taut {n : ℕ} (d e : Finset (Fin n)) (C : Finset ((Fin n × Bool) × Bool))
    (hnt : ¬ ∃ wire, (wire, true) ∈ C ∧ (wire, false) ∈ C) :
    let paired := (Finset.univ : Finset (Fin n)).filter (fun i =>
      (∃ p : Bool, ((i, false), p) ∈ C) ∧ (∃ q : Bool, ((i, true), q) ∈ C))
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun h =>
      ∃ l ∈ C, (decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2)).card =
      if d ∩ paired = symmDiff (e ∩ paired) (shiftSet C) then 2 ^ n - 2 ^ (unoccSet C).card else 2 ^ n := by
  intro paired
  have hsum := mass_add_falsified d e C
  have hprod := prod_okBits_not_taut d e C hnt
  dsimp only at hprod
  rw [hprod] at hsum
  split_ifs at hsum ⊢ <;> omega

lemma mass_taut {n : ℕ} (d e : Finset (Fin n)) (C : Finset ((Fin n × Bool) × Bool))
    (htaut : ∃ wire, (wire, true) ∈ C ∧ (wire, false) ∈ C) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun h =>
      ∃ l ∈ C, (decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2)).card = 2 ^ n := by
  have hsum := mass_add_falsified d e C
  rw [prod_okBits_taut d e C htaut, add_zero] at hsum
  exact hsum

lemma card_paired_mul_two_le {n : ℕ} (C : Finset ((Fin n × Bool) × Bool)) :
    let paired := (Finset.univ : Finset (Fin n)).filter (fun i =>
      (∃ p : Bool, ((i, false), p) ∈ C) ∧ (∃ q : Bool, ((i, true), q) ∈ C))
    2 * paired.card ≤ C.card := by
  intro paired
  let S := paired ×ˢ (Finset.univ : Finset Bool)
  have hScard : S.card = 2 * paired.card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]
  rw [← hScard]
  have hmap : ∀ x ∈ S, ∃ p : Bool, ((x.1, x.2), p) ∈ C := by
    intro ⟨i, side⟩ hx
    have hi := (Finset.mem_filter.mp (Finset.mem_product.mp hx).1).2
    cases side
    · exact hi.1
    · exact hi.2
  have hle : S.card ≤ (C.image (fun l => l.1)).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨p, hp⟩ := hmap x hx
    exact Finset.mem_image.mpr ⟨(x, p), hp, rfl⟩
  exact hle.trans Finset.card_image_le

lemma exists_subset_of_card {n k : ℕ} (hk : k ≤ n) :
    ∃ S : Finset (Fin n), S.card = k := by
  obtain ⟨S, _, hcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (by simpa using hk)
  exact ⟨S, hcard⟩

theorem main :
    ∀ (n w a b : Nat),
      let Bits := Finset (Fin n)
      let Clause := Finset ((Fin n × Bool) × Bool)
      let cube := (Finset.univ : Finset Bits)
      let mass := fun (d e : Bits) (C : Clause) =>
        (cube.filter (fun h => ∃ l ∈ C,
          (decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2)).card
      let fixed := fun (C : Clause) =>
        ∃ (L : Bits → Fin a) (R : Bits → Fin b) (decode : Fin a → Fin b → Nat),
          ∀ d e, decode (L d) (R e) = mass d e C
      let afterMessages :=
        ∃ (L : Bits → Fin a) (R : Bits → Fin b) (decode : Fin a → Fin b → Clause → Nat),
          ∀ d e C, C.card ≤ w → decode (L d) (R e) C = mass d e C
      let taut := fun (C : Clause) => ∃ wire, (wire, true) ∈ C ∧ (wire, false) ∈ C
      let paired := fun (C : Clause) =>
        (Finset.univ : Finset (Fin n)).filter (fun i =>
          (∃ p : Bool, ((i, false), p) ∈ C) ∧ (∃ q : Bool, ((i, true), q) ∈ C))
      (∀ C : Clause,
        let need := if taut C then 1 else 2 ^ (paired C).card
        fixed C ↔ need ≤ a ∧ need ≤ b) ∧
      ((∀ C : Clause, C.card ≤ w → fixed C) ↔
        2 ^ (min n (w / 2)) ≤ a ∧ 2 ^ (min n (w / 2)) ≤ b) ∧
      (afterMessages ↔
        (if 2 ≤ w then 2 ^ n else 1) ≤ a ∧ (if 2 ≤ w then 2 ^ n else 1) ≤ b) := by
  intro n w a b
  dsimp only
  let Bits := Finset (Fin n)
  let Clause := Finset ((Fin n × Bool) × Bool)
  let cube : Finset Bits := Finset.univ
  let mass := fun (d e : Bits) (C : Clause) =>
    (cube.filter (fun h => ∃ l ∈ C,
      (decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2)).card
  let fixed := fun (C : Clause) =>
    ∃ (L : Bits → Fin a) (R : Bits → Fin b) (decode : Fin a → Fin b → Nat),
      ∀ d e, decode (L d) (R e) = mass d e C
  let afterMessages :=
    ∃ (L : Bits → Fin a) (R : Bits → Fin b) (decode : Fin a → Fin b → Clause → Nat),
      ∀ d e C, C.card ≤ w → decode (L d) (R e) C = mass d e C
  let taut := fun (C : Clause) => ∃ wire, (wire, true) ∈ C ∧ (wire, false) ∈ C
  let paired := fun (C : Clause) =>
    (Finset.univ : Finset (Fin n)).filter (fun i =>
      (∃ p : Bool, ((i, false), p) ∈ C) ∧ (∃ q : Bool, ((i, true), q) ∈ C))
  have hpart1 : ∀ C : Clause,
      fixed C ↔ (if taut C then 1 else 2 ^ (paired C).card) ≤ a ∧
                (if taut C then 1 else 2 ^ (paired C).card) ≤ b := by
    intro C
    by_cases ht : taut C
    · rw [if_pos ht]
      constructor
      · rintro ⟨L, R, _, _⟩
        exact ⟨by have := (L ∅).isLt; omega, by have := (R ∅).isLt; omega⟩
      · rintro ⟨ha, hb⟩
        refine ⟨fun _ => ⟨0, by omega⟩, fun _ => ⟨0, by omega⟩, fun _ _ => 2 ^ n, fun d e => ?_⟩
        exact (mass_taut d e C ht).symm
    · rw [if_neg ht]
      have hshift_sub : shiftSet C ⊆ paired C := by
        intro i hi
        simp only [shiftSet, paired, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hi.1
      have hcard_pow : Fintype.card {S : Bits // S ⊆ paired C} = 2 ^ (paired C).card := by
        have heq : Fintype.card {S : Bits // S ⊆ paired C} = (paired C).powerset.card := by
          rw [Fintype.card_of_subtype (paired C).powerset (fun S => Finset.mem_powerset)]
        rw [heq, Finset.card_powerset]
      constructor
      · rintro ⟨L, R, decode, hdec⟩
        have hpos_unocc : 0 < 2 ^ (unoccSet C).card := Nat.pow_pos (by omega)
        have hle_unocc : 2 ^ (unoccSet C).card ≤ 2 ^ n :=
          Nat.pow_le_pow_right (by omega) (by simpa using Finset.card_le_univ (unoccSet C))
        have hne_val : 2 ^ n - 2 ^ (unoccSet C).card ≠ 2 ^ n := by omega
        have hL_inj : Function.Injective (fun x : {S : Bits // S ⊆ paired C} => L x.val) := by
          intro x y hxy
          by_contra hne
          have hne_val_xy : x.val ≠ y.val := fun h => hne (Subtype.ext h)
          let e0 : Bits := symmDiff x.val (shiftSet C)
          have he0_sub : e0 ⊆ paired C := by
            intro i hi
            rcases Finset.mem_symmDiff.mp hi with ⟨h1, _⟩ | ⟨h2, _⟩
            · exact x.property h1
            · exact hshift_sub h2
          have he0_inter : e0 ∩ paired C = e0 := Finset.inter_eq_left.mpr he0_sub
          have hx_inter : x.val ∩ paired C = x.val := Finset.inter_eq_left.mpr x.property
          have hy_inter : y.val ∩ paired C = y.val := Finset.inter_eq_left.mpr y.property
          have hm1 : mass x.val e0 C = 2 ^ n - 2 ^ (unoccSet C).card := by
            have h := mass_not_taut x.val e0 C ht
            dsimp only at h
            rw [hx_inter, he0_inter] at h
            have hsd : symmDiff e0 (shiftSet C) = x.val := by
              simp [e0, symmDiff_assoc, symmDiff_self]
            simpa [mass, cube, hsd] using h
          have hm2 : mass y.val e0 C = 2 ^ n := by
            have h := mass_not_taut y.val e0 C ht
            dsimp only at h
            rw [hy_inter, he0_inter] at h
            have hsd : symmDiff e0 (shiftSet C) = x.val := by
              simp [e0, symmDiff_assoc, symmDiff_self]
            rw [hsd, if_neg hne_val_xy.symm] at h
            exact h
          have heq_m : mass x.val e0 C = mass y.val e0 C := by
            have hxy' : L x.val = L y.val := hxy
            rw [← hdec x.val e0, ← hdec y.val e0, hxy']
          rw [hm1, hm2] at heq_m
          exact hne_val heq_m
        have hR_inj : Function.Injective (fun x : {S : Bits // S ⊆ paired C} => R x.val) := by
          intro x y hxy
          by_contra hne
          have hne_val_xy : x.val ≠ y.val := fun h => hne (Subtype.ext h)
          let d0 : Bits := symmDiff x.val (shiftSet C)
          have hd0_sub : d0 ⊆ paired C := by
            intro i hi
            rcases Finset.mem_symmDiff.mp hi with ⟨h1, _⟩ | ⟨h2, _⟩
            · exact x.property h1
            · exact hshift_sub h2
          have hd0_inter : d0 ∩ paired C = d0 := Finset.inter_eq_left.mpr hd0_sub
          have hx_inter : x.val ∩ paired C = x.val := Finset.inter_eq_left.mpr x.property
          have hy_inter : y.val ∩ paired C = y.val := Finset.inter_eq_left.mpr y.property
          have hm1 : mass d0 x.val C = 2 ^ n - 2 ^ (unoccSet C).card := by
            have h := mass_not_taut d0 x.val C ht
            dsimp only at h
            rw [hd0_inter, hx_inter, if_pos rfl] at h
            exact h
          have hm2 : mass d0 y.val C = 2 ^ n := by
            have h := mass_not_taut d0 y.val C ht
            dsimp only at h
            rw [hd0_inter, hy_inter] at h
            have hne_sd : d0 ≠ symmDiff y.val (shiftSet C) := by
              intro hsd
              have h1 := congrArg (fun u => symmDiff u (shiftSet C)) hsd
              simp only [d0, symmDiff_assoc, symmDiff_self, symmDiff_bot] at h1
              exact hne_val_xy h1
            rw [if_neg hne_sd] at h
            exact h
          have heq_m : mass d0 x.val C = mass d0 y.val C := by
            have hxy' : R x.val = R y.val := hxy
            rw [← hdec d0 x.val, ← hdec d0 y.val, hxy']
          rw [hm1, hm2] at heq_m
          exact hne_val heq_m
        have ha : 2 ^ (paired C).card ≤ a := by
          have := Fintype.card_le_of_injective _ hL_inj
          simpa [hcard_pow] using this
        have hb : 2 ^ (paired C).card ≤ b := by
          have := Fintype.card_le_of_injective _ hR_inj
          simpa [hcard_pow] using this
        exact ⟨ha, hb⟩
      · rintro ⟨ha, hb⟩
        let eqv : {S : Bits // S ⊆ paired C} ≃ Fin (2 ^ (paired C).card) :=
          Fintype.equivFinOfCardEq hcard_pow
        let L : Bits → Fin a := fun d =>
          ⟨(eqv ⟨d ∩ paired C, Finset.inter_subset_right⟩).val,
            lt_of_lt_of_le (eqv _).isLt ha⟩
        let R : Bits → Fin b := fun e =>
          ⟨(eqv ⟨symmDiff (e ∩ paired C) (shiftSet C), by
              intro i hi
              rcases Finset.mem_symmDiff.mp hi with ⟨h1, _⟩ | ⟨h2, _⟩
              · exact (Finset.mem_inter.mp h1).2
              · exact hshift_sub h2⟩).val,
            lt_of_lt_of_le (eqv _).isLt hb⟩
        let decode : Fin a → Fin b → ℕ := fun u v =>
          if u.val = v.val then 2 ^ n - 2 ^ (unoccSet C).card else 2 ^ n
        refine ⟨L, R, decode, fun d e => ?_⟩
        have h : mass d e C = if d ∩ paired C = symmDiff (e ∩ paired C) (shiftSet C) then
            2 ^ n - 2 ^ (unoccSet C).card else 2 ^ n := mass_not_taut d e C ht
        change decode (L d) (R e) = mass d e C
        rw [h]
        dsimp only [decode, L, R]
        have hesub : symmDiff (e ∩ paired C) (shiftSet C) ⊆ paired C := by
          intro i hi
          rcases Finset.mem_symmDiff.mp hi with ⟨h1, _⟩ | ⟨h2, _⟩
          · exact (Finset.mem_inter.mp h1).2
          · exact hshift_sub h2
        have hiff : ((eqv ⟨d ∩ paired C, Finset.inter_subset_right⟩).val =
            (eqv ⟨symmDiff (e ∩ paired C) (shiftSet C), hesub⟩).val) ↔
            d ∩ paired C = symmDiff (e ∩ paired C) (shiftSet C) := by
          constructor
          · intro hval
            have hinj := eqv.injective (Fin.ext hval)
            exact congrArg Subtype.val hinj
          · intro heq
            exact congrArg Fin.val (congrArg eqv (Subtype.ext heq))
        by_cases hm : d ∩ paired C = symmDiff (e ∩ paired C) (shiftSet C)
        · rw [if_pos (hiff.mpr hm), if_pos hm]
        · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]
  refine ⟨hpart1, ?_, ?_⟩
  · -- Part 2
    constructor
    · intro hall
      obtain ⟨S, hScard⟩ := exists_subset_of_card (n := n) (k := min n (w / 2)) (min_le_left _ _)
      let C : Finset ((Fin n × Bool) × Bool) :=
        S.image (fun i => ((i, false), false)) ∪ S.image (fun i => ((i, true), false))
      have hCcard : C.card ≤ w := by
        calc C.card ≤ (S.image (fun i => ((i, false), false))).card +
              (S.image (fun i => ((i, true), false))).card := Finset.card_union_le _ _
          _ ≤ S.card + S.card := add_le_add Finset.card_image_le Finset.card_image_le
          _ = 2 * min n (w / 2) := by omega
          _ ≤ w := by have := min_le_right n (w / 2); omega
      have hnt : ¬ taut C := by
        rintro ⟨wire, ht, _⟩
        change (wire, true) ∈ S.image (fun i => ((i, false), false)) ∪ S.image (fun i => ((i, true), false)) at ht
        simp only [Finset.mem_union, Finset.mem_image] at ht
        rcases ht with ⟨i, _, hi⟩ | ⟨i, _, hi⟩ <;> simp at hi
      have hpaired : paired C = S := by
        ext i
        simp only [paired, Finset.mem_filter, Finset.mem_univ, true_and]
        change ((∃ p : Bool, ((i, false), p) ∈ S.image (fun i => ((i, false), false)) ∪ S.image (fun i => ((i, true), false))) ∧
          (∃ q : Bool, ((i, true), q) ∈ S.image (fun i => ((i, false), false)) ∪ S.image (fun i => ((i, true), false)))) ↔ i ∈ S
        simp only [Finset.mem_union, Finset.mem_image]
        constructor
        · rintro ⟨⟨p, ⟨j, hj, hjeq⟩ | ⟨j, _, hjeq⟩⟩, _⟩
          · have : j = i := by
              have h1 := congrArg (fun x : (Fin n × Bool) × Bool => x.1.1) hjeq
              exact h1
            subst this; exact hj
          · exfalso
            have h1 := congrArg (fun x : (Fin n × Bool) × Bool => x.1.2) hjeq
            simp at h1
        · intro hi
          exact ⟨⟨false, Or.inl ⟨i, hi, rfl⟩⟩, ⟨false, Or.inr ⟨i, hi, rfl⟩⟩⟩
      have hfix := (hpart1 C).mp (hall C hCcard)
      rw [if_neg hnt, hpaired, hScard] at hfix
      exact hfix
    · rintro ⟨ha, hb⟩ C hCw
      change fixed C
      rw [hpart1 C]
      split_ifs with ht
      · have h1 : 1 ≤ 2 ^ min n (w / 2) := Nat.one_le_two_pow
        exact ⟨le_trans h1 ha, le_trans h1 hb⟩
      · have hle_n : (paired C).card ≤ n := by simpa using Finset.card_le_univ (paired C)
        have hle_w : (paired C).card ≤ w / 2 := by
          have h2 : 2 * (paired C).card ≤ C.card := card_paired_mul_two_le C
          omega
        have hle : 2 ^ (paired C).card ≤ 2 ^ min n (w / 2) :=
          Nat.pow_le_pow_right (by omega) (le_min hle_n hle_w)
        exact ⟨le_trans hle ha, le_trans hle hb⟩
  · -- Part 3
    by_cases hw : 2 ≤ w
    · rw [if_pos hw]
      constructor
      · rintro ⟨L, R, decode, hdec⟩
        have hsep_pair : ∀ (i : Fin n) (d e : Finset (Fin n)),
            let C : Finset ((Fin n × Bool) × Bool) := {((i, false), false), ((i, true), false)}
            C.card ≤ w ∧
            (mass d e C = if (i ∈ d ↔ i ∈ e) then 2 ^ n - 2 ^ (unoccSet C).card else 2 ^ n) ∧
            2 ^ n - 2 ^ (unoccSet C).card ≠ 2 ^ n := by
          intro i d e C
          have hCw : C.card ≤ w := (Finset.card_le_two).trans hw
          have hnt : ¬ taut C := by
            rintro ⟨wire, ht, _⟩
            change (wire, true) ∈ ({((i, false), false), ((i, true), false)} : Finset ((Fin n × Bool) × Bool)) at ht
            simp only [Finset.mem_insert, Finset.mem_singleton] at ht
            rcases ht with h | h <;> simp at h
          have hpaired : paired C = {i} := by
            ext j
            simp only [paired, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            change ((∃ p : Bool, ((j, false), p) ∈ ({((i, false), false), ((i, true), false)} : Finset ((Fin n × Bool) × Bool))) ∧
              (∃ q : Bool, ((j, true), q) ∈ ({((i, false), false), ((i, true), false)} : Finset ((Fin n × Bool) × Bool)))) ↔ j = i
            simp only [Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨⟨p, h1 | h2⟩, _⟩
              · exact congrArg (fun x : (Fin n × Bool) × Bool => x.1.1) h1
              · have := congrArg (fun x : (Fin n × Bool) × Bool => x.1.2) h2
                simp at this
            · rintro rfl
              exact ⟨⟨false, Or.inl rfl⟩, ⟨false, Or.inr rfl⟩⟩
          have hsh : shiftSet C = ∅ := by
            ext j
            simp only [shiftSet, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.notMem_empty, iff_false]
            rintro ⟨⟨_, ⟨q, hq⟩⟩, hiff⟩
            have hji : j = i := by
              simp only [C, Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with h1 | h2
              · have := congrArg (fun x : (Fin n × Bool) × Bool => x.1.2) h1; simp at this
              · exact congrArg (fun x : (Fin n × Bool) × Bool => x.1.1) h2
            subst hji
            have htf : ((j, false), true) ∈ C := hiff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            simp only [C, Finset.mem_insert, Finset.mem_singleton] at htf
            rcases htf with h1 | h1 <;> simp at h1
          have hm : mass d e C = if d ∩ paired C = symmDiff (e ∩ paired C) (shiftSet C) then
              2 ^ n - 2 ^ (unoccSet C).card else 2 ^ n := mass_not_taut d e C hnt
          have hsd_emp : symmDiff (e ∩ {i}) ∅ = e ∩ {i} := by ext x; simp [Finset.mem_symmDiff]
          rw [hpaired, hsh, hsd_emp] at hm
          have heq_iff : (d ∩ {i} = e ∩ {i}) ↔ (i ∈ d ↔ i ∈ e) := by
            constructor
            · intro h
              have := congrArg (fun s : Finset (Fin n) => i ∈ s) h
              simpa [Finset.mem_inter] using this
            · intro h
              ext j
              simp only [Finset.mem_inter, Finset.mem_singleton]
              constructor
              · rintro ⟨hd, rfl⟩; exact ⟨h.mp hd, rfl⟩
              · rintro ⟨he, rfl⟩; exact ⟨h.mpr he, rfl⟩
          have hpos_u : 0 < 2 ^ (unoccSet C).card := Nat.pow_pos (by omega)
          have hle_u : 2 ^ (unoccSet C).card ≤ 2 ^ n :=
            Nat.pow_le_pow_right (by omega) (by simpa using Finset.card_le_univ (unoccSet C))
          refine ⟨hCw, ?_, by omega⟩
          rw [hm]
          by_cases hde : i ∈ d ↔ i ∈ e
          · rw [if_pos (heq_iff.mpr hde), if_pos hde]
          · rw [if_neg (fun h => hde (heq_iff.mp h)), if_neg hde]
        have hL_inj : Function.Injective L := by
          intro d₁ d₂ hL
          by_contra hne
          have hex : ∃ i : Fin n, ¬ (i ∈ d₁ ↔ i ∈ d₂) := by
            by_contra hall; push Not at hall
            apply hne; ext i; exact hall i
          rcases hex with ⟨i, hi⟩
          let C : Finset ((Fin n × Bool) × Bool) := {((i, false), false), ((i, true), false)}
          have h1 := hsep_pair i d₁ d₁
          have h2 := hsep_pair i d₂ d₁
          dsimp only at h1 h2
          have hm1 : mass d₁ d₁ C = 2 ^ n - 2 ^ (unoccSet C).card := by
            rw [h1.2.1, if_pos Iff.rfl]
          have hm2 : mass d₂ d₁ C = 2 ^ n := by
            rw [h2.2.1, if_neg (fun h => hi h.symm)]
          have heq_m : mass d₁ d₁ C = mass d₂ d₁ C := by
            dsimp only [mass, cube]
            rw [← hdec d₁ d₁ C h1.1, ← hdec d₂ d₁ C h1.1, hL]
          rw [hm1, hm2] at heq_m
          exact h1.2.2 heq_m
        have hR_inj : Function.Injective R := by
          intro e₁ e₂ hR
          by_contra hne
          have hex : ∃ i : Fin n, ¬ (i ∈ e₁ ↔ i ∈ e₂) := by
            by_contra hall; push Not at hall
            apply hne; ext i; exact hall i
          rcases hex with ⟨i, hi⟩
          let C : Finset ((Fin n × Bool) × Bool) := {((i, false), false), ((i, true), false)}
          have h1 := hsep_pair i e₁ e₁
          have h2 := hsep_pair i e₁ e₂
          dsimp only at h1 h2
          have hm1 : mass e₁ e₁ C = 2 ^ n - 2 ^ (unoccSet C).card := by
            rw [h1.2.1, if_pos Iff.rfl]
          have hm2 : mass e₁ e₂ C = 2 ^ n := by
            rw [h2.2.1, if_neg hi]
          have heq_m : mass e₁ e₁ C = mass e₁ e₂ C := by
            dsimp only [mass, cube]
            rw [← hdec e₁ e₁ C h1.1, ← hdec e₁ e₂ C h1.1, hR]
          rw [hm1, hm2] at heq_m
          exact h1.2.2 heq_m
        have hcard_bits : Fintype.card Bits = 2 ^ n := by
          rw [Fintype.card_finset, Fintype.card_fin]
        have ha : 2 ^ n ≤ a := by
          have := Fintype.card_le_of_injective L hL_inj
          simpa [hcard_bits] using this
        have hb : 2 ^ n ≤ b := by
          have := Fintype.card_le_of_injective R hR_inj
          simpa [hcard_bits] using this
        exact ⟨ha, hb⟩
      · rintro ⟨ha, hb⟩
        have hcard_bits : Fintype.card Bits = 2 ^ n := by
          rw [Fintype.card_finset, Fintype.card_fin]
        let eqv : Bits ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq hcard_bits
        let L : Bits → Fin a := fun d => ⟨(eqv d).val, lt_of_lt_of_le (eqv d).isLt ha⟩
        let R : Bits → Fin b := fun e => ⟨(eqv e).val, lt_of_lt_of_le (eqv e).isLt hb⟩
        let decode : Fin a → Fin b → Clause → ℕ := fun u v C =>
          if hu : u.val < 2 ^ n then
            if hv : v.val < 2 ^ n then mass (eqv.symm ⟨u.val, hu⟩) (eqv.symm ⟨v.val, hv⟩) C
            else 0
          else 0
        refine ⟨L, R, decode, fun d e C _ => ?_⟩
        dsimp only [decode, L, R]
        rw [dif_pos (eqv d).isLt, dif_pos (eqv e).isLt]
        simp
        rfl
    · rw [if_neg hw]
      constructor
      · rintro ⟨L, R, _, _⟩
        exact ⟨by have := (L ∅).isLt; omega, by have := (R ∅).isLt; omega⟩
      · rintro ⟨ha, hb⟩
        refine ⟨fun _ => ⟨0, by omega⟩, fun _ => ⟨0, by omega⟩, fun _ _ C => mass ∅ ∅ C, fun d e C hCw => ?_⟩
        have hnt : ¬ taut C := by
          rintro ⟨wire, ht, hf⟩
          have h2 : ({(wire, true), (wire, false)} : Finset ((Fin n × Bool) × Bool)) ⊆ C := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption
          have hcard2 : ({(wire, true), (wire, false)} : Finset ((Fin n × Bool) × Bool)).card = 2 :=
            Finset.card_pair (by simp)
          have hle := Finset.card_le_card h2
          omega
        have hp_empty : paired C = ∅ := by
          have h2 : 2 * (paired C).card ≤ C.card := card_paired_mul_two_le C
          exact Finset.card_eq_zero.mp (by omega)
        have hsh_empty : shiftSet C = ∅ := by
          apply Finset.subset_empty.mp
          intro i hi
          have : i ∈ paired C := by
            simp only [shiftSet, paired, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact hi.1
          rwa [hp_empty] at this
        have h1 : mass ∅ ∅ C = if ∅ ∩ paired C = symmDiff (∅ ∩ paired C) (shiftSet C) then
            2 ^ n - 2 ^ (unoccSet C).card else 2 ^ n := mass_not_taut ∅ ∅ C hnt
        have h2 : mass d e C = if d ∩ paired C = symmDiff (e ∩ paired C) (shiftSet C) then
            2 ^ n - 2 ^ (unoccSet C).card else 2 ^ n := mass_not_taut d e C hnt
        change mass ∅ ∅ C = mass d e C
        rw [h1, h2, hp_empty, hsh_empty]
        simp

end PEqualNP.Outside.L_lib_1138_aux

theorem PEqualNP.Outside.L_lib_1138 :
∀ (n w a b : Nat),
  let Bits := Finset (Fin n)
  let Clause := Finset ((Fin n × Bool) × Bool)
  let cube := (Finset.univ : Finset Bits)
  let mass := fun (d e : Bits) (C : Clause) =>
    (cube.filter (fun h => ∃ l ∈ C,
      (decide (l.1.1 ∈ h) != decide (l.1.1 ∈ (if l.1.2 then e else d))) = l.2)).card
  let fixed := fun (C : Clause) =>
    ∃ (L : Bits → Fin a) (R : Bits → Fin b) (decode : Fin a → Fin b → Nat),
      ∀ d e, decode (L d) (R e) = mass d e C
  let afterMessages :=
    ∃ (L : Bits → Fin a) (R : Bits → Fin b) (decode : Fin a → Fin b → Clause → Nat),
      ∀ d e C, C.card ≤ w → decode (L d) (R e) C = mass d e C
  let taut := fun (C : Clause) => ∃ wire, (wire, true) ∈ C ∧ (wire, false) ∈ C
  let paired := fun (C : Clause) =>
    (Finset.univ : Finset (Fin n)).filter (fun i =>
      (∃ p : Bool, ((i, false), p) ∈ C) ∧ (∃ q : Bool, ((i, true), q) ∈ C))
  (∀ C : Clause,
    let need := if taut C then 1 else 2 ^ (paired C).card
    fixed C ↔ need ≤ a ∧ need ≤ b) ∧
  ((∀ C : Clause, C.card ≤ w → fixed C) ↔
    2 ^ (min n (w / 2)) ≤ a ∧ 2 ^ (min n (w / 2)) ≤ b) ∧
  (afterMessages ↔
    (if 2 ≤ w then 2 ^ n else 1) ≤ a ∧ (if 2 ≤ w then 2 ^ n else 1) ≤ b) :=
  PEqualNP.Outside.L_lib_1138_aux.main
