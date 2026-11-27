import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_699_aux

def unitV {n : Nat} (i : Fin n) : Fin n → ZMod 2 :=
  fun j => if j = i then (1 : ZMod 2) else 0

theorem unitV_self {n : Nat} (i : Fin n) : unitV i i = 1 := by
  simp [unitV]

theorem unitV_ne {n : Nat} {i j : Fin n} (h : i ≠ j) : unitV i ≠ unitV j := by
  intro heq
  have h1 := congrFun heq i
  simp [unitV, h] at h1

theorem zmod2_add_self {n : Nat} (v : Fin n → ZMod 2) : v + v = 0 := by
  ext j
  change v j + v j = 0
  generalize v j = x
  fin_cases x <;> decide

def wordA {k : Nat} (S : Finset (Fin k)) : Fin k → Nat :=
  fun a => if a ∈ S then 2 else 0

def wordB {k : Nat} (d : Nat) (t : Fin d) : Fin k → Nat :=
  fun a =>
    if a.val = 2 * t.val ∨ a.val = 2 * t.val + 1 then 1
    else if a.val < 2 * d ∧ a.val % 2 = 0 then 2
    else 0

theorem wordA_inj {k : Nat} : Function.Injective (@wordA k) := by
  intro S1 S2 h
  ext a
  have ha := congrFun h a
  unfold wordA at ha
  by_cases h1 : a ∈ S1 <;> by_cases h2 : a ∈ S2 <;> simp [h1, h2] at ha ⊢

theorem wordB_inj {k d : Nat} (hd : 2 * d ≤ k) : Function.Injective (@wordB k d) := by
  intro t1 t2 h
  let a0 : Fin k := ⟨2 * t1.val, by omega⟩
  have ha := congrFun h a0
  unfold wordB at ha
  simp only [a0, true_or, ↓reduceIte] at ha
  split_ifs at ha with h1
  · ext; omega
  · omega

theorem wordA_ne_wordB {k d : Nat} (hd : 2 * d ≤ k) (S : Finset (Fin k)) (t : Fin d) :
    wordA S ≠ wordB d t := by
  intro h
  let a0 : Fin k := ⟨2 * t.val, by omega⟩
  have ha := congrFun h a0
  unfold wordA wordB at ha
  simp only [a0, true_or, ↓reduceIte] at ha
  split_ifs at ha <;> omega

theorem wordA_sum {k d : Nat} {S : Finset (Fin k)} (hS : S.card = d) :
    ∑ a : Fin k, wordA S a = 2 * d := by
  unfold wordA
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have hflt : (Finset.univ.filter (fun a : Fin k => a ∈ S)) = S := by
    ext a; simp
  rw [hflt, hS, mul_comm]

theorem wordB_sum {k d : Nat} (hd : 2 * d ≤ k) (t : Fin d) :
    ∑ a : Fin k, wordB d t a = 2 * d := by
  have hsplit : ∑ a : Fin k, wordB d t a =
      ∑ a ∈ Finset.univ.filter (fun a : Fin k => a.val < 2 * d), wordB d t a := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha
    unfold wordB
    have h1 : ¬ (a.val = 2 * t.val ∨ a.val = 2 * t.val + 1) := by omega
    have h2 : ¬ (a.val < 2 * d ∧ a.val % 2 = 0) := by omega
    simp [h1, h2]
  rw [hsplit]
  let evens : Finset (Fin k) := (Finset.univ : Finset (Fin d)).image (fun s => ⟨2 * s.val, by omega⟩)
  let odds : Finset (Fin k) := (Finset.univ : Finset (Fin d)).image (fun s => ⟨2 * s.val + 1, by omega⟩)
  have hdisj : Disjoint evens odds := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [evens, odds, Finset.mem_image, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨s1, rfl⟩
    rcases hb with ⟨s2, h2⟩
    have := congrArg Fin.val h2
    dsimp only at this
    omega
  have hunion : Finset.univ.filter (fun a : Fin k => a.val < 2 * d) = evens ∪ odds := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      evens, odds, Finset.mem_image]
    constructor
    · intro ha
      by_cases hp : a.val % 2 = 0
      · left; exact ⟨⟨a.val / 2, by omega⟩, Fin.ext (by dsimp; omega)⟩
      · right; exact ⟨⟨a.val / 2, by omega⟩, Fin.ext (by dsimp; omega)⟩
    · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩) <;> dsimp <;> omega
  rw [hunion, Finset.sum_union hdisj]
  have heven_inj : Function.Injective (fun s : Fin d => (⟨2 * s.val, by omega⟩ : Fin k)) := by
    intro s1 s2 h; have := congrArg Fin.val h; dsimp at this; exact Fin.ext (by omega)
  have hodd_inj : Function.Injective (fun s : Fin d => (⟨2 * s.val + 1, by omega⟩ : Fin k)) := by
    intro s1 s2 h; have := congrArg Fin.val h; dsimp at this; exact Fin.ext (by omega)
  have hsum_even : ∑ a ∈ evens, wordB d t a = 2 * d - 1 := by
    rw [Finset.sum_image (fun s1 _ s2 _ h => heven_inj h)]
    have hval : ∀ s : Fin d, wordB d t (⟨2 * s.val, by have := s.isLt; omega⟩ : Fin k) = if s = t then 1 else 2 := by
      intro s
      have hs := s.isLt
      unfold wordB
      by_cases hst : s = t
      · subst hst; simp
      · have h1 : ¬ (2 * s.val = 2 * t.val ∨ 2 * s.val = 2 * t.val + 1) := by
          have : s.val ≠ t.val := fun hc => hst (Fin.ext hc)
          omega
        have h2 : 2 * s.val < 2 * d ∧ (2 * s.val) % 2 = 0 := by omega
        dsimp only
        rw [if_neg h1, if_pos h2, if_neg hst]
    have hrew : ∑ s : Fin d, wordB d t (⟨2 * s.val, by have := s.isLt; omega⟩ : Fin k) =
        ∑ s : Fin d, (if s = t then 1 else 2) :=
      Finset.sum_congr rfl (fun s _ => hval s)
    rw [hrew]
    have hsum1 : ∑ s : Fin d, (if s = t then (1 : Nat) else 2) + 1 = ∑ _s : Fin d, (2 : Nat) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
      simp only [↓reduceIte]
      have hrest : ∑ s ∈ Finset.univ.erase t, (if s = t then (1 : Nat) else 2) =
          ∑ _s ∈ Finset.univ.erase t, (2 : Nat) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [if_neg (Finset.ne_of_mem_erase hs)]
      rw [hrest]; omega
    have hsum2 : ∑ _s : Fin d, (2 : Nat) = 2 * d := by
      simp [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  have hsum_odd : ∑ a ∈ odds, wordB d t a = 1 := by
    rw [Finset.sum_image (fun s1 _ s2 _ h => hodd_inj h)]
    have hval : ∀ s : Fin d, wordB d t (⟨2 * s.val + 1, by have := s.isLt; omega⟩ : Fin k) = if s = t then 1 else 0 := by
      intro s
      have hs := s.isLt
      unfold wordB
      by_cases hst : s = t
      · subst hst; simp
      · have h1 : ¬ (2 * s.val + 1 = 2 * t.val ∨ 2 * s.val + 1 = 2 * t.val + 1) := by
          have : s.val ≠ t.val := fun hc => hst (Fin.ext hc)
          omega
        have h2 : ¬ (2 * s.val + 1 < 2 * d ∧ (2 * s.val + 1) % 2 = 0) := by omega
        dsimp only
        rw [if_neg h1, if_neg h2, if_neg hst]
    have hrew : ∑ s : Fin d, wordB d t (⟨2 * s.val + 1, by have := s.isLt; omega⟩ : Fin k) =
        ∑ s : Fin d, (if s = t then 1 else 0) :=
      Finset.sum_congr rfl (fun s _ => hval s)
    rw [hrew]
    simp
  have hd1 : 1 ≤ d := by have := t.isLt; omega
  rw [hsum_even, hsum_odd]; omega

theorem construct_cover {n k : Nat} (hk : 2 ≤ k) (hn : n ≤ Nat.choose k (k / 2) + k / 2) :
    ∃ (c : Fin k → (Fin n → ZMod 2)) (z : Fin k → Fin n → (Fin n → ZMod 2)),
      ∀ i j : Fin n, i ≠ j → ∃ a, c a + z a i + z a j = unitV i := by
  let d := k / 2
  have hd2 : 2 * d ≤ k := by dsimp [d]; omega
  let setA : Finset (Fin k → Nat) :=
    ((Finset.univ : Finset (Fin k)).powersetCard d).image wordA
  let setB : Finset (Fin k → Nat) :=
    (Finset.univ : Finset (Fin d)).image (wordB d)
  have hcardA : setA.card = Nat.choose k d := by
    rw [Finset.card_image_of_injective _ wordA_inj, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]
  have hcardB : setB.card = d := by
    rw [Finset.card_image_of_injective _ (wordB_inj hd2), Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint setA setB := by
    rw [Finset.disjoint_left]
    intro w ha hb
    simp only [setA, setB, Finset.mem_image] at ha hb
    rcases ha with ⟨S, _, rfl⟩
    rcases hb with ⟨t, _, heq⟩
    exact wordA_ne_wordB hd2 S t heq.symm
  let W := setA ∪ setB
  have hcardW : W.card = Nat.choose k d + d := by
    rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB]
  have hle : Fintype.card (Fin n) ≤ Fintype.card W := by
    rw [Fintype.card_fin, Fintype.card_coe, hcardW]
    exact hn
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hle
  let w : Fin n → Fin k → Nat := fun i => (emb i).val
  have hw_inj : Function.Injective w := fun i j h => emb.injective (Subtype.ext h)
  have hw_sum : ∀ i : Fin n, ∑ a : Fin k, w i a = 2 * d := by
    intro i
    have hmem := (emb i).property
    simp only [W, Finset.mem_union, setA, setB, Finset.mem_image, Finset.mem_powersetCard] at hmem
    rcases hmem with ⟨S, ⟨_, hSc⟩, heq⟩ | ⟨t, _, heq⟩
    · change ∑ a : Fin k, (emb i).val a = 2 * d
      rw [← heq]; exact wordA_sum hSc
    · change ∑ a : Fin k, (emb i).val a = 2 * d
      rw [← heq]; exact wordB_sum hd2 t
  have hw_le2 : ∀ i : Fin n, ∀ a : Fin k, w i a ≤ 2 := by
    intro i a
    have hmem := (emb i).property
    simp only [W, Finset.mem_union, setA, setB, Finset.mem_image] at hmem
    rcases hmem with ⟨S, _, heq⟩ | ⟨t, _, heq⟩
    · change (emb i).val a ≤ 2
      rw [← heq]; unfold wordA; split_ifs <;> omega
    · change (emb i).val a ≤ 2
      rw [← heq]; unfold wordB; split_ifs <;> omega
  have hw_mid_uniq : ∀ (a : Fin k) (i j : Fin n), w i a = 1 → w j a = 1 → i = j := by
    intro a i j hi hj
    have getB : ∀ x : Fin n, w x a = 1 → ∃ t : Fin d, w x = wordB d t ∧ (a.val = 2 * t.val ∨ a.val = 2 * t.val + 1) := by
      intro x hx
      have hmem := (emb x).property
      simp only [W, Finset.mem_union, setA, setB, Finset.mem_image] at hmem
      rcases hmem with ⟨S, _, heq⟩ | ⟨t, _, heq⟩
      · have : wordA S a = 1 := by rw [heq]; exact hx
        unfold wordA at this; split_ifs at this <;> omega
      · refine ⟨t, heq.symm, ?_⟩
        have h1 : wordB d t a = 1 := by rw [heq]; exact hx
        unfold wordB at h1
        by_cases hcond : a.val = 2 * t.val ∨ a.val = 2 * t.val + 1
        · exact hcond
        · rw [if_neg hcond] at h1; split_ifs at h1 <;> omega
    obtain ⟨t1, h1, ha1⟩ := getB i hi
    obtain ⟨t2, h2, ha2⟩ := getB j hj
    have ht : t1 = t2 := Fin.ext (by omega)
    subst ht
    exact hw_inj (h1.trans h2.symm)
  classical
  let c : Fin k → (Fin n → ZMod 2) := fun a =>
    if h : ∃ m : Fin n, w m a = 1 then unitV (Classical.choose h) else 0
  let z : Fin k → Fin n → (Fin n → ZMod 2) := fun a x =>
    if w x a = 2 then unitV x + c a else 0
  refine ⟨c, z, ?_⟩
  intro i j hij
  have hgt : ∃ a : Fin k, w j a < w i a := by
    by_contra hall
    push_neg at hall
    have heq_all : ∀ a : Fin k, w i a = w j a := by
      intro a
      by_contra hne
      have hlt : w i a < w j a := lt_of_le_of_ne (hall a) hne
      have hsum_lt : ∑ b : Fin k, w i b < ∑ b : Fin k, w j b :=
        Finset.sum_lt_sum (fun b _ => hall b) ⟨a, Finset.mem_univ a, hlt⟩
      rw [hw_sum i, hw_sum j] at hsum_lt
      exact lt_irrefl _ hsum_lt
    exact hij (hw_inj (funext heq_all))
  obtain ⟨a, ha⟩ := hgt
  refine ⟨a, ?_⟩
  have hi2 := hw_le2 i a
  have hj2 := hw_le2 j a
  by_cases hi_eq2 : w i a = 2
  · have hj_ne2 : w j a ≠ 2 := by omega
    simp only [z, hi_eq2, ↓reduceIte, hj_ne2, add_zero]
    rw [add_comm (unitV i) (c a), ← add_assoc, zmod2_add_self, zero_add]
  · have hi_eq1 : w i a = 1 := by omega
    have hj_eq0 : w j a = 0 := by omega
    have hex : ∃ m : Fin n, w m a = 1 := ⟨i, hi_eq1⟩
    have hm_eq : Classical.choose hex = i := hw_mid_uniq a _ i (Classical.choose_spec hex) hi_eq1
    have hca : c a = unitV i := by simp only [c, dif_pos hex, hm_eq]
    have hzi : z a i = 0 := by simp [z, hi_eq1]
    have hzj : z a j = 0 := by simp [z, hj_eq0]
    rw [hca, hzi, hzj, add_zero, add_zero]

noncomputable def enc {n : Nat} (v : Fin n → ZMod 2) : ℚ :=
  ((Fintype.equivFin (Fin n → ZMod 2) v).val : ℚ)

theorem enc_inj {n : Nat} : Function.Injective (@enc n) := by
  intro v w h
  exact (Fintype.equivFin (Fin n → ZMod 2)).injective (Fin.ext (Nat.cast_injective h))

theorem bound_cover {n k : Nat} (c : Fin k → (Fin n → ZMod 2))
    (z : Fin k → Fin n → (Fin n → ZMod 2))
    (hcov : ∀ i j : Fin n, i ≠ j → ∃ a, c a + z a i + z a j = unitV i) :
    let exceptional := (Finset.univ : Finset (Fin n)).filter (fun i => ∃ a, c a = unitV i)
    n ≤ 2 ^ k + exceptional.card ∧ exceptional.card ≤ k := by
  intro exceptional
  classical
  have hex_card : exceptional.card ≤ k := by
    by_cases hk0 : k = 0
    · subst hk0
      have hemp : exceptional = ∅ := by
        ext i
        simp only [exceptional, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_exists]
        intro a; exact Fin.elim0 a
      rw [hemp]; simp
    · let g : Fin n → Fin k := fun i =>
        if h : ∃ a : Fin k, c a = unitV i then Classical.choose h else ⟨0, Nat.pos_of_ne_zero hk0⟩
      have hinj : Set.InjOn g exceptional := by
        intro i hi j hj heq
        have hi' : ∃ a : Fin k, c a = unitV i := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        have hj' : ∃ a : Fin k, c a = unitV j := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        simp only [g, dif_pos hi', dif_pos hj'] at heq
        have h1 : c (Classical.choose hi') = unitV i := Classical.choose_spec hi'
        have h2 : c (Classical.choose hj') = unitV j := Classical.choose_spec hj'
        rw [heq] at h1
        by_contra hne
        exact unitV_ne hne (h1.symm.trans h2)
      calc exceptional.card
          = (exceptional.image g).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = k := by rw [Finset.card_univ, Fintype.card_fin]
  let ordinary := (Finset.univ : Finset (Fin n)).filter (fun i => ¬ ∃ a, c a = unitV i)
  have hpart : ordinary.card + exceptional.card = n := by
    have hdisj : Disjoint ordinary exceptional := by
      rw [Finset.disjoint_left]
      intro i hi he
      exact (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp he).2
    have hunion : ordinary ∪ exceptional = Finset.univ := by
      ext i
      simp only [ordinary, exceptional, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      exact (em (∃ a, c a = unitV i)).symm
    have hcard := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at hcard
    exact hcard.symm
  have hord_le : ordinary.card ≤ 2 ^ k := by
    let t : Fin n → Fin k → (Fin n → ZMod 2) := fun i a => c a + unitV i + z a i
    let coeff : ordinary → (Finset (Fin k) → ℚ) := fun i S =>
      ∏ a ∈ Finset.univ \ S, (- enc (t i.val a))
    let mon : Fin n → (Finset (Fin k) → ℚ) := fun j S =>
      ∏ a ∈ S, enc (z a j)
    have heval : ∀ (i : ordinary) (j : Fin n),
        ∑ S : Finset (Fin k), coeff i S * mon j S =
          ∏ a : Fin k, (enc (z a j) - enc (t i.val a)) := by
      intro i j
      have hprod := Finset.prod_add (fun a : Fin k => enc (z a j)) (fun a : Fin k => - enc (t i.val a)) Finset.univ
      simp only [← sub_eq_add_neg] at hprod
      rw [hprod]
      have hpow : (Finset.univ : Finset (Fin k)).powerset = Finset.univ := by
        ext S; simp
      rw [hpow]
      apply Finset.sum_congr rfl
      intro S _
      dsimp only [coeff, mon]
      ring
    have hdiag : ∀ i : ordinary, ∏ a : Fin k, (enc (z a i.val) - enc (t i.val a)) ≠ 0 := by
      intro i
      rw [Finset.prod_ne_zero_iff]
      intro a _
      rw [sub_ne_zero]
      intro heq
      have hveq : z a i.val = t i.val a := enc_inj heq
      have hca : c a = unitV i.val := by
        have h1 : c a + unitV i.val = 0 := by
          have h2 : z a i.val + z a i.val = c a + unitV i.val + z a i.val + z a i.val :=
            congrArg (· + z a i.val) hveq
          rw [zmod2_add_self, add_assoc (c a + unitV i.val), zmod2_add_self, add_zero] at h2
          exact h2.symm
        have h3 : c a = c a + (unitV i.val + unitV i.val) := by rw [zmod2_add_self, add_zero]
        rw [← add_assoc, h1, zero_add] at h3
        exact h3
      have hnot := (Finset.mem_filter.mp i.property).2
      exact hnot ⟨a, hca⟩
    have hoff : ∀ (i : ordinary) (j : Fin n), i.val ≠ j →
        ∏ a : Fin k, (enc (z a j) - enc (t i.val a)) = 0 := by
      intro i j hij
      obtain ⟨a, ha⟩ := hcov i.val j hij
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      have hz_eq : z a j = t i.val a := by
        dsimp only [t]
        have h1 : (c a + z a i.val) + (c a + z a i.val + z a j) = (c a + z a i.val) + unitV i.val :=
          congrArg (fun v => (c a + z a i.val) + v) ha
        rw [← add_assoc, zmod2_add_self, zero_add] at h1
        rw [h1]
        abel
      rw [hz_eq, sub_self]
    have hli : LinearIndependent ℚ coeff := by
      rw [Fintype.linearIndependent_iff]
      intro α hsum j
      have hdot : ∑ S : Finset (Fin k), (∑ i : ordinary, α i • coeff i) S * mon j.val S = 0 := by
        rw [hsum]; simp
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul] at hdot
      rw [Finset.sum_comm] at hdot
      have hsimp : ∑ i : ordinary, ∑ S : Finset (Fin k), α i * coeff i S * mon j.val S =
          ∑ i : ordinary, α i * ∏ a : Fin k, (enc (z a j.val) - enc (t i.val a)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← heval i j.val, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _; ring
      rw [hsimp] at hdot
      rw [Finset.sum_eq_single j] at hdot
      · exact (mul_eq_zero.mp hdot).resolve_right (hdiag j)
      · intro i _ hij
        rw [hoff i j.val (fun h => hij (Subtype.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_coe, Module.finrank_pi, Fintype.card_finset, Fintype.card_fin] at hcard
    exact hcard
  exact ⟨by omega, hex_card⟩

end PEqualNP.Outside.L_lib_699_aux

theorem PEqualNP.Outside.L_lib_699 : (∀ (n k : Nat), 2 ≤ k →
  let V := Fin n → ZMod 2
  let unit := fun (i j : Fin n) => if j = i then (1 : ZMod 2) else 0
  let covers := fun (c : Fin k → V) (z : Fin k → Fin n → V) =>
    ∀ i j : Fin n, i ≠ j → ∃ a, c a + z a i + z a j = unit i
  (n ≤ Nat.choose k (k/2) + k/2 → ∃ c z, covers c z) ∧
    ∀ c z, covers c z →
      let exceptional := (Finset.univ : Finset (Fin n)).filter (fun i => ∃ a, c a = unit i)
      n ≤ 2^k + exceptional.card ∧ exceptional.card ≤ k) := by
  intro n k hk V unit covers
  exact ⟨PEqualNP.Outside.L_lib_699_aux.construct_cover hk,
    fun c z hcov => PEqualNP.Outside.L_lib_699_aux.bound_cover c z hcov⟩
