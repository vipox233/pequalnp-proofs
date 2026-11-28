import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset

namespace PEqualNP.Outside.L_lib_913

private def testOf {v m : Nat} (ends : Fin m → Fin v × Fin v) (z : Fin m × Bool) : Finset Nat :=
  {v + 2 * z.1.val, v + 2 * z.1.val + 1, if z.2 then (ends z.1).2.val else (ends z.1).1.val}

private lemma endVal_lt {v m : Nat} (ends : Fin m → Fin v × Fin v) (z : Fin m × Bool) :
    (if z.2 then (ends z.1).2.val else (ends z.1).1.val) < v := by
  cases z.2 with
  | false => exact (ends z.1).1.isLt
  | true => exact (ends z.1).2.isLt

private lemma testOf_card {v m : Nat} (ends : Fin m → Fin v × Fin v) (z : Fin m × Bool) :
    (testOf ends z).card = 3 := by
  have hlt := endVal_lt ends z
  unfold testOf
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

private lemma testOf_inj {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2) : Function.Injective (testOf ends) := by
  intro z1 z2 h
  have hlt1 := endVal_lt ends z1
  have hlt2 := endVal_lt ends z2
  have ha : v + 2 * z1.1.val ∈ testOf ends z2 := by
    rw [← h]
    simp [testOf]
  have he : z1.1 = z2.1 := by
    simp only [testOf, Finset.mem_insert, Finset.mem_singleton] at ha
    apply Fin.ext
    omega
  have hc : (if z1.2 then (ends z1.1).2.val else (ends z1.1).1.val) ∈ testOf ends z2 := by
    rw [← h]
    simp [testOf]
  simp only [testOf, Finset.mem_insert, Finset.mem_singleton] at hc
  have hceq : (if z1.2 then (ends z1.1).2.val else (ends z1.1).1.val) =
      (if z2.2 then (ends z2.1).2.val else (ends z2.1).1.val) := by
    omega
  have hb : z1.2 = z2.2 := by
    rw [he] at hceq
    cases hb1 : z1.2 <;> cases hb2 : z2.2
    · rfl
    · simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte] at hceq
      exact False.elim (hends z2.1 (Fin.ext hceq))
    · simp only [hb1, hb2, Bool.false_eq_true, ↓reduceIte] at hceq
      exact False.elim (hends z2.1 (Fin.ext hceq.symm))
    · rfl
  exact Prod.ext he hb

private lemma tests_card {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2) :
    (Finset.univ.image (testOf ends)).card = 2 * m := by
  rw [Finset.card_image_of_injective _ (testOf_inj ends hends), Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]

private lemma inter_testOf_twin {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2) (z : Fin m × Bool) :
    (testOf ends (z.1, !z.2) ∩ testOf ends z).card = 2 := by
  have hlt1 := endVal_lt ends (z.1, !z.2)
  have hlt2 := endVal_lt ends z
  have hne : (if !z.2 then (ends z.1).2.val else (ends z.1).1.val) ≠
      (if z.2 then (ends z.1).2.val else (ends z.1).1.val) := by
    cases hb : z.2
    · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      intro h
      exact hends z.1 (Fin.ext h.symm)
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      intro h
      exact hends z.1 (Fin.ext h)
  have heq : testOf ends (z.1, !z.2) ∩ testOf ends z = {v + 2 * z.1.val, v + 2 * z.1.val + 1} := by
    ext x
    simp only [testOf, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      omega
    · rintro (rfl | rfl) <;> simp
  rw [heq, Finset.card_insert_of_notMem, Finset.card_singleton]
  simp only [Finset.mem_singleton]
  omega

private lemma inter_testOf_ne_edge {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (z1 z2 : Fin m × Bool) (hne : z1.1 ≠ z2.1) :
    (testOf ends z1 ∩ testOf ends z2).card ≤ 1 := by
  have hlt2 := endVal_lt ends z2
  have hval : z1.1.val ≠ z2.1.val := fun h => hne (Fin.ext h)
  have hsub : testOf ends z1 ∩ testOf ends z2 ⊆
      {if z1.2 then (ends z1.1).2.val else (ends z1.1).1.val} := by
    intro x hx
    simp only [testOf, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    omega
  calc
    (testOf ends z1 ∩ testOf ends z2).card
      ≤ ({if z1.2 then (ends z1.1).2.val else (ends z1.1).1.val} : Finset Nat).card :=
        Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

private lemma twin_filter_card {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2) (z : Fin m × Bool) :
    ((Finset.univ.image (testOf ends)).filter
      (fun T => T ≠ testOf ends z ∧ (T ∩ testOf ends z).card = 2)).card = 1 := by
  have heq : (Finset.univ.image (testOf ends)).filter
      (fun T => T ≠ testOf ends z ∧ (T ∩ testOf ends z).card = 2) =
      {testOf ends (z.1, !z.2)} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨w, rfl⟩, hneT, hcard⟩
      have hwe : w.1 = z.1 := by
        by_contra hne
        have hle := inter_testOf_ne_edge ends w z hne
        omega
      have hwb : w.2 = !z.2 := by
        cases h1 : w.2 <;> cases h2 : z.2
        · exfalso
          exact hneT (congrArg (testOf ends) (Prod.ext hwe (h1.trans h2.symm)))
        · rfl
        · rfl
        · exfalso
          exact hneT (congrArg (testOf ends) (Prod.ext hwe (h1.trans h2.symm)))
      exact congrArg (testOf ends) (Prod.ext hwe hwb)
    · rintro rfl
      refine ⟨⟨(z.1, !z.2), rfl⟩, ?_, inter_testOf_twin ends hends z⟩
      intro hEq
      have hpr := testOf_inj ends hends hEq
      have hbf : (!z.2) = z.2 := congrArg Prod.snd hpr
      cases z.2 <;> simp at hbf
  rw [heq, Finset.card_singleton]

private def p0 (v m t : Nat) (e : Fin m) : Fin (v + 2 * m + t) :=
  ⟨v + 2 * e.val, by omega⟩

private def p1 (v m t : Nat) (e : Fin m) : Fin (v + 2 * m + t) :=
  ⟨v + 2 * e.val + 1, by omega⟩

private def u0 {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat) (e : Fin m) :
    Fin (v + 2 * m + t) :=
  ⟨(ends e).1.val, by have := (ends e).1.isLt; omega⟩

private def u1 {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat) (e : Fin m) :
    Fin (v + 2 * m + t) :=
  ⟨(ends e).2.val, by have := (ends e).2.isLt; omega⟩

private def uEnd {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat) (e : Fin m) (b : Bool) :
    Fin (v + 2 * m + t) :=
  if b then u1 ends t e else u0 ends t e

private lemma u0_ne_u1 {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2) (t : Nat) (e : Fin m) :
    u0 ends t e ≠ u1 ends t e := by
  intro h
  have hv : (u0 ends t e).val = (u1 ends t e).val := congrArg Fin.val h
  exact hends e (Fin.ext hv)

private lemma mem_testOf_iff {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat)
    (e : Fin m) (b : Bool) (x : Fin (v + 2 * m + t)) :
    x.val ∈ testOf ends (e, b) ↔ x = p0 v m t e ∨ x = p1 v m t e ∨ x = uEnd ends t e b := by
  cases b <;> simp only [testOf, uEnd, p0, p1, u0, u1, Finset.mem_insert, Finset.mem_singleton,
    Fin.ext_iff, Bool.false_eq_true, ↓reduceIte]

private abbrev IsMatching {v m : Nat} (ends : Fin m → Fin v × Fin v) (S : Finset (Fin m)) : Prop :=
  ∀ e ∈ S, ∀ g ∈ S, e ≠ g →
    Disjoint ({(ends e).1, (ends e).2} : Finset (Fin v)) {(ends g).1, (ends g).2}

private def Wins {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat)
    (P : Equiv.Perm (Fin (v + 2 * m + t))) : Prop :=
  Function.Involutive P ∧
    ∀ R ∈ Finset.univ.image (testOf ends),
      ∃ u : Fin (v + 2 * m + t), u.val ∈ R ∧ (P u).val ∈ R ∧ P u ≠ u

private def Active {v m : Nat} (t : Nat) (P : Equiv.Perm (Fin (v + 2 * m + t))) :
    Finset (Fin m) :=
  Finset.univ.filter (fun e : Fin m =>
    ¬ ∃ u : Fin (v + 2 * m + t), u.val = v + 2 * e.val ∧ (P u).val = v + 2 * e.val + 1)

private lemma mem_active_iff {v m : Nat} (t : Nat)
    (P : Equiv.Perm (Fin (v + 2 * m + t))) (e : Fin m) :
    e ∈ Active (v := v) t P ↔ P (p0 v m t e) ≠ p1 v m t e := by
  simp only [Active, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h hEq
    exact h ⟨p0 v m t e, rfl, congrArg Fin.val hEq⟩
  · intro hNe ⟨u, hu0, hu1⟩
    have hu : u = p0 v m t e := Fin.ext hu0
    rw [hu] at hu1
    exact hNe (Fin.ext hu1)

private lemma active_edge_end {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat)
    (P : Equiv.Perm (Fin (v + 2 * m + t))) (hW : Wins ends t P)
    (e : Fin m) (he : e ∈ Active (v := v) t P) (b : Bool) :
    P (uEnd ends t e b) = p0 v m t e ∨ P (uEnd ends t e b) = p1 v m t e := by
  have hne01 : P (p0 v m t e) ≠ p1 v m t e := (mem_active_iff t P e).mp he
  have hne10 : P (p1 v m t e) ≠ p0 v m t e := by
    intro h
    have := congrArg P h
    rw [hW.1] at this
    exact hne01 this.symm
  have hmem : testOf ends (e, b) ∈ Finset.univ.image (testOf ends) :=
    Finset.mem_image.mpr ⟨(e, b), Finset.mem_univ _, rfl⟩
  rcases hW.2 _ hmem with ⟨x, hxR, hPxR, hne⟩
  rw [mem_testOf_iff] at hxR hPxR
  rcases hxR with rfl | rfl | rfl
  · rcases hPxR with h | h | h
    · exact False.elim (hne h)
    · exact False.elim (hne01 h)
    · left
      rw [← h, hW.1]
  · rcases hPxR with h | h | h
    · exact False.elim (hne10 h)
    · exact False.elim (hne h)
    · right
      rw [← h, hW.1]
  · rcases hPxR with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hne h)

private lemma active_edge_pair {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2) (t : Nat)
    (P : Equiv.Perm (Fin (v + 2 * m + t))) (hW : Wins ends t P)
    (e : Fin m) (he : e ∈ Active (v := v) t P) :
    (P (p0 v m t e) = u0 ends t e ∧ P (p1 v m t e) = u1 ends t e) ∨
    (P (p0 v m t e) = u1 ends t e ∧ P (p1 v m t e) = u0 ends t e) := by
  have h0 := active_edge_end ends t P hW e he false
  have h1 := active_edge_end ends t P hW e he true
  simp only [uEnd, Bool.false_eq_true, ↓reduceIte] at h0 h1
  have hne : P (u0 ends t e) ≠ P (u1 ends t e) := fun h =>
    u0_ne_u1 ends hends t e (P.injective h)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact False.elim (hne (h0.trans h1.symm))
  · left
    exact ⟨by rw [← h0, hW.1], by rw [← h1, hW.1]⟩
  · right
    exact ⟨by rw [← h1, hW.1], by rw [← h0, hW.1]⟩
  · exact False.elim (hne (h0.trans h1.symm))

private lemma matching_of_wins {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (t : Nat)
    (P : Equiv.Perm (Fin (v + 2 * m + t))) (hW : Wins ends t P) :
    IsMatching ends (Active (v := v) t P) := by
  intro e he g hg hne
  rw [Finset.disjoint_left]
  intro w hwe hwg
  let x : Fin (v + 2 * m + t) := ⟨w.val, by have := w.isLt; omega⟩
  have hxe : x = u0 ends t e ∨ x = u1 ends t e := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwe
    rcases hwe with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hxg : x = u0 ends t g ∨ x = u1 ends t g := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwg
    rcases hwg with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hPe : P x = p0 v m t e ∨ P x = p1 v m t e := by
    rcases hxe with h | h
    · rw [h]; simpa [uEnd] using active_edge_end ends t P hW e he false
    · rw [h]; simpa [uEnd] using active_edge_end ends t P hW e he true
  have hPg : P x = p0 v m t g ∨ P x = p1 v m t g := by
    rcases hxg with h | h
    · rw [h]; simpa [uEnd] using active_edge_end ends t P hW g hg false
    · rw [h]; simpa [uEnd] using active_edge_end ends t P hW g hg true
  have hval : e.val = g.val := by
    rcases hPe with h1 | h1 <;> rcases hPg with h2 | h2
    · have := congrArg Fin.val (h1.symm.trans h2); simp only [p0] at this; omega
    · have := congrArg Fin.val (h1.symm.trans h2); simp only [p0, p1] at this; omega
    · have := congrArg Fin.val (h1.symm.trans h2); simp only [p0, p1] at this; omega
    · have := congrArg Fin.val (h1.symm.trans h2); simp only [p1] at this; omega
  exact hne (Fin.ext hval)

private def privSet (v m t : Nat) : Finset (Fin (v + 2 * m + t)) :=
  Finset.univ.filter (fun x => v ≤ x.val ∧ x.val < v + 2 * m)

private def usedOrig {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat)
    (S : Finset (Fin m)) : Finset (Fin (v + 2 * m + t)) :=
  S.biUnion (fun e => {u0 ends t e, u1 ends t e})

private def remSet {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat)
    (S : Finset (Fin m)) : Finset (Fin (v + 2 * m + t)) :=
  Finset.univ \ (privSet v m t ∪ usedOrig ends t S)

private lemma p0_mem_privSet (v m t : Nat) (e : Fin m) :
    p0 v m t e ∈ privSet v m t := by
  simp only [privSet, p0, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

private lemma p1_mem_privSet (v m t : Nat) (e : Fin m) :
    p1 v m t e ∈ privSet v m t := by
  simp only [privSet, p1, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

private lemma u0_notMem_privSet {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat) (e : Fin m) :
    u0 ends t e ∉ privSet v m t := by
  simp only [privSet, u0, Finset.mem_filter, Finset.mem_univ, true_and]
  have := (ends e).1.isLt
  omega

private lemma u1_notMem_privSet {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat) (e : Fin m) :
    u1 ends t e ∉ privSet v m t := by
  simp only [privSet, u1, Finset.mem_filter, Finset.mem_univ, true_and]
  have := (ends e).2.isLt
  omega

private lemma privSet_cases {v m t : Nat} {x : Fin (v + 2 * m + t)} (hx : x ∈ privSet v m t) :
    ∃ e : Fin m, x = p0 v m t e ∨ x = p1 v m t e := by
  have h1 : v ≤ x.val ∧ x.val < v + 2 * m := (Finset.mem_filter.mp hx).2
  refine ⟨⟨(x.val - v) / 2, by omega⟩, ?_⟩
  by_cases hp : (x.val - v) % 2 = 0
  · left
    apply Fin.ext
    simp only [p0]
    omega
  · right
    apply Fin.ext
    simp only [p1]
    omega

private lemma privSet_card (v m t : Nat) : (privSet v m t).card = 2 * m := by
  let f : Fin (2 * m) → Fin (v + 2 * m + t) := fun i => ⟨v + i.val, by omega⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [f] at this
    omega
  have heq : privSet v m t = Finset.univ.image f := by
    ext x
    simp only [privSet, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x.val - v, by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [f]
      omega
    · rintro ⟨i, rfl⟩
      dsimp [f]
      omega
  rw [heq, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

private lemma usedOrig_card {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2) (t : Nat)
    (S : Finset (Fin m)) (hM : IsMatching ends S) :
    (usedOrig ends t S).card = 2 * S.card := by
  have hpw : (S : Set (Fin m)).PairwiseDisjoint (fun e => ({u0 ends t e, u1 ends t e} : Finset _)) := by
    intro e he g hg hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxe hxg
    have hdisj := hM e he g hg hne
    rw [Finset.disjoint_left] at hdisj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxe hxg
    rcases hxe with rfl | rfl <;> rcases hxg with h | h
    · have hv : (u0 ends t e).val = (u0 ends t g).val := congrArg Fin.val h
      have hw : (ends e).1 = (ends g).1 := Fin.ext hv
      exact hdisj (a := (ends e).1) (by simp) (by simp [hw])
    · have hv : (u0 ends t e).val = (u1 ends t g).val := congrArg Fin.val h
      have hw : (ends e).1 = (ends g).2 := Fin.ext hv
      exact hdisj (a := (ends e).1) (by simp) (by simp [hw])
    · have hv : (u1 ends t e).val = (u0 ends t g).val := congrArg Fin.val h
      have hw : (ends e).2 = (ends g).1 := Fin.ext hv
      exact hdisj (a := (ends e).2) (by simp) (by simp [hw])
    · have hv : (u1 ends t e).val = (u1 ends t g).val := congrArg Fin.val h
      have hw : (ends e).2 = (ends g).2 := Fin.ext hv
      exact hdisj (a := (ends e).2) (by simp) (by simp [hw])
  rw [usedOrig, Finset.card_biUnion hpw]
  have h2 : ∀ e ∈ S, ({u0 ends t e, u1 ends t e} : Finset (Fin (v + 2 * m + t))).card = 2 := by
    intro e _
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp only [Finset.mem_singleton]
    exact u0_ne_u1 ends hends t e
  rw [Finset.sum_const_nat h2, Nat.mul_comm]

private lemma disjoint_priv_usedOrig {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat)
    (S : Finset (Fin m)) : Disjoint (privSet v m t) (usedOrig ends t S) := by
  rw [Finset.disjoint_left]
  intro x hp hu
  rw [usedOrig, Finset.mem_biUnion] at hu
  rcases hu with ⟨e, _, hx⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact u0_notMem_privSet ends t e hp
  · exact u1_notMem_privSet ends t e hp

private lemma remSet_card {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2) (t : Nat)
    (S : Finset (Fin m)) (hM : IsMatching ends S) :
    (remSet ends t S).card = v + t - 2 * S.card := by
  rw [remSet, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    Finset.card_union_of_disjoint (disjoint_priv_usedOrig ends t S),
    privSet_card, usedOrig_card ends hends t S hM]
  omega

private lemma matching_edge_unique {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat)
    (S : Finset (Fin m)) (hM : IsMatching ends S)
    {e1 e2 : Fin m} (he1 : e1 ∈ S) (he2 : e2 ∈ S)
    {x : Fin (v + 2 * m + t)}
    (hx1 : x = u0 ends t e1 ∨ x = u1 ends t e1)
    (hx2 : x = u0 ends t e2 ∨ x = u1 ends t e2) : e1 = e2 := by
  by_contra hne
  have hdisj := hM e1 he1 e2 he2 hne
  rw [Finset.disjoint_left] at hdisj
  rcases hx1 with rfl | rfl <;> rcases hx2 with h | h
  · have hv : (u0 ends t e1).val = (u0 ends t e2).val := congrArg Fin.val h
    have hw : (ends e1).1 = (ends e2).1 := Fin.ext hv
    exact hdisj (a := (ends e1).1) (by simp) (by simp [hw])
  · have hv : (u0 ends t e1).val = (u1 ends t e2).val := congrArg Fin.val h
    have hw : (ends e1).1 = (ends e2).2 := Fin.ext hv
    exact hdisj (a := (ends e1).1) (by simp) (by simp [hw])
  · have hv : (u1 ends t e1).val = (u0 ends t e2).val := congrArg Fin.val h
    have hw : (ends e1).2 = (ends e2).1 := Fin.ext hv
    exact hdisj (a := (ends e1).2) (by simp) (by simp [hw])
  · have hv : (u1 ends t e1).val = (u1 ends t e2).val := congrArg Fin.val h
    have hw : (ends e1).2 = (ends e2).2 := Fin.ext hv
    exact hdisj (a := (ends e1).2) (by simp) (by simp [hw])

private def privBranch {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (t : Nat) (S : Finset (Fin m)) (dir : S → Bool)
    (e : Fin m) (isOdd : Bool) : Fin (v + 2 * m + t) :=
  if hS : e ∈ S then
    if isOdd then
      if dir ⟨e, hS⟩ then u0 ends t e else u1 ends t e
    else
      if dir ⟨e, hS⟩ then u1 ends t e else u0 ends t e
  else
    if isOdd then p0 v m t e else p1 v m t e

private def usedBranch {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (t : Nat) (S : Finset (Fin m)) (dir : S → Bool)
    (e : S) (x : Fin (v + 2 * m + t)) : Fin (v + 2 * m + t) :=
  if x = u0 ends t e.1 then
    if dir e then p1 v m t e.1 else p0 v m t e.1
  else
    if dir e then p0 v m t e.1 else p1 v m t e.1

private noncomputable def buildFun {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (t : Nat) (S : Finset (Fin m)) (dir : S → Bool)
    (Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S})
    (x : Fin (v + 2 * m + t)) : Fin (v + 2 * m + t) :=
  if hp : x ∈ privSet v m t then
    let e : Fin m := ⟨(x.val - v) / 2, by
      have h1 : v ≤ x.val ∧ x.val < v + 2 * m := (Finset.mem_filter.mp hp).2
      omega⟩
    privBranch ends t S dir e (decide ((x.val - v) % 2 = 1))
  else if hu : x ∈ usedOrig ends t S then
    let hex : ∃ e ∈ S, x = u0 ends t e ∨ x = u1 ends t e := by
      rw [usedOrig, Finset.mem_biUnion] at hu
      rcases hu with ⟨e, he, hx⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      exact ⟨e, he, hx⟩
    let e : Fin m := Classical.choose hex
    have hspec : e ∈ S ∧ (x = u0 ends t e ∨ x = u1 ends t e) := Classical.choose_spec hex
    usedBranch ends t S dir ⟨e, hspec.1⟩ x
  else
    have hr : x ∈ remSet ends t S := by
      rw [remSet, Finset.mem_sdiff, Finset.mem_union]
      exact ⟨Finset.mem_univ _, fun h => h.elim hp hu⟩
    (Q ⟨x, hr⟩).val

private lemma buildFun_p0_notMem {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (t : Nat) (S : Finset (Fin m)) (dir : S → Bool)
    (Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S})
    (e : Fin m) (hS : e ∉ S) :
    buildFun ends t S dir Q (p0 v m t e) = p1 v m t e := by
  have hp := p0_mem_privSet v m t e
  unfold buildFun
  simp only [hp, ↓reduceDIte]
  have he : (⟨((p0 v m t e).val - v) / 2, by
      have h1 : v ≤ (p0 v m t e).val ∧ (p0 v m t e).val < v + 2 * m := (Finset.mem_filter.mp hp).2
      omega⟩ : Fin m) = e := by
    apply Fin.ext
    simp only [p0]
    omega
  have hb : decide (((p0 v m t e).val - v) % 2 = 1) = false := by
    rw [decide_eq_false_iff_not]
    simp only [p0]
    omega
  rw [he, hb]
  simp only [privBranch, hS, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]

private lemma buildFun_p1_notMem {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (t : Nat) (S : Finset (Fin m)) (dir : S → Bool)
    (Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S})
    (e : Fin m) (hS : e ∉ S) :
    buildFun ends t S dir Q (p1 v m t e) = p0 v m t e := by
  have hp := p1_mem_privSet v m t e
  unfold buildFun
  simp only [hp, ↓reduceDIte]
  have he : (⟨((p1 v m t e).val - v) / 2, by
      have h1 : v ≤ (p1 v m t e).val ∧ (p1 v m t e).val < v + 2 * m := (Finset.mem_filter.mp hp).2
      omega⟩ : Fin m) = e := by
    apply Fin.ext
    simp only [p1]
    omega
  have hb : decide (((p1 v m t e).val - v) % 2 = 1) = true := by
    rw [decide_eq_true_eq]
    simp only [p1]
    omega
  rw [he, hb]
  simp only [privBranch, hS, ↓reduceDIte, ↓reduceIte]

private lemma buildFun_p0_mem {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (t : Nat) (S : Finset (Fin m)) (dir : S → Bool)
    (Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S})
    (e : Fin m) (hS : e ∈ S) :
    buildFun ends t S dir Q (p0 v m t e) =
      if dir ⟨e, hS⟩ then u1 ends t e else u0 ends t e := by
  have hp := p0_mem_privSet v m t e
  unfold buildFun
  simp only [hp, ↓reduceDIte]
  have he : (⟨((p0 v m t e).val - v) / 2, by
      have h1 : v ≤ (p0 v m t e).val ∧ (p0 v m t e).val < v + 2 * m := (Finset.mem_filter.mp hp).2
      omega⟩ : Fin m) = e := by
    apply Fin.ext
    simp only [p0]
    omega
  have hb : decide (((p0 v m t e).val - v) % 2 = 1) = false := by
    rw [decide_eq_false_iff_not]
    simp only [p0]
    omega
  rw [he, hb]
  simp only [privBranch, hS, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]

private lemma buildFun_p1_mem {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (t : Nat) (S : Finset (Fin m)) (dir : S → Bool)
    (Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S})
    (e : Fin m) (hS : e ∈ S) :
    buildFun ends t S dir Q (p1 v m t e) =
      if dir ⟨e, hS⟩ then u0 ends t e else u1 ends t e := by
  have hp := p1_mem_privSet v m t e
  unfold buildFun
  simp only [hp, ↓reduceDIte]
  have he : (⟨((p1 v m t e).val - v) / 2, by
      have h1 : v ≤ (p1 v m t e).val ∧ (p1 v m t e).val < v + 2 * m := (Finset.mem_filter.mp hp).2
      omega⟩ : Fin m) = e := by
    apply Fin.ext
    simp only [p1]
    omega
  have hb : decide (((p1 v m t e).val - v) % 2 = 1) = true := by
    rw [decide_eq_true_eq]
    simp only [p1]
    omega
  rw [he, hb]
  simp only [privBranch, hS, ↓reduceDIte, ↓reduceIte]

private lemma buildFun_u0_mem {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (t : Nat) (S : Finset (Fin m)) (hM : IsMatching ends S) (dir : S → Bool)
    (Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S})
    (e : Fin m) (hS : e ∈ S) :
    buildFun ends t S dir Q (u0 ends t e) =
      if dir ⟨e, hS⟩ then p1 v m t e else p0 v m t e := by
  have hnp := u0_notMem_privSet ends t e
  have hu : u0 ends t e ∈ usedOrig ends t S := by
    rw [usedOrig, Finset.mem_biUnion]
    exact ⟨e, hS, by simp⟩
  unfold buildFun
  simp only [hnp, hu, ↓reduceDIte]
  set hex : ∃ g ∈ S, u0 ends t e = u0 ends t g ∨ u0 ends t e = u1 ends t g := by
    rw [usedOrig, Finset.mem_biUnion] at hu
    rcases hu with ⟨g, hg, hx⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    exact ⟨g, hg, hx⟩
  have hspec := Classical.choose_spec hex
  have heq : Classical.choose hex = e :=
    matching_edge_unique ends t S hM hspec.1 hS hspec.2 (Or.inl rfl)
  have hsub : (⟨Classical.choose hex, hspec.1⟩ : S) = ⟨e, hS⟩ := Subtype.ext heq
  rw [hsub]
  simp only [usedBranch, ↓reduceIte]

private lemma buildFun_u1_mem {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2)
    (t : Nat) (S : Finset (Fin m)) (hM : IsMatching ends S) (dir : S → Bool)
    (Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S})
    (e : Fin m) (hS : e ∈ S) :
    buildFun ends t S dir Q (u1 ends t e) =
      if dir ⟨e, hS⟩ then p0 v m t e else p1 v m t e := by
  have hnp := u1_notMem_privSet ends t e
  have hu : u1 ends t e ∈ usedOrig ends t S := by
    rw [usedOrig, Finset.mem_biUnion]
    exact ⟨e, hS, by simp⟩
  unfold buildFun
  simp only [hnp, hu, ↓reduceDIte]
  set hex : ∃ g ∈ S, u1 ends t e = u0 ends t g ∨ u1 ends t e = u1 ends t g := by
    rw [usedOrig, Finset.mem_biUnion] at hu
    rcases hu with ⟨g, hg, hx⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    exact ⟨g, hg, hx⟩
  have hspec := Classical.choose_spec hex
  have heq : Classical.choose hex = e :=
    matching_edge_unique ends t S hM hspec.1 hS hspec.2 (Or.inr rfl)
  have hsub : (⟨Classical.choose hex, hspec.1⟩ : S) = ⟨e, hS⟩ := Subtype.ext heq
  rw [hsub]
  have hne : u1 ends t e ≠ u0 ends t e := (u0_ne_u1 ends hends t e).symm
  simp only [usedBranch, hne, ↓reduceIte]

private lemma buildFun_rem {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (t : Nat) (S : Finset (Fin m)) (dir : S → Bool)
    (Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S})
    {x : Fin (v + 2 * m + t)} (hx : x ∈ remSet ends t S) :
    buildFun ends t S dir Q x = (Q ⟨x, hx⟩).val := by
  have hnot : x ∉ privSet v m t ∪ usedOrig ends t S := (Finset.mem_sdiff.mp hx).2
  rw [Finset.mem_union, not_or] at hnot
  unfold buildFun
  simp only [hnot.1, hnot.2, ↓reduceDIte]

private lemma buildFun_involutive {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2)
    (t : Nat) (S : Finset (Fin m)) (hM : IsMatching ends S) (dir : S → Bool)
    (Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S})
    (hQ : Function.Involutive Q) :
    Function.Involutive (buildFun ends t S dir Q) := by
  intro x
  by_cases hp : x ∈ privSet v m t
  · rcases privSet_cases hp with ⟨e, rfl | rfl⟩
    · by_cases hS : e ∈ S
      · rw [buildFun_p0_mem ends t S dir Q e hS]
        cases hd : dir ⟨e, hS⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [buildFun_u0_mem ends t S hM dir Q e hS, hd]
          rfl
        · simp only [↓reduceIte]
          rw [buildFun_u1_mem ends hends t S hM dir Q e hS, hd]
          rfl
      · rw [buildFun_p0_notMem ends t S dir Q e hS, buildFun_p1_notMem ends t S dir Q e hS]
    · by_cases hS : e ∈ S
      · rw [buildFun_p1_mem ends t S dir Q e hS]
        cases hd : dir ⟨e, hS⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [buildFun_u1_mem ends hends t S hM dir Q e hS, hd]
          rfl
        · simp only [↓reduceIte]
          rw [buildFun_u0_mem ends t S hM dir Q e hS, hd]
          rfl
      · rw [buildFun_p1_notMem ends t S dir Q e hS, buildFun_p0_notMem ends t S dir Q e hS]
  · by_cases hu : x ∈ usedOrig ends t S
    · rw [usedOrig, Finset.mem_biUnion] at hu
      rcases hu with ⟨e, hS, hx⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [buildFun_u0_mem ends t S hM dir Q e hS]
        cases hd : dir ⟨e, hS⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [buildFun_p0_mem ends t S dir Q e hS, hd]
          rfl
        · simp only [↓reduceIte]
          rw [buildFun_p1_mem ends t S dir Q e hS, hd]
          rfl
      · rw [buildFun_u1_mem ends hends t S hM dir Q e hS]
        cases hd : dir ⟨e, hS⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [buildFun_p1_mem ends t S dir Q e hS, hd]
          rfl
        · simp only [↓reduceIte]
          rw [buildFun_p0_mem ends t S dir Q e hS, hd]
          rfl
    · have hr : x ∈ remSet ends t S := by
        rw [remSet, Finset.mem_sdiff, Finset.mem_union]
        exact ⟨Finset.mem_univ _, fun h => h.elim hp hu⟩
      rw [buildFun_rem ends t S dir Q hr, buildFun_rem ends t S dir Q (Q ⟨x, hr⟩).2]
      exact congrArg Subtype.val (hQ ⟨x, hr⟩)

private noncomputable def buildPerm {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2)
    (t : Nat) (S : Finset (Fin m)) (hM : IsMatching ends S) (dir : S → Bool)
    (Q : {Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S} //
      Function.Involutive Q}) :
    Equiv.Perm (Fin (v + 2 * m + t)) :=
  (buildFun_involutive ends hends t S hM dir Q.1 Q.2).toPerm

private lemma buildPerm_wins {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2)
    (t : Nat) (S : Finset (Fin m)) (hM : IsMatching ends S) (dir : S → Bool)
    (Q : {Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S} //
      Function.Involutive Q}) :
    Wins ends t (buildPerm ends hends t S hM dir Q) := by
  refine ⟨buildFun_involutive ends hends t S hM dir Q.1 Q.2, ?_⟩
  intro R hR
  rw [Finset.mem_image] at hR
  rcases hR with ⟨⟨e, b⟩, _, rfl⟩
  by_cases hS : e ∈ S
  · cases b with
    | false =>
      refine ⟨u0 ends t e, ?_, ?_, ?_⟩
      · rw [mem_testOf_iff]
        right; right; rfl
      · rw [mem_testOf_iff]
        have hv : buildPerm ends hends t S hM dir Q (u0 ends t e) =
            if dir ⟨e, hS⟩ then p1 v m t e else p0 v m t e :=
          buildFun_u0_mem ends t S hM dir Q.1 e hS
        rw [hv]
        cases dir ⟨e, hS⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · have hv : buildPerm ends hends t S hM dir Q (u0 ends t e) =
            if dir ⟨e, hS⟩ then p1 v m t e else p0 v m t e :=
          buildFun_u0_mem ends t S hM dir Q.1 e hS
        rw [hv]
        have hlt := (ends e).1.isLt
        cases dir ⟨e, hS⟩ <;> intro h <;>
          have := congrArg Fin.val h <;> simp only [p0, p1, u0, Bool.false_eq_true, ↓reduceIte] at this <;> omega
    | true =>
      refine ⟨u1 ends t e, ?_, ?_, ?_⟩
      · rw [mem_testOf_iff]
        right; right; rfl
      · rw [mem_testOf_iff]
        have hv : buildPerm ends hends t S hM dir Q (u1 ends t e) =
            if dir ⟨e, hS⟩ then p0 v m t e else p1 v m t e :=
          buildFun_u1_mem ends hends t S hM dir Q.1 e hS
        rw [hv]
        cases dir ⟨e, hS⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
      · have hv : buildPerm ends hends t S hM dir Q (u1 ends t e) =
            if dir ⟨e, hS⟩ then p0 v m t e else p1 v m t e :=
          buildFun_u1_mem ends hends t S hM dir Q.1 e hS
        rw [hv]
        have hlt := (ends e).2.isLt
        cases dir ⟨e, hS⟩ <;> intro h <;>
          have := congrArg Fin.val h <;> simp only [p0, p1, u1, Bool.false_eq_true, ↓reduceIte] at this <;> omega
  · refine ⟨p0 v m t e, ?_, ?_, ?_⟩
    · rw [mem_testOf_iff]
      left; rfl
    · rw [mem_testOf_iff]
      have hv : buildPerm ends hends t S hM dir Q (p0 v m t e) = p1 v m t e :=
        buildFun_p0_notMem ends t S dir Q.1 e hS
      rw [hv]
      right; left; rfl
    · have hv : buildPerm ends hends t S hM dir Q (p0 v m t e) = p1 v m t e :=
        buildFun_p0_notMem ends t S dir Q.1 e hS
      rw [hv]
      intro h
      have := congrArg Fin.val h
      simp only [p0, p1] at this
      omega

private lemma buildPerm_active {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2)
    (t : Nat) (S : Finset (Fin m)) (hM : IsMatching ends S) (dir : S → Bool)
    (Q : {Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S} //
      Function.Involutive Q}) :
    Active (v := v) t (buildPerm ends hends t S hM dir Q) = S := by
  ext e
  rw [mem_active_iff]
  change buildFun ends t S dir Q.1 (p0 v m t e) ≠ p1 v m t e ↔ e ∈ S
  by_cases hS : e ∈ S
  · simp only [hS, iff_true]
    rw [buildFun_p0_mem ends t S dir Q.1 e hS]
    have hlt1 := (ends e).1.isLt
    have hlt2 := (ends e).2.isLt
    cases dir ⟨e, hS⟩ <;> intro h <;>
      have := congrArg Fin.val h <;> simp only [p1, u0, u1, Bool.false_eq_true, ↓reduceIte] at this <;> omega
  · simp only [hS, iff_false, not_not]
    exact buildFun_p0_notMem ends t S dir Q.1 e hS

private lemma P_maps_remSet {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2)
    (t : Nat) (S : Finset (Fin m))
    (P : Equiv.Perm (Fin (v + 2 * m + t)))
    (hW : Wins ends t P) (hA : Active (v := v) t P = S)
    {x : Fin (v + 2 * m + t)} (hx : x ∈ remSet ends t S) :
    P x ∈ remSet ends t S := by
  have hnot : x ∉ privSet v m t ∪ usedOrig ends t S := (Finset.mem_sdiff.mp hx).2
  rw [Finset.mem_union, not_or] at hnot
  rw [remSet, Finset.mem_sdiff, Finset.mem_union]
  refine ⟨Finset.mem_univ _, ?_⟩
  rintro (hp | hu)
  · rcases privSet_cases hp with ⟨e, heq | heq⟩
    · by_cases hS : e ∈ S
      · have heA : e ∈ Active (v := v) t P := hA.symm ▸ hS
        have hpair := active_edge_pair ends hends t P hW e heA
        have hxEq : x = P (p0 v m t e) := by rw [← heq, hW.1]
        apply hnot.2
        rw [usedOrig, Finset.mem_biUnion]
        rcases hpair with ⟨h0, _⟩ | ⟨h0, _⟩
        · exact ⟨e, hS, by simp [hxEq, h0]⟩
        · exact ⟨e, hS, by simp [hxEq, h0]⟩
      · have hnotA : e ∉ Active (v := v) t P := fun h => hS (hA ▸ h)
        rw [mem_active_iff, not_not] at hnotA
        have hxEq : x = p1 v m t e := by rw [← hnotA, ← heq, hW.1]
        exact hnot.1 (hxEq ▸ p1_mem_privSet v m t e)
    · by_cases hS : e ∈ S
      · have heA : e ∈ Active (v := v) t P := hA.symm ▸ hS
        have hpair := active_edge_pair ends hends t P hW e heA
        have hxEq : x = P (p1 v m t e) := by rw [← heq, hW.1]
        apply hnot.2
        rw [usedOrig, Finset.mem_biUnion]
        rcases hpair with ⟨_, h1⟩ | ⟨_, h1⟩
        · exact ⟨e, hS, by simp [hxEq, h1]⟩
        · exact ⟨e, hS, by simp [hxEq, h1]⟩
      · have hnotA : e ∉ Active (v := v) t P := fun h => hS (hA ▸ h)
        rw [mem_active_iff, not_not] at hnotA
        have h10 : P (p1 v m t e) = p0 v m t e := by rw [← hnotA, hW.1]
        have hxEq : x = p0 v m t e := by rw [← h10, ← heq, hW.1]
        exact hnot.1 (hxEq ▸ p0_mem_privSet v m t e)
  · rw [usedOrig, Finset.mem_biUnion] at hu
    rcases hu with ⟨e, hS, hPx⟩
    have heA : e ∈ Active (v := v) t P := hA.symm ▸ hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hPx
    have hpair := active_edge_pair ends hends t P hW e heA
    apply hnot.1
    rcases hPx with hPx | hPx
    · have hxEq : x = P (u0 ends t e) := by rw [← hPx, hW.1]
      rcases hpair with ⟨h0, _⟩ | ⟨_, h1⟩
      · have : x = p0 v m t e := by rw [hxEq, ← h0, hW.1]
        exact this ▸ p0_mem_privSet v m t e
      · have : x = p1 v m t e := by rw [hxEq, ← h1, hW.1]
        exact this ▸ p1_mem_privSet v m t e
    · have hxEq : x = P (u1 ends t e) := by rw [← hPx, hW.1]
      rcases hpair with ⟨_, h1⟩ | ⟨h0, _⟩
      · have : x = p1 v m t e := by rw [hxEq, ← h1, hW.1]
        exact this ▸ p1_mem_privSet v m t e
      · have : x = p0 v m t e := by rw [hxEq, ← h0, hW.1]
        exact this ▸ p0_mem_privSet v m t e

private def extractDir {v m : Nat} (ends : Fin m → Fin v × Fin v) (t : Nat)
    (S : Finset (Fin m)) (P : Equiv.Perm (Fin (v + 2 * m + t))) : S → Bool :=
  fun e => decide (P (p0 v m t e.1) = u1 ends t e.1)

private def extractQ {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2)
    (t : Nat) (S : Finset (Fin m))
    (P : Equiv.Perm (Fin (v + 2 * m + t)))
    (hW : Wins ends t P) (hA : Active (v := v) t P = S) :
    {Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S} //
      Function.Involutive Q} :=
  let f : {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S} →
      {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S} :=
    fun x => ⟨P x.1, P_maps_remSet ends hends t S P hW hA x.2⟩
  have hf : Function.Involutive f := fun x => Subtype.ext (hW.1 x.1)
  ⟨hf.toPerm, hf⟩

private noncomputable def fiberEquiv {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2)
    (t : Nat) (S : Finset (Fin m)) (hM : IsMatching ends S) :
    {P : Equiv.Perm (Fin (v + 2 * m + t)) // Wins ends t P ∧ Active (v := v) t P = S} ≃
      (S → Bool) × {Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S} //
        Function.Involutive Q} where
  toFun P := (extractDir ends t S P.1, extractQ ends hends t S P.1 P.2.1 P.2.2)
  invFun dq := ⟨buildPerm ends hends t S hM dq.1 dq.2,
    buildPerm_wins ends hends t S hM dq.1 dq.2,
    buildPerm_active ends hends t S hM dq.1 dq.2⟩
  left_inv := by
    rintro ⟨P, hW, hA⟩
    apply Subtype.ext
    ext x
    change (buildFun ends t S (extractDir ends t S P)
      (extractQ ends hends t S P hW hA).1 x).val = (P x).val
    congr 1
    by_cases hp : x ∈ privSet v m t
    · rcases privSet_cases hp with ⟨e, rfl | rfl⟩
      · by_cases hS : e ∈ S
        · rw [buildFun_p0_mem ends t S _ _ e hS]
          have heA : e ∈ Active (v := v) t P := hA.symm ▸ hS
          rcases active_edge_pair ends hends t P hW e heA with ⟨h0, _⟩ | ⟨h0, _⟩
          · have hd : extractDir ends t S P ⟨e, hS⟩ = false := by
              simp only [extractDir, decide_eq_false_iff_not, h0]
              exact u0_ne_u1 ends hends t e
            rw [hd]
            exact h0.symm
          · have hd : extractDir ends t S P ⟨e, hS⟩ = true := by
              simp only [extractDir, decide_eq_true_eq, h0]
            rw [hd]
            exact h0.symm
        · rw [buildFun_p0_notMem ends t S _ _ e hS]
          have hnotA : e ∉ Active (v := v) t P := fun h => hS (hA ▸ h)
          rw [mem_active_iff, not_not] at hnotA
          exact hnotA.symm
      · by_cases hS : e ∈ S
        · rw [buildFun_p1_mem ends t S _ _ e hS]
          have heA : e ∈ Active (v := v) t P := hA.symm ▸ hS
          rcases active_edge_pair ends hends t P hW e heA with ⟨h0, h1⟩ | ⟨h0, h1⟩
          · have hd : extractDir ends t S P ⟨e, hS⟩ = false := by
              simp only [extractDir, decide_eq_false_iff_not, h0]
              exact u0_ne_u1 ends hends t e
            rw [hd]
            exact h1.symm
          · have hd : extractDir ends t S P ⟨e, hS⟩ = true := by
              simp only [extractDir, decide_eq_true_eq, h0]
            rw [hd]
            exact h1.symm
        · rw [buildFun_p1_notMem ends t S _ _ e hS]
          have hnotA : e ∉ Active (v := v) t P := fun h => hS (hA ▸ h)
          rw [mem_active_iff, not_not] at hnotA
          have h10 : P (p1 v m t e) = p0 v m t e := by rw [← hnotA, hW.1]
          exact h10.symm
    · by_cases hu : x ∈ usedOrig ends t S
      · rw [usedOrig, Finset.mem_biUnion] at hu
        rcases hu with ⟨e, hS, hx⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        have heA : e ∈ Active (v := v) t P := hA.symm ▸ hS
        rcases hx with rfl | rfl
        · rw [buildFun_u0_mem ends t S hM _ _ e hS]
          rcases active_edge_pair ends hends t P hW e heA with ⟨h0, _⟩ | ⟨h0, h1⟩
          · have hd : extractDir ends t S P ⟨e, hS⟩ = false := by
              simp only [extractDir, decide_eq_false_iff_not, h0]
              exact u0_ne_u1 ends hends t e
            simp only [hd, Bool.false_eq_true, ↓reduceIte]
            rw [← h0, hW.1]
          · have hd : extractDir ends t S P ⟨e, hS⟩ = true := by
              simp only [extractDir, decide_eq_true_eq, h0]
            simp only [hd, ↓reduceIte]
            rw [← h1, hW.1]
        · rw [buildFun_u1_mem ends hends t S hM _ _ e hS]
          rcases active_edge_pair ends hends t P hW e heA with ⟨h0, h1⟩ | ⟨h0, _⟩
          · have hd : extractDir ends t S P ⟨e, hS⟩ = false := by
              simp only [extractDir, decide_eq_false_iff_not, h0]
              exact u0_ne_u1 ends hends t e
            simp only [hd, Bool.false_eq_true, ↓reduceIte]
            rw [← h1, hW.1]
          · have hd : extractDir ends t S P ⟨e, hS⟩ = true := by
              simp only [extractDir, decide_eq_true_eq, h0]
            simp only [hd, ↓reduceIte]
            rw [← h0, hW.1]
      · have hr : x ∈ remSet ends t S := by
          rw [remSet, Finset.mem_sdiff, Finset.mem_union]
          exact ⟨Finset.mem_univ _, fun h => h.elim hp hu⟩
        rw [buildFun_rem ends t S _ _ hr]
        rfl
  right_inv := by
    rintro ⟨dir, Q⟩
    apply Prod.ext
    · funext ⟨e, hS⟩
      simp only [extractDir]
      change decide (buildFun ends t S dir Q.1 (p0 v m t e) = u1 ends t e) = dir ⟨e, hS⟩
      rw [buildFun_p0_mem ends t S dir Q.1 e hS]
      cases hd : dir ⟨e, hS⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not]
        exact u0_ne_u1 ends hends t e
      · simp only [↓reduceIte, decide_eq_true_eq]
    · apply Subtype.ext
      ext ⟨x, hx⟩
      change (buildFun ends t S dir Q.1 x).val = (Q.1 ⟨x, hx⟩).1.val
      rw [buildFun_rem ends t S dir Q.1 hx]

private def equivInvolutiveCongr {α β : Type*} (e : α ≃ β) :
    {P : Equiv.Perm α // Function.Involutive P} ≃
      {Q : Equiv.Perm β // Function.Involutive Q} where
  toFun P := ⟨e.symm.trans (P.1.trans e), fun y => by
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [P.2, Equiv.apply_symm_apply]⟩
  invFun Q := ⟨e.trans (Q.1.trans e.symm), fun x => by
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [Q.2, Equiv.symm_apply_apply]⟩
  left_inv P := by
    apply Subtype.ext
    ext x
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  right_inv Q := by
    apply Subtype.ext
    ext y
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]

private lemma card_fiber {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2) (t : Nat) (S : Finset (Fin m)) :
    Nat.card {P : Equiv.Perm (Fin (v + 2 * m + t)) //
      Wins ends t P ∧ Active (v := v) t P = S} =
    if IsMatching ends S then
      2 ^ S.card * Nat.card {P : Equiv.Perm (Fin (v + t - 2 * S.card)) // Function.Involutive P}
    else 0 := by
  split_ifs with hM
  · have hcard : Fintype.card {x : Fin (v + 2 * m + t) // x ∈ remSet ends t S} =
        v + t - 2 * S.card := by
      rw [Fintype.card_coe]
      exact remSet_card ends hends t S hM
    let eRem := Fintype.equivFinOfCardEq hcard
    let eTotal := (fiberEquiv ends hends t S hM).trans
      (Equiv.prodCongr (Equiv.refl _) (equivInvolutiveCongr eRem))
    rw [Nat.card_congr eTotal, Nat.card_prod, Nat.card_eq_fintype_card (α := (S → Bool)),
      Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  · have hNo : ∀ P : {P : Equiv.Perm (Fin (v + 2 * m + t)) //
        Wins ends t P ∧ Active (v := v) t P = S}, False :=
      fun ⟨P, hW, hA⟩ => hM (hA ▸ matching_of_wins ends t P hW)
    let e0 : {P : Equiv.Perm (Fin (v + 2 * m + t)) //
        Wins ends t P ∧ Active (v := v) t P = S} ≃ Fin 0 :=
      { toFun := fun P => (hNo P).elim
        invFun := fun x => x.elim0
        left_inv := fun P => (hNo P).elim
        right_inv := fun x => x.elim0 }
    rw [Nat.card_congr e0, Nat.card_eq_fintype_card, Fintype.card_fin]

private lemma wins_pos {v m : Nat} (ends : Fin m → Fin v × Fin v)
    (hends : ∀ e, (ends e).1 ≠ (ends e).2) (t : Nat) :
    0 < Nat.card {P : Equiv.Perm (Fin (v + 2 * m + t)) // Wins ends t P} := by
  have hM0 : IsMatching ends ∅ := fun _ he => False.elim (Finset.notMem_empty _ he)
  let dir0 : (∅ : Finset (Fin m)) → Bool := fun e => False.elim (Finset.notMem_empty e.1 e.2)
  let Q0 : {Q : Equiv.Perm {x : Fin (v + 2 * m + t) // x ∈ remSet ends t ∅} //
      Function.Involutive Q} := ⟨Equiv.refl _, fun _ => rfl⟩
  have hNe : Nonempty {P : Equiv.Perm (Fin (v + 2 * m + t)) // Wins ends t P} :=
    ⟨⟨buildPerm ends hends t ∅ hM0 dir0 Q0, buildPerm_wins ends hends t ∅ hM0 dir0 Q0⟩⟩
  exact @Nat.card_pos _ hNe _

end PEqualNP.Outside.L_lib_913

theorem PEqualNP.Outside.L_lib_913 : ∀ (v m : Nat) (ends : Fin m → Fin v × Fin v), (∀ e, (ends e).1 ≠ (ends e).2) →
  let vertices := fun e : Fin m => ({(ends e).1,(ends e).2} : Finset (Fin v))
  let matching := fun S : Finset (Fin m) => ∀ e ∈ S, ∀ g ∈ S, e ≠ g → Disjoint (vertices e) (vertices g)
  let tests := Finset.univ.image (fun z : Fin m × Bool =>
    ({v+2*z.1.val,v+2*z.1.val+1,if z.2 then (ends z.1).2.val else (ends z.1).1.val} : Finset Nat))
  let I := fun k : Nat => Nat.card {P : Equiv.Perm (Fin k) // Function.Involutive P}
  tests.card = 2*m ∧ (∀ R ∈ tests, R.card = 3 ∧
    (tests.filter (fun T => T ≠ R ∧ (T ∩ R).card = 2)).card = 1) ∧
  ∀ t : Nat,
    let k := v+2*m+t
    let wins := fun P : Equiv.Perm (Fin k) => Function.Involutive P ∧
      ∀ R ∈ tests, ∃ u : Fin k, u.val ∈ R ∧ (P u).val ∈ R ∧ P u ≠ u
    let active := fun P : Equiv.Perm (Fin k) => Finset.univ.filter (fun e : Fin m =>
      ¬ ∃ u : Fin k, u.val = v+2*e.val ∧ (P u).val = v+2*e.val+1)
    (∀ S : Finset (Fin m), Nat.card {P : Equiv.Perm (Fin k) // wins P ∧ active P = S} =
      if matching S then 2^S.card * I (v+t-2*S.card) else 0) ∧
    0 < Nat.card {P : Equiv.Perm (Fin k) // wins P} ∧
    Nat.card {P : Equiv.Perm (Fin k) // wins P} =
      (Finset.univ.filter matching).sum (fun S => 2^S.card * I (v+t-2*S.card)) := by
  intro v m ends hends
  dsimp only
  refine ⟨PEqualNP.Outside.L_lib_913.tests_card ends hends, ?_, ?_⟩
  · intro R hR
    rw [Finset.mem_image] at hR
    rcases hR with ⟨z, _, rfl⟩
    exact ⟨PEqualNP.Outside.L_lib_913.testOf_card ends z,
      PEqualNP.Outside.L_lib_913.twin_filter_card ends hends z⟩
  · intro t
    have hfib : ∀ S : Finset (Fin m),
        Nat.card {P : Equiv.Perm (Fin (v + 2 * m + t)) //
          PEqualNP.Outside.L_lib_913.Wins ends t P ∧
          PEqualNP.Outside.L_lib_913.Active (v := v) t P = S} =
        if PEqualNP.Outside.L_lib_913.IsMatching ends S then
          2 ^ S.card * Nat.card {P : Equiv.Perm (Fin (v + t - 2 * S.card)) // Function.Involutive P}
        else 0 :=
      PEqualNP.Outside.L_lib_913.card_fiber ends hends t
    refine ⟨?_, PEqualNP.Outside.L_lib_913.wins_pos ends hends t, ?_⟩
    · intro S
      exact hfib S
    · let ePart : {P : Equiv.Perm (Fin (v + 2 * m + t)) //
          PEqualNP.Outside.L_lib_913.Wins ends t P} ≃
          Σ S : Finset (Fin m), {P : Equiv.Perm (Fin (v + 2 * m + t)) //
            PEqualNP.Outside.L_lib_913.Wins ends t P ∧
            PEqualNP.Outside.L_lib_913.Active (v := v) t P = S} :=
        { toFun := fun ⟨P, hW⟩ => ⟨PEqualNP.Outside.L_lib_913.Active (v := v) t P, ⟨P, hW, rfl⟩⟩
          invFun := fun ⟨_, ⟨P, hW, _⟩⟩ => ⟨P, hW⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun ⟨_, ⟨_, _, hA⟩⟩ => by subst hA; rfl }
      change Nat.card {P : Equiv.Perm (Fin (v + 2 * m + t)) //
          PEqualNP.Outside.L_lib_913.Wins ends t P} = _
      rw [Nat.card_congr ePart, Nat.card_sigma, Finset.sum_filter]
      exact Finset.sum_congr rfl (fun S _ => hfib S)
