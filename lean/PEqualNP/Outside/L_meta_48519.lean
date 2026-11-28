import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_meta_48519_aux

def ordPairs (q : Nat) : Finset (Fin q × Fin q) :=
  (Finset.univ : Finset (Fin q × Fin q)).filter (fun p => p.1 < p.2)

lemma card_ordPairs (q : Nat) : (ordPairs q).card = Nat.choose q 2 := by
  induction q with
  | zero =>
    simp [ordPairs]
  | succ q ih =>
    have hsplit : ordPairs (q + 1) =
        ((ordPairs q).image (fun p => (Fin.castSucc p.1, Fin.castSucc p.2))) ∪
        ((Finset.univ : Finset (Fin q)).image (fun a => (Fin.castSucc a, Fin.last q))) := by
      ext ⟨a, b⟩
      simp only [ordPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro hab
        by_cases hb : b = Fin.last q
        · right
          have ha : a.val < q := by
            have h1 : a.val < b.val := hab
            have h2 : b.val = q := by rw [hb]; rfl
            omega
          exact ⟨⟨a.val, ha⟩, Fin.ext rfl, hb.symm⟩
        · left
          have hb_lt : b.val < q := by
            have h1 : b.val < q + 1 := b.isLt
            have h2 : b.val ≠ q := fun h => hb (Fin.ext h)
            omega
          have ha_lt : a.val < q := by
            have h1 : a.val < b.val := hab
            omega
          refine ⟨(⟨a.val, ha_lt⟩, ⟨b.val, hb_lt⟩), ?_, Fin.ext rfl, Fin.ext rfl⟩
          exact hab
      · rintro (⟨⟨a', b'⟩, hab', rfl, rfl⟩ | ⟨a', rfl, rfl⟩)
        · exact hab'
        · exact a'.isLt
    have hdisj : Disjoint
        ((ordPairs q).image (fun p => (Fin.castSucc p.1, Fin.castSucc p.2)))
        ((Finset.univ : Finset (Fin q)).image (fun a => (Fin.castSucc a, Fin.last q))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_image] at hx1 hx2
      rcases hx1 with ⟨⟨a1, b1⟩, _, rfl⟩
      rcases hx2 with ⟨a2, _, h2⟩
      have hval : (Fin.castSucc b1).val = (Fin.last q).val := congrArg (fun p => p.2.val) h2.symm
      have h1 : b1.val < q := b1.isLt
      simp only [Fin.val_castSucc, Fin.val_last] at hval
      omega
    have hinj1 : Function.Injective (fun p : Fin q × Fin q => (Fin.castSucc p.1, Fin.castSucc p.2)) := by
      intro p1 p2 h
      have h1 : p1.1.val = p2.1.val := congrArg (fun p => p.1.val) h
      have h2 : p1.2.val = p2.2.val := congrArg (fun p => p.2.val) h
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    have hinj2 : Function.Injective (fun a : Fin q => (Fin.castSucc a, Fin.last q)) := by
      intro a1 a2 h
      have h1 : a1.val = a2.val := congrArg (fun p => p.1.val) h
      exact Fin.ext h1
    rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj1,
      Finset.card_image_of_injective _ hinj2, ih, Finset.card_univ, Fintype.card_fin]
    have hch : Nat.choose (q + 1) 2 = Nat.choose q 1 + Nat.choose q 2 := Nat.choose_succ_succ q 1
    rw [hch, Nat.choose_one_right]
    omega

lemma card_choicePairs (n k : Nat) :
    (ordPairs k ×ˢ ordPairs n).card = Nat.choose k 2 * Nat.choose n 2 := by
  rw [Finset.card_product, card_ordPairs, card_ordPairs]

noncomputable def choiceEquiv (n k : Nat) :
    Fin (Nat.choose k 2 * Nat.choose n 2) ≃ { p // p ∈ ordPairs k ×ˢ ordPairs n } :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact card_choicePairs n k)).symm

noncomputable def s1 (n k : Nat) (c : Fin (Nat.choose k 2 * Nat.choose n 2)) : Fin k :=
  (choiceEquiv n k c).1.1.1

noncomputable def s2 (n k : Nat) (c : Fin (Nat.choose k 2 * Nat.choose n 2)) : Fin k :=
  (choiceEquiv n k c).1.1.2

noncomputable def v1 (n k : Nat) (c : Fin (Nat.choose k 2 * Nat.choose n 2)) : Fin n :=
  (choiceEquiv n k c).1.2.1

noncomputable def v2 (n k : Nat) (c : Fin (Nat.choose k 2 * Nat.choose n 2)) : Fin n :=
  (choiceEquiv n k c).1.2.2

lemma s1_lt_s2 (n k : Nat) (c : Fin (Nat.choose k 2 * Nat.choose n 2)) : s1 n k c < s2 n k c := by
  have hm := (choiceEquiv n k c).2
  rw [Finset.mem_product] at hm
  exact (Finset.mem_filter.mp hm.1).2

lemma v1_lt_v2 (n k : Nat) (c : Fin (Nat.choose k 2 * Nat.choose n 2)) : v1 n k c < v2 n k c := by
  have hm := (choiceEquiv n k c).2
  rw [Finset.mem_product] at hm
  exact (Finset.mem_filter.mp hm.2).2

lemma choice_ext {n k : Nat} {c d : Fin (Nat.choose k 2 * Nat.choose n 2)}
    (hs1 : s1 n k c = s1 n k d) (hs2 : s2 n k c = s2 n k d)
    (hv1 : v1 n k c = v1 n k d) (hv2 : v2 n k c = v2 n k d) : c = d := by
  apply (choiceEquiv n k).injective
  apply Subtype.ext
  exact Prod.ext (Prod.ext hs1 hs2) (Prod.ext hv1 hv2)

noncomputable def mkChoice (n k : Nat) (a b : Fin k) (hab : a < b) (u v : Fin n) (huv : u < v) :
    Fin (Nat.choose k 2 * Nat.choose n 2) :=
  (choiceEquiv n k).symm ⟨((a, b), (u, v)), by
    rw [Finset.mem_product]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩⟩⟩

lemma s1_mkChoice (n k : Nat) (a b : Fin k) (hab : a < b) (u v : Fin n) (huv : u < v) :
    s1 n k (mkChoice n k a b hab u v huv) = a := by
  simp [s1, mkChoice]

lemma s2_mkChoice (n k : Nat) (a b : Fin k) (hab : a < b) (u v : Fin n) (huv : u < v) :
    s2 n k (mkChoice n k a b hab u v huv) = b := by
  simp [s2, mkChoice]

lemma v1_mkChoice (n k : Nat) (a b : Fin k) (hab : a < b) (u v : Fin n) (huv : u < v) :
    v1 n k (mkChoice n k a b hab u v huv) = u := by
  simp [v1, mkChoice]

lemma v2_mkChoice (n k : Nat) (a b : Fin k) (hab : a < b) (u v : Fin n) (huv : u < v) :
    v2 n k (mkChoice n k a b hab u v huv) = v := by
  simp [v2, mkChoice]

def blk {m : Nat} (i : Fin (3 * m * (m + 1))) : Fin m :=
  ⟨i.val / (3 * (m + 1)), by
    apply Nat.div_lt_of_lt_mul
    have hi : i.val < 3 * m * (m + 1) := i.isLt
    have hmul : 3 * m * (m + 1) = 3 * (m + 1) * m := by
      calc
        3 * m * (m + 1) = 3 * (m * (m + 1)) := Nat.mul_assoc 3 m (m + 1)
        _ = 3 * ((m + 1) * m) := by rw [Nat.mul_comm m (m + 1)]
        _ = 3 * (m + 1) * m := (Nat.mul_assoc 3 (m + 1) m).symm
    omega⟩

def pth {m : Nat} (i : Fin (3 * m * (m + 1))) : Fin (m + 1) :=
  ⟨(i.val / 3) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

def pos {m : Nat} (i : Fin (3 * m * (m + 1))) : Fin 3 :=
  ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩

def mkV {m : Nat} (c : Fin m) (p : Fin (m + 1)) (r : Fin 3) : Fin (3 * m * (m + 1)) :=
  ⟨c.val * (3 * (m + 1)) + p.val * 3 + r.val, by
    have hc : c.val + 1 ≤ m := c.isLt
    have hp : p.val + 1 ≤ m + 1 := p.isLt
    have hr : r.val < 3 := r.isLt
    have h1 : p.val * 3 + r.val < 3 * (m + 1) := by
      have hpm : p.val * 3 + 3 ≤ (m + 1) * 3 := by
        have := Nat.mul_le_mul_right 3 hp
        omega
      omega
    have h2 : (c.val + 1) * (3 * (m + 1)) ≤ m * (3 * (m + 1)) :=
      Nat.mul_le_mul_right (3 * (m + 1)) hc
    have h3 : m * (3 * (m + 1)) = 3 * m * (m + 1) := by
      calc
        m * (3 * (m + 1)) = m * 3 * (m + 1) := (Nat.mul_assoc m 3 (m + 1)).symm
        _ = 3 * m * (m + 1) := by rw [Nat.mul_comm m 3]
    have h4 : (c.val + 1) * (3 * (m + 1)) = c.val * (3 * (m + 1)) + 3 * (m + 1) :=
      Nat.succ_mul c.val (3 * (m + 1))
    omega⟩

lemma pos_mkV {m : Nat} (c : Fin m) (p : Fin (m + 1)) (r : Fin 3) :
    pos (mkV c p r) = r := by
  apply Fin.ext
  change (c.val * (3 * (m + 1)) + p.val * 3 + r.val) % 3 = r.val
  have heq : c.val * (3 * (m + 1)) + p.val * 3 + r.val =
      r.val + 3 * (c.val * (m + 1) + p.val) := by
    have h1 : c.val * (3 * (m + 1)) = 3 * (c.val * (m + 1)) := by
      calc
        c.val * (3 * (m + 1)) = c.val * 3 * (m + 1) := (Nat.mul_assoc c.val 3 (m + 1)).symm
        _ = 3 * c.val * (m + 1) := by rw [Nat.mul_comm c.val 3]
        _ = 3 * (c.val * (m + 1)) := Nat.mul_assoc 3 c.val (m + 1)
    have h2 : 3 * (c.val * (m + 1) + p.val) = 3 * (c.val * (m + 1)) + 3 * p.val :=
      Nat.mul_add 3 (c.val * (m + 1)) p.val
    omega
  rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]

lemma pth_mkV {m : Nat} (c : Fin m) (p : Fin (m + 1)) (r : Fin 3) :
    pth (mkV c p r) = p := by
  apply Fin.ext
  change ((c.val * (3 * (m + 1)) + p.val * 3 + r.val) / 3) % (m + 1) = p.val
  have heq : c.val * (3 * (m + 1)) + p.val * 3 + r.val =
      r.val + 3 * (c.val * (m + 1) + p.val) := by
    have h1 : c.val * (3 * (m + 1)) = 3 * (c.val * (m + 1)) := by
      calc
        c.val * (3 * (m + 1)) = c.val * 3 * (m + 1) := (Nat.mul_assoc c.val 3 (m + 1)).symm
        _ = 3 * c.val * (m + 1) := by rw [Nat.mul_comm c.val 3]
        _ = 3 * (c.val * (m + 1)) := Nat.mul_assoc 3 c.val (m + 1)
    have h2 : 3 * (c.val * (m + 1) + p.val) = 3 * (c.val * (m + 1)) + 3 * p.val :=
      Nat.mul_add 3 (c.val * (m + 1)) p.val
    omega
  rw [heq, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt r.isLt, Nat.zero_add]
  rw [Nat.add_comm, Nat.mul_comm c.val (m + 1), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.isLt]

lemma blk_mkV {m : Nat} (c : Fin m) (p : Fin (m + 1)) (r : Fin 3) :
    blk (mkV c p r) = c := by
  apply Fin.ext
  change (c.val * (3 * (m + 1)) + p.val * 3 + r.val) / (3 * (m + 1)) = c.val
  have hp : p.val + 1 ≤ m + 1 := p.isLt
  have hr : r.val < 3 := r.isLt
  have hrem : p.val * 3 + r.val < 3 * (m + 1) := by
    have := Nat.mul_le_mul_right 3 hp
    omega
  have heq : c.val * (3 * (m + 1)) + p.val * 3 + r.val =
      (p.val * 3 + r.val) + (3 * (m + 1)) * c.val := by
    rw [Nat.mul_comm c.val (3 * (m + 1))]
    omega
  rw [heq, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hrem, Nat.zero_add]

lemma mkV_eta {m : Nat} (i : Fin (3 * m * (m + 1))) : mkV (blk i) (pth i) (pos i) = i := by
  apply Fin.ext
  change (i.val / (3 * (m + 1))) * (3 * (m + 1)) + ((i.val / 3) % (m + 1)) * 3 + i.val % 3 = i.val
  have hdiv : i.val / (3 * (m + 1)) = (i.val / 3) / (m + 1) := by
    rw [Nat.div_div_eq_div_mul]
  rw [hdiv]
  have hq : ((i.val / 3) / (m + 1)) * (m + 1) + (i.val / 3) % (m + 1) = i.val / 3 := by
    have := Nat.div_add_mod (i.val / 3) (m + 1)
    rw [Nat.mul_comm] at this
    exact this
  have hq3 : ((i.val / 3) / (m + 1)) * (3 * (m + 1)) + ((i.val / 3) % (m + 1)) * 3 =
      (i.val / 3) * 3 := by
    have hmul := congrArg (fun t => t * 3) hq
    simp only [Nat.add_mul] at hmul
    have hassoc : ((i.val / 3) / (m + 1)) * (m + 1) * 3 =
        ((i.val / 3) / (m + 1)) * (3 * (m + 1)) := by
      rw [Nat.mul_assoc, Nat.mul_comm (m + 1) 3]
    rw [hassoc] at hmul
    exact hmul
  have hi : (i.val / 3) * 3 + i.val % 3 = i.val := by
    have := Nat.div_add_mod i.val 3
    rw [Nat.mul_comm] at this
    exact this
  omega

noncomputable def consChoice (n k : Nat) (c d : Fin (Nat.choose k 2 * Nat.choose n 2)) : Bool :=
  decide ((s1 n k c = s1 n k d ↔ v1 n k c = v1 n k d) ∧
          (s1 n k c = s2 n k d ↔ v1 n k c = v2 n k d) ∧
          (s2 n k c = s1 n k d ↔ v2 n k c = v1 n k d) ∧
          (s2 n k c = s2 n k d ↔ v2 n k c = v2 n k d))

lemma consChoice_refl (n k : Nat) (c : Fin (Nat.choose k 2 * Nat.choose n 2)) :
    consChoice n k c c = true := by
  have hs := s1_lt_s2 n k c
  have hv := v1_lt_v2 n k c
  unfold consChoice
  rw [decide_eq_true_eq]
  refine ⟨⟨fun _ => rfl, fun _ => rfl⟩, ?_, ?_, ⟨fun _ => rfl, fun _ => rfl⟩⟩
  · exact ⟨fun h => absurd h (ne_of_lt hs), fun h => absurd h (ne_of_lt hv)⟩
  · exact ⟨fun h => absurd h (ne_of_gt hs), fun h => absurd h (ne_of_gt hv)⟩

lemma consChoice_symm (n k : Nat) (c d : Fin (Nat.choose k 2 * Nat.choose n 2)) :
    consChoice n k c d = consChoice n k d c := by
  simp only [consChoice, decide_eq_decide]
  constructor
  · rintro ⟨h11, h12, h21, h22⟩
    exact ⟨⟨fun h => (h11.mp h.symm).symm, fun h => (h11.mpr h.symm).symm⟩,
           ⟨fun h => (h21.mp h.symm).symm, fun h => (h21.mpr h.symm).symm⟩,
           ⟨fun h => (h12.mp h.symm).symm, fun h => (h12.mpr h.symm).symm⟩,
           ⟨fun h => (h22.mp h.symm).symm, fun h => (h22.mpr h.symm).symm⟩⟩
  · rintro ⟨h11, h12, h21, h22⟩
    exact ⟨⟨fun h => (h11.mp h.symm).symm, fun h => (h11.mpr h.symm).symm⟩,
           ⟨fun h => (h21.mp h.symm).symm, fun h => (h21.mpr h.symm).symm⟩,
           ⟨fun h => (h12.mp h.symm).symm, fun h => (h12.mpr h.symm).symm⟩,
           ⟨fun h => (h22.mp h.symm).symm, fun h => (h22.mpr h.symm).symm⟩⟩

lemma consChoice_slot_inj {n k : Nat} {c d : Fin (Nat.choose k 2 * Nat.choose n 2)}
    (hcons : consChoice n k c d = true)
    (hs1 : s1 n k c = s1 n k d) (hs2 : s2 n k c = s2 n k d) : c = d := by
  simp only [consChoice, decide_eq_true_eq] at hcons
  exact choice_ext hs1 hs2 (hcons.1.mp hs1) (hcons.2.2.2.mp hs2)

lemma card_le_of_pairwise_consChoice {n k : Nat}
    (C : Finset (Fin (Nat.choose k 2 * Nat.choose n 2)))
    (hcons : ∀ c ∈ C, ∀ d ∈ C, consChoice n k c d = true) :
    C.card ≤ Nat.choose k 2 := by
  calc
    C.card ≤ (ordPairs k).card := by
      refine Finset.card_le_card_of_injOn (fun c => (s1 n k c, s2 n k c)) ?_ ?_
      · intro c _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, s1_lt_s2 n k c⟩
      · intro c hc d hd hEq
        simp only [Prod.mk.injEq] at hEq
        exact consChoice_slot_inj (hcons c hc d hd) hEq.1 hEq.2
    _ = Nat.choose k 2 := card_ordPairs k

lemma clique_iff_consSet {n k : Nat} (hk : 2 ≤ k) (E : SimpleGraph (Fin n)) :
    (∃ h : Fin k → Fin n, Function.Injective h ∧ ∀ i j, i ≠ j → E.Adj (h i) (h j)) ↔
    ∃ C : Finset (Fin (Nat.choose k 2 * Nat.choose n 2)),
      C.card = Nat.choose k 2 ∧
      (∀ c ∈ C, E.Adj (v1 n k c) (v2 n k c)) ∧
      (∀ c ∈ C, ∀ d ∈ C, consChoice n k c d = true) := by
  constructor
  · rintro ⟨h, hInj, hAdj⟩
    let S : Finset (Fin n) := (Finset.univ : Finset (Fin k)).image h
    have hS : S.card = k := by
      rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin]
    let e : Fin k ↪o Fin n := S.orderEmbOfFin hS
    let mapFn : { p // p ∈ ordPairs k } → Fin (Nat.choose k 2 * Nat.choose n 2) :=
      fun p => mkChoice n k p.1.1 p.1.2 (Finset.mem_filter.mp p.2).2
        (e p.1.1) (e p.1.2) (e.lt_iff_lt.mpr (Finset.mem_filter.mp p.2).2)
    let C := (ordPairs k).attach.image mapFn
    refine ⟨C, ?_, ?_, ?_⟩
    · have hmapInj : Function.Injective mapFn := by
        intro p q hpq
        have h1 : p.1.1 = q.1.1 := by
          have := congrArg (s1 n k) hpq
          simpa [mapFn, s1_mkChoice] using this
        have h2 : p.1.2 = q.1.2 := by
          have := congrArg (s2 n k) hpq
          simpa [mapFn, s2_mkChoice] using this
        exact Subtype.ext (Prod.ext h1 h2)
      rw [Finset.card_image_of_injective _ hmapInj, Finset.card_attach, card_ordPairs]
    · intro c hc
      rcases Finset.mem_image.mp hc with ⟨p, _, rfl⟩
      rw [v1_mkChoice, v2_mkChoice]
      have hm1 : e p.1.1 ∈ S := Finset.orderEmbOfFin_mem S hS p.1.1
      have hm2 : e p.1.2 ∈ S := Finset.orderEmbOfFin_mem S hS p.1.2
      rcases Finset.mem_image.mp hm1 with ⟨i, _, hi⟩
      rcases Finset.mem_image.mp hm2 with ⟨j, _, hj⟩
      rw [← hi, ← hj]
      apply hAdj
      intro hij
      have hlt : e p.1.1 < e p.1.2 := e.lt_iff_lt.mpr (Finset.mem_filter.mp p.2).2
      rw [← hi, ← hj, hij] at hlt
      exact lt_irrefl _ hlt
    · intro c hc d hd
      rcases Finset.mem_image.mp hc with ⟨p, _, rfl⟩
      rcases Finset.mem_image.mp hd with ⟨q, _, rfl⟩
      simp only [consChoice, mapFn, s1_mkChoice, s2_mkChoice, v1_mkChoice, v2_mkChoice,
        decide_eq_true_eq]
      exact ⟨e.injective.eq_iff.symm, e.injective.eq_iff.symm,
        e.injective.eq_iff.symm, e.injective.eq_iff.symm⟩
  · rintro ⟨C, hcard, hE, hcons⟩
    let phi : Fin (Nat.choose k 2 * Nat.choose n 2) → Fin k × Fin k := fun c => (s1 n k c, s2 n k c)
    have hsub : C.image phi ⊆ ordPairs k := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨c, _, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, s1_lt_s2 n k c⟩
    have hphiInj : Set.InjOn phi C := by
      intro c hc d hd hEq
      simp only [phi, Prod.mk.injEq] at hEq
      exact consChoice_slot_inj (hcons c hc d hd) hEq.1 hEq.2
    have himg : C.image phi = ordPairs k := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [Finset.card_image_of_injOn hphiInj, hcard, card_ordPairs]
    have hex : ∀ a b : Fin k, a < b → ∃ c ∈ C, s1 n k c = a ∧ s2 n k c = b := by
      intro a b hab
      have hmem : (a, b) ∈ C.image phi := by
        rw [himg]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
      rcases Finset.mem_image.mp hmem with ⟨c, hc, hEq⟩
      simp only [phi, Prod.mk.injEq] at hEq
      exact ⟨c, hc, hEq.1, hEq.2⟩
    let z0 : Fin k := ⟨0, by omega⟩
    let z1 : Fin k := ⟨1, by omega⟩
    have hz01 : z0 < z1 := by
      change (0 : Nat) < 1
      omega
    let c01 := Classical.choose (hex z0 z1 hz01)
    have hc01 : c01 ∈ C ∧ s1 n k c01 = z0 ∧ s2 n k c01 = z1 :=
      Classical.choose_spec (hex z0 z1 hz01)
    let h : Fin k → Fin n := fun a =>
      if ha : a = z0 then v1 n k c01
      else
        have hlt : z0 < a := by
          change (0 : Nat) < a.val
          have hne : a.val ≠ 0 := fun h0 => ha (Fin.ext h0)
          omega
        v2 n k (Classical.choose (hex z0 a hlt))
    have hv1_eq : ∀ c ∈ C, v1 n k c = h (s1 n k c) := by
      intro c hc
      by_cases h0 : s1 n k c = z0
      · simp only [h, h0, ↓reduceDIte]
        have hcc := hcons c hc c01 hc01.1
        simp only [consChoice, decide_eq_true_eq] at hcc
        exact hcc.1.mp (h0.trans hc01.2.1.symm)
      · simp only [h, h0, ↓reduceDIte]
        have hlt : z0 < s1 n k c := by
          change (0 : Nat) < (s1 n k c).val
          have hne : (s1 n k c).val ≠ 0 := fun hzero => h0 (Fin.ext hzero)
          omega
        have hspec := Classical.choose_spec (hex z0 (s1 n k c) hlt)
        have hcc := hcons c hc _ hspec.1
        simp only [consChoice, decide_eq_true_eq] at hcc
        exact hcc.2.1.mp hspec.2.2.symm
    have hv2_eq : ∀ c ∈ C, v2 n k c = h (s2 n k c) := by
      intro c hc
      have h0 : s2 n k c ≠ z0 := by
        intro heq
        have hlt : (s1 n k c).val < (s2 n k c).val := s1_lt_s2 n k c
        have hz : (s2 n k c).val = 0 := congrArg Fin.val heq
        omega
      simp only [h, h0, ↓reduceDIte]
      have hlt : z0 < s2 n k c := by
        change (0 : Nat) < (s2 n k c).val
        have hne : (s2 n k c).val ≠ 0 := fun hzero => h0 (Fin.ext hzero)
        omega
      have hspec := Classical.choose_spec (hex z0 (s2 n k c) hlt)
      have hcc := hcons c hc _ hspec.1
      simp only [consChoice, decide_eq_true_eq] at hcc
      exact hcc.2.2.2.mp hspec.2.2.symm
    have hlt_map : ∀ a b : Fin k, a < b → h a < h b ∧ E.Adj (h a) (h b) := by
      intro a b hab
      rcases hex a b hab with ⟨c, hc, hs1, hs2⟩
      have ha : v1 n k c = h a := by rw [← hs1]; exact hv1_eq c hc
      have hb : v2 n k c = h b := by rw [← hs2]; exact hv2_eq c hc
      rw [← ha, ← hb]
      exact ⟨v1_lt_v2 n k c, hE c hc⟩
    refine ⟨h, ?_, ?_⟩
    · intro a b hab
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · exact absurd hab (ne_of_lt (hlt_map a b hlt).1)
      · rfl
      · exact absurd hab (ne_of_gt (hlt_map b a hgt).1)
    · intro a b hab
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · exact (hlt_map a b hlt).2
      · exact absurd rfl hab
      · exact (E.adj_comm (h b) (h a)).mp (hlt_map b a hgt).2

noncomputable def graphG (n k : Nat) :
    Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1)) →
    Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1)) → Bool :=
  fun i j =>
    if blk i = blk j then
      decide (pth i = pth j) &&
        decide ((pos i).val + 1 = (pos j).val ∨ (pos j).val + 1 = (pos i).val)
    else
      !(consChoice n k (blk i) (blk j))

noncomputable def wireOf (n k : Nat)
    (i : Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1))) :
    Fin n × Fin n :=
  (v1 n k (blk i), v2 n k (blk i))

lemma graphG_irrefl (n k : Nat)
    (i : Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1))) :
    graphG n k i i = false := by
  simp [graphG]

lemma graphG_symm (n k : Nat)
    (i j : Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1))) :
    graphG n k i j = graphG n k j i := by
  unfold graphG
  by_cases h : blk i = blk j
  · simp only [h, ↓reduceIte]
    congr 1
    · exact decide_eq_decide.mpr eq_comm
    · exact decide_eq_decide.mpr or_comm
  · have h' : blk j ≠ blk i := Ne.symm h
    simp only [h, h', ↓reduceIte]
    rw [consChoice_symm]

lemma wireOf_lt (n k : Nat)
    (i : Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1))) :
    (wireOf n k i).1 < (wireOf n k i).2 :=
  v1_lt_v2 n k (blk i)

def pathSet {m : Nat} (c : Fin m) (p : Fin (m + 1)) : Finset (Fin (3 * m * (m + 1))) :=
  {mkV c p ⟨0, by omega⟩, mkV c p ⟨1, by omega⟩, mkV c p ⟨2, by omega⟩}

lemma mem_pathSet_iff {m : Nat} (c : Fin m) (p : Fin (m + 1)) (i : Fin (3 * m * (m + 1))) :
    i ∈ pathSet c p ↔ blk i = c ∧ pth i = p := by
  constructor
  · intro hi
    simp only [pathSet, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨blk_mkV _ _ _, pth_mkV _ _ _⟩
    · exact ⟨blk_mkV _ _ _, pth_mkV _ _ _⟩
    · exact ⟨blk_mkV _ _ _, pth_mkV _ _ _⟩
  · rintro ⟨hc, hp⟩
    have heta : i = mkV c p (pos i) := by
      rw [← hc, ← hp, mkV_eta]
    rw [heta]
    have hlt : (pos i).val < 3 := (pos i).isLt
    have hcases : pos i = ⟨0, by omega⟩ ∨ pos i = ⟨1, by omega⟩ ∨ pos i = ⟨2, by omega⟩ := by
      rcases pos i with ⟨v, hv⟩
      have : v = 0 ∨ v = 1 ∨ v = 2 := by omega
      rcases this with rfl | rfl | rfl
      · left; rfl
      · right; left; rfl
      · right; right; rfl
    simp only [pathSet, Finset.mem_insert, Finset.mem_singleton]
    rcases hcases with h0 | h1 | h2
    · left; rw [h0]
    · right; left; rw [h1]
    · right; right; rw [h2]

noncomputable def alphaOf {N : Nat} (g : Fin N → Fin N → Bool) (y : Finset (Fin N)) : Nat :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (y.powerset.filter (fun z => ∀ i ∈ z, ∀ j ∈ z, g i j = false)).sup Finset.card

lemma le_alphaOf {N : Nat} (g : Fin N → Fin N → Bool) {z y : Finset (Fin N)}
    (hzy : z ⊆ y) (hind : ∀ i ∈ z, ∀ j ∈ z, g i j = false) :
    z.card ≤ alphaOf g y := by
  let _ : ∀ p : Prop, Decidable p := Classical.propDecidable
  change z.card ≤ (y.powerset.filter (fun z => ∀ i ∈ z, ∀ j ∈ z, g i j = false)).sup Finset.card
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hzy, hind⟩)

lemma alphaOf_le {N : Nat} (g : Fin N → Fin N → Bool) {y : Finset (Fin N)} {b : Nat}
    (h : ∀ z ⊆ y, (∀ i ∈ z, ∀ j ∈ z, g i j = false) → z.card ≤ b) :
    alphaOf g y ≤ b := by
  let _ : ∀ p : Prop, Decidable p := Classical.propDecidable
  change (y.powerset.filter (fun z => ∀ i ∈ z, ∀ j ∈ z, g i j = false)).sup Finset.card ≤ b
  rw [Finset.sup_le_iff]
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzp, hind⟩
  exact h z (Finset.mem_powerset.mp hzp) hind

lemma exists_indep_eq_alphaOf {N : Nat} (g : Fin N → Fin N → Bool) (y : Finset (Fin N)) :
    ∃ z ⊆ y, (∀ i ∈ z, ∀ j ∈ z, g i j = false) ∧ z.card = alphaOf g y := by
  let _ : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := y.powerset.filter (fun z => ∀ i ∈ z, ∀ j ∈ z, g i j = false)
  have hne : F.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset y), ?_⟩⟩
    intro i hi
    exact absurd hi (Finset.notMem_empty i)
  rcases Finset.exists_mem_eq_sup F hne Finset.card with ⟨z, hz, hsup⟩
  rcases Finset.mem_filter.mp hz with ⟨hzp, hind⟩
  exact ⟨z, Finset.mem_powerset.mp hzp, hind, hsup.symm⟩

lemma alphaOf_mono {N : Nat} (g : Fin N → Fin N → Bool) {u v : Finset (Fin N)} (huv : u ⊆ v) :
    alphaOf g u ≤ alphaOf g v := by
  apply alphaOf_le
  intro z hzu hind
  exact le_alphaOf g (hzu.trans huv) hind

lemma alphaOf_empty {N : Nat} (g : Fin N → Fin N → Bool) : alphaOf g ∅ = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply alphaOf_le
  intro z hz _
  rw [Finset.subset_empty.mp hz]
  simp

lemma alphaOf_disjoint_union {N : Nat} {g : Fin N → Fin N → Bool}
    (hsym : ∀ i j, g i j = g j i) {A B : Finset (Fin N)}
    (hdisj : Disjoint A B) (hno : ∀ i ∈ A, ∀ j ∈ B, g i j = false) :
    alphaOf g (A ∪ B) = alphaOf g A + alphaOf g B := by
  apply le_antisymm
  · apply alphaOf_le
    intro z hz hind
    have hsplit : z = (z ∩ A) ∪ (z ∩ B) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        rcases Finset.mem_union.mp (hz hx) with hxA | hxB
        · exact Or.inl ⟨hx, hxA⟩
        · exact Or.inr ⟨hx, hxB⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have hdz : Disjoint (z ∩ A) (z ∩ B) :=
      Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisj
    have hA : (z ∩ A).card ≤ alphaOf g A := by
      apply le_alphaOf g Finset.inter_subset_right
      intro i hi j hj
      exact hind i (Finset.mem_inter.mp hi).1 j (Finset.mem_inter.mp hj).1
    have hB : (z ∩ B).card ≤ alphaOf g B := by
      apply le_alphaOf g Finset.inter_subset_right
      intro i hi j hj
      exact hind i (Finset.mem_inter.mp hi).1 j (Finset.mem_inter.mp hj).1
    rw [hsplit, Finset.card_union_of_disjoint hdz]
    omega
  · rcases exists_indep_eq_alphaOf g A with ⟨zA, hzA, hindA, hcA⟩
    rcases exists_indep_eq_alphaOf g B with ⟨zB, hzB, hindB, hcB⟩
    have hdz : Disjoint zA zB := Disjoint.mono hzA hzB hdisj
    have hsub : zA ∪ zB ⊆ A ∪ B := Finset.union_subset_union hzA hzB
    have hind : ∀ i ∈ zA ∪ zB, ∀ j ∈ zA ∪ zB, g i j = false := by
      intro i hi j hj
      rcases Finset.mem_union.mp hi with hiA | hiB <;>
        rcases Finset.mem_union.mp hj with hjA | hjB
      · exact hindA i hiA j hjA
      · exact hno i (hzA hiA) j (hzB hjB)
      · rw [hsym]; exact hno j (hzA hjA) i (hzB hiB)
      · exact hindB i hiB j hjB
    have hle := le_alphaOf g hsub hind
    rw [Finset.card_union_of_disjoint hdz, hcA, hcB] at hle
    exact hle

lemma alphaOf_biUnion_eq_sum {N : Nat} {α : Type*} [DecidableEq α]
    {g : Fin N → Fin N → Bool} (hsym : ∀ i j, g i j = g j i)
    (S : Finset α) (F : α → Finset (Fin N))
    (hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (F a) (F b))
    (hno : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ i ∈ F a, ∀ j ∈ F b, g i j = false) :
    alphaOf g (S.biUnion F) = ∑ a ∈ S, alphaOf g (F a) := by
  induction S using Finset.induction with
  | empty =>
    simp [alphaOf_empty]
  | @insert a S ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hdisj' : Disjoint (F a) (S.biUnion F) := by
      rw [Finset.disjoint_biUnion_right]
      intro b hb
      exact hdisj a (Finset.mem_insert_self a S) b (Finset.mem_insert_of_mem hb)
        (fun hEq => ha (hEq ▸ hb))
    have hno' : ∀ i ∈ F a, ∀ j ∈ S.biUnion F, g i j = false := by
      intro i hi j hj
      rcases Finset.mem_biUnion.mp hj with ⟨b, hb, hjb⟩
      exact hno a (Finset.mem_insert_self a S) b (Finset.mem_insert_of_mem hb)
        (fun hEq => ha (hEq ▸ hb)) i hi j hjb
    rw [alphaOf_disjoint_union hsym hdisj' hno']
    congr 1
    apply ih
    · intro x hx y hy hne
      exact hdisj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hne
    · intro x hx y hy hne
      exact hno x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hne

lemma mkV_ne_of_pos_ne {m : Nat} (c : Fin m) (p : Fin (m + 1)) {r1 r2 : Fin 3} (h : r1 ≠ r2) :
    mkV c p r1 ≠ mkV c p r2 := by
  intro heq
  apply h
  have := congrArg pos heq
  simpa [pos_mkV] using this

lemma graphG_path_01 (n k : Nat)
    (c : Fin (Nat.choose k 2 * Nat.choose n 2))
    (p : Fin (Nat.choose k 2 * Nat.choose n 2 + 1)) :
    graphG n k (mkV c p ⟨0, by omega⟩) (mkV c p ⟨1, by omega⟩) = true := by
  simp [graphG, blk_mkV, pth_mkV, pos_mkV]

lemma graphG_path_12 (n k : Nat)
    (c : Fin (Nat.choose k 2 * Nat.choose n 2))
    (p : Fin (Nat.choose k 2 * Nat.choose n 2 + 1)) :
    graphG n k (mkV c p ⟨1, by omega⟩) (mkV c p ⟨2, by omega⟩) = true := by
  simp [graphG, blk_mkV, pth_mkV, pos_mkV]

lemma graphG_path_02 (n k : Nat)
    (c : Fin (Nat.choose k 2 * Nat.choose n 2))
    (p : Fin (Nat.choose k 2 * Nat.choose n 2 + 1)) :
    graphG n k (mkV c p ⟨0, by omega⟩) (mkV c p ⟨2, by omega⟩) = false := by
  simp [graphG, blk_mkV, pth_mkV, pos_mkV]

lemma alphaOf_pair_edge {N : Nat} {g : Fin N → Fin N → Bool}
    (hirr : ∀ i, g i i = false) {u v : Fin N} (hedge : g u v = true) :
    alphaOf g ({u, v} : Finset (Fin N)) = 1 := by
  apply le_antisymm
  · apply alphaOf_le
    intro z hz hind
    by_cases hu : u ∈ z
    · have hv : v ∉ z := fun hv => by
        have hfalse := hind u hu v hv
        rw [hedge] at hfalse
        cases hfalse
      have hsub : z ⊆ {u} := by
        intro w hw
        rcases Finset.mem_insert.mp (hz hw) with rfl | hvw
        · exact Finset.mem_singleton_self _
        · rw [Finset.mem_singleton.mp hvw] at hw
          exact absurd hw hv
      exact (Finset.card_le_card hsub).trans (by simp)
    · have hsub : z ⊆ {v} := by
        intro w hw
        rcases Finset.mem_insert.mp (hz hw) with rfl | hvw
        · exact absurd hw hu
        · exact hvw
      exact (Finset.card_le_card hsub).trans (by simp)
  · have hle : ({u} : Finset (Fin N)).card ≤ alphaOf g {u, v} := by
      apply le_alphaOf g
      · intro w hw
        rw [Finset.mem_singleton.mp hw]
        exact Finset.mem_insert_self _ _
      · intro i hi j hj
        rw [Finset.mem_singleton.mp hi, Finset.mem_singleton.mp hj]
        exact hirr u
    simpa using hle

lemma alphaOf_p3 (n k : Nat)
    (c : Fin (Nat.choose k 2 * Nat.choose n 2))
    (p : Fin (Nat.choose k 2 * Nat.choose n 2 + 1)) :
    alphaOf (graphG n k) (pathSet c p) = 2 := by
  let v0 := mkV c p ⟨0, by omega⟩
  let v1 := mkV c p ⟨1, by omega⟩
  let v2 := mkV c p ⟨2, by omega⟩
  have h01 : graphG n k v0 v1 = true := graphG_path_01 n k c p
  have h02 : graphG n k v0 v2 = false := graphG_path_02 n k c p
  have h20 : graphG n k v2 v0 = false := by rw [graphG_symm]; exact h02
  have hne02 : v0 ≠ v2 := mkV_ne_of_pos_ne c p (by decide)
  apply le_antisymm
  · apply alphaOf_le
    intro z hz hind
    by_cases hv0 : v0 ∈ z
    · have hv1 : v1 ∉ z := fun hv1 => by
        have hfalse := hind v0 hv0 v1 hv1
        rw [h01] at hfalse
        cases hfalse
      have hsub : z ⊆ {v0, v2} := by
        intro w hw
        have hmem : w = v0 ∨ w = v1 ∨ w = v2 := by
          simpa [pathSet, v0, v1, v2] using hz hw
        rcases hmem with rfl | rfl | rfl
        · exact Finset.mem_insert_self _ _
        · exact absurd hw hv1
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    · have hsub : z ⊆ {v1, v2} := by
        intro w hw
        have hmem : w = v0 ∨ w = v1 ∨ w = v2 := by
          simpa [pathSet, v0, v1, v2] using hz hw
        rcases hmem with rfl | rfl | rfl
        · exact absurd hw hv0
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  · have hle : ({v0, v2} : Finset _).card ≤ alphaOf (graphG n k) (pathSet c p) := by
      apply le_alphaOf (graphG n k)
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        simp only [pathSet, Finset.mem_insert, Finset.mem_singleton]
        rcases hw with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr rfl)
      · intro i hi j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · exact graphG_irrefl n k v0
        · exact h02
        · exact h20
        · exact graphG_irrefl n k v2
    rw [Finset.card_pair hne02] at hle
    exact hle

lemma card_le_alphaOf_add_one_of_subset_pathSet (n k : Nat)
    (c : Fin (Nat.choose k 2 * Nat.choose n 2))
    (p : Fin (Nat.choose k 2 * Nat.choose n 2 + 1))
    {w : Finset (Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1)))}
    (hw : w ⊆ pathSet c p) :
    w.card ≤ alphaOf (graphG n k) w + 1 := by
  let v0 := mkV c p ⟨0, by omega⟩
  let v1 := mkV c p ⟨1, by omega⟩
  let v2 := mkV c p ⟨2, by omega⟩
  have h02 : graphG n k v0 v2 = false := graphG_path_02 n k c p
  have h20 : graphG n k v2 v0 = false := by rw [graphG_symm]; exact h02
  let z := w.erase v1
  have hzsub : z ⊆ w := Finset.erase_subset v1 w
  have hind : ∀ i ∈ z, ∀ j ∈ z, graphG n k i j = false := by
    intro i hi j hj
    have hiw : i ∈ w := Finset.mem_of_mem_erase hi
    have hjw : j ∈ w := Finset.mem_of_mem_erase hj
    have hi_ne : i ≠ v1 := Finset.ne_of_mem_erase hi
    have hj_ne : j ≠ v1 := Finset.ne_of_mem_erase hj
    have hi_cases : i = v0 ∨ i = v2 := by
      have hmem : i = v0 ∨ i = v1 ∨ i = v2 := by simpa [pathSet, v0, v1, v2] using hw hiw
      rcases hmem with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd rfl hi_ne
      · exact Or.inr rfl
    have hj_cases : j = v0 ∨ j = v2 := by
      have hmem : j = v0 ∨ j = v1 ∨ j = v2 := by simpa [pathSet, v0, v1, v2] using hw hjw
      rcases hmem with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd rfl hj_ne
      · exact Or.inr rfl
    rcases hi_cases with rfl | rfl <;> rcases hj_cases with rfl | rfl
    · exact graphG_irrefl n k v0
    · exact h02
    · exact h20
    · exact graphG_irrefl n k v2
  have hle : z.card ≤ alphaOf (graphG n k) w := le_alphaOf (graphG n k) hzsub hind
  by_cases hv1 : v1 ∈ w
  · have hcard : z.card + 1 = w.card := Finset.card_erase_add_one hv1
    omega
  · have hcard : z = w := Finset.erase_eq_of_notMem hv1
    rw [hcard] at hle
    omega

def packOf {N : Nat} (x : Finset (Fin N)) (f : Finset (Fin N) → Fin N → Bool) :
    Nat → Finset (Fin N) → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin N) → Prop) (fun _ => True)
    (fun _ prev y => ∃ (u v : Finset (Fin N)) (j : Fin N), j ∈ x ∧
      prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false)

lemma unpack_packOf {N : Nat} {x : Finset (Fin N)} {f : Finset (Fin N) → Fin N → Bool} :
    ∀ {l : Nat} {y : Finset (Fin N)}, packOf x f l y →
      ∃ (u v : Fin l → Finset (Fin N)) (jw : Fin l → Fin N),
        (∀ t, jw t ∈ x ∧ u t ⊆ v t ∧ v t ⊆ y ∧ f (u t) (jw t) = true ∧ f (v t) (jw t) = false) ∧
        (∀ t1 t2 : Fin l, t1 < t2 → v t1 ⊆ u t2) := by
  intro l
  induction l with
  | zero =>
    intro y _
    exact ⟨Fin.elim0, Fin.elim0, Fin.elim0, fun t => Fin.elim0 t, fun t => Fin.elim0 t⟩
  | succ l ih =>
    intro y hp
    rcases hp with ⟨u0, v0, j0, hj0, hprev, hu0v0, hv0y, hfu0, hfv0⟩
    rcases ih hprev with ⟨u', v', jw', hstep, hchain⟩
    let u : Fin (l + 1) → Finset (Fin N) := fun t => if h : t.val < l then u' ⟨t.val, h⟩ else u0
    let v : Fin (l + 1) → Finset (Fin N) := fun t => if h : t.val < l then v' ⟨t.val, h⟩ else v0
    let jw : Fin (l + 1) → Fin N := fun t => if h : t.val < l then jw' ⟨t.val, h⟩ else j0
    refine ⟨u, v, jw, ?_, ?_⟩
    · intro t
      by_cases ht : t.val < l
      · simp only [u, v, jw, ht, ↓reduceDIte]
        rcases hstep ⟨t.val, ht⟩ with ⟨hjx, huv, hvu0, hfu, hfv⟩
        exact ⟨hjx, huv, hvu0.trans (hu0v0.trans hv0y), hfu, hfv⟩
      · simp only [u, v, jw, ht, ↓reduceDIte]
        exact ⟨hj0, hu0v0, hv0y, hfu0, hfv0⟩
    · intro t1 t2 hlt
      have ht1 : t1.val < l := by
        have h1 : t1.val < t2.val := hlt
        have h2 : t2.val < l + 1 := t2.isLt
        omega
      by_cases ht2 : t2.val < l
      · simp only [u, v, ht1, ht2, ↓reduceDIte]
        exact hchain ⟨t1.val, ht1⟩ ⟨t2.val, ht2⟩ hlt
      · simp only [u, v, ht1, ht2, ↓reduceDIte]
        exact (hstep ⟨t1.val, ht1⟩).2.2.1

lemma monotone_chain_strict_card {N l : Nat} {α : Type*} [DecidableEq α]
    {u v : Fin l → Finset (Fin N)} {y : Finset (Fin N)}
    (hvy : ∀ t, v t ⊆ y)
    (hchain : ∀ t1 t2 : Fin l, t1 < t2 → v t1 ⊆ u t2)
    (F : Finset (Fin N) → Finset α)
    (hFmono : ∀ a b, a ⊆ b → F a ⊆ F b)
    (T : Finset (Fin l))
    (hstrict : ∀ t ∈ T, ∃ a, a ∈ F (v t) ∧ a ∉ F (u t)) :
    T.card ≤ (F y).card := by
  by_cases hT : T.Nonempty
  · rcases hT with ⟨t0, ht0⟩
    let a0 : α := Classical.choose (hstrict t0 ht0)
    let w : Fin l → α := fun t => if h : t ∈ T then Classical.choose (hstrict t h) else a0
    refine Finset.card_le_card_of_injOn w ?_ ?_
    · intro t ht
      simp only [Finset.mem_coe] at ht ⊢
      simp only [w, ht, ↓reduceDIte]
      exact hFmono (v t) y (hvy t) (Classical.choose_spec (hstrict t ht)).1
    · intro t1 ht1 t2 ht2 hEq
      simp only [Finset.mem_coe] at ht1 ht2
      have hw1 : w t1 ∈ F (v t1) ∧ w t1 ∉ F (u t1) := by
        simpa [w, ht1] using Classical.choose_spec (hstrict t1 ht1)
      have hw2 : w t2 ∈ F (v t2) ∧ w t2 ∉ F (u t2) := by
        simpa [w, ht2] using Classical.choose_spec (hstrict t2 ht2)
      rcases lt_trichotomy t1 t2 with hlt | rfl | hgt
      · have hmem : w t1 ∈ F (u t2) := hFmono (v t1) (u t2) (hchain t1 t2 hlt) hw1.1
        rw [hEq] at hmem
        exact absurd hmem hw2.2
      · rfl
      · have hmem : w t2 ∈ F (u t1) := hFmono (v t2) (u t1) (hchain t2 t1 hgt) hw2.1
        rw [← hEq] at hmem
        exact absurd hmem hw1.2
  · rw [Finset.not_nonempty_iff_eq_empty.mp hT]
    simp

lemma clique_implies_not_admits {n k : Nat} (hk : 2 ≤ k) (E : SimpleGraph (Fin n))
    (x : Finset (Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1))))
    (hx : ∀ i, i ∈ x ↔ E.Adj (wireOf n k i).1 (wireOf n k i).2)
    (C : Finset (Fin (Nat.choose k 2 * Nat.choose n 2)))
    (hCcard : C.card = Nat.choose k 2)
    (hCE : ∀ c ∈ C, E.Adj (v1 n k c) (v2 n k c))
    (hCcons : ∀ c ∈ C, ∀ d ∈ C, consChoice n k c d = true)
    (f : Finset (Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1))) →
         Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1)) → Bool)
    (hf1 : ∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, graphG n k i j = false) → f y j = true)
    (hf2 : ∀ y, y ⊆ x → ∀ j ∈ y, f y j = false)
    (hf3 : ∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true)
    (hbound : ∀ y l, y ⊆ x → packOf x f l y →
      l ≤ alphaOf (graphG n k) y + ((Nat.choose k 2 * Nat.choose n 2 + 1) * Nat.choose k 2 - 1)) :
    False := by
  let m := Nat.choose k 2 * Nat.choose n 2
  let Q : Finset (Fin m × Fin (m + 1)) := C ×ˢ (Finset.univ : Finset (Fin (m + 1)))
  have hpath_sub_x : ∀ q ∈ Q, pathSet q.1 q.2 ⊆ x := by
    intro q hq i hi
    have hqC : q.1 ∈ C := (Finset.mem_product.mp hq).1
    have hblk : blk i = q.1 := (mem_pathSet_iff q.1 q.2 i).mp hi |>.1
    rw [hx]
    change E.Adj (v1 n k (blk i)) (v2 n k (blk i))
    rw [hblk]
    exact hCE q.1 hqC
  have hind_build : ∀ S : Finset (Fin m × Fin (m + 1)), S ⊆ Q →
      ∃ y, y ⊆ S.biUnion (fun q => pathSet q.1 q.2) ∧
        ∃ l, packOf x f l y ∧ l = alphaOf (graphG n k) y + S.card := by
    intro S
    induction S using Finset.induction with
    | empty =>
      intro _
      refine ⟨∅, Finset.empty_subset _, 0, trivial, ?_⟩
      simp [alphaOf_empty]
    | @insert q S hqS ih =>
      intro hSQ
      have hSq : S ⊆ Q := (Finset.subset_insert q S).trans hSQ
      have hqQ : q ∈ Q := hSQ (Finset.mem_insert_self q S)
      rcases ih hSq with ⟨y, hyS, l, hpack, hl⟩
      let c := q.1
      let p := q.2
      let v0 := mkV c p ⟨0, by omega⟩
      let v1 := mkV c p ⟨1, by omega⟩
      let v2 := mkV c p ⟨2, by omega⟩
      have hyx : y ⊆ x := by
        intro i hi
        rcases Finset.mem_biUnion.mp (hyS hi) with ⟨q', hq'S, hiq'⟩
        exact hpath_sub_x q' (hSq hq'S) hiq'
      have hpx : pathSet c p ⊆ x := hpath_sub_x q hqQ
      have hv0x : v0 ∈ x := hpx (by simp [pathSet, v0])
      have hv1x : v1 ∈ x := hpx (by simp [pathSet, v1])
      have hv2x : v2 ∈ x := hpx (by simp [pathSet, v2])
      have hdisj : Disjoint y (pathSet c p) := by
        rw [Finset.disjoint_left]
        intro i hiy hip
        rcases Finset.mem_biUnion.mp (hyS hiy) with ⟨q', hq'S, hiq'⟩
        have h1 := (mem_pathSet_iff q'.1 q'.2 i).mp hiq'
        have h2 := (mem_pathSet_iff c p i).mp hip
        have hqq : q' = q := Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
        exact hqS (hqq ▸ hq'S)
      have hnoedge : ∀ i ∈ y, ∀ j ∈ pathSet c p, graphG n k i j = false := by
        intro i hiy j hjp
        rcases Finset.mem_biUnion.mp (hyS hiy) with ⟨q', hq'S, hiq'⟩
        have h1 := (mem_pathSet_iff q'.1 q'.2 i).mp hiq'
        have h2 := (mem_pathSet_iff c p j).mp hjp
        have hne : q' ≠ q := fun hEq => hqS (hEq ▸ hq'S)
        unfold graphG
        rw [h1.1, h2.1]
        by_cases hc : q'.1 = c
        · have hpne : q'.2 ≠ p := fun hp => hne (Prod.ext hc hp)
          simp only [hc, ↓reduceIte, h1.2, h2.2]
          simp [hpne]
        · simp only [hc, ↓reduceIte]
          have hq'C : q'.1 ∈ C := (Finset.mem_product.mp (hSq hq'S)).1
          have hqC : c ∈ C := (Finset.mem_product.mp hqQ).1
          rw [hCcons q'.1 hq'C c hqC]
          rfl
      have hv0_not : v0 ∉ y := Finset.disjoint_right.mp hdisj (by simp [pathSet, v0])
      have hv1_not : v1 ∉ y := Finset.disjoint_right.mp hdisj (by simp [pathSet, v1])
      have hv2_not : v2 ∉ y := Finset.disjoint_right.mp hdisj (by simp [pathSet, v2])
      have hne01 : v0 ≠ v1 := mkV_ne_of_pos_ne c p (by intro h; have := congrArg Fin.val h; simp at this)
      have hne02 : v0 ≠ v2 := mkV_ne_of_pos_ne c p (by intro h; have := congrArg Fin.val h; simp at this)
      have hne12 : v1 ≠ v2 := mkV_ne_of_pos_ne c p (by intro h; have := congrArg Fin.val h; simp at this)
      have hg02 : graphG n k v0 v2 = false := graphG_path_02 n k c p
      have hg20 : graphG n k v2 v0 = false := by rw [graphG_symm]; exact hg02
      have hfy0 : f y v0 = true :=
        hf1 y hyx v0 hv0x ⟨hv0_not, fun i hi => hnoedge i hi v0 (by simp [pathSet, v0])⟩
      have hfy1 : f y v1 = true :=
        hf1 y hyx v1 hv1x ⟨hv1_not, fun i hi => hnoedge i hi v1 (by simp [pathSet, v1])⟩
      have hfy2 : f y v2 = true :=
        hf1 y hyx v2 hv2x ⟨hv2_not, fun i hi => hnoedge i hi v2 (by simp [pathSet, v2])⟩
      let y0 := y ∪ {v0}
      let y1 := y ∪ {v1}
      let y2 := y ∪ {v2}
      let y01 := y ∪ {v0, v1}
      let y12 := y ∪ {v1, v2}
      let y012 := y ∪ pathSet c p
      have hy0x : y0 ⊆ x := Finset.union_subset hyx (Finset.singleton_subset_iff.mpr hv0x)
      have hy1x : y1 ⊆ x := Finset.union_subset hyx (Finset.singleton_subset_iff.mpr hv1x)
      have hy2x : y2 ⊆ x := Finset.union_subset hyx (Finset.singleton_subset_iff.mpr hv2x)
      have hy01x : y01 ⊆ x := Finset.union_subset hyx (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)
      have hy12x : y12 ⊆ x := Finset.union_subset hyx (by intro w hw; simp at hw; rcases hw with rfl | rfl <;> assumption)
      have hy012x : y012 ⊆ x := Finset.union_subset hyx hpx
      have hfy0_v0 : f y0 v0 = false := hf2 y0 hy0x v0 (by simp [y0])
      have hfy1_v1 : f y1 v1 = false := hf2 y1 hy1x v1 (by simp [y1])
      have hfy2_v2 : f y2 v2 = false := hf2 y2 hy2x v2 (by simp [y2])
      have hfy01_v0 : f y01 v0 = false := hf2 y01 hy01x v0 (by simp [y01])
      have hfy012_v2 : f y012 v2 = false := hf2 y012 hy012x v2 (by simp [y012, pathSet, v2])
      have hfy0_v2 : f y0 v2 = true := by
        apply hf1 y0 hy0x v2 hv2x
        refine ⟨?_, ?_⟩
        · simp [y0, hv2_not, hne02.symm]
        · intro i hi
          rcases Finset.mem_union.mp hi with hiy | hi0
          · exact hnoedge i hiy v2 (by simp [pathSet, v2])
          · rw [Finset.mem_singleton.mp hi0]; exact hg02
      have hfy2_v0 : f y2 v0 = true := by
        apply hf1 y2 hy2x v0 hv0x
        refine ⟨?_, ?_⟩
        · simp [y2, hv0_not, hne02]
        · intro i hi
          rcases Finset.mem_union.mp hi with hiy | hi2
          · exact hnoedge i hiy v0 (by simp [pathSet, v0])
          · rw [Finset.mem_singleton.mp hi2]; exact hg20
      by_cases hcase1 : f y01 v2 = false
      · refine ⟨y01, ?_, l + 2, ?_, ?_⟩
        · rw [Finset.biUnion_insert]
          apply Finset.union_subset
          · exact hyS.trans Finset.subset_union_right
          · intro w hw
            apply Finset.mem_union_left
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            simp only [pathSet, Finset.mem_insert, Finset.mem_singleton]
            rcases hw with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
        · have hp1 : packOf x f (l + 1) y0 :=
            ⟨y, y0, v0, hv0x, hpack, Finset.subset_union_left, Finset.Subset.rfl, hfy0, hfy0_v0⟩
          have hy0_sub_y01 : y0 ⊆ y01 := by
            intro w hw
            simp only [y0, y01, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
            rcases hw with hw | rfl
            · exact Or.inl hw
            · exact Or.inr (Or.inl rfl)
          exact ⟨y0, y01, v2, hv2x, hp1, hy0_sub_y01, Finset.Subset.rfl, hfy0_v2, hcase1⟩
        · have hd01 : Disjoint y {v0, v1} := by
            refine Disjoint.mono_right ?_ hdisj
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            simp only [pathSet, Finset.mem_insert, Finset.mem_singleton]
            rcases hw with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
          have hno01 : ∀ i ∈ y, ∀ j ∈ ({v0, v1} : Finset _), graphG n k i j = false := by
            intro i hi j hj
            apply hnoedge i hi j
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            simp only [pathSet, Finset.mem_insert, Finset.mem_singleton]
            rcases hj with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
          have halpha : alphaOf (graphG n k) y01 = alphaOf (graphG n k) y + 1 := by
            rw [alphaOf_disjoint_union (graphG_symm n k) hd01 hno01,
              alphaOf_pair_edge (graphG_irrefl n k) (graphG_path_01 n k c p)]
          rw [halpha, Finset.card_insert_of_notMem hqS]
          omega
      · by_cases hcase2 : f y12 v0 = false
        · refine ⟨y12, ?_, l + 2, ?_, ?_⟩
          · rw [Finset.biUnion_insert]
            apply Finset.union_subset
            · exact hyS.trans Finset.subset_union_right
            · intro w hw
              apply Finset.mem_union_left
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              simp only [pathSet, Finset.mem_insert, Finset.mem_singleton]
              rcases hw with rfl | rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
          · have hp1 : packOf x f (l + 1) y2 :=
              ⟨y, y2, v2, hv2x, hpack, Finset.subset_union_left, Finset.Subset.rfl, hfy2, hfy2_v2⟩
            have hy2_sub_y12 : y2 ⊆ y12 := by
              intro w hw
              simp only [y2, y12, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
              rcases hw with hw | rfl
              · exact Or.inl hw
              · exact Or.inr (Or.inr rfl)
            exact ⟨y2, y12, v0, hv0x, hp1, hy2_sub_y12, Finset.Subset.rfl, hfy2_v0, hcase2⟩
          · have hd12 : Disjoint y {v1, v2} := by
              refine Disjoint.mono_right ?_ hdisj
              intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              simp only [pathSet, Finset.mem_insert, Finset.mem_singleton]
              rcases hw with rfl | rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
            have hno12 : ∀ i ∈ y, ∀ j ∈ ({v1, v2} : Finset _), graphG n k i j = false := by
              intro i hi j hj
              apply hnoedge i hi j
              simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              simp only [pathSet, Finset.mem_insert, Finset.mem_singleton]
              rcases hj with rfl | rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
            have halpha : alphaOf (graphG n k) y12 = alphaOf (graphG n k) y + 1 := by
              rw [alphaOf_disjoint_union (graphG_symm n k) hd12 hno12,
                alphaOf_pair_edge (graphG_irrefl n k) (graphG_path_12 n k c p)]
            rw [halpha, Finset.card_insert_of_notMem hqS]
            omega
        · have hf01_true : f y01 v2 = true := Bool.eq_true_of_not_eq_false hcase1
          have hf12_true : f y12 v0 = true := Bool.eq_true_of_not_eq_false hcase2
          have hy1_sub_y12 : y1 ⊆ y12 := by
            intro w hw
            simp only [y1, y12, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
            rcases hw with hw | rfl
            · exact Or.inl hw
            · exact Or.inr (Or.inl rfl)
          have hfy1_v0 : f y1 v0 = true := hf3 y1 y12 hy1_sub_y12 hy12x v0 hv0x hf12_true
          refine ⟨y012, ?_, l + 3, ?_, ?_⟩
          · rw [Finset.biUnion_insert]
            exact Finset.union_subset (hyS.trans Finset.subset_union_right) Finset.subset_union_left
          · have hp1 : packOf x f (l + 1) y1 :=
              ⟨y, y1, v1, hv1x, hpack, Finset.subset_union_left, Finset.Subset.rfl, hfy1, hfy1_v1⟩
            have hy1_sub_y01 : y1 ⊆ y01 := by
              intro w hw
              simp only [y1, y01, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
              rcases hw with hw | rfl
              · exact Or.inl hw
              · exact Or.inr (Or.inr rfl)
            have hp2 : packOf x f (l + 2) y01 :=
              ⟨y1, y01, v0, hv0x, hp1, hy1_sub_y01, Finset.Subset.rfl, hfy1_v0, hfy01_v0⟩
            have hy01_sub_y012 : y01 ⊆ y012 := by
              intro w hw
              simp only [y01, y012, pathSet, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw ⊢
              rcases hw with hw | rfl | rfl
              · exact Or.inl hw
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr (Or.inl rfl))
            exact ⟨y01, y012, v2, hv2x, hp2, hy01_sub_y012, Finset.Subset.rfl, hf01_true, hfy012_v2⟩
          · have halpha : alphaOf (graphG n k) y012 = alphaOf (graphG n k) y + 2 := by
              rw [alphaOf_disjoint_union (graphG_symm n k) hdisj hnoedge, alphaOf_p3 n k c p]
            rw [halpha, Finset.card_insert_of_notMem hqS]
            omega
  rcases hind_build Q Finset.Subset.rfl with ⟨y, hyQ, l, hpack, hl⟩
  have hyx : y ⊆ x := by
    intro i hi
    rcases Finset.mem_biUnion.mp (hyQ hi) with ⟨q, hqQ, hiq⟩
    exact hpath_sub_x q hqQ hiq
  have hle := hbound y l hyx hpack
  have hQcard : Q.card = (m + 1) * Nat.choose k 2 := by
    simp only [Q, Finset.card_product, Finset.card_univ, Fintype.card_fin, hCcard]
    exact Nat.mul_comm _ _
  have hKpos : 0 < Nat.choose k 2 := Nat.choose_pos hk
  have hQpos : 0 < (m + 1) * Nat.choose k 2 := Nat.mul_pos (Nat.succ_pos m) hKpos
  rw [hQcard] at hl
  dsimp only [m] at hl hQpos
  omega

def fMin {N : Nat} (g : Fin N → Fin N → Bool) (y : Finset (Fin N)) (j : Fin N) : Bool :=
  decide (j ∉ y ∧ ∀ i ∈ y, g i j = false)

lemma no_clique_implies_admits {n k : Nat} (hk : 2 ≤ k) (E : SimpleGraph (Fin n))
    (x : Finset (Fin (3 * (Nat.choose k 2 * Nat.choose n 2) * (Nat.choose k 2 * Nat.choose n 2 + 1))))
    (hx : ∀ i, i ∈ x ↔ E.Adj (wireOf n k i).1 (wireOf n k i).2)
    (hno : ¬ ∃ h : Fin k → Fin n, Function.Injective h ∧ ∀ i j, i ≠ j → E.Adj (h i) (h j)) :
    let g := graphG n k
    let f := fMin g
    (∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, g i j = false) → f y j = true) ∧
    (∀ y, y ⊆ x → ∀ j ∈ y, f y j = false) ∧
    (∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true) ∧
    ∀ y l, y ⊆ x → packOf x f l y →
      l ≤ alphaOf g y + ((Nat.choose k 2 * Nat.choose n 2 + 1) * Nat.choose k 2 - 1) := by
  dsimp only
  let m := Nat.choose k 2 * Nat.choose n 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y _ j _ hcond
    rw [fMin, decide_eq_true_eq]
    exact hcond
  · intro y _ j hj
    simp [fMin, hj]
  · intro u v huv _ j _ hfv
    simp only [fMin, decide_eq_true_eq] at hfv ⊢
    exact ⟨fun hju => hfv.1 (huv hju), fun i hi => hfv.2 i (huv hi)⟩
  · intro y l hyx hpack
    rcases unpack_packOf hpack with ⟨u, v, jw, hstep, hchain⟩
    let supp : Finset (Fin (3 * m * (m + 1))) → Finset (Fin m) := fun z => z.image blk
    let A_steps : Finset (Fin l) := (Finset.univ : Finset (Fin l)).filter (fun t => supp (u t) = supp (v t))
    let B_steps : Finset (Fin l) := (Finset.univ : Finset (Fin l)).filter (fun t => supp (u t) ≠ supp (v t))
    have hsplit_l : A_steps.card + B_steps.card = l := by
      have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin l)))
        (p := fun t => supp (u t) = supp (v t))
      simpa [A_steps, B_steps, Finset.card_univ, Fintype.card_fin] using hcard
    have hB_le : B_steps.card ≤ m := by
      have h1 : B_steps.card ≤ (supp y).card := by
        apply monotone_chain_strict_card (fun t => (hstep t).2.2.1) hchain supp
        · intro a b hab
          exact Finset.image_subset_image hab
        · intro t ht
          have hne : supp (u t) ≠ supp (v t) := (Finset.mem_filter.mp ht).2
          have hsub : supp (u t) ⊆ supp (v t) := Finset.image_subset_image (hstep t).2.1
          have hnsub : ¬ supp (v t) ⊆ supp (u t) := fun hrev => hne (Finset.Subset.antisymm hsub hrev)
          exact Finset.not_subset.mp hnsub
      have h2 : (supp y).card ≤ m := by
        have := Finset.card_le_univ (supp y)
        simpa [Fintype.card_fin] using this
      exact h1.trans h2
    have hcons_ut : ∀ t : Fin l, ∀ c' ∈ supp (u t), consChoice n k c' (blk (jw t)) = true := by
      intro t c' hc'
      rcases Finset.mem_image.mp hc' with ⟨i, hi, rfl⟩
      have hfu := (hstep t).2.2.2.1
      simp only [fMin, decide_eq_true_eq] at hfu
      have hgi : graphG n k i (jw t) = false := hfu.2 i hi
      by_cases hEq : blk i = blk (jw t)
      · rw [hEq]; exact consChoice_refl n k _
      · simp only [graphG, hEq, ↓reduceIte, Bool.not_eq_false'] at hgi
        exact hgi
    have hA_strict : ∀ t ∈ A_steps,
        (∃ a, a ∈ v t ∩ pathSet (blk (jw t)) (pth (jw t)) ∧
              a ∉ u t ∩ pathSet (blk (jw t)) (pth (jw t))) ∧
        blk (jw t) ∈ supp (v t) := by
      intro t ht
      have hEqSupp : supp (u t) = supp (v t) := (Finset.mem_filter.mp ht).2
      have hfu := (hstep t).2.2.2.1
      have hfv := (hstep t).2.2.2.2
      simp only [fMin, decide_eq_true_eq] at hfu
      simp only [fMin, decide_eq_false_iff_not, not_and, not_forall, Bool.not_eq_false] at hfv
      by_cases hmem : jw t ∈ v t
      · have hjp : jw t ∈ pathSet (blk (jw t)) (pth (jw t)) :=
          (mem_pathSet_iff _ _ _).mpr ⟨rfl, rfl⟩
        refine ⟨⟨jw t, Finset.mem_inter.mpr ⟨hmem, hjp⟩, fun h => hfu.1 (Finset.mem_inter.mp h).1⟩, ?_⟩
        exact Finset.mem_image.mpr ⟨jw t, hmem, rfl⟩
      · rcases hfv hmem with ⟨i, hiv, hgi⟩
        have hbi_supp : blk i ∈ supp (u t) := by
          rw [hEqSupp]
          exact Finset.mem_image.mpr ⟨i, hiv, rfl⟩
        have hcons_i : consChoice n k (blk i) (blk (jw t)) = true := hcons_ut t (blk i) hbi_supp
        have hblk_eq : blk i = blk (jw t) := by
          by_contra hne
          have hfalse : graphG n k i (jw t) = false := by
            simp [graphG, hne, hcons_i]
          rw [hgi] at hfalse
          cases hfalse
        have hpth_eq : pth i = pth (jw t) := by
          simp only [graphG, hblk_eq, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hgi
          exact hgi.1
        have hip : i ∈ pathSet (blk (jw t)) (pth (jw t)) :=
          (mem_pathSet_iff _ _ _).mpr ⟨hblk_eq, hpth_eq⟩
        have hiu : i ∉ u t := fun hiu => by
          have hfalse := hfu.2 i hiu
          rw [hgi] at hfalse
          cases hfalse
        refine ⟨⟨i, Finset.mem_inter.mpr ⟨hiv, hip⟩, fun h => hiu (Finset.mem_inter.mp h).1⟩, ?_⟩
        exact Finset.mem_image.mpr ⟨i, hiv, hblk_eq⟩
    let C_star : Finset (Fin m) := A_steps.image (fun t => blk (jw t))
    have hC_E : ∀ c ∈ C_star, E.Adj (v1 n k c) (v2 n k c) := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨t, _, rfl⟩
      exact (hx (jw t)).mp (hstep t).1
    have hC_cons : ∀ c1 ∈ C_star, ∀ c2 ∈ C_star, consChoice n k c1 c2 = true := by
      intro c1 hc1 c2 hc2
      rcases Finset.mem_image.mp hc1 with ⟨t1, ht1, rfl⟩
      rcases Finset.mem_image.mp hc2 with ⟨t2, ht2, rfl⟩
      rcases lt_trichotomy t1 t2 with hlt | rfl | hgt
      · have hmem1 : blk (jw t1) ∈ supp (v t1) := (hA_strict t1 ht1).2
        have hmem2 : blk (jw t1) ∈ supp (u t2) :=
          Finset.image_subset_image (hchain t1 t2 hlt) hmem1
        exact hcons_ut t2 (blk (jw t1)) hmem2
      · exact consChoice_refl n k _
      · have hmem1 : blk (jw t2) ∈ supp (v t2) := (hA_strict t2 ht2).2
        have hmem2 : blk (jw t2) ∈ supp (u t1) :=
          Finset.image_subset_image (hchain t2 t1 hgt) hmem1
        rw [consChoice_symm]
        exact hcons_ut t1 (blk (jw t2)) hmem2
    have hC_card_le : C_star.card ≤ Nat.choose k 2 - 1 := by
      have hle := card_le_of_pairwise_consChoice C_star hC_cons
      have hne : C_star.card ≠ Nat.choose k 2 := fun heq =>
        hno ((clique_iff_consSet hk E).mpr ⟨C_star, heq, hC_E, hC_cons⟩)
      omega
    let Q_star : Finset (Fin m × Fin (m + 1)) := C_star ×ˢ (Finset.univ : Finset (Fin (m + 1)))
    let A_cp : Fin m × Fin (m + 1) → Finset (Fin l) :=
      fun q => A_steps.filter (fun t => blk (jw t) = q.1 ∧ pth (jw t) = q.2)
    have hA_sub : A_steps ⊆ Q_star.biUnion A_cp := by
      intro t ht
      refine Finset.mem_biUnion.mpr ⟨(blk (jw t), pth (jw t)), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨t, ht, rfl⟩, Finset.mem_univ _⟩
      · exact Finset.mem_filter.mpr ⟨ht, rfl, rfl⟩
    have hA_cp_le : ∀ q ∈ Q_star, (A_cp q).card ≤ alphaOf (graphG n k) (y ∩ pathSet q.1 q.2) + 1 := by
      intro q _
      have h1 : (A_cp q).card ≤ (y ∩ pathSet q.1 q.2).card := by
        apply monotone_chain_strict_card (fun t => (hstep t).2.2.1) hchain (fun z => z ∩ pathSet q.1 q.2)
        · intro a b hab
          exact Finset.inter_subset_inter_right hab
        · intro t ht
          rcases Finset.mem_filter.mp ht with ⟨htA, h1, h2⟩
          rw [← h1, ← h2]
          exact (hA_strict t htA).1
      have h2 := card_le_alphaOf_add_one_of_subset_pathSet n k q.1 q.2
        (w := y ∩ pathSet q.1 q.2) Finset.inter_subset_right
      exact h1.trans h2
    have hA_le_sum : A_steps.card ≤ (∑ q ∈ Q_star, alphaOf (graphG n k) (y ∩ pathSet q.1 q.2)) + Q_star.card := by
      calc
        A_steps.card ≤ (Q_star.biUnion A_cp).card := Finset.card_le_card hA_sub
        _ ≤ ∑ q ∈ Q_star, (A_cp q).card := Finset.card_biUnion_le
        _ ≤ ∑ q ∈ Q_star, (alphaOf (graphG n k) (y ∩ pathSet q.1 q.2) + 1) :=
          Finset.sum_le_sum hA_cp_le
        _ = (∑ q ∈ Q_star, alphaOf (graphG n k) (y ∩ pathSet q.1 q.2)) + Q_star.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    have hsum_le_alpha : (∑ q ∈ Q_star, alphaOf (graphG n k) (y ∩ pathSet q.1 q.2)) ≤ alphaOf (graphG n k) y := by
      have heq : alphaOf (graphG n k) (Q_star.biUnion (fun q => y ∩ pathSet q.1 q.2)) =
          ∑ q ∈ Q_star, alphaOf (graphG n k) (y ∩ pathSet q.1 q.2) := by
        apply alphaOf_biUnion_eq_sum (graphG_symm n k)
        · intro q1 _ q2 _ hne
          rw [Finset.disjoint_left]
          intro i hi1 hi2
          have h1 := (mem_pathSet_iff q1.1 q1.2 i).mp (Finset.mem_inter.mp hi1).2
          have h2 := (mem_pathSet_iff q2.1 q2.2 i).mp (Finset.mem_inter.mp hi2).2
          exact hne (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2))
        · intro q1 hq1 q2 hq2 hne i hi1 j hj2
          have h1 := (mem_pathSet_iff q1.1 q1.2 i).mp (Finset.mem_inter.mp hi1).2
          have h2 := (mem_pathSet_iff q2.1 q2.2 j).mp (Finset.mem_inter.mp hj2).2
          unfold graphG
          rw [h1.1, h2.1]
          by_cases hc : q1.1 = q2.1
          · have hp : q1.2 ≠ q2.2 := fun hp => hne (Prod.ext hc hp)
            simp [hc, h1.2, h2.2, hp]
          · simp only [hc, ↓reduceIte]
            rw [hC_cons q1.1 (Finset.mem_product.mp hq1).1 q2.1 (Finset.mem_product.mp hq2).1]
            rfl
      rw [← heq]
      apply alphaOf_mono
      intro i hi
      rcases Finset.mem_biUnion.mp hi with ⟨q, _, hiq⟩
      exact (Finset.mem_inter.mp hiq).1
    have hQ_card : Q_star.card ≤ (Nat.choose k 2 - 1) * (m + 1) := by
      simp only [Q_star, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_le_mul_right (m + 1) hC_card_le
    have hKpos : 1 ≤ Nat.choose k 2 := Nat.choose_pos hk
    obtain ⟨K', hK'⟩ : ∃ K', Nat.choose k 2 = K' + 1 := ⟨Nat.choose k 2 - 1, by omega⟩
    have harith : (Nat.choose k 2 - 1) * (m + 1) + m = (m + 1) * Nat.choose k 2 - 1 := by
      rw [hK']
      have h1 : (K' + 1 - 1) * (m + 1) = K' * (m + 1) := by simp
      have h2 : (m + 1) * (K' + 1) = K' * (m + 1) + m + 1 := by
        rw [Nat.mul_succ, Nat.mul_comm (m + 1) K']
        omega
      rw [h1, h2]
      omega
    change l ≤ alphaOf (graphG n k) y + ((m + 1) * Nat.choose k 2 - 1)
    omega

end PEqualNP.Outside.L_meta_48519_aux

theorem PEqualNP.Outside.L_meta_48519 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n k : Nat), 2 ≤ k →
  let m := (Nat.choose k 2)*(Nat.choose n 2)
  let N := 3*m*(m+1)
  ∃ (g : Fin N → Fin N → Bool)
    (wire : Fin N → Fin n × Fin n),
    (∀ i, g i i = false) ∧ (∀ i j, g i j = g j i) ∧
    (∀ i, (wire i).1 < (wire i).2) ∧
    ∀ E : SimpleGraph (Fin n),
      let x := (Finset.univ : Finset (Fin N)).filter (fun i => E.Adj (wire i).1 (wire i).2)
      let alpha := fun (y : Finset (Fin N)) =>
        (y.powerset.filter (fun z => ∀ i ∈ z, ∀ j ∈ z, g i j = false)).sup Finset.card
      let admits := fun (e : Nat) =>
        ∃ f : Finset (Fin N) → Fin N → Bool,
          (∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, g i j = false) → f y j = true) ∧
          (∀ y, y ⊆ x → ∀ j ∈ y, f y j = false) ∧
          (∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true) ∧
          let pack := Nat.rec (motive := fun _ => Finset (Fin N) → Prop) (fun _ => True)
            (fun _ prev y => ∃ (u v : Finset (Fin N)) (j : Fin N), j ∈ x ∧
              prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false)
          ∀ y l, y ⊆ x → pack l y → l ≤ alpha y + e
      (∃ h : Fin k → Fin n, Function.Injective h ∧
        ∀ i j, i ≠ j → E.Adj (h i) (h j)) ↔ ¬ admits ((m+1)*(Nat.choose k 2)-1)) := by
  let _ : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro n k hk
  refine ⟨PEqualNP.Outside.L_meta_48519_aux.graphG n k,
          PEqualNP.Outside.L_meta_48519_aux.wireOf n k,
          PEqualNP.Outside.L_meta_48519_aux.graphG_irrefl n k,
          PEqualNP.Outside.L_meta_48519_aux.graphG_symm n k,
          PEqualNP.Outside.L_meta_48519_aux.wireOf_lt n k, ?_⟩
  intro E
  have hx : ∀ i, i ∈ (Finset.univ : Finset (Fin (3 * (Nat.choose k 2 * Nat.choose n 2) *
      (Nat.choose k 2 * Nat.choose n 2 + 1)))).filter
      (fun i => E.Adj (PEqualNP.Outside.L_meta_48519_aux.wireOf n k i).1
                      (PEqualNP.Outside.L_meta_48519_aux.wireOf n k i).2) ↔
      E.Adj (PEqualNP.Outside.L_meta_48519_aux.wireOf n k i).1
            (PEqualNP.Outside.L_meta_48519_aux.wireOf n k i).2 := by
    intro i
    simp
  constructor
  · intro hcl hadm
    rcases (PEqualNP.Outside.L_meta_48519_aux.clique_iff_consSet hk E).mp hcl with ⟨C, hCcard, hCE, hCcons⟩
    rcases hadm with ⟨f, hf1, hf2, hf3, hbound⟩
    exact PEqualNP.Outside.L_meta_48519_aux.clique_implies_not_admits hk E _ hx C hCcard hCE hCcons f hf1 hf2 hf3 hbound
  · intro hnot
    by_contra hno
    apply hnot
    exact ⟨PEqualNP.Outside.L_meta_48519_aux.fMin (PEqualNP.Outside.L_meta_48519_aux.graphG n k),
      PEqualNP.Outside.L_meta_48519_aux.no_clique_implies_admits hk E _ hx hno⟩
