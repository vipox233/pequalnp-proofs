import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace PEqualNP.Outside.L_lib_1213_aux

def pairSet (v : ℕ) : Finset (ℕ × Bool) := {(v, false), (v, true)}

lemma mem_pairSet (v : ℕ) (p : ℕ × Bool) : p ∈ pairSet v ↔ p.1 = v := by
  rcases p with ⟨x, b⟩
  cases b <;> simp [pairSet]

lemma card_pairSet (v : ℕ) : (pairSet v).card = 2 := by
  simp [pairSet]

def outdeg (arcs : Finset (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (arcs.filter (fun e => e.1 = v)).card

def indeg (arcs : Finset (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (arcs.filter (fun e => e.2 = v)).card

lemma outdeg_union_disjoint {A B : Finset (ℕ × ℕ)} (h : Disjoint A B) (v : ℕ) :
    outdeg (A ∪ B) v = outdeg A v + outdeg B v := by
  unfold outdeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

lemma indeg_union_disjoint {A B : Finset (ℕ × ℕ)} (h : Disjoint A B) (v : ℕ) :
    indeg (A ∪ B) v = indeg A v + indeg B v := by
  unfold indeg
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

lemma outdeg_eq_zero_of_forall {A : Finset (ℕ × ℕ)} {v : ℕ} (h : ∀ e ∈ A, e.1 ≠ v) :
    outdeg A v = 0 := by
  unfold outdeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  exact h e he

lemma indeg_eq_zero_of_forall {A : Finset (ℕ × ℕ)} {v : ℕ} (h : ∀ e ∈ A, e.2 ≠ v) :
    indeg A v = 0 := by
  unfold indeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he
  exact h e he

lemma outdeg_insert_of_not_mem {A : Finset (ℕ × ℕ)} {x y : ℕ} (h : (x, y) ∉ A) (v : ℕ) :
    outdeg (insert (x, y) A) v = outdeg A v + if x = v then 1 else 0 := by
  unfold outdeg
  rw [Finset.filter_insert]
  split_ifs with hxv
  · rw [Finset.card_insert_of_notMem]
    simp [h]
  · simp

lemma indeg_insert_of_not_mem {A : Finset (ℕ × ℕ)} {x y : ℕ} (h : (x, y) ∉ A) (v : ℕ) :
    indeg (insert (x, y) A) v = indeg A v + if y = v then 1 else 0 := by
  unfold indeg
  rw [Finset.filter_insert]
  split_ifs with hyv
  · rw [Finset.card_insert_of_notMem]
    simp [h]
  · simp

lemma outdeg_singleton (x y v : ℕ) :
    outdeg {(x, y)} v = if x = v then 1 else 0 := by
  have h := outdeg_insert_of_not_mem (A := (∅ : Finset (ℕ × ℕ))) (x := x) (y := y) (by simp) v
  simpa [outdeg] using h

lemma indeg_singleton (x y v : ℕ) :
    indeg {(x, y)} v = if y = v then 1 else 0 := by
  have h := indeg_insert_of_not_mem (A := (∅ : Finset (ℕ × ℕ))) (x := x) (y := y) (by simp) v
  simpa [indeg] using h

def shiftArcs (m : ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  S.image (fun e => (m + e.1, m + e.2))

def shiftBag (m : ℕ) (B : Finset (ℕ × Bool)) : Finset (ℕ × Bool) :=
  B.image (fun p => (m + p.1, p.2))

def shiftBags (m : ℕ) (L : List (Finset (ℕ × Bool))) : List (Finset (ℕ × Bool)) :=
  L.map (shiftBag m)

lemma mem_shiftArcs (m : ℕ) (S : Finset (ℕ × ℕ)) (e : ℕ × ℕ) :
    e ∈ shiftArcs m S ↔ ∃ a b, (a, b) ∈ S ∧ e = (m + a, m + b) := by
  simp only [shiftArcs, Finset.mem_image, Prod.exists]
  constructor
  · rintro ⟨a, b, hab, rfl⟩; exact ⟨a, b, hab, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩; exact ⟨a, b, hab, rfl⟩

lemma mem_shiftBag (m : ℕ) (B : Finset (ℕ × Bool)) (p : ℕ × Bool) :
    p ∈ shiftBag m B ↔ ∃ a b, (a, b) ∈ B ∧ p = (m + a, b) := by
  simp only [shiftBag, Finset.mem_image, Prod.exists]
  constructor
  · rintro ⟨a, b, hab, rfl⟩; exact ⟨a, b, hab, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩; exact ⟨a, b, hab, rfl⟩

lemma card_shiftBag (m : ℕ) (B : Finset (ℕ × Bool)) :
    (shiftBag m B).card = B.card := by
  unfold shiftBag
  apply Finset.card_image_of_injective
  intro p1 p2 h
  cases p1; cases p2
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Nat.add_left_cancel h.1) h.2

lemma outdeg_shiftArcs_add (m : ℕ) (S : Finset (ℕ × ℕ)) (v : ℕ) :
    outdeg (shiftArcs m S) (m + v) = outdeg S v := by
  unfold outdeg shiftArcs
  have hEq : (S.image (fun e => (m + e.1, m + e.2))).filter (fun e => e.1 = m + v) =
      (S.filter (fun e => e.1 = v)).image (fun e => (m + e.1, m + e.2)) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_image, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨a, b, hab, rfl, rfl⟩, hx⟩
      exact ⟨a, b, ⟨hab, Nat.add_left_cancel hx⟩, rfl, rfl⟩
    · rintro ⟨a, b, ⟨hab, rfl⟩, rfl, rfl⟩
      exact ⟨⟨a, b, hab, rfl, rfl⟩, rfl⟩
  rw [hEq]
  apply Finset.card_image_of_injective
  intro e1 e2 h
  cases e1; cases e2
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Nat.add_left_cancel h.1) (Nat.add_left_cancel h.2)

lemma indeg_shiftArcs_add (m : ℕ) (S : Finset (ℕ × ℕ)) (v : ℕ) :
    indeg (shiftArcs m S) (m + v) = indeg S v := by
  unfold indeg shiftArcs
  have hEq : (S.image (fun e => (m + e.1, m + e.2))).filter (fun e => e.2 = m + v) =
      (S.filter (fun e => e.2 = v)).image (fun e => (m + e.1, m + e.2)) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_image, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨a, b, hab, rfl, rfl⟩, hy⟩
      exact ⟨a, b, ⟨hab, Nat.add_left_cancel hy⟩, rfl, rfl⟩
    · rintro ⟨a, b, ⟨hab, rfl⟩, rfl, rfl⟩
      exact ⟨⟨a, b, hab, rfl, rfl⟩, rfl⟩
  rw [hEq]
  apply Finset.card_image_of_injective
  intro e1 e2 h
  cases e1; cases e2
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Nat.add_left_cancel h.1) (Nat.add_left_cancel h.2)

lemma outdeg_shiftArcs_lt {m : ℕ} (S : Finset (ℕ × ℕ)) {v : ℕ} (hv : v < m) :
    outdeg (shiftArcs m S) v = 0 := by
  apply outdeg_eq_zero_of_forall
  intro e he
  rw [mem_shiftArcs] at he
  rcases he with ⟨a, b, _, rfl⟩
  omega

lemma indeg_shiftArcs_lt {m : ℕ} (S : Finset (ℕ × ℕ)) {v : ℕ} (hv : v < m) :
    indeg (shiftArcs m S) v = 0 := by
  apply indeg_eq_zero_of_forall
  intro e he
  rw [mem_shiftArcs] at he
  rcases he with ⟨a, b, _, rfl⟩
  omega

def ListRI {α : Type*} (L : List (Finset α)) : Prop :=
  ∀ p s t u, s ≤ t → t ≤ u → (hs : s < L.length) → (ht : t < L.length) → (hu : u < L.length) →
    p ∈ L[s] → p ∈ L[u] → p ∈ L[t]

lemma ListRI_nil {α : Type*} : ListRI ([] : List (Finset α)) := by
  intro p s t u _ _ hs; simp at hs

lemma ListRI_singleton {α : Type*} (B : Finset α) : ListRI [B] := by
  intro p s t u hst htu hs ht hu hps _
  simp only [List.length_singleton] at hs ht hu
  have h1 : s = 0 := by omega
  have h2 : t = 0 := by omega
  subst h1; subst h2; exact hps

lemma ListRI_map_image {α β : Type*} [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    {L : List (Finset α)} (hL : ListRI L) :
    ListRI (L.map (Finset.image f)) := by
  intro q s t u hst htu hs ht hu hqs hqu
  simp only [List.length_map] at hs ht hu
  simp only [List.getElem_map, Finset.mem_image] at hqs hqu ⊢
  rcases hqs with ⟨p1, hp1, rfl⟩
  rcases hqu with ⟨p2, hp2, hp2eq⟩
  have heq : p2 = p1 := hf hp2eq
  rw [heq] at hp2
  exact ⟨p1, hL p1 s t u hst htu hs ht hu hp1 hp2, rfl⟩

lemma ListRI_map_union {α : Type*} [DecidableEq α] (S : Finset α)
    {L : List (Finset α)} (hL : ListRI L) :
    ListRI (L.map (fun B => S ∪ B)) := by
  intro p s t u hst htu hs ht hu hps hpu
  simp only [List.length_map] at hs ht hu
  simp only [List.getElem_map, Finset.mem_union] at hps hpu ⊢
  rcases hps with hpS | hps
  · exact Or.inl hpS
  · rcases hpu with hpS | hpu
    · exact Or.inl hpS
    · exact Or.inr (hL p s t u hst htu hs ht hu hps hpu)

lemma ListRI_append {α : Type*} {L1 L2 : List (Finset α)}
    (h1 : L1 ≠ []) (h2 : L2 ≠ [])
    (hRI1 : ListRI L1) (hRI2 : ListRI L2)
    (hBridge : ∀ p, (∃ B ∈ L1, p ∈ B) → (∃ B ∈ L2, p ∈ B) →
      p ∈ L1.getLast h1 ∧ p ∈ L2.head h2) :
    ListRI (L1 ++ L2) := by
  intro p s t u hst htu hs ht hu hps hpu
  have hlen1 : 0 < L1.length := List.length_pos_of_ne_nil h1
  have hlen2 : 0 < L2.length := List.length_pos_of_ne_nil h2
  simp only [List.length_append] at hs ht hu
  by_cases hu1 : u < L1.length
  · have hs1 : s < L1.length := by omega
    have ht1 : t < L1.length := by omega
    rw [List.getElem_append_left hs1] at hps
    rw [List.getElem_append_left hu1] at hpu
    rw [List.getElem_append_left ht1]
    exact hRI1 p s t u hst htu hs1 ht1 hu1 hps hpu
  · by_cases hs1 : s < L1.length
    · rw [List.getElem_append_left hs1] at hps
      rw [List.getElem_append_right (by omega)] at hpu
      have hB := hBridge p ⟨L1[s], List.getElem_mem hs1, hps⟩
        ⟨L2[u - L1.length], List.getElem_mem (by omega), hpu⟩
      have hlast : p ∈ L1[L1.length - 1]'(by omega) := by
        simpa [List.getLast_eq_getElem] using hB.1
      have hhead : p ∈ L2[0]'hlen2 := by
        simpa [List.head_eq_getElem] using hB.2
      by_cases ht1 : t < L1.length
      · rw [List.getElem_append_left ht1]
        exact hRI1 p s t (L1.length - 1) hst (by omega) hs1 ht1 (by omega) hps hlast
      · rw [List.getElem_append_right (by omega)]
        exact hRI2 p 0 (t - L1.length) (u - L1.length) (by omega) (by omega)
          hlen2 (by omega) (by omega) hhead hpu
    · rw [List.getElem_append_right (by omega)] at hps hpu
      rw [List.getElem_append_right (by omega)]
      exact hRI2 p (s - L1.length) (t - L1.length) (u - L1.length) (by omega) (by omega)
        (by omega) (by omega) (by omega) hps hpu

lemma ListRI_append_singleton {α : Type*} {L1 : List (Finset α)} (B : Finset α)
    (h1 : L1 ≠ []) (hRI1 : ListRI L1)
    (hBridge : ∀ p ∈ B, (∃ A ∈ L1, p ∈ A) → p ∈ L1.getLast h1) :
    ListRI (L1 ++ [B]) := by
  apply ListRI_append h1 (List.cons_ne_nil B []) hRI1 (ListRI_singleton B)
  intro p hA hB
  rcases hB with ⟨C, hC, hpC⟩
  simp only [List.mem_singleton] at hC
  subst hC
  exact ⟨hBridge p hpC hA, by simpa using hpC⟩

def vAt (m : ℕ) (v : Fin m → Bool) (p : ℕ) : Bool :=
  if h : p < m then v ⟨p, h⟩ else false

lemma vAt_of_lt {m : ℕ} (v : Fin m → Bool) {p : ℕ} (hp : p < m) :
    vAt m v p = v ⟨p, hp⟩ := by
  simp [vAt, hp]

def splitL (m k : ℕ) (v : Fin (m + k) → Bool) : Fin m → Bool :=
  fun i => v ⟨i.1, by omega⟩

def splitR (m k : ℕ) (v : Fin (m + k) → Bool) : Fin k → Bool :=
  fun j => v ⟨m + j.1, by omega⟩

def joinV (m k : ℕ) (v1 : Fin m → Bool) (v2 : Fin k → Bool) : Fin (m + k) → Bool :=
  fun i => if h : i.1 < m then v1 ⟨i.1, h⟩ else v2 ⟨i.1 - m, by omega⟩

lemma splitL_joinV (m k : ℕ) (v1 : Fin m → Bool) (v2 : Fin k → Bool) :
    splitL m k (joinV m k v1 v2) = v1 := by
  funext i
  simp [splitL, joinV, i.2]

lemma splitR_joinV (m k : ℕ) (v1 : Fin m → Bool) (v2 : Fin k → Bool) :
    splitR m k (joinV m k v1 v2) = v2 := by
  funext j
  have h1 : ¬ (m + j.1 < m) := by omega
  simp only [splitR, joinV, h1, ↓reduceDIte]
  congr 1; apply Fin.ext; simp

lemma joinV_split (m k : ℕ) (v : Fin (m + k) → Bool) :
    joinV m k (splitL m k v) (splitR m k v) = v := by
  funext i
  simp only [joinV, splitL, splitR]
  split_ifs with h
  · rfl
  · congr 1; apply Fin.ext; dsimp; omega

lemma vAt_joinV_lt {m k : ℕ} (v1 : Fin m → Bool) (v2 : Fin k → Bool) {p : ℕ} (hp : p < m) :
    vAt (m + k) (joinV m k v1 v2) p = vAt m v1 p := by
  have hp' : p < m + k := by omega
  simp [vAt, hp, hp', joinV]

lemma vAt_joinV_add {m k : ℕ} (v1 : Fin m → Bool) (v2 : Fin k → Bool) {j : ℕ} (hj : j < k) :
    vAt (m + k) (joinV m k v1 v2) (m + j) = vAt k v2 j := by
  have h1 : m + j < m + k := by omega
  have h2 : ¬ (m + j < m) := by omega
  simp only [vAt, h1, hj, ↓reduceDIte, joinV, h2]
  congr 1; apply Fin.ext; simp

lemma vAt_splitL_of_lt {m k : ℕ} (v : Fin (m + k) → Bool) {p : ℕ} (hp : p < m) :
    vAt m (splitL m k v) p = vAt (m + k) v p := by
  have hp' : p < m + k := by omega
  simp [vAt, hp, hp', splitL]

lemma vAt_splitR_of_lt {m k : ℕ} (v : Fin (m + k) → Bool) {j : ℕ} (hj : j < k) :
    vAt k (splitR m k v) j = vAt (m + k) v (m + j) := by
  have hp' : m + j < m + k := by omega
  simp [vAt, hj, hp', splitR]

lemma card_filter_add (m k : ℕ)
    (P1 : (Fin m → Bool) → Prop) [DecidablePred P1]
    (P2 : (Fin m → Bool) → (Fin k → Bool) → Prop) [∀ v1, DecidablePred (P2 v1)] :
    ((Finset.univ : Finset (Fin (m + k) → Bool)).filter
      (fun v => P1 (splitL m k v) ∧ P2 (splitL m k v) (splitR m k v))).card =
    ∑ v1 ∈ (Finset.univ : Finset (Fin m → Bool)).filter P1,
      ((Finset.univ : Finset (Fin k → Bool)).filter (fun v2 => P2 v1 v2)).card := by
  let S := ((Finset.univ : Finset (Fin m → Bool)) ×ˢ (Finset.univ : Finset (Fin k → Bool))).filter
    (fun p => P1 p.1 ∧ P2 p.1 p.2)
  have hbij : ((Finset.univ : Finset (Fin (m + k) → Bool)).filter
      (fun v => P1 (splitL m k v) ∧ P2 (splitL m k v) (splitR m k v))).card = S.card := by
    apply Finset.card_bij (fun v _ => (splitL m k v, splitR m k v))
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact hv
    · intro v1 _ v2 _ heq
      simp only [Prod.mk.injEq] at heq
      rw [← joinV_split m k v1, ← joinV_split m k v2, heq.1, heq.2]
    · intro ⟨v1, v2⟩ hp
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
      refine ⟨joinV m k v1 v2, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, splitL_joinV, splitR_joinV]
        exact hp
      · simp [splitL_joinV, splitR_joinV]
  rw [hbij]
  simp only [S, Finset.card_filter, Finset.sum_product]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v1 _
  split_ifs with h1
  · apply Finset.sum_congr rfl
    intro v2 _
    simp [h1]
  · simp [h1]

abbrev gValid (m : ℕ) (arcs : Finset (ℕ × ℕ)) (v : Fin m → Bool) : Prop :=
  ∀ e ∈ arcs, vAt m v e.1 = true → vAt m v e.2 = true

def gCount (m : ℕ) (arcs : Finset (ℕ × ℕ)) (a b : ℕ) (va vb : Bool) : ℕ :=
  ((Finset.univ : Finset (Fin m → Bool)).filter
    (fun v => gValid m arcs v ∧ vAt m v a = va ∧ vAt m v b = vb)).card

def gMat (K : ℕ) (va vb : Bool) : ℕ :=
  match va, vb with
  | false, false => 1
  | true, false => 0
  | true, true => 1
  | false, true => K

def gBase : ℕ × ℕ × ℕ × Finset (ℕ × ℕ) × List (Finset (ℕ × Bool)) :=
  (2, 0, 1, {(0, 1)}, [pairSet 0 ∪ pairSet 1])

def gInc (r : ℕ × ℕ × ℕ × Finset (ℕ × ℕ) × List (Finset (ℕ × Bool))) :
    ℕ × ℕ × ℕ × Finset (ℕ × ℕ) × List (Finset (ℕ × Bool)) :=
  let m := r.1
  let a := r.2.1
  let b := r.2.2.1
  let arcs := r.2.2.2.1
  let bags := r.2.2.2.2
  (m + 1, m, b, insert (m, a) arcs, bags ++ [pairSet m ∪ pairSet a ∪ pairSet b])

def dblNewArcs (m a b : ℕ) : Finset (ℕ × ℕ) :=
  {(a, m), (m, m + 1), (m + 1, a),
   (b, m + 2), (m + 2, m + 3), (m + 3, b),
   (m, m + 4), (m + 4, m + 2)}

def dblNewBag (m a b : ℕ) : Finset (ℕ × Bool) :=
  pairSet a ∪ pairSet b ∪ pairSet m ∪ pairSet (m + 1) ∪ pairSet (m + 2) ∪
    pairSet (m + 3) ∪ pairSet (m + 4)

def gDbl (r : ℕ × ℕ × ℕ × Finset (ℕ × ℕ) × List (Finset (ℕ × Bool))) :
    ℕ × ℕ × ℕ × Finset (ℕ × ℕ) × List (Finset (ℕ × Bool)) :=
  let m := r.1
  let a := r.2.1
  let b := r.2.2.1
  let arcs := r.2.2.2.1
  let bags := r.2.2.2.2
  (m + 5, m + 1, m + 3, arcs ∪ dblNewArcs m a b, bags ++ [dblNewBag m a b])

def gBuild : ℕ → ℕ × ℕ × ℕ × Finset (ℕ × ℕ) × List (Finset (ℕ × Bool))
  | 0 => gBase
  | 1 => gBase
  | k + 2 =>
    if (k + 2) % 2 = 0 then
      gDbl (gBuild ((k + 2) / 2))
    else
      gInc (gDbl (gBuild ((k + 2) / 2)))

def GInv (K : ℕ) (r : ℕ × ℕ × ℕ × Finset (ℕ × ℕ) × List (Finset (ℕ × Bool))) : Prop :=
  let m := r.1
  let a := r.2.1
  let b := r.2.2.1
  let arcs := r.2.2.2.1
  let bags := r.2.2.2.2
  a < m ∧ b < m ∧ a ≠ b ∧
  (∀ e ∈ arcs, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2) ∧
  (∀ v < m, outdeg arcs v ≤ 2 ∧ indeg arcs v ≤ 2) ∧
  outdeg arcs a ≤ 1 ∧ indeg arcs a ≤ 1 ∧ outdeg arcs b ≤ 1 ∧ indeg arcs b ≤ 1 ∧
  bags ≠ [] ∧
  (∀ B ∈ bags, ∀ p ∈ B, p.1 < m) ∧
  (∀ B ∈ bags, B.card ≤ 14) ∧
  (∀ hne : bags ≠ [], pairSet a ∪ pairSet b ⊆ bags.getLast hne) ∧
  (∀ v < m, ∃ B ∈ bags, (v, false) ∈ B ∧ (v, true) ∈ B) ∧
  (∀ e ∈ arcs, ∃ B ∈ bags, (e.1, true) ∈ B ∧ (e.2, false) ∈ B) ∧
  ListRI bags ∧
  bags.length + 1 ≤ m ∧
  ∀ va vb : Bool, gCount m arcs a b va vb = gMat K va vb

lemma gCount_base (va vb : Bool) : gCount 2 {(0, 1)} 0 1 va vb = gMat 1 va vb := by
  cases va <;> cases vb <;> decide

lemma GInv_base : GInv 1 gBase := by
  dsimp only [GInv, gBase]
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he; simp at he; subst he; omega
  · intro v hv
    interval_cases v <;> decide
  · decide
  · decide
  · decide
  · decide
  · exact List.cons_ne_nil _ _
  · intro B hB p hp
    simp only [List.mem_singleton] at hB; subst hB
    simp only [Finset.mem_union, mem_pairSet] at hp
    omega
  · intro B hB
    simp only [List.mem_singleton] at hB; subst hB
    decide
  · intro _; simp
  · intro v hv
    refine ⟨pairSet 0 ∪ pairSet 1, by simp, ?_, ?_⟩
    · interval_cases v <;> simp [pairSet]
    · interval_cases v <;> simp [pairSet]
  · intro e he
    simp only [Finset.mem_singleton] at he; subst he
    exact ⟨pairSet 0 ∪ pairSet 1, by simp, by simp [pairSet], by simp [pairSet]⟩
  · exact ListRI_singleton _
  · simp
  · exact gCount_base

lemma gInc_ext_count (va va' : Bool) :
    ((Finset.univ : Finset (Fin 1 → Bool)).filter
      (fun w => (w 0 = true → va = true) ∧ w 0 = va')).card =
    if (va' = true → va = true) then 1 else 0 := by
  cases va <;> cases va' <;> decide

lemma GInv_inc {K : ℕ} {r : ℕ × ℕ × ℕ × Finset (ℕ × ℕ) × List (Finset (ℕ × Bool))}
    (hr : GInv K r) : GInv (K + 1) (gInc r) := by
  rcases r with ⟨m, a, b, arcs, bags⟩
  dsimp only [GInv] at hr
  rcases hr with ⟨ha, hb, hab, harcs, hdeg, hoa, hia, hob, hib, hne, hblt, hbcard, hblast,
    hcovV, hcovE, hri, hlen, hcnt⟩
  dsimp only [GInv, gInc]
  have hnotmem : (m, a) ∉ arcs := by
    intro h; have := (harcs _ h).1; omega
  have hne' : bags ++ [pairSet m ∪ pairSet a ∪ pairSet b] ≠ [] := by simp
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, hne', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [Finset.mem_insert] at he
    rcases he with rfl | he
    · exact ⟨by omega, by omega, by omega⟩
    · have := harcs e he; exact ⟨by omega, by omega, this.2.2⟩
  · intro v hv
    rw [outdeg_insert_of_not_mem hnotmem, indeg_insert_of_not_mem hnotmem]
    by_cases hvm : v < m
    · have hd := hdeg v hvm
      split_ifs
      · omega
      · omega
      · subst_vars; omega
      · omega
    · have hveq : v = m := by omega
      subst v
      have ho0 : outdeg arcs m = 0 := outdeg_eq_zero_of_forall (fun e he => by have := (harcs e he).1; omega)
      have hi0 : indeg arcs m = 0 := indeg_eq_zero_of_forall (fun e he => by have := (harcs e he).2.1; omega)
      rw [ho0, hi0]
      split_ifs <;> omega
  · rw [outdeg_insert_of_not_mem hnotmem]
    have ho0 : outdeg arcs m = 0 := outdeg_eq_zero_of_forall (fun e he => by have := (harcs e he).1; omega)
    rw [ho0]; simp
  · rw [indeg_insert_of_not_mem hnotmem]
    have hi0 : indeg arcs m = 0 := indeg_eq_zero_of_forall (fun e he => by have := (harcs e he).2.1; omega)
    rw [hi0]; split_ifs <;> omega
  · rw [outdeg_insert_of_not_mem hnotmem]; split_ifs <;> omega
  · rw [indeg_insert_of_not_mem hnotmem]; split_ifs <;> omega
  · intro B hB p hp
    simp only [List.mem_append, List.mem_singleton] at hB
    rcases hB with hB | rfl
    · have := hblt B hB p hp; omega
    · simp only [Finset.mem_union, mem_pairSet] at hp; omega
  · intro B hB
    simp only [List.mem_append, List.mem_singleton] at hB
    rcases hB with hB | rfl
    · exact hbcard B hB
    · have h1 := Finset.card_union_le (pairSet m ∪ pairSet a) (pairSet b)
      have h2 := Finset.card_union_le (pairSet m) (pairSet a)
      simp only [card_pairSet] at h1 h2
      omega
  · intro _
    rw [List.getLast_append_singleton]
    intro p hp
    simp only [Finset.mem_union] at hp ⊢
    rcases hp with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · intro v hv
    by_cases hvm : v < m
    · rcases hcovV v hvm with ⟨B, hB, h1, h2⟩
      exact ⟨B, List.mem_append_left _ hB, h1, h2⟩
    · have hveq : v = m := by omega
      subst v
      refine ⟨pairSet m ∪ pairSet a ∪ pairSet b, by simp, ?_, ?_⟩ <;>
        simp [pairSet]
  · intro e he
    simp only [Finset.mem_insert] at he
    rcases he with rfl | he
    · refine ⟨pairSet m ∪ pairSet a ∪ pairSet b, by simp, ?_, ?_⟩ <;>
        simp [pairSet]
    · rcases hcovE e he with ⟨B, hB, h1, h2⟩
      exact ⟨B, List.mem_append_left _ hB, h1, h2⟩
  · apply ListRI_append_singleton _ hne hri
    intro p hp ⟨A, hA, hpA⟩
    have hplt : p.1 < m := hblt A hA p hpA
    simp only [Finset.mem_union, mem_pairSet] at hp
    rcases hp with (hpm | hpa) | hpb
    · omega
    · exact hblast hne (Finset.mem_union_left _ ((mem_pairSet a p).2 hpa))
    · exact hblast hne (Finset.mem_union_right _ ((mem_pairSet b p).2 hpb))
  · simp; omega
  · intro va' vb
    unfold gCount
    have hfilt : ((Finset.univ : Finset (Fin (m + 1) → Bool)).filter
        (fun v => gValid (m + 1) (insert (m, a) arcs) v ∧ vAt (m + 1) v m = va' ∧ vAt (m + 1) v b = vb)) =
        ((Finset.univ : Finset (Fin (m + 1) → Bool)).filter
        (fun v => (gValid m arcs (splitL m 1 v) ∧ vAt m (splitL m 1 v) b = vb) ∧
          ((splitR m 1 v 0 = true → vAt m (splitL m 1 v) a = true) ∧ splitR m 1 v 0 = va'))) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hvm : vAt (m + 1) v m = splitR m 1 v 0 := by
        have := vAt_splitR_of_lt (m := m) (k := 1) v (j := 0) (by omega)
        simpa [vAt] using this.symm
      have hvb : vAt (m + 1) v b = vAt m (splitL m 1 v) b :=
        (vAt_splitL_of_lt v hb).symm
      have hva : vAt (m + 1) v a = vAt m (splitL m 1 v) a :=
        (vAt_splitL_of_lt v ha).symm
      constructor
      · rintro ⟨hv, h1, h2⟩
        refine ⟨⟨?_, by rw [← hvb]; exact h2⟩, ?_, by rw [← hvm]; exact h1⟩
        · intro e he h1e
          have he1 := (harcs e he).1
          have he2 := (harcs e he).2.1
          rw [vAt_splitL_of_lt v he1] at h1e
          rw [vAt_splitL_of_lt v he2]
          exact hv e (Finset.mem_insert_of_mem he) h1e
        · intro h0
          rw [← hva]
          exact hv (m, a) (Finset.mem_insert_self _ _) (by rw [hvm]; exact h0)
      · rintro ⟨⟨hv, h2⟩, hma, h1⟩
        refine ⟨?_, by rw [hvm]; exact h1, by rw [hvb]; exact h2⟩
        intro e he h1e
        simp only [Finset.mem_insert] at he
        rcases he with rfl | he
        · rw [hva]; exact hma (by rw [← hvm]; exact h1e)
        · have he1 := (harcs e he).1
          have he2 := (harcs e he).2.1
          rw [← vAt_splitL_of_lt v he1] at h1e
          rw [← vAt_splitL_of_lt v he2]
          exact hv e he h1e
    rw [hfilt]
    rw [card_filter_add m 1
      (fun v1 => gValid m arcs v1 ∧ vAt m v1 b = vb)
      (fun v1 w => (w 0 = true → vAt m v1 a = true) ∧ w 0 = va')]
    have hsum : ∀ v1 : Fin m → Bool,
        ((Finset.univ : Finset (Fin 1 → Bool)).filter
          (fun w => (w 0 = true → vAt m v1 a = true) ∧ w 0 = va')).card =
        if (va' = true → vAt m v1 a = true) then 1 else 0 :=
      fun v1 => gInc_ext_count (vAt m v1 a) va'
    simp_rw [hsum]
    rw [← Finset.card_filter]
    have hsplit : ((Finset.univ : Finset (Fin m → Bool)).filter
        (fun v1 => gValid m arcs v1 ∧ vAt m v1 b = vb)).filter
        (fun v1 => va' = true → vAt m v1 a = true) =
        ((Finset.univ : Finset (Fin m → Bool)).filter
          (fun v1 => gValid m arcs v1 ∧ vAt m v1 a = true ∧ vAt m v1 b = vb)) ∪
        (if va' = false then
          (Finset.univ : Finset (Fin m → Bool)).filter
            (fun v1 => gValid m arcs v1 ∧ vAt m v1 a = false ∧ vAt m v1 b = vb)
         else ∅) := by
      ext v1
      cases va' <;> cases h : vAt m v1 a <;>
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and,
          Finset.notMem_empty, ↓reduceIte, h, Bool.false_eq_true, Bool.true_eq_false] <;>
        tauto
    rw [hsplit, Finset.card_union_of_disjoint]
    · cases va'
      · simp only [↓reduceIte]
        have h1 := hcnt true vb
        have h0 := hcnt false vb
        unfold gCount at h1 h0
        rw [h1, h0]
        cases vb
        · simp [gMat]
        · simp [gMat]; omega
      · simp only [Bool.true_eq_false, ↓reduceIte, Finset.card_empty, add_zero]
        have h1 := hcnt true vb
        unfold gCount at h1
        rw [h1]
        cases vb <;> simp [gMat]
    · rw [Finset.disjoint_left]
      intro v1 h1 h2
      cases va'
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ↓reduceIte] at h1 h2
        rw [h1.2.1] at h2; cases h2.2.1
      · simp at h2

lemma dblNewArcs_disjoint {m a b : ℕ} {arcs : Finset (ℕ × ℕ)}
    (harcs : ∀ e ∈ arcs, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2) :
    Disjoint arcs (dblNewArcs m a b) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  have h1 := (harcs e he1).1
  have h2 := (harcs e he1).2.1
  simp only [dblNewArcs, Finset.mem_insert, Finset.mem_singleton] at he2
  rcases he2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

lemma dblNewArcs_deg {m a b : ℕ} (ha : a < m) (hb : b < m) (v : ℕ) :
    outdeg (dblNewArcs m a b) v =
      (if v = a then 1 else 0) + (if v = b then 1 else 0) +
      (if v = m then 2 else 0) + (if v = m + 1 then 1 else 0) +
      (if v = m + 2 then 1 else 0) + (if v = m + 3 then 1 else 0) +
      (if v = m + 4 then 1 else 0) ∧
    indeg (dblNewArcs m a b) v =
      (if v = a then 1 else 0) + (if v = b then 1 else 0) +
      (if v = m then 1 else 0) + (if v = m + 1 then 1 else 0) +
      (if v = m + 2 then 2 else 0) + (if v = m + 3 then 1 else 0) +
      (if v = m + 4 then 1 else 0) := by
  have h1 : (a, m) ∉ ({(m, m + 1), (m + 1, a), (b, m + 2), (m + 2, m + 3), (m + 3, b),
      (m, m + 4), (m + 4, m + 2)} : Finset (ℕ × ℕ)) := by simp; omega
  have h2 : (m, m + 1) ∉ ({(m + 1, a), (b, m + 2), (m + 2, m + 3), (m + 3, b),
      (m, m + 4), (m + 4, m + 2)} : Finset (ℕ × ℕ)) := by simp
  have h3 : (m + 1, a) ∉ ({(b, m + 2), (m + 2, m + 3), (m + 3, b),
      (m, m + 4), (m + 4, m + 2)} : Finset (ℕ × ℕ)) := by simp; omega
  have h4 : (b, m + 2) ∉ ({(m + 2, m + 3), (m + 3, b),
      (m, m + 4), (m + 4, m + 2)} : Finset (ℕ × ℕ)) := by simp; omega
  have h5 : (m + 2, m + 3) ∉ ({(m + 3, b), (m, m + 4), (m + 4, m + 2)} : Finset (ℕ × ℕ)) := by simp
  have h6 : (m + 3, b) ∉ ({(m, m + 4), (m + 4, m + 2)} : Finset (ℕ × ℕ)) := by simp
  have h7 : (m, m + 4) ∉ ({(m + 4, m + 2)} : Finset (ℕ × ℕ)) := by simp
  have hcomm : ∀ x : ℕ, (if x = v then 1 else 0) = (if v = x then 1 else 0) :=
    fun x => by by_cases h : v = x <;> simp [h, eq_comm]
  have hm2 : (if v = m then 2 else 0) = (if v = m then 1 else 0) + (if v = m then 1 else 0) := by
    split_ifs <;> rfl
  have hm2b : (if v = m + 2 then 2 else 0) = (if v = m + 2 then 1 else 0) + (if v = m + 2 then 1 else 0) := by
    split_ifs <;> rfl
  constructor
  · unfold dblNewArcs
    rw [outdeg_insert_of_not_mem h1, outdeg_insert_of_not_mem h2, outdeg_insert_of_not_mem h3,
      outdeg_insert_of_not_mem h4, outdeg_insert_of_not_mem h5, outdeg_insert_of_not_mem h6,
      outdeg_insert_of_not_mem h7, outdeg_singleton]
    simp only [hcomm, hm2]
    ring
  · unfold dblNewArcs
    rw [indeg_insert_of_not_mem h1, indeg_insert_of_not_mem h2, indeg_insert_of_not_mem h3,
      indeg_insert_of_not_mem h4, indeg_insert_of_not_mem h5, indeg_insert_of_not_mem h6,
      indeg_insert_of_not_mem h7, indeg_singleton]
    simp only [hcomm, hm2b]
    ring

abbrev dblExtPred (va vb va' vb' : Bool) (w : Fin 5 → Bool) : Prop :=
  (va = true → w 0 = true) ∧ (w 0 = true → w 1 = true) ∧ (w 1 = true → va = true) ∧
  (vb = true → w 2 = true) ∧ (w 2 = true → w 3 = true) ∧ (w 3 = true → vb = true) ∧
  (w 0 = true → w 4 = true) ∧ (w 4 = true → w 2 = true) ∧
  w 1 = va' ∧ w 3 = vb'

lemma dblExt_count (va vb va' vb' : Bool) :
    ((Finset.univ : Finset (Fin 5 → Bool)).filter (dblExtPred va vb va' vb')).card =
    if va = va' ∧ vb = vb' then gMat 2 va' vb' else 0 := by
  cases va <;> cases vb <;> cases va' <;> cases vb' <;> decide

lemma mem_dblNewBag (m a b : ℕ) (p : ℕ × Bool) :
    p ∈ dblNewBag m a b ↔
      p.1 = a ∨ p.1 = b ∨ p.1 = m ∨ p.1 = m + 1 ∨ p.1 = m + 2 ∨ p.1 = m + 3 ∨ p.1 = m + 4 := by
  simp only [dblNewBag, Finset.mem_union, mem_pairSet]
  tauto

lemma GInv_dbl {K : ℕ} {r : ℕ × ℕ × ℕ × Finset (ℕ × ℕ) × List (Finset (ℕ × Bool))}
    (hr : GInv K r) : GInv (2 * K) (gDbl r) := by
  rcases r with ⟨m, a, b, arcs, bags⟩
  dsimp only [GInv] at hr
  rcases hr with ⟨ha, hb, hab, harcs, hdeg, hoa, hia, hob, hib, hne, hblt, hbcard, hblast,
    hcovV, hcovE, hri, hlen, hcnt⟩
  dsimp only [GInv, gDbl]
  have hdisj : Disjoint arcs (dblNewArcs m a b) := dblNewArcs_disjoint harcs
  have hne' : bags ++ [dblNewBag m a b] ≠ [] := by simp
  have hnew0 : ∀ v ≥ m, outdeg arcs v = 0 ∧ indeg arcs v = 0 := fun v hv =>
    ⟨outdeg_eq_zero_of_forall (fun e he => by have := (harcs e he).1; omega),
     indeg_eq_zero_of_forall (fun e he => by have := (harcs e he).2.1; omega)⟩
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, hne', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [Finset.mem_union] at he
    rcases he with he | he
    · have := harcs e he; exact ⟨by omega, by omega, this.2.2⟩
    · simp only [dblNewArcs, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · intro v hv
    rw [outdeg_union_disjoint hdisj, indeg_union_disjoint hdisj]
    have hnd := dblNewArcs_deg ha hb v
    rw [hnd.1, hnd.2]
    by_cases hvm : v < m
    · have hd := hdeg v hvm
      by_cases hva : v = a
      · subst v; split_ifs <;> omega
      · by_cases hvb : v = b
        · subst v; split_ifs <;> omega
        · split_ifs <;> omega
    · have hz := hnew0 v (by omega)
      rw [hz.1, hz.2]
      split_ifs <;> omega
  · rw [outdeg_union_disjoint hdisj, (hnew0 (m + 1) (by omega)).1, (dblNewArcs_deg ha hb (m + 1)).1]
    split_ifs <;> omega
  · rw [indeg_union_disjoint hdisj, (hnew0 (m + 1) (by omega)).2, (dblNewArcs_deg ha hb (m + 1)).2]
    split_ifs <;> omega
  · rw [outdeg_union_disjoint hdisj, (hnew0 (m + 3) (by omega)).1, (dblNewArcs_deg ha hb (m + 3)).1]
    split_ifs <;> omega
  · rw [indeg_union_disjoint hdisj, (hnew0 (m + 3) (by omega)).2, (dblNewArcs_deg ha hb (m + 3)).2]
    split_ifs <;> omega
  · intro B hB p hp
    simp only [List.mem_append, List.mem_singleton] at hB
    rcases hB with hB | rfl
    · have := hblt B hB p hp; omega
    · rw [mem_dblNewBag] at hp; omega
  · intro B hB
    simp only [List.mem_append, List.mem_singleton] at hB
    rcases hB with hB | rfl
    · exact hbcard B hB
    · unfold dblNewBag
      have h1 := Finset.card_union_le (pairSet a ∪ pairSet b ∪ pairSet m ∪ pairSet (m + 1) ∪ pairSet (m + 2) ∪ pairSet (m + 3)) (pairSet (m + 4))
      have h2 := Finset.card_union_le (pairSet a ∪ pairSet b ∪ pairSet m ∪ pairSet (m + 1) ∪ pairSet (m + 2)) (pairSet (m + 3))
      have h3 := Finset.card_union_le (pairSet a ∪ pairSet b ∪ pairSet m ∪ pairSet (m + 1)) (pairSet (m + 2))
      have h4 := Finset.card_union_le (pairSet a ∪ pairSet b ∪ pairSet m) (pairSet (m + 1))
      have h5 := Finset.card_union_le (pairSet a ∪ pairSet b) (pairSet m)
      have h6 := Finset.card_union_le (pairSet a) (pairSet b)
      simp only [card_pairSet] at h1 h2 h3 h4 h5 h6
      omega
  · intro _
    rw [List.getLast_append_singleton]
    intro p hp
    rw [mem_dblNewBag]
    simp only [Finset.mem_union, mem_pairSet] at hp
    omega
  · intro v hv
    by_cases hvm : v < m
    · rcases hcovV v hvm with ⟨B, hB, h1, h2⟩
      exact ⟨B, List.mem_append_left _ hB, h1, h2⟩
    · refine ⟨dblNewBag m a b, by simp, ?_, ?_⟩ <;>
      · rw [mem_dblNewBag]; dsimp; omega
  · intro e he
    simp only [Finset.mem_union] at he
    rcases he with he | he
    · rcases hcovE e he with ⟨B, hB, h1, h2⟩
      exact ⟨B, List.mem_append_left _ hB, h1, h2⟩
    · refine ⟨dblNewBag m a b, by simp, ?_, ?_⟩
      · rw [mem_dblNewBag]
        simp only [dblNewArcs, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
      · rw [mem_dblNewBag]
        simp only [dblNewArcs, Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega
  · apply ListRI_append_singleton _ hne hri
    intro p hp ⟨A, hA, hpA⟩
    have hplt : p.1 < m := hblt A hA p hpA
    rw [mem_dblNewBag] at hp
    rcases hp with hpa | hpb | hm0 | hm1 | hm2 | hm3 | hm4
    · exact hblast hne (Finset.mem_union_left _ ((mem_pairSet a p).2 hpa))
    · exact hblast hne (Finset.mem_union_right _ ((mem_pairSet b p).2 hpb))
    · omega
    · omega
    · omega
    · omega
    · omega
  · simp; omega
  · intro va' vb'
    unfold gCount
    have hfilt : ((Finset.univ : Finset (Fin (m + 5) → Bool)).filter
        (fun v => gValid (m + 5) (arcs ∪ dblNewArcs m a b) v ∧
          vAt (m + 5) v (m + 1) = va' ∧ vAt (m + 5) v (m + 3) = vb')) =
        ((Finset.univ : Finset (Fin (m + 5) → Bool)).filter
        (fun v => gValid m arcs (splitL m 5 v) ∧
          dblExtPred (vAt m (splitL m 5 v) a) (vAt m (splitL m 5 v) b) va' vb' (splitR m 5 v))) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hva : vAt (m + 5) v a = vAt m (splitL m 5 v) a := (vAt_splitL_of_lt v ha).symm
      have hvb : vAt (m + 5) v b = vAt m (splitL m 5 v) b := (vAt_splitL_of_lt v hb).symm
      have hw0 : vAt (m + 5) v m = splitR m 5 v 0 := by
        simpa [vAt] using (vAt_splitR_of_lt (m := m) (k := 5) v (j := 0) (by omega)).symm
      have hw1 : vAt (m + 5) v (m + 1) = splitR m 5 v 1 := by
        simpa [vAt] using (vAt_splitR_of_lt (m := m) (k := 5) v (j := 1) (by omega)).symm
      have hw2 : vAt (m + 5) v (m + 2) = splitR m 5 v 2 := by
        simpa [vAt] using (vAt_splitR_of_lt (m := m) (k := 5) v (j := 2) (by omega)).symm
      have hw3 : vAt (m + 5) v (m + 3) = splitR m 5 v 3 := by
        simpa [vAt] using (vAt_splitR_of_lt (m := m) (k := 5) v (j := 3) (by omega)).symm
      have hw4 : vAt (m + 5) v (m + 4) = splitR m 5 v 4 := by
        simpa [vAt] using (vAt_splitR_of_lt (m := m) (k := 5) v (j := 4) (by omega)).symm
      constructor
      · rintro ⟨hv, h1, h2⟩
        refine ⟨?_, ?_⟩
        · intro e he h1e
          have he1 := (harcs e he).1
          have he2 := (harcs e he).2.1
          rw [vAt_splitL_of_lt v he1] at h1e
          rw [vAt_splitL_of_lt v he2]
          exact hv e (Finset.mem_union_left _ he) h1e
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro h; rw [← hw0]; exact hv (a, m) (Finset.mem_union_right _ (by simp [dblNewArcs])) (by rw [hva]; exact h)
          · intro h; rw [← hw1]; exact hv (m, m + 1) (Finset.mem_union_right _ (by simp [dblNewArcs])) (by rw [hw0]; exact h)
          · intro h; rw [← hva]; exact hv (m + 1, a) (Finset.mem_union_right _ (by simp [dblNewArcs])) (by rw [hw1]; exact h)
          · intro h; rw [← hw2]; exact hv (b, m + 2) (Finset.mem_union_right _ (by simp [dblNewArcs])) (by rw [hvb]; exact h)
          · intro h; rw [← hw3]; exact hv (m + 2, m + 3) (Finset.mem_union_right _ (by simp [dblNewArcs])) (by rw [hw2]; exact h)
          · intro h; rw [← hvb]; exact hv (m + 3, b) (Finset.mem_union_right _ (by simp [dblNewArcs])) (by rw [hw3]; exact h)
          · intro h; rw [← hw4]; exact hv (m, m + 4) (Finset.mem_union_right _ (by simp [dblNewArcs])) (by rw [hw0]; exact h)
          · intro h; rw [← hw2]; exact hv (m + 4, m + 2) (Finset.mem_union_right _ (by simp [dblNewArcs])) (by rw [hw4]; exact h)
          · rw [← hw1]; exact h1
          · rw [← hw3]; exact h2
      · rintro ⟨hv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
        refine ⟨?_, by rw [hw1]; exact h9, by rw [hw3]; exact h10⟩
        intro e he h1e
        simp only [Finset.mem_union] at he
        rcases he with he | he
        · have he1 := (harcs e he).1
          have he2 := (harcs e he).2.1
          rw [← vAt_splitL_of_lt v he1] at h1e
          rw [← vAt_splitL_of_lt v he2]
          exact hv e he h1e
        · simp only [dblNewArcs, Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · rw [hw0]; exact h1 (by rw [← hva]; exact h1e)
          · rw [hw1]; exact h2 (by rw [← hw0]; exact h1e)
          · rw [hva]; exact h3 (by rw [← hw1]; exact h1e)
          · rw [hw2]; exact h4 (by rw [← hvb]; exact h1e)
          · rw [hw3]; exact h5 (by rw [← hw2]; exact h1e)
          · rw [hvb]; exact h6 (by rw [← hw3]; exact h1e)
          · rw [hw4]; exact h7 (by rw [← hw0]; exact h1e)
          · rw [hw2]; exact h8 (by rw [← hw4]; exact h1e)
    rw [hfilt]
    rw [card_filter_add m 5
      (fun v1 => gValid m arcs v1)
      (fun v1 w => dblExtPred (vAt m v1 a) (vAt m v1 b) va' vb' w)]
    simp_rw [dblExt_count]
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, smul_eq_mul]
    have hcard : (((Finset.univ : Finset (Fin m → Bool)).filter (gValid m arcs)).filter
        (fun v1 => vAt m v1 a = va' ∧ vAt m v1 b = vb')).card = gCount m arcs a b va' vb' := by
      unfold gCount
      congr 1; ext v1; simp
    rw [hcard, hcnt va' vb']
    cases va' <;> cases vb'
    · simp [gMat]
    · simp [gMat]; ring
    · simp [gMat]
    · simp [gMat]

lemma GInv_gBuild : ∀ K, 1 ≤ K → GInv K (gBuild K) := by
  intro K
  induction K using Nat.strong_induction_on with
  | ind K ih =>
    intro hK
    match K with
    | 0 => omega
    | 1 => simpa [gBuild] using GInv_base
    | k + 2 =>
      have hdiv_lt : (k + 2) / 2 < k + 2 := by omega
      have hdiv_pos : 1 ≤ (k + 2) / 2 := by omega
      have hsub := ih ((k + 2) / 2) hdiv_lt hdiv_pos
      unfold gBuild
      split_ifs with heven
      · have hmul : 2 * ((k + 2) / 2) = k + 2 := by omega
        have h1 := GInv_dbl hsub
        rwa [hmul] at h1
      · have hmul : 2 * ((k + 2) / 2) + 1 = k + 2 := by omega
        have h1 := GInv_inc (GInv_dbl hsub)
        rwa [hmul] at h1

lemma gBuild_size : ∀ K, 1 ≤ K → (gBuild K).1 ≤ 6 * Nat.log2 K + 2 := by
  intro K
  induction K using Nat.strong_induction_on with
  | ind K ih =>
    intro hK
    match K with
    | 0 => omega
    | 1 => simp [gBuild, gBase]
    | k + 2 =>
      have hdiv_lt : (k + 2) / 2 < k + 2 := by omega
      have hdiv_pos : 1 ≤ (k + 2) / 2 := by omega
      have hsub := ih ((k + 2) / 2) hdiv_lt hdiv_pos
      have hlog : Nat.log2 (k + 2) = Nat.log2 ((k + 2) / 2) + 1 := by
        rw [Nat.log2_def]
        simp
      unfold gBuild
      split_ifs with heven
      · simp only [gDbl]
        omega
      · simp only [gInc, gDbl]
        omega

def extZ {n : ℕ} (z0 : Fin n → Bool) (p : ℕ) : Bool :=
  if h : p < n then z0 ⟨p, h⟩ else false

lemma extZ_fin {n : ℕ} (z0 : Fin n → Bool) (i : Fin n) : extZ z0 i.1 = z0 i := by
  simp [extZ, i.2]

abbrev validV (m : ℕ) (arcs : Finset (ℕ × ℕ)) (tag : ℕ → ℕ) (z : ℕ → Bool) (v : Fin m → Bool) : Prop :=
  (∀ i : Fin m, z (tag i.1) = false → v i = true) ∧
  (∀ e ∈ arcs, z (tag e.1) = true → z (tag e.2) = true → vAt m v e.1 = true → vAt m v e.2 = true)

abbrev matchYT {n : ℕ} (z0 y0 t0 : Fin n → Bool) : Prop :=
  (∀ i, z0 i = false → y0 i = false ∧ t0 i = true) ∧
  (∀ i, z0 i = true → t0 i = y0 i)

abbrev legalOn {n : ℕ} (E : Finset (Fin n × Fin n)) (z0 y0 : Fin n → Bool) : Prop :=
  (∀ i, z0 i = false → y0 i = false) ∧
  (∀ e ∈ E, z0 e.1 = true → z0 e.2 = true → y0 e.1 = true → y0 e.2 = true)

def fiberCount {n : ℕ} (m : ℕ) (arcs : Finset (ℕ × ℕ)) (tag : ℕ → ℕ) (tip : Fin n → ℕ)
    (z0 y0 t0 : Fin n → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin m → Bool)).filter
    (fun v => validV m arcs tag (extZ z0) v ∧
      (∀ i : Fin n, (z0 i && vAt m v i.1) = y0 i) ∧
      (∀ i : Fin n, vAt m v (tip i) = t0 i))).card

def activeTips {n : ℕ} (active : Finset (Fin n)) (tip : Fin n → ℕ) : Finset (ℕ × Bool) :=
  active.image (fun x => (tip x, true))

lemma card_activeTips_le {n : ℕ} (active : Finset (Fin n)) (tip : Fin n → ℕ) :
    (activeTips active tip).card ≤ active.card :=
  Finset.card_image_le

lemma mem_activeTips {n : ℕ} (active : Finset (Fin n)) (tip : Fin n → ℕ) (p : ℕ × Bool) :
    p ∈ activeTips active tip ↔ ∃ x ∈ active, (tip x, true) = p := by
  simp [activeTips]

lemma gWrap_ext_count {q k a b : ℕ} {gArcs : Finset (ℕ × ℕ)} (hq : 2 ≤ q)
    (hcnt : ∀ va vb : Bool, gCount k gArcs a b va vb = gMat (q - 1) va vb)
    (vf vb : Bool) :
    ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun w => gValid k gArcs w ∧ (vf = true → vAt k w a = true) ∧ vAt k w b = vb)).card =
    gMat q vf vb := by
  have hsplit : ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun w => gValid k gArcs w ∧ (vf = true → vAt k w a = true) ∧ vAt k w b = vb)) =
      ((Finset.univ : Finset (Fin k → Bool)).filter
        (fun w => gValid k gArcs w ∧ vAt k w a = true ∧ vAt k w b = vb)) ∪
      (if vf = false then
        (Finset.univ : Finset (Fin k → Bool)).filter
          (fun w => gValid k gArcs w ∧ vAt k w a = false ∧ vAt k w b = vb)
       else ∅) := by
    ext w
    cases vf <;> cases h : vAt k w a <;>
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and,
        Finset.notMem_empty, ↓reduceIte, h, Bool.false_eq_true, Bool.true_eq_false] <;>
      tauto
  rw [hsplit, Finset.card_union_of_disjoint]
  · cases vf
    · simp only [↓reduceIte]
      have h1 := hcnt true vb
      have h0 := hcnt false vb
      unfold gCount at h1 h0
      rw [h1, h0]
      cases vb
      · simp [gMat]
      · simp [gMat]; omega
    · simp only [Bool.true_eq_false, ↓reduceIte, Finset.card_empty, add_zero]
      have h1 := hcnt true vb
      unfold gCount at h1
      rw [h1]
      cases vb <;> simp [gMat]
  · rw [Finset.disjoint_left]
    intro w h1 h2
    cases vf
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ↓reduceIte] at h1 h2
      rw [h1.2.1] at h2; cases h2.2.1
    · simp at h2

lemma cycle3_ext_count (vb vt : Bool) :
    ((Finset.univ : Finset (Fin 2 → Bool)).filter
      (fun w => (vb = true → w 0 = true) ∧ (w 0 = true → w 1 = true) ∧
        (w 1 = true → vb = true) ∧ w 1 = vt)).card =
    if vb = vt then 1 else 0 := by
  cases vb <;> cases vt <;> decide

lemma cycle3_eq (vb vp vt : Bool)
    (h1 : vb = true → vp = true) (h2 : vp = true → vt = true) (h3 : vt = true → vb = true) :
    vp = vt := by
  cases vb <;> cases vp <;> cases vt <;> simp_all

abbrev handoffExtPred (k a b : ℕ) (gArcs : Finset (ℕ × ℕ)) (vf vt : Bool)
    (w : Fin (k + 2) → Bool) : Prop :=
  gValid k gArcs (splitL k 2 w) ∧
  (vf = true → vAt k (splitL k 2 w) a = true) ∧
  (vAt k (splitL k 2 w) b = true → splitR k 2 w 0 = true) ∧
  (splitR k 2 w 0 = true → splitR k 2 w 1 = true) ∧
  (splitR k 2 w 1 = true → vAt k (splitL k 2 w) b = true) ∧
  splitR k 2 w 1 = vt

lemma handoff_ext_count {q k a b : ℕ} {gArcs : Finset (ℕ × ℕ)} (hq : 2 ≤ q)
    (hcnt : ∀ va vb : Bool, gCount k gArcs a b va vb = gMat (q - 1) va vb)
    (vf vt : Bool) :
    ((Finset.univ : Finset (Fin (k + 2) → Bool)).filter
      (handoffExtPred k a b gArcs vf vt)).card = gMat q vf vt := by
  have hfilt : ((Finset.univ : Finset (Fin (k + 2) → Bool)).filter
      (handoffExtPred k a b gArcs vf vt)) =
      ((Finset.univ : Finset (Fin (k + 2) → Bool)).filter
        (fun w => (gValid k gArcs (splitL k 2 w) ∧ (vf = true → vAt k (splitL k 2 w) a = true)) ∧
          ((vAt k (splitL k 2 w) b = true → splitR k 2 w 0 = true) ∧
           (splitR k 2 w 0 = true → splitR k 2 w 1 = true) ∧
           (splitR k 2 w 1 = true → vAt k (splitL k 2 w) b = true) ∧
           splitR k 2 w 1 = vt))) := by
    ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, handoffExtPred]; tauto
  rw [hfilt]
  rw [card_filter_add k 2
    (fun w1 => gValid k gArcs w1 ∧ (vf = true → vAt k w1 a = true))
    (fun w1 w2 => (vAt k w1 b = true → w2 0 = true) ∧ (w2 0 = true → w2 1 = true) ∧
      (w2 1 = true → vAt k w1 b = true) ∧ w2 1 = vt)]
  simp_rw [cycle3_ext_count]
  rw [← Finset.card_filter]
  have hEq : ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun w1 => gValid k gArcs w1 ∧ (vf = true → vAt k w1 a = true))).filter
      (fun w1 => vAt k w1 b = vt) =
      (Finset.univ : Finset (Fin k → Bool)).filter
        (fun w1 => gValid k gArcs w1 ∧ (vf = true → vAt k w1 a = true) ∧ vAt k w1 b = vt) := by
    ext w1; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  rw [hEq]
  exact gWrap_ext_count hq hcnt vf vt

lemma card_all_true (r : ℕ) :
    ((Finset.univ : Finset (Fin r → Bool)).filter (fun w => ∀ j : Fin r, w j = true)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun _ => true, ?_⟩
  ext w
  simp [funext_iff]

def wrapArcs (f ma mb port tipNew : ℕ) : Finset (ℕ × ℕ) :=
  {(f, ma), (mb, port), (port, tipNew), (tipNew, mb)}

lemma wrapArcs_deg {f ma mb port tipNew : ℕ}
    (hfb : f < mb) (hfp : f < port) (hft : f < tipNew)
    (hbp : mb < port) (hpt : port < tipNew) (v : ℕ) :
    outdeg (wrapArcs f ma mb port tipNew) v =
      (if v = f then 1 else 0) + (if v = mb then 1 else 0) +
      (if v = port then 1 else 0) + (if v = tipNew then 1 else 0) ∧
    indeg (wrapArcs f ma mb port tipNew) v =
      (if v = ma then 1 else 0) + (if v = port then 1 else 0) +
      (if v = tipNew then 1 else 0) + (if v = mb then 1 else 0) := by
  have h1 : (f, ma) ∉ ({(mb, port), (port, tipNew), (tipNew, mb)} : Finset (ℕ × ℕ)) := by simp; omega
  have h2 : (mb, port) ∉ ({(port, tipNew), (tipNew, mb)} : Finset (ℕ × ℕ)) := by simp; omega
  have h3 : (port, tipNew) ∉ ({(tipNew, mb)} : Finset (ℕ × ℕ)) := by simp; omega
  have hcomm : ∀ x : ℕ, (if x = v then 1 else 0) = (if v = x then 1 else 0) :=
    fun x => by by_cases h : v = x <;> simp [h, eq_comm]
  constructor
  · unfold wrapArcs
    rw [outdeg_insert_of_not_mem h1, outdeg_insert_of_not_mem h2,
      outdeg_insert_of_not_mem h3, outdeg_singleton]
    simp only [hcomm]; ring
  · unfold wrapArcs
    rw [indeg_insert_of_not_mem h1, indeg_insert_of_not_mem h2,
      indeg_insert_of_not_mem h3, indeg_singleton]
    simp only [hcomm]; ring

lemma step_handoff {n w q : ℕ} (hq : 2 ≤ q)
    {seen active : Finset (Fin n)} {m : ℕ} {arcs : Finset (ℕ × ℕ)}
    {tag : ℕ → ℕ} {tip : Fin n → ℕ} {bags : List (Finset (ℕ × Bool))}
    (u : Fin n) (hu : u ∈ active)
    (extra : Finset (ℕ × Bool)) (hextra_card : extra.card ≤ 1)
    (hextra_lt : ∀ p ∈ extra, p.1 < m)
    (hnm : n ≤ m) (hactive : active ⊆ seen) (hcard : active.card ≤ w)
    (htag_init : ∀ i : Fin n, tag i.1 = i.1) (htag_lt : ∀ p < m, tag p < n)
    (htip_lt : ∀ i : Fin n, tip i < m) (htip_tag : ∀ i : Fin n, tag (tip i) = i.1)
    (htip_unseen : ∀ i : Fin n, i ∉ seen → tip i = i.1)
    (htip_ge : ∀ i : Fin n, tip i < n → tip i = i.1)
    (harcs : ∀ e ∈ arcs, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2)
    (hdeg : ∀ p < m, outdeg arcs p ≤ 2 ∧ indeg arcs p ≤ 2)
    (htip_deg : ∀ i : Fin n, outdeg arcs (tip i) ≤ 1 ∧ indeg arcs (tip i) ≤ 1)
    (hne : bags ≠ [])
    (hbags_lt : ∀ B ∈ bags, ∀ p ∈ B, p.1 < m)
    (hbags_seen : ∀ B ∈ bags, ∀ p ∈ B, p.1 < n → ∃ hi : p.1 < n, (⟨p.1, hi⟩ : Fin n) ∈ seen)
    (hbags_card : ∀ B ∈ bags, B.card ≤ w + 15)
    (hbags_ri : ListRI bags)
    (hbags_last : activeTips active tip ∪ extra ⊆ bags.getLast hne)
    (hcov_seen : ∀ i ∈ seen, ∃ B ∈ bags, (i.1, false) ∈ B ∧ (i.1, true) ∈ B)
    (hcov_new : ∀ p, n ≤ p → p < m → ∃ B ∈ bags, (p, false) ∈ B ∧ (p, true) ∈ B)
    (hcov_arcs : ∀ e ∈ arcs, ∃ B ∈ bags, (e.1, true) ∈ B ∧ (e.2, false) ∈ B) :
    ∃ (m' port tipNew : ℕ) (arcs' : Finset (ℕ × ℕ)) (tag' : ℕ → ℕ)
      (bags' : List (Finset (ℕ × Bool))),
      let tip' := Function.update tip u tipNew
      m' = m + ((gBuild (q - 1)).1 + 2) ∧
      m ≤ port ∧ port < m' ∧ m ≤ tipNew ∧ tipNew < m' ∧ port ≠ tipNew ∧
      arcs ⊆ arcs' ∧
      (∀ p < m, tag' p = tag p) ∧
      (∀ p, m ≤ p → tag' p = u.1) ∧
      (∀ i : Fin n, tag' i.1 = i.1) ∧ (∀ p < m', tag' p < n) ∧
      (∀ i : Fin n, tip' i < m') ∧ (∀ i : Fin n, tag' (tip' i) = i.1) ∧
      (∀ i : Fin n, i ∉ seen → tip' i = i.1) ∧ (∀ i : Fin n, tip' i < n → tip' i = i.1) ∧
      (∀ e ∈ arcs', e.1 < m' ∧ e.2 < m' ∧ e.1 ≠ e.2) ∧
      (∀ p < m', outdeg arcs' p ≤ 2 ∧ indeg arcs' p ≤ 2) ∧
      (∀ i : Fin n, outdeg arcs' (tip' i) ≤ 1 ∧ indeg arcs' (tip' i) ≤ 1) ∧
      outdeg arcs' port = 1 ∧ indeg arcs' port = 1 ∧
      (∀ p < m, p ≠ tip u → outdeg arcs' p = outdeg arcs p ∧ indeg arcs' p = indeg arcs p) ∧
      (∀ e ∈ arcs', e.1 < m → e.2 ≥ m → e.1 = tip u) ∧
      (∃ hne' : bags' ≠ [],
        (∀ B ∈ bags', ∀ p ∈ B, p.1 < m') ∧
        (∀ B ∈ bags', ∀ p ∈ B, p.1 < n → ∃ hi : p.1 < n, (⟨p.1, hi⟩ : Fin n) ∈ seen) ∧
        (∀ B ∈ bags', B.card ≤ w + 15) ∧
        ListRI bags' ∧
        activeTips active tip' ∪ extra ∪ pairSet port ⊆ bags'.getLast hne' ∧
        (∀ i ∈ seen, ∃ B ∈ bags', (i.1, false) ∈ B ∧ (i.1, true) ∈ B) ∧
        (∀ p, n ≤ p → p < m' → ∃ B ∈ bags', (p, false) ∈ B ∧ (p, true) ∈ B) ∧
        (∀ e ∈ arcs', ∃ B ∈ bags', (e.1, true) ∈ B ∧ (e.2, false) ∈ B) ∧
        bags'.length ≤ bags.length + ((gBuild (q - 1)).1 + 2)) ∧
      (∀ (z0 : Fin n → Bool) (v : Fin m' → Bool),
        validV m' arcs' tag' (extZ z0) v →
        vAt m' v port = vAt m' v tipNew ∧
        ∀ (hm : m ≤ m'), validV m arcs tag (extZ z0)
          (fun i => v ⟨i.1, Nat.lt_of_lt_of_le i.2 hm⟩)) ∧
      (∀ (z0 y0 t0 : Fin n → Bool),
        fiberCount m' arcs' tag' tip' z0 y0 t0 % q =
        fiberCount m arcs tag tip z0 y0 t0 % q) := by
  have hG := GInv_gBuild (q - 1) (by omega)
  generalize hg : gBuild (q - 1) = r at hG ⊢
  rcases r with ⟨k, a, b, gArcs, gBags⟩
  dsimp only [GInv] at hG
  rcases hG with ⟨ha, hb, hab, hgarcs, hgdeg, hgoa, hgia, hgob, hgib, hgne, hgblt, hgbcard,
    hgblast, hgcovV, hgcovE, hgri, hglen, hgcnt⟩
  dsimp only
  let m' := m + (k + 2)
  let port := m + k
  let tipNew := m + k + 1
  let wArcs := wrapArcs (tip u) (m + a) (m + b) port tipNew
  let arcs' := arcs ∪ shiftArcs m gArcs ∪ wArcs
  let tag' : ℕ → ℕ := fun p => if p < m then tag p else u.1
  let tip' : Fin n → ℕ := Function.update tip u tipNew
  let S : Finset (ℕ × Bool) := activeTips active tip ∪ extra
  let L1 : List (Finset (ℕ × Bool)) := (shiftBags m gBags).map (fun B => S ∪ B)
  let finalB : Finset (ℕ × Bool) :=
    S ∪ {(m + a, false)} ∪ pairSet (m + b) ∪ pairSet port ∪ pairSet tipNew
  let bags' : List (Finset (ℕ × Bool)) := bags ++ L1 ++ [finalB]
  have htu_lt : tip u < m := htip_lt u
  have hdisj1 : Disjoint arcs (shiftArcs m gArcs) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    have h1 := (harcs e he1).1
    rw [mem_shiftArcs] at he2
    rcases he2 with ⟨x, y, _, rfl⟩
    omega
  have hdisj2 : Disjoint (arcs ∪ shiftArcs m gArcs) wArcs := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [wArcs, wrapArcs, Finset.mem_insert, Finset.mem_singleton] at he2
    simp only [Finset.mem_union] at he1
    rcases he1 with he1 | he1
    · have := harcs e he1
      rcases he2 with rfl | rfl | rfl | rfl <;> omega
    · rw [mem_shiftArcs] at he1
      rcases he1 with ⟨x, y, hxy, rfl⟩
      have := hgarcs (x, y) hxy
      rcases he2 with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hwdeg := wrapArcs_deg (f := tip u) (ma := m + a) (mb := m + b) (port := port) (tipNew := tipNew)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hdeg_eq : ∀ p, outdeg arcs' p = outdeg arcs p + outdeg (shiftArcs m gArcs) p + outdeg wArcs p ∧
      indeg arcs' p = indeg arcs p + indeg (shiftArcs m gArcs) p + indeg wArcs p := by
    intro p
    exact ⟨by simp only [arcs', outdeg_union_disjoint hdisj2, outdeg_union_disjoint hdisj1],
           by simp only [arcs', indeg_union_disjoint hdisj2, indeg_union_disjoint hdisj1]⟩
  have hne' : bags' ≠ [] := by simp [bags']
  have hL1ne : L1 ≠ [] := by simp [L1, shiftBags, hgne]
  have htip_inj : ∀ x : Fin n, x ≠ u → tip x ≠ tip u := by
    intro x hxu hEq
    apply hxu; apply Fin.ext
    rw [← htip_tag x, ← htip_tag u, hEq]
  have hS_lt : ∀ p ∈ S, p.1 < m := by
    intro p hp
    simp only [S, Finset.mem_union, mem_activeTips] at hp
    rcases hp with ⟨x, _, rfl⟩ | hp
    · exact htip_lt x
    · exact hextra_lt p hp
  have hS_card : S.card ≤ w + 1 := by
    dsimp only [S]
    have h1 := Finset.card_union_le (activeTips active tip) extra
    have h2 := card_activeTips_le active tip
    omega
  have hS_seen : ∀ p ∈ S, p.1 < n → ∃ hi : p.1 < n, (⟨p.1, hi⟩ : Fin n) ∈ seen :=
    fun p hp hlt => hbags_seen (bags.getLast hne) (List.getLast_mem hne) p (hbags_last hp) hlt
  refine ⟨m', port, tipNew, arcs', tag', bags',
    rfl, by omega, by omega, by omega, by omega, by omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he; exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  · intro p hp; simp only [tag', hp, ↓reduceIte]
  · intro p hp
    dsimp only [tag']
    split_ifs
    · omega
    · rfl
  · intro i
    dsimp only [tag']
    split_ifs
    · exact htag_init i
    · omega
  · intro p hp
    dsimp only [tag']
    split_ifs with hpm
    · exact htag_lt p hpm
    · exact u.2
  · intro i
    by_cases hiu : i = u
    · subst hiu; simp only [Function.update_self]; dsimp only [tipNew, m']; omega
    · simp only [Function.update_of_ne hiu]; have := htip_lt i; dsimp only [m']; omega
  · intro i
    by_cases hiu : i = u
    · subst hiu
      simp only [Function.update_self]
      dsimp only [tag', tipNew]
      split_ifs
      · omega
      · rfl
    · simp only [Function.update_of_ne hiu]; dsimp only [tag']; split_ifs
      · exact htip_tag i
      · have := htip_lt i; omega
  · intro i hi
    have hiu : i ≠ u := fun h => hi (hactive (h ▸ hu))
    simp only [Function.update_of_ne hiu, htip_unseen i hi]
  · intro i hlt
    by_cases hiu : i = u
    · subst hiu; simp only [Function.update_self, tipNew] at hlt; omega
    · simp only [Function.update_of_ne hiu] at hlt ⊢; exact htip_ge i hlt
  · intro e he
    simp only [arcs', Finset.mem_union] at he
    rcases he with (he | he) | he
    · have := harcs e he; exact ⟨by omega, by omega, this.2.2⟩
    · rw [mem_shiftArcs] at he; rcases he with ⟨x, y, hxy, rfl⟩
      have := hgarcs (x, y) hxy; exact ⟨by omega, by omega, by omega⟩
    · simp only [wArcs, wrapArcs, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega⟩
  · intro p hp
    have hd := hdeg_eq p
    have hw := hwdeg p
    rw [hd.1, hd.2, hw.1, hw.2]
    by_cases hpm : p < m
    · rw [outdeg_shiftArcs_lt gArcs hpm, indeg_shiftArcs_lt gArcs hpm]
      by_cases hptu : p = tip u
      · subst hptu; have := htip_deg u; split_ifs <;> omega
      · have := hdeg p hpm; split_ifs <;> omega
    · have ho0 : outdeg arcs p = 0 := outdeg_eq_zero_of_forall (fun e he => by have := (harcs e he).1; omega)
      have hi0 : indeg arcs p = 0 := indeg_eq_zero_of_forall (fun e he => by have := (harcs e he).2.1; omega)
      rw [ho0, hi0]
      by_cases hpk : p < m + k
      · obtain ⟨j, rfl⟩ : ∃ j, p = m + j := ⟨p - m, by omega⟩
        have hjk : j < k := by omega
        rw [outdeg_shiftArcs_add, indeg_shiftArcs_add]
        have := hgdeg j hjk
        by_cases hja : j = a
        · subst hja; split_ifs <;> omega
        · by_cases hjb : j = b
          · subst hjb; split_ifs <;> omega
          · split_ifs <;> omega
      · have hso0 : outdeg (shiftArcs m gArcs) p = 0 := outdeg_eq_zero_of_forall (fun e he => by
          rw [mem_shiftArcs] at he; rcases he with ⟨x, y, hxy, rfl⟩; have := (hgarcs _ hxy).1; omega)
        have hsi0 : indeg (shiftArcs m gArcs) p = 0 := indeg_eq_zero_of_forall (fun e he => by
          rw [mem_shiftArcs] at he; rcases he with ⟨x, y, hxy, rfl⟩; have := (hgarcs _ hxy).2.1; omega)
        rw [hso0, hsi0]
        split_ifs <;> omega
  · intro i
    have hd := hdeg_eq (tip' i)
    have hw := hwdeg (tip' i)
    rw [hd.1, hd.2, hw.1, hw.2]
    by_cases hiu : i = u
    · subst hiu
      simp only [tip', Function.update_self]
      have ho0 : outdeg arcs tipNew = 0 := outdeg_eq_zero_of_forall (fun e he => by have := (harcs e he).1; omega)
      have hi0 : indeg arcs tipNew = 0 := indeg_eq_zero_of_forall (fun e he => by have := (harcs e he).2.1; omega)
      have hso0 : outdeg (shiftArcs m gArcs) tipNew = 0 := outdeg_eq_zero_of_forall (fun e he => by
        rw [mem_shiftArcs] at he; rcases he with ⟨x, y, hxy, rfl⟩; have := (hgarcs _ hxy).1; omega)
      have hsi0 : indeg (shiftArcs m gArcs) tipNew = 0 := indeg_eq_zero_of_forall (fun e he => by
        rw [mem_shiftArcs] at he; rcases he with ⟨x, y, hxy, rfl⟩; have := (hgarcs _ hxy).2.1; omega)
      rw [ho0, hi0, hso0, hsi0]
      split_ifs <;> omega
    · simp only [tip', Function.update_of_ne hiu]
      have hne_tu : tip i ≠ tip u := htip_inj i hiu
      have hlt_i : tip i < m := htip_lt i
      rw [outdeg_shiftArcs_lt gArcs hlt_i, indeg_shiftArcs_lt gArcs hlt_i]
      have := htip_deg i
      split_ifs <;> omega
  · have hd := (hdeg_eq port).1
    have hw := (hwdeg port).1
    have ho0 : outdeg arcs port = 0 := outdeg_eq_zero_of_forall (fun e he => by have := (harcs e he).1; omega)
    have hso0 : outdeg (shiftArcs m gArcs) port = 0 := outdeg_eq_zero_of_forall (fun e he => by
      rw [mem_shiftArcs] at he; rcases he with ⟨x, y, hxy, rfl⟩; have := (hgarcs _ hxy).1; omega)
    rw [hd, hw, ho0, hso0]; split_ifs <;> omega
  · have hd := (hdeg_eq port).2
    have hw := (hwdeg port).2
    have hi0 : indeg arcs port = 0 := indeg_eq_zero_of_forall (fun e he => by have := (harcs e he).2.1; omega)
    have hsi0 : indeg (shiftArcs m gArcs) port = 0 := indeg_eq_zero_of_forall (fun e he => by
      rw [mem_shiftArcs] at he; rcases he with ⟨x, y, hxy, rfl⟩; have := (hgarcs _ hxy).2.1; omega)
    rw [hd, hw, hi0, hsi0]; split_ifs <;> omega
  · intro p hpm hne_tu
    have hd := hdeg_eq p
    have hw := hwdeg p
    rw [hd.1, hd.2, hw.1, hw.2, outdeg_shiftArcs_lt gArcs hpm, indeg_shiftArcs_lt gArcs hpm]
    split_ifs <;> omega
  · intro e he h1 h2
    simp only [arcs', Finset.mem_union] at he
    rcases he with (he | he) | he
    · have := (harcs e he).2.1; omega
    · rw [mem_shiftArcs] at he; rcases he with ⟨x, y, _, rfl⟩; omega
    · simp only [wArcs, wrapArcs, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> dsimp <;> omega
  · refine ⟨hne', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro B hB p hp
      simp only [bags', List.mem_append, List.mem_singleton] at hB
      rcases hB with (hB | hB) | rfl
      · have := hbags_lt B hB p hp; omega
      · simp only [L1, shiftBags, List.mem_map] at hB
        rcases hB with ⟨_, ⟨G, hGmem, rfl⟩, rfl⟩
        simp only [Finset.mem_union, mem_shiftBag] at hp
        rcases hp with hp | ⟨x, s, hx, rfl⟩
        · have := hS_lt p hp; omega
        · have := hgblt G hGmem (x, s) hx; dsimp at this; omega
      · simp only [finalB, Finset.mem_union, Finset.mem_singleton, mem_pairSet] at hp
        rcases hp with (((hp | hp) | hp) | hp) | hp
        · have := hS_lt p hp; omega
        · subst hp; dsimp; omega
        · omega
        · omega
        · omega
    · intro B hB p hp hpn
      simp only [bags', List.mem_append, List.mem_singleton] at hB
      rcases hB with (hB | hB) | rfl
      · exact hbags_seen B hB p hp hpn
      · simp only [L1, shiftBags, List.mem_map] at hB
        rcases hB with ⟨_, ⟨G, _, rfl⟩, rfl⟩
        simp only [Finset.mem_union, mem_shiftBag] at hp
        rcases hp with hp | ⟨x, s, _, rfl⟩
        · exact hS_seen p hp hpn
        · dsimp at hpn; omega
      · simp only [finalB, Finset.mem_union, Finset.mem_singleton, mem_pairSet] at hp
        rcases hp with (((hp | hp) | hp) | hp) | hp
        · exact hS_seen p hp hpn
        · subst hp; dsimp at hpn; omega
        · omega
        · omega
        · omega
    · intro B hB
      simp only [bags', List.mem_append, List.mem_singleton] at hB
      rcases hB with (hB | hB) | rfl
      · exact hbags_card B hB
      · simp only [L1, shiftBags, List.mem_map] at hB
        rcases hB with ⟨_, ⟨G, hGmem, rfl⟩, rfl⟩
        have h1 := Finset.card_union_le S (shiftBag m G)
        rw [card_shiftBag] at h1
        have h2 := hgbcard G hGmem
        omega
      · unfold finalB
        have h1 := Finset.card_union_le (S ∪ {(m + a, false)} ∪ pairSet (m + b) ∪ pairSet port) (pairSet tipNew)
        have h2 := Finset.card_union_le (S ∪ {(m + a, false)} ∪ pairSet (m + b)) (pairSet port)
        have h3 := Finset.card_union_le (S ∪ {(m + a, false)}) (pairSet (m + b))
        have h4 := Finset.card_union_le S {(m + a, false)}
        simp only [card_pairSet, Finset.card_singleton] at h1 h2 h3 h4
        omega
    · have hRI_L1 : ListRI L1 := by
        apply ListRI_map_union S
        apply ListRI_map_image (fun p : ℕ × Bool => (m + p.1, p.2))
        · intro p1 p2 h; cases p1; cases p2; simp only [Prod.mk.injEq] at h
          exact Prod.ext (Nat.add_left_cancel h.1) h.2
        · exact hgri
      have hRI_1 : ListRI (bags ++ L1) := by
        apply ListRI_append hne hL1ne hbags_ri hRI_L1
        intro p ⟨A, hA, hpA⟩ ⟨B, hB, hpB⟩
        have hplt : p.1 < m := hbags_lt A hA p hpA
        simp only [L1, shiftBags, List.mem_map] at hB
        rcases hB with ⟨_, ⟨G, _, rfl⟩, rfl⟩
        simp only [Finset.mem_union, mem_shiftBag] at hpB
        have hpS : p ∈ S := by
          rcases hpB with hpS | ⟨x, s, _, rfl⟩
          · exact hpS
          · dsimp at hplt; omega
        refine ⟨hbags_last hpS, ?_⟩
        have hhead : L1.head hL1ne = S ∪ shiftBag m (gBags.head hgne) := by
          simp [L1, shiftBags, List.head_map]
        rw [hhead]
        exact Finset.mem_union_left _ hpS
      have hne1 : bags ++ L1 ≠ [] := by simp [hne]
      apply ListRI_append_singleton finalB hne1 hRI_1
      intro p hp ⟨A, hA, hpA⟩
      have hlast1 : (bags ++ L1).getLast hne1 = S ∪ shiftBag m (gBags.getLast hgne) := by
        rw [List.getLast_append_of_ne_nil _ hL1ne]
        simp [L1, shiftBags, List.getLast_map]
      rw [hlast1]
      have hAlt : p.1 < m + k := by
        simp only [List.mem_append] at hA
        rcases hA with hA | hA
        · have := hbags_lt A hA p hpA; omega
        · simp only [L1, shiftBags, List.mem_map] at hA
          rcases hA with ⟨_, ⟨G, hGmem, rfl⟩, rfl⟩
          simp only [Finset.mem_union, mem_shiftBag] at hpA
          rcases hpA with hpS | ⟨x, s, hx, rfl⟩
          · have := hS_lt p hpS; omega
          · have := hgblt G hGmem (x, s) hx; dsimp at this; omega
      simp only [finalB, Finset.mem_union, Finset.mem_singleton, mem_pairSet] at hp
      rcases hp with (((hpS | hpa) | hpb) | hpp) | hpt
      · exact Finset.mem_union_left _ hpS
      · subst hpa
        apply Finset.mem_union_right
        rw [mem_shiftBag]
        exact ⟨a, false, hgblast hgne (Finset.mem_union_left _ (by simp [pairSet])), rfl⟩
      · apply Finset.mem_union_right
        rw [mem_shiftBag]
        rcases p with ⟨px, ps⟩; dsimp at hpb; subst hpb
        exact ⟨b, ps, hgblast hgne (Finset.mem_union_right _ ((mem_pairSet b (b, ps)).2 rfl)), rfl⟩
      · omega
      · omega
    · rw [List.getLast_append_singleton]
      intro p hp
      simp only [Finset.mem_union, mem_activeTips, mem_pairSet] at hp
      simp only [finalB, Finset.mem_union, mem_pairSet]
      rcases hp with (⟨x, hx, rfl⟩ | hpe) | hpp
      · by_cases hxu : x = u
        · subst hxu
          simp only [Function.update_self]
          exact Or.inr trivial
        · simp only [Function.update_of_ne hxu]
          left; left; left; left
          exact Finset.mem_union_left _ ((mem_activeTips active tip (tip x, true)).2 ⟨x, hx, rfl⟩)
      · left; left; left; left; exact Finset.mem_union_right _ hpe
      · left; right; exact hpp
    · intro i hi
      rcases hcov_seen i hi with ⟨B, hB, h1, h2⟩
      exact ⟨B, List.mem_append_left _ (List.mem_append_left _ hB), h1, h2⟩
    · intro p hnp hpm'
      by_cases hpm : p < m
      · rcases hcov_new p hnp hpm with ⟨B, hB, h1, h2⟩
        exact ⟨B, List.mem_append_left _ (List.mem_append_left _ hB), h1, h2⟩
      · by_cases hpk : p < m + k
        · obtain ⟨j, rfl⟩ : ∃ j, p = m + j := ⟨p - m, by omega⟩
          rcases hgcovV j (by omega) with ⟨G, hGmem, h1, h2⟩
          refine ⟨S ∪ shiftBag m G, ?_, ?_, ?_⟩
          · apply List.mem_append_left; apply List.mem_append_right
            simp only [L1, shiftBags, List.mem_map]
            exact ⟨shiftBag m G, ⟨G, hGmem, rfl⟩, rfl⟩
          · exact Finset.mem_union_right _ ((mem_shiftBag m G _).2 ⟨j, false, h1, rfl⟩)
          · exact Finset.mem_union_right _ ((mem_shiftBag m G _).2 ⟨j, true, h2, rfl⟩)
        · refine ⟨finalB, by simp [bags'], ?_, ?_⟩ <;>
          · simp only [finalB, Finset.mem_union, mem_pairSet]; omega
    · intro e he
      simp only [arcs', Finset.mem_union] at he
      rcases he with (he | he) | he
      · rcases hcov_arcs e he with ⟨B, hB, h1, h2⟩
        exact ⟨B, List.mem_append_left _ (List.mem_append_left _ hB), h1, h2⟩
      · rw [mem_shiftArcs] at he; rcases he with ⟨x, y, hxy, rfl⟩
        rcases hgcovE (x, y) hxy with ⟨G, hGmem, h1, h2⟩
        refine ⟨S ∪ shiftBag m G, ?_, ?_, ?_⟩
        · apply List.mem_append_left; apply List.mem_append_right
          simp only [L1, shiftBags, List.mem_map]
          exact ⟨shiftBag m G, ⟨G, hGmem, rfl⟩, rfl⟩
        · exact Finset.mem_union_right _ ((mem_shiftBag m G _).2 ⟨x, true, h1, rfl⟩)
        · exact Finset.mem_union_right _ ((mem_shiftBag m G _).2 ⟨y, false, h2, rfl⟩)
      · have hmb_in : ∀ s, (m + b, s) ∈ finalB := fun s =>
          Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ ((mem_pairSet (m + b) (m + b, s)).2 rfl)))
        have hp_in : ∀ s, (port, s) ∈ finalB := fun s =>
          Finset.mem_union_left _ (Finset.mem_union_right _ ((mem_pairSet port (port, s)).2 rfl))
        have ht_in : ∀ s, (tipNew, s) ∈ finalB := fun s =>
          Finset.mem_union_right _ ((mem_pairSet tipNew (tipNew, s)).2 rfl)
        refine ⟨finalB, by simp [bags'], ?_, ?_⟩
        · simp only [wArcs, wrapArcs, Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl | rfl | rfl
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                ((mem_activeTips active tip _).2 ⟨u, hu, rfl⟩)))))
          · exact hmb_in true
          · exact hp_in true
          · exact ht_in true
        · simp only [wArcs, wrapArcs, Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with rfl | rfl | rfl | rfl
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton_self _))))
          · exact hp_in false
          · exact ht_in false
          · exact hmb_in false
    · simp only [bags', L1, shiftBags, List.length_append, List.length_map, List.length_singleton]
      omega
  · intro z0 v hv
    have htag_ge' : ∀ p ≥ m, extZ z0 (tag' p) = z0 u := by
      intro p hp
      dsimp only [tag']
      split_ifs
      · omega
      · exact extZ_fin z0 u
    constructor
    · cases hzu : z0 u
      · have hp_tag : extZ z0 (tag' port) = false := by rw [htag_ge' port (by omega), hzu]
        have ht_tag : extZ z0 (tag' tipNew) = false := by rw [htag_ge' tipNew (by omega), hzu]
        have hp1 : v ⟨port, by omega⟩ = true := hv.1 ⟨port, by omega⟩ hp_tag
        have ht1 : v ⟨tipNew, by omega⟩ = true := hv.1 ⟨tipNew, by omega⟩ ht_tag
        rw [vAt_of_lt v (by omega), vAt_of_lt v (by omega), hp1, ht1]
      · have hmb_tag : extZ z0 (tag' (m + b)) = true := by rw [htag_ge' (m + b) (by omega), hzu]
        have hp_tag : extZ z0 (tag' port) = true := by rw [htag_ge' port (by omega), hzu]
        have ht_tag : extZ z0 (tag' tipNew) = true := by rw [htag_ge' tipNew (by omega), hzu]
        have h1 : vAt m' v (m + b) = true → vAt m' v port = true :=
          hv.2 (m + b, port) (Finset.mem_union_right _ (by simp [wArcs, wrapArcs])) hmb_tag hp_tag
        have h2 : vAt m' v port = true → vAt m' v tipNew = true :=
          hv.2 (port, tipNew) (Finset.mem_union_right _ (by simp [wArcs, wrapArcs])) hp_tag ht_tag
        have h3 : vAt m' v tipNew = true → vAt m' v (m + b) = true :=
          hv.2 (tipNew, m + b) (Finset.mem_union_right _ (by simp [wArcs, wrapArcs])) ht_tag hmb_tag
        exact cycle3_eq _ _ _ h1 h2 h3
    · intro hm
      refine ⟨?_, ?_⟩
      · intro i hi
        have hti : tag' i.1 = tag i.1 := by simp [tag', i.2]
        exact hv.1 ⟨i.1, Nat.lt_of_lt_of_le i.2 hm⟩ (by rw [hti]; exact hi)
      · intro e he hz1 hz2 h1e
        have he1 := (harcs e he).1
        have he2 := (harcs e he).2.1
        have ht1 : tag' e.1 = tag e.1 := by simp [tag', he1]
        have ht2 : tag' e.2 = tag e.2 := by simp [tag', he2]
        have he' : e ∈ arcs' := Finset.mem_union_left _ (Finset.mem_union_left _ he)
        have h1e' : vAt m' v e.1 = true := by
          rw [vAt_of_lt _ he1] at h1e
          rw [vAt_of_lt _ (Nat.lt_of_lt_of_le he1 hm)]
          exact h1e
        have h2e' := hv.2 e he' (by rw [ht1]; exact hz1) (by rw [ht2]; exact hz2) h1e'
        rw [vAt_of_lt _ (Nat.lt_of_lt_of_le he2 hm)] at h2e'
        rw [vAt_of_lt _ he2]
        exact h2e'
  · intro z0 y0 t0
    have htag_ge' : ∀ p ≥ m, extZ z0 (tag' p) = z0 u := by
      intro p hp
      dsimp only [tag']
      split_ifs
      · omega
      · exact extZ_fin z0 u
    have htag_tu' : extZ z0 (tag' (tip u)) = z0 u := by
      dsimp only [tag']
      split_ifs
      rw [htip_tag u, extZ_fin]
    cases hzu : z0 u
    ·
      by_cases htu0 : t0 u = true
      ·
        have hfilt : ((Finset.univ : Finset (Fin m' → Bool)).filter
            (fun v => validV m' arcs' tag' (extZ z0) v ∧
              (∀ i : Fin n, (z0 i && vAt m' v i.1) = y0 i) ∧
              (∀ i : Fin n, vAt m' v (tip' i) = t0 i))) =
            ((Finset.univ : Finset (Fin m' → Bool)).filter
              (fun v => (validV m arcs tag (extZ z0) (splitL m (k + 2) v) ∧
                (∀ i : Fin n, (z0 i && vAt m (splitL m (k + 2) v) i.1) = y0 i) ∧
                (∀ i : Fin n, vAt m (splitL m (k + 2) v) (tip i) = t0 i)) ∧
                (∀ j : Fin (k + 2), splitR m (k + 2) v j = true))) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hv, hy, ht⟩
            have hallR : ∀ j : Fin (k + 2), splitR m (k + 2) v j = true := by
              intro j
              have htj : extZ z0 (tag' (m + j.1)) = false := by rw [htag_ge' (m + j.1) (by omega), hzu]
              exact hv.1 ⟨m + j.1, by omega⟩ htj
            refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hallR⟩
            · intro i hi
              have hti : tag' i.1 = tag i.1 := by simp only [tag', i.2, ↓reduceIte]
              have := hv.1 ⟨i.1, by omega⟩ (by rw [hti]; exact hi)
              simpa [splitL] using this
            · intro e he hz1 hz2 h1e
              have he1 := (harcs e he).1; have he2 := (harcs e he).2.1
              have ht1 : tag' e.1 = tag e.1 := by simp only [tag', he1, ↓reduceIte]
              have ht2 : tag' e.2 = tag e.2 := by simp only [tag', he2, ↓reduceIte]
              have h1e' : vAt m' v e.1 = true := by simpa [vAt_splitL_of_lt v he1] using h1e
              have h2e' := hv.2 e (Finset.mem_union_left _ (Finset.mem_union_left _ he))
                (by rw [ht1]; exact hz1) (by rw [ht2]; exact hz2) h1e'
              simpa [vAt_splitL_of_lt v he2] using h2e'
            · intro i
              have hi_lt : i.1 < m := by omega
              rw [vAt_splitL_of_lt v hi_lt]; exact hy i
            · intro i
              by_cases hiu : i = u
              · subst i
                have hv_tu : v ⟨tip u, by omega⟩ = true :=
                  hv.1 ⟨tip u, by omega⟩ (by rw [htag_tu', hzu])
                rw [vAt_splitL_of_lt v htu_lt, vAt_of_lt v (by omega), hv_tu, htu0]
              · rw [vAt_splitL_of_lt v (htip_lt i)]
                have := ht i; simpa [tip', Function.update_of_ne hiu] using this
          · rintro ⟨⟨hv1, hy1, ht1⟩, hallR⟩
            refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
            · intro i hi
              by_cases him : i.1 < m
              · simp only [tag', him, ↓reduceIte] at hi
                have := hv1.1 ⟨i.1, him⟩ hi
                simpa [splitL] using this
              · have := hallR ⟨i.1 - m, by omega⟩
                simp only [splitR] at this
                convert this using 2; apply Fin.ext; dsimp; omega
            · intro e he hz1 hz2 h1e
              simp only [arcs', Finset.mem_union] at he
              rcases he with (he | he) | he
              · have he1 := (harcs e he).1; have he2 := (harcs e he).2.1
                simp only [tag', he1, he2, ↓reduceIte] at hz1 hz2
                rw [← vAt_splitL_of_lt v he1] at h1e
                rw [← vAt_splitL_of_lt v he2]
                exact hv1.2 e he hz1 hz2 h1e
              · rw [mem_shiftArcs] at he; rcases he with ⟨x, y, _, rfl⟩
                rw [htag_ge' (m + x) (by omega), hzu] at hz1; cases hz1
              · simp only [wArcs, wrapArcs, Finset.mem_insert, Finset.mem_singleton] at he
                rcases he with rfl | rfl | rfl | rfl
                · rw [htag_tu', hzu] at hz1; cases hz1
                · rw [htag_ge' (m + b) (by omega), hzu] at hz1; cases hz1
                · rw [htag_ge' port (by omega), hzu] at hz1; cases hz1
                · rw [htag_ge' tipNew (by omega), hzu] at hz1; cases hz1
            · intro i
              have hi_lt : i.1 < m := by omega
              rw [← vAt_splitL_of_lt v hi_lt]; exact hy1 i
            · intro i
              by_cases hiu : i = u
              · subst i
                simp only [tip', Function.update_self]
                have h := hallR ⟨k + 1, by omega⟩
                rw [vAt_of_lt v (by dsimp only [tipNew, m']; omega), htu0]
                have heqFin : (⟨tipNew, by dsimp only [tipNew, m']; omega⟩ : Fin m') =
                    ⟨m + (k + 1), by dsimp only [m']; omega⟩ := Fin.ext (by dsimp only [tipNew]; omega)
                rw [heqFin]
                exact h
              · simp only [tip', Function.update_of_ne hiu]
                rw [← vAt_splitL_of_lt v (htip_lt i)]; exact ht1 i
        unfold fiberCount
        rw [hfilt]
        rw [card_filter_add m (k + 2)
          (fun v1 => validV m arcs tag (extZ z0) v1 ∧
            (∀ i : Fin n, (z0 i && vAt m v1 i.1) = y0 i) ∧
            (∀ i : Fin n, vAt m v1 (tip i) = t0 i))
          (fun _ w => ∀ j : Fin (k + 2), w j = true)]
        simp_rw [card_all_true]
        simp
      ·
        have htu_f : t0 u = false := by cases h : t0 u <;> simp_all
        have hLHS0 : fiberCount m' arcs' tag' tip' z0 y0 t0 = 0 := by
          unfold fiberCount
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro v _ ⟨hv, _, ht⟩
          have hlt_tn : tipNew < m' := by dsimp only [tipNew, m']; omega
          have h1 : v ⟨tipNew, hlt_tn⟩ = true :=
            hv.1 ⟨tipNew, hlt_tn⟩ (by rw [htag_ge' tipNew (by omega), hzu])
          have h2 := ht u
          simp only [tip', Function.update_self] at h2
          rw [vAt_of_lt v hlt_tn, h1, htu_f] at h2
          cases h2
        have hRHS0 : fiberCount m arcs tag tip z0 y0 t0 = 0 := by
          unfold fiberCount
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro v _ ⟨hv, _, ht⟩
          have h1 : v ⟨tip u, htu_lt⟩ = true :=
            hv.1 ⟨tip u, htu_lt⟩ (by rw [htip_tag u, extZ_fin, hzu])
          have h2 := ht u
          rw [vAt_of_lt v htu_lt, h1, htu_f] at h2
          cases h2
        rw [hLHS0, hRHS0]
    ·
      have hfilt : ((Finset.univ : Finset (Fin m' → Bool)).filter
          (fun v => validV m' arcs' tag' (extZ z0) v ∧
            (∀ i : Fin n, (z0 i && vAt m' v i.1) = y0 i) ∧
            (∀ i : Fin n, vAt m' v (tip' i) = t0 i))) =
          ((Finset.univ : Finset (Fin m' → Bool)).filter
            (fun v => (validV m arcs tag (extZ z0) (splitL m (k + 2) v) ∧
              (∀ i : Fin n, (z0 i && vAt m (splitL m (k + 2) v) i.1) = y0 i) ∧
              (∀ i : Fin n, i ≠ u → vAt m (splitL m (k + 2) v) (tip i) = t0 i)) ∧
              handoffExtPred k a b gArcs (vAt m (splitL m (k + 2) v) (tip u)) (t0 u)
                (splitR m (k + 2) v))) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have htag_ge : ∀ p ≥ m, extZ z0 (tag' p) = true := fun p hp => by rw [htag_ge' p hp, hzu]
        have htag_tu : extZ z0 (tag' (tip u)) = true := by rw [htag_tu', hzu]
        have htu_v : vAt m' v (tip u) = vAt m (splitL m (k + 2) v) (tip u) :=
          (vAt_splitL_of_lt v htu_lt).symm
        have hsplit_g : ∀ j < k, vAt m' v (m + j) = vAt k (splitL k 2 (splitR m (k + 2) v)) j := by
          intro j hj
          rw [← vAt_splitR_of_lt (m := m) (k := k + 2) v (by omega)]
          exact (vAt_splitL_of_lt (m := k) (k := 2) (splitR m (k + 2) v) hj).symm
        have hport_v : vAt m' v port = splitR k 2 (splitR m (k + 2) v) 0 := by
          have h1 : vAt m' v port = vAt (k + 2) (splitR m (k + 2) v) k :=
            (vAt_splitR_of_lt (m := m) (k := k + 2) v (by omega)).symm
          rw [h1, vAt_of_lt _ (by omega)]; rfl
        have htipN_v : vAt m' v tipNew = splitR k 2 (splitR m (k + 2) v) 1 := by
          have h1 : vAt m' v (m + (k + 1)) = vAt (k + 2) (splitR m (k + 2) v) (k + 1) :=
            (vAt_splitR_of_lt (m := m) (k := k + 2) v (by omega)).symm
          have heq : tipNew = m + (k + 1) := by dsimp only [tipNew]; omega
          rw [heq, h1, vAt_of_lt _ (by omega)]; rfl
        constructor
        · rintro ⟨hv, hy, ht⟩
          refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro i hi
            have := hv.1 ⟨i.1, by omega⟩ (by simp [tag', i.2, hi])
            simpa [splitL] using this
          · intro e he hz1 hz2 h1e
            have he1 := (harcs e he).1; have he2 := (harcs e he).2.1
            have h1e' : vAt m' v e.1 = true := by simpa [vAt_splitL_of_lt v he1] using h1e
            have h2e' := hv.2 e (Finset.mem_union_left _ (Finset.mem_union_left _ he))
              (by simp [tag', he1, hz1]) (by simp [tag', he2, hz2]) h1e'
            simpa [vAt_splitL_of_lt v he2] using h2e'
          · intro i; rw [vAt_splitL_of_lt v (by omega)]; exact hy i
          · intro i hiu
            rw [vAt_splitL_of_lt v (htip_lt i)]
            have := ht i; simpa [tip', Function.update_of_ne hiu] using this
          · intro e he h1e
            have he1 := (hgarcs e he).1; have he2 := (hgarcs e he).2.1
            have h1e' : vAt m' v (m + e.1) = true := by rw [hsplit_g e.1 he1]; exact h1e
            have h2e' := hv.2 (m + e.1, m + e.2)
              (Finset.mem_union_left _ (Finset.mem_union_right _
                ((mem_shiftArcs m gArcs _).2 ⟨e.1, e.2, he, rfl⟩)))
              (htag_ge _ (by omega)) (htag_ge _ (by omega)) h1e'
            rw [← hsplit_g e.2 he2]; exact h2e'
          · intro h1
            rw [← hsplit_g a ha]
            exact hv.2 (tip u, m + a) (Finset.mem_union_right _ (by simp [wArcs, wrapArcs]))
              htag_tu (htag_ge _ (by omega)) (by rw [htu_v]; exact h1)
          · intro h1
            rw [← hport_v]
            exact hv.2 (m + b, port) (Finset.mem_union_right _ (by simp [wArcs, wrapArcs]))
              (htag_ge _ (by omega)) (htag_ge _ (by omega)) (by rw [hsplit_g b hb]; exact h1)
          · intro h1
            rw [← htipN_v]
            exact hv.2 (port, tipNew) (Finset.mem_union_right _ (by simp [wArcs, wrapArcs]))
              (htag_ge _ (by omega)) (htag_ge _ (by omega)) (by rw [hport_v]; exact h1)
          · intro h1
            rw [← hsplit_g b hb]
            exact hv.2 (tipNew, m + b) (Finset.mem_union_right _ (by simp [wArcs, wrapArcs]))
              (htag_ge _ (by omega)) (htag_ge _ (by omega)) (by rw [htipN_v]; exact h1)
          · rw [← htipN_v]; simpa [tip', Function.update_self] using ht u
        · rintro ⟨⟨hv1, hy1, ht1⟩, hgv, hfa, hbp, hpt, htb, htu_eq⟩
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
          · intro i hi
            by_cases him : i.1 < m
            · simp only [tag', him, ↓reduceIte] at hi
              have := hv1.1 ⟨i.1, him⟩ hi
              simpa [splitL] using this
            · have := htag_ge i.1 (by omega)
              rw [this] at hi; cases hi
          · intro e he hz1 hz2 h1e
            simp only [arcs', Finset.mem_union] at he
            rcases he with (he | he) | he
            · have he1 := (harcs e he).1; have he2 := (harcs e he).2.1
              simp only [tag', he1, he2, ↓reduceIte] at hz1 hz2
              rw [← vAt_splitL_of_lt v he1] at h1e
              rw [← vAt_splitL_of_lt v he2]
              exact hv1.2 e he hz1 hz2 h1e
            · rw [mem_shiftArcs] at he; rcases he with ⟨x, y, hxy, rfl⟩
              have hx := (hgarcs (x, y) hxy).1; have hy' := (hgarcs (x, y) hxy).2.1
              rw [hsplit_g y hy']
              exact hgv (x, y) hxy (by rw [← hsplit_g x hx]; exact h1e)
            · simp only [wArcs, wrapArcs, Finset.mem_insert, Finset.mem_singleton] at he
              rcases he with rfl | rfl | rfl | rfl
              · rw [hsplit_g a ha]; exact hfa (by rw [← htu_v]; exact h1e)
              · rw [hport_v]; exact hbp (by rw [← hsplit_g b hb]; exact h1e)
              · rw [htipN_v]; exact hpt (by rw [← hport_v]; exact h1e)
              · rw [hsplit_g b hb]; exact htb (by rw [← htipN_v]; exact h1e)
          · intro i; rw [← vAt_splitL_of_lt v (by omega)]; exact hy1 i
          · intro i
            by_cases hiu : i = u
            · subst hiu; simp only [tip', Function.update_self]; rw [htipN_v]; exact htu_eq
            · simp only [tip', Function.update_of_ne hiu]
              rw [← vAt_splitL_of_lt v (htip_lt i)]; exact ht1 i hiu
      unfold fiberCount
      rw [hfilt]
      rw [card_filter_add m (k + 2)
        (fun v1 => validV m arcs tag (extZ z0) v1 ∧
          (∀ i : Fin n, (z0 i && vAt m v1 i.1) = y0 i) ∧
          (∀ i : Fin n, i ≠ u → vAt m v1 (tip i) = t0 i))
        (fun v1 w => handoffExtPred k a b gArcs (vAt m v1 (tip u)) (t0 u) w)]
      simp_rw [handoff_ext_count hq hgcnt]
      let baseS := (Finset.univ : Finset (Fin m → Bool)).filter
        (fun v1 => validV m arcs tag (extZ z0) v1 ∧
          (∀ i : Fin n, (z0 i && vAt m v1 i.1) = y0 i) ∧
          (∀ i : Fin n, i ≠ u → vAt m v1 (tip i) = t0 i))
      have hpart : baseS = baseS.filter (fun v1 => vAt m v1 (tip u) = false) ∪
          baseS.filter (fun v1 => vAt m v1 (tip u) = true) := by
        ext v1; cases h : vAt m v1 (tip u) <;> simp [h]
      have hdisjP : Disjoint (baseS.filter (fun v1 => vAt m v1 (tip u) = false))
          (baseS.filter (fun v1 => vAt m v1 (tip u) = true)) := by
        rw [Finset.disjoint_left]
        intro v1 h1 h2
        simp only [Finset.mem_filter] at h1 h2
        rw [h1.2] at h2; cases h2.2
      have hsum_split : ∑ v1 ∈ baseS, gMat q (vAt m v1 (tip u)) (t0 u) =
          (baseS.filter (fun v1 => vAt m v1 (tip u) = false)).card * gMat q false (t0 u) +
          (baseS.filter (fun v1 => vAt m v1 (tip u) = true)).card * gMat q true (t0 u) := by
        conv_lhs => rw [hpart]
        rw [Finset.sum_union hdisjP]
        congr 1
        · calc ∑ v1 ∈ baseS.filter (fun v1 => vAt m v1 (tip u) = false),
              gMat q (vAt m v1 (tip u)) (t0 u)
            = ∑ _v1 ∈ baseS.filter (fun v1 => vAt m v1 (tip u) = false), gMat q false (t0 u) :=
              Finset.sum_congr rfl (fun v1 hv1 => by rw [(Finset.mem_filter.1 hv1).2])
            _ = _ := by rw [Finset.sum_const, smul_eq_mul]
        · calc ∑ v1 ∈ baseS.filter (fun v1 => vAt m v1 (tip u) = true),
              gMat q (vAt m v1 (tip u)) (t0 u)
            = ∑ _v1 ∈ baseS.filter (fun v1 => vAt m v1 (tip u) = true), gMat q true (t0 u) :=
              Finset.sum_congr rfl (fun v1 hv1 => by rw [(Finset.mem_filter.1 hv1).2])
            _ = _ := by rw [Finset.sum_const, smul_eq_mul]
      change (∑ v1 ∈ baseS, gMat q (vAt m v1 (tip u)) (t0 u)) % q = _
      rw [hsum_split]
      have hmatch : ∀ b0 : Bool,
          (baseS.filter (fun v1 => vAt m v1 (tip u) = b0)).card =
          ((Finset.univ : Finset (Fin m → Bool)).filter
            (fun v1 => validV m arcs tag (extZ z0) v1 ∧
              (∀ i : Fin n, (z0 i && vAt m v1 i.1) = y0 i) ∧
              (∀ i : Fin n, vAt m v1 (tip i) = Function.update t0 u b0 i))).card := by
        intro b0
        congr 1; ext v1
        simp only [baseS, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨hv1, hy1, ht1⟩, hbu⟩
          refine ⟨hv1, hy1, fun i => ?_⟩
          by_cases hiu : i = u
          · subst hiu; simp [hbu]
          · simp [Function.update_of_ne hiu, ht1 i hiu]
        · rintro ⟨hv1, hy1, ht1⟩
          refine ⟨⟨hv1, hy1, fun i hiu => ?_⟩, ?_⟩
          · simpa [Function.update_of_ne hiu] using ht1 i
          · simpa using ht1 u
      rw [hmatch false, hmatch true]
      cases htu : t0 u
      · have hupd : Function.update t0 u false = t0 := by
          funext i; by_cases hiu : i = u
          · subst hiu; simp [htu]
          · simp [Function.update_of_ne hiu]
        simp only [gMat, mul_one, mul_zero, add_zero, hupd]
      · have hupd : Function.update t0 u true = t0 := by
          funext i; by_cases hiu : i = u
          · subst hiu; simp [htu]
          · simp [Function.update_of_ne hiu]
        simp only [gMat, mul_one, hupd, Nat.mul_add_mod_self_right]

def StateInv (n w q : ℕ) (D : Finset (Fin n × Fin n))
    (kSteps : ℕ) (seen active : Finset (Fin n)) (E : Finset (Fin n × Fin n))
    (m : ℕ) (arcs : Finset (ℕ × ℕ)) (tag : ℕ → ℕ) (tip : Fin n → ℕ)
    (bags : List (Finset (ℕ × Bool))) : Prop :=
  n ≤ m ∧
  m ≤ n + 2 * ((gBuild (q - 1)).1 + 2) * E.card ∧
  active ⊆ seen ∧
  active.card ≤ w ∧
  E ⊆ D ∧
  (∀ i : Fin n, tag i.1 = i.1) ∧
  (∀ p < m, tag p < n) ∧
  (∀ i : Fin n, tip i < m) ∧
  (∀ i : Fin n, tag (tip i) = i.1) ∧
  (∀ i : Fin n, i ∉ seen → tip i = i.1) ∧
  (∀ i : Fin n, tip i < n → tip i = i.1) ∧
  (∀ e ∈ arcs, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2) ∧
  (∀ p < m, outdeg arcs p ≤ 2 ∧ indeg arcs p ≤ 2) ∧
  (∀ i : Fin n, outdeg arcs (tip i) ≤ 1 ∧ indeg arcs (tip i) ≤ 1) ∧
  (bags = [] → active = ∅) ∧
  (∀ B ∈ bags, ∀ p ∈ B, p.1 < m) ∧
  (∀ B ∈ bags, ∀ p ∈ B, p.1 < n → ∃ hi : p.1 < n, (⟨p.1, hi⟩ : Fin n) ∈ seen) ∧
  (∀ B ∈ bags, B.card ≤ w + 15) ∧
  ListRI bags ∧
  (∀ hne : bags ≠ [], activeTips active tip ⊆ bags.getLast hne) ∧
  (∀ i ∈ seen, ∃ B ∈ bags, (i.1, false) ∈ B ∧ (i.1, true) ∈ B) ∧
  (∀ p, n ≤ p → p < m → ∃ B ∈ bags, (p, false) ∈ B ∧ (p, true) ∈ B) ∧
  (∀ e ∈ arcs, ∃ B ∈ bags, (e.1, true) ∈ B ∧ (e.2, false) ∈ B) ∧
  bags.length ≤ kSteps + seen.card + (m - n) ∧
  ∀ (z0 y0 t0 : Fin n → Bool),
    fiberCount m arcs tag tip z0 y0 t0 % q =
    if (matchYT z0 y0 t0 ∧ legalOn E z0 y0) then 1 else 0

lemma base_state (n w q : ℕ) (hq : 2 ≤ q) (D : Finset (Fin n × Fin n)) :
    StateInv n w q D 0 ∅ ∅ ∅ n ∅ id (fun i => i.1) [] := by
  refine ⟨le_rfl, by simp, Finset.Subset.refl _, by simp, Finset.empty_subset _,
    fun _ => rfl, fun _ hp => hp, fun i => i.2, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ he => by simp at he, fun _ _ => by simp [outdeg, indeg],
    fun _ => by simp [outdeg, indeg], fun _ => rfl,
    fun _ hB => by simp at hB, fun _ hB => by simp at hB, fun _ hB => by simp at hB,
    ListRI_nil, fun hne => (hne rfl).elim,
    fun _ hi => by simp at hi, fun _ h1 h2 => by omega,
    fun _ he => by simp at he, by simp, ?_⟩
  intro z0 y0 t0
  unfold fiberCount
  have hfilt : ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun v => validV n ∅ id (extZ z0) v ∧
        (∀ i : Fin n, (z0 i && vAt n v i.1) = y0 i) ∧
        (∀ i : Fin n, vAt n v i.1 = t0 i))) =
      if (matchYT z0 y0 t0 ∧ legalOn ∅ z0 y0) then {t0} else ∅ := by
    ext v
    split_ifs with hml
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, _, ht⟩
        funext i; simpa [vAt_of_lt v i.2] using ht i
      · rintro hvt
        subst v
        refine ⟨⟨fun i hi => ?_, fun _ he => by simp at he⟩, fun i => ?_, fun i => vAt_of_lt t0 i.2⟩
        · simp only [id, extZ_fin] at hi
          exact (hml.1.1 i hi).2
        · rw [vAt_of_lt t0 i.2]
          cases hz : z0 i
          · simp [(hml.1.1 i hz).1]
          · simp [hml.1.2 i hz]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨⟨hv1, _⟩, hy, ht⟩
      apply hml
      have hvt : v = t0 := by funext i; simpa [vAt_of_lt v i.2] using ht i
      subst v
      refine ⟨⟨fun i hz => ?_, fun i hz => ?_⟩, ⟨fun i hz => ?_, fun _ he => by simp at he⟩⟩
      · have hti : t0 i = true := hv1 i (by simpa [id, extZ_fin] using hz)
        have hyi := hy i; simp [hz] at hyi
        exact ⟨hyi, hti⟩
      · have hyi := hy i; rw [vAt_of_lt t0 i.2, hz] at hyi; simpa using hyi
      · have hyi := hy i; simp [hz] at hyi; exact hyi
  rw [hfilt]
  split_ifs
  · simp [Nat.mod_eq_of_lt (by omega : 1 < q)]
  · simp

lemma step_carrier {n w q kSteps : ℕ} {D : Finset (Fin n × Fin n)}
    {seen active cur : Finset (Fin n)} {E : Finset (Fin n × Fin n)}
    {m : ℕ} {arcs : Finset (ℕ × ℕ)} {tag : ℕ → ℕ} {tip : Fin n → ℕ}
    {bags : List (Finset (ℕ × Bool))}
    (hS : StateInv n w q D kSteps seen active E m arcs tag tip bags)
    (hcur : cur ⊆ active) :
    let bags' := bags ++ [activeTips cur tip]
    bags' ≠ [] ∧ StateInv n w q D (kSteps + 1) seen cur E m arcs tag tip bags' := by
  rcases hS with ⟨hnm, hmE, hact, hcard, hED, htag_init, htag_lt, htip_lt, htip_tag,
    htip_unseen, htip_ge, harcs, hdeg, htip_deg, hnil, hblt, hbseen, hbcard, hri,
    hblast, hcovS, hcovN, hcovE, hlen, hcnt⟩
  dsimp only
  refine ⟨by simp, hnm, hmE, Finset.Subset.trans hcur hact,
    le_trans (Finset.card_le_card hcur) hcard, hED,
    htag_init, htag_lt, htip_lt, htip_tag, htip_unseen, htip_ge, harcs, hdeg, htip_deg,
    fun h => by simp at h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcnt⟩
  · intro B hB p hp
    simp only [List.mem_append, List.mem_singleton] at hB
    rcases hB with hB | rfl
    · exact hblt B hB p hp
    · rw [mem_activeTips] at hp; rcases hp with ⟨x, _, rfl⟩; exact htip_lt x
  · intro B hB p hp hpn
    simp only [List.mem_append, List.mem_singleton] at hB
    rcases hB with hB | rfl
    · exact hbseen B hB p hp hpn
    · rw [mem_activeTips] at hp; rcases hp with ⟨x, hx, rfl⟩
      dsimp at hpn
      have htx : tip x = x.1 := htip_ge x hpn
      refine ⟨hpn, ?_⟩
      have hxfin : (⟨tip x, hpn⟩ : Fin n) = x := Fin.ext htx
      rw [hxfin]
      exact hact (hcur hx)
  · intro B hB
    simp only [List.mem_append, List.mem_singleton] at hB
    rcases hB with hB | rfl
    · exact hbcard B hB
    · have h1 := card_activeTips_le cur tip
      have h2 := Finset.card_le_card hcur
      omega
  · by_cases hne : bags = []
    · subst hne; simpa using ListRI_singleton (activeTips cur tip)
    · apply ListRI_append_singleton _ hne hri
      intro p hp _
      apply hblast hne
      rw [mem_activeTips] at hp ⊢
      rcases hp with ⟨x, hx, rfl⟩
      exact ⟨x, hcur hx, rfl⟩
  · intro _; rw [List.getLast_append_singleton]
  · intro i hi
    rcases hcovS i hi with ⟨B, hB, h1, h2⟩
    exact ⟨B, List.mem_append_left _ hB, h1, h2⟩
  · intro p h1 h2
    rcases hcovN p h1 h2 with ⟨B, hB, hb1, hb2⟩
    exact ⟨B, List.mem_append_left _ hB, hb1, hb2⟩
  · intro e he
    rcases hcovE e he with ⟨B, hB, h1, h2⟩
    exact ⟨B, List.mem_append_left _ hB, h1, h2⟩
  · simp; omega

lemma step_intro {n w q kSteps : ℕ} {D : Finset (Fin n × Fin n)}
    {seen active : Finset (Fin n)} {E : Finset (Fin n × Fin n)}
    {m : ℕ} {arcs : Finset (ℕ × ℕ)} {tag : ℕ → ℕ} {tip : Fin n → ℕ}
    {bags : List (Finset (ℕ × Bool))}
    (hS : StateInv n w q D kSteps seen active E m arcs tag tip bags)
    (hne : bags ≠ []) (i : Fin n) (hi : i ∉ seen) (hcard' : (insert i active).card ≤ w) :
    let B := activeTips (insert i active) tip ∪ pairSet i.1
    let bags' := bags ++ [B]
    bags' ≠ [] ∧
    StateInv n w q D kSteps (insert i seen) (insert i active) E m arcs tag tip bags' := by
  rcases hS with ⟨hnm, hmE, hact, hcard, hED, htag_init, htag_lt, htip_lt, htip_tag,
    htip_unseen, htip_ge, harcs, hdeg, htip_deg, hnil, hblt, hbseen, hbcard, hri,
    hblast, hcovS, hcovN, hcovE, hlen, hcnt⟩
  dsimp only
  have hti : tip i = i.1 := htip_unseen i hi
  let B := activeTips (insert i active) tip ∪ pairSet i.1
  have hB_eq : B = insert (i.1, false) (activeTips (insert i active) tip) := by
    ext ⟨px, ps⟩
    simp only [B, Finset.mem_union, Finset.mem_insert, mem_activeTips, mem_pairSet]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · cases ps
        · exact Or.inl (Prod.ext h rfl)
        · exact Or.inr ⟨i, Or.inl rfl, Prod.ext (by rw [hti, h]) rfl⟩
    · rintro (h | h)
      · exact Or.inr (by cases h; rfl)
      · exact Or.inl h
  refine ⟨by simp, hnm, hmE, Finset.insert_subset_insert i hact, hcard', hED,
    htag_init, htag_lt, htip_lt, htip_tag,
    fun j hj => htip_unseen j (fun h => hj (Finset.mem_insert_of_mem h)),
    htip_ge, harcs, hdeg, htip_deg, fun h => by simp at h,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcnt⟩
  · intro C hC p hp
    simp only [List.mem_append, List.mem_singleton] at hC
    rcases hC with hC | rfl
    · exact hblt C hC p hp
    · simp only [Finset.mem_union, mem_activeTips, mem_pairSet] at hp
      rcases hp with ⟨x, _, rfl⟩ | hpi
      · exact htip_lt x
      · omega
  · intro C hC p hp hpn
    simp only [List.mem_append, List.mem_singleton] at hC
    rcases hC with hC | rfl
    · rcases hbseen C hC p hp hpn with ⟨hi', hmem⟩
      exact ⟨hi', Finset.mem_insert_of_mem hmem⟩
    · simp only [Finset.mem_union, mem_activeTips, mem_pairSet] at hp
      rcases hp with ⟨x, hx, rfl⟩ | hpi
      · dsimp at hpn
        have htx : tip x = x.1 := htip_ge x hpn
        have hxfin : (⟨tip x, hpn⟩ : Fin n) = x := Fin.ext htx
        refine ⟨hpn, ?_⟩
        rw [hxfin]
        exact Finset.insert_subset_insert i hact hx
      · refine ⟨hpn, ?_⟩
        have hfin : (⟨p.1, hpn⟩ : Fin n) = i := Fin.ext hpi
        rw [hfin]; exact Finset.mem_insert_self _ _
  · intro C hC
    simp only [List.mem_append, List.mem_singleton] at hC
    rcases hC with hC | rfl
    · exact hbcard C hC
    · change B.card ≤ w + 15
      rw [hB_eq]
      have h1 := Finset.card_insert_le (i.1, false) (activeTips (insert i active) tip)
      have h2 := card_activeTips_le (insert i active) tip
      omega
  · apply ListRI_append_singleton _ hne hri
    intro p hp ⟨A, hA, hpA⟩
    simp only [Finset.mem_union, mem_activeTips, mem_pairSet] at hp
    rcases hp with ⟨x, hx, rfl⟩ | hpi
    · simp only [Finset.mem_insert] at hx
      rcases hx with hxi | hx
      · subst x
        have hpn : tip i < n := by rw [hti]; exact i.2
        rcases hbseen A hA (tip i, true) hpA hpn with ⟨hi', hmem⟩
        have heq : (⟨tip i, hi'⟩ : Fin n) = i := Fin.ext hti
        rw [heq] at hmem
        exact (hi hmem).elim
      · exact hblast hne ((mem_activeTips active tip _).2 ⟨x, hx, rfl⟩)
    · have hpn : p.1 < n := by rw [hpi]; exact i.2
      rcases hbseen A hA p hpA hpn with ⟨hi', hmem⟩
      have heq : (⟨p.1, hi'⟩ : Fin n) = i := Fin.ext hpi
      rw [heq] at hmem
      exact (hi hmem).elim
  · intro _
    rw [List.getLast_append_singleton]
    exact Finset.subset_union_left
  · intro j hj
    simp only [Finset.mem_insert] at hj
    rcases hj with hji | hj
    · subst j
      refine ⟨B, by simp [B], ?_, ?_⟩
      · exact Finset.mem_union_right _ (by simp [pairSet])
      · exact Finset.mem_union_right _ (by simp [pairSet])
    · rcases hcovS j hj with ⟨C, hC, h1, h2⟩
      exact ⟨C, List.mem_append_left _ hC, h1, h2⟩
  · intro p h1 h2
    rcases hcovN p h1 h2 with ⟨C, hC, hb1, hb2⟩
    exact ⟨C, List.mem_append_left _ hC, hb1, hb2⟩
  · intro e he
    rcases hcovE e he with ⟨C, hC, h1, h2⟩
    exact ⟨C, List.mem_append_left _ hC, h1, h2⟩
  · rw [Finset.card_insert_of_notMem hi]
    simp; omega

lemma step_arc {n w q kSteps : ℕ} (hq : 2 ≤ q) {D : Finset (Fin n × Fin n)}
    (hD : ∀ i : Fin n, (i, i) ∉ D)
    {seen active : Finset (Fin n)} {E : Finset (Fin n × Fin n)}
    {m : ℕ} {arcs : Finset (ℕ × ℕ)} {tag : ℕ → ℕ} {tip : Fin n → ℕ}
    {bags : List (Finset (ℕ × Bool))}
    (hS : StateInv n w q D kSteps seen active E m arcs tag tip bags)
    (hne : bags ≠ []) (u v : Fin n) (hu : u ∈ active) (hv : v ∈ active)
    (huvD : (u, v) ∈ D) (huvE : (u, v) ∉ E) :
    ∃ (m' : ℕ) (arcs' : Finset (ℕ × ℕ)) (tag' : ℕ → ℕ) (tip' : Fin n → ℕ)
      (bags' : List (Finset (ℕ × Bool))),
      bags' ≠ [] ∧
      StateInv n w q D kSteps seen active (insert (u, v) E) m' arcs' tag' tip' bags' := by
  have huv_ne : u ≠ v := by intro h; subst h; exact hD u huvD
  rcases hS with ⟨hnm, hmE, hact, hcard, hED, htag_init, htag_lt, htip_lt, htip_tag,
    htip_unseen, htip_ge, harcs, hdeg, htip_deg, hnil, hblt, hbseen, hbcard, hri,
    hblast, hcovS, hcovN, hcovE, hlen, hcnt⟩

  obtain ⟨m1, portU, tipU, arcs1, tag1, bags1,
    hm1, hportU_ge, hportU_lt, htipU_ge, htipU_lt, hptU_ne, harcs01,
    htag1_old, htag1_new, htag1_init, htag1_lt, htip1_lt, htip1_tag,
    htip1_unseen, htip1_ge, harcs1, hdeg1, htip1_deg,
    hout_pU, hin_pU, hdeg1_old, hcross1,
    ⟨hne1, hb1_lt, hb1_seen, hb1_card, hb1_ri, hb1_last, hb1_covS, hb1_covN, hb1_covE, hb1_len⟩,
    hval1, hcnt1⟩ :=
    step_handoff hq u hu ∅ (by simp) (by simp)
      hnm hact hcard htag_init htag_lt htip_lt htip_tag htip_unseen htip_ge
      harcs hdeg htip_deg hne hblt hbseen hbcard hri (by simpa using hblast hne)
      hcovS hcovN hcovE
  let tip1 := Function.update tip u tipU
  have hlast1_sub : activeTips active tip1 ∪ {(portU, true)} ⊆ bags1.getLast hne1 := by
    intro p hp
    apply hb1_last
    simp only [Finset.mem_union, Finset.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
    · exact Finset.mem_union_right _ (by simp [pairSet])

  obtain ⟨m2, portV, tipV, arcs2, tag2, bags2,
    hm2, hportV_ge, hportV_lt, htipV_ge, htipV_lt, hptV_ne, harcs12,
    htag2_old, htag2_new, htag2_init, htag2_lt, htip2_lt, htip2_tag,
    htip2_unseen, htip2_ge, harcs2, hdeg2, htip2_deg,
    hout_pV, hin_pV, hdeg2_old, hcross2,
    ⟨hne2, hb2_lt, hb2_seen, hb2_card, hb2_ri, hb2_last, hb2_covS, hb2_covN, hb2_covE, hb2_len⟩,
    hval2, hcnt2⟩ :=
    step_handoff hq v hv {(portU, true)} (by simp)
      (by intro p hp; simp at hp; subst hp; exact hportU_lt)
      (by omega) hact hcard htag1_init htag1_lt htip1_lt htip1_tag htip1_unseen htip1_ge
      harcs1 hdeg1 htip1_deg hne1 hb1_lt hb1_seen hb1_card hb1_ri hlast1_sub
      hb1_covS hb1_covN hb1_covE
  let tip2 := Function.update tip1 v tipV

  let arcs3 := insert (portU, portV) arcs2
  have htip1_v : tip1 v = tip v := Function.update_of_ne huv_ne.symm _ _
  have hportU_ne_tv : portU ≠ tip1 v := by rw [htip1_v]; have := htip_lt v; omega
  have hnotmem : (portU, portV) ∉ arcs2 := by
    intro hmem
    have := hcross2 (portU, portV) hmem hportU_lt hportV_ge
    exact hportU_ne_tv this
  have hdeg_pU2 := hdeg2_old portU hportU_lt hportU_ne_tv
  refine ⟨m2, arcs3, tag2, tip2, bags2, hne2, ?_⟩
  refine ⟨by omega, ?_, hact, hcard, Finset.insert_subset huvD hED,
    htag2_init, htag2_lt, htip2_lt, htip2_tag, htip2_unseen, htip2_ge,
    ?_, ?_, ?_, fun h => (hne2 h).elim, hb2_lt, hb2_seen, hb2_card, hb2_ri,
    ?_, hb2_covS, hb2_covN, ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem huvE]
    have hmul : 2 * ((gBuild (q - 1)).1 + 2) * (E.card + 1) =
        2 * ((gBuild (q - 1)).1 + 2) * E.card + 2 * ((gBuild (q - 1)).1 + 2) := by ring
    omega
  · intro e he
    simp only [arcs3, Finset.mem_insert] at he
    rcases he with rfl | he
    · exact ⟨by omega, hportV_lt, by omega⟩
    · exact harcs2 e he
  · intro p hp
    rw [outdeg_insert_of_not_mem hnotmem, indeg_insert_of_not_mem hnotmem]
    have hd := hdeg2 p hp
    by_cases hp1 : portU = p <;> by_cases hp2 : portV = p
    · omega
    · subst p; simp only [↓reduceIte, hp2]; omega
    · subst p; simp only [hp1, ↓reduceIte]; omega
    · simp only [hp1, hp2, ↓reduceIte]; omega
  · intro i
    rw [outdeg_insert_of_not_mem hnotmem, indeg_insert_of_not_mem hnotmem]
    have hd := htip2_deg i
    have hne1' : portU ≠ tip2 i := by
      by_cases hiv : i = v
      · subst hiv; simp only [tip2, Function.update_self]; omega
      · by_cases hiu : i = u
        · subst hiu; simp only [tip2, Function.update_of_ne hiv, tip1, Function.update_self]; exact hptU_ne
        · simp only [tip2, Function.update_of_ne hiv, tip1, Function.update_of_ne hiu]
          have := htip_lt i; omega
    have hne2' : portV ≠ tip2 i := by
      by_cases hiv : i = v
      · subst hiv; simp only [tip2, Function.update_self]; exact hptV_ne
      · by_cases hiu : i = u
        · subst hiu; simp only [tip2, Function.update_of_ne hiv, tip1, Function.update_self]; omega
        · simp only [tip2, Function.update_of_ne hiv, tip1, Function.update_of_ne hiu]
          have := htip_lt i; omega
    simp only [hne1', hne2', ↓reduceIte, add_zero]
    exact hd
  · intro hne2' p hp
    apply hb2_last
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
  · intro e he
    simp only [arcs3, Finset.mem_insert] at he
    rcases he with rfl | he
    · refine ⟨bags2.getLast hne2, List.getLast_mem hne2, ?_, ?_⟩
      · apply hb2_last
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      · apply hb2_last
        exact Finset.mem_union_right _ (by simp [pairSet])
    · exact hb2_covE e he
  · omega
  · intro z0 y0 t0
    have htag2_pU : tag2 portU = u.1 := by rw [htag2_old portU hportU_lt, htag1_new portU hportU_ge]
    have htag2_pV : tag2 portV = v.1 := htag2_new portV hportV_ge
    have htip2_u : tip2 u = tipU := by
      simp [tip2, Function.update_of_ne huv_ne, tip1]
    have htip2_v : tip2 v = tipV := by simp [tip2]
    have hfilt : ((Finset.univ : Finset (Fin m2 → Bool)).filter
        (fun w => validV m2 arcs3 tag2 (extZ z0) w ∧
          (∀ i : Fin n, (z0 i && vAt m2 w i.1) = y0 i) ∧
          (∀ i : Fin n, vAt m2 w (tip2 i) = t0 i))) =
        if (z0 u = true → z0 v = true → t0 u = true → t0 v = true) then
          (Finset.univ : Finset (Fin m2 → Bool)).filter
            (fun w => validV m2 arcs2 tag2 (extZ z0) w ∧
              (∀ i : Fin n, (z0 i && vAt m2 w i.1) = y0 i) ∧
              (∀ i : Fin n, vAt m2 w (tip2 i) = t0 i))
        else ∅ := by
      have hrel : ∀ w : Fin m2 → Bool, validV m2 arcs2 tag2 (extZ z0) w →
          vAt m2 w portU = vAt m2 w (tip2 u) ∧ vAt m2 w portV = vAt m2 w (tip2 v) := by
        intro w hw
        have h2 := hval2 z0 w hw
        have h1 := hval1 z0 (fun i : Fin m1 => w ⟨i.1, Nat.lt_of_lt_of_le i.2 (by omega)⟩)
          (h2.2 (by omega))
        constructor
        · rw [htip2_u]
          have ha1 : vAt m2 w portU = vAt m1 (fun i : Fin m1 => w ⟨i.1, Nat.lt_of_lt_of_le i.2 (by omega)⟩) portU := by
            rw [vAt_of_lt w (by omega), vAt_of_lt _ hportU_lt]
          have ha2 : vAt m2 w tipU = vAt m1 (fun i : Fin m1 => w ⟨i.1, Nat.lt_of_lt_of_le i.2 (by omega)⟩) tipU := by
            rw [vAt_of_lt w (by omega), vAt_of_lt _ htipU_lt]
          rw [ha1, ha2]; exact h1.1
        · rw [htip2_v]; exact h2.1
      ext w
      split_ifs with himp
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨hw1, hw2⟩, hy, ht⟩
          exact ⟨⟨hw1, fun e he => hw2 e (Finset.mem_insert_of_mem he)⟩, hy, ht⟩
        · rintro ⟨hw, hy, ht⟩
          refine ⟨⟨hw.1, ?_⟩, hy, ht⟩
          intro e he hz1 hz2 h1e
          simp only [arcs3, Finset.mem_insert] at he
          rcases he with rfl | he
          · have hr := hrel w hw
            rw [htag2_pU, extZ_fin] at hz1
            rw [htag2_pV, extZ_fin] at hz2
            rw [hr.1, ht u] at h1e
            rw [hr.2, ht v]
            exact himp hz1 hz2 h1e
          · exact hw.2 e he hz1 hz2 h1e
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨⟨hw1, hw2⟩, _, ht⟩
        have hw2' : validV m2 arcs2 tag2 (extZ z0) w :=
          ⟨hw1, fun e he => hw2 e (Finset.mem_insert_of_mem he)⟩
        have hr := hrel w hw2'
        apply himp
        intro hzu hzv htu
        have hstep := hw2 (portU, portV) (Finset.mem_insert_self _ _)
          (by rw [htag2_pU, extZ_fin]; exact hzu)
          (by rw [htag2_pV, extZ_fin]; exact hzv)
          (by rw [hr.1, ht u]; exact htu)
        rw [hr.2, ht v] at hstep
        exact hstep
    have hfc3 : fiberCount m2 arcs3 tag2 tip2 z0 y0 t0 =
        if (z0 u = true → z0 v = true → t0 u = true → t0 v = true) then
          fiberCount m2 arcs2 tag2 tip2 z0 y0 t0
        else 0 := by
      unfold fiberCount
      rw [hfilt]
      split_ifs <;> simp
    rw [hfc3]
    have hfc2 : fiberCount m2 arcs2 tag2 tip2 z0 y0 t0 % q =
        if (matchYT z0 y0 t0 ∧ legalOn E z0 y0) then 1 else 0 := by
      rw [hcnt2, hcnt1, hcnt]
    by_cases himp : (z0 u = true → z0 v = true → t0 u = true → t0 v = true)
    · have hlhs : (if (z0 u = true → z0 v = true → t0 u = true → t0 v = true) then
          fiberCount m2 arcs2 tag2 tip2 z0 y0 t0 else 0) =
          fiberCount m2 arcs2 tag2 tip2 z0 y0 t0 := by
        split_ifs
        rfl
      rw [hlhs, hfc2]
      by_cases hm : matchYT z0 y0 t0
      · have heqL : legalOn (insert (u, v) E) z0 y0 ↔ legalOn E z0 y0 := by
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, fun e he => h2 e (Finset.mem_insert_of_mem he)⟩
          · rintro ⟨h1, h2⟩
            refine ⟨h1, fun e he => ?_⟩
            simp only [Finset.mem_insert] at he
            rcases he with rfl | he
            · intro hzu hzv hyu
              have := himp hzu hzv (by rw [hm.2 u hzu]; exact hyu)
              rwa [hm.2 v hzv] at this
            · exact h2 e he
        split_ifs with h1 h2 h2
        · rfl
        · exact (h2 ⟨h1.1, heqL.2 h1.2⟩).elim
        · exact (h1 ⟨h2.1, heqL.1 h2.2⟩).elim
        · rfl
      · split_ifs with h1 h2 h2
        · exact (hm h1.1).elim
        · exact (hm h1.1).elim
        · exact (hm h2.1).elim
        · rfl
    · have hlhs : (if (z0 u = true → z0 v = true → t0 u = true → t0 v = true) then
          fiberCount m2 arcs2 tag2 tip2 z0 y0 t0 else 0) = 0 := by
        split_ifs
        rfl
      rw [hlhs, Nat.zero_mod]
      split_ifs with h1
      · exfalso
        apply himp
        intro hzu hzv htu
        rw [h1.1.2 u hzu] at htu
        rw [h1.1.2 v hzv]
        exact h1.2.2 (u, v) (Finset.mem_insert_self _ _) hzu hzv htu
      · rfl

def nbOf (m : ℕ) (arcs : Finset (ℕ × ℕ)) (p : Fin m × Bool) : Finset (Fin m × Bool) :=
  Finset.univ.filter (fun r =>
    (p.2 = false ∧ r.2 = true ∧ (r.1 = p.1 ∨ (r.1.1, p.1.1) ∈ arcs)) ∨
    (p.2 = true ∧ r.2 = false ∧ (p.1 = r.1 ∨ (p.1.1, r.1.1) ∈ arcs)))

lemma nbOf_bipartite (m : ℕ) (arcs : Finset (ℕ × ℕ)) (p r : Fin m × Bool)
    (hr : r ∈ nbOf m arcs p) : p.2 ≠ r.2 := by
  simp only [nbOf, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  rcases hr with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> simp [h1, h2]

lemma nbOf_not_mem (m : ℕ) (arcs : Finset (ℕ × ℕ)) (p : Fin m × Bool) :
    p ∉ nbOf m arcs p :=
  fun h => nbOf_bipartite m arcs p p h rfl

lemma nbOf_symm (m : ℕ) (arcs : Finset (ℕ × ℕ)) (p r : Fin m × Bool) :
    r ∈ nbOf m arcs p ↔ p ∈ nbOf m arcs r := by
  simp only [nbOf, Finset.mem_filter, Finset.mem_univ, true_and]
  cases p.2 <;> cases r.2 <;> simp [eq_comm]

lemma nbOf_internal (m : ℕ) (arcs : Finset (ℕ × ℕ)) (i : Fin m) :
    (i, true) ∈ nbOf m arcs (i, false) := by
  simp [nbOf]

lemma nbOf_card_le (m : ℕ) (arcs : Finset (ℕ × ℕ))
    (hdeg : ∀ p < m, outdeg arcs p ≤ 2 ∧ indeg arcs p ≤ 2) (p : Fin m × Bool) :
    (nbOf m arcs p).card ≤ 3 := by
  rcases p with ⟨i, s⟩
  cases s
  · have hsub : nbOf m arcs (i, false) ⊆
        insert (i, true) (Finset.univ.filter (fun r : Fin m × Bool => r.2 = true ∧ (r.1.1, i.1) ∈ arcs)) := by
      intro r hr
      simp only [nbOf, Finset.mem_filter, Finset.mem_univ, true_and, Bool.false_eq_true, false_and,
        or_false] at hr
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hr with ⟨hr2, hri | harc⟩
      · exact Or.inl (Prod.ext hri hr2)
      · exact Or.inr ⟨hr2, harc⟩
    have hinj : (Finset.univ.filter (fun r : Fin m × Bool => r.2 = true ∧ (r.1.1, i.1) ∈ arcs)).card ≤
        indeg arcs i.1 := by
      unfold indeg
      apply Finset.card_le_card_of_injOn (fun r => (r.1.1, i.1))
      · intro r hr
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        simp [hr.2]
      · intro r1 hr1 r2 hr2 hEq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr1 hr2
        simp only [Prod.mk.injEq] at hEq
        exact Prod.ext (Fin.ext hEq.1) (by rw [hr1.1, hr2.1])
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (i, true)
      (Finset.univ.filter (fun r : Fin m × Bool => r.2 = true ∧ (r.1.1, i.1) ∈ arcs))
    have h3 := (hdeg i.1 i.2).2
    omega
  · have hsub : nbOf m arcs (i, true) ⊆
        insert (i, false) (Finset.univ.filter (fun r : Fin m × Bool => r.2 = false ∧ (i.1, r.1.1) ∈ arcs)) := by
      intro r hr
      simp only [nbOf, Finset.mem_filter, Finset.mem_univ, true_and, Bool.true_eq_false, false_and,
        false_or] at hr
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hr with ⟨hr2, hri | harc⟩
      · exact Or.inl (Prod.ext hri.symm hr2)
      · exact Or.inr ⟨hr2, harc⟩
    have hinj : (Finset.univ.filter (fun r : Fin m × Bool => r.2 = false ∧ (i.1, r.1.1) ∈ arcs)).card ≤
        outdeg arcs i.1 := by
      unfold outdeg
      apply Finset.card_le_card_of_injOn (fun r => (i.1, r.1.1))
      · intro r hr
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        simp [hr.2]
      · intro r1 hr1 r2 hr2 hEq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr1 hr2
        simp only [Prod.mk.injEq] at hEq
        exact Prod.ext (Fin.ext hEq.2) (by rw [hr1.1, hr2.1])
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (i, false)
      (Finset.univ.filter (fun r : Fin m × Bool => r.2 = false ∧ (i.1, r.1.1) ∈ arcs))
    have h3 := (hdeg i.1 i.2).1
    omega

def physCount {n : ℕ} (m : ℕ) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (tag : Fin m → Fin n) (rd : Fin n → Fin m) (z y : Fin n → Bool) : ℕ :=
  ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter
    (fun x => ((∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
      ∀ i, xor (x (i, false)) (x (i, true)) = z (tag i)) ∧
      (fun i => z i && x (rd i, false)) = y)).card

lemma physCount_eq_sum_fiber {n m : ℕ} (arcs : Finset (ℕ × ℕ)) (tag : ℕ → ℕ)
    (htag_lt : ∀ p < m, tag p < n) (hnm : n ≤ m) (tip : Fin n → ℕ)
    (harcs : ∀ e ∈ arcs, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2)
    (z y : Fin n → Bool) :
    physCount m (nbOf m arcs) (fun i => ⟨tag i.1, htag_lt i.1 i.2⟩)
      (fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hnm⟩) z y =
    ∑ t0 : Fin n → Bool, fiberCount m arcs tag tip z y t0 := by
  let tagFin : Fin m → Fin n := fun i => ⟨tag i.1, htag_lt i.1 i.2⟩
  let rdFin : Fin n → Fin m := fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hnm⟩
  have hbij : physCount m (nbOf m arcs) tagFin rdFin z y =
      ((Finset.univ : Finset (Fin m → Bool)).filter
        (fun v => validV m arcs tag (extZ z) v ∧
          (∀ i : Fin n, (z i && vAt m v i.1) = y i))).card := by
    unfold physCount
    apply Finset.card_bij (fun x _ i => x (i, false))
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rcases hx with ⟨⟨hcov, hxor⟩, hread⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i hi
        have hzi : z (tagFin i) = false := by
          simpa [extZ, htag_lt i.1 i.2, tagFin] using hi
        have h1 := hxor i
        rw [hzi] at h1
        have h2 := hcov (i, false) (i, true) (nbOf_internal m arcs i)
        cases hf : x (i, false) <;> cases ht : x (i, true) <;> simp_all
      · intro e he hz1 hz2 h1e
        have he1 := (harcs e he).1; have he2 := (harcs e he).2.1
        let a : Fin m := ⟨e.1, he1⟩
        let b : Fin m := ⟨e.2, he2⟩
        have hza : z (tagFin a) = true := by simpa [extZ, htag_lt e.1 he1, tagFin, a] using hz1
        have hxa : x (a, false) = true := by simpa [vAt_of_lt _ he1, a] using h1e
        have hxaT : x (a, true) = false := by
          have := hxor a; rw [hza, hxa] at this; cases ht : x (a, true) <;> simp_all
        have hmem : (b, false) ∈ nbOf m arcs (a, true) := by
          simp [nbOf, a, b, he]
        have h2 := hcov (a, true) (b, false) hmem
        rw [hxaT] at h2
        have hxb : x (b, false) = true := by simpa using h2
        simpa [vAt_of_lt _ he2, b] using hxb
      · intro i
        have h := congrFun hread i
        simpa [vAt_of_lt _ (Nat.lt_of_lt_of_le i.2 hnm), rdFin] using h
    · intro x1 hx1 x2 hx2 hEq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      funext ⟨i, s⟩
      have hf : x1 (i, false) = x2 (i, false) := congrFun hEq i
      cases s
      · exact hf
      · have h1 := hx1.1.2 i
        have h2 := hx2.1.2 i
        rw [hf] at h1
        cases h0 : x2 (i, false) <;> cases h1' : x1 (i, true) <;> cases h2' : x2 (i, true) <;> simp_all
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      let x : (Fin m × Bool) → Bool :=
        fun p => if p.2 then (if z (tagFin p.1) then !(v p.1) else true) else v p.1
      refine ⟨x, ?_, by funext i; rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro p r hr
        simp only [nbOf, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        rcases p with ⟨pi, ps⟩; rcases r with ⟨ri, rs⟩
        dsimp only at hr
        rcases hr with ⟨rfl, rfl, hpi | harc⟩ | ⟨rfl, rfl, hpi | harc⟩
        · subst ri
          cases hz : z (tagFin pi)
          · exact Or.inr (by simp [x, hz])
          · cases hvpi : v pi <;> simp [x, hz, hvpi]
        · cases hzr : z (tagFin ri)
          · exact Or.inr (by simp [x, hzr])
          · cases hvr : v ri
            · exact Or.inr (by simp [x, hzr, hvr])
            · cases hzp : z (tagFin pi)
              · have := hv.1.1 pi (by simpa [extZ, htag_lt pi.1 pi.2, tagFin] using hzp)
                exact Or.inl (by simp [x, this])
              · have := hv.1.2 (ri.1, pi.1) harc
                  (by simpa [extZ, htag_lt ri.1 ri.2, tagFin] using hzr)
                  (by simpa [extZ, htag_lt pi.1 pi.2, tagFin] using hzp)
                  (by simp [vAt_of_lt v ri.2, hvr])
                rw [vAt_of_lt v pi.2] at this
                exact Or.inl (by simp [x, this])
        · subst hpi
          cases hz : z (tagFin pi)
          · exact Or.inl (by simp [x, hz])
          · cases hvpi : v pi <;> simp [x, hz, hvpi]
        · cases hzp : z (tagFin pi)
          · exact Or.inl (by simp [x, hzp])
          · cases hvp : v pi
            · exact Or.inl (by simp [x, hzp, hvp])
            · cases hzr : z (tagFin ri)
              · have := hv.1.1 ri (by simpa [extZ, htag_lt ri.1 ri.2, tagFin] using hzr)
                exact Or.inr (by simp [x, this])
              · have := hv.1.2 (pi.1, ri.1) harc
                  (by simpa [extZ, htag_lt pi.1 pi.2, tagFin] using hzp)
                  (by simpa [extZ, htag_lt ri.1 ri.2, tagFin] using hzr)
                  (by simp [vAt_of_lt v pi.2, hvp])
                rw [vAt_of_lt v ri.2] at this
                exact Or.inr (by simp [x, this])
      · intro i
        cases hz : z (tagFin i)
        · have hvi := hv.1.1 i (by simpa [extZ, htag_lt i.1 i.2, tagFin] using hz)
          simp [x, hz, hvi]
        · cases hvi : v i <;> simp [x, hz, hvi]
      · funext i
        have := hv.2 i
        simpa [x, rdFin, vAt_of_lt v (Nat.lt_of_lt_of_le i.2 hnm)] using this
  rw [hbij]
  let S := (Finset.univ : Finset (Fin m → Bool)).filter
    (fun v => validV m arcs tag (extZ z) v ∧ (∀ i : Fin n, (z i && vAt m v i.1) = y i))
  have hpart := Finset.card_eq_sum_card_fiberwise
    (f := fun (v : Fin m → Bool) (i : Fin n) => vAt m v (tip i))
    (s := S) (t := (Finset.univ : Finset (Fin n → Bool)))
    (fun _ _ => Finset.mem_univ _)
  rw [hpart]
  apply Finset.sum_congr rfl
  intro t0 _
  unfold fiberCount
  congr 1; ext v
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
  tauto

lemma sum_matchYT_mod {n q : ℕ} (hq : 2 ≤ q) (D : Finset (Fin n × Fin n)) (z y : Fin n → Bool) :
    (∑ t0 : Fin n → Bool, if (matchYT z y t0 ∧ legalOn D z y) then 1 else 0) % q =
    if legalOn D z y then 1 else 0 := by
  by_cases hl : legalOn D z y
  · let tStar : Fin n → Bool := fun i => if z i then y i else true
    have huniq : ∀ t0 : Fin n → Bool, matchYT z y t0 ↔ t0 = tStar := by
      intro t0
      constructor
      · intro hm
        funext i
        cases hz : z i
        · simp [tStar, hz, (hm.1 i hz).2]
        · simp [tStar, hz, hm.2 i hz]
      · rintro rfl
        exact ⟨fun i hz => ⟨hl.1 i hz, by simp [tStar, hz]⟩, fun i hz => by simp [tStar, hz]⟩
    have hsum : (∑ t0 : Fin n → Bool, if (matchYT z y t0 ∧ legalOn D z y) then 1 else 0) = 1 := by
      have heq : (∑ t0 : Fin n → Bool, if (matchYT z y t0 ∧ legalOn D z y) then 1 else 0) =
          ∑ t0 : Fin n → Bool, if t0 = tStar then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro t0 _
        split_ifs with h1 h2 h2
        · rfl
        · exact (h2 ((huniq t0).1 h1.1)).elim
        · exact (h1 ⟨(huniq t0).2 h2, hl⟩).elim
        · rfl
      rw [heq]
      simp
    rw [hsum]
    split_ifs
    exact Nat.mod_eq_of_lt (by omega)
  · simp [hl]

lemma nat_log2_mono {a b : ℕ} (hab : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  by_cases ha : a = 0
  · subst ha; simp
  · have hb : b ≠ 0 := by omega
    rw [Nat.le_log2 hb]
    exact le_trans (Nat.log2_self_le ha) hab

lemma L_lib_1213_core (n w q : ℕ) (D : Finset (Fin n × Fin n))
    (hq : 2 ≤ q) (hD : ∀ i : Fin n, (i, i) ∉ D)
    (hbags : ∃ (l0 : ℕ) (bagOrig : Fin l0 → Finset (Fin n)),
      l0 ≤ 2 * n + 1 ∧ (∀ t, (bagOrig t).card ≤ w) ∧
      (∀ i, ∃ t, i ∈ bagOrig t) ∧
      (∀ i j, (i, j) ∈ D → ∃ t, i ∈ bagOrig t ∧ j ∈ bagOrig t) ∧
      ∀ i s t u, s ≤ t → t ≤ u → i ∈ bagOrig s → i ∈ bagOrig u → i ∈ bagOrig t) :
    ∃ (m : ℕ) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
      (tag : Fin m → Fin n) (rd : Fin n → Fin m),
      m ≤ n + 200 * (Nat.log2 q + 2) * D.card ∧ (∀ i, tag (rd i) = i) ∧
      (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
      (∀ p r, r ∈ nb p ↔ p ∈ nb r) ∧ (∀ p, ∀ r ∈ nb p, p.2 ≠ r.2) ∧
      (∀ i, (i, true) ∈ nb (i, false)) ∧
      (∃ (l : ℕ) (bag : Fin l → Finset (Fin m × Bool)),
        l ≤ 4 * m + 1 ∧ (∀ t, (bag t).card ≤ w + 34) ∧ (∀ p, ∃ t, p ∈ bag t) ∧
        (∀ p r, r ∈ nb p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
        ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t) ∧
      ∀ (z y : Fin n → Bool),
        physCount m nb tag rd z y % q = if legalOn D z y then 1 else 0 := by
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨0, fun p => Fin.elim0 p.1, Fin.elim0, Fin.elim0, by simp, fun i => Fin.elim0 i,
      fun p => Fin.elim0 p.1, fun p => Fin.elim0 p.1, fun p => Fin.elim0 p.1,
      fun i => Fin.elim0 i, ⟨0, Fin.elim0, by omega, fun t => Fin.elim0 t,
        fun p => Fin.elim0 p.1, fun p => Fin.elim0 p.1, fun p => Fin.elim0 p.1⟩, ?_⟩
    intro z y
    have hleg : legalOn D z y := ⟨fun i => Fin.elim0 i, fun e _ => Fin.elim0 e.1⟩
    have hcard1 : physCount 0 (fun p => Fin.elim0 p.1) Fin.elim0 Fin.elim0 z y = 1 := by
      unfold physCount
      rw [Finset.card_eq_one]
      refine ⟨fun p => Fin.elim0 p.1, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro _; funext p; exact Fin.elim0 p.1
      · rintro rfl
        exact ⟨⟨fun p => Fin.elim0 p.1, fun i => Fin.elim0 i⟩, funext fun i => Fin.elim0 i⟩
    rw [hcard1]
    split_ifs
    exact Nat.mod_eq_of_lt (by omega)
  · rcases hbags with ⟨l0, bagOrig, hl0, hcard0, hcov0, hedge0, hri0⟩
    have hl0_pos : 0 < l0 := by
      rcases hcov0 ⟨0, by omega⟩ with ⟨t, _⟩
      exact Nat.lt_of_le_of_lt (Nat.zero_le t.1) t.2

    let owner : Fin n × Fin n → Fin l0 := fun e =>
      if h : e ∈ D then Classical.choose (hedge0 e.1 e.2 h) else ⟨0, hl0_pos⟩
    have howner_spec : ∀ e ∈ D, e.1 ∈ bagOrig (owner e) ∧ e.2 ∈ bagOrig (owner e) := by
      intro e he
      simp only [owner, he, ↓reduceDIte]
      exact Classical.choose_spec (hedge0 e.1 e.2 he)
    let seenOf : ℕ → Finset (Fin n) := fun k =>
      Finset.univ.filter (fun i : Fin n => ∃ t : Fin l0, t.1 < k ∧ i ∈ bagOrig t)
    let activeOf : ℕ → Finset (Fin n) := fun k =>
      if h : 0 < k then (if h2 : k - 1 < l0 then bagOrig ⟨k - 1, h2⟩ else ∅) else ∅
    let EOf : ℕ → Finset (Fin n × Fin n) := fun k =>
      D.filter (fun e => (owner e).1 < k)
    have hmain : ∀ k ≤ l0,
        ∃ (m : ℕ) (arcs : Finset (ℕ × ℕ)) (tag : ℕ → ℕ) (tip : Fin n → ℕ)
          (bags : List (Finset (ℕ × Bool))),
          StateInv n w q D k (seenOf k) (activeOf k) (EOf k) m arcs tag tip bags := by
      intro k
      induction k with
      | zero =>
        intro _
        have hs0 : seenOf 0 = ∅ := by ext i; simp [seenOf]
        have ha0 : activeOf 0 = ∅ := by simp [activeOf]
        have he0 : EOf 0 = ∅ := by ext e; simp [EOf]
        rw [hs0, ha0, he0]
        exact ⟨n, ∅, id, fun i => i.1, [], base_state n w q hq D⟩
      | succ k ih =>
        intro hk1
        have hk : k < l0 := by omega
        obtain ⟨m0, arcs0, tag0, tip0, bags0, hS0⟩ := ih (by omega)
        let tk : Fin l0 := ⟨k, hk⟩
        let cur0 : Finset (Fin n) := activeOf k ∩ bagOrig tk

        obtain ⟨hne1, hS1⟩ := step_carrier hS0 Finset.inter_subset_left
        let bags1 := bags0 ++ [activeTips cur0 tip0]

        let newVs : Finset (Fin n) := bagOrig tk \ activeOf k
        have hdisj_seen : ∀ i ∈ newVs, i ∉ seenOf k := by
          intro i hi hseen
          simp only [newVs, Finset.mem_sdiff] at hi
          simp only [seenOf, Finset.mem_filter, Finset.mem_univ, true_and] at hseen
          rcases hseen with ⟨s, hsk, his⟩
          have hkpos : 0 < k := by omega
          have hkm1 : k - 1 < l0 := by omega
          have hmem : i ∈ bagOrig ⟨k - 1, hkm1⟩ :=
            hri0 i s ⟨k - 1, hkm1⟩ tk (by change s.1 ≤ k - 1; omega)
              (by change k - 1 ≤ k; omega) his hi.1
          apply hi.2
          simp [activeOf, hkpos, hkm1, hmem]
        have hintro_fold : ∀ S : Finset (Fin n), S ⊆ newVs →
            ∃ (bagsI : List (Finset (ℕ × Bool))),
              bagsI ≠ [] ∧
              StateInv n w q D (k + 1) (seenOf k ∪ S) (cur0 ∪ S) (EOf k)
                m0 arcs0 tag0 tip0 bagsI := by
          intro S
          induction S using Finset.induction_on with
          | empty =>
            intro _
            exact ⟨bags1, hne1, by simpa using hS1⟩
          | insert i S hiS ihS =>
            intro hSub
            have hSub' : S ⊆ newVs := Finset.Subset.trans (Finset.subset_insert i S) hSub
            obtain ⟨bagsI, hneI, hSI⟩ := ihS hSub'
            have hi_new : i ∈ newVs := hSub (Finset.mem_insert_self i S)
            have hi_not_seen : i ∉ seenOf k ∪ S := by
              simp only [Finset.mem_union, not_or]
              exact ⟨hdisj_seen i hi_new, hiS⟩
            have hsub_tk : insert i (cur0 ∪ S) ⊆ bagOrig tk := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_union] at hx
              rcases hx with rfl | hx | hx
              · exact (Finset.mem_sdiff.1 hi_new).1
              · exact (Finset.mem_inter.1 hx).2
              · exact (Finset.mem_sdiff.1 (hSub' hx)).1
            have hcardI : (insert i (cur0 ∪ S)).card ≤ w :=
              le_trans (Finset.card_le_card hsub_tk) (hcard0 tk)
            obtain ⟨hneI', hSI'⟩ := step_intro hSI hneI i hi_not_seen hcardI
            have hs_eq : insert i (seenOf k ∪ S) = seenOf k ∪ insert i S := by
              ext x; simp
            have ha_eq : insert i (cur0 ∪ S) = cur0 ∪ insert i S := by
              ext x; simp
            rw [hs_eq, ha_eq] at hSI'
            rw [ha_eq] at hneI'
            exact ⟨_, hneI', hSI'⟩
        obtain ⟨bags2, hne2, hS2⟩ := hintro_fold newVs (Finset.Subset.refl _)
        have hseen_succ : seenOf k ∪ newVs = seenOf (k + 1) := by
          ext i
          simp only [Finset.mem_union, newVs, Finset.mem_sdiff, seenOf, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · rintro (⟨s, hsk, his⟩ | ⟨hitk, _⟩)
            · exact ⟨s, by omega, his⟩
            · exact ⟨tk, by simp [tk], hitk⟩
          · rintro ⟨s, hsk1, his⟩
            by_cases hsk : s.1 < k
            · exact Or.inl ⟨s, hsk, his⟩
            · have hseq : s = tk := Fin.ext (by dsimp [tk]; omega)
              subst hseq
              by_cases hia : i ∈ activeOf k
              · by_cases hkpos : 0 < k
                · have hkm1 : k - 1 < l0 := by omega
                  simp only [activeOf, hkpos, hkm1, ↓reduceDIte] at hia
                  exact Or.inl ⟨⟨k - 1, hkm1⟩, by dsimp; omega, hia⟩
                · simp [activeOf, hkpos] at hia
              · exact Or.inr ⟨his, hia⟩
        have hact_succ : cur0 ∪ newVs = activeOf (k + 1) := by
          have hk1_pos : 0 < k + 1 := by omega
          have hkm : k + 1 - 1 < l0 := by omega
          have htk_eq : (⟨k + 1 - 1, hkm⟩ : Fin l0) = tk := Fin.ext (by simp [tk])
          simp only [activeOf, hk1_pos, hkm, ↓reduceDIte, htk_eq]
          ext i
          simp only [cur0, newVs, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
          tauto
        rw [hseen_succ, hact_succ] at hS2

        let A : Finset (Fin n × Fin n) := D.filter (fun e => owner e = tk)
        have harc_fold : ∀ T : Finset (Fin n × Fin n), T ⊆ A →
            ∃ (mA : ℕ) (arcsA : Finset (ℕ × ℕ)) (tagA : ℕ → ℕ) (tipA : Fin n → ℕ)
              (bagsA : List (Finset (ℕ × Bool))),
              bagsA ≠ [] ∧
              StateInv n w q D (k + 1) (seenOf (k + 1)) (activeOf (k + 1)) (EOf k ∪ T)
                mA arcsA tagA tipA bagsA := by
          intro T
          induction T using Finset.induction_on with
          | empty =>
            intro _
            exact ⟨m0, arcs0, tag0, tip0, bags2, hne2, by simpa using hS2⟩
          | insert e T heT ihT =>
            intro hSub
            have hSub' : T ⊆ A := Finset.Subset.trans (Finset.subset_insert e T) hSub
            obtain ⟨mA, arcsA, tagA, tipA, bagsA, hneA, hSA⟩ := ihT hSub'
            have heA : e ∈ A := hSub (Finset.mem_insert_self e T)
            have heD : e ∈ D := (Finset.mem_filter.1 heA).1
            have hown : owner e = tk := (Finset.mem_filter.1 heA).2
            have hspec := howner_spec e heD
            rw [hown] at hspec
            have hact_eq : activeOf (k + 1) = bagOrig tk := by
              have h1 : 0 < k + 1 := by omega
              have h2 : k + 1 - 1 < l0 := by omega
              simp only [activeOf, h1, h2, ↓reduceDIte, tk]
              congr 1
            have he1_act : e.1 ∈ activeOf (k + 1) := by rw [hact_eq]; exact hspec.1
            have he2_act : e.2 ∈ activeOf (k + 1) := by rw [hact_eq]; exact hspec.2
            have he_not_E : e ∉ EOf k ∪ T := by
              simp only [Finset.mem_union, not_or]
              refine ⟨?_, heT⟩
              simp only [EOf, Finset.mem_filter, hown, tk]
              omega
            rcases e with ⟨u, v⟩
            obtain ⟨mA', arcsA', tagA', tipA', bagsA', hneA', hSA'⟩ :=
              step_arc hq hD hSA hneA u v he1_act he2_act heD he_not_E
            refine ⟨mA', arcsA', tagA', tipA', bagsA', hneA', ?_⟩
            have heqE : insert (u, v) (EOf k ∪ T) = EOf k ∪ insert (u, v) T := by
              ext x; simp
            rwa [heqE] at hSA'
        obtain ⟨mF, arcsF, tagF, tipF, bagsF, _, hSF⟩ := harc_fold A (Finset.Subset.refl _)
        have hE_succ : EOf k ∪ A = EOf (k + 1) := by
          ext e
          simp only [Finset.mem_union, EOf, A, Finset.mem_filter]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨h1, by omega⟩
            · exact ⟨h1, by rw [h2]; simp [tk]⟩
          · rintro ⟨h1, h2⟩
            by_cases hlt : (owner e).1 < k
            · exact Or.inl ⟨h1, hlt⟩
            · exact Or.inr ⟨h1, Fin.ext (by dsimp [tk]; omega)⟩
        rw [hE_succ] at hSF
        exact ⟨mF, arcsF, tagF, tipF, bagsF, hSF⟩
    obtain ⟨m, arcs, tag, tip, bags, hS⟩ := hmain l0 le_rfl
    have hseen_univ : seenOf l0 = Finset.univ := by
      ext i
      simp only [seenOf, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rcases hcov0 i with ⟨t, ht⟩
      exact ⟨t, t.2, ht⟩
    have hE_D : EOf l0 = D := by
      ext e
      simp only [EOf, Finset.mem_filter, and_iff_left_iff_imp]
      intro _; exact (owner e).2
    rw [hseen_univ, hE_D] at hS
    rcases hS with ⟨hnm, hmE, _, _, _, htag_init, htag_lt, _, _, _, _,
      harcs, hdeg, _, _, hblt, _, hbcard, hri, _, hcovS, hcovN, hcovE, hlen, hcnt⟩
    let tagFin : Fin m → Fin n := fun i => ⟨tag i.1, htag_lt i.1 i.2⟩
    let rdFin : Fin n → Fin m := fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hnm⟩
    let nb := nbOf m arcs
    let bagFin : Fin bags.length → Finset (Fin m × Bool) :=
      fun t => Finset.univ.filter (fun p => (p.1.1, p.2) ∈ bags[t.1])
    refine ⟨m, nb, tagFin, rdFin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hgs := gBuild_size (q - 1) (by omega)
      have hlog : Nat.log2 (q - 1) ≤ Nat.log2 q := nat_log2_mono (by omega)
      have hcoef : 2 * ((gBuild (q - 1)).1 + 2) ≤ 200 * (Nat.log2 q + 2) := by omega
      exact le_trans hmE (Nat.add_le_add_left (Nat.mul_le_mul_right D.card hcoef) n)
    · intro i; exact Fin.ext (htag_init i)
    · intro p; exact ⟨nbOf_not_mem m arcs p, nbOf_card_le m arcs hdeg p⟩
    · intro p r; exact nbOf_symm m arcs p r
    · intro p r hr; exact nbOf_bipartite m arcs p r hr
    · intro i; exact nbOf_internal m arcs i
    · refine ⟨bags.length, bagFin, ?_, ?_, ?_, ?_, ?_⟩
      · have hcardU : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
        rw [hcardU] at hlen
        omega
      · intro t
        have hle : (bagFin t).card ≤ bags[t.1].card := by
          apply Finset.card_le_card_of_injOn (fun p : Fin m × Bool => (p.1.1, p.2))
          · intro p hp
            simp only [bagFin, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
            exact hp
          · intro p1 _ p2 _ hEq
            simp only [Prod.mk.injEq] at hEq
            exact Prod.ext (Fin.ext hEq.1) hEq.2
        have hbc := hbcard bags[t.1] (List.getElem_mem t.2)
        omega
      · intro ⟨i, s⟩
        have hcov : ∃ B ∈ bags, (i.1, false) ∈ B ∧ (i.1, true) ∈ B := by
          by_cases hin : i.1 < n
          · exact hcovS ⟨i.1, hin⟩ (Finset.mem_univ _)
          · exact hcovN i.1 (by omega) i.2
        rcases hcov with ⟨B, hB, hF, hT⟩
        rcases List.getElem_of_mem hB with ⟨idx, hidx, rfl⟩
        refine ⟨⟨idx, hidx⟩, ?_⟩
        simp only [bagFin, Finset.mem_filter, Finset.mem_univ, true_and]
        cases s <;> assumption
      · intro p r hr
        simp only [nb, nbOf, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        rcases p with ⟨pi, ps⟩; rcases r with ⟨ri, rs⟩
        dsimp only at hr
        rcases hr with ⟨rfl, rfl, hpi | harc⟩ | ⟨rfl, rfl, hpi | harc⟩
        · subst ri
          have hcov : ∃ B ∈ bags, (pi.1, false) ∈ B ∧ (pi.1, true) ∈ B := by
            by_cases hin : pi.1 < n
            · exact hcovS ⟨pi.1, hin⟩ (Finset.mem_univ _)
            · exact hcovN pi.1 (by omega) pi.2
          rcases hcov with ⟨B, hB, hF, hT⟩
          rcases List.getElem_of_mem hB with ⟨idx, hidx, rfl⟩
          exact ⟨⟨idx, hidx⟩, by simp [bagFin, hF], by simp [bagFin, hT]⟩
        · rcases hcovE (ri.1, pi.1) harc with ⟨B, hB, h1, h2⟩
          rcases List.getElem_of_mem hB with ⟨idx, hidx, rfl⟩
          exact ⟨⟨idx, hidx⟩, by simp [bagFin, h2], by simp [bagFin, h1]⟩
        · subst ri
          have hcov : ∃ B ∈ bags, (pi.1, false) ∈ B ∧ (pi.1, true) ∈ B := by
            by_cases hin : pi.1 < n
            · exact hcovS ⟨pi.1, hin⟩ (Finset.mem_univ _)
            · exact hcovN pi.1 (by omega) pi.2
          rcases hcov with ⟨B, hB, hF, hT⟩
          rcases List.getElem_of_mem hB with ⟨idx, hidx, rfl⟩
          exact ⟨⟨idx, hidx⟩, by simp [bagFin, hT], by simp [bagFin, hF]⟩
        · rcases hcovE (pi.1, ri.1) harc with ⟨B, hB, h1, h2⟩
          rcases List.getElem_of_mem hB with ⟨idx, hidx, rfl⟩
          exact ⟨⟨idx, hidx⟩, by simp [bagFin, h1], by simp [bagFin, h2]⟩
      · intro p s t u hst htu hps hpu
        simp only [bagFin, Finset.mem_filter, Finset.mem_univ, true_and] at hps hpu ⊢
        exact hri (p.1.1, p.2) s.1 t.1 u.1 hst htu s.2 t.2 u.2 hps hpu
    · intro z y
      rw [physCount_eq_sum_fiber arcs tag htag_lt hnm tip harcs z y]
      rw [Finset.sum_nat_mod]
      have hsum_eq :
          (∑ t0 : Fin n → Bool, fiberCount m arcs tag tip z y t0 % q) =
          ∑ t0 : Fin n → Bool, if (matchYT z y t0 ∧ legalOn D z y) then 1 else 0 :=
        Finset.sum_congr rfl (fun t0 _ => hcnt z y t0)
      rw [hsum_eq]
      exact sum_matchYT_mod hq D z y

end PEqualNP.Outside.L_lib_1213_aux

theorem PEqualNP.Outside.L_lib_1213 :
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let bags := fun (v : Nat) (edge : Fin v → Fin v → Prop) (w : Nat) =>
    ∃ (l : Nat) (bag : Fin l → Finset (Fin v)),
      l ≤ 2*v+1 ∧ (∀ t, (bag t).card ≤ w) ∧
      (∀ i, ∃ t, i ∈ bag t) ∧
      (∀ i j, edge i j → ∃ t, i ∈ bag t ∧ j ∈ bag t) ∧
      ∀ i s t u, s ≤ t → t ≤ u → i ∈ bag s → i ∈ bag u → i ∈ bag t
  ∀ (n w q : Nat) (D : Finset (Fin n × Fin n)), 2 ≤ q → (∀ i, (i,i) ∉ D) →
    bags n (fun i j => (i,j) ∈ D) w →
    ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
      (tag : Fin m → Fin n) (rd : Fin n → Fin m),
      m ≤ n+200*(Nat.log2 q+2)*D.card ∧ (∀ i, tag (rd i) = i) ∧
      (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
      (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧ (∀ p, ∀ q ∈ nb p, p.2 ≠ q.2) ∧
      (∀ i, (i,true) ∈ nb (i,false)) ∧
      (∃ (l : Nat) (bag : Fin l → Finset (Fin m × Bool)),
        l ≤ 4*m+1 ∧ (∀ t, (bag t).card ≤ w+34) ∧ (∀ p, ∃ t, p ∈ bag t) ∧
        (∀ p r, r ∈ nb p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
        ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t) ∧
      ∀ z : Fin n → Bool,
        let physical := fun (x : (Fin m × Bool) → Bool) =>
          (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
          ∀ i, xor (x (i,false)) (x (i,true)) = z (tag i)
        let legal := fun (y : Fin n → Bool) =>
          (∀ i, z i = false → y i = false) ∧
          ∀ i j, (i,j) ∈ D → z i = true → z j = true → y i = true → y j = true
        let readout := fun (x : (Fin m × Bool) → Bool) i => z i && x (rd i,false)
        ∀ y : Fin n → Bool,
          ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter
            (fun x => physical x ∧ readout x = y)).card % q = if legal y then 1 else 0 := by
  dsimp only
  intro n w q D hq hD hbags
  rcases PEqualNP.Outside.L_lib_1213_aux.L_lib_1213_core n w q D hq hD hbags with
    ⟨m, nb, tag, rd, hm, htr, hdeg, hsym, hbip, hint, hpd, hcnt⟩
  refine ⟨m, nb, tag, rd, hm, htr, hdeg, hsym, hbip, hint, hpd, ?_⟩
  intro z y
  have h := hcnt z y
  have hleg_iff :
      PEqualNP.Outside.L_lib_1213_aux.legalOn D z y ↔
      ((∀ i, z i = false → y i = false) ∧
        ∀ i j, (i, j) ∈ D → z i = true → z j = true → y i = true → y j = true) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i j hij => h2 (i, j) hij⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun e he => h2 e.1 e.2 he⟩
  calc _ = PEqualNP.Outside.L_lib_1213_aux.physCount m nb tag rd z y % q := by
        congr 1
        unfold PEqualNP.Outside.L_lib_1213_aux.physCount
        congr 1
        ext x
        simp
    _ = if PEqualNP.Outside.L_lib_1213_aux.legalOn D z y then 1 else 0 := h
    _ = _ := by
        split_ifs with h1 h2 h2
        · rfl
        · exact (h2 (hleg_iff.1 h1)).elim
        · exact (h1 (hleg_iff.2 h2)).elim
        · rfl
