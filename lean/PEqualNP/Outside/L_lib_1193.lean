import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1193_aux

inductive Node (n k : Nat) where
  | base (u : Fin n)
  | extraS
  | extraT
  | outCopy (e : Fin k)
  | inCopy (e : Fin k)
  | arcSlot (e : Fin k)
  deriving DecidableEq

def nodeToFin {n k : Nat} : Node n k → Fin (n + 3 * k + 2)
  | .base u => ⟨u.val, by omega⟩
  | .extraS => ⟨n, by omega⟩
  | .extraT => ⟨n + 1, by omega⟩
  | .outCopy e => ⟨n + 2 + e.val, by omega⟩
  | .inCopy e => ⟨n + 2 + k + e.val, by omega⟩
  | .arcSlot e => ⟨n + 2 + 2 * k + e.val, by omega⟩

def finToNode {n k : Nat} (i : Fin (n + 3 * k + 2)) : Node n k :=
  if h1 : i.val < n then .base ⟨i.val, h1⟩
  else if h2 : i.val = n then .extraS
  else if h3 : i.val = n + 1 then .extraT
  else if h4 : i.val < n + 2 + k then .outCopy ⟨i.val - (n + 2), by omega⟩
  else if h5 : i.val < n + 2 + 2 * k then .inCopy ⟨i.val - (n + 2 + k), by omega⟩
  else .arcSlot ⟨i.val - (n + 2 + 2 * k), by omega⟩

def nodeEquiv (n k : Nat) : Node n k ≃ Fin (n + 3 * k + 2) where
  toFun := nodeToFin
  invFun := finToNode
  left_inv := by
    intro p
    cases p with
    | base u =>
      dsimp only [nodeToFin, finToNode]
      rw [dif_pos u.isLt]
    | extraS =>
      dsimp only [nodeToFin, finToNode]
      rw [dif_neg (by omega), dif_pos rfl]
    | extraT =>
      dsimp only [nodeToFin, finToNode]
      rw [dif_neg (by omega), dif_neg (by omega), dif_pos rfl]
    | outCopy e =>
      have := e.isLt
      dsimp only [nodeToFin, finToNode]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
      congr 1; apply Fin.ext; change n + 2 + e.val - (n + 2) = e.val; omega
    | inCopy e =>
      have := e.isLt
      dsimp only [nodeToFin, finToNode]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
        dif_pos (by omega)]
      congr 1; apply Fin.ext; change n + 2 + k + e.val - (n + 2 + k) = e.val; omega
    | arcSlot e =>
      have := e.isLt
      dsimp only [nodeToFin, finToNode]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
        dif_neg (by omega)]
      congr 1; apply Fin.ext; change n + 2 + 2 * k + e.val - (n + 2 + 2 * k) = e.val; omega
  right_inv := by
    intro i
    have := i.isLt
    dsimp only [finToNode]
    split_ifs with h1 h2 h3 h4 h5
    · exact Fin.ext rfl
    · apply Fin.ext; dsimp only [nodeToFin]; omega
    · apply Fin.ext; dsimp only [nodeToFin]; omega
    · apply Fin.ext; dsimp only [nodeToFin]; omega
    · apply Fin.ext; dsimp only [nodeToFin]; omega
    · apply Fin.ext; dsimp only [nodeToFin]; omega

def owner {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n) : Node n k → Option (Fin n)
  | .base u => some u
  | .extraS => some s
  | .extraT => some t
  | .outCopy e => some (src e)
  | .inCopy e => some (dst e)
  | .arcSlot _ => none

def ringList {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n) (w : Fin n) : List (Node n k) :=
  [.base w] ++
  (if w = s then [.extraS] else []) ++
  (if w = t then [.extraT] else []) ++
  ((List.finRange k).filter (fun e => decide (src e = w))).map Node.outCopy ++
  ((List.finRange k).filter (fun e => decide (dst e = w))).map Node.inCopy

lemma mem_ringList_iff {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (w : Fin n) (p : Node n k) :
    p ∈ ringList src dst s t w ↔ owner src dst s t p = some w := by
  cases p with
  | base u =>
    simp [ringList, owner]
  | extraS =>
    simp only [ringList, owner, Option.some.injEq, List.mem_append, List.mem_singleton,
      List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    by_cases hs : w = s <;> by_cases ht : w = t <;> simp_all [eq_comm]
  | extraT =>
    simp only [ringList, owner, Option.some.injEq, List.mem_append, List.mem_singleton,
      List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    by_cases hs : w = s <;> by_cases ht : w = t <;> simp_all [eq_comm]
  | outCopy e =>
    simp only [ringList, owner, Option.some.injEq, List.mem_append, List.mem_singleton,
      List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    by_cases hs : w = s <;> by_cases ht : w = t <;> simp [hs, ht]
  | inCopy e =>
    simp only [ringList, owner, Option.some.injEq, List.mem_append, List.mem_singleton,
      List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    by_cases hs : w = s <;> by_cases ht : w = t <;> simp [hs, ht]
  | arcSlot e =>
    simp only [ringList, owner, List.mem_append, List.mem_singleton,
      List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    by_cases hs : w = s <;> by_cases ht : w = t <;> simp [hs, ht]

lemma ringList_nodup {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n) (w : Fin n) :
    (ringList src dst s t w).Nodup := by
  have hnd1 : (((List.finRange k).filter (fun e => decide (src e = w))).map (@Node.outCopy n k)).Nodup := by
    refine ((List.nodup_finRange k).filter _).map ?_
    intro a b h; cases h; rfl
  have hnd2 : (((List.finRange k).filter (fun e => decide (dst e = w))).map (@Node.inCopy n k)).Nodup := by
    refine ((List.nodup_finRange k).filter _).map ?_
    intro a b h; cases h; rfl
  have hndS : (if w = s then ([Node.extraS] : List (Node n k)) else []).Nodup := by
    split_ifs <;> simp
  have hndT : (if w = t then ([Node.extraT] : List (Node n k)) else []).Nodup := by
    split_ifs <;> simp
  dsimp only [ringList]
  rw [List.nodup_append, List.nodup_append, List.nodup_append, List.nodup_append]
  refine ⟨⟨⟨⟨by simp, hndS, ?_⟩, hndT, ?_⟩, hnd1, ?_⟩, hnd2, ?_⟩
  · intro a ha b hb
    simp only [List.mem_singleton] at ha
    subst ha
    split_ifs at hb <;> simp at hb
    subst hb; intro h; cases h
  · intro a ha b hb
    split_ifs at hb <;> simp at hb
    subst hb
    rcases List.mem_append.mp ha with ha1 | ha2
    · simp at ha1; subst ha1; intro h; cases h
    · split_ifs at ha2 <;> simp at ha2
      subst ha2; intro h; cases h
  · intro a ha b hb
    rcases List.mem_map.mp hb with ⟨e, _, rfl⟩
    rcases List.mem_append.mp ha with ha1 | ha2
    · rcases List.mem_append.mp ha1 with ha11 | ha12
      · simp at ha11; subst ha11; intro h; cases h
      · split_ifs at ha12 <;> simp at ha12
        subst ha12; intro h; cases h
    · split_ifs at ha2 <;> simp at ha2
      subst ha2; intro h; cases h
  · intro a ha b hb
    rcases List.mem_map.mp hb with ⟨e, _, rfl⟩
    rcases List.mem_append.mp ha with ha1 | ha2
    · rcases List.mem_append.mp ha1 with ha11 | ha12
      · rcases List.mem_append.mp ha11 with ha111 | ha112
        · simp at ha111; subst ha111; intro h; cases h
        · split_ifs at ha112 <;> simp at ha112
          subst ha112; intro h; cases h
      · split_ifs at ha12 <;> simp at ha12
        subst ha12; intro h; cases h
    · rcases List.mem_map.mp ha2 with ⟨e', _, rfl⟩
      intro h; cases h

def listNext {α : Type*} [DecidableEq α] (L : List α) (p : α) : Option α :=
  if h2 : 2 ≤ L.length then
    if hmem : p ∈ L then
      let idx := L.idxOf p
      some (L[(idx + 1) % L.length]'(Nat.mod_lt _ (by omega)))
    else none
  else none

def listPrev {α : Type*} [DecidableEq α] (L : List α) (p : α) : Option α :=
  if h2 : 2 ≤ L.length then
    if hmem : p ∈ L then
      let idx := L.idxOf p
      some (L[(idx + L.length - 1) % L.length]'(Nat.mod_lt _ (by omega)))
    else none
  else none

lemma listNext_iff_listPrev {α : Type*} [DecidableEq α] (L : List α) (hnd : L.Nodup) (p q : α) :
    listNext L p = some q ↔ listPrev L q = some p := by
  dsimp only [listNext, listPrev]
  by_cases h2 : 2 ≤ L.length
  · rw [dif_pos h2, dif_pos h2]
    constructor
    · intro h
      by_cases hp : p ∈ L
      · rw [dif_pos hp] at h
        have hq_eq : L[(L.idxOf p + 1) % L.length]'(Nat.mod_lt _ (by omega)) = q :=
          Option.some.inj h
        have hq : q ∈ L := hq_eq ▸ List.getElem_mem _
        rw [dif_pos hq]
        congr 1
        have hp_idx : L.idxOf p < L.length := List.idxOf_lt_length_of_mem hp
        have hq_idx : L.idxOf q = (L.idxOf p + 1) % L.length := by
          rw [← hq_eq]
          exact List.Nodup.idxOf_getElem hnd _ (Nat.mod_lt _ (by omega))
        have hmod : ((L.idxOf p + 1) % L.length + L.length - 1) % L.length = L.idxOf p := by
          by_cases hlast : L.idxOf p + 1 = L.length
          · rw [hlast, Nat.mod_self, zero_add]
            have : L.length - 1 < L.length := by omega
            rw [Nat.mod_eq_of_lt this]; omega
          · have hlt : L.idxOf p + 1 < L.length := by omega
            rw [Nat.mod_eq_of_lt hlt]
            have heq : L.idxOf p + 1 + L.length - 1 = L.idxOf p + L.length := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hp_idx]
        have hget : L[(L.idxOf q + L.length - 1) % L.length]'(Nat.mod_lt _ (by omega)) =
            L[L.idxOf p]'hp_idx := by
          simp only [hq_idx, hmod]
        rw [hget]
        exact List.getElem_idxOf hp_idx
      · rw [dif_neg hp] at h; cases h
    · intro h
      by_cases hq : q ∈ L
      · rw [dif_pos hq] at h
        have hp_eq : L[(L.idxOf q + L.length - 1) % L.length]'(Nat.mod_lt _ (by omega)) = p :=
          Option.some.inj h
        have hp : p ∈ L := hp_eq ▸ List.getElem_mem _
        rw [dif_pos hp]
        congr 1
        have hq_idx : L.idxOf q < L.length := List.idxOf_lt_length_of_mem hq
        have hp_idx : L.idxOf p = (L.idxOf q + L.length - 1) % L.length := by
          rw [← hp_eq]
          exact List.Nodup.idxOf_getElem hnd _ (Nat.mod_lt _ (by omega))
        have hmod : ((L.idxOf q + L.length - 1) % L.length + 1) % L.length = L.idxOf q := by
          by_cases hzero : L.idxOf q = 0
          · rw [hzero, zero_add]
            have hlt : L.length - 1 < L.length := by omega
            rw [Nat.mod_eq_of_lt hlt]
            have heq : L.length - 1 + 1 = L.length := by omega
            rw [heq, Nat.mod_self]
          · have hpos : 1 ≤ L.idxOf q := by omega
            have hlt1 : L.idxOf q - 1 < L.length := by omega
            have heq : L.idxOf q + L.length - 1 = (L.idxOf q - 1) + L.length := by omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
            have heq2 : L.idxOf q - 1 + 1 = L.idxOf q := by omega
            rw [heq2, Nat.mod_eq_of_lt hq_idx]
        have hget : L[(L.idxOf p + 1) % L.length]'(Nat.mod_lt _ (by omega)) =
            L[L.idxOf q]'hq_idx := by
          simp only [hp_idx, hmod]
        rw [hget]
        exact List.getElem_idxOf hq_idx
      · rw [dif_neg hq] at h; cases h
  · rw [dif_neg h2, dif_neg h2]
    simp

def ringNext {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n) (p : Node n k) :
    Option (Node n k) :=
  match owner src dst s t p with
  | some w => listNext (ringList src dst s t w) p
  | none => none

def ringPrev {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n) (p : Node n k) :
    Option (Node n k) :=
  match owner src dst s t p with
  | some w => listPrev (ringList src dst s t w) p
  | none => none

lemma ringNext_owner {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (p q : Node n k) (h : ringNext src dst s t p = some q) :
    ∃ w, owner src dst s t p = some w ∧ owner src dst s t q = some w := by
  dsimp only [ringNext] at h
  cases hw : owner src dst s t p with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    dsimp only [listNext] at h
    split_ifs at h with h2 hmem
    have hq_eq := Option.some.inj h
    have hq_mem : q ∈ ringList src dst s t w := hq_eq ▸ List.getElem_mem _
    exact ⟨w, rfl, (mem_ringList_iff src dst s t w q).mp hq_mem⟩

lemma ringPrev_owner {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (p q : Node n k) (h : ringPrev src dst s t p = some q) :
    ∃ w, owner src dst s t p = some w ∧ owner src dst s t q = some w := by
  dsimp only [ringPrev] at h
  cases hw : owner src dst s t p with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    dsimp only [listPrev] at h
    split_ifs at h with h2 hmem
    have hq_eq := Option.some.inj h
    have hq_mem : q ∈ ringList src dst s t w := hq_eq ▸ List.getElem_mem _
    exact ⟨w, rfl, (mem_ringList_iff src dst s t w q).mp hq_mem⟩

lemma ringNext_iff_ringPrev {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (p q : Node n k) :
    ringNext src dst s t p = some q ↔ ringPrev src dst s t q = some p := by
  constructor
  · intro h
    rcases ringNext_owner src dst s t p q h with ⟨w, hwp, hwq⟩
    dsimp only [ringNext, ringPrev] at h ⊢
    rw [hwp] at h
    rw [hwq]
    exact (listNext_iff_listPrev _ (ringList_nodup src dst s t w) p q).mp h
  · intro h
    rcases ringPrev_owner src dst s t q p h with ⟨w, hwq, hwp⟩
    dsimp only [ringNext, ringPrev] at h ⊢
    rw [hwq] at h
    rw [hwp]
    exact (listNext_iff_listPrev _ (ringList_nodup src dst s t w) p q).mpr h

def extraNb {n k : Nat} (s t : Fin n) : Node n k × Bool → Option (Node n k × Bool)
  | (.base u, false) => if u = s then some (.extraS, false) else none
  | (.extraS, false) => some (.base s, false)
  | (.base u, true) => if u = t then some (.extraT, true) else none
  | (.extraT, true) => some (.base t, true)
  | (.outCopy e, true) => some (.arcSlot e, false)
  | (.arcSlot e, false) => some (.outCopy e, true)
  | (.arcSlot e, true) => some (.inCopy e, false)
  | (.inCopy e, false) => some (.arcSlot e, true)
  | _ => none

lemma extraNb_symm {n k : Nat} (s t : Fin n) (u v : Node n k × Bool) :
    extraNb s t u = some v ↔ extraNb s t v = some u := by
  rcases u with ⟨p, b⟩
  rcases v with ⟨q, c⟩
  cases p <;> cases b <;> cases q <;> cases c <;> simp [extraNb, eq_comm]

lemma extraNb_ne_self {n k : Nat} (s t : Fin n) (u : Node n k × Bool) :
    extraNb s t u ≠ some u := by
  rcases u with ⟨p, b⟩
  cases p <;> cases b <;> simp [extraNb] <;> try (split_ifs <;> simp)

def ringNb {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n) :
    Node n k × Bool → Option (Node n k × Bool)
  | (p, true) => (ringNext src dst s t p).map (fun q => (q, false))
  | (p, false) => (ringPrev src dst s t p).map (fun q => (q, true))

lemma ringNb_symm {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (u v : Node n k × Bool) :
    ringNb src dst s t u = some v ↔ ringNb src dst s t v = some u := by
  rcases u with ⟨p, b⟩
  rcases v with ⟨q, c⟩
  cases b <;> cases c <;> simp [ringNb, ringNext_iff_ringPrev]

lemma ringNb_ne_self {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (u : Node n k × Bool) :
    ringNb src dst s t u ≠ some u := by
  rcases u with ⟨p, b⟩
  cases b <;> simp [ringNb]

def nbNode {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (u : Node n k × Bool) : Finset (Node n k × Bool) :=
  {(u.1, !u.2)} ∪ (ringNb src dst s t u).toFinset ∪ (extraNb s t u).toFinset

lemma nbNode_card_le {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (u : Node n k × Bool) : (nbNode src dst s t u).card ≤ 3 := by
  have h1 : ({(u.1, !u.2)} : Finset (Node n k × Bool)).card = 1 := Finset.card_singleton _
  have h2 : (ringNb src dst s t u).toFinset.card ≤ 1 := by
    cases ringNb src dst s t u <;> simp
  have h3 : (extraNb s t u).toFinset.card ≤ 1 := by
    cases extraNb s t u <;> simp
  have hu1 := Finset.card_union_le ({(u.1, !u.2)} ∪ (ringNb src dst s t u).toFinset)
    (extraNb s t u).toFinset
  have hu2 := Finset.card_union_le ({(u.1, !u.2)} : Finset (Node n k × Bool))
    (ringNb src dst s t u).toFinset
  dsimp only [nbNode]
  omega

lemma nbNode_not_mem_self {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (u : Node n k × Bool) : u ∉ nbNode src dst s t u := by
  simp only [nbNode, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def]
  rintro ((h1 | h2) | h3)
  · rcases u with ⟨p, b⟩
    have hb : b = !b := congrArg Prod.snd h1
    cases b <;> cases hb
  · exact ringNb_ne_self src dst s t u h2
  · exact extraNb_ne_self s t u h3

lemma nbNode_symm {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (u v : Node n k × Bool) :
    v ∈ nbNode src dst s t u ↔ u ∈ nbNode src dst s t v := by
  simp only [nbNode, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def]
  have h1 : v = (u.1, !u.2) ↔ u = (v.1, !v.2) := by
    rcases u with ⟨p, b⟩; rcases v with ⟨q, c⟩
    cases b <;> cases c <;> simp [eq_comm]
  rw [h1, ringNb_symm, extraNb_symm]

lemma nbNode_same_shore {n k : Nat} (src dst : Fin k → Fin n) (s t : Fin n)
    (c : Bool) (p q : Node n k) :
    (q, c) ∈ nbNode src dst s t (p, c) ↔
      match c with
      | false => (p = .base s ∧ q = .extraS) ∨ (p = .extraS ∧ q = .base s)
      | true => (p = .base t ∧ q = .extraT) ∨ (p = .extraT ∧ q = .base t) := by
  simp only [nbNode, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def]
  have h1 : (q, c) ≠ (p, !c) := by
    intro h; have := congrArg Prod.snd h; cases c <;> cases this
  have h2 : ringNb src dst s t (p, c) ≠ some (q, c) := by
    cases c <;> simp [ringNb]
  simp only [h1, h2, false_or]
  cases c
  · cases p <;> cases q <;> simp [extraNb, eq_comm]
  · cases p <;> cases q <;> simp [extraNb, eq_comm]

theorem main (n k : Nat) (src dst : Fin k → Fin n) (s t : Fin n) (hst : s ≠ t) :
    ∃ (m : Nat) (slot : Fin k ↪ Fin m)
      (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (a b : Bool → Fin m),
      m ≤ n + 3 * k + 2 ∧
      (∀ u, u ∉ nb u ∧ (nb u).card ≤ 3) ∧
      (∀ u v, v ∈ nb u ↔ u ∈ nb v) ∧
      (∀ i, (i, true) ∈ nb (i, false)) ∧
      (∀ c, a c ≠ b c ∧ ∀ i j,
        (j, c) ∈ nb (i, c) ↔ (i = a c ∧ j = b c) ∨ (i = b c ∧ j = a c)) ∧
      ∀ z : Fin k → Bool,
        let walk := Relation.ReflTransGen
          (fun (u v : Fin n) => ∃ e, z e = true ∧ src e = u ∧ dst e = v)
        let possible := ∃ x : (Fin m × Bool) → Bool,
          (∀ u, ∀ v ∈ nb u, x u = true ∨ x v = true) ∧
          (∀ e, xor (x (slot e, false)) (x (slot e, true)) = z e) ∧
          (∀ i, (∀ e, slot e ≠ i) → xor (x (i, false)) (x (i, true)) = true)
        ¬ possible ↔ walk s t := by
  let m := n + 3 * k + 2
  let eqN : Node n k ≃ Fin m := nodeEquiv n k
  let eqP : (Node n k × Bool) ≃ (Fin m × Bool) := eqN.prodCongr (Equiv.refl Bool)
  let slot : Fin k ↪ Fin m :=
    ⟨fun e => eqN (.arcSlot e), fun e1 e2 h => by
      have h' := eqN.injective h
      cases h'; rfl⟩
  let nb : (Fin m × Bool) → Finset (Fin m × Bool) :=
    fun u => (nbNode src dst s t (eqP.symm u)).image eqP
  let a : Bool → Fin m := fun c => if c then eqN (.base t) else eqN (.base s)
  let b : Bool → Fin m := fun c => if c then eqN .extraT else eqN .extraS
  have hmem_nb : ∀ (p q : Node n k) (c1 c2 : Bool),
      (eqN q, c2) ∈ nb (eqN p, c1) ↔ (q, c2) ∈ nbNode src dst s t (p, c1) := by
    intro p q c1 c2
    dsimp only [nb]
    have hsym : eqP.symm (eqN p, c1) = (p, c1) := by
      simp [eqP]
    rw [hsym, Finset.mem_image]
    constructor
    · rintro ⟨⟨q', c2'⟩, hmem, heq⟩
      have h1 : eqN q' = eqN q := congrArg Prod.fst heq
      have h2 : c2' = c2 := congrArg Prod.snd heq
      have hq' : q' = q := eqN.injective h1
      subst hq'; subst h2
      exact hmem
    · intro hmem
      exact ⟨(q, c2), hmem, rfl⟩
  refine ⟨m, slot, nb, a, b, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- no self-loops and card <= 3
    intro u
    rcases u with ⟨i, c⟩
    have hi : i = eqN (eqN.symm i) := (eqN.apply_symm_apply i).symm
    constructor
    · rw [hi, hmem_nb]
      exact nbNode_not_mem_self src dst s t (eqN.symm i, c)
    · dsimp only [nb]
      exact le_trans Finset.card_image_le (nbNode_card_le src dst s t _)
  · -- symmetry
    intro u v
    rcases u with ⟨i, c1⟩; rcases v with ⟨j, c2⟩
    rw [← eqN.apply_symm_apply i, ← eqN.apply_symm_apply j, hmem_nb, hmem_nb]
    exact nbNode_symm src dst s t _ _
  · -- internal pair edges
    intro i
    rw [← eqN.apply_symm_apply i, hmem_nb]
    simp [nbNode]
  · -- same-shore edges
    intro c
    constructor
    · cases c
      · simp only [a, b, Bool.false_eq_true, ↓reduceIte]
        intro h; have h' := eqN.injective h; cases h'
      · simp only [a, b, ↓reduceIte]
        intro h; have h' := eqN.injective h; cases h'
    · intro i j
      rw [← eqN.apply_symm_apply i, ← eqN.apply_symm_apply j, hmem_nb, nbNode_same_shore]
      cases c <;> simp only [a, b, Bool.false_eq_true, ↓reduceIte, eqN.injective.eq_iff]
  · -- reachability equivalence
    intro z
    dsimp only
    let step : Fin n → Fin n → Prop := fun u v => ∃ e, z e = true ∧ src e = u ∧ dst e = v
    constructor
    · -- ¬ possible → walk s t
      intro hnp
      by_contra hnwalk
      apply hnp
      classical
      let R : Fin n → Bool := fun w => decide (Relation.ReflTransGen step s w)
      have hRs : R s = true := by
        simp only [R, decide_eq_true_eq]
        exact Relation.ReflTransGen.refl
      have hRt : R t = false := by
        simp only [R, decide_eq_false_iff_not]
        exact hnwalk
      have hRstep : ∀ e : Fin k, z e = true → R (src e) = true → R (dst e) = true := by
        intro e hze hsrc
        simp only [R, decide_eq_true_eq] at hsrc ⊢
        exact Relation.ReflTransGen.tail hsrc ⟨e, hze, rfl, rfl⟩
      let xNode : Node n k × Bool → Bool := fun pb =>
        match pb.1 with
        | .arcSlot e =>
          if z e = true then (if pb.2 then !(R (src e)) else R (src e)) else true
        | p =>
          match owner src dst s t p with
          | some w => if pb.2 then !(R w) else R w
          | none => true
      have hxNode_own : ∀ (p : Node n k) (w : Fin n) (c : Bool),
          owner src dst s t p = some w →
          xNode (p, c) = if c then !(R w) else R w := by
        intro p w c hown
        cases p <;> simp [owner] at hown <;> subst hown <;> simp [xNode, owner]
      have hcovNode : ∀ (p q : Node n k) (c1 c2 : Bool),
          (q, c2) ∈ nbNode src dst s t (p, c1) →
          xNode (p, c1) = true ∨ xNode (q, c2) = true := by
        intro p q c1 c2 hmem
        simp only [nbNode, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset,
          Option.mem_def] at hmem
        rcases hmem with (h1 | h2) | h3
        · -- internal edge
          have hq : q = p := congrArg Prod.fst h1
          have hc2 : c2 = !c1 := congrArg Prod.snd h1
          rw [hq, hc2]
          cases p with
          | arcSlot e =>
            by_cases hze : z e = true
            · cases c1 <;> cases hR : R (src e) <;> simp [xNode, hze, hR]
            · simp [xNode, hze]
          | base w => cases c1 <;> cases hR : R w <;> simp [xNode, owner, hR]
          | extraS => cases c1 <;> cases hR : R s <;> simp [xNode, owner, hR]
          | extraT => cases c1 <;> cases hR : R t <;> simp [xNode, owner, hR]
          | outCopy e => cases c1 <;> cases hR : R (src e) <;> simp [xNode, owner, hR]
          | inCopy e => cases c1 <;> cases hR : R (dst e) <;> simp [xNode, owner, hR]
        · -- ring edge
          cases c1
          · simp only [ringNb, Option.map_eq_some_iff] at h2
            rcases h2 with ⟨q', hprev, heq⟩
            have hq' : q' = q := congrArg Prod.fst heq
            have hc2 : true = c2 := congrArg Prod.snd heq
            rw [← hq', ← hc2]
            rcases ringPrev_owner src dst s t p q' hprev with ⟨w, hwp, hwq⟩
            rw [hxNode_own p w false hwp, hxNode_own q' w true hwq]
            cases R w <;> simp
          · simp only [ringNb, Option.map_eq_some_iff] at h2
            rcases h2 with ⟨q', hnext, heq⟩
            have hq' : q' = q := congrArg Prod.fst heq
            have hc2 : false = c2 := congrArg Prod.snd heq
            rw [← hq', ← hc2]
            rcases ringNext_owner src dst s t p q' hnext with ⟨w, hwp, hwq⟩
            rw [hxNode_own p w true hwp, hxNode_own q' w false hwq]
            cases R w <;> simp
        · -- extra edge
          cases p <;> cases c1 <;> simp only [extraNb] at h3
          · split_ifs at h3 with hws
            · subst hws; cases h3; left; simp [xNode, owner, hRs]
          · split_ifs at h3 with hwt
            · subst hwt; cases h3; left; simp [xNode, owner, hRt]
          · cases h3; left; simp [xNode, owner, hRs]
          · cases h3
          · cases h3
          · cases h3; left; simp [xNode, owner, hRt]
          · cases h3
          · rename_i e
            cases h3
            by_cases hze : z e = true
            · simp only [xNode, owner, hze, ↓reduceIte]
              cases R (src e) <;> simp
            · right; simp [xNode, hze]
          · rename_i e
            cases h3
            by_cases hze : z e = true
            · simp only [xNode, owner, hze, ↓reduceIte]
              cases hR : R (src e)
              · right; simp
              · left; exact hRstep e hze hR
            · right; simp [xNode, hze]
          · cases h3
          · rename_i e
            cases h3
            by_cases hze : z e = true
            · simp only [xNode, owner, hze, ↓reduceIte]
              cases R (src e) <;> simp
            · left; simp [xNode, hze]
          · rename_i e
            cases h3
            by_cases hze : z e = true
            · simp only [xNode, owner, hze, ↓reduceIte]
              cases hR : R (src e)
              · left; simp
              · right; exact hRstep e hze hR
            · left; simp [xNode, hze]
      let x : (Fin m × Bool) → Bool := fun u => xNode (eqP.symm u)
      refine ⟨x, ?_, ?_, ?_⟩
      · -- cover condition
        intro u v hvu
        rcases u with ⟨i, c1⟩; rcases v with ⟨j, c2⟩
        have hmem : (eqN.symm j, c2) ∈ nbNode src dst s t (eqN.symm i, c1) := by
          have hi : i = eqN (eqN.symm i) := (eqN.apply_symm_apply i).symm
          have hj : j = eqN (eqN.symm j) := (eqN.apply_symm_apply j).symm
          rw [hi, hj, hmem_nb] at hvu
          exact hvu
        exact hcovNode (eqN.symm i) (eqN.symm j) c1 c2 hmem
      · -- slot parity
        intro e
        have h1 : eqP.symm (slot e, false) = (.arcSlot e, false) := by
          change eqP.symm (eqN (.arcSlot e), false) = (.arcSlot e, false)
          simp [eqP]
        have h2 : eqP.symm (slot e, true) = (.arcSlot e, true) := by
          change eqP.symm (eqN (.arcSlot e), true) = (.arcSlot e, true)
          simp [eqP]
        simp only [x, h1, h2, xNode]
        cases hze : z e
        · simp
        · cases R (src e) <;> simp
      · -- non-slot parity
        intro i hns
        have h1 : eqP.symm (i, false) = (eqN.symm i, false) := by simp [eqP]
        have h2 : eqP.symm (i, true) = (eqN.symm i, true) := by simp [eqP]
        simp only [x, h1, h2]
        cases hp : eqN.symm i with
        | arcSlot e =>
          exfalso
          apply hns e
          change eqN (.arcSlot e) = i
          rw [← hp, eqN.apply_symm_apply]
        | base w => cases R w <;> simp [xNode, owner]
        | extraS => cases R s <;> simp [xNode, owner]
        | extraT => cases R t <;> simp [xNode, owner]
        | outCopy e => cases R (src e) <;> simp [xNode, owner]
        | inCopy e => cases R (dst e) <;> simp [xNode, owner]
    · -- walk s t → ¬ possible
      intro hwalk hpos
      rcases hpos with ⟨x, hcov, hslot, hnonslot⟩
      let xN : Node n k × Bool → Bool := fun u => x (eqP u)
      have hcovN : ∀ u v, v ∈ nbNode src dst s t u → xN u = true ∨ xN v = true := by
        intro u v hvu
        rcases u with ⟨p, c1⟩; rcases v with ⟨q, c2⟩
        apply hcov (eqN p, c1) (eqN q, c2)
        rw [hmem_nb]
        exact hvu
      have hns_xor : ∀ p : Node n k, (∀ e : Fin k, p ≠ .arcSlot e) →
          xor (xN (p, false)) (xN (p, true)) = true := by
        intro p hp
        apply hnonslot (eqN p)
        intro e heq
        exact hp e (eqN.injective heq).symm
      have hns_true : ∀ p : Node n k, (∀ e : Fin k, p ≠ .arcSlot e) →
          xN (p, true) = !(xN (p, false)) := by
        intro p hp
        have hx := hns_xor p hp
        cases hf : xN (p, false) <;> cases ht : xN (p, true) <;> simp [hf, ht] at hx ⊢
      have hslot_xor : ∀ e : Fin k, xor (xN (.arcSlot e, false)) (xN (.arcSlot e, true)) = z e := by
        intro e
        exact hslot e
      have hring_step : ∀ (w : Fin n) (p q : Node n k),
          owner src dst s t p = some w → ringNext src dst s t p = some q →
          xN (p, false) = true → xN (q, false) = true := by
        intro w p q hwp hnext hpf
        have hp_ns : ∀ e, p ≠ .arcSlot e := by intro e he; subst he; simp [owner] at hwp
        have hpt : xN (p, true) = false := by rw [hns_true p hp_ns, hpf]; rfl
        have hmem : (q, false) ∈ nbNode src dst s t (p, true) := by
          simp [nbNode, ringNb, hnext]
        rcases hcovN (p, true) (q, false) hmem with h1 | h2
        · rw [hpt] at h1; cases h1
        · exact h2
      have hring_all : ∀ (w : Fin n) (p q : Node n k),
          owner src dst s t p = some w → owner src dst s t q = some w →
          xN (p, false) = true → xN (q, false) = true := by
        intro w p q hwp hwq hpf
        let L := ringList src dst s t w
        have hpL : p ∈ L := (mem_ringList_iff src dst s t w p).mpr hwp
        have hqL : q ∈ L := (mem_ringList_iff src dst s t w q).mpr hwq
        by_cases h2 : 2 ≤ L.length
        · have hwalk_idx : ∀ (d : Nat) (i : Nat) (hi : i < L.length),
              xN (L[i]'hi, false) = true →
              xN (L[(i + d) % L.length]'(Nat.mod_lt _ (by omega)), false) = true := by
            intro d
            induction d with
            | zero =>
              intro i hi hxi
              simpa [Nat.mod_eq_of_lt hi] using hxi
            | succ d ih =>
              intro i hi hxi
              let j := (i + d) % L.length
              have hj : j < L.length := Nat.mod_lt _ (by omega)
              have hxj : xN (L[j]'hj, false) = true := ih i hi hxi
              have hown_j : owner src dst s t (L[j]'hj) = some w :=
                (mem_ringList_iff src dst s t w _).mp (List.getElem_mem hj)
              have hidx_j : L.idxOf (L[j]'hj) = j :=
                List.Nodup.idxOf_getElem (ringList_nodup src dst s t w) j hj
              have hnext_j : ringNext src dst s t (L[j]'hj) =
                  some (L[(j + 1) % L.length]'(Nat.mod_lt _ (by omega))) := by
                dsimp only [ringNext]
                rw [hown_j]
                change listNext L (L[j]'hj) = _
                dsimp only [listNext]
                rw [dif_pos h2, dif_pos (List.getElem_mem hj)]
                simp only [hidx_j]
              have hres := hring_step w _ _ hown_j hnext_j hxj
              have hmod_eq : (j + 1) % L.length = (i + (d + 1)) % L.length := by
                dsimp only [j]
                rw [Nat.mod_add_mod, add_assoc]
              simpa only [hmod_eq] using hres
          have hp_idx : L.idxOf p < L.length := List.idxOf_lt_length_of_mem hpL
          have hq_idx : L.idxOf q < L.length := List.idxOf_lt_length_of_mem hqL
          let d := (L.idxOf q + L.length - L.idxOf p) % L.length
          have hstart : xN (L[L.idxOf p]'hp_idx, false) = true := by
            simpa [List.getElem_idxOf hp_idx] using hpf
          have hres := hwalk_idx d (L.idxOf p) hp_idx hstart
          have hmod_end : (L.idxOf p + d) % L.length = L.idxOf q := by
            dsimp only [d]
            rw [Nat.add_mod_mod]
            have heq : L.idxOf p + (L.idxOf q + L.length - L.idxOf p) = L.idxOf q + L.length := by
              omega
            rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hq_idx]
          have hres' : xN (L[L.idxOf q]'hq_idx, false) = true := by
            simpa only [hmod_end] using hres
          simpa [List.getElem_idxOf hq_idx] using hres'
        · have hlen1 : L.length = 1 := by
            have hpos : 0 < L.length := List.length_pos_of_mem hpL
            omega
          cases hL : L with
          | nil => simp [hL] at hlen1
          | cons a tl =>
            cases tl with
            | nil =>
              rw [hL] at hpL hqL
              simp at hpL hqL
              subst hpL; subst hqL
              exact hpf
            | cons b tl2 => simp [hL] at hlen1
      have hbase_s : xN (.base s, false) = true := by
        have hmem : (Node.extraS, false) ∈ nbNode src dst s t (.base s, false) := by
          simp [nbNode, extraNb]
        rcases hcovN (.base s, false) (.extraS, false) hmem with h1 | h2
        · exact h1
        · exact hring_all s .extraS (.base s) rfl rfl h2
      have hbase_t : xN (.base t, false) = false := by
        by_contra htf
        have hbt : xN (.base t, false) = true := Bool.eq_true_of_not_eq_false htf
        have het : xN (.extraT, false) = true := hring_all t (.base t) .extraT rfl rfl hbt
        have hbt_t : xN (.base t, true) = false := by
          rw [hns_true (.base t) (by intro e h; cases h), hbt]; rfl
        have het_t : xN (.extraT, true) = false := by
          rw [hns_true .extraT (by intro e h; cases h), het]; rfl
        have hmem : (Node.extraT, true) ∈ nbNode src dst s t (.base t, true) := by
          simp [nbNode, extraNb]
        rcases hcovN (.base t, true) (.extraT, true) hmem with h1 | h2
        · rw [hbt_t] at h1; cases h1
        · rw [het_t] at h2; cases h2
      have hreach_true : ∀ u, Relation.ReflTransGen step s u → xN (.base u, false) = true := by
        intro u hsu
        induction hsu with
        | refl => exact hbase_s
        | tail _ hstep ih =>
          rcases hstep with ⟨e, hze, hsrc, hdst⟩
          subst hsrc; subst hdst
          have hout_f : xN (.outCopy e, false) = true :=
            hring_all (src e) (.base (src e)) (.outCopy e) rfl rfl ih
          have hout_t : xN (.outCopy e, true) = false := by
            rw [hns_true (.outCopy e) (by intro e' h; cases h), hout_f]; rfl
          have hmem1 : (Node.arcSlot e, false) ∈ nbNode src dst s t (.outCopy e, true) := by
            simp [nbNode, extraNb]
          have hslot_f : xN (.arcSlot e, false) = true := by
            rcases hcovN (.outCopy e, true) (.arcSlot e, false) hmem1 with h1 | h2
            · rw [hout_t] at h1; cases h1
            · exact h2
          have hslot_t : xN (.arcSlot e, true) = false := by
            have hx := hslot_xor e
            rw [hze, hslot_f] at hx
            cases ht : xN (.arcSlot e, true) <;> simp [ht] at hx ⊢
          have hmem2 : (Node.inCopy e, false) ∈ nbNode src dst s t (.arcSlot e, true) := by
            simp [nbNode, extraNb]
          have hin_f : xN (.inCopy e, false) = true := by
            rcases hcovN (.arcSlot e, true) (.inCopy e, false) hmem2 with h1 | h2
            · rw [hslot_t] at h1; cases h1
            · exact h2
          exact hring_all (dst e) (.inCopy e) (.base (dst e)) rfl rfl hin_f
      have ht_true := hreach_true t hwalk
      rw [hbase_t] at ht_true
      cases ht_true

end PEqualNP.Outside.L_lib_1193_aux

theorem PEqualNP.Outside.L_lib_1193 :
∀ (n k : Nat) (src dst : Fin k → Fin n) (s t : Fin n), s ≠ t →
  ∃ (m : Nat) (slot : Fin k ↪ Fin m)
    (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (a b : Bool → Fin m),
    m ≤ n + 3*k + 2 ∧
    (∀ u, u ∉ nb u ∧ (nb u).card ≤ 3) ∧
    (∀ u v, v ∈ nb u ↔ u ∈ nb v) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    (∀ c, a c ≠ b c ∧ ∀ i j,
      (j,c) ∈ nb (i,c) ↔ (i = a c ∧ j = b c) ∨ (i = b c ∧ j = a c)) ∧
    ∀ z : Fin k → Bool,
      let walk := Relation.ReflTransGen
        (fun (u v : Fin n) => ∃ e, z e = true ∧ src e = u ∧ dst e = v)
      let possible := ∃ x : (Fin m × Bool) → Bool,
        (∀ u, ∀ v ∈ nb u, x u = true ∨ x v = true) ∧
        (∀ e, xor (x (slot e,false)) (x (slot e,true)) = z e) ∧
        (∀ i, (∀ e, slot e ≠ i) → xor (x (i,false)) (x (i,true)) = true)
      ¬ possible ↔ walk s t := by
  intro n k src dst s t hst
  exact PEqualNP.Outside.L_lib_1193_aux.main n k src dst s t hst
