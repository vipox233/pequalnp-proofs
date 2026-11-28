import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1197_aux

inductive Node (n k : Nat) where
  | base (i : Fin n)
  | outCopy (e : Fin k)
  | inCopy (e : Fin k)
  | arcSlot (e : Fin k)
  deriving DecidableEq

def nodeToFin {n k : Nat} : Node n k → Fin (n + 3 * k)
  | .base i => ⟨i.val, by omega⟩
  | .outCopy e => ⟨n + e.val, by omega⟩
  | .inCopy e => ⟨n + k + e.val, by omega⟩
  | .arcSlot e => ⟨n + 2 * k + e.val, by omega⟩

def finToNode {n k : Nat} (i : Fin (n + 3 * k)) : Node n k :=
  if h1 : i.val < n then .base ⟨i.val, h1⟩
  else if h4 : i.val < n + k then .outCopy ⟨i.val - n, by omega⟩
  else if h5 : i.val < n + 2 * k then .inCopy ⟨i.val - (n + k), by omega⟩
  else .arcSlot ⟨i.val - (n + 2 * k), by omega⟩

def nodeEquiv (n k : Nat) : Node n k ≃ Fin (n + 3 * k) where
  toFun := nodeToFin
  invFun := finToNode
  left_inv := by
    intro p
    cases p with
    | base u =>
      dsimp only [nodeToFin, finToNode]
      rw [dif_pos u.isLt]
    | outCopy e =>
      have := e.isLt
      dsimp only [nodeToFin, finToNode]
      rw [dif_neg (by omega), dif_pos (by omega)]
      congr 1; apply Fin.ext; change n + e.val - n = e.val; omega
    | inCopy e =>
      have := e.isLt
      dsimp only [nodeToFin, finToNode]
      rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
      congr 1; apply Fin.ext; change n + k + e.val - (n + k) = e.val; omega
    | arcSlot e =>
      have := e.isLt
      dsimp only [nodeToFin, finToNode]
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
      congr 1; apply Fin.ext; change n + 2 * k + e.val - (n + 2 * k) = e.val; omega
  right_inv := by
    intro i
    have := i.isLt
    dsimp only [finToNode]
    split_ifs with h1 h4 h5
    · exact Fin.ext rfl
    · apply Fin.ext; dsimp only [nodeToFin]; omega
    · apply Fin.ext; dsimp only [nodeToFin]; omega
    · apply Fin.ext; dsimp only [nodeToFin]; omega

def owner {n k : Nat} (src dst : Fin k → Fin n) : Node n k → Option (Fin n)
  | .base i => some i
  | .outCopy e => some (src e)
  | .inCopy e => some (dst e)
  | .arcSlot _ => none

def ringList {n k : Nat} (src dst : Fin k → Fin n) (w : Fin n) : List (Node n k) :=
  [.base w] ++
  ((List.finRange k).filter (fun e => decide (src e = w))).map Node.outCopy ++
  ((List.finRange k).filter (fun e => decide (dst e = w))).map Node.inCopy

lemma mem_ringList_iff {n k : Nat} (src dst : Fin k → Fin n)
    (w : Fin n) (p : Node n k) :
    p ∈ ringList src dst w ↔ owner src dst p = some w := by
  cases p with
  | base u => simp [ringList, owner]
  | outCopy e => simp [ringList, owner]
  | inCopy e => simp [ringList, owner]
  | arcSlot e => simp [ringList, owner]

lemma ringList_nodup {n k : Nat} (src dst : Fin k → Fin n) (w : Fin n) :
    (ringList src dst w).Nodup := by
  have hnd1 : (((List.finRange k).filter (fun e => decide (src e = w))).map
      (@Node.outCopy n k)).Nodup := by
    refine ((List.nodup_finRange k).filter _).map ?_
    intro a b h; cases h; rfl
  have hnd2 : (((List.finRange k).filter (fun e => decide (dst e = w))).map
      (@Node.inCopy n k)).Nodup := by
    refine ((List.nodup_finRange k).filter _).map ?_
    intro a b h; cases h; rfl
  dsimp only [ringList]
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨by simp, hnd1, ?_⟩, hnd2, ?_⟩
  · intro a ha b hb
    simp only [List.mem_singleton] at ha
    subst ha
    rcases List.mem_map.mp hb with ⟨e, _, rfl⟩
    intro h; cases h
  · intro a ha b hb
    rcases List.mem_map.mp hb with ⟨e, _, rfl⟩
    rcases List.mem_append.mp ha with ha1 | ha2
    · simp at ha1; subst ha1; intro h; cases h
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

def ringNext {n k : Nat} (src dst : Fin k → Fin n) (p : Node n k) : Option (Node n k) :=
  match owner src dst p with
  | some w => listNext (ringList src dst w) p
  | none => none

def ringPrev {n k : Nat} (src dst : Fin k → Fin n) (p : Node n k) : Option (Node n k) :=
  match owner src dst p with
  | some w => listPrev (ringList src dst w) p
  | none => none

lemma ringNext_owner {n k : Nat} (src dst : Fin k → Fin n)
    (p q : Node n k) (h : ringNext src dst p = some q) :
    ∃ w, owner src dst p = some w ∧ owner src dst q = some w := by
  dsimp only [ringNext] at h
  cases hw : owner src dst p with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    dsimp only [listNext] at h
    split_ifs at h with h2 hmem
    have hq_eq := Option.some.inj h
    have hq_mem : q ∈ ringList src dst w := hq_eq ▸ List.getElem_mem _
    exact ⟨w, rfl, (mem_ringList_iff src dst w q).mp hq_mem⟩

lemma ringPrev_owner {n k : Nat} (src dst : Fin k → Fin n)
    (p q : Node n k) (h : ringPrev src dst p = some q) :
    ∃ w, owner src dst p = some w ∧ owner src dst q = some w := by
  dsimp only [ringPrev] at h
  cases hw : owner src dst p with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    dsimp only [listPrev] at h
    split_ifs at h with h2 hmem
    have hq_eq := Option.some.inj h
    have hq_mem : q ∈ ringList src dst w := hq_eq ▸ List.getElem_mem _
    exact ⟨w, rfl, (mem_ringList_iff src dst w q).mp hq_mem⟩

lemma ringNext_iff_ringPrev {n k : Nat} (src dst : Fin k → Fin n) (p q : Node n k) :
    ringNext src dst p = some q ↔ ringPrev src dst q = some p := by
  constructor
  · intro h
    rcases ringNext_owner src dst p q h with ⟨w, hwp, hwq⟩
    dsimp only [ringNext, ringPrev] at h ⊢
    rw [hwp] at h
    rw [hwq]
    exact (listNext_iff_listPrev _ (ringList_nodup src dst w) p q).mp h
  · intro h
    rcases ringPrev_owner src dst q p h with ⟨w, hwq, hwp⟩
    dsimp only [ringNext, ringPrev] at h ⊢
    rw [hwq] at h
    rw [hwp]
    exact (listNext_iff_listPrev _ (ringList_nodup src dst w) p q).mpr h

def ringNb {n k : Nat} (src dst : Fin k → Fin n) :
    Node n k × Bool → Option (Node n k × Bool)
  | (p, true) => (ringNext src dst p).map (fun q => (q, false))
  | (p, false) => (ringPrev src dst p).map (fun q => (q, true))

lemma ringNb_symm {n k : Nat} (src dst : Fin k → Fin n) (u v : Node n k × Bool) :
    ringNb src dst u = some v ↔ ringNb src dst v = some u := by
  rcases u with ⟨p, b⟩
  rcases v with ⟨q, c⟩
  cases b <;> cases c <;> simp [ringNb, ringNext_iff_ringPrev]

lemma ringNb_ne_self {n k : Nat} (src dst : Fin k → Fin n) (u : Node n k × Bool) :
    ringNb src dst u ≠ some u := by
  rcases u with ⟨p, b⟩
  cases b <;> simp [ringNb]

/-- switch tips joined to opposite tips of the first occurrence -/
def c1Nb {n k : Nat} : Node n k × Bool → Option (Node n k × Bool)
  | (.arcSlot e, c) => some (.outCopy e, !c)
  | (.outCopy e, c) => some (.arcSlot e, !c)
  | _ => none

lemma c1Nb_symm {n k : Nat} (u v : Node n k × Bool) :
    c1Nb u = some v ↔ c1Nb v = some u := by
  rcases u with ⟨p, b⟩
  rcases v with ⟨q, c⟩
  cases p <;> cases b <;> cases q <;> cases c <;> simp [c1Nb, eq_comm]

lemma c1Nb_ne_self {n k : Nat} (u : Node n k × Bool) : c1Nb u ≠ some u := by
  rcases u with ⟨p, b⟩
  cases p <;> cases b <;> simp [c1Nb]

lemma c1Nb_eq_some {n k : Nat} (p q : Node n k × Bool) :
    c1Nb p = some q ↔
      (∃ e c, p = (.arcSlot e, c) ∧ q = (.outCopy e, !c)) ∨
      (∃ e c, p = (.outCopy e, c) ∧ q = (.arcSlot e, !c)) := by
  rcases p with ⟨p, c⟩
  constructor
  · intro h
    cases p with
    | base i => simp [c1Nb] at h
    | inCopy e => simp [c1Nb] at h
    | arcSlot e =>
      simp only [c1Nb, Option.some.injEq] at h
      subst h; left; exact ⟨e, c, rfl, rfl⟩
    | outCopy e =>
      simp only [c1Nb, Option.some.injEq] at h
      subst h; right; exact ⟨e, c, rfl, rfl⟩
  · rintro (⟨e, c', h1, rfl⟩ | ⟨e, c', h1, rfl⟩)
    · cases h1; rfl
    · cases h1; rfl

/-- the forbidden tip of the switch joined to the forbidden tip of the second occurrence -/
def c2Nb {n k : Nat} (a b : Fin k → Bool) : Node n k × Bool → Option (Node n k × Bool)
  | (.arcSlot e, c) => if c = a e then some (.inCopy e, b e) else none
  | (.inCopy e, c) => if c = b e then some (.arcSlot e, a e) else none
  | _ => none

lemma c2Nb_eq_some {n k : Nat} (a b : Fin k → Bool) (p q : Node n k × Bool) :
    c2Nb a b p = some q ↔
      (∃ e, p = (.arcSlot e, a e) ∧ q = (.inCopy e, b e)) ∨
      (∃ e, p = (.inCopy e, b e) ∧ q = (.arcSlot e, a e)) := by
  rcases p with ⟨p, c⟩
  constructor
  · intro h
    cases p with
    | base i => simp [c2Nb] at h
    | outCopy e => simp [c2Nb] at h
    | inCopy e =>
      simp only [c2Nb] at h
      by_cases hc : c = b e
      · rw [if_pos hc] at h
        simp only [Option.some.injEq] at h
        subst h; subst hc; right; exact ⟨e, rfl, rfl⟩
      · rw [if_neg hc] at h; cases h
    | arcSlot e =>
      simp only [c2Nb] at h
      by_cases hc : c = a e
      · rw [if_pos hc] at h
        simp only [Option.some.injEq] at h
        subst h; subst hc; left; exact ⟨e, rfl, rfl⟩
      · rw [if_neg hc] at h; cases h
  · rintro (⟨e, h1, rfl⟩ | ⟨e, h1, rfl⟩)
    · cases h1; simp [c2Nb]
    · cases h1; simp [c2Nb]

lemma c2Nb_symm {n k : Nat} (a b : Fin k → Bool) (u v : Node n k × Bool) :
    c2Nb a b u = some v ↔ c2Nb a b v = some u := by
  rw [c2Nb_eq_some, c2Nb_eq_some]
  constructor
  · rintro (⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩)
    · right; exact ⟨e, rfl, rfl⟩
    · left; exact ⟨e, rfl, rfl⟩
  · rintro (⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩)
    · right; exact ⟨e, rfl, rfl⟩
    · left; exact ⟨e, rfl, rfl⟩

lemma c2Nb_ne_self {n k : Nat} (a b : Fin k → Bool) (u : Node n k × Bool) :
    c2Nb a b u ≠ some u := by
  intro h
  rcases (c2Nb_eq_some a b u u).mp h with ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩
  · rw [h1] at h2; simp at h2
  · rw [h1] at h2; simp at h2

def nbNode {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (u : Node n k × Bool) : Finset (Node n k × Bool) :=
  {(u.1, !u.2)} ∪ (ringNb src dst u).toFinset ∪ (c1Nb u).toFinset ∪ (c2Nb a b u).toFinset

lemma nbNode_card_le {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (u : Node n k × Bool) : (nbNode src dst a b u).card ≤ 3 := by
  have h1 : ({(u.1, !u.2)} : Finset (Node n k × Bool)).card = 1 := Finset.card_singleton _
  have h2 : (ringNb src dst u).toFinset.card ≤ 1 := by
    cases ringNb src dst u <;> simp
  have h3 : (c1Nb u).toFinset.card ≤ 1 := by
    cases c1Nb u <;> simp
  have h4 : (c2Nb a b u).toFinset.card ≤ 1 := by
    cases c2Nb a b u <;> simp
  have h5 : (ringNb src dst u).toFinset.card + (c1Nb u).toFinset.card +
      (c2Nb a b u).toFinset.card ≤ 2 := by
    rcases u with ⟨p, c⟩
    cases p with
    | base i =>
      have e3 : c1Nb ((Node.base i : Node n k), c) = none := rfl
      have e4 : c2Nb a b ((Node.base i : Node n k), c) = none := rfl
      rw [e3, e4]; simp only [Option.toFinset_none, Finset.card_empty]; omega
    | outCopy e =>
      have e4 : c2Nb a b ((Node.outCopy e : Node n k), c) = none := rfl
      rw [e4]; simp only [Option.toFinset_none, Finset.card_empty]; omega
    | inCopy e =>
      have e3 : c1Nb ((Node.inCopy e : Node n k), c) = none := rfl
      rw [e3]; simp only [Option.toFinset_none, Finset.card_empty]; omega
    | arcSlot e =>
      have e2 : ringNb src dst (Node.arcSlot e, c) = none := by
        cases c <;> rfl
      rw [e2]; simp only [Option.toFinset_none, Finset.card_empty]; omega
  have hu1 := Finset.card_union_le
    ({(u.1, !u.2)} ∪ (ringNb src dst u).toFinset ∪ (c1Nb u).toFinset) (c2Nb a b u).toFinset
  have hu2 := Finset.card_union_le
    ({(u.1, !u.2)} ∪ (ringNb src dst u).toFinset) (c1Nb u).toFinset
  have hu3 := Finset.card_union_le ({(u.1, !u.2)} : Finset (Node n k × Bool))
    (ringNb src dst u).toFinset
  dsimp only [nbNode]
  omega

lemma nbNode_not_mem_self {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (u : Node n k × Bool) : u ∉ nbNode src dst a b u := by
  simp only [nbNode, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def]
  rintro (((h1 | h2) | h3) | h4)
  · rcases u with ⟨p, c⟩
    have hc : c = !c := congrArg Prod.snd h1
    cases c <;> cases hc
  · exact ringNb_ne_self src dst u h2
  · exact c1Nb_ne_self u h3
  · exact c2Nb_ne_self a b u h4

lemma nbNode_symm {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (u v : Node n k × Bool) :
    v ∈ nbNode src dst a b u ↔ u ∈ nbNode src dst a b v := by
  simp only [nbNode, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def]
  have h1 : v = (u.1, !u.2) ↔ u = (v.1, !v.2) := by
    rcases u with ⟨p, b1⟩; rcases v with ⟨q, c1⟩
    cases b1 <;> cases c1 <;> simp [eq_comm]
  rw [h1, ringNb_symm, c1Nb_symm, c2Nb_symm]

lemma nbNode_same_shore {n k : Nat} (src dst : Fin k → Fin n) (a b : Fin k → Bool)
    (c : Bool) (p q : Node n k) (h : (q, c) ∈ nbNode src dst a b (p, c)) :
    ∃ e, a e = c ∧ b e = c ∧ (p = .arcSlot e ∨ q = .arcSlot e) := by
  simp only [nbNode, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset,
    Option.mem_def] at h
  rcases h with (((h1 | h2) | h3) | h4)
  · have := congrArg Prod.snd h1
    cases c <;> simp at this
  · cases c <;> simp [ringNb] at h2
  · cases p <;> cases c <;> simp [c1Nb] at h3
  · rcases (c2Nb_eq_some a b _ _).mp h4 with ⟨e, h5, h6⟩ | ⟨e, h5, h6⟩
    · simp only [Prod.mk.injEq] at h5 h6
      exact ⟨e, h5.2.symm, h6.2.symm, Or.inl h5.1⟩
    · simp only [Prod.mk.injEq] at h5 h6
      exact ⟨e, h6.2.symm, h5.2.symm, Or.inr h6.1⟩

lemma bool_xor_or (v c : Bool) : xor v c = true ∨ xor v (!c) = true := by
  cases v <;> cases c <;> simp

lemma bool_sat (s1 s2 ae be : Bool) (h : ¬ (s1 = ae ∧ s2 = be)) :
    xor s1 ae = true ∨ xor s2 be = true := by
  cases s1 <;> cases s2 <;> cases ae <;> cases be <;> simp_all

lemma bool_switch (A B O : Bool) (h1 : xor A B = true) (h2 : A = true ∨ xor O true = true)
    (h3 : B = true ∨ xor O false = true) : A = xor O false ∧ B = xor O true := by
  cases A <;> cases B <;> cases O <;> simp_all

lemma bool_off (A B : Bool) (h1 : xor A B = false) (h2 : A = true ∨ B = true) :
    A = true ∧ B = true := by
  cases A <;> cases B <;> simp_all

theorem main (n k : Nat) (src dst : Fin k → Fin n) (a b : Fin k → Bool) :
  ∃ (m : Nat) (slot : Fin k ↪ Fin m) (read : Fin n ↪ Fin m)
    (nb : (Fin m × Bool) → Finset (Fin m × Bool)),
    m ≤ n+3*k ∧ (∀ i e, read i ≠ slot e) ∧
    (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧ (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    (∀ c i j, (j,c) ∈ nb (i,c) → ∃ e, a e = c ∧ b e = c ∧ (slot e = i ∨ slot e = j)) ∧
    ∀ z : Fin k → Bool,
      let sat := fun (y : Fin n → Bool) => ∀ e, z e = true → ¬ (y (src e) = a e ∧ y (dst e) = b e)
      let phys := fun (x : (Fin m × Bool) → Bool) =>
        (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
        (∀ e, xor (x (slot e,false)) (x (slot e,true)) = z e) ∧
        (∀ i, (∀ e, slot e ≠ i) → xor (x (i,false)) (x (i,true)) = true)
      let decode := fun (x : (Fin m × Bool) → Bool) (i : Fin n) => x (read i,false)
      (∀ x, phys x → sat (decode x)) ∧
      (∀ y, sat y → ∃! x, phys x ∧ decode x = y) := by
  let m := n + 3 * k
  let eqN : Node n k ≃ Fin m := nodeEquiv n k
  let eqP : (Node n k × Bool) ≃ (Fin m × Bool) := eqN.prodCongr (Equiv.refl Bool)
  let slot : Fin k ↪ Fin m :=
    ⟨fun e => eqN (.arcSlot e), fun e1 e2 h => by
      have h' := eqN.injective h
      cases h'; rfl⟩
  let read : Fin n ↪ Fin m :=
    ⟨fun i => eqN (.base i), fun i1 i2 h => by
      have h' := eqN.injective h
      cases h'; rfl⟩
  let nb : (Fin m × Bool) → Finset (Fin m × Bool) :=
    fun u => (nbNode src dst a b (eqP.symm u)).image eqP
  have hmem_nb : ∀ (p q : Node n k) (c1 c2 : Bool),
      (eqN q, c2) ∈ nb (eqN p, c1) ↔ (q, c2) ∈ nbNode src dst a b (p, c1) := by
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
  have hxe_gen : ∀ (f : (Fin m × Bool) → Bool) (p : Node n k) (c : Bool),
      f (eqP (p, c)) = f (eqN p, c) := fun _ _ _ => rfl
  refine ⟨m, slot, read, nb, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- read and slot are disjoint
    intro i e h
    have h' : eqN (.base i) = eqN (.arcSlot e) := h
    have h'' := eqN.injective h'
    cases h''
  · -- no self-loops and card <= 3
    intro u
    rcases u with ⟨i, c⟩
    have hi : i = eqN (eqN.symm i) := (eqN.apply_symm_apply i).symm
    constructor
    · rw [hi, hmem_nb]
      exact nbNode_not_mem_self src dst a b (eqN.symm i, c)
    · dsimp only [nb]
      exact le_trans Finset.card_image_le (nbNode_card_le src dst a b _)
  · -- symmetry
    intro u v
    rcases u with ⟨i, c1⟩; rcases v with ⟨j, c2⟩
    rw [← eqN.apply_symm_apply i, ← eqN.apply_symm_apply j, hmem_nb, hmem_nb]
    exact nbNode_symm src dst a b _ _
  · -- internal pair edges
    intro i
    rw [← eqN.apply_symm_apply i, hmem_nb]
    simp [nbNode]
  · -- same-shore edges
    intro c i j h
    rw [← eqN.apply_symm_apply i, ← eqN.apply_symm_apply j, hmem_nb] at h
    rcases nbNode_same_shore src dst a b c _ _ h with ⟨e, ha, hb, hor⟩
    refine ⟨e, ha, hb, ?_⟩
    rcases hor with h1 | h1
    · left
      change eqN (.arcSlot e) = i
      rw [← h1, eqN.apply_symm_apply]
    · right
      change eqN (.arcSlot e) = j
      rw [← h1, eqN.apply_symm_apply]
  · -- solution correspondence
    intro z sat phys decode
    have hfacts : ∀ x : (Fin m × Bool) → Bool, phys x →
        (∀ (p : Node n k) (w : Fin n), owner src dst p = some w →
            ∀ c, x (eqP (p, c)) = xor (x (eqP (.base w, false))) c) ∧
        (∀ e, z e = true → ∀ c,
            x (eqP (.arcSlot e, c)) = xor (x (eqP (.base (src e), false))) c) ∧
        (∀ e, z e = false → ∀ c, x (eqP (.arcSlot e, c)) = true) ∧
        (∀ e, z e = true →
            ¬ (x (eqP (.base (src e), false)) = a e ∧ x (eqP (.base (dst e), false)) = b e)) := by
      intro x hx
      obtain ⟨hcov, hslot, hnonslot⟩ := hx
      let xN : Node n k × Bool → Bool := fun p => x (eqP p)
      have hcovN : ∀ p q, q ∈ nbNode src dst a b p → xN p = true ∨ xN q = true := by
        intro p q hqp
        rcases p with ⟨p, c1⟩; rcases q with ⟨q, c2⟩
        apply hcov (eqN p, c1) (eqN q, c2)
        rw [hmem_nb]
        exact hqp
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
      have hring_step : ∀ (w : Fin n) (p q : Node n k),
          owner src dst p = some w → ringNext src dst p = some q →
          xN (p, false) = true → xN (q, false) = true := by
        intro w p q hwp hnext hpf
        have hp_ns : ∀ e, p ≠ .arcSlot e := by intro e he; subst he; simp [owner] at hwp
        have hpt : xN (p, true) = false := by rw [hns_true p hp_ns, hpf]; rfl
        have hmem : (q, false) ∈ nbNode src dst a b (p, true) := by
          simp [nbNode, ringNb, hnext]
        rcases hcovN (p, true) (q, false) hmem with h1 | h2
        · rw [hpt] at h1; cases h1
        · exact h2
      have hring_all : ∀ (w : Fin n) (p q : Node n k),
          owner src dst p = some w → owner src dst q = some w →
          xN (p, false) = true → xN (q, false) = true := by
        intro w p q hwp hwq hpf
        let L := ringList src dst w
        have hpL : p ∈ L := (mem_ringList_iff src dst w p).mpr hwp
        have hqL : q ∈ L := (mem_ringList_iff src dst w q).mpr hwq
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
              have hown_j : owner src dst (L[j]'hj) = some w :=
                (mem_ringList_iff src dst w _).mp (List.getElem_mem hj)
              have hidx_j : L.idxOf (L[j]'hj) = j :=
                List.Nodup.idxOf_getElem (ringList_nodup src dst w) j hj
              have hnext_j : ringNext src dst (L[j]'hj) =
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
            have heq : L.idxOf p + (L.idxOf q + L.length - L.idxOf p) =
                L.idxOf q + L.length := by
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
          | cons a1 tl =>
            cases tl with
            | nil =>
              rw [hL] at hpL hqL
              simp at hpL hqL
              subst hpL; subst hqL
              exact hpf
            | cons b1 tl2 => simp [hL] at hlen1
      have hring_eq : ∀ (w : Fin n) (p : Node n k), owner src dst p = some w →
          xN (p, false) = xN (.base w, false) := by
        intro w p hwp
        cases hpv : xN (p, false) <;> cases hbv : xN (.base w, false)
        · rfl
        · have h := hring_all w (.base w) p rfl hwp hbv
          rw [hpv] at h; cases h
        · have h := hring_all w p (.base w) hwp rfl hpv
          rw [hbv] at h; cases h
        · rfl
      have F1 : ∀ (p : Node n k) (w : Fin n), owner src dst p = some w →
          ∀ c, xN (p, c) = xor (xN (.base w, false)) c := by
        intro p w hwp c
        have hp_ns : ∀ e, p ≠ .arcSlot e := by intro e he; subst he; simp [owner] at hwp
        cases c
        · rw [hring_eq w p hwp]; simp
        · rw [hns_true p hp_ns, hring_eq w p hwp]; simp
      have F2 : ∀ e, z e = true → ∀ c,
          xN (.arcSlot e, c) = xor (xN (.base (src e), false)) c := by
        intro e hze
        have hx : xor (xN (.arcSlot e, false)) (xN (.arcSlot e, true)) = z e := hslot e
        rw [hze] at hx
        have hm1 : (Node.outCopy e, true) ∈ nbNode src dst a b (.arcSlot e, false) := by
          simp [nbNode, c1Nb]
        have hm2 : (Node.outCopy e, false) ∈ nbNode src dst a b (.arcSlot e, true) := by
          simp [nbNode, c1Nb]
        have h1 := hcovN _ _ hm1
        have h2 := hcovN _ _ hm2
        have ho := F1 (.outCopy e) (src e) rfl
        rw [ho true] at h1
        rw [ho false] at h2
        have key := bool_switch _ _ _ hx h1 h2
        intro c
        cases c
        · exact key.1
        · exact key.2
      have F3 : ∀ e, z e = false → ∀ c, xN (.arcSlot e, c) = true := by
        intro e hze
        have hx : xor (xN (.arcSlot e, false)) (xN (.arcSlot e, true)) = z e := hslot e
        rw [hze] at hx
        have hm : (Node.arcSlot e, true) ∈ nbNode src dst a b (.arcSlot e, false) := by
          simp [nbNode]
        have key := bool_off _ _ hx (hcovN _ _ hm)
        intro c
        cases c
        · exact key.1
        · exact key.2
      have F4 : ∀ e, z e = true →
          ¬ (xN (.base (src e), false) = a e ∧ xN (.base (dst e), false) = b e) := by
        intro e hze hcon
        rcases hcon with ⟨h1, h2⟩
        have hm : (Node.inCopy e, b e) ∈ nbNode src dst a b (.arcSlot e, a e) := by
          simp [nbNode, c2Nb]
        have hc := hcovN _ _ hm
        rw [F2 e hze, F1 (.inCopy e) (dst e) rfl, h1, h2] at hc
        simp at hc
      exact ⟨F1, F2, F3, F4⟩
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · obtain ⟨_, _, _, F4⟩ := hfacts x hx
      intro e hze hcon
      exact F4 e hze hcon
    · let xNode : Node n k × Bool → Bool := fun pc =>
        match pc.1 with
        | .base i => xor (y i) pc.2
        | .outCopy e => xor (y (src e)) pc.2
        | .inCopy e => xor (y (dst e)) pc.2
        | .arcSlot e => if z e = true then xor (y (src e)) pc.2 else true
      have hx_own : ∀ (p : Node n k) (w : Fin n) (c : Bool),
          owner src dst p = some w → xNode (p, c) = xor (y w) c := by
        intro p w c hown
        cases p with
        | base i => simp only [owner, Option.some.injEq] at hown; subst hown; rfl
        | outCopy e => simp only [owner, Option.some.injEq] at hown; subst hown; rfl
        | inCopy e => simp only [owner, Option.some.injEq] at hown; subst hown; rfl
        | arcSlot e => simp [owner] at hown
      have hx_on : ∀ e c, z e = true → xNode (.arcSlot e, c) = xor (y (src e)) c := by
        intro e c hz
        show (if z e = true then xor (y (src e)) c else true) = _
        rw [if_pos hz]
      have hx_off : ∀ e c, z e = false → xNode (.arcSlot e, c) = true := by
        intro e c hz
        show (if z e = true then xor (y (src e)) c else true) = _
        rw [if_neg (by simp [hz])]
      have hcovNode : ∀ p q : Node n k × Bool, q ∈ nbNode src dst a b p →
          xNode p = true ∨ xNode q = true := by
        intro p q hmem
        simp only [nbNode, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset,
          Option.mem_def] at hmem
        rcases p with ⟨p, c⟩
        rcases hmem with (((h1 | h2) | h3) | h4)
        · -- internal pair edge
          subst h1
          dsimp only
          cases p with
          | base i =>
            rw [hx_own (.base i) i c rfl, hx_own (.base i) i (!c) rfl]
            exact bool_xor_or _ _
          | outCopy e =>
            rw [hx_own (.outCopy e) (src e) c rfl, hx_own (.outCopy e) (src e) (!c) rfl]
            exact bool_xor_or _ _
          | inCopy e =>
            rw [hx_own (.inCopy e) (dst e) c rfl, hx_own (.inCopy e) (dst e) (!c) rfl]
            exact bool_xor_or _ _
          | arcSlot e =>
            cases hz : z e
            · left; exact hx_off e c hz
            · rw [hx_on e c hz, hx_on e (!c) hz]
              exact bool_xor_or _ _
        · -- ring edge
          cases c
          · simp only [ringNb, Option.map_eq_some_iff] at h2
            rcases h2 with ⟨q', hprev, heq⟩
            subst heq
            rcases ringPrev_owner src dst p q' hprev with ⟨w, hwp, hwq⟩
            rw [hx_own p w false hwp, hx_own q' w true hwq]
            exact bool_xor_or (y w) false
          · simp only [ringNb, Option.map_eq_some_iff] at h2
            rcases h2 with ⟨q', hnext, heq⟩
            subst heq
            rcases ringNext_owner src dst p q' hnext with ⟨w, hwp, hwq⟩
            rw [hx_own p w true hwp, hx_own q' w false hwq]
            exact bool_xor_or (y w) true
        · -- switch to first occurrence
          rcases (c1Nb_eq_some _ _).mp h3 with ⟨e, c', h5, rfl⟩ | ⟨e, c', h5, rfl⟩
          · simp only [Prod.mk.injEq] at h5
            obtain ⟨rfl, rfl⟩ := h5
            rw [hx_own (.outCopy e) (src e) (!c) rfl]
            cases hz : z e
            · left; exact hx_off e c hz
            · rw [hx_on e c hz]; exact bool_xor_or _ _
          · simp only [Prod.mk.injEq] at h5
            obtain ⟨rfl, rfl⟩ := h5
            rw [hx_own (.outCopy e) (src e) c rfl]
            cases hz : z e
            · right; exact hx_off e (!c) hz
            · rw [hx_on e (!c) hz]; exact bool_xor_or _ _
        · -- forbidden edge
          rcases (c2Nb_eq_some a b _ _).mp h4 with ⟨e, h5, rfl⟩ | ⟨e, h5, rfl⟩
          · simp only [Prod.mk.injEq] at h5
            obtain ⟨rfl, rfl⟩ := h5
            rw [hx_own (.inCopy e) (dst e) (b e) rfl]
            cases hz : z e
            · left; exact hx_off e (a e) hz
            · rw [hx_on e (a e) hz]; exact bool_sat _ _ _ _ (hy e hz)
          · simp only [Prod.mk.injEq] at h5
            obtain ⟨rfl, rfl⟩ := h5
            rw [hx_own (.inCopy e) (dst e) (b e) rfl]
            cases hz : z e
            · right; exact hx_off e (a e) hz
            · rw [hx_on e (a e) hz]; exact (bool_sat _ _ _ _ (hy e hz)).symm
      let x : (Fin m × Bool) → Bool := fun q => xNode (eqP.symm q)
      have hxe : ∀ p : Node n k × Bool, x (eqP p) = xNode p := by
        intro p
        show xNode (eqP.symm (eqP p)) = xNode p
        rw [Equiv.symm_apply_apply]
      have hphys : phys x := by
        show (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
          (∀ e, xor (x (slot e,false)) (x (slot e,true)) = z e) ∧
          (∀ i, (∀ e, slot e ≠ i) → xor (x (i,false)) (x (i,true)) = true)
        refine ⟨?_, ?_, ?_⟩
        · intro p q hqp
          obtain ⟨p', rfl⟩ := eqP.surjective p
          obtain ⟨q', rfl⟩ := eqP.surjective q
          rw [hxe, hxe]
          apply hcovNode
          rcases p' with ⟨p1, c1⟩; rcases q' with ⟨q1, c2⟩
          exact (hmem_nb p1 q1 c1 c2).mp hqp
        · intro e
          show xor (x (eqP (.arcSlot e, false))) (x (eqP (.arcSlot e, true))) = z e
          rw [hxe, hxe]
          cases hz : z e
          · rw [hx_off e false hz, hx_off e true hz]; rfl
          · rw [hx_on e false hz, hx_on e true hz]
            cases y (src e) <;> rfl
        · intro i hi
          obtain ⟨p', rfl⟩ := eqN.surjective i
          show xor (x (eqP (p', false))) (x (eqP (p', true))) = true
          rw [hxe, hxe]
          cases p' with
          | arcSlot e => exact (hi e rfl).elim
          | base j =>
            rw [hx_own (.base j) j false rfl, hx_own (.base j) j true rfl]
            cases y j <;> rfl
          | outCopy e =>
            rw [hx_own (.outCopy e) (src e) false rfl, hx_own (.outCopy e) (src e) true rfl]
            cases y (src e) <;> rfl
          | inCopy e =>
            rw [hx_own (.inCopy e) (dst e) false rfl, hx_own (.inCopy e) (dst e) true rfl]
            cases y (dst e) <;> rfl
      have hdec : decode x = y := by
        funext i
        show x (eqP (.base i, false)) = y i
        rw [hxe, hx_own (.base i) i false rfl, Bool.xor_false]
      refine ⟨x, ⟨hphys, hdec⟩, ?_⟩
      rintro x' ⟨hphys', hdec'⟩
      obtain ⟨F1, F2, F3, _⟩ := hfacts x' hphys'
      have hy' : ∀ w, x' (eqP (.base w, false)) = y w := fun w => congrFun hdec' w
      funext q
      obtain ⟨⟨p, c⟩, rfl⟩ := eqP.surjective q
      rw [hxe]
      cases p with
      | base i => rw [F1 (.base i) i rfl c, hy' i, hx_own (.base i) i c rfl]
      | outCopy e =>
        rw [F1 (.outCopy e) (src e) rfl c, hy' (src e), hx_own (.outCopy e) (src e) c rfl]
      | inCopy e =>
        rw [F1 (.inCopy e) (dst e) rfl c, hy' (dst e), hx_own (.inCopy e) (dst e) c rfl]
      | arcSlot e =>
        cases hz : z e
        · rw [F3 e hz c, hx_off e c hz]
        · rw [F2 e hz c, hy' (src e), hx_on e c hz]

end PEqualNP.Outside.L_lib_1197_aux

theorem PEqualNP.Outside.L_lib_1197 : ∀ (n k : Nat) (u v : Fin k → Fin n) (a b : Fin k → Bool),
  ∃ (m : Nat) (slot : Fin k ↪ Fin m) (read : Fin n ↪ Fin m)
    (nb : (Fin m × Bool) → Finset (Fin m × Bool)),
    m ≤ n+3*k ∧ (∀ i e, read i ≠ slot e) ∧
    (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧ (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    (∀ c i j, (j,c) ∈ nb (i,c) → ∃ e, a e = c ∧ b e = c ∧ (slot e = i ∨ slot e = j)) ∧
    ∀ z : Fin k → Bool,
      let sat := fun (y : Fin n → Bool) => ∀ e, z e = true → ¬ (y (u e) = a e ∧ y (v e) = b e)
      let phys := fun (x : (Fin m × Bool) → Bool) =>
        (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
        (∀ e, xor (x (slot e,false)) (x (slot e,true)) = z e) ∧
        (∀ i, (∀ e, slot e ≠ i) → xor (x (i,false)) (x (i,true)) = true)
      let decode := fun (x : (Fin m × Bool) → Bool) (i : Fin n) => x (read i,false)
      (∀ x, phys x → sat (decode x)) ∧
      (∀ y, sat y → ∃! x, phys x ∧ decode x = y) := by
  intro n k u v a b
  exact PEqualNP.Outside.L_lib_1197_aux.main n k u v a b
