import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_230_aux

open PEqualNP.ProofComplexity PEqualNP.Search

private abbrev Var (n w : ℕ) := Sum (Fin n) (Fin n × (Fin (w + 1) → Bool))

private def acceptsPred {n w : ℕ} (hn : 0 < n) (a : Var n w → Bool) : Prop :=
  ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
    a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true

private def rotWord {n : ℕ} (hn : 0 < n) (i : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun t => x ⟨(i.val + t.val) % n, Nat.mod_lt _ hn⟩

private def unrotWord {n : ℕ} (hn : 0 < n) (i : Fin n) (y : Fin n → Bool) : Fin n → Bool :=
  fun k => y ⟨(k.val + n - i.val) % n, Nat.mod_lt _ hn⟩

private lemma rotWord_unrotWord {n : ℕ} (hn : 0 < n) (i : Fin n) (y : Fin n → Bool) :
    rotWord hn i (unrotWord hn i y) = y := by
  funext t
  dsimp only [rotWord, unrotWord]
  congr 1
  ext
  dsimp only
  have hi : i.val < n := i.isLt
  have ht : t.val < n := t.isLt
  have h1 : (i.val + t.val) % n + n - i.val = (i.val + t.val) % n + (n - i.val) := by omega
  rw [h1, Nat.mod_add_mod]
  have h2 : i.val + t.val + (n - i.val) = t.val + n := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt ht]

private lemma unrotWord_rotWord {n : ℕ} (hn : 0 < n) (i : Fin n) (x : Fin n → Bool) :
    unrotWord hn i (rotWord hn i x) = x := by
  funext k
  dsimp only [rotWord, unrotWord]
  congr 1
  ext
  dsimp only
  have hi : i.val < n := i.isLt
  have hk : k.val < n := k.isLt
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h1 : i.val + (k.val + n - i.val) = k.val + n := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hk]

private def win {n w : ℕ} (hn : 0 < n) (i : Fin n) (x : Fin n → Bool) : Fin (w + 1) → Bool :=
  fun j => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

private def extPat {n w : ℕ} (hn : 0 < n) (q : Fin (min n (w + 1)) → Bool) :
    Fin (w + 1) → Bool :=
  fun j => q ⟨j.val % min n (w + 1), Nat.mod_lt _ (Nat.lt_min.mpr ⟨hn, Nat.succ_pos w⟩)⟩

private lemma extPat_injective {n w : ℕ} (hn : 0 < n) :
    Function.Injective (extPat (n := n) (w := w) hn) := by
  intro q₁ q₂ heq
  funext t
  have ht_w : t.val < w + 1 := lt_of_lt_of_le t.isLt (Nat.min_le_right n (w + 1))
  have h := congrFun heq ⟨t.val, ht_w⟩
  dsimp only [extPat] at h
  have hmod : t.val % min n (w + 1) = t.val := Nat.mod_eq_of_lt t.isLt
  have hfin : (⟨t.val % min n (w + 1), Nat.mod_lt _ (Nat.lt_min.mpr ⟨hn, Nat.succ_pos w⟩)⟩ :
      Fin (min n (w + 1))) = t := Fin.ext hmod
  rwa [hfin] at h

private lemma win_eq_extPat {n w : ℕ} (hn : 0 < n) (i : Fin n) (x : Fin n → Bool) :
    win (w := w) hn i x =
      extPat hn (fun t : Fin (min n (w + 1)) =>
        rotWord hn i x ⟨t.val, lt_of_lt_of_le t.isLt (Nat.min_le_left n (w + 1))⟩) := by
  funext j
  dsimp only [win, extPat, rotWord]
  congr 1
  ext
  by_cases hle : n ≤ w + 1
  · have hmin : min n (w + 1) = n := Nat.min_eq_left hle
    simp only [hmin]
    simp [Nat.add_mod]
  · have hmin : min n (w + 1) = w + 1 := Nat.min_eq_right (by omega)
    simp only [hmin, Nat.mod_eq_of_lt j.isLt]

private lemma realizable_iff_exists_extPat {n w : ℕ} (hn : 0 < n) (i : Fin n)
    (p : Fin (w + 1) → Bool) :
    (∃ x : Fin n → Bool, ∀ j : Fin (w + 1), x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ = p j) ↔
    ∃ q : Fin (min n (w + 1)) → Bool, extPat hn q = p := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun t => rotWord hn i x ⟨t.val, lt_of_lt_of_le t.isLt (Nat.min_le_left n (w + 1))⟩, ?_⟩
    rw [← win_eq_extPat hn i x]
    funext j
    exact hx j
  · rintro ⟨q, rfl⟩
    let y : Fin n → Bool := fun t =>
      if h : t.val < min n (w + 1) then q ⟨t.val, h⟩ else false
    refine ⟨unrotWord hn i y, fun j => ?_⟩
    change win (w := w) hn i (unrotWord hn i y) j = extPat hn q j
    rw [win_eq_extPat hn i (unrotWord hn i y), rotWord_unrotWord hn i y]
    dsimp only [extPat, y]
    have hlt : j.val % min n (w + 1) < min n (w + 1) :=
      Nat.mod_lt _ (Nat.lt_min.mpr ⟨hn, Nat.succ_pos w⟩)
    simp only [hlt, ↓reduceDIte]

private abbrev NodeIdx (n : ℕ) := Σ d : Fin (n - 1), (Fin (d.val + 1) → Bool)

private abbrev AuxVar (n : ℕ) := Sum (Fin n → Bool) (Fin n × NodeIdx n)

private lemma card_nodeIdx (n : ℕ) (hn : 0 < n) :
    Fintype.card (NodeIdx n) = 2 ^ n - 2 := by
  rw [Fintype.card_sigma]
  have hterm : ∀ d : Fin (n - 1), Fintype.card (Fin (d.val + 1) → Bool) = 2 ^ (d.val + 1) := by
    intro d; simp [Fintype.card_pi]
  simp_rw [hterm]
  have hsum : ∀ m : ℕ, (∑ d : Fin m, 2 ^ (d.val + 1)) = 2 ^ (m + 1) - 2 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc, Fin.val_last]
      simp only [Fin.val_castSucc]
      rw [ih]
      have h1 : 2 ≤ 2 ^ (m + 1) := by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ m + 1)
        simpa using this
      have h2 : 2 ^ (m + 1 + 1) = 2 ^ (m + 1) + 2 ^ (m + 1) := by ring
      omega
  rw [hsum (n - 1)]
  have : n - 1 + 1 = n := by omega
  rw [this]

private lemma card_auxVar (n : ℕ) (hn : 0 < n) :
    Fintype.card (AuxVar n) = 2 ^ n + n * (2 ^ n - 2) := by
  rw [Fintype.card_sum, Fintype.card_prod, card_nodeIdx n hn]
  simp [Fintype.card_pi]

private def mkIdx {n : ℕ} (d : ℕ) (hd1 : 1 ≤ d) (hdlt : d < n) (pref : Fin d → Bool) :
    NodeIdx n :=
  ⟨⟨d - 1, by omega⟩, fun t => pref ⟨t.val, by have := t.isLt; dsimp at this; omega⟩⟩

private def nodeVar {n : ℕ} (hn : 0 < n) (i : Fin n) (d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n)
    (pref : Fin d → Bool) : AuxVar n :=
  if h : d < n then
    Sum.inr (i, mkIdx d hd1 h pref)
  else
    Sum.inl (unrotWord hn i (fun t => pref ⟨t.val, by omega⟩))

private lemma nodeVar_lt {n : ℕ} (hn : 0 < n) (i : Fin n) (d : ℕ) (hd1 : 1 ≤ d) (hdlt : d < n)
    (pref : Fin d → Bool) :
    nodeVar hn i d hd1 (le_of_lt hdlt) pref = Sum.inr (i, mkIdx d hd1 hdlt pref) := by
  simp [nodeVar, hdlt]

private lemma nodeVar_eq {n : ℕ} (hn : 0 < n) (i : Fin n) (pref : Fin n → Bool) :
    nodeVar hn i n hn (le_refl n) pref = Sum.inl (unrotWord hn i pref) := by
  simp [nodeVar]

private lemma nodeVar_congr {n : ℕ} (hn : 0 < n) (i : Fin n)
    {d1 d2 : ℕ} (he : d1 = d2) (h1a : 1 ≤ d1) (h1b : d1 ≤ n)
    (h2a : 1 ≤ d2) (h2b : d2 ≤ n) (p1 : Fin d1 → Bool) (p2 : Fin d2 → Bool)
    (hp : ∀ j (hj1 : j < d1) (hj2 : j < d2), p1 ⟨j, hj1⟩ = p2 ⟨j, hj2⟩) :
    nodeVar hn i d1 h1a h1b p1 = nodeVar hn i d2 h2a h2b p2 := by
  subst he
  have hpeq : p1 = p2 := funext fun t => hp t.val t.isLt t.isLt
  subst hpeq
  rfl

private def extBit {d : ℕ} (pref : Fin d → Bool) (b : Bool) : Fin (d + 1) → Bool :=
  fun t => if h : t.val < d then pref ⟨t.val, h⟩ else b

private lemma nodeVar_extBit_idx {n : ℕ} (hn : 0 < n) (i : Fin n) {d : ℕ}
    (hd1 : 1 ≤ d) (hdlt : d < n) (pref : Fin d → Bool) (c : Bool) :
    nodeVar hn i ((mkIdx d hd1 hdlt pref).1.val + 2) (by omega) (by
        have hlt := (mkIdx d hd1 hdlt pref).1.isLt; omega)
        (extBit (mkIdx d hd1 hdlt pref).2 c) =
      nodeVar hn i (d + 1) (by omega) (by omega) (extBit pref c) := by
  have heq : (mkIdx d hd1 hdlt pref).1.val + 2 = d + 1 := by
    dsimp [mkIdx]; omega
  refine nodeVar_congr hn i heq _ _ _ _ _ _ fun j hj1 hj2 => ?_
  dsimp only [extBit, mkIdx]
  by_cases hjd : j < d
  · have hjd1 : j < d - 1 + 1 := by omega
    simp only [hjd, hjd1, ↓reduceDIte]
  · have hjd1 : ¬ j < d - 1 + 1 := by omega
    simp only [hjd, hjd1, ↓reduceDIte]

private def matchesPref {n : ℕ} (hn : 0 < n) (i : Fin n) {d : ℕ} (hdn : d ≤ n)
    (pref : Fin d → Bool) (x : Fin n → Bool) : Prop :=
  ∀ t : Fin d, rotWord hn i x ⟨t.val, lt_of_lt_of_le t.isLt hdn⟩ = pref t

private lemma matchesPref_extBit {n : ℕ} (hn : 0 < n) (i : Fin n) {d : ℕ} (hd : d < n)
    (pref : Fin d → Bool) (b : Bool) (x : Fin n → Bool) :
    matchesPref hn i (Nat.succ_le_of_lt hd) (extBit pref b) x ↔
      matchesPref hn i (le_of_lt hd) pref x ∧ rotWord hn i x ⟨d, hd⟩ = b := by
  constructor
  · intro h
    refine ⟨fun t => ?_, ?_⟩
    · have h1 := h ⟨t.val, by omega⟩
      simpa [extBit, t.isLt] using h1
    · have h1 := h ⟨d, by omega⟩
      simpa [extBit] using h1
  · rintro ⟨hm, hlast⟩ t
    by_cases ht : t.val < d
    · simpa [extBit, ht] using hm ⟨t.val, ht⟩
    · have heq : t.val = d := by omega
      have hfin : (⟨t.val, lt_of_lt_of_le t.isLt (Nat.succ_le_of_lt hd)⟩ : Fin n) = ⟨d, hd⟩ :=
        Fin.ext heq
      rw [hfin]
      simpa [extBit, ht] using hlast

private lemma matchesPref_full_iff {n : ℕ} (hn : 0 < n) (i : Fin n)
    (pref : Fin n → Bool) (x : Fin n → Bool) :
    matchesPref hn i (le_refl n) pref x ↔ x = unrotWord hn i pref := by
  constructor
  · intro hm
    have hrot : rotWord hn i x = pref := funext fun t => hm t
    rw [← unrotWord_rotWord hn i x, hrot]
  · rintro rfl t
    change rotWord hn i (unrotWord hn i pref) t = pref t
    rw [rotWord_unrotWord hn i pref]

private lemma upForces_sound {α : Type} {Γ : Set (Clause α)} {A : Set (Literal α)}
    {l : Literal α} (hup : UPForces Γ A l) {σ : α → Bool}
    (hΓ : Satisfies σ Γ) (hA : ∀ l' ∈ A, σ l'.1 = l'.2) :
    σ l.1 = l.2 := by
  induction hup with
  | hyp hmem => exact hA _ hmem
  | @unit D l₀ hD hl _ ih =>
    rcases hΓ D hD with ⟨l', hl'D, hl'sat⟩
    by_cases heq : l' = l₀
    · rwa [← heq]
    · have hneg := ih l' hl'D heq
      dsimp only [negLit] at hneg
      rw [hl'sat] at hneg
      cases l'.2 <;> simp at hneg

private lemma sum_card_union_le {α : Type} [DecidableEq α] (s₁ s₂ : Finset (Finset α)) :
    (∑ D ∈ s₁ ∪ s₂, D.card) ≤ (∑ D ∈ s₁, D.card) + (∑ D ∈ s₂, D.card) := by
  have h1 : (∑ D ∈ s₁ ∪ s₂, D.card) + (∑ D ∈ s₁ ∩ s₂, D.card) =
      (∑ D ∈ s₁, D.card) + (∑ D ∈ s₂, D.card) := Finset.sum_union_inter
  omega

private lemma sum_card_biUnion_le {ι α : Type} [DecidableEq α] (s : Finset ι)
    (f : ι → Finset (Finset α)) :
    (∑ D ∈ s.biUnion f, D.card) ≤ ∑ i ∈ s, ∑ D ∈ f i, D.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact le_trans (sum_card_union_le _ _) (Nat.add_le_add_left ih _)

private noncomputable abbrev mAux (n : ℕ) : ℕ := Fintype.card (AuxVar n)

private noncomputable def eAux (n : ℕ) : AuxVar n ≃ Fin (mAux n) :=
  Fintype.equivFin (AuxVar n)

private noncomputable def auxLit {n w : ℕ} (v : AuxVar n) (b : Bool) :
    Literal (Sum (Var n w) (Fin (mAux n))) :=
  (Sum.inr (eAux n v), b)

private noncomputable def cLeft {n w : ℕ} (hn : 0 < n) (i : Fin n) (idx : NodeIdx n) :
    Clause (Sum (Var n w) (Fin (mAux n))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  { auxLit (nodeVar hn i (idx.1.val + 2) (by omega) (by omega) (extBit idx.2 false)) false,
    auxLit (Sum.inr (i, idx)) true }

private noncomputable def cRight {n w : ℕ} (hn : 0 < n) (i : Fin n) (idx : NodeIdx n) :
    Clause (Sum (Var n w) (Fin (mAux n))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  { auxLit (nodeVar hn i (idx.1.val + 2) (by omega) (by omega) (extBit idx.2 true)) false,
    auxLit (Sum.inr (i, idx)) true }

private noncomputable def cUp {n w : ℕ} (hn : 0 < n) (i : Fin n) (idx : NodeIdx n) :
    Clause (Sum (Var n w) (Fin (mAux n))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  { auxLit (Sum.inr (i, idx)) false,
    auxLit (nodeVar hn i (idx.1.val + 2) (by omega) (by omega) (extBit idx.2 false)) true,
    auxLit (nodeVar hn i (idx.1.val + 2) (by omega) (by omega) (extBit idx.2 true)) true }

private noncomputable def tseitinNode {n w : ℕ} (hn : 0 < n) (p : Fin n × NodeIdx n) :
    Finset (Clause (Sum (Var n w) (Fin (mAux n)))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  { cLeft hn p.1 p.2, cRight hn p.1 p.2, cUp hn p.1 p.2 }

private noncomputable def F_ts {n w : ℕ} (hn : 0 < n) :
    Finset (Clause (Sum (Var n w) (Fin (mAux n)))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  Finset.univ.biUnion (tseitinNode hn)

private noncomputable def topClause {n w : ℕ} (hn : 0 < n) (i : Fin n) :
    Clause (Sum (Var n w) (Fin (mAux n))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  { auxLit (nodeVar hn i 1 (le_refl 1) hn (fun _ => false)) true,
    auxLit (nodeVar hn i 1 (le_refl 1) hn (fun _ => true)) true }

private noncomputable def F_top {n w : ℕ} (hn : 0 < n) :
    Finset (Clause (Sum (Var n w) (Fin (mAux n)))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  Finset.univ.image (topClause hn)

private noncomputable def bitClause {n w : ℕ} (hn : 0 < n) (i : Fin n) (b : Bool) :
    Clause (Sum (Var n w) (Fin (mAux n))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  { auxLit (nodeVar hn i 1 (le_refl 1) hn (fun _ => b)) false,
    (Sum.inl (Sum.inl i), b) }

private noncomputable def F_bit {n w : ℕ} (hn : 0 < n) :
    Finset (Clause (Sum (Var n w) (Fin (mAux n)))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  (Finset.univ : Finset (Fin n × Bool)).image (fun p => bitClause hn p.1 p.2)

private noncomputable def permClause {n w : ℕ} (hn : 0 < n) (i : Fin n)
    (q : Fin (min n (w + 1)) → Bool) :
    Clause (Sum (Var n w) (Fin (mAux n))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  have hr1 : 1 ≤ min n (w + 1) := Nat.le_min.mpr ⟨hn, Nat.succ_le_succ (Nat.zero_le w)⟩
  have hrn : min n (w + 1) ≤ n := Nat.min_le_left n (w + 1)
  { auxLit (nodeVar hn i (min n (w + 1)) hr1 hrn q) false,
    (Sum.inl (Sum.inr (i, extPat hn q)), true) }

private noncomputable def F_perm {n w : ℕ} (hn : 0 < n) :
    Finset (Clause (Sum (Var n w) (Fin (mAux n)))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  (Finset.univ : Finset (Fin n × (Fin (min n (w + 1)) → Bool))).image
    (fun p => permClause hn p.1 p.2)

private noncomputable def F_all {n w : ℕ} (hn : 0 < n) :
    Finset (Clause (Sum (Var n w) (Fin (mAux n)))) :=
  letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  F_ts hn ∪ F_top hn ∪ F_bit hn ∪ F_perm hn

private lemma mem_F_all_cases {n w : ℕ} (hn : 0 < n)
    {D : Clause (Sum (Var n w) (Fin (mAux n)))} (hD : D ∈ F_all hn) :
    D ∈ F_ts hn ∨ D ∈ F_top hn ∨ D ∈ F_bit hn ∨ D ∈ F_perm hn := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  simp only [F_all, Finset.mem_union] at hD
  tauto

private lemma mem_F_ts {n w : ℕ} (hn : 0 < n) (i : Fin n) (idx : NodeIdx n) :
    cLeft (w := w) hn i idx ∈ F_all hn ∧
    cRight (w := w) hn i idx ∈ F_all hn ∧
    cUp (w := w) hn i idx ∈ F_all hn := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  have hsub : tseitinNode (w := w) hn (i, idx) ⊆ F_all hn := by
    intro D hD
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨(i, idx), Finset.mem_univ _, hD⟩)))
  exact ⟨hsub (by simp [tseitinNode]), hsub (by simp [tseitinNode]), hsub (by simp [tseitinNode])⟩

private lemma mem_F_top {n w : ℕ} (hn : 0 < n) (i : Fin n) :
    topClause (w := w) hn i ∈ F_all hn := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))))

private lemma mem_F_bit {n w : ℕ} (hn : 0 < n) (i : Fin n) (b : Bool) :
    bitClause (w := w) hn i b ∈ F_all hn := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, rfl⟩))

private lemma mem_F_perm {n w : ℕ} (hn : 0 < n) (i : Fin n) (q : Fin (min n (w + 1)) → Bool) :
    permClause (w := w) hn i q ∈ F_all hn := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, q), Finset.mem_univ _, rfl⟩)

private lemma card_cLeft {n w : ℕ} (hn : 0 < n) (i : Fin n) (idx : NodeIdx n) :
    (cLeft (w := w) hn i idx).card ≤ 2 := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  exact le_trans (Finset.card_insert_le _ _) (by simp)

private lemma card_cRight {n w : ℕ} (hn : 0 < n) (i : Fin n) (idx : NodeIdx n) :
    (cRight (w := w) hn i idx).card ≤ 2 := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  exact le_trans (Finset.card_insert_le _ _) (by simp)

private lemma card_cUp {n w : ℕ} (hn : 0 < n) (i : Fin n) (idx : NodeIdx n) :
    (cUp (w := w) hn i idx).card ≤ 3 := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  exact le_trans (Finset.card_insert_le _ _)
    (Nat.add_le_add_right (le_trans (Finset.card_insert_le _ _) (by simp)) 1)

private lemma card_top {n w : ℕ} (hn : 0 < n) (i : Fin n) :
    (topClause (w := w) hn i).card ≤ 2 := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  exact le_trans (Finset.card_insert_le _ _) (by simp)

private lemma card_bit {n w : ℕ} (hn : 0 < n) (i : Fin n) (b : Bool) :
    (bitClause (w := w) hn i b).card ≤ 2 := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  exact le_trans (Finset.card_insert_le _ _) (by simp)

private lemma card_perm {n w : ℕ} (hn : 0 < n) (i : Fin n) (q : Fin (min n (w + 1)) → Bool) :
    (permClause (w := w) hn i q).card ≤ 2 := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  exact le_trans (Finset.card_insert_le _ _) (by simp)

private lemma size_bound {n w : ℕ} (hn : 0 < n) :
    mAux n + (∑ D ∈ F_all (w := w) hn, D.card) + 3 * n ≤
      (8 * n + 1) * 2 ^ n + 2 * n * 2 ^ (min n (w + 1)) := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  have hm_eq : mAux n = 2 ^ n + n * (2 ^ n - 2) := card_auxVar n hn
  have hts_sum : (∑ D ∈ F_ts (w := w) hn, D.card) ≤ 7 * (n * (2 ^ n - 2)) := by
    calc (∑ D ∈ F_ts (w := w) hn, D.card)
        ≤ ∑ p : Fin n × NodeIdx n, ∑ D ∈ tseitinNode (w := w) hn p, D.card :=
          sum_card_biUnion_le _ _
      _ ≤ ∑ _p : Fin n × NodeIdx n, 7 := by
          refine Finset.sum_le_sum fun p _ => ?_
          have h1 : (∑ D ∈ tseitinNode (w := w) hn p, D.card) ≤
              (cLeft (w := w) hn p.1 p.2).card + (cRight (w := w) hn p.1 p.2).card +
              (cUp (w := w) hn p.1 p.2).card := by
            have hu1 : tseitinNode (w := w) hn p =
                {cLeft hn p.1 p.2} ∪ ({cRight hn p.1 p.2} ∪ {cUp hn p.1 p.2}) := by
              ext x; simp [tseitinNode]; tauto
            rw [hu1]
            calc (∑ D ∈ {cLeft (w := w) hn p.1 p.2} ∪
                    ({cRight hn p.1 p.2} ∪ {cUp hn p.1 p.2}), D.card)
                ≤ (∑ D ∈ {cLeft (w := w) hn p.1 p.2}, D.card) +
                    (∑ D ∈ {cRight (w := w) hn p.1 p.2} ∪ {cUp hn p.1 p.2}, D.card) :=
                  sum_card_union_le _ _
              _ ≤ (cLeft (w := w) hn p.1 p.2).card +
                    ((cRight (w := w) hn p.1 p.2).card + (cUp (w := w) hn p.1 p.2).card) := by
                  simp only [Finset.sum_singleton]
                  have h2 := sum_card_union_le ({cRight (w := w) hn p.1 p.2} : Finset _)
                    ({cUp (w := w) hn p.1 p.2} : Finset _)
                  simp only [Finset.sum_singleton] at h2
                  exact Nat.add_le_add_left h2 _
              _ = _ := by omega
          have := card_cLeft (w := w) hn p.1 p.2
          have := card_cRight (w := w) hn p.1 p.2
          have := card_cUp (w := w) hn p.1 p.2
          omega
      _ = 7 * (n * (2 ^ n - 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              card_nodeIdx n hn, smul_eq_mul, mul_comm]
  have htop_sum : (∑ D ∈ F_top (w := w) hn, D.card) ≤ 2 * n := by
    calc (∑ D ∈ F_top (w := w) hn, D.card)
        ≤ ∑ _D ∈ F_top (w := w) hn, 2 := Finset.sum_le_sum fun D hD => by
            rcases Finset.mem_image.mp hD with ⟨i, _, rfl⟩; exact card_top hn i
      _ = (F_top (w := w) hn).card * 2 := by simp
      _ ≤ n * 2 := Nat.mul_le_mul_right 2 (by
            calc (F_top (w := w) hn).card ≤ (Finset.univ : Finset (Fin n)).card :=
                  Finset.card_image_le
              _ = n := by simp)
      _ = 2 * n := by ring
  have hbit_sum : (∑ D ∈ F_bit (w := w) hn, D.card) ≤ 4 * n := by
    calc (∑ D ∈ F_bit (w := w) hn, D.card)
        ≤ ∑ _D ∈ F_bit (w := w) hn, 2 := Finset.sum_le_sum fun D hD => by
            rcases Finset.mem_image.mp hD with ⟨⟨i, b⟩, _, rfl⟩; exact card_bit hn i b
      _ = (F_bit (w := w) hn).card * 2 := by simp
      _ ≤ (2 * n) * 2 := Nat.mul_le_mul_right 2 (by
          calc (F_bit (w := w) hn).card ≤ (Finset.univ : Finset (Fin n × Bool)).card :=
                Finset.card_image_le
            _ = 2 * n := by simp [mul_comm])
      _ = 4 * n := by ring
  have hperm_sum : (∑ D ∈ F_perm (w := w) hn, D.card) ≤ 2 * n * 2 ^ (min n (w + 1)) := by
    calc (∑ D ∈ F_perm (w := w) hn, D.card)
        ≤ ∑ _D ∈ F_perm (w := w) hn, 2 := Finset.sum_le_sum fun D hD => by
            rcases Finset.mem_image.mp hD with ⟨⟨i, q⟩, _, rfl⟩; exact card_perm hn i q
      _ = (F_perm (w := w) hn).card * 2 := by simp
      _ ≤ (n * 2 ^ (min n (w + 1))) * 2 := Nat.mul_le_mul_right 2 (by
          calc (F_perm (w := w) hn).card
              ≤ (Finset.univ : Finset (Fin n × (Fin (min n (w + 1)) → Bool))).card :=
                Finset.card_image_le
            _ = n * 2 ^ (min n (w + 1)) := by simp [Fintype.card_pi])
      _ = 2 * n * 2 ^ (min n (w + 1)) := by ring
  have hF_sum : (∑ D ∈ F_all (w := w) hn, D.card) ≤
      7 * (n * (2 ^ n - 2)) + 2 * n + 4 * n + 2 * n * 2 ^ (min n (w + 1)) := by
    calc (∑ D ∈ F_all (w := w) hn, D.card)
        ≤ (∑ D ∈ F_ts (w := w) hn ∪ F_top hn ∪ F_bit hn, D.card) +
            (∑ D ∈ F_perm (w := w) hn, D.card) := sum_card_union_le _ _
      _ ≤ ((∑ D ∈ F_ts (w := w) hn ∪ F_top hn, D.card) + (∑ D ∈ F_bit (w := w) hn, D.card)) +
            (∑ D ∈ F_perm (w := w) hn, D.card) := Nat.add_le_add_right (sum_card_union_le _ _) _
      _ ≤ (((∑ D ∈ F_ts (w := w) hn, D.card) + (∑ D ∈ F_top (w := w) hn, D.card)) +
            (∑ D ∈ F_bit (w := w) hn, D.card)) + (∑ D ∈ F_perm (w := w) hn, D.card) :=
            Nat.add_le_add_right (Nat.add_le_add_right (sum_card_union_le _ _) _) _
      _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hts_sum htop_sum) hbit_sum) hperm_sum
  have h2n_ge : 2 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn
    simpa using this
  have hmul_sub : 8 * (n * (2 ^ n - 2)) + 16 * n = 8 * n * 2 ^ n := by
    have hsub : 2 ^ n - 2 + 2 = 2 ^ n := Nat.sub_add_cancel h2n_ge
    calc 8 * (n * (2 ^ n - 2)) + 16 * n
        = 8 * n * (2 ^ n - 2 + 2) := by ring
      _ = 8 * n * 2 ^ n := by rw [hsub]
  have hcomb : (8 * n + 1) * 2 ^ n = 8 * n * 2 ^ n + 2 ^ n := by ring
  omega

private lemma is_3cnf {n w : ℕ} (hn : 0 < n) :
    ∀ D ∈ F_all (w := w) hn, D.card ≤ 3 := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  intro D hDF
  rcases mem_F_all_cases hn hDF with h1 | h2 | h3 | h4
  · rcases Finset.mem_biUnion.mp h1 with ⟨⟨i, idx⟩, _, hD⟩
    simp only [tseitinNode, Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl
    · exact le_trans (card_cLeft hn i idx) (by omega)
    · exact le_trans (card_cRight hn i idx) (by omega)
    · exact card_cUp hn i idx
  · rcases Finset.mem_image.mp h2 with ⟨i, _, rfl⟩
    exact le_trans (card_top hn i) (by omega)
  · rcases Finset.mem_image.mp h3 with ⟨⟨i, b⟩, _, rfl⟩
    exact le_trans (card_bit hn i b) (by omega)
  · rcases Finset.mem_image.mp h4 with ⟨⟨i, q⟩, _, rfl⟩
    exact le_trans (card_perm hn i q) (by omega)

private lemma bit_occ_count {n w : ℕ} (hn : 0 < n) (i : Fin n) (b : Bool) :
    letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
    ((F_all (w := w) hn).filter (fun D => (Sum.inl (Sum.inl i), b) ∈ D)).card = 1 := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  have heq : (F_all (w := w) hn).filter (fun D => (Sum.inl (Sum.inl i), b) ∈ D) =
      {bitClause hn i b} := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hDF, hmem⟩
      rcases mem_F_all_cases hn hDF with h1 | h2 | h3 | h4
      · exfalso
        rcases Finset.mem_biUnion.mp h1 with ⟨⟨i', idx⟩, _, hD⟩
        simp only [tseitinNode, Finset.mem_insert, Finset.mem_singleton] at hD
        rcases hD with rfl | rfl | rfl <;> simp [cLeft, cRight, cUp, auxLit] at hmem
      · exfalso
        rcases Finset.mem_image.mp h2 with ⟨i', _, rfl⟩
        simp [topClause, auxLit] at hmem
      · rcases Finset.mem_image.mp h3 with ⟨⟨i', b'⟩, _, rfl⟩
        simp only [bitClause, auxLit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
          Sum.inl.injEq, false_and, false_or, reduceCtorEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        rfl
      · exfalso
        rcases Finset.mem_image.mp h4 with ⟨⟨i', q⟩, _, rfl⟩
        simp [permClause, auxLit] at hmem
    · rintro rfl
      exact ⟨mem_F_bit hn i b, by simp [bitClause]⟩
  rw [heq, Finset.card_singleton]

private lemma perm_occ_count {n w : ℕ} (hn : 0 < n) (i : Fin n) (p : Fin (w + 1) → Bool) :
    letI : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
    ((F_all (w := w) hn).filter (fun D => (Sum.inl (Sum.inr (i, p)), false) ∈ D)).card = 0 ∧
    ((F_all (w := w) hn).filter (fun D => (Sum.inl (Sum.inr (i, p)), true) ∈ D)).card =
      (if ∃ x : Fin n → Bool, ∀ j : Fin (w + 1),
        x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ = p j then 1 else 0) := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  constructor
  · have hemp : (F_all (w := w) hn).filter (fun D => (Sum.inl (Sum.inr (i, p)), false) ∈ D) = ∅ := by
      ext D
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hDF hmem
      rcases mem_F_all_cases hn hDF with h1 | h2 | h3 | h4
      · rcases Finset.mem_biUnion.mp h1 with ⟨⟨i', idx⟩, _, hD⟩
        simp only [tseitinNode, Finset.mem_insert, Finset.mem_singleton] at hD
        rcases hD with rfl | rfl | rfl <;> simp [cLeft, cRight, cUp, auxLit] at hmem
      · rcases Finset.mem_image.mp h2 with ⟨i', _, rfl⟩
        simp [topClause, auxLit] at hmem
      · rcases Finset.mem_image.mp h3 with ⟨⟨i', b'⟩, _, rfl⟩
        simp [bitClause, auxLit] at hmem
      · rcases Finset.mem_image.mp h4 with ⟨⟨i', q⟩, _, rfl⟩
        simp [permClause, auxLit] at hmem
    rw [hemp, Finset.card_empty]
  · by_cases hreal : ∃ x : Fin n → Bool, ∀ j : Fin (w + 1),
        x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ = p j
    · simp only [hreal, ↓reduceIte]
      rcases (realizable_iff_exists_extPat hn i p).mp hreal with ⟨q, hq⟩
      have heq : (F_all (w := w) hn).filter (fun D => (Sum.inl (Sum.inr (i, p)), true) ∈ D) =
          {permClause hn i q} := by
        ext D
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hDF, hmem⟩
          rcases mem_F_all_cases hn hDF with h1 | h2 | h3 | h4
          · exfalso
            rcases Finset.mem_biUnion.mp h1 with ⟨⟨i', idx⟩, _, hD⟩
            simp only [tseitinNode, Finset.mem_insert, Finset.mem_singleton] at hD
            rcases hD with rfl | rfl | rfl <;> simp [cLeft, cRight, cUp, auxLit] at hmem
          · exfalso
            rcases Finset.mem_image.mp h2 with ⟨i', _, rfl⟩
            simp [topClause, auxLit] at hmem
          · exfalso
            rcases Finset.mem_image.mp h3 with ⟨⟨i', b'⟩, _, rfl⟩
            simp [bitClause, auxLit] at hmem
          · rcases Finset.mem_image.mp h4 with ⟨⟨i', q'⟩, _, rfl⟩
            simp only [permClause, auxLit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
              Sum.inl.injEq, Sum.inr.injEq, false_and, false_or, and_true, reduceCtorEq] at hmem
            rcases hmem with ⟨rfl, hpeq⟩
            have hqq : q' = q := (extPat_injective hn (hq.trans hpeq)).symm
            rw [hqq]
        · rintro rfl
          refine ⟨mem_F_perm hn i q, ?_⟩
          simp [permClause, hq]
      rw [heq, Finset.card_singleton]
    · simp only [hreal, ↓reduceIte]
      have hnoreal : ¬ ∃ q : Fin (min n (w + 1)) → Bool, extPat hn q = p := by
        intro hq; exact hreal ((realizable_iff_exists_extPat hn i p).mpr hq)
      have hemp : (F_all (w := w) hn).filter (fun D => (Sum.inl (Sum.inr (i, p)), true) ∈ D) = ∅ := by
        ext D
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hDF hmem
        rcases mem_F_all_cases hn hDF with h1 | h2 | h3 | h4
        · rcases Finset.mem_biUnion.mp h1 with ⟨⟨i', idx⟩, _, hD⟩
          simp only [tseitinNode, Finset.mem_insert, Finset.mem_singleton] at hD
          rcases hD with rfl | rfl | rfl <;> simp [cLeft, cRight, cUp, auxLit] at hmem
        · rcases Finset.mem_image.mp h2 with ⟨i', _, rfl⟩
          simp [topClause, auxLit] at hmem
        · rcases Finset.mem_image.mp h3 with ⟨⟨i', b'⟩, _, rfl⟩
          simp [bitClause, auxLit] at hmem
        · rcases Finset.mem_image.mp h4 with ⟨⟨i', q'⟩, _, rfl⟩
          simp only [permClause, auxLit, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
            Sum.inl.injEq, Sum.inr.injEq, false_and, false_or, and_true, reduceCtorEq] at hmem
          exact hnoreal ⟨q', hmem.2.symm⟩
      rw [hemp, Finset.card_empty]

private lemma tree_down_sat {n w : ℕ} (hn : 0 < n)
    (σ : Sum (Var n w) (Fin (mAux n)) → Bool) (hsat : Satisfies σ (↑(F_all (w := w) hn) : Set _))
    (i : Fin n) :
    ∀ (k d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n),
    n - d = k → ∀ (pref : Fin d → Bool),
    σ (Sum.inr (eAux n (nodeVar hn i d hd1 hdn pref))) = true →
    ∃ x : Fin n → Bool, matchesPref hn i hdn pref x ∧ σ (Sum.inr (eAux n (Sum.inl x))) = true := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  intro k
  induction k with
  | zero =>
    intro d hd1 hdn hkd pref htrue
    have hdeq : d = n := by omega
    subst hdeq
    rw [nodeVar_eq hn i pref] at htrue
    exact ⟨unrotWord hn i pref, (matchesPref_full_iff hn i pref _).mpr rfl, htrue⟩
  | succ k ih =>
    intro d hd1 hdn hkd pref htrue
    have hdlt : d < n := by omega
    let idx : NodeIdx n := mkIdx d hd1 hdlt pref
    rw [nodeVar_lt hn i d hd1 hdlt pref] at htrue
    rcases hsat (cUp hn i idx) (mem_F_ts hn i idx).2.2 with ⟨l, hl, hlsat⟩
    simp only [cUp, auxLit, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · rw [htrue] at hlsat; simp at hlsat
    · have hnext := nodeVar_extBit_idx hn i hd1 hdlt pref false
      rw [hnext] at hlsat
      rcases ih (d + 1) (by omega) (by omega) (by omega) (extBit pref false) hlsat with ⟨x, hmx, hx⟩
      exact ⟨x, ((matchesPref_extBit hn i hdlt pref false x).mp hmx).1, hx⟩
    · have hnext := nodeVar_extBit_idx hn i hd1 hdlt pref true
      rw [hnext] at hlsat
      rcases ih (d + 1) (by omega) (by omega) (by omega) (extBit pref true) hlsat with ⟨x, hmx, hx⟩
      exact ⟨x, ((matchesPref_extBit hn i hdlt pref true x).mp hmx).1, hx⟩

private lemma tree_up_sat {n w : ℕ} (hn : 0 < n)
    (σ : Sum (Var n w) (Fin (mAux n)) → Bool) (hsat : Satisfies σ (↑(F_all (w := w) hn) : Set _))
    (i : Fin n) (x : Fin n → Bool) (hx : σ (Sum.inr (eAux n (Sum.inl x))) = true) :
    ∀ (k d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n),
    n - d = k → ∀ (pref : Fin d → Bool), matchesPref hn i hdn pref x →
    σ (Sum.inr (eAux n (nodeVar hn i d hd1 hdn pref))) = true := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  intro k
  induction k with
  | zero =>
    intro d hd1 hdn hkd pref hm
    have hdeq : d = n := by omega
    subst hdeq
    rw [nodeVar_eq hn i pref, ← (matchesPref_full_iff hn i pref x).mp hm]
    exact hx
  | succ k ih =>
    intro d hd1 hdn hkd pref hm
    have hdlt : d < n := by omega
    let b := rotWord hn i x ⟨d, hdlt⟩
    have hm' : matchesPref hn i (by omega) (extBit pref b) x :=
      (matchesPref_extBit hn i hdlt pref b x).mpr ⟨hm, rfl⟩
    have hchild := ih (d + 1) (by omega) (by omega) (by omega) (extBit pref b) hm'
    let idx : NodeIdx n := mkIdx d hd1 hdlt pref
    rw [nodeVar_lt hn i d hd1 hdlt pref]
    have hnext := nodeVar_extBit_idx hn i hd1 hdlt pref b
    cases hb : b
    · rw [hb] at hchild hnext
      rcases hsat (cLeft hn i idx) (mem_F_ts hn i idx).1 with ⟨l, hl, hlsat⟩
      simp only [cLeft, auxLit, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · rw [hnext, hchild] at hlsat; simp at hlsat
      · exact hlsat
    · rw [hb] at hchild hnext
      rcases hsat (cRight hn i idx) (mem_F_ts hn i idx).2.1 with ⟨l, hl, hlsat⟩
      simp only [cRight, auxLit, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · rw [hnext, hchild] at hlsat; simp at hlsat
      · exact hlsat

private lemma sat_iff_accepts {n w : ℕ} (hn : 0 < n) (a : Var n w → Bool) :
    acceptsPred hn a ↔
      ∃ aux : Fin (mAux n) → Bool, Satisfies (Sum.elim a aux) (↑(F_all (w := w) hn) : Set _) := by
  classical
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  have hr1 : 1 ≤ min n (w + 1) := Nat.le_min.mpr ⟨hn, Nat.succ_le_succ (Nat.zero_le w)⟩
  have hrn : min n (w + 1) ≤ n := Nat.min_le_left n (w + 1)
  constructor
  · intro hacc
    let x₀ : Fin n → Bool := fun i => a (Sum.inl i)
    let auxA : AuxVar n → Bool := fun v =>
      match v with
      | Sum.inl x => decide (x = x₀)
      | Sum.inr (i, ⟨d, pref⟩) =>
          decide (matchesPref hn i (by omega : d.val + 1 ≤ n) pref x₀)
    let aux : Fin (mAux n) → Bool := fun j => auxA ((eAux n).symm j)
    have haux_nv : ∀ (i : Fin n) (d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n) (pref : Fin d → Bool),
        aux (eAux n (nodeVar hn i d hd1 hdn pref)) = decide (matchesPref hn i hdn pref x₀) := by
      intro i d hd1 hdn pref
      simp only [aux, Equiv.symm_apply_apply]
      by_cases hdlt : d < n
      · rw [nodeVar_lt hn i d hd1 hdlt pref]
        dsimp only [mkIdx, auxA]
        rw [decide_eq_decide]
        simp only [matchesPref]
        constructor
        · intro h t
          exact h ⟨t.val, by have := t.isLt; omega⟩
        · intro h t
          exact h ⟨t.val, by have := t.isLt; omega⟩
      · have hdeq : d = n := by omega
        subst hdeq
        rw [nodeVar_eq hn i pref]
        dsimp only [auxA]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, matchesPref_full_iff]
        exact eq_comm
    refine ⟨aux, fun D hDF => ?_⟩
    rcases mem_F_all_cases hn hDF with h1 | h2 | h3 | h4
    · rcases Finset.mem_biUnion.mp h1 with ⟨⟨i, ⟨d, pref⟩⟩, _, hD⟩
      have hparent : aux (eAux n (Sum.inr (i, ⟨d, pref⟩))) =
          decide (matchesPref hn i (by omega) pref x₀) := by
        simp [aux, auxA]
      simp only [tseitinNode, Finset.mem_insert, Finset.mem_singleton] at hD
      rcases hD with rfl | rfl | rfl
      · by_cases hm : matchesPref hn i (by omega) (extBit pref false) x₀
        · refine ⟨auxLit (Sum.inr (i, ⟨d, pref⟩)) true, by simp [cLeft], ?_⟩
          simp only [auxLit, Sum.elim_inr, hparent, decide_eq_true_eq]
          exact ((matchesPref_extBit hn i (by omega) pref false x₀).mp hm).1
        · refine ⟨auxLit (nodeVar hn i (d.val + 2) (by omega) (by omega) (extBit pref false)) false,
            by simp [cLeft], ?_⟩
          simp only [auxLit, Sum.elim_inr, haux_nv]
          exact decide_eq_false hm
      · by_cases hm : matchesPref hn i (by omega) (extBit pref true) x₀
        · refine ⟨auxLit (Sum.inr (i, ⟨d, pref⟩)) true, by simp [cRight], ?_⟩
          simp only [auxLit, Sum.elim_inr, hparent, decide_eq_true_eq]
          exact ((matchesPref_extBit hn i (by omega) pref true x₀).mp hm).1
        · refine ⟨auxLit (nodeVar hn i (d.val + 2) (by omega) (by omega) (extBit pref true)) false,
            by simp [cRight], ?_⟩
          simp only [auxLit, Sum.elim_inr, haux_nv]
          exact decide_eq_false hm
      · by_cases hm : matchesPref hn i (by omega) pref x₀
        · cases hb : rotWord hn i x₀ ⟨d.val + 1, by omega⟩
          · refine ⟨auxLit (nodeVar hn i (d.val + 2) (by omega) (by omega) (extBit pref false)) true,
              by simp [cUp], ?_⟩
            simp only [auxLit, Sum.elim_inr, haux_nv, decide_eq_true_eq]
            exact (matchesPref_extBit hn i (by omega) pref false x₀).mpr ⟨hm, hb⟩
          · refine ⟨auxLit (nodeVar hn i (d.val + 2) (by omega) (by omega) (extBit pref true)) true,
              by simp [cUp], ?_⟩
            simp only [auxLit, Sum.elim_inr, haux_nv, decide_eq_true_eq]
            exact (matchesPref_extBit hn i (by omega) pref true x₀).mpr ⟨hm, hb⟩
        · refine ⟨auxLit (Sum.inr (i, ⟨d, pref⟩)) false, by simp [cUp], ?_⟩
          simp only [auxLit, Sum.elim_inr, hparent]
          exact decide_eq_false hm
    · rcases Finset.mem_image.mp h2 with ⟨i, _, rfl⟩
      cases hb : x₀ i
      · refine ⟨auxLit (nodeVar hn i 1 (le_refl 1) hn (fun _ => false)) true,
          by simp [topClause], ?_⟩
        simp only [auxLit, Sum.elim_inr, haux_nv, decide_eq_true_eq]
        intro t
        simp [rotWord, Nat.mod_eq_of_lt i.isLt, hb]
      · refine ⟨auxLit (nodeVar hn i 1 (le_refl 1) hn (fun _ => true)) true,
          by simp [topClause], ?_⟩
        simp only [auxLit, Sum.elim_inr, haux_nv, decide_eq_true_eq]
        intro t
        simp [rotWord, Nat.mod_eq_of_lt i.isLt, hb]
    · rcases Finset.mem_image.mp h3 with ⟨⟨i, b⟩, _, rfl⟩
      by_cases hxi : x₀ i = b
      · refine ⟨(Sum.inl (Sum.inl i), b), by simp [bitClause], ?_⟩
        simpa [x₀] using hxi
      · refine ⟨auxLit (nodeVar hn i 1 (le_refl 1) hn (fun _ => b)) false,
          by simp [bitClause], ?_⟩
        simp only [auxLit, Sum.elim_inr, haux_nv]
        refine decide_eq_false fun hm => hxi ?_
        have h0 := hm ⟨0, by omega⟩
        simpa [rotWord, Nat.mod_eq_of_lt i.isLt] using h0
    · rcases Finset.mem_image.mp h4 with ⟨⟨i, q⟩, _, rfl⟩
      by_cases hm : matchesPref hn i hrn q x₀
      · refine ⟨(Sum.inl (Sum.inr (i, extPat hn q)), true), by simp [permClause], ?_⟩
        have hwin : win (w := w) hn i x₀ = extPat hn q := by
          rw [win_eq_extPat hn i x₀]
          congr 1; funext t; exact hm t
        rw [← hwin]
        exact hacc i
      · refine ⟨auxLit (nodeVar hn i (min n (w + 1)) hr1 hrn q) false,
          by simp [permClause], ?_⟩
        simp only [auxLit, Sum.elim_inr, haux_nv]
        exact decide_eq_false hm
  · rintro ⟨aux, hsat⟩
    let σ := Sum.elim a aux
    have htop0 := hsat (topClause hn ⟨0, hn⟩) (mem_F_top hn ⟨0, hn⟩)
    have hex_x : ∃ x : Fin n → Bool, σ (Sum.inr (eAux n (Sum.inl x))) = true := by
      rcases htop0 with ⟨l, hl, hlsat⟩
      simp only [topClause, auxLit, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · rcases tree_down_sat hn σ hsat ⟨0, hn⟩ (n - 1) 1 (le_refl 1) hn rfl (fun _ => false) hlsat with
          ⟨x, _, hx⟩
        exact ⟨x, hx⟩
      · rcases tree_down_sat hn σ hsat ⟨0, hn⟩ (n - 1) 1 (le_refl 1) hn rfl (fun _ => true) hlsat with
          ⟨x, _, hx⟩
        exact ⟨x, hx⟩
    rcases hex_x with ⟨x, hx⟩
    have ha_eq : ∀ i : Fin n, a (Sum.inl i) = x i := by
      intro i
      have hm1 : matchesPref hn i hn (fun _ => x i) x := by
        intro t
        simp [rotWord, Nat.mod_eq_of_lt i.isLt]
      have hhi := tree_up_sat hn σ hsat i x hx (n - 1) 1 (le_refl 1) hn rfl (fun _ => x i) hm1
      rcases hsat (bitClause hn i (x i)) (mem_F_bit hn i (x i)) with ⟨l, hl, hlsat⟩
      simp only [bitClause, auxLit, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · dsimp only [σ] at hhi; dsimp only at hlsat
        rw [hhi] at hlsat; simp at hlsat
      · exact hlsat
    intro i
    let q : Fin (min n (w + 1)) → Bool := fun t => rotWord hn i x ⟨t.val, lt_of_lt_of_le t.isLt hrn⟩
    have hmq : matchesPref hn i hrn q x := fun _ => rfl
    have hg := tree_up_sat hn σ hsat i x hx (n - min n (w + 1)) (min n (w + 1)) hr1 hrn rfl q hmq
    rcases hsat (permClause hn i q) (mem_F_perm hn i q) with ⟨l, hl, hlsat⟩
    simp only [permClause, auxLit, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · dsimp only [σ] at hg; dsimp only at hlsat
      rw [hg] at hlsat; simp at hlsat
    · have hpat : (fun j : Fin (w + 1) => a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩)) =
          extPat hn q := by
        rw [← win_eq_extPat hn i x]
        funext j; exact ha_eq _
      rw [hpat]
      exact hlsat

private def assumptionsOf {n w : ℕ} (ρ : Var n w → Option Bool) :
    Set (Literal (Sum (Var n w) (Fin (mAux n)))) :=
  {l | ∃ v : Var n w, l.1 = Sum.inl v ∧ ρ v = some l.2}

private def completionOf {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool)
    (a : Var n w → Bool) : Prop :=
  acceptsPred hn a ∧ ∀ (v : Var n w) (b : Bool), ρ v = some b → a v = b

private def survives {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) (x : Fin n → Bool) : Prop :=
  (∀ (i : Fin n) (b : Bool), ρ (Sum.inl i) = some b → x i = b) ∧
  (∀ i : Fin n, ρ (Sum.inr (i, win (w := w) hn i x)) ≠ some false)

private lemma comp_default_of_surv {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool)
    {x : Fin n → Bool} (hx : survives hn ρ x) :
    let a : Var n w → Bool := fun v =>
      match v with
      | Sum.inl i => x i
      | Sum.inr u => match ρ (Sum.inr u) with | some b => b | none => true
    completionOf hn ρ a := by
  intro a
  refine ⟨fun i => ?_, fun v b hρ => ?_⟩
  · dsimp only [a]
    change (match ρ (Sum.inr (i, win (w := w) hn i x)) with | some b => b | none => true) = true
    cases hρ : ρ (Sum.inr (i, win (w := w) hn i x)) with
    | some b =>
      cases b
      · exact absurd hρ (hx.2 i)
      · rfl
    | none => rfl
  · cases v with
    | inl i => exact hx.1 i b hρ
    | inr u => dsimp only [a]; rw [hρ]

private lemma comp_of_surv {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool)
    (x : Fin n → Bool) (hx : survives hn ρ x)
    (v0 : Fin n × (Fin (w + 1) → Bool)) (b0 : Bool)
    (hv0 : ρ (Sum.inr v0) = none → v0.2 ≠ win (w := w) hn v0.1 x) :
    ∃ a : Var n w → Bool, completionOf hn ρ a ∧ (∀ i, a (Sum.inl i) = x i) ∧
      (ρ (Sum.inr v0) = none → a (Sum.inr v0) = b0) := by
  let : DecidableEq (Fin n × (Fin (w + 1) → Bool)) := Classical.typeDecidableEq _
  let a : Var n w → Bool := fun v =>
    match v with
    | Sum.inl i => x i
    | Sum.inr u =>
        match ρ (Sum.inr u) with
        | some b => b
        | none => if u = v0 then b0 else true
  refine ⟨a, ⟨?_, ?_⟩, fun _ => rfl, ?_⟩
  · intro i
    dsimp only [a]
    have hwin_eq : (fun j : Fin (w + 1) => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) =
        win (w := w) hn i x := rfl
    rw [hwin_eq]
    cases hρ : ρ (Sum.inr (i, win (w := w) hn i x)) with
    | some b =>
      cases b
      · exact absurd hρ (hx.2 i)
      · rfl
    | none =>
      by_cases heq : (i, win (w := w) hn i x) = v0
      · exfalso
        have hρ0 : ρ (Sum.inr v0) = none := by rw [← heq]; exact hρ
        have hne := hv0 hρ0
        have h2 : win (w := w) hn v0.1 x = v0.2 := by
          rcases v0 with ⟨i0, p0⟩
          have hi : i = i0 := congrArg Prod.fst heq
          have hp : win (w := w) hn i x = p0 := congrArg Prod.snd heq
          subst hi; exact hp
        exact hne h2.symm
      · simp [heq]
  · intro v b hρ
    cases v with
    | inl i => exact hx.1 i b hρ
    | inr u => dsimp only [a]; rw [hρ]
  · intro hρ0
    dsimp only [a]; rw [hρ0]; simp

private lemma comp_iff_surv {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) :
    (∃ a : Var n w → Bool, completionOf hn ρ a) ↔ ∃ x : Fin n → Bool, survives hn ρ x := by
  constructor
  · rintro ⟨a, hacc, hρ⟩
    refine ⟨fun i => a (Sum.inl i), fun i b hb => hρ (Sum.inl i) b hb, fun i hf => ?_⟩
    have h1 := hρ (Sum.inr (i, win (w := w) hn i (fun i => a (Sum.inl i)))) false hf
    have h2 := hacc i
    change a (Sum.inr (i, fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = false at h1
    rw [h2] at h1
    simp at h1
  · rintro ⟨x, hx⟩
    exact ⟨_, comp_default_of_surv hn ρ hx⟩

private lemma up_down_false {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) (i : Fin n) :
    ∀ (k d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n),
    n - d = k → ∀ (pref : Fin d → Bool),
    UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
      (auxLit (nodeVar hn i d hd1 hdn pref) false) →
    ∀ x : Fin n → Bool, matchesPref hn i hdn pref x →
    UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ) (auxLit (Sum.inl x) false) := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  intro k
  induction k with
  | zero =>
    intro d hd1 hdn hkd pref hup x hm
    have hdeq : d = n := by omega
    subst hdeq
    rw [nodeVar_eq hn i pref, ← (matchesPref_full_iff hn i pref x).mp hm] at hup
    exact hup
  | succ k ih =>
    intro d hd1 hdn hkd pref hup x hm
    have hdlt : d < n := by omega
    let b := rotWord hn i x ⟨d, hdlt⟩
    let idx : NodeIdx n := mkIdx d hd1 hdlt pref
    rw [nodeVar_lt hn i d hd1 hdlt pref] at hup
    have hnext := nodeVar_extBit_idx hn i hd1 hdlt pref b
    have hchild_up : UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
        (auxLit (nodeVar hn i (d + 1) (by omega) (by omega) (extBit pref b)) false) := by
      cases hb : b
      · rw [hb] at hnext
        rw [← hnext]
        refine UPForces.unit (mem_F_ts hn i idx).1 (by simp [cLeft, idx]) fun l' hl' hne => ?_
        simp only [cLeft, Finset.mem_insert, Finset.mem_singleton] at hl'
        rcases hl' with rfl | rfl
        · exact absurd rfl hne
        · exact hup
      · rw [hb] at hnext
        rw [← hnext]
        refine UPForces.unit (mem_F_ts hn i idx).2.1 (by simp [cRight, idx]) fun l' hl' hne => ?_
        simp only [cRight, Finset.mem_insert, Finset.mem_singleton] at hl'
        rcases hl' with rfl | rfl
        · exact absurd rfl hne
        · exact hup
    exact ih (d + 1) (by omega) (by omega) (by omega) (extBit pref b) hchild_up x
      ((matchesPref_extBit hn i hdlt pref b x).mpr ⟨hm, rfl⟩)

private lemma dead_up {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool)
    (x : Fin n → Bool) (hns : ¬ survives hn ρ x) :
    UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ) (auxLit (Sum.inl x) false) := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  have hr1 : 1 ≤ min n (w + 1) := Nat.le_min.mpr ⟨hn, Nat.succ_le_succ (Nat.zero_le w)⟩
  have hrn : min n (w + 1) ≤ n := Nat.min_le_left n (w + 1)
  dsimp only [survives] at hns
  push Not at hns
  by_cases h1 : ∀ (i : Fin n) (b : Bool), ρ (Sum.inl i) = some b → x i = b
  · rcases hns h1 with ⟨i, hi⟩
    let q : Fin (min n (w + 1)) → Bool := fun t => rotWord hn i x ⟨t.val, lt_of_lt_of_le t.isLt hrn⟩
    have hwin : extPat hn q = win (w := w) hn i x := (win_eq_extPat hn i x).symm
    have hass : UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
        (negLit (Sum.inl (Sum.inr (i, extPat hn q)), true)) := by
      refine UPForces.hyp ⟨Sum.inr (i, extPat hn q), rfl, ?_⟩
      rw [hwin]; exact hi
    have hg_false : UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
        (auxLit (nodeVar hn i (min n (w + 1)) hr1 hrn q) false) := by
      refine UPForces.unit (mem_F_perm hn i q) (by simp [permClause]) fun l' hl' hne => ?_
      simp only [permClause, Finset.mem_insert, Finset.mem_singleton] at hl'
      rcases hl' with rfl | rfl
      · exact absurd rfl hne
      · exact hass
    exact up_down_false hn ρ i (n - min n (w + 1)) (min n (w + 1)) hr1 hrn rfl q hg_false x
      (fun _ => rfl)
  · push Not at h1
    rcases h1 with ⟨i, b, hρ, hne⟩
    have hbeq : b = !x i := by cases hb : b <;> cases hxi : x i <;> simp [hb, hxi] at hne ⊢
    have hass : UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
        (negLit (Sum.inl (Sum.inl i), x i)) := by
      refine UPForces.hyp ⟨Sum.inl i, rfl, ?_⟩
      simpa [negLit, hbeq] using hρ
    have hh_false : UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
        (auxLit (nodeVar hn i 1 (le_refl 1) hn (fun _ => x i)) false) := by
      refine UPForces.unit (mem_F_bit hn i (x i)) (by simp [bitClause]) fun l' hl' hne' => ?_
      simp only [bitClause, Finset.mem_insert, Finset.mem_singleton] at hl'
      rcases hl' with rfl | rfl
      · exact absurd rfl hne'
      · exact hass
    have hm1 : matchesPref hn i hn (fun _ => x i) x := by
      intro t
      simp [rotWord, Nat.mod_eq_of_lt i.isLt]
    exact up_down_false hn ρ i (n - 1) 1 (le_refl 1) hn rfl (fun _ => x i) hh_false x hm1

private lemma up_up_false {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) (i : Fin n) :
    ∀ (k d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n),
    n - d = k → ∀ (pref : Fin d → Bool),
    (∀ x : Fin n → Bool, matchesPref hn i hdn pref x → ¬ survives hn ρ x) →
    UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
      (auxLit (nodeVar hn i d hd1 hdn pref) false) := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  intro k
  induction k with
  | zero =>
    intro d hd1 hdn hkd pref hall
    have hdeq : d = n := by omega
    subst hdeq
    rw [nodeVar_eq hn i pref]
    exact dead_up hn ρ (unrotWord hn i pref)
      (hall (unrotWord hn i pref) ((matchesPref_full_iff hn i pref _).mpr rfl))
  | succ k ih =>
    intro d hd1 hdn hkd pref hall
    have hdlt : d < n := by omega
    let idx : NodeIdx n := mkIdx d hd1 hdlt pref
    rw [nodeVar_lt hn i d hd1 hdlt pref]
    have hnext_f := nodeVar_extBit_idx hn i hd1 hdlt pref false
    have hnext_t := nodeVar_extBit_idx hn i hd1 hdlt pref true
    have hf := ih (d + 1) (by omega) (by omega) (by omega) (extBit pref false)
      (fun x hm => hall x ((matchesPref_extBit hn i hdlt pref false x).mp hm).1)
    have ht := ih (d + 1) (by omega) (by omega) (by omega) (extBit pref true)
      (fun x hm => hall x ((matchesPref_extBit hn i hdlt pref true x).mp hm).1)
    refine UPForces.unit (mem_F_ts hn i idx).2.2 (by simp [cUp, idx]) fun l' hl' hne => ?_
    simp only [cUp, Finset.mem_insert, Finset.mem_singleton] at hl'
    rcases hl' with rfl | rfl | rfl
    · exact absurd rfl hne
    · change UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
        (auxLit (nodeVar hn i (idx.1.val + 2) (by omega) (by omega) (extBit idx.2 false)) false)
      rw [hnext_f]; exact hf
    · change UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
        (auxLit (nodeVar hn i (idx.1.val + 2) (by omega) (by omega) (extBit idx.2 true)) false)
      rw [hnext_t]; exact ht

private lemma up_down_true {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) (i : Fin n)
    (q : Fin (min n (w + 1)) → Bool)
    (hall : ∀ x : Fin n → Bool, survives hn ρ x →
      matchesPref hn i (Nat.min_le_left n (w + 1)) q x) :
    ∀ (d : ℕ) (hd1 : 1 ≤ d) (hdr : d ≤ min n (w + 1)),
    UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
      (auxLit (nodeVar hn i d hd1 (le_trans hdr (Nat.min_le_left n (w + 1)))
        (fun t => q ⟨t.val, lt_of_lt_of_le t.isLt hdr⟩)) true) := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  have hr1 : 1 ≤ min n (w + 1) := Nat.le_min.mpr ⟨hn, Nat.succ_le_succ (Nat.zero_le w)⟩
  have hrn : min n (w + 1) ≤ n := Nat.min_le_left n (w + 1)
  intro d
  induction d with
  | zero => intro hd1; omega
  | succ d ih =>
    intro hd1 hdr
    by_cases hd0 : d = 0
    · subst hd0
      let b0 := q ⟨0, hr1⟩
      have hpref_eq : (fun t : Fin 1 => q ⟨t.val, lt_of_lt_of_le t.isLt hdr⟩) = fun _ => b0 := by
        funext t
        have ht0 : t.val = 0 := by omega
        dsimp only [b0]
        congr 1
        exact Fin.ext ht0
      rw [hpref_eq]
      have hother_dead : ∀ x : Fin n → Bool,
          matchesPref hn i hn (fun _ => !b0) x → ¬ survives hn ρ x := by
        intro x hm hs
        have h1 := hall x hs ⟨0, hr1⟩
        have h2 := hm ⟨0, by omega⟩
        rw [h1] at h2
        change b0 = !b0 at h2
        cases b0 <;> simp at h2
      have hother_f := up_up_false hn ρ i (n - 1) 1 (le_refl 1) hn rfl (fun _ => !b0) hother_dead
      cases hb0 : b0
      · refine UPForces.unit (mem_F_top hn i) (by simp [topClause]) fun l' hl' hne => ?_
        simp only [topClause, Finset.mem_insert, Finset.mem_singleton] at hl'
        rcases hl' with rfl | rfl
        · exact absurd rfl hne
        · simpa [hb0, negLit, auxLit] using hother_f
      · refine UPForces.unit (mem_F_top hn i) (by simp [topClause]) fun l' hl' hne => ?_
        simp only [topClause, Finset.mem_insert, Finset.mem_singleton] at hl'
        rcases hl' with rfl | rfl
        · simpa [hb0, negLit, auxLit] using hother_f
        · exact absurd rfl hne
    · have hd1' : 1 ≤ d := by omega
      have hdlt : d < n := lt_of_lt_of_le hdr hrn
      have hprev := ih hd1' (by omega)
      let pref : Fin d → Bool := fun t => q ⟨t.val, lt_of_lt_of_le t.isLt (by omega)⟩
      let bd : Bool := q ⟨d, hdr⟩
      have hpref_ext : (fun t : Fin (d + 1) => q ⟨t.val, lt_of_lt_of_le t.isLt hdr⟩) =
          extBit pref bd := by
        funext t
        by_cases ht : t.val < d
        · simp [extBit, pref, ht]
        · have hteq : t.val = d := by omega
          simp [extBit, bd, hteq]
      rw [hpref_ext]
      let idx : NodeIdx n := mkIdx d hd1' hdlt pref
      rw [nodeVar_lt hn i d hd1' hdlt pref] at hprev
      have hsib_dead : ∀ x : Fin n → Bool,
          matchesPref hn i (le_trans hdr hrn) (extBit pref (!bd)) x → ¬ survives hn ρ x := by
        intro x hm hs
        have h1 := ((matchesPref_extBit hn i hdlt pref (!bd) x).mp hm).2
        have h2 := hall x hs ⟨d, hdr⟩
        rw [h2] at h1
        change bd = !bd at h1
        cases bd <;> simp at h1
      have hsib_f := up_up_false hn ρ i (n - (d + 1)) (d + 1) (by omega) (le_trans hdr hrn) rfl
        (extBit pref (!bd)) hsib_dead
      have hnext_f := nodeVar_extBit_idx hn i hd1' hdlt pref false
      have hnext_t := nodeVar_extBit_idx hn i hd1' hdlt pref true
      cases hbd : bd
      · rw [← hnext_f]
        refine UPForces.unit (mem_F_ts hn i idx).2.2 (by simp [cUp, idx]) fun l' hl' hne => ?_
        simp only [cUp, Finset.mem_insert, Finset.mem_singleton] at hl'
        rcases hl' with rfl | rfl | rfl
        · exact hprev
        · exact absurd rfl hne
        · change UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
            (auxLit (nodeVar hn i (idx.1.val + 2) (by omega) (by omega) (extBit idx.2 true)) false)
          rw [hnext_t]
          simpa [hbd] using hsib_f
      · rw [← hnext_t]
        refine UPForces.unit (mem_F_ts hn i idx).2.2 (by simp [cUp, idx]) fun l' hl' hne => ?_
        simp only [cUp, Finset.mem_insert, Finset.mem_singleton] at hl'
        rcases hl' with rfl | rfl | rfl
        · exact hprev
        · change UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
            (auxLit (nodeVar hn i (idx.1.val + 2) (by omega) (by omega) (extBit idx.2 false)) false)
          rw [hnext_f]
          simpa [hbd] using hsib_f
        · exact absurd rfl hne

private lemma up_complete_unsat {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) :
    (¬ ∃ a : Var n w → Bool, completionOf hn ρ a) ↔
      ∃ D ∈ F_all (w := w) hn, ∀ l ∈ D,
        UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ) (negLit l) := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  constructor
  · intro hunsat
    have hno_surv : ∀ x : Fin n → Bool, ¬ survives hn ρ x := fun x hx =>
      hunsat ((comp_iff_surv hn ρ).mpr ⟨x, hx⟩)
    have hf := up_up_false hn ρ ⟨0, hn⟩ (n - 1) 1 (le_refl 1) hn rfl (fun _ => false)
      (fun x _ => hno_surv x)
    have ht := up_up_false hn ρ ⟨0, hn⟩ (n - 1) 1 (le_refl 1) hn rfl (fun _ => true)
      (fun x _ => hno_surv x)
    refine ⟨topClause hn ⟨0, hn⟩, mem_F_top hn ⟨0, hn⟩, fun l hl => ?_⟩
    simp only [topClause, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact hf
    · exact ht
  · rintro ⟨D, hDF, hconf⟩ ⟨a, hacc, hρ⟩
    rcases (sat_iff_accepts hn a).mp hacc with ⟨aux, hsat⟩
    have hA : ∀ l' ∈ assumptionsOf ρ, Sum.elim a aux l'.1 = l'.2 := by
      rintro ⟨v', b'⟩ ⟨v, hvv, hvρ⟩
      dsimp only at hvv; rw [hvv]
      exact hρ v b' hvρ
    rcases hsat D hDF with ⟨l, hlD, hlsat⟩
    have hneg := upForces_sound (hconf l hlD) hsat hA
    dsimp only [negLit] at hneg
    rw [hlsat] at hneg
    cases l.2 <;> simp at hneg

private lemma up_complete_sat {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool)
    (hsat_comp : ∃ a : Var n w → Bool, completionOf hn ρ a) (v : Var n w) (b : Bool) :
    (∀ a : Var n w → Bool, completionOf hn ρ a → a v = b) ↔
      UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ) (Sum.inl v, b) := by
  let : DecidableEq (Sum (Var n w) (Fin (mAux n))) := Classical.typeDecidableEq _
  have hr1 : 1 ≤ min n (w + 1) := Nat.le_min.mpr ⟨hn, Nat.succ_le_succ (Nat.zero_le w)⟩
  have hrn : min n (w + 1) ≤ n := Nat.min_le_left n (w + 1)
  constructor
  · intro himp
    cases hρv : ρ v with
    | some b' =>
      rcases hsat_comp with ⟨a, hacc_a, hρa⟩
      have hb' : b' = b := (hρa v b' hρv).symm.trans (himp a ⟨hacc_a, hρa⟩)
      subst hb'
      exact UPForces.hyp ⟨v, rfl, hρv⟩
    | none =>
      cases v with
      | inl i =>
        have hall_bit : ∀ x : Fin n → Bool, survives hn ρ x → x i = b := fun x hx =>
          himp _ (comp_default_of_surv hn ρ hx)
        have hother_dead : ∀ x : Fin n → Bool,
            matchesPref hn i hn (fun _ => !b) x → ¬ survives hn ρ x := by
          intro x hm hs
          have h1 := hall_bit x hs
          have h2 := hm ⟨0, by omega⟩
          simp only [rotWord, add_zero, Nat.mod_eq_of_lt i.isLt] at h2
          rw [h1] at h2
          cases b <;> simp at h2
        have hother_f := up_up_false hn ρ i (n - 1) 1 (le_refl 1) hn rfl (fun _ => !b) hother_dead
        have hhb_true : UPForces (↑(F_all (w := w) hn) : Set _) (assumptionsOf ρ)
            (auxLit (nodeVar hn i 1 (le_refl 1) hn (fun _ => b)) true) := by
          cases hb : b
          · refine UPForces.unit (mem_F_top hn i) (by simp [topClause]) fun l' hl' hne => ?_
            simp only [topClause, Finset.mem_insert, Finset.mem_singleton] at hl'
            rcases hl' with rfl | rfl
            · exact absurd rfl hne
            · simpa [hb, negLit, auxLit] using hother_f
          · refine UPForces.unit (mem_F_top hn i) (by simp [topClause]) fun l' hl' hne => ?_
            simp only [topClause, Finset.mem_insert, Finset.mem_singleton] at hl'
            rcases hl' with rfl | rfl
            · simpa [hb, negLit, auxLit] using hother_f
            · exact absurd rfl hne
        refine UPForces.unit (mem_F_bit hn i b) (by simp [bitClause]) fun l' hl' hne => ?_
        simp only [bitClause, Finset.mem_insert, Finset.mem_singleton] at hl'
        rcases hl' with rfl | rfl
        · exact hhb_true
        · exact absurd rfl hne
      | inr u =>
        rcases u with ⟨i, p⟩
        rcases (comp_iff_surv hn ρ).mp hsat_comp with ⟨x0, hx0⟩
        have hb_true : b = true := by
          have h1 := himp _ (comp_default_of_surv hn ρ hx0)
          dsimp only at h1
          rw [hρv] at h1
          exact h1.symm
        subst hb_true
        have hall_win : ∀ x : Fin n → Bool, survives hn ρ x → win (w := w) hn i x = p := by
          intro x hx
          by_contra hne
          rcases comp_of_surv hn ρ x hx (i, p) false (fun _ h => hne h.symm) with
            ⟨a, ha_comp, _, ha_v0⟩
          have h1 := himp a ha_comp
          have h2 := ha_v0 hρv
          rw [h2] at h1
          simp at h1
        let q : Fin (min n (w + 1)) → Bool :=
          fun t => rotWord hn i x0 ⟨t.val, lt_of_lt_of_le t.isLt hrn⟩
        have hq_pat : extPat hn q = p := by
          rw [← win_eq_extPat hn i x0]
          exact hall_win x0 hx0
        have hall_q : ∀ x : Fin n → Bool, survives hn ρ x → matchesPref hn i hrn q x := by
          intro x hx t
          have h1 : extPat hn (fun t' : Fin (min n (w + 1)) =>
              rotWord hn i x ⟨t'.val, lt_of_lt_of_le t'.isLt hrn⟩) = extPat hn q := by
            rw [← win_eq_extPat hn i x, hall_win x hx, hq_pat]
          exact congrFun (extPat_injective hn h1) t
        have hg_true := up_down_true hn ρ i q hall_q (min n (w + 1)) hr1 (le_refl _)
        have hq_eta :
            (fun t : Fin (min n (w + 1)) =>
              q ⟨t.val, lt_of_lt_of_le t.isLt (le_refl _)⟩) = q := rfl
        rw [hq_eta] at hg_true
        rw [← hq_pat]
        refine UPForces.unit (mem_F_perm hn i q) (by simp [permClause]) fun l' hl' hne => ?_
        simp only [permClause, Finset.mem_insert, Finset.mem_singleton] at hl'
        rcases hl' with rfl | rfl
        · exact hg_true
        · exact absurd rfl hne
  · intro hup a ⟨hacc, hρa⟩
    rcases (sat_iff_accepts hn a).mp hacc with ⟨aux, hsat⟩
    have hA : ∀ l' ∈ assumptionsOf ρ, Sum.elim a aux l'.1 = l'.2 := by
      rintro ⟨v', b'⟩ ⟨v1, hvv, hvρ⟩
      dsimp only at hvv; rw [hvv]
      exact hρa v1 b' hvρ
    exact upForces_sound hup hsat hA

private lemma prove_230 (n w : ℕ) (hn : 0 < n) :
    let V := Sum (Fin n) (Fin n × (Fin (w + 1) → Bool))
    let accepts := fun (a : V → Bool) =>
      ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
        a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true
    letI : DecidableEq V := Classical.typeDecidableEq V
    ∃ (m : ℕ) (F : Finset (Clause (Sum V (Fin m)))),
      letI : DecidableEq (Sum V (Fin m)) := Classical.typeDecidableEq _
      m + (∑ D ∈ F, D.card) + 3 * n ≤ (8 * n + 1) * 2 ^ n + 2 * n * 2 ^ (min n (w + 1)) ∧
      (∀ (i : Fin n) (b : Bool),
        (F.filter (fun D => (Sum.inl (Sum.inl i), b) ∈ D)).card = 1) ∧
      (∀ (i : Fin n) (p : Fin (w + 1) → Bool),
        (F.filter (fun D => (Sum.inl (Sum.inr (i, p)), false) ∈ D)).card = 0 ∧
        (F.filter (fun D => (Sum.inl (Sum.inr (i, p)), true) ∈ D)).card =
          (if ∃ x : Fin n → Bool, ∀ j : Fin (w + 1), x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ = p j then 1 else 0)) ∧
      (∀ D ∈ F, D.card ≤ 3) ∧
      (∀ a : V → Bool, accepts a ↔ ∃ aux : Fin m → Bool,
        Satisfies (Sum.elim a aux) (↑F : Set _)) ∧
      ∀ ρ : V → Option Bool,
        let assumptions : Set (Literal (Sum V (Fin m))) :=
          {l | ∃ v : V, l.1 = Sum.inl v ∧ ρ v = some l.2}
        let completion := fun (a : V → Bool) =>
          accepts a ∧ ∀ (v : V) (b : Bool), ρ v = some b → a v = b
        ((¬ ∃ a : V → Bool, completion a) ↔
          ∃ D ∈ F, ∀ l ∈ D, UPForces (↑F : Set _) assumptions (negLit l)) ∧
        ((∃ a : V → Bool, completion a) → ∀ (v : V) (b : Bool),
          (∀ a : V → Bool, completion a → a v = b) ↔
            UPForces (↑F : Set _) assumptions (Sum.inl v, b)) := by
  refine ⟨mAux n, F_all (w := w) hn, size_bound hn, bit_occ_count hn, perm_occ_count hn,
    is_3cnf hn, sat_iff_accepts hn, fun ρ => ⟨up_complete_unsat hn ρ, up_complete_sat hn ρ⟩⟩

end PEqualNP.Outside.L_pcx_230_aux

theorem PEqualNP.Outside.L_pcx_230 : (∀ (n w : ℕ) (hn : 0 < n),
  let V := Sum (Fin n) (Fin n × (Fin (w + 1) → Bool))
  let accepts := fun (a : V → Bool) =>
    ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true
  letI : DecidableEq V := Classical.typeDecidableEq V
  ∃ (m : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m)))),
    letI : DecidableEq (Sum V (Fin m)) := Classical.typeDecidableEq _
    m + (∑ D ∈ F, D.card) + 3*n ≤ (8*n+1)*2^n + 2*n*2^(min n (w+1)) ∧
    (∀ (i : Fin n) (b : Bool),
      (F.filter (fun D => (Sum.inl (Sum.inl i), b) ∈ D)).card = 1) ∧
    (∀ (i : Fin n) (p : Fin (w+1) → Bool),
      (F.filter (fun D => (Sum.inl (Sum.inr (i,p)), false) ∈ D)).card = 0 ∧
      (F.filter (fun D => (Sum.inl (Sum.inr (i,p)), true) ∈ D)).card =
        (if ∃ x : Fin n → Bool, ∀ j : Fin (w+1), x ⟨(i.val+j.val)%n, Nat.mod_lt _ hn⟩ = p j then 1 else 0)) ∧
    (∀ D ∈ F, D.card ≤ 3) ∧
    (∀ a : V → Bool, accepts a ↔ ∃ aux : Fin m → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim a aux) (↑F : Set _)) ∧
    ∀ ρ : V → Option Bool,
      let assumptions : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) :=
        {l | ∃ v : V, l.1 = Sum.inl v ∧ ρ v = some l.2}
      let completion := fun (a : V → Bool) =>
        accepts a ∧ ∀ (v : V) (b : Bool), ρ v = some b → a v = b
      ((¬ ∃ a : V → Bool, completion a) ↔
        ∃ D ∈ F, ∀ l ∈ D, PEqualNP.Search.UPForces (↑F : Set _) assumptions
          (PEqualNP.Search.negLit l)) ∧
      ((∃ a : V → Bool, completion a) → ∀ (v : V) (b : Bool),
        (∀ a : V → Bool, completion a → a v = b) ↔
          PEqualNP.Search.UPForces (↑F : Set _) assumptions (Sum.inl v, b))) := by
  exact PEqualNP.Outside.L_pcx_230_aux.prove_230
