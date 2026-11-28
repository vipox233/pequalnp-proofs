import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_469_aux

open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

section ObsFormula

abbrev pairOf (t : ℕ) := {p : Fin t × Fin t // p.1 < p.2}

lemma card_filter_add_not {α : Type} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1))]
  congr 1; ext x; simp; tauto

def tailFn (t : ℕ) (e : Fin 3 × Fin t) : Option (Fin t × Bool) :=
  if e.1 = 0 then some (e.2, false) else none

def headFn (t : ℕ) (e : Fin 3 × Fin t) : Option (Fin t × Bool) :=
  some (e.2, decide (e.1 ≠ 1))

def weightFn {t : ℕ} (g : Option (pairOf t)) (e : Fin 3 × Fin t) (diff : Bool) : ℕ :=
  if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
  if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
    (if diff then 1 else 3) else 2

def obsFn {t : ℕ} (g : Option (pairOf t)) (p : Fin t → Fin 3) : ℕ :=
  ∑ x : Option (Fin t × Bool) → Bool,
    if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i, false)) then 2 else 1)) ∧
      (Finset.univ.filter (fun e : Fin 3 × Fin t => x (tailFn t e) ≠ x (headFn t e))).card = 2 * t then
      ∏ e : Fin 3 × Fin t, weightFn g e (xor (x (tailFn t e)) (x (headFn t e))) else 0

def readFn {t k : ℕ} (G : Fin k → Option (pairOf t)) (p : Fin t → Fin 3) : ℕ :=
  ∏ l : Fin k, obsFn (G l) p

def zCount {t : ℕ} (p : Fin t → Fin 3) : ℕ :=
  (Finset.univ.filter (fun i : Fin t => p i = 0)).card

def isLike {t : ℕ} (g : Option (pairOf t)) (p : Fin t → Fin 3) : Bool :=
  g.elim false (fun e => decide (p e.val.1 ≠ 0 ∧ p e.val.1 = p e.val.2))

def isUnlike {t : ℕ} (g : Option (pairOf t)) (p : Fin t → Fin 3) : Bool :=
  g.elim false (fun e => decide (p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 ∧ p e.val.1 ≠ p e.val.2))

def likeCount {t k : ℕ} (G : Fin k → Option (pairOf t)) (p : Fin t → Fin 3) : ℕ :=
  (Finset.univ.filter (fun l : Fin k => isLike (G l) p = true)).card

def unlikeCount {t k : ℕ} (G : Fin k → Option (pairOf t)) (p : Fin t → Fin 3) : ℕ :=
  (Finset.univ.filter (fun l : Fin k => isUnlike (G l) p = true)).card

def targetMass (t k z L U : ℕ) : ℕ :=
  2 ^ (k * (t + z - 1)) * 4 ^ (k - L - U) * 5 ^ L * 3 ^ U

lemma cut_card_of_opp {t : ℕ} (x : Option (Fin t × Bool) → Bool)
    (hopp : ∀ i : Fin t, x (some (i, false)) ≠ x (some (i, true))) :
    (Finset.univ.filter (fun e : Fin 3 × Fin t => x (tailFn t e) ≠ x (headFn t e))).card = 2 * t := by
  have hpart : ∀ i : Fin t,
      ((Finset.univ : Finset (Fin 3)).filter (fun j : Fin 3 => x (tailFn t (j, i)) ≠ x (headFn t (j, i)))).card = 2 := by
    intro i
    have hi := hopp i
    have h0 : x (tailFn t (0, i)) ≠ x (headFn t (0, i)) := by simpa [tailFn, headFn] using hi
    have h12 : (x (tailFn t (1, i)) ≠ x (headFn t (1, i))) ↔ ¬ (x (tailFn t (2, i)) ≠ x (headFn t (2, i))) := by
      simp only [tailFn, headFn, Fin.isValue, ne_eq, decide_not, Bool.not_eq_true']
      cases hc : x none <;> cases hxf : x (some (i, false)) <;> cases hxt : x (some (i, true)) <;>
        simp_all
    have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [huniv]
    by_cases h1 : x (tailFn t (1, i)) ≠ x (headFn t (1, i))
    · have h2 : ¬ (x (tailFn t (2, i)) ≠ x (headFn t (2, i))) := h12.mp h1
      simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]
    · have h2 : x (tailFn t (2, i)) ≠ x (headFn t (2, i)) := by tauto
      simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2]
  have heq : (Finset.univ.filter (fun e : Fin 3 × Fin t => x (tailFn t e) ≠ x (headFn t e))).card =
      ∑ i : Fin t, ((Finset.univ : Finset (Fin 3)).filter (fun j : Fin 3 => x (tailFn t (j, i)) ≠ x (headFn t (j, i)))).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [heq]
  simp_rw [hpart]
  simp [mul_comm]

lemma prod_zero_of_not_opp {t : ℕ} (g : Option (pairOf t)) (x : Option (Fin t × Bool) → Bool)
    (hnot : ¬ ∀ i : Fin t, x (some (i, false)) ≠ x (some (i, true))) :
    ∏ e : Fin 3 × Fin t, weightFn g e (xor (x (tailFn t e)) (x (headFn t e))) = 0 := by
  push_neg at hnot
  rcases hnot with ⟨i, hi⟩
  refine Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin 3), i)) ?_
  simp [weightFn, tailFn, headFn, hi]

def extAssign {t : ℕ} (c : Bool) (y : Fin t → Bool) : Option (Fin t × Bool) → Bool
  | none => c
  | some (i, false) => y i
  | some (i, true) => !(y i)

lemma obsFn_eq_sum_pair {t : ℕ} (g : Option (pairOf t)) (p : Fin t → Fin 3) :
    obsFn g p = ∑ c : Bool, ∏ i : Fin t,
      ∑ b : Bool,
        if p i = 0 ∨ p i = (if b then 2 else 1) then
          (if g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
            (if xor c b then 1 else 3) else 2)
        else 0 := by
  unfold obsFn
  have h1 : (∑ x : Option (Fin t × Bool) → Bool,
      if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i, false)) then 2 else 1)) ∧
        (Finset.univ.filter (fun e : Fin 3 × Fin t => x (tailFn t e) ≠ x (headFn t e))).card = 2 * t then
        ∏ e : Fin 3 × Fin t, weightFn g e (xor (x (tailFn t e)) (x (headFn t e))) else 0) =
      ∑ x ∈ Finset.univ.filter (fun x : Option (Fin t × Bool) → Bool =>
          ∀ i : Fin t, x (some (i, false)) ≠ x (some (i, true))),
        if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i, false)) then 2 else 1)) then
          ∏ e : Fin 3 × Fin t, weightFn g e (xor (x (tailFn t e)) (x (headFn t e))) else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hopp : ∀ i : Fin t, x (some (i, false)) ≠ x (some (i, true))
    · simp [hopp, cut_card_of_opp x hopp]
    · simp only [hopp, ↓reduceIte]
      split_ifs
      · exact prod_zero_of_not_opp g x hopp
      · rfl
  rw [h1]
  let φ : Bool × (Fin t → Bool) → Option (Fin t × Bool) → Bool := fun z => extAssign z.1 z.2
  have hsum_bij : (∑ x ∈ Finset.univ.filter (fun x : Option (Fin t × Bool) → Bool =>
          ∀ i : Fin t, x (some (i, false)) ≠ x (some (i, true))),
        if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i, false)) then 2 else 1)) then
          ∏ e : Fin 3 × Fin t, weightFn g e (xor (x (tailFn t e)) (x (headFn t e))) else 0) =
      ∑ z : Bool × (Fin t → Bool),
        if (∀ i : Fin t, p i = 0 ∨ p i = (if z.2 i then 2 else 1)) then
          ∏ i : Fin t, (if g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
            (if xor z.1 (z.2 i) then 1 else 3) else 2) else 0 := by
    refine Finset.sum_bij' (fun x _ => (x none, fun i => x (some (i, false))))
      (fun z _ => φ z) ?_ ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro z _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, φ, extAssign]
      intro i; cases z.2 i <;> decide
    · intro x hx
      have hopp := (Finset.mem_filter.mp hx).2
      funext v
      rcases v with _ | ⟨i, b⟩
      · rfl
      · cases b
        · rfl
        · dsimp [φ, extAssign]
          have hi := hopp i
          cases hxf : x (some (i, false)) <;> cases hxt : x (some (i, true)) <;> simp_all
    · intro z _
      ext <;> rfl
    · intro x hx
      have hopp := (Finset.mem_filter.mp hx).2
      split_ifs with hp
      · rw [Fintype.prod_prod_type_right]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
        rw [huniv]
        simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton, Finset.prod_singleton,
          Fin.isValue, Fin.reduceEq, or_self, not_false_eq_true]
        have h0 : weightFn g (0, i) (xor (x (tailFn t (0, i))) (x (headFn t (0, i)))) = 1 := by
          have hi := hopp i
          simp only [weightFn, tailFn, headFn, ↓reduceIte]
          cases hxf : x (some (i, false)) <;> cases hxt : x (some (i, true)) <;> simp_all
        have h2 : weightFn g (2, i) (xor (x (tailFn t (2, i))) (x (headFn t (2, i)))) = 1 := by
          simp [weightFn]
        rw [h0, h2, one_mul, mul_one]
        simp [weightFn, tailFn, headFn]
      · rfl
  rw [hsum_bij, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hps : (∏ i : Fin t, ∑ b : Bool,
      if p i = 0 ∨ p i = (if b then 2 else 1) then
        (if g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
          (if xor c b then 1 else 3) else 2)
      else 0) = ∑ y : Fin t → Bool, ∏ i : Fin t,
      if p i = 0 ∨ p i = (if y i then 2 else 1) then
        (if g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
          (if xor c (y i) then 1 else 3) else 2)
      else 0 := Fintype.prod_sum (fun (i : Fin t) (b : Bool) =>
        (if p i = 0 ∨ p i = (if b then 2 else 1) then
          (if g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
            (if xor c b then 1 else 3) else 2)
        else 0 : ℕ))
  rw [hps]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hp : ∀ i : Fin t, p i = 0 ∨ p i = (if y i then 2 else 1)
  · rw [if_pos hp]
    congr 1; funext i
    exact (if_pos (hp i)).symm
  · simp only [hp, ↓reduceIte]
    push_neg at hp
    rcases hp with ⟨i, hi1, hi2⟩
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [hi1, hi2]

lemma single_factor_not_mem {t : ℕ} (g : Option (pairOf t)) (p : Fin t → Fin 3) (c : Bool) (i : Fin t)
    (hnot : g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) = false) :
    (∑ b : Bool, if p i = 0 ∨ p i = (if b then 2 else 1) then
      (if g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
        (if xor c b then 1 else 3) else 2) else 0) =
      if p i = 0 then 4 else 2 := by
  rw [hnot]
  generalize p i = pi
  fin_cases pi <;> simp

lemma single_factor_mem_zero {t : ℕ} (g : Option (pairOf t)) (p : Fin t → Fin 3) (c : Bool) (i : Fin t)
    (hmem : g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) = true)
    (hp0 : p i = 0) :
    (∑ b : Bool, if p i = 0 ∨ p i = (if b then 2 else 1) then
      (if g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
        (if xor c b then 1 else 3) else 2) else 0) = 4 := by
  rw [hmem, hp0]
  cases c <;> simp

lemma single_factor_mem_nz {t : ℕ} (g : Option (pairOf t)) (p : Fin t → Fin 3) (c : Bool) (i : Fin t)
    (hmem : g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) = true)
    (hpnz : p i ≠ 0) :
    (∑ b : Bool, if p i = 0 ∨ p i = (if b then 2 else 1) then
      (if g.elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
        (if xor c b then 1 else 3) else 2) else 0) =
      if p i = (if c then 2 else 1) then 3 else 1 := by
  rw [hmem]
  have hpi : p i = 1 ∨ p i = 2 := by
    have := (p i).isLt
    have h0 : (p i).val ≠ 0 := fun h => hpnz (Fin.ext h)
    omega
  rcases hpi with h | h <;> rw [h] <;> cases c <;> simp

lemma prod_two_four {t : ℕ} (S : Finset (Fin t)) (p : Fin t → Fin 3) :
    ∏ i ∈ S, (if p i = 0 then (4 : ℕ) else 2) =
      2 ^ (S.card + (S.filter (fun i => p i = 0)).card) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.card_insert_of_notMem ha, Finset.filter_insert]
    by_cases hp : p a = 0
    · simp only [hp, ↓reduceIte, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.mp h).1)]
      have : (s.card + 1) + ((s.filter (fun i => p i = 0)).card + 1) =
          (s.card + (s.filter (fun i => p i = 0)).card) + 2 := by omega
      rw [this, pow_add]; ring
    · simp only [hp, ↓reduceIte]
      have : (s.card + 1) + (s.filter (fun i => p i = 0)).card =
          (s.card + (s.filter (fun i => p i = 0)).card) + 1 := by omega
      rw [this, pow_succ]; ring

lemma obs_some_table (a b : Fin 3) (cR t z : ℕ)
    (ht : 2 ≤ t) (hR : cR + 2 = t + (z - ((if a = 0 then 1 else 0) + (if b = 0 then 1 else 0))))
    (hz : (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) ≤ z) :
    ((if a = 0 then 4 else if a = 2 then 3 else 1) * (if b = 0 then 4 else if b = 2 then 3 else 1) * 2 ^ cR +
     (if a = 0 then 4 else if a = 1 then 3 else 1) * (if b = 0 then 4 else if b = 1 then 3 else 1) * 2 ^ cR) =
    (if decide (a ≠ 0 ∧ a = b) then 5 else if decide (a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) then 3 else 4) * 2 ^ (t + z - 1) := by
  have hpow_base : ∀ e : ℕ, 2 ^ (cR + e) = 2 ^ e * 2 ^ cR := by
    intro e; rw [pow_add, mul_comm]
  fin_cases a <;> fin_cases b <;> simp at hR hz ⊢
  all_goals first
    | (have hexp : t + z - 1 = cR + 3 := by omega
       rw [hexp, hpow_base 3]; ring)
    | (have hexp : t + z - 1 = cR + 2 := by omega
       rw [hexp, hpow_base 2]; ring)
    | (have hexp : t + z - 1 = cR + 1 := by omega
       rw [hexp, hpow_base 1]; ring)

lemma obsFn_formula {t : ℕ} (ht : 2 ≤ t) (g : Option (pairOf t)) (p : Fin t → Fin 3) :
    obsFn g p = (if isLike g p then 5 else if isUnlike g p then 3 else 4) * 2 ^ (t + zCount p - 1) := by
  rw [obsFn_eq_sum_pair]
  rcases g with _ | ⟨⟨u, v⟩, huv⟩
  · have hpt : ∀ c : Bool, ∏ i : Fin t,
        (∑ b : Bool, if p i = 0 ∨ p i = (if b then 2 else 1) then
          (if (none : Option (pairOf t)).elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
            (if xor c b then 1 else 3) else 2) else 0) =
        2 ^ (t + zCount p) := by
      intro c
      have h1 : ∀ i : Fin t, (∑ b : Bool, if p i = 0 ∨ p i = (if b then 2 else 1) then
          (if (none : Option (pairOf t)).elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
            (if xor c b then 1 else 3) else 2) else 0) = if p i = 0 then 4 else 2 := by
        intro i; simp only [Option.elim_none, Bool.false_eq_true, ↓reduceIte]
        generalize p i = pi; fin_cases pi <;> simp
      rw [Finset.prod_congr rfl (fun i _ => h1 i), prod_two_four Finset.univ p, Finset.card_univ, Fintype.card_fin]
      rfl
    have hsum_eq : (∑ c : Bool, ∏ i : Fin t,
        ∑ b : Bool, if p i = 0 ∨ p i = (if b then 2 else 1) then
          (if (none : Option (pairOf t)).elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
            (if xor c b then 1 else 3) else 2) else 0) = ∑ _c : Bool, 2 ^ (t + zCount p) :=
      Finset.sum_congr rfl (fun c _ => hpt c)
    rw [hsum_eq]
    simp only [isLike, isUnlike, Option.elim_none, Bool.false_eq_true, ↓reduceIte, Fintype.sum_bool]
    have hpow : 2 ^ (t + zCount p) = 2 * 2 ^ (t + zCount p - 1) := by
      have : t + zCount p = (t + zCount p - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
      ring
    rw [hpow]; ring
  · have huv_ne : u ≠ v := ne_of_lt huv
    let R : Finset (Fin t) := (Finset.univ.erase u).erase v
    have hv_in : v ∈ Finset.univ.erase u := Finset.mem_erase.mpr ⟨huv_ne.symm, Finset.mem_univ _⟩
    have hR_card : R.card + 2 = t := by
      simp only [R, Finset.card_erase_of_mem hv_in, Finset.card_erase_of_mem (Finset.mem_univ u),
        Finset.card_univ, Fintype.card_fin]
      omega
    have hR_prod : ∀ c : Bool,
        ∏ i ∈ R, (∑ b : Bool, if p i = 0 ∨ p i = (if b then 2 else 1) then
          (if (some (⟨(u, v), huv⟩ : pairOf t)).elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
            (if xor c b then 1 else 3) else 2) else 0) =
        2 ^ (R.card + (R.filter (fun i => p i = 0)).card) := by
      intro c
      have h1 : ∀ i ∈ R, (∑ b : Bool, if p i = 0 ∨ p i = (if b then 2 else 1) then
          (if (some (⟨(u, v), huv⟩ : pairOf t)).elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
            (if xor c b then 1 else 3) else 2) else 0) =
          if p i = 0 then 4 else 2 := by
        intro i hi
        have hne_v : i ≠ v := (Finset.mem_erase.mp hi).1
        have hne_u : i ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        have hdec : (some (⟨(u, v), huv⟩ : pairOf t)).elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) = false := by
          simp [hne_u.symm, hne_v.symm]
        rw [hdec]
        simp only [Bool.false_eq_true, ↓reduceIte]
        generalize p i = pi; fin_cases pi <;> simp
      rw [Finset.prod_congr rfl h1, prod_two_four R p]
    have hsplit : ∀ (f : Fin t → ℕ), ∏ i : Fin t, f i = f u * f v * ∏ i ∈ R, f i := by
      intro f
      have h1 : ∏ i : Fin t, f i = f u * ∏ i ∈ Finset.univ.erase u, f i :=
        (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ u)).symm
      have h2 : ∏ i ∈ Finset.univ.erase u, f i = f v * ∏ i ∈ R, f i :=
        (Finset.mul_prod_erase (Finset.univ.erase u) f hv_in).symm
      rw [h1, h2, mul_assoc]
    have hz_split : zCount p = (if p u = 0 then 1 else 0) + (if p v = 0 then 1 else 0) +
        (R.filter (fun i => p i = 0)).card := by
      unfold zCount
      have h1 : Finset.univ = insert u (insert v R) := by
        ext i; simp only [R, Finset.mem_univ, Finset.mem_insert, Finset.mem_erase, true_iff]
        by_cases hiu : i = u
        · exact Or.inl hiu
        · by_cases hiv : i = v
          · exact Or.inr (Or.inl hiv)
          · exact Or.inr (Or.inr ⟨hiv, hiu, trivial⟩)
      have hu_not_R : u ∉ R.filter (fun i => p i = 0) := by simp [R]
      have hu_not_ins : u ∉ insert v (R.filter (fun i => p i = 0)) := by simp [R, huv_ne]
      have hv_not_R : v ∉ R.filter (fun i => p i = 0) := by simp [R]
      rw [h1, Finset.filter_insert, Finset.filter_insert]
      by_cases hpu : p u = 0 <;> by_cases hpv : p v = 0
      · simp only [hpu, hpv, ↓reduceIte, Finset.card_insert_of_notMem hu_not_ins,
          Finset.card_insert_of_notMem hv_not_R]; omega
      · simp only [hpu, hpv, ↓reduceIte, Finset.card_insert_of_notMem hu_not_R]; omega
      · simp only [hpu, hpv, ↓reduceIte, Finset.card_insert_of_notMem hv_not_R]; omega
      · simp only [hpu, hpv, ↓reduceIte]; omega
    have hfact_c : ∀ c : Bool,
        (∏ i : Fin t, ∑ b : Bool, if p i = 0 ∨ p i = (if b then 2 else 1) then
          (if (some (⟨(u, v), huv⟩ : pairOf t)).elim false (fun q => decide (q.val.1 = i ∨ q.val.2 = i)) then
            (if xor c b then 1 else 3) else 2) else 0) =
        (if p u = 0 then 4 else if p u = (if c then 2 else 1) then 3 else 1) *
        (if p v = 0 then 4 else if p v = (if c then 2 else 1) then 3 else 1) *
        2 ^ (R.card + (R.filter (fun i => p i = 0)).card) := by
      intro c
      rw [hsplit, hR_prod c]
      have hfu : (∑ b : Bool, if p u = 0 ∨ p u = (if b then 2 else 1) then
          (if (some (⟨(u, v), huv⟩ : pairOf t)).elim false (fun q => decide (q.val.1 = u ∨ q.val.2 = u)) then
            (if xor c b then 1 else 3) else 2) else 0) =
          if p u = 0 then 4 else if p u = (if c then 2 else 1) then 3 else 1 := by
        have hd : (some (⟨(u, v), huv⟩ : pairOf t)).elim false (fun q => decide (q.val.1 = u ∨ q.val.2 = u)) = true := by
          simp
        rw [hd]; simp only [↓reduceIte]; generalize p u = pu; fin_cases pu <;> cases c <;> simp
      have hfv : (∑ b : Bool, if p v = 0 ∨ p v = (if b then 2 else 1) then
          (if (some (⟨(u, v), huv⟩ : pairOf t)).elim false (fun q => decide (q.val.1 = v ∨ q.val.2 = v)) then
            (if xor c b then 1 else 3) else 2) else 0) =
          if p v = 0 then 4 else if p v = (if c then 2 else 1) then 3 else 1 := by
        have hd : (some (⟨(u, v), huv⟩ : pairOf t)).elim false (fun q => decide (q.val.1 = v ∨ q.val.2 = v)) = true := by
          simp
        rw [hd]; simp only [↓reduceIte]; generalize p v = pv; fin_cases pv <;> cases c <;> simp
      rw [hfu, hfv]
    rw [Finset.sum_congr rfl (fun c _ => hfact_c c)]
    simp only [Fintype.sum_bool, isLike, isUnlike, Option.elim_some, ↓reduceIte, Bool.false_eq_true]
    exact obs_some_table (p u) (p v) (R.card + (R.filter (fun i => p i = 0)).card) t (zCount p) ht
      (by omega) (by omega)

lemma like_add_unlike_le {t k : ℕ} (G : Fin k → Option (pairOf t)) (p : Fin t → Fin 3) :
    likeCount G p + unlikeCount G p ≤ k := by
  unfold likeCount unlikeCount
  have hdisj : Disjoint (Finset.univ.filter (fun l : Fin k => isLike (G l) p = true))
      (Finset.univ.filter (fun l : Fin k => isUnlike (G l) p = true)) := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    have hl1 := (Finset.mem_filter.mp h1).2
    have hl2 := (Finset.mem_filter.mp h2).2
    rcases hgl : G l with _ | e
    · simp [isLike, hgl] at hl1
    · simp [isLike, isUnlike, hgl] at hl1 hl2
      exact hl2.2.2 hl1.2
  rw [← Finset.card_union_of_disjoint hdisj]
  exact (Finset.card_le_univ _).trans (by simp)

lemma readFn_formula {t k : ℕ} (ht : 2 ≤ t) (G : Fin k → Option (pairOf t)) (p : Fin t → Fin 3) :
    readFn G p = targetMass t k (zCount p) (likeCount G p) (unlikeCount G p) := by
  unfold readFn targetMass
  simp_rw [obsFn_formula ht]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm (t + zCount p - 1) k]
  let sL := Finset.univ.filter (fun l : Fin k => isLike (G l) p = true)
  let sU := Finset.univ.filter (fun l : Fin k => isUnlike (G l) p = true)
  let sO := Finset.univ.filter (fun l : Fin k => isLike (G l) p = false ∧ isUnlike (G l) p = false)
  have hdisjLU : Disjoint sL sU := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    have hl1 := (Finset.mem_filter.mp h1).2
    have hl2 := (Finset.mem_filter.mp h2).2
    rcases hgl : G l with _ | e
    · simp [isLike, hgl] at hl1
    · simp [isLike, isUnlike, hgl] at hl1 hl2
      exact hl2.2.2 hl1.2
  have hdisjLU_O : Disjoint (sL ∪ sU) sO := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    have ho := (Finset.mem_filter.mp h2).2
    rcases Finset.mem_union.mp h1 with hL | hU
    · rw [(Finset.mem_filter.mp hL).2] at ho; cases ho.1
    · rw [(Finset.mem_filter.mp hU).2] at ho; cases ho.2
  have huniv : (Finset.univ : Finset (Fin k)) = (sL ∪ sU) ∪ sO := by
    ext l
    simp only [sL, sU, sO, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    cases isLike (G l) p <;> cases isUnlike (G l) p <;> simp
  have hcardO : sO.card = k - likeCount G p - unlikeCount G p := by
    have h1 := congrArg Finset.card huniv
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_union_of_disjoint hdisjLU_O,
        Finset.card_union_of_disjoint hdisjLU] at h1
    change k = likeCount G p + unlikeCount G p + sO.card at h1
    omega
  have hprod : ∏ l : Fin k, (if isLike (G l) p = true then 5 else if isUnlike (G l) p = true then 3 else 4) =
      5 ^ sL.card * 3 ^ sU.card * 4 ^ sO.card := by
    conv_lhs => rw [huniv]
    rw [Finset.prod_union hdisjLU_O, Finset.prod_union hdisjLU]
    have hL : ∏ l ∈ sL, (if isLike (G l) p = true then 5 else if isUnlike (G l) p = true then 3 else 4) = 5 ^ sL.card := by
      rw [← Finset.prod_const]
      refine Finset.prod_congr rfl (fun l hl => ?_)
      simp [(Finset.mem_filter.mp hl).2]
    have hU : ∏ l ∈ sU, (if isLike (G l) p = true then 5 else if isUnlike (G l) p = true then 3 else 4) = 3 ^ sU.card := by
      rw [← Finset.prod_const]
      refine Finset.prod_congr rfl (fun l hl => ?_)
      have hnotL : isLike (G l) p ≠ true := fun h =>
        Finset.disjoint_left.mp hdisjLU (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩) hl
      simp [hnotL, (Finset.mem_filter.mp hl).2]
    have hO : ∏ l ∈ sO, (if isLike (G l) p = true then 5 else if isUnlike (G l) p = true then 3 else 4) = 4 ^ sO.card := by
      rw [← Finset.prod_const]
      refine Finset.prod_congr rfl (fun l hl => ?_)
      have ho := (Finset.mem_filter.mp hl).2
      simp [ho.1, ho.2]
    rw [hL, hU, hO]
  rw [hprod, hcardO]
  change 5 ^ likeCount G p * 3 ^ unlikeCount G p * 4 ^ (k - likeCount G p - unlikeCount G p) * 2 ^ (k * (t + zCount p - 1)) = _
  ring

lemma targetMass_lt {t k z L U : ℕ} (ht : 2 ≤ t) (hz : z ≤ t) (hLU : L + U ≤ k) :
    targetMass t k z L U < 2 ^ (k * (2 * t + 2) + 1) := by
  unfold targetMass
  have h1 : 4 ^ (k - L - U) * 5 ^ L * 3 ^ U ≤ 8 ^ k := by
    have h4 : 4 ^ (k - L - U) ≤ 8 ^ (k - L - U) := Nat.pow_le_pow_left (by omega) _
    have h5 : 5 ^ L ≤ 8 ^ L := Nat.pow_le_pow_left (by omega) _
    have h3 : 3 ^ U ≤ 8 ^ U := Nat.pow_le_pow_left (by omega) _
    calc 4 ^ (k - L - U) * 5 ^ L * 3 ^ U
        ≤ 8 ^ (k - L - U) * 8 ^ L * 8 ^ U := Nat.mul_le_mul (Nat.mul_le_mul h4 h5) h3
      _ = 8 ^ ((k - L - U) + L + U) := by rw [← pow_add, ← pow_add]
      _ = 8 ^ k := by congr 1; omega
  have h2 : 2 ^ (k * (t + z - 1)) ≤ 2 ^ (k * (2 * t - 1)) :=
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left k (by omega))
  have h3 : 2 ^ (k * (t + z - 1)) * 4 ^ (k - L - U) * 5 ^ L * 3 ^ U ≤ 2 ^ (k * (2 * t + 2)) := by
    calc 2 ^ (k * (t + z - 1)) * 4 ^ (k - L - U) * 5 ^ L * 3 ^ U
        = 2 ^ (k * (t + z - 1)) * (4 ^ (k - L - U) * 5 ^ L * 3 ^ U) := by ring
      _ ≤ 2 ^ (k * (2 * t - 1)) * 8 ^ k := Nat.mul_le_mul h2 h1
      _ = 2 ^ (k * (2 * t - 1)) * (2 ^ 3) ^ k := by norm_num
      _ = 2 ^ (k * (2 * t - 1) + 3 * k) := by rw [← pow_mul, ← pow_add]
      _ = 2 ^ (k * (2 * t + 2)) := by
          congr 1
          have : 2 * t - 1 + 3 = 2 * t + 2 := by omega
          calc k * (2 * t - 1) + 3 * k = k * ((2 * t - 1) + 3) := by ring
            _ = k * (2 * t + 2) := by rw [this]
  have hpos : 0 < 2 ^ (k * (2 * t + 2)) := Nat.pos_of_ne_zero (by positivity)
  rw [pow_succ]
  omega

lemma readFn_lt {t k : ℕ} (ht : 2 ≤ t) (G : Fin k → Option (pairOf t)) (p : Fin t → Fin 3) :
    readFn G p < 2 ^ (k * (2 * t + 2) + 1) := by
  rw [readFn_formula ht]
  exact targetMass_lt ht ((Finset.card_le_univ _).trans (by simp)) (like_add_unlike_le G p)

lemma targetMass_injective {t k z L1 U1 L2 U2 : ℕ}
    (heq : targetMass t k z L1 U1 = targetMass t k z L2 U2) :
    L1 = L2 ∧ U1 = U2 := by
  unfold targetMass at heq
  have hpos2 : 0 < 2 ^ (k * (t + z - 1)) := by positivity
  have hc : 4 ^ (k - L1 - U1) * 5 ^ L1 * 3 ^ U1 = 4 ^ (k - L2 - U2) * 5 ^ L2 * 3 ^ U2 := by
    have h1 : 2 ^ (k * (t + z - 1)) * (4 ^ (k - L1 - U1) * 5 ^ L1 * 3 ^ U1) =
        2 ^ (k * (t + z - 1)) * (4 ^ (k - L2 - U2) * 5 ^ L2 * 3 ^ U2) := by linarith
    exact Nat.eq_of_mul_eq_mul_left hpos2 h1
  have hfac := congrArg Nat.factorization hc
  have hfac_aux : ∀ a b c : ℕ,
      (4 ^ a * 5 ^ b * 3 ^ c).factorization 5 = b ∧
      (4 ^ a * 5 ^ b * 3 ^ c).factorization 3 = c := by
    intro a b c
    have h4 : 4 ^ a = 2 ^ (2 * a) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h4, Nat.factorization_mul (by positivity) (by positivity),
        Nat.factorization_mul (by positivity) (by positivity),
        Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow]
    constructor
    · simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 5),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 2),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 3)]
    · simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 3),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 5)]
  have h5 := (hfac_aux (k - L1 - U1) L1 U1).1
  have h5' := (hfac_aux (k - L2 - U2) L2 U2).1
  have h3 := (hfac_aux (k - L1 - U1) L1 U1).2
  have h3' := (hfac_aux (k - L2 - U2) L2 U2).2
  have e5 := congrFun (congrArg DFunLike.coe hfac) 5
  have e3 := congrFun (congrArg DFunLike.coe hfac) 3
  exact ⟨by rw [← h5, ← h5', e5], by rw [← h3, ← h3', e3]⟩

end ObsFormula

section LocalModels

def spinZ (c : Fin 3) : ℤ :=
  if c = 0 then 0 else if c = 1 then 1 else -1

abbrev LocPair (B : ℕ) := {p : Fin B × Fin B // p.1 ≤ p.2}
abbrev LocSlot (B : ℕ) := Option (LocPair B)
abbrev LocModel (B k : ℕ) := Fin k → LocSlot B

def ordPair {B : ℕ} (a b : Fin B) : LocPair B :=
  if h : a ≤ b then ⟨(a, b), h⟩ else ⟨(b, a), le_of_not_ge h⟩

def projSlot {t B : ℕ} (h : Fin t → Fin B) (s : Option (pairOf t)) : LocSlot B :=
  s.map (fun e => ordPair (h e.val.1) (h e.val.2))

def projModel {t B k : ℕ} (h : Fin t → Fin B) (G : Fin k → Option (pairOf t)) : LocModel B k :=
  fun l => projSlot h (G l)

def locLike {B : ℕ} (s : LocSlot B) (q : Fin B → Fin 3) : Bool :=
  s.elim false (fun e => decide (q e.val.1 ≠ 0 ∧ q e.val.1 = q e.val.2))

def locUnlike {B : ℕ} (s : LocSlot B) (q : Fin B → Fin 3) : Bool :=
  s.elim false (fun e => decide (q e.val.1 ≠ 0 ∧ q e.val.2 ≠ 0 ∧ q e.val.1 ≠ q e.val.2))

def locLikeCount {B k : ℕ} (M : LocModel B k) (q : Fin B → Fin 3) : ℕ :=
  (Finset.univ.filter (fun l : Fin k => locLike (M l) q = true)).card

def locUnlikeCount {B k : ℕ} (M : LocModel B k) (q : Fin B → Fin 3) : ℕ :=
  (Finset.univ.filter (fun l : Fin k => locUnlike (M l) q = true)).card

lemma locLike_add_locUnlike_le {B k : ℕ} (M : LocModel B k) (q : Fin B → Fin 3) :
    locLikeCount M q + locUnlikeCount M q ≤ k := by
  unfold locLikeCount locUnlikeCount
  have hdisj : Disjoint (Finset.univ.filter (fun l : Fin k => locLike (M l) q = true))
      (Finset.univ.filter (fun l : Fin k => locUnlike (M l) q = true)) := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    have hl1 := (Finset.mem_filter.mp h1).2
    have hl2 := (Finset.mem_filter.mp h2).2
    rcases hml : M l with _ | e
    · simp [locLike, hml] at hl1
    · simp [locLike, locUnlike, hml] at hl1 hl2
      exact hl2.2.2 hl1.2
  rw [← Finset.card_union_of_disjoint hdisj]
  exact (Finset.card_le_univ _).trans (by simp)

lemma proj_like_eq {t B k : ℕ} (h : Fin t → Fin B) (G : Fin k → Option (pairOf t)) (q : Fin B → Fin 3) :
    likeCount G (q ∘ h) = locLikeCount (projModel h G) q := by
  unfold likeCount locLikeCount
  congr 1; ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold projModel projSlot
  cases G l with
  | none => simp [isLike, locLike]
  | some e =>
    simp only [Option.map_some, isLike, locLike, Option.elim_some, Function.comp_apply, ordPair]
    by_cases hle : h e.val.1 ≤ h e.val.2
    · simp [hle]
    · simp only [hle, ↓reduceDIte, decide_eq_true_eq]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨h2 ▸ h1, h2.symm⟩
      · intro ⟨h1, h2⟩; exact ⟨h2 ▸ h1, h2.symm⟩

lemma proj_unlike_eq {t B k : ℕ} (h : Fin t → Fin B) (G : Fin k → Option (pairOf t)) (q : Fin B → Fin 3) :
    unlikeCount G (q ∘ h) = locUnlikeCount (projModel h G) q := by
  unfold unlikeCount locUnlikeCount
  congr 1; ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold projModel projSlot
  cases G l with
  | none => simp [isUnlike, locUnlike]
  | some e =>
    simp only [Option.map_some, isUnlike, locUnlike, Option.elim_some, Function.comp_apply, ordPair]
    by_cases hle : h e.val.1 ≤ h e.val.2
    · simp [hle]
    · simp only [hle, ↓reduceDIte, decide_eq_true_eq]
      constructor
      · intro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3.symm⟩
      · intro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3.symm⟩

lemma slot_signed_aux (c1 c2 : Fin 3) :
    ((if decide (c1 ≠ 0 ∧ c1 = c2) = true then (1 : ℤ) else 0) -
      (if decide (c1 ≠ 0 ∧ c2 ≠ 0 ∧ c1 ≠ c2) = true then 1 else 0)) =
      spinZ c1 * spinZ c2 := by
  fin_cases c1 <;> fin_cases c2 <;> decide

lemma slot_signed {B : ℕ} (s : LocSlot B) (q : Fin B → Fin 3) :
    ((if locLike s q = true then (1 : ℤ) else 0) - (if locUnlike s q = true then 1 else 0)) =
      s.elim 0 (fun e => spinZ (q e.val.1) * spinZ (q e.val.2)) := by
  rcases s with _ | ⟨⟨a, b⟩, hab⟩
  · simp [locLike, locUnlike]
  · simp only [locLike, locUnlike, Option.elim_some]
    exact slot_signed_aux (q a) (q b)

def signedLoc {B k : ℕ} (M : LocModel B k) (q : Fin B → Fin 3) : ℤ :=
  (locLikeCount M q : ℤ) - (locUnlikeCount M q : ℤ)

lemma signedLoc_eq_sum {B k : ℕ} (M : LocModel B k) (q : Fin B → Fin 3) :
    signedLoc M q = ∑ l : Fin k, (M l).elim (0 : ℤ) (fun e => spinZ (q e.val.1) * spinZ (q e.val.2)) := by
  unfold signedLoc locLikeCount locUnlikeCount
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h := slot_signed (M l) q
  simpa using h

def noLoopsAt {B k : ℕ} (c1 c2 : Fin B) (M : LocModel B k) : Prop :=
  ∀ l : Fin k, M l ≠ some ⟨(c1, c1), le_rfl⟩ ∧ M l ≠ some ⟨(c2, c2), le_rfl⟩

def multAt {B k : ℕ} (c1 c2 : Fin B) (hc : c1 < c2) (M : LocModel B k) : ℕ :=
  (Finset.univ.filter (fun l : Fin k => M l = some ⟨(c1, c2), le_of_lt hc⟩)).card

lemma ternary_square_ge_4 (c A B E : ℤ) (hc : c ≠ 0) :
    4 ≤ ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
      (fun p => c * spinZ p.1 * spinZ p.2 + A * spinZ p.1 + B * spinZ p.2 + E ≠ 0)).card := by
  have hrow : ∀ x : Fin 3, c * spinZ x + B ≠ 0 →
      2 ≤ ((Finset.univ : Finset (Fin 3)).filter
        (fun y => c * spinZ x * spinZ y + A * spinZ x + B * spinZ y + E ≠ 0)).card := by
    intro x hx
    have hnot2 : ¬ (∃ y1 y2 : Fin 3, y1 ≠ y2 ∧
        c * spinZ x * spinZ y1 + A * spinZ x + B * spinZ y1 + E = 0 ∧
        c * spinZ x * spinZ y2 + A * spinZ x + B * spinZ y2 + E = 0) := by
      rintro ⟨y1, y2, hne, h1, h2⟩
      have hdiff : (c * spinZ x + B) * (spinZ y1 - spinZ y2) = 0 := by linarith
      rcases mul_eq_zero.mp hdiff with h0 | hs
      · exact hx h0
      · fin_cases y1 <;> fin_cases y2 <;> simp_all [spinZ]
    have hle1 : ((Finset.univ : Finset (Fin 3)).filter
        (fun y => c * spinZ x * spinZ y + A * spinZ x + B * spinZ y + E = 0)).card ≤ 1 := by
      by_contra hgt
      have h2 : 1 < ((Finset.univ : Finset (Fin 3)).filter
          (fun y => c * spinZ x * spinZ y + A * spinZ x + B * spinZ y + E = 0)).card := by omega
      rcases Finset.one_lt_card.mp h2 with ⟨y1, hy1, y2, hy2, hne⟩
      exact hnot2 ⟨y1, y2, hne, (Finset.mem_filter.mp hy1).2, (Finset.mem_filter.mp hy2).2⟩
    have htot := card_filter_add_not (Finset.univ : Finset (Fin 3))
      (fun y => c * spinZ x * spinZ y + A * spinZ x + B * spinZ y + E = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at htot
    change ((Finset.univ : Finset (Fin 3)).filter
        (fun y => c * spinZ x * spinZ y + A * spinZ x + B * spinZ y + E = 0)).card +
      ((Finset.univ : Finset (Fin 3)).filter
        (fun y => c * spinZ x * spinZ y + A * spinZ x + B * spinZ y + E ≠ 0)).card = 3 at htot
    omega
  have hbadx : ((Finset.univ : Finset (Fin 3)).filter (fun x => c * spinZ x + B = 0)).card ≤ 1 := by
    by_contra hgt
    have h2 : 1 < ((Finset.univ : Finset (Fin 3)).filter (fun x => c * spinZ x + B = 0)).card := by omega
    rcases Finset.one_lt_card.mp h2 with ⟨x1, hx1, x2, hx2, hne⟩
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2' := (Finset.mem_filter.mp hx2).2
    have hdiff : c * (spinZ x1 - spinZ x2) = 0 := by linarith
    rcases mul_eq_zero.mp hdiff with h0 | hs
    · exact hc h0
    · fin_cases x1 <;> fin_cases x2 <;> simp_all [spinZ]
  have hgoodx : 2 ≤ ((Finset.univ : Finset (Fin 3)).filter (fun x => c * spinZ x + B ≠ 0)).card := by
    have htot := card_filter_add_not (Finset.univ : Finset (Fin 3))
      (fun x => c * spinZ x + B = 0)
    simp only [Finset.card_univ, Fintype.card_fin] at htot
    change ((Finset.univ : Finset (Fin 3)).filter (fun x => c * spinZ x + B = 0)).card +
      ((Finset.univ : Finset (Fin 3)).filter (fun x => c * spinZ x + B ≠ 0)).card = 3 at htot
    omega
  have hsum : ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
      (fun p => c * spinZ p.1 * spinZ p.2 + A * spinZ p.1 + B * spinZ p.2 + E ≠ 0)).card =
      ∑ x : Fin 3, ((Finset.univ : Finset (Fin 3)).filter
        (fun y => c * spinZ x * spinZ y + A * spinZ x + B * spinZ y + E ≠ 0)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hsum]
  calc 4 = 2 * 2 := by norm_num
    _ ≤ ((Finset.univ : Finset (Fin 3)).filter (fun x => c * spinZ x + B ≠ 0)).card * 2 :=
        Nat.mul_le_mul_right 2 hgoodx
    _ = ∑ _x ∈ Finset.univ.filter (fun x => c * spinZ x + B ≠ 0), 2 := by simp
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x => c * spinZ x + B ≠ 0),
        ((Finset.univ : Finset (Fin 3)).filter
          (fun y => c * spinZ x * spinZ y + A * spinZ x + B * spinZ y + E ≠ 0)).card :=
        Finset.sum_le_sum (fun x hx => hrow x (Finset.mem_filter.mp hx).2)
    _ ≤ ∑ x : Fin 3, ((Finset.univ : Finset (Fin 3)).filter
        (fun y => c * spinZ x * spinZ y + A * spinZ x + B * spinZ y + E ≠ 0)).card :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

lemma signedLoc_update_poly {B k : ℕ} (c1 c2 : Fin B) (hc : c1 < c2)
    (M : LocModel B k) (hnl : noLoopsAt c1 c2 M) (q : Fin B → Fin 3) :
    ∃ A B' E : ℤ, ∀ x y : Fin 3,
      signedLoc M (Function.update (Function.update q c1 x) c2 y) =
        (multAt c1 c2 hc M : ℤ) * spinZ x * spinZ y + A * spinZ x + B' * spinZ y + E := by
  have hne12 : c1 ≠ c2 := ne_of_lt hc
  have hterm : ∀ l : Fin k, ∃ a b e : ℤ, ∀ x y : Fin 3,
      (M l).elim (0 : ℤ) (fun p =>
        spinZ (Function.update (Function.update q c1 x) c2 y p.val.1) *
        spinZ (Function.update (Function.update q c1 x) c2 y p.val.2)) =
      (if M l = some ⟨(c1, c2), le_of_lt hc⟩ then (1 : ℤ) else 0) * spinZ x * spinZ y +
        a * spinZ x + b * spinZ y + e := by
    intro l
    have hnl_l := hnl l
    rcases hml : M l with _ | ⟨⟨u, v⟩, huv⟩
    · exact ⟨0, 0, 0, fun x y => by simp⟩
    · by_cases hu1 : u = c1
      · rcases hu1 with rfl
        by_cases hv2 : v = c2
        · rcases hv2 with rfl
          refine ⟨0, 0, 0, fun x y => ?_⟩
          simp [hne12]
        · have hv1 : v ≠ u := by
            intro h; rcases h with rfl; exact hnl_l.1 hml
          refine ⟨spinZ (q v), 0, 0, fun x y => ?_⟩
          have hne_s : some (⟨(u, v), huv⟩ : LocPair B) ≠ some ⟨(u, c2), le_of_lt hc⟩ := by
            intro h; injection h with h1; exact hv2 (congrArg (fun p : LocPair B => p.1.2) h1)
          simp [hne_s, hne12, hv1, hv2]; ring
      · by_cases hu2 : u = c2
        · rcases hu2 with rfl
          have hv1 : v ≠ c1 := by
            intro h; rcases h with rfl; exact absurd (lt_of_lt_of_le hc huv) (lt_irrefl _)
          have hv2 : v ≠ u := by
            intro h; rcases h with rfl; exact hnl_l.2 hml
          refine ⟨0, spinZ (q v), 0, fun x y => ?_⟩
          have hne_s : some (⟨(u, v), huv⟩ : LocPair B) ≠ some ⟨(c1, u), le_of_lt hc⟩ := by
            intro h; injection h with h1; exact hne12.symm (congrArg (fun p : LocPair B => p.1.1) h1)
          simp [hne_s, hv1, hv2]; ring
        · by_cases hv1 : v = c1
          · rcases hv1 with rfl
            refine ⟨spinZ (q u), 0, 0, fun x y => ?_⟩
            have hne_s : some (⟨(u, v), huv⟩ : LocPair B) ≠ some ⟨(v, c2), le_of_lt hc⟩ := by
              intro h; injection h with h1; exact hu1 (congrArg (fun p : LocPair B => p.1.1) h1)
            simp [hne_s, hu1, hu2, hne12]
          · by_cases hv2 : v = c2
            · rcases hv2 with rfl
              refine ⟨0, spinZ (q u), 0, fun x y => ?_⟩
              have hne_s : some (⟨(u, v), huv⟩ : LocPair B) ≠ some ⟨(c1, v), le_of_lt hc⟩ := by
                intro h; injection h with h1; exact hu1 (congrArg (fun p : LocPair B => p.1.1) h1)
              simp [hne_s, hu1, hu2]
            · refine ⟨0, 0, spinZ (q u) * spinZ (q v), fun x y => ?_⟩
              have hne_s : some (⟨(u, v), huv⟩ : LocPair B) ≠ some ⟨(c1, c2), le_of_lt hc⟩ := by
                intro h; injection h with h1; exact hu1 (congrArg (fun p : LocPair B => p.1.1) h1)
              simp [hne_s, hu1, hu2, hv1, hv2]
  choose a b e hbe using hterm
  refine ⟨∑ l : Fin k, a l, ∑ l : Fin k, b l, ∑ l : Fin k, e l, fun x y => ?_⟩
  rw [signedLoc_eq_sum]
  simp_rw [hbe]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hmc : ∑ l : Fin k, (if M l = some ⟨(c1, c2), le_of_lt hc⟩ then (1 : ℤ) else 0) = (multAt c1 c2 hc M : ℤ) := by
    unfold multAt
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast; rfl
  rw [hmc]

lemma local_agree_le_five_ninths {B k : ℕ} (c1 c2 : Fin B) (hc : c1 < c2)
    (M1 M2 : LocModel B k) (hnl1 : noLoopsAt c1 c2 M1) (hnl2 : noLoopsAt c1 c2 M2)
    (hdiff : multAt c1 c2 hc M1 ≠ multAt c1 c2 hc M2) :
    9 * (Finset.univ.filter (fun q : Fin B → Fin 3 =>
      locLikeCount M1 q = locLikeCount M2 q ∧ locUnlikeCount M1 q = locUnlikeCount M2 q)).card ≤
      5 * 3 ^ B := by
  have hne12 : c1 ≠ c2 := ne_of_lt hc
  let P : (Fin B → Fin 3) → Prop := fun q =>
    locLikeCount M1 q = locLikeCount M2 q ∧ locUnlikeCount M1 q = locUnlikeCount M2 q
  have hsq : ∀ q : Fin B → Fin 3,
      ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p =>
        P (Function.update (Function.update q c1 p.1) c2 p.2))).card ≤ 5 := by
    intro q
    obtain ⟨A1, B1, E1, h1⟩ := signedLoc_update_poly c1 c2 hc M1 hnl1 q
    obtain ⟨A2, B2, E2, h2⟩ := signedLoc_update_poly c1 c2 hc M2 hnl2 q
    have hc_ne : (multAt c1 c2 hc M1 : ℤ) - (multAt c1 c2 hc M2 : ℤ) ≠ 0 := by omega
    have hge4 := ternary_square_ge_4 ((multAt c1 c2 hc M1 : ℤ) - (multAt c1 c2 hc M2 : ℤ))
      (A1 - A2) (B1 - B2) (E1 - E2) hc_ne
    have hsub : ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p =>
        ((multAt c1 c2 hc M1 : ℤ) - (multAt c1 c2 hc M2 : ℤ)) * spinZ p.1 * spinZ p.2 +
          (A1 - A2) * spinZ p.1 + (B1 - B2) * spinZ p.2 + (E1 - E2) ≠ 0)) ⊆
        (Finset.univ.filter (fun p : Fin 3 × Fin 3 =>
          ¬ P (Function.update (Function.update q c1 p.1) c2 p.2))) := by
      intro p hp
      have hnz := (Finset.mem_filter.mp hp).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ⟨hL, hU⟩ => hnz ?_⟩
      have hs : signedLoc M1 (Function.update (Function.update q c1 p.1) c2 p.2) =
          signedLoc M2 (Function.update (Function.update q c1 p.1) c2 p.2) := by
        unfold signedLoc; rw [hL, hU]
      rw [h1 p.1 p.2, h2 p.1 p.2] at hs
      linarith
    have hne_ge4 := le_trans hge4 (Finset.card_le_card hsub)
    have htot := card_filter_add_not (Finset.univ : Finset (Fin 3 × Fin 3))
      (fun p => P (Function.update (Function.update q c1 p.1) c2 p.2))
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at htot
    omega
  let Φ : (Fin B → Fin 3) × (Fin 3 × Fin 3) → (Fin B → Fin 3) × (Fin 3 × Fin 3) :=
    fun z => (Function.update (Function.update z.1 c1 z.2.1) c2 z.2.2, (z.1 c1, z.1 c2))
  have hΦ_inv : ∀ z, Φ (Φ z) = z := by
    rintro ⟨q, x, y⟩
    ext i
    · dsimp [Φ]
      by_cases hi2 : i = c2
      · subst hi2; simp
      · by_cases hi1 : i = c1
        · subst hi1; simp [hne12]
        · simp [hi1, hi2]
    · dsimp [Φ]; simp [hne12]
    · dsimp [Φ]; simp
  have hdbl : ∑ q : Fin B → Fin 3, ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
      (fun p => P (Function.update (Function.update q c1 p.1) c2 p.2))).card =
      9 * (Finset.univ.filter P).card := by
    have h1 : ∑ q : Fin B → Fin 3, ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
        (fun p => P (Function.update (Function.update q c1 p.1) c2 p.2))).card =
        ∑ z : (Fin B → Fin 3) × (Fin 3 × Fin 3), if P (Φ z).1 then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [h1]
    have hbij : ∑ z : (Fin B → Fin 3) × (Fin 3 × Fin 3), (if P (Φ z).1 then 1 else 0) =
        ∑ z : (Fin B → Fin 3) × (Fin 3 × Fin 3), (if P z.1 then 1 else 0) := by
      refine Finset.sum_bij' (fun z _ => Φ z) (fun z _ => Φ z)
        (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
        (fun z _ => hΦ_inv z) (fun z _ => hΦ_inv z) (fun z _ => rfl)
    rw [hbij, Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    split_ifs <;> norm_num
  have hle : ∑ q : Fin B → Fin 3, ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
      (fun p => P (Function.update (Function.update q c1 p.1) c2 p.2))).card ≤ 5 * 3 ^ B := by
    calc ∑ q : Fin B → Fin 3, ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
            (fun p => P (Function.update (Function.update q c1 p.1) c2 p.2))).card
        ≤ ∑ _q : Fin B → Fin 3, 5 := Finset.sum_le_sum (fun q _ => hsq q)
      _ = 5 * 3 ^ B := by simp [mul_comm]
  rw [hdbl] at hle
  exact hle

end LocalModels

section Concentration

def protects {t B k : ℕ} (f : Fin t → Fin B) (G : Fin k → Option (pairOf t)) (e : pairOf t) : Prop :=
  f e.val.1 ≠ f e.val.2 ∧
  ∀ l : Fin k, ∀ p : pairOf t, G l = some p →
    (f p.val.1 = f e.val.1 → p.val.1 = e.val.1) ∧
    (f p.val.2 = f e.val.1 → p.val.2 = e.val.1) ∧
    (f p.val.1 = f e.val.2 → p.val.1 = e.val.2) ∧
    (f p.val.2 = f e.val.2 → p.val.2 = e.val.2)

instance {t B k : ℕ} (f : Fin t → Fin B) (G : Fin k → Option (pairOf t)) (e : pairOf t) :
    Decidable (protects f G e) := by
  unfold protects; infer_instance

lemma protects_noLoops_and_mult {t B k : ℕ} (f : Fin t → Fin B)
    (G : Fin k → Option (pairOf t)) (e : pairOf t) (hp : protects f G e) :
    let c1 := min (f e.val.1) (f e.val.2)
    let c2 := max (f e.val.1) (f e.val.2)
    ∃ hc : c1 < c2, noLoopsAt c1 c2 (projModel f G) ∧
      multAt c1 c2 hc (projModel f G) = (Finset.univ.filter (fun l : Fin k => G l = some e)).card := by
  dsimp only
  have hne : f e.val.1 ≠ f e.val.2 := hp.1
  have hc : min (f e.val.1) (f e.val.2) < max (f e.val.1) (f e.val.2) := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]; exact hlt
    · rw [min_eq_right (le_of_lt hgt), max_eq_left (le_of_lt hgt)]; exact hgt
  refine ⟨hc, ?_, ?_⟩
  · intro l
    have hno : ∀ c : Fin B, (c = f e.val.1 ∨ c = f e.val.2) →
        projModel f G l ≠ some ⟨(c, c), le_rfl⟩ := by
      intro c hc_eq hml
      unfold projModel projSlot at hml
      rcases hgl : G l with _ | p
      · simp [hgl] at hml
      · rw [hgl, Option.map_some] at hml
        injection hml with hord
        have h12 : f p.val.1 = c ∧ f p.val.2 = c := by
          unfold ordPair at hord
          split_ifs at hord with hle
          · exact ⟨congrArg (fun x : LocPair B => x.val.1) hord,
                   congrArg (fun x : LocPair B => x.val.2) hord⟩
          · exact ⟨congrArg (fun x : LocPair B => x.val.2) hord,
                   congrArg (fun x : LocPair B => x.val.1) hord⟩
        have hpl := hp.2 l p hgl
        rcases hc_eq with rfl | rfl
        · have e1 := hpl.1 h12.1
          have e2 := hpl.2.1 h12.2
          exact ne_of_lt p.property (e1.trans e2.symm)
        · have e1 := hpl.2.2.1 h12.1
          have e2 := hpl.2.2.2 h12.2
          exact ne_of_lt p.property (e1.trans e2.symm)
    exact ⟨hno _ (min_choice _ _), hno _ (max_choice _ _)⟩
  · unfold multAt
    congr 1; ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hml
      unfold projModel projSlot at hml
      rcases hgl : G l with _ | p
      · simp [hgl] at hml
      · rw [hgl, Option.map_some] at hml
        injection hml with hord
        have hpl := hp.2 l p hgl
        have hset : (f p.val.1 = f e.val.1 ∧ f p.val.2 = f e.val.2) ∨
            (f p.val.1 = f e.val.2 ∧ f p.val.2 = f e.val.1) := by
          have hval : (ordPair (f p.val.1) (f p.val.2)).val = (min (f e.val.1) (f e.val.2), max (f e.val.1) (f e.val.2)) :=
            congrArg Subtype.val hord
          unfold ordPair at hval
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)] at hval
            split_ifs at hval with hle
            · left; exact ⟨congrArg Prod.fst hval, congrArg Prod.snd hval⟩
            · right; exact ⟨congrArg Prod.snd hval, congrArg Prod.fst hval⟩
          · rw [min_eq_right (le_of_lt hgt), max_eq_left (le_of_lt hgt)] at hval
            split_ifs at hval with hle
            · right; exact ⟨congrArg Prod.fst hval, congrArg Prod.snd hval⟩
            · left; exact ⟨congrArg Prod.snd hval, congrArg Prod.fst hval⟩
        rcases hset with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have e1 := hpl.1 ha
          have e2 := hpl.2.2.2 hb
          have hpe : p = e := Subtype.ext (Prod.ext e1 e2)
          rw [hpe]
        · have e1 := hpl.2.2.1 ha
          have e2 := hpl.2.1 hb
          have hlt1 : p.val.1 < p.val.2 := p.property
          have hlt2 : e.val.1 < e.val.2 := e.property
          rw [e1, e2] at hlt1
          exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
    · intro hgl
      rw [projModel, projSlot, hgl, Option.map_some]
      congr 1
      unfold ordPair
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [le_of_lt hlt, min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
      · have hnot : ¬ (f e.val.1 ≤ f e.val.2) := not_le.mpr hgt
        simp [hnot, min_eq_right (le_of_lt hgt), max_eq_left (le_of_lt hgt)]

lemma card_collide_pair {t B : ℕ} (a b : Fin t) (hab : a ≠ b) :
    (Finset.univ.filter (fun f : Fin t → Fin B => f a = f b)).card * B = B ^ t := by
  have h1 : (Finset.univ.filter (fun f : Fin t → Fin B => f a = f b)).card * B =
      ((Finset.univ.filter (fun f : Fin t → Fin B => f a = f b)) ×ˢ (Finset.univ : Finset (Fin B))).card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  rw [h1]
  have hbij : ((Finset.univ.filter (fun f : Fin t → Fin B => f a = f b)) ×ˢ (Finset.univ : Finset (Fin B))).card =
      (Finset.univ : Finset (Fin t → Fin B)).card := by
    refine Finset.card_bij' (fun z _ => Function.update z.1 b z.2)
      (fun g _ => (Function.update g b (g a), g b)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro g _
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
      simp [hab]
    · intro ⟨f, c⟩ hz
      have hf : f a = f b := (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).2
      ext i
      · by_cases hi : i = b
        · rcases hi with rfl; simp [hab, hf]
        · simp [hi]
      · simp
    · intro g _
      funext i
      by_cases hi : i = b
      · rcases hi with rfl; simp
      · simp [hi]
  rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

lemma card_not_protects_le {t B k : ℕ} (G : Fin k → Option (pairOf t)) (e : pairOf t) :
    (Finset.univ.filter (fun f : Fin t → Fin B => ¬ protects f G e)).card * B ≤ (4 * k + 1) * B ^ t := by
  let col : Fin t → Fin t → Finset (Fin t → Fin B) := fun a b =>
    if a = b then ∅ else Finset.univ.filter (fun f : Fin t → Fin B => f a = f b)
  have hcol : ∀ a b : Fin t, (col a b).card * B ≤ B ^ t := by
    intro a b
    unfold col
    by_cases hab : a = b
    · simp [hab]
    · simp only [hab, ↓reduceIte]
      exact le_of_eq (card_collide_pair a b hab)
  let slotBad : Fin k → Finset (Fin t → Fin B) := fun l =>
    (G l).elim ∅ (fun p => col p.val.1 e.val.1 ∪ col p.val.2 e.val.1 ∪ col p.val.1 e.val.2 ∪ col p.val.2 e.val.2)
  have hslot : ∀ l : Fin k, (slotBad l).card * B ≤ 4 * B ^ t := by
    intro l
    unfold slotBad
    rcases G l with _ | p
    · simp
    · simp only [Option.elim_some]
      have hu1 := Finset.card_union_le (col p.val.1 e.val.1 ∪ col p.val.2 e.val.1 ∪ col p.val.1 e.val.2) (col p.val.2 e.val.2)
      have hu2 := Finset.card_union_le (col p.val.1 e.val.1 ∪ col p.val.2 e.val.1) (col p.val.1 e.val.2)
      have hu3 := Finset.card_union_le (col p.val.1 e.val.1) (col p.val.2 e.val.1)
      have hc1 := hcol p.val.1 e.val.1
      have hc2 := hcol p.val.2 e.val.1
      have hc3 := hcol p.val.1 e.val.2
      have hc4 := hcol p.val.2 e.val.2
      have hcard : (col p.val.1 e.val.1 ∪ col p.val.2 e.val.1 ∪ col p.val.1 e.val.2 ∪ col p.val.2 e.val.2).card ≤
          (col p.val.1 e.val.1).card + (col p.val.2 e.val.1).card + (col p.val.1 e.val.2).card + (col p.val.2 e.val.2).card := by omega
      calc _ ≤ ((col p.val.1 e.val.1).card + (col p.val.2 e.val.1).card +
                (col p.val.1 e.val.2).card + (col p.val.2 e.val.2).card) * B := Nat.mul_le_mul_right B hcard
        _ = (col p.val.1 e.val.1).card * B + (col p.val.2 e.val.1).card * B +
            (col p.val.1 e.val.2).card * B + (col p.val.2 e.val.2).card * B := by ring
        _ ≤ B ^ t + B ^ t + B ^ t + B ^ t := by omega
        _ = 4 * B ^ t := by ring
  have hsub : Finset.univ.filter (fun f : Fin t → Fin B => ¬ protects f G e) ⊆
      col e.val.1 e.val.2 ∪ Finset.univ.biUnion slotBad := by
    intro f hf
    have hnp := (Finset.mem_filter.mp hf).2
    unfold protects at hnp
    push_neg at hnp
    by_cases he : f e.val.1 = f e.val.2
    · refine Finset.mem_union_left _ ?_
      simp [col, ne_of_lt e.property, he]
    · obtain ⟨l, p, hgl, hbad⟩ := hnp he
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, ?_⟩)
      simp only [slotBad, hgl, Option.elim_some, Finset.mem_union]
      by_cases h1 : f p.val.1 = f e.val.1 ∧ p.val.1 ≠ e.val.1
      · left; left; left; simp [col, h1.2, h1.1]
      · by_cases h2 : f p.val.2 = f e.val.1 ∧ p.val.2 ≠ e.val.1
        · left; left; right; simp [col, h2.2, h2.1]
        · by_cases h3 : f p.val.1 = f e.val.2 ∧ p.val.1 ≠ e.val.2
          · left; right; simp [col, h3.2, h3.1]
          · right
            have h4 : f p.val.2 = f e.val.2 ∧ p.val.2 ≠ e.val.2 := by tauto
            simp [col, h4.2, h4.1]
  have hle_card : (Finset.univ.filter (fun f : Fin t → Fin B => ¬ protects f G e)).card ≤
      (col e.val.1 e.val.2).card + ∑ l : Fin k, (slotBad l).card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  calc (Finset.univ.filter (fun f : Fin t → Fin B => ¬ protects f G e)).card * B
      ≤ ((col e.val.1 e.val.2).card + ∑ l : Fin k, (slotBad l).card) * B := Nat.mul_le_mul_right B hle_card
    _ = (col e.val.1 e.val.2).card * B + ∑ l : Fin k, (slotBad l).card * B := by
        rw [Nat.add_mul, Finset.sum_mul]
    _ ≤ B ^ t + ∑ _l : Fin k, 4 * B ^ t := Nat.add_le_add (hcol e.val.1 e.val.2) (Finset.sum_le_sum (fun l _ => hslot l))
    _ = (4 * k + 1) * B ^ t := by simp; ring

lemma two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  linarith

lemma exp_two_lt_eight : Real.exp 2 < (8 : ℝ) := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith [Real.exp_pos 1]

lemma exp_le_quad {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + x + 2 * x ^ 2 := by
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hpos : 0 < 1 - x := by linarith
  have hmul : (1 - x) * Real.exp x ≤ 1 := by
    have hinv : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]; simp
    calc (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos x))
      _ = 1 := hinv
  have hquad : 1 ≤ (1 - x) * (1 + x + 2 * x ^ 2) := by
    have : (1 - x) * (1 + x + 2 * x ^ 2) - 1 = x ^ 2 * (1 - 2 * x) := by ring
    nlinarith [sq_nonneg x]
  nlinarith

lemma card_pairOf_le (t : ℕ) : Fintype.card (pairOf t) ≤ t ^ 2 := by
  have hinj : Function.Injective (fun p : pairOf t => p.val) := Subtype.val_injective
  have h := Fintype.card_le_of_injective _ hinj
  simpa [sq] using h

lemma card_locPair_le (B : ℕ) : Fintype.card (LocPair B) ≤ B ^ 2 := by
  have hinj : Function.Injective (fun p : LocPair B => p.val) := Subtype.val_injective
  have h := Fintype.card_le_of_injective _ hinj
  simpa [sq] using h

lemma exists_good_hashes {t k s : ℕ} (ht : 2 ≤ t) (hk : 0 < k) (hs : 3 ≤ s) :
    let B := 128 * (k + 1) * s
    let H := 256 * (k + 1) * s * (1 + Nat.log 2 t)
    ∃ h : Fin H → Fin t → Fin B,
      ∀ (G : Fin k → Option (pairOf t)) (e : pairOf t),
        (Finset.univ.filter (fun r : Fin H => ¬ protects (h r) G e)).card * (8 * s) ≤ H := by
  intro B H
  have hBpos : 0 < B := by positivity
  have hHpos : 0 < H := by positivity
  have hBt_pos : (0 : ℝ) < (B ^ t : ℕ) := by positivity
  let Ω := Fin H → (Fin t → Fin B)
  have hΩcard : (Fintype.card Ω : ℝ) = ((B ^ t : ℕ) : ℝ) ^ H := by
    simp [Ω, Fintype.card_fun, Fintype.card_fin]
  let badH (z : (Fin k → Option (pairOf t)) × pairOf t) : Finset Ω :=
    Finset.univ.filter (fun h : Ω =>
      H < (Finset.univ.filter (fun r : Fin H => ¬ protects (h r) z.1 z.2)).card * (8 * s))
  have hbad_bound : ∀ z : (Fin k → Option (pairOf t)) × pairOf t,
      ((badH z).card : ℝ) ≤ (Fintype.card Ω : ℝ) * Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 t : ℕ) : ℝ))) := by
    intro ⟨G, e⟩
    let pbad : Finset (Fin t → Fin B) := Finset.univ.filter (fun f : Fin t → Fin B => ¬ protects f G e)
    have hpbad_le : (pbad.card : ℝ) * (32 * (s : ℝ)) ≤ (B ^ t : ℕ) := by
      have h1 := card_not_protects_le (B := B) G e
      have h2 : (4 * k + 1) * (32 * s) ≤ B := by
        dsimp [B]; nlinarith
      have h3 : pbad.card * (32 * s) * B ≤ B * B ^ t := by
        calc pbad.card * (32 * s) * B = (pbad.card * B) * (32 * s) := by ring
          _ ≤ ((4 * k + 1) * B ^ t) * (32 * s) := Nat.mul_le_mul_right _ h1
          _ = ((4 * k + 1) * (32 * s)) * B ^ t := by ring
          _ ≤ B * B ^ t := Nat.mul_le_mul_right _ h2
      have h4 : pbad.card * (32 * s) ≤ B ^ t := Nat.le_of_mul_le_mul_right (by linarith) hBpos
      exact_mod_cast h4
    let S : ℝ := ∑ h : Ω, (8 : ℝ) ^ ((Finset.univ.filter (fun r : Fin H => ¬ protects (h r) G e)).card)
    have hS_eq : S = (∑ f : Fin t → Fin B, if ¬ protects f G e then (8 : ℝ) else 1) ^ H := by
      have hterm : ∀ h : Ω, (8 : ℝ) ^ ((Finset.univ.filter (fun r : Fin H => ¬ protects (h r) G e)).card) =
          ∏ r : Fin H, (if ¬ protects (h r) G e then (8 : ℝ) else 1) := by
        intro h
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      simp_rw [S, hterm]
      rw [← Fintype.prod_sum (fun (_ : Fin H) (f : Fin t → Fin B) => if ¬ protects f G e then (8 : ℝ) else 1)]
      simp
    have hone_step : (∑ f : Fin t → Fin B, if ¬ protects f G e then (8 : ℝ) else 1) ≤
        ((B ^ t : ℕ) : ℝ) * Real.exp (7 / (32 * (s : ℝ))) := by
      have hsum_val : (∑ f : Fin t → Fin B, if ¬ protects f G e then (8 : ℝ) else 1) =
          ((B ^ t : ℕ) : ℝ) + 7 * (pbad.card : ℝ) := by
        have hsplit : ∀ f : Fin t → Fin B,
            (if ¬ protects f G e then (8 : ℝ) else 1) = 1 + (if ¬ protects f G e then (7 : ℝ) else 0) := by
          intro f; split_ifs <;> norm_num
        simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        push_cast; ring
      rw [hsum_val]
      have hspos : (0 : ℝ) < 32 * (s : ℝ) := by positivity
      have h7 : 7 * (pbad.card : ℝ) ≤ ((B ^ t : ℕ) : ℝ) * (7 / (32 * (s : ℝ))) := by
        rw [mul_div_assoc', le_div_iff₀ hspos]
        linarith
      have hexp := Real.add_one_le_exp (7 / (32 * (s : ℝ)))
      nlinarith
    have hS_upper : S ≤ (Fintype.card Ω : ℝ) * Real.exp (7 * (H : ℝ) / (32 * (s : ℝ))) := by
      rw [hS_eq, hΩcard]
      have hnn : 0 ≤ ∑ f : Fin t → Fin B, if ¬ protects f G e then (8 : ℝ) else 1 :=
        Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
      calc _ ≤ (((B ^ t : ℕ) : ℝ) * Real.exp (7 / (32 * (s : ℝ)))) ^ H :=
            pow_le_pow_left₀ hnn hone_step H
        _ = ((B ^ t : ℕ) : ℝ) ^ H * (Real.exp (7 / (32 * (s : ℝ)))) ^ H := mul_pow _ _ _
        _ = ((B ^ t : ℕ) : ℝ) ^ H * Real.exp (7 * (H : ℝ) / (32 * (s : ℝ))) := by
            rw [← Real.exp_nat_mul]; congr 2; ring
    have hS_lower : ((badH (G, e)).card : ℝ) * Real.exp (8 * (H : ℝ) / (32 * (s : ℝ))) ≤ S := by
      calc ((badH (G, e)).card : ℝ) * Real.exp (8 * (H : ℝ) / (32 * (s : ℝ)))
          = ∑ _h ∈ badH (G, e), Real.exp (8 * (H : ℝ) / (32 * (s : ℝ))) := by simp
        _ ≤ ∑ h ∈ badH (G, e), (8 : ℝ) ^ ((Finset.univ.filter (fun r : Fin H => ¬ protects (h r) G e)).card) := by
            refine Finset.sum_le_sum (fun h hh => ?_)
            have hgt : H < (Finset.univ.filter (fun r : Fin H => ¬ protects (h r) G e)).card * (8 * s) :=
              (Finset.mem_filter.mp hh).2
            set c := (Finset.univ.filter (fun r : Fin H => ¬ protects (h r) G e)).card
            have hc_real : 8 * (H : ℝ) / (32 * (s : ℝ)) ≤ 2 * (c : ℝ) := by
              have hspos : (0 : ℝ) < 32 * (s : ℝ) := by positivity
              rw [div_le_iff₀ hspos]
              have hgt' : (H : ℝ) < (c : ℝ) * (8 * (s : ℝ)) := by exact_mod_cast hgt
              linarith
            calc Real.exp (8 * (H : ℝ) / (32 * (s : ℝ)))
                ≤ Real.exp (2 * (c : ℝ)) := Real.exp_le_exp.mpr hc_real
              _ = Real.exp ((c : ℕ) * 2) := by congr 1; ring
              _ = (Real.exp 2) ^ c := Real.exp_nat_mul 2 c
              _ ≤ (8 : ℝ) ^ c := pow_le_pow_left₀ (le_of_lt (Real.exp_pos 2)) (le_of_lt exp_two_lt_eight) c
        _ ≤ S := Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
    have hH_ratio : (H : ℝ) / (32 * (s : ℝ)) = 8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 t : ℕ) : ℝ) := by
      have hsne : (s : ℝ) ≠ 0 := by positivity
      dsimp [H]; push_cast; field_simp; ring
    have hmul := le_trans hS_lower hS_upper
    have hexp_pos : 0 < Real.exp (8 * (H : ℝ) / (32 * (s : ℝ))) := Real.exp_pos _
    rw [← le_div_iff₀ hexp_pos] at hmul
    have hdiv : (Fintype.card Ω : ℝ) * Real.exp (7 * (H : ℝ) / (32 * (s : ℝ))) /
        Real.exp (8 * (H : ℝ) / (32 * (s : ℝ))) =
        (Fintype.card Ω : ℝ) * Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 t : ℕ) : ℝ))) := by
      rw [mul_div_assoc, ← Real.exp_sub]
      congr 2
      rw [← hH_ratio]; ring
    linarith
  have hcount : Fintype.card ((Fin k → Option (pairOf t)) × pairOf t) ≤
      2 ^ (4 * (k + 1) * (1 + Nat.log 2 t)) := by
    have hp : Fintype.card (pairOf t) ≤ t ^ 2 := card_pairOf_le t
    have hopt : Fintype.card (Option (pairOf t)) ≤ (2 * t) ^ 2 := by
      rw [Fintype.card_option]
      nlinarith
    have h2t : 2 * t ≤ 2 ^ (2 * (1 + Nat.log 2 t)) := by
      have hlt : t < 2 ^ (Nat.log 2 t + 1) := Nat.lt_pow_succ_log_self (by norm_num) t
      have h1 : 2 * t ≤ 2 * 2 ^ (1 + Nat.log 2 t) := by
        rw [add_comm 1 (Nat.log 2 t)]; omega
      have h2 : 2 * 2 ^ (1 + Nat.log 2 t) = 2 ^ (1 + Nat.log 2 t + 1) := by rw [pow_succ]; ring
      have h3 : 1 + Nat.log 2 t + 1 ≤ 2 * (1 + Nat.log 2 t) := by omega
      exact h1.trans (h2 ▸ Nat.pow_le_pow_right (by norm_num) h3)
    calc Fintype.card ((Fin k → Option (pairOf t)) × pairOf t)
        = Fintype.card (Option (pairOf t)) ^ k * Fintype.card (pairOf t) := by
            simp [Fintype.card_prod]
      _ ≤ ((2 * t) ^ 2) ^ k * ((2 * t) ^ 2) := Nat.mul_le_mul (Nat.pow_le_pow_left hopt k) (by nlinarith)
      _ = ((2 * t) ^ 2) ^ (k + 1) := by ring
      _ = (2 * t) ^ (2 * (k + 1)) := by rw [← pow_mul]
      _ ≤ (2 ^ (2 * (1 + Nat.log 2 t))) ^ (2 * (k + 1)) := Nat.pow_le_pow_left h2t _
      _ = 2 ^ (4 * (k + 1) * (1 + Nat.log 2 t)) := by rw [← pow_mul]; congr 1; ring
  have hunion_lt : ((Finset.univ.biUnion badH).card : ℝ) < (Fintype.card Ω : ℝ) := by
    have h1 : ((Finset.univ.biUnion badH).card : ℝ) ≤
        ∑ z : (Fin k → Option (pairOf t)) × pairOf t, ((badH z).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : (∑ z : (Fin k → Option (pairOf t)) × pairOf t, ((badH z).card : ℝ)) ≤
        (Fintype.card ((Fin k → Option (pairOf t)) × pairOf t) : ℝ) *
        ((Fintype.card Ω : ℝ) * Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 t : ℕ) : ℝ)))) := by
      calc _ ≤ ∑ _z : (Fin k → Option (pairOf t)) × pairOf t,
                (Fintype.card Ω : ℝ) * Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 t : ℕ) : ℝ))) :=
              Finset.sum_le_sum (fun z _ => hbad_bound z)
        _ = _ := by simp
    set Nexp := 4 * (k + 1) * (1 + Nat.log 2 t)
    have hNpos : 0 < Nexp := by positivity
    have hpow_lt : ((2 ^ Nexp : ℕ) : ℝ) < Real.exp (2 * (Nexp : ℝ)) := by
      have h2e : (2 : ℝ) < Real.exp 1 := two_lt_exp_one
      calc ((2 ^ Nexp : ℕ) : ℝ) = (2 : ℝ) ^ Nexp := by push_cast; rfl
        _ < (Real.exp 1) ^ Nexp := pow_lt_pow_left₀ h2e (by norm_num) (by omega)
        _ = Real.exp (Nexp : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
        _ ≤ Real.exp (2 * (Nexp : ℝ)) := Real.exp_le_exp.mpr (by linarith [show (0 : ℝ) ≤ Nexp by positivity])
    have hN2 : (2 * (Nexp : ℝ)) = 8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 t : ℕ) : ℝ) := by
      dsimp [Nexp]; push_cast; ring
    have hprod_lt : (Fintype.card ((Fin k → Option (pairOf t)) × pairOf t) : ℝ) *
        Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 t : ℕ) : ℝ))) < 1 := by
      have hcR : (Fintype.card ((Fin k → Option (pairOf t)) × pairOf t) : ℝ) ≤ ((2 ^ Nexp : ℕ) : ℝ) := by
        exact_mod_cast hcount
      rw [← hN2, Real.exp_neg]
      have hpos : 0 < Real.exp (2 * (Nexp : ℝ)) := Real.exp_pos _
      rw [← div_eq_mul_inv, div_lt_one hpos]
      exact lt_of_le_of_lt hcR hpow_lt
    have hΩpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by rw [hΩcard]; positivity
    calc ((Finset.univ.biUnion badH).card : ℝ)
        ≤ (Fintype.card ((Fin k → Option (pairOf t)) × pairOf t) : ℝ) *
          ((Fintype.card Ω : ℝ) * Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 t : ℕ) : ℝ)))) := le_trans h1 h2
      _ = (Fintype.card Ω : ℝ) * ((Fintype.card ((Fin k → Option (pairOf t)) × pairOf t) : ℝ) *
          Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 t : ℕ) : ℝ)))) := by ring
      _ < (Fintype.card Ω : ℝ) * 1 := mul_lt_mul_of_pos_left hprod_lt hΩpos
      _ = (Fintype.card Ω : ℝ) := mul_one _
  have hlt_nat : (Finset.univ.biUnion badH).card < (Finset.univ : Finset Ω).card := by
    rw [Finset.card_univ]; exact_mod_cast hunion_lt
  have hne_sdiff : (Finset.univ \ Finset.univ.biUnion badH).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset Ω) ⊆ Finset.univ.biUnion badH := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  rcases hne_sdiff with ⟨h, hh⟩
  refine ⟨h, fun G e => ?_⟩
  have hnot : h ∉ badH (G, e) := fun hmem =>
    (Finset.mem_sdiff.mp hh).2 (Finset.mem_biUnion.mpr ⟨(G, e), Finset.mem_univ _, hmem⟩)
  simp only [badH, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
  exact hnot

lemma exists_good_masks {B k s : ℕ} (hB : 2 ≤ B) (hk : 0 < k) (hs : 3 ≤ s) :
    let M := 600 * (k + 1) * s ^ 2 * (1 + Nat.log 2 B)
    ∃ q : Fin M → Fin B → Fin 3,
      ∀ (c1 c2 : Fin B) (hc : c1 < c2) (M1 M2 : LocModel B k),
        noLoopsAt c1 c2 M1 → noLoopsAt c1 c2 M2 →
        multAt c1 c2 hc M1 ≠ multAt c1 c2 hc M2 →
        (16 * s - 9) * M ≤
          (Finset.univ.filter (fun j : Fin M =>
            locLikeCount M1 (q j) ≠ locLikeCount M2 (q j) ∨
            locUnlikeCount M1 (q j) ≠ locUnlikeCount M2 (q j))).card * (36 * s) := by
  intro M
  have hMpos : 0 < M := by positivity
  let Ω := Fin M → (Fin B → Fin 3)
  have hΩcard : (Fintype.card Ω : ℝ) = ((3 ^ B : ℕ) : ℝ) ^ M := by
    simp [Ω, Fintype.card_fun, Fintype.card_fin]
  let Tup := (Fin B × Fin B) × LocModel B k × LocModel B k
  let goodTup (z : Tup) : Prop :=
    ∃ hc : z.1.1 < z.1.2, noLoopsAt z.1.1 z.1.2 z.2.1 ∧ noLoopsAt z.1.1 z.1.2 z.2.2 ∧
      multAt z.1.1 z.1.2 hc z.2.1 ≠ multAt z.1.1 z.1.2 hc z.2.2
  classical
  let badM (z : Tup) : Finset Ω :=
    if goodTup z then
      Finset.univ.filter (fun q : Ω =>
        (20 * s + 9) * M < (Finset.univ.filter (fun j : Fin M =>
          locLikeCount z.2.1 (q j) = locLikeCount z.2.2 (q j) ∧
          locUnlikeCount z.2.1 (q j) = locUnlikeCount z.2.2 (q j))).card * (36 * s))
    else ∅
  have hbad_bound : ∀ z : Tup,
      ((badM z).card : ℝ) ≤ (Fintype.card Ω : ℝ) * Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ))) := by
    intro z
    by_cases hz : goodTup z
    · rcases hz with ⟨hc, hnl1, hnl2, hdiff⟩
      have hbadM_eq : badM z = Finset.univ.filter (fun q : Ω =>
          (20 * s + 9) * M < (Finset.univ.filter (fun j : Fin M =>
            locLikeCount z.2.1 (q j) = locLikeCount z.2.2 (q j) ∧
            locUnlikeCount z.2.1 (q j) = locUnlikeCount z.2.2 (q j))).card * (36 * s)) := by
        simp [badM, goodTup, hc, hnl1, hnl2, hdiff]
      let lam : ℝ := 1 / (10 * (s : ℝ))
      have hlam0 : 0 ≤ lam := by positivity
      have hlam1 : lam ≤ 1 / 2 := by
        dsimp [lam]
        have : (2 : ℝ) ≤ 10 * (s : ℝ) := by exact_mod_cast (show 2 ≤ 10 * s by omega)
        exact one_div_le_one_div_of_le (by norm_num) this
      have hexp_lam : Real.exp lam ≤ 1 + lam + 2 * lam ^ 2 := exp_le_quad hlam0 hlam1
      let P : (Fin B → Fin 3) → Prop := fun f =>
        locLikeCount z.2.1 f = locLikeCount z.2.2 f ∧ locUnlikeCount z.2.1 f = locUnlikeCount z.2.2 f
      let pset : Finset (Fin B → Fin 3) := Finset.univ.filter P
      have hpset : 9 * (pset.card : ℝ) ≤ 5 * ((3 ^ B : ℕ) : ℝ) := by
        exact_mod_cast local_agree_le_five_ninths z.1.1 z.1.2 hc z.2.1 z.2.2 hnl1 hnl2 hdiff
      let T : ℝ := ∑ q : Ω, (Real.exp lam) ^ ((Finset.univ.filter (fun j : Fin M => P (q j))).card)
      have hT_eq : T = (∑ f : Fin B → Fin 3, if P f then Real.exp lam else 1) ^ M := by
        have hterm : ∀ q : Ω, (Real.exp lam) ^ ((Finset.univ.filter (fun j : Fin M => P (q j))).card) =
            ∏ j : Fin M, (if P (q j) then Real.exp lam else 1) := by
          intro q
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        simp_rw [T, hterm]
        rw [← Fintype.prod_sum (fun (_ : Fin M) (f : Fin B → Fin 3) => if P f then Real.exp lam else 1)]
        simp
      have hone_step : (∑ f : Fin B → Fin 3, if P f then Real.exp lam else 1) ≤
          ((3 ^ B : ℕ) : ℝ) * Real.exp ((5 / 9 : ℝ) * lam + (10 / 9 : ℝ) * lam ^ 2) := by
        have hsum_val : (∑ f : Fin B → Fin 3, if P f then Real.exp lam else 1) =
            ((3 ^ B : ℕ) : ℝ) + (pset.card : ℝ) * (Real.exp lam - 1) := by
          have hsplit : ∀ f : Fin B → Fin 3,
              (if P f then Real.exp lam else 1) = 1 + (if P f then Real.exp lam - 1 else 0) := by
            intro f; split_ifs <;> ring
          simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_one]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        rw [hsum_val]
        have hdiff_nn : 0 ≤ Real.exp lam - 1 := by linarith [Real.add_one_le_exp lam]
        have h1 : (pset.card : ℝ) * (Real.exp lam - 1) ≤
            ((5 / 9 : ℝ) * ((3 ^ B : ℕ) : ℝ)) * (lam + 2 * lam ^ 2) := by
          calc (pset.card : ℝ) * (Real.exp lam - 1)
              ≤ ((5 / 9 : ℝ) * ((3 ^ B : ℕ) : ℝ)) * (Real.exp lam - 1) :=
                mul_le_mul_of_nonneg_right (by linarith) hdiff_nn
            _ ≤ ((5 / 9 : ℝ) * ((3 ^ B : ℕ) : ℝ)) * (lam + 2 * lam ^ 2) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have hexp := Real.add_one_le_exp ((5 / 9 : ℝ) * lam + (10 / 9 : ℝ) * lam ^ 2)
        have h3pos : (0 : ℝ) ≤ ((3 ^ B : ℕ) : ℝ) := by positivity
        nlinarith
      have hT_upper : T ≤ (Fintype.card Ω : ℝ) * Real.exp ((M : ℝ) * ((5 / 9 : ℝ) * lam + (10 / 9 : ℝ) * lam ^ 2)) := by
        rw [hT_eq, hΩcard]
        have hnn : 0 ≤ ∑ f : Fin B → Fin 3, if P f then Real.exp lam else 1 :=
          Finset.sum_nonneg (fun _ _ => by split_ifs; exact le_of_lt (Real.exp_pos _); norm_num)
        calc _ ≤ (((3 ^ B : ℕ) : ℝ) * Real.exp ((5 / 9 : ℝ) * lam + (10 / 9 : ℝ) * lam ^ 2)) ^ M :=
              pow_le_pow_left₀ hnn hone_step M
          _ = ((3 ^ B : ℕ) : ℝ) ^ M * (Real.exp ((5 / 9 : ℝ) * lam + (10 / 9 : ℝ) * lam ^ 2)) ^ M := mul_pow _ _ _
          _ = ((3 ^ B : ℕ) : ℝ) ^ M * Real.exp ((M : ℝ) * ((5 / 9 : ℝ) * lam + (10 / 9 : ℝ) * lam ^ 2)) := by
              rw [← Real.exp_nat_mul]
      have hT_lower : ((badM z).card : ℝ) * Real.exp ((M : ℝ) * ((5 / 9 : ℝ) * lam + lam / (4 * (s : ℝ)))) ≤ T := by
        calc ((badM z).card : ℝ) * Real.exp ((M : ℝ) * ((5 / 9 : ℝ) * lam + lam / (4 * (s : ℝ))))
            = ∑ _q ∈ badM z, Real.exp ((M : ℝ) * ((5 / 9 : ℝ) * lam + lam / (4 * (s : ℝ)))) := by simp
          _ ≤ ∑ q ∈ badM z, (Real.exp lam) ^ ((Finset.univ.filter (fun j : Fin M => P (q j))).card) := by
              refine Finset.sum_le_sum (fun q hq => ?_)
              rw [hbadM_eq] at hq
              have hgt : (20 * s + 9) * M < (Finset.univ.filter (fun j : Fin M => P (q j))).card * (36 * s) :=
                (Finset.mem_filter.mp hq).2
              set c := (Finset.univ.filter (fun j : Fin M => P (q j))).card
              have hc_real : (M : ℝ) * ((5 / 9 : ℝ) * lam + lam / (4 * (s : ℝ))) ≤ (c : ℝ) * lam := by
                have hgtR : ((20 * (s : ℝ) + 9) * (M : ℝ)) < (c : ℝ) * (36 * (s : ℝ)) := by exact_mod_cast hgt
                have hlam_pos : 0 < lam := by positivity
                have hs_pos : (0 : ℝ) < (s : ℝ) := by positivity
                have hfrac : (5 / 9 : ℝ) + 1 / (4 * (s : ℝ)) = (20 * (s : ℝ) + 9) / (36 * (s : ℝ)) := by
                  field_simp; ring
                have hstep : (M : ℝ) * ((5 / 9 : ℝ) + 1 / (4 * (s : ℝ))) ≤ (c : ℝ) := by
                  rw [hfrac, mul_div_assoc', div_le_iff₀ (by positivity)]
                  linarith
                calc (M : ℝ) * ((5 / 9 : ℝ) * lam + lam / (4 * (s : ℝ)))
                    = ((M : ℝ) * ((5 / 9 : ℝ) + 1 / (4 * (s : ℝ)))) * lam := by ring
                  _ ≤ (c : ℝ) * lam := mul_le_mul_of_nonneg_right hstep (le_of_lt hlam_pos)
              rw [← Real.exp_nat_mul]
              exact Real.exp_le_exp.mpr hc_real
          _ ≤ T := Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
      have hgap : (M : ℝ) * ((5 / 9 : ℝ) * lam + (10 / 9 : ℝ) * lam ^ 2) -
          (M : ℝ) * ((5 / 9 : ℝ) * lam + lam / (4 * (s : ℝ))) ≤
          - (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ)) := by
        have hs_ne : (s : ℝ) ≠ 0 := by positivity
        have hcalc : (M : ℝ) * ((5 / 9 : ℝ) * lam + (10 / 9 : ℝ) * lam ^ 2) -
            (M : ℝ) * ((5 / 9 : ℝ) * lam + lam / (4 * (s : ℝ))) =
            - ((25 / 3 : ℝ) * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ)) := by
          dsimp [M, lam]; push_cast; field_simp; ring
        rw [hcalc]
        have hposK : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ) := by positivity
        linarith
      have hmul := le_trans hT_lower hT_upper
      have hexp_pos : 0 < Real.exp ((M : ℝ) * ((5 / 9 : ℝ) * lam + lam / (4 * (s : ℝ)))) := Real.exp_pos _
      rw [← le_div_iff₀ hexp_pos] at hmul
      calc ((badM z).card : ℝ)
          ≤ (Fintype.card Ω : ℝ) * Real.exp ((M : ℝ) * ((5 / 9 : ℝ) * lam + (10 / 9 : ℝ) * lam ^ 2)) /
            Real.exp ((M : ℝ) * ((5 / 9 : ℝ) * lam + lam / (4 * (s : ℝ)))) := hmul
        _ = (Fintype.card Ω : ℝ) * Real.exp ((M : ℝ) * ((5 / 9 : ℝ) * lam + (10 / 9 : ℝ) * lam ^ 2) -
            (M : ℝ) * ((5 / 9 : ℝ) * lam + lam / (4 * (s : ℝ)))) := by rw [mul_div_assoc, ← Real.exp_sub]
        _ ≤ (Fintype.card Ω : ℝ) * Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgap) (by positivity)
    · simp only [badM, hz, ↓reduceIte, Finset.card_empty, Nat.cast_zero]
      positivity
  have hcount : Fintype.card Tup ≤ 2 ^ (8 * (k + 1) * (1 + Nat.log 2 B)) := by
    have hlp : Fintype.card (LocPair B) ≤ B ^ 2 := card_locPair_le B
    have hopt : Fintype.card (LocSlot B) ≤ (2 * B) ^ 2 := by
      rw [Fintype.card_option]
      nlinarith
    have h2B : 2 * B ≤ 2 ^ (2 * (1 + Nat.log 2 B)) := by
      have hlt : B < 2 ^ (Nat.log 2 B + 1) := Nat.lt_pow_succ_log_self (by norm_num) B
      have h1 : 2 * B ≤ 2 * 2 ^ (1 + Nat.log 2 B) := by
        rw [add_comm 1 (Nat.log 2 B)]; omega
      have h2 : 2 * 2 ^ (1 + Nat.log 2 B) = 2 ^ (1 + Nat.log 2 B + 1) := by rw [pow_succ]; ring
      have h3 : 1 + Nat.log 2 B + 1 ≤ 2 * (1 + Nat.log 2 B) := by omega
      exact h1.trans (h2 ▸ Nat.pow_le_pow_right (by norm_num) h3)
    have hB2 : B * B ≤ (2 * B) ^ 4 := by
      calc B * B ≤ (2 * B) * (2 * B) := by nlinarith
        _ = (2 * B) ^ 2 := by ring
        _ ≤ (2 * B) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    calc Fintype.card Tup
        = B * B * (Fintype.card (LocSlot B) ^ k * Fintype.card (LocSlot B) ^ k) := by
            simp [Tup, Fintype.card_prod, Fintype.card_fun]
      _ ≤ (2 * B) ^ 4 * (((2 * B) ^ 2) ^ k * ((2 * B) ^ 2) ^ k) :=
            Nat.mul_le_mul hB2 (Nat.mul_le_mul (Nat.pow_le_pow_left hopt k) (Nat.pow_le_pow_left hopt k))
      _ = (2 * B) ^ (4 * (k + 1)) := by
            rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ (2 ^ (2 * (1 + Nat.log 2 B))) ^ (4 * (k + 1)) := Nat.pow_le_pow_left h2B _
      _ = 2 ^ (8 * (k + 1) * (1 + Nat.log 2 B)) := by rw [← pow_mul]; congr 1; ring
  have hunion_lt : ((Finset.univ.biUnion badM).card : ℝ) < (Fintype.card Ω : ℝ) := by
    have h1 : ((Finset.univ.biUnion badM).card : ℝ) ≤ ∑ z : Tup, ((badM z).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    have h2 : (∑ z : Tup, ((badM z).card : ℝ)) ≤
        (Fintype.card Tup : ℝ) * ((Fintype.card Ω : ℝ) *
          Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ)))) := by
      calc _ ≤ ∑ _z : Tup, (Fintype.card Ω : ℝ) *
                Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ))) :=
              Finset.sum_le_sum (fun z _ => hbad_bound z)
        _ = _ := by simp
    set Nexp := 8 * (k + 1) * (1 + Nat.log 2 B)
    have hNpos : 0 < Nexp := by positivity
    have hpow_lt : ((2 ^ Nexp : ℕ) : ℝ) < Real.exp (Nexp : ℝ) := by
      have h2e : (2 : ℝ) < Real.exp 1 := two_lt_exp_one
      calc ((2 ^ Nexp : ℕ) : ℝ) = (2 : ℝ) ^ Nexp := by push_cast; rfl
        _ < (Real.exp 1) ^ Nexp := pow_lt_pow_left₀ h2e (by norm_num) (by omega)
        _ = Real.exp (Nexp : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
    have hN_eq : (Nexp : ℝ) = 8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ) := by
      dsimp [Nexp]; push_cast; ring
    have hprod_lt : (Fintype.card Tup : ℝ) *
        Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ))) < 1 := by
      have hcR : (Fintype.card Tup : ℝ) ≤ ((2 ^ Nexp : ℕ) : ℝ) := by exact_mod_cast hcount
      rw [← hN_eq, Real.exp_neg]
      have hpos : 0 < Real.exp (Nexp : ℝ) := Real.exp_pos _
      rw [← div_eq_mul_inv, div_lt_one hpos]
      exact lt_of_le_of_lt hcR hpow_lt
    have hΩpos : (0 : ℝ) < (Fintype.card Ω : ℝ) := by rw [hΩcard]; positivity
    calc ((Finset.univ.biUnion badM).card : ℝ)
        ≤ (Fintype.card Tup : ℝ) * ((Fintype.card Ω : ℝ) *
          Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ)))) := le_trans h1 h2
      _ = (Fintype.card Ω : ℝ) * ((Fintype.card Tup : ℝ) *
          Real.exp (- (8 * ((k + 1 : ℕ) : ℝ) * ((1 + Nat.log 2 B : ℕ) : ℝ)))) := by ring
      _ < (Fintype.card Ω : ℝ) * 1 := mul_lt_mul_of_pos_left hprod_lt hΩpos
      _ = (Fintype.card Ω : ℝ) := mul_one _
  have hlt_nat : (Finset.univ.biUnion badM).card < (Finset.univ : Finset Ω).card := by
    rw [Finset.card_univ]; exact_mod_cast hunion_lt
  have hne_sdiff : (Finset.univ \ Finset.univ.biUnion badM).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset Ω) ⊆ Finset.univ.biUnion badM := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  rcases hne_sdiff with ⟨q, hq⟩
  refine ⟨q, fun c1 c2 hc M1 M2 hnl1 hnl2 hdiff => ?_⟩
  let z : Tup := ((c1, c2), M1, M2)
  have hnot : q ∉ badM z := fun hmem =>
    (Finset.mem_sdiff.mp hq).2 (Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ _, hmem⟩)
  have hgz : goodTup z := ⟨hc, hnl1, hnl2, hdiff⟩
  simp only [badM, hgz, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
  have htot := card_filter_add_not (Finset.univ : Finset (Fin M))
    (fun j => locLikeCount M1 (q j) = locLikeCount M2 (q j) ∧
      locUnlikeCount M1 (q j) = locUnlikeCount M2 (q j))
  simp only [Finset.card_univ, Fintype.card_fin] at htot
  have hneg_eq : (Finset.univ.filter (fun j : Fin M =>
      ¬ (locLikeCount M1 (q j) = locLikeCount M2 (q j) ∧
        locUnlikeCount M1 (q j) = locUnlikeCount M2 (q j)))).card =
      (Finset.univ.filter (fun j : Fin M =>
        locLikeCount M1 (q j) ≠ locLikeCount M2 (q j) ∨
        locUnlikeCount M1 (q j) ≠ locUnlikeCount M2 (q j))).card := by
    congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  rw [hneg_eq] at htot
  set a := (Finset.univ.filter (fun j : Fin M =>
    locLikeCount M1 (q j) = locLikeCount M2 (q j) ∧
    locUnlikeCount M1 (q j) = locUnlikeCount M2 (q j))).card
  set b := (Finset.univ.filter (fun j : Fin M =>
    locLikeCount M1 (q j) ≠ locLikeCount M2 (q j) ∨
    locUnlikeCount M1 (q j) ≠ locUnlikeCount M2 (q j))).card
  have hnot' : a * (36 * s) ≤ (20 * s + 9) * M := hnot
  have hmul_tot : a * (36 * s) + b * (36 * s) = M * (36 * s) := by
    rw [← Nat.add_mul, htot]
  have h16 : (16 * s - 9) + (20 * s + 9) = 36 * s := by omega
  have hM36 : (16 * s - 9) * M + (20 * s + 9) * M = M * (36 * s) := by
    rw [← Nat.add_mul, h16, mul_comm]
  omega

def goodLocPred {t B k : ℕ} (f : Fin t → Fin B) (e : pairOf t) (m : ℕ) (M_loc : LocModel B k) : Prop :=
  ∃ hne : f e.val.1 ≠ f e.val.2,
    let c1 := min (f e.val.1) (f e.val.2)
    let c2 := max (f e.val.1) (f e.val.2)
    ∃ hc : c1 < c2, noLoopsAt c1 c2 M_loc ∧ multAt c1 c2 hc M_loc = m

noncomputable def goodLocList {t B k : ℕ} (f : Fin t → Fin B) (e : pairOf t) (m : ℕ) : List (LocModel B k) := by
  classical
  exact (Finset.univ : Finset (LocModel B k)).toList.filter (fun M_loc => decide (goodLocPred f e m M_loc))

lemma mem_goodLocList_iff {t B k : ℕ} (f : Fin t → Fin B) (e : pairOf t) (m : ℕ) (M_loc : LocModel B k) :
    M_loc ∈ goodLocList f e m ↔ goodLocPred f e m M_loc := by
  classical
  unfold goodLocList
  simp [List.mem_filter]

def locCostOf {t B k H M : ℕ} (h : Fin H → Fin t → Fin B) (q : Fin M → Fin B → Fin 3)
    (y : Fin (H * M) → Option ℕ) (r : Fin H) (M_loc : LocModel B k) : ℕ :=
  (Finset.univ.filter (fun j : Fin M =>
    let i := finProdFinEquiv (r, j)
    (y i).isSome = true ∧
    y i ≠ some (targetMass t k (zCount (q j ∘ h r)) (locLikeCount M_loc (q j)) (locUnlikeCount M_loc (q j))))).card

def listMinCost {t B k H M : ℕ} (h : Fin H → Fin t → Fin B) (q : Fin M → Fin B → Fin 3)
    (y : Fin (H * M) → Option ℕ) (r : Fin H) (L : List (LocModel B k)) : ℕ :=
  L.foldl (fun acc M_loc => min acc (locCostOf (t := t) h q y r M_loc)) M

lemma foldl_min_le_init {α : Type} (f : α → ℕ) (init : ℕ) (L : List α) :
    L.foldl (fun acc a => min acc (f a)) init ≤ init := by
  induction L generalizing init with
  | nil => exact le_rfl
  | cons a as ih =>
    simp only [List.foldl_cons]
    exact (ih (min init (f a))).trans (min_le_left _ _)

lemma foldl_min_le_mem {α : Type} (f : α → ℕ) (init : ℕ) (L : List α) {a : α} (ha : a ∈ L) :
    L.foldl (fun acc x => min acc (f x)) init ≤ f a := by
  induction L generalizing init with
  | nil => cases ha
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with rfl | hbs
    · exact (foldl_min_le_init f (min init (f a)) bs).trans (min_le_right _ _)
    · exact ih (min init (f b)) hbs

lemma foldl_min_cases {α : Type} (f : α → ℕ) (init : ℕ) (L : List α) :
    L.foldl (fun acc a => min acc (f a)) init = init ∨
    ∃ a ∈ L, L.foldl (fun acc x => min acc (f x)) init = f a := by
  induction L generalizing init with
  | nil => left; rfl
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rcases ih (min init (f b)) with h1 | ⟨a, ha, h2⟩
    · rcases min_choice init (f b) with hm | hm
      · left; rw [h1, hm]
      · right; exact ⟨b, List.mem_cons_self, by rw [h1, hm]⟩
    · right; exact ⟨a, List.mem_cons_of_mem b ha, h2⟩

noncomputable def totalCostOf {t B k H M : ℕ} (h : Fin H → Fin t → Fin B) (q : Fin M → Fin B → Fin 3)
    (y : Fin (H * M) → Option ℕ) (e : pairOf t) (m : ℕ) : ℕ :=
  ∑ r : Fin H, listMinCost (t := t) (k := k) h q y r (goodLocList (k := k) (h r) e m)

lemma decoding_unique {t B k s H M : ℕ} (ht : 2 ≤ t) (hs : 3 ≤ s)
    (h : Fin H → Fin t → Fin B) (q : Fin M → Fin B → Fin 3)
    (hGoodH : ∀ (G : Fin k → Option (pairOf t)) (e : pairOf t),
      (Finset.univ.filter (fun r : Fin H => ¬ protects (h r) G e)).card * (8 * s) ≤ H)
    (hGoodM : ∀ (c1 c2 : Fin B) (hc : c1 < c2) (M1 M2 : LocModel B k),
      noLoopsAt c1 c2 M1 → noLoopsAt c1 c2 M2 →
      multAt c1 c2 hc M1 ≠ multAt c1 c2 hc M2 →
      (16 * s - 9) * M ≤
        (Finset.univ.filter (fun j : Fin M =>
          locLikeCount M1 (q j) ≠ locLikeCount M2 (q j) ∨
          locUnlikeCount M1 (q j) ≠ locUnlikeCount M2 (q j))).card * (36 * s))
    (G : Fin k → Option (pairOf t)) (y : Fin (H * M) → Option ℕ)
    (hnoise : 9 * s * (2 * (Finset.univ.filter (fun i : Fin (H * M) =>
        y i ≠ none ∧ y i ≠ some (readFn G (let p := finProdFinEquiv.symm i; q p.2 ∘ h p.1)))).card +
        (Finset.univ.filter (fun i : Fin (H * M) => y i = none)).card) < (4 * s - 9) * (H * M))
    (e : pairOf t) (m' : ℕ)
    (hne : m' ≠ (Finset.univ.filter (fun l : Fin k => G l = some e)).card) :
    totalCostOf (t := t) (k := k) h q y e (Finset.univ.filter (fun l : Fin k => G l = some e)).card <
      totalCostOf (t := t) (k := k) h q y e m' := by
  set mstar := (Finset.univ.filter (fun l : Fin k => G l = some e)).card
  let batch : Fin (H * M) → Fin t → Fin 3 := fun i =>
    let p := finProdFinEquiv.symm i; q p.2 ∘ h p.1
  let errR : Fin H → ℕ := fun r =>
    (Finset.univ.filter (fun j : Fin M =>
      let i := finProdFinEquiv (r, j)
      y i ≠ none ∧ y i ≠ some (readFn G (q j ∘ h r)))).card
  let lostR : Fin H → ℕ := fun r =>
    (Finset.univ.filter (fun j : Fin M => y (finProdFinEquiv (r, j)) = none)).card
  have herr_sum : ∑ r : Fin H, errR r =
      (Finset.univ.filter (fun i : Fin (H * M) => y i ≠ none ∧ y i ≠ some (readFn G (batch i)))).card := by
    have h1 : (Finset.univ.filter (fun i : Fin (H * M) => y i ≠ none ∧ y i ≠ some (readFn G (batch i)))).card =
        (Finset.univ.filter (fun p : Fin H × Fin M =>
          y (finProdFinEquiv p) ≠ none ∧ y (finProdFinEquiv p) ≠ some (readFn G (q p.2 ∘ h p.1)))).card := by
      refine Finset.card_bij' (fun i _ => finProdFinEquiv.symm i) (fun p _ => finProdFinEquiv p) ?_ ?_ ?_ ?_
      · intro i hi
        have h' := (Finset.mem_filter.mp hi).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [finProdFinEquiv.apply_symm_apply]
        exact h'
      · intro p hp
        have h' := (Finset.mem_filter.mp hp).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        dsimp only [batch]
        rw [finProdFinEquiv.symm_apply_apply]
        exact h'
      · intro i _; exact finProdFinEquiv.apply_symm_apply i
      · intro p _; exact finProdFinEquiv.symm_apply_apply p
    rw [h1, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    unfold errR
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hlost_sum : ∑ r : Fin H, lostR r =
      (Finset.univ.filter (fun i : Fin (H * M) => y i = none)).card := by
    have h1 : (Finset.univ.filter (fun i : Fin (H * M) => y i = none)).card =
        (Finset.univ.filter (fun p : Fin H × Fin M => y (finProdFinEquiv p) = none)).card := by
      refine Finset.card_bij' (fun i _ => finProdFinEquiv.symm i) (fun p _ => finProdFinEquiv p)
        (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [finProdFinEquiv.apply_symm_apply]; exact (Finset.mem_filter.mp hi).2⟩)
        (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩)
        (fun i _ => finProdFinEquiv.apply_symm_apply i)
        (fun p _ => finProdFinEquiv.symm_apply_apply p)
    rw [h1, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    unfold lostR
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  set err := (Finset.univ.filter (fun i : Fin (H * M) => y i ≠ none ∧ y i ≠ some (readFn G (batch i)))).card
  set lost := (Finset.univ.filter (fun i : Fin (H * M) => y i = none)).card
  let BadH : Finset (Fin H) := Finset.univ.filter (fun r : Fin H => ¬ protects (h r) G e)
  let GoodH : Finset (Fin H) := Finset.univ.filter (fun r : Fin H => protects (h r) G e)
  have hBadH_le : BadH.card * (8 * s) ≤ H := hGoodH G e
  have hGH_card : GoodH.card + BadH.card = H := by
    have := card_filter_add_not (Finset.univ : Finset (Fin H)) (fun r => protects (h r) G e)
    simpa [GoodH, BadH] using this
  have hupper_r : ∀ r : Fin H,
      listMinCost (t := t) (k := k) h q y r (goodLocList (k := k) (h r) e mstar) ≤
        if protects (h r) G e then errR r else M := by
    intro r
    by_cases hp : protects (h r) G e
    · simp only [hp, ↓reduceIte]
      have hmem : projModel (h r) G ∈ goodLocList (k := k) (h r) e mstar := by
        rw [mem_goodLocList_iff]
        obtain ⟨hc, hnl, hmult⟩ := protects_noLoops_and_mult (h r) G e hp
        exact ⟨hp.1, hc, hnl, hmult⟩
      have hle := foldl_min_le_mem (fun M_loc => locCostOf (t := t) h q y r M_loc) M
        (goodLocList (k := k) (h r) e mstar) hmem
      have heq : locCostOf (t := t) h q y r (projModel (h r) G) = errR r := by
        unfold locCostOf errR
        congr 1; ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hread : readFn G (q j ∘ h r) =
            targetMass t k (zCount (q j ∘ h r)) (locLikeCount (projModel (h r) G) (q j))
              (locUnlikeCount (projModel (h r) G) (q j)) := by
          rw [readFn_formula ht, proj_like_eq, proj_unlike_eq]
        rw [hread]
        cases y (finProdFinEquiv (r, j)) <;> simp
      exact hle.trans (le_of_eq heq)
    · simp only [hp, ↓reduceIte]
      exact foldl_min_le_init _ M _
  have hupper : totalCostOf (t := t) (k := k) h q y e mstar ≤ err + BadH.card * M := by
    unfold totalCostOf
    calc ∑ r : Fin H, listMinCost (t := t) (k := k) h q y r (goodLocList (k := k) (h r) e mstar)
        ≤ ∑ r : Fin H, (if protects (h r) G e then errR r else M) := Finset.sum_le_sum (fun r _ => hupper_r r)
      _ ≤ ∑ r : Fin H, (errR r + if ¬ protects (h r) G e then M else 0) :=
          Finset.sum_le_sum (fun r _ => by split_ifs <;> omega)
      _ = (∑ r : Fin H, errR r) + ∑ r : Fin H, (if ¬ protects (h r) G e then M else 0) := Finset.sum_add_distrib
      _ = err + BadH.card * M := by
          rw [herr_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have hlower_r : ∀ r ∈ GoodH,
      (16 * s - 9) * M ≤
        (listMinCost (t := t) (k := k) h q y r (goodLocList (k := k) (h r) e m') + errR r + lostR r) * (36 * s) := by
    intro r hr
    have hp : protects (h r) G e := (Finset.mem_filter.mp hr).2
    obtain ⟨hc, hnlStar, hmultStar⟩ := protects_noLoops_and_mult (h r) G e hp
    rcases foldl_min_cases (fun M_loc => locCostOf (t := t) h q y r M_loc) M
        (goodLocList (k := k) (h r) e m') with hM | ⟨M', hmem', hEq'⟩
    · unfold listMinCost
      rw [hM]
      have h1 : 16 * s - 9 ≤ 36 * s := by omega
      calc (16 * s - 9) * M ≤ (36 * s) * M := Nat.mul_le_mul_right M h1
        _ = M * (36 * s) := mul_comm _ _
        _ ≤ (M + errR r + lostR r) * (36 * s) := Nat.mul_le_mul_right _ (by omega)
    · unfold listMinCost
      rw [hEq']
      rw [mem_goodLocList_iff] at hmem'
      rcases hmem' with ⟨_, hc', hnl', hmult'⟩
      have hdiff : multAt _ _ hc (projModel (h r) G) ≠ multAt _ _ hc M' := by
        rw [hmultStar, hmult']; exact hne.symm
      have hM_sep := hGoodM _ _ hc (projModel (h r) G) M' hnlStar hnl' hdiff
      have hsub : (Finset.univ.filter (fun j : Fin M =>
          locLikeCount (projModel (h r) G) (q j) ≠ locLikeCount M' (q j) ∨
          locUnlikeCount (projModel (h r) G) (q j) ≠ locUnlikeCount M' (q j))) ⊆
          (Finset.univ.filter (fun j : Fin M =>
            let i := finProdFinEquiv (r, j)
            (y i).isSome = true ∧
            y i ≠ some (targetMass t k (zCount (q j ∘ h r)) (locLikeCount M' (q j)) (locUnlikeCount M' (q j))))) ∪
          (Finset.univ.filter (fun j : Fin M =>
            let i := finProdFinEquiv (r, j)
            y i ≠ none ∧ y i ≠ some (readFn G (q j ∘ h r)))) ∪
          (Finset.univ.filter (fun j : Fin M => y (finProdFinEquiv (r, j)) = none)) := by
        intro j hj
        have hneq := (Finset.mem_filter.mp hj).2
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hy : y (finProdFinEquiv (r, j)) with _ | v
        · right; rfl
        · by_cases hveq : v = readFn G (q j ∘ h r)
          · left; left
            refine ⟨rfl, ?_⟩
            intro hcontra
            injection hcontra with hv2
            rw [hveq, readFn_formula ht, proj_like_eq, proj_unlike_eq] at hv2
            have ⟨hL, hU⟩ := targetMass_injective hv2
            rcases hneq with h1 | h2
            · exact h1 hL
            · exact h2 hU
          · left; right
            exact ⟨by simp, by intro h; injection h with h'; exact hveq h'⟩
      have hcard_le : (Finset.univ.filter (fun j : Fin M =>
          locLikeCount (projModel (h r) G) (q j) ≠ locLikeCount M' (q j) ∨
          locUnlikeCount (projModel (h r) G) (q j) ≠ locUnlikeCount M' (q j))).card ≤
          locCostOf (t := t) h q y r M' + errR r + lostR r := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le
          ((Finset.univ.filter (fun j : Fin M =>
            let i := finProdFinEquiv (r, j)
            (y i).isSome = true ∧
            y i ≠ some (targetMass t k (zCount (q j ∘ h r)) (locLikeCount M' (q j)) (locUnlikeCount M' (q j))))) ∪
          (Finset.univ.filter (fun j : Fin M =>
            let i := finProdFinEquiv (r, j)
            y i ≠ none ∧ y i ≠ some (readFn G (q j ∘ h r)))))
          (Finset.univ.filter (fun j : Fin M => y (finProdFinEquiv (r, j)) = none))
        have h3 := Finset.card_union_le
          (Finset.univ.filter (fun j : Fin M =>
            let i := finProdFinEquiv (r, j)
            (y i).isSome = true ∧
            y i ≠ some (targetMass t k (zCount (q j ∘ h r)) (locLikeCount M' (q j)) (locUnlikeCount M' (q j)))))
          (Finset.univ.filter (fun j : Fin M =>
            let i := finProdFinEquiv (r, j)
            y i ≠ none ∧ y i ≠ some (readFn G (q j ∘ h r))))
        unfold locCostOf errR lostR
        omega
      exact hM_sep.trans (Nat.mul_le_mul_right _ hcard_le)
  have hlower : GoodH.card * ((16 * s - 9) * M) ≤
      (totalCostOf (t := t) (k := k) h q y e m' + err + lost) * (36 * s) := by
    calc GoodH.card * ((16 * s - 9) * M)
        = ∑ _r ∈ GoodH, (16 * s - 9) * M := by simp
      _ ≤ ∑ r ∈ GoodH, (listMinCost (t := t) (k := k) h q y r (goodLocList (k := k) (h r) e m') + errR r + lostR r) * (36 * s) :=
          Finset.sum_le_sum hlower_r
      _ ≤ ∑ r : Fin H, (listMinCost (t := t) (k := k) h q y r (goodLocList (k := k) (h r) e m') + errR r + lostR r) * (36 * s) :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = (∑ r : Fin H, (listMinCost (t := t) (k := k) h q y r (goodLocList (k := k) (h r) e m') + errR r + lostR r)) * (36 * s) := by
          rw [Finset.sum_mul]
      _ = (totalCostOf (t := t) (k := k) h q y e m' + err + lost) * (36 * s) := by
          unfold totalCostOf
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, herr_sum, hlost_sum]
  by_contra hge
  push_neg at hge
  have hcomb : GoodH.card * ((16 * s - 9) * M) ≤ (2 * err + lost + BadH.card * M) * (36 * s) := by
    have : totalCostOf (t := t) (k := k) h q y e m' + err + lost ≤ 2 * err + lost + BadH.card * M := by omega
    exact hlower.trans (Nat.mul_le_mul_right _ this)
  have hnoise' : (2 * err + lost) * (36 * s) < 4 * (4 * s - 9) * (H * M) := by
    calc (2 * err + lost) * (36 * s) = 4 * (9 * s * (2 * err + lost)) := by ring
      _ < 4 * ((4 * s - 9) * (H * M)) := Nat.mul_lt_mul_of_pos_left hnoise (by omega)
      _ = 4 * (4 * s - 9) * (H * M) := by ring
  have hstep1 : H * ((16 * s - 9) * M) ≤
      (2 * err + lost) * (36 * s) + BadH.card * M * (52 * s - 9) := by
    have hG_add : GoodH.card * ((16 * s - 9) * M) + BadH.card * ((16 * s - 9) * M) = H * ((16 * s - 9) * M) := by
      rw [← Nat.add_mul, hGH_card]
    have h52 : 36 * s + (16 * s - 9) = 52 * s - 9 := by omega
    have hsplit : BadH.card * M * (36 * s) + BadH.card * ((16 * s - 9) * M) = BadH.card * M * (52 * s - 9) := by
      calc BadH.card * M * (36 * s) + BadH.card * ((16 * s - 9) * M)
          = BadH.card * M * (36 * s) + BadH.card * M * (16 * s - 9) := by ring
        _ = BadH.card * M * (36 * s + (16 * s - 9)) := (Nat.mul_add _ _ _).symm
        _ = BadH.card * M * (52 * s - 9) := by rw [h52]
    have hdist : (2 * err + lost + BadH.card * M) * (36 * s) =
        (2 * err + lost) * (36 * s) + BadH.card * M * (36 * s) := Nat.add_mul _ _ _
    omega
  have hstep2 : 8 * s * (H * ((16 * s - 9) * M)) <
      8 * s * (4 * (4 * s - 9) * (H * M)) + (52 * s - 9) * (H * M) := by
    have hbad_mul : 8 * s * (BadH.card * M * (52 * s - 9)) ≤ (52 * s - 9) * (H * M) := by
      calc 8 * s * (BadH.card * M * (52 * s - 9))
          = (BadH.card * (8 * s)) * (M * (52 * s - 9)) := by ring
        _ ≤ H * (M * (52 * s - 9)) := Nat.mul_le_mul_right _ hBadH_le
        _ = (52 * s - 9) * (H * M) := by ring
    have hstrict : 8 * s * ((2 * err + lost) * (36 * s)) < 8 * s * (4 * (4 * s - 9) * (H * M)) :=
      Nat.mul_lt_mul_of_pos_left hnoise' (by omega)
    have hmul1 : 8 * s * (H * ((16 * s - 9) * M)) ≤
        8 * s * ((2 * err + lost) * (36 * s)) + 8 * s * (BadH.card * M * (52 * s - 9)) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hstep1
    omega
  have hHM_pos : 0 < H * M := by
    by_contra h0
    have : H * M = 0 := by omega
    rw [this, mul_zero] at hnoise
    omega
  have hL : 8 * s * (H * ((16 * s - 9) * M)) = (8 * s * (16 * s - 9)) * (H * M) := by ring
  have hR : 8 * s * (4 * (4 * s - 9) * (H * M)) + (52 * s - 9) * (H * M) =
      (8 * s * (4 * (4 * s - 9)) + (52 * s - 9)) * (H * M) := by ring
  rw [hL, hR] at hstep2
  have hcoef : 8 * s * (16 * s - 9) < 8 * s * (4 * (4 * s - 9)) + (52 * s - 9) :=
    Nat.lt_of_mul_lt_mul_right hstep2
  have h3 : 288 * s ≤ 128 * s * s := by nlinarith
  have h1_le : 72 * s ≤ 128 * s * s := by omega
  have h1 : 8 * s * (16 * s - 9) = 128 * s * s - 72 * s := by
    have : 9 ≤ 16 * s := by omega
    zify [this, h1_le]; ring
  have h2 : 8 * s * (4 * (4 * s - 9)) = 128 * s * s - 288 * s := by
    have : 9 ≤ 4 * s := by omega
    zify [this, h3]; ring
  omega

end Concentration

section CircuitBuilder

def LegalGate (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)

def ValidState (N : ℕ) (gs : List Gate) : Prop :=
  ReadsBack N ⟨gs, 0⟩ ∧ ∀ g ∈ gs, LegalGate g

def Extends (gs1 gs2 : List Gate) : Prop :=
  ∃ suf, gs2 = gs1 ++ suf

lemma Extends.refl (gs : List Gate) : Extends gs gs := ⟨[], by simp⟩

lemma Extends.trans {gs1 gs2 gs3 : List Gate} (h1 : Extends gs1 gs2) (h2 : Extends gs2 gs3) :
    Extends gs1 gs3 := by
  rcases h1 with ⟨s1, rfl⟩
  rcases h2 with ⟨s2, rfl⟩
  exact ⟨s1 ++ s2, by simp [List.append_assoc]⟩

lemma Extends.length_le {gs1 gs2 : List Gate} (h : Extends gs1 gs2) :
    gs1.length ≤ gs2.length := by
  rcases h with ⟨s, rfl⟩; simp

lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  unfold Circuit.wires
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp; omega

lemma wires_append (gs1 gs2 : List Gate) (x : List Bool) :
    Circuit.wires ⟨gs1 ++ gs2, 0⟩ x = Circuit.wires ⟨gs2, 0⟩ (Circuit.wires ⟨gs1, 0⟩ x) := by
  unfold Circuit.wires
  exact List.foldl_append

lemma wires_isPrefix (gs : List Gate) (x : List Bool) :
    x <+: Circuit.wires ⟨gs, 0⟩ x := by
  unfold Circuit.wires
  induction gs generalizing x with
  | nil => exact List.prefix_refl x
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact (List.prefix_append x _).trans (ih _)

lemma getD_of_prefix {l1 l2 : List Bool} (hpre : l1 <+: l2) {i : ℕ} (hi : i < l1.length) :
    l2.getD i false = l1.getD i false := by
  rcases hpre with ⟨t, rfl⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def evalW (gs : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (Circuit.wires ⟨gs, 0⟩ x).getD w false

lemma Extends.evalW_eq {N : ℕ} {gs1 gs2 : List Gate} (hext : Extends gs1 gs2)
    {x : List Bool} (hx : x.length = N) {w : ℕ} (hw : w < N + gs1.length) :
    evalW gs2 x w = evalW gs1 x w := by
  rcases hext with ⟨suf, rfl⟩
  unfold evalW
  rw [wires_append]
  refine getD_of_prefix (wires_isPrefix suf _) ?_
  rw [wires_length, hx]
  exact hw

lemma evalW_input {N : ℕ} (gs : List Gate) {x : List Bool} (hx : x.length = N)
    {w : ℕ} (hw : w < N) :
    evalW gs x w = x.getD w false := by
  unfold evalW
  exact getD_of_prefix (wires_isPrefix gs x) (by omega)

lemma pushGate_valid {N : ℕ} {gs : List Gate} (hval : ValidState N gs) (g : Gate)
    (hleg : LegalGate g) (hread : ∀ i ∈ g.inputs, i < N + gs.length) :
    ValidState N (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        unfold gateAt
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hval.1 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hget : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        unfold gateAt
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hread i hi
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hval.2 g' h1
    · rw [List.mem_singleton.mp h2]; exact hleg

lemma pushGate_evalW {N : ℕ} (gs : List Gate) (g : Gate) {x : List Bool} (hx : x.length = N) :
    evalW (gs ++ [g]) x (N + gs.length) = g.op.eval (g.inputs.map (fun i => evalW gs x i)) := by
  unfold evalW
  rw [wires_append]
  unfold Circuit.wires
  simp only [List.foldl_cons, List.foldl_nil]
  have hlen : (Circuit.wires ⟨gs, 0⟩ x).length = N + gs.length := by
    rw [wires_length, hx]
  have hget : (Circuit.wires ⟨gs, 0⟩ x ++ [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)]).getD
      (N + gs.length) false = g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false) := by
    rw [← hlen]
    simp [List.getD_eq_getElem?_getD]
  exact hget

def mkNot (N : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.not, [a]⟩], N + gs.length)

def mkAnd (N : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.and, [a, b]⟩], N + gs.length)

def mkOr (N : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.or, [a, b]⟩], N + gs.length)

lemma mkNot_spec {N : ℕ} {gs : List Gate} (hval : ValidState N gs) {a : ℕ} (ha : a < N + gs.length) :
    let res := mkNot N gs a
    ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ res.2 < N + res.1.length ∧
      ∀ x : List Bool, x.length = N → evalW res.1 x res.2 = !(evalW gs x a) := by
  refine ⟨pushGate_valid hval _ (Or.inr ⟨rfl, rfl⟩) (by simpa using ha),
    ⟨[_], rfl⟩, by simp [mkNot], by simp [mkNot], fun x hx => ?_⟩
  dsimp [mkNot]
  rw [pushGate_evalW gs _ hx]
  rfl

lemma mkAnd_spec {N : ℕ} {gs : List Gate} (hval : ValidState N gs) {a b : ℕ}
    (ha : a < N + gs.length) (hb : b < N + gs.length) :
    let res := mkAnd N gs a b
    ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ res.2 < N + res.1.length ∧
      ∀ x : List Bool, x.length = N → evalW res.1 x res.2 = (evalW gs x a && evalW gs x b) := by
  refine ⟨pushGate_valid hval _ (Or.inl ⟨Or.inl rfl, rfl⟩) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    ⟨[_], rfl⟩, by simp [mkAnd], by simp [mkAnd], fun x hx => ?_⟩
  dsimp [mkAnd]
  rw [pushGate_evalW gs _ hx]
  simp [GateOp.eval]

lemma mkOr_spec {N : ℕ} {gs : List Gate} (hval : ValidState N gs) {a b : ℕ}
    (ha : a < N + gs.length) (hb : b < N + gs.length) :
    let res := mkOr N gs a b
    ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧ res.2 < N + res.1.length ∧
      ∀ x : List Bool, x.length = N → evalW res.1 x res.2 = (evalW gs x a || evalW gs x b) := by
  refine ⟨pushGate_valid hval _ (Or.inl ⟨Or.inr rfl, rfl⟩) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    ⟨[_], rfl⟩, by simp [mkOr], by simp [mkOr], fun x hx => ?_⟩
  dsimp [mkOr]
  rw [pushGate_evalW gs _ hx]
  simp [GateOp.eval]

def mkXor (N : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let (gs1, na) := mkNot N gs a
  let (gs2, nb) := mkNot N gs1 b
  let (gs3, t1) := mkAnd N gs2 a nb
  let (gs4, t2) := mkAnd N gs3 na b
  mkOr N gs4 t1 t2

lemma mkXor_spec {N : ℕ} {gs : List Gate} (hval : ValidState N gs) {a b : ℕ}
    (ha : a < N + gs.length) (hb : b < N + gs.length) :
    let res := mkXor N gs a b
    ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 5 ∧ res.2 < N + res.1.length ∧
      ∀ x : List Bool, x.length = N → evalW res.1 x res.2 = xor (evalW gs x a) (evalW gs x b) := by
  dsimp [mkXor]
  obtain ⟨v1, e1, l1, w1, ev1⟩ := mkNot_spec hval ha
  have hb1 : b < N + (mkNot N gs a).1.length := by omega
  obtain ⟨v2, e2, l2, w2, ev2⟩ := mkNot_spec v1 hb1
  have ha2 : a < N + (mkNot N (mkNot N gs a).1 b).1.length := by omega
  obtain ⟨v3, e3, l3, w3, ev3⟩ := mkAnd_spec v2 ha2 w2
  have hna3 : (mkNot N gs a).2 < N + (mkAnd N (mkNot N (mkNot N gs a).1 b).1 a (mkNot N (mkNot N gs a).1 b).2).1.length := by omega
  have hb3 : b < N + (mkAnd N (mkNot N (mkNot N gs a).1 b).1 a (mkNot N (mkNot N gs a).1 b).2).1.length := by omega
  obtain ⟨v4, e4, l4, w4, ev4⟩ := mkAnd_spec v3 hna3 hb3
  have ht1 : (mkAnd N (mkNot N (mkNot N gs a).1 b).1 a (mkNot N (mkNot N gs a).1 b).2).2 <
      N + (mkAnd N (mkAnd N (mkNot N (mkNot N gs a).1 b).1 a (mkNot N (mkNot N gs a).1 b).2).1 (mkNot N gs a).2 b).1.length := by omega
  obtain ⟨v5, e5, l5, w5, ev5⟩ := mkOr_spec v4 ht1 w4
  refine ⟨v5, e1.trans (e2.trans (e3.trans (e4.trans e5))), by omega, w5, fun x hx => ?_⟩
  rw [ev5 x hx, e4.evalW_eq hx w3, ev4 x hx, ev3 x hx, (e2.trans e3).evalW_eq hx w1,
      (e1.trans e2).evalW_eq hx ha, (e1.trans (e2.trans e3)).evalW_eq hx hb,
      ev2 x hx, e1.evalW_eq hx hb, ev1 x hx]
  cases evalW gs x a <;> cases evalW gs x b <;> rfl

def mkMux (N : ℕ) (gs : List Gate) (sel a b : ℕ) : List Gate × ℕ :=
  let (gs1, ns) := mkNot N gs sel
  let (gs2, t1) := mkAnd N gs1 sel a
  let (gs3, t2) := mkAnd N gs2 ns b
  mkOr N gs3 t1 t2

lemma mkMux_spec {N : ℕ} {gs : List Gate} (hval : ValidState N gs) {sel a b : ℕ}
    (hs : sel < N + gs.length) (ha : a < N + gs.length) (hb : b < N + gs.length) :
    let res := mkMux N gs sel a b
    ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 4 ∧ res.2 < N + res.1.length ∧
      ∀ x : List Bool, x.length = N →
        evalW res.1 x res.2 = if evalW gs x sel then evalW gs x a else evalW gs x b := by
  dsimp [mkMux]
  obtain ⟨v1, e1, l1, w1, ev1⟩ := mkNot_spec hval hs
  set p1 := mkNot N gs sel
  obtain ⟨v2, e2, l2, w2, ev2⟩ := mkAnd_spec (a := sel) (b := a) v1 (by omega) (by omega)
  set p2 := mkAnd N p1.1 sel a
  obtain ⟨v3, e3, l3, w3, ev3⟩ := mkAnd_spec (a := p1.2) (b := b) v2 (by omega) (by omega)
  set p3 := mkAnd N p2.1 p1.2 b
  obtain ⟨v4, e4, l4, w4, ev4⟩ := mkOr_spec (a := p2.2) (b := p3.2) v3 (by omega) w3
  refine ⟨v4, e1.trans (e2.trans (e3.trans e4)), by omega, w4, fun x hx => ?_⟩
  rw [ev4 x hx, e3.evalW_eq hx w2, ev3 x hx, ev2 x hx, e2.evalW_eq hx w1,
      e1.evalW_eq hx hs, e1.evalW_eq hx ha, (e1.trans e2).evalW_eq hx hb, ev1 x hx]
  cases evalW gs x sel <;> cases evalW gs x a <;> cases evalW gs x b <;> rfl

def ValidVec (N : ℕ) (gs : List Gate) (v : List ℕ) : Prop :=
  ∀ w ∈ v, w < N + gs.length

lemma ValidVec.mono {N : ℕ} {gs1 gs2 : List Gate} (hext : Extends gs1 gs2) {v : List ℕ}
    (hv : ValidVec N gs1 v) : ValidVec N gs2 v :=
  fun w hw => lt_of_lt_of_le (hv w hw) (Nat.add_le_add_left hext.length_le N)

def vecVal (gs : List Gate) (x : List Bool) : List ℕ → ℕ
  | [] => 0
  | w :: ws => (if evalW gs x w then 1 else 0) + 2 * vecVal gs x ws

lemma Extends.vecVal_eq {N : ℕ} {gs1 gs2 : List Gate} (hext : Extends gs1 gs2)
    {x : List Bool} (hx : x.length = N) {v : List ℕ} (hv : ValidVec N gs1 v) :
    vecVal gs2 x v = vecVal gs1 x v := by
  induction v with
  | nil => rfl
  | cons w ws ih =>
    simp only [vecVal]
    rw [hext.evalW_eq hx (hv w List.mem_cons_self), ih (fun u hu => hv u (List.mem_cons_of_mem w hu))]

lemma vecVal_lt (gs : List Gate) (x : List Bool) (v : List ℕ) :
    vecVal gs x v < 2 ^ v.length := by
  induction v with
  | nil => simp [vecVal]
  | cons w ws ih =>
    simp only [vecVal, List.length_cons, pow_succ]
    split_ifs <;> omega

def constVec (b n : ℕ) : List ℕ :=
  List.ofFn (fun j : Fin b => if n.testBit j.val then 1 else 0)

lemma constVec_length (b n : ℕ) : (constVec b n).length = b := by
  simp [constVec]

lemma constVec_valid {N : ℕ} (hN : 2 ≤ N) (gs : List Gate) (b n : ℕ) :
    ValidVec N gs (constVec b n) := by
  intro w hw
  simp only [constVec, List.mem_ofFn] at hw
  rcases hw with ⟨j, rfl⟩
  split_ifs <;> omega

lemma constVec_val {N : ℕ} (hN : 2 ≤ N) (gs : List Gate) {x : List Bool} (hx : x.length = N)
    (hx0 : x.getD 0 false = false) (hx1 : x.getD 1 false = true) (b n : ℕ) (hn : n < 2 ^ b) :
    vecVal gs x (constVec b n) = n := by
  induction b generalizing n with
  | zero =>
    simp only [pow_zero] at hn
    have : n = 0 := by omega
    subst this; rfl
  | succ b ih =>
    have hcons : constVec (b + 1) n = (if n.testBit 0 then 1 else 0) :: constVec b (n / 2) := by
      unfold constVec
      rw [List.ofFn_succ]
      congr 1
      congr 1
      funext j
      simp [Nat.testBit_succ]
    rw [hcons, vecVal]
    have hn2 : n / 2 < 2 ^ b := by
      rw [pow_succ] at hn; omega
    rw [ih (n / 2) hn2]
    have h0 : evalW gs x 0 = false := by rw [evalW_input gs hx (by omega), hx0]
    have h1 : evalW gs x 1 = true := by rw [evalW_input gs hx (by omega), hx1]
    have htb : n.testBit 0 = decide (n % 2 = 1) := by
      rw [Nat.testBit_zero]
    rw [htb]
    by_cases hmod : n % 2 = 1
    · simp only [hmod, decide_true, ↓reduceIte, h1]; omega
    · simp only [hmod, decide_false, Bool.false_eq_true, ↓reduceIte, h0]; omega

def mkEqConst (N : ℕ) : List Gate → List ℕ → ℕ → List Gate × ℕ
  | gs, [], _ => (gs, 1)
  | gs, w :: ws, c =>
    let (gs1, bm) := if c % 2 = 1 then (gs, w) else mkNot N gs w
    let (gs2, rm) := mkEqConst N gs1 ws (c / 2)
    mkAnd N gs2 bm rm

lemma mkEqConst_spec {N : ℕ} (hN : 2 ≤ N) :
    ∀ (ws : List ℕ) (gs : List Gate) (c : ℕ),
      ValidState N gs → ValidVec N gs ws → c < 2 ^ ws.length →
      let res := mkEqConst N gs ws c
      ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length ≤ gs.length + 2 * ws.length ∧
      res.2 < N + res.1.length ∧
      ∀ x : List Bool, x.length = N → x.getD 1 false = true →
        evalW res.1 x res.2 = decide (vecVal gs x ws = c) := by
  intro ws
  induction ws with
  | nil =>
    intro gs c hval _ hc
    refine ⟨hval, Extends.refl gs, by simp [mkEqConst], by simp [mkEqConst]; omega, fun x hx hx1 => ?_⟩
    simp only [mkEqConst, vecVal]
    rw [evalW_input gs hx (by omega), hx1]
    simp only [List.length_nil, pow_zero] at hc
    have : c = 0 := by omega
    subst this; rfl
  | cons w ws ih =>
    intro gs c hval hws hc
    dsimp [mkEqConst]
    have hw : w < N + gs.length := hws w List.mem_cons_self
    have hws' : ValidVec N gs ws := fun u hu => hws u (List.mem_cons_of_mem w hu)
    have hc2 : c / 2 < 2 ^ ws.length := by
      simp only [List.length_cons, pow_succ] at hc; omega
    have hstep1 : let p := if c % 2 = 1 then (gs, w) else mkNot N gs w
        ValidState N p.1 ∧ Extends gs p.1 ∧ p.1.length ≤ gs.length + 1 ∧ p.2 < N + p.1.length ∧
        ∀ x : List Bool, x.length = N → evalW p.1 x p.2 = decide ((if evalW gs x w then 1 else 0) = c % 2) := by
      by_cases hmod : c % 2 = 1
      · simp only [hmod, ↓reduceIte]
        refine ⟨hval, Extends.refl gs, by omega, hw, fun x _ => ?_⟩
        cases evalW gs x w <;> simp
      · simp only [hmod, ↓reduceIte]
        obtain ⟨v1, e1, l1, w1, ev1⟩ := mkNot_spec hval hw
        refine ⟨v1, e1, by omega, w1, fun x hx => ?_⟩
        rw [ev1 x hx]
        have h0 : c % 2 = 0 := by omega
        rw [h0]
        cases evalW gs x w <;> decide
    set p1 := if c % 2 = 1 then (gs, w) else mkNot N gs w
    rcases hstep1 with ⟨v1, e1, l1, w1, ev1⟩
    obtain ⟨v2, e2, l2, w2, ev2⟩ := ih p1.1 (c / 2) v1 (hws'.mono e1) hc2
    set p2 := mkEqConst N p1.1 ws (c / 2)
    have hp1_in : p1.2 < N + p2.1.length := lt_of_lt_of_le w1 (Nat.add_le_add_left e2.length_le N)
    obtain ⟨v3, e3, l3, w3, ev3⟩ := mkAnd_spec v2 hp1_in w2
    refine ⟨v3, e1.trans (e2.trans e3), by omega, w3, fun x hx hx1 => ?_⟩
    rw [ev3 x hx, e2.evalW_eq hx w1, ev1 x hx, ev2 x hx hx1, e1.vecVal_eq hx hws']
    simp only [vecVal]
    have hdiv := Nat.div_add_mod c 2
    by_cases h1 : (if evalW gs x w then 1 else 0) = c % 2 <;>
    by_cases h2 : vecVal gs x ws = c / 2
    · simp only [h1, h2, decide_true, Bool.and_true]
      symm; exact decide_eq_true (by split_ifs at h1 ⊢ <;> omega)
    · simp only [h1, h2, decide_true, decide_false, Bool.and_false]
      symm; exact decide_eq_false (by split_ifs at h1 ⊢ <;> omega)
    · simp only [h1, h2, decide_false, decide_true, Bool.false_and]
      symm; exact decide_eq_false (by split_ifs at h1 ⊢ <;> omega)
    · simp only [h1, h2, decide_false, Bool.false_and]
      symm; exact decide_eq_false (by split_ifs at h1 ⊢ <;> omega)

def mkAddBit (N : ℕ) : List Gate → List ℕ → ℕ → List Gate × List ℕ
  | gs, [], _ => (gs, [])
  | gs, w :: ws, cin =>
    let (gs1, sbit) := mkXor N gs w cin
    let (gs2, cout) := mkAnd N gs1 w cin
    let (gs3, rest) := mkAddBit N gs2 ws cout
    (gs3, sbit :: rest)

lemma mkAddBit_spec {N : ℕ} :
    ∀ (v : List ℕ) (gs : List Gate) (cin : ℕ),
      ValidState N gs → ValidVec N gs v → cin < N + gs.length →
      let res := mkAddBit N gs v cin
      ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 6 * v.length ∧
      res.2.length = v.length ∧ ValidVec N res.1 res.2 ∧
      ∀ x : List Bool, x.length = N →
        vecVal res.1 x res.2 = (vecVal gs x v + (if evalW gs x cin then 1 else 0)) % 2 ^ v.length := by
  intro v
  induction v with
  | nil =>
    intro gs cin hval _ _
    refine ⟨hval, Extends.refl gs, by simp [mkAddBit], rfl, (fun _ hw => by cases hw), fun x _ => by simp [mkAddBit, vecVal, Nat.mod_one]⟩
  | cons w ws ih =>
    intro gs cin hval hv hcin
    dsimp [mkAddBit]
    have hw : w < N + gs.length := hv w List.mem_cons_self
    have hws : ValidVec N gs ws := fun u hu => hv u (List.mem_cons_of_mem w hu)
    obtain ⟨v1, e1, l1, w1, ev1⟩ := mkXor_spec hval hw hcin
    set p1 := mkXor N gs w cin
    obtain ⟨v2, e2, l2, w2, ev2⟩ := mkAnd_spec (a := w) (b := cin) v1 (by omega) (by omega)
    set p2 := mkAnd N p1.1 w cin
    obtain ⟨v3, e3, l3, len3, hv3, ev3⟩ := ih p2.1 p2.2 v2 (hws.mono (e1.trans e2)) w2
    set p3 := mkAddBit N p2.1 ws p2.2
    refine ⟨v3, e1.trans (e2.trans e3), by omega, by simp only [len3], ?_, fun x hx => ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hus
      · exact lt_of_lt_of_le w1 (Nat.add_le_add_left (e2.trans e3).length_le N)
      · exact hv3 u hus
    · simp only [vecVal]
      rw [(e2.trans e3).evalW_eq hx w1, ev1 x hx, ev3 x hx, (e1.trans e2).vecVal_eq hx hws,
          ev2 x hx, e1.evalW_eq hx hw, e1.evalW_eq hx hcin]
      simp only [pow_succ]
      set rest := vecVal gs x ws
      set P := 2 ^ ws.length
      have hP : 0 < P := by positivity
      have hmod0 : ∀ n : ℕ, 2 * (n % P) = (2 * n) % (P * 2) := by
        intro n; rw [mul_comm P 2, Nat.mul_mod_mul_left]
      have hmod1 : ∀ n : ℕ, 1 + 2 * (n % P) = (1 + 2 * n) % (P * 2) := by
        intro n
        have h1 : 1 + 2 * (n % P) < P * 2 := by have := Nat.mod_lt n hP; omega
        have h2 : (1 + 2 * n) % (P * 2) = (1 + 2 * (n % P)) % (P * 2) := by
          have hd := Nat.div_add_mod n P
          have : 1 + 2 * n = 1 + 2 * (n % P) + (P * 2) * (n / P) := by linarith
          rw [this, Nat.add_mul_mod_self_left]
        rw [h2, Nat.mod_eq_of_lt h1]
      cases evalW gs x w <;> cases evalW gs x cin <;> simp only [Bool.xor_false, Bool.xor_true,
        Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true,
        zero_add, add_zero]
      · exact hmod0 rest
      · rw [hmod1 rest]; congr 1; ring
      · exact hmod1 rest
      · rw [hmod0 (rest + 1)]; congr 1; ring

lemma addBit_mod_aux (ba bc bcin : Bool) (ru rv P : ℕ) (hP : 0 < P) :
    (if xor (xor ba bc) bcin then 1 else 0) +
      2 * ((ru + rv + if ((ba && bc) || (xor ba bc && bcin)) then 1 else 0) % P) =
    ((if ba then 1 else 0) + 2 * ru + ((if bc then 1 else 0) + 2 * rv) + (if bcin then 1 else 0)) % (P * 2) := by
  have hmod0 : ∀ n : ℕ, 2 * (n % P) = (2 * n) % (P * 2) := by
    intro n; rw [mul_comm P 2, Nat.mul_mod_mul_left]
  have hmod1 : ∀ n : ℕ, 1 + 2 * (n % P) = (1 + 2 * n) % (P * 2) := by
    intro n
    have h1 : 1 + 2 * (n % P) < P * 2 := by have := Nat.mod_lt n hP; omega
    have h2 : (1 + 2 * n) % (P * 2) = (1 + 2 * (n % P)) % (P * 2) := by
      have hd := Nat.div_add_mod n P
      have : 1 + 2 * n = 1 + 2 * (n % P) + (P * 2) * (n / P) := by linarith
      rw [this, Nat.add_mul_mod_self_left]
    rw [h2, Nat.mod_eq_of_lt h1]
  cases ba <;> cases bc <;> cases bcin <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.and_false, Bool.and_true,
      Bool.or_false, Bool.or_true, Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true,
      zero_add, add_zero]
  · rw [hmod0 (ru + rv)]; congr 1; ring
  · rw [hmod1 (ru + rv)]; congr 1; ring
  · rw [hmod1 (ru + rv)]; congr 1; ring
  · rw [hmod0 (ru + rv + 1)]; congr 1; ring
  · rw [hmod1 (ru + rv)]; congr 1; ring
  · rw [hmod0 (ru + rv + 1)]; congr 1; ring
  · rw [hmod0 (ru + rv + 1)]; congr 1; ring
  · rw [hmod1 (ru + rv + 1)]; congr 1; ring

def mkAddVecAux (N : ℕ) : List Gate → List ℕ → List ℕ → ℕ → List Gate × List ℕ
  | gs, [], _, _ => (gs, [])
  | gs, _, [], _ => (gs, [])
  | gs, a :: us, c :: vs, cin =>
    let (gs1, ab) := mkXor N gs a c
    let (gs2, sbit) := mkXor N gs1 ab cin
    let (gs3, t1) := mkAnd N gs2 a c
    let (gs4, t2) := mkAnd N gs3 ab cin
    let (gs5, cout) := mkOr N gs4 t1 t2
    let (gs6, rest) := mkAddVecAux N gs5 us vs cout
    (gs6, sbit :: rest)

lemma mkAddVecAux_spec {N : ℕ} :
    ∀ (u v : List ℕ) (gs : List Gate) (cin : ℕ),
      u.length = v.length → ValidState N gs → ValidVec N gs u → ValidVec N gs v → cin < N + gs.length →
      let res := mkAddVecAux N gs u v cin
      ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 13 * u.length ∧
      res.2.length = u.length ∧ ValidVec N res.1 res.2 ∧
      ∀ x : List Bool, x.length = N →
        vecVal res.1 x res.2 = (vecVal gs x u + vecVal gs x v + (if evalW gs x cin then 1 else 0)) % 2 ^ u.length := by
  intro u
  induction u with
  | nil =>
    intro v gs cin hlen hval _ _ _
    cases v with
    | nil =>
      refine ⟨hval, Extends.refl gs, by simp [mkAddVecAux], rfl, (fun _ hw => by cases hw),
        fun x _ => by simp [mkAddVecAux, vecVal, Nat.mod_one]⟩
    | cons _ _ => simp at hlen
  | cons a us ih =>
    intro v gs cin hlen hval hu hv hcin
    cases v with
    | nil => simp at hlen
    | cons c vs =>
      have hlen' : us.length = vs.length := by simpa using hlen
      dsimp [mkAddVecAux]
      have ha : a < N + gs.length := hu a List.mem_cons_self
      have hc : c < N + gs.length := hv c List.mem_cons_self
      have hus : ValidVec N gs us := fun w hw => hu w (List.mem_cons_of_mem a hw)
      have hvs : ValidVec N gs vs := fun w hw => hv w (List.mem_cons_of_mem c hw)
      obtain ⟨v1, e1, l1, w1, ev1⟩ := mkXor_spec hval ha hc
      set p1 := mkXor N gs a c
      obtain ⟨v2, e2, l2, w2, ev2⟩ := mkXor_spec (a := p1.2) (b := cin) v1 w1 (by omega)
      set p2 := mkXor N p1.1 p1.2 cin
      obtain ⟨v3, e3, l3, w3, ev3⟩ := mkAnd_spec (a := a) (b := c) v2 (by omega) (by omega)
      set p3 := mkAnd N p2.1 a c
      obtain ⟨v4, e4, l4, w4, ev4⟩ := mkAnd_spec (a := p1.2) (b := cin) v3 (by omega) (by omega)
      set p4 := mkAnd N p3.1 p1.2 cin
      obtain ⟨v5, e5, l5, w5, ev5⟩ := mkOr_spec (a := p3.2) (b := p4.2) v4 (by omega) w4
      set p5 := mkOr N p4.1 p3.2 p4.2
      have e15 : Extends gs p5.1 := e1.trans (e2.trans (e3.trans (e4.trans e5)))
      obtain ⟨v6, e6, l6, len6, hv6, ev6⟩ := ih vs p5.1 p5.2 hlen' v5 (hus.mono e15) (hvs.mono e15) w5
      set p6 := mkAddVecAux N p5.1 us vs p5.2
      refine ⟨v6, e15.trans e6, by omega, by simp only [len6], ?_, fun x hx => ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hws
        · exact lt_of_lt_of_le w2 (Nat.add_le_add_left (e3.trans (e4.trans (e5.trans e6))).length_le N)
        · exact hv6 w hws
      · simp only [vecVal]
        rw [(e3.trans (e4.trans (e5.trans e6))).evalW_eq hx w2, ev2 x hx, ev1 x hx, e1.evalW_eq hx hcin,
            ev6 x hx, e15.vecVal_eq hx hus, e15.vecVal_eq hx hvs,
            ev5 x hx, e4.evalW_eq hx w3, ev4 x hx, ev3 x hx,
            (e2.trans e3).evalW_eq hx w1, ev1 x hx,
            (e1.trans e2).evalW_eq hx ha, (e1.trans e2).evalW_eq hx hc,
            (e1.trans (e2.trans e3)).evalW_eq hx hcin]
        simp only [pow_succ]
        exact addBit_mod_aux (evalW gs x a) (evalW gs x c) (evalW gs x cin)
          (vecVal gs x us) (vecVal gs x vs) (2 ^ us.length) (by positivity)

def mkLtAux (N : ℕ) : List Gate → List ℕ → List ℕ → ℕ → List Gate × ℕ
  | gs, [], _, acc => (gs, acc)
  | gs, _, [], acc => (gs, acc)
  | gs, a :: us, c :: vs, acc =>
    let (gs1, na) := mkNot N gs a
    let (gs2, ltBit) := mkAnd N gs1 na c
    let (gs3, xac) := mkXor N gs2 a c
    let (gs4, eqBit) := mkNot N gs3 xac
    let (gs5, eqAcc) := mkAnd N gs4 eqBit acc
    let (gs6, newAcc) := mkOr N gs5 ltBit eqAcc
    mkLtAux N gs6 us vs newAcc

lemma mkLtAux_spec {N : ℕ} :
    ∀ (u v : List ℕ) (gs : List Gate) (acc : ℕ),
      u.length = v.length → ValidState N gs → ValidVec N gs u → ValidVec N gs v → acc < N + gs.length →
      let res := mkLtAux N gs u v acc
      ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 10 * u.length ∧
      res.2 < N + res.1.length ∧
      ∀ x : List Bool, x.length = N →
        evalW res.1 x res.2 =
          decide (vecVal gs x u < vecVal gs x v ∨ (vecVal gs x u = vecVal gs x v ∧ evalW gs x acc = true)) := by
  intro u
  induction u with
  | nil =>
    intro v gs acc hlen hval _ _ hacc
    cases v with
    | nil =>
      refine ⟨hval, Extends.refl gs, by simp [mkLtAux], hacc, fun x _ => ?_⟩
      simp [mkLtAux, vecVal]
    | cons _ _ => simp at hlen
  | cons a us ih =>
    intro v gs acc hlen hval hu hv hacc
    cases v with
    | nil => simp at hlen
    | cons c vs =>
      have hlen' : us.length = vs.length := by simpa using hlen
      dsimp [mkLtAux]
      have ha : a < N + gs.length := hu a List.mem_cons_self
      have hc : c < N + gs.length := hv c List.mem_cons_self
      have hus : ValidVec N gs us := fun w hw => hu w (List.mem_cons_of_mem a hw)
      have hvs : ValidVec N gs vs := fun w hw => hv w (List.mem_cons_of_mem c hw)
      obtain ⟨v1, e1, l1, w1, ev1⟩ := mkNot_spec hval ha
      set p1 := mkNot N gs a
      obtain ⟨v2, e2, l2, w2, ev2⟩ := mkAnd_spec (a := p1.2) (b := c) v1 w1 (by omega)
      set p2 := mkAnd N p1.1 p1.2 c
      obtain ⟨v3, e3, l3, w3, ev3⟩ := mkXor_spec (a := a) (b := c) v2 (by omega) (by omega)
      set p3 := mkXor N p2.1 a c
      obtain ⟨v4, e4, l4, w4, ev4⟩ := mkNot_spec v3 w3
      set p4 := mkNot N p3.1 p3.2
      obtain ⟨v5, e5, l5, w5, ev5⟩ := mkAnd_spec (a := p4.2) (b := acc) v4 w4 (by omega)
      set p5 := mkAnd N p4.1 p4.2 acc
      obtain ⟨v6, e6, l6, w6, ev6⟩ := mkOr_spec (a := p2.2) (b := p5.2) v5 (by omega) w5
      set p6 := mkOr N p5.1 p2.2 p5.2
      have e16 : Extends gs p6.1 := e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))
      obtain ⟨v7, e7, l7, w7, ev7⟩ := ih vs p6.1 p6.2 hlen' v6 (hus.mono e16) (hvs.mono e16) w6
      refine ⟨v7, e16.trans e7, by omega, w7, fun x hx => ?_⟩
      rw [ev7 x hx, e16.vecVal_eq hx hus, e16.vecVal_eq hx hvs,
          ev6 x hx, (e3.trans (e4.trans e5)).evalW_eq hx w2, ev5 x hx, ev4 x hx, ev3 x hx,
          ev2 x hx, ev1 x hx, e1.evalW_eq hx hc, (e1.trans e2).evalW_eq hx ha,
          (e1.trans e2).evalW_eq hx hc, (e1.trans (e2.trans (e3.trans e4))).evalW_eq hx hacc]
      simp only [vecVal]
      have haux : ∀ (ba bc bacc : Bool) (ru rv : ℕ),
          decide (ru < rv ∨ ru = rv ∧ ((!(ba) && bc) || (!(xor ba bc) && bacc)) = true) =
          decide ((if ba then 1 else 0) + 2 * ru < (if bc then 1 else 0) + 2 * rv ∨
            (if ba then 1 else 0) + 2 * ru = (if bc then 1 else 0) + 2 * rv ∧ bacc = true) := by
        intro ba bc bacc ru rv
        cases ba <;> cases bc <;> cases bacc <;>
          (by_cases hlt : ru < rv <;> by_cases heq : ru = rv <;> simp [hlt, heq] <;> omega)
      exact haux (evalW gs x a) (evalW gs x c) (evalW gs x acc) (vecVal gs x us) (vecVal gs x vs)

def mkLtVec (N : ℕ) (gs : List Gate) (u v : List ℕ) : List Gate × ℕ :=
  mkLtAux N gs u v 0

lemma mkLtVec_spec {N : ℕ} (hN : 2 ≤ N) {gs : List Gate} {u v : List ℕ}
    (hlen : u.length = v.length) (hval : ValidState N gs) (hu : ValidVec N gs u) (hv : ValidVec N gs v) :
    let res := mkLtVec N gs u v
    ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 10 * u.length ∧
    res.2 < N + res.1.length ∧
    ∀ x : List Bool, x.length = N → x.getD 0 false = false →
      evalW res.1 x res.2 = decide (vecVal gs x u < vecVal gs x v) := by
  dsimp [mkLtVec]
  obtain ⟨v1, e1, l1, w1, ev1⟩ := mkLtAux_spec u v gs 0 hlen hval hu hv (by omega)
  refine ⟨v1, e1, l1, w1, fun x hx hx0 => ?_⟩
  rw [ev1 x hx, evalW_input gs hx (by omega), hx0]
  simp

def mkMuxVec (N : ℕ) (sel : ℕ) : List Gate → List ℕ → List ℕ → List Gate × List ℕ
  | gs, [], _ => (gs, [])
  | gs, _, [] => (gs, [])
  | gs, a :: us, c :: vs =>
    let (gs1, w) := mkMux N gs sel a c
    let (gs2, rest) := mkMuxVec N sel gs1 us vs
    (gs2, w :: rest)

lemma mkMuxVec_spec {N : ℕ} (sel : ℕ) :
    ∀ (u v : List ℕ) (gs : List Gate),
      u.length = v.length → ValidState N gs → sel < N + gs.length → ValidVec N gs u → ValidVec N gs v →
      let res := mkMuxVec N sel gs u v
      ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 4 * u.length ∧
      res.2.length = u.length ∧ ValidVec N res.1 res.2 ∧
      ∀ x : List Bool, x.length = N →
        vecVal res.1 x res.2 = if evalW gs x sel then vecVal gs x u else vecVal gs x v := by
  intro u
  induction u with
  | nil =>
    intro v gs hlen hval _ _ _
    cases v with
    | nil => refine ⟨hval, Extends.refl gs, by simp [mkMuxVec], rfl, (fun _ hw => by cases hw), fun x _ => by simp [mkMuxVec, vecVal]⟩
    | cons _ _ => simp at hlen
  | cons a us ih =>
    intro v gs hlen hval hsel hu hv
    cases v with
    | nil => simp at hlen
    | cons c vs =>
      have hlen' : us.length = vs.length := by simpa using hlen
      dsimp [mkMuxVec]
      have ha : a < N + gs.length := hu a List.mem_cons_self
      have hc : c < N + gs.length := hv c List.mem_cons_self
      have hus : ValidVec N gs us := fun w hw => hu w (List.mem_cons_of_mem a hw)
      have hvs : ValidVec N gs vs := fun w hw => hv w (List.mem_cons_of_mem c hw)
      obtain ⟨v1, e1, l1, w1, ev1⟩ := mkMux_spec hval hsel ha hc
      set p1 := mkMux N gs sel a c
      obtain ⟨v2, e2, l2, len2, hv2, ev2⟩ := ih vs p1.1 hlen' v1 (by omega) (hus.mono e1) (hvs.mono e1)
      set p2 := mkMuxVec N sel p1.1 us vs
      refine ⟨v2, e1.trans e2, by omega, by simp only [len2], ?_, fun x hx => ?_⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hws
        · exact lt_of_lt_of_le w1 (Nat.add_le_add_left e2.length_le N)
        · exact hv2 w hws
      · simp only [vecVal]
        rw [e2.evalW_eq hx w1, ev1 x hx, ev2 x hx, e1.evalW_eq hx hsel,
            e1.vecVal_eq hx hus, e1.vecVal_eq hx hvs]
        cases evalW gs x sel <;> simp

def mkMinVec (N : ℕ) (gs : List Gate) (u v : List ℕ) : List Gate × List ℕ :=
  let (gs1, lt) := mkLtVec N gs u v
  mkMuxVec N lt gs1 u v

lemma mkMinVec_spec {N : ℕ} (hN : 2 ≤ N) {gs : List Gate} {u v : List ℕ}
    (hlen : u.length = v.length) (hval : ValidState N gs) (hu : ValidVec N gs u) (hv : ValidVec N gs v) :
    let res := mkMinVec N gs u v
    ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 14 * u.length ∧
    res.2.length = u.length ∧ ValidVec N res.1 res.2 ∧
    ∀ x : List Bool, x.length = N → x.getD 0 false = false →
      vecVal res.1 x res.2 = min (vecVal gs x u) (vecVal gs x v) := by
  dsimp [mkMinVec]
  obtain ⟨v1, e1, l1, w1, ev1⟩ := mkLtVec_spec hN hlen hval hu hv
  set p1 := mkLtVec N gs u v
  obtain ⟨v2, e2, l2, len2, hv2, ev2⟩ := mkMuxVec_spec p1.2 u v p1.1 hlen v1 w1 (hu.mono e1) (hv.mono e1)
  refine ⟨v2, e1.trans e2, by omega, len2, hv2, fun x hx hx0 => ?_⟩
  rw [ev2 x hx, ev1 x hx hx0, e1.vecVal_eq hx hu, e1.vecVal_eq hx hv]
  by_cases hlt : vecVal gs x u < vecVal gs x v
  · simp [hlt, min_eq_left (le_of_lt hlt)]
  · simp [hlt, min_eq_right (le_of_not_gt hlt)]

def buildForList {α β : Type} [DecidableEq α]
    (step : List Gate → α → List Gate × β) (default : β) :
    List Gate → List α → List Gate × (α → β)
  | gs, [] => (gs, fun _ => default)
  | gs, a :: as =>
    let (gs1, v) := step gs a
    let (gs2, f) := buildForList step default gs1 as
    (gs2, fun x => if x = a then v else f x)

lemma buildForList_spec {N : ℕ} {α β : Type} [DecidableEq α]
    (step : List Gate → α → List Gate × β) (default : β) (G : ℕ) (gs0 : List Gate)
    (P : List Gate → α → β → Prop)
    (hmono : ∀ gs1 gs2 a b, Extends gs1 gs2 → P gs1 a b → P gs2 a b)
    (hstep : ∀ gs a, ValidState N gs → Extends gs0 gs →
      ValidState N (step gs a).1 ∧ Extends gs (step gs a).1 ∧
      (step gs a).1.length ≤ gs.length + G ∧ P (step gs a).1 a (step gs a).2) :
    ∀ (L : List α) (gs : List Gate), L.Nodup → ValidState N gs → Extends gs0 gs →
      let res := buildForList step default gs L
      ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length ≤ gs.length + L.length * G ∧
      ∀ a ∈ L, P res.1 a (res.2 a) := by
  intro L
  induction L with
  | nil =>
    intro gs _ hval _
    exact ⟨hval, Extends.refl gs, by simp [buildForList], fun _ h => by cases h⟩
  | cons a as ih =>
    intro gs hnodup hval hext0
    rw [List.nodup_cons] at hnodup
    dsimp [buildForList]
    obtain ⟨v1, e1, l1, hp1⟩ := hstep gs a hval hext0
    obtain ⟨v2, e2, l2, hp2⟩ := ih (step gs a).1 hnodup.2 v1 (hext0.trans e1)
    refine ⟨v2, e1.trans e2, ?_, fun x hx => ?_⟩
    · have : (as.length + 1) * G = as.length * G + G := by ring
      omega
    · rcases List.mem_cons.mp hx with rfl | hxs
      · simp only [↓reduceIte]
        exact hmono _ _ _ _ e2 hp1
      · have hne : x ≠ a := fun h => hnodup.1 (h ▸ hxs)
        simp only [hne, ↓reduceIte]
        exact hp2 x hxs

def foldCState {α β : Type} (step : List Gate → β → α → List Gate × β) :
    List Gate → β → List α → List Gate × β
  | gs, acc, [] => (gs, acc)
  | gs, acc, a :: as =>
    let (gs1, acc1) := step gs acc a
    foldCState step gs1 acc1 as

lemma foldCState_spec {N : ℕ} {α β : Type}
    (step : List Gate → β → α → List Gate × β) (G : ℕ)
    (Inv : List Gate → β → List α → Prop)
    (hstep : ∀ gs acc a as, ValidState N gs → Inv gs acc (a :: as) →
      ValidState N (step gs acc a).1 ∧ Extends gs (step gs acc a).1 ∧
      (step gs acc a).1.length ≤ gs.length + G ∧ Inv (step gs acc a).1 (step gs acc a).2 as) :
    ∀ (L : List α) (gs : List Gate) (acc : β),
      ValidState N gs → Inv gs acc L →
      let res := foldCState step gs acc L
      ValidState N res.1 ∧ Extends gs res.1 ∧ res.1.length ≤ gs.length + L.length * G ∧
      Inv res.1 res.2 [] := by
  intro L
  induction L with
  | nil =>
    intro gs acc hval hinv
    exact ⟨hval, Extends.refl gs, by dsimp [foldCState]; omega, hinv⟩
  | cons a as ih =>
    intro gs acc hval hinv
    dsimp [foldCState]
    obtain ⟨v1, e1, l1, hinv1⟩ := hstep gs acc a as hval hinv
    obtain ⟨v2, e2, l2, hinv2⟩ := ih (step gs acc a).1 (step gs acc a).2 v1 hinv1
    refine ⟨v2, e1.trans e2, ?_, hinv2⟩
    have : (as.length + 1) * G = as.length * G + G := by ring
    omega

lemma list_flatten_length_eq {α : Type} (L : List (List α)) (m : ℕ) (h : ∀ l ∈ L, l.length = m) :
    L.flatten.length = L.length * m := by
  induction L with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h a List.mem_cons_self, ih (fun l hl => h l (List.mem_cons_of_mem a hl))]
    ring

lemma list_flatten_getD_eq {L : List (List Bool)} {m : ℕ} (h : ∀ l ∈ L, l.length = m) :
    ∀ {i r : ℕ}, i < L.length → r < m →
      L.flatten.getD (i * m + r) false = (L.getD i []).getD r false := by
  induction L with
  | nil => intro i _ hi; simp at hi
  | cons a as ih =>
    intro i r hi hr
    have ha : a.length = m := h a List.mem_cons_self
    have has : ∀ l ∈ as, l.length = m := fun l hl => h l (List.mem_cons_of_mem a hl)
    cases i with
    | zero =>
      simp only [zero_mul, zero_add, List.flatten_cons, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, Option.getD_some]
      rw [List.getElem?_append_left (by omega)]
    | succ i' =>
      simp only [List.flatten_cons, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
      have hidx : (i' + 1) * m + r = a.length + (i' * m + r) := by rw [ha]; ring
      rw [hidx, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      have hi' : i' < as.length := by simp at hi; omega
      have hih := ih has hi' hr
      simp only [List.getD_eq_getElem?_getD] at hih
      exact hih

def bitsOf {d W : ℕ} (y : Fin d → Option ℕ) : List Bool :=
  (List.ofFn (fun i : Fin d => (y i).isSome ::
    List.ofFn (fun j : Fin W => ((y i).getD 0).testBit j.val))).flatten

lemma bitsOf_length {d W : ℕ} (y : Fin d → Option ℕ) :
    (bitsOf (W := W) y).length = d * (W + 1) := by
  unfold bitsOf
  rw [list_flatten_length_eq _ (W + 1)]
  · simp
  · intro l hl
    simp only [List.mem_ofFn] at hl
    rcases hl with ⟨i, rfl⟩
    simp

lemma input_isSome_getD {d W : ℕ} (y : Fin d → Option ℕ) (i : Fin d) :
    ([false, true] ++ bitsOf (W := W) y).getD (2 + i.val * (W + 1)) false = (y i).isSome := by
  have h1 : ([false, true] ++ bitsOf (W := W) y).getD (2 + i.val * (W + 1)) false =
      (bitsOf (W := W) y).getD (i.val * (W + 1) + 0) false := by
    have hidx : 2 + i.val * (W + 1) = ([false, true] : List Bool).length + (i.val * (W + 1) + 0) := by
      simp
    rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    rfl
  rw [h1]
  unfold bitsOf
  rw [list_flatten_getD_eq (m := W + 1)]
  · simp [List.getD_eq_getElem?_getD]
  · intro l hl
    simp only [List.mem_ofFn] at hl
    rcases hl with ⟨j, rfl⟩; simp
  · simp
  · omega

lemma input_bit_getD {d W : ℕ} (y : Fin d → Option ℕ) (i : Fin d) (j : Fin W) :
    ([false, true] ++ bitsOf (W := W) y).getD (2 + i.val * (W + 1) + 1 + j.val) false =
      ((y i).getD 0).testBit j.val := by
  have h1 : ([false, true] ++ bitsOf (W := W) y).getD (2 + i.val * (W + 1) + 1 + j.val) false =
      (bitsOf (W := W) y).getD (i.val * (W + 1) + (j.val + 1)) false := by
    have hidx : 2 + i.val * (W + 1) + 1 + j.val = ([false, true] : List Bool).length + (i.val * (W + 1) + (j.val + 1)) := by
      simp; omega
    rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    rfl
  rw [h1]
  unfold bitsOf
  rw [list_flatten_getD_eq (m := W + 1)]
  · simp [List.getD_eq_getElem?_getD]
  · intro l hl
    simp only [List.mem_ofFn] at hl
    rcases hl with ⟨idx, rfl⟩; simp
  · simp
  · omega

def dataWires {d W : ℕ} (i : Fin d) : List ℕ :=
  List.ofFn (fun j : Fin W => 2 + i.val * (W + 1) + 1 + j.val)

lemma dataWires_length {d W : ℕ} (i : Fin d) : (dataWires (W := W) i).length = W := by
  simp [dataWires]

lemma dataWires_valid {d W : ℕ} (gs : List Gate) (i : Fin d) :
    ValidVec (2 + d * (W + 1)) gs (dataWires (W := W) i) := by
  intro w hw
  simp only [dataWires, List.mem_ofFn] at hw
  rcases hw with ⟨j, rfl⟩
  have hi : i.val + 1 ≤ d := i.isLt
  have hmul : (i.val + 1) * (W + 1) ≤ d * (W + 1) := Nat.mul_le_mul_right (W + 1) hi
  have hj : j.val < W := j.isLt
  nlinarith

lemma vecVal_testBit_gen :
    ∀ (W : ℕ) (gs : List Gate) (x : List Bool) (N : ℕ) (base v : ℕ),
      x.length = N → base + W ≤ N →
      (∀ j : Fin W, x.getD (base + j.val) false = v.testBit j.val) →
      vecVal gs x (List.ofFn (fun j : Fin W => base + j.val)) = v % 2 ^ W := by
  intro W
  induction W with
  | zero =>
    intro gs x N base v _ _ _
    simp [vecVal, Nat.mod_one]
  | succ W ih =>
    intro gs x N base v hx hle hget
    rw [List.ofFn_succ, vecVal]
    have h0 : evalW gs x (base + (0 : Fin (W + 1)).val) = v.testBit 0 := by
      rw [evalW_input gs hx (by simp; omega)]
      exact hget ⟨0, by omega⟩
    have hrest : List.ofFn (fun j : Fin W => base + j.succ.val) =
        List.ofFn (fun j : Fin W => (base + 1) + j.val) := by
      congr 1; funext j; simp; omega
    rw [hrest]
    have ih' := ih gs x N (base + 1) (v / 2) hx (by omega) (fun j => by
      have h := hget j.succ
      have heq : base + 1 + j.val = base + j.succ.val := by simp; omega
      rw [heq, h, Fin.val_succ, Nat.testBit_succ])
    rw [ih', h0, Nat.testBit_zero]
    rw [pow_succ]
    have hmod : v % (2 ^ W * 2) = v % 2 + 2 * ((v / 2) % 2 ^ W) := by
      have h1 := Nat.div_add_mod v 2
      have h2 := Nat.div_add_mod (v / 2) (2 ^ W)
      have hlt : v % 2 + 2 * ((v / 2) % 2 ^ W) < 2 ^ W * 2 := by
        have := Nat.mod_lt (v / 2) (show 0 < 2 ^ W by positivity); omega
      have heq : v = (v % 2 + 2 * ((v / 2) % 2 ^ W)) + (2 ^ W * 2) * ((v / 2) / 2 ^ W) := by linarith
      conv_lhs => rw [heq]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    by_cases hodd : v % 2 = 1
    · simp only [hodd, decide_true, ↓reduceIte]; omega
    · simp only [hodd, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

lemma dataWires_val {d W : ℕ} (gs : List Gate) (y : Fin d → Option ℕ) (i : Fin d) :
    vecVal gs ([false, true] ++ bitsOf (W := W) y) (dataWires (W := W) i) = ((y i).getD 0) % 2 ^ W := by
  unfold dataWires
  have hx : ([false, true] ++ bitsOf (W := W) y).length = 2 + d * (W + 1) := by
    simp [bitsOf_length]; omega
  have hbase : 2 + i.val * (W + 1) + 1 + W ≤ 2 + d * (W + 1) := by
    have hi : i.val + 1 ≤ d := i.isLt
    have hmul : (i.val + 1) * (W + 1) ≤ d * (W + 1) := Nat.mul_le_mul_right (W + 1) hi
    nlinarith
  exact vecVal_testBit_gen W gs _ (2 + d * (W + 1)) (2 + i.val * (W + 1) + 1) ((y i).getD 0) hx hbase
    (fun j => input_bit_getD y i j)

lemma option_match_eq (o : Option ℕ) (W c : ℕ) :
    (o.isSome && decide (o.getD 0 % 2 ^ W = c)) = decide (o.map (fun v => v % 2 ^ W) = some c) := by
  cases o <;> simp

lemma option_disagree_eq (o : Option ℕ) (W c : ℕ) :
    (if (o.isSome && !decide (o.map (fun v => v % 2 ^ W) = some c)) = true then 1 else 0) =
    if (o.map (fun v => v % 2 ^ W)).isSome = true ∧ o.map (fun v => v % 2 ^ W) ≠ some c then 1 else 0 := by
  cases o <;> simp

noncomputable def buildDecoder {t B k H M : ℕ} (h : Fin H → Fin t → Fin B) (q : Fin M → Fin B → Fin 3) :
    let d := H * M
    let W := k * (2 * t + 2) + 1
    let N := 2 + d * (W + 1)
    let b := Nat.log 2 d + 2
    List Gate × (pairOf t → Fin (k + 1) → ℕ) := by
  classical
  let d := H * M
  let W := k * (2 * t + 2) + 1
  let N := 2 + d * (W + 1)
  let b := Nat.log 2 d + 2
  let batch : Fin d → Fin t → Fin 3 := fun i => let p := finProdFinEquiv.symm i; q p.2 ∘ h p.1
  let L1 : List (Fin d × Fin (k + 1) × Fin (k + 1)) := Finset.univ.toList
  let step1 : List Gate → (Fin d × Fin (k + 1) × Fin (k + 1)) → List Gate × ℕ :=
    fun gs ⟨i, L, U⟩ =>
      let (gs1, eqW) := mkEqConst N gs (dataWires (W := W) i) (targetMass t k (zCount (batch i)) L.val U.val)
      mkAnd N gs1 (2 + i.val * (W + 1)) eqW
  let (gs1, eqTab) := buildForList step1 0 [] L1
  let L2 : List (Fin H × LocModel B k) := Finset.univ.toList
  let step2 : List Gate → (Fin H × LocModel B k) → List Gate × List ℕ :=
    fun gs ⟨r, M_loc⟩ =>
      foldCState (fun g acc (j : Fin M) =>
        let i := finProdFinEquiv (r, j)
        let L : Fin (k + 1) := ⟨locLikeCount M_loc (q j), Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))⟩
        let U : Fin (k + 1) := ⟨locUnlikeCount M_loc (q j), Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))⟩
        let (g1, neqW) := mkNot N g (eqTab (i, L, U))
        let (g2, disW) := mkAnd N g1 (2 + i.val * (W + 1)) neqW
        mkAddBit N g2 acc disW) gs (constVec b 0) (List.finRange M)
  let (gs2, costTab) := buildForList step2 (constVec b 0) gs1 L2
  let L3 : List (pairOf t × Fin H × Fin (k + 1)) := Finset.univ.toList
  let step3 : List Gate → (pairOf t × Fin H × Fin (k + 1)) → List Gate × List ℕ :=
    fun gs ⟨e, r, m⟩ =>
      foldCState (fun g acc M_loc => mkMinVec N g acc (costTab (r, M_loc)))
        gs (constVec b M) (goodLocList (h r) e m.val)
  let (gs3, minTab) := buildForList step3 (constVec b 0) gs2 L3
  let L4 : List (pairOf t × Fin (k + 1)) := Finset.univ.toList
  let step4 : List Gate → (pairOf t × Fin (k + 1)) → List Gate × List ℕ :=
    fun gs ⟨e, m⟩ =>
      foldCState (fun g acc (r : Fin H) => mkAddVecAux N g acc (minTab (e, r, m)) 0)
        gs (constVec b 0) (List.finRange H)
  let (gs4, totTab) := buildForList step4 (constVec b 0) gs3 L4
  let step5 : List Gate → (pairOf t × Fin (k + 1)) → List Gate × ℕ :=
    fun gs ⟨e, m⟩ =>
      foldCState (fun g acc (m' : Fin (k + 1)) =>
        if m' = m then (g, acc) else
          let (g1, ltW) := mkLtVec N g (totTab (e, m)) (totTab (e, m'))
          mkAnd N g1 acc ltW) gs 1 (List.finRange (k + 1))
  let (gs5, outTab) := buildForList step5 0 gs4 L4
  exact (gs5, fun e m => outTab (e, m))

lemma buildDecoder_spec {t B k H M : ℕ} (ht : 2 ≤ t) (hH : 0 < H) (hM : 0 < M)
    (h : Fin H → Fin t → Fin B) (q : Fin M → Fin B → Fin 3) :
    let d := H * M
    let W := k * (2 * t + 2) + 1
    let N := 2 + d * (W + 1)
    let b := Nat.log 2 d + 2
    let res := buildDecoder h q
    ValidState N res.1 ∧
    res.1.length ≤
      d * (k + 1) ^ 2 * (2 * W + 1) +
      d * Fintype.card (LocModel B k) * (6 * b + 2) +
      Fintype.card (pairOf t) * H * (k + 1) * Fintype.card (LocModel B k) * (14 * b) +
      Fintype.card (pairOf t) * (k + 1) * H * (13 * b) +
      Fintype.card (pairOf t) * (k + 1) ^ 2 * (10 * b + 1) ∧
    (∀ e m, res.2 e m < N + res.1.length) ∧
    ∀ (y : Fin d → Option ℕ) (e : pairOf t) (m : Fin (k + 1)),
      let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
      evalW res.1 ([false, true] ++ bitsOf (W := W) y) (res.2 e m) =
        decide (∀ m' : Fin (k + 1), m' ≠ m →
          totalCostOf (t := t) (k := k) h q yT e m.val < totalCostOf (t := t) (k := k) h q yT e m'.val) := by
  classical
  dsimp only [buildDecoder]
  set d := H * M
  set W := k * (2 * t + 2) + 1
  set N := 2 + d * (W + 1)
  set b := Nat.log 2 d + 2
  have hd_pos : 0 < d := Nat.mul_pos hH hM
  have hN2 : 2 ≤ N := by omega
  have hd_lt_2b : d < 2 ^ b := by
    have h1 : d < 2 ^ (Nat.log 2 d + 1) := Nat.lt_pow_succ_log_self (by norm_num) d
    have h2 : 2 ^ (Nat.log 2 d + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h2d_lt_2b : 2 * d < 2 ^ b := by
    have h1 : d < 2 ^ (Nat.log 2 d + 1) := Nat.lt_pow_succ_log_self (by norm_num) d
    have h2 : 2 * 2 ^ (Nat.log 2 d + 1) = 2 ^ b := by
      have : b = (Nat.log 2 d + 1) + 1 := by omega
      rw [this, pow_succ]; ring
    omega
  have hM_le_d : M ≤ d := by
    calc M = 1 * M := (one_mul M).symm
      _ ≤ H * M := Nat.mul_le_mul_right M hH
  have hx_len : ∀ y : Fin d → Option ℕ, ([false, true] ++ bitsOf (W := W) y).length = N := by
    intro y; simp [N, bitsOf_length]; omega
  have hx0 : ∀ y : Fin d → Option ℕ, ([false, true] ++ bitsOf (W := W) y).getD 0 false = false := fun _ => rfl
  have hx1 : ∀ y : Fin d → Option ℕ, ([false, true] ++ bitsOf (W := W) y).getD 1 false = true := fun _ => rfl
  let batch : Fin d → Fin t → Fin 3 := fun i => let p := finProdFinEquiv.symm i; q p.2 ∘ h p.1
  let L1 : List (Fin d × Fin (k + 1) × Fin (k + 1)) := Finset.univ.toList
  let step1 : List Gate → (Fin d × Fin (k + 1) × Fin (k + 1)) → List Gate × ℕ :=
    fun gs ⟨i, L, U⟩ =>
      let (gs1, eqW) := mkEqConst N gs (dataWires (W := W) i) (targetMass t k (zCount (batch i)) L.val U.val)
      mkAnd N gs1 (2 + i.val * (W + 1)) eqW
  have hval0 : ValidState N [] := ⟨fun j hj => by simp at hj, fun _ hg => by cases hg⟩
  have hstep1 : ∀ gs z, ValidState N gs →
      ValidState N (step1 gs z).1 ∧ Extends gs (step1 gs z).1 ∧ (step1 gs z).1.length ≤ gs.length + (2 * W + 1) ∧
      ((step1 gs z).2 < N + (step1 gs z).1.length ∧
       ∀ (y : Fin d → Option ℕ), z.2.1.val + z.2.2.val ≤ k →
         let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
         evalW (step1 gs z).1 ([false, true] ++ bitsOf (W := W) y) (step1 gs z).2 =
           decide (yT z.1 = some (targetMass t k (zCount (batch z.1)) z.2.1.val z.2.2.val))) := by
    intro gs ⟨i, L, U⟩ hval
    dsimp [step1]
    have hisSome_lt : 2 + i.val * (W + 1) < N := by
      have hi : i.val + 1 ≤ d := i.isLt
      have hmul : (i.val + 1) * (W + 1) ≤ d * (W + 1) := Nat.mul_le_mul_right (W + 1) hi
      dsimp [N]; nlinarith
    have hdw := dataWires_valid (d := d) (W := W) gs i
    have hdw_len : (dataWires (W := W) i).length = W := dataWires_length i
    have hc_ok : ∀ (hLU : L.val + U.val ≤ k), targetMass t k (zCount (batch i)) L.val U.val < 2 ^ W := fun hLU =>
      targetMass_lt ht ((Finset.card_le_univ _).trans (by simp)) hLU
    have hmk_always : ∀ (ws : List ℕ) (g : List Gate) (c : ℕ),
        ValidState N g → ValidVec N g ws →
        let r := mkEqConst N g ws c
        ValidState N r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + 2 * ws.length ∧ r.2 < N + r.1.length := by
      intro ws
      induction ws with
      | nil => intro g c hv _; exact ⟨hv, Extends.refl g, by simp [mkEqConst], by simp [mkEqConst]; omega⟩
      | cons w ws' ih =>
        intro g c hv hws'
        dsimp [mkEqConst]
        have hw' : w < N + g.length := hws' w List.mem_cons_self
        have hws'' : ValidVec N g ws' := fun u hu => hws' u (List.mem_cons_of_mem w hu)
        have h1 : let p := if c % 2 = 1 then (g, w) else mkNot N g w
            ValidState N p.1 ∧ Extends g p.1 ∧ p.1.length ≤ g.length + 1 ∧ p.2 < N + p.1.length := by
          by_cases hmod : c % 2 = 1
          · simp only [hmod, ↓reduceIte]; exact ⟨hv, Extends.refl g, by omega, hw'⟩
          · simp only [hmod, ↓reduceIte]
            obtain ⟨va, ea, la, wa, _⟩ := mkNot_spec hv hw'
            exact ⟨va, ea, by omega, wa⟩
        set p1 := if c % 2 = 1 then (g, w) else mkNot N g w
        rcases h1 with ⟨v1, e1, l1, w1⟩
        obtain ⟨v2, e2, l2, w2⟩ := ih p1.1 (c / 2) v1 (hws''.mono e1)
        set p2 := mkEqConst N p1.1 ws' (c / 2)
        obtain ⟨v3, e3, l3, w3, _⟩ := mkAnd_spec v2 (lt_of_lt_of_le w1 (Nat.add_le_add_left e2.length_le N)) w2
        exact ⟨v3, e1.trans (e2.trans e3), by omega, w3⟩
    obtain ⟨v1, e1, l1, w1⟩ := hmk_always (dataWires (W := W) i) gs (targetMass t k (zCount (batch i)) L.val U.val) hval hdw
    set p1 := mkEqConst N gs (dataWires (W := W) i) (targetMass t k (zCount (batch i)) L.val U.val)
    obtain ⟨v2, e2, l2, w2, ev2⟩ := mkAnd_spec (a := 2 + i.val * (W + 1)) (b := p1.2) v1 (by omega) w1
    refine ⟨v2, e1.trans e2, by omega, w2, fun y hLU => ?_⟩
    obtain ⟨_, _, _, _, ev1⟩ := mkEqConst_spec hN2 (dataWires (W := W) i) gs
      (targetMass t k (zCount (batch i)) L.val U.val) hval hdw (by rw [hdw_len]; exact hc_ok hLU)
    change evalW (mkAnd N p1.1 (2 + i.val * (W + 1)) p1.2).1 ([false, true] ++ bitsOf (W := W) y)
        (mkAnd N p1.1 (2 + i.val * (W + 1)) p1.2).2 = _
    rw [ev2 _ (hx_len y), evalW_input p1.1 (hx_len y) hisSome_lt, input_isSome_getD y i,
        ev1 _ (hx_len y) (hx1 y), dataWires_val gs y i]
    exact option_match_eq (y i) W (targetMass t k (zCount (batch i)) L.val U.val)
  have h1_all := buildForList_spec step1 0 (2 * W + 1) []
    (fun gs z w => w < N + gs.length ∧
      ∀ (y : Fin d → Option ℕ), z.2.1.val + z.2.2.val ≤ k →
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        evalW gs ([false, true] ++ bitsOf (W := W) y) w =
          decide (yT z.1 = some (targetMass t k (zCount (batch z.1)) z.2.1.val z.2.2.val)))
    (fun gs1 gs2 z w hext ⟨hw, hev⟩ => ⟨lt_of_lt_of_le hw (Nat.add_le_add_left hext.length_le N),
      fun y hLU => by rw [hext.evalW_eq (hx_len y) hw]; exact hev y hLU⟩)
    (fun gs z hval _ => hstep1 gs z hval) L1 [] (Finset.nodup_toList _) hval0 (Extends.refl [])
  set res1 := buildForList step1 0 [] L1
  rcases h1_all with ⟨v1, _, len1, htab1⟩
  have htab1' : ∀ (i : Fin d) (L U : Fin (k + 1)),
      res1.2 (i, L, U) < N + res1.1.length ∧
      ∀ (y : Fin d → Option ℕ), L.val + U.val ≤ k →
        let yT : Fin d → Option ℕ := fun j => (y j).map (fun v => v % 2 ^ W)
        evalW res1.1 ([false, true] ++ bitsOf (W := W) y) (res1.2 (i, L, U)) =
          decide (yT i = some (targetMass t k (zCount (batch i)) L.val U.val)) :=
    fun i L U => htab1 (i, L, U) (Finset.mem_toList.mpr (Finset.mem_univ _))
  have hL1_len : L1.length = d * (k + 1) ^ 2 := by
    simp [L1, Finset.length_toList, Fintype.card_prod, Fintype.card_fin, sq, mul_assoc]
  let L2 : List (Fin H × LocModel B k) := Finset.univ.toList
  let step2 : List Gate → (Fin H × LocModel B k) → List Gate × List ℕ :=
    fun gs ⟨r, M_loc⟩ =>
      foldCState (fun g acc (j : Fin M) =>
        let i := finProdFinEquiv (r, j)
        let L : Fin (k + 1) := ⟨locLikeCount M_loc (q j), Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))⟩
        let U : Fin (k + 1) := ⟨locUnlikeCount M_loc (q j), Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))⟩
        let (g1, neqW) := mkNot N g (res1.2 (i, L, U))
        let (g2, disW) := mkAnd N g1 (2 + i.val * (W + 1)) neqW
        mkAddBit N g2 acc disW) gs (constVec b 0) (List.finRange M)
  have hstep2_aux : ∀ gs (z : Fin H × LocModel B k), ValidState N gs → Extends res1.1 gs →
      ValidState N (step2 gs z).1 ∧ Extends gs (step2 gs z).1 ∧
      (step2 gs z).1.length ≤ gs.length + M * (6 * b + 2) ∧
      (step2 gs z).2.length = b ∧ ValidVec N (step2 gs z).1 (step2 gs z).2 ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        vecVal (step2 gs z).1 ([false, true] ++ bitsOf (W := W) y) (step2 gs z).2 =
          locCostOf (t := t) h q yT z.1 z.2 := by
    intro gs ⟨r, M_loc⟩ hval hext1
    dsimp [step2]
    let f2 := fun g acc (j : Fin M) =>
      let i := finProdFinEquiv (r, j)
      let L : Fin (k + 1) := ⟨locLikeCount M_loc (q j), Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))⟩
      let U : Fin (k + 1) := ⟨locUnlikeCount M_loc (q j), Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))⟩
      let (g1, neqW) := mkNot N g (res1.2 (i, L, U))
      let (g2, disW) := mkAnd N g1 (2 + i.val * (W + 1)) neqW
      mkAddBit N g2 acc disW
    let disFn (y : Fin d → Option ℕ) (j : Fin M) : ℕ :=
      let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
      let i := finProdFinEquiv (r, j)
      if (yT i).isSome = true ∧
        yT i ≠ some (targetMass t k (zCount (q j ∘ h r)) (locLikeCount M_loc (q j)) (locUnlikeCount M_loc (q j)))
      then 1 else 0
    have hfold := foldCState_spec (N := N) f2 (6 * b + 2)
      (fun g acc rem => Extends res1.1 g ∧ acc.length = b ∧ ValidVec N g acc ∧
        ∀ y : Fin d → Option ℕ,
          vecVal g ([false, true] ++ bitsOf (W := W) y) acc + (rem.map (disFn y)).sum =
            ((List.finRange M).map (disFn y)).sum ∧
          vecVal g ([false, true] ++ bitsOf (W := W) y) acc + rem.length ≤ M)
      (fun g acc j rem hvg ⟨he1, hlen, hvac, hinv⟩ => by
        dsimp [f2]
        set i := finProdFinEquiv (r, j)
        set L : Fin (k + 1) := ⟨locLikeCount M_loc (q j), Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))⟩
        set U : Fin (k + 1) := ⟨locUnlikeCount M_loc (q j), Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))⟩
        have heqW := (htab1' i L U).1
        have heqW_g : res1.2 (i, L, U) < N + g.length := lt_of_lt_of_le heqW (Nat.add_le_add_left he1.length_le N)
        obtain ⟨va, ea, la, wa, eva⟩ := mkNot_spec hvg heqW_g
        set pa := mkNot N g (res1.2 (i, L, U))
        have his_lt : 2 + i.val * (W + 1) < N := by
          have hi : i.val + 1 ≤ d := i.isLt
          have hmul : (i.val + 1) * (W + 1) ≤ d * (W + 1) := Nat.mul_le_mul_right (W + 1) hi
          dsimp [N]; nlinarith
        obtain ⟨vb, eb, lb, wb, evb⟩ := mkAnd_spec (a := 2 + i.val * (W + 1)) (b := pa.2) va (by omega) wa
        set pb := mkAnd N pa.1 (2 + i.val * (W + 1)) pa.2
        obtain ⟨vc, ec, lc, lenc, hvc, evc⟩ := mkAddBit_spec acc pb.1 pb.2 vb (hvac.mono (ea.trans eb)) wb
        refine ⟨vc, ea.trans (eb.trans ec), by omega, he1.trans (ea.trans (eb.trans ec)), by omega, hvc, fun y => ?_⟩
        change vecVal (mkAddBit N pb.1 acc pb.2).1 ([false, true] ++ bitsOf (W := W) y) (mkAddBit N pb.1 acc pb.2).2 + _ = _ ∧
          vecVal (mkAddBit N pb.1 acc pb.2).1 ([false, true] ++ bitsOf (W := W) y) (mkAddBit N pb.1 acc pb.2).2 + _ ≤ M
        rw [evc _ (hx_len y), (ea.trans eb).vecVal_eq (hx_len y) hvac, evb _ (hx_len y),
            evalW_input pa.1 (hx_len y) his_lt, input_isSome_getD y i, eva _ (hx_len y),
            he1.evalW_eq (hx_len y) heqW, (htab1' i L U).2 y (locLike_add_locUnlike_le M_loc (q j))]
        have hbatch_i : batch i = q j ∘ h r := by
          dsimp [batch, i]; rw [finProdFinEquiv.symm_apply_apply]
        have hbit : (if ((y i).isSome && !decide ((y i).map (fun v => v % 2 ^ W) =
            some (targetMass t k (zCount (batch i)) L.val U.val))) = true then 1 else 0) = disFn y j := by
          rw [hbatch_i]
          exact option_disagree_eq (y i) W (targetMass t k (zCount (q j ∘ h r)) L.val U.val)
        rw [hbit]
        have ⟨hsum_inv, hle_inv⟩ := hinv y
        simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum_inv hle_inv
        have hdj : disFn y j ≤ 1 := by dsimp [disFn]; split_ifs <;> omega
        have hno_ovf : vecVal g ([false, true] ++ bitsOf (W := W) y) acc + disFn y j < 2 ^ acc.length := by
          rw [hlen]; omega
        rw [Nat.mod_eq_of_lt hno_ovf]
        exact ⟨by omega, by omega⟩)
      (List.finRange M) gs (constVec b 0) hval
      ⟨hext1, constVec_length b 0, constVec_valid hN2 gs b 0, fun y => by
        rw [constVec_val hN2 gs (hx_len y) (hx0 y) (hx1 y) b 0 (by positivity)]
        simp⟩
    rcases hfold with ⟨v', e', l', _, len', hv', hfin⟩
    refine ⟨v', e', by simpa only [List.length_finRange] using l', len', hv', fun y => ?_⟩
    have h1 := (hfin y).1
    simp only [List.map_nil, List.sum_nil, add_zero] at h1
    change vecVal (foldCState f2 gs (constVec b 0) (List.finRange M)).1 ([false, true] ++ bitsOf (W := W) y)
      (foldCState f2 gs (constVec b 0) (List.finRange M)).2 = _
    rw [h1]
    unfold locCostOf
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hsum_fin : ((List.finRange M).map (disFn y)).sum = ∑ j : Fin M, disFn y j := by
      rw [← Fin.sum_univ_def]
    rw [hsum_fin]
  have h2_all := buildForList_spec step2 (constVec b 0) (M * (6 * b + 2)) res1.1
    (fun gs z v => v.length = b ∧ ValidVec N gs v ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        vecVal gs ([false, true] ++ bitsOf (W := W) y) v = locCostOf (t := t) h q yT z.1 z.2)
    (fun gs1 gs2 z v hext ⟨hlen, hv, hev⟩ =>
      ⟨hlen, hv.mono hext, fun y => by rw [hext.vecVal_eq (hx_len y) hv]; exact hev y⟩)
    (fun gs z hval hext => hstep2_aux gs z hval hext)
    L2 res1.1 (Finset.nodup_toList _) v1 (Extends.refl res1.1)
  set res2 := buildForList step2 (constVec b 0) res1.1 L2
  rcases h2_all with ⟨v2, e12, len2, htab2⟩
  have htab2' : ∀ (r : Fin H) (M_loc : LocModel B k),
      (res2.2 (r, M_loc)).length = b ∧ ValidVec N res2.1 (res2.2 (r, M_loc)) ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        vecVal res2.1 ([false, true] ++ bitsOf (W := W) y) (res2.2 (r, M_loc)) =
          locCostOf (t := t) h q yT r M_loc :=
    fun r M_loc => htab2 (r, M_loc) (Finset.mem_toList.mpr (Finset.mem_univ _))
  have hL2_len : L2.length = H * Fintype.card (LocModel B k) := by
    simp [L2, Finset.length_toList, Fintype.card_prod, Fintype.card_fin]
  let L3 : List (pairOf t × Fin H × Fin (k + 1)) := Finset.univ.toList
  let step3 : List Gate → (pairOf t × Fin H × Fin (k + 1)) → List Gate × List ℕ :=
    fun gs ⟨e, r, m⟩ =>
      foldCState (fun g acc M_loc => mkMinVec N g acc (res2.2 (r, M_loc)))
        gs (constVec b M) (goodLocList (h r) e m.val)
  have hgoodList_len : ∀ (r : Fin H) (e : pairOf t) (m : ℕ),
      (goodLocList (k := k) (h r) e m).length ≤ Fintype.card (LocModel B k) := by
    intro r e m
    unfold goodLocList
    exact (List.length_filter_le _ _).trans (by simp [Finset.length_toList])
  have hstep3_aux : ∀ gs (z : pairOf t × Fin H × Fin (k + 1)), ValidState N gs → Extends res2.1 gs →
      ValidState N (step3 gs z).1 ∧ Extends gs (step3 gs z).1 ∧
      (step3 gs z).1.length ≤ gs.length + Fintype.card (LocModel B k) * (14 * b) ∧
      (step3 gs z).2.length = b ∧ ValidVec N (step3 gs z).1 (step3 gs z).2 ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        vecVal (step3 gs z).1 ([false, true] ++ bitsOf (W := W) y) (step3 gs z).2 =
          listMinCost (t := t) (k := k) h q yT z.2.1 (goodLocList (k := k) (h z.2.1) z.1 z.2.2.val) := by
    intro gs ⟨e, r, m⟩ hval hext2
    dsimp [step3]
    let f3 := fun g acc M_loc => mkMinVec N g acc (res2.2 (r, M_loc))
    have hfold := foldCState_spec (N := N) f3 (14 * b)
      (fun g acc rem => Extends res2.1 g ∧ acc.length = b ∧ ValidVec N g acc ∧
        ∀ y : Fin d → Option ℕ,
          let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
          rem.foldl (fun a M_loc => min a (locCostOf (t := t) h q yT r M_loc))
            (vecVal g ([false, true] ++ bitsOf (W := W) y) acc) =
          listMinCost (t := t) (k := k) h q yT r (goodLocList (k := k) (h r) e m.val))
      (fun g acc M_loc rem hvg ⟨he2, hlen, hvac, hinv⟩ => by
        dsimp [f3]
        obtain ⟨hlM, hvM, hevM⟩ := htab2' r M_loc
        obtain ⟨vm, em, lm, lenm, hvm, evm⟩ := mkMinVec_spec hN2 (by omega : acc.length = (res2.2 (r, M_loc)).length)
          hvg hvac (hvM.mono he2)
        refine ⟨vm, em, by omega, he2.trans em, by omega, hvm, fun y => ?_⟩
        change rem.foldl _ (vecVal (mkMinVec N g acc (res2.2 (r, M_loc))).1 ([false, true] ++ bitsOf (W := W) y)
          (mkMinVec N g acc (res2.2 (r, M_loc))).2) = _
        rw [evm _ (hx_len y) (hx0 y), he2.vecVal_eq (hx_len y) hvM, hevM y]
        simpa only [List.foldl_cons] using hinv y)
      (goodLocList (k := k) (h r) e m.val) gs (constVec b M) hval
      ⟨hext2, constVec_length b M, constVec_valid hN2 gs b M, fun y => by
        rw [constVec_val hN2 gs (hx_len y) (hx0 y) (hx1 y) b M (lt_of_le_of_lt hM_le_d hd_lt_2b)]
        rfl⟩
    rcases hfold with ⟨v', e', l', _, len', hv', hfin⟩
    have hlen_le : (goodLocList (k := k) (h r) e m.val).length * (14 * b) ≤ Fintype.card (LocModel B k) * (14 * b) :=
      Nat.mul_le_mul_right _ (hgoodList_len r e m.val)
    refine ⟨v', e', l'.trans (Nat.add_le_add_left hlen_le _), len', hv', fun y => ?_⟩
    change vecVal (foldCState f3 gs (constVec b M) (goodLocList (k := k) (h r) e m.val)).1
      ([false, true] ++ bitsOf (W := W) y)
      (foldCState f3 gs (constVec b M) (goodLocList (k := k) (h r) e m.val)).2 = _
    simpa only [List.foldl_nil] using hfin y
  have h3_all := buildForList_spec step3 (constVec b 0) (Fintype.card (LocModel B k) * (14 * b)) res2.1
    (fun gs z v => v.length = b ∧ ValidVec N gs v ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        vecVal gs ([false, true] ++ bitsOf (W := W) y) v =
          listMinCost (t := t) (k := k) h q yT z.2.1 (goodLocList (k := k) (h z.2.1) z.1 z.2.2.val))
    (fun gs1 gs2 z v hext ⟨hlen, hv, hev⟩ =>
      ⟨hlen, hv.mono hext, fun y => by rw [hext.vecVal_eq (hx_len y) hv]; exact hev y⟩)
    (fun gs z hval hext => hstep3_aux gs z hval hext)
    L3 res2.1 (Finset.nodup_toList _) v2 (Extends.refl res2.1)
  set res3 := buildForList step3 (constVec b 0) res2.1 L3
  rcases h3_all with ⟨v3, e23, len3, htab3⟩
  have htab3' : ∀ (e : pairOf t) (r : Fin H) (m : Fin (k + 1)),
      (res3.2 (e, r, m)).length = b ∧ ValidVec N res3.1 (res3.2 (e, r, m)) ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        vecVal res3.1 ([false, true] ++ bitsOf (W := W) y) (res3.2 (e, r, m)) =
          listMinCost (t := t) (k := k) h q yT r (goodLocList (k := k) (h r) e m.val) :=
    fun e r m => htab3 (e, r, m) (Finset.mem_toList.mpr (Finset.mem_univ _))
  have hL3_len : L3.length = Fintype.card (pairOf t) * H * (k + 1) := by
    simp [L3, Finset.length_toList, Fintype.card_prod, Fintype.card_fin, mul_assoc]
  let L4 : List (pairOf t × Fin (k + 1)) := Finset.univ.toList
  let step4 : List Gate → (pairOf t × Fin (k + 1)) → List Gate × List ℕ :=
    fun gs ⟨e, m⟩ =>
      foldCState (fun g acc (r : Fin H) => mkAddVecAux N g acc (res3.2 (e, r, m)) 0)
        gs (constVec b 0) (List.finRange H)
  have hstep4_aux : ∀ gs (z : pairOf t × Fin (k + 1)), ValidState N gs → Extends res3.1 gs →
      ValidState N (step4 gs z).1 ∧ Extends gs (step4 gs z).1 ∧
      (step4 gs z).1.length ≤ gs.length + H * (13 * b) ∧
      (step4 gs z).2.length = b ∧ ValidVec N (step4 gs z).1 (step4 gs z).2 ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        vecVal (step4 gs z).1 ([false, true] ++ bitsOf (W := W) y) (step4 gs z).2 =
          totalCostOf (t := t) (k := k) h q yT z.1 z.2.val := by
    intro gs ⟨e, m⟩ hval hext3
    dsimp [step4]
    let f4 := fun g acc (r : Fin H) => mkAddVecAux N g acc (res3.2 (e, r, m)) 0
    let mcFn (y : Fin d → Option ℕ) (r : Fin H) : ℕ :=
      let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
      listMinCost (t := t) (k := k) h q yT r (goodLocList (k := k) (h r) e m.val)
    have hmc_le : ∀ y r, mcFn y r ≤ M := fun y r => foldl_min_le_init _ M _
    have hfold := foldCState_spec (N := N) f4 (13 * b)
      (fun g acc rem => Extends res3.1 g ∧ acc.length = b ∧ ValidVec N g acc ∧
        ∀ y : Fin d → Option ℕ,
          vecVal g ([false, true] ++ bitsOf (W := W) y) acc + (rem.map (mcFn y)).sum =
            ((List.finRange H).map (mcFn y)).sum ∧
          vecVal g ([false, true] ++ bitsOf (W := W) y) acc + rem.length * M ≤ d)
      (fun g acc r rem hvg ⟨he3, hlen, hvac, hinv⟩ => by
        dsimp [f4]
        obtain ⟨hl3, hv3, hev3⟩ := htab3' e r m
        obtain ⟨va, ea, la, lena, hva, eva⟩ := mkAddVecAux_spec acc (res3.2 (e, r, m)) g 0
          (by omega) hvg hvac (hv3.mono he3) (by omega)
        refine ⟨va, ea, by omega, he3.trans ea, by omega, hva, fun y => ?_⟩
        change vecVal (mkAddVecAux N g acc (res3.2 (e, r, m)) 0).1 ([false, true] ++ bitsOf (W := W) y)
            (mkAddVecAux N g acc (res3.2 (e, r, m)) 0).2 + _ = _ ∧
          vecVal (mkAddVecAux N g acc (res3.2 (e, r, m)) 0).1 ([false, true] ++ bitsOf (W := W) y)
            (mkAddVecAux N g acc (res3.2 (e, r, m)) 0).2 + _ ≤ d
        rw [eva _ (hx_len y), he3.vecVal_eq (hx_len y) hv3, hev3 y, evalW_input g (hx_len y) (by omega), hx0 y]
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        have ⟨hsum_inv, hle_inv⟩ := hinv y
        simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum_inv hle_inv
        have hmr : mcFn y r ≤ M := hmc_le y r
        have hno_ovf : vecVal g ([false, true] ++ bitsOf (W := W) y) acc + mcFn y r < 2 ^ acc.length := by
          rw [hlen]
          have : (rem.length + 1) * M = rem.length * M + M := by ring
          omega
        change (vecVal g ([false, true] ++ bitsOf (W := W) y) acc + mcFn y r) % 2 ^ acc.length + _ = _ ∧
          (vecVal g ([false, true] ++ bitsOf (W := W) y) acc + mcFn y r) % 2 ^ acc.length + _ ≤ d
        rw [Nat.mod_eq_of_lt hno_ovf]
        have : (rem.length + 1) * M = rem.length * M + M := by ring
        exact ⟨by omega, by omega⟩)
      (List.finRange H) gs (constVec b 0) hval
      ⟨hext3, constVec_length b 0, constVec_valid hN2 gs b 0, fun y => by
        rw [constVec_val hN2 gs (hx_len y) (hx0 y) (hx1 y) b 0 (by positivity)]
        simp [d]⟩
    rcases hfold with ⟨v', e', l', _, len', hv', hfin⟩
    refine ⟨v', e', by simpa only [List.length_finRange] using l', len', hv', fun y => ?_⟩
    have h1 := (hfin y).1
    simp only [List.map_nil, List.sum_nil, add_zero] at h1
    change vecVal (foldCState f4 gs (constVec b 0) (List.finRange H)).1 ([false, true] ++ bitsOf (W := W) y)
      (foldCState f4 gs (constVec b 0) (List.finRange H)).2 = _
    rw [h1]
    unfold totalCostOf
    rw [← Fin.sum_univ_def]
  have h4_all := buildForList_spec step4 (constVec b 0) (H * (13 * b)) res3.1
    (fun gs z v => v.length = b ∧ ValidVec N gs v ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        vecVal gs ([false, true] ++ bitsOf (W := W) y) v = totalCostOf (t := t) (k := k) h q yT z.1 z.2.val)
    (fun gs1 gs2 z v hext ⟨hlen, hv, hev⟩ =>
      ⟨hlen, hv.mono hext, fun y => by rw [hext.vecVal_eq (hx_len y) hv]; exact hev y⟩)
    (fun gs z hval hext => hstep4_aux gs z hval hext)
    L4 res3.1 (Finset.nodup_toList _) v3 (Extends.refl res3.1)
  set res4 := buildForList step4 (constVec b 0) res3.1 L4
  rcases h4_all with ⟨v4, e34, len4, htab4⟩
  have htab4' : ∀ (e : pairOf t) (m : Fin (k + 1)),
      (res4.2 (e, m)).length = b ∧ ValidVec N res4.1 (res4.2 (e, m)) ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        vecVal res4.1 ([false, true] ++ bitsOf (W := W) y) (res4.2 (e, m)) =
          totalCostOf (t := t) (k := k) h q yT e m.val :=
    fun e m => htab4 (e, m) (Finset.mem_toList.mpr (Finset.mem_univ _))
  have hL4_len : L4.length = Fintype.card (pairOf t) * (k + 1) := by
    simp [L4, Finset.length_toList, Fintype.card_prod, Fintype.card_fin]
  let step5 : List Gate → (pairOf t × Fin (k + 1)) → List Gate × ℕ :=
    fun gs ⟨e, m⟩ =>
      foldCState (fun g acc (m' : Fin (k + 1)) =>
        if m' = m then (g, acc) else
          let (g1, ltW) := mkLtVec N g (res4.2 (e, m)) (res4.2 (e, m'))
          mkAnd N g1 acc ltW) gs 1 (List.finRange (k + 1))
  have hstep5_aux : ∀ gs (z : pairOf t × Fin (k + 1)), ValidState N gs → Extends res4.1 gs →
      ValidState N (step5 gs z).1 ∧ Extends gs (step5 gs z).1 ∧
      (step5 gs z).1.length ≤ gs.length + (k + 1) * (10 * b + 1) ∧
      (step5 gs z).2 < N + (step5 gs z).1.length ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        evalW (step5 gs z).1 ([false, true] ++ bitsOf (W := W) y) (step5 gs z).2 =
          decide (∀ m' : Fin (k + 1), m' ≠ z.2 →
            totalCostOf (t := t) (k := k) h q yT z.1 z.2.val < totalCostOf (t := t) (k := k) h q yT z.1 m'.val) := by
    intro gs ⟨e, m⟩ hval hext4
    dsimp [step5]
    let f5 := fun g acc (m' : Fin (k + 1)) =>
      if m' = m then (g, acc) else
        let (g1, ltW) := mkLtVec N g (res4.2 (e, m)) (res4.2 (e, m'))
        mkAnd N g1 acc ltW
    let prop5 (y : Fin d → Option ℕ) (m' : Fin (k + 1)) : Prop :=
      let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
      m' ≠ m → totalCostOf (t := t) (k := k) h q yT e m.val < totalCostOf (t := t) (k := k) h q yT e m'.val
    have hfold := foldCState_spec (N := N) f5 (10 * b + 1)
      (fun g acc rem => Extends res4.1 g ∧ acc < N + g.length ∧
        ∀ y : Fin d → Option ℕ,
          (evalW g ([false, true] ++ bitsOf (W := W) y) acc = true ∧ ∀ m' ∈ rem, prop5 y m') ↔
          (∀ m' : Fin (k + 1), prop5 y m'))
      (fun g acc m' rem hvg ⟨he4, hacc, hinv⟩ => by
        dsimp [f5]
        by_cases hmeq : m' = m
        · simp only [hmeq, ↓reduceIte]
          refine ⟨hvg, Extends.refl g, by omega, he4, hacc, fun y => ?_⟩
          have hy := hinv y
          constructor
          · intro ⟨ha, hrem⟩
            exact hy.mp ⟨ha, fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hxr
              · intro hc; exact absurd hmeq hc
              · exact hrem x hxr⟩
          · intro hall
            have ⟨ha, hcons⟩ := hy.mpr hall
            exact ⟨ha, fun x hx => hcons x (List.mem_cons_of_mem m' hx)⟩
        · simp only [hmeq, ↓reduceIte]
          obtain ⟨hlm, hvm, hevm⟩ := htab4' e m
          obtain ⟨hlm', hvm', hevm'⟩ := htab4' e m'
          obtain ⟨v1, e1, l1, w1, ev1⟩ := mkLtVec_spec hN2 (by omega : (res4.2 (e, m)).length = (res4.2 (e, m')).length)
            hvg (hvm.mono he4) (hvm'.mono he4)
          set p1 := mkLtVec N g (res4.2 (e, m)) (res4.2 (e, m'))
          obtain ⟨v2, e2, l2, w2, ev2⟩ := mkAnd_spec (a := acc) (b := p1.2) v1
            (lt_of_lt_of_le hacc (Nat.add_le_add_left e1.length_le N)) w1
          refine ⟨v2, e1.trans e2, by omega, he4.trans (e1.trans e2), w2, fun y => ?_⟩
          change (evalW (mkAnd N p1.1 acc p1.2).1 ([false, true] ++ bitsOf (W := W) y) (mkAnd N p1.1 acc p1.2).2 = true ∧ _) ↔ _
          rw [ev2 _ (hx_len y), e1.evalW_eq (hx_len y) hacc, ev1 _ (hx_len y) (hx0 y),
              he4.vecVal_eq (hx_len y) hvm, he4.vecVal_eq (hx_len y) hvm', hevm y, hevm' y]
          have hy := hinv y
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨⟨ha, hlt⟩, hrem⟩
            exact hy.mp ⟨ha, fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hxr
              · intro _; exact hlt
              · exact hrem x hxr⟩
          · intro hall
            have ⟨ha, hcons⟩ := hy.mpr hall
            exact ⟨⟨ha, hcons m' List.mem_cons_self hmeq⟩, fun x hx => hcons x (List.mem_cons_of_mem m' hx)⟩)
      (List.finRange (k + 1)) gs 1 hval
      ⟨hext4, by omega, fun y => by
        rw [evalW_input gs (hx_len y) (by omega), hx1 y]
        simp [List.mem_finRange]⟩
    rcases hfold with ⟨v', e', l', _, w', hfin⟩
    refine ⟨v', e', by simpa only [List.length_finRange] using l', w', fun y => ?_⟩
    have hy := hfin y
    simp only [List.not_mem_nil, false_implies, implies_true, and_true] at hy
    change evalW (foldCState f5 gs 1 (List.finRange (k + 1))).1 ([false, true] ++ bitsOf (W := W) y)
      (foldCState f5 gs 1 (List.finRange (k + 1))).2 = _
    cases hb : evalW (foldCState f5 gs 1 (List.finRange (k + 1))).1 ([false, true] ++ bitsOf (W := W) y)
      (foldCState f5 gs 1 (List.finRange (k + 1))).2
    · symm; exact decide_eq_false (fun hall => by have := hy.mpr hall; rw [hb] at this; cases this)
    · symm; exact decide_eq_true (hy.mp hb)
  have h5_all := buildForList_spec step5 0 ((k + 1) * (10 * b + 1)) res4.1
    (fun gs z w => w < N + gs.length ∧
      ∀ (y : Fin d → Option ℕ),
        let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
        evalW gs ([false, true] ++ bitsOf (W := W) y) w =
          decide (∀ m' : Fin (k + 1), m' ≠ z.2 →
            totalCostOf (t := t) (k := k) h q yT z.1 z.2.val < totalCostOf (t := t) (k := k) h q yT z.1 m'.val))
    (fun gs1 gs2 z w hext ⟨hw, hev⟩ =>
      ⟨lt_of_lt_of_le hw (Nat.add_le_add_left hext.length_le N),
       fun y => by rw [hext.evalW_eq (hx_len y) hw]; exact hev y⟩)
    (fun gs z hval hext => hstep5_aux gs z hval hext)
    L4 res4.1 (Finset.nodup_toList _) v4 (Extends.refl res4.1)
  set res5 := buildForList step5 0 res4.1 L4
  rcases h5_all with ⟨v5, e45, len5, htab5⟩
  refine ⟨v5, ?_, ?_, ?_⟩
  · have hlen_calc : res5.1.length ≤
        d * (k + 1) ^ 2 * (2 * W + 1) +
        d * Fintype.card (LocModel B k) * (6 * b + 2) +
        Fintype.card (pairOf t) * H * (k + 1) * Fintype.card (LocModel B k) * (14 * b) +
        Fintype.card (pairOf t) * (k + 1) * H * (13 * b) +
        Fintype.card (pairOf t) * (k + 1) ^ 2 * (10 * b + 1) := by
      rw [hL1_len, List.length_nil, zero_add] at len1
      rw [hL2_len] at len2
      rw [hL3_len] at len3
      rw [hL4_len] at len4 len5
      have ha : H * Fintype.card (LocModel B k) * (M * (6 * b + 2)) =
          d * Fintype.card (LocModel B k) * (6 * b + 2) := by dsimp [d]; ring
      have hb3 : Fintype.card (pairOf t) * H * (k + 1) * (Fintype.card (LocModel B k) * (14 * b)) =
          Fintype.card (pairOf t) * H * (k + 1) * Fintype.card (LocModel B k) * (14 * b) := by ring
      have hb : Fintype.card (pairOf t) * (k + 1) * (H * (13 * b)) =
          Fintype.card (pairOf t) * (k + 1) * H * (13 * b) := by ring
      have hc : Fintype.card (pairOf t) * (k + 1) * ((k + 1) * (10 * b + 1)) =
          Fintype.card (pairOf t) * (k + 1) ^ 2 * (10 * b + 1) := by ring
      omega
    exact hlen_calc
  · intro e m
    exact (htab5 (e, m) (Finset.mem_toList.mpr (Finset.mem_univ _))).1
  · intro y e m
    exact (htab5 (e, m) (Finset.mem_toList.mpr (Finset.mem_univ _))).2 y

lemma card_locModel_le (B k X : ℕ) (hX : 6 ≤ X) (hB : B ≤ X ^ 5) :
    Fintype.card (LocModel B k) ≤ X ^ (11 * k) := by
  have hslot : Fintype.card (LocSlot B) ≤ X ^ 11 := by
    rw [Fintype.card_option]
    have h1 : Fintype.card (LocPair B) ≤ B ^ 2 := card_locPair_le B
    have h2 : B ^ 2 ≤ X ^ 10 := by
      calc B ^ 2 ≤ (X ^ 5) ^ 2 := Nat.pow_le_pow_left hB 2
        _ = X ^ 10 := by ring
    have h3 : 1 ≤ X ^ 10 := Nat.one_le_pow 10 X (by omega)
    have h4 : X ^ 10 + X ^ 10 ≤ X ^ 11 := by
      calc X ^ 10 + X ^ 10 = 2 * X ^ 10 := by ring
        _ ≤ X * X ^ 10 := Nat.mul_le_mul_right (X ^ 10) (by omega)
        _ = X ^ 11 := by rw [pow_succ]; ring
    exact (Nat.add_le_add (h1.trans h2) h3).trans h4
  calc Fintype.card (LocModel B k) = Fintype.card (LocSlot B) ^ k := by simp
    _ ≤ (X ^ 11) ^ k := Nat.pow_le_pow_left hslot k
    _ = X ^ (11 * k) := by rw [← pow_mul]

lemma gate_size_bound_aux {t k s X T : ℕ} (ht : 2 ≤ t) (hk : 0 < k) (hs : 3 ≤ s)
    (hXeq : X = k + s + 2) (hTeq : T = t + 2) :
    let B := 128 * (k + 1) * s
    let H := 256 * (k + 1) * s * (1 + Nat.log 2 t)
    let M := 600 * (k + 1) * s ^ 2 * (1 + Nat.log 2 B)
    let d := H * M
    let W := k * (2 * t + 2) + 1
    let b := Nat.log 2 d + 2
    d * (k + 1) ^ 2 * (2 * W + 1) +
    d * Fintype.card (LocModel B k) * (6 * b + 2) +
    Fintype.card (pairOf t) * H * (k + 1) * Fintype.card (LocModel B k) * (14 * b) +
    Fintype.card (pairOf t) * (k + 1) * H * (13 * b) +
    Fintype.card (pairOf t) * (k + 1) ^ 2 * (10 * b + 1) ≤
      T ^ 50 * X ^ (50 * (k + 1)) := by
  intro B H M d W b
  have hX6 : 6 ≤ X := by omega
  have hT4 : 4 ≤ T := by omega
  have hX_pow : ∀ a c : ℕ, a ≤ c → X ^ a ≤ X ^ c := fun a c hac => Nat.pow_le_pow_right (by omega) hac
  have hT_pow : ∀ a c : ℕ, a ≤ c → T ^ a ≤ T ^ c := fun a c hac => Nat.pow_le_pow_right (by omega) hac
  have hkX : k + 1 ≤ X := by omega
  have hsX : s ≤ X := by omega
  have h128 : 128 ≤ X ^ 3 := by
    have : 6 ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hX6 3
    omega
  have h256 : 256 ≤ X ^ 4 := by
    have : 6 ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left hX6 4
    omega
  have h600 : 600 ≤ X ^ 4 := by
    have : 6 ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left hX6 4
    omega
  have hB_le : B ≤ X ^ 5 := by
    calc B = 128 * (k + 1) * s := rfl
      _ ≤ X ^ 3 * X * X := Nat.mul_le_mul (Nat.mul_le_mul h128 hkX) hsX
      _ = X ^ 5 := by ring
  have hlogt : 1 + Nat.log 2 t ≤ T := by
    have h1 : Nat.log 2 t ≤ t := Nat.log_le_self 2 t
    omega
  have hlogB : 1 + Nat.log 2 B ≤ X ^ 5 := by
    have h1 : Nat.log 2 B < B := Nat.log_lt_self 2 (by dsimp [B]; positivity)
    omega
  have hH_le : H ≤ T * X ^ 6 := by
    calc H = 256 * (k + 1) * s * (1 + Nat.log 2 t) := rfl
      _ ≤ X ^ 4 * X * X * T := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h256 hkX) hsX) hlogt
      _ = T * X ^ 6 := by ring
  have hM_le : M ≤ X ^ 12 := by
    calc M = 600 * (k + 1) * s ^ 2 * (1 + Nat.log 2 B) := rfl
      _ ≤ X ^ 4 * X * X ^ 2 * X ^ 5 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h600 hkX) (Nat.pow_le_pow_left hsX 2)) hlogB
      _ = X ^ 12 := by ring
  have hd_le : d ≤ T * X ^ 18 := by
    calc d = H * M := rfl
      _ ≤ (T * X ^ 6) * X ^ 12 := Nat.mul_le_mul hH_le hM_le
      _ = T * X ^ 18 := by ring
  have hb_le : b ≤ T ^ 2 * X ^ 18 := by
    set U := T * X ^ 18
    have hlogd : Nat.log 2 d ≤ d := Nat.log_le_self 2 d
    have hX18 : 1 ≤ X ^ 18 := Nat.one_le_pow 18 X (by omega)
    have h2le : 2 ≤ U := by
      calc 2 ≤ T := by omega
        _ = T * 1 := (mul_one T).symm
        _ ≤ T * X ^ 18 := Nat.mul_le_mul_left T hX18
    calc b = Nat.log 2 d + 2 := rfl
      _ ≤ d + 2 := by omega
      _ ≤ U + U := by omega
      _ = 2 * U := by ring
      _ ≤ T * U := Nat.mul_le_mul_right U (by omega)
      _ = T ^ 2 * X ^ 18 := by dsimp [U]; ring
  have hW_le : 2 * W + 1 ≤ T ^ 3 * X := by
    clear B H M d b hB_le hlogt hlogB hH_le hM_le hd_le hb_le
    have h1 : 2 * W + 1 = 4 * k * t + 4 * k + 3 := by dsimp [W]; ring
    have hkt : k * t ≤ X * T := Nat.mul_le_mul (by omega) (by omega)
    have hkx : k ≤ X * T := by
      calc k ≤ X := by omega
        _ = X * 1 := (mul_one X).symm
        _ ≤ X * T := Nat.mul_le_mul_left X (by omega)
    have h3 : 3 ≤ X * T := by
      calc 3 ≤ T := by omega
        _ = 1 * T := (one_mul T).symm
        _ ≤ X * T := Nat.mul_le_mul_right T (by omega)
    have h9 : 9 ≤ T ^ 2 := by
      have : 4 ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hT4 2
      omega
    calc 2 * W + 1 = 4 * (k * t) + 4 * k + 3 := by rw [h1]; ring
      _ ≤ 4 * (X * T) + 4 * (X * T) + (X * T) := by omega
      _ = 9 * (X * T) := by ring
      _ ≤ T ^ 2 * (X * T) := Nat.mul_le_mul_right (X * T) h9
      _ = T ^ 3 * X := by ring
  have hpair_le : Fintype.card (pairOf t) ≤ T ^ 2 :=
    (card_pairOf_le t).trans (Nat.pow_le_pow_left (by omega) 2)
  have hloc_le : Fintype.card (LocModel B k) ≤ X ^ (11 * k) :=
    card_locModel_le B k X hX6 hB_le
  have hterm1 : d * (k + 1) ^ 2 * (2 * W + 1) ≤ T ^ 10 * X ^ (40 * (k + 1)) := by
    calc d * (k + 1) ^ 2 * (2 * W + 1)
        ≤ (T * X ^ 18) * X ^ 2 * (T ^ 3 * X) :=
          Nat.mul_le_mul (Nat.mul_le_mul hd_le (Nat.pow_le_pow_left hkX 2)) hW_le
      _ = T ^ 4 * X ^ 21 := by ring
      _ ≤ T ^ 10 * X ^ (40 * (k + 1)) := Nat.mul_le_mul (hT_pow 4 10 (by omega)) (hX_pow 21 _ (by omega))
  have h6b : 6 * b + 2 ≤ T ^ 3 * X ^ 19 := by
    have h1 : 6 * b + 2 ≤ 8 * b := by dsimp [b]; omega
    have h2 : 8 ≤ T * X := by
      calc 8 ≤ 4 * 6 := by omega
        _ ≤ T * X := Nat.mul_le_mul hT4 hX6
    calc 6 * b + 2 ≤ 8 * b := h1
      _ ≤ (T * X) * (T ^ 2 * X ^ 18) := Nat.mul_le_mul h2 hb_le
      _ = T ^ 3 * X ^ 19 := by ring
  have hterm2 : d * Fintype.card (LocModel B k) * (6 * b + 2) ≤ T ^ 10 * X ^ (40 * (k + 1)) := by
    calc d * Fintype.card (LocModel B k) * (6 * b + 2)
        ≤ (T * X ^ 18) * X ^ (11 * k) * (T ^ 3 * X ^ 19) :=
          Nat.mul_le_mul (Nat.mul_le_mul hd_le hloc_le) h6b
      _ = T ^ 4 * X ^ (37 + 11 * k) := by rw [show T * X ^ 18 * X ^ (11 * k) * (T ^ 3 * X ^ 19) =
          (T * T ^ 3) * (X ^ 18 * X ^ 19 * X ^ (11 * k)) by ring, ← pow_add, ← pow_add]; ring_nf
      _ ≤ T ^ 10 * X ^ (40 * (k + 1)) := Nat.mul_le_mul (hT_pow 4 10 (by omega)) (hX_pow _ _ (by omega))
  have h14b : 14 * b ≤ T ^ 3 * X ^ 19 := by
    have h1 : 14 ≤ T * X := by
      calc 14 ≤ 4 * 6 := by omega
        _ ≤ T * X := Nat.mul_le_mul hT4 hX6
    calc 14 * b ≤ (T * X) * (T ^ 2 * X ^ 18) := Nat.mul_le_mul h1 hb_le
      _ = T ^ 3 * X ^ 19 := by ring
  have hterm3 : Fintype.card (pairOf t) * H * (k + 1) * Fintype.card (LocModel B k) * (14 * b) ≤
      T ^ 10 * X ^ (40 * (k + 1)) := by
    calc Fintype.card (pairOf t) * H * (k + 1) * Fintype.card (LocModel B k) * (14 * b)
        ≤ T ^ 2 * (T * X ^ 6) * X * X ^ (11 * k) * (T ^ 3 * X ^ 19) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hpair_le hH_le) hkX) hloc_le) h14b
      _ = T ^ 6 * X ^ (26 + 11 * k) := by rw [pow_add]; ring
      _ ≤ T ^ 10 * X ^ (40 * (k + 1)) := Nat.mul_le_mul (hT_pow 6 10 (by omega)) (hX_pow _ _ (by omega))
  have h13b : 13 * b ≤ T ^ 3 * X ^ 19 := le_trans (Nat.mul_le_mul_right b (by omega)) h14b
  have hterm4 : Fintype.card (pairOf t) * (k + 1) * H * (13 * b) ≤ T ^ 10 * X ^ (40 * (k + 1)) := by
    calc Fintype.card (pairOf t) * (k + 1) * H * (13 * b)
        ≤ T ^ 2 * X * (T * X ^ 6) * (T ^ 3 * X ^ 19) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hpair_le hkX) hH_le) h13b
      _ = T ^ 6 * X ^ 26 := by ring
      _ ≤ T ^ 10 * X ^ (40 * (k + 1)) := Nat.mul_le_mul (hT_pow 6 10 (by omega)) (hX_pow 26 _ (by omega))
  have h10b : 10 * b + 1 ≤ T ^ 3 * X ^ 19 := by
    have : 10 * b + 1 ≤ 14 * b := by dsimp [b]; omega
    exact this.trans h14b
  have hterm5 : Fintype.card (pairOf t) * (k + 1) ^ 2 * (10 * b + 1) ≤ T ^ 10 * X ^ (40 * (k + 1)) := by
    calc Fintype.card (pairOf t) * (k + 1) ^ 2 * (10 * b + 1)
        ≤ T ^ 2 * X ^ 2 * (T ^ 3 * X ^ 19) :=
          Nat.mul_le_mul (Nat.mul_le_mul hpair_le (Nat.pow_le_pow_left hkX 2)) h10b
      _ = T ^ 5 * X ^ 21 := by ring
      _ ≤ T ^ 10 * X ^ (40 * (k + 1)) := Nat.mul_le_mul (hT_pow 5 10 (by omega)) (hX_pow 21 _ (by omega))
  have h5_le : 5 ≤ T ^ 40 := by
    have h1 : 5 ≤ 4 ^ 2 := by decide
    have h2 : 4 ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hT4 2
    exact (h1.trans h2).trans (hT_pow 2 40 (by decide))
  set Bnd := T ^ 10 * X ^ (40 * (k + 1))
  have hsum5 : d * (k + 1) ^ 2 * (2 * W + 1) +
      d * Fintype.card (LocModel B k) * (6 * b + 2) +
      Fintype.card (pairOf t) * H * (k + 1) * Fintype.card (LocModel B k) * (14 * b) +
      Fintype.card (pairOf t) * (k + 1) * H * (13 * b) +
      Fintype.card (pairOf t) * (k + 1) ^ 2 * (10 * b + 1) ≤ 5 * Bnd := by
    have h12345 := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hterm1 hterm2) hterm3) hterm4) hterm5
    calc _ ≤ Bnd + Bnd + Bnd + Bnd + Bnd := h12345
      _ = 5 * Bnd := by ring
  calc _ ≤ 5 * Bnd := hsum5
    _ ≤ T ^ 40 * Bnd := Nat.mul_le_mul_right Bnd h5_le
    _ = T ^ 50 * X ^ (40 * (k + 1)) := by dsimp [Bnd]; ring
    _ ≤ T ^ 50 * X ^ (50 * (k + 1)) := Nat.mul_le_mul_left _ (hX_pow _ _ (by omega))

lemma gate_size_bound {t k s : ℕ} (ht : 2 ≤ t) (hk : 0 < k) (hs : 3 ≤ s) :
    let B := 128 * (k + 1) * s
    let H := 256 * (k + 1) * s * (1 + Nat.log 2 t)
    let M := 600 * (k + 1) * s ^ 2 * (1 + Nat.log 2 B)
    let d := H * M
    let W := k * (2 * t + 2) + 1
    let b := Nat.log 2 d + 2
    d * (k + 1) ^ 2 * (2 * W + 1) +
    d * Fintype.card (LocModel B k) * (6 * b + 2) +
    Fintype.card (pairOf t) * H * (k + 1) * Fintype.card (LocModel B k) * (14 * b) +
    Fintype.card (pairOf t) * (k + 1) * H * (13 * b) +
    Fintype.card (pairOf t) * (k + 1) ^ 2 * (10 * b + 1) ≤
      (t + 2) ^ 50 * (k + s + 2) ^ (50 * (k + 1)) :=
  gate_size_bound_aux ht hk hs rfl rfl

end CircuitBuilder

end PEqualNP.Outside.L_pcx_469_aux

theorem PEqualNP.Outside.L_pcx_469 : (∃ C A : ℕ, 0 < C ∧ ∀ t k s : ℕ, 2 ≤ t → 0 < k → 3 ≤ s →
  let T := Fin t
  let V := Option (T × Bool)
  let Pair := {p : T × T // p.1 < p.2}
  let E := Fin 3 × T
  let Mask := T → Fin 3
  let tail := fun e : E => if e.1 = 0 then some (e.2,false) else (none : V)
  let head := fun e : E => some (e.2,decide (e.1 ≠ 1))
  let weight := fun (g : Option Pair) (e : E) (diff : Bool) =>
    if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
    if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
      (if diff then 1 else 3) else (2 : ℕ)
  let obs := fun (g : Option Pair) (p : Mask) =>
    ∑ x : V → Bool, if (∀ i : T, p i = 0 ∨ p i = (if x (some (i,false)) then 2 else 1)) ∧
      (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card = 2*t then
      ∏ e : E, weight g e (xor (x (tail e)) (x (head e))) else 0

  let Model := Fin k → Option Pair
  let read := fun (G : Model) (p : Mask) => ∏ l, obs (G l) p
  let W := k*(2*t+2)+1
  ∃ (d : ℕ) (batch : Fin d → Mask) (g : PEqualNP.CircuitLowerBounds.Circuit)
    (out : Pair → Fin (k+1) → Fin (2+d*(W+1)+g.size)),
    0 < d ∧ d ≤ C*(k+1)^2*s^3*(1+Nat.log 2 ((k+1)*s))*(1+Nat.log 2 t) ∧
    g.size ≤ (t+2)^A*(k+s+2)^(A*(k+1)) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+d*(W+1)) g ∧
    (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1)) ∧
    ∀ (G : Model), (∀ i, read G (batch i) < 2^W) ∧
      ∀ (y : Fin d → Option ℕ),
        let lost := (Finset.univ.filter (fun i => y i = none)).card
        let err := (Finset.univ.filter (fun i => y i ≠ none ∧ y i ≠ some (read G (batch i)))).card
        9*s*(2*err+lost) < (4*s-9)*d →
        let bits := (List.ofFn (fun i : Fin d => (y i).isSome ::
          List.ofFn (fun j : Fin W => ((y i).getD 0).testBit j.val))).flatten
        ∀ (e : Pair) (m : Fin (k+1)), (g.wires ([false,true] ++ bits)).getD (out e m).val false =
          decide ((Finset.univ.filter (fun l => G l = some e)).card = m.val)) := by
  open PEqualNP.Outside.L_pcx_469_aux in
  refine ⟨1228800, 50, by omega, ?_⟩
  intro t k s ht hk hs
  dsimp only
  set B := 128 * (k + 1) * s
  set H := 256 * (k + 1) * s * (1 + Nat.log 2 t)
  set M := 600 * (k + 1) * s ^ 2 * (1 + Nat.log 2 B)
  set d := H * M
  set W := k * (2 * t + 2) + 1
  have hB2 : 2 ≤ B := by dsimp [B]; nlinarith
  have hHpos : 0 < H := by positivity
  have hMpos : 0 < M := by positivity
  have hdpos : 0 < d := Nat.mul_pos hHpos hMpos
  obtain ⟨h, hGoodH⟩ := exists_good_hashes ht hk hs
  obtain ⟨q, hGoodM⟩ := exists_good_masks hB2 hk hs
  let batch : Fin d → (Fin t → Fin 3) := fun i =>
    let p := finProdFinEquiv.symm i; q p.2 ∘ h p.1
  let dec := buildDecoder (t := t) (B := B) (k := k) (H := H) (M := M) h q
  obtain ⟨hval, hlen, hout_lt, heval⟩ := buildDecoder_spec ht hHpos hMpos h q
  let g : PEqualNP.CircuitLowerBounds.Circuit := ⟨dec.1, 0⟩
  let out : pairOf t → Fin (k + 1) → Fin (2 + d * (W + 1) + g.size) :=
    fun e m => ⟨dec.2 e m, hout_lt e m⟩
  refine ⟨d, batch, g, out, hdpos, ?_, ?_, hval.1, hval.2, ?_⟩
  · have hlogB : 1 + Nat.log 2 B ≤ 8 * (1 + Nat.log 2 ((k + 1) * s)) := by
      have h1 : (k + 1) * s < 2 ^ (Nat.log 2 ((k + 1) * s) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) ((k + 1) * s)
      have hB_lt : B < 2 ^ (Nat.log 2 ((k + 1) * s) + 8) := by
        calc B = 128 * ((k + 1) * s) := by dsimp [B]; ring
          _ < 128 * 2 ^ (Nat.log 2 ((k + 1) * s) + 1) := Nat.mul_lt_mul_of_pos_left h1 (by omega)
          _ = 2 ^ 7 * 2 ^ (Nat.log 2 ((k + 1) * s) + 1) := by norm_num
          _ = 2 ^ (Nat.log 2 ((k + 1) * s) + 8) := by rw [← pow_add]; congr 1; omega
      have hlog_lt : Nat.log 2 B < Nat.log 2 ((k + 1) * s) + 8 :=
        Nat.log_lt_of_lt_pow (by positivity) hB_lt
      omega
    calc d = (256 * (k + 1) * s * (1 + Nat.log 2 t)) * (600 * (k + 1) * s ^ 2 * (1 + Nat.log 2 B)) := rfl
      _ ≤ (256 * (k + 1) * s * (1 + Nat.log 2 t)) * (600 * (k + 1) * s ^ 2 * (8 * (1 + Nat.log 2 ((k + 1) * s)))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hlogB)
      _ = 1228800 * (k + 1) ^ 2 * s ^ 3 * (1 + Nat.log 2 ((k + 1) * s)) * (1 + Nat.log 2 t) := by ring
  · exact hlen.trans (gate_size_bound ht hk hs)
  · intro G
    refine ⟨fun i => readFn_lt ht G (batch i), ?_⟩
    intro y hnoise e m
    let yT : Fin d → Option ℕ := fun i => (y i).map (fun v => v % 2 ^ W)
    have hlost_eq : (Finset.univ.filter (fun i : Fin d => yT i = none)).card =
        (Finset.univ.filter (fun i : Fin d => y i = none)).card := by
      congr 1; ext i; simp [yT]
    have herr_le : (Finset.univ.filter (fun i : Fin d => yT i ≠ none ∧ yT i ≠ some (readFn G (batch i)))).card ≤
        (Finset.univ.filter (fun i : Fin d => y i ≠ none ∧ y i ≠ some (readFn G (batch i)))).card := by
      refine Finset.card_le_card (fun i hi => ?_)
      have ⟨h1, h2⟩ := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro hnone; exact h1 (by simp [yT, hnone])
      · intro hsome
        apply h2
        simp only [yT, hsome, Option.map_some, Option.some.injEq]
        exact Nat.mod_eq_of_lt (readFn_lt ht G (batch i))
    have hnoiseT : 9 * s * (2 * (Finset.univ.filter (fun i : Fin d =>
        yT i ≠ none ∧ yT i ≠ some (readFn G (batch i)))).card +
        (Finset.univ.filter (fun i : Fin d => yT i = none)).card) < (4 * s - 9) * d := by
      rw [hlost_eq]
      have h1 : 9 * s * (2 * (Finset.univ.filter (fun i : Fin d =>
          yT i ≠ none ∧ yT i ≠ some (readFn G (batch i)))).card +
          (Finset.univ.filter (fun i : Fin d => y i = none)).card) ≤
          9 * s * (2 * (Finset.univ.filter (fun i : Fin d =>
          y i ≠ none ∧ y i ≠ some (readFn G (batch i)))).card +
          (Finset.univ.filter (fun i : Fin d => y i = none)).card) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 herr_le) _)
      exact lt_of_le_of_lt h1 hnoise
    have hev := heval y e m
    change (g.wires ([false, true] ++ bitsOf (W := W) y)).getD (out e m).val false =
      decide ((Finset.univ.filter (fun l : Fin k => G l = some e)).card = m.val)
    change evalW dec.1 ([false, true] ++ bitsOf (W := W) y) (dec.2 e m) = _
    rw [hev]
    set mstar := (Finset.univ.filter (fun l : Fin k => G l = some e)).card
    have hmstar_lt : mstar < k + 1 := Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (by simp))
    have huniq : ∀ m' : Fin (k + 1), m'.val ≠ mstar →
        totalCostOf (t := t) (k := k) h q yT e mstar < totalCostOf (t := t) (k := k) h q yT e m'.val :=
      fun m' hne => decoding_unique ht hs h q hGoodH hGoodM G yT hnoiseT e m'.val hne
    by_cases hm : mstar = m.val
    · simp only [hm, decide_true]
      rw [decide_eq_true_eq]
      intro m' hne
      have hne' : m'.val ≠ mstar := by intro h'; apply hne; ext; omega
      simpa [hm] using huniq m' hne'
    · simp only [hm, decide_false]
      rw [decide_eq_false_iff_not]
      intro hall
      have h1 : totalCostOf (t := t) (k := k) h q yT e m.val < totalCostOf (t := t) (k := k) h q yT e mstar :=
        hall ⟨mstar, hmstar_lt⟩ (fun h' => hm (congrArg Fin.val h'))
      have h2 := huniq m (Ne.symm hm)
      omega
