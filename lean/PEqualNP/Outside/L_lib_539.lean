import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_539

open Finset

def Lf (l r : ℕ) (c : ℕ → Bool) (α : Bool) (i : ℕ) (a : Bool) : Prop :=
  (i = l ∧ (l = 0 → a = α)) ∨ (l < i ∧ i < r ∧ a = c i)

def Rf (h l r : ℕ) (c : ℕ → Bool) (β : Bool) (j : ℕ) (b : Bool) : Prop :=
  (j = r ∧ (r = h → b = β)) ∨ (l < j ∧ j < r ∧ b ≠ c j)

instance (l r : ℕ) (c : ℕ → Bool) (α : Bool) (i : ℕ) (a : Bool) : Decidable (Lf l r c α i a) := by
  unfold Lf; infer_instance

instance (h l r : ℕ) (c : ℕ → Bool) (β : Bool) (j : ℕ) (b : Bool) : Decidable (Rf h l r c β j b) := by
  unfold Rf; infer_instance

def cf {h : ℕ} (c : Fin (h + 1) → Bool) (k : ℕ) : Bool :=
  if hk : k < h + 1 then c ⟨k, hk⟩ else false

abbrev Idx (h : ℕ) : Type := Σ _ : ℕ × ℕ, (Fin (h + 1) → Bool) × (Bool × Bool)

def Ps (h : ℕ) : Finset (ℕ × ℕ) := (range (h + 1) ×ˢ range (h + 1)).filter fun x => x.1 < x.2

def Cs (h : ℕ) (x : ℕ × ℕ) : Finset (Fin (h + 1) → Bool) :=
  Fintype.piFinset fun k : Fin (h + 1) => if x.1 < k.val ∧ k.val < x.2 then univ else {false}

def AB (h : ℕ) (same : Prop) [Decidable same] (x : ℕ × ℕ) : Finset (Bool × Bool) :=
  ((if x.1 = 0 then univ else {false}) ×ˢ (if x.2 = h then univ else {false})).filter
    fun ab => same → x.1 = 0 → x.2 = h → ab.1 = ab.2

def Qs (h : ℕ) (same : Prop) [Decidable same] : Finset (Idx h) :=
  (Ps h).sigma fun x => Cs h x ×ˢ AB h same x

def keyq {h : ℕ} (q : Idx h) : Finset (Fin h × (Bool × Bool)) :=
  univ.filter fun e => Lf q.1.1 q.1.2 (cf q.2.1) q.2.2.1 e.1.val e.2.1 ∧
    Rf h q.1.1 q.1.2 (cf q.2.1) q.2.2.2 (e.1.val + 1) e.2.2

def gd {h p : ℕ} (s t : Fin p) (q : Idx h) :
    Finset (PEqualNP.ProofComplexity.Literal (Sum (Fin p) (Fin h × (Bool × Bool)))) :=
  (if q.1.1 = 0 then {(Sum.inl s, !q.2.2.1)} else ∅) ∪
    (if q.1.2 = h then {(Sum.inl t, !q.2.2.2)} else ∅)

def cl {h p : ℕ} (s t : Fin p) (q : Idx h) :
    PEqualNP.ProofComplexity.Clause (Sum (Fin p) (Fin h × (Bool × Bool))) :=
  (keyq q).image (fun e => (Sum.inr e, true)) ∪ gd s t q

lemma mem_Qs {h : ℕ} {same : Prop} [Decidable same] {q : Idx h} (hq : q ∈ Qs h same) :
    q.1.1 < q.1.2 ∧ q.1.2 ≤ h ∧ (∀ k : Fin (h + 1), ¬(q.1.1 < k.val ∧ k.val < q.1.2) → q.2.1 k = false) ∧
    (q.1.1 ≠ 0 → q.2.2.1 = false) ∧ (q.1.2 ≠ h → q.2.2.2 = false) ∧
    (same → q.1.1 = 0 → q.1.2 = h → q.2.2.1 = q.2.2.2) := by
  simp only [Qs, Ps, Cs, AB, mem_sigma, mem_filter, mem_product, mem_range, Fintype.mem_piFinset] at hq
  obtain ⟨⟨⟨_, h2⟩, h3⟩, hc, ⟨ha, hb⟩, hs⟩ := hq
  refine ⟨h3, by omega, ?_, ?_, ?_, hs⟩
  · intro k hk
    simpa [if_neg hk] using hc k
  · intro h0
    simpa [if_neg h0] using ha
  · intro h0
    simpa [if_neg h0] using hb

lemma layer {h l r : ℕ} {c : ℕ → Bool} {α β : Bool} {i : ℕ} (h1 : l ≤ i) (h2 : i < r) :
    ∃ a b, Lf l r c α i a ∧ Rf h l r c β (i + 1) b := by
  refine ⟨if i = l then α else c i, if i + 1 = r then β else !(c (i + 1)), ?_, ?_⟩
  · by_cases hi : i = l
    · exact Or.inl ⟨hi, fun _ => by simp [hi]⟩
    · exact Or.inr ⟨by omega, h2, by simp [hi]⟩
  · by_cases hi : i + 1 = r
    · exact Or.inl ⟨hi, fun _ => by simp [hi]⟩
    · exact Or.inr ⟨by omega, by omega, by simp [hi]⟩

lemma range_of {h l r : ℕ} {c : ℕ → Bool} {α β : Bool} {i : ℕ} {a b : Bool} (hlr : l < r)
    (h1 : Lf l r c α i a) (h2 : Rf h l r c β (i + 1) b) : l ≤ i ∧ i < r := by
  unfold Lf at h1
  unfold Rf at h2
  omega

lemma key_inj {h : ℕ} {same : Prop} [Decidable same] {q q' : Idx h} (hq : q ∈ Qs h same)
    (hq' : q' ∈ Qs h same) (hk : keyq q = keyq q') : q = q' := by
  obtain ⟨hlr, hr, hc, ha, hb, _⟩ := mem_Qs hq
  obtain ⟨hlr', hr', hc', ha', hb', _⟩ := mem_Qs hq'
  obtain ⟨⟨l, r⟩, c, α, β⟩ := q
  obtain ⟨⟨l', r'⟩, c', α', β'⟩ := q'
  dsimp only at *
  have tr : ∀ i : ℕ, i < h → ∀ a b, (Lf l r (cf c) α i a ∧ Rf h l r (cf c) β (i + 1) b) ↔
      (Lf l' r' (cf c') α' i a ∧ Rf h l' r' (cf c') β' (i + 1) b) := by
    intro i hi a b
    have := Finset.ext_iff.mp hk (⟨i, hi⟩, (a, b))
    simpa [keyq] using this
  have lay : ∀ i, (l ≤ i ∧ i < r) ↔ (l' ≤ i ∧ i < r') := by
    intro i
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨a, b, hab⟩ := layer (h := h) (c := cf c) (α := α) (β := β) h1 h2
      have := (tr i (by omega) a b).mp hab
      exact range_of hlr' this.1 this.2
    · rintro ⟨h1, h2⟩
      obtain ⟨a, b, hab⟩ := layer (h := h) (c := cf c') (α := α') (β := β') h1 h2
      have := (tr i (by omega) a b).mpr hab
      exact range_of hlr this.1 this.2
  have el : l = l' := by
    have x := (lay l).mp ⟨le_rfl, hlr⟩
    have y := (lay l').mpr ⟨le_rfl, hlr'⟩
    omega
  subst el
  have er : r = r' := by
    have x := (lay (r - 1)).mp ⟨by omega, by omega⟩
    have y := (lay (r' - 1)).mpr ⟨by omega, by omega⟩
    omega
  subst er
  have ec : c = c' := by
    funext k
    by_cases hin : l < k.val ∧ k.val < r
    · obtain ⟨a, b, hab⟩ := layer (h := h) (c := cf c) (α := α) (β := β) (le_of_lt hin.1) hin.2
      have hab' := (tr k.val (by omega) a b).mp hab
      have e1 : a = cf c k.val := by
        rcases hab.1 with h1 | h1
        · omega
        · exact h1.2.2
      have e2 : a = cf c' k.val := by
        rcases hab'.1 with h1 | h1
        · omega
        · exact h1.2.2
      have e3 := e1.symm.trans e2
      simpa [cf, k.isLt] using e3
    · rw [hc k hin, hc' k hin]
  subst ec
  have eα : α = α' := by
    by_cases h0 : l = 0
    · obtain ⟨a, b, hab⟩ := layer (h := h) (c := cf c) (α := α) (β := β) le_rfl hlr
      have hab' := (tr l (by omega) a b).mp hab
      have e1 : a = α := by
        rcases hab.1 with h1 | h1
        · exact h1.2 h0
        · omega
      have e2 : a = α' := by
        rcases hab'.1 with h1 | h1
        · exact h1.2 h0
        · omega
      exact e1.symm.trans e2
    · rw [ha h0, ha' h0]
  have eβ : β = β' := by
    by_cases h0 : r = h
    · obtain ⟨a, b, hab⟩ := layer (h := h) (c := cf c) (α := α) (β := β) (l := l) (r := r) (i := r - 1)
        (by omega) (by omega)
      have hab' := (tr (r - 1) (by omega) a b).mp hab
      have e1 : b = β := by
        rcases hab.2 with h1 | h1
        · exact h1.2 h0
        · omega
      have e2 : b = β' := by
        rcases hab'.2 with h1 | h1
        · exact h1.2 h0
        · omega
      exact e1.symm.trans e2
    · rw [hb h0, hb' h0]
  subst eα eβ
  rfl

lemma key_cl {h p : ℕ} (s t : Fin p) (q : Idx h) :
    (univ.filter fun e => (Sum.inr e, true) ∈ cl s t q) = keyq q := by
  ext e
  have x : (Sum.inr e, true) ∈ cl s t q ↔ e ∈ keyq q := by
    unfold cl gd
    rw [mem_union, mem_union, mem_image]
    constructor
    · rintro (⟨e', he, h2⟩ | h2 | h2)
      · simp only [Prod.mk.injEq, Sum.inr.injEq, and_true] at h2
        exact h2 ▸ he
      · split_ifs at h2 <;> simp at h2
      · split_ifs at h2 <;> simp at h2
    · intro he
      exact Or.inl ⟨e, he, rfl⟩
  rw [mem_filter]
  exact ⟨fun h => x.mp h.2, fun h => ⟨mem_univ _, x.mpr h⟩⟩

def nl (l : ℕ) : ℕ := if l = 0 then 1 else 2

def nr (h r : ℕ) : ℕ := if r = h then 1 else 2

def ks (h l r : ℕ) : ℕ := if r = l + 1 then nl l * nr h r else nl l + nr h r + (r - l - 2)

def gs (h : ℕ) (same : Prop) [Decidable same] (l r : ℕ) : ℕ :=
  if l = 0 ∧ r = h then (if same then 1 else 2)
  else (if l = 0 then 1 else 0) + (if r = h then 1 else 0)

def ws (h : ℕ) (same : Prop) [Decidable same] (l r : ℕ) : ℕ :=
  2 ^ (r - l - 1) *
    (if l = 0 ∧ r = h then (if same then 2 else 4)
     else (if l = 0 then 2 else 1) * (if r = h then 2 else 1))

lemma cardL (l r : ℕ) (c : ℕ → Bool) (α : Bool) (i : ℕ) :
    (univ.filter fun a => Lf l r c α i a).card =
      if i = l then nl l else if l < i ∧ i < r then 1 else 0 := by
  unfold nl
  by_cases h1 : i = l
  · subst h1
    by_cases h0 : i = 0
    · have : (univ.filter fun a => Lf i r c α i a) = {α} := by
        ext a; simp [Lf, h0]
      rw [this]; simp [h0]
    · have : (univ.filter fun a => Lf i r c α i a) = univ := by
        ext a; simp [Lf, h0]
      rw [this]; simp [h0]
  · by_cases h2 : l < i ∧ i < r
    · have : (univ.filter fun a => Lf l r c α i a) = {c i} := by
        ext a; simp [Lf, h1, h2.1, h2.2]
      rw [this]; simp [h1, h2]
    · have : (univ.filter fun a => Lf l r c α i a) = ∅ := by
        rw [filter_eq_empty_iff]
        intro a _ ha
        unfold Lf at ha
        rcases ha with x | x
        · exact h1 x.1
        · exact h2 ⟨x.1, x.2.1⟩
      rw [this]; simp [h1, h2]

lemma cardR (h l r : ℕ) (c : ℕ → Bool) (β : Bool) (j : ℕ) :
    (univ.filter fun b => Rf h l r c β j b).card =
      if j = r then nr h r else if l < j ∧ j < r then 1 else 0 := by
  unfold nr
  by_cases h1 : j = r
  · subst h1
    by_cases h0 : j = h
    · have : (univ.filter fun b => Rf h l j c β j b) = {β} := by
        ext a; simp [Rf, h0]
      rw [this]; simp [h0]
    · have : (univ.filter fun b => Rf h l j c β j b) = univ := by
        ext a; simp [Rf, h0]
      rw [this]; simp [h0]
  · by_cases h2 : l < j ∧ j < r
    · have : (univ.filter fun b => Rf h l r c β j b) = {!(c j)} := by
        ext a
        have x : a ≠ c j ↔ a = !(c j) := by cases a <;> cases c j <;> decide
        simp [Rf, h1, h2.1, h2.2, x]
      rw [this]; simp [h1, h2]
    · have : (univ.filter fun b => Rf h l r c β j b) = ∅ := by
        rw [filter_eq_empty_iff]
        intro a _ ha
        unfold Rf at ha
        rcases ha with x | x
        · exact h1 x.1
        · exact h2 ⟨x.1, x.2.1⟩
      rw [this]; simp [h1, h2]

lemma card_key {h : ℕ} (q : Idx h) (hlr : q.1.1 < q.1.2) (hr : q.1.2 ≤ h) :
    (keyq q).card = ks h q.1.1 q.1.2 := by
  obtain ⟨⟨l, r⟩, c, α, β⟩ := q
  dsimp only at *
  have e1 : (keyq (h := h) ⟨(l, r), c, α, β⟩).card =
      ∑ i : Fin h, (univ.filter fun a => Lf l r (cf c) α i.val a).card *
        (univ.filter fun b => Rf h l r (cf c) β (i.val + 1) b).card := by
    unfold keyq
    rw [card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [← card_product, ← filter_product, univ_product_univ, card_filter]
  rw [e1]
  simp only [cardL, cardR]
  rw [Fin.sum_univ_eq_sum_range (fun i => (if i = l then nl l else if l < i ∧ i < r then 1 else 0) *
    (if i + 1 = r then nr h r else if l < i + 1 ∧ i + 1 < r then 1 else 0))]
  rw [← sum_subset (s₁ := Ico l r)]
  · unfold ks
    by_cases h1 : r = l + 1
    · subst h1
      simp
    · rw [if_neg h1]
      obtain ⟨n, rfl⟩ : ∃ n, r = l + n + 2 := ⟨r - l - 2, by omega⟩
      rw [sum_eq_sum_Ico_succ_bot (by omega), show l + n + 2 = (l + n + 1) + 1 by omega,
        sum_Ico_succ_top (by omega)]
      have mid : ∀ i ∈ Ico (l + 1) (l + n + 1),
          (if i = l then nl l else if l < i ∧ i < l + n + 1 + 1 then 1 else 0) *
            (if i + 1 = l + n + 1 + 1 then nr h (l + n + 1 + 1)
              else if l < i + 1 ∧ i + 1 < l + n + 1 + 1 then 1 else 0) = 1 := by
        intro i hi
        rw [mem_Ico] at hi
        rw [if_neg (show i ≠ l by omega), if_pos (show l < i ∧ i < l + n + 1 + 1 by omega),
          if_neg (show i + 1 ≠ l + n + 1 + 1 by omega),
          if_pos (show l < i + 1 ∧ i + 1 < l + n + 1 + 1 by omega)]
      rw [sum_congr rfl mid]
      rw [if_pos rfl, if_neg (show l + 1 ≠ l + n + 1 + 1 by omega),
        if_pos (show l < l + 1 ∧ l + 1 < l + n + 1 + 1 by omega),
        if_neg (show l + n + 1 ≠ l by omega),
        if_pos (show l < l + n + 1 ∧ l + n + 1 < l + n + 1 + 1 by omega), if_pos rfl]
      simp
      omega
  · intro i hi
    rw [mem_Ico] at hi
    rw [mem_range]; omega
  · intro i _ hi
    rw [mem_Ico] at hi
    rw [if_neg (show ¬(l < i ∧ i < r) by omega)]
    by_cases x : i = l
    · exact absurd (show l ≤ i ∧ i < r by omega) hi
    · rw [if_neg x, zero_mul]

lemma card_cl {h p : ℕ} (s t : Fin p) (q : Idx h) (hq : q ∈ Qs h (s = t)) :
    (cl s t q).card = ks h q.1.1 q.1.2 + gs h (s = t) q.1.1 q.1.2 := by
  obtain ⟨hlr, hr, _, _, _, hs⟩ := mem_Qs hq
  unfold cl
  rw [card_union_of_disjoint, card_image_of_injective, card_key q hlr hr]
  · congr 1
    unfold gd gs
    by_cases h0 : q.1.1 = 0
    · by_cases h1 : q.1.2 = h
      · by_cases e : s = t
        · rw [if_pos h0, if_pos h1, if_pos ⟨h0, h1⟩, if_pos e, hs e h0 h1, e, union_self, card_singleton]
        · rw [if_pos h0, if_pos h1, if_pos ⟨h0, h1⟩, if_neg e, card_union_of_disjoint, card_singleton,
            card_singleton]
          simp [Ne.symm e, e]
      · simp [h0, h1]
    · by_cases h1 : q.1.2 = h
      · simp [h0, h1]
      · simp [h0, h1]
  · intro a b hab
    simpa using hab
  · rw [disjoint_left]
    intro x hx hg
    obtain ⟨e, _, rfl⟩ := mem_image.mp hx
    unfold gd at hg
    rw [mem_union] at hg
    rcases hg with hg | hg <;> split_ifs at hg <;> simp at hg

lemma card_Cs {h : ℕ} (x : ℕ × ℕ) (hx : x.2 ≤ h) : (Cs h x).card = 2 ^ (x.2 - x.1 - 1) := by
  unfold Cs
  rw [Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_univ, Fintype.card_bool, card_singleton]
  rw [prod_ite, prod_const, prod_const_one, mul_one]
  congr 1
  have : (univ.filter fun k : Fin (h + 1) => x.1 < k.val ∧ k.val < x.2).map Fin.valEmbedding =
      Ioo x.1 x.2 := by
    ext k
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ioo]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hk; exact ⟨⟨k, by omega⟩, hk, rfl⟩
  rw [← card_map Fin.valEmbedding, this, Nat.card_Ioo]

lemma card_AB (h : ℕ) (same : Prop) [Decidable same] (x : ℕ × ℕ) :
    (AB h same x).card =
      if x.1 = 0 ∧ x.2 = h then (if same then 2 else 4)
      else (if x.1 = 0 then 2 else 1) * (if x.2 = h then 2 else 1) := by
  unfold AB
  by_cases h0 : x.1 = 0 <;> by_cases h1 : x.2 = h <;> by_cases e : same <;>
    simp [h0, h1, e] <;> decide

lemma sum_Qs (h : ℕ) (same : Prop) [Decidable same] (f : ℕ → ℕ → ℕ) :
    ∑ q ∈ Qs h same, f q.1.1 q.1.2 =
      ∑ r ∈ range (h + 1), ∑ l ∈ range r, ws h same l r * f l r := by
  unfold Qs
  rw [sum_sigma]
  have : ∀ x ∈ Ps h, ∑ _y ∈ Cs h x ×ˢ AB h same x, f x.1 x.2 = ws h same x.1 x.2 * f x.1 x.2 := by
    intro x hx
    simp only [Ps, mem_filter, mem_product, mem_range] at hx
    rw [sum_const, card_product, card_Cs x (by omega), card_AB, smul_eq_mul]
    rfl
  rw [sum_congr rfl this]
  unfold Ps
  rw [sum_filter, sum_product_right]
  refine sum_congr rfl fun r hr => ?_
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext l
  simp only [mem_filter, mem_range] at hr ⊢
  omega

lemma split_sum (m : ℕ) (f : ℕ → ℕ → ℕ) (A I B : ℕ → ℕ)
    (hA : ∀ j < m, f 0 (j + 1) = A j)
    (hI : ∀ j < m, ∀ k < j, f (k + 1) (j + 1) = I (j - 1 - k))
    (hB : ∀ k < m, f (k + 1) (m + 1) = B (m - 1 - k)) :
    ∑ r ∈ range (m + 1 + 1), ∑ l ∈ range r, f l r =
      ∑ j ∈ range m, A j + ∑ j ∈ range m, ∑ k ∈ range j, I k + ∑ k ∈ range m, B k +
        f 0 (m + 1) := by
  rw [sum_range_succ, sum_range_succ' (fun r => ∑ l ∈ range r, f l r),
    sum_range_succ' (fun l => f l (m + 1))]
  have e1 : ∑ j ∈ range m, ∑ l ∈ range (j + 1), f l (j + 1) =
      ∑ j ∈ range m, A j + ∑ j ∈ range m, ∑ k ∈ range j, I k := by
    have : ∀ j ∈ range m, ∑ l ∈ range (j + 1), f l (j + 1) = A j + ∑ k ∈ range j, I k := by
      intro j hj
      rw [mem_range] at hj
      rw [sum_range_succ', hA j hj, add_comm, ← sum_range_reflect I j]
      congr 1
      exact sum_congr rfl fun k hk => hI j hj k (mem_range.mp hk)
    rw [sum_congr rfl this, sum_add_distrib]
  have e2 : ∑ k ∈ range m, f (k + 1) (m + 1) = ∑ k ∈ range m, B k := by
    rw [← sum_range_reflect B m]
    exact sum_congr rfl fun k hk => hB k (mem_range.mp hk)
  rw [e1, e2, range_zero, sum_empty]
  ring

lemma pow_sum (m : ℕ) : ∑ k ∈ range m, 2 ^ k + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, pow_succ]; omega

lemma count_sum (m : ℕ) : ∑ j ∈ range m, 2 ^ j * 2 + ∑ j ∈ range m, ∑ k ∈ range j, 2 ^ k +
    ∑ k ∈ range m, 2 ^ k * 2 + m + 5 = 5 * 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have x := pow_sum m
    rw [sum_range_succ, sum_range_succ (fun j => ∑ k ∈ range j, 2 ^ k), pow_succ]
    omega

lemma side_sum (m : ℕ) : ∑ j ∈ range m, 2 ^ j * 2 * (j + 3) + 2 = 2 * ((m + 1) * 2 ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, pow_succ]
    linear_combination ih

def In (k : ℕ) : ℕ := 2 ^ k * (k + 3 + if k = 0 then 1 else 0)

lemma in_sum (n : ℕ) : ∑ k ∈ range (n + 1), In k = (n + 2) * 2 ^ (n + 1) := by
  induction n with
  | zero => simp [In]
  | succ n ih =>
    rw [sum_range_succ, ih]
    unfold In
    rw [if_neg (by omega), pow_succ 2 (n + 1)]
    ring

lemma in_sum2 (n : ℕ) : ∑ j ∈ range (n + 1), ∑ k ∈ range j, In k = n * 2 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, in_sum, pow_succ 2 (n + 1)]
    ring

lemma count_Q (m : ℕ) (same : Prop) [Decidable same] :
    (Qs (m + 1) same).card + m + 5 = (if same then 7 else 9) * 2 ^ m := by
  have e : (Qs (m + 1) same).card = ∑ r ∈ range (m + 1 + 1), ∑ l ∈ range r, ws (m + 1) same l r * 1 := by
    rw [card_eq_sum_ones]
    exact sum_Qs (m + 1) same (fun _ _ => 1)
  rw [e, split_sum m (fun l r => ws (m + 1) same l r * 1) (fun j => 2 ^ j * 2) (fun k => 2 ^ k)
    (fun k => 2 ^ k * 2)]
  · have z : ws (m + 1) same 0 (m + 1) * 1 = 2 ^ m * (if same then 2 else 4) := by
      simp [ws]
    have c := count_sum m
    rw [z]
    split_ifs <;> omega
  · intro j hj
    simp [ws, show j ≠ m by omega]
  · intro j hj k hk
    simp only [ws]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show j + 1 - (k + 1) - 1 = j - 1 - k by omega]
    simp
  · intro k hk
    simp only [ws]
    rw [show m + 1 - (k + 1) - 1 = m - 1 - k by omega]
    simp [show k ≠ m by omega]

lemma cost_Q (m : ℕ) (same : Prop) [Decidable same] :
    ∑ q ∈ Qs (m + 1) same, (ks (m + 1) q.1.1 q.1.2 + gs (m + 1) same q.1.1 q.1.2) =
      if m + 1 = 1 then (if same then 4 else 12)
      else (if same then 7 * (m + 1) else 9 * (m + 1) + 6) * 2 ^ (m + 1 - 1) - 4 := by
  rw [sum_Qs (m + 1) same (fun l r => ks (m + 1) l r + gs (m + 1) same l r),
    split_sum m (fun l r => ws (m + 1) same l r * (ks (m + 1) l r + gs (m + 1) same l r))
      (fun j => 2 ^ j * 2 * (j + 3)) In (fun k => 2 ^ k * 2 * (k + 3))]
  · have z : ws (m + 1) same 0 (m + 1) * (ks (m + 1) 0 (m + 1) + gs (m + 1) same 0 (m + 1)) =
        2 ^ m * (if same then 2 else 4) * (m + 1 + if same then 1 else 2) := by
      have k1 : ks (m + 1) 0 (m + 1) = m + 1 := by
        unfold ks nl nr
        by_cases h : m = 0
        · simp [h]
        · rw [if_neg (by omega), if_pos rfl, if_pos rfl]; omega
      rw [k1]
      simp [ws, gs]
    rw [z]
    cases m with
    | zero => by_cases h : same <;> simp [h]
    | succ n =>
      have a := side_sum (n + 1)
      have b := in_sum2 n
      rw [b, if_neg (show n + 1 + 1 ≠ 1 by omega), show n + 1 + 1 - 1 = n + 1 by omega]
      symm
      apply Nat.sub_eq_of_eq_add
      by_cases h : same
      · simp only [if_pos h]
        nlinarith [a]
      · simp only [if_neg h]
        nlinarith [a]
  · intro j hj
    have k1 : ks (m + 1) 0 (j + 1) + gs (m + 1) same 0 (j + 1) = j + 3 := by
      unfold ks gs nl nr
      by_cases h : j = 0
      · subst h
        simp [show (1 : ℕ) ≠ m + 1 by omega, show m ≠ 0 by omega]
      · rw [if_neg (show j + 1 ≠ 0 + 1 by omega), if_pos rfl, if_neg (show j + 1 ≠ m + 1 by omega),
          if_neg (by omega), if_pos rfl, if_neg (show j + 1 ≠ m + 1 by omega)]
        omega
    rw [k1]
    simp [ws, show j ≠ m by omega]
  · intro j hj k hk
    have k1 : ks (m + 1) (k + 1) (j + 1) + gs (m + 1) same (k + 1) (j + 1) =
        j - 1 - k + 3 + if j - 1 - k = 0 then 1 else 0 := by
      unfold ks gs nl nr
      rw [if_neg (show k + 1 ≠ 0 by omega), if_neg (show j + 1 ≠ m + 1 by omega),
        if_neg (show ¬(k + 1 = 0 ∧ j + 1 = m + 1) by omega), if_neg (show k + 1 ≠ 0 by omega)]
      split_ifs <;> omega
    have w1 : ws (m + 1) same (k + 1) (j + 1) = 2 ^ (j - 1 - k) := by
      simp only [ws]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        show j + 1 - (k + 1) - 1 = j - 1 - k by omega]
      simp
    rw [k1, w1]
    rfl
  · intro k hk
    have k1 : ks (m + 1) (k + 1) (m + 1) + gs (m + 1) same (k + 1) (m + 1) = m - 1 - k + 3 := by
      unfold ks gs nl nr
      rw [if_neg (show k + 1 ≠ 0 by omega), if_pos rfl,
        if_neg (show ¬(k + 1 = 0 ∧ m + 1 = m + 1) by omega), if_neg (show k + 1 ≠ 0 by omega)]
      split_ifs <;> omega
    have w1 : ws (m + 1) same (k + 1) (m + 1) = 2 ^ (m - 1 - k) * 2 := by
      simp only [ws]
      rw [show m + 1 - (k + 1) - 1 = m - 1 - k by omega]
      simp [show k ≠ m by omega]
    rw [k1, w1]

def asg {h p : ℕ} (s t : Fin p) (q : Idx h) : Sum (Fin p) (Fin h × (Bool × Bool)) → Bool :=
  Sum.elim
    (fun i => if i = s ∧ q.1.1 = 0 then q.2.2.1 else if i = t then q.2.2.2
      else if i = s then q.2.2.1 else false)
    (fun e => decide (e ∉ keyq q))

def Pth {h p : ℕ} (s t : Fin p) (a : Sum (Fin p) (Fin h × (Bool × Bool)) → Bool) : Prop :=
  ∃ x : Fin (h + 1) → Bool,
    x 0 = a (Sum.inl s) ∧ x (Fin.last h) = a (Sum.inl t) ∧
    ∀ i : Fin h, a (Sum.inr (i, x i.castSucc, x i.succ)) = true

lemma mk_path {h p : ℕ} (s t : Fin p) (b : Sum (Fin p) (Fin h × (Bool × Bool)) → Bool) (x : ℕ → Bool)
    (h0 : x 0 = b (Sum.inl s)) (h1 : x h = b (Sum.inl t))
    (he : ∀ i : Fin h, b (Sum.inr (i, x i.val, x (i.val + 1))) = true) : Pth s t b :=
  ⟨fun k => x k.val, by simpa using h0, by simpa using h1, fun i => by simpa using he i⟩

lemma flips {h p : ℕ} (s t : Fin p) (q : Idx h) (hq : q ∈ Qs h (s = t)) :
    ∀ lit ∈ cl s t q, Pth s t (Function.update (asg s t q) lit.1 lit.2) := by
  obtain ⟨hlr, hr, _, _, _, hs⟩ := mem_Qs hq
  have as0 : q.1.1 = 0 → asg s t q (Sum.inl s) = q.2.2.1 := by
    intro h0; simp [asg, h0]
  have at0 : q.1.2 = h → asg s t q (Sum.inl t) = q.2.2.2 := by
    intro h1
    by_cases c : t = s ∧ q.1.1 = 0
    · simp only [asg, Sum.elim_inl, if_pos c]
      exact hs c.1.symm c.2 h1
    · simp only [asg, Sum.elim_inl, if_neg c, if_true]
  have edge : ∀ (e : Fin h × (Bool × Bool)),
      ¬(Lf q.1.1 q.1.2 (cf q.2.1) q.2.2.1 e.1.val e.2.1 ∧
        Rf h q.1.1 q.1.2 (cf q.2.1) q.2.2.2 (e.1.val + 1) e.2.2) → asg s t q (Sum.inr e) = true := by
    intro e he
    simp only [asg, Sum.elim_inr, decide_eq_true_eq, keyq, mem_filter, mem_univ, true_and]
    exact he
  intro lit hlit
  unfold cl at hlit
  rw [mem_union] at hlit
  rcases hlit with hk | hg
  · obtain ⟨⟨i0, a0, b0⟩, he0, rfl⟩ := mem_image.mp hk
    simp only [keyq, mem_filter, mem_univ, true_and] at he0
    obtain ⟨hL, hR⟩ := he0
    have rg := range_of hlr hL hR
    have i0h : i0.val < h := i0.isLt
    set a := asg s t q with ha
    let x : ℕ → Bool := fun k => if k = 0 then a (Sum.inl s) else if k = h then a (Sum.inl t)
      else if k ≤ i0.val then (if k = i0.val then a0 else cf q.2.1 k)
      else if k = i0.val + 1 then b0 else !(cf q.2.1 k)
    have xa : x i0.val = a0 := by
      by_cases z : i0.val = 0
      · have l0 : q.1.1 = 0 := by omega
        have : a0 = q.2.2.1 := by
          rcases hL with y | y
          · exact y.2 l0
          · omega
        simp only [x, if_pos z]
        rw [this]; exact as0 l0
      · simp only [x, if_neg z, if_neg (show i0.val ≠ h by omega), le_refl, if_true]
    have xb : x (i0.val + 1) = b0 := by
      by_cases z : i0.val + 1 = h
      · have rh : q.1.2 = h := by omega
        have : b0 = q.2.2.2 := by
          rcases hR with y | y
          · exact y.2 rh
          · omega
        simp only [x, if_neg (Nat.succ_ne_zero _), if_pos z]
        rw [this]; exact at0 rh
      · simp only [x, if_neg (Nat.succ_ne_zero _), if_neg z,
          if_neg (show ¬(i0.val + 1 ≤ i0.val) by omega), if_true]
    refine mk_path s t _ x ?_ ?_ ?_
    · rw [Function.update_of_ne (by simp)]; simp [x]
    · rw [Function.update_of_ne (by simp)]
      by_cases z : h = 0
      · omega
      · simp [x, z]
    · intro i
      by_cases ei : (i, x i.val, x (i.val + 1)) = (i0, a0, b0)
      · simp only [ei, Function.update_self]
      · rw [Function.update_of_ne (by simpa using ei)]
        apply edge
        rintro ⟨h1, h2⟩
        dsimp only at h1 h2
        have ri := range_of hlr h1 h2
        have ih : i.val < h := i.isLt
        rcases lt_trichotomy i.val i0.val with lt | eq | gt
        · have v : x (i.val + 1) = cf q.2.1 (i.val + 1) := by
            simp only [x, if_neg (Nat.succ_ne_zero _), if_neg (show i.val + 1 ≠ h by omega),
              if_pos (show i.val + 1 ≤ i0.val by omega)]
            split_ifs with w
            · rcases hL with y | y
              · omega
              · rw [w]; exact y.2.2
            · rfl
          rcases h2 with y | y
          · omega
          · exact y.2.2 v
        · have : i = i0 := Fin.ext eq
          subst this
          exact ei (by rw [xa, xb])
        · have v : x i.val ≠ cf q.2.1 i.val := by
            simp only [x, if_neg (show i.val ≠ 0 by omega), if_neg (show i.val ≠ h by omega),
              if_neg (show ¬(i.val ≤ i0.val) by omega)]
            split_ifs with w
            · rcases hR with y | y
              · omega
              · rw [w]; exact y.2.2
            · cases cf q.2.1 i.val <;> decide
          rcases h1 with y | y
          · omega
          · exact v y.2.2
  · unfold gd at hg
    rw [mem_union] at hg
    rcases hg with hg | hg
    · split_ifs at hg with l0
      swap
      · simp at hg
      rw [mem_singleton] at hg
      subst hg
      dsimp only
      set b := Function.update (asg s t q) (Sum.inl s) (!q.2.2.1) with hb
      let x : ℕ → Bool := fun k => if k = 0 then b (Sum.inl s) else if k = h then b (Sum.inl t)
        else !(cf q.2.1 k)
      refine mk_path s t b x (by simp [x]) ?_ ?_
      · simp [x, show h ≠ 0 by omega]
      · intro i
        rw [hb, Function.update_of_ne (by simp)]
        apply edge
        rintro ⟨h1, h2⟩
        dsimp only at h1 h2
        have ri := range_of hlr h1 h2
        have ih : i.val < h := i.isLt
        by_cases z : i.val = 0
        · have v : x i.val = !q.2.2.1 := by simp [x, z, hb]
          rcases h1 with y | y
          · have := v.symm.trans (y.2 l0)
            revert this; cases q.2.2.1 <;> decide
          · omega
        · have v : x i.val = !(cf q.2.1 i.val) := by
            simp only [x, if_neg z, if_neg (show i.val ≠ h by omega)]
          rcases h1 with y | y
          · omega
          · have := v.symm.trans y.2.2
            revert this; cases cf q.2.1 i.val <;> decide
    · split_ifs at hg with rh
      swap
      · simp at hg
      rw [mem_singleton] at hg
      subst hg
      dsimp only
      set b := Function.update (asg s t q) (Sum.inl t) (!q.2.2.2) with hb
      let x : ℕ → Bool := fun k => if k = 0 then b (Sum.inl s) else if k = h then b (Sum.inl t)
        else cf q.2.1 k
      refine mk_path s t b x (by simp [x]) ?_ ?_
      · simp [x, show h ≠ 0 by omega]
      · intro i
        rw [hb, Function.update_of_ne (by simp)]
        apply edge
        rintro ⟨h1, h2⟩
        dsimp only at h1 h2
        have ri := range_of hlr h1 h2
        have ih : i.val < h := i.isLt
        by_cases z : i.val + 1 = h
        · have v : x (i.val + 1) = !q.2.2.2 := by
            simp only [x, if_neg (Nat.succ_ne_zero _), if_pos z, hb, Function.update_self]
          rcases h2 with y | y
          · have := v.symm.trans (y.2 rh)
            revert this; cases q.2.2.2 <;> decide
          · omega
        · have v : x (i.val + 1) = cf q.2.1 (i.val + 1) := by
            simp only [x, if_neg (Nat.succ_ne_zero _), if_neg z]
          rcases h2 with y | y
          · omega
          · exact y.2.2 v

lemma unsat {h p : ℕ} (s t : Fin p) (q : Idx h) (hq : q ∈ Qs h (s = t)) :
    ¬PEqualNP.ProofComplexity.ClauseSat (asg s t q) (cl s t q) := by
  obtain ⟨hlr, hr, _, _, _, hs⟩ := mem_Qs hq
  rintro ⟨lit, hlit, hv⟩
  unfold cl at hlit
  rw [mem_union] at hlit
  rcases hlit with hk | hg
  · obtain ⟨e, he, rfl⟩ := mem_image.mp hk
    simp [asg, he] at hv
  · unfold gd at hg
    rw [mem_union] at hg
    rcases hg with hg | hg
    · split_ifs at hg with l0
      swap
      · simp at hg
      rw [mem_singleton] at hg
      subst hg
      simp [asg, l0] at hv
    · split_ifs at hg with rh
      swap
      · simp at hg
      rw [mem_singleton] at hg
      subst hg
      by_cases c : t = s ∧ q.1.1 = 0
      · simp only [asg, Sum.elim_inl, if_pos c] at hv
        rw [hs c.1.symm c.2 rh] at hv
        revert hv; cases q.2.2.2 <;> decide
      · simp only [asg, Sum.elim_inl, if_neg c, if_true] at hv
        revert hv; cases q.2.2.2 <;> decide

lemma encodes {h p : ℕ} (hh : 0 < h) (s t : Fin p) (a : Sum (Fin p) (Fin h × (Bool × Bool)) → Bool) :
    Pth s t a ↔ PEqualNP.ProofComplexity.Satisfies a (↑((Qs h (s = t)).image (cl s t)) : Set _) := by
  constructor
  · rintro ⟨x, x0, xl, xe⟩ C hC
    obtain ⟨q, hq, rfl⟩ := mem_image.mp (mem_coe.mp hC)
    obtain ⟨hlr, hr, _, _, _, _⟩ := mem_Qs hq
    by_contra no
    have g0 : q.1.1 = 0 → a (Sum.inl s) = q.2.2.1 := by
      intro l0
      by_contra ne
      refine no ⟨(Sum.inl s, !q.2.2.1), ?_, ?_⟩
      · unfold cl gd
        rw [if_pos l0]
        simp
      · revert ne; dsimp only; cases a (Sum.inl s) <;> cases q.2.2.1 <;> decide
    have g1 : q.1.2 = h → a (Sum.inl t) = q.2.2.2 := by
      intro rh
      by_contra ne
      refine no ⟨(Sum.inl t, !q.2.2.2), ?_, ?_⟩
      · unfold cl gd
        rw [if_pos rh]
        simp
      · revert ne; dsimp only; cases a (Sum.inl t) <;> cases q.2.2.2 <;> decide
    let y : ℕ → Bool := fun k => if hk : k < h + 1 then x ⟨k, hk⟩ else false
    have step : ∀ i, i < h → Lf q.1.1 q.1.2 (cf q.2.1) q.2.2.1 i (y i) →
        ¬Rf h q.1.1 q.1.2 (cf q.2.1) q.2.2.2 (i + 1) (y (i + 1)) := by
      intro i hi hL hR
      apply no
      refine ⟨(Sum.inr (⟨i, hi⟩, (y i, y (i + 1))), true), ?_, ?_⟩
      · unfold cl
        refine mem_union_left _ (mem_image.mpr ⟨(⟨i, hi⟩, (y i, y (i + 1))), ?_, rfl⟩)
        simp only [keyq, mem_filter, mem_univ, true_and]
        exact ⟨hL, hR⟩
      · have e1 : y i = x (⟨i, hi⟩ : Fin h).castSucc := dif_pos (show i < h + 1 by omega)
        have e2 : y (i + 1) = x (⟨i, hi⟩ : Fin h).succ := dif_pos (show i + 1 < h + 1 by omega)
        dsimp only
        rw [e1, e2]
        exact xe ⟨i, hi⟩
    have walk : ∀ n, q.1.1 + n < q.1.2 →
        Lf q.1.1 q.1.2 (cf q.2.1) q.2.2.1 (q.1.1 + n) (y (q.1.1 + n)) := by
      intro n
      induction n with
      | zero =>
        intro _
        refine Or.inl ⟨rfl, fun l0 => ?_⟩
        have : y (q.1.1 + 0) = a (Sum.inl s) := by
          rw [← x0]; simp [y, l0]
        exact this.trans (g0 l0)
      | succ n ih =>
        intro hn
        have nr := step (q.1.1 + n) (by omega) (ih (by omega))
        refine Or.inr ⟨by omega, hn, ?_⟩
        by_contra ne
        exact nr (Or.inr ⟨by omega, by omega, by rwa [← Nat.add_assoc] at ne⟩)
    have e : q.1.1 + (q.1.2 - 1 - q.1.1) = q.1.2 - 1 := by omega
    have last := walk (q.1.2 - 1 - q.1.1) (by omega)
    rw [e] at last
    apply step (q.1.2 - 1) (by omega) last
    refine Or.inl ⟨by omega, fun rh => ?_⟩
    have : y (q.1.2 - 1 + 1) = a (Sum.inl t) := by
      rw [← xl, show q.1.2 - 1 + 1 = h by omega]
      simp [y, Fin.last]
    exact this.trans (g1 rh)
  · intro sat
    by_contra no
    classical
    let Ed : ℕ → Bool → Bool → Prop := fun i u v => ∀ hi : i < h, a (Sum.inr (⟨i, hi⟩, (u, v))) = true
    let S : ℕ → Bool → Prop := fun k v => ∃ y : ℕ → Bool, y k = v ∧ y h = a (Sum.inl t) ∧
      ∀ i, k ≤ i → i < h → Ed i (y i) (y (i + 1))
    have Sstep : ∀ k u v, k < h → Ed k u v → S (k + 1) v → S k u := by
      rintro k u v hk he ⟨y, yk, yh, ye⟩
      refine ⟨Function.update y k u, by simp, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact yh
      · intro i hi hih
        rw [Function.update_of_ne (show i + 1 ≠ k by omega)]
        by_cases z : i = k
        · subst z
          rw [Function.update_self, yk]; exact he
        · rw [Function.update_of_ne z]
          exact ye i (by omega) hih
    have Send : S h (a (Sum.inl t)) :=
      ⟨fun _ => a (Sum.inl t), rfl, rfl, fun i h1 h2 => by omega⟩
    have S0 : ¬S 0 (a (Sum.inl s)) := by
      rintro ⟨y, y0, yh, ye⟩
      exact no (mk_path s t a y y0 yh fun i => ye i.val (Nat.zero_le _) i.isLt i.isLt)
    let full : ℕ → Prop := fun k => if k = 0 then ¬S 0 (a (Sum.inl s)) else ∀ v, ¬S k v
    have full0 : full 0 := by simpa [full] using S0
    obtain ⟨l, hl⟩ : ∃ l, l = Nat.findGreatest full (h - 1) := ⟨_, rfl⟩
    have fl : full l := hl ▸ Nat.findGreatest_spec (Nat.zero_le _) full0
    have lh : l ≤ h - 1 := hl ▸ Nat.findGreatest_le _
    have lmax : ∀ k, l < k → k ≤ h - 1 → ¬full k := fun k h1 h2 =>
      Nat.findGreatest_is_greatest (hl ▸ h1) h2
    let emp : ℕ → Prop := fun k => l < k ∧ (k = h ∨ ∀ v, S k v)
    have ex : ∃ k, emp k := ⟨h, by omega, Or.inl rfl⟩
    obtain ⟨r, hrr⟩ : ∃ r, r = Nat.find ex := ⟨_, rfl⟩
    have er : emp r := hrr ▸ Nat.find_spec ex
    have rh : r ≤ h := hrr ▸ Nat.find_min' ex ⟨by omega, Or.inl rfl⟩
    have rmin : ∀ k, k < r → ¬emp k := fun k hk => Nat.find_min ex (hrr ▸ hk)
    have lr : l < r := er.1
    let c : ℕ → Bool := fun k => if S k false then true else false
    have mid : ∀ k, l < k → k < r → ∀ v, ¬S k v ↔ v = c k := by
      intro k h1 h2 v
      have nf := lmax k h1 (by omega)
      have ne := rmin k h2
      simp only [full, if_neg (show k ≠ 0 by omega), not_forall, not_not] at nf
      have ne' : ¬∀ v, S k v := fun z => ne ⟨h1, Or.inr z⟩
      rw [Bool.forall_bool] at ne'
      rw [Bool.exists_bool] at nf
      by_cases z : S k false
      · have z' : ¬S k true := fun w => ne' ⟨z, w⟩
        cases v <;> simp [c, z, z']
      · have z' : S k true := nf.resolve_left z
        cases v <;> simp [c, z, z']
    let q : Idx h := ⟨(l, r), fun k => if l < k.val ∧ k.val < r then c k.val else false,
      (if l = 0 then a (Sum.inl s) else false, if r = h then a (Sum.inl t) else false)⟩
    have hq : q ∈ Qs h (s = t) := by
      simp only [q, Qs, Ps, Cs, AB, mem_sigma, mem_filter, mem_product, mem_range, Fintype.mem_piFinset]
      refine ⟨⟨⟨by omega, by omega⟩, lr⟩, ?_, ⟨?_, ?_⟩, ?_⟩
      · intro k
        by_cases z : l < k.val ∧ k.val < r
        · rw [if_pos z, if_pos z]; exact mem_univ _
        · rw [if_neg z, if_neg z]; exact mem_singleton_self _
      · by_cases z : l = 0
        · rw [if_pos z, if_pos z]; exact mem_univ _
        · rw [if_neg z, if_neg z]; exact mem_singleton_self _
      · by_cases z : r = h
        · rw [if_pos z, if_pos z]; exact mem_univ _
        · rw [if_neg z, if_neg z]; exact mem_singleton_self _
      · intro e l0 r0
        rw [if_pos l0, if_pos r0, e]
    have ceq : ∀ k, l < k → k < r → cf q.2.1 k = c k := by
      intro k h1 h2
      simp [cf, q, show k < h + 1 by omega, h1, h2]
    obtain ⟨lit, hlit, hv⟩ := sat (cl s t q) (mem_coe.mpr (mem_image_of_mem _ hq))
    unfold cl at hlit
    rw [mem_union] at hlit
    rcases hlit with hk | hg
    · obtain ⟨⟨i, u, v⟩, he, rfl⟩ := mem_image.mp hk
      simp only [keyq, mem_filter, mem_univ, true_and] at he
      obtain ⟨hL, hR⟩ := he
      change Lf l r (cf q.2.1) q.2.2.1 i.val u at hL
      change Rf h l r (cf q.2.1) q.2.2.2 (i.val + 1) v at hR
      have nu : ¬S i.val u := by
        rcases hL with ⟨e1, e2⟩ | ⟨h1, h2, h3⟩
        · by_cases z : l = 0
          · have : u = a (Sum.inl s) := by
              have := e2 z
              simpa [q, z] using this
            rw [e1, z, this]; exact S0
          · have f := fl
            simp only [full, if_neg z] at f
            rw [e1]; exact f u
        · rw [ceq _ h1 h2] at h3
          exact (mid _ h1 h2 u).mpr h3
      have sv : S (i.val + 1) v := by
        rcases hR with ⟨e1, e2⟩ | ⟨h1, h2, h3⟩
        · by_cases z : r = h
          · have : v = a (Sum.inl t) := by
              have := e2 z
              simpa [q, z] using this
            rw [e1, z, this]; exact Send
          · rcases er.2 with w | w
            · exact absurd w z
            · rw [e1]; exact w v
        · rw [ceq _ h1 h2] at h3
          by_contra w
          exact h3 ((mid _ h1 h2 v).mp w)
      exact nu (Sstep i.val u v i.isLt (fun _ => hv) sv)
    · unfold gd at hg
      rw [mem_union] at hg
      rcases hg with hg | hg
      · split_ifs at hg with l0
        swap
        · simp at hg
        rw [mem_singleton] at hg
        subst hg
        change l = 0 at l0
        simp [q, l0] at hv
      · split_ifs at hg with r0
        swap
        · simp at hg
        rw [mem_singleton] at hg
        subst hg
        change r = h at r0
        simp [q, r0] at hv

end PEqualNP.Outside.L_lib_539

theorem PEqualNP.Outside.L_lib_539 : (∀ (h p : ℕ), 0 < h → ∀ s t : Fin p,
  let E := Fin h × (Bool × Bool)
  let V := Sum (Fin p) E
  let path := fun a : V → Bool => ∃ x : Fin (h + 1) → Bool,
    x 0 = a (Sum.inl s) ∧ x (Fin.last h) = a (Sum.inl t) ∧
    ∀ i : Fin h, a (Sum.inr (i, x i.castSucc, x i.succ)) = true
  let enc := fun F : Finset (PEqualNP.ProofComplexity.Clause V) => ∀ a,
    path a ↔ PEqualNP.ProofComplexity.Satisfies a (↑F : Set _)
  let key := fun C : PEqualNP.ProofComplexity.Clause V =>
    Finset.univ.filter (fun e : E => (Sum.inr e, true) ∈ C)
  let count := (if s = t then 7 else 9) * 2 ^ (h - 1) - h - 4
  let cost := if h = 1 then (if s = t then 4 else 12)
    else (if s = t then 7*h else 9*h+6) * 2 ^ (h-1) - 4
  ∃ F : Finset (PEqualNP.ProofComplexity.Clause V), enc F ∧
    F.card = count ∧ (∑ C ∈ F, C.card) = cost ∧
    (∀ C ∈ F, (key C).Nonempty ∧
      (∀ e : E, (Sum.inr e, false) ∉ C) ∧
      (∀ (i : Fin p) (v : Bool), (Sum.inl i, v) ∈ C → i = s ∨ i = t) ∧
      ∃ a : V → Bool, (∀ e : E, a (Sum.inr e) = false ↔ e ∈ key C) ∧
        ¬PEqualNP.ProofComplexity.ClauseSat a C ∧
        ∀ lit ∈ C, path (Function.update a lit.1 lit.2)) ∧
    (∀ C ∈ F, ∀ B ∈ F, key C = key B → C = B) ∧
    ∀ G : Finset (PEqualNP.ProofComplexity.Clause V), enc G →
      ∀ C ∈ F, ∃ B ∈ G, C ⊆ B ∧ key C = key B) := by
  intro h p hh s t
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
  intro E V path enc key count cost
  have hkey : ∀ q, key (PEqualNP.Outside.L_lib_539.cl s t q) = PEqualNP.Outside.L_lib_539.keyq q := by
    intro q
    rw [← PEqualNP.Outside.L_lib_539.key_cl s t q]
  have inj : Set.InjOn (PEqualNP.Outside.L_lib_539.cl s t)
      (↑(PEqualNP.Outside.L_lib_539.Qs (m + 1) (s = t)) : Set (PEqualNP.Outside.L_lib_539.Idx (m + 1))) := by
    intro q hq q' hq' e
    apply PEqualNP.Outside.L_lib_539.key_inj hq hq'
    rw [← hkey, ← hkey, e]
  have henc : enc ((PEqualNP.Outside.L_lib_539.Qs (m + 1) (s = t)).image
      (PEqualNP.Outside.L_lib_539.cl s t)) :=
    fun a => PEqualNP.Outside.L_lib_539.encodes (Nat.succ_pos m) s t a
  refine ⟨_, henc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn inj]
    have c := PEqualNP.Outside.L_lib_539.count_Q m (s = t)
    show _ = (if s = t then 7 else 9) * 2 ^ (m + 1 - 1) - (m + 1) - 4
    rw [Nat.add_sub_cancel]
    omega
  · rw [Finset.sum_image inj]
    rw [Finset.sum_congr rfl fun q hq => PEqualNP.Outside.L_lib_539.card_cl s t q hq]
    exact PEqualNP.Outside.L_lib_539.cost_Q m (s = t)
  · intro C hC
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hC
    have m1 := PEqualNP.Outside.L_lib_539.mem_Qs hq
    refine ⟨?_, ?_, ?_, PEqualNP.Outside.L_lib_539.asg s t q, ?_,
      PEqualNP.Outside.L_lib_539.unsat s t q hq, PEqualNP.Outside.L_lib_539.flips s t q hq⟩
    · rw [hkey]
      obtain ⟨a, b, hab⟩ := PEqualNP.Outside.L_lib_539.layer (h := m + 1)
        (c := PEqualNP.Outside.L_lib_539.cf q.2.1) (α := q.2.2.1) (β := q.2.2.2) le_rfl m1.1
      have lt : q.1.1 < m + 1 := lt_of_lt_of_le m1.1 m1.2.1
      refine ⟨(⟨q.1.1, lt⟩, (a, b)), ?_⟩
      simp only [PEqualNP.Outside.L_lib_539.keyq, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hab
    · intro e he
      simp only [PEqualNP.Outside.L_lib_539.cl, PEqualNP.Outside.L_lib_539.gd, Finset.mem_union,
        Finset.mem_image] at he
      rcases he with ⟨_, _, h2⟩ | h2 | h2
      · simp at h2
      · split_ifs at h2 <;> simp at h2
      · split_ifs at h2 <;> simp at h2
    · intro i v he
      simp only [PEqualNP.Outside.L_lib_539.cl, PEqualNP.Outside.L_lib_539.gd, Finset.mem_union,
        Finset.mem_image] at he
      rcases he with ⟨_, _, h2⟩ | h2 | h2
      · simp at h2
      · split_ifs at h2
        · simp at h2; exact Or.inl h2.1
        · simp at h2
      · split_ifs at h2
        · simp at h2; exact Or.inr h2.1
        · simp at h2
    · intro e
      rw [hkey]
      simp [PEqualNP.Outside.L_lib_539.asg]
  · intro C hC B hB e
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hB
    rw [hkey, hkey] at e
    rw [PEqualNP.Outside.L_lib_539.key_inj hq hq' e]
  · intro G hG C hC
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hC
    have np : ¬path (PEqualNP.Outside.L_lib_539.asg s t q) := fun hp =>
      PEqualNP.Outside.L_lib_539.unsat s t q hq ((henc _).mp hp _ (Finset.mem_coe.mpr hC))
    have ng : ¬PEqualNP.ProofComplexity.Satisfies (PEqualNP.Outside.L_lib_539.asg s t q) (↑G : Set _) :=
      fun z => np ((hG _).mpr z)
    simp only [PEqualNP.ProofComplexity.Satisfies, not_forall] at ng
    obtain ⟨B, hB, nB⟩ := ng
    have sub : PEqualNP.Outside.L_lib_539.cl s t q ⊆ B := by
      intro lit hlit
      have pu := PEqualNP.Outside.L_lib_539.flips s t q hq lit hlit
      obtain ⟨l', hl', hv⟩ := (hG _).mp pu B hB
      by_cases z : l'.1 = lit.1
      · rw [z, Function.update_self] at hv
        have : l' = lit := Prod.ext z hv.symm
        exact this ▸ hl'
      · rw [Function.update_of_ne z] at hv
        exact absurd ⟨l', hl', hv⟩ nB
    refine ⟨B, Finset.mem_coe.mp hB, sub, ?_⟩
    rw [hkey]
    ext e
    constructor
    · intro he
      have : (Sum.inr e, true) ∈ B := by
        apply sub
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
    · intro he
      have mB := (Finset.mem_filter.mp he).2
      by_contra ne
      apply nB
      exact ⟨_, mB, by simp [PEqualNP.Outside.L_lib_539.asg, ne]⟩
