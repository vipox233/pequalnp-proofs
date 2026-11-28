import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1740


namespace Cex

namespace Alteration

open Finset

noncomputable def freeCoordinates {E A : Type} [Fintype E] [DecidableEq E]
    (s : Finset E) (z : A) :
    {f : E → A // ∀ e ∈ s, f e = z} ≃ (↥(sᶜ) → A) where
  toFun f e := f.val e.val
  invFun g := ⟨fun e => if he : e ∈ s then z else g ⟨e, mem_compl.mpr he⟩,
    by intro e he; simp [he]⟩
  left_inv f := by
    apply Subtype.ext
    funext e
    by_cases he : e ∈ s
    · simp [he, f.property e he]
    · simp [he]
  right_inv g := by
    funext e
    have he := mem_compl.mp e.property
    simp [he]

theorem forced_count {E A : Type} [Fintype E] [Fintype A] [DecidableEq E]
    [DecidableEq A] (s : Finset E) (z : A) :
    Fintype.card {f : E → A // ∀ e ∈ s, f e = z} =
      Fintype.card A ^ (Fintype.card E - s.card) := by
  rw [Fintype.card_congr (freeCoordinates s z)]
  simp

theorem thin {α : Type} (raw : Finset α) (bad : Finset (Finset α))
    (hne : ∀ s ∈ bad, s.Nonempty) :
    ∃ keep ⊆ raw, (∀ s ∈ bad, ¬s ⊆ keep) ∧ raw.card ≤ keep.card + bad.card := by
  classical
  let choose (s : ↥bad) : α := (hne s.val s.property).choose
  let removed := bad.attach.image choose
  refine ⟨raw \ removed, sdiff_subset, ?_, ?_⟩
  · intro s hs hsub
    have hr : choose ⟨s, hs⟩ ∈ removed := mem_image.mpr ⟨⟨s, hs⟩, mem_attach .., rfl⟩
    exact (mem_sdiff.mp (hsub (hne s hs).choose_spec)).2 hr
  · have hsmall : removed.card ≤ bad.card := by
      simpa [removed] using (card_image_le (s := bad.attach) (f := choose))
    exact le_trans card_le_card_sdiff_add_card (Nat.add_le_add_left hsmall _)

theorem positive_draw {Ω : Type} [Fintype Ω] (gain cost : Ω → Nat)
    (h : (∑ x, cost x) < ∑ x, gain x) : ∃ x, cost x < gain x := by
  by_contra! hn
  exact (not_le.mpr h) (sum_le_sum fun i _ => hn i)

def q : Nat := 4096

end Alteration

namespace Sampling

open Finset

abbrev Draw (T I A B : Type) := (T → A) × (I → B)

def hit {T I A B : Type} (a : A) (b : B) (s : Finset T) (t : Finset I) (x : Draw T I A B) : Prop :=
  (∀ i ∈ s, x.1 i = a) ∧ (∀ j ∈ t, x.2 j = b)

instance instDecidableHit {T I A B : Type} [DecidableEq A] [DecidableEq B] (a : A) (b : B) (s : Finset T) (t : Finset I) (x : Draw T I A B) : Decidable (hit a b s t x) :=
  inferInstanceAs (Decidable ((∀ i ∈ s, x.1 i = a) ∧ (∀ j ∈ t, x.2 j = b)))

private def separate {T I A B : Type} (a : A) (b : B) (s : Finset T) (t : Finset I) :
    {x : Draw T I A B // hit a b s t x} ≃
      {f : T → A // ∀ i ∈ s, f i = a} × {f : I → B // ∀ j ∈ t, f j = b} where
  toFun x := (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
  invFun x := ⟨(x.1.val, x.2.val), x.1.property, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem hit_mass {T I A B : Type} [Fintype T] [Fintype I] [Fintype A] [Fintype B]
    [DecidableEq T] [DecidableEq I] [DecidableEq A] [DecidableEq B]
    (a : A) (b : B) (s : Finset T) (t : Finset I) :
    (univ.filter (hit a b s t)).card * (Fintype.card A ^ s.card * Fintype.card B ^ t.card) =
      Fintype.card (Draw T I A B) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (separate a b s t),
    Fintype.card_prod, Alteration.forced_count, Alteration.forced_count]
  simp only [Draw, Fintype.card_prod, Fintype.card_fun]
  rw [Nat.mul_mul_mul_comm, ← pow_add, ← pow_add,
    Nat.sub_add_cancel (card_le_univ s), Nat.sub_add_cancel (card_le_univ t)]

def active {T I A B U : Type} [Fintype U] [DecidableEq A] [DecidableEq B]
    (a : A) (b : B) (s : U → Finset T) (t : U → Finset I) (x : Draw T I A B) :
    Finset U :=
  univ.filter fun u => hit a b (s u) (t u) x

theorem double_count {T I A B U : Type} [Fintype T] [Fintype I] [Fintype A] [Fintype B] [Fintype U]
    [DecidableEq T] [DecidableEq I] [DecidableEq A] [DecidableEq B]
    (a : A) (b : B) (s : U → Finset T) (t : U → Finset I) :
    (∑ x, (active a b s t x).card) = ∑ u, (univ.filter (hit a b (s u) (t u))).card := by
  simp only [active, card_filter]
  exact sum_comm

theorem uniform_mass {T I A B U : Type} [Fintype T] [Fintype I] [Fintype A] [Fintype B] [Fintype U]
    [DecidableEq T] [DecidableEq I] [DecidableEq A] [DecidableEq B]
    (a : A) (b : B) (s : U → Finset T) (t : U → Finset I)
    (m n : Nat) (hs : ∀ u, (s u).card = m) (ht : ∀ u, (t u).card = n) :
    (∑ x, (active a b s t x).card) * (Fintype.card A ^ m * Fintype.card B ^ n) =
      Fintype.card U * Fintype.card (Draw T I A B) := by
  rw [double_count, sum_mul]
  have per (u : U) : (univ.filter (hit a b (s u) (t u))).card *
      (Fintype.card A ^ m * Fintype.card B ^ n) = Fintype.card (Draw T I A B) := by
    simpa only [hs, ht] using hit_mass a b (s u) (t u)
  simp [per]

theorem class_mass_bound {T I A B U : Type} [Fintype T] [Fintype I] [Fintype A] [Fintype B] [Fintype U]
    [DecidableEq T] [DecidableEq I] [DecidableEq A] [DecidableEq B]
    (a : A) (b : B) (s : U → Finset T) (t : U → Finset I)
    (m n q v d k : Nat) (hq : 0 < q)
    (hs : ∀ u, (s u).card = m) (ht : ∀ u, (t u).card = n)
    (hv : Fintype.card U ≤ q ^ v) (hd : Fintype.card A ^ m * Fintype.card B ^ n = q ^ d)
    (hweight : v ≤ k + d) :
    (∑ x, (active a b s t x).card) ≤ Fintype.card (Draw T I A B) * q ^ k := by
  refine Nat.le_of_mul_le_mul_right ?_ (pow_pos hq d)
  calc
    _ = Fintype.card U * Fintype.card (Draw T I A B) := by
      rw [← hd, uniform_mass a b s t m n hs ht]
    _ ≤ q ^ (k + d) * Fintype.card (Draw T I A B) :=
      Nat.mul_le_mul_right _ (hv.trans (Nat.pow_le_pow_right hq hweight))
    _ = _ := by rw [pow_add]; ring

end Sampling

namespace Overlap

structure Four (α : Type) where
  a : α
  b : α
  c : α
  d : α
  deriving DecidableEq

def Four.atRole {α : Type} (v : Four α) (i : Fin 4) : α :=
  match i with | 0 => v.a | 1 => v.b | 2 => v.c | 3 => v.d

def vectorEquiv (A : Type) : Four A ≃ (Fin 4 → A) where
  toFun := Four.atRole
  invFun f := ⟨f 0, f 1, f 2, f 3⟩
  left_inv _ := rfl
  right_inv f := by funext i; fin_cases i <;> rfl

def fintypeFour {A : Type} [Fintype A] : Fintype (Four A) :=
  Fintype.ofEquiv _ (vectorEquiv A).symm

def mask {α : Type} [DecidableEq α] (v : Four α) : Nat :=
  (if v.a = v.b then 1 else 0) + (if v.a = v.c then 2 else 0) +
  (if v.a = v.d then 4 else 0) + (if v.b = v.c then 8 else 0) +
  (if v.b = v.d then 16 else 0) + (if v.c = v.d then 32 else 0)

def patterns : List Nat := [0, 1, 2, 4, 8, 11, 12, 16, 18, 21, 32, 33, 38, 56, 63]

def blocks (p : Nat) : Nat :=
  1 + (if p &&& 1 = 0 then 1 else 0) + (if p &&& 10 = 0 then 1 else 0) +
      (if p &&& 52 = 0 then 1 else 0)

def values {α : Type} [DecidableEq α] (v : Four α) : Finset α := {v.d, v.c, v.b, v.a}

theorem mask_spec {α : Type} [DecidableEq α] (v : Four α) :
    mask v ∈ patterns ∧ blocks (mask v) = (values v).card := by
  obtain ⟨a, b, c, d⟩ := v
  simp only [mask, values]
  split_ifs <;> simp_all [blocks, patterns, Finset.card_insert_of_notMem, eq_comm]

def zip {α β : Type} (u : Four α) (v : Four β) : Four (α × β) :=
  ⟨(u.a, v.a), (u.b, v.b), (u.c, v.c), (u.d, v.d)⟩

theorem bit_mask {α : Type} [DecidableEq α] (v : Four α) (i : Nat) :
    (mask v).testBit i =
      match i with
      | 0 => decide (v.a = v.b) | 1 => decide (v.a = v.c)
      | 2 => decide (v.a = v.d) | 3 => decide (v.b = v.c)
      | 4 => decide (v.b = v.d) | 5 => decide (v.c = v.d)
      | _ => false := by
  have small : mask v < 2 ^ 6 := by
    have hm := (mask_spec v).1
    simp [patterns] at hm
    omega
  rcases i with _ | _ | _ | _ | _ | _ | i
  all_goals first
    | exact Nat.testBit_lt_two_pow (lt_of_lt_of_le small
        (Nat.pow_le_pow_right (by decide) (by omega)))
    | (unfold mask; split_ifs <;> simp_all <;> decide)

theorem mask_zip {α β : Type} [DecidableEq α] [DecidableEq β] (u : Four α) (v : Four β) :
    mask (zip u v) = mask u &&& mask v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, bit_mask, bit_mask, bit_mask]
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [zip]

def row (p x y : Nat) : Int :=
  70 * (blocks p : Int) - 44 * ((blocks (p &&& x) : Int) + blocks (p &&& y))

def hubScore (h : Four Nat) : Int :=
  50 * ((blocks h.a : Int) + blocks h.b + blocks h.c + blocks h.d) -
  25 * ((blocks (h.a &&& h.b) : Int) + blocks (h.c &&& h.d))

def score (h w : Four Nat) : Int :=
  hubScore h + row w.a h.b h.d + row w.b h.b h.c +
    row w.c h.a h.c + row w.d h.a h.d

def rowDom (first second : Bool) : List Nat :=
  if first && second then [33] else if first then patterns.filter (·.testBit 0)
    else if second then patterns.filter (·.testBit 5) else patterns

def hubDom (first second : Bool) : List Nat :=
  if first && second then [12] else if first then patterns.filter (·.testBit 2)
    else if second then patterns.filter (·.testBit 3) else patterns

def realEdge (w h : Fin 4) : Bool :=
  match w with
  | 0 => h == 0 || h == 2 | 1 => h == 0 || h == 3
  | 2 => h == 1 || h == 3 | 3 => h == 1 || h == 2

def dom (f : Bool → Bool → List Nat) (a b i : Fin 4) :=
  f (i == a) (i == b)

def Each (f : Fin 4 → List Nat) (v : Four Nat) : Prop :=
  v.a ∈ f 0 ∧ v.b ∈ f 1 ∧ v.c ∈ f 2 ∧ v.d ∈ f 3

def allFour (f : Fin 4 → List Nat) (test : Four Nat → Bool) : Bool :=
  (f 0).all fun a => (f 1).all fun b => (f 2).all fun c =>
    (f 3).all fun d => test ⟨a, b, c, d⟩

theorem allFour_spec {f : Fin 4 → List Nat} {test : Four Nat → Bool} {v : Four Nat}
    (e : allFour f test = true) (hm : Each f v) : test v = true := by
  obtain ⟨a, b, c, d⟩ := v
  obtain ⟨ha, hb, hc, hd⟩ := hm
  simp only [allFour, List.all_eq_true] at e
  exact e _ ha _ hb _ hc _ hd

private def pack45 : List Nat → Nat
  | [] => 0
  | a :: l => a + (pack45 l <<< 45)

private def rankTable : Nat := pack45 [17609366110736, 4948879736882, 15942918602752, 1572865, 17592186044416, 1879048198]

private def rank (p : Nat) : Nat := (rankTable >>> (4 * p)) % 16

private def fastRowTable : Nat := pack45 [
  19279107993880, 19279107993880, 19279107993880, 19279108003096, 20516058575146, 20516058584344,
  19279112712472, 19281523913002, 20516063293720, 19281523912984, 20516058584344, 20516063293720,
  20516058575128, 19279108003114, 20518474494232, 20516063302936, 20518474503484, 21755429803288,
  20518474494232, 20516058593578, 21755429794072, 19279107993880, 20518479212824, 20518474494232,
  19279112712472, 20520895131946, 21755429794072, 19281523922200, 21755429803306, 21755429803288,
  19279107993880, 19279107993880, 20518479222058, 19279108003096, 20516058575146, 21755429812522,
  19281528631576, 20518474503466, 21755434521898, 20516058575128, 20518479222058, 21757845722410,
  20518479222040, 21757845731644, 22994801031466, 14459331017938, 17482987971838, 17482987994322,
  17488905131262, 20512562085162, 20512562107646, 15696286317778, 17485403900176, 18722359213266,
  14461746937042, 18722359199998, 18722359213266, 15696286317778, 17485403900176, 18722359213266,
  18725860431102, 20514978013500, 21751933326590, 15698702236882, 18724775128336, 19961730432210,
  14461746937042, 18722359199998, 18722359213266, 15698702236882, 18724775128336, 19961730432210,
  17491321050366, 21751933313322, 21751933326590, 14459331017938, 17482987971838, 18722359222500,
  17488905131262, 20512562085162, 21751933335824, 15698702236882, 18724775128336, 19961730441444,
  15698702236882, 18724775128336, 19961730441444, 18728276350206, 21754349241660, 22991304554768,
  14459330995410, 14459330995410, 17488905108734, 14459331004626, 15696281576676, 18725855699198,
  14461751633106, 15698697504996, 18725860408574, 14461751633106, 15698697504996, 18725860408574,
  15696281576658, 15698702223588, 18728271609086, 15698702223570, 16938068733174, 19965226918142,
  15698702214354, 16938068733174, 19965226908926, 15696281576658, 15698702223588, 18728271609086,
  15698702214354, 16938068733174, 19965226908926, 15698702223570, 16938068733174, 19965226918142,
  17488905108734, 17488905108734, 20518479222058, 17488905117950, 18725855690000, 21755429812522,
  17491325746430, 18728271618320, 21755434521898, 18725855689982, 18728276336912, 21757845722410,
  18728276336894, 19967642846498, 22994801031466, 9639554019468, 12663210973368, 15692785109176,
  12669128132792, 15692785086692, 18722359222500, 9639554019468, 12663210973368, 15692785109176,
  9639554019468, 12663210973368, 15692785109176, 9639554019468, 12663210973368, 15692785109176,
  12669128132792, 15692785086692, 18722359222500, 9639554019468, 12663210973368, 15692785109176,
  9639554019468, 12663210973368, 15692785109176, 9639554019468, 12663210973368, 15692785109176,
  12669128132792, 15692785086692, 18722359222500, 12669128132792, 15692785086692, 18722359222500,
  15698702246116, 18722359200016, 21751933335824, 12669128132792, 15692785086692, 18722359222500,
  12669128132792, 15692785086692, 18722359222500, 15698702246116, 18722359200016, 21751933335824
]

def fastRow (first second : Bool) (x y : Nat) : Int :=
  let k := first.toNat + 2 * second.toNat
  let offset := 9 * (225 * k + 15 * rank x + rank y)
  let digit := (fastRowTable >>> offset) % 512
  (digit : Int) - 352

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem row_certificate : ∀ a b : Bool,
    (patterns.all fun x => patterns.all fun y => (rowDom a b).all fun p =>
      decide (row p x y ≤ fastRow a b x y)) = true := by decide +kernel

theorem fastRow_sound {a b : Bool} {p x y : Nat}
    (ha : p ∈ rowDom a b) (hx : x ∈ patterns) (hy : y ∈ patterns) :
    row p x y ≤ fastRow a b x y := by
  have h := row_certificate a b
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h _ hx _ hy _ ha

def fastScore (c d : Fin 4) (h : Four Nat) : Int :=
  hubScore h + fastRow (0 == c) (0 == d) h.b h.d +
    fastRow (1 == c) (1 == d) h.b h.c + fastRow (2 == c) (2 == d) h.a h.c +
    fastRow (3 == c) (3 == d) h.a h.d

def certifiedCycle (a b c d : Fin 4) : Bool :=
  !(realEdge c a && realEdge c b && realEdge d a && realEdge d b) ||
    allFour (dom hubDom a b) fun h => decide (fastScore c d h ≤ 74)

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem cycle_certificate : ∀ a b c d, certifiedCycle a b c d = true := by decide +kernel

private theorem hub_in_patterns {a b : Bool} (p : Nat) (h : p ∈ hubDom a b) : p ∈ patterns := by
  cases a <;> cases b <;> simp [hubDom, patterns] at h ⊢ <;> grind

theorem cycle_bound (a b c d : Fin 4) (h w : Four Nat)
    (edges : realEdge c a && realEdge c b && realEdge d a && realEdge d b)
    (hh : Each (dom hubDom a b) h) (hw : Each (dom rowDom c d) w) : score h w ≤ 74 := by
  have cert := cycle_certificate a b c d
  simp only [certifiedCycle, edges, Bool.not_true, Bool.false_or] at cert
  have upper := of_decide_eq_true (allFour_spec cert hh)
  obtain ⟨h0, h1, h2, h3⟩ := hh
  obtain ⟨w0, w1, w2, w3⟩ := hw
  have a0 := fastRow_sound w0 (hub_in_patterns _ h1) (hub_in_patterns _ h3)
  have a1 := fastRow_sound w1 (hub_in_patterns _ h1) (hub_in_patterns _ h2)
  have a2 := fastRow_sound w2 (hub_in_patterns _ h0) (hub_in_patterns _ h2)
  have a3 := fastRow_sound w3 (hub_in_patterns _ h0) (hub_in_patterns _ h3)
  unfold fastScore at upper
  unfold score
  omega

def pairDomain (_ : Fin 4) : List Nat := [18, 63]

def sameTuple (h w : Four Nat) : Bool :=
  [h.a, h.b, h.c, h.d, w.a, w.b, w.c, w.d].all (· == 63)

def repeatsJ (h w : Four Nat) : Bool :=
  (w.a == 63 && (h.a == 63 || h.c == 63)) ||
  (w.b == 63 && (h.a == 63 || h.d == 63)) ||
  (w.c == 63 && (h.b == 63 || h.d == 63)) ||
  (w.d == 63 && (h.b == 63 || h.c == 63))

def repeatsS (w : Four Nat) : Bool :=
  (w.a == 63 && w.c == 63) || (w.b == 63 && w.d == 63)

set_option maxHeartbeats 0 in
private theorem pair_certificate : (allFour pairDomain fun h => allFour pairDomain fun w =>
    sameTuple h w || ((!repeatsJ h w || decide (score h w ≤ 67)) &&
                      (!repeatsS w || decide (score h w ≤ 60)))) = true := by decide +kernel

theorem duplicate_bounds {h w : Four Nat} (hh : Each pairDomain h) (hw : Each pairDomain w)
    (hd : sameTuple h w = false) :
    (repeatsJ h w → score h w ≤ 67) ∧ (repeatsS w → score h w ≤ 60) := by
  have check := allFour_spec (allFour_spec pair_certificate hh) hw
  simpa [hd, Bool.or_eq_true, Bool.and_eq_true, or_iff_not_imp_left] using check

theorem alternating_mask {α : Type} [DecidableEq α] (x y : α) :
    mask ⟨x, y, x, y⟩ = if x = y then 63 else 18 := by
  by_cases h : x = y <;> simp_all [mask, eq_comm]

theorem hub_mask_mem {α : Type} [DecidableEq α] (v : Four α) (a b : Bool)
    (h0 : a → v.a = v.d) (h1 : b → v.b = v.c) (hne : a → b → v.a ≠ v.b) :
    mask v ∈ hubDom a b := by
  have hv := (mask_spec v).1
  cases a <;> cases b
  · exact hv
  · exact List.mem_filter.mpr ⟨hv, by rw [bit_mask]; simpa using h1 rfl⟩
  · exact List.mem_filter.mpr ⟨hv, by rw [bit_mask]; simpa using h0 rfl⟩
  · have he := h0 rfl; have hf := h1 rfl; have hn := hne rfl rfl
    simp_all [hubDom, mask, eq_comm]

theorem corner_mask_mem {α : Type} [DecidableEq α] (v : Four α) (a b : Bool)
    (h0 : a → v.a = v.b) (h1 : b → v.c = v.d) (hne : a → b → v.a ≠ v.c) :
    mask v ∈ rowDom a b := by
  have hv := (mask_spec v).1
  cases a <;> cases b
  · exact hv
  · exact List.mem_filter.mpr ⟨hv, by rw [bit_mask]; simpa using h1 rfl⟩
  · exact List.mem_filter.mpr ⟨hv, by rw [bit_mask]; simpa using h0 rfl⟩
  · have he := h0 rfl; have hf := h1 rfl; have hn := hne rfl rfl
    simp_all [rowDom, mask]

theorem mem_values {A : Type} [DecidableEq A] (v : Four A) (x : A) :
    x ∈ values v ↔ ∃ i, v.atRole i = x := by
  constructor
  · simp only [values, Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨3, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [Four.atRole, values]

theorem equalities_of_mask {A B : Type} [DecidableEq A] [DecidableEq B] (u : Four A) (v : Four B)
    (h : mask u = mask v) (i j : Fin 4) :
    u.atRole i = u.atRole j ↔ v.atRole i = v.atRole j := by
  have bits (k : Nat) := congrArg (fun m : Nat => m.testBit k) h
  have ab := bits 0; have ac := bits 1; have ad := bits 2
  have bc := bits 3; have bd := bits 4; have cd := bits 5
  simp only [bit_mask, decide_eq_decide] at ab ac ad bc bd cd
  fin_cases i <;> fin_cases j <;> simp_all [Four.atRole, eq_comm]

abbrev Fiber (A : Type) [DecidableEq A] (p : Nat) := {v : Four A // mask v = p}

def fintypeFiber {A : Type} [Fintype A] [DecidableEq A] (p : Nat) : Fintype (Fiber A p) :=
  letI : Fintype (Four A) := fintypeFour
  Subtype.fintype (fun v : Four A => mask v = p)

theorem fiber_card (A : Type) [Fintype A] [DecidableEq A] (p : Nat) :
    @Fintype.card (Fiber A p) (fintypeFiber p) ≤ Fintype.card A ^ blocks p := by
  letI : Fintype (Four A) := fintypeFour
  letI : Fintype (Fiber A p) := fintypeFiber p
  classical
  by_cases he : Nonempty (Fiber A p)
  · obtain ⟨v⟩ := he
    let rep (x : ↥(values v.val)) := ((mem_values v.val x.val).mp x.property).choose
    have hr (x : ↥(values v.val)) : v.val.atRole (rep x) = x.val :=
      ((mem_values v.val x.val).mp x.property).choose_spec
    let enc (u : Fiber A p) (x : ↥(values v.val)) := u.val.atRole (rep x)
    have recover (u : Fiber A p) (i : Fin 4) :
        enc u ⟨v.val.atRole i, (mem_values _ _).mpr ⟨i, rfl⟩⟩ = u.val.atRole i :=
      (equalities_of_mask v.val u.val (v.property.trans u.property.symm) _ i).mp (hr _)
    have hi : Function.Injective enc := by
      intro a b e
      apply Subtype.ext
      apply (vectorEquiv A).injective
      funext i
      exact (recover a i).symm.trans ((congrFun e _).trans (recover b i))
    have sz := Fintype.card_le_of_injective enc hi
    have bv := (mask_spec v.val).2
    rw [v.property] at bv
    simpa only [Fintype.card_fun, Fintype.card_coe, ← bv] using sz
  · have : IsEmpty (Fiber A p) := not_nonempty_iff.mp he
    simp

abbrev Pattern := ↥patterns.toFinset
abbrev Shape := (Fin 4 → Pattern) × (Fin 4 → Pattern)
abbrev Class (A B : Type) [DecidableEq A] [DecidableEq B] (s : Shape) :=
  (∀ r, Fiber A (s.1 r).val) × (∀ r, Fiber B (s.2 r).val)

def fintypeClass {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (s : Shape) :
    Fintype (Class A B s) :=
  letI : ∀ r, Fintype (Fiber A (s.1 r).val) := fun r => fintypeFiber (s.1 r).val
  letI : ∀ r, Fintype (Fiber B (s.2 r).val) := fun r => fintypeFiber (s.2 r).val
  instFintypeProd _ _

def shapeMasks (f : Fin 4 → Pattern) : Four Nat :=
  ⟨(f 0).val, (f 1).val, (f 2).val, (f 3).val⟩

theorem class_card (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (s : Shape) : @Fintype.card (Class A B s) (fintypeClass s) ≤
    (Fintype.card A ^ ∑ r, blocks (s.1 r).val) *
    (Fintype.card B ^ ∑ r, blocks (s.2 r).val) := by
  letI : ∀ r, Fintype (Fiber A (s.1 r).val) := fun r => fintypeFiber (s.1 r).val
  letI : ∀ r, Fintype (Fiber B (s.2 r).val) := fun r => fintypeFiber (s.2 r).val
  change Fintype.card ((∀ r, Fiber A (s.1 r).val) × (∀ r, Fiber B (s.2 r).val)) ≤ _
  simp only [Fintype.card_prod, Fintype.card_pi]
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Nat.mul_le_mul (Finset.prod_le_prod fun r _ => fiber_card A _)
    (Finset.prod_le_prod fun r _ => fiber_card B _)

theorem shape_card : Fintype.card Shape ≤ 2 ^ 45 := by
  have hp : Fintype.card Pattern = 15 := by
    rw [Fintype.card_coe]; decide
  simp only [Shape, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hp]
  decide

end Overlap

namespace Model

open Finset Sampling

abbrev TwinKey (H : Type) := Bool × H × H
abbrev ClusterKey (H W : Type) := (Fin 4 × Bool) × W × H
abbrev Tuple (H W : Type) := (Fin 4 → H) × (Fin 4 → W)

def clusterHub (r : Fin 4) (side : Bool) : Fin 4 :=
  match r with
  | 0 => if side then 3 else 1 | 1 => if side then 2 else 1
  | 2 => if side then 2 else 0 | 3 => if side then 3 else 0

def twins {H W : Type} [DecidableEq H] (u : Tuple H W) : Finset (TwinKey H) :=
  univ.image fun s : Bool => (s, u.1 (if s then 2 else 0), u.1 (if s then 3 else 1))

def clusters {H W : Type} [DecidableEq H] [DecidableEq W] (u : Tuple H W) : Finset (ClusterKey H W) :=
  univ.image fun k : Fin 4 × Bool => (k, u.2 k.1, u.1 (clusterHub k.1 k.2))

theorem twins_card {H W : Type} [DecidableEq H] (u : Tuple H W) : (twins u).card = 2 := by
  unfold twins
  rw [card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  decide

theorem clusters_card {H W : Type} [DecidableEq H] [DecidableEq W] (u : Tuple H W) :
    (clusters u).card = 8 := by
  unfold clusters
  rw [card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  decide

abbrev Hub (q : Nat) := Fin (q ^ 50)
abbrev Corner (q : Nat) := Fin (q ^ 70)
abbrev Experiment (q : Nat) := Draw (TwinKey (Hub q)) (ClusterKey (Hub q) (Corner q))
    (Fin (q ^ 25)) (Fin (q ^ 44))

private def zeroColour {q : Nat} (hq : 0 < q) (k : Nat) : Fin (q ^ k) := ⟨0, pow_pos hq k⟩

def raw {q : Nat} (hq : 0 < q) (x : Experiment q) : Finset (Tuple (Hub q) (Corner q)) :=
  active (zeroColour hq 25) (zeroColour hq 44) twins clusters x

def sampleTwins {q : Nat} (hq : 0 < q) (x : Experiment q) : Finset (TwinKey (Hub q)) :=
  active (zeroColour hq 25) (zeroColour hq 44) (fun e => {e}) (fun _ => ∅) x

def sampleClusters {q : Nat} (hq : 0 < q) (x : Experiment q) : Finset (ClusterKey (Hub q) (Corner q)) :=
  active (zeroColour hq 25) (zeroColour hq 44) (fun _ => ∅) (fun e => {e}) x

private theorem splitMass (q c m k d : Nat) :
    (c * q ^ (k + d)) * m = (m * (c * q ^ k)) * q ^ d := by
  rw [pow_add]; ring

theorem raw_count {q : Nat} (hq : 0 < q) :
    (∑ x, (raw hq x).card) = Fintype.card (Experiment q) * q ^ 78 := by
  let mass := uniform_mass (zeroColour hq 25) (zeroColour hq 44)
    (twins (H := Hub q) (W := Corner q)) clusters 2 8 twins_card clusters_card
  change (∑ x, (raw hq x).card) * _ = _ at mass
  have cnt : Fintype.card (Tuple (Hub q) (Corner q)) = q ^ 200 * (q ^ 140 * q ^ 140) := by
    simp only [Tuple, Hub, Corner, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    have h70 : (q ^ 70) ^ 4 = q ^ 140 * q ^ 140 := by
      rw [← pow_add, ← pow_mul]
    rw [← pow_mul, h70]
  have denom : Fintype.card (Fin (q ^ 25)) ^ 2 * Fintype.card (Fin (q ^ 44)) ^ 8 =
      q ^ 50 * (q ^ 176 * q ^ 176) := by
    simp only [Fintype.card_fin]
    have h44 : (q ^ 44) ^ 8 = q ^ 176 * q ^ 176 := by
      rw [← pow_add, ← pow_mul]
    rw [← pow_mul, h44]
  rw [cnt, denom] at mass
  have hpos : 0 < q ^ 50 * (q ^ 176 * q ^ 176) :=
    Nat.mul_pos (pow_pos hq 50) (Nat.mul_pos (pow_pos hq 176) (pow_pos hq 176))
  apply Nat.eq_of_mul_eq_mul_right hpos
  have hexp : q ^ 78 * (q ^ 50 * (q ^ 176 * q ^ 176)) = q ^ 200 * (q ^ 140 * q ^ 140) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  calc
    (∑ x, (raw hq x).card) * (q ^ 50 * (q ^ 176 * q ^ 176))
      = q ^ 200 * (q ^ 140 * q ^ 140) * Fintype.card (Experiment q) := mass
    _ = Fintype.card (Experiment q) * (q ^ 78 * (q ^ 50 * (q ^ 176 * q ^ 176))) := by
        rw [hexp, Nat.mul_comm]
    _ = Fintype.card (Experiment q) * q ^ 78 * (q ^ 50 * (q ^ 176 * q ^ 176)) := by
        rw [Nat.mul_assoc]

theorem twins_count {q : Nat} (hq : 0 < q) :
    (∑ x, (sampleTwins hq x).card) = Fintype.card (Experiment q) * (2 * q ^ 75) := by
  have mass := uniform_mass (zeroColour hq 25) (zeroColour hq 44)
    (fun e : TwinKey (Hub q) => {e}) (fun _ => (∅ : Finset (ClusterKey (Hub q) (Corner q))))
    1 0 (by simp) (by simp)
  change (∑ x, (sampleTwins hq x).card) * _ = _ at mass
  have cnt : Fintype.card (TwinKey (Hub q)) = 2 * q ^ 100 := by
    simp only [TwinKey, Hub, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, ← pow_add]
  rw [cnt, pow_one, pow_zero, Nat.mul_one, Fintype.card_fin] at mass
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hq 25)
  calc
    _ = (2 * q ^ 100) * Fintype.card (Experiment q) := mass
    _ = _ := splitMass q 2 _ 75 25

theorem clusters_count {q : Nat} (hq : 0 < q) :
    (∑ x, (sampleClusters hq x).card) = Fintype.card (Experiment q) * (8 * q ^ 76) := by
  have mass := uniform_mass (zeroColour hq 25) (zeroColour hq 44)
    (fun _ : ClusterKey (Hub q) (Corner q) => (∅ : Finset (TwinKey (Hub q)))) (fun e => {e})
    0 1 (by simp) (by simp)
  change (∑ x, (sampleClusters hq x).card) * _ = _ at mass
  have cnt : Fintype.card (ClusterKey (Hub q) (Corner q)) = 8 * q ^ 120 := by
    simp only [ClusterKey, Hub, Corner, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, ← pow_add]
  rw [cnt, pow_one, pow_zero, Nat.one_mul, Fintype.card_fin] at mass
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hq 44)
  calc
    _ = (8 * q ^ 120) * Fintype.card (Experiment q) := mass
    _ = _ := splitMass q 8 _ 76 44

end Model

namespace Obstructions

open Finset Overlap Model Sampling

def tagged {K A : Type} [Fintype K] [DecidableEq K] [DecidableEq A] (f : K → Finset A) : Finset (K × A) :=
  univ.biUnion fun k => (f k).image (Prod.mk k)

theorem mem_tagged {K A : Type} [Fintype K] [DecidableEq K] [DecidableEq A] (f : K → Finset A)
    (k : K) (a : A) : (k, a) ∈ tagged f ↔ a ∈ f k := by
  simp [tagged]

theorem card_tagged {K A : Type} [Fintype K] [DecidableEq K] [DecidableEq A] (f : K → Finset A) :
    (tagged f).card = ∑ k, (f k).card := by
  unfold tagged
  rw [card_biUnion]
  · apply sum_congr rfl
    intro k _
    exact card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
  · intro k _ j _ ne
    rw [Function.onFun, Finset.disjoint_left]
    intro v h h'
    obtain ⟨a, _, rfl⟩ := mem_image.mp h
    obtain ⟨b, _, eq⟩ := mem_image.mp h'
    exact ne (congrArg Prod.fst eq).symm

def slot {H W : Type} [DecidableEq H] [DecidableEq W] {s : Shape} (u : Class H W s) (i : Fin 4) : Tuple H W :=
  (fun r => (u.1 r).val.atRole i, fun r => (u.2 r).val.atRole i)

def tFrom (s : Bool) : Fin 4 := if s then 2 else 0
def tTo (s : Bool) : Fin 4 := if s then 3 else 1

def tReq {H W : Type} [DecidableEq H] [DecidableEq W] {s : Shape} (u : Class H W s) : Finset (TwinKey H) :=
  tagged fun b : Bool => values (zip (u.1 (tFrom b)).val (u.1 (tTo b)).val)

def iReq {H W : Type} [DecidableEq H] [DecidableEq W] {s : Shape} (u : Class H W s) : Finset (ClusterKey H W) :=
  tagged fun k : Fin 4 × Bool =>
    values (zip (u.2 k.1).val (u.1 (clusterHub k.1 k.2)).val)

def nt (s : Shape) := ∑ b : Bool, blocks ((s.1 (tFrom b)).val &&& (s.1 (tTo b)).val)
def ni (s : Shape) := ∑ k : Fin 4 × Bool,
  blocks ((s.2 k.1).val &&& (s.1 (clusterHub k.1 k.2)).val)

private theorem zip_size {H W : Type} [DecidableEq H] [DecidableEq W]
    {a b : Nat} (u : Fiber H a) (v : Fiber W b) :
    (values (zip u.val v.val)).card = blocks (a &&& b) := by
  rw [← (mask_spec _).2, mask_zip, u.property, v.property]

theorem tReq_card {H W : Type} [DecidableEq H] [DecidableEq W] {s : Shape} (u : Class H W s) :
    (tReq u).card = nt s := by
  simp only [tReq, nt, card_tagged, zip_size]

theorem iReq_card {H W : Type} [DecidableEq H] [DecidableEq W] {s : Shape} (u : Class H W s) :
    (iReq u).card = ni s := by
  simp only [iReq, ni, card_tagged, zip_size]

theorem zip_at {H W : Type} (u : Four H) (v : Four W) (i : Fin 4) :
    (zip u v).atRole i = (u.atRole i, v.atRole i) := by
  fin_cases i <;> rfl

theorem all_slots_hit {H W A B : Type} [DecidableEq H] [DecidableEq W] {s : Shape}
    (u : Class H W s) {x : Draw (TwinKey H) (ClusterKey H W) A B}
    {a : A} {b : B}
    (hits : ∀ i, hit a b (twins (slot u i)) (clusters (slot u i)) x) :
    hit a b (tReq u) (iReq u) x := by
  constructor
  · rintro ⟨k, h⟩ hm
    rw [tReq, mem_tagged, mem_values] at hm
    obtain ⟨i, hi⟩ := hm
    rw [zip_at] at hi
    subst h
    exact (hits i).1 _ (mem_image.mpr ⟨k, mem_univ _, rfl⟩)
  · rintro ⟨k, h⟩ hm
    rw [iReq, mem_tagged, mem_values] at hm
    obtain ⟨i, hi⟩ := hm
    rw [zip_at] at hi
    subst h
    exact (hits i).2 _ (mem_image.mpr ⟨k, mem_univ _, rfl⟩)

def vertexWeight (s : Shape) := 50 * (∑ r, blocks (s.1 r).val) +
  70 * (∑ r, blocks (s.2 r).val)
def edgeWeight (s : Shape) := 25 * nt s + 44 * ni s
def low (s : Shape) : Prop := score (shapeMasks s.1) (shapeMasks s.2) ≤ 74

private theorem exists_lowShapes : ∃ S : Finset Shape, ∀ s, s ∈ S ↔ low s :=
  ⟨@Finset.filter Shape low (Classical.decPred low) Finset.univ, fun s => by simp⟩

noncomputable def lowShapes : Finset Shape :=
  Classical.choose exists_lowShapes

theorem mem_lowShapes (s : Shape) : s ∈ lowShapes ↔ low s :=
  Classical.choose_spec exists_lowShapes s

theorem weight_identity (s : Shape) :
    score (shapeMasks s.1) (shapeMasks s.2) =
    (vertexWeight s : Int) - edgeWeight s := by
  simp [vertexWeight, edgeWeight, score, hubScore, row, shapeMasks, nt, ni,
    Fintype.sum_prod_type, Fin.sum_univ_four, clusterHub, tFrom, tTo]
  ring

def present {q : Nat} (hq : 0 < q) (s : Shape) (x : Experiment q) :
    Finset (Class (Hub q) (Corner q) s) :=
  letI : Fintype (Class (Hub q) (Corner q) s) := fintypeClass s
  active (⟨0, pow_pos hq 25⟩ : Fin (q ^ 25)) (⟨0, pow_pos hq 44⟩ : Fin (q ^ 44))
    tReq iReq x

theorem class_bound {q : Nat} (hq : 0 < q) (s : Shape) (hs : low s) :
    (∑ x, (present hq s x).card) ≤ Fintype.card (Experiment q) * q ^ 74 := by
  letI : Fintype (Class (Hub q) (Corner q) s) := fintypeClass s
  apply class_mass_bound _ _ _ _ (nt s) (ni s) q (vertexWeight s) (edgeWeight s) 74 hq
    tReq_card iReq_card
  · simpa only [Hub, Corner, Fintype.card_fin, ← pow_mul, ← pow_add, vertexWeight] using
      class_card (Hub q) (Corner q) s
  · simp only [Fintype.card_fin, ← pow_mul, ← pow_add, edgeWeight]
  · have eq := weight_identity s
    unfold low at hs
    omega

def badOf {q : Nat} (S : Finset Shape) (hq : 0 < q) (x : Experiment q) :
    Finset (Finset (Tuple (Hub q) (Corner q))) :=
  S.biUnion fun s =>
    (present hq s x).image fun u => univ.image (slot u)

theorem badOf_nonempty {q : Nat} (S : Finset Shape) (hq : 0 < q) (x : Experiment q)
    (s) (hs : s ∈ badOf S hq x) : s.Nonempty := by
  unfold badOf at hs
  obtain ⟨k, _, hu⟩ := mem_biUnion.mp hs
  obtain ⟨u, _, rfl⟩ := mem_image.mp hu
  exact ⟨slot u 0, mem_image.mpr ⟨0, mem_univ _, rfl⟩⟩

theorem badOf_count {q : Nat} (S : Finset Shape) (hS : ∀ s ∈ S, low s) (hq : 0 < q) :
    (∑ x, (badOf S hq x).card) ≤ Fintype.card (Experiment q) * (2 ^ 45 * q ^ 74) := by
  calc
    _ ≤ ∑ x, ∑ s ∈ S, (present hq s x).card := by
      apply sum_le_sum; intro x _
      unfold badOf
      exact card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le)
    _ = ∑ s ∈ S, ∑ x, (present hq s x).card := sum_comm
    _ ≤ ∑ _s ∈ S, Fintype.card (Experiment q) * q ^ 74 := by
      apply sum_le_sum
      intro s hs
      exact class_bound hq s (hS s hs)
    _ ≤ _ := by
      have small : S.card ≤ 2 ^ 45 := (card_le_univ S).trans shape_card
      rw [sum_const, nsmul_eq_mul]
      calc
        _ ≤ 2 ^ 45 * (Fintype.card (Experiment q) * q ^ 74) := Nat.mul_le_mul_right _ small
        _ = _ := Nat.mul_left_comm ..

noncomputable def bad {q : Nat} (hq : 0 < q) (x : Experiment q) :
    Finset (Finset (Tuple (Hub q) (Corner q))) :=
  badOf lowShapes hq x

set_option maxRecDepth 8192 in
theorem bad_nonempty {q : Nat} (hq : 0 < q) (x : Experiment q) (s) (hs : s ∈ bad hq x) :
    s.Nonempty :=
  badOf_nonempty lowShapes hq x s hs

set_option maxRecDepth 8192 in
theorem bad_count {q : Nat} (hq : 0 < q) :
    (∑ x, (bad hq x).card) ≤ Fintype.card (Experiment q) * (2 ^ 45 * q ^ 74) :=
  badOf_count lowShapes (fun s hs => (mem_lowShapes s).mp hs) hq

set_option maxRecDepth 8192 in
theorem dense (q : Nat) (hq : q = Alteration.q) :
    ∃ (pos : 0 < q) (x : Experiment q) (keep : Finset (Tuple (Hub q) (Corner q))),
      keep ⊆ raw pos x ∧ (∀ b ∈ bad pos x, ¬ b ⊆ keep) ∧
      4 * (sampleTwins pos x).card + 4 * (sampleClusters pos x).card + 8 * q ^ 50 + 2 < keep.card := by
  have pos : 0 < q := hq ▸ (by decide : 0 < Alteration.q)
  have margin : 2 ^ 45 * q ^ 74 + 8 * q ^ 75 + 32 * q ^ 76 + (8 * q ^ 50 + 2) < q ^ 78 := by
    subst q; decide +kernel
  let D := Fintype.card (Experiment q)
  have nonemptyDraw : Nonempty (Experiment q) := ⟨(fun _ => ⟨0, pow_pos pos _⟩,
    fun _ => ⟨0, pow_pos pos _⟩)⟩
  have totalPos : 0 < D := Fintype.card_pos_iff.mpr nonemptyDraw
  let cost (x : Experiment q) := (bad pos x).card + 4 * (sampleTwins pos x).card +
    4 * (sampleClusters pos x).card + (8 * q ^ 50 + 2)
  have cheap : (∑ x, cost x) < ∑ x, (raw pos x).card := by
    rw [raw_count pos]
    apply lt_of_le_of_lt _ (Nat.mul_lt_mul_of_pos_left margin totalPos)
    simp only [cost, sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul,
      Nat.cast_id, twins_count, clusters_count]
    have z := bad_count pos
    change (∑ x, (bad pos x).card) ≤ D * (2 ^ 45 * q ^ 74) at z
    calc
      _ ≤ D * (2 ^ 45 * q ^ 74) + 4 * (D * (2 * q ^ 75)) + 4 * (D * (8 * q ^ 76)) + (8 * (D * q ^ 50) + D * 2) := by
        dsimp [D] at z ⊢; gcongr
      _ = _ := by ring
  obtain ⟨x, hx⟩ := Alteration.positive_draw _ cost cheap
  obtain ⟨keep, sub, clean, sz⟩ := Alteration.thin _ _ (bad_nonempty pos x)
  refine ⟨pos, x, keep, sub, clean, ?_⟩
  dsimp [cost] at hx
  omega

end Obstructions

inductive Parent (W K S P : Type) where
  | corner (w : W) | cluster (k : K) | opposite (s : S) | matched (p : P)
  deriving DecidableEq

inductive Vertex (H I R : Type) where
  | hub (d : H) | u (i : I) | z (i : I) | parent (r : R) | leaf (r : R)
  deriving DecidableEq

inductive Edge (I K S P R : Type) where
  | dw (i : I) | du (i : I) | yz (i : I) | uz (i : I) | wu (i : I)
  | rw (k : K) | ry (k : K) | sw (s : S) (b : Bool) | pu (p : P) (b : Bool)
  | pendant (r : R)
  deriving DecidableEq

def parentEquiv (W K S P : Type) : Parent W K S P ≃ (W ⊕ K) ⊕ (S ⊕ P) where
  toFun
    | .corner w => .inl (.inl w)
    | .cluster k => .inl (.inr k)
    | .opposite s => .inr (.inl s)
    | .matched p => .inr (.inr p)
  invFun
    | .inl (.inl w) => .corner w
    | .inl (.inr k) => .cluster k
    | .inr (.inl s) => .opposite s
    | .inr (.inr p) => .matched p
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (w | k) | (s | p) <;> rfl

def vertexEquiv (H I R : Type) : Vertex H I R ≃ (H ⊕ I) ⊕ (I ⊕ (R ⊕ R)) where
  toFun
    | .hub d => .inl (.inl d)
    | .u i => .inl (.inr i)
    | .z i => .inr (.inl i)
    | .parent r => .inr (.inr (.inl r))
    | .leaf r => .inr (.inr (.inr r))
  invFun
    | .inl (.inl d) => .hub d
    | .inl (.inr i) => .u i
    | .inr (.inl i) => .z i
    | .inr (.inr (.inl r)) => .parent r
    | .inr (.inr (.inr r)) => .leaf r
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (d | i) | (i | (r | r)) <;> rfl

def edgeEquiv (I K S P R : Type) :
    Edge I K S P R ≃ (((I ⊕ I) ⊕ (I ⊕ I)) ⊕ (I ⊕ K)) ⊕ ((K ⊕ (S × Bool)) ⊕ ((P × Bool) ⊕ R)) where
  toFun
    | .dw i => .inl (.inl (.inl (.inl i)))
    | .du i => .inl (.inl (.inl (.inr i)))
    | .yz i => .inl (.inl (.inr (.inl i)))
    | .uz i => .inl (.inl (.inr (.inr i)))
    | .wu i => .inl (.inr (.inl i))
    | .rw k => .inl (.inr (.inr k))
    | .ry k => .inr (.inl (.inl k))
    | .sw s b => .inr (.inl (.inr (s, b)))
    | .pu p b => .inr (.inr (.inl (p, b)))
    | .pendant r => .inr (.inr (.inr r))
  invFun
    | .inl (.inl (.inl (.inl i))) => .dw i
    | .inl (.inl (.inl (.inr i))) => .du i
    | .inl (.inl (.inr (.inl i))) => .yz i
    | .inl (.inl (.inr (.inr i))) => .uz i
    | .inl (.inr (.inl i)) => .wu i
    | .inl (.inr (.inr k)) => .rw k
    | .inr (.inl (.inl k)) => .ry k
    | .inr (.inl (.inr (s, b))) => .sw s b
    | .inr (.inr (.inl (p, b))) => .pu p b
    | .inr (.inr (.inr r)) => .pendant r
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (((i | i) | (i | i)) | (i | k)) | ((k | ⟨s, b⟩) | (⟨p, b⟩ | r)) <;> rfl

def fintypeParent {W K S P : Type} [Fintype W] [Fintype K] [Fintype S] [Fintype P] :
    Fintype (Parent W K S P) :=
  Fintype.ofEquiv _ (parentEquiv W K S P).symm

def fintypeVertex {H I R : Type} [Fintype H] [Fintype I] [Fintype R] :
    Fintype (Vertex H I R) :=
  Fintype.ofEquiv _ (vertexEquiv H I R).symm

def fintypeEdge {I K S P R : Type} [Fintype I] [Fintype K] [Fintype S] [Fintype P] [Fintype R] :
    Fintype (Edge I K S P R) :=
  Fintype.ofEquiv _ (edgeEquiv I K S P R).symm

structure Layout (H W I K S P : Type) where
  center : I → H
  twin : I → H
  corner : I → W
  clusterW : K → W
  clusterH : K → H
  opposite : S → Bool → W
  paired : P → Bool → I

namespace Layout

open PEqualNP.MetaComplexity.CoverPromise

def ends {H W I K S P : Type} (L : Layout H W I K S P) :
    Edge I K S P (Parent W K S P) → Vertex H I (Parent W K S P) × Vertex H I (Parent W K S P)
  | .dw i => (.hub (L.center i), .parent (.corner (L.corner i)))
  | .du i => (.hub (L.center i), .u i)
  | .yz i => (.hub (L.twin i), .z i)
  | .uz i => (.u i, .z i)
  | .wu i => (.parent (.corner (L.corner i)), .u i)
  | .rw k => (.parent (.cluster k), .parent (.corner (L.clusterW k)))
  | .ry k => (.parent (.cluster k), .hub (L.clusterH k))
  | .sw s b => (.parent (.opposite s), .parent (.corner (L.opposite s b)))
  | .pu p b => (.parent (.matched p), .u (L.paired p b))
  | .pendant r => (.parent r, .leaf r)

def edge {H W I K S P : Type} (L : Layout H W I K S P) (e : Edge I K S P (Parent W K S P)) :
    Sym2 (Vertex H I (Parent W K S P)) :=
  s((L.ends e).1, (L.ends e).2)

def graph {H W I K S P : Type} (L : Layout H W I K S P) :
    SimpleGraph (Vertex H I (Parent W K S P)) :=
  SimpleGraph.fromEdgeSet (Set.range L.edge)

theorem different {H W I K S P : Type} (L : Layout H W I K S P)
    (e : Edge I K S P (Parent W K S P)) : (L.ends e).1 ≠ (L.ends e).2 := by
  cases e <;> simp [ends]

theorem adjacent {H W I K S P : Type} (L : Layout H W I K S P)
    (e : Edge I K S P (Parent W K S P)) : L.graph.Adj (L.ends e).1 (L.ends e).2 :=
  ⟨⟨e, rfl⟩, L.different e⟩

theorem injective_edge {H W I K S P : Type} (L : Layout H W I K S P)
    (hj : ∀ i j, L.center i = L.center j → L.corner i = L.corner j → i = j)
    (hs : ∀ s, Function.Injective (L.opposite s))
    (hp : ∀ p, Function.Injective (L.paired p)) : Function.Injective L.edge := by
  intro x y h
  rw [edge, edge, Sym2.eq_iff] at h
  cases x <;> cases y <;> simp [ends] at h ⊢ <;> first
    | contradiction
    | exact hj _ _ h.1 h.2
    | exact h
    | exact h.1
    | exact h.2
    | (obtain ⟨rfl, he⟩ := h; exact ⟨rfl, hs _ he⟩)
    | (obtain ⟨rfl, he⟩ := h; exact ⟨rfl, hp _ he⟩)

theorem edgeSet_eq {H W I K S P : Type} (L : Layout H W I K S P) :
    L.graph.edgeSet = Set.range L.edge := by
  apply Set.Subset.antisymm
  · rw [graph, SimpleGraph.edgeSet_fromEdgeSet]
    exact Set.sdiff_subset
  · rintro _ ⟨e, rfl⟩
    exact L.adjacent e

theorem parent_card {W K S P : Type} [Fintype W] [Fintype K] [Fintype S] [Fintype P] :
    @Fintype.card (Parent W K S P) fintypeParent =
      Fintype.card W + Fintype.card K + Fintype.card S + Fintype.card P := by
  letI : Fintype (Parent W K S P) := fintypeParent
  rw [Fintype.card_congr (parentEquiv W K S P)]
  simp [Nat.add_assoc]

theorem edge_count {H W I K S P : Type} [Fintype H] [Fintype W] [Fintype I] [Fintype K]
    [Fintype S] [Fintype P] (L : Layout H W I K S P)
    (hj : ∀ i j, L.center i = L.center j → L.corner i = L.corner j → i = j)
    (hs : ∀ s, Function.Injective (L.opposite s))
    (hp : ∀ p, Function.Injective (L.paired p)) :
    L.graph.edgeSet.ncard = 5 * Fintype.card I + Fintype.card W +
      3 * Fintype.card K + 3 * Fintype.card S + 3 * Fintype.card P := by
  letI : Fintype (Parent W K S P) := fintypeParent
  letI : Fintype (Edge I K S P (Parent W K S P)) := fintypeEdge
  rw [L.edgeSet_eq, Set.ncard_range_of_injective (L.injective_edge hj hs hp),
    Nat.card_eq_fintype_card, Fintype.card_congr (edgeEquiv I K S P (Parent W K S P))]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  have hpc := @parent_card W K S P _ _ _ _
  omega

theorem cover_lower {H W I K S P : Type} [Fintype H] [Fintype W] [Fintype I] [Fintype K]
    [Fintype S] [Fintype P] (L : Layout H W I K S P)
    (C : Finset (Vertex H I (Parent W K S P))) (hc : IsVertexCover L.graph C) :
    Fintype.card I + @Fintype.card (Parent W K S P) fintypeParent ≤ C.card := by
  letI : Fintype (Parent W K S P) := fintypeParent
  classical
  let owner : Vertex H I (Parent W K S P) → Option (I ⊕ Parent W K S P)
    | .hub _ => none | .u i | .z i => some (.inl i)
    | .parent r | .leaf r => some (.inr r)
  let pick : I ⊕ Parent W K S P → ↥C := fun tag => match tag with
    | .inl i => if h : Vertex.u i ∈ C then ⟨.u i, h⟩ else
        ⟨.z i, (hc _ _ (L.adjacent (.uz i))).resolve_left h⟩
    | .inr r => if h : Vertex.parent r ∈ C then ⟨.parent r, h⟩ else
        ⟨.leaf r, (hc _ _ (L.adjacent (.pendant r))).resolve_left h⟩
  have back (t) : owner (pick t).val = some t := by
    cases t <;> simp only [pick] <;> split <;> rfl
  have inj : Function.Injective pick := by
    intro x y eq
    exact Option.some.inj ((back x).symm.trans ((congrArg (fun t => owner t.val) eq).trans (back y)))
  simpa using Fintype.card_le_of_injective pick inj

def base {H W I K S P : Type} (L : Layout H W I K S P) (d : H) (w : W) : Prop :=
  ∃ i, L.center i = d ∧ L.corner i = w

structure SquareConditions {H W I K S P : Type} (L : Layout H W I K S P) : Prop where
  baseSquare : ∀ d e w v, L.base d w → L.base e w → L.base e v → L.base d v →
    d = e ∨ w = v
  oneIncidence : ∀ i j, L.center i = L.center j → L.corner i = L.corner j → i = j
  twinAway : ∀ i, ¬ L.base (L.twin i) (L.corner i)
  clusterAway : ∀ k, ¬ L.base (L.clusterH k) (L.clusterW k)
  clusterUnique : ∀ k l, L.clusterH k = L.clusterH l → L.clusterW k = L.clusterW l → k = l
  oppositeUnique : ∀ s t a b c d, a ≠ b → c ≠ d →
    L.opposite s a = L.opposite t c → L.opposite s b = L.opposite t d → s = t
  oppositeAway : ∀ s a b d, a ≠ b → L.base d (L.opposite s a) → ¬ L.base d (L.opposite s b)
  pairedUnique : ∀ p q a b, L.paired p a = L.paired q b → p = q
  pairedHubs : ∀ p a b, a ≠ b → L.center (L.paired p a) ≠ L.center (L.paired p b)
  pairedCorners : ∀ p a b, a ≠ b → L.corner (L.paired p a) ≠ L.corner (L.paired p b)

private def touch {H W I K S P : Type} (L : Layout H W I K S P) :
    Vertex H I (Parent W K S P) → Vertex H I (Parent W K S P) → Prop
  | .hub d, .parent (.corner w) | .parent (.corner w), .hub d => L.base d w
  | .hub d, .u i | .u i, .hub d => L.center i = d
  | .hub d, .z i | .z i, .hub d => L.twin i = d
  | .u i, .z j | .z j, .u i => i = j
  | .parent (.corner w), .u i | .u i, .parent (.corner w) => L.corner i = w
  | .parent (.cluster k), .parent (.corner w)
  | .parent (.corner w), .parent (.cluster k) => L.clusterW k = w
  | .parent (.cluster k), .hub d | .hub d, .parent (.cluster k) => L.clusterH k = d
  | .parent (.opposite s), .parent (.corner w)
  | .parent (.corner w), .parent (.opposite s) => ∃ b, L.opposite s b = w
  | .parent (.matched p), .u i | .u i, .parent (.matched p) => ∃ b, L.paired p b = i
  | .parent p, .leaf q | .leaf q, .parent p => p = q
  | _, _ => False

private theorem touch_of_adj {H W I K S P : Type} (L : Layout H W I K S P)
    {u v : Vertex H I (Parent W K S P)} (ha : L.graph.Adj u v) : L.touch u v := by
  obtain ⟨e, he⟩ := ha.1
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals cases e <;> simp [ends, touch, base] <;> first
    | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl⟩ | (rename_i r; cases r <;> rfl)

set_option maxHeartbeats 8000000 in
private theorem noSquareTouch {H W I K S P : Type} (L : Layout H W I K S P)
    (hc : L.SquareConditions) (x y z t : Vertex H I (Parent W K S P))
    (xy : L.touch x y) (yz : L.touch y z) (zt : L.touch z t) (tx : L.touch t x) :
    x = z ∨ y = t := by
  obtain ⟨hbase, hi, ht, hk, hu, ho, hd, hp, hh, hw⟩ := hc
  have own (i : I) : L.base (L.center i) (L.corner i) := ⟨i, rfl, rfl⟩
  rcases x with x | x | x | (x | x | x | x) | x <;>
    rcases y with y | y | y | (y | y | y | y) | y <;> simp [touch] at xy <;>
    rcases z with z | z | z | (z | z | z | z) | z <;> simp [touch] at yz <;>
    rcases t with t | t | t | (t | t | t | t) | t <;> simp [touch] at zt tx <;>
    (try simp_all only [Vertex.hub.injEq, Vertex.u.injEq, Vertex.z.injEq, Vertex.parent.injEq,
      Vertex.leaf.injEq, Parent.corner.injEq, Parent.cluster.injEq,
      Parent.opposite.injEq, Parent.matched.injEq]) <;> grind

theorem no_four_cycle {H W I K S P : Type} (L : Layout H W I K S P)
    (hc : L.SquareConditions) (a b c d : Vertex H I (Parent W K S P))
    (hac : a ≠ c) (hbd : b ≠ d) (hab : L.graph.Adj a b) (hbc : L.graph.Adj b c)
    (hcd : L.graph.Adj c d) : ¬ L.graph.Adj d a := by
  intro hda
  exact (L.noSquareTouch hc a b c d (L.touch_of_adj hab) (L.touch_of_adj hbc)
    (L.touch_of_adj hcd) (L.touch_of_adj hda)).elim hac hbd

def inCluster {H W I K S P : Type} (L : Layout H W I K S P) (i : I) (k : K) : Prop :=
  L.corner i = L.clusterW k ∧ L.twin i = L.clusterH k

def clusterOutput {H W I K S P : Type} (L : Layout H W I K S P)
    (x : Vertex H I (Parent W K S P) → Prop) (k : K) : Prop :=
  (∃ i, L.inCluster i k ∧ x (.z i) ∧
    (x (.parent (.corner (L.clusterW k))) ∨ x (.hub (L.clusterH k)) ∨ x (.u i))) ∧
  (x (.hub (L.clusterH k)) ∨ ∃ j, L.inCluster j k ∧ x (.u j))

def direction {H W I K S P : Type} (L : Layout H W I K S P)
    (x : Vertex H I (Parent W K S P) → Prop) (d y : H) : Prop :=
  ∃ i, L.center i = d ∧ L.twin i = y ∧ (x (.parent (.corner (L.corner i))) ∨ x (.u i))

def hubOutput {H W I K S P : Type} (L : Layout H W I K S P)
    (x : Vertex H I (Parent W K S P) → Prop) (d : H) : Prop :=
  x (.hub d) ∧ ∃ y, (x (.hub y) ∨ L.direction x d y) ∧
    (L.direction x d y ∨ L.direction x y d)

def exposed {H W I K S P : Type} (L : Layout H W I K S P)
    (x : Vertex H I (Parent W K S P) → Prop) : Prop :=
  (∃ r, x (.parent r) ∧ x (.leaf r)) ∨
  (∃ k, x (.parent (.cluster k)) ∧
    (x (.parent (.corner (L.clusterW k))) ∨ x (.hub (L.clusterH k)))) ∨
  (∃ s b, x (.parent (.opposite s)) ∧ x (.parent (.corner (L.opposite s b)))) ∨
  (∃ p b, x (.parent (.matched p)) ∧ x (.u (L.paired p b))) ∨
  (∃ i, x (.parent (.corner (L.corner i))) ∧ x (.u i)) ∨
  (∃ k, L.clusterOutput x k) ∨ ∃ d, L.hubOutput x d

private def Fires {H W I K S P : Type} (L : Layout H W I K S P)
    (x : Vertex H I (Parent W K S P) → Prop) :=
  ∃ u v, L.graph.Adj u v ∧ x u ∧ x v

private theorem edge_fires {H W I K S P : Type} (L : Layout H W I K S P)
    (x : Vertex H I (Parent W K S P) → Prop) (e)
    (h : x (L.ends e).1) (k : x (L.ends e).2) : L.Fires x :=
  ⟨_, _, L.adjacent e, h, k⟩

private theorem direction_sound {H W I K S P : Type} (L : Layout H W I K S P)
    {x : Vertex H I (Parent W K S P) → Prop} {d y} (on : x (.hub d))
    (h : L.direction x d y) : L.Fires x := by
  obtain ⟨i, rfl, _, hw | hu⟩ := h
  · exact L.edge_fires x (.dw i) on hw
  · exact L.edge_fires x (.du i) on hu

private theorem cluster_sound {H W I K S P : Type} (L : Layout H W I K S P)
    {x : Vertex H I (Parent W K S P) → Prop} {k} (h : L.clusterOutput x k) : L.Fires x := by
  obtain ⟨⟨i, hi, hz, hw | hy | hu⟩, second⟩ := h
  · rcases second with hy | ⟨j, hj, hu⟩
    · exact L.edge_fires x (.yz i) (by simpa only [ends, hi.2] using hy) hz
    · exact L.edge_fires x (.wu j) (by simpa only [ends, hj.1] using hw) hu
  · exact L.edge_fires x (.yz i) (by simpa only [ends, hi.2] using hy) hz
  · exact L.edge_fires x (.uz i) hu hz

private theorem hub_sound {H W I K S P : Type} (L : Layout H W I K S P)
    {x : Vertex H I (Parent W K S P) → Prop} {d} (h : L.hubOutput x d) : L.Fires x := by
  obtain ⟨hd, y, hy | ha, second⟩ := h
  · rcases second with ha | hb
    · exact L.direction_sound hd ha
    · exact L.direction_sound hy hb
  · exact L.direction_sound hd ha

theorem exposed_exact {H W I K S P : Type} (L : Layout H W I K S P)
    (assigned : ∀ i, ∃ k, L.inCluster i k) (x : Vertex H I (Parent W K S P) → Prop) :
    L.exposed x ↔ ∃ u v, L.graph.Adj u v ∧ x u ∧ x v := by
  constructor
  · rintro (⟨r, h, z⟩ | ⟨k, h, w | y⟩ | ⟨s, b, h, w⟩ | ⟨p, b, h, u⟩ | ⟨i, w, u⟩ | ⟨k, h⟩ | ⟨d, h⟩)
    · exact L.edge_fires x (.pendant r) h z
    · exact L.edge_fires x (.rw k) h w
    · exact L.edge_fires x (.ry k) h y
    · exact L.edge_fires x (.sw s b) h w
    · exact L.edge_fires x (.pu p b) h u
    · exact L.edge_fires x (.wu i) w u
    · exact L.cluster_sound h
    · exact L.hub_sound h
  · rintro ⟨u, v, ha, hu, hv⟩
    obtain ⟨e, he⟩ := ha.1
    have both : x (L.ends e).1 ∧ x (L.ends e).2 := by
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    clear he hu hv ha u v
    rcases both with ⟨a, b⟩
    unfold exposed
    cases e with
    | dw i =>
      have dir : L.direction x (L.center i) (L.twin i) := ⟨i, rfl, rfl, .inl b⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (.inr ⟨_, a, _, .inr dir, .inl dir⟩)))))
    | du i =>
      have dir : L.direction x (L.center i) (L.twin i) := ⟨i, rfl, rfl, .inr b⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (.inr ⟨_, a, _, .inr dir, .inl dir⟩)))))
    | yz i =>
      obtain ⟨k, h⟩ := assigned i
      have hy : x (.hub (L.clusterH k)) := h.2 ▸ a
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (.inl
        ⟨k, ⟨i, h, b, .inr (.inl hy)⟩, .inl hy⟩)))))
    | uz i =>
      obtain ⟨k, h⟩ := assigned i
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (.inl
        ⟨k, ⟨i, h, b, .inr (.inr a)⟩, .inr ⟨i, h, a⟩⟩)))))
    | wu i => exact Or.inr (Or.inr (Or.inr (Or.inr (.inl ⟨i, a, b⟩))))
    | rw k => exact Or.inr (.inl ⟨k, a, .inl b⟩)
    | ry k => exact Or.inr (.inl ⟨k, a, .inr b⟩)
    | sw s bit => exact Or.inr (Or.inr (.inl ⟨s, bit, a, b⟩))
    | pu p bit => exact Or.inr (Or.inr (Or.inr (.inl ⟨p, bit, a, b⟩)))
    | pendant r => exact .inl ⟨r, a, b⟩

end Layout

namespace Template

open Model

def graphHub (r : Fin 4) (side : Bool) : Fin 4 :=
  match r with
  | 0 => if side then 2 else 0 | 1 => if side then 3 else 0
  | 2 => if side then 3 else 1 | 3 => if side then 2 else 1

def oppRole (pair side : Bool) : Fin 4 :=
  if pair then (if side then 3 else 1) else (if side then 2 else 0)

private theorem role_separation : ∀ r s t, clusterHub r s ≠ graphHub r t := by decide
private theorem opposite_role : ∀ p a b, a ≠ b → oppRole p a ≠ oppRole p b := by decide
private theorem opposite_neighbours : ∀ p a b s t, a ≠ b →
    graphHub (oppRole p a) s ≠ graphHub (oppRole p b) t := by decide
private theorem pair_from_role : ∀ p q a b, oppRole p a = oppRole q b → p = q := by decide

abbrev Inc (O : Type) := O × Fin 4 × Bool
abbrev Opp (O : Type) := O × Bool
abbrev Pair (O : Type) := O × Bool × Bool

def key {H W O : Type} (u : O → Tuple H W) (i : Inc O) : ClusterKey H W :=
  (i.2, (u i.1).2 i.2.1, (u i.1).1 (clusterHub i.2.1 i.2.2))

abbrev Used {H W O : Type} (u : O → Tuple H W) := Set.range (key u)

def layout {H W O : Type} (u : O → Tuple H W) :
    Layout (Fin 4 × H) (Fin 4 × W) (Inc O) (Used u) (Opp O) (Pair O) where
  center i := let j := graphHub i.2.1 i.2.2; (j, (u i.1).1 j)
  twin i := let j := clusterHub i.2.1 i.2.2; (j, (u i.1).1 j)
  corner i := (i.2.1, (u i.1).2 i.2.1)
  clusterW k := (k.val.1.1, k.val.2.1)
  clusterH k := (clusterHub k.val.1.1 k.val.1.2, k.val.2.2)
  opposite s b := let r := oppRole s.2 b; (r, (u s.1).2 r)
  paired p b := (p.1, oppRole p.2.1 b, p.2.2)

theorem assigned {H W O : Type} (u : O → Tuple H W) (i : Inc O) :
    ∃ k, (layout u).inCluster i k :=
  ⟨⟨key u i, i, rfl⟩, rfl, rfl⟩

theorem opposite_injective {H W O : Type} (u : O → Tuple H W) (s : Opp O) :
    Function.Injective ((layout u).opposite s) := by
  intro a b h
  by_contra ne
  exact opposite_role s.2 a b ne (congrArg Prod.fst h)

theorem paired_injective {H W O : Type} (u : O → Tuple H W) (p : Pair O) :
    Function.Injective ((layout u).paired p) := by
  intro a b h
  by_contra ne
  exact opposite_role p.2.1 a b ne (congrArg (fun i : Inc O => i.2.1) h)

private theorem base_roles {H W O : Type} (u : O → Tuple H W) {d w} (h : (layout u).base d w) :
    ∃ b, d.1 = graphHub w.1 b := by
  obtain ⟨i, rfl, rfl⟩ := h
  exact ⟨i.2.2, rfl⟩

theorem square_conditions {H W O : Type} (u : O → Tuple H W)
    (square : ∀ d e w v, (layout u).base d w → (layout u).base e w →
      (layout u).base e v → (layout u).base d v → d = e ∨ w = v)
    (single : ∀ i j, (layout u).center i = (layout u).center j →
      (layout u).corner i = (layout u).corner j → i = j)
    (opposite : ∀ s t a b c d, a ≠ b → c ≠ d →
      (layout u).opposite s a = (layout u).opposite t c →
      (layout u).opposite s b = (layout u).opposite t d → s = t) :
    (layout u).SquareConditions := by
  refine ⟨square, single, ?_, ?_, ?_, opposite, ?_, ?_, ?_, ?_⟩
  · intro i h
    obtain ⟨b, hb⟩ := base_roles u h
    exact role_separation i.2.1 i.2.2 b hb
  · intro k h
    obtain ⟨b, hb⟩ := base_roles u h
    exact role_separation k.val.1.1 k.val.1.2 b hb
  · rintro ⟨⟨⟨r, a⟩, w, h⟩, hk⟩ ⟨⟨⟨s, b⟩, v, j⟩, hl⟩ ha hb
    have hr : r = s := congrArg Prod.fst hb
    subst s
    have how : ∀ (i : Fin 4) (a b : Bool), clusterHub i a = clusterHub i b → a = b := by decide
    have hab := how r a b (congrArg Prod.fst ha)
    cases hab
    apply Subtype.ext
    simp only [Prod.mk.injEq, true_and, and_self, eq_self]
    exact ⟨congrArg Prod.snd hb, congrArg Prod.snd ha⟩
  · intro s a b d ne ha hb
    obtain ⟨i, hi⟩ := base_roles u ha
    obtain ⟨j, hj⟩ := base_roles u hb
    exact opposite_neighbours s.2 a b i j ne (hi.symm.trans hj)
  · rintro ⟨s, p, i⟩ ⟨t, q, j⟩ a b h
    change (s, oppRole p a, i) = (t, oppRole q b, j) at h
    obtain ⟨rfl, he, rfl⟩ := Prod.mk.inj h |>.imp_right Prod.mk.inj
    rw [pair_from_role _ _ _ _ he]
  · intro p a b ne h
    exact opposite_neighbours p.2.1 a b p.2.2 p.2.2 ne (congrArg Prod.fst h)
  · intro p a b ne h
    exact opposite_role p.2.1 a b ne (congrArg Prod.fst h)

end Template

namespace Clean

open Finset Overlap Model Obstructions Template

def col {A : Type} (f : Fin 4 → A) := (vectorEquiv A).symm f

def patternOf {A : Type} [DecidableEq A] (f : Fin 4 → A) : Pattern :=
  ⟨mask (col f), List.mem_toFinset.mpr (mask_spec _).1⟩

def shape {H W : Type} [DecidableEq H] [DecidableEq W] (f : Fin 4 → Tuple H W) : Shape :=
  (fun r => patternOf (fun i => (f i).1 r), fun r => patternOf (fun i => (f i).2 r))

def pack {H W : Type} [DecidableEq H] [DecidableEq W] (f : Fin 4 → Tuple H W) :
    Class H W (shape f) :=
  (fun r => ⟨col (fun i => (f i).1 r), rfl⟩, fun r => ⟨col (fun i => (f i).2 r), rfl⟩)

theorem unpack {H W : Type} [DecidableEq H] [DecidableEq W] (f : Fin 4 → Tuple H W) (i : Fin 4) :
    slot (pack f) i = f i := by
  fin_cases i <;> rfl

set_option maxRecDepth 8192 in
theorem excludes {q : Nat} {hq : 0 < q} {x : Experiment q} {keep}
    (sub : keep ⊆ raw hq x) (clean : ∀ b ∈ bad hq x, ¬ b ⊆ keep)
    (f : Fin 4 → Tuple (Hub q) (Corner q)) (hf : ∀ i, f i ∈ keep) : ¬low (shape f) := by
  letI : Fintype (Class (Hub q) (Corner q) (shape f)) := fintypeClass (shape f)
  intro hl
  let u := pack f
  have presentU : u ∈ present hq (shape f) x := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, all_slots_hit _ (fun i => ?_)⟩
    rw [show u = pack f from rfl, unpack]
    exact (mem_filter.mp (sub (hf i))).2
  have badU : univ.image (slot u) ∈ bad hq x := by
    unfold bad badOf
    apply mem_biUnion.mpr
    exact ⟨shape f, (mem_lowShapes _).mpr hl, mem_image.mpr ⟨u, presentU, rfl⟩⟩
  apply clean _ badU
  rintro _ hv
  obtain ⟨i, _, rfl⟩ := mem_image.mp hv
  simpa [u, unpack] using hf i

def supported {H W : Type} (v : Tuple H W) (d : Fin 4 × H) (w : Fin 4 × W) : Prop :=
  realEdge w.1 d.1 ∧ v.1 d.1 = d.2 ∧ v.2 w.1 = w.2

private theorem each_shape (p : Fin 4 → Pattern) (f : Fin 4 → List Nat)
    (h : ∀ i, (p i).val ∈ f i) : Each f (shapeMasks p) :=
  ⟨h 0, h 1, h 2, h 3⟩

theorem square_low {H W : Type} [DecidableEq H] [DecidableEq W]
    (f : Fin 4 → Tuple H W) {d e : Fin 4 × H} {w v : Fin 4 × W}
    (de : d ≠ e) (wv : w ≠ v) (x : supported (f 0) d w) (y : supported (f 1) e w)
    (z : supported (f 2) e v) (t : supported (f 3) d v) : low (shape f) := by
  apply cycle_bound d.1 e.1 w.1 v.1
  · simp [x.1, y.1, z.1, t.1]
  · apply each_shape; intro r
    apply hub_mask_mem
    · intro h; have he : r = d.1 := by simpa using h
      subst r; exact x.2.1.trans t.2.1.symm
    · intro h; have he : r = e.1 := by simpa using h
      subst r; exact y.2.1.trans z.2.1.symm
    · intro p q he
      have pp : r = d.1 := by simpa using p
      have qq : r = e.1 := by simpa using q
      change (f 0).1 r = (f 1).1 r at he
      apply de
      apply Prod.ext (pp.symm.trans qq)
      exact x.2.1.symm.trans ((pp ▸ he).trans (by simpa [← pp, ← qq] using y.2.1))
  · apply each_shape; intro r
    apply corner_mask_mem
    · intro h; have he : r = w.1 := by simpa using h
      subst r; exact x.2.2.trans y.2.2.symm
    · intro h; have he : r = v.1 := by simpa using h
      subst r; exact z.2.2.trans t.2.2.symm
    · intro p q he
      have pp : r = w.1 := by simpa using p
      have qq : r = v.1 := by simpa using q
      change (f 0).2 r = (f 2).2 r at he
      apply wv
      apply Prod.ext (pp.symm.trans qq)
      exact x.2.2.symm.trans ((pp ▸ he).trans (by simpa [← pp, ← qq] using z.2.2))

def alt {H W : Type} (u v : Tuple H W) : Fin 4 → Tuple H W := (Four.mk u v u v).atRole

private theorem alt_masks {H W : Type} [DecidableEq H] [DecidableEq W] {u v : Tuple H W} :
    (∀ r, ((shape (alt u v)).1 r).val = if u.1 r = v.1 r then 63 else 18) ∧
    (∀ r, ((shape (alt u v)).2 r).val = if u.2 r = v.2 r then 63 else 18) := by
  constructor <;> intro r <;> exact alternating_mask _ _

private theorem alt_bounds {H W : Type} [DecidableEq H] [DecidableEq W] {u v : Tuple H W} (ne : u ≠ v) :
    let s := shape (alt u v)
    (repeatsJ (shapeMasks s.1) (shapeMasks s.2) → low s) ∧
    (repeatsS (shapeMasks s.2) → low s) := by
  let s := shape (alt u v)
  obtain ⟨h, w⟩ := alt_masks (u := u) (v := v)
  have hm : Each pairDomain (shapeMasks s.1) := by
    apply each_shape; intro i; dsimp [s]; rw [h]; split <;> simp [pairDomain]
  have wm : Each pairDomain (shapeMasks s.2) := by
    apply each_shape; intro i; dsimp [s]; rw [w]; split <;> simp [pairDomain]
  have nd : sameTuple (shapeMasks s.1) (shapeMasks s.2) = false := by
    by_contra! hd
    simp [sameTuple, shapeMasks, s, h, w] at hd
    apply ne
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp_all
  have bound := duplicate_bounds hm wm nd
  exact ⟨fun j => (bound.1 j).trans (by decide), fun j => (bound.2 j).trans (by decide)⟩

theorem duplicateJ_low {H W : Type} [DecidableEq H] [DecidableEq W]
    {u v : Tuple H W} (ne : u ≠ v) {d w}
    (p : supported u d w) (q : supported v d w) : low (shape (alt u v)) := by
  apply (alt_bounds ne).1
  obtain ⟨h, w'⟩ := alt_masks (u := u) (v := v)
  have eh := p.2.1.trans q.2.1.symm
  have ew := p.2.2.trans q.2.2.symm
  obtain ⟨d, dh⟩ := d; obtain ⟨w, ww⟩ := w
  have j := p.1
  dsimp at j eh ew
  fin_cases d <;> fin_cases w <;> simp_all [realEdge, repeatsJ, shapeMasks]

theorem duplicateS_low {H W : Type} [DecidableEq H] [DecidableEq W]
    {u v : Tuple H W} (ne : u ≠ v) (p : Bool)
    (ha : u.2 (oppRole p false) = v.2 (oppRole p false))
    (hb : u.2 (oppRole p true) = v.2 (oppRole p true)) : low (shape (alt u v)) := by
  apply (alt_bounds ne).2
  have w := (alt_masks (u := u) (v := v)).2
  cases p <;> simp_all [repeatsS, shapeMasks, oppRole]

end Clean

namespace Compiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset

inductive Expr (V N : Type) where
  | input (v : V) | ref (i : N) | zero
  | binary (isAnd : Bool) (a b : Expr V N)

namespace Expr

def weight {V N : Type} : Expr V N → Nat
  | .binary _ a b => a.weight + b.weight + 1
  | _ => 0

def meaning {V N : Type} (x : V → Prop) (val : N → Prop) : Expr V N → Prop
  | .input v => x v | .ref i => val i | .zero => False
  | .binary op a b => if op then a.meaning x val ∧ b.meaning x val
    else a.meaning x val ∨ b.meaning x val

def Uses {V N : Type} (i : N) : Expr V N → Prop
  | .ref j => i = j | .binary _ a b => a.Uses i ∨ b.Uses i | _ => False

def foldOr {V N : Type} (seed : Expr V N) (ls : List (Expr V N)) := ls.foldl (.binary false) seed

theorem fold_meaning {V N : Type} (ls : List (Expr V N)) (seed) (x : V → Prop) (v : N → Prop) :
    (foldOr seed ls).meaning x v ↔ seed.meaning x v ∨ ∃ e ∈ ls, e.meaning x v := by
  induction ls generalizing seed with
  | nil => simp [foldOr]
  | cons a ls ih =>
    change (foldOr (.binary false seed a) ls).meaning x v ↔ _
    rw [ih]; simp [meaning, or_assoc]

theorem fold_weight {V N : Type} (ls : List (Expr V N)) (seed) :
    (foldOr seed ls).weight = seed.weight + ls.length + (ls.map weight).sum := by
  induction ls generalizing seed with
  | nil => simp [foldOr]
  | cons a ls ih =>
    change (foldOr (.binary false seed a) ls).weight = _
    rw [ih]; simp [weight]; omega

theorem fold_uses {V N : Type} (ls : List (Expr V N)) (seed) (i : N) :
    (foldOr seed ls).Uses i ↔ seed.Uses i ∨ ∃ e ∈ ls, e.Uses i := by
  induction ls generalizing seed with
  | nil => simp [foldOr]
  | cons a ls ih =>
    change (foldOr (.binary false seed a) ls).Uses i ↔ _
    rw [ih]; simp [Uses, or_assoc]

end Expr

abbrev Input (n : Nat) := Fin n → Bool
private def wires {n : Nat} (p : List Gate) (x : Input n) := (Circuit.mk p 0).wires (List.ofFn x)
private def valAt {n : Nat} (p : List Gate) (i : Nat) (x : Input n) := (wires p x).getD i false
private def Has {n : Nat} (p : List Gate) (f : Input n → Prop) := ∃ i, i < n + p.length ∧
  ∀ x, valAt p i x = true ↔ f x
private def mono (p : List Gate) := Monotone2 ⟨p, 0⟩

private theorem wires_step {n : Nat} (p : List Gate) (g : Gate) (x : Input n) :
    wires (p ++ [g]) x = wires p x ++ [g.op.eval (g.inputs.map fun i => valAt p i x)] := by
  simp [wires, valAt, Circuit.wires, List.foldl_append]

private theorem len_wires {n : Nat} (p : List Gate) (x : Input n) :
    (wires p x).length = n + p.length := by
  induction p using List.reverseRecOn with
  | nil => simp [wires, Circuit.wires]
  | append_singleton p g ih =>
    simp [wires, Circuit.wires, List.foldl_append] at ih ⊢
    omega

private theorem stays_one {n : Nat} {p : List Gate} {f : Input n → Prop}
    (h : Has p f) (g : Gate) : Has (p ++ [g]) f := by
  obtain ⟨i, hi, ok⟩ := h
  refine ⟨i, by simp; omega, fun x => ?_⟩
  have hi' : i < (wires p x).length := by simpa [len_wires] using hi
  unfold valAt; rw [wires_step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi', ← List.getD_eq_getElem?_getD]
  exact ok x

private theorem stays {n : Nat} {p : List Gate} {f : Input n → Prop}
    (h : Has p f) (t : List Gate) : Has (p ++ t) f := by
  induction t using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton t g ih => simpa [List.append_assoc] using stays_one ih g

private theorem new_wire {n : Nat} (p : List Gate) (g : Gate) :
    Has (p ++ [g]) (fun x : Input n =>
      g.op.eval (g.inputs.map fun i => valAt p i x) = true) := by
  refine ⟨n + p.length, by simp, fun x => ?_⟩
  unfold valAt; rw [wires_step]
  rw [← len_wires p x, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  simp [valAt]

private theorem join_gate {n : Nat} {p : List Gate} {f g : Input n → Prop}
    (op : Bool) (ha : Has p f) (hb : Has p g) :
    ∃ t : List Gate, mono t ∧ t.length = 1 ∧
      Has (p ++ t) (fun x => if op then f x ∧ g x else f x ∨ g x) := by
  obtain ⟨i, _, a⟩ := ha
  obtain ⟨j, _, b⟩ := hb
  let gate : Gate := ⟨if op then GateOp.and else GateOp.or, [i, j]⟩
  refine ⟨[gate], ?_, rfl, ?_⟩
  · cases op <;> simp [mono, Monotone2, gate]
  · have h := new_wire (n := n) p gate
    convert h using 1
    funext x
    cases op <;> simp [gate, GateOp.eval, a, b]

private theorem mono_append {a b : List Gate} (ha : mono a) (hb : mono b) : mono (a ++ b) := by
  intro g hg
  exact (List.mem_append.mp hg).elim (ha g) (hb g)

private theorem build_expr {V N : Type} {n : Nat} (label : V ≃ Fin n) (value : N → Input n → Prop)
    (e : Expr V N) (p : List Gate) (input : ∀ v, Has p (fun x => x (label v) = true))
    (zero : Has p (fun _ : Input n => False))
    (avail : ∀ i, e.Uses i → Has p (value i)) :
    ∃ t, mono t ∧ t.length = e.weight ∧ Has (p ++ t)
      (fun x => e.meaning (fun v => x (label v) = true) (fun i => value i x)) := by
  induction e generalizing p with
  | input v => exact ⟨[], by simp [mono, Monotone2], rfl, by simpa [Expr.meaning] using input v⟩
  | ref i => exact ⟨[], by simp [mono, Monotone2], rfl, by simpa [Expr.meaning] using avail i rfl⟩
  | zero => exact ⟨[], by simp [mono, Monotone2], rfl, by simpa [Expr.meaning] using zero⟩
  | binary op a b ia ib =>
    obtain ⟨ta, ma, la, wa⟩ := ia p input zero (fun i hi => avail i (.inl hi))
    obtain ⟨tb, mb, lb, wb⟩ := ib (p ++ ta) (fun v => stays (input v) ta) (stays zero ta)
      (fun i hi => stays (avail i (.inr hi)) ta)
    obtain ⟨tc, mc, lc, wc⟩ := join_gate op (stays wa tb) wb
    exact ⟨ta ++ tb ++ tc, mono_append (mono_append ma mb) mc,
      by simp [la, lb, lc, Expr.weight, Nat.add_assoc], by simpa [List.append_assoc, Expr.meaning] using wc⟩

theorem compile {V N : Type} {n : Nat} [Fintype N] [DecidableEq N] (label : V ≃ Fin n)
    (rank : N → Nat) (recipe : N → Expr V N) (value : N → Input n → Prop)
    (prior : ∀ i j, (recipe i).Uses j → rank j < rank i)
    (correct : ∀ i x, (recipe i).meaning (fun v => x (label v) = true) (fun j => value j x)
      ↔ value i x) (out : N) :
    ∃ C : Circuit, Monotone2 C ∧ C.size = 1 + ∑ i, (recipe i).weight ∧
      ∀ x, C.eval (List.ofFn x) = true ↔ value out x := by
  classical
  have finish (todo : Finset N) (p : List Gate) (inputs : ∀ v, Has p (fun x => x (label v) = true))
      (zero : Has p (fun _ : Input n => False)) (ready : ∀ i ∉ todo, Has p (value i)) :
      ∃ t, mono t ∧ t.length = ∑ i ∈ todo, (recipe i).weight ∧
        ∀ i, Has (p ++ t) (value i) := by
    induction todo using Finset.strongInductionOn generalizing p with
    | _ todo ih =>
      by_cases hn : todo.Nonempty
      · obtain ⟨i, hi, least⟩ := todo.exists_min_image rank hn
        obtain ⟨t, mt, lt, wi⟩ := build_expr label value (recipe i) p inputs zero
          (fun j hj => ready j (fun hmem => (prior i j hj).not_ge (least j hmem)))
        have vEq : (fun x => (recipe i).meaning (fun v => x (label v) = true)
          (fun j => value j x)) = value i := funext fun x => propext (correct i x)
        rw [vEq] at wi
        obtain ⟨s, ms, ls, done⟩ := ih (todo.erase i) (erase_ssubset hi) (p ++ t)
          (fun v => stays (inputs v) t) (stays zero t) (fun j hj => by
            by_cases eq : j = i
            · simpa [eq] using wi
            · exact stays (ready j (fun hm => hj (mem_erase.mpr ⟨eq, hm⟩))) t)
        refine ⟨t ++ s, mono_append mt ms, ?_, by simpa [List.append_assoc] using done⟩
        rw [List.length_append, lt, ls, Nat.add_comm, sum_erase_add _ _ hi]
      · have eq := not_nonempty_iff_eq_empty.mp hn
        subst todo
        exact ⟨[], by simp [mono, Monotone2], by simp, fun i => by simpa using ready i (by simp)⟩
  let z : Gate := ⟨.or, []⟩
  have inputs (v : V) : Has ([] : List Gate) (fun x : Input n => x (label v) = true) := by
    refine ⟨(label v).val, by simp, ?_⟩
    intro x; simp [valAt, wires, Circuit.wires, List.getD_eq_getElem?_getD]
  have hz : Has [z] (fun _ : Input n => False) := by
    simpa [z, GateOp.eval] using new_wire (n := n) [] z
  obtain ⟨t, mt, sz, done⟩ := finish univ [z] (fun v => stays_one (inputs v) z) hz (by simp)
  obtain ⟨i, _, ok⟩ := done out
  exact ⟨⟨[z] ++ t, i⟩, mono_append (by simp [mono, Monotone2, z]) mt,
    by simp [Circuit.size, sz, Nat.add_comm], ok⟩

end Compiler

namespace Gates

open Finset Compiler Model Template

abbrev HV (H : Type) := Fin 4 × H
abbrev WV (W : Type) := Fin 4 × W

def twinKey {H W O : Type} (u : O → Tuple H W) (e : O × Bool) : TwinKey H :=
  (e.2, (u e.1).1 (if e.2 then 2 else 0), (u e.1).1 (if e.2 then 3 else 1))

abbrev Twin {H W O : Type} (u : O → Tuple H W) := Set.range (twinKey u)

abbrev Vtx {H W O : Type} (u : O → Tuple H W) :=
  Vertex (HV H) (Inc O) (Parent (WV W) (Used u) (Opp O) (Pair O))

def clOf {H W O : Type} (u : O → Tuple H W) (i : Inc O) : Used u := ⟨key u i, i, rfl⟩
def twOf {H W O : Type} (u : O → Tuple H W) (e : O × Bool) : Twin u := ⟨twinKey u e, e, rfl⟩
def twinI {H W O : Type} (u : O → Tuple H W) (i : Inc O) := twOf u (i.1, i.2.2)
def twinP {H W O : Type} (u : O → Tuple H W) (p : Pair O) := twOf u (p.1, p.2.2)

def high (r : Fin 4) (side : Bool) : Bool :=
  if side then r == 1 || r == 2 else r == 2 || r == 3

def arc {H W O : Type} (u : O → Tuple H W) (i : Inc O) : Twin u × Bool :=
  (twinI u i, high i.2.1 i.2.2)

def hubAt {H W O : Type} (u : O → Tuple H W) (e : Twin u × Bool) : HV H :=
  if e.2 then (if e.1.val.1 then 3 else 1, e.1.val.2.2)
  else (if e.1.val.1 then 2 else 0, e.1.val.2.1)

theorem center_arc {H W O : Type} (u : O → Tuple H W) (i : Inc O) :
    (layout u).center i = hubAt u (arc u i) := by
  obtain ⟨o, r, b⟩ := i
  fin_cases r <;> cases b <;> rfl

theorem twin_arc {H W O : Type} (u : O → Tuple H W) (i : Inc O) :
    (layout u).twin i = hubAt u ((arc u i).1, !(arc u i).2) := by
  obtain ⟨o, r, b⟩ := i
  fin_cases r <;> cases b <;> rfl

inductive Node (O K W E H : Type) where
  | oppOr (s : Opp O) | oppEx (s : Opp O)
  | pairOr (p : Pair O) | pairEx (p : Pair O)
  | clOr (k : K) | clEx (k : K)
  | clList (k : K) | cornerEx (w : W)
  | guard (i : Inc O) | guarded (i : Inc O) | clOut (k : K)
  | fourOr (o : O) | grid (e : E) | star (s : E × Bool) | hubEx (d : H) | root
  deriving DecidableEq

def nodeEquiv (O K W E H : Type) :
    Node O K W E H ≃
      (((Opp O ⊕ Opp O) ⊕ (Pair O ⊕ Pair O)) ⊕ ((K ⊕ K) ⊕ (K ⊕ W))) ⊕
      (((Inc O ⊕ Inc O) ⊕ (K ⊕ O)) ⊕ ((E ⊕ (E × Bool)) ⊕ (H ⊕ Unit))) where
  toFun
    | .oppOr s => .inl (.inl (.inl (.inl s)))
    | .oppEx s => .inl (.inl (.inl (.inr s)))
    | .pairOr p => .inl (.inl (.inr (.inl p)))
    | .pairEx p => .inl (.inl (.inr (.inr p)))
    | .clOr k => .inl (.inr (.inl (.inl k)))
    | .clEx k => .inl (.inr (.inl (.inr k)))
    | .clList k => .inl (.inr (.inr (.inl k)))
    | .cornerEx w => .inl (.inr (.inr (.inr w)))
    | .guard i => .inr (.inl (.inl (.inl i)))
    | .guarded i => .inr (.inl (.inl (.inr i)))
    | .clOut k => .inr (.inl (.inr (.inl k)))
    | .fourOr o => .inr (.inl (.inr (.inr o)))
    | .grid e => .inr (.inr (.inl (.inl e)))
    | .star s => .inr (.inr (.inl (.inr s)))
    | .hubEx d => .inr (.inr (.inr (.inl d)))
    | .root => .inr (.inr (.inr (.inr ())))
  invFun
    | .inl (.inl (.inl (.inl s))) => .oppOr s
    | .inl (.inl (.inl (.inr s))) => .oppEx s
    | .inl (.inl (.inr (.inl p))) => .pairOr p
    | .inl (.inl (.inr (.inr p))) => .pairEx p
    | .inl (.inr (.inl (.inl k))) => .clOr k
    | .inl (.inr (.inl (.inr k))) => .clEx k
    | .inl (.inr (.inr (.inl k))) => .clList k
    | .inl (.inr (.inr (.inr w))) => .cornerEx w
    | .inr (.inl (.inl (.inl i))) => .guard i
    | .inr (.inl (.inl (.inr i))) => .guarded i
    | .inr (.inl (.inr (.inl k))) => .clOut k
    | .inr (.inl (.inr (.inr o))) => .fourOr o
    | .inr (.inr (.inl (.inl e))) => .grid e
    | .inr (.inr (.inl (.inr s))) => .star s
    | .inr (.inr (.inr (.inl d))) => .hubEx d
    | .inr (.inr (.inr (.inr ()))) => .root
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with (((s | s) | (p | p)) | ((k | k) | (k | w))) |
      (((i | i) | (k | o)) | ((e | s) | (d | ⟨⟩))) <;> rfl

abbrev Nodes {H W O : Type} (u : O → Tuple H W) := Node O (Used u) (WV W) (Twin u) (HV H)
abbrev Term {H W O : Type} (u : O → Tuple H W) := Expr (Vtx u) (Nodes u)

noncomputable def fintypeUsed {H W O : Type} [Fintype H] [Fintype W] (u : O → Tuple H W) :
    Fintype (Used u) :=
  Fintype.ofFinite _

noncomputable def fintypeTwin {H W O : Type} [Fintype H] (u : O → Tuple H W) :
    Fintype (Twin u) :=
  Fintype.ofFinite _

noncomputable def fintypeNodes {H W O : Type} [Fintype H] [Fintype W] [Fintype O]
    (u : O → Tuple H W) : Fintype (Nodes u) :=
  letI : Fintype (Used u) := fintypeUsed u
  letI : Fintype (Twin u) := fintypeTwin u
  Fintype.ofEquiv _ (nodeEquiv O (Used u) (WV W) (Twin u) (HV H)).symm

def level {H W O : Type} (u : O → Tuple H W) : Nodes u → Nat
  | .oppOr _ | .pairOr _ | .clOr _ | .clList _ => 0
  | .oppEx _ | .pairEx _ | .clEx _ | .guard _ | .cornerEx _ | .fourOr _ => 1
  | .guarded _ | .grid _ => 2
  | .clOut _ | .star _ => 3
  | .hubEx _ => 4 | .root => 5

noncomputable def allE {A V N : Type} [Fintype A] (f : A → Expr V N) :=
  (univ : Finset A).toList.map f

noncomputable def groupE {A B V N : Type} [Fintype A] (k : A → B) (b : B) (f : A → Expr V N) :=
  letI := Classical.decEq B
  ((univ : Finset A).filter (fun a => k a = b)).toList.map f

theorem exists_group {A B V N : Type} [Fintype A] (k : A → B) (b : B) (f : A → Expr V N)
    (p : Expr V N → Prop) :
    (∃ e ∈ groupE k b f, p e) ↔ ∃ i, k i = b ∧ p (f i) := by
  classical
  constructor
  · rintro ⟨e, he, hp⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    exact ⟨i, (mem_filter.mp (mem_toList.mp hi)).2, hp⟩
  · rintro ⟨i, hi, hp⟩
    exact ⟨_, List.mem_map.mpr ⟨i, mem_toList.mpr (mem_filter.mpr ⟨mem_univ _, hi⟩), rfl⟩, hp⟩

theorem exists_all {A V N : Type} [Fintype A] (f : A → Expr V N) (p : Expr V N → Prop) :
    (∃ e ∈ allE f, p e) ↔ ∃ i, p (f i) := by
  constructor
  · rintro ⟨e, he, hp⟩
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    exact ⟨i, hp⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, List.mem_map.mpr ⟨i, mem_toList.mpr (mem_univ _), rfl⟩, hi⟩

theorem exists_append {A : Type} (a b : List A) (p : A → Prop) :
    (∃ i ∈ a ++ b, p i) ↔ (∃ i ∈ a, p i) ∨ ∃ i ∈ b, p i := by
  simp only [List.mem_append]; grind

noncomputable def recipe {H W O : Type} [Fintype H] [Fintype W] [Fintype O]
    (u : O → Tuple H W) : Nodes u → Term u
  | .oppOr s => .binary false (.input (.parent (.corner ((layout u).opposite s false))))
      (.input (.parent (.corner ((layout u).opposite s true))))
  | .oppEx s => .binary true (.input (.parent (.opposite s)))
      (.binary false (.ref (.oppOr s)) (.input (.leaf (.opposite s))))
  | .pairOr p => .binary false (.input (.u ((layout u).paired p false)))
      (.input (.u ((layout u).paired p true)))
  | .pairEx p => .binary true (.input (.parent (.matched p)))
      (.binary false (.ref (.pairOr p)) (.input (.leaf (.matched p))))
  | .clOr k => .binary false (.input (.parent (.corner ((layout u).clusterW k))))
      (.input (.hub ((layout u).clusterH k)))
  | .clEx k => .binary true (.input (.parent (.cluster k)))
      (.binary false (.ref (.clOr k)) (.input (.leaf (.cluster k))))
  | .clList k => Expr.foldOr .zero (groupE (clOf u) k (fun i => .input (.u i)))
  | .cornerEx w =>
      letI : Fintype (Used u) := fintypeUsed u
      .binary true (.input (.parent (.corner w)))
        (Expr.foldOr (.input (.leaf (.corner w))) (groupE (layout u).clusterW w (fun k => .ref (.clList k))))
  | .guard i => .binary false (.ref (.clOr (clOf u i))) (.input (.u i))
  | .guarded i => .binary true (.input (.z i)) (.ref (.guard i))
  | .clOut k => .binary true (Expr.foldOr .zero (groupE (clOf u) k (fun i => .ref (.guarded i))))
      (.binary false (.input (.hub ((layout u).clusterH k))) (.ref (.clList k)))
  | .fourOr o => .binary false (.ref (.oppOr (o, false))) (.ref (.oppOr (o, true)))
  | .grid e => Expr.foldOr .zero
      (groupE (twOf u) e (fun p => .ref (.fourOr p.1)) ++
       groupE (twinP u) e (fun p => .ref (.pairOr p)))
  | .star s => .binary true (Expr.foldOr .zero (groupE (arc u) s (fun i => .ref (.guard i))))
      (.ref (.grid s.1))
  | .hubEx d =>
      letI : Fintype (Twin u) := fintypeTwin u
      .binary true (.input (.hub d))
        (Expr.foldOr .zero (groupE (hubAt u) d (fun s => .ref (.star s))))
  | .root =>
      letI : Fintype (Used u) := fintypeUsed u
      Expr.foldOr .zero
        (allE (fun s => .ref (.oppEx s)) ++ allE (fun p => .ref (.pairEx p)) ++
         allE (fun k => .ref (.clEx k)) ++ allE (fun w => .ref (.cornerEx w)) ++
         allE (fun k => .ref (.clOut k)) ++ allE (fun h => .ref (.hubEx h)))

theorem prior {H W O : Type} [Fintype H] [Fintype W] [Fintype O]
    (u : O → Tuple H W) (i j : Nodes u) (h : (recipe u i).Uses j) :
    level u j < level u i := by
  letI : Fintype (Used u) := fintypeUsed u
  letI : Fintype (Twin u) := fintypeTwin u
  classical
  cases i <;> simp only [recipe, Expr.fold_uses, exists_append, exists_all, exists_group,
    Expr.Uses, false_or, or_false] at h <;> grind [level]

noncomputable def sizeGroup {A B : Type} [Fintype A] (f : A → B) (b : B) :=
  letI := Classical.decEq B
  (univ.filter (fun a => f a = b)).card

theorem sum_groups {A B : Type} [Fintype A] [Fintype B] (f : A → B) :
    ∑ b, sizeGroup f b = Fintype.card A := by
  classical
  simp only [sizeGroup, card_filter]
  rw [sum_comm]
  simp

private theorem group_len {A B V N : Type} [Fintype A] (f : A → B) (b : B) (e : A → Expr V N) :
    (groupE f b e).length = sizeGroup f b := by
  classical simp [groupE, sizeGroup]

private theorem all_len {A V N : Type} [Fintype A] (e : A → Expr V N) :
    (allE e).length = Fintype.card A := by
  simp [allE]

private noncomputable def cost {H W O : Type} [Fintype H] [Fintype W] [Fintype O]
    (u : O → Tuple H W) : Nodes u → Nat
  | .oppOr _ | .pairOr _ | .clOr _ | .guard _ | .guarded _ | .fourOr _ => 1
  | .oppEx _ | .pairEx _ | .clEx _ => 2
  | .clList k => sizeGroup (clOf u) k
  | .cornerEx w =>
      letI : Fintype (Used u) := fintypeUsed u
      sizeGroup (layout u).clusterW w + 1
  | .clOut k => sizeGroup (clOf u) k + 2
  | .grid e => sizeGroup (twOf u) e + sizeGroup (twinP u) e
  | .star s => sizeGroup (arc u) s + 1
  | .hubEx d =>
      letI : Fintype (Twin u) := fintypeTwin u
      sizeGroup (hubAt u) d + 1
  | .root =>
      letI : Fintype (Used u) := fintypeUsed u
      Fintype.card (Opp O) + Fintype.card (Pair O) + Fintype.card (Used u) +
        Fintype.card (WV W) + Fintype.card (Used u) + Fintype.card (HV H)

private theorem cost_eq {H W O : Type} [Fintype H] [Fintype W] [Fintype O]
    (u : O → Tuple H W) (n : Nodes u) : (recipe u n).weight = cost u n := by
  letI : Fintype (Used u) := fintypeUsed u
  letI : Fintype (Twin u) := fintypeTwin u
  cases n <;> simp [recipe, cost, Expr.fold_weight, Expr.weight, group_len, all_len,
    List.map_append, List.sum_append]
  all_goals simp [groupE, allE, List.map_map, Function.comp_def, Expr.weight, Nat.add_assoc]

theorem weight_sum {H W O : Type} [Fintype H] [Fintype W] [Fintype O] (u : O → Tuple H W) :
    letI : Fintype (Nodes u) := fintypeNodes u
    letI : Fintype (Twin u) := fintypeTwin u
    letI : Fintype (Used u) := fintypeUsed u
    (∑ n, (recipe u n).weight) =
      71 * Fintype.card O + 4 * Fintype.card (Twin u) + 8 * Fintype.card (Used u) +
      2 * Fintype.card (WV W) + 2 * Fintype.card (HV H) := by
  letI : Fintype (Used u) := fintypeUsed u
  letI : Fintype (Twin u) := fintypeTwin u
  letI : Fintype (Nodes u) := fintypeNodes u
  classical
  simp_rw [cost_eq]
  rw [← (nodeEquiv O (Used u) (WV W) (Twin u) (HV H)).symm.sum_comp]
  simp [Fintype.sum_sum_type, nodeEquiv, cost, sum_add_distrib, sum_groups, Inc, Opp, Pair]
  ring

def guarded {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) (i : Inc O) :=
  (x (.parent (.corner ((layout u).corner i))) ∨ x (.hub ((layout u).twin i))) ∨ x (.u i)

def privateList {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) (k : Used u) :=
  ∃ i, clOf u i = k ∧ x (.u i)

def gridValue {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) (e : Twin u) :=
  ∃ i, twinI u i = e ∧ (x (.parent (.corner ((layout u).corner i))) ∨ x (.u i))

def starValue {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) (s : Twin u × Bool) :=
  (∃ i, arc u i = s ∧ guarded u x i) ∧ gridValue u x s.1

def hubValue {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) (d : HV H) :=
  x (.hub d) ∧ ∃ s, hubAt u s = d ∧ starValue u x s

def cornerValue {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) (w : WV W) :=
  x (.parent (.corner w)) ∧ (x (.leaf (.corner w)) ∨
    ∃ k, (layout u).clusterW k = w ∧ privateList u x k)

def clusterValue {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) (k : Used u) :=
  (∃ i, clOf u i = k ∧ x (.z i) ∧ guarded u x i) ∧
  (x (.hub ((layout u).clusterH k)) ∨ privateList u x k)

def value {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) : Nodes u → Prop
  | .oppOr s => ∃ b, x (.parent (.corner ((layout u).opposite s b)))
  | .oppEx s => x (.parent (.opposite s)) ∧
      ((∃ b, x (.parent (.corner ((layout u).opposite s b)))) ∨ x (.leaf (.opposite s)))
  | .pairOr p => ∃ b, x (.u ((layout u).paired p b))
  | .pairEx p => x (.parent (.matched p)) ∧
      ((∃ b, x (.u ((layout u).paired p b))) ∨ x (.leaf (.matched p)))
  | .clOr k => x (.parent (.corner ((layout u).clusterW k))) ∨ x (.hub ((layout u).clusterH k))
  | .clEx k => x (.parent (.cluster k)) ∧ ((x (.parent (.corner ((layout u).clusterW k))) ∨
      x (.hub ((layout u).clusterH k))) ∨ x (.leaf (.cluster k)))
  | .clList k => privateList u x k
  | .cornerEx w => cornerValue u x w
  | .guard i => guarded u x i
  | .guarded i => x (.z i) ∧ guarded u x i
  | .clOut k => clusterValue u x k
  | .fourOr o => ∃ r, x (.parent (.corner (r, (u o).2 r)))
  | .grid e => gridValue u x e
  | .star s => starValue u x s
  | .hubEx d => hubValue u x d
  | .root =>
      (∃ s, x (.parent (.opposite s)) ∧
        ((∃ b, x (.parent (.corner ((layout u).opposite s b)))) ∨ x (.leaf (.opposite s)))) ∨
      (∃ p, x (.parent (.matched p)) ∧
        ((∃ b, x (.u ((layout u).paired p b))) ∨ x (.leaf (.matched p)))) ∨
      (∃ k, x (.parent (.cluster k)) ∧ ((x (.parent (.corner ((layout u).clusterW k))) ∨
        x (.hub ((layout u).clusterH k))) ∨ x (.leaf (.cluster k)))) ∨
      (∃ w, cornerValue u x w) ∨ (∃ k, clusterValue u x k) ∨ ∃ h, hubValue u x h

private theorem role_surj (r : Fin 4) : ∃ a b, oppRole a b = r := by
  revert r; decide

private theorem four_value {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) (o : O) :
    ((∃ b, x (.parent (.corner ((layout u).opposite (o, false) b)))) ∨
     (∃ b, x (.parent (.corner ((layout u).opposite (o, true) b))))) ↔
      ∃ r, x (.parent (.corner (r, (u o).2 r))) := by
  constructor
  · rintro (⟨b, h⟩ | ⟨b, h⟩) <;> exact ⟨_, h⟩
  · rintro ⟨r, hr⟩
    obtain ⟨a, b, rfl⟩ := role_surj r
    cases a
    · exact .inl ⟨_, hr⟩
    · exact .inr ⟨_, hr⟩

private theorem grid_value {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) (e : Twin u) :
    ((∃ t : O × Bool, twOf u t = e ∧ ∃ r, x (.parent (.corner (r, (u t.1).2 r)))) ∨
     (∃ p, twinP u p = e ∧ ∃ b, x (.u ((layout u).paired p b)))) ↔ gridValue u x e := by
  constructor
  · rintro (⟨⟨o, t⟩, he, r, hr⟩ | ⟨p, he, b, hb⟩)
    · exact ⟨(o, r, t), he, .inl hr⟩
    · exact ⟨(layout u).paired p b, he, .inr hb⟩
  · rintro ⟨⟨o, r, t⟩, he, hw | hp⟩
    · exact .inl ⟨(o, t), he, r, hw⟩
    · obtain ⟨a, b, rfl⟩ := role_surj r
      exact .inr ⟨(o, a, t), he, b, hp⟩

theorem recipe_value {H W O : Type} [Fintype H] [Fintype W] [Fintype O]
    (u : O → Tuple H W) (x : Vtx u → Prop) (n : Nodes u) :
    (recipe u n).meaning x (value u x) ↔ value u x n := by
  letI : Fintype (Used u) := fintypeUsed u
  letI : Fintype (Twin u) := fintypeTwin u
  cases n <;> simp only [recipe, Expr.fold_meaning, exists_append, exists_group, exists_all,
    Expr.meaning, Bool.false_eq_true, ite_false, ite_true, false_or, value, privateList,
    cornerValue, guarded, clusterValue, starValue, hubValue]
  all_goals first | rfl | exact four_value .. | exact grid_value .. |
    (simp [Bool.exists_bool, or_assoc])

private theorem cluster_spec {H W O : Type} (u : O → Tuple H W) {x : Vtx u → Prop} {k : Used u}
    (h : clusterValue u x k) : (layout u).clusterOutput x k := by
  obtain ⟨⟨i, rfl, hz, hg⟩, h⟩ := h
  refine ⟨⟨i, ⟨rfl, rfl⟩, hz, ?_⟩, ?_⟩
  · simpa [guarded, or_assoc, layout, clOf, key] using hg
  · rcases h with h | ⟨j, hj, h⟩
    · exact .inl h
    · exact .inr ⟨j, by rw [← hj]; exact ⟨rfl, rfl⟩, h⟩

private theorem grid_direction {H W O : Type} (u : O → Tuple H W)
    {x : Vtx u → Prop} {s : Twin u × Bool} (g : gridValue u x s.1) :
    (layout u).direction x (hubAt u s) (hubAt u (s.1, !s.2)) ∨
    (layout u).direction x (hubAt u (s.1, !s.2)) (hubAt u s) := by
  obtain ⟨i, hi, h⟩ := g
  by_cases hb : (arc u i).2 = s.2
  · exact .inl ⟨i, by rw [center_arc]; congr 1; exact Prod.ext hi hb,
      by rw [twin_arc]; simp only [show (arc u i).1 = s.1 from hi, hb], h⟩
  · have flip : (arc u i).2 = !s.2 := by cases hs : s.2 <;> cases hi' : (arc u i).2 <;> simp_all
    exact .inr ⟨i, by rw [center_arc]; congr 1; exact Prod.ext hi flip,
      by rw [twin_arc]; simp only [show (arc u i).1 = s.1 from hi, flip, Bool.not_not, Prod.mk.eta], h⟩

private theorem hub_spec {H W O : Type} (u : O → Tuple H W) {x : Vtx u → Prop} {d}
    (h : hubValue u x d) : (layout u).hubOutput x d := by
  obtain ⟨hd, s, rfl, ⟨i, hi, hg⟩, g⟩ := h
  refine ⟨hd, hubAt u (s.1, !s.2), ?_, grid_direction u g⟩
  rcases hg with (hw | hy) | hp
  · exact .inr ⟨i, by rw [center_arc, hi], by rw [twin_arc, hi], .inl hw⟩
  · exact .inl (by simpa only [twin_arc, hi] using hy)
  · exact .inr ⟨i, by rw [center_arc, hi], by rw [twin_arc, hi], .inr hp⟩

private theorem root_sound {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop)
    (h : value u x .root) : (layout u).exposed x := by
  rcases h with ⟨s, hs, ⟨b, hb⟩ | hl⟩ | ⟨p, hp, ⟨b, hb⟩ | hl⟩ |
    ⟨k, hk, h | hl⟩ | ⟨w, hw, hl | ⟨k, hk, i, hi, hp⟩⟩ | ⟨k, hk⟩ | ⟨d, hd⟩
  all_goals unfold Layout.exposed
  · exact .inr (.inr (.inl ⟨s, b, hs, hb⟩))
  · exact .inl ⟨_, hs, hl⟩
  · exact .inr (.inr (.inr (.inl ⟨p, b, hp, hb⟩)))
  · exact .inl ⟨_, hp, hl⟩
  · exact .inr (.inl ⟨k, hk, h⟩)
  · exact .inl ⟨_, hk, hl⟩
  · exact .inl ⟨_, hw, hl⟩
  · subst k; subst w
    exact .inr (.inr (.inr (.inr (.inl ⟨i, hw, hp⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨k, cluster_spec u hk⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨d, hub_spec u hd⟩)))))

private theorem incident_on {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) (i : Inc O)
    (hd : x (.hub ((layout u).center i)))
    (ha : x (.parent (.corner ((layout u).corner i))) ∨ x (.u i)) :
    hubValue u x ((layout u).center i) := by
  refine ⟨hd, arc u i, (center_arc u i).symm, ⟨i, rfl, ?_⟩, i, rfl, ha⟩
  rcases ha with h | h
  · exact .inl (.inl h)
  · exact .inr h

theorem root_exact {H W O : Type} (u : O → Tuple H W) (x : Vtx u → Prop) :
    value u x .root ↔ (layout u).exposed x := by
  refine ⟨root_sound u x, ?_⟩
  rw [(layout u).exposed_exact (assigned u)]
  rintro ⟨a, b, hab, ha, hb⟩
  obtain ⟨e, he⟩ := hab.1
  have both : x ((layout u).ends e).1 ∧ x ((layout u).ends e).2 := by
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
  clear he hab ha hb a b
  obtain ⟨l, r⟩ := both
  unfold value
  cases e with
  | dw i => exact .inr (.inr (.inr (.inr (.inr ⟨_, incident_on u x i l (.inl r)⟩))))
  | du i => exact .inr (.inr (.inr (.inr (.inr ⟨_, incident_on u x i l (.inr r)⟩))))
  | yz i => exact .inr (.inr (.inr (.inr (.inl ⟨clOf u i, ⟨i, rfl, r, .inl (.inr l)⟩, .inl l⟩))))
  | uz i => exact .inr (.inr (.inr (.inr (.inl ⟨clOf u i, ⟨i, rfl, r, .inr l⟩, .inr ⟨i, rfl, l⟩⟩))))
  | wu i => exact .inr (.inr (.inr (.inl ⟨_, l, .inr ⟨clOf u i, rfl, i, rfl, r⟩⟩)))
  | rw k => exact .inr (.inr (.inl ⟨k, l, .inl (.inl r)⟩))
  | ry k => exact .inr (.inr (.inl ⟨k, l, .inl (.inr r)⟩))
  | sw s b => exact .inl ⟨s, l, .inl ⟨b, r⟩⟩
  | pu p b => exact .inr (.inl ⟨p, l, .inl ⟨b, r⟩⟩)
  | pendant p =>
    cases p with
    | corner w => exact .inr (.inr (.inr (.inl ⟨w, l, .inl r⟩)))
    | cluster k => exact .inr (.inr (.inl ⟨k, l, .inr r⟩))
    | opposite s => exact .inl ⟨s, l, .inr r⟩
    | matched p => exact .inr (.inl ⟨p, l, .inr r⟩)

end Gates

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.CoverPromise
open Finset Overlap Model Obstructions Template Clean Compiler Gates

def Recorded : Prop :=
  ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1

private theorem minimum_cover {n : Nat} (G : SimpleGraph (Fin n)) :
    ∃ t, (∃ S : Finset (Fin n), IsVertexCover G S ∧ S.card = t) ∧
      ∀ S : Finset (Fin n), IsVertexCover G S → t ≤ S.card := by
  classical
  let p := fun t => ∃ S : Finset (Fin n), IsVertexCover G S ∧ S.card = t
  have existsP : ∃ t, p t := ⟨_, Finset.univ, fun _ _ _ => Or.inl (Finset.mem_univ _), rfl⟩
  exact ⟨Nat.find existsP, Nat.find_spec existsP,
    fun S h => Nat.find_min' existsP ⟨S, h, rfl⟩⟩

theorem refute_of_implementation {H W I K S P : Type} [Fintype H] [Fintype W] [Fintype I] [Fintype K]
    [Fintype S] [Fintype P] (L : Layout H W I K S P)
    (good : L.SquareConditions) (os : ∀ s, Function.Injective (L.opposite s))
    (ps : ∀ p, Function.Injective (L.paired p)) (assigned : ∀ i, ∃ k, L.inCluster i k)
    (g e : Nat) (i8 : Fintype.card I = 8 * g) (s2 : Fintype.card S = 2 * g)
    (p4 : Fintype.card P = 4 * g) (saving : e + 2 * Fintype.card K + Fintype.card H < g)
    {n : Nat} (label : Vertex H I (Parent W K S P) ≃ Fin n) (C : Circuit) (mono : Monotone2 C)
    (sem : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      L.exposed (fun v => x (label v) = true))
    (budget : C.size + 1 ≤ 71 * g + e + 6 * Fintype.card K + 2 * Fintype.card W + Fintype.card H) :
    ¬Recorded := by
  classical
  intro universal
  let G := L.graph.comap label.symm
  obtain ⟨t, hcover, hmin⟩ := minimum_cover G
  obtain ⟨cover, hc, hcard⟩ := hcover
  have liftCover : IsVertexCover L.graph (cover.map label.symm.toEmbedding) := by
    intro u v hadj
    have hG : G.Adj (label u) (label v) := by simpa [G] using hadj
    rcases hc _ _ hG with h | h
    · exact .inl (Finset.mem_map.mpr ⟨_, h, label.symm_apply_apply u⟩)
    · exact .inr (Finset.mem_map.mpr ⟨_, h, label.symm_apply_apply v⟩)
  have lower := L.cover_lower _ liftCover
  rw [Finset.card_map, hcard, Layout.parent_card] at lower
  have eqEdges : G.edgeSet.ncard = L.graph.edgeSet.ncard :=
    Nat.card_congr (SimpleGraph.Iso.comap label.symm L.graph).mapEdgeSet
  have hcount := L.edge_count good.oneIncidence os ps
  have hI : 0 < Fintype.card I := by omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hI
  let edge := L.ends (.uz i)
  have nonemptyG : ∃ u v, G.Adj u v := ⟨label edge.1, label edge.2,
    by simpa [G, edge] using L.adjacent (.uz i)⟩
  apply Nat.not_lt_of_ge (universal n t G C nonemptyG
    (fun a b c d _ hac _ _ hbd _ => L.no_four_cycle good _ _ _ _
      (label.symm.injective.ne hac) (label.symm.injective.ne hbd))
    ⟨cover, hc, hcard⟩ hmin mono (fun x => ?_))
  · omega
  · rw [sem, L.exposed_exact assigned]
    constructor
    · rintro ⟨u, v, ha, hu, hv⟩
      exact ⟨label u, label v, by simpa [G] using ha, hu, hv⟩
    · rintro ⟨u, v, ha, hu, hv⟩
      exact ⟨label.symm u, label.symm v, ha, by simpa using hu, by simpa using hv⟩

private theorem realEdge_graphHub (r : Fin 4) (b : Bool) :
    realEdge r (graphHub r b) = true := by
  revert r b; decide

private theorem graphHub_inj (r : Fin 4) (b1 b2 : Bool)
    (h : graphHub r b1 = graphHub r b2) : b1 = b2 := by
  revert r b1 b2 h; decide

private theorem oppRole_pair (p1 p2 a c : Bool)
    (h : oppRole p1 a = oppRole p2 c) : p1 = p2 := by
  revert p1 p2 a c h; decide

private theorem oppRole_side (p a c : Bool)
    (h : oppRole p a = oppRole p c) : a = c := by
  revert p a c h; decide

private theorem base_supported {H W O : Type} (u : O → Tuple H W)
    {o : O} {r : Fin 4} {b : Bool} {d : HV H} {w : WV W}
    (hc : (layout u).center (o, r, b) = d) (hw : (layout u).corner (o, r, b) = w) :
    supported (u o) d w := by
  rcases d with ⟨dr, dh⟩
  rcases w with ⟨wr, ww⟩
  simp only [layout, Prod.mk.injEq] at hc hw
  rcases hc with ⟨rfl, hd⟩
  rcases hw with ⟨rfl, hw'⟩
  exact ⟨realEdge_graphHub r b, hd, hw'⟩

private theorem alt_mem {A : Type} {s : Finset A} {a b : A} (ha : a ∈ s) (hb : b ∈ s) :
    ∀ i : Fin 4, (Four.mk a b a b).atRole i ∈ s := by
  intro i; fin_cases i <;> assumption

private theorem twin_card_le {q : Nat} {pos : 0 < q} {x : Experiment q}
    {keep : Finset (Tuple (Hub q) (Corner q))} (sub : keep ⊆ raw pos x) :
    @Fintype.card (Twin (Subtype.val : ↥keep → Tuple (Hub q) (Corner q))) (fintypeTwin _) ≤
      (sampleTwins pos x).card := by
  let u : ↥keep → Tuple (Hub q) (Corner q) := Subtype.val
  letI : Fintype (Twin u) := fintypeTwin u
  classical
  let f : Twin u → ↥(sampleTwins pos x) := fun e =>
    ⟨e.val, by
      obtain ⟨⟨o, b⟩, he⟩ := e.property
      have ho : o.val ∈ raw pos x := sub o.property
      have hhit := (mem_filter.mp ho).2
      have hmem : e.val ∈ twins o.val := by
        rw [← he]
        exact mem_image.mpr ⟨b, mem_univ _, rfl⟩
      refine mem_filter.mpr ⟨mem_univ _, ⟨?_, ?_⟩⟩
      · intro t ht
        rw [mem_singleton.mp ht]
        exact hhit.1 _ hmem
      · intro _ hc
        exact absurd hc (notMem_empty _)⟩
  have inj : Function.Injective f := fun _ _ h =>
    Subtype.ext (congrArg (fun z : ↥(sampleTwins pos x) => z.val) h)
  simpa using Fintype.card_le_of_injective f inj

private theorem used_card_le {q : Nat} {pos : 0 < q} {x : Experiment q}
    {keep : Finset (Tuple (Hub q) (Corner q))} (sub : keep ⊆ raw pos x) :
    @Fintype.card (Used (Subtype.val : ↥keep → Tuple (Hub q) (Corner q))) (fintypeUsed _) ≤
      (sampleClusters pos x).card := by
  let u : ↥keep → Tuple (Hub q) (Corner q) := Subtype.val
  letI : Fintype (Used u) := fintypeUsed u
  classical
  let f : Used u → ↥(sampleClusters pos x) := fun k =>
    ⟨k.val, by
      obtain ⟨⟨o, r, b⟩, hk⟩ := k.property
      have ho : o.val ∈ raw pos x := sub o.property
      have hhit := (mem_filter.mp ho).2
      have hmem : k.val ∈ clusters o.val := by
        rw [← hk]
        exact mem_image.mpr ⟨(r, b), mem_univ _, rfl⟩
      refine mem_filter.mpr ⟨mem_univ _, ⟨?_, ?_⟩⟩
      · intro _ ht
        exact absurd ht (notMem_empty _)
      · intro c hc
        rw [mem_singleton.mp hc]
        exact hhit.2 _ hmem⟩
  have inj : Function.Injective f := fun _ _ h =>
    Subtype.ext (congrArg (fun z : ↥(sampleClusters pos x) => z.val) h)
  simpa using Fintype.card_le_of_injective f inj

theorem lmeta612_false : ¬Recorded := by
  classical
  obtain ⟨pos, x, keep, sub, clean, hdense⟩ := Obstructions.dense Alteration.q rfl
  let q := Alteration.q
  let O := ↥keep
  let u : O → Tuple (Hub q) (Corner q) := Subtype.val
  letI : Fintype (Used u) := fintypeUsed u
  letI : Fintype (Twin u) := fintypeTwin u
  letI : Fintype (Nodes u) := fintypeNodes u
  letI : Fintype (Parent (WV (Corner q)) (Used u) (Opp O) (Pair O)) := fintypeParent
  letI : Fintype (Vtx u) := fintypeVertex
  have hsq : (layout u).SquareConditions := by
    apply Template.square_conditions u
    · intro d e w v hdw hew hev hdv
      by_contra hne
      push Not at hne
      obtain ⟨de, wv⟩ := hne
      obtain ⟨⟨o0, r0, b0⟩, hc0, hw0⟩ := hdw
      obtain ⟨⟨o1, r1, b1⟩, hc1, hw1⟩ := hew
      obtain ⟨⟨o2, r2, b2⟩, hc2, hw2⟩ := hev
      obtain ⟨⟨o3, r3, b3⟩, hc3, hw3⟩ := hdv
      let f : Fin 4 → Tuple (Hub q) (Corner q) := (Four.mk (u o0) (u o1) (u o2) (u o3)).atRole
      have hf : ∀ i, f i ∈ keep := by
        intro i; fin_cases i <;> exact Subtype.property _
      exact Clean.excludes sub clean f hf
        (Clean.square_low f de wv
          (base_supported u hc0 hw0) (base_supported u hc1 hw1)
          (base_supported u hc2 hw2) (base_supported u hc3 hw3))
    · intro i j hc hw
      rcases i with ⟨o1, r1, b1⟩
      rcases j with ⟨o2, r2, b2⟩
      have hr : r1 = r2 := congrArg Prod.fst hw
      subst hr
      have hb : b1 = b2 := graphHub_inj r1 b1 b2 (congrArg Prod.fst hc)
      subst hb
      have ho : o1 = o2 := by
        by_contra hne
        have hne' : u o1 ≠ u o2 := fun h => hne (Subtype.ext h)
        exact Clean.excludes sub clean (Clean.alt (u o1) (u o2))
          (alt_mem o1.property o2.property)
          (Clean.duplicateJ_low hne'
            (base_supported u rfl rfl) (base_supported u hc.symm hw.symm))
      subst ho
      rfl
    · intro s t a b c d hab hcd h1 h2
      rcases s with ⟨o1, p1⟩
      rcases t with ⟨o2, p2⟩
      have hp : p1 = p2 := oppRole_pair p1 p2 a c (congrArg Prod.fst h1)
      subst hp
      have hac : a = c := oppRole_side p1 a c (congrArg Prod.fst h1)
      have hbd : b = d := oppRole_side p1 b d (congrArg Prod.fst h2)
      subst hac; subst hbd
      have ho : o1 = o2 := by
        by_contra hne
        have hne' : u o1 ≠ u o2 := fun h => hne (Subtype.ext h)
        have hv1 : (u o1).2 (oppRole p1 a) = (u o2).2 (oppRole p1 a) := congrArg Prod.snd h1
        have hv2 : (u o1).2 (oppRole p1 b) = (u o2).2 (oppRole p1 b) := congrArg Prod.snd h2
        have hfalse : (u o1).2 (oppRole p1 false) = (u o2).2 (oppRole p1 false) := by
          cases a <;> cases b <;> simp_all
        have htrue : (u o1).2 (oppRole p1 true) = (u o2).2 (oppRole p1 true) := by
          cases a <;> cases b <;> simp_all
        exact Clean.excludes sub clean (Clean.alt (u o1) (u o2))
          (alt_mem o1.property o2.property)
          (Clean.duplicateS_low hne' p1 hfalse htrue)
      subst ho
      rfl
  let label : Vtx u ≃ Fin (Fintype.card (Vtx u)) := Fintype.equivFin (Vtx u)
  obtain ⟨C, hmono, hsz, hsem⟩ :=
    Compiler.compile label (Gates.level u) (Gates.recipe u)
      (fun n inp => Gates.value u (fun v => inp (label v) = true) n)
      (Gates.prior u)
      (fun n inp => Gates.recipe_value u (fun v => inp (label v) = true) n)
      .root
  have hsem' : ∀ inp, C.eval (List.ofFn inp) = true ↔
      (layout u).exposed (fun v => inp (label v) = true) := fun inp =>
    (hsem inp).trans (Gates.root_exact u (fun v => inp (label v) = true))
  have hwt := Gates.weight_sum u
  have htw : Fintype.card (Twin u) ≤ (sampleTwins pos x).card := twin_card_le sub
  have hcl : Fintype.card (Used u) ≤ (sampleClusters pos x).card := used_card_le sub
  have hH : Fintype.card (HV (Hub q)) = 4 * q ^ 50 := by
    simp [HV, Hub, Fintype.card_prod, Fintype.card_fin]
  have hO : Fintype.card O = keep.card := Fintype.card_coe keep
  have hI : Fintype.card (Inc O) = 8 * Fintype.card O := by
    simp [Inc, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
  have hS : Fintype.card (Opp O) = 2 * Fintype.card O := by
    simp [Opp, Fintype.card_prod, Fintype.card_bool]; ring
  have hP : Fintype.card (Pair O) = 4 * Fintype.card O := by
    simp [Pair, Fintype.card_prod, Fintype.card_bool]; ring
  let eArg := 4 * Fintype.card (Twin u) + 2 * Fintype.card (Used u) + Fintype.card (HV (Hub q)) + 2
  have hsav : eArg + 2 * Fintype.card (Used u) + Fintype.card (HV (Hub q)) < Fintype.card O := by
    dsimp [eArg, q] at hH ⊢
    omega
  have hbud : C.size + 1 ≤
      71 * Fintype.card O + eArg + 6 * Fintype.card (Used u) +
      2 * Fintype.card (WV (Corner q)) + Fintype.card (HV (Hub q)) := by
    dsimp [eArg]
    omega
  exact refute_of_implementation (layout u) hsq
    (Template.opposite_injective u) (Template.paired_injective u) (Template.assigned u)
    (Fintype.card O) eArg hI hS hP hsav label C hmono hsem' hbud

end Cex

theorem Cex : (¬ (∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1)) := by
  exact PEqualNP.Outside.L_meta_1740.Cex.lmeta612_false


namespace Forest

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds
open SimpleGraph

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

section Support

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end Support

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [(Sum.inl b : Stat)]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem fix_many {N : ℕ} (T : Finset (Fin N)) (hT : T.Nonempty) :
    ∀ (L : List (Fin N)) (f : (Fin N → Bool) → Bool), L.Nodup → (∀ p ∈ L, p ∉ T) →
    (∀ (a : Fin N → Bool) (pre post : List (Fin N)) (p : Fin N), L = pre ++ p :: post →
      ∃ x : Fin N → Bool, (∀ q ∈ pre, x q = a q) ∧ f (Function.update x p (!x p)) ≠ f x) →
    (∀ (a : Fin N → Bool), ∀ i ∈ T, ∃ x : Fin N → Bool, (∀ q ∈ L, x q = a q) ∧
      f (Function.update x i (!x i)) ≠ f x) →
    ∀ s : ℕ, HasCircuitSize N f s → T.card + 2 * L.length ≤ s + 1 := by
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i0.2; omega⟩
  intro L
  induction L with
  | nil =>
    intro f _ _ _ hC s h
    have := dep_lower_set (n + 1) f T (fun i hi => by
      obtain ⟨x, _, hx⟩ := hC (fun _ => false) i hi
      exact ⟨x, hx⟩) s h
    simpa using this
  | cons p L ih =>
    intro f hnd hdis hA hC s h
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    have hpT : p ∉ T := hdis p List.mem_cons_self
    have hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x := by
      obtain ⟨x, _, hx⟩ := hA (fun _ => false) [] L p rfl
      exact ⟨x, hx⟩
    have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b) := by
      intro b
      obtain ⟨x, hxa, hx⟩ := hC (fun _ => b) i0 hi0
      have hxp : x p = b := hxa p List.mem_cons_self
      have hi0p : i0 ≠ p := fun e => hpT (e ▸ hi0)
      refine ⟨Function.update x i0 (!x i0), x, ?_⟩
      have e1 : Function.update (Function.update x i0 (!x i0)) p b
          = Function.update x i0 (!x i0) :=
        Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hi0p), hxp])
      have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
      rw [e1, e2]
      exact hx
    obtain ⟨b, s', hs, h'⟩ := gate_elim_at n f p s hdep hnc h
    have := ih (fun x => f (Function.update x p b)) (List.nodup_cons.1 hnd).2
      (fun q hq => hdis q (List.mem_cons_of_mem _ hq)) ?_ ?_ s' h'
    · simp only [List.length_cons]; omega
    · intro a pre post p' hL
      obtain ⟨x, hxa, hx⟩ := hA (Function.update a p b) (p :: pre) post p' (by rw [hL]; rfl)
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hp' : p' ≠ p := by
        intro e; apply hpL; rw [← e, hL]; simp
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := by
          intro e; apply hpL; rw [← e, hL]; simp [hq]
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x p' (!x p')) p b
            = Function.update x p' (!x p') :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hp'), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
    · intro a i hi
      obtain ⟨x, hxa, hx⟩ := hC (Function.update a p b) i hi
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hip : i ≠ p := fun e => hpT (e ▸ hi)
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := fun e => hpL (e ▸ hq)
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x i (!x i)) p b
            = Function.update x i (!x i) :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hip), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := PEqualNP.Outside.L_meta_1740.Forest.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem exists_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
      ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length := by
  by_contra hno
  push_neg at hno
  have hk : ∀ k : ℕ, ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ k ≤ P.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, le_refl _⟩
    | succ k ih =>
      obtain ⟨a, b, P, hP, hk⟩ := ih
      obtain ⟨c, d, Q, hQ, hlt⟩ := hno a b P hP
      exact ⟨c, d, Q, hQ, by omega⟩
  obtain ⟨a, b, P, hP, hle⟩ := hk (Fintype.card V)
  have := hP.length_lt
  omega

theorem forest_good_leaf {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (he : ∃ u v : V, G.Adj u v) :
    ∃ l p : V, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
      ((∃ q : V, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
        (∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p)) := by
  classical
  obtain ⟨u0, v0, h0⟩ := he
  haveI : Nonempty V := ⟨u0⟩
  obtain ⟨l, z, P, hP, hmax⟩ := exists_longest_path G
  have h1 : 1 ≤ P.length := by
    have := hmax u0 v0 (Walk.cons h0 Walk.nil) (by simp [Walk.cons_isPath_iff, h0.ne])
    simpa using this
  cases P with
  | nil => simp at h1
  | @cons _ p _ hlp P' =>
    rw [Walk.cons_isPath_iff] at hP
    obtain ⟨hP', hlP'⟩ := hP
    have hmax' : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P'.length + 1 := by
      intro c d Q hQ
      have := hmax c d Q hQ
      simpa using this
    have hPfull : (Walk.cons hlp P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hlP'⟩
    have hleaf : ∀ w, G.Adj l w → w = p := by
      intro w hw
      by_cases hm : w ∈ (Walk.cons hlp P').support
      · have := hG.eq_snd_of_adj_start hPfull hw hm
        simpa using this
      · exfalso
        have hQ : (Walk.cons hw.symm (Walk.cons hlp P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hPfull, hm⟩
        have := hmax' _ _ _ hQ
        simp at this
    refine ⟨l, p, hlp, hleaf, ?_⟩
    have hoff : ∀ w, G.Adj p w → w ∉ (Walk.cons hlp P').support →
        ∀ u, G.Adj w u → u = p := by
      intro w hw hwm u hu
      have hwP' : w ∉ P'.support := by
        intro h; exact hwm (by simp [h])
      have hQ : (Walk.cons hw.symm P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hwP'⟩
      by_cases hm : u ∈ (Walk.cons hw.symm P').support
      · have := hG.eq_snd_of_adj_start hQ hu hm
        simpa using this
      · exfalso
        have hQ2 : (Walk.cons hu.symm (Walk.cons hw.symm P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hQ, hm⟩
        have := hmax' _ _ _ hQ2
        simp at this
    by_cases hex : ∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p
    · exact Or.inr hex
    · left
      refine ⟨P'.snd, fun w hw => ?_⟩
      by_cases hwl : w = l
      · exact Or.inl hwl
      · right
        by_cases hm : w ∈ P'.support
        · exact hG.eq_snd_of_adj_start hP' hw hm
        · exfalso
          apply hex
          refine ⟨w, hwl, hw, hoff w hw ?_⟩
          simp [hwl, hm]

noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)

theorem F_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    F G A x = true ↔
      ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
  unfold F
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem F_eq {n : ℕ} (G G' : SimpleGraph (Fin n)) (A A' : Finset (Fin n)) (x y : Fin n → Bool)
    (h : ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ↔
      ((∃ a ∈ A', y a = true) ∨ ∃ i j : Fin n, G'.Adj i j ∧ y i = true ∧ y j = true)) :
    F G A x = F G' A' y := by
  rw [Bool.eq_iff_iff, F_true, F_true]
  exact h

theorem F_zero {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    F G A (fun _ => false) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  simp

theorem F_nc {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (h : A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) :
    ∃ x y : Fin n → Bool, F G A x ≠ F G A y := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (fun _ => true) = true := by
    rw [F_true]
    rcases h with ⟨a, ha⟩ | ⟨i, j, hij⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨i, j, hij, rfl, rfl⟩
  rw [this]
  simp

theorem F_dep {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u v : Fin n)
    (huv : G.Adj u v) (hv : v ∉ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x u (!x u)) ≠ F G A x := by
  have hne : u ≠ v := huv.ne
  refine ⟨Function.update (fun _ => false) v true, ?_⟩
  have h1 : F G A (Function.update (Function.update (fun _ => false) v true) u
      (!(Function.update (fun _ => false) v true u))) = true := by
    rw [F_true]
    right
    refine ⟨u, v, huv, ?_, ?_⟩
    · simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hne.symm]
  have h2 : F G A (Function.update (fun _ => false) v true) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, hx⟩ | ⟨i, j, hij, hi, hj⟩)
    · by_cases hav : a = v
      · exact hv (hav ▸ ha)
      · simp [Function.update_of_ne hav] at hx
    · have hiv : i = v := by
        by_contra h; simp [Function.update_of_ne h] at hi
      have hjv : j = v := by
        by_contra h; simp [Function.update_of_ne h] at hj
      exact hij.ne (hiv.trans hjv.symm)
  rw [h1, h2]
  simp

theorem F_dep_A {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x a (!x a)) ≠ F G A x := by
  refine ⟨fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (Function.update (fun _ => false) a (!false)) = true := by
    rw [F_true]
    exact Or.inl ⟨a, ha, by simp⟩
  rw [this]
  simp

theorem restrict_false {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlA : l ∉ A) (hleaf : ∀ w, G.Adj l w → w = p) (x : Fin n → Bool) :
    F G A (Function.update x l false) = F (G.deleteEdges {s(l, p)}) A x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal] at h⟩
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hil : i ≠ l := by rintro rfl; simp at hi
      have hjl : j ≠ l := by rintro rfl; simp at hj
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hil, hjl]
    · rintro ⟨i, j, hij, hi, hj⟩
      rw [deleteEdges_adj] at hij
      obtain ⟨hij, hne⟩ := hij
      have hil : i ≠ l := by
        rintro rfl
        have := hleaf j hij
        subst this
        exact hne rfl
      have hjl : j ≠ l := by
        rintro rfl
        have := hleaf i hij.symm
        subst this
        exact hne (Sym2.eq_swap)
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hil], by rwa [Function.update_of_ne hjl]⟩

theorem restrict_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlA : l ∉ A) (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (x : Fin n → Bool) :
    F G A (Function.update x l true) = F (G.deleteEdges {s(p, l), s(p, q)}) (insert p A) x := by
  have hpl : p ≠ l := hlp.ne.symm
  have hA : ∀ a ∈ A, Function.update x l true a = x a := fun a ha =>
    Function.update_of_ne (by rintro rfl; exact hlA ha) _ _
  have hG1 : ∀ i j, (G.deleteEdges {s(p, l), s(p, q)}).Adj i j → i ≠ p ∧ i ≠ l := by
    intro i j hij
    rw [deleteEdges_adj] at hij
    obtain ⟨hij, hne⟩ := hij
    constructor
    · rintro rfl
      rcases hp j hij with rfl | rfl
      · exact hne (by simp)
      · exact hne (by simp)
    · rintro rfl
      have := hleaf j hij
      subst this
      exact hne (by simp [Sym2.eq_swap])
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hA a ha] at h⟩
    · by_cases hip : i = p
      · subst hip
        exact Or.inl ⟨i, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hi⟩
      by_cases hjp : j = p
      · subst hjp
        exact Or.inl ⟨j, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hj⟩
      have hil : i ≠ l := by
        rintro rfl; exact hjp (hleaf j hij)
      have hjl : j ≠ l := by
        rintro rfl; exact hip (hleaf i hij.symm)
      right
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hip, hjp]
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · right
        exact ⟨l, a, hlp, by simp, by rwa [Function.update_of_ne hpl]⟩
      · exact Or.inl ⟨a, ha, by rwa [hA a ha]⟩
    · right
      have hi' := hG1 i j hij
      have hj' := hG1 j i hij.symm
      rw [deleteEdges_adj] at hij
      exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi'.2],
        by rwa [Function.update_of_ne hj'.2]⟩

def Cov {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T

theorem cov_insert {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (p : Fin n)
    (hS : ∀ e ∈ S, p ∈ e) (T : Finset (Fin n)) (hT : Cov (G.deleteEdges S) T) :
    Cov G (insert p T) := by
  intro i j hij
  by_cases he : s(i, j) ∈ S
  · have := hS _ he
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr (Finset.mem_insert_self _ _)
  · rcases hT i j ((deleteEdges_adj).2 ⟨hij, he⟩) with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)

theorem cov_swap {n : ℕ} (G : SimpleGraph (Fin n)) (l p l' : Fin n) (k : ℕ)
    (hll' : l' ≠ l) (hl'p : G.Adj p l') (hleaf' : ∀ w, G.Adj l' w → w = p)
    (hk : ∀ T, Cov G T → k ≤ T.card) (T : Finset (Fin n))
    (hT : Cov (G.deleteEdges {s(l, p)}) T) : k ≤ T.card := by
  have hS : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin n))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  by_cases hpT : p ∈ T
  · have := hk _ (cov_insert G _ p hS T hT)
    rwa [Finset.insert_eq_of_mem hpT] at this
  · have hl'T : l' ∈ T := by
      have hpl' : p ≠ l' := hl'p.ne
      rcases hT p l' ((deleteEdges_adj).2 ⟨hl'p, by
          simp [Sym2.eq_iff, hll', hpl'.symm]⟩) with h | h
      · exact absurd h hpT
      · exact h
    have hcov : Cov G (insert p (T.erase l')) := by
      intro i j hij
      by_cases hip : i = p
      · exact Or.inl (hip ▸ Finset.mem_insert_self _ _)
      by_cases hjp : j = p
      · exact Or.inr (hjp ▸ Finset.mem_insert_self _ _)
      have h0 : (G.deleteEdges {s(l, p)}).Adj i j :=
        (deleteEdges_adj).2 ⟨hij, by simp [Sym2.eq_iff, hip, hjp]⟩
      rcases hT i j h0 with h | h
      · have hil' : i ≠ l' := by
          rintro rfl; exact hjp (hleaf' j hij)
        exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hil', h⟩))
      · have hjl' : j ≠ l' := by
          rintro rfl; exact hip (hleaf' i hij.symm)
        exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjl', h⟩))
    have h1 := hk _ hcov
    have h2 := Finset.card_insert_le p (T.erase l')
    have h3 := Finset.card_erase_add_one hl'T
    omega

theorem ncard_del1 {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n) (h : G.Adj l p) :
    (G.deleteEdges {s(l, p)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.2 h)

theorem ncard_del2 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n) (h : G.Adj l p) :
    G.edgeSet.ncard ≤ (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard + 2 ∧
      (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  constructor
  · have h1 := Set.ncard_le_ncard_sdiff_add_ncard G.edgeSet ({s(p, l), s(p, q)} : Set (Sym2 (Fin n)))
    have h2 := Set.ncard_insert_le (s(p, l)) ({s(p, q)} : Set (Sym2 (Fin n)))
    rw [Set.ncard_singleton] at h2
    omega
  · have hmem : s(l, p) ∈ G.edgeSet := G.mem_edgeSet.2 h
    have hsub : G.edgeSet \ {s(p, l), s(p, q)} ⊆ G.edgeSet \ {s(l, p)} := by
      intro e he
      refine ⟨he.1, ?_⟩
      intro he'
      apply he.2
      rw [Set.mem_singleton_iff] at he'
      rw [he', Sym2.eq_swap]
      exact Set.mem_insert _ _
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_sdiff_singleton_lt_of_mem hmem
    omega

theorem noedge_ncard {n : ℕ} (G : SimpleGraph (Fin n)) (h : ∀ i j, ¬ G.Adj i j) :
    G.edgeSet.ncard = 0 := by
  have : G.edgeSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro e
    induction e using Sym2.ind with
    | _ i j => exact fun he => h i j (G.mem_edgeSet.1 he)
  rw [this, Set.ncard_empty]

theorem del_p_adj {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (i j : Fin n)
    (hij : (G.deleteEdges {s(p, l), s(p, q)}).Adj i j) : i ≠ p := by
  rw [deleteEdges_adj] at hij
  obtain ⟨hij, hne⟩ := hij
  rintro rfl
  rcases hp j hij with rfl | rfl
  · exact hne (by simp)
  · exact hne (by simp)

theorem claimQ : ∀ (m n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (k s : ℕ),
    G.edgeSet.ncard = m → G.IsAcyclic → (∀ i j, G.Adj i j → i ∉ A) →
    (∀ T, Cov G T → k ≤ T.card) → (A.Nonempty ∨ ∃ i j, G.Adj i j) →
    HasCircuitSize n (F G A) s → A.card + m + k ≤ s + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n G A k s hm hac hinv hk hne hC
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · push_neg at hE
    have hk0 : k ≤ (∅ : Finset (Fin n)).card := hk ∅ (fun i j h => absurd h (hE i j))
    have hm0 : m = 0 := by rw [← hm]; exact noedge_ncard G hE
    have := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    simp at hk0
    omega
  obtain ⟨l, p, hlp, hleaf, hcase⟩ := forest_good_leaf G hac hE
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := l.2; omega⟩
  have hlA : l ∉ A := hinv l p hlp
  have hpA : p ∉ A := hinv p l hlp.symm
  have hdepl := F_dep G A l p hlp hpA
  have hdepp := F_dep G A p l hlp.symm hlA
  have hs1 : 2 ≤ s + 1 := by
    have := dep_lower_set _ (F G A) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hdepl
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact hdepp) s hC
    rwa [Finset.card_pair hlp.ne] at this
  set G0 := G.deleteEdges {s(l, p)} with hG0
  have hm0 : G0.edgeSet.ncard + 1 = m := by rw [← hm]; exact ncard_del1 G l p hlp
  have hac0 : G0.IsAcyclic := hac.anti (deleteEdges_le _)
  have hinv0 : ∀ i j, G0.Adj i j → i ∉ A := fun i j h => hinv i j ((deleteEdges_adj).1 h).1
  have hS0 : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  have hrf : (fun x => F G A (Function.update x l false)) = F G0 A :=
    funext (restrict_false G A l p hlA hleaf)
  rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
  · set G1 := G.deleteEdges {s(p, l), s(p, q)} with hG1
    by_cases h0 : A.Nonempty ∨ ∃ i j, G0.Adj i j
    · have hrt : (fun x => F G A (Function.update x l true)) = F G1 (insert p A) :=
        funext (restrict_true G A l p q hlA hlp hleaf hq)
      have hnc : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
          F G A (Function.update x l b) ≠ F G A (Function.update y l b) := by
        intro b
        cases b
        · obtain ⟨x, y, hxy⟩ := F_nc G0 A h0
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrf x
          have e2 := congrFun hrf y
          rw [e1, e2]; exact hxy
        · obtain ⟨x, y, hxy⟩ := F_nc G1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrt x
          have e2 := congrFun hrt y
          rw [e1, e2]; exact hxy
      obtain ⟨b, s', hs', hC'⟩ := gate_elim_at n' (F G A) l s hdepl hnc hC
      cases b
      · rw [hrf] at hC'
        have hk0 : ∀ T, Cov G0 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS0 T hT)
          have := Finset.card_insert_le p T
          omega
        have := ih G0.edgeSet.ncard (by omega) _ G0 A (k - 1) s' rfl hac0 hinv0 hk0 h0 hC'
        omega
      · rw [hrt] at hC'
        have hS1 : ∀ e ∈ ({s(p, l), s(p, q)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
          intro e he
          rcases he with rfl | he
          · exact Sym2.mem_mk_left _ _
          · rw [Set.mem_singleton_iff] at he
            subst he
            exact Sym2.mem_mk_left _ _
        have hk1 : ∀ T, Cov G1 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS1 T hT)
          have := Finset.card_insert_le p T
          omega
        have hac1 : G1.IsAcyclic := hac.anti (deleteEdges_le _)
        have hinv1 : ∀ i j, G1.Adj i j → i ∉ insert p A := by
          intro i j h hi
          rcases Finset.mem_insert.1 hi with heq | hi
          · exact del_p_adj G l p q hq i j h heq
          · exact hinv i j ((deleteEdges_adj).1 h).1 hi
        obtain ⟨hc1, hc2⟩ := ncard_del2 G l p q hlp
        rw [← hG1] at hc1 hc2
        have := ih G1.edgeSet.ncard (by omega) _ G1 (insert p A) (k - 1) s' rfl hac1 hinv1
          hk1 (Or.inl (Finset.insert_nonempty _ _)) hC'
        rw [Finset.card_insert_of_notMem hpA] at this
        omega
    · push_neg at h0
      obtain ⟨hA0, hG00⟩ := h0
      have hm1 : m = 1 := by
        have := noedge_ncard G0 hG00
        omega
      have hk1 : k ≤ ({p} : Finset (Fin (n' + 1))).card := by
        apply hk
        intro i j hij
        have h1 := hG00 i j
        rw [deleteEdges_adj] at h1
        push_neg at h1
        have h2 := h1 hij
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at h2
        rcases h2 with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr (Finset.mem_singleton_self _)
        · exact Or.inl (Finset.mem_singleton_self _)
      rw [Finset.card_singleton] at hk1
      subst hA0
      simp only [Finset.card_empty]
      omega
  · obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    have hpl'0 : G0.Adj p l' := (deleteEdges_adj).2 ⟨hpl', by
      simp [Sym2.eq_iff, hl'l, hpl'.ne.symm]⟩
    have hnc0 : ∃ x y : Fin (n' + 1) → Bool,
        F G A (Function.update x l false) ≠ F G A (Function.update y l false) := by
      obtain ⟨x, y, hxy⟩ := F_nc G0 A (Or.inr ⟨p, l', hpl'0⟩)
      refine ⟨x, y, ?_⟩
      have e1 := congrFun hrf x
      have e2 := congrFun hrf y
      rw [e1, e2]; exact hxy
    have hC' := one_gate_at n' (F G A) l false s0 hdepl hnc0 hC
    rw [hrf] at hC'
    have hk0 : ∀ T, Cov G0 T → k ≤ T.card := cov_swap G l p l' k hl'l hpl' hleaf' hk
    have := ih G0.edgeSet.ncard (by omega) _ G0 A k s0 rfl hac0 hinv0 hk0
      (Or.inr ⟨p, l', hpl'0⟩) hC'
    omega

end Forest

theorem Forest : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x5 : Fin x1) (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x6 ≠ x8 → x6 ≠ x9 → x7 ≠ x8 → x7 ≠ x9 → x8 ≠ x9 → x3.Adj x6 x7 → x3.Adj x7 x8 → x3.Adj x8 x9 → ¬x3.Adj x9 x6) → (∃ (x7 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x3 x7 ∧ x7.card = x2) → (∀ (x8 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x3 x8 → x2 ≤ x8.card) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin x1 → Bool), x4.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin x1) (x12 : Fin x1), x3.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → x3.IsAcyclic → x3.edgeSet.ncard + x2 ≤ x4.size + (1 : ℕ) := by
  intro n t G C hE _ _ hmin hM hev hac
  have hC : PEqualNP.MetaComplexity.HasCircuitSize n (PEqualNP.Outside.L_meta_1740.Forest.F G ∅) C.size := by
    refine ⟨C, fun g hg => ⟨?_, (hM g hg).2⟩, le_refl _, fun x => ?_⟩
    · rcases (hM g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [Bool.eq_iff_iff, hev x, PEqualNP.Outside.L_meta_1740.Forest.F_true]
      simp
  have h := PEqualNP.Outside.L_meta_1740.Forest.claimQ G.edgeSet.ncard n G ∅ t C.size rfl hac
    (fun _ _ _ => Finset.notMem_empty _) (fun T hT => hmin T hT) (Or.inr hE) hC
  simpa using h

end PEqualNP.Outside.L_meta_1740

theorem PEqualNP.Outside.L_meta_1740 : ¬ (∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x5 : Fin x1) (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x6 ≠ x8 → x6 ≠ x9 → x7 ≠ x8 → x7 ≠ x9 → x8 ≠ x9 → x3.Adj x6 x7 → x3.Adj x7 x8 → x3.Adj x8 x9 → ¬x3.Adj x9 x6) → (∃ (x7 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x3 x7 ∧ x7.card = x2) → (∀ (x8 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x3 x8 → x2 ≤ x8.card) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin x1 → Bool), x4.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin x1) (x12 : Fin x1), x3.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ¬x3.IsAcyclic → x3.edgeSet.ncard + x2 ≤ x4.size + (1 : ℕ)) := by
  intro h
  apply PEqualNP.Outside.L_meta_1740.Cex
  intro n t G C hedge h4 ht hmin hmono hc
  by_cases ha : G.IsAcyclic
  · exact PEqualNP.Outside.L_meta_1740.Forest n t G C hedge h4 ht hmin hmono hc ha
  · exact h n t G C hedge h4 ht hmin hmono hc ha
