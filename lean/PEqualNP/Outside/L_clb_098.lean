import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_098_aux

variable {I : Type*} [DecidableEq I] [Fintype I]

abbrev Mask (U : Finset I) := {i : I // i ∉ U} → ZMod 2

def bit (x : Finset I) (i : I) : ZMod 2 := if i ∈ x then 1 else 0

def offset (U : Finset I) (d : Mask U) (i : I) : ZMod 2 :=
  if hi : i ∉ U then d ⟨i,hi⟩ else 0

def flip (U : Finset I) (d : Mask U) (x : Finset I) : Finset I :=
  Finset.univ.filter (fun i => bit x i + offset U d i = 1)

theorem bit_flip (U : Finset I) (d : Mask U) (x : Finset I) (i : I) :
    bit (flip U d x) i = bit x i + offset U d i := by
  have binary : ∀ b : ZMod 2, (if b = 1 then (1 : ZMod 2) else 0) = b := by decide
  have mem : i ∈ flip U d x ↔ bit x i + offset U d i = 1 := by
    simp [flip]
  change (if i ∈ flip U d x then (1 : ZMod 2) else 0) = bit x i + offset U d i
  split_ifs with h
  · exact (mem.mp h).symm
  · have h' := mt mem.mpr h
    simpa only [if_neg h'] using binary (bit x i + offset U d i)

theorem bit_injective_set (x y : Finset I) (h : ∀ i, bit x i = bit y i) : x = y := by
  ext i
  have hh := h i
  by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;> simp_all [bit]

theorem offset_add (U : Finset I) (d e : Mask U) (i : I) :
    offset U (d+e) i = offset U d i + offset U e i := by
  by_cases hi : i ∉ U <;> simp [offset,hi,Pi.add_apply]

theorem offset_zero (U : Finset I) (i : I) : offset U 0 i = 0 := by
  by_cases hi : i ∉ U <;> simp [offset,hi]

theorem flip_zero (U : Finset I) (x : Finset I) : flip U 0 x = x := by
  apply bit_injective_set
  intro i
  rw [bit_flip,offset_zero,add_zero]

theorem flip_add (U : Finset I) (d e : Mask U) (x : Finset I) :
    flip U (d+e) x = flip U d (flip U e x) := by
  apply bit_injective_set
  intro i
  simp only [bit_flip, offset_add]
  ac_rfl

theorem flip_twice (U : Finset I) (d : Mask U) (x : Finset I) :
    flip U d (flip U d x) = x := by
  have zero : d+d=0 := by
    funext i
    exact (show ∀ b : ZMod 2, b+b=0 from by decide) (d i)
  rw [← flip_add,zero,flip_zero]

theorem flip_injective (U : Finset I) (d : Mask U) : Function.Injective (flip U d) := by
  intro x y he
  have hs := congrArg (flip U d) he
  simpa only [flip_twice] using hs

theorem flip_inter (U : Finset I) (d : Mask U) (x S : Finset I) :
    flip U d (x ∩ S) ∩ S = flip U d x ∩ S := by
  ext i
  simp only [Finset.mem_inter]
  by_cases hi : i ∈ S
  · have h : bit (x ∩ S) i = bit x i := by simp [bit,hi]
    simp only [flip,Finset.mem_filter,Finset.mem_univ,true_and,hi,and_true,h]
  · simp [hi]

theorem flip_inter_inside (U : Finset I) (d : Mask U) (x S : Finset I) (sub : S ⊆ U) :
    flip U d x ∩ S = x ∩ S := by
  ext i
  simp only [Finset.mem_inter]
  by_cases hi : i ∈ S
  · have hiU := sub hi
    simp [flip,bit,offset,hi,hiU]
  · simp [hi]

theorem lift_along_flip (U x y : Finset I) (same : x ∩ U = y ∩ U) :
    ∃ d : Mask U, flip U d x = y := by
  refine ⟨fun i => bit y i.val - bit x i.val, ?_⟩
  apply bit_injective_set
  intro i
  rw [bit_flip]
  by_cases h : i ∈ U
  · have hx : i ∈ x ↔ i ∈ y := by
      have q : i ∈ x ∩ U ↔ i ∈ y ∩ U := by rw [same]
      simpa [h] using q
    simp [offset,h,bit,hx]
  · simp [offset,h,add_sub_cancel]

def fullRows (scope : I → Finset I) : Finset (I × Finset I) :=
  Finset.univ.filter (fun p => p.2 ⊆ scope p.1)

def reqRows (scope : I → Finset I) (x : Finset I) : Finset (I × Finset I) :=
  Finset.univ.image (fun i => (i, x ∩ scope i))

def projectedSites (scope : I → Finset I) (M : Finset (I × Finset I)) : Finset I :=
  (fullRows scope \ M).biUnion (fun p => scope p.1)

theorem scopeInside {scope : I → Finset I} {M : Finset (I × Finset I)}
    {i : I} {q : Finset I} (valid : q ⊆ scope i) (miss : (i,q) ∉ M) :
    scope i ⊆ projectedSites scope M := by
  intro j hj
  apply Finset.mem_biUnion.mpr
  refine ⟨(i,q), Finset.mem_sdiff.mpr ⟨?_,miss⟩, hj⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,valid⟩

theorem shiftRow {scope : I → Finset I} {M : Finset (I × Finset I)}
    (sub : M ⊆ fullRows scope) (d : Mask (projectedSites scope M))
    {i : I} {q : Finset I} (hq : (i,q) ∈ M) :
    (i, flip (projectedSites scope M) d q ∩ scope i) ∈ M := by
  by_contra absent
  have hs := scopeInside (Finset.inter_subset_right : flip (projectedSites scope M) d q ∩ scope i ⊆ scope i) absent
  have valid : q ⊆ scope i := (Finset.mem_filter.mp (sub hq)).2
  have eq : flip (projectedSites scope M) d q ∩ scope i = q :=
    (flip_inter_inside _ d q (scope i) hs).trans (Finset.inter_eq_left.mpr valid)
  rw [eq] at absent
  exact absent hq

theorem shiftReq {scope : I → Finset I} {M : Finset (I × Finset I)}
    (sub : M ⊆ fullRows scope) (d : Mask (projectedSites scope M))
    {x : Finset I} (h : reqRows scope x ⊆ M) :
    reqRows scope (flip (projectedSites scope M) d x) ⊆ M := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  have orig : (i,x∩scope i) ∈ M := h (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  simpa only [flip_inter] using shiftRow sub d orig

theorem shiftCover {scope : I → Finset I} {M : Finset (I × Finset I)}
    {X : Finset (Finset I)} (sub : M ⊆ fullRows scope)
    (d : Mask (projectedSites scope M)) (eq : X.biUnion (reqRows scope) = M) :
    (X.image (flip (projectedSites scope M) d)).biUnion (reqRows scope) = M := by
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨x,hx,hpx⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    apply shiftReq sub d _ hpx
    intro z hz
    rw [←eq]
    exact Finset.mem_biUnion.mpr ⟨y,hy,hz⟩
  · rintro ⟨i,q⟩ hq
    have hnew := shiftRow sub d hq
    have hnew' : (i, flip (projectedSites scope M) d q ∩ scope i) ∈ X.biUnion (reqRows scope) :=
      Eq.mpr (congrArg (fun T : Finset (I × Finset I) =>
        (i, flip (projectedSites scope M) d q ∩ scope i) ∈ T) eq) hnew
    obtain ⟨x,hx,hpx⟩ := Finset.mem_biUnion.mp hnew' 
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp hpx
    have hji := congrArg Prod.fst he
    change j = i at hji
    subst j
    have eqRow : x∩scope i = flip (projectedSites scope M) d q ∩ scope i :=
      congrArg Prod.snd he
    have qSub : q ⊆ scope i := (Finset.mem_filter.mp (sub hq)).2
    have finalEq : flip (projectedSites scope M) d x ∩ scope i = q := by
      calc
        _ = flip (projectedSites scope M) d (x ∩ scope i) ∩ scope i := (flip_inter _ _ _ _).symm
        _ = flip (projectedSites scope M) d (flip (projectedSites scope M) d q ∩ scope i) ∩ scope i := by rw [eqRow]
        _ = flip (projectedSites scope M) d (flip (projectedSites scope M) d q) ∩ scope i := flip_inter _ _ _ _
        _ = q := by rw [flip_twice, Finset.inter_eq_left.mpr qSub]
    apply Finset.mem_biUnion.mpr
    refine ⟨_,Finset.mem_image.mpr ⟨x,hx,rfl⟩,?_⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by rw [finalEq]⟩

end PEqualNP.Outside.L_clb_098_aux

namespace PEqualNP.Outside.L_clb_098_aux

open scoped BigOperators

theorem choose_two_pow_bit (n j : ℕ) : (n.choose (2 ^ j)).testBit 0 = n.testBit j := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := 2) (n := n) (k := 2 ^ j.succ)
    have h2 : n.choose (2 ^ j.succ) % 2 = (n/2).choose (2 ^ j) % 2 := by
      simpa [Nat.ModEq, pow_succ] using h
    rw [Nat.testBit_succ, ← ih (n / 2)]
    simp [Nat.testBit_zero, h2]

theorem powerset_supersets_card {S : Type*} [DecidableEq S]
    (M U : Finset S) (hu : U ⊆ M) :
    (M.powerset.filter (fun t => U ⊆ t)).card = 2 ^ (M \ U).card := by
  rw [← Finset.card_powerset]
  apply Finset.card_nbij' (fun t => t \ U) (fun v => v ∪ U)
  · intro t ht
    have ht' : t ∈ M.powerset ∧ U ⊆ t := Finset.mem_filter.mp ht
    apply Finset.mem_powerset.mpr
    intro x hx
    obtain ⟨hxt, hxu⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp ht'.1) hxt, hxu⟩
  · intro v hv
    have hv' : v ⊆ M \ U := Finset.mem_powerset.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.union_subset (hv'.trans Finset.sdiff_subset) hu), Finset.subset_union_right⟩
  · intro t ht
    exact Finset.sdiff_union_of_subset (Finset.mem_filter.mp ht).2
  · intro v hv
    apply Finset.union_sdiff_cancel_right
    rw [Finset.disjoint_left]
    intro x hxv hxU
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hv) hxv)).2 hxU

theorem powerset_supersets_mod {S : Type*} [DecidableEq S] (M U : Finset S) :
    (M.powerset.filter (fun t => U ⊆ t)).card ≡ (if U = M then 1 else 0) [MOD 2] := by
  by_cases hu : U ⊆ M
  · rw [powerset_supersets_card M U hu]
    by_cases e : U = M
    · simp [e,Nat.ModEq]
    · have hv : (M \ U).card ≠ 0 := by
        intro hz
        have hs : M \ U = ∅ := Finset.card_eq_zero.mp hz
        have hh := Finset.sdiff_union_of_subset hu
        rw [hs, Finset.empty_union] at hh
        exact e hh
      obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hv
      simp [e,hk,pow_succ,Nat.ModEq]
  · have e : M.powerset.filter (fun t => U ⊆ t) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro t ht
      obtain ⟨ht1,ht2⟩ := Finset.mem_filter.mp ht
      exact hu (ht2.trans (Finset.mem_powerset.mp ht1))
    have ne : U ≠ M := fun h => hu (h ▸ Finset.Subset.refl M)
    simp [e,ne,Nat.ModEq]

theorem coeff_cover_bit {W S : Type*} [DecidableEq W] [DecidableEq S]
    (pool : Finset W) (req : W → Finset S) (M : Finset S) (j : ℕ) :
    (M.powerset.filter (fun t => (pool.filter (fun w => req w ⊆ t)).card.testBit j = true)).card.testBit 0 =
      ((pool.powersetCard (2 ^ j)).filter (fun X => X.biUnion req = M)).card.testBit 0 := by
  classical
  let pass (t : Finset S) := pool.filter (fun w => req w ⊆ t)
  let K := pool.powersetCard (2 ^ j)
  let B (X : Finset W) := X.biUnion req
  have memEq (t : Finset S) :
      (pass t).powersetCard (2 ^ j) = K.filter (fun X => B X ⊆ t) := by
    ext X
    simp only [Finset.mem_filter, Finset.mem_powersetCard, K, B, Finset.biUnion_subset]
    constructor
    · rintro ⟨h,hc⟩
      refine ⟨⟨fun w hw => (Finset.mem_filter.mp (h hw)).1,hc⟩,?_⟩
      intro w hw
      exact (Finset.mem_filter.mp (h hw)).2
    · rintro ⟨⟨hs,hc⟩,hreq⟩
      exact ⟨fun w hw => Finset.mem_filter.mpr ⟨hs hw,hreq w hw⟩,hc⟩
  have bitMod (t : Finset S) :
      (if (pass t).card.testBit j = true then 1 else 0) ≡
        ((pass t).powersetCard (2 ^ j)).card [MOD 2] := by
    rw [Finset.card_powersetCard, ← choose_two_pow_bit (pass t).card j, Nat.testBit_zero]
    by_cases h : ((pass t).card.choose (2 ^ j)) % 2 = 1
    · simp [h,Nat.ModEq]
    · have hz : ((pass t).card.choose (2 ^ j)) % 2 = 0 := by omega
      simp [hz,Nat.ModEq]
  have h1 : (M.powerset.filter (fun t => (pass t).card.testBit j = true)).card ≡
      (∑ t ∈ M.powerset, ((pass t).powersetCard (2 ^ j)).card) [MOD 2] := by
    rw [Finset.card_filter]
    exact Nat.ModEq.sum (fun t _ => bitMod t)
  have h2 : (∑ t ∈ M.powerset, ((pass t).powersetCard (2 ^ j)).card) =
      ∑ X ∈ K, (M.powerset.filter (fun t => B X ⊆ t)).card := by
    simp_rw [memEq, Finset.card_filter]
    exact Finset.sum_comm
  have h3 : (∑ X ∈ K, (M.powerset.filter (fun t => B X ⊆ t)).card) ≡
      (K.filter (fun X => B X = M)).card [MOD 2] := by
    rw [Finset.card_filter]
    exact Nat.ModEq.sum (fun X _ => powerset_supersets_mod M (B X))
  have out := h1.trans (h2 ▸ h3)
  simp only [Nat.testBit_zero]
  rw [show (M.powerset.filter (fun t => (pass t).card.testBit j = true)).card % 2 =
      (K.filter (fun X => B X = M)).card % 2 from out]

end PEqualNP.Outside.L_clb_098_aux

namespace PEqualNP.Outside.L_clb_098_aux

theorem odd_exists_fixed {I α : Type*} [Fintype I] [Fintype α]
    (act : (I → ZMod 2) → α → α)
    (zero_act : ∀ a, act 0 a = a)
    (add_act : ∀ x y a, act (x + y) a = act x (act y a))
    (odd : Odd (Fintype.card α)) :
    ∃ a, ∀ x, act x a = a := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : AddAction (I → ZMod 2) α :=
    { vadd := act, zero_vadd := zero_act, add_vadd := add_act }
  have groupSize : Nat.card (I → ZMod 2) = 2 ^ Fintype.card I := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  have isGroup : IsAddPGroup 2 (I → ZMod 2) := IsAddPGroup.of_card groupSize
  have indiv : ¬ 2 ∣ Nat.card α := by
    rw [Nat.card_eq_fintype_card, Nat.dvd_iff_mod_eq_zero]
    exact fun h => by have := Nat.odd_iff.mp odd; omega
  obtain ⟨a, ha⟩ := isGroup.nonempty_fixed_point_of_prime_not_dvd_card α indiv
  exact ⟨a, ha⟩

theorem odd_exists_fixed_finset {I α : Type*} [Fintype I] [DecidableEq α] (S : Finset α)
    (act : (I → ZMod 2) → α → α)
    (zero_act : ∀ a, act 0 a = a)
    (add_act : ∀ x y a, act (x + y) a = act x (act y a))
    (stable : ∀ x a, a ∈ S → act x a ∈ S)
    (odd : Odd S.card) :
    ∃ a ∈ S, ∀ x, act x a = a := by
  let f (x : I → ZMod 2) (a : S) : S := ⟨act x a.val, stable x a.val a.property⟩
  have fzero (a : S) : f 0 a = a := Subtype.ext (zero_act a.val)
  have fadd (x y : I → ZMod 2) (a : S) : f (x+y) a = f x (f y a) :=
    Subtype.ext (add_act x y a.val)
  have hcard : Odd (Fintype.card S) := by simpa only [Fintype.card_coe] using odd
  obtain ⟨a, ha⟩ := odd_exists_fixed f fzero fadd hcard
  exact ⟨a.val, a.property, fun x => congrArg Subtype.val (ha x)⟩

end PEqualNP.Outside.L_clb_098_aux

namespace PEqualNP.Outside.L_clb_098_aux

variable {I : Type*} [DecidableEq I] [Fintype I]

theorem fixed_family_card (U : Finset I) (X : Finset (Finset I))
    (stable : ∀ x ∈ X, ∀ y : Finset I, x ∩ U = y ∩ U → y ∈ X) :
    X.card = (X.image (fun x => x ∩ U)).card * 2 ^ (Fintype.card I - U.card) := by
  let V : Finset I := Finset.univ \ U
  let projected := X.image (fun x => x ∩ U)
  let combinations := projected ×ˢ V.powerset
  let assemble (p : Finset I × Finset I) := p.1 ∪ p.2
  have smaller {q : Finset I} (hq : q ∈ projected) : q ⊆ U := by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.inter_subset_right
  have getLeft {q r : Finset I} (hq : q ⊆ U) (hr : r ⊆ V) : (q ∪ r) ∩ U = q := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hi | hi, hu⟩
      · exact hi
      · exact ((Finset.mem_sdiff.mp (hr hi)).2 hu).elim
    · intro hi
      exact ⟨Or.inl hi,hq hi⟩
  have getRight {q r : Finset I} (hq : q ⊆ U) (hr : r ⊆ V) : (q ∪ r) \ U = r := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hi | hi, hu⟩
      · exact (hu (hq hi)).elim
      · exact hi
    · intro hi
      exact ⟨Or.inr hi,(Finset.mem_sdiff.mp (hr hi)).2⟩
  have imageEq : combinations.image assemble = X := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨q,r⟩, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hq,hr⟩ := Finset.mem_product.mp hp
      obtain ⟨y,hy,ey⟩ := Finset.mem_image.mp hq
      have e : y ∩ U = (q ∪ r) ∩ U := ey.trans (getLeft (smaller hq) (Finset.mem_powerset.mp hr)).symm
      exact stable y hy _ e
    · intro hx
      have hr : x \ U ⊆ V := by
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hi).2⟩
      refine Finset.mem_image.mpr ⟨(x ∩ U, x \ U), Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩, Finset.mem_powerset.mpr hr⟩, ?_⟩
      change x ∩ U ∪ (x \ U) = x
      exact (Finset.union_comm _ _).trans (Finset.sdiff_union_inter _ _)
  have inj : Set.InjOn assemble combinations := by
    rintro ⟨q,r⟩ hp ⟨q',r'⟩ hp' he
    obtain ⟨hq,hr⟩ := Finset.mem_product.mp hp
    obtain ⟨hq',hr'⟩ := Finset.mem_product.mp hp'
    have eqLeft := congrArg (fun x => x ∩ U) he
    have eqRight := congrArg (fun x => x \ U) he
    change (q ∪ r) ∩ U = (q' ∪ r') ∩ U at eqLeft
    change (q ∪ r) \ U = (q' ∪ r') \ U at eqRight
    rw [getLeft (smaller hq) (Finset.mem_powerset.mp hr),
      getLeft (smaller hq') (Finset.mem_powerset.mp hr')] at eqLeft
    rw [getRight (smaller hq) (Finset.mem_powerset.mp hr),
      getRight (smaller hq') (Finset.mem_powerset.mp hr')] at eqRight
    exact Prod.ext eqLeft eqRight
  have hV : V.card = Fintype.card I - U.card := by
    change (Finset.univ \ U).card = _
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  calc
    X.card = (combinations.image assemble).card := congrArg Finset.card imageEq.symm
    _ = combinations.card := Finset.card_image_of_injOn inj
    _ = projected.card * 2 ^ V.card := by simp [combinations]
    _ = _ := by rw [hV]

end PEqualNP.Outside.L_clb_098_aux

namespace PEqualNP.Outside.L_clb_098_aux

variable {I : Type*} [DecidableEq I] [Fintype I]

def covers (scope : I → Finset I) (M : Finset (I × Finset I)) (j : ℕ) :
    Finset (Finset (Finset I)) :=
  ((Finset.univ : Finset (Finset I)).powersetCard (2^j)).filter (fun X => X.biUnion (reqRows scope) = M)

theorem invariant_cover (scope : I → Finset I) (M : Finset (I × Finset I))
    (sub : M ⊆ fullRows scope) (j : ℕ) (hCoeff : Odd (covers scope M j).card) :
    ∃ X : Finset (Finset I), X.card = 2^j ∧ X.biUnion (reqRows scope) = M ∧
      ∀ d : Mask (projectedSites scope M), X.image (flip (projectedSites scope M) d) = X := by
  let U := projectedSites scope M
  let act (d : Mask U) (X : Finset (Finset I)) := X.image (flip U d)
  have zero (X : Finset (Finset I)) : act 0 X = X := by
    have idFlip : flip U 0 = id := funext (flip_zero U)
    simp [act,idFlip]
  have add (d e : Mask U) (X : Finset (Finset I)) : act (d+e) X = act d (act e X) := by
    unfold act
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact flip_add U d e x
  have stable (d : Mask U) (X : Finset (Finset I)) (hX : X ∈ covers scope M j) :
      act d X ∈ covers scope M j := by
    have h := Finset.mem_filter.mp hX
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,?_⟩,?_⟩
    · unfold act
      rw [Finset.card_image_of_injective _ (flip_injective U d)]
      exact (Finset.mem_powersetCard.mp h.1).2
    · exact shiftCover sub d h.2
  obtain ⟨X,hX,hFix⟩ := odd_exists_fixed_finset (covers scope M j) act zero add stable hCoeff
  have hX' := Finset.mem_filter.mp hX
  exact ⟨X,(Finset.mem_powersetCard.mp hX'.1).2,hX'.2,hFix⟩

theorem card_power_factor {a d j : ℕ} (h : 2^j = a * 2^d) :
    d ≤ j ∧ a = 2^(j-d) := by
  have hp : 0 < (2 : ℕ)^j := by positivity
  have ha : 0 < a := by
    by_contra! he
    have hz : a = 0 := by omega
    rw [hz,zero_mul] at h
    omega
  have hle : (2 : ℕ)^d ≤ 2^j := by
    rw [h]
    simpa using Nat.mul_le_mul_right ((2 : ℕ)^d) (show 1 ≤ a by omega)
  have hdj : d ≤ j := by
    by_contra! hlt
    exact (Nat.not_lt_of_ge hle) (Nat.pow_lt_pow_right (by norm_num) hlt)
  refine ⟨hdj,?_⟩
  have hm : (2 : ℕ)^(j-d) * 2^d = a*2^d := by
    rw [← pow_add, Nat.sub_add_cancel hdj]
    exact h
  exact (Nat.eq_of_mul_eq_mul_right (by positivity) hm).symm

theorem projected_row_card {scope : I → Finset I} {M : Finset (I × Finset I)}
    {X : Finset (Finset I)} (U : Finset I) (exactCover : X.biUnion (reqRows scope) = M)
    (i : I) :
    ((M.filter (fun p => p.1 = i)).image (fun p => p.2 ∩ U)).card ≤ (X.image (fun x => x∩U)).card := by
  let Y := X.image (fun x => x∩U)
  have hsub : (M.filter (fun p => p.1 = i)).image (fun p => p.2 ∩ U) ⊆
      Y.image (fun y => y ∩ scope i) := by
    intro q hq
    obtain ⟨⟨a,b⟩, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hM, e⟩ := Finset.mem_filter.mp hp
    change a = i at e
    subst a
    have orig : (i,b) ∈ X.biUnion (reqRows scope) :=
      Eq.mpr (congrArg (fun T : Finset (I × Finset I) => (i,b) ∈ T) exactCover) hM
    obtain ⟨x,hx,hr⟩ := Finset.mem_biUnion.mp orig
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hr
    have ke : k=i := congrArg Prod.fst hk
    subst k
    have hb : x∩scope i = b := congrArg Prod.snd hk
    refine Finset.mem_image.mpr ⟨x∩U, Finset.mem_image.mpr ⟨x,hx,rfl⟩,?_⟩
    rw [← hb]
    ac_rfl
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem projected_from_coeff (scope : I → Finset I) (M : Finset (I × Finset I))
    (sub : M ⊆ fullRows scope) (j : ℕ)
    (fixedCard : ∀ (U : Finset I) (X : Finset (Finset I)),
      (∀ d : Mask U, X.image (flip U d) = X) →
      X.card = (X.image (fun x => x∩U)).card * 2^(Fintype.card I-U.card))
    (h : (M.powerset.filter (fun s =>
      ((Finset.univ : Finset (Finset I)).filter (fun x => reqRows scope x ⊆ s)).card.testBit j = true)).card.testBit 0 = true) :
    let U := projectedSites scope M
    Fintype.card I-U.card ≤ j ∧ ∀ i : I,
      ((M.filter (fun p => p.1 = i)).image (fun p => p.2 ∩ U)).card ≤ 2^(j-(Fintype.card I-U.card)) := by
  have hCover := coeff_cover_bit (Finset.univ : Finset (Finset I)) (reqRows scope) M j
  rw [h] at hCover
  have hOdd : Odd (covers scope M j).card :=
    Nat.odd_iff.mpr (Nat.mod_two_eq_one_iff_testBit_zero.mpr hCover.symm)
  obtain ⟨X,hx,heq,hfix⟩ := invariant_cover scope M sub j hOdd
  let U := projectedSites scope M
  have hc := fixedCard U X hfix
  rw [hx] at hc
  obtain ⟨hle,hProj⟩ := card_power_factor hc
  refine ⟨hle,?_⟩
  intro i
  exact (projected_row_card U heq i).trans (le_of_eq hProj)

end PEqualNP.Outside.L_clb_098_aux

namespace PEqualNP.Outside.L_clb_098_aux

open scoped BigOperators

theorem degreeBound :
∀ (n w : Nat) (hn : 0 < n),
  let Site := Fin n
  let Slot := Site × Finset Site
  let k := min n (w+1)
  let scope := fun i : Site => (Finset.range k).image
    (fun t => (⟨(i.val+t)%n, Nat.mod_lt _ hn⟩ : Site))
  let full := (Finset.univ : Finset Slot).filter (fun candidate => candidate.2 ⊆ scope candidate.1)
  let total := fun table : Finset Slot =>
    ((Finset.univ : Finset (Finset Site)).filter
      (fun x => ∀ i : Site, (i, x ∩ scope i) ∈ table)).card
  let coeff := fun (bit : Nat) (support : Finset Slot) =>
    ((support.powerset.filter (fun sub => (total sub).testBit bit)).card).testBit 0
  let degree := fun idx : Nat => (full.powerset.filter (fun mon => coeff idx mon = true)).sup Finset.card
  ∀ (j : Nat), j < n →
    (∀ M ∈ full.powerset, coeff j M = true →
      let U := (full \ M).biUnion (fun missing => scope missing.1)
      n-U.card ≤ j ∧
        ∀ i : Site,
          ((M.filter (fun item => item.1 = i)).image (fun entry => entry.2 ∩ U)).card ≤
            2^(j-(n-U.card))) →
    degree j + min (2^(k-1)) (1 + (n-j+k-1)/k) ≤ n*2^k := by
  classical
  intro n w hn Site Slot k scope full total coeff degree j hj projection
  have hk : 0 < k := by
    dsimp [k]
    exact Nat.lt_min.mpr ⟨hn, Nat.zero_lt_succ _⟩
  have hkn : k ≤ n := Nat.min_le_left _ _
  have scopeCard (i : Site) : (scope i).card = k := by
    dsimp [scope]
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have aLt : a < n := (Finset.mem_range.mp ha).trans_le hkn
    have bLt : b < n := (Finset.mem_range.mp hb).trans_le hkn
    have eq : (i.val + a) % n = (i.val + b) % n := congrArg Fin.val hab
    have modEq := Nat.ModEq.add_left_cancel' i.val (show i.val + a ≡ i.val + b [MOD n] from eq)
    exact Nat.ModEq.eq_of_lt_of_lt modEq aLt bLt
  let rowFull (i : Site) := full.filter (fun p => p.1 = i)
  have rowCard (i : Site) : (rowFull i).card = 2 ^ k := by
    have rowEq : rowFull i = (scope i).powerset.image (Prod.mk i) := by
      ext p
      rcases p with ⟨a, b⟩
      constructor
      · intro hp
        obtain ⟨hFull, hEq⟩ := Finset.mem_filter.mp hp
        change a = i at hEq
        subst a
        have hScope : b ⊆ scope i := (Finset.mem_filter.mp hFull).2
        exact Finset.mem_image.mpr ⟨b, Finset.mem_powerset.mpr hScope, rfl⟩
      · intro hp
        obtain ⟨c, hc, hEq⟩ := Finset.mem_image.mp hp
        cases hEq
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_powerset.mp hc⟩, rfl⟩
    rw [rowEq, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h),
      Finset.card_powerset, scopeCard]
  have fullCard : full.card = n * 2 ^ k := by
    rw [← show (∑ i : Site, (rowFull i).card) = full.card by
      simpa [rowFull] using Finset.sum_card_fiberwise_eq_card_filter full
        (Finset.univ : Finset Site) (fun p => p.1)]
    simp [rowCard, Site]
  let bound := min (2^(k-1)) (1 + (n-j+k-1)/k)
  have boundLe : bound ≤ full.card := by
    unfold bound
    refine (Nat.min_le_left _ _).trans ?_
    rw [fullCard]
    have hp : (2 : Nat) ^ (k-1) ≤ 2^k := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    refine hp.trans ?_
    simpa using Nat.mul_le_mul_right (2^k) hn
  have supportBound : ∀ M ∈ full.powerset.filter (fun mon => coeff j mon = true),
      M.card ≤ full.card - bound := by
    intro M hM
    obtain ⟨hM, hCoeff⟩ := Finset.mem_filter.mp hM
    have hSub := Finset.mem_powerset.mp hM
    let D := full \ M
    let d := D.card
    let U := D.biUnion (fun missing => scope missing.1)
    obtain ⟨hLeft, hRight⟩ := projection M hM hCoeff
    change n - U.card ≤ j at hLeft
    change ∀ i : Site, ((M.filter (fun item => item.1 = i)).image
      (fun entry => entry.2 ∩ U)).card ≤ 2^(j-(n-U.card)) at hRight
    have hCardD : d + M.card = full.card := Finset.card_sdiff_add_card_eq_card hSub
    have hDpos : 0 < d := by
      by_contra h
      have dZero : d = 0 := by omega
      have dEmpty : D = ∅ := Finset.card_eq_zero.mp dZero
      have uEmpty : U = ∅ := by simp [U, dEmpty]
      simp [uEmpty] at hLeft
      omega
    have uCard : U.card ≤ d*k := by
      unfold U
      refine Finset.card_biUnion_le.trans ?_
      simp [scopeCard, d]
    have uLe : U.card ≤ n := by
      simpa [Site] using Finset.card_le_univ U
    have hMin : bound ≤ d := by
      by_cases hl : 2^(k-1) ≤ d
      · exact (Nat.min_le_left _ _).trans hl
      have hsmall : d < 2^(k-1) := by omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hDpos
      let i := p.1
      have scopeSub : scope i ⊆ U := fun x hx =>
        Finset.mem_biUnion.mpr ⟨p, hp, hx⟩
      let row := M.filter (fun q => q.1 = i)
      have rowInter : rowFull i ∩ M = row := by
        ext q
        simp only [rowFull, row, Finset.mem_inter, Finset.mem_filter]
        exact ⟨fun ⟨⟨_, hEq⟩, hq⟩ => ⟨hq, hEq⟩,
          fun ⟨hq, hEq⟩ => ⟨⟨hSub hq, hEq⟩, hq⟩⟩
      have dRowLe : (rowFull i \ M).card ≤ d := by
        exact Finset.card_le_card (fun q hq =>
          Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp hq).1).1,
            (Finset.mem_sdiff.mp hq).2⟩)
      have rowBig : 2^(k-1) < row.card := by
        have split : (rowFull i \ M).card + row.card = 2^k := by
          rw [Finset.card_sdiff, Finset.inter_comm M (rowFull i), rowInter, rowCard]
          have hRowLe : row.card ≤ 2^k := by
            rw [← rowCard i, ← rowInter]
            exact Finset.card_le_card Finset.inter_subset_left
          omega
        have hPower : (2 : Nat)^k = 2^(k-1)*2 := by
          calc
            (2 : Nat)^k = 2^(k-1+1) := congrArg (fun a : Nat => 2^a) (by omega)
            _ = _ := pow_succ _ _
        omega
      have rowImage : (row.image (fun entry => entry.2 ∩ U)).card = row.card := by
        apply Finset.card_image_of_injOn
        intro p hp q hq hEq
        have pEq := (Finset.mem_filter.mp hp).2
        have qEq := (Finset.mem_filter.mp hq).2
        have pSub : p.2 ⊆ U :=
          ((Finset.mem_filter.mp (hSub (Finset.mem_filter.mp hp).1)).2.trans
            (pEq.symm ▸ scopeSub))
        have qSub : q.2 ⊆ U :=
          ((Finset.mem_filter.mp (hSub (Finset.mem_filter.mp hq).1)).2.trans
            (qEq.symm ▸ scopeSub))
        exact Prod.ext (pEq.trans qEq.symm)
          (by simpa only [Finset.inter_eq_left.mpr pSub, Finset.inter_eq_left.mpr qSub] using hEq)
      have hProj := hRight i
      change (row.image _).card ≤ _ at hProj
      rw [rowImage] at hProj
      have hExp : k ≤ j - (n-U.card) := by
        have hStrict := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : Nat))).mp
          (rowBig.trans_le hProj)
        omega
      have hMul : n - j + k ≤ d*k := by omega
      have hDiv : (n-j+k-1)/k < d := (Nat.div_lt_iff_lt_mul hk).mpr (by omega)
      exact (Nat.min_le_right _ _).trans (by omega)
    omega
  have degLe : degree j ≤ full.card - bound := Finset.sup_le supportBound
  omega

end PEqualNP.Outside.L_clb_098_aux

theorem PEqualNP.Outside.L_clb_098 : (∀ (n w : Nat) (hn : 0 < n),
  let Site := Fin n
  let Slot := Site × Finset Site
  let k := min n (w+1)
  let scope := fun i : Site => (Finset.range k).image
    (fun t => (⟨(i.val+t)%n, Nat.mod_lt _ hn⟩ : Site))
  let full := (Finset.univ : Finset Slot).filter (fun candidate => candidate.2 ⊆ scope candidate.1)
  let total := fun table : Finset Slot =>
    ((Finset.univ : Finset (Finset Site)).filter
      (fun x => ∀ i : Site, (i, x ∩ scope i) ∈ table)).card
  let coeff := fun (bit : Nat) (support : Finset Slot) =>
    ((support.powerset.filter (fun sub => (total sub).testBit bit)).card).testBit 0
  let degree := fun idx : Nat => (full.powerset.filter (fun mon => coeff idx mon = true)).sup Finset.card
  ∀ (j : Nat), j < n →
    (∀ M ∈ full.powerset, coeff j M = true →
      let U := (full \ M).biUnion (fun missing => scope missing.1)
      n-U.card ≤ j ∧
        ∀ i : Site,
          ((M.filter (fun item => item.1 = i)).image (fun entry => entry.2 ∩ U)).card ≤
            2^(j-(n-U.card))) ∧
    degree j + min (2^(k-1)) (1 + (n-j+k-1)/k) ≤ n*2^k) := by
  classical
  intro n w hn Site Slot k scope full total coeff degree j hj
  have totals (s : Finset Slot) :
      total s = ((Finset.univ : Finset (Finset Site)).filter
        (fun x => PEqualNP.Outside.L_clb_098_aux.reqRows scope x ⊆ s)).card := by
    change ((Finset.univ : Finset (Finset Site)).filter
      (fun x => ∀ i : Site, (i,x∩scope i) ∈ s)).card = _
    congr 1
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hx p hp
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      exact hx i
    · intro hx i
      exact hx (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have fixedCard (U : Finset Site) (X : Finset (Finset Site))
      (hFix : ∀ d : PEqualNP.Outside.L_clb_098_aux.Mask U,
        X.image (PEqualNP.Outside.L_clb_098_aux.flip U d) = X) :
      X.card = (X.image (fun x => x∩U)).card * 2^(Fintype.card Site-U.card) := by
    apply PEqualNP.Outside.L_clb_098_aux.fixed_family_card U X
    intro x hx y hey
    obtain ⟨d,hd⟩ := PEqualNP.Outside.L_clb_098_aux.lift_along_flip U x y hey
    rw [←hFix d]
    exact Finset.mem_image.mpr ⟨x,hx,hd⟩
  have first : ∀ M ∈ full.powerset, coeff j M = true →
      let U := (full \ M).biUnion (fun missing => scope missing.1)
      n-U.card ≤ j ∧
        ∀ i : Site,
          ((M.filter (fun item => item.1 = i)).image (fun entry => entry.2 ∩ U)).card ≤
            2^(j-(n-U.card)) := by
    intro M hM hCoeff
    have ho : (M.powerset.filter (fun s =>
      ((Finset.univ : Finset (Finset Site)).filter (fun x =>
        PEqualNP.Outside.L_clb_098_aux.reqRows scope x ⊆ s)).card.testBit j = true)).card.testBit 0 = true := by
      simpa only [coeff,totals] using hCoeff
    have proj := PEqualNP.Outside.L_clb_098_aux.projected_from_coeff scope M
      (Finset.mem_powerset.mp hM) j fixedCard ho
    have sizeSite : Fintype.card Site = n := Fintype.card_fin n
    simpa only [PEqualNP.Outside.L_clb_098_aux.projectedSites,
      PEqualNP.Outside.L_clb_098_aux.fullRows,full,sizeSite] using proj
  exact ⟨first, PEqualNP.Outside.L_clb_098_aux.degreeBound n w hn j hj first⟩
