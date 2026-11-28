import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1067

open Finset

variable {n : ℕ}

abbrev R (D : Fin n → Finset (Fin n)) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen (fun i j : Fin n => j ∈ D i)

def IsSrc (D : Fin n → Finset (Fin n)) (i : Fin n) : Prop := ∀ j, R D j i → R D i j

variable {D : Fin n → Finset (Fin n)}

lemma IsSrc.of_reach {p k : Fin n} (hp : IsSrc D p) (hkp : R D k p) : IsSrc D k :=
  fun j hjk => hkp.trans (hp j (hjk.trans hkp))

lemma IsSrc.mutual {j k : Fin n} (hj : IsSrc D j) (hjk : j ∈ D k) : R D k j ∧ R D j k :=
  ⟨.single hjk, hj k (.single hjk)⟩

lemma IsSrc.reader {j k : Fin n} (hj : IsSrc D j) (hjk : j ∈ D k) : IsSrc D k :=
  hj.of_reach (.single hjk)

lemma exists_src (j : Fin n) : ∃ p, IsSrc D p ∧ R D p j := by
  classical
  obtain ⟨p, hp, hmin⟩ := (univ.filter (fun i => R D i j)).exists_min_image
    (fun i => (univ.filter (fun k => R D k i)).card) ⟨j, mem_filter.2 ⟨mem_univ _, .refl⟩⟩
  rw [mem_filter] at hp
  refine ⟨p, fun k hkp => ?_, hp.2⟩
  have hsub : univ.filter (fun i => R D i k) ⊆ univ.filter (fun i => R D i p) := by
    intro i; simp only [mem_filter, mem_univ, true_and]; exact fun h => h.trans hkp
  have heq := eq_of_subset_of_card_le hsub (hmin k (by simp [hkp.trans hp.2]))
  have hp' : p ∈ univ.filter (fun i => R D i k) := heq ▸ mem_filter.2 ⟨mem_univ _, .refl⟩
  exact (mem_filter.1 hp').2

section classes

variable (Sset : Finset (Fin n)) (hS : ∀ i, i ∈ Sset ↔ IsSrc D i)
  (cls : Fin n → Finset (Fin n)) (hcls : ∀ i j, j ∈ cls i ↔ R D i j ∧ R D j i)

include hcls in
lemma self_mem (i : Fin n) : i ∈ cls i := (hcls i i).2 ⟨.refl, .refl⟩

include hcls in
lemma cls_eq {p k : Fin n} (hpk : R D p k) (hkp : R D k p) : cls k = cls p := by
  ext j
  rw [hcls, hcls]
  exact ⟨fun h => ⟨hpk.trans h.1, h.2.trans hkp⟩, fun h => ⟨hkp.trans h.1, h.2.trans hpk⟩⟩

include hcls in
lemma mem_cls_iff_of_read {p j k : Fin n} (hj : IsSrc D j) (hjk : j ∈ D k) :
    j ∈ cls p ↔ k ∈ cls p := by
  obtain ⟨hkj, hjk'⟩ := hj.mutual hjk
  rw [hcls, hcls]
  exact ⟨fun h => ⟨h.1.trans hjk', hkj.trans h.2⟩, fun h => ⟨h.1.trans hkj, hjk'.trans h.2⟩⟩

variable [DecidableEq (Fin n)]

def reps : Finset (Fin n) := Sset.filter (fun i => ∀ j ∈ cls i, i ≤ j)

include hS hcls in
lemma exists_rep {p : Fin n} (hp : IsSrc D p) : ∃ m ∈ reps Sset cls, cls m = cls p := by
  set m := (cls p).min' ⟨p, self_mem cls hcls p⟩
  obtain ⟨hpm, hmp⟩ := (hcls p m).1 (min'_mem _ _)
  have hm := cls_eq cls hcls hpm hmp
  refine ⟨m, mem_filter.2 ⟨(hS m).2 (hp.of_reach hmp), fun j hj => ?_⟩, hm⟩
  exact min'_le _ _ (hm ▸ hj)

include hcls in
lemma rep_unique {i k : Fin n} (hi : i ∈ reps Sset cls) (hk : k ∈ reps Sset cls)
    (hki : k ∈ cls i) : k = i := by
  obtain ⟨hik, hki'⟩ := (hcls i k).1 hki
  refine le_antisymm ?_ ((mem_filter.1 hi).2 k hki)
  exact (mem_filter.1 hk).2 i (cls_eq cls hcls hik hki' ▸ self_mem cls hcls i)

include hS hcls in
lemma card_reps [DecidableEq (Finset (Fin n))] :
    (reps Sset cls).card = (Sset.image cls).card := by
  refine card_bij (fun i _ => cls i) (fun i hi => mem_image_of_mem cls (mem_filter.1 hi).1)
    (fun i hi k hk h => rep_unique Sset cls hcls hk hi (h ▸ self_mem cls hcls i))
    (fun c hc => ?_)
  obtain ⟨p, hp, rfl⟩ := mem_image.1 hc
  obtain ⟨m, hm, hmp⟩ := exists_rep Sset hS cls hcls ((hS p).1 hp)
  exact ⟨m, hm, hmp⟩

end classes

section upper

variable (T : Fin n → (Fin n → ZMod 2) → ZMod 2)
  (hloc : ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y)
  (hlock : ∀ x, ∑ i, (x i + T i x) = 0)

include hloc hlock in
lemma class_sum_eq (cls : Fin n → Finset (Fin n)) (hcls : ∀ i j, j ∈ cls i ↔ R D i j ∧ R D j i)
    {p : Fin n} (hp : IsSrc D p) {x x' : Fin n → ZMod 2} (hx : ∀ j, ¬IsSrc D j → x j = x' j) :
    ∑ k ∈ cls p, (x k + T k x) = ∑ k ∈ cls p, (x' k + T k x') := by
  classical
  set c := cls p
  set y : Fin n → ZMod 2 := fun j => if j ∈ c then x' j else x j
  have hout : ∀ k ∉ c, y k + T k y = x k + T k x := by
    intro k hk
    refine congrArg₂ (· + ·) (ite_eq_right hk)
      (hloc k y x fun j hj => ite_eq_right fun hjc => hk ?_)
    exact (mem_cls_iff_of_read cls hcls (hp.of_reach ((hcls p j).1 hjc).2) hj).1 hjc
  have hin : ∀ k ∈ c, y k + T k y = x' k + T k x' := by
    intro k hk
    refine congrArg₂ (· + ·) (ite_eq_left hk) (hloc k y x' fun j hj => ?_)
    by_cases hjc : j ∈ c
    · exact ite_eq_left hjc
    · exact (ite_eq_right hjc).trans
        (hx j fun hjs => hjc ((mem_cls_iff_of_read cls hcls hjs hj).2 hk))
  have h1 := hlock y
  have h2 := hlock x
  rw [← sum_add_sum_compl c, sum_congr rfl hin,
    sum_congr rfl fun k hk => hout k (mem_compl.1 hk)] at h1
  rw [← sum_add_sum_compl c] at h2
  exact add_right_cancel (h2.trans h1.symm)

include hloc hlock in
theorem upper [DecidableEq (Fin n)] [DecidableEq (Finset (Fin n))]
    [DecidableEq (Fin n → ZMod 2)] (Sset : Finset (Fin n)) (hS : ∀ i, i ∈ Sset ↔ IsSrc D i)
    (cls : Fin n → Finset (Fin n)) (hcls : ∀ i j, j ∈ cls i ↔ R D i j ∧ R D j i) :
    (univ.image (fun x i => x i + T i x)).card ≤ 2 ^ (n - (Sset.image cls).card) := by
  rw [← card_reps Sset hS cls hcls]
  set Q := reps Sset cls
  let key := fun (x : Fin n → ZMod 2) (i : {i // i ∉ Q}) =>
    if i.1 ∈ Sset then x i.1 + T i.1 x else x i.1
  have hinj : ∀ x x', key x = key x' → (fun i => x i + T i x) = fun i => x' i + T i x' := by
    intro x x' hk
    have hkey : ∀ i ∉ Q, (if i ∈ Sset then x i + T i x else x i) =
        if i ∈ Sset then x' i + T i x' else x' i := fun i hi => congrFun hk ⟨i, hi⟩
    have hx : ∀ j, ¬IsSrc D j → x j = x' j := by
      intro j hj
      have hjS : j ∉ Sset := fun h => hj ((hS j).1 h)
      simpa [hjS] using hkey j fun h => hjS (mem_filter.1 h).1
    have hsrc : ∀ i ∈ Sset, i ∉ Q → x i + T i x = x' i + T i x' :=
      fun i hi hiQ => by simpa [hi] using hkey i hiQ
    funext i
    by_cases hi : IsSrc D i
    · by_cases hiQ : i ∈ Q
      · have hrest : ∀ k ∈ (cls i).erase i, x k + T k x = x' k + T k x' := by
          intro k hk
          have hki := mem_of_mem_erase hk
          exact hsrc k ((hS k).2 (hi.of_reach ((hcls i k).1 hki).2))
            fun hkQ => ne_of_mem_erase hk (rep_unique Sset cls hcls hiQ hkQ hki)
        have hsum := class_sum_eq T hloc hlock cls hcls hi hx
        rw [← add_sum_erase _ _ (self_mem cls hcls i), ← add_sum_erase _ _ (self_mem cls hcls i),
          sum_congr rfl hrest] at hsum
        exact add_right_cancel hsum
      · exact hsrc i ((hS i).2 hi) hiQ
    · show x i + T i x = x' i + T i x'
      rw [hx i hi, hloc i x x' fun j hj => hx j fun hjs => hi (hjs.reader hj)]
  calc (univ.image (fun x i => x i + T i x)).card
      ≤ (univ : Finset ({i // i ∉ Q} → ZMod 2)).card := by
        refine card_le_card_of_injOn (fun v => key (Function.invFun (fun x i => x i + T i x) v))
          (by intro _ _; simp) ?_
        intro v hv v' hv' h
        obtain ⟨x, -, rfl⟩ := mem_image.1 hv
        obtain ⟨x', -, rfl⟩ := mem_image.1 hv'
        have := hinj _ _ h
        rwa [Function.invFun_eq (f := fun x i => x i + T i x) ⟨x, rfl⟩,
          Function.invFun_eq (f := fun x i => x i + T i x) ⟨x', rfl⟩] at this
    _ = 2 ^ (n - Q.card) := by simp

end upper

section lower

def Lay (D : Fin n → Finset (Fin n)) (Q : Finset (Fin n)) : ℕ → Fin n → Prop
  | 0, j => j ∈ Q
  | m + 1, j => Lay D Q m j ∨ ∃ k, Lay D Q m k ∧ j ∈ D k

lemma lay_of_reach {Q : Finset (Fin n)} {q j : Fin n} (hq : q ∈ Q) (h : R D q j) :
    ∃ m, Lay D Q m j := by
  induction h with
  | refl => exact ⟨0, hq⟩
  | tail _ hbc ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + 1, Or.inr ⟨_, hm, hbc⟩⟩

lemma exists_owner (Q : Finset (Fin n)) (hQ : ∀ j, ∃ q ∈ Q, R D q j)
    (hread : ∀ j, ∃ i, j ∈ D i) :
    ∃ (owner : Fin n → Fin n) (d : Fin n → ℕ),
      (∀ j, j ∈ D (owner j)) ∧ ∀ j ∉ Q, d (owner j) < d j := by
  classical
  have hex : ∀ j, ∃ m, Lay D Q m j := fun j => by
    obtain ⟨q, hq, h⟩ := hQ j
    exact lay_of_reach hq h
  have hown : ∀ j, ∃ k, j ∈ D k ∧ (j ∉ Q → Nat.find (hex k) < Nat.find (hex j)) := by
    intro j
    by_cases hj : j ∈ Q
    · obtain ⟨k, hk⟩ := hread j
      exact ⟨k, hk, fun h => absurd hj h⟩
    · have hspec := Nat.find_spec (hex j)
      have h0 : Nat.find (hex j) ≠ 0 := fun h0 => hj (by rw [h0] at hspec; exact hspec)
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
      rw [hm] at hspec ⊢
      rcases hspec with h | ⟨k, hk, hjk⟩
      · exact absurd h (Nat.find_min (hex j) (by omega))
      · exact ⟨k, hjk, fun _ => Nat.lt_succ_of_le (Nat.find_min' (hex k) hk)⟩
  choose owner howner hlt using hown
  exact ⟨owner, fun j => Nat.find (hex j), howner, hlt⟩

variable [DecidableEq (Fin n)] (owner : Fin n → Fin n)

def Tof (i : Fin n) (x : Fin n → ZMod 2) : ZMod 2 := ∑ j, if owner j = i then x j else 0

def Fof (x : Fin n → ZMod 2) : Fin n → ZMod 2 := fun i => x i + Tof owner i x

lemma Tof_sub (i : Fin n) (x y : Fin n → ZMod 2) :
    Tof owner i (x - y) = Tof owner i x - Tof owner i y := by
  simp only [Tof, ← sum_sub_distrib, Pi.sub_apply]
  exact sum_congr rfl fun j _ => by split_ifs <;> simp

lemma Fof_sub (x y : Fin n → ZMod 2) : Fof owner (x - y) = Fof owner x - Fof owner y := by
  funext i
  simp only [Fof, Tof_sub, Pi.sub_apply]
  ring

lemma Tof_local (howner : ∀ j, j ∈ D (owner j)) (i : Fin n) (x y : Fin n → ZMod 2)
    (h : ∀ j ∈ D i, x j = y j) : Tof owner i x = Tof owner i y :=
  sum_congr rfl fun j _ => by split_ifs with hj <;> [exact h j (hj ▸ howner j); rfl]

lemma Tof_lock (x : Fin n → ZMod 2) : ∑ i, (x i + Tof owner i x) = 0 := by
  simp only [Tof, sum_add_distrib]
  rw [sum_comm]
  simp [CharTwo.add_self_eq_zero]

lemma ker_trivial {Q : Finset (Fin n)} {d : Fin n → ℕ} (hlt : ∀ j ∉ Q, d (owner j) < d j)
    {y : Fin n → ZMod 2} (hy : Fof owner y = 0) (hyQ : ∀ q ∈ Q, y q = 0) : y = 0 := by
  have heq : ∀ i, y i = Tof owner i y := fun i => CharTwo.add_eq_zero.1 (congrFun hy i)
  have key : ∀ m i, i ∉ Q → univ.sup d < d i + m → y i = 0 := by
    intro m
    induction m with
    | zero => intro i _ h; have := le_sup (f := d) (mem_univ i); omega
    | succ m ih =>
      intro i _ h
      rw [heq i]
      refine sum_eq_zero fun j _ => ?_
      split_ifs with hji
      · by_cases hjQ : j ∈ Q
        · exact hyQ j hjQ
        · exact ih j hjQ (by have := hlt j hjQ; rw [hji] at this; omega)
      · rfl
  funext i
  by_cases hiQ : i ∈ Q
  · exact hyQ i hiQ
  · exact key (univ.sup d + 1) i hiQ (by omega)

theorem lower [DecidableEq (Finset (Fin n))] [DecidableEq (Fin n → ZMod 2)]
    (Sset : Finset (Fin n)) (hS : ∀ i, i ∈ Sset ↔ IsSrc D i)
    (cls : Fin n → Finset (Fin n)) (hcls : ∀ i j, j ∈ cls i ↔ R D i j ∧ R D j i)
    (hread : ∀ j, ∃ i, j ∈ D i) :
    ∃ owner : Fin n → Fin n, (∀ j, j ∈ D (owner j)) ∧
      (∀ i x y, (∀ j ∈ D i, x j = y j) → Tof owner i x = Tof owner i y) ∧
      (∀ x, ∑ i, (x i + Tof owner i x) = 0) ∧
      (univ.image (Fof owner)).card = 2 ^ (n - (Sset.image cls).card) ∧
      ∀ v, Nat.card {x // Fof owner x = v} = 0 ∨
        Nat.card {x // Fof owner x = v} = 2 ^ (Sset.image cls).card := by
  rw [← card_reps Sset hS cls hcls]
  set Q := reps Sset cls
  have hQ : ∀ j, ∃ q ∈ Q, R D q j := by
    intro j
    obtain ⟨p, hp, hpj⟩ := exists_src j
    obtain ⟨m, hm, hmp⟩ := exists_rep Sset hS cls hcls hp
    exact ⟨m, hm, ((hcls p m).1 (hmp ▸ self_mem cls hcls m)).2.trans hpj⟩
  obtain ⟨owner, d, howner, hlt⟩ := exists_owner Q hQ hread
  refine ⟨owner, howner, Tof_local owner howner, Tof_lock owner, ?_⟩

  set K := (univ.filter fun x => Fof owner x = 0).card
  have hK : K ≤ 2 ^ Q.card := by
    calc K ≤ (univ : Finset ({q // q ∈ Q} → ZMod 2)).card := by
          refine card_le_card_of_injOn (fun x q => x q.1) (by intro _ _; simp) ?_
          intro x hx x' hx' h
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hx hx'
          refine sub_eq_zero.1 (ker_trivial owner hlt (by rw [Fof_sub, hx, hx', sub_zero])
            fun q hq => ?_)
          rw [Pi.sub_apply, sub_eq_zero]
          exact congrFun h ⟨q, hq⟩
      _ = 2 ^ Q.card := by simp

  have hfib : ∀ x0, (univ.filter fun x => Fof owner x = Fof owner x0).card = K := by
    intro x0
    refine card_nbij' (fun x => x - x0) (fun x => x + x0) ?_ ?_ ?_ ?_ <;> intro x hx <;>
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
    · rw [Fof_sub, hx, sub_self]
    · rw [← sub_eq_zero, ← Fof_sub, add_sub_cancel_right, hx]
    · exact sub_add_cancel x x0
    · exact add_sub_cancel_right x x0
  have htot : (univ.image (Fof owner)).card * K = 2 ^ n := by
    calc (univ.image (Fof owner)).card * K
        = ∑ v ∈ univ.image (Fof owner), (univ.filter fun x => Fof owner x = v).card :=
          (sum_const_nat fun v hv => by obtain ⟨x0, -, rfl⟩ := mem_image.1 hv; exact hfib x0).symm
      _ = 2 ^ n := by rw [← card_eq_sum_card_image]; simp

  have hup : (univ.image (Fof owner)).card ≤ 2 ^ (n - Q.card) := by
    have := upper (Tof owner) (Tof_local owner howner) (Tof_lock owner) Sset hS cls hcls
    rwa [← card_reps Sset hS cls hcls] at this
  have hpow : 2 ^ (n - Q.card) * 2 ^ Q.card = 2 ^ n := by
    rw [← pow_add, Nat.sub_add_cancel ((card_le_univ Q).trans (by simp))]

  have hK0 : 0 < K := card_pos.2 ⟨0, by simpa using Fof_sub owner 0 0⟩
  have hI : (univ.image (Fof owner)).card = 2 ^ (n - Q.card) := by
    refine le_antisymm hup (le_of_not_gt fun hlt => ?_)
    have := Nat.mul_lt_mul_of_lt_of_le hlt hK (by positivity)
    rw [htot, hpow] at this
    exact lt_irrefl _ this
  have hKeq : K = 2 ^ Q.card := by
    have h2 : 2 ^ (n - Q.card) * K = 2 ^ (n - Q.card) * 2 ^ Q.card := by
      rw [← hI, htot, hI, hpow]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  refine ⟨hI, fun v => ?_⟩
  by_cases hv : ∃ x0, Fof owner x0 = v
  · obtain ⟨x0, rfl⟩ := hv
    right
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hfib x0, hKeq]
  · left
    exact Nat.card_eq_zero.2 (Or.inl ⟨fun x => hv ⟨x.1, x.2⟩⟩)

end lower

end PEqualNP.Outside.L_lib_1067

theorem PEqualNP.Outside.L_lib_1067 :
(
∀ (n : Nat) (D : Fin n → Finset (Fin n)),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let W := Fin n → ZMod 2
  let edge := fun i j : Fin n => j ∈ D i
  let reach := Relation.ReflTransGen edge
  let src := fun i : Fin n => ∀ j, reach j i → reach i j
  let cls := fun i : Fin n => Finset.univ.filter (fun j => reach i j ∧ reach j i)
  let s := ((Finset.univ.filter src).image cls).card
  let localT := fun (T : Fin n → W → ZMod 2) =>
    ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y
  let out := fun (T : Fin n → W → ZMod 2) (x : W) (i : Fin n) => x i + T i x
  let lock := fun T => ∀ x, (∑ i : Fin n, out T x i) = 0
  let size := fun T => (Finset.univ.image (out T)).card
  (∀ j, ∃ i, edge i j) →
  (∀ T, localT T → lock T → size T ≤ 2^(n-s)) ∧
    ∃ owner : Fin n → Fin n, (∀ j, edge (owner j) j) ∧
      let T := fun (i : Fin n) (x : W) => ∑ j, if owner j = i then x j else 0
      localT T ∧ lock T ∧ size T = 2^(n-s) ∧
        ∀ v : W, let count := Nat.card {x : W // out T x = v}
                 count = 0 ∨ count = 2^s
) := by
  intro n D W edge reach src cls s localT out lock size hread
  let _ : ∀ p : Prop, Decidable p := Classical.propDecidable
  have hS : ∀ i, i ∈ Finset.univ.filter src ↔ L_lib_1067.IsSrc D i := fun i => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have hcls : ∀ i j, j ∈ cls i ↔ L_lib_1067.R D i j ∧ L_lib_1067.R D j i := fun i j => by
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  exact ⟨fun T hT hl => L_lib_1067.upper T hT hl _ hS cls hcls,
    L_lib_1067.lower _ hS cls hcls hread⟩
