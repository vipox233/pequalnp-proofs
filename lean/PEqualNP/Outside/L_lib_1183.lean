import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1183_aux

lemma card_filter_add_card_filter_not {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card + (s.filter (fun a => ¬ p a)).card = s.card := by
  have hdisj : Disjoint (s.filter p) (s.filter (fun a => ¬ p a)) := by
    rw [Finset.disjoint_left]
    intro a h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hunion : s.filter p ∪ s.filter (fun a => ¬ p a) = s := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases h : p a <;> simp [h]
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

def sdiffU {n : Nat} (x y : Finset (Fin n)) : Finset (Fin n) := (x \ y) ∪ (y \ x)

lemma sdiffU_comm {n : Nat} (x y : Finset (Fin n)) : sdiffU x y = sdiffU y x :=
  Finset.union_comm _ _

lemma sdiffU_invol {n : Nat} (x y : Finset (Fin n)) : sdiffU (sdiffU x y) y = x := by
  ext a
  simp only [sdiffU, Finset.mem_union, Finset.mem_sdiff]
  by_cases ha : a ∈ x <;> by_cases hb : a ∈ y <;> simp [ha, hb]

lemma sdiffU_invol_left {n : Nat} (x y : Finset (Fin n)) : sdiffU x (sdiffU x y) = y := by
  rw [sdiffU_comm x (sdiffU x y), sdiffU_comm x y, sdiffU_invol]

lemma sdiffU_eq_empty_iff {n : Nat} (x y : Finset (Fin n)) : sdiffU x y = ∅ ↔ x = y := by
  constructor
  · intro h
    ext a
    have ha : a ∉ sdiffU x y := by rw [h]; simp
    simp only [sdiffU, Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not] at ha
    exact ⟨ha.1, ha.2⟩
  · rintro rfl
    simp [sdiffU]

def chi {n : Nat} (E x : Finset (Fin n)) : Int := (-1 : Int) ^ (E ∩ x).card

lemma chi_comm {n : Nat} (E x : Finset (Fin n)) : chi E x = chi x E := by
  simp only [chi, Finset.inter_comm]

lemma chi_empty_left {n : Nat} (x : Finset (Fin n)) : chi ∅ x = 1 := by
  simp [chi]

lemma chi_empty_right {n : Nat} (E : Finset (Fin n)) : chi E ∅ = 1 := by
  simp [chi]

lemma chi_singleton {n : Nat} (E : Finset (Fin n)) (u : Fin n) :
    chi E {u} = if u ∈ E then -1 else 1 := by
  by_cases hu : u ∈ E
  · have h : E ∩ {u} = {u} := by ext a; simp [hu]
    simp [chi, h, hu]
  · have h : E ∩ {u} = ∅ := by ext a; simp; rintro ha rfl; exact hu ha
    simp [chi, h, hu]

lemma chi_mul_sdiffU {n : Nat} (E x y : Finset (Fin n)) :
    chi E (sdiffU x y) = chi E x * chi E y := by
  let A := E ∩ x
  let B := E ∩ y
  have hinter : E ∩ sdiffU x y = (A \ B) ∪ (B \ A) := by
    ext a
    simp only [A, B, sdiffU, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    by_cases hE : a ∈ E <;> by_cases hx : a ∈ x <;> by_cases hy : a ∈ y <;> simp [hE, hx, hy]
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_sdiff.mp ha).1
  have hc1 := Finset.card_sdiff_add_card_inter A B
  have hc2 := Finset.card_sdiff_add_card_inter B A
  have hc_comm : (B ∩ A).card = (A ∩ B).card := by rw [Finset.inter_comm]
  have hcard : (E ∩ sdiffU x y).card + 2 * (A ∩ B).card = A.card + B.card := by
    rw [hinter, Finset.card_union_of_disjoint hdisj]
    omega
  simp only [chi]
  calc
    (-1 : Int) ^ (E ∩ sdiffU x y).card
        = (-1 : Int) ^ (E ∩ sdiffU x y).card * ((-1 : Int) ^ 2) ^ (A ∩ B).card := by norm_num
    _ = (-1 : Int) ^ ((E ∩ sdiffU x y).card + 2 * (A ∩ B).card) := by
          rw [pow_add, pow_mul]
    _ = (-1 : Int) ^ (A.card + B.card) := by rw [hcard]
    _ = (-1 : Int) ^ A.card * (-1 : Int) ^ B.card := pow_add _ _ _

lemma sum_chi_eq {n : Nat} (E : Finset (Fin n)) :
    (∑ x : Finset (Fin n), chi E x) = if E = ∅ then (2 ^ n : Int) else 0 := by
  by_cases hE : E = ∅
  · subst hE
    simp only [↓reduceIte, chi_empty_left, Finset.sum_const, Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · simp only [hE, ↓reduceIte]
    rcases Finset.nonempty_iff_ne_empty.mpr hE with ⟨u, hu⟩
    have hshift : (∑ x : Finset (Fin n), chi E x) =
        ∑ x : Finset (Fin n), chi E (sdiffU x {u}) := by
      refine Finset.sum_bij (fun x _ => sdiffU x {u}) (fun _ _ => Finset.mem_univ _)
        (fun x1 _ x2 _ heq => by
          have := congrArg (fun z => sdiffU z {u}) heq
          simpa [sdiffU_invol] using this)
        (fun y _ => ⟨sdiffU y {u}, Finset.mem_univ _, sdiffU_invol y {u}⟩)
        (fun x _ => by rw [sdiffU_invol])
    have hneg : (∑ x : Finset (Fin n), chi E (sdiffU x {u})) =
        -(∑ x : Finset (Fin n), chi E x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [chi_mul_sdiffU, chi_singleton, if_pos hu]
      ring
    linarith

lemma card_powersetCard_two_sum {n : Nat} (g : Finset (Fin n) → Int) :
    2 * (∑ d ∈ (Finset.univ : Finset (Fin n)).powersetCard 2, g d) =
      ∑ u : Fin n, ∑ v ∈ (Finset.univ : Finset (Fin n)).erase u, g {u, v} := by
  let S : Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n)).offDiag
  have hS : (∑ p ∈ S, g {p.1, p.2}) =
      ∑ u : Fin n, ∑ v ∈ (Finset.univ : Finset (Fin n)).erase u, g {u, v} := by
    have h1 : S = (Finset.univ : Finset (Fin n)).biUnion
        (fun u => ((Finset.univ : Finset (Fin n)).erase u).image (fun v => (u, v))) := by
      ext ⟨u, v⟩
      simp [S, Finset.mem_offDiag, ne_comm]
    rw [h1, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_image]
      intro v1 _ v2 _ heq
      exact congrArg Prod.snd heq
    · intro u1 _ u2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, heq⟩
      exact hne (congrArg Prod.fst heq).symm
  rw [← hS]
  have hmaps : ∀ p ∈ S, ({p.1, p.2} : Finset (Fin n)) ∈
      (Finset.univ : Finset (Fin n)).powersetCard 2 := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    simp [Finset.mem_powersetCard, Finset.card_pair hne]
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun p => g {p.1, p.2})
  rw [← hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdc : d.card = 2 := (Finset.mem_powersetCard.mp hd).2
  rcases Finset.card_eq_two.mp hdc with ⟨a, b, hab, rfl⟩
  have hset : S.filter (fun p => ({p.1, p.2} : Finset (Fin n)) = {a, b}) = {(a, b), (b, a)} := by
    ext ⟨u, v⟩
    simp only [S, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨huv, heq⟩
      have hu : u ∈ ({a, b} : Finset (Fin n)) := by rw [← heq]; simp
      have hv : v ∈ ({a, b} : Finset (Fin n)) := by rw [← heq]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl huv
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl huv
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hab, rfl⟩
      · exact ⟨hab.symm, Finset.pair_comm _ _⟩
  rw [hset]
  have hpair_ne : (a, b) ≠ (b, a) := fun h => hab (congrArg Prod.fst h)
  rw [Finset.sum_pair hpair_ne, Finset.pair_comm b a]
  ring

lemma sum_chi_ball {n : Nat} (E : Finset (Fin n)) :
    2 * (∑ d ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun d => d.card ≤ 2), chi E d) =
      ((n : Int) + 1 - 2 * (E.card : Int)) ^ 2 - ((n : Int) - 1) := by
  let B0 : Finset (Finset (Fin n)) := Finset.univ.filter (fun d => d.card ≤ 2)
  let P0 : Finset (Finset (Fin n)) := {∅}
  let P1 : Finset (Finset (Fin n)) := Finset.univ.powersetCard 1
  let P2 : Finset (Finset (Fin n)) := Finset.univ.powersetCard 2
  have hpart : B0 = P0 ∪ (P1 ∪ P2) := by
    ext d
    simp only [B0, P0, P1, P2, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_powersetCard, Finset.subset_univ]
    rw [← Finset.card_eq_zero]
    omega
  have hd12 : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]
    intro d h1 h2
    have c1 := (Finset.mem_powersetCard.mp h1).2
    have c2 := (Finset.mem_powersetCard.mp h2).2
    omega
  have hd0 : Disjoint P0 (P1 ∪ P2) := by
    rw [Finset.disjoint_left]
    intro d h0 h12
    simp only [P0, Finset.mem_singleton] at h0
    subst h0
    rcases Finset.mem_union.mp h12 with h1 | h2
    · have c1 := (Finset.mem_powersetCard.mp h1).2; simp at c1
    · have c2 := (Finset.mem_powersetCard.mp h2).2; simp at c2
  have hsum_split : (∑ d ∈ B0, chi E d) =
      (∑ d ∈ P0, chi E d) + (∑ d ∈ P1, chi E d) + (∑ d ∈ P2, chi E d) := by
    rw [hpart, Finset.sum_union hd0, Finset.sum_union hd12, add_assoc]
  have hS0 : (∑ d ∈ P0, chi E d) = 1 := by simp [P0, chi_empty_right]
  have hL : (∑ u : Fin n, chi E {u}) = (n : Int) - 2 * (E.card : Int) := by
    have h1 : (∑ u : Fin n, chi E {u}) = ∑ u : Fin n, (if u ∈ E then (-1 : Int) else 1) :=
      Finset.sum_congr rfl (fun u _ => chi_singleton E u)
    rw [h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    have hE_eq : (Finset.univ.filter (fun u : Fin n => u ∈ E)) = E := by ext u; simp
    have hEc_card : (Finset.univ.filter (fun u : Fin n => u ∉ E)).card + E.card = n := by
      have h := card_filter_add_card_filter_not (Finset.univ : Finset (Fin n)) (fun u => u ∈ E)
      rw [hE_eq, Finset.card_univ, Fintype.card_fin] at h
      omega
    rw [hE_eq]
    simp only [nsmul_eq_mul, mul_neg, mul_one]
    omega
  have hS1 : (∑ d ∈ P1, chi E d) = (n : Int) - 2 * (E.card : Int) := by
    rw [← hL]
    refine (Finset.sum_bij (fun u _ => ({u} : Finset (Fin n)))
      (fun u _ => by simp [P1, Finset.mem_powersetCard])
      (fun u1 _ u2 _ heq => Finset.singleton_injective heq)
      (fun d hd => by
        rcases Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hd).2 with ⟨u, rfl⟩
        exact ⟨u, Finset.mem_univ u, rfl⟩)
      (fun _ _ => rfl)).symm
  have hS2 : 2 * (∑ d ∈ P2, chi E d) = ((n : Int) - 2 * (E.card : Int)) ^ 2 - (n : Int) := by
    have h2 := card_powersetCard_two_sum (chi E)
    have hterm : ∀ u : Fin n, ∀ v ∈ (Finset.univ : Finset (Fin n)).erase u,
        chi E {u, v} = chi E {u} * chi E {v} := by
      intro u v hv
      have hne : v ≠ u := (Finset.mem_erase.mp hv).1
      have hsd : ({u, v} : Finset (Fin n)) = sdiffU {u} {v} := by
        ext a
        simp only [sdiffU, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union,
          Finset.mem_sdiff]
        by_cases hau : a = u <;> by_cases hav : a = v <;> simp [hau, hav, hne.symm]
        · exact hne
      rw [hsd, chi_mul_sdiffU]
    have hsum_er :
        (∑ u : Fin n, ∑ v ∈ (Finset.univ : Finset (Fin n)).erase u, chi E {u, v}) =
        (∑ u : Fin n, chi E {u}) ^ 2 - (n : Int) := by
      have hrew :
          (∑ u : Fin n, ∑ v ∈ (Finset.univ : Finset (Fin n)).erase u, chi E {u, v}) =
          ∑ u : Fin n, ∑ v ∈ (Finset.univ : Finset (Fin n)).erase u, chi E {u} * chi E {v} :=
        Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v hv => hterm u v hv))
      rw [hrew]
      have hadd :
          (∑ u : Fin n, ∑ v ∈ (Finset.univ : Finset (Fin n)).erase u, chi E {u} * chi E {v}) +
          (∑ u : Fin n, chi E {u} * chi E {u}) =
          (∑ u : Fin n, chi E {u}) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        have hstep : ∀ u : Fin n,
            (∑ v ∈ (Finset.univ : Finset (Fin n)).erase u, chi E {u} * chi E {v}) +
            chi E {u} * chi E {u} = ∑ v : Fin n, chi E {u} * chi E {v} := fun u =>
          Finset.sum_erase_add _ _ (Finset.mem_univ u)
        simp_rw [hstep, ← Finset.mul_sum, ← Finset.sum_mul, sq]
      have hsq1 : (∑ u : Fin n, chi E {u} * chi E {u}) = (n : Int) := by
        have h1 : ∀ u : Fin n, chi E {u} * chi E {u} = 1 := fun u => by
          rw [chi_singleton]; split_ifs <;> norm_num
        simp [h1]
      linarith
    rw [h2, hsum_er, hL]
  change 2 * (∑ d ∈ B0, chi E d) = _
  rw [hsum_split, hS0, hS1]
  linarith

lemma card_ball_zero (n : Nat) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun d => d.card ≤ 2)).card =
      1 + n + Nat.choose n 2 := by
  let P0 : Finset (Finset (Fin n)) := {∅}
  let P1 : Finset (Finset (Fin n)) := Finset.univ.powersetCard 1
  let P2 : Finset (Finset (Fin n)) := Finset.univ.powersetCard 2
  have hpart : (Finset.univ : Finset (Finset (Fin n))).filter (fun d => d.card ≤ 2) =
      P0 ∪ (P1 ∪ P2) := by
    ext d
    simp only [P0, P1, P2, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_powersetCard, Finset.subset_univ]
    rw [← Finset.card_eq_zero]
    omega
  have hd12 : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]
    intro d h1 h2
    have c1 := (Finset.mem_powersetCard.mp h1).2
    have c2 := (Finset.mem_powersetCard.mp h2).2
    omega
  have hd0 : Disjoint P0 (P1 ∪ P2) := by
    rw [Finset.disjoint_left]
    intro d h0 h12
    simp only [P0, Finset.mem_singleton] at h0
    subst h0
    rcases Finset.mem_union.mp h12 with h1 | h2
    · have c1 := (Finset.mem_powersetCard.mp h1).2; simp at c1
    · have c2 := (Finset.mem_powersetCard.mp h2).2; simp at c2
  rw [hpart, Finset.card_union_of_disjoint hd0, Finset.card_union_of_disjoint hd12]
  simp [P0, P1, P2, Finset.card_powersetCard, add_assoc]

lemma sum_ball_eq_sum_sdiffU {n : Nat} (x : Finset (Fin n)) (g : Finset (Fin n) → Int) :
    (∑ c ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun c => (sdiffU x c).card ≤ 2), g c) =
      ∑ d ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun d => d.card ≤ 2), g (sdiffU x d) := by
  refine Finset.sum_bij (fun c _ => sdiffU x c)
    (fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hc)
    (fun c1 _ c2 _ heq => by
      have := congrArg (sdiffU x) heq
      simpa [sdiffU_invol_left] using this)
    (fun d hd => by
      refine ⟨sdiffU x d, ?_, sdiffU_invol_left x d⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      rw [sdiffU_invol_left]
      exact hd)
    (fun c _ => by rw [sdiffU_invol_left])

lemma two_mul_even_ind (k : Nat) :
    2 * ((if Even k then 1 else 0 : Nat) : Int) = 1 + (-1 : Int) ^ k := by
  rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · have hev : Even (r + r) := ⟨r, rfl⟩
    rw [if_pos hev]
    have hpow : (-1 : Int) ^ (r + r) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [hpow]
    norm_num
  · have hnev : ¬ Even (2 * r + 1) := by
      rintro ⟨m, hm⟩
      omega
    rw [if_neg hnev]
    have hpow : (-1 : Int) ^ (2 * r + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [hpow]
    norm_num

lemma balanced_region_of_even (n : Nat) (hn : 3 ≤ n) (i : Fin n)
    (hev : Even (1 + n + Nat.choose n 2)) :
    let Word := Finset (Fin n)
    let cube := (Finset.univ : Finset Word)
    let triples := (Finset.univ : Finset (Fin n)).powersetCard 3
    let region := fun (s : Word → Word) => cube.filter (fun x =>
      ∀ E ∈ triples, x ∩ E ≠ s E ∩ E)
    ∃ s : Word → Word, (region s).card = 1 + n + Nat.choose n 2 ∧
      2 * ((region s).filter (fun x => i ∈ x)).card = 1 + n + Nat.choose n 2 := by
  dsimp only
  let old : Finset (Fin n) := Finset.univ.erase i
  have hold_card : old.card = n - 1 := by
    simp [old]
  let small : Finset (Finset (Fin n)) := old.powerset.filter (fun y => y.card ≤ 1)
  let shell : Finset (Finset (Fin n)) := old.powersetCard 2
  have hsmall_card : small.card = n := by
    have hpart : small = {∅} ∪ old.powersetCard 1 := by
      ext y
      simp only [small, Finset.mem_filter, Finset.mem_powerset, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_powersetCard, Finset.card_eq_zero]
      constructor
      · rintro ⟨hy, hc⟩
        by_cases hc0 : y.card = 0
        · exact Or.inl (Finset.card_eq_zero.mp hc0)
        · exact Or.inr ⟨hy, by omega⟩
      · rintro (rfl | ⟨hy, hc⟩)
        · exact ⟨Finset.empty_subset _, by simp⟩
        · exact ⟨hy, by omega⟩
    have hdisj : Disjoint ({∅} : Finset (Finset (Fin n))) (old.powersetCard 1) := by
      rw [Finset.disjoint_left]
      intro y hy0 hy1
      simp only [Finset.mem_singleton] at hy0
      subst hy0
      have hc := (Finset.mem_powersetCard.mp hy1).2
      simp at hc
    rw [hpart, Finset.card_union_of_disjoint hdisj, Finset.card_singleton,
      Finset.card_powersetCard, hold_card, Nat.choose_one_right]
    omega
  have hshell_card : shell.card = Nat.choose (n - 1) 2 := by
    simp [shell, Finset.card_powersetCard, hold_card]
  have hV_eq : 1 + n + Nat.choose n 2 = 2 * n + shell.card := by
    have hch : Nat.choose n 2 = Nat.choose (n - 1) 2 + (n - 1) := by
      have hn1 : n = (n - 1) + 1 := by omega
      conv_lhs => rw [hn1]
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    rw [hshell_card, hch]
    omega
  have hshell_half : 2 * (shell.card / 2) = shell.card := by
    rcases hev with ⟨r, hr⟩
    omega
  rcases Finset.exists_subset_card_eq (s := shell) (n := shell.card / 2) (by omega) with
    ⟨F, hFsub, hFcard⟩
  let R : Finset (Finset (Fin n)) := Finset.univ.filter (fun x =>
    (x.erase i).card ≤ 1 ∨ ((x.erase i).card = 2 ∧ (i ∈ x ↔ x.erase i ∈ F)))
  let s : Finset (Fin n) → Finset (Fin n) := fun E =>
    if i ∉ E then E else if E.erase i ∈ F then E.erase i else E
  have hreg_eq : (Finset.univ : Finset (Finset (Fin n))).filter (fun x =>
      ∀ E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, x ∩ E ≠ s E ∩ E) = R := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, R]
    constructor
    · intro hx
      have hcard_le : (x.erase i).card ≤ 2 := by
        by_contra hgt
        push Not at hgt
        rcases Finset.exists_subset_card_eq (s := x.erase i) (n := 3) (by omega) with
          ⟨E, hEsub, hEc⟩
        have hEtri : E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3 :=
          Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hEc⟩
        have hiE : i ∉ E := fun hi => (Finset.mem_erase.mp (hEsub hi)).1 rfl
        have hEx : E ⊆ x := Finset.Subset.trans hEsub (Finset.erase_subset i x)
        have hbad := hx E hEtri
        apply hbad
        simp only [s, if_pos hiE, Finset.inter_self]
        exact Finset.inter_eq_right.mpr hEx
      by_cases hle1 : (x.erase i).card ≤ 1
      · exact Or.inl hle1
      · right
        have hcard2 : (x.erase i).card = 2 := by omega
        refine ⟨hcard2, ?_⟩
        let y := x.erase i
        let E := insert i y
        have hiy : i ∉ y := Finset.notMem_erase i x
        have hEc : E.card = 3 := by
          rw [Finset.card_insert_of_notMem hiy]
          change (x.erase i).card + 1 = 3
          omega
        have hEtri : E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3 :=
          Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hEc⟩
        have hiE : i ∈ E := Finset.mem_insert_self i y
        have hEer : E.erase i = y := Finset.erase_insert hiy
        have hbad := hx E hEtri
        simp only [s, if_neg (not_not.mpr hiE), hEer] at hbad
        by_cases hix : i ∈ x
        · have hxE : x ∩ E = E := by
            ext a
            simp only [Finset.mem_inter, E, y, Finset.mem_insert, Finset.mem_erase]
            constructor
            · exact fun h => h.2
            · rintro (rfl | ⟨_, hax⟩)
              · exact ⟨hix, Or.inl rfl⟩
              · exact ⟨hax, Or.inr ⟨by assumption, hax⟩⟩
          constructor
          · intro _
            by_contra hyF
            rw [if_neg hyF, Finset.inter_self, hxE] at hbad
            exact hbad rfl
          · intro _; exact hix
        · have hxE : x ∩ E = y := by
            ext a
            simp only [Finset.mem_inter, E, y, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨hax, rfl | ⟨hne, _⟩⟩
              · exact absurd hax hix
              · exact ⟨hne, hax⟩
            · rintro ⟨hne, hax⟩
              exact ⟨hax, Or.inr ⟨hne, hax⟩⟩
          have hyE : y ∩ E = y := Finset.inter_eq_left.mpr (Finset.subset_insert i y)
          constructor
          · intro h; exact absurd h hix
          · intro hyF
            rw [if_pos hyF, hyE, hxE] at hbad
            exact absurd rfl hbad
    · intro hx E hEtri hEq
      have hEc : E.card = 3 := (Finset.mem_powersetCard.mp hEtri).2
      have hcard_le : (x.erase i).card ≤ 2 := by
        rcases hx with h1 | ⟨h2, _⟩ <;> omega
      by_cases hiE : i ∉ E
      · simp only [s, if_pos hiE, Finset.inter_self] at hEq
        have hEx : E ⊆ x := by
          intro a ha
          have ha' : a ∈ x ∩ E := by rw [hEq]; exact ha
          exact (Finset.mem_inter.mp ha').1
        have hEer : E ⊆ x.erase i := fun a ha =>
          Finset.mem_erase.mpr ⟨fun h => hiE (h ▸ ha), hEx ha⟩
        have := Finset.card_le_card hEer
        omega
      · push Not at hiE
        let y := E.erase i
        have hyc : y.card = 2 := by
          have := Finset.card_erase_of_mem hiE
          change (E.erase i).card = 2
          omega
        have hysubE : y ⊆ E := Finset.erase_subset i E
        have hys : y ⊆ s E ∩ E := by
          simp only [s, if_neg (not_not.mpr hiE)]
          split_ifs
          · exact Finset.subset_inter (Finset.Subset.refl y) hysubE
          · exact Finset.subset_inter hysubE hysubE
        have hyx : y ⊆ x := fun a ha => (Finset.mem_inter.mp (hEq ▸ hys ha)).1
        have hyxer : y ⊆ x.erase i := fun a ha =>
          Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1, hyx ha⟩
        have hy_eq : y = x.erase i := Finset.eq_of_subset_of_card_le hyxer (by omega)
        have hcard2 : (x.erase i).card = 2 := by rw [← hy_eq]; exact hyc
        have hiff : i ∈ x ↔ y ∈ F := by
          rcases hx with h1 | ⟨_, h2⟩
          · omega
          · rwa [hy_eq]
        simp only [s, if_neg (not_not.mpr hiE)] at hEq
        by_cases hyF : y ∈ F
        · rw [if_pos hyF] at hEq
          have hix : i ∈ x := hiff.mpr hyF
          have hi_in : i ∈ x ∩ E := Finset.mem_inter.mpr ⟨hix, hiE⟩
          rw [hEq] at hi_in
          exact (Finset.mem_erase.mp (Finset.mem_inter.mp hi_in).1).1 rfl
        · rw [if_neg hyF, Finset.inter_self] at hEq
          have hnix : i ∉ x := fun h => hyF (hiff.mp h)
          have hi_in : i ∈ x ∩ E := by rw [hEq]; exact hiE
          exact hnix (Finset.mem_inter.mp hi_in).1
  have hdisj_in : Disjoint small F := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    have c1 := (Finset.mem_filter.mp hy1).2
    have c2 := (Finset.mem_powersetCard.mp (hFsub hy2)).2
    omega
  have hdisj_out : Disjoint small (shell \ F) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    have c1 := (Finset.mem_filter.mp hy1).2
    have c2 := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hy2).1).2
    omega
  have hRin_card : (R.filter (fun x => i ∈ x)).card = n + shell.card / 2 := by
    have hbij : (R.filter (fun x => i ∈ x)).card = (small ∪ F).card := by
      refine Finset.card_bij (fun x _ => x.erase i)
        (fun x hx => by
          simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have hsub : x.erase i ⊆ old := fun a ha =>
            Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1, Finset.mem_univ a⟩
          rcases hx.1 with h1 | ⟨_, hiff⟩
          · exact Finset.mem_union_left F
              (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, h1⟩)
          · exact Finset.mem_union_right small (hiff.mp hx.2))
        (fun x1 hx1 x2 hx2 heq => by
          have hi1 : i ∈ x1 := (Finset.mem_filter.mp hx1).2
          have hi2 : i ∈ x2 := (Finset.mem_filter.mp hx2).2
          rw [← Finset.insert_erase hi1, ← Finset.insert_erase hi2, heq])
        (fun y hy => by
          have hiy : i ∉ y := by
            rcases Finset.mem_union.mp hy with h1 | h2
            · have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp h1).1
              exact fun hi => (Finset.mem_erase.mp (hsub hi)).1 rfl
            · have hsub := (Finset.mem_powersetCard.mp (hFsub h2)).1
              exact fun hi => (Finset.mem_erase.mp (hsub hi)).1 rfl
          refine ⟨insert i y, ?_, Finset.erase_insert hiy⟩
          simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert_self,
            and_true, Finset.erase_insert hiy]
          rcases Finset.mem_union.mp hy with h1 | h2
          · exact Or.inl (Finset.mem_filter.mp h1).2
          · exact Or.inr ⟨(Finset.mem_powersetCard.mp (hFsub h2)).2,
              ⟨fun _ => h2, fun _ => True.intro⟩⟩)
    rw [hbij, Finset.card_union_of_disjoint hdisj_in, hsmall_card, hFcard]
  have hRout_card : (R.filter (fun x => i ∉ x)).card = n + shell.card / 2 := by
    have hbij : (R.filter (fun x => i ∉ x)).card = (small ∪ (shell \ F)).card := by
      refine Finset.card_bij (fun x _ => x)
        (fun x hx => by
          simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have her : x.erase i = x := Finset.erase_eq_of_notMem hx.2
          have hsub : x ⊆ old := fun a ha =>
            Finset.mem_erase.mpr ⟨fun h => hx.2 (h ▸ ha), Finset.mem_univ a⟩
          rw [her] at hx
          rcases hx.1 with h1 | ⟨h2, hiff⟩
          · exact Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, h1⟩)
          · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨?_, fun h => hx.2 (hiff.mpr h)⟩)
            exact Finset.mem_powersetCard.mpr ⟨hsub, h2⟩)
        (fun _ _ _ _ heq => heq)
        (fun y hy => by
          have hiy : i ∉ y := by
            rcases Finset.mem_union.mp hy with h1 | h2
            · have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp h1).1
              exact fun hi => (Finset.mem_erase.mp (hsub hi)).1 rfl
            · have hsub := (Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp h2).1).1
              exact fun hi => (Finset.mem_erase.mp (hsub hi)).1 rfl
          have her : y.erase i = y := Finset.erase_eq_of_notMem hiy
          refine ⟨y, ?_, rfl⟩
          simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, hiy, her]
          refine ⟨?_, by simp⟩
          rcases Finset.mem_union.mp hy with h1 | h2
          · exact Or.inl (Finset.mem_filter.mp h1).2
          · refine Or.inr ⟨(Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp h2).1).2, ?_⟩
            exact ⟨fun h => False.elim h, fun h => absurd h (Finset.mem_sdiff.mp h2).2⟩)
    have hcs := Finset.card_sdiff_add_card_inter shell F
    rw [Finset.inter_eq_right.mpr hFsub] at hcs
    rw [hbij, Finset.card_union_of_disjoint hdisj_out, hsmall_card]
    omega
  have hR_card : R.card = 1 + n + Nat.choose n 2 := by
    have hsplit := card_filter_add_card_filter_not R (fun x => i ∈ x)
    rw [hRin_card, hRout_card] at hsplit
    omega
  refine ⟨s, ?_, ?_⟩
  · rw [hreg_eq]; exact hR_card
  · rw [hreg_eq, hRin_card]; omega

theorem main (n : Nat) (hn : 3 ≤ n) :
    let Site := Fin n
    let Word := Finset Site
    let cube := (Finset.univ : Finset Word)
    let triples := (Finset.univ : Finset Site).powersetCard 3
    let region := fun (s : Word → Word) => cube.filter (fun x =>
      ∀ E ∈ triples, x ∩ E ≠ s E ∩ E)
    let ball := fun (x c : Word) => ((x \ c) ∪ (c \ x)).card ≤ 2
    let regular := fun (f : Word → Nat) => ∃ b : Nat, ∀ x : Word,
      (cube.filter (fun c => ball x c)).sum f = b
    let V := 1 + n + Nat.choose n 2
    (∀ i : Site, (∃ s : Word → Word, (region s).card = V ∧
      2 * ((region s).filter (fun x => i ∈ x)).card = V) ↔ Even V) ∧
    ((∃ f : Word → Nat, regular f ∧ ∃ x y : Word, f x ≠ f y) ↔
      ∃ m : Nat, m * m = n - 1) ∧
    ((∃ E : Word, E.Nonempty ∧ regular (fun c => if Even (E ∩ c).card then 1 else 0)) ↔
      ∃ m : Nat, m * m = n - 1) := by
  dsimp only
  have hsq_to_parity :
      (∃ m : Nat, m * m = n - 1) →
      ∃ E : Finset (Fin n), E.Nonempty ∧
        ∃ b : Nat, ∀ x : Finset (Fin n),
          ((Finset.univ : Finset (Finset (Fin n))).filter
            (fun c => ((x \ c) ∪ (c \ x)).card ≤ 2)).sum
              (fun c => if Even (E ∩ c).card then 1 else 0) = b := by
    rintro ⟨m, hm⟩
    have hm2 : 2 ≤ m := by
      by_contra hlt
      push Not at hlt
      have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;> omega
    have hm_eq : m * m + 1 = n := by omega
    have hmlt : m < n := by nlinarith
    have heven_diff : Even (n + 1 - m) := by
      rcases Nat.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · have hmul : (r + r) * (r + r) = 4 * (r * r) := by ring
        have hge : r ≤ 2 * (r * r) := by nlinarith
        refine ⟨2 * (r * r) - r + 1, ?_⟩
        omega
      · have hmul : (2 * r + 1) * (2 * r + 1) = 4 * (r * r) + 4 * r + 1 := by ring
        refine ⟨2 * (r * r) + r + 1, ?_⟩
        omega
    let w : Nat := (n + 1 - m) / 2
    have hw2 : 2 * w = n + 1 - m := by
      rcases heven_diff with ⟨r, hr⟩
      omega
    have hw_pos : 1 ≤ w := by omega
    have hw_le : w ≤ n := by omega
    let E : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < w)
    have hE_card : E.card = w := by
      have hbij : E.card = (Finset.univ : Finset (Fin w)).card := by
        refine Finset.card_bij
          (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin w))
          (fun _ _ => Finset.mem_univ _)
          (fun i1 _ i2 _ heq => Fin.ext (congrArg (Fin.val : Fin w → Nat) heq))
          (fun j _ => ⟨⟨j.val, lt_of_lt_of_le j.isLt hw_le⟩,
            by simp [E, j.isLt], Fin.ext rfl⟩)
      simpa using hbij
    have hE_ne : E.Nonempty := Finset.card_pos.mp (by omega)
    have hBHat0 :
        (∑ d ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun d => d.card ≤ 2),
          chi E d) = 0 := by
      have hform := sum_chi_ball E
      rw [hE_card] at hform
      have hdiff : ((n : Int) + 1 - 2 * (w : Int)) = (m : Int) := by omega
      have hsq : ((m : Int)) ^ 2 = ((n : Int) - 1) := by
        have h1 : (m : Int) * (m : Int) = ((n - 1 : Nat) : Int) := by
          exact_mod_cast hm
        have h2 : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
        linarith [sq (m : Int)]
      rw [hdiff, hsq] at hform
      omega
    let f : Finset (Fin n) → Nat := fun c => if Even (E ∩ c).card then 1 else 0
    have hval : ∀ x : Finset (Fin n),
        2 * ((((Finset.univ : Finset (Finset (Fin n))).filter
          (fun c => (sdiffU x c).card ≤ 2)).sum f : Nat) : Int) =
        (((Finset.univ : Finset (Finset (Fin n))).filter (fun d => d.card ≤ 2)).card : Int) := by
      intro x
      rw [Nat.cast_sum, Finset.mul_sum]
      have hrew := sum_ball_eq_sum_sdiffU x (fun c => 2 * (f c : Int))
      rw [hrew]
      have hterm : ∀ d : Finset (Fin n), 2 * (f (sdiffU x d) : Int) = 1 + chi E x * chi E d := by
        intro d
        dsimp only [f]
        rw [two_mul_even_ind]
        change 1 + chi E (sdiffU x d) = 1 + chi E x * chi E d
        rw [chi_mul_sdiffU]
      rw [Finset.sum_congr rfl (fun d _ => hterm d), Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum, hBHat0, mul_zero, add_zero]
    let b : Nat :=
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun c => (sdiffU ∅ c).card ≤ 2)).sum f
    refine ⟨E, hE_ne, b, fun x => ?_⟩
    have hx := hval x
    have h0 := hval ∅
    have heq : ((((Finset.univ : Finset (Finset (Fin n))).filter
        (fun c => (sdiffU x c).card ≤ 2)).sum f : Nat) : Int) = (b : Int) := by
      change ((((Finset.univ : Finset (Finset (Fin n))).filter
        (fun c => (sdiffU x c).card ≤ 2)).sum f : Nat) : Int) =
        ((((Finset.univ : Finset (Finset (Fin n))).filter
        (fun c => (sdiffU ∅ c).card ≤ 2)).sum f : Nat) : Int)
      linarith
    exact_mod_cast heq
  have hreg_to_sq :
      (∃ f : Finset (Fin n) → Nat,
        (∃ b : Nat, ∀ x : Finset (Fin n),
          ((Finset.univ : Finset (Finset (Fin n))).filter
            (fun c => ((x \ c) ∪ (c \ x)).card ≤ 2)).sum f = b) ∧
        ∃ x y : Finset (Fin n), f x ≠ f y) →
      ∃ m : Nat, m * m = n - 1 := by
    rintro ⟨f, ⟨b, hreg⟩, x0, y0, hne⟩
    by_contra hnosq
    let fHat : Finset (Fin n) → Int := fun E => ∑ c : Finset (Fin n), chi E c * (f c : Int)
    have hfHat0 : ∀ E : Finset (Fin n), E ≠ ∅ → fHat E = 0 := by
      intro E hEne
      have hconv :
          (∑ x : Finset (Fin n), chi E x *
            ((((Finset.univ : Finset (Finset (Fin n))).filter
              (fun c => (sdiffU x c).card ≤ 2)).sum f : Nat) : Int)) =
          (∑ d ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun d => d.card ≤ 2),
            chi E d) * fHat E := by
        have hstep1 : ∀ x : Finset (Fin n),
            chi E x *
              ((((Finset.univ : Finset (Finset (Fin n))).filter
                (fun c => (sdiffU x c).card ≤ 2)).sum f : Nat) : Int) =
            ∑ d ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun d => d.card ≤ 2),
              chi E x * (f (sdiffU x d) : Int) := by
          intro x
          rw [Nat.cast_sum, sum_ball_eq_sum_sdiffU x (fun c => (f c : Int)), Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun x _ => hstep1 x), Finset.sum_comm, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun x _ => sdiffU x d) (fun _ _ => Finset.mem_univ _)
          (fun x1 _ x2 _ heq => by
            have := congrArg (fun z => sdiffU z d) heq
            simpa [sdiffU_invol] using this)
          (fun c _ => ⟨sdiffU c d, Finset.mem_univ _, sdiffU_invol c d⟩)
          (fun x _ => by
            rw [chi_mul_sdiffU]
            have hsq : chi E d * chi E d = 1 := by
              simp only [chi, ← pow_add, ← two_mul, pow_mul]
              norm_num
            calc
              chi E x * (f (sdiffU x d) : Int)
                  = (chi E d * chi E d) * (chi E x * (f (sdiffU x d) : Int)) := by
                    rw [hsq, one_mul]
              _ = chi E d * (chi E x * chi E d * (f (sdiffU x d) : Int)) := by ring)
      have hlhs0 :
          (∑ x : Finset (Fin n), chi E x *
            ((((Finset.univ : Finset (Finset (Fin n))).filter
              (fun c => (sdiffU x c).card ≤ 2)).sum f : Nat) : Int)) = 0 := by
        have hconst : ∀ x : Finset (Fin n),
            chi E x *
              ((((Finset.univ : Finset (Finset (Fin n))).filter
                (fun c => (sdiffU x c).card ≤ 2)).sum f : Nat) : Int) = chi E x * (b : Int) := fun x => by
          have hfx : ((Finset.univ : Finset (Finset (Fin n))).filter
              (fun c => (sdiffU x c).card ≤ 2)).sum f = b := hreg x
          rw [hfx]
        rw [Finset.sum_congr rfl (fun x _ => hconst x), ← Finset.sum_mul,
          sum_chi_eq E, if_neg hEne, zero_mul]
      have hBHat_ne :
          (∑ d ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun d => d.card ≤ 2),
            chi E d) ≠ 0 := by
        intro hzero
        have hform := sum_chi_ball E
        rw [hzero, mul_zero] at hform
        let z : Int := (n : Int) + 1 - 2 * (E.card : Int)
        have hzsq : z * z = (n : Int) - 1 := by
          have : z ^ 2 = (n : Int) - 1 := by linarith
          linarith [sq z]
        have hnat : z.natAbs * z.natAbs = n - 1 := by
          have h1 : ((z.natAbs * z.natAbs : Nat) : Int) = z * z := by
            rw [Nat.cast_mul]
            rcases Int.natAbs_eq z with h | h <;> nlinarith
          have h2 : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
          exact_mod_cast (h1.trans (hzsq.trans h2.symm))
        exact hnosq ⟨z.natAbs, hnat⟩
      have hprod0 :
          (∑ d ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun d => d.card ≤ 2),
            chi E d) * fHat E = 0 := by
        linarith
      exact (mul_eq_zero.mp hprod0).resolve_left hBHat_ne
    have hinv : ∀ x : Finset (Fin n),
        (2 ^ n : Int) * (f x : Int) = fHat ∅ := by
      intro x
      have h1 : (∑ E : Finset (Fin n), chi E x * fHat E) = fHat ∅ := by
        rw [Finset.sum_eq_single ∅]
        · rw [chi_empty_left, one_mul]
        · intro E _ hEne
          rw [hfHat0 E hEne, mul_zero]
        · intro h; exact absurd (Finset.mem_univ ∅) h
      have h2 : (∑ E : Finset (Fin n), chi E x * fHat E) = (2 ^ n : Int) * (f x : Int) := by
        simp only [fHat, Finset.mul_sum]
        rw [Finset.sum_comm]
        have hinner : ∀ c : Finset (Fin n),
            (∑ E : Finset (Fin n), chi E x * (chi E c * (f c : Int))) =
            (if c = x then (2 ^ n : Int) else 0) * (f c : Int) := by
          intro c
          have hrew : ∀ E : Finset (Fin n),
              chi E x * (chi E c * (f c : Int)) = chi (sdiffU x c) E * (f c : Int) := fun E => by
            rw [← mul_assoc, ← chi_mul_sdiffU, chi_comm]
          rw [Finset.sum_congr rfl (fun E _ => hrew E), ← Finset.sum_mul, sum_chi_eq]
          have hiff : sdiffU x c = ∅ ↔ c = x := by
            rw [sdiffU_eq_empty_iff, eq_comm]
          by_cases hcx : c = x
          · rw [if_pos (hiff.mpr hcx), if_pos hcx]
          · rw [if_neg (fun h => hcx (hiff.mp h)), if_neg hcx]
        rw [Finset.sum_congr rfl (fun c _ => hinner c)]
        rw [Finset.sum_eq_single x]
        · simp
        · intro c _ hcx
          simp [hcx]
        · intro h; exact absurd (Finset.mem_univ x) h
      linarith
    have hx := hinv x0
    have hy := hinv y0
    have h2pos : (0 : Int) < (2 ^ n : Int) := by positivity
    have heq : (f x0 : Int) = (f y0 : Int) := mul_left_cancel₀ (ne_of_gt h2pos) (by linarith)
    exact hne (by exact_mod_cast heq)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    constructor
    · rintro ⟨s, hcard, hbal⟩
      exact ⟨((Finset.univ.filter (fun x =>
        ∀ E ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, x ∩ E ≠ s E ∩ E)).filter
        (fun x => i ∈ x)).card, by omega⟩
    · exact balanced_region_of_even n hn i
  · constructor
    · exact hreg_to_sq
    · intro hsq
      rcases hsq_to_parity hsq with ⟨E, hEne, hreg⟩
      rcases hEne with ⟨u, hu⟩
      refine ⟨fun c => if Even (E ∩ c).card then 1 else 0, hreg, ∅, {u}, ?_⟩
      have h0 : (E ∩ ∅).card = 0 := by simp
      have h1 : (E ∩ {u}).card = 1 := by
        have : E ∩ {u} = {u} := by ext a; simp [hu]
        simp [this]
      simp [h0, h1]
  · constructor
    · rintro ⟨E, hEne, hreg⟩
      apply hreg_to_sq
      rcases hEne with ⟨u, hu⟩
      refine ⟨fun c => if Even (E ∩ c).card then 1 else 0, hreg, ∅, {u}, ?_⟩
      have h0 : (E ∩ ∅).card = 0 := by simp
      have h1 : (E ∩ {u}).card = 1 := by
        have : E ∩ {u} = {u} := by ext a; simp [hu]
        simp [this]
      simp [h0, h1]
    · exact hsq_to_parity

end PEqualNP.Outside.L_lib_1183_aux

theorem PEqualNP.Outside.L_lib_1183 :
∀ (n : Nat), 3 ≤ n →
  let Site := Fin n
  let Word := Finset Site
  let cube := (Finset.univ : Finset Word)
  let triples := (Finset.univ : Finset Site).powersetCard 3
  let region := fun (s : Word → Word) => cube.filter (fun x =>
    ∀ E ∈ triples, x ∩ E ≠ s E ∩ E)
  let ball := fun (x c : Word) => ((x \ c) ∪ (c \ x)).card ≤ 2
  let regular := fun (f : Word → Nat) => ∃ b : Nat, ∀ x : Word,
    (cube.filter (fun c => ball x c)).sum f = b
  let V := 1 + n + Nat.choose n 2
  (∀ i : Site, (∃ s : Word → Word, (region s).card = V ∧
    2 * ((region s).filter (fun x => i ∈ x)).card = V) ↔ Even V) ∧
  ((∃ f : Word → Nat, regular f ∧ ∃ x y : Word, f x ≠ f y) ↔
    ∃ m : Nat, m * m = n - 1) ∧
  ((∃ E : Word, E.Nonempty ∧ regular (fun c => if Even (E ∩ c).card then 1 else 0)) ↔
    ∃ m : Nat, m * m = n - 1) := by
  intro n hn Site Word cube triples region ball regular V
  exact PEqualNP.Outside.L_lib_1183_aux.main n hn
