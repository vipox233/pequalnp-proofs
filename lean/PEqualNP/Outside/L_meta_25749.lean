import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_25749_aux

private def scopeOf (n k : Nat) (hn : 0 < n) (i : Fin n) : Finset (Fin n) :=
  (Finset.range k).image (fun t => (⟨(i.val + t) % n, Nat.mod_lt _ hn⟩ : Fin n))

private def fullOf (n k : Nat) (hn : 0 < n) : Finset (Fin n × Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n × Finset (Fin n))).filter (fun p => p.2 ⊆ scopeOf n k hn p.1)

private def totalOf (n k : Nat) (hn : 0 < n) (table : Finset (Fin n × Finset (Fin n))) : Nat :=
  ((Finset.univ : Finset (Finset (Fin n))).filter
    (fun x => ∀ i : Fin n, (i, x ∩ scopeOf n k hn i) ∈ table)).card

private def hitOf (n k : Nat) (hn : 0 < n) (p : Fin n × Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun x => x ∩ scopeOf n k hn p.1 = p.2)

private theorem mod_diff_eq {n a b : Nat} (ha : a < n) (hb : b < n) :
    (a + n - b) % n = if a < b then a + n - b else a - b := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · have h1 : a + n - b = n + (a - b) := by omega
    rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

private theorem scopeOf_card {n k : Nat} (hn : 0 < n) (hk : k ≤ n) (i : Fin n) :
    (scopeOf n k hn i).card = k := by
  unfold scopeOf
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro t1 ht1 t2 ht2 heq
  simp only [Finset.mem_coe, Finset.mem_range] at ht1 ht2
  have hval : (i.val + t1) % n = (i.val + t2) % n := congrArg Fin.val heq
  have hi : i.val < n := i.isLt
  have h1 : (i.val + t1) % n = if i.val + t1 < n then i.val + t1 else i.val + t1 - n := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have h2 : (i.val + t2) % n = if i.val + t2 < n then i.val + t2 else i.val + t2 - n := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2] at hval
  split_ifs at hval <;> omega

private theorem mem_scopeOf_iff {n k : Nat} (hn : 0 < n) (i j : Fin n) :
    j ∈ scopeOf n k hn i ↔ ∃ t < k, (i.val + t) % n = j.val := by
  unfold scopeOf
  simp only [Finset.mem_image, Finset.mem_range, Fin.ext_iff]

private theorem mem_scopeOf_dist_iff {n k : Nat} (hn : 0 < n) (hk : k ≤ n) (i j : Fin n) :
    j ∈ scopeOf n k hn i ↔ (j.val + n - i.val) % n < k := by
  rw [mem_scopeOf_iff]
  have hi := i.isLt
  have hj := j.isLt
  constructor
  · rintro ⟨t, ht, heq⟩
    have h1 : (j.val + n - i.val) % n = t := by
      have hmod : (i.val + t) % n = if i.val + t < n then i.val + t else i.val + t - n := by
        split_ifs with h
        · exact Nat.mod_eq_of_lt h
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hmod] at heq
      split_ifs at heq with h
      · have : j.val + n - i.val = n + t := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      · have : j.val + n - i.val = t := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro hlt
    refine ⟨(j.val + n - i.val) % n, hlt, ?_⟩
    have h1 : (j.val + n - i.val) % n = if j.val < i.val then j.val + n - i.val else j.val - i.val := mod_diff_eq hj hi
    rw [h1]
    split_ifs with h
    · have : i.val + (j.val + n - i.val) = n + j.val := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hj]
    · have : i.val + (j.val - i.val) = j.val := by omega
      rw [this, Nat.mod_eq_of_lt hj]

private theorem fullOf_card {n k : Nat} (hn : 0 < n) (hk : k ≤ n) :
    (fullOf n k hn).card = n * 2 ^ k := by
  unfold fullOf
  let emb : Fin n → Finset (Fin n) ↪ Fin n × Finset (Fin n) :=
    fun i => ⟨fun P => (i, P), fun _ _ h => (Prod.mk.inj h).2⟩
  have heq : (Finset.univ : Finset (Fin n × Finset (Fin n))).filter
      (fun p => p.2 ⊆ scopeOf n k hn p.1) =
      (Finset.univ : Finset (Fin n)).biUnion (fun i =>
        (scopeOf n k hn i).powerset.map (emb i)) := by
    ext ⟨i, P⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_map,
      Finset.mem_powerset]
    constructor
    · intro hP; exact ⟨i, P, hP, rfl⟩
    · rintro ⟨a, P', hP', heq⟩
      have h1 : a = i := (Prod.mk.inj heq).1
      have h2 : P' = P := (Prod.mk.inj heq).2
      subst h1; subst h2; exact hP'
  rw [heq, Finset.card_biUnion]
  · simp only [Finset.card_map, Finset.card_powerset, scopeOf_card hn hk, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  · intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hpi hpj
    simp only [emb, Finset.mem_map, Function.Embedding.coeFn_mk] at hpi hpj
    obtain ⟨_, _, rfl⟩ := hpi
    obtain ⟨_, _, heq2⟩ := hpj
    exact hij (Prod.mk.inj heq2).1.symm

private theorem fixed_inter_card {n : Nat} (S P : Finset (Fin n)) (hPS : P ⊆ S) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => x ∩ S = P)).card =
      2 ^ (n - S.card) := by
  have hbij : ((Finset.univ : Finset (Finset (Fin n))).filter (fun x => x ∩ S = P)).card =
      (Finset.univ \ S).powerset.card := by
    refine Finset.card_bij (fun x _ => x \ S) ?_ ?_ ?_
    · intro x _
      simp only [Finset.mem_powerset]
      intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
      exact ha.2
    · intro x1 hx1 x2 hx2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      ext a
      by_cases haS : a ∈ S
      · have h1 : a ∈ x1 ↔ a ∈ P := by rw [← hx1]; simp [haS]
        have h2 : a ∈ x2 ↔ a ∈ P := by rw [← hx2]; simp [haS]
        exact h1.trans h2.symm
      · have h1 : a ∈ x1 ↔ a ∈ x1 \ S := by simp [haS]
        have h2 : a ∈ x2 ↔ a ∈ x2 \ S := by simp [haS]
        rw [h1, h2, heq]
    · intro y hy
      simp only [Finset.mem_powerset] at hy
      refine ⟨P ∪ y, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        ext a
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨haP | hay, haS⟩
          · exact haP
          · exact False.elim ((Finset.mem_sdiff.mp (hy hay)).2 haS)
        · intro haP
          exact ⟨Or.inl haP, hPS haP⟩
      · ext a
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨haP | hay, hnaS⟩
          · exact False.elim (hnaS (hPS haP))
          · exact hay
        · intro hay
          exact ⟨Or.inr hay, (Finset.mem_sdiff.mp (hy hay)).2⟩
  rw [hbij, Finset.card_powerset, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, Fintype.card_fin]

private theorem hitOf_card {n k : Nat} (hn : 0 < n) (hk : k ≤ n)
    {p : Fin n × Finset (Fin n)} (hp : p ∈ fullOf n k hn) :
    (hitOf n k hn p).card = 2 ^ (n - k) := by
  simp only [fullOf, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  unfold hitOf
  rw [fixed_inter_card (scopeOf n k hn p.1) p.2 hp, scopeOf_card hn hk p.1]

private theorem hitOf_inter_card {n k : Nat} (hn : 0 < n)
    {a b : Fin n × Finset (Fin n)} (ha : a ∈ fullOf n k hn) (hb : b ∈ fullOf n k hn)
    (hne : (hitOf n k hn a ∩ hitOf n k hn b).Nonempty) :
    (hitOf n k hn a ∩ hitOf n k hn b).card =
      2 ^ (n - (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1).card) := by
  obtain ⟨x0, hx0⟩ := hne
  simp only [Finset.mem_inter, hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx0
  have hfilt : hitOf n k hn a ∩ hitOf n k hn b =
      (Finset.univ : Finset (Finset (Fin n))).filter
        (fun x => x ∩ (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1) =
          x0 ∩ (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1)) := by
    ext x
    simp only [Finset.mem_inter, hitOf, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left, hx0.1, hx0.2]
    constructor
    · rintro ⟨h1, h2⟩; rw [h1, h2]
    · intro heq
      have h1 : x ∩ scopeOf n k hn a.1 = a.2 := by
        ext r
        by_cases hr : r ∈ scopeOf n k hn a.1
        · have hmem := Finset.ext_iff.mp heq r
          simp only [Finset.mem_union, Finset.mem_inter, hr, and_true] at hmem
          have ha_sub : a.2 ⊆ scopeOf n k hn a.1 := by
            simp only [fullOf, Finset.mem_filter, Finset.mem_univ, true_and] at ha; exact ha
          constructor
          · intro hxr
            have := hmem.mp (Or.inl (Finset.mem_inter.mp hxr).1)
            rcases this with h | h
            · exact h
            · rw [← hx0.2] at h; rw [← hx0.1]; exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1, hr⟩
          · intro har
            have := hmem.mpr (Or.inl har)
            rcases this with h | ⟨h, _⟩
            · exact Finset.mem_inter.mpr ⟨h, hr⟩
            · exact Finset.mem_inter.mpr ⟨h, hr⟩
        · simp only [Finset.mem_inter, hr, and_false, false_iff]
          intro har
          simp only [fullOf, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact hr (ha har)
      have h2 : x ∩ scopeOf n k hn b.1 = b.2 := by
        ext r
        by_cases hr : r ∈ scopeOf n k hn b.1
        · have hmem := Finset.ext_iff.mp heq r
          simp only [Finset.mem_union, Finset.mem_inter, hr, and_true] at hmem
          constructor
          · intro hxr
            have := hmem.mp (Or.inr (Finset.mem_inter.mp hxr).1)
            rcases this with h | h
            · rw [← hx0.1] at h; rw [← hx0.2]; exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1, hr⟩
            · exact h
          · intro hbr
            have := hmem.mpr (Or.inr hbr)
            rcases this with ⟨h, _⟩ | h
            · exact Finset.mem_inter.mpr ⟨h, hr⟩
            · exact Finset.mem_inter.mpr ⟨h, hr⟩
        · simp only [Finset.mem_inter, hr, and_false, false_iff]
          intro hbr
          simp only [fullOf, Finset.mem_filter, Finset.mem_univ, true_and] at hb
          exact hr (hb hbr)
      exact ⟨h1, h2⟩
  rw [hfilt, fixed_inter_card _ _ Finset.inter_subset_right]

private theorem total_add_bad {n k : Nat} (hn : 0 < n)
    {D : Finset (Fin n × Finset (Fin n))} (hD : D ⊆ fullOf n k hn) :
    totalOf n k hn (fullOf n k hn \ D) + (D.biUnion (hitOf n k hn)).card = 2 ^ n := by
  unfold totalOf
  have hcompl : (Finset.univ : Finset (Finset (Fin n))).filter
      (fun x => ∀ i : Fin n, (i, x ∩ scopeOf n k hn i) ∈ fullOf n k hn \ D) =
      (Finset.univ : Finset (Finset (Fin n))) \ D.biUnion (hitOf n k hn) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_biUnion,
      hitOf, fullOf]
    constructor
    · intro h
      rintro ⟨⟨i, P⟩, hmemD, hxP⟩
      have hi := h i
      rw [hxP] at hi
      exact hi.2 hmemD
    · intro h i
      refine ⟨Finset.inter_subset_right, fun hmemD => ?_⟩
      exact h ⟨(i, x ∩ scopeOf n k hn i), hmemD, rfl⟩
  rw [hcompl]
  have hsub : D.biUnion (hitOf n k hn) ⊆ (Finset.univ : Finset (Finset (Fin n))) := Finset.subset_univ _
  rw [Finset.card_sdiff_add_card_eq_card hsub, Finset.card_univ, Fintype.card_finset,
    Fintype.card_fin]

private theorem total_add_bad_T {n k : Nat} (hn : 0 < n)
    {T : Finset (Fin n × Finset (Fin n))} (hT : T ⊆ fullOf n k hn) :
    totalOf n k hn T + ((fullOf n k hn \ T).biUnion (hitOf n k hn)).card = 2 ^ n := by
  have heq : fullOf n k hn \ (fullOf n k hn \ T) = T := Finset.sdiff_sdiff_eq_self hT
  have h := total_add_bad hn (D := fullOf n k hn \ T) Finset.sdiff_subset
  rwa [heq] at h

private theorem part1_off {n w : Nat} (hn : 0 < n) :
    let k := min n (w + 1)
    let N := 2 ^ n
    let u := 2 ^ (n - k)
    let off := fun t : Nat => sInf {c : Nat | ∃ D ∈ (fullOf n k hn).powerset,
      totalOf n k hn (fullOf n k hn \ D) < t ∧ D.card = c}
    ∀ t : Nat, 0 < t → t ≤ N → off t = (N - t + u) / u := by
  dsimp only
  set k := min n (w + 1)
  have hk : k ≤ n := min_le_left n (w + 1)
  set N := 2 ^ n
  set u := 2 ^ (n - k)
  have hu_pos : 0 < u := Nat.two_pow_pos (n - k)
  have hN_eq : N = 2 ^ k * u := by
    change 2 ^ n = 2 ^ k * 2 ^ (n - k)
    rw [← pow_add, Nat.add_sub_of_le hk]
  intro t ht0 htN
  set c := (N - t + u) / u
  have hc_ge : ∀ x ∈ {c' : Nat | ∃ D ∈ (fullOf n k hn).powerset,
      totalOf n k hn (fullOf n k hn \ D) < t ∧ D.card = c'}, c ≤ x := by
    rintro x ⟨D, hD, hlt, rfl⟩
    rw [Finset.mem_powerset] at hD
    have hsum := total_add_bad hn hD
    have hbad_le : (D.biUnion (hitOf n k hn)).card ≤ D.card * u := by
      calc (D.biUnion (hitOf n k hn)).card
          ≤ ∑ p ∈ D, (hitOf n k hn p).card := Finset.card_biUnion_le
        _ = ∑ _p ∈ D, u := Finset.sum_congr rfl fun p hp => hitOf_card hn hk (hD hp)
        _ = D.card * u := by simp
    have hlt2 : N - t < D.card * u := by omega
    have hdiv : (N - t + u) / u ≤ D.card := by
      have h1 : N - t + u ≤ D.card * u + (u - 1) := by omega
      have h2 : (N - t + u) / u ≤ (D.card * u + (u - 1)) / u := Nat.div_le_div_right h1
      have h3 : (D.card * u + (u - 1)) / u = D.card := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hu_pos, Nat.div_eq_of_lt (by omega), zero_add]
      omega
    exact hdiv
  have hc_mem : c ∈ {c' : Nat | ∃ D ∈ (fullOf n k hn).powerset,
      totalOf n k hn (fullOf n k hn \ D) < t ∧ D.card = c'} := by
    have hc_le : c ≤ 2 ^ k := by
      have h1 : N - t + u ≤ 2 ^ k * u + (u - 1) := by omega
      have h2 : (N - t + u) / u ≤ (2 ^ k * u + (u - 1)) / u := Nat.div_le_div_right h1
      have h3 : (2 ^ k * u + (u - 1)) / u = 2 ^ k := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hu_pos, Nat.div_eq_of_lt (by omega), zero_add]
      omega
    let i0 : Fin n := ⟨0, hn⟩
    have hcard_ps : (scopeOf n k hn i0).powerset.card = 2 ^ k := by
      rw [Finset.card_powerset, scopeOf_card hn hk i0]
    have hle_ps : c ≤ (scopeOf n k hn i0).powerset.card := by rw [hcard_ps]; exact hc_le
    obtain ⟨Ssub, hSsub, hScard⟩ := Finset.exists_subset_card_eq hle_ps
    let emb0 : Finset (Fin n) ↪ Fin n × Finset (Fin n) := ⟨fun P => (i0, P), fun _ _ h => (Prod.mk.inj h).2⟩
    let D : Finset (Fin n × Finset (Fin n)) := Ssub.map emb0
    have hD_sub : D ⊆ fullOf n k hn := by
      intro p hp
      simp only [D, emb0, Finset.mem_map, Function.Embedding.coeFn_mk] at hp
      obtain ⟨P, hP, rfl⟩ := hp
      simp only [fullOf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.mem_powerset.mp (hSsub hP)
    have hD_card : D.card = c := by simp only [D, Finset.card_map, hScard]
    have hdisj : (D : Set (Fin n × Finset (Fin n))).PairwiseDisjoint (hitOf n k hn) := by
      intro p1 hp1 p2 hp2 hne
      simp only [Finset.mem_coe, D, emb0, Finset.mem_map, Function.Embedding.coeFn_mk] at hp1 hp2
      obtain ⟨P1, _, rfl⟩ := hp1
      obtain ⟨P2, _, rfl⟩ := hp2
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      exact hne (Prod.ext rfl (hx1.symm.trans hx2))
    have hbad_eq : (D.biUnion (hitOf n k hn)).card = c * u := by
      rw [Finset.card_biUnion hdisj]
      calc ∑ p ∈ D, (hitOf n k hn p).card = ∑ _p ∈ D, u :=
            Finset.sum_congr rfl fun p hp => hitOf_card hn hk (hD_sub hp)
        _ = D.card * u := by simp
        _ = c * u := by rw [hD_card]
    have hsum := total_add_bad hn hD_sub
    have hcu : N - t < c * u := by
      have hmod : u * c + (N - t + u) % u = N - t + u := Nat.div_add_mod (N - t + u) u
      have hrem : (N - t + u) % u < u := Nat.mod_lt (N - t + u) hu_pos
      have hcomm : c * u = u * c := Nat.mul_comm c u
      omega
    refine ⟨D, Finset.mem_powerset.mpr hD_sub, by omega, hD_card⟩
  exact le_antisymm (Nat.sInf_le hc_mem) (le_csInf ⟨c, hc_mem⟩ hc_ge)

private theorem scopeOf_union_card_gt {n k : Nat} (hn : 0 < n) (hk0 : 0 < k) (hk : k < n)
    {i j : Fin n} (hij : i ≠ j) :
    k + 1 ≤ (scopeOf n k hn i ∪ scopeOf n k hn j).card := by
  have hk_le : k ≤ n := le_of_lt hk
  have hne : scopeOf n k hn i ≠ scopeOf n k hn j := by
    intro heq
    let pred : Fin n := ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩
    have hpred_not : pred ∉ scopeOf n k hn i := by
      rw [mem_scopeOf_dist_iff hn hk_le]
      have hi := i.isLt
      have hval : (pred.val + n - i.val) % n = n - 1 := by
        have hp : pred.val = if i.val = 0 then n - 1 else i.val - 1 := by
          dsimp only [pred]
          split_ifs with h0
          · rw [h0, zero_add, Nat.mod_eq_of_lt (by omega)]
          · have : i.val + n - 1 = n + (i.val - 1) := by omega
            rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [hp]
        split_ifs with h0
        · rw [h0, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · have : i.val - 1 + n - i.val = n - 1 := by omega
          rw [this, Nat.mod_eq_of_lt (by omega)]
      omega
    have hpred_in_or : i ∈ scopeOf n k hn j := by
      rw [← heq, mem_scopeOf_dist_iff hn hk_le]
      have h0 : (i.val + n - i.val) % n = 0 := by
        have : i.val + n - i.val = n := by omega
        rw [this, Nat.mod_self]
      omega
    have hpred_in : pred ∈ scopeOf n k hn j := by
      rw [mem_scopeOf_dist_iff hn hk_le] at hpred_in_or ⊢
      have hi := i.isLt
      have hj := j.isLt
      have hne_val : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have hd_pos : 0 < (i.val + n - j.val) % n := by
        have h1 : (i.val + n - j.val) % n = if i.val < j.val then i.val + n - j.val else i.val - j.val := mod_diff_eq hi hj
        rw [h1]; split_ifs <;> omega
      have hstep : (pred.val + n - j.val) % n = (i.val + n - j.val) % n - 1 := by
        have hp : pred.val = if i.val = 0 then n - 1 else i.val - 1 := by
          dsimp only [pred]
          split_ifs with h0
          · rw [h0, zero_add, Nat.mod_eq_of_lt (by omega)]
          · have : i.val + n - 1 = n + (i.val - 1) := by omega
            rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        have h1 : (i.val + n - j.val) % n = if i.val < j.val then i.val + n - j.val else i.val - j.val := mod_diff_eq hi hj
        have h2 : (pred.val + n - j.val) % n = if pred.val < j.val then pred.val + n - j.val else pred.val - j.val := mod_diff_eq pred.isLt hj
        rw [h1, h2, hp]
        split_ifs <;> omega
      omega
    rw [← heq] at hpred_in
    exact hpred_not hpred_in
  have hss : scopeOf n k hn i ⊂ scopeOf n k hn i ∪ scopeOf n k hn j := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_union_left, fun heq => hne ?_⟩
    have hsub : scopeOf n k hn j ⊆ scopeOf n k hn i := by
      rw [heq]; exact Finset.subset_union_right
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [scopeOf_card hn hk_le, scopeOf_card hn hk_le])).symm
  have hlt := Finset.card_lt_card hss
  rw [scopeOf_card hn hk_le i] at hlt
  omega

private theorem scopeOf_union_adj {n k : Nat} (hn : 0 < n) (hk0 : 0 < k) (hk : k < n) (i : Fin n) :
    let j : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩
    (scopeOf n k hn i ∪ scopeOf n k hn j).card = k + 1 := by
  dsimp only
  set j : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩
  have hk_le : k ≤ n := le_of_lt hk
  have h1 : scopeOf n k hn i ∪ scopeOf n k hn j = scopeOf n (k + 1) hn i := by
    ext r
    simp only [Finset.mem_union, mem_scopeOf_dist_iff hn hk_le, mem_scopeOf_dist_iff hn (by omega : k + 1 ≤ n)]
    have hi := i.isLt
    have hr := r.isLt
    have hj : j.val = if i.val + 1 < n then i.val + 1 else 0 := by
      dsimp only [j]
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · have : i.val + 1 = n := by omega
        rw [this, Nat.mod_self]
    have hri : (r.val + n - i.val) % n = if r.val < i.val then r.val + n - i.val else r.val - i.val := mod_diff_eq hr hi
    have hrj : (r.val + n - j.val) % n = if r.val < j.val then r.val + n - j.val else r.val - j.val := mod_diff_eq hr j.isLt
    rw [hri, hrj, hj]
    split_ifs <;> omega
  rw [h1, scopeOf_card hn (by omega : k + 1 ≤ n) i]

private theorem scopeOf_union_nonadj {n k : Nat} (hn : 0 < n) (hk2 : 2 ≤ k) (hkn2 : k + 2 ≤ n)
    {i j : Fin n} (hd1 : (j.val + n - i.val) % n ≠ 0)
    (hd2 : (j.val + n - i.val) % n ≠ 1) (hd3 : (j.val + n - i.val) % n ≠ n - 1) :
    k + 2 ≤ (scopeOf n k hn i ∪ scopeOf n k hn j).card := by
  have hk_le : k ≤ n := by omega
  set d := (j.val + n - i.val) % n
  have hd_lt : d < n := Nat.mod_lt _ hn
  have hd_range : 2 ≤ d ∧ d ≤ n - 2 := by omega
  have h1 : (scopeOf n k hn j \ scopeOf n k hn i).card ≥ 2 := by
    let p1 : Fin n := ⟨(i.val + (if d ≤ n - k then max d k else max d k)) % n, Nat.mod_lt _ hn⟩
    let s := max d k
    have hs_lo : k ≤ s := le_max_right d k
    have hs_hi : s + 1 < n := by omega
    let x1 : Fin n := ⟨(i.val + s) % n, Nat.mod_lt _ hn⟩
    let x2 : Fin n := ⟨(i.val + (s + 1)) % n, Nat.mod_lt _ hn⟩
    have hdist : ∀ t < n, ((⟨(i.val + t) % n, Nat.mod_lt _ hn⟩ : Fin n).val + n - i.val) % n = t := by
      intro t ht
      have hi := i.isLt
      have hmod : (i.val + t) % n = if i.val + t < n then i.val + t else i.val + t - n := by
        split_ifs with h
        · exact Nat.mod_eq_of_lt h
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      dsimp only
      rw [hmod]
      split_ifs with h
      · have : i.val + t + n - i.val = n + t := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt ht]
      · have : i.val + t - n + n - i.val = t := by omega
        rw [this, Nat.mod_eq_of_lt ht]
    have hdist_j : ∀ t < n,
        ((⟨(i.val + t) % n, Nat.mod_lt _ hn⟩ : Fin n).val + n - j.val) % n =
          if d ≤ t then t - d else t + n - d := by
      intro t ht
      have hi := i.isLt
      have hj := j.isLt
      have hd_eq : d = if j.val < i.val then j.val + n - i.val else j.val - i.val := mod_diff_eq hj hi
      have hmod : (i.val + t) % n = if i.val + t < n then i.val + t else i.val + t - n := by
        split_ifs with h
        · exact Nat.mod_eq_of_lt h
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      dsimp only
      have hval : ((i.val + t) % n + n - j.val) % n =
          if (i.val + t) % n < j.val then (i.val + t) % n + n - j.val else (i.val + t) % n - j.val := mod_diff_eq (Nat.mod_lt _ hn) hj
      rw [hval, hmod, hd_eq]
      split_ifs <;> omega
    have hx1_mem : x1 ∈ scopeOf n k hn j \ scopeOf n k hn i := by
      rw [Finset.mem_sdiff, mem_scopeOf_dist_iff hn hk_le, mem_scopeOf_dist_iff hn hk_le]
      rw [hdist s (by omega), hdist_j s (by omega), if_pos (le_max_left d k)]
      omega
    have hx2_mem : x2 ∈ scopeOf n k hn j \ scopeOf n k hn i := by
      rw [Finset.mem_sdiff, mem_scopeOf_dist_iff hn hk_le, mem_scopeOf_dist_iff hn hk_le]
      rw [hdist (s + 1) (by omega), hdist_j (s + 1) (by omega), if_pos (by omega)]
      omega
    have hne : x1 ≠ x2 := by
      intro heq
      have h := congrArg (fun r : Fin n => (r.val + n - i.val) % n) heq
      rw [hdist s (by omega), hdist (s + 1) (by omega)] at h
      omega
    have hsub : ({x1, x2} : Finset (Fin n)) ⊆ scopeOf n k hn j \ scopeOf n k hn i := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hx1_mem
      · exact hx2_mem
    calc 2 = ({x1, x2} : Finset (Fin n)).card := (Finset.card_pair hne).symm
      _ ≤ (scopeOf n k hn j \ scopeOf n k hn i).card := Finset.card_le_card hsub
  have hu : (scopeOf n k hn i ∪ scopeOf n k hn j).card =
      (scopeOf n k hn i).card + (scopeOf n k hn j \ scopeOf n k hn i).card := by
    rw [← Finset.card_union_of_disjoint Finset.sdiff_disjoint.symm, Finset.union_sdiff_self_eq_union]
  rw [hu, scopeOf_card hn hk_le i]
  omega

private theorem middle_scope_sub {n k : Nat} (hn : 0 < n) (hk2 : 2 ≤ k) (hkn : k < n) (i : Fin n) :
    let j : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩
    let l : Fin n := ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩
    scopeOf n k hn j ⊆ scopeOf n k hn i ∪ scopeOf n k hn l := by
  dsimp only
  intro r hr
  rw [mem_scopeOf_iff] at hr
  obtain ⟨t, ht, heq⟩ := hr
  rw [Finset.mem_union, mem_scopeOf_iff, mem_scopeOf_iff]
  by_cases htlast : t + 1 < k
  · left
    refine ⟨t + 1, htlast, ?_⟩
    rw [← heq]
    have h1 : (i.val + (t + 1)) % n = ((i.val + 1) + t) % n := by congr 1; omega
    have h2 : ((i.val + 1) % n + t) % n = ((i.val + 1) + t) % n := by simp [Nat.add_mod]
    rw [h1, h2]
  · right
    refine ⟨t - 1, by omega, ?_⟩
    rw [← heq]
    have h1 : (((i.val + 1) % n + 1) % n + (t - 1)) % n = ((i.val + 1) + 1 + (t - 1)) % n := by
      simp [Nat.add_mod]
    have h2 : ((i.val + 1) % n + t) % n = ((i.val + 1) + t) % n := by
      simp [Nat.add_mod]
    rw [h1, h2]
    congr 1; omega

private theorem pair_inter_le_half {n k : Nat} (hn : 0 < n) (hk0 : 0 < k) (hkn : k < n)
    {a b : Fin n × Finset (Fin n)} (ha : a ∈ fullOf n k hn) (hb : b ∈ fullOf n k hn)
    (hab : a ≠ b) :
    2 * (hitOf n k hn a ∩ hitOf n k hn b).card ≤ 2 ^ (n - k) := by
  by_cases hne : (hitOf n k hn a ∩ hitOf n k hn b).Nonempty
  · have hij : a.1 ≠ b.1 := by
      intro heq
      obtain ⟨x, hx⟩ := hne
      simp only [Finset.mem_inter, hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      apply hab
      refine Prod.ext heq ?_
      rw [← hx.1, ← hx.2, heq]
    rw [hitOf_inter_card hn ha hb hne]
    have hgt := scopeOf_union_card_gt hn (by omega) hkn hij
    have hle : n - (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1).card + 1 ≤ n - k := by omega
    calc 2 * 2 ^ (n - (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1).card)
        = 2 ^ (n - (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1).card + 1) := by ring
      _ ≤ 2 ^ (n - k) := Nat.pow_le_pow_right (by omega) hle
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty, mul_zero]
    exact Nat.zero_le _

private theorem pair_inter_le_quarter {n k : Nat} (hn : 0 < n) (hk2 : 2 ≤ k) (hkn2 : k + 2 ≤ n)
    {a b : Fin n × Finset (Fin n)} (ha : a ∈ fullOf n k hn) (hb : b ∈ fullOf n k hn)
    (hd1 : (b.1.val + n - a.1.val) % n ≠ 0)
    (hd2 : (b.1.val + n - a.1.val) % n ≠ 1) (hd3 : (b.1.val + n - a.1.val) % n ≠ n - 1) :
    4 * (hitOf n k hn a ∩ hitOf n k hn b).card ≤ 2 ^ (n - k) := by
  by_cases hne : (hitOf n k hn a ∩ hitOf n k hn b).Nonempty
  · rw [hitOf_inter_card hn ha hb hne]
    have hgt := scopeOf_union_nonadj hn hk2 hkn2 hd1 hd2 hd3
    have hle : n - (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1).card + 2 ≤ n - k := by omega
    calc 4 * 2 ^ (n - (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1).card)
        = 2 ^ (n - (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1).card + 2) := by ring
      _ ≤ 2 ^ (n - k) := Nat.pow_le_pow_right (by omega) hle
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty, mul_zero]
    exact Nat.zero_le _

private theorem card_union3_eq {α : Type*} [DecidableEq α] (A B C : Finset α) :
    (A ∪ B ∪ C).card + (A ∩ B).card + (A ∩ C).card + (B ∩ C).card =
      A.card + B.card + C.card + (A ∩ B ∩ C).card := by
  have h1 := Finset.card_union_add_card_inter (A ∪ B) C
  have h2 := Finset.card_union_add_card_inter A B
  have hdist : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := Finset.union_inter_distrib_right A B C
  have h3 := Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  have hint : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by ext x; simp only [Finset.mem_inter]; tauto
  rw [hdist] at h1
  rw [hint] at h3
  omega

private theorem three_holes_ge_two_u {n k : Nat} (hn : 0 < n) (hk2 : 2 ≤ k) (hkn : k < n)
    {a b c : Fin n × Finset (Fin n)} (ha : a ∈ fullOf n k hn) (hb : b ∈ fullOf n k hn)
    (hc : c ∈ fullOf n k hn) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    2 * 2 ^ (n - k) ≤ (hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c).card := by
  set u := 2 ^ (n - k)
  have hk_le : k ≤ n := le_of_lt hkn
  have hca : (hitOf n k hn a).card = u := hitOf_card hn hk_le ha
  have hcb : (hitOf n k hn b).card = u := hitOf_card hn hk_le hb
  have hcc : (hitOf n k hn c).card = u := hitOf_card hn hk_le hc

  by_cases hAB : (hitOf n k hn a ∩ hitOf n k hn b).Nonempty
  · by_cases hAC : (hitOf n k hn a ∩ hitOf n k hn c).Nonempty
    · by_cases hBC : (hitOf n k hn b ∩ hitOf n k hn c).Nonempty
      ·
        have hij : a.1 ≠ b.1 := by
          intro h; obtain ⟨x, hx⟩ := hAB
          simp only [Finset.mem_inter, hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact hab (Prod.ext h (by rw [← hx.1, ← hx.2, h]))
        have hil : a.1 ≠ c.1 := by
          intro h; obtain ⟨x, hx⟩ := hAC
          simp only [Finset.mem_inter, hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact hac (Prod.ext h (by rw [← hx.1, ← hx.2, h]))
        have hjl : b.1 ≠ c.1 := by
          intro h; obtain ⟨x, hx⟩ := hBC
          simp only [Finset.mem_inter, hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact hbc (Prod.ext h (by rw [← hx.1, ← hx.2, h]))
        by_cases hk_top : k + 1 = n
        ·
          have hu2 : u = 2 := by
            change 2 ^ (n - k) = 2
            have : n - k = 1 := by omega
            rw [this]; rfl
          have hAB1 : (hitOf n k hn a ∩ hitOf n k hn b).card = 1 := by
            rw [hitOf_inter_card hn ha hb hAB]
            have hgt := scopeOf_union_card_gt hn (by omega) hkn hij
            have hle : (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1).card ≤ n := by
              calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
                _ = n := Fintype.card_fin n
            have : n - (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1).card = 0 := by omega
            rw [this]; rfl
          have hAB3 : (hitOf n k hn a ∪ hitOf n k hn b).card = 3 := by
            have := Finset.card_union_add_card_inter (hitOf n k hn a) (hitOf n k hn b)
            omega

          let m : Fin n := ⟨(c.1.val + n - 1) % n, Nat.mod_lt _ hn⟩
          have hm_not_c : m ∉ scopeOf n k hn c.1 := by
            rw [mem_scopeOf_dist_iff hn hk_le]
            have hc1 := c.1.isLt
            have hm : m.val = if c.1.val = 0 then n - 1 else c.1.val - 1 := by
              dsimp only [m]
              split_ifs with h0
              · rw [h0, zero_add, Nat.mod_eq_of_lt (by omega)]
              · have : c.1.val + n - 1 = n + (c.1.val - 1) := by omega
                rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            have hval : (m.val + n - c.1.val) % n = n - 1 := by
              rw [hm]; split_ifs with h0
              · rw [h0, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              · have : c.1.val - 1 + n - c.1.val = n - 1 := by omega
                rw [this, Nat.mod_eq_of_lt (by omega)]
            omega
          have hm_in : ∀ i : Fin n, i ≠ c.1 → m ∈ scopeOf n k hn i := by
            intro i hic
            rw [mem_scopeOf_dist_iff hn hk_le]
            have hc1 := c.1.isLt
            have hi := i.isLt
            have hne_val : i.val ≠ c.1.val := fun h => hic (Fin.ext h)
            have hm : m.val = if c.1.val = 0 then n - 1 else c.1.val - 1 := by
              dsimp only [m]
              split_ifs with h0
              · rw [h0, zero_add, Nat.mod_eq_of_lt (by omega)]
              · have : c.1.val + n - 1 = n + (c.1.val - 1) := by omega
                rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
            have hval : (m.val + n - i.val) % n = if m.val < i.val then m.val + n - i.val else m.val - i.val := mod_diff_eq m.isLt hi
            rw [hval, hm]; split_ifs <;> omega
          have hm_a : m ∈ scopeOf n k hn a.1 := hm_in a.1 hil
          have hm_b : m ∈ scopeOf n k hn b.1 := hm_in b.1 hjl
          obtain ⟨x0, hx0⟩ := hAB
          simp only [Finset.mem_inter, hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx0
          have hc_sub : c.2 ⊆ scopeOf n k hn c.1 := by
            simp only [fullOf, Finset.mem_filter, Finset.mem_univ, true_and] at hc; exact hc
          have hmem_c1 : c.2 ∈ hitOf n k hn c := by
            simp only [hitOf, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Finset.inter_eq_left.mpr hc_sub
          have hmem_c2 : insert m c.2 ∈ hitOf n k hn c := by
            simp only [hitOf, Finset.mem_filter, Finset.mem_univ, true_and]
            ext r
            simp only [Finset.mem_inter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hrc, hrs⟩
              · exact False.elim (hm_not_c hrs)
              · exact hrc
            · intro hrc; exact ⟨Or.inr hrc, hc_sub hrc⟩
          have hex_out : ∃ y ∈ hitOf n k hn c, y ∉ hitOf n k hn a ∪ hitOf n k hn b := by
            have hsame : ∀ y ∈ hitOf n k hn a ∪ hitOf n k hn b, (m ∈ y ↔ m ∈ x0) := by
              intro y hy
              simp only [Finset.mem_union, hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hy
              rcases hy with hya | hyb
              · have h1 := Finset.ext_iff.mp (hya.trans hx0.1.symm) m
                simpa [hm_a] using h1
              · have h1 := Finset.ext_iff.mp (hyb.trans hx0.2.symm) m
                simpa [hm_b] using h1
            by_cases hmx0 : m ∈ x0
            · refine ⟨c.2, hmem_c1, fun h => ?_⟩
              have := (hsame c.2 h).mpr hmx0
              exact hm_not_c (hc_sub this)
            · refine ⟨insert m c.2, hmem_c2, fun h => ?_⟩
              have := (hsame (insert m c.2) h).mp (Finset.mem_insert_self m c.2)
              exact hmx0 this
          obtain ⟨y, hyc, hyout⟩ := hex_out
          have hss : hitOf n k hn a ∪ hitOf n k hn b ⊂ hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨Finset.subset_union_left, fun heq => hyout ?_⟩
            rw [heq]; exact Finset.mem_union_right _ hyc
          have hlt := Finset.card_lt_card hss
          omega
        ·
          have hkn2 : k + 2 ≤ n := by omega

          have hmid_case : ∀ p1 p2 p3 : Fin n × Finset (Fin n),
              p1 ∈ fullOf n k hn → p2 ∈ fullOf n k hn → p3 ∈ fullOf n k hn →
              p1 ≠ p2 → p2 ≠ p3 →
              (hitOf n k hn p1 ∩ hitOf n k hn p2).Nonempty →
              (hitOf n k hn p2 ∩ hitOf n k hn p3).Nonempty →
              scopeOf n k hn p2.1 ⊆ scopeOf n k hn p1.1 ∪ scopeOf n k hn p3.1 →
              2 * u ≤ (hitOf n k hn p1 ∪ hitOf n k hn p2 ∪ hitOf n k hn p3).card := by
            intro p1 p2 p3 hp1 hp2 hp3 h12 h23 hne12 hne23 hsub_sc
            obtain ⟨x12, hx12⟩ := hne12
            obtain ⟨x23, hx23⟩ := hne23
            simp only [Finset.mem_inter, hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx12 hx23
            have hint_sub : hitOf n k hn p1 ∩ hitOf n k hn p3 ⊆ hitOf n k hn p2 := by
              intro x hx
              simp only [Finset.mem_inter, hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              ext r
              by_cases hr2 : r ∈ scopeOf n k hn p2.1
              · simp only [Finset.mem_inter, hr2, and_true]
                rcases Finset.mem_union.mp (hsub_sc hr2) with hr1 | hr3
                · have h1 := Finset.ext_iff.mp (hx.1.trans hx12.1.symm) r
                  have h2 := Finset.ext_iff.mp hx12.2 r
                  simp only [Finset.mem_inter, hr1, hr2, and_true] at h1 h2
                  exact h1.trans h2
                · have h1 := Finset.ext_iff.mp (hx.2.trans hx23.2.symm) r
                  have h2 := Finset.ext_iff.mp hx23.1 r
                  simp only [Finset.mem_inter, hr3, hr2, and_true] at h1 h2
                  exact h1.trans h2
              · simp only [Finset.mem_inter, hr2, and_false, false_iff]
                intro hrp
                simp only [fullOf, Finset.mem_filter, Finset.mem_univ, true_and] at hp2
                exact hr2 (hp2 hrp)
            have h3eq : hitOf n k hn p1 ∩ hitOf n k hn p2 ∩ hitOf n k hn p3 =
                hitOf n k hn p1 ∩ hitOf n k hn p3 := by
              ext x
              simp only [Finset.mem_inter]
              exact ⟨fun ⟨⟨h1, _⟩, h3⟩ => ⟨h1, h3⟩,
                fun ⟨h1, h3⟩ => ⟨⟨h1, hint_sub (Finset.mem_inter.mpr ⟨h1, h3⟩)⟩, h3⟩⟩
            have hie := card_union3_eq (hitOf n k hn p1) (hitOf n k hn p2) (hitOf n k hn p3)
            rw [h3eq, hitOf_card hn hk_le hp1, hitOf_card hn hk_le hp2, hitOf_card hn hk_le hp3] at hie
            have hp12 := pair_inter_le_half hn (by omega) hkn hp1 hp2 h12
            have hp23 := pair_inter_le_half hn (by omega) hkn hp2 hp3 h23
            omega

          let adj := fun (x y : Fin n) =>
            (y.val + n - x.val) % n = 1 ∨ (y.val + n - x.val) % n = n - 1
          have hdist_ne0 : ∀ {x y : Fin n}, x ≠ y → (y.val + n - x.val) % n ≠ 0 := by
            intro x y hxy
            have hx := x.isLt; have hy := y.isLt
            have hne_val : x.val ≠ y.val := fun h => hxy (Fin.ext h)
            have h1 : (y.val + n - x.val) % n = if y.val < x.val then y.val + n - x.val else y.val - x.val := mod_diff_eq hy hx
            rw [h1]; split_ifs <;> omega
          have hsucc_eq : ∀ {x y : Fin n}, (y.val + n - x.val) % n = 1 →
              y = ⟨(x.val + 1) % n, Nat.mod_lt _ hn⟩ := by
            intro x y h1
            have hx := x.isLt; have hy := y.isLt
            have h2 : (y.val + n - x.val) % n = if y.val < x.val then y.val + n - x.val else y.val - x.val := mod_diff_eq hy hx
            have h3 : (x.val + 1) % n = if x.val + 1 < n then x.val + 1 else 0 := by
              split_ifs with h
              · exact Nat.mod_eq_of_lt h
              · have : x.val + 1 = n := by omega
                rw [this, Nat.mod_self]
            apply Fin.ext; dsimp only; rw [h3]; rw [h2] at h1
            split_ifs at h1 ⊢ <;> omega
          have hpred_eq : ∀ {x y : Fin n}, (y.val + n - x.val) % n = n - 1 →
              x = ⟨(y.val + 1) % n, Nat.mod_lt _ hn⟩ := by
            intro x y h1
            have hx := x.isLt; have hy := y.isLt
            have h2 : (y.val + n - x.val) % n = if y.val < x.val then y.val + n - x.val else y.val - x.val := mod_diff_eq hy hx
            have h3 : (y.val + 1) % n = if y.val + 1 < n then y.val + 1 else 0 := by
              split_ifs with h
              · exact Nat.mod_eq_of_lt h
              · have : y.val + 1 = n := by omega
                rw [this, Nat.mod_self]
            apply Fin.ext; dsimp only; rw [h3]; rw [h2] at h1
            split_ifs at h1 ⊢ <;> omega
          have hperm_ab : hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c =
              hitOf n k hn b ∪ hitOf n k hn a ∪ hitOf n k hn c := by ext x; simp; tauto
          have hperm_ac : hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c =
              hitOf n k hn a ∪ hitOf n k hn c ∪ hitOf n k hn b := by ext x; simp; tauto
          by_cases h1 : adj a.1 b.1
          · by_cases h2 : adj b.1 c.1
            ·
              rcases h1 with h1f | h1b <;> rcases h2 with h2f | h2b
              · have hb_eq := hsucc_eq h1f
                have hc_eq := hsucc_eq h2f
                have hsc : scopeOf n k hn b.1 ⊆ scopeOf n k hn a.1 ∪ scopeOf n k hn c.1 := by
                  rw [hb_eq, hc_eq, hb_eq]; exact middle_scope_sub hn hk2 hkn a.1
                exact hmid_case a b c ha hb hc hab hbc hAB hBC hsc
              · exact False.elim (hil ((hsucc_eq h1f).symm.trans (hpred_eq h2b) |> fun heq => by
                  have := congrArg Fin.val heq
                  have ha1 := a.1.isLt; have hc1 := c.1.isLt
                  have hfa : (a.1.val + 1) % n = if a.1.val + 1 < n then a.1.val + 1 else 0 := by
                    split_ifs with h
                    · exact Nat.mod_eq_of_lt h
                    · have : a.1.val + 1 = n := by omega
                      rw [this, Nat.mod_self]
                  have hfc : (c.1.val + 1) % n = if c.1.val + 1 < n then c.1.val + 1 else 0 := by
                    split_ifs with h
                    · exact Nat.mod_eq_of_lt h
                    · have : c.1.val + 1 = n := by omega
                      rw [this, Nat.mod_self]
                  dsimp only at this; rw [hfa, hfc] at this
                  apply Fin.ext; split_ifs at this <;> omega))
              · exact False.elim (hil ((hpred_eq h1b).trans (hsucc_eq h2f).symm))
              · have ha_eq := hpred_eq h1b
                have hb_eq := hpred_eq h2b
                have hsc : scopeOf n k hn b.1 ⊆ scopeOf n k hn c.1 ∪ scopeOf n k hn a.1 := by
                  rw [hb_eq, ha_eq, hb_eq]; exact middle_scope_sub hn hk2 hkn c.1
                have hsc' : scopeOf n k hn b.1 ⊆ scopeOf n k hn a.1 ∪ scopeOf n k hn c.1 := by
                  rw [Finset.union_comm]; exact hsc
                exact hmid_case a b c ha hb hc hab hbc hAB hBC hsc'
            · by_cases h3 : adj a.1 c.1
              ·
                rcases h1 with h1f | h1b <;> rcases h3 with h3f | h3b
                · exact False.elim (hjl ((hsucc_eq h1f).trans (hsucc_eq h3f).symm))
                · have ha_eq := hpred_eq h3b
                  have hb_eq := hsucc_eq h1f
                  have hsc : scopeOf n k hn a.1 ⊆ scopeOf n k hn c.1 ∪ scopeOf n k hn b.1 := by
                    rw [ha_eq, hb_eq, ha_eq]; exact middle_scope_sub hn hk2 hkn c.1
                  have hsc' : scopeOf n k hn a.1 ⊆ scopeOf n k hn b.1 ∪ scopeOf n k hn c.1 := by
                    rw [Finset.union_comm]; exact hsc
                  rw [hperm_ab]
                  exact hmid_case b a c hb ha hc hab.symm hac (by rwa [Finset.inter_comm]) hAC hsc'
                · have ha_eq := hpred_eq h1b
                  have hc_eq := hsucc_eq h3f
                  have hsc : scopeOf n k hn a.1 ⊆ scopeOf n k hn b.1 ∪ scopeOf n k hn c.1 := by
                    rw [ha_eq, hc_eq, ha_eq]; exact middle_scope_sub hn hk2 hkn b.1
                  rw [hperm_ab]
                  exact hmid_case b a c hb ha hc hab.symm hac (by rwa [Finset.inter_comm]) hAC hsc
                · exact False.elim (hjl (by
                    have heq := (hpred_eq h1b).symm.trans (hpred_eq h3b)
                    have := congrArg Fin.val heq
                    have hb1 := b.1.isLt; have hc1 := c.1.isLt
                    have hfb : (b.1.val + 1) % n = if b.1.val + 1 < n then b.1.val + 1 else 0 := by
                      split_ifs with h
                      · exact Nat.mod_eq_of_lt h
                      · have : b.1.val + 1 = n := by omega
                        rw [this, Nat.mod_self]
                    have hfc : (c.1.val + 1) % n = if c.1.val + 1 < n then c.1.val + 1 else 0 := by
                      split_ifs with h
                      · exact Nat.mod_eq_of_lt h
                      · have : c.1.val + 1 = n := by omega
                        rw [this, Nat.mod_self]
                    dsimp only at this; rw [hfb, hfc] at this
                    apply Fin.ext; split_ifs at this <;> omega))
              ·
                have h2' := not_or.mp h2
                have h3' := not_or.mp h3
                have hp12 := pair_inter_le_half hn (by omega) hkn ha hb hab
                have hp23 := pair_inter_le_quarter hn hk2 hkn2 hb hc (hdist_ne0 hjl) h2'.1 h2'.2
                have hp13 := pair_inter_le_quarter hn hk2 hkn2 ha hc (hdist_ne0 hil) h3'.1 h3'.2
                have hie := card_union3_eq (hitOf n k hn a) (hitOf n k hn b) (hitOf n k hn c)
                rw [hca, hcb, hcc] at hie
                omega
          · by_cases h2 : adj b.1 c.1
            · by_cases h3 : adj a.1 c.1
              ·
                rcases h2 with h2f | h2b <;> rcases h3 with h3f | h3b
                · exact False.elim (hij (by
                    have heq := (hsucc_eq h3f).symm.trans (hsucc_eq h2f)
                    have := congrArg Fin.val heq
                    have ha1 := a.1.isLt; have hb1 := b.1.isLt
                    have hfa : (a.1.val + 1) % n = if a.1.val + 1 < n then a.1.val + 1 else 0 := by
                      split_ifs with h
                      · exact Nat.mod_eq_of_lt h
                      · have : a.1.val + 1 = n := by omega
                        rw [this, Nat.mod_self]
                    have hfb : (b.1.val + 1) % n = if b.1.val + 1 < n then b.1.val + 1 else 0 := by
                      split_ifs with h
                      · exact Nat.mod_eq_of_lt h
                      · have : b.1.val + 1 = n := by omega
                        rw [this, Nat.mod_self]
                    dsimp only at this; rw [hfa, hfb] at this
                    apply Fin.ext; split_ifs at this <;> omega))
                · have hc_eq := hsucc_eq h2f
                  have ha_eq := hpred_eq h3b
                  have hsc : scopeOf n k hn c.1 ⊆ scopeOf n k hn b.1 ∪ scopeOf n k hn a.1 := by
                    rw [hc_eq, ha_eq, hc_eq]; exact middle_scope_sub hn hk2 hkn b.1
                  have hsc' : scopeOf n k hn c.1 ⊆ scopeOf n k hn a.1 ∪ scopeOf n k hn b.1 := by
                    rw [Finset.union_comm]; exact hsc
                  rw [hperm_ac]
                  exact hmid_case a c b ha hc hb hac hbc.symm hAC (by rwa [Finset.inter_comm]) hsc'
                · have hc_eq := hsucc_eq h3f
                  have hb_eq := hpred_eq h2b
                  have hsc : scopeOf n k hn c.1 ⊆ scopeOf n k hn a.1 ∪ scopeOf n k hn b.1 := by
                    rw [hc_eq, hb_eq, hc_eq]; exact middle_scope_sub hn hk2 hkn a.1
                  rw [hperm_ac]
                  exact hmid_case a c b ha hc hb hac hbc.symm hAC (by rwa [Finset.inter_comm]) hsc
                · exact False.elim (hij ((hpred_eq h3b).trans (hpred_eq h2b).symm))
              ·
                have h1' := not_or.mp h1
                have h3' := not_or.mp h3
                have hp23 := pair_inter_le_half hn (by omega) hkn hb hc hbc
                have hp12 := pair_inter_le_quarter hn hk2 hkn2 ha hb (hdist_ne0 hij) h1'.1 h1'.2
                have hp13 := pair_inter_le_quarter hn hk2 hkn2 ha hc (hdist_ne0 hil) h3'.1 h3'.2
                have hie := card_union3_eq (hitOf n k hn a) (hitOf n k hn b) (hitOf n k hn c)
                rw [hca, hcb, hcc] at hie
                omega
            ·
              have h1' := not_or.mp h1
              have h2' := not_or.mp h2
              have hp13 := pair_inter_le_half hn (by omega) hkn ha hc hac
              have hp12 := pair_inter_le_quarter hn hk2 hkn2 ha hb (hdist_ne0 hij) h1'.1 h1'.2
              have hp23 := pair_inter_le_quarter hn hk2 hkn2 hb hc (hdist_ne0 hjl) h2'.1 h2'.2
              have hie := card_union3_eq (hitOf n k hn a) (hitOf n k hn b) (hitOf n k hn c)
              rw [hca, hcb, hcc] at hie
              omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hBC
        have hdisj : Disjoint (hitOf n k hn b) (hitOf n k hn c) := Finset.disjoint_iff_inter_eq_empty.mpr hBC
        have hsub : hitOf n k hn b ∪ hitOf n k hn c ⊆ hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c := by
          intro x hx; simp only [Finset.mem_union] at hx ⊢; tauto
        calc 2 * u = (hitOf n k hn b).card + (hitOf n k hn c).card := by omega
          _ = (hitOf n k hn b ∪ hitOf n k hn c).card := (Finset.card_union_of_disjoint hdisj).symm
          _ ≤ (hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c).card := Finset.card_le_card hsub
    · rw [Finset.not_nonempty_iff_eq_empty] at hAC
      have hdisj : Disjoint (hitOf n k hn a) (hitOf n k hn c) := Finset.disjoint_iff_inter_eq_empty.mpr hAC
      have hsub : hitOf n k hn a ∪ hitOf n k hn c ⊆ hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c := by
        intro x hx; simp only [Finset.mem_union] at hx ⊢; tauto
      calc 2 * u = (hitOf n k hn a).card + (hitOf n k hn c).card := by omega
        _ = (hitOf n k hn a ∪ hitOf n k hn c).card := (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ (hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c).card := Finset.card_le_card hsub
  · rw [Finset.not_nonempty_iff_eq_empty] at hAB
    have hdisj : Disjoint (hitOf n k hn a) (hitOf n k hn b) := Finset.disjoint_iff_inter_eq_empty.mpr hAB
    have hsub : hitOf n k hn a ∪ hitOf n k hn b ⊆ hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c :=
      Finset.subset_union_left
    calc 2 * u = (hitOf n k hn a).card + (hitOf n k hn b).card := by omega
      _ = (hitOf n k hn a ∪ hitOf n k hn b).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c).card := Finset.card_le_card hsub

private theorem solve_25749 :
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
      let price := fun t : Nat => sInf {c : Nat | ∃ A ∈ full.powerset,
        t ≤ total A ∧ A.card = c}
      let N := 2^n
      let E := n*2^k
      let u := 2^(n-k)
      let off := fun t : Nat => sInf {c : Nat | ∃ D ∈ full.powerset,
        total (full \ D) < t ∧ D.card = c}
      (∀ t : Nat, 0 < t → t ≤ N → off t = (N-t+u)/u) ∧
      (2 ≤ k → k < n →
        (∀ b : Nat, b < 2*u →
          price (N-b) = E - (if b < u then 0 else if 2*b < 3*u then 1 else 2)) ∧
        ∀ T ∈ full.powerset, N-total T < 2*u →
          let omitted := full \ T
          omitted.card ≤ 2 ∧
          ∀ a ∈ omitted, ∀ b ∈ omitted, a ≠ b →
            (∃ x : Finset Site, x ∩ scope a.1 = a.2 ∧ x ∩ scope b.1 = b.2) ∧
            (N-total T) + 2^(n-(scope a.1 ∪ scope b.1).card) = 2*u) := by
  intro n w hn
  refine ⟨part1_off hn, ?_⟩
  intro hk2 hkn
  dsimp only
  set k := min n (w + 1)
  have hk_le : k ≤ n := le_of_lt hkn
  set N := 2 ^ n
  set E := n * 2 ^ k
  set u := 2 ^ (n - k)
  have hE_card : (fullOf n k hn).card = E := fullOf_card hn hk_le
  have hE_ge2 : 2 ≤ E := by
    have h1 : 1 ≤ n := hn
    have h2 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk2
    calc 2 ≤ 1 * 4 := by norm_num
      _ ≤ n * 2 ^ k := Nat.mul_le_mul h1 h2
  have hu_even : ∃ u2, u = 2 * u2 := by
    have hpos : 0 < n - k := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    refine ⟨2 ^ m, ?_⟩
    change 2 ^ (n - k) = 2 * 2 ^ m
    rw [hm, pow_succ']
  have hstruct : ∀ T ∈ (fullOf n k hn).powerset, N - totalOf n k hn T < 2 * u →
      let omitted := fullOf n k hn \ T
      omitted.card ≤ 2 ∧
      ∀ a ∈ omitted, ∀ b ∈ omitted, a ≠ b →
        (∃ x : Finset (Fin n), x ∩ scopeOf n k hn a.1 = a.2 ∧ x ∩ scopeOf n k hn b.1 = b.2) ∧
        (N - totalOf n k hn T) + 2 ^ (n - (scopeOf n k hn a.1 ∪ scopeOf n k hn b.1).card) = 2 * u := by
    intro T hT hlt
    rw [Finset.mem_powerset] at hT
    set omitted := fullOf n k hn \ T
    have hsum := total_add_bad_T hn hT
    have hbad_eq : N - totalOf n k hn T = (omitted.biUnion (hitOf n k hn)).card := by
      change 2 ^ n - totalOf n k hn T = _
      have hsum' : totalOf n k hn T + (omitted.biUnion (hitOf n k hn)).card = 2 ^ n := hsum
      omega
    have hom_le2 : omitted.card ≤ 2 := by
      by_contra hgt
      have hge3 : 3 ≤ omitted.card := by omega
      obtain ⟨S3, hS3, hS3c⟩ := Finset.exists_subset_card_eq hge3
      rw [Finset.card_eq_three] at hS3c
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hS3c
      have ha : a ∈ fullOf n k hn := Finset.sdiff_subset (hS3 (by simp))
      have hb : b ∈ fullOf n k hn := Finset.sdiff_subset (hS3 (by simp))
      have hc : c ∈ fullOf n k hn := Finset.sdiff_subset (hS3 (by simp))
      have h3 := three_holes_ge_two_u hn hk2 hkn ha hb hc hab hac hbc
      have hsub : hitOf n k hn a ∪ hitOf n k hn b ∪ hitOf n k hn c ⊆ omitted.biUnion (hitOf n k hn) := by
        intro x hx
        simp only [Finset.mem_biUnion, Finset.mem_union] at hx ⊢
        rcases hx with (hxa | hxb) | hxc
        · exact ⟨a, hS3 (by simp), hxa⟩
        · exact ⟨b, hS3 (by simp), hxb⟩
        · exact ⟨c, hS3 (by simp), hxc⟩
      have hle := Finset.card_le_card hsub
      omega
    refine ⟨hom_le2, fun a ha b hb hab => ?_⟩
    have hom_eq : omitted = {a, b} := by
      have hsub : ({a, b} : Finset (Fin n × Finset (Fin n))) ⊆ omitted := by
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl <;> assumption
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab]; exact hom_le2)).symm
    have hbad2 : omitted.biUnion (hitOf n k hn) = hitOf n k hn a ∪ hitOf n k hn b := by
      rw [hom_eq]; ext x; simp
    have ha_f : a ∈ fullOf n k hn := Finset.sdiff_subset ha
    have hb_f : b ∈ fullOf n k hn := Finset.sdiff_subset hb
    have hiu := Finset.card_union_add_card_inter (hitOf n k hn a) (hitOf n k hn b)
    rw [hitOf_card hn hk_le ha_f, hitOf_card hn hk_le hb_f] at hiu
    have hne : (hitOf n k hn a ∩ hitOf n k hn b).Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.card_empty, add_zero] at hiu
      rw [hbad2] at hbad_eq
      omega
    obtain ⟨x, hx⟩ := hne
    simp only [Finset.mem_inter, hitOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨⟨x, hx.1, hx.2⟩, ?_⟩
    rw [hbad_eq, hbad2, ← hitOf_inter_card hn ha_f hb_f ⟨x, by simp [hitOf, hx.1, hx.2]⟩]
    omega
  refine ⟨?_, hstruct⟩
  intro b hb
  set target := E - (if b < u then 0 else if 2 * b < 3 * u then 1 else 2)
  have hge : ∀ c ∈ {c' : Nat | ∃ A ∈ (fullOf n k hn).powerset,
      N - b ≤ totalOf n k hn A ∧ A.card = c'}, target ≤ c := by
    rintro c ⟨A, hA, htot, rfl⟩
    have hA_sub : A ⊆ fullOf n k hn := Finset.mem_powerset.mp hA
    have hsum := total_add_bad_T hn hA_sub
    have hbad_le : ((fullOf n k hn \ A).biUnion (hitOf n k hn)).card ≤ b := by omega
    have hcard_split : A.card + (fullOf n k hn \ A).card = E := by
      rw [add_comm, Finset.card_sdiff_add_card_eq_card hA_sub, hE_card]
    have hst := hstruct A hA (by omega)
    dsimp only at hst
    have hd_bound : (fullOf n k hn \ A).card ≤ (if b < u then 0 else if 2 * b < 3 * u then 1 else 2) := by
      split_ifs with h1 h2
      · by_contra hpos
        have hne : (fullOf n k hn \ A).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨a, ha⟩ := hne
        have hsub : hitOf n k hn a ⊆ (fullOf n k hn \ A).biUnion (hitOf n k hn) :=
          Finset.subset_biUnion_of_mem _ ha
        have hle := Finset.card_le_card hsub
        rw [hitOf_card hn hk_le (Finset.sdiff_subset ha)] at hle
        omega
      · by_contra hgt1
        have hge2 : 2 ≤ (fullOf n k hn \ A).card := by omega
        obtain ⟨S2, hS2, hS2c⟩ := Finset.exists_subset_card_eq hge2
        rw [Finset.card_eq_two] at hS2c
        obtain ⟨p1, p2, hpne, rfl⟩ := hS2c
        have hp1 : p1 ∈ fullOf n k hn \ A := hS2 (by simp)
        have hp2 : p2 ∈ fullOf n k hn \ A := hS2 (by simp)
        have hsub : hitOf n k hn p1 ∪ hitOf n k hn p2 ⊆ (fullOf n k hn \ A).biUnion (hitOf n k hn) := by
          intro x hx; simp only [Finset.mem_union, Finset.mem_biUnion] at hx ⊢
          rcases hx with h | h
          · exact ⟨p1, hp1, h⟩
          · exact ⟨p2, hp2, h⟩
        have hle := Finset.card_le_card hsub
        have hiu := Finset.card_union_add_card_inter (hitOf n k hn p1) (hitOf n k hn p2)
        rw [hitOf_card hn hk_le (Finset.sdiff_subset hp1), hitOf_card hn hk_le (Finset.sdiff_subset hp2)] at hiu
        have hhalf := pair_inter_le_half hn (by omega) hkn (Finset.sdiff_subset hp1) (Finset.sdiff_subset hp2) hpne
        omega
      · exact hst.1
    omega
  have hmem : target ∈ {c' : Nat | ∃ A ∈ (fullOf n k hn).powerset,
      N - b ≤ totalOf n k hn A ∧ A.card = c'} := by
    dsimp only [target]
    split_ifs with h1 h2
    · refine ⟨fullOf n k hn, Finset.mem_powerset.mpr Finset.Subset.rfl, ?_, by rw [hE_card]; omega⟩
      have h := total_add_bad_T hn (T := fullOf n k hn) Finset.Subset.rfl
      simp only [Finset.sdiff_self, Finset.biUnion_empty, Finset.card_empty, add_zero] at h
      omega
    · let a0 : Fin n × Finset (Fin n) := (⟨0, hn⟩, ∅)
      have ha0 : a0 ∈ fullOf n k hn := by simp [a0, fullOf]
      let A := fullOf n k hn \ {a0}
      have hA_sub : A ⊆ fullOf n k hn := Finset.sdiff_subset
      have hA_diff : fullOf n k hn \ A = {a0} := Finset.sdiff_sdiff_eq_self (Finset.singleton_subset_iff.mpr ha0)
      have hsum := total_add_bad_T hn hA_sub
      rw [hA_diff, Finset.singleton_biUnion, hitOf_card hn hk_le ha0] at hsum
      have hA_card : A.card = E - 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr ha0),
          Finset.card_singleton, hE_card]
      exact ⟨A, Finset.mem_powerset.mpr hA_sub, by omega, hA_card⟩
    · let i0 : Fin n := ⟨0, hn⟩
      let i1 : Fin n := ⟨(0 + 1) % n, Nat.mod_lt _ hn⟩
      have hi01 : i0 ≠ i1 := by
        intro heq
        have hv := congrArg Fin.val heq
        dsimp only [i0, i1] at hv
        rw [zero_add, Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
        omega
      let a0 : Fin n × Finset (Fin n) := (i0, ∅)
      let a1 : Fin n × Finset (Fin n) := (i1, ∅)
      have ha0 : a0 ∈ fullOf n k hn := by simp [a0, fullOf]
      have ha1 : a1 ∈ fullOf n k hn := by simp [a1, fullOf]
      have ha01 : a0 ≠ a1 := fun h => hi01 (Prod.mk.inj h).1
      let D : Finset (Fin n × Finset (Fin n)) := {a0, a1}
      have hD_sub : D ⊆ fullOf n k hn := by
        intro p hp; simp only [D, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> assumption
      let A := fullOf n k hn \ D
      have hA_sub : A ⊆ fullOf n k hn := Finset.sdiff_subset
      have hA_diff : fullOf n k hn \ A = D := Finset.sdiff_sdiff_eq_self hD_sub
      have hsum := total_add_bad_T hn hA_sub
      rw [hA_diff] at hsum
      have hD_bad : D.biUnion (hitOf n k hn) = hitOf n k hn a0 ∪ hitOf n k hn a1 := by
        ext x; simp [D]
      rw [hD_bad] at hsum
      have hne01 : (hitOf n k hn a0 ∩ hitOf n k hn a1).Nonempty := by
        refine ⟨∅, ?_⟩
        simp [hitOf, a0, a1]
      have hinter := hitOf_inter_card hn ha0 ha1 hne01
      have hsc_adj : (scopeOf n k hn i0 ∪ scopeOf n k hn i1).card = k + 1 :=
        scopeOf_union_adj hn (by omega) hkn i0
      change (hitOf n k hn a0 ∩ hitOf n k hn a1).card = 2 ^ (n - (scopeOf n k hn i0 ∪ scopeOf n k hn i1).card) at hinter
      rw [hsc_adj] at hinter
      have hiu := Finset.card_union_add_card_inter (hitOf n k hn a0) (hitOf n k hn a1)
      rw [hitOf_card hn hk_le ha0, hitOf_card hn hk_le ha1, hinter] at hiu
      have h2half : 2 * 2 ^ (n - (k + 1)) = u := by
        change 2 * 2 ^ (n - (k + 1)) = 2 ^ (n - k)
        have : n - k = (n - (k + 1)) + 1 := by omega
        rw [this, pow_succ']
      have hA_card : A.card = E - 2 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hD_sub, Finset.card_pair ha01, hE_card]
      obtain ⟨u2, hu2⟩ := hu_even
      exact ⟨A, Finset.mem_powerset.mpr hA_sub, by omega, hA_card⟩
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨target, hmem⟩ hge)

end PEqualNP.Outside.L_meta_25749_aux

theorem PEqualNP.Outside.L_meta_25749 :
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
      let price := fun t : Nat => sInf {c : Nat | ∃ A ∈ full.powerset,
        t ≤ total A ∧ A.card = c}
      let N := 2^n
      let E := n*2^k
      let u := 2^(n-k)
      let off := fun t : Nat => sInf {c : Nat | ∃ D ∈ full.powerset,
        total (full \ D) < t ∧ D.card = c}
      (∀ t : Nat, 0 < t → t ≤ N → off t = (N-t+u)/u) ∧
      (2 ≤ k → k < n →
        (∀ b : Nat, b < 2*u →
          price (N-b) = E - (if b < u then 0 else if 2*b < 3*u then 1 else 2)) ∧
        ∀ T ∈ full.powerset, N-total T < 2*u →
          let omitted := full \ T
          omitted.card ≤ 2 ∧
          ∀ a ∈ omitted, ∀ b ∈ omitted, a ≠ b →
            (∃ x : Finset Site, x ∩ scope a.1 = a.2 ∧ x ∩ scope b.1 = b.2) ∧
            (N-total T) + 2^(n-(scope a.1 ∪ scope b.1).card) = 2*u) :=
  PEqualNP.Outside.L_meta_25749_aux.solve_25749
