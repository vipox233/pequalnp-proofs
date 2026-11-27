import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_229

open PEqualNP.ProofComplexity PEqualNP.Search

noncomputable section

abbrev Lit (W : Type) := Literal W
abbrev Cl (W : Type) := Clause W
abbrev Vis (n w : ℕ) := Sum (Fin n) (Fin n × (Fin (w + 1) → Bool))

def negL {W : Type} (l : Lit W) : Lit W := negLit l

lemma negL_negL {W : Type} (l : Lit W) : negL (negL l) = l := by
  cases l with | mk v b => cases b <;> rfl

lemma negL_sat_iff {W : Type} (α : W → Bool) (r : Lit W) :
    α (negL r).1 = (negL r).2 ↔ α r.1 ≠ r.2 := by
  cases r with | mk v b =>
    dsimp only [negL, negLit]
    cases h : α v <;> cases b <;> decide

def upStep {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) : Set (Lit W) :=
  S ∪ {l | ∃ D ∈ F, l ∈ D ∧ ∀ other ∈ D, other ≠ l → negL other ∈ S}

def seedOf {V M : Type} (ρ : V → Option Bool) : Set (Lit (Sum V M)) :=
  {l | ∃ v : V, l.1 = Sum.inl v ∧ ρ v = some l.2}

lemma mem_seedOf_inl {V M : Type} (ρ : V → Option Bool) (v : V) (b : Bool) :
    ((Sum.inl v, b) : Lit (Sum V M)) ∈ seedOf ρ ↔ ρ v = some b :=
  ⟨fun ⟨_, hv, hr⟩ => Sum.inl.inj hv ▸ hr, fun h => ⟨v, rfl, h⟩⟩

lemma subset_upStep {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) : S ⊆ upStep F S :=
  Set.subset_union_left

lemma upStep_mono {W : Type} {F1 F2 : Finset (Cl W)} {S1 S2 : Set (Lit W)}
    (hF : F1 ⊆ F2) (hS : S1 ⊆ S2) : upStep F1 S1 ⊆ upStep F2 S2 := by
  rintro l (hl | ⟨D, hD, hlD, ho⟩)
  · exact Or.inl (hS hl)
  · exact Or.inr ⟨D, hF hD, hlD, fun o hoD hne => hS (ho o hoD hne)⟩

lemma upStep_iter_mono {W : Type} {F1 F2 : Finset (Cl W)} {S1 S2 : Set (Lit W)}
    (hF : F1 ⊆ F2) (hS : S1 ⊆ S2) : ∀ k : ℕ, (upStep F1)^[k] S1 ⊆ (upStep F2)^[k] S2
  | 0 => hS
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact upStep_mono hF (upStep_iter_mono hF hS k)

lemma upStep_iter_le {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) {k1 k2 : ℕ}
    (h : k1 ≤ k2) : (upStep F)^[k1] S ⊆ (upStep F)^[k2] S :=
  Function.monotone_iterate_of_id_le (subset_upStep F) h S

lemma upStep_iter_pred_succ {W : Type} {F : Finset (Cl W)} {S : Set (Lit W)} {n : ℕ}
    (hn : 0 < n) {l : Lit W} (h : l ∈ upStep F ((upStep F)^[n - 1] S)) :
    l ∈ (upStep F)^[n] S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt hn)
  rw [Function.iterate_succ_apply']
  exact h

lemma upStep_iter_sound {W : Type} {F : Finset (Cl W)} {α : W → Bool}
    (hF : Satisfies α (↑F : Set (Cl W))) {S : Set (Lit W)}
    (hS : ∀ l ∈ S, α l.1 = l.2) : ∀ k : ℕ, ∀ l ∈ (upStep F)^[k] S, α l.1 = l.2
  | 0 => hS
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    rintro l (hl | ⟨D, hD, hlD, ho⟩)
    · exact upStep_iter_sound hF hS k l hl
    · obtain ⟨u, huD, hu⟩ := hF D (Finset.mem_coe.2 hD)
      by_cases hEq : u = l
      · exact hEq ▸ hu
      · exact absurd hu ((negL_sat_iff α u).1 (upStep_iter_sound hF hS k _ (ho u huD hEq)))

lemma upStep_conflict_false {W : Type} {F : Finset (Cl W)} {α : W → Bool}
    (hF : Satisfies α (↑F : Set (Cl W))) {S : Set (Lit W)}
    (hS : ∀ l ∈ S, α l.1 = l.2) (d : ℕ) {D : Cl W} (hD : D ∈ F)
    (hfalse : ∀ l ∈ D, negL l ∈ (upStep F)^[d] S) : False := by
  obtain ⟨l, hlD, hl⟩ := hF D (Finset.mem_coe.2 hD)
  exact (negL_sat_iff α l).1 (upStep_iter_sound hF hS d _ (hfalse l hlD)) hl

lemma seedOf_sound {V M : Type} {ρ : V → Option Bool} {a : V → Bool} {aux : M → Bool}
    (hρ : ∀ (v : V) (b : Bool), ρ v = some b → a v = b) :
    ∀ l ∈ (seedOf ρ : Set (Lit (Sum V M))), Sum.elim a aux l.1 = l.2 :=
  fun _ ⟨v, hv, hrv⟩ => hv ▸ hρ v _ hrv

lemma upStep_support {W : Type} [DecidableEq W] {F : Finset (Cl W)}
    (hcard : ∀ D ∈ F, D.card ≤ 3) (S : Set (Lit W)) :
    ∀ k : ℕ, ∀ l ∈ (upStep F)^[k] S,
      ∃ T : Finset (Lit W), (∀ x ∈ T, x ∈ S) ∧ T.card ≤ 2 ^ k ∧
        l ∈ (upStep F)^[k] (↑T : Set (Lit W))
  | 0, l, hl =>
    ⟨{l}, fun _ hx => (Finset.mem_singleton.1 hx) ▸ hl,
      by simp only [Finset.card_singleton, pow_zero, le_refl],
      Finset.mem_coe.2 (Finset.mem_singleton_self l)⟩
  | k + 1, l, hl => by
    rw [Function.iterate_succ_apply'] at hl
    rcases hl with hl | ⟨D, hD, hlD, hother⟩
    · obtain ⟨T, hTS, hTcard, hlT⟩ := upStep_support hcard S k l hl
      exact ⟨T, hTS, hTcard.trans (Nat.pow_le_pow_right (by omega) k.le_succ),
        by rw [Function.iterate_succ_apply']; exact Or.inl hlT⟩
    · have hrec : ∀ o ∈ D.erase l, ∃ T : Finset (Lit W), (∀ x ∈ T, x ∈ S) ∧ T.card ≤ 2 ^ k ∧
          negL o ∈ (upStep F)^[k] (↑T : Set (Lit W)) :=
        fun o ho => upStep_support hcard S k (negL o)
          (hother o (Finset.mem_of_mem_erase ho) (Finset.ne_of_mem_erase ho))
      choose Q hQS hQcard hQmem using hrec
      have hEcard : (D.erase l).card ≤ 2 := by
        have h1 := hcard D hD
        have h2 := Finset.card_erase_add_one hlD
        omega
      refine ⟨(D.erase l).attach.biUnion fun o => Q o.1 o.2,
        fun x hx => by
          rcases Finset.mem_biUnion.1 hx with ⟨o, _, hxo⟩
          exact hQS o.1 o.2 x hxo,
        ?_, ?_⟩
      · calc ((D.erase l).attach.biUnion fun o => Q o.1 o.2).card
            ≤ ∑ o ∈ (D.erase l).attach, (Q o.1 o.2).card := Finset.card_biUnion_le
          _ ≤ ∑ _o ∈ (D.erase l).attach, 2 ^ k := Finset.sum_le_sum fun o _ => hQcard o.1 o.2
          _ = (D.erase l).card * 2 ^ k := by rw [Finset.sum_const, Finset.card_attach, smul_eq_mul]
          _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_right _ hEcard
          _ = 2 ^ (k + 1) := by rw [pow_succ, mul_comm]
      · rw [Function.iterate_succ_apply']
        refine Or.inr ⟨D, hD, hlD, fun o hoD hne => ?_⟩
        have ho' : o ∈ D.erase l := Finset.mem_erase.2 ⟨hne, hoD⟩
        have hsub : (↑(Q o ho') : Set (Lit W)) ⊆
            ↑((D.erase l).attach.biUnion fun u => Q u.1 u.2) :=
          Finset.coe_subset.2
            (Finset.subset_biUnion_of_mem (fun u => Q u.1 u.2) (Finset.mem_attach _ ⟨o, ho'⟩))
        exact upStep_iter_mono Finset.Subset.rfl hsub k (hQmem o ho')

abbrev FailR (W : Type) := Option (List (Lit W))

def Fails {W : Type} (α : W → Bool) : FailR W → Prop
  | none => True
  | some R => ∃ r ∈ R, α r.1 = r.2

def KnownFail {W : Type} (K : Set (Lit W)) : FailR W → Prop
  | none => True
  | some R => ∃ r ∈ R, r ∈ K

def rLen {W : Type} : FailR W → ℕ
  | none => 0
  | some R => R.length

def OptSat {W : Type} (α : W → Bool) : Option (Lit W) → Prop
  | none => False
  | some l => α l.1 = l.2

def failLits {W : Type} : FailR W → List (List (Lit W))
  | none => [[]]
  | some R => R.map fun r => [negL r]

lemma failLits_len_le {W : Type} (X : FailR W) : ∀ c ∈ failLits X, c.length ≤ 1 := by
  cases X with
  | none => intro c hc; rw [List.mem_singleton.1 hc]; exact Nat.zero_le 1
  | some R => intro c hc; rcases List.mem_map.1 hc with ⟨_, _, rfl⟩; exact le_rfl

lemma failLits_length {W : Type} (X : FailR W) : (failLits X).length ≤ max 1 (rLen X) := by
  cases X with
  | none => exact le_max_left 1 0
  | some R => simp only [failLits, rLen, List.length_map]; exact le_max_right 1 R.length

lemma Fails_iff_failLits {W : Type} (α : W → Bool) (X : FailR W) :
    Fails α X ↔ ∃ c ∈ failLits X, ∀ u ∈ c, α u.1 ≠ u.2 := by
  cases X with
  | none =>
    exact ⟨fun _ => ⟨[], List.mem_singleton_self _, fun _ h => absurd h List.not_mem_nil⟩,
      fun _ => trivial⟩
  | some R =>
    simp only [Fails, failLits, List.mem_map]
    constructor
    · rintro ⟨r, hr, h⟩
      refine ⟨[negL r], ⟨r, hr, rfl⟩, fun u hu => ?_⟩
      rw [List.mem_singleton.1 hu]
      exact fun hn => (negL_sat_iff α r).1 hn h
    · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
      have hne := h (negL r) (List.mem_singleton_self _)
      exact ⟨r, hr, by_contra fun hn => hne ((negL_sat_iff α r).2 hn)⟩

lemma KnownFail_iff_failLits {W : Type} (K : Set (Lit W)) (X : FailR W) :
    KnownFail K X ↔ ∃ c ∈ failLits X, ∀ u ∈ c, negL u ∈ K := by
  cases X with
  | none =>
    exact ⟨fun _ => ⟨[], List.mem_singleton_self _, fun _ h => absurd h List.not_mem_nil⟩,
      fun _ => trivial⟩
  | some R =>
    simp only [KnownFail, failLits, List.mem_map]
    constructor
    · rintro ⟨r, hr, h⟩
      exact ⟨[negL r], ⟨r, hr, rfl⟩, fun u hu => by rw [List.mem_singleton.1 hu, negL_negL]; exact h⟩
    · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
      exact ⟨r, hr, by have := h (negL r) (List.mem_singleton_self _); rwa [negL_negL] at this⟩

def orClauses {W : Type} [DecidableEq W] (A B : FailR W) (out : Option (Lit W)) : List (Cl W) :=
  (failLits A).flatMap fun c1 =>
    (failLits B).flatMap fun c2 =>
      [(c1 ++ c2 ++ out.toList).toFinset]

lemma orClauses_card {W : Type} [DecidableEq W] (A B : FailR W) (out : Option (Lit W)) :
    ∀ C ∈ orClauses A B out, C.card ≤ 3 := by
  intro C hC
  simp only [orClauses, List.mem_flatMap, List.mem_singleton] at hC
  rcases hC with ⟨c1, hc1, c2, hc2, rfl⟩
  have h1 := failLits_len_le A c1 hc1
  have h2 := failLits_len_le B c2 hc2
  have h3 : out.toList.length ≤ 1 := by
    cases out <;> simp only [Option.toList_none, Option.toList_some, List.length_nil,
      List.length_singleton, Nat.zero_le, le_refl]
  exact (List.toFinset_card_le _).trans (by simp only [List.length_append]; omega)

lemma list_flatMap_length_le {α β : Type} (L : List α) (f : α → List β) (c : ℕ)
    (hf : ∀ x ∈ L, (f x).length ≤ c) : (L.flatMap f).length ≤ L.length * c := by
  induction L with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := hf a (List.mem_cons_self ..)
    have hr := ih fun x hx => hf x (List.mem_cons_of_mem a hx)
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (rest.length * c)]
    exact Nat.add_le_add ha hr

lemma orClauses_length {W : Type} [DecidableEq W] (A B : FailR W) (out : Option (Lit W)) :
    (orClauses A B out).length ≤ max 1 (rLen A) * max 1 (rLen B) := by
  have h1 : (orClauses A B out).length ≤ (failLits A).length * (failLits B).length := by
    refine list_flatMap_length_le _ _ _ fun c1 _ => ?_
    have := list_flatMap_length_le (failLits B) (fun c2 => [(c1 ++ c2 ++ out.toList).toFinset]) 1
      (fun _ _ => le_rfl)
    rwa [Nat.mul_one] at this
  exact h1.trans (Nat.mul_le_mul (failLits_length A) (failLits_length B))

lemma orClauses_cost {W : Type} [DecidableEq W] (A B : FailR W) (out : Option (Lit W)) :
    ∑ C ∈ (orClauses A B out).toFinset, C.card ≤ 3 * (max 1 (rLen A) * max 1 (rLen B)) := by
  calc ∑ C ∈ (orClauses A B out).toFinset, C.card
      ≤ ∑ _C ∈ (orClauses A B out).toFinset, 3 :=
        Finset.sum_le_sum fun C hC => orClauses_card A B out C (List.mem_toFinset.1 hC)
    _ = (orClauses A B out).toFinset.card * 3 := by rw [Finset.sum_const, smul_eq_mul]
    _ = 3 * (orClauses A B out).toFinset.card := Nat.mul_comm _ _
    _ ≤ 3 * (orClauses A B out).length := Nat.mul_le_mul_left 3 (List.toFinset_card_le _)
    _ ≤ 3 * (max 1 (rLen A) * max 1 (rLen B)) := Nat.mul_le_mul_left 3 (orClauses_length A B out)

lemma orClauses_sat {W : Type} [DecidableEq W] (α : W → Bool)
    (A B : FailR W) (out : Option (Lit W)) :
    (∀ C ∈ orClauses A B out, ClauseSat α C) ↔ ((Fails α A ∧ Fails α B) → OptSat α out) := by
  rw [Fails_iff_failLits α A, Fails_iff_failLits α B]
  constructor
  · rintro h ⟨⟨c1, hc1, h1⟩, ⟨c2, hc2, h2⟩⟩
    obtain ⟨u, hu, hsat⟩ := h _
      (List.mem_flatMap.2 ⟨c1, hc1, List.mem_flatMap.2 ⟨c2, hc2, List.mem_singleton_self _⟩⟩)
    simp only [List.mem_toFinset, List.mem_append] at hu
    rcases hu with (hu | hu) | hu
    · exact absurd hsat (h1 u hu)
    · exact absurd hsat (h2 u hu)
    · cases out with
      | none => exact absurd hu List.not_mem_nil
      | some l => exact (List.mem_singleton.1 hu) ▸ hsat
  · intro h C hC
    simp only [orClauses, List.mem_flatMap, List.mem_singleton] at hC
    rcases hC with ⟨c1, hc1, c2, hc2, rfl⟩
    by_cases h1 : ∀ u ∈ c1, α u.1 ≠ u.2
    · by_cases h2 : ∀ u ∈ c2, α u.1 ≠ u.2
      · have hout := h ⟨⟨c1, hc1, h1⟩, ⟨c2, hc2, h2⟩⟩
        cases out with
        | none => exact False.elim hout
        | some l =>
          exact ⟨l, List.mem_toFinset.2 (List.mem_append_right _ (List.mem_singleton_self l)), hout⟩
      · push Not at h2
        obtain ⟨u, hu, hs⟩ := h2
        exact ⟨u, List.mem_toFinset.2 (List.mem_append_left _ (List.mem_append_right _ hu)), hs⟩
    · push Not at h1
      obtain ⟨u, hu, hs⟩ := h1
      exact ⟨u, List.mem_toFinset.2 (List.mem_append_left _ (List.mem_append_left _ hu)), hs⟩

lemma orClauses_upStep_none {W : Type} [DecidableEq W] {F : Finset (Cl W)} {K : Set (Lit W)}
    {A B : FailR W} (hF : ∀ C ∈ orClauses A B none, C ∈ F)
    (hA : KnownFail K A) (hB : KnownFail K B) :
    ∃ D ∈ F, ∀ l ∈ D, negL l ∈ K := by
  obtain ⟨c1, hc1, h1⟩ := (KnownFail_iff_failLits K A).1 hA
  obtain ⟨c2, hc2, h2⟩ := (KnownFail_iff_failLits K B).1 hB
  refine ⟨(c1 ++ c2 ++ (none : Option (Lit W)).toList).toFinset,
    hF _ (List.mem_flatMap.2 ⟨c1, hc1, List.mem_flatMap.2 ⟨c2, hc2, List.mem_singleton_self _⟩⟩), ?_⟩
  intro u hu
  simp only [Option.toList_none, List.append_nil, List.mem_toFinset, List.mem_append] at hu
  exact hu.elim (h1 u) (h2 u)

lemma orClauses_upStep_some {W : Type} [DecidableEq W] {F : Finset (Cl W)} {K : Set (Lit W)}
    {A B : FailR W} {l : Lit W} (hF : ∀ C ∈ orClauses A B (some l), C ∈ F)
    (hA : KnownFail K A) (hB : KnownFail K B) :
    l ∈ upStep F K := by
  obtain ⟨c1, hc1, h1⟩ := (KnownFail_iff_failLits K A).1 hA
  obtain ⟨c2, hc2, h2⟩ := (KnownFail_iff_failLits K B).1 hB
  refine Or.inr ⟨(c1 ++ c2 ++ (some l).toList).toFinset,
    hF _ (List.mem_flatMap.2 ⟨c1, hc1, List.mem_flatMap.2 ⟨c2, hc2, List.mem_singleton_self _⟩⟩),
    List.mem_toFinset.2 (List.mem_append_right _ (List.mem_singleton_self l)), ?_⟩
  intro u hu hne
  simp only [Option.toList_some, List.mem_toFinset, List.mem_append, List.mem_singleton] at hu
  rcases hu with (hu | hu) | rfl
  · exact h1 u hu
  · exact h2 u hu
  · exact absurd rfl hne

lemma sum_biUnion_le {ι β : Type*} [DecidableEq β] (s : Finset ι) (t : ι → Finset β)
    (g : β → ℕ) : ∑ x ∈ s.biUnion t, g x ≤ ∑ i ∈ s, ∑ x ∈ t i, g x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.biUnion_empty, Finset.sum_empty, le_refl]
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have h := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := g)
    omega

lemma sum_union_le {β : Type*} [DecidableEq β] (A B : Finset β) (g : β → ℕ) :
    ∑ x ∈ A ∪ B, g x ≤ (∑ x ∈ A, g x) + (∑ x ∈ B, g x) := by
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := g)
  omega

lemma testBit_div_pow (m : ℕ) : ∀ (d t : ℕ), (m / 2 ^ d).testBit t = m.testBit (d + t)
  | 0, t => by simp only [pow_zero, Nat.div_one, Nat.zero_add]
  | d + 1, t => by
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.testBit_succ, testBit_div_pow m d (t + 1)]
    have h : d + (t + 1) = d + 1 + t := by omega
    rw [h]

lemma testBit_eq_false_of_lt_pow {m k j : ℕ} (hm : m < 2 ^ k) (hjk : k ≤ j) :
    m.testBit j = false := by
  have hle : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hjk
  have hdiv : m / 2 ^ j = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hm hle)
  have h1 := testBit_div_pow m j 0
  rw [Nat.add_zero, hdiv, Nat.zero_testBit] at h1
  exact h1.symm

def leToNat : ∀ {k : ℕ}, (Fin k → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, f => (if f 0 then 1 else 0) + 2 * leToNat (fun r => f r.succ)

lemma leToNat_lt : ∀ {k : ℕ} (f : Fin k → Bool), leToNat f < 2 ^ k
  | 0, _ => by simp only [leToNat, pow_zero]; omega
  | k + 1, f => by
    have ih := leToNat_lt (fun r : Fin k => f r.succ)
    simp only [leToNat, pow_succ]
    cases f 0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

lemma testBit_leToNat : ∀ {k : ℕ} (f : Fin k → Bool) (j : ℕ),
    (leToNat f).testBit j = if h : j < k then f ⟨j, h⟩ else false
  | 0, _, _ => by simp only [leToNat, Nat.zero_testBit, Nat.not_lt_zero, ↓reduceDIte]
  | k + 1, f, j => by
    cases j with
    | zero =>
      simp only [leToNat, Nat.testBit_zero, Nat.zero_lt_succ, ↓reduceDIte]
      cases h0 : f 0
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.mul_mod_right]
        exact h0.symm
      · simp only [↓reduceIte]
        have hmod : (1 + 2 * leToNat (fun r => f r.succ)) % 2 = 1 := by omega
        rw [hmod]
        exact h0.symm
    | succ j' =>
      have hdiv : leToNat f / 2 = leToNat (fun r : Fin k => f r.succ) := by
        simp only [leToNat]
        cases f 0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      rw [Nat.testBit_succ, hdiv, testBit_leToNat]
      by_cases hj : j' < k
      · have hj1 : j' + 1 < k + 1 := Nat.succ_lt_succ hj
        simp only [hj, hj1, ↓reduceDIte]
        rfl
      · have hj1 : ¬ (j' + 1 < k + 1) := by omega
        simp only [hj, hj1, ↓reduceDIte]

def beToNat {n : ℕ} (f : Fin n → Bool) : ℕ :=
  leToNat (fun r : Fin n => f ⟨n - 1 - r.val, by omega⟩)

def beOfNat (n m : ℕ) : Fin n → Bool :=
  fun r => m.testBit (n - 1 - r.val)

lemma beToNat_lt {n : ℕ} (f : Fin n → Bool) : beToNat f < 2 ^ n :=
  leToNat_lt _

lemma testBit_beToNat {n : ℕ} (f : Fin n → Bool) (j : ℕ) :
    (beToNat f).testBit j = if h : j < n then f ⟨n - 1 - j, by omega⟩ else false := by
  unfold beToNat
  rw [testBit_leToNat]

lemma beOfNat_beToNat {n : ℕ} (f : Fin n → Bool) : beOfNat n (beToNat f) = f := by
  funext r
  unfold beOfNat
  rw [testBit_beToNat]
  have hr := r.isLt
  have hlt : n - 1 - r.val < n := by omega
  simp only [hlt, ↓reduceDIte]
  have heq : (⟨n - 1 - (n - 1 - r.val), by omega⟩ : Fin n) = r :=
    Fin.ext (show n - 1 - (n - 1 - r.val) = r.val by omega)
  rw [heq]

lemma beToNat_beOfNat {n m : ℕ} (hm : m < 2 ^ n) : beToNat (beOfNat n m) = m := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_beToNat]
  by_cases hj : j < n
  · simp only [hj, ↓reduceDIte, beOfNat]
    have heq : n - 1 - (n - 1 - j) = j := by omega
    rw [heq]
  · simp only [hj, ↓reduceDIte]
    exact (testBit_eq_false_of_lt_pow hm (by omega)).symm

lemma beOfNat_zero_eq {n m : ℕ} (hn : 0 < n) (hm : m < 2 ^ n) :
    beOfNat n m ⟨0, hn⟩ = decide (2 ^ (n - 1) ≤ m) := by
  unfold beOfNat
  simp only [Nat.sub_zero]
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have heq : n = (n - 1) + 1 := by omega
    conv_lhs => rw [heq, pow_succ, Nat.mul_comm]
  have htb : m.testBit (n - 1) = (m / 2 ^ (n - 1)).testBit 0 := by
    have := testBit_div_pow m (n - 1) 0
    rw [Nat.add_zero] at this
    exact this.symm
  rw [htb]
  by_cases hle : 2 ^ (n - 1) ≤ m
  · have hdiv : m / 2 ^ (n - 1) = 1 := by
      have hpos : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hdiv, decide_eq_true hle]
    rfl
  · have hdiv : m / 2 ^ (n - 1) = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv, decide_eq_false hle]
    rfl

lemma beOfNat_prefix_iff_div {n K m1 m2 : ℕ} (hKn : K ≤ n) (hm1 : m1 < 2 ^ n) (hm2 : m2 < 2 ^ n) :
    (∀ r : Fin K, beOfNat n m1 ⟨r.val, Nat.lt_of_lt_of_le r.isLt hKn⟩ =
      beOfNat n m2 ⟨r.val, Nat.lt_of_lt_of_le r.isLt hKn⟩) ↔
      m1 / 2 ^ (n - K) = m2 / 2 ^ (n - K) := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro t
    rw [testBit_div_pow, testBit_div_pow]
    by_cases ht : t < K
    · have hr := h ⟨K - 1 - t, by omega⟩
      unfold beOfNat at hr
      have heq : n - 1 - (K - 1 - t) = (n - K) + t := by omega
      rwa [heq] at hr
    · rw [testBit_eq_false_of_lt_pow hm1 (by omega), testBit_eq_false_of_lt_pow hm2 (by omega)]
  · intro hdiv r
    unfold beOfNat
    have ht : (n - K) + (K - 1 - r.val) = n - 1 - r.val := by omega
    rw [← ht, ← testBit_div_pow, ← testBit_div_pow, hdiv]

def rotShift {n : ℕ} (hn : 0 < n) (i r : Fin n) : Fin n :=
  ⟨(i.val + r.val) % n, Nat.mod_lt _ hn⟩

def rotUnshift {n : ℕ} (hn : 0 < n) (i k : Fin n) : Fin n :=
  ⟨(k.val + n - i.val) % n, Nat.mod_lt _ hn⟩

lemma rotShift_rotUnshift {n : ℕ} (hn : 0 < n) (i k : Fin n) :
    rotShift hn i (rotUnshift hn i k) = k := by
  apply Fin.ext
  dsimp only [rotShift, rotUnshift]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h1 : i.val + (k.val + n - i.val) = k.val + n := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]

lemma rotUnshift_rotShift {n : ℕ} (hn : 0 < n) (i r : Fin n) :
    rotUnshift hn i (rotShift hn i r) = r := by
  apply Fin.ext
  dsimp only [rotShift, rotUnshift]
  by_cases hlt : i.val + r.val < n
  · rw [Nat.mod_eq_of_lt hlt]
    have h1 : i.val + r.val + n - i.val = r.val + n := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
  · have hmod : (i.val + r.val) % n = i.val + r.val - n := by
      have hsub : i.val + r.val = (i.val + r.val - n) + n := by omega
      conv_lhs => rw [hsub]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have h1 : i.val + r.val - n + n - i.val = r.val := by omega
    rw [h1, Nat.mod_eq_of_lt r.isLt]

lemma rotUnshift_self {n : ℕ} (hn : 0 < n) (k : Fin n) :
    rotUnshift hn k k = ⟨0, hn⟩ := by
  apply Fin.ext
  dsimp only [rotUnshift]
  have h1 : k.val + n - k.val = n := by omega
  rw [h1, Nat.mod_self]

def rotBits {n : ℕ} (hn : 0 < n) (i : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun r => x (rotShift hn i r)

def unrotBits {n : ℕ} (hn : 0 < n) (i : Fin n) (f : Fin n → Bool) : Fin n → Bool :=
  fun k => f (rotUnshift hn i k)

lemma unrotBits_rotBits {n : ℕ} (hn : 0 < n) (i : Fin n) (x : Fin n → Bool) :
    unrotBits hn i (rotBits hn i x) = x := by
  funext k
  dsimp only [unrotBits, rotBits]
  rw [rotShift_rotUnshift]

lemma rotBits_unrotBits {n : ℕ} (hn : 0 < n) (i : Fin n) (f : Fin n → Bool) :
    rotBits hn i (unrotBits hn i f) = f := by
  funext r
  dsimp only [unrotBits, rotBits]
  rw [rotUnshift_rotShift]

def rotIdx {n : ℕ} (hn : 0 < n) (i : Fin n) (x : Fin n → Bool) : ℕ :=
  beToNat (rotBits hn i x)

lemma rotIdx_lt {n : ℕ} (hn : 0 < n) (i : Fin n) (x : Fin n → Bool) :
    rotIdx hn i x < 2 ^ n :=
  beToNat_lt _

def rotWord {n : ℕ} (hn : 0 < n) (i : Fin n) (s : ℕ) : Fin n → Bool :=
  unrotBits hn i (beOfNat n (s % 2 ^ n))

lemma rotWord_mod {n : ℕ} (hn : 0 < n) (i : Fin n) (s : ℕ) :
    rotWord hn i (s % 2 ^ n) = rotWord hn i s := by
  unfold rotWord
  rw [Nat.mod_mod]

lemma rotWord_rotIdx {n : ℕ} (hn : 0 < n) (i : Fin n) (x : Fin n → Bool) :
    rotWord hn i (rotIdx hn i x) = x := by
  unfold rotWord rotIdx
  rw [Nat.mod_eq_of_lt (beToNat_lt _), beOfNat_beToNat, unrotBits_rotBits]

lemma rotIdx_rotWord {n : ℕ} (hn : 0 < n) (i : Fin n) (s : ℕ) :
    rotIdx hn i (rotWord hn i s) = s % 2 ^ n := by
  unfold rotWord rotIdx
  rw [rotBits_unrotBits, beToNat_beOfNat (Nat.mod_lt _ (Nat.two_pow_pos n))]

lemma rotWord_self {n : ℕ} (hn : 0 < n) (k : Fin n) {s : ℕ} (hs : s < 2 ^ n) :
    rotWord hn k s k = decide (2 ^ (n - 1) ≤ s) := by
  unfold rotWord unrotBits
  rw [rotUnshift_self, Nat.mod_eq_of_lt hs]
  exact beOfNat_zero_eq hn hs

def inHalf (H s m : ℕ) : Prop :=
  ∃ t : ℕ, t < H ∧ (s + t) % (2 * H) = m

lemma half_cover_iff {H B a m : ℕ} (_hH : 0 < H) (hBH : B ≤ H) (haB : a + B ≤ 2 * H)
    (hm : m < 2 * H) :
    (inHalf H ((a + B) % (2 * H)) m ∨ inHalf H ((a + H) % (2 * H)) m) ↔
      ¬ (a ≤ m ∧ m < a + B) := by
  have hmod1 : ∀ t : ℕ, ((a + B) % (2 * H) + t) % (2 * H) = (a + B + t) % (2 * H) := fun t => by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hmod2 : ∀ t : ℕ, ((a + H) % (2 * H) + t) % (2 * H) = (a + H + t) % (2 * H) := fun t => by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  constructor
  · rintro (⟨t, ht, hmt⟩ | ⟨t, ht, hmt⟩) ⟨ham, hmaB⟩
    · rw [hmod1] at hmt
      by_cases hlt : a + B + t < 2 * H
      · rw [Nat.mod_eq_of_lt hlt] at hmt
        omega
      · have hsub : a + B + t = (a + B + t - 2 * H) + 2 * H := by omega
        rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hmt
        omega
    · rw [hmod2] at hmt
      by_cases hlt : a + H + t < 2 * H
      · rw [Nat.mod_eq_of_lt hlt] at hmt
        omega
      · have hsub : a + H + t = (a + H + t - 2 * H) + 2 * H := by omega
        rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hmt
        omega
  · intro hnot
    by_cases hge : a + B ≤ m
    · by_cases hlt : m < a + B + H
      · left
        refine ⟨m - (a + B), by omega, ?_⟩
        rw [hmod1]
        have h1 : a + B + (m - (a + B)) = m := by omega
        rw [h1, Nat.mod_eq_of_lt hm]
      · right
        refine ⟨m - (a + H), by omega, ?_⟩
        rw [hmod2]
        have h1 : a + H + (m - (a + H)) = m := by omega
        rw [h1, Nat.mod_eq_of_lt hm]
    · have hma : m < a := by omega
      by_cases hle : a ≤ m + H
      · right
        refine ⟨m + H - a, by omega, ?_⟩
        rw [hmod2]
        have h1 : a + H + (m + H - a) = m + 2 * H := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
      · left
        refine ⟨m + 2 * H - (a + B), by omega, ?_⟩
        rw [hmod1]
        have h1 : a + B + (m + 2 * H - (a + B)) = m + 2 * H := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hm]

def win {n : ℕ} (hn : 0 < n) (w : ℕ) (i : Fin n) (x : Fin n → Bool) : Fin (w + 1) → Bool :=
  fun j => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

def wordOf {n w : ℕ} (a : Vis n w → Bool) : Fin n → Bool :=
  fun k => a (Sum.inl k)

def Accepts {n : ℕ} (hn : 0 < n) (w : ℕ) (a : Vis n w → Bool) : Prop :=
  ∀ i : Fin n, a (Sum.inr (i, win hn w i (wordOf a))) = true

def Completion {n : ℕ} (hn : 0 < n) (w : ℕ) (ρ : Vis n w → Option Bool) (a : Vis n w → Bool) :
    Prop :=
  Accepts hn w a ∧ ∀ (v : Vis n w) (b : Bool), ρ v = some b → a v = b

lemma win_eq_iff_rotIdx_div {n : ℕ} (hn : 0 < n) (w : ℕ) (i : Fin n) (x y : Fin n → Bool) :
    win hn w i x = win hn w i y ↔
      rotIdx hn i x / 2 ^ (n - min n (w + 1)) = rotIdx hn i y / 2 ^ (n - min n (w + 1)) := by
  have hKn : min n (w + 1) ≤ n := Nat.min_le_left n (w + 1)
  have hiff := beOfNat_prefix_iff_div hKn (rotIdx_lt hn i x) (rotIdx_lt hn i y)
  have hbe : ∀ z : Fin n → Bool, beOfNat n (rotIdx hn i z) = rotBits hn i z := fun z => by
    unfold rotIdx
    exact beOfNat_beToNat _
  rw [hbe x, hbe y] at hiff
  rw [← hiff]
  constructor
  · intro h r
    have hrw : r.val < w + 1 := Nat.lt_of_lt_of_le r.isLt (Nat.min_le_right n (w + 1))
    exact congrFun h ⟨r.val, hrw⟩
  · intro h
    funext j
    unfold win
    by_cases hnw : n ≤ w + 1
    · have hmin : min n (w + 1) = n := Nat.min_eq_left hnw
      let r : Fin (min n (w + 1)) := ⟨j.val % n, hmin.symm ▸ Nat.mod_lt _ hn⟩
      have hr := h r
      dsimp only [rotBits, rotShift] at hr
      have hmod : (i.val + j.val % n) % n = (i.val + j.val) % n := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hfin : (⟨(i.val + j.val % n) % n, Nat.mod_lt _ hn⟩ : Fin n) =
          ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ := Fin.ext hmod
      simpa only [r, hfin] using hr
    · have hjlt : j.val < min n (w + 1) := by have := j.isLt; omega
      exact h ⟨j.val, hjlt⟩

lemma lower_bound {n w : ℕ} (hn : 0 < n) (hnw : n ≤ w + 1) {d m : ℕ}
    {F : Finset (Cl (Sum (Vis n w) (Fin m)))}
    (hcard : ∀ D ∈ F, D.card ≤ 3)
    (hsat : ∀ total : Vis n w → Bool, Accepts hn w total ↔ ∃ aux : Fin m → Bool,
      Satisfies (Sum.elim total aux) (↑F : Set _))
    (hforce : ∀ ρ : Vis n w → Option Bool,
      (∃ a : Vis n w → Bool, Completion hn w ρ a) → ∀ v : Vis n w, ∀ b : Bool,
        (∀ a : Vis n w → Bool, Completion hn w ρ a → a v = b) ↔
          (Sum.inl v, b) ∈ (upStep F)^[d] (seedOf ρ)) :
    n ≤ d := by
  let _ : DecidableEq (Vis n w) := Classical.decEq _
  let i0 : Fin n := ⟨0, hn⟩
  let x0 : Fin n → Bool := fun _ => false
  let pat : (Fin n → Bool) → (Fin (w + 1) → Bool) := win hn w i0
  have hpat_inj : Function.Injective pat := by
    intro x y hxy
    funext k
    have hk : k.val < w + 1 := Nat.lt_of_lt_of_le k.isLt hnw
    have h := congrFun hxy ⟨k.val, hk⟩
    dsimp only [pat, win, i0] at h
    have hmod : (0 + k.val) % n = k.val := by rw [Nat.zero_add, Nat.mod_eq_of_lt k.isLt]
    have hfin : (⟨(0 + k.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = k := Fin.ext hmod
    simpa only [hfin] using h
  let ρ : Vis n w → Option Bool := fun v =>
    match v with
    | Sum.inl _ => none
    | Sum.inr (i, p) =>
      if i = i0 ∧ ∃ x : Fin n → Bool, x ≠ x0 ∧ pat x = p then some false else none
  let a0 : Vis n w → Bool := fun v =>
    match v with
    | Sum.inl k => x0 k
    | Sum.inr (i, p) => if i = i0 ∧ p ≠ pat x0 then false else true
  have ha0 : Completion hn w ρ a0 := by
    refine ⟨?_, ?_⟩
    · intro i
      dsimp only [a0]
      have hwin : win hn w i (wordOf a0) = pat x0 := by
        funext j; rfl
      rw [hwin]
      simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte]
    · intro v b hρv
      cases v with
      | inl k => simp only [ρ] at hρv; cases hρv
      | inr ip =>
        rcases ip with ⟨i, p⟩
        dsimp only [ρ] at hρv
        by_cases hcond : i = i0 ∧ ∃ x : Fin n → Bool, x ≠ x0 ∧ pat x = p
        · simp only [hcond] at hρv
          rcases hcond with ⟨rfl, x, hne, rfl⟩
          have hb : b = false := Option.some.inj hρv.symm
          subst hb
          dsimp only [a0]
          have hpne : pat x ≠ pat x0 := fun h => hne (hpat_inj h)
          simp only [hpne, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
        · simp only [hcond, ↓reduceIte] at hρv
          cases hρv
  have hforced : ∀ a : Vis n w → Bool, Completion hn w ρ a → a (Sum.inr (i0, pat x0)) = true := by
    intro a ⟨hacc, hρa⟩
    have hwx : wordOf a = x0 := by
      by_contra hne
      have hρp : ρ (Sum.inr (i0, pat (wordOf a))) = some false := by
        dsimp only [ρ]
        have hcond : i0 = i0 ∧ ∃ x : Fin n → Bool, x ≠ x0 ∧ pat x = pat (wordOf a) :=
          ⟨rfl, wordOf a, hne, rfl⟩
        exact ite_eq_left_iff.2 fun hnot => absurd hcond hnot
      have hfalse := hρa (Sum.inr (i0, pat (wordOf a))) false hρp
      have htrue := hacc i0
      rw [htrue] at hfalse
      cases hfalse
    have htrue := hacc i0
    dsimp only [pat]
    rwa [← hwx]
  have hmem : (Sum.inl (Sum.inr (i0, pat x0)), true) ∈ (upStep F)^[d] (seedOf ρ) :=
    (hforce ρ ⟨a0, ha0⟩ (Sum.inr (i0, pat x0)) true).1 hforced
  by_contra hlt
  have hdn : d < n := Nat.lt_of_not_le hlt
  by_cases hd0 : d = 0
  · subst hd0
    simp only [Function.iterate_zero, id_eq] at hmem
    have hρp := (mem_seedOf_inl ρ (Sum.inr (i0, pat x0)) true).1 hmem
    dsimp only [ρ] at hρp
    have hnot : ¬ (i0 = i0 ∧ ∃ x : Fin n → Bool, x ≠ x0 ∧ pat x = pat x0) := by
      rintro ⟨_, x, hne, heq⟩
      exact hne (hpat_inj heq)
    rw [ite_eq_right_iff.2 fun h => absurd h hnot] at hρp
    cases hρp
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨T, hTS, hTcard, hmemT⟩ := upStep_support hcard (seedOf ρ) d _ hmem
    let others : Finset (Fin n → Bool) := Finset.univ.erase x0
    let emb : (Fin n → Bool) → Lit (Sum (Vis n w) (Fin m)) :=
      fun x => (Sum.inl (Sum.inr (i0, pat x)), false)
    have hemb_inj : Function.Injective emb := by
      intro x y hxy
      have h1 := Prod.mk.inj hxy
      have h2 := Sum.inl.inj h1.1
      have h3 := Sum.inr.inj h2
      have h4 := Prod.mk.inj h3
      exact hpat_inj h4.2
    have hothers_card : (others.image emb).card = 2 ^ n - 1 := by
      rw [Finset.card_image_of_injective _ hemb_inj,
        Finset.card_erase_of_mem (Finset.mem_univ x0), Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin]
    have hlt_card : T.card < (others.image emb).card := by
      rw [hothers_card]
      have h1 : 2 ^ d ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        have heq : n = (n - 1) + 1 := by omega
        conv_lhs => rw [heq, pow_succ, Nat.mul_comm]
      have h3 : 2 ≤ 2 ^ (n - 1) := by
        have := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ n - 1 by omega)
        simpa only [pow_one] using this
      omega
    obtain ⟨lit1, hlit1_in, hlit1_notin⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_card
    obtain ⟨x1, hx1_mem, rfl⟩ := Finset.mem_image.1 hlit1_in
    have hx1_ne : x1 ≠ x0 := Finset.ne_of_mem_erase hx1_mem
    let a1 : Vis n w → Bool := fun v =>
      match v with
      | Sum.inl k => x1 k
      | Sum.inr (i, p) => if i = i0 then decide (p = pat x1) else true
    have ha1_acc : Accepts hn w a1 := by
      intro i
      dsimp only [a1]
      split_ifs with hi
      · subst hi
        have hwin : win hn w i0 (wordOf a1) = pat x1 := rfl
        rw [hwin, decide_eq_true rfl]
      · rfl
    obtain ⟨aux1, hsat1⟩ := (hsat a1).1 ha1_acc
    have hT_sound : ∀ l ∈ (↑T : Set (Lit (Sum (Vis n w) (Fin m)))),
        Sum.elim a1 aux1 l.1 = l.2 := by
      intro l hlT
      have hl_mem : l ∈ T := Finset.mem_coe.1 hlT
      obtain ⟨v, hv, hρv⟩ := hTS l hl_mem
      cases v with
      | inl k => simp only [ρ] at hρv; cases hρv
      | inr ip =>
        rcases ip with ⟨i, p⟩
        dsimp only [ρ] at hρv
        by_cases hcond : i = i0 ∧ ∃ x : Fin n → Bool, x ≠ x0 ∧ pat x = p
        · simp only [hcond] at hρv
          rcases hcond with ⟨rfl, x, _, rfl⟩
          have hl2 : l.2 = false := Option.some.inj hρv.symm
          have hne_x : x ≠ x1 := by
            intro heq
            subst heq
            have hleq : l = emb x := Prod.ext hv hl2
            exact hlit1_notin (hleq ▸ hl_mem)
          rw [hv, hl2]
          dsimp only [Sum.elim, a1]
          have hpne : pat x ≠ pat x1 := fun h => hne_x (hpat_inj h)
          simp only [↓reduceIte, decide_eq_false hpne]
        · simp only [hcond, ↓reduceIte] at hρv
          cases hρv
    have hres := upStep_iter_sound hsat1 hT_sound d _ hmemT
    dsimp only [Sum.elim, a1] at hres
    have hpne01 : pat x0 ≠ pat x1 := fun h => hx1_ne (hpat_inj h.symm)
    simp only [↓reduceIte, decide_eq_false hpne01] at hres
    cases hres

abbrev AuxType (n : ℕ) := Fin n × Fin (n - 1) × Fin (2 ^ n)

def mAux (n : ℕ) : ℕ := Fintype.card (AuxType n)

def ι (n : ℕ) : AuxType n ≃ Fin (mAux n) := Fintype.equivFin (AuxType n)

abbrev W (n w : ℕ) := Sum (Vis n w) (Fin (mAux n))

def sMod (n k : ℕ) : Fin (2 ^ n) :=
  ⟨k % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

def auxLit {n w : ℕ} (i : Fin n) (d : Fin (n - 1)) (s : Fin (2 ^ n)) : Lit (W n w) :=
  (Sum.inr (ι n (i, d, s)), true)

def wordFail {n : ℕ} (hn : 0 < n) (w : ℕ) (x : Fin n → Bool) : FailR (W n w) :=
  some (
    (List.finRange n).map (fun k => (Sum.inl (Sum.inl k), !(x k))) ++
    (List.finRange n).map (fun i => (Sum.inl (Sum.inr (i, win hn w i x)), false))
  )

lemma rLen_wordFail {n : ℕ} (hn : 0 < n) (w : ℕ) (x : Fin n → Bool) :
    rLen (wordFail hn w x) = 2 * n := by
  simp only [wordFail, rLen, List.length_append, List.length_map, List.length_finRange]
  omega

lemma Fails_wordFail_iff {n : ℕ} (hn : 0 < n) (w : ℕ) (total : Vis n w → Bool)
    (aux : Fin (mAux n) → Bool) (x : Fin n → Bool) :
    Fails (Sum.elim total aux) (wordFail hn w x) ↔
      (∃ k : Fin n, total (Sum.inl k) = !(x k)) ∨
      (∃ i : Fin n, total (Sum.inr (i, win hn w i x)) = false) := by
  simp only [wordFail, Fails, List.mem_append, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨r, (⟨k, rfl⟩ | ⟨i, rfl⟩), h⟩
    · exact Or.inl ⟨k, h⟩
    · exact Or.inr ⟨i, h⟩
  · rintro (⟨k, h⟩ | ⟨i, h⟩)
    · exact ⟨_, Or.inl ⟨k, rfl⟩, h⟩
    · exact ⟨_, Or.inr ⟨i, rfl⟩, h⟩

lemma KnownFail_wordFail_seed_iff {n : ℕ} (hn : 0 < n) (w : ℕ)
    (ρ : Vis n w → Option Bool) (x : Fin n → Bool) :
    KnownFail (seedOf ρ : Set (Lit (W n w))) (wordFail hn w x) ↔
      (∃ k : Fin n, ρ (Sum.inl k) = some (!(x k))) ∨
      (∃ i : Fin n, ρ (Sum.inr (i, win hn w i x)) = some false) := by
  simp only [wordFail, KnownFail, List.mem_append, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨r, (⟨k, rfl⟩ | ⟨i, rfl⟩), h⟩
    · exact Or.inl ⟨k, (mem_seedOf_inl ρ _ _).1 h⟩
    · exact Or.inr ⟨i, (mem_seedOf_inl ρ _ _).1 h⟩
  · rintro (⟨k, h⟩ | ⟨i, h⟩)
    · exact ⟨_, Or.inl ⟨k, rfl⟩, (mem_seedOf_inl ρ _ _).2 h⟩
    · exact ⟨_, Or.inr ⟨i, rfl⟩, (mem_seedOf_inl ρ _ _).2 h⟩

def halfFail {n : ℕ} (hn : 0 < n) (w : ℕ) (i : Fin n) (s : Fin (2 ^ n)) : FailR (W n w) :=
  if h : 0 < n - 1 then
    some [auxLit i ⟨n - 2, by omega⟩ s]
  else
    wordFail hn w (rotWord hn i s.val)

lemma rLen_halfFail_le {n : ℕ} (hn : 0 < n) (w : ℕ) (i : Fin n) (s : Fin (2 ^ n)) :
    rLen (halfFail hn w i s) ≤ 2 := by
  unfold halfFail
  split_ifs with h
  · simp only [rLen, List.length_singleton]; omega
  · rw [rLen_wordFail]; omega

def F_lvl1 {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)] : Finset (Cl (W n w)) :=
  if h : 0 < n - 1 then
    (Finset.univ : Finset (Fin n × Fin (2 ^ n))).biUnion fun p =>
      (orClauses
        (wordFail hn w (rotWord hn p.1 p.2.val))
        (wordFail hn w (rotWord hn p.1 (p.2.val + 1)))
        (some (auxLit p.1 ⟨0, h⟩ p.2))).toFinset
  else ∅

def F_dbl (n w : ℕ) [DecidableEq (Vis n w)] : Finset (Cl (W n w)) :=
  (Finset.univ : Finset (Fin n × Fin (n - 1) × Fin (2 ^ n))).biUnion fun p =>
    if h : 0 < p.2.1.val then
      (orClauses
        (some [auxLit p.1 ⟨p.2.1.val - 1, by omega⟩ p.2.2])
        (some [auxLit p.1 ⟨p.2.1.val - 1, by omega⟩ (sMod n (p.2.2.val + 2 ^ p.2.1.val))])
        (some (auxLit p.1 p.2.1 p.2.2))).toFinset
    else ∅

def F_perm {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)] : Finset (Cl (W n w)) :=
  let B := 2 ^ (n - min n (w + 1))
  let H := 2 ^ (n - 1)
  (Finset.univ : Finset (Fin n × Fin (2 ^ n))).biUnion fun p =>
    let a := (p.2.val / B) * B
    (orClauses
      (halfFail hn w p.1 (sMod n (a + B)))
      (halfFail hn w p.1 (sMod n (a + H)))
      (some (Sum.inl (Sum.inr (p.1, win hn w p.1 (rotWord hn p.1 p.2.val))), true))).toFinset

def F_bit {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)] : Finset (Cl (W n w)) :=
  let H := 2 ^ (n - 1)
  (Finset.univ : Finset (Fin n × Bool)).biUnion fun p =>
    let s := if p.2 then sMod n 0 else sMod n H
    (orClauses
      (halfFail hn w p.1 s)
      none
      (some (Sum.inl (Sum.inl p.1), p.2))).toFinset

def F_conf {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)] : Finset (Cl (W n w)) :=
  let i0 : Fin n := ⟨0, hn⟩
  let H := 2 ^ (n - 1)
  (orClauses
    (halfFail hn w i0 (sMod n 0))
    (halfFail hn w i0 (sMod n H))
    none).toFinset

def F_all {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)] : Finset (Cl (W n w)) :=
  F_lvl1 hn w ∪ F_dbl n w ∪ F_perm hn w ∪ F_bit hn w ∪ F_conf hn w

lemma F_all_card {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)] :
    ∀ D ∈ F_all hn w, D.card ≤ 3 := by
  intro D hD
  simp only [F_all, Finset.mem_union] at hD
  rcases hD with (((h1 | h2) | h3) | h4) | h5
  · unfold F_lvl1 at h1
    split_ifs at h1 with h
    · rcases Finset.mem_biUnion.1 h1 with ⟨p, _, hp⟩
      exact orClauses_card _ _ _ D (List.mem_toFinset.1 hp)
    · exact absurd h1 (Finset.notMem_empty D)
  · rcases Finset.mem_biUnion.1 h2 with ⟨p, _, hp⟩
    split_ifs at hp with h
    · exact orClauses_card _ _ _ D (List.mem_toFinset.1 hp)
    · exact absurd hp (Finset.notMem_empty D)
  · rcases Finset.mem_biUnion.1 h3 with ⟨p, _, hp⟩
    exact orClauses_card _ _ _ D (List.mem_toFinset.1 hp)
  · rcases Finset.mem_biUnion.1 h4 with ⟨p, _, hp⟩
    exact orClauses_card _ _ _ D (List.mem_toFinset.1 hp)
  · exact orClauses_card _ _ _ D (List.mem_toFinset.1 h5)

lemma F_all_cost {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)] :
    mAux n + ∑ D ∈ F_all hn w, D.card ≤ 64 * (n + 1) ^ 3 * 2 ^ n := by
  have hm : mAux n ≤ n ^ 2 * 2 ^ n := by
    unfold mAux
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    have h1 : n * ((n - 1) * 2 ^ n) = (n * (n - 1)) * 2 ^ n := by ring
    rw [h1]
    refine Nat.mul_le_mul_right (2 ^ n) ?_
    have h2 : n - 1 ≤ n := Nat.sub_le n 1
    calc n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n h2
      _ = n ^ 2 := by ring
  have h1 : ∑ D ∈ F_lvl1 hn w, D.card ≤ 12 * n ^ 3 * 2 ^ n := by
    unfold F_lvl1
    split_ifs with h
    · refine (sum_biUnion_le _ _ _).trans ?_
      have hterm : ∀ p : Fin n × Fin (2 ^ n),
          ∑ D ∈ (orClauses (wordFail hn w (rotWord hn p.1 p.2.val))
            (wordFail hn w (rotWord hn p.1 (p.2.val + 1)))
            (some (auxLit p.1 ⟨0, h⟩ p.2))).toFinset, D.card ≤ 12 * n ^ 2 := by
        intro p
        refine (orClauses_cost _ _ _).trans ?_
        rw [rLen_wordFail, rLen_wordFail]
        have h2n : 1 ≤ 2 * n := by omega
        rw [max_eq_right h2n]
        have heq : 3 * (2 * n * (2 * n)) = 12 * n ^ 2 := by ring
        omega
      refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, smul_eq_mul]
      have heq : n * 2 ^ n * (12 * n ^ 2) = 12 * n ^ 3 * 2 ^ n := by ring
      omega
    · simp only [Finset.sum_empty, Nat.zero_le]
  have h2 : ∑ D ∈ F_dbl n w, D.card ≤ 3 * n ^ 2 * 2 ^ n := by
    unfold F_dbl
    refine (sum_biUnion_le _ _ _).trans ?_
    have hterm : ∀ p : Fin n × Fin (n - 1) × Fin (2 ^ n),
        ∑ D ∈ (if h : 0 < p.2.1.val then
          (orClauses (some [auxLit (w := w) p.1 ⟨p.2.1.val - 1, by omega⟩ p.2.2])
            (some [auxLit (w := w) p.1 ⟨p.2.1.val - 1, by omega⟩ (sMod n (p.2.2.val + 2 ^ p.2.1.val))])
            (some (auxLit (w := w) p.1 p.2.1 p.2.2))).toFinset else ∅), D.card ≤ 3 := by
      intro p
      split_ifs with h
      · refine (orClauses_cost _ _ _).trans ?_
        simp only [rLen, List.length_singleton, max_self, Nat.mul_one, le_refl]
      · simp only [Finset.sum_empty, Nat.zero_le]
    refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, smul_eq_mul]
    have h3 : n * ((n - 1) * 2 ^ n) * 3 = 3 * (n * (n - 1)) * 2 ^ n := by ring
    rw [h3]
    refine Nat.mul_le_mul_right (2 ^ n) ?_
    refine Nat.mul_le_mul_left 3 ?_
    calc n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
      _ = n ^ 2 := by ring
  have h3 : ∑ D ∈ F_perm hn w, D.card ≤ 12 * n * 2 ^ n := by
    unfold F_perm
    dsimp only
    refine (sum_biUnion_le _ _ _).trans ?_
    have hterm : ∀ p : Fin n × Fin (2 ^ n),
        ∑ D ∈ (orClauses
          (halfFail hn w p.1 (sMod n (p.2.val / 2 ^ (n - min n (w + 1)) * 2 ^ (n - min n (w + 1)) +
            2 ^ (n - min n (w + 1)))))
          (halfFail hn w p.1 (sMod n (p.2.val / 2 ^ (n - min n (w + 1)) * 2 ^ (n - min n (w + 1)) +
            2 ^ (n - 1))))
          (some (Sum.inl (Sum.inr (p.1, win hn w p.1 (rotWord hn p.1 p.2.val))), true))).toFinset,
          D.card ≤ 12 := by
      intro p
      refine (orClauses_cost _ _ _).trans ?_
      have hhf : ∀ s : Fin (2 ^ n), max 1 (rLen (halfFail hn w p.1 s)) ≤ 2 :=
        fun s => max_le (by omega) (rLen_halfFail_le hn w p.1 s)
      calc 3 * (max 1 (rLen _) * max 1 (rLen _))
          ≤ 3 * (2 * 2) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul (hhf _) (hhf _))
        _ = 12 := by omega
    refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, smul_eq_mul]
    have heq : n * 2 ^ n * 12 = 12 * n * 2 ^ n := by ring
    omega
  have h4 : ∑ D ∈ F_bit hn w, D.card ≤ 12 * n * 2 ^ n := by
    unfold F_bit
    dsimp only
    refine (sum_biUnion_le _ _ _).trans ?_
    have hterm : ∀ p : Fin n × Bool,
        ∑ D ∈ (orClauses
          (halfFail hn w p.1 (if p.2 then sMod n 0 else sMod n (2 ^ (n - 1))))
          none
          (some (Sum.inl (Sum.inl p.1), p.2))).toFinset, D.card ≤ 6 := by
      intro p
      refine (orClauses_cost _ _ _).trans ?_
      have ha : max 1 (rLen (halfFail hn w p.1 (if p.2 then sMod n 0 else sMod n (2 ^ (n - 1))))) ≤ 2 :=
        max_le (by omega) (rLen_halfFail_le hn w p.1 _)
      have hb : max 1 (rLen (none : FailR (W n w))) = 1 := rfl
      rw [hb, Nat.mul_one]
      omega
    refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, smul_eq_mul]
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    calc n * 2 * 6 = 12 * n * 1 := by ring
      _ ≤ 12 * n * 2 ^ n := Nat.mul_le_mul_left (12 * n) hpow
  have h5 : ∑ D ∈ F_conf hn w, D.card ≤ 12 * 2 ^ n := by
    unfold F_conf
    dsimp only
    refine (orClauses_cost _ _ _).trans ?_
    have ha : max 1 (rLen (halfFail hn w ⟨0, hn⟩ (sMod n 0))) ≤ 2 :=
      max_le (by omega) (rLen_halfFail_le hn w _ _)
    have hb : max 1 (rLen (halfFail hn w ⟨0, hn⟩ (sMod n (2 ^ (n - 1))))) ≤ 2 :=
      max_le (by omega) (rLen_halfFail_le hn w _ _)
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
    calc 3 * (max 1 (rLen _) * max 1 (rLen _))
        ≤ 3 * (2 * 2) := Nat.mul_le_mul_left 3 (Nat.mul_le_mul ha hb)
      _ = 12 * 1 := by omega
      _ ≤ 12 * 2 ^ n := Nat.mul_le_mul_left 12 hpow
  have hunion : ∑ D ∈ F_all hn w, D.card ≤
      (∑ D ∈ F_lvl1 hn w, D.card) + (∑ D ∈ F_dbl n w, D.card) +
      (∑ D ∈ F_perm hn w, D.card) + (∑ D ∈ F_bit hn w, D.card) +
      (∑ D ∈ F_conf hn w, D.card) := by
    unfold F_all
    have u1 := sum_union_le (F_lvl1 hn w ∪ F_dbl n w ∪ F_perm hn w ∪ F_bit hn w) (F_conf hn w) Finset.card
    have u2 := sum_union_le (F_lvl1 hn w ∪ F_dbl n w ∪ F_perm hn w) (F_bit hn w) Finset.card
    have u3 := sum_union_le (F_lvl1 hn w ∪ F_dbl n w) (F_perm hn w) Finset.card
    have u4 := sum_union_le (F_lvl1 hn w) (F_dbl n w) Finset.card
    omega
  have hsum : mAux n + ∑ D ∈ F_all hn w, D.card ≤
      (12 * n ^ 3 + 4 * n ^ 2 + 24 * n + 12) * 2 ^ n := by
    have hcomb : n ^ 2 * 2 ^ n + 12 * n ^ 3 * 2 ^ n + 3 * n ^ 2 * 2 ^ n +
        12 * n * 2 ^ n + 12 * n * 2 ^ n + 12 * 2 ^ n =
        (12 * n ^ 3 + 4 * n ^ 2 + 24 * n + 12) * 2 ^ n := by ring
    omega
  refine hsum.trans (Nat.mul_le_mul_right (2 ^ n) ?_)
  have hexp : 64 * (n + 1) ^ 3 = 64 * n ^ 3 + 192 * n ^ 2 + 192 * n + 64 := by ring
  omega

def inInterval (n : ℕ) (d s m : ℕ) : Prop :=
  ∃ t : ℕ, t < 2 ^ d ∧ (s + t) % 2 ^ n = m

def auxOf {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) : Fin (mAux n) → Bool :=
  fun idx =>
    let p := (ι n).symm idx
    @decide (¬ inInterval n (p.2.1.val + 1) p.2.2.val (rotIdx hn p.1 x)) (Classical.propDecidable _)

lemma auxOf_eval {n : ℕ} (hn : 0 < n) (x : Fin n → Bool)
    (i : Fin n) (d : Fin (n - 1)) (s : Fin (2 ^ n)) :
    auxOf hn x (ι n (i, d, s)) = true ↔ ¬ inInterval n (d.val + 1) s.val (rotIdx hn i x) := by
  unfold auxOf
  rw [(ι n).symm_apply_apply]
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

lemma inInterval_succ_iff (n d s m : ℕ) :
    inInterval n (d + 1) s m ↔
      inInterval n d s m ∨ inInterval n d ((s + 2 ^ d) % 2 ^ n) m := by
  have hmod : ∀ t : ℕ, ((s + 2 ^ d) % 2 ^ n + t) % 2 ^ n = (s + (2 ^ d + t)) % 2 ^ n := fun t => by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
  constructor
  · rintro ⟨t, ht, hmt⟩
    rw [pow_succ] at ht
    by_cases hlt : t < 2 ^ d
    · exact Or.inl ⟨t, hlt, hmt⟩
    · refine Or.inr ⟨t - 2 ^ d, by omega, ?_⟩
      rw [hmod]
      have h1 : 2 ^ d + (t - 2 ^ d) = t := by omega
      rw [h1]
      exact hmt
  · rintro (⟨t, ht, hmt⟩ | ⟨t, ht, hmt⟩)
    · refine ⟨t, ?_, hmt⟩
      rw [pow_succ]; omega
    · refine ⟨2 ^ d + t, ?_, ?_⟩
      · rw [pow_succ]; omega
      · rwa [hmod] at hmt

lemma F_all_sat_forward {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)]
    {total : Vis n w → Bool} (hacc : Accepts hn w total) :
    Satisfies (Sum.elim total (auxOf hn (wordOf total))) (↑(F_all hn w) : Set _) := by
  let x := wordOf total
  let α : W n w → Bool := Sum.elim total (auxOf hn x)
  have hwf : ∀ y : Fin n → Bool, Fails α (wordFail hn w y) ↔ y ≠ x := by
    intro y
    rw [Fails_wordFail_iff]
    constructor
    · rintro (⟨k, hk⟩ | ⟨i, hi⟩) hEq
      · subst hEq
        have hxk : total (Sum.inl k) = x k := rfl
        rw [hxk] at hk
        cases hx : x k <;> rw [hx] at hk <;> cases hk
      · subst hEq
        have ht := hacc i
        rw [ht] at hi
        cases hi
    · intro hne
      have hex : ∃ k : Fin n, x k ≠ y k := by
        by_contra hall
        apply hne
        funext k
        by_contra hkn
        exact hall ⟨k, Ne.symm hkn⟩
      obtain ⟨k, hk⟩ := hex
      refine Or.inl ⟨k, ?_⟩
      change x k = !(y k)
      cases h1 : x k <;> cases h2 : y k <;> simp_all
  have hhalf : ∀ (i : Fin n) (s : Fin (2 ^ n)),
      Fails α (halfFail hn w i s) ↔ ¬ inInterval n (n - 1) s.val (rotIdx hn i x) := by
    intro i s
    unfold halfFail
    split_ifs with h
    · simp only [Fails, List.mem_singleton, exists_eq_left]
      change auxOf hn x (ι n (i, ⟨n - 2, by omega⟩, s)) = true ↔ _
      rw [auxOf_eval]
      have heq : n - 2 + 1 = n - 1 := by omega
      rw [heq]
    · rw [hwf]
      have hn1 : n - 1 = 0 := by omega
      rw [hn1]
      constructor
      · rintro hne ⟨t, ht, hmt⟩
        rw [pow_zero] at ht
        have ht0 : t = 0 := by omega
        subst ht0
        rw [Nat.add_zero] at hmt
        apply hne
        rw [← rotWord_rotIdx hn i x, ← hmt, rotWord_mod]
      · intro hnot hEq
        apply hnot
        refine ⟨0, by rw [pow_zero]; omega, ?_⟩
        rw [Nat.add_zero, ← hEq, rotIdx_rotWord]
  intro C hC
  have hCm : C ∈ F_all hn w := Finset.mem_coe.1 hC
  simp only [F_all, Finset.mem_union] at hCm
  rcases hCm with (((h1 | h2) | h3) | h4) | h5
  · unfold F_lvl1 at h1
    split_ifs at h1 with h
    · rcases Finset.mem_biUnion.1 h1 with ⟨⟨i, s⟩, _, hp⟩
      refine (orClauses_sat α _ _ _).2 (fun ⟨hA, hB⟩ => ?_) C (List.mem_toFinset.1 hp)
      rw [hwf] at hA hB
      change auxOf hn x (ι n (i, ⟨0, h⟩, s)) = true
      rw [auxOf_eval]
      rintro ⟨t, ht, hmt⟩
      rw [pow_one] at ht
      have hcases : t = 0 ∨ t = 1 := by omega
      rcases hcases with rfl | rfl
      · apply hA
        rw [← rotWord_rotIdx hn i x, ← hmt, Nat.add_zero, rotWord_mod]
      · apply hB
        rw [← rotWord_rotIdx hn i x, ← hmt, rotWord_mod]
    · exact absurd h1 (Finset.notMem_empty C)
  · rcases Finset.mem_biUnion.1 h2 with ⟨⟨i, d, s⟩, _, hp⟩
    split_ifs at hp with h
    · refine (orClauses_sat α _ _ _).2 (fun ⟨hA, hB⟩ => ?_) C (List.mem_toFinset.1 hp)
      simp only [Fails, List.mem_singleton, exists_eq_left] at hA hB
      change auxOf hn x (ι n (i, ⟨d.val - 1, by omega⟩, s)) = true at hA
      change auxOf hn x (ι n (i, ⟨d.val - 1, by omega⟩, sMod n (s.val + 2 ^ d.val))) = true at hB
      rw [auxOf_eval] at hA hB
      change auxOf hn x (ι n (i, d, s)) = true
      rw [auxOf_eval]
      dsimp only at h
      have hd1 : d.val - 1 + 1 = d.val := by omega
      rw [hd1] at hA hB
      rw [inInterval_succ_iff]
      rintro (hi1 | hi2)
      · exact hA hi1
      · exact hB hi2
    · exact absurd hp (Finset.notMem_empty C)
  · rcases Finset.mem_biUnion.1 h3 with ⟨⟨i, s⟩, _, hp⟩
    refine (orClauses_sat α _ _ _).2 (fun ⟨hA, hB⟩ => ?_) C (List.mem_toFinset.1 hp)
    rw [hhalf] at hA hB
    let K := min n (w + 1)
    let B := 2 ^ (n - K)
    let H := 2 ^ (n - 1)
    let a := (s.val / B) * B
    have h2H : 2 * H = 2 ^ n := by
      have heq : n = (n - 1) + 1 := by omega
      conv_rhs => rw [heq, pow_succ, Nat.mul_comm]
    have hBH : B ≤ H := Nat.pow_le_pow_right (by omega) (by omega)
    have haB : a + B ≤ 2 * H := by
      have hmul : B * 2 ^ K = 2 ^ n := by
        rw [← pow_add]
        have heq : n - K + K = n := by omega
        rw [heq]
      have hq : s.val / B < 2 ^ K := Nat.div_lt_of_lt_mul (by rw [hmul]; exact s.isLt)
      have hq1 : s.val / B + 1 ≤ 2 ^ K := hq
      have hle : (s.val / B + 1) * B ≤ 2 ^ K * B := Nat.mul_le_mul_right B hq1
      have h1 : (s.val / B + 1) * B = a + B := by dsimp only [a]; ring
      have h2 : 2 ^ K * B = 2 * H := by rw [Nat.mul_comm, hmul, h2H]
      omega
    have hcov := half_cover_iff (Nat.two_pow_pos (n - 1)) hBH haB
      (h2H.symm ▸ rotIdx_lt hn i x)
    have hnot : ¬ (inHalf H ((a + B) % (2 * H)) (rotIdx hn i x) ∨
        inHalf H ((a + H) % (2 * H)) (rotIdx hn i x)) := by
      rintro (hi1 | hi2)
      · exact hA (by simpa only [inHalf, inInterval, sMod, h2H] using hi1)
      · exact hB (by simpa only [inHalf, inInterval, sMod, h2H] using hi2)
    have hin : a ≤ rotIdx hn i x ∧ rotIdx hn i x < a + B := by
      by_contra hc
      exact hnot (hcov.2 hc)
    have hdiv_eq : rotIdx hn i x / B = s.val / B := by
      have h1 : (s.val / B + 1) * B = a + B := by dsimp only [a]; ring
      exact Nat.div_eq_of_lt_le hin.1 (by omega)
    have hs_idx : rotIdx hn i (rotWord hn i s.val) = s.val := by
      rw [rotIdx_rotWord, Nat.mod_eq_of_lt s.isLt]
    have hwin_eq : win hn w i x = win hn w i (rotWord hn i s.val) :=
      (win_eq_iff_rotIdx_div hn w i x (rotWord hn i s.val)).2 (by rw [hs_idx]; exact hdiv_eq)
    change total (Sum.inr (i, win hn w i (rotWord hn i s.val))) = true
    rw [← hwin_eq]
    exact hacc i
  · rcases Finset.mem_biUnion.1 h4 with ⟨⟨k, b⟩, _, hp⟩
    refine (orClauses_sat α _ _ _).2 (fun ⟨hA, _⟩ => ?_) C (List.mem_toFinset.1 hp)
    rw [hhalf] at hA
    have h2H : 2 * 2 ^ (n - 1) = 2 ^ n := by
      have heq : n = (n - 1) + 1 := by omega
      conv_rhs => rw [heq, pow_succ, Nat.mul_comm]
    have hxk : total (Sum.inl k) = decide (2 ^ (n - 1) ≤ rotIdx hn k x) := by
      have h1 := rotWord_self hn k (rotIdx_lt hn k x)
      rw [rotWord_rotIdx] at h1
      exact h1
    change total (Sum.inl k) = b
    rw [hxk]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, sMod] at hA
      have hlt : rotIdx hn k x < 2 ^ (n - 1) := by
        by_contra hge
        apply hA
        have hHpos : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
        have hHlt : 2 ^ (n - 1) < 2 ^ n := by omega
        refine ⟨rotIdx hn k x - 2 ^ (n - 1), by have := rotIdx_lt hn k x; omega, ?_⟩
        rw [Nat.mod_eq_of_lt hHlt]
        have h1 : 2 ^ (n - 1) + (rotIdx hn k x - 2 ^ (n - 1)) = rotIdx hn k x := by omega
        rw [h1, Nat.mod_eq_of_lt (rotIdx_lt hn k x)]
      exact decide_eq_false (by omega)
    · simp only [↓reduceIte, sMod, Nat.zero_mod] at hA
      have hge : 2 ^ (n - 1) ≤ rotIdx hn k x := by
        by_contra hlt
        apply hA
        refine ⟨rotIdx hn k x, by omega, ?_⟩
        rw [Nat.zero_add, Nat.mod_eq_of_lt (rotIdx_lt hn k x)]
      exact decide_eq_true hge
  · refine (orClauses_sat α _ _ _).2 (fun ⟨hA, hB⟩ => ?_) C (List.mem_toFinset.1 h5)
    rw [hhalf] at hA hB
    let i0 : Fin n := ⟨0, hn⟩
    have h2H : 2 * 2 ^ (n - 1) = 2 ^ n := by
      have heq : n = (n - 1) + 1 := by omega
      conv_rhs => rw [heq, pow_succ, Nat.mul_comm]
    by_cases hlt : rotIdx hn i0 x < 2 ^ (n - 1)
    · apply hA
      refine ⟨rotIdx hn i0 x, hlt, ?_⟩
      simp only [sMod, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt (rotIdx_lt hn i0 x)]
      rfl
    · apply hB
      have hHpos : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
      have hHlt : 2 ^ (n - 1) < 2 ^ n := by omega
      refine ⟨rotIdx hn i0 x - 2 ^ (n - 1), by have := rotIdx_lt hn i0 x; omega, ?_⟩
      simp only [sMod, Nat.mod_eq_of_lt hHlt]
      have h1 : 2 ^ (n - 1) + (rotIdx hn i0 x - 2 ^ (n - 1)) = rotIdx hn i0 x := by omega
      rw [h1, Nat.mod_eq_of_lt (rotIdx_lt hn i0 x)]

lemma F_all_sat_backward {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)]
    {total : Vis n w → Bool} {aux : Fin (mAux n) → Bool}
    (hsat : Satisfies (Sum.elim total aux) (↑(F_all hn w) : Set _)) :
    Accepts hn w total := by
  let α : W n w → Bool := Sum.elim total aux
  by_contra hnot
  unfold Accepts at hnot
  push Not at hnot
  obtain ⟨iBad, hiBad⟩ := hnot
  have hiFalse : total (Sum.inr (iBad, win hn w iBad (wordOf total))) = false := by
    cases h : total (Sum.inr (iBad, win hn w iBad (wordOf total)))
    · rfl
    · exact absurd h hiBad
  have hall_wf : ∀ y : Fin n → Bool, Fails α (wordFail hn w y) := by
    intro y
    rw [Fails_wordFail_iff]
    by_cases hEq : y = wordOf total
    · subst hEq
      exact Or.inr ⟨iBad, hiFalse⟩
    · have hex : ∃ k : Fin n, total (Sum.inl k) ≠ y k := by
        by_contra hall
        apply hEq
        funext k
        by_contra hkn
        exact hall ⟨k, Ne.symm hkn⟩
      obtain ⟨k, hk⟩ := hex
      refine Or.inl ⟨k, ?_⟩
      cases h1 : total (Sum.inl k) <;> cases h2 : y k <;> simp_all
  let i0 : Fin n := ⟨0, hn⟩
  have hmem_F : ∀ {G : Finset (Cl (W n w))}, G ⊆ F_all hn w → ∀ C ∈ G, ClauseSat α C :=
    fun hsub C hC => hsat C (Finset.mem_coe.2 (hsub hC))
  have hhalf : ∀ s : Fin (2 ^ n), Fails α (halfFail hn w i0 s) := by
    unfold halfFail
    split_ifs with h
    · have hind : ∀ (d : ℕ) (hd : d < n - 1) (s : Fin (2 ^ n)),
          α (auxLit i0 ⟨d, hd⟩ s).1 = true := by
        intro d
        induction d with
        | zero =>
          intro hd s
          have hC : ∀ C ∈ orClauses (wordFail hn w (rotWord hn i0 s.val))
              (wordFail hn w (rotWord hn i0 (s.val + 1)))
              (some (auxLit i0 ⟨0, h⟩ s)), ClauseSat α C := by
            intro C hC
            refine hsat C (Finset.mem_coe.2 ?_)
            simp only [F_all, Finset.mem_union]
            left; left; left; left
            unfold F_lvl1
            simp only [h, ↓reduceDIte]
            exact Finset.mem_biUnion.2 ⟨(i0, s), Finset.mem_univ _, List.mem_toFinset.2 hC⟩
          exact (orClauses_sat α _ _ _).1 hC ⟨hall_wf _, hall_wf _⟩
        | succ d ih =>
          intro hd s
          have hd0 : 0 < d + 1 := Nat.succ_pos d
          have hC : ∀ C ∈ orClauses
              (some [auxLit i0 ⟨d, by omega⟩ s])
              (some [auxLit i0 ⟨d, by omega⟩ (sMod n (s.val + 2 ^ (d + 1)))])
              (some (auxLit i0 ⟨d + 1, hd⟩ s)), ClauseSat α C := by
            intro C hC
            refine hsat C (Finset.mem_coe.2 ?_)
            simp only [F_all, Finset.mem_union]
            left; left; left; right
            refine Finset.mem_biUnion.2 ⟨(i0, ⟨d + 1, hd⟩, s), Finset.mem_univ _, ?_⟩
            simp only [hd0, ↓reduceDIte]
            exact List.mem_toFinset.2 hC
          have hA : Fails α (some [auxLit i0 ⟨d, by omega⟩ s]) :=
            ⟨_, List.mem_singleton_self _, ih (by omega) s⟩
          have hB : Fails α (some [auxLit i0 ⟨d, by omega⟩ (sMod n (s.val + 2 ^ (d + 1)))]) :=
            ⟨_, List.mem_singleton_self _, ih (by omega) _⟩
          exact (orClauses_sat α _ _ _).1 hC ⟨hA, hB⟩
      intro s
      exact ⟨_, List.mem_singleton_self _, hind (n - 2) (by omega) s⟩
    · intro s
      exact hall_wf _
  have hC : ∀ C ∈ orClauses (halfFail hn w i0 (sMod n 0))
      (halfFail hn w i0 (sMod n (2 ^ (n - 1)))) none, ClauseSat α C := by
    intro C hC
    refine hsat C (Finset.mem_coe.2 ?_)
    simp only [F_all, Finset.mem_union]
    right
    exact List.mem_toFinset.2 hC
  exact (orClauses_sat α _ _ _).1 hC ⟨hhalf _, hhalf _⟩

lemma up_interval {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)]
    (ρ : Vis n w → Option Bool) (i : Fin n) :
    ∀ (d : ℕ) (hd : d < n - 1) (s : Fin (2 ^ n)),
      (∀ t : ℕ, t < 2 ^ (d + 1) →
        KnownFail (seedOf ρ : Set (Lit (W n w))) (wordFail hn w (rotWord hn i (s.val + t)))) →
      auxLit i ⟨d, hd⟩ s ∈ (upStep (F_all hn w))^[d + 1] (seedOf ρ)
  | 0, hd, s, hall => by
    rw [Function.iterate_one]
    have hF : ∀ C ∈ orClauses (wordFail hn w (rotWord hn i s.val))
        (wordFail hn w (rotWord hn i (s.val + 1))) (some (auxLit i ⟨0, hd⟩ s)),
        C ∈ F_all hn w := by
      intro C hC
      simp only [F_all, Finset.mem_union]
      left; left; left; left
      unfold F_lvl1
      simp only [hd, ↓reduceDIte]
      exact Finset.mem_biUnion.2 ⟨(i, s), Finset.mem_univ _, List.mem_toFinset.2 hC⟩
    have h0 := hall 0 (by rw [pow_one]; omega)
    rw [Nat.add_zero] at h0
    have h1 := hall 1 (by rw [pow_one]; omega)
    exact orClauses_upStep_some hF h0 h1
  | d + 1, hd, s, hall => by
    have ih1 := up_interval hn w ρ i d (by omega) s fun t ht =>
      hall t (lt_trans ht (Nat.pow_lt_pow_right (by omega) (by omega)))
    have ih2 := up_interval hn w ρ i d (by omega) (sMod n (s.val + 2 ^ (d + 1))) fun t ht => by
      have hmod : rotWord hn i ((s.val + 2 ^ (d + 1)) % 2 ^ n + t) =
          rotWord hn i (s.val + (2 ^ (d + 1) + t)) := by
        unfold rotWord
        have h1 : ((s.val + 2 ^ (d + 1)) % 2 ^ n + t) % 2 ^ n =
            (s.val + (2 ^ (d + 1) + t)) % 2 ^ n := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
        rw [h1]
      dsimp only [sMod]
      rw [hmod]
      refine hall (2 ^ (d + 1) + t) ?_
      rw [pow_succ]; omega
    have hF : ∀ C ∈ orClauses
        (some [auxLit i ⟨d, by omega⟩ s])
        (some [auxLit i ⟨d, by omega⟩ (sMod n (s.val + 2 ^ (d + 1)))])
        (some (auxLit i ⟨d + 1, hd⟩ s)), C ∈ F_all hn w := by
      intro C hC
      simp only [F_all, Finset.mem_union]
      left; left; left; right
      refine Finset.mem_biUnion.2 ⟨(i, ⟨d + 1, hd⟩, s), Finset.mem_univ _, ?_⟩
      have hd0 : 0 < d + 1 := Nat.succ_pos d
      simp only [hd0, ↓reduceDIte]
      exact List.mem_toFinset.2 hC
    rw [Function.iterate_succ_apply']
    exact orClauses_upStep_some hF
      ⟨_, List.mem_singleton_self _, ih1⟩
      ⟨_, List.mem_singleton_self _, ih2⟩

lemma up_halfFail {n : ℕ} (hn : 0 < n) (w : ℕ) [DecidableEq (Vis n w)]
    (ρ : Vis n w → Option Bool) (i : Fin n) (s : Fin (2 ^ n))
    (hall : ∀ t : ℕ, t < 2 ^ (n - 1) →
      KnownFail (seedOf ρ : Set (Lit (W n w))) (wordFail hn w (rotWord hn i (s.val + t)))) :
    KnownFail ((upStep (F_all hn w))^[n - 1] (seedOf ρ)) (halfFail hn w i s) := by
  unfold halfFail
  split_ifs with h
  · have hstep := up_interval hn w ρ i (n - 2) (by omega) s (by
      have heq : n - 2 + 1 = n - 1 := by omega
      rwa [heq])
    have heq : n - 2 + 1 = n - 1 := by omega
    rw [heq] at hstep
    exact ⟨_, List.mem_singleton_self _, hstep⟩
  · have hn1 : n - 1 = 0 := by omega
    rw [hn1, Function.iterate_zero, id_eq]
    have h0 := hall 0 (by rw [hn1, pow_zero]; omega)
    rwa [Nat.add_zero] at h0

lemma word_survives_mk_true {n : ℕ} (hn : 0 < n) (w : ℕ) (ρ : Vis n w → Option Bool)
    {x : Fin n → Bool}
    (hsurv : ¬ KnownFail (seedOf ρ : Set (Lit (W n w))) (wordFail hn w x)) :
    let a : Vis n w → Bool := fun v =>
      match v with
      | Sum.inl k => x k
      | Sum.inr ip => (ρ (Sum.inr ip)).getD true
    Completion hn w ρ a := by
  rw [KnownFail_wordFail_seed_iff] at hsurv
  push Not at hsurv
  rcases hsurv with ⟨hbit, hperm⟩
  refine ⟨?_, ?_⟩
  · intro i
    have hne := hperm i
    change (ρ (Sum.inr (i, win hn w i x))).getD true = true
    cases h : ρ (Sum.inr (i, win hn w i x)) with
    | none => rfl
    | some b =>
      cases b
      · exact absurd h hne
      · rfl
  · intro v b hρv
    cases v with
    | inl k =>
      have hne := hbit k
      change x k = b
      cases hx : x k <;> cases b <;> simp_all
    | inr ip =>
      change (ρ (Sum.inr ip)).getD true = b
      rw [hρv]
      rfl

lemma word_survives_mk_false {n : ℕ} (hn : 0 < n) (w : ℕ) (ρ : Vis n w → Option Bool)
    {x : Fin n → Bool}
    (hsurv : ¬ KnownFail (seedOf ρ : Set (Lit (W n w))) (wordFail hn w x))
    (i0 : Fin n) (p0 : Fin (w + 1) → Bool)
    (hnone : ρ (Sum.inr (i0, p0)) = none) (hne : win hn w i0 x ≠ p0) :
    ∃ a : Vis n w → Bool, Completion hn w ρ a ∧ a (Sum.inr (i0, p0)) = false := by
  let _ : DecidableEq (Vis n w) := Classical.decEq _
  have hbase := word_survives_mk_true hn w ρ hsurv
  let a0 : Vis n w → Bool := fun v =>
    match v with
    | Sum.inl k => x k
    | Sum.inr ip => (ρ (Sum.inr ip)).getD true
  let a1 : Vis n w → Bool := fun v =>
    if v = Sum.inr (i0, p0) then false else a0 v
  refine ⟨a1, ⟨?_, ?_⟩, ?_⟩
  · intro i
    have hw1 : wordOf a1 = x := by
      funext k
      dsimp only [wordOf, a1, a0]
      simp only [reduceCtorEq, ↓reduceIte]
    rw [hw1]
    dsimp only [a1]
    have hneq : (Sum.inr (i, win hn w i x) : Vis n w) ≠ Sum.inr (i0, p0) := by
      intro heq
      have h1 := Sum.inr.inj heq
      have h2 := Prod.mk.inj h1
      rcases h2 with ⟨rfl, hp⟩
      exact hne hp
    simp only [hneq, ↓reduceIte]
    exact hbase.1 i
  · intro v b hρv
    have hneq : v ≠ Sum.inr (i0, p0) := by
      intro heq
      rw [heq, hnone] at hρv
      cases hρv
    dsimp only [a1]
    simp only [hneq, ↓reduceIte]
    exact hbase.2 v b hρv
  · dsimp only [a1]
    simp only [↓reduceIte]

lemma upper_bound (n w : ℕ) (hn : 0 < n) [DecidableEq (Vis n w)] :
    let F := F_all hn w
    (∀ D ∈ F, D.card ≤ 3) ∧
    (∀ total : Vis n w → Bool, Accepts hn w total ↔ ∃ aux : Fin (mAux n) → Bool,
      Satisfies (Sum.elim total aux) (↑F : Set _)) ∧
    (∀ ρ : Vis n w → Option Bool,
      let known := (upStep F)^[n] (seedOf ρ)
      ((¬ ∃ a : Vis n w → Bool, Completion hn w ρ a) ↔
        ∃ D ∈ F, ∀ l ∈ D, negL l ∈ known) ∧
      ((∃ a : Vis n w → Bool, Completion hn w ρ a) → ∀ v : Vis n w, ∀ b : Bool,
        (∀ a : Vis n w → Bool, Completion hn w ρ a → a v = b) ↔ (Sum.inl v, b) ∈ known)) ∧
    mAux n + (∑ D ∈ F, D.card) ≤ 64 * (n + 1) ^ 3 * 2 ^ n := by
  have hsat_iff : ∀ total : Vis n w → Bool, Accepts hn w total ↔ ∃ aux : Fin (mAux n) → Bool,
      Satisfies (Sum.elim total aux) (↑(F_all hn w) : Set _) := fun total =>
    ⟨fun hacc => ⟨auxOf hn (wordOf total), F_all_sat_forward hn w hacc⟩,
      fun ⟨_, hs⟩ => F_all_sat_backward hn w hs⟩
  refine ⟨F_all_card hn w, hsat_iff, ?_, F_all_cost hn w⟩
  intro ρ
  constructor
  · constructor
    · intro hno
      have hall : ∀ y : Fin n → Bool, KnownFail (seedOf ρ : Set (Lit (W n w))) (wordFail hn w y) := by
        intro y
        by_contra hsurv
        exact hno ⟨_, word_survives_mk_true hn w ρ hsurv⟩
      let i0 : Fin n := ⟨0, hn⟩
      have hA := up_halfFail hn w ρ i0 (sMod n 0) fun _ _ => hall _
      have hB := up_halfFail hn w ρ i0 (sMod n (2 ^ (n - 1))) fun _ _ => hall _
      have hF : ∀ C ∈ orClauses (halfFail hn w i0 (sMod n 0))
          (halfFail hn w i0 (sMod n (2 ^ (n - 1)))) none, C ∈ F_all hn w := by
        intro C hC
        simp only [F_all, Finset.mem_union]
        right
        exact List.mem_toFinset.2 hC
      obtain ⟨D, hDF, hDneg⟩ := orClauses_upStep_none hF hA hB
      exact ⟨D, hDF, fun l hl => upStep_iter_le (F_all hn w) (seedOf ρ) (Nat.sub_le n 1) (hDneg l hl)⟩
    · rintro ⟨D, hDF, hDneg⟩ ⟨a, hacc, hρa⟩
      obtain ⟨aux, hsat⟩ := (hsat_iff a).1 hacc
      exact upStep_conflict_false hsat (seedOf_sound hρa) n hDF hDneg
  · intro hex v b
    constructor
    · intro hforce
      cases hρv : ρ v with
      | some b' =>
        obtain ⟨a0, hacc0, hρ0⟩ := hex
        have h1 := hρ0 v b' hρv
        have h2 := hforce a0 ⟨hacc0, hρ0⟩
        have hbb : b' = b := h1.symm.trans h2
        subst hbb
        exact upStep_iter_le (F_all hn w) (seedOf ρ) (Nat.zero_le n)
          ((mem_seedOf_inl ρ v b').2 hρv)
      | none =>
        have hn_eq : n = (n - 1) + 1 := by omega
        have h2H : 2 * 2 ^ (n - 1) = 2 ^ n := by
          conv_rhs => rw [hn_eq, pow_succ, Nat.mul_comm]
        cases v with
        | inl k =>
          have hall : ∀ y : Fin n → Bool, y k = !b →
              KnownFail (seedOf ρ : Set (Lit (W n w))) (wordFail hn w y) := by
            intro y hy
            by_contra hsurv
            have hc := word_survives_mk_true hn w ρ hsurv
            have hf := hforce _ hc
            change y k = b at hf
            rw [hy] at hf
            cases b <;> cases hf
          let s := if b then sMod n 0 else sMod n (2 ^ (n - 1))
          have hA : KnownFail ((upStep (F_all hn w))^[n - 1] (seedOf ρ)) (halfFail hn w k s) := by
            refine up_halfFail hn w ρ k s fun t ht => hall _ ?_
            cases b
            · simp only [s, Bool.false_eq_true, ↓reduceIte, sMod]
              have hHpos : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
              have hHlt : 2 ^ (n - 1) < 2 ^ n := by omega
              rw [Nat.mod_eq_of_lt hHlt]
              rw [rotWord_self hn k (by omega)]
              exact decide_eq_true (by omega)
            · simp only [s, ↓reduceIte, sMod, Nat.zero_mod, Nat.zero_add]
              rw [rotWord_self hn k (by omega)]
              exact decide_eq_false (by omega)
          have hF : ∀ C ∈ orClauses (halfFail hn w k s) none (some (Sum.inl (Sum.inl k), b)),
              C ∈ F_all hn w := by
            intro C hC
            simp only [F_all, Finset.mem_union]
            left; right
            exact Finset.mem_biUnion.2 ⟨(k, b), Finset.mem_univ _, List.mem_toFinset.2 hC⟩
          exact upStep_iter_pred_succ hn (orClauses_upStep_some hF hA trivial)
        | inr ip =>
          rcases ip with ⟨i, p⟩
          obtain ⟨a0, hacc0, hρ0⟩ := hex
          let x0 := wordOf a0
          have hsurv0 : ¬ KnownFail (seedOf ρ : Set (Lit (W n w))) (wordFail hn w x0) := by
            rw [KnownFail_wordFail_seed_iff]
            rintro (⟨k, hk⟩ | ⟨j, hj⟩)
            · have h1 := hρ0 (Sum.inl k) (!(x0 k)) hk
              change x0 k = !(x0 k) at h1
              cases hx : x0 k <;> rw [hx] at h1 <;> cases h1
            · have h1 := hρ0 (Sum.inr (j, win hn w j x0)) false hj
              have h2 := hacc0 j
              rw [h2] at h1
              cases h1
          have hb_true : b = true := by
            have hc := word_survives_mk_true hn w ρ hsurv0
            have hf := hforce _ hc
            change (ρ (Sum.inr (i, p))).getD true = b at hf
            rw [hρv] at hf
            exact hf.symm
          subst hb_true
          have hwin0 : win hn w i x0 = p := by
            by_contra hne
            obtain ⟨a1, hc1, ha1⟩ := word_survives_mk_false hn w ρ hsurv0 i p hρv hne
            have hf := hforce a1 hc1
            rw [hf] at ha1
            cases ha1
          have hall : ∀ y : Fin n → Bool, win hn w i y ≠ p →
              KnownFail (seedOf ρ : Set (Lit (W n w))) (wordFail hn w y) := by
            intro y hne
            by_contra hsurv
            obtain ⟨a1, hc1, ha1⟩ := word_survives_mk_false hn w ρ hsurv i p hρv hne
            have hf := hforce a1 hc1
            rw [hf] at ha1
            cases ha1
          let K := min n (w + 1)
          let B := 2 ^ (n - K)
          let H := 2 ^ (n - 1)
          let s0 : Fin (2 ^ n) := ⟨rotIdx hn i x0, rotIdx_lt hn i x0⟩
          let a := (s0.val / B) * B
          have hBH : B ≤ H := Nat.pow_le_pow_right (by omega) (by omega)
          have haB : a + B ≤ 2 * H := by
            have hmul : B * 2 ^ K = 2 ^ n := by
              rw [← pow_add]
              have heq : n - K + K = n := by omega
              rw [heq]
            have hq : s0.val / B < 2 ^ K := Nat.div_lt_of_lt_mul (by rw [hmul]; exact s0.isLt)
            have hle : (s0.val / B + 1) * B ≤ 2 ^ K * B := Nat.mul_le_mul_right B hq
            have h1 : (s0.val / B + 1) * B = a + B := by dsimp only [a]; ring
            have h2 : 2 ^ K * B = 2 * H := by rw [Nat.mul_comm, hmul, h2H]
            omega
          have hnot_win : ∀ (m : ℕ), m < 2 * H → ¬ (a ≤ m ∧ m < a + B) →
              win hn w i (rotWord hn i m) ≠ p := by
            intro m hm hnm heq
            rw [← hwin0, win_eq_iff_rotIdx_div, rotIdx_rotWord, Nat.mod_eq_of_lt (h2H ▸ hm)] at heq
            change m / B = s0.val / B at heq
            have hBpos : 0 < B := Nat.two_pow_pos _
            have hge : a ≤ m := by
              dsimp only [a, s0]
              rw [← heq]
              exact Nat.div_mul_le_self m B
            have hlt : m < a + B := by
              dsimp only [a, s0]
              rw [← heq]
              have hdm := Nat.div_add_mod m B
              have hml := Nat.mod_lt m hBpos
              have hcomm : B * (m / B) = m / B * B := Nat.mul_comm _ _
              omega
            exact hnm ⟨hge, hlt⟩
          have hA := up_halfFail hn w ρ i (sMod n (a + B)) fun t ht => by
            let m := ((a + B) % 2 ^ n + t) % 2 ^ n
            have hm_lt : m < 2 * H := h2H.symm ▸ Nat.mod_lt _ (Nat.two_pow_pos n)
            have hinH : inHalf H ((a + B) % (2 * H)) m := ⟨t, ht, by dsimp only [m]; rw [h2H]⟩
            have hnm := (half_cover_iff (Nat.two_pow_pos (n - 1)) hBH haB hm_lt).1 (Or.inl hinH)
            have hneq := hnot_win m hm_lt hnm
            have hrw : rotWord hn i ((a + B) % 2 ^ n + t) = rotWord hn i m := by
              dsimp only [m]; rw [rotWord_mod]
            dsimp only [sMod]
            rw [hrw]
            exact hall _ hneq
          have hB := up_halfFail hn w ρ i (sMod n (a + H)) fun t ht => by
            let m := ((a + H) % 2 ^ n + t) % 2 ^ n
            have hm_lt : m < 2 * H := h2H.symm ▸ Nat.mod_lt _ (Nat.two_pow_pos n)
            have hinH : inHalf H ((a + H) % (2 * H)) m := ⟨t, ht, by dsimp only [m]; rw [h2H]⟩
            have hnm := (half_cover_iff (Nat.two_pow_pos (n - 1)) hBH haB hm_lt).1 (Or.inr hinH)
            have hneq := hnot_win m hm_lt hnm
            have hrw : rotWord hn i ((a + H) % 2 ^ n + t) = rotWord hn i m := by
              dsimp only [m]; rw [rotWord_mod]
            dsimp only [sMod]
            rw [hrw]
            exact hall _ hneq
          have hF : ∀ C ∈ orClauses (halfFail hn w i (sMod n (a + B)))
              (halfFail hn w i (sMod n (a + H))) (some (Sum.inl (Sum.inr (i, p)), true)),
              C ∈ F_all hn w := by
            intro C hC
            simp only [F_all, Finset.mem_union]
            left; left; right
            refine Finset.mem_biUnion.2 ⟨(i, s0), Finset.mem_univ _, ?_⟩
            have hw0 : win hn w i (rotWord hn i s0.val) = p := by
              dsimp only [s0]
              rw [rotWord_rotIdx]
              exact hwin0
            dsimp only [F_perm]
            rw [hw0]
            exact List.mem_toFinset.2 hC
          exact upStep_iter_pred_succ hn (orClauses_upStep_some hF hA hB)
    · intro hmem a ⟨hacc, hρa⟩
      obtain ⟨aux, hsat⟩ := (hsat_iff a).1 hacc
      exact upStep_iter_sound hsat (seedOf_sound hρa) n _ hmem

end

end PEqualNP.Outside.L_pcx_229

theorem PEqualNP.Outside.L_pcx_229 : ∀ (n w : ℕ) (hn : 0 < n),
  let V := Sum (Fin n) (Fin n × (Fin (w + 1) → Bool))
  let accepts := fun (a : V → Bool) =>
    ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true
  let enc := fun (d m : ℕ)
      (F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m)))) =>
    let step := fun S : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) =>
      S ∪ {l | ∃ D ∈ F, l ∈ D ∧ ∀ other ∈ D, other ≠ l →
        PEqualNP.Search.negLit other ∈ S}
    (∀ D ∈ F, D.card ≤ 3) ∧
    (∀ total : V → Bool, accepts total ↔ ∃ aux : Fin m → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim total aux) (↑F : Set _)) ∧
    ∀ ρ : V → Option Bool,
      let seed : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) :=
        {l | ∃ v : V, l.1 = Sum.inl v ∧ ρ v = some l.2}
      let known := (step^[d]) seed
      let completion := fun (a : V → Bool) =>
        accepts a ∧ ∀ (v : V) (b : Bool), ρ v = some b → a v = b
      ((¬ ∃ a : V → Bool, completion a) ↔
        ∃ D ∈ F, ∀ l ∈ D, PEqualNP.Search.negLit l ∈ known) ∧
      ((∃ a : V → Bool, completion a) → ∀ v : V, ∀ b : Bool,
        (∀ a : V → Bool, completion a → a v = b) ↔ (Sum.inl v, b) ∈ known)
  (∃ m F, enc n m F ∧
    m + (∑ D ∈ F, D.card) ≤ 64 * (n + 1) ^ 3 * 2 ^ n) ∧
    (n ≤ w + 1 → ∀ d m F, enc d m F → n ≤ d) := by
  intro n w hn
  dsimp only
  constructor
  · let _ : DecidableEq (PEqualNP.Outside.L_pcx_229.Vis n w) := Classical.decEq _
    obtain ⟨hcard, hsat, hprop, hcost⟩ := PEqualNP.Outside.L_pcx_229.upper_bound n w hn
    exact ⟨PEqualNP.Outside.L_pcx_229.mAux n, PEqualNP.Outside.L_pcx_229.F_all hn w,
      ⟨hcard, hsat, hprop⟩, hcost⟩
  · intro hnw d m F ⟨hcard, hsat, hprop⟩
    exact PEqualNP.Outside.L_pcx_229.lower_bound hn hnw hcard hsat fun ρ => (hprop ρ).2
