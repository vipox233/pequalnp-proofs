import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_214_aux

open PEqualNP.ProofComplexity
open scoped Classical

def Vars {n : ℕ} (C : Clause (Fin n)) : Finset (Fin n) :=
  C.image Prod.fst

def Falsifies {n : ℕ} (α : Fin n → Bool) (C : Clause (Fin n)) : Prop :=
  ∀ l ∈ C, α l.1 ≠ l.2

def AgreeOn {n : ℕ} (S : Finset (Fin n)) (α β : Fin n → Bool) : Prop :=
  ∀ v ∈ S, α v = β v

def asgnOf {n : ℕ} (T : Finset (Fin n)) : Fin n → Bool :=
  fun v => decide (v ∈ T)

lemma agreeOn_refl {n : ℕ} (S : Finset (Fin n)) (α : Fin n → Bool) :
    AgreeOn S α α := fun _ _ => rfl

lemma agreeOn_symm {n : ℕ} {S : Finset (Fin n)} {α β : Fin n → Bool}
    (h : AgreeOn S α β) : AgreeOn S β α := fun v hv => (h v hv).symm

lemma agreeOn_trans {n : ℕ} {S : Finset (Fin n)} {α β γ : Fin n → Bool}
    (h1 : AgreeOn S α β) (h2 : AgreeOn S β γ) : AgreeOn S α γ :=
  fun v hv => (h1 v hv).trans (h2 v hv)

lemma agreeOn_mono {n : ℕ} {S₁ S₂ : Finset (Fin n)} (hsub : S₁ ⊆ S₂)
    {α β : Fin n → Bool} (h : AgreeOn S₂ α β) : AgreeOn S₁ α β :=
  fun v hv => h v (hsub hv)

lemma falsifies_of_agreeOn {n : ℕ} {S : Finset (Fin n)} {C : Clause (Fin n)}
    {α β : Fin n → Bool} (hvars : Vars C ⊆ S) (hagree : AgreeOn S α β)
    (hf : Falsifies α C) : Falsifies β C := by
  intro l hl
  have hv : l.1 ∈ S := hvars (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
  rw [← hagree l.1 hv]
  exact hf l hl

lemma falsifies_iff_not_clauseSat {n : ℕ} (α : Fin n → Bool) (C : Clause (Fin n)) :
    Falsifies α C ↔ ¬ ClauseSat α C := by
  unfold Falsifies ClauseSat
  constructor
  · rintro hf ⟨l, hl, hsat⟩
    exact hf l hl hsat
  · intro hns l hl hsat
    exact hns ⟨l, hl, hsat⟩

lemma card_le_of_falsifies {n : ℕ} {S : Finset (Fin n)} {C : Clause (Fin n)}
    {α : Fin n → Bool} (hvars : Vars C ⊆ S) (hf : Falsifies α C) :
    C.card ≤ S.card := by
  have hsub : C ⊆ S.image (fun v => (v, !α v)) := by
    intro ⟨v, pol⟩ hl
    have hv : v ∈ S := hvars (Finset.mem_image.mpr ⟨(v, pol), hl, rfl⟩)
    have hne : α v ≠ pol := hf (v, pol) hl
    have hpol : (!α v) = pol := by
      cases h1 : α v <;> cases pol <;> simp_all
    exact Finset.mem_image.mpr ⟨v, hv, by rw [hpol]⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

def ValidDeriv {n : ℕ} (F : Set (Clause (Fin n))) (W D : ℕ)
    (π : List (Clause (Fin n) × ℕ)) : Prop :=
  ∀ i : Fin π.length,
    let L := π.get i
    L.1.card ≤ W ∧ L.2 ≤ D ∧
    (L.1 ∈ F ∨
      ∃ j k : Fin π.length, i < j ∧ i < k ∧
        (π.get j).2 < L.2 ∧ (π.get k).2 < L.2 ∧
        IsResolvent (π.get j).1 (π.get k).1 L.1)

lemma validDeriv_mono_D {n : ℕ} {F : Set (Clause (Fin n))} {W D₁ D₂ : ℕ}
    {π : List (Clause (Fin n) × ℕ)} (h : ValidDeriv F W D₁ π) (hle : D₁ ≤ D₂) :
    ValidDeriv F W D₂ π := by
  intro i
  rcases h i with ⟨hw, hd, hstep⟩
  exact ⟨hw, le_trans hd hle, hstep⟩

lemma validDeriv_nil {n : ℕ} (F : Set (Clause (Fin n))) (W D : ℕ) :
    ValidDeriv F W D [] := by
  intro i
  exact Fin.elim0 i

lemma validDeriv_cons_ax {n : ℕ} {F : Set (Clause (Fin n))} {W D : ℕ}
    {π : List (Clause (Fin n) × ℕ)} (hπ : ValidDeriv F W D π)
    {C : Clause (Fin n)} {d : ℕ} (hC : C ∈ F) (hW : C.card ≤ W) (hD : d ≤ D) :
    ValidDeriv F W D ((C, d) :: π) := by
  intro i
  cases i using Fin.cases with
  | zero =>
    exact ⟨hW, hD, Or.inl hC⟩
  | succ i' =>
    rcases hπ i' with ⟨hw, hd, hstep⟩
    refine ⟨hw, hd, ?_⟩
    rcases hstep with hax | ⟨j, k, hij, hik, hdj, hdk, hres⟩
    · exact Or.inl hax
    · exact Or.inr ⟨j.succ, k.succ, Fin.succ_lt_succ_iff.mpr hij, Fin.succ_lt_succ_iff.mpr hik,
        hdj, hdk, hres⟩

lemma validDeriv_cons_res {n : ℕ} {F : Set (Clause (Fin n))} {W D : ℕ}
    {π : List (Clause (Fin n) × ℕ)} (hπ : ValidDeriv F W D π)
    {p₁ p₂ : Clause (Fin n) × ℕ} (hp₁ : p₁ ∈ π) (hp₂ : p₂ ∈ π)
    {R : Clause (Fin n)} {d : ℕ} (hW : R.card ≤ W) (hD : d ≤ D)
    (hd₁ : p₁.2 < d) (hd₂ : p₂.2 < d) (hres : IsResolvent p₁.1 p₂.1 R) :
    ValidDeriv F W D ((R, d) :: π) := by
  intro i
  cases i using Fin.cases with
  | zero =>
    rcases List.mem_iff_get.mp hp₁ with ⟨j, rfl⟩
    rcases List.mem_iff_get.mp hp₂ with ⟨k, rfl⟩
    exact ⟨hW, hD, Or.inr ⟨j.succ, k.succ, Fin.succ_pos j, Fin.succ_pos k, hd₁, hd₂, hres⟩⟩
  | succ i' =>
    rcases hπ i' with ⟨hw, hd, hstep⟩
    refine ⟨hw, hd, ?_⟩
    rcases hstep with hax | ⟨j, k, hij, hik, hdj, hdk, hres'⟩
    · exact Or.inl hax
    · exact Or.inr ⟨j.succ, k.succ, Fin.succ_lt_succ_iff.mpr hij, Fin.succ_lt_succ_iff.mpr hik,
        hdj, hdk, hres'⟩

lemma validDeriv_append {n : ℕ} {F : Set (Clause (Fin n))} {W D : ℕ}
    {π₁ π₂ : List (Clause (Fin n) × ℕ)}
    (h1 : ValidDeriv F W D π₁) (h2 : ValidDeriv F W D π₂) :
    ValidDeriv F W D (π₁ ++ π₂) := by
  intro i
  by_cases hi : i.val < π₁.length
  · have hget : (π₁ ++ π₂).get i = π₁.get ⟨i.val, hi⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_left hi]
    rw [hget]
    rcases h1 ⟨i.val, hi⟩ with ⟨hw, hd, hstep⟩
    refine ⟨hw, hd, ?_⟩
    rcases hstep with hax | ⟨j, k, hij, hik, hdj, hdk, hres⟩
    · exact Or.inl hax
    · let j' : Fin (π₁ ++ π₂).length := ⟨j.val, by simp [Nat.lt_add_right _ j.isLt]⟩
      let k' : Fin (π₁ ++ π₂).length := ⟨k.val, by simp [Nat.lt_add_right _ k.isLt]⟩
      have hj' : (π₁ ++ π₂).get j' = π₁.get j := by
        simp [j', List.get_eq_getElem, List.getElem_append_left j.isLt]
      have hk' : (π₁ ++ π₂).get k' = π₁.get k := by
        simp [k', List.get_eq_getElem, List.getElem_append_left k.isLt]
      refine Or.inr ⟨j', k', hij, hik, ?_, ?_, ?_⟩
      · rwa [hj']
      · rwa [hk']
      · rwa [hj', hk']
  · have hge : π₁.length ≤ i.val := Nat.not_lt.mp hi
    have hi2 : i.val - π₁.length < π₂.length := by
      have := i.isLt
      simp only [List.length_append] at this
      omega
    have hget : (π₁ ++ π₂).get i = π₂.get ⟨i.val - π₁.length, hi2⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_right hge]
    rw [hget]
    rcases h2 ⟨i.val - π₁.length, hi2⟩ with ⟨hw, hd, hstep⟩
    refine ⟨hw, hd, ?_⟩
    rcases hstep with hax | ⟨j, k, hij, hik, hdj, hdk, hres⟩
    · exact Or.inl hax
    · let j' : Fin (π₁ ++ π₂).length := ⟨π₁.length + j.val, by simp⟩
      let k' : Fin (π₁ ++ π₂).length := ⟨π₁.length + k.val, by simp⟩
      have hj' : (π₁ ++ π₂).get j' = π₂.get j := by
        simp [j', List.get_eq_getElem, List.getElem_append_right (Nat.le_add_right _ _)]
      have hk' : (π₁ ++ π₂).get k' = π₂.get k := by
        simp [k', List.get_eq_getElem, List.getElem_append_right (Nat.le_add_right _ _)]
      have hij' : i < j' := by
        change i.val < π₁.length + j.val
        change i.val - π₁.length < j.val at hij
        omega
      have hik' : i < k' := by
        change i.val < π₁.length + k.val
        change i.val - π₁.length < k.val at hik
        omega
      refine Or.inr ⟨j', k', hij', hik', ?_, ?_, ?_⟩
      · rwa [hj']
      · rwa [hk']
      · rwa [hj', hk']

lemma validDeriv_isDerivation {n : ℕ} {F : Set (Clause (Fin n))} {W D : ℕ}
    {π : List (Clause (Fin n) × ℕ)} (h : ValidDeriv F W D π) :
    IsDerivation F (π.map Prod.fst) := by
  induction π with
  | nil =>
    exact IsDerivation.nil
  | cons L π' ih =>
    have hπ' : ValidDeriv F W D π' := by
      intro i
      rcases h i.succ with ⟨hw, hd, hstep⟩
      refine ⟨hw, hd, ?_⟩
      rcases hstep with hax | ⟨j, k, hij, hik, hdj, hdk, hres⟩
      · exact Or.inl hax
      · cases j using Fin.cases with
        | zero => exact absurd hij (Fin.not_lt_zero _)
        | succ j' =>
          cases k using Fin.cases with
          | zero => exact absurd hik (Fin.not_lt_zero _)
          | succ k' =>
            exact Or.inr ⟨j', k', Fin.succ_lt_succ_iff.mp hij, Fin.succ_lt_succ_iff.mp hik,
              hdj, hdk, hres⟩
    have hder' : IsDerivation F (π'.map Prod.fst) := ih hπ'
    rcases h ⟨0, Nat.zero_lt_succ _⟩ with ⟨_, _, hstep⟩
    simp only [List.map_cons]
    rcases hstep with hax | ⟨j, k, hij, hik, _, _, hres⟩
    · exact IsDerivation.ax hder' hax
    · cases j using Fin.cases with
      | zero => exact absurd hij (lt_irrefl _)
      | succ j' =>
        cases k using Fin.cases with
        | zero => exact absurd hik (lt_irrefl _)
        | succ k' =>
          have hjmem : (π'.get j').1 ∈ π'.map Prod.fst :=
            List.mem_map.mpr ⟨π'.get j', List.get_mem π' j', rfl⟩
          have hkmem : (π'.get k').1 ∈ π'.map Prod.fst :=
            List.mem_map.mpr ⟨π'.get k', List.get_mem π' k', rfl⟩
          exact IsDerivation.res hder' hjmem hkmem hres

lemma extend_over_vars {n : ℕ} {F : Set (Clause (Fin n))} {W D D_all bCost : ℕ}
    (S : Finset (Fin n)) :
    ∀ (B : Finset (Fin n)), Disjoint B S → (B ∪ S).card ≤ W → D + S.card ≤ D_all →
    ∀ (α : Fin n → Bool) (π₀ : List (Clause (Fin n) × ℕ)),
      ValidDeriv F W D_all π₀ →
      (∀ (π : List (Clause (Fin n) × ℕ)) (β : Fin n → Bool),
        ValidDeriv F W D_all π → (∀ x ∈ π₀, x ∈ π) → AgreeOn B α β →
        ∃ π' : List (Clause (Fin n) × ℕ),
          ValidDeriv F W D_all π' ∧
          π'.length ≤ π.length + bCost ∧
          (∀ x ∈ π, x ∈ π') ∧
          ∃ p ∈ π', Vars p.1 ⊆ B ∪ S ∧ Falsifies β p.1 ∧ p.2 ≤ D) →
      ∃ π₁ : List (Clause (Fin n) × ℕ),
        ValidDeriv F W D_all π₁ ∧
        π₁.length ≤ π₀.length + ((bCost + 1) * 2 ^ S.card - 1) ∧
        (∀ x ∈ π₀, x ∈ π₁) ∧
        ∃ p ∈ π₁, Vars p.1 ⊆ B ∧ Falsifies α p.1 ∧ p.2 ≤ D + S.card := by
  induction S using Finset.induction_on with
  | empty =>
    intro B _ _ _ α π₀ hπ₀ hbase
    rcases hbase π₀ α hπ₀ (fun _ hx => hx) (agreeOn_refl B α) with
      ⟨π', hπ', hlen, hsub, p, hp, hvars, hf, hd⟩
    refine ⟨π', hπ', ?_, hsub, p, hp, ?_, hf, ?_⟩
    · simpa using hlen
    · simpa using hvars
    · simpa using hd
  | @insert v S' hvS ih =>
    intro B hdisj hW hDall α π₀ hπ₀ hbase
    have hvB : v ∉ B := (Finset.disjoint_right.mp hdisj) (Finset.mem_insert_self v S')
    let B' : Finset (Fin n) := insert v B
    have hdisj' : Disjoint B' S' := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      rcases Finset.mem_insert.mp hu1 with rfl | huB
      · exact hvS hu2
      · exact (Finset.disjoint_left.mp hdisj) huB (Finset.mem_insert_of_mem hu2)
    have hunion : B' ∪ S' = B ∪ insert v S' := by
      ext u
      simp [B']
    have hW' : (B' ∪ S').card ≤ W := by
      rw [hunion]; exact hW
    have hcard : (insert v S').card = S'.card + 1 := Finset.card_insert_of_notMem hvS
    have hDall' : D + S'.card ≤ D_all := by omega
    let α₀ : Fin n → Bool := Function.update α v false
    let α₁ : Fin n → Bool := Function.update α v true
    have hbase0 : ∀ (π : List (Clause (Fin n) × ℕ)) (β : Fin n → Bool),
        ValidDeriv F W D_all π → (∀ x ∈ π₀, x ∈ π) → AgreeOn B' α₀ β →
        ∃ π' : List (Clause (Fin n) × ℕ),
          ValidDeriv F W D_all π' ∧
          π'.length ≤ π.length + bCost ∧
          (∀ x ∈ π, x ∈ π') ∧
          ∃ p ∈ π', Vars p.1 ⊆ B' ∪ S' ∧ Falsifies β p.1 ∧ p.2 ≤ D := by
      intro π β hπ hsub hagree
      have hagreeB : AgreeOn B α β := by
        intro u hu
        have huv : u ≠ v := fun h => hvB (h ▸ hu)
        have h1 : α₀ u = β u := hagree u (Finset.mem_insert_of_mem hu)
        simpa [α₀, Function.update_of_ne huv] using h1
      rcases hbase π β hπ hsub hagreeB with ⟨π', hπ', hlen, hsub', p, hp, hvars, hf, hd⟩
      refine ⟨π', hπ', hlen, hsub', p, hp, ?_, hf, hd⟩
      rwa [hunion]
    rcases ih B' hdisj' hW' hDall' α₀ π₀ hπ₀ hbase0 with
      ⟨π₁, hπ₁, hlen1, hsub1, p₀, hp₀, hvars0, hf0, hd0⟩
    have hbase1 : ∀ (π : List (Clause (Fin n) × ℕ)) (β : Fin n → Bool),
        ValidDeriv F W D_all π → (∀ x ∈ π₁, x ∈ π) → AgreeOn B' α₁ β →
        ∃ π' : List (Clause (Fin n) × ℕ),
          ValidDeriv F W D_all π' ∧
          π'.length ≤ π.length + bCost ∧
          (∀ x ∈ π, x ∈ π') ∧
          ∃ p ∈ π', Vars p.1 ⊆ B' ∪ S' ∧ Falsifies β p.1 ∧ p.2 ≤ D := by
      intro π β hπ hsub hagree
      have hagreeB : AgreeOn B α β := by
        intro u hu
        have huv : u ≠ v := fun h => hvB (h ▸ hu)
        have h1 : α₁ u = β u := hagree u (Finset.mem_insert_of_mem hu)
        simpa [α₁, Function.update_of_ne huv] using h1
      have hsub0 : ∀ x ∈ π₀, x ∈ π := fun x hx => hsub x (hsub1 x hx)
      rcases hbase π β hπ hsub0 hagreeB with ⟨π', hπ', hlen, hsub', p, hp, hvars, hf, hd⟩
      refine ⟨π', hπ', hlen, hsub', p, hp, ?_, hf, hd⟩
      rwa [hunion]
    rcases ih B' hdisj' hW' hDall' α₁ π₁ hπ₁ hbase1 with
      ⟨π₂, hπ₂, hlen2, hsub2, p₁, hp₁, hvars1, hf1, hd1⟩
    have hsub02 : ∀ x ∈ π₀, x ∈ π₂ := fun x hx => hsub2 x (hsub1 x hx)
    have hp₀2 : p₀ ∈ π₂ := hsub2 p₀ hp₀
    have hbound2 : π₂.length + 1 ≤ π₀.length + ((bCost + 1) * 2 ^ (insert v S').card - 1) := by
      rw [hcard, pow_succ]
      have hmul : (bCost + 1) * (2 ^ S'.card * 2) = 2 * ((bCost + 1) * 2 ^ S'.card) := by ring
      rw [hmul]
      have hpos : 1 ≤ (bCost + 1) * 2 ^ S'.card := by
        have h1 : 1 ≤ 2 ^ S'.card := Nat.one_le_two_pow
        have h2 : 1 ≤ bCost + 1 := Nat.succ_pos bCost
        exact Nat.mul_le_mul h2 h1
      omega
    have hneg0 : (v, false) ∉ p₀.1 := by
      intro hmem
      have := hf0 (v, false) hmem
      simp [α₀] at this
    have hpos1 : (v, true) ∉ p₁.1 := by
      intro hmem
      have := hf1 (v, true) hmem
      simp [α₁] at this
    by_cases h0 : (v, true) ∈ p₀.1
    · by_cases h1 : (v, false) ∈ p₁.1
      · let R : Clause (Fin n) := p₀.1.erase (v, true) ∪ p₁.1.erase (v, false)
        let dR : ℕ := max p₀.2 p₁.2 + 1
        have hres : IsResolvent p₀.1 p₁.1 R := ⟨v, h0, h1, rfl⟩
        have hvarsR : Vars R ⊆ B := by
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨⟨u', pol⟩, hl, rfl⟩
          rcases Finset.mem_union.mp hl with hl0 | hl1
          · have hmem0 : (u', pol) ∈ p₀.1 := Finset.mem_of_mem_erase hl0
            have hne0 : (u', pol) ≠ (v, true) := Finset.ne_of_mem_erase hl0
            have huB' : u' ∈ B' := hvars0 (Finset.mem_image.mpr ⟨(u', pol), hmem0, rfl⟩)
            rcases Finset.mem_insert.mp huB' with rfl | huB
            · cases pol
              · exact absurd hmem0 hneg0
              · exact absurd rfl hne0
            · exact huB
          · have hmem1 : (u', pol) ∈ p₁.1 := Finset.mem_of_mem_erase hl1
            have hne1 : (u', pol) ≠ (v, false) := Finset.ne_of_mem_erase hl1
            have huB' : u' ∈ B' := hvars1 (Finset.mem_image.mpr ⟨(u', pol), hmem1, rfl⟩)
            rcases Finset.mem_insert.mp huB' with rfl | huB
            · cases pol
              · exact absurd rfl hne1
              · exact absurd hmem1 hpos1
            · exact huB
        have hfR : Falsifies α R := by
          intro l hl
          have hlB : l.1 ∈ B := hvarsR (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
          have hne : l.1 ≠ v := fun h => hvB (h ▸ hlB)
          rcases Finset.mem_union.mp hl with hl0 | hl1
          · have := hf0 l (Finset.mem_of_mem_erase hl0)
            simpa [α₀, Function.update_of_ne hne] using this
          · have := hf1 l (Finset.mem_of_mem_erase hl1)
            simpa [α₁, Function.update_of_ne hne] using this
        have hWR : R.card ≤ W := by
          have h1 : R.card ≤ B.card := card_le_of_falsifies hvarsR hfR
          have h2 : B.card ≤ (B ∪ insert v S').card := Finset.card_le_card Finset.subset_union_left
          exact le_trans (le_trans h1 h2) hW
        have hdR_le : dR ≤ D + (insert v S').card := by
          rw [hcard]; omega
        have hdR_all : dR ≤ D_all := le_trans hdR_le hDall
        have hπ3 : ValidDeriv F W D_all ((R, dR) :: π₂) :=
          validDeriv_cons_res hπ₂ hp₀2 hp₁ hWR hdR_all (by omega) (by omega) hres
        refine ⟨(R, dR) :: π₂, hπ3, ?_, fun x hx => List.mem_cons_of_mem _ (hsub02 x hx),
          (R, dR), List.mem_cons_self, hvarsR, hfR, hdR_le⟩
        simpa using hbound2
      · have hvars1B : Vars p₁.1 ⊆ B := by
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨⟨u', pol⟩, hl, rfl⟩
          have huB' : u' ∈ B' := hvars1 (Finset.mem_image.mpr ⟨(u', pol), hl, rfl⟩)
          rcases Finset.mem_insert.mp huB' with rfl | huB
          · cases pol
            · exact absurd hl h1
            · exact absurd hl hpos1
          · exact huB
        have hf1α : Falsifies α p₁.1 := by
          intro l hl
          have hlB : l.1 ∈ B := hvars1B (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
          have hne : l.1 ≠ v := fun h => hvB (h ▸ hlB)
          have := hf1 l hl
          simpa [α₁, Function.update_of_ne hne] using this
        refine ⟨π₂, hπ₂, by omega, hsub02, p₁, hp₁, hvars1B, hf1α, by rw [hcard]; omega⟩
    · have hvars0B : Vars p₀.1 ⊆ B := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨⟨u', pol⟩, hl, rfl⟩
        have huB' : u' ∈ B' := hvars0 (Finset.mem_image.mpr ⟨(u', pol), hl, rfl⟩)
        rcases Finset.mem_insert.mp huB' with rfl | huB
        · cases pol
          · exact absurd hl hneg0
          · exact absurd hl h0
        · exact huB
      have hf0α : Falsifies α p₀.1 := by
        intro l hl
        have hlB : l.1 ∈ B := hvars0B (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
        have hne : l.1 ≠ v := fun h => hvB (h ▸ hlB)
        have := hf0 l hl
        simpa [α₀, Function.update_of_ne hne] using this
      refine ⟨π₂, hπ₂, by omega, hsub02, p₀, hp₀2, hvars0B, hf0α, by rw [hcard]; omega⟩

lemma memoize_list {n : ℕ} {F : Set (Clause (Fin n))} {W D_all stepCost : ℕ}
    (B : Finset (Fin n)) (P : (Fin n → Bool) → Prop)
    (ts : List (Finset (Fin n)))
    (π₀ : List (Clause (Fin n) × ℕ)) (hπ₀ : ValidDeriv F W D_all π₀)
    (hstep : ∀ (T : Finset (Fin n)) (π : List (Clause (Fin n) × ℕ)),
      T ∈ ts → ValidDeriv F W D_all π → (∀ x ∈ π₀, x ∈ π) → P (asgnOf T) →
      ∃ π' : List (Clause (Fin n) × ℕ),
        ValidDeriv F W D_all π' ∧
        π'.length ≤ π.length + stepCost ∧
        (∀ x ∈ π, x ∈ π') ∧
        ∃ p ∈ π', Vars p.1 ⊆ B ∧ Falsifies (asgnOf T) p.1) :
    ∃ π₁ : List (Clause (Fin n) × ℕ),
      ValidDeriv F W D_all π₁ ∧
      π₁.length ≤ π₀.length + ts.length * stepCost ∧
      (∀ x ∈ π₀, x ∈ π₁) ∧
      ∀ T ∈ ts, P (asgnOf T) → ∃ p ∈ π₁, Vars p.1 ⊆ B ∧ Falsifies (asgnOf T) p.1 := by
  induction ts with
  | nil =>
    exact ⟨π₀, hπ₀, by simp, fun _ hx => hx, fun _ h => absurd h List.not_mem_nil⟩
  | cons T ts' ih =>
    have hstep' : ∀ (T' : Finset (Fin n)) (π : List (Clause (Fin n) × ℕ)),
        T' ∈ ts' → ValidDeriv F W D_all π → (∀ x ∈ π₀, x ∈ π) → P (asgnOf T') →
        ∃ π' : List (Clause (Fin n) × ℕ),
          ValidDeriv F W D_all π' ∧
          π'.length ≤ π.length + stepCost ∧
          (∀ x ∈ π, x ∈ π') ∧
          ∃ p ∈ π', Vars p.1 ⊆ B ∧ Falsifies (asgnOf T') p.1 :=
      fun T' π hT' hπ hsub hP => hstep T' π (List.mem_cons_of_mem T hT') hπ hsub hP
    rcases ih hstep' with ⟨π₁, hπ₁, hlen1, hsub1, hmem1⟩
    by_cases hPT : P (asgnOf T)
    · rcases hstep T π₁ List.mem_cons_self hπ₁ hsub1 hPT with
        ⟨π₂, hπ₂, hlen2, hsub2, pT, hpT, hvarsT, hfT⟩
      refine ⟨π₂, hπ₂, ?_, fun x hx => hsub2 x (hsub1 x hx), ?_⟩
      · simp only [List.length_cons, Nat.succ_mul]
        omega
      · intro T' hT' hPT'
        rcases List.mem_cons.mp hT' with rfl | hT''
        · exact ⟨pT, hpT, hvarsT, hfT⟩
        · rcases hmem1 T' hT'' hPT' with ⟨p, hp, hvars, hf⟩
          exact ⟨p, hsub2 p hp, hvars, hf⟩
    · refine ⟨π₁, hπ₁, ?_, hsub1, ?_⟩
      · simp only [List.length_cons, Nat.succ_mul]
        omega
      · intro T' hT' hPT'
        rcases List.mem_cons.mp hT' with rfl | hT''
        · exact absurd hPT' hPT
        · exact hmem1 T' hT'' hPT'

lemma prefix_split {p l : List Bool} (hlt : p.length < l.length) (hpre : List.IsPrefix p l) :
    List.IsPrefix (p ++ [false]) l ∨ List.IsPrefix (p ++ [true]) l := by
  rcases hpre with ⟨t, rfl⟩
  cases t with
  | nil => simp at hlt
  | cons b t' =>
    cases b
    · exact Or.inl ⟨t', by simp⟩
    · exact Or.inr ⟨t', by simp⟩

lemma prefix_append_disjoint {p l : List Bool}
    (h0 : List.IsPrefix (p ++ [false]) l) (h1 : List.IsPrefix (p ++ [true]) l) : False := by
  rcases h0 with ⟨t0, ht0⟩
  rcases h1 with ⟨t1, ht1⟩
  have heq : p ++ ([false] ++ t0) = p ++ ([true] ++ t1) := by
    simpa [List.append_assoc] using ht0.trans ht1.symm
  have hcons := List.append_cancel_left heq
  simp at hcons

lemma prefix_of_append {p l : List Bool} {b : Bool}
    (h : List.IsPrefix (p ++ [b]) l) : List.IsPrefix p l := by
  rcases h with ⟨t, rfl⟩
  exact ⟨b :: t, by simp⟩

lemma card_filter_eq_nat_card {n : ℕ} (P : Fin n → Prop) :
    (Finset.univ.filter P).card = Nat.card {v : Fin n // P v} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma double_count_three {n : ℕ} (A B C : Finset (Fin n))
    (hcov : ∀ v ∈ A ∪ B ∪ C, (v ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ v ∈ C) ∨ (v ∈ B ∧ v ∈ C)) :
    2 * (A ∪ B ∪ C).card ≤ A.card + B.card + C.card := by
  let U := A ∪ B ∪ C
  have hsum : ∀ X : Finset (Fin n), X ⊆ U →
      X.card = ∑ v ∈ U, (if v ∈ X then 1 else 0) := by
    intro X hX
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun hv => ⟨hX hv, hv⟩, fun hv => hv.2⟩
  have hA : A ⊆ U := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hB : B ⊆ U := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hC : C ⊆ U := Finset.subset_union_right
  rw [hsum A hA, hsum B hB, hsum C hC, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have h2U : 2 * U.card = ∑ _v ∈ U, (2 : ℕ) := by
    simp [mul_comm]
  rw [h2U]
  refine Finset.sum_le_sum fun v hv => ?_
  rcases hcov v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

lemma main_proof (n m h a b : ℕ) (clause : Fin m → Clause (Fin n))
    (addr : Fin m → List Bool)
    (haddr : ∀ i, (addr i).length = h)
    (hleaf : ∀ leaf : List Bool, leaf.length = h →
      Nat.card {v : Fin n // ∃ i, List.IsPrefix leaf (addr i) ∧ ∃ sign, (v, sign) ∈ clause i} ≤ a)
    (hbnd : ∀ p : List Bool, p.length ≤ h →
      Nat.card {v : Fin n //
        (∃ i, List.IsPrefix p (addr i) ∧ ∃ sign, (v, sign) ∈ clause i) ∧
        (∃ j, ¬ List.IsPrefix p (addr j) ∧ ∃ sign, (v, sign) ∈ clause j)} ≤ b)
    (hunsat : ¬ Satisfiable (Set.range clause)) :
    let W := max a (3 * b / 2)
    ∃ π : List (Clause (Fin n) × ℕ),
      IsRefutation (Set.range clause) (π.map Prod.fst) ∧
      π.length ≤ 2 ^ (h + W + 2) ∧
      ValidDeriv (Set.range clause) W (a + b * h) π := by
  let F : Set (Clause (Fin n)) := Set.range clause
  let W : ℕ := max a (3 * b / 2)
  let occurs : Fin m → Fin n → Prop := fun i v => ∃ sign, (v, sign) ∈ clause i
  let inside : List Bool → Fin n → Prop := fun p v => ∃ i, List.IsPrefix p (addr i) ∧ occurs i v
  let outside : List Bool → Fin n → Prop := fun p v => ∃ j, ¬ List.IsPrefix p (addr j) ∧ occurs j v
  let InSet : List Bool → Finset (Fin n) := fun p => Finset.univ.filter (fun v => inside p v)
  let Bnd : List Bool → Finset (Fin n) := fun p => Finset.univ.filter (fun v => inside p v ∧ outside p v)
  let SubF : List Bool → Set (Clause (Fin n)) :=
    fun p => {C | ∃ i : Fin m, List.IsPrefix p (addr i) ∧ C = clause i}
  let Feasible : List Bool → (Fin n → Bool) → Prop :=
    fun p α => ∃ β : Fin n → Bool, AgreeOn (Bnd p) α β ∧ Satisfies β (SubF p)
  have hIn_card : ∀ leaf : List Bool, leaf.length = h → (InSet leaf).card ≤ a := by
    intro leaf hl
    have heq : (InSet leaf).card = Nat.card {v : Fin n // inside leaf v} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [heq]
    exact hleaf leaf hl
  have hBnd_card : ∀ p : List Bool, p.length ≤ h → (Bnd p).card ≤ b := by
    intro p hp
    have heq : (Bnd p).card = Nat.card {v : Fin n // inside p v ∧ outside p v} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [heq]
    exact hbnd p hp
  have hBnd_sub_In : ∀ p : List Bool, Bnd p ⊆ InSet p := by
    intro p v hv
    simp only [Bnd, InSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.1
  have hFeas_congr : ∀ (p : List Bool) {α β : Fin n → Bool},
      AgreeOn (Bnd p) α β → (Feasible p α ↔ Feasible p β) := by
    intro p α β hagree
    constructor
    · rintro ⟨γ, hγ, hsat⟩
      exact ⟨γ, agreeOn_trans (agreeOn_symm hagree) hγ, hsat⟩
    · rintro ⟨γ, hγ, hsat⟩
      exact ⟨γ, agreeOn_trans hagree hγ, hsat⟩
  have hglue : ∀ (p : List Bool), p.length < h → ∀ (α : Fin n → Bool),
      Feasible (p ++ [false]) α → Feasible (p ++ [true]) α → Feasible p α := by
    intro p hlt α ⟨β₀, hβ₀_ag, hβ₀_sat⟩ ⟨β₁, hβ₁_ag, hβ₁_sat⟩
    let p₀ := p ++ [false]
    let p₁ := p ++ [true]
    let β : Fin n → Bool := fun v =>
      if v ∈ InSet p₀ then β₀ v else if v ∈ InSet p₁ then β₁ v else α v
    have hshared : ∀ v : Fin n, v ∈ InSet p₀ → v ∈ InSet p₁ → v ∈ Bnd p₀ ∧ v ∈ Bnd p₁ := by
      intro v hv0 hv1
      simp only [InSet, Bnd, Finset.mem_filter, Finset.mem_univ, true_and] at hv0 hv1 ⊢
      rcases hv0 with ⟨i0, hi0, ho0⟩
      rcases hv1 with ⟨i1, hi1, ho1⟩
      refine ⟨⟨⟨i0, hi0, ho0⟩, ⟨i1, fun h => prefix_append_disjoint h hi1, ho1⟩⟩,
        ⟨⟨i1, hi1, ho1⟩, ⟨i0, fun h => prefix_append_disjoint hi0 h, ho0⟩⟩⟩
    refine ⟨β, ?_, ?_⟩
    · intro v hv
      simp only [Bnd, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rcases hv with ⟨_, ⟨j, hj, hoj⟩⟩
      by_cases hv0 : v ∈ InSet p₀
      · have hvB0 : v ∈ Bnd p₀ := by
          simp only [InSet, Bnd, Finset.mem_filter, Finset.mem_univ, true_and] at hv0 ⊢
          exact ⟨hv0, ⟨j, fun h => hj (prefix_of_append h), hoj⟩⟩
        simp only [β, hv0, ↓reduceIte]
        exact hβ₀_ag v hvB0
      · by_cases hv1 : v ∈ InSet p₁
        · have hvB1 : v ∈ Bnd p₁ := by
            simp only [InSet, Bnd, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 ⊢
            exact ⟨hv1, ⟨j, fun h => hj (prefix_of_append h), hoj⟩⟩
          simp only [β, hv0, hv1, ↓reduceIte]
          exact hβ₁_ag v hvB1
        · simp [β, hv0, hv1]
    · rintro C ⟨i, hi, rfl⟩
      have hlen_i : p.length < (addr i).length := by rw [haddr i]; exact hlt
      rcases prefix_split hlen_i hi with hi0 | hi1
      · rcases hβ₀_sat (clause i) ⟨i, hi0, rfl⟩ with ⟨l, hl, hsat⟩
        refine ⟨l, hl, ?_⟩
        have hl0 : l.1 ∈ InSet p₀ := by
          simp only [InSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, hi0, l.2, hl⟩
        simp [β, hl0, hsat]
      · rcases hβ₁_sat (clause i) ⟨i, hi1, rfl⟩ with ⟨l, hl, hsat⟩
        refine ⟨l, hl, ?_⟩
        have hl1 : l.1 ∈ InSet p₁ := by
          simp only [InSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, hi1, l.2, hl⟩
        by_cases hl0 : l.1 ∈ InSet p₀
        · rcases hshared l.1 hl0 hl1 with ⟨hB0, hB1⟩
          have heq : β₀ l.1 = β₁ l.1 := (hβ₀_ag l.1 hB0).symm.trans (hβ₁_ag l.1 hB1)
          simp [β, hl0, heq, hsat]
        · simp [β, hl0, hl1, hsat]
  have htree : ∀ (r : ℕ) (p : List Bool), p.length + r = h →
      ∃ π : List (Clause (Fin n) × ℕ),
        ValidDeriv F W (a + b * r) π ∧
        π.length ≤ 2 ^ (r + W + 2) - 2 ^ W ∧
        ∀ α : Fin n → Bool, ¬ Feasible p α →
          ∃ q ∈ π, Vars q.1 ⊆ Bnd p ∧ Falsifies α q.1 := by
    intro r
    induction r with
    | zero =>
      intro p hlen
      have hph : p.length = h := by omega
      let B := Bnd p
      let S := InSet p \ Bnd p
      have hdisj : Disjoint B S := Finset.disjoint_sdiff
      have hunion : B ∪ S = InSet p := Finset.union_sdiff_of_subset (hBnd_sub_In p)
      have hIn_le_a : (InSet p).card ≤ a := hIn_card p hph
      have hW_BS : (B ∪ S).card ≤ W := by
        rw [hunion]; exact le_trans hIn_le_a (le_max_left _ _)
      have hS_le_a : 0 + S.card ≤ a := by
        have h1 : S.card ≤ (InSet p).card := Finset.card_le_card Finset.sdiff_subset
        omega
      let ts : List (Finset (Fin n)) := B.powerset.toList
      have hts_len : ts.length = 2 ^ B.card := by
        simp [ts]
      have hstep : ∀ (T : Finset (Fin n)) (π : List (Clause (Fin n) × ℕ)),
          T ∈ ts → ValidDeriv F W a π → (∀ x ∈ ([] : List (Clause (Fin n) × ℕ)), x ∈ π) →
          ¬ Feasible p (asgnOf T) →
          ∃ π' : List (Clause (Fin n) × ℕ),
            ValidDeriv F W a π' ∧
            π'.length ≤ π.length + (2 * 2 ^ S.card - 1) ∧
            (∀ x ∈ π, x ∈ π') ∧
            ∃ q ∈ π', Vars q.1 ⊆ B ∧ Falsifies (asgnOf T) q.1 := by
        intro T π _ hπ _ hnotF
        have hbase : ∀ (πc : List (Clause (Fin n) × ℕ)) (β : Fin n → Bool),
            ValidDeriv F W a πc → (∀ x ∈ π, x ∈ πc) → AgreeOn B (asgnOf T) β →
            ∃ π' : List (Clause (Fin n) × ℕ),
              ValidDeriv F W a π' ∧
              π'.length ≤ πc.length + 1 ∧
              (∀ x ∈ πc, x ∈ π') ∧
              ∃ q ∈ π', Vars q.1 ⊆ B ∪ S ∧ Falsifies β q.1 ∧ q.2 ≤ 0 := by
          intro πc β hπc _ hagree
          have hnotSat : ¬ Satisfies β (SubF p) := by
            intro hsat
            exact hnotF ⟨β, hagree, hsat⟩
          unfold Satisfies at hnotSat
          push Not at hnotSat
          rcases hnotSat with ⟨C, ⟨i, hi, rfl⟩, hnsat⟩
          have hfC : Falsifies β (clause i) := (falsifies_iff_not_clauseSat β (clause i)).mpr hnsat
          have hvarsC : Vars (clause i) ⊆ B ∪ S := by
            rw [hunion]
            intro v hv
            rcases Finset.mem_image.mp hv with ⟨⟨v', pol⟩, hl, rfl⟩
            simp only [InSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨i, hi, pol, hl⟩
          have hWC : (clause i).card ≤ W := le_trans (card_le_of_falsifies hvarsC hfC) hW_BS
          have hπ' : ValidDeriv F W a ((clause i, 0) :: πc) :=
            validDeriv_cons_ax hπc ⟨i, rfl⟩ hWC (Nat.zero_le a)
          exact ⟨(clause i, 0) :: πc, hπ', by simp, fun x hx => List.mem_cons_of_mem _ hx,
            (clause i, 0), List.mem_cons_self, hvarsC, hfC, le_rfl⟩
        rcases extend_over_vars (F := F) (W := W) (D := 0) (D_all := a) (bCost := 1)
            S B hdisj hW_BS hS_le_a (asgnOf T) π hπ hbase with
          ⟨π', hπ', hlen', hsub', q, hq, hvars, hf, _⟩
        exact ⟨π', hπ', by simpa using hlen', hsub', q, hq, hvars, hf⟩
      rcases memoize_list (F := F) (W := W) (D_all := a) (stepCost := 2 * 2 ^ S.card - 1)
          B (fun α => ¬ Feasible p α) ts [] (validDeriv_nil F W a) hstep with
        ⟨π, hπ, hlenπ, _, hmemπ⟩
      refine ⟨π, by simpa using hπ, ?_, ?_⟩
      · have hBS_card : B.card + S.card ≤ W := by
          rw [← Finset.card_union_of_disjoint hdisj]
          exact hW_BS
        have hpow : 2 ^ B.card * (2 * 2 ^ S.card - 1) ≤ 2 ^ (W + 1) := by
          have h1 : 2 * 2 ^ S.card - 1 ≤ 2 * 2 ^ S.card := Nat.sub_le _ _
          calc
            2 ^ B.card * (2 * 2 ^ S.card - 1) ≤ 2 ^ B.card * (2 * 2 ^ S.card) :=
              Nat.mul_le_mul_left _ h1
            _ = 2 ^ (B.card + S.card + 1) := by
              rw [pow_add, pow_succ]; ring
            _ ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hlen1 : π.length ≤ 2 ^ (W + 1) := by
          rw [hts_len, List.length_nil, zero_add] at hlenπ
          exact le_trans hlenπ hpow
        have hlen2 : 2 ^ (W + 1) ≤ 2 ^ (0 + W + 2) - 2 ^ W := by
          have h2 : 2 ^ (0 + W + 2) = 4 * 2 ^ W := by
            rw [zero_add, pow_add]; ring
          have h1 : 2 ^ (W + 1) = 2 * 2 ^ W := by
            rw [pow_succ]; ring
          rw [h2, h1]; omega
        exact le_trans hlen1 hlen2
      · intro α hnotF
        let T : Finset (Fin n) := B.filter (fun v => α v = true)
        have hTmem : T ∈ ts := by
          simp only [ts, Finset.mem_toList, Finset.mem_powerset]
          exact Finset.filter_subset _ _
        have hagree : AgreeOn B α (asgnOf T) := by
          intro v hv
          simp only [asgnOf, T, Finset.mem_filter, hv, true_and]
          cases α v <;> rfl
        have hnotFT : ¬ Feasible p (asgnOf T) := by
          rwa [← hFeas_congr p hagree]
        rcases hmemπ T hTmem hnotFT with ⟨q, hq, hvars, hf⟩
        exact ⟨q, hq, hvars, falsifies_of_agreeOn hvars (agreeOn_symm hagree) hf⟩
    | succ r ih =>
      intro p hlen
      have hplt : p.length < h := by omega
      let p₀ := p ++ [false]
      let p₁ := p ++ [true]
      have hlen0 : p₀.length + r = h := by simp [p₀]; omega
      have hlen1 : p₁.length + r = h := by simp [p₁]; omega
      rcases ih p₀ hlen0 with ⟨π₀, hπ₀, hπ₀len, hπ₀mem⟩
      rcases ih p₁ hlen1 with ⟨π₁, hπ₁, hπ₁len, hπ₁mem⟩
      let D_prev := a + b * r
      let D_cur := a + b * (r + 1)
      have hD_le : D_prev ≤ D_cur := by simp [D_prev, D_cur, Nat.mul_succ]
      let π_base := π₀ ++ π₁
      have hπ_base : ValidDeriv F W D_cur π_base :=
        validDeriv_mono_D (validDeriv_append hπ₀ hπ₁) hD_le
      let B := Bnd p
      let S := (Bnd p₀ ∪ Bnd p₁) \ Bnd p
      have hdisj : Disjoint B S := Finset.disjoint_sdiff
      have hunion : B ∪ S = Bnd p ∪ Bnd p₀ ∪ Bnd p₁ := by
        ext v
        simp only [B, S, Finset.mem_union, Finset.mem_sdiff]
        tauto
      have hcov3 : ∀ v ∈ Bnd p ∪ Bnd p₀ ∪ Bnd p₁,
          (v ∈ Bnd p ∧ v ∈ Bnd p₀) ∨ (v ∈ Bnd p ∧ v ∈ Bnd p₁) ∨ (v ∈ Bnd p₀ ∧ v ∈ Bnd p₁) := by
        intro v hv
        simp only [Finset.mem_union, Bnd, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        rcases hv with (⟨⟨i, hi, hoi⟩, ⟨j, hj, hoj⟩⟩ | ⟨⟨i0, hi0, ho0⟩, ⟨j0, hj0, hoj0⟩⟩) |
            ⟨⟨i1, hi1, ho1⟩, ⟨j1, hj1, hoj1⟩⟩
        · have hlen_i : p.length < (addr i).length := by rw [haddr i]; exact hplt
          rcases prefix_split hlen_i hi with hi0 | hi1
          · left
            exact ⟨⟨⟨i, hi, hoi⟩, ⟨j, hj, hoj⟩⟩,
              ⟨⟨i, hi0, hoi⟩, ⟨j, fun h => hj (prefix_of_append h), hoj⟩⟩⟩
          · right; left
            exact ⟨⟨⟨i, hi, hoi⟩, ⟨j, hj, hoj⟩⟩,
              ⟨⟨i, hi1, hoi⟩, ⟨j, fun h => hj (prefix_of_append h), hoj⟩⟩⟩
        · by_cases hjp : List.IsPrefix p (addr j0)
          · have hlen_j : p.length < (addr j0).length := by rw [haddr j0]; exact hplt
            rcases prefix_split hlen_j hjp with hj0' | hj1
            · exact absurd hj0' hj0
            · right; right
              exact ⟨⟨⟨i0, hi0, ho0⟩, ⟨j0, hj0, hoj0⟩⟩,
                ⟨⟨j0, hj1, hoj0⟩, ⟨i0, fun h => prefix_append_disjoint hi0 h, ho0⟩⟩⟩
          · left
            exact ⟨⟨⟨i0, prefix_of_append hi0, ho0⟩, ⟨j0, hjp, hoj0⟩⟩,
              ⟨⟨i0, hi0, ho0⟩, ⟨j0, hj0, hoj0⟩⟩⟩
        · by_cases hjp : List.IsPrefix p (addr j1)
          · have hlen_j : p.length < (addr j1).length := by rw [haddr j1]; exact hplt
            rcases prefix_split hlen_j hjp with hj0 | hj1'
            · right; right
              exact ⟨⟨⟨j1, hj0, hoj1⟩, ⟨i1, fun h => prefix_append_disjoint h hi1, ho1⟩⟩,
                ⟨⟨i1, hi1, ho1⟩, ⟨j1, hj1, hoj1⟩⟩⟩
            · exact absurd hj1' hj1
          · right; left
            exact ⟨⟨⟨i1, prefix_of_append hi1, ho1⟩, ⟨j1, hjp, hoj1⟩⟩,
              ⟨⟨i1, hi1, ho1⟩, ⟨j1, hj1, hoj1⟩⟩⟩
      have hW_BS : (B ∪ S).card ≤ W := by
        rw [hunion]
        have h2 := double_count_three (Bnd p) (Bnd p₀) (Bnd p₁) hcov3
        have hc0 : (Bnd p).card ≤ b := hBnd_card p (by omega)
        have hc1 : (Bnd p₀).card ≤ b := hBnd_card p₀ (by simp [p₀]; omega)
        have hc2 : (Bnd p₁).card ≤ b := hBnd_card p₁ (by simp [p₁]; omega)
        have h3b : (Bnd p ∪ Bnd p₀ ∪ Bnd p₁).card ≤ 3 * b / 2 := by omega
        exact le_trans h3b (le_max_right _ _)
      have hS_sub_B0 : S ⊆ Bnd p₀ := by
        intro v hv
        rcases Finset.mem_sdiff.mp hv with ⟨hv01, hnotB⟩
        have hvU : v ∈ Bnd p ∪ Bnd p₀ ∪ Bnd p₁ := by
          rw [← hunion]; exact Finset.mem_union_right B hv
        rcases hcov3 v hvU with ⟨hB, _⟩ | ⟨hB, _⟩ | ⟨hB0, _⟩
        · exact absurd hB hnotB
        · exact absurd hB hnotB
        · exact hB0
      have hS_le_b : S.card ≤ b :=
        le_trans (Finset.card_le_card hS_sub_B0) (hBnd_card p₀ (by simp [p₀]; omega))
      have hD_step : D_prev + S.card ≤ D_cur := by
        simp only [D_prev, D_cur, Nat.mul_succ]; omega
      let ts : List (Finset (Fin n)) := B.powerset.toList
      have hts_len : ts.length = 2 ^ B.card := by simp [ts]
      have hstep : ∀ (T : Finset (Fin n)) (π : List (Clause (Fin n) × ℕ)),
          T ∈ ts → ValidDeriv F W D_cur π → (∀ x ∈ π_base, x ∈ π) →
          ¬ Feasible p (asgnOf T) →
          ∃ π' : List (Clause (Fin n) × ℕ),
            ValidDeriv F W D_cur π' ∧
            π'.length ≤ π.length + (2 ^ S.card - 1) ∧
            (∀ x ∈ π, x ∈ π') ∧
            ∃ q ∈ π', Vars q.1 ⊆ B ∧ Falsifies (asgnOf T) q.1 := by
        intro T π _ hπ hsubBase hnotF
        have hbase : ∀ (πc : List (Clause (Fin n) × ℕ)) (β : Fin n → Bool),
            ValidDeriv F W D_cur πc → (∀ x ∈ π, x ∈ πc) → AgreeOn B (asgnOf T) β →
            ∃ π' : List (Clause (Fin n) × ℕ),
              ValidDeriv F W D_cur π' ∧
              π'.length ≤ πc.length + 0 ∧
              (∀ x ∈ πc, x ∈ π') ∧
              ∃ q ∈ π', Vars q.1 ⊆ B ∪ S ∧ Falsifies β q.1 ∧ q.2 ≤ D_prev := by
          intro πc β hπc hsubπ hagree
          have hnotFβ : ¬ Feasible p β := by
            rwa [← hFeas_congr p hagree]
          have hdisjF : ¬ Feasible p₀ β ∨ ¬ Feasible p₁ β := by
            by_contra hboth
            push Not at hboth
            exact hnotFβ (hglue p hplt β hboth.1 hboth.2)
          rcases hdisjF with hnot0 | hnot1
          · rcases hπ₀mem β hnot0 with ⟨q, hq0, hvars0, hf0⟩
            have hq_base : q ∈ π_base := List.mem_append_left π₁ hq0
            have hq_c : q ∈ πc := hsubπ q (hsubBase q hq_base)
            have hqd : q.2 ≤ D_prev := by
              rcases List.mem_iff_get.mp hq0 with ⟨idx, rfl⟩
              exact (hπ₀ idx).2.1
            have hvarsU : Vars q.1 ⊆ B ∪ S := by
              rw [hunion]
              exact Finset.Subset.trans hvars0
                (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)
            exact ⟨πc, hπc, by simp, fun _ hx => hx, q, hq_c, hvarsU, hf0, hqd⟩
          · rcases hπ₁mem β hnot1 with ⟨q, hq1, hvars1, hf1⟩
            have hq_base : q ∈ π_base := List.mem_append_right π₀ hq1
            have hq_c : q ∈ πc := hsubπ q (hsubBase q hq_base)
            have hqd : q.2 ≤ D_prev := by
              rcases List.mem_iff_get.mp hq1 with ⟨idx, rfl⟩
              exact (hπ₁ idx).2.1
            have hvarsU : Vars q.1 ⊆ B ∪ S := by
              rw [hunion]
              exact Finset.Subset.trans hvars1 Finset.subset_union_right
            exact ⟨πc, hπc, by simp, fun _ hx => hx, q, hq_c, hvarsU, hf1, hqd⟩
        rcases extend_over_vars (F := F) (W := W) (D := D_prev) (D_all := D_cur) (bCost := 0)
            S B hdisj hW_BS hD_step (asgnOf T) π hπ hbase with
          ⟨π', hπ', hlen', hsub', q, hq, hvars, hf, _⟩
        exact ⟨π', hπ', by simpa using hlen', hsub', q, hq, hvars, hf⟩
      rcases memoize_list (F := F) (W := W) (D_all := D_cur) (stepCost := 2 ^ S.card - 1)
          B (fun α => ¬ Feasible p α) ts π_base hπ_base hstep with
        ⟨π, hπ, hlenπ, _, hmemπ⟩
      refine ⟨π, hπ, ?_, ?_⟩
      · have hBS_card : B.card + S.card ≤ W := by
          rw [← Finset.card_union_of_disjoint hdisj]
          exact hW_BS
        have hadd : ts.length * (2 ^ S.card - 1) ≤ 2 ^ W := by
          rw [hts_len]
          calc
            2 ^ B.card * (2 ^ S.card - 1) ≤ 2 ^ B.card * 2 ^ S.card :=
              Nat.mul_le_mul_left _ (Nat.sub_le _ _)
            _ = 2 ^ (B.card + S.card) := (pow_add 2 B.card S.card).symm
            _ ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hBS_card
        have hbase_len : π_base.length ≤ 2 * (2 ^ (r + W + 2) - 2 ^ W) := by
          simp only [π_base, List.length_append]
          omega
        have hpow_le : 2 ^ W ≤ 2 ^ (r + W + 2) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hpow_step : 2 * (2 ^ (r + W + 2) - 2 ^ W) + 2 ^ W = 2 ^ (r + 1 + W + 2) - 2 ^ W := by
          have hexp : 2 ^ (r + 1 + W + 2) = 2 * 2 ^ (r + W + 2) := by
            have : r + 1 + W + 2 = (r + W + 2) + 1 := by omega
            rw [this, pow_succ, mul_comm]
          rw [hexp]
          omega
        omega
      · intro α hnotF
        let T : Finset (Fin n) := B.filter (fun v => α v = true)
        have hTmem : T ∈ ts := by
          simp only [ts, Finset.mem_toList, Finset.mem_powerset]
          exact Finset.filter_subset _ _
        have hagree : AgreeOn B α (asgnOf T) := by
          intro v hv
          simp only [asgnOf, T, Finset.mem_filter, hv, true_and]
          cases α v <;> rfl
        have hnotFT : ¬ Feasible p (asgnOf T) := by
          rwa [← hFeas_congr p hagree]
        rcases hmemπ T hTmem hnotFT with ⟨q, hq, hvars, hf⟩
        exact ⟨q, hq, hvars, falsifies_of_agreeOn hvars (agreeOn_symm hagree) hf⟩
  rcases htree h [] (by simp) with ⟨π, hπvalid, hπlen, hπmem⟩
  have hnotFeasRoot : ¬ Feasible [] (fun _ => false) := by
    rintro ⟨β, _, hsat⟩
    apply hunsat
    refine ⟨β, ?_⟩
    rintro C ⟨i, rfl⟩
    exact hsat (clause i) ⟨i, List.nil_prefix, rfl⟩
  rcases hπmem (fun _ => false) hnotFeasRoot with ⟨q, hq, hvars, _⟩
  have hBnd_nil : Bnd [] = ∅ := by
    ext v
    simp [Bnd, outside]
  have hq_empty : q.1 = ∅ := by
    rw [hBnd_nil, Finset.subset_empty] at hvars
    by_contra hne
    rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨l, hl⟩
    have : l.1 ∈ Vars q.1 := Finset.mem_image.mpr ⟨l, hl, rfl⟩
    rw [hvars] at this
    exact Finset.notMem_empty _ this
  have hemp_mem : (∅ : Clause (Fin n)) ∈ π.map Prod.fst :=
    List.mem_map.mpr ⟨q, hq, hq_empty⟩
  exact ⟨π, ⟨validDeriv_isDerivation hπvalid, hemp_mem⟩, le_trans hπlen (Nat.sub_le _ _), hπvalid⟩

end PEqualNP.Outside.L_pcx_214_aux

theorem PEqualNP.Outside.L_pcx_214 : (∀ (n m h a b : ℕ) (clause : Fin m → PEqualNP.ProofComplexity.Clause (Fin n))
    (addr : Fin m → List Bool),
  (∀ i, (addr i).length = h) →
  let occurs := fun (i : Fin m) (v : Fin n) => ∃ sign, (v, sign) ∈ clause i
  let inside := fun (p : List Bool) (v : Fin n) =>
    ∃ i, List.IsPrefix p (addr i) ∧ occurs i v
  let outside := fun (p : List Bool) (v : Fin n) =>
    ∃ j, ¬ List.IsPrefix p (addr j) ∧ occurs j v
  (∀ leaf : List Bool, leaf.length = h →
    Nat.card {v : Fin n // inside leaf v} ≤ a) →
  (∀ p : List Bool, p.length ≤ h →
    Nat.card {v : Fin n // inside p v ∧ outside p v} ≤ b) →
  ¬ PEqualNP.ProofComplexity.Satisfiable (Set.range clause) →
  let W := max a (3 * b / 2)
  ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin n) × ℕ),
    PEqualNP.ProofComplexity.IsRefutation (Set.range clause) (π.map Prod.fst) ∧
    π.length ≤ 2 ^ (h + W + 2) ∧
    ∀ i : Fin π.length, let L := π.get i
      L.1.card ≤ W ∧ L.2 ≤ a + b * h ∧
      (L.1 ∈ Set.range clause ∨
        ∃ j k : Fin π.length, i < j ∧ i < k ∧
          (π.get j).2 < L.2 ∧ (π.get k).2 < L.2 ∧
          PEqualNP.ProofComplexity.IsResolvent (π.get j).1 (π.get k).1 L.1)) := by
  intro n m h a b clause addr haddr
  dsimp only
  intro hleaf hbnd hunsat
  exact PEqualNP.Outside.L_pcx_214_aux.main_proof n m h a b clause addr haddr hleaf hbnd hunsat
